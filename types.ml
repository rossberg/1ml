(*
 * (c) 2014 Andreas Rossberg
 *)

type lab = string
type var = string
type level = int

type varset = Fomega.VarSet.t

type 'a row = (lab * 'a) list

type eff =
  | Impure
  | Pure

type feff =
  | Explicit of eff
  | Implicit

type kind =
  | BaseK
  | ProdK of kind row
  | FunK of kind list * kind

type typ =
  | VarT of var * kind
  | PrimT of Prim.typ
  | StrT of typ row
  | FunT of (var * kind) list * typ * extyp * feff
  | TypT of extyp
  | WrapT of extyp
  | LamT of (var * kind) list * typ
  | AppT of typ * typ list
  | TupT of typ row
  | DotT of typ * lab
  | RecT of (var * kind) * typ
  | InferT of infer ref

and extyp =
  | ExT of (var * kind) list * typ

and infer =
  | Undet of undet
  | Det of typ

and undet =
  { id : int;
    mutable level : level;
    mutable vars : varset;
    mutable il : Fomega.typ lazy_t option
  }


(* Path names *)

let default_path p l = if p = "" then l else p
let append_path p l = if p = "" then l else p ^ "." ^ l
let prepend_path p p' = assert (p' <> ""); if p = "" then p' else p ^ "." ^ p'
let cut_path p p' =
  if Lib.String.is_prefix (p ^ ".") p' then
    String.sub p' (String.length p + 1) (String.length p' - String.length p - 1)
  else
    p'

let rename_vars f aks = List.map (fun (a, k) -> f a, k) aks


(* Variable Sets *)

module VarSet = Fomega.VarSet
open VarSet

let add_bind aks vs = List.fold_left (fun vs (a, k) -> add a vs) vs aks
let remove_bind aks vs = List.fold_left (fun vs (a, k) -> remove a vs) vs aks


(* Simple operations *)

let join_eff p1 p2 =
  match p1, p2 with
  | Pure, Pure -> Pure
  | _, _ -> Impure


(* Rows *)

let domain_row r = List.map fst r
let range_row r = List.map snd r

let lab i = "_" ^ string_of_int i

let tup_row xs = List.mapi (fun i x -> lab (i + 1), x) xs
let rec as_tup_row = function
  | [] -> Some []
  | [_] -> None
  | tr ->
    if Lib.List.for_alli (fun i (l, _) -> l = lab (i + 1)) tr then
      Some (range_row tr)
    else
      None

let map_row f xr = List.map (fun (l, x) -> (l, f x)) xr
let map_rowi f xr = List.map (fun (l, x) -> (l, f l x)) xr

let intersect_row r1 r2 =
  List.filter (fun (l1, _) -> List.exists (fun (l2, _) -> l1 = l2) r2) r1

let diff_row r1 r2 =
  List.filter (fun (l1, _) -> List.for_all (fun (l2, _) -> l1 <> l2) r2) r1

let rec project_typ ls t =
  match ls, t with
  | [], _ -> t
  | l::ls', StrT(tr) -> project_typ ls' (List.assoc l tr)
  | _ -> raise Not_found


(* Size check *)

let undecidable_flag = ref false

let rec is_small_typ = function
  | VarT(a, k) -> true
  | PrimT(t) -> true
  | StrT(r) -> is_small_row r
  | FunT(aks, t, s, f) ->
    aks = [] && is_small_typ t && is_small_extyp s && f = Explicit Impure
  | TypT(s) -> is_small_extyp s
  | WrapT(s) -> true
  | LamT(aks, t) -> is_small_typ t
  | AppT(t, ts) -> is_small_typ t && List.for_all is_small_typ ts
  | TupT(r) -> is_small_row r
  | DotT(t, l) -> is_small_typ t
  | RecT(ak, t) -> assert (is_small_typ t); true
  | InferT(z) -> true

and is_small_extyp = function
  | ExT(aks, t) -> aks = [] && is_small_typ t

and is_small_row r = List.for_all (fun (l, t) -> is_small_typ t) r


(* Free variables and occurrence check *)

let rec vars_typ = function
  | VarT(a, k) -> VarSet.singleton a
  | PrimT(t) -> VarSet.empty
  | StrT(r) -> vars_row r
  | FunT(aks, t, s, f) -> remove_bind aks (union (vars_typ t) (vars_extyp s))
  | TypT(s) -> vars_extyp s
  | WrapT(s) -> vars_extyp s
  | LamT(aks, t) -> remove_bind aks (vars_typ t)
  | AppT(t, ts) -> union (vars_typ t) (vars_typs ts)
  | TupT(r) -> vars_row r
  | DotT(t, l) -> vars_typ t
  | RecT(ak, t) -> remove_bind [ak] (vars_typ t)
  | InferT(z) -> VarSet.empty

and vars_extyp = function
  | ExT(aks, t) -> remove_bind aks (vars_typ t)

and vars_typs ts =
  List.fold_left (fun vs t -> union vs (vars_typ t)) VarSet.empty ts
and vars_row r = vars_typs (List.map snd r)


let contains_bind a = List.exists (fun (a', k) -> a = a')

let rec contains_typ a = function
  | VarT(a', k) -> a = a'
  | PrimT(t) -> false
  | StrT(r) -> contains_row a r
  | FunT(aks, t, s, f) ->
    not (contains_bind a aks) && (contains_typ a t || contains_extyp a s)
  | TypT(s) -> contains_extyp a s
  | WrapT(s) -> contains_extyp a s
  | LamT(aks, t) -> not (contains_bind a aks) && contains_typ a t
  | AppT(t, ts) -> contains_typ a t || List.exists (contains_typ a) ts
  | TupT(r) -> contains_row a r
  | DotT(t, l) -> contains_typ a t
  | RecT(ak, t) -> not (contains_bind a [ak]) && contains_typ a t
  | InferT(z) -> false

and contains_extyp a = function
  | ExT(aks, t) -> not (contains_bind a aks) && contains_typ a t

and contains_row a = List.exists (fun (l, t) -> contains_typ a t)


let rec occurs_typ u = function
  | VarT(a, k) -> false
  | PrimT(t) -> false
  | StrT(r) -> occurs_row u r
  | FunT(aks, t, s, f) -> occurs_typ u t || occurs_extyp u s
  | TypT(s) -> occurs_extyp u s
  | WrapT(s) -> occurs_extyp u s
  | LamT(aks, t) -> occurs_typ u t
  | AppT(t, ts) -> occurs_typ u t || List.exists (occurs_typ u) ts
  | TupT(r) -> occurs_row u r
  | DotT(t, l) -> occurs_typ u t
  | RecT(ak, t) -> occurs_typ u t
  | InferT(z) ->
    match !z with
    | Det t -> occurs_typ u t
    | Undet u' -> u.id = u'.id

and occurs_extyp u = function
  | ExT(aks, t) -> occurs_typ u t

and occurs_row u = List.exists (fun (l, t) -> occurs_typ u t)


(* TODO: remove
let rec undet_typ level = function
  | VarT(a, k) -> []
  | PrimT(t) -> []
  | StrT(r) -> undet_row level r
  | FunT(aks, t, s, f) ->
    Lib.List.merge_nodup (undet_typ level t) (undet_extyp level s)
  | TypT(s) -> undet_extyp level s
  | WrapT(s) -> undet_extyp level s
  | LamT(aks, t) -> undet_typ level t
  | AppT(t, ts) ->
    Lib.List.merge_nodup (undet_typ level t) (undet_typs level ts)
  | TupT(r) -> undet_row level r
  | DotT(t, l) -> undet_typ level t
  | RecT(ak, t) -> undet_typ level t
  | InferT(z) ->
    match !z with
    | Det t -> undet_typ level t
    | Undet u -> if u.level <= level then [] else [z]

and undet_extyp level = function
  | ExT(aks, t) -> undet_typ level t

and undet_typs level ts =
  List.fold_left (fun zs t -> Lib.List.merge_nodup zs (undet_typ level t)) [] ts
and undet_row level r = undet_typs level (List.map snd r)
*)


(* Substitution *)

type subst = (var * typ) list

let varTs aks = List.map (fun (a, k) -> VarT(a, k)) aks
let subst aks ts = List.map2 (fun (a, k) t -> a, t) aks ts

let string_of_typ_fwd = ref (fun _ -> raise Not_found)

let rename = Fomega.rename

let avoid1 a k su =
  if List.mem_assoc a su then
    a, List.filter (fun (a', t) -> a' <> a) su
  else if List.exists (fun (_, t) -> contains_typ a t) su then
    let a' = rename a in a', [a, VarT(a', k)]@su
  else
    a, su

let avoid aks su =
  List.fold_right (fun (a, k) (aks, su) ->
    let a', su' = avoid1 a k su in (a', k)::aks, su'
  ) aks ([], su)

let rec subst_typ su = function
  | VarT(a, k) -> (try List.assoc a su with Not_found -> VarT(a, k))
  | PrimT(t) -> PrimT(t)
  | StrT(r) -> StrT(subst_row su r)
  | FunT(aks, t, s, f) ->
    let aks', su' = avoid aks su in
    FunT(aks', subst_typ su' t, subst_extyp su' s, f)
  | TypT(s) -> TypT(subst_extyp su s)
  | WrapT(s) -> WrapT(subst_extyp su s)
  | LamT(aks, t) ->
    let aks', su' = avoid aks su in
    LamT(aks', subst_typ su' t)
  | AppT(t, ts) ->
    (match subst_typ su t, List.map (subst_typ su) ts with
    | LamT(aks, t'), ts' -> subst_typ (subst aks ts') t'
    | t', ts' -> AppT(t', ts')
    )
  | TupT(r) -> TupT(subst_row su r)
  | DotT(t, l) ->
    (match subst_typ su t with
    | TupT(r) -> List.assoc l r
    | t' -> DotT(t', l)
    )
  | RecT(ak, t) ->
    let aks', su' = avoid [ak] su in
    RecT(List.hd aks', subst_typ su' t)
  | InferT(z) ->
    match !z with
    | Undet _ -> InferT(z)
    | Det t -> subst_typ su t

and subst_extyp su = function
  | ExT(aks, t) ->
    let aks', su' = avoid aks su in
    ExT(aks', subst_typ su' t)

and subst_row su = map_row (subst_typ su)


let subst_used subst su x = if su = [] then x else subst su x

let subst_typ = subst_used subst_typ
let subst_extyp = subst_used subst_extyp
let subst_row = subst_used subst_row

let subst_infer su z =
  match !z with
  | Det _ -> ()
  | Undet u ->
    List.iter (fun (a, t) ->
      if VarSet.mem a u.vars then
      match t with
      | VarT(a', k) -> u.vars <- add a' (remove a u.vars)
      | _ -> assert false
    ) su


(* Normalisation *)

let rec norm_typ = function
  | VarT(a, k) -> VarT(a, k)
  | PrimT(t) -> PrimT(t)
  | StrT(r) -> StrT(norm_row r)
  | FunT(aks, t, s, f) -> FunT(aks, norm_typ t, norm_extyp s, f)
  | TypT(s) -> TypT(norm_extyp s)
  | WrapT(s) -> WrapT(norm_extyp s)
  | LamT(aks, t) -> LamT(aks, norm_typ t)
  | AppT(t, ts) ->
    (match norm_typ t with
    | LamT(aks, t') -> norm_typ (subst_typ (subst aks ts) t')
    | t' -> AppT(t', List.map norm_typ ts)
    )
  | TupT(r) -> TupT(norm_row r)
  | DotT(t, l) ->
    (match norm_typ t with
    | TupT(r) -> norm_typ (List.assoc l r)
    | t' -> DotT(t', l)
    )
  | RecT(ak, t) -> RecT(ak, norm_typ t)
  | InferT(z) ->
    match !z with
    | Undet _ -> InferT(z)
    | Det t -> norm_typ t

and norm_extyp = function
  | ExT(aks, t) -> ExT(aks, norm_typ t)

and norm_row r = map_row norm_typ r


(* Kinding *)

exception Kind

let rec kind_of_typ = function
  | VarT(a, k) -> k
  | PrimT(t) -> BaseK
  | StrT(r) ->
    if List.for_all (fun (l, k) -> k = BaseK) (kind_of_row r) then BaseK
    else raise Kind
  | FunT(aks, t, s, f) ->
    if kind_of_typ t = BaseK && kind_of_extyp s = BaseK then BaseK
    else raise Kind
  | TypT(s) -> if kind_of_extyp s = BaseK then BaseK else raise Kind
  | WrapT(s) -> if kind_of_extyp s = BaseK then BaseK else raise Kind
  | LamT(aks, t) -> FunK(List.map snd aks, kind_of_typ t)
  | AppT(t, ts) ->
    (match kind_of_typ t, List.map kind_of_typ ts with
    | FunK(ks1, k), ks2 when ks1 = ks2 -> k
    | _ -> raise Kind
    )
  | TupT(r) -> ProdK(kind_of_row r)
  | DotT(t, l) ->
    (match kind_of_typ t with
    | ProdK(kr) -> (try List.assoc l kr with Not_found -> raise Kind)
    | _ -> raise Kind
    )
  | RecT(ak, t) -> assert (kind_of_typ t = snd ak); snd ak
  | InferT(z) -> BaseK

and kind_of_extyp = function
  | ExT(aks, t) -> if kind_of_typ t = BaseK then BaseK else raise Kind

and kind_of_row r = map_row kind_of_typ r


(* Construction helpers *)

let funK(ks, k) = if ks = [] then k else FunK(ks, k)

let lamT(aks, t) = if aks = [] then t else LamT(aks, t)
let appT(t, ts) = if ts = [] then t else AppT(t, ts)

let unvarT = function
  | VarT(a, k) -> a, k
  | _ -> assert false

let unexT = function
  | ExT(_, t) -> t


(* Unification *)

let stamp_count = ref 1
let level () = !stamp_count
let stamp () =
  if !stamp_count = max_int then failwith "stamp";
  let n = !stamp_count in
  incr stamp_count; n

let rec guess_typ vars = function
  | BaseK ->
    let i = stamp () in
    let z = ref (Undet{id = i; level = i; vars = vars; il = None}) in
    InferT(z), [z]
  | ProdK(kr) ->
    let tzsr = map_row (guess_typ vars) kr in
    TupT(map_row fst tzsr), List.concat (List.map snd (List.map snd tzsr))
  | FunK _ -> assert false

let guess_typs vars aks =
  List.fold_right (fun (a, k) (ts, zs) ->
    let t, zs' = guess_typ vars k in t::ts, zs' @ zs
  ) aks ([], [])

let rec follow_typ = function
  | InferT(z) as t ->
    (match !z with
    | Undet _ -> t
    | Det t' -> follow_typ t'
    )
  | t -> t

let rec extrude_typ u vs = function
  | VarT(a, k) -> mem a u.vars || mem a vs
  | PrimT(t) -> true
  | StrT(r) -> extrude_row u vs r
  | FunT(aks, t, s, f) ->
    let vs' = add_bind aks vs in extrude_typ u vs' t && extrude_extyp u vs' s
  | TypT(s) -> extrude_extyp u vs s
  | WrapT(s) -> extrude_extyp u vs s
  | LamT(aks, t) -> extrude_typ u (add_bind aks vs) t
  | AppT(t, ts) -> extrude_typ u vs t && List.for_all (extrude_typ u vs) ts
  | TupT(r) -> extrude_row u vs r
  | DotT(t, l) -> extrude_typ u vs t
  | RecT(ak, t) -> extrude_typ u (add_bind [ak] vs) t
  | InferT(z) ->
    match !z with
    | Undet u' -> u.id != u'.id && (u'.level <- min u.level u'.level; true)
    | Det t -> extrude_typ u vs t

and extrude_extyp u vs = function
  | ExT(aks, t) -> extrude_typ u (add_bind aks vs) t

and extrude_row u vs = List.for_all (fun (l, t) -> extrude_typ u vs t)

let update_infer z t =
  assert (kind_of_typ t = BaseK);
  let u = match !z with Undet u -> u | Det _ -> assert false in
  z := Det t;
  (match u.il with None -> () | Some t' -> ignore (Lazy.force t'))

let close_typ z t =
  assert (VarSet.cardinal (vars_typ t) = 1);
  update_infer z t

let resolve_typ z t =
  let u = match !z with Undet u -> u | Det _ -> assert false in
  match follow_typ t with
  | InferT(z') as t' ->
    z == z' ||
    (match !z' with
    | Undet u' ->
      let vars = inter u.vars u'.vars in
      if u.level >= u'.level then (update_infer z t'; u'.vars <- vars)
      else (update_infer z' (InferT(z)); u.vars <- vars);
      true
    | Det _ -> assert false
    )
  | t' ->
    is_small_typ t' &&
    extrude_typ u VarSet.empty t' &&
    (update_infer z t'; true)

let resolve_always z t = if not (resolve_typ z t) then assert false


let rec unify_typ t1 t2 =
  t1 = t2 ||
  match t1, t2 with
  | InferT(z), _ ->
    (match !z with
    | Det t1' -> unify_typ t1' t2
    | Undet _ -> resolve_typ z t2
    )
  | _, InferT(z) ->
    (match !z with
    | Det t2' -> unify_typ t1 t2'
    | Undet _ -> resolve_typ z t1
    )
  | StrT(r1), StrT(r2) ->
    unify_row r1 r2
  | FunT([], t11, ExT([], t12), Explicit Impure),
    FunT([], t21, ExT([], t22), Explicit Impure) ->
    unify_typ t11 t21 && unify_typ t12 t22
  | WrapT(ExT(aks1, t11)), WrapT(ExT(aks2, t21)) ->
    List.map snd aks1 = List.map snd aks2 &&
    unify_typ t11 (subst_typ (subst aks2 (varTs aks1)) t21)
  | RecT(ak1, t11), RecT(ak2, t21) ->  (* TODO: need to do paths? *)
    snd ak1 = snd ak2 &&
    unify_typ t11 (subst_typ (subst [ak2] (varTs [ak1])) t21)
  | TypT(ExT([], t1')), TypT(ExT([], t2')) ->
    unify_typ t1' t2'
  | _, _ -> false
    
and unify_row r1 r2 =
  (* TODO: reorder; row unification *)
  try List.for_all2 (fun (l1, t1) (l2, t2) -> l1 = l2 && unify_typ t1 t2) r1 r2
  with Invalid_argument _ -> false


(* String conversion *)

let verbose_binders_flag = ref false
let verbose_paths_flag = ref false
let verbose_vars_flag = ref false
let verbose_levels_flag = ref false

let verbosest_on () =
  verbose_binders_flag := true;
  verbose_paths_flag := true;
  verbose_vars_flag := true;
  verbose_levels_flag := true
  
let string_of_eff_sort = function
  | Impure -> "impure"
  | Pure -> "pure"

let string_of_feff_sort = function
  | Explicit eff -> string_of_eff_sort eff
  | Implicit -> "implicit"

let rec string_of_typ_sort = function
  | VarT(a, k) -> "abstract"
  | PrimT(t) -> Prim.string_of_typ t
  | StrT(r) -> "structure"
  | FunT(aks, t, s, f) -> string_of_feff_sort f ^ " function"
  | TypT(s) -> (if is_small_extyp s then "small" else "large") ^ " type"
  | WrapT(s) -> "wrapped"
  | LamT(aks, t) -> "abstract"
  | AppT(t, ts) ->
    string_of_typ_sort t ^ String.concat ""
      (List.map (fun t' -> "(" ^ string_of_typ_sort t' ^ ")") ts)
  | TupT(r) -> "abstract"
  | DotT(t, l) -> string_of_typ_sort t ^ "." ^ l
  | RecT(ak, t) -> "recursive"
  | InferT(z) ->
    match !z with
    | Det t -> string_of_typ_sort t
    | Undet u -> "unknown"

let base_prec = 0
let binder_prec = 1
let app_prec = 2
let dot_prec = 2
let atom_prec = 2

let paren my_prec required_prec s =
    if my_prec < required_prec then "(" ^ s ^ ")" else s

let rec string_of_row' sep string_of' prec r =
    String.concat ", "
      (List.map (fun (l, t) -> l ^ sep ^ string_of' base_prec t) r)

let rec string_of_kind' prec = function
  | BaseK -> "*"
  | ProdK(kr) -> "{" ^ string_of_row' ":" string_of_kind' base_prec kr ^ "}"
  | FunK([], k) -> string_of_kind' prec k
  | FunK(k1::ks, k) ->
    paren binder_prec prec (
      string_of_kind' app_prec k ^ "->" ^
      string_of_kind' binder_prec (FunK(ks, k))
    )

let rec string_of_typ' prec = function
  | VarT(a, k) ->
    if k <> BaseK && !verbose_vars_flag then
      paren base_prec prec (a ^ ":" ^ string_of_kind' base_prec k)
    else
      a
  | PrimT(t) -> Prim.string_of_typ t
  | StrT(tr) ->
    (match as_tup_row tr with
    | Some ts ->
      "(" ^ String.concat ", " (List.map (string_of_typ' base_prec) ts) ^ ")"
    | None ->
      "{" ^ string_of_row' " : " string_of_typ' base_prec tr ^ "}"
    )
  | FunT(aks, t, s, f) ->
    paren binder_prec prec (
      string_of_binder "!" aks ^
      string_of_typ' (binder_prec + 1) t ^
      (match f with
      | Explicit Impure -> " -> "
      | Explicit Pure -> " => "
      | Implicit -> "'=> "
      ) ^
      string_of_extyp' binder_prec s
    )
  | TypT(s) -> "[= " ^ string_of_extyp' base_prec s ^ "]"
  | WrapT(s) -> "[" ^ string_of_extyp' base_prec s ^ "]"
  | LamT(aks, t) ->
    paren binder_prec prec (
      string_of_binder "\\" aks ^
      string_of_typ' binder_prec t
    )
  | AppT(t, ts) ->
    paren app_prec prec (
      string_of_typ' app_prec t ^
      String.concat ""
        (List.map (fun t' -> "(" ^ string_of_typ' base_prec t' ^ ")") ts)
    )
  | TupT(tr) -> "{" ^ string_of_row' " = " string_of_typ' base_prec tr ^ "}"
  | DotT(t, l) ->
    if !verbose_paths_flag then
      paren dot_prec prec (string_of_typ' dot_prec t ^ "." ^ l)
    else
      l
  | RecT(ak, t) ->
    paren binder_prec prec (
      string_of_binder "@" [ak] ^
      string_of_typ' binder_prec t
    )
  | InferT(z) ->
    match !z with
    | Det t -> string_of_typ' prec t
    | Undet u ->
      "'" ^ string_of_int u.id ^
      (if not !verbose_levels_flag then "" else
        "@" ^ string_of_int u.level ^
        "{" ^ String.concat "," (VarSet.elements u.vars) ^ "}"
      )

and string_of_extyp' prec = function
  | ExT(aks, t) ->
    paren binder_prec prec (
      string_of_binder "?" aks ^ string_of_typ' binder_prec t
    )

and string_of_binder sym = function
  | [] -> ""
  | aks ->
    sym ^ String.concat " " (List.map (fun (a, k) ->
      a ^
      (if k = BaseK || not !verbose_binders_flag then "" else
      ":" ^ string_of_kind' atom_prec k
      )
    ) aks) ^ ". "


let string_of_kind = string_of_kind' base_prec
let string_of_typ = string_of_typ' base_prec
let string_of_extyp = string_of_extyp' base_prec

let string_of_norm_typ t = try string_of_typ (norm_typ t)
with Not_found -> "!! " ^ string_of_typ t  (* TODO: debug *)
let string_of_norm_extyp s = try string_of_extyp (norm_extyp s)
with Not_found -> "!! " ^ string_of_extyp s  (* TODO: debug *)

let _ = string_of_typ_fwd := string_of_typ


(* Formatting *)

open Format

let print_brack lbrack rbrack print =
  open_box (String.length lbrack);
  print_string lbrack;
  print ();
  print_cut ();
  print_string rbrack;
  close_box ()

let print_paren my_prec required_prec print =
  if my_prec < required_prec then
    print_brack "(" ")" print
  else
    print ()

let enter l = function
  | path::ctxt -> (l::path)::path::ctxt
  | [] -> assert false

let rec matches_path t path =
  match t, path with
  | VarT(a, _), [a'] -> a = a'  (* TODO: adapt *)
  | AppT(t', _), "()"::path' -> matches_path t' path'
  | _ -> false

let matches_ctxt t = List.exists (matches_path t)

let rec print_list' print' prec ctxt xs =
  let n = ref (List.length xs) in
  List.iter (fun x ->
    print' prec ctxt x;
    decr n;
    if (!n > 0) then (print_string ","; print_break 1 2)
  ) xs

let rec print_row' sep print' prec ctxt xr =
  open_hvbox 0;
  List.iter (fun (l, x) ->
    open_hovbox 0;
    print_string l;
    print_string " ";
    print_string sep;
    print_break 1 2;
    open_hovbox 0;
    print' prec (enter l ctxt) x;
    print_string ";";
    close_box ();
    close_box ();
    print_break 1 0;
  ) xr;
  close_box ()

let rec print_kind' prec ctxt = function
  | BaseK ->
    print_string "*"
  | ProdK(kr) ->
    print_brack "{" "}" (fun () ->
      print_row' ":" print_kind' base_prec ctxt kr;
    )
  | FunK([], k) ->
    print_kind' prec ctxt k;
  | FunK(k1::ks, k) ->
    print_paren binder_prec prec (fun () ->
      print_kind' app_prec ctxt k1;
      print_string " ";
      print_string "->";
      print_break 1 2;
      print_kind' binder_prec ctxt (FunK(ks, k))
    )

let rec print_typ' prec ctxt = function
  | VarT(a, k) ->
    if k <> BaseK && !verbose_vars_flag then
      print_paren base_prec prec (fun () ->
        print_string a;
        print_string ":";
        print_break 0 2;
        print_kind' base_prec ctxt k
      )
    else
      print_string a
  | PrimT(t) ->
    print_string (Prim.string_of_typ t)
  | StrT(tr) ->
    (match as_tup_row tr with
    | Some ts ->
      print_brack "(" ")" (fun () ->
        print_list' print_typ' base_prec ctxt ts;
      )
    | None ->
      print_brack "{" "}" (fun () ->
        print_row' ":" print_typ' base_prec ctxt tr;
      )
    )
  | FunT(aks, t, s, f) ->
    print_binder prec "!" aks (fun () ->
      open_box 0;
      print_typ' (binder_prec + 1) ([List.map fst aks] @ ctxt) t;
      close_box ();
      print_string " ";
      print_string
        (match f with
        | Explicit Impure -> "->"
        | Explicit Pure -> "=>"
        | Implicit -> "'=>"
        );
      print_break 1 2;
      open_box 0;
      print_extyp' binder_prec (enter "()" ctxt) s;
      close_box ()
    )
  | TypT(s) ->
    print_brack "[= " "]" (fun () -> print_extyp' base_prec ctxt s);
  | WrapT(s) ->
    print_brack "[" "]" (fun () -> print_extyp' base_prec ctxt s);
  | LamT(aks, t) ->
    print_binder prec "\\" aks (fun () ->
      print_typ' binder_prec ctxt t
    )
  | AppT(t, []) ->
    print_typ' prec ctxt t
  | AppT(t, [t1]) ->
    print_paren app_prec prec (fun () ->
      print_typ' app_prec ctxt t;
      print_string "(";
      print_break 0 2;
      print_typ' base_prec ctxt t1;
      print_string ")"
    )
  | AppT(t, t1::ts) ->
    print_typ' prec ctxt (AppT(AppT(t, [t1]), ts))
  | TupT(tr) ->
    print_brack "{" "}" (fun () ->
      print_row' "=" print_typ' base_prec ctxt tr;
    )
  | DotT(t, l) ->
    if String.contains l '$' then
      print_typ' prec ctxt t
    else if matches_ctxt t ctxt then
      print_string l
    else
      print_paren dot_prec prec (fun () ->
        print_typ' dot_prec ctxt t;
        print_string ".";
        print_string l
      )
  | RecT(ak, t) ->
    print_binder prec "@" [ak] (fun () ->
      print_typ' binder_prec ctxt t
    )
  | InferT(z) ->
    match !z with
    | Det t -> print_typ' prec ctxt t
    | Undet u -> print_string ("'" ^ string_of_int u.id)

and print_extyp' prec ctxt = function
  | ExT(aks, t) ->
    print_binder prec "?" aks (fun () ->
      print_typ' binder_prec ([List.map fst aks] @ ctxt) t
    )

and print_binder prec sym aks print =
  print_paren binder_prec prec (fun () ->
    open_hovbox 2;
    if aks <> [] then begin
      print_string sym;
      List.iter (fun (a, k) ->
        print_string a;
        if k <> BaseK && !verbose_binders_flag then begin
          print_string ":";
          print_break 0 2;
          print_kind' atom_prec [[""]] k
        end;
        print_space ()
      ) aks
    end;
    print ();
    close_box ()
  )

let print_kind k = print_kind' base_prec [["prog"]] k; print_flush ()
let print_typ t = print_typ' base_prec [["prog"]] (norm_typ t); print_flush ()
let print_extyp s =
  print_extyp' base_prec [["prog"]] (norm_extyp s); print_flush ()
let print_row tr =
  print_row' ":" print_typ' base_prec [["prog"]] (norm_row tr); print_flush ()
