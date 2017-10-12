(*
 * (c) 2014 Andreas Rossberg
 *)

type lab = string
type var = string

type 'a row = (lab * 'a) list

type eff =
  | Pure
  | Impure

type kind =
  | BaseK
  | ProdK of kind row
  | FunK of kind * kind

type typ =
  | VarT of var * kind
  | PrimT of Prim.typ
  | StrT of typ row
  | FunT of var * kind * typ * extyp * eff
  | TypT of extyp
  | PackT of extyp
  | ProdT of typ row
  | LamT of var * kind * typ
  | DotT of typ * lab
  | AppT of typ * typ

and extyp =
  | ExT of var * kind * typ

type env = (var * typ) list
type 'a subst = (var * 'a) list

exception Error of string


(* Occurrence check *)

let rec occurs_row a = List.exists (fun (l, t) -> occurs_typ a t)

and occurs_typ a = function
  | VarT(a', k) -> a = a'
  | PrimT(t) -> false
  | StrT(r) -> occurs_row a r
  | FunT(a', k, t, s, p) -> a <> a' && (occurs_typ a t || occurs_extyp a s)
  | TypT(s) -> occurs_extyp a s
  | PackT(s) -> occurs_extyp a s
  | ProdT(r) -> occurs_row a r
  | LamT(a', k, t) -> a <> a' && occurs_typ a t
  | DotT(t, l) -> occurs_typ a t
  | AppT(t1, t2) -> occurs_typ a t1 || occurs_typ a t2

and occurs_extyp a = function
  | ExT(a', k, t) -> a <> a' && occurs_typ a t


(* Substitution *)

let avoid a k su =
  if List.exists (fun (_, t) -> occurs_typ a t) su then
    let a' = Fomega.rename a in a', [a, VarT(a', k)]@su
  else
    a, su

let rec subst_row su = List.map (fun (l, t) -> l, subst_typ su t)

and subst_typ su = function
  | VarT(a, k) ->
    assert (a <> "_");
    (try List.assoc a su with Not_found -> VarT(a, k))
  | PrimT(t) -> PrimT(t)
  | StrT(r) -> StrT(subst_row su r)
  | FunT(a, k, t, s, p) ->
    let a', su' = avoid a k su in
    FunT(a', k, subst_typ su' t, subst_extyp su' s, p)
  | TypT(s) -> TypT(subst_extyp su s)
  | PackT(s) -> PackT(subst_extyp su s)
  | ProdT(r) -> ProdT(subst_row su r)
  | LamT(a, k, t) ->
    let a', su' = avoid a k su in
    LamT(a', k, subst_typ su' t)
  | DotT(t, l) -> DotT(subst_typ su t, l)
  | AppT(t1, t2) -> AppT(subst_typ su t1, subst_typ su t2)

and subst_extyp su = function
  | ExT(a, k, t) ->
    let a', su' = avoid a k su in
    ExT(a', k, subst_typ su' t)


(* Normalisation *)

let rec norm_row r = List.map (fun (l, t) -> l, norm_typ t) r

and norm_typ = function
  | VarT(a, k) -> assert (a <> "_"); VarT(a, k)
  | PrimT(t) -> PrimT(t)
  | StrT(r) -> StrT(norm_row r)
  | FunT(a, k, t, s, p) -> FunT(a, k, norm_typ t, norm_extyp s, p)
  | TypT(s) -> TypT(norm_extyp s)
  | PackT(s) -> PackT(norm_extyp s)
  | ProdT(r) -> ProdT(norm_row r)
  | LamT(a, k, t) -> LamT(a, k, norm_typ t)
  | DotT(t, l) ->
    (match norm_typ t with
    | ProdT(r) -> norm_typ (List.assoc l r)
    | t' -> DotT(t', l)
    )
  | AppT(t1, t2) ->
    (match norm_typ t1 with
    | LamT(a, k, t) -> norm_typ (subst_typ [a, t2] t)
    | t1' -> AppT(t1', norm_typ t2)
    )

and norm_extyp = function
  | ExT(a, k, t) -> ExT(a, k , norm_typ t)


(* Kinding *)

let rec kind_of_row r = List.map (fun (l, t) -> l, kind_of_typ t) r

and kind_of_typ = function
  | VarT(a, k) -> k
  | PrimT(t) -> BaseK
  | StrT(r) -> BaseK
  | FunT(a', k, t, s, p) -> BaseK
  | TypT(s) -> BaseK
  | PackT(s) -> BaseK
  | ProdT(r) -> ProdK(kind_of_row r)
  | LamT(a', k, t) -> FunK(k, kind_of_typ t)
  | DotT(t, l) ->
    (match kind_of_typ t with
    | ProdK(r) -> List.assoc l r
    | _ -> raise Not_found
    )
  | AppT(t1, t2) ->
    (match kind_of_typ t1, kind_of_typ t2 with
    | FunK(t3, t1), t2 when t3 = t2 -> t1
    | _ -> raise Not_found
    )


(* Other operations *)

let domain env = List.map fst env
let range env = List.map snd env

let rename = Fomega.rename

let freshen_var ts a =
  if a <> "_" && List.exists (occurs_typ a) ts then
    rename a
  else
    a

let freshen_extyp ts (ExT(a, k, t) as s) =
  let a' = freshen_var ts a in
  if a' <> a then
    (assert (k <> ProdK[]); ExT(a', k, subst_typ [a, VarT(a', k)] t))
  else
    s

let intersect_row r1 r2 =
  List.filter (fun (l1, _) -> List.exists (fun (l2, _) -> l1 = l2) r2) r1

let diff_row r1 r2 =
  List.filter (fun (l1, _) -> List.for_all (fun (l2, _) -> l1 <> l2) r2) r1

let join_eff p1 p2 =
  match p1, p2 with
  | Pure, Pure -> Pure
  | _, _ -> Impure


(* String conversion *)

let verbose_binders_flag = ref false
let verbose_paths_flag = ref false

let string_of_eff_sort = function
  | Pure -> "pure"
  | Impure -> "impure"

let rec string_of_typ_sort = function
  | VarT(a, k) -> "abstract"
  | PrimT(t) -> Prim.string_of_typ t
  | StrT(r) -> "structure"
  | FunT(a, k, t, s, p) -> string_of_eff_sort p ^ " function"
  | TypT(ExT(a, ProdK[], t)) -> "small type"
  | TypT(s) -> "large type"
  | PackT(s) -> "package"
  | ProdT(r) -> "abstract"
  | LamT(a, k, t) -> "abstract"
  | DotT(t, l) -> string_of_typ_sort t ^ "." ^ l
  | AppT(t1, t2) -> string_of_typ_sort t1 ^ "(" ^ string_of_typ_sort t2 ^ ")"

let base_prec = 0
let binder_prec = 1
let app_prec = 2
let dot_prec = 2
let atom_prec = 2

let paren required_prec current_prec s =
    if required_prec > current_prec then "(" ^ s ^ ")" else s

let rec string_of_row' sep string_of' prec r =
    String.concat ", "
      (List.map (fun (l, t) -> l ^ sep ^ string_of' base_prec t) r)

let rec string_of_kind' prec = function
  | BaseK -> "*"
  | ProdK(kr) -> "{" ^ string_of_row' ":" string_of_kind' base_prec kr ^ "}"
  | FunK(k1, k2) ->
    paren prec binder_prec (
      string_of_kind' app_prec k1 ^ "->" ^ string_of_kind' binder_prec k2
    )

let rec as_tup = function
  | [] -> Some []
  | [_] -> None
  | tr ->
    if
      List.for_all (fun b -> b)
        (List.mapi (fun i (l, _) -> l = "_" ^ string_of_int (i + 1)) tr)
    then
      Some (List.map snd tr)
    else
      None

let rec string_of_typ' prec = function
  | VarT(a, k) -> a
  | PrimT(t) -> Prim.string_of_typ t
  | StrT(tr) ->
    (match as_tup tr with
    | Some ts ->
      "(" ^ String.concat ", " (List.map (string_of_typ' base_prec) ts) ^ ")"
    | None ->
      "{" ^ string_of_row' " : " string_of_typ' base_prec tr ^ "}"
    )
  | FunT(a, k, t, s, p) ->
    paren prec binder_prec (
      string_of_binder "!" a k ^
      string_of_typ' (binder_prec + 1) t ^
      (match p with Pure -> " => " | Impure -> " -> ") ^
      string_of_extyp' binder_prec s
    )
  | TypT(s) -> "[= " ^ string_of_extyp' base_prec s ^ "]"
  | PackT(s) -> "[" ^ string_of_extyp' base_prec s ^ "]"
  | ProdT(tr) -> "{" ^ string_of_row' " = " string_of_typ' base_prec tr ^ "}"
  | LamT(a, k, t) ->
    paren prec binder_prec (
      string_of_binder "\\" a k ^
      string_of_typ' binder_prec t
    )
  | DotT(t, l) ->
    if !verbose_paths_flag then
      paren prec dot_prec (string_of_typ' dot_prec t ^ "." ^ l)
    else
      l
  | AppT(t1, t2) ->
    paren prec app_prec (
      string_of_typ' app_prec t1 ^ "(" ^ string_of_typ' base_prec t2 ^ ")"
    )

and string_of_extyp' prec = function
  | ExT(a, k, t) ->
    paren prec binder_prec (
      string_of_binder "?" a k ^ string_of_typ' binder_prec t
    )

and string_of_binder sym a k =
  if k = ProdK[] then "" else
  sym ^ a ^
  (if k = BaseK || not !verbose_binders_flag then "" else
    ":" ^ string_of_kind' atom_prec k
  ) ^ " "


let string_of_kind = string_of_kind' base_prec
let string_of_typ = string_of_typ' base_prec
let string_of_extyp = string_of_extyp' base_prec

let string_of_norm_typ t = try string_of_typ (norm_typ t)
with Not_found -> "!! " ^ string_of_typ t  (* TODO: debug *)
let string_of_norm_extyp s = try string_of_extyp (norm_extyp s)
with Not_found -> "!! " ^ string_of_extyp s  (* TODO: debug *)
