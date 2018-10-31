(*
 * (c) 2014 Andreas Rossberg
 *)

(* Syntax *)

type lab = string
type var = string

type 'a row = (lab * 'a) list

type kind =
  | BaseK
  | ArrK of kind * kind
  | ProdK of kind row

type typ =
  | VarT of var
  | PrimT of Prim.typ
  | ArrT of typ * typ
  | ProdT of typ row
  | AllT of var * kind * typ
  | AnyT of var * kind * typ
  | LamT of var * kind * typ
  | AppT of typ * typ
  | TupT of typ row
  | DotT of typ * lab
  | RecT of var * kind * typ
  | InferT of typ lazy_t * int

type exp =
  | VarE of var
  | PrimE of Prim.const
  | IfE of exp * exp * exp
  | LamE of var * typ * exp
  | AppE of exp * exp
  | TupE of exp row
  | DotE of exp * lab
  | GenE of var * kind * exp
  | InstE of exp * typ
  | PackE of typ * exp * typ
  | OpenE of exp * var * var * exp
  | RollE of exp * typ
  | UnrollE of exp
  | RecE of var * typ * exp
  | LetE of exp * var * exp

exception Error of string


(* Helpers *)

let lab i = "_" ^ string_of_int i

let tup_row xs = List.mapi (fun i x -> lab (i + 1), x) xs

let lookup_lab l row =
  try List.assoc l row with Not_found -> raise (Error ("label " ^ l))

let rec force_typ = function
  | InferT(t', _) -> force_typ (Lazy.force t')
  | t -> t

let string_of_typ_fwd = ref (fun _ -> failwith "string_of_typ_fwd")
let string_of_typ t = !string_of_typ_fwd t
let string_of_kind_fwd = ref (fun _ -> failwith "string_of_kind_fwd")
let string_of_kind t = !string_of_kind_fwd t


(* Environments *)

module VarMap = Map.Make(String)

type env = {typ : kind VarMap.t; var : typ VarMap.t}

let empty = {typ = VarMap.empty; var = VarMap.empty}

let add_typ a k env = {env with typ = VarMap.add a k env.typ}
let add_val x t env = {env with var = VarMap.add x t env.var}

let lookup_typ a env =
  try VarMap.find a env.typ with Not_found -> raise (Error ("type " ^ a))
let lookup_val x env =
  try VarMap.find x env.var with Not_found -> raise (Error ("value " ^ x))


(* Renaming *)

module VarSet = Set.Make(String)

let basename x = try String.sub x 0 (String.index x '#') with Not_found -> x

let rename_for vars x =
  let x' = basename x in
  let rec iter i =
    let x'' = x' ^ string_of_int i in
    if VarSet.mem x'' vars then iter (i + 1) else x''
  in if VarSet.mem x' vars then iter 1 else x'

let renamings = ref VarMap.empty

let rename x =
  let x' = basename x in
  let n = try VarMap.find x' !renamings with Not_found ->
    let n = ref 0 in renamings := VarMap.add x' n !renamings; n
  in incr n; x' ^ "#" ^ string_of_int !n


(* Substitutions *)

type 'a subst = (var * 'a) list

let rec subst_row subst s = List.map (fun (l, z) -> l, subst s z)

let rec subst_typ s = function
  | VarT(a) -> (try List.assoc a s with Not_found -> VarT(a))
  | PrimT(t) -> PrimT(t)
  | ArrT(t1, t2) -> ArrT(subst_typ s t1, subst_typ s t2)
  | ProdT(tr) -> ProdT(subst_row subst_typ s tr)
  | AllT(a, k, t) ->
    let a' = rename a in AllT(a', k, subst_typ ([a, VarT(a')]@s) t)
  | AnyT(a, k, t) ->
    let a' = rename a in AnyT(a', k, subst_typ ([a, VarT(a')]@s) t)
  | LamT(a, k, t) ->
    let a' = rename a in LamT(a', k, subst_typ ([a, VarT(a')]@s) t)
  | AppT(t1, t2) -> AppT(subst_typ s t1, subst_typ s t2)
  | TupT(tr) -> TupT(subst_row subst_typ s tr)
  | DotT(t, l) -> DotT(subst_typ s t, l)
  | RecT(a, k, t) ->
    let a' = rename a in RecT(a', k, subst_typ ([a, VarT(a')]@s) t)
  | InferT(t', id) ->
    if Lazy.is_val t' then subst_typ s (Lazy.force t') else InferT(t', id)

let rec subst_typ_exp s = function
  | VarE(x) -> VarE(x)
  | PrimE(c) -> PrimE(c)
  | IfE(e1, e2, e3) ->
    IfE(subst_typ_exp s e1, subst_typ_exp s e2, subst_typ_exp s e3)
  | LamE(x, t, e) -> LamE(x, subst_typ s t, subst_typ_exp s e)
  | AppE(e1, e2) -> AppE(subst_typ_exp s e1, subst_typ_exp s e2)
  | TupE(er) -> TupE(subst_row subst_typ_exp s er)
  | DotE(e, l) -> DotE(subst_typ_exp s e, l)
  | GenE(a, k, e) ->
    let a' = rename a in GenE(a', k, subst_typ_exp ([a, VarT(a')]@s) e)
  | InstE(e, t) -> InstE(subst_typ_exp s e, subst_typ s t)
  | PackE(t1, e, t) -> PackE(subst_typ s t1, subst_typ_exp s e, subst_typ s t)
  | OpenE(e1, a, x, e2) ->
    let a' = rename a in
    OpenE(subst_typ_exp s e1, a', x, subst_typ_exp ([a, VarT(a')]@s) e2)
  | RollE(e, t) -> RollE(subst_typ_exp s e, subst_typ s t)
  | UnrollE(e) -> UnrollE(subst_typ_exp s e)
  | RecE(x, t, e) -> RecE(x, subst_typ s t, subst_typ_exp s e)
  | LetE(e1, x, e2) -> LetE(subst_typ_exp s e1, x, subst_typ_exp s e2)

let rec subst_exp s = function
  | VarE(x) -> (try List.assoc x s with Not_found -> VarE(x))
  | PrimE(c) -> PrimE(c)
  | IfE(e1, e2, e3) -> IfE(subst_exp s e1, subst_exp s e2, subst_exp s e3)
  | LamE(x, t, e) ->
    let x' = rename x in LamE(x', t, subst_exp ([x, VarE(x')]@s) e)
  | AppE(e1, e2) -> AppE(subst_exp s e1, subst_exp s e2)
  | TupE(er) -> TupE(subst_row subst_exp s er)
  | DotE(e, l) -> DotE(subst_exp s e, l)
  | GenE(a, k, e) -> GenE(a, k, subst_exp s e)
  | InstE(e, t) -> InstE(subst_exp s e, t)
  | PackE(t1, e, t) -> PackE(t1, subst_exp s e, t)
  | OpenE(e1, a, x, e2) ->
    let x' = rename x in
    OpenE(subst_exp s e1, a, x', subst_exp ([x, VarE(x')]@s) e2)
  | RollE(e, t) -> RollE(subst_exp s e, t)
  | UnrollE(e) -> UnrollE(subst_exp s e)
  | RecE(x, t, e) ->
    let x' = rename x in RecE(x', t, subst_exp ([x, VarE(x')]@s) e)
  | LetE(e1, x, e2) ->
    let x' = rename x in
    LetE(subst_exp s e1, x', subst_exp ([x, VarE(x')]@s) e2)


(* Normalisation *)

let rec varT(a, k) = varT' (VarT(a)) k
and varT' t = function
  | BaseK -> t
  | ArrK(k1, k2) ->
    let a = rename "eta" in LamT(a, k1, varT' (AppT(t, varT(a, k1))) k2)
  | ProdK(kr) ->
    TupT(List.map (fun (l, k) -> l, varT' (DotT(t, l)) k) kr)


let norm_row norm = List.map (fun (l, z) -> l, norm z)

let rec norm_typ = function
  | VarT(a) -> VarT(a)
  | PrimT(t) -> PrimT(t)
  | ArrT(t1, t2) -> ArrT(norm_typ t1, norm_typ t2)
  | ProdT(tr) -> ProdT(norm_row norm_typ tr)
  | AllT(a, k, t) -> AllT(a, k, norm_typ t)
  | AnyT(a, k, t) -> AnyT(a, k, norm_typ t)
  | LamT(a, k, t) -> LamT(a, k, t)
  | AppT(t1, t2) ->
    (match norm_typ t1 with
    | LamT(a, k, t) -> norm_typ (subst_typ [a, t2] t)
    | t1' -> AppT(t1', norm_typ t2)
    )
  | TupT(tr) -> TupT(norm_row norm_typ tr)
  | DotT(t, l) ->
    (match norm_typ t with
    | TupT(tr) -> norm_typ (lookup_lab l tr)
    | t' -> DotT(t', l)
    )
  | RecT(a, k, t) -> RecT(a, k, norm_typ t)
  | InferT(t', id) ->
    if Lazy.is_val t' then norm_typ (Lazy.force t') else InferT(t', id)


let rec consts_of_val = function
  | PrimE(c) -> [c]
  | TupE(vr) -> List.map (fun (l, v) -> List.hd (consts_of_val v)) vr
  | _ -> raise (Error "AppE2")

let val_of_consts = function
  | [c] -> PrimE(c)
  | cs -> TupE(tup_row (List.map (fun c -> PrimE(c)) cs))

let rec norm_exp = function
  | VarE(x) -> VarE(x)
  | PrimE(c) -> PrimE(c)
  | IfE(e1, e2, e3) ->
    (match norm_exp e1 with
    | PrimE(Prim.BoolV(b)) -> norm_exp (if b then e2 else e3)
    | _ -> raise (Error "IfE")
    )
  | LamE(x, t, e) -> LamE(x, t, e)
  | AppE(e1, e2) ->
    (match norm_exp e1, norm_exp e2 with
    | LamE(x, t, e), v2 -> norm_exp (subst_exp [x, v2] e)
    | PrimE(Prim.FunV f), v2 -> val_of_consts (f.Prim.fn (consts_of_val v2))
    | _ -> raise (Error "AppE")
    )
  | TupE(er) -> TupE(norm_row norm_exp er)
  | DotE(e, l) ->
    (match norm_exp e with
    | TupE(vr) -> lookup_lab l vr
    | _ -> raise (Error "DotE")
    )
  | GenE(a, k, e) -> GenE(a, k, e)
  | InstE(e1, t) ->
    (match norm_exp e1 with
    | GenE(a, k, e) -> norm_exp (subst_typ_exp [a, t] e)
    | _ -> raise (Error "InstE")
    )
  | PackE(t, e, t') -> PackE(t, norm_exp e, t')
  | OpenE(e1, a, x, e2) ->
    (match norm_exp e1 with
    | PackE(t, v, t') -> norm_exp (subst_exp [x, v] (subst_typ_exp [a, t] e2))
    | _ -> raise (Error "OpenE")
    )
  | RollE(e, t) -> RollE(norm_exp e, t)
  | UnrollE(e) ->
    (match norm_exp e with
    | RollE(v, t) -> v
    | _ -> raise (Error "UnrollE")
    )
  | RecE(x, t, e) as e' -> norm_exp (subst_exp [x, e'] e)
  | LetE(e1, x, e2) -> let v1 = norm_exp e1 in norm_exp (subst_exp [x, v1] e2)


(* Equality *)

let equal_row equal r1 r2 =
  List.length r1 = List.length r2 &&
  List.for_all2 (fun (l1, z1) (l2, z2) -> l1 = l2 && equal z1 z2) r1 r2

let rec equal_typ t1 t2 = equal_typ' (norm_typ t1) (norm_typ t2)
and equal_typ' t1 t2 =
  match t1, t2 with
  | VarT(a1), VarT(a2) -> a1 = a2
  | PrimT(t1), PrimT(t2) -> t1 = t2
  | ArrT(t11, t12), ArrT(t21, t22) -> equal_typ' t11 t21 && equal_typ' t12 t22
  | ProdT(tr1), ProdT(tr2) -> equal_row equal_typ' tr1 tr2
  | AllT(a1, k1, t1), AllT(a2, k2, t2) ->
    k1 = k2 && equal_typ t1 (subst_typ [a2, VarT(a1)] t2)
  | AnyT(a1, k1, t1), AnyT(a2, k2, t2) ->
    k1 = k2 && equal_typ t1 (subst_typ [a2, VarT(a1)] t2)
  | LamT(a1, k1, t1), LamT(a2, k2, t2) ->
    k1 = k2 && equal_typ t1 (subst_typ [a2, VarT(a1)] t2)
  | AppT(t11, t12), AppT(t21, t22) -> equal_typ' t11 t21 && equal_typ' t12 t22
  | TupT(tr1), TupT(tr2) -> equal_row equal_typ' tr1 tr2
  | DotT(t1, l1), DotT(t2, l2) -> equal_typ' t1 t2 && l1 = l2
  | RecT(a1, k1, t1), RecT(a2, k2, t2) ->
    k1 = k2 && equal_typ t1 (subst_typ [a2, VarT(a1)] t2)
  | InferT(t1', id1), InferT(t2', id2) when id1 = id2 -> true
  | InferT(t1', _), _ when Lazy.is_val t1' -> equal_typ (Lazy.force t1') t2
  | _, InferT(t2', _) when Lazy.is_val t2' -> equal_typ t1 (Lazy.force t2')
  | _ -> false


(* Unrolling *)

let rec unroll_typ' = function
  | AppT(t1, t2) -> AppT(unroll_typ' t1, t2)
  | DotT(t, l) -> DotT(unroll_typ' t, l)
  | RecT(a, k, t) as t' -> subst_typ [a, t'] t
  | _ -> raise (Error "unroll")

let unroll_typ t = try Some (unroll_typ' t) with Error _ -> None


(* Checking *)

let infer_row infer env r = List.map (fun (l, z) -> l, infer env z) r
let check_row check env r q s = List.iter (fun (l, z) -> check env z q s) r

let rec infer_typ env = function
  | VarT(a) -> lookup_typ a env
  | PrimT(t) -> BaseK
  | ArrT(t1, t2) ->
    check_typ env t1 BaseK "ArrT1"; check_typ env t2 BaseK "ArrT2"; BaseK
  | ProdT(tr) -> check_row check_typ env tr BaseK "ProdT"; BaseK
  | AllT(a, k, t) -> check_typ (add_typ a k env) t BaseK "AllT"; BaseK
  | AnyT(a, k, t) -> check_typ (add_typ a k env) t BaseK "AnyT"; BaseK
  | LamT(a, k, t) -> ArrK(k, infer_typ (add_typ a k env) t)
  | AppT(t1, t2) ->
    (match infer_typ env t1 with
    | ArrK(k2, k) -> check_typ env t2 k2 "AppT2"; k
    | _ -> raise (Error "AppT1")
    )
  | TupT(tr) -> ProdK(infer_row infer_typ env tr)
  | DotT(t, l) ->
    (match infer_typ env t with
    | ProdK(kr) -> lookup_lab l kr
    | _ -> raise (Error "DotT1")
    )
  | RecT(a, k, t) -> check_typ (add_typ a k env) t k "RecT"; k
  | InferT(t', id) -> BaseK

and check_typ env t k s = if infer_typ env t <> k then raise (Error s)

let infer_prim_typ = function
  | Prim.VarT -> VarT("a")
  | t -> PrimT(t)

let infer_prim_typs = function
  | [t] -> infer_prim_typ t
  | ts -> ProdT(tup_row (List.map infer_prim_typ ts))

let infer_prim_fun {Prim.typ = ts1, ts2} =
  ArrT(infer_prim_typs ts1, infer_prim_typs ts2)

let infer_const = function
  | Prim.FunV(f) -> infer_prim_fun f
  | c -> PrimT(Prim.typ_of_const c)

let rec infer_exp env = function
  | VarE(x) -> lookup_val x env
  | PrimE(c) -> infer_const c
  | IfE(e1, e2, e3) ->
    check_exp env e1 (PrimT(Prim.BoolT)) "IfE1";
    let t = infer_exp env e2 in
    check_exp env e3 t "IfE";
    t
  | LamE(x, t, e) -> ArrT(t, infer_exp (add_val x t env) e)
  | AppE(e1, e2) ->
    (match force_typ (infer_exp env e1) with
    | ArrT(t2, t) -> check_exp env e2 t2 "AppE2"; t
    | _ -> raise (Error "AppE1")
    )
  | TupE(er) -> ProdT(infer_row infer_exp env er)
  | DotE(e, l) ->
    (match force_typ (infer_exp env e) with
    | ProdT(tr) -> lookup_lab l tr
    | _ -> raise (Error "DotE1")
    )
  | GenE(a, k, e) -> AllT(a, k, infer_exp (add_typ a k env) e)
  | InstE(e, t) ->
    (match force_typ (infer_exp env e) with
    | AllT(a, k, t') -> check_typ env t k "InstE"; subst_typ [a, t] t'
    | _ -> raise (Error "InstE")
    )
  | PackE(t, e, t') ->
    check_typ env t' BaseK "PackE";
    (match force_typ t' with
    | AnyT(a, k, t'') ->
      check_typ env t k "PackE1";
      check_exp env e (subst_typ [a, t] t'') "PackE2";
      t'
    | _ -> raise (Error "PackE")
    )
  | OpenE(e1, a, x, e2) ->
    (match force_typ (infer_exp env e1) with
    | AnyT(a1, k, t1) ->
      let t =
        infer_exp (add_val x (subst_typ [a1, VarT(a)] t1) (add_typ a k env)) e2
      in check_typ env t BaseK "OpenE2"; t
    | _ -> raise (Error "OpenE")
    )
  | RollE(e, t) ->
    check_typ env t BaseK "PackE";
    (match unroll_typ t with
    | Some t' ->
      check_exp env e t' "RollE";
      t
    | None -> raise (Error "RollE")
    )
  | UnrollE(e) ->
    (match unroll_typ (infer_exp env e) with
    | Some t' -> t'
    | None -> raise (Error "UnrollE")
    )
  | RecE(x, t, e) ->
    check_typ env t BaseK "RecE1";
    check_exp (add_val x t env) e t "RecE2";
    t
  | LetE(e1, x, e2) ->
    let t1 = infer_exp env e1 in
    infer_exp (add_val x t1 env) e2

and check_exp env e t s =
  if not (equal_typ (infer_exp env e) t) then raise (Error s)


(* String conversion *)

let verbose_exp_flag = ref true
let verbose_typ_flag = ref true

let string_of_row sep string_of r =
    String.concat ", " (List.map (fun (l, z) -> l ^ sep ^ string_of z) r)

let rec string_of_kind = function
  | BaseK -> "*"
  | ArrK(k1, k2) -> "(" ^ string_of_kind k1 ^ "->" ^ string_of_kind k2 ^ ")"
  | ProdK[] -> "1"
  | ProdK(kr) -> "{" ^ string_of_row ":" string_of_kind kr ^ "}"

let rec string_of_typ = function
  | VarT(a) -> a
  | PrimT(t) -> Prim.string_of_typ t
  | ArrT(t1, t2) -> "(" ^ string_of_typ t1 ^ " -> " ^ string_of_typ t2 ^ ")"
  | ProdT[] -> "1"
  | ProdT(tr) -> "{" ^ string_of_row " : " string_of_typ tr ^ "}"
  | AllT(a, k, t) ->
    "(" ^ "!" ^ a ^ ":" ^ string_of_kind k ^ ". " ^ string_of_typ t ^ ")"
  | AnyT(a, k, t) ->
    "(" ^ "?" ^ a ^ ":" ^ string_of_kind k ^ ". " ^ string_of_typ t ^ ")"
  | LamT(a, k, t) ->
    "(" ^ "\\" ^ a ^ ":" ^ string_of_kind k ^ ". " ^ string_of_typ t ^ ")"
  | AppT(t1, t2) -> string_of_typ t1 ^ "(" ^ string_of_typ t2 ^ ")"
  | TupT(tr) -> "{" ^ string_of_row " = " string_of_typ tr ^ "}"
  | DotT(t, l) -> string_of_typ t ^ "." ^ l
  | RecT(a, k, t) ->
    "(" ^ "@" ^ a ^ ":" ^ string_of_kind k ^ ". " ^ string_of_typ t ^ ")"
  | InferT(t', id) ->
    if Lazy.is_val t' then string_of_typ (Lazy.force t')
    else "'" ^ string_of_int id

let rec string_of_exp = function
  | VarE(x) -> x
  | PrimE(c) -> Prim.string_of_const c
  | IfE(e1, e2, e3) ->
    "(if " ^ string_of_exp e1 ^ " then " ^ string_of_exp e2 ^
      " else " ^ string_of_exp e3 ^ ")"
  | LamE(x, t, e) ->
    "(\\" ^ x ^
    (if !verbose_typ_flag then ":" ^ string_of_typ t else "") ^
    ". " ^
    (if !verbose_exp_flag then string_of_exp e else "_") ^
    ")"
  | AppE(e1, e2) -> "(" ^ string_of_exp e1 ^ " " ^ string_of_exp e2 ^ ")"
  | TupE(er) -> "{" ^ string_of_row " = " string_of_exp er ^ "}"
  | DotE(e, l) -> string_of_exp e ^ "." ^ l
  | GenE(a, k, e) ->
    "(\\" ^ a ^ ":" ^ string_of_kind k ^ ". " ^ string_of_exp e ^ ")"
  | InstE(e, t) -> "(" ^ string_of_exp e ^ " " ^ string_of_typ t ^ ")"
  | PackE(t1, e, t2) ->
    "pack(" ^ string_of_typ t1 ^ ", " ^ string_of_exp e ^ ")" ^
    (if !verbose_typ_flag then ":" ^ string_of_typ t2 else "")
  | OpenE(e1, a, x, e2) ->
    "(unpack(" ^ a ^ "," ^ x ^ ") = " ^ string_of_exp e1 ^
    " in " ^ string_of_exp e2 ^ ")"
  | RollE(e, t) ->
    "roll(" ^ string_of_exp e ^ ")" ^
    (if !verbose_typ_flag then ":" ^ string_of_typ t else "")
  | UnrollE(e) -> "unroll(" ^ string_of_exp e ^ ")"
  | RecE(x, t, e) ->
    "(rec " ^ x ^
    (if !verbose_typ_flag then ":" ^ string_of_typ t else "") ^
    ". " ^
    (if !verbose_exp_flag then string_of_exp e else "_") ^
    ")"
  | LetE(e1, x, e2) ->
    "(let " ^ x ^ " = " ^ string_of_exp e1 ^ " in " ^ string_of_exp e2 ^ ")"

let _ = string_of_typ_fwd := string_of_typ
let _ = string_of_kind_fwd := string_of_kind
