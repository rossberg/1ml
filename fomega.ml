(*
 * (c) 2014 Andreas Rossberg
 *)

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
  | FunT of var * kind * typ
  | AppT of typ * typ
  | StrT of typ row
  | DotT of typ * lab

type exp =
  | VarE of var
  | PrimE of Prim.const
  | IfE of exp * exp * exp
  | FunE of var * typ * exp
  | AppE of exp * exp
  | StrE of exp row
  | DotE of exp * lab
  | GenE of var * kind * exp
  | InstE of exp * typ
  | PackE of typ * exp * typ
  | OpenE of exp * var * var * exp

type env = {typ : (var * kind) list; var : (var * typ) list}
type 'a subst = (var * 'a) list

exception Error of string


(* Helpers *)

let rec letE(ds, e) =
  match ds with
  | [] -> e
  | (x, t, e1)::ds' -> letE(ds', AppE(FunE(x, t, e), e1))


(* Environments *)

let empty = {typ = []; var = []}

let add_typ a k env = {env with typ = (a, k)::env.typ}
let add_val x t env = {env with var = (x, t)::env.var}

let lookup_typ a env =
  try List.assoc a env.typ with Not_found -> raise (Error ("type " ^ a))
let lookup_val x env =
  try List.assoc x env.var with Not_found -> raise (Error ("value " ^ x))
let lookup_lab l row =
  try List.assoc l row with Not_found -> raise (Error ("label " ^ l))


(* Renaming *)

module VarMap = Map.Make(String)

let renamings = ref VarMap.empty

let rename x =
  let x' = try String.sub x 0 (String.index x '#') with Not_found -> x in
  let n = try VarMap.find x' !renamings with Not_found ->
    let n = ref 0 in renamings := VarMap.add x' n !renamings; n
  in incr n; x' ^ "#" ^ string_of_int !n


(* Substitutions *)

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
  | FunT(a, k, t) ->
    let a' = rename a in FunT(a', k, subst_typ ([a, VarT(a')]@s) t)
  | AppT(t1, t2) -> AppT(subst_typ s t1, subst_typ s t2)
  | StrT(tr) -> StrT(subst_row subst_typ s tr)
  | DotT(t, l) -> DotT(subst_typ s t, l)

let rec subst_typ_exp s = function
  | VarE(x) -> VarE(x)
  | PrimE(c) -> PrimE(c)
  | IfE(e1, e2, e3) ->
    IfE(subst_typ_exp s e1, subst_typ_exp s e2, subst_typ_exp s e3)
  | FunE(x, t, e) -> FunE(x, subst_typ s t, subst_typ_exp s e)
  | AppE(e1, e2) -> AppE(subst_typ_exp s e1, subst_typ_exp s e2)
  | StrE(er) -> StrE(subst_row subst_typ_exp s er)
  | DotE(e, l) -> DotE(subst_typ_exp s e, l)
  | GenE(a, k, e) ->
    let a' = rename a in GenE(a', k, subst_typ_exp ([a, VarT(a')]@s) e)
  | InstE(e, t) -> InstE(subst_typ_exp s e, subst_typ s t)
  | PackE(t1, e, t) -> PackE(subst_typ s t1, subst_typ_exp s e, subst_typ s t)
  | OpenE(e1, a, x, e2) ->
    let a' = rename a in
    OpenE(subst_typ_exp s e1, a', x, subst_typ_exp ([a, VarT(a')]@s) e2)

let rec subst_exp s = function
  | VarE(x) -> (try List.assoc x s with Not_found -> VarE(x))
  | PrimE(c) -> PrimE(c)
  | IfE(e1, e2, e3) -> IfE(subst_exp s e1, subst_exp s e2, subst_exp s e3)
  | FunE(x, t, e) ->
    let x' = rename x in FunE(x', t, subst_exp ([x, VarE(x')]@s) e)
  | AppE(e1, e2) -> AppE(subst_exp s e1, subst_exp s e2)
  | StrE(er) -> StrE(subst_row subst_exp s er)
  | DotE(e, l) -> DotE(subst_exp s e, l)
  | GenE(a, k, e) -> GenE(a, k, subst_exp s e)
  | InstE(e, t) -> InstE(subst_exp s e, t)
  | PackE(t1, e, t) -> PackE(t1, subst_exp s e, t)
  | OpenE(e1, a, x, e2) ->
    let x' = rename x in
    OpenE(subst_exp s e1, a, x', subst_exp ([x, VarE(x')]@s) e2)


(* Normalisation *)

let rec varT(a, k) = varT' (VarT(a)) k
and varT' t = function
  | BaseK -> t
  | ArrK(k1, k2) ->
    let a = rename "eta" in FunT(a, k1, varT' (AppT(t, varT(a, k1))) k2)
  | ProdK(kr) ->
    StrT(List.map (fun (l, k) -> l, varT' (DotT(t, l)) k) kr)


let norm_row norm = List.map (fun (l, z) -> l, norm z)

let rec norm_typ = function
  | VarT(a) -> VarT(a)
  | PrimT(t) -> PrimT(t)
  | ArrT(t1, t2) -> ArrT(norm_typ t1, norm_typ t2)
  | ProdT(tr) -> ProdT(norm_row norm_typ tr)
  | AllT(a, k, t) -> AllT(a, k, norm_typ t)
  | AnyT(a, k, t) -> AnyT(a, k, norm_typ t)
  | FunT(a, k, t) -> FunT(a, k, t)
  | AppT(t1, t2) ->
    (match norm_typ t1 with
    | FunT(a, k, t) -> norm_typ (subst_typ [a, t2] t)
    | t1' -> AppT(t1', norm_typ t2)
    )
  | StrT(tr) -> StrT(norm_row norm_typ tr)
  | DotT(t, l) ->
    (match norm_typ t with
    | StrT(tr) -> norm_typ (lookup_lab l tr)
    | t' -> DotT(t', l)
    )


let rec consts_of_val = function
  | PrimE(c) -> [c]
  | StrE(vr) -> List.map (fun (l, v) -> List.hd (consts_of_val v)) vr
  | _ -> raise (Error "AppE2")

let val_of_consts = function
  | [c] -> PrimE(c)
  | cs -> StrE(List.mapi (fun i c -> "_" ^ string_of_int (i + 1), PrimE(c)) cs)

let rec norm_exp = function
  | VarE(x) -> VarE(x)
  | PrimE(c) -> PrimE(c)
  | IfE(e1, e2, e3) ->
    (match norm_exp e1 with
    | PrimE(Prim.BoolV(b)) -> norm_exp (if b then e2 else e3)
    | _ -> raise (Error "IfE")
    )
  | FunE(x, t, e) -> FunE(x, t, e)
  | AppE(e1, e2) ->
    (match norm_exp e1, norm_exp e2 with
    | FunE(x, t, e), v2 -> norm_exp (subst_exp [x, v2] e)
    | PrimE(Prim.FunV f), v2 -> val_of_consts (f.Prim.fn (consts_of_val v2))
    | _ -> raise (Error "AppE")
    )
  | StrE(er) -> StrE(norm_row norm_exp er)
  | DotE(e, l) ->
    (match norm_exp e with
    | StrE(vr) -> lookup_lab l vr
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


(* Equality *)

let equal_row equal r1 r2 =
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
  | FunT(a1, k1, t1), FunT(a2, k2, t2) ->
    k1 = k2 && equal_typ t1 (subst_typ [a2, VarT(a1)] t2)
  | AppT(t11, t12), AppT(t21, t22) -> equal_typ' t11 t21 && equal_typ' t12 t22
  | StrT(tr1), StrT(tr2) -> equal_row equal_typ' tr1 tr2
  | DotT(t1, l1), DotT(t2, l2) -> equal_typ' t1 t2 && l1 = l2
  | _ -> false


(* Checking *)

let infer_row infer env r = List.map (fun (l, z) -> l, infer env z) r
let check_row check env r q s = List.iter (fun (l, z) -> check env z q s) r

let rec check_typ env t k s = if infer_typ env t <> k then raise (Error s)
and infer_typ env = function
  | VarT(a) -> lookup_typ a env
  | PrimT(t) -> BaseK
  | ArrT(t1, t2) ->
    check_typ env t1 BaseK "ArrT1"; check_typ env t2 BaseK "ArrT2"; BaseK
  | ProdT(tr) -> check_row check_typ env tr BaseK "StrT"; BaseK
  | AllT(a, k, t) -> check_typ (add_typ a k env) t BaseK "AllT"; BaseK
  | AnyT(a, k, t) -> check_typ (add_typ a k env) t BaseK "AnyT"; BaseK
  | FunT(a, k, t) -> infer_typ (add_typ a k env) t
  | AppT(t1, t2) ->
    (match infer_typ env t1 with
    | ArrK(k2, k) -> check_typ env t2 k2 "AppT2"; k
    | _ -> raise (Error "AppT1")
    )
  | StrT(tr) -> ProdK(infer_row infer_typ env tr)
  | DotT(t, l) ->
    (match infer_typ env t with
    | ProdK(kr) -> lookup_lab l kr
    | _ -> raise (Error "DotT1")
    )


let infer_prim_typ = function
  | Prim.VarT -> VarT("a")
  | t -> PrimT(t)

let infer_prim_typs = function
  | [t] -> infer_prim_typ t
  | ts ->
    StrT(List.mapi (fun i t -> "_" ^ string_of_int (i+1), infer_prim_typ t) ts)

let infer_prim_fun {Prim.typ = ts1, ts2} =
  ArrT(infer_prim_typs ts1, infer_prim_typs ts2)

let infer_const = function
  | Prim.FunV(f) -> infer_prim_fun f
  | c -> PrimT(Prim.typ_of_const c)


let rec check_exp env e t s =
  if not (equal_typ (infer_exp env e) t) then raise (Error s)
and infer_exp env = function
  | VarE(x) -> lookup_val x env
  | PrimE(c) -> infer_const c
  | IfE(e1, e2, e3) ->
    check_exp env e1 (PrimT(Prim.BoolT)) "IfE1";
    let t = infer_exp env e2 in
    check_exp env e3 t "IfE";
    t
  | FunE(x, t, e) -> ArrT(t, infer_exp (add_val x t env) e)
  | AppE(e1, e2) ->
    (match infer_exp env e1 with
    | ArrT(t2, t) -> check_exp env e2 t2 "AppE2"; t
    | _ -> raise (Error "AppE1")
    )
  | StrE(er) -> ProdT(infer_row infer_exp env er)
  | DotE(e, l) ->
    (match infer_exp env e with
    | ProdT(tr) -> lookup_lab l tr
    | _ -> raise (Error "DotE1")
    )
  | GenE(a, k, e) -> AllT(a, k, infer_exp (add_typ a k env) e)
  | InstE(e, t) ->
    (match infer_exp env e with
    | AllT(a, k, t') -> check_typ env t k "InstE"; subst_typ [a, t] t'
    | _ -> raise (Error "InstE")
    )
  | PackE(t, e, t') ->
    check_typ env t' BaseK "PackE";
    (match t' with
    | AnyT(a, k, t'') ->
      check_typ env t k "PackE1";
      check_exp env e (subst_typ [a, t] t'') "PackE2";
      t'
    | _ -> raise (Error "PackE")
    )
  | OpenE(e1, a, x, e2) ->
    (match infer_exp env e1 with
    | AnyT(a1, k, t1) ->
      let t = infer_exp (add_val x t1 (add_typ a1 k env)) e2 in
      check_typ env t BaseK "OpenE2"; t
    | _ -> raise (Error "OpenE")
    )


(* String conversion *)

let string_of_row sep string_of r =
    String.concat ", " (List.map (fun (l, z) -> l ^ sep ^ string_of z) r)

let rec string_of_exp = function
  | VarE(x) -> x
  | PrimE(c) -> Prim.string_of_const c
  | FunE(x, t, e) -> "(fun)"
  | StrE(er) -> "{" ^ string_of_row " = " string_of_exp er ^ "}"
  | GenE(a, t, e) -> "(poly)"
  | PackE(t, e, _) -> "(pack)"
  | _ -> "(stuck)"
