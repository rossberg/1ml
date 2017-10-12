(*
 * (c) 2014 Andreas Rossberg
 *)

open Source

type var = (string, unit) phrase

type eff = (eff', unit) phrase
and eff' =
  | Pure
  | Impure

type typ = (typ', unit) phrase
and typ' =
  | PathT of exp
  | PrimT of string
  | TypT
  | StrT of dec
  | FunT of var * typ * typ * eff
  | PackT of typ
  | LikeT of exp
  | WithT of typ * var list * exp

and dec = (dec', unit) phrase
and dec' =
  | EmptyD
  | SeqD of dec * dec
  | VarD of var * typ
  | InclD of typ

and exp = (exp', unit) phrase
and exp' =
  | VarE of var
  | PrimE of Prim.const
  | TypE of typ
  | StrE of bind
  | FunE of var * typ * exp
  | PackE of var * typ
  | IfE of var * exp * exp * typ
  | DotE of exp * var
  | AppE of var * var
  | UnpackE of var * typ

and bind = (bind', unit) phrase
and bind' =
  | EmptyB
  | SeqB of bind * bind
  | VarB of var * exp
  | InclB of exp


let var_counts = ref []
let var s =
  let count = try List.assoc s !var_counts with Not_found ->
    let count = ref 0 in var_counts := (s, count) :: !var_counts; count
  in incr count; s ^ "$" ^ string_of_int !count


(* Sugar *)

let rec tupT(ts) = StrT(tupT' 1 ts)
and tupT' n = function
  | [] -> EmptyD@@nowhere_region
  | t::ts ->
    let x' = "_" ^ string_of_int n in
    let d = tupT' (n + 1) ts in
    SeqD(VarD(x'@@t.at, t)@@t.at, d)@@
      (match d.it with EmptyD -> t.at | _ -> span[t.at; d.at])

let rec tupE(es) = StrE(tupE' 1 es)
and tupE' n = function
  | [] -> EmptyB@@nowhere_region
  | e::es ->
    let x' = "_" ^ string_of_int n in
    let b = tupE' (n + 1) es in
    SeqB(VarB(x'@@e.at, e)@@e.at, b)@@
      (match b.it with EmptyB -> e.at | _ -> span[e.at; b.at])

let rec funT(ps, t, f) = (funT'(ps, t, f)).it
and funT'(ps, t, f) =
  match ps with
  | [] -> t
  | p::ps' ->
    FunT(fst p.it, snd p.it, funT'(ps', t, f), f.it@@f.at)@@span[p.at; f.at]

let rec funE(ps, e) = (funE'(ps, e)).it
and funE'(ps, e) =
  match ps with
  | [] -> e
  | p::ps' -> FunE(fst p.it, snd p.it, funE'(ps', e))@@span[p.at; e.at]

let letE(b, e) =
  let x' = var "let" in
  let b2 = VarB(x'@@e.at, e)@@e.at in
  DotE(StrE(SeqB(b, b2)@@span[b.at; e.at])@@span[b.at; e.at], x'@@e.at)

let letT(b, t) = PathT(letE(b, TypE(t)@@t.at)@@span[b.at; t.at])
let letD(b, d) = InclD(letT(b, StrT(d)@@d.at)@@span[b.at; d.at])
let letB(b, b') = InclB(letE(b, StrE(b')@@b'.at)@@span[b.at; b'.at])

let doE(e) = letE(VarB("_"@@e.at, e)@@e.at, tupE[]@@e.at)
let doB(e) = letB(VarB("_"@@e.at, e)@@e.at, EmptyB@@e.at)

let ifE(e1, e2, e3, t) =
  match e1.it with
  | VarE(x) -> IfE(x, e2, e3, t)
  | _ ->
    let x' = var "if" in
    let e = IfE(x'@@e1.at, e2, e3, t)@@span[e1.at; t.at] in
    letE(VarB(x'@@e1.at, e1)@@e1.at, e)

let orE(e1, e2) =
  ifE(e1, PrimE(Prim.BoolV(true))@@e1.at, e2,
    PrimT("bool")@@span[e1.at; e2.at])
let andE(e1, e2) =
  ifE(e1, e2, PrimE(Prim.BoolV(false))@@e1.at,
    PrimT("bool")@@span[e1.at; e2.at])

let appE(e1, e2) =
  match e1.it, e2.it with
  | VarE(x1), VarE(x2) -> AppE(x1, x2)
  | VarE(x1), _ ->
    let x2' = var "app2" in
    letE(VarB(x2'@@e2.at, e2)@@e2.at, AppE(x1, x2'@@e2.at)@@span[e1.at; e2.at])
  | _, VarE(x2) ->
    let x1' = var "app1" in
    letE(VarB(x1'@@e1.at, e1)@@e1.at, AppE(x1'@@e1.at, x2)@@span[e1.at; e2.at])
  | _, _ ->
    let x1' = var "app1" in
    let x2' = var "app2" in
    let b1 = VarB(x1'@@e1.at, e1)@@e1.at in
    let b2 = VarB(x2'@@e2.at, e2)@@e2.at in
    let b = SeqB(b1, b2)@@span[e1.at; e2.at] in
    letE(b, AppE(x1'@@e1.at, x2'@@e2.at)@@span[e1.at; e2.at])

let packE(e, t) =
  match e.it with
  | VarE(x) -> PackE(x, t)
  | _ ->
    let x' = var "pack" in
    letE(VarB(x'@@e.at, e)@@e.at, PackE(x'@@e.at, t)@@span[e.at; t.at])

let unpackE(e, t) =
  match e.it with
  | VarE(x) -> UnpackE(x, t)
  | _ ->
    let x' = var "pack" in
    letE(VarB(x'@@e.at, e)@@e.at, UnpackE(x'@@e.at, t)@@span[e.at; t.at])

let annotE(e, t) =
  let x' = var "annot" in
  appE(FunE(x'@@t.at, t, VarE(x'@@t.at)@@t.at)@@span[e.at; t.at], e)

let sealE(e, t) =
  unpackE(packE(e, t)@@span[e.at; t.at], t)   (* TODO: clone t! *)


(* String conversion *)

let node label = function
  | [] -> label
  | args -> label ^ "(" ^ String.concat ", " args ^ ")"

let label_of_eff p =
  match p.it with
  | Pure -> "P"
  | Impure -> "I"

let label_of_typ t =
  match t.it with
  | PathT _ -> "PathT"
  | PrimT _ -> "PrimT"
  | TypT -> "TypT"
  | StrT _ -> "StrT"
  | FunT _ -> "FunT"
  | PackT _ -> "PackT"
  | LikeT _ -> "LikeT"
  | WithT _ -> "WithT"

let label_of_dec d =
  match d.it with
  | EmptyD -> "EmptyD"
  | SeqD _ -> "SeqD"
  | VarD _ -> "VarD"
  | InclD _ -> "InclD"

let label_of_exp e =
  match e.it with
  | VarE _ -> "VarE"
  | PrimE _ -> "PrimE"
  | TypE _ -> "TypT"
  | StrE _ -> "StrE"
  | FunE _ -> "FunE"
  | PackE _ -> "PackE"
  | IfE _ -> "IfE"
  | DotE _ -> "DotE"
  | AppE _ -> "AppE"
  | UnpackE _ -> "UnpackE"

let label_of_bind b =
  match b.it with
  | EmptyB -> "EmptyB"
  | SeqB _ -> "SeqB"
  | VarB _ -> "VarB"
  | InclB _ -> "InclB"


let string_of_var x = x.it

let string_of_eff p = label_of_eff p

let rec string_of_typ t =
  let node' = node (label_of_typ t) in
  match t.it with
  | PathT(e) -> node' [string_of_exp e]
  | PrimT(n) -> node' ["\"" ^ n ^"\""]
  | TypT -> node' []
  | StrT(d) -> node' [string_of_dec d]
  | FunT(x, t1, t2, p) ->
    node' [string_of_var x; string_of_typ t1; string_of_typ t2; string_of_eff p]
  | PackT(t) -> node' [string_of_typ t]
  | LikeT(e) -> node' [string_of_exp e]
  | WithT(t, xs, e) ->
    node' ([string_of_typ t] @ List.map string_of_var xs @ [string_of_exp e])

and string_of_dec d =
  let node' = node (label_of_dec d) in
  match d.it with
  | EmptyD -> node' []
  | SeqD(d1, d2) -> node' [string_of_dec d1; string_of_dec d2]
  | VarD(x, t) -> node' [string_of_var x; string_of_typ t]
  | InclD(t) -> node' [string_of_typ t]

and string_of_exp e =
  let node' = node (label_of_exp e) in
  match e.it with
  | VarE(x) -> node' [string_of_var x]
  | PrimE(c) -> node' [Prim.string_of_const c]
  | TypE(t) -> node' [string_of_typ t]
  | StrE(b) -> node' [string_of_bind b]
  | FunE(x, t, e) -> node' [string_of_var x; string_of_typ t; string_of_exp e]
  | PackE(x, t) -> node' [string_of_var x; string_of_typ t]
  | IfE(x, e1, e2, t) ->
    node' [string_of_var x; string_of_exp e1; string_of_exp e2; string_of_typ t]
  | DotE(e, x) -> node' [string_of_exp e; string_of_var x]
  | AppE(x1, x2) -> node' [string_of_var x1; string_of_var x2]
  | UnpackE(x, t) -> node' [string_of_var x; string_of_typ t]

and string_of_bind b =
  let node' = node (label_of_bind b) in
  match b.it with
  | EmptyB -> node' []
  | SeqB(b1, b2) -> node' [string_of_bind b1; string_of_bind b2]
  | VarB(x, e) -> node' [string_of_var x; string_of_exp e]
  | InclB(e) -> node' [string_of_exp e]
