(*
 * (c) 2014 Andreas Rossberg
 *)

open Source

type var = (string, unit) phrase

type impl = (impl', unit) phrase
and impl' =
  | Impl
  | Expl

type eff = (eff', unit) phrase
and eff' =
  | Pure
  | Impure

type typ = (typ', unit) phrase
and typ' =
  | PathT of exp
  | PrimT of string
  | TypT
  | HoleT
  | StrT of dec
  | FunT of var * typ * typ * eff * impl
  | WrapT of typ
  | EqT of exp
  | AsT of typ * typ
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
  | FunE of var * typ * exp * impl
  | WrapE of var * typ
  | RollE of var * typ
  | IfE of var * exp * exp * typ
  | DotE of exp * var
  | AppE of var * var
  | UnwrapE of var * typ
  | UnrollE of var * typ
  | RecE of var * typ * exp

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

let index n = "_" ^ string_of_int n


(* Sugar *)

let letE(b, e) =
  let x' = var "let" in
  let b2 = VarB(x'@@e.at, e)@@e.at in
  DotE(StrE(SeqB(b, b2)@@span[b.at; e.at])@@span[b.at; e.at], x'@@e.at)

let letT(b, t) = PathT(letE(b, TypE(t)@@t.at)@@span[b.at; t.at])
let letD(b, d) = InclD(letT(b, StrT(d)@@d.at)@@span[b.at; d.at])
let letB(b, b') = InclB(letE(b, StrE(b')@@b'.at)@@span[b.at; b'.at])

let rec tupT(ts) = StrT(tupT' 1 ts)
and tupT' n = function
  | [] -> EmptyD@@nowhere_region
  | t::ts ->
    let d = tupT' (n + 1) ts in
    SeqD(VarD((index n)@@t.at, t)@@t.at, d)@@
      (match d.it with EmptyD -> t.at | _ -> span[t.at; d.at])

let rec tupE(es) = StrE(tupE' 1 es)
and tupE' n = function
  | [] -> EmptyB@@nowhere_region
  | e::es ->
    let b = tupE' (n + 1) es in
    SeqB(VarB((index n)@@e.at, e)@@e.at, b)@@
      (match b.it with EmptyB -> e.at | _ -> span[e.at; b.at])

let rec funT(ps, t, f) = (funT'(ps, t, f)).it
and funT'(ps, t, f) =
  match ps with
  | [] -> t
  | p::ps' ->
    let (b, t1, i) = p.it in
    let t2 = funT'(ps', t, f) in
    let x, t2' =
      match b.it with
      | EmptyB -> "_"@@p.at, t2
      | VarB(x, {it = VarE({it = "$"})}) -> x, t2
      | _ -> "$"@@p.at, letT(b, t2)@@span[p.at; t2.at]
    in FunT(x, t1, t2', f.it@@f.at, i)@@span[p.at; t.at]

let rec funE(ps, e) = (funE'(ps, e)).it
and funE'(ps, e) =
  match ps with
  | [] -> e
  | p::ps' ->
    let (b, t, i) = p.it in
    let e' = funE'(ps', e) in
    let x, e'' =
      match b.it with
      | EmptyB -> "_"@@p.at, e'
      | VarB(x, {it = VarE({it = "$"})}) -> x, e'
      | _ -> "$"@@p.at, letE(b, e')@@span[p.at; e.at]
    in FunE(x, t, e'', i)@@span[p.at; e.at]

let doE(e) = letE(VarB("_"@@e.at, e)@@e.at, tupE[]@@e.at)
let doB(e) = letB(VarB("_"@@e.at, e)@@e.at, EmptyB@@e.at)

let seqE(es) =
  let b =
    List.fold_right (fun e b -> SeqB(doB(e)@@e.at, b)@@span[e.at; b.at])
      es (EmptyB@@(after (Lib.List.last es).at))
  in
  doE(StrE(b)@@@(List.map at es))

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

let wrapE(e, t) =
  match e.it with
  | VarE(x) -> WrapE(x, t)
  | _ ->
    let x' = var "wrap" in
    letE(VarB(x'@@e.at, e)@@e.at, WrapE(x'@@e.at, t)@@span[e.at; t.at])

let unwrapE(e, t) =
  match e.it with
  | VarE(x) -> UnwrapE(x, t)
  | _ ->
    let x' = var "wrap" in
    letE(VarB(x'@@e.at, e)@@e.at, UnwrapE(x'@@e.at, t)@@span[e.at; t.at])

let rollE(e, t) =
  match e.it with
  | VarE(x) -> RollE(x, t)
  | _ ->
    let x' = var "@" in
    letE(VarB(x'@@e.at, e)@@e.at, RollE(x'@@e.at, t)@@span[e.at; t.at])

let unrollE(e, t) =
  match e.it with
  | VarE(x) -> UnrollE(x, t)
  | _ ->
    let x' = var "@" in
    letE(VarB(x'@@e.at, e)@@e.at, UnrollE(x'@@e.at, t)@@span[e.at; t.at])

let annotE(e, t) =
  let x' = var "annot" in
  appE(FunE(x'@@t.at, t, VarE(x'@@t.at)@@t.at, Expl@@t.at)@@span[e.at; t.at], e)

let sealE(e, t) =
  (* TODO: clone t! *)
  unwrapE(wrapE(e, WrapT(t)@@t.at)@@span[e.at; t.at], WrapT(t)@@t.at)

let dotopE(x) =
  FunE("x"@@x.at, HoleT@@x.at, DotE(VarE("x"@@x.at)@@x.at, x)@@x.at, Expl@@x.at)


let recT(p, t2) =
  let b, t1 = p.it in
  let e = TypE(t2)@@t2.at in
  let e' =
    match b.it with
    | VarB(x, _) -> RecE(x, t1, e)
    | EmptyB -> RecE("_"@@b.at, t1, e)
    | _ -> RecE("$"@@b.at, t1, letE(b, e)@@span[b.at; e.at])
  in PathT(e'@@span[p.at; t2.at])

let recE(p, e) =
  let b, t = p.it in
  match b.it with
  | VarB(x, _) -> RecE(x, t, e)
  | EmptyB -> RecE("_"@@b.at, t, e)
  | _ -> RecE("$"@@b.at, t, letE(b, e)@@span[b.at; e.at])

let patB(p, e) =
  let b, topt = p.it in
  let e' =
    match topt with
    | None -> e
    | Some t -> annotE(e, t)@@span[e.at; t.at]
  in
  match b.it with
  | EmptyB -> doB(e')
  | VarB(x, {it = VarE({it = "$"})}) -> VarB(x, e')
  | _ -> letB(VarB("$"@@e.at, e')@@e.at, b.it@@p.at)

let defaultP p =
  match p.it with
  | b, None -> (b, HoleT@@p.at)@@p.at
  | b, Some t -> (b, t)@@p.at

let defaultTP p =
  match p.it with
  | b, None -> (b, TypT@@p.at)@@p.at
  | b, Some t -> (b, t)@@p.at

let varP(x) = VarB(x, VarE("$"@@x.at)@@x.at)@@x.at, None

let holeP : bind * typ option =
  EmptyB@@nowhere_region, None

let asTopt(to1, to2) =
  match to1, to2 with
  | None, None -> None
  | None, some | some, None -> some
  | Some t1, Some t2 -> Some(AsT(t1, t2)@@span[t1.at; t2.at])

let asP(p1, p2) =
  let b1, to1 = p1.it in
  let b2, to2 = p2.it in
  SeqB(b1.it@@p1.at, b2.it@@p2.at)@@span[p1.at; p2.at], asTopt(to1, to2)

let annotP(p, t2) =
  let b, to1 = p.it in
  match b.it with
  | EmptyB | VarB(_, {it = VarE({it = "$"})}) -> b, Some t2
  | _ ->
    let t =
      match asTopt(to1, Some t2) with Some t -> t | None -> assert false in
    patB(p, annotE(VarE("$"@@t2.at)@@t2.at, t)@@t2.at)@@span[p.at; t2.at],
    Some t

let wrapP(p, t2) =
  let _, to1 = p.it in
  letB(
    VarB("$"@@t2.at, UnwrapE("$"@@t2.at, t2)@@t2.at)@@t2.at,
    patB(p, VarE("$"@@t2.at)@@t2.at)@@span[p.at; t2.at]
  )@@span[p.at; t2.at],
  match to1 with
  | None -> Some t2
  | Some t1 -> Some (AsT(t2, WrapT(t1)@@t1.at)@@span[p.at; t2.at])

let strP(xps) =
  match xps with
  | [] ->
    EmptyB@@nowhere_region, Some (StrT(EmptyD@@nowhere_region)@@nowhere_region)
  | xp::_ ->
    let b, d =
      List.fold_right (fun xp (b, d) ->
        let x, p = xp.it in
        let _, t = (defaultP p).it in
        SeqB(patB(p, DotE(VarE("$"@@xp.at)@@xp.at, x)@@xp.at)@@xp.at, b)
          @@span[b.at; p.at],
        SeqD(VarD(x, t.it@@p.at)@@xp.at, d)@@span[d.at; p.at]
      ) xps (EmptyB@@xp.at, EmptyD@@xp.at)
    in b, Some (StrT(d)@@d.at)

let rec tupP(ps) = strP(tupP' 1 ps)
and tupP' n = function
  | [] -> []
  | p::ps -> (((index n)@@p.at, p)@@p.at) :: tupP' (n + 1) ps

let rollP(p, t2) =
  let _, to1 = p.it in
  letB(
    VarB("$"@@t2.at, UnrollE("$"@@t2.at, t2)@@t2.at)@@t2.at,
    patB(p, VarE("$"@@t2.at)@@t2.at)@@span[p.at; t2.at]
  )@@span[p.at; t2.at],
  match to1 with
  | None -> Some t2
  | Some t1 ->
    Some (AsT(t2, PathT(RecE("_"@@t1.at, TypT@@t1.at,
      TypE(t1.it@@p.at)@@p.at)@@p.at)@@p.at)@@span[p.at; t2.at])


(* String conversion *)

let node label = function
  | [] -> label
  | args -> label ^ "(" ^ String.concat ", " args ^ ")"

let label_of_impl i =
  match i.it with
  | Expl -> "Expl"
  | Impl -> "Impl"

let label_of_eff p =
  match p.it with
  | Pure -> "P"
  | Impure -> "I"

let label_of_typ t =
  match t.it with
  | PathT _ -> "PathT"
  | PrimT _ -> "PrimT"
  | TypT -> "TypT"
  | HoleT -> "HoleT"
  | StrT _ -> "StrT"
  | FunT _ -> "FunT"
  | WrapT _ -> "WrapT"
  | EqT _ -> "EqT"
  | AsT _ -> "AsT"
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
  | TypE _ -> "TypE"
  | StrE _ -> "StrE"
  | FunE _ -> "FunE"
  | WrapE _ -> "WrapE"
  | RollE _ -> "RollE"
  | IfE _ -> "IfE"
  | DotE _ -> "DotE"
  | AppE _ -> "AppE"
  | UnwrapE _ -> "UnwrapE"
  | UnrollE _ -> "UnrollE"
  | RecE _ -> "RecE"

let label_of_bind b =
  match b.it with
  | EmptyB -> "EmptyB"
  | SeqB _ -> "SeqB"
  | VarB _ -> "VarB"
  | InclB _ -> "InclB"


let string_of_var x = "\"" ^ x.it ^ "\""

let string_of_impl i = label_of_impl i
let string_of_eff p = label_of_eff p

let rec string_of_typ t =
  let node' = node (label_of_typ t) in
  match t.it with
  | PathT(e) -> node' [string_of_exp e]
  | PrimT(n) -> node' ["\"" ^ n ^ "\""]
  | TypT -> node' []
  | HoleT -> node' []
  | StrT(d) -> node' [string_of_dec d]
  | FunT(x, t1, t2, p, i) ->
    node' [string_of_var x; string_of_typ t1; string_of_typ t2;
      string_of_eff p; string_of_impl i]
  | WrapT(t) -> node' [string_of_typ t]
  | EqT(e) -> node' [string_of_exp e]
  | AsT(t1, t2) -> node' [string_of_typ t1; string_of_typ t2]
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
  | FunE(x, t, e, i) ->
    node' [string_of_var x; string_of_typ t; string_of_exp e; string_of_impl i]
  | WrapE(x, t) -> node' [string_of_var x; string_of_typ t]
  | RollE(x, t) -> node' [string_of_var x; string_of_typ t]
  | IfE(x, e1, e2, t) ->
    node' [string_of_var x; string_of_exp e1; string_of_exp e2; string_of_typ t]
  | DotE(e, x) -> node' [string_of_exp e; string_of_var x]
  | AppE(x1, x2) -> node' [string_of_var x1; string_of_var x2]
  | UnwrapE(x, t) -> node' [string_of_var x; string_of_typ t]
  | UnrollE(x, t) -> node' [string_of_var x; string_of_typ t]
  | RecE(x, t, e) -> node' [string_of_var x; string_of_typ t; string_of_exp e]

and string_of_bind b =
  let node' = node (label_of_bind b) in
  match b.it with
  | EmptyB -> node' []
  | SeqB(b1, b2) -> node' [string_of_bind b1; string_of_bind b2]
  | VarB(x, e) -> node' [string_of_var x; string_of_exp e]
  | InclB(e) -> node' [string_of_exp e]
