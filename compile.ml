(*
 * (c) 2014 Andreas Rossberg
 *)

module F = Fomega
module L = Lambda

(* Rows *)

let sort_row r = List.sort (fun (l1, _) (l2, _) -> compare l1 l2) r

let rec lookup_row l i = function
  | [] -> assert false
  | (l', t)::r -> if l = l' then i, t else lookup_row l (i + 1) r


(* Compilation *)

let rec compile_exp env = function
  | F.VarE(x) -> L.VarE(x), F.lookup_val x env
  | F.PrimE(c) as e -> L.PrimE(c), F.infer_exp env e
  | F.IfE(e1, e2, e3) ->
    let e1', _ = compile_exp env e1 in
    let e2', _ = compile_exp env e2 in
    let e3', t = compile_exp env e3 in
    L.IfE(e1', e2', e3'), t
  | F.LamE(x, t, e) ->
    let e', t' = compile_exp (F.add_val x t env) e in
    L.LamE(x, e'), F.ArrT(t, t')
  | F.AppE(e1, e2) ->
    let e1', t1 = compile_exp env e1 in
    let e2', _ = compile_exp env e2 in
    (match F.force_typ t1 with
    | F.ArrT(_, t) -> L.AppE(e1', e2'), t
    | _ -> assert false
    )
  | F.TupE(er) ->
    let er', tr = compile_row env er in
    List.fold_right (fun (l, e') e'' -> L.LetE(e', "." ^ l, e''))
      er' (L.TupE(List.map (fun (l, _) -> L.VarE("." ^ l)) (sort_row er'))),
    F.ProdT(tr)
  | F.DotE(e, l) ->
    let e', t = compile_exp env e in
    (match F.force_typ t with
    | F.ProdT(tr) ->
      let i, t' = lookup_row l 0 (sort_row tr) in
      L.DotE(e', i), t'
    | t_ -> assert false
    )
  | F.GenE(a, k, e) ->
    let e', t = compile_exp (F.add_typ a k env) e in
    e', F.AllT(a, k, t)
  | F.InstE(e, t) ->
    let e', t' = compile_exp env e in
    (match F.force_typ t' with
    | F.AllT(a, k, t'') -> e', F.subst_typ [a, t] t''
    | _ -> assert false
    )
  | F.PackE(t, e, t') ->
    let e', _ = compile_exp env e in
    e', t'
  | F.OpenE(e1, a, x, e2) ->
    let e1', t1 = compile_exp env e1 in
    (match F.force_typ t1 with
    | F.AnyT(a, k, t) ->
      let e2', t2 = compile_exp (F.add_val x t (F.add_typ a k env)) e2 in
      L.LetE(e1', x, e2'), t2
    | _ -> assert false
    )
  | F.RollE(e, t) ->
    let e', _ = compile_exp env e in
    e', t
  | F.UnrollE(e) ->
    let e', t = compile_exp env e in
    (match F.unroll_typ t with
    | Some t' -> e', t'
    | _ -> assert false
    )
  | F.RecE(x, t, e) ->
    let e', t = compile_exp (F.add_val x t env) e in
    L.RecE(x, e'), t
  | F.LetE(e1, x, e2) ->
    let e1', t1 = compile_exp env e1 in
    let e2', t2 = compile_exp (F.add_val x t1 env) e2 in
    L.LetE(e1', x, e2'), t2

and compile_row env = function
  | [] -> [], []
  | (l, e)::er ->
    let e', t = compile_exp env e in
    let er', tr = compile_row env er in
    (l, e')::er', (l, t)::tr


let compile env e = fst (compile_exp env e)
