(*
 * (c) 2014 Andreas Rossberg
 *)

open Types
open Env

let rec erase_row erase = map_row erase

let rec erase_kind = function
  | BaseK -> IL.BaseK
  | ProdK(kr) -> IL.ProdK(erase_row erase_kind kr)
  | FunK(ks, k) -> IL.arrK(List.map erase_kind ks, erase_kind k)

let erase_bind aks = List.map (fun (a, k) -> a, erase_kind k) aks

let rec erase_typ t =
  match norm_typ t with
  | VarT(a, k) -> IL.varT(a, erase_kind k)
  | PrimT(n) -> IL.PrimT(n)
  | StrT(r) -> IL.ProdT(erase_row erase_typ r)
  | FunT(aks, t, s, p) ->
    IL.allT(erase_bind aks, IL.ArrT(erase_typ t, erase_extyp s))
  | TypT(s) -> IL.ArrT(erase_extyp s, IL.ProdT[])
  | WrapT(s) -> IL.ProdT["wrap", erase_extyp s]
  | LamT(aks, t) -> IL.lamT(erase_bind aks, erase_typ t)
  | AppT(t, ts) -> IL.appT(erase_typ t, List.map erase_typ ts)
  | DotT(t, l) -> IL.DotT(erase_typ t, l)
  | TupT(r) -> IL.TupT(erase_row erase_typ r)
  | RecT(ak, t) -> IL.RecT(fst ak, erase_kind (snd ak), erase_typ t)
  | InferT(z) ->
    match !z with
    | Det t -> erase_typ t
    | Undet u ->
      match u.il with
      | Some t' -> IL.InferT(t', u.id)
      | None ->
        let t' = lazy (
          match !z with
          | Det t -> erase_typ t
          | Undet u -> assert false
        ) in
        u.il <- Some t'; IL.InferT(t', u.id)

and erase_extyp = function
  | ExT(aks, t) -> IL.anyT(erase_bind aks, erase_typ t)


let erase_env env =
  let env0' = IL.empty in
  let env1' = VarSet.fold (fun a env' ->
    IL.add_typ a (erase_kind (lookup_typ a env)) env') (domain_typ env) env0' in
  let env2' = VarSet.fold (fun x env' ->
    IL.add_val x (erase_typ (lookup_val x env)) env') (domain_val env) env1' in
  env2'
