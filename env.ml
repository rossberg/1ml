(*
 * (c) 2014 Andreas Rossberg
 *)

open Types

module VarMap = Map.Make(String)

type env = {typ : kind VarMap.t; var : typ VarMap.t}


(* Basic operations *)

let empty = {typ = VarMap.empty; var = VarMap.empty}

let add_typ a k env =
  assert (not (VarMap.mem a env.typ)); {env with typ = VarMap.add a k env.typ}
let add_typs aks env =
  List.fold_left (fun env (a, k) -> add_typ a k env) env aks
let add_val x t env = {env with var = VarMap.add x t env.var}
let add_row tr env = List.fold_left (fun env (l, t) -> add_val l t env) env tr

let mem_typ a env = VarMap.mem a env.typ
let mem_val x env = VarMap.mem x env.var
let lookup_typ a env = VarMap.find a env.typ
let lookup_val x env = VarMap.find x env.var

let domain map =
  List.fold_right VarSet.add (List.map fst (VarMap.bindings map)) VarSet.empty
let domain_typ env = domain env.typ
let domain_val env = domain env.var


(* Freshening *)

let freshen_var env a =
  if VarMap.mem a env.typ
  then Fomega.rename_for (domain_typ env) a
  else a

let freshen_vars env aks =
  let _, aks' = List.fold_left (fun (env, aks') (a, k) ->
      let a' = freshen_var env a in add_typ a' k env, (a', k)::aks'
    ) (env, []) aks
  in List.rev aks'

let rec freshen_typ env = function
  | FunT(aks, t, s, f) as t' ->
    let aks' = freshen_vars env aks in
    if aks' = aks then t' else begin
      let su = subst aks (varTs aks') in
      FunT(aks', subst_typ su t, subst_extyp su s, f)
    end
  | LamT(aks, t) as t' ->
    let aks' = freshen_vars env aks in
    if aks' = aks then t' else LamT(aks', subst_typ (subst aks (varTs aks')) t)
  | RecT(ak, t) as t' ->
    let ak' = List.hd (freshen_vars env [ak]) in
    if ak' = ak then t' else RecT(ak', subst_typ (subst [ak] (varTs [ak'])) t)
  | InferT(z) as t ->
    (match !z with
    | Det t -> freshen_typ env t
    | _ -> t
    )
  | t -> t

let freshen_extyp env = function
  | ExT(aks, t) as s ->
    let aks' = freshen_vars env aks in
    if aks' = aks then s else ExT(aks', subst_typ (subst aks (varTs aks')) t)

let is_fresh_extyp env (ExT(aks, t)) =
  List.for_all (fun (a, k) -> not (VarMap.mem a env.typ)) aks
