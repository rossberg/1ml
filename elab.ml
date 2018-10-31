(*
 * (c) 2014 Andreas Rossberg
 *)

open Source
open Types
open Env
open Sub
open Erase

module EL = Syntax

exception Error of string

let quote x = "`" ^ x ^ "'"


(* Verification *)

let verify_flag = ref false
let verify_fomega_flag = ref true

let (<<<) f x =
  if not !verify_flag then x else
  let at, env, s, zs, eo, label = f x in
  let prefix = "[" ^ label ^ "] " ^ string_of_region at ^ " " in
  (try if kind_of_extyp s <> BaseK then raise Kind with Kind ->
    verbosest_on ();
    print_endline (prefix ^ "malformed type: " ^ string_of_extyp s);
    ignore (kind_of_extyp s)
  );
  if not (is_fresh_extyp env s) then begin
    print_endline (prefix ^ "non-fresh type: " ^ string_of_extyp s);
    failwith "fresh"
  end;
  List.iter (fun z ->
    match !z with
    | Det _ -> ()
    | Undet u ->
      if not (VarSet.for_all (fun a -> mem_typ a env) u.vars) then
        let t = InferT(z) in
        verbosest_on ();
        print_endline (prefix ^ "malformed undet: " ^ string_of_typ t);
        print_endline (prefix ^ "type environment:" ^
          VarSet.fold (fun a s -> s ^ " " ^ a ^ ":" ^
            string_of_kind (lookup_typ a env)) (domain_typ env) "");
        failwith "undet"
  ) zs;
  if !verify_fomega_flag then begin
    let env' = erase_env env in
    let t' = erase_extyp s in
    (try IL.check_typ env' t' IL.BaseK "kind" with IL.Error _ as exn ->
      verbosest_on ();
      print_endline (prefix ^ "malformed F type: " ^ IL.string_of_typ t');
      print_endline (prefix ^ "unerased type: " ^ string_of_extyp s);
        print_endline (prefix ^ "type environment:" ^
          VarSet.fold (fun a s -> s ^ " " ^ a ^ ":" ^
            string_of_kind (lookup_typ a env)) (domain_typ env) "");
      raise exn
    );
    (match eo with
    | None -> ()
    | Some e ->
      (try IL.check_exp env' e t' "type" with IL.Error _ as exn ->
        verbosest_on ();
        print_endline (prefix ^ "malformed F term: " ^ IL.string_of_exp e);
        print_endline (prefix ^ "inferred F type: " ^
          IL.string_of_typ (IL.infer_exp env' e));
        print_endline (prefix ^ "expected F type: " ^ IL.string_of_typ t');
        print_endline (prefix ^ "unerased type: " ^ string_of_extyp s);
        print_endline (prefix ^ "type environment:" ^
          VarSet.fold (fun a s -> s ^ " " ^ a ^ ":" ^
            string_of_kind (lookup_typ a env)) (domain_typ env) "");
        print_endline (prefix ^ "value environment:" ^
          VarSet.fold (fun x s -> s ^ " " ^ x ^ " : " ^
            string_of_typ (lookup_val x env)) (domain_val env) "" ^ ",");
        raise exn
      )
    )
  end;
  x


(* Recursive types *)

exception Recursive

let rec make_rec_typ = function
  | StrT(tr) ->
    let tr', kr = make_rec_row tr in
    TupT(tr'), ProdK(kr)
  | FunT(aks, t, s, Explicit Pure) ->
    let t', k = make_rec_extyp s in
    LamT(aks, t'), FunK(List.map snd aks, k)
  | TypT(ExT([], t)) -> t, BaseK
  | _ -> raise Recursive

and make_rec_extyp = function
  | ExT(aks, t) -> if aks = [] then make_rec_typ t else raise Recursive

and make_rec_row tr =
  let tkr = map_row make_rec_typ tr in
  map_row fst tkr, map_row snd tkr


let rec paths_typ ta ps = function
  | StrT(tr) -> paths_row ta ps tr
  | FunT(aks, t, s, Explicit Pure) ->
    paths_extyp ta (List.map (fun p -> AppT(p, varTs aks)) ps) s
  | TypT(ExT([], t)) ->
    (match ps with p::_ when p = t -> [ta] | _ -> [])
  | _ -> raise Recursive

and paths_extyp ta ps = function
  | ExT(aks, t) -> if aks = [] then paths_typ ta ps t else raise Recursive

and paths_row ta ps = function
  | [] -> []
  | (l, t)::tr ->
    let ts1 = paths_typ (DotT(ta, l)) ps t in
    let ts2 = paths_row ta (Lib.List.drop (List.length ts1) ps) tr in
    ts1 @ ts2


(* Instantiation *)

let rec instantiate env t e =
  match follow_typ t with
  | FunT(aks1, t1, ExT(aks2, t2), Implicit) ->
    assert (aks2 = []);
    let ts, zs = guess_typs (Env.domain_typ env) aks1 in
    let t', zs', e' =
      instantiate env (subst_typ (subst aks1 ts) t2)
        (IL.AppE(IL.instE(e, List.map erase_typ ts),
          materialize_typ (subst_typ (subst aks1 ts) t1)))
    in t', zs @ zs', e'
  | t -> t, [], e


(* Type Elaboration *)

let elab_impl env impl =
  match impl.it with
  | EL.Expl -> Explicit Pure
  | EL.Impl -> Implicit

let elab_eff env eff =
  match eff.it with
  | EL.Pure -> Pure
  | EL.Impure -> Impure

let rec elab_typ env typ l =
  Trace.elab (lazy ("[elab_typ] " ^ EL.label_of_typ typ));
  (fun (s, zs) -> typ.at, env, s, zs, None, EL.label_of_typ typ) <<<
  match typ.it with
  | EL.PathT(exp) ->
    let t, zs = elab_pathexp env exp l in
    (match t with
    | TypT(s) ->
      let ExT(aks, t) = s in
      let aks' = freshen_vars env (rename_vars (prepend_path l) aks) in
      ExT(aks', subst_typ (subst aks (varTs aks')) t), zs
    | InferT(z) ->
      let t', zs2 = guess_typ (Env.domain_typ env) BaseK in
      let s = ExT([], t') in
      resolve_always z (TypT(s));
      s, zs @ zs2
    | _ -> error typ.at "expression does not denote a type"
    )

  | EL.PrimT(n) ->
    (match Prim.typ_of_string n with
    | Some t -> ExT([], PrimT(t)), []
    | None -> error typ.at "unknown primitive type"
    )

  | EL.TypT ->
    let a = freshen_var env (default_path l "t") in
    ExT([a, BaseK], TypT(ExT([], VarT(a, BaseK)))), []

  | EL.HoleT ->
    let t, zs = guess_typ (Env.domain_typ env) BaseK in
    ExT([], t), zs

  | EL.StrT(dec) ->
    elab_dec env dec l

  | EL.FunT(var, typ1, typ2, eff, impl) ->
    let ExT(aks1, t1) as s1, zs1 = elab_typ env typ1 var.it in
    let ExT(aks2, t2) as s2, zs2 =
      elab_typ (add_val var.it t1 (add_typs aks1 env)) typ2 l in
    (match elab_eff env eff, elab_impl env impl with
    | Impure, Explicit _ ->
      let aks2' =
        freshen_vars (add_typs aks1 env) (rename_vars (cut_path l) aks2) in
      let s2' = ExT(aks2', subst_typ (subst aks2 (varTs aks2')) t2) in
      let t = FunT(aks1, t1, s2', Explicit Impure) in
      ExT([], t), lift_warn typ.at t env (zs1 @ zs2)
    | Pure, f ->
      let aks2' =
        freshen_vars (add_typs aks1 env)
          (List.map (fun (a2, k2) -> a2, funK(List.map snd aks1, k2)) aks2) in
      let tas2' =
        List.map (fun (a2', k2') -> appT(VarT(a2', k2'), varTs aks1)) aks2' in
      let t2' = subst_typ (subst aks2 tas2') t2 in
      let t = FunT(aks1, t1, ExT([], t2'), f) in
      ExT(aks2', t), lift_warn typ.at t (add_typs aks2' env) (zs1 @ zs2)
    | _ -> error impl.at "impure function cannot be implicit"
    )

  | EL.WrapT(typ1) ->
    let s1, zs = elab_typ env typ1 "" in
    ExT([], WrapT(s1)), lift_warn typ.at (WrapT(s1)) env zs

  | EL.EqT(exp) ->
    let t, zs = elab_pathexp env exp l in
    ExT([], t), zs

  | EL.AsT(typ1, typ2) ->
    let ExT(aks1, t1) as s1, zs1 = elab_typ env typ1 l in
    let s2, zs2 = elab_typ env typ2 l in
    let zs3 = try equal_extyp env s1 s2 with Sub e ->
      error typ.at (
        "inconsistent types equated by `as': " ^
        Types.string_of_extyp s1 ^ " vs " ^ Types.string_of_extyp s2
      )
    in
    s1, lift_warn typ.at t1 (add_typs aks1 env) (zs1 @ zs2 @ zs3)

  | EL.WithT(typ1, vars, exp) ->
    let t2, zs2 = elab_pathexp env exp l in
    let ExT(aks1, t1), zs1 = elab_typ env typ1 l in
    let ls = List.map (fun var -> var.it) vars in
Trace.debug (lazy ("[WithT] s1 = " ^ string_of_norm_extyp (ExT(aks1, t1))));
Trace.debug (lazy ("[WithT] ls = " ^ String.concat "." ls));
Trace.debug (lazy ("[WithT] t2 = " ^ string_of_norm_typ t2));
    let ta = try project_typ ls t1 with Not_found ->
      error typ.at ("path " ^ quote (String.concat "." ls) ^ " unbound") in
Trace.debug (lazy ("[WithT] ta = " ^ string_of_norm_typ ta));
    let bs = vars_typ ta in
    let aks11 = List.filter (fun (a, k) -> not (VarSet.mem a bs)) aks1 in
    let aks12 = List.filter (fun (a, k) -> VarSet.mem a bs) aks1 in
Trace.debug (lazy ("[WithT] aks11 = " ^ string_of_norm_extyp (ExT(aks11, StrT []))));
Trace.debug (lazy ("[WithT] aks12 = " ^ string_of_norm_extyp (ExT(aks12, StrT []))));
    let ts, zs3, _ =
      try sub_typ env t2 ta (varTs aks12) with Sub e -> error exp.at
        ("refinement type does not match type component: " ^ Sub.string_of_error e)
    in
    ExT(aks11, subst_typ (subst aks12 ts) t1),
    lift_warn typ.at t1 (add_typs aks11 env) (zs1 @ zs2 @ zs3)

and elab_dec env dec l =
  Trace.elab (lazy ("[elab_dec] " ^ EL.label_of_dec dec));
  (fun (s, zs) -> dec.at, env, s, zs, None, EL.label_of_dec dec) <<<
  match dec.it with
  | EL.VarD(var, typ) ->
    let l' = var.it in
    let ExT(aks, t), zs = elab_typ env typ (append_path l l') in
    Trace.bind (lazy ("[VarD] " ^ l ^ " : " ^
      string_of_norm_extyp (ExT(aks, t))));
    ExT(aks, StrT[l', t]), zs

  | EL.InclD(typ) ->
    let ExT(aks, t) as s, zs = elab_typ env typ l in
    (match t with
    | StrT(tr) -> ()
    | InferT(z) -> resolve_always z (StrT[])  (* TODO: row polymorphism *)
    | _ -> error dec.at "included type is not a structure"
    ); s, zs

  | EL.EmptyD ->
    ExT([], StrT[]), []

  | EL.SeqD(dec1, dec2) ->
    (match elab_dec env dec1 l with
    | ExT(aks1, StrT(tr1)), zs1 ->
      (match elab_dec (add_row tr1 (add_typs aks1 env)) dec2 l with
      | ExT(aks2, StrT(tr2)), zs2 ->
        let ls = intersect_row tr1 tr2 in
        if ls <> [] then
          error dec.at ("multiple declarations for " ^
            String.concat ", " (List.map (fun (l, _) -> quote l) ls));
        ExT(aks1 @ aks2, StrT(tr1 @ tr2)), zs1 @ zs2
      | _ -> assert false
      )
    | _ -> assert false
    )

and elab_pathexp env exp l =
  Trace.elab (lazy ("[elab_pathexp] " ^ EL.label_of_exp exp));
  let ExT(aks, t), p, zs, _ = elab_instexp env exp l in
Trace.debug (lazy ("[ExpP] s = " ^ string_of_norm_extyp (ExT(aks, t))));
  if p = Impure then
    error exp.at "impure path expression";
  if List.exists (fun (a, k) -> contains_typ a t) aks then
    error exp.at "local type(s) escape scope"
  else
    follow_typ t, lift_warn exp.at t env zs


(* Expression elaboration *)

and lookup_var env var =
  try lookup_val var.it env with Not_found ->
    error var.at ("unbound identifier " ^ quote var.it)

and elab_instvar env var =
  (fun (t, zs, e) -> var.at, env, ExT([], t), zs, Some e, "InstVE") <<<
  instantiate env (lookup_var env var) (IL.VarE(var.it))

and elab_prim_typ = function
  | Prim.VarT -> VarT("a", BaseK)
  | t -> PrimT(t)

and elab_prim_typs = function
  | [t] -> elab_prim_typ t
  | ts -> StrT(tup_row (List.map elab_prim_typ ts))

and elab_prim_fun f =
  let t1 = elab_prim_typs (fst f.Prim.typ) in
  let t2 = elab_prim_typs (snd f.Prim.typ) in
  let t = FunT([], t1, ExT([], t2), Explicit Impure) in
  let e = IL.PrimE(Prim.FunV f) in
  if Prim.is_poly f then
    let ta = TypT(ExT([], VarT("a", BaseK))) in
    FunT(["a", BaseK], ta, ExT([], t), Explicit Impure),
    IL.GenE("a", IL.BaseK, IL.LamE("_", erase_typ ta, e))
  else
    t, e

and elab_const = function
  | Prim.FunV(f) -> elab_prim_fun f
  | c -> PrimT(Prim.typ_of_const c), IL.PrimE(c)

and elab_exp env exp l =
  Trace.elab (lazy ("[elab_exp] " ^ EL.label_of_exp exp));
  (fun (s, p, zs, e) -> exp.at, env, s, zs, Some e, EL.label_of_exp exp) <<<
  match exp.it with
  | EL.VarE(var) ->
Trace.debug (lazy ("[VarE] x = " ^ var.it));
Trace.debug (lazy ("[VarE] s = " ^ string_of_norm_extyp (ExT([], lookup_var env var))));
    ExT([], lookup_var env var), Pure, [], IL.VarE(var.it)

  | EL.PrimE(c) ->
    let t, e = elab_const c in
    ExT([], t), Pure, [], e

  | EL.TypE(typ) ->
    let s, zs = elab_typ env typ "" in
    ExT([], TypT(s)), Pure, zs, IL.LamE("_", erase_extyp s, IL.TupE[])

  | EL.StrE(bind) ->
    elab_bind env bind l

  | EL.FunE(var, typ, exp2, impl) ->
Trace.debug (lazy ("[FunE] " ^ string_of_region exp.at));
    let ExT(aks, t) as s1, zs1 = elab_typ env typ var.it in
    let s, p, zs2, e2 =
      elab_exp (add_val var.it t (add_typs aks env)) exp2 "" in
Trace.debug (lazy ("[FunE] s1 = " ^ string_of_norm_extyp s1));
Trace.debug (lazy ("[FunE] s2 = " ^ string_of_norm_extyp s));
Trace.debug (lazy ("[FunE] env =" ^ VarSet.fold (fun a s -> s ^ " " ^ a) (domain_typ env) ""));
    assert (let ExT(aks, _) = s in p = Impure || aks = []);
    let p' =
      match p, elab_impl env impl with
      | Impure, Explicit _ -> Explicit Impure
      | Pure, f -> f
      | _ -> error impl.at "impure function cannot be implicit" in
    ExT([], FunT(aks, t, s, p')), Pure,
    lift_warn exp.at (FunT(aks, t, s, p')) env (zs1 @ zs2),
    IL.genE(erase_bind aks, IL.LamE(var.it, erase_typ t, e2))

  | EL.WrapE(var, typ) ->
    let s, zs1 =
      match elab_typ env typ "" with
      | ExT([], WrapT(s)), zs1 -> s, zs1
      | _ -> error typ.at "non-wrapped type for wrap"
    in
    let _, zs2, f =
      try sub_extyp env (ExT([], lookup_var env var)) s []
      with Sub e -> error exp.at
        ("wrapped type does not match annotation: " ^ Sub.string_of_error e)
    in
    ExT([], WrapT(s)), Pure, lift_warn exp.at (WrapT(s)) env (zs1 @ zs2),
    IL.TupE["wrap", IL.AppE(f, IL.VarE(var.it))]

  | EL.RollE(var, typ) ->
    let s, zs1 = elab_typ env typ l in
    let t, ak, t' =
      match s with
      | ExT([], (RecT(ak, t') as t)) -> t, ak, t'
      | _ -> error typ.at "non-recursive type for rolling" in
    let _, zs2, f =
      try sub_typ env (lookup_var env var) (subst_typ (subst [ak] [t]) t') []
      with Sub e -> error var.at ("rolled value does not match annotation") in
    ExT([], t), Pure, zs1 @ zs2,
    IL.RollE(IL.AppE(f, IL.VarE(var.it)), erase_typ t)

  | EL.IfE(var, exp1, exp2, typ) ->
    let t0, zs0, ex = elab_instvar env var in
    let _ =
      match t0 with
      | PrimT(Prim.BoolT) -> ()
      | InferT(z) -> resolve_always z (PrimT(Prim.BoolT))
      | _ -> error var.at "condition is not Boolean" in
    let ExT(aks, t) as s, zs = elab_typ env typ l in
    let s1, p1, zs1, e1 = elab_exp env exp1 l in
    let s2, p2, zs2, e2 = elab_exp env exp2 l in
    let _, zs3, f1 = try sub_extyp env s1 s [] with Sub e -> error exp1.at
      ("branch type does not match annotation: " ^ Sub.string_of_error e) in
    let _, zs4, f2 = try sub_extyp env s2 s [] with Sub e -> error exp2.at
      ("branch type does not match annotation: " ^ Sub.string_of_error e) in
    s, join_eff p1 p2,
    lift_warn exp.at t (add_typs aks env) (zs0 @ zs @ zs1 @ zs2 @ zs3 @ zs4),
    IL.IfE(ex, IL.AppE(f1, e1), IL.AppE(f2, e2))

  | EL.DotE(exp1, var) ->
    let ExT(aks, t), p, zs1, e1 = elab_instexp env exp1 "" in
    let tr, zs2 =
      match t with
      | StrT(tr) -> tr, []
      | InferT(z) ->
        (* TODO: row polymorphism *)
        let t, zs = guess_typ (Env.domain_typ (add_typs aks env)) BaseK in
        let tr = [l, t] in
        resolve_always z (StrT(tr)); tr, zs
      | _ -> error exp1.at "expression is not a structure"
    in
Trace.debug (lazy ("[DotE] l = " ^ var.it));
Trace.debug (lazy ("[DotE] s1 = " ^ string_of_extyp (ExT(aks, t))));
    let t' = try List.assoc var.it tr with Not_found ->
      error exp.at ("field " ^ quote var.it ^ " unbound in expression") in
    let aks' = freshen_vars env (rename_vars (cut_path var.it) aks) in
    let s = ExT(aks', subst_typ (subst aks (varTs aks')) t') in
Trace.debug (lazy ("[DotE] s = " ^ string_of_extyp s));
    List.iter (subst_infer (subst aks (varTs aks'))) (zs1 @ zs2);
    s, p, zs1 @ zs2,
    IL.openE(e1, List.map fst aks', "x",
      IL.packE(List.map erase_typ (varTs aks'),
        IL.DotE(IL.VarE("x"), var.it), erase_extyp s))

  | EL.AppE(var1, var2) ->
    let tf, zs1, ex1 = elab_instvar env var1 in
Trace.debug (lazy ("[AppE] tf = " ^ string_of_norm_typ tf));
    let aks1, t1, s, p, zs =
      match freshen_typ env tf with
      | FunT(aks1, t1, s, Explicit p) -> aks1, t1, s, p, []
      | InferT(z) ->
        let t1, zs1 = guess_typ (Env.domain_typ env) BaseK in
        let t2, zs2 = guess_typ (Env.domain_typ env) BaseK in
        let s = ExT([], t2) in
        resolve_always z (FunT([], t1, s, Explicit Impure));
        [], t1, s, Impure, zs1 @ zs2
      | _ -> error var1.at "expression is not a function" in
    let t2 = lookup_var env var2 in
Trace.debug (lazy ("[AppE] s1 = " ^ string_of_norm_extyp (ExT(aks1, t1))));
Trace.debug (lazy ("[AppE] t2 = " ^ string_of_norm_typ t2));
    let ts, zs3, f =
      try sub_typ env t2 t1 (varTs aks1) with Sub e -> error var2.at
        ("argument type does not match function: " ^ Sub.string_of_error e)
    in
Trace.debug (lazy ("[AppE] ts = " ^ String.concat ", " (List.map string_of_norm_typ ts)));
    let ExT(aks2, t2) = s in
    let aks2' = freshen_vars env (rename_vars (prepend_path l) aks2) in
    let s' = ExT(aks2', subst_typ (subst aks2 (varTs aks2')) t2) in
    subst_extyp (subst aks1 ts) s', p, zs1 @ zs @ zs3,
    IL.AppE(IL.instE(ex1, List.map erase_typ ts), IL.AppE(f, IL.VarE(var2.it)))

  | EL.UnwrapE(var, typ) ->
    let aks, t, s2, zs2 =
      match elab_typ env typ l with
      | ExT([], WrapT(ExT(aks, t) as s2)), zs2 -> aks, t, s2, zs2
      | _ -> error typ.at "non-wrapped type for unwrap" in
    let t1, zs1, ex = elab_instvar env var in
    let s1 =
      match t1 with
      | WrapT(s1) -> s1
      | InferT(z) ->
        if resolve_typ z (WrapT(s2)) then s2
        else error var.at "inferred type would escape scope"
      | _ -> error var.at "expression is not a wrapped value" in
Trace.debug (lazy ("[UnwrapE] s1 = " ^ string_of_norm_extyp s1));
Trace.debug (lazy ("[UnwrapE] s2 = " ^ string_of_norm_extyp s2));
    let _, zs3, f = try sub_extyp env s1 s2 [] with Sub e -> error exp.at
      ("wrapped type does not match annotation: " ^ Sub.string_of_error e) in
    s2, Impure, lift_warn exp.at t (add_typs aks env) (zs1 @ zs2 @ zs3),
    IL.AppE(f, IL.DotE(ex, "wrap"))

  | EL.UnrollE(var, typ) ->
    let s, zs1 = elab_typ env typ l in
    let t, ak, t' =
      match s with
      | ExT([], (RecT(ak, t') as t)) -> t, ak, t'
      | _ -> error typ.at "non-recursive type for rolling" in
    let _, zs2, f = try sub_typ env (lookup_var env var) t [] with Sub e ->
      error var.at ("unrolled value does not match annotation") in
    ExT([], subst_typ (subst [ak] [t]) t'), Pure, zs1 @ zs2,
    IL.UnrollE(IL.AppE(f, IL.VarE(var.it)))

  | EL.RecE(var, typ, exp1) ->
    let ExT(aks1, t1) as s1, zs1 = elab_typ env typ l in
    let env1 = add_val var.it t1 (add_typs aks1 env) in
    (match aks1 with
    | [] ->
      let ExT(aks2, t2), p, zs2, e = elab_exp env1 exp1 l in
      if p <> Pure then error exp.at "recursive expression is not pure";
      let _, zs3, f =
        try sub_typ (add_typs aks2 env1) t2 t1 [] with Sub e -> error exp.at
          ("recursive expression does not match annotation: " ^
            Sub.string_of_error e)
      in
      (* TODO: syntactic restriction *)
      s1, Pure, lift_warn exp.at t1 (add_typs aks2 env) (zs1 @ zs2 @ zs3),
      IL.RecE(var.it, erase_typ t1, IL.AppE(f, e))
    | _ ->
      let t2, zs2 = elab_pathexp env1 exp1 l in
Trace.debug (lazy ("[RecT] s1 = " ^ string_of_norm_extyp s1));
Trace.debug (lazy ("[RecT] t2 = " ^ string_of_norm_typ t2));
      let ts, zs3, e =
        try sub_typ env1 t2 t1 (varTs aks1) with Sub e -> error typ.at
          ("recursive type does not match annotation: " ^ Sub.string_of_error e)
      in
Trace.debug (lazy ("[RecT] ts = " ^ String.concat ", " (List.map string_of_norm_typ ts)));
      let t3, k3 = try make_rec_typ t1 with Recursive ->
        error typ.at "illegal type for recursive expression" in
      let a = freshen_var env var.it in
      let tas1 = paths_typ (VarT(a, k3)) (varTs aks1) t1 in
      let t3' = subst_typ (subst aks1 tas1) (subst_typ (subst aks1 ts) t3) in
      let t4 = RecT((a, k3), t3') in
Trace.debug (lazy ("[RecT] t4 = " ^ string_of_norm_typ t4));
      let t = subst_typ (subst aks1 (List.map (subst_typ [a, t4]) tas1)) t1 in
Trace.debug (lazy ("[RecT] t = " ^ string_of_norm_typ t));
      ExT([], t), Pure, lift_warn exp.at t env (zs1 @ zs2 @ zs3),
      IL.LetE(e, "_", materialize_typ t)
    )

(*
rec (X : (b : type) => {type t; type u a}) fun (b : type) => {type t = (X int.u b, X bool.t); type u a = (a, X b.t)}
s1 = ?Xt:*->*, Xu:*->*->*. !b:*. [= b] -> {t : [= Xt b], u : !a:*. [= a] => [= Xu b a]}
s2 = !b:*. [= b] => {t : [= (Xu int b, Xt bool)], u : !a:*. [= a] => [= (a, Xt b)]}

as1 = Xt, Xu
ts = \b:*. (Xu int b, Xt bool), \b:*, a:*. (a, Xt b)
k3 = {t:*->*,u:*->*->*}
t3 = \b:*. {t = Xt b, u = \a:*. Xu b a}
tas1 = X.t, X.u
t3' = \b:*. {t = (X.u int b, X.t bool), u = \a:*. (a, X.t b)}
t4 = @X:{t:*->*,u:*->*->*}. \b:*. {t = (X.u int b, X.t bool), u = \a:*. (a, X.t b)}
t = !b:*. [= b] -> {t : [= t4.t b], u : !a:*. [= a] => [= (a, t4.u b a)]}
*)

and elab_bind env bind l =
  Trace.elab (lazy ("[elab_bind] " ^ EL.label_of_bind bind));
  (fun (s, p, zs, e) -> bind.at, env, s, zs, Some e, EL.label_of_bind bind) <<<
  match bind.it with
  | EL.VarB(var, exp) ->
    let l' = var.it in
    let ExT(aks, t), p, zs, e = elab_genexp env exp (append_path l l') in
    Trace.bind (lazy ("[VarB] " ^ l' ^ " : " ^
      string_of_norm_extyp (ExT(aks, t))));
    let s = ExT(aks, StrT[l', t]) in
    s, p, zs,
    IL.openE(e, List.map fst aks, var.it,
      IL.packE(List.map erase_typ (varTs aks), IL.TupE[l', IL.VarE(var.it)],
        erase_extyp s))

  | EL.InclB(exp) ->
    let ExT(aks, t) as s, p, zs, e = elab_instexp env exp l in
    (match t with
    | StrT(tr) -> ()
    | InferT(z) -> resolve_always z (StrT[])  (* TODO: row polymorphism *)
    | _ -> error bind.at "included expression is not a structure"
    );
    s, p, zs, e

  | EL.EmptyB ->
    ExT([], StrT[]), Pure, [], IL.TupE[]

  | EL.SeqB(bind1, bind2) ->
    (match elab_bind env bind1 l with
    | ExT(aks1, StrT(tr1)), p1, zs1, e1 ->
      (match elab_bind (add_row tr1 (add_typs aks1 env)) bind2 l with
      | ExT(aks2, StrT(tr2)), p2, zs2, e2 ->
        let tr1' = diff_row tr1 tr2 in
        let s = ExT(aks1 @ aks2, StrT(tr1' @ tr2)) in
        let x1 = IL.rename "x1" and x2 = IL.rename "x2" in
Trace.debug (lazy ("[SeqB] x1 : t1 = " ^ x1 ^ " : " ^ string_of_norm_typ (StrT(tr1))));
Trace.debug (lazy ("[SeqB] x2 : t2 = " ^ x2 ^ " : " ^ string_of_norm_typ (StrT(tr2))));
Trace.debug (lazy ("[SeqB] s = " ^ string_of_norm_extyp s));
        s, join_eff p1 p2,
        lift_warn bind.at (unexT s) env (zs1 @ zs2),  (* TODO: over-strict! *)
        IL.openE(e1, List.map fst aks1, x1,
          List.fold_right (fun (x, e1) e2 -> IL.LetE(e1, x, e2))
            (IL.eta_exprow x1 tr1)
            (IL.openE(e2, List.map fst aks2, x2,
              IL.packE(
                List.map erase_typ (varTs aks1 @ varTs aks2),
                IL.TupE(IL.eta_exprow x1 tr1' @ IL.eta_exprow x2 tr2),
                erase_extyp s
              )
            )
          )
        )
      | _ -> error bind.at "internal SeqB2"
      )
    | _ -> error bind.at "internal SeqB1"
    )

and elab_genexp env exp l =
  (fun (s, p, zs, e) -> exp.at, env, s, zs, Some e, "GenE") <<<
  let level = level () in
  let a1 = freshen_var env "$" in
Trace.debug (lazy ("[GenE] " ^ EL.string_of_exp exp));
Trace.debug (lazy ("[GenE] a1 = " ^ string_of_typ (VarT(a1, BaseK))));
  let ExT(aks, t) as s, p, zs, e = elab_exp (add_typ a1 BaseK env) exp l in
  let zs1, zs2 =
    List.partition (fun z ->
      match !z with
      | Undet u -> u.level >= level
      | Det _ -> assert false
    ) (lift (add_typs aks env) zs) in
  if p = Impure || zs1 = [] then
    s, p, zs1 @ zs2, e
  else begin
    assert (aks = []);
    let kr = List.mapi (fun i _ -> lab (i + 1), BaseK) zs1 in
    let k1 = ProdK(kr) in
    let ta1 = VarT(a1, ProdK(kr)) in
    let tr = map_rowi (fun l k -> TypT(ExT([], DotT(ta1, l)))) kr in
    List.iter2 (fun z (l, k) -> close_typ z (DotT(ta1, l))) zs1 kr;
    let t1' = StrT(tr) in
    ExT(aks, FunT([a1, k1], t1', ExT([], t), Implicit)), Pure, zs2,
    IL.GenE(a1, erase_kind k1, IL.LamE("_", erase_typ t1', e))
  end

and elab_instexp env exp l =
  (fun (s, p, zs, e) -> exp.at, env, s, zs, Some e, "InstE") <<<
  let ExT(aks, t), p, zs1, e = elab_exp env exp l in
  let t', zs2, e' = instantiate (add_typs aks env) t e in
  ExT(aks, t'), p, zs1 @ zs2, e'


let elab env exp =
  let s, p, zs, e = elab_exp env exp "" in
  s, p, e
