(*
 * (c) 2014 Andreas Rossberg
 *)

open Source
open Types

module EL = Syntax
module IL = Fomega

exception Error of string

let quote x = "`" ^ x ^ "'"


(* Helpers *)

let eta_row a k r =
  List.map (fun (l, _) -> (l, DotT(VarT(a, k), l))) r

let eta_exprow x r =
  List.map (fun (l, _) -> (l, IL.DotE(IL.VarE(x), l))) r

let trace_sub_flag = ref false
let trace_elab_flag = ref false
let trace_debug_flag = ref true

let trace flag s = if !flag then print_endline (Lazy.force s)
let trace_sub = trace trace_sub_flag
let trace_elab = trace trace_elab_flag
let trace_debug = trace trace_debug_flag


(* Erasure *)

let rec erase_row erase = List.map (fun (l, z) -> l, erase z)

let rec erase_kind = function
  | BaseK -> IL.BaseK
  | ProdK(r) -> IL.ProdK(erase_row erase_kind r)
  | FunK(k1, k2) -> IL.ArrK(erase_kind k1, erase_kind k2)

let rec erase_typ = function
  | VarT(a, k) -> IL.varT(a, erase_kind k)
  | PrimT(n) -> IL.PrimT(n)
  | StrT(r) -> IL.ProdT(erase_row erase_typ r)
  | FunT(a, k, t, s, p) ->
    IL.AllT(a, erase_kind k, IL.ArrT(erase_typ t, erase_extyp s))
  | TypT(s) -> IL.ArrT(erase_extyp s, IL.StrT[])
  | PackT(s) -> erase_extyp s
  | ProdT(r) -> IL.StrT(erase_row erase_typ r)
  | LamT(a, k, t) -> IL.FunT(a, erase_kind k, erase_typ t)
  | DotT(t, l) -> IL.DotT(erase_typ t, l)
  | AppT(t1, t2) -> IL.AppT(erase_typ t1, erase_typ t2)

and erase_extyp = function
  | ExT(a, k, t) -> IL.AnyT(a, erase_kind k, erase_typ t)


(* Matching *)

type sub_error =
  | Missing
  | Mismatch of typ * typ
  | Struct of lab * sub_error
  | FunEffect of eff * eff
  | FunParam of sub_error
  | FunResult of sub_error
  | TypeLeft of sub_error
  | TypeRight of sub_error
  | PackageLeft of sub_error
  | PackageRight of sub_error

exception Sub of sub_error

let rec string_of_sub_error = function
  | Missing -> "missing"
  | Mismatch(t1, t2) ->
    "mismatch (" ^ string_of_typ_sort t1 ^ " vs " ^ string_of_typ_sort t2 ^ ")"
    ^ " (trying " ^ string_of_typ t1 ^ " < " ^ string_of_typ t2 ^ ")"
  | Struct(l, e) -> "field " ^ quote l ^ ": " ^ string_of_sub_error e
  | FunEffect(p1, p2) -> "mismatch (" ^
    string_of_eff_sort p1 ^ " vs " ^ string_of_eff_sort p2 ^ " function)"
  | FunParam e -> "function parameter type: " ^ string_of_sub_error e
  | FunResult e -> "function result type: " ^ string_of_sub_error e
  | TypeLeft e -> "left-hand type: " ^ string_of_sub_error e
  | TypeRight e -> "right-hand type: " ^ string_of_sub_error e
  | PackageLeft e -> "left-hand package: " ^ string_of_sub_error e
  | PackageRight e -> "right-hand package: " ^ string_of_sub_error e


let lookup_lab l r =
  try List.assoc l r with Not_found -> raise (Sub Missing)

let rec lookup_row kr tr1 tr2 =
  List.map (fun (l, k) ->
    try l, lookup_typ k (lookup_lab l tr1) (lookup_lab l tr2) with Sub e ->
      raise (Sub (Struct(l, e)))
  ) kr

and lookup_typ k t1 t2 =
  trace_sub (lazy ("[lookup_typ] k = " ^ string_of_kind k));
  trace_sub (lazy ("[lookup_typ] t1 = " ^ string_of_norm_typ t1));
  trace_sub (lazy ("[lookup_typ] t2 = " ^ string_of_norm_typ t2));
  match k, t1, t2 with
  | ProdK[], _, _ -> ProdT[]
  | BaseK, TypT(ExT(a, ProdK[], t)), _ -> t
  | ProdK(kr), StrT(tr1), StrT(tr2) -> ProdT(lookup_row kr tr1 tr2)
  | FunK(k3, k'),
    FunT(a1, k1, t11, ExT(_, ProdK[], t12), Pure),
    FunT(a2, k2, t21, ExT(_, ProdK[], t22), Pure) ->
    assert (k2 = k3);
    let t' = lookup_typ k1 t21 t11 in
    LamT(a2, k2, lookup_typ k' (subst_typ [a1, t'] t12) t22)
  | _, _, _ -> raise (Sub (Mismatch(t1, t2)))

let rec match_typ t1 (ExT(a, k, t2)) =
  trace_sub (lazy ("[match_typ] t = " ^ string_of_norm_typ t1));
  trace_sub (lazy ("[match_typ] s = " ^ string_of_norm_extyp (ExT(a, k, t2))));
  let t = lookup_typ k t1 t2 in
  t, sub_typ t1 (subst_typ [a, t] t2)

and sub_typ t1 t2 =
  trace_sub (lazy ("[sub_typ] t1 = " ^ string_of_norm_typ t1));
  trace_sub (lazy ("[sub_typ] t2 = " ^ string_of_norm_typ t2));
  let e1 = IL.VarE("x") in
  let e =
    match norm_typ t1, norm_typ t2 with
    | StrT(r1), StrT(r2) ->
      IL.StrE(List.map (fun (l, t2') ->
        let f = try sub_typ (lookup_lab l r1) t2' with Sub e ->
          raise (Sub (Struct(l, e)))
        in l, IL.AppE(f, IL.DotE(e1, l))
      ) r2)
    | FunT(a1, k1, t1', s1, p1), FunT(a2, k2, t2', s2, p2) ->
      if p1 = Impure && p2 = Pure then
        raise (Sub (FunEffect(p1, p2)));
      let t, f1 = try match_typ t2' (ExT(a1, k1, t1')) with Sub e ->
        raise (Sub (FunParam e)) in
      let f2 = try sub_extyp (subst_extyp [a1, t] s1) s2 with Sub e ->
        raise (Sub (FunResult e)) in
      IL.GenE(a2, erase_kind k2, (IL.FunE("y", erase_typ t2',
        IL.AppE(f2, IL.AppE(IL.InstE(e1, erase_typ t),
          IL.AppE(f1, IL.VarE("y")))))))
    | TypT(s1), TypT(s2) ->
      let _ = try sub_extyp s1 s2 with Sub e -> raise (Sub (TypeLeft e)) in
      let _ = try sub_extyp s2 s1 with Sub e -> raise (Sub (TypeRight e)) in
      e1
    | PackT(s1), PackT(s2) ->
      let _ = try sub_extyp s1 s2 with Sub e -> raise (Sub (PackageLeft e)) in
      let _ = try sub_extyp s2 s1 with Sub e -> raise (Sub (PackageRight e)) in
      e1
    | AppT(t11, t12), AppT(t21, t22) ->
      (try
        let _ = sub_typ t11 t21 in let _ = sub_typ t21 t11 in
        let _ = sub_typ t12 t22 in let _ = sub_typ t22 t12 in
        e1
      with Sub e ->
        raise (Sub (Mismatch(t1, t2)))
      )
    | DotT(t1', l1), DotT(t2', l2) ->
      if l1 <> l2 then raise (Sub (Mismatch(t1, t2))) else
      (try
        let _ = sub_typ t1' t2' in let _ = sub_typ t2' t1' in e1
      with Sub e ->
        raise (Sub (Mismatch(t1, t2)))
      )
    | t1', t2' when t1' = t2' -> e1
    | _ -> raise (Sub (Mismatch(t1, t2)))
  in IL.FunE("x", erase_typ t1, e)

and sub_extyp (ExT(a1, k1, t1) as s1) s2 =
  trace_sub (lazy ("[sub_extyp] s1 = " ^ string_of_norm_extyp s1));
  trace_sub (lazy ("[sub_extyp] s2 = " ^ string_of_norm_extyp s2));
  let t, f = match_typ t1 s2 in
  IL.FunE("x", erase_extyp s1, IL.OpenE(IL.VarE("x"), a1, "y",
    IL.PackE(erase_typ t, IL.AppE(f, IL.VarE("y")), erase_extyp s2)))


(* Type Elaboration *)

let rec refine_typ k t ls =
  trace_sub (lazy ("[refine_typ] k = " ^ string_of_kind k));
  trace_sub (lazy ("[refine_typ] t = " ^ string_of_norm_typ t));
  trace_sub (lazy ("[refine_typ] ls = " ^ String.concat "." ls));
  match ls with
  | [] -> t, k, ProdK[], fun t_root t_new -> t_new
  | l::ls ->
    match k, t with
    | ProdK(kr), StrT(tr) ->
      let kl = List.assoc l kr in
      let tl = List.assoc l tr in
      let t_ls, k_ls, kl', tf = refine_typ kl tl ls in
      let kr', tfr =
        List.fold_right (fun (l', k) (kr', tfr) ->
          if l = l' then
            (if kl' = ProdK[] then kr' else (l, kl')::kr'),
            (l, fun t_root t_new -> tf (DotT(t_root, l)) t_new)::tfr
          else
            (l', k)::kr',
            (l', fun t_root t_new -> DotT(t_root, l'))::tfr
        ) kr ([], []) in
      t_ls, k_ls, ProdK(kr'),
      fun t_root t_new ->
        ProdT(List.map (fun (l, tf) -> l, tf t_root t_new) tfr)
    | _ -> raise Not_found


let elab_eff env eff =
  match eff.it with
  | EL.Pure -> Pure
  | EL.Impure -> Impure

let rec elab_typ env typ l =
  trace_elab (lazy ("[elab_typ] " ^ EL.label_of_typ typ));
  match typ.it with
  | EL.PathT(exp) ->
    (match elab_pathexp env exp l with
    | TypT(s) -> s
    | _ -> error typ.at "expression does not denote a type"
    )
  | EL.PrimT(n) ->
    (match Prim.typ_of_string n with
    | Some t -> ExT("_", ProdK[], PrimT(t))
    | None -> error typ.at "unknown primitive type"
    )
  | EL.StrT(dec) -> elab_dec env dec l
  | EL.FunT(var, typ1, typ2, eff) ->
    let ExT(a1, k1, t1) =
      freshen_extyp (range env) (elab_typ env typ1 var.it) in
trace_debug (lazy ("[FunT] s1 = " ^ string_of_norm_extyp (ExT(a1, k1, t1))));
    let s2 = elab_typ ((var.it, t1)::env) typ2 l in
trace_debug (lazy ("[FunT] s2 = " ^ string_of_norm_extyp s2));
    (match elab_eff env eff with
    | Impure -> ExT("_", ProdK[], FunT(a1, k1, t1, s2, Impure))
    | Pure ->
      let ExT(a2, k2, t2) = freshen_extyp [VarT(a1, k1)] s2 in
      let k2', t2' = if k2 = ProdK[] then k2, t2 else
        let k2' = FunK(k1, k2) in
        k2', subst_typ [a2, AppT(VarT(a2, k2'), VarT(a1, k1))] t2 in
      ExT(a2, k2', FunT(a1, k1, t1, ExT("_", ProdK[], t2'), Pure))
    )
  | EL.TypT ->
    ExT(l, BaseK, TypT(ExT("_", ProdK[], VarT(l, BaseK))))
  | EL.PackT(typ1) ->
    let s1 = elab_typ env typ1 "pack" in
    ExT("_", ProdK[], PackT(s1))
  | EL.LikeT(exp) ->
    let t = elab_pathexp env exp l in
    ExT("_", ProdK[], t)
  | EL.WithT(typ1, vars, exp) ->
    let t2 = elab_pathexp env exp "with" in
    let ExT(a1, k1, t1) = freshen_extyp [t2] (elab_typ env typ1 l) in
    let ls = List.map (fun var -> var.it) vars in
verbose_binders_flag := true; verbose_paths_flag := true;
trace_debug (lazy ("[WithT] s1 = " ^ string_of_norm_extyp (ExT(a1, k1, t1))));
trace_debug (lazy ("[WithT] ls = " ^ String.concat "." ls));
trace_debug (lazy ("[WithT] t2 = " ^ string_of_norm_typ t2));
    let t1_ls, k1_ls, k1', tf = try refine_typ k1 t1 ls with Not_found ->
      error typ.at
        ("path " ^ quote (String.concat "." ls) ^ " unbound or not a type") in
trace_debug (lazy ("[WithT] t1_ls = " ^ string_of_norm_typ t1_ls));
trace_debug (lazy ("[WithT] k1_ls = " ^ string_of_kind k1_ls));
    let ta =
      try
trace_debug (lazy ("[WithT] t = " ^ string_of_norm_typ (lookup_typ k1_ls t2 t1_ls)));
        let ta = tf (VarT(a1, k1')) (lookup_typ k1_ls t2 t1_ls) in
trace_debug (lazy ("[WithT] ta = " ^ string_of_norm_typ ta));
trace_debug (lazy ("[WithT] ta' = " ^ string_of_norm_typ (subst_typ [a1, ta] t1_ls)));
        let _ = sub_typ t2 (subst_typ [a1, ta] t1_ls) in
        ta
      with Sub e ->
        error exp.at
          ("refinement does not match respective type: " ^
            string_of_sub_error e) in
trace_debug (lazy ("[WithT] s = " ^ string_of_norm_extyp (ExT(a1, k1, t1))));
trace_debug (lazy ("[WithT] s' = " ^ string_of_norm_extyp (ExT(a1, k1', subst_typ [a1, ta] t1))));
verbose_binders_flag := false; verbose_paths_flag := false;
    ExT(a1, k1', subst_typ [a1, ta] t1)

and elab_dec env dec l =
  trace_elab (lazy ("[elab_dec] " ^ EL.label_of_dec dec));
  match dec.it with
  | EL.VarD(var, typ) ->
    let l = var.it in
    let ExT(a, k, t) = elab_typ env typ var.it in
    let k' = if k = ProdK[] then ProdK[] else ProdK[l, k] in
    ExT(a, k', StrT[l, subst_typ [a, DotT(VarT(a, k'), l)] t])
  | EL.InclD(typ) ->
    let ExT(a, k, t) as s = elab_typ env typ l in
    (match t with
    | StrT _ -> s
    | _ -> error dec.at "included type is not a structure"
    )
  | EL.EmptyD ->
    ExT("_", ProdK[], StrT[])
  | EL.SeqD(dec1, dec2) ->
    (match freshen_extyp (range env) (elab_dec env dec1 l) with
    | ExT(a1, ProdK(kr1), StrT(tr1)) ->
      (match elab_dec (tr1 @ env) dec2 l with
      | ExT(a2, ProdK(kr2), StrT(tr2)) ->
        (match intersect_row tr1 tr2 with
        | [] ->
          let k = ProdK(kr1 @ kr2) in
trace_debug (lazy ("[SeqD] k1 = " ^ string_of_kind (ProdK kr1)));
trace_debug (lazy ("[SeqD] k2 = " ^ string_of_kind (ProdK kr2)));
trace_debug (lazy ("[SeqD] k = " ^ string_of_kind k));
          let a =
            if k = ProdK[] then "_" else freshen_var [StrT(tr1); StrT(tr2)] l in
          let t1 = ProdT(eta_row a k kr1) in
          let t2 = ProdT(eta_row a k kr2) in
          let tr = subst_row [a1, t1] tr1 @ subst_row [a2, t2; a1, t1] tr2 in
trace_debug (lazy ("[SeqD] t1 = " ^ string_of_norm_typ (StrT(tr1))));
trace_debug (lazy ("[SeqD] t2 = " ^ string_of_norm_typ (StrT(tr2))));
trace_debug (lazy ("[SeqD] s = " ^ string_of_norm_extyp (ExT(a, k, StrT(tr)))));
          ExT(a, k, StrT(tr))
        | ls ->
          error dec.at ("multiple declarations for " ^
            String.concat ", " (List.map (fun (l, _) -> quote l) ls))
        )
      | _ -> error dec.at "internal SeqD2"
      )
    | _ -> error dec.at "internal SeqD1"
    )

and elab_pathexp env exp l =
  trace_elab (lazy ("[elab_pathexp] " ^ EL.label_of_exp exp));
  let ExT(a, k, t), p, _ = elab_exp env exp l in
trace_debug (lazy ("[ExpP] s = " ^ string_of_norm_extyp (ExT(a, k, t))));
  if p = Impure then
    error exp.at "impure path expression";
  if occurs_typ a t then
    error exp.at
      ("local type(s) " ^ quote a ^ ":" ^ string_of_kind k ^ " escape scope")
  else
    t


(* Expression elaboration *)

and lookup_var env var =
  try List.assoc var.it env with Not_found ->
    error var.at ("unbound identifier " ^ quote var.it)

and elab_prim_typ = function
  | Prim.VarT -> VarT("a", BaseK)
  | t -> PrimT(t)

and elab_prim_typs = function
  | [t] -> elab_prim_typ t
  | ts ->
    StrT(List.mapi (fun i t -> "_" ^ string_of_int (i + 1), elab_prim_typ t) ts)

and elab_prim_fun f =
  let t1 = elab_prim_typs (fst f.Prim.typ) in
  let t2 = elab_prim_typs (snd f.Prim.typ) in
  let t = FunT("_", ProdK[], t1, ExT("_", ProdK[], t2), Impure) in
  let e = IL.PrimE(Prim.FunV f) in
  if Prim.is_poly f then
    let ta = TypT(ExT("_", ProdK[], VarT("a", BaseK))) in
    FunT("a", BaseK, ta, ExT("_", ProdK[], t), Impure),
    IL.GenE("a", IL.BaseK, IL.FunE("_", erase_typ ta, e))
  else
    t, e

and elab_const = function
  | Prim.FunV(f) -> elab_prim_fun f
  | c -> PrimT(Prim.typ_of_const c), IL.PrimE(c)

and elab_exp env exp l =
  trace_elab (lazy ("[elab_exp] " ^ EL.label_of_exp exp));
  match exp.it with
  | EL.VarE(var) ->
trace_debug (lazy ("[VarE] x = " ^ var.it));
trace_debug (lazy ("[VarE] s = " ^ string_of_norm_extyp (ExT("_", ProdK[], lookup_var env var))));
    ExT("_", ProdK[], lookup_var env var), Pure, IL.VarE(var.it)
  | EL.PrimE(c) ->
    let t, e = elab_const c in
    ExT("_", ProdK[], t), Pure, e
  | EL.TypE(typ) ->
    let s = elab_typ env typ l in
    ExT("_", ProdK[], TypT(s)), Pure, IL.FunE("_", erase_extyp s, IL.StrE[])
  | EL.StrE(bind) ->
trace_debug (lazy ("[StrE] l = " ^ l));
    elab_bind env bind l
  | EL.FunE(var, typ, exp2) ->
    let ExT(a, k, t) = freshen_extyp (range env) (elab_typ env typ var.it) in
    let s, p, e2 = elab_exp ((var.it, t)::env) exp2 l in
    ExT("_", ProdK[], FunT(a, k, t, s, p)), Pure,
    IL.GenE(a, erase_kind k, IL.FunE(var.it, erase_typ t, e2))
  | EL.PackE(var, typ) ->
    let s = elab_typ env typ "pack" in
trace_debug (lazy ("[PackE] t = " ^ string_of_norm_typ (lookup_var env var)));
trace_debug (lazy ("[PackE] s = " ^ string_of_extyp s));
    let f =
      try sub_extyp (ExT("_", ProdK[], lookup_var env var)) s with Sub e ->
        error exp.at
          ("packaged type does not match annotation: " ^ string_of_sub_error e)
    in ExT("_", ProdK[], PackT(s)), Pure, IL.AppE(f, IL.VarE(var.it))
  | EL.IfE(var, exp1, exp2, typ) ->
    (match lookup_var env var with
    | PrimT(Prim.BoolT) ->
      let s1, p1, e1 = elab_exp env exp1 l in
      let s2, p2, e2 = elab_exp env exp2 l in
      let s = elab_typ env typ l in
      let f1 = try sub_extyp s1 s with Sub e -> error exp1.at
        ("branch type does not match annotation: " ^ string_of_sub_error e) in
      let f2 = try sub_extyp s2 s with Sub e -> error exp2.at
        ("branch type does not match annotation: " ^ string_of_sub_error e) in
      s, join_eff p1 p2,
      IL.IfE(IL.VarE(var.it), IL.AppE(f1, e1), IL.AppE(f2, e2))
    | _ -> error var.at "condition is not Boolean"
    )
  | EL.DotE(exp1, var) ->
    (match elab_exp env exp1 l with
    | ExT(a, k, StrT(tr)), p, e1 ->
trace_debug (lazy ("[DotE] l = " ^ var.it));
trace_debug (lazy ("[DotE] s = " ^ string_of_extyp (ExT(a, k, StrT(tr)))));
      let t = try List.assoc var.it tr with Not_found ->
        error exp.at ("field " ^ quote var.it ^ " unbound in expression") in
      let s = ExT(a, k, t) in
      s, p, IL.OpenE(e1, a, "x",
        IL.PackE(IL.VarT(a), IL.DotE(IL.VarE("x"), var.it), erase_extyp s))
    | _ -> error exp1.at "expression is not a structure"
    )
  | EL.AppE(var1, var2) ->
    (match lookup_var env var1 with
    | FunT(a, k, t1, s, p) ->
trace_debug (lazy ("[AppE] s1 = " ^ string_of_norm_extyp (ExT(a, k, t1))));
trace_debug (lazy ("[AppE] t2 = " ^ string_of_norm_typ (lookup_var env var2)));
      let t, f =
        try match_typ (lookup_var env var2) (ExT(a, k, t1)) with Sub e ->
          error var2.at
            ("argument type does not match function: " ^ string_of_sub_error e)
      in
      subst_extyp [a, t] s, p,
      IL.AppE(IL.InstE(IL.VarE(var1.it), erase_typ t),
        IL.AppE(f, IL.VarE(var2.it)))
    | _ -> error var1.at "expression is not a function"
    )
  | EL.UnpackE(var, typ) ->
    (match lookup_var env var with
    | PackT(s1) ->
      let ExT(a, k, t) as s2 = elab_typ env typ l in
trace_debug (lazy ("[UnpackE] s1 = " ^ string_of_norm_extyp s1));
trace_debug (lazy ("[UnpackE] s2 = " ^ string_of_norm_extyp s2));
      let f = try sub_extyp s1 s2 with Sub e -> error exp.at
        ("package type does not match annotation: " ^ string_of_sub_error e) in
      let a' = freshen_var [t] l in
trace_debug (lazy ("[UnpackE] s2' = " ^ string_of_norm_extyp (ExT(a', k, subst_typ [a, VarT(a', k)] t))));
      ExT(a', k, subst_typ [a, VarT(a', k)] t),
      Impure, IL.AppE(f, IL.VarE(var.it))
    | _ -> error var.at "expression is not a package"
    )

and elab_bind env bind l =
  trace_elab (lazy ("[elab_bind] " ^ EL.label_of_bind bind));
  match bind.it with
  | EL.VarB(var, exp) ->
    let l = var.it in
    let ExT(a, k, t), p, e = elab_exp env exp l in
    let k' = if k = ProdK[] then ProdK[] else ProdK[l, k] in
    let s = ExT(a, k', StrT[l, subst_typ [a, DotT(VarT(a, k'), l)] t]) in
trace_debug (lazy ("[VarB] s = " ^ string_of_norm_extyp s));
    s, p, IL.OpenE(e, a, var.it,
      IL.PackE(IL.VarT(a), IL.StrE[l, IL.VarE(var.it)], erase_extyp s))
  | EL.InclB(exp) ->
    let ExT(a, k, t) as s, p, e = elab_exp env exp l in
    (match t with
    | StrT _ -> s, p, e
    | _ -> error bind.at "expression is not a structure"
    )
  | EL.EmptyB ->
    ExT("_", ProdK[], StrT[]), Pure, IL.StrE[]
  | EL.SeqB(bind1, bind2) ->
    let s1, p1, e1 = elab_bind env bind1 l in
    (match freshen_extyp (range env) s1 with
    | ExT(a1, ProdK(kr1), StrT(tr1)) ->
      (match elab_bind (tr1 @ env) bind2 l with
      | ExT(a2, ProdK(kr2), StrT(tr2)), p2, e2 ->
        let tr1' = diff_row tr1 tr2 in
        let kr1', kr1'' =
          List.partition (fun (l, _) -> List.mem_assoc l tr1') kr1 in
        let kr1''' =
          if kr1'' = [] then [] else [Fomega.rename "", ProdK kr1''] in
        let k = ProdK(kr1''' @ kr1' @ kr2) in
trace_debug (lazy ("[SeqB] k1 = " ^ string_of_kind (ProdK kr1)));
trace_debug (lazy ("[SeqB] k2 = " ^ string_of_kind (ProdK kr2)));
trace_debug (lazy ("[SeqB] k1' = " ^ string_of_kind (ProdK kr1')));
trace_debug (lazy ("[SeqB] k1'' = " ^ string_of_kind (ProdK kr1'')));
trace_debug (lazy ("[SeqB] k1''' = " ^ string_of_kind (ProdK kr1''')));
trace_debug (lazy ("[SeqB] k = " ^ string_of_kind k));
        let a =
          if k = ProdK[] then "_" else freshen_var [StrT(tr1'); StrT(tr2)] l in
        let t1 = ProdT(eta_row a k kr1) in
        let t2 = ProdT(eta_row a k kr2) in
        let tr = subst_row [a1, t1] tr1' @ subst_row [a2, t2; a1, t1] tr2 in
        let s = ExT(a, k, StrT(tr)) in
trace_debug (lazy ("[SeqB] t1 = " ^ string_of_norm_typ (StrT(tr1))));
trace_debug (lazy ("[SeqB] t2 = " ^ string_of_norm_typ (StrT(tr2))));
trace_debug (lazy ("[SeqB] s = " ^ string_of_norm_extyp s));
        let x1 = Fomega.rename "" and x2 = Fomega.rename "" in
        s, join_eff p1 p2,
        IL.OpenE(e1, a1, x1,
          IL.letE(
            List.map2 (fun (l, e) (_, t) -> l, erase_typ t, e)
              (eta_exprow x1 tr1) tr1,
            IL.OpenE(e1, a2, x2,
              IL.PackE(IL.VarT(a1),
                IL.StrE(eta_exprow x1 tr1' @ eta_exprow x2 tr2),
                erase_extyp s
              )
            )
          )
        )
      | _ -> error bind.at "internal SeqB2"
      )
    | _ -> error bind.at "internal SeqB1"
    )


let elab env exp = elab_exp env exp "prog"
