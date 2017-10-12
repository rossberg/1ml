(*
 * (c) 2014 Andreas Rossberg
 *)

include Fomega

let eta_typrow a r = Types.map_rowi (fun l _ -> DotT(VarT(a), l)) r
let eta_exprow x r = Types.map_rowi (fun l _ -> DotE(VarE(x), l)) r

let arrK(ks, k) = List.fold_right (fun ki k -> ArrK(ki, k)) ks k

let allT(aks, t) = List.fold_right (fun (a, k) t -> AllT(a, k, t)) aks t
let anyT(aks, t) = List.fold_right (fun (a, k) t -> AnyT(a, k, t)) aks t
let lamT(aks, t) = List.fold_right (fun (a, k) t -> LamT(a, k, t)) aks t
let appT(t, ts) = List.fold_left (fun t ti -> AppT(t, ti)) t ts

let genE(aks, e) = List.fold_right (fun (a, k) e -> GenE(a, k, e)) aks e
let instE(e, ts) = List.fold_left (fun e ti -> InstE(e, ti)) e ts

let rec packE(ts, e, t) =
  match ts, t with
  | [], _ -> e
  | t1::ts', AnyT(a, k, t') ->
    PackE(t1, packE(ts', e, subst_typ [a, t1] t'), t)
  | _ -> assert false

let rec openE(e1, vs, x, e2) =
  match vs with
  | [] -> LetE(e1, x, e2)
  | [a] -> OpenE(e1, a, x, e2)
  | a::vs' -> OpenE(e1, a, x, openE(VarE(x), vs', x, e2))
