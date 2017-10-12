(*
 * (c) 2014 Andreas Rossberg
 *)

val erase_kind : Types.kind -> Fomega.kind
val erase_typ : Types.typ -> Fomega.typ
val erase_extyp : Types.extyp -> Fomega.typ
val erase_bind :
  (Types.var * Types.kind) list -> (Fomega.var * Fomega.kind) list
val erase_env : Env.env -> Fomega.env
