(*
 * (c) 2014 Andreas Rossberg
 *)

(* Elaboration *)

exception Error of string

val elab : Env.env -> Syntax.exp -> Types.extyp * Types.eff * Fomega.exp


(* Flags *)

val verify_flag : bool ref
val verify_fomega_flag : bool ref
