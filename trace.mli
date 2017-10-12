(*
 * (c) 2014 Andreas Rossberg
 *)

(* Flags *)

val bind_flag : bool ref
val elab_flag : bool ref
val sub_flag : bool ref
val debug_flag : bool ref


(* Tracing *)

val bind : string Lazy.t -> unit
val elab : string Lazy.t -> unit
val sub : string Lazy.t -> unit
val debug : string Lazy.t -> unit
