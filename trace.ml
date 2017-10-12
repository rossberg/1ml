(*
 * (c) 2014 Andreas Rossberg
 *)

(* Flags *)

let bind_flag = ref false
let elab_flag = ref false
let sub_flag = ref false
let debug_flag = ref false


(* Tracing *)

let trace flag s = if !flag then print_endline (Lazy.force s)

let bind = trace bind_flag
let elab = trace elab_flag
let sub = trace sub_flag
let debug = trace debug_flag
