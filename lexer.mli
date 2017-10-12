(*
 * (c) 2014 Andreas Rossberg
 *)

val convert_pos : Lexing.position -> Source.pos

val token : Lexing.lexbuf -> Parser.token  (* raises Source.Error *)
