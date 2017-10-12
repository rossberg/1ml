(*
 * (c) 2014 Andreas Rossberg
 *)

type pos = {file : string; line : int; column : int}
type region = {left : pos; right : pos}

type ('a, 'b) phrase =
  { at : region;
    it : 'a;
    mutable sem : 'b option
  }

exception Error of region * string

val nowhere_pos : pos
val nowhere_region : region

val string_of_pos : pos -> string
val string_of_region : region -> string

val before : region -> region
val after : region -> region
val span : region list -> region

val (@@) : 'a -> region -> ('a, 'b) phrase
val (@@@) : 'a -> region list -> ('a, 'b) phrase
val (<~) : ('a, 'b) phrase -> 'b -> 'b
val dup : ('a, 'b) phrase -> ('a, 'b) phrase

val at : ('a, 'b) phrase -> region
val it : ('a, 'b) phrase -> 'a
val sem : ('a, 'b) phrase -> 'b

val warn : region -> string -> unit
val error : region -> string -> 'a  (* raises Error *)
val indent : string -> string
