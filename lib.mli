(*
 * (c) 2014 Andreas Rossberg
 *)

module List :
sig
  val last : 'a list -> 'a (* raise Failure *)
  val take : int -> 'a list -> 'a list
  val drop : int -> 'a list -> 'a list

  val for_alli : (int -> 'a -> bool) -> 'a list -> bool

  val merge_nodup : 'a list -> 'a list -> 'a list
end

module String :
sig
  val is_prefix : string -> string -> bool
  val split : string -> int -> string * string
end
