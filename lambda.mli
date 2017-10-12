(*
 * (c) 2014 Andreas Rossberg
 *)

(* Syntax *)

type var = string
type lab = string

module Env : Map.S with type key = var
type env = value Env.t

and exp =
  | VarE of var
  | PrimE of Prim.const
  | IfE of exp * exp * exp
  | LamE of var * exp
  | AppE of exp * exp
  | TupE of exp list
  | DotE of exp * int
  | RecE of var * exp
  | LetE of exp * var * exp

and value =
  | PrimV of Prim.const
  | TupV of value list
  | FunV of env * var * exp
  | RecV of value option ref


(* Evaluation *)

exception Error of string

val eval : env -> exp -> value


(* String conversion *)

val string_of_value : value -> string
