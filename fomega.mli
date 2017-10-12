(*
 * (c) 2014 Andreas Rossberg
 *)

(* Syntax *)

type lab = string
type var = string

type 'a row = (lab * 'a) list

type kind =
  | BaseK
  | ArrK of kind * kind
  | ProdK of kind row

type typ =
  | VarT of var
  | PrimT of Prim.typ
  | ArrT of typ * typ
  | ProdT of typ row
  | AllT of var * kind * typ
  | AnyT of var * kind * typ
  | LamT of var * kind * typ
  | AppT of typ * typ
  | TupT of typ row
  | DotT of typ * lab
  | RecT of var * kind * typ
  | InferT of typ lazy_t * int

type exp =
  | VarE of var
  | PrimE of Prim.const
  | IfE of exp * exp * exp
  | LamE of var * typ * exp
  | AppE of exp * exp
  | TupE of exp row
  | DotE of exp * lab
  | GenE of var * kind * exp
  | InstE of exp * typ
  | PackE of typ * exp * typ
  | OpenE of exp * var * var * exp
  | RollE of exp * typ
  | UnrollE of exp
  | RecE of var * typ * exp
  | LetE of exp * var * exp

exception Error of string


(* Renaming *)

module VarSet : Set.S with type elt = var

val rename : var -> var
val rename_for : VarSet.t -> var -> var


(* Environments *)

type env

val empty : env
val add_typ : var -> kind -> env -> env
val add_val : var -> typ -> env -> env

val lookup_typ : var -> env -> kind (* raise Error *)
val lookup_val : var -> env -> typ (* raise Error *)


(* Substitutions *)

type 'a subst = (var * 'a) list

val subst_typ : typ subst -> typ -> typ
val subst_typ_exp : typ subst -> exp -> exp
val subst_exp : exp subst -> exp -> exp


(* Normalisation and Equality *)

val varT : var * kind -> typ  (* eta-long-normal *)

val norm_typ : typ -> typ (* raise Error *)  (* beta normalisation *)
val norm_exp : exp -> exp (* raise Error *)

val equal_typ : typ -> typ -> bool (* raise Error *)

val force_typ : typ -> typ


(* Checking *)

val infer_typ : env -> typ -> kind (* raise Error *)
val infer_exp : env -> exp -> typ (* raise Error *)

val check_typ : env -> typ -> kind -> string -> unit (* raise Error *)
val check_exp : env -> exp -> typ -> string -> unit (* raise Error *)


(* Unrolling *)

val unroll_typ : typ -> typ option


(* String conversion *)

val verbose_exp_flag : bool ref
val verbose_typ_flag : bool ref

val string_of_kind : kind -> string
val string_of_typ : typ -> string
val string_of_exp : exp -> string
