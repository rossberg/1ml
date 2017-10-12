(*
 * (c) 2014 Andreas Rossberg
 *)

(* Syntax *)

type level = int
type lab = Fomega.lab
type var = Fomega.var

module VarSet = Fomega.VarSet
type varset = VarSet.t

type 'a row = (lab * 'a) list

type eff =
  | Impure
  | Pure

type feff =
  | Explicit of eff
  | Implicit

type kind =
  | BaseK
  | ProdK of kind row
  | FunK of kind list * kind

type typ =
  | VarT of var * kind
  | PrimT of Prim.typ
  | StrT of typ row
  | FunT of (var * kind) list * typ * extyp * feff
  | TypT of extyp
  | WrapT of extyp
  | LamT of (var * kind) list * typ
  | AppT of typ * typ list
  | TupT of typ row
  | DotT of typ * lab
  | RecT of (var * kind) * typ
  | InferT of infer ref

and extyp =
  | ExT of (var * kind) list * typ

and infer =
  | Undet of undet
  | Det of typ

and undet =
  { id : int;
    mutable level : level;
    mutable vars : varset;
    mutable il : Fomega.typ lazy_t option
  }


(* Construction helpers *)

val funK : kind list * kind -> kind

val lamT : (var * kind) list * typ -> typ
val appT : typ * typ list -> typ

val varTs : (var * kind) list -> typ list

val unvarT : typ -> var * kind
val unexT : extyp -> typ


(* Path names *)

val default_path : var -> lab -> var
val append_path : var -> lab -> var
val prepend_path : lab -> var -> var
val cut_path : lab -> var -> var

val rename_vars : (var -> var) -> (var * kind) list -> (var * kind) list


(* Effects *)

val join_eff : eff -> eff -> eff


(* Rows *)

val lab : int -> lab

val tup_row : 'a list -> 'a row
val as_tup_row : 'a row -> 'a list option

val map_row : ('a -> 'b) -> 'a row -> 'b row
val map_rowi : (lab -> 'a -> 'b) -> 'a row -> 'b row

val intersect_row : 'a row -> 'a row -> 'a row
val diff_row : 'a row -> 'a row -> 'a row

val project_typ : lab list -> typ -> typ (* raise Not_found *)


(* Size check *)

val is_small_typ : typ -> bool
val is_small_extyp : extyp -> bool


(* Free variables and occurrence check *)

val vars_typ : typ -> varset
val vars_extyp : extyp -> varset

val contains_typ : var -> typ -> bool
val contains_extyp : var -> extyp -> bool

val occurs_typ : undet -> typ -> bool
val occurs_extyp : undet -> extyp -> bool

(* TODO: remove
val undet_typ : level -> typ -> infer ref list
val undet_extyp : level -> extyp -> infer ref list
*)


(* Substitution *)

type subst = (var * typ) list

val subst : (var * kind) list -> typ list -> subst

val subst_typ : subst -> typ -> typ
val subst_extyp : subst -> extyp -> extyp
val subst_row : subst -> typ row -> typ row

val subst_infer : subst -> infer ref -> unit


(* Normalisation *)

val follow_typ : typ -> typ

val norm_typ : typ -> typ
val norm_extyp : extyp -> extyp


(* Kinding *)

exception Kind

val kind_of_typ : typ -> kind (* raise Kind *)
val kind_of_extyp : extyp -> kind (* raise Kind *)


(* Unification *)

val level : unit -> level
val stamp : unit -> level

val guess_typ : varset -> kind -> typ * infer ref list
val guess_typs : varset -> (var * kind) list -> typ list * infer ref list

val resolve_typ : infer ref -> typ -> bool
val resolve_always : infer ref -> typ -> unit
val close_typ : infer ref -> typ -> unit

val unify_typ : typ -> typ -> bool

val undecidable_flag : bool ref


(* String conversion *)

val verbose_binders_flag : bool ref
val verbose_paths_flag : bool ref
val verbose_vars_flag : bool ref
val verbose_levels_flag : bool ref

val verbosest_on : unit -> unit
  
val string_of_eff_sort : eff -> string
val string_of_typ_sort : typ -> string

val string_of_kind : kind -> string
val string_of_typ : typ -> string
val string_of_extyp : extyp -> string

val string_of_norm_typ : typ -> string
val string_of_norm_extyp : extyp -> string


(* Formatting *)

val print_kind : kind -> unit
val print_typ : typ -> unit
val print_extyp : extyp -> unit
val print_row : typ row -> unit
