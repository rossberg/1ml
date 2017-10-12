(*
 * (c) 2014 Andreas Rossberg
 *)

type typ =
  | BoolT
  | IntT
  | TextT
  | VarT

type const =
  | BoolV of bool
  | IntV of int
  | TextV of string
  | FunV of func

and func =
  { name : string;
    typ : typ list * typ list;
    fn : const list -> const list
  }

let typ_of_string = function
  | "bool" -> Some BoolT
  | "int" -> Some IntT
  | "text" -> Some TextT
  | _ -> None

let string_of_typ = function
  | BoolT -> "bool"
  | IntT -> "int"
  | TextT -> "text"
  | VarT -> assert false

let typ_of_const = function
  | BoolV _ -> BoolT
  | IntV _ -> IntT
  | TextV _ -> TextT
  | FunV _ -> assert false

let string_of_const = function
  | BoolV(b) -> string_of_bool b
  | IntV(i) -> string_of_int i
  | TextV(t) -> "\"" ^ String.escaped t ^ "\""
  | FunV(f) -> "(prim " ^ f.name ^ ")"

let is_poly {typ = ts1, ts2} = List.mem VarT ts1 || List.mem VarT ts2

let typs = [BoolT; IntT; TextT]

let funs =
  [
    {name = "true";
      typ = [], [BoolT];
      fn = fun [] -> [BoolV(true)]};
    {name = "false";
      typ = [], [BoolT];
      fn = fun [] -> [BoolV(false)]};
    {name = "+";
      typ = [IntT; IntT], [IntT];
      fn = fun [IntV i1; IntV i2] -> [IntV(i1 + i2)]};
    {name = "-";
      typ = [IntT; IntT], [IntT];
      fn = fun [IntV i1; IntV i2] -> [IntV(i1 - i2)]};
    {name = "*";
      typ = [IntT; IntT], [IntT];
      fn = fun [IntV i1; IntV i2] -> [IntV(i1 * i2)]};
    {name = "++";
      typ = [TextT; TextT], [TextT];
      fn = fun [TextV t1; TextV t2] -> [TextV(t1 ^ t2)]};
    {name = "==";
      typ = [VarT; VarT], [BoolT];
      fn = fun [x1; x2] -> [BoolV(x1 = x2)]};
    {name = "<>";
      typ = [VarT; VarT], [BoolT];
      fn = fun [x1; x2] -> [BoolV(x1 <> x2)]};
    {name = "<";
      typ = [IntT; IntT], [BoolT];
      fn = fun [x1; x2] -> [BoolV(x1 < x2)]};
    {name = ">";
      typ = [IntT; IntT], [BoolT];
      fn = fun [x1; x2] -> [BoolV(x1 > x2)]};
    {name = "<=";
      typ = [IntT; IntT], [BoolT];
      fn = fun [x1; x2] -> [BoolV(x1 <= x2)]};
    {name = ">=";
      typ = [IntT; IntT], [BoolT];
      fn = fun [x1; x2] -> [BoolV(x1 >= x2)]};
    {name = "print";
      typ = [TextT], [];
      fn = fun [TextV t] -> print_string t; []};
    {name = "printInt"; 
      typ = [IntT], [];
      fn = fun [IntV i] -> print_int i; []};
  ]

let fun_of_string name =
  try Some (List.find (fun f -> name = f.name) funs) with Not_found -> None
