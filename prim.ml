(*
 * (c) 2014 Andreas Rossberg
 *)

type typ =
  | BoolT
  | IntT
  | CharT
  | TextT
  | VarT

type const =
  | BoolV of bool
  | IntV of int
  | CharV of char
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
  | "char" -> Some CharT
  | "text" -> Some TextT
  | _ -> None

let string_of_typ = function
  | BoolT -> "bool"
  | IntT -> "int"
  | CharT -> "char"
  | TextT -> "text"
  | VarT -> assert false

let typ_of_const = function
  | BoolV _ -> BoolT
  | IntV _ -> IntT
  | CharV _ -> CharT
  | TextV _ -> TextT
  | FunV _ -> assert false

let string_of_const = function
  | BoolV(b) -> string_of_bool b
  | IntV(i) -> string_of_int i
  | CharV(c) -> "'" ^ Char.escaped c ^ "'"
  | TextV(t) -> "\"" ^ String.escaped t ^ "\""
  | FunV(f) -> "(prim " ^ f.name ^ ")"

let is_poly {typ = ts1, ts2} = List.mem VarT ts1 || List.mem VarT ts2

let typs = [BoolT; IntT; CharT; TextT]

let funs =
  [
    {name = "==";
      typ = [VarT; VarT], [BoolT];
      fn = fun [x1; x2] -> [BoolV(x1 = x2)]};
    {name = "<>";
      typ = [VarT; VarT], [BoolT];
      fn = fun [x1; x2] -> [BoolV(x1 <> x2)]};

    {name = "true";
      typ = [], [BoolT];
      fn = fun [] -> [BoolV(true)]};
    {name = "false";
      typ = [], [BoolT];
      fn = fun [] -> [BoolV(false)]};

    {name = "Int.+";
      typ = [IntT; IntT], [IntT];
      fn = fun [IntV i1; IntV i2] -> [IntV(i1 + i2)]};
    {name = "Int.-";
      typ = [IntT; IntT], [IntT];
      fn = fun [IntV i1; IntV i2] -> [IntV(i1 - i2)]};
    {name = "Int.*";
      typ = [IntT; IntT], [IntT];
      fn = fun [IntV i1; IntV i2] -> [IntV(i1 * i2)]};
    {name = "Int./";
      typ = [IntT; IntT], [IntT];
      fn = fun [IntV i1; IntV i2] -> [IntV(i1 / i2)]};
    {name = "Int.%";
      typ = [IntT; IntT], [IntT];
      fn = fun [IntV i1; IntV i2] -> [IntV(i1 mod i2)]};
    {name = "Int.<";
      typ = [IntT; IntT], [BoolT];
      fn = fun [x1; x2] -> [BoolV(x1 < x2)]};
    {name = "Int.>";
      typ = [IntT; IntT], [BoolT];
      fn = fun [x1; x2] -> [BoolV(x1 > x2)]};
    {name = "Int.<=";
      typ = [IntT; IntT], [BoolT];
      fn = fun [x1; x2] -> [BoolV(x1 <= x2)]};
    {name = "Int.>=";
      typ = [IntT; IntT], [BoolT];
      fn = fun [x1; x2] -> [BoolV(x1 >= x2)]};
    {name = "Int.print";
      typ = [IntT], [];
      fn = fun [IntV i] -> print_int i; flush_all (); []};

    {name = "Char.toInt";
      typ = [CharT], [IntT];
      fn = fun [CharV c] -> [IntV(Char.code c)]};
    {name = "Char.fromInt";
      typ = [IntT], [CharT];
      fn = fun [IntV i] -> [CharV(Char.chr i)]};
    {name = "Char.print";
      typ = [CharT], [];
      fn = fun [CharV c] -> print_char c; flush_all (); []};

    {name = "Text.++";
      typ = [TextT; TextT], [TextT];
      fn = fun [TextV t1; TextV t2] -> [TextV(t1 ^ t2)]};
    {name = "Text.<";
      typ = [TextT; TextT], [BoolT];
      fn = fun [x1; x2] -> [BoolV(x1 < x2)]};
    {name = "Text.>";
      typ = [TextT; TextT], [BoolT];
      fn = fun [x1; x2] -> [BoolV(x1 > x2)]};
    {name = "Text.<=";
      typ = [TextT; TextT], [BoolT];
      fn = fun [x1; x2] -> [BoolV(x1 <= x2)]};
    {name = "Text.>=";
      typ = [TextT; TextT], [BoolT];
      fn = fun [x1; x2] -> [BoolV(x1 >= x2)]};
    {name = "Text.length";
      typ = [TextT], [IntT];
      fn = fun [TextV t] -> [IntV(String.length t)]};
    {name = "Text.sub";
      typ = [TextT; IntT], [CharT];
      fn = fun [TextV t; IntV i] -> [CharV(t.[i])]};
    {name = "Text.fromChar";
      typ = [CharT], [TextT];
      fn = fun [CharV c] -> [TextV(String.make 1 c)]};
    {name = "Text.print";
      typ = [TextT], [];
      fn = fun [TextV t] -> print_string t; flush_all (); []};
  ]

let fun_of_string name =
  try Some (List.find (fun f -> name = f.name) funs) with Not_found -> None
