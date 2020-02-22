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

type 'a def =
  | VoidD: unit def
  | BoolD: bool def
  | IntD: int def
  | CharD: char def
  | TextD: string def
  | VarD: const def
  | ProdD: 'a def * 'b def -> ('a * 'b) def

let (&) l r = ProdD (l, r)

let rec typs_of: type a. a def -> typ list = function
  | VoidD -> []
  | BoolD -> [BoolT]
  | IntD -> [IntT]
  | CharD -> [CharT]
  | TextD -> [TextT]
  | VarD -> [VarT]
  | ProdD (l, r) -> typs_of l @ typs_of r

let rec inj: type a. a def -> a -> const list -> const list = function
  | VoidD -> fun () vs -> vs
  | BoolD -> fun v vs -> BoolV v :: vs
  | IntD -> fun v vs -> IntV v :: vs
  | CharD -> fun v vs -> CharV v :: vs
  | TextD -> fun v vs -> TextV v :: vs
  | VarD -> fun v vs -> v :: vs
  | ProdD (lD, rD) ->
    let injL = inj lD and injR = inj rD in fun (l, r) vs -> injL l (injR r vs)

let rec prj: type a. a def -> const list -> a * const list = function
  | VoidD -> fun vs -> ((), vs)
  | BoolD -> (function (BoolV v :: vs) -> (v, vs) | _ -> failwith "bool")
  | IntD -> (function (IntV v :: vs) -> (v, vs) | _ -> failwith "int")
  | CharD -> (function (CharV v :: vs) -> (v, vs) | _ -> failwith "char")
  | TextD -> (function (TextV v :: vs) -> (v, vs) | _ -> failwith "text")
  | VarD -> (function (v :: vs) -> (v, vs) | _ -> failwith "var")
  | ProdD (lD, rD) ->
    let prjL = prj lD and prjR = prj rD in
    fun vs -> let (l, vs) = prjL vs in let (r, vs) = prjR vs in ((l, r), vs)

let def name inD outD fn = {
    name = name;
    typ = typs_of inD, typs_of outD;
    fn = let inj = inj outD and prj = prj inD in
         fun vs -> let (v, vs) = prj vs in assert (vs = []); inj (fn v) []
  }

let funs =
  [
    def "==" (VarD & VarD) BoolD (fun (x1, x2) -> x1 = x2);
    def "<>" (VarD & VarD) BoolD (fun (x1, x2) -> x1 <> x2);

    def "true" VoidD BoolD (fun () -> true);
    def "false" VoidD BoolD (fun () -> false);

    def "Int.+" (IntD & IntD) IntD (fun (i1, i2) -> i1 + i2);
    def "Int.-" (IntD & IntD) IntD (fun (i1, i2) -> i1 - i2);
    def "Int.*" (IntD & IntD) IntD (fun (i1, i2) -> i1 * i2);
    def "Int./" (IntD & IntD) IntD (fun (i1, i2) -> i1 / i2);
    def "Int.%" (IntD & IntD) IntD (fun (i1, i2) -> i1 mod i2);

    def "Int.<" (IntD & IntD) BoolD (fun (i1, i2) -> i1 < i2);
    def "Int.>" (IntD & IntD) BoolD (fun (i1, i2) -> i1 > i2);
    def "Int.<=" (IntD & IntD) BoolD (fun (i1, i2) -> i1 <= i2);
    def "Int.>=" (IntD & IntD) BoolD (fun (i1, i2) -> i1 >= i2);

    def "Int.print" IntD VoidD (fun i -> print_int i; flush_all ());

    def "Char.toInt" CharD IntD Char.code;
    def "Char.fromInt" IntD CharD Char.chr;

    def "Char.print" CharD VoidD (fun c -> print_char c; flush_all ());

    def "Text.++" (TextD & TextD) TextD (fun (t1, t2) -> t1 ^ t2);

    def "Text.<" (TextD & TextD) BoolD (fun (i1, i2) -> i1 < i2);
    def "Text.>" (TextD & TextD) BoolD (fun (i1, i2) -> i1 > i2);
    def "Text.<=" (TextD & TextD) BoolD (fun (i1, i2) -> i1 <= i2);
    def "Text.>=" (TextD & TextD) BoolD (fun (i1, i2) -> i1 >= i2);

    def "Text.length" TextD IntD String.length;
    def "Text.sub" (TextD & IntD) CharD (fun (t, i) -> t.[i]);
    def "Text.fromChar" CharD TextD (String.make 1);

    def "Text.print" TextD VoidD (fun t -> print_string t; flush_all ());
  ]

let fun_of_string name =
  try Some (List.find (fun f -> name = f.name) funs) with Not_found -> None
