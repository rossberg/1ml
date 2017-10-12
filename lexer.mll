(*
 * (c) 2014 Andreas Rossberg
 *)

{
open Parser

type pos = {file : string; line : int; column : int}
type region = {left : pos; right : pos}

let convert_pos pos =
  { Source.file = pos.Lexing.pos_fname;
    Source.line = pos.Lexing.pos_lnum;
    Source.column = pos.Lexing.pos_cnum - pos.Lexing.pos_bol
  }

let region lexbuf =
  let left = convert_pos (Lexing.lexeme_start_p lexbuf) in
  let right = convert_pos (Lexing.lexeme_end_p lexbuf) in 
  {Source.left = left; Source.right = right}

let error lexbuf m = raise (Source.Error (region lexbuf, m))
let error_nest start lexbuf m =
  lexbuf.Lexing.lex_start_p <- start;
  error lexbuf m

let convert_num s =
  let n = ref 0 in
  for i = 0 to String.length s - 1 do
    n := !n*10 + Char.code s.[i] - Char.code '0'
  done;
  !n

let convert_escape = function
  | 'n' -> '\n'
  | 't' -> '\t'
  | '\\' -> '\\'
  | '\'' -> '\''
  | '\"' -> '\"'
  | _ -> assert false

let convert_text s =
  let b = Buffer.create (String.length s) in
  let i = ref 1 in
  while !i < String.length s - 1 do
    Buffer.add_char b
      (if s.[!i] <> '\\' then s.[!i] else (incr i; convert_escape s.[!i]));
    incr i
  done;
  Buffer.contents b
}

let space = [' ''\t']
let digit = ['0'-'9']
let letter = ['a'-'z''A'-'Z']
let symbol = ['+''-''*''/''\\''^''~''=''<''>''!''?''@''#''$''%''&''|'':''`']
let tick = '\''
let escape = ['n''t''\\''\'''\"']
let character = [^'"''\\''\n'] | '\\'escape

let num = digit+
let name = (letter | '_') (letter | digit | '_' | tick)*
let text = '"'character*'"'

rule token = parse
  | "_" { HOLE }
  | "and" { AND }
  | "do" { DO }
  | "else" { ELSE }
  | "fun" { FUN }
  | "if" { IF }
  | "in" { IN }
  | "include" { INCLUDE }
  | "let" { LET }
  | "like" { LIKE }
  | "local" { LOCAL }
  | "or" { OR }
  | "pack" { PACK }
  | "primitive" { PRIMITIVE }
  | "then" { THEN }
  | "type" { TYPE }
  | "unpack" { UNPACK }
  | "with" { WITH }
  | "=" { EQUAL }
  | ":" { COLON }
  | ":>" { SEAL }
  | "->" { ARROW }
  | "=>" { DARROW }
  | "." { DOT }
  | "(" { LPAR }
  | ")" { RPAR }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | "," { COMMA }
  | ";" { SEMI }
  | name as name { NAME name }
  | symbol* as sym { SYM sym }
  | num as num { NUM (convert_num num) }
  | text as text { TEXT (convert_text text) }
  | '"'character*('\n'|eof) { error lexbuf "unclosed text literal" }
  | '"'character*'\\'_
    { error_nest (Lexing.lexeme_end_p lexbuf) lexbuf "illegal escape" }
  | ";;;;"_*eof { EOF }
  | ";;"[^'\n']*eof { EOF }
  | ";;"[^'\n']*'\n' { Lexing.new_line lexbuf; token lexbuf }
  | "(;" { comment (Lexing.lexeme_start_p lexbuf) lexbuf; token lexbuf }
  | space { token lexbuf }
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | eof { EOF }
  | _ { error lexbuf "illegal character" }

and comment start = parse
  | ";)" { () }
  | "(;" { comment (Lexing.lexeme_start_p lexbuf) lexbuf; comment start lexbuf }
  | '\n' { Lexing.new_line lexbuf; comment start lexbuf }
  | eof { error_nest start lexbuf "unclosed comment" }
  | _ { comment start lexbuf }
