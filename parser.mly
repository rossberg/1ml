/*
 * (c) 2014 Andreas Rossberg
 */

%{
open Source
open Syntax

let position_to_pos position =
  { file = position.Lexing.pos_fname;
    line = position.Lexing.pos_lnum;
    column = position.Lexing.pos_cnum - position.Lexing.pos_bol
  }

let positions_to_region position1 position2 =
  { left = position_to_pos position1;
    right = position_to_pos position2
  }

let at () =
  positions_to_region (Parsing.symbol_start_pos ()) (Parsing.symbol_end_pos ())
let ati i =
  positions_to_region (Parsing.rhs_start_pos i) (Parsing.rhs_end_pos i)

let parse_error s = raise (Source.Error (Source.nowhere_region, s))
%}

%token TRUE FALSE HOLE PRIMITIVE
%token FUN LET LOCAL IN DO PACK UNPACK TYPE LIKE INCLUDE
%token IF THEN ELSE OR AND
%token EQUAL COLON SEAL ARROW DARROW
%token WITH
%token LPAR RPAR
%token LBRACE RBRACE
%token DOT
%token COMMA SEMI

%token EOF

%token<string> NAME
%token<string> SYM
%token<string> TEXT
%token<int> NUM

%start prog
%type<Syntax.exp> prog

%%

sym :
  | SYM
    { $1@@at() }
;
name :
  | NAME
    { $1@@at() }
  | LPAR sym RPAR
    { $2 }
;
namelist :
  | name
    { $1::[] }
  | name DOT namelist
    { $1::$3 }
;

head :
  | name
    { $1 }
  | HOLE
    { "_"@@at() }
;
typparam :
  | LPAR head COLON typ RPAR
    { ($2, $4)@@at() }
  | LPAR TYPE head RPAR
    { ($3, TypT@@ati 2)@@at() }
;
param :
  | typparam
    { $1 }
  | head
    { ($1, TypT@@at())@@at() }
;
paramlist :
  |
    { [] }
  | param paramlist
    { $1::$2 }
;
arrow :
  | ARROW
    { Impure@@at() }
  | DARROW
    { Pure@@at() }
;

attyp :
  | pathexp
    { PathT($1)@@at() }
  | PRIMITIVE TEXT
    { PrimT($2)@@at() }
  | TYPE
    { TypT@@at() }
  | LBRACE dec RBRACE
    { StrT($2)@@at() }
  | LPAR RPAR
    { StrT(EmptyD@@at())@@at() }
  | LPAR typlist RPAR
    { match $2 with [t] -> t | ts -> tupT(ts)@@at() }
;
apptyp :
  | attyp
    { $1 }
;
withtyp :
  | apptyp
    { $1 }
  | withtyp WITH namelist paramlist EQUAL pathexp
    { WithT($1, $3, funE($4, $6)@@span[ati 4; ati 6])@@at() }
  | withtyp WITH TYPE namelist paramlist EQUAL apptyp
    { WithT($1, $4, funE($5, TypE($7)@@ati 7)@@span[ati 5; ati 7])@@at() }
;
typ :
  | withtyp
    { $1 }
  | typparam arrow typ
    { funT([$1], $3, $2)@@at() }
  | withtyp arrow typ
    { funT([("_"@@ati 1, $1)@@ati 1], $3, $2)@@at() }
  | PACK typ
    { PackT($2)@@at() }
  | LIKE pathexp
    { LikeT($2)@@at() }
  | LET bind IN typ
    { letT($2, $4)@@at() }
;
typlist :
  | typ
    { $1::[] }
  | typ COMMA typlist
    { $1::$3 }
;

atdec :
  | head paramlist COLON typ
    { VarD($1, funT($2, $4, Pure@@ati 2)@@span[ati 2; ati 4])@@at() }
  | TYPE head paramlist
    { VarD($2, funT($3, TypT@@ati 1, Pure@@ati 3)@@at())@@at() }
  | head paramlist EQUAL exp
    { VarD($1, funT($2, LikeT($4)@@ati 4, Pure@@ati 3)@@span[ati 2; ati 4])
        @@at() }
  | TYPE head paramlist EQUAL typ
    { VarD($2, funT($3, LikeT(TypE($5)@@ati 5)@@ati 5, Pure@@ati 4)@@at())
        @@at() }
  | INCLUDE typ
    { InclD($2)@@at() }
  | LOCAL bind IN atdec
    { letD($2, $4)@@at() }
  | LPAR dec RPAR
    { $2 }
;
dec :
  |
    { EmptyD@@at() }
  | atdec
    { $1 }
  | atdec SEMI dec
    { SeqD($1, $3)@@at() }
;

atpathexp :
  | name
    { VarE($1)@@at() }
;
apppathexp :
  | atpathexp
    { $1 }
  | apppathexp atexp
    { appE($1, $2)@@at() }
  | apppathexp DOT name
    { DotE($1, $3)@@at() }
  | apppathexp DOT NUM
    { DotE($1, ("_" ^ string_of_int $3)@@ati(3))@@at() }
;
infpathexp :
  | apppathexp
    { $1 }
  | sym apppathexp
    { appE(VarE($1)@@ati(1), $2)@@at() }
  | infpathexp sym apppathexp
    { appE(VarE($2)@@ati(2), tupE[$1; $3]@@at())@@at() }
;
pathexp :
  | infpathexp
    { $1 }
;

atexp :
  | name
    { VarE($1)@@at() }
  | PRIMITIVE TEXT
    { match Prim.fun_of_string $2 with
      | Some f -> PrimE(Prim.FunV f)@@at()
      | None -> parse_error ("unknown primitive \"" ^ $2 ^ "\"") }
  | NUM
    { PrimE(Prim.IntV($1))@@at() }
  | TEXT
    { PrimE(Prim.TextV($1))@@at() }
  | LBRACE bind RBRACE
    { StrE($2)@@at() }
  | LPAR RPAR
    { StrE(EmptyB@@at())@@at() }
  | LPAR explist RPAR
    { match $2 with [e] -> e | es -> tupE(es)@@at() }
;
appexp :
  | atexp
    { $1 }
  | appexp atexp
    { appE($1, $2)@@at() }
  | appexp DOT name
    { DotE($1, $3)@@at() }
  | appexp DOT NUM
    { DotE($1, ("_" ^ string_of_int $3)@@ati(3))@@at() }
;
infexp :
  | appexp
    { $1 }
  | sym appexp
    { appE(VarE($1)@@ati(1), $2)@@at() }
  | infexp sym appexp
    { appE(VarE($2)@@ati(2), tupE[$1; $3]@@at())@@at() }
  | infexp OR appexp
    { orE($1, $3)@@at() }
  | infexp AND appexp
    { andE($1, $3)@@at() }
;
annexp :
  | infexp
    { $1 }
  | TYPE typ
    { TypE($2)@@at() }
  | annexp COLON typ
    { annotE($1, $3)@@at() }
  | annexp SEAL typ
    { sealE($1, $3)@@at() }
  | PACK infexp COLON typ
    { packE($2, $4)@@at() }
  | UNPACK infexp COLON typ
    { unpackE($2, $4)@@at() }
;
exp :
  | annexp
    { $1 }
  | FUN param paramlist DARROW exp
    { funE($2::$3, $5)@@at() }
  | IF exp THEN exp ELSE infexp COLON typ
    { ifE($2, $4, $6, $8)@@at() }
  | LET bind IN exp
    { letE($2, $4)@@at() }
  | DO exp
    { doE($2)@@at() }
;
explist :
  | exp
    { $1::[] }
  | exp COMMA explist
    { $1::$3 }
;

atbind :
  | head paramlist EQUAL exp
    { VarB($1, funE($2, $4)@@span[ati 2; ati 4])@@at() }
  | head paramlist COLON typ EQUAL exp
    { VarB($1, funE($2, annotE($6, $4)@@span[ati 4; ati 6])
        @@span[ati 2; ati 6])@@at() }
  | head paramlist SEAL typ EQUAL exp
    { VarB($1, funE($2, sealE($6, $4)@@span[ati 4; ati 6])
        @@span[ati 2; ati 6])@@at() }
  | TYPE head paramlist EQUAL typ
    { VarB($2, funE($3, TypE($5)@@ati 5)@@span[ati 3; ati 5])@@at() }
  | INCLUDE exp
    { InclB($2)@@at() }
  | LOCAL bind IN atbind
    { letB($2, $4)@@at() }
  | DO exp
    { doB($2)@@at() }
  | LPAR bind RPAR
    { $2 }
;
bind :
  |
    { EmptyB@@at() }
  | atbind
    { $1 }
  | atbind SEMI bind
    { SeqB($1, $3)@@at() }
;

prog :
  | bind EOF
    { StrE($1)@@at() }
;

%%
  