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
%token FUN REC LET LOCAL IN DO WRAP UNWRAP TYPE INCLUDE END
%token IF THEN ELSE OR AND AS
%token EQUAL COLON SEAL ARROW DARROW
%token WITH
%token LPAR RPAR
%token LBRACE RBRACE
%token DOT AT TICK
%token COMMA SEMI

%token EOF

%token<string> NAME
%token<string> SYM
%token<string> TEXT
%token<char> CHAR
%token<int> NUM

%start prog
%type<Syntax.exp> prog

%%

label :
  | name
    { $1 }
  | sym
    { $1 }
  | NUM
    { index($1)@@at() }
;
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
annparam :
  | LPAR head COLON typ RPAR
    { let b, _ = varP($2) in (b, $4, Expl@@ati 3)@@at() }
  | LPAR TYPE head typparamlist RPAR
    { let b, _ = varP($3) in
      (b, funT($4, TypT@@ati 2, Pure@@ati 2)@@span[ati 2; ati 4],
        Expl@@ati 2)@@at() }
  | TICK LPAR head COLON TYPE RPAR
    { let b, _ = varP($3) in (b, TypT@@ati 5, Impl@@ati 1)@@at() }
  | TICK LPAR TYPE head RPAR
    { let b, _ = varP($4) in (b, TypT@@ati 3, Impl@@ati 1)@@at() }
  | TICK head
    { let b, _ = varP($2) in (b, TypT@@at(), Impl@@ati 1)@@at() }
;
param :
  | atpat
    { let b, t = (defaultP $1).it in (b, t, Expl@@at())@@at() }
  | TICK LPAR head COLON TYPE RPAR
    { let b, _ = varP($3) in (b, TypT@@ati 5, Impl@@ati 1)@@at() }
  | TICK LPAR TYPE head RPAR
    { let b, _ = varP($4) in (b, TypT@@ati 3, Impl@@ati 1)@@at() }
  | TICK head
    { let b, _ = varP($2) in (b, TypT@@at(), Impl@@ati 1)@@at() }
;
paramlist :
  |
    { [] }
  | param paramlist
    { $1::$2 }
;
typparamlist :
  | paramlist
    { List.map (fun p ->
        match p.it with
        | (b, {it = HoleT; at}, i) -> (b, TypT@@at, i)@@p.at
        | _ -> p
      ) $1 }
;
arrow :
  | ARROW
    { Impure@@at() }
  | DARROW
    { Pure@@at() }
;

attyp :
  | PRIMITIVE TEXT
    { PrimT($2)@@at() }
  | TYPE
    { TypT@@at() }
  | HOLE
    { HoleT@@at() }
  | LBRACE dec RBRACE
    { StrT($2)@@at() }
  | LPAR RPAR
    { StrT(EmptyD@@at())@@at() }
  | LPAR typlist RPAR
    { match $2 with [t] -> t | ts -> tupT(ts)@@at() }
  | LPAR EQUAL exp RPAR
    { EqT($3)@@at() }
;
apptyp :
  | attyp
    { $1 }
  | pathexp
    { PathT($1)@@at() }
;
withtyp :
  | apptyp
    { $1 }
  | withtyp WITH LPAR namelist typparamlist EQUAL exp RPAR
    { WithT($1, $4, funE($5, $7)@@span[ati 5; ati 7])@@at() }
  | withtyp WITH LPAR TYPE namelist typparamlist EQUAL typ RPAR
    { WithT($1, $5, funE($6, TypE($8)@@ati 8)@@span[ati 6; ati 8])@@at() }
;
typ :
  | withtyp
    { $1 }
  | annparam arrow typ
    { funT([$1], $3, $2)@@at() }
  | withtyp arrow typ
    { let b, _ = varP("_"@@ati 1) in
      funT([(b, $1, Expl@@ati 2)@@ati 1], $3, $2)@@at() }
  | WRAP typ
    { WrapT($2)@@at() }
  | REC atpat DARROW typ
    { recT(defaultTP $2, $4)@@at() }
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
  | head typparamlist COLON typ
    { VarD($1, funT($2, $4, Pure@@ati 2)@@span[ati 2; ati 4])@@at() }
  | TYPE head typparamlist
    { VarD($2, funT($3, TypT@@ati 1, Pure@@ati 3)@@at())@@at() }
  | head typparamlist EQUAL exp
    { VarD($1, funT($2, EqT($4)@@ati 4, Pure@@ati 3)@@span[ati 2; ati 4])
        @@at() }
  | TYPE head typparamlist EQUAL typ
    { VarD($2, funT($3, EqT(TypE($5)@@ati 5)@@ati 5, Pure@@ati 4)@@at())
        @@at() }
  | INCLUDE typ
    { InclD($2)@@at() }
  | LOCAL bind IN dec END
    { letD($2, $4)@@at() }
/*
  | LPAR dec RPAR
    { $2 }
*/
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
  | HOLE
    { TypE(HoleT@@at())@@at() }
;
apppathexp :
  | atpathexp
    { $1 }
  | apppathexp atexp
    { appE($1, $2)@@at() }
  | apppathexp DOT label
    { DotE($1, $3)@@at() }
  | AT attyp atexp
    { rollE($3, $2)@@at() }
  | AT name atexp
    { rollE($3, PathT(VarE($2)@@ati 2)@@ati 2)@@at() }
  | apppathexp DOT AT attyp
    { unrollE($1, $4)@@at() }
  | apppathexp DOT AT name
    { unrollE($1, PathT(VarE($4)@@ati 4)@@ati 4)@@at() }
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
  | HOLE
    { TypE(HoleT@@at())@@at() }
  | PRIMITIVE TEXT
    { match Prim.fun_of_string $2 with
      | Some f -> PrimE(Prim.FunV f)@@at()
      | None -> parse_error ("unknown primitive \"" ^ $2 ^ "\"") }
  | NUM
    { PrimE(Prim.IntV($1))@@at() }
  | CHAR
    { PrimE(Prim.CharV($1))@@at() }
  | TEXT
    { PrimE(Prim.TextV($1))@@at() }
  | LBRACE bind RBRACE
    { StrE($2)@@at() }
  | LPAR RPAR
    { StrE(EmptyB@@at())@@at() }
  | LPAR explist RPAR
    { match $2 with [e] -> e | es -> tupE(es)@@at() }
  | LPAR expsemilist RPAR
    { seqE($2)@@at() }
  | LPAR DOT label RPAR
    { dotopE($3)@@at() }
;
appexp :
  | atexp
    { $1 }
  | appexp atexp
    { appE($1, $2)@@at() }
  | appexp DOT label
    { DotE($1, $3)@@at() }
  | AT attyp atexp
    { rollE($3, $2)@@at() }
  | AT name atexp
    { rollE($3, PathT(VarE($2)@@ati 2)@@ati 2)@@at() }
  | appexp DOT AT attyp
    { unrollE($1, $4)@@at() }
  | appexp DOT AT name
    { unrollE($1, PathT(VarE($4)@@ati 4)@@ati 4)@@at() }
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
  | DO appexp
    { doE($2)@@at() }
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
  | WRAP infexp COLON typ
    { wrapE($2, $4)@@at() }
  | UNWRAP infexp COLON typ
    { unwrapE($2, $4)@@at() }
;
exp :
  | annexp
    { $1 }
  | FUN param paramlist DARROW exp
    { funE($2::$3, $5)@@at() }
  | IF exp THEN exp ELSE infexp COLON typ
    { ifE($2, $4, $6, $8)@@at() }
  | IF exp THEN exp ELSE infexp
    { ifE($2, $4, $6, HoleT@@ati 1)@@at() }
  | LET bind IN exp
    { letE($2, $4)@@at() }
  | REC atpat DARROW exp
    { recE(defaultP $2, $4)@@at() }
;
explist :
  | exp
    { $1::[] }
  | exp COMMA explist
    { $1::$3 }
;
expsemilist :
  | exp SEMI
    { $1::[] }
  | exp SEMI exp
    { $1::$3::[] }
  | exp SEMI expsemilist
    { $1::$3 }
;

atbind :
  | head param paramlist EQUAL exp
    { VarB($1, funE($2::$3, $5)@@span[ati 2; ati 5])@@at() }
  | head param paramlist COLON typ EQUAL exp
    { VarB($1, funE($2::$3, annotE($7, $5)@@span[ati 5; ati 7])
        @@span[ati 2; ati 7])@@at() }
  | head paramlist SEAL typ EQUAL exp
    { VarB($1, funE($2, sealE($6, $4)@@span[ati 4; ati 6])
        @@span[ati 2; ati 6])@@at() }
  | pat EQUAL exp
    { patB($1, $3)@@at() }
  | name
    { VarB($1, VarE($1.it@@at())@@at())@@at() }
  | TYPE head typparamlist EQUAL typ
    { VarB($2, funE($3, TypE($5)@@ati 5)@@span[ati 3; ati 5])@@at() }
  | INCLUDE exp
    { InclB($2)@@at() }
  | LOCAL bind IN bind END
    { letB($2, $4)@@at() }
  | DO exp
    { doB($2)@@at() }
/*
  | LPAR bind RPAR
    { $2 }
*/
;
bind :
  |
    { EmptyB@@at() }
  | atbind
    { $1 }
  | atbind SEMI bind
    { SeqB($1, $3)@@at() }
;

atpat :
  | head
    { if $1.it = "_" then holeP@@at() else varP($1)@@at() }
  | LBRACE decon RBRACE
    { strP($2)@@at() }
  | LPAR RPAR
    { strP([])@@at() }
  | LPAR patlist RPAR
    { match $2 with [p] -> p | ps -> tupP(ps)@@at() }
  | LPAR TYPE name typparamlist RPAR
    { annotP(varP($3.it@@ati 3)@@ati 3,
        funT($4, TypT@@ati 2, Pure@@ati 2)@@at())@@at() }
;
apppat :
  | atpat
    { $1 }
  | AT attyp atpat
    { rollP($3, $2)@@at() }
  | AT name atpat
    { rollP($3, PathT(VarE($2)@@ati 2)@@ati 2)@@at() }
;
annpat :
  | apppat
    { $1 }
  | annpat COLON typ
    { annotP($1, $3)@@at() }
  | WRAP apppat COLON typ
    { wrapP($2, $4)@@at() }
;
pat :
  | annpat
    { $1 }
  | annpat AS annpat
    { asP($1, $3)@@at() }
;
patlist :
  | pat
    { $1::[] }
  | pat COMMA patlist
    { $1::$3 }
;

atdecon :
  | name EQUAL pat
    { [($1, $3)@@at()] }
  | name
    { [($1, varP($1.it@@at())@@at())@@at()] }
  | name COLON typ EQUAL pat
    { [($1, annotP($5, $3)@@span[ati 2; ati 5])@@at()] }
  | name COLON typ
    { [($1, annotP(varP($1.it@@ati 1)@@ati 1, $3)@@at())@@at()] }
  | TYPE name typparamlist
    { [($2, annotP(varP($2.it@@ati 2)@@ati 2,
        funT($3, TypT@@ati 1, Pure@@ati 1)@@at())@@at())@@at()] }
/*
  | LPAR decon RPAR
    { $2 }
*/
;
decon :
  |
    { [] }
  | atdecon
    { $1 }
  | atdecon SEMI decon
    { $1 @ $3 }
;

prog :
  | bind EOF
    { StrE($1)@@at() }
;

%%
  