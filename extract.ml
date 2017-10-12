(*
 * (c) 2014 Andreas Rossberg
 *)

open Fomega

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
  | FunT of var * kind * typ
  | AppT of typ * typ
  | StrT of typ row
  | DotT of typ * lab
  | RecT of var * kind * typ
  | InferT of typ lazy_t * int

let rec print_typ' prec = function
  | VarT(a, k, n) ->
    let s = string_of_var a n in
    if k <> BaseK && !verbose_vars_flag then
      print_paren base_prec prec (fun () ->
        print_string s;
        print_string ":";
        print_break 0 2;
        print_kind' base_prec ctxt k
      )
    else
      print_string s
  | PrimT(t) ->
    print_string (Prim.string_of_typ t)
  | StrT(tr) ->
    (match as_tup_row tr with
    | Some ts ->
      print_brack "(" ")" (fun () ->
        print_list' print_typ' base_prec ctxt ts;
      )
    | None ->
      print_brack "{" "}" (fun () ->
        print_row' ":" print_typ' base_prec ctxt tr;
      )
    )
  | FunT(a, k, t, s, p) ->
    print_binder prec "!" a k (fun () ->
      open_box 0;
      print_typ' (binder_prec + 1) ([a]::ctxt) t;
      close_box ();
      print_string " ";
      print_string
        (match p with Impure -> "->" | Pure -> "=>" | Implicit -> "'=>");
      print_break 1 2;
      open_box 0;
      print_extyp' binder_prec (enter "()" ctxt) s;
      close_box ()
    )
  | TypT(s) ->
    print_brack "[= " "]" (fun () -> print_extyp' base_prec ctxt s);
  | PackT(s) ->
    print_brack "[" "]" (fun () -> print_extyp' base_prec ctxt s);
  | ProdT(tr) ->
    print_brack "{" "}" (fun () ->
      print_row' "=" print_typ' base_prec ctxt tr;
    )
  | LamT(a, k, t) ->
    print_binder prec "\\" a k (fun () ->
      print_typ' binder_prec ctxt t
    )
  | DotT(t, l) ->
    if String.contains l '$' then
      print_typ' prec ctxt t
    else if matches_ctxt t ctxt then
      print_string l
    else
      print_paren dot_prec prec (fun () ->
        print_typ' dot_prec ctxt t;
        print_string ".";
        print_string l
      )
  | AppT(t1, t2) ->
    print_paren app_prec prec (fun () ->
      print_typ' app_prec ctxt t1;
      print_string "(";
      print_break 0 2;
      print_typ' base_prec ctxt t2;
      print_string ")"
    )
  | RecT(a, k, t) ->
    print_binder prec "@" a k (fun () ->
      print_typ' binder_prec ctxt t
    )
  | InferT(z) ->
    match !z with
    | Det t -> print_typ' prec ctxt t
    | Undet u -> print_string (string_of_var ("'" ^ string_of_int u.id) u.level)

let rec print_exp' prec = function
  | VarE(x) -> print_var x
  | PrimE(c) -> print_const c
  | IfE(e1, e2, e3) ->
    print_paren pre_prec prec (fun () ->
      open_box 0;
      print_string "if ";
      print_exp' prec e1;
      print_break 1 0;
      print_string "then ";
      print_exp' base_prec e2;
      print_break 1 0;
      print_string "then ";
      print_exp' pre_prec e3;
      close_box ()
    )
  | FunE(x, t, e) ->
    print_paren pre_prec prec (fun () ->
      open_box 0;
      print_string "fun (";
      print_var x;
      print_string " : ";
      print_typ' base_prec t;
      print_string ")";
      print_break 1 0;
      print_string "-> ";
      print_exp' pre_prec e;
      close_box ()
    )
  | AppE(e1, e2) ->
    print_paren app_prec prec (fun () ->
      open_box 0;
      print_exp' app_prec e1;
      print_break 1 0;
      print_exp' (app_prec + 1) e2;
      close_box ()
    )
  | StrE(er) ->
    print_paren tup_prec prec (fun () ->
      print_list' print_exp' (tup_prec + 1) (List.map snd er)
    )
  | DotE(e, l) ->
    print_paren pre_prec prec (fun () ->
      open_box 0;
      print_string "let ";
      print_list' print_exp' tup_prec (List.map snd er)
 (* TODO *)
      print_string " =";
      print_break 1 2;
      open_box 0;
      print_exp' base_prec e;
      close_box ();
      print_break 1 0;
      print_string "in";
      print_break 1 0;
      print_var l;
      close_box ()
    )
  | GenE(a, k, e) ->
    print_brack "(" ")" (fun () ->
      open_box 0;
      print_string "module ";
      close_box ()
    )
  | InstE of exp * typ
  | PackE(t1, e, t2) ->
    
  | OpenE of exp * var * var * exp
  | RollE of exp * typ
  | UnrollE of exp
  | RecE of var * typ * exp
  | LetE of exp * var * exp
