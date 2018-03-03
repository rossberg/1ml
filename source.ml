(*
 * (c) 2014 Andreas Rossberg
 *)

type pos = {file : string; line : int; column : int}
type region = {left : pos; right : pos}

type ('a, 'b) phrase =
  { at : region;
    it : 'a;
    mutable sem : 'b option
  }

exception Error of region * string


(* Positions and regions *)

let nowhere_pos = {file = ""; line = 0; column = 0}
let nowhere_region = {left = nowhere_pos; right = nowhere_pos}

let string_of_pos pos =
  string_of_int pos.line ^ "." ^ string_of_int (pos.column + 1)
let string_of_region r =
  r.left.file ^ ":" ^ string_of_pos r.left ^ "-" ^ string_of_pos r.right

let before region = {left = region.left; right = region.left}
let after region = {left = region.right; right = region.right}

let rec span regions = match regions with
  | [] -> raise (Failure "span")
  | r::rs -> span' r.left r.right rs
and span' left right regions = match regions with
  | [] -> {left = left; right = right}
  | r::rs -> span' (min left r.left) (max right r.right) rs


(* Phrases *)

let (@@) phrase' region = {at = region; it = phrase'; sem = None}
let (@@@) phrase' regions = phrase'@@(span regions)
let (<~) phrase sem = assert (phrase.sem = None); phrase.sem <- Some sem; sem
let dup phrase = phrase.it@@phrase.at

let at phrase = phrase.at
let it phrase = phrase.it
let sem phrase = match phrase.sem with
  | Some x -> x
  | _ -> raise (Invalid_argument "sem")


(* Errors *)

let warn at m = prerr_endline (string_of_region at ^ ": warning: " ^ m)

let error at m = raise (Error (at, m))

let rec count_newlines i s =
  if i == String.length s then 0
  else (if s.[i] == '\n' then 1 else 0) + count_newlines (i + 1) s

let indent s =
  let s' = Bytes.make (String.length s + 2 * count_newlines 0 s + 2) ' ' in
  let i = ref 0 in
  let i' = ref 2 in
  while !i < String.length s do
    let j =
      try String.index_from s !i '\n' + 1 with Not_found -> String.length s in
    Bytes.blit_string s !i s' !i' (j - !i);
    i' := !i' + (j - !i) + 2;
    i := j
  done;
  Bytes.to_string s'
