(*
 * (c) 2014 Andreas Rossberg
 *)

let name = "1ml"

let trace_flag = ref false
let dump_flag = ref false
let check_flag = ref false
let no_run_flag = ref true

let trace_phase name = if !trace_flag then print_endline ("-- " ^ name)

let load file =
  let f = open_in file in
  let size = in_channel_length f in
  let source = String.create size in
  really_input f source 0 size;
  close_in f;
  source

let parse name source =
  let lexbuf = Lexing.from_string source in
  lexbuf.Lexing.lex_curr_p <-
    {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = name};
  try Parser.prog Lexer.token lexbuf with Source.Error (region, s) ->
    let region' = if region <> Source.nowhere_region then region else
      {Source.left = Lexer.convert_pos lexbuf.Lexing.lex_start_p;
       Source.right = Lexer.convert_pos lexbuf.Lexing.lex_curr_p} in
    raise (Source.Error (region', s))

let env = ref []
let state = ref []
let types = ref []

let print_sig s =
  match s with
  | Types.ExT(a, k, Types.StrT(tr)) ->
    if k <> Types.ProdK[] then (
      print_endline ("?" ^ a ^ " : " ^ Types.string_of_kind k)
    );
    List.iter (fun (l, t) ->
      print_endline (l ^ " : " ^ Types.string_of_norm_typ t)
    ) tr
  | _ ->
    print_endline (Types.string_of_norm_extyp s)

let process file source =
  try
    trace_phase "Parsing...";
    let prog = parse file source in
    trace_phase "Elaborating...";
    let sign, _, prog' = Elab.elab !env prog in
    if !check_flag then begin
      trace_phase "Checking...";
      let f_env =
        List.fold_right (fun (a, k) e ->
          Fomega.add_typ a (Elab.erase_kind k) e
        ) !types
          (List.fold_right (fun (x, t) e ->
            Fomega.add_val x (Elab.erase_typ t) e
          ) !env Fomega.empty)
      in Fomega.check_exp f_env prog' (Elab.erase_extyp sign) "Prog"
    end;
    let Types.ExT(a, k, typ) = sign in
    if a <> "_" then types := (a, k) :: !types;
    let env' = match typ with Types.StrT(tr) -> tr | _ -> [] in
    env := env' @ !env;
    if !no_run_flag then
      print_sig sign
    else begin
      trace_phase "Running...";
      let result = Fomega.norm_exp (Fomega.letE(!state, prog')) in
      trace_phase "Result:";
      print_string (Fomega.string_of_exp result);
      print_string " : ";
      print_endline (Types.string_of_norm_extyp sign);
      let str = match result with Fomega.PackE(_, v, _) -> v | v -> v in
      let row = match str with Fomega.StrE(vr) -> vr | _ -> [] in
      let state' = List.map2 (fun (x, t) (x', v) ->
          assert (x = x'); x, Elab.erase_typ t, v
        ) env' row
      in state := !state @ state'
    end
  with Source.Error (at, s) ->
    trace_phase "Error:";
    prerr_endline (Source.string_of_region at ^ ": " ^ s)

let num_files = ref 0
let process_file file =
  trace_phase ("Loading (" ^ file ^ ")...");
  let source = load file in
  process file source;
  incr num_files

let rec process_stdin () =
  print_string (name ^ "> "); flush_all ();
  match try Some (input_line stdin) with End_of_file -> None with
  | None -> print_endline ""; trace_phase "Bye."
  | Some source -> process "stdin" source; process_stdin ()


let usage = "Usage: " ^ name ^ " [option] [file]"
let argspec = Arg.align
[
  "-c", Arg.Set check_flag, " check target program";
  "-r", Arg.Set no_run_flag, " do not run program";
  "-d", Arg.Set dump_flag, " dump types";
  "-v", Arg.Set trace_flag, " verbose output";
]

let () =
  Printexc.record_backtrace true;
  try
    Arg.parse argspec process_file usage;
    if !num_files = 0 then process_stdin ()
  with exn ->
    flush stdout;
    prerr_endline
      (Sys.argv.(0) ^ ": uncaught exception " ^ Printexc.to_string exn);
    Printexc.print_backtrace stderr;
    exit 2
