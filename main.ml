(*
 * (c) 2014 Andreas Rossberg
 *)

let name = "1ML"
let version = "0.2"

let interactive_flag = ref false
let trace_flag = ref false
let ast_flag = ref false
let result_flag = ref false
let no_run_flag = ref false
let run_f_flag = ref false

let trace_phase name = if !trace_flag then print_endline ("-- " ^ name)

let load file =
  let f = open_in file in
  let size = in_channel_length f in
  let source = really_input_string f size in
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

let env = ref Env.empty
let state = ref Lambda.Env.empty
let f_state = ref []

let print_sig s =
  match s with
  | Types.ExT(aks, Types.StrT(tr)) ->
    List.iter (fun (a, k) ->
      Format.open_box 0;
      Format.print_string ("? " ^ a ^ " : ");
      Types.print_kind k;
      Format.print_break 1 0;
      Format.close_box ()
    ) aks;
    Types.print_row tr;
    print_endline ""
  | _ ->
    Types.print_extyp s;
    print_endline ""

let process file source =
  try
    trace_phase "Parsing...";
    let prog = parse file source in
    if !ast_flag then begin
      print_endline (Syntax.string_of_exp prog)
    end;
    trace_phase "Elaborating...";
    let sign, _, fprog = Elab.elab !env prog in
    if !Elab.verify_flag then begin
      trace_phase "Checking...";
      Fomega.check_exp
        (Erase.erase_env !env) fprog (Erase.erase_extyp sign) "Prog"
    end;
    let Types.ExT(aks, typ) = sign in
    let typrow = match typ with Types.StrT(row) -> row | _ -> [] in
    if !no_run_flag then
      print_sig sign
    else begin
      if !run_f_flag then begin
        trace_phase "Running...";
        let closed_prog =
          List.fold_right (fun (x, t, e1) e2 -> Fomega.LetE(e1, x, e2))
            !f_state fprog in
        let result = Fomega.norm_exp closed_prog in
        trace_phase "Result:";
        if !result_flag then begin
          print_string (Fomega.string_of_exp result);
          print_string " : ";
          print_endline (Types.string_of_norm_extyp sign)
        end else begin
          print_sig sign
        end;
        let rec unpack = function
          | Fomega.PackE(_, v, _) -> unpack v
          | Fomega.TupE(vr) -> vr
          | _ -> assert false
        in
        let f_state' = List.map2 (fun (x, t) (x', v) ->
            assert (x = x'); x, Erase.erase_typ t, v
          ) typrow (unpack result)
        in f_state := !f_state @ f_state'
      end else begin
        trace_phase "Compiling...";
        let lambda = Compile.compile (Erase.erase_env !env) fprog in
        trace_phase "Running...";
        let value = Lambda.eval !state lambda in
        trace_phase "Result:";
        if !result_flag then begin
          print_string (Lambda.string_of_value value);
          print_string " : ";
          print_endline (Types.string_of_norm_extyp sign)
        end else begin
          print_sig sign
        end;
        let ls = match sign with
          | Types.ExT(_, Types.StrT(tr)) -> List.sort compare (List.map fst tr)
          | _ -> assert false
        in
        let vs = match value with
          | Lambda.TupV(vs) -> vs
          | _ -> assert false
        in
        state := List.fold_right2 Lambda.Env.add ls vs !state
      end
    end;
    env := Env.add_row typrow (Env.add_typs aks !env)
  with Source.Error (at, s) ->
    trace_phase "Error:";
    prerr_endline (Source.string_of_region at ^ ": " ^ s);
    if not !interactive_flag then exit 1

let process_file file =
  trace_phase ("Loading (" ^ file ^ ")...");
  let source = load file in
  process file source

let rec process_stdin () =
  print_string (name ^ "> "); flush_all ();
  match try Some (input_line stdin) with End_of_file -> None with
  | None -> print_endline ""; trace_phase "Bye."
  | Some source -> process "stdin" source; process_stdin ()

let greet () =
  print_endline ("Version " ^ version)

let usage = "Usage: " ^ name ^ " [option] [file ...]"
let argspec = Arg.align
[
  "-", Arg.Set interactive_flag,
    " run interactively (default if no files given)";
  "-c", Arg.Set Elab.verify_flag, " check target program";
  "-d", Arg.Set no_run_flag, " dry, do not run program";
  "-f", Arg.Set run_f_flag, " run program as System F reduction";
  "-p", Arg.Set ast_flag, " show parse tree";
  "-r", Arg.Set result_flag, " show resulting term";
  "-t", Arg.Set trace_flag, " trace compiler phases";
  "-v", Arg.Unit greet, " show version";
  "-tb", Arg.Set Trace.bind_flag, " trace bindings";
  "-te", Arg.Set Trace.elab_flag, " trace elaboration";
  "-ts", Arg.Set Trace.sub_flag, " trace subtyping";
  "-td", Arg.Set Trace.debug_flag, " debug output";
  "-vt", Arg.Unit Types.verbosest_on, " verbose types";
  "-ut", Arg.Set Types.undecidable_flag, " allow undecidable subtyping"
]

let () =
  Printexc.record_backtrace true;
  try
    let files = ref [] in
    Arg.parse argspec (fun file -> files := !files @ [file]) usage;
    if !files = [] then interactive_flag := true;
    List.iter process_file !files;
    if !interactive_flag then process_stdin ()
  with exn ->
    flush stdout;
    prerr_endline
      (Sys.argv.(0) ^ ": uncaught exception " ^ Printexc.to_string exn);
    Printexc.print_backtrace stderr;
    exit 2
