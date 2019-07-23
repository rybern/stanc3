(** stanc console application *)

open Core_kernel
open Frontend
open Stan_math_backend
open Analysis_and_optimization.Factor_graph

(** The main program. *)
let version = "stanc version 3.0 alpha"

let name = "stanc"

(** The usage message. *)
let usage = "Usage: " ^ name ^ " [option] ... <model_file.stan>"

let model_file = ref ""
let pretty_print_program = ref false
let print_model_cpp = ref false
let dump_mir = ref false
let dump_dot = ref false
let output_file = ref ""
let generate_data = ref false

(** Some example command-line options here *)
let options =
  Arg.align
    [ ( "--debug-lex"
      , Arg.Set Debugging.lexer_logging
      , " For debugging purposes: print the lexer actions" )
    ; ( "--debug-parse"
      , Arg.Set Debugging.grammar_logging
      , " For debugging purposes: print the parser actions" )
    ; ( "--debug-ast"
      , Arg.Set Debugging.ast_printing
      , " For debugging purposes: print the undecorated AST, before semantic \
         checking" )
    ; ( "--debug-decorated-ast"
      , Arg.Set Debugging.typed_ast_printing
      , " For debugging purposes: print the decorated AST, after semantic \
         checking" )
    ; ( "--debug-generate-data"
      , Arg.Set generate_data
      , " For debugging purposes: generate a mock dataset to run the model on"
      )
    ; ( "--debug-mir"
      , Arg.Set dump_mir
      , " For debugging purposes: print the MIR." )
    ; ( "--print-dot"
      , Arg.Set dump_dot
      , " To demo dependency analysis, print a graphviz dot file of the factor graph. To generate a .png of the graph, pipe this output to a .dot file and use \"dot -Tpng FILE.dot -o outfile.png\"." )
    ; ( "--auto-format"
      , Arg.Set pretty_print_program
      , " Pretty prints the program to the console" )
    ; ( "--version"
      , Arg.Unit
          (fun _ ->
            print_endline (version ^ " " ^ "(" ^ Sys.os_type ^ ")") ;
            exit 1)
      , " Display stanc version number" )
    ; ( "--name"
      , Arg.Set_string Semantic_check.model_name
      , " Take a string to set the model name (default = \
         \"$model_filename_model\")" )
    ; ( "--o"
      , Arg.Set_string output_file
      , " Take the path to an output file for generated C++ code (default = \
         \"$name.hpp\")" )
    ; ( "--print-cpp"
      , Arg.Set print_model_cpp
      , " If set, output the generated C++ Stan model class to stdout." )
    ; ( "--allow_undefined"
      , Arg.Clear Semantic_check.check_that_all_functions_have_definition
      , " Do not fail if a function is declared but not defined" )
    ; ( "--include_paths"
      , Arg.String
          (fun str ->
            Preprocessor.include_paths := String.split_on_chars ~on:[','] str)
      , " Takes a comma-separated list of directories that may contain a file \
         in an #include directive (default = \"\")" ) ]

let model_file_err () =
  Arg.usage options ("Please specify one model_file.\n\n" ^ usage) ;
  exit 127

let add_file filename =
  if !model_file = "" then model_file := filename else model_file_err ()

(** ad directives from the given file. *)
let use_file filename =
  let ast =
    try
      match Parse.parse_file Parser.Incremental.program filename with
      | Result.Ok ast -> ast
      | Result.Error err ->
          let loc = Parse.syntax_error_location err
          and msg = Parse.syntax_error_message err in
          Errors.report_parsing_error (msg, loc) ;
          exit 1
    with Errors.SyntaxError err ->
      Errors.report_syntax_error err ;
      exit 1 in
  Debugging.ast_logger ast ;
  if !pretty_print_program then
    print_endline (Pretty_printing.pretty_print_program ast) ;
  let typed_ast =
    try
      match Semantic_check.semantic_check_program ast with
      | Result.Ok prog -> prog
      | Result.Error (error :: _) ->
          let loc = Semantic_error.location error
          and msg = (Fmt.to_to_string Semantic_error.pp) error in
          Errors.report_semantic_error (msg, loc) ;
          exit 1
      | _ ->
          Printf.eprintf "The impossible happened" ;
          exit 1
    with Errors.SemanticError err ->
      Errors.report_semantic_error err ;
      exit 1 in
  if !generate_data then
    print_endline (Debug_data_generation.print_data_prog typed_ast) ;
  Debugging.typed_ast_logger typed_ast ;
  if not !pretty_print_program then (
    let mir = Ast_to_Mir.trans_prog filename typed_ast in
    if !dump_dot then
      let dotfile = factor_graph_to_dot (prog_factor_graph mir) in
      print_string dotfile;
    if !dump_mir then
      Sexp.pp_hum Format.std_formatter [%sexp (mir : Middle.typed_prog)] ;
    let cpp = Format.asprintf "%a" Stan_math_code_gen.pp_prog mir in
    Out_channel.write_all !output_file ~data:cpp ;
    if !print_model_cpp then print_endline cpp )

let remove_dotstan s = String.drop_suffix s 5

let main () =
  (* Parse the arguments. *)
  Arg.parse options add_file usage ;
  if !model_file = "" then model_file_err () ;
  if !Semantic_check.model_name = "" then
    Semantic_check.model_name :=
      remove_dotstan List.(hd_exn (rev (String.split !model_file ~on:'/')))
      ^ "_model" ;
  if !output_file = "" then output_file := remove_dotstan !model_file ^ ".hpp" ;
  use_file !model_file

let () = main ()
