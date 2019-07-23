(** Some helpers to produce nice error messages and for auto-formatting Stan programs *)

(* TODO: this should probably be made tail recursive by accumulating list of strings in reverse *)
(* TODO: to preserve comments during pretty printing, we should capture them during parsing and attach them to AST nodes *)
(* TODO: we could consider cutting off lines after 80 characters *)

open Core_kernel
open Ast

let wrap_fmt fmt x =
  x |> fmt Format.str_formatter |> Format.flush_str_formatter

let with_hbox ppf f =
  Format.pp_open_hbox ppf () ; f () ; Format.pp_close_box ppf () ; ()

let with_box ppf offset f =
  Format.pp_open_box ppf offset ;
  f () ;
  Format.pp_close_box ppf () ;
  ()

let with_vbox ppf offset f =
  Format.pp_open_vbox ppf offset ;
  f () ;
  Format.pp_close_box ppf () ;
  ()

let comma_no_break = Fmt.unit ", "

let with_indented_box ppf indentation offset f =
  let rec pp_print_n_spaces ppf = function
    | 0 -> ()
    | i ->
        Format.pp_print_space ppf () ;
        pp_print_n_spaces ppf (i - 1) in
  with_hbox ppf (fun () ->
      pp_print_n_spaces ppf indentation ;
      with_box ppf offset f) ;
  ()

let rec unwind_sized_array_type = function
  | Middle.SArray (st, e) -> (
    match unwind_sized_array_type st with st2, es -> (st2, es @ [e]) )
  | st -> (st, [])

let rec unwind_array_type = function
  | Middle.UArray ut -> (
    match unwind_array_type ut with ut2, d -> (ut2, d + 1) )
  | ut -> (ut, 0)

(** XXX this should use the MIR pretty printers after AST pretty printers
    are updated to use `Fmt`. *)
let rec pp_autodifftype ppf = function
  | Middle.DataOnly -> Fmt.pf ppf "data "
  | Middle.AutoDiffable -> Fmt.pf ppf ""

and pp_unsizedtype ppf = function
  | Middle.UInt -> Fmt.pf ppf "int"
  | Middle.UReal -> Fmt.pf ppf "real"
  | Middle.UVector -> Fmt.pf ppf "vector"
  | Middle.URowVector -> Fmt.pf ppf "row_vector"
  | Middle.UMatrix -> Fmt.pf ppf "matrix"
  | Middle.UArray ut ->
      let ut2, d = unwind_array_type ut in
      let array_str = "[" ^ String.make d ',' ^ "]" in
      Fmt.(suffix (const string array_str) pp_unsizedtype ppf ut2)
  | Middle.UFun (argtypes, rt) ->
      Fmt.pf ppf "{|@[<h>(%a) => %a@]|}"
        Fmt.(list ~sep:comma_no_break pp_argtype)
        argtypes pp_returntype rt
  | Middle.UMathLibraryFunction -> Fmt.pf ppf "Stan Math function"

and pp_unsizedtypes ppf l = Fmt.(list ~sep:comma_no_break pp_unsizedtype) ppf l

and pp_argtype ppf = function
  | at, ut -> Fmt.append pp_autodifftype pp_unsizedtype ppf (at, ut)

and pp_returntype ppf = function
  | ReturnType x -> pp_unsizedtype ppf x
  | Void -> Fmt.pf ppf "void"

and pp_identifier ppf id = Fmt.pf ppf "%s" id.name

and pp_operator ppf = function
  | Middle.Plus | PPlus -> Fmt.pf ppf "+"
  | Minus | PMinus -> Fmt.pf ppf "-"
  | Times -> Fmt.pf ppf "*"
  | Divide -> Fmt.pf ppf "/"
  | Modulo -> Fmt.pf ppf "%%"
  | LDivide -> Fmt.pf ppf "\\"
  | EltTimes -> Fmt.pf ppf ".*"
  | EltDivide -> Fmt.pf ppf "./"
  | Pow -> Fmt.pf ppf "^"
  | Or -> Fmt.pf ppf "||"
  | And -> Fmt.pf ppf "&&"
  | Equals -> Fmt.pf ppf "=="
  | NEquals -> Fmt.pf ppf "!="
  | Less -> Fmt.pf ppf "<"
  | Leq -> Fmt.pf ppf "<="
  | Greater -> Fmt.pf ppf ">"
  | Geq -> Fmt.pf ppf ">="
  | PNot -> Fmt.pf ppf "!"
  | Transpose -> Fmt.pf ppf "'"

and pp_index ppf = function
  | All -> Fmt.pf ppf " : "
  | Single e -> pp_expression ppf e
  | Upfrom e -> Fmt.pf ppf "%a : " pp_expression e
  | Downfrom e -> Fmt.pf ppf " : %a" pp_expression e
  | Between (e1, e2) -> Fmt.pf ppf "%a : %a" pp_expression e1 pp_expression e2

and pp_list_of_indices ppf l =
  Fmt.(list ~sep:comma_no_break pp_index) ppf l ;
  ()

and pp_expression ppf {expr= e_content; _} =
  match e_content with
  | TernaryIf (e1, e2, e3) ->
      with_box ppf 0 (fun () ->
          Fmt.pf ppf "%a" pp_expression e1 ;
          Format.pp_print_space ppf () ;
          Fmt.pf ppf "? %a" pp_expression e2 ;
          Format.pp_print_space ppf () ;
          Fmt.pf ppf ": %a" pp_expression e3)
  | BinOp (e1, op, e2) ->
      with_box ppf 0 (fun () ->
          Fmt.pf ppf "%a" pp_expression e1 ;
          Format.pp_print_space ppf () ;
          Fmt.pf ppf "%a %a" pp_operator op pp_expression e2)
  | PrefixOp (op, e) -> Fmt.pf ppf "%a%a" pp_operator op pp_expression e
  | PostfixOp (e, op) -> Fmt.pf ppf "%a%a" pp_expression e pp_operator op
  | Variable id -> pp_identifier ppf id
  | IntNumeral i -> Fmt.pf ppf "%s" i
  | RealNumeral r -> Fmt.pf ppf "%s" r
  | FunApp (_, id, es) ->
      Fmt.pf ppf "%a(" pp_identifier id ;
      with_box ppf 0 (fun () -> Fmt.pf ppf "%a)" pp_list_of_expression es)
  | CondDistApp (_, id, es) -> (
    match es with
    | [] -> Errors.fatal_error ()
    | e :: es' ->
        with_hbox ppf (fun () ->
            Fmt.pf ppf "%a(%a| %a)" pp_identifier id pp_expression e
              pp_list_of_expression es') )
  (* GetLP is deprecated *)
  | GetLP -> Fmt.pf ppf "get_lp()"
  | GetTarget -> Fmt.pf ppf "target()"
  | ArrayExpr es ->
      Fmt.pf ppf "{" ;
      with_box ppf 0 (fun () -> Fmt.pf ppf "%a}" pp_list_of_expression es)
  | RowVectorExpr es ->
      Fmt.pf ppf "[" ;
      with_box ppf 0 (fun () -> Fmt.pf ppf "%a]" pp_list_of_expression es)
  | Paren e -> Fmt.pf ppf "(%a)" pp_expression e
  | Indexed (e, l) -> (
    match l with
    | [] -> Fmt.pf ppf "%a" pp_expression e
    | l -> Fmt.pf ppf "%a[%a]" pp_expression e pp_list_of_indices l )

and pp_list_of_expression ppf es = Fmt.(list ~sep:comma pp_expression) ppf es

and pp_assignmentoperator ppf = function
  | Assign -> Fmt.pf ppf "="
  (* ArrowAssign is deprecated *)
  | ArrowAssign -> Fmt.pf ppf "<-"
  | OperatorAssign op -> Fmt.pf ppf "%a=" pp_operator op

and pretty_print_assignmentoperator op = wrap_fmt pp_assignmentoperator op

and pp_truncation ppf = function
  | NoTruncate -> Fmt.pf ppf ""
  | TruncateUpFrom e -> Fmt.pf ppf " T[%a, ]" pp_expression e
  | TruncateDownFrom e -> Fmt.pf ppf " T[ , %a]" pp_expression e
  | TruncateBetween (e1, e2) ->
      Fmt.pf ppf " T[%a, %a]" pp_expression e1 pp_expression e2

and pp_printable ppf = function
  | PString s -> Fmt.pf ppf "%s" s
  | PExpr e -> pp_expression ppf e

and pp_list_of_printables ppf l =
  Fmt.(list ~sep:comma_no_break pp_printable) ppf l

and pp_sizedtype ppf = function
  | Middle.SInt -> Fmt.pf ppf "int"
  | Middle.SReal -> Fmt.pf ppf "real"
  | Middle.SVector e -> Fmt.pf ppf "vector[%a]" pp_expression e
  | Middle.SRowVector e -> Fmt.pf ppf "row_vector[%a]" pp_expression e
  | Middle.SMatrix (e1, e2) ->
      Fmt.pf ppf "matrix[%a, %a]" pp_expression e1 pp_expression e2
  | Middle.SArray _ -> raise (Errors.FatalError "This should never happen.")

and pp_transformation ppf = function
  | Identity -> Fmt.pf ppf ""
  | Lower e -> Fmt.pf ppf "<lower=%a>" pp_expression e
  | Upper e -> Fmt.pf ppf "<upper=%a>" pp_expression e
  | LowerUpper (e1, e2) ->
      Fmt.pf ppf "<lower=%a, upper=%a>" pp_expression e1 pp_expression e2
  | Offset e -> Fmt.pf ppf "<offset=%a>" pp_expression e
  | Multiplier e -> Fmt.pf ppf "<multiplier=%a>" pp_expression e
  | OffsetMultiplier (e1, e2) ->
      Fmt.pf ppf "<offset=%a, multiplier=%a>" pp_expression e1 pp_expression e2
  | Ordered -> Fmt.pf ppf ""
  | PositiveOrdered -> Fmt.pf ppf ""
  | Simplex -> Fmt.pf ppf ""
  | UnitVector -> Fmt.pf ppf ""
  | CholeskyCorr -> Fmt.pf ppf ""
  | CholeskyCov -> Fmt.pf ppf ""
  | Correlation -> Fmt.pf ppf ""
  | Covariance -> Fmt.pf ppf ""

and pp_transformed_type ppf (st, trans) =
  let unsizedtype_fmt, sizes_fmt =
    match st with
    | Middle.SInt -> (Fmt.const pp_unsizedtype UInt, Fmt.nop)
    | SReal -> (Fmt.const pp_unsizedtype UReal, Fmt.nop)
    | SVector e ->
        ( Fmt.const pp_unsizedtype UVector
        , Fmt.const (fun ppf -> Fmt.pf ppf "[%a]" pp_expression) e )
    | SRowVector e ->
        ( Fmt.const pp_unsizedtype URowVector
        , Fmt.const (fun ppf -> Fmt.pf ppf "[%a]" pp_expression) e )
    | SMatrix (e1, e2) ->
        ( Fmt.const pp_unsizedtype UMatrix
        , Fmt.const
            (fun ppf -> Fmt.pf ppf "[%a, %a]" pp_expression e1 pp_expression)
            e2 )
    | SArray _ -> (
      match unwind_sized_array_type st with
      | st, _ -> (Fmt.const pp_sizedtype st, Fmt.nop) ) in
  let cov_sizes_fmt =
    match st with
    | SMatrix (e1, e2) ->
        if e1 = e2 then
          Fmt.const (fun ppf -> Fmt.pf ppf "[%a]" pp_expression) e1
        else
          Fmt.const
            (fun ppf -> Fmt.pf ppf "[%a, %a]" pp_expression e1 pp_expression)
            e2
    | _ -> Fmt.nop in
  match trans with
  | Identity -> pp_sizedtype ppf st
  | Lower _ | Upper _ | LowerUpper _ | Offset _ | Multiplier _
   |OffsetMultiplier _ ->
      Fmt.pf ppf "%a%a%a" unsizedtype_fmt () pp_transformation trans sizes_fmt
        ()
  | Ordered -> Fmt.pf ppf "ordered%a" sizes_fmt ()
  | PositiveOrdered -> Fmt.pf ppf "positive_ordered%a" sizes_fmt ()
  | Simplex -> Fmt.pf ppf "simplex%a" sizes_fmt ()
  | UnitVector -> Fmt.pf ppf "unit_vector%a" sizes_fmt ()
  | CholeskyCorr -> Fmt.pf ppf "cholesky_factor_corr%a" cov_sizes_fmt ()
  | CholeskyCov -> Fmt.pf ppf "cholesky_factor_cov%a" cov_sizes_fmt ()
  | Correlation -> Fmt.pf ppf "corr_matrix%a" cov_sizes_fmt ()
  | Covariance -> Fmt.pf ppf "cov_matrix%a" cov_sizes_fmt ()

and pp_array_dims ppf = function
  | [] -> Fmt.pf ppf ""
  | es ->
      Fmt.pf ppf "[" ;
      with_box ppf 0 (fun () ->
          Fmt.pf ppf "%a]" pp_list_of_expression (List.rev es))

and pp_indent_unless_block ppf s =
  match s.stmt with
  | Block _ -> pp_statement ppf s
  | _ ->
      Format.pp_print_cut ppf () ;
      with_indented_box ppf 2 0 (fun () -> Fmt.pf ppf "%a" pp_statement s)

(* This function helps write chained if-then-else-if-... blocks
 * correctly. Without it, each IfThenElse would trigger a new
 * vbox in front of the if, adding spaces for each level of IfThenElse.
 *)
and pp_recursive_ifthenelse ppf s =
  match s.stmt with
  | IfThenElse (e, s, None) ->
      Fmt.pf ppf "if (%a) %a" pp_expression e pp_indent_unless_block s
  | IfThenElse (e, s1, Some s2) ->
      Fmt.pf ppf "if (%a) %a" pp_expression e pp_indent_unless_block s1 ;
      Format.pp_print_cut ppf () ;
      Fmt.pf ppf "else %a" pp_recursive_ifthenelse s2
  | _ -> pp_indent_unless_block ppf s

and pp_statement ppf ({stmt= s_content; _} as ss) =
  match s_content with
  | Assignment
      { assign_lhs= {assign_identifier= id; assign_indices= lindex; _}
      ; assign_op= assop
      ; assign_rhs= e } ->
      let inds_fmt ppf lindex =
        match lindex with
        | [] -> Fmt.nop ppf ()
        | l -> Fmt.pf ppf "[%a]" pp_list_of_indices l in
      with_hbox ppf (fun () ->
          Fmt.pf ppf "%a%a %a %a;" pp_identifier id inds_fmt lindex
            pp_assignmentoperator assop pp_expression e)
  | NRFunApp (_, id, es) ->
      Fmt.pf ppf "%a(" pp_identifier id ;
      with_box ppf 0 (fun () -> Fmt.pf ppf "%a);" pp_list_of_expression es)
  | TargetPE e -> Fmt.pf ppf "target += %a;" pp_expression e
  | IncrementLogProb e ->
      with_hbox ppf (fun () ->
          Fmt.pf ppf "increment_log_prob(%a);" pp_expression e)
  | Tilde {arg= e; distribution= id; args= es; truncation= t} ->
      Fmt.pf ppf "%a ~ %a(" pp_expression e pp_identifier id ;
      with_box ppf 0 (fun () -> Fmt.pf ppf "%a)" pp_list_of_expression es) ;
      Fmt.pf ppf "%a;" pp_truncation t
  | Break -> Fmt.pf ppf "break;"
  | Continue -> Fmt.pf ppf "continue;"
  | Return e ->
      with_hbox ppf (fun () -> Fmt.pf ppf "return %a;" pp_expression e)
  | ReturnVoid -> Fmt.pf ppf "return;"
  | Print ps -> Fmt.pf ppf "print(%a);" pp_list_of_printables ps
  | Reject ps -> Fmt.pf ppf "reject(%a);" pp_list_of_printables ps
  | Skip -> Fmt.pf ppf ";"
  | IfThenElse (_, _, _) ->
      with_vbox ppf 0 (fun () -> pp_recursive_ifthenelse ppf ss)
  | While (e, s) -> Fmt.pf ppf "while (%a) %a" pp_expression e pp_statement s
  | For {loop_variable= id; lower_bound= e1; upper_bound= e2; loop_body= s} ->
      with_vbox ppf 0 (fun () ->
          Fmt.pf ppf "for (%a in %a : %a) %a" pp_identifier id pp_expression e1
            pp_expression e2 pp_indent_unless_block s)
  | ForEach (id, e, s) ->
      Fmt.pf ppf "for (%a in %a) %a" pp_identifier id pp_expression e
        pp_indent_unless_block s
  | Block vdsl ->
      Fmt.pf ppf "{" ;
      Format.pp_print_cut ppf () ;
      with_indented_box ppf 2 0 (fun () -> pp_list_of_statements ppf vdsl) ;
      Format.pp_print_cut ppf () ;
      Fmt.pf ppf "}"
  | VarDecl
      { sizedtype= st
      ; transformation= trans
      ; identifier= id
      ; initial_value= init
      ; is_global= _ } ->
      let st2, es = unwind_sized_array_type st in
      let pp_init ppf init =
        match init with
        | None -> Fmt.pf ppf ""
        | Some e -> Fmt.pf ppf " = %a" pp_expression e in
      with_hbox ppf (fun () ->
          Fmt.pf ppf "%a %a%a%a;" pp_transformed_type (st2, trans)
            pp_identifier id pp_array_dims es pp_init init)
  | FunDef {returntype= rt; funname= id; arguments= args; body= b} -> (
      Fmt.pf ppf "%a %a(" pp_returntype rt pp_identifier id ;
      with_box ppf 0 (fun () ->
          Fmt.pf ppf "%a" (Fmt.list ~sep:Fmt.comma pp_args) args) ;
      match b with
      | {stmt= Skip; _} -> Fmt.pf ppf ");"
      | b -> Fmt.pf ppf ") %a" pp_statement b )

and pp_args ppf (at, ut, id) =
  Fmt.pf ppf "%a%a %a" pp_autodifftype at pp_unsizedtype ut pp_identifier id

and pp_list_of_statements ppf l =
  with_vbox ppf 0 (fun () -> Format.pp_print_list pp_statement ppf l)

and pp_block block_name ppf block_stmts =
  Fmt.pf ppf "%s {" block_name ;
  Format.pp_print_cut ppf () ;
  if List.length block_stmts > 0 then (
    with_indented_box ppf 2 0 (fun () ->
        pp_list_of_statements ppf block_stmts ;
        ()) ;
    Format.pp_print_cut ppf () )
  else Format.pp_print_cut ppf () ;
  Fmt.pf ppf "}" ;
  Format.pp_print_cut ppf ()

and pp_opt_block ppf block_name opt_block =
  Fmt.option ~none:Fmt.nop (pp_block block_name) ppf opt_block

and pp_program ppf = function
  | { functionblock= bf
    ; datablock= bd
    ; transformeddatablock= btd
    ; parametersblock= bp
    ; transformedparametersblock= btp
    ; modelblock= bm
    ; generatedquantitiesblock= bgq } ->
      Format.pp_open_vbox ppf 0 ;
      pp_opt_block ppf "functions" bf ;
      pp_opt_block ppf "data" bd ;
      pp_opt_block ppf "transformed data" btd ;
      pp_opt_block ppf "parameters" bp ;
      pp_opt_block ppf "transformed parameters" btp ;
      pp_opt_block ppf "model" bm ;
      pp_opt_block ppf "generated quantities" bgq ;
      Format.pp_close_box ppf ()

and pretty_print_program p = wrap_fmt pp_program p
