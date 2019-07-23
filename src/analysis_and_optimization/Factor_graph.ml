open Core_kernel
open Middle
open Dataflow_types
open Mir_utils

(*open Dataflow_utils*)
open Dependence_analysis

type factor =
  | TargetTerm of expr_typed_located
  | Reject
  | LPFunction of (string * expr_typed_located list)
[@@deriving sexp, hash, compare]

let extract_factors_statement (stmt : (expr_typed_located, 's) statement) :
    factor list =
  match stmt with
  | Middle.TargetPE e ->
      List.map (summation_terms e) ~f:(fun x -> TargetTerm x)
  | Middle.NRFunApp (_, f, _) when internal_fn_of_string f = Some FnReject ->
      [Reject]
  | Middle.NRFunApp (_, s, args) when String.suffix s 3 = "_lp" ->
      [LPFunction (s, args)]
  | Middle.Assignment (_, _)
   |Middle.NRFunApp (_, _, _)
   |Middle.Break | Middle.Continue | Middle.Return _ | Middle.Skip
   |Middle.IfElse (_, _, _)
   |Middle.While (_, _)
   |Middle.For _ | Middle.Block _ | Middle.SList _
   |Middle.Decl {decl_id= _; _} ->
      []

let rec extract_factors
    (statement_map :
      (label, (expr_typed_located, label) statement * 'm) Map.Poly.t)
    (label : label) : (label * factor) list =
  let stmt, _ = Map.Poly.find_exn statement_map label in
  let this_stmt =
    List.map (extract_factors_statement stmt) ~f:(fun x -> (label, x)) in
  fold_statement
    (fun s _ -> s)
    (fun state label ->
      List.append state (extract_factors statement_map label))
    this_stmt stmt

let factor_rhs (factor : factor) : vexpr Set.Poly.t =
  match factor with
  | TargetTerm e -> expr_var_set e
  | Reject -> Set.Poly.empty
  | LPFunction (_, es) -> Set.Poly.of_list (List.map es ~f:vexpr_of_expr_exn)

let factor_var_dependencies
    (statement_map :
      (label, (expr_typed_located, label) statement * node_dep_info) Map.Poly.t)
    ((label, factor) : label * factor) : vexpr Set.Poly.t =
  let rhs = factor_rhs factor in
  let dep_labels = node_vars_dependencies statement_map rhs label in
  let label_vars l =
    stmt_rhs_var_set (fst (Map.Poly.find_exn statement_map l)) in
  let dep_vars = union_map dep_labels ~f:label_vars in
  Set.Poly.union dep_vars rhs

(* So far just extracts factors in log_prob, finds their dependencies *)
let prog_factor_graph (prog : typed_prog) :
    (label * factor * vexpr Set.Poly.t) list =
  let statement_map = log_prob_build_dep_info_map prog in
  let factors = extract_factors statement_map 1 in
  let outvars = Set.Poly.of_list (List.map prog.output_vars ~f:(fun (s, _) -> VVar s)) in
  List.map factors ~f:(fun (fac, l) ->
      (fac, l, Set.Poly.inter outvars (factor_var_dependencies statement_map (fac, l))))

let string_of_factor (factor : factor) : string =
  match factor with
  | TargetTerm e -> Fmt.strf "%a" Pretty.pp_expr_typed_located e
  | Reject -> "reject"
  | LPFunction (s, _) -> s

let string_of_vexpr (vexpr : vexpr) : string = match vexpr with VVar s -> s

let factor_graph_to_dot (factors : (label * factor * vexpr Set.Poly.t) list) : string =
  let factor_names = List.map ~f:(fun (_, f, ps) -> (string_of_factor f, List.map ~f:string_of_vexpr (Set.Poly.to_list ps))) factors in
  let (factor_strings, param_string_lists) = List.unzip factor_names in
  let param_strings = List.dedup_and_sort ~compare:String.compare (List.concat param_string_lists) in
  let edge_strings = List.concat_map ~f:(fun (f, ps) -> List.map ~f:(fun p -> String.concat [f; " -- "; p]) ps) factor_names in
  [ [ "graph {" ]
  ; factor_strings
  ; param_strings
  ; edge_strings
  ; [ "}" ]
  ]
  |> List.concat
  |> String.concat ~sep:"\n"
