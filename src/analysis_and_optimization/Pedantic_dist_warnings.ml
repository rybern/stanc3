open Core_kernel
open Middle
open Mir_utils

(* Useful information about an expression. Opaque means we don't know anything. *)
type compiletime_val
  = Opaque
  | Number of (float * string)
  | Param of (string * bound_values)
  | Data of string

(* Info about a distribution occurrences that's useful for checking that
   distribution properties are met
*)
type dist_info =
  { name : string
  ; loc : Location_span.t
  ; args : (compiletime_val * Expr.Typed.Meta.t) List.t
  }

let uniform_dist_message (pname : string) : string =
  Printf.sprintf
    "Parameter %s is given a uniform distribution. The uniform distribution is \
     not recommended, for two reasons: (a) Except when there are logical or \
     physical constraints, it is very unusual for you to be sure that a \
     parameter will fall inside a specified range, and (b) The infinite \
     gradient induced by a uniform density can cause difficulties for Stan's \
     sampling algorithm. As a consequence, we recommend soft constraints rather \
     than hard constraints; for example, instead of giving an elasticity \
     parameter a uniform(0,1) distribution, try normal(0.5,0.5)."
    pname

(* Warning for all uniform distributions with a parameter *)
let uniform_dist_warning (dist_info : dist_info) : (Location_span.t * string) option =
  match dist_info with
  | {args=(Param (pname, bounds), _)::(arg1,_)::(arg2,_)::_; _} ->
    let warning =
      Some (dist_info.loc, uniform_dist_message pname)
    in
    (match (arg1, arg2, bounds) with
     | (_, _, {upper = `None; _})
     | (_, _, {lower = `None; _}) ->
       (* the variate is unbounded *)
       warning
     | (Number (uni, _), _, {lower = `Lit bound; _})
     | (_, Number (uni, _), {upper = `Lit bound; _}) ->
       (* the variate is bounded differently than the uniform dist *)
       if uni = bound then
         None
       else
         warning
     | _ -> None)
  | _ -> None

let lkj_corr_message : string =
  "It is suggested to replace lkj_corr with lkj_corr_cholesky, the Cholesky \
   factor variant. lkj_corr tends to run slower, consume more memory, and has \
   higher risk of numerical errors."

let lkj_corr_dist_warning (dist_info : dist_info)
  : (Location_span.t * string) option =
  Some (dist_info.loc, lkj_corr_message)

let gamma_arg_dist_message : string =
  "There is a gamma or inverse-gamma distribution with parameters that are \
   equal to each other and set to values less than 1. This is mathematically \
   acceptable and can make sense in some problems, but typically we see this \
   model used as an attempt to assign a noninformative prior distribution. In \
   fact, priors such as inverse-gamma(.001,.001) can be very strong, as \
   explained by Gelman (2006). Instead we recommend something like a \
   normal(0,1) or student_t(4,0,1), with parameter constrained to be \
   positive."

(* Warning particular to gamma and inv_gamma, when A=B<1 *)
let gamma_arg_dist_warning (dist_info : dist_info) : (Location_span.t * string) option =
  match dist_info with
  | {args= [ _; (Number (a, _), meta); (Number (b, _), _) ]; _} ->
    if a = b && a < 1. then
      Some (meta.loc, gamma_arg_dist_message)
    else None
  | _ -> None

type range =
  { name : string
  ; lower : (float * bool) option
  ; upper : (float * bool) option
  }

let unit_range =
  { name = "[0,1]"
  ; lower = Some (0., true)
  ; upper = Some (1., true)
  }

let positive_range =
  { name = "positive"
  ; lower = Some (0., false)
  ; upper = None
  }

let bounds_out_of_range (range : range) (bounds : bound_values) =
  match (bounds.lower, bounds.upper, range.lower, range.upper) with
  | (`None, _, Some _, _) -> true
  | (_, `None, _, Some _) -> true
  | (`Lit l, _, Some (l', _), _) when l < l' -> true
  | (_, `Lit u, _, Some (u', _)) when u > u' -> true
  | _ -> false

let value_out_of_range (range : range) (v : float) =
  let lower_bad = match range.lower with
    | Some (l, true) -> v < l
    | Some (l, false) -> v <= l
    | None -> false
  in
  let upper_bad = match range.upper with
    | Some (u, true) -> v > u
    | Some (u, false) -> v >= u
    | None -> false
  in lower_bad || upper_bad

let arg_range_bounds_message (dist_name : string) (param_name : string)
    (arg_name : string) (argn : int) (range_name : string) : string =
  Printf.sprintf
    "A %s distribution has parameter %s as %s (argument %d), but %s is not \
     constrained to be %s."
    dist_name param_name arg_name argn param_name range_name

let arg_range_literal_message (dist_name : string) (num_str : string)
    (arg_name : string) (argn : int) (range_name : string) : string =
  Printf.sprintf
    "A %s distribution has value %s as %s (argument %d), but %s should be %s."
    dist_name num_str arg_name argn arg_name range_name

let arg_range_warning (range : range) (argn : int) (arg_name : string)
    ({args; name; loc} : dist_info) : (Location_span.t * string) option =
  let v = match (List.nth args argn) with
    | Some v -> v
    | None ->
      (raise (Failure ("Distribution " ^ name
                       ^ " at " ^ Location_span.to_string loc
                       ^ " expects more arguments." )))
  in
  match v with
  | (Param (pname, bounds), meta) ->
    if bounds_out_of_range range bounds then
      Some ( meta.loc
           , arg_range_bounds_message name pname arg_name argn range.name)
    else None
  | (Number (num, num_str), meta) ->
    if value_out_of_range range num then
      Some ( meta.loc
           , arg_range_literal_message name num_str arg_name argn range.name)
    else None
  | _ -> None

let variate_range_bounds_message (dist_name : string) (param_name : string)
    (range_name : string) : string =
  Printf.sprintf
    "Parameter %s is given a %s distribution, which has %s range, but was \
     declared with no constraints or incompatible constraints. Either \
     change the distribution or change the constraints."
    param_name dist_name range_name

(* Warning when the dist's parameter should be bounded >0 *)
let variate_range_warning (range : range) (dist_info : dist_info)
  : (Location_span.t * string) option =
  match dist_info with
  | {args=(Param (pname, bounds), meta)::_; _} ->
    if bounds_out_of_range range bounds then
      Some ( meta.loc
           , variate_range_bounds_message dist_info.name pname range.name)
    else None
  | _ -> None

(* Generate the warnings that are relevant to a given distribution *)
let distribution_warning (dist_info : dist_info)
  : (Location_span.t * string) List.t =
  let scale_name = "a scale parameter" in
  let inv_scale_name = "an inverse scale parameter" in
  let shape_name = "a shape parameter" in
  let dof_name = "degrees of freedom" in
  (* Information mostly from:
     https://mc-stan.org/docs/2_21/functions-reference/unbounded-continuous-distributions.html
  *)
  let warning_fns = match dist_info.name with
  (* Unbounded Continuous Distributions *)
  | "normal" -> [
      arg_range_warning positive_range 2 scale_name
    ]
  | "normal_id_glm" -> [
      arg_range_warning positive_range 4 scale_name
    ]
  | "exp_mod_normal" -> [
      arg_range_warning positive_range 2 scale_name
    ; arg_range_warning positive_range 3 shape_name
    ]
  | "skew_normal" -> [
      arg_range_warning positive_range 2 scale_name
    ]
  | "student_t" -> [
      arg_range_warning positive_range 1 dof_name
    ; arg_range_warning positive_range 3 scale_name
    ]
  | "cauchy" -> [
      arg_range_warning positive_range 2 scale_name
    ]
  | "double_exponential" -> [
      arg_range_warning positive_range 2 scale_name
    ]
  | "logistic" -> [
      arg_range_warning positive_range 2 scale_name
    ]
  | "gumbel" -> [
      arg_range_warning positive_range 2 scale_name
    ]
  (* Positive Continuous Distributions *)
  | "lognormal" -> [
      variate_range_warning positive_range
    ; arg_range_warning positive_range 2 scale_name
    ]
  | "chi_square" -> [
      variate_range_warning positive_range
    ; arg_range_warning positive_range 1 dof_name
    ]
  | "inv_chi_square" -> [
      variate_range_warning positive_range
    ; arg_range_warning positive_range 1 dof_name
    ]
  | "scaled_inv_chi_square" -> [
      variate_range_warning positive_range
    ; arg_range_warning positive_range 1 dof_name
    ; arg_range_warning positive_range 2 scale_name
    ]
  | "exponential" -> [
      variate_range_warning positive_range
    ; arg_range_warning positive_range 1 scale_name
    ]
  | "gamma" -> [
      variate_range_warning positive_range
    ; arg_range_warning positive_range 1 shape_name
    ; arg_range_warning positive_range 2 inv_scale_name
    ; gamma_arg_dist_warning
    ]
  | "inv_gamma" -> [
      variate_range_warning positive_range
    ; arg_range_warning positive_range 1 shape_name
    ; arg_range_warning positive_range 2 scale_name
    ; gamma_arg_dist_warning
    ]
  | "weibull" -> [
      (* Note: variate non-negative *)
      variate_range_warning positive_range
    ; arg_range_warning positive_range 1 shape_name
    ; arg_range_warning positive_range 2 scale_name
    ]
  | "frechet" -> [
      variate_range_warning positive_range
    ; arg_range_warning positive_range 1 shape_name
    ; arg_range_warning positive_range 2 scale_name
    ]
  (* Non-negative Continuous Distributions *)
  (* No real distinction needed here between positive and non-negative lower
     bounds *)
  | "rayleigh" -> [
      variate_range_warning positive_range
    ; arg_range_warning positive_range 1 scale_name
    ]
  | "wiener" -> [
      (* Note: Could do more here, since variate should be > arg 2 *)
      (* Note: Variate actually positive, not non-negative *)
      variate_range_warning positive_range
    ; arg_range_warning positive_range 1 "a boundary separation parameter"
    ; arg_range_warning positive_range 2 "a non-decision time parameter"
    ; arg_range_warning unit_range 3 "an a-priori bias parameter"
    ]
  (* Positive Lower-Bounded Probabilities *)
  (* Currently treating these as if they're positive bounded,
     could easily do better *)
  | "pareto" -> [
      (* Note: Variate >= arg 1 *)
      variate_range_warning positive_range
    ; arg_range_warning positive_range 1 "a positive minimum parameter"
    ; arg_range_warning positive_range 2 shape_name
    ]
  | "pareto_type_2" -> [
      (* Note: Variate >= arg 1 *)
      arg_range_warning positive_range 2 scale_name
    ; arg_range_warning positive_range 3 shape_name
    ]
  (* Continuous Distributions on [0,1] *)
  | "beta" -> [
      (* Note: Variate is actually (0, 1) *)
      variate_range_warning unit_range
    ; arg_range_warning positive_range 1 "a count parameter"
    ; arg_range_warning positive_range 2 "a count parameter"
    ]
  | "beta_proportion" -> [
      variate_range_warning unit_range
    (* Note: Variate is actually (0, 1) *)
    (* Note: Arg 1 is actually (0, 1) *)
    ; arg_range_warning unit_range 1 "a unit mean parameter"
    ; arg_range_warning positive_range 2 "a precision parameter"
    ]
  (* Circular Distributions *)
  | "von_mises" -> [
      arg_range_warning positive_range 2 scale_name
    ]
  (* Bounded Continuous Distributions *)
  | "uniform" -> [
      (* Could also check b > c *)
      (* Can this be generalized, by restricting a < variate < b? *)
      uniform_dist_warning
    ]
  (* Distributions over Unbounded Vectors *)
  (* Note: untested section *)
  | "multi_normal" -> [
      (* Note: arg 2 "covariance matrix" symmetric and pos-definite *)
    ]
  | "multi_normal_prec" -> [
      (* Note: arg 2 "positive definite precision matrix" is
         symmetric and pos-definite *)
    ]
  | "multi_normal_cholesky" -> [
      (* Note: arg 2 "covariance matrix" is symmetric and pos-definite *)
    ]
  | "multi_gp" -> [
      (* Note: arg 1 "kernel matrix" is symmetric, positive definite kernel matrix*)
      (* Note: arg 2 "inverse scales" is vector of positive inverse scales*)
    ]
  | "multi_gp_cholesky" -> [
      (* Note: arg 1 "Cholesky factor of the kernel matrix"
         is lower triangular and such that LL^⊤ is positive
         definite kernel matrix
         (implying L n , n > 0 for n ∈ 1 : N)*)
      (* Note: arg 2 "inverse scales" is vector of positive inverse scales*)
    ]
  | "multi_student_t" -> [
      (* Note: arg 2 "scale matrix" symmetric and pos-definite *)
      arg_range_warning positive_range 1 dof_name
    ]
  | "gaussian_dlm_obs" -> [
      (* Note: arg 2 "transition matrix" might be positive? *)
      (* Note: arg 3 "observation covariance matrix" is covariance *)
      (* Note: arg 4 "system covariance matrix" is covariance *)
    ]
  (* Simplex Distributions *)
  | "dirichlet" -> [
      (* Note: variate simplex *)
      variate_range_warning unit_range
    ; arg_range_warning positive_range 1 "a count parameter"
    ]
  (* Correlation Matrix Distributions *)
  (* Note: untested section *)
  | "lkj_corr" -> [
      (* Note: variate is symmetric, pos-definite (correlation) *)
      (* Note: Warning: The only reason to use this density function is if you want the code to run slower and consume more memory with more risk of numerical errors. Use its Cholesky factor as described in the next section.
      *)
      lkj_corr_dist_warning
    ]
  | "lkj_corr_cholesky" -> [
      (* variate is lower-triangular *)
    ]
  (* Covariance Matrix Distributions *)
  (* Note: untested section *)
  | "wishart" -> [
      (* Note: variate is symmetric and pos-def *)
      (* Note: arg 2 "scale matrix" is symmetric and pos-def *)
        arg_range_warning positive_range 1 dof_name
    ]
  | "inv_wishart" -> [
      (* Note: variate is symmetric and pos-def *)
      (* Note: arg 2 "scale matrix" is symmetric and pos-def *)
        arg_range_warning positive_range 1 dof_name
    ]
  | _ -> []
  in
  List.filter_map ~f:(fun f -> f dist_info) warning_fns

(* Generate the distribution warnings for a program *)
let list_distribution_warnings (distributions_list : dist_info Set.Poly.t)
  : (Location_span.t * string) Set.Poly.t =
  union_map
    ~f:(fun dist_info ->
        Set.Poly.of_list (distribution_warning dist_info))
    distributions_list
