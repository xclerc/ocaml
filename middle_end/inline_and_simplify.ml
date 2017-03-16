(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2016 OCamlPro SAS                                    *)
(*   Copyright 2014--2016 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module A = Simple_value_approx
module B = Inlining_cost.Benefit
module E = Inline_and_simplify_aux.Env
module R = Inline_and_simplify_aux.Result

(** Values of two types hold the information propagated during simplification:
    - [E.t] "environments", top-down, almost always called "env";
    - [R.t] "results", bottom-up approximately following the evaluation order,
      almost always called "r".  These results come along with rewritten
      Flambda terms.
    The environments map variables to approximations, which enable various
    simplifications to be performed; for example, some variable may be known
    to always hold a particular constant.
*)

let ret = R.set_approx

type simplify_variable_result =
  | No_binding of Variable.t
  | Binding of Variable.t * (Flambda.named Flambda.With_free_variables.t)

let simplify_free_variable_internal env original_var =
  let var = Freshening.apply_variable (E.freshening env) original_var in
  let original_var = var in
  (* In the case where an approximation is useful, we introduce a [let]
     to bind (e.g.) the constant or symbol replacing [var], unless this
     would introduce a useless [let] as a consequence of [var] already being
     in the current scope.

     Even when the approximation is not useful, this simplification helps.
     In particular, it squashes aliases of the form:
      let var1 = var2 in ... var2 ...
     by replacing [var2] in the body with [var1].  Simplification can then
     eliminate the [let].
  *)
  let var =
    let approx = E.find_exn env var in
    match approx.var with
    | Some var when E.mem env var -> var
    | Some _ | None -> var
  in
  (* CR-soon mshinwell: Should we update [r] when we *add* code?
     Aside from that, it looks like maybe we don't need [r] in this function,
     because the approximation within it wouldn't be used by any of the
     call sites. *)
  match E.find_with_scope_exn env var with
  | Current, approx -> No_binding var, approx  (* avoid useless [let] *)
  | Outer, approx ->
    let module W = Flambda.With_free_variables in
    match A.simplify_var approx with
    | None -> No_binding var, approx
    | Some (named, approx) -> Binding (original_var, W.of_named named), approx

(*
let _simplify_free_variable env var ~f =
  match simplify_free_variable_internal env var with
  | No_binding var, approx -> f env var approx
  | Binding (var, named), approx ->
    let var = Variable.rename var in
    let env = E.add env var approx in
    let body, r = f env var approx in
    Flambda.create_let var named body, r
*)

let simplify_free_variable env var ~f : Flambda.t * R.t =
  match simplify_free_variable_internal env var with
  | No_binding var, approx -> f env var approx
  | Binding (var, named), approx ->
    let module W = Flambda.With_free_variables in
    let var = Variable.rename var in
    let env = E.add env var approx in
    let body, r = f env var approx in
    (W.create_let_reusing_defining_expr var named body), r

let simplify_free_variables env vars ~f : Flambda.t * R.t =
  let rec collect_bindings vars env bound_vars approxs : Flambda.t * R.t =
    match vars with
    | [] -> f env (List.rev bound_vars) (List.rev approxs)
    | var::vars ->
      match simplify_free_variable_internal env var with
      | No_binding var, approx ->
        collect_bindings vars env (var::bound_vars) (approx::approxs)
      | Binding (var, named), approx ->
        let module W = Flambda.With_free_variables in
        let var = Variable.rename var in
        let env = E.add env var approx in
        let body, r =
          collect_bindings vars env (var::bound_vars) (approx::approxs)
        in
        (W.create_let_reusing_defining_expr var named body), r
  in
  collect_bindings vars env [] []

let simplify_free_variables_named env vars ~f =
  let rec collect_bindings vars env bound_vars approxs
        : (Variable.t * Flambda.named) list * Flambda.named_reachable
            * R.t =
    match vars with
    | [] -> f env (List.rev bound_vars) (List.rev approxs)
    | var::vars ->
      match simplify_free_variable_internal env var with
      | No_binding var, approx ->
        collect_bindings vars env (var::bound_vars) (approx::approxs)
      | Binding (var, named), approx ->
        let named = Flambda.With_free_variables.to_named named in
        let var = Variable.rename var in
        let env = E.add env var approx in
        let bindings, body_named, r =
          collect_bindings vars env (var::bound_vars) (approx::approxs)
        in
        (var, named) :: bindings, body_named, r
  in
  collect_bindings vars env [] []

(* CR-soon mshinwell: tidy this up *)
let simplify_free_variable_named env var ~f =
  simplify_free_variables_named env [var] ~f:(fun env vars vars_approxs ->
    match vars, vars_approxs with
    | [var], [approx] -> f env var approx
    | _ -> assert false)

let simplify_named_using_approx r named approx
      : (Variable.t * Flambda.named) list * Flambda.named_reachable
          * R.t =
  let named, _summary, approx = A.simplify_named approx named in
  [], Reachable named, R.set_approx r approx

let simplify_named_using_approx_and_env env r original_named approx
      : (Variable.t * Flambda.named) list * Flambda.named_reachable
          * R.t =
  let named, summary, approx =
    A.simplify_named_using_env approx ~is_present_in_env:(E.mem env)
      original_named
  in
  let r =
    let r = ret r approx in
    match summary with
    | Replaced_term -> R.map_benefit r (B.remove_code_named original_named)
    | Nothing_done -> r
  in
  [], Reachable named, r

let approx_for_const (const : Flambda.const) =
  match const with
  | Int i -> A.value_int i
  | Char c -> A.value_char c
  | Const_pointer i -> A.value_constptr i

let approx_for_allocated_const (const : Allocated_const.t) =
  match const with
  | String s -> A.value_string (String.length s) None
  | Immutable_string s -> A.value_string (String.length s) (Some s)
  | Int32 i -> A.value_boxed_int Int32 i
  | Int64 i -> A.value_boxed_int Int64 i
  | Nativeint i -> A.value_boxed_int Nativeint i
  | Float f -> A.value_float f
  | Float_array a -> A.value_mutable_float_array ~size:(List.length a)
  | Immutable_float_array a ->
      A.value_immutable_float_array
        (Array.map A.value_float (Array.of_list a))

type filtered_switch_branches =
  | Must_be_taken of Continuation.t
  | Can_be_taken of (int * Continuation.t) list

(* Determine whether a given closure ID corresponds directly to a variable
   (bound to a closure) in the given environment.  This happens when the body
   of a [let rec]-bound function refers to another in the same set of closures.
   If we succeed in this process, we can change [Project_closure]
   expressions into [Var] expressions, thus sharing closure projections. *)
let reference_recursive_function_directly env closure_id =
  let closure_id = Closure_id.unwrap closure_id in
  match E.find_opt env closure_id with
  | None -> None
  | Some approx -> Some (Flambda.Var closure_id, approx)

(* Simplify an expression that takes a set of closures and projects an
   individual closure from it. *)
let simplify_project_closure env r ~(project_closure : Flambda.project_closure)
      : (Variable.t * Flambda.named) list
          * Flambda.named_reachable * R.t =
  simplify_free_variable_named env project_closure.set_of_closures
    ~f:(fun _env set_of_closures set_of_closures_approx ->
      match A.check_approx_for_set_of_closures set_of_closures_approx with
      | Wrong ->
        Misc.fatal_errorf "Wrong approximation when projecting closure: %a"
          Flambda.print_project_closure project_closure
      | Unresolved value ->
        (* A set of closures coming from another compilation unit, whose .cmx is
           missing; as such, we cannot have rewritten the function and don't
           need to do any freshening. *)
        [], Reachable (Project_closure {
          set_of_closures;
          closure_id = project_closure.closure_id;
        }), ret r (A.value_unresolved value)
      | Unknown ->
        (* CR-soon mshinwell: see CR comment in e.g. simple_value_approx.ml
           [check_approx_for_closure_allowing_unresolved] *)
        [], Reachable (Project_closure {
          set_of_closures;
          closure_id = project_closure.closure_id;
        }), ret r (A.value_unknown Other)
      | Unknown_because_of_unresolved_value value ->
        [], Reachable (Project_closure {
          set_of_closures;
          closure_id = project_closure.closure_id;
        }), ret r (A.value_unknown (Unresolved_value value))
      | Ok (set_of_closures_var, value_set_of_closures) ->
        let closure_id =
          A.freshen_and_check_closure_id value_set_of_closures
            project_closure.closure_id
        in
        let () =
          match Closure_id.Set.elements closure_id with
          | _ :: _ :: _ ->
            Format.printf "Set of closures approximation is not a singleton \
                in project closure@ %a@ %a@."
              A.print set_of_closures_approx
              Projection.print_project_closure project_closure
          | [] ->
            Format.printf "Set of closures approximation is empty in project \
                closure@ %a@ %a@."
              A.print set_of_closures_approx
              Projection.print_project_closure project_closure
          | _ ->
            ()
        in
        let projecting_from =
          match set_of_closures_var with
          | None -> None
          | Some set_of_closures_var ->
            let projection : Projection.t =
              Project_closure {
                set_of_closures = set_of_closures_var;
                closure_id;
              }
            in
            match E.find_projection env ~projection with
            | None -> None
            | Some var -> Some (var, projection)
        in
        match projecting_from with
        | Some (var, projection) ->
          simplify_free_variable_named env var ~f:(fun _env var var_approx ->
            let r = R.map_benefit r (B.remove_projection projection) in
            [], Reachable (Var var), ret r var_approx)
        | None ->
          let if_not_reference_recursive_function_directly ()
            : (Variable.t * Flambda.named) list * Flambda.named_reachable
                * R.t =
            let set_of_closures_var =
              match set_of_closures_var with
              | Some set_of_closures_var' when E.mem env set_of_closures_var' ->
                set_of_closures_var
              | Some _ | None -> None
            in
            let approx =
              A.value_closure ?set_of_closures_var
                (Closure_id.Map.of_set (fun _ -> value_set_of_closures)
                   closure_id)
            in
            [], Reachable (Project_closure { set_of_closures; closure_id; }),
              ret r approx
          in
          match Closure_id.Set.get_singleton closure_id with
          | None ->
            if_not_reference_recursive_function_directly ()
          | Some closure_id ->
            match reference_recursive_function_directly env closure_id with
            | Some (flam, approx) -> [], Reachable flam, ret r approx
            | None ->
              if_not_reference_recursive_function_directly ())

(* Simplify an expression that, given one closure within some set of
   closures, returns another closure (possibly the same one) within the
   same set. *)
let simplify_move_within_set_of_closures env r
      ~(move_within_set_of_closures : Flambda.move_within_set_of_closures)
      : (Variable.t * Flambda.named) list
          * Flambda.named_reachable * R.t =
  simplify_free_variable_named env move_within_set_of_closures.closure
    ~f:(fun _env closure closure_approx ->
    match A.check_approx_for_closure_allowing_unresolved closure_approx with
    | Wrong ->
      Misc.fatal_errorf "Wrong approximation when moving within set of \
          closures.  Approximation: %a  Term: %a"
        A.print closure_approx
        Flambda.print_move_within_set_of_closures move_within_set_of_closures
    | Unresolved sym ->
      [], Reachable (Move_within_set_of_closures {
          closure;
          move = move_within_set_of_closures.move;
        }),
        ret r (A.value_unresolved sym)
    | Unknown ->
      [], Reachable (Move_within_set_of_closures {
          closure;
          move = move_within_set_of_closures.move;
        }),
        ret r (A.value_unknown Other)
    | Unknown_because_of_unresolved_value value ->
      (* For example: a move upon a (move upon a closure whose .cmx file
         is missing). *)
      [], Reachable (Move_within_set_of_closures {
          closure;
          move = move_within_set_of_closures.move;
        }),
        ret r (A.value_unknown (Unresolved_value value))
    | Ok (value_closures, set_of_closures_var, set_of_closures_symbol) ->
      let () =
        match Closure_id.Map.bindings value_closures with
        | _ :: _ :: _ ->
          Format.printf "Closure approximation is not a singleton in \
              move@ %a@ %a@."
            A.print closure_approx
            Projection.print_move_within_set_of_closures
            move_within_set_of_closures
        | [] ->
          Format.printf "Closure approximation is empty in move@ %a@ %a@."
            A.print closure_approx
            Projection.print_move_within_set_of_closures
            move_within_set_of_closures
        | _ ->
          ()
      in
      (* Freshening of the move. *)
      let move, approx_map =
        Closure_id.Map.fold
          (fun closure_id_in_approx
               (value_set_of_closures:A.value_set_of_closures)
               (move, approx_map) ->
            (* Pas efficace: on refait le freshening de tout pour ne
               garder que la partie pertinente, mais n'est pas très
               grave parce que ces map sont petites (normalement) *)
            let freshened_move =
              Freshening.freshen_move_within_set_of_closures
                ~closure_freshening:value_set_of_closures.freshening
                move_within_set_of_closures.move
            in
            let start_from = closure_id_in_approx in
            let move_to =
              try Closure_id.Map.find start_from freshened_move with
              | Not_found ->
                Misc.fatal_errorf "Move %a freshened to %a does not contain \
                                   projection for %a@. Approximation is:@ %a@.\
                                   Environment:@ %a@."
                  Projection.print_move_within_set_of_closures
                    move_within_set_of_closures
                  (Closure_id.Map.print Closure_id.print) freshened_move
                  Closure_id.print start_from
                  (Closure_id.Map.print A.print_value_set_of_closures)
                    value_closures
                  E.print env
            in
            assert(not (Closure_id.Map.mem start_from move));
            Closure_id.Map.add start_from move_to move,
            Closure_id.Map.add move_to value_set_of_closures approx_map)
          value_closures (Closure_id.Map.empty, Closure_id.Map.empty)
      in
      let projection : Projection.t =
        Move_within_set_of_closures {
          closure;
          move;
        }
      in
      match Closure_id.Map.get_singleton value_closures,
            Closure_id.Map.get_singleton move with
      | None, Some _ | Some _, None ->
        (* After the freshening, move and value_closures have the same
           cardinality *)
        assert false
      | None, None ->
        let approx = A.value_closure approx_map in
        let move_within : Flambda.move_within_set_of_closures =
          { closure; move; }
        in
        [], Reachable (Move_within_set_of_closures move_within),
          ret r approx
      | Some (_start_from, value_set_of_closures),
        Some (start_from, move_to) ->
      match E.find_projection env ~projection with
      | Some var ->
        simplify_free_variable_named env var ~f:(fun _env var var_approx ->
          let r = R.map_benefit r (B.remove_projection projection) in
          [], Reachable (Var var), ret r var_approx)
      | None ->
        match reference_recursive_function_directly env move_to with
        | Some (flam, approx) -> [], Reachable flam, ret r approx
        | None ->
          if Closure_id.equal start_from move_to then
            (* Moving from one closure to itself is a no-op.  We can return an
               [Var] since we already have a variable bound to the closure. *)
            [], Reachable (Var closure), ret r closure_approx
          else
            match set_of_closures_var with
            | Some set_of_closures_var when E.mem env set_of_closures_var ->
              (* A variable bound to the set of closures is in scope,
                 meaning we can rewrite the [Move_within_set_of_closures] to a
                 [Project_closure]. *)
              let project_closure : Flambda.project_closure =
                { set_of_closures = set_of_closures_var;
                  closure_id = Closure_id.Set.singleton move_to;
                }
              in
              let approx =
                A.value_closure ~set_of_closures_var
                  (Closure_id.Map.singleton move_to value_set_of_closures)
              in
              [], Reachable (Project_closure project_closure), ret r approx
            | Some _ | None ->
              match set_of_closures_symbol with
              | Some set_of_closures_symbol ->
                let set_of_closures_var = Variable.create "symbol" in
                let project_closure : Flambda.project_closure =
                  { set_of_closures = set_of_closures_var;
                    closure_id = Closure_id.Set.singleton move_to;
                  }
                in
                let approx =
                  A.value_closure ~set_of_closures_var ~set_of_closures_symbol
                    (Closure_id.Map.singleton move_to value_set_of_closures)
                in
                let bindings : (Variable.t * Flambda.named) list = [
                  set_of_closures_var, Symbol set_of_closures_symbol;
                ]
                in
                bindings, Reachable (Project_closure project_closure),
                  ret r approx
              | None ->
                (* The set of closures is not available in scope, and we
                   have no other information by which to simplify the move. *)
                let move_within : Flambda.move_within_set_of_closures =
                  { closure; move; }
                in
                let approx = A.value_closure approx_map in
                [], Reachable (Move_within_set_of_closures move_within),
                  ret r approx)

(* Transform an expression denoting an access to a variable bound in
   a closure.  Variables in the closure ([project_var.closure]) may
   have been freshened since [expr] was constructed; as such, we
   must ensure the same happens to [expr].  The renaming information is
   contained within the approximation deduced from [closure] (as
   such, that approximation *must* identify which closure it is).

   For instance in some imaginary syntax for flambda:

     [let f x =
        let g y ~closure:{a} = a + y in
        let closure = { a = x } in
          g 12 ~closure]

   when [f] is traversed, [g] can be inlined, resulting in the
   expression

     [let f z =
        let g y ~closure:{a} = a + y in
        let closure = { a = x } in
          closure.a + 12]

   [closure.a] being a notation for:

     [Project_var{closure = closure; closure_id = g; var = a}]

   If [f] is inlined later, the resulting code will be

     [let x = ... in
      let g' y' ~closure':{a'} = a' + y' in
      let closure' = { a' = x } in
        closure'.a' + 12]

   in particular the field [a] of the closure has been alpha renamed to [a'].
   This information must be carried from the declaration to the use.

   If the function is declared outside of the alpha renamed part, there is
   no need for renaming in the [Ffunction] and [Project_var].
   This is not usually the case, except when the closure declaration is a
   symbol.

   What ensures that this information is available at [Project_var]
   point is that those constructions can only be introduced by inlining,
   which requires that same information. For this to still be valid,
   other transformation must avoid transforming the information flow in
   a way that the inline function can't propagate it.
*)
let rec simplify_project_var env r ~(project_var : Flambda.project_var) =
  simplify_free_variable_named env project_var.closure
    ~f:(fun _env closure approx ->
      match A.check_approx_for_closure_allowing_unresolved approx with
      | Ok (value_closures, _set_of_closures_var, _set_of_closures_symbol) -> begin
        let () =
          match Closure_id.Map.bindings value_closures with
           | _ :: _ :: _ ->
             Format.printf "Closure approximation is not a singleton in project@ %a@ %a@."
               A.print approx
               Projection.print_project_var project_var
           | [] ->
             Format.printf "Closure approximation is empty in project@ %a@ %a@."
               A.print approx
               Projection.print_project_var project_var
           | _ ->
             ()
        in
        (* Freshening of the projection *)
        let project_var_var, approx =
          Closure_id.Map.fold
            (fun closure_id_in_approx
              (value_set_of_closures:A.value_set_of_closures)
              (project_var_var, set_approx) ->
              let freshened_var =
                Freshening.freshen_project_var project_var.var
                  ~closure_freshening:value_set_of_closures.freshening
              in
              let closure_id = closure_id_in_approx in
              let var =
                try Closure_id.Map.find closure_id_in_approx freshened_var with
                | Not_found ->
                  Misc.fatal_errorf "When simplifying [Project_var], the \
                    closure ID %a in the approximation of the set of closures \
                    did not match any closure ID in the [Project_var] term %a \
                    freshened to %a. \
                    Approximation: %a@."
                    Closure_id.print closure_id_in_approx
                    Projection.print_project_var project_var
                    (Closure_id.Map.print Var_within_closure.print) freshened_var
                    Simple_value_approx.print approx
              in
              let set_approx =
                let approx = A.approx_for_bound_var value_set_of_closures var in
                let really_import_approx = E.really_import_approx env in
                A.join ~really_import_approx approx set_approx
              in
              Closure_id.Map.add closure_id var project_var_var,
              set_approx)
            value_closures (Closure_id.Map.empty, A.value_bottom)
        in
        let projection : Projection.t =
          Project_var {
            closure;
            var = project_var_var;
          }
        in
        begin match E.find_projection env ~projection with
        | Some var ->
          simplify_free_variable_named env var ~f:(fun _env var var_approx ->
            let r = R.map_benefit r (B.remove_projection projection) in
            [], Reachable (Var var), ret r var_approx)
        | None ->
          let expr : Flambda.named =
            Project_var { closure; var = project_var_var; }
          in
          let expr =
            match Closure_id.Map.get_singleton project_var_var with
            | None ->
              expr
            | Some (_closure_id, var) ->
              let unwrapped = Var_within_closure.unwrap var in
              if E.mem env unwrapped then
                Flambda.Var unwrapped
              else
                expr
          in
          simplify_named_using_approx_and_env env r expr approx
        end
      end
      | Unresolved value ->
        (* This value comes from a symbol for which we couldn't find any
          approximation, telling us that names within the closure couldn't
          have been renamed.  So we don't need to change the variable or
          closure ID in the [Project_var] expression. *)
        [], Reachable (Project_var { project_var with closure }),
          ret r (A.value_unresolved value)
      | Unknown ->
        [], Reachable (Project_var { project_var with closure }),
          ret r (A.value_unknown Other)
      | Unknown_because_of_unresolved_value value ->
        [], Reachable (Project_var { project_var with closure }),
          ret r (A.value_unknown (Unresolved_value value))
      | Wrong ->
        (* We must have the correct approximation of the value to ensure
          we take account of all freshenings. *)
        Misc.fatal_errorf "[Project_var] from a value with wrong \
            approximation: %a@.closure=%a@.approx of closure=%a@."
          Flambda.print_project_var project_var
          Variable.print closure
          Simple_value_approx.print approx)

(* Transforms closure definitions by applying [loop] on the code of every
   one of the set and on the expressions of the free variables.
   If the substitution is activated, alpha renaming also occur on everything
   defined by the set of closures:
   * Variables bound by a closure of the set
   * closure identifiers
   * parameters

   The rewriting occurs in a clean environment without any of the variables
   defined outside reachable.  This helps increase robustness against
   accidental, potentially unsound simplification of variable accesses by
   [simplify_using_approx_and_env].

   The rewriting occurs in an environment filled with:
   * The approximation of the free variables
   * An explicitely unknown approximation for function parameters,
     except for those where it is known to be safe: those present in the
     [specialised_args] set.
   * An approximation for the closures in the set. It contains the code of
     the functions before rewriting.

   The approximation of the currently defined closures is available to
   allow marking recursives calls as direct and in some cases, allow
   inlining of one closure from the set inside another one. For this to
   be correct an alpha renaming is first applied on the expressions by
   [apply_function_decls_and_free_vars].

   For instance when rewriting the declaration

     [let rec f_1 x_1 =
        let y_1 = x_1 + 1 in
        g_1 y_1
      and g_1 z_1 = f_1 (f_1 z_1)]

   When rewriting this function, the first substitution will contain
   some mapping:
   { f_1 -> f_2;
     g_1 -> g_2;
     x_1 -> x_2;
     z_1 -> z_2 }

   And the approximation for the closure will contain

   { f_2:
       fun x_2 ->
         let y_1 = x_2 + 1 in
         g_2 y_1
     g_2:
       fun z_2 -> f_2 (f_2 z_2) }

   Note that no substitution is applied to the let-bound variable [y_1].
   If [f_2] where to be inlined inside [g_2], we known that a new substitution
   will be introduced in the current scope for [y_1] each time.


   If the function where a recursive one coming from another compilation
   unit, the code already went through [Flambdasym] that could have
   replaced the function variable by the symbol identifying the function
   (this occur if the function contains only constants in its closure).
   To handle that case, we first replace those symbols by the original
   variable.
*)
and simplify_set_of_closures original_env r
      (set_of_closures : Flambda.set_of_closures)
      : Flambda.set_of_closures * R.t * Freshening.Project_var.t =
  let function_decls =
    let module Backend = (val (E.backend original_env) : Backend_intf.S) in
    (* CR-soon mshinwell: Does this affect
       [reference_recursive_function_directly]?
       mshinwell: This should be thought about as part of the wider issue of
       references to functions via symbols or variables. *)
    Freshening.rewrite_recursive_calls_with_symbols (E.freshening original_env)
      set_of_closures.function_decls
      ~make_closure_symbol:Backend.closure_symbol
  in
  let env = E.increase_closure_depth original_env in
  let free_vars, specialised_args, function_decls, parameter_approximations,
      internal_value_set_of_closures, set_of_closures_env =
    Inline_and_simplify_aux.prepare_to_simplify_set_of_closures ~env
      ~set_of_closures ~function_decls ~only_for_function_decl:None
      ~freshen:true
  in
  let continuation_param_uses = Continuation.Tbl.create 42 in
  let simplify_function fun_var (function_decl : Flambda.function_declaration)
        (funs, used_params, r)
        : Flambda.function_declaration Variable.Map.t * Variable.Set.t * R.t =
    let closure_env =
      Inline_and_simplify_aux.prepare_to_simplify_closure ~function_decl
        ~free_vars ~specialised_args ~parameter_approximations
        ~set_of_closures_env
    in
    let continuation_param, closure_env =
      let continuation_param, freshening =
        Freshening.add_static_exception (E.freshening closure_env)
          function_decl.continuation_param
      in
      let cont_approx =
        Continuation_approx.create_unknown ~name:continuation_param
          ~num_params:function_decl.return_arity
      in
      let closure_env =
        E.add_continuation (E.set_freshening closure_env freshening)
          continuation_param cont_approx
      in
(*
Format.eprintf "Function's return continuation renaming: %a -> %a\n%!"
  Continuation.print function_decl.continuation_param
  Continuation.print continuation_param;
*)
      continuation_param, closure_env
    in
    let body, r =
      E.enter_closure closure_env ~closure_id:(Closure_id.wrap fun_var)
        ~inline_inside:
          (Inlining_decision.should_inline_inside_declaration function_decl)
        ~dbg:function_decl.dbg
        ~f:(fun body_env ->
(*
Format.eprintf "Simplifying function body@;%a@;Environment:@;%a"
  Flambda.print function_decl.body E.print body_env;
*)
          let body, r, uses =
            let descr =
              Format.asprintf "the body of %a" Variable.print fun_var
            in
            simplify_toplevel body_env r function_decl.body
              ~continuation:continuation_param
              ~descr
          in
          Continuation.Tbl.add continuation_param_uses continuation_param uses;
          body, r)
    in
    let inline : Lambda.inline_attribute =
      match function_decl.inline with
      | Default_inline ->
        if !Clflags.classic_inlining && not function_decl.stub then
          (* In classic-inlining mode, the inlining decision is taken at
             definition site (here). If the function is small enough
             (below the -inline threshold) it will always be inlined. *)
          let inlining_threshold =
            Inline_and_simplify_aux.initial_inlining_threshold
              ~round:(E.round env)
          in
          if Inlining_cost.can_inline body inlining_threshold ~bonus:0
          then
            Always_inline
          else
            Default_inline
        else
          Default_inline
      | inline ->
        inline
    in
    let function_decl =
      Flambda.create_function_declaration ~params:function_decl.params
        ~continuation_param:continuation_param
        ~return_arity:function_decl.return_arity
        ~body ~stub:function_decl.stub ~dbg:function_decl.dbg
        ~inline ~specialise:function_decl.specialise
        ~is_a_functor:function_decl.is_a_functor
    in
    let function_decl =
      match Unrecursify.unrecursify_function ~fun_var ~function_decl with
      | None -> function_decl
      | Some function_decl -> function_decl
    in
    let used_params' = Flambda.used_params function_decl in
    Variable.Map.add fun_var function_decl funs,
      Variable.Set.union used_params used_params', r
  in
  let funs, _used_params, r =
    Variable.Map.fold simplify_function function_decls.funs
      (Variable.Map.empty, Variable.Set.empty, r)
  in
  let function_decls =
    Flambda.update_function_declarations function_decls ~funs
  in
  let function_decls, new_specialised_args =
    (* CR mshinwell: I'm not sure about this "round" condition.  It seems
       though that doing [Unbox_returns] too early may be
       detrimental, as it prevents small functions being inlined *)
    if E.never_inline env || E.round env < 2 then
      function_decls, Variable.Map.empty
    else
      let continuation_param_uses =
        Continuation.Tbl.to_map continuation_param_uses
      in
      Unbox_returns.run ~continuation_uses:continuation_param_uses
        ~function_decls ~specialised_args ~backend:(E.backend env)
  in
  let specialised_args =
    Variable.Map.disjoint_union specialised_args new_specialised_args
  in
  let invariant_params =
    lazy (Invariant_params.Functions.invariant_params_in_recursion
      function_decls ~backend:(E.backend env))
  in
  let value_set_of_closures =
    A.create_value_set_of_closures ~function_decls
      ~bound_vars:internal_value_set_of_closures.bound_vars
      ~invariant_params
      ~specialised_args:internal_value_set_of_closures.specialised_args
      ~freshening:internal_value_set_of_closures.freshening
      ~direct_call_surrogates:
        internal_value_set_of_closures.direct_call_surrogates
  in
  let direct_call_surrogates =
    Closure_id.Map.fold (fun existing surrogate surrogates ->
        Variable.Map.add (Closure_id.unwrap existing)
          (Closure_id.unwrap surrogate) surrogates)
      internal_value_set_of_closures.direct_call_surrogates
      Variable.Map.empty
  in
  let set_of_closures =
    Flambda.create_set_of_closures ~function_decls
      ~free_vars:(Variable.Map.map fst free_vars)
      ~specialised_args
      ~direct_call_surrogates
  in
  let r = ret r (A.value_set_of_closures value_set_of_closures) in
  set_of_closures, r, value_set_of_closures.freshening

and simplify_apply env r ~(apply : Flambda.apply) : Flambda.t * R.t =
  match apply.kind with
  | Function -> simplify_function_apply env r ~apply
  | Method { kind; obj; } ->
    simplify_method_call env r ~apply ~kind ~obj

and simplify_method_call env r ~(apply : Flambda.apply) ~kind ~obj =
  simplify_free_variable env obj ~f:(fun env obj _obj_approx ->
    simplify_free_variable env apply.func ~f:(fun env func _func_approx ->
      simplify_free_variables env apply.args ~f:(fun env args _args_approxs ->
        let continuation, r =
          simplify_apply_cont_to_cont env r apply.continuation
            ~args_approxs:[A.value_unknown Other]
        in
        let dbg = E.add_inlined_debuginfo env ~dbg:apply.dbg in
        let apply : Flambda.apply = {
          kind = Method { kind; obj; };
          func;
          continuation;
          args;
          call_kind = apply.call_kind;
          dbg;
          inline = apply.inline;
          specialise = apply.specialise;
        }
        in
        Apply apply, ret r (A.value_unknown Other))))

and simplify_function_apply env r ~(apply : Flambda.apply) : Flambda.t * R.t =
  let {
    Flambda. func = lhs_of_application; args; call_kind; dbg;
    inline = inline_requested; specialise = specialise_requested;
    continuation; kind;
  } = apply in
  let dbg = E.add_inlined_debuginfo env ~dbg in
(*
Format.eprintf "Simplifying function application with cont %a\n%!"
  Continuation.print continuation;
*)
(*
Format.eprintf "...freshened cont is %a\n%!"
  Continuation.print continuation;
*)
  simplify_free_variable env lhs_of_application
    ~f:(fun env lhs_of_application lhs_of_application_approx ->
      simplify_free_variables env args ~f:(fun env args args_approxs ->
        (* By using the approximation of the left-hand side of the
           application, attempt to determine which function is being applied
           (even if the application is currently [Indirect]).  If
           successful---in which case we then have a direct
           application---consider inlining. *)
        match A.check_approx_for_closure_singleton lhs_of_application_approx with
        | Ok (closure_id_being_applied, set_of_closures_var,
              set_of_closures_symbol, value_set_of_closures) ->
          let lhs_of_application, closure_id_being_applied,
                value_set_of_closures, env, wrap =
            (* If the call site is a direct call to a function that has a
               "direct call surrogate" (see inline_and_simplify_aux.mli),
               repoint the call to the surrogate. *)
            let surrogates = value_set_of_closures.direct_call_surrogates in
            match Closure_id.Map.find closure_id_being_applied surrogates with
            | exception Not_found ->
              lhs_of_application, closure_id_being_applied,
                value_set_of_closures, env, (fun expr -> expr)
            | surrogate ->
              let rec find_transitively surrogate =
                match Closure_id.Map.find surrogate surrogates with
                | exception Not_found -> surrogate
                | surrogate -> find_transitively surrogate
              in
              let surrogate = find_transitively surrogate in
              let surrogate_var =
                Variable.rename lhs_of_application ~append:"_surrogate"
              in
              let move_to_surrogate : Projection.move_within_set_of_closures =
                { closure = lhs_of_application;
                  move = Closure_id.Map.singleton closure_id_being_applied
                           surrogate;
                }
              in
              let approx_for_surrogate =
                A.value_closure ~closure_var:surrogate_var
                  ?set_of_closures_var ?set_of_closures_symbol
                  (Closure_id.Map.singleton surrogate value_set_of_closures)
              in
              let env = E.add env surrogate_var approx_for_surrogate in
              let wrap expr =
                Flambda.create_let surrogate_var
                  (Move_within_set_of_closures move_to_surrogate)
                  expr
              in
              surrogate_var, surrogate, value_set_of_closures, env, wrap
          in
          let function_decls = value_set_of_closures.function_decls in
          let function_decl =
            try
              Flambda_utils.find_declaration closure_id_being_applied
                function_decls
            with
            | Not_found ->
              Misc.fatal_errorf "When handling application expression, \
                  approximation references non-existent closure %a@."
                Closure_id.print closure_id_being_applied
          in
          let arity_of_application =
            match apply.call_kind with
            | Direct { return_arity; } -> return_arity
            | Indirect -> 1
          in
          if arity_of_application <> function_decl.return_arity then begin
            Misc.fatal_errorf "Application of %a (%a):@,function has return \
                arity %d but the application expression is expecting it \
                to have arity %d.  Function declaration is:@,%a"
              Variable.print lhs_of_application
              Variable.print_list args
              function_decl.return_arity
              arity_of_application
              Flambda.print_function_declaration
              (lhs_of_application, function_decl)
          end;
          let r =
            match apply.call_kind with
            | Indirect ->
              R.map_benefit r Inlining_cost.Benefit.direct_call_of_indirect
            | Direct _ -> r
          in
          let nargs = List.length args in
          let arity = Flambda_utils.function_arity function_decl in
          let result, r =
            if nargs = arity then
              simplify_full_application env r ~function_decls
                ~lhs_of_application ~closure_id_being_applied ~function_decl
                ~value_set_of_closures ~args ~args_approxs ~continuation ~dbg
                ~inline_requested ~specialise_requested
            else if nargs > arity then
              simplify_over_application env r ~args ~args_approxs
                ~continuation ~function_decls ~lhs_of_application
                ~closure_id_being_applied ~function_decl ~value_set_of_closures
                ~dbg ~inline_requested ~specialise_requested
            else if nargs > 0 && nargs < arity then
              simplify_partial_application env r ~lhs_of_application
                ~closure_id_being_applied ~function_decl ~args
                ~continuation ~dbg ~inline_requested ~specialise_requested
            else
              Misc.fatal_errorf "Function with arity %d when simplifying \
                  application expression: %a"
                arity Flambda.print (Flambda.Apply apply)
          in
(*
let used_conts = R.continuation_uses r in
Format.eprintf "After simplifying application of %a to %a, r contains:\n@ %a\n%!"
  Variable.print lhs_of_application
  Variable.print_list args
  (Continuation.Map.print
    Inline_and_simplify_aux.Continuation_uses.print) used_conts;
let joins =
  Continuation.Map.map (fun uses ->
    Inline_and_simplify_aux.Continuation_uses.meet_of_args_approxs uses
      ~num_params:0)
    used_conts
in
Format.eprintf "Continuation args join:\n@ %a\n%!"
  (Continuation.Map.print
    (Format.pp_print_list A.print)) joins;
*)
          wrap result, r
        | Wrong ->  (* Insufficient approximation information to simplify. *)
          let args_approxs =
            match call_kind with
            | Indirect -> [A.value_unknown Other]
            | Direct { return_arity; _ }
                when E.less_precise_approximations env ->
              Array.to_list (Array.init return_arity (fun _ ->
                A.value_unknown Other))
            | Direct _ ->
              Misc.fatal_errorf "Application of function %a (%a) is marked as \
                  a direct call but the approximation of the function was \
                  wrong: %a@ \nEnvironment:@ %a\n%!"
                Variable.print lhs_of_application
                Variable.print_list args
                A.print lhs_of_application_approx
                E.print env
          in
          let continuation, r =
            simplify_apply_cont_to_cont env r continuation ~args_approxs
          in
          let call_kind : Flambda.call_kind =
            if E.less_precise_approximations env then call_kind
            else Indirect
          in
          Apply ({ kind; func = lhs_of_application; args; call_kind;
              dbg; inline = inline_requested; specialise = specialise_requested;
              continuation; }),
            ret r (A.value_unknown Other)))

and simplify_full_application env r ~function_decls ~lhs_of_application
      ~closure_id_being_applied ~function_decl ~value_set_of_closures ~args
      ~args_approxs ~continuation ~dbg ~inline_requested ~specialise_requested =
  Inlining_decision.for_call_site ~env ~r ~function_decls
    ~lhs_of_application ~closure_id_being_applied ~function_decl
    ~value_set_of_closures ~args ~args_approxs ~continuation ~dbg ~simplify
    ~simplify_apply_cont_to_cont ~inline_requested ~specialise_requested

and simplify_partial_application env r ~lhs_of_application
      ~closure_id_being_applied
      ~(function_decl : Flambda.function_declaration) ~args ~continuation ~dbg
      ~inline_requested ~specialise_requested =
(*
  let continuation, r =
    let args_approxs =
      Array.to_list (Array.init function_decl.return_arity
        (fun _index -> A.value_unknown Other))
    in
    simplify_apply_cont_to_cont env r continuation
      ~args_approxs
  in
*)
  let arity = Flambda_utils.function_arity function_decl in
  assert (arity > List.length args);
  (* For simplicity, we disallow [@inline] attributes on partial
     applications.  The user may always write an explicit wrapper instead
     with such an attribute. *)
  (* CR-someday mshinwell: Pierre noted that we might like a function to be
     inlined when applied to its first set of arguments, e.g. for some kind
     of type class like thing. *)
  begin match (inline_requested : Lambda.inline_attribute) with
  | Always_inline | Never_inline ->
    Location.prerr_warning (Debuginfo.to_location dbg)
      (Warnings.Inlining_impossible "[@inlined] attributes may not be used \
        on partial applications")
  | Unroll _ ->
    Location.prerr_warning (Debuginfo.to_location dbg)
      (Warnings.Inlining_impossible "[@unroll] attributes may not be used \
        on partial applications")
  | Default_inline -> ()
  end;
  begin match (specialise_requested : Lambda.specialise_attribute) with
  | Always_specialise | Never_specialise ->
    Location.prerr_warning (Debuginfo.to_location dbg)
      (Warnings.Inlining_impossible "[@specialised] attributes may not be used \
        on partial applications")
  | Default_specialise -> ()
  end;
  let freshened_params =
    List.map (fun id -> Variable.rename id) function_decl.Flambda.params
  in
  let applied_args, remaining_args =
    Misc.Stdlib.List.map2_prefix (fun arg id' -> id', arg)
      args freshened_params
  in
  let wrapper_continuation_param = Continuation.create () in
  let wrapper_accepting_remaining_args =
    let body : Flambda.t =
      Apply {
        kind = Function;
        continuation = wrapper_continuation_param;
        func = lhs_of_application;
        args = freshened_params;
        call_kind = Direct {
          closure_id = closure_id_being_applied;
          return_arity = function_decl.return_arity;
        };
        dbg;
        inline = Default_inline;
        specialise = Default_specialise;
      }
    in
    let closure_variable =
      Variable.rename
        ~append:"_partial_fun"
        (Closure_id.unwrap closure_id_being_applied)
    in
    Flambda_utils.make_closure_declaration ~id:closure_variable
      ~body
      ~params:remaining_args
      ~stub:true
      ~continuation_param:wrapper_continuation_param
      ~continuation
  in
  let with_known_args =
    Flambda_utils.bind
      ~bindings:(List.map (fun (var, arg) ->
          var, Flambda.Var arg) applied_args)
      ~body:wrapper_accepting_remaining_args
  in
  simplify env r with_known_args

and simplify_over_application env r ~args ~args_approxs ~continuation
      ~function_decls ~lhs_of_application ~closure_id_being_applied
      ~(function_decl : Flambda.function_declaration) ~value_set_of_closures
      ~dbg ~inline_requested ~specialise_requested =
  let continuation, r =
    let args_approxs =
      Array.to_list (Array.init function_decl.return_arity
        (fun _index -> A.value_unknown Other))
    in
    simplify_apply_cont_to_cont env r continuation
      ~args_approxs
  in
  let arity = Flambda_utils.function_arity function_decl in
  assert (arity < List.length args);
  assert (List.length args = List.length args_approxs);
  let full_app_args, remaining_args =
    Misc.Stdlib.List.split_at arity args
  in
  let full_app_approxs, _ =
    Misc.Stdlib.List.split_at arity args_approxs
  in
  let func_var = Variable.create "full_apply" in
  let handler : Flambda.continuation_handler =
    { stub = false;
      is_exn_handler = false;
      params = [func_var];
      handler =
        Apply {
          kind = Function;
          continuation;
          func = func_var;
          args = remaining_args;
          call_kind = Indirect;
          dbg;
          inline = inline_requested;
          specialise = specialise_requested;
        };
      specialised_args = Variable.Map.empty;
    }
  in
  let after_full_application = Continuation.create () in
  let after_full_application_approx =
    Continuation_approx.create ~name:after_full_application
      ~handlers:(Nonrecursive handler) ~num_params:1
  in
  let full_application, r =
    let env =
      E.add_continuation env after_full_application
        after_full_application_approx
    in
    simplify_full_application env r ~function_decls ~lhs_of_application
      ~closure_id_being_applied ~function_decl ~value_set_of_closures
      ~args:full_app_args ~args_approxs:full_app_approxs
      ~continuation:after_full_application ~dbg ~inline_requested
      ~specialise_requested
  in
(*
Format.eprintf "full_application:@;%a@;" Flambda.print full_application;
*)
  (* CR mshinwell: Maybe it would be better just to build a proper term
     including the full application as a normal Apply node and call simplify
     on that? *)
  let r, after_full_application_uses =
    R.exit_scope_catch r env after_full_application
  in
  let r =
    R.define_continuation r after_full_application env Nonrecursive
      after_full_application_uses after_full_application_approx
  in
  let expr : Flambda.t =
    Let_cont {
      body = full_application;
      handlers = Nonrecursive {
        name = after_full_application;
        handler;
      };
    }
  in
  expr, r

(** Simplify an application of a continuation. *)
and simplify_apply_cont env r cont ~(trap_action : Flambda.trap_action option)
      ~args ~args_approxs : Flambda.t * R.t =
(*let orig_cont = cont in*)
  let cont = Freshening.apply_static_exception (E.freshening env) cont in
(*
Format.eprintf "APPLICATION of %a (was %a)\n%!" Continuation.print cont
  Continuation.print orig_cont;
*)
  let cont_approx = E.find_continuation env cont in
  let cont = Continuation_approx.name cont_approx in
  let freshen_trap_action env r (trap_action : Flambda.trap_action) =
    match trap_action with
    | Push { id; exn_handler; } ->
      let id = Freshening.apply_trap (E.freshening env) id in
      let exn_handler, r =
        simplify_apply_cont_to_cont env r exn_handler
          ~args_approxs:[A.value_unknown Other]
      in
      Flambda.Push { id; exn_handler; }, r
    | Pop { id; exn_handler; } ->
      let id = Freshening.apply_trap (E.freshening env) id in
      let exn_handler, r =
        simplify_apply_cont_to_cont env r exn_handler
          ~args_approxs:[A.value_unknown Other]
      in
      Flambda.Pop { id; exn_handler; }, r
  in
  match Continuation_approx.handlers cont_approx with
  | Some (Nonrecursive handler) when handler.stub && trap_action = None ->
    (* Stubs are unconditionally inlined out now so that we don't need to run
       the second [Continuation_inlining] pass when doing a "noinline" run
       of [Inline_and_simplify].
       Note that we don't call [R.use_continuation] here, because we're going
       to eliminate the use. *)
    let env = E.activate_freshening env in
    let env = E.disallow_continuation_inlining (E.set_never_inline env) in
    let params, freshening =
      Freshening.add_variables' (E.freshening env) handler.params
    in
    let params_and_approxs = List.combine params args_approxs in
    let env =
      List.fold_left (fun env (param, arg_approx) ->
          E.add env param arg_approx)
        (E.set_freshening env freshening)
        params_and_approxs
    in
(*Format.eprintf "Inlining stub: %a\n%!" Continuation.print cont;*)
    let stub's_body : Flambda.expr =
      match trap_action with
      | None -> handler.handler
      | Some trap_action ->
        let new_cont = Continuation.create () in
        Let_cont {
          body = Apply_cont (new_cont, Some trap_action, []);
          handlers = Nonrecursive {
            name = new_cont;
            handler = {
              handler = handler.handler;
              params = [];
              stub = false;
              is_exn_handler = false;
              specialised_args = Variable.Map.empty;
            };
          };
        }
    in
    simplify env r stub's_body
  | Some _ | None ->
(*
Format.eprintf "Recording use of %a in Apply_cont with approxs: %a\n%!"
  Continuation.print cont
  (Format.pp_print_list A.print) args_approxs;
*)
    let r =
      let kind : Inline_and_simplify_aux.Continuation_uses.Use.Kind.t =
        let args_and_approxs = List.combine args args_approxs in
        match trap_action with
        | None -> Inlinable_and_specialisable args_and_approxs
        | Some _ -> Only_specialisable args_and_approxs
      in
      R.use_continuation r env cont kind
    in
    let trap_action, r =
      match trap_action with
      | None -> None, r
      | Some trap_action ->
        let trap_action, r = freshen_trap_action env r trap_action in
        Some trap_action, r
    in
    Apply_cont (cont, trap_action, args), ret r (A.value_unknown Other)

(** Simplify an application of a continuation for a context where only a
    continuation is valid (e.g. a switch arm) and there are no opportunities
    for inlining or specialisation. *)
and simplify_apply_cont_to_cont env r cont ~args_approxs =
  let cont = Freshening.apply_static_exception (E.freshening env) cont in
  let cont_approx = E.find_continuation env cont in
  let cont = Continuation_approx.name cont_approx in
  let r =
    R.use_continuation r env cont (Not_inlinable_or_specialisable args_approxs)
  in
  cont, ret r (A.value_unknown Other)

(** [simplify_named] returns:
    - extra [Let]-bindings to be inserted prior to the one being simplified;
    - the simplified [named];
    - the new result environment. *)
and simplify_named env r (tree : Flambda.named)
      : (Variable.t * Flambda.named) list * Flambda.named_reachable
          * R.t =
  match tree with
  | Var var ->
    let var = Freshening.apply_variable (E.freshening env) var in
    (* If from the approximations we can simplify [var], then we will be
       forced to insert [let]-expressions to bind a [named].  This has an
       important consequence: it brings bindings of constants closer to their
       use points. *)
    simplify_named_using_approx_and_env env r (Var var) (E.find_exn env var)
  | Symbol sym ->
    (* New Symbol construction could have been introduced during
       transformation (by simplify_named_using_approx_and_env).
       When this comes from another compilation unit, we must load it. *)
    let approx = E.find_or_load_symbol env sym in
    simplify_named_using_approx r tree approx
  | Const cst -> [], Reachable tree, ret r (approx_for_const cst)
  | Allocated_const cst ->
    [], Reachable tree, ret r (approx_for_allocated_const cst)
  | Read_mutable mut_var ->
    (* See comment on the [Assign] case. *)
    let mut_var =
      Freshening.apply_mutable_variable (E.freshening env) mut_var
    in
    [], Reachable (Read_mutable mut_var), ret r (A.value_unknown Other)
  | Read_symbol_field (symbol, field_index) ->
    let approx = E.find_or_load_symbol env symbol in
    begin match A.get_field approx ~field_index with
    (* CR-someday mshinwell: Think about [Unreachable] vs. [Bottom]. *)
    | Unreachable -> [], Unreachable, r
    | Ok approx ->
      let approx = A.augment_with_symbol_field approx symbol field_index in
      simplify_named_using_approx_and_env env r tree approx
    end
  | Set_of_closures set_of_closures -> begin
    let backend = E.backend env in
    let cont_usage_snapshot = R.snapshot_continuation_uses r in
    let set_of_closures, r, first_freshening =
      simplify_set_of_closures env r set_of_closures
    in
    let simplify env r ~bindings ~set_of_closures ~pass_name =
      (* If simplifying a set of closures more than once during any given round
         of simplification, the [Freshening.Project_var] substitutions arising
         from each call to [simplify_set_of_closures] must be composed.
         Note that this function only composes with [first_freshening] owing
         to the structure of the code below (this new [simplify] is always
         in tail position).
         We also need to be careful not to double-count (or worse) uses of
         continuations. *)
      (* CR-someday mshinwell: It was mooted that maybe we could try
         structurally-typed closures (i.e. where we would never rename the
         closure elements), or something else, to try to remove
         the "closure freshening" thing in the approximation which is hard
         to deal with. *)
      let r = R.roll_back_continuation_uses r cont_usage_snapshot in
      let bindings, set_of_closures, r =
        let env = E.set_never_inline env in
        simplify_newly_introduced_let_bindings env r ~bindings
          ~around:((Set_of_closures set_of_closures) : Flambda.named)
      in
      let approx = R.approx r in
      let value_set_of_closures =
        match A.strict_check_approx_for_set_of_closures approx with
        | Wrong ->
          Misc.fatal_errorf "Unexpected approximation returned from \
              simplification of [%s] result: %a"
            pass_name A.print approx
        | Ok (_var, value_set_of_closures) ->
          let freshening =
            Freshening.Project_var.compose ~earlier:first_freshening
              ~later:value_set_of_closures.freshening
          in
          A.update_freshening_of_value_set_of_closures value_set_of_closures
            ~freshening
      in
      bindings, set_of_closures,
        (ret r (A.value_set_of_closures value_set_of_closures))
    in
    (* This does the actual substitutions of specialised args introduced
       by [Unbox_closures] for free variables.  (Apart from simplifying
       the [Unbox_closures] output, this also prevents applying
       [Unbox_closures] over and over.) *)
    let set_of_closures =
      match Remove_free_vars_equal_to_args.run set_of_closures with
      | None -> set_of_closures
      | Some set_of_closures -> set_of_closures
    in
    (* Do [Unbox_closures] next to try to decide which things are
       free variables and which things are specialised arguments before
       unboxing them. *)
    match
      Unbox_closures.rewrite_set_of_closures ~env
        ~duplicate_function ~set_of_closures
    with
    | Some (bindings, set_of_closures, benefit) ->
      let r = R.add_benefit r benefit in
      simplify env r ~bindings ~set_of_closures ~pass_name:"Unbox_closures"
    | None ->
      match Unbox_free_vars_of_closures.run ~env ~set_of_closures with
      | Some (bindings, set_of_closures, benefit) ->
        let r = R.add_benefit r benefit in
        simplify env r ~bindings ~set_of_closures
          ~pass_name:"Unbox_free_vars_of_closures"
      | None ->
        (* CR-soon mshinwell: should maybe add one allocation for the
           stub *)
        match
          Unbox_specialised_args.rewrite_set_of_closures ~env
            ~duplicate_function ~set_of_closures
        with
        | Some (bindings, set_of_closures, benefit) ->
          let r = R.add_benefit r benefit in
          simplify env r ~bindings ~set_of_closures
            ~pass_name:"Unbox_specialised_args"
        | None ->
          match
            Remove_unused_arguments.
                separate_unused_arguments_in_set_of_closures
              set_of_closures ~backend
          with
          | Some set_of_closures ->
            simplify env r ~bindings:[] ~set_of_closures
              ~pass_name:"Remove_unused_arguments"
          | None ->
                [], Reachable (Set_of_closures set_of_closures), r
    end
  | Project_closure project_closure ->
    simplify_project_closure env r ~project_closure
  | Project_var project_var -> simplify_project_var env r ~project_var
  | Move_within_set_of_closures move_within_set_of_closures ->
    simplify_move_within_set_of_closures env r ~move_within_set_of_closures
  | Assign { being_assigned; new_value; } ->
    (* No need to use something like [simplify_free_variable]: the
       approximation of [being_assigned] is always unknown. *)
    let being_assigned =
      Freshening.apply_mutable_variable (E.freshening env) being_assigned
    in
    simplify_free_variable_named env new_value ~f:(fun _env new_value _approx ->
      [], Reachable (Assign { being_assigned; new_value; }),
        ret r (A.value_unknown Other))
  | Prim (prim, args, dbg) ->
    let dbg = E.add_inlined_debuginfo env ~dbg in
    simplify_free_variables_named env args ~f:(fun env args args_approxs ->
      let tree = Flambda.Prim (prim, args, dbg) in
      let projection : Projection.t = Prim (prim, args) in
      begin match E.find_projection env ~projection with
      | Some var ->
        (* CSE of pure primitives.
           The [Pisint] case in particular is also used when unboxing
           continuation parameters of variant type. *)
        simplify_free_variable_named env var ~f:(fun _env var var_approx ->
          let r = R.map_benefit r (B.remove_projection projection) in
          [], Reachable (Var var), ret r var_approx)
      | None ->
        let default () : (Variable.t * Flambda.named) list
              * Flambda.named_reachable * R.t =
          let named, approx, benefit =
            let module Backend = (val (E.backend env) : Backend_intf.S) in
            Simplify_primitives.primitive prim (args, args_approxs) tree dbg
              ~size_int:Backend.size_int ~big_endian:Backend.big_endian
          in
          let r = R.map_benefit r (B.(+) benefit) in
          let approx =
            match prim with
            | Popaque -> A.value_unknown Other
            | _ -> approx
          in
          [], Reachable named, ret r approx
        in
        begin match prim, args, args_approxs with
        | Pgetglobal _, _, _ ->
          Misc.fatal_error "Pgetglobal is forbidden in Inline_and_simplify"
        | Pfield field_index, [arg], [arg_approx] ->
          let projection : Projection.t = Field (field_index, arg) in
          begin match E.find_projection env ~projection with
          | Some var ->
            simplify_free_variable_named env var ~f:(fun _env var var_approx ->
              let r = R.map_benefit r (B.remove_projection projection) in
              [], Reachable (Var var), ret r var_approx)
          | None ->
            begin match A.get_field arg_approx ~field_index with
            | Unreachable ->
(*
Format.eprintf "get_field %d from %a returns Unreachable (approx %a)\n%!"
  field_index Variable.print arg A.print arg_approx;
*)
              [], Unreachable, r
            | Ok approx ->
              let tree, approx =
                match arg_approx.symbol with
                (* If the [Pfield] is projecting directly from a symbol, rewrite
                   the expression to [Read_symbol_field]. *)
                | Some (symbol, None) ->
                  let approx =
                    A.augment_with_symbol_field approx symbol field_index
                  in
                  Flambda.Read_symbol_field (symbol, field_index), approx
                | None | Some (_, Some _ ) ->
                  (* This [Pfield] is either not projecting from a symbol at
                     all, or it is the projection of a projection from a
                     symbol. *)
                  let approx' = E.really_import_approx env approx in
                  tree, approx'
              in
              simplify_named_using_approx_and_env env r tree approx
            end
          end
        | Pfield _, _, _ -> Misc.fatal_error "Pfield arity error"
        | (Parraysetu kind | Parraysets kind),
            [_block; _field; _value],
            [block_approx; _field_approx; value_approx] ->
          if A.is_definitely_immutable block_approx then begin
            Location.prerr_warning (Debuginfo.to_location dbg)
              Warnings.Assignment_to_non_mutable_value
          end;
          let kind =
            match A.descr block_approx, A.descr value_approx with
            | (Float_array _, _)
            | (_, Float _) ->
              begin match kind with
              | Pfloatarray | Pgenarray -> ()
              | Paddrarray | Pintarray ->
                (* CR pchambart: Do a proper warning here *)
                Misc.fatal_errorf "Assignment of a float to a specialised \
                                  non-float array: %a"
                  Flambda.print_named tree
              end;
              Lambda.Pfloatarray
              (* CR pchambart: This should be accounted by the benefit *)
            | _ ->
              kind
          in
          let prim : Lambda.primitive =
            match prim with
            | Parraysetu _ -> Parraysetu kind
            | Parraysets _ -> Parraysets kind
            | _ -> assert false
          in
          [], Reachable (Prim (prim, args, dbg)), ret r (A.value_unknown Other)
        | Psetfield _, _block::_, block_approx::_ ->
          if A.is_definitely_immutable block_approx then begin
            Location.prerr_warning (Debuginfo.to_location dbg)
              Warnings.Assignment_to_non_mutable_value
          end;
          [], Reachable tree, ret r (A.value_unknown Other)
        | (Psetfield _ | Parraysetu _ | Parraysets _), _, _ ->
          Misc.fatal_error "Psetfield / Parraysetu / Parraysets arity error"
        | Pisint, [_arg], [arg_approx] ->
          begin match A.check_approx_for_block_or_immediate arg_approx with
          | Wrong -> default ()
          | Immediate ->
            let r = R.map_benefit r B.remove_prim in
            let const_true = Variable.create "true" in
            [const_true, Const (Int 1)], Reachable (Var const_true),
              ret r (A.value_int 1)
          | Block ->
            let r = R.map_benefit r B.remove_prim in
            let const_false = Variable.create "false" in
            [const_false, Const (Int 0)], Reachable (Var const_false),
              ret r (A.value_int 0)
          end
        | Pisint, _, _ -> Misc.fatal_error "Pisint arity error"
        | Pgettag, [_arg], [arg_approx] ->
          begin match A.check_approx_for_block arg_approx with
          | Wrong -> default ()
          | Ok (tag, _fields) ->
            let r = R.map_benefit r B.remove_prim in
            let const_tag = Variable.create "tag" in
            let tag = Tag.to_int tag in
            [const_tag, Const (Int tag)], Reachable (Var const_tag),
              ret r (A.value_int tag)
          end
        | Pgettag, _, _ -> Misc.fatal_error "Pgettag arity error"
        | (Psequand | Psequor), _, _ ->
          Misc.fatal_error "Psequand and Psequor must be expanded (see \
              handling in closure_conversion.ml)"
        | _, _, _ -> default ()
        end
      end)

(** Simplify a set of [Let]-bindings introduced by a pass such as
    [Unbox_specialised_args] surrounding the term [around] that is in turn
    the defining expression of a [Let].  This is like simplifying a fragment
    of a context:

      let x0 = ... in
      ...
      let xn = ... in
      let var = around in  (* this is the original [Let] being simplified *)
      <hole>

    (In this example, [bindings] would map [x0] through [xn].)
*)
and simplify_newly_introduced_let_bindings env r ~bindings
      ~(around : Flambda.named) =
  let bindings, env, r, _stop =
    List.fold_left (fun ((bindings, env, r, stop) as acc)
            (var, defining_expr) ->
        if stop then
          acc
        else
          let (env, r), new_bindings, var, defining_expr =
            for_defining_expr_of_let (env, r) var defining_expr
          in
          match (defining_expr : Flambda.named_reachable) with
          | Reachable defining_expr ->
            let bindings =
              (var, defining_expr) :: (List.rev new_bindings) @ bindings
            in
            bindings, env, r, false
          | Non_terminating defining_expr ->
            let bindings =
              (var, defining_expr) :: (List.rev new_bindings) @ bindings
            in
            bindings, env, r, true
          | Unreachable ->
            let bindings = (List.rev new_bindings) @ bindings in
            bindings, env, r, true)
      ([], env, r, false)
      bindings
  in
  let new_bindings, around, r = simplify_named env r around in
  let around_fvs =
    match around with
    | Reachable around
    | Non_terminating around -> Flambda.free_variables_named around
    | Unreachable -> Variable.Set.empty
  in
  let bindings, r, _fvs =
    List.fold_left (fun (bindings, r, fvs) (var, defining_expr) ->
        let r, var, defining_expr =
          filter_defining_expr_of_let r var defining_expr fvs
        in
        match defining_expr with
        | Some defining_expr ->
          let fvs =
            Variable.Set.union (Flambda.free_variables_named defining_expr)
              (Variable.Set.remove var fvs)
          in
          (var, defining_expr)::bindings, r, fvs
        | None ->
          bindings, r, fvs)
      ([], r, around_fvs)
      ((List.rev new_bindings) @ bindings)
  in
  bindings, around, r

and for_defining_expr_of_let (env, r) var defining_expr =
  let new_bindings, defining_expr, r = simplify_named env r defining_expr in
  let defining_expr : Flambda.named_reachable =
    match defining_expr with
    | Non_terminating _ | Unreachable -> defining_expr
    | Reachable defining_expr ->
      (* Cause subsequent code to be deleted if the evaluation of this
         let's defining expression doesn't terminate. *)
      if A.is_bottom (R.approx r) then Non_terminating defining_expr
      else Reachable defining_expr
  in
  let var, sb = Freshening.add_variable (E.freshening env) var in
  let env = E.set_freshening env sb in
  let env = E.add env var (R.approx r) in
  (env, r), new_bindings, var, defining_expr

and filter_defining_expr_of_let r var (defining_expr : Flambda.named)
      free_vars_of_body =
  if Variable.Set.mem var free_vars_of_body then
    r, var, Some defining_expr
  else if Effect_analysis.no_effects_named defining_expr then
    match defining_expr with
    | Set_of_closures _ ->
      (* Don't delete closure definitions: there might be a reference to them
         (propagated through approximations) that is not in scope. *)
      r, var, Some defining_expr
    | _ ->
      let r = R.map_benefit r (B.remove_code_named defining_expr) in
      r, var, None
  else
    r, var, Some defining_expr

and simplify_let_cont_handler ~env ~r ~cont
      ~(handler : Flambda.continuation_handler) ~args_approxs =
(*
Format.eprintf "Handler of %a has args_approxs (%a)\n%!"
  Continuation.print cont
  (Format.pp_print_list A.print) args_approxs;
*)
  let { Flambda. params = vars; stub; is_exn_handler; handler;
    specialised_args; } = handler
  in
  (* CR mshinwell: rename "vars" to "params" *)
  let freshened_vars, sb =
    Freshening.add_variables' (E.freshening env) vars
  in
(*
Format.eprintf "simplify_let_cont_handler %a (params %a, freshened params %a)\n%!"
  Continuation.print cont
  Variable.print_list vars
  Variable.print_list freshened_vars;
*)
  if List.length vars <> List.length args_approxs then begin
    Misc.fatal_errorf "simplify_let_cont_handler (%a): params are %a but \
        args_approxs has length %d"
      Continuation.print cont
      Variable.print_list vars
      (List.length args_approxs)
  end;
  let freshened_params_to_args_approxs =
    let params_to_args_approxs = List.combine vars args_approxs in
    let freshened_params_to_args_approxs =
      List.map (fun (param, approx) ->
          Freshening.apply_variable sb param, approx)
        params_to_args_approxs
    in
    Variable.Map.of_list freshened_params_to_args_approxs
  in
  let specialised_args =
    let specialised_args =
      Variable.Map.map_keys (Freshening.apply_variable sb) specialised_args
    in
    let specialised_args =
      (* CR mshinwell: Duplicate of a part of
          [Inline_and_simplify_aux.prepare_to_simplify_set_of_closures]
      *)
      Variable.Map.map (fun (spec_to : Flambda.specialised_to) ->
          match spec_to.var with
          | Some external_var ->
            let var =
              Freshening.apply_variable sb external_var
            in
            let var =
              match
                A.simplify_var_to_var_using_env (E.find_exn env var)
                  ~is_present_in_env:(fun var -> E.mem env var)
              with
              | None -> var
              | Some var -> var
            in
            let projection = spec_to.projection in
            ({ var = Some var; projection; } : Flambda.specialised_to)
          | None ->
            spec_to)
        specialised_args
    in
    Freshening.freshen_specialised_args_projection_relation
      specialised_args
      ~freshening:sb
      ~closure_freshening:None
  in
  let param_approxs =
    List.map (fun param ->
        let not_specialised () =
          match Variable.Map.find param freshened_params_to_args_approxs with
          | exception Not_found -> assert false
          | arg_approx -> arg_approx
        in
        match Variable.Map.find param specialised_args with
        | exception Not_found -> not_specialised ()
        | spec_to ->
          match spec_to.var with
          | None -> not_specialised ()
          (* CR mshinwell: Maybe this should do a *meet* (not a join) with
             the args_approxs, in the specialised args case *)
          | Some var -> E.find_exn env var)
      freshened_vars
  in
  let vars = freshened_vars in
  let params_and_approxs = List.combine vars param_approxs in
  let env =
    List.fold_left (fun env (id, approx) -> E.add env id approx)
      (E.set_freshening env sb) params_and_approxs
  in
  let env =
    Variable.Map.fold (fun param (spec_to : Flambda.specialised_to)
            env ->
        match spec_to.projection with
        | None -> env
        | Some projection ->
          E.add_projection env ~projection ~bound_to:param)
      specialised_args
      env
  in
  let handler, r = simplify (E.inside_branch env) r handler in
  let specialised_args =
    Variable.Map.filter_map specialised_args
      ~f:(fun _param (spec_to : Flambda.specialised_to) ->
        match spec_to.var, spec_to.projection with
        | None, None -> None
        | _ -> Some spec_to)
  in
  let handler : Flambda.continuation_handler =
    { params = vars;
      stub;
      is_exn_handler;
      handler;
      specialised_args;
    }
  in
  r, handler

and simplify_let_cont_handlers ~env ~r ~handlers ~args_approxs
      ~(recursive : Asttypes.rec_flag) ~freshening ~update_use_env
      : Flambda.let_cont_handlers option * R.t =
  (* If none of the handlers are used in the body, delete them all. *)
  let all_unused =
    Continuation.Map.for_all (fun cont _handler ->
        let cont = Freshening.apply_static_exception freshening cont in
        R.continuation_unused r cont)
      handlers
  in
  (* CR mshinwell: we should enhance the deletion of continuations so it
     can get rid of stubs inside recursive bindings *)
  if all_unused then begin
(*
Format.eprintf "Deleting handlers binding %a\n%!"
  Continuation.Set.print (Continuation.Map.keys handlers);
*)
    None, r
  end else
    (* First we simplify the continuations themselves.  We also remember
       which continuations were added to [r] whilst simplifying each handler,
       so if we delete one or more of the handlers, we can also update [r]
       accordingly. *)
    let r, handlers =
      Continuation.Map.fold (fun cont
                (handler : Flambda.continuation_handler) (r, handlers) ->
          let cont' = Freshening.apply_static_exception freshening cont in
          let cont_snapshot_before = R.snapshot_continuation_uses r in
          let args_approxs =
            let unknown () =
              Array.to_list (Array.init (List.length handler.params)
                (fun _ -> A.value_unknown Other))
            in
            match args_approxs with
            | None ->
              begin match recursive with
              | Recursive -> unknown ()
              | Nonrecursive ->
                R.continuation_args_approxs r cont'
                  ~num_params:(List.length handler.params)
              end
            | Some args_approxs ->
              begin match Continuation.Map.find cont args_approxs with
              | exception Not_found ->
                (* A new continuation introduced by
                   [Unbox_continuation_params] (see below). *)
                (* CR mshinwell: maybe we should enforce that? *)
                unknown ()
              | args_approxs ->
                assert (List.length handler.params = List.length args_approxs);
                args_approxs
              end
          in
          let r, handler =
(*
Format.eprintf "Simplifying handler for %a:@ \n%a\n%!"
  Continuation.print cont Flambda.print ((handler : Flambda.continuation_handler).handler);
*)
            simplify_let_cont_handler ~env ~r ~cont:cont' ~handler
              ~args_approxs
          in
          let cont_snapshot_after = R.snapshot_continuation_uses r in
          let introduced_conts =
            Inline_and_simplify_aux.Continuation_usage_snapshot.
              continuations_defined_between_snapshots
              ~before:cont_snapshot_before ~after:cont_snapshot_after
          in
(*
Format.eprintf "New handler for %a is:@ \n%a\n%!"
  Continuation.print cont Flambda.print ((handler : Flambda.continuation_handler).handler);
*)
          r, Continuation.Map.add cont' (handler, introduced_conts) handlers)
        handlers
        (r, Continuation.Map.empty)
    in
    (* Then we collect uses of the continuations and delete any unused ones.
       The usage information will subsequently be used by the continuation
       inlining and specialisation transformations. *)
    let r, handlers =
      Continuation.Map.fold (fun cont
              ((handler : Flambda.continuation_handler), introduced_conts)
              (r, handlers) ->
          let r, uses =
            R.exit_scope_catch ~update_use_env r env cont
          in
          if Inline_and_simplify_aux.Continuation_uses.unused uses then begin
(*Format.eprintf "Removing %a\n%!" Continuation.print cont;*)
            let handlers = Continuation.Map.remove cont handlers in
            let r = R.forget_continuation_definition r cont in
            let r =
              Continuation.Set.fold (fun cont r ->
                  R.forget_continuation_definition r cont)
                introduced_conts
                r
            in
            r, handlers
          end else begin
(*Format.eprintf "Defining %a\n%!" Continuation.print cont;*)
            let approx =
              let num_params = List.length handler.params in
              let handlers : Continuation_approx.continuation_handlers =
                match recursive with
                | Nonrecursive ->
                  begin match Continuation.Map.bindings handlers with
                  | [_cont, (handler, _)] -> Nonrecursive handler
                  | _ -> assert false
                  end
                | Recursive ->
                  let handlers =
                    Continuation.Map.map (fun (handler, _) -> handler)
                      handlers
                  in
                  Recursive handlers
              in
              Continuation_approx.create ~name:cont ~handlers ~num_params
            in
            let r = R.define_continuation r cont env recursive uses approx in
            r, handlers
          end)
        handlers
        (r, handlers)
    in
    let handlers =
      Continuation.Map.map (fun (handler, _) -> handler)
        handlers
    in
    if Continuation.Map.is_empty handlers then begin
(*Format.eprintf "No handlers left!\n%!";*)
      None, r
    end else
      match recursive with
      | Nonrecursive ->
        begin match Continuation.Map.bindings handlers with
        | [name, handler] -> Some (Flambda.Nonrecursive { name; handler; }), r
        | _ ->
          Misc.fatal_errorf "Nonrecursive Let_cont may only have one handler"
        end
      | Recursive ->
        let is_non_recursive =
          if Continuation.Map.cardinal handlers > 1 then None
          else
            match Continuation.Map.bindings handlers with
            | [name, (handler : Flambda.continuation_handler)] ->
              let fcs = Flambda.free_continuations handler.handler in
              if not (Continuation.Set.mem name fcs) then
                Some (name, handler)
              else
                None
            | _ -> None
        in
        match is_non_recursive with
        | Some (name, handler) ->
          Some (Flambda.Nonrecursive { name; handler; }), r
        | None -> Some (Flambda.Recursive handlers), r

and simplify env r (tree : Flambda.t) : Flambda.t * R.t =
  match tree with
  | Apply apply ->
    simplify_apply env r ~apply
  | Let _ ->
    let for_last_body (env, r) body =
      simplify env r body
    in
    Flambda.fold_lets_option tree
      ~init:(env, r)
      ~for_defining_expr:for_defining_expr_of_let
      ~for_last_body
      ~filter_defining_expr:filter_defining_expr_of_let
  | Let_mutable { var = mut_var; initial_value = var; body; contents_kind } ->
    (* CR-someday mshinwell: add the dead let elimination, as above. *)
    simplify_free_variable env var ~f:(fun env var _var_approx ->
      let mut_var, sb =
        Freshening.add_mutable_variable (E.freshening env) mut_var
      in
      let env = E.set_freshening env sb in
      let body, r =
        simplify (E.add_mutable env mut_var (A.value_unknown Other)) r body
      in
      Flambda.Let_mutable
        { var = mut_var;
          initial_value = var;
          body;
          contents_kind },
      r)
  | Apply_cont (cont, trap_action, args) ->
    simplify_free_variables env args ~f:(fun env args args_approxs ->
      simplify_apply_cont env r cont ~trap_action ~args ~args_approxs)
  | Let_cont { body; handlers = Nonrecursive { name; handler = {
      params; handler = Apply_cont (alias_of, None, params');
      is_exn_handler = false; }; }; }
    when Variable.compare_lists params params' = 0 ->
    (* Introduction of continuation aliases. *)
    let expr : Flambda.t =
      Let_cont { body; handlers = Alias { name; alias_of; }; }
    in
    simplify env r expr
  | Let_cont { body; handlers; } ->
    (* In two stages we form the environment to be used for simplifying the
       [body].  If the continuations in [handlers] are recursive then
       that environment will also be used for simplifying the continuations
       themselves (otherwise the environment of the [Let_cont] is used). *)
(*Format.eprintf "Simplifying Let_cont:@ \n%a\n%!" Flambda.print tree;*)
    let conts_and_approxs, freshening =
      let normal_case ~handlers =
        Continuation.Map.fold (fun name
                (handler : Flambda.continuation_handler)
                (conts_and_approxs, freshening) ->
            let freshened_name, freshening =
              Freshening.add_static_exception freshening name
            in
            let num_params = List.length handler.params in
            let approx =
              (* If it's a stub, we put the code for [handler] in the
                 environment; this is unfreshened, but will be freshened up
                 if we inline it.
                 Note that stubs are not allowed to call themselves.
                 The code for [handler] is also put in the environment if
                 the continuation just contains [Proved_unreachable].  This
                 enables earlier [Switch]es that branch to such continuation
                 to be simplified, in some cases removing them entirely. *)
              let is_unreachable =
                match handler.handler with
                | Proved_unreachable -> true
                | _ -> false
              in
              if handler.stub || is_unreachable then begin
                assert (not (Continuation.Set.mem name
                  (Flambda.free_continuations handler.handler)));
                Continuation_approx.create ~name:freshened_name
                  ~handlers:(Nonrecursive handler)
                  ~num_params
              end else begin
                Continuation_approx.create_unknown ~name:freshened_name
                  ~num_params
              end
            in
            let conts_and_approxs =
              Continuation.Map.add freshened_name (name, approx)
                conts_and_approxs
            in
            conts_and_approxs, freshening)
          handlers
          (Continuation.Map.empty, E.freshening env)
      in
      match handlers with
      | Nonrecursive { name; handler; } ->
        let handlers =
          Continuation.Map.add name handler Continuation.Map.empty
        in
        normal_case ~handlers
      | Recursive handlers -> normal_case ~handlers
      | Alias { name; alias_of; } ->
        let freshened_name, freshening =
          Freshening.add_static_exception (E.freshening env) name
        in
        let alias_of =
          Freshening.apply_static_exception (E.freshening env) alias_of
        in
        let approx =
          let approx = E.find_continuation env alias_of in
          Continuation_approx.create_unknown
            ~name:(Continuation_approx.name approx)
            ~num_params:(Continuation_approx.num_params approx)
        in
        assert (Continuation_approx.handlers approx = None);
        let conts_and_approxs =
          Continuation.Map.of_list [
            freshened_name, (name, approx);
          ]
        in
        conts_and_approxs, freshening
    in
    (* CR mshinwell: Is _unfreshened_name redundant? *)
    let body_env =
      let env = E.set_freshening env freshening in
      Continuation.Map.fold (fun name (_unfreshened_name, approx) env ->
          E.add_continuation env name approx)
        conts_and_approxs
        env
    in
(*Format.eprintf "Simplifying body:\n%a" Flambda.print body;*)
    let body, r = simplify body_env r body in
(*Format.eprintf "Simplifying body finished.\n";*)
    begin match handlers with
    | Nonrecursive { name; handler; } ->
      let with_wrapper : Flambda_utils.with_wrapper =
        (* CR mshinwell: Tidy all this up somehow. *)
        (* Unboxing of continuation parameters is done now so that in one pass
           of [Inline_and_simplify] such unboxing will go all the way down the
           control flow. *)
        if handler.stub || E.never_inline_continuations env
        then Unchanged { handler; }
        else
          let args_approxs =
            R.continuation_args_approxs r name
              ~num_params:(List.length handler.params)
          in
          Unbox_continuation_params.for_non_recursive_continuation ~handler
            ~args_approxs ~name ~backend:(E.backend env)
      in
      let simplify_one_handler ?update_use_env env r ~name ~handler ~body
              : Flambda.expr * R.t =
        (* CR mshinwell: Consider whether we should call [exit_scope_catch] for
           non-recursive ones before simplifying their body.  I'm not sure we
           need to, since we already ensure such continuations aren't in the
           environment when simplifying the [handlers]. *)
        let handlers =
          Continuation.Map.add name handler Continuation.Map.empty
        in
        let update_use_env =
          match update_use_env with
          | None -> (fun env -> env)
          | Some f -> f
        in
        let handlers, r =
          simplify_let_cont_handlers ~env ~r ~handlers ~args_approxs:None
            ~recursive:Asttypes.Nonrecursive ~freshening ~update_use_env
        in
        match handlers with
        | None -> body, r
        | Some handlers -> Let_cont { body; handlers; }, r
      in
      begin match with_wrapper with
      | Unchanged _ -> simplify_one_handler env r ~name ~handler ~body
      | With_wrapper { new_cont; new_handler; wrapper_handler; } ->
        let body, r =
          let approx =
            Continuation_approx.create_unknown ~name:new_cont
              ~num_params:(List.length new_handler.params)
          in
          let update_use_env env =
            E.add_continuation env new_cont approx
          in
          (* CR mshinwell: See if we can cut down the continuation information
             in the environment (probably just to stub definitions and
             alias definitions) so we don't need [update_use_env]. *)
          let env = update_use_env env in
(*
Format.eprintf "Adding %a to the environment to simplify the wrapper\n%!"
  Continuation.print new_cont;
*)
          simplify_one_handler ~update_use_env env r ~name
            ~handler:wrapper_handler ~body
        in
        simplify_one_handler env r ~name:new_cont ~handler:new_handler ~body
(*
in
Format.eprintf "With wrappers applied:\n@ %a\n%!"
  Flambda.print body;
body, r
*)
      end
    | Recursive handlers ->
      (* The sequence is:
         1. Simplify the recursive handlers assuming that all of their
            parameters have [Value_unknown] approximation.  This may result in
            simplifying terms with less precise approximations than when
            they were previously simplified (e.g. there might have been a
            direct call to a closure whose approximation is now unknown).
            We mark the environment to avoid causing errors as a result of
            this.
         2. If all of the handlers are unused, there's nothing more to do.
         3. Extract the (hopefully more precise) approximations for the
            handlers' parameters from [r].  These will be at least as precise
            as the approximations deduced in any previous round of
            simplification.
         4. The code from the simplification is discarded.
         5. The continuation(s) is/are unboxed as required.
         6. The continuation(s) are simplified once again using the
            approximations deduced in step 2.
      *)
      let original_r = r in
      let original_handlers = handlers in
      let handlers, r =
        let env = E.allow_less_precise_approximations body_env in
        simplify_let_cont_handlers ~env ~r ~handlers
          ~args_approxs:None ~recursive:Asttypes.Recursive ~freshening
          ~update_use_env:(fun env -> env)
      in
      begin match handlers with
      | None -> body, r
      | Some _handlers ->
        let args_approxs =
          Continuation.Map.mapi (fun cont
                    (handler : Flambda.continuation_handler) ->
              let num_params = List.length handler.params in
              let cont =
                Freshening.apply_static_exception (E.freshening body_env) cont
              in
              R.defined_continuation_args_approxs r cont ~num_params)
            original_handlers
        in
(*
Format.eprintf "args_approxs override:@ %a\n%!"
  (Continuation.Map.print (Format.pp_print_list A.print)) args_approxs;
*)
        let handlers = original_handlers in
        let r = original_r in
        let handlers, env, update_use_env =
          if E.never_inline_continuations env then
            handlers, body_env, (fun env -> env)
          else
            let with_wrappers =
              Unbox_continuation_params.for_recursive_continuations
                ~handlers ~args_approxs ~backend:(E.backend env)
            in
            (* CR mshinwell: move to Flambda_utils, probably *)
            Continuation.Map.fold (fun cont
                    (with_wrapper : Flambda_utils.with_wrapper)
                    (handlers, env, update_use_env) ->
                match with_wrapper with
                | Unchanged { handler; } ->
                  Continuation.Map.add cont handler handlers, env,
                    update_use_env
                | With_wrapper { new_cont; new_handler; wrapper_handler; } ->
                  let handlers =
                    Continuation.Map.add new_cont new_handler
                      (Continuation.Map.add cont wrapper_handler handlers)
                  in
                  let approx =
                    Continuation_approx.create_unknown ~name:new_cont
                      ~num_params:(List.length new_handler.params)
                  in
                  let env = E.add_continuation env new_cont approx in
                  let update_use_env env =
                    update_use_env (E.add_continuation env new_cont approx)
                  in
                  handlers, env, update_use_env)
              with_wrappers
              (Continuation.Map.empty, body_env, (fun env -> env))
        in
        let handlers, r =
          simplify_let_cont_handlers ~env ~r ~handlers
            ~args_approxs:(Some args_approxs) ~recursive:Asttypes.Recursive
            ~freshening ~update_use_env
        in
        begin match handlers with
        | None -> body, r
        | Some handlers -> Let_cont { body; handlers; }, r
        end
      end
(*
Format.eprintf "After Unbox_continuation_params, Recursive, handlers are:\n%a%!"
  Flambda.print_let_cont_handlers (Flambda.Recursive handlers);
*)
    | Alias { name; alias_of = _; } ->
      (* As a result of adding the approximation of [name], above, to the
         environment then all uses of it in the [body] should have been
         replaced by [alias_of]. *)
      assert (R.continuation_unused r name);
      let r, _uses = R.exit_scope_catch r env name in
      assert (not (R.is_used_continuation r name));
      body, ret r (A.value_unknown Other)
    end
  | Switch (arg, sw) ->
    simplify_free_variable env arg ~f:(fun env arg arg_approx ->
(*
Format.eprintf "Switch on %a: approx of scrutinee is %a\n%!"
  Variable.print arg A.print arg_approx;
*)
      (* CR mshinwell: Maybe do "simplify_apply_cont_to_cont" on all the
         arms here? *)
      let destination_is_unreachable cont =
        (* CR mshinwell: This unreachable thing should be tidied up and also
           done on [Apply_cont]. *)
        let cont, _r =
          simplify_apply_cont_to_cont env r cont ~args_approxs:[]
        in
        let cont_approx = E.find_continuation env cont in
        match Continuation_approx.handlers cont_approx with
        | None | Some (Recursive _) -> false
        | Some (Nonrecursive handler) ->
          match handler.handler with
          | Proved_unreachable -> true
          | _ -> false
      in
      let rec filter_branches filter branches compatible_branches =
        match branches with
        | [] -> Can_be_taken compatible_branches
        | (c, cont) as branch :: branches ->
          if destination_is_unreachable cont then
            filter_branches filter branches compatible_branches
          else
            match filter arg_approx c with
            | A.Cannot_be_taken ->
(*
Format.eprintf "Switch arm %a cannot_be_taken\n%!" Continuation.print cont;
*)
              filter_branches filter branches compatible_branches
            | A.Can_be_taken ->
(*
Format.eprintf "Switch arm %a can_be_taken\n%!" Continuation.print cont;
*)
              filter_branches filter branches (branch :: compatible_branches)
            | A.Must_be_taken ->
(*
Format.eprintf "Switch arm %a must_be_taken\n%!" Continuation.print cont;
*)
              Must_be_taken cont
      in
      (* Use approximation information to determine which branches definitely
         will be taken, or may be taken.  (Note that the "Union" case in
         [Simple_value_approx] helps here.) *)
      let filtered_consts =
        filter_branches A.potentially_taken_const_switch_branch sw.consts []
      in
      begin match filtered_consts with
      | Must_be_taken cont ->
        let expr, r =
          simplify_apply_cont env r cont ~trap_action:None
            ~args:[] ~args_approxs:[]
        in
        expr, R.map_benefit r B.remove_branch
      | Can_be_taken consts ->
        match consts, sw.failaction with
        | [], None ->
          (* If the switch is applied to a statically-known value that does not
            match any case:
            * if there is a default action take that case;
            * otherwise this is something that is guaranteed not to
              be reachable by the type checker.  For example:
              [type 'a t = Int : int -> int t | Float : float -> float t
                match Int 1 with
                | Int _ -> ...
                | Float f as v ->
                  match v with   <-- This match is unreachable
                  | Float f -> ...]
          *)
          Proved_unreachable, r
        | [_, cont], None ->
          let cont, r =
            simplify_apply_cont_to_cont env r cont ~args_approxs:[]
          in
          Apply_cont (cont, None, []), R.map_benefit r B.remove_branch
        | [], Some cont ->
          if destination_is_unreachable cont then
            Proved_unreachable, R.map_benefit r B.remove_branch
          else
            let cont, r =
              simplify_apply_cont_to_cont env r cont ~args_approxs:[]
            in
            Apply_cont (cont, None, []), R.map_benefit r B.remove_branch
        | _ ->
          let env = E.inside_branch env in
          let f (acc, r) (i, cont) =
            let cont, r =
              simplify_apply_cont_to_cont env r cont ~args_approxs:[]
            in
            (i, cont)::acc, r
          in
          let r = R.set_approx r A.value_bottom in
          let consts, r = List.fold_left f ([], r) consts in
          let failaction, r =
            match sw.failaction with
            | None -> None, r
            | Some cont ->
              if destination_is_unreachable cont then
                None, r
              else
                let cont, r =
                  simplify_apply_cont_to_cont env r cont ~args_approxs:[]
                in
                Some cont, r
          in
          let switch =
            Flambda.create_switch ~scrutinee:arg
              ~all_possible_values:sw.numconsts
              ~arms:consts
              ~default:failaction
          in
          switch, r
      end)
  | Proved_unreachable -> Proved_unreachable, ret r A.value_bottom

and simplify_toplevel env r expr ~continuation ~descr =
  if not (Continuation.Map.mem continuation (E.continuations_in_scope env))
  then begin
    Misc.fatal_errorf "The continuation parameter (%a) must be in the \
        environment before calling [simplify_toplevel]"
      Continuation.print continuation
  end;
  (* Use-def pairs of continuations cannot cross function boundaries.
     We localise the uses and definitions of continuations within each
     toplevel expression / function body by using the snapshot/restore
     functions in [R].  This ensures in particular that passes such as
     [Continuation_specialisation] which look at the defined
     continuations information in [r] won't see definitions that don't
     actually exist at toplevel in the expression they are analysing.
  *)
  let continuation_uses_snapshot, r =
    R.snapshot_and_forget_continuation_uses r
  in
(*
Format.eprintf "Simplifying at toplevel:@ \n%a\n%!" Flambda.print expr;
*)
  let expr, r = simplify env r expr in
  let expr, r =
    Flambda_invariants.check_toplevel_simplification_result r expr
      ~continuation ~descr;
    if E.never_inline_continuations env then begin
      expr, r
    end else begin
      (* Continuation inlining and specialisation is done now, rather than
         during [simplify]'s traversal itself, to reduce quadratic behaviour
         to linear.
         Since we only inline linearly-used non-recursive continuations, the
         changes to [r] that need to be made by the inlining pass are
         straightforward. *)
      let expr, r =
        Continuation_inlining.for_toplevel_expression expr r
      in
      Flambda_invariants.check_toplevel_simplification_result r expr
        ~continuation ~descr;
      let vars_in_scope = E.vars_in_scope env in
      let expr =
        (* CR mshinwell: Should the specialisation pass return some
           benefit value? *)
        Continuation_specialisation.for_toplevel_expression expr
          ~vars_in_scope r ~simplify_let_cont_handlers
          ~backend:(E.backend env)
      in
      expr, r
    end
  in
  (* Continuation specialisation could theoretically improve the precision
     of the approximation for [continuation].  However tracking changes to 
     continuation usage during specialisation is complicated and error-prone,
     so instead, we accept an approximation for [continuation] that may be
     slightly less precise.  Any subsequent round of simplification will
     calculate the improved approximation anyway. *)
  (* CR mshinwell: try to fix the above *)
  let r, uses = R.exit_scope_catch r env continuation in
  let r = R.roll_back_continuation_uses r continuation_uses_snapshot in
  (* At this stage:
     - no continuation defined in [expr] should be mentioned in [r];
     - the free continuations of [expr] must be at most the [continuation]
       parameter. *)
  if !Clflags.flambda_invariant_checks then begin
    let defined_conts = Flambda_utils.all_defined_continuations_toplevel expr in
    let r_used = R.used_continuations r in
    let r_defined =
      Continuation.Map.keys (R.continuation_definitions_with_uses r)
    in
    let check_defined from_r descr' =
      let bad = Continuation.Set.inter defined_conts from_r in
      if not (Continuation.Set.is_empty bad) then begin
        Misc.fatal_errorf "Continuations (%a) defined locally to %s are still \
            mentioned in %s [r] upon leaving [simplify_toplevel]:@ \n%a"
          Continuation.Set.print bad
          descr
          descr'
          Flambda.print expr
      end
    in
    check_defined r_used "the use information inside";
    check_defined r_defined "the defined-continuations information inside";
    let free_conts = Flambda.free_continuations expr in
    let bad_free_conts =
      Continuation.Set.diff free_conts
        (Continuation.Set.singleton continuation)
    in
    if not (Continuation.Set.is_empty bad_free_conts) then begin
      Misc.fatal_errorf "The free continuations of %s \
          must be at most {%a} (but are instead {%a}):@ \n%a"
        descr
        Continuation.print continuation
        Continuation.Set.print free_conts
        Flambda.print expr
    end
  end;
  expr, r, uses

and duplicate_function ~env ~(set_of_closures : Flambda.set_of_closures)
      ~fun_var =
  let function_decl =
    match Variable.Map.find fun_var set_of_closures.function_decls.funs with
    | exception Not_found ->
      Misc.fatal_errorf "duplicate_function: cannot find function %a"
        Variable.print fun_var
    | function_decl -> function_decl
  in
  let env = E.activate_freshening (E.set_never_inline env) in
  let free_vars, specialised_args, function_decls, parameter_approximations,
      _internal_value_set_of_closures, set_of_closures_env =
    Inline_and_simplify_aux.prepare_to_simplify_set_of_closures ~env
      ~set_of_closures ~function_decls:set_of_closures.function_decls
      ~freshen:false ~only_for_function_decl:(Some function_decl)
  in
  let function_decl =
    match Variable.Map.find fun_var function_decls.funs with
    | exception Not_found ->
      Misc.fatal_errorf "duplicate_function: cannot find function %a (2)"
        Variable.print fun_var
    | function_decl -> function_decl
  in
  let closure_env =
    Inline_and_simplify_aux.prepare_to_simplify_closure ~function_decl
      ~free_vars ~specialised_args ~parameter_approximations
      ~set_of_closures_env
  in
  let cont_approx =
    Continuation_approx.create_unknown ~name:function_decl.continuation_param
      ~num_params:1
  in
  let closure_env =
    E.add_continuation closure_env function_decl.continuation_param
      cont_approx
  in
  let r = R.create () in
  let body, r =
    E.enter_closure closure_env
      ~closure_id:(Closure_id.wrap fun_var)
      ~inline_inside:false
      ~dbg:function_decl.dbg
      ~f:(fun body_env -> simplify body_env r function_decl.body)
  in
  let _r, _uses =
    R.exit_scope_catch r env function_decl.continuation_param
  in
  let function_decl =
    Flambda.create_function_declaration ~params:function_decl.params
      ~continuation_param:function_decl.continuation_param
      ~return_arity:function_decl.return_arity
      ~body ~stub:function_decl.stub ~dbg:function_decl.dbg
      ~inline:function_decl.inline ~specialise:function_decl.specialise
      ~is_a_functor:function_decl.is_a_functor
  in
  function_decl, specialised_args

let constant_defining_value_approx
    env
    (constant_defining_value:Flambda.constant_defining_value) =
  match constant_defining_value with
  | Allocated_const const ->
    approx_for_allocated_const const
  | Block (tag, fields) ->
    let fields =
      List.map
        (function
          | Flambda.Symbol sym -> begin
              match E.find_symbol_opt env sym with
              | Some approx -> approx
              | None -> A.value_unresolved (Symbol sym)
            end
          | Flambda.Const cst -> approx_for_const cst)
        fields
    in
    A.value_block tag (Array.of_list fields)
  | Set_of_closures { function_decls; free_vars; specialised_args } ->
    (* At toplevel, there is no freshening currently happening (this
       cannot be the body of a currently inlined function), so we can
       keep the original set_of_closures in the approximation. *)
    assert(E.freshening env = Freshening.empty);
    assert(Variable.Map.is_empty free_vars);
    assert(Variable.Map.is_empty specialised_args);
    let invariant_params =
      lazy (Invariant_params.Functions.invariant_params_in_recursion
        function_decls ~backend:(E.backend env))
    in
    let value_set_of_closures =
      A.create_value_set_of_closures ~function_decls
        ~bound_vars:Var_within_closure.Map.empty
        ~invariant_params
        ~specialised_args:Variable.Map.empty
        ~freshening:Freshening.Project_var.empty
        ~direct_call_surrogates:Closure_id.Map.empty
    in
    A.value_set_of_closures value_set_of_closures
  | Project_closure (set_of_closures_symbol, closure_id) -> begin
      match E.find_symbol_opt env set_of_closures_symbol with
      | None ->
        A.value_unresolved (Symbol set_of_closures_symbol)
      | Some set_of_closures_approx ->
        let checked_approx =
          A.check_approx_for_set_of_closures set_of_closures_approx
        in
        match checked_approx with
        | Ok (_, value_set_of_closures) ->
          let closure_id =
            A.freshen_and_check_closure_id value_set_of_closures
              (Closure_id.Set.singleton closure_id)
          in
          A.value_closure
            (Closure_id.Map.of_set (fun _ -> value_set_of_closures) closure_id)
        | Unresolved sym -> A.value_unresolved sym
        | Unknown -> A.value_unknown Other
        | Unknown_because_of_unresolved_value value ->
          A.value_unknown (Unresolved_value value)
        | Wrong ->
          Misc.fatal_errorf "Wrong approximation for [Project_closure] \
                             when being used as a [constant_defining_value]: %a"
            Flambda.print_constant_defining_value constant_defining_value
    end

(* See documentation on [Let_rec_symbol] in flambda.mli. *)
let define_let_rec_symbol_approx env defs =
  (* First declare an empty version of the symbols *)
  let env =
    List.fold_left (fun env (symbol, _) ->
        E.add_symbol env symbol (A.value_unresolved (Symbol symbol)))
      env defs
  in
  let rec loop times env =
    if times <= 0 then
      env
    else
      let env =
        List.fold_left (fun env (symbol, constant_defining_value) ->
            let approx =
              constant_defining_value_approx env constant_defining_value
            in
            E.redefine_symbol env symbol approx)
          env defs
      in
      loop (times-1) env
  in
  loop 2 env

let simplify_constant_defining_value
    env r symbol
    (constant_defining_value:Flambda.constant_defining_value) =
  let r, constant_defining_value, approx =
    match constant_defining_value with
    (* No simplifications are possible for [Allocated_const] or [Block]. *)
    | Allocated_const const ->
      r, constant_defining_value, approx_for_allocated_const const
    | Block (tag, fields) ->
      let fields = List.map
          (function
            | Flambda.Symbol sym -> E.find_symbol_exn env sym
            | Flambda.Const cst -> approx_for_const cst)
          fields
      in
      r, constant_defining_value, A.value_block tag (Array.of_list fields)
    | Set_of_closures set_of_closures ->
      if Variable.Map.cardinal set_of_closures.free_vars <> 0 then begin
        Misc.fatal_errorf "Set of closures bound by [Let_symbol] is not \
                           closed: %a"
          Flambda.print_set_of_closures set_of_closures
      end;
      let set_of_closures, r, _freshening =
        simplify_set_of_closures env r set_of_closures
      in
      r, ((Set_of_closures set_of_closures) : Flambda.constant_defining_value),
        R.approx r
    | Project_closure (set_of_closures_symbol, closure_id) ->
      (* No simplifications are necessary here. *)
      let set_of_closures_approx =
        E.find_symbol_exn env set_of_closures_symbol
      in
      let closure_approx =
        match A.check_approx_for_set_of_closures set_of_closures_approx with
        | Ok (_, value_set_of_closures) ->
          let closure_id =
            A.freshen_and_check_closure_id value_set_of_closures
              (Closure_id.Set.singleton closure_id)
          in
          A.value_closure
            (Closure_id.Map.of_set (fun _ -> value_set_of_closures) closure_id)
        | Unresolved sym -> A.value_unresolved sym
        | Unknown -> A.value_unknown Other
        | Unknown_because_of_unresolved_value value ->
          A.value_unknown (Unresolved_value value)
        | Wrong ->
          Misc.fatal_errorf "Wrong approximation for [Project_closure] \
                             when being used as a [constant_defining_value]: %a"
            Flambda.print_constant_defining_value constant_defining_value
      in
      r, constant_defining_value, closure_approx
  in
  let approx = A.augment_with_symbol approx symbol in
  let r = ret r approx in
  r, constant_defining_value, approx

let rec simplify_program_body env r (program : Flambda.program_body)
  : Flambda.program_body * R.t =
  match program with
  | Let_rec_symbol (defs, program) ->
    let env = define_let_rec_symbol_approx env defs in
    let env, r, defs =
      List.fold_left (fun (env, r, defs) (symbol, def) ->
          let r, def, approx =
            simplify_constant_defining_value env r symbol def
          in
          let approx = A.augment_with_symbol approx symbol in
          let env = E.redefine_symbol env symbol approx in
          (env, r, (symbol, def) :: defs))
        (env, r, []) defs
    in
    let program, r = simplify_program_body env r program in
    Let_rec_symbol (defs, program), r
  | Let_symbol (symbol, constant_defining_value, program) ->
    let r, constant_defining_value, approx =
      simplify_constant_defining_value env r symbol constant_defining_value
    in
    let approx = A.augment_with_symbol approx symbol in
    let env = E.add_symbol env symbol approx in
    let program, r = simplify_program_body env r program in
    Let_symbol (symbol, constant_defining_value, program), r
  | Initialize_symbol (symbol, tag, fields, program) ->
    let rec simplify_fields env r l =
      match l with
      | [] -> [], [], r
      | (h, cont) :: t ->
        let t', approxs, r = simplify_fields env r t in
        let cont_approx =
          Continuation_approx.create_unknown ~name:cont ~num_params:1
        in
        let env = E.add_continuation env cont cont_approx in
(*
Format.eprintf "Simplifying initialize_symbol field:@;%a"
  Flambda.print h;
*)
        let h', r, uses =
          let descr =
            Format.asprintf "Initialize_symbol %a" Symbol.print symbol
          in
          simplify_toplevel env r h ~continuation:cont ~descr
        in
        let approx =
          Inline_and_simplify_aux.Continuation_uses.meet_of_args_approxs
            uses ~num_params:1
        in
        let approx =
          match approx with
          | [approx] -> approx
          | _ -> assert false
        in
        let approxs = approx :: approxs in
        if t' == t && h' == h
        then l, approxs, r
        else (h', cont) :: t', approxs, r
    in
    let fields, approxs, r = simplify_fields env r fields in
    let approx =
      A.augment_with_symbol (A.value_block tag (Array.of_list approxs)) symbol
    in
(*
Format.eprintf "Symbol %a has approximation %a\n%!"
  Symbol.print symbol
  A.print (A.value_block tag (Array.of_list approxs));
*)
    let module Backend = (val (E.backend env) : Backend_intf.S) in
    let env = E.add_symbol env symbol approx in
    let program, r = simplify_program_body env r program in
    (* CR mshinwell: This should turn things into [Effect] when it can, no? *)
    Initialize_symbol (symbol, tag, fields, program), r
  | Effect (expr, cont, program) ->
    let cont_approx =
      Continuation_approx.create_unknown ~name:cont ~num_params:1
    in
    let env = E.add_continuation env cont cont_approx in
    let expr, r, uses =
      let descr =
        Format.asprintf "Effect (return continuation %a)"
          Continuation.print cont
      in
      simplify_toplevel env r expr ~continuation:cont ~descr
    in
    begin match
      Inline_and_simplify_aux.Continuation_uses.meet_of_args_approxs
        uses ~num_params:1
    with
    | [_] -> ()
    | _ -> assert false
    end;
    let program, r = simplify_program_body env r program in
    Effect (expr, cont, program), r
  | End root -> End root, r

let simplify_program env r (program : Flambda.program) =
  let env, r =
    Symbol.Set.fold (fun symbol (env, r) ->
        let env, approx =
          match E.find_symbol_exn env symbol with
          | exception Not_found ->
            let module Backend = (val (E.backend env) : Backend_intf.S) in
            (* CR-someday mshinwell for mshinwell: Is there a reason we cannot
               use [simplify_named_using_approx_and_env] here? *)
            let approx = Backend.import_symbol symbol in
            E.add_symbol env symbol approx, approx
          | approx -> env, approx
        in
        env, ret r approx)
      program.imported_symbols
      (env, r)
  in
  let program_body, r = simplify_program_body env r program.program_body in
  let program = { program with program_body; } in
  program, r

let add_predef_exns_to_environment ~env ~backend =
  let module Backend = (val backend : Backend_intf.S) in
  List.fold_left (fun env predef_exn ->
      assert (Ident.is_predef_exn predef_exn);
      let symbol = Backend.symbol_for_global' predef_exn in
      let name = Ident.name predef_exn in
      let approx =
        A.value_block Tag.object_tag
          [| A.value_string (String.length name) (Some name);
             A.value_unknown Other;
          |]
      in
      E.add_symbol env symbol (A.augment_with_symbol approx symbol))
    env
    Predef.all_predef_exns

let run ~never_inline ~allow_continuation_inlining ~backend ~prefixname ~round
      program =
  let r = R.create () in
  let report = !Clflags.inlining_report in
  if never_inline then Clflags.inlining_report := false;
  let initial_env =
    add_predef_exns_to_environment
      ~env:(E.create ~never_inline ~allow_continuation_inlining ~backend ~round)
      ~backend
  in
  let result, r = simplify_program initial_env r program in
  let result = Flambda_utils.introduce_needed_import_symbols result in
  if not (R.no_continuations_in_scope r)
  then begin
    Misc.fatal_errorf "Continuations %a had uses but not definitions recorded \
        in [r] by the end of simplification.  Program:@ \n%a"
      Continuation.Set.print (R.used_continuations r)
      Flambda.print_program result
  end;
  assert (R.no_continuations_in_scope r);
  if !Clflags.inlining_report then begin
    let output_prefix = Printf.sprintf "%s.%d" prefixname round in
    Inlining_stats.save_then_forget_decisions ~output_prefix
  end;
  Clflags.inlining_report := report;
  result
