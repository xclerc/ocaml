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

module B = Inlining_cost.Benefit
module E = Inline_and_simplify_aux.Env
module R = Inline_and_simplify_aux.Result

let new_var name =
  Variable.create name
    ~current_compilation_unit:(Compilation_unit.get_current_exn ())

let which_function_parameters_can_we_specialise
      ~(params           : Variable.t list)
      ~(args             : Variable.t list)
      ~(args_approxs     : Simple_value_approx.t list)
      ~(invariant_params : Variable.Set.t Variable.Map.t lazy_t)
      ~(specialised_args : Flambda.specialised_to Variable.Map.t) =
  assert (List.length params = List.length args);
  assert (List.length args = List.length args_approxs);
  List.fold_right2
    (fun (var, arg) approx
      (worth_specialising_args,
       old_params_to_new_outside,
       old_outside_to_new_outside) ->
      let old_outside_to_new_outside =
        match Variable.Map.find_opt var specialised_args with
        | Some { Flambda.var; } ->
          Variable.Map.add var arg old_outside_to_new_outside
        | None ->
          old_outside_to_new_outside
      in
      let old_params_to_new_outside, worth_specialising_args =
        if (Variable.Map.mem var specialised_args) ||
           (Simple_value_approx.useful approx
            && Variable.Map.mem var (Lazy.force invariant_params)) then begin
          let old_params_to_new_outside =
            Variable.Map.add var arg old_params_to_new_outside
          in
          let old_params_to_new_outside =
            match Variable.Map.find_opt var (Lazy.force invariant_params) with
            | Some set ->
              Variable.Set.fold
                (fun elem acc -> Variable.Map.add elem arg acc)
                set
                old_params_to_new_outside
            | None ->
              old_params_to_new_outside
          in
          old_params_to_new_outside, Variable.Set.add var worth_specialising_args
        end else
          old_params_to_new_outside, worth_specialising_args
      in
      worth_specialising_args,
      old_params_to_new_outside,
      old_outside_to_new_outside)
    (List.combine params args) args_approxs
    (Variable.Set.empty, Variable.Map.empty, Variable.Map.empty)

(** Fold over all variables bound by the given closure, which is bound to the
    variable [lhs_of_application], and corresponds to the given
    [function_decls].  Each variable bound by the closure is passed to the
    user-specified function as an [Flambda.named] value that projects the
    variable from its closure. *)
let fold_over_projections_of_vars_bound_by_closure ~closure_id_being_applied
      ~lhs_of_application ~function_decls ~init ~f =
  Variable.Set.fold (fun var acc ->
      let expr : Flambda.named =
        Project_var {
          closure = lhs_of_application;
          closure_id = closure_id_being_applied;
          var = Var_within_closure.wrap var;
        }
      in
      f ~acc ~var ~expr)
    (Flambda_utils.variables_bound_by_the_closure closure_id_being_applied
      function_decls)
    init

let set_inline_attribute_on_all_apply body inline specialise =
  Flambda_iterators.map_toplevel_expr (function
      | Apply apply -> Apply { apply with inline; specialise }
      | expr -> expr)
    body

(** Assign fresh names for a function's parameters and rewrite the body to
    use these new names. *)
let copy_of_function's_body_with_freshened_params env
      ~(function_decl : Flambda.function_declaration) =
  let params = function_decl.params in
  let param_vars = Parameter.List.vars params in
  (* We cannot avoid the substitution in the case where we are inlining
     inside the function itself.  This can happen in two ways: either
     (a) we are inlining the function itself directly inside its declaration;
     or (b) we are inlining the function into an already-inlined copy.
     For (a) we cannot short-cut the substitution by freshening since the
     original [params] may still be referenced; for (b) we cannot do it
     either since the freshening may already be renaming the parameters for
     the first inlining of the function. *)
  if E.does_not_bind env param_vars
    && E.does_not_freshen env param_vars
  then
    params, function_decl.body
  else
    let freshened_params = List.map (fun p -> Parameter.rename p) params in
    let subst =
      Variable.Map.of_list
        (List.combine param_vars (Parameter.List.vars freshened_params))
    in
    let body = Flambda_utils.toplevel_substitution subst function_decl.body in
    freshened_params, body

(* CR-soon mshinwell: Add a note somewhere to explain why "bound by the closure"
   does not include the function identifiers for other functions in the same
   set of closures.
   mshinwell: The terminology may be used inconsistently. *)

(** Inline a function by copying its body into a context where it becomes
    closed.  That is to say, we bind the free variables of the body
    (= "variables bound by the closure"), and any function identifiers
    introduced by the corresponding set of closures. *)
let inline_by_copying_function_body ~env ~r
      ~(function_decls : Flambda.function_declarations)
      ~lhs_of_application
      ~(inline_requested : Lambda.inline_attribute)
      ~(specialise_requested : Lambda.specialise_attribute)
      ~closure_id_being_applied
      ~(function_decl : Flambda.function_declaration) ~args ~dbg ~simplify =
  assert (E.mem env lhs_of_application);
  assert (List.for_all (E.mem env) args);
  let r =
    if function_decl.stub then r
    else R.map_benefit r B.remove_call
  in
  let freshened_params, body =
    copy_of_function's_body_with_freshened_params env ~function_decl
  in
  let body =
    if function_decl.stub &&
       ((inline_requested <> Lambda.Default_inline)
        || (specialise_requested <> Lambda.Default_specialise)) then
      (* When the function inlined function is a stub, the annotation
         is reported to the function applications inside the stub.
         This allows to report the annotation to the application the
         original programmer really intended: the stub is not visible
         in the source. *)
      set_inline_attribute_on_all_apply body
        inline_requested specialise_requested
    else
      body
  in
  let bindings_for_params_to_args =
    (* Bind the function's parameters to the arguments from the call site. *)
    let args = List.map (fun arg -> Flambda.Expr (Var arg)) args in
    Flambda_utils.bind ~body
      ~bindings:(List.combine (Parameter.List.vars freshened_params) args)
  in
  (* Add bindings for the variables bound by the closure. *)
  let bindings_for_vars_bound_by_closure_and_params_to_args =
    fold_over_projections_of_vars_bound_by_closure ~closure_id_being_applied
      ~lhs_of_application ~function_decls ~init:bindings_for_params_to_args
      ~f:(fun ~acc:body ~var ~expr -> Flambda.create_let var expr body)
  in
  (* Add bindings for variables corresponding to the functions introduced by
     the whole set of closures.  Each such variable will be bound to a closure;
     each such closure is in turn produced by moving from the closure being
     applied to another closure in the same set.
  *)
  let expr =
    Variable.Map.fold (fun another_closure_in_the_same_set _ expr ->
      let used =
        Variable.Set.mem another_closure_in_the_same_set
           function_decl.free_variables
      in
      if used then
        Flambda.create_let another_closure_in_the_same_set
          (Move_within_set_of_closures {
            closure = lhs_of_application;
            start_from = closure_id_being_applied;
            move_to = Closure_id.wrap another_closure_in_the_same_set;
          })
          expr
      else expr)
      function_decls.funs
      bindings_for_vars_bound_by_closure_and_params_to_args
  in
  let env = E.activate_freshening (E.set_never_inline env) in
  let env = E.set_inline_debuginfo ~dbg env in
  simplify env r expr

type state = {
  to_rewrite               : Variable.t list;
  rewritten                : Flambda.function_declaration Variable.Map.t;
  old_inside_to_new_inside : Variable.t Variable.Map.t;
  free_vars                : Flambda.specialised_to Variable.Map.t;
  let_bindings             : (Variable.t * Flambda.named) list;
  specialised_args         : Flambda.specialised_to Variable.Map.t;
}

let empty_state =
  { to_rewrite               = [];
    rewritten                = Variable.Map.empty;
    old_inside_to_new_inside = Variable.Map.empty;
    free_vars                = Variable.Map.empty;
    let_bindings             = [];
    specialised_args         = Variable.Map.empty; }

let make_state closure_id =
  { empty_state with to_rewrite = [Closure_id.unwrap closure_id]; }

let add_fun_var
      ({ old_inside_to_new_inside; free_vars; let_bindings; _ } as state)
      ~lhs_of_application
      ~closure_id_being_applied
      fun_var =
  let inside_var = Variable.rename ~append:"_original" fun_var in
  let outside_var = Variable.create "closure" in
  let spec : Flambda.specialised_to =
    { var = outside_var; projection = None; }
  in
  let let_closure_be_move =
    outside_var,
    Flambda.Move_within_set_of_closures
      { closure    = lhs_of_application;
        start_from = closure_id_being_applied;
        move_to    = Closure_id.wrap fun_var; }
  in
  { state with
    old_inside_to_new_inside = Variable.Map.add fun_var inside_var old_inside_to_new_inside;
    free_vars                = Variable.Map.add inside_var spec free_vars;
    let_bindings             = let_closure_be_move :: let_bindings; }

let add_free_var
      ({ free_vars; let_bindings; _ } as state)
      ~lhs_of_application
      ~closure_id_being_applied
      var =
  let var_clos = new_var "from_closure" in
  let spec : Flambda.specialised_to =
    { var = var_clos; projection = None; }
  in
  let expr : Flambda.named =
    Project_var {
      closure = lhs_of_application;
      closure_id = closure_id_being_applied;
      var = Var_within_closure.wrap var;
    }
  in
  { state with
    free_vars    = Variable.Map.add var spec free_vars;
    let_bindings = (var_clos, expr) :: let_bindings; }

let add_fresh_params
      ({ old_inside_to_new_inside; _ } as state)
      params =
  let old_inside_to_new_inside, new_params, old_params_to_new_params =
    List.fold_left
      (fun
        (old_inside_to_new_inside, new_params, old_params_to_new_params)
        param ->
        let old_param = Parameter.var param in
        let new_param = Variable.rename ~append:"_param" old_param in
        Variable.Map.add old_param new_param old_inside_to_new_inside,
        (Parameter.wrap new_param) :: new_params,
        Variable.Map.add old_param new_param old_params_to_new_params)
      (old_inside_to_new_inside, [], Variable.Map.empty)
      params
  in
  { state with old_inside_to_new_inside; },
  List.rev new_params,
  old_params_to_new_params

let create_function_declaration_with_new_body
      { Flambda.params = _;
        body = _;
        free_variables = _;
        free_symbols = _;
        stub;
        dbg;
        inline;
        specialise;
        is_a_functor; }
      params
      body =
  Flambda.create_function_declaration
    ~params
    ~stub
    ~dbg
    ~inline
    ~specialise
    ~is_a_functor
    ~body

let add_rewritten_function
      ({ rewritten; _} as state)
      fun_var
      fun_decl
      params
      body =
  let rewritten =
    Variable.Map.add
      fun_var
      (create_function_declaration_with_new_body fun_decl params body)
      rewritten
  in
  { state with rewritten; }

let rewrite_surrogates rewritten direct_call_surrogates =
  Closure_id.Map.fold
    (fun closure_id surrogate_id acc ->
       let closure_var   = Closure_id.unwrap closure_id in
       let surrogate_var = Closure_id.unwrap surrogate_id in
       if Variable.Map.mem closure_var rewritten
       && Variable.Map.mem surrogate_var rewritten then
         Variable.Map.add closure_var surrogate_var acc
       else
         acc)
    direct_call_surrogates
    Variable.Map.empty

let rec rewrite_functions
    ~(function_decls           : Flambda.function_declarations)
    ~(lhs_of_application       : Variable.t)
    ~(closure_id_being_applied : Closure_id.t)
    ~old_params_to_new_outside
    ({ to_rewrite; rewritten; _ } as state) =
  match to_rewrite with
  | [] -> state
  | fun_to_rewrite :: others_to_rewrite ->
    if Variable.Map.mem fun_to_rewrite rewritten then
      rewrite_functions
        ~function_decls
        ~lhs_of_application
        ~closure_id_being_applied
        ~old_params_to_new_outside
        { state with to_rewrite = others_to_rewrite; }
    else begin
      let fun_decl =
        Variable.Map.find fun_to_rewrite function_decls.funs
      in
      let state, new_params, _XXX =
        add_fresh_params state fun_decl.params in
      let state =
        Variable.Set.fold
          (fun var state ->
             if Variable.Map.mem var state.old_inside_to_new_inside then
               state
             else begin
               let add =
                 if Variable.Map.mem var function_decls.funs then
                   add_fun_var
                 else
                   add_free_var
               in
               add state ~lhs_of_application ~closure_id_being_applied var
             end)
          fun_decl.free_variables
          state
      in
      let body =
        Flambda_utils.toplevel_substitution
          state.old_inside_to_new_inside
          fun_decl.body
      in
      let to_rewrite = ref others_to_rewrite in
      let body =
        let preserve_specialisation
              (arg : Variable.t)
              (param : Flambda_utils.specialised_to_same_as) =
          let arg =
            try
              Variable.Map.find
                arg
                old_params_to_new_outside
            with Not_found ->
              arg
          in
          begin match param with
          | Not_specialised ->
            true
          | Specialised_and_aliased_to aliases ->
            Variable.Set.exists
              (fun alias ->
                 let alias =
                   try
                     Variable.Map.find
                       alias
                       state.old_inside_to_new_inside
                   with Not_found ->
                     alias
                 in
                 Variable.equal alias arg)
              aliases
          end
        in
        let functions'_specialised_params = Variable.Map.empty in (*XXX*)
        (* XXX must distribute new closure identifiers;
           will allow to move the substitution after this map *)
        Flambda_iterators.map_toplevel_expr
          (fun (expr : Flambda.t) ->
             match expr with
             | Apply ({ kind = Direct closure_id; args; } as apply) ->
               let closure_var = Closure_id.unwrap closure_id in
               let specialised_parameters =
                 Variable.Map.find_opt
                   closure_var
                   functions'_specialised_params
               in
               begin match specialised_parameters with
               | Some parameters ->
                 assert (List.length args = List.length parameters);
                 let rewrite_call =
                   List.for_all2
                     preserve_specialisation
                     args
                     parameters
                 in
                 if rewrite_call then begin
                   to_rewrite := closure_var :: !to_rewrite;
                   Flambda.Apply { apply with func = closure_var; }
                 end else
                   expr
               | None -> expr
               end
             | _ -> expr)
          body
      in
      let state =
        add_rewritten_function
          state
          fun_to_rewrite
          fun_decl
          new_params
          body
      in
      rewrite_functions
        ~function_decls
        ~lhs_of_application
        ~closure_id_being_applied
        ~old_params_to_new_outside
        { state with to_rewrite = !to_rewrite; }
    end

let inline_by_copying_function_declaration
    ~(env                      : Inline_and_simplify_aux.Env.t)
    ~(r                        : Inline_and_simplify_aux.Result.t)
    ~(function_decls           : Flambda.function_declarations)
    ~(lhs_of_application       : Variable.t)
    ~(inline_requested         : Lambda.inline_attribute)
    ~(closure_id_being_applied : Closure_id.t)
    ~(function_decl            : Flambda.function_declaration)
    ~(args                     : Variable.t list)
    ~(args_approxs             : Simple_value_approx.t list)
    ~(invariant_params         : Variable.Set.t Variable.Map.t lazy_t)
    ~(specialised_args         : Flambda.specialised_to Variable.Map.t)
    ~(direct_call_surrogates   : Closure_id.t Closure_id.Map.t)
    ~(dbg                      : Debuginfo.t)
    ~(simplify                 : Inlining_decision_intf.simplify)
  : (Flambda.t * Inline_and_simplify_aux.Result.t) option =
  let worth_specialising_args,
      old_params_to_new_outside,
      old_outside_to_new_outside =
    which_function_parameters_can_we_specialise
      ~params:(Parameter.List.vars function_decl.params)
      ~args
      ~args_approxs
      ~invariant_params
      ~specialised_args
  in
  let worth_specialising =
    not (Variable.Set.subset
           worth_specialising_args
           (Variable.Map.keys specialised_args))
  in
  match worth_specialising with
  | false -> None
  | true ->
    match rewrite_functions
            ~function_decls
            ~lhs_of_application
            ~closure_id_being_applied
            ~old_params_to_new_outside
            (make_state closure_id_being_applied) with
    | { to_rewrite;
        rewritten;
        old_inside_to_new_inside;
        free_vars;
        let_bindings;
        specialised_args; } ->
      assert (to_rewrite = []);
      let body =
        let func = new_var "dup_func" in
        let set_of_closures = new_var "dup_set_of_closures" in
        let function_decls =
          Flambda.update_function_declarations
            ~funs:rewritten
            function_decls
        in
        let direct_call_surrogates =
          rewrite_surrogates
            rewritten
            direct_call_surrogates
        in
        Flambda.create_let
          set_of_closures
          (Set_of_closures
             (Flambda.create_set_of_closures
                ~function_decls
                ~free_vars
                ~specialised_args
                ~direct_call_surrogates))
          (Flambda.create_let
             func
             (Project_closure {
                set_of_closures;
                closure_id = closure_id_being_applied;
              })
             (Apply {
                func;
                args;
                kind = Direct closure_id_being_applied;
                dbg;
                inline = inline_requested;
                specialise = Default_specialise;
              }))
      in
      let env = E.activate_freshening (E.set_never_inline env) in
      Some (simplify env r (Flambda_utils.bind ~body ~bindings:let_bindings))
