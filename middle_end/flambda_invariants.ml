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

[@@@ocaml.warning "+a-4-30-40-41-42"]

type flambda_kind =
  | Normal
  | Lifted

(* CR mshinwell: Check that apply_cont is well-formed when there is a
   trap installation or removal. *)

(* Explicit "ignore" functions.  We name every pattern variable, avoiding
   underscores, to try to avoid accidentally failing to handle (for example)
   a particular variable.
   We also avoid explicit record field access during the checking functions,
   preferring instead to use exhaustive record matches.
*)
(* CR-someday pchambart: for sum types, we should probably add an exhaustive
   pattern in ignores functions to be reminded if a type change *)
let ignore_variable (_ : Variable.t) = ()
let ignore_call_kind (_ : Flambda.call_kind) = ()
let ignore_debuginfo (_ : Debuginfo.t) = ()
let ignore_meth_kind (_ : Lambda.meth_kind) = ()
let ignore_int (_ : int) = ()
let ignore_int_set (_ : Numbers.Int.Set.t) = ()
let ignore_bool (_ : bool) = ()
let ignore_switch_block_pattern (_ : Ilambda.switch_block_pattern) = ()
let ignore_continuation (_ : Continuation.t) = ()
let ignore_primitive ( _ : Lambda.primitive) = ()
let ignore_const (_ : Flambda.const) = ()
let ignore_allocated_const (_ : Allocated_const.t) = ()
let ignore_set_of_closures_id (_ : Set_of_closures_id.t) = ()
let ignore_set_of_closures_origin (_ : Set_of_closures_origin.t) = ()
let ignore_closure_id (_ : Closure_id.t) = ()
let ignore_closure_id_set (_ : Closure_id.Set.t) = ()
let ignore_closure_id_map (_ : 'a -> unit) (_ : 'a Closure_id.Map.t) = ()
let ignore_var_within_closure (_ : Var_within_closure.t) = ()
let ignore_tag (_ : Tag.t) = ()
let ignore_inline_attribute (_ : Lambda.inline_attribute) = ()
let ignore_specialise_attribute (_ : Lambda.specialise_attribute) = ()
let ignore_value_kind (_ : Lambda.value_kind) = ()
let ignore_rec_flag (_ : Asttypes.rec_flag) = ()

exception Binding_occurrence_not_from_current_compilation_unit of Variable.t
exception Mutable_binding_occurrence_not_from_current_compilation_unit of
  Mutable_variable.t
exception Binding_occurrence_of_variable_already_bound of Variable.t
exception Binding_occurrence_of_mutable_variable_already_bound of
  Mutable_variable.t
exception Binding_occurrence_of_symbol_already_bound of Symbol.t
exception Unbound_variable of Variable.t
exception Unbound_mutable_variable of Mutable_variable.t
exception Unbound_symbol of Symbol.t
exception Vars_in_function_body_not_bound_by_closure_or_params of
  Variable.Set.t * Flambda.set_of_closures * Variable.t
exception Function_decls_have_overlapping_parameters of Variable.Set.t
exception Specialised_arg_that_is_not_a_parameter of Variable.t
exception Projection_must_be_a_free_var of Projection.t
exception Projection_must_be_a_specialised_arg of Projection.t
exception Free_variables_set_is_lying of
  Variable.t * Variable.Set.t * Variable.Set.t * Flambda.function_declaration
exception Set_of_closures_free_vars_map_has_wrong_range of Variable.Set.t
exception Continuation_not_caught of Continuation.t * string
exception Continuation_caught_in_multiple_places of Continuation.t
exception Continuation_called_with_wrong_arity of Continuation.t * int * int
exception Malformed_exception_continuation of Continuation.t * string
exception Access_to_global_module_identifier of Lambda.primitive
exception Pidentity_should_not_occur
exception Pdirapply_should_be_expanded
exception Prevapply_should_be_expanded
exception Sequential_logical_operator_primitives_must_be_expanded of
  Lambda.primitive
exception Var_within_closure_bound_multiple_times of Var_within_closure.t
exception Declared_closure_from_another_unit of Compilation_unit.t
exception Closure_id_is_bound_multiple_times of Closure_id.t
exception Set_of_closures_id_is_bound_multiple_times of Set_of_closures_id.t
exception Unbound_closure_ids of Closure_id.Set.t
exception Unbound_vars_within_closures of Var_within_closure.Set.t
exception Move_to_a_closure_not_in_the_free_variables
  of Variable.t * Variable.Set.t

exception Flambda_invariants_failed

(* CR-someday mshinwell: We should make "direct applications should not have
   overapplication" be an invariant throughout.  At the moment I think this is
   only true after [Inline_and_simplify] has split overapplications. *)

(* CR-someday mshinwell: What about checks for shadowed variables and
   symbols? *)


module Push_pop_invariants = struct
  type stack_t =
    | Root
    | Var (* Debug *)
    | Link of stack_type
    | Push of Trap_id.t * Continuation.t * stack_type

  and stack_type = stack_t ref

  type env = stack_type Continuation.Map.t

  let rec repr t =
    match !t with
    | Link s ->
      let u = repr s in
      t := u;
      u
    | v -> v

  let rec occur_check cont t checked =
    if t == checked then
      raise (Malformed_exception_continuation (cont, "recursive stack"));
    match !checked with
    | Var
    | Root -> ()
    | Link s
    | Push (_, _, s) ->
      occur_check cont t s

  let rec unify_stack cont t1 t2 =
    if t1 == t2 then ()
    else
      match repr t1, repr t2 with
      | Link _, _ | _, Link _ -> assert false
      | Var, _ ->
        occur_check cont t1 t2;
        t1 := Link t2
      | _, Var ->
        occur_check cont t2 t1;
        t2 := Link t1
      | Root, Root -> ()
      | Push (id1, c1, s1), Push (id2, c2, s2) ->
        if not (Trap_id.equal id1 id2) then
          raise (Malformed_exception_continuation (cont, "mismatched trap id"));
        if not (Continuation.equal c1 c2) then
          raise (Malformed_exception_continuation (cont, "mismatched continuation"));
        unify_stack cont s1 s2
      | Root, Push _ | Push _, Root ->
        raise (Malformed_exception_continuation (cont, "root stack is not empty"))

  let var () =
    ref (Var)

  let push id cont s =
    ref (Push(id, cont, s))

  let define table k stack =
    Continuation.Map.add k stack table

  let rec loop (env:env) current_stack (expr : Flambda.t) =
    match expr with
    | Let_mutable { body; _ }
    | Let { body; _ } ->
      loop env current_stack body
    | Let_cont { name; body; handler } ->
      let handler_stack = var () in
      begin match handler with
        | Alias cont ->
          let cont_stack =
            match Continuation.Map.find cont env with
            | exception Not_found ->
              Misc.fatal_errorf "Unbound continuation %a in Let_cont Alias %a"
                Continuation.print cont
                Flambda.print expr
            | cont_stack -> cont_stack
          in
          unify_stack cont handler_stack cont_stack
        | Handler { recursive; handler; _ } ->
          let env =
            match recursive with
            | Recursive -> define env name handler_stack
            | Nonrecursive -> env
          in
          loop env handler_stack handler
      end;
      let env = define env name handler_stack in
      loop env current_stack body
    | Apply_cont ( cont, exn, _args ) ->
      let cont_stack =
        match Continuation.Map.find cont env with
        | exception Not_found ->
          Misc.fatal_errorf "Unbound continuation %a in Apply_cont %a"
            Continuation.print cont
            Flambda.print expr
        | cont_stack -> cont_stack
      in
      let stack, cont_stack = match exn with
        | None ->
          current_stack,
          cont_stack
        | Some (Push { id; exn_handler }) ->
          push id exn_handler current_stack,
          cont_stack
        | Some (Pop { id; exn_handler }) ->
          current_stack,
          push id exn_handler cont_stack
      in
      unify_stack cont stack cont_stack
    | Apply { continuation; _ } ->
      let stack = current_stack in
      let cont_stack =
        match Continuation.Map.find continuation env with
        | exception Not_found ->
          Misc.fatal_errorf "Unbound continuation %a in application %a"
            Continuation.print continuation
            Flambda.print expr
        | cont_stack -> cont_stack
      in
      unify_stack continuation stack cont_stack
    | Switch (_,{ consts; blocks; failaction; _ } ) ->
      List.iter (fun (_, cont) ->
        let cont_stack =
          match Continuation.Map.find cont env with
          | exception Not_found ->
            Misc.fatal_errorf "Unbound continuation %a in switch %a"
              Continuation.print cont
              Flambda.print expr
          | cont_stack -> cont_stack
        in
        unify_stack cont cont_stack current_stack)
        consts;
      List.iter (fun (_, cont) ->
        let cont_stack =
          match Continuation.Map.find cont env with
          | exception Not_found ->
            Misc.fatal_errorf "Unbound continuation %a in switch %a"
              Continuation.print cont
              Flambda.print expr
          | cont_stack -> cont_stack
        in
        unify_stack cont cont_stack current_stack)
        blocks;
      begin match failaction with
      | None -> ()
      | Some cont ->
        let cont_stack =
          match Continuation.Map.find cont env with
          | exception Not_found ->
            Misc.fatal_errorf "Unbound continuation %a in switch %a"
              Continuation.print cont
              Flambda.print expr
          | cont_stack -> cont_stack
        in
        unify_stack cont cont_stack current_stack
      end
    | Proved_unreachable -> ()

  let well_formed_trap k (expr : Flambda.t) =
    let root = ref Root in
    let env = Continuation.Map.singleton k root in
    loop env root expr

  let check program =
    Flambda_iterators.iter_exprs_at_toplevel_of_program program
      ~f:well_formed_trap

end

module Continuation_scoping = struct

  let rec loop env (expr : Flambda.t) =
    match expr with
    | Let_mutable { body; _ }
    | Let { body; _ } ->
      loop env body
    | Let_cont { name; body; handler } ->
      begin match handler with
        | Alias cont -> begin
          match Continuation.Map.find cont env with
          | exception Not_found ->
            raise (Continuation_not_caught (cont, "alias"))
          | arity ->
            let env = Continuation.Map.add name arity env in
            loop env body
        end
        | Handler { recursive; handler; params; specialised_args; } ->
          let arity = List.length params in
          let env_with_handler =
            Continuation.Map.add name arity env
          in
          let handler_env =
            match recursive with
            | Recursive -> env_with_handler
            | Nonrecursive -> env
          in
          loop handler_env handler;
          loop env_with_handler body;
          ignore specialised_args (* CR mshinwell: fixme *)
      end;
    | Apply_cont ( cont, exn, args ) -> begin
      let arity =
        try Continuation.Map.find cont env with
        | Not_found ->
          raise (Continuation_not_caught (cont, "apply_cont"))
      in
      if not (List.length args = arity) then
        raise (Continuation_called_with_wrong_arity (cont, List.length args, arity));
      match exn with
      | None -> ()
      | Some (Push { id = _; exn_handler })
      | Some (Pop { id = _; exn_handler }) ->
        match Continuation.Map.find exn_handler env with
        | exception Not_found ->
          raise (Continuation_not_caught (exn_handler, "push/pop"))
        | arity ->
          if not (arity = 1) then
            raise (Continuation_called_with_wrong_arity (cont, 1, arity));
      end
    | Apply { continuation; _ } -> begin
        match Continuation.Map.find continuation env with
        | exception Not_found ->
          raise (Continuation_not_caught (continuation, "apply"))
        | arity ->
          if not (arity = 1) then
            raise (Continuation_called_with_wrong_arity (continuation, 1, arity));
      end
    | Switch (_,{ consts; blocks; failaction; _ } ) ->
      let check (_, cont) =
        match Continuation.Map.find cont env with
        | exception Not_found ->
          raise (Continuation_not_caught (cont, "switch"))
        | arity ->
          if not (arity = 0) then
            raise (Continuation_called_with_wrong_arity (cont, 0, arity));
      in
      List.iter check consts;
      List.iter check blocks;
      begin match failaction with
      | None -> ()
      | Some cont ->
        check ((), cont)
      end
    | Proved_unreachable -> ()

  let check_expr k (expr : Flambda.t) =
    let env = Continuation.Map.singleton k 1 in
    loop env expr

  let check program =
    Flambda_iterators.iter_exprs_at_toplevel_of_program program
      ~f:check_expr

end

let variable_and_symbol_invariants (program : Flambda.program) =
  let all_declared_variables = ref Variable.Set.empty in
  let declare_variable var =
    if Variable.Set.mem var !all_declared_variables then
      raise (Binding_occurrence_of_variable_already_bound var);
    all_declared_variables := Variable.Set.add var !all_declared_variables
  in
  let declare_variables vars =
    Variable.Set.iter declare_variable vars
  in
  let all_declared_mutable_variables = ref Mutable_variable.Set.empty in
  let declare_mutable_variable mut_var =
    if Mutable_variable.Set.mem mut_var !all_declared_mutable_variables then
      raise (Binding_occurrence_of_mutable_variable_already_bound mut_var);
    all_declared_mutable_variables :=
      Mutable_variable.Set.add mut_var !all_declared_mutable_variables
  in
  let add_binding_occurrence (var_env, mut_var_env, sym_env) var =
    let compilation_unit = Compilation_unit.get_current_exn () in
    if not (Variable.in_compilation_unit var compilation_unit) then
      raise (Binding_occurrence_not_from_current_compilation_unit var);
    declare_variable var;
    Variable.Set.add var var_env, mut_var_env, sym_env
  in
  let add_mutable_binding_occurrence (var_env, mut_var_env, sym_env) mut_var =
    let compilation_unit = Compilation_unit.get_current_exn () in
    if not (Mutable_variable.in_compilation_unit mut_var compilation_unit) then
      raise (Mutable_binding_occurrence_not_from_current_compilation_unit
        mut_var);
    declare_mutable_variable mut_var;
    var_env, Mutable_variable.Set.add mut_var mut_var_env, sym_env
  in
  let add_binding_occurrence_of_symbol (var_env, mut_var_env, sym_env) sym =
    if Symbol.Set.mem sym sym_env then
      raise (Binding_occurrence_of_symbol_already_bound sym)
    else
      var_env, mut_var_env, Symbol.Set.add sym sym_env
  in
  let add_binding_occurrences env vars =
    List.fold_left (fun env var -> add_binding_occurrence env var) env vars
  in
  let check_variable_is_bound (var_env, _, _) var =
    if not (Variable.Set.mem var var_env) then raise (Unbound_variable var)
  in
  let check_symbol_is_bound (_, _, sym_env) sym =
    if not (Symbol.Set.mem sym sym_env) then raise (Unbound_symbol sym)
  in
  let check_variables_are_bound env vars =
    List.iter (check_variable_is_bound env) vars
  in
  let check_mutable_variable_is_bound (_, mut_var_env, _) mut_var =
    if not (Mutable_variable.Set.mem mut_var mut_var_env) then begin
      raise (Unbound_mutable_variable mut_var)
    end
  in
  let rec loop env (flam : Flambda.t) =
    match flam with
    (* Expressions that can bind [Variable.t]s: *)
    | Let { var; defining_expr; body; _ } ->
      loop_named env defining_expr;
      loop (add_binding_occurrence env var) body
    | Let_mutable { var = mut_var; initial_value = var;
                    body; contents_kind } ->
      ignore_value_kind contents_kind;
      check_variable_is_bound env var;
      loop (add_mutable_binding_occurrence env mut_var) body
    | Let_cont { name; body;
        handler = Handler { params; recursive; handler;
          specialised_args; }; } ->
      ignore_continuation name;
      loop env body;
      ignore_rec_flag recursive;
      loop (add_binding_occurrences env params) handler;
      ignore specialised_args (* CR mshinwell: fixme *)
    | Let_cont { name; body; handler = Alias alias_of; } ->
      ignore_continuation name;
      loop env body;
      ignore_continuation alias_of
    (* Everything else: *)
    | Apply { kind = Function; func; continuation; args; call_kind; dbg; inline;
        specialise; } ->
      check_variable_is_bound env func;
      check_variables_are_bound env args;
      (* CR mshinwell: check continuations are bound *)
      ignore_continuation continuation;
      ignore_call_kind call_kind;
      ignore_debuginfo dbg;
      ignore_inline_attribute inline;
      ignore_specialise_attribute specialise
    | Apply { kind = Method { kind; obj; }; func; continuation; args; call_kind;
        dbg; inline; specialise; } ->
      ignore_meth_kind kind;
      check_variable_is_bound env obj;
      check_variable_is_bound env func;
      check_variables_are_bound env args;
      ignore_continuation continuation;
      ignore_call_kind call_kind;
      ignore_debuginfo dbg;
      ignore_inline_attribute inline;
      ignore_specialise_attribute specialise
    | Switch (arg, { numconsts; consts; numblocks; blocks; failaction; }) ->
      check_variable_is_bound env arg;
      ignore_int_set numconsts;
      ignore_int_set numblocks;
      List.iter (fun (n, e) ->
          ignore_int n;
          ignore_continuation e)
        consts;
      List.iter (fun (n, e) ->
          ignore_switch_block_pattern n;
          ignore_continuation e)
        blocks;
      Misc.may ignore_continuation failaction
    | Apply_cont (static_exn, trap_action, es) ->
      begin match trap_action with
      | None -> ()
      | Some (Push { id = _; exn_handler; })
      | Some (Pop { id = _; exn_handler; }) -> ignore_continuation exn_handler
      end;
      ignore_continuation static_exn;
      List.iter (check_variable_is_bound env) es
    | Proved_unreachable -> ()
  and loop_named env (named : Flambda.named) =
    match named with
    | Var var -> check_variable_is_bound env var
    | Symbol symbol -> check_symbol_is_bound env symbol
    | Const const -> ignore_const const
    | Allocated_const const -> ignore_allocated_const const
    | Read_mutable mut_var ->
      check_mutable_variable_is_bound env mut_var
    | Assign { being_assigned; new_value; } ->
      check_mutable_variable_is_bound env being_assigned;
      check_variable_is_bound env new_value
    | Read_symbol_field (symbol, index) ->
      check_symbol_is_bound env symbol;
      assert (index >= 0)  (* CR-someday mshinwell: add proper error *)
    | Set_of_closures set_of_closures ->
      loop_set_of_closures env set_of_closures
    | Project_closure { set_of_closures; closure_id; } ->
      check_variable_is_bound env set_of_closures;
      ignore_closure_id_set closure_id
    | Move_within_set_of_closures { closure; move } ->
      check_variable_is_bound env closure;
      ignore_closure_id_map ignore_closure_id move
    | Project_var { closure; var; } ->
      check_variable_is_bound env closure;
      ignore_closure_id_map ignore_var_within_closure var;
    | Prim (prim, args, dbg) ->
      ignore_primitive prim;
      check_variables_are_bound env args;
      ignore_debuginfo dbg
  and loop_set_of_closures env
      ({ Flambda.function_decls; free_vars; specialised_args;
          direct_call_surrogates = _; } as set_of_closures) =
      (* CR-soon mshinwell: check [direct_call_surrogates] *)
      let { Flambda.set_of_closures_id; set_of_closures_origin; funs; } =
        function_decls
      in
      ignore_set_of_closures_id set_of_closures_id;
      ignore_set_of_closures_origin set_of_closures_origin;
      let functions_in_closure = Variable.Map.keys funs in
      let variables_in_closure =
        Variable.Map.fold (fun var (var_in_closure : Flambda.specialised_to)
                  variables_in_closure ->
            (* [var] may occur in the body, but will effectively be renamed
               to [var_in_closure], so the latter is what we check to make
               sure it's bound. *)
            ignore_variable var;
            check_variable_is_bound env var_in_closure.var;
            Variable.Set.add var variables_in_closure)
          free_vars Variable.Set.empty
      in
      let all_params, all_free_vars =
        Variable.Map.fold (fun fun_var function_decl acc ->
            let all_params, all_free_vars = acc in
            (* CR-soon mshinwell: check function_decl.all_symbols *)
            let { Flambda.params; body; free_variables; stub; dbg; _ } =
              function_decl
            in
            assert (Variable.Set.mem fun_var functions_in_closure);
            ignore_bool stub;
            ignore_debuginfo dbg;
            (* Check that [free_variables], which is only present as an
               optimization, is not lying. *)
            let free_variables' = Flambda.free_variables body in
            if not (Variable.Set.subset free_variables' free_variables) then
              raise (Free_variables_set_is_lying (fun_var,
                free_variables, free_variables', function_decl));
            (* Check that every variable free in the body of the function is
               bound by either the set of closures or the parameter list. *)
            let acceptable_free_variables =
              Variable.Set.union
                (Variable.Set.union variables_in_closure functions_in_closure)
                (Variable.Set.of_list params)
            in
            let bad =
              Variable.Set.diff free_variables acceptable_free_variables
            in
            if not (Variable.Set.is_empty bad) then begin
              raise (Vars_in_function_body_not_bound_by_closure_or_params
                (bad, set_of_closures, fun_var))
            end;
            (* Check that parameters are unique across all functions in the
               declaration. *)
            let old_all_params_size = Variable.Set.cardinal all_params in
            let params = Variable.Set.of_list params in
            let params_size = Variable.Set.cardinal params in
            let all_params = Variable.Set.union all_params params in
            let all_params_size = Variable.Set.cardinal all_params in
            if all_params_size <> old_all_params_size + params_size then begin
              raise (Function_decls_have_overlapping_parameters all_params)
            end;
            (* Check that parameters and function variables are not
               bound somewhere else in the program *)
            declare_variables params;
            declare_variable fun_var;
            (* Check that the body of the functions is correctly structured *)
            let body_env =
              let (var_env, _, sym_env) = env in
              let var_env =
                Variable.Set.fold (fun var -> Variable.Set.add var)
                  free_variables var_env
              in
              (* Mutable variables cannot be captured by closures *)
              let mut_env = Mutable_variable.Set.empty in
              (var_env, mut_env, sym_env)
            in
            loop body_env body;
            all_params, Variable.Set.union free_variables all_free_vars)
          funs (Variable.Set.empty, Variable.Set.empty)
      in
      (* CR-soon pchambart: This is not a property that we can certainly
         ensure.
         If the function get inlined, it is possible for the inlined version
         to still use that variable. To be able to ensure that, we need to
         also ensure that the inlined version will certainly be transformed
         in a same way that can drop the dependency.
         mshinwell: This should get some thought after the first release to
         decide for sure what to do. *)
      (* Check that the free variables rewriting map in the set of closures
         does not contain variables in its domain that are not actually free
         variables of any of the function bodies. *)
      let bad_free_vars =
        Variable.Set.diff (Variable.Map.keys free_vars) all_free_vars
      in
(*
      if not (Variable.Set.is_empty bad_free_vars) then begin
        raise (Set_of_closures_free_vars_map_has_wrong_range bad_free_vars)
      end;
*)
      (* CR-someday pchambart: Ignore it to avoid the warning: get rid of that
         when the case is settled *)
      ignore (Set_of_closures_free_vars_map_has_wrong_range bad_free_vars);
      (* Check that free variables are not bound somewhere
         else in the program *)
      declare_variables (Variable.Map.keys free_vars);
      (* Check that every "specialised arg" is a parameter of one of the
         functions being declared, and that the variable to which the
         parameter is being specialised is bound. *)
      Variable.Map.iter (fun _inner_var
                (specialised_to : Flambda.specialised_to) ->
          check_variable_is_bound env specialised_to.var;
          match specialised_to.projection with
          | None -> ()
          | Some projection ->
            let projecting_from = Projection.projecting_from projection in
            if not (Variable.Map.mem projecting_from free_vars)
            then begin
              raise (Projection_must_be_a_free_var projection)
            end)
        free_vars;
      Variable.Map.iter (fun being_specialised
                (specialised_to : Flambda.specialised_to) ->
          if not (Variable.Set.mem being_specialised all_params) then begin
            raise (Specialised_arg_that_is_not_a_parameter being_specialised)
          end;
          check_variable_is_bound env specialised_to.var;
          match specialised_to.projection with
          | None -> ()
          | Some projection ->
            let projecting_from = Projection.projecting_from projection in
            if not (Variable.Map.mem projecting_from specialised_args)
            then begin
              raise (Projection_must_be_a_specialised_arg projection)
            end)
        specialised_args
  in
  let loop_constant_defining_value env
        (const : Flambda.constant_defining_value) =
    match const with
    | Flambda.Allocated_const c ->
      ignore_allocated_const c
    | Flambda.Block (tag,fields) ->
      ignore_tag tag;
      List.iter (fun (fields : Flambda.constant_defining_value_block_field) ->
          match fields with
          | Const c -> ignore_const c
          | Symbol s -> check_symbol_is_bound env s)
        fields
    | Flambda.Set_of_closures set_of_closures ->
      loop_set_of_closures env set_of_closures;
      (* Constant set of closures must not have free variables *)
      if not (Variable.Map.is_empty set_of_closures.free_vars) then
        assert false; (* TODO: correct error *)
      if not (Variable.Map.is_empty set_of_closures.specialised_args) then
        assert false; (* TODO: correct error *)
    | Flambda.Project_closure (symbol,closure_id) ->
      ignore_closure_id closure_id;
      check_symbol_is_bound env symbol
  in
  let rec loop_program_body env (program : Flambda.program_body) =
    match program with
    | Let_rec_symbol (defs, program) ->
      let env =
        List.fold_left (fun env (symbol, _) ->
            add_binding_occurrence_of_symbol env symbol)
          env defs
      in
      List.iter (fun (_, def) ->
          loop_constant_defining_value env def)
        defs;
      loop_program_body env program
    | Let_symbol (symbol, def, program) ->
      loop_constant_defining_value env def;
      let env = add_binding_occurrence_of_symbol env symbol in
      loop_program_body env program
    | Initialize_symbol (symbol, _tag, fields, program) ->
      List.iter (fun (field, cont) ->
          loop env field;
          ignore_continuation cont)
        fields;
      let env = add_binding_occurrence_of_symbol env symbol in
      loop_program_body env program
    | Effect (expr, cont, program) ->
      loop env expr;
      ignore_continuation cont;
      loop_program_body env program
    | End root ->
      check_symbol_is_bound env root
  in
  let env =
    Symbol.Set.fold (fun symbol env ->
        add_binding_occurrence_of_symbol env symbol)
      program.imported_symbols
      (Variable.Set.empty, Mutable_variable.Set.empty, Symbol.Set.empty)
  in
  loop_program_body env program.program_body

let primitive_invariants flam ~no_access_to_global_module_identifiers =
  Flambda_iterators.iter_named (function
      | Prim (prim, _, _) ->
        begin match prim with
        | Psequand | Psequor ->
          raise (Sequential_logical_operator_primitives_must_be_expanded prim)
        | Pgetglobal id ->
          if no_access_to_global_module_identifiers
            && not (Ident.is_predef_exn id) then
          begin
            raise (Access_to_global_module_identifier prim)
          end
        | Pidentity -> raise Pidentity_should_not_occur
        | Pdirapply -> raise Pdirapply_should_be_expanded
        | Prevapply -> raise Prevapply_should_be_expanded
        | _ -> ()
        end
      | _ -> ())
    flam

let declared_var_within_closure (flam:Flambda.program) =
  let bound = ref Var_within_closure.Set.empty in
  let bound_multiple_times = ref None in
  let add_and_check var =
    if Var_within_closure.Set.mem var !bound then begin
      bound_multiple_times := Some var
    end;
    bound := Var_within_closure.Set.add var !bound
  in
  Flambda_iterators.iter_on_set_of_closures_of_program
    ~f:(fun ~constant:_ { Flambda. free_vars; _ } ->
      Variable.Map.iter (fun id _ ->
          let var = Var_within_closure.wrap id in
          add_and_check var)
        free_vars)
    flam;
  !bound, !bound_multiple_times

let no_var_within_closure_is_bound_multiple_times (flam:Flambda.program) =
  match declared_var_within_closure flam with
  | _, Some var -> raise (Var_within_closure_bound_multiple_times var)
  | _, None -> ()

let every_declared_closure_is_from_current_compilation_unit flam =
  let current_compilation_unit = Compilation_unit.get_current_exn () in
  Flambda_iterators.iter_on_sets_of_closures (fun
        { Flambda. function_decls; _ } ->
      let compilation_unit =
        Set_of_closures_id.get_compilation_unit
          function_decls.set_of_closures_id
      in
      if not (Compilation_unit.equal compilation_unit current_compilation_unit)
      then raise (Declared_closure_from_another_unit compilation_unit))
    flam

let declared_closure_ids program =
  let bound = ref Closure_id.Set.empty in
  let bound_multiple_times = ref None in
  let add_and_check var =
    if Closure_id.Set.mem var !bound
    then bound_multiple_times := Some var;
    bound := Closure_id.Set.add var !bound
  in
  Flambda_iterators.iter_on_set_of_closures_of_program program
    ~f:(fun ~constant:_ { Flambda. function_decls; _; } ->
        Variable.Map.iter (fun id _ ->
            let var = Closure_id.wrap id in
            add_and_check var)
          function_decls.funs);
  !bound, !bound_multiple_times

let no_closure_id_is_bound_multiple_times program =
  match declared_closure_ids program with
  | _, Some closure_id ->
    raise (Closure_id_is_bound_multiple_times closure_id)
  | _, None -> ()

let declared_set_of_closures_ids program =
  let bound = ref Set_of_closures_id.Set.empty in
  let bound_multiple_times = ref None in
  let add_and_check var =
    if Set_of_closures_id.Set.mem var !bound
    then bound_multiple_times := Some var;
    bound := Set_of_closures_id.Set.add var !bound
  in
  Flambda_iterators.iter_on_set_of_closures_of_program program
    ~f:(fun ~constant:_ { Flambda. function_decls; _; } ->
        add_and_check function_decls.set_of_closures_id);
  !bound, !bound_multiple_times

let no_set_of_closures_id_is_bound_multiple_times program =
  match declared_set_of_closures_ids program with
  | _, Some set_of_closures_id ->
    raise (Set_of_closures_id_is_bound_multiple_times set_of_closures_id)
  | _, None -> ()

let used_closure_ids (program:Flambda.program) =
  let used = ref Closure_id.Set.empty in
  let f (flam : Flambda.named) =
    match flam with
    | Project_closure { closure_id; _} ->
      used := Closure_id.Set.union closure_id !used;
    | Move_within_set_of_closures { closure = _; move; } ->
      Closure_id.Map.iter (fun start_from move_to ->
        used := Closure_id.Set.add start_from !used;
        used := Closure_id.Set.add move_to !used)
        move
    | Project_var { closure = _; var } ->
      used := Closure_id.Set.union (Closure_id.Map.keys var) !used
    | Set_of_closures _ | Var _ | Symbol _ | Const _ | Allocated_const _
    | Prim _ | Assign _ | Read_mutable _ | Read_symbol_field _ -> ()
  in
  (* CR-someday pchambart: check closure_ids of constant_defining_values'
     project_closures *)
  Flambda_iterators.iter_named_of_program ~f program;
  !used

let used_vars_within_closures (flam:Flambda.program) =
  let used = ref Var_within_closure.Set.empty in
  let f (flam : Flambda.named) =
    match flam with
    | Project_var { closure = _; var; } ->
      Closure_id.Map.iter (fun _ var ->
        used := Var_within_closure.Set.add var !used)
        var
    | _ -> ()
  in
  Flambda_iterators.iter_named_of_program ~f flam;
  !used

let every_used_function_from_current_compilation_unit_is_declared
      (program:Flambda.program) =
  let current_compilation_unit = Compilation_unit.get_current_exn () in
  let declared, _ = declared_closure_ids program in
  let used = used_closure_ids program in
  let used_from_current_unit =
    Closure_id.Set.filter (fun cu ->
        Closure_id.in_compilation_unit cu current_compilation_unit)
      used
  in
  let counter_examples =
    Closure_id.Set.diff used_from_current_unit declared
  in
  if Closure_id.Set.is_empty counter_examples
  then ()
  else raise (Unbound_closure_ids counter_examples)

let every_used_var_within_closure_from_current_compilation_unit_is_declared
      (flam:Flambda.program) =
  let current_compilation_unit = Compilation_unit.get_current_exn () in
  let declared, _ = declared_var_within_closure flam in
  let used = used_vars_within_closures flam in
  let used_from_current_unit =
    Var_within_closure.Set.filter (fun cu ->
        Var_within_closure.in_compilation_unit cu current_compilation_unit)
      used
  in
  let counter_examples =
    Var_within_closure.Set.diff used_from_current_unit declared in
  if Var_within_closure.Set.is_empty counter_examples
  then ()
  else raise (Unbound_vars_within_closures counter_examples)

let _every_continuation_is_caught flam =
  let check env (flam : Flambda.t) =
    match flam with
    | Apply_cont (exn, _trap_action, _) ->
      (* CR mshinwell: look at the trap action *)
      if not (Continuation.Set.mem exn env)
      then raise (Continuation_not_caught (exn, ""))
    | _ -> ()
  in
  let rec loop env (flam : Flambda.t) =
    match flam with
    | Let_cont { name; body; handler = Handler { handler; _ }; _ } ->
      let env = Continuation.Set.add name env in
      loop env handler;
      loop env body
    | Let_cont { name; body; handler = Alias _; _ } ->
      let env = Continuation.Set.add name env in
      loop env body
    | exp ->
      check env exp;
      Flambda_iterators.apply_on_subexpressions (loop env)
        (fun (_ : Flambda.named) -> ()) exp
  in
  loop Continuation.Set.empty flam

let _every_continuation_is_caught_at_a_single_position flam =
  let caught = ref Continuation.Set.empty in
  let f (flam : Flambda.t) =
    match flam with
    | Let_cont { name; _ } ->
      if Continuation.Set.mem name !caught then
        raise (Continuation_caught_in_multiple_places name);
      caught := Continuation.Set.add name !caught
    | _ -> ()
  in
  Flambda_iterators.iter f (fun (_ : Flambda.named) -> ()) flam

let _every_move_within_set_of_closures_is_to_a_function_in_the_free_vars
      program =
  let moves = ref Closure_id.Map.empty in
  Flambda_iterators.iter_named_of_program program
    ~f:(function
        | Move_within_set_of_closures { move; _ } ->
          Closure_id.Map.iter (fun start_from move_to ->
            let moved_to =
              try Closure_id.Map.find start_from !moves with
              | Not_found -> Closure_id.Set.empty
            in
            moves :=
              Closure_id.Map.add start_from
                (Closure_id.Set.add move_to moved_to)
                !moves)
            move
        | _ -> ());
  Flambda_iterators.iter_on_set_of_closures_of_program program
    ~f:(fun ~constant:_ { Flambda.function_decls = { funs; _ }; _ } ->
        Variable.Map.iter (fun fun_var { Flambda.free_variables; _ } ->
            match Closure_id.Map.find (Closure_id.wrap fun_var) !moves with
            | exception Not_found -> ()
            | moved_to ->
              let missing_dependencies =
                Variable.Set.diff (Closure_id.unwrap_set moved_to)
                  free_variables
              in
              if not (Variable.Set.is_empty missing_dependencies) then
                raise (Move_to_a_closure_not_in_the_free_variables
                         (fun_var, missing_dependencies)))
          funs)

let check_exn ?(kind=Normal) ?(cmxfile=false) (flam:Flambda.program) =
  ignore kind;
  try
    variable_and_symbol_invariants flam;
    no_closure_id_is_bound_multiple_times flam;
    no_set_of_closures_id_is_bound_multiple_times flam;
    every_used_function_from_current_compilation_unit_is_declared flam;
    no_var_within_closure_is_bound_multiple_times flam;
    every_used_var_within_closure_from_current_compilation_unit_is_declared
      flam;
    (* CR-soon pchambart: This invariant is not maintained. It should be
       either relaxed or reformulated. Currently, it is safe to disable it as
       the potential related errors would result in fatal errors, not in
       miscompilations *)
    (* every_move_within_set_of_closures_is_to_a_function_in_the_free_vars
        flam; *)
    Flambda_iterators.iter_exprs_at_toplevel_of_program flam
      ~f:(fun _cont flam ->
        primitive_invariants flam
          ~no_access_to_global_module_identifiers:cmxfile;
(* CR mshinwell: We need to fix this.  It needs to take account of the
   return continuations including in "program" constructs probably *)
(*
      every_continuation_is_caught flam;
      every_continuation_is_caught_at_a_single_position flam;
*)
        every_declared_closure_is_from_current_compilation_unit flam);
    Push_pop_invariants.check flam;
    Continuation_scoping.check flam
  with exn -> begin
  (* CR-someday split printing code into its own function *)
    begin match exn with
    | Binding_occurrence_not_from_current_compilation_unit var ->
      Format.eprintf ">> Binding occurrence of variable marked as not being \
          from the current compilation unit: %a"
        Variable.print var
    | Mutable_binding_occurrence_not_from_current_compilation_unit mut_var ->
      Format.eprintf ">> Binding occurrence of mutable variable marked as not \
          being from the current compilation unit: %a"
        Mutable_variable.print mut_var
    | Binding_occurrence_of_variable_already_bound var ->
      Format.eprintf ">> Binding occurrence of variable that was already \
            bound: %a"
        Variable.print var
    | Binding_occurrence_of_mutable_variable_already_bound mut_var ->
      Format.eprintf ">> Binding occurrence of mutable variable that was \
            already bound: %a"
        Mutable_variable.print mut_var
    | Binding_occurrence_of_symbol_already_bound sym ->
      Format.eprintf ">> Binding occurrence of symbol that was already \
            bound: %a"
        Symbol.print sym
    | Unbound_variable var ->
      Format.eprintf ">> Unbound variable: %a" Variable.print var
    | Unbound_mutable_variable mut_var ->
      Format.eprintf ">> Unbound mutable variable: %a"
        Mutable_variable.print mut_var
    | Unbound_symbol sym ->
      Format.eprintf ">> Unbound symbol: %a %s"
        Symbol.print sym
        (Printexc.raw_backtrace_to_string (Printexc.get_callstack 100))
    | Vars_in_function_body_not_bound_by_closure_or_params
        (vars, set_of_closures, fun_var) ->
      Format.eprintf ">> Variable(s) (%a) in the body of a function \
          declaration (fun_var = %a) that is not bound by either the closure \
          or the function's parameter list.  Set of closures: %a"
        Variable.Set.print vars
        Variable.print fun_var
        Flambda.print_set_of_closures set_of_closures
    | Function_decls_have_overlapping_parameters vars ->
      Format.eprintf ">> Function declarations whose parameters overlap: \
          %a"
        Variable.Set.print vars
    | Specialised_arg_that_is_not_a_parameter var ->
      Format.eprintf ">> Variable in [specialised_args] that is not a \
          parameter of any of the function(s) in the corresponding \
          declaration(s): %a"
        Variable.print var
    | Projection_must_be_a_free_var var ->
      Format.eprintf ">> Projection %a in [free_vars] from a variable that is \
          not a (inner) free variable of the set of closures"
        Projection.print var
    | Projection_must_be_a_specialised_arg var ->
      Format.eprintf ">> Projection %a in [specialised_args] from a variable \
          that is not a (inner) specialised argument variable of the set of \
          closures"
        Projection.print var
    | Free_variables_set_is_lying (var, claimed, calculated, function_decl) ->
      Format.eprintf ">> Function declaration whose [free_variables] set (%a) \
          is not a superset of the result of [Flambda.free_variables] \
          applied to the body of the function (%a).  Declaration: %a"
        Variable.Set.print claimed
        Variable.Set.print calculated
        Flambda.print_function_declaration (var, function_decl)
    | Set_of_closures_free_vars_map_has_wrong_range vars ->
      Format.eprintf ">> [free_vars] map in set of closures has in its range \
          variables that are not free variables of the corresponding \
          functions: %a"
        Variable.Set.print vars
    | Sequential_logical_operator_primitives_must_be_expanded prim ->
      Format.eprintf ">> Sequential logical operator primitives must be \
          expanded (see closure_conversion.ml): %a"
        Printlambda.primitive prim
    | Var_within_closure_bound_multiple_times var ->
      Format.eprintf ">> Variable within a closure is bound multiple times: \
          %a"
        Var_within_closure.print var
    | Closure_id_is_bound_multiple_times closure_id ->
      Format.eprintf ">> Closure ID is bound multiple times: %a"
        Closure_id.print closure_id
    | Set_of_closures_id_is_bound_multiple_times set_of_closures_id ->
      Format.eprintf ">> Set of closures ID is bound multiple times: %a"
        Set_of_closures_id.print set_of_closures_id
    | Declared_closure_from_another_unit compilation_unit ->
      Format.eprintf ">> Closure declared as being from another compilation \
          unit: %a"
        Compilation_unit.print compilation_unit
    | Unbound_closure_ids closure_ids ->
      Format.eprintf ">> Unbound closure ID(s) from the current compilation \
          unit: %a"
        Closure_id.Set.print closure_ids
    | Unbound_vars_within_closures vars_within_closures ->
      Format.eprintf ">> Unbound variable(s) within closure(s) from the \
          current compilation_unit: %a"
        Var_within_closure.Set.print vars_within_closures
    | Continuation_not_caught (static_exn, s) ->
      Format.eprintf ">> Uncaught continuation variable %a: %s"
        Continuation.print static_exn s
    | Continuation_caught_in_multiple_places static_exn ->
      Format.eprintf ">> Continuation variable caught in multiple places: %a"
        Continuation.print static_exn
    | Access_to_global_module_identifier prim ->
      (* CR-someday mshinwell: backend-specific checks should move to another
         module, in the asmcomp/ directory. *)
      Format.eprintf ">> Forbidden access to a global module identifier (not \
          allowed in Flambda that will be exported to a .cmx file): %a"
        Printlambda.primitive prim
    | Pidentity_should_not_occur ->
      Format.eprintf ">> The Pidentity primitive should never occur in an \
        Flambda expression (see closure_conversion.ml)"
    | Pdirapply_should_be_expanded ->
      Format.eprintf ">> The Pdirapply primitive should never occur in an \
        Flambda expression (see closure_conversion.ml); use Apply instead"
    | Prevapply_should_be_expanded ->
      Format.eprintf ">> The Prevapply primitive should never occur in an \
        Flambda expression (see closure_conversion.ml); use Apply instead"
    | Move_to_a_closure_not_in_the_free_variables (start_from, move_to) ->
      Format.eprintf ">> A Move_within_set_of_closures from the closure %a \
        to closures that are not parts of its free variables: %a"
          Variable.print start_from
          Variable.Set.print move_to
    | exn -> raise exn
    end;
    Format.eprintf "\n@?";
    raise Flambda_invariants_failed
  end
