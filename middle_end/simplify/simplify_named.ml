(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2017 OCamlPro SAS                                    *)
(*   Copyright 2014--2017 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module B = Inlining_cost.Benefit
module E = Simplify_env
module R = Simplify_result
module T = Flambda_type

type named_simplifier =
  (Variable.t * Flambda.Named.t) list * Flambda.Reachable.t
    * Flambda_type.t * R.t

let type_for_const (const : Flambda.Const.t) =
  match const with
  (* CR mshinwell: unify terminology: "untagged" vs "naked" *)
  | Untagged_immediate i -> T.this_naked_immediate i
  | Tagged_immediate i -> T.this_tagged_immediate i
  | Naked_float f -> T.this_naked_float f
  | Naked_int32 n -> T.this_naked_int32 n
  | Naked_int64 n -> T.this_naked_int64 n
  | Naked_nativeint n -> T.this_naked_nativeint n

let type_for_allocated_const (const : Allocated_const.t) =
  match const with
  | Mutable_string { initial_value; } ->
    T.mutable_string ~size:(String.length initial_value)
  | Immutable_string s -> T.this_immutable_string s
  | Boxed_int32 i -> T.this_boxed_int32 i
  | Boxed_int64 i -> T.this_boxed_int64 i
  | Boxed_nativeint i -> T.this_boxed_nativeint i
  | Boxed_float f -> T.this_boxed_float f
  | Mutable_float_array { initial_value; } ->
    T.mutable_float_array ~size:(List.length initial_value)
  | Immutable_float_array fs ->
    T.this_immutable_float_array (Array.of_list fs)

(* Simplify an expression that takes a set of closures and projects an
   individual closure from it. *)
let simplify_project_closure env r
      ~(project_closure : Projection.Project_closure.t) : named_simplifier =
  let set_of_closures, set_of_closures_ty =
    freshen_and_squash_aliases env project_closure.set_of_closures
  in
  let closure_id = project_closure.closure_id in
  let importer = E.importer env in
  match T.prove_set_of_closures ~importer set_of_closures_ty with
  | Wrong ->
    let ty = Flambda_type.bottom (Flambda_kind.value Must_scan) in
    let term = Flambda.Reachable.invalid () in
    [], ty, term
  | Unknown ->
    let ty = Flambda_type.bottom (Flambda_kind.value Must_scan) in
    let term =
      Flambda.Reachable.reachable (Project_closure {
        set_of_closures;
        closure_id;
      }
    in
    [], ty, term
  | Known set ->
(*
    begin match Closure_id.Set.elements closure_id with
      | _ :: _ :: _ ->
        Format.printf "Set of closures type is not a singleton \
            in project closure@ %a@ %a@."
          T.print set_of_closures_type
          Projection.print_project_closure project_closure
      | [] ->
        Format.printf "Set of closures type is empty in project \
            closure@ %a@ %a@."
          T.print set_of_closures_type
          Projection.print_project_closure project_closure
      | _ ->
        ()
    end;
*)
    let projecting_from =
      match Flambda_type.Set_of_closures.set_of_closures_var set with
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
      let var, var_ty = freshen_and_squash_aliases env var in
      let r = R.map_benefit r (B.remove_projection projection) in
      if Flambda_type.is_bottom ~importer var_ty then
        [], Flambda.Reachable.invalid (), r
      else
        [], Flambda.Reachable.reachable (Var var), r
    | None ->
      assert false
(* XXX for pchambart to fix: 
      let if_not_reference_recursive_function_directly ()
        : (Variable.t * Flambda.Named.t) list * Flambda.Named.t_reachable
            * R.t =
        let set_of_closures_var =
          match set_of_closures_var with
          | Some set_of_closures_var' when E.mem env set_of_closures_var' ->
            set_of_closures_var
          | Some _ | None -> None
        in
        let ty =
          T.closure ?set_of_closures_var
            (Closure_id.Map.of_set (fun _ -> value_set_of_closures)
                closure_id)
        in
        [], Reachable (Project_closure { set_of_closures; closure_id; }),
          ty
      in
      match Closure_id.Set.get_singleton closure_id with
      | None ->
        if_not_reference_recursive_function_directly ()
      | Some closure_id ->
        match reference_recursive_function_directly env closure_id with
        | Some (flam, ty) -> [], Reachable flam, ty
        | None ->
          if_not_reference_recursive_function_directly ()
*)

(* Simplify an expression that, given one closure within some set of
   closures, returns another closure (possibly the same one) within the
   same set. *)
let simplify_move_within_set_of_closures env r
      ~(move_within_set_of_closures : Projection.Move_within_set_of_closures.t)
      : named_simplifier =
  let closure, closure_ty =
    freshen_and_squash_aliases env move_within_set_of_closures.closure
  in
  match T.prove_closure_allowing_unresolved closure_ty with
  | Wrong ->
    Misc.fatal_errorf "Wrong Flambda type when moving within set of \
        closures.  Flambda type: %a  Term: %a"
      T.print closure_ty
      Flambda.print_move_within_set_of_closures move_within_set_of_closures
  | Unresolved sym ->
    [], Reachable (Move_within_set_of_closures {
        closure;
        move = move_within_set_of_closures.move;
      }),
      ret r (T.unresolved_symbol sym)
  | Unknown ->
    [], Reachable (Move_within_set_of_closures {
        closure;
        move = move_within_set_of_closures.move;
      }),
      ret r (T.unknown Value Other)
  | Unknown_because_of_unresolved_value value ->
    (* For example: a move upon a (move upon a closure whose .cmx file
        is missing). *)
    [], Reachable (Move_within_set_of_closures {
        closure;
        move = move_within_set_of_closures.move;
      }),
      ret r (T.unknown Value (Unresolved_value value))
  | Ok (value_closures, set_of_closures_var, set_of_closures_symbol) ->
    let () =
      match Closure_id.Map.bindings value_closures with
      | _ :: _ :: _ ->
        Format.printf "Closure type is not a singleton in \
            move@ %a@ %a@."
          T.print closure_ty
          Projection.print_move_within_set_of_closures
          move_within_set_of_closures
      | [] ->
        Format.printf "Closure type is empty in move@ %a@ %a@."
          T.print closure_ty
          Projection.print_move_within_set_of_closures
          move_within_set_of_closures
      | _ ->
        ()
    in
    (* Freshening of the move. *)
    let move, type_map =
      Closure_id.Map.fold
        (fun closure_id_in_type
              (value_set_of_closures:T.set_of_closures)
              (move, type_map) ->
          (* Pas efficace: on refait le freshening de tout pour ne
             garder que la partie pertinente, mais n'est pas très
             grave parce que ces map sont petites (normalement) *)
          let freshened_move =
            Freshening.freshen_move_within_set_of_closures
              ~closure_freshening:value_set_of_closures.freshening
              move_within_set_of_closures.move
          in
          let start_from = closure_id_in_type in
          let move_to =
            try Closure_id.Map.find start_from freshened_move with
            | Not_found ->
              Misc.fatal_errorf "Move %a freshened to %a does not contain \
                                  projection for %a@.  Type is:@ %a@.\
                                  Environment:@ %a@."
                Projection.print_move_within_set_of_closures
                  move_within_set_of_closures
                (Closure_id.Map.print Closure_id.print) freshened_move
                Closure_id.print start_from
                (Closure_id.Map.print T.print_value_set_of_closures)
                  value_closures
                E.print env
          in
          assert(not (Closure_id.Map.mem start_from move));
          Closure_id.Map.add start_from move_to move,
          Closure_id.Map.add move_to value_set_of_closures type_map)
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
      let ty = T.closure ty_map in
      let move_within : Projection.Move_within_set_of_closures.t =
        { closure; move; }
      in
      [], Reachable (Move_within_set_of_closures move_within), ty
    | Some (_start_from, value_set_of_closures),
      Some (start_from, move_to) ->
      match E.find_projection env ~projection with
      | Some var ->
        freshen_and_squash_aliases_named env var ~f:(fun _env var var_ty ->
          let r = R.map_benefit r (B.remove_projection projection) in
          [], Reachable (Var var), var_ty)
      | None ->
        match reference_recursive_function_directly env move_to with
        | Some (flam, ty) -> [], Reachable flam, ty
        | None ->
          if Closure_id.equal start_from move_to then
            (* Moving from one closure to itself is a no-op.  We can return an
               [Var] since we already have a variable bound to the closure. *)
            [], Reachable (Var closure), closure_ty
          else
            match set_of_closures_var with
            | Some set_of_closures_var when E.mem env set_of_closures_var ->
              (* A variable bound to the set of closures is in scope,
                 meaning we can rewrite the [Move_within_set_of_closures] to a
                 [Project_closure]. *)
              let project_closure : Projection.Project_closure.t =
                { set_of_closures = set_of_closures_var;
                  closure_id = Closure_id.Set.singleton move_to;
                }
              in
              let ty =
                T.closure ~set_of_closures_var
                  (Closure_id.Map.singleton move_to value_set_of_closures)
              in
              [], Reachable (Project_closure project_closure), ty
            | Some _ | None ->
              match set_of_closures_symbol with
              | Some set_of_closures_symbol ->
                let set_of_closures_var = Variable.create "symbol" in
                let project_closure : Projection.Project_closure.t =
                  { set_of_closures = set_of_closures_var;
                    closure_id = Closure_id.Set.singleton move_to;
                  }
                in
                let ty =
                  T.closure ~set_of_closures_var ~set_of_closures_symbol
                    (Closure_id.Map.singleton move_to value_set_of_closures)
                in
                let bindings : (Variable.t * Flambda.Named.t) list = [
                  set_of_closures_var, Symbol set_of_closures_symbol;
                ]
                in
                bindings, Reachable (Project_closure project_closure),
                  ty
              | None ->
                (* The set of closures is not available in scope, and we
                  have no other information by which to simplify the move. *)
                let move_within : Projection.Move_within_set_of_closures.t =
                  { closure; move; }
                in
                let ty = T.closure ty_map in
                [], Reachable (Move_within_set_of_closures move_within), ty

let rec simplify_project_var env r ~(project_var : Projection.Project_var.t)
      : named_simplifier =
  let closure, closure_ty =
    freshen_and_squash_aliases env project_var.closure
  in
  match T.prove_closure_allowing_unresolved closure_ty with
  | Ok (value_closures, _set_of_closures_var, _set_of_closures_symbol) ->
(*
    let () =
      match Closure_id.Map.bindings value_closures with
        | _ :: _ :: _ ->
          Format.printf "Closure type is not a singleton in \
              project@ %a@ %a@."
            T.print ty
            Projection.print_project_var project_var
        | [] ->
          Format.printf "Closure type is empty in project@ %a@ %a@."
            T.print ty
            Projection.print_project_var project_var
        | _ ->
          ()
    in
*)
    (* Freshening of the projection *)
    let project_var_var, ty =
      Closure_id.Map.fold
        (fun closure_id_in_type
          (value_set_of_closures : T.set_of_closures)
          (project_var_var, set_type) ->
          let freshened_var =
            Freshening.freshen_project_var project_var.var
              ~closure_freshening:value_set_of_closures.freshening
          in
          let closure_id = closure_id_in_type in
          let var =
            try Closure_id.Map.find closure_id_in_type freshened_var with
            | Not_found ->
              Misc.fatal_errorf "When simplifying [Project_var], the \
                closure ID %a in the type of the set of closures \
                did not match any closure ID in the [Project_var] term %a \
                freshened to %a. \
                Type: %a@."
                Closure_id.print closure_id_in_type
                Projection.print_project_var project_var
                (Closure_id.Map.print Var_within_closure.print) freshened_var
                Flambda_type.print ty
          in
          let set_type =
            let ty = T.type_for_bound_var value_set_of_closures var in
            let really_import_type = E.really_import_type env in
            T.join ~really_import_type ty set_type
          in
          Closure_id.Map.add closure_id var project_var_var,
          set_type)
        value_closures (Closure_id.Map.empty, T.bottom)
    in
    let projection : Projection.t =
      Project_var {
        closure;
        var = project_var_var;
      }
    in
    begin match E.find_projection env ~projection with
    | Some var ->
      freshen_and_squash_aliases_named env var ~f:(fun _env var var_ty ->
        let r = R.map_benefit r (B.remove_projection projection) in
        [], Reachable (Var var), var_ty)
    | None ->
      let expr : Flambda.Named.t =
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
      simpler_equivalent_term env r expr ty
    end
  | Unknown ->
    [], Flambda.Reachable.reachable (Project_var { project_var with closure }),
      r
  | Wrong ->
    [], Flambda.Reachable.invalid (), r

let simplify_set_of_closures original_env r
      (set_of_closures : Flambda.Set_of_closures.t)
      : Flambda.Set_of_closures.t * R.t * Freshening.Project_var.t =
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
  let free_vars, function_decls, parameter_types,
      internal_value_set_of_closures, set_of_closures_env =
    Simplify_aux.prepare_to_simplify_set_of_closures ~env
      ~set_of_closures ~function_decls ~only_for_function_decl:None
      ~freshen:true
  in
  let continuation_param_uses = Continuation.Tbl.create 42 in
  let simplify_function fun_var (function_decl : Flambda.Function_declaration.t)
        (funs, used_params, r)
        : Flambda.Function_declaration.t Variable.Map.t * Variable.Set.t * R.t =
    let closure_env =
      Simplify_aux.prepare_to_simplify_closure ~function_decl
        ~free_vars ~parameter_types ~set_of_closures_env
    in
    let continuation_param, closure_env =
      let continuation_param, freshening =
        Freshening.add_static_exception (E.freshening closure_env)
          function_decl.continuation_param
      in
      let cont_type =
        Continuation_approx.create_unknown ~name:continuation_param
          ~num_params:function_decl.return_arity
      in
      let closure_env =
        E.add_continuation (E.set_freshening closure_env freshening)
          continuation_param cont_type
      in
      continuation_param, closure_env
    in
    let body, r =
      E.enter_closure closure_env ~closure_id:(Closure_id.wrap fun_var)
        ~inline_inside:
          (Inlining_decision.should_inline_inside_declaration function_decl)
        ~dbg:function_decl.dbg
        ~f:(fun body_env ->
          assert (E.inside_set_of_closures_declaration
            function_decls.set_of_closures_origin body_env);
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
            Simplify_aux.initial_inlining_threshold
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
      Flambda.Function_declaration.create ~params:function_decl.params
        ~continuation_param:continuation_param
        ~return_arity:function_decl.return_arity
        ~body ~stub:function_decl.stub ~dbg:function_decl.dbg
        ~inline ~specialise:function_decl.specialise
        ~is_a_functor:function_decl.is_a_functor
        ~closure_origin:function_decl.closure_origin
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
    Flambda.Function_declarations.update function_decls ~funs
  in
  let function_decls =
    (* CR mshinwell: I'm not sure about this "round" condition.  It seems
       though that doing [Unbox_returns] too early may be
       detrimental, as it prevents small functions being inlined *)
    if E.never_inline env
      || E.round env < 2
      || E.never_unbox_continuations env
    then
      function_decls, Variable.Map.empty
    else
      let continuation_param_uses =
        Continuation.Tbl.to_map continuation_param_uses
      in
      Unbox_returns.run ~continuation_uses:continuation_param_uses
        ~function_decls ~backend:(E.backend env)
  in
  let invariant_params =
    lazy (Invariant_params.Functions.invariant_params_in_recursion
      function_decls ~backend:(E.backend env))
  in
  let value_set_of_closures =
    T.create_set_of_closures ~function_decls
      ~bound_vars:internal_value_set_of_closures.bound_vars
      ~size:(lazy (Flambda.Function_declarations.size function_decls))
      ~invariant_params
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
    Flambda.Set_of_closures.create ~function_decls
      ~free_vars:(Variable.Map.map fst free_vars)
      ~direct_call_surrogates
  in
  let r = ret r (T.set_of_closures value_set_of_closures) in
  set_of_closures, r, value_set_of_closures.freshening

let simplify_primitive env r prim args dbg : named_simplifier =
  let dbg = E.add_inlined_debuginfo env ~dbg in
  freshen_and_squash_aliases_list_named env args ~f:(fun env args args_tys ->
    let tree = Flambda.Prim (prim, args, dbg) in
    let projection : Projection.t = Prim (prim, args) in
    begin match E.find_projection env ~projection with
    | Some var ->
      (* CSE of pure primitives.
         The [Pisint] case in particular is also used when unboxing
         continuation parameters of variant type. *)
      freshen_and_squash_aliases_named env var ~f:(fun _env var var_ty ->
        let r = R.map_benefit r (B.remove_projection projection) in
        [], Reachable (Var var), var_ty)
    | None ->
      let default () : (Variable.t * Flambda.Named.t) list
            * Flambda.Named.t_reachable * R.t =
        let named, ty, benefit =
          (* CR mshinwell: if the primitive is pure, add it to the environment
             so CSE will work.  Need to be careful if the variable being
             bound is a continuation argument *)
          let module Backend = (val (E.backend env) : Backend_intf.S) in
          Simplify_primitives.primitive prim (args, args_tys) tree dbg
            ~size_int:Backend.size_int ~big_endian:Backend.big_endian
        in
        let r = R.map_benefit r (B.(+) benefit) in
        let ty =
          match prim with
          | Popaque -> T.unknown Other
          | _ -> ty
        in
        [], Reachable (named, value_kind), ty
      in
      begin match prim, args, args_tys with
      | Pgetglobal _, _, _ ->
        Misc.fatal_error "Pgetglobal is forbidden in Simplify"
      | Pfield field_index, [arg], [arg_ty] ->
        let projection : Projection.t = Prim (Pfield field_index, [arg]) in
        begin match E.find_projection env ~projection with
        | Some var ->
          freshen_and_squash_aliases_named env var ~f:(fun _env var var_ty ->
            let r = R.map_benefit r (B.remove_projection projection) in
            [], Reachable (Var var), var_ty)
        | None ->
          begin match T.get_field arg_ty ~field_index with
          | Invalid _ ->
            [], Flambda.Reachable.invalid (), r
          | Ok ty ->
            let tree, ty =
              match arg_ty.symbol with
              (* If the [Pfield] is projecting directly from a symbol, rewrite
                  the expression to [Read_symbol_field]. *)
              | Some (symbol, None) ->
                let ty =
                  T.augment_with_symbol_field ty symbol field_index
                in
                Flambda.Read_symbol_field (symbol, field_index), ty
              | None | Some (_, Some _ ) ->
                (* This [Pfield] is either not projecting from a symbol at
                   all, or it is the projection of a projection from a
                   symbol. *)
                let ty' = E.really_import_ty env ty in
                tree, ty'
            in
            simpler_equivalent_term env r tree ty
          end
        end
      | Pfield _, _, _ -> Misc.fatal_error "Pfield arity error"
      | (Parraysetu kind | Parraysets kind),
          [_block; _field; _value],
          [block_ty; field_ty; value_ty] ->
        if T.invalid_to_mutate block_ty then begin
          [], Flambda.Reachable.invalid (), r
        end else begin
          let size = T.length_of_array block_ty in
          let index = T.reify_as_int field_ty in
          let bounds_check_definitely_fails =
            match size, index with
            | Some size, _ when size <= 0 ->
              assert (size = 0);  (* see [Simple_value_ty] *)
              true
            | Some size, Some index ->
              (* This is ok even in the presence of [Obj.truncate], since that
                 can only make blocks smaller. *)
              index >= 0 && index < size
            | _, _ -> false
          in
          let convert_to_raise =
            match prim with
            | Parraysets _ -> bounds_check_definitely_fails
            | Parraysetu _ -> false
            | _ -> assert false  (* see above *)
          in
          if convert_to_raise then begin
            (* CR mshinwell: move to separate function *)
            let invalid_argument_var = Variable.create "invalid_argument" in
            let invalid_argument : Flambda.Named.t =
              let module Backend = (val (E.backend env) : Backend_intf.S) in
              Symbol (Backend.symbol_for_global'
                Predef.ident_invalid_argument)
            in
            let msg_var = Variable.create "msg" in
            let msg : Flambda.Named.t =
              Allocated_const (String "index out of bounds")
            in
            let exn_var = Variable.create "exn" in
            let exn : Flambda.Named.t =
              Prim (Pmakeblock (0, Immutable, None),
                [invalid_argument_var; msg_var], dbg)
            in
            let bindings = [
                invalid_argument_var, invalid_argument;
                msg_var, msg;
                exn_var, exn;
              ]
            in
            bindings, Reachable (Prim (Praise Raise_regular, [exn_var], dbg)),
              T.bottom
          end else begin
            let kind =
              match T.is_float_array block_ty, T.is_boxed_float value_ty with
              | (true, _)
              | (_, true) ->
                begin match kind with
                | Pfloatarray | Pgenarray -> ()
                | Paddrarray | Pintarray ->
                  (* CR pchambart: Do a proper warning here *)
                  Misc.fatal_errorf "Assignment of a float to a specialised \
                                    non-float array: %a"
                    Flambda.Named.print tree
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
            [], Reachable (Prim (prim, args, dbg)), ret r (T.unknown Other)
          end
        end
      | Psetfield _, _block::_, block_ty::_ ->
        if T.invalid_to_mutate block_ty then begin
          [], Flambda.Reachable.invalid (), r
        end else begin
          [], Reachable tree, ret r (T.unknown Other)
        end
      | (Psetfield _ | Parraysetu _ | Parraysets _), _, _ ->
        Misc.fatal_error "Psetfield / Parraysetu / Parraysets arity error"
      | Pisint, [_arg], [arg_ty] ->
        begin match T.reify_as_block_or_immediate arg_ty with
        | Wrong -> default ()
        | Immediate ->
          let r = R.map_benefit r B.remove_prim in
          let const_true = Variable.create "true" in
          [const_true, Const (Int 1)], Reachable (Var const_true),
            ret r (T.int 1)
        | Block ->
          let r = R.map_benefit r B.remove_prim in
          let const_false = Variable.create "false" in
          [const_false, Const (Int 0)], Reachable (Var const_false),
            ret r (T.int 0)
        end
      | Pisint, _, _ -> Misc.fatal_error "Pisint arity error"
      | Pgettag, [_arg], [arg_ty] ->
        begin match T.reify_as_block arg_ty with
        | Wrong -> default ()
        | Ok (tag, _fields) ->
          let r = R.map_benefit r B.remove_prim in
          let const_tag = Variable.create "tag" in
          let tag = Tag.to_int tag in
          [const_tag, Const (Int tag)], Reachable (Var const_tag),
            ret r (T.int tag)
        end
      | Pgettag, _, _ -> Misc.fatal_error "Pgettag arity error"
      | Parraylength _, [_arg], [arg_ty] ->
        begin match T.length_of_array arg_ty with
        | None -> default ()
        | Some length ->
          let r = R.map_benefit r B.remove_prim in
          let const_length = Variable.create "length" in
          [const_length, Const (Int length)], Reachable (Var const_length),
            ret r (T.int length)
        end
      | Parraylength _, _, _ -> Misc.fatal_error "Parraylength arity error"
      | (Psequand | Psequor), _, _ ->
        Misc.fatal_error "Psequand and Psequor must be expanded (see \
            handling in closure_conversion.ml)"
      | _, _, _ -> default ()
      end
    end)

(** [simplify_named] returns:
    - extra [Let]-bindings to be inserted prior to the one being simplified;
    - the simplified [named];
    - the new result structure. *)
let simplify_named env r (tree : Flambda.Named.t) : named_simplifier =
  match tree with
  | Var var ->
    let var, var_ty = freshen_and_squash_aliases env var in

  | Symbol sym ->
    let ty = E.find_or_load_symbol env sym in
    simpler_equivalent_term r tree ty
  | Const cst -> [], Reachable tree, ret r (type_for_const cst)
  | Allocated_const cst ->
    [], Reachable tree, ret r (type_for_allocated_const cst)
  | Read_mutable mut_var ->
    (* See comment on the [Assign] case. *)
    let mut_var =
      Freshening.apply_mutable_variable (E.freshening env) mut_var
    in
    [], Reachable (Read_mutable mut_var), ret r (T.unknown Value Other)
  | Read_symbol_field (symbol, field_index) ->
    let ty = E.find_or_load_symbol env symbol in
    begin match T.get_field ty ~field_index with
    | (Invalid _) as invalid -> [], invalid, r
    | Ok flambda_type ->
      let flambda_type = T.augment_with_symbol_field ty symbol field_index in
      simpler_equivalent_term env r tree ty
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
         the "closure freshening" thing in the Flambda type which is hard
         to deal with. *)
      let r = R.roll_back_continuation_uses r cont_usage_snapshot in
      let bindings, set_of_closures, r =
        let env = E.set_never_inline env in
        simplify_newly_introduced_let_bindings env r ~bindings
          ~around:((Set_of_closures set_of_closures) : Flambda.Named.t)
      in
      let ty = R.inferred_type r in
      let value_set_of_closures =
        match T.strict_check_type_for_set_of_closures ty with
        | Wrong ->
          Misc.fatal_errorf "Unexpected Flambda type returned from \
              simplification of [%s] result: %a"
            pass_name T.print ty
        | Ok (_var, value_set_of_closures) ->
          let freshening =
            Freshening.Project_var.compose ~earlier:first_freshening
              ~later:value_set_of_closures.freshening
          in
          T.update_freshening_of_value_set_of_closures value_set_of_closures
            ~freshening
      in
      bindings, set_of_closures,
        (ret r (T.set_of_closures value_set_of_closures))
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
          | None -> [], Reachable (Set_of_closures set_of_closures), r
    end
  | Project_closure project_closure ->
    simplify_project_closure env r ~project_closure
  | Project_var project_var -> simplify_project_var env r ~project_var
  | Move_within_set_of_closures move_within_set_of_closures ->
    simplify_move_within_set_of_closures env r ~move_within_set_of_closures
  | Assign { being_assigned; new_value; } ->
    (* No need to use something like [freshen_and_squash_aliases]: the
       Flambda type of [being_assigned] is always unknown. *)
    let being_assigned =
      Freshening.apply_mutable_variable (E.freshening env) being_assigned
    in
    freshen_and_squash_aliases_named env new_value ~f:(fun _env new_value _type ->
      [], Reachable (Assign { being_assigned; new_value; }),
        ret r (T.unknown Value Other))
  | Prim (prim, args, dbg) -> simplify_primitive env r prim args dbg
