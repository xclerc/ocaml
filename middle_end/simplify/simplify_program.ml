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

module Program = Flambda_static.Program
module Program_body = Flambda_static.Program_body

let constant_defining_value_type
    env
    (constant_defining_value:Flambda_static.Constant_defining_value.t) =
  match constant_defining_value with
  | Allocated_const const ->
    type_for_allocated_const const
  | Block (tag, fields) ->
    let fields =
      List.map
        (function
          | Flambda.Symbol sym -> begin
              match E.find_symbol_opt env sym with
              | Some ty -> ty
              | None -> T.unknown Value (Unresolved_value (Symbol sym))
            end
          | Flambda.Const cst -> type_for_const cst)
        fields
    in
    T.block tag (Array.of_list fields)
 | Set_of_closures { function_decls; free_vars; specialised_args } ->
    (* At toplevel, there is no freshening currently happening (this
       cannot be the body of a currently inlined function), so we can
       keep the original set_of_closures in the Flambda type. *)
    assert(E.freshening env = Freshening.empty);
    assert(Variable.Map.is_empty free_vars);
    assert(Variable.Map.is_empty specialised_args);
    let invariant_params =
      lazy (Invariant_params.Functions.invariant_params_in_recursion
        function_decls ~backend:(E.backend env))
    in
    let value_set_of_closures =
      T.create_set_of_closures ~function_decls
        ~size:(lazy (Flambda.Function_declarations.size function_decls))
        ~bound_vars:Var_within_closure.Map.empty
        ~invariant_params
        ~specialised_args:Variable.Map.empty
        ~freshening:Freshening.Project_var.empty
        ~direct_call_surrogates:Closure_id.Map.empty
    in
    T.set_of_closures value_set_of_closures
  | Project_closure (set_of_closures_symbol, closure_id) -> begin
      match E.find_symbol_opt env set_of_closures_symbol with
      | None -> T.unresolved_symbol set_of_closures_symbol
      | Some set_of_closures_type ->
        let reified_type =
          T.reify_as_set_of_closures set_of_closures_type
        in
        match reified_type with
        | Ok (_, value_set_of_closures) ->
          let closure_id =
            T.freshen_and_check_closure_id value_set_of_closures
              (Closure_id.Set.singleton closure_id)
          in
          T.closure
            (Closure_id.Map.of_set (fun _ -> value_set_of_closures) closure_id)
        | Unresolved sym -> T.unresolved_symbol sym
        | Unknown kind ->
          begin match kind with
          | Value -> ()
          | _ ->
            Misc.fatal_errorf "Project_closure %a from %a has wrong kind %a"
              Closure_id.print closure_id
              Symbol.print set_of_closures_symbol
              Flambda_kind.print kind
          end;
          T.unknown Value Other
        | Wrong ->
          Misc.fatal_errorf "Wrong type for [Project_closure] when being used \
              as a [constant_defining_value]: %a"
            Flambda_static.Constant_defining_value.print constant_defining_value
    end

let initial_environment_for_recursive_symbols env defn =
  (* First declare an empty version of the symbols *)
  let env =
    List.fold_left (fun env (symbol, _) ->
        E.add_symbol env symbol (T.unresolved (Symbol symbol)))
      env defs
  in
  let rec loop times env =
    if times <= 0 then
      env
    else
      let env =
        List.fold_left (fun env (symbol, constant_defining_value) ->
            let ty =
              constant_defining_value_ty env constant_defining_value
            in
            E.redefine_symbol env symbol ty)
          env defs
      in
      loop (times-1) env
  in
  loop 2 env

let simplify_constant_defining_value
    env r symbol
    (constant_defining_value : Flambda_static.Constant_defining_value.t) =
  let r, constant_defining_value, ty =
    match constant_defining_value with
    (* No simplifications are possible for [Allocated_const] or [Block]. *)
    | Allocated_const const ->
      r, constant_defining_value, type_for_allocated_const const
    | Block (tag, fields) ->
      let fields = List.map
          (function
            | Flambda.Symbol sym -> E.find_symbol_exn env sym
            | Flambda.Const cst -> type_for_const cst)
          fields
      in
      r, constant_defining_value, T.block tag (Array.of_list fields)
    | Set_of_closures set_of_closures ->
      if Variable.Map.cardinal set_of_closures.free_vars <> 0 then begin
        Misc.fatal_errorf "Set of closures bound by [Let_symbol] is not \
                           closed: %a"
          Flambda.Set_of_closures.print set_of_closures
      end;
      let set_of_closures, r, _freshening =
        simplify_set_of_closures env r set_of_closures
      in
      r, ((Set_of_closures set_of_closures) : Flambda_static.Constant_defining_value.t),
        R.inferred_type r
    | Project_closure (set_of_closures_symbol, closure_id) ->
      (* No simplifications are necessary here. *)
      let set_of_closures_type =
        E.find_symbol_exn env set_of_closures_symbol
      in
      let closure_type =
        match T.reify_as_set_of_closures set_of_closures_type with
        | Ok (_, value_set_of_closures) ->
          let closure_id =
            T.freshen_and_check_closure_id value_set_of_closures
              (Closure_id.Set.singleton closure_id)
          in
          T.closure
            (Closure_id.Map.of_set (fun _ -> value_set_of_closures) closure_id)
        | Unresolved sym -> T.unresolved_symbol sym
        | Unknown -> T.unknown Other
        | Wrong ->
          Misc.fatal_errorf "Wrong Flambda type for [Project_closure] \
                             when being used as a [constant_defining_value]: %a"
            Flambda_static.Constant_defining_value.print constant_defining_value
      in
      r, constant_defining_value, closure_type
  in
  let ty = T.augment_with_symbol ty symbol in
  let r = ty in
  r, constant_defining_value, ty

let simplify_static_part env r (static_part : Flambda_static0.Static_part.t) =
  match static_part with
  | Block _ ->

  | Set_of_closures _ ->

  | Project_closure _ ->

  | Boxed_float _ ->

  | Boxed_int32 _ ->

  | Boxed_int64 _ ->

  | Boxed_nativeint _ ->

  | Mutable_float_array _ ->

  | Immutable_float_array _ ->

  | Mutable_string _ ->

  | Immutable_string _ ->


let simplify_static_structure env r str =
  let r, str =
    List.fold_left
      (fun (r, str) (sym, static_part) ->
        let static_part = simplify_static_part env r static_part in
        r, (static_part :: str))
      str
  in
  r, List.rev str

let simplify_define_symbol env r (recursive : Asttypes.rec_flag)
      (defn : Program_body.definition)
      : Program_body.definition * E.t * R.t =
  let env =
    match recursive with
    | Nonrecursive -> env
    | Recursive -> initial_environment_for_recursive_symbols env defn
  in
  let env, r =
    match defn.computation with
    | None -> env, r
    | Some computation ->
      let arity =
        List.map (fun (_var, kind) -> kind) computation.computed_values
      in
      let name = computation.return_cont in
      let return_cont_approx =
        Continuation_approx.create_unknown ~name ~arity
      in
      let expr_env =
        E.add_continuation computation.return_cont return_cont_approx
      in
      let expr, r =
        Simplify_expr.simplify_expr expr_env r computation.expr
      in
      let args_types = R.continuation_args_types r name ~arity in
      assert (List.for_all2 (fun (_var, kind1) ty ->
          let kind2 = T.kind ~importer:(E.importer env) ty in
          Flambda_kind.equal kind1 kind2)
        computation.computed_values args_types);
      let env =
        List.fold_left2 (fun env (var, _kind) ty -> E.add env var ty)
          env
          computation.computed_values args_types
      in
      env, r
  in
  simplify_static_structure env r defn.static_structure

let rec simplify_program_body env r (body : Program_body.t)
      : Program_body.t * R.t =
  match body with
  | Define_symbol (defn, body) ->
    let defn, env, r = simplify_define_symbol env r Nonrecursive defn in
    let body = simplify_program_body env body in
    Define_symbol (defn, body), r
  | Define_symbol_rec (defn, body) ->
    let defn, env, r = simplify_define_symbol env r Recursive defn in
    let body = simplify_program_body env body in
    Define_symbol_rec (defn, body), r
  | Root _ -> body, r


  | Let_rec_symbol (defs, program) ->
    let env = define_let_rec_symbol_type env defs in
    let env, r, defs =
      List.fold_left (fun (env, r, defs) (symbol, def) ->
          let r, def, ty =
            simplify_constant_defining_value env r symbol def
          in
          let ty = T.augment_with_symbol ty symbol in
          let env = E.redefine_symbol env symbol ty in
          (env, r, (symbol, def) :: defs))
        (env, r, []) defs
    in
    let program, r = simplify_program_body env r program in
    Let_rec_symbol (defs, program), r
  | Let_symbol (symbol, constant_defining_value, program) ->
    let r, constant_defining_value, ty =
      simplify_constant_defining_value env r symbol constant_defining_value
    in
    let ty = T.augment_with_symbol ty symbol in
    let env = E.add_symbol env symbol ty in
    let program, r = simplify_program_body env r program in
    Let_symbol (symbol, constant_defining_value, program), r
  | Initialize_symbol (symbol, tag, fields, program) ->
    (* CR mshinwell: Work out how to deal with [Initialize_symbol] so that there
       can be constant initializers amongst inconstant initializing
       expressions -- with the constants filled in early. *)
    let rec simplify_fields env r l =
      match l with
      | [] -> [], [], r
      | (h, cont) :: t ->
        let t', types, r = simplify_fields env r t in
        let cont_type =
          Continuation_approx.create_unknown ~name:cont ~num_params:1
        in
        let env = E.add_continuation env cont cont_type in
        let h', r, uses =
          let descr =
            Format.asprintf "Initialize_symbol %a" Symbol.print symbol
          in
          simplify_toplevel env r h ~continuation:cont ~descr
        in
        let ty =
          Simplify_aux.Continuation_uses.meet_of_args_types
            uses ~num_params:1
        in
        let ty =
          match ty with
          | [ty] -> ty
          | _ -> assert false
        in
        let tys = ty :: tys in
        if t' == t && h' == h
        then l, tys, r
        else (h', cont) :: t', tys, r
    in
    let fields, tys, r = simplify_fields env r fields in
    let ty =
      T.augment_with_symbol (T.block tag (Array.of_list tys)) symbol
    in
    let module Backend = (val (E.backend env) : Backend_intf.S) in
    let env = E.add_symbol env symbol ty in
    let program, r = simplify_program_body env r program in
    (* The [Initialize_symbol] will be turned into an [Effect], if suitable,
       by [Remove_unused_program_constructs]. *)
    Initialize_symbol (symbol, tag, fields, program), r
  | Effect (expr, cont, program) ->
    let expr : Flambda.Expr.t =
      let discard_result_cont = Continuation.create () in
      let result_var = Variable.create "effect_result" in
      let result_ty = Flambda_ty.any_value Must_scan in
      let result_param =
        Flambda.Typed_parameter.create (Parameter.wrap result_var)
          result_ty
      in
      Let_cont {
        body = expr;
        handlers = Nonrecursive {
          name = discard_result_cont;
          handler = {
            params = [result_param];
            stub = false;
            is_exn_handler = false;
            handler = Apply_cont (cont, None, []);
          };
        };
      }
    in
    let cont_ty =
      Continuation_approx.create_unknown ~name:cont ~num_params:0
    in
    let env = E.add_continuation env cont cont_ty in
    let expr, r, uses =
      let descr =
        Format.asprintf "Effect (return continuation %a)"
          Continuation.print cont
      in
      simplify_toplevel env r expr ~continuation:cont ~descr
    in
    begin match
      Simplify_aux.Continuation_uses.meet_of_args_types
        uses ~num_params:0
    with
    | [] -> ()
    | _ -> assert false
    end;
    let program, r = simplify_program_body env r program in
    Effect (expr, cont, program), r
  | End root -> End root, r

let simplify_program env r ~backend (program : Program.t) =
  let predef_exn_symbols = Backend.all_predefined_exception_symbols () in
  let symbols = Symbol.Set.union program.imported_symbols predef_exn_symbols in
  let env, r =
    Symbol.Set.fold (fun symbol (env, r) ->
        let env, ty =
          match E.find_symbol_exn env symbol with
          | exception Not_found ->
            let ty = T.symbol_loaded_lazily (Flambda_kind.value ()) symbol in
            E.add_symbol env symbol ty, ty
          | ty -> env, ty
        in
        env, ty)
      (env, r)
  in
  let program_body, r = simplify_program_body env r program.program_body in
  let program = { program with program_body; } in
  program, r
