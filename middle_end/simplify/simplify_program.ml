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

type 'a or_wrong =
  | Ok of 'a
  | Wrong

let simplify_static_part env r (static_part : Flambda_static0.Static_part.t)
      : _ or_wrong =
  let importer = E.importer env in
  let simplify_float_fields fields =
    List.fold_left
      (fun (done_something, fields_rev) (field : _ Static_part.or_variable) ->
        match field with
        | Const _ -> done_something, (field :: fields_rev)
        | Var var ->
          begin match T.prove_naked_float ~importer ty with
          | None -> done_something, (field :: fields_rev)
          | Some f -> true, ((Const f) :: fields_rev)
          end)
      (false, [])
      fields
  in
  match static_part with
  | Block (tag, fields) ->
    let fields =
      List.map (fun (field : Flambda_static0.Field_of_kind_value.t) ->
          match field with
          | Symbol sym ->
            E.check_symbol_bound env sym;
            field
          | Tagged_immediate _ -> field
          | Dynamically_computed var ->
            let ty = E.find env var in
            begin match T.symbol ty with
            | Some sym -> Symbol sym
            | None ->
              match T.prove_tagged_immediate ~importer ty with
              | Some imm -> Tagged_immediate imm
              | None -> field
            end)
        fields
    in
    Ok (Block (tag, fields), ...)
  | Set_of_closures set ->
    let r = R.create () in
    let set = Simplify_named.simplify_set_of_closures env r set in
    Ok (Set_of_closures set, ...)
  | Project_closure (sym, _closure_id) ->
    E.check_symbol_bound env sym;
    Ok (static_part, ...)
  | Boxed_float (Const f) -> Ok (static_part, T.this_boxed_float f)
  | Mutable_string { initial_value = Const s; } ->
    Ok (static_part, T.this_mutable_string ~initial_value:s)
  | Immutable_string (Const s) ->
    Ok (static_part, T.this_immutable_string s)
  | Boxed_float (Var var) ->
    let ty = E.find env var in
    begin match T.prove_boxed_float ~importer ty with
    | Ok f -> Ok (Boxed_float (Const f), T.this_boxed_float f)
    | Unknown -> Ok (static_part, T.any_boxed_float ())
    | Wrong -> Wrong
    end
  | Boxed_int32 (Const n) -> Ok (static_part, T.this_boxed_int32 n)
  | Boxed_int32 (Var var) ->
    let ty = E.find env var in
    begin match T.prove_boxed_int32 ~importer ty with
    | Ok n -> Ok (Boxed_int32 (Const n), T.this_boxed_int32 n)
    | Unknown -> Ok (static_part, T.any_boxed_int32 ())
    | Wrong -> Wrong
    end
  | Boxed_int64 (Const n) -> Ok (static_part, T.this_boxed_int64 n)
  | Boxed_int64 (Var var) ->
    let ty = E.find env var in
    begin match T.prove_boxed_int64 ~importer ty with
    | Ok n -> Ok (Boxed_int64 (Const n), T.this_boxed_int64 n)
    | Unknown -> Ok (static_part, T.any_boxed_int64 ())
    | Wrong -> Wrong
    end
  | Boxed_nativeint (Const n) -> Ok (static_part, T.this_boxed_nativeint n)
  | Boxed_nativeint (Var var) ->
    let ty = E.find env var in
    begin match T.prove_boxed_nativeint ~importer ty with
    | Ok n -> Ok (Boxed_nativeint (Const n), T.this_boxed_nativeint n)
    | Unknown -> Ok (static_part, T.any_boxed_nativeint ())
    | Wrong -> Wrong
    end
  | Mutable_float_array { initial_value = fields; } ->
    let done_something, fields = simplify_float_fields fields in
    let ty = T.mutable_float_array ~size:(List.length fields) in
    if not done_something then Ok (static_part, ty)
    else Ok (Mutable_float_array { initial_value = List.rev fields; }, ty)
  | Immutable_float_array fields ->
    let done_something, fields = simplify_float_fields fields in
    if not done_something then Ok (static_part, ...)
    else Ok (Immutable_float_array (List.rev fields), ...)
  | Mutable_string { initial_value = Var var; } ->
    let ty = E.find env var in
    begin match T.prove_string ~importer ty with
    | Ok s ->
      let ty = T.mutable_string ~size:(String.length s) in
      Ok (Mutable_string { initial_value = Const s; }, ty)
    | Unknown -> Ok (static_part, ...)
    | Wrong -> Wrong
    end
  | Immutable_string (Var var) ->
    let ty = E.find env var in
    begin match T.prove_string ~importer ty with
    | Ok s -> Ok (Immutable_string (Const s), T.this_immutable_string s)
    | Unknown -> Ok (static_part, ...)
    | Wrong -> Wrong
    end

let simplify_static_structure initial_env str =
  let unreachable, env, str =
    List.fold_left
      (fun ((now_unreachable, env, str) as acc) (sym, static_part) ->
        if now_unreachable then
          acc
        else
          match simplify_static_part initial_env static_part with
          | Ok (static_part, ty) ->
            let env = E.add_symbol env symbol ty in
            false, env, (static_part :: str)
          | Wrong ->
            true, env, str)
      (false, initial_env, r, [])
      str
  in
  unreachable, env, List.rev str

let simplify_define_symbol env (recursive : Asttypes.rec_flag)
      (defn : Program_body.definition)
      : Program_body.definition * E.t =
  let env, computation =
    match defn.computation with
    | None -> env, defn.computation
    | Some computation ->
      let arity =
        List.map (fun (_var, kind) -> kind) computation.computed_values
      in
      let name = computation.return_cont in
      let return_cont_approx =
        Continuation_approx.create_unknown ~name ~arity
      in
      let expr, r =
        let env = E.add_continuation name return_cont_approx in
        let r = R.create () in
        let descr =
          let symbol_names =
            List.map (fun (sym, _) -> Symbol.to_string sym) defn.static_part
          in
          Printf.sprintf "Toplevel binding(s) of: %s"
            (String.concat "+" symbol_names)
        in
        Simplify.simplify_toplevel env r computation.expr ~continuation:name
          descr
      in
      (* CR mshinwell: Add unboxing of the continuation here.  This will look
         like half of Unbox_returns (same analysis and the same thing to
         happen to [expr]; but instead of generating a function wrapper, we
         need to do something else here).  Note that the linearity check
         for Unbox_returns will enable us to handle mutable returned values
         too. *)
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
      let computation =
        match expr with
        | Apply_cont (cont, None, []) ->
          assert (Continuation.equal cont return_cont);
          None
        | _ ->
          Some {
            expr;
            return_cont = computation.return_cont;
            computed_values = computation.computed_values;
          }
      in
      env, computation
  in
  let env =
    match recursive with
    | Nonrecursive -> env
    | Recursive ->
      initial_environment_for_recursive_symbols env defn.static_structure
  in
  let unreachable, static_structure, env =
    simplify_static_structure env defn.static_structure
  in
  let computation =
    match computation with
    | None -> Flambda.Expr.invalid ()
    | Some computation ->
      let params =
        List.map (fun (var, kind) ->
            let ty = Flambda_type.unknown kind Other in
            let param = Parameter.wrap (Variable.rename var) in
            Flambda.Typed_parameter.create param ty)
          computation.computed_values
      in
      let expr : Flambda.Expr.t =
        Let_cont {
          body = computation.expr;
          handlers = Nonrecursive {
            name = computation.return_cont;
            handler = {
              params;
              stub = false;
              is_exn_handler = false;
              handler = Flambda.Expr.invalid ();
            };
          };
        }
      in
      let new_return_cont =
        (* This continuation will never be called. *)
        Continuation.create ()
      in
      { expr;
        return_cont = new_return_cont;
        computed_values = computation.computed_values;
      }
  in
  let definition =
    { static_structure;
      computation;
    }
  in
  definition, env

let rec simplify_program_body env (body : Program_body.t) : Program_body.t =
  match body with
  | Define_symbol (defn, body) ->
    let defn, env = simplify_define_symbol env r Nonrecursive defn in
    let body = simplify_program_body env body in
    Define_symbol (defn, body)
  | Define_symbol_rec (defn, body) ->
    let defn, env, r = simplify_define_symbol env Recursive defn in
    let body = simplify_program_body env body in
    Define_symbol_rec (defn, body)
  | Root _ -> body

let simplify_program env ~backend (program : Program.t) =
  let predef_exn_symbols = Backend.all_predefined_exception_symbols () in
  let env =
    Symbol.Set.fold (fun symbol env -> E.import_symbol env symbol)
      (Symbol.Set.union program.imported_symbols predef_exn_symbols)
      env
  in
  let program_body = simplify_program_body env program.program_body in
  { program with program_body; }
