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

module E = Simplify_env
module R = Simplify_result
module T = Flambda_type

module Program = Flambda_static.Program
module Program_body = Flambda_static.Program_body
module Static_part = Flambda_static.Static_part

type 'a or_wrong =
  | Ok of 'a
  | Wrong

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
    let set, _r = Simplify_named.simplify_set_of_closures env r set in
    let set' =
      (* this should be like normal simplification for this -- share? *)
      T.create_set_of_closures ~set_of_closures_id:...
        ~set_of_closures_origin:...
        ~function_decls:...
        ~closure_elements:...
    in
    let ty = T.set_of_closures set' in
    Ok (Set_of_closures set, ty)
  | Project_closure (sym, closure_id) ->
    let ty = E.find_symbol env sym in
    begin match T.prove_set_of_closures ~importer ty with
    (* XXX the set of closures types don't match on the next line *)
    | Ok set -> Ok (Project_closure (sym, closure_id), set)
    | Unknown -> Ok (static_part, T.any_value Must_scan Other)
    | Wrong -> Wrong
    end
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
  let computation, static_structure =
    (* CR-someday mshinwell: We could imagine propagating an "unreachable"
       (if that's what [invalid ()] turns into, rather than a trap) back to
       previous [Define_symbol]s. *)
    if not unreachable then
      computation, static_structure
    else
      match computation with
      | None -> Flambda.Expr.invalid (), []
      | Some computation ->
        let params =
          List.map (fun (var, kind) ->
              let ty = Flambda_type.unknown kind Other in
              let param = Parameter.wrap var in
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
        let computation =
          { expr;
            return_cont = new_return_cont;
            computed_values = [];
          }
        in
        computation, []
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
