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

let simplify_static_part env r (static_part : Flambda_static0.Static_part.t)
      : _ or_wrong =
  let importer = E.importer env in
  let simplify_float_fields mut fields =
    let or_unknown field =
      match mut with
      | Immutable -> Some field
      | Mutable -> None
    in
    let done_something, fields_rev =
      List.fold_left
        (fun (done_something, fields_rev) (field : _ Static_part.or_variable) ->
          match field with
          | Const f -> done_something, ((field, or_unknown f) :: fields_rev)
          | Var var ->
            begin match T.prove_naked_float ~importer ty with
            | None -> done_something, ((field, None) :: fields_rev)
            | Some f -> true, ((Const f, or_unknown f) :: fields_rev)
            end)
        (false, [])
        fields
    in
    let static_part_fields, fields = List.split (List.rev fields_rev) in
    done_something, static_part_fields, fields
  in
  match static_part with
  | Block (tag, mut, fields) ->
    let or_unknown scanning ty =
      match mut with
      | Immutable -> ty
      | Mutable -> T.any_value scanning Other
    in
    let fields_and_types =
      List.map (fun (field : Flambda_static0.Field_of_kind_value.t) ->
          match field with
          | Symbol sym ->
            let ty = E.find_symbol env sym in
            field, or_unknown Can_scan ty
          | Tagged_immediate imm ->
            field, or_unknown Can_scan (T.this_tagged_immediate imm)
          | Dynamically_computed var ->
            let ty = E.find env var in
            begin match T.symbol ty with
            | Some sym -> Symbol sym, or_unknown Can_scan ty
            | None ->
              match T.prove_tagged_immediate ~importer ty with
              | Some imm ->
                Tagged_immediate imm,
                  or_unknown Can_scan (T.this_tagged_immediate imm)
              | None -> field, or_unknown Must_scan ty
            end)
        fields
    in
    let fields, field_types = List.split fields_and_types in
    assert (match mut with
      | Immutable -> ()
      | Mutable ->
        List.for_all (fun ty -> not (T.known ~importer:(E.importer env) ty))
          field_types);
    let ty = T.block tag field_types in
    Ok (Block (tag, fields), ty)
  | Set_of_closures set ->
    let r = R.create () in
    let set, ty, _r = Simplify_named.simplify_set_of_closures env r set in
    Ok (Set_of_closures set, ty)
  | Project_closure (sym, closure_id) ->
    let ty = E.find_symbol env sym in
    begin match T.prove_set_of_closures ~importer ty with
    | Ok set -> Ok (static_part, T.Set_of_closures.to_type ty)
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
    let done_something, initial_value, fields =
      simplify_float_fields Mutable fields
    in
    let ty = T.float_array fields in
    if not done_something then Ok (static_part, ty)
    else Ok (Mutable_float_array { initial_value; }, ty)
  | Immutable_float_array fields ->
    let done_something, initial_value, fields =
      simplify_float_fields Immutable fields
    in
    let ty = T.float_array fields in
    if not done_something then Ok (static_part, ty)
    else Ok (Immutable_float_array { initial_value; }, ty)
  | Mutable_string { initial_value = Var var; } ->
    let ty = E.find env var in
    begin match T.prove_string ~importer ty with
    | Ok s ->
      let ty = T.mutable_string ~size:(String.length s) in
      Ok (Mutable_string { initial_value = Const s; }, ty)
    | Unknown -> Ok (static_part, T.any_value Must_scan Other)
    | Wrong -> Wrong
    end
  | Immutable_string (Var var) ->
    let ty = E.find env var in
    begin match T.prove_string ~importer ty with
    | Ok s -> Ok (Immutable_string (Const s), T.this_immutable_string s)
    (* CR mshinwell: Should the types be able to represent "immutable string
       of unknown length"? *)
    | Unknown -> Ok (static_part, T.any_value Must_scan Other)
    | Wrong -> Wrong
    end

let simplify_static_structure initial_env (recursive : Flambda.recursive) str =
  let unreachable, env, str =
    List.fold_left
      (fun ((now_unreachable, env, str) as acc) (sym, static_part) ->
        if now_unreachable then
          acc
        else
          match simplify_static_part initial_env static_part with
          | Ok (static_part, ty) ->
            let env =
              match recursive with
              | Nonrecursive -> E.add_symbol env symbol ty
              | Recursive -> E.redefine_symbol env symbol ty
            in
            false, env, (static_part :: str)
          | Wrong ->
            true, env, str)
      (false, initial_env, r, [])
      str
  in
  unreachable, env, List.rev str

let initial_environment_for_recursive_symbols env defn =
  let env =
    List.fold_left (fun env (symbol, _static_part) ->
        E.add_symbol env symbol (T.unresolved_symbol symbol))
      env defn
  in
  let _unreachable, env, str = simplify_static_structure env defn in
  env

let simplify_define_symbol env (recursive : Flambda.recursive)
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
    simplify_static_structure env recursive defn.static_structure
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
