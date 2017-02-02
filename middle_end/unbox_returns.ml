(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2017 OCamlPro SAS                                          *)
(*   Copyright 2017 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module A = Simple_value_approx
module R = Inline_and_simplify_aux.Result
module U = R.Continuation_uses

let wrapper_returning_boxed_result ~params ~new_fun_var ... =
  let stub_return_cont = Continuation.create () in
  let stub_params = List.map (fun param -> Variable.rename param) params in
  let new_closure_id = ... in
  let return_cont = Continuation.create () in
  let unboxed_results =
    Array.to_list (Array.init size (fun index ->
      Variable.create (Printf.sprintf "unboxed_result%d" index)))
  in
  let dbg = Debuginfo.none in
  let box_results =
    let boxed_result = Variable.create "boxed_result" in
    Flambda.create_let boxed_result
      (Prim (Pmakeblock (tag, Immutable, None), unboxed_results,
        Debuginfo.none))
      (Apply {
        kind = Function;
        func = new_fun_var;
        continuation = stub_return_cont;
        args = [boxed_result];
        call_kind = Direct { closure_id = ...; return_arity = Singleton; };
        dbg;
        inline = Lambda.Default_inline;
        specialise = Lambda.Default_specialise;
      })
  in
  let body : Flambda.expr =
    Let_cont {
      body = Apply {
        kind = Function;
        func = ...;
        continuation = return_cont;
        args = stub_params;
        call_kind = Direct { closure_id = new_closure_id; return_arity; };
        dbg;
        inline = Lambda.Default_inline;
        specialise = Lambda.Default_specialise;
      };
      handler = Nonrecursive {
        name = return_cont;
        handler = {
          params = unboxed_results;
          stub = false;
          is_exn_handler = false;
          handler = box_results;
          specialised_args = Variable.Map.empty;
        };
      }
    }
  in
  let function_decl =
    Flambda.create_function_declaration ~params:stub_params
      ~continuation_param:stub_return_cont
      ~return_arity:Singleton
      ~body
      ~stub:true
      ~dbg
      ~inline:Lambda.Default_inline
      ~specialise:Lambda.Default_specialise
      ~is_a_functor:false
  in
  Some function_decl


let unbox_function_decl ~fun_var ~(function_decl : Flambda.function_declaration)
      ~how_to_unbox ~return_cont_param =
  let dbg = Debuginfo.none in
  let new_fun_var = Variable.rename fun_var in
  (* There are two steps:
     1. Build a stub continuation that is called by the function instead of
        its existing return continuation.  This stub breaks apart the boxed
        value and then calls the (renamed) return continuation (which is now
        deemed to accept multiple arguments).
     2. Build a stub function that calls the original function, receives the
        unboxed result, and then boxes it.  (When this stub is inlined at a
        direct call site of the original function, the boxing should normally
        be eliminated.) *)
  let _cont_wrapper_params_map, cont_wrapper_params,
      cont_wrapper_specialised_args =
    Flambda_utils.create_wrapper_params ~params:[return_cont_param]
      ~specialised_args:Variable.Map.empty
      ~freshening_already_assigned:(how_to_unbox.
        being_unboxed_to_wrapper_params_being_unboxed)
  in
  let new_return_cont = Continuation.create () in
  let wrapper_body =
    let initial_body : Flambda.t =
      Apply_cont (new_return_cont, None,
        cont_wrapper_params
          @ how_to_unbox.new_arguments_for_call_in_wrapper)
    in
    how_to_unbox.add_bindings_in_wrapper initial_body
  in
  let new_function_body : Flambda.expr =
    Let_cont {
      body = function_decl.body;
      handler = Nonrecursive {
        name = function_decl.continuation_param;
        handler = {
          params = cont_wrapper_params;
          stub = true;
          is_exn_handler = false;
          handler = wrapper_body;
          specialised_args = cont_wrapper_specialised_args;
        };
      };
    }
  in
  let function_decl =
    Flambda.create_function_declaration ~continuation_param:new_return_cont
      ~params:function_decl.params
      ~body:new_function_body
      ~stub:function_decl.stub
      ~dbg:function_decl.dbg
      ~inline:function_decl.inline
      ~specialise:function_decl.specialise
      ~is_a_functor:function_decl.is_a_functor
  in
  let new_fun_var = Variable.rename fun_var in
  let wrapper_return_cont = Continuation.create () in
  let _fun_wrapper_params_map, fun_wrapper_params,
      fun_wrapper_specialised_args =
    Flambda_utils.create_wrapper_params ~params:function_decl.params
      ~specialised_args:function_decl.specialised_args
      ~freshening_already_assigned:Variable.Map.empty
  in
  let function_stub_body : Flambda.expr =
    let receive_results = Continuation.create () in
    let results =
      Array.to_list (Array.create (List.length how_to_unbox.params)
        (fun index ->
          let name = Printf.sprintf "result%d" index in
          Variable.create name))
    in
    let box_results_and_call_return_cont : Flambda.expr =

    in
    Let_cont {
      body = Apply {
        kind = Function;
        func = new_fun_var;
        continuation = receive_results;
        args = fun_wrapper_params;
        call_kind = Direct (Closure_id.wrap new_fun_var);
        dbg;
        inline = Lambda.Default_inline;
        specialise = Lambda.Default_specialise;
      };
      handler = Nonrecursive {
        name = receive_results;
        handler = {
          params = results;
          handler = box_results_and_call_return_cont;
          stub = false;
          is_exn_handler = false;
          specialised_args = Variable.Map.empty;
        };
      };
    };
  in
  let function_stub_decl =
    Flambda.create_function_declaration ~continuation_param:wrapper_return_cont
      ~params:fun_wrapper_params
      ~body:function_stub_body
      ~stub:true
      ~dbg:function_decl.dbg
      ~inline:function_decl.inline
      ~specialise:function_decl.specialise
      ~is_a_functor:function_decl.is_a_functor
  in
  Variable.Map.add new_fun_var function_decl
    (Variable.Map.add fun_var function_stub_decl
      Variable.Map.empty),
    fun_wrapper_specialised_args

let for_function_decl r ~backend:_ ~fun_var
        ~(function_decl : Flambda.function_declaration) =
  let definitions_with_uses = R.continuation_definitions_with_uses r in
  let return_cont = function_decl.continuation_param in
  match Continuation.Map.find return_cont definitions_with_uses with
  | exception Not_found -> None
  | (uses, approx, env, recursive) ->
    match U.meet_of_args_approxs_opt uses with
    | None -> None
    | Some args_approxs ->
      match args_approxs with
      | _::_::_ ->
        (* For the moment, don't apply this transformation more than once
           to any given function. *)
        None
      | [arg_approx] ->
        let return_cont_param = Variable.create "return_cont_param" in
        let how_to_unbox =
          Unbox_one_variable.how_to_unbox ~being_unboxed:return_cont_param
            ~being_unboxed_approx:arg_approx
        in
        match how_to_unbox with
        | None -> None
        | Some how_to_unbox ->
          let function_decls, new_specialised_args =
            unbox_function_decl ~fun_var ~function_decl ~how_to_unbox
              ~return_cont_param
          in
          Some (function_decls, new_specialised_args)

let run r ... =

      let function_decls =
        Flambda.update_function_declarations set_of_closures.function_decls
          ~funs
      in
