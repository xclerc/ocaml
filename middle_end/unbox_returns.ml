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

module U = Inline_and_simplify_aux.Continuation_uses

(* CR mshinwell: Fix [Unbox_one_variable] so that when we don't need the
   discriminant, etc, then they aren't generated.  These are simplified
   away automatically for [Unbox_continuation_params] but cannot be for
   this one. *)

let unbox_function_decl ~fun_var ~(function_decl : Flambda.function_declaration)
      ~(how_to_unbox : Unbox_one_variable.How_to_unbox.t) ~return_cont_param
      ~specialised_args =
  let dbg = Debuginfo.none in
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
        how_to_unbox.new_arguments_for_call_in_wrapper)
    in
    how_to_unbox.add_bindings_in_wrapper initial_body
  in
  let new_function_body : Flambda.expr =
    Let_cont {
      body = function_decl.body;
      handlers = Nonrecursive {
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
  let return_arity =
    function_decl.return_arity - 1 + List.length how_to_unbox.new_params
  in
  let function_decl =
    Flambda.create_function_declaration ~continuation_param:new_return_cont
      ~return_arity
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
      ~specialised_args
      ~freshening_already_assigned:Variable.Map.empty
  in
  let function_stub_body : Flambda.expr =
    let receive_results = Continuation.create () in
    let results = List.map (fun (var, _proj) -> var) how_to_unbox.new_params in
    let box_results_and_call_return_cont : Flambda.expr =
      let args_to_return_cont =
        List.map (fun (var, _) -> var)
          how_to_unbox.build_boxed_value_from_new_params
      in
      List.fold_right (fun (_var, add_binding) expr -> add_binding expr)
        how_to_unbox.build_boxed_value_from_new_params
        (Flambda.Apply_cont (wrapper_return_cont, None, args_to_return_cont))
    in
    Let_cont {
      body = Apply {
        kind = Function;
        func = new_fun_var;
        continuation = receive_results;
        args = fun_wrapper_params;
        call_kind = Direct {
          closure_id = Closure_id.wrap new_fun_var;
          return_arity = function_decl.return_arity;
        };
        dbg;
        inline = Lambda.Default_inline;
        specialise = Lambda.Default_specialise;
      };
      handlers = Nonrecursive {
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
      ~return_arity:1
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

let for_function_decl ~continuation_uses ~fun_var
        ~(function_decl : Flambda.function_declaration)
        ~specialised_args ~recursively_used =
  let return_cont = function_decl.continuation_param in
  if function_decl.stub || Variable.Set.mem fun_var recursively_used then
    None
  else
    match Continuation.Map.find return_cont continuation_uses with
    | exception Not_found -> None
    | uses ->
      match U.meet_of_args_approxs_opt uses with
      | None -> None
      | Some args_approxs ->
        match args_approxs with
        | _::_::_ ->
          (* For the moment, don't apply this transformation more than once
             to any given function. *)
          None
        | [] ->
          Misc.fatal_errorf "Function %a has zero return arity"
            Variable.print fun_var
        | [arg_approx] ->
          assert (function_decl.return_arity = 1);
          let return_cont_param = Variable.create "return_cont_param" in
          let how_to_unbox =
            Unbox_one_variable.how_to_unbox ~being_unboxed:return_cont_param
              ~being_unboxed_approx:arg_approx
          in
          match how_to_unbox with
          | None -> None
          | Some how_to_unbox ->
            (* For the moment, don't go too overboard... *)
            if List.length how_to_unbox.new_params > 4 then begin
              None
            end else begin
    Format.eprintf "Unbox_returns on:\n@ %a\n%!"
      Flambda.print_function_declaration (fun_var, function_decl);
              let function_decls, new_specialised_args =
                unbox_function_decl ~fun_var ~function_decl ~how_to_unbox
                  ~return_cont_param ~specialised_args
              in
    Format.eprintf "Unbox_returns returns:\n@ %a\n%!"
      Flambda.print_function_declarations
        (Flambda.create_function_declarations ~funs:function_decls);
              Some (function_decls, new_specialised_args)
            end

let run ~continuation_uses ~(function_decls : Flambda.function_declarations)
      ~specialised_args ~backend =
  let recursively_used =
    Find_recursive_functions.in_function_declarations function_decls ~backend
  in
  let funs, new_specialised_args =
    Variable.Map.fold (fun fun_var function_decl (funs, new_specialised_args) ->
        match
          for_function_decl ~continuation_uses ~fun_var ~function_decl
            ~specialised_args ~recursively_used
        with
        | None ->
          let funs = Variable.Map.add fun_var function_decl funs in
          funs, new_specialised_args
        | Some (function_decls, new_specialised_args') ->
          let funs = Variable.Map.disjoint_union funs function_decls in
          let new_specialised_args =
            Variable.Map.disjoint_union new_specialised_args
              new_specialised_args'
          in
          funs, new_specialised_args)
      function_decls.funs
      (Variable.Map.empty, specialised_args)
  in
  Flambda.create_function_declarations ~funs, new_specialised_args
