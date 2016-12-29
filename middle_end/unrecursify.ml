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

let unrecursify_function function_variable
    (function_decl : Flambda.function_declaration)
  : Flambda.function_declaration =
  let closure_id = Closure_id.wrap function_variable in
  let loop_continuation = Continuation.create () in
  let new_params = List.map (fun v -> Variable.rename v) function_decl.params in
  let did_something = ref false in
  let handler =
    Flambda_iterators.map_toplevel_expr
      (function
        | (Let _ | Let_mutable _ | Let_cont _ |
           Apply_cont _ | Switch _) as expr ->
          expr
        | Apply { kind = Function;
                  continuation;
                  args;
                  call_kind = Direct call_closure_id; }
          when Continuation.equal continuation function_decl.continuation_param
            && Closure_id.equal call_closure_id closure_id ->
          did_something := true;
          Apply_cont (loop_continuation, None, args)
        | Apply _ as expr ->
          expr)
      function_decl.body
  in
  if !did_something then
    let body : Flambda.t =
      Let_cont
        { name = loop_continuation;
          handler =
            Handler {
              params = function_decl.params;
              recursive = Recursive;
              handler;
              specialised_args = Variable.Map.empty;
            };
          body = Apply_cont (loop_continuation, None, new_params) }
    in
    Flambda.create_function_declaration
      ~params:new_params
      ~continuation_param:function_decl.continuation_param
      ~body
      ~stub:function_decl.stub
      ~dbg:function_decl.dbg
      ~inline:function_decl.inline
      ~specialise:function_decl.specialise
      ~is_a_functor:function_decl.is_a_functor
  else
    function_decl
