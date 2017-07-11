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

(* CR mshinwell: check specialisation behaviour is preserved *)

let unrecursify_function ~fun_var:function_variable
    ~(function_decl : Flambda.function_declaration) =
  let closure_id = Closure_id.wrap function_variable in
  let loop_continuation = Continuation.create () in
  let did_something = ref false in
  let handler =
    Flambda_iterators.map_toplevel_expr (fun expr ->
        match expr with
        | Apply {
            kind = Function;
            continuation;
            args;
            call_kind = Direct {
              closure_id = call_closure_id;
              return_arity = 1;
            };
          }
          when Continuation.equal continuation function_decl.continuation_param
            && Closure_id.equal call_closure_id closure_id ->
          did_something := true;
          Apply_cont (loop_continuation, None, args)
        | Let _ | Let_mutable _ | Let_cont _ | Apply_cont _ | Switch _
        | Apply _ | Proved_unreachable -> expr)
      function_decl.body
  in
  if not !did_something then None
  else
    let new_params = Parameter.List.rename function_decl.params in
    let body : Flambda.t =
      Let_cont
        { handlers =
            Recursive (
              Continuation.Map.of_list [
                loop_continuation,
                  { Flambda.
                    params = function_decl.params;
                    stub = false;
                    is_exn_handler = false;
                    handler;
                    specialised_args = Variable.Map.empty;
                  };
              ]);
          body = Apply_cont (loop_continuation, None,
            Parameter.List.vars new_params);
        }
    in
    let function_decl =
      Flambda.update_function_decl's_params_and_body function_decl
        ~params:new_params ~body
    in
    Some function_decl
