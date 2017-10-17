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

(* CR mshinwell: check specialisation behaviour is preserved *)

let unrecursify_function ~closure_id
    ~(function_decl : Flambda.Function_declaration.t) =
  let loop_continuation = Continuation.create () in
  let did_something = ref false in
  let handler =
    Flambda.Expr.Mappers.Toplevel_only.map_expr (fun expr ->
        match expr with
        | Apply {
            kind = Function;
            continuation;
            args;
            call_kind = Direct {
              closure_id = call_closure_id;
              _;
            };
          }
          when Continuation.equal continuation function_decl.continuation_param
            (* CR mshinwell for pchambart: I'm not sure this next line is
               correct now.  It may not be the same function any more... *)
            && Closure_id.equal call_closure_id closure_id ->
          did_something := true;
          Apply_cont (loop_continuation, None, args)
        | Let _ | Let_mutable _ | Let_cont _ | Apply_cont _ | Switch _
        | Apply _ | Invalid _ -> expr)
      function_decl.body
  in
  if not !did_something then None
  else
    let new_params = Flambda.Typed_parameter.List.rename function_decl.params in
    let body : Flambda.Expr.t =
      Let_cont
        { handlers =
            Recursive (
              Continuation.Map.of_list [
                loop_continuation,
                  { Flambda.Continuation_handler.
                    params = function_decl.params;
                    stub = false;
                    is_exn_handler = false;
                    handler;
                  };
              ]);
          body = Apply_cont (loop_continuation, None,
            Flambda.Typed_parameter.List.vars new_params);
        }
    in
    let function_decl =
      Flambda.Function_declaration.update_params_and_body function_decl
        ~params:new_params ~body
    in
    Some function_decl
