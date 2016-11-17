(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2016 OCamlPro SAS                                          *)
(*   Copyright 2016 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module W = Flambda.With_free_variables

module State = struct
  type t = {
    to_sink : (Variable.t * Flambda.named W.t) Continuation.Map.t;
    
  }
end

let rec sink_expr (expr : Flambda.expr) ~state =
  match expr with
  | Let ({ var; defining_expr; body; } as let_expr) ->
    let body, state = sink_expr body ~state in
    let fvs =
      Variable.Set.union (Flambda.free_variables_named defining_expr)
        (Variable.Set.remove var (Flambda.free_variables body))
    in

  | Let_mutable { var; initial_value; contents_kind; body; } ->

  | Let_cont { name; body; handler = (Alias alias_of) as handler; } ->

  | Let_cont { name; body; handler =
      Handler { params; recursive; handler; } } ->
    let body, state = sink_expr body ~state in
    let handler, handler_state = sink_expr handler ~state:(State.create ()) in
    let fvs_handler =
      Variable.Set.diff (Flambda.free_variables handler)
        (Variable.Set.of_list params)
    in
    let candidates_to_be_sunk =
      Variable.Set.diff fvs_handler (Flambda.free_variables body)
    in


  | Apply _ | Apply_cont _ | Switch _ ->

and sink (expr : Flambda.t) =

let run program =
  Flambda_iterators.map_exprs_at_toplevel_of_program program ~f:sink
