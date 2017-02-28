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

module R = Inline_and_simplify_aux.Result

let for_toplevel_expression expr r =
  let used_linearly =
    R.non_recursive_continuations_used_linearly_in_inlinable_position r
  in
  let r = ref r in
  let expr =
    Flambda_iterators.map_toplevel_expr (fun (expr : Flambda.t) ->
        match expr with
        | Let_cont { body; handlers = Nonrecursive { name; _ }; } ->
          if Continuation.Map.mem name used_linearly then body
          else expr
        | Apply_cont (cont, trap_action, args) ->
          begin match Continuation.Map.find cont used_linearly with
          | exception Not_found -> expr
          | handler ->
            begin match trap_action with
            | None -> ()
            | Some _ ->
              Misc.fatal_errorf "Continuation %a should not have been deemed \
                  as used ``linearly in inlinable position'' when it occurs \
                  in an [Apply_cont] expression with a trap handler action"
                Continuation.print cont
            end;
            r := R.forget_continuation_uses !r cont;
            List.fold_left2 (fun expr param arg ->
                Flambda.create_let param (Var arg) expr)
              handler.handler
              handler.params args
          end
        | Apply _ | Let _ | Let_cont _ | Let_mutable _ | Switch _
        | Proved_unreachable -> expr)
      expr
  in
  expr, !r
