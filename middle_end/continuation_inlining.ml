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
  if Continuation.Set.is_empty used_linearly then begin
    expr, r
  end else begin
    Format.eprintf "Continuations used linearly: %a\nTerm:@ \n%a%!"
      Continuation.Set.print used_linearly Flambda.print expr;
    let r = ref r in
    (* CR mshinwell: Consider adding phys-equal checks and use of the tail
      recursive [Let] mapper. *)
    let rec substitute env (expr : Flambda.expr) : Flambda.expr =
      match expr with
      | Let ({ var; body; _ } as let_expr) ->
        let module W = Flambda.With_free_variables in
        let defining_expr = W.of_defining_expr_of_let let_expr in
        let body = substitute env body in
        W.create_let_reusing_defining_expr var defining_expr body
      | Let_mutable ({ body; _ } as let_mutable) ->
        let body = substitute env body in
        Let_mutable { let_mutable with body; }
      | Let_cont { body; handlers = Nonrecursive { name; handler; }; } ->
        let handler =
          { handler with
            handler = substitute env handler.handler;
          }
        in
        let used_linearly = Continuation.Set.mem name used_linearly in
        let body_env =
          if used_linearly then Continuation.Map.add name handler env
          else env
        in
        let body = substitute body_env body in
        if used_linearly then body
        else Let_cont { body; handlers = Nonrecursive { name; handler; }; }
      | Let_cont { body; handlers = Recursive handlers; } ->
        let body = substitute env body in
        let handlers =
          Continuation.Map.map (fun (handler : Flambda.continuation_handler) ->
              { handler with
                handler = substitute env handler.handler;
              })
            handlers
        in
        Let_cont { body; handlers = Recursive handlers; }
      | Apply_cont (cont, trap_action, args) ->
        begin match Continuation.Map.find cont env with
        | exception Not_found -> expr
        | (handler : Flambda.continuation_handler) ->
          begin match trap_action with
          | None -> ()
          | Some _ ->
            Misc.fatal_errorf "Continuation %a should not have been deemed \
                as used ``linearly in inlinable position'' when it occurs \
                in an [Apply_cont] expression with a trap handler action"
              Continuation.print cont
          end;
          r := R.forget_continuation_definition !r cont;
          List.fold_left2 (fun expr param arg ->
              Flambda.create_let param (Var arg) expr)
            handler.handler
            handler.params args
        end
      | Let_cont { body; handlers = (Alias _) as handlers; } ->
        let body = substitute env body in
        Let_cont { body; handlers; }
      | Apply _ | Switch _ | Proved_unreachable -> expr
    in
    let expr = substitute Continuation.Map.empty expr in
    Format.eprintf "After continuation inlining:@ \n%a" Flambda.print expr;
    expr, !r
  end
