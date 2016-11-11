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

let params_do_not_overlap_free_variables ~params ~handler =
  let params = Variable.Set.of_list params in
  let handler_fvs = Flambda.free_variables handler in
  Variable.Set.is_empty (Variable.Set.inter params handler_fvs)

let params_do_not_overlap_free_variables_let ~params
      ~(let_expr : Flambda.let_expr) =
  let params = Variable.Set.of_list params in
  let defining_expr_fvs = let_expr.free_vars_of_defining_expr in
  Variable.Set.is_empty (Variable.Set.inter params defining_expr_fvs)

type thing_to_lift =
  | Continuation of Continuation.t * Flambda.let_cont_handler
  | Let of Variable.t * Flambda.named

let rec find_things_to_lift (acc : thing_to_lift list) (expr : Flambda.t) =
  match expr with
  | Let_cont { name; body = body1; handler = Handler {
        params; recursive; handler = (Let_cont { name = name'; body = _;
          handler = Handler { handler; _ }; _ }) as let_cont2; }; }
      when params_do_not_overlap_free_variables ~params ~handler ->
Format.eprintf "lifting continuation %a nested inside %a\n%!"
  Continuation.print name'
  Continuation.print name;
    (* The continuation [handler] can be lifted.  First we try to lift things
       (recursively) from inside [handler] itself and then (on the way back
       up from that recursion) we add the lifted continuations to [acc]. *)
    let acc, body2 = find_things_to_lift acc let_cont2 in
    let acc =
      (Continuation (name, Handler {
          params; recursive; handler = body2; }))
        :: acc
    in
    acc, lift body1
  | Let_cont { name; body; handler = Handler {
      handler = Let_cont { handler = Alias alias_to; _ }; }; } ->
    (* Continuation aliases nested immediately inside another [Let_cont]'s
       handler can always be lifted. *)
    let acc = (Continuation (name, Alias alias_to)) :: acc in
    acc, lift body
  | Let_cont { name; body; handler = Handler {
        params; handler = Let let_expr; }; }
      when params_do_not_overlap_free_variables_let ~params ~let_expr
        && Effect_analysis.no_effects_named let_expr.defining_expr ->
Format.eprintf "lifting let %a nested inside %a\n%!" Variable.print let_expr.var
  Continuation.print name;
    (* The let-bound expression [let_expr] can be lifted.  Since there cannot
       be any nested [Let] or [Let_cont] in the defining expression of the
       [Let], we don't need to recurse into that expression.
       Lifting let-bound expressions in this manner allows us to lift more
       continuations (that may depend on such lets). *)
    let acc, body2 = find_things_to_lift acc (Flambda.Let let_expr) in
    let acc =
      (Continuation (name, Handler {
          params; recursive = Nonrecursive; handler = body2; }))
        :: acc
    in
    acc, lift body
  | Let_cont { name; body; handler = Handler {
      params; recursive; handler; }; } ->
Format.eprintf "not lifting continuation %a\n%!" Continuation.print name;
    (* The continuation [handler] cannot be lifted---but there might be
       sequences of [Let_cont]s or [Let]s inside [handler] that can be lifted
       (without bringing them out of [handler]).  First we deal with those.
       At that point, observe that there cannot be any non-lifted [Let_cont]s
       (or [Let]s) between this [Let_cont] and the (outer) [Let] or [Let_cont]
       where we started lifting.  By virtue of this property we can just add
       the [Let_cont] to [acc] without breaking any scoping rules. *)
    let handler = lift handler in
    let acc =
      (Continuation (name, Handler { params; recursive; handler; })) :: acc
    in
    acc, lift body
  | Let_cont { name; body; handler = Alias alias_to; } ->
    (* Similar to the previous case, but there's no handler. *)
    let acc = (Continuation (name, Alias alias_to)) :: acc in
    acc, lift body
  | Let { var; defining_expr; body; _ } ->
    (* Same as the previous case. *)
    let acc = (Let (var, defining_expr)) :: acc in
    acc, lift body
    (* Same as the previous case. *)
  | Apply _ | Apply_cont _ | Switch _ ->
    (* These things have no subexpressions, so we're done. *)
    acc, expr
  | Let_mutable _ ->
    (* CR mshinwell: Think about this case *)
    acc, expr

and lift (expr : Flambda.t) : Flambda.t =
Format.eprintf "lift starting\n%!";
  let defs, body = find_things_to_lift [] expr in
let res =
  List.fold_left (fun body (def : thing_to_lift) ->
      match def with
      | Continuation (name, handler) ->
        Flambda.Let_cont { name; body; handler; }
      | Let (var, Set_of_closures set) ->
        let set = Flambda_iterators.map_function_bodies set ~f:lift in
        Flambda.create_let var (Set_of_closures set) body
      | Let (var, defining_expr) ->
        Flambda.create_let var defining_expr body)
    body
    defs
in
Format.eprintf "lift starting\n%!";
res

let run program =
  Flambda_iterators.map_exprs_at_toplevel_of_program program ~f:lift
