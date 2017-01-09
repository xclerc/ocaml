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

module A = Simple_value_approx
module B = Inlining_cost.Benefit
module E = Inline_and_simplify_aux.Env
module R = Inline_and_simplify_aux.Result

module Continuation_with_args = struct
  type t = Continuation.t * Variable.t list

  include Identifiable.Make (struct
    type nonrec t = t

    let compare t1 t2 =
      let c = Continuation.compare (fst t1) (fst t2) in
      if c <> 0 then c
      else Variable.compare_lists (snd t1) (snd t2)

    let equal t1 t2 =
      compare t1 t2 = 0

    let hash t =
      Hashtbl.hash (Continuation.hash (fst t),
        List.map Variable.hash (snd t))

    let output _chan _t = Misc.fatal_error "not implemented"
    let print _ppf _t = Misc.fatal_error "not implemented"
  end)
end

type inlining_result =
  | Didn't_inline
  | Inlined of Variable.t list * Flambda.expr

let try_inlining ~cont ~args ~args_approxs ~env
        ~(handler : Flambda.continuation_handler)
      ~inline_unconditionally ~count ~simplify =
  if List.length handler.params <> List.length args then begin
    Misc.fatal_errorf "Continuation %a applied with wrong number of arguments"
      Continuation.print cont
  end;
  assert (List.length args = List.length args_approxs);
  let params, env, expr =
    (* If there are multiple uses of the continuation with the same arguments,
       we will create a new shared continuation (see comment below); the
       parameters of that continuation must be fresh. *)
    if Num_continuation_uses.linear count then
      let params = handler.params in
      let expr =
        List.fold_left2 (fun expr param arg ->
            if not (E.mem env arg) then begin
              Misc.fatal_errorf "When inlining continuation %a, argument %a \
                  was not in scope in the environment: %a"
                Continuation.print cont
                Variable.print arg
                E.print env
            end;
            Flambda.create_let param (Var arg) expr)
          handler.handler
          params args
      in
      params, env, expr
    else
      let freshening =
        List.map (fun param -> param, Variable.rename param) handler.params
      in
      let subst = Variable.Map.of_list freshening in
      let handler =
        Flambda_utils.toplevel_substitution subst handler.handler
      in
      let params = List.map snd freshening in
      let env =
        (* Care: some of the arguments may not be in scope in [env].
           [Inline_and_simplify] will correctly take care of this. *)
        List.fold_left2 (fun env param arg_approx ->
            let param_approx = A.augment_with_variable arg_approx param in
            E.add env param param_approx)
          env
          params args_approxs
      in
      params, env, handler
  in
  let r = R.create () in
  let original : Flambda.t = Apply_cont (cont, None, args) in
(*
Format.eprintf "try_inlining simplification %a (params %a) starts@;%a@;\n%!"
  Continuation.print cont Variable.print_list params
  Flambda.print expr;
*)
  let expr, r =
(*
Format.eprintf "Continuation %a inlining@;%a%!"
  Continuation.print cont Flambda.print expr;
*)
    simplify (E.activate_freshening (E.set_never_inline env)) r expr
  in
(*
Format.eprintf "try_inlining simplification %a ends@;%a\n%!"
  Continuation.print cont Flambda.print expr;
*)
  let inlining_benefit = B.remove_prim (R.benefit r) in
(*  let r = R.map_benefit r (fun _ -> existing_benefit) in *)
  let module W = Inlining_cost.Whether_sufficient_benefit in
  let wsb =
    W.create ~original
      ~toplevel:(E.at_toplevel env)
      ~branch_depth:(E.branch_depth env)
      expr
      ~benefit:inlining_benefit
      ~lifting:false
      ~round:(E.round env)
  in
  if inline_unconditionally || W.evaluate wsb then begin
(*
Format.eprintf "Inlining apply_cont %a to %a%s (inlining benefit %a, desc: %a) Original:\n%a\nInlined:\n%a\n%!"
  Continuation.print cont
  Variable.print_list args
  (if not inline_unconditionally then "" else " (unconditionally)")
  B.print inlining_benefit
  (W.print_description ~subfunctions:false) wsb
  Flambda.print original
  Flambda.print expr;
*)
    Inlined (params, expr)
  end else begin
(*
Format.eprintf "Not inlining apply_cont %a to %a (inlining benefit %a)\n%!"
  Continuation.print cont
  Variable.print_list args
  B.print inlining_benefit;
*)
    Didn't_inline
  end

let find_inlinings r ~simplify =
  let module N = Num_continuation_uses in
  let module U = Inline_and_simplify_aux.Continuation_uses in
  (* We share code between application points that have the same continuation
     and the same arguments. This is done by making a new continuation, whose
     body is the inlined version after simplification of the original
     continuation in the context of such arguments, and redirecting all of the
     uses to that.
     In preparation for this transformation we count up, for each continuation,
     how many uses it has with distinct sets of arguments. *)
  let definitions =
    Continuation.Map.fold (fun cont (uses, approx, env, recursive)
          definitions ->
        match (recursive : Asttypes.rec_flag) with
        | Recursive -> definitions
        | Nonrecursive ->
          let inline_unconditionally = U.linearly_used uses in
          let has_non_inlinable_uses = U.has_non_inlinable_uses uses in
(*
Format.eprintf "Continuation %a used linearly? %b\n%!"
  Continuation.print cont inline_unconditionally;
*)
          List.fold_left (fun definitions (use : U.Use.t) ->
              let args, args_approxs = List.split use.args in
              let key : Continuation_with_args.t = cont, args in
              match Continuation_with_args.Map.find key definitions with
              | exception Not_found ->
                let count =
                  if has_non_inlinable_uses then N.Many
                  else N.One
                in
                Continuation_with_args.Map.add key
                  (inline_unconditionally, count, use.env, approx, args_approxs)
                  definitions
              | inline_unconditionally, count, _env, approx, args_approxs ->
                assert (not inline_unconditionally);
                (* When generating a shared continuation the environment is
                  always that immediately prior to the continuation whose
                  body will be simplified to form the body of the shared
                  continuation. *)
                Continuation_with_args.Map.add key
                  (false, N.(+) count N.One, env, approx, args_approxs)
                  definitions)
            definitions
            (U.inlinable_application_points uses))
      (R.continuation_definitions_with_uses r)
      Continuation_with_args.Map.empty
  in
  Continuation_with_args.Map.fold (fun (cont, args)
            (inline_unconditionally, count, env, approx, args_approxs)
            ((inlinings, new_shared_conts, zero_uses) as acc) ->
      assert ((not inline_unconditionally) || N.linear count);
      let inlining_result =
        match Continuation_approx.handler approx with
        | None -> Didn't_inline
        | Some handler ->
          try_inlining ~cont ~args ~args_approxs ~env ~handler
            ~inline_unconditionally ~count ~simplify
      in
      match inlining_result with
      | Didn't_inline -> acc
      | Inlined (params, body) ->
        begin match (count : N.t) with
        | Zero ->
          inlinings, new_shared_conts, Continuation.Set.add cont zero_uses
        | One ->
          let inlinings =
            Continuation_with_args.Map.add (cont, args) body inlinings
          in
          inlinings, new_shared_conts, zero_uses
        | Many ->
          let new_shared_cont = Continuation.create () in
(*
Format.eprintf "Continuation %a: new shared cont %a with body:@;%a\n%!"
  Continuation.print cont
  Continuation.print new_shared_cont Flambda.print body;
*)
          let apply_shared_cont : Flambda.expr =
            Apply_cont (new_shared_cont, None, args)
          in
          let inlinings =
            Continuation_with_args.Map.add (cont, args)
              apply_shared_cont inlinings
          in
          (* [cont] is recorded because it's the place where the binding of the
             [new_shared_cont] is going to be inserted. *)
          let new_shared_conts =
            let existing =
              match Continuation.Map.find cont new_shared_conts with
              | exception Not_found -> []
              | existing -> existing
            in
            Continuation.Map.add cont
              ((new_shared_cont, params, body) :: existing)
              new_shared_conts
          in
          inlinings, new_shared_conts, zero_uses
        end)
    definitions
    (Continuation_with_args.Map.empty, Continuation.Map.empty,
      Continuation.Set.empty)

(* At the moment this doesn't apply the substitution to handlers as we
   discover inlinings (unlike what happens for function inlining).  Let's
   see how it goes. *)
let substitute (expr : Flambda.expr) ~inlinings ~new_shared_conts
      ~zero_uses =
  Flambda_iterators.map_toplevel_expr (fun (expr : Flambda.t) ->
      match expr with
      | Let_cont { name; body; _ } ->
        let expr =
          if Continuation.Set.mem name zero_uses then
            body
          else
            expr
        in
        begin match Continuation.Map.find name new_shared_conts with
        | exception Not_found -> expr
        | new_shared_conts ->
          List.fold_left (fun expr (name, params, handler) ->
(*
Format.eprintf "Adding shared cont %a\n%!" Continuation.print name;
*)
              Flambda.Let_cont {
                name;
                body = expr;
                handler = Handler {
                  params;
                  recursive = Nonrecursive;
                  handler;
                  specialised_args = Variable.Map.empty;
                };
              })
            expr
            new_shared_conts
        end
      | Apply_cont (cont, trap_action, args) ->
        begin match Continuation_with_args.Map.find (cont, args) inlinings with
        | exception Not_found -> expr
        | inlined_body ->
          match trap_action with
          | None -> inlined_body
          | Some _ ->
            (* Uses like this, with a trap action, will not have been
               counted as inlinable
               (cf. [Inline_and_simplify.simplify_apply_cont]).  However
               there might be other uses with the same continuation and
               arguments and no trap action, which is why we cannot
               fail here. *)
            expr
        end
      | Apply _ | Let _ | Let_mutable _ | Switch _ | Proved_unreachable -> expr)
    expr

let for_toplevel_expression expr r ~simplify =
(*
Format.eprintf "Continuation inlining starting on:@;%a@;" Flambda.print expr;
*)
  let inlinings, new_shared_conts, zero_uses = find_inlinings r ~simplify in
  substitute expr ~inlinings ~new_shared_conts ~zero_uses
