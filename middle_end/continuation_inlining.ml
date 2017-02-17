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

module B = Inlining_cost.Benefit
module E = Inline_and_simplify_aux.Env
module R = Inline_and_simplify_aux.Result

type inlining_result =
  | Didn't_inline
  | Inlined of Variable.t list * (Flambda.expr array) * R.t

type num_uses = {
  has_non_inlinable_uses : bool;
  inlinable_uses : int;
}

let try_inlining r ~cont ~args ~args_approxs ~env
        ~(handler : Flambda.continuation_handler)
      ~inline_unconditionally ~(count : num_uses) ~simplify =
  if List.length handler.params <> List.length args then begin
    Misc.fatal_errorf "Continuation %a applied with wrong number of arguments"
      Continuation.print cont
  end;
  assert (count.inlinable_uses >= 1);
  assert (List.length args = List.length args_approxs);
  let params, env, expr =
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
  in
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
    simplify (E.activate_freshening (
        E.disallow_continuation_inlining (E.set_never_inline env)))
      r expr
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
    let exprs, r =
      (* For a given (continuation, arguments) pair we need as many
         freshened copies of the continuation as there are occurrences of that
         pair in the overall expression. *)
      let r = ref r in
      let exprs =
        Array.init count.inlinable_uses (fun index ->
          if index < 1 then begin
            expr
          end else begin
            let expr, r =
              simplify (E.activate_freshening (
                  (E.disallow_continuation_inlining (E.set_never_inline env))))
                !r expr
            in
            r := r;
            expr
          end)
      in
      exprs, !r
    in
    Inlined (params, exprs, r)
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
  (* Count up, for each continuation, how many uses it has with distinct
     sets of arguments. *)
  let definitions =
    Continuation.Map.fold (fun cont (uses, approx, _env, recursive)
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
              let key : Continuation.With_args.t = cont, args in
              match Continuation.With_args.Map.find key definitions with
              | exception Not_found ->
                let count : num_uses =
                  { has_non_inlinable_uses;
                    inlinable_uses = 1;
                  }
                in
                Continuation.With_args.Map.add key
                  (inline_unconditionally, count, use.env, approx, args_approxs)
                  definitions
              | inline_unconditionally, count, _env, approx, args_approxs ->
                assert (not inline_unconditionally);
                let count =
                  { count with
                    inlinable_uses = count.inlinable_uses + 1;
                  }
                in
                Continuation.With_args.Map.add key
                  (false, count, use.env, approx, args_approxs)
                  definitions)
            definitions
            (U.inlinable_application_points uses))
      (R.continuation_definitions_with_uses r)
      Continuation.With_args.Map.empty
  in
  Continuation.With_args.Map.fold (fun (cont, args)
            (inline_unconditionally, count, env, approx, args_approxs)
            ((inlinings, zero_uses, r) as acc) ->
      if count.inlinable_uses < 1 && not count.has_non_inlinable_uses then acc
      else
        let inlining_result =
          match Continuation_approx.handlers approx with
          | None | Some (Recursive _) -> Didn't_inline
          | Some (Nonrecursive { is_exn_handler = true; }) ->
            (* This should be caught by handling of [Apply_cont] in
               [Inline_and_simplify], but just to be on the safe side... *)
            Didn't_inline
          | Some (Nonrecursive handler) ->
            let inline_unconditionally =
              (* CR-soon mshinwell: Stubs should probably just be immediately
                 inlined by [Inline_and_simplify] upon the first traversal. *)
              inline_unconditionally || handler.stub
            in
            try_inlining ~cont ~args ~args_approxs ~env ~handler
              ~inline_unconditionally ~count ~simplify
        in
        match inlining_result with
        | Didn't_inline -> acc
        | Inlined (_params, bodies, r) ->
          let inlinings =
            Continuation.With_args.Map.add (cont, args) bodies inlinings
          in
          inlinings, zero_uses, r)
    definitions
    (Continuation.With_args.Map.empty, Continuation.Set.empty, r)

(* At the moment this doesn't apply the substitution to handlers as we
   discover inlinings (unlike what happens for function inlining).  Let's
   see how it goes. *)
let substitute r (expr : Flambda.expr) ~inlinings ~zero_uses =
  let counts = Continuation.With_args.Tbl.create 42 in
  let r = ref r in
  let expr =
    Flambda_iterators.map_toplevel_expr (fun (expr : Flambda.t) ->
        match expr with
        (* [Inline_and_simplify] will only put non-bottom continuation
           approximations in the environment for non-recursive continuations
           at present. *)
        | Let_cont { body; handlers = Nonrecursive { name; _ }; } ->
          if Continuation.Set.mem name zero_uses then body
          else expr
        | Apply_cont (cont, trap_action, args) ->
          (* Uses are forgotten one by one: it's possible that new calls to
             a continuation being inlined out, with the same arguments as
             at a point where it is being inlined, arose whilst inlining some
             other continuation.  As such we can't just unilaterally forget all
             uses of (cont, args) within [r]. *)
          r := R.forget_one_continuation_use r cont ~args;
          begin match Continuation.With_args.Map.find (cont, args) inlinings with
          | exception Not_found -> expr
          | inlined_bodies ->
            let count =
              (* Find out how many of this (cont, args) pair we've seen so far,
                 so we can select the correct freshened body. *)
              match Continuation.With_args.Tbl.find counts (cont, args) with
              | exception Not_found -> 0
              | count -> count
            in
            if count >= Array.length inlined_bodies then begin
              Misc.fatal_errorf "Not enough copies of the freshened inlined \
                  body to substitute out all applications of %a to %a"
                Continuation.print cont
                Variable.print_list args
            end;
            Continuation.With_args.Tbl.replace counts (cont, args) (count + 1);
            let inlined_body = inlined_bodies.(count) in
            match trap_action with
            | None ->
              inlined_body
            | Some trap_action ->
              (* CR mshinwell: This should maybe be done instead by
                 [Continuation_specialisation].  This probably requires
                 changing [Continuation_uses] so it can track which uses are
                 inlinable and which are only specialisable, or similar.
                 (May be a good change anyway.) *)
              (* We have to eta-expand in order to preserve the trap. *)
              let new_cont = Continuation.create () in
              Let_cont {
                body = Apply_cont (new_cont, Some trap_action, []);
                handlers = Nonrecursive {
                  name = new_cont;
                  handler = {
                    params = [];
                    handler = inlined_body;
                    stub = false;
                    is_exn_handler = false;
                    specialised_args = Variable.Map.empty;
                  };
                };
              }
          end
        | Apply _ | Let _ | Let_cont _ | Let_mutable _ | Switch _
        | Proved_unreachable -> expr)
      expr
  in
  expr, r

let for_toplevel_expression expr r ~simplify =
(*
Format.eprintf "Continuation inlining starting on:@;%a@;" Flambda.print expr;
*)
  let inlinings, zero_uses, r = find_inlinings r ~simplify in
let expr, r =  substitute r expr ~inlinings ~zero_uses in
(*
Format.eprintf "Continuation inlining returns:@;%a@;" Flambda.print expr;
*)
expr, r
