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

module Continuation_with_args = struct
  include Identifiable.Make (struct
    type t = Continuation.t * Variable.t list

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

let try_inlining ~cont
      ~(use : Inline_and_simplify_aux.Continuation_uses.Use.t)
      ~(handler : Flambda.continuation_handler) ~inline_unconditionally
      ~simplify =
  if List.length handler.params <> List.length use.args then begin
    Misc.fatal_errorf "Continuation %a applied with wrong number of arguments"
      Continuation.print cont
  end;
  let expr =
    List.fold_left2 (fun expr param arg ->
        Flambda.create_let param (Var arg) expr)
      handler.handler
      handler.params use.args
  in
  let r = R.create () in
  let original : Flambda.t = Apply_cont (cont, use.args) in
Format.eprintf "try_inlining simplification %a starts\n%!"
  Continuation.print cont;
  let expr, r = simplify (E.activate_freshening use.env) r expr in
Format.eprintf "try_inlining simplification %a ends\n%!"
  Continuation.print cont;
  let inlining_benefit = B.remove_prim (R.benefit r) in
(*  let r = R.map_benefit r (fun _ -> existing_benefit) in *)
  let module W = Inlining_cost.Whether_sufficient_benefit in
  let wsb =
    W.create ~original
      ~toplevel:(E.at_toplevel use.env)
      ~branch_depth:(E.branch_depth use.env)
      expr
      ~benefit:inlining_benefit
      ~lifting:false
      ~round:(E.round use.env)
  in
  if (not inline_unconditionally) && W.evaluate wsb then begin
Format.eprintf "Inlining apply_cont %a to %a%s (inlining benefit %a, desc: %a) Original:\n%a\nInlined:\n%a\n%!"
  Continuation.print cont
  Variable.print_list use.args
  (if not inline_unconditionally then "" else " (unconditionally)")
  B.print inlining_benefit
  (W.print_description ~subfunctions:false) wsb
  Flambda.print original
  Flambda.print expr;
    Inlined (handler.params, expr)
  end else begin
Format.eprintf "Not inlining apply_cont %a to %a (inlining benefit %a)\n%!"
  Continuation.print cont
  Variable.print_list use.args
  B.print inlining_benefit;
    Didn't_inline
  end

type inlining =
  | Seen_one_use_already of
      { params : Variable.t list; inlined : Flambda.expr; }
  | Seen_multiple_uses_already of Continuation.t

let find_inlinings r ~simplify =
  let module U = Inline_and_simplify_aux.Continuation_uses in
  Continuation.Map.fold (fun cont (uses, approx) (new_conts, inlinings) ->
      let inline_unconditionally = U.linearly_used uses in
      List.fold_left (fun (new_conts, inlinings) (use : U.Use.t) ->
          match Continuation_with_args.Map.find (cont, use.args) inlinings with
          | exception Not_found ->
            let inlining_result =
              match Continuation_approx.handler approx with
              | None -> Didn't_inline
              | Some handler ->
                try_inlining ~cont ~use ~handler ~inline_unconditionally
                  ~simplify
            in
            begin match inlining_result with
            | Didn't_inline -> new_conts, inlinings
            | Inlined (params, inlined) ->
              let inlinings =
                Continuation_with_args.Map.add (cont, use.args)
                  (Seen_one_use_already { params; inlined; }) inlinings
              in
              new_conts, inlinings
            end
          | Seen_one_use_already { params; inlined; } ->
            (* Share code between application points that have the same
               continuation and the same arguments.  This is done by making a
               new continuation, whose body is the inlined version after
               simplification of the original continuation in the context of
               such arguments, and redirecting all of the uses to that. *)
            let shared_cont = Continuation.create () in
Format.eprintf "Sharing uses of %a applied to %a, new cont %a\n%!"
  Continuation.print cont
  Variable.print_list use.args
  Continuation.print shared_cont;
(* XXX params needs freshening (params of the new shared cont) *)
            let new_conts =
              Continuation.Map.add cont (shared_cont, params, inlined)
                new_conts
            in
            let inlinings =
              Continuation_with_args.Map.add (cont, use.args)
                (Seen_multiple_uses_already shared_cont)
                inlinings
            in
            new_conts, inlinings
          | Seen_multiple_uses_already _ -> new_conts, inlinings)
        (new_conts, inlinings)
        (U.inlinable_application_points uses))
    (R.continuation_definitions_with_uses r)
    (Continuation.Map.empty, Continuation_with_args.Map.empty)

(* At the moment this doesn't apply the substitution to handlers as we
   discover inlinings (unlike what happens for function inlining).  Let's
   see how it goes.
   Only mapping the [Apply_cont] nodes also means that we need another pass
   of simplify to remove continuation handlers for continuations that don't
   have any remaining uses. *)
let substitute (expr : Flambda.expr) ~new_conts
      ~(inlinings : inlining Continuation_with_args.Map.t) =
  Flambda_iterators.map_toplevel_expr (fun (expr : Flambda.t) ->
      match expr with
      | Let_cont { name; _ } ->
        begin match Continuation.Map.find name new_conts with
        | exception Not_found -> expr
        | (name, params, inlined) ->
          Flambda.Let_cont {
            name;
            body = expr;
            handler = Handler {
              params;
              recursive = Nonrecursive;
              handler = inlined;
            };
          }
        end
      | Apply_cont (cont, args) ->
        begin match Continuation_with_args.Map.find (cont, args) inlinings with
        | exception Not_found -> expr
        | Seen_one_use_already { inlined; } -> inlined
        | Seen_multiple_uses_already cont ->
          Flambda.Apply_cont (cont, args)
        end
      | Apply _ | Let _ | Let_mutable _ | Switch _ -> expr)
    expr

let for_toplevel_expression expr r ~simplify =
  let new_conts, inlinings = find_inlinings r ~simplify in
  substitute expr ~new_conts ~inlinings
