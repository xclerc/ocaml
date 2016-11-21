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
  | Inlined of Flambda.expr

let try_inlining r ~cont
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
(*  let existing_benefit = R.benefit r in *)
  let r = R.reset_benefit r in
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
(*
Format.eprintf "Inlining apply_cont %a to %a%s (inlining benefit %a, desc: %a) Original:\n%a\nInlined:\n%a\n%!"
  Continuation.print cont
  Variable.print_list use.args
  (if not inline_unconditionally then "" else " (unconditionally)")
  B.print inlining_benefit
  (W.print_description ~subfunctions:false) wsb
  Flambda.print original
  Flambda.print expr;
*)
    Inlined expr
  end else begin
(*
Format.eprintf "Not inlining apply_cont %a to %a (inlining benefit %a)\n%!"
  Continuation.print cont
  Variable.print_list use.args
  B.print inlining_benefit;
*)
    Didn't_inline
  end

let find_inlinings r ~simplify =
  let all_uses = R.continuation_uses r in
  let module U = Inline_and_simplify_aux.Continuation_uses in
  Continuation.Map.fold (fun cont (uses : U.t) inlinings ->
      let handler = U.handler uses in
      let inline_unconditionally = U.linearly_used uses in
      List.fold_left (fun inlinings (use : U.Use.t) ->
          let inlining_result =
            match handler with
            | None -> Didn't_inline  (* e.g. a return continuation *)
            | Some handler ->
              try_inlining r ~cont ~use ~handler ~inline_unconditionally
                ~simplify
          in
          match inlining_result with
          | Didn't_inline -> inlinings
          | Inlined inlined ->
            Continuation_with_args.Map.add (cont, use.args) inlined inlinings)
        inlinings
        (U.inlinable_application_points uses))
    all_uses
    Continuation_with_args.Map.empty

(* At the moment this doesn't apply the substitution to handlers as we
   discover inlinings (unlike what happens for function inlining).  Let's
   see how it goes.
   Only mapping the [Apply_cont] nodes also means that we need another pass
   of simplify to remove continuation handlers for continuations that don't
   have any remaining uses. *)
let substitute (expr : Flambda.expr)
      (subst : Flambda.expr Continuation_with_args.Map.t) =
  Flambda_iterators.map_toplevel_apply_cont expr
    ~f:(fun cont args ->
      match Continuation_with_args.Map.find (cont, args) subst with
      | exception Not_found -> None
      | expr -> Some expr)

let for_toplevel_expression expr r ~simplify =
  let subst = find_inlinings r ~simplify in
  substitute expr subst
