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

module A = Simple_value_approx
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

module Use = struct
  type t = {
    args : Variable.t list;
    env : E.t;
  }
end

module Uses : sig
  type t

  val create : handler:Flambda.continuation_handler -> t

  val add_inlinable_use
     : t
    -> env:E.t
    -> args:Variable.t list
    -> t

  val add_non_inlinable_use : t -> t

  val handler : t -> Flambda.continuation_handler
  val linearly_used : t -> bool
end = struct
  type t = {
    handler : Flambda.continuation_handler;
    inlinable_application_points : Use.t list;
    num_non_inlinable_application_points : Num_continuation_uses.t;
  }

  let create ~handler =
    { handler;
      inlinable_application_points = [];
      num_non_inlinable_application_points = 0;
    }

  let add_inlinable_use t ~env ~args =
    { t with
      inlinable_application_points =
        (env, args) :: t.inlinable_application_points;
    }

  let add_non_inlinable_use t =
    { t with
      num_non_inlinable_application_points =
        t.num_non_inlinable_application_points + 1;
    }

  let num_inlinable_application_points t : Num_continuation_uses.t =
    match t.application_points with
    | [] -> Zero
    | [_] -> One
    | _ -> Many

  let linearly_used t =
    match num_inlinable_application_points t,
      t.num_non_inlinable_application_points
    with
    | One, Zero -> true
    | _, _ -> false
end

type inlining_result =
  | Didn't_inline
  | Inlined of Flambda.expr

let try_inlining ~use ~(handler : Flambda.continuation_handler)
      ~inline_unconditionally ~simplify =
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
  let existing_benefit = R.benefit r in
  let r = R.reset_benefit r in
  let original : Flambda.t = Apply_cont (cont, use.args) in
  let expr, r = simplify (E.activate_freshening use.env) r expr in
  let inlining_benefit = B.remove_prim (R.benefit r) in
  let r = R.map_benefit r (fun _ -> existing_benefit) in
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
  if (not inline_unconditionally) || W.evaluate wsb then begin
(*
Format.eprintf "Inlining apply_cont %a to %a%s (inlining benefit %a, desc: %a) Original:\n%a\nInlined:\n%a\n%!"
  Continuation.print cont
  Variable.print_list use.args
  (if check_benefit then "" else " (unconditionally)")
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
    Don't_inline
  end

let find_inlinings expr r ~simplify =
  let all_uses = R.continuation_uses r in
  Continuation.Map.fold (fun inlinings cont (uses : Uses.t) ->
      let handler = Uses.handler uses in
      let inline_unconditionally = Uses.linearly_used uses in
      List.fold_left (fun inlinings use ->
          let inlining_result =
            try_inlining ~use ~handler ~inline_unconditionally ~simplify
          in
          match inlining_result with
          | Didn't_inline -> inlinings
          | Inlined inlined ->
            Continuation_with_args.Map.add (cont, use.args) inlined inlinings)
        inlinings
        uses.application_points)
    Continuation_with_args.Map.empty
    all_uses

(* At the moment this doesn't apply the substitution to handlers as we
   discover inlinings (unlike what happens for function inlining).  Let's
   see how it goes. *)
let substitute (expr : Flambda.expr)
      (subst : Flambda.expr Continuation_with_args.Map.t) =
  Flambda_iterators.map_toplevel_apply_cont expr
    ~f:(fun cont args ->
      match Continuation_with_args.Map.find (cont, args) subst with
      | exception Not_found -> None
      | expr -> Some expr)

let for_toplevel_expression expr r ~simplify =
  let subst = find_inlinings expr r ~simplify in
  substitute expr subst
