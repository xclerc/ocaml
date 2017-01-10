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

module Continuation_with_specialised_args = struct
  (* A continuation together with, for each of its specialised arguments, the
     variable corresponding to such argument in a particular application of
     that continuation.
  *)
  type t = Continuation.t * Flambda.specialised_args

  include Identifiable.Make (struct
    type nonrec t = t

    let compare t1 t2 =
      let c = Continuation.compare (fst t1) (fst t2) in
      if c <> 0 then c
      else (Variable.Map.compare Variable.compare) (snd t1) (snd t2)

    let equal t1 t2 =
      compare t1 t2 = 0

    let hash t =
      Hashtbl.hash (Continuation.hash (fst t),
        (Variable.Map.hash Variable.hash) (snd t))

    let output _chan _t = Misc.fatal_error "not implemented"
    let print _ppf _t = Misc.fatal_error "not implemented"
  end)
end

type specialising_result =
  | Didn't_specialise
  | Specialised of Continuation.t * Flambda.continuation_handler

let try_specialising ~cont ~(old_handler : Flambda.continuation_handler)
      ~(specialised_args : Flambda.specialised_args) ~env ~simplify =
  let freshening =
    List.map (fun param -> param, Variable.rename param) handler.params
  in
  let subst = Variable.Map.of_list freshening in
  let handler =
    Flambda_utils.toplevel_substitution subst handler.handler
  in
  let params = List.map snd freshening in


let find_specialisations r ~simplify =
  let module N = Num_continuation_uses in
  let module U = Inline_and_simplify_aux.Continuation_uses in
  (* The first step constructs a map:
          (continuation * (specialised_params -> arg))
       -> set of (continuation * args)
     which groups together uses of the continuation where some subset of
     its invariant parameters have the same arguments across those uses.  The
     range of the map enables identification of the corresponding [Apply_cont]
     nodes which will need to be repointed if the continuation is specialised
     for those uses. *)
  let specialisations =
    (* CR mshinwell: [recursive] appears to be redundant with
      [approx.recursive] *)
    Continuation.Map.fold (fun cont (uses, approx, env, recursive)
          specialisations ->
        match (recursive : Asttypes.rec_flag) with
        | Nonrecursive -> specialisations
        | Recursive ->
          match Continuation_approx.handler approx with
          | None -> specialisations
          | Some handler ->
            let invariant_params =
              Invariant_params.invariant_params_of_continuation cont handler
            in
            List.fold_left (fun specialisations (use : U.Use.t) ->
                assert (List.length handler.params = List.length use.args);
                let params_with_args =
                  Variable.Map.of_list (List.combine handler.params use.args)
                in
                let params_with_specialised_args =
                  Variable.Map.filter (fun param (_arg, arg_approx) ->
                      Variable.Set.mem param invariant_params
                        && not (Variable.Map.mem param
                          handler.specialised_args)
                        && A.useful arg_approx)
                    params_with_args
                in
                if Variable.Map.cardinal params_with_specialised_args < 1 then
                  new_conts, uses_to_new_conts
                else
                  let params_with_specialised_args =
                    Variable.Map.map (fun (arg, _) : Flambda.specialised_to ->
                        { var = arg;
                          projection = None;
                        })
                      params_with_specialised_args
                  in
                  let key : Continuation_with_specialised_args.t =
                    cont, params_with_specialised_args
                  in
                  let uses =
                    match
                      Continuation_with_specialised_args.Map.find key
                        specialisations
                    with
                    | exception Not_found -> Continuation_with_args.Set.empty
                    | uses -> uses
                  in
                  Continuation_with_specialised_args.Map.add key
                    (Continuation_with_args.Set.add (cont, use.args) uses)
                    specialisations)
              Continuation_with_specialised_args.Map.empty
              (U.inlinable_application_points uses))
      (R.continuation_definitions_with_uses r)
      Continuation_with_specialised_args.Map.empty
  in
  (* The second step takes the map from above and makes a decision for
     each proposed specialisation, returning two maps:
       continuation "k" -> new continuations to be defined just before "k"
       (continuation * args) -> new continuation
     The first map is then used to add new [Let_cont] definitions and the
     second is used to rewrite [Apply_cont] to specialised continuations. *)
  Continuation_with_specialised_args.Map.fold (fun (cont, spec_args)
          cont_application_points ((new_conts, apply_cont_rewrites) as acc) ->
      match
        try_specialising ~cont ~handler ~specialised_args ~env ~simplify
      with
      | Didn't_specialise -> acc
      | Specialised (new_cont, handler) ->
        let existing_conts =
          match Continuation.Map.find cont new_conts with
          | exception Not_found -> []
          | existing_conts -> existing_conts
        in
        let new_conts =
          Continuation.Map.add cont ((new_cont, handler) :: existing_conts)
            new_conts
        in
        let apply_cont_rewrites =
          Continuation_with_args.Set.fold (fun ((cont', args) as key)
                  apply_cont_rewrites ->
              assert (Continuation.equal cont cont');
              assert (not (Continuation.Map.mem key apply_cont_rewrites));
              Continuation.Map.add key new_cont apply_cont_rewrites)
            cont_application_points
            apply_cont_rewrites
        in
        new_conts, apply_cont_rewrites)
    specialisations
    (Continuation.Map.empty, Continuation.With_args.Map.empty)

let insert_specialisations (expr : Flambda.expr) ~new_conts
        ~apply_cont_rewrites =
  Flambda_iterators.map_toplevel_expr (fun (expr : Flambda.t) ->
      match expr with
      | Let_cont { name; _ } ->
        begin match Continuation.Map.find name new_conts with
        | exception Not_found -> expr
        | new_conts ->
          List.fold_left (fun body (new_cont, handler) ->
              Let_cont {
                name = new_cont;
                body;
                handler;
              })
            expr
            new_conts
        end
      | Apply_cont (cont, trap_action, args) ->
        begin match Continuation.Map.find cont apply_cont_rewrites with
        | exception Not_found -> expr
        | new_cont ->
          assert (trap_action = None);
          Apply_cont (new_cont, None, args)
        end
      | Apply _ | Let _ | Let_mutable _ | Switch _ | Proved_unreachable -> expr)
    expr

let for_toplevel_expression expr r ~simplify =
  let new_conts, apply_cont_rewrites = find_specialisations r ~simplify in
  insert_specialisations expr ~new_conts ~apply_cont_rewrites
