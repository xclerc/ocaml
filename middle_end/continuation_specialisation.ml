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
(*
module A = Simple_value_approx
module B = Inlining_cost.Benefit
module E = Inline_and_simplify_aux.Env
module R = Inline_and_simplify_aux.Result

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
(*
Format.eprintf "Continuation %a used linearly? %b\n%!"
  Continuation.print cont inline_unconditionally;
*)
          List.fold_left (fun definitions (use : U.Use.t) ->
              let args, args_approxs = List.split use.args in
              let key : Continuation_with_args.t = cont, args in
              match Continuation_with_args.Map.find key definitions with
              | exception Not_found ->
                Continuation_with_args.Map.add key
                  (inline_unconditionally, N.One, use.env, approx, args_approxs)
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

*)
