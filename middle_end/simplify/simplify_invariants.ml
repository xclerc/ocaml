(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2017 OCamlPro SAS                                    *)
(*   Copyright 2014--2017 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module R = Simplify_result

let check_toplevel_simplification_result r expr ~continuation ~descr =
  if !Clflags.flambda_invariant_checks then begin
    let without_definitions = R.used_continuations r in
    let bad_without_definitions =
      Continuation.Set.remove continuation without_definitions
    in
    if not (Continuation.Set.is_empty bad_without_definitions) then begin
      Misc.fatal_errorf "The following continuations in %s \
          had uses but no definitions recorded for them in [r]: %a.  \
          Term:\n@ %a"
        descr
        Continuation.Set.print bad_without_definitions
        Flambda.Expr.print expr
    end;
    let continuation_definitions_with_uses =
      R.continuation_definitions_with_uses r
    in
    let defined_continuations_in_r =
      Continuation.Map.keys continuation_definitions_with_uses
    in
    let defined_continuations =
      Flambda_utils.all_defined_continuations_toplevel expr
    in
    (* This is deliberately a strong condition. *)
    if not (Continuation.Set.equal defined_continuations_in_r
      defined_continuations)
    then begin
      Misc.fatal_errorf "Defined continuations in [r] (%a) do not match those \
          defined in %s (%a) (in [r] but not in the term: %a; \
          in the term but not in [r]: %a):@ \n%a"
        Continuation.Set.print defined_continuations_in_r
        descr
        Continuation.Set.print defined_continuations
        Continuation.Set.print
        (Continuation.Set.diff defined_continuations_in_r
          defined_continuations)
        Continuation.Set.print
        (Continuation.Set.diff defined_continuations
          defined_continuations_in_r)
        Flambda.Expr.print expr
    end;
    (* CR mshinwell: The following could check the actual code in the
       continuation approximations matches the code in the term. *)
    let all_handlers_in_continuation_approxs =
      Continuation.Map.fold (fun _cont (_, approx, _, _) all_handlers ->
          match Continuation_approx.handlers approx with
          | None -> all_handlers
          | Some (Nonrecursive _) ->
            Continuation.Set.add (Continuation_approx.name approx) all_handlers
          | Some (Recursive handlers) ->
            Continuation.Set.union all_handlers
              (Continuation.Map.keys handlers))
        (R.continuation_definitions_with_uses r)
        Continuation.Set.empty
    in
    if not (Continuation.Set.equal defined_continuations
      all_handlers_in_continuation_approxs)
    then begin
      Misc.fatal_errorf "Continuations don't match up between the \
          continuation approximations in [r] (%a) and the term \
          (%a):@ \n%a\n"
        Continuation.Set.print all_handlers_in_continuation_approxs
        Continuation.Set.print defined_continuations
        Flambda.Expr.print expr
    end;
    (* Checking the number of uses recorded in [r] is correct helps to catch
       bugs where, for example, some [Value_unknown] approximation for some
       argument of some continuation fails to be removed by a transformation
       that produces a more precise approximation (which can cause the
       join of the argument's approximations to remain at [Value_unknown]). *)
    let counts = Flambda_utils.count_continuation_uses_toplevel expr in
    Continuation.Map.iter (fun cont (uses, _, _, _) ->
        let num_in_term =
          match Continuation.Map.find cont counts with
          | exception Not_found -> 0
          | count -> count
        in
        let num_in_r =
          Simplify_aux.Continuation_uses.num_uses uses
        in
(*
let application_points =
  Simplify_aux.Continuation_uses.application_points uses
in
Format.eprintf "Uses of continuation %a:\n" Continuation.print cont;
let count = ref 1 in
List.iter (fun (use : Simplify_aux.Continuation_uses.Use.t) ->
  let env = use.env in
  Format.eprintf "Use %d: %a@ \n%!"
    (!count) Simplify_env.print env;
  incr count)
application_points;
*)
        if num_in_term <> num_in_r then begin
          Misc.fatal_errorf "Continuation count mismatch for %a between the \
              term (%d) and [r] (%d): %a@ %a"
            Continuation.print cont
            num_in_term
            num_in_r
            Simplify_aux.Continuation_uses.print uses
            Flambda.Expr.print expr
        end)
      continuation_definitions_with_uses
  end
