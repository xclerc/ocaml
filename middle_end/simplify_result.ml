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

module Env = Simplify_env

type t =
  (* CR mshinwell: remove [approx]? *)
  { approx : Flambda_type.t;
    (* CR mshinwell: What about combining these next two? *)
    used_continuations : Continuation_uses.t Continuation.Map.t;
    defined_continuations :
      (Continuation_uses.t * Continuation_approx.t * Env.t
          * Asttypes.rec_flag)
        Continuation.Map.t;
    inlining_threshold : Inlining_cost.Threshold.t option;
    benefit : Inlining_cost.Benefit.t;
    num_direct_applications : int;
  }

let create () =
  { approx = Flambda_type.value_bottom;
    used_continuations = Continuation.Map.empty;
    defined_continuations = Continuation.Map.empty;
    inlining_threshold = None;
    benefit = Inlining_cost.Benefit.zero;
    num_direct_applications = 0;
  }

let union t1 t2 =
  { approx = Flambda_type.value_bottom;
    used_continuations =
      Continuation.Map.union_merge Continuation_uses.union
        t1.used_continuations t2.used_continuations;
    defined_continuations =
      Continuation.Map.disjoint_union
        t1.defined_continuations t2.defined_continuations;
    inlining_threshold = t1.inlining_threshold;
    benefit = Inlining_cost.Benefit.(+) t1.benefit t2.benefit;
    num_direct_applications =
      t1.num_direct_applications + t2.num_direct_applications;
  }

let approx t = t.approx
let set_approx t approx = { t with approx }

let meet_approx t env approx =
  let really_import_approx = Env.really_import_approx env in
  let meet =
    Flambda_type.join ~really_import_approx t.approx approx
  in
  set_approx t meet

let use_continuation t env cont kind =
  let args = Continuation_uses.Use.Kind.args kind in
  if not (List.for_all (fun arg -> Env.mem env arg) args) then begin
    Misc.fatal_errorf "use_continuation %a: argument(s) (%a) not in \
        environment %a"
      Continuation.print cont
      Variable.print_list args
      Env.print env
  end;
(*
let k = 6589 in
if Continuation.to_int cont = k then begin
Format.eprintf "Adding use of continuation k%d, args %a approxs %a:\n%s\n%!"
  k
  Variable.print_list args
  (Format.pp_print_list Flambda_type.print)
  (Continuation_uses.Use.Kind.args_approxs kind)
  (Printexc.raw_backtrace_to_string (Printexc.get_callstack 20))
end;
*)
  let uses =
    match Continuation.Map.find cont t.used_continuations with
    | exception Not_found ->
      Continuation_uses.create ~continuation:cont ~backend:(Env.backend env)
    | uses -> uses
  in
  let uses = Continuation_uses.add_use uses env kind in
(*
if Continuation.to_int cont = k then begin
Format.eprintf "Join of args approxs for k%d: %a\n%!"
  k
  (Format.pp_print_list Flambda_type.print)
  (Continuation_uses.meet_of_args_approxs uses ~num_params:1)
end;
*)
  { t with
    used_continuations =
      Continuation.Map.add cont uses t.used_continuations;
  }

let non_recursive_continuations_used_linearly_in_inlinable_position t =
  let used_linearly =
    Continuation.Map.filter (fun _cont (uses, _approx, _env, recursive) ->
(*
Format.eprintf "NRCUL: continuation %a number of uses %d\n%!"
Continuation.print _cont
(List.length uses.Continuation_uses.application_points);
*)
        match (recursive : Asttypes.rec_flag) with
        | Nonrecursive ->
          Continuation_uses.linearly_used_in_inlinable_position uses
        | Recursive -> false)
      t.defined_continuations
  in
  Continuation.Map.keys used_linearly

let forget_continuation_definition t cont =
  { t with
    defined_continuations =
      Continuation.Map.remove cont t.defined_continuations;
  }

let is_used_continuation t i =
  Continuation.Map.mem i t.used_continuations

let used_continuations t =
  Continuation.Map.keys t.used_continuations

let continuation_uses t = t.used_continuations

let no_continuations_in_scope t =
  Continuation.Map.is_empty t.used_continuations

let snapshot_continuation_uses t =
  { Continuation_usage_snapshot.
    used_continuations = t.used_continuations;
    defined_continuations = t.defined_continuations;
  }

let snapshot_and_forget_continuation_uses t =
  let snapshot = snapshot_continuation_uses t in
  let t =
    { t with
      used_continuations = Continuation.Map.empty;
      defined_continuations = Continuation.Map.empty;
    }
  in
  snapshot, t

let roll_back_continuation_uses t (snapshot : Continuation_usage_snapshot.t) =
  { t with
    used_continuations = snapshot.used_continuations;
    defined_continuations = snapshot.defined_continuations;
  }

let continuation_unused t cont =
  not (Continuation.Map.mem cont t.used_continuations)

let continuation_defined t cont =
  Continuation.Map.mem cont t.defined_continuations

let continuation_args_approxs t i ~num_params =
  match Continuation.Map.find i t.used_continuations with
  | exception Not_found ->
(*
Format.eprintf "Continuation %a not in used_continuations, returning bottom\n%!"
Continuation.print i;
*)
    let approxs = Array.make num_params (Flambda_type.value_bottom) in
    Array.to_list approxs
  | uses ->
(*
let approxs =
*)
    Continuation_uses.meet_of_args_approxs uses ~num_params
(*
in
Format.eprintf "Continuation %a IS in used_continuations: %a\n%!"
Continuation.print i
(Format.pp_print_list Flambda_type.print) approxs;
approxs
*)
let defined_continuation_args_approxs t i ~num_params =
  match Continuation.Map.find i t.defined_continuations with
  | exception Not_found ->
    let approxs = Array.make num_params (Flambda_type.value_bottom) in
    Array.to_list approxs
  | (uses, _approx, _env, _recursive) ->
    Continuation_uses.meet_of_args_approxs uses ~num_params

let exit_scope_catch t env i =
(*
  Format.eprintf "exit_scope_catch %a\n%!" Continuation.print i;
*)
  let t, uses =
    match Continuation.Map.find i t.used_continuations with
    | exception Not_found ->
(*
Format.eprintf "no uses\n%!";
*)
      let uses =
        Continuation_uses.create ~continuation:i ~backend:(Env.backend env)
      in
      t, uses
    | uses ->
(*
let application_points =
Continuation_uses.application_points uses
in
Format.eprintf "Uses:\n";
let count = ref 1 in
List.iter (fun (use : Continuation_uses.Use.t) ->
let env = use.env in
Format.eprintf "Use %d: %a@ \n%!"
  (!count) Env.print env;
incr count)
application_points;
*)
      { t with
        used_continuations = Continuation.Map.remove i t.used_continuations;
      }, uses
  in
  assert (continuation_unused t i);
(*
  Format.eprintf "exit_scope_catch %a finished.\n%!" Continuation.print i;
let application_points =
Continuation_uses.application_points uses
in
Format.eprintf "Uses being returned:\n";
let count = ref 1 in
List.iter (fun (use : Continuation_uses.Use.t) ->
let env = use.env in
Format.eprintf "Use %d: %a@ \n%!"
  (!count) Env.print env;
incr count)
application_points;
*)
  t, uses

let update_all_continuation_use_environments t ~if_present_in_env
      ~then_add_to_env =
  let used_continuations =
    Continuation.Map.map (fun uses ->
          Continuation_uses.update_use_environments uses
            ~if_present_in_env ~then_add_to_env)
      t.used_continuations
  in
  let defined_continuations =
    Continuation.Map.map (fun (uses, approx, env, recursive) ->
        let uses =
          Continuation_uses.update_use_environments uses
            ~if_present_in_env ~then_add_to_env
        in
        uses, approx, env, recursive)
      t.defined_continuations
  in
  { t with
    used_continuations;
    defined_continuations;
  }

let define_continuation t cont env recursive uses approx =
(*    Format.eprintf "define_continuation %a\n%!" Continuation.print cont;*)
(*
let k = 25987 in
if Continuation.to_int cont = k then begin
Format.eprintf "Defining continuation k%d:\n%s%!"
  k
  (Printexc.raw_backtrace_to_string (Printexc.get_callstack 30))
end;
*)
  Env.invariant env;
  if Continuation.Map.mem cont t.used_continuations then begin
    Misc.fatal_errorf "Must call exit_scope_catch before \
        define_continuation %a"
      Continuation.print cont
  end;
  if Continuation.Map.mem cont t.defined_continuations then begin
    Misc.fatal_errorf "Cannot redefine continuation %a"
      Continuation.print cont
  end;
  { t with
    defined_continuations =
      Continuation.Map.add cont (uses, approx, env, recursive)
        t.defined_continuations;
  }

let update_defined_continuation_approx t cont approx =
  match Continuation.Map.find cont t.defined_continuations with
  | exception Not_found ->
    Misc.fatal_errorf "Cannot update approximation of undefined \
        continuation %a"
      Continuation.print cont
  | (uses, _old_approx, env, recursive) ->
    { t with
      defined_continuations =
        Continuation.Map.add cont (uses, approx, env, recursive)
          t.defined_continuations;
    }

let continuation_definitions_with_uses t =
  t.defined_continuations

let map_benefit t f =
  { t with benefit = f t.benefit }

let add_benefit t b =
  { t with benefit = Inlining_cost.Benefit.(+) t.benefit b }

let benefit t = t.benefit

let reset_benefit t =
  { t with benefit = Inlining_cost.Benefit.zero; }

let set_inlining_threshold t inlining_threshold =
  { t with inlining_threshold }

let add_inlining_threshold t j =
  match t.inlining_threshold with
  | None -> t
  | Some i ->
    let inlining_threshold = Some (Inlining_cost.Threshold.add i j) in
    { t with inlining_threshold }

let sub_inlining_threshold t j =
  match t.inlining_threshold with
  | None -> t
  | Some i ->
    let inlining_threshold = Some (Inlining_cost.Threshold.sub i j) in
    { t with inlining_threshold }

let inlining_threshold t = t.inlining_threshold

let seen_direct_application t =
  { t with num_direct_applications = t.num_direct_applications + 1; }

let num_direct_applications t =
  t.num_direct_applications
