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

(** The result structure used during simplification.  (See simplify.ml.) *)

module Continuation_uses : sig
  module Use : sig
    module Kind : sig
      type t =
        | Not_inlinable_or_specialisable of Flambda_type.t list
          (** Do not attempt to inline or specialise the continuation at this
              use point. *)
        | Inlinable_and_specialisable of
            (Variable.t * Flambda_type.t) list
          (** The continuation may be inlined or specialised at this
              use point. *)
        | Only_specialisable of (Variable.t * Flambda_type.t) list
          (** The continuation may be specialised but not inlined at this use
              point.  (Used for [Apply_cont] which have a [trap_action].) *)

      val is_specialisable
         : t
        -> (Variable.t * Flambda_type.t) list option
    end

    type t = private {
      kind : Kind.t;
      env : Env.t;
    }
  end

  type t

  val create
     : continuation:Continuation.t
    -> backend:(module Backend_intf.S)
    -> t

  val print : Format.formatter -> t -> unit

  val application_points : t -> Use.t list

  val unused : t -> bool
  val linearly_used : t -> bool

  val num_uses : t -> int

  val meet_of_arg_tys
     : t
    -> num_params:int
    -> Flambda_type.t list

  val meet_of_arg_tys_opt : t -> Flambda_type.t list option
end

module Continuation_usage_snapshot : sig
  type t

  val continuations_defined_between_snapshots
     : before:t
    -> after:t
    -> Continuation.Set.t
end

type t

val create : unit -> t

val union : t -> t -> t

(** Check that [prepare_for_continuation_uses] has been called on the given
    result structure. *)
val is_used_continuation : t -> Continuation.t -> bool

(** Mark that the given continuation has been used and provide
    an approximation for the arguments. *)
val use_continuation
  : t
  -> Env.t
  -> Continuation.t
  -> Continuation_uses.Use.Kind.t
  -> t

val snapshot_continuation_uses : t -> Continuation_usage_snapshot.t

val snapshot_and_forget_continuation_uses
   : t
  -> Continuation_usage_snapshot.t * t

val roll_back_continuation_uses : t -> Continuation_usage_snapshot.t -> t

val continuation_unused : t -> Continuation.t -> bool
val continuation_defined : t -> Continuation.t -> bool

val continuation_args_types
   : t
  -> Continuation.t
  -> arity:Flambda_arity.t
  -> Flambda_type.t list

(* CR mshinwell: improve names of these two functions *)
val defined_continuation_args_types
   : t
  -> Continuation.t
  -> arity:Flambda_arity.t
  -> Flambda_type.t list

(** Continuation usage information for use after examining the body of
    a [Let_cont] but before [define_continuation] has been called. *)
val continuation_uses : t -> Continuation_uses.t Continuation.Map.t

val non_recursive_continuations_used_linearly_in_inlinable_position
   : t
  -> Continuation.Set.t

(** Mark that we are moving up out of the scope of a continuation-binding
    construct. *)
val exit_scope_catch
   : t
  -> Env.t
  -> Continuation.t
  -> t * Continuation_uses.t

(** Record the post-simplification definition of a continuation. *)
val define_continuation
   : t
  -> Continuation.t
  -> Env.t
  -> Flambda.recursive
  -> Continuation_uses.t
  -> Continuation_approx.t
  -> t

(** Update all use environments (both for "used" and "defined" continuations)
    such that if [is_present_in_env] is in such an environment then
    [then_add_to_env] will be added with the given approximation.

    This is used after wrappers have been added during continuation unboxing
    to keep [r] up to date. *)
val update_all_continuation_use_environments
   : t
  -> if_present_in_env:Continuation.t
  -> then_add_to_env:(Continuation.t * Continuation_approx.t)
  -> t

(** Update the approximation for a defined continuation. *)
val update_defined_continuation_approx
   : t
  -> Continuation.t
  -> Continuation_approx.t
  -> t

(** Continuation definition information for the inliner. *)
val continuation_definitions_with_uses
   : t
  -> (Continuation_uses.t * Continuation_approx.t * Env.t
    * Flambda.recursive) Continuation.Map.t

val forget_continuation_definition
   : t
  -> Continuation.t
  -> t

(** Check that there is no continuation binding construct in scope. *)
val no_continuations_in_scope : t -> bool

(** All continuations for which [continuation_uses] has been
    called on the given result structure.  O(n*log(n)). *)
val used_continuations : t -> Continuation.Set.t

(** The benefit to be gained by inlining the subexpression whose
    simplification yielded the given result structure. *)
val benefit : t -> Inlining_cost.Benefit.t

(** Apply a transformation to the inlining benefit stored within the
    given result structure. *)
val map_benefit
  : t
  -> (Inlining_cost.Benefit.t -> Inlining_cost.Benefit.t)
  -> t

(** Add some benefit to the inlining benefit stored within the
    given result structure. *)
val add_benefit : t -> Inlining_cost.Benefit.t -> t

(** Set the benefit of inlining the subexpression corresponding to the
    given result structure to zero. *)
val reset_benefit : t -> t

val set_inlining_threshold :
  t -> Inlining_cost.Threshold.t option -> t
val add_inlining_threshold :
  t -> Inlining_cost.Threshold.t -> t
val sub_inlining_threshold :
  t -> Inlining_cost.Threshold.t -> t
val inlining_threshold : t -> Inlining_cost.Threshold.t option

val seen_direct_application : t -> t
val num_direct_applications : t -> int
