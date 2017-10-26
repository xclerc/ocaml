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

(* CR mshinwell: the name Projection is misleading now *)

(** Representation of projections from closures and blocks. *)

(** The selection of one closure given a set of closures, required before
    a function defined by said set of closures can be applied.  See more
    detailed documentation below on [set_of_closures]. *)
module Project_closure : sig
  type t = {
    set_of_closures : Variable.t; (** must yield a set of closures *)
    closure_id : Closure_id.Set.t;
    (** Every closure_id from the set must come from a different set.
        A projection with multiple potential closures represents a
        conditional projection depending on the given set of closures.
        The set of closures is implicit as there can also be only one
        set defining a given closure_id. *)
  }

  include Identifiable.S with type t := t
end

(** The selection of one closure given another closure in the same set of
    closures.  See more detailed documentation below on [set_of_closures].
    The [move_to] closure must be part of the free variables of
    [start_from]. *)
module Move_within_set_of_closures : sig
  type t = {
    closure : Variable.t;  (** must yield a closure *)
    move : Closure_id.t Closure_id.Map.t;
    (** For each possible value of closures, get a different closure
        from the set. *)
  }

  include Identifiable.S with type t := t
end

(** The selection from a closure of a variable bound by said closure.
    In other words, access to a function's environment.  Also see more
    detailed documentation below on [set_of_closures]. *)
module Project_var : sig
  type t = {
    closure : Variable.t;  (** must yield a closure *)
    (* CR mshinwell: Change the name of [var]. *)
    var : Var_within_closure.t Closure_id.Map.t;
    (** For each possible value of closure, get a different field of the
        closure. *)
  }

  include Identifiable.S with type t := t
end

type t =
  | Project_var of Project_var.t
  | Project_closure of Project_closure.t
  | Move_within_set_of_closures of Move_within_set_of_closures.t
  | Pure_primitive of Flambda_primitive.t
  (** "Pure" means both no effects and no coeffects. *)
  | Field of int * Variable.t
  | Switch of Variable.t

include Identifiable.S with type t := t

(** Return which variable the given projection projects from. *)
val projecting_from : t -> Variable.t

(** Change the variable that the given projection projects from. *)
val map_projecting_from : t -> f:(Variable.t -> Variable.t) -> t

(** Free variables of the given projection. *)
val free_variables : t -> Variable.Set.t
