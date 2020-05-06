(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-30-40-41-42"]

module type S = sig
  type flambda_type
  type typing_env
  type typing_env_extension
  type typing_env_level
  type meet_env
  type meet_or_join_env
  type head

  module Descr : sig
    type t = private
      | No_alias of head Or_unknown_or_bottom.t
        (** For each kind there is a lattice of types.
            Unknown = "Any value can flow to this point": the top element.
            Bottom = "No value can flow to this point": the least element.
        *)
      | Equals of Simple.t
      | Type of Export_id.t
  end

  type t

  val print_with_cache : cache:Printing_cache.t -> Format.formatter -> t -> unit

  val print : Format.formatter -> t -> unit

  val create_no_alias : head Or_unknown_or_bottom.t -> t
  val create_equals : Simple.t -> t
  val create_type : Export_id.t -> t

  val create : head -> t

  val unknown : unit -> t
  val bottom : unit -> t

  val descr : t -> Descr.t

  val get_alias_exn : t -> Simple.t

  val is_obviously_bottom : t -> bool
  val is_obviously_unknown : t -> bool

  (* CR mshinwell: Try to use [Type_structure_intf] or similar *)

  include Contains_names.S with type t := t

  val apply_coercion : t -> Coercion.t -> t Or_bottom.t

  val expand_head
     : force_to_kind:(flambda_type -> t)  (* CR mshinwell: "of_type"? *)
    -> t
    -> typing_env
    -> head Or_unknown_or_bottom.t

  val expand_head'
     : force_to_kind:(flambda_type -> t)  (* CR mshinwell: "of_type"? *)
    -> t
    -> typing_env
    -> t

  module Make_meet_or_join (_ : Lattice_ops_intf.S
    with type meet_env := meet_env
    with type meet_or_join_env := meet_or_join_env
    with type typing_env := typing_env
    with type typing_env_extension := typing_env_extension)
  : sig
    val meet_or_join
       : ?bound_name:Name.t
      -> force_to_kind:(flambda_type -> t)  (* CR mshinwell: "of_type"? *)
      -> to_type:(t -> flambda_type)
      -> meet_or_join_env
      -> flambda_type
      -> flambda_type
      -> t
      -> t
      -> flambda_type * typing_env_extension
  end
end
