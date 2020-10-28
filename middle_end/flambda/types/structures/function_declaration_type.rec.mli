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

module Inlinable : sig
  type t

  val create
     : code_id:Code_id.t
    -> dbg:Debuginfo.t
    -> coercion:Coercion.t
    -> is_tupled:bool
    -> t

  val code_id : t -> Code_id.t
  val dbg : t -> Debuginfo.t
  val coercion : t -> Coercion.t
  val is_tupled : t -> bool
end

module Non_inlinable : sig
  type t

  val create
     : code_id:Code_id.t
    -> is_tupled:bool
    -> t

  val code_id : t -> Code_id.t
  val is_tupled : t -> bool
end

type t0 =
  | Inlinable of Inlinable.t
  | Non_inlinable of Non_inlinable.t

type t = t0 Or_unknown_or_bottom.t

(* CR mshinwell: Add [create] and make [private]. *)

include Type_structure_intf.S
  with type t := t
  with type flambda_type := Type_grammar.t
  with type typing_env := Typing_env.t
  with type meet_env := Meet_env.t
  with type meet_or_join_env := Meet_or_join_env.t
  with type typing_env_extension := Typing_env_extension.t

val apply_coercion : t -> Coercion.t -> t Or_bottom.t
