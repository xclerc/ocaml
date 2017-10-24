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

[@@@ocaml.warning "+a-4-30-40-41-42"]

(** Environments used for invariant checks. *)

type continuation_kind = Normal | Exn_handler

type t

val create : unit -> t

val add_variable : t -> Variable.t -> Flambda_kind.t -> t

val add_variables : t -> (Variable.t * Flambda_kind.t) list -> t

val add_typed_parameters
   : (t
  -> Flambda0.Typed_parameter.t list
  -> t) Flambda_type.with_importer

val add_mutable_variable : t -> Mutable_variable.t -> Flambda_kind.t -> t

val add_symbol : t -> Symbol.t -> t

val add_continuation
   : t
  -> Continuation.t
  -> Flambda_arity.t
  -> continuation_kind
  -> t

val check_variable_is_bound : t -> Variable.t -> unit

val check_mutable_variable_is_bound : t -> Mutable_variable.t -> unit

val check_symbol_is_bound : t -> Symbol.t -> unit
