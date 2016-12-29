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

(** Approximations of continuations.  Used during simplification. *)

type t

val create
   : name:Continuation.t
  -> handler:Flambda.continuation_handler
  -> num_params:int
  -> specialised_args:Flambda.specialised_args
  -> t

(* CR mshinwell: maybe "unknown" isn't a very good name *)
val create_unknown
   : name:Continuation.t
  -> num_params:int
  -> specialised_args:Flambda.specialised_args
  -> t

val name : t -> Continuation.t

val num_params : t -> int
val handler : t -> Flambda.continuation_handler option
val specialised_args : t -> Flambda.specialised_args

val print : Format.formatter -> t -> unit
