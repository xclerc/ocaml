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
   : alias_of:Continuation.t
  -> handler:Flambda.continuation_handler
  -> t

val alias_of : t -> Continuation.t

val params : t -> Variable.t list
val recursive : t -> Asttypes.rec_flag
val handler : t -> Flambda.t
