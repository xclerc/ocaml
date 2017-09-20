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
(*
[@@@ocaml.warning "+a-4-9-30-40-41-42"]

type flambda_kind =
  | Normal
  | Lifted

(** Checking of invariants on Flambda expressions.  Raises an exception if
    a check fails. *)
val check_exn
   : ?kind:flambda_kind
  -> ?cmxfile:bool
  -> Flambda_static.Program.t
  -> unit

*)
