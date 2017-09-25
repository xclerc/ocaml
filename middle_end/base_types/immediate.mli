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

(** Immediate constants that can be held in registers. *)

type 'a or_wrong = private
  | Ok of 'a
  | Wrong

type t = private {
  value : Targetint.t;
  print_as_char : bool;
}

(** The comparison function for type [t] ignores [print_as_char]. *)
include Identifiable.S with type t := t

val join : t -> t -> t or_wrong

val join_set : Set.t -> Set.t -> Set.t

val bool_true : t
val bool_false : t
