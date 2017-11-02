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

(** A "name" in Flambda identifies:
    1. a variable;
    2. a constant address, given by a symbol;
    3. a constant value, which can be held in one of the target machine's
       registers (of the appropriate kind).

    This conflation of related concepts reduces the complexity of Flambda
    terms by eliminating excess [Let]-bindings.  It also helps reduce the
    number of different functions dealing with the related concepts.
*)

module Const : sig
  (** Simple constants which can be held entirely in registers. *)
  type t =
    | Untagged_immediate of Immediate.t
    | Tagged_immediate of Immediate.t
    | Naked_float of float
    | Naked_int32 of Int32.t
    | Naked_int64 of Int64.t
    | Naked_nativeint of Targetint.t

  include Identifiable.S with type t := t
end

type t = private
  | Var of Variable.t
  | Symbol of Symbol.t
  | Const of Const.t

val var : Variable.t -> t
val symbol : Symbol.t -> t
val const : Const.t -> t

val map_var : t -> f:(Variable.t -> Variable.t) -> t

include Identifiable.S with type t := t
