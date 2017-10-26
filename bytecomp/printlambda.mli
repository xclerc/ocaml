(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

open Lambda

open Format

val structured_constant: formatter -> structured_constant -> unit
val struct_const: formatter -> structured_constant -> unit
val lambda: formatter -> lambda -> unit
val program: formatter -> program -> unit
val primitive: formatter -> primitive -> unit
val name_of_primitive : primitive -> string
val array_kind : array_kind -> string
val record_rep : Format.formatter -> Types.record_representation -> unit
val value_kind : value_kind -> string
val meth_kind : formatter -> meth_kind -> unit
val function_attribute : formatter -> function_attribute -> unit
val apply_tailcall_attribute : formatter -> bool -> unit
val apply_inlined_attribute : formatter -> inline_attribute -> unit
val apply_specialised_attribute : formatter -> specialise_attribute -> unit
