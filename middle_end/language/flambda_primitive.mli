(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*            Mark Shinwell and Xavier Clerc, Jane Street Europe          *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   Copyright 2017 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(** Primitives used in Flambda.  The list excludes primitives forbidden in
    Flambda; we are thus able to avoid "fatal error" cases in pattern matches.
    We obtain greater static safety over [Lambda] by explicitly annotating
    the correct arity of arguments.

    All of the numerical primitives in Flambda, including [Bigarray]
    accessors, work on unboxed or untagged representations.
*)

[@@@ocaml.warning "+a-4-30-40-41-42"]

(* CR mshinwell: We need to be more precise about which ones are the
   unboxed/untagged ones *)

(** Primitives taking exactly one argument. *)
type unary_primitive =
  | Field of int
  | Floatfield of int
  | Duparray of Lambda.array_kind * Asttypes.mutable_flag
  | Duprecord of Types.record_representation * int
  | Lazyforce
  | Isint
  | Gettag
  | Isout
  | Bittest
  | Offsetint of int
  | Offsetref of int
  | Bytes_to_string
  | Bytes_of_string
  | Stringlength
  | Byteslength
  | Bswap16
  | Bswap of Flambda_kind.Of_naked_number.t
  | Int_as_pointer
  | Opaque
  | Raise of Lambda.raise_kind
  | Not of Flambda_kind.Of_naked_number.t
  | Negint of Flambda_kind.Of_naked_number.t
  | Intoffloat
  | Floatofint
  | Negfloat
  | Arraylength of Lambda.array_kind
  | Bigarrayref of bool * int * Lambda.bigarray_kind * Lambda.bigarray_layout
  | Bigarrayset of bool * int * Lambda.bigarray_kind * Lambda.bigarray_layout
  | Bigarraydim of int
  | Unbox_float
  | Box_float
  | Unbox_int32
  | Box_int32
  | Unbox_int64
  | Box_int64
  | Unbox_nativeint
  | Box_nativeint
  | Untag_immediate
  | Tag_immediate

(** Primitives taking exactly two arguments. *)
type binary_primitive =
  | Setfield of int * Lambda.immediate_or_pointer
      * Lambda.initialization_or_assignment
  | Setfloatfield of int * Lambda.initialization_or_assignment
  | Field_computed
  | Addint of Flambda_kind.Of_naked_number.t
  | Subint of Flambda_kind.Of_naked_number.t
  | Mulint of Flambda_kind.Of_naked_number.t
  | Divint of Lambda.is_safe * Flambda_kind.Of_naked_number.t
  | Modint of Lambda.is_safe * Flambda_kind.Of_naked_number.t
  | Andint of Flambda_kind.Of_naked_number.t
  | Orint of Flambda_kind.Of_naked_number.t
  | Xorint of Flambda_kind.Of_naked_number.t
  | Lslint of Flambda_kind.Of_naked_number.t
  | Lsrint of Flambda_kind.Of_naked_number.t
  | Asrint of Flambda_kind.Of_naked_number.t
  | Intcomp of Lambda.comparison
  | Absfloat
  | Addfloat
  | Subfloat
  | Mulfloat
  | Divfloat
  | Floatcomp of Lambda.comparison
  | Arrayrefu of Lambda.array_kind
  | Arrayrefs of Lambda.array_kind
  | Stringrefu
  | Stringrefs
  | Bytesrefu
  | Bytesrefs
  | String_load_16 of bool
  | String_load_32 of bool
  | String_load_64 of bool
  | Bigstring_load_16 of bool
  | Bigstring_load_32 of bool
  | Bigstring_load_64 of bool

(** Primitives taking exactly three arguments. *)
type ternary_primitive =
  | Setfield_computed of Lambda.immediate_or_pointer
      * Lambda.initialization_or_assignment
  | Bytessetu
  | Bytessets
  | String_set_16 of bool
  | String_set_32 of bool
  | String_set_64 of bool
  | Bigstring_set_16 of bool
  | Bigstring_set_32 of bool
  | Bigstring_set_64 of bool
  | Arraysetu of Lambda.array_kind
  | Arraysets of Lambda.array_kind

(** Primitives taking zero or more arguments. *)
type variadic_primitive =
  | Makeblock of int * Asttypes.mutable_flag * Lambda.block_shape
  | Makearray of Lambda.array_kind * Asttypes.mutable_flag
  | Ccall of Primitive.description
  (* CR mshinwell: Should [Ccall_unboxed] take an [Flambda_arity.t]?  It seems
     like it should to avoid risking unnecessary boxings. *)
  | Ccall_unboxed of Primitive.description

(** The application of a primitive to its arguments. *)
type t =
  | Unary of unary_primitive * Variable.t
  | Binary of binary_primitive * Variable.t * Variable.t
  | Ternary of ternary_primitive * Variable.t * Variable.t * Variable.t
  | Variadic of variadic_primitive * (Variable.t list)

(** Print a primitive and its arguments to a formatter. *)
val print : Format.formatter -> t -> unit

(** A description of the kinds of values which a primitive expects as
    its arguments. *)
type arg_kinds =
  | Unary of Flambda_kind.t
  | Binary of Flambda_kind.t * Flambda_kind.t
  | Ternary of Flambda_kind.t * Flambda_kind.t * Flambda_kind.t
  | Variadic of Flambda_kind.t

(** Describe the argument kinds required for the given primitive. *)
val arg_kinds : t -> arg_kinds

(** A description of the kinds of values (or in the case of [Unit], the
    actual value) which a primitive expects as its arguments. *)
type result_kind =
  | Singleton of Flambda_kind.t
  (** The primitive returns a single value of the given kind. *)
  | Unit
  (** The primitive returns the constant unit value. *)
  | Never_returns
  (** The primitive does not terminate normally (e.g. by raising an
      exception). *)

(** Describe the kind of the result of the given primitive. *)
val result_kind : t -> result_kind
