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

    The semantics of these primitives follows this rule: no (un)tagging or
    (un)boxing is performed by the primitive either when accepting an input
    or producing an output.  These operations must be performed by the caller
    if required.
*)

[@@@ocaml.warning "+a-4-30-40-41-42"]

(* CR mshinwell: We need to be more precise about which ones are the
   unboxed/untagged ones *)

type array_kind =
  | Dynamic_must_scan_or_naked_float
  | Must_scan
  | Can_scan
  | Naked_float

type field_kind = Not_a_float | Float

type string_or_bytes = String | Bytes

type mutable_or_immutable = Immutable | Mutable

type initialization_or_assignment = Initialization | Assignment

type is_safe = Safe | Unsafe

type comparison =
  | Eq | Neq | Lt | Gt | Le | Ge

type bigarray_kind =
  | Unknown
  | Float32 | Float64
  | Sint8 | Uint8
  | Sint16 | Uint16
  | Int32 | Int64
  | Caml_int | Native_int
  | Complex32 | Complex64

type bigarray_layout = Unknown | C | Fortran

type raise_kind = Regular | Reraise | Notrace

(** Primitives taking exactly one argument. *)
type unary_primitive =
  | Field of int * field_kind
  | Dup_array of array_kind * mutable_or_immutable
  | Dup_record of Types.record_representation * int
  | Lazy_force
  | Is_int
  | Get_tag
  | String_length of string_or_bytes
  | Bswap16
  | Bswap of Flambda_kind.Of_naked_number.t
  | Int_as_pointer
  | Opaque
  | Raise of raise_kind
  | Not of Flambda_kind.Of_naked_number.t
  | Neg_int of Flambda_kind.Of_naked_number.t
  | Abs_float
  | Neg_float
  | Int_of_float
  | Float_of_int
  | Array_length of array_kind
  | Bigarray_dimension of int
  | Unbox_or_untag_number of K.Of_naked_number.t
  | Box_or_tag_number of K.Of_naked_number.t

(** Untagged integer arithmetic operations. *)
type int_arith_op =
  | Add
  | Sub
  | Mul
  | Div of is_safe
  | Mod of is_safe
  | And
  | Or
  | Xor

(** Untagged integer shift operations. *)
type int_shift_op =
  | Lsl
  | Lsr
  | Asr

(** Naked float arithmetic operations. *)
type float_arith_op =
  | Add
  | Sub
  | Mul
  | Div

type setfield_kind =
  | Immediate
  | Pointer
  | Float

(** Primitives taking exactly two arguments. *)
type binary_primitive =
  | Set_field of int * setfield_kind * initialization_or_assignment
  | Field_computed
  | Int_arith of Flambda_kind.Of_naked_number.t * int_arith_op
  | Int_shift of Flambda_kind.Of_naked_number.t * int_shift_op
  | Int_comp of comparison
  | Float_arith of float_arith_op
  | Float_comp of comparison
  | Array_ref of array_kind * is_safe
  | Bigarray_ref of bool * int * bigarray_kind * bigarray_layout
  | String_ref of string_or_bytes * is_safe
  | String_load of string_accessor_width * is_safe
  | Bigstring_load of string_accessor_width * is_safe

type string_accessor_width =
  | Sixteen
  | Thirty_two
  | Sixty_four

(** Primitives taking exactly three arguments. *)
type ternary_primitive =
  | Set_field_computed of Flambda_kind.scanning * initialization_or_assignment
  | Bytes_set of is_safe
  | Bigarray_set of bool * int * bigarray_kind * bigarray_layout
  | String_set of string_accessor_width * is_safe
  | Bigstring_set of string_accessor_width * is_safe
  | Array_set of array_kind * is_safe

(** Primitives taking zero or more arguments. *)
type variadic_primitive =
  | Make_block of int * mutable_or_immutable * Flambda_arity.t
  | Make_array of array_kind * mutable_or_immutable
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
