
(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2017 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

type naked_int_kind =
  | Untagged_immediate
  | Naked_int32
  | Naked_int64
  | Naked_nativeint

type t =
  | Bytes_to_string
  | Bytes_of_string
  | Ignore
  | Makeblock of int * mutable_flag * block_shape
  | Field of int
  | Field_computed
  | Setfield of int * immediate_or_pointer * initialization_or_assignment
  | Setfield_computed of immediate_or_pointer * initialization_or_assignment
  | Floatfield of int
  | Setfloatfield of int * initialization_or_assignment
  | Duprecord of Types.record_representation * int
  | Lazyforce
  | Ccall of Primitive.description
  | Ccall_unboxed of Primitive.description
  | Raise of raise_kind
  | Not of naked_int_kind
  | Negint of naked_int_kind
  | Addint of naked_int_kind
  | Subint of naked_int_kind
  | Mulint of naked_int_kind
  | Divint of is_safe * naked_int_kind
  | Modint of is_safe * naked_int_kind
  | Andint of naked_int_kind
  | Orint of naked_int_kind
  | Xorint of naked_int_kind
  | Lslint of naked_int_kind
  | Lsrint of naked_int_kind
  | Asrint of naked_int_kind
  | Intcomp of comparison
  | Offsetint of int
  | Offsetref of int
  | Intoffloat | Pfloatofint
  | Negfloat | Pabsfloat
  | Addfloat | Psubfloat | Pmulfloat
  | Divfloat
  | Floatcomp of comparison
  | Stringlength | Pstringrefu  | Pstringrefs
  | Byteslength | Pbytesrefu | Pbytessetu | Pbytesrefs | Pbytessets
  | Makearray of array_kind * mutable_flag
  | Duparray of array_kind * mutable_flag
  | Arraylength of array_kind
  | Arrayrefu of array_kind
  | Arraysetu of array_kind
  | Arrayrefs of array_kind
  | Arraysets of array_kind
  | Isint
  | Gettag
  | Isout
  | Bittest
  | Bigarrayref of bool * int * bigarray_kind * bigarray_layout * boxed
  | Bigarrayset of bool * int * bigarray_kind * bigarray_layout * boxed
  | Bigarraydim of int
  | String_load_16 of bool
  | String_load_32 of bool
  | String_load_64 of bool
  | String_set_16 of bool
  | String_set_32 of bool
  | String_set_64 of bool
  | Bigstring_load_16 of bool
  | Bigstring_load_32 of bool
  | Bigstring_load_64 of bool
  | Bigstring_set_16 of bool
  | Bigstring_set_32 of bool
  | Bigstring_set_64 of bool
  | Ctconst of compile_time_constant
  | Bswap16
  | Bbswap of boxed_integer
  | Int_as_pointer
  | Opaque
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
