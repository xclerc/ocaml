
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

type t =
  | Pbytes_to_string
  | Pbytes_of_string
  | Pignore
  | Ploc of loc_kind
  | Pmakeblock of int * mutable_flag * block_shape
  | Pfield of int
  | Pfield_computed
  | Psetfield of int * immediate_or_pointer * initialization_or_assignment
  | Psetfield_computed of immediate_or_pointer * initialization_or_assignment
  | Pfloatfield of int
  | Psetfloatfield of int * initialization_or_assignment
  | Pduprecord of Types.record_representation * int
  | Plazyforce
  | Pccall of Primitive.description
  | Pccall_unboxed of Primitive.description
  | Praise of raise_kind
  | Psequand | Psequor | Pnot
  | Pnegint | Paddint | Psubint | Pmulint
  | Pdivint of is_safe | Pmodint of is_safe
  | Pandint | Porint | Pxorint
  | Plslint | Plsrint | Pasrint
  | Pintcomp of comparison
  | Poffsetint of int
  | Poffsetref of int
  | Pintoffloat of boxed | Pfloatofint of boxed
  | Pnegfloat of boxed | Pabsfloat of boxed
  | Paddfloat of boxed | Psubfloat of boxed | Pmulfloat of boxed
  | Pdivfloat of boxed
  | Pfloatcomp of comparison * boxed
  | Pstringlength | Pstringrefu  | Pstringrefs
  | Pbyteslength | Pbytesrefu | Pbytessetu | Pbytesrefs | Pbytessets
  | Pmakearray of array_kind * mutable_flag
  | Pduparray of array_kind * mutable_flag
  | Parraylength of array_kind
  | Parrayrefu of array_kind
  | Parraysetu of array_kind
  | Parrayrefs of array_kind
  | Parraysets of array_kind
  | Pisint
  | Pgettag
  | Pisout
  | Pbittest
  | Pbigarrayref of bool * int * bigarray_kind * bigarray_layout * boxed
  | Pbigarrayset of bool * int * bigarray_kind * bigarray_layout * boxed
  | Pbigarraydim of int
  | Pstring_load_16 of bool
  | Pstring_load_32 of bool
  | Pstring_load_64 of bool
  | Pstring_set_16 of bool
  | Pstring_set_32 of bool
  | Pstring_set_64 of bool
  | Pbigstring_load_16 of bool
  | Pbigstring_load_32 of bool
  | Pbigstring_load_64 of bool
  | Pbigstring_set_16 of bool
  | Pbigstring_set_32 of bool
  | Pbigstring_set_64 of bool
  | Pctconst of compile_time_constant
  | Pbswap16
  | Pbbswap of boxed_integer
  | Pint_as_pointer
  | Popaque
  | Punbox_float
  | Pbox_float
  | Punbox_int32
  | Pbox_int32
  | Punbox_int64
  | Pbox_int64
  | Punbox_nativeint
  | Pbox_nativeint
  | Puntag_immediate
  | Ptag_immediate
