(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                    Mark Shinwell, Jane Street Europe                   *)
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

module K = Flambda_kind

type result_kind =
  | Singleton of K.t
  | Unit
  | Never_returns

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
  | Bswap of K.Of_naked_number.t
  | Int_as_pointer
  | Opaque
  | Raise of Lambda.raise_kind
  | Not of K.Of_naked_number.t
  | Negint of K.Of_naked_number.t
  | Intoffloat
  | Floatofint
  | Negfloat
  | Arraylength of Lambda.array_kind
  | Bigarrayref of bool * int * Lambda.bigarray_kind * Lambda.bigarray_layout
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

let print_unary_primitive p =
  match p with

let result_kind_of_unary_primitive p : result_kind =
  match p with
  | Field _ -> Singleton (K.value Must_scan)
  | Floatfield _ -> Singleton (K.naked_float ())
  | Duparray _ -> Singleton (K.value Must_scan)
  | Duprecord _ -> Singleton (K.value Must_scan)
  | Lazyforce -> Singleton (K.value Must_scan)
  | Isint -> Singleton (K.naked_immediate ())
  | Gettag -> Singleton (K.naked_immediate ())
  | Isout
  | Bittest
  | Offsetint _ -> ...
  | Offsetref _ -> ...
  | Bytes_to_string
  | Bytes_of_string -> Singleton (K.value Must_scan)
  | Stringlength
  | Byteslength -> Singleton (K.naked_immediate ())
  | Bswap16 -> ???
  | Not kind
  | Negint kind
  | Bswap kind -> Singleton (K.Of_naked_number.to_kind kind)
  | Int_as_pointer -> Singleton (K.naked_immediate ())  (* CR mshinwell: ok? *)
  | Opaque -> Singleton (K.value Must_scan)
  | Raise _ -> Never_returns
  | Intoffloat -> Singleton (K.naked_immediate ())
  | Floatofint -> Singleton (K.naked_float ())
  | Negfloat -> Singleton (K.naked_float ())
  | Arraylength _ -> Singleton (K.naked_immediate ())
  | Bigarrayref _ -> ???  (* the Flambda_kind needs to be in the arg. type *)
  | Bigarraydim _ -> Singleton (K.naked_immediate ())
  | Unbox_float -> Singleton (K.naked_float ())
  | Unbox_int32 -> Singleton (K.naked_int32 ())
  | Unbox_int64 -> Singleton (K.naked_int64 ())
  | Unbox_nativeint -> Singleton (K.naked_nativeint ())
  | Untag_immediate -> Singleton (K.naked_immediate ())
  | Box_float
  | Box_int32
  | Box_int64
  | Box_nativeint
  | Tag_immediate -> Singleton (K.value Must_scan)

type binary_primitive =
  | Setfield of int * Lambda.immediate_or_pointer
      * Lambda.initialization_or_assignment
  | Setfloatfield of int * Lambda.initialization_or_assignment
  | Field_computed
  | Addint of K.Of_naked_number.t
  | Subint of K.Of_naked_number.t
  | Mulint of K.Of_naked_number.t
  | Divint of Lambda.is_safe * K.Of_naked_number.t
  | Modint of Lambda.is_safe * K.Of_naked_number.t
  | Andint of K.Of_naked_number.t
  | Orint of K.Of_naked_number.t
  | Xorint of K.Of_naked_number.t
  | Lslint of K.Of_naked_number.t
  | Lsrint of K.Of_naked_number.t
  | Asrint of K.Of_naked_number.t
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

let print_binary_primitive ppf p =
  match p with

let result_kind_of_binary_primitive ppf p : result_kind =
  match p with
  | Setfield _
  | Setfloatfield _ -> Unit
  | Field_computed _ -> Singleton (K.value Must_scan)
  | Addint kind
  | Subint kind
  | Mulint kind
  | Divint (_, kind)
  | Modint (_, kind)
  | Andint kind
  | Orint kind
  | Xorint kind
  | Lslint kind
  | Lsrint kind
  | Asrint kind -> Singleton (K.Of_naked_number.to_kind kind)
  | Intcomp | Floatcomp -> Singleton (K.naked_immediate ())
  | Absfloat
  | Addfloat
  | Subfloat
  | Mulfloat
  | Divfloat -> Singleton (K.naked_float ())
  | Arrayrefu (Pgenarray | Paddrarray)
  | Arrayrefs (Pgenarray | Paddrarray) -> Singleton (K.value Must_scan)
  | Arrayrefu Pintarray
  | Arrayrefs Pintarray -> Singleton (K.value Can_scan)
  | Arrayrefu Pfloatarray
  | Arrayrefs Pfloatarray -> Singleton (K.naked_float ())
  | Stringrefu
  | Stringrefs
  | Bytesrefu
  | Bytesrefs -> Singleton (K.value Can_scan)
  | String_load_16 _
  | String_load_32 _
  | String_load_64 _
  | Bigstring_load_16 _
  | Bigstring_load_32 _
  | Bigstring_load_64 _ -> ???

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
  | Bigarrayset of bool * int * Lambda.bigarray_kind * Lambda.bigarray_layout
  | Arraysetu of Lambda.array_kind
  | Arraysets of Lambda.array_kind

let print_ternary_primitive ppf p =
  match p with

let result_kind_of_ternary_primitive p : result_kind =
  match p with
  | Setfield_computed _
  | Bytessetu
  | Bytessets
  | String_set_16 _
  | String_set_32 _
  | String_set_64 _
  | Bigstring_set_16 _
  | Bigstring_set_32 _
  | Bigstring_set_64 _
  | Bigarrayset _
  | Arraysetu _
  | Arraysets _ -> Unit

type variadic_primitive =
  | Makeblock of int * Asttypes.mutable_flag * Lambda.block_shape
  | Makearray of Lambda.array_kind * Asttypes.mutable_flag
  | Ccall of Primitive.description
  | Ccall_unboxed of Primitive.description

let print_variadic_primitive ppf p =
  match p with

let result_kind_of_variadic_primitive p : result_kind =
  match p with
  | Makeblock _
  | Makearray _
  | Ccall _
  | Ccall_unboxed _ -> K.value Must_scan

type t =
  | Unary of unary_primitive * Variable.t
  | Binary of binary_primitive * Variable.t * Variable.t
  | Ternary of ternary_primitive * Variable.t * Variable.t * Variable.t
  | Variadic of variadic_primitive * (Variable.t list)

let print ppf t =
  match t with
  | Unary (prim, v0) ->
    Format.fprintf ppf "@[(Prim %a %a)@]"
      print_unary_primitive prim
      Variable.print v0
  | Binary (prim, v0, v1) ->
    Format.fprintf ppf "@[(Prim %a %a %a)@]"
      print_unary_primitive prim
      Variable.print v0
      Variable.print v1
  | Ternary (prim, v0, v1, v2) ->
    Format.fprintf ppf "@[(Prim %a %a %a %a)@]"
      print_unary_primitive prim
      Variable.print v0
      Variable.print v1
      Variable.print v2
  | Variadic (prim, vs) ->
    Format.fprintf ppf "@[(Prim %a %a)@]"
      print_variadic_primitive prim
      (Format.pp_print_list ~pp_sep:pp_print_space Variable.print) vs

type arg_kinds =
  | Unary of K.t
  | Binary of K.t * K.t
  | Ternary of K.t * K.t * K.t
  | Variadic of K.t

let arg_kinds t =
  match t with

let result_kind t =
  match t with
  | Unary (prim, _) -> result_kind_of_unary_primitive prim
  | Binary (prim, _, _) -> result_kind_of_binary_primitive prim
  | Ternary (prim, _, _, _) -> result_kind_of_ternary_primitive prim
  | Variadic (prim, _) -> result_kind_of_variadic_primitive prim
