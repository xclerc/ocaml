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

[@@@ocaml.warning "+a-4-30-40-41-42"]

module K = Flambda_kind
module L = Lambda
module PL = Printlambda

type result_kind =
  | Singleton of K.t
  | Unit
  | Never_returns

type unary_primitive =
  | Field of int
  | Floatfield of int
  | Duparray of L.array_kind * Flambda.mutable_or_immutable
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
  | Raise of L.raise_kind
  | Not of K.Of_naked_number.t
  | Negint of K.Of_naked_number.t
  | Intoffloat
  | Floatofint
  | Negfloat
  | Arraylength of L.array_kind
  | Bigarrayref of bool * int * L.bigarray_kind * L.bigarray_layout
  | Bigarraydim of int
  | Unbox_number of K.Of_naked_number.t
  | Box_number of K.Of_naked_number.t
  | Untag_immediate
  | Tag_immediate

let print_unary_primitive p =
  let fprintf = Format.fprintf in
  match p with
  | Pfield n -> fprintf ppf "field %i" n
  | Pfloatfield n -> fprintf ppf "floatfield %i" n
  | Pduparray (k, Mutable) -> fprintf ppf "duparray[%s]" (array_kind k)
  | Pduparray (k, Immutable) -> fprintf ppf "duparray_imm[%s]" (array_kind k)
  | Pduprecord (rep, size) ->
    fprintf ppf "duprecord %a %i" PL.record_rep rep size
  | Plazyforce -> fprintf ppf "force"
  | Pisint -> fprintf ppf "isint"
  | Pgettag -> fprintf ppf "gettag"
  | Pisout -> fprintf ppf "isout"
  | Pbittest -> fprintf ppf "testbit"
  | Poffsetint n -> fprintf ppf "%i+" n
  | Poffsetref n -> fprintf ppf "+:=%i"n
  | Pbytes_to_string -> fprintf ppf "bytes_to_string"
  | Pbytes_of_string -> fprintf ppf "bytes_of_string"
  | Pstringlength -> fprintf ppf "string.length"
  | Pbyteslength -> fprintf ppf "bytes.length"
  | Pbswap16 -> fprintf ppf "bswap16"
  | Pbswap kind  -> "bswap_%a" ppf K.Of_naked_number.print kind
  | Pint_as_pointer -> fprintf ppf "int_as_pointer"
  | Popaque -> fprintf ppf "opaque"
  | Praise k -> fprintf ppf "%s" (Lraise_kind k)
  | Pnot -> fprintf ppf "not"
  | Pnegint -> fprintf ppf "~"
  | Pintoffloat -> fprintf ppf "int_of_float"
  | Pfloatofint -> fprintf ppf "float_of_int"
  | Pnegfloat -> fprintf ppf "~."
  | Parraylength k -> fprintf ppf "array.length[%s]" (array_kind k)
  | Pbigarrayref (unsafe, _n, kind, layout, boxed) ->
    PL.print_bigarray "get" unsafe PL.kind
      ppf PL.layout boxed
  | Pbigarraydim n -> fprintf ppf "Bigarray.dim_%i" n
  | Punbox_number kind ->
    fprintf ppf "unbox_%a" K.Of_naked_number.print_lowercase kind
  | Pbox_number kind ->
    fprintf ppf "box_%a" K.Of_naked_number.print_lowercase kind
  | Puntag_immediate -> fprintf ppf "untag"
  | Ptag_immediate -> fprintf ppf "tag"

let arg_kind_of_unary_primitive p =
  match p with
  | Field _ ->
  | Floatfield _ ->
  | Duparray _ ->
  | Duprecord _ ->
  | Lazyforce ->
  | Isint ->
  | Gettag ->
  | Isout
  | Bittest
  | Offsetint _ ->
  | Offsetref _ ->
  | Bytes_to_string
  | Bytes_of_string ->
  | Stringlength
  | Byteslength ->
  | Bswap16 ->
  | Not kind
  | Negint kind
  | Bswap kind ->
  | Int_as_pointer ->
  | Opaque ->
  | Raise _ ->
  | Intoffloat ->
  | Floatofint ->
  | Negfloat ->
  | Arraylength _ ->
  | Bigarrayref _ ->
  | Bigarraydim _ ->
  | Unbox_number kind ->
  | Box_number _ ->
  | Untag_immediate ->
  | Tag_immediate ->

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
  | Unbox_number kind -> Singleton (K.Of_naked_number.to_kind kind)
  | Box_number _ -> Singleton (K.value Must_scan)
  | Untag_immediate -> Singleton (K.naked_immediate ())
  | Tag_immediate -> Singleton (K.value Can_scan)

type binary_primitive =
  | Setfield of int * L.immediate_or_pointer
      * L.initialization_or_assignment
  | Setfloatfield of int * L.initialization_or_assignment
  | Field_computed
  | Addint of K.Of_naked_number.t
  | Subint of K.Of_naked_number.t
  | Mulint of K.Of_naked_number.t
  | Divint of L.is_safe * K.Of_naked_number.t
  | Modint of L.is_safe * K.Of_naked_number.t
  | Andint of K.Of_naked_number.t
  | Orint of K.Of_naked_number.t
  | Xorint of K.Of_naked_number.t
  | Lslint of K.Of_naked_number.t
  | Lsrint of K.Of_naked_number.t
  | Asrint of K.Of_naked_number.t
  | Intcomp of L.comparison
  | Absfloat
  | Addfloat
  | Subfloat
  | Mulfloat
  | Divfloat
  | Floatcomp of L.comparison
  | Arrayrefu of L.array_kind
  | Arrayrefs of L.array_kind
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
  let fprintf = Format.fprintf in
  match p with
  | Psetfield (n, ptr, init) ->
    let instr =
      match ptr with
      | Pointer -> "ptr"
      | Immediate -> "imm"
    in
    let init =
      match init with
      | Heap_initialization -> "(heap-init)"
      | Root_initialization -> "(root-init)"
      | Assignment -> ""
    in
    fprintf ppf "setfield_%s%s %i" instr init n
  | Psetfloatfield (n, init) ->
    let init =
      match init with
      | Heap_initialization -> "(heap-init)"
      | Root_initialization -> "(root-init)"
      | Assignment -> ""
    in
    fprintf ppf "setfloatfield%s %i" init n
  | Pfield_computed -> fprintf ppf "field_computed"
  | Paddint -> fprintf ppf "+"
  | Psubint -> fprintf ppf "-"
  | Pmulint -> fprintf ppf "*"
  | Pdivint Safe -> fprintf ppf "/"
  | Pdivint Unsafe -> fprintf ppf "/u"
  | Pmodint Safe -> fprintf ppf "mod"
  | Pmodint Unsafe -> fprintf ppf "mod_unsafe"
  | Pandint -> fprintf ppf "and"
  | Porint -> fprintf ppf "or"
  | Pxorint -> fprintf ppf "xor"
  | Plslint -> fprintf ppf "lsl"
  | Plsrint -> fprintf ppf "lsr"
  | Pasrint -> fprintf ppf "asr"
  | Pintcomp Ceq -> fprintf ppf "=="
  | Pintcomp Cneq -> fprintf ppf "!="
  | Pintcomp Clt -> fprintf ppf "<"
  | Pintcomp Cle -> fprintf ppf "<="
  | Pintcomp Cgt -> fprintf ppf ">"
  | Pintcomp Cge -> fprintf ppf ">="
  | Pabsfloat -> fprintf ppf "abs.%a"
  | Paddfloat -> fprintf ppf "+.%a"
  | Psubfloat -> fprintf ppf "-.%a"
  | Pmulfloat -> fprintf ppf "*.%a"
  | Pdivfloat -> fprintf ppf "/.%a"
  | Pfloatcomp Ceq -> fprintf ppf "==.%a"
  | Pfloatcomp Cneq -> fprintf ppf "!=.%a"
  | Pfloatcomp Clt -> fprintf ppf "<.%a"
  | Pfloatcomp Cle -> fprintf ppf "<=.%a"
  | Pfloatcomp Cgt -> fprintf ppf ">.%a"
  | Pfloatcomp Cge -> fprintf ppf ">=.%a"
  | Parrayrefu k -> fprintf ppf "array.unsafe_get[%s]" (array_kind k)
  | Parrayrefs k -> fprintf ppf "array.get[%s]" (array_kind k)
  | Pstringrefu -> fprintf ppf "string.unsafe_get"
  | Pstringrefs -> fprintf ppf "string.get"
  | Pbytesrefu -> fprintf ppf "bytes.unsafe_get"
  | Pbytesrefs -> fprintf ppf "bytes.get"
  | Pstring_load_16 unsafe ->
    if unsafe then fprintf ppf "string.unsafe_get16"
    else fprintf ppf "string.get16"
  | Pstring_load_32 unsafe ->
    if unsafe then fprintf ppf "string.unsafe_get32"
    else fprintf ppf "string.get32"
  | Pstring_load_64 unsafe ->
    if unsafe then fprintf ppf "string.unsafe_get64"
    else fprintf ppf "string.get64"
  | Pbigstring_load_16 unsafe ->
    if unsafe then fprintf ppf "bigarray.array1.unsafe_get16"
    else fprintf ppf "bigarray.array1.get16"
  | Pbigstring_load_32 unsafe ->
    if unsafe then fprintf ppf "bigarray.array1.unsafe_get32"
    else fprintf ppf "bigarray.array1.get32"
  | Pbigstring_load_64 unsafe ->
    if unsafe then fprintf ppf "bigarray.array1.unsafe_get64"
    else fprintf ppf "bigarray.array1.get64"

let args_kind_of_binary_primitive p =
  match p with
  | Setfield _
  | Setfloatfield _ ->
  | Field_computed _ ->
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
  | Asrint kind ->
  | Intcomp | Floatcomp ->
  | Absfloat
  | Addfloat
  | Subfloat
  | Mulfloat
  | Divfloat ->
  | Arrayrefu (Pgenarray | Paddrarray)
  | Arrayrefs (Pgenarray | Paddrarray) ->
  | Arrayrefu Pintarray
  | Arrayrefs Pintarray ->
  | Arrayrefu Pfloatarray
  | Arrayrefs Pfloatarray ->
  | Stringrefu
  | Stringrefs
  | Bytesrefu
  | Bytesrefs ->
  | String_load_16 _
  | String_load_32 _
  | String_load_64 _
  | Bigstring_load_16 _
  | Bigstring_load_32 _
  | Bigstring_load_64 _ ->

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
  | Bigstring_load_16 _ -> Singleton (K.value Can_scan)
  | Bigstring_load_32 _ -> 
  | Bigstring_load_64 _ -> ???

type ternary_primitive =
  | Setfield_computed of Lambda.immediate_or_pointer
      * Lambda.initialization_or_assignment
  | Bytesset of Lambda.is_safe
  | Bigarrayset of bool * int * L.bigarray_kind * L.bigarray_layout
  | String_set_16 of is_safe
  | String_set_32 of is_safe
  | String_set_64 of is_safe
  | Bigstring_set_16 of is_safe
  | Bigstring_set_32 of is_safe
  | Bigstring_set_64 of is_safe
  | Arrayset of Lambda.array_kind * Lambda.is_safe

let print_ternary_primitive ppf p =
  | Psetfield_computed (ptr, init) ->
    let instr =
      match ptr with
      | Pointer -> "ptr"
      | Immediate -> "imm"
    in
    let init =
      match init with
      | Heap_initialization -> "(heap-init)"
      | Root_initialization -> "(root-init)"
      | Assignment -> ""
    in
    fprintf ppf "setfield_%s%s_computed" instr init
  | Pbytessetu -> fprintf ppf "bytes.unsafe_set"
  | Pbytessets -> fprintf ppf "bytes.set"
  | Parraysetu k -> fprintf ppf "array.unsafe_set[%s]" (PL.array_kind k)
  | Parraysets k -> fprintf ppf "array.set[%s]" (PL.array_kind k)
  | Pbigarrayset (unsafe, _n, kind, layout, boxed) ->
    print_bigarray "set" unsafe PL.kind ppf PL.layout boxed
  | Pstring_set_16 unsafe ->
    if unsafe then fprintf ppf "string.unsafe_set16"
    else fprintf ppf "string.set16"
  | Pstring_set_32 unsafe ->
    if unsafe then fprintf ppf "string.unsafe_set32"
    else fprintf ppf "string.set32"
  | Pstring_set_64 unsafe ->
    if unsafe then fprintf ppf "string.unsafe_set64"
    else fprintf ppf "string.set64"
  | Pbigstring_set_16 unsafe ->
    if unsafe then fprintf ppf "bigarray.array1.unsafe_set16"
    else fprintf ppf "bigarray.array1.set16"
  | Pbigstring_set_32 unsafe ->
    if unsafe then fprintf ppf "bigarray.array1.unsafe_set32"
    else fprintf ppf "bigarray.array1.set32"
  | Pbigstring_set_64 unsafe ->
    if unsafe then fprintf ppf "bigarray.array1.unsafe_set64"
    else fprintf ppf "bigarray.array1.set64"

let args_kind_of_ternary_primitive p =
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
  | Arraysets _ ->

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
  | Makeblock of int * Flambda.mutable_or_immutable * L.block_shape
  | Makearray of L.array_kind * Flambda.mutable_or_immutable
  | Ccall of Primitive.description
  | Ccall_unboxed of Primitive.description

let print_variadic_primitive ppf p =
  let fprintf = Format.fprintf in
  match p with
  | Pmakeblock (tag, Immutable, shape) ->
    fprintf ppf "makeblock %a%a" Tag.print tag PL.block_shape shape
  | Pmakeblock (tag, Mutable, shape) ->
    fprintf ppf "makemutable %a%a" Tag.print tag PL.block_shape shape
  | Pccall p -> fprintf ppf "%s" p.prim_name
  | Pccall_unboxed p -> fprintf ppf "%s(unboxed)" p.prim_name
  | Pmakearray (k, Mutable) ->
    fprintf ppf "makearray[%s]" (PL.array_kind k)
  | Pmakearray (k, Immutable) ->
    fprintf ppf "makearray_imm[%s]" (PL.array_kind k)

let args_kind_of_variadic_primitive p =
  match p with
  | Makeblock _
  | Makearray _
  | Ccall _
  | Ccall_unboxed _ ->

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

let arg_kinds (t : t) : arg_kinds =
  match t with
  | Unary (prim, _) ->
    let kind = arg_kind_of_unary_primitive prim in
    Unary kind
  | Binary (prim, _) ->
    let kind0, kind1 = args_kind_of_binary_primitive prim in
    Binary (kind0, kind1)
  | Ternary (prim, _) ->
    let kind0, kind1, kind2 = args_kind_of_ternary_primitive prim in
    Ternary (kind0, kind1, kind3)
  | Variadic (prim, _) ->
    let kind = args_kind_of_variadic_primitive prim in
    Variadic kind

let result_kind (t : t) =
  match t with
  | Unary (prim, _) -> result_kind_of_unary_primitive prim
  | Binary (prim, _, _) -> result_kind_of_binary_primitive prim
  | Ternary (prim, _, _, _) -> result_kind_of_ternary_primitive prim
  | Variadic (prim, _) -> result_kind_of_variadic_primitive prim
