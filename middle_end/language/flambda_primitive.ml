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

type effects = No_effects | Only_generative_effects | Arbitrary_effects

type coeffects = No_coeffects | Has_coeffects

type array_kind =
  | Dynamic_must_scan_or_naked_float
  | Must_scan
  | Can_scan
  | Naked_float

let print_array_kind ppf k =
  let fprintf = Format.fprintf in
  match k with
  | Dynamic_must_scan_or_naked_float -> fprintf ppf "dynamic"
  | Must_scan -> fprintf ppf "must_scan"
  | Can_scan -> fprintf ppf "can_scan"
  | Naked_float -> fprintf ppf "float"

type field_kind = Not_a_float | Float

type string_or_bytes = String | Bytes

type mutable_or_immutable = Immutable | Mutable

type init_or_assign = Initialization | Assignment

let print_init_or_assign ppf x =
  let fprintf = Format.fprintf in
  match x with
  | Initialization -> "init"
  | Assignment -> ""

type is_safe = Safe | Unsafe

let print_is_safe ppf s =
  let fprintf = Format.fprintf in
  match x with
  | Safe -> fprintf ppf "safe"
  | Unsafe -> fprintf ppf "unsafe"

type array_like_operation = Reading | Writing

let effects_of_is_safe operation is_safe =
  match is_safe with
  | Safe -> Arbitrary_effects
  | Unsafe ->
    match operation with
    | Reading -> No_effects
    | Writing -> Arbitrary_effects

let reading_from_an_array_like_thing is_safe =
  let effects = effects_of_is_safe Reading is_safe in
  effects, Has_coeffects

(* CR-someday mshinwell: Change this when [Obj.truncate] is removed (although
   beware, bigarrays will still be resizable). *)
let writing_to_an_array_like_thing is_safe =
  let effects = effects_of_is_safe Writing is_safe in
  (* Care: the bounds check may read a mutable place---namely the size of
     the block (for [Bytes_set] and [Array_set]) or the dimension of the
     bigarray.  As such these primitives have coeffects. *)
  effects, Has_coeffects

type comparison = Eq | Neq | Lt | Gt | Le | Ge

let print_comparison ppf c =
  let fprintf = Format.fprintf in
  match c with
  | Eq  -> fprintf ppf "=="
  | Neq -> fprintf ppf "!="
  | Lt  -> fprintf ppf "<"
  | Le  -> fprintf ppf "<="
  | Gt  -> fprintf ppf ">"
  | Ge  -> fprintf ppf ">="

type bigarray_kind =
  | Unknown
  | Float32 | Float64
  | Sint8 | Uint8
  | Sint16 | Uint16
  | Int32 | Int64
  | Caml_int | Native_int
  | Complex32 | Complex64

let print_bigarray_kind ppf k =
  let fprintf = Format.fprintf in
  match k with
  | Unknown -> fprintf ppf "unknown"
  | Float32 -> fprintf ppf "float32"
  | Float64 -> fprintf ppf "float64"
  | Sint8 -> fprintf ppf "sint8"
  | Uint8 -> fprintf ppf "uint8"
  | Sint16 -> fprintf ppf "sint16"
  | Uint16 -> fprintf ppf "uint16"
  | Int32 -> fprintf ppf "int32"
  | Int64 -> fprintf ppf "int64"
  | Caml_int -> fprintf ppf "caml_int"
  | Native_int -> fprintf ppf "native_int"
  | Complex32 -> fprintf ppf "complex32"
  | Complex64 -> fprintf ppf "complex64"

type bigarray_layout = Unknown | C | Fortran

let print_bigarray_layout ppf l =
  let fprintf = Format.fprintf in
  match l with
  | Unknown -> fprintf ppf "unknown"
  | C -> fprintf ppf "C"
  | Fortran -> fprintf ppf "fortran"

type raise_kind = Regular | Reraise | No_trace

let print_raise_kind ppf k =
  let fprintf = Format.fprintf in
  match k with
  | Regular -> fprintf ppf "regular"
  | Reraise -> fprintf ppf "reraise"
  | No_trace -> fprintf ppf "no_trace"

type setfield_kind =
  | Immediate
  | Pointer
  | Float

let print_setfield_kind ppf k =
  let fprintf = Format.fprintf in
  match k with
  | Immediate -> fprintf ppf "imm"
  | Pointer -> fprintf ppf "ptr"
  | Float -> fprintf ppf "float"

type string_accessor_width =
  | Eight
  | Sixteen
  | Thirty_two
  | Sixty_four

let print_string_accessor_width ppf w =
  let fprintf = Format.fprintf in
  match w with
  | Eight -> fprintf ppf "8"
  | Sixteen -> fprintf ppf "16"
  | Thirty_two -> fprintf ppf "32"
  | Sixty_four -> fprintf ppf "64"

type bigstring_accessor_width =
  | Sixteen
  | Thirty_two
  | Sixty_four

let print_bigstring_accessor_width ppf w =
  let fprintf = Format.fprintf in
  match w with
  | Sixteen -> fprintf ppf "16"
  | Thirty_two -> fprintf ppf "32"
  | Sixty_four -> fprintf ppf "64"

type num_dimensions = int

let print_num_dimesions ppf d =
  Format.fprintf ppf "%d" d

type boxed_integer = Pnativeint | Pint32 | Pint64 (* CR? remove the leading 'P' *)

let print_boxed_integer ppx b =
  let fprintf = Format.fprintf in
  match b with
  | Pnativeint -> fprintf ppf "nativeint"
  | Pint32 -> fprintf ppf "int32"
  | Pint64 -> fprintf ppf "int64"

type unary_int_arith_op = Neg

let print_unary_int_arith_op ppf o =
  let fprintf = Format.fprintf in
  match o with
  | Neg -> fprintf ppf "~"

type unary_float_arith_op = Abs | Neg

let print_unary_float_arith_op ppf o =
  let fprintf = Format.fprintf in
  match o with
  | Abs -> fprintf ppf "abs"
  | Neg -> fprintf ppf "~"

type result_kind =
  | Singleton of K.t
  | Unit
  | Never_returns

type unary_primitive =
  | Block_load of int * field_kind
  | Duplicate_array of array_kind * mutable_or_immutable
  | Duplicate_record of {
      repr : Types.record_representation;
      num_fields : int;
    }
  | Is_int
  | Get_tag
  | String_length of string_or_bytes
  | Swap_byte_endianness of K.Of_naked_number_not_float.t
  | Int_as_pointer
  | Opaque
  | Raise of raise_kind
  | Int_arith of K.Of_naked_number_not_float.t * unary_int_arith_op
  | Float_arith of unary_float_arity_op
  | Int_of_float
  | Float_of_int
  | Array_length of array_kind
  | Bigarray_length of { dimension : int; } (* CR? rename to [num_]dimensions? *)
  | Unbox_or_untag_number of K.Of_naked_number.t
  | Box_or_tag_number of K.Of_naked_number.t

let print_unary_primitive p =
  let fprintf = Format.fprintf in
  match p with
  | Block_load (i, _k) ->
    fprintf ppf "block_load %i" n
  | Duplicate_array (k, Mutable) ->
    fprintf ppf "duplicate_array[%a]" print_array_kind k
  | Duplicate_array (k, Immutable) ->
    fprintf ppf "duplicate_array_imm[%a]" print_array_kind k
  | Duplicate_record { repr; num_fields; } ->
    fprintf ppf "duplicate_record %a %i" PL.record_rep repr num_fields
  | Is_int -> fprintf ppf "is_int"
  | Get_tag -> fprintf ppf "get_tag"
  | String_length _ -> fprintf ppf "string_length"
  | Swap_byte_endianness _ -> fprintf ppf "swap_byte_endianness"
  | Int_as_pointer -> fprintf ppf "int_as_pointer"
  | Opaque -> fprintf ppf "opaque"
  | Praise k -> fprintf ppf "raise %a" print_raise_kind k
  | Int_arith (_k, o) -> print_unary_int_arith_op o
  | Float_arith o -> print_unary_float_arith_op o
  | Int_of_float -> fprintf ppf "int_of_float"
  | Float_of_int -> fprintf ppf "float_of_int"
  | Array_length _ -> fprintf ppf "array_length"
  | Bigarray_length { dimension; } ->
    fprintf ppf "bigarray_length %a" print_num_dimesions dimension
  | Unbox_or_untag_number k ->
    fprintf ppf "unbox_%a" K.Of_naked_number.print_lowercase k
  | Box_or_tag_number k ->
    fprintf ppf "box_%a" K.Of_naked_number.print_lowercase k

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

let effects_and_coeffects_of_unary_primitive p =
  match p with
  | Block_load _ ->
    reading_from_an_array_like_thing Unsafe
  | Duplicate_array (_, Immutable) ->
    (* Duplicate_array (_, Immutable) is allowed only on immutable arrays. *)
    Only_generative_effects, No_coeffects
  | Duplicate_array (_, Mutable)
  | Duplicate_record { repr = _; num_fields = _; } ->
    Only_generative_effects, Has_coeffects
  | Is_int -> No_effects, No_coeffects
  | Get_tag -> No_effects, Has_coeffects
  | String_length _ -> reading_from_an_array_like_thing Unsafe
  | Swap_byte_endianness
  | Int_as_pointer
  | Opaque -> No_effects, No_coeffects
  | Raise -> Arbitrary_effects, No_coeffects
  | Int_arith Neg
  | Float_arith (Abs | Neg)
  | Int_of_float
  | Float_of_int -> No_effects, No_coeffects
  | Array_length _ ->
    reading_from_an_array_like_thing Unsafe
  | Bigarray_length { dimension = _; } ->
    reading_from_an_array_like_thing Unsafe
  | Unbox_or_untag_number _ ->
    No_effects, No_coeffects
  | Box_or_tag_number Naked_immediate ->
    No_effects, No_coeffects
  | Box_or_tag_number (
      Naked_float | Naked_int32 | Naked_int64 | Naked_nativeint) ->
    Only_generative_effects, No_coeffects

type int_arith_op = (* CR? prefix with "binary"? *)
  | Add | Sub | Mul
  | Div of is_safe
  | Mod of is_safe
  | And | Or | Xor

let print_int_arith_op ppf o =
  let fprintf = Format.fprintf in
  match o with
  | Add -> fprintf ppf "+"
  | Sub -> fprintf ppf "-"
  | Mul -> fprintf ppf "*"
  | Div Safe -> fprintf ppf "/"
  | Div Unsafe -> fprintf ppf "/u"
  | Mod Safe -> fprintf ppf "mod"
  | Mod Unsafe -> fprintf ppf "mod_unsafe"
  | And -> fprintf ppf "and"
  | Or -> fprintf ppf "or"
  | Xor -> fprintf ppf "xor"

type int_shift_op = Lsl | Lsr | Asr

let print_int_shift_op ppf o =
  let fprintf = Format.fprintf in
  match o with
  | Lsl -> fprintf ppf "lsl"
  | Lsr -> fprintf ppf "lsr"
  | Asr -> fprintf ppf "asr"

type binary_float_arith_op = Add | Sub | Mul | Div

let print_binary_float_arith_op ppf o =
  let fprintf = Format.fprintf in
  match o with
  | Add -> fprintf ppf "+."
  | Sub -> fprintf ppf "-."
  | Mul -> fprintf ppf "*."
  | Div -> fprintf ppf "/."

type binary_primitive =
  | Block_load_computed_index
  | Set_field of int * setfield_kind * init_or_assign (* CR? rename to Block_set? *)
  | Int_arith of K.Of_naked_number_not_float.t * binary_int_arith_op
  | Int_shift of K.Of_naked_number_not_float.t * int_shift_op
  | Int_comp of comparison
  | Float_arith of binary_float_arith_op
  | Float_comp of comparison
  | Bit_test
  | Array_load of array_kind * is_safe
  | String_load of string_accessor_width * is_safe
  | Bigstring_load of bigstring_accessor_width * is_safe

let print_binary_primitive ppf p =
  let fprintf = Format.fprintf in
  match p with
  | Block_load_computed_index ->
    fprintf ppf "block_load_computed"
  | Set_field (n, k, init) ->
    let init =
      match init with
      | Initialization -> "init"
      | Assignment -> ""
    in
    fprintf ppf "set_field_%a%s i"
      print_setfield_kind k
      print_init_or_assign init
      n
  | Int_arith (_k, o) -> print_int_arith_op ppf o
  | Int_shift (_k, o) -> print_int_shift_op ppf o
  | Int_comp c -> print_comparison ppf c
  | Float_arith o -> print_binary_float_arith_op o
  | Float_comp c -> print_comparison ppf c; fprintf ppf "."
  | Bit_test -> fprintf ppf "bit_test"
  | Array_load (array_kind, is_safe) ->
    fprintf ppf "array_load_%a[%a]"
      print_is_safe is_safe
      print_array_kind array_kind
  | String_load (string_accessor_width, is_safe) ->
    fprintf ppf "string_load_%a_%a"
      print_is_safe is_safe
      print_string_accessor_width string_accessor_width
  | Bigstring_load (bigstring_accessor_width, is_safe) ->
    fprintf ppf "bigstring_load_%a_%a"
      print_is_safe is_safe
      print_bigstring_accessor_width bigstring_accessor_width

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

let effects_and_coeffects_of_binary_primitive p =
  match p with
  | Block_load_computed_index ->
    reading_from_an_array_like_thing Unsafe
  | Set_field _ ->
    writing_to_an_array_like_thing Unsafe
  | Int_arith (Add | Sub | Mul | Div Unsafe | Mod Unsafe | And | Or | Xor) ->
    No_effects, No_coeffects
  | Int_arith (Div Safe | Mod Safe) -> Arbitrary_effects, No_coeffects
  | Int_shift _ -> No_effects, No_coeffects
  | Int_comp _ -> No_effects, No_coeffects
  | Float_arith (Add | Sub | Mul | Div) -> No_effects, No_coeffects
  | Float_comp _ -> No_effects, No_coeffects
  | Bit_test -> No_effects, No_coeffects
  | Array_load (_, is_safe)
  | String_load (_, is_safe)
  | Bigstring_load (_, is_safe) -> reading_from_an_array_like_thing is_safe

type ternary_primitive =
  | Set_field_computed_index of Flambda_kind.scanning * init_or_assign (* CR? rename to Block_set_computed? *)
  | Bytes_set of string_accessor_width * is_safe
  | Array_set of array_kind * is_safe
  | Bigstring_set of bigstring_accessor_width * is_safe

let print_ternary_primitive ppf p =
  let fprintf = Format.fprintf in
  match p with
  | Set_field_computed_index (_, init) ->
    fprintf ppf "setfield_computed_index%a" print_init_or_assign init
  | Bytes_set (string_accessor_width, is_safe) ->
    fprintf ppf "bytes_set_%a_%a"
      print_is_safe is_safe
      print_string_accessor_width string_accessor_width
  | Array_set (array_kind, is_safe) ->
    fprintf ppf "array_set__%a[%a]"
      print_is_safe is_safe
      print_array_kind array_kind
  | Bigstring_set (bigstring_accessor_width, is_safe) ->
    fprintf ppf "bigstring_set_%a_%a"
      print_is_safe is_safe
      print_bigstring_accessor_width bigstring_accessor_width

let args_kind_of_ternary_primitive p =
  match p with
  | Set_field_computed_index _
  | Bytes_set _
  | Array_set _
  | Bigstring_set _

let result_kind_of_ternary_primitive p : result_kind =
  match p with
  | Set_field_computed_index _
  | Bytes_set _
  | Array_set _
  | Bigstring_set _

let effects_and_coeffects_of_ternary_primitive p =
  match p with
  | Set_field_computed_index _ ->
    writing_to_an_array_like_thing Unsafe
  | Bytes_set (_, is_safe)
  | Array_set (_, is_safe)
  | Bigstring_set (_, is_safe) ->
    writing_to_an_array_like_thing is_safe

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

let effects_and_coeffects_of_variadic_primitive p =
  match p with
  | Make_block _
  | Make_array (_, Immutable)
  | Make_array (_, Mutable) -> Only_generative_effects, No_coeffects
  | Bigarray_set (is_safe, _, _, _) ->
    writing_to_an_array_like_thing is_safe
  | Bigarray_load (is_safe, _, _, _) ->
    reading_from_an_array_like_thing is_safe
  | Ccall of { name; native_name; args; result; alloc; } ->
    begin match name with
    | "caml_format_float" | "caml_format_int" | "caml_int32_format"
    | "caml_nativeint_format" | "caml_int64_format" ->
      (* CR mshinwell: xclerc thinks this is dubious.  Should there be some
         kind of annotation on externals? *)
      No_effects, No_coeffects
    | _ -> Arbitrary_effects, Has_coeffects
    end

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

let effects_and_coeffects (t : t) =
  match t with
  | Unary (prim, _) -> effects_and_coeffects_of_unary_primitive prim
  | Binary (prim, _, _) -> effects_and_coeffects_of_binary_primitive prim
  | Ternary (prim, _, _, _) -> effects_and_coeffects_of_ternary_primitive prim
  | Variadic (prim, _) -> effects_and_coeffects_of_variadic_primitive prim
