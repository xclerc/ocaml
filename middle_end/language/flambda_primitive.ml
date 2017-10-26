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

type field_kind = Not_a_float | Float

type string_or_bytes = String | Bytes

type mutable_or_immutable = Immutable | Mutable

type init_or_assign = Initialization | Assignment

type is_safe = Safe | Unsafe

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

type bigarray_kind =
  | Unknown
  | Float32 | Float64
  | Sint8 | Uint8
  | Sint16 | Uint16
  | Int32 | Int64
  | Int_width_int | Targetint_width_int
  | Complex32 | Complex64

let element_kind_of_bigarray_kind k =
  match k with
  | Unknown -> K.value Must_scan
  | Float32
  | Float64 -> K.naked_float ()
  | Sint8
  | Uint8
  | Sint16
  | Uint16 -> K.naked_immediate ()
  | Int32 -> K.naked_int32 ()
  | Int64 -> K.naked_int64 ()
  | Int_width_int -> K.naked_immediate ()
  | Targetint_width_int -> K.naked_nativeint ()
  | Complex32
  | Complex64 ->
    (* See [copy_two_doubles] in bigarray_stubs.c. *)
    K.value Must_scan

type bigarray_layout = Unknown | C | Fortran

type raise_kind = Regular | Reraise | No_trace

type set_field_kind =
  | Immediate
  | Pointer
  | Float

type string_accessor_width =
  | Eight
  | Sixteen
  | Thirty_two
  | Sixty_four

type bigstring_accessor_width =
  | Sixteen
  | Thirty_two
  | Sixty_four

type num_dimensions = int

type boxed_integer = Pnativeint | Pint32 | Pint64

type record_representation =
  | Regular
  | Float
  | Unboxed { inlined : bool; }
  | Inlined of int
  | Extension

type unary_int_arith_op = Neg

type unary_float_arith_op = Abs | Neg

type result_kind =
  | Singleton of K.t
  | Unit
  | Never_returns

type unary_primitive =
  | Block_load of int * field_kind
  | Duplicate_array of array_kind * mutable_or_immutable
  | Duplicate_record of {
      repr : record_representation;
      num_fields : int;
    }
  | Is_int
  | Get_tag
  | String_length of string_or_bytes
  | Swap_byte_endianness of K.Of_naked_number_not_float.t
  | Int_as_pointer
  | Opaque_identity
  | Raise of raise_kind
  | Int_arith of K.Of_naked_number_not_float.t * unary_int_arith_op
  | Float_arith of unary_float_arity_op
  | Int_of_float
  | Float_of_int
  | Array_length of array_kind
  | Bigarray_length of { dimension : int; }
  | Unbox_or_untag_number of K.Of_naked_number.t
  | Box_or_tag_number of K.Of_naked_number.t

let print_unary_primitive p =
  let fprintf = Format.fprintf in
  match p with
  | Block_load (n, Not_a_float) -> fprintf ppf "field %i" n
  | Block_load (n, Float) -> fprintf ppf "floatfield %i" n
  | Duplicate_array (k, Mutable) ->
    fprintf ppf "duparray[%s]" print_array_kind k
  | Duplicate_array (k, Immutable) ->
    fprintf ppf "duparray_imm[%s]" print_array_kind k
  | Duplicate_record (rep, size) ->
    fprintf ppf "duprecord %a %i" print_record_representation rep size
  | Is_int -> fprintf ppf "isint"
  | Get_tag -> fprintf ppf "gettag"
  | String_length String -> fprintf ppf "string.length"
  | String_length Bytes -> fprintf ppf "bytes.length"
  | Swap_byte_endianness kind ->
    fprint ppf "bswap_%a" ppf K.Of_naked_number.print kind
  | Int_as_pointer -> fprintf ppf "int_as_pointer"
  | Opaque -> fprintf ppf "opaque"
  | Raise k -> fprintf ppf "%s" print_raise_kind k
  | Int_arith of K.Of_naked_number_not_float.t * unary_int_arith_op
  | Float_arith Neg -> fprintf ppf "~."
  | Int_of_float -> fprintf ppf "int_of_float"
  | Float_of_int -> fprintf ppf "float_of_int"
  | Array_length k -> fprintf ppf "array.length[%a]" array_kind k
  | Bigarray_length { dimension; } -> fprintf ppf "Bigarray.dim_%i" dimension
  | Punbox_number kind ->
    fprintf ppf "unbox_%a" K.Of_naked_number.print_lowercase kind
  | Pbox_number kind ->
    fprintf ppf "box_%a" K.Of_naked_number.print_lowercase kind

let arg_kind_of_unary_primitive p =
  match p with
  | Block_load (_index, (Float | Not_a_float))
  | Duplicate_array (kind, mut)
  | Duplicate_record { repr; num_fields; }
  | Is_int
  | Get_tag
  | String_length _ -> K.value Must_scan
  | Swap_byte_endianness kind -> K.Of_naked_number.to_kind kind
  | Int_as_pointer -> K.value Can_scan
  | Opaque -> K.value Must_scan
  | Raise _raise_kind -> K.value Must_scan
  | Int_arith (kind, _) -> kind
  | Float_arith _ -> K.naked_float ()
  | Int_of_float -> K.naked_float ()
  | Float_of_int -> K.naked_immediate ()
  | Array_length _
  | Bigarray_length _ -> K.value Must_scan
  | Unbox_or_untag_number Naked_immediate -> K.value Can_scan
  | Unbox_or_untag_number (
      Naked_float Naked_int32 | Naked_int64 | Naked_nativeint) ->
    K.value Must_scan
  | Box_or_tag_number kind -> K.Of_naked_number.to_kind kind

let result_kind_of_unary_primitive p : result_kind =
  match p with
  | Block_load (_index, Not_a_float) -> Singleton (K.value Must_scan)
  | Block_load (_index, Float) -> Singleton (K.naked_float ())
  | Duplicate_array _
  | Duplicate_record _ -> Singleton (K.value Must_scan)
  | Is_int
  | Get_tag
  | String_length _ -> Singleton (K.naked_immediate ())
  | Swap_byte_endianness kind ->
    Singleton (K.Of_naked_number_not_float.to_kind kind)
  | Int_as_pointer -> Singleton (K.naked_immediate ())
  | Opaque -> Singleton (K.value Must_scan)
  | Raise _ -> Never_returns
  | Int_arith (kind, _) -
    Singleton (K.Of_naked_number_not_float.to_kind kind)
  | Float_arith _ -> Singleton (K.naked_float ())
  | Int_of_float -> Singleton (K.naked_immediate ())
  | Float_of_int -> Singleton (K.naked_float ())
  | Array_length _
  | Bigarray_length _ -> Singleton (K.naked_immediate ())
  | Unbox_or_untag_number kind -> Singleton (K.Of_naked_number.to_kind kind)
  | Box_or_tag_number _ -> Singleton (K.value Must_scan)

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

type int_arith_op =
  | Add | Sub | Mul
  | Div of is_safe
  | Mod of is_safe
  | And | Or | Xor

type int_shift_op = Lsl | Lsr | Asr

type binary_float_arith_op = Add | Sub | Mul | Div

type binary_primitive =
  | Block_load_computed_index
  | Set_field of int * set_field_kind * init_or_assign
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
  | Block_load_computed_index ->
    K.value Must_scan, K.value Can_scan
  | Set_field _ ->
    K.value Must_scan, K.value Must_scan
  | Int_arith (kind, _) | Int_shift (kind, _) ->
    let kind = K.Of_naked_number_not_float.to_kind kind in
    kind, kind
  | Int_comp _ -> K.value Can_scan, K.value Can_scan
  | Float_arith _
  | Float_comp _ -> K.naked_float (), K.naked_float ()
  | Bit_test -> K.value Can_scan  (* CR mshinwell: is this correct? *)
  | Array_load _
  | String_load _ ->
  | Bigstring_load _ ->
    K.value Must_scan, K.value Can_scan
    K.value Must_scan, K.value Can_scan

let result_kind_of_binary_primitive ppf p : result_kind =
  match p with
  | Block_load_computed_index -> Singleton (K.value Must_scan)
  | Set_field _ -> Unit
  | Int_arith (kind, _)
  | Int_shift (kind, _) -> Singleton (K.Of_naked_number_not_float.to_kind kind)
  | Float_arith _ -> Singleton (K.naked_float ())
  | Int_comp _ ->
  | Float_comp _ -> Singleton (K.naked_immediate ())
  | Bit_test -> Singleton (K.value Can_scan)
  | Array_load (Dynamic_must_scan_or_naked_float | Must_scan) ->
    Singleton (K.value Must_scan)
  | Array_load Can_scan -> Singleton (K.value Can_scan)
  | Array_load Naked_float -> Singleton (K.naked_float ())
  | String_load _
  | Bigstring_load _ -> Singleton (K.naked_immediate ())

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
  | Set_field_computed_index of Flambda_kind.scanning * init_or_assign
  | Bytes_set of string_accessor_width * is_safe
  | Array_set of array_kind * is_safe
  | Bigstring_set of bigstring_accessor_width * is_safe

let print_ternary_primitive ppf p =
  | Set_field_computed_index (ptr, init) ->
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
  | Set_field_computed_index _
  | Bytes_set _
  | Array_set _
  | Bigstring_set _ -> K.value Must_scan, K.value Can_scan, K.value Must_scan

let result_kind_of_ternary_primitive p : result_kind =
  match p with
  | Set_field_computed_index _
  | Bytes_set _
  | Array_set _
  | Bigstring_set _ -> Unit

let effects_and_coeffects_of_ternary_primitive p =
  match p with
  | Set_field_computed_index _ ->
    writing_to_an_array_like_thing Unsafe
  | Bytes_set (_, is_safe)
  | Array_set (_, is_safe)
  | Bigstring_set (_, is_safe) ->
    writing_to_an_array_like_thing is_safe

type variadic_primitive =
  | Make_block of Tag.Scannable.t * mutable_or_immutable * Flambda_arity.t
  | Make_array of array_kind * mutable_or_immutable
  | Bigarray_set of is_safe * num_dimensions * bigarray_kind * bigarray_layout
  | Bigarray_load of is_safe * num_dimensions * bigarray_kind * bigarray_layout
  | C_call of {
      name : Linkage_name.t;
      native_name : Linkage_name.t;
      args : Flambda_arity.t;
      result : Flambda_kind.t;
      alloc : bool;
    }

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
  | Make_block (_tag, _mut, arity) -> arity
  | Make_array (Dynamic_must_scan_or_naked_float | Must_scan) ->
    K.value Must_scan
  | Make_array Can_scan -> K.value Can_scan
  | Make_array Naked_float -> K.naked_float ()
  | Bigarray_set (_, num_dims, kind, _) ->
    let array = K.value Must_scan in
    let index = List.init num_dims (fun _ -> K.value Can_scan) in
    let new_value = element_kind_of_bigarray_kind kind in
    [array] @ index @ [new_value]
  | Bigarray_load (_, _, kind, _) ->
    let array = K.value Must_scan in
    let index = List.init num_dims (fun _ -> K.value Can_scan) in
    [array] @ index
  | C_call { name = _; native_name = _; args; result = _; alloc = _; } -> args

let result_kind_of_variadic_primitive p : result_kind =
  match p with
  | Make_block _
  | Make_array _ -> [Flambda_kind.value Must_scan]
  | Bigarray_set _ -> Unit
  | Bigarray_load (_, _, kind, _) -> element_kind_of_bigarray_kind kind
  | C_call { name = _; native_name = _; args = _; result; alloc = _; } ->
    [result]

let effects_and_coeffects_of_variadic_primitive p =
  match p with
  | Make_block _
  | Make_array (_, Immutable)
  | Make_array (_, Mutable) -> Only_generative_effects, No_coeffects
  | Bigarray_set (is_safe, _, _, _) ->
    writing_to_an_array_like_thing is_safe
  | Bigarray_load (is_safe, _, _, _) ->
    reading_from_an_array_like_thing is_safe
  | C_call of { name; native_name; args; result; alloc; } ->
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
