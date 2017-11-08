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

type mutable_or_immutable = Immutable | Mutable

type effects =
  | No_effects
  | Only_generative_effects of mutable_or_immutable
  | Arbitrary_effects

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

type init_or_assign = Initialization | Assignment

let print_init_or_assign ppf init_or_assign =
  let fprintf = Format.fprintf in
  match init_or_assign with
  | Initialization -> fprintf ppf "init"
  | Assignment -> ()

type is_safe = Safe | Unsafe

let print_is_safe ppf s =
  let fprintf = Format.fprintf in
  match s with
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

let array_like_thing_index_kind = K.value Can_scan

let array_kind = K.value Must_scan
let bigarray_kind = K.value Must_scan
let bigstring_kind = K.value Must_scan
let bigstring_element_kind = K.naked_immediate ()
let block_kind = K.value Must_scan
let block_element_kind = K.value Must_scan
let string_or_bytes_kind = K.value Must_scan
let string_or_bytes_element_kind = K.naked_immediate ()

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

(*
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
  | Int_width_int -> fprintf ppf "int_width_int"
  | Targetint_width_int -> fprintf ppf "targetint_width_int"
  | Complex32 -> fprintf ppf "complex32"
  | Complex64 -> fprintf ppf "complex64"
*)

type bigarray_layout = Unknown | C | Fortran

(*
let print_bigarray_layout ppf l =
  let fprintf = Format.fprintf in
  match l with
  | Unknown -> fprintf ppf "unknown"
  | C -> fprintf ppf "C"
  | Fortran -> fprintf ppf "fortran"
*)

type raise_kind = Regular | Reraise | No_trace

let print_raise_kind ppf k =
  let fprintf = Format.fprintf in
  match k with
  | Regular -> fprintf ppf "regular"
  | Reraise -> fprintf ppf "reraise"
  | No_trace -> fprintf ppf "no_trace"

type block_set_kind =
  | Immediate
  | Pointer
  | Float

let print_block_set_kind ppf k =
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

type record_representation =
  | Regular
  | Float
  | Unboxed of { inlined : bool; }
  | Inlined of Tag.Scannable.t
  | Extension

let print_record_representation ppf repr =
  let fprintf = Format.fprintf in
  match repr with
  | Regular -> fprintf ppf "regular"
  | Inlined tag -> fprintf ppf "inlined(%a)" Tag.Scannable.print tag
  | Unboxed { inlined = false; } -> fprintf ppf "unboxed"
  | Unboxed { inlined = true; } -> fprintf ppf "inlined(unboxed)"
  | Float -> fprintf ppf "float"
  | Extension -> fprintf ppf "ext"

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

type arg_kinds =
  | Variadic of K.t list
  | Variadic_all_of_kind of K.t

type result_kind =
  | Singleton of K.t
  | Unit
  | Never_returns

type unary_primitive =
  | Block_load of int * field_kind * mutable_or_immutable
  | Duplicate_array of array_kind * mutable_or_immutable
  | Duplicate_record of {
      repr : record_representation;
      num_fields : int;
    }
  | Is_int
  | Get_tag
  | String_length of string_or_bytes
  | Swap_byte_endianness of K.Standard_int.t
  | Int_as_pointer
  | Opaque_identity
  | Raise of raise_kind
  | Int_arith of K.Standard_int.t * unary_int_arith_op
  | Int_conv of {
      src : Flambda_kind.Standard_int.t;
      dst : Flambda_kind.Standard_int.t;
    }
  | Float_arith of unary_float_arith_op
  | Int_of_float
  | Float_of_int
  | Array_length of array_kind
  | Bigarray_length of { dimension : int; }
  | Unbox_number of K.Boxable_number.t
  | Box_number of K.Boxable_number.t
  | Project_closure of Closure_id.Set.t
  | Move_within_set_of_closures of Closure_id.t Closure_id.Map.t
  | Project_var of Var_within_closure.t Closure_id.Map.t

let print_unary_primitive ppf p =
  let fprintf = Format.fprintf in
  match p with
  | Block_load (n, _k, _mut) ->
    fprintf ppf "block_load %i" n
  | Duplicate_array (k, Mutable) ->
    fprintf ppf "duplicate_array[%a]" print_array_kind k
  | Duplicate_array (k, Immutable) ->
    fprintf ppf "duplicate_array_imm[%a]" print_array_kind k
  | Duplicate_record { repr; num_fields; } ->
    fprintf ppf "duplicate_record %a %i"
      print_record_representation repr
      num_fields
  | Is_int -> fprintf ppf "is_int"
  | Get_tag -> fprintf ppf "get_tag"
  | String_length _ -> fprintf ppf "string_length"
  | Swap_byte_endianness _ -> fprintf ppf "swap_byte_endianness"
  | Int_as_pointer -> fprintf ppf "int_as_pointer"
  | Opaque_identity -> fprintf ppf "opaque_identity"
  | Raise k -> fprintf ppf "raise %a" print_raise_kind k
  | Int_arith (_k, o) -> print_unary_int_arith_op ppf o
  | Int_conv { src; dst; } ->
    fprintf ppf "conv_%a_to_%a"
      Flambda_kind.Standard_int.print src
      Flambda_kind.Standard_int.print dst
  | Float_arith o -> print_unary_float_arith_op ppf o
  | Int_of_float -> fprintf ppf "int_of_float"
  | Float_of_int -> fprintf ppf "float_of_int"
  | Array_length _ -> fprintf ppf "array_length"
  | Bigarray_length { dimension; } ->
    fprintf ppf "bigarray_length %a" print_num_dimesions dimension
  | Unbox_number k ->
    fprintf ppf "unbox_%a" K.Boxable_number.print_lowercase k
  | Box_number k ->
    fprintf ppf "box_%a" K.Boxable_number.print_lowercase k
  | Project_closure set ->
    Format.fprintf ppf "(project_closure@ %a)"
      Closure_id.Set.print set
  | Move_within_set_of_closures moves ->
    Format.fprintf ppf "(move_within_set_of_closures@ %a)"
      (Closure_id.Map.print Closure_id.print) moves
  | Project_var by_closure ->
    Format.fprintf ppf "(project_var@ %a)"
      (Closure_id.Map.print Var_within_closure.print) by_closure

let arg_kind_of_unary_primitive p =
  match p with
  | Block_load (_, Not_a_float, _) -> K.value Must_scan
  | Block_load (_, Float, _) -> K.naked_float ()
  | Duplicate_array _
  | Duplicate_record _
  | Is_int
  | Get_tag
  | String_length _ -> K.value Must_scan
  | Swap_byte_endianness kind -> K.Standard_int.to_kind kind
  | Int_as_pointer -> K.value Can_scan
  | Opaque_identity -> K.value Must_scan
  | Raise _ -> K.value Must_scan
  | Int_arith (kind, _) -> K.Standard_int.to_kind kind
  | Int_conv { src; dst = _; } -> K.Standard_int.to_kind src
  | Float_arith _ -> K.naked_float ()
  | Int_of_float -> K.value Can_scan
  | Float_of_int -> K.naked_float ()
  | Array_length _
  | Bigarray_length _ -> K.value Must_scan
  | Unbox_number _ -> K.value Must_scan
  | Box_number kind -> K.Boxable_number.to_kind kind
  | Project_closure _
  | Move_within_set_of_closures _
  | Project_var _ -> K.value Must_scan

let result_kind_of_unary_primitive p : result_kind =
  match p with
  | Block_load (_, Not_a_float, _) -> Singleton (K.value Must_scan)
  | Block_load (_, Float, _) -> Singleton (K.naked_float ())
  | Duplicate_array _
  | Duplicate_record _ -> Singleton (K.value Must_scan)
  | Is_int
  | Get_tag
  | String_length _ -> Singleton (K.value Can_scan)
  | Swap_byte_endianness kind -> Singleton (K.Standard_int.to_kind kind)
  | Int_as_pointer -> Singleton (K.naked_immediate ())
  | Opaque_identity -> Singleton (K.value Must_scan)
  | Raise _ -> Never_returns
  | Int_arith (kind, _) -> Singleton (K.Standard_int.to_kind kind)
  | Int_conv { src = _; dst; } -> Singleton (K.Standard_int.to_kind dst)
  | Float_arith _ -> Singleton (K.naked_float ())
  | Int_of_float -> Singleton (K.value Can_scan)
  | Float_of_int -> Singleton (K.naked_float ())
  | Array_length _
  | Bigarray_length _ -> Singleton (K.value Can_scan)
  | Unbox_number kind -> Singleton (K.Boxable_number.to_kind kind)
  | Box_number _ -> Singleton (K.value Must_scan)
  | Project_closure _
  | Move_within_set_of_closures _
  | Project_var _ -> Singleton (K.value Must_scan)

let effects_and_coeffects_of_unary_primitive p =
  match p with
  | Block_load (_, _, Immutable) -> No_effects, No_coeffects
  | Block_load (_, _, Mutable) ->
    reading_from_an_array_like_thing Unsafe
  | Duplicate_array (_, Immutable) ->
    (* Duplicate_array (_, Immutable) is allowed only on immutable arrays. *)
    Only_generative_effects Immutable, No_coeffects
  | Duplicate_array (_, Mutable)
  | Duplicate_record { repr = _; num_fields = _; } ->
    Only_generative_effects Mutable, Has_coeffects
  | Is_int -> No_effects, No_coeffects
  | Get_tag -> No_effects, Has_coeffects
  | String_length _ -> reading_from_an_array_like_thing Unsafe
  | Int_as_pointer
  | Opaque_identity -> Arbitrary_effects, Has_coeffects
  | Raise _ -> Arbitrary_effects, No_coeffects
  | Swap_byte_endianness _
  | Int_arith (_, Neg)
  | Int_conv _
  | Float_arith (Abs | Neg)
  | Int_of_float
  | Float_of_int -> No_effects, No_coeffects
  | Array_length _ ->
    reading_from_an_array_like_thing Unsafe
  | Bigarray_length { dimension = _; } ->
    reading_from_an_array_like_thing Unsafe
  | Unbox_number _ ->
    No_effects, No_coeffects
  | Box_number _ ->
    Only_generative_effects Immutable, No_coeffects
  | Project_closure _
  | Move_within_set_of_closures _
  | Project_var _ -> No_effects, No_coeffects

type binary_int_arith_op =
  | Add | Sub | Mul
  | Div of is_safe
  | Mod of is_safe
  | And | Or | Xor

let print_binary_int_arith_op ppf o =
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
  | Block_set of int * block_set_kind * init_or_assign
  | Int_arith of K.Standard_int.t * binary_int_arith_op
  | Int_shift of K.Standard_int.t * int_shift_op
  | Int_comp of K.Standard_int.t * comparison
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
  | Block_set (n, k, init) ->
    fprintf ppf "set_field_%a%a %i"
      print_block_set_kind k
      print_init_or_assign init
      n
  | Int_arith (_k, op) -> print_binary_int_arith_op ppf op
  | Int_shift (_k, op) -> print_int_shift_op ppf op
  | Int_comp (_, c) -> print_comparison ppf c
  | Float_arith op -> print_binary_float_arith_op ppf op
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
  | Block_load_computed_index ->
    block_kind, array_like_thing_index_kind
  | Block_set _ ->
    block_kind, block_element_kind
  | Int_arith (kind, _) ->
    let kind = K.Standard_int.to_kind kind in
    kind, kind
  | Int_shift (kind, _) ->
    K.Standard_int.to_kind kind, K.naked_immediate ()
  | Int_comp (kind, _) ->
    let kind = K.Standard_int.to_kind kind in
    kind, kind
  | Float_arith _
  | Float_comp _ -> K.naked_float (), K.naked_float ()
  | Bit_test -> string_or_bytes_kind, array_like_thing_index_kind
  | Array_load _ -> array_kind, array_like_thing_index_kind
  | String_load _ -> string_or_bytes_kind, array_like_thing_index_kind
  | Bigstring_load _ -> bigstring_kind, array_like_thing_index_kind

let result_kind_of_binary_primitive p : result_kind =
  match p with
  | Block_load_computed_index -> Singleton (block_element_kind)
  | Block_set _ -> Unit
  | Int_arith (kind, _)
  | Int_shift (kind, _) -> Singleton (K.Standard_int.to_kind kind)
  | Float_arith _ -> Singleton (K.naked_float ())
  | Int_comp _
  | Float_comp _ -> Singleton (K.naked_immediate ())
  | Bit_test -> Singleton (K.naked_immediate ())
  | Array_load ((Dynamic_must_scan_or_naked_float | Must_scan), _) ->
    Singleton (K.value Must_scan)
  | Array_load (Can_scan, _) -> Singleton (K.value Can_scan)
  | Array_load (Naked_float, _) -> Singleton (K.naked_float ())
  | String_load _ -> Singleton (string_or_bytes_element_kind)
  | Bigstring_load _ -> Singleton (bigstring_element_kind)

let effects_and_coeffects_of_binary_primitive p =
  match p with
  | Block_load_computed_index ->
    reading_from_an_array_like_thing Unsafe
  | Block_set _ ->
    writing_to_an_array_like_thing Unsafe
  | Int_arith (_kind,
      (Add | Sub | Mul | Div Unsafe | Mod Unsafe | And | Or | Xor)) ->
    No_effects, No_coeffects
  | Int_arith (_kind, (Div Safe | Mod Safe)) -> Arbitrary_effects, No_coeffects
  | Int_shift _ -> No_effects, No_coeffects
  | Int_comp _ -> No_effects, No_coeffects
  | Float_arith (Add | Sub | Mul | Div) -> No_effects, No_coeffects
  | Float_comp _ -> No_effects, No_coeffects
  | Bit_test -> No_effects, No_coeffects
  | Array_load (_, is_safe)
  | String_load (_, is_safe)
  | Bigstring_load (_, is_safe) -> reading_from_an_array_like_thing is_safe

type ternary_primitive =
  | Block_set_computed of Flambda_kind.scanning * init_or_assign
  | Bytes_set of string_accessor_width * is_safe
  | Array_set of array_kind * is_safe
  | Bigstring_set of bigstring_accessor_width * is_safe

let print_ternary_primitive ppf p =
  let fprintf = Format.fprintf in
  match p with
  | Block_set_computed (_, init) ->
    fprintf ppf "block_set_computed%a" print_init_or_assign init
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
  | Block_set_computed _ ->
    block_kind, array_like_thing_index_kind, block_element_kind
  | Bytes_set _ ->
    string_or_bytes_kind, array_like_thing_index_kind, string_or_bytes_element_kind
  | Array_set _ ->
    array_kind, array_like_thing_index_kind, K.value Must_scan
  | Bigstring_set _ ->
    bigstring_kind, array_like_thing_index_kind, bigstring_element_kind

let result_kind_of_ternary_primitive p : result_kind =
  match p with
  | Block_set_computed _
  | Bytes_set _
  | Array_set _
  | Bigstring_set _ -> Unit

let effects_and_coeffects_of_ternary_primitive p =
  match p with
  | Block_set_computed _ ->
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
  | Make_block (tag, Immutable, arity) ->
    fprintf ppf "makeblock %a%a"
      Tag.Scannable.print tag
      Flambda_arity.print arity
  | Make_block (tag, Mutable, arity) ->
    fprintf ppf "makemutable %a%a"
      Tag.Scannable.print tag
      Flambda_arity.print arity
  | Make_array (k, Mutable) ->
    fprintf ppf "makearray[%a]" print_array_kind k
  | Make_array (k, Immutable) ->
    fprintf ppf "makearray_imm[%a]" print_array_kind k
  | Bigarray_set _ -> fprintf ppf "bigarray_set"
  | Bigarray_load _ -> fprintf ppf "bigarray_load"
  | C_call { name; native_name = _; args; result; alloc = _; } ->
    fprintf ppf "%a : %a -> %a"
      Linkage_name.print name
      Flambda_arity.print args
      Flambda_kind.print result

let args_kind_of_variadic_primitive p : arg_kinds =
  match p with
  | Make_block (_tag, _mut, arity) -> Variadic arity
  | Make_array ((Dynamic_must_scan_or_naked_float | Must_scan), _) ->
    Variadic_all_of_kind (K.value Must_scan)
  | Make_array (Can_scan, _) ->
    Variadic_all_of_kind (K.value Can_scan)
  | Make_array (Naked_float, _) ->
    Variadic_all_of_kind (K.naked_float ())
  | Bigarray_set (_, num_dims, kind, _) ->
    let index = List.init num_dims (fun _ -> array_like_thing_index_kind) in
    let new_value = element_kind_of_bigarray_kind kind in
    Variadic ([bigarray_kind] @ index @ [new_value])
  | Bigarray_load (_, num_dims, _, _) ->
    let index = List.init num_dims (fun _ -> array_like_thing_index_kind) in
    Variadic ([bigarray_kind] @ index)
  | C_call { name = _; native_name = _; args; result = _; alloc = _; } ->
    Variadic args

let result_kind_of_variadic_primitive p : result_kind =
  match p with
  | Make_block _ -> Singleton block_kind
  | Make_array _ -> Singleton array_kind
  | Bigarray_set _ -> Unit
  | Bigarray_load (_, _, kind, _) ->
    Singleton (element_kind_of_bigarray_kind kind)
  | C_call { name = _; native_name = _; args = _; result; alloc = _; } ->
    Singleton result

let effects_and_coeffects_of_variadic_primitive p =
  match p with
  | Make_block _
  (* CR mshinwell: Arrays of size zero? *)
  | Make_array (_, Immutable) -> Only_generative_effects Immutable, No_coeffects
  | Make_array (_, Mutable) -> Only_generative_effects Mutable, No_coeffects
  | Bigarray_set (is_safe, _, _, _) ->
    writing_to_an_array_like_thing is_safe
  | Bigarray_load (Unsafe, _, (Unknown | Complex32 | Complex64), _) ->
    Only_generative_effects Immutable, Has_coeffects
  | Bigarray_load (is_safe, _, _, _) ->
    reading_from_an_array_like_thing is_safe
  | C_call { name = _; native_name = _; args = _; result = _; alloc = _; } ->
    (* CR-someday xclerc: we could add annotations to external declarations
       (akin to [@@noalloc]) in order to be able to refine the computation of
       effects/coeffects for such functions. *)
    Arbitrary_effects, Has_coeffects

type t =
  | Unary of unary_primitive * Simple.t
  | Binary of binary_primitive * Simple.t * Simple.t
  | Ternary of ternary_primitive * Simple.t * Simple.t * Simple.t
  | Variadic of variadic_primitive * (Simple.t list)

type primitive_application = t

let print ppf t =
  match t with
  | Unary (prim, v0) ->
    Format.fprintf ppf "@[(Prim %a %a)@]"
      print_unary_primitive prim
      Simple.print v0
  | Binary (prim, v0, v1) ->
    Format.fprintf ppf "@[(Prim %a %a %a)@]"
      print_binary_primitive prim
      Simple.print v0
      Simple.print v1
  | Ternary (prim, v0, v1, v2) ->
    Format.fprintf ppf "@[(Prim %a %a %a %a)@]"
      print_ternary_primitive prim
      Simple.print v0
      Simple.print v1
      Simple.print v2
  | Variadic (prim, vs) ->
    Format.fprintf ppf "@[(Prim %a %a)@]"
      print_variadic_primitive prim
      (Format.pp_print_list ~pp_sep:Format.pp_print_space Simple.print) vs

let free_names t =
  match t with
  | Unary (_prim, x0) -> Simple.free_names x0
  | Binary (_prim, x0, x1) ->
    Name.Set.union (Simple.free_names x0) (Simple.free_names x1)
  | Ternary (_prim, x0, x1, x2) ->
    Name.Set.union (Simple.free_names x0)
      (Name.Set.union (Simple.free_names x1) (Simple.free_names x2))
  | Variadic (_prim, xs) -> Simple.List.free_names xs

let rename_variables t ~f =
  match t with
  | Unary (prim, x0) -> Unary (prim, Simple.map_var x0 ~f)
  | Binary (prim, x0, x1) ->
    Binary (prim, Simple.map_var x0 ~f, Simple.map_var x1 ~f)
  | Ternary (prim, x0, x1, x2) ->
    Ternary (prim, Simple.map_var x0 ~f, Simple.map_var x1 ~f,
      Simple.map_var x2 ~f)
  | Variadic (prim, xs) ->
    Variadic (prim, List.map (fun x -> Simple.map_var x ~f) xs)

(* Probably not required
let arg_kinds (t : t) : arg_kinds =
  match t with
  | Unary (prim, _) ->
    let kind = arg_kind_of_unary_primitive prim in
    Unary kind
  | Binary (prim, _, _) ->
    let kind0, kind1 = args_kind_of_binary_primitive prim in
    Binary (kind0, kind1)
  | Ternary (prim, _, _, _) ->
    let kind0, kind1, kind2 = args_kind_of_ternary_primitive prim in
    Ternary (kind0, kind1, kind2)
  | Variadic (prim, _) ->
    args_kind_of_variadic_primitive prim
*)

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

module With_fixed_value = struct
  type t = primitive_application

  let create t =
    match effects_and_coeffects t with
    | No_effects, No_coeffects -> Some t
    | Only_generative_effects Immutable, No_coeffects ->
      (* Allow constructions of immutable blocks to be shared. *)
      Some t
    | _, _ -> None

  let to_primitive t = t

  let free_names = free_names
  let print = print
end
