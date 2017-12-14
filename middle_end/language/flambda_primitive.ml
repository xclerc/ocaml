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

module Generic_array_specialisation = struct
  type t =
    | No_specialisation
    | Full_of_naked_floats
    | Full_of_immediates
    | Full_of_arbitrary_values_but_not_floats

  let check () =
    if not Config.flat_float_array then begin
      Misc.fatal_errorf "Generic arrays cannot be used unless the \
        float array optimisation has been enabled at compiler configuration \
        time"
    end

  let no_specialisation () =
    check ();
    No_specialisation

  let full_of_naked_floats () =
    check ();
    Full_of_naked_floats

  let full_of_immediates () =
    check ();
    Full_of_immediates

  let full_of_arbitrary_values_but_not_floats () =
    check ();
    Full_of_arbitrary_values_but_not_floats

  let print ppf t =
    match t with
    | No_specialisation -> Format.pp_print_string ppf "not-specialised"
    | Full_of_naked_floats -> Format.pp_print_string ppf "floats"
    | Full_of_immediates -> Format.pp_print_string ppf "imms"
    | Full_of_arbitrary_values_but_not_floats ->
      Format.pp_print_string ppf "non-floats"

  let compare = Pervasives.compare
end

type mutable_or_immutable = Immutable | Mutable

let print_mutable_or_immutable ppf mut =
  match mut with
  | Immutable -> Format.pp_print_string ppf "Imm"
  | Mutable -> Format.pp_print_string ppf "Mut"

let compare_mutable_or_immutable mut1 mut2 =
  match mut1, mut2 with
  | Immutable, Immutable
  | Mutable, Mutable -> 0
  | Immutable, Mutable -> -1
  | Mutable, Immutable -> 1

type effects =
  | No_effects
  | Only_generative_effects of mutable_or_immutable
  | Arbitrary_effects

type coeffects = No_coeffects | Has_coeffects

(* CR mshinwell: These types should probably go in their own modules with
   a comparison function next to each. *)

type make_block_kind =
  | Full_of_values of Tag.Scannable.t * (Flambda_kind.Value_kind.t list)
  | Full_of_naked_floats
  | Generic_array of Generic_array_specialisation.t

let print_make_block_kind ppf kind =
  match kind with
  | Full_of_values (tag, arity) ->
    Format.fprintf ppf "values[%a: (%a)]"
      Tag.Scannable.print tag
      (Format.pp_print_list Flambda_kind.Value_kind.print) arity
  | Full_of_naked_floats -> Format.pp_print_string ppf "floats"
  | Generic_array generic ->
    Format.fprintf ppf "generic[%a]"
      Generic_array_specialisation.print generic

let compare_make_block_kind kind1 kind2 =
  match kind1, kind2 with
  | Full_of_values (tag1, arity1), Full_of_values (tag2, arity2) ->
    let c = Tag.Scannable.compare tag1 tag2 in
    if c <> 0 then c
    else Misc.Stdlib.List.compare K.Value_kind.compare arity1 arity2
  | Full_of_values _, _ -> -1
  | _, Full_of_values _ -> 1
  | Full_of_naked_floats, Full_of_naked_floats -> 0
  | Generic_array spec1, Generic_array spec2 ->
    Generic_array_specialisation.compare spec1 spec2
  | _, Generic_array _ -> -1
  | Generic_array _, _ -> 1

type duplicate_block_kind =
  | Full_of_values_known_length of
      Tag.Scannable.t * (Flambda_kind.Value_kind.t list)
  | Full_of_values_unknown_length of Tag.Scannable.t * Flambda_kind.Value_kind.t
  | Full_of_naked_floats of { length : Targetint.OCaml.t option; }
  | Generic_array of Generic_array_specialisation.t

let print_duplicate_block_kind ppf (kind : duplicate_block_kind) =
  match kind with
  | Full_of_values_known_length (tag, kinds) ->
    Format.fprintf ppf "%a: (%a)"
      Tag.Scannable.print tag
      (Format.pp_print_list Flambda_kind.Value_kind.print) kinds
  | Full_of_values_unknown_length (tag, kind) ->
    Format.fprintf ppf "%a: all %a"
      Tag.Scannable.print tag
      Flambda_kind.Value_kind.print kind
  | Full_of_naked_floats { length = None; } ->
    Format.pp_print_string ppf "floats"
  | Full_of_naked_floats { length = Some length; } ->
    Format.fprintf ppf "%a floats"
      Targetint.OCaml.print length
  | Generic_array spec ->
    Format.fprintf ppf "generic %a"
      Generic_array_specialisation.print spec

(* CR-someday mshinwell: We should have unboxed arrays of int32, int64 and
   nativeint. *)

type block_access_kind =
  | Any_value
  | Definitely_immediate
  | Naked_float
  | Generic_array of Generic_array_specialisation.t

let print_block_access_kind ppf kind =
  match kind with
  | Any_value -> Format.pp_print_string ppf "any"
  | Definitely_immediate -> Format.pp_print_string ppf "imm"
  | Naked_float -> Format.pp_print_string ppf "float"
  | Generic_array spec ->
    Format.fprintf ppf "generic(%a)" Generic_array_specialisation.print spec

let compare_block_access_kind kind1 kind2 =
  Pervasives.compare kind1 kind2

type string_or_bytes = String | Bytes

type init_or_assign = Initialization | Assignment

let print_init_or_assign ppf init_or_assign =
  let fprintf = Format.fprintf in
  match init_or_assign with
  | Initialization -> fprintf ppf "init"
  | Assignment -> fprintf ppf "assign"

type array_like_operation = Reading | Writing

let effects_of_operation operation =
  match operation with
  | Reading -> No_effects
  | Writing -> Arbitrary_effects

let reading_from_an_array_like_thing =
  let effects = effects_of_operation Reading in
  effects, Has_coeffects

let reading_from_an_immutable_array_like_thing =
  let effects = effects_of_operation Reading in
  effects, No_coeffects

let length_from_an_array_like_thing =
  if Config.ban_obj_dot_truncate then
    No_effects, No_coeffects
  else
    No_effects, Has_coeffects

let length_from_a_bigarray =
  (* Even if truncate is banned, reshape can change the length for a
     particular dimension (the overall size of the bigarray being
     guaranteed to remain constant). *)
  No_effects, Has_coeffects

let writing_to_an_array_like_thing =
  let effects = effects_of_operation Writing in
  (* no bound check should occur when executing the primitive,
     hence no coeffects *)
  effects, No_coeffects

let array_like_thing_index_kind = K.value Definitely_immediate

let bigarray_kind = K.value Definitely_pointer
let bigstring_kind = K.value Definitely_pointer
let block_kind = K.value Definitely_pointer
let array_kind = K.value Definitely_pointer
let _block_element_kind = K.value Unknown (* CR xclerc: now unused *)
let string_or_bytes_kind = K.value Definitely_pointer

let float_kind = K.naked_float ()
let int_kind = K.naked_immediate ()
let bool_kind = K.naked_immediate ()
let int32_kind = K.naked_int32 ()
let int64_kind = K.naked_int64 ()
let nativeint_kind = K.naked_nativeint ()
let unknown_kind = K.value Unknown
let complex_kind = K.value Definitely_pointer (* See [copy_two_doubles] in bigarray_stubs.c. *)

let arithmetic_effects = No_effects, No_coeffects


type signed_or_unsigned =
  | Signed
  | Unsigned

type comparison = Eq | Neq | Lt | Gt | Le | Ge

let print_comparison ppf signedness c =
  let fprintf = Format.fprintf in
  match signedness with
  | Unsigned ->
    begin match c with
    | Eq -> fprintf ppf "=="
    | Neq -> fprintf ppf "!="
    | Lt -> fprintf ppf "<"
    | Le -> fprintf ppf "<="
    | Gt -> fprintf ppf ">"
    | Ge -> fprintf ppf ">="
    end
  | Signed ->
    begin match c with
    | Eq -> fprintf ppf "==u"
    | Neq -> fprintf ppf "!=u"
    | Lt -> fprintf ppf "<u"
    | Le -> fprintf ppf "<=u"
    | Gt -> fprintf ppf ">u"
    | Ge -> fprintf ppf ">=u"
    end

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
  | Unknown -> unknown_kind
  | Float32
  | Float64 -> float_kind
  | Sint8
  | Uint8
  | Sint16
  | Uint16 -> int_kind
  | Int32 -> int32_kind
  | Int64 -> int64_kind
  | Int_width_int -> int_kind
  | Targetint_width_int -> nativeint_kind
  | Complex32
  | Complex64 -> complex_kind

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

type string_like_value =
  | String
  | Bytes
  | Bigstring

let print_string_like_value ppf s =
  match s with
  | String -> Format.pp_print_string ppf "string"
  | Bytes -> Format.pp_print_string ppf "bytes"
  | Bigstring -> Format.pp_print_string ppf "bigstring"

type bytes_like_value =
  | Bytes
  | Bigstring

let print_bytes_like_value ppf b =
  match b with
  | Bytes -> Format.pp_print_string ppf "bytes"
  | Bigstring -> Format.pp_print_string ppf "bigstring"

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

let byte_width_of_string_accessor_width width =
  match width with
  | Eight -> 1
  | Sixteen -> 2
  | Thirty_two -> 4
  | Sixty_four -> 8

let kind_of_string_accessor_width width =
  match width with
  | Eight | Sixteen -> int_kind
  | Thirty_two -> int32_kind
  | Sixty_four -> int64_kind

type num_dimensions = int

let print_num_dimensions ppf d =
  Format.fprintf ppf "%d" d

type unary_int_arith_op = Not | Neg | Swap_byte_endianness

let print_unary_int_arith_op ppf o =
  let fprintf = Format.fprintf in
  match o with
  | Not -> fprintf ppf "~"
  | Neg -> fprintf ppf "-"
  | Swap_byte_endianness -> fprintf ppf "bswap"

type unary_float_arith_op = Abs | Neg

let print_unary_float_arith_op ppf o =
  let fprintf = Format.fprintf in
  match o with
  | Abs -> fprintf ppf "abs"
  | Neg -> fprintf ppf "-"

type arg_kinds =
  | Variadic of K.t list
  | Variadic_all_of_kind of K.t

type result_kind =
  | Singleton of K.t
  | Unit
  | Never_returns

type unary_primitive =
  | Duplicate_block of {
      kind : duplicate_block_kind;
      source_mutability : mutable_or_immutable;
      destination_mutability : mutable_or_immutable;
    }
  | Is_int
  | Get_tag of {
      possible_tags_and_sizes : int Tag.Map.t;
    }
  | Array_length of block_access_kind
  | Bigarray_length of { dimension : int; }
  | String_length of string_or_bytes
  | Int_as_pointer
  | Opaque_identity
  | Int_arith of Flambda_kind.Standard_int.t * unary_int_arith_op
  | Float_arith of unary_float_arith_op
  | Num_conv of {
      src : Flambda_kind.Standard_int_or_float.t;
      dst : Flambda_kind.Standard_int_or_float.t;
    }
  | Unbox_number of Flambda_kind.Boxable_number.t
  | Box_number of Flambda_kind.Boxable_number.t
  | Project_closure of Closure_id.Set.t
  | Move_within_set_of_closures of Closure_id.t Closure_id.Map.t
  | Project_var of Var_within_closure.t Closure_id.Map.t

(* NOTE: when a sum type is modified, check calls of the associated ignore
         function in order to ensure that the change has no semantic impact *)
let ignore_duplicate_block_kind (_ : duplicate_block_kind) = ()
let ignore_mutable_or_immutable (Immutable | Mutable : mutable_or_immutable) = ()
let ignore_possible_tags_and_sizes (_ : int Tag.Map.t) = ()
let ignore_string_or_bytes (String | Bytes : string_or_bytes) = ()
let ignore_unary_int_arith_op (Not | Neg | Swap_byte_endianness : unary_int_arith_op) = ()
let ignore_unary_float_arith_op (Abs | Neg : unary_float_arith_op) = ()
let ignore_standard_int (_ : K.Standard_int.t ) = ()
let ignore_standard_int_or_float (_ : K.Standard_int_or_float.t ) = ()
let ignore_dimension (_ : int) = ()
let ignore_block_access_kind (_ : block_access_kind) = ()
let ignore_boxable_number (_ : K.Boxable_number.t) = ()
let ignore_closure_id_set (_ : Closure_id.Set.t) = ()
let ignore_closure_id_map (_ : Closure_id.t Closure_id.Map.t) = ()
let ignore_var_closure_id_map (_ : Var_within_closure.t Closure_id.Map.t) = ()

let compare_unary_primitive p1 p2 =
  let unary_primitive_numbering p =
    match p with
    | Duplicate_block _ -> 0
    | Is_int -> 1
    | Get_tag _ -> 2
    | Array_length _ -> 3
    | Bigarray_length _ -> 4
    | String_length _ -> 5
    | Int_as_pointer -> 6
    | Opaque_identity -> 7
    | Int_arith _ -> 8
    | Float_arith _ -> 9
    | Num_conv _ -> 10
    | Unbox_number _ -> 11
    | Box_number _ -> 12
    | Project_closure _ -> 13
    | Move_within_set_of_closures _ -> 14
    | Project_var _ -> 15
  in
  match p1, p2 with
  | Duplicate_block { kind = kind1;
        source_mutability = source_mutability1;
        destination_mutability = destination_mutability1;
      },
    Duplicate_block { kind = kind2;
        source_mutability = source_mutability2;
        destination_mutability = destination_mutability2;
      } ->
    let c = Pervasives.compare kind1 kind2 in
    if c <> 0 then c
    else
      let c = Pervasives.compare source_mutability1 source_mutability2 in
      if c <> 0 then c
      else
        Pervasives.compare destination_mutability1 destination_mutability2
  | String_length kind1, String_length kind2 ->
    Pervasives.compare kind1 kind2
  | Int_arith (kind1, op1), Int_arith (kind2, op2) ->
    let c = K.Standard_int.compare kind1 kind2 in
    if c <> 0 then c
    else Pervasives.compare op1 op2
  | Num_conv { src = src1; dst = dst1; },
      Num_conv { src = src2; dst = dst2; } ->
    let c = K.Standard_int_or_float.compare src1 src2 in
    if c <> 0 then c
    else K.Standard_int_or_float.compare dst1 dst2
  | Float_arith op1, Float_arith op2 ->
    Pervasives.compare op1 op2
  | Array_length kind1, Array_length kind2 ->
    Pervasives.compare kind1 kind2
  | Bigarray_length { dimension = dim1; },
      Bigarray_length { dimension = dim2; } ->
    Pervasives.compare dim1 dim2
  | Unbox_number kind1, Unbox_number kind2 ->
    K.Boxable_number.compare kind1 kind2
  | Box_number kind1, Box_number kind2 ->
    K.Boxable_number.compare kind1 kind2
  | Project_closure set1, Project_closure set2 ->
    Closure_id.Set.compare set1 set2
  | Move_within_set_of_closures map1, Move_within_set_of_closures map2 ->
    Closure_id.Map.compare Closure_id.compare map1 map2
  | Project_var map1, Project_var map2 ->
    Closure_id.Map.compare Var_within_closure.compare map1 map2
  | (Duplicate_block _
    | Is_int
    | Get_tag _
    | String_length _
    | Int_as_pointer
    | Opaque_identity
    | Int_arith _
    | Num_conv _
    | Float_arith _
    | Array_length _
    | Bigarray_length _
    | Unbox_number _
    | Box_number _
    | Project_closure _
    | Move_within_set_of_closures _
    | Project_var _), _ ->
    Pervasives.compare (unary_primitive_numbering p1)
      (unary_primitive_numbering p2)

let print_unary_primitive ppf p =
  let fprintf = Format.fprintf in
  match p with
  | Duplicate_block { kind; source_mutability; destination_mutability; } ->
    fprintf ppf "duplicate_array[%a, %a -> %a]"
      print_duplicate_block_kind kind
      print_mutable_or_immutable source_mutability
      print_mutable_or_immutable destination_mutability
  | Is_int -> fprintf ppf "is_int"
  | Get_tag _ -> fprintf ppf "get_tag"
  | String_length _ -> fprintf ppf "string_length"
  | Int_as_pointer -> fprintf ppf "int_as_pointer"
  | Opaque_identity -> fprintf ppf "opaque_identity"
  | Int_arith (_k, o) -> print_unary_int_arith_op ppf o
  | Num_conv { src; dst; } ->
    fprintf ppf "conv_%a_to_%a"
      Flambda_kind.Standard_int_or_float.print src
      Flambda_kind.Standard_int_or_float.print dst
  | Float_arith o -> print_unary_float_arith_op ppf o
  | Array_length _ -> fprintf ppf "array_length"
  | Bigarray_length { dimension; } ->
    fprintf ppf "bigarray_length %a" print_num_dimensions dimension
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

(* CR xclerc: there is no dedicated way to read the length of a bigstring.
   A bigstring is a bigarray_of dimension 1, so it seems plausible that we
   should have no coeffects, as the coeffects from [length_from_a_bigarray]
   are due to [reshape] (and [reshape] has no effect on a bigarray whose
   dimension is 1, as [reshape] does not change the overall size). *)
let arg_kind_of_unary_primitive p =
  match p with
  | Duplicate_block { kind; source_mutability; destination_mutability; } ->
    ignore_duplicate_block_kind kind;
    ignore_mutable_or_immutable source_mutability;
    ignore_mutable_or_immutable destination_mutability;
    block_kind
  | Is_int ->
    unknown_kind
  | Get_tag { possible_tags_and_sizes; } ->
    ignore_possible_tags_and_sizes possible_tags_and_sizes;
    block_kind
  | String_length sob ->
    ignore_string_or_bytes sob;
    string_or_bytes_kind
  | Int_as_pointer ->
    int_kind
  | Opaque_identity ->
    unknown_kind
  | Int_arith (kind, op) ->
    ignore_unary_int_arith_op op;
    K.Standard_int.to_kind kind
  | Num_conv { src; dst; } ->
    ignore_standard_int_or_float dst;
    K.Standard_int_or_float.to_kind src
  | Float_arith op ->
    ignore_unary_float_arith_op op;
    float_kind
  | Array_length bak ->
    ignore_block_access_kind bak;
    array_kind
  | Bigarray_length { dimension; } ->
    ignore_dimension dimension;
    bigarray_kind
  | Unbox_number bn ->
    ignore_boxable_number bn;
    block_kind
  | Box_number kind ->
    K.Boxable_number.to_kind kind
  | Project_closure cis ->
    ignore_closure_id_set cis;
    block_kind
  | Move_within_set_of_closures cim ->
    ignore_closure_id_map cim;
    block_kind
  | Project_var vcim ->
    ignore_var_closure_id_map vcim;
    block_kind

let result_kind_of_unary_primitive p : result_kind =
  Singleton (match p with
    | Duplicate_block { kind; source_mutability; destination_mutability; } ->
      ignore_duplicate_block_kind kind;
      ignore_mutable_or_immutable source_mutability;
      ignore_mutable_or_immutable destination_mutability;
      block_kind
    | Is_int ->
      bool_kind
    | Get_tag { possible_tags_and_sizes; } ->
      ignore_possible_tags_and_sizes possible_tags_and_sizes;
      int_kind
    | String_length sob ->
      ignore_string_or_bytes sob;
      int_kind
    | Int_as_pointer ->
      (* This primitive is *only* to be used when the resulting pointer points
         at something which is a valid OCaml value (even if outside of the
         heap). *)
      unknown_kind (* CR xclerc: could it be "Definitely_pointer"? *)
    | Opaque_identity ->
      unknown_kind
    | Int_arith (kind, op) ->
      ignore_unary_int_arith_op op;
      K.Standard_int.to_kind kind
    | Num_conv { src; dst; } ->
      ignore_standard_int_or_float src;
      K.Standard_int_or_float.to_kind dst
    | Float_arith op ->
      ignore_unary_float_arith_op op;
      float_kind
    | Array_length bak ->
      ignore_block_access_kind bak;
      int_kind
    | Bigarray_length { dimension; } ->
      ignore_dimension dimension;
      int_kind
    | Unbox_number kind ->
      K.Boxable_number.to_kind kind
    | Box_number bn ->
      ignore_boxable_number bn;
      block_kind
    | Project_closure cis ->
      ignore_closure_id_set cis;
      block_kind
    | Move_within_set_of_closures cim ->
      ignore_closure_id_map cim;
      block_kind
    | Project_var vcim ->
      ignore_var_closure_id_map vcim;
      unknown_kind)

let effects_and_coeffects_of_unary_primitive p =
  match p with
  | Duplicate_block { kind; source_mutability; destination_mutability; } ->
    ignore_duplicate_block_kind kind;
    begin match source_mutability with
    | Immutable ->
      (* Beware: we still need to read the size of the block being duplicated,
         which is a coeffect, unless [Config.ban_obj_dot_truncate] is on. *)
      Only_generative_effects destination_mutability,
      (if Config.ban_obj_dot_truncate then No_coeffects else Has_coeffects)
    | Mutable ->
      Only_generative_effects destination_mutability, Has_coeffects
    end
  | Is_int ->
    No_effects, No_coeffects
  | Get_tag { possible_tags_and_sizes; } ->
    ignore_possible_tags_and_sizes possible_tags_and_sizes;
    (* CR xclerc: isn't truncate only expected to change the tag (and hence
       not the size)?  *)
    if Config.ban_obj_dot_truncate then No_effects, No_coeffects
    else No_effects, Has_coeffects
  | String_length sob ->
    ignore_string_or_bytes sob;
    length_from_an_array_like_thing
  | Int_as_pointer ->
    (* CR xclerc: not sure about "Arbitrary_effects", why could it have more
       effects than "Duplicate_block"? More: this one does not allocate.
       Or maybe the couple "Arbitrary_effects, Has_coeffects" is used to
       prevent any optimization. *)
    Arbitrary_effects, Has_coeffects
  | Opaque_identity ->
    Arbitrary_effects, Has_coeffects
  | Int_arith (kind, op) ->
    ignore_standard_int kind;
    ignore_unary_int_arith_op op;
    arithmetic_effects
  | Num_conv { src; dst; } ->
    ignore_standard_int_or_float src;
    ignore_standard_int_or_float dst;
    arithmetic_effects
  | Float_arith op ->
    ignore_unary_float_arith_op op;
    arithmetic_effects
  | Array_length bak ->
    ignore_block_access_kind bak;
    length_from_an_array_like_thing
  | Bigarray_length { dimension; } ->
    ignore_dimension dimension;
    length_from_a_bigarray
  | Unbox_number bn ->
    ignore_boxable_number bn;
    No_effects, No_coeffects
  | Box_number bn ->
    ignore_boxable_number bn;
    Only_generative_effects Immutable, No_coeffects
  | Project_closure cis ->
    ignore_closure_id_set cis;
    No_effects, No_coeffects
  | Move_within_set_of_closures cim ->
    ignore_closure_id_map cim;
    No_effects, No_coeffects
  | Project_var vcim ->
    ignore_var_closure_id_map vcim;
    No_effects, No_coeffects

type binary_int_arith_op =
  | Add | Sub | Mul | Div | Mod | And | Or | Xor

let print_binary_int_arith_op ppf o =
  let fprintf = Format.fprintf in
  match o with
  | Add -> fprintf ppf "+"
  | Sub -> fprintf ppf "-"
  | Mul -> fprintf ppf "*"
  | Div -> fprintf ppf "/"
  | Mod -> fprintf ppf "mod"
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
  | Block_load of block_access_kind * mutable_or_immutable
  | String_or_bigstring_load of string_like_value * string_accessor_width
  | Int_arith of Flambda_kind.Standard_int.t * binary_int_arith_op
  | Int_shift of Flambda_kind.Standard_int.t * int_shift_op
  | Int_comp of Flambda_kind.Standard_int.t * signed_or_unsigned * comparison
  | Float_arith of binary_float_arith_op
  | Float_comp of comparison

(* NOTE: when a sum type is modified, check calls of the associated ignore
         function in order to ensure that the change has no semantic impact *)
let ignore_string_like_value (String | Bytes | Bigstring : string_like_value) = ()
let ignore_string_accessor_width (Eight | Sixteen | Thirty_two | Sixty_four : string_accessor_width) = ()
let ignore_binary_int_arith_op (Add | Sub | Mul | Div | Mod | And | Or | Xor : binary_int_arith_op) = ()
let ignore_int_shift_op (Lsl | Lsr | Asr : int_shift_op) = ()
let ignore_signed_or_unsigned (Signed | Unsigned : signed_or_unsigned) = ()
let ignore_comparison (Eq | Neq | Lt | Gt | Le | Ge : comparison) = ()
let ignore_binary_float_arith_op (Add | Sub | Mul | Div : binary_float_arith_op) = ()

let compare_binary_primitive p1 p2 =
  let binary_primitive_numbering p =
    match p with
    | Block_load _ -> 0
    | String_or_bigstring_load _ -> 1
    | Int_arith _ -> 2
    | Int_shift _ -> 3
    | Int_comp _ -> 4
    | Float_arith _ -> 5
    | Float_comp _ -> 6
  in
  match p1, p2 with
  | Block_load (kind1, mut1), Block_load (kind2, mut2) ->
    let c = compare_block_access_kind kind1 kind2 in
    if c <> 0 then c
    else compare_mutable_or_immutable mut1 mut2
  | Int_arith (kind1, op1), Int_arith (kind2, op2) ->
    let c = K.Standard_int.compare kind1 kind2 in
    if c <> 0 then c
    else Pervasives.compare op1 op2
  | Int_shift (kind1, op1), Int_shift (kind2, op2) ->
    let c = K.Standard_int.compare kind1 kind2 in
    if c <> 0 then c
    else Pervasives.compare op1 op2
  | Int_comp (kind1, signedness1, comp1),
    Int_comp (kind2, signedness2, comp2) ->
    let c = K.Standard_int.compare kind1 kind2 in
    if c <> 0 then c
    else
      let c = Pervasives.compare signedness1 signedness2 in
      if c <> 0 then c
      else Pervasives.compare comp1 comp2
  | Float_arith op1, Float_arith op2 ->
    Pervasives.compare op1 op2
  | Float_comp comp1, Float_comp comp2 ->
    Pervasives.compare comp1 comp2
  | (Block_load _
    | String_or_bigstring_load _
    | Int_arith _
    | Int_shift _
    | Int_comp _
    | Float_arith _
    | Float_comp _), _ ->
    Pervasives.compare (binary_primitive_numbering p1)
      (binary_primitive_numbering p2)

let print_binary_primitive ppf p =
  let fprintf = Format.fprintf in
  match p with
  | Block_load (kind, mut) ->
    fprintf ppf "block_load[%a,%a]"
      print_block_access_kind kind
      print_mutable_or_immutable mut
  | String_or_bigstring_load (string_like, width) ->
    fprintf ppf "string_load[%a,%a]"
      print_string_like_value string_like
      print_string_accessor_width width
  | Int_arith (_k, op) -> print_binary_int_arith_op ppf op
  | Int_shift (_k, op) -> print_int_shift_op ppf op
  | Int_comp (_, signedness, c) -> print_comparison ppf signedness c
  | Float_arith op -> print_binary_float_arith_op ppf op
  | Float_comp c -> print_comparison ppf Signed c; fprintf ppf "."

let args_kind_of_binary_primitive p =
  match p with
  | Block_load (bak, mut) ->
    ignore_block_access_kind bak;
    ignore_mutable_or_immutable mut;
    block_kind, array_like_thing_index_kind
  | String_or_bigstring_load ((String | Bytes), saw) ->
    ignore_string_accessor_width saw;
    string_or_bytes_kind, array_like_thing_index_kind
  | String_or_bigstring_load (Bigstring, saw) ->
    ignore_string_accessor_width saw;
    bigstring_kind, array_like_thing_index_kind
  | Int_arith (kind, op) ->
    ignore_binary_int_arith_op op;
    let kind = K.Standard_int.to_kind kind in
    kind, kind
  | Int_shift (kind, op) ->
    ignore_int_shift_op op;
    K.Standard_int.to_kind kind, int_kind
  | Int_comp (kind, sou, cmp) ->
    ignore_signed_or_unsigned sou;
    ignore_comparison cmp;
    let kind = K.Standard_int.to_kind kind in
    kind, kind
  | Float_arith op ->
    ignore_binary_float_arith_op op;
    float_kind, float_kind
  | Float_comp cmp ->
    ignore_comparison cmp;
    float_kind, float_kind

let kind_of_block_access_kind = function
  | Any_value ->
    unknown_kind
  | Definitely_immediate ->
    int_kind
  | Naked_float ->
    float_kind
  | Generic_array No_specialisation ->
    unknown_kind
  | Generic_array Full_of_naked_floats ->
    float_kind
  | Generic_array Full_of_immediates ->
    int_kind
  | Generic_array Full_of_arbitrary_values_but_not_floats ->
    unknown_kind

let result_kind_of_binary_primitive p : result_kind =
  Singleton (match p with
    | Block_load (bak, mut) ->
      ignore_mutable_or_immutable mut;
      kind_of_block_access_kind bak
    | String_or_bigstring_load (slv, width) ->
      ignore_string_like_value slv;
      kind_of_string_accessor_width width
    | Int_arith (kind, op) ->
      ignore_binary_int_arith_op op;
      K.Standard_int.to_kind kind
    | Int_shift (kind, op) ->
      ignore_int_shift_op op;
      K.Standard_int.to_kind kind
    | Float_arith op ->
      ignore_binary_float_arith_op op;
      float_kind
    | Int_comp (kind, sou, cmp) ->
      ignore_standard_int kind;
      ignore_signed_or_unsigned sou;
      ignore_comparison cmp;
      bool_kind
    | Float_comp cmp ->
      ignore_comparison cmp;
      bool_kind)

let effects_and_coeffects_of_binary_primitive p =
  match p with
  | Block_load (bak, mut) ->
    ignore_block_access_kind bak;
    begin match mut with
    | Mutable -> reading_from_an_array_like_thing
    | Immutable -> reading_from_an_immutable_array_like_thing
    end
  | Int_arith (kind, op) ->
    ignore_standard_int kind;
    ignore_binary_int_arith_op op;
    arithmetic_effects
  | Int_shift (kind, op) ->
    ignore_standard_int kind;
    ignore_int_shift_op op;
    arithmetic_effects
  | Int_comp (kind, sou, cmp) ->
    ignore_standard_int kind;
    ignore_signed_or_unsigned sou;
    ignore_comparison cmp;
    arithmetic_effects
  | Float_arith op ->
    ignore_binary_float_arith_op op;
    arithmetic_effects
  | Float_comp cmp ->
    ignore_comparison cmp;
    arithmetic_effects
  | String_or_bigstring_load (slv, saw) ->
    ignore_string_accessor_width saw;
    begin match slv with
    | String -> reading_from_an_immutable_array_like_thing
    | Bytes | Bigstring -> reading_from_an_array_like_thing
    end

type ternary_primitive =
  | Block_set of block_access_kind * init_or_assign
  | Bytes_or_bigstring_set of bytes_like_value * string_accessor_width

(* NOTE: when a sum type is modified, check calls of the associated ignore
         function in order to ensure that the change has no semantic impact *)
let ignore_init_or_assign (Initialization | Assignment : init_or_assign) = ()
let ignore_bytes_like_value (Bytes | Bigstring : bytes_like_value) = ()

let compare_ternary_primitive p1 p2 =
  let ternary_primitive_numbering p =
    match p with
    | Block_set _ -> 0
    | Bytes_or_bigstring_set _ -> 1
  in
  match p1, p2 with
  | Block_set (kind1, init_or_assign1),
      Block_set (kind2, init_or_assign2) ->
    let c = compare_block_access_kind kind1 kind2 in
    if c <> 0 then c
    else Pervasives.compare init_or_assign1 init_or_assign2
  | Bytes_or_bigstring_set (kind1, width1),
      Bytes_or_bigstring_set (kind2, width2) ->
    let c = Pervasives.compare kind1 kind2 in
    if c <> 0 then c
    else Pervasives.compare width1 width2
  | (Block_set _
    | Bytes_or_bigstring_set _), _ ->
    Pervasives.compare (ternary_primitive_numbering p1)
      (ternary_primitive_numbering p2)

let print_ternary_primitive ppf p =
  let fprintf = Format.fprintf in
  match p with
  | Block_set (kind, init) ->
    fprintf ppf "block_set[%a,%a]"
      print_block_access_kind kind
      print_init_or_assign init
  | Bytes_or_bigstring_set (kind, string_accessor_width) ->
    fprintf ppf "bytes_set[%a,%a]"
      print_bytes_like_value kind
      print_string_accessor_width string_accessor_width

let args_kind_of_ternary_primitive p =
  match p with
  | Block_set (bak, ioa) ->
    ignore_init_or_assign ioa;
    block_kind, array_like_thing_index_kind,
      kind_of_block_access_kind bak
  | Bytes_or_bigstring_set (blv, saw) ->
    let bytes_or_bigstring_kind =
      match blv with
      | Bytes -> string_or_bytes_kind
      | Bigstring -> bigstring_kind
    in
    bytes_or_bigstring_kind, array_like_thing_index_kind,
      kind_of_string_accessor_width saw

let result_kind_of_ternary_primitive p : result_kind =
  match p with
  | Block_set (bak, ioa) ->
    ignore_block_access_kind bak;
    ignore_init_or_assign ioa;
    Unit
  | Bytes_or_bigstring_set (blv, saw) ->
    ignore_bytes_like_value blv;
    ignore_string_accessor_width saw;
    Unit

let effects_and_coeffects_of_ternary_primitive p =
  match p with
  | Block_set (bak, ioa) ->
    ignore_block_access_kind bak;
    ignore_init_or_assign ioa;
    writing_to_an_array_like_thing
  | Bytes_or_bigstring_set (blv, saw) ->
    ignore_bytes_like_value blv;
    ignore_string_accessor_width saw;
    writing_to_an_array_like_thing

type variadic_primitive =
  | Make_block of make_block_kind * mutable_or_immutable
  | Bigarray_set of num_dimensions * bigarray_kind * bigarray_layout
  | Bigarray_load of num_dimensions * bigarray_kind * bigarray_layout

(* NOTE: when a sum type is modified, check calls of the associated ignore
         function in order to ensure that the change has no semantic impact *)
let ignore_tag (_ : Tag.Scannable.t) = ()
let ignore_make_block_kind (Full_of_values _
                           | Full_of_naked_floats
                           | Generic_array _: make_block_kind) = ()
let ignore_num_dimensions (_ : num_dimensions) = ()
let ignore_bigarray_kind (Unknown
                          | Float32
                          | Float64
                          | Sint8
                          | Uint8
                          | Sint16
                          | Uint16
                          | Int32
                          | Int64
                          | Int_width_int
                          | Targetint_width_int
                          | Complex32
                          | Complex64 : bigarray_kind) = ()
let ignore_bigarray_layout (Unknown | C | Fortran : bigarray_layout) = ()

let compare_variadic_primitive p1 p2 =
  let variadic_primitive_numbering p =
    match p with
    | Make_block _ -> 0
    | Bigarray_set _ -> 1
    | Bigarray_load _ -> 2
  in
  match p1, p2 with
  | Make_block (kind1, mut1), Make_block (kind2, mut2) ->
    let c = compare_make_block_kind kind1 kind2 in
    if c <> 0 then c
    else Pervasives.compare mut1 mut2
  | Bigarray_set (num_dims1, kind1, layout1),
      Bigarray_set (num_dims2, kind2, layout2) ->
    let c = Pervasives.compare num_dims1 num_dims2 in
    if c <> 0 then c
    else
      let c = Pervasives.compare kind1 kind2 in
      if c <> 0 then c
      else Pervasives.compare layout1 layout2
  | (Make_block _
    | Bigarray_set _
    | Bigarray_load _
    ), _ ->
    Pervasives.compare (variadic_primitive_numbering p1)
      (variadic_primitive_numbering p2)

let print_variadic_primitive ppf p =
  let fprintf = Format.fprintf in
  match p with
  | Make_block (kind, mut) ->
    fprintf ppf "make_block[%a,%a]"
      print_make_block_kind kind
      print_mutable_or_immutable mut
  | Bigarray_set _ -> fprintf ppf "bigarray_set"
  | Bigarray_load _ -> fprintf ppf "bigarray_load"

let args_kind_of_variadic_primitive p : arg_kinds =
  match p with
  | Make_block (mbk, mut) ->
    ignore_mutable_or_immutable mut;
    begin match mbk with
    | Full_of_values (tag, value_kinds) ->
      ignore_tag tag;
      let kinds =
        List.map (fun value_kind -> K.value value_kind) value_kinds
      in
      Variadic kinds
    | Full_of_naked_floats ->
      Variadic_all_of_kind float_kind
    | Generic_array No_specialisation ->
      Variadic_all_of_kind unknown_kind
    | Generic_array Full_of_naked_floats ->
      Variadic_all_of_kind float_kind
    | Generic_array Full_of_immediates ->
      Variadic_all_of_kind int_kind
    | Generic_array Full_of_arbitrary_values_but_not_floats ->
      Variadic_all_of_kind unknown_kind
    end
  | Bigarray_set (num_dims, kind, layout) ->
    ignore_bigarray_layout layout;
    let index = List.init num_dims (fun _ -> array_like_thing_index_kind) in
    let new_value = element_kind_of_bigarray_kind kind in
    Variadic ([bigarray_kind] @ index @ [new_value])
  | Bigarray_load (num_dims, kind, layout) ->
    ignore_bigarray_kind kind;
    ignore_bigarray_layout layout;
    let index = List.init num_dims (fun _ -> array_like_thing_index_kind) in
    Variadic ([bigarray_kind] @ index)

let result_kind_of_variadic_primitive p : result_kind =
  match p with
  | Make_block (mbk, mut) ->
    ignore_make_block_kind mbk;
    ignore_mutable_or_immutable mut;
    Singleton block_kind
  | Bigarray_set (dims, kind, layout) ->
    ignore_num_dimensions dims;
    ignore_bigarray_kind kind;
    ignore_bigarray_layout layout;
    Unit
  | Bigarray_load (dims, kind, layout) ->
    ignore_num_dimensions dims;
    ignore_bigarray_layout layout;
    Singleton (element_kind_of_bigarray_kind kind)

let effects_and_coeffects_of_variadic_primitive p =
  match p with
  (* CR mshinwell: Arrays of size zero?
     xclerc: maybe, but if the size is statically known to be zero
     we can probably expect to produce the immediate 0 and never get
     there. *)
  | Make_block (mbk, mut) ->
    ignore_make_block_kind mbk;
    Only_generative_effects mut, No_coeffects
  | Bigarray_set (dims, kind, layout) ->
    ignore_num_dimensions dims;
    ignore_bigarray_kind kind;
    ignore_bigarray_layout layout;
    writing_to_an_array_like_thing
  | Bigarray_load (dims, (Unknown | Complex32 | Complex64), layout) ->
    ignore_num_dimensions dims;
    ignore_bigarray_layout layout;
    Only_generative_effects Immutable, Has_coeffects
  | Bigarray_load (dims, kind, layout) ->
    ignore_num_dimensions dims;
    ignore_bigarray_kind kind;
    ignore_bigarray_layout layout;
    reading_from_an_array_like_thing

type t =
  | Unary of unary_primitive * Simple.t
  | Binary of binary_primitive * Simple.t * Simple.t
  | Ternary of ternary_primitive * Simple.t * Simple.t * Simple.t
  | Variadic of variadic_primitive * (Simple.t list)

type primitive_application = t

include Identifiable.Make_no_hash (struct
  type nonrec t = t

  let compare t1 t2 =
    let numbering t =
      match t with
      | Unary _ -> 0
      | Binary _ -> 1
      | Ternary _ -> 2
      | Variadic _ -> 3
    in
    match t1, t2 with
    | Unary (p, s1), Unary (p', s1') ->
      let c = compare_unary_primitive p p' in
      if c <> 0 then c
      else Simple.compare s1 s1'
    | Binary (p, s1, s2), Binary (p', s1', s2') ->
      let c = compare_binary_primitive p p' in
      if c <> 0 then c
      else
        let c = Simple.compare s1 s1' in
        if c <> 0 then c
        else Simple.compare s2 s2'
    | Ternary (p, s1, s2, s3), Ternary (p', s1', s2', s3') ->
      let c = compare_ternary_primitive p p' in
      if c <> 0 then c
      else
        let c = Simple.compare s1 s1' in
        if c <> 0 then c
        else
          let c = Simple.compare s2 s2' in
          if c <> 0 then c
          else Simple.compare s3 s3'
    | Variadic (p, s), Variadic (p', s') ->
      let c = compare_variadic_primitive p p' in
      if c <> 0 then c
      else Simple.List.compare s s'
    | (Unary _ | Binary _ | Ternary _ | Variadic _), _ ->
      Pervasives.compare (numbering t1) (numbering t2)

  let equal t1 t2 =
    compare t1 t2 = 0

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
end)

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

let no_effects_or_coeffects t =
  match effects_and_coeffects t with
  | No_effects, No_coeffects -> true
  | _, _ -> false

let maybe_generative_effects_but_no_coeffects t =
  match effects_and_coeffects t with
  | (No_effects | Only_generative_effects _), No_coeffects -> true
  | _, _ -> false

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

  include Identifiable.Make_no_hash (struct
    type nonrec t = t

    let compare = compare
    let equal = equal
    let print = print
  end)
end
