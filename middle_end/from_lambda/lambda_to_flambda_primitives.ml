(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2017 OCamlPro SAS                                    *)
(*   Copyright 2014--2017 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module P = Flambda_primitive

(* CR mshinwell: Moved here from Flambda_kind


val of_block_shape : Lambda.block_shape -> num_fields:int -> t
*)

let of_block_shape (shape : Lambda.block_shape) ~num_fields =
  match shape with
  | None ->
    List.init num_fields (fun _field -> Flambda_kind.value Must_scan)
  | Some shape ->
    let shape_length = List.length shape in
    if num_fields <> shape_length then begin
      Misc.fatal_errorf "Flambda_arity.of_block_shape: num_fields is %d \
          yet the shape has %d fields"
        num_fields
        shape_length
    end;
    List.map (fun (kind : Lambda.value_kind) ->
        match kind with
        | Pgenval | Pfloatval | Pboxedintval _ -> Flambda_kind.value Must_scan
        | Pintval -> Flambda_kind.value Can_scan
        | Pnaked_intval -> Flambda_kind.naked_immediate ())
      shape

let convert_mutable_flag (flag : Asttypes.mutable_flag)
      : P.mutable_or_immutable =
  match flag with
  | Mutable -> Mutable
  | Immutable -> Immutable

let convert (prim : Lambda.primitive) (args : Simple.t list) : P.t =
  match prim, args with
  | Pmakeblock (tag, flag, shape), _ ->
    let flag = convert_mutable_flag flag in
    let arity = of_block_shape shape ~num_fields:(List.length args) in
    Variadic (Make_block (Tag.Scannable.create_exn tag, flag, arity), args)
  | Pnegint, [arg] ->
    Unary (Int_arith (Flambda_kind.Standard_int.Tagged_immediate, Neg), arg)
  | Pfield field, [arg] ->
    (* CR pchambart: every load is annotated as mutable we must be
       careful to update that when we know it is not. This should not
       be an error.
       We need more type propagations to be precise here *)
    Unary (Block_load (field, Not_a_float, Mutable), arg)
  | Psetfield (field, immediate_or_pointer, initialization_or_assignment),
    [block; value] ->
    let set_kind : P.block_set_kind =
      match immediate_or_pointer with
        | Immediate -> Immediate
        | Pointer -> Pointer
    in
    let init_or_assign : P.init_or_assign =
      match initialization_or_assignment with
      | Assignment -> Assignment
      | Heap_initialization -> Initialization
      (* Root initialization cannot exist in lambda. This is
         represented by the static part of expressions in flambda. *)
      | Root_initialization -> assert false
    in
    Binary (Block_set (field, set_kind, init_or_assign), block, value)
  | ( Pfield _ | Pnegint | Psetfield _ ), _ ->
    Misc.fatal_errorf "Closure_conversion.convert_primitive: \
                       Wrong arrity for %a: %i"
      Printlambda.primitive prim (List.length args)
  | _ ->
    assert false
