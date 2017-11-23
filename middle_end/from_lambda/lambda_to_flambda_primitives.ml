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


(* *** Please see the top of flambda_primitive.mli for details on producing
   the new Duplicate_scannable_block primitive *** *)



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
  | Paddint, [arg1; arg2] ->
    Binary (Int_arith (Flambda_kind.Standard_int.Tagged_immediate, Add), arg1, arg2)
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

(*
[@@@ocaml.warning "-37"]

type expr_primitive =
  | Unary of P.unary_primitive * simple_or_prim
  | Binary of P.binary_primitive * simple_or_prim * simple_or_prim
  | Ternary of P.ternary_primitive * simple_or_prim * simple_or_prim * simple_or_prim
  | Variadic of P.variadic_primitive * (simple_or_prim list)
  | Checked of { validity_condition : expr_primitive;
                 primitive : expr_primitive;
                 failure : Symbol.t; (* Predefined exception *)
                 dbg : Debuginfo.t }

and simple_or_prim =
  | Simple of Simple.t
  | Prim of expr_primitive

let rec bind_rec
          (var : Variable.t)
          (prim : expr_primitive)
          (dbg : Debuginfo.t)
          (cont : Simple.t -> Flambda.Expr.t)
  : Flambda.Expr.t =
  match prim with
  | Unary (prim, arg) ->
    let cont arg =
      Flambda.Expr.create_let var (Flambda_kind.value Must_scan)
        (Prim (Unary (prim, arg), dbg))
        (cont (Simple.var var))
    in
    bind_rec_primitive arg dbg cont
  | Binary (prim, arg1, arg2) ->
    let cont2 arg2 =
      let cont1 arg1 =
        Flambda.Expr.create_let var (Flambda_kind.value Must_scan)
          (Prim (Binary (prim, arg1, arg2), dbg))
          (cont (Simple.var var))
      in
      bind_rec_primitive arg1 dbg cont1
    in
    bind_rec_primitive arg2 dbg cont2
  | Ternary (prim, arg1, arg2, arg3) ->
    let cont3 arg3 =
      let cont2 arg2 =
        let cont1 arg1 =
          Flambda.Expr.create_let var (Flambda_kind.value Must_scan)
            (Prim (Ternary (prim, arg1, arg2, arg3), dbg))
            (cont (Simple.var var))
        in
        bind_rec_primitive arg1 dbg cont1
      in
      bind_rec_primitive arg2 dbg cont2
    in
    bind_rec_primitive arg3 dbg cont3
  | Variadic (prim, args) ->
    let cont args =
      Flambda.Expr.create_let var (Flambda_kind.value Must_scan)
        (Prim (Variadic (prim, args), dbg))
        (cont (Simple.var var))
    in
    let rec build_cont args_to_convert converted_args =
      match args_to_convert with
      | [] ->
        cont converted_args
      | arg :: args_to_convert ->
        let cont arg =
          build_cont args_to_convert (arg :: converted_args)
        in
        bind_rec_primitive arg dbg cont
    in
    build_cont (List.rev args) []
  | Checked { validity_condition; primitive; failure; dbg } ->
    let exception_cont =
      (* À changer bientot: raise devient apply_cont *)
      let v = Variable.create "dummy" in
      Flambda.Expr.create_let v (Flambda_kind.value Must_scan)
        (Prim (Unary (Raise (Regular), Simple.symbol failure), dbg))
        (Simple (Simple.var v))

and bind_rec_primitive
      (prim : simple_or_prim)
      (dbg : Debuginfo.t)
      (cont : Simple.t -> Flambda.Expr.t) =
  match prim with
  | Simple s -> cont s
  | Prim p ->
    (* CR pchambart: find a better name, and fix the other ones *)
    let var = Variable.create "prim" in
    bind_rec var p dbg cont

let bind_primitive
      (var : Variable.t)
      (prim : expr_primitive)
      (dbg : Debuginfo.t)
      (cont : Flambda.Expr.t)
  : Flambda.Expr.t =
  bind_rec var prim dbg (fun _ -> cont)

let convert_lprim (prim : Lambda.primitive) (args : Simple.t list)
      (exception_continuation : Continuation.t)
  : expr_primitive =
  let args = List.map (fun arg : simple_or_prim -> Simple arg) args in
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

  (* Test checked *)

  (* | Pdivint Safe, [arg] -> *)
  (*   Binary (Int_arith (Flambda_kind.Standard_int.Tagged_immediate, Neg), arg) *)


  | ( Pfield _ | Pnegint | Psetfield _ ), _ ->
    Misc.fatal_errorf "Closure_conversion.convert_primitive: \
                       Wrong arrity for %a: %i"
      Printlambda.primitive prim (List.length args)
  | _ ->
    assert false

let () =
  ignore bind_primitive;
  ignore convert_lprim

(* let convert_and_bind *)
(*       (var : Variable.t) *)
(*       (prim : Lambda.primitive) *)
(*       (args : Simple.t list) *)
(*       (cont : Flambda.Expr.t) : Flambda.Expr.t = *)
*)
