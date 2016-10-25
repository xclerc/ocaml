(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2016 OCamlPro SAS                                          *)
(*   Copyright 2016 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(** Ilambda: halfway between Lambda and Flambda.  Used only as an internal
    language for communication between the CPS and closure conversion
    passes. *)

[@@@ocaml.warning "+a-4-9-30-40-41-42-49"]

(* Once everything is finished, Ilambda will be in CPS form but not
   closure converted, whereas Flambda is CPS with closures.
*)

type t =
  | Var of Ident.t
  | Const of Lambda.structured_constant
  | Function of function_declaration
  | Let of Lambda.let_kind * Lambda.value_kind * Ident.t * t * t
  | Let_rec of (Ident.t * t) list * t
  | Let_cont of t * int * Ident.t list * t
  | Apply of apply
  | Apply_cont of int * t list
  | Prim of Lambda.primitive * t list * Location.t
  | Switch of t * switch
  | String_switch of t * (string * t) list * t option * Location.t
  | Try_with of t * Ident.t * t
  | If_then_else of t * t * t
  | Send of Lambda.meth_kind * t * t * t list * Location.t
  | Event of t * Lambda.lambda_event

and function_declaration =
  { kind : Lambda.function_kind;
    params : Ident.t list;
    body : t;
    attr : Lambda.function_attribute;
    loc : Location.t;
  }

and apply =
  { func : t;
    args : t list;
    loc : Location.t;
    should_be_tailcall : bool;
    inlined : Lambda.inline_attribute;
    specialised : Lambda.specialise_attribute;
  }

and switch =
  { numconsts : int;
    consts : (int * t) list;
    numblocks : int;
    blocks : (int * t) list;
    failaction : t option;
  }
