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
  | Let of Lambda.let_kind * Lambda.value_kind * Ident.t * named * t
  | Let_rec of (Ident.t * function_declaration) list * t
  | Let_cont of Continuation.t * Ident.t list * t (* <-- code of cont'n *) * t
  | Apply of apply
  | Apply_cont of Continuation.t * Ident.t list
  | Switch of Ident.t * switch
  | String_switch of Ident.t * (string * t) list * t option * Location.t
  | Try_with of t * Ident.t * t
  | Send of Lambda.meth_kind * t * t * t list * Location.t
  | Event of t * Lambda.lambda_event

and named =
  | Var of Ident.t
  | Const of Lambda.structured_constant
  | Function of function_declaration
  | Prim of Lambda.primitive * Ident.t list * Location.t

and function_declaration =
  { kind : Lambda.function_kind;
    continuation_param : Continuation.t;
    params : Ident.t list;
    body : t;
    attr : Lambda.function_attribute;
    loc : Location.t;
    free_idents_of_body : Lambda.IdentSet.t;
  }

and apply =
  { func : Ident.t;
    args : Ident.t list;
    continuation : Continuation.t;
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

val print : Format.formatter -> t -> unit
