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

(** Ilambda: halfway between Lambda and Flambda.  In CPS but without closures.
    Used only as an internal language for communication between the CPS and
    closure conversion passes. *)

[@@@ocaml.warning "+a-4-9-30-40-41-42-49"]

type trap_action =
  | Push of { id : Trap_id.t; exn_handler : Continuation.t; }
  | Pop of { id : Trap_id.t; exn_handler : Continuation.t; }

type t =
  | Let of Ident.t * named * t
  | Let_mutable of let_mutable
  | Let_rec of (Ident.t * function_declaration) list * t
  | Let_cont of let_cont
  | Apply of apply
  | Apply_cont of Continuation.t * trap_action option * Ident.t list
  | Switch of Ident.t * switch
  | Event of t * Lambda.lambda_event

and named =
  | Var of Ident.t
  | Const of Lambda.structured_constant
  | Prim of Lambda.primitive * Ident.t list * Location.t
  | Assign of { being_assigned : Ident.t; new_value : Ident.t; }

and let_mutable = {
  id : Ident.t;
  initial_value : Ident.t;
  contents_kind : Lambda.value_kind;
  body : t;
}

and function_declaration =
  { kind : Lambda.function_kind;
    continuation_param : Continuation.t;
    params : Ident.t list;
    body : t;
    attr : Lambda.function_attribute;
    loc : Location.t;
    free_idents_of_body : Lambda.IdentSet.t;
    stub : bool;
  }

and let_cont = {
  name : Continuation.t;
  administrative : bool;
  is_exn_handler : bool;
  (** If the continuation is an exception handler, it must not be marked as
      [administrative].
      Continuations that are exception handlers must be [Nonrecursive] and
      have exactly one parameter. *)
  params : Ident.t list;
  recursive : Asttypes.rec_flag;
  body : t;
  handler : t;
}

and apply =
  { kind : apply_kind;
    func : Ident.t;
    args : Ident.t list;
    continuation : Continuation.t;
    loc : Location.t;
    should_be_tailcall : bool;
    inlined : Lambda.inline_attribute;
    specialised : Lambda.specialise_attribute;
  }

and apply_kind =
  | Function
  | Method of { kind : Lambda.meth_kind; obj : Ident.t; }

(** Tag block switches must be encoded as [Pgettag] followed by a switch
    on constants.  String switches must be expanded out. *)
and switch =
  { numconsts : int;
    consts : (int * Continuation.t) list;
    failaction : Continuation.t option;
  }

val print : Format.formatter -> t -> unit
