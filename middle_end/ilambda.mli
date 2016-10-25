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

(* Once everything is finished, Ilambda will be in CPS form but not
   closure converted, whereas Flambda is CPS with closures.
*)

type t = private
  | Var of Ident.t
  | Const of Lambda.structured_constant
  | Function of function_declaration
  | Let of let_kind * value_kind * Ident.t * function_declaration * t
  | Let_rec of (Ident.t * t) list * t
  | Let_cont of t * int * Ident.t list * t
  | Apply of apply
  | Apply_cont of int * t list
  | Prim of primitive * t list * Location.t
  | Switch of t * switch
  | String_switch of t * (string * t) list * t option * Location.t
  | Try_with of t * Ident.t * t
  | If_then_else of t * t * t
  | Send of meth_kind * t * t * t list * Location.t
  | Event of t * Lambda.event

and function_decl =
  { kind: function_kind;
    params: Ident.t list;
    body: lambda;
    attr: function_attribute;
    loc : Location.t;
  }

and apply =
  { func : lambda;
    args : lambda list;
    loc : Location.t;
    should_be_tailcall : bool;
    inlined : inline_attribute;
    specialised : specialise_attribute;
  }

and switch =
  { numconsts: int;
    consts: (int * lambda) list;
    numblocks: int;
    blocks: (int * lambda) list;
    failaction : lambda option;
  }
