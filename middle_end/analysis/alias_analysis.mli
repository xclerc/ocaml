(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2017 OCamlPro SAS                                    *)
(*   Copyright 2014--2017 Jane Street Group LLC                           *)

(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

type allocation_point =
  | Symbol of Symbol.t
  | Variable of Variable.t

type allocated_const =
  | Normal of Allocated_const.t
  | Array of Lambda.array_kind * Asttypes.mutable_flag * Variable.t list
  | Duplicate_array of Lambda.array_kind * Asttypes.mutable_flag * Variable.t

type constant_project_var = {
  closure : Variable.t;
  closure_id : Closure_id.t;
  var : Var_within_closure.t;
}

type constant_defining_value =
  | Allocated_const of allocated_const
  | Block of Tag.t * Variable.t list
  | Set_of_closures of Flambda.Set_of_closures.t
  | Project_closure of Projection.Project_closure.t
  | Move_within_set_of_closures of Projection.Move_within_set_of_closures.t
  | Project_var of constant_project_var
  | Field of Variable.t * int
  | Symbol_field of Symbol.t * int
  | Const of Flambda.Const.t
  | Symbol of Symbol.t
  | Variable of Variable.t

type initialize_symbol_field = Variable.t option

(** Simple alias analysis working over information about which
    symbols have been assigned to variables; and which constants have
    been assigned to symbols.  The return value gives the assignment
    of the defining values of constants to variables.
    Also see comments for [Lift_constants], whose input feeds this
    pass.

    Variables found to be ill-typed accesses to other constants, for
    example arising from dead code, will be pointed at [the_dead_constant].
*)
val run
   : constant_defining_value Variable.Tbl.t
  -> initialize_symbol_field list Symbol.Tbl.t
  -> Flambda_static.Constant_defining_value.t Symbol.Tbl.t
  -> the_dead_constant:Symbol.t
  -> allocation_point Variable.Map.t

val print_constant_defining_value
   : Format.formatter
  -> constant_defining_value
  -> unit
