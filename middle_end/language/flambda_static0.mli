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

(** Flambda language terms that represent statically-allocated objects
    (lifted closed functions, constants, etc). *)

type t =

module Field_of_kind_value : sig
  type t =
    | Symbol of Symbol.t
    | Tagged_immediate of Immediate.t
    | Dynamically_computed of Variable.t
end

module Static_part : sig
  type t = private
    | Block of Tag.Scannable.t * (Of_kind_value.t list)
    | Set_of_closures of Flambda0.Set_of_closures.t
    | Project_closure of Symbol.t * Closure_id.t
    | Boxed_float of float or_variable
    | Boxed_int32 of Int32.t or_variable
    | Boxed_int64 of Int64.t or_variable
    | Boxed_nativeint of Targetint.t or_variable
    | Mutable_float_array of { initial_value : float or_variable list; }
    | Immutable_float_array of float or_variable list
    | Mutable_string of { initial_value : string or_variable; }
    | Immutable_string of string or_variable

(*
  include Identifiable.S with type t := t

  val create_allocated_const : Allocated_const.t -> t

  val create_block
     : Tag.Scannable.t
    -> Block_field.t list
    -> t

  val create_set_of_closures : Flambda0.Set_of_closures.t -> t

  val create_project_closure : Symbol.t -> Closure_id.t -> t

  val tag : t -> Tag.t

  module Mappers : sig
    val map_set_of_closures
       : t
      -> f:(Flambda0.Set_of_closures.t -> Flambda0.Set_of_closures.t)
      -> t
  end
*)
end

(** A "program" is the contents of one compilation unit.  It describes the
    various values that are assigned to symbols (and in some cases fields of
    such symbols) in the object file.  As such, it is closely related to
    the compilation of toplevel modules. *)
module Program : sig
  type computation = {
    expr : Expr.t;
    return_cont : Continuation.t;
    computed_values : (Variable.t * Flambda_kind.t) list;
  }

  type definition = {
    static_structure : (Symbol.t * Static_part.t) list;
    computation : computation option;
  }

  type definition_group = {
    recursive : Asttypes.rec_flag;
    definitions : definition list;
  }

  type t = {
    imported_symbols : Symbol.Set.t;
    definitions : definition_group list;
    root_symbol : Symbol.t;
  }

  val free_symbols : t -> Symbol.Set.t

  val print : Format.formatter -> t -> unit
end
