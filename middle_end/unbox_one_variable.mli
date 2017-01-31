(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2017 OCamlPro SAS                                          *)
(*   Copyright 2017 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(** Given a variable and its approximation, devise a strategy to unbox it. *)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module How_to_unbox : sig
  type t = private {
    being_unboxed_to_wrapper_params_being_unboxed : Variable.t Variable.Map.t;
    bindings_in_wrapper : Flambda.expr Variable.Map.t;
    new_arguments_for_call_in_wrapper : Variable.t list;
    new_params : Variable.t list;
    new_projections : Projection.t list;
    wrap_body : Flambda.expr -> Flambda.expr;
  }

  val merge : t -> t -> t

  val merge_variable_map : t Variable.Map.t -> t

  val add_bindings_in_wrapper : t -> Flambda.expr -> Flambda.expr
  val wrap_body : t -> Flambda.expr -> Flambda.expr
end

val how_to_unbox
  -> being_unboxed:Variable.t
  -> being_unboxed_approx:Simple_value_approx.t
  -> How_to_unbox.t option
