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

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

type t

include Identifiable with type t := t

val create : A.t -> t option

type how_to_unbox = {
  wrapper_param_being_unboxed : Variable.t;
  bindings_in_wrapper : Flambda.expr Variable.Map.t;
  new_arguments_for_call_in_wrapper : Variable.t list;
  new_params : Variable.t list;
  new_projections : Projection.t list;
  wrap_body : Flambda.expr -> Flambda.expr;
}

val how_to_unbox : t -> being_unboxed:Variable.t -> how_to_unbox
