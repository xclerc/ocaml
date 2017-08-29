(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2016 OCamlPro SAS                                    *)
(*   Copyright 2014--2016 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module type S = sig
  type t

  val simplify_unop
     : Lambda.primitive
    -> t Flambda_type.boxed_int
    -> Flambda.Named.t
    -> t
    -> Flambda.Named.t * Flambda_type.t * Inlining_cost.Benefit.t

  val simplify_binop
     : Lambda.primitive
    -> t Flambda_type.boxed_int
    -> Flambda.Named.t
    -> t
    -> t
    -> Flambda.Named.t * Flambda_type.t * Inlining_cost.Benefit.t

  val simplify_binop_int
     : Lambda.primitive
    -> t Flambda_type.boxed_int
    -> Flambda.Named.t
    -> t
    -> int
    -> size_int:int
    -> Flambda.Named.t * Flambda_type.t * Inlining_cost.Benefit.t
end
