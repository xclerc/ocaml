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

(** Operations on Flambda statically-allocated code and data whose
    implementations cannot break invariants enforced by the private types. *)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module Constant_defining_value
  : module type of Flambda_static0.Constant_defining_value

module Program_body : module type of Flambda_static0.Program_body

module Program : sig
  include module type of Flambda_static0.Program

  val initialize_symbols
     : t
    -> (Symbol.t * Tag.t * (Flambda.Expr.t * Continuation.t) list) list

  val imported_symbols : t -> Symbol.Set.t

  val needed_import_symbols : t -> Symbol.Set.t

  val introduce_needed_import_symbols : t -> t

  val root_symbol : t -> Symbol.t

  (** Creates a map from closure IDs to function declarations by iterating over
      all sets of closures in the given program. *)
  val make_closure_map : t -> Flambda.Function_declarations.t Closure_id.Map.t

  (** The definitions of all constants that have been lifted out to [Let_symbol]
      or [Let_rec_symbol] constructions. *)
  val all_lifted_constants : t -> (Symbol.t * Constant_defining_value.t) list

  (** Like [all_lifted_constant_symbols], but returns a map instead of a
      list. *)
  val all_lifted_constants_as_map : t -> Constant_defining_value.t Symbol.Map.t

  (** The identifiers of all constant sets of closures that have been lifted out
      to [Let_symbol] or [Let_rec_symbol] constructions. *)
  val all_lifted_constant_sets_of_closures : t -> Set_of_closures_id.Set.t

  (** All sets of closures in the given program (whether or not bound to a
      symbol.) *)
  val all_sets_of_closures : t -> Flambda.Set_of_closures.t list

  val all_sets_of_closures_map
     : t
    -> Flambda.Set_of_closures.t Set_of_closures_id.Map.t

  val all_function_decls_indexed_by_set_of_closures_id
     : t
    -> Flambda.Function_declarations.t Set_of_closures_id.Map.t

  val all_function_decls_indexed_by_closure_id
     : t
    -> Flambda.Function_declarations.t Closure_id.Map.t
end
