(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-30-40-41-42"]

type t

val invariant : t -> unit

val print : Format.formatter -> t -> unit

val create : resolver:(Export_id.t -> Type_grammar.t option) -> t

val create_using_resolver_and_symbol_bindings_from : t -> t

val resolver : t -> (Export_id.t -> Type_grammar.t option)

val current_scope : t -> Scope.t

val increment_scope : t -> t

val add_definition : t -> Name_in_binding_pos.t -> Flambda_kind.t -> t

(** The caller is to ensure that the supplied type is the most precise
    available for the given name. *)
val add_equation : t -> Name.t -> Type_grammar.t -> t

val add_definitions_of_params : t -> params:Kinded_parameter.t list -> t

val add_symbol_definition : t -> Symbol.t -> t

val add_symbol_definitions : t -> Symbol.Set.t -> t

val add_equations_on_params
   : t
  -> params:Kinded_parameter.t list
  -> param_types:Type_grammar.t list
  -> t

val find : t -> Name.t -> Type_grammar.t

val find_params : t -> Kinded_parameter.t list -> Type_grammar.t list

val mem : t -> Name.t -> bool

val mem_simple : t -> Simple.t -> bool

val add_cse
   : t
  -> Flambda_primitive.Eligible_for_cse.t
  -> bound_to:Simple.t
  -> t

val find_cse
   : t
  -> Flambda_primitive.Eligible_for_cse.t
  -> Simple.t option

val add_env_extension_from_level
   : t
  -> Typing_env_level.t
  -> t

(* CR mshinwell: clarify that this does not meet *)
(* CR vlaviron: If the underlying level in the extension defines several
   variables, then there is no guarantee that the binding order in the result
   will match the binding order used to create the level. If they don't match,
   then adding equations in the wrong order can make equations disappear. *)
val add_env_extension
   : t
  -> Typing_env_extension.t
  -> t

val get_canonical_simple_exn
   : t
  -> ?min_name_mode:Name_mode.t
  -> Simple.t
  -> Simple.t

val get_canonical_simple_with_kind_exn
   : t
  -> ?min_name_mode:Name_mode.t
  -> Simple.t
  -> Simple.t * Flambda_kind.t

val get_alias_then_canonical_simple_exn
   : t
  -> ?min_name_mode:Name_mode.t
  -> Type_grammar.t
  -> Simple.t

val aliases_of_simple
   : t
  -> min_name_mode:Name_mode.t
  -> Simple.t
  -> Simple.Set.t

val aliases_of_simple_allowable_in_types : t -> Simple.t -> Simple.Set.t

val add_to_code_age_relation : t -> newer:Code_id.t -> older:Code_id.t -> t

val code_age_relation : t -> Code_age_relation.t

val with_code_age_relation : t -> Code_age_relation.t -> t

(* CR mshinwell: Consider labelling arguments e.g. [definition_typing_env] *)
val cut_and_n_way_join
   : t
  -> (t * Apply_cont_rewrite_id.t * Continuation_use_kind.t) list
  -> params:Kinded_parameter.t list
  -> unknown_if_defined_at_or_later_than:Scope.t
  -> Typing_env_extension.t * Continuation_extra_params_and_args.t

val free_names_transitive : t -> Type_grammar.t -> Name_occurrences.t

val defined_symbols : t -> Symbol.Set.t

val substitute_depths : t -> Simple.t -> Simple.t
