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

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module T = Flambda_type0

module Make (Function_declarations : sig
  type t
  val print : Format.formatter -> t -> unit
end) = struct
  let import_set_of_closures =
    let aux set_of_closures_id =
      ignore (Compilenv.approx_for_global
        (Set_of_closures_id.get_compilation_unit set_of_closures_id));
      let ex_info = Compilenv.approx_env () in
      match
        Set_of_closures_id.Map.find set_of_closures_id
          ex_info.sets_of_closures
      with
      | exception Not_found -> None
      | function_decls -> Some function_decls
    in
    Set_of_closures_id.Tbl.memoize Compilenv.imported_sets_of_closures_table aux

  let rec import_ex ex =
    ignore (Compilenv.approx_for_global (Export_id.get_compilation_unit ex));
    let ex_info = Compilenv.approx_env () in
    let import_value_set_of_closures ~set_of_closures_id ~bound_vars
          ~(ex_info : Export_info.t) ~what : T.value_set_of_closures option =
      let bound_vars = Var_within_closure.Map.map import_approx bound_vars in
      match
        Set_of_closures_id.Map.find set_of_closures_id ex_info.invariant_params
      with
      | exception Not_found ->
        Misc.fatal_errorf "Set of closures ID %a not found in invariant_params \
            (when importing [%a: %s])"
          Set_of_closures_id.print set_of_closures_id
          Export_id.print ex
          what
      | invariant_params ->
        match import_set_of_closures set_of_closures_id with
        | None -> None
        | Some function_decls ->
          Some (T.create_value_set_of_closures
            ~function_decls
            ~bound_vars
            ~invariant_params:(lazy invariant_params)
            ~specialised_args:Variable.Map.empty
            ~freshening:Freshening.Project_var.empty
            ~direct_call_surrogates:Closure_id.Map.empty)
    in
    match Export_info.find_description ex_info ex with
    | exception Not_found -> T.value_unknown Other
    | Value_int i -> T.value_int i
    | Value_char c -> T.value_char c
    | Value_constptr i -> T.value_constptr i
    | Value_float f -> T.value_float f
    | Value_float_array float_array ->
      begin match float_array.contents with
      | Unknown_or_mutable ->
        T.value_mutable_float_array ~size:float_array.size
      | Contents contents ->
        T.value_immutable_float_array
          (Array.map (function
             | None -> T.value_any_float
             | Some f -> T.value_float f)
             contents)
      end
    | Export_info.Value_boxed_int (t, i) -> T.value_boxed_int t i
    | Value_string { size; contents } ->
      let contents =
        match contents with
        | Unknown_or_mutable -> None
        | Contents contents -> Some contents
      in
      T.value_string size contents
    | Value_mutable_block _ -> T.value_unknown Other
    | Value_block (tag, fields) ->
      T.value_block tag (Array.map import_approx fields)
    | Value_closure { closure_id;
          set_of_closures =
            { set_of_closures_id; bound_vars; aliased_symbol } } ->
      let value_set_of_closures =
        import_value_set_of_closures ~set_of_closures_id ~bound_vars ~ex_info
          ~what:(Format.asprintf "Value_closure %a" Closure_id.print closure_id)
      in
      begin match value_set_of_closures with
      | None ->
        T.value_unknown (Unresolved_value (Set_of_closures_id set_of_closures_id))
      | Some value_set_of_closures ->
        T.value_closure ?set_of_closures_symbol:aliased_symbol
          (Closure_id.Map.add closure_id value_set_of_closures
            Closure_id.Map.empty)
      end
    | Value_set_of_closures { set_of_closures_id; bound_vars; aliased_symbol } ->
      let value_set_of_closures =
        import_value_set_of_closures ~set_of_closures_id ~bound_vars ~ex_info
          ~what:"Value_set_of_closures"
      in
      match value_set_of_closures with
      | None ->
        T.value_unknown (Unresolved_value (Set_of_closures_id set_of_closures_id))
      | Some value_set_of_closures ->
        let approx = T.value_set_of_closures value_set_of_closures in
        match aliased_symbol with
        | None -> approx
        | Some symbol -> T.augment_with_symbol approx symbol

  and import_approx (ap : Export_info.approx) =
    match ap with
    | Value_unknown -> T.value_unknown Other
    | Value_id ex -> T.value_extern ex
    | Value_symbol sym -> T.value_symbol sym

  let import_symbol sym =
    if Compilenv.is_predefined_exception sym then
      T.value_unknown Other
    else
      let symbol_id_map =
        let global = Symbol.compilation_unit sym in
        (Compilenv.approx_for_global global).symbol_id
      in
      match Symbol.Map.find sym symbol_id_map with
      | approx -> T.augment_with_symbol (import_ex approx) sym
      | exception Not_found ->
        T.value_unknown (Unresolved_value (Symbol sym))

  (* Note for code reviewers: Observe that [really_import] iterates until
     the approximation description is fully resolved (or a necessary .cmx
     file is missing). *)

  let rec really_import (approx : T.descr) =
    match approx with
    | Extern ex -> really_import_ex ex
    | Symbol sym -> really_import_symbol sym
    | r -> r

  and really_import_ex ex =
    really_import (import_ex ex).descr

  and really_import_symbol sym =
    really_import (import_symbol sym).descr

  let really_import_approx (approx : Simple_value_approx.t) =
    T.replace_description approx (really_import approx.descr)
end
