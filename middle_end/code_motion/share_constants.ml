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

module CDV = Flambda_static.Constant_defining_value
module BF = Flambda_static.Constant_defining_value_block_field

let update_constant_for_sharing sharing_symbol_tbl const : CDV.t =
  let substitute_symbol sym =
    match Symbol.Tbl.find sharing_symbol_tbl sym with
    | exception Not_found -> sym
    | symbol -> symbol
  in
  match (const : Flambda_static.Constant_defining_value.t) with
  | Allocated_const const ->
    CDV.create_allocated_const const
  | Block (tag, fields) ->
    let subst_field (field : BF.t) : BF.t =
      match field with
      | Tagged_immediate _ -> field
      | Symbol sym ->
        Symbol (substitute_symbol sym)
    in
    let fields = List.map subst_field fields in
    CDV.create_block tag fields
  | Set_of_closures set_of_closures ->
    CDV.create_set_of_closures
      (Flambda.Set_of_closures.Mappers.map_symbols
        ~f:substitute_symbol set_of_closures)
  | Project_closure (sym, closure_id) ->
    CDV.create_project_closure (substitute_symbol sym) closure_id

let cannot_share (const : CDV.t) =
  match const with
  | Allocated_const ((Mutable_string _) | (Mutable_float_array _)) -> true
  | Allocated_const ((Boxed_float _) | (Boxed_int32 _) | (Boxed_int64 _)
      | (Boxed_nativeint _) | (Immutable_string _)
      | (Immutable_float_array _))
  | Set_of_closures _ | Project_closure _ | Block _ ->
    false

let share_definition constant_to_symbol_tbl sharing_symbol_tbl
      symbol def root_symbol =
  let def = update_constant_for_sharing sharing_symbol_tbl def in
  if cannot_share def || Symbol.equal symbol root_symbol then
    (* The symbol exported by the unit (root_symbol), cannot be removed
       from the module. We prevent it from being shared to avoid that. *)
    Some def
  else
    begin match CDV.Tbl.find constant_to_symbol_tbl def with
    | exception Not_found ->
      CDV.Tbl.add constant_to_symbol_tbl def symbol;
      Some def
    | equal_symbol ->
      Symbol.Tbl.add sharing_symbol_tbl symbol equal_symbol;
      None
    end

let share_constants (program : Flambda_static.Program.t) =
  let root_symbol = Flambda_static.Program.root_symbol program in
  let sharing_symbol_tbl = Symbol.Tbl.create 42 in
  let constant_to_symbol_tbl = CDV.Tbl.create 42 in
  let rec loop (program : Flambda_static.Program_body.t)
        : Flambda_static.Program_body.t =
    match program with
    | Let_symbol (symbol, def, program) ->
      begin match
        share_definition constant_to_symbol_tbl sharing_symbol_tbl symbol
          def root_symbol
      with
      | None ->
        loop program
      | Some def' ->
        Let_symbol (symbol, def', loop program)
      end
    | Let_rec_symbol (defs, program) ->
      let defs =
        List.map (fun (symbol, def) ->
            let def = update_constant_for_sharing sharing_symbol_tbl def in
            symbol, def)
          defs
      in
      Let_rec_symbol (defs, loop program)
    | Initialize_symbol (symbol, descr, program) ->
      let expr =
        Flambda.Expr.Mappers.map_symbols descr.expr ~f:(fun symbol ->
            try Symbol.Tbl.find sharing_symbol_tbl symbol with
            | Not_found -> symbol)
      in
      Initialize_symbol (symbol, { descr with expr; }, loop program)
    | Effect (expr, cont, program) ->
      let expr =
        Flambda.Expr.Mappers.map_symbols
          ~f:(fun symbol ->
              try Symbol.Tbl.find sharing_symbol_tbl symbol with
              | Not_found -> symbol)
          expr
      in
      Effect (expr, cont, loop program)
    | End root -> End root
  in
  { program with
    program_body = loop program.program_body;
  }
