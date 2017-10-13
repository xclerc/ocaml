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

module F0 = Flambda0

module Constant_defining_value_block_field = struct
  type t =
    | Symbol of Symbol.t
    | Tagged_immediate of Immediate.t

  let compare (t1 : t) (t2 : t) =
    match t1, t2 with
    | Symbol s1, Symbol s2 -> Symbol.compare s1 s2
    | Tagged_immediate t1, Tagged_immediate t2 -> Immediate.compare t1 t2
    | Symbol _, Tagged_immediate _ -> -1
    | Tagged_immediate _, Symbol _ -> 1

  let print ppf (field : t) =
    match field with
    | Symbol symbol -> Symbol.print ppf symbol
    | Tagged_immediate immediate -> Immediate.print ppf immediate
end

module Constant_defining_value = struct
  type t =
    | Allocated_const of Allocated_const.t
    | Block of Tag.Scannable.t * Constant_defining_value_block_field.t list
    | Set_of_closures of F0.Set_of_closures.t
    | Project_closure of Symbol.t * Closure_id.t

  include Identifiable.Make (struct
    type nonrec t = t

    let compare (t1 : t) (t2 : t) =
      match t1, t2 with
      | Allocated_const c1, Allocated_const c2 ->
        Allocated_const.compare c1 c2
      | Block (tag1, fields1), Block (tag2, fields2) ->
        let c = Tag.Scannable.compare tag1 tag2 in
        if c <> 0 then c
        else
          Misc.Stdlib.List.compare Constant_defining_value_block_field.compare
            fields1 fields2
      | Set_of_closures set1, Set_of_closures set2 ->
        Set_of_closures_id.compare set1.function_decls.set_of_closures_id
          set2.function_decls.set_of_closures_id
      | Project_closure (set1, closure_id1),
          Project_closure (set2, closure_id2) ->
        let c = Symbol.compare set1 set2 in
        if c <> 0 then c
        else Closure_id.compare closure_id1 closure_id2
      | Allocated_const _, Block _ -> -1
      | Allocated_const _, Set_of_closures _ -> -1
      | Allocated_const _, Project_closure _ -> -1
      | Block _, Allocated_const _ -> 1
      | Block _, Set_of_closures _ -> -1
      | Block _, Project_closure _ -> -1
      | Set_of_closures _, Allocated_const _ -> 1
      | Set_of_closures _, Block _ -> 1
      | Set_of_closures _, Project_closure _ -> -1
      | Project_closure _, Allocated_const _ -> 1
      | Project_closure _, Block _ -> 1
      | Project_closure _, Set_of_closures _ -> 1

    let equal t1 t2 =
      t1 == t2 || compare t1 t2 = 0

    let hash = Hashtbl.hash

    let print ppf (t : t) =
      let fprintf = Format.fprintf in
      match t with
      | Allocated_const const ->
        fprintf ppf "(Allocated_const %a)" Allocated_const.print const
      | Block (tag, []) ->
        fprintf ppf "(Empty block (tag %a))" Tag.Scannable.print tag
      | Block (tag, fields) ->
        fprintf ppf "(Block (tag %a, %a))"
          Tag.Scannable.print tag
          (Format.pp_print_list ~pp_sep:Format.pp_print_space
            Constant_defining_value_block_field.print) fields
      | Set_of_closures set_of_closures ->
        fprintf ppf "@[<2>(Set_of_closures (@ %a))@]"
          F0.Set_of_closures.print set_of_closures
      | Project_closure (set_of_closures, closure_id) ->
        fprintf ppf "(Project_closure (%a, %a))"
          Symbol.print set_of_closures
          Closure_id.print closure_id
  end)

  let create_allocated_const ac = Allocated_const ac

  let create_block tag fields = Block (tag, fields)

  let create_set_of_closures set =
    if not (F0.Set_of_closures.has_empty_environment set) then begin
      Misc.fatal_errorf "Cannot have set of closures with a non-empty \
          environment as static data: %a"
        F0.Set_of_closures.print set
    end;
    Set_of_closures set

  let create_project_closure sym closure_id = Project_closure (sym, closure_id)

  let free_symbols_helper symbols (const : t) =
    match const with
    | Allocated_const _ -> ()
    | Block (_, fields) ->
      List.iter
        (function
          | (Symbol s : Constant_defining_value_block_field.t) ->
            symbols := Symbol.Set.add s !symbols
          | (Tagged_immediate _ : Constant_defining_value_block_field.t) -> ())
        fields
    | Set_of_closures set_of_closures ->
      symbols := Symbol.Set.union !symbols
        (F0.Named.free_symbols (Set_of_closures set_of_closures))
    | Project_closure (s, _) ->
      symbols := Symbol.Set.add s !symbols

  module Mappers = struct
    let map_set_of_closures t ~f =
      match t with
      | Allocated_const _ | Block _ | Project_closure _ -> t
      | Set_of_closures set ->
        create_set_of_closures (f set)
  end
end

module Program_body = struct
  module Initialize_symbol = struct
    type t = {
      expr : Flambda0.Expr.t;
      return_cont : Continuation.t;
      return_arity : Flambda_arity.t;
    }
  end

  type t =
    | Let_symbol of Symbol.t * Constant_defining_value.t * t
    | Let_rec_symbol of (Symbol.t * Constant_defining_value.t) list * t
    | Initialize_symbol of Symbol.t * Initialize_symbol.t * t
    | Effect of F0.Expr.t * Continuation.t * t
    | End of Symbol.t

  let rec print ppf (program : t) =
    let fprintf = Format.fprintf in
    match program with
    | Let_symbol (symbol, constant_defining_value, body) ->
      let rec let_body (ul : t) =
        match ul with
        | Let_symbol (symbol, constant_defining_value, body) ->
          fprintf ppf "@ @[<2>(%a@ %a)@]" Symbol.print symbol
            Constant_defining_value.print constant_defining_value;
          let_body body
        | _ -> ul
      in
      fprintf ppf "@[<2>let_symbol@ @[<hv 1>(@[<2>%a@ %a@])@]@ "
        Symbol.print symbol
        Constant_defining_value.print constant_defining_value;
      let program = let_body body in
      fprintf ppf "@]@.";
      print ppf program
    | Let_rec_symbol (defs, program) ->
      let bindings ppf id_arg_list =
        let spc = ref false in
        List.iter
          (fun (symbol, constant_defining_value) ->
            if !spc then fprintf ppf "@ " else spc := true;
            fprintf ppf "@[<2>%a@ %a@]"
              Symbol.print symbol
              Constant_defining_value.print constant_defining_value)
          id_arg_list in
      fprintf ppf
        "@[<2>let_rec_symbol@ (@[<hv 1>%a@])@]@."
        bindings defs;
      print ppf program
    | Initialize_symbol (symbol, descr, program) ->
      fprintf ppf
        "@[<2>initialize_symbol@ @[<hv 1>(@[<2>%a@;@[<v>%a@]@])@]@]@."
        Symbol.print symbol
        Flambda.Expr.print descr.expr;
        (* CR mshinwell: Print continuation and arity *)
      print ppf program
    | Effect (expr, cont, program) ->
      fprintf ppf "@[effect @[<v 2><%a>:@. %a@]@]"
        Continuation.print cont
        F0.Expr.print expr;
      print ppf program;
    | End root -> fprintf ppf "End %a" Symbol.print root

  let free_symbols t =
    let symbols = ref Symbol.Set.empty in
    let rec loop (program : t) =
      match program with
      | Let_symbol (_, const, program) ->
        Constant_defining_value.free_symbols_helper symbols const;
        loop program
      | Let_rec_symbol (defs, program) ->
        List.iter (fun (_, const) ->
            Constant_defining_value.free_symbols_helper symbols const)
          defs;
        loop program
      | Initialize_symbol (_, descr, program) ->
        symbols := Symbol.Set.union !symbols (F0.Expr.free_symbols descr.expr);
        loop program
      | Effect (expr, _cont, program) ->
        symbols := Symbol.Set.union !symbols (F0.Expr.free_symbols expr);
        loop program
      | End symbol -> symbols := Symbol.Set.add symbol !symbols
    in
    loop t;
    !symbols
end

module Program = struct
  type t = {
    imported_symbols : Symbol.Set.t;
    program_body : Program_body.t;
  }

  let free_symbols (program : t) =
    (* Note that there is no need to count the [imported_symbols]. *)
    Program_body.free_symbols program.program_body

  let print ppf t =
    Symbol.Set.iter (fun symbol ->
        Format.fprintf ppf "@[import_symbol@ %a@]@." Symbol.print symbol)
      t.imported_symbols;
    Program_body.print ppf t.program_body
end
