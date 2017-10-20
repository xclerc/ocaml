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

module Of_kind_value = struct
  type t =
    | Symbol of Symbol.t
    | Tagged_immediate of Immediate.t
    | Dynamically_computed of Variable.t

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

  let needs_gc_root t =
    match t with
    | Symbol _ | Tagged_immediate _ -> false
    | Dynamically_computed _ -> true
end

module Static_part = struct
  type 'a or_variable =
    | Const of 'a
    | Var of Variable.t

  type t = private
    | Block of Tag.Scannable.t * Asttypes.mutable_flag * (Of_kind_value.t list)
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

  let needs_gc_root t =
    match t with
    | Block (tag, mut, fields) ->
      begin match mut with
      | Mutable -> true
      | Immutable -> List.exists Of_kind_value.needs_gc_root fields
      end
    | Set_of_closures set ->
      not (Var_within_closure.Map.is_empty set.free_vars)
    | Project_closure _
    | Boxed_float _
    | Boxed_int32 _
    | Boxed_int64 _
    | Boxed_nativeint _
    | Mutable_float_array _
    | Immutable_float_array _
    | Mutable_string _
    | Immutable_string _ -> false

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

(*
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
*)

  module Mappers = struct
    let map_set_of_closures t ~f =
      match t with
      | Allocated_const _ | Block _ | Project_closure _ -> t
      | Set_of_closures set ->
        create_set_of_closures (f set)
  end
end

module Program_body = struct
  type computation = {
    expr : Expr.t;
    return_cont : Continuation.t;
    computed_values : (Variable.t * Flambda_kind.t) list;
  }

  type definition = {
    static_structure : (Symbol.t * Static_part.t) list;
    computation : computation option;
  }

  type t =
    | Define_symbol of definition * t
    | Define_symbol_rec of definition * t
    | Root of Symbol.t

  let gc_roots t =
    let rec gc_roots t roots =
      match t with
      | Root _ -> roots
      | Define_symbol (defn, t) | Define_symbol_rec (defn, t) ->
        List.fold (fun roots (sym, static_part) ->
            if Static_part.needs_gc_root static_part then
              Symbol.Set.add sym roots
            else
              roots)
          roots
          defn
    in
    gc_roots t Symbol.Set.empty

(*
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
*)
end

module Program = struct
  type t = {
    imported_symbols : Symbol.Set.t;
    body : Program_body.t;
  }

  let gc_roots t = Program_body.gc_roots t.body


(*
  let declare_simple t static_part =
    let symbol = Symbol.create "boxed_float" in
    let definition =
      { static_structure = [symbol, static_part];
        computation = None;
      }
    in
    let definition_group =
      { recursive = Nonrecursive;
        definitions = [definition];
      }
    in
    { t with
      definitions = definition_group :: t.definitions;
    }

  let declare_boxed_float t f = declare_simple t (Boxed_float (Const f))
  let declare_boxed_int32 t n = declare_simple t (Boxed_int32 (Const n))
  let declare_boxed_int64 t n = declare_simple t (Boxed_int64 (Const n))
  let declare_boxed_nativeint t n = declare_simple t (Boxed_nativeint (Const n))

  let declare_immutable_string t s =
    declare_simple t (Immutable_string (Const s))

  let declare_mutable_string t ~initial_value =
    declare_simple t (Immutable_string (Const { initial_value; }))

  let declare_float_array t fs =
    let fs = List.map (fun f : _ or_variable -> Const f) fs in
    declare_simple t (Immutable_float_array fs)

  let declare_block t tag fields =
    let fields = List.map (fun s : Field_of_kind_value.t -> Symbol s) fields in
    declare_simple t (Block (tag, fields))

  let declare_single_field_block_pointing_at t thing kind =
    let field : Field_of_kind_value.t = Dynamically_computed thing in
    declare_simple t (Block (Tag.Scannable.zero, [field]))

  let free_symbols (program : t) =
    (* Note that there is no need to count the [imported_symbols]. *)
    Program_body.free_symbols program.program_body

  let print ppf t =
    Symbol.Set.iter (fun symbol ->
        Format.fprintf ppf "@[import_symbol@ %a@]@." Symbol.print symbol)
      t.imported_symbols;
    Program_body.print ppf t.program_body
*)
end
