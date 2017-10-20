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
    | Dynamically_computed v1, Dynamically_computed v2 -> Variable.compare v1 v2
    | Symbol _, Tagged_immediate _ -> -1
    | Tagged_immediate _, Symbol _ -> 1
    | Symbol _, Dynamically_computed _ -> -1
    | Dynamically_computed _, Symbol _ -> 1
    | Tagged_immediate _, Dynamically_computed _ -> -1
    | Dynamically_computed _, Tagged_immediate _ -> 1

  let print ppf (field : t) =
    match field with
    | Symbol symbol -> Symbol.print ppf symbol
    | Tagged_immediate immediate -> Immediate.print ppf immediate
    | Dynamically_computed var -> Variable.print ppf var

  let needs_gc_root t =
    match t with
    | Symbol _ | Tagged_immediate _ -> false
    | Dynamically_computed _ -> true

  let free_symbols t =
    match t with
    | Symbol sym -> Symbol.Set.singleton sym
    | Tagged_immediate _ | Dynamically_computed _ -> Symbol.Set.empty
end

module Static_part = struct
  type 'a or_variable =
    | Const of 'a
    | Var of Variable.t

  type t = private
    | Block of Tag.Scannable.t * Asttypes.mutable_flag * (Of_kind_value.t list)
    | Set_of_closures of Flambda0.Set_of_closures.t
    | Closure of Symbol.t * Closure_id.t
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
    | Closure _
    | Boxed_float _
    | Boxed_int32 _
    | Boxed_int64 _
    | Boxed_nativeint _
    | Mutable_float_array _
    | Immutable_float_array _
    | Mutable_string _
    | Immutable_string _ -> false

  let free_symbols t =
    match t with
    | Block (_tag, _mut, fields) ->
      List.fold_left (fun syms field ->
          Symbol.Set.union syms (Of_kind_value.free_symbols field))
        Symbol.Set.empty
        fields
    | Closure (sym, ) -> Symbol.Set.singleton sym
    | Set_of_closures _
    | Boxed_float _
    | Boxed_int32 _
    | Boxed_int64 _
    | Boxed_nativeint _
    | Mutable_float_array _
    | Immutable_float_array _
    | Mutable_string _
    | Immutable_string _ -> Symbol.Set.empty

  let print ppf (t : t) =
    let fprintf = Format.fprintf in
    let print_float_array_field ppf = function
      | Const f -> fprintf ppf "%f" f
      | Var v -> Variable.print ppf v
    in
    match t with
    | Block (tag, mut, fields) ->
      fprintf ppf "@[(%sblock [%a: %a])@]"
        (match mut with Immutable -> "Immutable_" | Mutable -> "Mutable_")
        Tag.Scannable.print tag
        (Format.pp_print_list ~pp_sep:Format.pp_print_space
          Of_kind_value.print) fields
    | Set_of_closures set_of_closures ->
      fprintf ppf "@[(Set_of_closures@ (%a))@]"
        F0.Set_of_closures.print set_of_closures
    | Closure (set_of_closures, closure_id) ->
      fprintf ppf "@[(Closure (%a).%a))@]"
        Symbol.print set_of_closures
        Closure_id.print closure_id
    | Boxed_float (Const f) ->
      fprintf ppf "@[(Boxed_float %f)@]" f
    | Boxed_float (Var v) ->
      fprintf ppf "@[(Boxed_float %a)@]" Variable.print v
    | Boxed_int32 (Const n) ->
      fprintf ppf "@[(Boxed_int32 %ld)@]" n
    | Boxed_int32 (Var v) ->
      fprintf ppf "@[(Boxed_int32 %a)@]" Variable.print v
    | Boxed_int64 (Const n) ->
      fprintf ppf "@[(Boxed_int64 %ld)@]" n
    | Boxed_int64 (Var v) ->
      fprintf ppf "@[(Boxed_int64 %a)@]" Variable.print v
    | Boxed_nativeint (Const n) ->
      fprintf ppf "@[(Boxed_nativeint %ld)@]" n
    | Boxed_nativeint (Var v) ->
      fprintf ppf "@[(Boxed_nativeint %a)@]" Variable.print v
    | Mutable_float_array { initial_value; } ->
      fprintf ppf "@[(Mutable_float_array@ @[[| %a |]@])@]"
        (Format.pp_print_list
           ~pp_sep:(fun ppf () -> Format.pp_print_string ppf "@[; @]")
           print_float_array_field)
        initial_value
    | Immutable_float_array fields ->
      fprintf ppf "@[(Immutable_float_array@ @[[| %a |]@])@]"
        (Format.pp_print_list
           ~pp_sep:(fun ppf () -> Format.pp_print_string ppf "@[; ")
           print_float_array_field)
        initial_value
    | Mutable_string { initial_value; } ->
      fprintf ppf "@[(Mutable_string@ \"%s\")@]" initial_value
    | Immutable_string s ->
      fprintf ppf "@[(Immutable_string@ \"%s\")@]" s

  module Mappers = struct
    let map_set_of_closures t ~f =
      match t with
      | Set_of_closures set -> Set_of_closures (f set)
      | Block _
      | Closure _
      | Boxed_float _
      | Boxed_int32 _
      | Boxed_int64 _
      | Boxed_nativeint _
      | Mutable_float_array _
      | Immutable_float_array _
      | Mutable_string _
      | Immutable_string _ -> t
  end
end

module Program_body = struct
  type computation = {
    expr : Expr.t;
    return_cont : Continuation.t;
    computed_values : (Variable.t * Flambda_kind.t) list;
  }

  let print_computation ppf comp =
    Format.fprintf "@[(\
        @[(expr@ %a)@]@ \
        @[(return_cont@ %a)@]@ \
        @[(computed_values@ @[(%a)@])@])@]"
      Flambda.Expr.print comp.expr
      Continuation.print comp.return_cont
      (Format.pp_print_list ~pp_sep:Format.pp_print_space
        (fun ppf (var, kind) ->
          Format.fprintf "@[(%a :: %a)@]"
            Variable.print var
            Flambda_kind.print kind)
      comp.computed_values

  let free_symbols_of_computation comp = Flambda.Expr.free_symbols comp.expr

  type definition = {
    computation : computation option;
    static_structure : (Symbol.t * Static_part.t) list;
  }

  let print_definition ppf defn =
    Format.fprintf "@[(\
        @[(computation@ %a)@]@ \
        @[(static_structure@ @[(%a)@])@])@]"
      (Misc.Stdlib.Option.print print_computation)
      defn.computation
      (Format.pp_print_list ~pp_sep:Format.pp_print_space
        (fun (sym, static_part) ->
          Format.fprintf ppf "@[(%a@ %a)@]"
            Symbol.print sym
            Static_part.print static_part))
      defn.static_structure

  let free_symbols_of_definition defn (recursive : Asttypes.rec_flag) =
    let free_in_computation =
      match defn.computation with
      | None -> Symbol.Set.empty
      | Some computation -> free_symbols_of_computation computation
    in
    let being_defined =
      Symbol.Set.of_list (List.map (fun (sym, _) -> sym) defn.static_structure)
    in
    let bound_recursively =
      match recursive with
      | Nonrecursive -> Symbol.Set.empty
      | Recursive -> being_defined
    in
    let free_in_static_parts =
      let symbols =
        List.fold_left (fun syms (_sym, static_part) ->
            Symbol.Set.union syms (Static_part.free_symbols static_part))
          Symbol.Set.empty
          defn.static_structure
      in
      Symbol.Set.diff symbols bound_recursively
    in
    Symbol.Set.union free_in_computation free_in_static_parts

  type t =
    | Define_symbol of definition * t
    | Define_symbol_rec of definition * t
    | Root of Symbol.t

  let rec print ppf t =
    match t with
    | Define_symbol (defn, t) ->
      Format.fprintf ppf "@[(Define_symbol@ %a)@]@;"
        print_definition defn;
      print ppf t
    | Define_symbol_rec (defn, t) ->
      Format.fprintf ppf "@[(Define_symbol_rec@ %a)@]@;"
        print_definition defn;
      print ppf t
    | Root sym ->
      Format.fprint ppf "@[(Root %a)@]" Symbol.print sym

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

  let rec free_symbols t =
    match t with
    | Define_symbol (defn, t) | Define_symbol_rec (defn, t) ->
      Symbol.Set.union (free_symbols_of_definition defn) (free_symbols t)
    | Root sym -> Symbol.Set.singleton sym
end

module Program = struct
  type t = {
    imported_symbols : Symbol.Set.t;
    body : Program_body.t;
  }

  let gc_roots t = Program_body.gc_roots t.body

  let free_symbols (program : t) =
    (* Note that there is no need to count the [imported_symbols]. *)
    Program_body.free_symbols program.program_body

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
*)
end
