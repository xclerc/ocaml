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

module Make (Function_declarations : sig
  type t
  val print : Format.formatter -> t -> unit
end) = struct
  type value_string_contents =
    | Contents of string
    | Unknown_or_mutable

  type value_string = {
    contents : value_string_contents;
    size : int;
  }

  type value_float_array_contents =
    | Contents of float option array
    | Unknown_or_mutable

  type value_float_array = {
    contents : value_float_array_contents;
    size : int;
  }

  type descr =
    | Untagged_immediate of Immediate.t
    | Unboxed_float of float
    | Unboxed_int32 of Int32.t
    | Unboxed_int64 of Int64.t
    | Unboxed_nativeint of Nativeint.t
    | Tagged_immediate of Immediate.t
    | Boxed_float of float
    | Boxed_int32 of Int32.t
    | Boxed_int64 of Int64.t
    | Boxed_nativeint of Nativeint.t
    | Block of Tag.Scannable.t * approx array
    | Mutable_block of Tag.Scannable.t * int
    | Closure of value_closure
    | Set_of_closures of value_set_of_closures
    | String of value_string
    | Float_array of value_float_array

  and value_closure = {
    closure_id : Closure_id.t;
    set_of_closures : value_set_of_closures;
  }

  and value_set_of_closures = {
    set_of_closures_id : Set_of_closures_id.t;
    bound_vars : approx Var_within_closure.Map.t;
    results : approx list Closure_id.Map.t;
    aliased_symbol : Symbol.t option;
  }

  and approx =
    | Unknown
    | Id of Export_id.t
    | Symbol of Symbol.t

  let equal_approx (a1:approx) (a2:approx) =
    match a1, a2 with
    | Unknown, Unknown ->
      true
    | Id id1, Id id2 ->
      Export_id.equal id1 id2
    | Symbol s1, Symbol s2 ->
      Symbol.equal s1 s2
    | (Unknown | Symbol _ | Id _),
      (Unknown | Symbol _ | Id _) ->
      false

  let equal_approx_list a1s a2s =
    try List.for_all2 equal_approx a1s a2s
    with Invalid_argument _ -> false

  let join_approx (a1 : approx) (a2 : approx) : approx =
    if equal_approx a1 a2 then a1
    else Unknown

  let equal_array eq a1 a2 =
    Array.length a1 = Array.length a2 &&
    try
      Array.iteri (fun i v1 -> if not (eq a2.(i) v1) then raise Exit) a1;
      true
    with Exit -> false

  let equal_option eq o1 o2 =
    match o1, o2 with
    | None, None -> true
    | Some v1, Some v2 -> eq v1 v2
    | Some _, None | None, Some _ -> false

  let equal_set_of_closures (s1:value_set_of_closures)
        (s2:value_set_of_closures) =
    Set_of_closures_id.equal s1.set_of_closures_id s2.set_of_closures_id &&
    Var_within_closure.Map.equal equal_approx s1.bound_vars s2.bound_vars &&
    Closure_id.Map.equal equal_approx_list s1.results s2.results &&
    equal_option Symbol.equal s1.aliased_symbol s2.aliased_symbol

  let equal_descr (d1:descr) (d2:descr) : bool =
    match d1, d2 with
    | Block (t1, f1), Block (t2, f2) ->
      Tag.equal t1 t2 && equal_array equal_approx f1 f2
    | Mutable_block (t1, s1), Mutable_block (t2, s2) ->
      Tag.equal t1 t2 &&
      s1 = s2
    | Int i1, Int i2 ->
      i1 = i2
    | Char c1, Char c2 ->
      c1 = c2
    | Constptr i1, Constptr i2 ->
      i1 = i2
    | Float f1, Float f2 ->
      f1 = f2
    | Float_array s1, Float_array s2 ->
      s1 = s2
    | Boxed_int (t1, v1), Boxed_int (t2, v2) ->
      Simple_value_approx.equal_boxed_int t1 v1 t2 v2
    | String s1, String s2 ->
      s1 = s2
    | Closure c1, Closure c2 ->
      Closure_id.equal c1.closure_id c2.closure_id &&
      equal_set_of_closures c1.set_of_closures c2.set_of_closures
    | Set_of_closures s1, Set_of_closures s2 ->
      equal_set_of_closures s1 s2
    | ( Block (_, _) | Mutable_block (_, _) | Int _
      | Char _ | Constptr _ | Float _ | Float_array _
      | Boxed_int _ | String _ | Closure _
      | Set_of_closures _ ),
      ( Block (_, _) | Mutable_block (_, _) | Int _
      | Char _ | Constptr _ | Float _ | Float_array _
      | Boxed_int _ | String _ | Closure _
      | Set_of_closures _ ) ->
      false

  type t = {
    sets_of_closures : Flambda.Function_declarations.t Set_of_closures_id.Map.t;
    closures : Flambda.Function_declarations.t Closure_id.Map.t;
    values : descr Export_id.Map.t Compilation_unit.Map.t;
    symbol_id : Export_id.t Symbol.Map.t;
    offset_fun : int Closure_id.Map.t;
    offset_fv : int Var_within_closure.Map.t;
    constant_sets_of_closures : Set_of_closures_id.Set.t;
    invariant_params : Variable.Set.t Variable.Map.t Set_of_closures_id.Map.t;
  }

  let empty : t = {
    sets_of_closures = Set_of_closures_id.Map.empty;
    closures = Closure_id.Map.empty;
    values = Compilation_unit.Map.empty;
    symbol_id = Symbol.Map.empty;
    offset_fun = Closure_id.Map.empty;
    offset_fv = Var_within_closure.Map.empty;
    constant_sets_of_closures = Set_of_closures_id.Set.empty;
    invariant_params = Set_of_closures_id.Map.empty;
  }

  let create ~sets_of_closures ~closures ~values ~symbol_id
        ~offset_fun ~offset_fv ~constant_sets_of_closures
        ~invariant_params =
    { sets_of_closures;
      closures;
      values;
      symbol_id;
      offset_fun;
      offset_fv;
      constant_sets_of_closures;
      invariant_params;
    }

  let add_clambda_info t ~offset_fun ~offset_fv ~constant_sets_of_closures =
    assert (Closure_id.Map.cardinal t.offset_fun = 0);
    assert (Var_within_closure.Map.cardinal t.offset_fv = 0);
    assert (Set_of_closures_id.Set.cardinal t.constant_sets_of_closures = 0);
    { t with offset_fun; offset_fv; constant_sets_of_closures; }

  let merge (t1 : t) (t2 : t) : t =
    let eidmap_disjoint_union ?eq map1 map2 =
      Compilation_unit.Map.merge (fun _id map1 map2 ->
          match map1, map2 with
          | None, None -> None
          | None, Some map
          | Some map, None -> Some map
          | Some map1, Some map2 ->
            Some (Export_id.Map.disjoint_union ?eq map1 map2))
        map1 map2
    in
    let int_eq (i : int) j = i = j in
    { values = eidmap_disjoint_union ~eq:equal_descr t1.values t2.values;
      sets_of_closures =
        Set_of_closures_id.Map.disjoint_union t1.sets_of_closures
          t2.sets_of_closures;
      closures = Closure_id.Map.disjoint_union t1.closures t2.closures;
      symbol_id = Symbol.Map.disjoint_union ~print:Export_id.print t1.symbol_id t2.symbol_id;
      offset_fun = Closure_id.Map.disjoint_union
          ~eq:int_eq t1.offset_fun t2.offset_fun;
      offset_fv = Var_within_closure.Map.disjoint_union
          ~eq:int_eq t1.offset_fv t2.offset_fv;
      constant_sets_of_closures =
        Set_of_closures_id.Set.union t1.constant_sets_of_closures
          t2.constant_sets_of_closures;
      invariant_params =
        Set_of_closures_id.Map.disjoint_union
          ~print:(Variable.Map.print Variable.Set.print)
          ~eq:(Variable.Map.equal Variable.Set.equal)
          t1.invariant_params t2.invariant_params;
    }

  let find_value eid map =
    let unit_map =
      Compilation_unit.Map.find (Export_id.get_compilation_unit eid) map
    in
    Export_id.Map.find eid unit_map

  let find_description (t : t) eid =
    find_value eid t.values

  let nest_eid_map map =
    let add_map eid v map =
      let unit = Export_id.get_compilation_unit eid in
      let m =
        try Compilation_unit.Map.find unit map
        with Not_found -> Export_id.Map.empty
      in
      Compilation_unit.Map.add unit (Export_id.Map.add eid v m) map
    in
    Export_id.Map.fold add_map map Compilation_unit.Map.empty

  let print_approx ppf ((t,root_symbols) : t * Symbol.t list) =
    let values = t.values in
    let fprintf = Format.fprintf in
    let printed = ref Export_id.Set.empty in
    let recorded_symbol = ref Symbol.Set.empty in
    let symbols_to_print = Queue.create () in
    let printed_set_of_closures = ref Set_of_closures_id.Set.empty in
    let rec print_approx ppf (approx : approx) =
      match approx with
      | Value_unknown -> fprintf ppf "?"
      | Value_id id ->
        if Export_id.Set.mem id !printed then
          fprintf ppf "(%a: _)" Export_id.print id
        else begin
          try
            let descr = find_value id values in
            printed := Export_id.Set.add id !printed;
            fprintf ppf "@[<hov 2>(%a:@ %a)@]"
              Export_id.print id print_descr descr
          with Not_found ->
            fprintf ppf "(%a: Not available)" Export_id.print id
        end
      | Value_symbol sym ->
        if not (Symbol.Set.mem sym !recorded_symbol) then begin
          recorded_symbol := Symbol.Set.add sym !recorded_symbol;
          Queue.push sym symbols_to_print;
        end;
        Symbol.print ppf sym
    and print_descr ppf (descr : descr) =
      match descr with
      | Int i -> Format.pp_print_int ppf i
      | Char c -> fprintf ppf "%c" c
      | Constptr i -> fprintf ppf "%ip" i
      | Block (tag, fields) ->
        fprintf ppf "[%a:%a]" Tag.print tag print_fields fields
      | Mutable_block (tag, size) ->
        fprintf ppf "[mutable %a:%i]" Tag.print tag size
      | Closure {closure_id; set_of_closures} ->
        fprintf ppf "(closure %a, %a)" Closure_id.print closure_id
          print_set_of_closures set_of_closures
      | Set_of_closures set_of_closures ->
        fprintf ppf "(set_of_closures %a)" print_set_of_closures set_of_closures
      | String { contents; size } ->
        begin match contents with
        | Unknown_or_mutable -> Format.fprintf ppf "string %i" size
        | Contents s ->
          let s =
            if size > 10
            then String.sub s 0 8 ^ "..."
            else s
          in
          Format.fprintf ppf "string %i %S" size s
        end
      | Float f -> Format.pp_print_float ppf f
      | Float_array float_array ->
        Format.fprintf ppf "float_array%s %i"
          (match float_array.contents with
            | Unknown_or_mutable -> ""
            | Contents _ -> "_imm")
          float_array.size
      | Boxed_int (t, i) ->
        match t with
        | Int32 -> Format.fprintf ppf "%li" i
        | Int64 -> Format.fprintf ppf "%Li" i
        | Nativeint -> Format.fprintf ppf "%ni" i
    and print_fields ppf fields =
      Array.iter (fun approx -> fprintf ppf "%a@ " print_approx approx) fields
    and print_set_of_closures ppf
        { set_of_closures_id; bound_vars; aliased_symbol; results } =
      if Set_of_closures_id.Set.mem set_of_closures_id !printed_set_of_closures
      then fprintf ppf "%a" Set_of_closures_id.print set_of_closures_id
      else begin
        printed_set_of_closures :=
          Set_of_closures_id.Set.add set_of_closures_id !printed_set_of_closures;
        let print_alias ppf = function
          | None -> ()
          | Some symbol ->
            Format.fprintf ppf "@ (alias: %a)" Symbol.print symbol
        in
        fprintf ppf "{%a: %a%a => %a}"
          Set_of_closures_id.print set_of_closures_id
          print_binding bound_vars
          print_alias aliased_symbol
          (Closure_id.Map.print (Format.pp_print_list print_approx)) results
      end
    and print_binding ppf bound_vars =
      Var_within_closure.Map.iter (fun clos_id approx ->
          fprintf ppf "%a -> %a,@ "
            Var_within_closure.print clos_id
            print_approx approx)
        bound_vars
    in
    let rec print_recorded_symbols () =
      if not (Queue.is_empty symbols_to_print) then begin
        let sym = Queue.pop symbols_to_print in
        begin match Symbol.Map.find sym t.symbol_id with
        | exception Not_found -> ()
        | id ->
          fprintf ppf "@[<hov 2>%a:@ %a@];@ "
            Symbol.print sym
            print_approx (Value_id id)
        end;
        print_recorded_symbols ();
      end
    in
    List.iter (fun s -> Queue.push s symbols_to_print) root_symbols;
    fprintf ppf "@[<hov 2>Globals:@ ";
    fprintf ppf "@]@ @[<hov 2>Symbols:@ ";
    print_recorded_symbols ();
    fprintf ppf "@]"

  let print_offsets ppf (t : t) =
    Format.fprintf ppf "@[<v 2>offset_fun:@ ";
    Closure_id.Map.iter (fun cid off ->
        Format.fprintf ppf "%a -> %i@ "
          Closure_id.print cid off) t.offset_fun;
    Format.fprintf ppf "@]@ @[<v 2>offset_fv:@ ";
    Var_within_closure.Map.iter (fun vid off ->
        Format.fprintf ppf "%a -> %i@ "
          Var_within_closure.print vid off) t.offset_fv;
    Format.fprintf ppf "@]@ "

  let print_functions ppf (t : t) =
    Set_of_closures_id.Map.print Flambda.print_function_declarations ppf
      t.sets_of_closures

  let print_all ppf ((t, root_symbols) : t * Symbol.t list) =
    let fprintf = Format.fprintf in
    fprintf ppf "approxs@ %a@.@."
      print_approx (t, root_symbols);
    fprintf ppf "functions@ %a@.@."
      print_functions t
end
