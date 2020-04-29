(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2020 OCamlPro SAS                                    *)
(*   Copyright 2014--2020 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-30-40-41-42"]

open! Int_replace_polymorphic_compare

module Option = struct
  include Option
  let hash h = function
    | None -> 0
    | Some x -> h x
end

(* XXX should be moved to another file *)
module Depth_variable = struct
        (* XXX include Mutable_Variable?*)
  let next_id = ref 0
  type t = string
  let create name = incr next_id; Printf.sprintf "%s_%d" name !next_id
  module With_map = Identifiable.Make (struct
      type nonrec t = t
      let print ppf t = Format.fprintf ppf "%s" t
      let output chan t = print (Format.formatter_of_out_channel chan) t
      let hash = Hashtbl.hash
      let compare = String.compare
      let equal = String.equal
    end)
  module T = With_map.T
  let compare = T.compare
  let equal t1 t2 = T.compare t1 t2 = 0
  let print = T.print
  let output = T.output
  let hash = T.hash
  module Map = With_map.Map
  module Set = With_map.Set
  module Tbl = With_map.Tbl
end

(* XXX should be moved to another file *)
module Depth_expr = struct
  type t =
    | Zero
    | Succ of t
    | Variable of Depth_variable.t
  let print ppf t =
    let rec print ppf k = function
      | Zero -> Format.fprintf ppf "%d" k
      | Succ d -> print ppf (succ k) d
      | Variable v ->
        if k = 0 then
          Depth_variable.print ppf v
        else
          Format.fprintf ppf "%a+%d" Depth_variable.print v k
    in
    print ppf 0 t
  let rec compare left right =
    match left, right with
    | Zero, Zero -> 0
    | Succ left, Succ right -> compare left right
    | Variable left, Variable right -> Depth_variable.compare left right
    | Zero, (Succ _ | Variable _) -> -1
    | Succ _, Zero -> 1
    | Succ _, Variable _ -> -1
    | Variable _, (Zero | Succ _) -> 1
  let rec equal left right =
    match left, right with
    | Zero, Zero -> true
    | Succ left, Succ right -> equal left right
    | Variable left, Variable right -> Depth_variable.equal left right
    | Zero, (Succ _ | Variable _)
    | Succ _, (Zero | Variable _)
    | Variable _, (Zero | Succ _) ->
      false
  let rec hash = function
    | Zero -> 0
    | Succ d -> 1 + hash d
    | Variable v -> Depth_variable.hash v
end

(* XXX should be moved to another file *)
module Coercion = struct

  type change_depth = { from : Depth_expr.t; to_ : Depth_expr.t; }
  let equal_change_depth
        { from = from_left; to_ = to_left; }
        { from = from_right; to_ = to_right; } =
    Depth_expr.equal from_left from_right
    && Depth_expr.equal to_left to_right
  let compare_change_depth
        { from = from_left; to_ = to_left; }
        { from = from_right; to_ = to_right; } =
    let c = Depth_expr.compare from_left from_right in
    if c <> 0 then c
    else Depth_expr.compare to_left to_right
  let hash_change_depth { from; to_; } =
    Depth_expr.hash from + Depth_expr.hash to_
  let print_change_depth ppf { from; to_; } =
    Format.fprintf ppf "depth: %a->%a" Depth_expr.print from Depth_expr.print to_
  let change_depth ~from ~to_ () =
    if Depth_expr.equal from to_ then
      None
    else
      Some { from; to_ }
  let compose_change_depth
        ({ from = src; to_ = mid1; } : change_depth)
        ({ from = mid2; to_ = dst; } : change_depth) =
    if Depth_expr.equal mid1 mid2 then
      Or_bottom.Ok (change_depth ~from:src ~to_:dst ())
    else
      Or_bottom.Bottom
  let inverse_change_depth { from; to_; } =
    { from = to_; to_ = from; }

  type change_unroll_to = { from : Depth_expr.t option; to_ : Depth_expr.t option; }
  let equal_change_unroll_to
        { from = from_left; to_ = to_left; }
        { from = from_right; to_ = to_right; } =
    Option.equal Depth_expr.equal from_left from_right
    && Option.equal Depth_expr.equal to_left to_right
  let compare_change_unroll_to
        { from = from_left; to_ = to_left; }
        { from = from_right; to_ = to_right; } =
    let c = Option.compare Depth_expr.compare from_left from_right in
    if c <> 0 then c
    else Option.compare Depth_expr.compare to_left to_right
  let hash_change_unroll_to { from; to_; } =
    Option.hash Depth_expr.hash from + Option.hash Depth_expr.hash to_
  let print_change_unroll_to ppf { from; to_; } =
    Format.fprintf ppf "unroll_to: %a->%a"
      (Misc.Stdlib.Option.print Depth_expr.print) from
      (Misc.Stdlib.Option.print Depth_expr.print) to_
  let change_unroll_to ~from ~to_ () =
    if Option.equal Depth_expr.equal from to_ then
      None
    else
      Some { from; to_ }
  let compose_change_unroll_to
        ({ from = src; to_ = mid1; } : change_unroll_to)
        ({ from = mid2; to_ = dst; } : change_unroll_to) =
    if Option.equal Depth_expr.equal mid1 mid2 then
      Or_bottom.Ok (change_unroll_to ~from:src ~to_:dst ())
    else
      Or_bottom.Bottom
  let inverse_change_unroll_to { from; to_; } =
    { from = to_; to_ = from; }

  type t =
    | Id
    | Change_depth of change_depth
    | Change_unroll_to of change_unroll_to
    | Change_depth_and_unroll_to of {
        change_depth : change_depth;
        change_unroll_to : change_unroll_to;
      }

  let hash = function
    | Id -> 0
    | Change_depth change_depth -> hash_change_depth change_depth
    | Change_unroll_to change_unroll_to -> hash_change_unroll_to change_unroll_to
    | Change_depth_and_unroll_to { change_depth; change_unroll_to; } ->
      hash_change_depth change_depth + hash_change_unroll_to change_unroll_to

  let assemble change_depth change_unroll_to =
    match change_depth, change_unroll_to with
    | None, None -> Id
    | Some change_depth, None -> Change_depth change_depth
    | None, Some change_unroll_to -> Change_unroll_to change_unroll_to
    | Some change_depth , Some change_unroll_to ->
      Change_depth_and_unroll_to { change_depth; change_unroll_to }

  let id = Id
  let is_id = function
    | Id -> true
    | Change_depth _ -> false
    | Change_unroll_to _ -> false
    | Change_depth_and_unroll_to _ -> false
  let change_depth_and_unroll_to ~from_depth ~to_depth ~from_unroll_to ~to_unroll_to () =
    assemble
      (change_depth ~from:from_depth ~to_:to_depth ())
      (change_unroll_to ~from:from_unroll_to ~to_:to_unroll_to ())
  let change ~f ~wrap =
    fun ~from ~to_ () ->
      f ~from ~to_ ()
      |> Option.fold ~none:Id ~some:wrap
  let change_depth =
    change ~f:change_depth ~wrap:(fun cd -> Change_depth cd)
  let change_unroll_to =
    change ~f:change_unroll_to ~wrap:(fun cut -> Change_unroll_to cut)

  let descr = function
    | Id -> None, None
    | Change_depth change_depth -> Some change_depth, None
    | Change_unroll_to change_unroll_to -> None, Some change_unroll_to
    | Change_depth_and_unroll_to { change_depth; change_unroll_to; } ->
      Some change_depth, Some change_unroll_to
  let print ppf t =
    let change_depth, change_unroll_to = descr t in
    Format.fprintf ppf "%a %a"
      (Misc.Stdlib.Option.print print_change_depth) change_depth
      (Misc.Stdlib.Option.print print_change_unroll_to) change_unroll_to
  let compare left right =
    let change_depth_left, change_unroll_to_left = descr left in
    let change_depth_right, change_unroll_to_right = descr right in
    let c = Option.compare compare_change_depth change_depth_left change_depth_right in
    if c <> 0 then c
    else Option.compare compare_change_unroll_to change_unroll_to_left change_unroll_to_right
  let equal left right =
    let change_depth_left, change_unroll_to_left = descr left in
    let change_depth_right, change_unroll_to_right = descr right in
    Option.equal equal_change_depth change_depth_left change_depth_right
    && Option.equal equal_change_unroll_to change_unroll_to_left change_unroll_to_right

  let compose left right =
    let change_depth_left, change_unroll_to_left = descr left in
    let change_depth_right, change_unroll_to_right = descr right in
    let map2 f left right =
      match left, right with
      | None, None -> Or_bottom.Ok None
      | None, Some _ -> Or_bottom.Ok right
      | Some _, None -> Or_bottom.Ok left
      | Some left, Some right -> f left right
    in
    Or_bottom.both ~f:assemble
      (map2 compose_change_depth change_depth_left change_depth_right)
      (map2 compose_change_unroll_to change_unroll_to_left change_unroll_to_right)

  let inverse = function
    | Id -> Id
    | Change_depth cd -> Change_depth (inverse_change_depth cd)
    | Change_unroll_to cut -> Change_unroll_to (inverse_change_unroll_to cut)
    | Change_depth_and_unroll_to {
        change_depth = cd;
        change_unroll_to = cut;
      } ->
      Change_depth_and_unroll_to {
        change_depth = inverse_change_depth cd;
        change_unroll_to = inverse_change_unroll_to cut;
      }

end

module Id = Table_by_int_id.Id

let var_flags = 0
let symbol_flags = 1
let const_flags = 2
let simple_flags = 3

module Const_data = struct
  type t =
    | Naked_immediate of Immediate.t
    | Tagged_immediate of Immediate.t
    | Naked_float of Numbers.Float_by_bit_pattern.t
    | Naked_int32 of Int32.t
    | Naked_int64 of Int64.t
    | Naked_nativeint of Targetint.t

  let flags = const_flags

  include Identifiable.Make (struct
    type nonrec t = t

    let print ppf (t : t) =
      match t with
      | Naked_immediate i ->
        Format.fprintf ppf "@<0>%s#%a@<0>%s"
          (Flambda_colours.naked_number ())
          Immediate.print i
          (Flambda_colours.normal ())
      | Tagged_immediate i ->
        Format.fprintf ppf "@<0>%s%a@<0>%s"
          (Flambda_colours.tagged_immediate ())
          Immediate.print i
          (Flambda_colours.normal ())
      | Naked_float f ->
        Format.fprintf ppf "@<0>%s#%a@<0>%s"
          (Flambda_colours.naked_number ())
          Numbers.Float_by_bit_pattern.print f
          (Flambda_colours.normal ())
      | Naked_int32 n ->
        Format.fprintf ppf "@<0>%s#%ldl@<0>%s"
          (Flambda_colours.naked_number ())
          n
          (Flambda_colours.normal ())
      | Naked_int64 n ->
        Format.fprintf ppf "@<0>%s#%LdL@<0>%s"
          (Flambda_colours.naked_number ())
          n
          (Flambda_colours.normal ())
      | Naked_nativeint n ->
        Format.fprintf ppf "@<0>%s#%an@<0>%s"
          (Flambda_colours.naked_number ())
          Targetint.print n
          (Flambda_colours.normal ())

    let output _ _ = Misc.fatal_error "[output] not yet implemented"

    let compare t1 t2 =
      match t1, t2 with
      | Naked_immediate i1, Naked_immediate i2 ->
        Immediate.compare i1 i2
      | Tagged_immediate i1, Tagged_immediate i2 ->
        Immediate.compare i1 i2
      | Naked_float f1, Naked_float f2 ->
        Numbers.Float_by_bit_pattern.compare f1 f2
      | Naked_int32 n1, Naked_int32 n2 ->
        Int32.compare n1 n2
      | Naked_int64 n1, Naked_int64 n2 ->
        Int64.compare n1 n2
      | Naked_nativeint n1, Naked_nativeint n2 ->
        Targetint.compare n1 n2
      | Naked_immediate _, _ -> -1
      | _, Naked_immediate _ -> 1
      | Tagged_immediate _, _ -> -1
      | _, Tagged_immediate _ -> 1
      | Naked_float _, _ -> -1
      | _, Naked_float _ -> 1
      | Naked_int32 _, _ -> -1
      | _, Naked_int32 _ -> 1
      | Naked_int64 _, _ -> -1
      | _, Naked_int64 _ -> 1

    let equal t1 t2 =
      if t1 == t2 then true
      else
        match t1, t2 with
        | Naked_immediate i1, Naked_immediate i2 ->
          Immediate.equal i1 i2
        | Tagged_immediate i1, Tagged_immediate i2 ->
          Immediate.equal i1 i2
        | Naked_float f1, Naked_float f2 ->
          Numbers.Float_by_bit_pattern.equal f1 f2
        | Naked_int32 n1, Naked_int32 n2 ->
          Int32.equal n1 n2
        | Naked_int64 n1, Naked_int64 n2 ->
          Int64.equal n1 n2
        | Naked_nativeint n1, Naked_nativeint n2 ->
          Targetint.equal n1 n2
        | (Naked_immediate _ | Tagged_immediate _ | Naked_float _
            | Naked_int32 _ | Naked_int64 _ | Naked_nativeint _), _ -> false

    let hash t =
      match t with
      | Naked_immediate n -> Immediate.hash n
      | Tagged_immediate n -> Immediate.hash n
      | Naked_float n -> Numbers.Float_by_bit_pattern.hash n
      | Naked_int32 n -> Hashtbl.hash n
      | Naked_int64 n -> Hashtbl.hash n
      | Naked_nativeint n -> Targetint.hash n
  end)
end

module Variable_data = struct
  type t = {
    compilation_unit : Compilation_unit.t;
    name : string;
    name_stamp : int;
    user_visible : bool;
  }

  let flags = var_flags

  let print ppf { compilation_unit; name; name_stamp; user_visible; } =
    Format.fprintf ppf "@[<hov 1>(\
        @[<hov 1>(compilation_unit@ %a)@]@ \
        @[<hov 1>(name@ %s)@]@ \
        @[<hov 1>(name_stamp@ %d)@]@ \
        @[<hov 1>(user_visible@ %b)@]\
        )@]"
      Compilation_unit.print compilation_unit
      name
      name_stamp
      user_visible

  let hash { compilation_unit; name = _; name_stamp; user_visible = _; } =
    (* The [name_stamp] uniquely determines [name] and [user_visible]. *)
    Hashtbl.hash (Compilation_unit.hash compilation_unit, name_stamp)

  let equal t1 t2 =
    if t1 == t2 then true
    else
      let { compilation_unit = compilation_unit1; name = _;
            name_stamp = name_stamp1; user_visible = _; 
          } = t1
      in
      let { compilation_unit = compilation_unit2; name = _;
            name_stamp = name_stamp2; user_visible = _; 
          } = t2
      in
      Int.equal name_stamp1 name_stamp2
        && Compilation_unit.equal compilation_unit1 compilation_unit2
end

module Symbol_data = struct
  type t = {
    compilation_unit : Compilation_unit.t;
    linkage_name : Linkage_name.t;
  }

  let flags = symbol_flags

  let print ppf { compilation_unit; linkage_name; } =
    Format.fprintf ppf "@[<hov 1>(\
        @[<hov 1>(compilation_unit@ %a)@]@ \
        @[<hov 1>(linkage_name@ %a)@]\
        )@]"
      Compilation_unit.print compilation_unit
      Linkage_name.print linkage_name

  let hash { compilation_unit = _; linkage_name; } =
    (* Linkage names are unique across a whole project, so there's no need
       to hash the compilation unit. *)
    Linkage_name.hash linkage_name

  let equal t1 t2 =
    if t1 == t2 then true
    else
      let { compilation_unit = _; linkage_name = linkage_name1; } = t1 in
      let { compilation_unit = _; linkage_name = linkage_name2; } = t2 in
      (* Linkage names are unique across a whole project, so there's no need
         to check the compilation units. *)
      Linkage_name.equal linkage_name1 linkage_name2
end

module Simple_data = struct
  type t = {
    simple : Id.t;  (* always without [Rec_info] *)
    coercion : Coercion.t;
  }

  let flags = simple_flags

  let print ppf { simple = _; coercion; } =
    Format.fprintf ppf "@[<hov 1>\
        @[<hov 1>(coercion@ %a)@]\
        @]"
      Coercion.print coercion

  let hash { simple; coercion; } =
    Hashtbl.hash (Id.hash simple, Coercion.hash coercion)

  let equal t1 t2 =
    if t1 == t2 then true
    else
      let { simple = simple1; coercion = coercion1; } = t1 in
      let { simple = simple2; coercion = coercion2; } = t2 in
      Id.equal simple1 simple2
        && Coercion.equal coercion1 coercion2
end

module Const = struct
  type t = Id.t

  module Table = Table_by_int_id.Make (Const_data)
  let grand_table_of_constants = ref (Table.create ())

  let initialise () =
    grand_table_of_constants := Table.create ()

  let find_data t = Table.find !grand_table_of_constants t

  module Descr = Const_data

  let create (data : Const_data.t) =
    Table.add !grand_table_of_constants data

  let naked_immediate imm = create (Naked_immediate imm)
  let tagged_immediate imm = create (Tagged_immediate imm)
  let naked_float f = create (Naked_float f)
  let naked_int32 i = create (Naked_int32 i)
  let naked_int64 i = create (Naked_int64 i)
  let naked_nativeint i = create (Naked_nativeint i)

  let const_true = tagged_immediate Immediate.bool_true
  let const_false = tagged_immediate Immediate.bool_false

  let untagged_const_true = naked_immediate Immediate.bool_true
  let untagged_const_false = naked_immediate Immediate.bool_false

  let untagged_const_zero = naked_immediate Immediate.zero

  let untagged_const_int i = naked_immediate (Immediate.int i)

  let const_int i = tagged_immediate (Immediate.int i)

  let const_zero = tagged_immediate Immediate.zero
  let const_one = tagged_immediate Immediate.one
  let const_unit = const_zero

  let descr t = find_data t

  module T0 = struct
    let compare = Id.compare
    let equal = Id.equal
    let hash = Id.hash

    let print ppf t = Const_data.print ppf (descr t)

    let output chan t = print (Format.formatter_of_out_channel chan) t
  end

  include T0
  module T = struct
    type nonrec t = t
    include T0
  end

  module Set = Patricia_tree.Make_set (struct let print = print end)
  module Map = Patricia_tree.Make_map (struct let print = print end) (Set)
  (* CR mshinwell: The [Tbl]s will still print integers! *)
  module Tbl = Identifiable.Make_tbl (Numbers.Int) (Map)
end

module Variable = struct
  type t = Id.t

  module Table = Table_by_int_id.Make (Variable_data)
  let grand_table_of_variables = ref (Table.create ())

  let initialise () =
    grand_table_of_variables := Table.create ()

  let find_data t = Table.find !grand_table_of_variables t

  let compilation_unit t = (find_data t).compilation_unit
  let name t = (find_data t).name
  let name_stamp t = (find_data t).name_stamp
  let user_visible t = (find_data t).user_visible

  let previous_name_stamp = ref (-1)

  let create ?user_visible name =
    let name_stamp =
      (* CR mshinwell: check for overflow on 32 bit *)
      incr previous_name_stamp;
      !previous_name_stamp
    in
    let data : Variable_data.t =
      { compilation_unit = Compilation_unit.get_current_exn ();
        name;
        name_stamp;
        user_visible = Option.is_some user_visible;
      }
    in
    Table.add !grand_table_of_variables data

  module T0 = struct
    let compare = Id.compare
    let equal = Id.equal
    let hash = Id.hash

    (* CR mshinwell: colour? *)
    let print ppf t = Format.fprintf ppf "%s/%d" (name t) (name_stamp t)

    let output chan t = print (Format.formatter_of_out_channel chan) t
  end

  include T0
  module T = struct
    type nonrec t = t
    include T0
  end

  module Set = Patricia_tree.Make_set (struct let print = print end)
  module Map = Patricia_tree.Make_map (struct let print = print end) (Set)
  module Tbl = Identifiable.Make_tbl (Numbers.Int) (Map)
end

module Symbol = struct
  type t = Id.t

  module Table = Table_by_int_id.Make (Symbol_data)
  let grand_table_of_symbols = ref (Table.create ())

  let initialise () =
    grand_table_of_symbols := Table.create ()

  let find_data t = Table.find !grand_table_of_symbols t

  let unsafe_create compilation_unit linkage_name =
    let data : Symbol_data.t = { compilation_unit; linkage_name; } in
    Table.add !grand_table_of_symbols data

  let create compilation_unit linkage_name =
    let unit_linkage_name =
      Linkage_name.to_string
        (Compilation_unit.get_linkage_name compilation_unit)
    in
    let linkage_name =
      Linkage_name.create
        (unit_linkage_name ^ "__" ^ (Linkage_name.to_string linkage_name))
    in
    unsafe_create compilation_unit linkage_name

  let compilation_unit t = (find_data t).compilation_unit
  let linkage_name t = (find_data t).linkage_name

  module T0 = struct
    let compare = Id.compare
    let equal = Id.equal
    let hash = Id.hash

    let print ppf t =
      Format.fprintf ppf "@<0>%s" (Flambda_colours.symbol ());
      Compilation_unit.print ppf (compilation_unit t);
      Format.pp_print_string ppf ".";
      Linkage_name.print ppf (linkage_name t);
      Format.fprintf ppf "@<0>%s" (Flambda_colours.normal ())

    let output chan t =
      print (Format.formatter_of_out_channel chan) t
  end

  include T0
  module T = struct
    type nonrec t = t
    include T0
  end

  module Set = Patricia_tree.Make_set (struct let print = print end)
  module Map = Patricia_tree.Make_map (struct let print = print end) (Set)
  module Tbl = Identifiable.Make_tbl (Numbers.Int) (Map)
end

module Name = struct
  type t = Id.t

  let var v = v
  let symbol s = s

  let [@inline always] pattern_match t ~var ~symbol =
    let flags = Id.flags t in
    if flags = var_flags then var t
    else if flags = symbol_flags then symbol t
    else assert false

  module T0 = struct
    let compare = Id.compare
    let equal = Id.equal
    let hash = Id.hash

    let print ppf t =
      Format.fprintf ppf "@<0>%s" (Flambda_colours.name ());
      pattern_match t
        ~var:(fun var -> Variable.print ppf var)
        ~symbol:(fun symbol -> Symbol.print ppf symbol);
      Format.fprintf ppf "@<0>%s" (Flambda_colours.normal ())

    let output chan t =
      print (Format.formatter_of_out_channel chan) t
  end

  include T0
  module T = struct
    type nonrec t = t
    include T0
  end

  module Set = Patricia_tree.Make_set (struct let print = print end)
  module Map = Patricia_tree.Make_map (struct let print = print end) (Set)
  module Tbl = Identifiable.Make_tbl (Numbers.Int) (Map)
end

module Simple = struct
  type t = Id.t

  module Table = Table_by_int_id.Make (Simple_data)
  (* This table only holds [Simple]s that have auxiliary data associated
     with them, as indicated by the setting of the [simple_flags]. *)
  let grand_table_of_simples = ref (Table.create ())

  let initialise () =
    grand_table_of_simples := Table.create ()

  let find_data t = Table.find !grand_table_of_simples t

  let name n = n
  let var v = v
  let vars vars = vars
  let symbol s = s
  let const cst = cst

  let [@inline always] pattern_match t ~name ~const ~coercion =
    let flags = Id.flags t in
    if flags = var_flags then name (Name.var t)
    else if flags = symbol_flags then name (Name.symbol t)
    else if flags = const_flags then const t
    else if flags = simple_flags then begin
      match (find_data t).coercion with
      | c when not (Coercion.is_id c) ->
        coercion c (find_data t).simple
      | _ ->
        let t = (find_data t).simple in
        let flags = Id.flags t in
        if flags = var_flags then name (Name.var t)
        else if flags = symbol_flags then name (Name.symbol t)
        else if flags = const_flags then const t
        else assert false
    end else assert false

  let [@inline always] pattern_match_ignoring_coercion t ~name ~const =
    pattern_match t ~name ~const ~coercion:(fun _coercion s ->
      pattern_match s ~name ~const ~coercion:(fun _ -> assert false))

  let same t1 t2 =
    let name n1 =
      pattern_match_ignoring_coercion t2 ~name:(fun n2 -> Name.equal n1 n2)
        ~const:(fun _ -> false)
    in
    let const c1 =
      pattern_match_ignoring_coercion t2 ~name:(fun _ -> false)
        ~const:(fun c2 -> Const.equal c1 c2)
    in
    pattern_match_ignoring_coercion t1 ~name ~const

  let [@inline always] coercion t =
    let flags = Id.flags t in
    if flags = simple_flags then Some ((find_data t).coercion)
    else None

  module T0 = struct
    let compare = Id.compare
    let equal = Id.equal
    let hash = Id.hash

    let print ppf t =
      let print ppf t =
        pattern_match_ignoring_coercion t
          ~name:(fun name -> Name.print ppf name)
          ~const:(fun cst -> Const.print ppf cst)
      in
      match coercion t with
      | None -> print ppf t
      | Some rec_info ->
       Format.fprintf ppf "@[<hov 1>\
            @[<hov 1>(simple@ %a)@] \
            @[<hov 1>(coercion@ %a)@]\
            @]"
          print t
          Coercion.print rec_info

    let output chan t =
      print (Format.formatter_of_out_channel chan) t
  end

  include T0
  module T = struct
    type nonrec t = t
    include T0
  end

  let coerce t new_coercion =
    if Coercion.is_id new_coercion then t
    else
      match coercion t with
      | None ->
        let data : Simple_data.t = { simple = t; coercion = new_coercion; } in
        Table.add !grand_table_of_simples data
      | Some _ ->
        (* XXX *)
        Misc.fatal_errorf "Cannot add [Rec_info] to [Simple] %a that already \
            has [Rec_info]"
          print t

  module Set = Patricia_tree.Make_set (struct let print = print end)
  module Map = Patricia_tree.Make_map (struct let print = print end) (Set)
  module Tbl = Identifiable.Make_tbl (Numbers.Int) (Map)
end

let initialise () =
  Const.initialise ();
  Variable.initialise ();
  Symbol.initialise ();
  Simple.initialise ()
