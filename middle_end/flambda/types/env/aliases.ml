(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                   Mark Shinwell, Jane Street Europe                    *)
(*                                                                        *)
(*   Copyright 2019 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-30-40-41-42"]

type 'a coercion_to_canonical = {
  coercion_to_canonical : 'a;
} [@@ocaml.unboxed]

module type Coercion = sig
  type t
  val equal : t -> t -> bool
  val inverse : t -> t
  val id : t
  val is_id : t -> bool
  val compose : t -> newer:t -> t
  val print : Format.formatter -> t -> unit
end

module type Element = sig
  type t
  val name : Name.t -> t
  val without_coercion : t -> t
  val pattern_match
     : t
    -> name:(Reg_width_things.Name.t -> 'a)
    -> const:(Reg_width_things.Const.t -> 'a)
    -> 'a
  include Identifiable.S with type t := t
end

module type Export = sig
  type e
  type t
  val add : t -> e -> t
  val empty : t
  val to_ids_for_export : t -> Ids_for_export.t
  module Import_map : sig
    type t
    val of_import_map : Ids_for_export.Import_map.t -> t
    val simple : t -> e -> e
  end
end

module Make (C : Coercion) (E : Element) (Exp : Export with type e = E.t) = struct

  type nonrec coercion_to_canonical = C.t coercion_to_canonical

  let print_coercion_to_canonical ppf { coercion_to_canonical; } =
    C.print ppf coercion_to_canonical

  let equal_coercion_to_canonical c1 c2 =
    C.equal c1.coercion_to_canonical c2.coercion_to_canonical

  type map_to_canonical = coercion_to_canonical E.Map.t

  let fatal_inconsistent ~func_name elt coercion1 coercion2 =
    Misc.fatal_errorf "[%s] maps with inconsistent  element/coercion couples; \
                       %a has coercions %a and %a"
      func_name
      E.print elt
      C.print coercion1
      C.print coercion2

  let map_inter map1 map2 =
    E.Map.merge (fun elt coercion1 coercion2 ->
      match coercion1, coercion2 with
      | None, None | Some _, None | None, Some _ -> None
      | Some { coercion_to_canonical = coercion1; }, Some { coercion_to_canonical = coercion2; } ->
        if C.equal coercion1 coercion2 then
          Some { coercion_to_canonical = coercion1; }
        else
          fatal_inconsistent ~func_name:"Aliases.map_inter" elt coercion1 coercion2)
      map1
      map2

  let map_union map1 map2 =
    E.Map.union (fun elt coercion1 coercion2 ->
      match coercion1, coercion2 with
      | { coercion_to_canonical = coercion1; }, { coercion_to_canonical = coercion2; } ->
      if C.equal coercion1 coercion2 then
        Some { coercion_to_canonical = coercion1; }
      else
        fatal_inconsistent ~func_name:"Aliases.map_union" elt coercion1 coercion2)
      map1
      map2

  module Aliases_of_canonical_element : sig
    type t

    val print : Format.formatter -> t -> unit

    val invariant : t -> unit

    val empty : t
    val is_empty : t -> bool

    val add : t -> E.t -> coercion_to_canonical:C.t -> Name_mode.t -> t

    val find_earliest_candidates_exn
      : t
      -> min_name_mode:Name_mode.t
      -> map_to_canonical

    val all : t -> map_to_canonical

    val mem : t -> E.t -> bool

    val union : t -> t -> t
    val inter : t -> t -> t

    val import : (E.t -> E.t) -> t -> t

    val merge : t -> t -> t

    val compose : t -> newer:C.t -> t
  end = struct
    type t = {
      aliases : map_to_canonical Name_mode.Map.t;
      all : map_to_canonical;
    }

    let invariant { aliases; all; } =
      (* The elements in [aliases] have disjoint set of keys. *)
      let aliases_union : map_to_canonical =
        Name_mode.Map.fold (fun _name_mode map acc ->
          E.Map.union (fun elt _coercion1 _coercion2 ->
            Misc.fatal_errorf "[Aliases_of_canonical_element.invariant]: \
                               element %a appears in several modes"
              E.print elt)
            map
            acc)
          aliases
          E.Map.empty
      in
      (* [all] is the union of all elements in [aliases] *)
      if E.Map.equal equal_coercion_to_canonical all aliases_union then
        ()
      else
        Misc.fatal_errorf "[Aliases_of_canonical_element.invariant]: \
                           [aliases] and [all] are not consistent"

    let print ppf { aliases; all = _; } =
      Name_mode.Map.print (E.Map.print print_coercion_to_canonical) ppf aliases

    let empty = {
      aliases = Name_mode.Map.empty;
      all = E.Map.empty;
    }

    let is_empty t = E.Map.is_empty t.all

    let add t elt ~coercion_to_canonical name_mode =
      if E.Map.mem elt t.all then begin
        Misc.fatal_errorf "%a already added to [Aliases_of_canonical_element]: \
                           %a"
          E.print elt
          print t
      end;
      let aliases =
        Name_mode.Map.update name_mode
          (function
            | None -> Some (E.Map.singleton elt { coercion_to_canonical; })
            | Some elts ->
              if !Clflags.flambda_invariant_checks then begin
                assert (not (E.Map.mem elt elts))
              end;
              Some (E.Map.add elt { coercion_to_canonical; } elts))
          t.aliases
      in
      let all = E.Map.add elt { coercion_to_canonical; } t.all in
      { aliases;
        all;
      }

    let find_earliest_candidates_exn t ~min_name_mode =
      let _order, elts =
        Name_mode.Map.find_first (fun order ->
          match
            Name_mode.compare_partial_order
              order min_name_mode
          with
          | None -> false
          | Some result -> result >= 0)
          t.aliases
      in
      elts

    let mem t elt =
      E.Map.mem elt t.all

    let all t = t.all

    let union t1 t2 =
      let aliases : map_to_canonical Name_mode.Map.t=
        Name_mode.Map.union (fun _order elts1 elts2 ->
          Some (map_union elts1 elts2))
          t1.aliases t2.aliases
      in
      let t =
        { aliases;
          all = map_union t1.all t2.all;
        }
      in
      invariant t; (* CR xclerc for xclerc: not guaranteed to hold *)
      t

    let inter t1 t2 =
      let aliases =
        Name_mode.Map.merge (fun _order elts1 elts2 ->
          match elts1, elts2 with
          | None, None | Some _, None | None, Some _ -> None
          | Some elts1, Some elts2 ->
            Some (map_inter elts1 elts2))
          t1.aliases t2.aliases
      in
      let t =
        { aliases;
          all = map_inter t1.all t2.all;
        }
      in
      invariant t;
      t

    let import import_simple { aliases; all } =
      let map_simple elts =
        E.Map.fold (fun elt coercion acc ->
          E.Map.add (import_simple elt) coercion acc)
          elts
          E.Map.empty
      in
      let aliases = Name_mode.Map.map map_simple aliases in
      let all = map_simple all in
      let t = { aliases; all } in
      invariant t; (* CR xclerc for xclerc: not guaranteed to hold *)
      t

    let merge t1 t2 =
      let aliases =
        Name_mode.Map.union (fun _mode map1 map2 ->
          Some (map_union map1 map2)
        )
          t1.aliases
          t2.aliases
      in
      let all = map_union t1.all t2.all in
      let t = { aliases; all; } in
      invariant t; (* CR xclerc for xclerc: not guaranteed to hold *)
      t

    let compose { aliases; all; } ~newer =
      let f m =
        E.Map.map
          (fun { coercion_to_canonical; } ->
             { coercion_to_canonical = C.compose coercion_to_canonical ~newer; })
          m
      in
      let aliases = Name_mode.Map.map f aliases in
      let all = f all in
      { aliases; all; }

  end

type t = {
  canonical_elements : (E.t * coercion_to_canonical) E.Map.t;
  (* Canonical elements that have no known aliases are not included in
     [canonical_elements]. *)
  aliases_of_canonical_elements : Aliases_of_canonical_element.t E.Map.t;
  (* For [elt |-> aliases] in [aliases_of_canonical_elements], then
     [aliases] never includes [elt]. *)
  (* CR mshinwell: check this always holds *)
  binding_times_and_modes : Binding_time.With_name_mode.t E.Map.t;
  (* Binding times and name modes define an order on the elements.
     The canonical element for a set of aliases is always the minimal
     element for this order, which is different from the order used
     for creating sets and maps. *)
}

(* Canonical elements can be seen as a collection of star graphs:

   canon_i <--[coercion_i_0]-- elem_i_0
       ^ ^--[...]-- ...
        \--[coercion_i_m]-- elem_i_m

   ...

   canon_j <--[coercion_j_0]-- elem_j_0
       ^ ^--[...]-- ...
        \--[coercion_j_n]-- elem_j_n


   stored as a map:

   canonical_elements[elem_i_0] = (canon_i, coercion_i_0)
   ...
   canonical_elements[elem_i_m] = (canon_i, coercion_i_m)

   ...

   canonical_elements[elem_j_0] = (canon_j, coercion_j_0)
   ...
   canonical_elements[elem_j_n] = (canon_j, coercion_j_n)
*)

let print ppf { canonical_elements; aliases_of_canonical_elements;
                binding_times_and_modes; } =
  let print_element_and_coercion ppf (elt, coercion) =
    Format.fprintf ppf "%a (%a)"
      E.print elt
      print_coercion_to_canonical coercion
  in
  Format.fprintf ppf
    "@[<hov 1>(\
     @[<hov 1>(canonical_elements@ %a)@]@ \
     @[<hov 1>(aliases_of_canonical_elements@ %a)@]@ \
     @[<hov 1>(binding_times_and_modes@ %a)@]\
     )@]"
    (E.Map.print print_element_and_coercion) canonical_elements
    (E.Map.print Aliases_of_canonical_element.print)
    aliases_of_canonical_elements
    (E.Map.print Binding_time.With_name_mode.print)
    binding_times_and_modes

let defined_earlier t alias ~than =
  let info1 = E.Map.find alias t.binding_times_and_modes in
  let info2 = E.Map.find than t.binding_times_and_modes in
  Binding_time.strictly_earlier
    (Binding_time.With_name_mode.binding_time info1)
    ~than:(Binding_time.With_name_mode.binding_time info2)

let name_mode t elt =
  Binding_time.With_name_mode.name_mode
    (E.Map.find elt t.binding_times_and_modes)

let invariant t =
  if !Clflags.flambda_invariant_checks then begin
    let _all_aliases : map_to_canonical =
      E.Map.fold (fun canonical_element aliases all_aliases ->
          Aliases_of_canonical_element.invariant aliases;
          let aliases = Aliases_of_canonical_element.all aliases in
          if not (E.Map.for_all (fun elt _coercion ->
            defined_earlier t canonical_element ~than:elt) aliases)
          then begin
            Misc.fatal_errorf "Canonical element %a is not earlier than \
                all of its aliases:@ %a"
              E.print canonical_element
              print t
          end;
          if E.Map.mem canonical_element aliases then begin
            Misc.fatal_errorf "Canonical element %a occurs in alias set:@ %a"
              E.print canonical_element
              (E.Map.print print_coercion_to_canonical) aliases
          end;
          if not (E.Map.is_empty (map_inter aliases all_aliases)) then
          begin
            Misc.fatal_errorf "Overlapping alias sets:@ %a" print t
          end;
          map_union aliases all_aliases)
        t.aliases_of_canonical_elements
        E.Map.empty
    in
    ()
  end

let empty = {
  (* CR mshinwell: Rename canonical_elements, maybe to
     aliases_to_canonical_elements. *)
  canonical_elements = E.Map.empty;
  aliases_of_canonical_elements = E.Map.empty;
  binding_times_and_modes = E.Map.empty;
}

type canonical =
  | Is_canonical of E.t
  | Alias_of_canonical of {
      element : E.t;
      canonical_element : E.t;
      coercion_to_canonical : coercion_to_canonical;
    }

let canonical t element : canonical =
  match E.Map.find element t.canonical_elements with
  | exception Not_found -> Is_canonical element
  | canonical_element, coercion_to_canonical ->
    if !Clflags.flambda_invariant_checks then begin
      assert (not (E.equal element canonical_element))
    end;
    Alias_of_canonical { element; canonical_element; coercion_to_canonical; }

let get_aliases_of_canonical_element t ~canonical_element =
  match E.Map.find canonical_element t.aliases_of_canonical_elements with
  | exception Not_found -> Aliases_of_canonical_element.empty
  | aliases -> aliases

(*
   before
   ~~~~~~
   canonical_element <--[coercion_ce_0]-- ce_0
     ^ ^--[...]-- ...
      \--[coercion_ce_m]-- ce_m
   to_be_demoted <--[coercion_tbd_0]-- tbd_0
     ^ ^--[...]-- ...
      \--[coercion_tbd_n]-- tbd_n

   i.e.

   canonical_elements[ce_0] = (canonical_element, coercion_ce_0)
   ...
   canonical_elements[ce_m] = (canonical_element, coercion_ce_m)
   canonical_elements[tbd_0] = (to_be_demoted, coercion_tbd_0)
   ...
   canonical_elements[tbd_n] = (to_be_demoted, coercion_tbd_n)


   after
   ~~~~~
   canonical_element <--[coercion_ce_0]-- ce_0
     ^ ^ ^ ^ ^ ^--[...]-- ...
     | | | |  \--[coercion_ce_m]-- ce_m
     | | | \--[coercion_to_canonical]-- to_be_demoted
     | | \--[compose(coercion_tbd_0, coercion_to_canonical)]-- tbd_0
     | \--[...]-- ...
     \--[compose(coercion_tbd_n, coercion_to_canonical)]-- tbd_n

   i.e.

   canonical_elements[ce_0] = (canonical_element, coercion_ce_0)
   ...
   canonical_elements[ce_m] = (canonical_element, coercion_ce_m)
   canonical_elements[to_be_demoted] = (canonical_element, coercion_to_canonical)
   canonical_elements[tbd_0] = (canonical_element, compose(coercion_tbd_0, coercion_to_canonical))
   ...
   canonical_elements[tbd_n] = (canonical_element, compose(coercion_tbd_n, coercion_to_canonical))

*)
let add_alias_between_canonical_elements t ~canonical_element ~coercion_to_canonical:{ coercion_to_canonical; } ~to_be_demoted =
  if E.equal canonical_element to_be_demoted then begin
    if C.is_id coercion_to_canonical then begin
      t
    end else
      Misc.fatal_errorf "Cannot add an alias to itself with a non-identity coercion"
  end else
    let aliases_of_to_be_demoted =
      get_aliases_of_canonical_element t ~canonical_element:to_be_demoted
    in
    if !Clflags.flambda_invariant_checks then begin
      assert (not (Aliases_of_canonical_element.mem
        aliases_of_to_be_demoted canonical_element))
    end;
    let canonical_elements =
      t.canonical_elements
      |> E.Map.fold (fun alias { coercion_to_canonical = coercion_to_to_be_demoted; } canonical_elements ->
        let coercion_to_canonical =
          C.compose coercion_to_to_be_demoted ~newer:coercion_to_canonical
        in
        E.Map.add alias (canonical_element, { coercion_to_canonical; }) canonical_elements)
        (Aliases_of_canonical_element.all aliases_of_to_be_demoted)
      |> E.Map.add to_be_demoted (canonical_element, { coercion_to_canonical; })
    in
    let aliases_of_canonical_element =
      get_aliases_of_canonical_element t ~canonical_element
    in
    if !Clflags.flambda_invariant_checks then begin
      assert (not (Aliases_of_canonical_element.mem
        aliases_of_canonical_element to_be_demoted));
      assert (Aliases_of_canonical_element.is_empty (
        Aliases_of_canonical_element.inter
          aliases_of_canonical_element aliases_of_to_be_demoted))
    end;
    let aliases =
      Aliases_of_canonical_element.add
        (Aliases_of_canonical_element.union
           (Aliases_of_canonical_element.compose aliases_of_to_be_demoted ~newer:coercion_to_canonical)
           aliases_of_canonical_element)
        to_be_demoted
        ~coercion_to_canonical
        (name_mode t to_be_demoted)
    in
    let aliases_of_canonical_elements =
      t.aliases_of_canonical_elements
      |> E.Map.remove to_be_demoted
      |> E.Map.add (* replace *) canonical_element aliases
    in
    let res =
    { canonical_elements;
      aliases_of_canonical_elements;
      binding_times_and_modes = t.binding_times_and_modes;
    } in
    invariant res;
    res

type to_be_demoted = {
  canonical_element : E.t;
  to_be_demoted : E.t;
}

let choose_canonical_element_to_be_demoted t ~canonical_element1
      ~canonical_element2 =
  if defined_earlier t canonical_element1 ~than:canonical_element2
  then
    { canonical_element = canonical_element1;
      to_be_demoted = canonical_element2;
    }
  else
    { canonical_element = canonical_element2;
      to_be_demoted = canonical_element1;
    }

(* CR mshinwell: add submodule *)
type add_result = {
  t : t;
  canonical_element : E.t;
  alias_of : E.t;
  coerce_alias_of_to_canonical_element : C.t;
}

let invariant_add_result ~original_t { canonical_element; alias_of; t; coerce_alias_of_to_canonical_element = _; } =
  if !Clflags.flambda_invariant_checks then begin
    invariant t;
    if not (E.equal canonical_element alias_of) then begin
      if not (defined_earlier t canonical_element ~than:alias_of) then begin
        Misc.fatal_errorf "Canonical element %a should be defined earlier \
                           than %a after alias addition.@ Original alias tracker:@ %a@ \
                           Resulting alias tracker:@ %a"
          E.print canonical_element
          E.print alias_of
          print original_t
          print t
      end
    end
  end

let add_alias t ~element1 ~coerce_from_element2_to_element1 ~element2 =
  let wrap ~canonical_element ~coercion_to_canonical ~to_be_demoted =
    let t =
      add_alias_between_canonical_elements
        t
        ~canonical_element
        ~coercion_to_canonical:{ coercion_to_canonical; }
        ~to_be_demoted
    in
    { t;
      canonical_element;
      (* CR mshinwell: [alias_of] is not a good name. *)
      alias_of = to_be_demoted;
      coerce_alias_of_to_canonical_element = coercion_to_canonical;
    }
  in
  match canonical t element1, canonical t element2 with
  | Is_canonical canonical_element1, Is_canonical canonical_element2 ->
    let { canonical_element; to_be_demoted; } =
      choose_canonical_element_to_be_demoted t ~canonical_element1
        ~canonical_element2
    in
    let coercion_to_canonical =
      if E.equal to_be_demoted canonical_element1 then
        (* canonical_element1=element1 <--[c]-- canonical_element2=element2
           ~>
           canonical_element2 <--[inverse(c)]-- canonical_element1 *)
        C.inverse coerce_from_element2_to_element1
      else
        (* canonical_element1=element1 <--[c]-- canonical_element2=element2
           ~>
           canonical_element1 <--[c]-- canonical_element2 *)
        coerce_from_element2_to_element1 in
    wrap ~canonical_element ~coercion_to_canonical ~to_be_demoted
  | Alias_of_canonical {
      element = _element1;
      canonical_element = canonical_element1;
      coercion_to_canonical = { coercion_to_canonical = coercion_from_element1_to_canonical_element1; };
    },
    Is_canonical canonical_element2 ->
    let { canonical_element; to_be_demoted; } =
      choose_canonical_element_to_be_demoted t ~canonical_element1
        ~canonical_element2
    in
    let coercion_to_canonical =
      if E.equal to_be_demoted canonical_element1 then
        (* canonical_element1 <--[c1]-- element1
           +
           element1 <--[c]-- canonical_element2=element2
           ~>
           canonical_element2 <--[compose(inverse(c1),inverse(c))]-- canonical_element1 *)
        C.compose
          (C.inverse coercion_from_element1_to_canonical_element1)
          ~newer:(C.inverse coerce_from_element2_to_element1)
      else
        (* canonical_element1 <--[c1]-- element1
           +
           element1 <--[c]-- canonical_element2=element2
           ~>
           canonical_element1 <--[compose(c, c1)]-- canonical_element2 *)
        C.compose
          coerce_from_element2_to_element1
          ~newer:coercion_from_element1_to_canonical_element1
    in
    wrap ~canonical_element ~coercion_to_canonical ~to_be_demoted
  | Is_canonical canonical_element1,
    Alias_of_canonical {
      element = _element2;
      canonical_element = canonical_element2;
      coercion_to_canonical = { coercion_to_canonical = coercion_from_element2_to_canonical_element2; };
    } ->
    let { canonical_element; to_be_demoted; } =
      choose_canonical_element_to_be_demoted t ~canonical_element1
        ~canonical_element2
    in
    let coercion_to_canonical =
      if E.equal to_be_demoted canonical_element1 then
        (* canonical_element1=element1
           canonical_element2 <--[c2]-- element2
           +
           element1 <--[c]-- element2
           ~>
           canonical_element2 <--[compose(inverse(c), c2)]-- canonical_element1
        *)
        C.compose
          (C.inverse coerce_from_element2_to_element1)
          ~newer:coercion_from_element2_to_canonical_element2
      else
        (* canonical_element1=element1
           canonical_element2 <--[c2]-- element2
           +
           element1 <--[c]-- element2
           ~>
           canonical_element1 <--[compose(inverse(c2), c)]-- canonical_element2 *)
        C.compose
          (C.inverse coercion_from_element2_to_canonical_element2)
          ~newer:coerce_from_element2_to_element1
    in
    wrap ~canonical_element ~coercion_to_canonical ~to_be_demoted
  | Alias_of_canonical {
      element = _element1;
      canonical_element = canonical_element1;
      coercion_to_canonical = { coercion_to_canonical = coercion_from_element1_to_canonical_element1; };
    },
    Alias_of_canonical {
      element = _element2;
      canonical_element = canonical_element2;
      coercion_to_canonical = { coercion_to_canonical = coercion_from_element2_to_canonical_element2; };
    } ->
    let { canonical_element; to_be_demoted; } =
      choose_canonical_element_to_be_demoted t ~canonical_element1
        ~canonical_element2
    in
    let coercion_to_canonical =
      if E.equal to_be_demoted canonical_element1 then
        (* canonical_element1 <--[c1]-- element1
           canonical_element2 <--[c2]-- element2
           +
           element1 <--[c]-- element2
           ~>
           canonical_element2 <--[compose(inverse(c1), compose(inverse(c), c2))]--canonical_element1 *)
        C.compose
          (C.inverse coercion_from_element1_to_canonical_element1)
          ~newer:(C.compose
                    (C.inverse coerce_from_element2_to_element1)
                    ~newer:coercion_from_element2_to_canonical_element2)
      else
        (* canonical_element1 <--[c1]-- element1
           canonical_element2 <--[c2]-- element2
           +
           element1 <--[c]-- element2
           ~>
           canonical_element1 <--[compose(inverse(c2), compose(c, c1))]--canonical_element2 *)
        C.compose
          (C.inverse coercion_from_element2_to_canonical_element2)
          ~newer:(C.compose
                    coerce_from_element2_to_element1
                    ~newer:coercion_from_element1_to_canonical_element1)
    in
    wrap ~canonical_element ~coercion_to_canonical ~to_be_demoted

let add t ~element1 ~binding_time_and_mode1
      ~coerce_from_element2_to_element1
      ~element2 ~binding_time_and_mode2 =
  let original_t = t in
  let element1 = E.without_coercion element1 in
  let element2 = E.without_coercion element2 in
  let t =
    { t with binding_times_and_modes =
               E.Map.add element1 binding_time_and_mode1
                 (E.Map.add element2 binding_time_and_mode2
                    t.binding_times_and_modes);
    }
  in
  let add_result = add_alias t ~element1 ~coerce_from_element2_to_element1 ~element2 in
  if !Clflags.flambda_invariant_checks then begin
    invariant_add_result ~original_t add_result
  end;
  add_result

let mem t element =
  E.Map.mem element t.binding_times_and_modes

  (* CR mshinwell: This needs documenting.  For the moment we allow
     relations between canonical elements that are actually incomparable
     under the name mode ordering, and check in [get_canonical_element_exn]
     accordingly.  However maybe we should never allow these situations to
     arise. *)
  (*
  let canonical_mode =
    name_mode t add_result.canonical_element
  in
  let alias_of_mode = name_mode t add_result.alias_of in
  match
    Name_mode.compare_partial_order
      canonical_mode alias_of_mode
  with
  | Some _ -> add_result
  | None ->
    Misc.fatal_errorf "Canonical %a has mode incomparable with %a in:@ %a"
      Simple.print add_result.canonical_element
      Simple.print add_result.alias_of
      print t
  *)

let get_canonical_element_exn t element elt_name_mode ~min_name_mode =
  match E.Map.find element t.canonical_elements with
  | exception Not_found ->
    begin match
      Name_mode.compare_partial_order elt_name_mode min_name_mode
    with
    | None -> raise Not_found
    | Some c ->
      if c >= 0 then element, { coercion_to_canonical = C.id; }
      else raise Not_found
    end
  | canonical_element, coercion_to_canonical ->
  (*
Format.eprintf "looking for canonical for %a, candidate canonical %a, min order %a\n%!"
  Simple.print element
  Simple.print canonical_element
  Name_mode.print min_name_mode;
*)
    let find_earliest () =
      let aliases = get_aliases_of_canonical_element t ~canonical_element in
      let at_earliest_mode =
        (* May raise Not_found if no aliases exist at a mode compatible with
           min_name_mode *)
        Aliases_of_canonical_element.find_earliest_candidates_exn aliases
          ~min_name_mode
      in
      (* Aliases_of_canonical_element.find_earliest_candidates_exn only returns
         non-empty sets *)
      assert (not (E.Map.is_empty at_earliest_mode));
      E.Map.fold (fun elt coercion ((min_elt, _min_coercion) as min_binding) ->
          if defined_earlier t elt ~than:min_elt
          then elt, coercion
          else min_binding)
        at_earliest_mode
        (E.Map.min_binding at_earliest_mode)
    in
    match
      Name_mode.compare_partial_order
        (name_mode t canonical_element)
        min_name_mode
    with
    | None -> find_earliest ()
    | Some c ->
      if c >= 0 then canonical_element, coercion_to_canonical
      else find_earliest ()

let get_aliases t element =
  match canonical t element with
  | Is_canonical canonical_element ->
    let aliases =
      Aliases_of_canonical_element.all
        (get_aliases_of_canonical_element t ~canonical_element)
    in
    E.Map.add element { coercion_to_canonical = C.id; } aliases
  | Alias_of_canonical { element = _; canonical_element; coercion_to_canonical; } ->
    if !Clflags.flambda_invariant_checks then begin
      assert (not (E.equal element canonical_element))
    end;
    let aliases =
      Aliases_of_canonical_element.all
        (get_aliases_of_canonical_element t ~canonical_element)
    in
    if !Clflags.flambda_invariant_checks then begin
      assert (E.Map.mem element aliases)
    end;
    E.Map.add canonical_element coercion_to_canonical aliases

let all_ids_for_export { canonical_elements = _;
                         aliases_of_canonical_elements = _;
                         binding_times_and_modes; } =
  E.Map.fold (fun elt _binding_time_and_mode ids ->
    Exp.add ids elt)
    binding_times_and_modes
    Exp.empty
  |> Exp.to_ids_for_export

let import import_map { canonical_elements;
                        aliases_of_canonical_elements;
                        binding_times_and_modes; } =
  let import_map = Exp.Import_map.of_import_map import_map in
  let import_simple x = Exp.Import_map.simple import_map x in
  let canonical_elements =
    E.Map.fold (fun elt (canonical, coercion) acc ->
      E.Map.add (import_simple elt) (import_simple canonical, coercion) acc)
      canonical_elements
      E.Map.empty
  in
  let aliases_of_canonical_elements =
    E.Map.fold (fun canonical aliases acc ->
        E.Map.add (import_simple canonical)
          (Aliases_of_canonical_element.import import_simple aliases)
          acc)
      aliases_of_canonical_elements
      E.Map.empty
  in
  let binding_times_and_modes =
    E.Map.fold (fun simple binding_time_and_mode acc ->
        E.Map.add (import_simple simple) binding_time_and_mode acc)
      binding_times_and_modes
      E.Map.empty
  in
  { canonical_elements;
    aliases_of_canonical_elements;
    binding_times_and_modes;
  }

let merge t1 t2 =
  let canonical_elements =
    E.Map.disjoint_union
      t1.canonical_elements
      t2.canonical_elements
  in
  let aliases_of_canonical_elements =
    (* Warning: here the keys of the map can come from other
       compilation units, so we cannot assume the keys are disjoint *)
    E.Map.union (fun _simple aliases1 aliases2 ->
        Some (Aliases_of_canonical_element.merge aliases1 aliases2))
      t1.aliases_of_canonical_elements
      t2.aliases_of_canonical_elements
  in
  let symbol_data =
    Binding_time.With_name_mode.create
      Binding_time.symbols
      Name_mode.normal
  in
  let binding_times_and_modes =
    E.Map.union (fun simple data1 data2 ->
        E.pattern_match simple
          ~const:(fun _ ->
            assert (Binding_time.With_name_mode.equal data1 data2);
            Some data1)
          ~name:(fun name ->
            Name.pattern_match name
              ~var:(fun var ->
                (* TODO: filter variables on export and restore fatal_error *)
                if Binding_time.(equal (With_name_mode.binding_time data1)
                                   imported_variables)
                then Some data2
                else if Binding_time.(equal (With_name_mode.binding_time data2)
                                   imported_variables)
                then Some data1
                else
                  Misc.fatal_errorf
                    "Variable %a is present in multiple environments"
                    Variable.print var)
              ~symbol:(fun _sym ->
                assert (Binding_time.With_name_mode.equal data1 symbol_data);
                assert (Binding_time.With_name_mode.equal data2 symbol_data);
                Some data1)))
      t1.binding_times_and_modes
      t2.binding_times_and_modes
  in
  { canonical_elements;
    aliases_of_canonical_elements;
    binding_times_and_modes;
  }

let get_canonical_ignoring_name_mode t name =
  let elt = E.name name in
  match canonical t elt with
  | Is_canonical _ -> elt
  | Alias_of_canonical { canonical_element; _ } -> canonical_element

end[@@inline always]
