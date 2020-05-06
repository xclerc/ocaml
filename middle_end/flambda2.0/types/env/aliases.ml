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

(* The structure of aliases, although encoded here using maps, it probably
   best seen as a directed graph where an edge from `a` to `b` means that `a`
   is declared to be an alias of `b`. In particular, it means that `b` is older
   than `a`. It follows that the graph is without cycles.

   The map-base encoding means that we actually store edges from elements to
   their canonical representations. As a consequence, the graphs are indeed
   collection of stars where the centers are the canonical representations.

   Graph vertices are labelled with Simple.t values while edges are labelled
   with Coercion.t. In practice it means that the two simples linked by an
   edge are equal up to the coercion labelling the edge.

   Below, we use the following notation to represent an alias from `a` to `b`
   with coercion `c`:

       b <--[c]-- a
*)

let mem_key key map =
  match Simple.Map.find_opt key map with
  | None -> false
  | Some _ -> true

let map_inter =
  Simple.Map.merge (fun _key x y ->
    match x, y with
    | _, None | None, _ -> None
    | Some x, Some y ->
      (* TODO: double check *)
      assert (Reg_width_things.Coercion.equal x y);
      Some x)

  let union_function _key coercion1 coercion2 =
    (* TODO: double check *)
    assert (Reg_width_things.Coercion.equal coercion1 coercion2);
    Some coercion1

(* Aliases_of_canonical_element represents a connected component of the graph
   of aliases. The map bindings `[(e1, c1); ...; (en, cn)]` encode:

       r <--[c1]-- e1
       ...
       r <--[cn]-- en

   where `r` is the canonical representation (which is not stored in this data
   structure).

   TODO: document name mode
*)
module Aliases_of_canonical_element : sig
  type t

  val print : Format.formatter -> t -> unit

  val invariant : t -> unit

  val empty : t
  val is_empty : t -> bool

  val add : t -> Simple.t -> coercion_to_canonical:Reg_width_things.Coercion.t -> Name_mode.t -> t

  val find_earliest_candidates_exn
     : t
    -> min_name_mode:Name_mode.t
    -> Reg_width_things.Coercion.t Simple.Map.t

  val all : t -> Reg_width_things.Coercion.t Simple.Map.t

  val mem : t -> Simple.t -> bool

  val union : t -> t -> t
  val inter : t -> t -> t
  val map_coercions : t -> f:(Reg_width_things.Coercion.t -> Reg_width_things.Coercion.t) -> t
end = struct
  type t = {
    (* XXX Q? should aliases be a Simple.Set.t? *)
    aliases : Reg_width_things.Coercion.t Simple.Map.t Name_mode.Map.t;
    all : Reg_width_things.Coercion.t Simple.Map.t;
  }

  let invariant _t = ()

  let print ppf { aliases; all = _; } =
    Name_mode.Map.print (Simple.Map.print Reg_width_things.Coercion.print) ppf aliases

  let empty = {
    aliases = Name_mode.Map.empty;
    all = Simple.Map.empty;
  }

  let is_empty t = Simple.Map.is_empty t.all

  let add t elt ~coercion_to_canonical:coercion name_mode =
    if mem_key elt t.all then begin
      Misc.fatal_errorf "%a already added to [Aliases_of_canonical_element]: \
          %a"
        Simple.print elt
        print t
    end;
    let aliases =
      Name_mode.Map.update name_mode
        (function
          | None -> Some (Simple.Map.singleton elt coercion)
          | Some elts ->
            if !Clflags.flambda_invariant_checks then begin
              assert (not (mem_key elt elts))
            end;
            Some (Simple.Map.add elt coercion elts))
        t.aliases
    in
    let all = Simple.Map.add elt coercion t.all in
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
    mem_key elt t.all

  let all t = t.all

  let union t1 t2 =
    let aliases =
      Name_mode.Map.union (fun _order elts1 elts2 ->
          Some (Simple.Map.union union_function elts1 elts2))
        t1.aliases t2.aliases
    in
    let t =
      { aliases;
        all = Simple.Map.union union_function  t1.all t2.all;
      }
    in
    invariant t;
    t

  let inter t1 t2 =
    let aliases =
      Name_mode.Map.merge (fun _order elts1 elts2 ->
          match elts1, elts2 with
          | None, None | Some _, None | None, Some _ -> None
          | Some elts1, Some elts2 -> Some (map_inter elts1 elts2))
        t1.aliases t2.aliases
    in
    let t =
      { aliases;
        all = map_inter t1.all t2.all;
      }
    in
    invariant t;
    t

  let map_coercions t ~f =
    let m = Simple.Map.map f in
    let aliases = Name_mode.Map.map m t.aliases in
    let all = m t.all in
    { aliases; all; }
end

type canonical_element = {
  canonical_element : Simple.t;
  coercion_to_canonical : Reg_width_things.Coercion.t;
}

let print_canonical_element ppf { canonical_element; coercion_to_canonical; } =
  Format.fprintf ppf "(%a %a)"
    Simple.print canonical_element
    Reg_width_things.Coercion.print coercion_to_canonical

(* `canonical_elements` encoding is such that:
     Simple.Map.mem simple { canonical_element; coercion_to_canonical; }  = true
   means:
     canonical_element <--[coercion_to_canonical]-- simple
   i.e.:
     (apply_coercion simple coercion_to_canonical) = canonical_element
*)

type t = {
  canonical_elements : canonical_element Simple.Map.t;
  (* Canonical elements that have no known aliases are not included in
     [canonical_elements]. *)
  aliases_of_canonical_elements : Aliases_of_canonical_element.t Simple.Map.t;
  (* For [elt |-> aliases] in [aliases_of_canonical_elements], then
     [aliases] never includes [elt]. *)
  (* CR mshinwell: check this always holds *)
  binding_times_and_modes : Binding_time.With_name_mode.t Simple.Map.t;
  (* Binding times and name modes define an order on the elements.
     The canonical element for a set of aliases is always the minimal
     element for this order, which is different from the order used
     for creating sets and maps. *)
}

let print ppf { canonical_elements; aliases_of_canonical_elements;
                binding_times_and_modes; } =
  Format.fprintf ppf
    "@[<hov 1>(\
      @[<hov 1>(canonical_elements@ %a)@]@ \
      @[<hov 1>(aliases_of_canonical_elements@ %a)@]\
      @[<hov 1>(binding_times_and_modes@ %a)@]\
      )@]"
    (Simple.Map.print print_canonical_element) canonical_elements
    (Simple.Map.print Aliases_of_canonical_element.print)
    aliases_of_canonical_elements
    (Simple.Map.print Binding_time.With_name_mode.print)
    binding_times_and_modes

let defined_earlier t alias ~than =
  let info1 = Simple.Map.find alias t.binding_times_and_modes in
  let info2 = Simple.Map.find than t.binding_times_and_modes in
  Binding_time.strictly_earlier
    (Binding_time.With_name_mode.binding_time info1)
    ~than:(Binding_time.With_name_mode.binding_time info2)

let name_mode t elt =
  Binding_time.With_name_mode.name_mode
    (Simple.Map.find elt t.binding_times_and_modes)

let invariant t =
  if !Clflags.flambda_invariant_checks then begin
    let _all_aliases : _ Simple.Map.t =
      Simple.Map.fold (fun canonical_element aliases all_aliases ->
          Aliases_of_canonical_element.invariant aliases;
          let aliases : Reg_width_things.Coercion.t Simple.Map.t =
            Aliases_of_canonical_element.all aliases in
          if not (Simple.Map.for_all (fun elt _ ->
            defined_earlier t canonical_element ~than:elt) aliases)
          then begin
            Misc.fatal_errorf "Canonical element %a is not earlier than \
                all of its aliases:@ %a"
              Simple.print canonical_element
              print t
          end;
          if mem_key canonical_element aliases then begin
            Misc.fatal_errorf "Canonical element %a occurs in alias set:@ %a"
              Simple.print canonical_element
              (Simple.Map.print Reg_width_things.Coercion.print) aliases
          end;
          if not (Simple.Map.is_empty (map_inter aliases all_aliases)) then
          begin
            Misc.fatal_errorf "Overlapping alias sets:@ %a" print t
          end;
          Simple.Map.union union_function aliases all_aliases)
        t.aliases_of_canonical_elements
        Simple.Map.empty
    in
    ()
  end

let empty = {
  (* CR mshinwell: Rename canonical_elements, maybe to
     aliases_to_canonical_elements. *)
  canonical_elements = Simple.Map.empty;
  aliases_of_canonical_elements = Simple.Map.empty;
  binding_times_and_modes = Simple.Map.empty;
}

type canonical =
  | Is_canonical of Simple.t
  | Alias_of_canonical of {
      element : Simple.t;
      canonical_element : Simple.t;
      coercion_to_canonical : Reg_width_things.Coercion.t;
    }

let canonical t element : canonical =
  match Simple.Map.find element t.canonical_elements with
  | exception Not_found -> Is_canonical element
  | { canonical_element; coercion_to_canonical; } ->
    if !Clflags.flambda_invariant_checks then begin
      assert (not (Simple.equal element canonical_element))
    end;
    Alias_of_canonical {
      element;
      canonical_element;
      coercion_to_canonical;
    }

let get_aliases_of_canonical_element t ~canonical_element =
  match Simple.Map.find canonical_element t.aliases_of_canonical_elements with
  | exception Not_found -> Aliases_of_canonical_element.empty
  | aliases -> aliases

(* before:
   canonical_element <--[c_0]-- e_0    to_be_demoted <--[c'_0]-- e'_0
                   ^--[c_i]-- e_m                  ^--[c'_j]-- e'_n

   change:
   canonical_element <-------[c]------- to_be_demoted <--[c'_0]-- e'_0
                ^  ^--[c_0]-- e_0                   ^--[c'_j]-- e'_n
                 \--[c_i]-- e_m

   after:
   canonical_element <--[c]-- to_be_demoted
          ^  ^  ^  ^--[c_0]-- e_0
           \  \  \--[c_m]-- e_m
            \  \-- [compose(c, c'_0)]-- e'_0
             \--[compose(c, c'_n)]-- e'_n

   notation (in the function below):
   - c'_k is aliases_of_to_be_demoted
*)
let add_alias_between_canonical_elements t ~canonical_element ~to_be_demoted c =
  if Simple.equal canonical_element to_be_demoted then
    t
  else
    let aliases_of_to_be_demoted : Aliases_of_canonical_element.t =
      get_aliases_of_canonical_element t ~canonical_element:to_be_demoted
      (* change c'_j to compose(c, c'_j) *)
      |> Aliases_of_canonical_element.map_coercions ~f:(fun c'_j ->
        match Reg_width_things.Coercion.compose c c'_j with
        | Ok x -> x
        | Bottom -> assert false (*XXX*))
    in
    if !Clflags.flambda_invariant_checks then begin
      assert (not (Aliases_of_canonical_element.mem
        aliases_of_to_be_demoted canonical_element))
    end;
    let canonical_elements : canonical_element Simple.Map.t =
      t.canonical_elements
      (* add the canonical_element <--[compose(c, c'_j)]-- e'_k *)
      |> Simple.Map.fold (fun alias coercion_to_canonical canonical_elements ->
          let canonical_element = { canonical_element; coercion_to_canonical; } in
          Simple.Map.add alias canonical_element canonical_elements)
        (Aliases_of_canonical_element.all aliases_of_to_be_demoted)
      (* add the canonical_element <--[c]-- to_be_demoted *)
      |> Simple.Map.add to_be_demoted { canonical_element; coercion_to_canonical = c; }
    in
    let aliases_of_canonical_element : Aliases_of_canonical_element.t =
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
           aliases_of_to_be_demoted
           aliases_of_canonical_element)
        to_be_demoted
        (name_mode t to_be_demoted)
        ~coercion_to_canonical:c
    in
    let aliases_of_canonical_elements =
      t.aliases_of_canonical_elements
      |> Simple.Map.remove to_be_demoted
      |> Simple.Map.add (* replace *) canonical_element aliases
    in
    { canonical_elements;
      aliases_of_canonical_elements;
      binding_times_and_modes = t.binding_times_and_modes;
    }

type to_be_demoted = {
  canonical_element : Simple.t;
  to_be_demoted : Simple.t;
  coercion_to_canonical : Reg_width_things.Coercion.t;
}

(* XXX comment *)
let choose_canonical_element_to_be_demoted t ~canonical_element1 ~coercion
      ~canonical_element2 : to_be_demoted =
  if defined_earlier t canonical_element1 ~than:canonical_element2
  then
    { canonical_element = canonical_element1;
      to_be_demoted = canonical_element2;
      coercion_to_canonical = coercion;
    }
  else
    { canonical_element = canonical_element2;
      to_be_demoted = canonical_element1;
      coercion_to_canonical = Reg_width_things.Coercion.inverse coercion;
    }

(* CR mshinwell: add submodule *)
type add_result = {
  t : t;
  canonical_element : Simple.t;
  alias_of : Simple.t;
}

let invariant_add_result ~original_t { canonical_element; alias_of; t; } =
  if !Clflags.flambda_invariant_checks then begin
    invariant t;
    if not (Simple.equal canonical_element alias_of) then begin
      if not (defined_earlier t canonical_element ~than:alias_of) then begin
        Misc.fatal_errorf "Canonical element %a should be defined earlier \
            than %a after alias addition.@ Original alias tracker:@ %a@ \
            Resulting alias tracker:@ %a"
          Simple.print canonical_element
          Simple.print alias_of
          print original_t
          print t
      end
    end
  end

(* adding element1 <--[coercion]-- element2 *)
let add_alias (t : t) (element1 : Simple.t) (coercion : Reg_width_things.Coercion.t) (element2 : Simple.t) : add_result =
  match canonical t element1, canonical t element2 with
  | Is_canonical canonical_element1, Is_canonical canonical_element2 ->
    let { canonical_element; to_be_demoted; coercion_to_canonical; } =
      choose_canonical_element_to_be_demoted t ~canonical_element1 ~coercion
        ~canonical_element2
    in
    let t =
      add_alias_between_canonical_elements t ~canonical_element
        ~to_be_demoted coercion_to_canonical
    in
    { t;
      canonical_element;
      (* CR mshinwell: [alias_of] is not a good name. *)
      alias_of = to_be_demoted;
    }
  | Alias_of_canonical
        { element = element1; canonical_element = canonical_element1; coercion_to_canonical; },
      Is_canonical canonical_element2 ->
    (* canonical_element1 <--[coercion_to_canonical]-- element1 <--[coercion]-- element2
       where element2 is canonical *)
    let { canonical_element; to_be_demoted; coercion_to_canonical; } =
      choose_canonical_element_to_be_demoted t ~canonical_element1
        ~coercion:coercion_to_canonical
        ~canonical_element2
    in
    let alias_of, coercion_to_canonical =
      if Simple.equal to_be_demoted canonical_element1 then
        element1, Reg_width_things.Coercion.inverse coercion_to_canonical
      else
        canonical_element2, coercion_to_canonical
    in
    let t =
      add_alias_between_canonical_elements t ~canonical_element
        ~to_be_demoted
        coercion_to_canonical
    in
    { t;
      canonical_element;
      alias_of;
    }
  | Is_canonical canonical_element2,
      Alias_of_canonical
        { element = element1; canonical_element = canonical_element1; coercion_to_canonical; } ->
    (* TODO: merge back with previous case *)
    let { canonical_element; to_be_demoted; coercion_to_canonical; } =
      choose_canonical_element_to_be_demoted t ~canonical_element1
        ~coercion:coercion_to_canonical
        ~canonical_element2
    in
    let alias_of, coercion_to_canonical =
      if Simple.equal to_be_demoted canonical_element1 then
        element1, coercion_to_canonical
      else
        canonical_element2, Reg_width_things.Coercion.inverse coercion_to_canonical
    in
    let t =
      add_alias_between_canonical_elements t ~canonical_element
        ~to_be_demoted
        coercion_to_canonical
    in
    { t;
      canonical_element;
      alias_of;
    }
  | Alias_of_canonical
        { element = element1; canonical_element = canonical_element1; coercion_to_canonical = _; },
      Alias_of_canonical
        { element = element2; canonical_element = canonical_element2; coercion_to_canonical = _; }
      ->
    let { canonical_element; to_be_demoted; coercion_to_canonical; } =
      choose_canonical_element_to_be_demoted t ~canonical_element1
        ~canonical_element2
        ~coercion
    in
    let alias_of =
      if Simple.equal to_be_demoted canonical_element1 then
        element1
      else
        element2
    in
    let t =
      add_alias_between_canonical_elements t ~canonical_element
        ~to_be_demoted
        coercion_to_canonical
    in
    { t;
      canonical_element;
      alias_of;
    }

let add t element1 binding_time_and_mode1
      coercion
      element2 binding_time_and_mode2 =
  let original_t = t in
  let t =
    let element1 = Simple.without_coercion element1 in
    let element2 = Simple.without_coercion element2 in
    { t with binding_times_and_modes =
               Simple.Map.add element1 binding_time_and_mode1
                 (Simple.Map.add element2 binding_time_and_mode2
                    t.binding_times_and_modes);
    }
  in
  let add_result = add_alias t element1 coercion element2 in
  if !Clflags.flambda_invariant_checks then begin
    invariant_add_result ~original_t add_result
  end;
  add_result

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
  match Simple.Map.find element t.canonical_elements with
  | exception Not_found ->
    begin match
      Name_mode.compare_partial_order elt_name_mode min_name_mode
    with
    | None -> raise Not_found
    | Some c ->
      if c >= 0 then element
      else raise Not_found
    end
  | ({ canonical_element; _ } : canonical_element) ->
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
      assert (not (Simple.Map.is_empty at_earliest_mode));
      let s, c =
        Simple.Map.fold (fun elt coercion (min_elt, min_coercion) ->
          if defined_earlier t elt ~than:min_elt
          then (elt, coercion)
          else (min_elt, min_coercion))
        at_earliest_mode
        (Simple.Map.min_binding at_earliest_mode) in
      Simple.apply_coercion s ~newer_coercion:(Some c)
      |> Option.get (*XXX*)
    in
    match
      Name_mode.compare_partial_order
        (name_mode t canonical_element)
        min_name_mode
    with
    | None -> find_earliest ()
    | Some c ->
      if c >= 0 then canonical_element
      else find_earliest ()

let get_aliases t element =
  let to_set m =
    Simple.Map.fold (fun (simple : Simple.t) (coercion : Reg_width_things.Coercion.t) acc ->
      Simple.Set.add (Option.get (*XXX*) @@ Simple.apply_coercion simple ~newer_coercion:(Some coercion)) acc)
      m
      Simple.Set.empty in
  match canonical t element with
  | Is_canonical canonical_element ->
    let aliases =
      Aliases_of_canonical_element.all
        (get_aliases_of_canonical_element t ~canonical_element)
      |> to_set
    in
    Simple.Set.add element aliases
  | Alias_of_canonical { element = _; canonical_element; coercion_to_canonical; } ->
    if !Clflags.flambda_invariant_checks then begin
      assert (not (Simple.equal element canonical_element))
    end;
    let aliases =
      Simple.Map.add
        canonical_element
        coercion_to_canonical
        (Aliases_of_canonical_element.all
           (get_aliases_of_canonical_element t ~canonical_element))
      |> to_set
    in
    if !Clflags.flambda_invariant_checks then begin
      assert (Simple.Set.mem element aliases)
    end;
    aliases
