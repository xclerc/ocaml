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

(* CR mshinwell: turn this off once namespacing issues sorted *)
[@@@ocaml.warning "-44-45"]

module Float = Numbers.Float
module Int32 = Numbers.Int32
module Int64 = Numbers.Int64

module Boxed_number_kind : sig
  type t =
    | Float
    | Int32
    | Int64
    | Nativeint

  let print ppf t =
    match t with
    | Float -> fprintf ppf "float"
    | Int32 -> fprintf ppf "int32"
    | Int64 -> fprintf ppf "int64"
    | Nativeint -> fprintf ppf "nativeint"
end

type unresolved_value =
  | Set_of_closures_id of Set_of_closures_id.t
  | Symbol of Symbol.t

type unknown_because_of =
  | Unresolved_value of unresolved_value
  | Other

(** Types from other compilation units are loaded lazily.  There are two
    kinds of cross-compilation unit reference to be resolved: via
    [Export_id.t] values and via [Symbol.t] values. *)
type have_not_yet_tried_to_import =
  | Export_id of Export_id.t
  | Symbol of Symbol.t

type specialised_to = {
  var : Variable.t option;
  projection : Projection.t option;
}

type specialised_args = specialised_to Variable.Map.t

(* A value of type [T.t] corresponds to an "approximation" of the result of
    a computation in the program being compiled.  That is to say, it
    represents what knowledge we have about such a result at compile time.
    The simplification pass exploits this information to partially evaluate
    computations.

    At a high level, an approximation for a value [v] has three parts:
    - the "description" (for example, "the constant integer 42");
    - an optional variable;
    - an optional symbol or symbol field.
    If the variable (resp. symbol) is present then that variable (resp.
    symbol) may be used to obtain the value [v].

    The exact semantics of the variable and symbol fields follows.

    Approximations are deduced at particular points in an expression tree,
    but may subsequently be propagated to other locations.

    At the point at which an approximation is built for some value [v], we can
    construct a set of variables (call the set [S]) that are known to alias the
    same value [v].  Each member of [S] will have the same or a more precise
    [descr] field in its approximation relative to the approximation for [v].
    (An increase in precision may currently be introduced for pattern
    matches.)  If [S] is non-empty then it is guaranteed that there is a
    unique member of [S] that was declared in a scope further out ("earlier")
    than all other members of [S].  If such a member exists then it is
    recorded in the [var] field.  Otherwise [var] is [None].

    Analogous to the construction of the set [S], we can construct a set [T]
    consisting of all symbols that are known to alias the value whose
    approximation is being constructed.  If [T] is non-empty then the
    [symbol] field is set to some member of [T]; it does not matter which
    one.  (There is no notion of scope for symbols.)

    Note about mutable blocks:

    Mutable blocks are always represented by [Unknown] or
    [Bottom].  Any other approximation could leave the door open to
    a miscompilation.   Such bad scenarios are most likely a user using
    [Obj.magic] or [Obj.set_field] in an inappropriate situation.
    Such a situation might be:
    [let x = (1, 1) in
     Obj.set_field (Obj.repr x) 0 (Obj.repr 2);
     assert(fst x = 2)]
    The user would probably expect the assertion to be true, but the
    compiler could in fact propagate the value of [x] across the
    [Obj.set_field].

    Insisting that mutable blocks have [Unknown] or [bottom]
    approximations certainly won't always prevent this kind of error, but
    should help catch many of them.

    It is possible that there may be some false positives, with correct
    but unreachable code causing this check to fail.  However the likelihood
    of this seems sufficiently low, especially compared to the advantages
    gained by performing the check, that we include it.

    An example of a pattern that might trigger a false positive is:
    [type a = { a : int }
     type b = { mutable b : int }
     type _ t =
       | A : a t
       | B : b t
     let f (type x) (v:x t) (r:x) =
       match v with
       | A -> r.a
       | B -> r.b <- 2; 3

    let v =
    let r =
      ref A in
      r := A; (* Some pattern that the compiler can't understand *)
      f !r { a = 1 }]
    When inlining [f], the B branch is unreachable, yet the compiler
    cannot prove it and must therefore keep it.
*)

module rec T : sig
  type value_string = {
    (* CR-soon mshinwell: use variant *)
    contents : string option; (* None if unknown or mutable *)
    size : int;
  }

  (** The type of an Flambda term. *)
  type ('decls, 'freshening) t = {
    descr : descr;
    var : (Variable.t * (Projection.t option)) option;
    symbol : (Symbol.t * int option) option;
  } 

  (** Types are equipped with a subtyping relation given by a partial order.
      For the purposes of this order, [Load_lazily] is excluded, since that
      will have been squashed (either yielding a known type or an [Unknown])
      by the time we make a judgement about the order.

      [Bottom] is, well, bottom.
      Each [Unknown (k, _)] gives a top element.

      [Bottom] means "no value can flow to this point".
      [Unknown (k, _)] means "any value of kind [k] might flow to this point".
  *)
  (* CR mshinwell: After the closure reworking patch has been merged and
     the work on classic mode closure approximations has been merged (the
     latter introducing a type of function declarations in this module), then
     the only circularity between this type and Flambda will be for
     Flambda.expr on function bodies. *)
  and ('decls, 'freshening) descr = private 
    | Unknown of Flambda_kind.t * unknown_because_of
    | Union of Unionable.t
    | Unboxed_float of Float.Set.t
    | Unboxed_int32 of Int32.Set.t
    | Unboxed_int64 of Int64.Set.t
    | Unboxed_nativeint of Nativeint.Set.t
    | Boxed_number of boxed_number_kind * t
    | Set_of_closures of ('decls, 'freshening) set_of_closures
    | Closure of ('decls, 'freshening) closure
    | String of string
    | Float_array of float_array
    | Bottom
    | Load_lazily of load_lazily

  and ('decls, 'freshening) closure = {
    potential_closures : ('decls, 'freshening) t Closure_id.Map.t;
    (** Map of closures ids to set of closures *)
  } [@@unboxed]

  (* CR-soon mshinwell: add support for the approximations of the results, so we
     can do all of the tricky higher-order cases. *)
  and ('decls, 'freshening) set_of_closures = private {
    function_decls : 'decls;
    bound_vars : t Var_within_closure.Map.t;
    invariant_params : Variable.Set.t Variable.Map.t lazy_t;
    size : int option Variable.Map.t lazy_t;
    (** For functions that are very likely to be inlined, the size of the
        function's body. *)
    specialised_args : specialised_args;
    freshening : 'freshening;
    (** Any freshening that has been applied to [function_decls]. *)
    direct_call_surrogates : Closure_id.t Closure_id.Map.t;
  }

  and float_array_contents =
    | Contents of t array
    | Unknown_or_mutable

  and float_array = {
    contents : float_array_contents;
    size : int;
  }

  and specialised_args = specialised_to Variable.Map.t

  val kind : t -> Flambda_kind.t

  val join : really_import_approx:(t -> t) -> t -> t -> t

  val equal_boxed_int : 'a boxed_int -> 'a -> 'b boxed_int -> 'b -> bool

  val print : Format.formatter -> t -> unit
  val print_descr : Format.formatter -> descr -> unit
  val print_value_set_of_closures
    : Format.formatter
    -> value_set_of_closures
    -> unit
end = struct
  include T

  let kind t ~really_import_approx : Flambda_kind.t =
    match t.descr with
    | Unknown (kind, _) -> kind
    | Float _ -> Unboxed_float
    | Int32 _ -> Unboxed_int32
    | Int64 _ -> Unboxed_int64
    | Nativeint _ -> Unboxed_nativeint
    | Union _
    | Boxed_number _
    | Set_of_closures _
    | Closure _
    | String _
    | Float_array _ -> Other
    | Bottom -> Bottom
    | Load_lazily _ -> kind (really_import_approx t) ~really_import_approx

  let kind_exn t =
    let really_import_approx t =
      Misc.fatal_errorf "With_free_variables.create_let_reusing_body: \
          Flambda type is not fully resolved: %a"
        Flambda_type0.T.print t
    in
    kind t ~really_import_approx

  (* Closures and set of closures descriptions cannot be merged.

    let f x =
      let g y -> x + y in
      g
    in
    let v =
      if ...
      then f 1
      else f 2
    in
    v 3

    The approximation for [f 1] and [f 2] could both contain the
    description of [g]. But if [f] where inlined, a new [g] would
    be created in each branch, leading to incompatible description.
    And we must never make the descrition for a function less
    precise that it used to be: its information are needed for
    rewriting [Project_var] and [Project_closure] constructions
    in [Simplify].
  *)
  let rec join_descr ~really_import_approx d1 d2 =
    match d1, d2 with
    | Union union1, Union union2 ->
      begin match Unionable.join union1 union2 ~really_import_approx with
      | Ok union -> Union union
      | Ill_typed_code -> Bottom
      | Anything -> Unknown Other
      end
    | Float fs1, Float fs2 -> Float (Float.Set.union fs1 fs2)
    | Int32 is1, Int32 is2 -> Int32 (Int32.Set.union is1 is2)
    | Int64 is1, Int64 is2 -> Int64 (Int64.Set.union is1 is2)
    | Nativeint is1, Nativeint is2 -> Nativeint (Nativeint.Set.union is1 is2)
    | Boxed_number (Float, t1), Boxed_number (Float, t2)
      Boxed_number (Float, join t1 t2)
    | Boxed_number (Int32, t1), Boxed_number (Int32, t2)
      Boxed_number (Int32, join t1 t2)
    | Boxed_number (Int64, t1), Boxed_number (Int64, t2)
      Boxed_number (Int64, join t1 t2)
    | Boxed_number (Nativeint, t1), Boxed_number (Nativeint, t2)
      Boxed_number (Nativeint, join t1 t2)
    | Extern e1, Extern e2 when Export_id.equal e1 e2 -> d1
    | Symbol s1, Symbol s2 when Symbol.equal s1 s2 -> d1
    | Closure { potential_closures = map1 },
      Closure { potential_closures = map2 } ->
      let potential_closures =
        Closure_id.Map.union_merge
          (* CR pchambart:
            merging the closure value might loose information in the
            case of one branch having the approximation and the other
            having 'Unknown'. We could imagine such as

            {[if ... then M1.f else M2.f]}

            where M1 is where the function is defined and M2 is

            {[let f = M3.f]}

            and M3 is

            {[let f = M1.f]}

            with the cmx for M3 missing

            Since we know that the approximation comes from the same
            value, we know that both version provide additional
            information on the value. Hence what we really want is an
            approximation intersection, not an union (that this join
            is). *)
          (join ~really_import_approx)
          map1 map2
      in
      Closure { potential_closures }
    | _ -> Unknown Other

  and join ~really_import_approx a1 a2 =
    if Flambda_kind.compatible a1 a2 ~really_import_approx then begin
      match a1, a2 with
      | { descr = Bottom }, _ -> a2
      | _, { descr = Bottom } -> a1
      | { descr = (Symbol _ | Extern _) }, _
      | _, { descr = (Symbol _ | Extern _) } ->
        join ~really_import_approx
          (really_import_approx a1) (really_import_approx a2)
      | _ ->
          let var =
            match a1.var, a2.var with
            | None, _ | _, None -> None
            | Some v1, Some v2 ->
              if Variable.equal v1 v2 then Some v1
              else None
          in
          let symbol =
            match a1.symbol, a2.symbol with
            | None, _ | _, None -> None
            | Some (v1, field1), Some (v2, field2) ->
              if Symbol.equal v1 v2 then
                match field1, field2 with
                | None, None -> a1.symbol
                | Some f1, Some f2 when f1 = f2 -> a1.symbol
                | _ -> None
              else None
          in
          let descr = join_descr ~really_import_approx a1.descr a2.descr in
          match descr with
          | Union union when not (Unionable.is_singleton union) ->
            (* CR mshinwell: Think about whether we need to do better here *)
            { descr;
              var = None;
              symbol = None;
            }
          | _ ->
            { descr;
              var;
              symbol;
            }
    end else begin
      Misc.fatal_errorf "Values with incompatible kinds must not flow to \
          the same place: %a and %a"
        print a1
        print a2
    end

  let print_value_set_of_closures ppf
        { function_decls = { funs }; invariant_params; freshening; _ } =
    Format.fprintf ppf
      "(set_of_closures:@ %a invariant_params=%a freshening=%a)"
      (fun ppf -> Variable.Map.iter (fun id _ -> Variable.print ppf id)) funs
      (Variable.Map.print Variable.Set.print) (Lazy.force invariant_params)
      Freshening.Project_var.print freshening

  let print_unresolved_value ppf (unresolved : unresolved_value) =
    match unresolved with
    | Set_of_closures_id set ->
      Format.fprintf ppf "Set_of_closures_id %a" Set_of_closures_id.print set
    | Symbol symbol ->
      Format.fprintf ppf "Symbol %a" Symbol.print symbol

  let rec print_descr ppf = function
    | Union union -> Unionable.print ppf union
    | Unknown (kind, reason) ->
      begin match reason with
      | Unresolved_value value ->
        Format.fprintf ppf "?(%a)(due to unresolved %a)"
          Flambda_kind.print kind
          print_unresolved_value value
      | Other -> Format.fprintf ppf "?(%a)" Flambda_kind.print kind
      end;
    | Bottom -> Format.fprintf ppf "bottom"
    | Extern id -> Format.fprintf ppf "_%a_" Export_id.print id
    | Symbol sym -> Format.fprintf ppf "%a" Symbol.print sym
    | Closure { potential_closures } ->
      Format.fprintf ppf "(closure:@ @[<2>[@ ";
      Closure_id.Map.iter (fun closure_id set_of_closures ->
        Format.fprintf ppf "%a @[<2>from@ %a@];@ "
          Closure_id.print closure_id
          print set_of_closures)
        potential_closures;
      Format.fprintf ppf "]@])";
    | Set_of_closures set_of_closures ->
      print_value_set_of_closures ppf set_of_closures
    | Unresolved value ->
      Format.fprintf ppf "(unresolved %a)" print_unresolved_value value
    | Float fs -> Format.fprintf ppf "float(%a)" Float.Set.print fs
    | Int32 ns -> Format.fprintf ppf "int32(%a)" Int32.Set.print ns
    | Int64 ns -> Format.fprintf ppf "int64(%a)" Int64.Set.print ns
    | Nativeint ns -> Format.fprintf ppf "nativeint(%a)" Nativeint.Set.print ns
    | Boxed_number (bn, t) ->
      Format.fprintf ppf "box_%a(%a)"
        Boxed_number_kind.print bn
        print t
    | String { contents; size } -> begin
        match contents with
        | None ->
            Format.fprintf ppf "string %i" size
        | Some s ->
            let s =
              if size > 10
              then String.sub s 0 8 ^ "..."
              else s
            in
            Format.fprintf ppf "string %i %S" size s
      end
    | Float_array float_array ->
      begin match float_array.contents with
      | Unknown_or_mutable ->
        Format.fprintf ppf "float_array %i" float_array.size
      | Contents _ ->
        Format.fprintf ppf "float_array_imm %i" float_array.size
      end

  and print ppf { descr; var; symbol; } =
    let print ppf = function
      | None -> Symbol.print_opt ppf None
      | Some (sym, None) -> Symbol.print ppf sym
      | Some (sym, Some field) ->
          Format.fprintf ppf "%a.(%i)" Symbol.print sym field
    in
    Format.fprintf ppf "{ descr=%a var=%a symbol=%a }"
      print_descr descr
      Variable.print_opt var
      print symbol
end and Unionable : sig
  module Immediate : sig
    type t = private
      | Int of int
      | Char of char
      | Constptr of int

    include Identifiable.S with type t := t

    val represents : t -> int
  end

  type blocks = T.t array Tag.Scannable.Map.t

  (* Values of type [t] represent unions of approximations, that is to say,
     disjunctions of properties known to hold of a value at one or more of
     its use points.

     Other representations are possible, but this one has two nice properties:
     1. It doesn't involve any comparison on values of type [T.t].
     2. It lines up with the classification of approximations required when
        unboxing (cf. [Unbox_one_variable]). *)
  type t =
    | Blocks of blocks
    | Blocks_and_immediates of blocks * Immediate.Set.t
    | Immediates of Immediate.Set.t

  val invariant : t -> unit

  val print : Format.formatter -> t -> unit

  val is_singleton : t -> bool

  val value_int : int -> t
  val value_char : char -> t
  val value_constptr : int -> t
  val value_block : Tag.Scannable.t -> T.t array -> t

  val useful : t -> bool

  type 'a or_bottom =
    | Anything
    | Ok of 'a
    | Ill_typed_code

  val join : t -> t -> really_import_approx:(T.t -> T.t) -> t or_bottom

  type singleton = private
    | Block of Tag.Scannable.t * T.t array
    | Int of int
    | Char of char
    | Constptr of int

  val flatten : t -> singleton or_bottom

  val maybe_is_immediate_value : t -> int -> bool

  val ok_for_variant : t -> bool

  val as_int : t -> int option
  val size_of_block : t -> int option

  val invalid_to_mutate : t -> bool
end = struct
  type 'a or_bottom =  (* CR mshinwell: rename type *)
    | Anything
    | Ok of 'a
    | Ill_typed_code

  module Immediate = struct
    type t =
      | Int of int
      | Char of char
      | Constptr of int

    include Identifiable.Make (struct
      type nonrec t = t

      let compare = Pervasives.compare
      let equal t1 t2 = (compare t1 t2 = 0)
      let hash = Hashtbl.hash

      let print ppf t =
        match t with
        | Int i -> Format.pp_print_int ppf i
        | Char c -> Format.fprintf ppf "%c" c
        | Constptr i -> Format.fprintf ppf "%ia" i

      let output _ _ = Misc.fatal_error "Not implemented"
    end)

    let join t1 t2 : t or_bottom =
      if equal t1 t2 then Ok t1
      else Anything

    let join_set ts =
      let t = Set.choose ts in
      let ts = Set.remove t ts in
      Set.fold (fun t ts ->
          match ts with
          | Ok ts -> join t ts
          | Ill_typed_code -> Ill_typed_code
          | Anything -> Anything)
        ts (Ok t)

    let represents = function
      | Int n | Constptr n -> n
      | Char c -> Char.code c
  end

  type blocks = T.t array Tag.Scannable.Map.t

  let print_blocks ppf (by_tag : blocks) =
    let print_binding ppf (tag, fields) =
      Format.fprintf ppf "@[[|%a: %a|]@]"
        Tag.Scannable.print tag
        (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf "; ")
          T.print)
        (Array.to_list fields)
    in
    Format.fprintf ppf "@[%a@]"
      (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf " U ")
        print_binding)
      (Tag.Scannable.Map.bindings by_tag)

  type t =
    | Blocks of blocks
    | Blocks_and_immediates of blocks * Immediate.Set.t
    | Immediates of Immediate.Set.t

  let invariant t =
    if !Clflags.flambda_invariant_checks then begin
      match t with
      | Blocks blocks -> assert (Tag.Scannable.Map.cardinal blocks >= 1)
      | Blocks_and_immediates (blocks, immediates) ->
        assert (Tag.Scannable.Map.cardinal blocks >= 1);
        assert (Immediate.Set.cardinal immediates >= 1)
      | Immediates immediates ->
        assert (Immediate.Set.cardinal immediates >= 1)
    end

  let print ppf t =
    match t with
    | Blocks by_tag ->
      Format.fprintf ppf "@[(blocks (%a))@]"
        print_blocks by_tag
    | Blocks_and_immediates (by_tag, imms) ->
      Format.fprintf ppf "@[(blocks (%a)) U (immediates (%a))@]"
        print_blocks by_tag
        Immediate.Set.print imms
    | Immediates imms ->
      Format.fprintf ppf "@[(immediates (%a))@]"
        Immediate.Set.print imms

  let is_singleton t =
    invariant t;
    match t with
    | Blocks blocks -> Tag.Scannable.Map.cardinal blocks = 1
    | Blocks_and_immediates (blocks, imms) ->
      (Tag.Scannable.Map.cardinal blocks = 1 && Immediate.Set.is_empty imms)
        || (Tag.Scannable.Map.is_empty blocks && Immediate.Set.cardinal imms = 1)
    | Immediates imms -> Immediate.Set.cardinal imms = 1

  let value_int i =
    Immediates (Immediate.Set.singleton (Int i))

  let value_char c =
    Immediates (Immediate.Set.singleton (Char c))

  let value_constptr p =
    Immediates (Immediate.Set.singleton (Constptr p))

  let value_block tag fields =
    Blocks (Tag.Scannable.Map.add tag fields Tag.Scannable.Map.empty)

  (* CR mshinwell: Bad name? *)
  let maybe_is_immediate_value t i =
    invariant t;
    match t with
    | Blocks _ -> false
    | Blocks_and_immediates (_, imms) | Immediates imms ->
      Immediate.Set.exists (fun (imm : Immediate.t) ->
          match imm with
          | Int i' when i = i' -> true
          | Int _ -> false
          | Char c when i = Char.code c -> true
          | Char _ -> false
          | Constptr p when i = p -> true
          | Constptr _ -> false)
        imms

  let ok_for_variant t =
    invariant t;
    (* CR mshinwell: Shouldn't this function say "false" for e.g.
       (Int 0) u (Constptr 0) ? *)
    match t with
    | Blocks by_tag | Blocks_and_immediates (by_tag, _) ->
      (* CR mshinwell: Should the failure of this check be an error?
         Perhaps the invariants pass should check "makeblock" to ensure it's
         not used at or above No_scan_tag either *)
      Tag.Scannable.Map.for_all (fun tag _contents ->
          (Tag.Scannable.to_int tag) < Obj.no_scan_tag)
        by_tag
    | Immediates _imms -> true

  let as_int t =
    invariant t;
    let check_immediates imms =
      (* CR mshinwell: Should this include Char and Constptr? *)
      match Immediate.Set.elements imms with
      | [Int i] -> Some i
      | _ -> None
    in
    match t with
    | Blocks _ -> None
    | Blocks_and_immediates (by_tag, imms) ->
      if not (Tag.Scannable.Map.is_empty by_tag) then None
      else check_immediates imms
    | Immediates imms -> check_immediates imms

  let join (t1 : t) (t2 : t) ~really_import_approx : t or_bottom =
    invariant t1;
    invariant t2;
    let get_immediates t =
      match t with
      | Blocks _ -> Immediate.Set.empty
      | Blocks_and_immediates (_, imms) | Immediates imms -> imms
    in
    let immediates_t1 = get_immediates t1 in
    let immediates_t2 = get_immediates t2 in
    let immediates = Immediate.Set.union immediates_t1 immediates_t2 in
    let get_blocks t =
      match t with
      | Blocks by_tag | Blocks_and_immediates (by_tag, _) -> by_tag
      | Immediates _ -> Tag.Scannable.Map.empty
    in
    let blocks_t1 = get_blocks t1 in
    let blocks_t2 = get_blocks t2 in
    let anything = ref false in
    let blocks =
      Tag.Scannable.Map.union (fun _tag fields1 fields2 ->
          if Array.length fields1 <> Array.length fields2 then begin
            anything := true;
            None
          end else begin
            Some (Array.map2 (fun field existing_field ->
                T.join field existing_field ~really_import_approx)
              fields1 fields2)
          end)
        blocks_t1 blocks_t2
    in
    if !anything then Anything
    else if Immediate.Set.is_empty immediates then Ok (Blocks blocks)
    else if Tag.Scannable.Map.is_empty blocks then Ok (Immediates immediates)
    else Ok (Blocks_and_immediates (blocks, immediates))

  let useful t =
    (* CR mshinwell: some of these are necessarily [true] when [invariant]
       holds *)
    invariant t;
    match t with
    | Blocks blocks -> not (Tag.Scannable.Map.is_empty blocks)
    | Blocks_and_immediates (blocks, immediates) ->
      (not (Tag.Scannable.Map.is_empty blocks))
        || (not (Immediate.Set.is_empty immediates))
    | Immediates immediates -> not (Immediate.Set.is_empty immediates)

  type singleton =
    | Block of Tag.Scannable.t * T.t array
    | Int of int
    | Char of char
    | Constptr of int

  let rec flatten t : singleton or_bottom =
    invariant t;
    match t with
    | Blocks by_tag ->
      begin match Tag.Scannable.Map.bindings by_tag with
      | [tag, fields] -> Ok (Block (tag, fields))
      | _ -> Anything
      end
    | Blocks_and_immediates (by_tag, imms) ->
      if Tag.Scannable.Map.is_empty by_tag then flatten (Immediates imms)
      else if Immediate.Set.is_empty imms then flatten (Blocks by_tag)
      else Anything
    | Immediates imms ->
      match Immediate.join_set imms with
      | Ok (Int i) -> Ok (Int i)
      | Ok (Char c) -> Ok (Char c)
      | Ok (Constptr p) -> Ok (Constptr p)
      | Ill_typed_code -> Ill_typed_code
      | Anything -> Anything

  let size_of_block t =
    invariant t;
    match t with
    | Blocks by_tag ->
      let sizes =
        List.map (fun (_tag, fields) -> Array.length fields)
          (Tag.Scannable.Map.bindings by_tag)
      in
      let sizes = Numbers.Int.Set.of_list sizes in
      begin match Numbers.Int.Set.elements sizes with
      | [] -> Some 0
      | [size] -> Some size
      | _ -> None
      end
    | Blocks_and_immediates _ | Immediates _ -> None

  let invalid_to_mutate t =
    invariant t;
    match size_of_block t with
    | None -> true
    | Some 0 -> false  (* empty arrays are treated as mutable *)
    | Some _ -> true
end

let equal_boxed_int = T.equal_boxed_int
let print_value_set_of_closures = T.print_value_set_of_closures
let print_descr = T.print_descr
let print = T.print
let join = T.join

(* CR mshinwell: Sort out all this namespacing crap *)

type value_string = T.string = {
  (* CR-soon mshinwell: use variant *)
  contents : string option; (* None if unknown or mutable *)
  size : int;
}

type t = T.t = {
  descr : descr;
  var : Variable.t option;
  symbol : (Symbol.t * int option) option;
}

and descr = T.descr =
  | Unknown of Flambda_kind.t * unknown_because_of
  | Union of Unionable.t
  | Float of Float.Set.t
  | Int32 of Int32.Set.t
  | Int64 of Int64.Set.t
  | Nativeint of Nativeint.Set.t
  | Boxed_number of boxed_number * t
  | Set_of_closures of set_of_closures
  | Closure of closure
  | String of T.string
  | Float_array of float_array
  | Extern of Export_id.t
  | Symbol of Symbol.t
  | Unresolved of unresolved_value
    (** No description was found for this symbol *)
  | Bottom

and closure = T.closure = {
  potential_closures : t Closure_id.Map.t;
} [@@unboxed]

and set_of_closures = T.set_of_closures = {
  function_decls : Flambda.function_declarations;
  bound_vars : t Var_within_closure.Map.t;
  invariant_params : Variable.Set.t Variable.Map.t lazy_t;
  size : int option Variable.Map.t lazy_t;
  specialised_args : Flambda.specialised_args;
  freshening : Freshening.Project_var.t;
  direct_call_surrogates : Closure_id.t Closure_id.Map.t;
}

and float_array_contents = T.float_array_contents =
  | Contents of t array
  | Unknown_or_mutable

and float_array = T.float_array = {
  ontents : float_array_contents;
  size : int;
}

let descr t = t.descr
let descrs ts = List.map (fun t -> t.descr) ts

let approx descr = { descr; var = None; symbol = None }

let augment_with_variable t var = { t with var = Some var }
let augment_with_symbol t symbol = { t with symbol = Some (symbol, None) }
let augment_with_symbol_field t symbol field =
  match t.symbol with
  | None -> { t with symbol = Some (symbol, Some field) }
  | Some _ -> t

let replace_description t descr = { t with descr }

let unknown kind reason = approx (Unknown (kind, reason))
let int i = approx (Union (Unionable.int i))
let char i = approx (Union (Unionable.char i))
let constptr i = approx (Union (Unionable.constptr i))
let boxed_float f = approx (Boxed_float (Some f))
let boxed_int32 i = approx (Boxed_number (Int32, unboxed_int32 i))
let boxed_int64 i = approx (Boxed_number (Int64, unboxed_int64 i))
let boxed_nativeint i = approx (Boxed_number (Nativeint, unboxed_nativeint i))

let any_float = approx (Boxed_float None)
let any_unboxed_float = approx (Unknown (Unboxed_float, Other))
let any_unboxed_int32 = approx (Unknown (Unboxed_int32, Other))
let any_unboxed_int64 = approx (Unknown (Unboxed_int64, Other))
let any_unboxed_nativeint = approx (Unknown (Unboxed_nativeint, Other))

let closure ?closure_var ?set_of_closures_var ?set_of_closures_symbol
      closures =
  let approx_set_of_closures value_set_of_closures =
    { descr = Set_of_closures value_set_of_closures;
      var = set_of_closures_var;
      symbol = Misc.may_map (fun s -> s, None) set_of_closures_symbol;
    }
  in
  let potential_closures =
    Closure_id.Map.map approx_set_of_closures closures
  in
  { descr = Closure { potential_closures };
    var = closure_var;
    symbol = None;
  }

let create_set_of_closures
      ~(function_decls : Flambda.function_declarations) ~bound_vars
      ~invariant_params ~specialised_args ~freshening
      ~direct_call_surrogates =
  let size =
    lazy (
      let functions = Variable.Map.keys function_decls.funs in
      Variable.Map.map (fun (function_decl : Flambda.function_declaration) ->
          let params = Parameter.Set.vars function_decl.params in
          let free_vars =
            Variable.Set.diff
              (Variable.Set.diff function_decl.free_variables params)
              functions
          in
          let num_free_vars = Variable.Set.cardinal free_vars in
          let max_size =
            Inlining_cost.maximum_interesting_size_of_function_body
              num_free_vars
          in
          Inlining_cost.lambda_smaller' function_decl.body ~than:max_size)
        function_decls.funs)
  in
  { function_decls;
    bound_vars;
    invariant_params;
    size;
    specialised_args;
    freshening;
    direct_call_surrogates;
  }

let update_freshening_of_set_of_closures set_of_closures
      ~freshening =
  (* CR-someday mshinwell: We could maybe check that [freshening] is
     reasonable. *)
  { set_of_closures with freshening; }

let set_of_closures ?set_of_closures_var set_of_closures =
  { descr = Set_of_closures set_of_closures;
    var = set_of_closures_var;
    symbol = None;
  }

let block t b =
  (* Avoid having multiple possible approximations for e.g. [Int64] values. *)
  if Tag.Scannable.if_at_or_above_no_scan_tag then unknown Other
  else approx (Union (Unionable.block t b))

let extern ex = approx (Extern ex)
let symbol sym =
  { (approx (Symbol sym)) with symbol = Some (sym, None) }
let bottom = approx Bottom
let unresolved value = approx (Unresolved value)

let string size contents = approx (String {size; contents })
let mutable_float_array ~size =
  approx (Float_array { contents = Unknown_or_mutable; size; } )
let immutable_float_array (contents:t array) =
  let size = Array.length contents in
  let contents =
    Array.map (fun t -> augment_with_kind t Pfloatval) contents
  in
  approx (Float_array { contents = Contents contents; size; } )

let refine_using_value_kind t (kind : Lambda.value_kind) =
  match kind with
  | Pgenval -> t
  | Pfloatval ->
    begin match t.descr with
    | Boxed_number (Float, { descr = Float _; _ }) ->
      t
    | Unknown (Other, _) | Unresolved _ ->
      { t with descr = Boxed_number (Float, value_unknown Float Other); }
    | Unknown (Unboxed_float | Unboxed_int32 | Unboxed_int64
        | Unboxed_nativeint, _) ->
      Misc.fatal_errorf "An unboxed value cannot have Pfloatval kind: %a"
        print t
    | Union _
    | Float _
    | Int32 _
    | Int64 _
    | Nativeint _
    | Boxed_number _
    | Set_of_closures _
    | Closure _
    | String _
    | Float_array _
    | Bottom ->
      (* Unreachable *)
      { t with descr = Bottom }
    | Extern _ | Symbol _ ->
      (* We don't know yet *)
      t
    end
  | _ -> t

let refine_value_kind t (kind : Lambda.value_kind) : Lambda.value_kind =
  match t.descr with
  | Boxed_number (Float, { descr = Float _; _ }) -> Pfloatval
  | Boxed_number (Int32, { descr = Int32 _; _ }) -> Pboxedintval Pint32
  | Boxed_number (Int64, { descr = Int64 _; _ }) -> Pboxedintval Pint64
  | Boxed_number (Nativeint, { descr = Nativeint _; _ }) ->
    Pboxedintval Pnativeint
  | Union union ->
    begin match Unionable.flatten union with
    | Ok (Int _) -> Pintval
    | _ -> kind
    end
  | _ -> kind

module type Constructors_and_accessors = sig
  val kind : t -> Flambda_kind.t
  val descr : t -> descr
  val descrs : t list -> descr list
  val create_set_of_closures
     : function_decls:Flambda.function_declarations
    -> bound_vars:t Var_within_closure.Map.t
    -> invariant_params:Variable.Set.t Variable.Map.t lazy_t
    -> specialised_args:Flambda.specialised_to Variable.Map.t
    -> freshening:Freshening.Project_var.t
    -> direct_call_surrogates:Closure_id.t Closure_id.Map.t
    -> set_of_closures
  val update_freshening_of_set_of_closures
     : set_of_closures
    -> freshening:Freshening.Project_var.t
    -> set_of_closures
  val unknown : Flambda_kind.t -> unknown_because_of -> t
  val int : int -> t
  val char : char -> t
  val boxed_float : float -> t
  val any_float : t
  val any_unboxed_float : t
  val any_unboxed_int32 : t
  val any_unboxed_int64 : t
  val any_unboxed_nativeint : t
  val unboxed_float : float -> t
  val unboxed_int32 : Int32.t -> t
  val unboxed_int64 : Int64.t -> t
  val unboxed_nativeint : Nativeint.t -> t
  val boxed_float : float -> t
  val boxed_int32 : Int32.t -> t
  val boxed_int64 : Int64.t -> t
  val boxed_nativeint : Nativeint.t -> t
  val mutable_float_array : size:int -> t
  val immutable_float_array : t array -> t
  val string : int -> string option -> t
  val boxed_int : 'i boxed_int -> 'i -> t
  val constptr : int -> t
  val block : Tag.Scannable.t -> t array -> t
  val extern : Export_id.t -> t
  val symbol : Symbol.t -> t
  val bottom : t
  val unresolved : unresolved_value -> t
  val closure
     : ?closure_var:Variable.t
    -> ?set_of_closures_var:Variable.t
    -> ?set_of_closures_symbol:Symbol.t
    -> set_of_closures Closure_id.Map.t
    -> t
  val set_of_closures
     : ?set_of_closures_var:Variable.t
    -> set_of_closures
    -> t
  val make_const_int_named : int -> Flambda.named * t
  val make_const_char_named : char -> Flambda.named * t
  val make_const_ptr_named : int -> Flambda.named * t
  val make_const_bool_named : bool -> Flambda.named * t
  val make_const_float_named : float -> Flambda.named * t
  val make_const_boxed_int_named : 'i boxed_int -> 'i -> Flambda.named * t
  val augment_with_variable : t -> Variable.t -> t
  val augment_with_symbol : t -> Symbol.t -> t
  val augment_with_symbol_field : t -> Symbol.t -> int -> t
  val replace_description : t -> descr -> t
  val refine_using_value_kind : t -> Lambda.value_kind -> t
  val refine_value_kind : t -> Lambda.value_kind -> Lambda.value_kind
end
