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

module Char = Misc.Stdlib.Char
module Float = Numbers.Float
module Int = Numbers.Int
module Int32 = Numbers.Int32
module Int64 = Numbers.Int64
module Nativeint = Numbers.Nativeint

module K = Flambda_kind

type 'a simple_commutative_op = 'a -> 'a -> 'a

module Make (Function_declarations : sig
  type t
  val print : Format.formatter -> t -> unit
end) = struct
  type function_declarations = Function_declarations.t

  module Naked_number = struct
    type t =
      | Int of Targetint.t
      | Const_pointer of Targetint.t
      | Char of Char.t
      | Float of Float.t
      | Int32 of Int32.t
      | Int64 of Int64.t
      | Nativeint of Targetint.t

    include Identifiable.Make (struct
      type nonrec t = t

      let to_int t =
        match t with
        | Int _ -> 0
        | Char _ -> 1
        | Float _ -> 2
        | Int32 _ -> 3
        | Int64 _ -> 4
        | Nativeint _ -> 5

      let compare t1 t2 =
        match t1, t2 with
        | Int n1, Int n2 -> Targetint.compare n1 n2
        | Char n1, Char n2 -> n1 = n2
        | Float n1, Float n2 -> n1 = n2
        | Int32 n1, Int32 n2 -> Int32.compare n1 n2
        | Int64 n1, Int64 n2 -> Int64.compare n1 n2
        | Nativeint n1, Nativeint n2 -> Targetint.compare n1 n2
        | (Int _ | Char _ | Float _ | Int32 _ | Int64 _ | Nativeint _), _ ->
          Pervasives.compare (to_int t1) (to_int t2)

      let equal t1 t2 = (compare t1 t2 = 0)

      let hash t = Hashtbl.hash t

      let print ppf t =
        let fprintf = Format.fprintf in
        match t with
        | Int n -> fprintf "int{%d}" n
        | Char c -> fprintf "char{%c}" c
        | Float n -> fprintf "float{%f}" n
        | Int32 n -> fprintf "int32{%ld}" n
        | Int64 n -> fprintf "int64{%Ld}" n
        | Nativeint n -> fprintf "nativeint{%nd}" n
  end

  module Boxed_or_encoded_number_kind = struct
    type encoded =
      | Tagged_int

    type boxed =
      | Float
      | Int32
      | Int64
      | Nativeint

    type t =
      | Boxed of boxed
      | Encoded of encoded

    include Identifiable.Make (struct
      type nonrec t = t

      let compare t1 t2 = Pervasives.compare t1 t2

      let equal t1 t2 = (compare t1 t2 = 0)

      let hash t = Hashtbl.hash t

      let print ppf t =
        match t with
        | Boxed Float -> Format.fprintf ppf "boxed_float"
        | Boxed Int32 -> Format.fprintf ppf "boxed_int32"
        | Boxed Int64 -> Format.fprintf ppf "boxed_int64"
        | Boxed Nativeint -> Format.fprintf ppf "boxed_nativeint"
        | Encoded Tagged_int -> Format.fprint ppf "tagged_int"

      let output _ _ = Misc.fatal_error "Not implemented"
    end)

    let num_words_allocated_excluding_header t =
      let custom_block_size = 2 in
      match t with
      | Encoded Tagged_int -> 0
      | Boxed Float ->
        begin match Targetint.num_bits with
        | Thirty_two -> 2
        | Sixty_four -> 1
        end
      | Boxed Int32 -> custom_block_size + 1
      | Boxed Int64 ->
        begin match Targetint.num_bits with
        | Thirty_two -> custom_block_size + 2
        | Sixty_four -> custom_block_size + 1
        end
      | Boxed Nativeint -> custom_block_size + 1
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
  type load_lazily =
    | Export_id of Export_id.t * Flambda_kind.t
    | Symbol of Symbol.t

  (* CR mshinwell: Remove this once Pierre's patch lands *)
  type closure_freshening =
    { vars_within_closure : Var_within_closure.t Var_within_closure.Map.t;
      closure_id : Closure_id.t Closure_id.Map.t;
    }

  let print_closure_freshening ppf t =
    Format.fprintf ppf "{ vars_within_closure %a, closure_id %a }"
      (Var_within_closure.Map.print Var_within_closure.print)
      t.vars_within_closure
      (Closure_id.Map.print Closure_id.print)
      t.closure_id

  (* CR mshinwell: update comment *)
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
     type t =
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

  (* CR mshinwell: Remove this signature and somehow import from
     Flambda_type0_intf. *)
  type string_contents = private
    | Contents of string
    | Unknown_or_mutable

  type string_ty = private {
    contents : string_contents;
    size : int;
  }

  type 'a with_aliases = private {
    thing : 'a;
    var : Variable.t option;
    (** An optional equality to a variable. *)
    symbol : (Symbol.t * int option) option;
    (** An optional equality to a symbol, or if the integer field number is
        specified, to a field of a symbol. *)
  }

  type t = private {
    descr : descr;
    var : Variable.t option;
    symbol : (Symbol.t * int option) option;
    mutable summary : summary option;
    (** [summary] is only present for performance reasons. *)
  }

  and descr =
    | Ok of singleton_or_union
    | Load_lazily of load_lazily

  and singleton_or_union =
    | Unknown of K.t * unknown_because_of
    | Singleton of singleton
    | Union of t * t
    | Bottom

  and singleton =
    | Naked_number of Naked_number.t
    | Boxed_or_encoded_number of Boxed_or_encoded_number_kind.t * t
    | Block of Tag.Scannable.t * (t array)
    | Set_of_closures of set_of_closures
    | Closure of { set_of_closures : t; closure_id : Closure_id.t }
    | String of string_ty
    | Float_array of float_array

  (* CR-soon mshinwell: add support for the approximations of the results,
     so we can do all of the tricky higher-order cases. *)
  and set_of_closures = private {
    function_decls : function_declarations;
    bound_vars : t Var_within_closure.Map.t;
    invariant_params : Variable.Set.t Variable.Map.t lazy_t;
    size : int option Variable.Map.t lazy_t;
    (** For functions that are very likely to be inlined, the size of the
        function's body. *)
    freshening : closure_freshening;
    (** Any freshening that has been applied to [function_decls]. *)
    direct_call_surrogates : Closure_id.t Closure_id.Map.t;
  }

  and float_array_contents = private
    | Contents of t array
    | Unknown_or_mutable

  and float_array = private {
    contents : float_array_contents;
    size : int;
  }

  and summary =
    | Unknown of K.t * unknown_because_of
    | Naked_number of Naked_number.t
    | Blocks_and_immediates of {
        blocks : t array Tag.Scannable.Map.t;
        immediates : Targetint.Set.t list;
      }
    | Boxed_float of float option with_aliases
    | Boxed_int32 of Int32.t option with_aliases
    | Boxed_int64s of Int64.t option with_aliases
    | Boxed_nativeint of Targetint.t option with_aliases
    | Block of t array Tag.Scannable.Map.t
    | Set_of_closures of set_of_closures
    | Closure of t Closure_id.Map.t
    | String of string_ty
    | Float_array of float_array
    | Bottom

  let print_set_of_closures ppf
        { function_decls; invariant_params; freshening; _ } =
    Format.fprintf ppf
      "(set_of_closures:@ %a invariant_params=%a freshening=%a)"
      Function_declarations.print function_decls
      (Variable.Map.print Variable.Set.print) (Lazy.force invariant_params)
      print_closure_freshening freshening

  let print_unresolved_value ppf (unresolved : unresolved_value) =
    match unresolved with
    | Set_of_closures_id set ->
      Format.fprintf ppf "Set_of_closures_id %a" Set_of_closures_id.print set
    | Symbol symbol ->
      Format.fprintf ppf "Symbol %a" Symbol.print symbol

  let rec print_singleton ppf singleton =
    match singleton with
    | Naked_number nn -> Naked_number.print ppf nn
    | Block (tag, fields) ->
      Format.fprintf ppf "@[[%a: %a]@]"
        Tag.Scannable.print tag
        (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf "; ")
          print) (Array.to_list fields)
    | Boxed_or_encoded_number (bn, t) ->
      Format.fprintf ppf "%a(%a)"
        Boxed_number_kind.print bn
        print t
    | Set_of_closures set_of_closures ->
      print_set_of_closures ppf set_of_closures
    | Closure { set_of_closures; closure_id; } ->
      Format.fprintf ppf "(closure:@ @[<2>[@ %a @[<2>from@ %a@];@ ]@])"
          Closure_id.print closure_id
          print set_of_closures
    | String { contents; size; } ->
      begin match contents with
      | None -> Format.fprintf ppf "string %i" size
      | Some s ->
        let s =
          if size > 10 then String.sub s 0 8 ^ "..."
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

  and print_singleton_or_union ppf singleton_or_union =
    match singleton_or_union with
    | Unknown (kind, reason) ->
      begin match reason with
      | Unresolved_value value ->
        Format.fprintf ppf "?(%a)(due to unresolved %a)"
          K.Basic.print kind
          print_unresolved_value value
      | Other -> Format.fprintf ppf "?(%a)" K.print kind
      end;
    | Singleton singleton -> print_singleton ppf singleton
    | Union (t1, t2) ->
      Format.fprintf ppf "(%a)U(%a)" print t1 print t2
    | Bottom -> Format.fprintf ppf "bottom"

  and print_descr ppf descr =
    match descr with
    | Ok singleton_or_union -> print_singleton_or_union ppf singleton_or_union
    | Load_lazily (Export_id (id, kind)) ->
      Format.fprintf ppf "lazy[%a](eid %a)"
        Flambda_kind.print kind
        Export_id.print id
    | Load_lazily (Symbol sym) ->
      Format.fprintf ppf "lazy[%a](sym %a)"
        Flambda_kind.print (Flambda_kind.value ())
        Symbol.print sym

  and print ppf { descr; var; symbol; } =
    let print_symbol ppf = function
      | None -> Symbol.print_opt ppf None
      | Some (sym, None) -> Symbol.print ppf sym
      | Some (sym, Some field) ->
        Format.fprintf ppf "%a.(%i)" Symbol.print sym field
    in
    Format.fprintf ppf "{ descr=%a var=%a symbol=%a }"
      print_descr descr
      Variable.print_opt var
      print_symbol symbol

  (* CR pchambart:  (This was written for the "join" case)
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
     is).
     mshinwell: changed to meet *)

  let just_descr descr =
    { descr; var = None; projection = None; symbol = None; }

  (* CR mshinwell: read carefully *)
  let refine_using_value_kind t (kind : Lambda.value_kind) =
    match kind with
    | Pgenval -> t
    | Pfloatval ->
      begin match t.descr with
      | Boxed_or_encoded_number (Boxed Float,
          { descr = Naked_number (Float _); _ }) ->
        t
      | Unknown ((Unboxed_float | Bottom), reason) ->
        { t with
          descr = Boxed_or_encoded_number (Boxed Float,
            just_descr (Unknown (K.unboxed_float (), reason)));
        }
      | Unknown (
          (Value | Tagged_int | Naked_int | Naked_int32 | Naked_int64
            | Unboxed_nativeint), _) ->
        Misc.fatal_errorf "Wrong type for Pfloatval kind: %a"
          print t
      | Union _
      | Naked_number _
      | Boxed_or_encoded_number _
      | Set_of_closures _
      | Closure _
      | Immutable_string _
      | Mutable_string _
      | Float_array _
      | Bottom ->
        (* Unreachable *)
        { t with descr = Bottom }
      | Load_lazily _ ->
        (* We don't know yet *)
        t
      end
    (* CR mshinwell: Do we need more cases here?  We could add Pintval *)
    | _ -> t

  let augment_with_variable t var = { t with var = Some var }
  let update_variable t var = { t with var; }
  let augment_with_symbol t symbol = { t with symbol = Some (symbol, None) }
  let augment_with_symbol_field t symbol field =
    match t.symbol with
    | None -> { t with symbol = Some (symbol, Some field) }
    | Some _ -> t

  let replace_description t descr = { t with descr }

  let unknown kind reason = just_descr (Unknown (kind, reason))

  let tagged_int i = just_descr (Union (Unionable.int i))
  let tagged_char i = just_descr (Union (Unionable.char i))

  let constptr i = just_descr (Union (Unionable.constptr i))

  let unboxed_int n =
    just_descr (Naked_number (Int (Int.Set.singleton n)))

  let unboxed_char c =
    just_descr (Naked_number (Char (Char.Set.singleton n)))

  let unboxed_float n =
    if Targetint.size < 64 then None
    else just_descr (Naked_number (Float (Float.Set.singleton n)))

  let unboxed_int32 n =
    just_descr (Naked_number (Int32 (Int32.Set.singleton n)))

  let unboxed_int64 n =
    if Targetint.size < 64 then None
    else Some (just_descr (Naked_number (Int64 (Int64.Set.singleton n))))

  let unboxed_nativeint n =
    just_descr (Naked_number (Nativeint (Nativeint.Set.singleton n)))

  let boxed_float f =
    just_descr (Boxed_or_encoded_number (Boxed Float, unboxed_float f))
  let boxed_int32 i =
    just_descr (Boxed_or_encoded_number (Boxed Int32, unboxed_int32 i))
  let boxed_int64 i =
    just_descr (Boxed_or_encoded_number (Boxed Int64, unboxed_int64 i))
  let boxed_nativeint i =
    just_descr (Boxed_or_encoded_number (
      Boxed Nativeint, unboxed_nativeint i))

  let export_id_loaded_lazily ex = just_descr (Load_lazily (Export_id ex))
  let symbol_loaded_lazily sym =
    { (just_descr (Load_lazily (Symbol sym)))
      with symbol = Some (sym, None);
    }
  let immutable_string str = just_descr (Immutable_string str)
  let mutable_string ~size = just_descr (Mutable_string { size; })
  (* CR mshinwell: Split Float_array into immutable and mutable as for
     strings? *)
  let mutable_float_array ~size =
    just_descr (Float_array { contents = Unknown_or_mutable; size; } )
  let immutable_float_array (contents : t array) =
    let size = Array.length contents in
    let contents =
      Array.map (fun t -> refine_using_value_kind t Pfloatval) contents
    in
    just_descr (Float_array { contents = Contents contents; size; } )
  let bottom () = just_descr Bottom

  let any_unboxed_float () =
    just_descr (Unknown (K.unboxed_float (), Other))
  let any_unboxed_int32 () =
    just_descr (Unknown (K.unboxed_int32 (), Other))
  let any_unboxed_int64 () =
    just_descr (Unknown (K.unboxed_int64 (), Other))
  let any_unboxed_nativeint () =
    just_descr (Unknown (K.unboxed_nativeint (), Other))

  let any_boxed_float () =
    just_descr (Boxed_number (Float, any_unboxed_float ()))

  let closure ?closure_var ?set_of_closures_var ?set_of_closures_symbol
        closures =
    let type_set_of_closures value_set_of_closures =
      { descr = Set_of_closures value_set_of_closures;
        var = set_of_closures_var;
        projection = None;
        symbol = Misc.may_map (fun s -> s, None) set_of_closures_symbol;
      }
    in
    let potential_closures =
      Closure_id.Map.map type_set_of_closures closures
    in
    { descr = Closure { potential_closures };
      var = closure_var;
      projection = None;
      symbol = None;
    }

  let create_set_of_closures ~function_decls ~size ~bound_vars
        ~invariant_params ~freshening
        ~direct_call_surrogates : set_of_closures =
    { function_decls;
      bound_vars;
      invariant_params;
      size;
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
      projection = None;
      symbol = None;
    }

  let block tag b =
    (* We avoid having multiple possible approximations for e.g. [Int64]
       values. *)
    match Tag.Scannable.of_tag tag with
    | None -> unknown (K.value ()) Other
    | Some tag -> just_descr (Union (Unionable.block tag b))

  let free_variables t =
    let rec free_variables t acc =
      let acc =
        match t.var with
        | None -> acc
        | Some var -> Variable.Set.add var acc
      in
      let acc =
        match t.projection with
        | None -> acc
        | Some projection ->
          Variable.Set.add (Projection.projecting_from projection) acc
      in
      match t.descr with
      | Union unionable ->
        begin match unionable with
        | Blocks blocks
        | Blocks_and_immediates (blocks, _) ->
          Tag.Scannable.Map.fold (fun _tag t_array acc ->
              Array.fold_left (fun acc t -> free_variables t acc)
                acc t_array)
            blocks acc
        | Immediates _ -> acc
        end
      | Unknown _
      | Unboxed_float _
      | Unboxed_int32 _
      | Unboxed_int64 _
      | Unboxed_nativeint _ -> acc
      | Boxed_number (_, t) -> free_variables t acc
      | Set_of_closures set_of_closures ->
        Var_within_closure.Map.fold (fun _var t acc -> free_variables t acc)
          set_of_closures.bound_vars acc
      | Closure { potential_closures; } ->
        Closure_id.Map.fold (fun _closure_id t acc -> free_variables t acc)
          potential_closures acc
      | Immutable_string _
      | Mutable_string _ -> acc
      | Float_array { contents; size = _; } ->
        begin match contents with
        | Contents ts ->
          Array.fold_left (fun acc t -> free_variables t acc) acc ts
        | Unknown_or_mutable -> acc
        end
      | Bottom
      | Load_lazily _ -> acc
    in
    free_variables t Variable.Set.empty

  let rec clean t classify =
    let clean_var var_opt =
      match var_opt with
      | None -> None
      | Some var ->
        match classify var with
        | Available -> var_opt
        | Available_different_name new_var -> Some new_var
        | Unavailable -> None
    in
    let t = update_variable t (clean_var t.var) in
    match t.descr with
    | Union unionable ->
      let unionable =
        Unionable.map_blocks unionable ~f:(fun blocks ->
          Tag.Scannable.Map.map (fun ts ->
            Array.map (fun t -> clean t classify) ts) blocks)
      in
      { t with descr = Union unionable; }
    | Unknown _
    | Unboxed_float _
    | Unboxed_int32 _
    | Unboxed_int64 _
    | Unboxed_nativeint _ -> t
    | Boxed_number (kind, contents) ->
      { t with descr = Boxed_number (kind, clean contents classify); }
    | Set_of_closures set_of_closures ->
      let bound_vars =
        Var_within_closure.Map.map (fun t -> clean t classify)
          set_of_closures.bound_vars
      in
      { t with descr = Set_of_closures { set_of_closures with bound_vars; }; }
    | Closure closure ->
      let potential_closures =
        Closure_id.Map.map (fun t -> clean t classify)
          closure.potential_closures
      in
      { t with descr = Closure { potential_closures; }; }
    | Immutable_string _
    | Mutable_string _ -> t
    | Float_array { contents; size; } ->
      let contents : float_array_contents =
        match contents with
        | Contents ts -> Contents (Array.map (fun t -> clean t classify) ts)
        | Unknown_or_mutable -> Unknown_or_mutable
      in
      { t with descr = Float_array { contents; size; }; }
    | Load_lazily _
    | Bottom -> t

  type 'a result =
    | Ok of 'a
    | Not_fully_loaded

  let map_descr t ~f : t result =
    match t.descr with
    | Ok descr -> Ok { t with descr = Ok (f descr); }
    | Load_lazily _ -> Not_fully_loaded

  let tag_int t =
    map_descr t ~f:(fun descr ->
      match descr with
      | Unknown (Naked_int, _) | Naked_number (Int _) ->
        Boxed_or_encoded_number (Encoded Tagged_int, t)
      | Naked_number _
      | Boxed_or_encoded_number _
      | Block _
      | Set_of_closures _
      | Closure _
      | String _
      | Float_array _
      | Bottom -> Bottom)

  let rec kind t =
    match t.descr with
    | Load_lazily (Export_id (_, kind)) -> kind
    | Load_lazily (Symbol _) -> K.value ()
    | Ok su ->
      match su with
      | Unknown (kind, _) -> kind
      | Singleton s ->
        begin match s with
        | Naked_number (Int _)
        | Naked_number (Char _) -> K.naked_int ()
        | Naked_number (Float _) -> K.naked_float ()
        | Naked_number (Int32 _) -> K.naked_int32 ()
        | Naked_number (Int64 _) -> K.naked_int64 ()
        | Naked_number (Nativeint _) -> K.naked_nativeint ()
        | Boxed_or_encoded_number (Encoded _, _) -> K.tagged_int ()
        | Boxed_or_encoded_number (Boxed _, _)
        | Block _
        | Set_of_closures _
        | Closure _
        | String _
        | Float_array _ -> K.value ()
        end
      | Union (t1, t2) ->
        let kind1 = kind t1 in
        let kind2 = kind t2 in
        assert (Flambda_kind.equal kind1 kind2);
        kind1
      | Bottom -> Flambda_kind.bottom ()

  let join t1 t2 ~load_type =
    if not (Flambda_kind.equal (kind t1) (kind t2)) then begin
      Misc.fatal_errorf "Cannot take the join of two types with incompatible \
          kinds: %a and %a"
        print t1
        print t2
    end;
    let var =
      match a1.var, a2.var with
      | None, _ | _, None -> None
      | Some v1, Some v2 ->
        if Variable.equal v1 v2 then Some v1
        else None
    in
    let projection =
      match a1.projection, a2.projection with
      | None, _ | _, None -> None
      | Some proj1, Some proj2 ->
        if Projection.equal proj1 proj2 then Some proj1 else None
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
    let descr =
      match t1.descr, t2.descr with
      | Load_lazily _, _
      | _, Load_lazily _ -> Union (t1, t2)
      | Ok su1, Ok su2 ->
        let su =
          match su1, su2 with
          | Bottom _, _ -> su2
          | _, Bottom _ -> su1
          | Unknown _, _ -> su1
          | _, Unknown _ -> su2
          | Singleton _, Union _
          | Union _, Singleton _
          | Union _, Union _ -> Union (t1, t2)
          | Singleton _, Singleton _ ->
            (* CR mshinwell: Could add:
              if singletons_definitely_equal s1 s2 then Singleton s1
              else Union (t1, t2)
            *)
            Union (t1, t2)
        in
        Ok su
    in
    { descr;
      var;
      projection;
      symbol;
    }

  type 'a fold_result =
    | Unknown of Flambda_kind.Basic.t
    | Ok of 'a
    | Bottom

  let fold t what ~import_type ~f =
    let rec fold t acc : _ fold_result =
      match t.descr with
      | Singleton singleton ->
        begin match singleton with
        | Unknown (kind, _reason) ->
          begin match what with
          | Join -> Unknown kind
          | Meet -> acc
          end
        | Bottom ->
          begin match what with
          | Join -> acc
          | Meet -> Bottom
          end
        | Known known -> f acc known
        end
      | Union (t1, t2) ->
        let acc = fold t1 acc in
        match what, acc with
        | Join, Unknown -> Unknown
        | Meet, Bottom -> Bottom
        | _, Ok _ -> fold t2 acc
    in
    let t = import_type t in
    let kind = kind_exn t in
    let unit_type : _ fold_result =
      match what with
      | Join -> Bottom
      | Meet -> Unknown kind
    in
    fold t unit_type

  let summarize_main t ~import_type =
    fold t Join ~import_type
      ~f:(fun acc (known : known) : unboxable fold_result ->
        match known with
        | Boxed_or_encoded_number (Encoded Tagged_int, t) ->
          begin match acc with
          | Blocks_and_immediates of { blocks; immediates; } ->
            let join_of_immediates =
              fold t Join ~import_type
                ~f:(fun acc (known : known) : Immediate.Set.t fold_result ->
                  match known with
                  | Naked_number (Int i) ->
                    Ok (Immediate.Set.add (Immediate.of_int i) acc)
                  | Naked_number (Const_pointer i) ->
                    Ok (Immediate.Set.add (Immediate.of_const_pointer i) acc)
                  | Naked_number (Char c) ->
                    Ok (Immediate.Set.add (Immediate.of_char c) acc)
                  | Naked_number (Float _ | Int32 _ | Int64 _ | Nativeint _)
                  | Boxed_or_encoded_number _
                  | Block _
                  | Closure _
                  | Set_of_closures _
                  | String _
                  | Float_array _ -> Bottom)
            in
            begin match join_of_immediates with
            | Unknown _ -> Unknown (Flambda_kind.Basic.value ())
            | Ok immediates' ->
              Ok (Blocks_and_immediates {
                blocks;
                immediates = Immediate.Set.union immediates immediates';
              })
            | Bottom -> Bottom
            end
          | Boxed_floats _ | Boxed_int32s _ | Boxed_int64s _
          | Boxed_nativeints _ -> Bottom
          end
        | Boxed_or_encoded_number (Boxed Float, t) ->
          begin match acc with
          | Boxed_floats floats ->
            let join_of_floats =
              fold t Join ~import_type
                ~f:(fun acc (known : known) : Float.Set.t fold_result ->
                  match known with
                  | Naked_number (Float f) -> Ok (Float.Set.add f acc)
                  | Naked_number (Int _ | Const_pointer _ | Char _ | Int32 _
                      | Int64 _ | Nativeint _)
                  | Boxed_or_encoded_number _
                  | Block _
                  | Closure _
                  | Set_of_closures _
                  | String _
                  | Float_array _ -> Bottom)
            in
            begin match join_of_floats with
            | Unknown _ -> Unknown (Flambda_kind.Basic.value ())
            | Ok floats' ->
              Ok (Boxed_floats (Float.Set.union floats floats'))
            | Bottom -> Bottom
            end
          | Blocks_and_immediates _ | Boxed_int32s _ | Boxed_int64s _
          | Boxed_nativeints _ -> Bottom
          end
        | Boxed_or_encoded_number (Boxed Int32, t) ->
          begin match acc with
          | Boxed_int32s int32s ->
            let join_of_int32s =
              fold t Join ~import_type
                ~f:(fun acc (known : known) : Int32.Set.t fold_result ->
                  match known with
                  | Naked_number (Int32 f) -> Ok (Int32.Set.add f acc)
                  | Naked_number (Int _ | Const_pointer _ | Char _ | Float _
                      | Int64 _ | Nativeint _)
                  | Boxed_or_encoded_number _
                  | Block _
                  | Closure _
                  | Set_of_closures _
                  | String _
                  | Float_array _ -> Bottom)
            in
            begin match join_of_int32s with
            | Unknown _ -> Unknown (Flambda_kind.Basic.value ())
            | Ok int32s' ->
              Ok (Boxed_int32s (Int32.Set.union int32s int32s'))
            | Bottom -> Bottom
            end
          | Blocks_and_immediates _ | Boxed_floats _ | Boxed_int64s _
          | Boxed_nativeints _ -> Bottom
          end
        | Boxed_or_encoded_number (Boxed Int64, t) ->
          begin match acc with
          | Boxed_int64s int64s ->
            let join_of_int64s =
              fold t Join ~import_type
                ~f:(fun acc (known : known) : Int64.Set.t fold_result ->
                  match known with
                  | Naked_number (Int64 f) -> Ok (Int64.Set.add f acc)
                  | Naked_number (Int _ | Const_pointer _ | Char _ | Float _
                      | Int32 _ | Nativeint _)
                  | Boxed_or_encoded_number _
                  | Block _
                  | Closure _
                  | Set_of_closures _
                  | String _
                  | Float_array _ -> Bottom)
            in
            begin match join_of_int64s with
            | Unknown _ -> Unknown (Flambda_kind.Basic.value ())
            | Ok int64s' ->
              Ok (Boxed_int64s (Int64.Set.union int64s int64s'))
            | Bottom -> Bottom
            end
          | Blocks_and_immediates _ | Boxed_floats _ | Boxed_int32s _
          | Boxed_nativeints _ -> Bottom
          end
        | Boxed_or_encoded_number (Boxed Nativeint, t) ->
          begin match acc with
          | Boxed_nativeints nativeints ->
            let join_of_nativeints =
              fold t Join ~import_type
                ~f:(fun acc (known : known) : Nativeint.Set.t fold_result ->
                  match known with
                  | Naked_number (Nativeint f) -> Ok (Nativeint.Set.add f acc)
                  | Naked_number (Int _ | Const_pointer _ | Char _ | Float _
                      | Int32 _ | Int64 _)
                  | Boxed_or_encoded_number _
                  | Block _
                  | Closure _
                  | Set_of_closures _
                  | String _
                  | Float_array _ -> Bottom)
            in
            begin match join_of_nativeints with
            | Unknown _ -> Unknown (Flambda_kind.Basic.value ())
            | Ok nativeints' ->
              Ok (Boxed_nativeints (Nativeint.Set.union nativeints nativeints'))
            | Bottom -> Bottom
            end
          | Blocks_and_immediates _ | Boxed_floats _ | Boxed_int32s _
          | Boxed_int64s _ -> Bottom
          end
        | Block (tag, fields) ->
          begin match acc with
          | Blocks_and_immediates of { blocks; immediates; } ->
            begin match Tag.Scannable.Map.find tag blocks with
            | exception Not_found ->
              Ok (Blocks_and_immediates {
                blocks = Tag.Scannable.Map.add tag fields blocks;
                immediates;
              })
            | existing_fields ->
              if Array.length fields <> Array.length existing_fields then
                Bottom
              else
                let fields =
                  Array.map2 (fun t existing_t ->
                      just_descr (Union (t, existing_t)))
                    fields existing_fields
                in
                Ok (Blocks_and_immediates {
                  blocks = Tag.Scannable.Map.add tag fields blocks;
                  immediates;
                })
            end
          | Boxed_floats _ | Boxed_int32s _ | Boxed_int64s _
          | Boxed_nativeints _ -> Bottom
          end
        | Closure _
        | Naked_number _
        | Set_of_closures _
        | String _
        | Float_array _ -> Bottom)

  let summarize t ~import_type =
    match t.summary with
    | None -> summarize_main t ~import_type
    | Some summary -> summary
end
