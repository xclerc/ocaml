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

module Char = Misc.Stdlib.Char
module Float = Numbers.Float
module Int = Numbers.Int
module Int32 = Numbers.Int32
module Int64 = Numbers.Int64
module Nativeint = Numbers.Nativeint

module K = Flambda_kind

module Make (Function_declarations : sig
  type t
  val print : Format.formatter -> t -> unit
end) = struct
  type function_declarations = Function_declarations.t

  type unresolved_value =
    | Set_of_closures_id of Set_of_closures_id.t
    | Export_id of Export_id.t
    | Symbol of Symbol.t

  type unknown_because_of =
    | Unresolved_value of unresolved_value
    | Other

  (** Types from other compilation units are loaded lazily.  There are two
      kinds of cross-compilation unit reference to be resolved: via
      [Export_id.t] values and via [Symbol.t] values. *)
  type load_lazily =
    | Export_id of Export_id.t
    | Symbol of Symbol.t

  let print_load_lazily ppf (ll : load_lazily) =
    match ll with
    | Export_id id -> Format.fprintf ppf "(eid %a)" Export_id.print id
    | Symbol sym -> Format.fprintf ppf "(sym %a)" Symbol.print sym

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

  type string_contents =
    | Contents of string
    | Unknown_or_mutable

  type string_ty = {
    contents : string_contents;
    size : int;
  }

  type 'a with_var_and_symbol = {
    descr : 'a;
    var : Variable.t option;
    symbol : (Symbol.t * int option) option;
  }

  type 'a or_wrong =
    | Ok of 'a
    | Wrong

  type t =
    | Value of ty_value
    | Naked_immediate of ty_naked_immediate
    | Naked_float of ty_naked_float
    | Naked_int32 of ty_naked_int32
    | Naked_int64 of ty_naked_int64
    | Naked_nativeint of ty_naked_nativeint

  and ty_value = (of_kind_value, Flambda_kind.scanning) ty
  and ty_naked_immediate = (of_kind_naked_immediate, unit) ty
  and ty_naked_float = (of_kind_naked_float, unit) ty
  and ty_naked_int32 = (of_kind_naked_int32, unit) ty
  and ty_naked_int64 = (of_kind_naked_int64, unit) ty
  and ty_naked_nativeint = (of_kind_naked_nativeint, unit) ty

  and ('a, 'u) ty = ('a, 'u) maybe_unresolved with_var_and_symbol

  and resolved_t =
    | Value of resolved_ty_value
    | Naked_immediate of resolved_ty_naked_immediate
    | Naked_float of resolved_ty_naked_float
    | Naked_int32 of resolved_ty_naked_int32
    | Naked_int64 of resolved_ty_naked_int64
    | Naked_nativeint of resolved_ty_naked_nativeint

  and resolved_ty_value = (of_kind_value, Flambda_kind.scanning) resolved_ty
  and resolved_ty_naked_immediate = (of_kind_naked_immediate, unit) resolved_ty
  and resolved_ty_naked_float = (of_kind_naked_float, unit) resolved_ty
  and resolved_ty_naked_int32 = (of_kind_naked_int32, unit) resolved_ty
  and resolved_ty_naked_int64 = (of_kind_naked_int64, unit) resolved_ty
  and resolved_ty_naked_nativeint = (of_kind_naked_nativeint, unit) resolved_ty

  and ('a, 'u) resolved_ty = ('a, 'u) or_unknown_or_bottom with_var_and_symbol

  and ('a, 'u) maybe_unresolved =
    | Ok of ('a, 'u) or_unknown_or_bottom
    | Load_lazily of load_lazily

  and ('a, 'u) or_unknown_or_bottom =
    | Unknown of unknown_because_of * 'u
    | Ok of 'a
    | Bottom

  and of_kind_value =
    | Singleton of of_kind_value_singleton
    | Union of of_kind_value with_var_and_symbol
        * of_kind_value with_var_and_symbol

  and of_kind_value_singleton =
    | Tagged_immediate of ty_naked_immediate
    | Boxed_float of ty_naked_float
    | Boxed_int32 of ty_naked_int32
    | Boxed_int64 of ty_naked_int64
    | Boxed_nativeint of ty_naked_nativeint
    | Block of Tag.Scannable.t * (ty_value array)
    | Set_of_closures of set_of_closures
    | Closure of {
        set_of_closures : ty_value;
        closure_id : Closure_id.t
      }
    | String of string_ty
    | Float_array of float_array_ty

  (* CR-soon mshinwell: add support for the approximations of the results,
     so we can do all of the tricky higher-order cases. *)
  and set_of_closures = {
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

  and float_array_contents =
    | Contents of t array
    | Unknown_or_mutable

  and float_array_ty = {
    contents : float_array_contents;
    size : int;
  }

  and of_kind_naked_immediate =
    | Naked_immediate of Immediate.t

  and of_kind_naked_float =
    | Naked_float of float

  and of_kind_naked_int32 =
    | Naked_int32 of Int32.t

  and of_kind_naked_int64 =
    | Naked_int64 of Int64.t

  and of_kind_naked_nativeint =
    | Naked_nativeint of Targetint.t

  let augment_with_variable (t : t) var : t =
    let var = Some var in
    match t with
    | Value ty -> Value { ty with var; }
    | Naked_immediate ty -> Naked_immediate { ty with var; }
    | Naked_float ty -> Naked_float { ty with var; }
    | Naked_int32 ty -> Naked_int32 { ty with var; }
    | Naked_int64 ty -> Naked_int64 { ty with var; }
    | Naked_nativeint ty -> Naked_nativeint { ty with var; }

  let augment_with_symbol (t : t) symbol : t =
    let symbol = Some symbol in
    match t with
    | Value ty -> Value { ty with symbol; }
    | Naked_immediate ty -> Naked_immediate { ty with symbol; }
    | Naked_float ty -> Naked_float { ty with symbol; }
    | Naked_int32 ty -> Naked_int32 { ty with symbol; }
    | Naked_int64 ty -> Naked_int64 { ty with symbol; }
    | Naked_nativeint ty -> Naked_nativeint { ty with symbol; }

  let augment_with_symbol_internal (t : t) symbol field : t =
    let symbol = Some (symbol, field) in
    match t with
    | Value ty -> Value { ty with symbol; }
    | Naked_immediate ty -> Naked_immediate { ty with symbol; }
    | Naked_float ty -> Naked_float { ty with symbol; }
    | Naked_int32 ty -> Naked_int32 { ty with symbol; }
    | Naked_int64 ty -> Naked_int64 { ty with symbol; }
    | Naked_nativeint ty -> Naked_nativeint { ty with symbol; }

  let augment_with_symbol t symbol =
    augment_with_symbol_internal t symbol None

  let augment_with_symbol_field t symbol field =
    augment_with_symbol_internal t symbol (Some field)

  let replace_variable (t : t) var : t =
    match t with
    | Value ty -> Value { ty with var; }
    | Naked_immediate ty -> Naked_immediate { ty with var; }
    | Naked_float ty -> Naked_float { ty with var; }
    | Naked_int32 ty -> Naked_int32 { ty with var; }
    | Naked_int64 ty -> Naked_int64 { ty with var; }
    | Naked_nativeint ty -> Naked_nativeint { ty with var; }

  let unknown_as_ty_value reason scanning : ty_value =
    { descr = Ok (Unknown (reason, scanning));
      var = None;
      symbol = None;
    }

  let unknown_as_resolved_ty_value reason scanning : resolved_ty_value =
    { descr = Unknown (reason, scanning);
      var = None;
      symbol = None;
    }

  let unknown_as_resolved_ty_naked_immediate reason scanning
        : resolved_ty_naked_immediate =
    { descr = Unknown (reason, scanning);
      var = None;
      symbol = None;
    }

  let unknown_as_resolved_ty_naked_float reason scanning
        : resolved_ty_naked_float =
    { descr = Unknown (reason, scanning);
      var = None;
      symbol = None;
    }

  let unknown_as_resolved_ty_naked_int32 reason scanning
        : resolved_ty_naked_int32 =
    { descr = Unknown (reason, scanning);
      var = None;
      symbol = None;
    }

  let unknown_as_resolved_ty_naked_int64 reason scanning
        : resolved_ty_naked_int64 =
    { descr = Unknown (reason, scanning);
      var = None;
      symbol = None;
    }

  let unknown_as_resolved_ty_naked_nativeint reason scanning
        : resolved_ty_naked_nativeint =
    { descr = Unknown (reason, scanning);
      var = None;
      symbol = None;
    }

  let unknown (kind : K.t) reason : t =
    match kind with
    | Value scanning ->
      Value {
        descr = Ok (Unknown (reason, scanning));
        var = None;
        symbol = None;
      }
    | Naked_immediate ->
      Naked_immediate {
        descr = Ok (Unknown (reason, ()));
        var = None;
        symbol = None;
      }
    | Naked_float ->
      Naked_float {
        descr = Ok (Unknown (reason, ()));
        var = None;
        symbol = None;
      }
    | Naked_int32 ->
      Naked_int32 {
        descr = Ok (Unknown (reason, ()));
        var = None;
        symbol = None;
      }
    | Naked_int64 ->
      Naked_int64 {
        descr = Ok (Unknown (reason, ()));
        var = None;
        symbol = None;
      }
    | Naked_nativeint ->
      Naked_nativeint {
        descr = Ok (Unknown (reason, ()));
        var = None;
        symbol = None;
      }

  let bottom (kind : K.t) : t =
    match kind with
    | Value _ ->
      Value {
        descr = Ok Bottom;
        var = None;
        symbol = None;
      }
    | Naked_immediate ->
      Naked_immediate {
        descr = Ok Bottom;
        var = None;
        symbol = None;
      }
    | Naked_float ->
      Naked_float {
        descr = Ok Bottom;
        var = None;
        symbol = None;
      }
    | Naked_int32 ->
      Naked_int32 {
        descr = Ok Bottom;
        var = None;
        symbol = None;
      }
    | Naked_int64 ->
      Naked_int64 {
        descr = Ok Bottom;
        var = None;
        symbol = None;
      }
    | Naked_nativeint ->
      Naked_nativeint {
        descr = Ok Bottom;
        var = None;
        symbol = None;
      }

  let naked_immediate (i : of_kind_naked_immediate) : t =
    Naked_immediate {
      descr = Ok (Ok i);
      var = None;
      symbol = None;
    }

  let tagged_naked_immediate (i : of_kind_naked_immediate) : t =
    let i : ty_naked_immediate =
      { descr = Ok (Ok i);
        var = None;
        symbol = None;
      }
    in
    Value {
      descr = Ok (Ok (Singleton (Tagged_immediate i)));
      var = None;
      symbol = None;
    }

  let unboxed_float f : t =
    let f : of_kind_naked_float = Naked_float f in
    Naked_float {
      descr = Ok (Ok f);
      var = None;
      symbol = None;
    }

  let unboxed_int32 n : t =
    let n : of_kind_naked_int32 = Naked_int32 n in
    Naked_int32 {
      descr = Ok (Ok n);
      var = None;
      symbol = None;
    }

  let unboxed_int64 n =
    let n : of_kind_naked_int64 = Naked_int64 n in
    Naked_int64 {
      descr = Ok (Ok n);
      var = None;
      symbol = None;
    }

  let unboxed_nativeint n : t =
    let n : of_kind_naked_nativeint = Naked_nativeint n in
    Naked_nativeint {
      descr = Ok (Ok n);
      var = None;
      symbol = None;
    }

  let boxed_float f =
    let f : ty_naked_float =
      let f : of_kind_naked_float = Naked_float f in
      { descr = Ok (Ok f);
        var = None;
        symbol = None;
      }
    in
    Value {
      descr = Ok (Ok (Singleton (Boxed_float f)));
      var = None;
      symbol = None;
    }

  let boxed_int32 n =
    let n : ty_naked_int32 =
      let n : of_kind_naked_int32 = Naked_int32 n in
      { descr = Ok (Ok n);
        var = None;
        symbol = None;
      }
    in
    Value {
      descr = Ok (Ok (Singleton (Boxed_int32 n)));
      var = None;
      symbol = None;
    }

  let boxed_int64 n =
    let n : ty_naked_int64 =
      let n : of_kind_naked_int64 = Naked_int64 n in
      { descr = Ok (Ok n);
        var = None;
        symbol = None;
      }
    in
    Value {
      descr = Ok (Ok (Singleton (Boxed_int64 n)));
      var = None;
      symbol = None;
    }

  let boxed_nativeint n =
    let n : ty_naked_nativeint =
      let n : of_kind_naked_nativeint = Naked_nativeint n in
      { descr = Ok (Ok n);
        var = None;
        symbol = None;
      }
    in
    Value {
      descr = Ok (Ok (Singleton (Boxed_nativeint n)));
      var = None;
      symbol = None;
    }

  let immutable_string_as_ty_value str : ty_value =
    let string_ty : string_ty =
      { contents = Contents str;
        size = String.length str;
      }
    in
    { descr = Ok (Ok (Singleton (String string_ty)));
      var = None;
      symbol = None;
    }

  let immutable_string str : t =
    Value (immutable_string_as_ty_value str)

  let mutable_string ~size : t =
    let string_ty : string_ty =
      { contents = Unknown_or_mutable;
        size;
      }
    in
    Value {
      descr = Ok (Ok (Singleton (String string_ty)));
      var = None;
      symbol = None;
    }

  let immutable_float_array fields : t =
    let float_array : float_array_ty =
      { contents = Contents fields;
        size = Array.length fields;
      }
    in
    Value {
      descr = Ok (Ok (Singleton (Float_array float_array)));
      var = None;
      symbol = None;
    }

  let mutable_float_array ~size : t =
    let float_array : float_array_ty =
      { contents = Unknown_or_mutable;
        size;
      }
    in
    Value {
      descr = Ok (Ok (Singleton (Float_array float_array)));
      var = None;
      symbol = None;
    }

  let block tag fields : t =
    Value {
      descr = Ok (Ok (Singleton (Block (tag, fields))));
      var = None;
      symbol = None;
    }

  let export_id_loaded_lazily (kind : K.t) export_id : t =
    match kind with
    | Value _ ->
      Value {
        descr = Load_lazily (Export_id export_id);
        var = None;
        symbol = None;
      }
    | Naked_immediate ->
      Naked_immediate {
        descr = Load_lazily (Export_id export_id);
        var = None;
        symbol = None;
      }
    | Naked_float ->
      Naked_float {
        descr = Load_lazily (Export_id export_id);
        var = None;
        symbol = None;
      }
    | Naked_int32 ->
      Naked_int32 {
        descr = Load_lazily (Export_id export_id);
        var = None;
        symbol = None;
      }
    | Naked_int64 ->
      Naked_int64 {
        descr = Load_lazily (Export_id export_id);
        var = None;
        symbol = None;
      }
    | Naked_nativeint ->
      Naked_nativeint {
        descr = Load_lazily (Export_id export_id);
        var = None;
        symbol = None;
      }

  let symbol_loaded_lazily (kind : K.t) sym : t =
    match kind with
    | Value _ ->
      Value {
        descr = Load_lazily (Symbol sym);
        var = None;
        symbol = None;
      }
    | Naked_immediate ->
      Naked_immediate {
        descr = Load_lazily (Symbol sym);
        var = None;
        symbol = None;
      }
    | Naked_float ->
      Naked_float {
        descr = Load_lazily (Symbol sym);
        var = None;
        symbol = None;
      }
    | Naked_int32 ->
      Naked_int32 {
        descr = Load_lazily (Symbol sym);
        var = None;
        symbol = None;
      }
    | Naked_int64 ->
      Naked_int64 {
        descr = Load_lazily (Symbol sym);
        var = None;
        symbol = None;
      }
    | Naked_nativeint ->
      Naked_nativeint {
        descr = Load_lazily (Symbol sym);
        var = None;
        symbol = None;
      }

  let any_boxed_float f =
    let f : ty_naked_float =
      { descr = Ok (Unknown (Other, ()));
        var = None;
        symbol = None;
      }
    in
    Value {
      descr = Ok (Ok (Singleton (Boxed_float f)));
      var = None;
      symbol = None;
    }

  let any_boxed_int32 n =
    let n : ty_naked_int32 =
      { descr = Ok (Unknown (Other, ()));
        var = None;
        symbol = None;
      }
    in
    Value {
      descr = Ok (Ok (Singleton (Boxed_int32 n)));
      var = None;
      symbol = None;
    }

  let any_boxed_int64 n =
    let n : ty_naked_int64 =
      { descr = Ok (Unknown (Other, ()));
        var = None;
        symbol = None;
      }
    in
    Value {
      descr = Ok (Ok (Singleton (Boxed_int64 n)));
      var = None;
      symbol = None;
    }

  let any_boxed_nativeint n =
    let n : ty_naked_nativeint =
      { descr = Ok (Unknown (Other, ()));
        var = None;
        symbol = None;
      }
    in
    Value {
      descr = Ok (Ok (Singleton (Boxed_nativeint n)));
      var = None;
      symbol = None;
    }

  let any_untagged_immediate () = unknown (K.naked_immediate ())
  let any_naked_float () = unknown (K.naked_float ())
  let any_naked_int32 () = unknown (K.naked_int32 ())
  let any_naked_int64 () = unknown (K.naked_int64 ())
  let any_naked_nativeint () = unknown (K.naked_nativeint ())

  let resolved_ty_value_for_predefined_exception ~name ~symbol
        : resolved_ty_value =
    let fields =
      [| immutable_string_as_ty_value name;
         unknown_as_ty_value Other Must_scan;
      |]
    in
    { descr = Ok (Singleton (Block (Tag.Scannable.object_tag, fields)));
      var = None;
      symbol = Some (symbol, None);
    }

  module type Importer = sig
    val import_value_type_as_resolved_ty_value
       : ty_value
      -> resolved_ty_value

    val import_naked_immediate_type_as_resolved_ty_naked_immediate
       : ty_naked_immediate
      -> resolved_ty_naked_immediate

    val import_naked_float_type_as_resolved_ty_naked_float
       : ty_naked_float
      -> resolved_ty_naked_float

    val import_naked_int32_type_as_resolved_ty_naked_int32
       : ty_naked_int32
      -> resolved_ty_naked_int32

    val import_naked_int64_type_as_resolved_ty_naked_int64
       : ty_naked_int64
      -> resolved_ty_naked_int64

    val import_naked_nativeint_type_as_resolved_ty_naked_nativeint
       : ty_naked_nativeint
      -> resolved_ty_naked_nativeint

    val import_value_type : ty_value -> resolved_t
    val import_naked_immediate_type : ty_naked_immediate -> resolved_t
    val import_naked_float_type : ty_naked_float -> resolved_t
    val import_naked_int32_type : ty_naked_int32 -> resolved_t
    val import_naked_int64_type : ty_naked_int64 -> resolved_t
    val import_naked_nativeint_type : ty_naked_nativeint -> resolved_t
  end

  module type Importer_intf = sig
    val import_export_id : Export_id.t -> t option
    val import_symbol : Symbol.t -> t option
    val symbol_is_predefined_exception : Symbol.t -> string option
  end

  type 'a with_importer = importer:(module Importer) -> 'a

  type 'a create_resolved_t_result =
    | Ok of 'a
    | Load_lazily_again of load_lazily

  module Make_importer (S : sig
    val import_export_id : Export_id.t -> t option
    val import_symbol : Symbol.t -> t option
    val symbol_is_predefined_exception : Symbol.t -> string option
  end) : Importer = struct
    type 'a import_result =
      | Ok of 'a
      | Treat_as_unknown_must_scan of unknown_because_of

    let import_type (type a) ll
          ~(create_resolved_t : t -> a create_resolved_t_result)
          ~(resolve_predefined_exception : Symbol.t -> a option) =
      let rec import_type (ll : load_lazily) ~export_ids_seen ~symbols_seen
            : a import_result =
        match ll with
        | Export_id id ->
          if Export_id.Set.mem id export_ids_seen then begin
            Misc.fatal_errorf "Circularity whilst resolving export ID %a"
              Export_id.print id
          end;
          begin match S.import_export_id id with
          | None -> Treat_as_unknown_must_scan (Unresolved_value (Export_id id))
          | Some t ->
            match create_resolved_t t with
            | Ok resolved_t -> Ok resolved_t
            | Load_lazily_again ll ->
              let export_ids_seen = Export_id.Set.add id export_ids_seen in
              import_type ll ~export_ids_seen ~symbols_seen
          end
        | Symbol sym ->
          match resolve_predefined_exception sym with
          | Some resolved_t -> Ok resolved_t
          | None ->
            if Symbol.Set.mem sym symbols_seen then begin
              Misc.fatal_errorf "Circularity whilst resolving symbol %a"
                Symbol.print sym
            end;
            begin match S.import_symbol sym with
            | None -> Treat_as_unknown_must_scan (Unresolved_value (Symbol sym))
            | Some t ->
              match create_resolved_t t with
              (* CR mshinwell: We used to [augment_with_symbol] here but maybe
                 we don't need it any more? *)
              | Ok resolved_t -> Ok resolved_t
              | Load_lazily_again ll ->
                let symbols_seen = Symbol.Set.add sym symbols_seen in
                import_type ll ~export_ids_seen ~symbols_seen
            end
      in
      import_type ll ~export_ids_seen:Export_id.Set.empty
        ~symbols_seen:Symbol.Set.empty

    let import_value_type_as_resolved_ty_value (ty : ty_value)
          : resolved_ty_value =
      match ty.descr with
      | Ok descr ->
        { descr;
          var = ty.var;
          symbol = ty.symbol;
        }
      | Load_lazily load_lazily ->
        let resolve_predefined_exception sym =
          match S.symbol_is_predefined_exception sym with
          | None -> None
          | Some name ->
            Some (resolved_ty_value_for_predefined_exception ~name ~symbol:sym)
        in
        let create_resolved_t t : resolved_ty_value create_resolved_t_result =
          match t with
          | Value ty ->
            begin match ty.descr with
            | Ok descr ->
              Ok {
                descr;
                var = ty.var;
                symbol = ty.symbol;
              }
            | Load_lazily ll -> Load_lazily_again ll
            end
          | Naked_immediate _
          | Naked_float _
          | Naked_int32 _
          | Naked_int64 _
          | Naked_nativeint _ ->
            Misc.fatal_errorf "Kind mismatch when importing %a; expected kind \
                [Value]"
              print_load_lazily load_lazily
        in
        let result =
          import_type load_lazily ~create_resolved_t
            ~resolve_predefined_exception
        in
        match result with
        | Ok result -> result
        | Treat_as_unknown_must_scan reason ->
          unknown_as_resolved_ty_value reason Must_scan

    let import_value_type ty : resolved_t =
      Value (import_value_type_as_resolved_ty_value ty)

    let import_naked_immediate_type_as_resolved_ty_naked_immediate
          (ty : ty_naked_immediate) : resolved_ty_naked_immediate =
      match ty.descr with
      | Ok descr ->
        { descr;
          var = ty.var;
          symbol = ty.symbol;
        }
      | Load_lazily load_lazily ->
        let resolve_predefined_exception _sym = None in
        let create_resolved_t t
              : resolved_ty_naked_immediate create_resolved_t_result =
          match t with
          | Naked_immediate ty ->
            begin match ty.descr with
            | Ok descr ->
              Ok {
                descr;
                var = ty.var;
                symbol = ty.symbol;
              }
            | Load_lazily ll -> Load_lazily_again ll
            end
          | Value _
          | Naked_float _
          | Naked_int32 _
          | Naked_int64 _
          | Naked_nativeint _ ->
            Misc.fatal_errorf "Kind mismatch when importing %a; expected kind \
                [Naked_immediate]"
              print_load_lazily load_lazily
        in
        let result =
          import_type load_lazily ~create_resolved_t
            ~resolve_predefined_exception
        in
        match result with
        | Ok result -> result
        | Treat_as_unknown_must_scan reason ->
          unknown_as_resolved_ty_naked_immediate reason ()

    let import_naked_immediate_type ty : resolved_t =
      Naked_immediate (
        import_naked_immediate_type_as_resolved_ty_naked_immediate ty)

    let import_naked_float_type_as_resolved_ty_naked_float
          (ty : ty_naked_float) : resolved_ty_naked_float =
      match ty.descr with
      | Ok descr ->
        { descr;
          var = ty.var;
          symbol = ty.symbol;
        }
      | Load_lazily load_lazily ->
        let resolve_predefined_exception _sym = None in
        let create_resolved_t t
              : resolved_ty_naked_float create_resolved_t_result =
          match t with
          | Naked_float ty ->
            begin match ty.descr with
            | Ok descr ->
              Ok {
                descr;
                var = ty.var;
                symbol = ty.symbol;
              }
            | Load_lazily ll -> Load_lazily_again ll
            end
          | Value _
          | Naked_immediate _
          | Naked_int32 _
          | Naked_int64 _
          | Naked_nativeint _ ->
            Misc.fatal_errorf "Kind mismatch when importing %a; expected kind \
                [Naked_float]"
              print_load_lazily load_lazily
        in
        let result =
          import_type load_lazily ~create_resolved_t
            ~resolve_predefined_exception
        in
        match result with
        | Ok result -> result
        | Treat_as_unknown_must_scan reason ->
          unknown_as_resolved_ty_naked_float reason ()

    let import_naked_float_type ty : resolved_t =
      Naked_float (import_naked_float_type_as_resolved_ty_naked_float ty)

    let import_naked_int32_type_as_resolved_ty_naked_int32
          (ty : ty_naked_int32) : resolved_ty_naked_int32 =
      match ty.descr with
      | Ok descr ->
        { descr;
          var = ty.var;
          symbol = ty.symbol;
        }
      | Load_lazily load_lazily ->
        let resolve_predefined_exception _sym = None in
        let create_resolved_t t
              : resolved_ty_naked_int32 create_resolved_t_result =
          match t with
          | Naked_int32 ty ->
            begin match ty.descr with
            | Ok descr ->
              Ok {
                descr;
                var = ty.var;
                symbol = ty.symbol;
              }
            | Load_lazily ll -> Load_lazily_again ll
            end
          | Value _
          | Naked_immediate _
          | Naked_float _
          | Naked_int64 _
          | Naked_nativeint _ ->
            Misc.fatal_errorf "Kind mismatch when importing %a; expected kind \
                [Naked_int32]"
              print_load_lazily load_lazily
        in
        let result =
          import_type load_lazily ~create_resolved_t
            ~resolve_predefined_exception
        in
        match result with
        | Ok result -> result
        | Treat_as_unknown_must_scan reason ->
          unknown_as_resolved_ty_naked_int32 reason ()

    let import_naked_int32_type ty : resolved_t =
      Naked_int32 (import_naked_int32_type_as_resolved_ty_naked_int32 ty)

    let import_naked_int64_type_as_resolved_ty_naked_int64
          (ty : ty_naked_int64) : resolved_ty_naked_int64 =
      match ty.descr with
      | Ok descr ->
        { descr;
          var = ty.var;
          symbol = ty.symbol;
        }
      | Load_lazily load_lazily ->
        let resolve_predefined_exception _sym = None in
        let create_resolved_t t
              : resolved_ty_naked_int64 create_resolved_t_result =
          match t with
          | Naked_int64 ty ->
            begin match ty.descr with
            | Ok descr ->
              Ok {
                descr;
                var = ty.var;
                symbol = ty.symbol;
              }
            | Load_lazily ll -> Load_lazily_again ll
            end
          | Value _
          | Naked_immediate _
          | Naked_float _
          | Naked_int32 _
          | Naked_nativeint _ ->
            Misc.fatal_errorf "Kind mismatch when importing %a; expected kind \
                [Naked_int64]"
              print_load_lazily load_lazily
        in
        let result =
          import_type load_lazily ~create_resolved_t
            ~resolve_predefined_exception
        in
        match result with
        | Ok result -> result
        | Treat_as_unknown_must_scan reason ->
          unknown_as_resolved_ty_naked_int64 reason ()

    let import_naked_int64_type ty : resolved_t =
      Naked_int64 (import_naked_int64_type_as_resolved_ty_naked_int64 ty)

    let import_naked_nativeint_type_as_resolved_ty_naked_nativeint
          (ty : ty_naked_nativeint) : resolved_ty_naked_nativeint =
      match ty.descr with
      | Ok descr ->
        { descr;
          var = ty.var;
          symbol = ty.symbol;
        }
      | Load_lazily load_lazily ->
        let resolve_predefined_exception _sym = None in
        let create_resolved_t t
              : resolved_ty_naked_nativeint create_resolved_t_result =
          match t with
          | Naked_nativeint ty ->
            begin match ty.descr with
            | Ok descr ->
              Ok {
                descr;
                var = ty.var;
                symbol = ty.symbol;
              }
            | Load_lazily ll -> Load_lazily_again ll
            end
          | Value _
          | Naked_immediate _
          | Naked_float _
          | Naked_int32 _
          | Naked_int64 _ ->
            Misc.fatal_errorf "Kind mismatch when importing %a; expected kind \
                [Naked_nativeint]"
              print_load_lazily load_lazily
        in
        let result =
          import_type load_lazily ~create_resolved_t
            ~resolve_predefined_exception
        in
        match result with
        | Ok result -> result
        | Treat_as_unknown_must_scan reason ->
          unknown_as_resolved_ty_naked_nativeint reason ()

    let import_naked_nativeint_type ty : resolved_t =
      Naked_nativeint (
        import_naked_nativeint_type_as_resolved_ty_naked_nativeint ty)
  end

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

  let print_with_var_and_symbol print_descr ppf { descr; var; symbol; } =
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

  let print_maybe_unresolved print_contents ppf (m : _ maybe_unresolved) =
    match m with
    | Ok contents -> print_contents ppf contents
    | Load_lazily (Export_id (id, kind)) ->
      Format.fprintf ppf "lazy[%a](eid %a)"
        K.print kind
        Export_id.print id
    | Load_lazily (Symbol sym) ->
      Format.fprintf ppf "lazy[%a](sym %a)"
        K.print (K.value ())
        Symbol.print sym

  let print_of_kind_naked_immediate ppf (o : of_kind_naked_immediate) =
    match o with
    | Naked_int i -> Format.fprintf ppf "%a" Targetint.print i
    | Naked_char c -> Format.fprintf ppf "%c" c
    | Naked_constptr i -> Format.fprintf ppf "%aa" Targetint.print i

  let print_of_kind_naked_float ppf (o : of_kind_naked_float) =
    match o with
    | Naked_float f -> Format.fprintf ppf "%f" f

  let print_of_kind_naked_int32 ppf (o : of_kind_naked_int32) =
    match o with
    | Naked_int32 i -> Format.fprintf ppf "%a" Int32.print i

  let print_of_kind_naked_int64 ppf (o : of_kind_naked_int64) =
    match o with
    | Naked_int64 i -> Format.fprintf ppf "%a" Int64.print i

  let print_of_kind_naked_nativeint ppf (o : of_kind_naked_nativeint) =
    match o with
    | Naked_nativeint i -> Format.fprintf ppf "%a" Nativeint.print i

  let rec print_of_kind_value ppf (o : of_kind_value) =
    match o with
    | Singleton singleton -> print_of_kind_value_singleton ppf singleton
    | Union (w1, w2) ->
      let print_part ppf w =
        print_with_var_and_symbol print_of_kind_value ppf w
      in
      Format.fprintf "@[(Union (%a)(%a))@]" print w1 print w2

  and print_of_kind_value_singleton ppf (singleton : of_kind_value_singleton) =
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

  and print_or_unknown_or_bottom print_contents ppf
        (o : _ or_unknown_or_bottom) =
    match o with
    | Unknown reason ->
      begin match reason with
      | Unresolved_value value ->
        Format.fprintf ppf "?(due to unresolved %a)"
          print_unresolved_value value
      | Other -> Format.fprintf ppf "?"
      end;
    | Ok contents -> print_contents ppf contents
    | Bottom -> Format.fprintf ppf "bottom"

  and print_ty_generic print_contents ppf ty =
    print_with_var_and_symbol
      (print_maybe_unresolved
        (print_unknown_or_bottom print_contents))
      ppf ty

  and print_ty_value ppf (ty : ty_value) =
    print_ty_generic print_of_kind_value ppf ty

  and print_ty_naked_immediate ppf (ty : ty_naked_immediate) =
    print_ty_generic print_of_kind_naked_immediate ppf ty

  and print_ty_naked_float ppf (ty : ty_naked_float) =
    print_ty_generic print_of_kind_naked_float ppf ty

  and print_ty_naked_int32 ppf (ty : ty_naked_int32) =
    print_ty_generic print_of_kind_naked_int32 ppf ty

  and print_ty_naked_int64 ppf (ty : ty_naked_int64) =
    print_ty_generic print_of_kind_naked_int64 ppf ty

  and print_ty_naked_nativeint ppf (ty : ty_naked_nativeint) =
    print_ty_generic print_of_kind_naked_nativeint ppf ty

  and print ppf (t : t) =
    match t with
    | Value ty ->
      Format.fprintf ppf "(Value (%a))" print_ty_value ty
    | Naked_immediate ty ->
      Format.fprintf ppf "(Naked_immediate (%a))" print_ty_naked_immediate ty
    | Naked_float ty ->
      Format.fprintf ppf "(Naked_float (%a))" print_ty_naked_float ty
    | Naked_int32 ty ->
      Format.fprintf ppf "(Naked_int32 (%a))" print_ty_naked_int32 ty
    | Naked_int64 ty ->
      Format.fprintf ppf "(Naked_int64 (%a))" print_ty_naked_int64 ty
    | Naked_nativeint ty ->
      Format.fprintf ppf "(Naked_nativeint (%a))" print_ty_naked_nativeint ty

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

  let kind ~importer (t : t) =
    match t with
    | Naked_immediate _ -> K.naked_immediate ()
    | Naked_float _ -> K.naked_float ()
    | Naked_int32 _ -> K.naked_int32 ()
    | Naked_int64 _ -> K.naked_int64 ()
    | Naked_nativeint _ -> K.naked_nativeint ()
    | Value ty ->
      let descr =
        match ty with
        | Ok descr -> descr
        | Load_lazily load_lazily ->
          let module I = (val importer : Importer) in
          (I.import_value_type_as_resolved_ty_value load_lazily).descr
      in
      match descr with
      | Unknown _ -> K.value ~must_scan:true
      | Bottom -> K.value ~must_scan:false
      | Ok of_kind_value ->
        let rec must_scan (o : of_kind_value) =
          match o with
          | Singleton (Tagged_immediate _) -> false
          | Singleton _ -> true
          | Union (w1, w2) -> must_scan w1.descr || must_scan w2.descr
        in
        K.value ~must_scan:(must_scan of_kind_value)

(*
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
*)

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

  let rec free_variables t acc =
    match t with
    | Value ty_value -> free_variables_ty_value ty_value acc
    | Naked_immediate { var; _ }
    | Naked_float { var; _ }
    | Naked_int32 { var; _ }
    | Naked_int64 { var; _ }
    | Naked_nativeint { var; _ } ->
      match var with
      | None -> acc
      | Some var -> Variable.Set.add var acc

  and free_variables_ty_value ({ descr; var; _ } : ty_value) acc =
    let acc =
      match var with
      | None -> acc
      | Some var -> Variable.Set.add var acc
    in
    match descr with
    | Ok ((Unknown _) | Bottom) -> acc
    | Ok of_kind_value ->
      free_variables_of_kind_value of_kind_value acc
    | Load_lazily _load_lazily ->
      (* Types saved in .cmx files cannot contain free variables. *)
      acc

  and free_variables_of_kind_value (o : of_kind_value) acc =
    match o with
    | Singleton singleton ->
      begin match singleton with
      | Boxed_or_encoded_number (_kind, t) ->
        Variable.Set.union from_var (free_variables t)
      | Set_of_closures set_of_closures ->
        Var_within_closure.Map.fold (fun _var t acc ->
            free_variables t acc)
          set_of_closures.bound_vars acc
      | Closure { set_of_closures; closure_id = _; } ->
        free_variables set_of_closures acc
      | Immutable_string _
      | Mutable_string _ -> acc
      | Float_array { contents; size = _; } ->
        begin match contents with
        | Contents ts ->
          Array.fold_left (fun acc t -> free_variables t acc)
            acc ts
        | Unknown_or_mutable -> acc
        end
      end
    | Union (w1, w2) ->
      let acc =
        match w1.var with
        | None -> acc
        | Some var -> Variable.Set.add var acc
      in
      let acc =
        match w2.var with
        | None -> acc
        | Some var -> Variable.Set.add var acc
      in
      free_variables_of_kind_value w2.descr
        (free_variables_of_kind_value w1.descr acc)

  let free_variables t =
    free_variables t Variable.Set.empty


(*
  let rec clean ~import_type t classify =
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
*)
  let rec join_ty (type a) ~import_type join_contents (ty1 : a ty) (ty2 : a ty)
        : a ty =
    let resolve ty : a resolved_ty =
      match ty with
      | Ok descr ->
        { descr;
          var;
          symbol;
        }
      | Load_lazily load_lazily -> import_type load_lazily
    in
    let ty1 : a resolved_ty = resolve ty1 in
    let ty2 : a resolved_ty = resolve ty2 in
    let var =
      match ty1.var, ty2.var with
      | None, _ | _, None -> None
      | Some v1, Some v2 ->
        if Variable.equal v1 v2 then Some v1
        else None
    in
    let symbol =
      match ty1.symbol, ty2.symbol with
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
      match ty1.descr, ty2.descr with
      | Unknown, _ -> ty1
      | _, Unknown -> ty2
      | Bottom, _ -> ty2
      | _, Bottom -> ty1
      | Ok contents1, Ok contents2 -> join_contents ty1 contents1 ty2 contents2
    in
    Ok {
      descr;
      var;
      symbol;
    }

  and join_value ty1 (t1 : of_kind_value) ty2 t2 ~import_type
        : of_kind_value unknown_or_bottom =
    let form_union () : of_kind_value unknown_or_bottom =
      let w1 : of_kind_value with_var_and_symbol =
        { descr = t1;
          var = ty1.var;
          symbol = ty1.symbol;
        }
      in
      let w2 : of_kind_value with_var_and_symbol =
        { descr = t2;
          var = ty2.var;
          symbol = ty2.symbol;
        }
      in
      Ok (Union (w1, w2))
    in
    match t1, t2 with
    | Singleton s1, Singleton s2 ->
      begin match join_value_singleton s1 s2 ~import_type with
      | Singleton result -> result
      | Form_union -> form_union ()
      end
    | Singleton _, Union _
    | Union _, Singleton _
    | Union _, Union _ -> form_union ()

  and join_value_singleton (t1 : of_kind_value_singleton) t2
        ~import_type : of_kind_value unknown_or_bottom or_union =
    (* For cases where forming unions is fruitless, we just return [Unknown]. *)
    match t1, t2 with
    | Boxed_or_encoded_number (kind1, ty1),
        Boxed_or_encoded_number (kind2, ty2) ->
      if not (Boxed_or_encoded_number_kind.equal kind1 kind2) then Unknown
      else
        let ty = join_ty join_ty_value ty1 ty2 ~import_type in
        Singleton (Ok (Boxed_or_encoded_number (kind1, ty)))
    | Block (tag1, fields1), Block (tag2, fields2) ->
      if not (Tag.Scannable.equal tag1 tag2) then Form_union
      else if Array.length fields1 <> Array.length fields2 then Unknown
      else
        let fields =
          Array.map2 (fun ty1 ty2 -> join_ty join_ty_value ty1 ty2 ~import_type)
            fields1 fields2
        in
        Singleton (Ok (Block (tag1, fields)))
    | Set_of_closures _, Set_of_closures _ -> Form_union
    | Closure _, Closure _ -> Form_union
    | String { contents = Contents str1; _ },
        String { contents = Contents str2; _ } ->
      if String.equal str1 str2 then Singleton (Ok t1)
      else Unknown
    | Float_array { contents = Contents ts1; _ },
        Float_array { contents = Contents ts2; _ } ->
      if Array.length ts1 <> Array.length ts2 then Unknown
      else
        let ts =
          Array.map2 (fun ty1 ty2 -> join_ty join_ty_value ty1 ty2 ~import_type)
            ts1 ts2
        in
        Singleton (Ok (Float_array {
          contents = Contents ts;
          size = Array.length ts;
        }))
    | _, _ -> Unknown

  and join_naked_immediate _ty1 (t1 : of_kind_naked_immediate) _ty2 t2
        ~import_type:_ : of_kind_naked_immediate unknown_or_bottom =
    match t1, t2 with
    | Naked_int i1, Naked_int i2 ->
      if Targetint.equal i1 i2 then Ok (Naked_int i1)
      else Unknown
    | Naked_char i1, Naked_char i2 ->
      if Char.equal i1 i2 then Ok (Naked_char i1)
      else Unknown
    | Naked_constptr i1, Naked_constptr i2 ->
      if Targetint.equal i1 i2 then Ok (Naked_constptr i1)
      else Unknown

  and join_naked_int32 _ty1 (t1 : of_kind_naked_int32) _ty2 t2 ~import_type:_
        : of_kind_naked_int32 unknown_or_bottom =
    match t1, t2 with
    | Naked_int32 i1, Naked_int32 i2 ->
      if Int32.equal i1 i2 then Ok (Naked_int32 i1)
      else Unknown

  and join_naked_int64 _ty1 (t1 : of_kind_naked_int64) _ty2 t2 ~import_type:_
        : of_kind_naked_int64 unknown_or_bottom =
    match t1, t2 with
    | Naked_int64 i1, Naked_int64 i2 ->
      if Int64.equal i1 i2 then Ok (Naked_int64 i1)
      else Unknown

  and join_naked_nativeint _ty1 (t1 : of_kind_naked_nativeint) _ty2 t2
        ~import_type:_ : of_kind_naked_nativeint unknown_or_bottom =
    match t1, t2 with
    | Naked_nativeint i1, Naked_nativeint i2 ->
      if Targetint.equal i1 i2 then Ok (Naked_nativeint i1)
      else Unknown

  let join ~importer (t1 : t) (t2 : t) : t =
    let module B = (val importer : Importer) in
    match t1, t2 with
    | Value ty1, Value ty2 ->
      Value (join_ty ~importer join_value ty1 ty2
        ~import_type:B.import_value_type)
    | Naked_immediate ty1, Naked_immediate ty2 ->
      Naked_immediate (join_ty ~importer join_naked_immediate ty1 ty2
        ~import_type:B.import_naked_immediate_type)
    | Naked_float ty1, Naked_float ty2 ->
      Naked_float (join_ty ~importer join_naked_float ty1 ty2
        ~import_type:B.import_naked_float_type)
    | Naked_int32 ty1, Naked_int32 ty2 ->
      Naked_int32 (join_ty ~importer join_naked_int32 ty1 ty2
        ~import_type:B.import_naked_int32_type)
    | Naked_int64 ty1, Naked_int64 ty2 ->
      Naked_int64 (join_ty ~importer join_naked_int64 ty1 ty2
        ~import_type:B.import_naked_int64_type)
    | Naked_nativeint ty1, Naked_nativeint ty2 ->
      Naked_nativeint (join_ty ~importer join_naked_nativeint ty1 ty2
        ~import_type:B.import_naked_nativeint_type)
    | _, _ ->
      Misc.fatal_errorf "Cannot take the join of two types with different \
          kinds: %a and %a"
        print t1
        print t2
end
