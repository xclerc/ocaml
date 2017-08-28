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
module Nativeint = Numbers.Nativeint

type 'a simple_commutative_op = 'a -> 'a -> 'a

module Make (Function_declarations : sig
  type t
  val print : Format.formatter -> t -> unit
end) = struct
  type function_declarations = Function_declarations.t

  module Boxed_number_kind = struct
    type t =
      | Float
      | Int32
      | Int64
      | Nativeint

    include Identifiable.Make (struct
      type nonrec t = t

      let compare t1 t2 = Pervasives.compare t1 t2

      let equal t1 t2 = (compare t1 t2 = 0)

      let hash t = Hashtbl.hash t

      let print ppf t =
        match t with
        | Float -> Format.fprintf ppf "float"
        | Int32 -> Format.fprintf ppf "int32"
        | Int64 -> Format.fprintf ppf "int64"
        | Nativeint -> Format.fprintf ppf "nativeint"

      let output _ _ = Misc.fatal_error "Not implemented"
    end)
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
    | Export_id of Export_id.t
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

  module rec T : sig
    type value_string = {
      (* CR-soon mshinwell: use variant *)
      contents : string option; (* None if unknown or mutable *)
      size : int;
    }

    (** The type of an Flambda term. *)
    type t = {
      descr : descr;
      var : Variable.t option;
      projection : Projection.t option;
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
      Flambda.Expr.t on function bodies. *)
    and descr =
      | Unknown of Flambda_kind.t * unknown_because_of
      | Union of Unionable.t
      | Unboxed_float of Numbers.Float.Set.t
      | Unboxed_int32 of Numbers.Int32.Set.t
      | Unboxed_int64 of Numbers.Int64.Set.t
      | Unboxed_nativeint of Numbers.Nativeint.Set.t
      | Boxed_number of Boxed_number_kind.t * t
      | Set_of_closures of set_of_closures
      | Closure of closure
      | Immutable_string of string
      | Mutable_string of { size : int; }
      | Float_array of float_array
      | Bottom
      | Load_lazily of load_lazily

    and closure = {
      potential_closures : t Closure_id.Map.t;
      (** Map of closures ids to set of closures *)
    } [@@unboxed]

    (* CR-soon mshinwell: add support for the approximations of the results, so we
       can do all of the tricky higher-order cases. *)
    and set_of_closures = {
      function_decls : Function_declarations.t;
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

    and float_array = {
      contents : float_array_contents;
      size : int;
    }

    val join
      : really_import_approx:(t -> t)
      -> t
      -> t
      -> t
    val print
       : Format.formatter
      -> t
      -> unit
    val print_descr
       : Format.formatter
      -> descr
      -> unit
    val print_set_of_closures
       : Format.formatter
      -> set_of_closures
      -> unit
    val kind
      : t
      -> really_import_approx:(t -> t)
      -> Flambda_kind.t
    val kind_exn : t -> Flambda_kind.t
    val unknown : Flambda_kind.t -> unknown_because_of -> t
    val bottom : unit -> t
    val int : int -> t
    val constptr : int -> t
    val char : char -> t
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
    val mutable_string : size:int -> t
    val immutable_string : string -> t
    val block : Tag.t -> t array -> t
    val export_id_loaded_lazily : Export_id.t -> t
    val symbol_loaded_lazily : Symbol.t -> t
    val any_boxed_float : unit -> t
    val any_unboxed_float : unit -> t
    val any_unboxed_int32 : unit -> t
    val any_unboxed_int64 : unit -> t
    val any_unboxed_nativeint : unit -> t
    val closure
       : ?closure_var:Variable.t
      -> ?set_of_closures_var:Variable.t
      -> ?set_of_closures_symbol:Symbol.t
      -> set_of_closures Closure_id.Map.t
      -> t
    val create_set_of_closures
       : function_decls:Function_declarations.t
      -> size:int option Variable.Map.t lazy_t
      -> bound_vars:t Var_within_closure.Map.t
      -> invariant_params:Variable.Set.t Variable.Map.t lazy_t
      -> freshening:closure_freshening
      -> direct_call_surrogates:Closure_id.t Closure_id.Map.t
      -> set_of_closures
    val set_of_closures
       : ?set_of_closures_var:Variable.t
      -> set_of_closures
      -> t
    val update_freshening_of_set_of_closures
       : set_of_closures
      -> freshening:closure_freshening
      -> set_of_closures
    val augment_with_variable : t -> Variable.t -> t
    val update_variable : t -> Variable.t option -> t
    val augment_with_symbol : t -> Symbol.t -> t
    val augment_with_symbol_field : t -> Symbol.t -> int -> t
    val replace_description : t -> descr -> t
    val refine_using_value_kind : t -> Lambda.value_kind -> t
    val free_variables : t -> Variable.Set.t
    type cleaning_spec =
      | Available
      | Available_different_name of Variable.t
      | Unavailable
    val clean
       : t
      -> (Variable.t -> cleaning_spec)
      -> t
  end = struct
    include T

    let print_value_set_of_closures ppf
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
      | Load_lazily (Export_id id) ->
        Format.fprintf ppf "_%a_" Export_id.print id
      | Load_lazily (Symbol sym) ->
        Format.fprintf ppf "%a" Symbol.print sym
      | Closure { potential_closures } ->
        Format.fprintf ppf "(closure:@ @[<2>[@ ";
        Closure_id.Map.iter (fun closure_id set_of_closures ->
          Format.fprintf ppf "%a @[<2>from@ %a@];@ "
            Closure_id.print closure_id
            (print) set_of_closures)
          potential_closures;
        Format.fprintf ppf "]@])";
      | Set_of_closures set_of_closures ->
        print_value_set_of_closures ppf set_of_closures
      | Unboxed_float fs -> Format.fprintf ppf "float(%a)" Float.Set.print fs
      | Unboxed_int32 ns -> Format.fprintf ppf "int32(%a)" Int32.Set.print ns
      | Unboxed_int64 ns -> Format.fprintf ppf "int64(%a)" Int64.Set.print ns
      | Unboxed_nativeint ns ->
        Format.fprintf ppf "nativeint(%a)" Nativeint.Set.print ns
      | Boxed_number (bn, t) ->
        Format.fprintf ppf "box_%a(%a)"
          Boxed_number_kind.print bn
          (print) t
      | Immutable_string contents ->
        let size = String.length contents in
        let contents =
          if size > 10
          then String.sub contents 0 8 ^ "..."
          else contents
        in
        Format.fprintf ppf "immut_string %i %S" size contents
      | Mutable_string { size; } ->
        Format.fprintf ppf "mut_string %i" size
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
        (print_descr) descr
        Variable.print_opt var
        print symbol

    let kind t ~really_import_approx : Flambda_kind.t =
      match t.descr with
      | Unknown (kind, _) -> kind
      | Unboxed_float _ -> Flambda_kind.unboxed_float ()
      | Unboxed_int32 _ -> Flambda_kind.unboxed_int32 ()
      | Unboxed_int64 _ -> Flambda_kind.unboxed_int64 ()
      | Unboxed_nativeint _ -> Flambda_kind.unboxed_nativeint ()
      | Union _
      | Boxed_number _
      | Set_of_closures _
      | Closure _
      | Immutable_string _
      | Mutable_string _
      | Float_array _ -> Flambda_kind.value ()
      | Bottom -> Flambda_kind.bottom ()
      | Load_lazily _ -> kind (really_import_approx t) ~really_import_approx

    let kind_exn t =
      let really_import_approx t =
        Misc.fatal_errorf "With_free_variables.create_let_reusing_body: \
            Flambda type is not fully resolved: %a"
          print t
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

    module type Meet_or_join = sig
      val meet_or_join
         : really_import_approx:(t -> t)
        -> t
        -> t
        -> t
    end

    module Meet_or_join (AG : sig
      val name : string

      val is_unit : t -> bool

      module Ops : sig
        val unionable
           : really_import_approx:(t -> t)
          -> Unionable.t
          -> Unionable.t
          -> Unionable.t Unionable.or_bottom

        val float_set : Float.Set.t simple_commutative_op
        val int32_set : Int32.Set.t simple_commutative_op
        val int64_set : Int64.Set.t simple_commutative_op
        val nativeint_set : Nativeint.Set.t simple_commutative_op

        val closure_id_map
           : (t -> t -> t option)
          -> t Closure_id.Map.t 
          -> t Closure_id.Map.t
          -> t Closure_id.Map.t
      end
    end) (Inverse : Meet_or_join) : Meet_or_join = struct
      let rec meet_or_join_descr kind ~really_import_approx d1 d2 =
        match d1, d2 with
        | Union union1, Union union2 ->
          begin match AG.Ops.unionable union1 union2 ~really_import_approx with
          | Ok union -> Union union
          | Ill_typed_code -> Bottom
          | Anything -> Unknown (Flambda_kind.value (), Other)
          end
        | Unboxed_float fs1, Unboxed_float fs2 ->
          Unboxed_float (AG.Ops.float_set fs1 fs2)
        | Unboxed_int32 is1, Unboxed_int32 is2 ->
          Unboxed_int32 (AG.Ops.int32_set is1 is2)
        | Unboxed_int64 is1, Unboxed_int64 is2 ->
          Unboxed_int64 (AG.Ops.int64_set is1 is2)
        | Unboxed_nativeint is1, Unboxed_nativeint is2 ->
          Unboxed_nativeint (AG.Ops.nativeint_set is1 is2)
        | Boxed_number (Float, t1), Boxed_number (Float, t2) ->
          Boxed_number (Float, meet_or_join ~really_import_approx t1 t2)
        | Boxed_number (Int32, t1), Boxed_number (Int32, t2) ->
          Boxed_number (Int32, meet_or_join ~really_import_approx t1 t2)
        | Boxed_number (Int64, t1), Boxed_number (Int64, t2) ->
          Boxed_number (Int64, meet_or_join ~really_import_approx t1 t2)
        | Boxed_number (Nativeint, t1), Boxed_number (Nativeint, t2) ->
          Boxed_number (Nativeint, meet_or_join ~really_import_approx t1 t2)
        | Load_lazily (Export_id e1), Load_lazily (Export_id e2)
            when Export_id.equal e1 e2 -> d1
        | Load_lazily (Symbol s1), Load_lazily (Symbol s2)
            when Symbol.equal s1 s2 -> d1
        | Closure { potential_closures = map1 },
          Closure { potential_closures = map2 } ->
          let potential_closures =
            AG.Ops.closure_id_map
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
              (Inverse.meet_or_join ~really_import_approx)
              map1 map2
          in
          Closure { potential_closures }
        | _ -> Unknown (kind, Other)

      and meet_or_join ~really_import_approx a1 a2 =
        let kind1 = kind a1 ~really_import_approx in
        let kind2 = kind a2 ~really_import_approx in
        if Flambda_kind.compatible kind1 kind2 then begin
          if AG.is_unit a1 then a2
          else if AG.is_unit a2 then a1
          else
            match a1, a2 with
            | { descr = Load_lazily _ }, _
            | _, { descr = Load_lazily _ } ->
              meet_or_join ~really_import_approx
                (really_import_approx a1) (really_import_approx a2)
            | _ ->
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
                  meet_or_join_descr kind1 ~really_import_approx
                    a1.descr a2.descr
                in
                { descr;
                  var;
                  projection;
                  symbol;
                }
        end else begin
          Misc.fatal_errorf "Cannot take the %s of two types with incompatible \
              kinds: %a and %a"
            AG.name
            print a1
            print a2
        end
    end

    module rec Join : Meet_or_join =
      Meet_or_join (struct
        let name = "join"

        let is_unit t =
          match t.descr with
          | Unknown _ -> true
          | _ -> false

        module Ops = struct
          let unionable = Unionable.join
          let float_set = Float.Set.union
          let int32_set = Int32.Set.union
          let int64_set = Int64.Set.union
          let nativeint_set = Nativeint.Set.union
          let closure_id_map = Closure_id.Map.union
        end
      end) (Meet)
    and Meet : Meet_or_join =
      Meet_or_join (struct
        let name = "meet"

        let is_unit t =
          match t.descr with
          | Bottom -> true
          | _ -> false

        module Ops = struct
          let unionable = Unionable.meet
          let float_set = Float.Set.inter
          let int32_set = Int32.Set.inter
          let int64_set = Int64.Set.inter
          let nativeint_set = Nativeint.Set.inter
          let closure_id_map = Closure_id.Map.inter
        end
      end) (Join)

    let join = Join.meet_or_join
    let meet = Meet.meet_or_join

    let just_descr descr =
      { descr; var = None; projection = None; symbol = None; }

    let refine_using_value_kind t (kind : Lambda.value_kind) =
      match kind with
      | Pgenval -> t
      | Pfloatval ->
        begin match t.descr with
        | Boxed_number (Float, { descr = Unboxed_float _; _ }) ->
          t
        | Unknown ((Unboxed_float | Bottom), reason) ->
          { t with
            descr = Boxed_number (Float,
              just_descr (Unknown (Flambda_kind.unboxed_float (), reason)));
          }
        | Unknown (
            (Value | Unboxed_int32 | Unboxed_int64 | Unboxed_nativeint), _) ->
          Misc.fatal_errorf "Wrong type for Pfloatval kind: %a"
            print t
        | Union _
        | Unboxed_float _
        | Unboxed_int32 _
        | Unboxed_int64 _
        | Unboxed_nativeint _
        | Boxed_number _
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
    let int i = just_descr (Union (Unionable.int i))
    let char i = just_descr (Union (Unionable.char i))
    let constptr i = just_descr (Union (Unionable.constptr i))
    let unboxed_float n = just_descr (Unboxed_float (Float.Set.singleton n))
    let unboxed_int32 n = just_descr (Unboxed_int32 (Int32.Set.singleton n))

    let unboxed_int64 n =
      if Targetint.size < 64 then
        Misc.fatal_errorf "Cannot create unboxed int64 Flambda types on this \
            target platform"
      else
        just_descr (Unboxed_int64 (Int64.Set.singleton n))

    let unboxed_nativeint n =
      just_descr (Unboxed_nativeint (Nativeint.Set.singleton n))
    let boxed_float f = just_descr (Boxed_number (Float, unboxed_float f))
    let boxed_int32 i = just_descr (Boxed_number (Int32, unboxed_int32 i))
    let boxed_int64 i = just_descr (Boxed_number (Int64, unboxed_int64 i))
    let boxed_nativeint i =
      just_descr (Boxed_number (Nativeint, unboxed_nativeint i))
    let export_id_loaded_lazily ex = just_descr (Load_lazily (Export_id ex))
    let symbol_loaded_lazily sym =
      { (just_descr (Load_lazily (Symbol sym))) with symbol = Some (sym, None); }
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
      just_descr (Unknown (Flambda_kind.unboxed_float (), Other))
    let any_unboxed_int32 () =
      just_descr (Unknown (Flambda_kind.unboxed_int32 (), Other))
    let any_unboxed_int64 () =
      just_descr (Unknown (Flambda_kind.unboxed_int64 (), Other))
    let any_unboxed_nativeint () =
      just_descr (Unknown (Flambda_kind.unboxed_nativeint (), Other))

    let any_boxed_float () =
      just_descr (Boxed_number (Float, any_unboxed_float ()))

    let closure ?closure_var ?set_of_closures_var ?set_of_closures_symbol
          closures =
      let approx_set_of_closures value_set_of_closures =
        { descr = Set_of_closures value_set_of_closures;
          var = set_of_closures_var;
          projection = None;
          symbol = Misc.may_map (fun s -> s, None) set_of_closures_symbol;
        }
      in
      let potential_closures =
        Closure_id.Map.map approx_set_of_closures closures
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
      | None -> unknown (Flambda_kind.value ()) Other
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
  end and Unionable : sig
    module Immediate : sig
      type t = private
        (* CR mshinwell: We could consider splitting these again *)
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
       1. It doesn't involve any comparison on values of type [t.t].
       2. It lines up with the classification of approximations required when
           unboxing (cf. [Unbox_one_variable]). *)
    type t = private
      | Blocks of blocks
      | Blocks_and_immediates of blocks * Immediate.Set.t
      | Immediates of Immediate.Set.t

    val invariant : t -> unit

    val print
       : Format.formatter
      -> t
      -> unit

    val map_blocks : t -> f:(blocks -> blocks) -> t

    (** Partial ordering:
          Ill_typed_code <= Ok _ <= Anything
    *)
    type 'a or_bottom =
      | Anything
      | Ok of 'a
      | Ill_typed_code

    val join
      : really_import_approx:(T.t -> T.t)
      -> t
      -> t
      -> t or_bottom

    val meet
      : really_import_approx:(T.t -> T.t)
      -> t
      -> t
      -> t or_bottom

    type singleton = private
      | Block of Tag.Scannable.t * (T.t array)
      | Int of int
      | Char of char
      | Constptr of int

    (** Find the properties that are guaranteed to hold of a value with union type
        at every point it is used. *)
    val flatten : t -> singleton or_bottom

    val is_singleton : t -> bool

    val int : int -> t
    val char : char -> t
    val constptr : int -> t
    val block : Tag.Scannable.t -> T.t array -> t

    val useful : t -> bool

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

    let map_blocks t ~f =
      match t with
      | Blocks blocks -> Blocks (f blocks)
      | Blocks_and_immediates (blocks, imms) ->
        Blocks_and_immediates (f blocks, imms)
      | Immediates _ -> t

    let is_singleton t =
      invariant t;
      match t with
      | Blocks blocks -> Tag.Scannable.Map.cardinal blocks = 1
      | Blocks_and_immediates (blocks, imms) ->
        (Tag.Scannable.Map.cardinal blocks = 1 && Immediate.Set.is_empty imms)
          || (Tag.Scannable.Map.is_empty blocks && Immediate.Set.cardinal imms = 1)
      | Immediates imms -> Immediate.Set.cardinal imms = 1

    let int i =
      Immediates (Immediate.Set.singleton (Int i))

    let char c =
      Immediates (Immediate.Set.singleton (Char c))

    let constptr p =
      Immediates (Immediate.Set.singleton (Constptr p))

    let block tag fields =
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
           not used at or above No_scan_tag either.
           In fact if we had our own type of primitives we could statically
           enforce it (or maybe we could anyway) *)
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

    module Make_meet_or_join (Ops : sig
      val t
         : really_import_approx:(t -> t)
        -> t
        -> t
        -> t

      val immediate_set : Immediate.Set.t simple_commutative_op

      val tag_map
         : (Tag.t -> 'a -> 'a -> 'a)
        -> 'a Tag.Scannable.Map.t
        -> 'a Tag.Scannable.Map.t
        -> 'a Tag.Scannable.Map.t
    end) = struct
      let meet_or_join ~really_import_approx (t1 : t) (t2 : t) : t or_bottom =
        invariant t1;
        invariant t2;
        let get_immediates t =
          match t with
          | Blocks _ -> Immediate.Set.empty
          | Blocks_and_immediates (_, imms) | Immediates imms -> imms
        in
        let immediates_t1 = get_immediates t1 in
        let immediates_t2 = get_immediates t2 in
        let immediates = Ops.immediate_set immediates_t1 immediates_t2 in
        let get_blocks t =
          match t with
          | Blocks by_tag | Blocks_and_immediates (by_tag, _) -> by_tag
          | Immediates _ -> Tag.Scannable.Map.empty
        in
        let blocks_t1 = get_blocks t1 in
        let blocks_t2 = get_blocks t2 in
        let anything = ref false in
        let blocks =
          Ops.tag_map (fun _tag fields1 fields2 ->
              if Array.length fields1 <> Array.length fields2 then begin
                anything := true;
                None
              end else begin
                Some (Array.map2 (fun field existing_field ->
                    Ops.t ~really_import_approx field existing_field)
                  fields1 fields2)
              end)
            blocks_t1 blocks_t2
        in
        if !anything then
          Anything
        else if Immediate.Set.is_empty immediates then
          Ok (Blocks blocks)
        else if Tag.Scannable.Map.is_empty blocks then
          Ok (Immediates immediates)
        else
          Ok (Blocks_and_immediates (blocks, immediates))
    end

    module Join = Make_meet_or_join (struct
      let t = T.join
      let immediate_set = Immediate.Set.union
      let tag_map = Tag.Scannable.Map.union_merge
    end)

    let join = Join.meet_or_join

    module Meet = Make_meet_or_join (struct
      let t = T.join
      let immediate_set = Immediate.Set.inter
      let tag_map = Tag.Scannable.Map.inter
    end)

    let meet = Meet.meet_or_join

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

  include T
end
