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

module B = Inlining_cost.Benefit
module E = Simplify_env_and_result.Env
module K = Flambda_kind
module R = Simplify_env_and_result.Result
module T = Flambda_type

module Named = Flambda.Named
module Reachable = Flambda.Reachable

type named_simplifier =
  (Variable.t * Named.t) list * Reachable.t
    * Flambda_type.t * R.t

(* Simplify an expression that takes a set of closures and projects an
   individual closure from it. *)
let simplify_project_closure env r
      ~(project_closure : Projection.Project_closure.t) : named_simplifier =
  let set_of_closures, set_of_closures_ty =
    freshen_and_squash_aliases env project_closure.set_of_closures
  in
  let closure_id = project_closure.closure_id in
  let importer = E.importer env in
  match T.prove_set_of_closures ~importer set_of_closures_ty with
  | Wrong ->
    let ty = Flambda_type.bottom (K.value Must_scan) in
    let term = Reachable.invalid () in
    [], ty, term
  | Unknown ->
    let ty = Flambda_type.bottom (K.value Must_scan) in
    let term =
      Reachable.reachable (Project_closure {
        set_of_closures;
        closure_id;
      })
    in
    [], ty, term
  | Known set ->
(*
    begin match Closure_id.Set.elements closure_id with
      | _ :: _ :: _ ->
        Format.printf "Set of closures type is not a singleton \
            in project closure@ %a@ %a@."
          T.print set_of_closures_type
          Projection.print_project_closure project_closure
      | [] ->
        Format.printf "Set of closures type is empty in project \
            closure@ %a@ %a@."
          T.print set_of_closures_type
          Projection.print_project_closure project_closure
      | _ ->
        ()
    end;
*)
    let projecting_from =
      match Flambda_type.Set_of_closures.set_of_closures_var set with
      | None -> None
      | Some set_of_closures_var ->
        let projection : Projection.t =
          Project_closure {
            set_of_closures = set_of_closures_var;
            closure_id;
          }
        in
        match E.find_projection env ~projection with
        | None -> None
        | Some var -> Some (var, projection)
    in
    match projecting_from with
    | Some (var, projection) ->
      let var, var_ty = freshen_and_squash_aliases env var in
      let r = R.map_benefit r (B.remove_projection projection) in
      if Flambda_type.is_bottom ~importer var_ty then
        [], Reachable.invalid (), r
      else
        [], Reachable.reachable (Var var), r
    | None ->
      assert false
(* XXX for pchambart to fix: 
      let if_not_reference_recursive_function_directly ()
        : (Variable.t * Named.t) list * Named.t_reachable
            * R.t =
        let set_of_closures_var =
          match set_of_closures_var with
          | Some set_of_closures_var' when E.mem env set_of_closures_var' ->
            set_of_closures_var
          | Some _ | None -> None
        in
        let ty =
          T.closure ?set_of_closures_var
            (Closure_id.Map.of_set (fun _ -> value_set_of_closures)
                closure_id)
        in
        [], Reachable (Project_closure { set_of_closures; closure_id; }),
          ty
      in
      match Closure_id.Set.get_singleton closure_id with
      | None ->
        if_not_reference_recursive_function_directly ()
      | Some closure_id ->
        match reference_recursive_function_directly env closure_id with
        | Some (flam, ty) -> [], Reachable flam, ty
        | None ->
          if_not_reference_recursive_function_directly ()
*)

(* Simplify an expression that, given one closure within some set of
   closures, returns another closure (possibly the same one) within the
   same set. *)
let simplify_move_within_set_of_closures env r
      ~(move_within_set_of_closures : Projection.Move_within_set_of_closures.t)
      : named_simplifier =
  let closure, closure_ty =
    freshen_and_squash_aliases env move_within_set_of_closures.closure
  in
  match T.prove_closure_allowing_unresolved closure_ty with
  | Wrong ->
    Misc.fatal_errorf "Wrong Flambda type when moving within set of \
        closures.  Flambda type: %a  Term: %a"
      T.print closure_ty
      Flambda.print_move_within_set_of_closures move_within_set_of_closures
  | Unresolved sym ->
    [], Reachable (Move_within_set_of_closures {
        closure;
        move = move_within_set_of_closures.move;
      }),
      ret r (T.unresolved_symbol sym)
  | Unknown ->
    [], Reachable (Move_within_set_of_closures {
        closure;
        move = move_within_set_of_closures.move;
      }),
      ret r (T.unknown Value Other)
  | Unknown_because_of_unresolved_value value ->
    (* For example: a move upon a (move upon a closure whose .cmx file
        is missing). *)
    [], Reachable (Move_within_set_of_closures {
        closure;
        move = move_within_set_of_closures.move;
      }),
      ret r (T.unknown Value (Unresolved_value value))
  | Ok (value_closures, set_of_closures_var, set_of_closures_symbol) ->
    let () =
      match Closure_id.Map.bindings value_closures with
      | _ :: _ :: _ ->
        Format.printf "Closure type is not a singleton in \
            move@ %a@ %a@."
          T.print closure_ty
          Projection.print_move_within_set_of_closures
          move_within_set_of_closures
      | [] ->
        Format.printf "Closure type is empty in move@ %a@ %a@."
          T.print closure_ty
          Projection.print_move_within_set_of_closures
          move_within_set_of_closures
      | _ ->
        ()
    in
    (* Freshening of the move. *)
    let move, type_map =
      Closure_id.Map.fold
        (fun closure_id_in_type
              (value_set_of_closures:T.set_of_closures)
              (move, type_map) ->
          (* Pas efficace: on refait le freshening de tout pour ne
             garder que la partie pertinente, mais n'est pas très
             grave parce que ces map sont petites (normalement) *)
          let freshened_move =
            Freshening.freshen_move_within_set_of_closures
              ~closure_freshening:value_set_of_closures.freshening
              move_within_set_of_closures.move
          in
          let start_from = closure_id_in_type in
          let move_to =
            try Closure_id.Map.find start_from freshened_move with
            | Not_found ->
              Misc.fatal_errorf "Move %a freshened to %a does not contain \
                                  projection for %a@.  Type is:@ %a@.\
                                  Environment:@ %a@."
                Projection.print_move_within_set_of_closures
                  move_within_set_of_closures
                (Closure_id.Map.print Closure_id.print) freshened_move
                Closure_id.print start_from
                (Closure_id.Map.print T.print_value_set_of_closures)
                  value_closures
                E.print env
          in
          assert(not (Closure_id.Map.mem start_from move));
          Closure_id.Map.add start_from move_to move,
          Closure_id.Map.add move_to value_set_of_closures type_map)
        value_closures (Closure_id.Map.empty, Closure_id.Map.empty)
    in
    let projection : Projection.t =
      Move_within_set_of_closures {
        closure;
        move;
      }
    in
    match Closure_id.Map.get_singleton value_closures,
          Closure_id.Map.get_singleton move with
    | None, Some _ | Some _, None ->
      (* After the freshening, move and value_closures have the same
         cardinality *)
      assert false
    | None, None ->
      let ty = T.closure ty_map in
      let move_within : Projection.Move_within_set_of_closures.t =
        { closure; move; }
      in
      [], Reachable (Move_within_set_of_closures move_within), ty
    | Some (_start_from, value_set_of_closures),
      Some (start_from, move_to) ->
      match E.find_projection env ~projection with
      | Some var ->
        freshen_and_squash_aliases_named env var ~f:(fun _env var var_ty ->
          let r = R.map_benefit r (B.remove_projection projection) in
          [], Reachable (Var var), var_ty)
      | None ->
        match reference_recursive_function_directly env move_to with
        | Some (flam, ty) -> [], Reachable flam, ty
        | None ->
          if Closure_id.equal start_from move_to then
            (* Moving from one closure to itself is a no-op.  We can return an
               [Var] since we already have a variable bound to the closure. *)
            [], Reachable (Var closure), closure_ty
          else
            match set_of_closures_var with
            | Some set_of_closures_var when E.mem env set_of_closures_var ->
              (* A variable bound to the set of closures is in scope,
                 meaning we can rewrite the [Move_within_set_of_closures] to a
                 [Project_closure]. *)
              let project_closure : Projection.Project_closure.t =
                { set_of_closures = set_of_closures_var;
                  closure_id = Closure_id.Set.singleton move_to;
                }
              in
              let ty =
                T.closure ~set_of_closures_var
                  (Closure_id.Map.singleton move_to value_set_of_closures)
              in
              [], Reachable (Project_closure project_closure), ty
            | Some _ | None ->
              match set_of_closures_symbol with
              | Some set_of_closures_symbol ->
                let set_of_closures_var = Variable.create "symbol" in
                let project_closure : Projection.Project_closure.t =
                  { set_of_closures = set_of_closures_var;
                    closure_id = Closure_id.Set.singleton move_to;
                  }
                in
                let ty =
                  T.closure ~set_of_closures_var ~set_of_closures_symbol
                    (Closure_id.Map.singleton move_to value_set_of_closures)
                in
                let bindings : (Variable.t * Named.t) list = [
                  set_of_closures_var, Symbol set_of_closures_symbol;
                ]
                in
                bindings, Reachable (Project_closure project_closure),
                  ty
              | None ->
                (* The set of closures is not available in scope, and we
                  have no other information by which to simplify the move. *)
                let move_within : Projection.Move_within_set_of_closures.t =
                  { closure; move; }
                in
                let ty = T.closure ty_map in
                [], Reachable (Move_within_set_of_closures move_within), ty

let rec simplify_project_var env r ~(project_var : Projection.Project_var.t)
      : named_simplifier =
  let closure, closure_ty =
    freshen_and_squash_aliases env project_var.closure
  in
  match T.prove_closure_allowing_unresolved closure_ty with
  | Ok (value_closures, _set_of_closures_var, _set_of_closures_symbol) ->
(*
    let () =
      match Closure_id.Map.bindings value_closures with
        | _ :: _ :: _ ->
          Format.printf "Closure type is not a singleton in \
              project@ %a@ %a@."
            T.print ty
            Projection.print_project_var project_var
        | [] ->
          Format.printf "Closure type is empty in project@ %a@ %a@."
            T.print ty
            Projection.print_project_var project_var
        | _ ->
          ()
    in
*)
    (* Freshening of the projection *)
    let project_var_var, ty =
      Closure_id.Map.fold
        (fun closure_id_in_type
          (value_set_of_closures : T.set_of_closures)
          (project_var_var, set_type) ->
          let freshened_var =
            Freshening.freshen_project_var project_var.var
              ~closure_freshening:value_set_of_closures.freshening
          in
          let closure_id = closure_id_in_type in
          let var =
            try Closure_id.Map.find closure_id_in_type freshened_var with
            | Not_found ->
              Misc.fatal_errorf "When simplifying [Project_var], the \
                closure ID %a in the type of the set of closures \
                did not match any closure ID in the [Project_var] term %a \
                freshened to %a. \
                Type: %a@."
                Closure_id.print closure_id_in_type
                Projection.print_project_var project_var
                (Closure_id.Map.print Var_within_closure.print) freshened_var
                Flambda_type.print ty
          in
          let set_type =
            let ty = T.type_for_bound_var value_set_of_closures var in
            let really_import_type = E.really_import_type env in
            T.join ~really_import_type ty set_type
          in
          Closure_id.Map.add closure_id var project_var_var,
          set_type)
        value_closures (Closure_id.Map.empty, T.bottom)
    in
    let projection : Projection.t =
      Project_var {
        closure;
        var = project_var_var;
      }
    in
    begin match E.find_projection env ~projection with
    | Some var ->
      freshen_and_squash_aliases_named env var ~f:(fun _env var var_ty ->
        let r = R.map_benefit r (B.remove_projection projection) in
        [], Reachable (Var var), var_ty)
    | None ->
      let expr : Named.t =
        Project_var { closure; var = project_var_var; }
      in
      let expr =
        match Closure_id.Map.get_singleton project_var_var with
        | None ->
          expr
        | Some (_closure_id, var) ->
          let unwrapped = Var_within_closure.unwrap var in
          if E.mem env unwrapped then
            Flambda.Var unwrapped
          else
            expr
      in
      simpler_equivalent_term env r expr ty
    end
  | Unknown ->
    [], Reachable.reachable (Project_var { project_var with closure }),
      r
  | Wrong ->
    [], Reachable.invalid (), r

(*
module Simplify_boxed_integer_operator (I : sig
  type t
  val kind : Lambda.boxed_integer
  val zero : t
  val add : t -> t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t
  val div : t -> t -> t
  val rem : t -> t -> t
  val logand : t -> t -> t
  val logor : t -> t -> t
  val logxor : t -> t -> t
  val shift_left : t -> int -> t
  val shift_right : t -> int -> t
  val shift_right_logical : t -> int -> t
  val to_int : t -> int
  val to_int32 : t -> Int32.t
  val to_int64 : t -> Int64.t
  val neg : t -> t
  val swap : t -> t
  val compare : t -> t -> int
end) : Simplify_boxed_integer_ops_intf.S with type t := I.t = struct
  module C = Inlining_cost
  module S = Simplify_common
  module T = Flambda_types

  let simplify_unop (p : Lambda.primitive) (kind : I.t T.boxed_int)
        expr (n : I.t) =
    let eval op = S.const_boxed_int_expr expr kind (op n) in
    let eval_conv kind op = S.const_boxed_int_expr expr kind (op n) in
    let eval_unboxed op = S.const_int_expr expr (op n) in
    match p with
    | Pintofbint kind when kind = I.kind -> eval_unboxed I.to_int
    | Pcvtbint (kind, Pint32) when kind = I.kind ->
      eval_conv T.Int32 I.to_int32
    | Pcvtbint (kind, Pint64) when kind = I.kind ->
      eval_conv T.Int64 I.to_int64
    | Pnegbint kind when kind = I.kind -> eval I.neg
    | Pbbswap kind when kind = I.kind -> eval I.swap
    | _ -> expr, T.value_unknown Other, C.Benefit.zero

  let simplify_binop (p : Lambda.primitive) (kind : I.t T.boxed_int)
        expr (n1 : I.t) (n2 : I.t) =
    let eval op = S.const_boxed_int_expr expr kind (op n1 n2) in
    let non_zero n = (I.compare I.zero n) <> 0 in
    match p with
    | Pbintcomp (kind, c) when kind = I.kind ->
      S.const_comparison_expr expr c n1 n2
    | _ -> expr, T.value_unknown Other, C.Benefit.zero

  let simplify_binop_int (p : Lambda.primitive) (kind : I.t T.boxed_int)
        expr (n1 : I.t) (n2 : int) ~size_int =
    let eval op = S.const_boxed_int_expr expr kind (op n1 n2) in
    let precond = 0 <= n2 && n2 < 8 * size_int in
    match p with
    | Plslbint kind when kind = I.kind && precond -> eval I.shift_left
    | Plsrbint kind when kind = I.kind && precond -> eval I.shift_right_logical
    | Pasrbint kind when kind = I.kind && precond -> eval I.shift_right
    | _ -> expr, T.value_unknown Other, C.Benefit.zero
end
*)

let simplify_unary_primitive env r prim arg dbg =
  match prim with
  | Block_load (field_index, field_kind, field_is_mutable) ->
    let arg, ty = S.simplify_simple env arg in
    let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
    let kind = Flambda_primitive.kind_of_field_kind field_kind in
    let get_field_result =
      (E.type_accessor env T.get_field) ty
        ~field_index ~field_is_mutable ~field_kind
    in
    begin match get_field_result with
    | Ok field_ty ->
      let reified =
        (E.type_accessor env T.reify) ~allow_free_variables:true field_ty
      in
      begin match reified with
      | Term (simple, ty) -> Named.Simple simple, ty
      | Cannot_reify -> original_term (), field_ty
      | Invalid -> Reachable.invalid (), T.bottom kind
      end
    | Invalid -> Reachable.invalid (), T.bottom kind
    end
  | Duplicate_array (new_array_kind, new_array_mut) ->
    let arg, ty = S.simplify_simple env arg in
    let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
    let like_a_block (scanning : Flambda_kind.scanning) =
      let proof =
        (E.type_accessor env T.prove_block_with_unique_tag_and_size) ty
      in
      match proof with
      | Proved (Ok (tag, fields)) ->
        (* We could in some circumstances turn the [Duplicate_array] into
           [Make_array], but it isn't clear what value this has, so we don't
           yet do it. *)
        let type_of_new_array =
          match new_array_mut with
          | Immutable -> T.block tag fields
          | Mutable ->
            let fields =
              Array.map (fun _field_ty -> T.unknown (K.value scanning) Other)
                fields
            in
            T.block tag fields
        in
        Reachable.reachable (original_term ())
      | Proved Not_all_values_known ->
        Reachable.reachable (original_term ()),
          T.unknown (K.value scanning) Other
      | Invalid ->
        Reachable.invalid (), T.bottom (K.value scanning)
    in
    begin match new_array_kind with
    | Dynamic_must_scan_or_naked_float ->
      original_term (), T.unknown (K.value Must_scan) Other
    | Must_scan -> like_a_block Must_scan
    | Can_scan -> like_a_block Can_scan
    | Naked_float ->

    end
  | Duplicate_record { repr; num_fields; } ->

  | Is_int ->
    let arg, ty = S.simplify_simple env arg in
    let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
    let proof = (E.type_accessor env T.prove_is_tagged_immediate) ty in
    begin match proof with
    | Proved is_tagged_immediate ->
      let simple =
        if is_tagged_immediate then Simple.const_true else Simple.const_false
      in
      let imm =
        if is_tagged_immediate then Immediate.bool_true
        else Immediate.bool_false
      in
      (* CR mshinwell: naming inconsistency const_true / bool_true *)
      Reachable.reachable (Simple simple),
        T.this_tagged_immediate imm
    | Proved Not_all_values_known ->
      Reachable.reachable (original_term ()),
        T.these_tagged_immediates Immediate.all_bools
    | Invalid -> 
      Reachable.invalid (), T.bottom (K.value Can_scan)
    end
  | Get_tag ->
    let arg, ty = S.simplify_simple env arg in
    let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
    let eval, _canonical_name = (E.type_accessor env T.Evaluated.create) ty in
    let tags = T.Evaluated.tags eval in
    begin match tags with
    | Not_all_values_known ->
      original_term (), T.these_tagged_immediates Tag.all_as_targetints
    | Exactly tags ->
      if Targetint.Set.is_empty tags then
        Reachable.invalid (), T.bottom (K.value Can_scan)
      else
        begin match Targetint.Set.get_singleton tags with
        | Some tag ->
          (* CR mshinwell: Add [Named.this_tagged_immediate] etc? *)
          let simple = Simple.const (Tagged_immediate tag) in
          Reachable.reachable (Simple simple),
            T.this_tagged_immediate tag
        | None ->
          original_term (), T.these_tagged_immediates tags
        end
    end
  | String_length string_or_bytes ->

  | Swap_byte_endianness Tagged_immediate ->
    let arg, ty = S.simplify_simple env arg in
    let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
    let proof = (E.type_accessor env T.prove_tagged_immediate) ty in
    begin match proof with
    | Proved imms ->
      let imms =
        Immediate.Set.map (fun imm ->
            Immediate.map (fun i ->
                Targetint.get_least_significant_16_bits_then_byte_swap i)
              imm)
          imms
      in
      (* XXX in these various cases (and below) shouldn't we be seeing if the
         [ty] has a canonical name associated with it? *)
      begin match Immediate.Set.get_singleton imms with
      | Some i ->
        let simple = Simple.const (Tagged_immediate i) in
        Reachable.reachable (Simple simple), T.this_tagged_immediate i
      | None ->
        Reachable.reachable (original_term ()), T.these_tagged_immediates imms
      end
    | Proved Not_all_values_known ->
      Reachable.reachable (original_term ()),
        T.unknown (K.value Can_scan) Other
    | Invalid -> 
      Reachable.invalid (), T.bottom (K.value Can_scan)
    end
  | Swap_byte_endianness Naked_int32 ->
    let arg, ty = S.simplify_simple env arg in
    let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
    let proof = (E.type_accessor env T.prove_naked_int32) ty in
    begin match proof with
    | Proved is ->
      let is = Int32.Set.map Int32.byte_swap is in
      begin match Int32.Set.get_singleton is with
      | Some i ->
        let simple = Simple.const (Naked_int32 i) in
        Reachable.reachable (Simple simple), T.this_naked_int32 i
      | None ->
        Reachable.reachable (original_term ()), T.these_naked_int32s is
      end
    | Proved Not_all_values_known ->
      Reachable.reachable (original_term ()), T.unknown Naked_int32 Other
    | Invalid -> 
      Reachable.invalid (), T.bottom Naked_int32
    end
  | Swap_byte_endianness Naked_int64 ->
    let arg, ty = S.simplify_simple env arg in
    let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
    let proof = (E.type_accessor env T.prove_naked_int64) ty in
    begin match proof with
    | Proved is ->
      let is = Int64.Set.map Int64.byte_swap is in
      begin match Int64.Set.get_singleton is with
      | Some i ->
        let simple = Simple.const (Naked_int64 i) in
        Reachable.reachable (Simple simple), T.this_naked_int64 i
      | None ->
        Reachable.reachable (original_term ()), T.these_naked_int64s is
      end
    | Proved Not_all_values_known ->
      Reachable.reachable (original_term ()), T.unknown Naked_int64 Other
    | Invalid -> 
      Reachable.invalid (), T.bottom Naked_int64
    end
  | Swap_byte_endianness Naked_nativeint ->
    let arg, ty = S.simplify_simple env arg in
    let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
    let proof = (E.type_accessor env T.prove_naked_nativeint) ty in
    begin match proof with
    | Proved is ->
      let is = Nativeint.Set.map Nativeint.byte_swap is in
      begin match Nativeint.Set.get_singleton is with
      | Some i ->
        let simple = Simple.const (Naked_nativeint i) in
        Reachable.reachable (Simple simple), T.this_naked_nativeint i
      | None ->
        Reachable.reachable (original_term ()), T.these_naked_nativeints is
      end
    | Proved Not_all_values_known ->
      Reachable.reachable (original_term ()), T.unknown Naked_nativeint Other
    | Invalid -> 
      Reachable.invalid (), T.bottom Naked_nativeint
    end
  | Int_as_pointer ->
    let arg, _ty = S.simplify_simple env arg in
    (* There is no check on the kind of [arg]: a fatal error resulting from
       such could potentially be triggered by wrong user code. *)
    (* CR mshinwell: think about this some more *)
    Prim (Unary (prim, arg), dbg), T.unknown K.naked_immediate Other
  | Opaque_identity ->
    let arg, ty = S.simplify_simple env arg in
    let kind = (E.type_accessor env T.kind) ty in
    Prim (Unary (prim, arg), dbg), T.unknown kind Other
  | Int_arith (kind, op) ->

  | Int_conv { src; dst; } ->

  | Float_arith op ->

  | Int_of_float ->
    (* CR mshinwell: We need to validate that the backend compiles
       the [Int_of_float] primitive in the same way as
       [Targetint.of_float].  Ditto for [Float_of_int].  (For the record,
       [Pervasives.int_of_float] and [Nativeint.of_float] on [nan] produce
       wildly different results). *)
    let arg, ty = S.simplify_simple env arg in
    let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
    let proof = (E.type_accessor env T.prove_naked_float) ty in
    begin match proof with
    | Proved fs ->
      begin match Float.Set.get_singleton fs with
      | Some f ->
        let i =
          (* It seems as if the various [float_of_int] functions never raise
             an exception even in the case of NaN or infinity. *)
          (* CR mshinwell: We should be sure this semantics is reasonable. *)
          Immediate.int (Targetint.of_float f)
        in
        let simple = Simple.const (Tagged_immediate i) in
        Reachable.reachable (Simple simple),
          T.this_tagged_immediate i
      | None ->
        let is =
          Float.Set.fold (fun f is ->
              let i = Immediate.int (Targetint.of_float f) in
              Immediate.Set.add i is)
            fs
            Immediate.Set.empty
        in
        Reachable.reachable (original_term ()),
          T.these_tagged_immediates is
      end
    | Proved Not_all_values_known ->
      Reachable.reachable (original_term ()),
        T.unknown (K.value Can_scan) Other
    | Invalid -> 
      Reachable.invalid (), T.bottom (K.value Can_scan)
    end
  | Float_of_int ->
    let arg, ty = S.simplify_simple env arg in
    let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
    let proof = (E.type_accessor env T.prove_tagged_immediate) ty in
    begin match proof with
    | Proved is ->
      begin match Immediate.Set.get_singleton is with
      | Some i ->
        let f = Targetint.to_float (Immediate.to_targetint i) in
        let simple = Simple.const (Naked_float f) in
        Reachable.reachable (Simple simple),
          T.this_naked_float f
      | None ->
        let fs =
          Float.Set.fold (fun i fs ->
              let f = Targetint.to_float (Immediate.to_targetint i) in
              Float.Set.add f fs)
            is
            Float.Set.empty
        in
        Reachable.reachable (original_term ()),
          T.these_naked_floats fs
      end
    | Proved Not_all_values_known ->
      Reachable.reachable (original_term ()),
        T.unknown (K.value Can_scan) Other
    | Invalid -> 
      Reachable.invalid (), T.bottom (K.value Can_scan)
    end
  | Array_length array_kind ->

  | Bigarray_length { dimension : int; } ->

  | Unbox_number Naked_float ->
    let arg, ty = S.simplify_simple env arg in
    let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
    let proof = (E.type_accessor env T.prove_boxed_float) ty in
    begin match proof with
    (* CR mshinwell: To factorize the code here for the various kinds, change
       the "proof" types in Flambda_type to use a single parameterised proof
       type *)
    | Proved fs ->
      begin match Float.Set.get_singleton fs with
      | Some f ->
        let simple = Simple.const (Naked_float f) in
        Reachable.reachable (Simple simple), T.this_naked_float f
      | None ->
        Reachable.reachable (original_term ()),
          T.these_naked_floats fs
      end
    | Proved Not_all_values_known ->
      Reachable.reachable (original_term ()),
        T.unknown Naked_float Other
    | Invalid -> 
      Reachable.invalid (), T.bottom Naked_float
    end
  | Unbox_number Naked_int32 ->
    let arg, ty = S.simplify_simple env arg in
    let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
    let proof = (E.type_accessor env T.prove_boxed_int32) ty in
    begin match proof with
    | Proved fs ->
      begin match Int32.Set.get_singleton fs with
      | Some f ->
        let simple = Simple.const (Naked_int32 f) in
        Reachable.reachable (Simple simple), T.this_naked_int32 f
      | None ->
        Reachable.reachable (original_term ()),
          T.these_naked_int32s fs
      end
    | Proved Not_all_values_known ->
      Reachable.reachable (original_term ()),
        T.unknown Naked_int32 Other
    | Invalid -> 
      Reachable.invalid (), T.bottom Naked_int32
    end
  | Unbox_number Naked_int64 ->
    let arg, ty = S.simplify_simple env arg in
    let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
    let proof = (E.type_accessor env T.prove_boxed_int64) ty in
    begin match proof with
    | Proved fs ->
      begin match Int64.Set.get_singleton fs with
      | Some f ->
        let simple = Simple.const (Naked_int64 f) in
        Reachable.reachable (Simple simple), T.this_naked_int64 f
      | None ->
        Reachable.reachable (original_term ()),
          T.these_naked_int64s fs
      end
    | Proved Not_all_values_known ->
      Reachable.reachable (original_term ()),
        T.unknown Naked_int64 Other
    | Invalid -> 
      Reachable.invalid (), T.bottom Naked_int64
    end
  | Unbox_number Naked_nativeint ->
    let arg, ty = S.simplify_simple env arg in
    let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
    let proof = (E.type_accessor env T.prove_boxed_nativeint) ty in
    begin match proof with
    | Proved fs ->
      begin match Targetint.Set.get_singleton fs with
      | Some f ->
        let simple = Simple.const (Naked_nativeint f) in
        Reachable.reachable (Simple simple), T.this_naked_nativeint f
      | None ->
        Reachable.reachable (original_term ()),
          T.these_naked_nativeints fs
      end
    | Proved Not_all_values_known ->
      Reachable.reachable (original_term ()),
        T.unknown Naked_nativeint Other
    | Invalid -> 
      Reachable.invalid (), T.bottom Naked_nativeint
    end
  | Box_number Naked_float ->

  | Project_closure of Closure_id.Set.t

  | Move_within_set_of_closures of Closure_id.t Closure_id.Map.t

  | Project_var of Var_within_closure.t Closure_id.Map.t

module Binary_int_arith (I : sig
  type t

  val kind : K.Standard_int.t
  val term : t -> Named.t

  val zero : t
  val one : t
  val minus_one : t

  val add : t -> t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t
  (* CR mshinwell: We should think very carefully to make sure this is right.
     Also see whether unsafe division can be exposed to the user.  The
     current assumption that division by zero reaching here is dead code. *)
  val div : t -> t -> t option
  val mod_ : t -> t -> t option
  val and_ : t -> t -> t
  val or_ : t -> t -> t
  val xor : t -> t -> t

  module Identifiable.S with type t := t

  module Pair : sig
    type nonrec t = t * t

    module Identifiable.S with type t := t
  end

  val cross_product : Set.t -> Set.t -> Pair.Set.t
end) = struct
  module Possible_result = struct
    type t =
      | Var of Variable.t
      | Prim of Flambda_primitive.t
      | Exactly of I.t

    include Identifiable.Make_no_hash (struct
      type nonrec t = t

      let compare t1 t2 =
        match t1, t2 with
        | Var var1, Var var2 -> Variable.compare var1 var2
        | Prim prim1, Prim prim2 -> Flambda_primitive.compare prim1 prim2
        | Exactly i1, Exactly i2 -> I.compare i1 i2
        | Var _, (Prim _ | Exactly _) -> -1
        | Prim _, Var _ -> 1
        | Prim _, Exactly _ -> -1
        | Exactly, (Var _ | Prim _) -> 1

      let print _ppf _t = Misc.fatal_error "Not yet implemented"
    end)
  end

  type outcome_for_one_side_only =
    | Exactly of I.t
    | This_primitive of Flambda_primitive.t
    | The_other_side
    | Cannot_simplify
    | Invalid

  type symmetric_op =
    | Add
    | Mul
    | And
    | Or
    | Xor

  let simplify env r prim dbg op arg1 arg2 : Named.t * R.t =
    let module P = Possible_result in
    let arg1, ty1 = S.simplify_simple env arg1 in
    let arg2, ty2 = S.simplify_simple env arg2 in
    let proof1 = (E.type_accessor env T.prove_tagged_immediate) arg1 in
    let proof2 = (E.type_accessor env T.prove_tagged_immediate) arg2 in
    let op =
      let always_some f x = Some (f x) in
      match op with
      | Add -> always_some I.add
      | Sub -> always_some I.sub
      | Mul -> always_some I.mul
      | Div -> I.div
      | Mod -> I.mod_
      | And -> always_some I.and_
      | Or -> always_some I.or_
      | Xor -> always_some I.xor
    in
    let symmetric_op_one_side_unknown (op : symmetric_op) ~this_side
          : outcome_for_one_side_only =
      let negate_lhs () : outcome_for_one_side_only =
        This_primitive (Unary (Int_arith Neg, arg1))
      in
      match op with
      | Add ->
        if I.equal rhs I.zero then The_other_side
        else Cannot_simplify
      | Mul ->
        if I.equal rhs I.zero then Exactly I.zero
        else if I.equal rhs I.one then The_other_side
        else if I.equal rhs I.minus_one then negate_lhs ()
        else Cannot_simplify
      | And ->
        if I.equal rhs I.minus_one then The_other_side
        else if I.equal rhs I.zero then Exactly I.zero
        else Cannot_simplify
      | Or ->
        if I.equal rhs I.minus_one then Exactly I.minus_one
        else if I.equal rhs I.zero then The_other_side
        else Cannot_simplify
      | Xor ->
        if I.equal lhs I.zero then The_other_side
        (* CR mshinwell: We don't have bitwise NOT
        else if I.equal lhs I.minus_one then bitwise NOT of rhs *)
        else Cannot_simplify
    in
    let op_lhs_unknown ~rhs : outcome_for_one_side_only =
      let negate_the_other_side () : outcome_for_one_side_only =
        This_primitive (Unary (Int_arith Neg, arg1))
      in
      match op with
      | Add -> symmetric_op_one_side_unknown Add ~this_side:rhs
      | And -> symmetric_op_one_side_unknown And ~this_side:rhs
      | Or -> symmetric_op_one_side_unknown Or ~this_side:rhs
      | Xor -> symmetric_op_one_side_unknown Xor ~this_side:rhs
      | Sub ->
        if I.equal rhs I.zero then The_other_side
        else Cannot_simplify
      | Mul ->
        if I.equal rhs I.zero then Exactly I.zero
        else if I.equal rhs I.one then The_other_side
        else if I.equal rhs I.minus_one then negate_the_other_side ()
        else Cannot_simplify
      | Div ->
        if I.equal rhs I.zero then Invalid
        else if I.equal rhs I.one then The_other_side
        else if I.equal rhs I.minus_one then negate_the_other_side ()
        else Cannot_simplify
      | Mod ->
        (* CR mshinwell: We could be more clever for Mod and And *)
        if I.equal rhs I.zero then Invalid
        else if I.equal rhs I.one then Exactly I.zero
        else if I.equal rhs I.minus_one then Exactly I.zero
        else Cannot_simplify
    in
    let op_rhs_unknown ~lhs : outcome_for_one_side_only =
      let negate_the_other_side () : outcome_for_one_side_only =
        This_primitive (Unary (Int_arith Neg, arg2))
      in
      match op with
      | Add -> symmetric_op_one_side_unknown Add ~this_side:lhs
      | And -> symmetric_op_one_side_unknown And ~this_side:lhs
      | Or -> symmetric_op_one_side_unknown Or ~this_side:lhs
      | Xor -> symmetric_op_one_side_unknown Xor ~this_side:lhs
      | Sub ->
        if I.equal lhs I.zero then negate_the_other_side ()
        else Cannot_simplify
      | Mul ->
        if I.equal lhs I.zero then Exactly I.zero
        else if I.equal lhs I.one then The_other_side
        else if I.equal lhs I.minus_one then negate_the_other_side ()
        else Cannot_simplify
      | Div | Mod -> Cannot_simplify
    in
    let only_one_side_known op ints ~other_side_var =
      let possible_results =
        I.Set.fold (fun i possible_results ->
            match possible_results with
            | None -> None
            | Some possible_results ->
              match op i with
              | Exactly result ->
                P.Set.add (Exactly result) possible_results
              | This_primitive prim ->
                P.Set.add (Prim prim) possible_results
              | The_other_side ->
                P.Set.add (Var other_side_var) possible_results
              | Cannot_simplify -> None
              | Invalid -> possible_results)
          ints
          Some (P.Set.empty)
      in
      begin match possible_results with
      | Some results -> check_possible_results ~possible_results
      | None -> result_unknown ()
      end
    in
    let original_term () : Named.t =
      Prim (Binary (prim, arg1, arg2), dbg)
    in
    let result_unknown () =
      Reachable.reachable (original_term ()),
        T.unknown (K.Standard_int.to_kind I.kind) Other
    in
    let result_invalid () =
      Reachable.invalid (),
        T.bottom (K.Standard_int.to_kind I.kind)
    in
    let check_possible_results ~possible_results =
      (* CR mshinwell: We may want to bound the size of the set. *)
      let named, ty =
        if P.Set.is_empty possible_results then
          result_invalid ()
        else
          let named =
            match P.Set.get_singleton possible_results with
            | Some (Exactly i) -> I.term i
            | Some (Prim prim) -> Named.Prim (prim, dbg)
            | Some (Var var) -> Named.Simple (Simple.var var)
            | None -> original_term ()
          in
          let ty = T.these_tagged_immediates possible_results in
          named, ty
      in
      Reachable.reachable named, ty
    in
    begin match proof1, proof2 with
    | Proved (Exactly ints1), Proved (Exactly ints2) ->
      let all_pairs = I.cross_product ints1 ints2 in
      let possible_results =
        I.Pair.Set.fold (fun (i1, i2) possible_results ->
            match op i1 i2 with
            | None -> possible_results
            | Some result -> P.Set.add (Exactly result) possible_results)
          all_pairs
          P.Set.empty
      in
      check_possible_results ~possible_results
    | Proved (Exactly ints1), Proved Not_all_values_known ->
      only_one_side_known (fun i -> op_rhs_unknown ~lhs:i) ints1
        ~other_side_var:arg2
    | Proved Not_all_values_known, Proved (Exactly ints2) ->
      only_one_side_known (fun i -> op_lhs_unknown ~rhs:i) ints2
        ~other_side_var:arg1
    | Proved Not_all_values_known, Proved Not_all_values_known ->
      result_unknown ()
    | Invalid, _ | _, Invalid ->
      result_invalid ()
end

module Binary_int_arith_tagged_immediate = Binary_int_arith (Targetint)
module Binary_int_arith_naked_int32 = Binary_int_arith (Int32)
module Binary_int_arith_naked_int64 = Binary_int_arith (Int64)
module Binary_int_arith_naked_nativeint = Binary_int_arith (Targetint)

let simplify_binary_primitive env r prim arg1 arg2 dbg =
  match prim with
  | Block_load_computed_index
  | Block_set of int * block_set_kind * init_or_assign

  | Int_arith (kind, op) ->
    begin match kind with
    | Tagged_immediate ->
      Binary_int_arith_tagged_immediate.simplify env r op arg1 arg2
    | Naked_int32 ->
      Binary_int_arith_naked_int32.simplify env r op arg1 arg2
    | Naked_int64 ->
      Binary_int_arith_naked_int64.simplify env r op arg1 arg2
    | Naked_nativeint ->
      Binary_int_arith_naked_nativeint.simplify env r op arg1 arg2
    end

  | Int_shift of K.Standard_int.t * int_shift_op
  | Int_comp of K.Standard_int.t * comparison
  | Int_comp_unsigned of comparison
  | Float_arith of binary_float_arith_op
  | Float_comp of comparison
  | Bit_test
  | Array_load of array_kind
  | String_load of string_accessor_width
  | Bigstring_load of bigstring_accessor_width

let simplify_ternary_primitive env r prim arg1 arg2 arg3 dbg =
  match prim with
  | Block_set_computed of K.scanning * init_or_assign
  | Bytes_set of string_accessor_width
  | Array_set of array_kind
  | Bigstring_set of bigstring_accessor_width

let simplify_variadic_primitive env r prim args dbg =
  match prim with
  | Make_block of Tag.Scannable.t * mutable_or_immutable * Flambda_arity.t
  | Make_array of array_kind * mutable_or_immutable
  | Bigarray_set of num_dimensions * bigarray_kind * bigarray_layout
  | Bigarray_load of num_dimensions * bigarray_kind * bigarray_layout

let simplify_primitive env r prim dbg =
  (* CR mshinwell: Need to deal with [r] for benefits *)
  match prim with
  | Unary (prim, arg) ->
    simplify_unary_primitive env r prim arg dbg
  | Binary (prim, arg1, arg2) ->
    simplify_binary_primitive env r prim arg1 arg2 dbg
  | Ternary (prim, arg1, arg2, arg3) ->
    simplify_ternary_primitive env r prim arg1 arg2 arg3 dbg
  | Variadic (prim, args) ->
    simplify_variadic_primitive env r prim args dbg

let simplify_set_of_closures original_env r
      (set_of_closures : Flambda.Set_of_closures.t)
      : Flambda.Set_of_closures.t * T.t * R.t =
  let function_decls =
    let module Backend = (val (E.backend original_env) : Backend_intf.S) in
    (* CR-soon mshinwell: Does this affect
       [reference_recursive_function_directly]?
       mshinwell: This should be thought about as part of the wider issue of
       references to functions via symbols or variables. *)
    Freshening.rewrite_recursive_calls_with_symbols (E.freshening original_env)
      set_of_closures.function_decls
      ~make_closure_symbol:Backend.closure_symbol
  in
  let env = E.increase_closure_depth original_env in
  let free_vars, function_decls, parameter_types,
      internal_value_set_of_closures, set_of_closures_env =
    Simplify_aux.prepare_to_simplify_set_of_closures ~env
      ~set_of_closures ~function_decls ~only_for_function_decl:None
      ~freshen:true
  in
  let continuation_param_uses = Continuation.Tbl.create 42 in
  let simplify_function fun_var (function_decl : Flambda.Function_declaration.t)
        (funs, used_params, r)
        : Flambda.Function_declaration.t Variable.Map.t * Variable.Set.t * R.t =
    let closure_env =
      Simplify_aux.prepare_to_simplify_closure ~function_decl
        ~free_vars ~parameter_types ~set_of_closures_env
    in
    let continuation_param, closure_env =
      let continuation_param, freshening =
        Freshening.add_static_exception (E.freshening closure_env)
          function_decl.continuation_param
      in
      let cont_type =
        Continuation_approx.create_unknown ~name:continuation_param
          ~num_params:function_decl.return_arity
      in
      let closure_env =
        E.add_continuation (E.set_freshening closure_env freshening)
          continuation_param cont_type
      in
      continuation_param, closure_env
    in
    let body, r =
      E.enter_closure closure_env ~closure_id:(Closure_id.wrap fun_var)
        ~inline_inside:
          (Inlining_decision.should_inline_inside_declaration function_decl)
        ~dbg:function_decl.dbg
        ~f:(fun body_env ->
          assert (E.inside_set_of_closures_declaration
            function_decls.set_of_closures_origin body_env);
          let body, r, uses =
            let descr =
              Format.asprintf "the body of %a" Variable.print fun_var
            in
            (E.simplify_toplevel body_env) body_env r function_decl.body
              ~continuation:continuation_param
              ~descr
          in
          Continuation.Tbl.add continuation_param_uses continuation_param uses;
          body, r)
    in
    let inline : Lambda.inline_attribute =
      match function_decl.inline with
      | Default_inline ->
        if !Clflags.classic_inlining && not function_decl.stub then
          (* In classic-inlining mode, the inlining decision is taken at
             definition site (here). If the function is small enough
             (below the -inline threshold) it will always be inlined. *)
          let inlining_threshold =
            Simplify_aux.initial_inlining_threshold
              ~round:(E.round env)
          in
          if Inlining_cost.can_inline body inlining_threshold ~bonus:0
          then
            Always_inline
          else
            Default_inline
        else
          Default_inline
      | inline ->
        inline
    in
    let function_decl =
      Flambda.Function_declaration.create ~params:function_decl.params
        ~continuation_param:continuation_param
        ~return_arity:function_decl.return_arity
        ~body ~stub:function_decl.stub ~dbg:function_decl.dbg
        ~inline ~specialise:function_decl.specialise
        ~is_a_functor:function_decl.is_a_functor
        ~closure_origin:function_decl.closure_origin
    in
    let function_decl =
      match Unrecursify.unrecursify_function ~fun_var ~function_decl with
      | None -> function_decl
      | Some function_decl -> function_decl
    in
    let used_params' = Flambda.used_params function_decl in
    Variable.Map.add fun_var function_decl funs,
      Variable.Set.union used_params used_params', r
  in
  let funs, _used_params, r =
    Variable.Map.fold simplify_function function_decls.funs
      (Variable.Map.empty, Variable.Set.empty, r)
  in
  let function_decls =
    Flambda.Function_declarations.update function_decls ~funs
  in
  let function_decls =
    (* CR mshinwell: I'm not sure about this "round" condition.  It seems
       though that doing [Unbox_returns] too early may be
       detrimental, as it prevents small functions being inlined *)
    if E.never_inline env
      || E.round env < 2
      || E.never_unbox_continuations env
    then
      function_decls, Variable.Map.empty
    else
      let continuation_param_uses =
        Continuation.Tbl.to_map continuation_param_uses
      in
      Unbox_returns.run ~continuation_uses:continuation_param_uses
        ~function_decls ~backend:(E.backend env)
  in
  let invariant_params =
    lazy (Invariant_params.Functions.invariant_params_in_recursion
      function_decls ~backend:(E.backend env))
  in
  let value_set_of_closures =
    T.create_set_of_closures ~function_decls
      ~bound_vars:internal_value_set_of_closures.bound_vars
      ~size:(lazy (Flambda.Function_declarations.size function_decls))
      ~invariant_params
      ~freshening:internal_value_set_of_closures.freshening
      ~direct_call_surrogates:
        internal_value_set_of_closures.direct_call_surrogates
  in
  let direct_call_surrogates =
    Closure_id.Map.fold (fun existing surrogate surrogates ->
        Variable.Map.add (Closure_id.unwrap existing)
          (Closure_id.unwrap surrogate) surrogates)
      internal_value_set_of_closures.direct_call_surrogates
      Variable.Map.empty
  in
  let set_of_closures =
    Flambda.Set_of_closures.create ~function_decls
      ~free_vars:(Variable.Map.map fst free_vars)
      ~direct_call_surrogates
  in
  let ty = T.set_of_closures value_set_of_closures in
  set_of_closures, ty, r

(*
let simplify_primitive0 (p : Lambda.primitive) (args, approxs) expr dbg
      ~size_int ~big_endian : Named.t * T.t * Inlining_cost.Benefit.t =
  let fpc = !Clflags.float_const_prop in
  match p with
  | Pmakeblock(tag_int, Flambda.Immutable, shape) ->
    let tag = Tag.create_exn tag_int in
    let shape = match shape with
      | None -> List.map (fun _ -> Lambda.Pgenval) args
      | Some shape -> shape
    in
    let approxs = List.map2 T.augment_with_kind approxs shape in
    let shape = List.map2 T.augment_kind_with_approx approxs shape in
    Prim (Pmakeblock(tag_int, Flambda.Immutable, Some shape), args, dbg),
    T.value_block tag (Array.of_list approxs), C.Benefit.zero
  | Pmakearray(_, _) when approxs = [] ->
    Prim (Pmakeblock(0, Flambda.Immutable, Some []), [], dbg),
    T.value_block (Tag.create_exn 0) [||], C.Benefit.zero
  | Pmakearray (Pfloatarray, Mutable) ->
      let approx =
        T.value_mutable_float_array ~size:(List.length args)
      in
      expr, approx, C.Benefit.zero
  | Pmakearray (Pfloatarray, Immutable) ->
      let approx =
        T.value_immutable_float_array (Array.of_list approxs)
      in
      expr, approx, C.Benefit.zero
  | Pintcomp Ceq when T.phys_equal approxs ->
    S.const_bool_expr expr true
  | Pintcomp Cneq when T.phys_equal approxs ->
    S.const_bool_expr expr false
    (* N.B. Having [not (phys_equal approxs)] would not on its own tell us
       anything about whether the two values concerned are unequal.  To judge
       that, it would be necessary to prove that the approximations are
       different, which would in turn entail them being completely known.

       It may seem that in the case where we have two approximations each
       annotated with a symbol that we should be able to judge inequality
       even if part of the approximation description(s) are unknown.  This is
       unfortunately not the case.  Here is an example:

         let a = f 1
         let b = f 1
         let c = a, a
         let d = a, a

       If [Share_constants] is run before [f] is completely inlined (assuming
       [f] always generates the same result; effects of [f] aren't in fact
       relevant) then [c] and [d] will not be shared.  However if [f] is
       inlined later, [a] and [b] could be shared and thus [c] and [d] could
       be too.  As such, any intermediate non-aliasing judgement would be
       invalid. *)
  | Pintcomp Ceq when T.phys_different approxs ->
    S.const_bool_expr expr false
  | Pintcomp Cneq when T.phys_different approxs ->
    S.const_bool_expr expr true
    (* If two values are structurally different we are certain they can never
       be shared*)
  | _ ->
    match T.descrs approxs with
    | [Union union] ->
      begin match T.Unionable.flatten union with
      | Ok (Int x) ->
        begin match p with
        | Pidentity -> S.const_int_expr expr x
        | Pnot -> S.const_bool_expr expr (x = 0)
      | Pnegint -> S.const_int_expr expr (-x)
      | Pbswap16 -> S.const_int_expr expr (S.swap16 x)
      | Poffsetint y -> S.const_int_expr expr (x + y)
      | Pfloatofint Boxed when fpc -> S.const_float_expr expr (float_of_int x)
      | Pbintofint Pnativeint ->
        S.const_boxed_int_expr expr Nativeint (Nativeint.of_int x)
      | Pbintofint Pint32 -> S.const_boxed_int_expr expr Int32 (Int32.of_int x)
        | Pbintofint Pint64 -> S.const_boxed_int_expr expr Int64 (Int64.of_int x)
        | _ -> expr, T.value_unknown Other, C.Benefit.zero
        end
      | Ok (Constptr x) ->
        begin match p with
        (* [Pidentity] should probably never appear, but is here for
          completeness. *)
        | Pidentity -> S.const_ptr_expr expr x
        | Pnot -> S.const_bool_expr expr (x = 0)
        | Poffsetint y -> S.const_ptr_expr expr (x + y)
        | _ -> expr, T.value_unknown Other, C.Benefit.zero
        end
      | _ -> expr, T.value_unknown Other, C.Benefit.zero
      end
    | [Union union1; Union union2] ->
      begin match T.Unionable.flatten union1, T.Unionable.flatten union2 with
      | Ok (Int x | Constptr x), Ok (Int y | Constptr y) ->
        let shift_precond = 0 <= y && y < 8 * size_int in
        begin match p with
        | Plslint when shift_precond -> S.const_int_expr expr (x lsl y)
        | Plsrint when shift_precond -> S.const_int_expr expr (x lsr y)
        | Pasrint when shift_precond -> S.const_int_expr expr (x asr y)
        | Pintcomp cmp -> S.const_comparison_expr expr cmp x y
        | Pisout -> S.const_bool_expr expr (y > x || y < 0)
        | _ -> expr, T.value_unknown Other, C.Benefit.zero
        end
      | Ok (Char x), Ok (Char y) ->
        begin match p with
        | Pintcomp cmp -> S.const_comparison_expr expr cmp x y
        | _ -> expr, T.value_unknown Other, C.Benefit.zero
        end
      | _, _ -> expr, T.value_unknown Other, C.Benefit.zero
      end
    | [Boxed_float (Some x)] when fpc ->
      begin match p with
      | Pintoffloat Boxed -> S.const_int_expr expr (int_of_float x)
      | Pnegfloat Boxed -> S.const_float_expr expr (-. x)
      | Pabsfloat Boxed -> S.const_float_expr expr (abs_float x)
      | _ -> expr, T.value_unknown Other, C.Benefit.zero
      end
    | [Boxed_float (Some n1); Boxed_float (Some n2)] when fpc ->
      begin match p with
      | Paddfloat Boxed -> S.const_float_expr expr (n1 +. n2)
      | Psubfloat Boxed -> S.const_float_expr expr (n1 -. n2)
      | Pmulfloat Boxed -> S.const_float_expr expr (n1 *. n2)
      | Pdivfloat Boxed -> S.const_float_expr expr (n1 /. n2)
      | Pfloatcomp (c, Boxed)  -> S.const_comparison_expr expr c n1 n2
      | _ -> expr, T.value_unknown Other, C.Benefit.zero
      end
    | [T.Boxed_int(T.Nativeint, n)] ->
      I.Simplify_boxed_nativeint.simplify_unop p Nativeint expr n
    | [T.Boxed_int(T.Int32, n)] ->
      I.Simplify_boxed_int32.simplify_unop p Int32 expr n
    | [T.Boxed_int(T.Int64, n)] ->
      I.Simplify_boxed_int64.simplify_unop p Int64 expr n
    | [T.Boxed_int(T.Nativeint, n1);
       T.Boxed_int(T.Nativeint, n2)] ->
      I.Simplify_boxed_nativeint.simplify_binop p Nativeint expr n1 n2
    | [T.Boxed_int(T.Int32, n1); T.Boxed_int(T.Int32, n2)] ->
      I.Simplify_boxed_int32.simplify_binop p Int32 expr n1 n2
    | [T.Boxed_int(T.Int64, n1); T.Boxed_int(T.Int64, n2)] ->
      I.Simplify_boxed_int64.simplify_binop p Int64 expr n1 n2
    | [T.Boxed_int(T.Nativeint, n1); Union union2] ->
      begin match T.Unionable.flatten union2 with
      | Ok (Int n2) ->
        I.Simplify_boxed_nativeint.simplify_binop_int p Nativeint expr n1 n2
          ~size_int
      | _ -> expr, T.value_unknown Other, C.Benefit.zero
      end
    | [T.Boxed_int(T.Int32, n1); Union union2] ->
      begin match T.Unionable.flatten union2 with
      | Ok (Int n2) ->
        I.Simplify_boxed_int32.simplify_binop_int p Int32 expr n1 n2
          ~size_int
      | _ -> expr, T.value_unknown Other, C.Benefit.zero
      end
    | [T.Boxed_int(T.Int64, n1); Union union2] ->
      begin match T.Unionable.flatten union2 with
      | Ok (Int n2) ->
        I.Simplify_boxed_int64.simplify_binop_int p Int64 expr n1 n2
          ~size_int
      | _ -> expr, T.value_unknown Other, C.Benefit.zero
      end
    | [String { size }]
      when (p = Lambda.Pstringlength || p = Lambda.Pbyteslength) ->
      S.const_int_expr expr size
    | [String { size; contents = Some s }; Union union2] ->
      begin match T.Unionable.flatten union2 with
      | Ok (Int x) | Ok (Constptr x) when x >= 0 && x < size ->
        begin match p with
        | Pstringrefu
        | Pstringrefs
        | Pbytesrefu
        | Pbytesrefs ->
          S.const_char_expr (Prim(Pstringrefu, args, dbg)) s.[x]
        | _ -> expr, T.value_unknown Other, C.Benefit.zero
        end
      | _ -> expr, T.value_unknown Other, C.Benefit.zero
      end
    | [String { size; contents = None }; Union union2] ->
      begin match T.Unionable.flatten union2 with
      | Ok (Int x) | Ok (Constptr x)
          when x >= 0 && x < size && p = Lambda.Pstringrefs ->
        Flambda.Prim (Pstringrefu, args, dbg),
          T.value_unknown Other,
          (* we improved it, but there is no way to account for that: *)
          C.Benefit.zero
      | Ok (Int x) | Ok (Constptr x)
          when x >= 0 && x < size && p = Lambda.Pbytesrefs ->
        Flambda.Prim (Pbytesrefu, args, dbg),
          T.value_unknown Other,
          (* we improved it, but there is no way to account for that: *)
          C.Benefit.zero
      | _ -> expr, T.value_unknown Other, C.Benefit.zero
      end
    | [Float_array { size; contents }] ->
        begin match p with
        | Parraylength _ -> S.const_int_expr expr size
        | Pfloatfield i ->
          begin match contents with
          | T.Contents a when i >= 0 && i < size ->
            begin match T.check_approx_for_float a.(i) with
            | None -> expr, a.(i), C.Benefit.zero
            | Some v -> S.const_float_expr expr v
            end
          | Contents _ | Unknown_or_mutable ->
            expr, T.value_unknown Other, C.Benefit.zero
          end
        | _ -> expr, T.value_unknown Other, C.Benefit.zero
        end
    | _ ->
      match Semantics_of_primitives.return_type_of_primitive p with
      | Boxed_float ->
        expr, T.value_any_float, C.Benefit.zero
      | Unboxed_float ->
        expr, T.any_unboxed_float, C.Benefit.zero
      | Unboxed_int32 ->
        expr, T.any_unboxed_int32, C.Benefit.zero
      | Unboxed_int64 ->
        expr, T.any_unboxed_int64, C.Benefit.zero
      | Unboxed_nativeint ->
        expr, T.any_unboxed_nativeint, C.Benefit.zero
      | Other ->
        expr, T.value_unknown Other, C.Benefit.zero

let simplify_primitive env r prim args dbg : named_simplifier =
  let dbg = E.add_inlined_debuginfo env ~dbg in
  let args, args_tys = freshen_and_squash_aliases_list env args in
  let tree = Flambda.Prim (prim, args, dbg) in
  let projection : Projection.t = Prim (prim, args) in
  begin match E.find_projection env ~projection with
  | Some var ->
    (* CSE of pure primitives.
       The [Pisint] case in particular is also used when unboxing
       continuation parameters of variant type. *)
    let var, var_ty = freshen_and_squash_aliases env var in
    let r = R.map_benefit r (B.remove_projection projection) in
    [], Reachable (Var var), var_ty
  | None ->
    let default () : (Variable.t * Named.t) list
          * Named.t_reachable * R.t =
      let named, ty, benefit =
        (* CR mshinwell: if the primitive is pure, add it to the environment
           so CSE will work.  Need to be careful if the variable being
           bound is a continuation argument *)
        let module Backend = (val (E.backend env) : Backend_intf.S) in
        simplify_primitive0 prim (args, args_tys) tree dbg
          ~size_int:Backend.size_int ~big_endian:Backend.big_endian
      in
      let r = R.map_benefit r (B.(+) benefit) in
      let ty =
        match prim with
        | Popaque -> T.unknown Other
        | _ -> ty
      in
      [], Reachable (named, value_kind), ty
    in
    begin match prim, args, args_tys with
    | Pfield field_index, [arg], [arg_ty] ->
      let projection : Projection.t = Prim (Pfield field_index, [arg]) in
      begin match E.find_projection env ~projection with
      | Some var ->
        let var, var_ty = freshen_and_squash_aliases env var in
        let r = R.map_benefit r (B.remove_projection projection) in
        [], Reachable (Var var), var_ty
      | None ->
        begin match T.get_field arg_ty ~field_index with
        | Invalid _ ->
          [], Reachable.invalid (), r
        | Ok ty ->
          let tree, ty =
            match arg_ty.symbol with
            (* If the [Pfield] is projecting directly from a symbol, rewrite
                the expression to [Read_symbol_field]. *)
            | Some (symbol, None) ->
              let ty =
                T.augment_with_symbol_field ty symbol field_index
              in
              Flambda.Read_symbol_field (symbol, field_index), ty
            | None | Some (_, Some _ ) ->
              (* This [Pfield] is either not projecting from a symbol at
                 all, or it is the projection of a projection from a
                 symbol. *)
              let ty' = E.really_import_ty env ty in
              tree, ty'
          in
          simpler_equivalent_term env r tree ty
        end
      end
    | Pfield _, _, _ -> Misc.fatal_error "Pfield arity error"
    | (Parraysetu kind | Parraysets kind),
        [_block; _field; _value],
        [block_ty; field_ty; value_ty] ->
      if T.invalid_to_mutate block_ty then begin
        [], Reachable.invalid (), r
      end else begin
        let size = T.length_of_array block_ty in
        let index = T.reify_as_int field_ty in
        let bounds_check_definitely_fails =
          match size, index with
          | Some size, _ when size <= 0 ->
            assert (size = 0);  (* see [Simple_value_ty] *)
            true
          | Some size, Some index ->
            (* This is ok even in the presence of [Obj.truncate], since that
               can only make blocks smaller. *)
            index >= 0 && index < size
          | _, _ -> false
        in
        let convert_to_raise =
          match prim with
          | Parraysets _ -> bounds_check_definitely_fails
          | Parraysetu _ -> false
          | _ -> assert false  (* see above *)
        in
        if convert_to_raise then begin
          (* CR mshinwell: move to separate function *)
          let invalid_argument_var = Variable.create "invalid_argument" in
          let invalid_argument : Named.t =
            let module Backend = (val (E.backend env) : Backend_intf.S) in
            Symbol (Backend.symbol_for_global'
              Predef.ident_invalid_argument)
          in
          let msg_var = Variable.create "msg" in
          let msg : Named.t =
            Allocated_const (String "index out of bounds")
          in
          let exn_var = Variable.create "exn" in
          let exn : Named.t =
            Prim (Pmakeblock (0, Immutable, None),
              [invalid_argument_var; msg_var], dbg)
          in
          let bindings = [
              invalid_argument_var, invalid_argument;
              msg_var, msg;
              exn_var, exn;
            ]
          in
          bindings, Reachable (Prim (Praise Raise_regular, [exn_var], dbg)),
            T.bottom
        end else begin
          let kind =
            match T.is_float_array block_ty, T.is_boxed_float value_ty with
            | (true, _)
            | (_, true) ->
              begin match kind with
              | Pfloatarray | Pgenarray -> ()
              | Paddrarray | Pintarray ->
                (* CR pchambart: Do a proper warning here *)
                Misc.fatal_errorf "Assignment of a float to a specialised \
                                  non-float array: %a"
                  Named.print tree
              end;
              Lambda.Pfloatarray
              (* CR pchambart: This should be accounted by the benefit *)
            | _ ->
              kind
          in
          let prim : Lambda.primitive =
            match prim with
            | Parraysetu _ -> Parraysetu kind
            | Parraysets _ -> Parraysets kind
            | _ -> assert false
          in
          [], Reachable (Prim (prim, args, dbg)), ret r (T.unknown Other)
        end
      end
    | Psetfield _, _block::_, block_ty::_ ->
      if T.invalid_to_mutate block_ty then begin
        [], Reachable.invalid (), r
      end else begin
        [], Reachable tree, ret r (T.unknown Other)
      end
    | Parraylength _, [_arg], [arg_ty] ->
      begin match T.length_of_array arg_ty with
      | None -> default ()
      | Some length ->
        let r = R.map_benefit r B.remove_prim in
        let const_length = Variable.create "length" in
        [const_length, Const (Int length)], Reachable (Var const_length),
          ret r (T.int length)
      end
    end
  end
*)

(** [simplify_named] returns:
    - extra [Let]-bindings to be inserted prior to the one being simplified;
    - the simplified [named];
    - the new result structure. *)
let simplify_named env r (tree : Named.t) : named_simplifier =
  match tree with
  | Var var ->
    let var, var_ty = freshen_and_squash_aliases env var in
    var, var_ty, r
  | Symbol sym ->
    let symbol_ty = E.find_symbol env sym in
    Reachable tree, symbol_ty, r
  | Const cst -> [], Reachable tree, type_for_const cst, r
  | Read_mutable mut_var ->
    (* See comment on the [Assign] case. *)
    let mut_var =
      Freshening.apply_mutable_variable (E.freshening env) mut_var
    in
    [], Reachable (Read_mutable mut_var), T.unknown Value Other
  | Set_of_closures set_of_closures ->
(*
    let backend = E.backend env in
    let cont_usage_snapshot = R.snapshot_continuation_uses r in
*)
    let set_of_closures, r =
      simplify_set_of_closures env r set_of_closures
    in
    [], Reachable (Set_of_closures set_of_closures), r
(* XXX Disabled just for the moment -- mshinwell
    let simplify env r ~bindings ~set_of_closures ~pass_name =
      (* If simplifying a set of closures more than once during any given round
         of simplification, the [Freshening.Project_var] substitutions arising
         from each call to [simplify_set_of_closures] must be composed.
         Note that this function only composes with [first_freshening] owing
         to the structure of the code below (this new [simplify] is always
         in tail position).
         We also need to be careful not to double-count (or worse) uses of
         continuations. *)
      let r = R.roll_back_continuation_uses r cont_usage_snapshot in
      let bindings, set_of_closures, r =
        let env = E.set_never_inline env in
        simplify_newly_introduced_let_bindings env r ~bindings
          ~around:((Set_of_closures set_of_closures) : Named.t)
      in
      let ty = R.inferred_type r in
      let value_set_of_closures =
        match T.strict_check_type_for_set_of_closures ty with
        | Wrong ->
          Misc.fatal_errorf "Unexpected Flambda type returned from \
              simplification of [%s] result: %a"
            pass_name T.print ty
        | Ok (_var, value_set_of_closures) ->
          let freshening =
            Freshening.Project_var.compose ~earlier:first_freshening
              ~later:value_set_of_closures.freshening
          in
          T.update_freshening_of_value_set_of_closures value_set_of_closures
            ~freshening
      in
      bindings, set_of_closures,
        (ret r (T.set_of_closures value_set_of_closures))
    in
    (* This does the actual substitutions of specialised args introduced
       by [Unbox_closures] for free variables.  (Apart from simplifying
       the [Unbox_closures] output, this also prevents applying
       [Unbox_closures] over and over.) *)
    let set_of_closures =
      match Remove_free_vars_equal_to_args.run set_of_closures with
      | None -> set_of_closures
      | Some set_of_closures -> set_of_closures
    in
    (* Do [Unbox_closures] next to try to decide which things are
       free variables and which things are specialised arguments before
       unboxing them. *)
    match
      Unbox_closures.rewrite_set_of_closures ~env
        ~duplicate_function ~set_of_closures
    with
    | Some (bindings, set_of_closures, benefit) ->
      let r = R.add_benefit r benefit in
      simplify env r ~bindings ~set_of_closures ~pass_name:"Unbox_closures"
    | None ->
      match Unbox_free_vars_of_closures.run ~env ~set_of_closures with
      | Some (bindings, set_of_closures, benefit) ->
        let r = R.add_benefit r benefit in
        simplify env r ~bindings ~set_of_closures
          ~pass_name:"Unbox_free_vars_of_closures"
      | None ->
        (* CR-soon mshinwell: should maybe add one allocation for the
           stub *)
        match
          Unbox_specialised_args.rewrite_set_of_closures ~env
            ~duplicate_function ~set_of_closures
        with
        | Some (bindings, set_of_closures, benefit) ->
          let r = R.add_benefit r benefit in
          simplify env r ~bindings ~set_of_closures
            ~pass_name:"Unbox_specialised_args"
        | None ->
          match
            Remove_unused_arguments.
                separate_unused_arguments_in_set_of_closures
              set_of_closures ~backend
          with
          | Some set_of_closures ->
            simplify env r ~bindings:[] ~set_of_closures
              ~pass_name:"Remove_unused_arguments"
          | None -> [], Reachable (Set_of_closures set_of_closures), r
    end *)
  | Prim (prim, dbg) -> simplify_primitive env r prim dbg
  | Assign { being_assigned; new_value; } ->
    (* No need to use something like [freshen_and_squash_aliases]: the
       Flambda type of [being_assigned] is always unknown. *)
    let being_assigned =
      Freshening.apply_mutable_variable (E.freshening env) being_assigned
    in
    freshen_and_squash_aliases_named env new_value ~f:(fun _env new_value _type ->
      [], Reachable (Assign { being_assigned; new_value; }),
        ret r (T.unknown Value Other))
