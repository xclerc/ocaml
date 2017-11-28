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

module Int = Numbers.Int
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
*)

let simplify_block_load env r prim arg dbg ~field_index ~field_kind
      ~field_is_mutable =
  let arg, ty = S.simplify_simple env arg in
  let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
  let kind = Flambda_primitive.kind_of_field_kind field_kind in
  let get_field_result =
    (E.type_accessor env T.get_field) ty
      ~field_index ~field_is_mutable ~field_kind
  in
  let term, ty =
    match get_field_result with
    | Ok field_ty ->
      assert ((not field_is_mutable) || T.is_unknown field_ty);
      let reified =
        (E.type_accessor env T.reify) ~allow_free_variables:true field_ty
      in
      begin match reified with
      | Term (simple, ty) -> Named.Simple simple, ty
      | Cannot_reify -> original_term (), field_ty
      | Invalid -> Reachable.invalid (), T.bottom kind
      end
    | Invalid -> Reachable.invalid (), T.bottom kind
  in
  term, ty, r

let simplify_duplicate_scannable_block env r prim arg dbg ~kind
      ~source_mutability ~destination_mutability =
  let arg, ty = S.simplify_simple env arg in
  let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
  let like_a_block tag (scanning : Flambda_kind.scanning) =
    let proof =
      (E.type_accessor env T.prove_block_with_unique_tag_and_size) ty
    in
    match proof with
    | Proved (Ok (tag, fields)) ->
      begin match source_mutability with
      | Immutable -> ()
      | Mutable ->
        Array.iteri (fun field_index field_ty ->
            (* CR-someday mshinwell: This will have to be adjusted if we
               start remembering things about immutable fields in records
               which also have mutable fields. *)
            if not ((E.type_accessor env T.is_unknown) t) then begin
              Misc.fatal_errorf "Field %d of type %a in block being \
                  duplicated with the following type is apparently mutable, \
                  yet its type is not unknown: %a"
                field_index
                print field_ty
                print ty
            end)
          fields
      end;
      (* We could in some circumstances turn the [Duplicate_array] into
         [Make_array], but it isn't clear what value this has, so we don't
         yet do it. *)
      let type_of_new_block =
        match destination_mutability with
        | Immutable -> T.block tag fields
        | Mutable -> T.block tag (T.unknown_like_array fields)
      in
      Reachable.reachable (original_term ()), type_of_new_block
    | Proved Not_all_values_known ->
      let term = Reachable.reachable (original_term ()) in
      (* Here and below: when the type [ty] of the source array evaluates to
         "unknown", we use [ty] as the type of the destination array, so long
         as the latter is immutable.  This means that if [ty] contains some
         complicated union, which may be later simplified by a meet, then
         we don't lose that information. *)
      begin match destination_mutability with
      | Immutable -> term, ty
      | Mutable -> term, T.unknown (K.value scanning) Other
      end
    | Invalid ->
      Reachable.invalid (), T.bottom (K.value scanning)
  in
  let term, ty =
    match kind with
    | Dynamic_must_scan_or_naked_float ->
      (* XXX Shouldn't this prove that the value is either a
         Blocks-and-immediates or a float array? *)
      let term = Reachable.reachable (original_term ()) in
      begin match destination_mutability with
      | Immutable -> term, ty
      | Mutable -> term, T.unknown (K.value Must_scan) Other
      end
    | Must_scan -> like_a_block Must_scan
    | Can_scan -> like_a_block Can_scan
    | Naked_float ->
      let proof = (E.type_accessor env T.prove_float_array) ty in
      match proof with
      | Proved (Exactly sizes) ->
        assert (not (Int.Set.is_empty sizes));
        let type_of_new_block =
          match destination_mutability with
          | Immutable ->
            let possible_types =
              List.map (fun size ->
                  let fields =
                    Array.init size (fun _index ->
                      unknown (K.naked_float ()) Other)
                  in
                  T.immutable_float_array fields)
                (Numbers.Int.Set.to_list sizes)
            in
            (E.type_accessor env T.join_list) (K.value Must_scan)
              possible_types
          | Mutable -> T.mutable_float_arrays_of_various_sizes ~sizes
        in
        Reachable.reachable (original_term ()), type_of_new_block
      | Proved Not_all_values_known ->
        let term = Reachable.reachable (original_term ()) in
        begin match destination_mutability with
        | Immutable -> term, ty
        | Mutable -> term, T.unknown (K.value Must_scan) Other
        end
      | Invalid ->
        Reachable.invalid (), T.bottom (K.value Must_scan)
  in
  term, ty, r

let simplify_is_int env r prim arg dbg =
  let arg, ty = S.simplify_simple env arg in
  let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
  let proof = (E.type_accessor env T.prove_is_tagged_immediate) ty in
  let term, ty =
    match proof with
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
  in
  term, ty, r

let simplify_get_tag env r prim arg dbg =
  let arg, ty = S.simplify_simple env arg in
  let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
  let eval, _canonical_name = (E.type_accessor env T.Evaluated.create) ty in
  let tags = T.Evaluated.tags eval in
  let term, ty =
    match tags with
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
          assert (not (Targetint.Set.is_empty tags));
          original_term (), T.these_tagged_immediates tags
        end
  in
  term, ty, r

module type For_standard_ints = sig
  module Num : sig
    include Identifiable.S

    val swap_byte_endianness : t -> t

    val to_const : t -> Simple.Const.t

    (* Care: [to_tagged_immediate] has to perform some arithmetic to ensure
       that the [Targetint.t] inside the [Immediate.t] represents the result
       as it would be if the conversion were evaluated on the target machine
       at type "int". *)
    (* CR mshinwell: Should there be a new module, [OCaml_int_on_target]?
       Then [Immediate.t] can use that. *)
    val to_tagged_immediate : t -> Immediate.t
    val to_naked_int32 : t -> Int32.t
    val to_naked_int64 : t -> Int64.t
    val to_naked_nativeint : t -> Targetint.t
  end

  val kind : K.Standard_int.t
  val prover : (T.t -> Num.Set.t proof) T.type_accessor
  val this : Num.t -> T.t
  val these : Num.Set.t -> T.t
end

module Make_simplify_swap_byte_endianness (P : For_standard_ints) = struct
  let simplify env r prim arg dbg =
    let arg, ty = S.simplify_simple env arg in
    let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
    let proof = (E.type_accessor env P.prover) ty in
    let kind = K.Standard_int.to_kind P.kind in
    let term, ty =
      match proof with
      | Proved nums ->
        let nums =
          P.Set.map (fun imm -> P.swap_byte_endianness imm) nums
        in
        begin match P.Num.Set.get_singleton nums with
        | Some i ->
          let simple = Simple.const (P.Num.to_const i) in
          Reachable.reachable (Simple simple), P.this i
        | None ->
          assert (not (P.Num.Set.is_empty nums));
          Reachable.reachable (original_term ()), P.these nums
        end
      | Proved Not_all_values_known ->
        Reachable.reachable (original_term ()), T.unknown kind Other
      | Invalid ->
        Reachable.invalid (), T.bottom kind
    in
    term, ty, r
end

module For_standard_ints_tagged_immediate : For_standard_ints = struct
  module Num = struct
    include Immediate

    let swap_byte_endianness t =
      Immediate.map (fun i ->
          Targetint.get_least_significant_16_bits_then_byte_swap i)
        t

    let to_const t = Simple.Const.Tagged_immediate t

    let to_tagged_immediate t = t
    let to_naked_int32 t = Targetint.to_int32 (Immediate.to_targetint t)
    let to_naked_int64 t = Targetint.to_int64 (Immediate.to_targetint t)
    let to_naked_nativeint t = Immediate.to_targetint t
  end

  let kind : K.Standard_int.t = Tagged_immediate
  let prover = T.prove_tagged_immediate
  let this = T.this_tagged_immediate
  let these = T.these_tagged_immediates
end

module For_standard_ints_naked_int32 : For_standard_ints = struct
  module Num = struct
    include Int32

    let to_const t = Simple.Const.Naked_int32 t

    let to_tagged_immediate t =
      Immediate.int (Targetint.treat_as_int (Targetint.of_int32 t))
    let to_naked_int32 t = t
    let to_naked_int64 t = Int64.of_int32 t
    let to_naked_nativeint t = Targetint.of_int64 t
  end

  let kind : K.Standard_int.t = Naked_int32
  let prover = T.prove_naked_int32
  let this = T.this_naked_int32
  let these = T.these_naked_int32s
end

module For_standard_ints_naked_int64 : For_standard_ints = struct
  module Num = struct
    include Int64

    let to_const t = Simple.Const.Naked_int64 t

    let to_tagged_immediate t =
      Immediate.int (Targetint.treat_as_int (Targetint.of_int64 t))
    let to_naked_int32 t = Int64.to_int32 t
    let to_naked_int64 t = t
    let to_naked_nativeint t = Targetint.of_int64 t
  end

  let kind : K.Standard_int.t = Naked_int64
  let prover = T.prove_naked_int64
  let this = T.this_naked_int64
  let these = T.these_naked_int64s
end

module For_standard_ints_naked_nativeint : For_standard_ints = struct
  module Num = struct
    include Targetint

    let to_const t = Simple.Const.Naked_nativeint t

    let to_tagged_immediate t = Immediate.int (Targetint.treat_as_int t)
    let to_naked_int32 t = Targetint.to_int32
    let to_naked_int64 t = Targetint.to_int64
    let to_naked_nativeint t = t
  end

  let kind : K.Standard_int.t = Naked_nativeint
  let prover = T.prove_naked_nativeint
  let this = T.this_naked_nativeint
  let these = T.these_naked_nativeints
end

module Simplify_swap_byte_endianness_tagged_immediate =
  Make_simplify_swap_byte_endianness (For_standard_ints_tagged_immediate)

module Simplify_swap_byte_endianness_naked_int32 =
  Make_simplify_swap_byte_endianness (For_standard_ints_naked_int32)

module Simplify_swap_byte_endianness_naked_int64 =
  Make_simplify_swap_byte_endianness (For_standard_ints_naked_int64)

module Simplify_swap_byte_endianness_naked_nativeint =
  Make_simplify_swap_byte_endianness (For_standard_ints_naked_nativeint)

let simplify_int_of_float env r prim arg dbg =
  (* CR mshinwell: We need to validate that the backend compiles
     the [Int_of_float] primitive in the same way as
     [Targetint.of_float].  Ditto for [Float_of_int].  (For the record,
     [Pervasives.int_of_float] and [Nativeint.of_float] on [nan] produce
     wildly different results). *)
  let module F = Numbers.Float_by_bit_pattern in
  let arg, ty = S.simplify_simple env arg in
  let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
  let proof = (E.type_accessor env T.prove_naked_float) ty in
  let term, ty =
    match proof with
    | Proved fs ->
      begin match F.Set.get_singleton fs with
      | Some f ->
        let i =
          (* It seems as if the various [float_of_int] functions never raise
             an exception even in the case of NaN or infinity. *)
          (* CR mshinwell: We should be sure this semantics is reasonable. *)
          Immediate.int (Targetint.of_float (F.to_float f))
        in
        let simple = Simple.const (Tagged_immediate i) in
        Reachable.reachable (Simple simple),
          T.this_tagged_immediate i
      | None ->
        assert (not (F.Set.is_empty fs));
        let is =
          F.Set.fold (fun f is ->
              let i = Immediate.int (Targetint.of_float (F.to_float f)) in
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
  in
  term, ty, r

let simplify_float_of_int env r prim arg dbg =
  let module F = Numbers.Float_by_bit_pattern in
  let arg, ty = S.simplify_simple env arg in
  let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
  let proof = (E.type_accessor env T.prove_tagged_immediate) ty in
  let term, ty =
    match proof with
    | Proved is ->
      begin match Immediate.Set.get_singleton is with
      | Some i ->
        let f = Targetint.to_float (Immediate.to_targetint i) in
        let simple = Simple.const (Naked_float f) in
        Reachable.reachable (Simple simple),
          T.this_naked_float f
      | None ->
        assert (not (Immediate.Set.is_empty fs));
        let fs =
          F.Set.fold (fun i fs ->
              let f = Targetint.to_float (Immediate.to_targetint i) in
              F.Set.add (F.create f) fs)
            is
            F.Set.empty
        in
        Reachable.reachable (original_term ()),
          T.these_naked_floats fs
      end
    | Proved Not_all_values_known ->
      Reachable.reachable (original_term ()),
        T.unknown (K.value Can_scan) Other
    | Invalid -> 
      Reachable.invalid (), T.bottom (K.value Can_scan)
  in
  term, ty, r

module type For_unboxable_ints = sig
  module Num : sig
    include Identifiable.S

    val swap_byte_endianness : t -> t
    val to_const : t -> Simple.Const.t
  end

  val kind : K.Boxable_number.t
  val prover : (T.t -> Num.Set.t proof) T.type_accessor

  val this : Num.t -> T.t
  val these : Num.Set.t -> T.t
  val box : T.t -> T.t
end

module Make_simplify_unbox_number (P : For_unboxable_ints) = struct
  let simplify env r prim arg dbg =
    let arg, ty = S.simplify_simple env arg in
    let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
    let proof = (E.type_accessor env P.boxed_prover) ty in
    let kind = K.Boxable_number.to_kind P.kind in
    let term, ty =
      match proof with
      | Proved unboxed_ty ->
        let proof = (E.type_accessor env P.unboxed_prover) unboxed_ty in
        begin match proof with
        | Proved nums ->
          begin match P.Num.Set.get_singleton nums with
          | Some n ->
            let simple = Simple.const (P.Num.to_const n) in
            Reachable.reachable (Simple simple), P.this n
          | None ->
            assert (not (P.Num.Set.is_empty nums));
            Reachable.reachable (original_term ()), P.these nums
          end
        | Proved Not_all_values_known ->
          Reachable.reachable (original_term ()), unboxed_ty
        | Invalid ->
          Reachable.invalid (), T.bottom kind
        end
      | Invalid -> 
        Reachable.invalid (), T.bottom kind
    in
    term, ty, r
end

module Simplify_unbox_number_float =
  Make_simplify_unbox_number (struct
    module Num = struct
      include Float
      let to_const t = Simple.Const.Naked_float t
    end

    let kind : K.Boxable_number.t = Naked_float
    let boxed_prover = T.prove_boxed_float
    let unboxed_prover = T.prove_naked_float
    let this = T.this_naked_float
    let these = T.these_naked_floats
  end)

module Simplify_unbox_number_int32 =
  Make_simplify_unbox_number (struct
    module Num = struct
      include Int32
      let to_const t = Simple.Const.Naked_int32 t
    end

    let kind : K.Boxable_number.t = Naked_int32
    let boxed_prover = T.prove_boxed_int32
    let unboxed_prover = T.prove_naked_int32
    let this = T.this_naked_int32
    let these = T.these_naked_int32s
  end)

module Simplify_unbox_number_int64 =
  Make_simplify_unbox_number (struct
    module Num = struct
      include Int64
      let to_const t = Simple.Const.Naked_int64 t
    end

    let kind : K.Boxable_number.t = Naked_int64
    let boxed_prover = T.prove_boxed_int64
    let unboxed_prover = T.prove_naked_int64
    let this = T.this_naked_int64
    let these = T.these_naked_int64s
  end)

module Simplify_unbox_number_nativeint =
  Make_simplify_unbox_number (struct
    module Num = struct
      include Nativeint
      let to_const t = Simple.Const.Naked_nativeint t
    end

    let kind : K.Boxable_number.t = Naked_nativeint
    let boxed_prover = T.prove_boxed_nativeint
    let unboxed_prover = T.prove_naked_nativeint
    let this = T.this_naked_nativeint
    let these = T.these_naked_nativeints
  end)

(* CR mshinwell:
   1. Overlap with Lift_constants?
   2. Work out how to make use of the projection information, e.g. for
      boxing/unboxing.
   3. Where there are aliases e.g. x = 3 and x = 5, we don't emit a term
      "x" even if we emit "3 union 5" as the type.
*)

module Make_simplify_box_number (P : For_unboxable_ints) = struct
  let simplify env r prim arg dbg =
    (* CR mshinwell: If [arg] is already a [Const] we shouldn't have to do
       much work... *)
    let arg, ty = S.simplify_simple env arg in
    let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
    let proof = (E.type_accessor env P.unboxed_prover) ty in
    let kind = K.Boxable_number.to_kind P.kind in
    match proof with
    | Proved nums ->
      begin match P.Num.Set.get_singleton nums with
      | Some n ->
        let symbol, r = R.new_lifted_constant r env (Boxed_float (Const n)) in
        let r = R.map_benefit r (Inlining_cost.Benefit.remove_box P.kind) in
        let named : Named.t = Simple (Simple.name (Name.symbol symbol)) in
        Reachable.reachable named, P.this n, r
      | None ->
        assert (not (P.Num.Set.is_empty nums));
        Reachable.reachable (original_term ()), P.these nums, r
      end
    | Proved Not_all_values_known ->
      Reachable.reachable (original_term ()), P.box ty, r
    | Invalid -> 
      Reachable.invalid (), T.bottom kind, r
end

module Simplify_box_number_float =
  Make_simplify_box_number (struct
    module Num = struct
      include Numbers.Float_by_bit_pattern
      let to_const t = Simple.Const.Naked_float t
    end

    let kind : K.Boxable_number.t = Naked_float
    let prover = T.prove_naked_float
    let this = T.this_boxed_float
    let these = T.these_boxed_floats
    let box = T.box_float
  end)

module Simplify_box_number_int32 =
  Make_simplify_box_number (struct
    module Num = struct
      include Int32
      let to_const t = Simple.Const.Naked_int32 t
    end

    let kind : K.Boxable_number.t = Naked_int32
    let prover = T.prove_naked_int32
    let this = T.this_boxed_int32
    let these = T.these_boxed_int32s
    let box = T.box_int32
  end)

module Simplify_box_number_int64 =
  Make_simplify_box_number (struct
    module Num = struct
      include Int64
      let to_const t = Simple.Const.Naked_int64 t
    end

    let kind : K.Boxable_number.t = Naked_int64
    let prover = T.prove_naked_int64
    let this = T.this_boxed_int64
    let these = T.these_boxed_int64s
    let box = T.box_int64
  end)

module Simplify_box_number_nativeint =
  Make_simplify_box_number (struct
    module Num = struct
      include Nativeint
      let to_const t = Simple.Const.Naked_nativeint t
    end

    let kind : K.Boxable_number.t = Naked_nativeint
    let prover = T.prove_naked_nativeint
    let this = T.this_boxed_nativeint
    let these = T.these_boxed_nativeints
    let box = T.box_nativeint
  end)

module Unary_int_arith (I : sig
  type t

  val kind : K.Standard_int.t
  val term : t -> Named.t

  val neg : t -> t

  include Identifiable.S with type t := t

  val this : t -> flambda_type
  val these : Set.t -> flambda_type
end) = struct
  let simplify env r prim dbg (op : Flambda_primitive.unary_int_arith_op) arg =
    let arg, ty = S.simplify_simple env arg in
    let proof = (E.type_accessor env T.prove_tagged_immediate) arg in
    let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
    let result_unknown () =
      (* One might imagine doing something complicated to [ty] to reflect
         the operation that has happened, but we don't.  As such we cannot
         propagate [ty] and must return "unknown". *)
      Reachable.reachable (original_term ()),
        T.unknown (K.Standard_int.to_kind I.kind) Other
    in
    let result_invalid () =
      Reachable.invalid (),
        T.bottom (K.Standard_int.to_kind I.kind)
    in
    let term, ty =
      match proof with
      | Proved (Exactly ints) ->
        assert (not (I.Set.is_empty ints));
        begin match op with
        | Neg ->
          let possible_results = I.Set.map (fun i -> I.neg i) ints in
          begin match I.Set.get_singleton possible_results with
          | Some i ->
            Reachable.reachable (I.term i), I.this i
          | None ->
            Reachable.reachable (original_term ()), I.these possible_results
          end
        end
      | Proved Not_all_values_known -> result_unknown ()
      | Invalid -> result_invalid ()
    in
    term, ty, r
end

module Unary_int_arith_tagged_immediate = Unary_int_arith (Targetint)
module Unary_int_arith_naked_int32 = Unary_int_arith (Int32)
module Unary_int_arith_naked_int64 = Unary_int_arith (Int64)
module Unary_int_arith_naked_nativeint = Unary_int_arith (Targetint)

module Make_simplify_int_conv (I : For_standard_ints) = struct
  let simplify env r prim arg ~(dst : Flambda_kind.Standard_int.t) dbg =
    let arg, ty = S.simplify_simple env arg in
    if Flambda_kind.Standard_int.equal I.kind dst then
      if T.is_bottom ty then
        Reachable.invalid (), T.bottom (K.Standard_int.to_kind dst), r
      else
        Reachable.reachable (Flambda.Named.Simple arg), ty, r
    else
      let proof = (E.type_accessor env I.prover) arg in
      let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
      let module N = I.Num in
      let term, ty =
        match proof with
        | Proved (Exactly is) ->
          assert (N.Set.length is > 0);
          begin match dst with
          | Tagged_immediate ->
            let imms =
              N.Set.fold (fun i imms ->
                  Immediate.Set.add (N.to_tagged_immediate i) imms)
                is
                Immediate.Set.empty
            in
            begin match Immediate.Set.get_singleton imms with
            | Some imm ->
              Reachable.reachable (
                  Simple (Simple.const (Tagged_immediate imm))),
                T.this_tagged_immediate imm
            | None ->
              Reachable.reachable (original_term ()),
                T.these_tagged_immediates imms
            end
          | Naked_int32 ->
            let is =
              N.Set.fold (fun i is ->
                  Naked_int32.Set.add (N.to_naked_int32 i) is)
                is
                Naked_int32.Set.empty
            in
            begin match Naked_int32.Set.get_singleton is with
            | Some i ->
              Reachable.reachable (Simple (Simple.const (Naked_int32 i))),
                T.this_naked_int32 i
            | None ->
              Reachable.reachable (original_term ()),
                T.these_naked_int32s is
            end
          | Naked_int64 ->
            let is =
              N.Set.fold (fun i is ->
                  Naked_int64.Set.add (N.to_naked_int64 i) is)
                is
                Naked_int64.Set.empty
            in
            begin match Naked_int64.Set.get_singleton is with
            | Some i ->
              Reachable.reachable (Simple (Simple.const (Naked_int64 i))),
                T.this_naked_int64 i
            | None ->
              Reachable.reachable (original_term ()),
                T.these_naked_int64s is
            end
          | Naked_nativeint ->
            let is =
              N.Set.fold (fun i is ->
                  Naked_nativeint.Set.add (N.to_naked_nativeint i) is)
                is
                Naked_nativeint.Set.empty
            in
            begin match Naked_nativeint.Set.get_singleton is with
            | Some i ->
              Reachable.reachable (Simple (Simple.const (Naked_nativeint i))),
                T.this_naked_nativeint i
            | None ->
              Reachable.reachable (original_term ()),
                T.these_naked_nativeints is
            end
          end
        | Proved Not_all_values_known ->
          Reachable.reachable (original_term ()),
            T.unknown (K.Standard_int.to_kind dst) Other
        | Invalid ->
          Reachable.invalid (), T.bottom (K.Standard_int.to_kind dst)
      in
      term, ty, r
end

module Simplify_int_conv_tagged_immediate =
  Make_simplify_int_conv (For_standard_ints_tagged_immediate)
module Simplify_int_conv_naked_int32 =
  Make_simplify_int_conv (For_standard_ints_naked_int32)
module Simplify_int_conv_naked_int64 =
  Make_simplify_int_conv (For_standard_ints_naked_int64)
module Simplify_int_conv_naked_nativeint =
  Make_simplify_int_conv (For_standard_ints_naked_nativeint)

let simplify_unary_float_arith_op env r prim
      (op : Flambda_primitive.unary_float_arith_op) arg dbg =
  let module F = Numbers.Float_by_bit_pattern in
  let arg, ty = S.simplify_simple env arg in
  let proof = (E.type_accessor env T.prove_naked_float) arg in
  let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
  let result_unknown () =
    Reachable.reachable (original_term ()), T.unknown (K.naked_float ()) Other
  in
  let result_invalid () = Reachable.invalid (), T.bottom (K.naked_float ()) in
  let term, ty =
    match proof with
    | Proved (Exactly fs) when E.const_float_prop env ->
      assert (not (F.Set.is_empty fs));
      let possible_results =
        match op with
        | Abs -> F.Set.map (fun f -> F.abs f) fs
        | Neg -> F.Set.map (fun f -> F.neg f) fs
      in
      begin match F.Set.get_singleton possible_results with
      | Some f ->
        let simple = Simple.const (Naked_float f) in
        Reachable.reachable (Simple simple), T.this_naked_float f
      | None ->
        Reachable.reachable (original_term ()),
          T.these_naked_floats possible_results
      end
    | Proved (Exactly _ | Not_all_values_known) -> result_unknown ()
    | Invalid -> result_invalid ()
  in
  term, ty, r

let simplify_string_length env r prim arg dbg =
  let arg, ty = S.simplify_simple env arg in
  let proof = (E.type_accessor env T.prove_string) arg in
  let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
  let result_kind = K.value Can_scan in
  let result_invalid () = Reachable.invalid (), T.bottom result_kind in
  let term, ty =
    match proof with
    | Proved (Exactly strs) ->
      assert (T.String_info.Set.cardinal strs > 0);
      let lengths =
        T.String_info.Set.fold (fun str lengths ->
            let size = Immediate.of_int str.size in
            Immediate.Set.add size lengths)
          strs
          Immediate.Set.empty
      in
      begin match Immediate.Set.get_singleton lengths with
      | Some length ->
        let simple = Simple.const (Tagged_immediate length) in
        Reachable (Simple simple), T.this_tagged_immediate length
      | None ->
        Reachable (original_term ()), T.these_tagged_immediates lengths
      end
    | Proved Not_all_values_known ->
      Reachable (original_term ()), T.unknown result_kind Other
    | Invalid -> result_invalid ()
  in
  term, ty, r

(* CR mshinwell: Factorize out together with [simplify_string_length] *)
let simplify_array_length env r prim arg ~array_kind dbg =
  let arg, ty = S.simplify_simple env arg in
  let proof = (E.type_accessor env T.lengths_of_arrays_or_blocks) arg in
  let original_term () : Named.t = Prim (Unary (prim, arg), dbg) in
  let result_kind = K.value Can_scan in
  let result_invalid () = Reachable.invalid (), T.bottom result_kind in
  let term, ty =
    match proof with
    | Proved (Exactly lengths) ->
      assert (Targetint.Set.cardinal lengths > 0);
      let lengths =
        Targetint.Set.fold (fun length lengths ->
            let length = Immediate.of_int length in
            Immediate.Set.add length lengths)
          lengths
          Immediate.Set.empty
      in
      begin match Immediate.Set.get_singleton lengths with
      | Some length ->
        let simple = Simple.const (Tagged_immediate length) in
        Reachable (Simple simple), T.this_tagged_immediate length
      | None ->
        Reachable (original_term ()), T.these_tagged_immediates lengths
      end
    | Proved Not_all_values_known ->
      Reachable (original_term ()), T.unknown result_kind Other
    | Invalid -> result_invalid ()
  in
  term, ty, r

let simplify_bigarray_length env r prim arg ~dimension dbg =
  let arg, ty = S.simplify_simple env arg in
  let result_kind = K.value Can_scan in
  if (E.type_accessor env T.is_bottom) ty then
    Reachable.invalid (), T.bottom result_kind
  else
    let named : Named.t = Prim (Unary (prim, arg), dbg) in
    named, T.unknown result_kind Other

let simplify_unary_primitive env r prim arg dbg =
  match prim with
  | Block_load (field_index, field_kind, field_is_mutable) ->
    simplify_block_load env r prim arg dbg ~field_index ~field_kind
      ~field_is_mutable
  | Duplicate_scannable_block { kind; source_mutability;
      destination_mutability; } ->
    simplify_duplicate_scannable_block env r prim arg dbg ~kind
      ~source_mutability ~destination_mutability
  | Is_int -> simplify_is_int env r prim arg dbg
  | Get_tag -> simplify_get_tag env r prim arg dbg
  | String_length _string_or_bytes ->
    simplify_string_length env r prim arg dbg
  | Swap_byte_endianness Tagged_immediate ->
    Simplify_swap_byte_endianness_tagged_immediate.simplify env r prim arg dbg
  | Swap_byte_endianness Naked_int32 ->
    Simplify_swap_byte_endianness_naked_int32.simplify env r prim arg dbg
  | Swap_byte_endianness Naked_int64 ->
    Simplify_swap_byte_endianness_naked_int64.simplify env r prim arg dbg
  | Swap_byte_endianness Naked_nativeint ->
    Simplify_swap_byte_endianness_naked_nativeint.simplify env r prim arg dbg
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
    begin match kind with
    | Tagged_immediate ->
      Unary_int_arith_tagged_immediate.simplify env r op arg
    | Naked_int32 ->
      Unary_int_arith_naked_int32.simplify env r op arg
    | Naked_int64 ->
      Unary_int_arith_naked_int64.simplify env r op arg
    | Naked_nativeint ->
      Unary_int_arith_naked_nativeint.simplify env r op arg
    end
  | Int_conv { src = Tagged_immediate; dst; } ->
    Simplify_int_conv_tagged_immediate.simplify env r prim arg ~dst dbg
  | Int_conv { src = Naked_int32; dst; } ->
    Simplify_int_conv_naked_int32.simplify env r prim arg ~dst dbg
  | Int_conv { src = Naked_int64; dst; } ->
    Simplify_int_conv_naked_int64.simplify env r prim arg ~dst dbg
  | Int_conv { src = Naked_nativeint; dst; } ->
    Simplify_int_conv_naked_nativeint.simplify env r prim arg ~dst dbg
  | Float_arith op -> simplify_unary_float_arith_op env r prim op arg dbg
  | Int_of_float -> simplify_int_of_float env r prim arg dbg
  | Float_of_int -> simplify_float_of_int env r prim arg dbg
  | Array_length array_kind ->
    simplify_array_length env r prim arg ~array_kind dbg
  | Bigarray_length { dimension : int; } ->
    simplify_bigarray_length env r prim arg ~dimension dbg
  | Unbox_number Naked_float ->
    Simplify_unbox_number_float.simplify env r prim arg dbg
  | Unbox_number Naked_int32 ->
    Simplify_unbox_number_int32.simplify env r prim arg dbg
  | Unbox_number Naked_int64 ->
    Simplify_unbox_number_int64.simplify env r prim arg dbg
  | Unbox_number Naked_nativeint ->
    Simplify_unbox_number_nativeint.simplify env r prim arg dbg
  | Box_number Naked_float ->
    Simplify_box_number_float.simplify env r prim arg dbg
  | Box_number Naked_int32 ->
    Simplify_box_number_int32.simplify env r prim arg dbg
  | Box_number Naked_int64 ->
    Simplify_box_number_int64.simplify env r prim arg dbg
  | Box_number Naked_nativeint ->
    Simplify_box_number_nativeint.simplify env r prim arg dbg
  | Project_closure closures ->
    simplify_project_closure env r closures
  | Move_within_set_of_closures by_closure_id ->
    simplify_move_within_set_of_closures env r by_closure_id
  | Project_var by_closure_id ->
    simplify_project_var env r by_closure_id

type 'a binary_arith_outcome_for_one_side_only =
  | Exactly of 'a
  | This_primitive of Flambda_primitive.t
  | The_other_side
  | Cannot_simplify
  | Invalid

module type Binary_arith_like_sig = sig
  module Lhs : Identifiable.S
  module Rhs : Identifiable.S

  module Pair : sig
    type nonrec t = Lhs.t * Rhs.t

    include Identifiable.S with type t := t
  end

  module Result : sig
    include Identifiable.S
  end

  val ok_to_evaluate : Env.t -> unit

  val cross_product : Lhs.Set.t -> Rhs.Set.t -> Pair.Set.t

  val kind : K.t
  val term : Result.t -> Named.t

  val prover_lhs : (flambda_type -> Lhs.Set.t) T.type_accessor
  val prover_rhs : (flambda_type -> Rhs.Set.t) T.type_accessor

  val these : Result.Set.t -> flambda_type

  type op

  val op : op -> Lhs.t -> Rhs.t -> Result.t option

  val op_lhs_unknown
     : op
    -> rhs:Rhs.t
    -> Result.t binary_arith_outcome_for_one_side_only

  val op_rhs_unknown
     : op
    -> lhs:Lhs.t
    -> Result.t binary_arith_outcome_for_one_side_only
end

module Binary_arith_like (N : Binary_arith_like_sig) : sig
  val simplify
     : E.t
    -> R.t
    -> Flambda_primitive.t
    -> Debuginfo.t
    -> op:N.op
    -> Simple.t
    -> Simple.t
    -> Named.t * R.t
end = struct
  module Possible_result = struct
    type t =
      | Var of Variable.t
      | Prim of Flambda_primitive.t
      | Exactly of N.t

    include Identifiable.Make_no_hash (struct
      type nonrec t = t

      let compare t1 t2 =
        match t1, t2 with
        | Var var1, Var var2 -> Variable.compare var1 var2
        | Prim prim1, Prim prim2 -> Flambda_primitive.compare prim1 prim2
        | Exactly i1, Exactly i2 -> N.compare i1 i2
        | Var _, (Prim _ | Exactly _) -> -1
        | Prim _, Var _ -> 1
        | Prim _, Exactly _ -> -1
        | Exactly, (Var _ | Prim _) -> 1

      let print _ppf _t = Misc.fatal_error "Not yet implemented"
    end)
  end

  let simplify env r prim dbg op arg1 arg2 : Named.t * R.t =
    let module P = Possible_result in
    let arg1, ty1 = S.simplify_simple env arg1 in
    let arg2, ty2 = S.simplify_simple env arg2 in
    let proof1 = (E.type_accessor env N.prover_lhs) arg1 in
    let proof2 = (E.type_accessor env N.prover_rhs) arg2 in
    let original_term () : Named.t = Prim (Binary (prim, arg1, arg2), dbg) in
    let result_unknown () =
      Reachable.reachable (original_term ()), T.unknown N.kind Other
    in
    let result_invalid () = Reachable.invalid (), T.bottom N.kind in
    let check_possible_results ~possible_results =
      (* CR mshinwell: We may want to bound the size of the set. *)
      let named, ty =
        if N.Result.Set.is_empty possible_results then
          result_invalid ()
        else
          let named =
            match N.Result.Set.get_singleton possible_results with
            | Some (Exactly i) -> N.term i
            | Some (Prim prim) -> Named.Prim (prim, dbg)
            | Some (Var var) -> Named.Simple (Simple.var var)
            | None -> original_term ()
          in
          let ty =
            let is =
              List.filter_map (function
                  | Exactly i -> Some i
                  | Prim _ | Var _ -> None)
                (N.Result.Set.to_list possible_results)
            in
            if List.length is = N.Result.Set.cardinal possible_results then
              N.these (N.Result.Set.of_list is)
            else
              match N.Result.Set.get_singleton possible_results with
              | Some (Var var) -> T.alias kind var
              | Some (Exactly _)
              | Some (Prim _)
              | None -> T.unknown kind Other
          in
          named, ty
      in
      Reachable.reachable named, ty
    in
    let only_one_side_known op nums ~folder ~other_side_var =
      let possible_results =
        folder (fun i possible_results ->
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
          nums
          Some (N.Result.Set.empty)
      in
      match possible_results with
      | Some results -> check_possible_results ~possible_results
      | None -> result_unknown ()
    in
    let term, ty =
      match proof1, proof2 with
      | (Proved (Exactly nums1), Proved (Exactly nums2))
          when N.ok_to_evaluate env ->
        assert (not (N.Lhs.Set.is_empty nums1));
        assert (not (N.Rhs.Set.is_empty nums2));
        let all_pairs = N.cross_product nums1 nums2 in
        let possible_results =
          N.Pair.Set.fold (fun (i1, i2) possible_results ->
              match N.op op i1 i2 with
              | None -> possible_results
              | Some result ->
                N.Result.Set.add (Exactly result) possible_results)
            all_pairs
            N.Result.Set.empty
        in
        check_possible_results ~possible_results
      | (Proved (Exactly nums1), Proved Not_all_values_known)
          when N.ok_to_evaluate env ->
        assert (not (N.Lhs.Set.is_empty nums1));
        only_one_side_known (fun i -> N.op_rhs_unknown op ~lhs:i) nums1
          ~folder:N.Lhs.Set.fold
          ~other_side_var:arg2
      | (Proved Not_all_values_known, Proved (Exactly nums2))
          when N.ok_to_evaluate env ->
        assert (not (N.Rhs.Set.is_empty nums2));
        only_one_side_known (fun i -> N.op_lhs_unknown op ~rhs:i) nums2
          ~folder:N.Rhs.Set.fold
          ~other_side_var:arg1
      | Proved _, Proved _ ->
        result_unknown ()
      | Invalid, _ | _, Invalid ->
        result_invalid ()
    in
    term, ty, r
end

module Int_ops_for_binary_arith (I : sig
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

  include Identifiable.S with type t := t

  val these : Set.t -> flambda_type

  val prover : (flambda_type -> Set.t) T.type_accessor

  module Pair : sig
    type nonrec t = t * t

    include Identifiable.S with type t := t
  end

  val cross_product : Set.t -> Set.t -> Pair.Set.t
end) : sig
  include Binary_arith_like_sig
    with type op = binary_int_arith_op
end = struct
  module Lhs = I
  module Rhs = I
  module Result = I

  let ok_to_evaluate _env = true

  let prover_lhs = I.prover
  let prover_rhs = I.prover

  let op (op : binary_int_arith_op) n1 n2 =
    let always_some f = Some (f n1 n2) in
    match op with
    | Add -> always_some I.add
    | Sub -> always_some I.sub
    | Mul -> always_some I.mul
    | Div -> I.div n1 n2
    | Mod -> I.mod_ n1 n2
    | And -> always_some I.and_
    | Or -> always_some I.or_
    | Xor -> always_some I.xor

  type symmetric_op =
    | Add
    | Mul
    | And
    | Or
    | Xor

  let symmetric_op_one_side_unknown (op : symmetric_op) ~this_side
        : N.t binary_arith_outcome_for_one_side_only =
    let negate_lhs () : N.t binary_arith_outcome_for_one_side_only =
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

  let op_lhs_unknown ~rhs : N.t binary_arith_outcome_for_one_side_only =
    let negate_the_other_side () : N.t binary_arith_outcome_for_one_side_only =
      This_primitive (Unary (Int_arith Neg, arg1))
    in
    match op with
    | Add -> symmetric_op_one_side_unknown Add ~this_side:rhs
    | Mul -> symmetric_op_one_side_unknown Mul ~this_side:rhs
    | And -> symmetric_op_one_side_unknown And ~this_side:rhs
    | Or -> symmetric_op_one_side_unknown Or ~this_side:rhs
    | Xor -> symmetric_op_one_side_unknown Xor ~this_side:rhs
    | Sub ->
      if I.equal rhs I.zero then The_other_side
      else Cannot_simplify
    | Div ->
      if I.equal rhs I.zero then Invalid
      else if I.equal rhs I.one then The_other_side
      else if I.equal rhs I.minus_one then negate_the_other_side ()
      (* CR mshinwell: Add 0 / x = 0 when x <> 0 *)
      else Cannot_simplify
    | Mod ->
      (* CR mshinwell: We could be more clever for Mod and And *)
      if I.equal rhs I.zero then Invalid
      else if I.equal rhs I.one then Exactly I.zero
      else if I.equal rhs I.minus_one then Exactly I.zero
      else Cannot_simplify

  let op_rhs_unknown ~lhs : N.t binary_arith_outcome_for_one_side_only =
    let negate_the_other_side () : N.t binary_arith_outcome_for_one_side_only =
      This_primitive (Unary (Int_arith Neg, arg2))
    in
    match op with
    | Add -> symmetric_op_one_side_unknown Add ~this_side:lhs
    | Mul -> symmetric_op_one_side_unknown Mul ~this_side:lhs
    | And -> symmetric_op_one_side_unknown And ~this_side:lhs
    | Or -> symmetric_op_one_side_unknown Or ~this_side:lhs
    | Xor -> symmetric_op_one_side_unknown Xor ~this_side:lhs
    | Sub ->
      if I.equal lhs I.zero then negate_the_other_side ()
      else Cannot_simplify
    | Div | Mod -> Cannot_simplify
  in
end

module Int_ops_for_binary_arith_tagged_immediate =
  Int_ops_for_binary_arith (Targetint.OCaml)
module Int_ops_for_binary_arith_int32 =
  Int_ops_for_binary_arith (Int32)
module Int_ops_for_binary_arith_int64 =
  Int_ops_for_binary_arith (Int64)
module Int_ops_for_binary_arith_nativeint =
  Int_ops_for_binary_arith (Targetint)

module Binary_int_arith_tagged_immediate =
  Binary_arith_like (Int_ops_for_binary_arith_tagged_immediate)
module Binary_int_arith_int32 =
  Binary_arith_like (Int_ops_for_binary_arith_int32)
module Binary_int_arith_int64 =
  Binary_arith_like (Int_ops_for_binary_arith_int64)
module Binary_int_arith_nativeint =
  Binary_arith_like (Int_ops_for_binary_arith_nativeint)

module Int_ops_for_binary_shift (I : sig
  type t

  val kind : K.Standard_int.t
  val term : t -> Named.t

  val zero : t

  val shift_left : t -> t -> t
  (* [shift_right] is arithmetic shift right, matching [Int32], [Int64], etc. *)
  val shift_right : t -> t -> t
  val shift_right_logical : t -> t -> t

  include Identifiable.S with type t := t

  val these : Set.t -> flambda_type

  val prover : (flambda_type -> Set.t) T.type_accessor

  module Pair : sig
    type nonrec t = t * t

    include Identifiable.S with type t := t
  end

  val cross_product : Set.t -> Set.t -> Pair.Set.t
end) : sig
  include Binary_arith_sig
    with type op = binary_int_arith_op
end = struct
  module Lhs = I
  module Rhs = Immediate
  module Result = I

  let ok_to_evaluate _env = true

  let prover_lhs = I.prover
  let prover_rhs = T.prove_tagged_immediate

  let op (op : binary_int_arith_op) n1 n2 =
    let always_some f = Some (f n1 n2) in
    match op with
    | Lsl -> always_some I.shift_left
    | Lsr -> always_some I.shift_right_logical
    | Asr -> always_some I.shift_right

  let op_lhs_unknown ~rhs : N.t binary_arith_outcome_for_one_side_only =
    let module O = Targetint.OCaml in
    let rhs = Immediate.to_targetint rhs in
    match op with
    | Lsl | Lsr | Asr ->
      (* Shifting either way by [Targetint.size] or above is undefined.
         However note that we cannot produce [Invalid] unless the code is
         type unsafe, which it is not here.  (Otherwise a GADT match might
         be reduced to only one possible case which it would be wrong to
         take.) *)
      if O.equal rhs O.zero then The_other_side
      else Cannot_simplify

  let op_rhs_unknown ~lhs : N.t binary_arith_outcome_for_one_side_only =
    match op with
    | Lsl | Lsr ->
      if I.equal lhs I.zero then Exactly I.zero
      else Cannot_simplify
    | Asr ->
      if I.equal lhs I.zero then Exactly I.zero
      else if I.equal lhs I.minus_one then Exactly I.minus_one
      else Cannot_simplify
end

module Int_ops_for_binary_shift_tagged_immediate =
  Int_ops_for_binary_shift (Targetint.OCaml)
module Int_ops_for_binary_shift_int32 =
  Int_ops_for_binary_shift (Int32)
module Int_ops_for_binary_shift_int64 =
  Int_ops_for_binary_shift (Int64)
module Int_ops_for_binary_shift_nativeint =
  Int_ops_for_binary_shift (Targetint)

module Binary_int_shift_tagged_immediate =
  Binary_arith_like (Int_ops_for_binary_shift_tagged_immediate)
module Binary_int_shift_int32 =
  Binary_arith_like (Int_ops_for_binary_shift_int32)
module Binary_int_shift_int64 =
  Binary_arith_like (Int_ops_for_binary_shift_int64)
module Binary_int_shift_nativeint =
  Binary_arith_like (Int_ops_for_binary_shift_nativeint)

module Int_ops_for_binary_comp (I : sig
  type t

  val kind : K.Standard_int.t
  val term : t -> Named.t

  val zero : t

  val compare : t -> t -> int

  include Identifiable.S with type t := t

  val these : Set.t -> flambda_type

  val prover : (flambda_type -> Set.t) T.type_accessor

  module Pair : sig
    type nonrec t = t * t

    include Identifiable.S with type t := t
  end

  val cross_product : Set.t -> Set.t -> Pair.Set.t
end) : sig
  include Binary_arith_sig
    with type op = Flambda_primitive.comparison
end = struct
  module Lhs = I
  module Rhs = I
  module Result = Immediate

  let ok_to_evaluate _env = true

  let prover_lhs = I.prover
  let prover_rhs = I.prover

  let op (op : Flambda_primitive.comparison) n1 n2 =
    let bool b =
      if b then Immediate.const_true else Immediate.const_false
    in
    match op with
    | Eq -> Some (bool (I.equal n1 n2))
    | Neq -> Some (bool (not (I.equal n1 n2)))
    | Lt -> Some (bool (I.compare n1 n2 < 0))
    | Gt -> Some (bool (I.compare n1 n2 > 0))
    | Le -> Some (bool (I.compare n1 n2 <= 0))
    | Ge -> Some (bool (I.compare n1 n2 >= 0))

  let op_lhs_unknown _op ~rhs:_ : N.t binary_arith_outcome_for_one_side_only =
    Cannot_simplify

  let op_rhs_unknown _op ~lhs:_ : N.t binary_arith_outcome_for_one_side_only =
    Cannot_simplify
end

module Int_ops_for_binary_comp_tagged_immediate =
  Int_ops_for_binary_comp (Targetint.OCaml)
module Int_ops_for_binary_comp_int32 =
  Int_ops_for_binary_comp (Int32)
module Int_ops_for_binary_comp_int64 =
  Int_ops_for_binary_comp (Int64)
module Int_ops_for_binary_comp_nativeint =
  Int_ops_for_binary_comp (Targetint)

module Binary_int_comp_tagged_immediate =
  Binary_arith_like (Int_ops_for_binary_comp_tagged_immediate)
module Binary_int_comp_int32 =
  Binary_arith_like (Int_ops_for_binary_comp_int32)
module Binary_int_comp_int64 =
  Binary_arith_like (Int_ops_for_binary_comp_int64)
module Binary_int_comp_nativeint =
  Binary_arith_like (Int_ops_for_binary_comp_nativeint)

module Int_ops_for_binary_comp_unsigned : sig
  include Binary_arith_sig
    with type op = Flambda_primitive.comparison
end = struct
  module Lhs = Targetint
  module Rhs = Targetint
  module Result = Immediate

  let ok_to_evaluate _env = true

  let prover_lhs = T.prove_naked_immediate
  let prover_rhs = T.prove_naked_immediate

  let op (op : Flambda_primitive.comparison) n1 n2 =
    let bool b =
      if b then Immediate.const_true else Immediate.const_false
    in
    match op with
    | Eq -> Some (bool (Targetint.equal n1 n2))
    | Neq -> Some (bool (not (Targetint.equal n1 n2)))
    | Lt -> Some (bool (Targetint.compare_unsigned n1 n2 < 0))
    | Gt -> Some (bool (Targetint.compare_unsigned n1 n2 > 0))
    | Le -> Some (bool (Targetint.compare_unsigned n1 n2 <= 0))
    | Ge -> Some (bool (Targetint.compare_unsigned n1 n2 >= 0))

  let op_lhs_unknown _op ~rhs:_ : N.t binary_arith_outcome_for_one_side_only =
    Cannot_simplify

  let op_rhs_unknown _op ~lhs:_ : N.t binary_arith_outcome_for_one_side_only =
    Cannot_simplify
end

module Binary_int_comp_unsigned =
  Binary_arith_like (Int_ops_for_binary_comp_unsigned)

module Float_ops_for_binary_arith : sig
  include Binary_arith_sig
    with type op = binary_float_arith_op
end = struct
  module F = Numbers.Float_by_bit_pattern

  let ok_to_evaluate env = E.float_const_prop env

  let op op n1 n2 =
    let always_some f = Some (f n1 n2) in
    match op with
    | Add -> always_some F.add
    | Sub -> always_some F.sub
    | Mul -> always_some F.mul
    | Div -> always_some F.div

  type symmetric_op =
    | Add
    | Mul

  let symmetric_op_one_side_unknown (op : symmetric_op) ~this_side
        : N.t binary_arith_outcome_for_one_side_only =
    let negate_lhs () : N.t binary_arith_outcome_for_one_side_only =
      This_primitive (Unary (Float_arith Neg, arg1))
    in
    match op with
    | Add ->
      (* You might think that "x + 0" has the same representation as "x".
         However it doesn't in the case where that constant zero is +0 and
         x is equal to -0. *)
      Cannot_simplify
    | Mul ->
      if I.equal rhs I.one then The_other_side
      else if I.equal rhs I.minus_one then negate_lhs ()
      else Cannot_simplify

  let op_lhs_unknown ~rhs : N.t binary_arith_outcome_for_one_side_only =
    let negate_the_other_side () : N.t binary_arith_outcome_for_one_side_only =
      This_primitive (Unary (Float_arith Neg, arg1))
    in
    match op with
    | Add -> symmetric_op_one_side_unknown Add ~this_side:rhs
    | Mul -> symmetric_op_one_side_unknown Mul ~this_side:rhs
    | Sub -> Cannot_simplify
    | Div ->
      if I.equal rhs I.one then The_other_side
      else if I.equal rhs I.minus_one then negate_the_other_side ()
      else Cannot_simplify

  let op_rhs_unknown ~lhs : N.t binary_arith_outcome_for_one_side_only =
    let negate_the_other_side () : N.t binary_arith_outcome_for_one_side_only =
      This_primitive (Unary (Float_arith Neg, arg2))
    in
    match op with
    | Add -> symmetric_op_one_side_unknown Add ~this_side:lhs
    | Mul -> symmetric_op_one_side_unknown Mul ~this_side:lhs
    | Sub -> Cannot_simplify
    | Div -> Cannot_simplify
end

module Binary_float_arith = Binary_arith_like (Float_ops_for_binary_arith)

module Float_ops_for_binary_comp : sig
  include Binary_arith_like_sig
    with type op = binary_float_comp_op
end = struct
  module Lhs = I
  module Rhs = I
  module Result = Immediate

  let prover_lhs = I.prover
  let prover_rhs = I.prover

  let ok_to_evaluate env = E.float_const_prop env

  module F = Numbers.Float_by_bit_pattern

  let op (op : Flambda_primitive.comparison) n1 n2 =
    let bool b =
      if b then Immediate.const_true else Immediate.const_false
    in
    match op with
    | Eq -> Some (bool (F.equal_ieee n1 n2))
    | Neq -> Some (bool (not (F.equal_ieee n1 n2)))
    | Lt -> Some (bool (F.compare_ieee n1 n2 < 0))
    | Gt -> Some (bool (F.compare_ieee n1 n2 > 0))
    | Le -> Some (bool (F.compare_ieee n1 n2 <= 0))
    | Ge -> Some (bool (F.compare_ieee n1 n2 >= 0))

  let result_of_comparison_with_nan op =
    match op with
    | Neq -> Immediate.const_true
    | Eq ->
    | Lt ->
    | Gt ->
    | Le ->
    | Ge -> Immediate.const_false

  let op_lhs_unknown op ~rhs : N.t binary_arith_outcome_for_one_side_only =
    if F.is_any_nan rhs then result_of_comparison_with_nan op
    else Cannot_simplify

  let op_rhs_unknown op ~lhs : N.t binary_arith_outcome_for_one_side_only =
    if F.is_any_nan lhs then result_of_comparison_with_nan op
    else Cannot_simplify
end

module Binary_float_comp = Binary_arith_like (Float_ops_for_binary_comp)

let simplify_block_load_computed_index env r prim ~block ~index
      ~field_kind ~field_is_mutable dbg =
  let orig_block = block in
  let index, index_ty = S.simplify_simple env index in
  let block, block_ty = S.simplify_simple env block in
  let original_term () : Named.t = Prim (Binary (prim, block, index), dbg) in
  let invalid () = Reachable.invalid (), T.bottom field_kind in
  let proof = (E.type_accessor env T.prove_tagged_immediate) arg in
  let unique_index_unknown () =
    (* XXX maybe this isn't good enough; we should check [block] is actually
       a block.  What constraints on tags/sizes are there? *)
    if (E.type_accessor env T.is_bottom) ty then
      invalid ()
    else
      Reachable.reachable (original_term ()), T.unknown field_kind Other
  in
  let term, ty =
    match proof with
    | Proved (Exactly indexes) ->
      begin match Immediate.Set.get_singleton indexes with
      | Some field_index ->
        simplify_block_load env r prim orig_block dbg ~field_index ~field_kind
          ~field_is_mutable
      | None -> unique_index_unknown ()
      end
    | Proved Not_all_values_known -> unique_index_unknown ()
    | Invalid -> invalid ()
  in
  term, ty, r

let simplify_block_set env r prim ~field ~field_kind ~init_or_assign
      ~block ~new_value dbg =
  if field < 0 then begin
    Misc.fatal_errorf "[Block_set] with bad field index %d: %a"
      field
      Flambda_primitive.print prim
  end;
  let field_kind' = Flambda_primitive.kind_of_block_set_kind field_kind in
  let block, block_ty = S.simplify_simple env block in
  let new_value, new_value_ty = S.simplify_simple env new_value in
  let original_term () : Named.t = Prim (Binary (prim, block, index), dbg) in
  let result_kind = Flambda_kind.value Can_scan in
  let invalid () = Reachable.invalid (), T.bottom result_kind in
  let ok () =
    match new_value_proof with
    | Proved _ ->
      Reachable.reachable (original_term ()), T.unknown result_kind Other
    | Invalid -> invalid ()
  in
  match field_kind with
  | Immediate | Pointer ->
    let proof = (E.type_accessor env T.prove_blocks_and_immediates) block_ty in
    begin match proof with
    | Proved (Exactly (blocks, _imms)) ->
      if not (T.Blocks.valid_field_access blocks ~field) then invalid ()
      else ok ()
    | Proved Not_all_values_known -> ok ()
    | Invalid -> invalid ()
    end
  | Float ->
    let block_proof = (E.type_accessor env T.prove_float_array) block_ty in
    let new_value_proof =
      (E.type_accessor env T.prove_naked_float) new_value_ty
    in
    match block_proof with
    | Proved (Exactly sizes) ->
      if not (Int.Set.exists (fun size -> size > field) sizes) then invalid ()
      else ok ()
    | Proved Not_all_values_known -> ok ()
    | Invalid -> invalid ()

let simplify_array_load env r prim dbg array_kind arg1 arg2 =
  ...

let simplify_string_load env r prim dbg width arg1 arg2 =
  ...

let simplify_bigstring_load env r prim dbg width arg1 arg2 =
  ...

let simplify_binary_primitive env r prim arg1 arg2 dbg =
  match prim with
  | Block_load_computed_index ->
    simplify_block_load_computed_index env r prim ~block:arg1 ~index:arg2 dbg
  | Block_set (field, field_kind, init_or_assign) ->
    simplify_block_set env r prim ~field ~field_kind ~init_or_assign
      ~block:arg1 ~new_value:arg2 dbg
  | Int_arith (kind, op) ->
    begin match kind with
    | Tagged_immediate ->
      Binary_int_arith_tagged_immediate.simplify env r prim dbg op arg1 arg2
    | Naked_int32 ->
      Binary_int_arith_naked_int32.simplify env r prim dbg op arg1 arg2
    | Naked_int64 ->
      Binary_int_arith_naked_int64.simplify env r prim dbg op arg1 arg2
    | Naked_nativeint ->
      Binary_int_arith_naked_nativeint.simplify env r prim dbg op arg1 arg2
    end
  | Int_shift (kind, op) ->
    begin match kind with
    | Tagged_immediate ->
      Binary_int_shift_tagged_immediate.simplify env r prim dbg op arg1 arg2
    | Naked_int32 ->
      Binary_int_shift_naked_int32.simplify env r prim dbg op arg1 arg2
    | Naked_int64 ->
      Binary_int_shift_naked_int64.simplify env r prim dbg op arg1 arg2
    | Naked_nativeint ->
      Binary_int_shift_naked_nativeint.simplify env r prim dbg op arg1 arg2
    end
  | Int_comp (kind, op) ->
    begin match kind with
    | Tagged_immediate ->
      Binary_int_comp_tagged_immediate.simplify env r prim dbg op arg1 arg2
    | Naked_int32 ->
      Binary_int_comp_naked_int32.simplify env r prim dbg op arg1 arg2
    | Naked_int64 ->
      Binary_int_comp_naked_int64.simplify env r prim dbg op arg1 arg2
    | Naked_nativeint ->
      Binary_int_comp_naked_nativeint.simplify env r prim dbg op arg1 arg2
    end
  | Int_comp_unsigned op ->
    Binary_int_comp_unsigned.simplify env r prim dbg op arg1 arg2
  | Float_arith op ->
    Binary_float_arith.simplify env r prim dbg op arg1 arg2
  | Float_comp op ->
    Binary_float_comp.simplify env r prim dbg op arg1 arg2
  | Array_load array_kind ->
    simplify_array_load env r prim dbg array_kind arg1 arg2
  | String_load width ->
    simplify_string_load env r prim dbg width arg1 arg2
  | Bigstring_load width ->
    simplify_bigstring_load env r prim dbg width arg1 arg2

let simplify_block_set_computed env r prim dbg ~scanning ~init_or_assign
      arg1 arg2 arg3 =
  ...

let simplify_bytes_set env r prim dbg ~string_accessor_width arg1 arg2 arg3 =
  ...

let simplify_array_set env r prim dbg ~array_kind arg1 arg2 arg3 =
  ...

let simplify_bigstring_set env r prim dbg ~bigstring_accessor_width
      arg1 arg2 arg3 =
  ...

let simplify_ternary_primitive env r prim arg1 arg2 arg3 dbg =
  match prim with
  | Block_set_computed (scanning, init_or_assign) ->
    simplify_block_set_computed env r prim dbg ~scanning ~init_or_assign
      arg1 arg2 arg3
  | Bytes_set string_accessor_width ->
    simplify_bytes_set env r prim dbg ~string_accessor_width arg1 arg2 arg3
  | Array_set array_kind ->
    simplify_array_set env r prim dbg ~array_kind arg1 arg2 arg3
  | Bigstring_set bigstring_accessor_width ->
    simplify_bigstring_set env r prim dbg ~bigstring_accessor_width
      arg1 arg2 arg3

let simplify_make_block env r prim dbg ~tag ~mutable_or_immutable ~arity args =
  ...

let simplify_make_array env r prim dbg ~array_kind ~mutable_or_immutable args =
  ...

let simplify_bigarray_set env r prim dbg ~num_dims ~kind ~layout ~args =
  ...

let simplify_bigarray_load env r prim dbg ~num_dims ~kind ~layout args =
  ...

let simplify_variadic_primitive env r prim args dbg =
  match prim with
  | Make_block (tag, mutable_or_immutable, arity) ->
    simplify_make_block env r prim dbg ~tag ~mutable_or_immutable ~arity args
  | Make_array (array_kind, mutable_or_immutable) ->
    simplify_make_array env r prim dbg ~array_kind ~mutable_or_immutable args
  | Bigarray_set (num_dims, kind, layout) ->
    simplify_bigarray_set env r prim dbg ~num_dims ~kind ~layout ~args
  | Bigarray_load (num_dims, kind, layout) ->
    simplify_bigarray_load env r prim dbg ~num_dims ~kind ~layout args

let simplify_primitive env r prim dbg =
  match prim with
  | Unary (prim, arg) ->
    simplify_unary_primitive env r prim arg dbg
  | Binary (prim, arg1, arg2) ->
    simplify_binary_primitive env r prim arg1 arg2 dbg
  | Ternary (prim, arg1, arg2, arg3) ->
    simplify_ternary_primitive env r prim arg1 arg2 arg3 dbg
  | Variadic (prim, args) ->
    simplify_variadic_primitive env r prim args dbg

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
