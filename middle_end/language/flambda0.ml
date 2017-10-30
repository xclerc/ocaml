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

module Int = Numbers.Int
module K = Flambda_kind

let fprintf = Format.fprintf

module Call_kind = struct
  type method_kind = Self | Public | Cached

  let print_method_kind ppf kind =
    let fprintf = Format.fprintf in
    match kind with
    | Self -> fprintf ppf "Self"
    | Public -> fprintf ppf "Public"
    | Cached -> fprintf ppf "Cached"

  type t =
    | Direct of {
        closure_id : Closure_id.t;
        return_arity : Flambda_arity.t;
      }
    | Indirect_unknown_arity
    | Indirect_known_arity of {
        param_arity : Flambda_arity.t;
        return_arity : Flambda_arity.t;
      }
    | Method of { kind : method_kind; obj : Variable.t; }


  let equal t1 t2 =
    match t1, t2 with
    | Direct { closure_id = closure_id1; return_arity = return_arity1; },
        Direct { closure_id = closure_id2; return_arity = return_arity2; } ->
      Closure_id.equal closure_id1 closure_id2
        && Flambda_arity.equal return_arity1 return_arity2
    | Indirect_unknown_arity, Indirect_unknown_arity -> true
    | Indirect_known_arity {
        param_arity = param_arity1; return_arity = return_arity1;
      },
        Indirect_known_arity {
          param_arity = param_arity2; return_arity = return_arity2;
        } ->
      Flambda_arity.equal param_arity1 param_arity2
        && Flambda_arity.equal return_arity1 return_arity2
    | Method { kind = kind1; obj = obj1; },
        Method { kind = kind2; obj = obj2; } ->
      Variable.equal obj1 obj2
        && begin match kind1, kind2 with
           | Self, Self
           | Public, Public
           | Cached, Cached -> true
           | Self, _
           | Public, _
           | Cached, _ -> false
           end
    | Direct _, _
    | Indirect_unknown_arity, _
    | Indirect_known_arity _, _
    | Method _, _ -> false

  let print ppf t =
    let fprintf = Format.fprintf in
    match t with
    | Direct { closure_id; return_arity; } ->
      fprintf ppf "@[(Direct %a %a)@]"
        Closure_id.print closure_id
        Flambda_arity.print return_arity
    | Indirect_unknown_arity ->
      fprintf ppf "Indirect_unknown_arity"
    | Indirect_known_arity { param_arity; return_arity; } ->
      fprintf ppf "@[(Indirect_known_arity %a -> %a)@]"
        Flambda_arity.print param_arity
        Flambda_arity.print return_arity
    | Method { kind; obj; } ->
      fprintf ppf "@[(Method %a : %a)@]"
        Variable.print obj
        print_method_kind kind

  let return_arity t : Flambda_arity.t =
    match t with
    | Direct { return_arity; _ }
    | Indirect_known_arity { return_arity; _ } -> return_arity
    | Indirect_unknown_arity
    | Method _ -> [Flambda_kind.value Must_scan]
end

module Const = struct
  type t =
    | Untagged_immediate of Immediate.t
    | Tagged_immediate of Immediate.t
    | Naked_float of float
    | Naked_int32 of Int32.t
    | Naked_int64 of Int64.t
    | Naked_nativeint of Targetint.t

  include Identifiable.Make (struct
    type nonrec t = t

    let compare t1 t2 =
      match t1, t2 with
      | Untagged_immediate i1, Untagged_immediate i2 ->
        Immediate.compare i1 i2
      | Tagged_immediate i1, Tagged_immediate i2 ->
        Immediate.compare i1 i2
      | Naked_float f1, Naked_float f2 ->
        Pervasives.compare f1 f2
      | Naked_int32 n1, Naked_int32 n2 ->
        Int32.compare n1 n2
      | Naked_int64 n1, Naked_int64 n2 ->
        Int64.compare n1 n2
      | Naked_nativeint n1, Naked_nativeint n2 ->
        Targetint.compare n1 n2
      | Untagged_immediate _, _ -> -1
      | _, Untagged_immediate _ -> 1
      | Tagged_immediate _, _ -> -1
      | _, Tagged_immediate _ -> 1
      | Naked_float _, _ -> -1
      | _, Naked_float _ -> 1
      | Naked_int32 _, _ -> -1
      | _, Naked_int32 _ -> 1
      | Naked_int64 _, _ -> -1
      | _, Naked_int64 _ -> 1

    let equal t1 t2 = (compare t1 t2 = 0)

    let hash t =
      match t with
      | Untagged_immediate n -> Immediate.hash n
      | Tagged_immediate n -> Immediate.hash n
      | Naked_float n -> Hashtbl.hash n
      | Naked_int32 n -> Hashtbl.hash n
      | Naked_int64 n -> Hashtbl.hash n
      | Naked_nativeint n -> Targetint.hash n

    let print ppf (t : t) =
      match t with
      | Untagged_immediate i -> Format.fprintf ppf "%a!" Immediate.print i
      | Tagged_immediate i -> Format.fprintf ppf "%a" Immediate.print i
      | Naked_float f -> Format.fprintf ppf "%f!" f
      | Naked_int32 n -> Format.fprintf ppf "%ld!" n
      | Naked_int64 n -> Format.fprintf ppf "%Ld!" n
      | Naked_nativeint n -> Format.fprintf ppf "%a!" Targetint.print n
  end)
end

type inline_attribute =
  | Always_inline
  | Never_inline
  | Unroll of int
  | Default_inline

let print_inline_attribute ppf attr =
  let fprintf = Format.fprintf in
  match attr with
  | Always_inline -> fprintf ppf "Always_inline"
  | Never_inline -> fprintf ppf "Never_inline"
  | Unroll n -> fprintf ppf "@[(Unroll %d)@]" n
  | Default_inline -> fprintf ppf "Default_inline"

type specialise_attribute =
  | Always_specialise
  | Never_specialise
  | Default_specialise

let _print_specialise_attribute ppf attr =
  let fprintf = Format.fprintf in
  match attr with
  | Always_specialise -> fprintf ppf "Always_specialise"
  | Never_specialise -> fprintf ppf "Never_specialise"
  | Default_specialise -> fprintf ppf "Default_specialise"

module Apply = struct
  type t = {
    func : Variable.t;
    continuation : Continuation.t;
    args : Variable.t list;
    call_kind : Call_kind.t;
    dbg : Debuginfo.t;
    inline : inline_attribute;
    specialise : specialise_attribute;
  }

  let equal t1 t2 =
    Variable.equal t1.func t2.func
      && Continuation.equal t1.continuation t2.continuation
      && Misc.Stdlib.List.equal Variable.equal t1.args t2.args
      && Call_kind.equal t1.call_kind t2.call_kind
      && Debuginfo.equal t1.dbg t2.dbg
      && t1.inline = t2.inline
      && t1.specialise = t2.specialise
end

type assign = {
  being_assigned : Mutable_variable.t;
  new_value : Variable.t;
}

module Free_var = struct
  type t = {
    var : Variable.t;
    projection : Projection.t option;
  }

  let var t = t.var

  include Identifiable.Make (struct
    type nonrec t = t

    let compare (t1 : t) (t2 : t) =
      let c = Variable.compare t1.var t2.var in
      if c <> 0 then c
      else
        match t1.projection, t2.projection with
        | None, None -> 0
        | Some _, None -> 1
        | None, Some _ -> -1
        | Some proj1, Some proj2 -> Projection.compare proj1 proj2

    let equal (t1 : t) (t2 : t) =
      compare t1 t2 = 0

    let hash = Hashtbl.hash

    let print ppf (t : t) =
      match t.projection with
      | None ->
        fprintf ppf "%a" Variable.print t.var
      | Some projection ->
        fprintf ppf "%a(= %a)"
          Variable.print t.var
          Projection.print projection
  end)
end

module Free_vars = struct
  (* CR mshinwell: We could make this abstract in the interface and maintain
     the reverse map too. *)
  type t = Free_var.t Var_within_closure.Map.t

  let find_by_variable t var =
    let exception Found of Var_within_closure.t in
    try
      Var_within_closure.Map.iter (fun in_closure (outer_var : Free_var.t) ->
          if Variable.equal var outer_var.var then raise (Found in_closure))
        t;
      None
    with Found in_closure -> Some in_closure

  let print ppf free_vars =
    Var_within_closure.Map.iter (fun inner_var outer_var ->
        fprintf ppf "@ %a -rename-> %a"
          Var_within_closure.print inner_var
          Free_var.print outer_var)
      free_vars

  let all_outer_variables t =
    let outer_vars = Var_within_closure.Map.data t in
    Variable.Set.of_list (List.map Free_var.var outer_vars)
end

module Trap_action = struct
  type t =
    | Push of { id : Trap_id.t; exn_handler : Continuation.t; }
    | Pop of { id : Trap_id.t; exn_handler : Continuation.t; }

  include Identifiable.Make (struct
    type nonrec t = t

    let compare t1 t2 =
      match t1, t2 with
      | Push { id = id1; exn_handler = exn_handler1; },
          Push { id = id2; exn_handler = exn_handler2; } ->
        let c = Trap_id.compare id1 id2 in
        if c <> 0 then c
        else Continuation.compare exn_handler1 exn_handler2
      | Pop { id = id1; exn_handler = exn_handler1; },
          Pop { id = id2; exn_handler = exn_handler2; } ->
        let c = Trap_id.compare id1 id2 in
        if c <> 0 then c
        else Continuation.compare exn_handler1 exn_handler2
      | Push _, Pop _ -> -1
      | Pop _, Push _ -> 1

    let equal t1 t2 = (compare t1 t2 = 0)

    let hash t =
      match t with
      | Push { id; exn_handler; }
      | Pop { id; exn_handler; } ->
        Hashtbl.hash (Trap_id.hash id, Continuation.hash exn_handler)

    let print ppf t =
      match t with
      | Push { id; exn_handler; } ->
        fprintf ppf "push %a %a then "
          Trap_id.print id
          Continuation.print exn_handler
      | Pop { id; exn_handler; } ->
        fprintf ppf "pop %a %a then "
          Trap_id.print id
          Continuation.print exn_handler
  end)

  module Option = struct
    let print ppf = function
      | None -> ()
      | Some t -> print ppf t
  end
end

module Switch = struct
  type t = {
    numconsts : Targetint.Set.t;
    consts : (Targetint.t * Continuation.t) list;
    failaction : Continuation.t option;
  }

  include Identifiable.Make (struct
    type nonrec t = t

    let compare t1 t2 =
      let c = Targetint.Set.compare t1.numconsts t2.numconsts in
      if c <> 0 then c
      else
        let c =
          let compare_one (i1, k1) (i2, k2) =
            let c = Targetint.compare i1 i2 in
            if c <> 0 then c
            else Continuation.compare k1 k2
          in
          Misc.Stdlib.List.compare compare_one t1.consts t2.consts
        in
        if c <> 0 then c
        else
          Misc.Stdlib.Option.compare Continuation.compare
            t1.failaction t2.failaction

    let equal t1 t2 = (compare t1 t2 = 0)

    let hash _t = Misc.fatal_error "Not implemented"

    let print ppf (t : t) =
      let spc = ref false in
      List.iter (fun (n, l) ->
          if !spc then fprintf ppf "@ " else spc := true;
          fprintf ppf "@[<hv 1>| %a ->@ goto %a@]"
            Targetint.print n
            Continuation.print l)
        t.consts;
      begin match t.failaction with
      | None  -> ()
      | Some l ->
        if !spc then fprintf ppf "@ " else spc := true;
        let module Int = Int in
        fprintf ppf "@[<hv 1>| _ ->@ goto %a@]" Continuation.print l
      end
  end)
end

type invalid_term_semantics =
  | Treat_as_unreachable
  | Halt_and_catch_fire

type recursive =
  | Non_recursive
  | Recursive

type mutable_or_immutable =
  | Mutable
  | Immutable

module rec Expr : sig
  type t =
    | Let of Let.t
    | Let_mutable of Let_mutable.t
    | Let_cont of Let_cont.t
    | Apply of Apply.t
    | Apply_cont of Continuation.t * Trap_action.t option * Variable.t list
    | Switch of Variable.t * Switch.t
    | Invalid of invalid_term_semantics

  val create_let : Variable.t -> Flambda_kind.t -> Named.t -> t -> t
  val create_switch
     : scrutinee:Variable.t
    -> all_possible_values:Targetint.Set.t
    -> arms:(Targetint.t * Continuation.t) list
    -> default:Continuation.t option
    -> Expr.t
  val create_switch'
     : scrutinee:Variable.t
    -> all_possible_values:Targetint.Set.t
    -> arms:(Targetint.t * Continuation.t) list
    -> default:Continuation.t option
    -> Expr.t * (int Continuation.Map.t)
  val free_variables
     : ?ignore_uses_as_callee:unit
    -> ?ignore_uses_as_argument:unit
    -> ?ignore_uses_as_continuation_argument:unit
    -> ?ignore_uses_in_project_var:unit
    -> ?ignore_uses_in_apply_cont:unit
    -> t
    -> Variable.Set.t
  val free_symbols : t -> Symbol.Set.t
  val used_variables
     : ?ignore_uses_as_callee:unit
    -> ?ignore_uses_as_argument:unit
    -> ?ignore_uses_as_continuation_argument:unit
    -> ?ignore_uses_in_project_var:unit
    -> t
    -> Variable.Set.t
  val free_continuations : t -> Continuation.Set.t
  val invalid : unit -> t
  val iter_lets
     : t
    -> for_defining_expr:(Variable.t -> Flambda_kind.t -> Named.t -> unit)
    -> for_last_body:(t -> unit)
    -> for_each_let:(t -> unit)
    -> unit
  val map_lets
     : t
    -> for_defining_expr:(Variable.t -> Flambda_kind.t -> Named.t -> Named.t)
    -> for_last_body:(t -> t)
    -> after_rebuild:(t -> t)
    -> t
  type maybe_named =
    | Is_expr of t
    | Is_named of Named.t
  val iter_general
     : toplevel:bool
    -> (Expr.t -> unit)
    -> (Named.t -> unit)
    -> maybe_named
    -> unit
  val print : Format.formatter -> t -> unit
end = struct
  include Expr

  let variable_usage ?ignore_uses_as_callee
      ?ignore_uses_as_argument ?ignore_uses_as_continuation_argument
      ?ignore_uses_in_project_var ?ignore_uses_in_apply_cont
      ~all_used_variables tree =
    let free = ref Variable.Set.empty in
    let bound = ref Variable.Set.empty in
    let free_variables ids = free := Variable.Set.union ids !free in
    let free_variable fv = free := Variable.Set.add fv !free in
    let bound_variable id = bound := Variable.Set.add id !bound in
    (* N.B. This function assumes that all bound identifiers are distinct. *)
    let rec aux (flam : t) : unit =
      match flam with
      | Apply { func; args; call_kind; _ } ->
        begin match ignore_uses_as_callee with
        | None -> free_variable func
        | Some () -> ()
        end;
        begin match call_kind with
        | Direct { closure_id = _; return_arity = _; }
        | Indirect_unknown_arity
        | Indirect_known_arity { param_arity = _; return_arity = _; } -> ()
        | Method { kind = _; obj; } -> free_variable obj
        end;
        begin match ignore_uses_as_argument with
        | None -> List.iter free_variable args
        | Some () -> ()
        end
      | Let { var; free_vars_of_defining_expr; free_vars_of_body;
              defining_expr; body; _ } ->
        bound_variable var;
        if all_used_variables
            || ignore_uses_as_callee <> None
            || ignore_uses_as_argument <> None
            || ignore_uses_as_continuation_argument <> None
            || ignore_uses_in_project_var <> None
            || ignore_uses_in_apply_cont <> None
        then begin
          (* In these cases we can't benefit from the pre-computed free
             variable sets. *)
          free_variables
            (Named.variable_usage ?ignore_uses_in_project_var defining_expr);
          aux body
        end else begin
          free_variables free_vars_of_defining_expr;
          free_variables free_vars_of_body
        end
      | Let_mutable { initial_value = var; body; _ } ->
        free_variable var;
        aux body
      | Apply_cont (_, _, es) ->
        (* CR mshinwell: why two variables? *)
        begin match ignore_uses_in_apply_cont with
        | Some () -> ()
        | None ->
          match ignore_uses_as_continuation_argument with
          | None -> List.iter free_variable es
          | Some () -> ()
        end
      | Let_cont { handlers; body; } ->
        aux body;
        (* CR-soon mshinwell: Move the following into a separate function in
           the [Let_cont] module. *)
        begin match handlers with
        | Nonrecursive { name = _; handler = { Continuation_handler.
            params; handler; _ }; } ->
          List.iter (fun param -> bound_variable (Typed_parameter.var param))
            params;
          aux handler
        | Recursive handlers ->
          Continuation.Map.iter (fun _name { Continuation_handler.
            params; handler; _ } ->
              List.iter (fun param ->
                  bound_variable (Typed_parameter.var param))
                params;
              aux handler)
            handlers
        end
      | Switch (var, _) -> free_variable var
      | Invalid _ -> ()
    in
    aux tree;
    if all_used_variables then
      !free
    else
      Variable.Set.diff !free !bound

  let free_variables ?ignore_uses_as_callee ?ignore_uses_as_argument
      ?ignore_uses_as_continuation_argument ?ignore_uses_in_project_var
      ?ignore_uses_in_apply_cont tree =
    variable_usage ?ignore_uses_as_callee ?ignore_uses_as_argument
      ?ignore_uses_as_continuation_argument ?ignore_uses_in_project_var
      ?ignore_uses_in_apply_cont ~all_used_variables:false tree

  let used_variables ?ignore_uses_as_callee ?ignore_uses_as_argument
      ?ignore_uses_as_continuation_argument ?ignore_uses_in_project_var tree =
    variable_usage ?ignore_uses_as_callee ?ignore_uses_as_argument
      ?ignore_uses_as_continuation_argument ?ignore_uses_in_project_var
      ~all_used_variables:true tree

  let invalid () =
    if !Clflags.treat_invalid_code_as_unreachable then
      Invalid Treat_as_unreachable
    else
      Invalid Halt_and_catch_fire

  let create_switch' ~scrutinee ~all_possible_values ~arms ~default
        : t * (int Continuation.Map.t) =
    let result_switch : Switch.t =
      { numconsts = all_possible_values;
        consts = arms;
        failaction = default;
      }
    in
    let result : t = Switch (scrutinee, result_switch) in
    let arms =
      List.sort (fun (value1, _) (value2, _) -> Pervasives.compare value1 value2)
        arms
    in
    let num_possible_values = Targetint.Set.cardinal all_possible_values in
    let num_arms = List.length arms in
    let arm_values = List.map (fun (value, _cont) -> value) arms in
    let num_arm_values = List.length arm_values in
    let arm_values_set = Targetint.Set.of_list arm_values in
    let num_arm_values_set = Targetint.Set.cardinal arm_values_set in
    if num_arm_values <> num_arm_values_set then begin
      Misc.fatal_errorf "More than one arm of this switch matches on \
          the same value: %a"
        print result
    end;
    if num_arms > num_possible_values then begin
      Misc.fatal_errorf "This switch has too many arms: %a"
        print result
    end;
    if not (Targetint.Set.subset arm_values_set all_possible_values) then begin
      Misc.fatal_errorf "This switch matches on values that were not specified \
          in the set of all possible values: %a"
        print result
    end;
    if num_possible_values < 1 then begin
      invalid (), Continuation.Map.empty
    end else if num_arms = 0 && default = None then begin
      (* [num_possible_values] might be strictly greater than zero in this
         case, but that doesn't matter. *)
      invalid (), Continuation.Map.empty
    end else begin
      let default =
        if num_arm_values = num_possible_values then None
        else default
      in
      let single_case =
        match arms, default with
        | [_, cont], None
        | [], Some cont -> Some cont
        | arms, default ->
          let destinations =
            Continuation.Set.of_list (List.map (fun (_, cont) -> cont) arms)
          in
          assert (not (Continuation.Set.is_empty destinations));
          match Continuation.Set.elements destinations, default with
          | [cont], None -> Some cont
          | [cont], Some cont' when Continuation.equal cont cont' -> Some cont
          | _, _ -> None
      in
      match single_case with
      | Some cont ->
        Apply_cont (cont, None, []),
          Continuation.Map.add cont 1 Continuation.Map.empty
      | None ->
        let num_uses = Continuation.Tbl.create 42 in
        let add_use cont =
          match Continuation.Tbl.find num_uses cont with
          | exception Not_found -> Continuation.Tbl.add num_uses cont 1
          | num -> Continuation.Tbl.replace num_uses cont (num + 1)
        in
        List.iter (fun (_const, cont) -> add_use cont) result_switch.consts;
        begin match default with
        | None -> ()
        | Some default -> add_use default
        end;
        Switch (scrutinee, { result_switch with failaction = default; }),
          Continuation.Tbl.to_map num_uses
    end

  let create_switch ~scrutinee ~all_possible_values ~arms ~default =
    let switch, _uses =
      create_switch' ~scrutinee ~all_possible_values ~arms ~default
    in
    switch

  let rec free_continuations (t : t) =
    match t with
    | Let { body; _ }
    | Let_mutable { body; _ } ->
      (* No continuations occur in a [Named.t] except inside closures---and
         closures do not have free continuations.  As such we don't need
         to traverse the defining expression of the let. *)
      free_continuations body
    | Let_cont { body; handlers; } ->
      let free_and_bound =
        Let_cont_handlers.free_and_bound_continuations handlers
      in
      Continuation.Set.union free_and_bound.free
        (Continuation.Set.diff (free_continuations body)
          free_and_bound.bound)
    | Apply_cont (cont, trap_action, _args) ->
      let trap_action =
        match trap_action with
        | Some (Push { exn_handler; _ })
        | Some (Pop { exn_handler; _ }) ->
          Continuation.Set.singleton exn_handler
        | None -> Continuation.Set.empty
      in
      Continuation.Set.add cont trap_action
    | Apply { continuation; } -> Continuation.Set.singleton continuation
    | Switch (_scrutinee, switch) ->
      let consts = List.map (fun (_int, cont) -> cont) switch.consts in
      let failaction =
        match switch.failaction with
        | None -> Continuation.Set.empty
        | Some cont -> Continuation.Set.singleton cont
      in
      Continuation.Set.union failaction (Continuation.Set.of_list consts)
    | Invalid _ -> Continuation.Set.empty

  let create_let var kind defining_expr body : t =
    begin match !Clflags.dump_flambda_let with
    | None -> ()
    | Some stamp ->
      Variable.debug_when_stamp_matches var ~stamp ~f:(fun () ->
        Printf.eprintf "Creation of [Let] with stamp %d:\n%s\n%!"
          stamp
          (Printexc.raw_backtrace_to_string (Printexc.get_callstack max_int)))
    end;
    let free_vars_of_defining_expr = Named.free_variables defining_expr in
    Let {
      var;
      kind;
      defining_expr;
      body;
      free_vars_of_defining_expr;
      free_vars_of_body = free_variables body;
    }

  let iter_lets t ~for_defining_expr ~for_last_body ~for_each_let =
    let rec loop (t : t) =
      match t with
      | Let { var; kind; defining_expr; body; _ } ->
        for_each_let t;
        for_defining_expr var kind defining_expr;
        loop body
      | t ->
        for_last_body t
    in
    loop t

  let map_lets t ~for_defining_expr ~for_last_body ~after_rebuild =
    let rec loop (t : t) ~rev_lets =
      match t with
      | Let { var; kind; defining_expr; body; _ } ->
        let new_defining_expr = for_defining_expr var kind defining_expr in
        let original =
          if new_defining_expr == defining_expr then
            Some t
          else
            None
        in
        let rev_lets = (var, kind, new_defining_expr, original) :: rev_lets in
        loop body ~rev_lets
      | t ->
        let last_body = for_last_body t in
        (* As soon as we see a change, we have to rebuild that [Let] and every
          outer one. *)
        let seen_change = ref (not (last_body == t)) in
        List.fold_left (fun (t : t) (var, kind, defining_expr, original) : t ->
            let let_expr =
              match original with
              | Some original when not !seen_change -> original
              | Some _ | None ->
                seen_change := true;
                create_let var kind defining_expr t
            in
            let new_let = after_rebuild let_expr in
            if not (new_let == let_expr) then begin
              seen_change := true
            end;
            new_let)
          last_body
          rev_lets
    in
    loop t ~rev_lets:[]

  let iter_general ~toplevel f f_named maybe_named =
    let rec aux (t : t) =
      match t with
      | Let _ ->
        iter_lets t
          ~for_defining_expr:(fun _var _kind named -> aux_named named)
          ~for_last_body:aux
          ~for_each_let:f
      (* CR mshinwell: add tail recursive case for Let_cont *)
      | _ ->
        f t;
        match t with
        | Apply _ | Apply_cont _ | Switch _ -> ()
        | Let _ -> assert false
        | Let_mutable { body; _ } -> aux body
        | Let_cont { body; handlers; _ } ->
          aux body;
          begin match handlers with
          | Nonrecursive { name = _; handler = { handler; _ }; } ->
            aux handler
          | Recursive handlers ->
            Continuation.Map.iter (fun _cont
                  { Continuation_handler. handler; } ->
                aux handler)
              handlers
          end
        | Invalid _ -> ()
    and aux_named (named : Named.t) =
      f_named named;
      match named with
      | Var _ | Symbol _ | Const _ | Read_mutable _
      | Read_symbol_field _ | Project_closure _ | Project_var _
      | Move_within_set_of_closures _ | Prim _ | Assign _ -> ()
      | Set_of_closures { function_decls = funcs; _; } ->
        if not toplevel then begin
          Closure_id.Map.iter (fun _ (decl : Function_declaration.t) ->
              aux decl.body)
            funcs.funs
        end
    in
    match maybe_named with
    | Is_expr expr -> aux expr
    | Is_named named -> aux_named named

  let free_symbols t =
    let symbols = ref Symbol.Set.empty in
    iter_general ~toplevel:true
      (fun (_ : t) -> ())
      (fun (named : Named.t) -> Named.free_symbols_helper symbols named)
      (Is_expr t);
    !symbols

  let rec print ppf (t : t) =
    match t with
    | Apply ({ func; continuation; args; call_kind; inline; dbg; }) ->
      fprintf ppf "@[<2>(apply %a %a%a@ <%a> %a %a)@]"
        Call_kind.print call_kind
        print_inline_attribute inline
        Debuginfo.print_or_elide dbg
        Continuation.print continuation
        Variable.print func
        Variable.print_list args
    | Let { var = id; defining_expr = arg; body; _ } ->
        let rec letbody (ul : t) =
          match ul with
          | Let { var = id; defining_expr = arg; body; _ } ->
              fprintf ppf "@ @[<2>%a@ %a@]" Variable.print id Named.print arg;
              letbody body
          | _ -> ul
        in
        fprintf ppf "@[<2>(let@ @[<hv 1>(@[<2>%a@ %a@]"
          Variable.print id Named.print arg;
        let expr = letbody body in
        fprintf ppf ")@]@ %a)@]" print expr
    | Let_mutable { var = mut_var; initial_value = var; body; contents_type } ->
      fprintf ppf "@[<2>(let_mutable%a@ @[<2>%a@ %a@]@ %a)@]"
        Flambda_type.print contents_type
        Mutable_variable.print mut_var
        Variable.print var
        print body
    | Switch (scrutinee, sw) ->
      fprintf ppf
        "@[<v 1>(switch %a@ @[<v 0>%a@])@]"
        Variable.print scrutinee Switch.print sw
    | Apply_cont (i, trap_action, []) ->
      fprintf ppf "@[<2>(%agoto@ %a)@]"
        Trap_action.Option.print trap_action
        Continuation.print i
    | Apply_cont (i, trap_action, ls) ->
      fprintf ppf "@[<2>(%aapply_cont@ %a@ %a)@]"
        Trap_action.Option.print trap_action
        Continuation.print i
        Variable.print_list ls
    | Let_cont { body; handlers; } ->
      (* Printing the same way as for [Let] is easier when debugging lifting
         passes. *)
      if !Clflags.dump_let_cont then begin
        let rec let_cont_body (ul : t) =
          match ul with
          | Let_cont { body; handlers; } ->
            fprintf ppf "@ @[<2>%a@]" Let_cont_handlers.print handlers;
            let_cont_body body
          | _ -> ul
        in
        fprintf ppf "@[<2>(let_cont@ @[<hv 1>(@[<2>%a@]"
          Let_cont_handlers.print handlers;
        let expr = let_cont_body body in
        fprintf ppf ")@]@ %a)@]" print expr
      end else begin
        (* CR mshinwell: Share code with ilambda.ml *)
        let rec gather_let_conts let_conts (t : t) =
          match t with
          | Let_cont let_cont ->
            gather_let_conts (let_cont.handlers :: let_conts) let_cont.body
          | body -> let_conts, body
        in
        let let_conts, body = gather_let_conts [] t in
        let pp_sep ppf () = fprintf ppf "@ " in
        fprintf ppf "@[<2>(@[<v 0>%a@;@[<v 0>%a@]@])@]"
          Expr.print body
          (Format.pp_print_list ~pp_sep
            Let_cont_handlers.print_using_where) let_conts
      end
    | Invalid _ -> fprintf ppf "unreachable"

  let print ppf t =
    fprintf ppf "%a@." print t
end and Named : sig
  type t =
    | Var of Variable.t
    | Const of Const.t
    | Prim of Flambda_primitive.t * Debuginfo.t
    | Assign of assign
    | Read_mutable of Mutable_variable.t
    | Symbol of Symbol.t
    | Read_symbol_field of Symbol.t * int
    | Set_of_closures of Set_of_closures.t
    | Project_closure of Projection.Project_closure.t
    | Move_within_set_of_closures of Projection.Move_within_set_of_closures.t
    | Project_var of Projection.Project_var.t

  val free_variables
     : ?ignore_uses_in_project_var:unit
    -> t
    -> Variable.Set.t
  val free_symbols : t -> Symbol.Set.t
  val free_symbols_helper : Symbol.Set.t ref -> t -> unit
  val used_variables
     : ?ignore_uses_in_project_var:unit
    -> t
    -> Variable.Set.t
  val variable_usage
     : ?ignore_uses_in_project_var:unit
    -> t
    -> Variable.Set.t
  val print : Format.formatter -> t -> unit
  val box_value
      : Variable.t
     -> Flambda_kind.t
     -> Debuginfo.t
     -> Named.t * Flambda_kind.t
  val unbox_value
      : Variable.t
     -> Flambda_kind.t
     -> Debuginfo.t
     -> Named.t * Flambda_kind.t
end = struct
  include Named

  let free_symbols_helper symbols (t : t) =
    match t with
    | Symbol symbol ->
      symbols := Symbol.Set.add symbol !symbols
    | Read_symbol_field (symbol, _) ->
      symbols := Symbol.Set.add symbol !symbols
    | Set_of_closures set_of_closures ->
      Closure_id.Map.iter (fun _ (function_decl : Function_declaration.t) ->
          symbols := Symbol.Set.union function_decl.free_symbols !symbols)
        set_of_closures.function_decls.funs
    | _ -> ()

  let free_symbols t =
    let symbols = ref Symbol.Set.empty in
    Expr.iter_general ~toplevel:true
      (fun (_ : Expr.t) -> ())
      (fun (t : Named.t) -> free_symbols_helper symbols t)
      (Is_named t);
    !symbols

  let variable_usage ?ignore_uses_in_project_var (t : t) =
    match t with
    | Var var -> Variable.Set.singleton var
    | _ ->
      let free = ref Variable.Set.empty in
      let free_variable fv = free := Variable.Set.add fv !free in
      begin match t with
      | Var var -> free_variable var
      | Symbol _ | Const _ | Read_mutable _
      | Read_symbol_field _ -> ()
      | Assign { being_assigned = _; new_value; } ->
        free_variable new_value
      | Set_of_closures { free_vars; _ } ->
        (* Sets of closures are, well, closed---except for the free variable and
           specialised argument lists, which may identify variables currently in
           scope outside of the closure. *)
        Var_within_closure.Map.iter (fun _ (renamed_to : Free_var.t) ->
            (* We don't need to do anything with [renamed_to.projectee.var], if
               it is present, since it would only be another free variable
               in the same set of closures. *)
            free_variable renamed_to.var)
          free_vars
      | Project_closure { set_of_closures; closure_id = _ } ->
        free_variable set_of_closures
      | Project_var { closure; var = _ } ->
        begin match ignore_uses_in_project_var with
        | None -> free_variable closure
        | Some () -> ()
        end
      | Move_within_set_of_closures { closure; move = _ } ->
        free_variable closure
      | Prim (Unary (_prim, x0), _dbg) ->
        free_variable x0
      | Prim (Binary (_prim, x0, x1), _dbg) ->
        free_variable x0;
        free_variable x1
      | Prim (Ternary (_prim, x0, x1, x2), _dbg) ->
        free_variable x0;
        free_variable x1;
        free_variable x2
      | Prim (Variadic (_prim, xs), _dbg) ->
        List.iter free_variable xs
      end;
      !free

  let free_variables ?ignore_uses_in_project_var t =
    variable_usage ?ignore_uses_in_project_var t

  let used_variables ?ignore_uses_in_project_var named =
    variable_usage ?ignore_uses_in_project_var named

  let print ppf (t : t) =
    match t with
    | Var var -> Variable.print ppf var
    | Symbol symbol -> Symbol.print ppf symbol
    | Const cst -> fprintf ppf "Const(%a)" Const.print cst
    | Read_mutable mut_var ->
      fprintf ppf "Read_mut(%a)" Mutable_variable.print mut_var
    | Assign { being_assigned; new_value; } ->
      fprintf ppf "@[<2>(assign@ %a@ %a)@]"
        Mutable_variable.print being_assigned
        Variable.print new_value
    | Read_symbol_field (symbol, field) ->
      fprintf ppf "%a.(%d)" Symbol.print symbol field
    | Project_closure project_closure ->
      Projection.Project_closure.print ppf project_closure
    | Project_var project_var ->
      Projection.Project_var.print ppf project_var
    | Move_within_set_of_closures move_within_set_of_closures ->
      Projection.Move_within_set_of_closures.print ppf
        move_within_set_of_closures
    | Set_of_closures set_of_closures ->
      Set_of_closures.print ppf set_of_closures
    | Prim (prim, dbg) ->
      fprintf ppf "@[<2>(%a@ %a)@]"
        Flambda_primitive.print prim
        Debuginfo.print_or_elide dbg

  let box_value var (kind : Flambda_kind.t) dbg : Named.t * Flambda_kind.t =
    match kind with
    | Value _ -> Var var, kind
    | Naked_immediate ->
      Misc.fatal_error "Not yet supported"
    | Naked_float ->
      Prim (Unary (Box_number Naked_float, var), dbg), K.value Must_scan
    | Naked_int32 ->
      Prim (Unary (Box_number Naked_int32, var), dbg), K.value Must_scan
    | Naked_int64 ->
      Prim (Unary (Box_number Naked_int64, var), dbg), K.value Must_scan
    | Naked_nativeint ->
      Prim (Unary (Box_number Naked_nativeint, var), dbg), K.value Must_scan

  let unbox_value var (kind : Flambda_kind.t) dbg : Named.t * Flambda_kind.t =
    match kind with
    | Value _ -> Var var, kind
    | Naked_immediate ->
      Misc.fatal_error "Not yet supported"
    | Naked_float ->
      Prim (Unary (Unbox_number Naked_float, var), dbg), K.naked_float ()
    | Naked_int32 ->
      Prim (Unary (Unbox_number Naked_int32, var), dbg), K.naked_int32 ()
    | Naked_int64 ->
      Prim (Unary (Unbox_number Naked_int64, var), dbg), K.naked_int64 ()
    | Naked_nativeint ->
      Prim (Unary (Unbox_number Naked_nativeint, var), dbg),
        K.naked_nativeint ()
end and Let : sig
  type t = {
    var : Variable.t;
    kind : Flambda_kind.t;
    defining_expr : Named.t;
    body : Expr.t;
    free_vars_of_defining_expr : Variable.Set.t;
    free_vars_of_body : Variable.Set.t;
  }

  val map_defining_expr : Let.t -> f:(Named.t -> Named.t) -> Expr.t
end = struct
  include Let

  let map_defining_expr (let_expr : Let.t) ~f : Expr.t =
    let defining_expr = f let_expr.defining_expr in
    if defining_expr == let_expr.defining_expr then
      Let let_expr
    else
      let free_vars_of_defining_expr =
        Named.free_variables defining_expr
      in
      Let {
        var = let_expr.var;
        kind = let_expr.kind;
        defining_expr;
        body = let_expr.body;
        free_vars_of_defining_expr;
        free_vars_of_body = let_expr.free_vars_of_body;
      }
end and Let_mutable : sig
  type t = {
    var : Mutable_variable.t;
    initial_value : Variable.t;
    contents_type : Flambda_type.t;
    body : Expr.t;
  }
end = struct
  include Let_mutable
end and Let_cont : sig
  type t = {
    body : Expr.t;
    handlers : Let_cont_handlers.t;
  }
end = struct
  include Let_cont
end and Let_cont_handlers : sig
  type t =
    | Nonrecursive of {
        name : Continuation.t;
        handler : Continuation_handler.t;
      }
    | Recursive of Continuation_handlers.t

  val free_variables : t -> Variable.Set.t
  val bound_continuations : t -> Continuation.Set.t
  val free_continuations : t -> Continuation.Set.t
  type free_and_bound = {
    free : Continuation.Set.t;
    bound : Continuation.Set.t;
  }
  val free_and_bound_continuations : t -> free_and_bound
  val to_continuation_map : t -> Continuation_handlers.t
  val map : t -> f:(Continuation_handlers.t -> Continuation_handlers.t) -> t
  val print : Format.formatter -> t -> unit
  val print_using_where : Format.formatter -> t -> unit
end = struct
  include Let_cont_handlers

  let to_continuation_map t =
    match t with
    | Nonrecursive { name; handler } -> Continuation.Map.singleton name handler
    | Recursive handlers -> handlers

  let free_and_bound_continuations (t : t) : free_and_bound =
    match t with
    | Nonrecursive { name; handler = { handler; _ }; } ->
      let fcs = Expr.free_continuations handler in
      if Continuation.Set.mem name fcs then begin
        Misc.fatal_errorf "Nonrecursive [Let_cont] handler appears to be \
            recursive:@ \n%a"
          print t
      end;
      { free = fcs;
        bound = Continuation.Set.singleton name;
      }
    | Recursive handlers ->
      let bound_conts = Continuation.Map.keys handlers in
      let fcs =
        Continuation.Map.fold (fun _name
              { Continuation_handler. handler; _ } fcs ->
            Continuation.Set.union fcs
              (Continuation.Set.diff (Expr.free_continuations handler)
                bound_conts))
          handlers
          Continuation.Set.empty
      in
      { free = fcs;
        bound = bound_conts;
      }

  let free_continuations t = (free_and_bound_continuations t).free
  let bound_continuations t = (free_and_bound_continuations t).bound

  let free_variables (t : t) =
    Continuation.Map.fold (fun _name
          { Continuation_handler. params; handler; _ } fvs ->
        Variable.Set.union fvs
          (Variable.Set.union
            (Typed_parameter.List.free_variables params)
            (Variable.Set.diff (Expr.free_variables handler)
              (Typed_parameter.List.var_set params))))
      (to_continuation_map t)
      Variable.Set.empty

  let map (t : t) ~f =
    match t with
    | Nonrecursive { name; handler } ->
      let handlers = f (Continuation.Map.singleton name handler) in
      begin match Continuation.Map.bindings handlers with
      | [ name, handler ] -> Nonrecursive { name; handler; }
      | _ ->
        Misc.fatal_errorf "Flambda.map: the provided mapping function \
          returned more than one handler for a [Nonrecursive] binding"
      end
    | Recursive handlers -> Recursive (f handlers)

  let print_using_where ppf (t : t) =
    match t with
    | Nonrecursive { name; handler = { params; stub; handler; }; } ->
      fprintf ppf "@[<v 2>where %a%s%s@[%a@]%s =@ %a@]"
        Continuation.print name
        (if stub then " *stub*" else "")
        (match params with [] -> "" | _ -> " (")
        Typed_parameter.List.print params
        (match params with [] -> "" | _ -> ")")
        Expr.print handler
    | Recursive handlers ->
      let first = ref true in
      fprintf ppf "@[<v 2>where rec ";
      Continuation.Map.iter (fun name
              { Continuation_handler. params; stub; is_exn_handler;
                handler; } ->
          if not !first then fprintf ppf "@ ";
          fprintf ppf "@[%s%a%s%s%s@[%a@]%s@] =@ %a"
            (if !first then "" else "and ")
            Continuation.print name
            (if stub then " *stub*" else "")
            (if is_exn_handler then "*exn* " else "")
            (match params with [] -> "" | _ -> " (")
            Typed_parameter.List.print params
            (match params with [] -> "" | _ -> ")")
            Expr.print handler;
          first := false)
        handlers;
      fprintf ppf "@]"

  let print ppf (t : t) =
    match t with
    | Nonrecursive { name; handler = {
        params; stub; handler; }; } ->
      fprintf ppf "%a@ %s%s%a%s=@ %a"
        Continuation.print name
        (if stub then "*stub* " else "")
        (match params with [] -> "" | _ -> "(")
        Typed_parameter.List.print params
        (match params with [] -> "" | _ -> ") ")
        Expr.print handler
    | Recursive handlers ->
      let first = ref true in
      Continuation.Map.iter (fun name
              { Continuation_handler.params; stub; is_exn_handler; handler; } ->
          if !first then begin
            fprintf ppf "@;rec "
          end else begin
            fprintf ppf "@;and "
          end;
          fprintf ppf "%a@ %s%s%s%a%s=@ %a"
            Continuation.print name
            (if stub then "*stub* " else "")
            (if is_exn_handler then "*exn* " else "")
            (match params with [] -> "" | _ -> "(")
            Typed_parameter.List.print params
            (match params with [] -> "" | _ -> ") ")
            Expr.print handler;
          first := false)
        handlers
end and Continuation_handlers : sig
  type t = Continuation_handler.t Continuation.Map.t
end = struct
  include Continuation_handlers
end and Continuation_handler : sig
  type t = {
    params : Typed_parameter.t list;
    stub : bool;
    is_exn_handler : bool;
    handler : Expr.t;
  }
end = struct
  include Continuation_handler
end and Set_of_closures : sig
  type t = {
    function_decls : Function_declarations.t;
    free_vars : Free_vars.t;
    direct_call_surrogates : Closure_id.t Closure_id.Map.t;
  }

  val create
     : function_decls:Function_declarations.t
    -> free_vars:Free_vars.t
    -> direct_call_surrogates:Closure_id.t Closure_id.Map.t
    -> t
  val has_empty_environment : t -> bool
  val print : Format.formatter -> t -> unit
end = struct
  include Set_of_closures

  let create ~(function_decls : Function_declarations.t) ~free_vars
        ~direct_call_surrogates =
    (* CR pchambart: there is nothing to check about free vars anymore. *)
    (*
    if !Clflags.flambda_invariant_checks then begin
      let all_fun_vars = Closure_id.Map.keys function_decls.funs in
      let expected_free_vars =
        Variable.Map.fold (fun _fun_var (function_decl : Function_declaration.t)
                  expected_free_vars ->
            let free_vars =
              Variable.Set.diff function_decl.free_variables
                (Variable.Set.union
                  (Typed_parameter.List.var_set function_decl.params)
                  all_fun_vars)
            in
            Variable.Set.union free_vars expected_free_vars)
          function_decls.funs
          Variable.Set.empty
      in
      (* CR-soon pchambart: We do not seem to be able to maintain the
         invariant that if a variable is not used inside the closure, it
         is not used outside either. This would be a nice property for
         better dead code elimination during inline_and_simplify, but it
         is not obvious how to ensure that.
 
         This would be true when the function is known never to have
         been inlined.
 
         Note that something like that may maybe enforcable in
         inline_and_simplify, but there is no way to do that on other
         passes.
 
         mshinwell: see CR in Flambda_invariants about this too
      *)
      let free_vars_domain = Closure_id.Map.keys free_vars in
      if not (Variable.Set.subset expected_free_vars free_vars_domain) then begin
        Misc.fatal_errorf "Set_of_closures.create: [free_vars] mapping of \
            variables bound by the closure(s) is wrong.  (Must map at least \
            %a but only maps %a.)@ \nfunction_decls:@ %a"
          Variable.Set.print expected_free_vars
          Variable.Set.print free_vars_domain
          Function_declarations.print function_decls
      end
    end;
    *)
    { function_decls;
      free_vars;
      direct_call_surrogates;
    }

  let has_empty_environment t =
    Var_within_closure.Map.is_empty t.free_vars

  let print ppf t =
    match t with
    | { function_decls; free_vars; } ->
      let funs ppf t =
        Closure_id.Map.iter (fun var decl ->
            Function_declaration.print var ppf decl)
          t
      in
      fprintf ppf "@[<2>(set_of_closures id=%a@ %a@ @[<2>free_vars={%a@ }@]@ \
          @[<2>direct_call_surrogates=%a@]@ \
          @[<2>set_of_closures_origin=%a@]@]"
        Set_of_closures_id.print function_decls.set_of_closures_id
        funs function_decls.funs
        Free_vars.print free_vars
        (Closure_id.Map.print Closure_id.print) t.direct_call_surrogates
        Set_of_closures_origin.print function_decls.set_of_closures_origin
end and Function_declarations : sig
  type t = {
    set_of_closures_id : Set_of_closures_id.t;
    set_of_closures_origin : Set_of_closures_origin.t;
    funs : Function_declaration.t Closure_id.Map.t;
  }

  val create : funs:Function_declaration.t Closure_id.Map.t -> t
  val find : Closure_id.t -> t -> Function_declaration.t
  val update : t -> funs:Function_declaration.t Closure_id.Map.t -> t
  val import_for_pack
     : t
    -> (Set_of_closures_id.t -> Set_of_closures_id.t)
    -> (Set_of_closures_origin.t -> Set_of_closures_origin.t)
    -> t
  val print : Format.formatter -> t -> unit
end = struct
  include Function_declarations

  let create ~funs =
    let compilation_unit = Compilation_unit.get_current_exn () in
    let set_of_closures_id = Set_of_closures_id.create compilation_unit in
    let set_of_closures_origin =
      Set_of_closures_origin.create set_of_closures_id
    in
    { set_of_closures_id;
      set_of_closures_origin;
      funs;
    }

  let find cf ({ funs } : t) =
    Closure_id.Map.find cf funs

  let update function_decls ~funs =
    let compilation_unit = Compilation_unit.get_current_exn () in
    let set_of_closures_id = Set_of_closures_id.create compilation_unit in
    let set_of_closures_origin = function_decls.set_of_closures_origin in
    { set_of_closures_id;
      set_of_closures_origin;
      funs;
    }

  let import_for_pack function_decls
        import_set_of_closures_id import_set_of_closures_origin =
    { set_of_closures_id =
        import_set_of_closures_id function_decls.set_of_closures_id;
      set_of_closures_origin =
        import_set_of_closures_origin function_decls.set_of_closures_origin;
      funs = function_decls.funs;
    }

  let print ppf (t : t) =
    let funs ppf t =
      Closure_id.Map.iter (fun var decl ->
          Function_declaration.print var ppf decl)
        t
    in
    fprintf ppf "@[<2>(%a)(origin = %a)@]" funs t.funs
      Set_of_closures_origin.print t.set_of_closures_origin
end and Function_declaration : sig
  type t = {
    closure_origin : Closure_origin.t;
    continuation_param : Continuation.t;
    return_arity : Flambda_arity.t;
    params : Typed_parameter.t list;
    body : Expr.t;
    free_symbols : Symbol.Set.t;
    stub : bool;
    dbg : Debuginfo.t;
    inline : inline_attribute;
    specialise : specialise_attribute;
    is_a_functor : bool;
    my_closure : Variable.t;
  }

  val create
     : params:Typed_parameter.t list
    -> continuation_param:Continuation.t
    -> return_arity:Flambda_arity.t
    -> my_closure:Variable.t
    -> body:Expr.t
    -> stub:bool
    -> dbg:Debuginfo.t
    -> inline:inline_attribute
    -> specialise:specialise_attribute
    -> is_a_functor:bool
    -> closure_origin:Closure_origin.t
    -> t
  val update_body : t -> body:Expr.t -> t
  val update_params : t -> params:Typed_parameter.t list -> t
  val update_params_and_body
    : t
    -> params:Typed_parameter.t list
    -> body:Expr.t
    -> t
  val used_params : t -> Variable.Set.t
  val print : Closure_id.t -> Format.formatter -> t -> unit
end = struct
  include Function_declaration

  let create ~params ~continuation_param ~return_arity ~my_closure
        ~body ~stub ~dbg
        ~(inline : inline_attribute)
        ~(specialise : specialise_attribute) ~is_a_functor
        ~closure_origin : t =
    begin match stub, inline with
    | true, (Never_inline | Default_inline)
    | false, (Never_inline | Default_inline | Always_inline | Unroll _) -> ()
    | true, (Always_inline | Unroll _) ->
      Misc.fatal_errorf
        "Stubs may not be annotated as [Always_inline] or [Unroll]: %a"
        Expr.print body
    end;
    begin match stub, specialise with
    | true, (Never_specialise | Default_specialise)
    | false, (Never_specialise | Default_specialise | Always_specialise) -> ()
    | true, Always_specialise ->
      Misc.fatal_errorf
        "Stubs may not be annotated as [Always_specialise]: %a"
        Expr.print body
    end;
    { closure_origin;
      params;
      continuation_param;
      return_arity;
      body;
      free_symbols = Expr.free_symbols body;
      stub;
      dbg;
      inline;
      specialise;
      is_a_functor;
      my_closure;
    }

  let update_body (t : t) ~body : t =
    { closure_origin = t.closure_origin;
      params = t.params;
      continuation_param = t.continuation_param;
      return_arity = t.return_arity;
      body;
      free_symbols = Expr.free_symbols body;
      stub = t.stub;
      dbg = t.dbg;
      inline = t.inline;
      specialise = t.specialise;
      is_a_functor = t.is_a_functor;
      my_closure = t.my_closure
    }

  let update_params_and_body (t : t) ~params ~body : t =
    { closure_origin = t.closure_origin;
      params;
      continuation_param = t.continuation_param;
      return_arity = t.return_arity;
      body;
      free_symbols = Expr.free_symbols body;
      stub = t.stub;
      dbg = t.dbg;
      inline = t.inline;
      specialise = t.specialise;
      is_a_functor = t.is_a_functor;
      my_closure = t.my_closure; (* Updating that field is probably needed also *)
    }

  let update_params t ~params =
    update_params_and_body t ~params ~body:t.body

  let used_params (function_decl : Function_declaration.t) =
    Variable.Set.filter (fun param ->
        Variable.Set.mem param (Expr.free_variables function_decl.body))
      (Typed_parameter.List.var_set function_decl.params)

  let print closure_id ppf (f : t) =
    let stub =
      if f.stub then
        " *stub*"
      else
        ""
    in
    let is_a_functor =
      if f.is_a_functor then
        " *functor*"
      else
        ""
    in
    let inline =
      match f.inline with
      | Always_inline -> " *inline*"
      | Never_inline -> " *never_inline*"
      | Unroll _ -> " *unroll*"
      | Default_inline -> ""
    in
    let specialise =
      match f.specialise with
      | Always_specialise -> " *specialise*"
      | Never_specialise -> " *never_specialise*"
      | Default_specialise -> ""
    in
    fprintf ppf
      "@[<2>(%a%s( return arity %a)%s%s%s(origin %a)@ =@ \
        fun@[<2> <%a>%a@] ->@ @[<2>%a@])@]@ "
      Closure_id.print closure_id
      stub
      Flambda_arity.print f.return_arity
      is_a_functor inline specialise
      Closure_origin.print f.closure_origin
      Continuation.print f.continuation_param
      Typed_parameter.List.print f.params
      Expr.print f.body
end and Typed_parameter : sig
  type t
  val create : Parameter.t -> Flambda_type.t -> t
  val var : t -> Variable.t
  val projection : t -> Projection.t option
  val ty : t -> Flambda_type.t
  val with_type : t -> Flambda_type.t -> t
  val with_projection : t -> Projection.t option -> t
  val map_var : t -> f:(Variable.t -> Variable.t) -> t
  val map_type : t -> f:(Flambda_type.t -> Flambda_type.t) -> t
  val free_variables : t -> Variable.Set.t
  module List : sig
    type nonrec t = t list
    val vars : t -> Variable.t list
    val var_set : t -> Variable.Set.t
    val equal_vars : t -> Variable.t list -> bool
    val rename : t -> t
    val arity : (t -> Flambda_kind.t list) Flambda_type.with_importer
    val free_variables : t -> Variable.Set.t
    val print : Format.formatter -> t -> unit
  end
(*  include Identifiable.S with type t := t *)
  val print : Format.formatter -> t -> unit
end = struct
  type t = {
    param : Parameter.t;
    projection : Projection.t option;
    ty : Flambda_type.t;
  }

  let create param ty =
    { param;
      projection = None;
      ty;
    }

  let var t = Parameter.var t.param
  let projection t = t.projection
  let ty t = t.ty

  let with_type t ty = { t with ty; }
  let with_projection t projection = { t with projection; } 

  let rename t = { t with param = Parameter.rename t.param; }

  let map_var t ~f = { t with param = Parameter.map_var f t.param; }

  let map_type t ~f = { t with ty = f t.ty; }

  let free_variables t =
    (* The variable within [t] is always presumed to be a binding
       occurrence, so the only free variables are those within the
       projection (if such exists) and the type. *)
    let from_proj =
      match t.projection with
      | None -> Variable.Set.empty
      | Some projection -> Projection.free_variables projection
    in
    Variable.Set.union (Flambda_type.free_variables t.ty) from_proj

(*
  include Identifiable.Make (struct
    type nonrec t = t

    let compare { param = param1; projection = projection1; ty = ty1; }
          { param = param2; projection = projection2; ty = ty2; } =
      let c = Parameter.compare param1 param2 in
      if c <> 0 then c
      else
        let c = Projection.compare projection1 projection2 in
        if c <> 0 then c
        else
          Flambda_type.compare ...

    let equal t1 t2 = (compare t1 t2 = 0)

    let hash t =

  end)
*)

  let print ppf { param; projection; ty; } =
    let print_projection ppf proj =
      match proj with
      | None -> ()
      | Some proj -> Format.fprintf ppf " = %a" Projection.print proj
    in
    Format.fprintf ppf "@[(%a : %a%a)@]"
      Parameter.print param
      Flambda_type.print ty
      print_projection projection

  module List = struct
    type nonrec t = t list

    let free_variables t =
      Variable.Set.union_list (List.map free_variables t)

    let vars t = List.map var t

    let equal_vars t1 t2 =
      List.length t1 = List.length t2
        && List.for_all2 (fun param1 var2 -> Variable.equal (var param1) var2)
             t1 t2

    let var_set t = Variable.Set.of_list (vars t)

    let rename t = List.map (fun t -> rename t) t

    let arity ~importer t =
      List.map (fun t -> Flambda_type.kind ~importer (ty t)) t

    let print ppf t =
      Format.pp_print_list ~pp_sep:Format.pp_print_space print ppf t
  end
end and Flambda_type : sig
  include Flambda_type0_intf.S with type expr := Expr.t
end = Flambda_type0.Make (Expr)

module With_free_variables = struct
  type 'a t =
    | Expr : Expr.t * Variable.Set.t -> Expr.t t
    | Named : Flambda_kind.t * Named.t * Variable.Set.t -> Named.t t

  let print (type a) ppf (t : a t) =
    match t with
    | Expr (expr, _) -> Expr.print ppf expr
    | Named (_, named, _) -> Named.print ppf named

  let of_defining_expr_of_let (let_expr : Let.t) =
    Named (let_expr.kind, let_expr.defining_expr,
      let_expr.free_vars_of_defining_expr)

  let of_body_of_let (let_expr : Let.t) =
    Expr (let_expr.body, let_expr.free_vars_of_body)

  let of_expr expr =
    Expr (expr, Expr.free_variables expr)

  let of_named kind named =
    Named (kind, named, Named.free_variables named)

  let to_named (t : Named.t t) =
    match t with
    | Named (_, named, _) -> named

  let create_let_reusing_defining_expr var (t : Named.t t) body : Expr.t =
    match t with
    | Named (kind, defining_expr, free_vars_of_defining_expr) ->
      Let {
        var;
        kind;
        defining_expr;
        body;
        free_vars_of_defining_expr;
        free_vars_of_body = Expr.free_variables body;
      }

  let create_let_reusing_body var kind defining_expr (t : Expr.t t) : Expr.t =
    match t with
    | Expr (body, free_vars_of_body) ->
      Let {
        var;
        kind;
        defining_expr;
        body;
        free_vars_of_defining_expr = Named.free_variables defining_expr;
        free_vars_of_body;
      }

  let create_let_reusing_both var (t1 : Named.t t) (t2 : Expr.t t) : Expr.t =
    match t1, t2 with
    | Named (kind, defining_expr, free_vars_of_defining_expr),
        Expr (body, free_vars_of_body) ->
      Let {
        var;
        kind;
        defining_expr;
        body;
        free_vars_of_defining_expr;
        free_vars_of_body;
      }

  let contents (type a) (t : a t) : a =
    match t with
    | Expr (expr, _) -> expr
    | Named (_, named, _) -> named

  let free_variables (type a) (t : a t) =
    match t with
    | Expr (_, free_vars) -> free_vars
    | Named (_, _, free_vars) -> free_vars
end
