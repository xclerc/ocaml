(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2016 OCamlPro SAS                                    *)
(*   Copyright 2014--2016 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module Int = Numbers.Int

let fprintf = Format.fprintf

type call_kind =
  | Indirect
  | Direct of {
      closure_id : Closure_id.t;
      return_arity : int;
    }

module Const = struct
  type t =
    | Int of int
    | Char of char
    | Const_pointer of int

  include Identifiable.Make (struct
    type nonrec t = t

    let compare = Pervasives.compare
    let equal t1 t2 = (compare t1 t2) = 0
    let hash = Hashtbl.hash

    let print ppf (t : t) =
      match t with
      | Int n -> Format.fprintf ppf "%i" n
      | Char c -> Format.fprintf ppf "%C" c
      | Const_pointer n -> Format.fprintf ppf "%ia" n

    let output _ _ = Misc.fatal_error "Not implemented"
  end)
end

type const = Const.t

type apply_kind =
  | Function
  | Method of { kind : Lambda.meth_kind; obj : Variable.t; }

type apply = {
  kind : apply_kind;
  func : Variable.t;
  continuation : Continuation.t;
  args : Variable.t list;
  call_kind : call_kind;
  dbg : Debuginfo.t;
  inline : Lambda.inline_attribute;
  specialise : Lambda.specialise_attribute;
}

type assign = {
  being_assigned : Mutable_variable.t;
  new_value : Variable.t;
}

module Free_var : sig
  type t = {
    var : Variable.t;
    projection : Projection.t option;
  }

  include Identifiable.S with type t := t
end = struct
  include Free_var

  let compare (free_var1 : t) (free_var2 : t) =
    let c = Variable.compare free_var1.var free_var2.var in
    if c <> 0 then c
    else
      match free_var1.projection, free_var2.projection with
      | None, None -> 0
      | Some _, None -> 1
      | None, Some _ -> -1
      | Some proj1, Some proj2 -> Projection.compare proj1 proj2

  let equal (free_var1 : free_var) (free_var2 : free_var) =
    compare free_var1 free_var2 = 0

  let print ppf (free_var : free_var) =
    match free_var.projection with
    | None ->
      fprintf ppf "%a" Variable.print free_var.var
    | Some projection ->
      fprintf ppf "%a(= %a)"
        Variable.print free_var.var
        Projection.print projection
end

module Free_vars = struct
  type t = Free_var.t Variable.Map.t

  let print ppf free_vars =
    Variable.Map.iter (fun id v ->
        fprintf ppf "@ %a -rename-> %a"
          Variable.print id print_free_var v)
      free_vars
end

module Trap_action = struct
  type t =
    | Push of { id : Trap_id.t; exn_handler : Continuation.t; }
    | Pop of { id : Trap_id.t; exn_handler : Continuation.t; }

  let print ppf t =
    match t with
    | None -> ()
    | Some (Push { id; exn_handler; }) ->
      fprintf ppf "push %a %a then " Trap_id.print id
        Continuation.print exn_handler
    | Some (Pop { id; exn_handler; }) ->
      fprintf ppf "pop %a %a then " Trap_id.print id
        Continuation.print exn_handler
        (Format.pp_print_list ~pp_sep print_let_cont) let_conts
      end
    | Proved_unreachable -> fprintf ppf "unreachable"
end

module Switch = struct
  type t = {
    numconsts : Numbers.Int.Set.t;
    consts : (int * Continuation.t) list;
    failaction : Continuation.t option;
  }

  let print ppf (t : t) =
    let spc = ref false in
    List.iter
      (fun (n, l) ->
          if !spc then fprintf ppf "@ " else spc := true;
          fprintf ppf "@[<hv 1>| %i ->@ goto %a@]"
            n Continuation.print l)
      sw.consts;
    begin match sw.failaction with
    | None  -> ()
    | Some l ->
        if !spc then fprintf ppf "@ " else spc := true;
        let module Int = Int in
        fprintf ppf "@[<hv 1>| _ ->@ goto %a@]"
          Continuation.print l
    end
end

module rec Expr : sig
  type t =
    | Let of let_expr
    | Let_mutable of let_mutable
    | Let_cont of let_cont
    | Apply of apply
    | Apply_cont of Continuation.t * trap_action option * Variable.t list
    | Switch of Variable.t * switch
    | Proved_unreachable

  val create_let : Variable.t -> Named.t -> t -> t
  val create_switch
     : scrutinee:Variable.t
    -> all_possible_values:Numbers.Int.Set.t
    -> arms:(int * Continuation.t) list
    -> default:Continuation.t option
    -> Expr.t
  val create_switch'
     : scrutinee:Variable.t
    -> all_possible_values:Numbers.Int.Set.t
    -> arms:(int * Continuation.t) list
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
  val print : Format.formatter -> t -> unit
end = struct
  include Expr

  let rec variable_usage ?ignore_uses_as_callee
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
      | Apply { func; args; kind; _ } ->
        begin match ignore_uses_as_callee with
        | None -> free_variable func
        | Some () -> ()
        end;
        begin match kind with
        | Function -> ()
        | Method { obj; _ } -> free_variable obj
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
            (variable_usage_named ?ignore_uses_in_project_var defining_expr);
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
        begin match handlers with
        | Nonrecursive { name = _; handler = {
            params; handler; specialised_args; _ }; } ->
          List.iter (fun param -> bound_variable (Parameter.var param)) params;
          free_variables
            (free_variables_of_specialised_args specialised_args);
          aux handler
        | Recursive handlers ->
          Continuation.Map.iter (fun _name { params; handler;
                  specialised_args; _ } ->
              List.iter (fun param -> bound_variable (Parameter.var param))
                params;
              free_variables
                (free_variables_of_specialised_args specialised_args);
              aux handler)
            handlers
        end
      | Switch (var, _) -> free_variable var
      | Proved_unreachable -> ()
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

  let create_switch' ~scrutinee ~all_possible_values ~arms ~default
        : expr * (int Continuation.Map.t) =
    let result_switch : switch =
      { numconsts = all_possible_values;
        consts = arms;
        failaction = default;
      }
    in
    let result : expr = Switch (scrutinee, result_switch) in
    let arms =
      List.sort (fun (value1, _) (value2, _) -> Pervasives.compare value1 value2)
        arms
    in
    let num_possible_values = Int.Set.cardinal all_possible_values in
    let num_arms = List.length arms in
    let arm_values = List.map (fun (value, _cont) -> value) arms in
    let num_arm_values = List.length arm_values in
    let arm_values_set = Int.Set.of_list arm_values in
    let num_arm_values_set = Int.Set.cardinal arm_values_set in
    if num_arm_values <> num_arm_values_set then begin
      Misc.fatal_errorf "More than one arm of this switch matches on \
          the same value: %a"
        print result
    end;
    if num_arms > num_possible_values then begin
      Misc.fatal_errorf "This switch has too many arms: %a"
        print result
    end;
    if not (Int.Set.subset arm_values_set all_possible_values) then begin
      Misc.fatal_errorf "This switch matches on values that were not specified \
          in the set of all possible values: %a"
        print result
    end;
    if num_possible_values < 1 then begin
      Proved_unreachable, Continuation.Map.empty
    end else if num_arms = 0 && default = None then begin
      (* [num_possible_values] might be strictly greater than zero in this
         case, but that doesn't matter. *)
      Proved_unreachable, Continuation.Map.empty
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

  let rec free_continuations (expr : expr) =
    match expr with
    | Let { body; _ }
    | Let_mutable { body; _ } ->
      (* No continuations occur in a [Named.t] except inside closures---and
         closures do not have free continuations.  As such we don't need
         to traverse the defining expression of the let. *)
      free_continuations body
    | Let_cont { body; handlers; } ->
      let fcs_handlers, bound_conts =
        Let_cont_handlers.free_continuations' ~handlers
      in
      Continuation.Set.union fcs_handlers
      (Continuation.Set.diff (free_continuations body) bound_conts)
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
    | Proved_unreachable -> Continuation.Set.empty

  let create_let var defining_expr body : t =
    begin match !Clflags.dump_flambda_let with
    | None -> ()
    | Some stamp ->
      Variable.debug_when_stamp_matches var ~stamp ~f:(fun () ->
        Printf.eprintf "Creation of [Let] with stamp %d:\n%s\n%!"
          stamp
          (Printexc.raw_backtrace_to_string (Printexc.get_callstack max_int)))
    end;
    let free_vars_of_defining_expr = free_variables_named defining_expr in
    Let {
      var;
      defining_expr;
      body;
      free_vars_of_defining_expr;
      free_vars_of_body = free_variables body;
    }

  let map_defining_expr_of_let let_expr ~f : t =
    let defining_expr = f let_expr.defining_expr in
    if defining_expr == let_expr.defining_expr then
      Let let_expr
    else
      let free_vars_of_defining_expr =
        free_variables_named defining_expr
      in
      Let {
        var = let_expr.var;
        defining_expr;
        body = let_expr.body;
        free_vars_of_defining_expr;
        free_vars_of_body = let_expr.free_vars_of_body;
      }

  let free_symbols expr =
    let symbols = ref Symbol.Set.empty in
    iter_general ~toplevel:true
      (fun (_ : t) -> ())
      (fun (named : Named.t) -> Named.free_symbols_helper symbols named)
      (Is_expr expr);
    !symbols

  let rec print ppf (fprint : t) =
    match fprint with
    | Apply({kind; func; continuation; args; call_kind; inline;
        dbg}) ->
      let print_func_and_kind ppf func =
        match kind with
        | Function -> Variable.print ppf func
        | Method { kind; obj; } ->
          Format.fprintf ppf "send%a %a#%a"
            Printlambda.meth_kind kind
            Variable.print obj
            Variable.print func
      in
      let direct ppf () =
        match call_kind with
        | Indirect -> ()
        | Direct { closure_id; _ } ->
          fprintf ppf "*[%a]" Closure_id.print closure_id
      in
      let inline ppf () =
        match inline with
        | Always_inline -> fprintf ppf "<always>"
        | Never_inline -> fprintf ppf "<never>"
        | Unroll i -> fprintf ppf "<unroll %i>" i
        | Default_inline -> ()
      in
      let return_arity =
        match call_kind with
        | Indirect -> ""
        | Direct { return_arity; _ } ->
          if return_arity < 2 then ""
          else Printf.sprintf " (return arity %d)" return_arity
      in
      fprintf ppf "@[<2>(apply%a%a<%s>%s@ <%a> %a %a)@]" direct () inline ()
        (Debuginfo.to_string dbg)
        return_arity
        Continuation.print continuation
        print_func_and_kind func
        Variable.print_list args
    | Let { var = id; defining_expr = arg; body; _ } ->
        let rec letbody (ul : t) =
          match ul with
          | Let { var = id; defining_expr = arg; body; _ } ->
              fprintf ppf "@ @[<2>%a@ %a@]" Variable.print id print_named arg;
              letbody body
          | _ -> ul
        in
        fprintf ppf "@[<2>(let@ @[<hv 1>(@[<2>%a@ %a@]"
          Variable.print id print_named arg;
        let expr = letbody body in
        fprintf ppf ")@]@ %a)@]" print expr
    | Let_mutable { var = mut_var; initial_value = var; body; contents_kind } ->
      let print_kind ppf (kind : Lambda.value_kind) =
        match kind with
        | Pgenval -> ()
        | _ -> Format.fprintf ppf " %s" (Printlambda.value_kind kind)
      in
      fprintf ppf "@[<2>(let_mutable%a@ @[<2>%a@ %a@]@ %a)@]"
        print_kind contents_kind
        Mutable_variable.print mut_var
        Variable.print var
        print body
    | Switch (scrutinee, sw) ->
      fprintf ppf
        "@[<v 1>(switch %a@ @[<v 0>%a@])@]"
        Variable.print scrutinee print_switch sw
    | Apply_cont (i, trap_action, []) ->
      fprintf ppf "@[<2>(%agoto@ %a)@]"
        print_trap_action trap_action
        Continuation.print i
    | Apply_cont (i, trap_action, ls) ->
      fprintf ppf "@[<2>(%aapply_cont@ %a@ %a)@]"
        print_trap_action trap_action
        Continuation.print i
        Variable.print_list ls
    | Let_cont { body; handlers; } ->
      (* Printing the same way as for [Let] is easier when debugging lifting
        passes. *)
      if !Clflags.dump_let_cont then begin
        let rec let_cont_body (ul : t) =
          match ul with
          | Let_cont { body; handlers; } ->
            fprintf ppf "@ @[<2>%a@]" print_let_cont_handlers handlers;
            let_cont_body body
          | _ -> ul
        in
        fprintf ppf "@[<2>(let_cont@ @[<hv 1>(@[<2>%a@]"
          print_let_cont_handlers handlers;
        let expr = let_cont_body body in
        fprintf ppf ")@]@ %a)@]" print expr
      end else begin
        (* CR mshinwell: Share code with ilambda.ml *)
        let rec gather_let_conts let_conts (t : t) =
          match t with
          | Let_cont let_cont ->
            gather_let_conts (let_cont :: let_conts) let_cont.body
          | body -> let_conts, body
        in
        let let_conts, body = gather_let_conts [] fprint in
        let print_let_cont ppf { handlers; body = _; } =
          match handlers with
          | Nonrecursive { name; handler = { params; stub; handler; }; } ->
            fprintf ppf "@[<v 2>where %a%s%s@[%a@]%s =@ %a@]"
              Continuation.print name
              (if stub then " *stub*" else "")
              (match params with [] -> "" | _ -> " (")
              Parameter.List.print params
              (match params with [] -> "" | _ -> ")")
              print handler
          | Recursive handlers ->
            let first = ref true in
            fprintf ppf "@[<v 2>where rec ";
            Continuation.Map.iter (fun name
                    { params; stub; is_exn_handler; handler; } ->
                if not !first then fprintf ppf "@ ";
                fprintf ppf "@[%s%a%s%s%s@[%a@]%s@] =@ %a"
                  (if !first then "" else "and ")
                  Continuation.print name
                  (if stub then " *stub*" else "")
                  (if is_exn_handler then "*exn* " else "")
                  (match params with [] -> "" | _ -> " (")
                  Parameter.List.print params
                  (match params with [] -> "" | _ -> ")")
                  print handler;
                first := false)
              handlers;
            fprintf ppf "@]"
        in
        let pp_sep ppf () = fprintf ppf "@ " in
        fprintf ppf "@[<2>(@[<v 0>%a@;@[<v 0>%a@]@])@]" print body

  let print ppf t =
    fprintf ppf "%a@." print t
end and Named : sig
  type t =
    | Var of Variable.t
    | Const of const
    | Prim of Lambda.primitive * Variable.t list * Debuginfo.t
    | Assign of assign
    | Read_mutable of Mutable_variable.t
    | Symbol of Symbol.t
    | Read_symbol_field of Symbol.t * int
    | Allocated_const of Allocated_const.t
    | Set_of_closures of set_of_closures
    | Project_closure of project_closure
    | Move_within_set_of_closures of move_within_set_of_closures
    | Project_var of project_var

end = struct
  include Named

  let free_symbols_helper symbols (t : t) =
    match t with
    | Symbol symbol
    | Read_symbol_field (symbol, _) -> symbols := Symbol.Set.add symbol !symbols
    | Set_of_closures set_of_closures ->
      Variable.Map.iter (fun _ (function_decl : function_declaration) ->
          symbols := Symbol.Set.union function_decl.free_symbols !symbols)
        set_of_closures.function_decls.funs
    | _ -> ()

  let free_symbols t =
    let symbols = ref Symbol.Set.empty in
    iter_general ~toplevel:true
      (fun (_ : t) -> ())
      (fun (t : t) -> free_symbols_helper symbols named)
      (Is_named t);
    !symbols

  let variable_usage ?ignore_uses_in_project_var (t : t) =
    match t with
    | Var var -> Variable.Set.singleton var
    | _ ->
      let free = ref Variable.Set.empty in
      let free_variable fv = free := Variable.Set.add fv !free in
      begin match named with
      | Var var -> free_variable var
      | Symbol _ | Const _ | Allocated_const _ | Read_mutable _
      | Read_symbol_field _ -> ()
      | Assign { being_assigned = _; new_value; } ->
        free_variable new_value
      | Set_of_closures { free_vars; _ } ->
        (* Sets of closures are, well, closed---except for the free variable and
           specialised argument lists, which may identify variables currently in
           scope outside of the closure. *)
        Variable.Map.iter (fun _ (renamed_to : free_var) ->
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
      | Prim (_, args, _) -> List.iter free_variable args
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
    | Const cst -> fprintf ppf "Const(%a)" print_const cst
    | Allocated_const cst -> fprintf ppf "Aconst(%a)" Allocated_const.print cst
    | Read_mutable mut_var ->
      fprintf ppf "Read_mut(%a)" Mutable_variable.print mut_var
    | Assign { being_assigned; new_value; } ->
      fprintf ppf "@[<2>(assign@ %a@ %a)@]"
        Mutable_variable.print being_assigned
        Variable.print new_value
    | Read_symbol_field (symbol, field) ->
      fprintf ppf "%a.(%d)" Symbol.print symbol field
    | Project_closure project_closure ->
      print_project_closure ppf project_closure
    | Project_var project_var -> print_project_var ppf project_var
    | Move_within_set_of_closures move_within_set_of_closures ->
      print_move_within_set_of_closures ppf move_within_set_of_closures
    | Set_of_closures set_of_closures ->
      print_set_of_closures ppf set_of_closures
    | Prim (prim, args, dbg) ->
      fprintf ppf "@[<2>(%a@ <%s>@ %a)@]" Printlambda.primitive prim
        (Debuginfo.to_string dbg)
        Variable.print_list args
end and Let : sig
  type t = {
    var : Variable.t;
    defining_expr : Named.t;
    body : Expr.t;
    free_vars_of_defining_expr : Variable.Set.t;
    free_vars_of_body : Variable.Set.t;
  }
end = struct
  include Let
end and Let_mutable : sig
  type t = {
    var : Mutable_variable.t;
    initial_value : Variable.t;
    contents_kind : Lambda.value_kind;
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
end = struct
  include Let_cont_handlers

  type free_and_bound = {
    free : Continuation.Set.t;
    bound : Continuation.Set.t;
  }

  let free_and_bound_continuations (t : t) : free_and_bound =
    match handlers with
    | Nonrecursive { name; handler = { handler; _ }; } ->
      let fcs = Expr.free_continuations handler in
      if Continuation.Set.mem name fcs then begin
        Misc.fatal_errorf "Nonrecursive [Let_cont] handler appears to be \
            recursive:@ \n%a"
          print handlers
      end;
      { free = fcs;
        bound = Continuation.Set.singleton name;
      }
    | Recursive handlers ->
      let bound_conts = Continuation.Map.keys handlers in
      let fcs =
        Continuation.Map.fold (fun _name { handler; _ } fcs ->
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

  let free_variables (handlers : let_cont_handlers) =
    Continuation.Map.fold (fun _name { params; handler; _ } fvs ->
        Variable.Set.union fvs
          (Variable.Set.union
            (Typed_parameter.List.free_variables params)
            (Variable.Set.diff (free_variables handler)
              (Typed_parameter.List.vars params))))
      (continuation_map_of_let_handlers ~handlers)
      Variable.Set.empty

  let to_continuation_map t =
    match t with
    | Nonrecursive { name; handler } -> Continuation.Map.singleton name handler
    | Recursive handlers -> handlers

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
              { params; stub; is_exn_handler; handler; } ->
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
  type t = {
    Continuation_handler.t Continuation.Map.t;
  }
end = struct
  include Continuation_handlers

end and Continuation_handler : sig
  type t = {
    params : Parameter.t list;
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
    direct_call_surrogates : Variable.t Variable.Map.t;
  }
end = struct
  include Set_of_closures

  let create_set_of_closures ~function_decls ~free_vars ~specialised_args
        ~direct_call_surrogates =
    if !Clflags.flambda_invariant_checks then begin
      let all_fun_vars = Variable.Map.keys function_decls.funs in
      let expected_free_vars =
        Variable.Map.fold (fun _fun_var (function_decl : function_declaration)
                  expected_free_vars ->
            let free_vars =
              Variable.Set.diff function_decl.free_variables
                (Variable.Set.union (Parameter.Set.vars function_decl.params)
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
      let free_vars_domain = Variable.Map.keys free_vars in
      if not (Variable.Set.subset expected_free_vars free_vars_domain) then begin
        Misc.fatal_errorf "create_set_of_closures: [free_vars] mapping of \
            variables bound by the closure(s) is wrong.  (Must map at least \
            %a but only maps %a.)@ \nfunction_decls:@ %a"
          Variable.Set.print expected_free_vars
          Variable.Set.print free_vars_domain
          print_function_declarations function_decls
      end;
      let all_params =
        Variable.Map.fold (fun _fun_var (function_decl : function_declaration)
                  all_params ->
            Variable.Set.union (Parameter.Set.vars function_decl.params)
              all_params)
          function_decls.funs
          Variable.Set.empty
      in
      let spec_args_domain = Variable.Map.keys specialised_args in
      if not (Variable.Set.subset spec_args_domain all_params) then begin
        Misc.fatal_errorf "create_set_of_closures: [specialised_args] \
            maps variable(s) that are not parameters of the given function \
            declarations.  specialised_args domain=%a all_params=%a \n\
            function_decls:@ %a"
          Variable.Set.print spec_args_domain
          Variable.Set.print all_params
          print_function_declarations function_decls
      end
    end;
    { function_decls;
      free_vars;
      specialised_args;
      direct_call_surrogates;
    }

  let print ppf t =
    match t with
    | { function_decls; free_vars; specialised_args} ->
      let funs ppf =
        Variable.Map.iter (print_function_declaration ppf)
      in
      fprintf ppf "@[<2>(set_of_closures id=%a@ %a@ @[<2>free_vars={%a@ }@]@ \
          @[<2>specialised_args={%a})@]@ \
          @[<2>direct_call_surrogates=%a@]@ \
          @[<2>set_of_closures_origin=%a@]@]"
        Set_of_closures_id.print function_decls.set_of_closures_id
        funs function_decls.funs
        print_free_vars free_vars
        print_specialised_args specialised_args
        (Variable.Map.print Variable.print)
        set_of_closures.direct_call_surrogates
        Set_of_closures_origin.print function_decls.set_of_closures_origin
end and Function_declarations : sig =
  type t = {
    set_of_closures_id : Set_of_closures_id.t;
    set_of_closures_origin : Set_of_closures_origin.t;
    funs : Function_declaration.t Variable.Map.t;
  }

  val create
     : funs:Function_declaration.t Variable.Map.t
    -> t
  val update_function_declarations
     : t
    -> funs:Function_declaration.t Variable.Map.t
    -> t
  val import_for_pack
     : t
    -> (Set_of_closures_id.t -> Set_of_closures_id.t)
    -> (Set_of_closures_origin.t -> Set_of_closures_origin.t)
    -> t
  val print : Format.formatter -> t -> unit
end = struct
  include Function_declarations

  let create_function_declarations ~funs =
    let compilation_unit = Compilation_unit.get_current_exn () in
    let set_of_closures_id = Set_of_closures_id.create compilation_unit in
    let set_of_closures_origin =
      Set_of_closures_origin.create set_of_closures_id
    in
    { set_of_closures_id;
      set_of_closures_origin;
      funs;
    }

  let update_function_declarations function_decls ~funs =
    let compilation_unit = Compilation_unit.get_current_exn () in
    let set_of_closures_id = Set_of_closures_id.create compilation_unit in
    let set_of_closures_origin = function_decls.set_of_closures_origin in
    { set_of_closures_id;
      set_of_closures_origin;
      funs;
    }

  let import_function_declarations_for_pack function_decls
      import_set_of_closures_id import_set_of_closures_origin =
    { set_of_closures_id =
        import_set_of_closures_id function_decls.set_of_closures_id;
      set_of_closures_origin =
        import_set_of_closures_origin function_decls.set_of_closures_origin;
      funs = function_decls.funs;
    }

  let print ppf (t : t) =
    let funs ppf =
      Variable.Map.iter (print_function_declaration ppf)
    in
    fprintf ppf "@[<2>(%a)(origin = %a)@]" funs t.funs
      Set_of_closures_origin.print t.set_of_closures_origin
end and Function_declaration : sig =
  type t = {
    closure_origin : Closure_origin.t;
    continuation_param : Continuation.t;
    return_arity : int;
    params : Parameter.t list;
    body : Expr.t;
    free_variables : Variable.Set.t;
    free_symbols : Symbol.Set.t;
    stub : bool;
    dbg : Debuginfo.t;
    inline : Lambda.inline_attribute;
    specialise : Lambda.specialise_attribute;
    is_a_functor : bool;
  }

  val create
     : params:Typed_parameter.t list
    -> continuation_param:Continuation.t
    -> return_arity:int
    -> body:t
    -> stub:bool
    -> dbg:Debuginfo.t
    -> inline:Lambda.inline_attribute
    -> specialise:Lambda.specialise_attribute
    -> is_a_functor:bool
    -> closure_origin:Closure_origin.t
    -> t
  val update_body : t -> body:Expr.t -> t
  val update_params_and_body
    : t
    -> params:Typed_parameter.t list
    -> body:Expr.t
    -> t
  val used_params : t -> Variable.Set.t
  val print : Format.formatter -> t -> unit
end = struct
  include Function_declaration

  let create ~params ~continuation_param ~return_arity ~body ~stub ~dbg
        ~(inline : Lambda.inline_attribute)
        ~(specialise : Lambda.specialise_attribute) ~is_a_functor
        ~closure_origin : t =
    begin match stub, inline with
    | true, (Never_inline | Default_inline)
    | false, (Never_inline | Default_inline | Always_inline | Unroll _) -> ()
    | true, (Always_inline | Unroll _) ->
      Misc.fatal_errorf
        "Stubs may not be annotated as [Always_inline] or [Unroll]: %a"
        print body
    end;
    begin match stub, specialise with
    | true, (Never_specialise | Default_specialise)
    | false, (Never_specialise | Default_specialise | Always_specialise) -> ()
    | true, Always_specialise ->
      Misc.fatal_errorf
        "Stubs may not be annotated as [Always_specialise]: %a"
        print body
    end;
    if return_arity < 1 then begin
      Misc.fatal_errorf "Illegal return arity %d" return_arity
    end;
    { closure_origin;
      params;
      continuation_param;
      return_arity;
      body;
      free_variables = free_variables body;
      free_symbols = free_symbols body;
      stub;
      dbg;
      inline;
      specialise;
      is_a_functor;
    }

  let update_body_of_function_declaration (t : t) ~body : t =
    { closure_origin = t.closure_origin;
      params = t.params;
      continuation_param = t.continuation_param;
      return_arity = t.return_arity;
      body;
      free_variables = free_variables body;
      free_symbols = free_symbols body;
      stub = t.stub;
      dbg = t.dbg;
      inline = t.inline;
      specialise = t.specialise;
      is_a_functor = t.is_a_functor;
    }

  let update_params_and_body (t : t) ~params ~body : t =
    { closure_origin = t.closure_origin;
      params;
      continuation_param = t.continuation_param;
      return_arity = t.return_arity;
      body;
      free_variables = free_variables body;
      free_symbols = free_symbols body;
      stub = t.stub;
      dbg = t.dbg;
      inline = t.inline;
      specialise = t.specialise;
      is_a_functor = t.is_a_functor;
    }

  let used_params (function_decl : Function_declaration.t) =
    Variable.Set.filter (fun param ->
        Variable.Set.mem param function_decl.free_variables)
      (Parameter.Set.vars function_decl.params)

  let print ppf var (f : t) =
    let stub =
      if f.stub then
        " *stub*"
      else
        ""
    in
    let arity =
      if f.return_arity < 2 then ""
      else Printf.sprintf " (return arity %d)" f.return_arity
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
      "@[<2>(%a%s%s%s%s%s(origin %a)@ =@ fun@[<2> <%a>%a@] ->@ @[<2>%a@])@]@ "
      Variable.print var
      stub arity is_a_functor inline specialise
      Closure_origin.print f.closure_origin
      Continuation.print f.continuation_param
      Typed_parameter.List.print f.params
      Expr.print f.body

  let print ppf (var, t) =
    print ppf var t
end and Typed_parameter : sig
  type t = Parameter.t * (Function_declarations.t Flambda_type0.T.t)

  val free_variables : t -> Variable.Set.t

  module List : sig
    type nonrec t = t list

    val free_variables : t -> Variable.Set.t

    val print : Format.formatter -> t -> unit
  end

  val print : Format.formatter -> t -> unit
end = struct
  include Typed_parameter

  let print ppf (param, ty) =
    Format.fprintf ppf "@[(%a : %a)@]"
      Parameter.print param
      (Flambda_type0.T.print Function_declarations.print) ty

  let free_variables t =
    (* The variable within [t] is always presumed to be a binding
       occurrence, so the only free variables are those within the type. *)
    Flambda_type0.T.free_variables t.ty

  module List = struct
    type nonrec t = t list

    let free_variables t =
      Variable.Set.union_list (List.map free_variables t)

    let vars t =
      List.map (fun (param, _ty) -> Parameter.var param) t

    let print ppf t =
      Format.pp_print_list ~pp_sep:pp_print_space print t
  end
end

module With_free_variables = struct
  type 'a t =
    | Expr : expr * Variable.Set.t -> expr t
    | Named : Flambda_kind.t * named * Variable.Set.t -> named t

  let print (type a) ppf (t : a t) =
    match t with
    | Expr (expr, _) -> print ppf expr
    | Named (_, named, _) -> print_named ppf named

  let of_defining_expr_of_let let_expr =
    Named (let_expr.kind, let_expr.defining_expr,
      let_expr.free_vars_of_defining_expr)

  let of_body_of_let let_expr =
    Expr (let_expr.body, let_expr.free_vars_of_body)

  let of_expr expr =
    Expr (expr, free_variables expr)

  let of_named kind named =
    Named (kind, named, free_variables_named named)

  let to_named (t : named t) =
    match t with
    | Named (_, named, _) -> named

  let create_let_reusing_defining_expr var (t : named t) body =
    match t with
    | Named (kind, defining_expr, free_vars_of_defining_expr) ->
      Let {
        var;
        kind;
        defining_expr;
        body;
        free_vars_of_defining_expr;
        free_vars_of_body = free_variables body;
      }

  let create_let_reusing_body var ty defining_expr (t : expr t) =
    match t with
    | Expr (body, free_vars_of_body) ->
      Let {
        var;
        kind = Flambda_type0.kind_exn ty;
        defining_expr;
        body;
        free_vars_of_defining_expr = free_variables_named defining_expr;
        free_vars_of_body;
      }

  let create_let_reusing_both var (t1 : named t) (t2 : expr t) =
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
