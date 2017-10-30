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

[@@@ocaml.warning "+a-4-30-40-41-42"]

type continuation_kind = Normal | Exn_handler

(* For checking that push- and pop-trap operations match up correctly. *)
module Continuation_stack : sig
  type t

  val var : unit -> t
  val root : unit -> t
  val push : Trap_id.t -> Continuation.t -> t -> t

  val unify : Continuation.t -> t -> t -> unit
end = struct
  type t0 =
    | Root
    | Var (* Debug *)
    | Link of t
    | Push of Trap_id.t * Continuation.t * t

  and t = t0 ref

  let var () = ref Var

  let root () = ref Root

  let push id cont s = ref (Push (id, cont, s))

  let rec repr t =
    match !t with
    | Link s ->
      let u = repr s in
      t := u;
      u
    | v -> v

  let rec occurs_check cont t checked =
    if t == checked then begin
      Misc.fatal_errorf "Malformed exception continuation \
          (recursive stack) for %a"
        Continuation.print cont
    end;
    match !checked with
    | Var
    | Root -> ()
    | Link s
    | Push (_, _, s) ->
      occurs_check cont t s

  let rec unify cont t1 t2 =
    if t1 == t2 then ()
    else
      match repr t1, repr t2 with
      | Link _, _ | _, Link _ -> assert false
      | Var, _ ->
        occurs_check cont t1 t2;
        t1 := Link t2
      | _, Var ->
        occurs_check cont t2 t1;
        t2 := Link t1
      | Root, Root -> ()
      | Push (id1, c1, s1), Push (id2, c2, s2) ->
        if not (Trap_id.equal id1 id2) then begin
          Misc.fatal_errorf "Malformed exception continuation \
              (mismatched trap ID) for %a"
            Continuation.print cont
        end;
        if not (Continuation.equal c1 c2) then begin
          Misc.fatal_errorf "Malformed exception continuation \
              (mismatched continuations, %a vs. %a) for %a"
            Continuation.print c1
            Continuation.print c2
            Continuation.print cont
        end;
        unify cont s1 s2
      | Root, Push _ | Push _, Root ->
        Misc.fatal_errorf "Malformed exception continuation \
            (root stack is not empty) for %a"
          Continuation.print cont
end

type t = {
  all_variables_seen : Variable.Set.t ref;
  all_mutable_variables_seen : Mutable_variable.Set.t ref;
  all_continuations_seen : Continuation.Set.t ref;
  all_symbols_seen : Symbol.Set.t ref;
  all_set_of_closures_ids_seen : Set_of_closures_id.Set.t ref;
  all_closure_ids_seen : Closure_id.Set.t ref;
  uses_of_closure_ids_seen : Closure_id.Set.t ref;
  all_var_within_closures_seen : Var_within_closure.Set.t ref;
  uses_of_var_within_closures_seen : Var_within_closure.Set.t ref;
  variables : Flambda_kind.t Variable.Map.t;
  mutable_variables : Flambda_kind.t Mutable_variable.Map.t;
  continuations :
    (Flambda_arity.t * continuation_kind * Continuation_stack.t)
      Continuation.Map.t;
  symbols : Symbol.Set.t;
  continuation_stack : Continuation_stack.t;
}

let create () =
  { all_variables_seen = ref Variable.Set.empty;
    all_mutable_variables_seen = ref Mutable_variable.Set.empty;
    all_continuations_seen = ref Continuation.Set.empty;
    all_symbols_seen = ref Symbol.Set.empty;
    all_set_of_closures_ids_seen = ref Set_of_closures_id.Set.empty;
    all_closure_ids_seen = ref Closure_id.Set.empty;
    uses_of_closure_ids_seen = ref Closure_id.Set.empty;
    all_var_within_closures_seen = ref Var_within_closure.Set.empty;
    uses_of_var_within_closures_seen = ref Var_within_closure.Set.empty;
    variables = Variable.Map.empty;
    mutable_variables = Mutable_variable.Map.empty;
    continuations = Continuation.Map.empty;
    symbols = Symbol.Set.empty;
    continuation_stack = Continuation_stack.var ();
  }

let clean t ~return_cont ~return_cont_arity ~allowed_free_variables =
  let variables =
    Variable.Map.filter (fun var -> Variable.Map.mem var allowed_free_variables)
      t.variables
  in
  let continuation_stack = Continuation_stack.var () in
  let continuations =
    Continuation.Map.singleton
      (return_cont_arity, return_cont, continuation_stack)
  in
  { t with
    variables;
    mutable_variables = Mutable_variable.Map.empty;
    continuations;
    continuation_stack;
  }

let add_variable t var kind =
  if Variable.Map.mem var t.variables then begin
    Misc.fatal_errorf "Duplicate binding of variable %a which is already \
        bound in the current scope"
      Variable.print var
  end;
  if Variable.Set.mem var !(t.all_variables_seen) then begin
    Misc.fatal_errorf "Duplicate binding of variable %a which is bound \
        in some other scope"
      Variable.print var
  end;
  let compilation_unit = Compilation_unit.get_current_exn () in
  if not (Variable.in_compilation_unit var compilation_unit) then begin
    Misc.fatal_errorf "Binding occurrence of variable %a cannot occur in \
        this compilation unit since the variable is from another compilation \
        unit"
      Variable.print var
  end;
  t.all_variables_seen := Variable.Set.add var !(t.all_variables_seen);
  { t with
    variables = Variable.Map.add var kind t.variables;
  }

let add_variables t vars_and_kinds =
  List.fold_left (fun t (var, kind) -> add_variable t var kind) t vars_and_kinds

let add_mutable_variable t var kind =
  if Mutable_variable.Map.mem var t.mutable_variables then begin
    Misc.fatal_errorf "Duplicate binding of mutable variable %a which is \
        already bound in the current scope"
      Mutable_variable.print var
  end;
  if Mutable_variable.Set.mem var !(t.all_mutable_variables_seen) then begin
    Misc.fatal_errorf "Duplicate binding of mutable variable %a which is \
        bound in some other scope"
      Mutable_variable.print var
  end;
  let compilation_unit = Compilation_unit.get_current_exn () in
  if not (Mutable_variable.in_compilation_unit var compilation_unit) then begin
    Misc.fatal_errorf "Binding occurrence of mutable variable %a cannot occur \
        in this compilation unit since the variable is from another \
        compilation unit"
      Mutable_variable.print var
  end;
  t.all_mutable_variables_seen :=
    Mutable_variable.Set.add var !(t.all_mutable_variables_seen);
  { t with
    mutable_variables = Mutable_variable.Map.add var kind t.mutable_variables;
  }

let add_symbol t sym =
  if Symbol.Set.mem sym t.symbols then begin
    Misc.fatal_errorf "Duplicate binding of symbol %a which is already \
        bound in the current scope"
      Symbol.print sym
  end;
  if Symbol.Set.mem sym !(t.all_symbols_seen) then begin
    Misc.fatal_errorf "Duplicate binding of symbol %a which is bound \
        in some other scope"
      Symbol.print sym
  end;
  let compilation_unit = Compilation_unit.get_current_exn () in
  if not (Symbol.in_compilation_unit sym compilation_unit) then begin
    Misc.fatal_errorf "Binding occurrence of symbol %a cannot occur in \
        this compilation unit since the symbol is from another compilation \
        unit"
      Symbol.print sym
  end;
  t.all_symbols_seen := Symbol.Set.add sym !(t.all_symbols_seen);
  { t with
    symbols = Symbol.Set.add sym t.symbols;
  }

let add_continuation t cont arity kind stack =
  if Continuation.Map.mem cont t.continuations then begin
    Misc.fatal_errorf "Duplicate binding of continuation %a which is already \
        bound in the current scope"
      Continuation.print cont
  end;
  if Continuation.Set.mem cont !(t.all_continuations_seen) then begin
    Misc.fatal_errorf "Duplicate binding of continuation %a which is bound \
        in some other scope"
      Continuation.print cont
  end;
  t.all_continuations_seen :=
    Continuation.Set.add cont !(t.all_continuations_seen);
  { t with
    continuations =
      Continuation.Map.add cont (arity, kind, stack) t.continuations;
  }

let check_variable_is_bound t var =
  if not (Variable.Map.mem var t.variables) then begin
    Misc.fatal_errorf "Unbound variable %a" Variable.print var
  end

let check_variables_are_bound t vars =
  List.iter (fun var -> check_variable_is_bound t var) vars

let check_variable_is_bound_and_of_kind t var desired_kind =
  match Variable.Map.find var t.variables with
  | exception Not_found ->
    Misc.fatal_errorf "Unbound variable %a" Variable.print var
  | kind ->
    if not (Flambda_kind.equal kind desired_kind) then begin
      Misc.fatal_errorf "Variable %a is expected to have kind [%a] but is \
          of kind %a"
        Variable.print var
        Flambda_kind.print desired_kind
        Flambda_kind.print kind
      end

let check_variables_are_bound_and_of_kind t vars desired_kind =
  List.iter (fun var ->
      check_variable_is_bound_and_of_kind t var desired_kind)
    vars

let check_mutable_variable_is_bound t var =
  if not (Mutable_variable.Map.mem var t.mutable_variables) then begin
    Misc.fatal_errorf "Unbound mutable variable %a" Mutable_variable.print var
  end

let check_symbol_is_bound t var =
  if not (Symbol.Set.mem var t.symbols) then begin
    Misc.fatal_errorf "Unbound symbol %a" Symbol.print var
  end

let find_continuation_opt t cont =
  match Continuation.Map.find cont t.continuations with
  | exception Not_found -> None
  | result -> Some result

let continuation_arity t cont =
  match find_continuation_opt t cont with
  | Some (arity, _, _) -> arity
  | None ->
    Misc.fatal_errorf "Unbound continuation %a" Continuation.print cont

let kind_of_variable t var =
  match Variable.Map.find var t.variables with
  | exception Not_found ->
    Misc.fatal_errorf "Unbound variable %a" Variable.print var
  | kind -> kind

let kind_of_mutable_variable t var =
  match Mutable_variable.Map.find var t.mutable_variables with
  | exception Not_found ->
    Misc.fatal_errorf "Unbound mutable variable %a" Mutable_variable.print var
  | kind -> kind

let current_continuation_stack t = t.continuation_stack

let set_current_continuation_stack t continuation_stack =
  { t with continuation_stack; }

let add_set_of_closures_id t id =
  if Set_of_closures_id.Set.mem id !(t.all_set_of_closures_ids_seen) then begin
    Misc.fatal_errorf "Set of closures ID %a occurs more than once in the \
        program"
      Set_of_closures_id.print id
  end;
  t.all_set_of_closures_ids_seen :=
    Set_of_closures_id.Set.add id !(t.all_set_of_closures_ids_seen)

let add_closure_id t id =
  (* The same closure ID may be bound multiple times in the same program, so
     there is no membership check here. *)
  t.all_closure_ids_seen := Closure_id.Set.add id !(t.all_closure_ids_seen)

let add_use_of_closure_id t id =
  t.uses_of_closure_ids_seen :=
    Closure_id.Set.add id !(t.uses_of_closure_ids_seen)

let add_var_within_closure t id =
  (* The same closure ID may be bound multiple times in the same program, so
     there is no membership check here. *)
  t.all_var_within_closures_seen :=
    Var_within_closure.Set.add id !(t.all_var_within_closures_seen)

let add_use_of_var_within_closure t id =
  t.uses_of_var_within_closures_seen :=
    Var_within_closure.Set.add id !(t.uses_of_var_within_closures_seen)
