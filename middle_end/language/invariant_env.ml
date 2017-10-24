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

  val repr : t -> t

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
        unify_stack cont s1 s2
      | Root, Push _ | Push _, Root ->
        Misc.fatal_errorf "Malformed exception continuation \
            (root stack is not empty) for %a"
          Continuation.print cont
end

type t = {
  mutable all_variables_seen : Variable.Set.t;
  mutable all_mutable_variables_seen : Mutable_variable.Set.t;
  mutable all_continuations_seen : Continuation.Set.t;
  mutable all_symbols_seen : Symbol.Set.t;
  variables : Flambda_kind.t Variable.Map.t;
  mutable_variables : Flambda_kind.t Mutable_variable.Set.t;
  continuations :
    (Flambda_arity.t * continuation_kind * stack_type) Continuation.Map.t;
  symbols : Symbol.Set.t;
  continuation_stack : Continuation_stack.t;
}

let create () =
  { all_variables_seen = Variable.Set.empty;
    all_mutable_variables_seen = Mutable_variable.Map.empty;
    all_continuations_seen = Continuation.Set.empty;
    all_symbols_seen = Symbol.Set.empty;
    variables = Variable.Map.empty;
    mutable_variables = Mutable_variable.Map.empty;
    continuations = Continuation.Map.empty;
    symbols = Symbol.Set.empty;
    continuation_stack = Continuation_stack.var ();
  }

let add_variable t var kind =
  if Variable.Map.mem var t.variables then begin
    Misc.fatal_errorf "Duplicate binding of variable %a which is already \
        bound in the current scope"
      Variable.print var
  end;
  if Variable.Set.mem var t.all_variables_seen then begin
    Misc.fatal_errorf "Duplicate binding of variable %a which is bound \
        in some other scope"
      Variable.print var
  end;
  let compilation_unit = Compilation_unit.get_current_exn () in
  if not (Variable.in_compilation_unit var compilation_unit) then
    Misc.fatal_errorf "Binding occurrence of variable %a cannot occur in \
        this compilation unit since the variable is from another compilation \
        unit"
      Variable.print var
  end;
  { t with
    all_variables_seen = Variable.Set.add var t.all_variables_seen;
    variables = Variable.Map.add var kind t.variables;
  }

let add_variables t vars_and_kinds =
  List.fold_left (fun t (var, kind) -> add_variable t var kind) t vars_and_kinds

let add_typed_parameters ~importer t params =
  List.fold_left (fun t param ->
      let var = Flambda.Typed_parameter.var param in
      let kind = Flambda.Typed_parameter.kind ~importer param in
      add_variable t var kind)
    t
    params

let add_mutable_variable t var kind =
  if Mutable_variable.Map.mem var t.mutable_variables then begin
    Misc.fatal_errorf "Duplicate binding of mutable variable %a which is \
        already bound in the current scope"
      Mutable_variable.print var
  end;
  if Mutable_variable.Set.mem var t.all_mutable_variables_seen then begin
    Misc.fatal_errorf "Duplicate binding of mutable variable %a which is \
        bound in some other scope"
      Mutable_variable.print var
  end;
  let compilation_unit = Compilation_unit.get_current_exn () in
  if not (Mutable_variable.in_compilation_unit var compilation_unit) then
    Misc.fatal_errorf "Binding occurrence of mutable variable %a cannot occur \
        in this compilation unit since the variable is from another \
        compilation unit"
      Mutable_variable.print var
  end;
  { t with
    mutable_variables_seen =
      Mutable_variable.Set.add var t.mutable_variables_seen;
    mutable_variables = Mutable_variable.Map.add var kind t.mutable_variables;
  }

let add_symbol t sym =
  if Symbol.Map.mem sym t.symbols then begin
    Misc.fatal_errorf "Duplicate binding of symbol %a which is already \
        bound in the current scope"
      Symbol.print sym
  end;
  if Symbol.Set.mem sym t.all_symbols_seen then begin
    Misc.fatal_errorf "Duplicate binding of symbol %a which is bound \
        in some other scope"
      Symbol.print sym
  end;
  let compilation_unit = Compilation_unit.get_current_exn () in
  if not (Variable.in_compilation_unit var compilation_unit) then
    Misc.fatal_errorf "Binding occurrence of variable %a cannot occur in \
        this compilation unit since the variable is from another compilation \
        unit"
      Variable.print var
  end;
  { t with
    symbols = Symbol.Set.add sym t.symbols;
  }

let add_continuation t cont arity kind =
  if Continuation.Map.mem cont t.continuations then begin
    Misc.fatal_errorf "Duplicate binding of continuation %a which is already \
        bound in the current scope"
      Continuation.print cont
  end;
  if Continuation.Set.mem cont t.all_continuations_seen then begin
    Misc.fatal_errorf "Duplicate binding of continuation %a which is bound \
        in some other scope"
      Continuation.print cont
  end;
  { t with
    continuations =
      Continuation.Map.add cont (arity, kind) t.continuations;
  }

let check_variable_is_bound t var =
  if not (Variable.Set.mem var t.variables) then begin
    Misc.fatal_errorf "Unbound variable %a" Variable.print var
  end

let check_variable_is_bound_and_of_kind_value t var =
  match Variable.Set.find var t.variables with
  | exception Not_found ->
    Misc.fatal_errorf "Unbound variable %a" Variable.print var
  | kind ->
    if not (Flambda_kind.is_value kind) then begin
      Misc.fatal_errorf "Variable %a is expected to have kind [Value] but is \
          of kind %a"
        Variable.print var
        Flambda_kind.print kind
    end

let check_variable_is_bound_and_of_kind_value_must_scan t var =
  match Variable.Set.find var t.variables with
  | exception Not_found ->
    Misc.fatal_errorf "Unbound variable %a" Variable.print var
  | Value Must_scan -> ()
  | _ ->
    Misc.fatal_errorf "Variable %a is expected to have kind [Value Must_scan] \
        but is of kind %a"
      Variable.print var
      Flambda_kind.print kind

let check_mutable_variable_is_bound t var =
  if not (Mutable_Variable.Set.mem var t.mutable_variables) then begin
    Misc.fatal_errorf "Unbound mutable variable %a" Mutable_Variable.print var
  end

let check_symbol_is_bound t var =
  if not (Symbol.Set.mem var t.symbols) then begin
    Misc.fatal_errorf "Unbound symbol %a" Symbol.print var
  end

let find_continuation_opt t cont =
  match Continuation.Map.find t.continuations cont with
  | exception Not_found -> None
  | result -> Some result

let kind_of_variable t var =
  match Variable.Set.find var t.variables with
  | exception Not_found ->
    Misc.fatal_errorf "Unbound variable %a" Variable.print var
  | kind -> kind

let kind_of_mutable_variable t var =
  match Mutable_variable.Set.find var t.mutable_variables with
  | exception Not_found ->
    Misc.fatal_errorf "Unbound mutable variable %a" Mutable_variable.print var
  | kind -> kind

let current_continuation_stack t = t.current_continuation_stack

let set_current_continuation_stack t continuation_stack =
  { t with continuation_stack; }
