(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2016 OCamlPro SAS                                          *)
(*   Copyright 2016 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module A = Simple_value_approx
module E = Inline_and_simplify_aux.Env
module R = Inline_and_simplify_aux.Result

module Continuation_with_specialised_args = struct
  (* A continuation together with, for each of its specialised arguments, the
     variable corresponding to such argument in a particular application of
     that continuation.
  *)
  type t = Continuation.t * Flambda.specialised_args

  include Identifiable.Make (struct
    type nonrec t = t

    let compare t1 t2 =
      let c = Continuation.compare (fst t1) (fst t2) in
      if c <> 0 then c
      else
        (Variable.Map.compare Flambda.compare_specialised_to) (snd t1) (snd t2)

    let equal t1 t2 =
      compare t1 t2 = 0

    let hash t =
      Hashtbl.hash (Continuation.hash (fst t),
        Hashtbl.hash (Variable.Map.bindings (snd t)))

    let output _chan _t = Misc.fatal_error "not implemented"

    let print ppf (cont, spec_args) =
      Format.fprintf ppf "@[(%a, %a)@]"
        Continuation.print cont
        Flambda.print_specialised_args spec_args
  end)
end

type specialising_result =
  | Didn't_specialise
  | Specialised of Continuation.t * Flambda.let_cont_handlers

(* This function constructs a suitable environment for simplification of a
   continuation's body that is eligible for specialisation.  The freshening
   of the body is performed during the simplification.
   If the continuation is defined simultaneously with others, all of the
   bodies will be simplified; specialised argument information may be
   introduced for continuations apart from the starting point (called [cont])
   using the invariant parameters flow information.
*)
let try_specialising ~cont ~(old_handlers : Flambda.continuation_handlers)
      ~(newly_specialised_args : Flambda.specialised_args)
      ~invariant_params_flow ~env ~recursive ~simplify_let_cont_handlers
      : specialising_result =
  let freshening =
    Continuation.Map.fold (fun cont _handler freshening ->
        let _new_cont, freshening =
          Freshening.add_static_exception freshening cont
        in
        freshening)
      old_handlers
      (Freshening.activate (E.freshening env))
  in
  let env = E.set_never_inline (E.set_freshening env freshening) in
  let env =
    Continuation.Map.fold (fun cont (handler : Flambda.continuation_handler)
              env ->
        let cont = Freshening.apply_static_exception (E.freshening env) cont in
        let approx =
          Continuation_approx.create_unknown ~name:cont
            ~num_params:(List.length handler.params)
        in
        E.add_continuation env cont approx)
      old_handlers
      env
  in
  let entry_point_cont = cont in
  let entry_point_new_cont =
    Freshening.apply_static_exception freshening cont
  in
  let new_handlers =
    Continuation.Map.fold (fun cont (old_handler : Flambda.continuation_handler)
            new_handlers ->
        let wrong_spec_args =
          Variable.Set.inter (Variable.Map.keys old_handler.specialised_args)
            (Variable.Map.keys newly_specialised_args)
        in
        if not (Variable.Set.is_empty wrong_spec_args) then begin
           Misc.fatal_errorf "These parameters of continuation %a have already \
              been specialised: %a"
            Continuation.print cont
            Variable.Set.print wrong_spec_args
        end;
        (* Compute the newly-specialised args.  These are either:
           (a) those arising from the "entry point" (i.e. [Apply_cont] of
               [entry_point_cont]); or
           (b) those arising from invariant parameters flow from the entry
               point's continuation handler. *)
        let newly_specialised_args =
          if Continuation.equal cont entry_point_cont then
            newly_specialised_args
          else
            Variable.Map.fold (fun param (spec_to : Flambda.specialised_to)
                    newly_specialised_args ->
                match Variable.Map.find param invariant_params_flow with
                | exception Not_found -> newly_specialised_args
                | flows_to ->
                  let module CV =
                    Invariant_params.Continuations.Continuation_and_variable
                  in
                  CV.Set.fold (fun (cont', param')
                          newly_specialised_args ->
                      if not (Continuation.equal cont cont') then
                        newly_specialised_args
                      else
                        Variable.Map.add param' spec_to
                          newly_specialised_args)
                    flows_to
                    newly_specialised_args)
              newly_specialised_args
              Variable.Map.empty
        in
        let specialised_args =
          Variable.Map.disjoint_union old_handler.specialised_args
            newly_specialised_args
        in
        let new_handler =
          { old_handler with
            specialised_args;
          }
        in
        Continuation.Map.add cont new_handler new_handlers)
      old_handlers
      Continuation.Map.empty
  in
  let r =
    Continuation.Map.fold (fun cont (handler : Flambda.continuation_handler)
            r ->
        let num_params = List.length handler.params in
        let args_approxs =
          Array.to_list (Array.init num_params (fun _ -> A.value_bottom))
        in
        let cont = Freshening.apply_static_exception (E.freshening env) cont in
        R.use_continuation r env cont ~inlinable_position:false
          ~args:[] ~args_approxs)
      old_handlers
      (R.create ())
  in
  let new_handlers, r =
    simplify_let_cont_handlers ~env ~r ~handlers:new_handlers
      ~recursive ~freshening:(E.freshening env)
      ~update_use_env:(fun env -> env)
  in
  match new_handlers with
  | None ->
Format.eprintf "try_specialising: None case\n%!";
    Didn't_specialise
  | Some new_handlers ->
Format.eprintf "try_specialising: new handlers:\n@ %a\n%!"
  Flambda.print_let_cont_handlers new_handlers;
    let module W = Inlining_cost.Whether_sufficient_benefit in
    let wsb =
      let originals =
        List.map (fun (handler : Flambda.continuation_handler) ->
            handler.handler)
          (Continuation.Map.data old_handlers)
      in
      let new_handlers =
        match (new_handlers : Flambda.let_cont_handlers) with
        | Nonrecursive { handler; _ } -> [handler.handler]
        | Recursive handlers ->
          List.map (fun (handler : Flambda.continuation_handler) ->
              handler.handler)
            (Continuation.Map.data handlers)
        | Alias _ ->
          Misc.fatal_error "simplify_let_cont_handlers should not return Alias"
      in
      (* CR mshinwell: Probably some stuff about jump benefits should be
        added... *)
      W.create_list ~originals
        ~toplevel:(E.at_toplevel env)
        ~branch_depth:(E.branch_depth env)
        new_handlers
        ~benefit:(R.benefit r)
        ~lifting:false
        ~round:(E.round env)
    in
Format.eprintf "Evaluating %a\n%!" (W.print_description ~subfunctions:false) wsb;
    if W.evaluate wsb then
      Specialised (entry_point_new_cont, new_handlers)
    else
      Didn't_specialise

let find_specialisations r ~simplify_let_cont_handlers ~backend =
  let module N = Num_continuation_uses in
  let module U = Inline_and_simplify_aux.Continuation_uses in
  (* The first step constructs two maps.  The first of these is:
          (continuation * (specialised_params -> arg))
       -> set of (continuation * args)
     which groups together uses of the continuation where some subset of
     its invariant parameters have the same arguments across those uses.  The
     range of the map enables identification of the corresponding [Apply_cont]
     nodes which will need to be repointed if the continuation is specialised
     for those uses.
     The second map just maps continuations to their handlers (including any
     handlers defined simultaneously) and the environment of definition. *)
  let specialisations, conts_to_handlers =
    (* CR mshinwell: [recursive] appears to be redundant with
       [approx.recursive] *)
    Continuation.Map.fold (fun cont (uses, approx, _env, recursive)
          ((specialisations, conts_to_handlers) as acc) ->
        match Continuation_approx.handlers approx with
        | None ->
          (* Applications of continuations inside their own handlers will
             hit this case.  This is equivalent to the "self call" check
             in [Inlining_decision]. *)
          acc
        | Some (Nonrecursive { is_exn_handler = true; _ }) ->
          acc
        | Some handlers ->
          let handlers, invariant_params, invariant_params_flow =
            match handlers with
            | Nonrecursive handler ->
              let handlers =
                Continuation.Map.add cont handler Continuation.Map.empty
              in
              (* Non-recursive continuation: all parameters are invariant. *)
              let invariant_params =
                List.fold_left (fun invariant_params param ->
                    let param_set = Variable.Set.singleton param in
                    Variable.Map.add param param_set invariant_params)
                  Variable.Map.empty
                  handler.params
              in
              let invariant_params_flow = Variable.Map.empty in
              handlers, invariant_params, invariant_params_flow
            | Recursive handlers ->
              let invariant_params =
                Invariant_params.Continuations.invariant_params_in_recursion
                  handlers ~backend
              in
              let invariant_params_flow =
                Invariant_params.Continuations.invariant_param_sources
                  handlers ~backend
              in
              handlers, invariant_params, invariant_params_flow
          in
          (* We don't currently share specialised continuations in the same
             set of recursive handlers between entry points to that set.
             So for example if there is a [Let_cont] binding k1 and k2
             which are recursive and we see [Apply_cont]s that can be
             specialised---one for k1 and one for k2---then they will end up
             each producing a specialised copy of the entire {k1, k2} set. *)
          let handler =
            match Continuation.Map.find cont handlers with
            | handler -> handler
            | exception Not_found ->
              Misc.fatal_errorf "Continuation %a not found in handler map \
                  inside the approximation"
                Continuation.print cont
          in
(*
Format.eprintf "Number of inlinable application points: %d\n%!"
            (List.length (U.inlinable_application_points uses));
*)
          List.fold_left (fun ((specialisations, conts_to_handlers) as acc)
                  (use : U.Use.t) ->
              assert (List.length handler.params = List.length use.args);
              let params_with_args =
                Variable.Map.of_list (List.combine handler.params use.args)
              in
              let params_with_specialised_args =
                Variable.Map.filter (fun param (_arg, arg_approx) ->
(*
Format.eprintf "Considering use of param %a as arg %a, approx %a: \
    Invariant? %b New spec arg? %b Useful approx? %b\n%!"
  Variable.print param
  Variable.print arg
  Simple_value_approx.print arg_approx
  (Variable.Map.mem param invariant_params)
  (not (Variable.Map.mem param handler.specialised_args))
  (A.useful arg_approx);
*)
                    Variable.Map.mem param invariant_params
                      && not (Variable.Map.mem param
                        handler.specialised_args)
                      && A.useful arg_approx)
                  params_with_args
              in
              if Variable.Map.cardinal params_with_specialised_args < 1 then
                acc
              else
                let params_with_specialised_args =
                  Variable.Map.map (fun (arg, _) : Flambda.specialised_to ->
                      { var = Some arg;
                        projection = None;
                      })
                    params_with_specialised_args
                in
                let key : Continuation_with_specialised_args.t =
                  cont, params_with_specialised_args
                in
                let uses =
                  match
                    Continuation_with_specialised_args.Map.find key
                      specialisations
                  with
                  | exception Not_found -> Continuation.With_args.Set.empty
                  | uses -> uses
                in
                let use_args =
                  List.map (fun (arg, _approx) -> arg) use.args
                in
                let specialisations =
                  Continuation_with_specialised_args.Map.add key
                    (Continuation.With_args.Set.add (cont, use_args) uses)
                    specialisations
                in
                let conts_to_handlers =
                  (* This [add] is of course executed once per use of the
                     continuation; it will thus choose the environment for
                     some arbitrary use of that continuation as that to be
                     used during [try_specialising].  This is fine: the only
                     things we need during the simplification inside that
                     function are the dependencies of the continuation
                     handler(s) and the approximations of the newly-specialised
                     arguments (and their dependencies, transitively).  All of
                     these will be present in the environment at each of the
                     use sites. *)
                  Continuation.Map.add cont
                    (handlers, use.env, invariant_params_flow, recursive)
                    conts_to_handlers
                in
                specialisations, conts_to_handlers)
            (specialisations, conts_to_handlers)
            (U.inlinable_application_points uses))
      (R.continuation_definitions_with_uses r)
      (Continuation_with_specialised_args.Map.empty,
        Continuation.Map.empty)
  in
Format.eprintf "Specialisation first stage result:\n%a\n%!"
  (Continuation_with_specialised_args.Map.print
    Continuation.With_args.Set.print)
  specialisations;
  (* The second step takes the map from above and makes a decision for
     each proposed specialisation, returning two maps:
       continuation "k" -> new continuation(s) to be defined just before "k"
       (continuation * args) -> new "entry" continuation
     The first map is then used to add new [Let_cont] definitions and the
     second is used to rewrite [Apply_cont] to specialised continuations. *)
  Continuation_with_specialised_args.Map.fold (fun
          (cont, newly_specialised_args)
          cont_application_points ((new_conts, apply_cont_rewrites) as acc) ->
      let old_handlers, env, invariant_params_flow, recursive =
        match Continuation.Map.find cont conts_to_handlers with
        | exception Not_found -> assert false  (* see above *)
        | old_handlers -> old_handlers
      in
      match
        try_specialising ~cont ~old_handlers ~newly_specialised_args
          ~invariant_params_flow ~env ~recursive ~simplify_let_cont_handlers
      with
      | Didn't_specialise -> acc
      | Specialised (entry_point_new_cont, new_handlers) ->
        let existing_conts =
          match Continuation.Map.find cont new_conts with
          | exception Not_found -> []
          | existing_conts -> existing_conts
        in
        let new_conts =
          Continuation.Map.add cont (new_handlers :: existing_conts)
            new_conts
        in
        let apply_cont_rewrites =
          Continuation.With_args.Set.fold (fun ((cont', _args) as key)
                  apply_cont_rewrites ->
              assert (Continuation.equal cont cont');
              assert (not (Continuation.With_args.Map.mem key
                apply_cont_rewrites));
              Continuation.With_args.Map.add key entry_point_new_cont
                apply_cont_rewrites)
            cont_application_points
            apply_cont_rewrites
        in
        new_conts, apply_cont_rewrites)
    specialisations
    (Continuation.Map.empty, Continuation.With_args.Map.empty)

module Placement = struct
  type t =
    | After_let of Variable.t
    | After_let_cont of Continuation.Set.t
    | Just_inside_continuation of Continuation.t

  include Identifiable.Make (struct
    type nonrec t = t

    let compare t1 t2 =
      match t1, t2 with
      | After_let v1, After_let v2 -> Variable.compare v1 v2
      | After_let _, _ -> -1
      | _, After_let _ -> 1
      | After_let_cont conts1, After_let_cont conts2 ->
        Continuation.Set.compare conts1 conts2
      | After_let_cont _, _ -> -1
      | _, After_let_cont _ -> 1
      | Just_inside_continuation cont1, Just_inside_continuation cont2 ->
        Continuation.compare cont1 cont2

    let equal t1 t2 = (compare t1 t2 = 0)

    let hash t =
      match t with
      | After_let v -> Hashtbl.hash (0, Variable.hash v)
      | After_let_cont conts ->
        let conts_hash =
          Continuation.Set.fold (fun cont hash ->
              Hashtbl.hash (hash, Continuation.hash cont))
            conts
            0
        in
        Hashtbl.hash (1, conts_hash)
      | Just_inside_continuation cont ->
        Hashtbl.hash (2, Continuation.hash cont)

    let print ppf t =
      match t with
      | After_let var ->
        Format.fprintf ppf "after let-binding of %a" Variable.print var
      | After_let_cont conts ->
        Format.fprintf ppf "after Let_cont binding {%a}"
          Continuation.Set.print conts
      | Just_inside_continuation cont ->
        Format.fprintf ppf "just inside handler of %a" Continuation.print cont

    let output _ _ = Misc.fatal_error "Not implemented"
  end)
end

(* For each specialised version of a continuation, find where in the
   expression the continuation should be placed, such that all of its
   free variables are in scope. *)

type being_placed = {
  handlers : Flambda.let_cont_handlers;
  handlers_as_map : Flambda.continuation_handlers;
  needed_fvs : Variable.Set.t;
}

type insertion_state = {
  vars_in_scope : Variable.Set.t;
  (* All variables currently in scope. *)
  pending : Flambda.let_cont_handlers list Continuation.Map.t;
  (* From pre-existing continuations to specialised versions thereof.
     (For each pre-existing, possibly mutually-recursive, set of continuations
     there may be multiple specialised versions; hence the "list".) *)
  placing : being_placed list;
  (* Specialised continuations whose corresponding pre-existing continuation
     is in scope and that we are looking to place as soon as all required
     variables are in scope. *)
  all_needed_variables : Variable.Set.t;
  (* The union of all variables that the handlers in [placing] require to
     be in scope.  This field is present as an optimisation. *)
  placed : Flambda.let_cont_handlers Placement.Map.t;
  (* Specialised continuations whose placement has been identified. *)
}

let find_insertion_points expr ~vars_in_scope ~new_conts =
  let rec find_insertion_points (expr : Flambda.expr) ~state =
    let passing_var_binder var ~make_placement ~state =
      let vars_in_scope = Variable.Set.add var state.vars_in_scope in
      let placed = ref state.placed in
      let placing =
        Misc.Stdlib.List.filter_map (fun (being_placed : being_placed) ->
            let needed_fvs = Variable.Set.remove var being_placed.needed_fvs in
            if Variable.Set.is_empty needed_fvs then begin
              let placement = make_placement var in
Format.eprintf "Placing %a %a\n%!"
  Continuation.Set.print (Continuation.Map.keys being_placed.handlers_as_map)
  Placement.print placement;
              placed :=
                Placement.Map.add placement being_placed.handlers !placed;
              None
            end else begin
              Some { being_placed with needed_fvs; }
            end)
          state.placing
      in
      { state with
        placed = !placed;
        placing;
        vars_in_scope;
      }
    in
    let passing_continuation_binding ~name ~state =
Format.eprintf "Passing binding of %a\n%!" Continuation.print name;
      match Continuation.Map.find name state.pending with
      | exception Not_found -> state
      | new_handlers_list ->
        List.fold_left (fun state
                (new_handlers : Flambda.let_cont_handlers) ->
            let pending = Continuation.Map.remove name state.pending in
            let needed_fvs =
              Variable.Set.diff
                (Flambda.free_variables_of_let_cont_handlers new_handlers)
                state.vars_in_scope
            in
            let being_placed =
              let handlers_as_map =
                match new_handlers with
                | Nonrecursive { name; handler; } ->
                  Continuation.Map.add name handler Continuation.Map.empty
                | Recursive handlers -> handlers
                | Alias _ -> assert false
              in
Format.eprintf "Being placed: %a (needed fvs %a)\n%!"
Continuation.Set.print (Continuation.Map.keys handlers_as_map)
Variable.Set.print needed_fvs;
              { handlers = new_handlers;
                handlers_as_map;
                needed_fvs;
              }
            in
            let placing = being_placed :: state.placing in
            let all_needed_variables =
              Variable.Set.union state.all_needed_variables needed_fvs
            in
            { state with
              pending;
              placing;
              all_needed_variables;
            })
          state
          new_handlers_list
    in
    let enter_continuation_handlers ~handlers ~state =
      Continuation.Map.fold (fun name
              (handler : Flambda.continuation_handler) state ->
          let params = Variable.Set.of_list handler.params in
          let vars_in_scope =
            Variable.Set.union state.vars_in_scope params
          in
          let state = { state with vars_in_scope; } in
          let needed_params =
            Variable.Set.inter params state.all_needed_variables
          in
          let state =
            Variable.Set.fold (fun var state ->
Format.eprintf "Passing binding of continuation parameter %a\n%!"
Variable.print var;
                let state =
                  passing_var_binder var ~make_placement:(fun _var ->
                      Just_inside_continuation name)
                    ~state
                in
                let all_needed_variables =
                  Variable.Set.remove var state.all_needed_variables
                in
                { state with
                  all_needed_variables;
                })
              needed_params
              state
          in
          find_insertion_points handler.handler ~state)
        handlers
        state
    in
    let passing_continuation_bindings ~body ~handlers ~state =
      let state =
        Continuation.Map.fold (fun name _handler state ->
            passing_continuation_binding ~name ~state)
          handlers
          state
      in
      let state =
        Variable.Set.fold (fun var state ->
            passing_var_binder var ~make_placement:(fun _var ->
                After_let_cont (Continuation.Map.keys handlers))
              ~state)
          state.vars_in_scope
          state
      in
      let state = enter_continuation_handlers ~handlers ~state in
      find_insertion_points body ~state
    in
    match expr with
    | Let { var; body; _ } ->
      if not (Variable.Set.mem var state.all_needed_variables) then
        find_insertion_points body ~state
      else
        let state =
          passing_var_binder var ~make_placement:(fun var -> After_let var)
            ~state
        in
        let all_needed_variables =
          Variable.Set.remove var state.all_needed_variables
        in
        let state =
          { state with
            all_needed_variables;
          }
        in
        find_insertion_points body ~state
    | Let_cont { body; handlers = Nonrecursive { name; handler; }; } ->
      let handlers = Continuation.Map.add name handler Continuation.Map.empty in
      passing_continuation_bindings ~body ~handlers ~state
    | Let_cont { body; handlers = Recursive handlers; } ->
      passing_continuation_bindings ~body ~handlers ~state
    | Let_cont { body; handlers = Alias _; }
    | Let_mutable { body; _ } -> find_insertion_points body ~state
    | Apply _ | Apply_cont _ | Switch _ | Proved_unreachable -> state
  in
  let state =
    let state =
      { vars_in_scope;
        pending = new_conts;
        placing = [];
        all_needed_variables = Variable.Set.empty;
        placed = Placement.Map.empty;
      }
    in
    find_insertion_points expr ~state
  in
  assert (Continuation.Map.is_empty state.pending);
  assert (state.placing = []);
  assert (Variable.Set.is_empty state.all_needed_variables);
  assert (
    let num_new_conts =
      Continuation.Map.fold (fun _cont new_conts num_new_conts ->
          num_new_conts + List.length new_conts)
        new_conts
        0
    in
    num_new_conts = Placement.Map.cardinal state.placed);
  state.placed

let insert_specialisations r (expr : Flambda.expr) ~vars_in_scope ~new_conts
        ~apply_cont_rewrites =
  let placed = find_insertion_points expr ~vars_in_scope ~new_conts in
  let place ~placement ~around =
    match Placement.Map.find placement placed with
    | exception Not_found -> None
    | handlers ->
      Some (Flambda.Let_cont {
        body = around;
        handlers;
      })
  in
  let r = ref r in
  let expr =
    Flambda_iterators.map_toplevel_expr (fun (expr : Flambda.t) : Flambda.t ->
        match expr with
        | Let { var; defining_expr; body } ->
          let placement : Placement.t = After_let var in
          begin match place ~placement ~around:body with
          | None -> expr
          | Some body -> Flambda.create_let var defining_expr body
          end
        | Let_cont { body; handlers = Nonrecursive { name; handler; }; } ->
          let done_something = ref false in
          let placement : Placement.t = Just_inside_continuation name in
          let handler_body =
            match place ~placement ~around:handler.handler with
            | None -> handler.handler
            | Some handler_body ->
              done_something := true;
              handler_body
          in
          let body =
            let placement : Placement.t =
              After_let_cont (Continuation.Set.singleton name)
            in
            match place ~placement ~around:body with
            | None -> body
            | Some body ->
              done_something := true;
              body
          in
          if not !done_something then expr
          else
            Let_cont {
              body;
              handlers = Nonrecursive { name; handler = {
                handler with handler = handler_body; };
              };
            }
        | Let_cont { body; handlers = Recursive handlers; } ->
          let done_something = ref false in
          let handlers =
            Continuation.Map.mapi (fun name
                    (handler : Flambda.continuation_handler) ->
                let placement : Placement.t = Just_inside_continuation name in
                begin match place ~placement ~around:handler.handler with
                | None -> handler
                | Some handler_body ->
                  done_something := true;
                  { handler with handler = handler_body; }
                end)
              handlers
          in
          let body =
            let placement : Placement.t =
              After_let_cont (Continuation.Map.keys handlers)
            in
            match place ~placement ~around:body with
            | None -> body
            | Some body ->
              done_something := true;
              body
          in
          if not !done_something then expr
          else Let_cont { body; handlers = Recursive handlers; }
        | Apply_cont (cont, trap_action, args) ->
          let key = cont, args in
          begin match
            Continuation.With_args.Map.find key apply_cont_rewrites
          with
          | exception Not_found -> expr
          | new_cont ->
            assert (trap_action = None);
            r := R.forget_inlinable_continuation_uses !r cont ~args;
            Apply_cont (new_cont, None, args)
          end
        | Let_cont { handlers = Alias _; _ }
        | Apply _ | Let_mutable _ | Switch _ | Proved_unreachable -> expr)
      expr
  in
  expr, !r

let for_toplevel_expression expr ~vars_in_scope r ~simplify_let_cont_handlers
      ~backend =
Format.eprintf "Input (with {%a} in scope) to Continuation_specialisation:\n@;%a\n"
  Variable.Set.print vars_in_scope
  Flambda.print expr;
  let new_conts, apply_cont_rewrites =
    find_specialisations r ~simplify_let_cont_handlers ~backend
  in
let output, r =
  insert_specialisations r expr ~vars_in_scope ~new_conts ~apply_cont_rewrites
in
Format.eprintf "Output of Continuation_specialisation:\n@;%a\n"
  Flambda.print output;
output, r
