(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-30-40-41-42"]

module TE = Typing_env
module TEE = Typing_env_extension

module Inlinable = struct
  type t = {
    code_id : Code_id.t;
    dbg : Debuginfo.t;
    coercion : Coercion.t;
    is_tupled : bool;
  }

  let print ppf { code_id; dbg; coercion; is_tupled; } =
    Format.fprintf ppf
      "@[<hov 1>(Inlinable@ \
        @[<hov 1>(code_id@ %a)@]@ \
        @[<hov 1>(dbg@ %a)@] \
        @[<hov 1>(coercion@ %a)@]\
        @[<hov 1><is_tupled@ %b)@]\
        )@]"
      Code_id.print code_id
      Debuginfo.print_compact dbg
      Coercion.print coercion
      is_tupled

  let create ~code_id ~dbg ~coercion ~is_tupled =
    { code_id;
      dbg;
      coercion;
      is_tupled;
    }

  let code_id t = t.code_id
  let dbg t = t.dbg
  let coercion t = t.coercion
  let is_tupled t = t.is_tupled
end

module Non_inlinable = struct
  type t = {
    code_id : Code_id.t;
    is_tupled : bool;
  }

  let print ppf { code_id; is_tupled; } =
    Format.fprintf ppf
      "@[<hov 1>(Non_inlinable@ \
        @[<hov 1>(code_id@ %a)@]@ \
        @[<hov 1>(is_tupled@ %b)@]\
        )@]"
      Code_id.print code_id
      is_tupled

  let create ~code_id ~is_tupled =
    { code_id;
      is_tupled;
    }

  let code_id t = t.code_id
  let is_tupled t = t.is_tupled
end

type t0 =
  | Inlinable of Inlinable.t
  | Non_inlinable of Non_inlinable.t

type t = t0 Or_unknown_or_bottom.t

let print_t0 ppf t0 =
  match t0 with
  | Inlinable inlinable -> Inlinable.print ppf inlinable
  | Non_inlinable non_inlinable -> Non_inlinable.print ppf non_inlinable

let print_with_cache ~cache:_ ppf t =
  Or_unknown_or_bottom.print print_t0 ppf t

let print ppf t =
  Or_unknown_or_bottom.print print_t0 ppf t

let free_names (t : t) =
  match t with
  | Bottom | Unknown -> Name_occurrences.empty
  | Ok (Inlinable { code_id; dbg = _; coercion = _; is_tupled = _; })
  | Ok (Non_inlinable { code_id; is_tupled = _; }) ->
    Name_occurrences.add_code_id Name_occurrences.empty code_id
      Name_mode.in_types

let all_ids_for_export (t : t) =
  match t with
  | Bottom | Unknown -> Ids_for_export.empty
  | Ok (Inlinable { code_id; dbg = _; coercion = _; is_tupled = _; })
  | Ok (Non_inlinable { code_id; is_tupled = _; }) ->
    Ids_for_export.add_code_id Ids_for_export.empty code_id

let import import_map (t : t) : t =
  match t with
  | Bottom | Unknown -> t
  | Ok (Inlinable { code_id; dbg; coercion; is_tupled; }) ->
    let code_id = Ids_for_export.Import_map.code_id import_map code_id in
    Ok (Inlinable { code_id; dbg; coercion; is_tupled; })
  | Ok (Non_inlinable { code_id; is_tupled; }) ->
    let code_id = Ids_for_export.Import_map.code_id import_map code_id in
    Ok (Non_inlinable { code_id; is_tupled; })

let apply_name_permutation t _perm = t

module Make_meet_or_join
  (E : Lattice_ops_intf.S
   with type meet_env := Meet_env.t
   with type meet_or_join_env := Meet_or_join_env.t
   with type typing_env := Typing_env.t
   with type typing_env_extension := Typing_env_extension.t) =
struct
  let meet_or_join (env : Meet_or_join_env.t) (t1 : t) (t2 : t)
        : (t * TEE.t) Or_bottom.t =
    match t1, t2 with
    (* CR mshinwell: Try to factor out "Or_unknown_or_bottom" handling from here
       and elsewhere *)
    | Bottom, Bottom -> Ok (Bottom, TEE.empty ())
    | Bottom, _ ->
      begin match E.op () with
      | Meet -> Ok (Bottom, TEE.empty ())
      | Join -> Ok (t2, TEE.empty ())
      end
    | _, Bottom ->
      begin match E.op () with
      | Meet -> Ok (Bottom, TEE.empty ())
      | Join -> Ok (t1, TEE.empty ())
      end
    | Unknown, Unknown -> Ok (Unknown, TEE.empty ())
    | Unknown, _ ->
      begin match E.op () with
      | Meet -> Ok (t2, TEE.empty ())
      | Join -> Ok (Unknown, TEE.empty ())
      end
    | _, Unknown ->
      begin match E.op () with
      | Meet -> Ok (t1, TEE.empty ())
      | Join -> Ok (Unknown, TEE.empty ())
      end
    | Ok (Non_inlinable {
        code_id = code_id1; is_tupled = is_tupled1;
      }), Ok (Non_inlinable {
        code_id = code_id2; is_tupled = is_tupled2;
      }) ->
      let typing_env = Meet_or_join_env.target_join_env env in
      let target_code_age_rel = TE.code_age_relation typing_env in
      let resolver = TE.code_age_relation_resolver typing_env in
      let check_other_things_and_return code_id : (t * TEE.t) Or_bottom.t =
        assert (Bool.equal is_tupled1 is_tupled2);
        Ok (Ok (Non_inlinable {
            code_id;
            is_tupled = is_tupled1;
          }),
          TEE.empty ())
      in
      begin match E.op () with
      | Meet ->
        begin match
          Code_age_relation.meet target_code_age_rel ~resolver code_id1 code_id2
        with
        | Ok code_id -> check_other_things_and_return code_id
        | Bottom -> Bottom
        end
      | Join ->
        let code_age_rel1 =
          TE.code_age_relation (Meet_or_join_env.left_join_env env)
        in
        let code_age_rel2 =
          TE.code_age_relation (Meet_or_join_env.right_join_env env)
        in
        begin match
          Code_age_relation.join ~target_t:target_code_age_rel ~resolver
            code_age_rel1 code_age_rel2 code_id1 code_id2
        with
        | Known code_id -> check_other_things_and_return code_id
        | Unknown -> Ok (Unknown, TEE.empty ())
        end
      end
    | Ok (Non_inlinable _), Ok (Inlinable _)
    | Ok (Inlinable _), Ok (Non_inlinable _) ->
      (* CR mshinwell: This should presumably return [Non_inlinable] if
         the arities match. *)
      Ok (Unknown, TEE.empty ())
    | Ok (Inlinable {
        code_id = code_id1;
        dbg = dbg1;
        coercion = _coercion1;
        is_tupled = is_tupled1;
      }),
      Ok (Inlinable {
        code_id = code_id2;
        dbg = dbg2;
        coercion = _coercion2;
        is_tupled = is_tupled2;
      }) ->
      let typing_env = Meet_or_join_env.target_join_env env in
      let target_code_age_rel = TE.code_age_relation typing_env in
      let resolver = TE.code_age_relation_resolver typing_env in
      let check_other_things_and_return code_id : (t * TEE.t) Or_bottom.t =
        assert (Int.equal (Debuginfo.compare dbg1 dbg2) 0);
        assert (Bool.equal is_tupled1 is_tupled2);
        Ok (Ok (Inlinable {
            code_id;
            dbg = dbg1;
            coercion = _coercion1;
            is_tupled = is_tupled1;
          }),
          TEE.empty ())
      in
      (* CR mshinwell: What about [coercion]? *)
      match E.op () with
      | Meet ->
        begin match
          Code_age_relation.meet target_code_age_rel ~resolver code_id1 code_id2
        with
        | Ok code_id -> check_other_things_and_return code_id
        | Bottom -> Bottom
        end
      | Join ->
        let code_age_rel1 =
          TE.code_age_relation (Meet_or_join_env.left_join_env env)
        in
        let code_age_rel2 =
          TE.code_age_relation (Meet_or_join_env.right_join_env env)
        in
        begin match
          Code_age_relation.join ~target_t:target_code_age_rel ~resolver
            code_age_rel1 code_age_rel2 code_id1 code_id2
        with
        | Known code_id -> check_other_things_and_return code_id
        | Unknown -> Ok (Unknown, TEE.empty ())
        end
end

module Meet = Make_meet_or_join (Lattice_ops.For_meet)
module Join = Make_meet_or_join (Lattice_ops.For_join)

let meet env t1 t2 : _ Or_bottom.t =
  let env = Meet_or_join_env.create_for_meet env in
  match Meet.meet_or_join env t1 t2 with
  | Bottom | Ok (Bottom, _) -> Bottom
  | Ok ((Ok _ | Unknown) as t, env_extension) -> Ok (t, env_extension)

let join env t1 t2 : t =
(*
  Format.eprintf "FDT.join:@ %a@ and@ %a@ in:@ %a\n%!"
    print t1 print t2
    Meet_or_join_env.print env;
    *)
  match Join.meet_or_join env t1 t2 with
  | Bottom | Ok (Bottom, _) -> Bottom
  | Ok ((Ok _ | Unknown) as t, env_extension) ->
    assert (TEE.is_empty env_extension);
    t

let apply_coercion (t : t) coercion : t Or_bottom.t =
  match t with
  | Ok (Inlinable { code_id; dbg; coercion = coercion'; is_tupled; }) ->
    let coercion = Coercion.compose coercion' ~newer:coercion in
    Ok (Ok (Inlinable { code_id;
      dbg;
      coercion;
      is_tupled;
    }))
  | Ok (Non_inlinable { code_id = _; is_tupled = _; }) -> Ok t
  | Unknown | Bottom -> Ok t
