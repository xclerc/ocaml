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

(** Construct Flambda types from export information in .cmx files. *)

(** Given an approximation description, load .cmx files (possibly more
    than one) until the description is fully resolved.  If a necessary .cmx
    file cannot be found, "unresolved" will be returned. *)
(*
val really_import : Flambda_type0.descr -> Flambda_type0.descr
*)
(* CR mshinwell: update comments etc *)

(** Maps the description of the given approximation through [really_import]. *)
val import_type : Flambda_type0.t -> Flambda_type0.t

(** Read and convert the approximation of a given symbol from the
    relevant .cmx file.  Unlike the "really_" functions, this does not
    continue to load .cmx files until the approximation is fully
    resolved. *)
val import_symbol : Symbol.t -> Flambda_type0.t
