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

(** Annotate Mach instructions with the stack of trap handlers (from the
    current function) in scope at each program point.

    This is needed by [Liveness] and [Spill] to avoid a circularity (see
    comment in [Liveness].  It is also needed by [Linearize] to emit trap
    depth adjustment directives.  The order in which code is traversed
    during [Linearize] prohibits calculating this information in the same
    pass (and in any case, it would be redundant work). *)

val run : Mach.fundecl -> Mach.fundecl
