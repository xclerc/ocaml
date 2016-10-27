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

(** Preparation of [Lambda] code before CPS and closure conversion:
    - Compilation of Lsequence to Llet
    - Compilation of Lfor and Lwhile to Lstaticcatch / Lstaticraise
    - Compilation of Lifthenelse to Lswitch
    - Splitting of Lletrec into three parts (block initialisation, closure
      creation, block patching-up)
    - Marking of default argument wrappers as stubs
*)

val run : Lambda.lambda -> Lambda.lambda
