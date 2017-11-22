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

type t = {
  sets_of_closures : Flambda.Function_declarations.t Set_of_closures_id.Map.t;
  closures : Flambda.Function_declarations.t Closure_id.Map.t;
  values : Flambda_type.t Export_id.Map.t Compilation_unit.Map.t;
  symbol_id : Export_id.t Symbol.Map.t;
  offset_fun : int Closure_id.Map.t;
  offset_fv : int Var_within_closure.Map.t;
  constant_sets_of_closures : Set_of_closures_id.Set.t;
  invariant_params : Variable.Set.t Variable.Map.t Set_of_closures_id.Map.t;
}

let empty : t = {
  sets_of_closures = Set_of_closures_id.Map.empty;
  closures = Closure_id.Map.empty;
  values = Compilation_unit.Map.empty;
  symbol_id = Symbol.Map.empty;
  offset_fun = Closure_id.Map.empty;
  offset_fv = Var_within_closure.Map.empty;
  constant_sets_of_closures = Set_of_closures_id.Set.empty;
  invariant_params = Set_of_closures_id.Map.empty;
}

let create ~sets_of_closures ~closures ~values ~symbol_id
      ~offset_fun ~offset_fv ~constant_sets_of_closures
      ~invariant_params =
  { sets_of_closures;
    closures;
    values;
    symbol_id;
    offset_fun;
    offset_fv;
    constant_sets_of_closures;
    invariant_params;
  }

let print_all _ = assert false
let print_offsets _ = assert false
let print_functions _ = assert false
let print_approx _ = assert false
let nest_eid_map _ = assert false
let merge _ = assert false
let add_clambda_info _ = assert false
let find_description _ = assert false

(* let add_clambda_info t ~offset_fun ~offset_fv ~constant_sets_of_closures = *)
(*   assert (Closure_id.Map.cardinal t.offset_fun = 0); *)
(*   assert (Var_within_closure.Map.cardinal t.offset_fv = 0); *)
(*   assert (Set_of_closures_id.Set.cardinal t.constant_sets_of_closures = 0); *)
(*   { t with offset_fun; offset_fv; constant_sets_of_closures; } *)

(* let merge (t1 : t) (t2 : t) : t = *)
(*   let eidmap_disjoint_union ?eq map1 map2 = *)
(*     Compilation_unit.Map.merge (fun _id map1 map2 -> *)
(*         match map1, map2 with *)
(*         | None, None -> None *)
(*         | None, Some map *)
(*         | Some map, None -> Some map *)
(*         | Some map1, Some map2 -> *)
(*           Some (Export_id.Map.disjoint_union ?eq map1 map2)) *)
(*       map1 map2 *)
(*   in *)
(*   let int_eq (i : int) j = i = j in *)
(*   { values = eidmap_disjoint_union ~eq:equal_descr t1.values t2.values; *)
(*     sets_of_closures = *)
(*       Set_of_closures_id.Map.disjoint_union t1.sets_of_closures *)
(*         t2.sets_of_closures; *)
(*     closures = Closure_id.Map.disjoint_union t1.closures t2.closures; *)
(*     symbol_id = Symbol.Map.disjoint_union ~print:Export_id.print t1.symbol_id t2.symbol_id; *)
(*     offset_fun = Closure_id.Map.disjoint_union *)
(*         ~eq:int_eq t1.offset_fun t2.offset_fun; *)
(*     offset_fv = Var_within_closure.Map.disjoint_union *)
(*         ~eq:int_eq t1.offset_fv t2.offset_fv; *)
(*     constant_sets_of_closures = *)
(*       Set_of_closures_id.Set.union t1.constant_sets_of_closures *)
(*         t2.constant_sets_of_closures; *)
(*     invariant_params = *)
(*       Set_of_closures_id.Map.disjoint_union *)
(*         ~print:(Variable.Map.print Variable.Set.print) *)
(*         ~eq:(Variable.Map.equal Variable.Set.equal) *)
(*         t1.invariant_params t2.invariant_params; *)
(*   } *)

(* let find_value eid map = *)
(*   let unit_map = *)
(*     Compilation_unit.Map.find (Export_id.get_compilation_unit eid) map *)
(*   in *)
(*   Export_id.Map.find eid unit_map *)

(* let find_description (t : t) eid = *)
(*   find_value eid t.values *)

(* let nest_eid_map map = *)
(*   let add_map eid v map = *)
(*     let unit = Export_id.get_compilation_unit eid in *)
(*     let m = *)
(*       try Compilation_unit.Map.find unit map *)
(*       with Not_found -> Export_id.Map.empty *)
(*     in *)
(*     Compilation_unit.Map.add unit (Export_id.Map.add eid v m) map *)
(*   in *)
(*   Export_id.Map.fold add_map map Compilation_unit.Map.empty *)
