type change_depth = { from : Depth_expr.t; to_ : Depth_expr.t; }

type change_unroll_to = { from : Depth_expr.t option; to_ : Depth_expr.t option; }

type t

type descr = {
  change_depth : change_depth option;
  change_unroll_to : change_unroll_to option;
}

val print : Format.formatter -> t -> unit

val equal : t -> t -> bool

val compare : t -> t -> int

val hash : t -> int

val descr : t -> descr

val id : t

val is_id : t -> bool

val change_depth : from:Depth_expr.t -> to_:Depth_expr.t -> unit -> t

val change_unroll_to : from:Depth_expr.t option -> to_:Depth_expr.t option -> unit -> t

val change_depth_and_unroll_to : from_depth:Depth_expr.t -> to_depth:Depth_expr.t -> from_unroll_to:Depth_expr.t option -> to_unroll_to:Depth_expr.t option -> unit -> t

val compose : t -> t -> t Or_bottom.t

val inverse : t -> t

val substitute_depths : (Depth_variable.t -> Depth_expr.t) -> t -> t
