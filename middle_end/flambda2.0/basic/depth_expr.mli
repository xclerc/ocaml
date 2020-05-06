type t =
  | Zero
  | Succ of t
  | Variable of Depth_variable.t

val print : Format.formatter -> t -> unit

val equal : t -> t -> bool

val compare : t -> t -> int

val hash : t -> int

val substitute_depths : (Depth_variable.t -> t) -> t -> t
