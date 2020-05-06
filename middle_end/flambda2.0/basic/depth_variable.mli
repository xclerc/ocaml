type t

val create : string -> t

include Identifiable.S with type t := t
