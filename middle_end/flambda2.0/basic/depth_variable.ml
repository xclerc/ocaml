let next_id = ref 0

type t = string

let create name = incr next_id; Printf.sprintf "%s_%d" name !next_id

module With_map = Identifiable.Make (struct
    type nonrec t = t
    let print ppf t = Format.fprintf ppf "%s" t
    let output chan t = print (Format.formatter_of_out_channel chan) t
    let hash = Hashtbl.hash
    let compare = String.compare
    let equal = String.equal
  end)

module T = With_map.T

let compare = T.compare

let equal t1 t2 = T.compare t1 t2 = 0

let print = T.print

let output = T.output

let hash = T.hash

module Map = With_map.Map

module Set = With_map.Set

module Tbl = With_map.Tbl
