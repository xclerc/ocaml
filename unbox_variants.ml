external ( < ) : 'a -> 'a -> bool = "%lessthan"
external ( > ) : 'a -> 'a -> bool = "%greaterthan"
external ( + ) : int -> int -> int = "%addint"
external ( - ) : int -> int -> int = "%subint"
external fst : 'a * 'b -> 'a = "%field0"
external snd : 'a * 'b -> 'b = "%field1"

type 'a variant =
  | A
  | B of 'a
  | C of int * int

let foo x y z f c =
  let i =
    if x < 42 then A
    else if x > 100 then C (3, 4)
    else B (y + z)
  in
  (* start of arbitrary large block of code *)
  let clos1 a b = c, a, b, a, b, a, b, a, b in
  let clos2 a b = c, a, b, a, b, a, b, a, b in
  let clos3 a b = c, a, b, a, b, a, b, a, b in
  let clos4 a b = c, a, b, a, b, a, b, a, b in
  let clos5 a b = c, a, b, a, b, a, b, a, b in
  let clos6 a b = c, a, b, a, b, a, b, a, b in
  let clos7 a b = c, a, b, a, b, a, b, a, b in
  let clos8 a b = c, a, b, a, b, a, b, a, b in
  let clos9 a b = c, a, b, a, b, a, b, a, b in
  let clos10 a b = c, a, b, a, b, a, b, a, b in
  let block =
    clos1, clos2, clos3, clos4, clos5, clos6,
      clos7, clos8, clos9, clos10
  in
  (* end of arbitrary large block of code *)
  let a =
    match i with
    | A -> 42
    | B i -> i + 4
    | C x -> x + 3
  in
  block, a
