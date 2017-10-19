let f x =
  match x with
  | 0 -> true
  | _ -> false
  | exception Not_found -> false

let g x y =
  match x.contents, Some y with
  | 0, _ -> true
  | _ -> false
  | exception Not_found -> false
