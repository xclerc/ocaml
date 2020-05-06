type t =
  | Zero
  | Succ of t
  | Variable of Depth_variable.t

let print ppf t =
  let rec print ppf k = function
    | Zero -> Format.fprintf ppf "%d" k
    | Succ d -> print ppf (succ k) d
    | Variable v ->
      if k = 0 then
        Depth_variable.print ppf v
      else
        Format.fprintf ppf "%a+%d" Depth_variable.print v k
  in
  print ppf 0 t

let rec compare left right =
  match left, right with
  | Zero, Zero -> 0
  | Succ left, Succ right -> compare left right
  | Variable left, Variable right -> Depth_variable.compare left right
  | Zero, (Succ _ | Variable _) -> -1
  | Succ _, Zero -> 1
  | Succ _, Variable _ -> -1
  | Variable _, (Zero | Succ _) -> 1

let rec equal left right =
  match left, right with
  | Zero, Zero -> true
  | Succ left, Succ right -> equal left right
  | Variable left, Variable right -> Depth_variable.equal left right
  | Zero, (Succ _ | Variable _)
  | Succ _, (Zero | Variable _)
  | Variable _, (Zero | Succ _) ->
    false

let rec hash = function
  | Zero -> 0
  | Succ d -> 1 + hash d
  | Variable v -> Depth_variable.hash v

let rec substitute_depths subst = function
  | Zero -> Zero
  | Succ d -> Succ (substitute_depths subst d)
  | Variable v -> subst v
