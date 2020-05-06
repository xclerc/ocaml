module Option = struct
  include Option
  let hash h = function
    | None -> 0
    | Some x -> h x
end

type change_depth = { from : Depth_expr.t; to_ : Depth_expr.t; }

let equal_change_depth
      { from = from_left; to_ = to_left; }
      { from = from_right; to_ = to_right; } =
  Depth_expr.equal from_left from_right
  && Depth_expr.equal to_left to_right

let compare_change_depth
      { from = from_left; to_ = to_left; }
      { from = from_right; to_ = to_right; } =
  let c = Depth_expr.compare from_left from_right in
  if c <> 0 then c
  else Depth_expr.compare to_left to_right

let hash_change_depth { from; to_; } =
  Depth_expr.hash from + Depth_expr.hash to_

let print_change_depth ppf { from; to_; } =
  Format.fprintf ppf "depth: %a->%a" Depth_expr.print from Depth_expr.print to_

let change_depth ~from ~to_ () =
  if Depth_expr.equal from to_ then
    None
  else
    Some { from; to_ }

let compose_change_depth
      ({ from = src; to_ = mid1; } : change_depth)
      ({ from = mid2; to_ = dst; } : change_depth) =
  if Depth_expr.equal mid1 mid2 then
    Or_bottom.Ok (change_depth ~from:src ~to_:dst ())
  else
    Or_bottom.Bottom

let inverse_change_depth { from; to_; } =
  { from = to_; to_ = from; }

let substitute_depths_change_depth subst { from; to_; } =
  let from = Depth_expr.substitute_depths subst from in
  let to_ = Depth_expr.substitute_depths subst to_ in
  { from; to_; }


type change_unroll_to = { from : Depth_expr.t option; to_ : Depth_expr.t option; }

let equal_change_unroll_to
      { from = from_left; to_ = to_left; }
      { from = from_right; to_ = to_right; } =
  Option.equal Depth_expr.equal from_left from_right
  && Option.equal Depth_expr.equal to_left to_right

let compare_change_unroll_to
      { from = from_left; to_ = to_left; }
      { from = from_right; to_ = to_right; } =
  let c = Option.compare Depth_expr.compare from_left from_right in
  if c <> 0 then c
  else Option.compare Depth_expr.compare to_left to_right

let hash_change_unroll_to { from; to_; } =
  Option.hash Depth_expr.hash from + Option.hash Depth_expr.hash to_

let print_change_unroll_to ppf { from; to_; } =
  Format.fprintf ppf "unroll_to: %a->%a"
    (Misc.Stdlib.Option.print Depth_expr.print) from
    (Misc.Stdlib.Option.print Depth_expr.print) to_

let change_unroll_to ~from ~to_ () =
  if Option.equal Depth_expr.equal from to_ then
    None
  else
    Some { from; to_ }

let compose_change_unroll_to
      ({ from = src; to_ = mid1; } : change_unroll_to)
      ({ from = mid2; to_ = dst; } : change_unroll_to) =
  if Option.equal Depth_expr.equal mid1 mid2 then
    Or_bottom.Ok (change_unroll_to ~from:src ~to_:dst ())
  else
    Or_bottom.Bottom

let inverse_change_unroll_to { from; to_; } =
  { from = to_; to_ = from; }

let substitute_depths_change_unroll_to subst { from; to_; } =
  let from = Option.map (Depth_expr.substitute_depths subst) from in
  let to_ = Option.map (Depth_expr.substitute_depths subst) to_ in
  { from; to_; }

type t =
  | Id
  | Change_depth of change_depth
  | Change_unroll_to of change_unroll_to
  | Change_depth_and_unroll_to of {
      change_depth : change_depth;
      change_unroll_to : change_unroll_to;
    }

type descr = {
  change_depth : change_depth option;
  change_unroll_to : change_unroll_to option;
}

let hash = function
  | Id -> 0
  | Change_depth change_depth -> hash_change_depth change_depth
  | Change_unroll_to change_unroll_to -> hash_change_unroll_to change_unroll_to
  | Change_depth_and_unroll_to { change_depth; change_unroll_to; } ->
    hash_change_depth change_depth + hash_change_unroll_to change_unroll_to

let assemble change_depth change_unroll_to =
  match change_depth, change_unroll_to with
  | None, None -> Id
  | Some change_depth, None -> Change_depth change_depth
  | None, Some change_unroll_to -> Change_unroll_to change_unroll_to
  | Some change_depth , Some change_unroll_to ->
    Change_depth_and_unroll_to { change_depth; change_unroll_to }

let id = Id

let is_id = function
  | Id -> true
  | Change_depth _ -> false
  | Change_unroll_to _ -> false
  | Change_depth_and_unroll_to _ -> false

let change_depth_and_unroll_to ~from_depth ~to_depth ~from_unroll_to ~to_unroll_to () =
  assemble
    (change_depth ~from:from_depth ~to_:to_depth ())
    (change_unroll_to ~from:from_unroll_to ~to_:to_unroll_to ())

let change ~f ~wrap =
  fun ~from ~to_ () ->
  f ~from ~to_ ()
  |> Option.fold ~none:Id ~some:wrap

let change_depth =
  change ~f:change_depth ~wrap:(fun cd -> Change_depth cd)

let change_unroll_to =
  change ~f:change_unroll_to ~wrap:(fun cut -> Change_unroll_to cut)

let descr t =
  let change_depth, change_unroll_to =
    match t with
    | Id -> None, None
    | Change_depth change_depth -> Some change_depth, None
    | Change_unroll_to change_unroll_to -> None, Some change_unroll_to
    | Change_depth_and_unroll_to { change_depth; change_unroll_to; } ->
      Some change_depth, Some change_unroll_to in
  { change_depth; change_unroll_to; }

let print ppf t =
  let { change_depth; change_unroll_to; } = descr t in
  Format.fprintf ppf "%a %a"
    (Misc.Stdlib.Option.print print_change_depth) change_depth
    (Misc.Stdlib.Option.print print_change_unroll_to) change_unroll_to

let compare left right =
  let { change_depth = change_depth_left; change_unroll_to = change_unroll_to_left; } =
    descr left in
  let { change_depth =change_depth_right; change_unroll_to = change_unroll_to_right; } =
    descr right in
  let c = Option.compare compare_change_depth change_depth_left change_depth_right in
  if c <> 0 then c
  else Option.compare compare_change_unroll_to change_unroll_to_left change_unroll_to_right

let equal left right =
  let { change_depth = change_depth_left; change_unroll_to = change_unroll_to_left; } =
    descr left in
  let { change_depth =change_depth_right; change_unroll_to = change_unroll_to_right; } =
    descr right in
  Option.equal equal_change_depth change_depth_left change_depth_right
  && Option.equal equal_change_unroll_to change_unroll_to_left change_unroll_to_right

let compose left right =
  let { change_depth = change_depth_left; change_unroll_to = change_unroll_to_left; } =
    descr left in
  let { change_depth =change_depth_right; change_unroll_to = change_unroll_to_right; } =
    descr right in
  let map2 f left right =
    match left, right with
    | None, None -> Or_bottom.Ok None
    | None, Some _ -> Or_bottom.Ok right
    | Some _, None -> Or_bottom.Ok left
    | Some left, Some right -> f left right
  in
  Or_bottom.both ~f:assemble
    (map2 compose_change_depth change_depth_left change_depth_right)
    (map2 compose_change_unroll_to change_unroll_to_left change_unroll_to_right)

let inverse = function
  | Id -> Id
  | Change_depth cd -> Change_depth (inverse_change_depth cd)
  | Change_unroll_to cut -> Change_unroll_to (inverse_change_unroll_to cut)
  | Change_depth_and_unroll_to {
    change_depth = cd;
    change_unroll_to = cut;
  } ->
    Change_depth_and_unroll_to {
      change_depth = inverse_change_depth cd;
      change_unroll_to = inverse_change_unroll_to cut;
    }

let substitute_depths subst t =
  match t with
  | Id -> Id
  | Change_depth cd -> Change_depth (substitute_depths_change_depth subst cd)
  | Change_unroll_to cu -> Change_unroll_to (substitute_depths_change_unroll_to subst cu)
  | Change_depth_and_unroll_to { change_depth; change_unroll_to; } ->
    let change_depth = substitute_depths_change_depth subst change_depth in
    let change_unroll_to = substitute_depths_change_unroll_to subst change_unroll_to in
    Change_depth_and_unroll_to { change_depth; change_unroll_to; }
