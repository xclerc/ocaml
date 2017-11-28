(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2016 OCamlPro SAS                                    *)
(*   Copyright 2014--2016 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

module Int_base = Identifiable.Make (struct
  type t = int

  let compare x y = x - y
  let hash i = i
  let equal (i : int) j = i = j
  let print = Format.pp_print_int
end)

module Int = struct
  type t = int

  include Int_base

  let rec zero_to_n n =
    if n < 0 then Set.empty else Set.add n (zero_to_n (n-1))
end

module Int8 = struct
  type t = int

  let zero = 0
  let one = 1

  let of_int_exn i =
    if i < -(1 lsl 7) || i > ((1 lsl 7) - 1) then
      Misc.fatal_errorf "Int8.of_int_exn: %d is out of range" i
    else
      i

  let to_int i = i
end

module Int16 = struct
  type t = int

  let of_int_exn i =
    if i < -(1 lsl 15) || i > ((1 lsl 15) - 1) then
      Misc.fatal_errorf "Int16.of_int_exn: %d is out of range" i
    else
      i

  let lower_int64 = Int64.neg (Int64.shift_left Int64.one 15)
  let upper_int64 = Int64.sub (Int64.shift_left Int64.one 15) Int64.one

  let of_int64_exn i =
    if Int64.compare i lower_int64 < 0
        || Int64.compare i upper_int64 > 0
    then
      Misc.fatal_errorf "Int16.of_int64_exn: %Ld is out of range" i
    else
      Int64.to_int i

  let to_int t = t
end

module Float_by_bit_pattern = struct
  type t = Int64.t

  let create f = Int64.bits_of_float f

  let to_float t = Int64.float_of_bits t

  include Identifiable.Make (struct
    type t = Int64.t

    let compare = Int64.compare
    let equal = Int64.equal
    let hash f = Hashtbl.hash f
    let print ppf t = Format.pp_print_float ppf (Int64.float_of_bits f)
  end)

  let add t1 t2 = create (Pervasives.(+.) (to_float t1) (to_float t2))
  let sub t1 t2 = create (Pervasives.(-.) (to_float t1) (to_float t2))
  let mul t1 t2 = create (Pervasives.( *. ) (to_float t1) (to_float t2))
  let div t1 t2 = create (Pervasives.(/.) (to_float t1) (to_float t2))

  let neg t = create (Pervasives.(~-.) (to_float t))
  let abs t = create (Pervasives.abs_float (to_float t))

  let compare_ieee t1 t2 =
    Pervasives.compare (to_float t1) (to_float t2)

  let equal_ieee t1 t2 = 
    (* N.B. This can't just be defined in terms of [compare_ieee]! *)
    Pervasives.(=) (to_float t1) (to_float t2)
end

module Int32 = struct
  type t = Int32.t

  external byte_swap : t -> t = "%bswap_int32"

  include Identifiable.Make (struct
    type t = Int32.t

    let compare x y = Int32.compare x y
    let hash f = Hashtbl.hash f
    let equal (i : Int32.t) j = i = j
    let print ppf t = Format.fprintf ppf "%ld" t
  end)
end

module Int64 = struct
  type t = Int64.t

  external byte_swap : t -> t = "%bswap_int64"

  include Identifiable.Make (struct
    type t = Int64.t

    let compare x y = Int64.compare x y
    let hash f = Hashtbl.hash f
    let equal (i : Int64.t) j = i = j
    let print ppf t = Format.fprintf ppf "%Ld" t
  end)
end

module Nativeint = struct
  type t = Nativeint.t

  external byte_swap : t -> t = "%bswap_native"

  include Identifiable.Make (struct
    type t = Nativeint.t

    let compare x y = Nativeint.compare x y
    let hash f = Hashtbl.hash f
    let equal (i : Nativeint.t) j = i = j
    let print ppf t = Format.fprintf ppf "%nd" t
  end)
end
