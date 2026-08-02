(** This module implements "Fast Splittable Pseudorandom Number Generators" by Steele et.
    al. (1).  The paper's algorithm provides decent randomness for most purposes, but
    sacrifices cryptographic-quality randomness in favor of performance.  The original
    implementation was tested with DieHarder and BigCrush; see the paper for details.

    Our implementation is a port from Java to OCaml of the paper's algorithm.  Other than
    the choice of initial seed for [create], our port should be faithful.  We have not
    re-run the DieHarder or BigCrush tests on our implementation.  Our port is also not as
    performant as the original; two factors that hurt us are boxed [int64] values and lack
    of a POPCNT primitive.

    (1) http://2014.splashcon.org/event/oopsla2014-fast-splittable-pseudorandom-number-generators
    (also mirrored at http://gee.cs.oswego.edu/dl/papers/oopsla14.pdf)

    Beware when implementing this interface; it is easy to implement a [split] operation
    whose output is not as "independent" as it seems (2).  This bug caused problems for
    Haskell's Quickcheck library for a long time.

    (2) Schaathun, "Evaluation of splittable pseudo-random generators", JFP 2015.
    http://www.hg.schaathun.net/research/Papers/hgs2015jfp.pdf
*)

open! Base
(* Compat shim (see vendor/sr_real/dune comment): Base v0.18 preview
   drops the bitwise operators from Int64.O and changes popcount. *)
let int64_popcount (x : int64) : int =
  let n = ref 0 in
  let v = ref x in
  for _ = 0 to 63 do
    if Int64.( <> ) (Int64.bit_and !v 1L) 0L then Int.incr n;
    v := Int64.shift_right_logical !v 1
  done;
  !n

open Int64.O

let ( lxor ) = Int64.bit_xor
let ( lor ) = Int64.bit_or
let ( land ) = Int64.bit_and
let _ = ( land ) (* used only on some Base versions *)
let ( lsr ) x n = Int64.shift_right_logical x n

let is_odd x = x lor 1L = x
let popcount = int64_popcount

type t =
  { mutable seed : int64
  ; odd_gamma : int64
  ; mutable intercept : intercept option
  }

(* Interception hooks for property-testing engines (see the [Intercept]
   module below). [None] is the default and costs one branch per draw.

   Seam v2 (design/stream-keyed-tapes.md): [on_split] returns the
   hooks for the freshly split state ([None] keeps it hook-free), and
   [on_perturb] receives the salt and may return replacement hooks for
   this state ([None] keeps the current hooks). This is what lets an
   engine give split-off streams their own identity, so generated
   functions shrink; the submitted upstream PR carries the v1
   unit-returning signatures. *)
and intercept =
  { int64 :
      t -> lo:int64 -> hi:int64 -> default:(t -> lo:int64 -> hi:int64 -> int64) -> int64
  ; float :
      t -> lo:float -> hi:float -> default:(t -> lo:float -> hi:float -> float) -> float
  ; unit_float : t -> default:(t -> float) -> float
  ; bool : t -> default:(t -> bool) -> bool
  ; on_split : unit -> intercept option
  ; on_perturb : int -> intercept option
  }

(* Alias used below when [t] is shadowed. *)
type state = t

let golden_gamma = 0x9e37_79b9_7f4a_7c15L
let of_int seed =
  { seed = Int64.of_int seed; odd_gamma = golden_gamma; intercept = None }
;;

let copy { seed; odd_gamma; intercept } = { seed; odd_gamma; intercept }
let mix_bits z n = z lxor (z lsr n)

let mix64 z =
  let z = mix_bits z 33 * 0xff51_afd7_ed55_8ccdL in
  let z = mix_bits z 33 * 0xc4ce_b9fe_1a85_ec53L in
  mix_bits z 33
;;

let mix64_variant13 z =
  let z = mix_bits z 30 * 0xbf58_476d_1ce4_e5b9L in
  let z = mix_bits z 27 * 0x94d0_49bb_1331_11ebL in
  mix_bits z 31
;;

let mix_odd_gamma z =
  let z = mix64_variant13 z lor 1L in
  let n = popcount (z lxor (z lsr 1)) in
  (* The original paper uses [>=] in the conditional immediately below; however this is
     a typo, and we correct it by using [<]. This was fixed in response to [1] and [2].

     [1] https://github.com/janestreet/splittable_random/issues/1
     [2] http://www.pcg-random.org/posts/bugs-in-splitmix.html
  *)
  if Int.( < ) n 24 then z lxor 0xaaaa_aaaa_aaaa_aaaaL else z
;;


let next_seed t =
  let next = t.seed + t.odd_gamma in
  t.seed <- next;
  next
;;

let of_seed_and_gamma ~seed ~gamma =
  let seed = mix64 seed in
  let odd_gamma = mix_odd_gamma gamma in
  { seed; odd_gamma; intercept = None }
;;

let random_int64 random_state =
  Random.State.int64_incl random_state Int64.min_value Int64.max_value
;;

let create random_state =
  let seed = random_int64 random_state in
  let gamma = random_int64 random_state in
  of_seed_and_gamma ~seed ~gamma
;;

let split t =
  let child_hooks =
    match t.intercept with
    | None -> None
    | Some i -> i.on_split ()
  in
  let seed = next_seed t in
  let gamma = next_seed t in
  let child = of_seed_and_gamma ~seed ~gamma in
  child.intercept <- child_hooks;
  child
;;

let next_int64 t = mix64 (next_seed t)

(* [perturb] is not from any external source, but provides a way to mix in external
   entropy with a pseudo-random state. *)
let perturb t salt =
  (match t.intercept with
   | None -> ()
   | Some i ->
     (match i.on_perturb salt with
      | None -> ()
      | Some hooks -> t.intercept <- Some hooks));
  let next = t.seed + mix64 (Int64.of_int salt) in
  t.seed <- next
;;

let bool_default state = is_odd (next_int64 state)

let bool state =
  match state.intercept with
  | None -> bool_default state
  | Some i -> i.bool state ~default:bool_default
;;

(* We abuse terminology and refer to individual values as biased or unbiased.  More
   properly, what is unbiased is the sampler that results if we keep only these "unbiased"
   values. *)
let remainder_is_unbiased ~draw ~remainder ~draw_maximum ~remainder_maximum =
  let open Int64.O in
  draw - remainder <= draw_maximum - remainder_maximum
;;


(* This implementation of bounded randomness is adapted from [Random.State.int*] in the
   OCaml standard library.  The purpose is to use the minimum number of calls to
   [next_int64] to produce a number uniformly chosen within the given range. *)
let int64_default =
  let open Int64.O in
  let rec between state ~lo ~hi =
    let draw = next_int64 state in
    if lo <= draw && draw <= hi then draw else between state ~lo ~hi
  in
  let rec non_negative_up_to state maximum =
    let draw = next_int64 state land Int64.max_value in
    let remainder = Int64.rem draw (Int64.succ maximum) in
    if remainder_is_unbiased
         ~draw
         ~remainder
         ~draw_maximum:Int64.max_value
         ~remainder_maximum:maximum
    then remainder
    else non_negative_up_to state maximum
  in
  fun state ~lo ~hi ->
    if lo > hi
    then Error.raise_s [%message "int64: crossed bounds" (lo : int64) (hi : int64)];
    let diff = hi - lo in
    if diff = Int64.max_value
    then (next_int64 state land Int64.max_value) + lo
    else if diff >= 0L
    then non_negative_up_to state diff + lo
    else between state ~lo ~hi
;;

let int64 state ~lo ~hi =
  match state.intercept with
  | None -> int64_default state ~lo ~hi
  | Some i -> i.int64 state ~lo ~hi ~default:int64_default
;;

let int state ~lo ~hi =
  let lo = Int64.of_int lo in
  let hi = Int64.of_int hi in
  (* truncate unneeded bits *)
  Int64.to_int_trunc (int64 state ~lo ~hi)
;;

let int32 state ~lo ~hi =
  let lo = Int64.of_int32 lo in
  let hi = Int64.of_int32 hi in
  (* truncate unneeded bits *)
  Int64.to_int32_trunc (int64 state ~lo ~hi)
;;

let nativeint state ~lo ~hi =
  let lo = Int64.of_nativeint lo in
  let hi = Int64.of_nativeint hi in
  (* truncate unneeded bits *)
  Int64.to_nativeint_trunc (int64 state ~lo ~hi)
;;

let int63 state ~lo ~hi =
  let lo = Int63.to_int64 lo in
  let hi = Int63.to_int64 hi in
  (* truncate unneeded bits *)
  Int63.of_int64_trunc (int64 state ~lo ~hi)
;;

let double_ulp = 2. **. -53.


let unit_float_from_int64 int64 = Int64.to_float (int64 lsr 11) *. double_ulp


let unit_float_default state = unit_float_from_int64 (next_int64 state)

let unit_float state =
  match state.intercept with
  | None -> unit_float_default state
  | Some i -> i.unit_float state ~default:unit_float_default
;;

(* Note about roundoff error:

   Although [float state ~lo ~hi] is nominally inclusive of endpoints, we are relying on
   the fact that [unit_float] never returns 1., because there are pairs [(lo,hi)] for
   which [lo +. 1. *. (hi -. lo) > hi].  There are also pairs [(lo,hi)] and values of [x]
   with [x < 1.] such that [lo +. x *. (hi -. lo) = hi], so it would not be correct to
   document this as being exclusive of [hi].
*)
let float_default =
  (* Uses the [_default] internals: when a hook delegates to [default],
     the fallback must not re-enter the hooks, or a single [float] draw
     would be observed twice (once whole, once as its internal
     [unit_float]/[bool] draws). *)
  let rec finite_float state ~lo ~hi =
    let range = hi -. lo in
    if Float.is_finite range
    then lo +. (unit_float_default state *. range)
    else (
      (* If [hi - lo] is infinite, then [hi + lo] is finite because [hi] and [lo] have
         opposite signs. *)
      let mid = (hi +. lo) /. 2. in
      if bool_default state
         (* Depending on rounding, the recursion with [~hi:mid] might be inclusive of [mid],
         which would mean the two cases overlap on [mid]. The alternative is to increment
         or decrement [mid] using [one_ulp] in either of the calls, but then if the first
         case is exclusive we leave a "gap" between the two ranges. There's no perfectly
         uniform solution, so we use the simpler code that does not call [one_ulp]. *)
      then finite_float state ~lo ~hi:mid
      else finite_float state ~lo:mid ~hi)
  in
  fun state ~lo ~hi ->
    if not (Float.is_finite lo && Float.is_finite hi)
    then
      raise_s [%message "float: bounds are not finite numbers" (lo : float) (hi : float)];
    if Float.( > ) lo hi
    then raise_s [%message "float: bounds are crossed" (lo : float) (hi : float)];
    finite_float state ~lo ~hi
;;

let float state ~lo ~hi =
  match state.intercept with
  | None -> float_default state ~lo ~hi
  | Some i -> i.float state ~lo ~hi ~default:float_default
;;


module Log_uniform = struct
  module Make (M : sig
    include Int.S

    val uniform : state -> lo:t -> hi:t -> t
  end) : sig
    val log_uniform : state -> lo:M.t -> hi:M.t -> M.t
  end = struct
    open M

    let bits_to_represent t =
      assert (t >= zero);
      let t = ref t in
      let n = ref 0 in
      while !t > zero do
        t := shift_right !t 1;
        Int.incr n
      done;
      !n
    ;;


    let min_represented_by_n_bits n =
      if Int.equal n 0 then zero else shift_left one (Int.pred n)
    ;;


    let max_represented_by_n_bits n = pred (shift_left one n)


    let log_uniform state ~lo ~hi =
      let min_bits = bits_to_represent lo in
      let max_bits = bits_to_represent hi in
      let bits = int state ~lo:min_bits ~hi:max_bits in
      uniform
        state
        ~lo:(min_represented_by_n_bits bits |> max lo)
        ~hi:(max_represented_by_n_bits bits |> min hi)
    ;;
  end

  module For_int = Make (struct
    include Int

    let uniform = int
  end)

  module For_int32 = Make (struct
    include Int32

    let uniform = int32
  end)

  module For_int63 = Make (struct
    include Int63

    let uniform = int63
  end)

  module For_int64 = Make (struct
    include Int64

    let uniform = int64
  end)

  module For_nativeint = Make (struct
    include Nativeint

    let uniform = nativeint
  end)

  let int = For_int.log_uniform
  let int32 = For_int32.log_uniform
  let int63 = For_int63.log_uniform
  let int64 = For_int64.log_uniform
  let nativeint = For_nativeint.log_uniform
end

module Intercept = struct
  type state = t

  type t = intercept =
    { int64 :
        state
        -> lo:int64
        -> hi:int64
        -> default:(state -> lo:int64 -> hi:int64 -> int64)
        -> int64
    ; float :
        state
        -> lo:float
        -> hi:float
        -> default:(state -> lo:float -> hi:float -> float)
        -> float
    ; unit_float : state -> default:(state -> float) -> float
    ; bool : state -> default:(state -> bool) -> bool
    ; on_split : unit -> t option
    ; on_perturb : int -> t option
    }
end

let with_intercept t intercept = { t with intercept = Some intercept }




module State = struct
  type t = state

  let create = create
  let of_int = of_int
  let perturb = perturb
  let copy = copy
  let split = split
end
