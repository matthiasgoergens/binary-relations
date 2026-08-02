(* Choice-tape core, after Hypothesis's Conjecture and our proptest port
   (proptest-rs/proptest#658).

   Generation records every random decision as a typed, bounded choice.
   Shrinking edits the recorded tape and replays generation; an edit is
   accepted iff the test still fails and the re-recorded output tape is
   shortlex-smaller. This module is engine-core only: it knows nothing
   about base_quickcheck. The splittable_random shim calls [draw_*]; the
   engine drives [start_recording] / [start_replay] / [finish].

   Streams (design/stream-keyed-tapes.md): draws carry a stream key so
   that split-off PRNG states (Generator.fn) are tape-controlled too.
   The main generation stream has key [root]; [on_split] allocates a
   child key per split, and [on_perturb] extends a child key with the
   perturb salt, which is exactly the per-argument identity
   Generator.fn uses. Each stream is an independently shrinkable
   sub-sequence with its own replay cursor. A perturb on a child key is
   a call boundary: it resets that stream's cursors so same-argument
   calls replay identically (function purity under edited tapes). *)

type choice =
  | Integer of { value : int64; lo : int64; hi : int64 }
  | Float of { value : float; lo : float; hi : float }
  | Bool of bool
  | Marker
      (* Alignment marker for split/perturb events on the stream they
         happened on. *)

(* Stream keys. [Split n] is the n-th split recorded on the parent
   stream this run; [Salt s] is a perturb salt. Keys are deterministic
   given the taped draws, because the generator's split/perturb pattern
   is a function of the values drawn. *)
type key_elt =
  | Split of int
  | Salt of int

type key = key_elt list

let root : key = []

let compare_key_elt a b =
  match (a, b) with
  | Split a, Split b -> compare a b
  | Salt a, Salt b -> compare a b
  | Split _, Salt _ -> -1
  | Salt _, Split _ -> 1

let rec compare_key (a : key) (b : key) =
  match (a, b) with
  | [], [] -> 0
  | [], _ :: _ -> -1
  | _ :: _, [] -> 1
  | x :: xs, y :: ys ->
    let c = compare_key_elt x y in
    if c <> 0 then c else compare_key xs ys

type mode =
  | Off
  | Recording
  | Replaying

(* Realignment policy for kind mismatches during replay. [Consume]
   skips the mismatched input entry and retries at the next position
   (resyncs clean insertions/deletions); [Freeze] leaves the position
   put and fresh-samples just this draw (holds the entry for a later
   same-kind draw). Neither dominates; the engine can try both and keep
   the shortlex-better result. Applied per stream. *)
type policy =
  | Consume
  | Freeze

(* Per-stream state. [written]/[wlen] is the output side (what this run
   actually used); [wpos] can rewind to 0 at a call boundary so that a
   second same-argument call re-records over the same entries instead
   of appending duplicates. [input]/[rpos] is the replay side; [known]
   distinguishes a stream present in the replay image (exhausting it is
   an overrun) from a brand-new stream (all draws fresh, no flags: new
   salts appear whenever an edit changes an argument's hash, and
   whole-stream deletion relies on absent streams sampling fresh). *)
type stream = {
  mutable written : choice array;
  mutable wlen : int;
  mutable wpos : int;
  mutable input : choice array;
  mutable rpos : int;
  mutable known : bool;
  (* Set once the stream has been entered (or donated) during a replay,
     so orphan adoption never reuses a donor. *)
  mutable claimed : bool;
}

let new_stream ~known ~input =
  { written = [||]; wlen = 0; wpos = 0; input; rpos = 0; known
  ; claimed = false }

(* A complete tape: the main stream plus keyed sub-streams, sorted by
   key. This is the unit of replay, comparison, and persistence. *)
type image = {
  main : choice array;
  streams : (key * choice array) array;
}

let image_of_main main = { main; streams = [||] }

type t = {
  mutable mode : mode;
  mutable policy : policy;
  mutable overrun : bool;
  mutable misaligned : bool;
  streams : (key, stream) Hashtbl.t;
  (* Split ordinal counters, per parent key, reset each run. *)
  splits : (key, int) Hashtbl.t;
}

let create () =
  {
    mode = Off;
    policy = Consume;
    overrun = false;
    misaligned = false;
    streams = Hashtbl.create 8;
    splits = Hashtbl.create 8;
  }

let reset t =
  Hashtbl.reset t.streams;
  Hashtbl.reset t.splits;
  t.overrun <- false;
  t.misaligned <- false

let get_stream t k =
  match Hashtbl.find_opt t.streams k with
  | Some s -> s
  | None ->
    let s = new_stream ~known:false ~input:[||] in
    Hashtbl.replace t.streams k s;
    s

let start_recording t =
  reset t;
  t.mode <- Recording;
  ignore (get_stream t root : stream)

let start_replay_image ?(policy = Consume) t (img : image) =
  reset t;
  t.mode <- Replaying;
  t.policy <- policy;
  Hashtbl.replace t.streams root (new_stream ~known:true ~input:img.main);
  Array.iter
    (fun (k, input) ->
      Hashtbl.replace t.streams k (new_stream ~known:true ~input))
    img.streams

let start_replay ?policy t input =
  start_replay_image ?policy t (image_of_main input)

type output = {
  image : image;
  choices : choice array;
      (* [image.main], repeated as a field: the main-stream view most
         callers want, and what all pre-stream code compiled against. *)
  overrun : bool;
  misaligned : bool;
}

let stream_written (s : stream) = Array.sub s.written 0 s.wlen

let finish t =
  let main =
    match Hashtbl.find_opt t.streams root with
    | Some s -> stream_written s
    | None -> [||]
  in
  let subs =
    Hashtbl.fold
      (fun k s acc ->
        if k == root || compare_key k root = 0 then acc
        else if s.wlen = 0 then acc (* never written: orphan, drop *)
        else (k, stream_written s) :: acc)
      t.streams []
  in
  let subs = List.sort (fun (a, _) (b, _) -> compare_key a b) subs in
  let image = { main; streams = Array.of_list subs } in
  let overrun = t.overrun in
  let misaligned = t.misaligned in
  t.mode <- Off;
  reset t;
  { image; choices = image.main; overrun; misaligned }

(* Overrun so far: lets the engine skip running the test on a proposal
   that already truncated during generation. Monotone within a run. *)
let overrun_now (t : t) = t.overrun

(* Record into a stream with rewrite-over semantics: at a call boundary
   [wpos] rewinds, and re-recording an identical prefix advances through
   it without growing the stream. A divergent value overwrites and
   truncates (the calls genuinely differ, keep the latest). *)
let record_in s c =
  if s.wpos < s.wlen && s.written.(s.wpos) = c then s.wpos <- s.wpos + 1
  else begin
    if s.wpos >= Array.length s.written then begin
      let cap = max 8 (2 * Array.length s.written) in
      let grown = Array.make cap Marker in
      Array.blit s.written 0 grown 0 s.wlen;
      s.written <- grown
    end;
    s.written.(s.wpos) <- c;
    s.wpos <- s.wpos + 1;
    s.wlen <- s.wpos
  end

(* Pop the next input choice of the requested kind from one stream.
   Kind-mismatch handling follows [t.policy]; exhausted KNOWN input
   marks an overrun so the engine can reject deletion proposals that
   merely truncated. Unknown streams always sample fresh, silently. *)
let pop t s ~matches =
  match t.mode with
  | Off | Recording -> None
  | Replaying ->
    if not s.known then None
    else begin
      let take_here () =
        let c = s.input.(s.rpos) in
        s.rpos <- s.rpos + 1;
        c
      in
      let rec consume () =
        if s.rpos >= Array.length s.input then (
          t.overrun <- true;
          None)
        else if matches s.input.(s.rpos) then Some (take_here ())
        else (
          t.misaligned <- true;
          ignore (take_here ());
          consume ())
      in
      if s.rpos >= Array.length s.input then (
        t.overrun <- true;
        None)
      else if matches s.input.(s.rpos) then Some (take_here ())
      else (
        t.misaligned <- true;
        match t.policy with
        | Freeze -> None (* leave the position; fresh-sample this draw *)
        | Consume ->
          (* skip the mismatched entry, retry at the next position *)
          ignore (take_here ());
          consume ())
    end

let clamp_int64 v ~lo ~hi = if v < lo then lo else if v > hi then hi else v

(* Edge-case-biased numeric generation, ported from Python Hypothesis's
   Conjecture provider (the design's origin: see
   outreach/hypothesis-sources/providers_hypothesis.py,
   HypothesisProvider.draw_integer/_draw_integer_from_distribution and
   draw_float around lines 831-1014). Uniform sampling over a wide
   range essentially never lands on the values that break tests --
   exact bounds, zero, values with [x mod y = 0] (proptest upstream
   issue #500) -- because they are a vanishingly small fraction of the
   range. The ICSE 2024 paper's RO4 names this streamlining directly.

   The shape below (roll a die; on a hit return a boundary candidate;
   otherwise pick a random bit-size and step that magnitude from the
   shrink target) is adapted from the sibling Rust port
   (proptest-rs/proptest, itself a port of the same Hypothesis design):
   TestRunner::sample_integer_biased and maybe_weird_float in
   proptest/src/test_runner/runner.rs. That version is the model for
   HOW to express Hypothesis's idea in a statically typed, fixed-width
   language -- OCaml's int64/float choices need exactly that, whereas
   Hypothesis's own provider operates over Python's arbitrary-precision
   integers and a source-scanning constant pool that has no OCaml
   analogue (and is a separate, heavier feature from RO4's core ask;
   deliberately not ported here).

   Only used for a FRESH draw: nothing recorded on the tape to replay
   from at this position (initial generation, or a shrink proposal that
   needs a value the recorded tape does not cover). A replayed choice
   always keeps the tape's own value untouched -- see [draw_int] below
   -- so biasing generation cannot perturb an already-recorded, already
   -shrunk tape. *)

(* [v + 1] / [v - 1], saturating at [hi] / [lo] instead of wrapping.
   Callers only ever apply these to values already known to sit at [lo]
   or [hi] or at the (in-range) shrink target, so the "+1"/"-1" case
   never overflows: if [v < hi] then [v <= hi - 1 <= max_int - 1]. *)
let bump_up v ~hi = if v >= hi then hi else Int64.add v 1L
let bump_down v ~lo = if v <= lo then lo else Int64.sub v 1L

let unsigned_min (a : int64) (b : int64) =
  if Int64.unsigned_compare a b <= 0 then a else b

(* [sample_range ~lo ~hi] draws a fresh uniform int64 in [lo, hi] from
   the real underlying RNG; it is used both for the eventual value AND
   for the auxiliary "which strategy" / "which bit-size" / "which
   direction" rolls, none of which are themselves recorded to the tape
   (only the chosen [choice] is, via [record_in] in the caller) so they
   cost RNG draws but not tape entries. *)
let biased_int ~lo ~hi ~(sample_range : lo:int64 -> hi:int64 -> int64) :
    int64 =
  let target = clamp_int64 0L ~lo ~hi in
  let roll = sample_range ~lo:0L ~hi:15L in
  if Int64.equal roll 0L then begin
    (* Boundary-ish values, at ANY range width -- this is what finds
       bugs guarded by [x mod y = 0], [x = 0], or an exact bound. *)
    let candidates =
      [| lo; bump_up lo ~hi; hi; bump_down hi ~lo; target; bump_up target ~hi |]
    in
    let idx = sample_range ~lo:0L ~hi:5L in
    candidates.(Int64.to_int idx)
  end
  else begin
    (* Unsigned: exact modulo 2^64 even for full-range spans like
       [min_int, max_int], same reasoning as [int_distance] below. *)
    let width = Int64.sub hi lo in
    if Int64.unsigned_compare width 0x100_0000L < 0 || Int64.compare roll 2L <= 0
    then sample_range ~lo ~hi
    else begin
      (* Magnitude within a weighted random bit-size of the shrink
         target: small sizes heavily preferred, a wide tail retained.
         Hypothesis's INT_SIZES table (via the Rust port) spans
         8/16/32/64/128 bits with weights 4/8/1/1/1 out of 15; int64
         has no 128-bit lane, so its weight is folded into 64-bit
         (giving 8/16/32/64 weights 4/8/1/2 out of 15) -- the OCaml
         deviation from both sources, noted in the write-up. *)
      let bits =
        match sample_range ~lo:0L ~hi:14L with
        | r when Int64.compare r 3L <= 0 -> 8
        | r when Int64.compare r 11L <= 0 -> 16
        | 12L -> 32
        | _ -> 64
      in
      let mask =
        if bits >= 64 then -1L else Int64.sub (Int64.shift_left 1L bits) 1L
      in
      let raw = sample_range ~lo:Int64.min_int ~hi:Int64.max_int in
      let magnitude = Int64.logand raw mask in
      let up_room = Int64.sub hi target and down_room = Int64.sub target lo in
      let go_up =
        if Int64.equal down_room 0L then true
        else if Int64.equal up_room 0L then false
        else Int64.equal (sample_range ~lo:0L ~hi:1L) 1L
      in
      if go_up then Int64.add target (unsigned_min magnitude up_room)
      else Int64.sub target (unsigned_min magnitude down_room)
    end
  end

let draw_int ?(stream = root) t ~lo ~hi
    ~(sample : lo:int64 -> hi:int64 -> int64) : int64 =
  match t.mode with
  | Off -> sample ~lo ~hi
  | Recording | Replaying ->
    let s = get_stream t stream in
    let value =
      match pop t s ~matches:(function Integer _ -> true | _ -> false) with
      | Some (Integer { value; _ }) -> clamp_int64 value ~lo ~hi
      | _ -> biased_int ~lo ~hi ~sample_range:sample
    in
    record_in s (Integer { value; lo; hi });
    value

let clamp_float v ~lo ~hi = if v < lo then lo else if v > hi then hi else v

(* Float boundary/special-value injection, same origin and adaptation
   path as [biased_int] above (Hypothesis's [draw_float] "weird_floats"
   upweight, providers_hypothesis.py:972-996, via the Rust port's
   [maybe_weird_float] in runner.rs). Every draw reaching this codebase
   already carries FINITE, non-crossed [lo]/[hi] (sr_real.float_default
   raises otherwise: vendor/sr_real/sr_real.ml lines 285-291), so unlike
   both sources there is no infinite-bound or [allow_nan] case to carry
   through -- "NaN only where the range allows" becomes "never", since
   the range here never allows it. That is an OCaml/base_quickcheck
   deviation, not an omission: injecting NaN would violate this
   generator's own finite-range invariant. *)
let biased_float ~lo ~hi ~(sample_range : lo:float -> hi:float -> float) :
    float =
  (* 1-in-20, matching the Rust port's [maybe_weird_float] roll (itself
     modelled on Hypothesis's independent 0.05 "weird floats" upweight,
     kept separate there from a 0.15 source-constants pool this port
     does not have). *)
  let roll = sample_range ~lo:0. ~hi:1. in
  if Float.compare roll (1. /. 20.) >= 0 then sample_range ~lo ~hi
  else begin
    let in_range v = v >= lo && v <= hi in
    let candidates =
      List.filter in_range
        [ 0.; -0.; 1.; -1.; 0.5; 1.5; lo; hi; lo +. 1.; hi -. 1.
        ; Float.succ lo; Float.pred hi
        ]
    in
    match candidates with
    | [] -> sample_range ~lo ~hi (* unreachable: [lo] always qualifies *)
    | candidates ->
      let candidates = Array.of_list candidates in
      let pick = sample_range ~lo:0. ~hi:1. in
      let idx =
        let n = Array.length candidates in
        let i = int_of_float (pick *. float_of_int n) in
        if i >= n then n - 1 else i
      in
      candidates.(idx)
  end

let draw_float ?(stream = root) t ~lo ~hi
    ~(sample : lo:float -> hi:float -> float) : float =
  match t.mode with
  | Off -> sample ~lo ~hi
  | Recording | Replaying ->
    let s = get_stream t stream in
    let value =
      match pop t s ~matches:(function Float _ -> true | _ -> false) with
      | Some (Float { value; _ }) ->
        if Float.is_nan value then biased_float ~lo ~hi ~sample_range:sample
        else clamp_float value ~lo ~hi
      | _ -> biased_float ~lo ~hi ~sample_range:sample
    in
    record_in s (Float { value; lo; hi });
    value

let draw_bool ?(stream = root) t ~(sample : unit -> bool) : bool =
  match t.mode with
  | Off -> sample ()
  | Recording | Replaying ->
    let s = get_stream t stream in
    let value =
      match pop t s ~matches:(function Bool _ -> true | _ -> false) with
      | Some (Bool b) -> b
      | _ -> sample ()
    in
    record_in s (Bool value);
    value

let record_marker_in t k =
  match t.mode with
  | Off -> ()
  | Recording | Replaying ->
    let s = get_stream t k in
    (* Consume a matching marker on replay to stay aligned. *)
    ignore (pop t s ~matches:(function Marker -> true | _ -> false));
    record_in s Marker

let record_marker t = record_marker_in t root

(* A split on [stream]: record an alignment marker there and allocate
   the child stream's key by per-parent ordinal. Deterministic across
   record and replay because splits happen at generator-driven points. *)
let on_split t ~stream:k =
  record_marker_in t k;
  let n = match Hashtbl.find_opt t.splits k with Some n -> n | None -> 0 in
  Hashtbl.replace t.splits k (n + 1);
  k @ [ Split n ]

(* A perturb on the ROOT stream is Generator.perturb mid-generation:
   record a marker for alignment and keep the key (splitting the main
   stream at every such point would scatter the shrink passes). On a
   child stream it is a call boundary (Generator.fn perturbs a copy of
   the split state with the argument hash): extend the key with the
   salt and rewind that stream's cursors so same-argument calls replay
   identically. *)
(* Orphan adoption (ported from the Rust engine, where it took a
   data+function co-shrink from 19/60 stuck seeds to 0): a replay that
   enters an UNKNOWN salted stream (the argument's hash, and so the
   key, changed under a shrink edit) adopts the input of an unclaimed
   sibling: same parent, salt leaf, deterministic key order. That
   sibling is exactly the orphan whose argument just changed, so the
   function keeps its observed behaviour across the edit instead of
   flipping a fresh coin; the accepted output re-records under the new
   salt, realigning the tape for the next round. *)
let adopt_orphan t key s =
  let n = List.length key in
  let parent = List.filteri (fun i _ -> i < n - 1) key in
  let donors =
    Hashtbl.fold
      (fun k' s' acc ->
        if
          s'.known && not s'.claimed
          && List.length k' = n
          && List.filteri (fun i _ -> i < n - 1) k' = parent
          &&
          match List.nth_opt k' (n - 1) with
          | Some (Salt _) -> true
          | _ -> false
        then (k', s') :: acc
        else acc)
      t.streams []
  in
  match List.sort (fun (a, _) (b, _) -> compare_key a b) donors with
  | (_, donor) :: _ ->
    s.input <- donor.input;
    s.known <- true;
    donor.claimed <- true
  | [] -> ()

let on_perturb t ~stream:k ~salt =
  match k with
  | [] ->
    record_marker_in t k;
    None
  | _ :: _ ->
    let salted = k @ [ Salt salt ] in
    (match t.mode with
     | Off -> ()
     | Recording | Replaying ->
       let s = get_stream t salted in
       (match t.mode with
        | Replaying when not s.known -> adopt_orphan t salted s
        | _ -> ());
       s.claimed <- true;
       s.rpos <- 0;
       s.wpos <- 0);
    Some salted

(* Serialization. Version 1 ("ct1", after the proptest tape engine's
   format): version byte then one record per choice; still emitted for
   main-only tapes so pre-stream regression files and readers keep
   working. Version 2 adds keyed stream sections. Deserialization is
   total over well-formed records via clamping at replay time; a
   truncated or unknown-tag input returns None. *)

let buf_add_int64 buf v =
  for shift = 0 to 7 do
    Buffer.add_char buf
      (Char.chr (Int64.to_int (Int64.logand (Int64.shift_right_logical v (shift * 8)) 0xffL)))
  done

let buf_add_choice buf c =
  match c with
  | Integer { value; lo; hi } ->
    Buffer.add_char buf 'i';
    buf_add_int64 buf value;
    buf_add_int64 buf lo;
    buf_add_int64 buf hi
  | Float { value; lo; hi } ->
    Buffer.add_char buf 'f';
    buf_add_int64 buf (Int64.bits_of_float value);
    buf_add_int64 buf (Int64.bits_of_float lo);
    buf_add_int64 buf (Int64.bits_of_float hi)
  | Bool b ->
    Buffer.add_char buf 'b';
    Buffer.add_char buf (if b then '\001' else '\000')
  | Marker -> Buffer.add_char buf 'm'

let serialize_image (img : image) : string =
  if Array.length img.streams = 0 then begin
    let buf = Buffer.create (Array.length img.main * 20) in
    Buffer.add_char buf '\001';
    Array.iter (buf_add_choice buf) img.main;
    Buffer.contents buf
  end
  else begin
    let buf = Buffer.create 256 in
    Buffer.add_char buf '\002';
    buf_add_int64 buf (Int64.of_int (Array.length img.main));
    Array.iter (buf_add_choice buf) img.main;
    buf_add_int64 buf (Int64.of_int (Array.length img.streams));
    Array.iter
      (fun (k, arr) ->
        buf_add_int64 buf (Int64.of_int (List.length k));
        List.iter
          (fun elt ->
            match elt with
            | Split n ->
              Buffer.add_char buf 'S';
              buf_add_int64 buf (Int64.of_int n)
            | Salt s ->
              Buffer.add_char buf 'P';
              buf_add_int64 buf (Int64.of_int s))
          k;
        buf_add_int64 buf (Int64.of_int (Array.length arr));
        Array.iter (buf_add_choice buf) arr)
      img.streams;
    Buffer.contents buf
  end

let serialize (choices : choice array) : string =
  serialize_image (image_of_main choices)

(* Shared cursor-based reader over [s]. *)
type reader = { src : string; mutable pos : int }

let take_char r =
  if r.pos >= String.length r.src then None
  else begin
    let c = r.src.[r.pos] in
    r.pos <- r.pos + 1;
    Some c
  end

let take_int64 r =
  if r.pos + 8 > String.length r.src then None
  else begin
    let v = ref 0L in
    for shift = 7 downto 0 do
      v :=
        Int64.logor
          (Int64.shift_left !v 8)
          (Int64.of_int (Char.code r.src.[r.pos + shift]))
    done;
    r.pos <- r.pos + 8;
    Some !v
  end

let take_choice r =
  match take_char r with
  | Some 'i' ->
    (match (take_int64 r, take_int64 r, take_int64 r) with
     | Some value, Some lo, Some hi -> Some (Integer { value; lo; hi })
     | _ -> None)
  | Some 'f' ->
    (match (take_int64 r, take_int64 r, take_int64 r) with
     | Some value, Some lo, Some hi ->
       Some
         (Float
            { value = Int64.float_of_bits value
            ; lo = Int64.float_of_bits lo
            ; hi = Int64.float_of_bits hi
            })
     | _ -> None)
  | Some 'b' ->
    (match take_char r with
     | Some '\000' -> Some (Bool false)
     | Some '\001' -> Some (Bool true)
     | _ -> None)
  | Some 'm' -> Some Marker
  | _ -> None

let take_count r =
  match take_int64 r with
  | Some n when n >= 0L && n <= 0x0fff_ffffL -> Some (Int64.to_int n)
  | _ -> None

let take_choices r n =
  let acc = ref [] in
  let ok = ref true in
  for _ = 1 to n do
    if !ok then
      match take_choice r with
      | Some c -> acc := c :: !acc
      | None -> ok := false
  done;
  if !ok then Some (Array.of_list (List.rev !acc)) else None

let deserialize_image (s : string) : image option =
  let r = { src = s; pos = 0 } in
  match take_char r with
  | Some '\001' ->
    (* v1: main-only, records to end of input. *)
    let acc = ref [] in
    let ok = ref true in
    while !ok && r.pos < String.length s do
      match take_choice r with
      | Some c -> acc := c :: !acc
      | None -> ok := false
    done;
    if !ok then Some (image_of_main (Array.of_list (List.rev !acc)))
    else None
  | Some '\002' ->
    let ( let* ) = Option.bind in
    let* n_main = take_count r in
    let* main = take_choices r n_main in
    let* n_streams = take_count r in
    let rec streams acc i =
      if i >= n_streams then
        if r.pos = String.length s then Some (List.rev acc) else None
      else
        let* n_key = take_count r in
        let rec key acc j =
          if j >= n_key then Some (List.rev acc)
          else
            match take_char r with
            | Some 'S' ->
              let* n = take_int64 r in
              key (Split (Int64.to_int n) :: acc) (j + 1)
            | Some 'P' ->
              let* n = take_int64 r in
              key (Salt (Int64.to_int n) :: acc) (j + 1)
            | _ -> None
        in
        let* k = key [] 0 in
        let* n_choices = take_count r in
        let* arr = take_choices r n_choices in
        streams ((k, arr) :: acc) (i + 1)
    in
    let* subs = streams [] 0 in
    Some { main; streams = Array.of_list subs }
  | _ -> None

let deserialize (s : string) : choice array option =
  match deserialize_image s with
  | Some { main; streams = [||] } -> Some main
  | Some _ -> None (* stream-carrying tape: use deserialize_image *)
  | None -> None

(* Shortlex order: fewer choices first; ties broken choice-by-choice by
   distance from the shrink target (the value in [lo, hi] closest to
   zero), so "simpler" means shorter, then closer to zero. *)

(* Distance from the shrink target as an UNSIGNED int64 (the wrapped
   subtraction is exact modulo 2^64, so this cannot overflow even for
   full-range spans like [min_int, max_int]), plus which side of the
   target the value sits on. Ordering: smaller distance first; on equal
   distance, above-target before below (the zigzag preference), the
   target itself first of all. *)
let int_distance ~value ~lo ~hi =
  let target = clamp_int64 0L ~lo ~hi in
  if value >= target then (Int64.sub value target, 0) (* above or equal *)
  else (Int64.sub target value, 1) (* below *)

let float_key ~value ~lo ~hi =
  let target = clamp_float 0. ~lo ~hi in
  if Float.is_nan value then Float.infinity else Float.abs (value -. target)

let compare_choice a b =
  match (a, b) with
  | Integer a', Integer b' ->
    let da, sa = int_distance ~value:a'.value ~lo:a'.lo ~hi:a'.hi in
    let db, sb = int_distance ~value:b'.value ~lo:b'.lo ~hi:b'.hi in
    let c = Int64.unsigned_compare da db in
    if c <> 0 then c else compare sa sb
  | Float a', Float b' ->
    compare (float_key ~value:a'.value ~lo:a'.lo ~hi:a'.hi)
      (float_key ~value:b'.value ~lo:b'.lo ~hi:b'.hi)
  | Bool a', Bool b' -> compare a' b'
  | Marker, Marker -> 0
  (* Mixed kinds: stable arbitrary order; mixed comparisons only arise
     on misaligned tapes, which replay re-records anyway. *)
  | Integer _, _ -> -1
  | _, Integer _ -> 1
  | Float _, _ -> -1
  | _, Float _ -> 1
  | Bool _, _ -> -1
  | _, Bool _ -> 1

let compare_shortlex (a : choice array) (b : choice array) =
  let la = Array.length a and lb = Array.length b in
  if la <> lb then compare la lb
  else begin
    let rec go i =
      if i >= la then 0
      else
        let c = compare_choice a.(i) b.(i) in
        if c <> 0 then c else go (i + 1)
    in
    go 0
  end

(* Image order: total choice count first (a deleted stream is a smaller
   tape), then the main stream shortlex, then fewer streams, then the
   sorted stream lists pairwise (key order, then per-stream shortlex).
   A total order, so shrink acceptance stays a strict descent. *)
let image_size (img : image) =
  Array.fold_left
    (fun acc (_, arr) -> acc + Array.length arr)
    (Array.length img.main) img.streams

let compare_image (a : image) (b : image) =
  let c = compare (image_size a) (image_size b) in
  if c <> 0 then c
  else begin
    let c = compare_shortlex a.main b.main in
    if c <> 0 then c
    else begin
      let la = Array.length a.streams and lb = Array.length b.streams in
      let c = compare la lb in
      if c <> 0 then c
      else begin
        let rec go i =
          if i >= la then 0
          else begin
            let ka, arr_a = a.streams.(i) and kb, arr_b = b.streams.(i) in
            let c = compare_key ka kb in
            if c <> 0 then c
            else
              let c = compare_shortlex arr_a arr_b in
              if c <> 0 then c else go (i + 1)
          end
        in
        go 0
      end
    end
  end
