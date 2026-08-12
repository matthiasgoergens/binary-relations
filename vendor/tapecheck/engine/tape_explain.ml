(* RO5, input half of Hypothesis's Phase.explain (outreach/ro-roadmap.md,
   "RO5 half 2"). After shrinking has converged on a minimal tape image,
   perturb each recorded choice IN ISOLATION -- holding every other
   choice on the tape fixed -- and re-run the generator and test. A
   choice whose value can change without the test starting to pass is
   irrelevant to the failure; a choice for which no such change was
   found is a candidate for being load-bearing.

   This suits the tape model specifically: choices are individually
   addressable and independently replayable, which a rose-tree /
   integrated shrinker (QCheck2, Bam) has no equivalent handle for,
   because its shrink structure is fixed as the value is constructed.
   There is no "choice 7" to perturb in a shrink tree assembled around
   already-committed sub-values; the tape gives every recorded decision
   a stable address that survives the whole run.

   Hypothesis's own stated posture, copied deliberately: "If there are
   no clearly suspicious lines of code, we refuse the temptation to
   guess." Applied here: failing to find a still-failing perturbation
   within budget does NOT prove the choice is load-bearing, only that
   this bounded search did not find one. [No_variation_found] is
   reported as exactly that, never as proof, and [complete] on the
   overall report says plainly when the budget ran out before every
   choice was even given a fair try.

   This module is intentionally a leaf: [Tape_engine] does not know it
   exists, so the "phase" is switched off simply by not calling
   [analyze] (wired as an opt-in ?explain flag in Tape_test). One
   consequence: this module never goes through [Tape_engine.shrink]'s
   own attempt budget or stall tracking at all -- every replay here is
   its own fresh [Tape.start_replay_image] / [run_and_test], entirely
   independent of the shrink loop that produced the minimal image in
   the first place. Hypothesis's [_explain] sets `self.max_stall =
   2**100` at the top precisely because ITS explain phase reuses the
   SAME shrinker object and its stall-detection would otherwise abort
   the whole thing early; there is no equivalent knob to disable here,
   because there was never a shared stall counter to begin with. *)

open! Base

type 'a outcome =
  | Varies of { examples : 'a list }
      (* At least one alternative value at this position -- everything
         else on the tape held fixed -- regenerated a value that still
         failed the test. [examples] holds up to
         [max_examples_per_choice] distinct such values, so a human can
         compare them against the minimal example directly rather than
         trust a bare "choice 7" label. *)
  | No_variation_found
      (* Every alternative tried within budget either made the test
         pass, or could not be tried cleanly (it overran or
         desynchronized the tape, so it is not evidence either way).
         A negative result from a BOUNDED search, not a proof of
         necessity. *)
  | No_alternative_possible
      (* The choice's range is a single point (lo = hi): "does it vary"
         is not a meaningful question, so this is kept separate from a
         search that came up empty. *)

type 'a choice_report =
  { seg : int (* 0 = main stream; s >= 1 = image.streams.(s - 1) *)
  ; stream_key : Tape.key
  ; index : int (* position within that stream *)
  ; original : Tape.choice
  ; outcome : 'a outcome
  ; tries : int (* candidates actually executed at this position *)
  }

type 'a t =
  { choices : 'a choice_report list
  ; attempts_per_choice : int
      (* The cap PER CHOICE, not a pool shared across the whole tape --
         see the note below on why the old shape was wrong. *)
  ; used : int (* candidate replays actually spent, across every choice *)
  ; complete : bool
      (* false if some choice's own search did not run to ITS natural
         conclusion (quota met, candidates and random budget exhausted,
         or the early-abort-on-mostly-noise heuristic fired) -- i.e.
         [attempts_per_choice] was set so low (typically 0) that a
         choice with real alternatives to try got none. With the
         Hypothesis-sized default below this is essentially always
         true in practice; it exists so a caller can still ask for, and
         detect, a deliberately cheap/degenerate run. *)
  }

(* Governing principle (the reason this shape changed at all): the
   PASSING path runs on every CI invocation and must stay cheap --
   that is [Tape_engine]'s own shrink budget, spent constantly. The
   EXPLAIN path only runs once, after a test has already failed and
   already been shrunk, and its output goes in front of a human who is
   about to spend real time reading it. That failing path is rare, so
   it can afford orders of magnitude more replays than the passing path
   ever should. A flat global budget of 200 split across however many
   choices happen to be on the minimal tape (the old shape here) gets
   this backwards: it taxes every choice by the SIZE of the example,
   which is exactly when a human most wants a thorough answer.

   Hypothesis's own [_explain] (outreach/hypothesis-sources/
   shrinker_hypothesis.py, ~line 499) makes the budget PER SPAN
   instead: `for n_attempt in range(500 + len(candidates))`, one such
   loop per part of the minimal example, not one loop shared over all
   of them. [default_attempts_per_choice] below is that same 500,
   applied per recorded tape choice (tapecheck's finer-grained analogue
   of a Hypothesis "span" -- see the note further down on why choices
   don't nest the way spans do). Their own comment is left in as a
   `# TODO: is 100 same-failures out of 500 attempts a good heuristic?`
   -- they are not certain the constant is right either, so this is a
   starting point copied deliberately, not a number treated as
   sacred. *)
let default_attempts_per_choice = 500

(* Independent of the attempts budget: how many distinct still-failing
   example VALUES to keep for the human-readable report once a choice
   is confirmed to vary. Hypothesis doesn't collect examples at all --
   once a span accumulates 100 same-ish failures in a row it just
   stamps a fixed note ("or any other generated value") without keeping
   any of them. Showing 3 concrete alternative values costs nothing
   extra in replays (it only trims [found] early) and is more useful to
   a human than a constant string, so this divergence stays. *)
let max_examples_per_choice = 3

(* Deterministic candidate alternative values for one recorded choice,
   most informative first: the shrink target and the range endpoints
   (the values a reader is most likely to already be comparing
   against), then the immediate neighbors of the current value.
   Mirrors Hypothesis's `_explain_candidates`: try a few targeted,
   plausible values before falling back to genuine random sampling, so
   a case like `assert n1 == n2` -- where the only passing value of
   `n1` is exactly `n2`'s value -- isn't reported as freely-variable
   just because random sampling missed the one value that matters.
   Deliberately NOT capped and NOT padded with random samples (the old
   [max_tries_per_choice]/[extra_random_samples] existed only because
   the old shared budget needed every choice's candidate list bounded
   up front); the list here is inherently small (at most 5 entries),
   and genuine random sampling is drawn fresh, attempt by attempt, in
   [run_item] below instead, exactly as Hypothesis draws a fresh random
   replacement inside its own attempt loop rather than precomputing a
   pool of them. *)
let candidates_for (c : Tape.choice) : Tape.choice list =
  match c with
  | Tape.Marker -> []
  | Tape.Bool b -> [ Tape.Bool (not b) ]
  | Tape.Integer { value; lo; hi } ->
    if Int64.(lo = hi) then []
    else begin
      let target = Tape.clamp_int64 0L ~lo ~hi in
      [ Some target
      ; Some lo
      ; Some hi
      ; (if Int64.(value > lo) then Some Int64.(value - 1L) else None)
      ; (if Int64.(value < hi) then Some Int64.(value + 1L) else None)
      ]
      |> List.filter_opt
      |> List.filter ~f:(fun v -> Int64.(v <> value))
      |> List.dedup_and_sort ~compare:Int64.compare
      |> List.map ~f:(fun value -> Tape.Integer { value; lo; hi })
    end
  | Tape.Float { value; lo; hi } ->
    if Float.(lo = hi) then []
    else begin
      let target = Tape.clamp_float 0. ~lo ~hi in
      [ target; lo; hi ]
      |> List.filter ~f:(fun v -> Float.(v <> value) && not (Float.is_nan v))
      |> List.dedup_and_sort ~compare:Float.compare
      |> List.map ~f:(fun value -> Tape.Float { value; lo; hi })
    end

(* A genuinely fresh random alternative, drawn on demand (one draw per
   attempt, not a precomputed pool) -- Hypothesis's `draw_choice(node
   .type, node.constraints, random=self.random)` inside the same loop.
   Only reachable for Integer/Float, whose ranges can be large enough
   that the handful of [candidates_for] doesn't cover them; Bool has
   exactly one alternative (already the sole candidate) and Marker is
   filtered out before this is ever called. *)
let fresh_random_alternative (c : Tape.choice) (rand : Splittable_random.t) :
    Tape.choice =
  match c with
  | Tape.Integer { lo; hi; _ } ->
    Tape.Integer { value = Splittable_random.int64 rand ~lo ~hi; lo; hi }
  | Tape.Float { lo; hi; _ } ->
    Tape.Float { value = Splittable_random.float rand ~lo ~hi; lo; hi }
  | Tape.Bool _ | Tape.Marker -> c

let positions_of (image : Tape.image) : (int * Tape.key * int * Tape.choice) list
  =
  List.concat_map
    (List.range 0 (Tape_engine.seg_count image))
    ~f:(fun seg ->
      let arr = Tape_engine.seg_get image seg in
      let key = if seg = 0 then Tape.root else fst image.streams.(seg - 1) in
      List.init (Array.length arr) ~f:(fun idx -> (seg, key, idx, arr.(idx))))

(* Redundant-work avoidance, adapted rather than ported directly.
   Hypothesis's [_explain] looks up `self.engine.passing_choice_sequences
   (prefix=...)` before running any experiment for a span, and skips the
   span entirely if a PASSING sequence already on file has the same
   prefix and suffix -- "the shrinking process means that we've already
   tried many variations on the minimal test case, so this can save a
   lot of time." That specific check does not transfer as-is: Hypothesis
   is hunting for a PASSING alternative (any single one disproves "varies
   freely" outright), so a known-passing sequence directly answers its
   question. tapecheck hunts for the opposite thing -- a STILL-FAILING
   alternative -- so a known PASS tells us nothing about whether a
   failing one also exists.

   What tapecheck already has on file that DOES answer the right
   question is [Tape_engine.failure.trail]: every image accepted during
   shrinking, each one independently confirmed still-failing (that is
   the acceptance criterion). Two tape images in that chain that agree
   everywhere except one position are exactly a validated "changing this
   choice here still fails" data point -- the precise evidence
   [Varies] wants, already paid for once during shrinking. We surface
   those as extra CANDIDATES (tried for real, same as
   [candidates_for]'s hand-picked ones, so [used] accounts for them
   honestly) rather than as a hard skip, both because they still need
   one replay to materialize the reported example value and because
   unlike Hypothesis's binary "varies freely" verdict, ours wants actual
   example values to show a human. *)
let trail_alternatives ~(trail : Tape.image list) (image : Tape.image) seg idx :
    Tape.choice list =
  let seg_count_image = Tape_engine.seg_count image in
  List.filter_map trail ~f:(fun cand ->
    if Tape_engine.seg_count cand <> seg_count_image then None
    else begin
      let other_segments_match =
        List.for_all (List.range 0 seg_count_image) ~f:(fun s ->
          if s = seg then true
          else begin
            let a = Tape_engine.seg_get image s
            and b = Tape_engine.seg_get cand s in
            Array.length a = Array.length b
            && Array.for_alli a ~f:(fun i x -> Tape.compare_choice x b.(i) = 0)
          end)
      in
      if not other_segments_match then None
      else begin
        let a = Tape_engine.seg_get image seg and b = Tape_engine.seg_get cand seg in
        if Array.length a <> Array.length b then None
        else begin
          let same_except_idx =
            Array.for_alli a ~f:(fun i x ->
              i = idx || Tape.compare_choice x b.(i) = 0)
          in
          if same_except_idx && Tape.compare_choice a.(idx) b.(idx) <> 0 then
            Some b.(idx)
          else None
        end
      end
    end)
  |> List.dedup_and_sort ~compare:Tape.compare_choice

(* One perturbation: replace the choice at [(seg, idx)] with [candidate]
   and nothing else, replay, and classify the result. [`Untestable]
   covers both an overrun (the edit truncated generation before the
   test ran) and a misalignment (the tape resynchronized somewhere,
   so more than the intended choice may have changed) -- neither is
   evidence about THIS choice specifically, so neither counts toward
   [Varies] or against it. *)
let try_candidate (type a) ~(gen : a Base_quickcheck.Generator.t) ~size
    ~(test : a -> bool) (image : Tape.image) seg idx candidate :
    [ `Untestable | `Passed | `Still_failing of a ] =
  let arr = Tape_engine.seg_get image seg in
  let proposal =
    Tape_engine.seg_set image seg (Tape_engine.with_choice arr idx candidate)
  in
  let tape = Tape.create () in
  Tape.start_replay_image ~policy:Tape.Consume tape proposal;
  let value, tested, out =
    Tape_engine.run_and_test ~tape ~gen ~size
      ~seed:Tape_engine.replay_fresh_seed ~test
  in
  match tested with
  | None -> `Untestable
  | Some verdict ->
    if out.Tape.overrun || out.Tape.misaligned then `Untestable
    else (
      match verdict with
      | Tape_stats.Case_passed | Tape_stats.Case_invalid -> `Passed
      | Tape_stats.Case_failed -> `Still_failing value)

type 'a item =
  { seg : int
  ; stream_key : Tape.key
  ; index : int
  ; original : Tape.choice
  ; candidates : Tape.choice array (* trail-derived, then hand-picked *)
  ; rand : Splittable_random.t (* persistent across this item's attempts *)
  ; cap : int (* total attempts this item may spend, candidates included *)
  ; mutable found : 'a list
  ; mutable found_choices : Tape.choice list
      (* The tape choices already backing [found], so a repeat draw of
         the SAME alternative (a real possibility on a small range, e.g.
         Bool or a two-valued Integer) doesn't masquerade as a second
         distinct example: [found] is meant to show a human up to
         [max_examples_per_choice] genuinely DIFFERENT alternative
         values, not the same one three times. Only gates what counts
         toward [found]/the quota; [n_same_failures] below (which
         governs the early-abort heuristic) still counts every
         still-failing replay, repeats included, exactly as Hypothesis's
         own n_same_failures does. *)
  ; mutable tries : int
  }

(* One item's search, run to ITS OWN completion -- no shared pool with
   any other choice, so processing order across items cannot affect any
   item's outcome (unlike the old round-robin, which existed only to
   share a global budget fairly). Hypothesis processes spans
   largest-first so that its subset-of-an-already-explained-range skip
   fires correctly; that optimization has no analogue here (see the
   comment on [trail_alternatives] for why choices, unlike spans, never
   nest inside one another -- each tape position is already the
   smallest addressable unit), so there is nothing that ordering could
   help or hurt. Order is therefore just (seg, key, idx) position order,
   for reproducible output. *)
let run_item (type a) ~(gen : a Base_quickcheck.Generator.t) ~size
    ~(test : a -> bool) (image : Tape.image) (it : a item) : unit =
  let n_candidates = Array.length it.candidates in
  let n_same_failures = ref 0 in
  let attempt_idx = ref 0 in
  let continue_ = ref true in
  while
    !continue_ && !attempt_idx < it.cap
    && List.length it.found < max_examples_per_choice
  do
    (* Port of Hypothesis's early-abort test verbatim: `if n_attempt -
       10 - len(candidates) > n_same_failures * 5: break` -- stop
       spending budget once the replays are mostly coming back
       Untestable/Passed rather than confirming still-failing, instead
       of grinding through the whole per-choice cap on noise. Their own
       comment: "TODO: is 100 same-failures out of 500 attempts a good
       heuristic?" -- not treated as sacred, just a documented start. *)
    if !attempt_idx - 10 - n_candidates > !n_same_failures * 5 then
      continue_ := false
    else begin
      let candidate =
        if !attempt_idx < n_candidates then it.candidates.(!attempt_idx)
        else fresh_random_alternative it.original it.rand
      in
      it.tries <- it.tries + 1;
      (match try_candidate ~gen ~size ~test image it.seg it.index candidate with
       | `Still_failing v ->
         Int.incr n_same_failures;
         if
           not
             (List.mem it.found_choices candidate
                ~equal:(fun a b -> Tape.compare_choice a b = 0))
         then begin
           it.found <- it.found @ [ v ];
           it.found_choices <- candidate :: it.found_choices
         end
       | `Passed | `Untestable -> ());
      Int.incr attempt_idx
    end
  done

let analyze (type a) ~(gen : a Base_quickcheck.Generator.t) ~size
    ~(test : a -> bool) ?(attempts_per_choice = default_attempts_per_choice)
    ?(trail : Tape.image list = [])
    (image : Tape.image) : a t =
  let items =
    List.filter_map (positions_of image) ~f:(fun (seg, key, idx, choice) ->
      match choice with
      | Tape.Marker -> None
      | _ ->
        let no_alternative_exists = List.is_empty (candidates_for choice) in
        (* Deterministic per-position seed: reproducible across runs,
           independent of wall-clock or process state. *)
        let seed = Stdlib.Hashtbl.hash (seg, idx, key) in
        let candidates =
          (* Trail-derived (already-validated) alternatives first, then
             the hand-picked ones; a value appearing in both is only
             tried once. *)
          trail_alternatives ~trail image seg idx
          @ candidates_for choice
          |> List.dedup_and_sort ~compare:Tape.compare_choice
          |> Array.of_list
        in
        let n_candidates = Array.length candidates in
        (* [attempts_per_choice <= 0] disables the search for this item
           entirely, including its free candidates -- a deliberately
           harder guarantee than Hypothesis's own `range(0 +
           len(candidates))` (which would still try candidates at a
           configured cap of zero). A caller asking for zero plainly
           wants zero replays, not "just the free ones"; ?explain:false
           already covers "skip the whole phase" for everyone else. *)
        let cap =
          if no_alternative_exists then 0
          else if attempts_per_choice <= 0 then 0
          else begin
            let random_fallback_budget =
              match choice with
              | Tape.Integer _ | Tape.Float _ -> attempts_per_choice
              (* Bool has exactly one alternative, already the sole
                 candidate; Marker never reaches here. *)
              | Tape.Bool _ | Tape.Marker -> 0
            in
            n_candidates + random_fallback_budget
          end
        in
        Some
          { seg
          ; stream_key = key
          ; index = idx
          ; original = choice
          ; candidates
          ; rand = Splittable_random.of_int seed
          ; cap
          ; found = []
          ; found_choices = []
          ; tries = 0
          })
  in
  List.iter items ~f:(run_item ~gen ~size ~test image);
  let used = List.sum (module Int) items ~f:(fun it -> it.tries) in
  (* [complete] is about a search being pre-empted, not about how it
     concluded: reaching your own per-choice cap without confirming
     [Varies], or the early-abort-on-mostly-noise heuristic firing, are
     both ordinary, expected ways for an item's search to finish (they
     are exactly how Hypothesis's own per-span loop ends for most spans
     too) -- neither makes the overall report incomplete. The only way
     a real search gets cut short here is [attempts_per_choice <= 0]
     while genuine candidates existed to try. *)
  let complete =
    List.for_all items ~f:(fun it ->
      not (it.cap = 0 && not (Array.is_empty it.candidates)))
  in
  let choices =
    List.map items ~f:(fun it ->
      let outcome =
        if not (List.is_empty it.found) then Varies { examples = it.found }
        else if it.cap = 0 && Array.is_empty it.candidates then
          (* [cap] can be 0 for two different reasons: a genuinely
             single-point choice (no candidate ever existed), or
             [attempts_per_choice <= 0] disabling an otherwise-real
             search. Only the former is [No_alternative_possible]; the
             empty-candidates check tells them apart, since a real
             search that got disabled still has candidates it never
             got to run. *)
          No_alternative_possible
        else No_variation_found
      in
      { seg = it.seg
      ; stream_key = it.stream_key
      ; index = it.index
      ; original = it.original
      ; outcome
      ; tries = it.tries
      })
  in
  { choices; attempts_per_choice; used; complete }

let string_of_choice = function
  | Tape.Integer { value; lo; hi } ->
    Stdlib.Printf.sprintf "int %Ld  (range [%Ld, %Ld])" value lo hi
  | Tape.Float { value; lo; hi } ->
    Stdlib.Printf.sprintf "float %f  (range [%f, %f])" value lo hi
  | Tape.Bool b -> Stdlib.Printf.sprintf "bool %b" b
  | Tape.Marker -> "marker"

let string_of_key (k : Tape.key) =
  if List.is_empty k then "main"
  else
    String.concat ~sep:"."
      (List.map k ~f:(function
        | Tape.Split n -> Stdlib.Printf.sprintf "split%d" n
        | Tape.Salt s -> Stdlib.Printf.sprintf "salt%d" s))

(* Human-readable report. [sexp_of] converts the regenerated value type
   so a "varies freely" verdict can be shown next to concrete
   alternative values -- the best available substitute for a semantic
   component name, since the engine has no type-level view of what a
   tape position corresponds to in the generator's output; showing the
   actual regenerated values lets a reader map the choice to "the
   second tuple element" (or wherever) themselves. *)
let to_string_hum (type a) ~(sexp_of : a -> Sexp.t) (t : a t) : string =
  let buf = Buffer.create 1024 in
  let add fmt = Stdlib.Printf.ksprintf (Buffer.add_string buf) fmt in
  add
    "explain: free-variation analysis of the minimal example (up to %d \
     attempts per choice, %d replays used%s)\n"
    t.attempts_per_choice t.used
    (if t.complete then ""
     else ", budget exhausted before every choice got a full check");
  add
    "  Each choice below was perturbed on its own, holding every other \
     recorded choice fixed, and the test re-run. \"varies freely\" means \
     at least one alternative value at that position still failed the \
     test -- that part of the example is not what makes it fail. \"no \
     variation found\" is a negative result from a BOUNDED search, not \
     proof the choice is load-bearing: if there is nothing clearly \
     suspicious, we refuse the temptation to guess.\n";
  List.iter t.choices ~f:(fun cr ->
    let loc = Stdlib.Printf.sprintf "%s[%d]" (string_of_key cr.stream_key) cr.index in
    match cr.outcome with
    | No_alternative_possible ->
      add "  %-14s %-30s -- only one legal value; freedom is not applicable\n"
        loc (string_of_choice cr.original)
    | No_variation_found ->
      add
        "  %-14s %-30s -- no variation found in %d tr%s (may still be free; \
         search was bounded)\n"
        loc (string_of_choice cr.original) cr.tries
        (if cr.tries = 1 then "y" else "ies")
    | Varies { examples } ->
      add "  %-14s %-30s -- VARIES FREELY (%d/%d tries still failed), e.g.:\n"
        loc (string_of_choice cr.original) (List.length examples) cr.tries;
      List.iter examples ~f:(fun v ->
        add "      still fails with: %s\n" (Sexp.to_string (sexp_of v))));
  Buffer.contents buf
