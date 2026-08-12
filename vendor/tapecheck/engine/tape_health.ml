(* RO6 health checks (outreach/ro-roadmap.md, outreach/hypothesis-inventory.md
   section 2): proactive warnings that a GREEN test is not actually
   testing much. Ported from Hypothesis's [record_for_health_check] /
   [HealthCheckState]
   (outreach/hypothesis-sources/engine_hypothesis.py, read directly --
   see the constants and logic around lines 116-215, 789-915, and
   1186-1210). Four of Hypothesis's checks transfer; two
   (function_scoped_fixture, differing_executors) are pytest-fixture-
   and executor-specific concepts with no OCaml analogue and are
   intentionally not ported (outreach/hypothesis-inventory.md section 2
   already reaches this conclusion). [nested_given] doesn't apply
   either: this engine has no nested-property call shape to detect.

   Posture, deliberately kept from Hypothesis: a health check is a
   PROACTIVE WARNING about the TEST's rigor, not a correctness bug in
   the code under test -- but Hypothesis's own [fail_health_check]
   (internal/healthcheck.py) actually RAISES an exception that fails
   the run unless suppressed, and this port does the same, for the
   same reason this codebase already gives a corrupt regression tape a
   loud failure rather than a silent pass (engine/tape_test.ml,
   [Regressions.load]): a warning that is easy to scroll past defeats
   the point of catching the problem early. [suppress_health_check] is
   the escape hatch, exactly mirroring Hypothesis's
   [@settings(suppress_health_check=...)]. *)

open! Base

type t =
  | Filter_too_much
  | Too_slow
  | Data_too_large
  | Large_base_example
[@@deriving sexp_of]

let equal (a : t) (b : t) =
  match (a, b) with
  | Filter_too_much, Filter_too_much -> true
  | Too_slow, Too_slow -> true
  | Data_too_large, Data_too_large -> true
  | Large_base_example, Large_base_example -> true
  | (Filter_too_much | Too_slow | Data_too_large | Large_base_example), _ ->
    false

let to_string = function
  | Filter_too_much -> "filter_too_much"
  | Too_slow -> "too_slow"
  | Data_too_large -> "data_too_large"
  | Large_base_example -> "large_base_example"

(* Thresholds. Where Hypothesis's own constant transfers as a count
   (cases observed, not bytes), we keep its exact number, cited inline
   below. Where the unit doesn't transfer (byte buffer size), we pick
   an analogous choice-count threshold and say why -- see the
   write-up (agent-tapecheck-stats.md) for the full reasoning. *)

(* Hypothesis: max_valid_draws = 10 (engine.py, record_for_health_check).
   The health-check WINDOW closes after this many valid cases; nothing
   past it is tracked, so a rare late burst of filtering never trips a
   check that only looks at a cheap early sample. Kept exactly. *)
let max_valid_draws = 10

(* Hypothesis: max_invalid_draws = 50 -> HealthCheck.filter_too_much.
   Kept exactly: it's a pure case count, no unit conversion needed. *)
let max_invalid_draws = 50

(* Hypothesis: max_overrun_draws = 20 -> HealthCheck.data_too_large,
   counting cases where GENERATION ITSELF overran a fixed BUFFER_SIZE
   (8 * 1024 bytes) and was aborted mid-draw. This engine's tape has no
   such fixed cap during generation (Tape.overrun_now is always false
   while recording -- it only ever fires on a SHRINK REPLAY that
   truncated; see tape.ml's [pop]), so "generation was aborted for
   being too large" cannot happen here at all. We keep the spirit
   (some cases are routinely, needlessly large) by counting ordinary
   completed cases whose tape exceeds [data_too_large_choices] instead
   of counting aborted ones; the case COUNT threshold (20) is kept
   exactly, since it's unrelated to the byte-vs-choice unit question. *)
let max_large_draws = 20

(* Hypothesis: draw_time_limit = max(1.0, 5 * deadline), deadline
   defaulting to 200ms -> 1.0 second (the max(...) floor dominates at
   the default). This engine has no deadline setting (yet), so we keep
   the 1.0s figure Hypothesis itself lands on at its own default,
   rather than inventing a new number. *)
let generate_time_limit_seconds = 1.0

(* Hypothesis: HealthCheck.large_base_example fires when the smallest
   POSSIBLE example's byte length exceeds BUFFER_SIZE / 2 = 4096 bytes
   (engine.py: "zero_data.length * 2 > BUFFER_SIZE"). Hypothesis's
   choices are packed into a variable-width byte buffer; ours are a
   typed [Tape.choice array] where every entry is a whole Integer/
   Float/Bool/Marker record, so "bytes" and "choices" are not the same
   unit and a straight numeric transfer (4096) would be meaningless --
   see the write-up for the reasoning. We pick 256 CHOICES instead: an
   order of magnitude comfortably above every scalar/short-tuple/short-
   list property in this repo's own results table (README.md), and
   comfortably below what a naturally sprawling generator (a list with
   a large minimum size, deeply nested records) would produce even at
   its smallest. *)
let large_base_example_choices = 256

(* Hypothesis's data_too_large threshold (8192 bytes) is exactly double
   large_base_example's (4096 bytes); we keep that 2x RATIO rather than
   the absolute figures, since the ratio -- "routinely large" is a
   somewhat higher bar than "smallest possible is already large" -- is
   the part of the design worth preserving. *)
let data_too_large_choices = 2 * large_base_example_choices

type state = {
  mutable valid : int;
  mutable invalid : int;
  mutable large : int;
  mutable generate_time : float;
  mutable closed : bool;
  (* Window closed: stop tracking (Hypothesis: health_check_state = None). *)
  mutable checked_base_example : bool;
  (* [maybe_check_large_base_example] runs at most once per state,
     regardless of how many times it is called -- needed because
     [Tape_engine.run] may be invoked many times sharing one [state]
     (Tape_test.result calls it once per size value, ~10,000 times by
     default, each generating exactly one case; the health check must
     still see this as "one test run", not 10,000). *)
  mutable base_example_choices : int;
  (* Recorded for the message/report once [maybe_check_large_base_example]
     has run; meaningless (0) before that. *)
  mutable fired : t list;
      (* Every check that has fired so far (whether suppressed or not),
         most recent first; used for the statistics report and to
         guard against re-firing the same check twice. *)
}

let create () =
  { valid = 0
  ; invalid = 0
  ; large = 0
  ; generate_time = 0.
  ; closed = false
  ; checked_base_example = false
  ; base_example_choices = 0
  ; fired = []
  }

let already_fired state check = List.mem state.fired check ~equal

let message_for check ~state =
  match check with
  | Data_too_large ->
    Printf.sprintf
      "health check data_too_large: %d of the first %d cases had a \
       recorded tape of more than %d choices. Testing with inputs this \
       large tends to be slow, and to produce failures that are hard to \
       shrink and hard to understand; consider decreasing the amount of \
       data generated (e.g. a smaller minimum collection size). Suppress \
       with ~suppress_health_check:[Tape_health.Data_too_large] if inputs \
       this large are expected."
      state.large
      (state.valid + state.invalid + state.large)
      data_too_large_choices
  | Filter_too_much ->
    Printf.sprintf
      "health check filter_too_much: %d inputs were generated \
       successfully, while %d were discarded (assume(), or a filtered \
       generator). This much filtering makes generation slow, and may \
       leave the test far less rigorous than it looks -- consider \
       narrowing the generator instead of filtering after the fact. \
       Suppress with ~suppress_health_check:[Tape_health.Filter_too_much] \
       if this much filtering is expected."
      state.valid state.invalid
  | Too_slow ->
    Printf.sprintf
      "health check too_slow: input generation is slow -- only %d valid \
       inputs were generated in %.2fs. This is usually an expensive \
       generator, or expensive work accidentally happening during \
       generation rather than in the test body. Suppress with \
       ~suppress_health_check:[Tape_health.Too_slow] if this is expected."
      state.valid state.generate_time
  | Large_base_example ->
    Printf.sprintf
      "health check large_base_example: the smallest natural input for \
       this test already uses %d choices (over the %d-choice threshold). \
       This makes it harder to generate small inputs and to shrink well; \
       consider a smaller base case (e.g. an optional/empty alternative). \
       Suppress with \
       ~suppress_health_check:[Tape_health.Large_base_example] if this is \
       expected."
      state.base_example_choices large_base_example_choices

(* Raise (unless suppressed), and remember that [check] fired either
   way so it never re-fires and so the statistics report can mention
   it even when suppressed. *)
let fire state ~suppress check =
  if not (already_fired state check) then begin
    state.fired <- check :: state.fired;
    if not (List.mem suppress check ~equal) then begin
      let message = message_for check ~state in
      Error.raise_s (Sexp.Atom message)
    end
  end

(* Called once per FRESH generation-phase case (never for shrink-phase
   replays -- Hypothesis stops health-checking once shrinking starts
   too, by clearing health_check_state on the first interesting/failing
   example). [choices] is the resulting tape's total choice count
   ([Tape.image_size]); [generate_time] is the wall-clock seconds spent
   in ONLY the generator call (not the test body), matching Hypothesis's
   [draw_times] (which likewise excludes test-body runtime). *)
let record state ~suppress ~(status : [ `Valid | `Invalid ]) ~choices
    ~generate_time =
  if not state.closed then begin
    state.generate_time <- state.generate_time +. generate_time;
    (* A case whose tape exceeds [data_too_large_choices] is classified
       as [large] ONLY, never ALSO as valid or invalid -- mirroring
       Hypothesis's own three mutually exclusive statuses (VALID,
       INVALID, OVERRUN: see engine.py's [record_for_health_check],
       where [valid_examples]/[invalid_examples]/[overrun_examples] are
       an if/elif/else over [data.status], not three independent
       counters). This matters: if a large case ALSO counted as valid,
       a generator that is ALWAYS large would hit [max_valid_draws] (10)
       and close the window long before [max_large_draws] (20) could
       ever be reached, and [data_too_large] could never fire. *)
    if choices > data_too_large_choices then state.large <- state.large + 1
    else begin
      match status with
      | `Valid -> state.valid <- state.valid + 1
      | `Invalid -> state.invalid <- state.invalid + 1
    end;
    if state.valid >= max_valid_draws then state.closed <- true
    else begin
      if state.large >= max_large_draws then fire state ~suppress Data_too_large;
      if (not state.closed) && state.invalid >= max_invalid_draws then
        fire state ~suppress Filter_too_much;
      if
        (not state.closed)
        && Float.(state.generate_time > generate_time_limit_seconds)
      then fire state ~suppress Too_slow
    end
  end

(* The "smallest natural example" check, independent of the windowed
   counters above: run at most once per [state], regardless of how many
   times [Tape_engine.run] is called sharing this [state] (see the
   [checked_base_example] field comment). [choices] is the choice count
   of the generator's output when every recorded choice on some actual
   generated case is replayed with every choice forced to its target
   value (Tape_engine.image_trivialized, then re-run through the
   generator) -- the tape's analogue of Hypothesis's [zero_data]. *)
let maybe_check_large_base_example state ~suppress ~choices =
  if not state.checked_base_example then begin
    state.checked_base_example <- true;
    state.base_example_choices <- choices;
    if choices > large_base_example_choices then
      fire state ~suppress Large_base_example
  end
