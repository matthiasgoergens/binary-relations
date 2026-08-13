(* Source-compatible replacement for ordinary Base_quickcheck.Test calls:
   same Config and (module S) shape, and the same five callable entry points.
   It is not a semantic implementation of the Base Test module type:
   [with_sample] retains Base's stock sequence rather than previewing this
   module's taped, edge-biased [run] sequence, and [quickcheck_shrinker] is
   accepted but ignored. Shrinking is the tape engine's replay-based search
   over [quickcheck_generator]. *)

open! Base
module Config = Base_quickcheck.Test.Config
module type S = Base_quickcheck.Test.S

(* Raised when a failure was observed but its minimal example no longer
   reproduces. Distinct from an ordinary test failure: the run is
   neither a pass nor a clean failure, and silently choosing either
   would be wrong. See [report_failure]. *)
exception Flaky_test of string

let default_config = Base_quickcheck.Test.default_config

(* Sampling does not shrink.  These two functions deliberately retain
   base_quickcheck's stock sample sequence and precise lazy semantics; they are
   source-compatible utilities, not a preview of [Tape_test.run]'s taped,
   edge-biased generation schedule.  In particular, generators of functions
   may be observed in the callback rather than while the value is generated. *)
let with_sample = Base_quickcheck.Test.with_sample
let with_sample_exn = Base_quickcheck.Test.with_sample_exn

(* RO6 (outreach/ro-roadmap.md): re-exported here, alongside [run]/
   [run_exn]/[result], because this is the module a suite actually
   opens/qualifies against -- the natural place for the property
   function to reach [assume]/[event], mirroring how Hypothesis exports
   both from the top-level [hypothesis] package rather than a separate
   "runner" module. See [Tape_stats] for the implementation. *)
let assume = Tape_stats.assume
let event = Tape_stats.event

(* How much of the statistics report to print, on every run
   (pass or fail) unless [`Silent]:
   - [`Silent]: nothing (the pre-RO6 behavior).
   - [`Summary] (default): one line -- cases tried, valid, DISCARDED,
     failing, and which health checks fired, if any. This is the direct
     answer to the paper's "OCaml's QuickCheck hides output when tests
     succeed" (outreach/paper-full.txt, quoted in ro-roadmap.md): it
     requires no change to how a suite invokes its tests to appear.
   - [`Full]: the summary plus every event() tag and its count, the
     generate/run/shrink time split, and shrink call counts -- the
     analogue of --hypothesis-show-statistics. *)
type report_level =
  [ `Silent
  | `Summary
  | `Full
  ]

let seed_int (seed : Config.Seed.t) =
  match seed with
  | Deterministic s -> Hashtbl.hash s
  | Nondeterministic ->
    (* Must NOT use [Random.bits ()], which reads the process-global
       state and is deterministic unless something else happened to
       self-init it -- so "nondeterministic" silently gave the same seed
       every run. base_quickcheck itself uses [make_self_init]. Found in
       review of 061923e. *)
    Random.State.bits (Random.State.make_self_init ())

(* Regression files: one lowercase-hex serialized tape per line,
   optional trailing "# comment". Replaying a tape regenerates the
   exact persisted failure through the generator, independent of seeds
   and robust to distribution changes. A line that no longer parses or
   generates is a loud error: a regression entry that stops guarding
   must not silently pass. *)
module Regressions = struct
  let hex_of_string s =
    String.concat_map s ~f:(fun c -> Printf.sprintf "%02x" (Char.to_int c))

  let string_of_hex h =
    if String.length h % 2 <> 0 then None
    else
      Option.try_with (fun () ->
        String.init
          (String.length h / 2)
          ~f:(fun i ->
            Char.of_int_exn
              (Int.of_string ("0x" ^ String.sub h ~pos:(i * 2) ~len:2))))

  (* Line format: "<hex tape> @<size> # comment". The size the failure
     was recorded at matters: base_quickcheck combinators read ~size
     for control flow (length bounds, recursion choices), so replaying
     at a different size can regenerate a different value. Legacy lines
     without @size replay at the historical default of 30. *)
  let load path =
    match Stdlib.Sys.file_exists path with
    | false -> Ok []
    | true ->
      let lines = Stdlib.In_channel.with_open_text path Stdlib.In_channel.input_lines in
      List.filter_mapi lines ~f:(fun lineno line ->
        let payload =
          match String.lsplit2 line ~on:'#' with
          | Some (before, _) -> String.strip before
          | None -> String.strip line
        in
        if String.is_empty payload then None
        else begin
          let hex, size =
            match String.lsplit2 payload ~on:'@' with
            | Some (hex, size_str) ->
              (String.strip hex, Int.of_string_opt (String.strip size_str))
            | None -> (payload, Some 30)
          in
          match
            (Option.bind (string_of_hex hex) ~f:Tape.deserialize_image, size)
          with
          | Some image, Some size -> Some (Ok (lineno + 1, size, image))
          | _ -> Some (Error (lineno + 1))
        end)
      |> Result.combine_errors
      |> Result.map_error ~f:(fun bad_lines ->
           Error.create_s
             [%message
               "corrupt regression tape; delete the stale line to continue"
                 (path : string)
                 (bad_lines : int list)])

  let append path ~image ~size ~comment =
    Stdlib.Out_channel.with_open_gen
      [ Open_append; Open_creat; Open_text ] 0o644 path
      (fun oc ->
        Stdlib.Printf.fprintf oc "%s @%d # %s\n"
          (hex_of_string (Tape.serialize_image image))
          size comment)
end

(* Hypothesis's own numbers (outreach/hypothesis-sources/engine_hypothesis.py):
   `MAX_SHRINKS: int = 500` (a count) and `MAX_SHRINKING_SECONDS: int =
   300` (wall-clock), two INDEPENDENT knobs -- a user wants to be able
   to say "at most N shrink steps", "at most T seconds", or both, which
   is exactly the pain point behind upstream issues #231 ("Slow
   shrinking gives poor dev experience") and #2340 ("Stop shrink phase
   after timeout when progress is very slow"). Both default GENEROUS on
   purpose, not conservative: the passing path runs on every CI
   invocation and must stay cheap, but this path only runs once a test
   has already failed and is about to be shown to a human; someone who
   needs a tighter bound (a CI job that must not stall) sets a smaller
   value explicitly, rather than every caller paying for the cautious
   default.

   [default_max_shrink_seconds] copies Hypothesis's 300 verbatim: wall-
   clock seconds mean the same thing regardless of what is being
   counted underneath. [default_max_shrinks] deliberately does NOT
   copy Hypothesis's 500 verbatim: Hypothesis's `self.shrinks` counts
   ACCEPTED improvements only ("500" there means 500 successful
   shrinks, typically backed by many times that many rejected
   attempts), whereas [Tape_engine]'s budget counts TOTAL replay
   attempts, accepted or not -- a pre-existing property of how every
   pass in [Tape_engine.shrink] already meters itself, not something
   this task introduced. Reusing "500" as a total-attempt cap would be
   far tighter than Hypothesis's real generosity, and would undershoot
   this project's own measured numbers: the list-length property in
   the README results table already averages 641 TOTAL attempts to
   reach its true minimum on an ordinary seed, leaving "500" almost no
   headroom. [Tape_engine.run]'s pre-existing default of 2000 -- chosen
   with exactly this property set in mind, and already used by
   demo/shrink_table.exe and demo/explain_bench.exe -- gives roughly
   the same margin over that measured worst case (~3x) that
   Hypothesis's 500-accepted-shrinks gives over typical Hypothesis
   usage, so it is reused here rather than inventing a fresh number. *)
let default_max_shrinks = 2000
let default_max_shrink_seconds : float option = Some 300.

(* [Config.shrink_count] is NOT used, and that needs saying out loud
   rather than being discovered.

   This module aliases [Base_quickcheck.Test.Config] so that switching a
   test over is a one-word change, which makes it fair to assume every
   Config field is honoured. [shrink_count] is not, for two reasons.
   It counts base_quickcheck's own rose-tree shrink attempts, a
   different mechanism from the tape budget; and its default of 10_000
   is five times [default_max_shrinks], so adopting it would silently
   loosen the budget and discard the reasoning above.

   Silently ignoring it is still wrong -- a caller setting
   [shrink_count = 0] expecting no shrinking would get up to 2000 tape
   attempts and no indication why. So: warn once, name the knob that
   does work, and carry on. Found in review of 061923e. *)
let warned_shrink_count = ref false

let warn_if_shrink_count_set (config : Config.t) =
  if
    (not !warned_shrink_count)
    && config.shrink_count <> default_config.shrink_count
  then begin
    warned_shrink_count := true;
    Stdlib.prerr_endline
      (Printf.sprintf
         "tapecheck: Config.shrink_count = %d is ignored. It counts           base_quickcheck's rose-tree shrink attempts, which this engine does           not use. Pass ?max_shrinks (total tape attempts, default %d) or           ?max_shrink_seconds instead."
         config.shrink_count default_max_shrinks);
    Stdlib.flush Stdlib.stderr
  end


(* Printed when shrinking stops because it ran out of budget rather
   than because it converged -- the distinction Hypothesis itself
   treats as important enough to warn about loudly (its own "WARNING:
   Hypothesis has spent more than five minutes working to shrink..."
   message on the same MAX_SHRINKING_SECONDS deadline). The tape is
   printed in exactly the "ct1" hex format already used by regression
   files (see [Regressions] above), because that format IS the
   resumable state: unlike a rose-tree shrinker's in-memory search
   state, a tape is already a value you can print, save, and hand back
   in verbatim via [resume_result]/[resume_run]/[resume_run_exn]. *)
let truncation_message ~(image : Tape.image) ~size ~attempts ~max_shrinks
    ~(max_shrink_seconds : float option) =
  let hex = Regressions.hex_of_string (Tape.serialize_image image) in
  let seconds_shown =
    match max_shrink_seconds with
    | None -> "disabled"
    | Some s -> Printf.sprintf "%.0f" s
  in
  Printf.sprintf
    "shrinking TRUNCATED, not converged: stopped after %d attempts \
     (budget: up to %d attempts, up to %ss of wall-clock time -- \
     whichever limit was hit first) without reaching a point where \
     every remaining edit had been tried and none of them helped. The \
     example above is the SMALLEST FOUND SO FAR -- treat it as a lead, \
     not a proof of minimality; a smaller one may still exist.\n\n\
     To keep shrinking from exactly this point, save this tape and \
     resume it:\n\n\
     \  %s @%d\n\n\
     \    Tape_test.resume_run_exn ~tape:\"%s\" ~size:%d ~f:(* your \
     property *) (module Your_module)\n\n\
     Or rerun from scratch with more room: raise ?max_shrinks (currently \
     %d) and/or ?max_shrink_seconds (currently %s).\n"
    attempts max_shrinks seconds_shown hex size hex size max_shrinks
    seconds_shown

(* Shared tail for both a fresh failing run ([result]) and a resumed one
   ([resume_result]): given the tape engine's [failure], decide whether
   the shrunk minimal still reproduces, and if so persist it, print the
   opt-in explain report, and print the truncation report when
   shrinking did not converge. Kept as one function so a resumed run
   gets identical regression/explain/truncation handling to a fresh
   one, rather than two copies that can drift apart. *)
let report_failure (type a e) ~(f : a -> (unit, e) Result.t)
    ~(sexp_of : a -> Sexp.t) ~(gen : a Base_quickcheck.Generator.t)
    ~regressions ~explain ~explain_budget ~max_shrinks ~max_shrink_seconds
    ~size (failure : a Tape_engine.failure) : (unit, a * e) Result.t =
  let { Tape_engine.minimal; image; converged; trail; attempts; _ } =
    failure
  in
  match f minimal with
  | Ok () ->
    (* FLAKY. The engine observed a genuine failure, shrank it, and the
       result no longer reproduces.

       This used to return [Ok ()] -- "treat as passed" -- which is a
       FALSE NEGATIVE and the most damaging kind of bug a testing
       library can have: a real failure was seen and the run reported
       success. Flagged in review, and rightly the highest priority
       finding, because everything else in that review costs shrink
       quality whereas this costs correctness.

       Hypothesis raises rather than swallowing, and so do we now. The
       tape is included because it is the whole point of the model: a
       flaky failure is still exactly reproducible from its recording
       even when the value is not. *)
    let hex = Regressions.hex_of_string (Tape.serialize_image image) in
    let msg =
      String.concat ~sep:"\n"
        [ "tapecheck: FLAKY TEST."
        ; "  A failure was found and shrunk, but the minimal example no \
           longer fails when re-run."
        ; "  This run is NOT a pass: a real failure was observed."
        ; ""
        ; "  Likely causes: the test depends on external state (a clock, a \
           global, an"
        ; "  unsynchronised resource), or the generator is not a pure \
           function of the tape"
        ; "  (check with Tape_engine.check_generator_determinism)."
        ; ""
        ; "  Minimal value: " ^ Sexp.to_string (sexp_of minimal)
        ; "  Resume from this tape with Tape_test.resume_run_exn ~tape:"
          ^ hex
        ]
    in
    raise (Flaky_test msg)
  | Error e ->
    Option.iter regressions ~f:(fun path ->
      Regressions.append path ~image ~size ~comment:(Sexp.to_string (sexp_of minimal)));
    (* Phase.explain, switched off by default (?explain:false):
       free-variation analysis over the just-shrunk minimal example,
       printed for a human the way Hypothesis prints its own
       explanation alongside the falsifying example. Off by default
       because it is pure overhead on top of a failing run that is
       about to be reported anyway; on, it costs a bounded number of
       extra replays PER CHOICE (Tape_explain.default_attempts_per_choice,
       configurable via ?explain_budget). *)
    if explain then
      Stdlib.print_string
        (Tape_explain.to_string_hum ~sexp_of
           (Tape_explain.analyze ~gen ~size
              ~test:(fun v -> Result.is_ok (f v))
              ~attempts_per_choice:explain_budget ~trail image));
    (* Truncated vs converged must never be silently lost -- see
       [truncation_message]. Unconditional, unlike ?explain: this is
       safety information about how much to trust [minimal], not an
       optional extra report. *)
    if not converged then
      Stdlib.print_string
        (truncation_message ~image ~size ~attempts ~max_shrinks
           ~max_shrink_seconds);
    Error (minimal, e)

let result (type a e) ~(f : a -> (unit, e) Result.t)
    ?(config = default_config) ?(examples = []) ?regressions
    ?(realign = `Both) ?(explain = false)
    ?(explain_budget = Tape_explain.default_attempts_per_choice)
    ?(max_shrinks = default_max_shrinks)
    ?(max_shrink_seconds = default_max_shrink_seconds)
    ?(report : report_level = `Summary) ?(suppress_health_check = [])
    ?db ?db_key ?stats (module M : Base_quickcheck.Test.S with type t = a) :
    (unit, a * e) Result.t =
  (* RO6: [stats]/[health] are shared across every [Tape_engine.run]
     call in the fresh-generation loop below (one call per size value,
     config.test_count of them -- 10,000 by default), so the discard
     count and the health-check window both see "the whole test run",
     not just its first generated case. *)
  let stats = match stats with Some s -> s | None -> Tape_engine.no_stats () in
  let health = Tape_health.create () in
  (match (db, db_key) with
   | Some _, None ->
     Error.raise_s
       [%message "?db requires ?db_key (use a stable, property-specific key)"]
   | None, Some _ -> Error.raise_s [%message "?db_key requires ?db"]
   | Some _, Some _ | None, None -> ());
  let print_report () =
    match report with
    | `Silent -> ()
    | `Summary -> Stdlib.print_endline (Tape_engine.stats_summary_line stats)
    | `Full -> Stdlib.print_string (Tape_engine.stats_to_string_hum stats)
  in
  let test v = Result.is_ok (f v) in
  (* tapecheck#1, the two paths the engine's run loop never sees.
     Neither [?regressions] nor [?examples] goes through
     [Tape_engine.run], so a failure found by either returned [Error]
     while the summary line said "0 cases (0 valid, 0 discarded, 0
     failing)" -- the return value and the report contradicting each
     other, which is the whole subject of the issue.

     Whether a user-supplied example is a "case" was left open as a
     design question, on the grounds that neither runs a GENERATED
     case, so 0 is arguably honest. Settled the other way, because the
     invariant being broken is not "generated cases are counted" but "a
     returned failure is never reported as 0 failing" -- and that one
     does not care where the value came from. A user handed it over, it
     ran, and it failed.

     [Invalid_example] counts as a discard, matching what the engine
     does with an [assume] that rejects a generated case. *)
  let count_verdict : (unit, e) Result.t -> unit = function
    | Ok () -> stats.Tape_engine.cases_valid <- stats.Tape_engine.cases_valid + 1
    | Error _ ->
      stats.Tape_engine.cases_failed <- stats.Tape_engine.cases_failed + 1
  in
  (* Persisted failures replay first: they are the cheapest and the
     most likely to fail again. *)
  (* Replay EVERY regression entry before deciding anything: a real
     counterexample from any entry is reported immediately, while
     entries that replay to passing values are collected and raised at
     the END of the whole run, so one stale line neither hides a
     failure in a later entry nor blocks fresh generation (the
     blast-radius lesson from the sibling Rust engine's review). *)
  let stale_entries = ref [] in
  let regression_failure =
    match regressions with
    | None -> None
    | Some path ->
      (match Regressions.load path with
       | Error err -> Error.raise err
       | Ok entries ->
         List.find_map entries ~f:(fun (line, size, image) ->
           (* Apply the property while the tape is live: a persisted
              failure that involves a generated function only
              reproduces if the function's streams stay
              tape-controlled during [f]. *)
           let value, verdict =
             Tape_engine.replay_image_and_apply M.quickcheck_generator
               ~size image ~f
           in
           count_verdict verdict;
           match verdict with
           | Error e -> Some (Error (value, e))
           | Ok () ->
             stale_entries := line :: !stale_entries;
             None))
  in
  let finish_run (result : (unit, a * e) Result.t) : (unit, a * e) Result.t =
    match (result, List.rev !stale_entries, regressions) with
    | Error _, _, _ | _, [], _ | _, _, None -> result
    | Ok (), stale, Some path ->
      (* Everything passes, but entries stopped guarding: loud, with
         the complete list, after full coverage ran. *)
      Error.raise_s
        [%message
          "regression tape entries replay to passing values; the bugs \
           they guarded may be fixed (delete the lines) or the \
           generator has drifted (re-record them)"
            (path : string)
            ~lines:(stale : int list)]
  in
  match regression_failure with
  | Some err ->
    (* Route through the same report path as a fresh-generation failure:
       without this a regression-entry failure was the one result that
       printed no summary line at all (tapecheck#11). *)
    print_report ();
    err
  | None ->
    finish_run
      @@
  let example_failure =
    List.find_map examples ~f:(fun v ->
      match f v with
      | Ok () as ok ->
        count_verdict ok;
        None
      | Error e as err ->
        count_verdict err;
        Some (Error (v, e))
      | exception Tape_stats.Invalid_example ->
        stats.Tape_engine.cases_invalid
        <- stats.Tape_engine.cases_invalid + 1;
        None)
  in
  match example_failure with
  | Some err ->
    print_report ();
    err
  | None ->
    let base_seed = seed_int config.seed in
    let sizes =
      Sequence.take config.sizes config.test_count |> Sequence.to_list
    in
    if List.length sizes < config.test_count then
      Error.raise_s
        [%message
          "insufficient size values for test count"
            ~test_count:(config.test_count : int)
            ~sizes_available:(List.length sizes : int)];
    let failure = ref None in
    let case = ref 0 in
    warn_if_shrink_count_set config;
    let sizes = Array.of_list sizes in
    (* Failure database (parity review #6: Tape_db existed but was not
       reachable from here, so the feature was unusable from the normal
       entry point). Replay a stored tape FIRST: a bug that is still
       present reproduces immediately instead of after a search, and a
       fixed one has its entry deleted so it costs nothing again.
       Requires BOTH ?db and ?db_key -- a database with no key would
       collide across every test in a suite. *)
    let db_entry =
      match (db, db_key) with
      | Some d, Some k -> Some (d, k)
      | None, None -> None
      | Some _, None | None, Some _ -> assert false
    in
    (match db_entry with
     | None -> ()
     | Some (d, k) -> (
       match Tape_db.load_sized d ~key:k with
       | None -> ()
       | Some (img, saved_size) -> (
         (* Replay at the size the failure was FOUND at, not sizes.(0).
            A tape recorded at size 40 can regenerate a different value
            at size 0 -- the tape only covers the draws it recorded, and
            size guides anything past its end -- and the entry would
            then look stale and be deleted. Entries written before the
            size was persisted report None and fall back as before. *)
         let replay_size =
           match saved_size with
           | Some n when n >= 0 -> n
           | _ when Array.length sizes > 0 -> sizes.(0)
           | _ -> 30
         in
         match
           Tape_engine.resume M.quickcheck_generator ~test ~realign
             ~size:replay_size ~budget:max_shrinks
             ~max_seconds:max_shrink_seconds ~stats img
         with
         | Tape_engine.Passed _ ->
           (* Stale: the bug is fixed. Drop it, or the database only
              grows and re-runs get slower rather than faster. *)
           Tape_db.remove d ~key:k
         | Tape_engine.Failed engine_failure -> (
           match
             report_failure ~f ~sexp_of:M.sexp_of_t
               ~gen:M.quickcheck_generator ~regressions ~explain
               ~explain_budget ~max_shrinks ~max_shrink_seconds
               ~size:replay_size engine_failure
           with
           | Error _ as e -> failure := Some e
           | Ok () -> ()))));
    while Option.is_none !failure && !case < Array.length sizes do
      (match
         Tape_engine.run M.quickcheck_generator ~test ~realign
           ~seed:(base_seed + !case) ~count:1 ~size:sizes.(!case)
    (* Budget stays master's ?max_shrinks rather than the branch's
       config.shrink_count: shrink_count defaults to 10_000, five
       times default_max_shrinks, and counts base_quickcheck's own
       rose-tree attempts. Adopting it here would silently loosen
       the budget and invalidate the reasoning recorded at
       default_max_shrinks. The warning added in 0570c1f keeps that
       choice visible to callers. *)
           ~budget:max_shrinks ~max_seconds:max_shrink_seconds ~stats
           ~health ~suppress_health_check
       with
      | Tape_engine.Passed _ -> ()
      | Tape_engine.Failed engine_failure -> (
        match
          report_failure ~f ~sexp_of:M.sexp_of_t ~gen:M.quickcheck_generator
            ~regressions ~explain ~explain_budget ~max_shrinks
            ~max_shrink_seconds ~size:sizes.(!case) engine_failure
        with
        | Error _ as e ->
          failure := Some e;
          (match db_entry with
           | None -> ()
           | Some (d, k) ->
             Tape_db.save d ~key:k ~size:sizes.(!case)
               engine_failure.Tape_engine.image)
        | Ok () -> ()));
      Int.incr case
    done;
    print_report ();
    (match !failure with
     | Some err -> err
     | None -> Ok ())

(* [Or_error.try_with]/[try_with_join] catch EVERY exception, including
   [Tape_stats.Invalid_example] -- but that one must propagate all the
   way down into [Tape_engine.run_and_test]'s own handler, or
   [Tape_test.assume] would silently stop working the moment a property
   is run through [run]/[run_exn] rather than [result] (whose ~f is the
   caller's own, never pre-wrapped). These behave exactly like their
   Or_error counterparts for every other exception, but re-raise
   [Invalid_example] instead of converting it to an [Error]. *)
let try_with_join_preserving_assume f =
  match f () with
  | result -> result
  | exception Tape_stats.Invalid_example -> raise Tape_stats.Invalid_example
  | exception exn -> Or_error.of_exn exn

let try_with_preserving_assume f =
  match f () with
  | result -> Ok result
  | exception Tape_stats.Invalid_example -> raise Tape_stats.Invalid_example
  | exception exn -> Or_error.of_exn exn

let run (type a) ~(f : a -> unit Or_error.t) ?config ?examples ?regressions
    ?realign ?explain ?explain_budget ?max_shrinks ?max_shrink_seconds ?report ?suppress_health_check ?db ?db_key ?stats
    (module M : Base_quickcheck.Test.S with type t = a) : unit Or_error.t =
  let f v = try_with_join_preserving_assume (fun () -> f v) in
  match
    result ~f ?config ?examples ?regressions ?realign ?explain ?explain_budget
      ?max_shrinks ?max_shrink_seconds ?report ?suppress_health_check ?db
      ?db_key ?stats (module M)
  with
  | Ok () -> Ok ()
  | Error (input, error) ->
    Or_error.error_s
      [%message
        "Base_quickcheck.Test.run: test failed (tape engine)"
          (input : M.t)
          (error : Error.t)]

let run_exn (type a) ~(f : a -> unit) ?config ?examples ?regressions ?realign
    ?explain ?explain_budget ?max_shrinks ?max_shrink_seconds ?report ?suppress_health_check ?db ?db_key ?stats
    (module M : Base_quickcheck.Test.S with type t = a) : unit =
  let f v = try_with_preserving_assume (fun () -> f v) in
  run ~f ?config ?examples ?regressions ?realign ?explain ?explain_budget
    ?max_shrinks ?max_shrink_seconds ?report ?suppress_health_check ?db
    ?db_key ?stats (module M)
  |> Or_error.ok_exn

(* Resumable shrinking: continue from a tape printed by
   [truncation_message] above (or from any other source of a saved
   "ct1" hex tape, e.g. a regression file's tape column) with a FRESH
   budget, instead of re-searching for a failure from scratch. This is
   the payoff of the tape being a serializable recording rather than an
   in-memory rose-tree shrink state: the stopping point of a truncated
   run is a value you can print, save, and hand back in verbatim.
   [size] must match the size the tape was recorded at (same caveat as
   a regression file's "@size" column: base_quickcheck combinators read
   ~size for control flow, so replaying at a different size can
   regenerate a different value); the historical default of 30 matches
   [Regressions]'s own default for a size-less entry. *)
let resume_result (type a e) ~(f : a -> (unit, e) Result.t) ?(size = 30)
    ?regressions ?(realign = `Both) ?(explain = false)
    ?(explain_budget = Tape_explain.default_attempts_per_choice)
    ?(max_shrinks = default_max_shrinks)
    ?(max_shrink_seconds = default_max_shrink_seconds) ~(tape : string)
    (module M : Base_quickcheck.Test.S with type t = a) :
    (unit, a * e) Result.t =
  let test v = Result.is_ok (f v) in
  match
    Option.bind (Regressions.string_of_hex tape) ~f:Tape.deserialize_image
  with
  | None ->
    Error.raise_s
      [%message
        "corrupt tape: could not parse the hex-encoded image" (tape : string)]
  | Some image -> (
    match
      Tape_engine.resume M.quickcheck_generator ~test ~size ~realign
        ~budget:max_shrinks ~max_seconds:max_shrink_seconds image
    with
    | Tape_engine.Passed _ ->
      (* Loud, not a silent Ok (): mirrors the existing stale-
         regression-entry handling above -- a tape that stops
         reproducing means either the generator drifted or this tape
         was never a real failure, and both deserve the caller's
         attention rather than a quiet pass. *)
      Error.raise_s
        [%message
          "resumed tape no longer fails: nothing to shrink (the generator \
           or the property may have changed since this tape was saved)"
            (tape : string)]
    | Tape_engine.Failed engine_failure ->
      report_failure ~f ~sexp_of:M.sexp_of_t ~gen:M.quickcheck_generator
        ~regressions ~explain ~explain_budget ~max_shrinks ~max_shrink_seconds
        ~size engine_failure)

let resume_run (type a) ~(f : a -> unit Or_error.t) ?size ?regressions
    ?realign ?explain ?explain_budget ?max_shrinks ?max_shrink_seconds ~tape
    (module M : Base_quickcheck.Test.S with type t = a) : unit Or_error.t =
  (* Preserving, exactly as [run] above: plain [Or_error.try_with_join]
     catches [Invalid_example] too, which turns an assume-REJECTED input
     into a reported counterexample on the resumed path. *)
  let f v = try_with_join_preserving_assume (fun () -> f v) in
  match
    resume_result ~f ?size ?regressions ?realign ?explain ?explain_budget
      ?max_shrinks ?max_shrink_seconds ~tape (module M)
  with
  | Ok () -> Ok ()
  | Error (input, error) ->
    Or_error.error_s
      [%message
        "Base_quickcheck.Test.run: test failed (tape engine, resumed)"
          (input : M.t)
          (error : Error.t)]

let resume_run_exn (type a) ~(f : a -> unit) ?size ?regressions ?realign
    ?explain ?explain_budget ?max_shrinks ?max_shrink_seconds ~tape
    (module M : Base_quickcheck.Test.S with type t = a) : unit =
  let f v = try_with_preserving_assume (fun () -> f v) in
  resume_run ~f ?size ?regressions ?realign ?explain ?explain_budget
    ?max_shrinks ?max_shrink_seconds ~tape (module M)
  |> Or_error.ok_exn
