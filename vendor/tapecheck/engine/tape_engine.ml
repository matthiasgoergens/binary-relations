(* The runner: generate with a recording tape, and on failure shrink by
   editing the tape and replaying generation through the UNMODIFIED
   base_quickcheck generator. An edit is accepted iff the test still
   fails and the re-recorded output tape is shortlex-smaller.

   Pass schedule ported from the proptest tape engine
   (proptest-rs/proptest#658): one all-choices-to-target attempt, then
   rounds of lower-and-delete (the length-prefix pass), redistribution,
   and per-choice minimization with bisection, to a fixpoint under an
   attempt budget.

   Streams (design/stream-keyed-tapes.md): a tape is an image (main
   stream plus keyed sub-streams for split-off PRNG states, i.e.
   generated functions). The test runs BEFORE Tape.finish, because
   function draws happen when the test calls the function; the passes
   iterate every stream, so function behaviour shrinks too. *)

open! Base

type 'a failure =
  { minimal : 'a
  ; original : 'a
  ; attempts : int (* test executions spent shrinking *)
  ; choices : Tape.choice array (* main stream of the winning tape *)
  ; image : Tape.image (* the winning tape, for replay/persistence *)
  ; trail : Tape.image list
      (* Every image accepted during shrinking, oldest first, ending
         with [image] itself: [search_attempt] pushes each accepted
         image, including the final one. Empty when no proposal was ever
         accepted -- either the first failure was already fully trivial
         and shrinking never ran, or no pass found anything smaller.
         Hypothesis reports intermediate examples alongside the minimal
         one; this is the same idea, cheap to keep because a
         [Tape.image] is just the
         compact recording, not a materialized value -- replay it with
         [replay_image_and_apply] to see what it built. Secondary output:
         the free-variation analysis in [Tape_explain] is what actually
         answers the paper's "the minimum can mislead" complaint. *)
  ; converged : bool
      (* true iff shrinking stopped because it reached a genuine local
         minimum (a full round of every pass tried and found nothing
         smaller) WITH budget and time still to spare -- i.e. we know
         for certain nothing more was possible, not just that we ran
         out of room to keep looking. false means [budget] (attempt
         count) or the wall-clock deadline was exhausted first: the
         search was TRUNCATED, and [minimal] may still be reducible
         further. This distinction must never be silently lost --
         Hypothesis's own MAX_SHRINKS/MAX_SHRINKING_SECONDS exist
         because slow shrinking is a real, reported pain point
         (upstream issues #231, #2340), and a truncated result that
         looks identical to a converged one is worse than no result:
         it invites treating a merely-best-effort example as the true
         minimum. See [Tape_test]'s handling for how this is surfaced
         to a human, including how to resume shrinking from exactly
         this point. *)
  }

type 'a result =
  | Passed of { cases : int }
  | Failed of 'a failure

let clamp64 = Tape.clamp_int64

(* Total, like [clamp64]: a hand-edited tape can carry CROSSED float
   bounds ([lo > hi]) -- nothing at deserialize rejects them -- and
   [Float.clamp_exn] answers those with [Assert_failure], which is how
   [resume] used to crash on such an image (tapecheck#11).
   [Tape.clamp_float] clamps instead of asserting, so the engine treats
   a crossed-bounds choice as merely odd data, not a fatal one. *)
let clampf = Tape.clamp_float

(* Fresh draws during replay (misaligned or overrun positions) sample
   from this fixed seed so every attempt, sequential or pooled, sees
   the same fallback stream. *)
let replay_fresh_seed = 0x7ea9e

(* Both delegate to [Tape.Domain], which states the target next to the
   comparison it has to agree with. They were independent definitions
   here, in a different file from [compare_choice], with nothing
   checking that "smallest" matched "smaller". Kept as names because
   they are the vocabulary the passes below are written in. *)
let choice_at_target = Tape.Domain.at_target
let trivial_choice = Tape.Domain.target

let with_choice tape_choices i c =
  let copy = Array.copy tape_choices in
  copy.(i) <- c;
  copy

let with_deleted_block tape_choices ~pos ~len =
  Array.append
    (Array.sub tape_choices ~pos:0 ~len:pos)
    (Array.sub tape_choices ~pos:(pos + len)
       ~len:(Array.length tape_choices - pos - len))

(* Segments: segment 0 is the main stream, segment s >= 1 is
   streams.(s-1). All shrink passes run over every segment. *)
let seg_count (img : Tape.image) = 1 + Array.length img.streams

let seg_get (img : Tape.image) s =
  if s = 0 then img.main else snd img.streams.(s - 1)

let seg_set (img : Tape.image) s arr : Tape.image =
  if s = 0 then { img with main = arr }
  else
    { img with
      streams =
        Array.mapi img.streams ~f:(fun i (k, a) ->
          if i = s - 1 then (k, arr) else (k, a))
    }

let image_all_trivial (img : Tape.image) =
  Array.for_all img.main ~f:choice_at_target
  && Array.for_all img.streams ~f:(fun (_, arr) ->
       Array.for_all arr ~f:choice_at_target)

let image_trivialized (img : Tape.image) : Tape.image =
  { main = Array.map img.main ~f:trivial_choice
  ; streams =
      Array.map img.streams ~f:(fun (k, arr) ->
        (k, Array.map arr ~f:trivial_choice))
  }

(* Generate under an already-configured tape mode and run the test
   BEFORE finishing the tape: generated functions draw during the test
   call, and those draws belong on the tape. [tested] is [None] when
   the tape had already overrun during generation (the proposal
   truncated; the test is not worth running). A [tested] verdict of
   [Tape_stats.Case_invalid] means the test called [Tape_stats.assume]
   with a false condition -- RO6 (outreach/ro-roadmap.md): every call
   site that invokes the user's test function must go through here (or
   [run_and_test_timed] below) so that a discarded case is caught and
   accounted for, never left to crash the run as an uncaught
   exception. *)
let run_and_test (type a) ~tape ~(gen : a Base_quickcheck.Generator.t) ~size
    ~seed ~(test : a -> bool) : a * Tape_stats.verdict option * Tape.output =
  let random =
    Splittable_random.For_tape.attach (Splittable_random.of_int seed) tape
  in
  let value = Base_quickcheck.Generator.generate gen ~size ~random in
  let tested =
    if Tape.overrun_now tape then None
    else begin
      Tape_stats.begin_case ();
      Some
        (match test value with
         | true -> Tape_stats.Case_passed
         | false -> Tape_stats.Case_failed
         | exception Tape_stats.Invalid_example -> Tape_stats.Case_invalid)
    end
  in
  let out = Tape.finish tape in
  (value, tested, out)

(* Like [run_and_test], but for the top-level generate-phase search in
   [run] only: split wall-clock between the generator call and the test
   call (RO6's "time spent generating vs running" statistic), and skip
   the overrun check ([Tape.overrun_now] can only become true on a
   SHRINK REPLAY that ran out of recorded input -- see tape.ml's [pop]
   -- and this path always starts a fresh recording, never a replay, so
   it is always false here). *)
let run_and_test_timed (type a) ~tape ~(gen : a Base_quickcheck.Generator.t)
    ~size ~seed ~(test : a -> bool) :
    a * Tape_stats.verdict * Tape.output * float * float =
  let random =
    Splittable_random.For_tape.attach (Splittable_random.of_int seed) tape
  in
  let t0 = Stdlib.Sys.time () in
  let value = Base_quickcheck.Generator.generate gen ~size ~random in
  let t1 = Stdlib.Sys.time () in
  Tape_stats.begin_case ();
  let verdict =
    match test value with
    | true -> Tape_stats.Case_passed
    | false -> Tape_stats.Case_failed
    | exception Tape_stats.Invalid_example -> Tape_stats.Case_invalid
  in
  let t2 = Stdlib.Sys.time () in
  let out = Tape.finish tape in
  (value, verdict, out, t1 -. t0, t2 -. t1)

(* Dispatches to [run_and_test] or [run_and_test_timed] depending on
   [timed], behind one uniform return shape, so [run]'s generate-phase
   loop below can call ONE function regardless of whether timing is
   worth paying for on this particular case.

   Why this matters (measured in
   demo/stats_overhead_bench.ml): [Stdlib.Sys.time()] is a real
   syscall, and THREE calls per case (around generate, around the test)
   turned out to dominate the entire per-case cost -- +327% versus a
   hand-rolled loop with none of RO6's bookkeeping, on a cheap
   single-int-draw property. Health checks only need per-case timing
   during Hypothesis's own bounded early window (closed by
   Tape_health.max_valid_draws/max_invalid_draws/max_large_draws, at
   most on the order of tens of cases); a run of thousands of cases
   pays the timing cost on none of the rest once the window closes.
   [gen_dt]/[run_dt] are simply 0. on an untimed case, so
   [stats.generate_time]/[stats.run_time] undercount a long run
   slightly (they reflect the health-check sampling window, not every
   case) -- an accepted, documented trade-off for keeping the actually
   -expensive part of the passing path cheap; see the write-up. *)
let run_and_test_maybe_timed (type a) ~timed ~tape
    ~(gen : a Base_quickcheck.Generator.t) ~size ~seed ~(test : a -> bool) :
    a * Tape_stats.verdict option * Tape.output * float * float =
  if not timed then
    let value, tested, out = run_and_test ~tape ~gen ~size ~seed ~test in
    (value, tested, out, 0., 0.)
  else
    let value, verdict, out, gen_dt, run_dt =
      run_and_test_timed ~tape ~gen ~size ~seed ~test
    in
    (value, Some verdict, out, gen_dt, run_dt)

(* A persistent worker pool: domains are expensive to spawn (each
   registers a GC domain), so spawn once per shrink and feed batches
   through a mutex-protected queue. *)
module Pool = struct
  type 'r t =
    { mutex : Stdlib.Mutex.t
    ; nonempty : Stdlib.Condition.t
    ; all_done : Stdlib.Condition.t
    ; mutable queue : (int * (unit -> 'r)) list
    ; mutable results : ('r, exn) Result.t option array
    ; mutable pending : int
    ; mutable stop : bool
    ; mutable workers : unit Stdlib.Domain.t list
    }

  let rec worker_loop t =
    Stdlib.Mutex.lock t.mutex;
    let rec take () =
      if t.stop then None
      else
        match t.queue with
        | [] ->
          Stdlib.Condition.wait t.nonempty t.mutex;
          take ()
        | (i, task) :: rest ->
          t.queue <- rest;
          Some (i, task)
    in
    match take () with
    | None -> Stdlib.Mutex.unlock t.mutex
    | Some (i, task) ->
      Stdlib.Mutex.unlock t.mutex;
      (* A raising task (user generator or test) must still account for
         itself, or run_batch waits forever; the exception is stored
         and re-raised on the main domain. *)
      let r =
        match task () with
        | r -> Ok r
        | exception exn -> Error exn
      in
      Stdlib.Mutex.lock t.mutex;
      t.results.(i) <- Some r;
      t.pending <- t.pending - 1;
      if t.pending = 0 then Stdlib.Condition.signal t.all_done;
      Stdlib.Mutex.unlock t.mutex;
      worker_loop t

  (* Clamp to the core count. OxCaml's [do_not_spawn_domains] alert
     spells out why: "spawning more than [recommended_domain_count]
     domains (the CPU core count) will significantly degrade GC
     performance." That is a real footgun independent of OxCaml --
     nothing previously stopped [~domains:64] on an 8-core box from
     getting exactly that degradation -- so this is a fix rather than a
     lint appeasement. Warn once, because silently ignoring what the
     caller asked for is its own kind of surprise. *)
  let warned_about_domains = ref false

  let clamp_domains n =
    let recommended = Stdlib.Domain.recommended_domain_count () in
    if n > recommended then begin
      if not !warned_about_domains then begin
        warned_about_domains := true;
        Stdlib.prerr_endline
          (Printf.sprintf
             "tapecheck: ~domains:%d exceeds the %d recommended for this machine; using %d. More domains than cores degrades GC performance rather than helping."
             n recommended recommended);
        Stdlib.flush Stdlib.stderr
      end;
      recommended
    end
    else n

  let create n =
    let n = clamp_domains n in
    let t =
      { mutex = Stdlib.Mutex.create ()
      ; nonempty = Stdlib.Condition.create ()
      ; all_done = Stdlib.Condition.create ()
      ; queue = []
      ; results = [||]
      ; pending = 0
      ; stop = false
      ; workers = []
      }
    in
    t.workers <-
      List.init n ~f:(fun _ -> Stdlib.Domain.spawn (fun () -> worker_loop t));
    t

  (* Run tasks to completion; returns results in task order. A task
     that raised has its exception re-raised here, on the caller's
     domain, after the whole batch has been accounted for. *)
  let run_batch t tasks =
    let tasks = Array.of_list tasks in
    let n = Array.length tasks in
    Stdlib.Mutex.lock t.mutex;
    t.results <- Array.create ~len:n None;
    t.pending <- n;
    t.queue <- Array.to_list (Array.mapi tasks ~f:(fun i task -> (i, task)));
    Stdlib.Condition.broadcast t.nonempty;
    while t.pending > 0 do
      Stdlib.Condition.wait t.all_done t.mutex
    done;
    let results = t.results in
    Stdlib.Mutex.unlock t.mutex;
    List.map (List.filter_opt (Array.to_list results)) ~f:(function
      | Ok r -> r
      | Error exn -> raise exn)

  let shutdown t =
    Stdlib.Mutex.lock t.mutex;
    t.stop <- true;
    Stdlib.Condition.broadcast t.nonempty;
    Stdlib.Mutex.unlock t.mutex;
    List.iter t.workers ~f:Stdlib.Domain.join
end

(* Shrink-phase accounting for one evaluated proposal, mirroring the
   updates [search_candidate] makes on the sequential path (one replay;
   one test iff the case ran; one misalign on a kind mismatch; one
   discard on an [assume]-rejected case). A pooled worker computes this
   locally and hands it back as data -- [stats] is plain mutable state
   on the main domain and several domains would race on it, the same
   constraint [pool_payload] documents for generate-phase verdicts. The
   main domain folds the contributions in after [Pool.run_batch].

   Without this the pooled arm of [attempt_batch] evaluated every
   proposal invisibly: [attempts] moved while
   [replays]/[tests]/[misaligns] did not (tapecheck#6). *)
type eval_stats =
  { e_replays : int
  ; e_tests : int
  ; e_misaligns : int
  ; e_discards : int
  }

let no_eval_stats =
  { e_replays = 0; e_tests = 0; e_misaligns = 0; e_discards = 0 }

(* Evaluate one proposal in isolation: own tape, own RNG, no shared
   state. Safe to run in a separate domain when the generator and test
   are thread-safe. One replay under [policy]; returns (misaligned,
   stats contribution, still-failing-candidate). *)
let eval_once (type a) ~(gen : a Base_quickcheck.Generator.t) ~size
    ~(test : a -> bool) ~policy proposal =
  let tape = Tape.create () in
  Tape.start_replay_image ~policy tape proposal;
  let _value, tested, out =
    run_and_test ~tape ~gen ~size ~seed:replay_fresh_seed ~test
  in
  let estats =
    { e_replays = 1
    ; e_tests = (match tested with None -> 0 | Some _ -> 1)
    ; e_misaligns = (if out.Tape.misaligned then 1 else 0)
    ; e_discards =
        (match tested with
         | Some Tape_stats.Case_invalid -> 1
         | None | Some (Tape_stats.Case_passed | Tape_stats.Case_failed) -> 0)
    }
  in
  let candidate =
    match tested with
    | Some Tape_stats.Case_failed when not out.Tape.overrun ->
      Some (out.Tape.image, _value)
    | _ -> None
  in
  (out.Tape.misaligned, estats, candidate)

(* Pool-side proposal evaluation honouring the realign policy, so a
   pooled run reaches the SAME result as the sequential engine at any
   ?domains (only [`Both] on a misaligned proposal does the second
   replay). Returns the candidate alongside the summed [eval_stats] of
   the replay(s) it made, for the main domain to fold into [stats]. *)
let eval_proposal (type a) ~(gen : a Base_quickcheck.Generator.t) ~size
    ~(test : a -> bool) ~(realign : [ `Consume | `Freeze | `Both ]) proposal =
  let primary, secondary =
    match realign with
    | `Freeze -> (Tape.Freeze, Tape.Consume)
    | `Consume | `Both -> (Tape.Consume, Tape.Freeze)
  in
  let mis1, es1, c1 = eval_once ~gen ~size ~test ~policy:primary proposal in
  let estats, cands =
    match realign with
    | `Both when mis1 ->
      let _mis2, es2, c2 = eval_once ~gen ~size ~test ~policy:secondary proposal in
      ( { e_replays = es1.e_replays + es2.e_replays
        ; e_tests = es1.e_tests + es2.e_tests
        ; e_misaligns = es1.e_misaligns + es2.e_misaligns
        ; e_discards = es1.e_discards + es2.e_discards
        }
      , [ c1; c2 ] )
    | _ -> (es1, [ c1 ])
  in
  ( List.filter_opt cands
    |> List.min_elt ~compare:(fun (a, _) (b, _) -> Tape.compare_image a b)
  , estats )

(* Realignment strategy for kind mismatches during shrink replay.
   [`Consume] and [`Freeze] use one fixed policy; [`Both] replays a
   MISALIGNED proposal under both and keeps the shortlex-better still
   -failing result (neither policy dominates, and accepted shrinks
   re-verify through the test, so trying both is sound and >= either
   alone). Aligned proposals never pay the second replay. *)
type realign =
  [ `Consume
  | `Freeze
  | `Both
  ]

(* True cost of a shrink, separate from the proposal-count budget:
   [replays] generation runs, [tests] test executions, [misaligns]
   proposals whose replay hit a kind mismatch (the only ones on which
   [`Both] does extra work).

   RO6 (outreach/ro-roadmap.md): the fields below extend this same
   record with the generate-phase accounting the statistics report
   needs -- cases valid/discarded, aggregated event() tags, and a
   three-way time split (generate / run-the-test / shrink). This
   reuses the existing [stats]/[no_stats] rather than adding a parallel
   type, so every existing caller (bench_realign.ml, and anyone who
   already threads a [stats] through [shrink]) keeps working
   unchanged: the new fields just start at their zero value. *)
type stats =
  { mutable replays : int
  ; mutable tests : int
  ; mutable misaligns : int
  ; mutable cases_valid : int (* generate-phase: test ran and passed *)
  ; mutable cases_invalid : int
      (* generate-phase: Tape_stats.assume discarded the case *)
  ; mutable cases_failed : int (* generate-phase: 0 or 1 *)
  ; mutable shrink_discards : int
      (* shrink-phase proposals discarded via assume -- secondary/
         diagnostic only, not health-checked (Hypothesis stops
         health-checking once shrinking starts too). *)
  ; events : (string, int) Hashtbl.t
      (* Tape_stats.event tags, generate-phase cases only, aggregated
         across every case (valid, invalid, or the one failing case). *)
  ; mutable generate_time : float (* wall seconds, Generator.generate only *)
  ; mutable run_time : float (* wall seconds, the test body only *)
  ; mutable shrink_time : float (* wall seconds, the whole shrink phase *)
  ; mutable warnings : Tape_health.t list
      (* Health checks that fired during this run, most recent first --
         populated whether or not each one was suppressed (see
         ?suppress_health_check on [run]); empty when [?domains > 1],
         since health checks are not evaluated in the pooled path (see
         [run]'s comment on why). *)
  }


(* Hypothesis's find_integer (junkdrawer.py:313): the largest k with
   [f k] true, assuming [f 0] is true and f is downward-closed.

   The linear scan over 1..4 BEFORE going exponential is the part that
   matters, and the part I got wrong the first time I tried galloping in
   this engine. Starting from the full range and halving costs
   ~log(range) FAILURES whenever only a small step is accepted, which is
   how the rejected patch took bind from 59 to 984 calls
   (galloping-attempt-REJECTED.patch). Their comment: "it's very hard to
   win big when the result is small. If the result is 0 and we try 2
   first then we've done twice as much work as we needed to!" *)
let find_integer (f : int64 -> bool) : int64 =
  let rec small i =
    if Int64.( > ) i 4L then None
    else if not (f i) then Some (Int64.( - ) i 1L)
    else small (Int64.( + ) i 1L)
  in
  match small 1L with
  | Some r -> r
  | None ->
    let lo = ref 4L and hi = ref 5L in
    let overflow () = Int64.( < ) !hi 0L in
    while (not (overflow ())) && f !hi do
      lo := !hi;
      hi := Int64.( * ) !hi 2L
    done;
    if overflow () then !lo
    else begin
      while Int64.( < ) (Int64.( + ) !lo 1L) !hi do
        let mid =
          Int64.( + ) !lo (Stdlib.Int64.shift_right_logical (Int64.( - ) !hi !lo) 1)
        in
        if f mid then lo := mid else hi := mid
      done;
      !lo
    end

let no_stats () =
  { replays = 0
  ; tests = 0
  ; misaligns = 0
  ; cases_valid = 0
  ; cases_invalid = 0
  ; cases_failed = 0
  ; shrink_discards = 0
  ; events = Hashtbl.create (module String)
  ; generate_time = 0.
  ; run_time = 0.
  ; shrink_time = 0.
  ; warnings = []
  }

(* Diagnostic only: attempts attributed to each shrink pass, plus how
   many proposals were exact repeats of one already tried. Reset at the
   start of every shrink. Used to find where tapecheck spends 641 calls
   on a property Hypothesis finishes in 27 (see
   ../tapecheck-hypothesis-baseline/README.md). *)
let pass_names =
  [| "lower_and_delete"; "(removed: delete_streams)"; "redistribute_pairs"
   ; "minimize_choices"; "pre-loop"; "sort_siblings" |]

let pass_costs = Array.create ~len:6 0
let greedy_cost = ref 0
let duplicate_proposals = ref 0
let distinct_proposals = ref 0
let last_pass_costs () = Array.to_list (Array.mapi pass_costs ~f:(fun i c -> (pass_names.(i), c)))
let last_duplicate_stats () = (!duplicate_proposals, !distinct_proposals)
let last_greedy_cost () = !greedy_cost
(* Instrumentation for the length repair in [minimize_integer] below.
   A mechanism that never fires is indistinguishable from one that is
   absent, so count attempts and successes rather than inferring from
   headline numbers -- that distinction is exactly what showed the
   repair to be inert under the current pass order (one firing in 100
   lengthlist trials). *)
let length_repair_tries = ref 0
let length_repair_hits = ref 0
let last_length_repair () = (!length_repair_tries, !length_repair_hits)

let accepted_shrinks = ref 0
let sweeps = ref 0
let initial_choices = ref 0
let final_choices = ref 0
let scan_i_visits = ref 0
let scan_jk_visits = ref 0
let lad_successes = ref 0

(* Earned probing for the computed repair in lower_and_delete. The probe
   costs one evaluation whether or not it finds anything, so on shapes
   where lowering never shortens the tape it is pure overhead -- bind
   went 52 -> 80 calls and deep bind 141 -> 256 before this cap.

   Same shape as the earned patience above: spend a small fixed number
   of probes finding out whether this property is one where the move
   pays, and stop probing if it never does. A property where it DOES pay
   banks a success immediately and keeps the probe for the rest of the
   shrink. *)
let cr_probes = ref 0
let cr_hits = ref 0
let cr_probe_budget = 8
let last_computed_repair () = (!cr_probes, !cr_hits)
let last_shape () =
  ( !sweeps, !initial_choices, !final_choices, !scan_i_visits, !scan_jk_visits
  , !lad_successes )


(* What a pooled task hands back. The pool's element type is fixed when
   it is created, and ONE pool serves both the generate phase and the
   shrink phase, so the payload has to satisfy both.

   The verdict component exists because pooled generate-phase cases used
   to be uncounted entirely: the worker returned only "did this fail",
   the verdict was dropped on the floor, and [run] reported
   [Passed {cases = 300}] while the statistics said 0 valid and 0
   invalid (tapecheck#1). Counting inside the worker is not an option --
   [stats] is plain mutable state on the main domain and several domains
   would race on it -- so the verdict travels back as data and the main
   domain does the arithmetic. Shrinking passes [None].

   The [eval_stats] half is the same arrangement for pooled SHRINK
   evaluations (tapecheck#6): the worker sums what the replay did, the
   main domain folds it into [stats]. The generate phase has no shrink
   accounting to report and passes [no_eval_stats]. *)
type 'a pool_payload = ('a * eval_stats) * Tape_stats.verdict option

(* Mutable state for a tape SEARCH -- shared by shrinking today, and by
   anything else that proposes edits and keeps the best result.

   Hoisted out of [shrink] so that [target()] (TARGET-PBT.md) and
   multi-bug reporting (MULTI-BUG.md) can reuse the proposal machinery
   instead of copying it. Both were blocked on exactly this: every pass
   in [shrink] closed over a single [best], so the refactor got dearer
   the longer it waited.

   The one field that differs between users is [accept]: shrinking
   accepts a strictly shortlex-smaller still-failing image, a target
   search would accept an improved score, and multi-bug would accept a
   still-failing image with the SAME origin. Everything else -- budget
   accounting, duplicate skipping, realignment, the worker pool -- is
   common. *)
type 'a search =
  { s_gen : 'a Base_quickcheck.Generator.t
  ; s_size : int
  ; s_test : 'a -> bool
  ; s_tape : Tape.t
  ; s_realign : realign
  ; s_stats : stats
  ; s_pool : (Tape.image * 'a) option pool_payload Pool.t option
        (* The payload is shared with the GENERATE phase, which runs on
           the same pool and needs to report each case's verdict back to
           the main domain -- worker domains cannot safely touch [stats]
           themselves. Shrinking has no verdict to report and passes
           [None], but it DOES have accounting to report: each evaluated
           proposal's [eval_stats] rides the first component; see
           [pool_payload]. *)
  ; s_domains : int
  ; s_budget : int
  ; s_max_shrinks : int
  ; s_deadline : float option
    (* These are the SAME ref cells the caller's own loop uses, not
       copies. That is what makes the hoist free: [shrink]'s passes go
       on reading [!best] and [!attempts] directly, while the shared
       proposal machinery below reads [st.s_best] -- one storage
       location, no bulk rewrite of 69 call sites, and no risk of the
       two views drifting apart. *)
  ; s_best : Tape.image ref
  ; s_best_value : 'a ref
  ; s_trail : Tape.image list ref
  ; s_attempts : int ref
  ; s_shrinks : int ref
  ; s_attempts_at_last_shrink : int ref
  ; s_max_stall : int ref
  ; s_seen : (Tape.image, unit) Hashtbl.t
  ; s_last_recorded : Tape.image option ref
        (* What the last SEQUENTIAL replay actually consumed, retained
           even when the proposal was uninteresting. A proposal that
           stops failing is useless as a candidate, but the number of
           choices it consumed is precisely the signal the length repair
           in [minimize_integer] needs: it sizes its deletion as given
           length minus consumed length instead of searching for it.

           Only the sequential path writes this, so the repair uses
           [attempt] and never [attempt_batch]: pooled proposals are
           evaluated in worker domains via [eval_proposal], which has no
           access to [st]. *)
  ; s_interesting : Tape_stats.verdict -> bool
        (* Which verdicts count as a candidate at all. Shrinking wants
           only [Case_failed] -- a proposal that stops failing is no
           use. A target search wants any VALID case, since it is
           maximising a score over passing inputs, not chasing a
           failure. *)
  ; s_accept : best:Tape.image -> Tape.image -> 'a -> bool
        (* The ONLY thing that differs between users of this machinery.
           Shrinking accepts a strictly shortlex-smaller image; a target
           search would accept an improved score; multi-bug would accept
           a still-failing image carrying the same origin. *)
  }

(* Consumed length of the SAME logical stream in a replayed image.

   [seg_get] addresses streams positionally, but [Tape.finish] emits
   them sorted by key and a replay may drop or re-key one, so index [s]
   in a recorded image need not be the stream that [s] named in [best].
   Subtracting their lengths would then compare two unrelated numbers
   and hand a confident, wrong deletion size to the caller.

   Segment 0 is safe by construction -- it is always [image.main]. For a
   child stream, match on the key and return [None] if it did not
   survive the replay: there is then no meaningful length to compare.

   Found by an independent review during a skeptic pass. The positional
   version was live on every multi-stream tape. *)
let consumed_in_same_stream (best : Tape.image) (rec_img : Tape.image) s =
  if s = 0 then Some (Array.length rec_img.Tape.main)
  else if s - 1 >= Array.length best.Tape.streams then None
  else begin
    let key = fst best.Tape.streams.(s - 1) in
    Array.find_map rec_img.Tape.streams ~f:(fun (k, arr) ->
      if Tape.compare_key k key = 0 then Some (Array.length arr) else None)
  end

let search_budget_ok (st : 'a search) =
  !(st.s_attempts) < st.s_budget
  && !(st.s_shrinks) < st.s_max_shrinks
  && !(st.s_attempts) - !(st.s_attempts_at_last_shrink) < !(st.s_max_stall)
  && (match st.s_deadline with
      | None -> true
      | Some d -> Float.( < ) (Unix.gettimeofday ()) d)

let search_note_shrink (st : 'a search) =
  Int.incr st.s_shrinks;
  Int.incr accepted_shrinks;
  st.s_max_stall
    := Int.max !(st.s_max_stall)
         ((!(st.s_attempts) - !(st.s_attempts_at_last_shrink)) * 2);
  st.s_attempts_at_last_shrink := !(st.s_attempts)

(* One replay under [policy]; count it, and return a candidate
   (image, value) iff it is still-failing, with whether it misaligned. *)
let search_candidate (type a) (st : a search) ~policy proposal =
  Tape.start_replay_image ~policy st.s_tape proposal;
  let value, tested, out =
    run_and_test ~tape:st.s_tape ~gen:st.s_gen ~size:st.s_size
      ~seed:replay_fresh_seed ~test:st.s_test
  in
  st.s_stats.replays <- st.s_stats.replays + 1;
  if out.Tape.misaligned then
    st.s_stats.misaligns <- st.s_stats.misaligns + 1;
  (* Record what was consumed BEFORE the interesting/overrun filtering
     below discards the image. An overrun replay wanted MORE than it was
     given and so carries no short-read signal; leave the field empty
     rather than reporting a length a caller would act on. *)
  st.s_last_recorded
    := (if out.Tape.overrun then None else Some out.Tape.image);
  match tested with
  | None -> (out.Tape.misaligned, None)
  | Some verdict ->
    st.s_stats.tests <- st.s_stats.tests + 1;
    (match verdict with
     | Tape_stats.Case_invalid ->
       st.s_stats.shrink_discards <- st.s_stats.shrink_discards + 1
     | Tape_stats.Case_passed | Tape_stats.Case_failed -> ());
    if out.Tape.overrun then (out.Tape.misaligned, None)
    else (
      if st.s_interesting verdict then
        (out.Tape.misaligned, Some (out.Tape.image, value))
      else (out.Tape.misaligned, None))

let search_attempt (type a) (st : a search) proposal =
  if not (search_budget_ok st) then false
  else if Option.is_some (Hashtbl.find st.s_seen proposal) then begin
    Int.incr duplicate_proposals;
    false
  end
  else begin
    Int.incr st.s_attempts;
    Hashtbl.set st.s_seen ~key:proposal ~data:();
    Int.incr distinct_proposals;
    let primary, secondary =
      match st.s_realign with
      | `Freeze -> (Tape.Freeze, Tape.Consume)
      | `Consume | `Both -> (Tape.Consume, Tape.Freeze)
    in
    let mis1, c1 = search_candidate st ~policy:primary proposal in
    let cands =
      match st.s_realign with
      | `Both when mis1 ->
        let _mis2, c2 = search_candidate st ~policy:secondary proposal in
        [ c1; c2 ]
      | _ -> [ c1 ]
    in
    let best_cand =
      List.filter_opt cands
      |> List.min_elt ~compare:(fun (a, _) (b, _) -> Tape.compare_image a b)
    in
    match best_cand with
    | Some (image, value) when st.s_accept ~best:!(st.s_best) image value ->
      st.s_best := image;
      st.s_best_value := value;
      st.s_trail := image :: !(st.s_trail);
      search_note_shrink st;
      true
    | _ -> false
  end

let shrink (type a) ~tape ~(gen : a Base_quickcheck.Generator.t) ~size
    ~(test : a -> bool) ~budget ~(max_seconds : float option)
    ~(max_shrinks : int) ~(max_stall : int option)
    ~(max_pass_failures : int option) ~domains ~pool
    ~(realign : realign) ~(stats : stats) ~(initial_tape : Tape.image)
    ~(initial_value : a) : a * int * Tape.image * Tape.image list * bool =
  let best = ref initial_tape in
  let best_value = ref initial_value in
  (* Every accepted image, oldest first once reversed at the end: cheap
     (an image is a compact recording, not a materialized value), and
     the secondary "intermediate examples" output the task write-up
     asks for if it is cheap. *)
  let trail = ref [] in
  let attempts = ref 0 in
  (* Hypothesis's actual accounting, ported rather than approximated.
     An earlier version of this engine charged every proposal against
     one flat [budget], which penalises a property equally for work that
     is paying off and work that is not. Hypothesis separates the two
     (hypothesis/internal/conjecture/{engine,shrinker}.py):

     - MAX_SHRINKS = 500 counts ACCEPTED improvements only
       (engine.py:45, incremented at engine.py:257 under
       [sort_key(new) < sort_key(old)]). Failed attempts never touch it.
     - max_stall = 200 (shrinker.py:292) bounds only the CURRENT dry
       spell: [calls - calls_at_last_shrink >= max_stall] stops
       shrinking (shrinker.py:414), and [calls_at_last_shrink] is reset
       on every success (shrinker.py:972). A success therefore refunds
       the stall allowance completely.
     - The stall allowance also ADAPTS upward on success
       (shrinker.py:969-971):
         max_stall = max(max_stall, (calls - calls_at_last_shrink) * 2)
       so a shrink that took 500 calls to find raises tolerance to 1000.
       Their comment: "whenever we shrink successfully we give ourselves
       a bit of breathing room to make sure we would find a shrink that
       took that long to find the next time."
     - A wall-clock deadline is the backstop for the steady-progress
       case (engine.py:903).

     [budget] is kept as a hard ceiling on total attempts so a
     pathological property cannot run forever even while succeeding.
     [max_seconds = None] disables the wall-clock side only.

     [max_stall] defaults to OFF, and that is a deliberate deviation
     from Hypothesis, measured rather than assumed. Porting it at
     Hypothesis's 200 destroyed shrink quality here: demo/shrink_table
     went from 100/100 fully-minimal to 1/100 on "int list, fail iff
     length >= 3" and 26/100 on "sum >= 100". The cause is that this
     port omitted the fourth of Hypothesis's four mechanisms, the floor
     at shrinker.py:705-708 that widens max_stall enough to complete one
     whole iteration of fixate_shrink_passes -- whose comment predicts
     exactly this: "if we're unlucky and the shrink passes are in a bad
     order where only the ones at the end are useful, if we're not
     careful this heuristic might stop us before we've tried
     everything."

     But porting that floor turns out not to be worth it either, for a
     structural reason. Hypothesis needs max_stall because one of its
     passes can burn unbounded calls; this engine's outer loop is
       while !continue_ && budget_ok () do ...; continue_ := improved done
     which already halts on the first fully unproductive sweep, and its
     passes are individually bounded by segment counts. A sweep-granular
     stall is therefore inert, and a finer-grained one needs per-pass
     metering that does not exist yet. Making passes first class is the
     real prerequisite -- and it is the same prerequisite as
     Hypothesis's productivity-based pass reordering (shrinker.py:742),
     which is the mechanism that would actually address repeated,
     unproductive proposals measured in the tape arm of
     head_to_head/VERIFICATION.md.  Its proposal count is not a ratio
     against qcheck-stm's accepted-step count; those are different units.

     So: [max_shrinks] is ported and on, [max_stall] is available but
     off, and the cost work is deferred to a change that makes passes
     first class. See SHRINK-BUDGET-DESIGN.md. *)
  let deadline =
    Option.map max_seconds ~f:(fun s -> Unix.gettimeofday () +. s)
  in
  Array.fill pass_costs ~pos:0 ~len:(Array.length pass_costs) 0;
  duplicate_proposals := 0;
  distinct_proposals := 0;
  greedy_cost := 0;
  accepted_shrinks := 0;
  sweeps := 0;
  scan_i_visits := 0;
  scan_jk_visits := 0;
  lad_successes := 0;
  cr_probes := 0;
  cr_hits := 0;
  final_choices := 0;
  initial_choices :=
    Array.length initial_tape.Tape.main
    + Array.fold initial_tape.Tape.streams ~init:0 ~f:(fun a (_, c) ->
        a + Array.length c);
  let seen_proposals = Hashtbl.Poly.create () in
  let shrinks = ref 0 in
  let attempts_at_last_shrink = ref 0 in
  let last_recorded = ref None in
  let max_stall = ref (Option.value max_stall ~default:Int.max_value) in
  (* Build the shared search state over the SAME ref cells this
     function's passes already use, then alias the proposal machinery to
     it. Nothing below changes: [budget_ok] and [attempt] keep their
     names and signatures. See the [search] type for why this exists --
     target() and multi-bug reporting were both blocked on the proposal
     machinery being trapped inside this function. *)
  let st =
    { s_gen = gen
    ; s_size = size
    ; s_test = test
    ; s_tape = tape
    ; s_realign = realign
    ; s_stats = stats
    ; s_pool = pool
    ; s_domains = domains
    ; s_budget = budget
    ; s_max_shrinks = max_shrinks
    ; s_deadline = deadline
    ; s_best = best
    ; s_best_value = best_value
    ; s_trail = trail
    ; s_attempts = attempts
    ; s_shrinks = shrinks
    ; s_attempts_at_last_shrink = attempts_at_last_shrink
    ; s_max_stall = max_stall
    ; s_seen = seen_proposals
    ; s_last_recorded = last_recorded
    ; (* Shrinking: only a still-failing proposal is a candidate, and it
         is accepted only if strictly shortlex-smaller. *)
      s_interesting =
        (function
        | Tape_stats.Case_failed -> true
        | Tape_stats.Case_passed | Tape_stats.Case_invalid -> false)
    ; s_accept = (fun ~best image _value -> Tape.compare_image image best < 0)
    }
  in
  let budget_ok () = search_budget_ok st in
  let note_shrink () = search_note_shrink st in
  let candidate ~policy proposal = search_candidate st ~policy proposal in
  let attempt proposal = search_attempt st proposal in
  ignore (note_shrink : unit -> unit);
  ignore (candidate : policy:Tape.policy -> Tape.image -> bool * (Tape.image * a) option);

  (* Evaluate several independent proposals (in parallel domains when a
     pool exists) and accept the LOWEST-INDEX improvement, exactly the
     proposal the sequential first-accept scan would have taken, so
     accepted-edit sequences are identical at every ?domains. Returns
     the accepted proposal's index, if any. With a pool the whole batch
     is evaluated speculatively, so attempt counts (not results) may
     exceed the sequential engine's. *)
  let attempt_batch proposals =
    let proposals =
      List.take proposals (max 1 (min 64 (budget - !attempts)))
    in
    match (proposals, pool) with
    | [], _ -> None
    | [ p ], _ -> if attempt p then Some 0 else None
    | ps, None ->
      List.foldi ps ~init:None ~f:(fun i acc p ->
        match acc with
        | Some _ -> acc
        | None -> if attempt p then Some i else None)
    | ps, Some pool ->
      (* Deduplicated too, now. My earlier note here said filtering
         "would have to happen at build time" and left it -- which was
         true and not an obstacle: the proposals are all known before
         dispatch. The only real constraint is that the caller uses the
         returned position as an offset, so the mapping back to ORIGINAL
         indices has to survive the filter. *)
      let kept =
        List.filter_mapi ps ~f:(fun i p ->
          if Hashtbl.mem seen_proposals p then begin
            Int.incr duplicate_proposals;
            None
          end
          else begin
            Hashtbl.set seen_proposals ~key:p ~data:();
            Int.incr distinct_proposals;
            Some (i, p)
          end)
      in
      if List.is_empty kept then None
      else begin
        let results =
          Pool.run_batch pool
            (List.map kept ~f:(fun (_, p) () ->
                 (eval_proposal ~gen ~size ~test ~realign p, None)))
        in
        attempts := !attempts + List.length kept;
        (* Workers report what their replays did as data -- they cannot
           touch [stats] without racing, see [pool_payload] -- and the
           fold happens here so pooled evaluations count exactly as the
           sequential [search_candidate] path counts them (tapecheck#6). *)
        List.iter results ~f:(fun ((_, e), _) ->
          stats.replays <- stats.replays + e.e_replays;
          stats.tests <- stats.tests + e.e_tests;
          stats.misaligns <- stats.misaligns + e.e_misaligns;
          stats.shrink_discards <- stats.shrink_discards + e.e_discards);
        let accepted =
          List.foldi results ~init:None ~f:(fun i acc r ->
            match (acc, r) with
            | Some _, _ | _, ((None, _), _) -> acc
            | None, ((Some (image, value), _), _) ->
              if Tape.compare_image image !best < 0 then
                (* Map back to the position in the ORIGINAL batch. *)
                Some (fst (List.nth_exn kept i), image, value)
              else None)
        in
        match accepted with
        | Some (i, image, value) ->
          best := image;
          best_value := value;
          trail := image :: !trail;
          note_shrink ();
          Some i
        | None -> None
      end
  in

  (* Port of Hypothesis's [lower_blocks_together] (shrinker.py:1258),
     the defence against the ZIG-ZAG TRAP: two values that must keep a
     fixed difference to stay failing. Lowering either one ALONE always
     works by exactly one step and never more, so a shrinker without
     this pass walks them down in lockstep, O(value) attempts instead of
     O(log value).

     Measured before this pass existed, on "fails iff |m - n| = 1" over
     [0,300]: 2929 attempts and only 51/100 fully minimal, because the
     lockstep descent exhausted the budget. With it: 37 attempts, and
     every case found reaches the true minimum. Hypothesis considers the
     trap important enough to assert a quantitative bound on it
     (tests/quality/test_zig_zagging.py).

     Lower BOTH choices by the same k and let [find_integer] find the
     largest workable k. Because the difference is preserved, one
     galloping search covers the whole distance. Lookahead is bounded at
     8 following their comment: far enough to be useful, near enough to
     avoid quadratic cost. m and n are read once and all attempts are
     relative to those originals, exactly as they capture [buffer] up
     front; a larger k is strictly better, so committing along the way
     is safe. *)
  (* PROTOTYPE: a span-free approximation of Hypothesis's [reorder_spans].

     Theirs sorts the children of a span that share a LABEL, using
     [sort_key] -- shortlex over the choice sequence. That gives
     normalisation: their docstring's example is two [st.text()] draws
     with [x <> y], which without reordering fails as either ("", "0")
     or ("0", ""), and with it reliably as ("", "0").

     We have neither spans nor labels. The stand-in is the one
     [correlate_image] already uses for single choices, lifted to
     subsequences: two windows with the same SIGNATURE -- the same
     sequence of (kind, lo, hi) -- were plausibly drawn by the same
     generator at comparable positions. Group the windows by signature,
     take a non-overlapping subset, and propose them sorted by the
     existing shortlex order.

     One proposal per (window length, signature) group, not per pair, so
     a group of k siblings costs one attempt rather than k^2 swaps.

     Guessing structure from bounds is exactly that -- a guess. Two
     unrelated draws that happen to share bounds will be reordered
     against each other. That cannot produce a wrong ANSWER, because
     every proposal is still validated by re-running the test and
     re-recording, but it can waste attempts, which is what
     [max_pass_failures] is there to contain. *)
  let signature arr i k =
    let b = Buffer.create (k * 8) in
    for j = i to i + k - 1 do
      match arr.(j) with
      | Tape.Integer { lo; hi; _ } ->
        Buffer.add_string b (Printf.sprintf "I%Ld,%Ld;" lo hi)
      | Tape.Float { lo; hi; _ } ->
        Buffer.add_string b (Printf.sprintf "F%h,%h;" lo hi)
      | Tape.Bool _ -> Buffer.add_string b "B;"
      | Tape.Marker -> Buffer.add_string b "M;"
    done;
    Buffer.contents b
  in
  let max_window = 8 in
  let sort_siblings () =
    let improved = ref false in
    (* Its own consecutive-failure cutoff, same constant as the other
       passes. Without one this can propose up to max_window groups per
       position on a long tape, and a pass that scores nothing while
       spending the budget is precisely the failure mode the cutoff
       exists to contain. *)
    let failures = ref 0 in
    let live () =
      match max_pass_failures with
      | None -> true
      | Some n -> !failures < n
    in
    let s = ref 0 in
    while !s < seg_count !best && budget_ok () && live () do
      let k = ref 1 in
      while !k <= max_window && budget_ok () && live () do
        let arr = seg_get !best !s in
        let n = Array.length arr in
        let groups = Hashtbl.create (module String) in
        let i = ref 0 in
        while !i + !k <= n do
          Hashtbl.add_multi groups ~key:(signature arr !i !k) ~data:!i;
          Int.incr i
        done;
        Hashtbl.iteri groups ~f:(fun ~key:_ ~data:positions ->
          if budget_ok () && live () then begin
            (* [add_multi] prepends, so restore ascending order, then
               keep a greedy non-overlapping subset. *)
            let ascending = List.rev positions in
            let chosen = ref [] and last_end = ref (-1) in
            List.iter ascending ~f:(fun p ->
              if p > !last_end then begin
                chosen := p :: !chosen;
                last_end := p + !k - 1
              end);
            let chosen = List.rev !chosen in
            if List.length chosen >= 2 then begin
              let contents =
                List.map chosen ~f:(fun p -> Array.sub arr ~pos:p ~len:!k)
              in
              let sorted =
                List.sort contents ~compare:Tape.compare_shortlex
              in
              let already_sorted =
                List.for_all2_exn contents sorted ~f:(fun a b ->
                  Tape.compare_shortlex a b = 0)
              in
              if not already_sorted then begin
                let a = Array.copy arr in
                List.iter2_exn chosen sorted ~f:(fun p c ->
                  Array.blit ~src:c ~src_pos:0 ~dst:a ~dst_pos:p ~len:!k);
                if attempt (seg_set !best !s a) then begin
                  improved := true;
                  failures := 0
                end
                else Int.incr failures
              end
            end
          end);
        Int.incr k
      done;
      Int.incr s
    done;
    !improved
  in

  let lower_together () =
    let improved = ref false in
    let s = ref 0 in
    while !s < seg_count !best && budget_ok () do
      let i = ref 0 in
      while !i < Array.length (seg_get !best !s) && budget_ok () do
        (match (seg_get !best !s).(!i) with
         | Tape.Integer { value = m; lo = lo1; hi = hi1 }
           when Int64.(m > clamp64 0L ~lo:lo1 ~hi:hi1) ->
           let t1 = clamp64 0L ~lo:lo1 ~hi:hi1 in
           let arr0 = seg_get !best !s in
           let stop = Int.min (Array.length arr0) (!i + 9) in
           let j = ref (!i + 1) in
           while !j < stop && budget_ok () do
             (match arr0.(!j) with
              | Tape.Integer { value = n; lo = lo2; hi = hi2 }
                when Int64.(n > clamp64 0L ~lo:lo2 ~hi:hi2) ->
                let t2 = clamp64 0L ~lo:lo2 ~hi:hi2 in
                let try_k k =
                  if Int64.(k > m - t1) || Int64.(k > n - t2) then false
                  else begin
                    let arr = seg_get !best !s in
                    if
                      !i < Array.length arr
                      && !j < Array.length arr
                      && budget_ok ()
                    then begin
                      let a =
                        with_choice arr !i
                          (Tape.Integer
                             { value = Int64.( - ) m k; lo = lo1; hi = hi1 })
                      in
                      let a =
                        with_choice a !j
                          (Tape.Integer
                             { value = Int64.( - ) n k; lo = lo2; hi = hi2 })
                      in
                      attempt (seg_set !best !s a)
                    end
                    else false
                  end
                in
                if Int64.( > ) (find_integer try_k) 0L then improved := true
              | _ -> ());
             Int.incr j
           done
         | _ -> ());
        Int.incr i
      done;
      Int.incr s
    done;
    !improved
  in

  (* Pass 1: everything to target at once, across all streams. *)
  let trivial = image_trivialized !best in
  if Tape.compare_image trivial !best < 0 then
    ignore (attempt trivial : bool);

  (* Lower an integer choice by one while deleting one later choice in
     the same stream: what shrinks length-prefixed data (bind), where
     neither edit works alone. *)
  let lower_and_delete () =
    let improved = ref false in
    (* Per-pass consecutive-failure cutoff, Hypothesis's max_failures =
       20 (shrinker.py, the [while failures < max_failures] loop inside
       fixate_shrink_passes; their note: "this implicitly boosts shrink
       passes that are more likely to work").

       Measured justification: on both list properties this pass scores
       ZERO successes while spending 612 and 427 attempts, 96% of the
       whole shrink. On bind it succeeds on its 3rd (j,k) visit, so a
       20-failure cutoff never fires there. See
       ../tapecheck-hypothesis-baseline/README.md.

       [live] is checked alongside budget_ok in this pass's loops.
       Truncation is recorded, because a pass cut short cannot support a
       claim of convergence. *)
    let consecutive_failures = ref 0 in
    (* A FLAT count, deliberately, after trying to make it proportional
       to tape length and measuring the result.

       The motivation was real: lengthlist from the Shrinking Challenge
       sat at 64/100 because a budget of 20 is a very different fraction
       of a 200-choice tape than of a 20-choice one, and every miss
       stopped with converged=false and the global budget untouched.
       A floor of max(n, len/3) took it to 50/50 at HALF the cost, left
       the other nine guarded properties untouched, and looked like a
       free win.

       It is not. test_poison's base-tree construction regressed badly
       under it: the size-2 base tree stopped shrinking at 50 leaves
       instead of 2, turning 34 testable positions into 130. The reason
       is that the floor grants long-tape patience to UNPRODUCTIVE
       passes as well as useful ones, which is precisely what the flat
       cutoff exists to prevent -- lower_and_delete scoring zero
       successes while consuming 96% of the shrink. Per-pass persistence
       is paid for out of the global budget.

       No divisor satisfies both. Measured at 3, 4, 6, 8: at 3 the floor
       binds and poison breaks; at 4 and above it never binds on
       lengthlist's tapes and nothing changes. There is no window.

       The right fix is to make patience EARNED rather than granted --
       scale a pass's allowance by its own success rate in this shrink,
       which is the spirit of Hypothesis's fixate_shrink_passes -- and
       that is a design change rather than a constant. Recorded here so
       the proportional version is not re-attempted from scratch;
       lengthlist stays a known frontier in the regression guard. *)
    (* EARNED patience: the allowance is the flat base PLUS one extra
       failure per success this pass has already banked in this shrink.

       This is not the adaptation the guard warns against. That one grew
       the budget WITHIN a single invocation, so a pass whose budget was
       too small to reach its first success could never grow. Here the
       credit is carried ACROSS sweeps: lower_and_delete succeeds freely
       early on (deleting and lowering elements), so by the time it
       faces a move that needs many tries -- lengthlist's length
       reduction -- it has banked enough to keep going.

       And it stays zero exactly where the flat cutoff earns its keep:
       on the list properties this pass scores NO successes while
       consuming 96% of the shrink, so it banks nothing and is cut at
       the base as before. That is the difference from the
       tape-proportional floor, which handed the same patience to
       productive and unproductive passes alike and broke test_poison. *)
    let live () =
      match max_pass_failures with
      | None -> true
      | Some n -> !consecutive_failures < n + !lad_successes
    in
    let s = ref 0 in
    while !s < seg_count !best && budget_ok () && live () do
      let i = ref 0 in
      while !i < Array.length (seg_get !best !s) && budget_ok () && live () do
        let arr = seg_get !best !s in
        Int.incr scan_i_visits;
        (match arr.(!i) with
        | Tape.Integer { value; lo; hi }
          when Int64.(value <> clamp64 0L ~lo ~hi) ->
          (* Step one toward the target from EITHER side: length-like
             choices usually sit above it, but nothing guarantees that. *)
          let step =
            if Int64.(value > clamp64 0L ~lo ~hi) then Int64.( - ) value 1L
            else Int64.( + ) value 1L
          in
          let lowered = Tape.Integer { value = step; lo; hi } in
          (* Try deleting a contiguous block of k later choices with the
             lowered prefix; one list element can span several choices
             (e.g. base_quickcheck's list machinery draws a shuffle
             position and a value draw per element), so k ranges over
             small block sizes. Deletable choices cluster early (the
             redistribute pass piles zeros there), so walk j upward, and
             after an accepted deletion stay at the same position: the
             next deletable block usually sits exactly there. *)
          (* COMPUTED DELETION, tried before the j/k search below.

             Same move as the length repair in minimize_integer, but at
             lower_and_delete's existing position in the sweep, because
             the measured blocker for lengthlist was pass ORDER:
             hoisting the lowering earlier closes lengthlist and costs
             test_poison 10/34 -> 6/34 (LENGTH-REPAIR.md).

             This deliberately does NOT accept a bare lowering -- that
             is exactly what damaged poison. It PROBES one to learn how
             many choices the replay consumed, then attempts only the
             repaired proposal. One probe plus one attempt replaces a
             j/k search costing up to 4n. The probe is charged to
             [attempts]: it runs the generator and the test like any
             other evaluation.

             Repeated greedily, which is not optional. Without the loop
             each success restarts the whole scan at [i := 0] -- the
             search path has always had its own greedy repeat -- and the
             measured cost of leaving it out was bind 52 -> 80 calls and
             deep bind 141 -> 256. *)
          let computed_repair () =
            let arr = seg_get !best !s in
            if !i >= Array.length arr then false
            else
              match arr.(!i) with
              | Tape.Integer { value; lo; hi }
                when Int64.(value <> clamp64 0L ~lo ~hi) ->
                let target = clamp64 0L ~lo ~hi in
                let step =
                  if Int64.(value > target) then Int64.( - ) value 1L
                  else Int64.( + ) value 1L
                in
                let lowered = Tape.Integer { value = step; lo; hi } in
                let lowered_only =
                  seg_set !best !s (with_choice arr !i lowered)
                in
(* The seg_count = 1 restriction that used to sit here is
                   GONE, and was a quarantine rather than a fix. It was
                   added because allowing the repair on tapes with
                   sub-streams took test_fn_shrink's orphan property
                   from 0/1000 stuck to 19/1000 (McNemar p < 0.0001),
                   and the explanation offered was that the per-stream
                   length arithmetic breaks when siblings re-key.

                   That explanation was wrong. On the orphan property
                   the root tape is [Integer x; Marker], so lowering x
                   shortens nothing, L = 0, and no computed deletion is
                   ever attempted there. The damage was the line below
                   that used to insert [lowered_only] into
                   [seen_proposals]: the probe discards its candidate,
                   so marking the proposal seen suppressed the SAME
                   proposal when minimize_integer later offered it for
                   real -- and on this property that proposal is x = 0,
                   the winning shrink.

                   Not poisoning the table fixes it with no restriction
                   at all (orphan 0/1000) and additionally takes
                   lengthlist from 994/1000 to 1000/1000, because the
                   same suppression was costing shrinks there too. *)
                if Hashtbl.mem seen_proposals lowered_only then false
                else if not (!cr_hits > 0 || !cr_probes < cr_probe_budget) then
                  false
                else begin
                  Int.incr cr_probes;
                  Int.incr attempts;
                  (* Deliberately NOT recorded in seen_proposals. The
                     probe throws its candidate away, so marking the
                     proposal seen would suppress the SAME proposal when
                     minimize_integer later offers it for real. *)
                  last_recorded := None;
                  ignore
                    (candidate ~policy:Tape.Consume lowered_only
                      : bool * (Tape.image * a) option);
                  match
                    Option.bind !last_recorded ~f:(fun rec_img ->
                      consumed_in_same_stream !best rec_img !s)
                  with
                  | Some consumed ->
                    let l = Array.length arr - consumed in
                    if l > 0 && !i + 1 + l <= Array.length arr then begin
                      let ok =
                        attempt
                          (seg_set !best !s
                             (with_deleted_block
                                (with_choice arr !i lowered)
                                ~pos:(!i + 1) ~len:l))
                      in
                      if ok then Int.incr cr_hits;
                      ok
                    end
                    else false
                  | _ -> false
                end
              | _ -> false
          in
          (* No special-cased first attempt here. An earlier version
             tried one explicitly -- lower a step, delete the single
             choice at i+1 -- and it took lengthlist from 719/1000 to
             987/1000. That proposal is IDENTICAL to the k/j search's
             first candidate, so it should have changed nothing, and
             chasing why exposed the real defect: it was banking a
             patience credit per accepted edit where the greedy repeat
             below banked one per run. The credit is now incremented
             where it belongs (see the greedy repeat), which reproduces
             that result exactly -- 987/1000 and 150.5 calls, matching
             to the decimal on all five benchmark properties -- without
             a redundant attempt whose effect was accidental.

             The single cheap attempt IS kept, but on its real merit and
             not the one first claimed for it: it accepts the common
             deletion in ONE evaluation where the probe below needs two
             (a probe plus the repair). Measured with the credit fix
             already in place, dropping it costs lengthlist 994 -> 990
             and 84.1 -> 126.6 calls. So it is a cost optimisation for
             the common shape, exactly as the probe is a cost
             optimisation for the far/large shape. Neither is what buys
             the quality; the credit does. *)
          let accepted = ref false in
          if !i + 1 <= Array.length arr - 1 then
            if
              attempt
                (seg_set !best !s
                   (with_deleted_block
                      (with_choice arr !i lowered)
                      ~pos:(!i + 1) ~len:1))
            then begin
              Int.incr lad_successes;
              consecutive_failures := 0;
              accepted := true;
              improved := true
            end;
          let again = ref (not !accepted) in
          while !again && budget_ok () && live () do
            again := computed_repair ();
            if !again then begin
              accepted := true;
              Int.incr lad_successes;
              Int.incr length_repair_hits;
              consecutive_failures := 0;
              improved := true
            end
          done;
          let k = ref 1 in
          while (not !accepted) && !k <= 4 && budget_ok () && live () do
            let j = ref (!i + 1) in
            while
              (not !accepted)
              && !j <= Array.length (seg_get !best !s) - !k
              && budget_ok ()
              && live ()
            do
              let arr = seg_get !best !s in
              Int.incr scan_jk_visits;
              let batch =
                List.filter_map
                  (List.init (max 1 (domains * 4)) ~f:(fun d -> !j + d))
                  ~f:(fun j ->
                    if j <= Array.length arr - !k then
                      Some
                        (seg_set !best !s
                           (with_deleted_block
                              (with_choice arr !i lowered)
                              ~pos:j ~len:!k))
                    else None)
              in
              (match attempt_batch batch with
              | Some offset ->
                Int.incr lad_successes;
                consecutive_failures := 0;
                accepted := true;
                improved := true;
                (* Greedily repeat the same edit shape at the position
                   that actually succeeded (the batch may have accepted
                   a later candidate than !j). *)
                let jj = !j + offset in
                let greedy_start = !attempts in
                let again = ref true in
                while !again && budget_ok () do
                  let arr = seg_get !best !s in
                  match
                    (if !i < Array.length arr then Some arr.(!i) else None)
                  with
                  | Some (Tape.Integer { value; lo; hi })
                    when Int64.(value <> clamp64 0L ~lo ~hi)
                         && jj <= Array.length arr - !k ->
                    let step =
                      if Int64.(value > clamp64 0L ~lo ~hi) then
                        Int64.( - ) value 1L
                      else Int64.( + ) value 1L
                    in
                    let lowered = Tape.Integer { value = step; lo; hi } in
                    again :=
                      attempt
                        (seg_set !best !s
                           (with_deleted_block
                              (with_choice arr !i lowered)
                              ~pos:jj ~len:!k));
                    (* Each greedy repeat is a separate accepted shrink
                       and banks its own patience credit. Without this a
                       run of N deletions at one position earned ONE
                       credit, and [live ()] is
                         consecutive_failures < max_pass_failures
                                                + lad_successes
                       so the pass was starved of patience in precisely
                       the situation where it was being most productive.
                       Worth 719/1000 -> 987/1000 fully-minimal on
                       lengthlist, n=1000 paired, McNemar p = 4.2e-81,
                       and it costs one increment. *)
                    if !again then Int.incr lad_successes
                  | _ -> again := false
                done;
                greedy_cost := !greedy_cost + (!attempts - greedy_start)
              | None ->
                Int.incr consecutive_failures;
                j := !j + max 1 (domains * 4))
            done;
            Int.incr k
          done;
          (* Fallback, not a first move. On ordinary shapes the deletable
             block sits at j = i+1 and the search above finds it in ONE
             attempt, so probing first cost two evaluations where one
             sufficed -- measured as bind 52 -> 80 calls and deep bind
             141 -> 256. The computed repair earns its place only where
             that search FAILS: a deletion further away than the scan
             reaches, or larger than the k <= 4 cap can express, which is
             exactly lengthlist's shape. *)
          if !accepted then i := 0 else Int.incr i
        | _ -> Int.incr i);
        (* An acceptance may change the stream layout; keep s valid. *)
        if !s >= seg_count !best then s := seg_count !best
      done;
      Int.incr s
    done;
    !improved
  in

  (* Move weight from an earlier integer choice to the next integer
     after it in the same stream, preserving their sum: [27, 23]
     becomes [0, 50], after which lower-and-delete can drop the zero.
     This is what turns minimal-sum-many-elements local optima into
     single elements. *)
  let redistribute_pairs () =
    let improved = ref false in
    let s = ref 0 in
    while !s < seg_count !best && budget_ok () do
      let i = ref 0 in
      while !i < Array.length (seg_get !best !s) && budget_ok () do
        let arr = seg_get !best !s in
        Int.incr scan_i_visits;
        (match arr.(!i) with
        | Tape.Integer { value = vi; lo = lo_i; hi = hi_i }
          when Int64.(vi <> clamp64 0L ~lo:lo_i ~hi:hi_i) -> (
          (* find the next integer choice after i *)
          let j = ref (!i + 1) in
          while
            !j < Array.length arr
            && not (match arr.(!j) with
                    | Tape.Integer _ -> true
                    | _ -> false)
          do
            Int.incr j
          done;
          if !j >= Array.length arr then Int.incr i
          else
            match arr.(!j) with
            | Tape.Integer { value = vj; lo = lo_j; hi = hi_j } ->
              let target_i = clamp64 0L ~lo:lo_i ~hi:hi_i in
              (* Move choice i toward its target and choice j the other
                 way, preserving their sum, in whichever direction i
                 needs (Hypothesis's redistribute originally handled
                 only the above-target side; both sides matter). *)
              let above = Int64.(vi > target_i) in
              let d_max =
                if above then
                  Int64.min (Int64.( - ) vi target_i) (Int64.( - ) hi_j vj)
                else Int64.min (Int64.( - ) target_i vi) (Int64.( - ) vj lo_j)
              in
              let d = ref d_max in
              let accepted = ref false in
              while (not !accepted) && Int64.(!d > 0L) && budget_ok () do
                let new_i =
                  if above then Int64.( - ) vi !d else Int64.( + ) vi !d
                in
                let new_j =
                  if above then Int64.( + ) vj !d else Int64.( - ) vj !d
                in
                let proposal =
                  seg_set !best !s
                    (with_choice
                       (with_choice arr !i
                          (Tape.Integer { value = new_i; lo = lo_i; hi = hi_i }))
                       !j
                       (Tape.Integer { value = new_j; lo = lo_j; hi = hi_j }))
                in
                if attempt proposal then begin
                  accepted := true;
                  improved := true
                end
                else d := Int64.( / ) !d 2L
              done;
              if !accepted then i := 0 else Int.incr i
            | _ -> Int.incr i)
        | _ -> Int.incr i);
        if !s >= seg_count !best then s := seg_count !best
      done;
      Int.incr s
    done;
    !improved
  in

  (* Minimize one integer choice toward its target by bisection on
     the DISTANCE from the target, from whichever side the value sits.
     Distances are unsigned int64 (wrapped subtraction is exact modulo
     2^64), so full-range spans like [min_int, max_int] cannot
     overflow. *)
  let minimize_integer s i value lo hi =
    let target = clamp64 0L ~lo ~hi in
    (* LENGTH REPAIR, folded into the lowering attempt. This is
       Hypothesis's try_shrinking_nodes (shrinker.py:1146): lower the
       choice at [i] to [v]; if the replay is not interesting but
       consumed L FEWER choices than it was handed, retry with exactly
       those L choices deleted immediately after [i]. The deletion size
       is COMPUTED, never searched, which is what lower_and_delete
       cannot do -- that pass steps the value down by one and hunts for
       a block of at most 4 to drop.

       An ablation of Hypothesis over seeds 0..99 put the weight here:
       with minimize_individual_choices (this move's only caller)
       disabled it solves lengthlist 14/100, and with just this retry
       removed 51/100, the failures all shaped [0,...,0,900] -- elements
       zeroed, length never coming down. With reorder_spans,
       pass_to_descendant, minimize_duplicated_choices,
       lower_integers_together and reduce_each_alternative ALL disabled
       it still scores 100/100 at 90.6 evaluations against 87.2 stock.
       Spans are not load-bearing for this problem.

       IT IS CURRENTLY INERT HERE, AND THE REASON IS PASS ORDER, NOT THE
       MOVE. [minimize_integer] skips a choice already at its target,
       and by the time the sweep reaches minimize_choices,
       lower_and_delete has ground the length prefix down one step at a
       time. Measured: this fires ONCE across 100 lengthlist trials, and
       lengthlist is unmoved at 74/100 against a 73/100 baseline.

       Hoisting the lowering earlier DOES close lengthlist -- 100/100 at
       135 calls against 256 -- and costs test_poison, which drops from
       10/34 to 6/34. That drop is not caused by this repair: with the
       repair switched off and only the order changed, poison is the
       same 6/34 while lengthlist collapses to 7/100. A dedicated
       integers-only pass in the same early slot measured identically,
       and a variant that probes without accepting bare lowerings was
       worse on every axis (76/100, 373 calls, and the poison base tree
       drifted from 34 positions to 36). So the mechanism is kept and
       correct, the reordering is not shipped, and lengthlist stays a
       recorded frontier. See LENGTH-REPAIR.md for the full 2x2.

       Right-truncation is already free and is not what this adds: an
       accepted candidate is [out.Tape.image], what the replay actually
       consumed, so surplus trailing choices vanish by construction.
       What this adds is deletion from the FRONT of the element region,
       which is what walks a late failing element leftward. *)
    let try_value v =
      let arr = seg_get !best s in
      if i >= Array.length arr then false
      else begin
        let lowered =
          with_choice arr i (Tape.Integer { value = v; lo; hi })
        in
        (* Clear FIRST. [attempt] returns false both for "replayed, not
           interesting" and for "already seen, never replayed", and only
           the former leaves a consumed length describing THIS proposal.
           Reading the field without clearing it would size the deletion
           from whatever unrelated replay happened to run last. *)
        last_recorded := None;
        if attempt (seg_set !best s lowered) then true
        else
          match
            Option.bind !last_recorded ~f:(fun rec_img ->
              consumed_in_same_stream !best rec_img s)
          with
          | None -> false
          | Some consumed ->
            begin
              let l = Array.length lowered - consumed in
              if l > 0 && i + 1 + l <= Array.length lowered then begin
                Int.incr length_repair_tries;
                let ok =
                  attempt
                    (seg_set !best s
                       (with_deleted_block lowered ~pos:(i + 1) ~len:l))
                in
                if ok then Int.incr length_repair_hits;
                ok
              end
              else false
            end
      end
    in
    if Int64.(value <> target) && not (try_value target) then begin
      let above = Int64.(value > target) in
      let dist =
        if above then Int64.( - ) value target else Int64.( - ) target value
      in
      let of_dist d =
        if above then Int64.( + ) target d else Int64.( - ) target d
      in
      let low = ref 0L and high = ref dist in
      while
        Stdlib.Int64.unsigned_compare (Int64.( - ) !high !low) 1L > 0
        && budget_ok ()
      do
        let mid =
          Int64.( + ) !low
            (Stdlib.Int64.shift_right_logical (Int64.( - ) !high !low) 1)
        in
        if try_value (of_dist mid) then high := mid else low := mid
      done
    end
  in

  let minimize_float s i value lo hi =
    let target = clampf 0. ~lo ~hi in
    let try_value v =
      attempt
        (seg_set !best s
           (with_choice (seg_get !best s) i (Tape.Float { value = v; lo; hi })))
    in
    if Float.( <> ) value target && not (try_value target) then begin
      (* Prefer round values, then bisect a bounded number of steps. *)
      let rounded = Float.round_down value in
      if Float.( <> ) rounded value then ignore (try_value rounded : bool);
      let low = ref target and high = ref value in
      let steps = ref 0 in
      while !steps < 40 && budget_ok () do
        Int.incr steps;
        let mid = !low +. ((!high -. !low) /. 2.) in
        if Float.( = ) mid !low || Float.( = ) mid !high then steps := 40
        else if try_value mid then high := mid
        else low := mid
      done;
      (* One more integer-snap attempt near the found boundary. *)
      let snap = Float.round_up !high in
      if Float.( <> ) snap !high then ignore (try_value snap : bool)
    end
  in

  let minimize_choices () =
    let improved_any = ref false in
    let s = ref 0 in
    while !s < seg_count !best && budget_ok () do
      let i = ref 0 in
      while !i < Array.length (seg_get !best !s) && budget_ok () do
        let before = !best in
        (match (seg_get !best !s).(!i) with
        | Tape.Integer { value; lo; hi } -> minimize_integer !s !i value lo hi
        | Tape.Float { value; lo; hi } -> minimize_float !s !i value lo hi
        | Tape.Bool true ->
          ignore
            (attempt
               (seg_set !best !s
                  (with_choice (seg_get !best !s) !i (Tape.Bool false)))
              : bool)
        | Tape.Bool false | Tape.Marker -> ());
        if not (phys_equal before !best) then improved_any := true;
        if !s >= seg_count !best then s := seg_count !best else Int.incr i
      done;
      Int.incr s
    done;
    !improved_any
  in

  let continue_ = ref true in
  pass_costs.(4) <- !attempts;
  while !continue_ && budget_ok () do
    Int.incr sweeps;
    let a0 = !attempts in
    let improved = lower_and_delete () in
    pass_costs.(0) <- pass_costs.(0) + (!attempts - a0);
    let a2 = !attempts in
    let improved = redistribute_pairs () || improved in
    pass_costs.(2) <- pass_costs.(2) + (!attempts - a2);
    let a3 = !attempts in
    let improved = minimize_choices () || improved in
    pass_costs.(3) <- pass_costs.(3) + (!attempts - a3);
    let improved = lower_together () || improved in
    (* OFF by default. See SORT-SIBLINGS.md.

       RE-MEASURED 2026-08-09 at n=1000 on both arms, because the
       original justification was taken at n=100 and half of it turned
       out to be noise. Exact scores per 1000 runs:

                        stock off  stock on  +patch off  +patch on
         distinct               0         0         116        649
         reverse                0         0         452        487
         binheap               93       110          93        110
         bound5               158       159          52          0
         calculator            16        12          14         14
         large_union_list  1338.8    1671.1      1306.2     1560.9   (evals)

       What held up: the large_union_list cost penalty (~25%, for no
       gain in either arm), and the big distinct win once the patch
       equalises sibling draw counts.

       What did NOT hold up, and was the stated reason for keeping this
       off: bound5 was recorded as 12.5% against 15.9% on stock. At
       n=1000 both arms are 15.8-15.9% -- the pass does nothing there.
       The original note admits its intervals overlapped; it should not
       have been load-bearing.

       Two effects the original missed: binheap gains 93 -> 110 on stock
       (299 -> 327 at-or-below optimal size), and bound5 collapses
       52 -> 0 on the patched arm.

       So the honest summary is a trade in BOTH arms, not "inert on
       stock, decisive with the patch". On stock it is now +17 binheap
       against -4 calculator at ~25% more evaluations on one challenge,
       which is no longer obviously negative. Left OFF pending a
       decision rather than flipped, because that is a shipping default
       and the call is not mine to make silently. *)
    let sort_siblings_enabled = false in
    let improved =
      if sort_siblings_enabled then begin
        let a5 = !attempts in
        let r = sort_siblings () || improved in
        pass_costs.(5) <- pass_costs.(5) + (!attempts - a5);
        r
      end
      else improved
    in
    continue_ := improved
  done;
  (* [budget_ok ()] still true here can only mean the loop exited
     because [continue_] went false, i.e. one full round of every pass
     ran to completion and found nothing smaller ANYWHERE, with budget
     and time to spare -- a genuine fixpoint. If it is false, some pass
     may have been cut off partway through (its own inner while loops
     share the same [budget_ok ()]), so [continue_] being false in that
     case proves nothing; report truncated rather than risk a false
     "converged". *)
  final_choices :=
    Array.length (!best).Tape.main
    + Array.fold (!best).Tape.streams ~init:0 ~f:(fun a (_, c) ->
        a + Array.length c);
  (* What [converged] means, stated precisely, because it is easy to
     read more into it than is there.

     It does NOT mean "no smaller failing example exists". Establishing
     that would need exhaustive search over all smaller images. Every
     pass here is a heuristic over a limited neighbourhood -- lower an
     integer, delete a short block, redistribute a pair, minimize a
     choice -- so a smaller failing image may sit outside what they can
     reach, converged or not. The shrink_table's [is_minimal] knows the
     true minimum only because a human wrote it down.

     What it means is: THE SEARCH SETTLED rather than being cut off with
     work left to do. Its practical job is to answer "is re-running with
     a bigger budget or a longer deadline worth it?".

     Read that way the per-pass failure cutoff must NOT clear it. A pass
     that stops after [max_pass_failures] fruitless attempts has
     settled; more budget changes nothing, because the cutoff is not
     budget-driven. Only genuine budget or deadline exhaustion answers
     "yes, retry with more". An earlier version ran extra uncut sweeps
     to keep this flag true, costing the speedup (3.6x down to 2x) to
     buy a distinction that does not survive the observation that the
     passes are heuristics either way. *)
  let converged = budget_ok () in
  (!best_value, !attempts, !best, List.rev !trail, converged)

(* Replay a persisted tape image and apply [f] to the regenerated
   value. The tape is deliberately left in replay mode: functions
   inside the value keep drawing from the image's streams for as long
   as the value lives (each call rewinds its stream's cursor at the
   perturb boundary, so repeated same-argument calls stay pure), and
   arguments the image never saw sample fresh. *)
let replay_image_and_apply (type a r) (gen : a Base_quickcheck.Generator.t)
    ?(size = 30) (image : Tape.image) ~(f : a -> r) : a * r =
  let tape = Tape.create () in
  Tape.start_replay_image tape image;
  let random =
    Splittable_random.For_tape.attach
      (Splittable_random.of_int replay_fresh_seed)
      tape
  in
  let value = Base_quickcheck.Generator.generate gen ~size ~random in
  let r = f value in
  (value, r)

(* Replay a persisted main-stream tape: regenerate the value it
   encodes. Replayed values come from the tape itself, so [size] only
   guides draws past the end of a stale tape. Note: functions inside
   the value draw fresh once this returns; use [replay_image_and_apply]
   to run a property against the replayed value. *)
let replay (type a) (gen : a Base_quickcheck.Generator.t) ?size
    (choices : Tape.choice array) : a =
  fst
    (replay_image_and_apply gen ?size (Tape.image_of_main choices)
       ~f:(fun _ -> ()))

(* HealthCheck.large_base_example's tape analogue: trivialize [image]
   (every recorded choice forced to its shrink target -- the same
   operation the shrink loop's own "Pass 1" performs) and replay it
   through the generator. Trivializing just rewrites the recorded
   VALUES; replaying is what actually gives the SHORTER shape a real
   generator produces from them (e.g. a list generator that sees its
   length choice forced to the minimum genuinely emits a short list and
   never draws the now-unneeded element choices), mirroring Hypothesis's
   own [zero_data] probe (engine_hypothesis.py, ChoiceTemplate
   ("simplest")). Costs one extra generation pass; called at most once
   per [Tape_health.state] (guarded by the caller in [run]), so it is
   not paid on every case. *)
let natural_example_choices (type a) ~(gen : a Base_quickcheck.Generator.t)
    ~size (image : Tape.image) : int =
  let trivial = image_trivialized image in
  let tape = Tape.create () in
  Tape.start_replay_image tape trivial;
  let random =
    Splittable_random.For_tape.attach
      (Splittable_random.of_int replay_fresh_seed)
      tape
  in
  let (_ : a) = Base_quickcheck.Generator.generate gen ~size ~random in
  let out = Tape.finish tape in
  Tape.image_size out.Tape.image

(* Shared tail of both [run] (a fresh search) and [resume] (continuing
   from a previously-saved tape): given a confirmed-still-failing
   (image0, value), either report it as already fully trivial or spend
   the shrink budget on it, and package the result -- including the
   converged/truncated distinction that lets a caller tell a genuine
   local minimum from a best-effort one. *)
let finish_from_failure (type a) ~tape ~(gen : a Base_quickcheck.Generator.t)
    ~size ~(test : a -> bool) ~budget ~(max_seconds : float option)
    ~(max_shrinks : int) ~(max_stall : int option)
    ~(max_pass_failures : int option) ~domains
    ~pool ~(realign : realign) ~(stats : stats) ~(image0 : Tape.image)
    ~(value : a) : a result =
  (* The single point at which the engine commits to a failing image.
     Every discovery path reaches here -- ordinary generation, the
     correlated-value mutation, the pooled batch, and [resume]'s replay
     -- so counting here cannot miss one, and a fifth path added later
     cannot silently reintroduce the gap.

     It used to be counted at the generate-phase discovery site only, so
     a failure first found by the mutation was counted in NEITHER
     bucket: the summary line read "12 cases (12 valid, 0 discarded, 0
     failing)" on a run that returned a counterexample, and the total is
     derived from the three buckets so the failing case went missing
     from that too. Reported as issue #1, with a reproducer showing
     30/50 runs affected when the property needs two draws to be equal
     (which is what the mutation constructs) against 0/50 when it does
     not. *)
  stats.cases_failed <- stats.cases_failed + 1;
  let live_value image =
    fst (replay_image_and_apply gen ~size image ~f:(fun _ -> ()))
  in
  if image_all_trivial image0 then
    Failed
      { minimal = live_value image0
      ; original = value
      ; attempts = 0
      ; choices = image0.main
      ; image = image0
      ; trail = []
      ; converged = true
      }
  else begin
    (* Wall-clock the whole shrink phase: [stats.shrink_time] is printed
       in the `Full report's three-way time split and was previously
       never assigned, so the split always read shrink 0.0000s
       (tapecheck#7). *)
    let shrink_start = Unix.gettimeofday () in
    let _minimal, attempts, image, trail, converged =
      shrink ~tape ~gen ~size ~test ~budget ~max_seconds ~max_shrinks
        ~max_stall ~max_pass_failures ~domains ~pool ~realign ~stats
        ~initial_tape:image0 ~initial_value:value
    in
    stats.shrink_time
      <- stats.shrink_time +. (Unix.gettimeofday () -. shrink_start);
    Failed
      { minimal = live_value image
      ; original = value
      ; attempts
      ; choices = image.main
      ; image
      ; trail
      ; converged
      }
  end

(* Non-deterministic generator detection, ported in spirit from
   Hypothesis's DataTree, which raises Flaky with:

     "Inconsistent data generation! Data generation behaved differently
      between different runs. Is your data generation depending on
      external state?"

   A generator that reads a clock, a global, or an unseeded PRNG makes
   every recorded tape meaningless: replay produces a different value,
   so a saved failure will not reproduce, shrinking chases a moving
   target, and the whole model quietly stops holding. Today tapecheck
   produces silent nonsense in that situation.

   The check is exact here and needs no equality on values, which is the
   nice part. Replay the SAME image twice and compare the images the two
   replays record. A deterministic generator consumes the tape
   identically both times and records an identical image; one that draws
   from outside the tape does not. [Tape.compare_image] is already
   defined, so this costs one extra replay and no new machinery.

   Deliberately checked once per run, on the first failure, rather than
   per case: the failing path is off the CI happy path.

   LIMITATION, measured (test_nondet/test_flaky_gen.ml). Two replays
   catch an ALWAYS-divergent generator every time, but an intermittently
   flaky one only when the two samples happen to straddle the
   divergence. Detection tracks 2p(1-p) almost exactly:

     flake rate 0.50 -> 50% detected
     flake rate 0.10 -> 17%
     flake rate 0.01 ->  3%

   So this is a coin-flip detector for rare flakiness. [replays] raises
   the sample count -- detection becomes 1 - (p^k + (1-p)^k) -- which
   helps linearly and cheaply, but does not change the shape.

   (Note a generator that CONSISTENTLY draws differently from what the
   tape recorded is deterministic and correctly passes: consistently
   different is not divergent.)

   The real fix is Hypothesis's, and it is structural rather than
   statistical: DataTree observes every draw of every run against a
   persistent tree, so a divergence anywhere is caught, with an effective
   sample size of the whole run rather than k. tapecheck already replays
   hundreds of times during shrinking, so hooking the check there would
   get the same power nearly free. Written up in MINING-BACKLOG.md; not
   done, because it touches the replay path rather than sitting beside
   it. *)
let check_generator_determinism (type a) ?(replays = 8)
    ~(gen : a Base_quickcheck.Generator.t) ~size ~(test : a -> bool)
    (image : Tape.image) : bool =
  let replay_once () =
    let tape = Tape.create () in
    Tape.start_replay_image tape image;
    let _v, _tested, out =
      run_and_test ~tape ~gen ~size ~seed:replay_fresh_seed ~test
    in
    out.Tape.image
  in
  let first = replay_once () in
  let rec go k =
    if k <= 1 then true
    (* [Tape.equal_image], not [compare_image = 0]. The order is a
       PREORDER: float choices compare by distance from their target, so
       0.0 drawn from [0,1] and 5.0 drawn from [5,6] are indistinguishable
       to it. A generator alternating between two such draws is
       nondeterministic and this check passed it. *)
    else if not (Tape.equal_image (replay_once ()) first) then false
    else go (k - 1)
  in
  go replays

let nondeterminism_warning =
  "tapecheck: INCONSISTENT DATA GENERATION.\n\
  \  Replaying the same tape twice produced different draws, so this\n\
  \  generator is not a pure function of the tape. Is it reading a clock,\n\
  \  a global, or an unseeded random source?\n\
  \  Consequences: saved failures will not reproduce, shrinking chases a\n\
  \  moving target, and the minimal example reported may not fail at all."

(* Correlated-value mutation.

   Parity review #3: Hypothesis mutates test cases by structurally
   duplicating equivalent spans, "to produce correlated or repeated
   values that random sampling rarely finds". tapecheck drew every case
   from an independent seed and had no such move.

   Measured need (diag2/probe_correlation.ml), finding a bug that
   requires two values to COINCIDE, over 200 runs:

     pair a = b, each 0..10        200/200
     pair a = b, each 0..100       182/200
     pair a = b, each 0..1000       69/200
     pair a = b, each 0..100000     32/200

   Independent sampling simply cannot make two wide-range values agree.
   Edge-case biasing helps a little -- both draws sometimes land on the
   same special value -- and nowhere near enough.

   The mutation: take a recorded image, find two integer choices with
   IDENTICAL bounds, and copy one value over the other. Same bounds is
   the cheap stand-in for "same kind of thing"; without span structure
   we cannot know that two choices belong to comparable positions, but
   equal bounds means the generator drew them from the same range, which
   is a decent proxy and costs nothing. *)
let correlate_image (img : Tape.image) ~(pick : int) : Tape.image option =
  let arr = img.Tape.main in
  let n = Array.length arr in
  (* Every ordered pair of integer choices sharing bounds is a candidate
     mutation; [pick] selects among them deterministically, so a run
     stays reproducible from its seed. *)
  let pairs = ref [] in
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      if i <> j then
        match (arr.(i), arr.(j)) with
        | Tape.Integer a, Tape.Integer b
          when Int64.(a.lo = b.lo)
               && Int64.(a.hi = b.hi)
               && Int64.(a.value <> b.value) ->
          pairs := (i, j) :: !pairs
        | _ -> ()
    done
  done;
  match !pairs with
  | [] -> None
  | ps ->
    let ps = List.rev ps in
    let i, j = List.nth_exn ps (pick % List.length ps) in
    let src = arr.(i) in
    Some
      { img with
        Tape.main = Array.mapi arr ~f:(fun k c -> if k = j then src else c)
      }

(* Multiple distinct failures in ONE run, each minimised separately.

   Ported from Hypothesis, which keys failures by [interesting_origin]
   (data.py) -- exception type plus location, including __cause__ and
   __context__ chains -- and shrinks each origin under a predicate that
   preserves it (engine.py, shrink_interesting_examples).

   THE DETAIL THAT MAKES IT WORK, and which is easy to omit: shrinking
   bug A must only accept candidates that still fail AS BUG A. Without
   that constraint, shrinking one failure "slips" into a different,
   smaller one and the first is lost. That is exactly what [s_accept]
   is for, so this needed no new machinery -- only a different
   acceptance rule.

   [test] here RAISES to fail, unlike [run]'s bool. That is deliberate
   (Matthias's suggestion): a bool has no identity, so two different
   bugs are indistinguishable from one bug found twice. Keeping [run]
   untouched means nothing existing pays for a feature it does not use,
   and the cheap path stays cheap. *)
type origin =
  { exn_name : string
  ; loc : string
  }

let compare_origin a b =
  match String.compare a.exn_name b.exn_name with
  | 0 -> String.compare a.loc b.loc
  | c -> c

let sexp_of_origin o =
  Sexp.List [ Sexp.Atom o.exn_name; Sexp.Atom o.loc ]

(* Exception identity plus the first source location in its backtrace.
   The OCaml analogue of their (type, file, line) tuple. A raise with no
   recorded backtrace still gets a stable origin from its exception
   name alone, which is weaker but never wrong. *)
let origin_of_exn exn bt =
  let exn_name =
    let s = Stdlib.Printexc.to_string exn in
    match String.lsplit2 s ~on:'(' with Some (n, _) -> n | None -> s
  in
  let loc =
    match Stdlib.Printexc.backtrace_slots bt with
    | None -> "<no backtrace>"
    | Some slots ->
      let rec first = function
        | [] -> "<no location>"
        | slot :: rest -> (
          match Stdlib.Printexc.Slot.location slot with
          | Some l ->
            Printf.sprintf "%s:%d" l.Stdlib.Printexc.filename
              l.Stdlib.Printexc.line_number
          | None -> first rest)
      in
      first (Array.to_list slots)
  in
  { exn_name; loc }

type 'a failure_report =
  { fr_origin : origin
  ; fr_minimal : 'a
  ; fr_image : Tape.image
  ; fr_attempts : int
  }

let run_multi (type a) ?(seed = 0) ?(count = 100) ?(size = 10)
    ?(budget = 2000) ?(realign : realign = `Consume) ?stats
    (gen : a Base_quickcheck.Generator.t) ~(test : a -> unit) :
    a failure_report list =
  let stats = match stats with Some s -> s | None -> no_stats () in
  Stdlib.Printexc.record_backtrace true;
  let found : (origin, Tape.image * a) Hashtbl.t = Hashtbl.Poly.create () in
  let tape = Tape.create () in
  let last_origin = ref None in
  (* A wrapper that reports failure as [false] and records WHICH failure
     it was. The origin has to be captured here, inside the callback,
     because the exception does not survive; the image has to be taken
     after, from the finished tape. *)
  let probing v =
    last_origin := None;
    match test v with
    | () -> true
    | exception e ->
      last_origin := Some (origin_of_exn e (Stdlib.Printexc.get_raw_backtrace ()));
      false
  in
  for case = 0 to count - 1 do
    Tape.start_recording tape;
    let value, _tested, out =
      run_and_test ~tape ~gen ~size ~seed:(seed + case) ~test:probing
    in
    match !last_origin with
    | Some o when not (Hashtbl.mem found o) ->
      Hashtbl.set found ~key:o ~data:(out.Tape.image, value)
    | _ -> ()
  done;
  (* Shrink each origin separately. The whole point is the predicate:
     a candidate counts as failing ONLY if it fails with the SAME
     origin, so shrinking bug A cannot slip into a smaller bug B and
     lose A. Everything else is the ordinary shrink pass suite, reused
     unchanged by handing it a different [~test]. *)
  Hashtbl.fold found ~init:[] ~f:(fun ~key:o ~data:(img, v) acc ->
    let same_origin_only value =
      match test value with
      | () -> true
      | exception e ->
        let o' = origin_of_exn e (Stdlib.Printexc.get_raw_backtrace ()) in
        (* "true" means passing, i.e. not a candidate. A DIFFERENT bug
           is treated as a pass here on purpose. *)
        compare_origin o o' <> 0
    in
    let shrink_tape = Tape.create () in
    let _minimal, attempts, image, _trail, _converged =
      shrink ~tape:shrink_tape ~gen ~size ~test:same_origin_only ~budget
        ~max_seconds:None ~max_shrinks:500 ~max_stall:None
        ~max_pass_failures:(Some 20) ~domains:1 ~pool:None ~realign ~stats
        ~initial_tape:img ~initial_value:v
    in
    (* Rebuild from [image] rather than returning shrink's own value,
       exactly as [finish_from_failure] does and for the same reason:
       shrink's value was built on a tape that [Tape.finish] has since
       reset, and a value CONTAINING a generated function keeps drawing
       from that tape when called. Returning it directly reported a
       stale, non-minimal function -- measured, [f 0 = 298] where the
       minimal tape gives 101. *)
    let minimal =
      fst (replay_image_and_apply gen ~size image ~f:(fun _ -> ()))
    in
    { fr_origin = o; fr_minimal = minimal; fr_image = image;
      fr_attempts = attempts }
    :: acc)
  |> List.sort ~compare:(fun a b -> compare_origin a.fr_origin b.fr_origin)

(* Targeted property-based testing: hill-climb to MAXIMISE a score,
   rather than shrinking to minimise a tape.

   Ported from Hypothesis's Optimiser (optimiser.py), which cites
   Loescher & Sagonas, "Targeted property-based testing", ISSTA 2017.
   Their own framing is worth keeping: "a fairly naive hill climbing
   algorithm ... not expected to produce amazing results, because it is
   designed to be run in a fairly small testing budget, so it
   prioritises finding easy wins and bailing out quickly".

   Four details from their implementation that the idea alone does not
   imply, all of which are carried over here:

   1. LATERAL MOVES at equal score, gated on the tape not growing.
      A strict hill climber sticks on plateaus; accepting equal-score
      moves escapes them, and tying that to "the tape did not grow"
      stops it wandering. Their comment: "gives us a certain amount of
      freedom for lateral moves that will take us out of local maxima".
   2. Walk choices BACK TO FRONT, restarting from the end whenever the
      best improves.
   3. Replace against the CURRENT best, not the starting case, "so if we
      luck into a good draw we get to keep the good bits".
   4. Cap improvements (100), because a score need not be bounded above
      -- without it the loop has no termination condition at all.

   Uses [find_integer] for the value search, and the same [search]
   machinery as shrinking: only [s_interesting] (any valid case, not
   just failures) and [s_accept] (better score, or equal score with no
   growth) differ.

   LIMITATION: this EDITS existing choices and cannot grow the tape, so
   it can raise the values in a list but never add an element, and an
   empty starting draw has nothing to climb at all. Hypothesis's
   optimiser can extend the buffer (its [__extend] field, set to "full"
   in the target phase).

   A cheap growth move was tried and REJECTED: append a copy of the last
   choice and let replay read it. Measured over 30 seeds
   (diag2/probe_growth.ml) it added a list element in 3/30 runs under
   [G.list] and 0/30 under a continuation-bool encoding -- the opposite
   way round from what I predicted, and useless either way. Under the
   continuation encoding the last choice is the STOP bool, so appending
   another changes nothing; growing there means flipping that bool AND
   supplying a value, which append-a-copy cannot express.

   Real growth needs their mechanism rather than a proxy: extend with
   FRESH data and let the generator draw more, which means letting a
   proposal run past the recorded end instead of treating that as an
   overrun. Worth doing; still not done. *)
let run_target (type a) ?(seed = 0) ?(size = 10) ?(max_improvements = 100)
    ?(budget = 2000) ?(realign : realign = `Consume) ?stats
    (gen : a Base_quickcheck.Generator.t) ~(objective : a -> float) :
    a * float * int =
  let stats = match stats with Some s -> s | None -> no_stats () in
  let tape = Tape.create () in
  Tape.start_recording tape;
  let value0, _tested, out0 =
    run_and_test ~tape ~gen ~size ~seed ~test:(fun _ -> true)
  in
  let best_score = ref (objective value0) in
  let best = ref out0.Tape.image
  and best_value = ref value0
  and trail = ref []
  and attempts = ref 0
  and shrinks = ref 0
  and alast = ref 0
  and mstall = ref Int.max_value in
  let improvements = ref 0 in
  let st =
    { s_gen = gen
    ; s_size = size
    ; s_test = (fun _ -> true)
    ; s_tape = tape
    ; s_realign = realign
    ; s_stats = stats
    ; s_pool = None
    ; s_domains = 1
    ; s_budget = budget
    ; s_max_shrinks = Int.max_value
    ; s_deadline = None
    ; s_best = best
    ; s_best_value = best_value
    ; s_trail = trail
    ; s_attempts = attempts
    ; s_shrinks = shrinks
    ; s_attempts_at_last_shrink = alast
    ; s_max_stall = mstall
    ; s_seen = Hashtbl.Poly.create ()
    ; s_last_recorded = ref None
    ; (* Any VALID case is a candidate -- we are maximising over passing
         inputs, not chasing a failure. *)
      s_interesting =
        (function
        | Tape_stats.Case_passed | Tape_stats.Case_failed -> true
        | Tape_stats.Case_invalid -> false)
    ; s_accept =
        (fun ~best image value ->
          let sc = objective value in
          if Float.( > ) sc !best_score then begin
            best_score := sc;
            Int.incr improvements;
            true
          end
          else if
            (* Detail 1: lateral move, but only if the tape does not grow. *)
            Float.( = ) sc !best_score
            && Tape.image_size image <= Tape.image_size best
          then true
          else false)
    }
  in
  (* Detail 2: back to front, restarting on improvement. Detail 3 is
     implicit -- every proposal is built from [!best], which moves. *)
  let examined = Hashtbl.Poly.create () in
  let continue_ = ref true in
  while !continue_ && !improvements <= max_improvements && search_budget_ok st do
    let arr = (!best).Tape.main in
    let n = Array.length arr in
    let improved_here = ref false in
    let i = ref (n - 1) in
    while (not !improved_here) && !i >= 0 && search_budget_ok st do
      (if not (Hashtbl.mem examined !i) then begin
         Hashtbl.set examined ~key:!i ~data:();
         match arr.(!i) with
         | Tape.Integer { value; lo; hi } ->
           let try_delta d =
             let arr = (!best).Tape.main in
             if !i >= Array.length arr then false
             else begin
               let v = Int64.( + ) value d in
               if Int64.( > ) v hi || Int64.( < ) v lo then false
               else
                 search_attempt st
                   { !best with
                     Tape.main =
                       Array.mapi arr ~f:(fun j c ->
                         if j = !i then Tape.Integer { value = v; lo; hi }
                         else c)
                   }
             end
           in
           (* Detail 4's companion: find_integer for the step size, in
              both directions, since a score may be maximised either
              way. *)
           if Int64.( > ) (find_integer (fun k -> try_delta k)) 0L then
             improved_here := true
           else if
             Int64.( > ) (find_integer (fun k -> try_delta (Int64.neg k))) 0L
           then improved_here := true
         | Tape.Float _ | Tape.Bool _ | Tape.Marker -> ()
       end);
      Int.decr i
    done;
    if !improved_here then Hashtbl.clear examined else continue_ := false
  done;
  (!best_value, !best_score, !attempts)

(* Automatic failure replay. See tape_db.ml for why this exists and why
   deleting stale entries matters as much as saving new ones. *)
let run_with_db (type a) ~(db : Tape_db.t) ~(db_key : string)
    ~(run_fresh : unit -> a result)
    ~(resume_from : Tape.image -> a result)
    ~(image_of : a result -> Tape.image option) : a result =
  let stored = Tape_db.load db ~key:db_key in
  let outcome =
    match stored with
    | None -> run_fresh ()
    | Some img -> (
      (* Replay the saved tape FIRST. This is the whole point: a bug that
         is still present reproduces on call one instead of after a
         search. *)
      match resume_from img with
      | Failed _ as f -> f
      | Passed _ ->
        (* It no longer fails, so the entry is stale. Delete it and do a
           normal run. Without this the database only ever grows and
           re-runs get SLOWER, which is the opposite of the point. *)
        Tape_db.remove db ~key:db_key;
        run_fresh ())
  in
  (match image_of outcome with
   | Some img -> Tape_db.save db ~key:db_key img
   | None -> ());
  outcome

let run (type a) ?(seed = 0) ?(count = 100) ?(size = 10) ?(budget = 2000)
    ?(max_seconds : float option = None) ?(max_shrinks = 500)
    ?(max_stall : int option = None)
    ?(max_pass_failures : int option = Some 20) ?(domains = 1)
    ?(realign : realign = `Consume) ?stats ?health
    ?(suppress_health_check = []) (gen : a Base_quickcheck.Generator.t)
    ~(test : a -> bool) : a result =
  let stats = match stats with Some s -> s | None -> no_stats () in
  let health = match health with Some h -> h | None -> Tape_health.create () in
  let tape = Tape.create () in
  let pool = if domains > 1 then Some (Pool.create domains) else None in
  (* Protection must start HERE, immediately after the pool exists, not
     after the failure search. The search itself runs batches on the pool,
     so a generator or test raising during GENERATION skipped the
     finalizer entirely and leaked every worker. An earlier fix wrapped
     only the shrink phase and missed exactly that. *)
  Exn.protect
    ~finally:(fun () -> Option.iter pool ~f:Pool.shutdown)
    ~f:(fun () ->
    (* Find the first failing case. With a pool, generate and test cases
       in parallel batches; taking the lowest failing index in the batch
       preserves the sequential engine's choice of failure exactly. *)
    (* Exhaustion detection: the practical half of Hypothesis's
       DataTree. They track explored choice-prefixes exactly and know
       when a finite space is finished; this approximates it by noticing
       that generation has stopped producing anything NEW.

       Worth having because the alternative is silently wasteful: a
       generator over a small space (a bool, an enum, a narrow int
       range) re-draws the same handful of inputs for the rest of
       [count], testing nothing. Approximate rather than exact -- a big
       space can throw a run of coincidental repeats -- so the threshold
       is set where a false positive is cheap: it only ever stops a run
       that was already finding nothing new. *)
    let seen_generated = Hashtbl.Poly.create () in
    let first_correlated_failure = ref None in
    let consecutive_repeats = ref 0 in
    let exhausted_after = ref None in
    let repeats_before_giving_up = 64 in
    (* [cases_run] is what [Passed {cases}] reports: the number of cases
       actually executed, which the exhaustion early-stop can leave well
       below [count]. Reporting [count] there claimed work that never
       happened -- the summary line said 66 valid while the result said
       Passed {cases = 200} (tapecheck#11). *)
    let first_failure, cases_run =
      match pool with
      | None ->
        let found = ref None in
        let case = ref 0 in
        while
          Option.is_none !found
          && !case < count
          && !consecutive_repeats < repeats_before_giving_up
        do
          Tape.start_recording tape;
          (* Only pay for per-case timing (three Sys.time() calls,
             measured to be the dominant added cost -- see
             run_and_test_maybe_timed's comment and
             demo/stats_overhead_bench.ml) while the health-check window
             is still open; once it has closed, nothing downstream reads
             gen_dt/run_dt for this case, so skip computing them. *)
          let timed = not health.Tape_health.closed in
          let value, tested, out, gen_dt, run_dt =
            run_and_test_maybe_timed ~timed ~tape ~gen ~size
              ~seed:(seed + !case) ~test
          in
          if timed then begin
            stats.generate_time <- stats.generate_time +. gen_dt;
            stats.run_time <- stats.run_time +. run_dt
          end;
          Tape_stats.merge_current_events_into stats.events;
          (match tested with
           | None ->
             (* Unreachable: this path always starts a fresh recording,
                never a replay, so Tape.overrun_now is always false (see
                run_and_test's comment). *)
             ()
           | Some Tape_stats.Case_failed ->
             (* Counted in [finish_from_failure], not here: this is only
                ONE of four ways a failure is discovered, and counting at
                the discovery sites meant the correlated-value mutation's
                failures were never counted at all. *)
             found := Some (out.Tape.image, value)
           | Some ((Tape_stats.Case_passed | Tape_stats.Case_invalid) as verdict)
             ->
             let is_valid =
               match verdict with
               | Tape_stats.Case_passed -> true
               | Tape_stats.Case_invalid | Tape_stats.Case_failed -> false
             in
             if is_valid then stats.cases_valid <- stats.cases_valid + 1
             else stats.cases_invalid <- stats.cases_invalid + 1;
             if timed then begin
               let choices = Tape.image_size out.Tape.image in
               (* [natural_example_choices] replays this case's tape, so
                  it is only worth its own cost once per [health]
                  (guarded here, not just inside
                  [maybe_check_large_base_example], so the argument
                  itself is never even computed on later cases). *)
               if not health.Tape_health.checked_base_example then
                 Tape_health.maybe_check_large_base_example health
                   ~suppress:suppress_health_check
                   ~choices:(natural_example_choices ~gen ~size out.Tape.image);
               Tape_health.record health ~suppress:suppress_health_check
                 ~status:(if is_valid then `Valid else `Invalid) ~choices
                 ~generate_time:gen_dt
             end);
          (if Hashtbl.mem seen_generated out.Tape.image then
             Int.incr consecutive_repeats
           else begin
             Hashtbl.set seen_generated ~key:out.Tape.image ~data:();
             consecutive_repeats := 0
           end);
          (* After a fresh case, try one CORRELATED variant of it: two
             integer choices of the same bounds made equal. Random
             sampling finds these essentially never at wide ranges (see
             correlate_image), and the extra case is cheap because the
             mutation is a local edit on a tape we already have.

             Only when the fresh case passed -- if it already failed we
             are done searching -- and only every other case, so the
             generation budget is not halved.

             "Every other case" is keyed on [seed + case], NOT on [case]
             alone. [case] is local to one [run] call, and the main
             public entry point -- [Tape_test.result] -- calls [run]
             once per size with ~count:1, so [case] was always 0 and
             [0 % 2 = 1] never held. The mutation was therefore
             unreachable through the whole Tape_test API: it worked only
             for callers driving [Tape_engine.run] directly with a large
             ~count, which is exactly what its own benchmark and guard
             test do. [seed] varies per call there ([base_seed + case]),
             so this alternates across calls as well as within one. *)
          (if
             Option.is_none !found
             && (seed + !case) % 2 = 1
             && Option.is_none !first_correlated_failure
           then
             match correlate_image out.Tape.image ~pick:!case with
             | None -> ()
             | Some mutant -> (
               let mtape = Tape.create () in
               Tape.start_replay_image mtape mutant;
               let mvalue, mtested, mout =
                 run_and_test ~tape:mtape ~gen ~size
                   ~seed:replay_fresh_seed ~test
               in
               match mtested with
               | Some Tape_stats.Case_failed when not mout.Tape.overrun ->
                 first_correlated_failure := Some (mout.Tape.image, mvalue)
               | _ -> ()));
          if !consecutive_repeats >= repeats_before_giving_up then
            exhausted_after := Some (!case + 1);
          Int.incr case
        done;
        (match !exhausted_after with
         | Some n when Option.is_none !found ->
           Stdlib.prerr_endline
             (Printf.sprintf
                "tapecheck: generation appears EXHAUSTED after %d of %d cases \
                 (%d distinct inputs, then %d consecutive repeats). The \
                 remaining cases would only re-test inputs already tried. If \
                 the space really is that small, lower ~count; if not, the \
                 generator may be narrower than intended."
                n count
                (Hashtbl.length seen_generated)
                repeats_before_giving_up);
           Stdlib.flush Stdlib.stderr
         | _ -> ());
        stats.warnings <- health.Tape_health.fired;
        ( (match !found with
           | Some _ as f -> f
           | None -> !first_correlated_failure)
        , !case )
      | Some pool ->
        let found = ref None in
        let batch_start = ref 0 in
        let width = domains * 2 in
        while Option.is_none !found && !batch_start < count do
          let n = min width (count - !batch_start) in
          let results =
            Pool.run_batch pool
              (List.init n ~f:(fun d () ->
                 let tape = Tape.create () in
                 Tape.start_recording tape;
                 let value, tested, out =
                   run_and_test ~tape ~gen ~size
                     ~seed:(seed + !batch_start + d) ~test
                 in
                 (* Verdict-aware since the stats merge: only a genuine
                    failure counts, and an [assume]-discarded case
                    (Case_invalid) must NOT be mistaken for one.

                    The verdict is also returned, not just consumed: the
                    main domain needs it to count the case. See
                    [pool_payload] for why this cannot be counted here.
                    [no_eval_stats]: this phase has no shrink accounting
                    to report. *)
                 let failure =
                   match tested with
                   | Some Tape_stats.Case_failed -> Some (out.Tape.image, value)
                   | _ -> None
                 in
                 ((failure, no_eval_stats), tested)))
          in
          (* Count every case the workers actually ran, on this domain.
             Without this the pooled path reported [Passed {cases = N}]
             with 0 valid and 0 invalid -- the returned result and the
             summary line disagreeing, which is tapecheck#1.

             Only cases up to and including the first failure are
             counted: run_batch evaluates the whole batch speculatively,
             so a later case in the same batch ran but is not part of
             the run the engine reports. *)
          let stop_at =
            match List.findi results ~f:(fun _ ((f, _), _) -> Option.is_some f) with
            | Some (i, _) -> i + 1
            | None -> List.length results
          in
          List.iteri results ~f:(fun i ((_, _), tested) ->
            if i < stop_at then
              match tested with
              | Some Tape_stats.Case_passed ->
                stats.cases_valid <- stats.cases_valid + 1
              | Some Tape_stats.Case_invalid ->
                stats.cases_invalid <- stats.cases_invalid + 1
              | Some Tape_stats.Case_failed | None ->
                (* Failures are counted in [finish_from_failure], the
                   single commit point, exactly as on the sequential
                   path. *)
                ());
          (* run_batch preserves task order, so the first Some is the
             lowest failing case index. *)
          found := List.find_map results ~f:(fun ((f, _), _) -> f);
          batch_start := !batch_start + n
        done;
        (!found, !batch_start)
    in
    (* The reported minimal is regenerated from the winning image on a
       tape left in replay mode, so a counterexample containing functions
       keeps its observed behaviour after the engine returns (a function
       backed by a finished tape would silently fall back to fresh
       randomness on the very calls the report is about). *)
    (* Shut the pool down on EVERY exit, not just the normal one. A test
       or generator that raises under [~domains > 1] previously left the
       worker domains blocked forever, so a caller that catches the
       exception and retries accumulates leaked domains until the process
       dies. Found in review of 061923e. *)
    match first_failure with
      | None -> Passed { cases = cases_run }
      | Some (image0, value) ->
        (* Check determinism ONCE, on the failure path, before shrinking.
           This existed but nothing outside diagnostic tests called it --
           flagged in review, and fair: an unreachable check is not a
           feature. The failure path is the right place. It costs nothing
           on a passing run, and a generator that is not a pure function
           of the tape makes everything downstream meaningless: a saved
           failure that will not reproduce, a shrinker chasing a moving
           target, a reported minimal example that may not fail at all.

           WARNS rather than raising. The failure is real and worth
           reporting even when the generator is impure; refusing to
           shrink would replace a useful-but-caveated answer with none. *)
        if not (check_generator_determinism ~gen ~size ~test image0) then begin
          Stdlib.prerr_endline nondeterminism_warning;
          Stdlib.flush Stdlib.stderr
        end;
        finish_from_failure ~tape ~gen ~size ~test ~budget ~max_seconds
          ~max_shrinks ~max_stall ~max_pass_failures ~domains ~pool ~realign
          ~stats ~image0 ~value)

(* Resumable shrinking: continue from a tape saved earlier (typically
   printed on a previous run that hit its budget -- see [Tape_test]'s
   truncation message) instead of searching for a fresh failure. The
   tape is exactly the same serializable image [run] already produces
   ([Tape.serialize_image]/[deserialize_image], the same "ct1" format
   the regression file uses), which is the whole point: a tape is a
   value you can print, save, and hand back in, unlike a rose tree's
   in-memory shrink state. [image] is replayed once to confirm it still
   fails (and to obtain the value shrinking continues from); if it no
   longer does -- the generator changed, or the tape was hand-edited
   into something that now passes -- this reports [Passed { cases = 0 }]
   rather than guessing, exactly as loudly as [Tape_test]'s existing
   stale-regression-entry handling. *)
let resume (type a) ?(size = 10) ?(budget = 2000)
    ?(max_seconds : float option = None) ?(max_shrinks = 500)
    ?(max_stall : int option = None)
    ?(max_pass_failures : int option = Some 20) ?(domains = 1)
    ?(realign : realign = `Consume) ?stats
    (gen : a Base_quickcheck.Generator.t) ~(test : a -> bool)
    (image : Tape.image) : a result =
  let stats = match stats with Some s -> s | None -> no_stats () in
  let tape = Tape.create () in
  let pool = if domains > 1 then Some (Pool.create domains) else None in
  (* Same correction as in [run]: the confirmation replay below can
     raise, and it ran OUTSIDE the protection before, leaking the idle
     workers. Everything after pool creation belongs inside. *)
  Exn.protect
    ~finally:(fun () -> Option.iter pool ~f:Pool.shutdown)
    ~f:(fun () ->
      let value, tested, out =
        let replay_tape = Tape.create () in
        Tape.start_replay_image replay_tape image;
        run_and_test ~tape:replay_tape ~gen ~size ~seed:replay_fresh_seed ~test
      in
      match tested with
      | Some Tape_stats.Case_failed when not out.Tape.overrun ->
        finish_from_failure ~tape ~gen ~size ~test ~budget ~max_seconds
          ~max_shrinks ~max_stall ~max_pass_failures ~domains ~pool ~realign
          ~stats ~image0:image ~value
      | _ -> Passed { cases = 0 })

let stats_summary_line (stats : stats) =
  let warnings_suffix =
    if List.is_empty stats.warnings then ""
    else
      Printf.sprintf " -- health checks fired: %s"
        (String.concat ~sep:", "
           (List.rev_map stats.warnings ~f:Tape_health.to_string))
  in
  Printf.sprintf "tapecheck: %d cases (%d valid, %d discarded, %d failing)%s"
    (stats.cases_valid + stats.cases_invalid + stats.cases_failed)
    stats.cases_valid stats.cases_invalid stats.cases_failed warnings_suffix

(* The fuller report (?report:`Full), the direct analogue of
   Hypothesis's --hypothesis-show-statistics
   (outreach/hypothesis-inventory.md section 3): every event() tag and
   its count, and the generate/run/shrink time split plus shrink call
   counts the task write-up asks for. *)
let stats_to_string_hum (stats : stats) : string =
  let buf = Buffer.create 512 in
  let add fmt = Stdlib.Printf.ksprintf (Buffer.add_string buf) fmt in
  add "%s\n" (stats_summary_line stats);
  if Hashtbl.is_empty stats.events then add "  events: (none)\n"
  else begin
    add "  events:\n";
    Hashtbl.to_alist stats.events
    |> List.sort ~compare:(fun (_, a) (_, b) -> Int.compare b a)
    |> List.iter ~f:(fun (label, count) -> add "    %-50s %d\n" label count)
  end;
  add "  timing: generate %.4fs, run %.4fs, shrink %.4fs\n" stats.generate_time
    stats.run_time stats.shrink_time;
  add "  shrink calls: %d replays, %d tests, %d misaligned, %d discarded proposals\n"
    stats.replays stats.tests stats.misaligns stats.shrink_discards;
  Buffer.contents buf
