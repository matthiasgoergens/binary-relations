(* RO6 (outreach/ro-roadmap.md): "tools should always announce counts of
   discarded test cases... OCaml's QuickCheck hides output when tests
   succeed, which obscures that information" (the ICSE 2024 paper,
   quoted in outreach/paper-full.txt). This module ports Hypothesis's
   two primitives for that (control.py's [assume]/[event], read via
   outreach/hypothesis-inventory.md section 3 and 6):

   - [assume cond] marks the CURRENT test case invalid (discarded, not
     failed, not passed) when [cond] is false -- the direct analogue of
     [assume()] raising [UnsatisfiedAssumption] in Hypothesis. There is
     no "steering away from similar cases" beyond that (Hypothesis
     itself doesn't do this either, despite folklore to the contrary;
     see the inventory's section 6 correction).
   - [event ?payload label] tags the current case with a label,
     aggregated by [Tape_engine.run] into a frequency table for the
     statistics report -- the analogue of Hypothesis's [event()] /
     [--hypothesis-show-statistics]'s event table.

   Both need a way to reach "the current test case" from inside an
   arbitrarily nested call in the user's property function, without
   threading extra arguments through every generator and test. Hypothesis
   does this with a thread-local "current build context"; the OCaml
   analogue for a multicore engine that can run test bodies on several
   domains at once (Tape_engine.Pool, used by ?domains > 1) is
   domain-local storage: each domain gets its own current-case slot, so
   two domains evaluating different shrink proposals concurrently never
   see each other's events. *)

open! Base

exception Invalid_example
(* Raised by [assume] when its condition is false. The engine catches
   this at every point it invokes the user's test function (never
   elsewhere), and turns it into a discarded case: neither a pass nor a
   failure. An [assume] this module does not catch (e.g. one raised on
   a domain not currently running a case) is a programmer error and is
   left to propagate as an ordinary uncaught exception. *)

let assume cond = if not cond then raise Invalid_example

(* The three-way outcome of actually calling the user's test function
   once, replacing the old [bool] result everywhere the engine invokes
   [test]. [Case_invalid] is new; [Case_passed]/[Case_failed] are the
   old [true]/[false]. *)
type verdict =
  | Case_passed
  | Case_failed
  | Case_invalid

(* Per-case event bag: label (or "label: payload") -> occurrence count
   WITHIN THIS ONE CASE. [Tape_engine.run]'s generate-phase loop
   aggregates this into the run-wide frequency table after every case;
   [take_events] hands over the current bag and starts a fresh one, so
   two consecutive cases on the same domain never see each other's
   events even if the test function forgets to call [event] at all on
   the second one. *)
type case = { mutable events : (string, int) Hashtbl.t }

let empty_case () = { events = Hashtbl.create (module String) }

let current : case Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key empty_case

let event ?payload label =
  let key =
    match payload with
    | None -> label
    | Some payload -> label ^ ": " ^ payload
  in
  let c = Stdlib.Domain.DLS.get current in
  Hashtbl.update c.events key ~f:(function
    | None -> 1
    | Some n -> n + 1)

(* Called by the engine immediately before invoking the test function
   for one case: clear whatever the previous case (on this domain, if
   any) left behind. *)
let begin_case () =
  let c = Stdlib.Domain.DLS.get current in
  Hashtbl.clear c.events

(* Called by the engine immediately after: fold this case's events into
   [dst] (the run-wide aggregate), summing on key collision, then clear
   the current bag IN PLACE for the next case.

   Deliberately does NOT allocate a fresh Hashtbl per case (an earlier
   version handed back the bag and replaced it with
   [Hashtbl.create (module String)], which measurably cost more than
   the rest of RO6's per-case bookkeeping combined -- see
   demo/stats_overhead_bench.ml): [Hashtbl.iteri]/[Hashtbl.clear] on an
   EMPTY table (the overwhelmingly common case, since most properties
   never call [event]) are cheap, so the common path pays almost
   nothing, while a property that does call [event] still gets
   correctly aggregated. *)
let merge_current_events_into dst =
  let c = Stdlib.Domain.DLS.get current in
  if not (Hashtbl.is_empty c.events) then begin
    Hashtbl.iteri c.events ~f:(fun ~key ~data ->
      Hashtbl.update dst key ~f:(function
        | None -> data
        | Some n -> n + data));
    Hashtbl.clear c.events
  end
