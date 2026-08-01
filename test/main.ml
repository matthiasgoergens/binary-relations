open! Core
open Rel

(* A deliberately plain harness. The interesting content is in what is
   checked, and several of the checks below are measurements rather than
   assertions — "the index was built once", "the planner touched fewer tuples"
   — because those are the claims that are easiest to believe without evidence
   and wrong most often. *)

let failures = ref 0
let checks = ref 0

let check name b =
  incr checks;
  if not b then (
    incr failures;
    print_endline ("FAIL  " ^ name))

let check_eq_int name ~expect actual =
  incr checks;
  if expect <> actual then (
    incr failures;
    printf "FAIL  %s: expected %d, got %d\n" name expect actual)

let section name = printf "\n-- %s\n" name

(* ------------------------------------------------------------------ *)
(* Generators                                                          *)
(* ------------------------------------------------------------------ *)

module Sample = struct
  module L = Laws.Make (Eval)

  type t = {
    a : (int * int) list;
    b : (int * int) list;
    c : (int * int) list;
  }
  [@@deriving sexp_of]

  (* A small element domain on purpose: laws about meet, division and closure
     only bite when relations actually overlap, and over a wide domain
     randomly generated relations are almost always disjoint, so nearly every
     law would hold vacuously. *)
  let elem = Base_quickcheck.Generator.int_inclusive 0 5

  let rel =
    let open Base_quickcheck.Generator.Let_syntax in
    let%bind n = Base_quickcheck.Generator.int_inclusive 0 12 in
    Base_quickcheck.Generator.list_with_length
      ~length:n
      (Base_quickcheck.Generator.both elem elem)

  let quickcheck_generator =
    let open Base_quickcheck.Generator.Let_syntax in
    let%map a = rel and b = rel and c = rel in
    { a; b; c }

  let quickcheck_shrinker = Base_quickcheck.Shrinker.atomic
  let to_sample { a; b; c } = { L.a = Eval.of_list a; b = Eval.of_list b; c = Eval.of_list c }
end

let qc_config = { Base_quickcheck.Test.default_config with test_count = 300 }

(* ------------------------------------------------------------------ *)
(* M0 — the laws                                                       *)
(* ------------------------------------------------------------------ *)

let test_laws () =
  section "M0: laws of the algebra, property-checked against Eval";
  let module L = Laws.Make (Eval) in
  let by_group = Hashtbl.create (module String) in
  List.iter L.all ~f:(fun law ->
    let ok = ref true in
    (try
       Base_quickcheck.Test.run_exn
         ~config:qc_config
         (module Sample)
         ~f:(fun s -> if not (law.L.check (Sample.to_sample s)) then failwith "law violated")
     with
    | e ->
      ok := false;
      incr failures;
      printf "FAIL  law %s/%s\n      %s\n" law.L.group law.L.name (Exn.to_string e));
    incr checks;
    Hashtbl.update by_group law.L.group ~f:(function
      | None -> (1, if !ok then 0 else 1)
      | Some (n, f) -> (n + 1, f + if !ok then 0 else 1)));
  Hashtbl.iteri by_group ~f:(fun ~key ~data:(n, f) ->
    printf "   %-20s %2d laws, %d failing\n" key n f)

(* ------------------------------------------------------------------ *)
(* M2 — lazy automatic indexes                                         *)
(* ------------------------------------------------------------------ *)

let test_indexes () =
  section "M2: indexes are built on demand, once, and never invalidated";
  let r = Relation.of_list (List.init 200 ~f:(fun i -> (i % 20, i))) in
  Relation.reset_counters ();
  check_eq_int "no index is built until one is demanded" ~expect:0 (Relation.index_builds ());
  ignore (Relation.image r 3 : int Set.Poly.t);
  check_eq_int "first lookup builds exactly one index" ~expect:1 (Relation.index_builds ());
  for i = 0 to 99 do
    ignore (Relation.image r i : int Set.Poly.t)
  done;
  check_eq_int
    "a hundred more lookups build none: memoised, and immutability means it can never go stale"
    ~expect:1
    (Relation.index_builds ());
  ignore (Relation.preimage r 7 : int Set.Poly.t);
  check_eq_int "the other direction is a second, separate index" ~expect:2 (Relation.index_builds ());

  (* The access-path claim, measured: taking a converse does no index work,
     because the converse's forward index *is* the original's backward one. *)
  Relation.reset_counters ();
  let r2 = Relation.of_list (List.init 200 ~f:(fun i -> (i % 20, i))) in
  ignore (Relation.image r2 3 : int Set.Poly.t);
  ignore (Relation.preimage r2 3 : int Set.Poly.t);
  let before = Relation.index_builds () in
  let c = Relation.converse r2 in
  for i = 0 to 50 do
    ignore (Relation.image c i : int Set.Poly.t);
    ignore (Relation.preimage c i : int Set.Poly.t)
  done;
  check_eq_int "converse reuses both indexes: no rebuild at all" ~expect:before (Relation.index_builds ());

  (* Statistics are exact, not sampled, and are a pure function of the value. *)
  let s = Relation.stats r in
  check_eq_int "exact cardinality" ~expect:200 s.card;
  check_eq_int "exact distinct domain" ~expect:20 s.domain_size;
  check_eq_int "exact distinct range" ~expect:200 s.range_size;
  check_eq_int "exact max fan-out" ~expect:10 s.max_fanout

(* ------------------------------------------------------------------ *)
(* M3 — transitive closure                                             *)
(* ------------------------------------------------------------------ *)

(* The reference: iterate to a fixpoint recomposing everything each round. *)
let naive_plus r =
  let rec go acc =
    let next = Relation.union acc (Relation.compose acc r) in
    if Relation.equal next acc then acc else go next
  in
  go r

let test_closure () =
  section "M3: transitive closure";
  let chain n = Relation.of_list (List.init n ~f:(fun i -> (i, i + 1))) in
  let c = chain 30 in
  check "semi-naive agrees with the naive fixpoint" (Relation.equal (Relation.plus c) (naive_plus c));
  check_eq_int
    "a 30-link chain has n(n+1)/2 reachable pairs"
    ~expect:(30 * 31 / 2)
    (Relation.card (Relation.plus c));

  (* A cycle: the closure must terminate and be total on the cycle. *)
  let cyc = Relation.of_list (List.init 10 ~f:(fun i -> (i, (i + 1) % 10))) in
  check_eq_int "closure of a 10-cycle is complete" ~expect:100 (Relation.card (Relation.plus cyc));

  (* Semi-naive is meant to be cheaper, not merely equal. Measure it. *)
  Relation.reset_counters ();
  ignore (Relation.plus c : (int, int) Relation.t);
  let semi = Relation.tuples_touched () in
  Relation.reset_counters ();
  ignore (naive_plus c : (int, int) Relation.t);
  let naive = Relation.tuples_touched () in
  printf "   semi-naive touched %d tuples, naive %d (%.1fx)\n" semi naive
    (Float.of_int naive /. Float.of_int semi);
  check "semi-naive does strictly less work than the naive fixpoint" (semi < naive);

  let star = Relation.star_on_carrier c in
  check "star contains plus" (Relation.subset (Relation.plus c) star);
  check_eq_int
    "star adds exactly the diagonal on the carrier"
    ~expect:(Relation.card (Relation.plus c) + 31)
    (Relation.card star)

(* ------------------------------------------------------------------ *)
(* M1 — the scalar language and the two-layer bridge                   *)
(* ------------------------------------------------------------------ *)

let test_scalar () =
  section "M1: scalars, coreflexives, and reading a predicate back";
  let people = [ (1, 34); (2, 41); (3, 19); (4, 67) ] in
  let module Q (R : Algebra.RELATIONS) = struct
    open R
    open R.V

    let over_40 = of_list people >> where_ (fun age -> age >. int_ 40)
  end in
  let module E = Q (Eval) in
  let module S = Q (Symbolic) in
  check "filtering is composition with a coreflexive, and needs no combinator"
    (Poly.equal [ (2, 41); (4, 67) ] (Eval.to_list E.over_40));
  check "the same program evaluates the same way through the symbolic tree"
    (Relation.equal (Eval.to_relation E.over_40) (Symbolic.run S.over_40));
  let printed = Symbolic.to_string S.over_40 in
  printf "   symbolic: %s\n" printed;
  check "the predicate's structure is recovered, not lost in a closure"
    (String.is_substring printed ~substring:"(x > 40)");
  check "and the program is free of holes in the cost model"
    (not (Symbolic.has_opaque S.over_40));

  (* The escape hatch is visible, which is the whole point of having it. *)
  let module Q2 (R : Algebra.RELATIONS) = struct
    open R

    let odd_ages = of_list people >> where_ (fun age -> R.V.opaque ~name:"odd" (fun n -> n % 2 = 1) age)
  end in
  let module S2 = Q2 (Symbolic) in
  let module E2 = Q2 (Eval) in
  check "an opaque predicate still runs" ([ (1, 34); (2, 41); (3, 19); (4, 67) ] |> List.filter ~f:(fun (_, a) -> a % 2 = 1) |> List.equal Poly.equal (Eval.to_list E2.odd_ages));
  check "and it is visible in the plan" (Symbolic.has_opaque S2.odd_ages);
  check "and it names itself when printed"
    (String.is_substring (Symbolic.to_string S2.odd_ages) ~substring:"opaque:odd")

(* ------------------------------------------------------------------ *)
(* The unbounded cases                                                 *)
(* ------------------------------------------------------------------ *)

let raises_unbounded f =
  match f () with
  | exception Eval.Unbounded _ -> true
  | _ -> false

let test_unbounded () =
  section "Unbounded values are refused by name, not silently mishandled";
  check "converse of a function graph is refused"
    (raises_unbounded (fun () -> Eval.to_list (Eval.converse (Eval.fn Int.succ))));
  check "join with an unbounded relation is refused"
    (raises_unbounded (fun () -> Eval.to_list (Eval.join Eval.id (Eval.of_list [ (1, 1) ]))));
  check "a function graph on the left of a finite relation is refused"
    (raises_unbounded (fun () -> Eval.to_list (Eval.( >> ) (Eval.fn Int.succ) (Eval.of_list [ (1, 2) ]))));
  (* ... and materialising on a carrier is the way through. *)
  let f = Eval.materialise ~dom:[ 1; 2; 3 ] (Eval.fn (fun x -> x * 10)) in
  check "materialise on a carrier makes it an ordinary relation"
    (Poly.equal [ (10, 1); (20, 2); (30, 3) ] (Eval.to_list (Eval.converse f)));
  check "join with bot is fine even unbounded" (Poly.equal (Eval.to_list (Eval.join Eval.bot (Eval.of_list [ (1, 1) ]))) [ (1, 1) ])

(* ------------------------------------------------------------------ *)
(* M5 — the planner                                                    *)
(* ------------------------------------------------------------------ *)

(* Built fresh each time so that no index survives from a previous
   measurement: comparing two plans is only fair if both start cold. *)
let three_relations () =
  let a = Relation.of_list (List.init 500 ~f:(fun i -> (i, i))) in
  let b = Relation.of_list (List.init 500 ~f:(fun i -> (i, i + 1))) in
  let c = Relation.of_list [ (300, 0) ] in
  (a, b, c)

let test_planner () =
  section "M5: planning on exact statistics";
  let a, b, c = three_relations () in
  let written = Symbolic.(of_relation a >> of_relation b >> of_relation c) in
  print_endline (Plan.explain written);

  (* Correctness first: an optimiser that is fast and wrong is worse than
     none. Same relations, both plans, results compared. *)
  let planned = Plan.optimise written in
  check "the planned tree computes the same relation"
    (Relation.equal (Symbolic.run written) (Symbolic.run planned));

  (* Then the measurement, and the fair version of it took a correction worth
     recording. Statistics are exact and never stale, but they are not free:
     [Relation.stats] forces both indexes, so planning a three-leaf chain cold
     costs six index builds. Charging that to the planned run and not to the
     unplanned one made the plan look slower than the order written.

     The honest comparison gives both sides the same information — the indexes
     get built either way, because execution needs them too — and measures
     what the plan actually controls, which is execution. The one-time cost of
     knowing the statistics is reported separately below rather than hidden. *)
  let run_chain ~planned =
    let a, b, c = three_relations () in
    let t = Symbolic.(of_relation a >> of_relation b >> of_relation c) in
    let t = if planned then Plan.optimise t else t in
    let info_cost =
      Relation.reset_counters ();
      List.iter [ Relation.stats a; Relation.stats b; Relation.stats c ] ~f:(fun (_ : Relation.stats) -> ());
      Relation.tuples_touched ()
    in
    Relation.reset_counters ();
    let r = Symbolic.run t in
    (r, Relation.tuples_touched (), info_cost)
  in
  let res_w, cost_written, info_w = run_chain ~planned:false in
  let res_p, cost_planned, _ = run_chain ~planned:true in
  printf "   statistics for three relations cost %d tuples, once per value\n" info_w;
  printf "   execution: as written %d tuples, planned %d (%.0fx)\n" cost_written cost_planned
    (Float.of_int cost_written /. Float.of_int (Int.max 1 cost_planned));
  check "the plan touches strictly fewer tuples than the order written"
    (cost_planned < cost_written);
  check "and both orders compute the same relation" (Relation.equal res_w res_p);

  (* Pushing converse to the leaves: at a leaf it is free, because the index
     is already there. *)
  let a, b, _ = three_relations () in
  let conv_written = Symbolic.(converse (of_relation a >> of_relation b)) in
  let conv_planned = Plan.optimise conv_written in
  check "converse is pushed down to the leaves"
    (String.equal (Symbolic.to_string conv_planned) "(«500» >> «500»)");
  check "and it still computes the same relation"
    (Relation.equal (Symbolic.run conv_written) (Symbolic.run conv_planned));

  (* Simplification of units and absorbing elements. *)
  check "id is eliminated"
    (String.equal Symbolic.(to_string (Plan.optimise (id >> of_relation a >> id))) "«500»");
  check "bot absorbs" (String.equal Symbolic.(to_string (Plan.optimise (of_relation a >> bot))) "bot");

  (* And the honest part: the planner declines to reorder across something it
     cannot cost, and says so. *)
  let module Q (R : Algebra.RELATIONS) = struct
    open R

    let q =
      of_relation a
      >> where_ (fun x -> R.V.opaque ~name:"business_rule" (fun n -> n % 7 = 0) x)
      >> of_relation b
  end in
  let module S = Q (Symbolic) in
  let spots = Plan.blind_spots S.q in
  printf "   blind spots: %s\n" (String.concat ~sep:"; " spots);
  check "an opaque predicate is reported as a hole in the cost model"
    (List.exists spots ~f:(fun s -> String.is_substring s ~substring:"opaque"));
  check "and the barrier does not stop the program from running"
    (Relation.equal
       (Symbolic.run S.q)
       (Symbolic.run (Plan.optimise S.q)))

(* ------------------------------------------------------------------ *)
(* M4 — the same program as a self-adjusting graph                     *)
(* ------------------------------------------------------------------ *)

(* Written once, against the signature. Nothing in it knows whether it will
   be run to a set of pairs or compiled into an Incremental graph. *)
module Reachable_in_three (R : Algebra.RELATIONS) = struct
  open R

  let q ~a ~b ~c = a >> b >> c
end

let test_incremental () =
  section "M4: one program, run one-shot and as a live self-adjusting graph";
  let module QE = Reachable_in_three (Eval) in
  let module QI = Reachable_in_three (Incr) in
  let b = Relation.of_list (List.init 500 ~f:(fun i -> (i, i + 1))) in
  let c = Relation.of_list (List.init 500 ~f:(fun i -> (i + 1, i * 2))) in
  let a0 = Relation.of_list (List.init 500 ~f:(fun i -> (i, i))) in
  let one_shot a =
    Eval.to_relation
      (QE.q ~a:(Eval.of_relation a) ~b:(Eval.of_relation b) ~c:(Eval.of_relation c))
  in
  let va = Incr.Var.create a0 in
  let obs =
    Incr.observe (QI.q ~a:(Incr.Var.watch va) ~b:(Incr.of_relation b) ~c:(Incr.of_relation c))
  in
  Incr.stabilize ();
  check "the graph agrees with the one-shot evaluator"
    (Relation.equal (Incr.Observer.value obs) (one_shot a0));

  (* A stabilize with nothing changed must do nothing at all. *)
  Relation.reset_counters ();
  Incr.stabilize ();
  check_eq_int "an unchanged stabilize does no work" ~expect:0 (Relation.tuples_touched ());

  (* One tuple inserted. Built by union so that the new value shares structure
     with the old one — which is what makes the diff cheap, and is only
     possible because relations are immutable. *)
  let a1 = Relation.union a0 (Relation.singleton 700 5) in
  Relation.reset_counters ();
  Incr.Var.set va a1;
  Incr.stabilize ();
  let incremental_cost = Relation.tuples_touched () in
  Relation.reset_counters ();
  let from_scratch = one_shot a1 in
  let full_cost = Relation.tuples_touched () in
  check "the incremental result is the right one"
    (Relation.equal (Incr.Observer.value obs) from_scratch);
  printf "   after inserting one tuple: incremental %d tuples, from scratch %d (%.0fx)\n"
    incremental_cost full_cost
    (Float.of_int full_cost /. Float.of_int (Int.max 1 incremental_cost));
  check "maintaining the view is cheaper than recomputing it"
    (incremental_cost < full_cost);

  (* Changing the leaf nearest the root must not recompute the subtree that
     did not change. Both ends are variables here so that [a >> b] is a real
     node in the graph rather than a constant folded at construction time.

     The first such update is not cheap, and the reason is worth stating
     rather than hiding: composing the intermediate with a one-tuple delta
     probes the intermediate's backward index, which does not exist yet, so
     the update pays to build it. That is a one-off — it is an index, and an
     index of an immutable value is never rebuilt. The steady-state cost is
     what maintenance actually costs, so both are measured. *)
  let va2 = Incr.Var.create a0 in
  let vc = Incr.Var.create c in
  let obs2 = Incr.observe (QI.q ~a:(Incr.Var.watch va2) ~b:(Incr.of_relation b) ~c:(Incr.Var.watch vc)) in
  Incr.stabilize ();
  let c1 = Relation.union c (Relation.singleton 1 999) in
  Relation.reset_counters ();
  Incr.Var.set vc c1;
  Incr.stabilize ();
  let first_update = Relation.tuples_touched () in
  let c2 = Relation.union c1 (Relation.singleton 2 998) in
  Relation.reset_counters ();
  Incr.Var.set vc c2;
  Incr.stabilize ();
  let steady_update = Relation.tuples_touched () in
  printf
    "   changing the last leaf: first update %d tuples (builds an index on the intermediate), \
     then %d\n"
    first_update steady_update;
  check "in the steady state the unchanged sibling subtree costs nothing" (steady_update < 100);
  check "and the answer is still right"
    (Relation.equal
       (Incr.Observer.value obs2)
       (Eval.to_relation
          (QE.q ~a:(Eval.of_relation a0) ~b:(Eval.of_relation b) ~c:(Eval.of_relation c2))));

  (* Deletion is the case the delta path does not handle, because a pair may
     still be derivable another way. It must fall back and still be right —
     that is the part worth testing, since a wrong incremental view is far
     worse than a slow one. *)
  let a2 = Relation.diff a1 (Relation.singleton 300 300) in
  Incr.Var.set va a2;
  Incr.stabilize ();
  check "a deletion falls back to recomputation and stays correct"
    (Relation.equal (Incr.Observer.value obs) (one_shot a2));

  (* And a mixed change, which is where an insert-only shortcut taken by
     mistake would show up. *)
  let a3 = Relation.union (Relation.diff a2 (Relation.singleton 100 100)) (Relation.singleton 42 7) in
  Incr.Var.set va a3;
  Incr.stabilize ();
  check "an insert and a delete together stay correct"
    (Relation.equal (Incr.Observer.value obs) (one_shot a3))

(* ------------------------------------------------------------------ *)
(* Trying to break it                                                  *)
(* ------------------------------------------------------------------ *)

(* Everything above this point tests a case I chose, which means it shares
   every assumption the implementation does and can only agree with me. The
   two things most worth attacking are the two whose failure mode is a wrong
   answer rather than a slow one: the optimiser and the incremental view. *)

let rng = Random.State.make [| 20260801 |]

let random_relation ~elems ~size =
  Relation.of_list
    (List.init (Random.State.int rng size + 1) ~f:(fun _ ->
       (Random.State.int rng elems, Random.State.int rng elems)))

(* Random well-typed expression trees over (int, int). Every constructor here
   keeps the value finite, so [Eval] can compare results; the unbounded cases
   are covered separately above. *)
let rec random_tree depth : (int, int) Symbolic.t =
  let leaf () = Symbolic.of_relation (random_relation ~elems:8 ~size:10) in
  if depth <= 0 then leaf ()
  else
    let sub () = random_tree (depth - 1) in
    match Random.State.int rng 9 with
    | 0 | 1 | 2 -> Symbolic.( >> ) (sub ()) (sub ())
    | 3 -> Symbolic.converse (sub ())
    | 4 -> Symbolic.meet (sub ()) (sub ())
    | 5 -> Symbolic.join (sub ()) (sub ())
    | 6 -> Symbolic.plus (sub ())
    | 7 -> Symbolic.star (sub ())
    | _ ->
      (* a filter, which is a barrier the planner must not reorder across *)
      let threshold = Random.State.int rng 8 in
      Symbolic.( >> ) (sub ()) (Symbolic.where_ (fun x -> Symbolic.V.( >. ) x (Symbolic.V.int_ threshold)))

let test_optimiser_is_sound () =
  section "Adversarial: does the optimiser ever change the answer?";
  let mismatches = ref 0 in
  let rewritten = ref 0 in
  let trees = 400 in
  for _ = 1 to trees do
    let t = random_tree 4 in
    let planned = Plan.optimise t in
    if not (String.equal (Symbolic.to_string t) (Symbolic.to_string planned)) then incr rewritten;
    let before = Symbolic.run t in
    let after = Symbolic.run planned in
    if not (Relation.equal before after) then (
      incr mismatches;
      if !mismatches <= 3 then
        printf "   MISMATCH\n     %s\n     %s\n" (Symbolic.to_string t)
          (Symbolic.to_string (Plan.optimise t)))
  done;
  printf "   %d random expression trees, of which the planner rewrote %d\n" trees !rewritten;
  check_eq_int "the optimiser never changed a result" ~expect:0 !mismatches;
  (* Without this the test above could pass by the planner doing nothing. *)
  check "and the test is not vacuous: most trees were actually rewritten"
    (!rewritten * 2 > trees)

(* A mutation that shares structure with what it came from, which is the
   realistic case and the one the delta path is tuned for. *)
let mutate r ~elems =
  let adds =
    Relation.of_list
      (List.init (Random.State.int rng 3) ~f:(fun _ ->
         (Random.State.int rng elems, Random.State.int rng elems)))
  in
  let existing = Relation.to_list r in
  let dels =
    if List.is_empty existing || Random.State.int rng 2 = 0 then Relation.empty
    else
      Relation.of_list
        (List.init (Random.State.int rng 3) ~f:(fun _ ->
           List.nth_exn existing (Random.State.int rng (List.length existing))))
  in
  Relation.union (Relation.diff r dels) adds

let test_incremental_is_sound () =
  section "Adversarial: does the incremental view ever drift from the truth?";
  let module Q (R : Algebra.RELATIONS) = struct
    open R

    let q ~a ~b ~c = (a >> b) >> c
  end in
  let module QE = Q (Eval) in
  let module QI = Q (Incr) in
  let a0 = random_relation ~elems:10 ~size:15 in
  let b0 = random_relation ~elems:10 ~size:15 in
  let c0 = random_relation ~elems:10 ~size:15 in
  let va = Incr.Var.create a0 and vb = Incr.Var.create b0 and vc = Incr.Var.create c0 in
  let obs =
    Incr.observe (QI.q ~a:(Incr.Var.watch va) ~b:(Incr.Var.watch vb) ~c:(Incr.Var.watch vc))
  in
  let a = ref a0 and b = ref b0 and c = ref c0 in
  let drifted = ref 0 in
  let rounds = 300 in
  Incr.stabilize ();
  Incr.reset_counters ();
  for _ = 1 to rounds do
    (* Change one input, sometimes two, by inserting and deleting at once. *)
    (match Random.State.int rng 3 with
    | 0 ->
      a := mutate !a ~elems:10;
      Incr.Var.set va !a
    | 1 ->
      b := mutate !b ~elems:10;
      Incr.Var.set vb !b
    | _ ->
      c := mutate !c ~elems:10;
      Incr.Var.set vc !c);
    Incr.stabilize ();
    let truth =
      Eval.to_relation
        (QE.q ~a:(Eval.of_relation !a) ~b:(Eval.of_relation !b) ~c:(Eval.of_relation !c))
    in
    if not (Relation.equal (Incr.Observer.value obs) truth) then incr drifted
  done;
  printf
    "   %d rounds of insert-and-delete against a from-scratch recomputation\n\
    \   composition nodes: %d maintained by delta, %d fell back to recomputing\n"
    rounds (Incr.delta_updates ()) (Incr.full_recomputes ());
  check_eq_int "the maintained view never drifted" ~expect:0 !drifted;
  (* And the delta path was genuinely exercised: a node that quietly
     recomputed every time would pass the check above and mean nothing. *)
  check "the delta path was taken, not merely available" (Incr.delta_updates () > rounds / 4)

(* The planner is only allowed to be wrong about cost, never about meaning.
   Its estimate should at least be in the right order of magnitude for a plan
   it can see all the way through, or the DP is optimising noise. *)
let test_estimate_is_calibrated () =
  section "Adversarial: is the cost estimate anywhere near the measurement?";
  let a = Relation.of_list (List.init 400 ~f:(fun i -> (i, i % 40))) in
  let b = Relation.of_list (List.init 400 ~f:(fun i -> (i % 40, i))) in
  let t = Symbolic.(of_relation a >> of_relation b) in
  let predicted = Plan.estimated_cost t in
  ignore (Relation.stats a : Relation.stats);
  ignore (Relation.stats b : Relation.stats);
  Relation.reset_counters ();
  ignore (Symbolic.run t : (int, int) Relation.t);
  let actual = Relation.tuples_touched () in
  printf "   predicted %.0f tuples, measured %d\n" predicted actual;
  check "the estimate is within an order of magnitude of the measurement"
    (Float.( > ) predicted (Float.of_int actual /. 10.)
    && Float.( < ) predicted (Float.of_int actual *. 10.))

(* ------------------------------------------------------------------ *)

let () =
  test_laws ();
  test_indexes ();
  test_scalar ();
  test_closure ();
  test_unbounded ();
  test_planner ();
  test_incremental ();
  test_optimiser_is_sound ();
  test_incremental_is_sound ();
  test_estimate_is_calibrated ();
  printf "\n%d checks, %d failures\n" !checks !failures;
  if !failures > 0 then exit 1
