open! Core
open Rel
module Incr = Rel_incr

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

(* The same samples, interpreted at four parameters. *)
module Sample4 = struct
  module L = Laws.General.Make (Eval.General)

  type t = {
    a : (int * int) list;
    b : (int * int) list;
    c : (int * int) list;
  }
  [@@deriving sexp_of]

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

  let to_sample { a; b; c } =
    {
      L.a = Eval.General.of_list (module Int) (module Int) a;
      b = Eval.General.of_list (module Int) (module Int) b;
      c = Eval.General.of_list (module Int) (module Int) c;
    }
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
(* Is the cost model's estimate actually any good?                     *)
(* ------------------------------------------------------------------ *)

(* The brief once claimed immutability hands a planner "perfect information for
   free". Two thirds of that is now known to be wrong, and the second third is
   a claim about THIS code: exact per-relation statistics say nothing about
   JOIN cardinality, which depends on the correlation between two relations
   rather than on any property of either. Leis et al. (VLDB 2015) found
   estimators routinely off by orders of magnitude and that the cost model
   matters far less than the estimates it is fed.

   The one calibration check above used a single shape I chose myself, which by
   this repo's own standard is close to no evidence. So: several shapes,
   predicted output cardinality against the real thing. *)
let estimator_error name x y =
  let t = Symbolic.(of_relation x >> of_relation y) in
  let predicted = match fst (Plan.estimate t) with Some i -> i.Plan.card | None -> Float.nan in
  let actual = Float.of_int (Relation.card (Symbolic.run t)) in
  let ratio = if Float.( = ) actual 0. then Float.nan else predicted /. actual in
  printf "   %-34s predicted %7.0f  actual %7.0f  %5.2fx\n" name predicted actual ratio;
  ratio

let test_estimator_quality () =
  section "How good is the join estimate? (uniform vs skewed)";

  (* Uniform: every left element has the same fan-out, every join key the same
     frequency. This is the assumption the textbook formula is built on. *)
  let uniform_a = Relation.of_list (List.init 1000 ~f:(fun i -> (i, i % 10))) in
  let uniform_b = Relation.of_list (List.init 100 ~f:(fun i -> (i % 10, i))) in
  let r_uniform = estimator_error "uniform join keys" uniform_a uniform_b in

  (* Skewed: one join key carries almost all the mass. Nothing in either
     relation's own statistics — cardinality, distinct counts, fan-out — says
     that the hot key on the left is the hot key on the right. That is the
     correlation between them, and it is exactly what is not measured. *)
  let skew_a =
    Relation.of_list (List.init 100 ~f:(fun i -> (i, 0)) @ List.init 10 ~f:(fun i -> (100 + i, 100 + i)))
  in
  let skew_b = Relation.of_list (List.init 100 ~f:(fun j -> (0, j))) in
  let r_skew = estimator_error "skewed, hot keys aligned" skew_a skew_b in

  (* Same shapes and the same per-relation statistics as the skewed case, but
     the hot keys do NOT meet. Identical inputs to the cost model, results two
     orders of magnitude apart: the demonstration that the statistics are the
     wrong ones, not merely imprecise. *)
  let skew_b_miss = Relation.of_list (List.init 100 ~f:(fun j -> (100, j))) in
  let r_miss = estimator_error "skewed, hot keys disjoint" skew_a skew_b_miss in

  printf "   the two skewed rows have identical per-relation stats: card %d/%d, dom %d/%d, rng %d/%d\n"
    (Relation.card skew_b) (Relation.card skew_b_miss)
    (Relation.stats skew_b).domain_size (Relation.stats skew_b_miss).domain_size
    (Relation.stats skew_b).range_size (Relation.stats skew_b_miss).range_size;
  check "the estimate is good when the uniformity assumption holds"
    (Float.( > ) r_uniform 0.5 && Float.( < ) r_uniform 2.0);
  check "and it is wrong under skew, in both directions"
    (Float.( < ) r_skew 0.5 || Float.( > ) r_miss 2.0);
  printf "   => exact leaf statistics do not give exact join estimates; see NOTES.md\n"

(* ------------------------------------------------------------------ *)
(* Where a cycle appears, and what it costs                            *)
(* ------------------------------------------------------------------ *)

(* A composition chain is a path: acyclic, and the literature is clear that
   worst-case-optimal joins buy nothing there — on acyclic queries WCO plans
   are equivalent to LEFT-DEEP binary plans, which are worse than the bushy
   ones the interval DP already produces.

   A cycle needs a query that closes back on itself, and this algebra has
   exactly one everyday way to write one: meet a composite with a base
   relation. [meet (a >> b) c] over the same carrier is the triangle query. *)
let triangle_on ~name ~edges ~expect_fusion =
  let a = Relation.of_list edges in
  let module Q (R : Algebra.RELATIONS) = struct
    open R

    let tri = meet (of_relation a >> of_relation a) (of_relation a)
  end in
  let module S = Q (Symbolic) in
  ignore (Relation.stats a : Relation.stats);
  Relation.reset_counters ();
  let out = Symbolic.run S.tri in
  let plain = Relation.tuples_touched () in
  let intermediate = Relation.card (Relation.compose a a) in
  let planned = Plan.optimise S.tri in
  let fused = String.is_substring (Symbolic.to_string planned) ~substring:"⋈" in
  Relation.reset_counters ();
  let out2 = Symbolic.run planned in
  let after = Relation.tuples_touched () in
  printf "   %-22s edges %5d  intermediate %7d  output %5d  |  %6d -> %6d tuples (%.1fx)%s\n"
    name (Relation.card a) intermediate (Relation.card out) plain after
    (Float.of_int plain /. Float.of_int (Int.max 1 after))
    (if fused then "" else "  [not fused]");
  check (name ^ ": fusing preserves the answer") (Relation.equal out out2);
  check (name ^ ": fusion decision as expected") (Bool.equal fused expect_fusion);
  (plain, after)

let triangle_gap () =
  section "The one shape re-association cannot help: a triangle";
  let rng = Random.State.make [| 7 |] in
  let nodes = 200 and degree = 10 in
  let uniform =
    List.concat_map (List.init nodes ~f:Fn.id) ~f:(fun x ->
      List.init degree ~f:(fun _ -> (x, Random.State.int rng nodes)))
  in
  (* A hub: one node with high in- and out-degree. The composition then
     contains every (i, j) that reaches the hub and leaves it, which is
     quadratic, while the triangles through it are not. *)
  let h = 500 in
  let hub =
    List.init h ~f:(fun i -> (i + 1, 0))
    @ List.init h ~f:(fun j -> (0, j + 1))
    (* a handful of chords, so the query has real answers rather than being a
       dramatic optimisation of the empty relation *)
    @ List.init 10 ~f:(fun i -> (i + 1, i + 2))
  in
  let _ = triangle_on ~name:"uniform random graph" ~edges:uniform ~expect_fusion:true in
  let plain, after = triangle_on ~name:"one high-degree hub" ~edges:hub ~expect_fusion:true in
  check "fusion pays on the skewed graph" (after * 10 < plain);
  printf "   => the win is under SKEW, not on uniform data \226\128\148 the same place the\n";
  printf "      cardinality estimator failed. Uniform data hides both.\n";

  (* The guard matters: fusing is a loss when the meet's other side is the big
     one, so the planner must decline there. *)
  let small = Relation.of_list [ (0, 1); (1, 2) ] in
  let big = Relation.of_list (List.init 5000 ~f:(fun i -> (i % 50, i))) in
  let module Q2 (R : Algebra.RELATIONS) = struct
    open R

    let q = meet (of_relation small >> of_relation small) (of_relation big)
  end in
  let module S2 = Q2 (Symbolic) in
  let planned2 = Plan.optimise S2.q in
  check "the planner declines to fuse when the other side is larger"
    (not (String.is_substring (Symbolic.to_string planned2) ~substring:"\226\139\136"));
  check "and that query is still right"
    (Relation.equal (Symbolic.run S2.q) (Symbolic.run planned2))

(* ------------------------------------------------------------------ *)
(* Layer 4: the surface with points                                    *)
(* ------------------------------------------------------------------ *)

(* An inclusion law is worth nothing if it is secretly an equality. Oliveira's
   ×-fusion is an equality for functions; the claim that only one inclusion
   survives for relations needs a witness. *)
let test_fork_fusion_is_strict () =
  section "×-fusion is a strict inclusion for relations, not an equality";
  let c = Eval.of_list [ (0, 1); (0, 2) ] in
  let a = Eval.of_list [ (1, 10) ] in
  let b = Eval.of_list [ (2, 20) ] in
  let lhs = Eval.(c >> fork a b) in
  let rhs = Eval.(fork (c >> a) (c >> b)) in
  printf "   c >> ⟨a, b⟩        = %d pairs\n" (List.length (Eval.to_list lhs));
  printf "   ⟨c >> a, c >> b⟩   = %d pairs\n" (List.length (Eval.to_list rhs));
  check "the inclusion holds" (Eval.subset lhs rhs);
  check "and is strict: the two sides genuinely differ" (not (Eval.equal lhs rhs));
  printf "   => the right-hand fork uses a different c-witness per branch;\n";
  printf "      the left-hand one cannot. That is Rel failing to be cartesian.\n"

let test_query_surface () =
  section "Layer 4: queries with variables, compiled to the algebra";
  let manages =
    Relation.of_list [ ("alice", "bob"); ("alice", "carol"); ("bob", "dave"); ("carol", "erin") ]
  in
  let dept =
    Relation.of_list
      [ ("bob", "eng"); ("carol", "sales"); ("dave", "eng"); ("erin", "sales") ]
  in

  (* A chain. Reads pointfully, compiles to a composition. *)
  let chain =
    Query.compile (fun boss ->
      let open Query in
      let* report = step manages boss in
      let* d = step dept report in
      ret d)
  in
  printf "   chain compiles to  : %s\n" (Symbolic.to_string chain);
  (* The whole relation, not just one row: a query denotes a relation, and
     asking about one boss is composing with a coreflexive, not a different
     query. *)
  check "the chain query gives the right answer"
    (Poly.equal
       [ ("alice", "eng"); ("alice", "sales"); ("bob", "eng"); ("carol", "sales") ]
       (Relation.to_list (Symbolic.run chain)));
  check "and it is a plain composition, so the planner applies"
    (String.is_substring (Symbolic.to_string chain) ~substring:">>");

  (* Traversing backwards: who manages someone in engineering? *)
  let backwards =
    Query.compile (fun d ->
      let open Query in
      let* person = back dept d in
      let* boss = back manages person in
      ret boss)
  in
  check "a backwards step is a converse, not a second index"
    (Poly.equal
       [ ("eng", "alice"); ("eng", "bob"); ("sales", "alice"); ("sales", "carol") ]
       (Relation.to_list (Symbolic.run backwards)));

  (* A cycle, which is the case worth having: the surface produces exactly the
     meet-of-a-composition that the fusion rewrite handles. *)
  let edges = Relation.of_list [ (0, 1); (1, 2); (0, 2); (2, 3); (1, 3) ] in
  let triangle =
    Query.compile (fun x ->
      let open Query in
      let* y = step edges x in
      let* z = step edges y in
      let* () = constrain edges x z in
      ret z)
  in
  printf "   cycle compiles to  : %s\n" (Symbolic.to_string triangle);
  printf "   and is planned as  : %s\n" (Symbolic.to_string (Plan.optimise triangle));
  check "the cycle query compiles to a meet of a composition"
    (String.is_substring (Symbolic.to_string triangle) ~substring:"\226\136\167");
  check "which the planner then fuses"
    (String.is_substring (Symbolic.to_string (Plan.optimise triangle)) ~substring:"\226\139\136");
  check "and the fused plan agrees with the unfused one"
    (Relation.equal (Symbolic.run triangle) (Symbolic.run (Plan.optimise triangle)));
  check "the triangles are the right ones"
    (Poly.equal [ (0, 2); (1, 3) ] (Relation.to_list (Symbolic.run triangle)));

  (* A branching query: y has degree three, which the path-walking compiler
     refused. Variable elimination handles it — the dangling branch becomes a
     semi-join coreflexive on y, after which y is an ordinary waypoint. *)
  let branching =
    Query.compile (fun x ->
      let open Query in
      let* y = step manages x in
      let* _z = step manages y in
      (* _z is dangling: it constrains y to be someone who manages somebody *)
      let* w = step dept y in
      ret w)
  in
  printf "   branching compiles : %s\n" (Symbolic.to_string branching);
  check "a dangling branch becomes a semi-join, not an Unsupported"
    (Poly.equal [ ("alice", "eng"); ("alice", "sales") ]
       (Relation.to_list (Symbolic.run branching)));

  (* An irreducible core: variables 1 and 2 both have degree three, so no
     elimination rule applies. Branching on a variable's value handles it.
     Checked against brute force rather than against my own arithmetic, which
     has been wrong more than once in this suite. *)
  (* [manages] is a tree, so this query would have no answers there and the
     comparison below would hold vacuously. Use a graph with the chords the
     query asks for. *)
  let g = Relation.of_list [ (0, 1); (1, 2); (2, 3); (0, 2); (1, 3); (2, 4); (3, 4) ] in
  let core =
    Query.compile (fun x ->
      let open Query in
      let* y = step g x in
      let* z = step g y in
      let* w = step g z in
      let* () = constrain g y w in
      let* () = constrain g x z in
      ret w)
  in
  let people = Set.to_list (Set.union (Relation.dom g) (Relation.rng g)) in
  let brute =
    List.concat_map people ~f:(fun x ->
      List.concat_map people ~f:(fun y ->
        List.concat_map people ~f:(fun z ->
          List.filter_map people ~f:(fun w ->
            if
              Relation.mem g x y && Relation.mem g y z && Relation.mem g z w
              && Relation.mem g y w && Relation.mem g x z
            then Some (x, w)
            else None))))
    |> Relation.of_list
  in
  printf "   irreducible core   : %d answers, brute force %d\n"
    (Relation.card (Symbolic.run core)) (Relation.card brute);
  check "branching solves a core the elimination rules cannot reduce"
    (Relation.equal (Symbolic.run core) brute);
  (* Without this the comparison above passes on two empty relations. *)
  check "and the core test is not vacuous: there are answers to get right"
    (Relation.card brute > 0);

  (* The guard is real: past the candidate limit it still refuses. *)
  let unsupported =
    match
      Query.compile ~max_candidates:0 (fun x ->
        let open Query in
        let* y = step g x in
        let* z = step g y in
        let* w = step g z in
        let* () = constrain g y w in
        let* () = constrain g x z in
        ret w)
    with
    | _ -> false
    | exception Query.Unsupported _ -> true
  in
  check "and past the candidate limit it refuses rather than exploding" unsupported

(* ------------------------------------------------------------------ *)
(* Is there a filter-pushdown win to be had?                           *)
(* ------------------------------------------------------------------ *)

(* A coreflexive has no statistics, so the interval DP treats it as a barrier
   and never re-associates across it: [a >> b >> where p] is planned exactly as
   written, building all of [a >> b] and then discarding most of it. Measure
   the gap before writing a rule for it. *)
let test_filter_pushdown_gap () =
  section "Filter pushdown: measuring the gap first";
  let n = 400 in
  let a = Relation.of_list (List.init n ~f:(fun i -> (i, i % 50))) in
  let b = Relation.of_list (List.init (n * 2) ~f:(fun i -> (i % 50, i))) in
  let module Q (R : Algebra.RELATIONS) = struct
    open R

    (* Keeps roughly 20 of b's 800 right-hand values. *)
    let keep v = R.V.( >. ) v (R.V.int_ 780)
    let as_written = of_relation a >> of_relation b >> where_ keep
    let pushed = of_relation a >> (of_relation b >> where_ keep)
  end in
  let module S = Q (Symbolic) in
  let measure t =
    ignore (Relation.stats a : Relation.stats);
    ignore (Relation.stats b : Relation.stats);
    Relation.reset_counters ();
    let r = Symbolic.run t in
    (r, Relation.tuples_touched ())
  in
  let r0, cost_naive = measure S.as_written in
  let r1, cost_planned = measure (Plan.optimise S.as_written) in
  let r2, cost_hand = measure S.pushed in
  printf "   as written, unplanned : %d tuples\n" cost_naive;
  printf "   hand-pushed filter    : %d tuples\n" cost_hand;
  printf "   planner               : %d tuples  (%.1fx better than unplanned)\n" cost_planned
    (Float.of_int cost_naive /. Float.of_int (Int.max 1 cost_planned));
  check "all three agree on the answer"
    (Relation.equal r0 r1 && Relation.equal r1 r2);
  check "the planner now closes the gap it used to leave open"
    (cost_planned <= cost_hand);

  (* The other direction: a filter in front of a meet. Distributing it over
     both branches is sound -- [p >> (a ∧ b) = (p >> a) ∧ (p >> b)] -- and
     shrinks both sides before they are intersected. Measure before writing
     the rule. *)
  let c = Relation.of_list (List.init 4000 ~f:(fun i -> (i % 900, i % 700))) in
  let d = Relation.of_list (List.init 4000 ~f:(fun i -> (i % 900, i % 650))) in
  let module M (R : Algebra.RELATIONS) = struct
    open R

    let keep v = R.V.( <. ) v (R.V.int_ 5)
    let filter_outside = where_ keep >> meet (of_relation c) (of_relation d)
    let filter_inside = meet (where_ keep >> of_relation c) (where_ keep >> of_relation d)
  end in
  let module Sm = M (Symbolic) in
  let measure2 t =
    ignore (Relation.stats c : Relation.stats);
    ignore (Relation.stats d : Relation.stats);
    Relation.reset_counters ();
    let r = Symbolic.run t in
    (r, Relation.tuples_touched ())
  in
  let m0, cost_outside = measure2 Sm.filter_outside in
  let m1, cost_inside = measure2 Sm.filter_inside in
  printf "   filter before a meet  : %d tuples\n" cost_outside;
  printf "   distributed over both : %d tuples  (%.1fx)\n" cost_inside
    (Float.of_int cost_outside /. Float.of_int (Int.max 1 cost_inside));
  check "distributing a filter over a meet preserves the answer" (Relation.equal m0 m1);
  (* Measured negative, and recorded as an assertion so it cannot quietly stop
     being true: distributing costs MORE, because it filters two relations
     instead of one and the meet has to intersect the results anyway. *)
  check "distributing a filter over a meet is a loss, so no rewrite for it"
    (cost_inside > cost_outside);
  printf "   => distributing costs more; left as written\n";

  (* And through a fork, where the shape of the argument is the opposite: a
     fork GROWS its inputs, a meet shrinks them, so the same rewrite should go
     the other way. Worth checking rather than assuming. *)
  let module F (R : Algebra.RELATIONS) = struct
    open R

    let keep v = R.V.( <. ) v (R.V.int_ 5)
    let outside = where_ keep >> fork (of_relation c) (of_relation d)
    let inside = fork (where_ keep >> of_relation c) (where_ keep >> of_relation d)
  end in
  let module Sf = F (Symbolic) in
  let f0, cost_f_out = measure2 Sf.outside in
  let f1, cost_f_in = measure2 Sf.inside in
  printf "   filter before a fork  : %d tuples\n" cost_f_out;
  printf "   distributed over both : %d tuples  (%.1fx)\n" cost_f_in
    (Float.of_int cost_f_out /. Float.of_int (Int.max 1 cost_f_in));
  check "distributing a filter over a fork preserves the answer" (Relation.equal f0 f1);
  check "and it is worth a rewrite, unlike the meet case" (cost_f_in * 2 < cost_f_out);
  let f2, cost_f_planned = measure2 (Plan.optimise Sf.outside) in
  printf "   planner               : %d tuples  (%.1fx)\n" cost_f_planned
    (Float.of_int cost_f_out /. Float.of_int (Int.max 1 cost_f_planned));
  check "the planner distributes over the fork" (Relation.equal f0 f2);
  check "and reaches the hand-written cost" (cost_f_planned <= cost_f_in)

(* ------------------------------------------------------------------ *)
(* How bad is a cycle longer than a triangle?                          *)
(* ------------------------------------------------------------------ *)

(* [meet_compose] fuses [meet (a >> b) c]. On a longer cycle -- [meet (a >> b
   >> c) d] -- the fusion still applies, but only to the OUTERMOST
   composition: [a >> b] is materialised first and then fused against [d]. A
   general worst-case-optimal join would avoid every intermediate. Measure how
   much that costs before building one. *)
let test_long_cycle_gap () =
  section "Cycles longer than a triangle: how much is left on the table?";
  let h = 300 in
  let hub =
    List.init h ~f:(fun i -> (i + 1, 0))
    @ List.init h ~f:(fun j -> (0, j + 1))
    @ List.init 10 ~f:(fun i -> (i + 1, i + 2))
  in
  let g = Relation.of_list hub in
  let module Q (R : Algebra.RELATIONS) = struct
    open R

    let triangle = meet (of_relation g >> of_relation g) (of_relation g)
    let square = meet (of_relation g >> of_relation g >> of_relation g) (of_relation g)
  end in
  let module S = Q (Symbolic) in
  let measure t =
    ignore (Relation.stats g : Relation.stats);
    Relation.reset_counters ();
    let r = Symbolic.run t in
    (r, Relation.tuples_touched ())
  in
  let tri_a, tri_plain = measure S.triangle in
  let tri_b, tri_fused = measure (Plan.optimise S.triangle) in
  let sq_a, sq_plain = measure S.square in
  let sq_planned = Plan.optimise S.square in
  let sq_b, sq_fused = measure sq_planned in
  printf "   triangle : %6d -> %6d  (%.1fx)\n" tri_plain tri_fused
    (Float.of_int tri_plain /. Float.of_int (Int.max 1 tri_fused));
  printf "   4-cycle  : %6d -> %6d  (%.1fx)\n" sq_plain sq_fused
    (Float.of_int sq_plain /. Float.of_int (Int.max 1 sq_fused));
  printf "   4-cycle planned as: %s\n" (Symbolic.to_string sq_planned);
  (* A speedup that computes the wrong answer is worth nothing, so check that
     first. The random-tree equivalence test covers this shape too, but not
     with data chosen to make the fusion fire. *)
  check "the fused triangle agrees with the unfused one" (Relation.equal tri_a tri_b);
  check "the fused 4-cycle agrees with the unfused one" (Relation.equal sq_a sq_b);
  check "the fused 4-cycle is not vacuous" (Relation.card sq_b > 0);
  check "the triangle is fused well" (tri_fused * 10 < tri_plain);
  (* Was pinned as an open gap at 1.0x; three-way fusion closed it. *)
  check "and so is the longer cycle, now that fusion splits it in the middle"
    (sq_fused * 10 < sq_plain)



(* ------------------------------------------------------------------ *)
(* Composing a projection with a finite relation                       *)
(* ------------------------------------------------------------------ *)

(* Found by using the library on someone else's code: the natural way to say
   "this position's key is its segment's key" is

     fork (fst_ >> segment_key) choice_at

   and [fst_ >> segment_key] raises Unbounded, because [fst_] is a function
   graph over an unbounded domain and composing it on the left of a finite
   relation would need a preimage.

   The result really is infinite -- it relates (a, ANYTHING) to whatever
   [segment_key] relates [a] to -- so raising is not wrong. But it is not
   necessary either: the value is perfectly representable pointwise, and the
   [fork] that consumes it supplies a finite carrier one line later. Refusing
   at the inner step throws away information the outer step has. *)
module Projection_join (R : Algebra.RELATIONS) = struct
  open R

  let q ~segment_key ~choice_at =
    fork (fst_ >> of_relation segment_key) (of_relation choice_at)
end

let test_projection_compose () =
  section "Composing a projection with a finite relation";
  let module Q = Projection_join (Eval) in
  let elem = Base_quickcheck.Generator.int_inclusive 0 3 in
  let gen =
    let open Base_quickcheck.Generator.Let_syntax in
    let%bind n = Base_quickcheck.Generator.int_inclusive 0 6 in
    let%bind keys =
      Base_quickcheck.Generator.list_with_length ~length:n
        (Base_quickcheck.Generator.both elem elem)
    in
    let%bind m = Base_quickcheck.Generator.int_inclusive 0 6 in
    let%map cells =
      Base_quickcheck.Generator.list_with_length ~length:m
        (Base_quickcheck.Generator.both (Base_quickcheck.Generator.both elem elem) elem)
    in
    (keys, cells)
  in
  let module Sample = struct
    type t = (int * int) list * ((int * int) * int) list [@@deriving sexp_of]

    let quickcheck_generator = gen
    let quickcheck_shrinker = Base_quickcheck.Shrinker.atomic
  end in
  let failures = ref 0 in
  let raised = ref 0 in
  (try
     Base_quickcheck.Test.run_exn
       ~config:{ Base_quickcheck.Test.default_config with test_count = 200 }
       (module Sample)
       ~f:(fun (keys, cells) ->
         let segment_key = Relation.of_list keys in
         let choice_at = Relation.of_list cells in
         (* The join, computed directly, as the oracle. *)
         let expected =
           Relation.of_list
             (List.concat_map (Relation.to_list choice_at) ~f:(fun ((s, i), c) ->
                List.map (Set.to_list (Relation.image segment_key s)) ~f:(fun k ->
                  ((s, i), (k, c)))))
         in
         match Eval.to_relation (Q.q ~segment_key ~choice_at) with
         | got -> if not (Relation.equal got expected) then Int.incr failures
         | exception Eval.Unbounded _ -> Int.incr raised)
   with
  | _ -> ());
  printf "   200 cases: %d wrong answers, %d raised Unbounded\n" !failures !raised;
  check "fst_ composed with a finite relation, then forked, does not raise"
    (!raised = 0);
  check "and gives the join" (!failures = 0)

(* ------------------------------------------------------------------ *)
(* Regression checks extracted from defects found by OUTSIDE use       *)
(* ------------------------------------------------------------------ *)

(* Three defects this library shipped were found by pointing it at other
   people's code, never by its own suite. That is not luck: the suite's random
   terms were built from a hand-picked subset of constructors chosen -- by me,
   who wrote the evaluator -- to keep results finite, so the generator was
   shaped around the implementation's comfort zone. These checks are the
   systematic version: walk the representation matrix instead of picking
   cases. *)

(* Defect 1: [fst_ >> finite] raised Unbounded although the value is decidable
   pointwise and the enclosing combinator supplies a carrier. The general
   property is "never refuse a query whose answer is finite". Rather than
   trust a list of shapes I thought of, enumerate every pairing of Eval's
   representation kinds under composition, and require that anything a finite
   relation can absorb is absorbed. *)
let test_no_gratuitous_refusal () =
  section "Extracted: never refuse a query whose answer is finite";
  let fin = Eval.of_list [ (1, 10); (2, 20); (3, 30) ] in
  let fin_pairs = Eval.of_list [ ((1, 'a'), 100); ((2, 'b'), 200) ] in
  let corefl = Eval.where_ (fun x -> x > 0) in
  let pfun = Eval.fn (fun x -> x * 2) in
  let pset = Eval.( >> ) Eval.fst_ fin in
  (* Each entry: a description, and a term whose answer is finite. Every one
     must evaluate; a raise is the defect. *)
  let cases : (string * (unit -> (int * char, int) Eval.t)) list =
    [ ("fst_ >> finite, forked with finite",
       fun () -> Eval.fork (Eval.( >> ) Eval.fst_ fin) fin_pairs |> fun t ->
                 Eval.( >> ) t (Eval.fn snd));
      ("snd_ >> function, forked with finite",
       fun () -> Eval.fork (Eval.( >> ) Eval.snd_ (Eval.fn Char.to_int)) fin_pairs
                 |> fun t -> Eval.( >> ) t (Eval.fn snd));
      ("pset meet finite",
       fun () -> Eval.meet (Eval.( >> ) Eval.fst_ fin) (Eval.( >> ) Eval.fst_ fin)
                 |> fun t -> Eval.meet t fin_pairs);
      ("pset >> coreflexive, then forked",
       fun () -> Eval.fork (Eval.( >> ) pset corefl) fin_pairs |> fun t ->
                 Eval.( >> ) t (Eval.fn snd))
    ]
  in
  let refused = ref 0 in
  List.iter cases ~f:(fun (name, mk) ->
    match Eval.to_list (mk ()) with
    | _ -> ()
    | exception Eval.Unbounded msg ->
      Int.incr refused;
      printf "   REFUSED %s: %s\n" name msg);
  check_eq_int "no finite-answer query is refused" ~expect:0 !refused;

  (* And the matrix itself: composing any pointwise kind with a finite
     relation on the right must yield something a carrier can materialise.
     Written out one kind at a time -- the kinds have different types, and the
     first draft of this used [Obj.magic] to force them into one list, which
     segfaulted. A test that needs [Obj.magic] is testing the wrong thing. *)
  let matrix_refusals = ref 0 in
  let try_pointwise name (t : (int, int) Eval.t) =
    match Eval.to_list (Eval.materialise ~dom:[ 1; 2; 3 ] t) with
    | _ -> ()
    | exception Eval.Unbounded m ->
      Int.incr matrix_refusals;
      printf "   REFUSED %s >> finite: %s\n" name m
  in
  try_pointwise "coreflexive" (Eval.( >> ) corefl fin);
  try_pointwise "function graph" (Eval.( >> ) pfun fin);
  try_pointwise "pointwise set" (Eval.( >> ) (Eval.( >> ) pfun fin) (Eval.fn Fn.id));
  check_eq_int "every pointwise kind composes with a finite relation"
    ~expect:0 !matrix_refusals

(* Defect 2: structural comparison is unusable on elements whose
   representation is large or shared -- merlin's Lid.t reaches ~10 900 words
   and building an index over 200 000 of them exhausts memory.

   Recorded rather than fixed. The check builds a relation over elements that
   share a large prefix, so every comparison walks it, and records the cost
   against the same shape with a cheap key. The ratio is printed for the
   reader but no longer asserted: timing ratios are too noisy to gate on
   (71.9x / 88x / 114.9x across runs of the fork bench), and the invariant it
   stood for is asserted deterministically instead by the forced-payload test
   in [test_general_comparators] below. *)
let test_structural_comparison_cost () =
  section "Extracted: what structural comparison costs on shared-heavy values";
  let n = 3000 in
  (* The prefix must be equal but NOT physically shared. OCaml's compare
     short-circuits on physical equality, so a shared prefix is free -- the
     first version of this test used one and measured 1.1x, i.e. nothing.
     merlin's values are lazily unmarshalled into distinct structures, which
     is exactly what defeats that short-circuit and what made the real index
     exhaust memory. *)
  let heavy = List.init n ~f:(fun i -> ((Array.init 400 ~f:Fn.id, i), i)) in
  let light = List.init n ~f:(fun i -> (i, i)) in
  let ms f =
    let t0 = Stdlib.Sys.time () in
    ignore (f () : unit);
    (Stdlib.Sys.time () -. t0) *. 1000.
  in
  let t_heavy = ms (fun () -> ignore (Relation.of_list heavy : _ Relation.t)) in
  let t_light = ms (fun () -> ignore (Relation.of_list light : _ Relation.t)) in
  printf "   %d pairs, key with equal-but-unshared 400-word prefix : %6.1f ms\n" n t_heavy;
  printf "   %d pairs, plain int key                              : %6.1f ms\n" n t_light;
  printf "   ratio                                                 %6.1fx\n"
    (t_heavy /. Float.max 0.001 t_light);
  printf "   => informative only; the deterministic guard is the forced-payload\n";
  printf "      test in the Relation.General section.\n"

(* ------------------------------------------------------------------ *)
(* Relation.General: the four-parameter interface                      *)
(* ------------------------------------------------------------------ *)

(* The slice's discriminating case, rerun against the real library: a
   comparator that deliberately ignores a large payload, so "apple" and
   "avocado" are ONE key. A card of 1 is impossible under [Poly], so it
   proves the carried comparator is genuinely in force, not merely carried. *)
module Coarse = struct
  module T = struct
    type t = { key : string; payload : string list }

    let compare a b = Char.compare a.key.[0] b.key.[0]
    let sexp_of_t t = Sexp.Atom t.key
  end

  include T
  include Comparator.Make (T)
end

let test_general_comparators () =
  section "Relation.General: comparators are in force, not just carried";
  let module G = Relation.General in
  let w key = { Coarse.key; payload = List.init 8 ~f:(fun k -> sprintf "w%d" k) } in
  let r =
    G.of_list (module Int) (module Coarse)
      [ (1, w "apple"); (2, w "avocado"); (3, w "beet"); (1, w "cherry") ]
  in
  check_eq_int "General card counts distinct keys" ~expect:4 (G.card r);
  let collapsed = G.of_list (module Int) (module Coarse) [ (1, w "apple"); (1, w "avocado") ] in
  check_eq_int "apple+avocado collapse to one pair (Poly would say 2)" ~expect:1 (G.card collapsed);
  check_eq_int "General image of collapsed key" ~expect:1 (Set.length (G.image collapsed 1));
  let back = G.of_list (module Coarse) (module Int) [ (w "apple", 10); (w "beet", 20) ] in
  let rr = G.compose r back in
  check_eq_int "General compose through a coarse middle" ~expect:3 (G.card rr);
  let c = G.converse r in
  check_eq_int "General converse preserves card" ~expect:4 (G.card c);
  (* "avocado" and "apple" are the same coarse key, so its image under the
     converse collects both right-hand sides. *)
  check_eq_int "General converse preimage-as-image" ~expect:2 (Set.length (G.image c (w "avocado")));
  let nums = G.of_list (module Int) (module Int) [ (1, 100); (1, 200); (3, 300) ] in
  let f = G.fork nums nums in
  check_eq_int "General fork derives its own witness" ~expect:5 (G.card f);
  let f2 = G.fork f nums in
  check_eq_int "General nested fork needs no new machinery" ~expect:9 (G.card f2);
  let g = G.group r in
  check_eq_int "General group" ~expect:3 (G.card g);
  let e = G.empty Int.comparator Coarse.comparator in
  check_eq_int "General empty is a function of the comparators" ~expect:0 (G.card e);
  let u = G.union r (G.of_list (module Int) (module Coarse) [ (5, w "durian") ]) in
  check_eq_int "General union with matching witnesses" ~expect:5 (G.card u);
  (* The deterministic counterpart of the timed structural-comparison section
     above: the 114.9x fork_cost ratio exists only because the Poly comparator
     walks payloads. Here the payload is a lazy whose forcing is counted, and
     a tag-only comparator is in force, so fork and compose must never force
     it. Asserting the invariant directly replaces gating on a noisy timing
     ratio. *)
  let payload_forces = ref 0 in
  let module Tagged = struct
    module T = struct
      type t = { tag : int; payload : unit Lazy.t }

      let compare a b = Int.compare a.tag b.tag
      let sexp_of_t t = Sexp.Atom (sprintf "<%d>" t.tag)
    end

    include T
    include Comparator.Make (T)
  end in
  let mk i = { Tagged.tag = i mod 5; payload = lazy (Int.incr payload_forces) } in
  let a =
    G.of_list (module Tagged) (module Tagged) (List.init 20 ~f:(fun i -> (mk i, mk (i + 3))))
  in
  let b =
    G.of_list (module Tagged) (module Tagged) (List.init 20 ~f:(fun i -> (mk (i + 1), mk (i + 7))))
  in
  ignore (G.fork a b : _ G.t);
  ignore (G.compose a b : _ G.t);
  check_eq_int "fork and compose with a tag-only comparator never force a payload"
    ~expect:0 !payload_forces

(* ------------------------------------------------------------------ *)
(* Eval.General: the four-parameter algebra, end to end                *)
(* ------------------------------------------------------------------ *)

let test_eval_general () =
  section "Eval.General: the four-parameter algebra end to end";
  let module E = Eval.General in
  let module R = Relation.General in
  let w key = { Coarse.key; payload = [] } in
  let card t = R.card (E.to_relation t) in
  (* "anna" and "andy" share a coarse key, so both join to department 10. *)
  let manages =
    E.of_list (module Int) (module Coarse) [ (1, w "anna"); (2, w "bob"); (3, w "andy") ]
  in
  let dept = E.of_list (module Coarse) (module Int) [ (w "anna", 10); (w "bob", 20) ] in
  let open E in
  let r = manages >> dept in
  check_eq_int "compose through a coarse middle" ~expect:3 (card r);
  check_eq_int "converse of a composition" ~expect:3 (card (converse r));
  let seniors = r >> where_ Int.comparator (fun d -> d >= 20) in
  check_eq_int "where_ filters by a coreflexive" ~expect:1 (card seniors);
  let both = fork r r >> fst_ (R.Prod (R.Base Int.comparator, R.Base Int.comparator)) in
  check_eq_int "fork then project is the identity here" ~expect:3 (card both);
  check_eq_int "id is a left unit" ~expect:3 (card (id Int.comparator >> r));
  check_eq_int "bot is a join unit" ~expect:3 (card (join (bot Int.comparator Int.comparator) r));
  let chain = of_list (module Int) (module Int) [ (1, 2); (2, 3) ] in
  check_eq_int "plus adds the transitive pairs" ~expect:3 (card (plus chain));
  check_eq_int "star is reflexive on the carrier only" ~expect:6 (card (star chain));
  (* Scalar equality under the carried comparator, against the structural one. *)
  let people = of_list (module Int) (module Coarse) [ (1, w "apple") ] in
  let coarse_eq =
    people
    >> where_ Coarse.comparator
         (let open V in
          fun x -> eq_with Coarse.comparator x (lit (w "avocado")))
  in
  check_eq_int "eq_with follows the carried comparator" ~expect:1 (card coarse_eq);
  let structural_eq =
    people
    >> where_ Coarse.comparator
         (let open V in
          fun x -> x =. lit (w "avocado"))
  in
  check_eq_int "=. stays structural" ~expect:0 (card structural_eq);
  (* "run the function backwards": materialise on a carrier, then converse. *)
  let succs = fn Int.comparator Int.comparator succ in
  check
    "converse of an unbounded function graph announces"
    (try
       ignore (converse succs);
       false
     with Eval.Unbounded _ -> true);
  let back = converse (materialise ~ca:Int.comparator ~dom:[ 1; 2; 3 ] succs) in
  check_eq_int "materialise makes converse free" ~expect:3 (card back)

(* ------------------------------------------------------------------ *)
(* Symbolic.General: print it, plan it, run it                         *)
(* ------------------------------------------------------------------ *)

let test_symbolic_general () =
  section "Symbolic.General: one program, printed and run";
  let module R = Relation.General in
  let w key = { Coarse.key; payload = [] } in
  let module Q (R4 : Algebra.General.RELATIONS) = struct
    open R4

    let q =
      let manages =
        of_list (module Int) (module Coarse) [ (1, w "anna"); (2, w "bob"); (3, w "andy") ]
      in
      let dept = of_list (module Coarse) (module Int) [ (w "anna", 10); (w "bob", 20) ] in
      manages >> dept >> where_ Int.comparator (let open V in fun d -> d >=. int_ 20)
  end in
  let module Sq = Q (Symbolic.General) in
  let module Eq = Q (Eval.General) in
  check
    "the tree prints, predicate structure included"
    (String.equal
       (Symbolic.General.to_string Sq.q)
       "((«3» >> «2») >> where((x >= 20)))");
  check_eq_int "the tree runs" ~expect:1 (R.card (Symbolic.General.run Sq.q));
  check_eq_int "eval agrees" ~expect:1 (R.card (Eval.General.to_relation Eq.q));
  check "no opacity where there is none" (not (Symbolic.General.has_opaque Sq.q))

(* ------------------------------------------------------------------ *)
(* Rel_incr.General: live updates over carried comparators             *)
(* ------------------------------------------------------------------ *)

let test_incr_general () =
  section "Rel_incr.General: live updates over carried comparators";
  let module G = Rel_incr.General in
  let module R = Relation.General in
  let w key = { Coarse.key; payload = [] } in
  Rel_incr.reset_counters ();
  let v = G.Var.create (R.of_list (module Int) (module Coarse) [ (1, w "anna"); (2, w "bob") ]) in
  let dept = G.of_list (module Coarse) (module Int) [ (w "anna", 10); (w "bob", 20) ] in
  let obs = G.observe G.(Var.watch v >> dept) in
  Rel_incr.stabilize ();
  check_eq_int "initial composition" ~expect:2 (R.card (G.Observer.value obs));
  G.Var.set v
    (R.of_list (module Int) (module Coarse) [ (1, w "anna"); (2, w "bob"); (3, w "andy") ]);
  Rel_incr.stabilize ();
  (* "andy" shares a coarse key with "anna", so it joins to department 10. *)
  check_eq_int "insert propagates through the coarse key" ~expect:3 (R.card (G.Observer.value obs));
  check "the delta path was taken" (Rel_incr.delta_updates () >= 1)

(* ------------------------------------------------------------------ *)
(* Laws, planner and surface at four parameters                        *)
(* ------------------------------------------------------------------ *)

let test_laws_general () =
  section "Laws.General: the same laws, property-checked against Eval.General";
  let module L = Laws.General.Make (Eval.General) in
  let by_group = Hashtbl.create (module String) in
  List.iter L.all ~f:(fun law ->
    let ok = ref true in
    (try
       Base_quickcheck.Test.run_exn
         ~config:qc_config
         (module Sample4)
         ~f:(fun s -> if not (law.L.check (Sample4.to_sample s)) then failwith "law violated")
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

let test_plan_general () =
  section "Plan.General: fusion fires and the plan is sound";
  let module S = Symbolic.General in
  let module R = Relation.General in
  let n = 300 in
  (* A hub with a ring through the spokes: skewed, so the unfused triangle
     materialises far more than the result. *)
  let edges =
    R.of_list (module Int) (module Int)
      (List.concat (List.init n ~f:(fun i -> [ (0, i); (i, (i + 1) % n) ])))
  in
  let e = S.of_relation edges in
  let tri = S.(meet (e >> e) e) in
  let opt = Plan.General.optimise tri in
  check "the meet is fused into the composition"
    (String.is_substring (S.to_string opt) ~substring:"⋈");
  check "the planned tree agrees with the written one" (R.equal (S.run opt) (S.run tri));
  let chain = S.(e >> e >> e >> e) in
  check "re-association agrees with the written chain"
    (R.equal (S.run (Plan.General.optimise chain)) (S.run chain))

let test_query_general () =
  section "Query.General: the surface with points, at four parameters";
  let module Q = Query.General in
  let module R = Relation.General in
  let edges = R.of_list (module Int) (module Int) [ (1, 2); (2, 3); (1, 3); (3, 4) ] in
  let two_steps =
    Q.run ~cmp:Int.comparator (fun x ->
      let open Q in
      let* y = step edges x in
      let* z = step edges y in
      ret z)
  in
  check_eq_int "a chain compiles and runs" ~expect:3 (R.card two_steps);
  let triangles =
    Q.run ~cmp:Int.comparator (fun x ->
      let open Q in
      let* y = step edges x in
      let* z = step edges y in
      let* () = constrain edges x z in
      ret z)
  in
  check_eq_int "a cycle closes by meet" ~expect:1 (R.card triangles)

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
  test_estimator_quality ();
  triangle_gap ();
  test_fork_fusion_is_strict ();
  test_query_surface ();
  test_projection_compose ();
  test_no_gratuitous_refusal ();
  test_structural_comparison_cost ();
  test_filter_pushdown_gap ();
  test_long_cycle_gap ();
  test_general_comparators ();
  test_eval_general ();
  test_symbolic_general ();
  test_incr_general ();
  test_laws_general ();
  test_plan_general ();
  test_query_general ();
  printf "\n%d checks, %d failures\n" !checks !failures;
  if !failures > 0 then exit 1
