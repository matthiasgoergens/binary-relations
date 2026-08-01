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

let () =
  test_laws ();
  test_indexes ();
  test_scalar ();
  test_closure ();
  test_unbounded ();
  test_planner ();
  printf "\n%d checks, %d failures\n" !checks !failures;
  if !failures > 0 then exit 1
