(* Wall-clock numbers, with spread, for every ratio this repo publishes.

   These exist because an audit refuted the published figures. Every headline
   was stated in [Relation.tuples_touched], which is a model: it counts tuples
   scanned and produced, and charges nothing for the per-tuple constants that
   dominate at small sizes — set allocation, index probes, intersections. It
   therefore flatters probe-heavy work over allocate-heavy work. Measured
   against the clock, the 4-cycle fusion is 13x rather than 223x, and the
   planner's chain re-association is a wash end-to-end.

   Two timings are reported for anything involving the planner, because they
   answer different questions and only one of them was ever published:

     warm  -- execution only, statistics already paid for. What re-association
              buys, given a plan.
     cold  -- build, plan and execute. What a caller actually pays. *)

open! Base

let time_ms f =
  let t0 = Stdlib.Sys.time () in
  f ();
  (Stdlib.Sys.time () -. t0) *. 1000.

let stats xs =
  let n = Float.of_int (List.length xs) in
  let mean = List.sum (module Float) xs ~f:Fn.id /. n in
  let var = List.sum (module Float) xs ~f:(fun x -> (x -. mean) **. 2.) /. n in
  (mean, Float.sqrt var)

(* Discard the first run: it pays for lazy initialisation that later runs do
   not, and including it inflates the spread rather than the mean. *)
let measure ?(reps = 11) f =
  let xs = List.init reps ~f:(fun _ -> time_ms f) in
  stats (List.tl_exn xs)

let row name (m, sd) = Stdio.printf "   %-42s %8.3f ms  ± %.3f\n" name m sd

let compare_rows name a b =
  let ma, _ = a and mb, _ = b in
  Stdio.printf "   %-42s %8.2fx\n\n" name (ma /. Float.max 1e-9 mb)

open Rel

let () =
  Stdio.printf "\nWall-clock, mean ± sd over 10 runs (first discarded)\n\n";

  (* ---- semi-naive vs naive transitive closure ---- *)
  Stdio.print_endline "Transitive closure of a 30-link chain";
  let chain () = Relation.of_list (List.init 30 ~f:(fun i -> (i, i + 1))) in
  let naive r =
    let rec go acc =
      let next = Relation.union acc (Relation.compose acc r) in
      if Relation.equal next acc then acc else go next
    in
    go r
  in
  row "semi-naive" (measure (fun () -> ignore (Relation.plus (chain ()) : _ Relation.t)));
  row "naive fixpoint" (measure (fun () -> ignore (naive (chain ()) : _ Relation.t)));
  compare_rows "ratio"
    (measure (fun () -> ignore (naive (chain ()) : _ Relation.t)))
    (measure (fun () -> ignore (Relation.plus (chain ()) : _ Relation.t)));

  (* ---- the planner's chain: warm and cold ---- *)
  Stdio.print_endline "Chain 500 x 500 x 1, re-associated by the planner";
  let mk3 () =
    ( Relation.of_list (List.init 500 ~f:(fun i -> (i, i))),
      Relation.of_list (List.init 500 ~f:(fun i -> (i, i + 1))),
      Relation.of_list [ (300, 0) ] )
  in
  let term (a, b, c) = Symbolic.(of_relation a >> of_relation b >> of_relation c) in
  (* warm: build and plan once, then time execution alone *)
  let rels = mk3 () in
  let written = term rels in
  let planned = Plan.optimise written in
  let a, b, c = rels in
  List.iter [ a; b; c ] ~f:(fun r -> ignore (Relation.stats r : Relation.stats));
  row "warm: as written" (measure (fun () -> ignore (Symbolic.run written : _ Relation.t)));
  row "warm: planned" (measure (fun () -> ignore (Symbolic.run planned : _ Relation.t)));
  compare_rows "warm ratio (what re-association buys)"
    (measure (fun () -> ignore (Symbolic.run written : _ Relation.t)))
    (measure (fun () -> ignore (Symbolic.run planned : _ Relation.t)));
  row "cold: build + run" (measure (fun () -> ignore (Symbolic.run (term (mk3 ())) : _ Relation.t)));
  row "cold: build + plan + run"
    (measure (fun () -> ignore (Symbolic.run (Plan.optimise (term (mk3 ()))) : _ Relation.t)));
  compare_rows "cold ratio (what a caller pays)"
    (measure (fun () -> ignore (Symbolic.run (term (mk3 ())) : _ Relation.t)))
    (measure (fun () -> ignore (Symbolic.run (Plan.optimise (term (mk3 ()))) : _ Relation.t)));

  (* ---- cycle fusion on a skewed graph ---- *)
  Stdio.print_endline "Cyclic queries on a hub graph (300 spokes)";
  let hub () =
    Relation.of_list
      (List.init 300 ~f:(fun i -> (i + 1, 0))
      @ List.init 300 ~f:(fun j -> (0, j + 1))
      @ List.init 10 ~f:(fun i -> (i + 1, i + 2)))
  in
  let tri () =
    let g = hub () in
    Symbolic.(meet (of_relation g >> of_relation g) (of_relation g))
  in
  let sq () =
    let g = hub () in
    Symbolic.(meet (of_relation g >> of_relation g >> of_relation g) (of_relation g))
  in
  row "triangle, unfused" (measure (fun () -> ignore (Symbolic.run (tri ()) : _ Relation.t)));
  row "triangle, fused"
    (measure (fun () -> ignore (Symbolic.run (Plan.optimise (tri ())) : _ Relation.t)));
  compare_rows "triangle ratio"
    (measure (fun () -> ignore (Symbolic.run (tri ()) : _ Relation.t)))
    (measure (fun () -> ignore (Symbolic.run (Plan.optimise (tri ())) : _ Relation.t)));
  row "4-cycle, unfused" (measure ~reps:5 (fun () -> ignore (Symbolic.run (sq ()) : _ Relation.t)));
  row "4-cycle, fused"
    (measure ~reps:5 (fun () -> ignore (Symbolic.run (Plan.optimise (sq ())) : _ Relation.t)));
  compare_rows "4-cycle ratio"
    (measure ~reps:5 (fun () -> ignore (Symbolic.run (sq ()) : _ Relation.t)))
    (measure ~reps:5 (fun () -> ignore (Symbolic.run (Plan.optimise (sq ())) : _ Relation.t)))
