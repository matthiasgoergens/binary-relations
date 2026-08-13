(** The confirmed business case: an org chart.

    Reachability over a hierarchy is the thing plain Codd cannot express, so
    it is where a relational value earns its keep over a hand-rolled map. The
    example also makes the access-path argument concrete: the same value
    answers "who does Frank report to, ultimately?" and "who is under Alice?"
    without being reshaped, because neither direction was ever written into
    it.

    Written against the four-parameter [Relation.General] ladder, the API the
    library recommends: the two-parameter [Poly] façade exists for quick
    scalar experiments, but it is the one that cannot survive the real values
    this library was built for (see [examples/merlin_index.ml] and NOTES.md).

    Run with [dune exec examples/org_chart.exe]. *)

open! Core
open Rel
module Incr = Rel_incr
module G = Relation.General

let reports_to =
  G.of_list (module String) (module String)
    [
      ("bob", "alice");
      ("carol", "alice");
      ("dave", "bob");
      ("erin", "bob");
      ("frank", "carol");
      ("grace", "carol");
      ("heidi", "frank");
      ("ivan", "frank");
      ("judy", "dave");
    ]

let department =
  G.of_list (module String) (module String)
    [
      ("alice", "exec"); ("bob", "eng"); ("carol", "eng"); ("dave", "eng"); ("erin", "eng");
      ("frank", "sales"); ("grace", "sales"); ("heidi", "sales"); ("ivan", "sales");
      ("judy", "eng");
    ]

let show label xs = printf "  %-34s %s\n" label (String.concat ~sep:", " xs)

let () =
  printf "\nThe chain of command\n\n";

  (* [plus] is transitive closure: every manager above a person, at any
     distance. Semi-naive, so a pair is never re-derived from an old one. *)
  let above = G.plus reports_to in
  show "everyone above heidi" (Set.to_list (G.image above "heidi"));

  (* The same value, read the other way. No second index was declared, no data
     was reshaped, and no call site knows which direction is "the" direction —
     that is Codd's point, restated for a value in memory. *)
  show "everyone under alice" (Set.to_list (G.preimage above "alice"));
  show "everyone under carol" (Set.to_list (G.preimage above "carol"));

  printf "\n  distinct people above someone: %d, below someone: %d, pairs: %d\n"
    (G.stats above).domain_size (G.stats above).range_size (G.card above);

  (* Composition answers a question about two relations at once: the
     departments represented under each manager. Written as a program against
     the signature, so it runs under any interpreter. *)
  printf "\nDepartments under each manager\n\n";
  let module Q (R : Algebra.General.RELATIONS) = struct
    open R

    let depts_below = converse (of_relation above) >> of_relation department
    let rolled_up = group depts_below
  end in
  let module E = Q (Eval.General) in
  List.iter (Eval.General.to_list E.rolled_up) ~f:(fun (mgr, depts) -> show mgr depts);

  (* Division: universal quantification without a complement. "Which people
     have every member of the sales department beneath them?" *)
  printf "\nWho has all of sales beneath them\n\n";
  let sales =
    G.filter_rng department ~f:(fun d -> String.equal d "sales")
    |> G.converse
    |> G.map_dom String.comparator ~f:(fun _ -> "sales-team")
  in
  let below = G.converse above in
  let covers_all = G.rdiv below sales in
  show "covers the whole sales team" (List.map (G.to_list covers_all) ~f:fst);

  (* What the planner makes of a three-way composition. *)
  printf "\nThe plan\n\n";
  let module P (R : Algebra.General.RELATIONS) = struct
    open R

    let q = of_relation reports_to >> of_relation reports_to >> of_relation department
  end in
  let module S = P (Symbolic.General) in
  print_endline (Plan.General.explain S.q);

  (* And the same query kept live. Erin moves from bob to carol; the view is
     maintained rather than recomputed. *)
  printf "\nA reorganisation, incrementally\n\n";
  let module I = P (Incr.General) in
  let var = Incr.General.Var.create reports_to in
  let module Live (R : Algebra.General.RELATIONS) = struct
    open R

    let q ~edges = converse (plus edges) >> of_relation department
  end in
  let module L = Live (Incr.General) in
  let obs = Incr.General.observe (L.q ~edges:(Incr.General.Var.watch var)) in
  Incr.stabilize ();
  let before = G.image (Incr.General.Observer.value obs) "bob" in
  show "departments under bob, before" (Set.to_list before);
  let moved =
    G.union
      (G.diff reports_to (G.singleton String.comparator String.comparator "erin" "bob"))
      (G.singleton String.comparator String.comparator "erin" "carol")
  in
  Incr.General.Var.set var moved;
  Incr.stabilize ();
  show "departments under bob, after" (Set.to_list (G.image (Incr.General.Observer.value obs) "bob"));
  show "departments under carol, after"
    (Set.to_list (G.image (Incr.General.Observer.value obs) "carol"));
  printf "\n"
