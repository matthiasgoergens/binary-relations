(* Is bulk construction worth a transient builder?

   The brief budgets for transients -- an O(1)-in/out mutable builder behind an
   immutable interface -- and notes they do not help the one-tuple-at-a-time
   case. Before building one, measure which case is actually slow. *)

open! Base
open Rel

let time name f =
  let t0 = Unix.gettimeofday () in
  let r = f () in
  let dt = Unix.gettimeofday () -. t0 in
  Stdio.printf "   %-38s %7.1f ms   (%d pairs)\n" name (dt *. 1000.) (Relation.card r);
  dt

let () =
  let n = 50_000 in
  let pairs = List.init n ~f:(fun i -> (i, i * 7 % n)) in
  Stdio.printf "\nBuilding a %d-pair relation\n\n" n;
  let bulk = time "of_list (one pass)" (fun () -> Relation.of_list pairs) in
  let incremental =
    time "repeated union with a singleton" (fun () ->
      List.fold pairs ~init:Relation.empty ~f:(fun acc (a, b) ->
        Relation.union acc (Relation.singleton a b)))
  in
  Stdio.printf "\n   repeated insert is %.1fx the cost of the bulk path\n" (incremental /. bulk);
  Stdio.printf
    "   per insert: %.2f us\n" (incremental *. 1e6 /. Float.of_int n);
  (* What a transient would remove is the per-insert rebuild. If the ratio is
     small and the per-insert cost is already sub-microsecond, there is nothing
     to win. *)
  Stdio.printf "\n   index build on the finished value:\n";
  let r = Relation.of_list pairs in
  let fwd = time "first image lookup (builds an index)" (fun () -> ignore (Relation.image r 0 : int Set.Poly.t); r) in
  ignore fwd
