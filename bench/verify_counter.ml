(* Does tuples_touched track reality? Every performance number in this repo is
   stated in that unit, and the counter is a model I wrote and corrected twice
   in one session. If its ratios diverge from wall-clock ratios, the published
   figures are decoration. *)

open! Base
open Rel

let time f =
  let t0 = Stdlib.Sys.time () in
  let r = f () in
  (r, Stdlib.Sys.time () -. t0)

let both name build =
  (* counter *)
  let t = build () in
  Relation.reset_counters ();
  let _ = Symbolic.run t in
  let touched = Relation.tuples_touched () in
  (* wall clock, fresh value, repeated to get out of the noise *)
  let reps = 5 in
  let _, secs =
    time (fun () ->
      for _ = 1 to reps do
        let t = build () in
        ignore (Symbolic.run t : (int, int) Relation.t)
      done)
  in
  let ms = secs *. 1000. /. Float.of_int reps in
  Stdio.printf "   %-34s %9d tuples   %8.2f ms\n" name touched ms;
  (touched, ms)

let () =
  let h = 300 in
  let hub =
    List.init h ~f:(fun i -> (i + 1, 0))
    @ List.init h ~f:(fun j -> (0, j + 1))
    @ List.init 10 ~f:(fun i -> (i + 1, i + 2))
  in
  let mk () = Relation.of_list hub in
  Stdio.print_endline "\nDoes the counter's ratio match the clock's?\n";
  let plain () =
    let g = mk () in
    Symbolic.(of_relation g >> of_relation g >> of_relation g |> fun c ->
              meet c (of_relation g))
  in
  let fused () = Plan.optimise (plain ()) in
  let tc, mc = both "4-cycle, unfused" plain in
  let tf, mf = both "4-cycle, fused" fused in
  Stdio.printf "\n   counter ratio %.1fx     wall-clock ratio %.1fx\n"
    (Float.of_int tc /. Float.of_int (Int.max 1 tf))
    (mc /. Float.max 0.0001 mf);
  let report a b =
    Stdio.printf "\n   counter ratio %.1fx     wall-clock ratio %.1fx   %s\n" a b
      (if Float.( > ) (Float.min a b /. Float.max a b) 0.25 then "(comparable)"
       else "DIVERGENT")
  in
  report (Float.of_int tc /. Float.of_int (Int.max 1 tf)) (mc /. Float.max 0.0001 mf);

  (* The other headline: the 500 x 500 x 1 chain the planner re-associates. *)
  Stdio.print_endline "\nThe planner's chain, the other published headline\n";
  let mk3 () =
    ( Relation.of_list (List.init 500 ~f:(fun i -> (i, i))),
      Relation.of_list (List.init 500 ~f:(fun i -> (i, i + 1))),
      Relation.of_list [ (300, 0) ] )
  in
  let chain_plain () =
    let a, b, c = mk3 () in
    Symbolic.(of_relation a >> of_relation b >> of_relation c)
  in
  let chain_planned () = Plan.optimise (chain_plain ()) in
  let tc2, mc2 = both "chain, as written" chain_plain in
  let tf2, mf2 = both "chain, planned" chain_planned in
  report (Float.of_int tc2 /. Float.of_int (Int.max 1 tf2)) (mc2 /. Float.max 0.0001 mf2)
