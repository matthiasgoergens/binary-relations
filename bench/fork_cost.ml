(* Does keeping [Comparator.Poly] "only for products" actually contain the
   structural-comparison problem?

   This probe exists because an audit caught a claim that outran its evidence.
   The reasoning offered was: merlin's stored relation is [uid -> Lid.t], and
   neither side is a pair, so keeping [Poly] for [fork] results only would fix
   the real failure and degrade "only where you construct tuples yourself,
   which is usually small values".

   The second half is wrong on inspection. [Relation.fork] builds

     Set.add acc (a, (b, c))

   into a [Set.Poly], so the pair's order recurses into [b] and [c]. The
   components of the tuple are not small values chosen by the caller; they are
   whatever the forked relations range over. On merlin data that is [Lid.t] --
   precisely the type that runs out of memory.

   So the question is whether fork's cost tracks its components' comparison
   cost. Domain and cardinality are held fixed; only the range type varies.
   [equal but unshared] matters: OCaml's polymorphic compare short-circuits on
   physical equality, so shared values are free and only distinct-but-equal
   structures pay. That is what merlin's lazy unmarshalling produces. *)

open! Base

let time_ms f =
  let t0 = Stdlib.Sys.time () in
  let r = f () in
  ((Stdlib.Sys.time () -. t0) *. 1000., r)

(* Mean and sd over repeats, discarding the first run. This repo's standard is
   mean +- sd over 10 runs (bench/headline.ml); the first version of this file
   reported a single run, and that single number then reached NOTES.md and a
   commit message before anyone checked it against the house standard. *)
let stats xs =
  let n = Float.of_int (List.length xs) in
  let mean = List.sum (module Float) xs ~f:Fn.id /. n in
  let var = List.sum (module Float) xs ~f:(fun x -> (x -. mean) **. 2.) /. n in
  (mean, Float.sqrt var)

let measure ?(reps = 11) f =
  let xs = List.init reps ~f:(fun _ -> fst (time_ms f)) in
  stats (List.tl_exn xs)

(* Two things have to be true for this probe to measure anything, and the
   first version of it got both wrong -- which showed up as the expensive case
   timing *faster* than the control.

   1. The relations must be NON-FUNCTIONAL. [fork] inserts [(a, (b, c))], so
      if every domain element carries one range value, [compare] settles on
      the [int] first and never reaches the pair at all.

   2. The discriminator must come LAST. A value whose differing field is at
      the front is cheap however long the rest is, because [compare] returns
      at the first difference. Only an identical-but-unshared prefix is
      expensive -- which is the merlin case: lazily unmarshalled structures
      that are equal without being shared. *)
let big i = List.init 400 ~f:(fun k -> Printf.sprintf "w%d" k) @ [ Printf.sprintf "t%d" i ]
let small i = [ Printf.sprintf "t%d" i ]

let () =
  let doms = 3 and per_dom = 40 in
  Stdio.printf "\nfork cost against range-comparison cost (%d domain elements, %d values each)\n\n"
    doms per_dom;

  let run name mk =
    (* Build both branches first and do not charge that to fork. *)
    let mkrel off =
      Rel.Relation.of_list
        (List.concat_map (List.init doms ~f:Fn.id) ~f:(fun d ->
           List.init per_dom ~f:(fun j -> (d, mk (off + (d * per_dom) + j)))))
    in
    let a = mkrel 0 and b = mkrel 10_000 in
    let _, out = time_ms (fun () -> Rel.Relation.fork a b) in
    let mean, sd = measure (fun () -> ignore (Rel.Relation.fork a b : _ Rel.Relation.t)) in
    Stdio.printf "   %-34s %9.3f ms  ± %.3f  (%d pairs out)\n" name mean sd
      (Rel.Relation.card out);
    mean
  in
  let cheap = run "range = short list (control)" small in
  let dear = run "range = 400-word shared prefix" big in
  Stdio.printf "\n   ratio %.1fx\n" (dear /. Float.max 1e-9 cheap);
  Stdio.printf
    "\n   If this ratio is large, fork's cost is set by the component type, so\n\
    \   'Poly for products only' does not contain the problem: it re-exposes\n\
    \   exactly the type the four-parameter change was made to protect.\n"
