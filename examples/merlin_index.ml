(** Merlin's occurrence index, as a relation.

    The best-scoring target from a scan of prominent OCaml projects: it wants
    the same data under more than one key, and it is read far more often than
    it is rebuilt, so an index amortises without anyone having to be clever
    about maintaining it.

    (The index also stores shapes, per-file stats and a related-uid union-find;
    "stored one way" below is about the {e occurrence mapping} specifically.)

    From [src/index-format/index_format.ml]:

    {[
      type index = {
        defs         : Lid_set.t Uid_map.t;   (* uid -> occurrences *)
        approximated : Lid_set.t Uid_map.t;   (* same shape, lower confidence *)
        ...
      }
    ]}

    [defs] {e is} a binary relation between definitions and their occurrences,
    stored as a map in one direction. That direction answers "find references".
    Two other questions an editor asks constantly are not stored at all:

    - {b what is defined at this location?} — the converse. It is not in the
      index: a [Lid.t] carries a filename and a source range but no owning uid
      ([lid.ml:10]), so location → uid could only be recovered by scanning
      every uid entry. Merlin instead resolves a cursor position through the
      typed environment and shapes ([locate.ml:864], [locate.ml:687]) and
      consults the index only *after* it has a uid
      ([occurrences.ml:175]). Independently confirmed by a cross-model review
      of the merlin sources.
    - {b which definitions does this file use?} — needs the occurrences keyed
      by file, a third access path nobody has.

    This file models the shape faithfully with stand-in types (a real
    integration would link [Index_format], which drags in the compiler libs)
    and compares the two implementations on all three questions.

    {2 Which relation API this uses}

    The relational side is written against [Relation.General] — the
    comparator-carrying API — because that is what a real integration would
    use: a merlin [Lid.t] is a handle into a lazily-unmarshalled graph, and
    merlin's own [Lid.compare] reads three scalars from it rather than
    comparing the structure. The stand-in [occurrence] gets the same
    treatment here: a hand-written comparator over [file] and [line], two
    scalars. The [Poly] façade would be fine for these stand-ins, but it is
    precisely the one that cannot survive the real values — on merlin's real
    13 MB index it runs out of memory, where the same build on the comparators
    below takes 193 ms (see [NOTES.md]). If the demo is going to be a template
    for the real thing, it should be a template for the API the real thing
    needs.

    {2 The comparison that matters is how the code reads}

    At merlin's index sizes the performance question is mostly "does this stay
    competitive with hand-rolling", and it does. What is worth looking at is
    what each version {e says}:

    {v
      Q2, what is defined at this location?

        map        Map.fold t ~init:[] ~f:(fun ~key ~data acc ->
                     if List.mem data o ~equal:Poly.equal then key :: acc else acc)

        relation   Relation.preimage t o

      Q3, which definitions does this file use?

        map        Map.fold t ~init:[] ~f:(fun ~key ~data acc ->
                     if List.exists data ~f:(fun o -> String.equal o.file file)
                     then key :: acc else acc)

        relation   Relation.preimage (Relation.map_rng t ~f:(fun o -> o.file)) file
    v}

    The map versions are not hard, but each one is a hand-rolled scan carrying
    its own predicate, and the predicate is where a silent bug lives: compare
    the wrong field, use the wrong equality, forget that [data] is a list and
    reach for [=] on it. Nothing in the type stops any of that. The relational
    versions have no predicate to get wrong — [preimage] is the converse and
    says so.

    That is the real claim: not that this is faster, but that "look it up the
    other way" is spelled as looking it up the other way, and a reviewer can
    see it is right without reading a loop.

    Run with [dune exec examples/merlin_index.exe]. *)

open! Core
module Rel_ = Rel

type uid = string

type occurrence = {
  file : string;
  line : int;
}
[@@deriving sexp_of]

let occ file line = { file; line }

(* The comparators a real integration would hand the library. [Occurrence]'s
   plays the role of merlin's [Lid.compare]: two scalars, and the rest of the
   value is deliberately not looked at. *)
module Occurrence = struct
  module T = struct
    type t = occurrence

    let compare a b =
      match String.compare a.file b.file with
      | 0 -> Int.compare a.line b.line
      | n -> n

    let sexp_of_t = sexp_of_occurrence
  end

  include T
  include Comparator.Make (T)
end

(* ------------------------------------------------------------------ *)
(* A synthetic index of the shape merlin builds                        *)
(* ------------------------------------------------------------------ *)

let build ~units ~defs_per_unit ~refs_per_def =
  List.concat_map (List.init units ~f:Fn.id) ~f:(fun u ->
    List.concat_map (List.init defs_per_unit ~f:Fn.id) ~f:(fun d ->
      let uid = Printf.sprintf "u%d.d%d" u d in
      List.init refs_per_def ~f:(fun r ->
        (* references are spread across units, which is what makes the
           file-keyed question interesting *)
        (uid, occ (Printf.sprintf "m%d.ml" ((u + r) % units)) (d + r)))))

(* ------------------------------------------------------------------ *)
(* As merlin stores it: one map, uid -> occurrences                    *)
(* ------------------------------------------------------------------ *)

module As_map = struct
  type t = occurrence list Map.M(String).t

  let of_pairs pairs : t =
    List.fold pairs ~init:(Map.empty (module String)) ~f:(fun acc (uid, o) ->
      Map.add_multi acc ~key:uid ~data:o)

  (* Q1. The direction the map is built for. *)
  let references (t : t) uid = Option.value (Map.find t uid) ~default:[]

  (* Q2. The converse. No access path, so every uid must be examined. *)
  let definition_at (t : t) o =
    Map.fold t ~init:[] ~f:(fun ~key ~data acc ->
      if List.mem data o ~equal:Poly.equal then key :: acc else acc)

  (* Q3. Keyed by file, which is a third path nobody has. Same scan. *)
  let uids_used_in (t : t) file =
    Map.fold t ~init:[] ~f:(fun ~key ~data acc ->
      if List.exists data ~f:(fun o -> String.equal o.file file) then key :: acc else acc)
end

(* ------------------------------------------------------------------ *)
(* As a relation: one value, three questions                           *)
(* ------------------------------------------------------------------ *)

module As_relation = struct
  open Rel_

  type t =
    (uid, String.comparator_witness, occurrence, Occurrence.comparator_witness) Relation.General.t

  let of_pairs pairs : t =
    Relation.General.of_list (module String) (module Occurrence) pairs

  let references (t : t) uid = Set.to_list (Relation.General.image t uid)

  (* The converse is not a second structure to build and keep in step; it is
     the same value read the other way. *)
  let definition_at (t : t) o = Set.to_list (Relation.General.preimage t o)

  (* The third access path is a derived relation, and it is derived once. *)
  let by_file (t : t) = Relation.General.map_rng String.comparator t ~f:(fun o -> o.file)
  let uids_used_in by_file file = Set.to_list (Relation.General.preimage by_file file)
end

(* ------------------------------------------------------------------ *)

let () =
  let pairs = build ~units:60 ~defs_per_unit:40 ~refs_per_def:5 in
  let m = As_map.of_pairs pairs in
  let r = As_relation.of_pairs pairs in
  printf "\nMerlin's index shape: %d (uid, occurrence) pairs, %d definitions\n\n"
    (List.length pairs)
    (Set.length (Rel_.Relation.General.dom r));

  let probe_uids = List.take (Set.to_list (Rel_.Relation.General.dom r)) 200 in
  let probe_occs =
    List.take (Set.to_list (Rel_.Relation.General.rng r)) 200
  in
  let files = List.take (List.dedup_and_sort ~compare:String.compare
                           (List.map pairs ~f:(fun (_, o) -> o.file))) 20
  in

  let timed name f =
    let t0 = Stdlib.Sys.time () in
    let n = f () in
    printf "   %-46s %7.1f ms  (%d results)\n" name ((Stdlib.Sys.time () -. t0) *. 1000.) n;
    ()
  in

  printf "Q1 -- find references (the direction the map is built for)\n";
  timed "map" (fun () ->
    List.sum (module Int) probe_uids ~f:(fun u -> List.length (As_map.references m u)));
  timed "relation" (fun () ->
    List.sum (module Int) probe_uids ~f:(fun u -> List.length (As_relation.references r u)));

  printf "\nQ2 -- what is defined at this location? (the converse)\n";
  timed "map: scans every definition" (fun () ->
    List.sum (module Int) probe_occs ~f:(fun o -> List.length (As_map.definition_at m o)));
  timed "relation: preimage" (fun () ->
    List.sum (module Int) probe_occs ~f:(fun o -> List.length (As_relation.definition_at r o)));

  printf "\nQ3 -- which definitions does this file use? (a third key)\n";
  (* Deriving the by-file relation and indexing it costs O(n) once. Charging
     that to a handful of queries makes the relation look slower, which is the
     honest picture at that query count and the wrong picture at an editor's.
     So: measure both, and say where the crossover is. *)
  let repeat n = List.init n ~f:(fun i -> List.nth_exn files (i % List.length files)) in
  let q3_map n () =
    List.sum (module Int) (repeat n) ~f:(fun f -> List.length (As_map.uids_used_in m f))
  in
  let by_file = As_relation.by_file r in
  let q3_rel n () =
    List.sum (module Int) (repeat n) ~f:(fun f ->
      List.length (As_relation.uids_used_in by_file f))
  in
  timed "map, 20 queries" (q3_map 20);
  timed "relation, 20 queries (index build included)" (q3_rel 20);
  timed "map, 2000 queries" (q3_map 2000);
  timed "relation, 2000 queries" (q3_rel 2000);

  (* The claim that converse is free needs a FRESH value: by this point both
     indexes of [r] have been forced by the questions above, so measuring it
     there would report zero builds and prove nothing. *)
  let fresh = As_relation.of_pairs pairs in
  Rel_.Relation.reset_counters ();
  ignore (Rel_.Relation.General.image fresh (List.hd_exn probe_uids));
  let after_forward = Rel_.Relation.index_builds () in
  ignore (Rel_.Relation.General.preimage fresh (List.hd_exn probe_occs));
  let after_backward = Rel_.Relation.index_builds () in
  let c = Rel_.Relation.General.converse fresh in
  List.iter (List.take probe_occs 50) ~f:(fun o ->
    ignore (Rel_.Relation.General.image c o));
  printf
    "\n   index builds on a fresh value: %d after the forward question, %d after\n\
    \   the converse one, %d after 50 further lookups through [converse]\n"
    after_forward after_backward (Rel_.Relation.index_builds ());
  printf
    "\n   Both directions are lookups on one value. The map answers one question\n\
    \   and scans for the other two; the third access path does not exist at all.\n";
  printf
    "\n   At these sizes the timings only need to show no regression, and they do.\n\
    \   The argument is the code: 'preimage t o' against a fold carrying a\n\
    \   hand-written predicate, which is where a silent bug would live.\n"
