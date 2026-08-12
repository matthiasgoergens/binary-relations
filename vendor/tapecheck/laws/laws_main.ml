(** The algebra's laws, property-checked with tapecheck's choice-tape shrinker
    instead of [Base_quickcheck.Shrinker.atomic].

    This lives inside the vendored tapecheck tree rather than in [test/], and
    that is not a stylistic choice. tapecheck vendors its own
    [base_quickcheck] and [splittable_random] under those exact library names,
    so any dune target that also reaches the installed [base_quickcheck] —
    which every user of [Core] does, transitively through [base_bigstring] and
    [int_repr] — fails to resolve, and fails to link even with
    [(allow_overlapping_dependencies)]. The main suite in [test/] uses [Core]
    because [Incremental] does. So the two cannot share a scope, and this
    suite can reach [rel] at all only because [rel] itself was made Core-free.

    Build:  dune build vendor/tapecheck/laws/laws_main.exe
    Run:    dune exec  vendor/tapecheck/laws/laws_main.exe *)

open! Base
open Rel

module Sample = struct
  module L = Laws.Make (Eval)

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

  (* Unchanged from the stock suite, and deliberately so: tapecheck's claim is
     that the shrinker your types already declare is accepted and ignored, so
     leaving [atomic] here is part of testing the claim rather than an
     oversight. *)
  let quickcheck_shrinker = Base_quickcheck.Shrinker.atomic
  let to_sample { a; b; c } = { L.a = Eval.of_list a; b = Eval.of_list b; c = Eval.of_list c }
end

let config = { Base_quickcheck.Test.default_config with test_count = 300 }

(* Both engines take the same (module S) and the same ~f, so the runner is
   written once and pointed at either. That much of the drop-in claim holds
   exactly. *)
let run_stock ~f = Base_quickcheck.Test.run ~config (module Sample) ~f
(* [?report] defaults to [`Summary], which prints a line to stdout on every
   run -- 47 of them for the law suite. [`Silent] is available but is not in
   the README's usage section, so it takes reading tape_test.ml to find. *)
let run_tape ?(report = `Silent) ~f () = Tape_test.run ~config ~report (module Sample) ~f

(* Pull the failing input back out of the error, so the two engines can be
   compared on the size of what they report and not merely on whether they
   fail at all. *)
let reported_input msg =
  match String.substr_index msg ~pattern:"(input" with
  | None -> msg
  | Some i -> (
    let rest = String.subo msg ~pos:i in
    match String.substr_index rest ~pattern:"(error" with
    | None -> rest
    | Some j -> String.sub rest ~pos:0 ~len:j)

let show name = function
  | Ok () -> Stdio.printf "  %-18s did not falsify it\n" name
  | Error e ->
    Stdio.printf "  %-18s %s\n" name
      (String.strip (reported_input (Error.to_string_hum e)))

let () =
  let module L = Laws.Make (Eval) in
  Stdio.printf "\nThe %d laws, checked with the choice-tape engine\n\n" (List.length L.all);
  let failed = ref 0 in
  List.iter L.all ~f:(fun law ->
    match
      run_tape
        ~f:(fun s ->
          if law.L.check (Sample.to_sample s) then Ok () else Or_error.error_string "law violated")
        ()
    with
    | Ok () -> ()
    | Error e ->
      Int.incr failed;
      Stdio.printf "  FAIL %s/%s\n%s\n" law.L.group law.L.name (Error.to_string_hum e));
  Stdio.printf "  %d of %d laws failing\n" !failed (List.length L.all);

  (* The comparison that matters: a law that is simply false, checked by both
     engines against the same generators, so the only difference between them
     is what each hands back when it fails.

     Composition does not commute. The smallest witness is one pair on each
     side — a = [(0,1)], b = [(1,0)] gives a >> b = [(0,0)] against
     b >> a = [(1,1)]. Anything larger is noise the shrinker did not remove. *)
  let commutes s =
    let { L.a; b; _ } = Sample.to_sample s in
    if Eval.equal Eval.(a >> b) Eval.(b >> a) then Ok ()
    else Or_error.error_string "composition is not commutative"
  in
  Stdio.print_endline "\nA deliberately false law, as each engine reports it\n";
  show "base_quickcheck" (run_stock ~f:commutes);
  show "tapecheck" (run_tape ~f:commutes ());

  (* And one where the failure is a rare structural condition rather than a
     wrong equation, which is the shape the real bug in this project had: the
     residual's Galois connection fails only when the divisor is empty. *)
  let galois s =
    let { L.a; b; c } = Sample.to_sample s in
    let open Eval in
    if Bool.equal (subset (c >> b) a) (subset c (rdiv a b)) then Ok ()
    else Or_error.error_string "rdiv is not adjoint to composition"
  in
  Stdio.print_endline "\nThe law that actually failed during development\n";
  show "base_quickcheck" (run_stock ~f:galois);
  show "tapecheck" (run_tape ~f:galois ());
  Stdio.print_endline ""
