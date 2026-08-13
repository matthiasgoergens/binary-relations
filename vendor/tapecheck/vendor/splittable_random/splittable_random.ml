(* Tape shim over the PATCHED splittable_random (vendored as Sr_real,
   carrying the proposed upstream Intercept seam, here at seam v2). The
   whole interception is one [Intercept.t] record per stream: every
   bounded integer draw (int, int32, int63, nativeint, and all of
   Log_uniform) reaches the [int64] hook with its bounds, because
   upstream funnels them through [int64].

   Streams (design/stream-keyed-tapes.md): each hook record closes over
   a stream key. [on_split] allocates the child key and returns hooks
   for the split-off state, so Generator.fn's per-function stream is
   tape-controlled; [on_perturb] extends a child key with the salt
   (Generator.fn's per-argument identity) and rewinds that stream, so
   same-argument calls replay identically and generated functions
   shrink. A perturb on the root stream only records an alignment
   marker, keeping the main stream in one piece. *)

open! Base
include Sr_real

module For_tape = struct
  let rec hooks tape key : Sr_real.Intercept.t =
    { int64 =
        (fun st ~lo ~hi ~default ->
          (* [default] is generic over its own [lo]/[hi] (it is just
             the real uniform sampler), so we hand the tape a fully
             general ranged sampler: it can call this with ANY bounds,
             not only the ones this draw declared, to source the extra
             randomness edge-case biasing needs (which boundary
             candidate, which bit-size, ...). Only the FINAL chosen
             value is recorded to the tape (in [Tape.draw_int]); these
             auxiliary rolls just consume RNG state. *)
          Tape.draw_int tape ~stream:key ~lo ~hi
            ~sample:(fun ~lo ~hi -> default st ~lo ~hi))
    ; float =
        (fun st ~lo ~hi ~default ->
          Tape.draw_float tape ~stream:key ~lo ~hi
            ~sample:(fun ~lo ~hi -> default st ~lo ~hi))
    ; unit_float =
        (fun st ~default ->
          Tape.draw_float tape ~stream:key ~lo:0. ~hi:1.
            ~sample:(fun ~lo:_ ~hi:_ -> default st))
    ; bool =
        (fun st ~default ->
          Tape.draw_bool tape ~stream:key ~sample:(fun () -> default st))
    ; bool_with_probability =
        (fun st ~probability ~default ->
          Tape.draw_bool tape ~stream:key ~sample:(fun () -> default st ~probability))
    ; on_span_start = (fun _label -> ())
    ; on_span_stop = (fun () -> ())
    ; on_split =
        (fun () -> Some (hooks tape (Tape.on_split tape ~stream:key)))
    ; on_perturb =
        (fun salt ->
          match Tape.on_perturb tape ~stream:key ~salt with
          | None -> None
          | Some salted -> Some (hooks tape salted))
    }

  let attach t tape = Sr_real.with_intercept t (hooks tape Tape.root)
end
