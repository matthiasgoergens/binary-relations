(** M4, and the demo: the same relational program as a live self-adjusting
    graph, on Jane Street's {!Incremental}.

    The pitch for this audience is "[Incr_map], generalised from maps to
    relations", and the reason the generalisation is available is the same
    reason [Incr_map] works at all. [Incr_map] diffs with
    [Map.symmetric_diff], which is cheap {e because} the maps are immutable
    and share structure; two versions of a mutable map would have nothing to
    skip. This library's premise is that relations are immutable, so the same
    trick is available one level up — {!Relation.delta} is
    [Set.symmetric_diff] on the pair sets.

    Two things happen here, and they are worth keeping apart because only one
    of them is [Incremental]'s doing.

    - {b Node-level cutoff}, which comes free from the graph: when an input
      changes, only the nodes on the path from it to the root recompute.
      A sibling subtree is not touched at all.
    - {b Delta propagation inside composition}, which does not come free: a
      recomputing composition node diffs its inputs against what it saw last
      time and, when the change was insert-only, extends the previous output
      by [Δx ∘ y ∪ x ∘ Δy] instead of recomposing. That identity is just
      distributivity of composition over union, and it is exact.

    On deletion it recomputes from scratch. That is a deliberate stopping
    point rather than an oversight: a deleted pair may still be derivable by
    another route, and getting that right without multiplicities means
    counting derivations, which is what Z-sets and DBSP are for. The brief
    files DBSP under "the optimisation for the versioned case"; this is the
    boundary at which it would have to be picked up.

    {2 One global state}

    [Incremental.Make ()] is generative and carries its own state, so this
    module holds exactly one incremental graph for the whole program. That is
    fine for a demonstration and wrong for a library that someone embeds; the
    fix is to make this a functor over the state, which costs nothing but
    noise in the example code. *)

open! Core
module I = Incremental.Make ()

let stabilize = I.stabilize

(* Instrumentation, so that a test can tell whether the delta path was
   actually taken. Without it, a composition node that fell back to
   recomputing every single time would still pass every correctness test --
   the answers would be right and the whole point would be missing. *)
let delta_count = ref 0
let recompute_count = ref 0
let delta_updates () = !delta_count
let full_recomputes () = !recompute_count

let reset_counters () =
  delta_count := 0;
  recompute_count := 0

module Impl = struct
  module V = Eval.V

  (* [Const] exists so that the polymorphic constants of the signature — [id],
     [bot], [fst_] — can be values. An [Incremental] node is created by a
     function call, which the value restriction would pin to a single type.
     It earns its keep anyway: a program built entirely from constants is
     folded at construction time and never enters the graph. *)
  type ('a, 'b) t =
    | Const of ('a, 'b) Eval.t
    | Node of ('a, 'b) Eval.t I.t

  let node = function Const x -> I.const x | Node n -> n
  let of_incr n = Node n
  let to_incr t = node t

  let lift1 f x = match x with Const a -> Const (f a) | Node n -> Node (I.map n ~f)

  let lift2 f x y =
    match (x, y) with
    | Const a, Const b -> Const (f a b)
    | _ -> Node (I.map2 (node x) (node y) ~f)

  (* A composition node that remembers what it last saw. This is the
     [Incr_map] pattern: the incremental behaviour lives in a stateful [f],
     not in a special kind of node. *)
  let compose_incrementally (type a b c) () : (a, b) Eval.t -> (b, c) Eval.t -> (a, c) Eval.t =
    let prev : ((a, b) Relation.t * (b, c) Relation.t * (a, c) Relation.t) option ref =
      ref None
    in
    fun ex ey ->
      match (ex, ey) with
      | Eval.Fin rx, Eval.Fin ry -> (
        let recompute () =
          incr recompute_count;
          let out = Relation.compose rx ry in
          prev := Some (rx, ry, out);
          Eval.Fin out
        in
        match !prev with
        | None -> recompute ()
        | Some (px, py, out) ->
          let add_x, del_x = Relation.delta ~from:px ~to_:rx in
          let add_y, del_y = Relation.delta ~from:py ~to_:ry in
          if not (Relation.is_empty del_x && Relation.is_empty del_y) then recompute ()
          else if Relation.is_empty add_x && Relation.is_empty add_y then Eval.Fin out
          else begin
            (* (x ∪ Δx) ∘ (y ∪ Δy) = x∘y ∪ x'∘Δy ∪ Δx∘y', which is
               distributivity and nothing more. *)
            let out' =
              Relation.union out
                (Relation.union (Relation.compose rx add_y) (Relation.compose add_x ry))
            in
            incr delta_count;
            prev := Some (rx, ry, out');
            Eval.Fin out'
          end)
      | _ -> Eval.( >> ) ex ey

  let ( >> ) x y =
    match (x, y) with
    | Const a, Const b -> Const (Eval.( >> ) a b)
    | _ -> Node (I.map2 (node x) (node y) ~f:(compose_incrementally ()))

  let id = Const Eval.id
  let bot = Const Eval.bot
  let fst_ = Const Eval.fst_
  let snd_ = Const Eval.snd_
  let converse x = lift1 Eval.converse x
  let meet x y = lift2 Eval.meet x y

  (* Union is incremental without any bookkeeping: the result of a union
     shares structure with both arguments, so the next delta downstream is
     cheap for free. *)
  let join x y = lift2 Eval.join x y
  let rdiv x y = lift2 Eval.rdiv x y
  let ldiv x y = lift2 Eval.ldiv x y
  let plus x = lift1 Eval.plus x
  let star x = lift1 Eval.star x
  let fork x y = lift2 Eval.fork x y
  let group x = lift1 Eval.group x
  let where_ p = Const (Eval.where_ p)
  let fn f = Const (Eval.fn f)
  let of_relation r = Const (Eval.of_relation r)
  let of_list l = Const (Eval.of_list l)
end

include Impl

module _ : Algebra.RELATIONS = Impl

(** {2 Inputs and outputs} *)

module Var = struct
  type ('a, 'b) t = ('a, 'b) Eval.t I.Var.t

  let create r = I.Var.create (Eval.of_relation r)
  let set v r = I.Var.set v (Eval.of_relation r)
  let watch v = Node (I.Var.watch v)
end

module Observer = struct
  type ('a, 'b) t = ('a, 'b) Eval.t I.Observer.t

  let value t = Eval.to_relation (I.Observer.value_exn t)
end

let observe t = I.observe (node t)
