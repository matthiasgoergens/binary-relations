(** M5: a query planner over {!Symbolic} trees.

    DataScript has no planner — its joins are hash joins folded over the
    clauses {e in the order written}. That is the gap this closes, and it
    closes with an advantage that inverts the usual difficulty:

    {v
      Immutability makes planning easier than in a real DBMS. Cardinality,
      distinct counts and fan-out are pure functions of an immutable value,
      so they are computed once, memoised on the relation, and are exact and
      never stale. A real database plans against sampled statistics that
      drift; here the planner has perfect information, for free.
    v}

    Three passes, in order.

    - {b Algebraic simplification.} Units and absorbing elements, and pushing
      [converse] down to the leaves. That last one is not cosmetic: the
      converse of a {e leaf} costs nothing at all, because it hands over an
      index that already exists, whereas the converse of a composed result has
      to materialise a new set of pairs. Rewriting [(a >> b)°] to [b° >> a°]
      turns a real cost into none.
    - {b Re-association} of composition chains, by the usual interval dynamic
      program, over exact statistics.
    - Nothing at all across a {b barrier}. An element the cost model cannot
      see through — an [opaque] predicate, a host function, a [where_] whose
      selectivity is unknown — stops re-association there rather than being
      guessed at. {!blind_spots} names them. This is the concrete form of the
      brief's warning that an opaque predicate is a hole in the {e cost model},
      not merely in the optimiser: the planner does not silently invent a
      number, it declines to reorder and says why. *)

open! Base
open Symbolic

(* ------------------------------------------------------------------ *)
(* Algebraic simplification                                            *)
(* ------------------------------------------------------------------ *)

let comp : type a b c. (a, b) Symbolic.t -> (b, c) Symbolic.t -> (a, c) Symbolic.t =
 fun x y ->
  match (x, y) with
  | Id, _ -> y
  | _, Id -> x
  | Bot, _ -> Bot
  | _, Bot -> Bot
  | _ -> Comp (x, y)

let meet_ : type a b. (a, b) Symbolic.t -> (a, b) Symbolic.t -> (a, b) Symbolic.t =
 fun x y -> match (x, y) with Bot, _ -> Bot | _, Bot -> Bot | _ -> Meet (x, y)

let join_ : type a b. (a, b) Symbolic.t -> (a, b) Symbolic.t -> (a, b) Symbolic.t =
 fun x y -> match (x, y) with Bot, _ -> y | _, Bot -> x | _ -> Join (x, y)

(* Converse distributes over everything in sight, and at a leaf it is free.
   So the right normal form is to have converses only on leaves. *)
let rec conv : type a b. (a, b) Symbolic.t -> (b, a) Symbolic.t =
 fun t ->
  match t with
  | Conv x -> x
  | Id -> Id
  | Bot -> Bot
  | Comp (x, y) -> comp (conv y) (conv x)
  | Meet (x, y) -> meet_ (conv x) (conv y)
  | Join (x, y) -> join_ (conv x) (conv y)
  | Plus x -> Plus (conv x)
  | Star x -> Star (conv x)
  | Where (n, p) -> Where (n, p) (* a coreflexive is its own converse *)
  | Leaf r -> Leaf (Relation.converse r) (* free: the indexes are shared *)
  | _ -> Conv t

let rec simplify : type a b. (a, b) Symbolic.t -> (a, b) Symbolic.t =
 fun t ->
  match t with
  | Comp (x, y) -> comp (simplify x) (simplify y)
  | Conv x -> conv (simplify x)
  | Meet (x, y) -> meet_ (simplify x) (simplify y)
  | Join (x, y) -> join_ (simplify x) (simplify y)
  | Plus x -> Plus (simplify x)
  | Star x -> Star (simplify x)
  | Group x -> Group (simplify x)
  | Fork (x, y) -> Fork (simplify x, simplify y)
  | Rdiv (x, y) -> Rdiv (simplify x, simplify y)
  | Ldiv (x, y) -> Ldiv (simplify x, simplify y)
  | Id | Bot | Fst | Snd | Where _ | Fn _ | Leaf _ -> t

(* ------------------------------------------------------------------ *)
(* Composition chains                                                  *)
(* ------------------------------------------------------------------ *)

(* A chain makes the intermediate types existential, which is what lets the
   dynamic program cut it anywhere. *)
type ('a, 'b) chain =
  | Nil : ('a, 'a) chain
  | Cons : ('a, 'b) Symbolic.t * ('b, 'c) chain -> ('a, 'c) chain

type ('a, 'c) split = Split : ('a, 'b) chain * ('b, 'c) chain -> ('a, 'c) split

let rec flatten : type a b c. (a, b) Symbolic.t -> (b, c) chain -> (a, c) chain =
 fun t rest -> match t with Comp (x, y) -> flatten x (flatten y rest) | _ -> Cons (t, rest)

let rec chain_length : type a b. (a, b) chain -> int =
 fun ch -> match ch with Nil -> 0 | Cons (_, rest) -> 1 + chain_length rest

let rec split_at : type a c. int -> (a, c) chain -> (a, c) split =
 fun n ch ->
  match (n, ch) with
  | 0, _ -> Split (Nil, ch)
  | _, Nil -> Split (Nil, Nil)
  | _, Cons (x, rest) ->
    let (Split (l, r)) = split_at (n - 1) rest in
    Split (Cons (x, l), r)

let rec right_deep : type a b. (a, b) chain -> (a, b) Symbolic.t =
 fun ch ->
  match ch with Nil -> Id | Cons (x, Nil) -> x | Cons (x, rest) -> Comp (x, right_deep rest)

(* ------------------------------------------------------------------ *)
(* The cost model                                                      *)
(* ------------------------------------------------------------------ *)

(** What the planner knows about a (sub)expression. For a leaf every field is
    exact; for an intermediate they are estimates, but estimates built from
    exact inputs rather than from a sample. *)
type info = { card : float; dom : float; rng : float }

let info_of_relation r =
  let s = Relation.stats r in
  {
    card = Float.of_int s.card;
    dom = Float.of_int s.domain_size;
    rng = Float.of_int s.range_size;
  }

let info_of : type a b. (a, b) Symbolic.t -> info option = function
  | Leaf r -> Some (info_of_relation r)
  | _ -> None

(* The textbook join-size estimate under uniformity. The uniformity assumption
   is the only guess left, because the inputs to it are not estimated. *)
let combine x y =
  let denom = Float.max 1.0 (Float.max x.rng y.dom) in
  let card = x.card *. y.card /. denom in
  { card; dom = Float.min x.dom card; rng = Float.min y.rng card }

(* Cost in tuples touched: both operands are scanned or probed, and the result
   is built. The same unit [Relation.tuples_touched] counts, so a prediction
   can be checked against a measurement. *)
let step_cost x y = x.card +. y.card +. (combine x y).card

type bracket =
  | BLeaf
  | BSplit of int * bracket * bracket  (** left segment length *)

let plan_run (infos : info array) : bracket * float =
  let n = Array.length infos in
  if n = 1 then (BLeaf, 0.0)
  else begin
    let cost = Array.make_matrix ~dimx:(n + 1) ~dimy:(n + 1) 0.0 in
    let inf = Array.make_matrix ~dimx:(n + 1) ~dimy:(n + 1) infos.(0) in
    let sp = Array.make_matrix ~dimx:(n + 1) ~dimy:(n + 1) (-1) in
    for i = 0 to n - 1 do
      inf.(i).(i + 1) <- infos.(i)
    done;
    for len = 2 to n do
      for i = 0 to n - len do
        let j = i + len in
        let best = ref Float.infinity and best_k = ref (i + 1) in
        for k = i + 1 to j - 1 do
          let c = cost.(i).(k) +. cost.(k).(j) +. step_cost inf.(i).(k) inf.(k).(j) in
          if Float.( < ) c !best then (
            best := c;
            best_k := k)
        done;
        cost.(i).(j) <- !best;
        sp.(i).(j) <- !best_k;
        inf.(i).(j) <- combine inf.(i).(!best_k) inf.(!best_k).(j)
      done
    done;
    let rec brack i j = if j - i = 1 then BLeaf else
        let k = sp.(i).(j) in
        BSplit (k - i, brack i k, brack k j)
    in
    (brack 0 n, cost.(0).(n))
  end

let rec build : type a c. bracket -> (a, c) chain -> (a, c) Symbolic.t =
 fun br ch ->
  match br with
  (* A bracket is built for a chain of a known length, so these two cases are
     unreachable. They raise rather than quietly falling back to a right-deep
     build: a planner that silently emits a different plan from the one it
     costed would still be correct, and would make every measurement above a
     lie. *)
  | BLeaf -> (
    match ch with
    | Cons (x, Nil) -> x
    | Nil -> failwith "Plan.build: bracket and chain disagree (empty segment)"
    | Cons (_, _) -> failwith "Plan.build: bracket and chain disagree (segment too long)")
  | BSplit (n, bl, brr) ->
    let (Split (l, r)) = split_at n ch in
    Comp (build bl l, build brr r)

(* Walk the chain taking the longest prefix the cost model can see all the way
   through, plan that, and start again after it. An element with no statistics
   is a barrier: re-association stops rather than guessing. *)
let rec plan_chain : type a b. (a, b) chain -> (a, b) Symbolic.t =
 fun ch ->
  let rec run_length : type x y. (x, y) chain -> int = function
    | Nil -> 0
    | Cons (x, rest) -> ( match info_of x with None -> 0 | Some _ -> 1 + run_length rest)
  in
  let rec infos_of : type x y. (x, y) chain -> int -> info list =
   fun ch n ->
    if n = 0 then []
    else match ch with
      | Nil -> []
      | Cons (x, rest) -> (match info_of x with
        | Some i -> i :: infos_of rest (n - 1)
        | None -> [])
  in
  match ch with
  | Nil -> Id
  | Cons (x, Nil) -> x
  | Cons (x, rest) ->
    let p = run_length ch in
    if p >= 2 then begin
      let infos = Array.of_list (infos_of ch p) in
      let br, _ = plan_run infos in
      let (Split (l, r)) = split_at p ch in
      let planned = build br l in
      match r with Nil -> planned | _ -> Comp (planned, plan_chain r)
    end
    else Comp (x, plan_chain rest)

(* ------------------------------------------------------------------ *)
(* The entry points                                                    *)
(* ------------------------------------------------------------------ *)

let rec reassociate : type a b. (a, b) Symbolic.t -> (a, b) Symbolic.t =
 fun t ->
  match t with
  | Comp _ ->
    let rec descend : type x y. (x, y) chain -> (x, y) chain = function
      | Nil -> Nil
      | Cons (e, rest) -> Cons (reassociate e, descend rest)
    in
    plan_chain (descend (flatten t Nil))
  | Conv x -> Conv (reassociate x)
  | Meet (x, y) -> Meet (reassociate x, reassociate y)
  | Join (x, y) -> Join (reassociate x, reassociate y)
  | Fork (x, y) -> Fork (reassociate x, reassociate y)
  | Rdiv (x, y) -> Rdiv (reassociate x, reassociate y)
  | Ldiv (x, y) -> Ldiv (reassociate x, reassociate y)
  | Plus x -> Plus (reassociate x)
  | Star x -> Star (reassociate x)
  | Group x -> Group (reassociate x)
  | Id | Bot | Fst | Snd | Where _ | Fn _ | Leaf _ -> t

let optimise t = reassociate (simplify t)

(** The estimated cost of a tree as written, in tuples touched. Composition
    chains are costed left-to-right unless they have been planned. *)
let rec estimate : type a b. (a, b) Symbolic.t -> info option * float =
 fun t ->
  match t with
  | Leaf r -> (Some (info_of_relation r), 0.0)
  | Comp (x, y) -> (
    let ix, cx = estimate x and iy, cy = estimate y in
    match (ix, iy) with
    | Some ix, Some iy -> (Some (combine ix iy), cx +. cy +. step_cost ix iy)
    | _ -> (None, cx +. cy))
  | Conv x ->
    let i, c = estimate x in
    (Option.map i ~f:(fun i -> { i with dom = i.rng; rng = i.dom }), c)
  | Meet (x, y) | Join (x, y) ->
    let ix, cx = estimate x and iy, cy = estimate y in
    let i =
      match (ix, iy) with
      | Some a, Some b ->
        Some { card = Float.max a.card b.card; dom = Float.max a.dom b.dom; rng = Float.max a.rng b.rng }
      | _ -> None
    in
    (i, cx +. cy)
  | _ -> (None, 0.0)

let estimated_cost t = snd (estimate t)

(** Where the cost model cannot see. Each of these is a place the planner
    refuses to reorder across, and knowing they are there is the difference
    between a plan that is merely bad and one that is unaccountably bad. *)
let blind_spots : type a b. (a, b) Symbolic.t -> string list =
 fun t ->
  let acc = ref [] in
  let add s = acc := s :: !acc in
  let rec go : type x y. (x, y) Symbolic.t -> unit = function
    | Where (n, _) ->
      if Symbolic.node_is_opaque n then add ("opaque predicate in where(" ^ Symbolic.string_of_node n ^ ")")
      else add ("unknown selectivity: where(" ^ Symbolic.string_of_node n ^ ")")
    | Fn _ -> add "host function: fn"
    | Id | Bot | Fst | Snd | Leaf _ -> ()
    | Conv x -> go x
    | Plus x -> add "fixpoint: closure size is not predicted"; go x
    | Star x -> add "fixpoint: closure size is not predicted"; go x
    | Group x -> go x
    | Comp (x, y) -> go x; go y
    | Meet (x, y) -> go x; go y
    | Join (x, y) -> go x; go y
    | Fork (x, y) -> go x; go y
    | Rdiv (x, y) -> go x; go y
    | Ldiv (x, y) -> go x; go y
  in
  go t;
  List.rev !acc

let explain t =
  let o = optimise t in
  let spots = blind_spots t in
  String.concat ~sep:"\n"
    ([
       "  as written : " ^ Symbolic.to_string t;
       Printf.sprintf "  estimated  : %.0f tuples" (estimated_cost t);
       "  planned    : " ^ Symbolic.to_string o;
       Printf.sprintf "  estimated  : %.0f tuples" (estimated_cost o);
     ]
    @
    match spots with
    | [] -> [ "  the cost model sees the whole program" ]
    | l -> "  blind spots:" :: List.map l ~f:(fun s -> "    - " ^ s))
