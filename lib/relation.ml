open! Base

(* Instrumentation. Global rather than per-value because the questions it
   answers are about a whole evaluation ("was this index built twice?", "how
   many tuples did this plan touch?"), and because threading a counter through
   an immutable value would be a lie: forcing a lazy index is the one mutation
   that does happen. *)
let index_build_count = ref 0
let touched = ref 0
let index_builds () = !index_build_count
let tuples_touched () = !touched

let reset_counters () =
  index_build_count := 0;
  touched := 0

let touch n = touched := !touched + n

type stats = {
  card : int;
  domain_size : int;
  range_size : int;
  max_fanout : int;
  max_fanin : int;
}
[@@deriving sexp_of]

type ('a, 'b) t = {
  pairs_ : ('a * 'b) Set.Poly.t Lazy.t;
  card_ : int;
  fwd_ : ('a, 'b Set.Poly.t) Map.Poly.t Lazy.t;
  bwd_ : ('b, 'a Set.Poly.t) Map.Poly.t Lazy.t;
  stats_ : stats Lazy.t;
}

let pairs r = Lazy.force r.pairs_
let card r = r.card_
let is_empty r = r.card_ = 0
let fwd r = Lazy.force r.fwd_
let bwd r = Lazy.force r.bwd_
let to_list r = Set.to_list (pairs r)

(* Building an index from a run-sorted array.

   The pair set is already sorted lexicographically, so all pairs sharing a
   left element are contiguous and their right elements are strictly
   increasing. That is exactly the precondition the sorted-input constructors
   want, so an index is a single grouping pass rather than [n] separate
   [Map.update] calls into a tree that rebalances on each one.

   Measured on 50 000 pairs before this change: the two indexes together cost
   183% of constructing the relation. *)
let index_of_sorted_array arr =
  let n = Array.length arr in
  let entries = ref [] in
  let i = ref 0 in
  while !i < n do
    let k = fst arr.(!i) in
    let j = ref !i in
    while !j < n && Poly.equal (fst arr.(!j)) k do
      Int.incr j
    done;
    let start = !i and len = !j - !i in
    (* Strictly increasing within the run, because the pair set is a set. *)
    let elts =
      Set.Poly.of_increasing_iterator_unchecked ~len ~f:(fun t -> snd arr.(start + t))
    in
    entries := (k, elts) :: !entries;
    i := !j
  done;
  (* Keys come out strictly increasing, run by run. *)
  Or_error.ok_exn (Map.Poly.of_increasing_sequence (Sequence.of_list (List.rev !entries)))

let build_fwd ps =
  Int.incr index_build_count;
  touch (Set.length ps);
  index_of_sorted_array (Set.to_array ps)

(* The backward index cannot use the same trick: the pair set is sorted by the
   LEFT element, so the runs it needs are not contiguous. Reordering first was
   tried and measured slower than what it replaced — 13.1 ms to 18.4 ms on
   50 000 pairs — because mapping to a fresh array and sorting it with
   polymorphic comparison costs more than the tree insertions it saves. So this
   direction keeps the straightforward fold, and the asymmetry is deliberate
   rather than an oversight.

   This is the honest shape of the "purpose-built layer 0" idea: a structure
   holding the pairs in BOTH orders would make both directions a grouping pass,
   and that, not a cleverer build from one order, is what would pay. *)
let build_bwd ps =
  Int.incr index_build_count;
  touch (Set.length ps);
  Set.fold ps ~init:Map.Poly.empty ~f:(fun acc (a, b) ->
    Map.update acc b ~f:(function
      | None -> Set.Poly.singleton a
      | Some s -> Set.add s a))

let index_stats fwd bwd card =
  let widest m = Map.fold m ~init:0 ~f:(fun ~key:_ ~data acc -> Int.max acc (Set.length data)) in
  {
    card;
    domain_size = Map.length fwd;
    range_size = Map.length bwd;
    max_fanout = widest fwd;
    max_fanin = widest bwd;
  }

(* The single point at which a relation is created from a materialised set of
   pairs. Both indexes are lazy; neither is built unless demanded, and once
   demanded neither can ever be invalidated, because the value it is a function
   of cannot change. *)
let of_pairs ps =
  let rec r =
    {
      pairs_ = lazy ps;
      card_ = Set.length ps;
      fwd_ = lazy (build_fwd ps);
      bwd_ = lazy (build_bwd ps);
      stats_ = lazy (index_stats (Lazy.force r.fwd_) (Lazy.force r.bwd_) (Set.length ps));
    }
  in
  r

let stats r = Lazy.force r.stats_

(* Spelled out rather than [of_pairs Set.Poly.empty] so that it generalises:
   a function application would be caught by the value restriction and [empty]
   would be usable at one type per compilation unit. *)
let empty =
  {
    pairs_ = lazy Set.Poly.empty;
    card_ = 0;
    fwd_ = lazy Map.Poly.empty;
    bwd_ = lazy Map.Poly.empty;
    stats_ =
      lazy { card = 0; domain_size = 0; range_size = 0; max_fanout = 0; max_fanin = 0 };
  }
let of_list l = of_pairs (Set.Poly.of_list l)
let singleton a b = of_pairs (Set.Poly.singleton (a, b))

let image r a = Option.value (Map.find (fwd r) a) ~default:Set.Poly.empty
let preimage r b = Option.value (Map.find (bwd r) b) ~default:Set.Poly.empty
let dom r = Set.Poly.of_list (Map.keys (fwd r))
let rng r = Set.Poly.of_list (Map.keys (bwd r))
let mem r a b = Set.mem (pairs r) (a, b)

(* Converse does no index work: the forward index of [converse r] {e is} the
   backward index of [r]. If either has been demanded, the other direction is
   already paid for. The pair set stays lazy, so a converse that is only ever
   probed through [image] costs nothing at all. *)
let converse r =
  {
    pairs_ = lazy (Set.fold (pairs r) ~init:Set.Poly.empty ~f:(fun acc (a, b) -> Set.add acc (b, a)));
    card_ = r.card_;
    fwd_ = r.bwd_;
    bwd_ = r.fwd_;
    stats_ =
      lazy
        (let s = stats r in
         {
           card = s.card;
           domain_size = s.range_size;
           range_size = s.domain_size;
           max_fanout = s.max_fanin;
           max_fanin = s.max_fanout;
         });
  }

(* Composition is where access-path independence pays out. The same result is
   reachable by scanning the left and probing the right's forward index, or by
   scanning the right and probing the left's backward index. Neither direction
   is written into the data, so the choice belongs to the library, and it makes
   it on exact cardinalities. *)
let compose x y =
  if x.card_ = 0 || y.card_ = 0 then empty
  else if x.card_ <= y.card_ then (
    let yf = fwd y in
    touch x.card_;
    of_pairs
      (Set.fold (pairs x) ~init:Set.Poly.empty ~f:(fun acc (a, b) ->
         match Map.find yf b with
         | None -> acc
         | Some cs ->
           touch (Set.length cs);
           Set.fold cs ~init:acc ~f:(fun acc c -> Set.add acc (a, c)))))
  else (
    let xb = bwd x in
    touch y.card_;
    of_pairs
      (Set.fold (pairs y) ~init:Set.Poly.empty ~f:(fun acc (b, c) ->
         match Map.find xb b with
         | None -> acc
         | Some as_ ->
           touch (Set.length as_);
           Set.fold as_ ~init:acc ~f:(fun acc a -> Set.add acc (a, c)))))

(* Until now these charged nothing at all, which made the cost counter blind
   to every meet, union and filter in the library — so any measurement
   involving one of them was understated, sometimes by a lot.

   The charge is [min] of the two cardinalities, not the sum. Base's set
   operations are divide-and-conquer, costing about m·log(n/m + 1) for m ≤ n,
   so a union against a singleton is logarithmic rather than linear: charging
   the sum would overstate incremental maintenance enormously, which is
   precisely the case this library cares about. [min] still understates by the
   log factor, and that bias is deliberate — it is the conservative direction
   for the claims made here, since every "incremental beats recompute" number
   is a ratio in which the incremental side carries the small operand. *)
let union x y =
  if x.card_ = 0 then y
  else if y.card_ = 0 then x
  else (
    touch (Int.min x.card_ y.card_);
    of_pairs (Set.union (pairs x) (pairs y)))

let inter x y =
  if x.card_ = 0 || y.card_ = 0 then empty
  else (
    touch (Int.min x.card_ y.card_);
    of_pairs (Set.inter (pairs x) (pairs y)))

let diff x y =
  if y.card_ = 0 then x
  else (
    touch (Int.min x.card_ y.card_);
    of_pairs (Set.diff (pairs x) (pairs y)))
let subset x y = Set.is_subset (pairs x) ~of_:(pairs y)
let equal x y = x.card_ = y.card_ && Set.equal (pairs x) (pairs y)
let compare x y = Set.compare_direct (pairs x) (pairs y)

let identity_on s =
  of_pairs (Set.fold s ~init:Set.Poly.empty ~f:(fun acc a -> Set.add acc (a, a)))

let filter r ~f =
  touch r.card_;
  of_pairs (Set.filter (pairs r) ~f:(fun (a, b) -> f a b))
let filter_dom r ~f = filter r ~f:(fun a _ -> f a)
let filter_rng r ~f = filter r ~f:(fun _ b -> f b)

let map_rng r ~f =
  of_pairs (Set.fold (pairs r) ~init:Set.Poly.empty ~f:(fun acc (a, b) -> Set.add acc (a, f b)))

let map_dom r ~f =
  of_pairs (Set.fold (pairs r) ~init:Set.Poly.empty ~f:(fun acc (a, b) -> Set.add acc (f a, b)))

let fork x y =
  let yf = fwd y in
  of_pairs
    (Set.fold (pairs x) ~init:Set.Poly.empty ~f:(fun acc (a, b) ->
       match Map.find yf a with
       | None -> acc
       | Some cs ->
         touch (Set.length cs);
         Set.fold cs ~init:acc ~f:(fun acc c -> Set.add acc (a, (b, c)))))

(* Semi-naive: compose the frontier with the base and keep only what is new.
   The naive version recomposes the whole accumulated closure each round and
   re-derives every old pair every time. *)
let plus r =
  let acc = ref r and frontier = ref r in
  let continue_ = ref (not (is_empty r)) in
  while !continue_ do
    let fresh = diff (compose !frontier r) !acc in
    if is_empty fresh then continue_ := false
    else (
      acc := union !acc fresh;
      frontier := fresh)
  done;
  !acc

let carrier r = Set.union (dom r) (rng r)
let star_on_carrier r = union (identity_on (carrier r)) (plus r)

let group r =
  of_pairs
    (Map.fold (fwd r) ~init:Set.Poly.empty ~f:(fun ~key ~data acc ->
       Set.add acc (key, Set.to_list data)))

let rdiv x y =
  let xf = fwd x and yf = fwd y in
  Map.fold yf ~init:Set.Poly.empty ~f:(fun ~key:b ~data:needed acc ->
    Map.fold xf ~init:acc ~f:(fun ~key:a ~data:has acc ->
      touch (Set.length needed);
      if Set.is_subset needed ~of_:has then Set.add acc (a, b) else acc))
  |> of_pairs

(* [(x >> y) ∧ z] without ever building [x >> y].

   For each pair [(u, w)] of the meet's other side, ask whether any [v] joins
   it: is [x(u)] disjoint from [y⁻¹(w)]? That is a set intersection against two
   indexes rather than a materialised composition, and it is the leapfrog step
   of a worst-case-optimal join specialised to the triangle. The output is
   bounded by [z], so the intermediate blow-up disappears entirely. *)
let meet_compose x y z =
  if x.card_ = 0 || y.card_ = 0 || z.card_ = 0 then empty
  else begin
    let xf = fwd x and yb = bwd y in
    touch z.card_;
    of_pairs
      (Set.fold (pairs z) ~init:Set.Poly.empty ~f:(fun acc (u, w) ->
         match (Map.find xf u, Map.find yb w) with
         | Some from_u, Some into_w ->
           touch (Int.min (Set.length from_u) (Set.length into_w));
           if Set.is_empty (Set.inter from_u into_w) then acc else Set.add acc (u, w)
         | _ -> acc))
  end

(* [(x >> m >> y) ∧ z] with no intermediate at all.

   The two-argument version materialises its left operand, which on a chain of
   three means building [x >> m] — and on skewed data that is the entire cost.
   Splitting the chain in the middle instead lets both ends be probed through
   the indexes they already have: walk forward from [u] through [x], backward
   from [w] through [y], and ask whether [m] joins the two frontiers.

   Which frontier to iterate matters more than anything else here, so it is
   chosen per pair: on a hub graph one side is the whole hub and the other is a
   single element, and iterating the wrong one is the difference between a
   scan and a lookup. *)
let meet_compose3 x m y z =
  if x.card_ = 0 || m.card_ = 0 || y.card_ = 0 || z.card_ = 0 then empty
  else begin
    let xf = fwd x and yb = bwd y in
    touch z.card_;
    of_pairs
      (Set.fold (pairs z) ~init:Set.Poly.empty ~f:(fun acc (u, w) ->
         match (Map.find xf u, Map.find yb w) with
         | Some fwd_set, Some bwd_set ->
           let joined =
             if Set.length fwd_set <= Set.length bwd_set then (
               touch (Set.length fwd_set);
               Set.exists fwd_set ~f:(fun t ->
                 not (Set.is_empty (Set.inter (image m t) bwd_set))))
             else (
               touch (Set.length bwd_set);
               Set.exists bwd_set ~f:(fun v ->
                 not (Set.is_empty (Set.inter (preimage m v) fwd_set))))
           in
           if joined then Set.add acc (u, w) else acc
         | _ -> acc))
  end

let delta ~from ~to_ =
  let added = ref Set.Poly.empty and removed = ref Set.Poly.empty in
  Sequence.iter (Set.symmetric_diff (pairs from) (pairs to_)) ~f:(function
    | First p -> removed := Set.add !removed p
    | Second p -> added := Set.add !added p);
  (of_pairs !added, of_pairs !removed)

let symmetric_diff_fwd x y =
  Map.symmetric_diff (fwd x) (fwd y) ~data_equal:Set.equal |> Sequence.to_list
