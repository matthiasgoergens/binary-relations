open! Core

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

let pairs r = force r.pairs_
let card r = r.card_
let is_empty r = r.card_ = 0
let fwd r = force r.fwd_
let bwd r = force r.bwd_
let to_list r = Set.to_list (pairs r)

let build_index ~key ~elt ps =
  incr index_build_count;
  touch (Set.length ps);
  Set.fold ps ~init:Map.Poly.empty ~f:(fun acc p ->
    Map.update acc (key p) ~f:(function
      | None -> Set.Poly.singleton (elt p)
      | Some s -> Set.add s (elt p)))

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
      fwd_ = lazy (build_index ~key:fst ~elt:snd ps);
      bwd_ = lazy (build_index ~key:snd ~elt:fst ps);
      stats_ = lazy (index_stats (force r.fwd_) (force r.bwd_) (Set.length ps));
    }
  in
  r

let stats r = force r.stats_

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
let dom r = Map.key_set (fwd r)
let rng r = Map.key_set (bwd r)
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

let union x y =
  if x.card_ = 0 then y else if y.card_ = 0 then x else of_pairs (Set.union (pairs x) (pairs y))

let inter x y =
  if x.card_ = 0 || y.card_ = 0 then empty else of_pairs (Set.inter (pairs x) (pairs y))

let diff x y = if y.card_ = 0 then x else of_pairs (Set.diff (pairs x) (pairs y))
let subset x y = Set.is_subset (pairs x) ~of_:(pairs y)
let equal x y = x.card_ = y.card_ && Set.equal (pairs x) (pairs y)
let compare x y = Set.compare_direct (pairs x) (pairs y)

let identity_on s =
  of_pairs (Set.fold s ~init:Set.Poly.empty ~f:(fun acc a -> Set.add acc (a, a)))

let filter r ~f = of_pairs (Set.filter (pairs r) ~f:(fun (a, b) -> f a b))
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

let symmetric_diff_fwd x y =
  Map.symmetric_diff (fwd x) (fwd y) ~data_equal:Set.equal |> Sequence.to_list
