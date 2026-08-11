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

(* The comparators derived from element comparators. Each functor is applied
   ONCE, here, because functor applicativity is nominal: two anonymous
   applications would not unify, and every pair set (respectively list-typed
   range) in the library has to share one witness constructor. *)
module Pair = struct
  type ('a, 'b) t = 'a * 'b

  let compare cmp_a cmp_b (a1, b1) (a2, b2) =
    match cmp_a a1 a2 with
    | 0 -> cmp_b b1 b2
    | n -> n

  let sexp_of_t sexp_a sexp_b (a, b) = Sexp.List [ sexp_a a; sexp_b b ]
end

module Pcmp = Comparator.Derived2 (Pair)

module List_cmp = Comparator.Derived (struct
  type 'a t = 'a list

  let compare = List.compare
  let sexp_of_t = List.sexp_of_t
end)

(* The relation record, parameterised on both comparator witnesses AND on the
   pair set's witness ['pw]. Keeping ['pw] free is what lets the public
   two-parameter API fix it at [Poly]:

   a polymorphic [empty] VALUE is only possible because [Set.Poly.empty] is a
   Base-provided polymorphic value. An empty set with a DERIVED comparator can
   only be produced by a function call, and the value restriction refuses to
   generalise those — the element type is invariant in [Set.t], so the relaxed
   restriction does not apply. (Verified on the compiler: neither a record
   literal nor a functor body lifts it.) Had the public pair sets used the
   derived witness, [empty] — and with it the algebra's [bot] — would have had
   to become a function. With ['pw] = [Poly] in the public API, every public
   signature is unchanged; the general four-parameter interface lives in
   [General] below and derives its pair witnesses instead. *)
type ('a, 'acmp, 'b, 'bcmp, 'pw) g = {
  ca : ('a, 'acmp) Comparator.t;
  cb : ('b, 'bcmp) Comparator.t;
  pairs_ : ('a * 'b, 'pw) Set.t Lazy.t;
  card_ : int;
  fwd_ : ('a, ('b, 'bcmp) Set.t, 'acmp) Map.t Lazy.t;
  bwd_ : ('b, ('a, 'acmp) Set.t, 'bcmp) Map.t Lazy.t;
  stats_ : stats Lazy.t;
}

type ('a, 'b) t =
  ('a, Comparator.Poly.comparator_witness, 'b, Comparator.Poly.comparator_witness, Comparator.Poly.comparator_witness) g

let pair_cmp ca cb = Pcmp.comparator ca cb
let poly = Comparator.Poly.comparator

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

   Runs are delimited by the CARRIED comparator, not [Poly.equal]: with a
   user comparator in force, structurally different left elements can be the
   same key, and the run structure must follow the comparator or the index and
   the pair set would disagree about what a key is.

   Measured on 50 000 pairs before this change: the two indexes together cost
   183% of constructing the relation. *)
let index_of_sorted_array (ca : (_, _) Comparator.t) cb arr =
  let n = Array.length arr in
  let entries = ref [] in
  let i = ref 0 in
  while !i < n do
    let k = fst arr.(!i) in
    let j = ref !i in
    while !j < n && ca.compare (fst arr.(!j)) k = 0 do
      Int.incr j
    done;
    let start = !i and len = !j - !i in
    (* Strictly increasing within the run, because the pair set is a set. *)
    let elts =
      Set.Using_comparator.of_increasing_iterator_unchecked ~comparator:cb ~len ~f:(fun t ->
        snd arr.(start + t))
    in
    entries := (k, elts) :: !entries;
    i := !j
  done;
  (* Keys come out strictly increasing, run by run. *)
  Or_error.ok_exn
    (Map.Using_comparator.of_increasing_sequence ~comparator:ca (Sequence.of_list (List.rev !entries)))

let build_fwd ca cb ps =
  Int.incr index_build_count;
  touch (Set.length ps);
  index_of_sorted_array ca cb (Set.to_array ps)

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
let build_bwd ca cb ps =
  Int.incr index_build_count;
  touch (Set.length ps);
  Set.fold ps ~init:(Map.Using_comparator.empty ~comparator:cb) ~f:(fun acc (a, b) ->
    Map.update acc b ~f:(function
      | None -> Set.Using_comparator.singleton ~comparator:ca a
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
let of_pairs_g ca cb ps =
  let rec r =
    {
      ca;
      cb;
      pairs_ = lazy ps;
      card_ = Set.length ps;
      fwd_ = lazy (build_fwd ca cb ps);
      bwd_ = lazy (build_bwd ca cb ps);
      stats_ = lazy (index_stats (Lazy.force r.fwd_) (Lazy.force r.bwd_) (Set.length ps));
    }
  in
  r

let stats r = Lazy.force r.stats_

(* [pcmp] is the comparator of the pair type, which the callers choose:
   [Poly] in the public API, the derived product in [General]. *)
let empty_g ca cb pcmp =
  {
    ca;
    cb;
    pairs_ = lazy (Set.Using_comparator.empty ~comparator:pcmp);
    card_ = 0;
    fwd_ = lazy (Map.Using_comparator.empty ~comparator:ca);
    bwd_ = lazy (Map.Using_comparator.empty ~comparator:cb);
    stats_ =
      lazy { card = 0; domain_size = 0; range_size = 0; max_fanout = 0; max_fanin = 0 };
  }

(* A record of values, not [empty_g poly poly poly], so that it generalises:
   an application would be caught by the value restriction and [empty] would
   be usable at one type per compilation unit. See the note on [g] above. *)
let empty =
  {
    ca = poly;
    cb = poly;
    pairs_ = lazy Set.Poly.empty;
    card_ = 0;
    fwd_ = lazy Map.Poly.empty;
    bwd_ = lazy Map.Poly.empty;
    stats_ =
      lazy { card = 0; domain_size = 0; range_size = 0; max_fanout = 0; max_fanin = 0 };
  }

let of_pairs ps = of_pairs_g poly poly ps
let of_list l = of_pairs (Set.Poly.of_list l)
let singleton a b = of_pairs (Set.Poly.singleton (a, b))

let image r a =
  Option.value (Map.find (fwd r) a) ~default:(Set.Using_comparator.empty ~comparator:r.cb)

let preimage r b =
  Option.value (Map.find (bwd r) b) ~default:(Set.Using_comparator.empty ~comparator:r.ca)

let dom r = Set.Using_comparator.of_list ~comparator:r.ca (Map.keys (fwd r))
let rng r = Set.Using_comparator.of_list ~comparator:r.cb (Map.keys (bwd r))
let mem r a b = Set.mem (pairs r) (a, b)

(* Converse does no index work: the forward index of [converse r] {e is} the
   backward index of [r]. If either has been demanded, the other direction is
   already paid for. The pair set stays lazy, so a converse that is only ever
   probed through [image] costs nothing at all. *)
let converse_g ~pcmp r =
  {
    ca = r.cb;
    cb = r.ca;
    pairs_ =
      lazy
        (Set.fold (pairs r)
           ~init:(Set.Using_comparator.empty ~comparator:pcmp)
           ~f:(fun acc (a, b) -> Set.add acc (b, a)));
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

let converse r = converse_g ~pcmp:poly r

(* Composition is where access-path independence pays out. The same result is
   reachable by scanning the left and probing the right's forward index, or by
   scanning the right and probing the left's backward index. Neither direction
   is written into the data, so the choice belongs to the library, and it makes
   it on exact cardinalities. *)
let compose_g ~pcmp x y =
  if x.card_ = 0 || y.card_ = 0 then empty_g x.ca y.cb pcmp
  else if x.card_ <= y.card_ then (
    let yf = fwd y in
    touch x.card_;
    of_pairs_g x.ca y.cb
      (Set.fold (pairs x)
         ~init:(Set.Using_comparator.empty ~comparator:pcmp)
         ~f:(fun acc (a, b) ->
           match Map.find yf b with
           | None -> acc
           | Some cs ->
             touch (Set.length cs);
             Set.fold cs ~init:acc ~f:(fun acc c -> Set.add acc (a, c)))))
  else (
    let xb = bwd x in
    touch y.card_;
    of_pairs_g x.ca y.cb
      (Set.fold (pairs y)
         ~init:(Set.Using_comparator.empty ~comparator:pcmp)
         ~f:(fun acc (b, c) ->
           match Map.find xb b with
           | None -> acc
           | Some as_ ->
             touch (Set.length as_);
             Set.fold as_ ~init:acc ~f:(fun acc a -> Set.add acc (a, c)))))

let compose x y = compose_g ~pcmp:poly x y

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
    of_pairs_g x.ca x.cb (Set.union (pairs x) (pairs y)))

let inter x y =
  if x.card_ = 0 || y.card_ = 0 then empty_g x.ca x.cb (Set.comparator (pairs x))
  else (
    touch (Int.min x.card_ y.card_);
    of_pairs_g x.ca x.cb (Set.inter (pairs x) (pairs y)))

let diff x y =
  if y.card_ = 0 then x
  else (
    touch (Int.min x.card_ y.card_);
    of_pairs_g x.ca x.cb (Set.diff (pairs x) (pairs y)))

let subset x y = Set.is_subset (pairs x) ~of_:(pairs y)
let equal x y = x.card_ = y.card_ && Set.equal (pairs x) (pairs y)
let compare x y = Set.compare_direct (pairs x) (pairs y)

let identity_on_g ~pcmp s =
  let ca = Set.comparator s in
  of_pairs_g ca ca
    (Set.fold s
       ~init:(Set.Using_comparator.empty ~comparator:pcmp)
       ~f:(fun acc a -> Set.add acc (a, a)))

let identity_on s = identity_on_g ~pcmp:poly s

let filter r ~f =
  touch r.card_;
  of_pairs_g r.ca r.cb (Set.filter (pairs r) ~f:(fun (a, b) -> f a b))

let filter_dom r ~f = filter r ~f:(fun a _ -> f a)
let filter_rng r ~f = filter r ~f:(fun _ b -> f b)

let map_rng_g ~cb' ~pcmp r ~f =
  of_pairs_g r.ca cb'
    (Set.fold (pairs r)
       ~init:(Set.Using_comparator.empty ~comparator:pcmp)
       ~f:(fun acc (a, b) -> Set.add acc (a, f b)))

let map_rng r ~f = map_rng_g ~cb':poly ~pcmp:poly r ~f

let map_dom_g ~ca' ~pcmp r ~f =
  of_pairs_g ca' r.cb
    (Set.fold (pairs r)
       ~init:(Set.Using_comparator.empty ~comparator:pcmp)
       ~f:(fun acc (a, b) -> Set.add acc (f a, b)))

let map_dom r ~f = map_dom_g ~ca':poly ~pcmp:poly r ~f

(* The general version's result witness is a FUNCTION of the two input
   witnesses, so [General.fork] takes no comparator argument and the algebra
   keeps its shape. *)
let fork_g ~cbc ~pcmp x y =
  let yf = fwd y in
  of_pairs_g x.ca cbc
    (Set.fold (pairs x)
       ~init:(Set.Using_comparator.empty ~comparator:pcmp)
       ~f:(fun acc (a, b) ->
         match Map.find yf a with
         | None -> acc
         | Some cs ->
           touch (Set.length cs);
           Set.fold cs ~init:acc ~f:(fun acc c -> Set.add acc (a, (b, c)))))

let fork x y = fork_g ~cbc:poly ~pcmp:poly x y

(* Semi-naive: compose the frontier with the base and keep only what is new.
   The naive version recomposes the whole accumulated closure each round and
   re-derives every old pair every time.

   The pair comparator is recovered from the relation itself — [plus] forces
   the pair set on the first round anyway, and recovering it keeps the
   closure's pairs in the same order the base relation already uses. *)
let plus r =
  let pcmp = Set.comparator (pairs r) in
  let acc = ref r and frontier = ref r in
  let continue_ = ref (not (is_empty r)) in
  while !continue_ do
    let fresh = diff (compose_g ~pcmp !frontier r) !acc in
    if is_empty fresh then continue_ := false
    else (
      acc := union !acc fresh;
      frontier := fresh)
  done;
  !acc

let carrier r = Set.union (dom r) (rng r)
let star_on_carrier r = union (identity_on_g ~pcmp:(Set.comparator (pairs r)) (carrier r)) (plus r)

let group_g ~cbl ~pcmp r =
  of_pairs_g r.ca cbl
    (Map.fold (fwd r)
       ~init:(Set.Using_comparator.empty ~comparator:pcmp)
       ~f:(fun ~key ~data acc -> Set.add acc (key, Set.to_list data)))

let group r = group_g ~cbl:poly ~pcmp:poly r

let rdiv_g ~pcmp x y =
  let xf = fwd x and yf = fwd y in
  Map.fold yf
    ~init:(Set.Using_comparator.empty ~comparator:pcmp)
    ~f:(fun ~key:b ~data:needed acc ->
      Map.fold xf ~init:acc ~f:(fun ~key:a ~data:has acc ->
        touch (Set.length needed);
        if Set.is_subset needed ~of_:has then Set.add acc (a, b) else acc))
  |> of_pairs_g x.ca y.ca

let rdiv x y = rdiv_g ~pcmp:poly x y

(* [(x >> y) ∧ z] without ever building [x >> y].

   For each pair [(u, w)] of the meet's other side, ask whether any [v] joins
   it: is [x(u)] disjoint from [y⁻¹(w)]? That is a set intersection against two
   indexes rather than a materialised composition, and it is the leapfrog step
   of a worst-case-optimal join specialised to the triangle. The output is
   bounded by [z], so the intermediate blow-up disappears entirely. *)
let meet_compose_g ~pcmp x y z =
  if x.card_ = 0 || y.card_ = 0 || z.card_ = 0 then empty_g x.ca y.cb pcmp
  else begin
    let xf = fwd x and yb = bwd y in
    touch z.card_;
    of_pairs_g x.ca y.cb
      (Set.fold (pairs z)
         ~init:(Set.Using_comparator.empty ~comparator:pcmp)
         ~f:(fun acc (u, w) ->
           match (Map.find xf u, Map.find yb w) with
           | Some from_u, Some into_w ->
             touch (Int.min (Set.length from_u) (Set.length into_w));
             if Set.is_empty (Set.inter from_u into_w) then acc else Set.add acc (u, w)
           | _ -> acc))
  end

let meet_compose x y z = meet_compose_g ~pcmp:poly x y z

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
let meet_compose3_g ~pcmp x m y z =
  if x.card_ = 0 || m.card_ = 0 || y.card_ = 0 || z.card_ = 0 then empty_g x.ca y.cb pcmp
  else begin
    let xf = fwd x and yb = bwd y in
    touch z.card_;
    of_pairs_g x.ca y.cb
      (Set.fold (pairs z)
         ~init:(Set.Using_comparator.empty ~comparator:pcmp)
         ~f:(fun acc (u, w) ->
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

let meet_compose3 x m y z = meet_compose3_g ~pcmp:poly x m y z

let delta ~from ~to_ =
  let pcmp = Set.comparator (pairs from) in
  let added = ref (Set.Using_comparator.empty ~comparator:pcmp)
  and removed = ref (Set.Using_comparator.empty ~comparator:pcmp) in
  Sequence.iter (Set.symmetric_diff (pairs from) (pairs to_)) ~f:(function
    | First p -> removed := Set.add !removed p
    | Second p -> added := Set.add !added p);
  (of_pairs_g from.ca from.cb !added, of_pairs_g from.ca from.cb !removed)

let symmetric_diff_fwd x y =
  Map.symmetric_diff (fwd x) (fwd y) ~data_equal:Set.equal |> Sequence.to_list

(* The general four-parameter interface: the same relation, with the pair
   set's witness fixed at the derived product of the two element witnesses.
   This is the shape the algebra and the interpreters are ported to next; the
   two-parameter API above is what existing consumers see, and it is NOT a
   special case of this one — converting between the two is a rebuild of the
   pair set, because their ['pw] differs. Here [empty] is a function, as it
   must be: an empty set over a derived comparator is not a Base-provided
   value the way [Set.Poly.empty] is. *)
module General = struct
  type ('a, 'acmp, 'b, 'bcmp) t = ('a, 'acmp, 'b, 'bcmp, ('acmp, 'bcmp) Pcmp.comparator_witness) g
  type ('acmp, 'bcmp) pair_witness = ('acmp, 'bcmp) Pcmp.comparator_witness
  type 'bcmp list_witness = 'bcmp List_cmp.comparator_witness

  let pair_comparator = pair_cmp
  let list_comparator = List_cmp.comparator

  let ca r = r.ca
  let cb r = r.cb

  let empty ca cb = empty_g ca cb (pair_cmp ca cb)
  let of_pairs = of_pairs_g

  let of_list_with ca cb l =
    of_pairs_g ca cb (Set.Using_comparator.of_list ~comparator:(pair_cmp ca cb) l)

  (* A comparator that remembers how it was built. Projections need to take a
     product comparator apart, and [Comparator.Derived2] has no inverse, so the
     decomposition has to happen on this descriptor instead.

     The recovery is partial by construction: nothing stops [Base c] being
     built at a product witness type ([pair_comparator] is public, so the
     witness offers no protection), and the type checker does not refute it.
     Every construction site inside the library maintains "no [Base] at a
     product witness", and the projections below ANNOUNCE the degraded state
     rather than returning something plausible — the same rule this project
     applies elsewhere: an invariant held by construction, not by type. *)
  type ('a, 'w) desc =
    | Base : ('a, 'w) Comparator.t -> ('a, 'w) desc
    | Prod : ('a, 'wa) desc * ('b, 'wb) desc -> ('a * 'b, ('wa, 'wb) pair_witness) desc

  let rec comparator_of_desc : type a w. (a, w) desc -> (a, w) Comparator.t = function
    | Base c -> c
    | Prod (da, db) -> pair_cmp (comparator_of_desc da) (comparator_of_desc db)

  let fst_comparator : type a b ac bc. (a * b, (ac, bc) pair_witness) desc -> (a, ac) Comparator.t =
    function
    | Prod (da, _) -> comparator_of_desc da
    | Base _ ->
      invalid_arg
        "Relation.General.fst_comparator: a bare comparator at a product witness cannot be \
         decomposed; build the descriptor with Prod"

  let snd_comparator : type a b ac bc. (a * b, (ac, bc) pair_witness) desc -> (b, bc) Comparator.t =
    function
    | Prod (_, db) -> comparator_of_desc db
    | Base _ ->
      invalid_arg
        "Relation.General.snd_comparator: a bare comparator at a product witness cannot be \
         decomposed; build the descriptor with Prod"

  let of_list (type a ac b bc)
        (module A : Comparator.S with type t = a and type comparator_witness = ac)
        (module B : Comparator.S with type t = b and type comparator_witness = bc)
        (l : (a * b) list) =
    of_pairs_g A.comparator B.comparator
      (Set.Using_comparator.of_list ~comparator:(pair_cmp A.comparator B.comparator) l)

  let singleton ca cb a b =
    of_pairs_g ca cb (Set.Using_comparator.singleton ~comparator:(pair_cmp ca cb) (a, b))

  let pairs = pairs
  let card = card
  let is_empty = is_empty
  let fwd = fwd
  let bwd = bwd
  let to_list = to_list
  let stats = stats
  let image = image
  let preimage = preimage
  let dom = dom
  let rng = rng
  let mem = mem
  let subset = subset
  let equal = equal
  let compare = compare
  let union = union
  let inter = inter
  let diff = diff
  let filter = filter
  let filter_dom = filter_dom
  let filter_rng = filter_rng
  let plus = plus
  let star_on_carrier = star_on_carrier
  let delta = delta
  let symmetric_diff_fwd = symmetric_diff_fwd

  let converse r = converse_g ~pcmp:(pair_cmp r.cb r.ca) r
  let compose x y = compose_g ~pcmp:(pair_cmp x.ca y.cb) x y

  let identity_on s =
    let ca = Set.comparator s in
    identity_on_g ~pcmp:(pair_cmp ca ca) s

  let map_rng cb' r ~f = map_rng_g ~cb' ~pcmp:(pair_cmp r.ca cb') r ~f
  let map_dom ca' r ~f = map_dom_g ~ca' ~pcmp:(pair_cmp ca' r.cb) r ~f

  let fork x y =
    let cbc = pair_cmp x.cb y.cb in
    fork_g ~cbc ~pcmp:(pair_cmp x.ca cbc) x y

  let group r =
    let cbl = List_cmp.comparator r.cb in
    group_g ~cbl ~pcmp:(pair_cmp r.ca cbl) r

  let rdiv x y = rdiv_g ~pcmp:(pair_cmp x.ca y.ca) x y
  let meet_compose x y z = meet_compose_g ~pcmp:(pair_cmp x.ca y.cb) x y z
  let meet_compose3 x m y z = meet_compose3_g ~pcmp:(pair_cmp x.ca y.cb) x m y z
end
