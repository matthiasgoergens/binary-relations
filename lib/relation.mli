(** Layer 1: the relation value — a finite binary relation together with
    lazily built, memoised indexes and exact statistics.

    This is where the brief's central claim lives. Under immutability an index
    is a {e pure function of the relation}, so it can be computed on first use
    and {e never invalidated}. There is no [:db/index] schema decision to make,
    as there is in DataScript, and no cache to keep coherent. The same argument
    applies to statistics: cardinality, distinct counts and fan-out are pure
    functions of the value, so the planner's inputs are exact rather than
    sampled, and cannot go stale.

    {2 Access-path independence}

    A relation privileges no direction. {!image} and {!preimage} cost the same,
    and {!converse} does {e no} index work — it hands the forward index over as
    the backward one and vice versa, so turning a "map from customer to orders"
    into a "map from order to customer" is free whenever either direction has
    already been demanded. That is the concrete cash value of Codd's argument
    restated for in-memory data.

    {2 Layer 0}

    The brief budgets for a purpose-built persistent sorted structure, on the
    evidence that DataScript could not use Clojure's stock sorted set. That
    turned out not to be necessary here: [Core.Map] and [Core.Set] already
    provide O(1) [length], a [Comparator.Poly] instance that keeps the relation
    at exactly two type parameters, and [Map.symmetric_diff] — which is the
    very primitive [Incr_map] is built on, so layer 0 already carries what the
    incremental interpreter needs. See [NOTES.md].

    {2 Ordering}

    Elements are ordered by structural comparison ([Comparator.Poly]). The
    premise the whole design rests on is that a relation has exactly two type
    parameters; carrying comparators the way [Core.Map] normally does costs two
    more, and carrying them as values inside the relation makes [union] unsound
    the moment two relations built with different comparators for the same type
    meet. Structural comparison is the option that keeps the premise. Its
    limits are the usual ones — it raises on functional values, diverges on
    cyclic ones, and cannot express a domain-specific ordering such as
    case-insensitive strings; the escape hatch is to wrap the element in a type
    whose structural order {e is} the intended one. *)

open! Base

type ('a, 'b) t

type stats = {
  card : int;  (** number of pairs *)
  domain_size : int;  (** distinct left elements *)
  range_size : int;  (** distinct right elements *)
  max_fanout : int;  (** largest [image] *)
  max_fanin : int;  (** largest [preimage] *)
}
[@@deriving sexp_of]

(** {2 Construction} *)

val empty : ('a, 'b) t
val of_list : ('a * 'b) list -> ('a, 'b) t
val of_pairs : ('a * 'b) Set.Poly.t -> ('a, 'b) t
val singleton : 'a -> 'b -> ('a, 'b) t

(** {2 Observation} *)

val to_list : ('a, 'b) t -> ('a * 'b) list
(** Sorted, so it is a canonical form. *)

val pairs : ('a, 'b) t -> ('a * 'b) Set.Poly.t

val card : ('a, 'b) t -> int
(** O(1), and never forces an index. *)

val is_empty : ('a, 'b) t -> bool

val stats : ('a, 'b) t -> stats
(** Exact and memoised. Forces both indexes. *)

val fwd : ('a, 'b) t -> ('a, 'b Set.Poly.t) Map.Poly.t
val bwd : ('a, 'b) t -> ('b, 'a Set.Poly.t) Map.Poly.t
val image : ('a, 'b) t -> 'a -> 'b Set.Poly.t
val preimage : ('a, 'b) t -> 'b -> 'a Set.Poly.t
val dom : ('a, 'b) t -> 'a Set.Poly.t
val rng : ('a, 'b) t -> 'b Set.Poly.t
val mem : ('a, 'b) t -> 'a -> 'b -> bool

(** {2 Algebra} *)

val converse : ('a, 'b) t -> ('b, 'a) t
val compose : ('a, 'b) t -> ('b, 'c) t -> ('a, 'c) t
val union : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
val inter : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
val diff : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
val subset : ('a, 'b) t -> ('a, 'b) t -> bool
val equal : ('a, 'b) t -> ('a, 'b) t -> bool
val compare : ('a, 'b) t -> ('a, 'b) t -> int
val identity_on : 'a Set.Poly.t -> ('a, 'a) t
val filter : ('a, 'b) t -> f:('a -> 'b -> bool) -> ('a, 'b) t
val filter_dom : ('a, 'b) t -> f:('a -> bool) -> ('a, 'b) t
val filter_rng : ('a, 'b) t -> f:('b -> bool) -> ('a, 'b) t
val map_rng : ('a, 'b) t -> f:('b -> 'c) -> ('a, 'c) t
val map_dom : ('a, 'b) t -> f:('a -> 'c) -> ('c, 'b) t

val fork : ('a, 'b) t -> ('a, 'c) t -> ('a, 'b * 'c) t
(** Tabulation: [(a, (b, c))] whenever [(a,b)] and [(a,c)]. Products in an
    allegory, and the reason binary relations recover Codd's expressiveness
    rather than stopping at FO³. *)

val plus : ('a, 'a) t -> ('a, 'a) t
(** Transitive closure, semi-naive: each round composes only the {e new} pairs
    with the base relation, so nothing is re-derived from a pair that was
    already old. *)

val star_on_carrier : ('a, 'a) t -> ('a, 'a) t
(** Reflexive-transitive closure restricted to the elements occurring in the
    argument. Unrestricted [star] is the identity on an unbounded type and so
    is not a finite value; {!Eval} says how that is handled. *)

val group : ('a, 'b) t -> ('a, 'b list) t
(** Power transpose: each left element paired with the sorted list of its
    image. The list is a canonical set representation, so the result is an
    ordinary relation and nests without needing relations inside relations. *)

val rdiv : ('a, 'c) t -> ('b, 'c) t -> ('a, 'b) t
(** Relational division: [(a, b)] whenever every [c] related to [b] by the
    second argument is related to [a] by the first — "the customers who bought
    {e all} of these products". Universal quantification without complement,
    which is why it survives in a library that has no [top].

    This is a {b restricted residual} in the sense of Kahl (2008): the
    unrestricted residual of two finite relations need not be finite, so the
    universal condition is conjoined with existence witnesses — [a] ranges over
    the domain of the first argument and [b] over the domain of the second.
    Kahl writes the same thing as
    [(Q /● S) b c = (∀ a → Q a b → S a c) × ∃ (λ a → Q a b)]. See {!Rel.Algebra}
    and [NOTES.md]. *)

(** {2 Incremental support} *)

val delta : from:('a, 'b) t -> to_:('a, 'b) t -> ('a, 'b) t * ('a, 'b) t
(** The pairs added and the pairs removed, via [Set.symmetric_diff]. Cheap
    when the two values share structure — which they do whenever one was
    derived from the other by a union or an insert — because the traversal
    skips physically equal subtrees instead of walking both sets in full. This
    is the primitive incremental maintenance is built on, and the reason it
    exists at all is immutability: two versions of a mutable relation would
    share nothing to skip. *)

val symmetric_diff_fwd :
  ('a, 'b) t ->
  ('a, 'b) t ->
  ('a
  * [ `Left of 'b Set.Poly.t
    | `Right of 'b Set.Poly.t
    | `Unequal of 'b Set.Poly.t * 'b Set.Poly.t ])
  list
(** Keys whose forward image differs, via [Map.symmetric_diff]: cheap because
    the maps are immutable and share structure, so the traversal skips whole
    subtrees that are physically equal. Provided because this is the primitive
    [Incr_map] is built on, and therefore the one an incremental interpreter
    over relations needs. *)

(** {2 Instrumentation}

    Exposed so that claims about this layer can be {e measured} rather than
    asserted. [index_builds] is what makes "computed once, never invalidated" a
    testable statement, and [tuples_touched] is the unit the planner's cost
    model is written in. *)

val index_builds : unit -> int
val tuples_touched : unit -> int
val reset_counters : unit -> unit
