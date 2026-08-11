(** Layer 1: the relation value — a finite binary relation together with
    lazily built, memoised indexes and exact statistics.

    Under immutability an index is a {e pure function of the relation}, so it
    can be computed on first use and {e never invalidated}. There is no
    [:db/index] schema decision to make, as there is in DataScript, and no
    cache to keep coherent.

    {b What that does and does not buy.} It removes a class of bug — a stale or
    incoherent index — and the machinery that would otherwise prevent one. It
    does {e not} make an index cheap. Building one is O(n) whatever the
    language says about mutation, and the property that actually decides
    whether that cost is worth paying is how long the value stays frozen
    relative to how often it is queried. An index amortises over a long
    read-mostly lifetime, and language-level immutability is silent on that:
    a program can rebuild a relation on every tick and never amortise
    anything, while a mutable table that is frozen and then read a million
    times amortises perfectly. Immutability means a freshly bound variable
    each time, which is a statement about the language, not about churn.

    This library has measured both halves of that. Maintaining an incremental
    view costs 3 tuples in the steady state but 503 the first time a given
    intermediate is touched, because each change mints a fresh intermediate
    with no index; and the M5 correction turned on the same point — the
    intermediates a planner most wants to reason about are exactly the ones
    just created, so the memoisation barely reaches them. See [NOTES.md].

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

    Elements are ordered by structural comparison ([Comparator.Poly]) {e in the
    public API}. The premise the whole design rests on is that a relation has
    exactly two type parameters; carrying comparators the way [Core.Map]
    normally does costs two more, and carrying them as values inside the
    relation makes [union] unsound the moment two relations built with
    different comparators for the same type meet. Structural comparison is the
    option that keeps the premise. Its limits are the usual ones — it raises on
    functional values, diverges on cyclic ones, and cannot express a
    domain-specific ordering such as case-insensitive strings; the escape hatch
    is to wrap the element in a type whose structural order {e is} the intended
    one.

    Internally the representation is already comparator-parameterised — the
    record carries real comparator witnesses, in Core's shape, and this
    two-parameter interface is the instantiation at [Poly]. That is the first
    step of the port that real merlin data forced: structural comparison runs
    out of memory on values built on lazy links (see [NOTES.md]). The general
    four-parameter interface is exposed as {!General} below and is what the
    algebra and the interpreters will be ported to; this API keeps every
    witness at [Poly], pair set included, which is what allows [empty] to
    remain a value (a derived-comparator empty set cannot be a polymorphic
    value — the value restriction meets [Set.t]'s invariance). *)


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

val meet_compose : ('a, 'b) t -> ('b, 'c) t -> ('a, 'c) t -> ('a, 'c) t
(** [meet_compose x y z] is [(x >> y) ∧ z], computed without materialising
    [x >> y].

    This is the one shape where re-association cannot help: a two-relation
    composition has only one bracketing, so a cost-based planner has nothing to
    choose, and the whole cost is in building an intermediate that the meet then
    mostly discards. Meeting a composite with a base relation is also the only
    everyday way to write a {e cyclic} query in this algebra — it is the
    triangle — and cyclic queries are precisely where worst-case-optimal joins
    beat binary ones. On acyclic queries they do not: a WCO plan is equivalent
    to a left-deep binary plan, which is worse than the bushy ones {!Rel.Plan}
    already finds.

    So this is deliberately not a general WCO join engine. It is the leapfrog
    step of one, specialised to the shape that needs it, which is the direction
    Free Join (Wang, Willsey and Suciu, SIGMOD 2023) argues for: start from a
    good binary plan and fuse where it pays. *)

val meet_compose3 : ('a, 'm) t -> ('m, 'n) t -> ('n, 'b) t -> ('a, 'b) t -> ('a, 'b) t
(** [meet_compose3 x m y z] is [(x >> m >> y) ∧ z] with no intermediate built.

    {!meet_compose} materialises its left operand, so on a chain of three it
    still builds [x >> m] — measured as no help at all on a 4-cycle. Splitting
    in the middle lets both ends be probed through existing indexes: forward
    from the left endpoint through [x], backward from the right through [y],
    then ask whether [m] joins the frontiers. Which frontier is iterated is
    chosen per pair by size, which is what makes it work on skewed data. *)

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
(** Keys whose forward image differs, via [Map.symmetric_diff]. The traversal
    skips whole subtrees that are physically equal, so it is cheap {e when the
    two maps share structure} — which they do when one was derived from the
    other, and do not when they were built independently with the same
    contents. Immutability is what makes that sharing {e safe}; it is not what
    makes it cheap. Provided because this is the primitive [Incr_map] is built
    on, and therefore the one an incremental interpreter over relations
    needs. *)

(** {2 Instrumentation}

    Exposed so that claims about this layer can be {e measured} rather than
    asserted. [index_builds] is what makes "computed once, never invalidated" a
    testable statement, and [tuples_touched] is the unit the planner's cost
    model is written in. *)

val index_builds : unit -> int
val tuples_touched : unit -> int
val reset_counters : unit -> unit

(** {2 The general four-parameter interface}

    The same relation with real comparator witnesses, in Core's shape. This is
    the target of the port recorded in [NOTES.md]: the algebra and the
    interpreters move here, and this two-parameter API remains as the [Poly]
    front end.

    Two deliberate differences from the API above:

    - [empty] is a {e function} of the two comparators. A polymorphic empty
      value over a derived comparator is not expressible from outside Base
      (the value restriction meets [Set.t]'s invariance); only the [Poly]
      instantiation gets to keep [empty] as a value.
    - The pair set's witness is the {e derived product} of the two element
      witnesses, not [Poly]'s — so [General.pairs] and [pairs] return sets of
      different types, and converting between a [General.t] and a [t] is a
      rebuild, not a coercion.

    Comparators are arguments only where a genuinely new element type appears
    ([empty], [of_pairs], [of_list], [singleton], [map_rng], [map_dom]);
    everywhere else the result witness is a function of the inputs', which is
    what [Comparator.Derived2] buys. *)
module General : sig
  type ('a, 'acmp, 'b, 'bcmp) t

  type ('acmp, 'bcmp) pair_witness
  (** The witness of a pair set over elements witnessed by ['acmp] and
      ['bcmp]. Nominal to a single library-level [Comparator.Derived2]
      application, so all pair sets over the same element comparators
      unify. *)

  type 'bcmp list_witness
  (** The witness of a list-typed range, from a single library-level
      [Comparator.Derived] application; {!group}'s result. *)

  val pair_comparator :
    ('a, 'acmp) Comparator.t ->
    ('b, 'bcmp) Comparator.t ->
    ('a * 'b, ('acmp, 'bcmp) pair_witness) Comparator.t

  (** {3 Construction} *)

  val empty : ('a, 'acmp) Comparator.t -> ('b, 'bcmp) Comparator.t -> ('a, 'acmp, 'b, 'bcmp) t

  val of_pairs :
    ('a, 'acmp) Comparator.t ->
    ('b, 'bcmp) Comparator.t ->
    ('a * 'b, ('acmp, 'bcmp) pair_witness) Set.t ->
    ('a, 'acmp, 'b, 'bcmp) t

  val of_list :
    ('a, 'acmp) Comparator.Module.t ->
    ('b, 'bcmp) Comparator.Module.t ->
    ('a * 'b) list ->
    ('a, 'acmp, 'b, 'bcmp) t

  val singleton :
    ('a, 'acmp) Comparator.t -> ('b, 'bcmp) Comparator.t -> 'a -> 'b -> ('a, 'acmp, 'b, 'bcmp) t

  (** {3 Observation} *)

  val to_list : ('a, 'acmp, 'b, 'bcmp) t -> ('a * 'b) list
  val pairs : ('a, 'acmp, 'b, 'bcmp) t -> ('a * 'b, ('acmp, 'bcmp) pair_witness) Set.t
  val card : ('a, 'acmp, 'b, 'bcmp) t -> int
  val is_empty : ('a, 'acmp, 'b, 'bcmp) t -> bool
  val stats : ('a, 'acmp, 'b, 'bcmp) t -> stats
  val fwd : ('a, 'acmp, 'b, 'bcmp) t -> ('a, ('b, 'bcmp) Set.t, 'acmp) Map.t
  val bwd : ('a, 'acmp, 'b, 'bcmp) t -> ('b, ('a, 'acmp) Set.t, 'bcmp) Map.t
  val image : ('a, 'acmp, 'b, 'bcmp) t -> 'a -> ('b, 'bcmp) Set.t
  val preimage : ('a, 'acmp, 'b, 'bcmp) t -> 'b -> ('a, 'acmp) Set.t
  val dom : ('a, 'acmp, 'b, 'bcmp) t -> ('a, 'acmp) Set.t
  val rng : ('a, 'acmp, 'b, 'bcmp) t -> ('b, 'bcmp) Set.t
  val mem : ('a, 'acmp, 'b, 'bcmp) t -> 'a -> 'b -> bool

  (** {3 Algebra} *)

  val converse : ('a, 'acmp, 'b, 'bcmp) t -> ('b, 'bcmp, 'a, 'acmp) t
  val compose : ('a, 'acmp, 'b, 'bcmp) t -> ('b, 'bcmp, 'c, 'ccmp) t -> ('a, 'acmp, 'c, 'ccmp) t
  val union : ('a, 'acmp, 'b, 'bcmp) t -> ('a, 'acmp, 'b, 'bcmp) t -> ('a, 'acmp, 'b, 'bcmp) t
  val inter : ('a, 'acmp, 'b, 'bcmp) t -> ('a, 'acmp, 'b, 'bcmp) t -> ('a, 'acmp, 'b, 'bcmp) t
  val diff : ('a, 'acmp, 'b, 'bcmp) t -> ('a, 'acmp, 'b, 'bcmp) t -> ('a, 'acmp, 'b, 'bcmp) t
  val subset : ('a, 'acmp, 'b, 'bcmp) t -> ('a, 'acmp, 'b, 'bcmp) t -> bool
  val equal : ('a, 'acmp, 'b, 'bcmp) t -> ('a, 'acmp, 'b, 'bcmp) t -> bool
  val compare : ('a, 'acmp, 'b, 'bcmp) t -> ('a, 'acmp, 'b, 'bcmp) t -> int
  val identity_on : ('a, 'acmp) Set.t -> ('a, 'acmp, 'a, 'acmp) t
  val filter : ('a, 'acmp, 'b, 'bcmp) t -> f:('a -> 'b -> bool) -> ('a, 'acmp, 'b, 'bcmp) t
  val filter_dom : ('a, 'acmp, 'b, 'bcmp) t -> f:('a -> bool) -> ('a, 'acmp, 'b, 'bcmp) t
  val filter_rng : ('a, 'acmp, 'b, 'bcmp) t -> f:('b -> bool) -> ('a, 'acmp, 'b, 'bcmp) t

  val map_rng :
    ('c, 'ccmp) Comparator.t -> ('a, 'acmp, 'b, 'bcmp) t -> f:('b -> 'c) -> ('a, 'acmp, 'c, 'ccmp) t

  val map_dom :
    ('c, 'ccmp) Comparator.t -> ('a, 'acmp, 'b, 'bcmp) t -> f:('a -> 'c) -> ('c, 'ccmp, 'b, 'bcmp) t

  val fork :
    ('a, 'acmp, 'b, 'bcmp) t ->
    ('a, 'acmp, 'c, 'ccmp) t ->
    ('a, 'acmp, 'b * 'c, ('bcmp, 'ccmp) pair_witness) t
  (** No comparator argument: the result witness is derived from the inputs'. *)

  val plus : ('a, 'acmp, 'a, 'acmp) t -> ('a, 'acmp, 'a, 'acmp) t
  val star_on_carrier : ('a, 'acmp, 'a, 'acmp) t -> ('a, 'acmp, 'a, 'acmp) t

  val group : ('a, 'acmp, 'b, 'bcmp) t -> ('a, 'acmp, 'b list, 'bcmp list_witness) t

  val rdiv : ('a, 'acmp, 'c, 'ccmp) t -> ('b, 'bcmp, 'c, 'ccmp) t -> ('a, 'acmp, 'b, 'bcmp) t

  val meet_compose :
    ('a, 'acmp, 'b, 'bcmp) t ->
    ('b, 'bcmp, 'c, 'ccmp) t ->
    ('a, 'acmp, 'c, 'ccmp) t ->
    ('a, 'acmp, 'c, 'ccmp) t

  val meet_compose3 :
    ('a, 'acmp, 'm, 'mcmp) t ->
    ('m, 'mcmp, 'n, 'ncmp) t ->
    ('n, 'ncmp, 'b, 'bcmp) t ->
    ('a, 'acmp, 'b, 'bcmp) t ->
    ('a, 'acmp, 'b, 'bcmp) t

  (** {3 Incremental support} *)

  val delta :
    from:('a, 'acmp, 'b, 'bcmp) t ->
    to_:('a, 'acmp, 'b, 'bcmp) t ->
    ('a, 'acmp, 'b, 'bcmp) t * ('a, 'acmp, 'b, 'bcmp) t

  val symmetric_diff_fwd :
    ('a, 'acmp, 'b, 'bcmp) t ->
    ('a, 'acmp, 'b, 'bcmp) t ->
    ('a
    * [ `Left of ('b, 'bcmp) Set.t
      | `Right of ('b, 'bcmp) Set.t
      | `Unequal of ('b, 'bcmp) Set.t * ('b, 'bcmp) Set.t ])
    list
end
