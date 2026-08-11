(** Layer 2: the algebra, as module types cut on the joints of the structure
    lattice — semigroupoid, category, allegory, union allegory, division
    allegory, Kleene. The point of cutting here rather than presenting one flat
    signature is that {e a backend advertises exactly what it supports}. An
    interpreter that can compose and take converses but cannot take a fixpoint
    satisfies {!ALLEGORY} and says so in its type.

    {2 The identity is a joint, and the lowest one}

    The ladder starts below the category, at the {!SEMIGROUPOID}, because the
    identity is the operation this library cannot represent as a value: [id] is
    the diagonal of an unbounded type. Kahl reached the same conclusion from
    the theory side and it is the organising idea of his RATH-Agda development,
    where the whole hierarchy is built twice, once with identities and once
    without —

    {v
      finite maps or finite relations between infinite sets do not even form
      a category, since the necessary identities are not finite
    v}

    — so the split is not a local workaround, it is where the subject divides.
    The practical consequence is visible in this very file: {!plus} needs no
    identity and lives in {!KLEENE_SEMIGROUPOID}, while {!star} does and lives
    one level up. A backend that cannot supply an identity can still supply
    everything below {!CATEGORY}, and its type will say so.

    The signatures are also the object language. That is not a coincidence and
    it is the reason the design is tagless-final: the point-free calculus of
    relations already {e is} a typed combinator signature, so there is no
    separate syntax to define. A query is a functor
    [module Q (R : RELATIONS) = struct ... end], and interpreting it is
    applying it to {!Eval}, {!Symbolic} or an incremental backend. *)

open! Base

(** Composition alone. Everything here is available even when no identity can
    be represented, which for finite relations over unbounded types is the
    normal situation rather than an edge case. *)
module type SEMIGROUPOID = sig
  type ('a, 'b) t

  val ( >> ) : ('a, 'b) t -> ('b, 'c) t -> ('a, 'c) t
end

(** A semigroupoid with identities. Everything from here up assumes a value
    that this library can only represent symbolically; see {!Eval}. *)
module type CATEGORY = sig
  include SEMIGROUPOID

  val id : ('a, 'a) t
end

(** Converse and meet without an identity — Kahl's "semi-allegory". This is the
    largest fragment of the relational algebra that a backend with no
    representable identity can implement in full. *)
module type SEMI_ALLEGORY = sig
  include SEMIGROUPOID

  val converse : ('a, 'b) t -> ('b, 'a) t
  val meet : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
end

(** Converse and meet. The law that distinguishes an allegory from "a category
    with some extra operations" is the {e modular law},
    [(r >> s) ∧ t ⊆ r >> (s ∧ (r° >> t))]; it is not derivable and it is what
    makes the meet interact correctly with composition. It is checked in
    {!Laws}. *)
module type ALLEGORY = sig
  include SEMI_ALLEGORY

  val id : ('a, 'a) t
end

(** Adds joins and a bottom. Relations form a {e distributive} allegory, so
    meet distributes over join and vice versa.

    There is deliberately no [top] and no complement. Neither is a finite
    value: the universal relation on an unbounded type cannot be enumerated,
    and complement is defined in terms of it. Excluding them is what keeps
    every operation in this signature total on values. Universal
    quantification survives anyway, through {!DIVISION_ALLEGORY}. *)
module type UNION_ALLEGORY = sig
  include ALLEGORY

  val join : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
  val bot : ('a, 'b) t
end

(** Residuals — the adjoints of composition. [rdiv x y] is "the largest [z]
    with [z >> y ⊆ x]", and [ldiv x y] the largest [z] with [x >> z ⊆ y]. These
    are where "for all" lives once complement has been given up: [rdiv] is
    relational division, "the customers who bought every one of these
    products".

    The scare quotes are load-bearing. The residual of a finite relation need
    not be finite — take [y] empty and every [z] qualifies, so the largest is
    the universal relation — so what is implemented here is the {e restricted
    residual}, which conjoins an existence condition to the universal one.
    That construct is Kahl's, introduced for exactly this reason:

    {v
      Restricted residuals were first introduced by Kahl (2008) in the context
      of semigroupoids motivated by applications to finite relations between
      infinite sets, where the residuals of finite relations are not
      necessarily finite again. Restricted residuals restrict attention to the
      "interesting part" of residuals and preserve finiteness in that context.
    v}

    Consequently the Galois connection does not hold in its textbook form, and
    {!Laws} states the two that do. They are his: [rdiv-sound] is
    [/-universal′], and [rdiv-maximal-on-carrier] is
    [●/-cancel-inner : ran T ⊑ dom S → T ⊑ (T # S) ●/ S], whose guard is the
    same domain restriction. Restricted residuals require a {e domain}
    operator, which here is the coreflexive [meet id (r >> converse r)]. *)
module type DIVISION_ALLEGORY = sig
  include UNION_ALLEGORY

  val rdiv : ('a, 'c) t -> ('b, 'c) t -> ('a, 'b) t
  val ldiv : ('a, 'b) t -> ('a, 'c) t -> ('b, 'c) t
end

(** Transitive closure, which needs no identity.

    This is the first capability plain Codd cannot express and the confirmed
    business-logic case: org charts, bill-of-materials, reachability. It is
    also finite whenever its argument is, which is why it sits below the
    identity line: the closure of a finite relation only ever adds pairs
    between elements already present.

    Kahl's [KleeneSemigroupoid] is the same level — "Kleene categories without
    identities … essentially a heterogeneous version of the {e 1-free Kleene
    algebras} of Kozen (1998)" — carrying transitive closure and no star. *)
module type KLEENE_SEMIGROUPOID = sig
  include SEMIGROUPOID

  val plus : ('a, 'a) t -> ('a, 'a) t
end

(** Adds the reflexive-transitive closure, which does {e not} come for free:
    [star r] contains the identity on everything, so it is only a finite value
    once restricted to a carrier. That restriction is the concession;
    {!KLEENE_SEMIGROUPOID.plus} is not one. Kahl draws the same line, between
    [KleeneSemigroupoid] and [KleeneCategory]. *)
module type KLEENE_ALLEGORY = sig
  include DIVISION_ALLEGORY

  val plus : ('a, 'a) t -> ('a, 'a) t
  val star : ('a, 'a) t -> ('a, 'a) t
end

(** Products in an allegory. This is what pays the FO³ bill: Tarski's bare
    calculus of binary relations is strictly weaker than Codd's algebra, and
    tabulation is what buys the expressiveness back. Note that these are {e
    not} categorical products — Rel is not cartesian, the set product is the
    monoidal tensor, and the laws are inclusions rather than the equations one
    would expect. {!Laws} states the ones that do hold. *)
module type PRODUCTS = sig
  type ('a, 'b) t

  val fst_ : ('a * 'b, 'a) t
  val snd_ : ('a * 'b, 'b) t
  val fork : ('a, 'b) t -> ('a, 'c) t -> ('a, 'b * 'c) t
end

(** The scalar language: the second, smaller object language, stratified below
    the relational one.

    Two things about it are load-bearing. It is {e separate}, so predicates
    never mention relations and the relational layer stays first-order — which
    is what stops the missing internal hom from ever biting. And it is an
    object language rather than host functions, so a symbolic interpreter can
    read a predicate's structure back by applying it to a fresh variable, and a
    planner can push it down.

    {!opaque} is the escape hatch for a host function. It is deliberately
    visible: an opaque predicate is a hole in the {e cost model}, not merely in
    the optimiser, so making it nameable and printable is the point. How often
    it is needed is the measurable question — see [examples/predicates.ml]. *)
module type SCALAR = sig
  type 'a v

  val lit : 'a -> 'a v
  val int_ : int -> int v
  val str : string -> string v
  val bool_ : bool -> bool v
  val ( =. ) : 'a v -> 'a v -> bool v
  val ( <>. ) : 'a v -> 'a v -> bool v
  val ( <. ) : 'a v -> 'a v -> bool v
  val ( <=. ) : 'a v -> 'a v -> bool v
  val ( >. ) : 'a v -> 'a v -> bool v
  val ( >=. ) : 'a v -> 'a v -> bool v
  val ( &&. ) : bool v -> bool v -> bool v
  val ( ||. ) : bool v -> bool v -> bool v
  val not_ : bool v -> bool v
  val add : int v -> int v -> int v
  val sub : int v -> int v -> int v
  val mul : int v -> int v -> int v
  val fst_v : ('a * 'b) v -> 'a v
  val snd_v : ('a * 'b) v -> 'b v
  val is_prefix : string v -> prefix:string v -> bool v

  val field : name:string -> ('a -> 'b) -> 'a v -> 'b v
  (** Project out a component. This is a host function like {!opaque}, and it
      is deliberately {e not} the same thing.

      An opaque predicate is a hole in the cost model: it decides membership by
      means the planner cannot see, so its selectivity is unknown and
      re-association has to stop. A projection decides nothing. It is total,
      cheap, and its result is then compared by operations the planner {e can}
      see, so the selectivity of the surrounding predicate remains legible and
      the field is nameable in a plan.

      This entry exists because spike 4 immediately ran into it: without a
      projection, {e every} predicate over a record has to go through
      {!opaque}, and the escape hatch would have looked far more necessary than
      it is. See [examples/predicates.ml]. *)

  val opaque : name:string -> ('a -> bool) -> 'a v -> bool v
end

(** The whole surface an interpreter must provide.

    [where_] is the bridge between the two object languages: a scalar predicate
    becomes a coreflexive relation, so filtering needs no combinator of its
    own — it is composition with a sub-identity. [fn] is the graph of a host
    function, and [group] the power transpose, which is how nesting is
    expressed without a function space. There is no [apply] and no currying:
    Rel has no internal hom, higher-order combinators live in the host, and the
    object language stays first-order. *)
module type RELATIONS = sig
  include KLEENE_ALLEGORY
  include PRODUCTS with type ('a, 'b) t := ('a, 'b) t

  module V : SCALAR

  val where_ : ('a V.v -> bool V.v) -> ('a, 'a) t
  val fn : ('a -> 'b) -> ('a, 'b) t
  val group : ('a, 'b) t -> ('a, 'b list) t
  val of_list : ('a * 'b) list -> ('a, 'b) t
  val of_relation : ('a, 'b) Relation.t -> ('a, 'b) t
end

(** An interpreter whose values can be compared, which is what a law needs in
    order to be a test rather than a comment. *)
module type EQ_RELATIONS = sig
  include RELATIONS

  val equal : ('a, 'b) t -> ('a, 'b) t -> bool
  val subset : ('a, 'b) t -> ('a, 'b) t -> bool
end

(** The same ladder over comparator-carrying relations — the four-parameter
    target of the port recorded in [NOTES.md]. The rungs, the joints and the
    laws are unchanged; what changes is where comparators enter as {e value}
    arguments, which is exactly the set of places the two-parameter versions
    got one silently from [Poly]:

    - [bot], [id], [where_], [fn] take a comparator, because an unbounded or
      empty value carries no relation to recover one from;
    - [fst_]/[snd_] take a {{!Relation.General.desc} descriptor}, because a
      product comparator cannot be decomposed ([Derived2] has no inverse) and
      the descriptor is what remembers the components;
    - [of_list] takes first-class comparator modules, [of_relation] needs
      nothing — a [Relation.General.t] already carries its own;
    - everything else keeps its shape: the comparators travel {e inside} the
      values, and [fork]'s result witness is still computed from its inputs'.

    This is the concrete form of a refutation the port plan records: the move
    to four parameters does {e not} leave the signatures touching only types.
    The extra arguments are the honest price of ordering that is not
    structural. *)
module General = struct
  module type SEMIGROUPOID = sig
    type ('a, 'acmp, 'b, 'bcmp) t

    val ( >> ) : ('a, 'acmp, 'b, 'bcmp) t -> ('b, 'bcmp, 'c, 'ccmp) t -> ('a, 'acmp, 'c, 'ccmp) t
  end

  module type CATEGORY = sig
    include SEMIGROUPOID

    val id : ('a, 'acmp) Comparator.t -> ('a, 'acmp, 'a, 'acmp) t
  end

  module type SEMI_ALLEGORY = sig
    include SEMIGROUPOID

    val converse : ('a, 'acmp, 'b, 'bcmp) t -> ('b, 'bcmp, 'a, 'acmp) t
    val meet : ('a, 'acmp, 'b, 'bcmp) t -> ('a, 'acmp, 'b, 'bcmp) t -> ('a, 'acmp, 'b, 'bcmp) t
  end

  module type ALLEGORY = sig
    include SEMI_ALLEGORY

    val id : ('a, 'acmp) Comparator.t -> ('a, 'acmp, 'a, 'acmp) t
  end

  module type UNION_ALLEGORY = sig
    include ALLEGORY

    val join : ('a, 'acmp, 'b, 'bcmp) t -> ('a, 'acmp, 'b, 'bcmp) t -> ('a, 'acmp, 'b, 'bcmp) t
    val bot : ('a, 'acmp) Comparator.t -> ('b, 'bcmp) Comparator.t -> ('a, 'acmp, 'b, 'bcmp) t
  end

  module type DIVISION_ALLEGORY = sig
    include UNION_ALLEGORY

    val rdiv : ('a, 'acmp, 'c, 'ccmp) t -> ('b, 'bcmp, 'c, 'ccmp) t -> ('a, 'acmp, 'b, 'bcmp) t
    val ldiv : ('a, 'acmp, 'b, 'bcmp) t -> ('a, 'acmp, 'c, 'ccmp) t -> ('b, 'bcmp, 'c, 'ccmp) t
  end

  module type KLEENE_SEMIGROUPOID = sig
    include SEMIGROUPOID

    val plus : ('a, 'acmp, 'a, 'acmp) t -> ('a, 'acmp, 'a, 'acmp) t
  end

  module type KLEENE_ALLEGORY = sig
    include DIVISION_ALLEGORY

    val plus : ('a, 'acmp, 'a, 'acmp) t -> ('a, 'acmp, 'a, 'acmp) t
    val star : ('a, 'acmp, 'a, 'acmp) t -> ('a, 'acmp, 'a, 'acmp) t
  end

  module type PRODUCTS = sig
    type ('a, 'acmp, 'b, 'bcmp) t

    val fst_ :
      ('a * 'b, ('acmp, 'bcmp) Relation.General.pair_witness) Relation.General.desc ->
      ('a * 'b, ('acmp, 'bcmp) Relation.General.pair_witness, 'a, 'acmp) t

    val snd_ :
      ('a * 'b, ('acmp, 'bcmp) Relation.General.pair_witness) Relation.General.desc ->
      ('a * 'b, ('acmp, 'bcmp) Relation.General.pair_witness, 'b, 'bcmp) t

    val fork :
      ('a, 'acmp, 'b, 'bcmp) t ->
      ('a, 'acmp, 'c, 'ccmp) t ->
      ('a, 'acmp, 'b * 'c, ('bcmp, 'ccmp) Relation.General.pair_witness) t
  end

  module type RELATIONS = sig
    include KLEENE_ALLEGORY
    include PRODUCTS with type ('a, 'acmp, 'b, 'bcmp) t := ('a, 'acmp, 'b, 'bcmp) t

    module V : SCALAR

    val where_ : ('a, 'acmp) Comparator.t -> ('a V.v -> bool V.v) -> ('a, 'acmp, 'a, 'acmp) t
    val fn : ('b, 'bcmp) Comparator.t -> ('a -> 'b) -> ('a, 'acmp, 'b, 'bcmp) t

    val group :
      ('a, 'acmp, 'b, 'bcmp) t -> ('a, 'acmp, 'b list, 'bcmp Relation.General.list_witness) t

    val of_list :
      ('a, 'acmp) Comparator.Module.t ->
      ('b, 'bcmp) Comparator.Module.t ->
      ('a * 'b) list ->
      ('a, 'acmp, 'b, 'bcmp) t

    val of_relation : ('a, 'acmp, 'b, 'bcmp) Relation.General.t -> ('a, 'acmp, 'b, 'bcmp) t
  end

  module type EQ_RELATIONS = sig
    include RELATIONS

    val equal : ('a, 'acmp, 'b, 'bcmp) t -> ('a, 'acmp, 'b, 'bcmp) t -> bool
    val subset : ('a, 'acmp, 'b, 'bcmp) t -> ('a, 'acmp, 'b, 'bcmp) t -> bool
  end
end
