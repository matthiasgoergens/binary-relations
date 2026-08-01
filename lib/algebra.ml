(** Layer 2: the algebra, as module types cut on the joints of the structure
    lattice — category, allegory, union allegory, division allegory,
    residuated Kleene allegory. The point of cutting here rather than
    presenting one flat signature is that {e a backend advertises exactly what
    it supports}. An interpreter that can compose and take converses but cannot
    take a fixpoint satisfies {!ALLEGORY} and says so in its type.

    The signatures are also the object language. That is not a coincidence and
    it is the reason the design is tagless-final: the point-free calculus of
    relations already {e is} a typed combinator signature, so there is no
    separate syntax to define. A query is a functor
    [module Q (R : RELATIONS) = struct ... end], and interpreting it is
    applying it to {!Eval}, {!Symbolic} or an incremental backend. *)

module type CATEGORY = sig
  type ('a, 'b) t

  val id : ('a, 'a) t
  val ( >> ) : ('a, 'b) t -> ('b, 'c) t -> ('a, 'c) t
end

(** Converse and meet. The law that distinguishes an allegory from "a category
    with some extra operations" is the {e modular law},
    [(r >> s) ∧ t ⊆ r >> (s ∧ (r° >> t))]; it is not derivable and it is what
    makes the meet interact correctly with composition. It is checked in
    {!Laws}. *)
module type ALLEGORY = sig
  include CATEGORY

  val converse : ('a, 'b) t -> ('b, 'a) t
  val meet : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
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

(** Residuals — the adjoints of composition. [rdiv x y] is the largest [z] with
    [z >> y ⊆ x], and [ldiv x y] the largest [z] with [x >> z ⊆ y]. These are
    where "for all" lives once complement has been given up: [rdiv] is
    relational division, "the customers who bought every one of these
    products". *)
module type DIVISION_ALLEGORY = sig
  include UNION_ALLEGORY

  val rdiv : ('a, 'c) t -> ('b, 'c) t -> ('a, 'b) t
  val ldiv : ('a, 'b) t -> ('a, 'c) t -> ('b, 'c) t
end

(** Fixpoints. [plus] is transitive closure and [star] its reflexive variant.
    This is the first capability plain Codd cannot express and the confirmed
    business-logic case: org charts, bill-of-materials, reachability. *)
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
