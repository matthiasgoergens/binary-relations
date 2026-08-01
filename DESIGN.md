# Relations as first-class values — project brief

**This is the brief as handed off, kept as written.** It is the record of what
was decided before any code existed, and it is deliberately not edited to match
what the code turned out to be — where implementation contradicted it, that is
recorded in [`NOTES.md`](./NOTES.md) with the reason, which is more useful than
a document that has been quietly brought into line. Self-contained: it should
work without the conversation that produced it. The reasoning behind each
decision is in [`binary-relations.md`](https://github.com/matthiasgoergens/coordinate-work/blob/master/research/binary-relations.md) and
[`datascript.md`](https://github.com/matthiasgoergens/coordinate-work/blob/master/research/datascript.md); this file is the *decisions*, not the
research.

---

## What it is

An OCaml library that makes **binary relations first-class immutable values**,
with **access-path independence** for ordinary in-memory data: you declare the
relation and write the query; the library chooses and holds the indexes.

Codd's 1970 argument — that ordering, indexing and access-path dependence are
defects — applies verbatim to in-memory values, because choosing
`(customer_id, order list) Map.t` *is* an access-path commitment. It privileges
one direction, it is a hand-chosen index, and a new query pattern means
reshaping the data and every call site with it.

**One-line pitch, Jane Street audience:** *`Incr_map`, generalised from maps to
relations.*

**One-line pitch, neutral:** *DataScript with static types* — see below; this is
the honest framing and it is narrower and better than "a generalised relational
algebra".

---

## Premises — decided, do not re-litigate

| decision | reason | argued in |
|---|---|---|
| **Binary, unnamed relations** `('a, 'b) t` | the whole type-checking win. Two type parameters, versus the row polymorphism / type-level labels that named columns force. Named-column EDSLs pay heavily for the names | `binary-relations.md` §EDSL |
| **Keep the points** — variables in the surface | point-free was inspiration only. The typing win comes from *binary*, not from *point-free*; those are independent axes. Point-free stays as a local normal form where a decision procedure needs it | §"Third constraint" |
| **All data in memory** | scope | — |
| **All relations immutable** | this is what makes the equational agenda legitimate rather than decorative — every law needs referential transparency. It also closes Codd's loop: a program *cannot* depend on an access path that is not part of the value | §"Two assumptions" |
| **Immutable interface, mutable implementation** | transients / uniqueness modes. Only values escape, so the laws still hold of the values. DataScript does exactly this | §"Immutable interface" |
| **EDSL, tagless-final** | the point-free calculus is *already* a typed combinator signature — object language and signature are the same thing. Gives theory/backend/proofs as three interpretations of one program | §EDSL |
| **Two stratified object languages** | scalars/predicates `v`, relations `t`, bridged by coreflexives. The stratification keeps the relational layer first-order, which is what stops the missing internal hom from ever biting | §"predicate opacity" |
| **OCaml / OxCaml** | signature checking gives legible errors where constraint solving gives a wall; functors sidestep the `Ord`/constrained-monad problem entirely; uniqueness modes for the mutable implementation; and the audience is Jane Street | §"Host-language fit" |

---

## Architecture

Five layers, bottom to top.

0. **Persistent sorted structures.** Expect to need a purpose-built one —
   DataScript could not use Clojure's stock sorted set and factored a B-tree
   library out into its own project. Budget for this; it is the hard part.
1. **The relation value.** A relation plus **lazily built, memoised indexes**.
   Under immutability an index is a *pure function of the relation*, so it is
   computed on first use and **never invalidated**. This is strictly better than
   DataScript, where indexing is a human `:db/index` schema decision.
2. **The algebra**, as module types cut on Pous's joints (category → allegory →
   division allegory → residuated Kleene allegory). He has already worked out
   which axioms buy which operations; cut the signatures there so a backend can
   advertise exactly what it supports.
3. **Interpreters.** One program, several meanings.
4. **Surface.** `let*` binding operators, or OxCaml comprehensions.

**In OCaml, tagless-final means programs are functors.** A query is
`module Q (R : RELATIONS) = struct ... end`, and interpretation is applying it
to `Eval`, `Symbolic` or `Incr`.

```ocaml
module type CATEGORY = sig
  type ('a, 'b) t
  val id     : ('a, 'a) t
  val ( >> ) : ('a, 'b) t -> ('b, 'c) t -> ('a, 'c) t
end

module type ALLEGORY = sig
  include CATEGORY
  val converse : ('a, 'b) t -> ('b, 'a) t
  val meet     : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
  val join     : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
  val bot      : ('a, 'b) t
  (* the modular law governs meet/composition; it is a test, see M0 *)
end

module type SCALAR = sig                        (* the stratified [v] *)
  type 'a v
  val lit    : 'a -> 'a v
  val ( =. ) : 'a v -> 'a v -> bool v
  val ( <. ) : 'a v -> 'a v -> bool v
  val opaque : ('a -> bool) -> 'a v -> bool v   (* escape hatch, VISIBLE to the planner *)
end

module type RELATIONS = sig
  include ALLEGORY
  module V : SCALAR
  val where_ : ('a V.v -> bool V.v) -> ('a, 'a) t   (* coreflexive; filter needs no combinator *)
  val fn     : ('a -> 'b) -> ('a, 'b) t             (* graph of a function *)
  val fst_   : ('a * 'b, 'a) t
  val snd_   : ('a * 'b, 'b) t
  val fork   : ('a, 'b) t -> ('a, 'c) t -> ('a, 'b * 'c) t
  val star   : ('a, 'a) t -> ('a, 'a) t             (* transitive closure *)
  val group  : ('a, 'b) t -> ('a, 'b Set.t) t       (* power transpose *)
end
```

Notes on the sketch:

- `fst_`/`snd_`/`fork` are **products in an allegory**, and they are how n-ary
  relations are recovered from binary ones. This is what pays the FO³ bill:
  Tarski's bare calculus of binary relations is strictly weaker than Codd's
  algebra, and products are what buy the expressiveness back.
- `where_` takes `'a V.v -> bool V.v`, **not** `'a -> bool`. HOAS over
  object-language terms, so the symbolic interpreter recovers the structure by
  applying to a fresh variable and the planner can push it down. `opaque` exists
  so host functions *can* be used, at a cost that shows up in the plan.
- No `apply`/currying. Rel has no internal hom. Nesting (`group`) yes, function
  space no. Higher-order combinators live in the host; the object language stays
  first-order, which is what keeps optimisation tractable.

**The three interpreters:**

| interpreter | what it is | why |
|---|---|---|
| `Eval` | naive set-at-a-time evaluation over the layer-1 values | correctness baseline; everything is tested against it |
| `Symbolic` | builds an AST | planning, printing, hashing, tests |
| `Incr` | builds a Jane Street `Incremental` graph | **the demo.** One program, run one-shot *and* as a live self-adjusting graph |

---

## Milestones

- **M0 — skeleton.** `RELATIONS` signature, `Eval`, `id`/`>>`/`converse`/`meet`/
  `join`/`bot`, relations built from lists. **Property tests generated from the
  laws** — modular law, converse involution/antidistribution, lattice laws. This
  is the first non-prose artefact and it is small.
- **M1 — the scalar language.** `SCALAR`, `where_`, `opaque`. Spike 4 sizes `v`.
- **M2 — lazy automatic indexes.** Spike 8. The first thing that is better than
  DataScript, and it falls straight out of immutability.
- **M3 — transitive closure**, semi-naive. Spike 6. The first capability plain
  Codd cannot express, and the confirmed business-logic case (org charts,
  bill-of-materials, reachability).
- **M4 — `Incr` interpreter.** Spike 7. The pitch rests on this.
- **M5 — `Symbolic` + a planner.** See below.

M0–M3 are a working library. M4 is the demo. M5 is the differentiator.

---

## The planner — why it is tractable here

DataScript has no query planner: joins are hash joins folded over the clauses
**in the order written**. Matthias's read is "probably fixable", and it is —
with one advantage worth stating, because it inverts the usual difficulty:

> **Immutability makes planning easier than in a real DBMS.** Statistics —
> cardinality, per-index distributions, distinct counts — are *pure functions of
> an immutable value*. They can be computed once, memoised on the relation, and
> are **exact and never stale**. Real databases plan against sampled statistics
> that drift; here the planner has perfect information for free.

So the M5 planner is a cost model over exact statistics, plus join ordering,
plus (later) worst-case-optimal joins. The one thing that breaks it is `opaque`
— an opaque host predicate is a hole in the cost model, not merely in the
optimiser. That is the real reason to keep `v` expressive enough that `opaque`
is rare.

---

## Live spikes

Parked ones (Python checkers, Python surfaces, the Haskell `Ord` encoding) are
in `binary-relations.md`; they revive only if the host changes.

| # | spike | budget |
|---|---|---|
| 1 | **OxCaml modes for relational contraction** — can the linear modality express "used twice, insert a copy"? Expectation: **no**. Disprove and move on | **30 min** |
| 4 | **How big must `v` be?** A dozen realistic business predicates; count how many need only comparison/arithmetic and how many need `opaque` | half a day |
| 6 | **Semi-naive evaluation** for transitive closure | half a day |
| 7 | **`Incremental` as a second interpreter** — one derived relation, built twice | 1 day |
| 8 | **Lazy automatic index selection** on an immutable relation | half a day |

Note the OxCaml distinction: **modes-for-uniqueness** (spike 0-adjacent, for the
mutable implementation) is squarely what modes are for and is solid;
**modes-for-relational-contraction** (spike 1) is speculative and expected to
fail. Do not let them borrow credibility from each other.

---

## Reading, prioritised

1. ~~DataScript~~ — **done**, see `datascript.md`.
2. **Kahl, *Semigroupoid Interfaces for Relation-Algebraic Programming in
   Haskell*** (MPC 2006). The closest existing predecessor: someone built this
   interface once and wrote down what had to bend. Matters more now, since it is
   the typed-relations interface DataScript deliberately does not have.
3. **Oliveira, `pdbc.pdf`** — the chapters on relations, products and
   coreflexives. Where `fork`/`fst_`/`where_` come from.
4. **Pous, `relation-algebra`** — for the structure lattice, i.e. which axioms
   buy which operations. Shapes the signatures even though the host is OCaml.
5. **`Incremental` / `Incr_map` docs** — before M4.
6. **Datafun** (fixpoints with monotonicity in types) and **Flix** (Datalog
   programs as first-class values, the inject–program–query pattern) — the two
   existing language-integrated designs.
7. **`chyp`** — only if a rewriting layer happens.

---

## Ruled out, with reasons

Recorded so they do not come back.

- **Named columns.** The type-level machinery is the cost the binary framing
  exists to avoid.
- **A point-free *surface*.** Point-free is theory, backend and proofs only.
- **miniKanren-style search.** It buys running-backwards, which business logic
  over known data never spends, and it costs goal-ordering-dependent termination,
  no aggregation and no planner. Converse gives the tractable fragment of
  running backwards: same directional freedom, priced as an index rather than a
  search.
- **Dhall-style totality** (no recursion). We need recursion — transitive
  closure is the point. Datalog's mechanism (no function symbols → finite
  domain) is the available one; Datafun is the version that carries it in types.
- **`concat` / compiling-to-categories.** Needs a cartesian closed category.
  **Rel is not cartesian at all** — the set product is the monoidal tensor, not
  the categorical product; the monoidal unit is not terminal; copy and discard
  exist but are not natural.
- **`ArrowApply` / currying relations.** No internal hom.
- **Term-tree rewriting as the optimiser core**, if a rewriting layer ever
  happens: it is unsound modulo the monoidal laws. The correct object is a
  hypergraph (String Diagram Rewrite Theory I–III), and a conjunctive query with
  variables *is* that hypergraph — vertices are variables, hyperedges are atoms,
  and Chandra–Merlin containment is a homomorphism of exactly those. So the
  pointful representation and the categorical one are the same object; prefer
  the database presentation, which has far better tooling.
- **Python as primary host.** Good demonstration host — `Rel[A, B]` is exactly
  what Python generics do well — but no higher-kinded types means it must go
  *initial* rather than final, losing statically-checked multiple
  interpretations.

---

## Open questions

- **Index maintenance under insertion.** Transients handle bulk building; they
  do not help one-tuple-at-a-time. One insert into a relation carrying three
  indexes touches three structures. Can index maintenance be lazy too — mark
  dirty, rebuild on next use? This is where the deferred IVM literature (DBSP,
  differential dataflow) may return.
- **Does `Incremental`'s granularity match relational change?** `Incr_map` diffs
  via `Map.symmetric_diff`, cheap because maps are immutable and share
  structure. Whether that maps cleanly onto relational deltas is the risk in M4
  and the reason spike 7 comes early.
- **How big `v` has to be** (spike 4), and therefore how often `opaque` is
  needed — which is the same as asking how often the cost model has a hole.
- **Whether the surface should be `let*`, OxCaml comprehensions, or both.**

---

## Where the detail lives

- [`binary-relations.md`](https://github.com/matthiasgoergens/coordinate-work/blob/master/research/binary-relations.md) — the full research note: the
  paper this started from (Oliveira, *Functional dependency theory made
  'simpler'*, 2005), what became of that line, the four traditions, the EDSL
  analysis, host-language fit, higher-order operations, and every caution with
  the ones that were later withdrawn marked as such.
- [`datascript.md`](https://github.com/matthiasgoergens/coordinate-work/blob/master/research/datascript.md) — the source read, the architecture, and
  the four gaps that are this project's differentiators.
