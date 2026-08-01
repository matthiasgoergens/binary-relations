# Implementation notes

Where the code departs from [`DESIGN.md`](./DESIGN.md), and why. The brief is
kept as it was handed off; this is the record of what happened when it met a
compiler. Decisions and reasons, not state — the state is in the code and in
`git log`.

## What the brief got right and the code did not have to argue with

M0–M5 are all in, and the shape held: five layers, three interpreters, one
program written as a functor over `RELATIONS`. Nothing below is a retreat from
the premises in the brief's "do not re-litigate" table. Binary and unnamed,
points kept, everything immutable, tagless-final, two stratified object
languages — all of those paid off exactly as argued.

## Layer 0: not built, and that is the finding

The brief budgets for a purpose-built persistent sorted structure and calls it
the hard part, on the evidence that DataScript could not use Clojure's stock
sorted set and had to factor out a B-tree library.

That was not necessary here. `Core.Map` and `Core.Set` already provide the
three things this design actually needs:

- **O(1) `length`**, so exact cardinality statistics are free rather than a
  traversal;
- **`Comparator.Poly`**, which keeps a relation at exactly two type
  parameters — the premise everything else rests on;
- **`Map.symmetric_diff` / `Set.symmetric_diff`**, which skip physically equal
  subtrees. That is the primitive `Incr_map` is built on, so layer 0 already
  carried what M4 needed.

The reason DataScript's constraint does not transfer is that its sorted set is
a set of *datoms* compared on a rotating subset of four fields; ours is a set
of pairs. Try the stock thing first.

**What would make a purpose-built structure worth it later:** the pair set and
the two indexes are three separate structures over the same data. A structure
that let the indexes share the pair set's spine would cut allocation by
roughly a third and make an index build a traversal rather than a rebuild.
That is a measured optimisation to reach for when allocation shows up in a
profile, not a prerequisite.

## Ordering is structural

Elements are compared with `Comparator.Poly`, i.e. structural comparison.

The alternative was to carry comparators the way `Core.Map` normally does,
which costs two more type parameters — and two type parameters is the whole
type-checking win the binary framing exists to buy. Carrying them as *values*
inside the relation keeps the type but is unsound: two relations built with
different comparators for the same type meeting in a `union` would dedup
inconsistently, silently.

Cost, stated plainly: it raises on functional values, diverges on cyclic ones,
and cannot express a domain-specific order such as case-insensitive strings.
The escape hatch is to wrap the element in a type whose structural order *is*
the intended one. If this ever becomes the binding constraint, the fix is
OxCaml's or a future OCaml's ability to carry the comparator without widening
the type — not a fourth type parameter.

## The signature ladder, and two operations that are not there

The brief sketches one flat `ALLEGORY`. The code cuts it as the brief says it
wants: `CATEGORY` → `ALLEGORY` (converse, meet) → `UNION_ALLEGORY` (join, bot)
→ `DIVISION_ALLEGORY` (residuals) → `KLEENE_ALLEGORY` (plus, star), with
`PRODUCTS` separate. A backend then advertises exactly what it supports.

**There is no `top` and no complement.** Neither is a finite value: the
universal relation on an unbounded type cannot be enumerated, and complement is
defined from it. Excluding them is what makes every other operation total on
values.

That exclusion has a consequence I did not anticipate and the property tests
found:

> **The residual's universal property is false as usually stated.** The
> textbook law is `z ⊆ x / y ⟺ z >> y ⊆ x`. Take `y` empty: then `z >> y ⊆ x`
> holds for *every* `z`, so `x / y` would have to be `top`. The Galois
> connection and the finiteness of a relation value cannot both be had.

The library keeps finiteness. `rdiv` returns the finite-carrier residual, and
`Laws` states what actually holds: soundness in full, cancellation in full, and
maximality restricted to the carriers the operation can see. Division still
does the job it was wanted for — "customers who bought *all* of these
products" — because that question always has a finite carrier.

`star` is restricted the same way, and for the same reason: unrestricted `star`
is reflexive on the whole type, so `star r` is reflexive only on the carrier of
`r`. The Kleene laws in `Laws` are the carrier-restricted ones.

## `Eval` has three constructors

Three operations in the signature are not finite values — `id`, `fn f`,
`where_ p` — so an evaluated relation is a materialised relation, a
coreflexive, or a partial function graph. The finite case absorbs the others on
contact: composing a relation with a coreflexive is a filter, with a function
is a map.

Every combination that *would* be infinite raises `Unbounded` naming the
operation, rather than diverging or returning something wrong. `converse (fn
f)` really is "run this function backwards" and the library says it cannot;
`materialise ~dom` gives it a carrier, after which converse is free. This is
not a wart to apologise for — it is the shape of the domain, made visible.

## `SCALAR` gained `field`

Not in the brief, and spike 4 forced it within minutes. Without a projection,
*every* predicate over a record has to go through `opaque`, because there is no
way to say "the `qty` field". The spike would have reported 14 of 14 predicates
needing the escape hatch, and the design would have looked unworkable on a
measurement that was really about a missing combinator.

The distinction that makes the count mean anything: **an opaque predicate is a
selectivity hole; a projection is not.** A projection decides nothing, is
total, and the comparison wrapped around it stays visible to the planner. They
are different things and conflating them makes the escape hatch look far more
necessary than it is.

Residual cost: `field ~name:"qty" (fun o -> o.qty) o` names the field twice.
That is a ppx's job.

## The planner refuses rather than guesses

`Plan` does algebraic simplification, then re-associates composition chains by
interval DP over exact statistics, and does **nothing across a barrier** — an
element whose cardinality it cannot know. `Plan.blind_spots` names them.

This is the operational form of the brief's point that an opaque predicate is a
hole in the cost model rather than in the optimiser. The planner does not
invent a selectivity constant; it declines to reorder and says why.

**Statistics are exact and never stale, but they are not free.**
`Relation.stats` forces both indexes, so planning a three-leaf chain cold costs
six index builds. My first measurement charged that to the planned run only and
concluded the plan was slower than the order written. The honest comparison
gives both sides the same information — the indexes get built either way,
because execution needs them — and reports the one-time cost separately.

**Index *selection* is trivial here, and that is a consequence of the binary
framing.** A binary relation has exactly two directions, so there is nothing to
select: build whichever is asked for. With named n-ary relations, choosing
which composite indexes to maintain is a real search problem. This is an
unadvertised dividend of the decision the brief made for type-checking reasons.

## `Incr`: insert-only deltas, and where DBSP would start

Two effects, kept apart because only one is `Incremental`'s doing. Node-level
cutoff comes free from the graph. Delta propagation inside composition does
not: a recomputing node diffs its inputs against what it saw last time and
extends the previous output by `Δx >> y ∪ x >> Δy`, which is distributivity and
nothing more.

**Deletion recomputes.** A deleted pair may still be derivable another way, and
getting that right without multiplicities means counting derivations — which is
what Z-sets and DBSP are for. The brief files DBSP under "the optimisation for
the versioned case"; this is precisely the boundary at which it would have to
be picked up. Tested that the fallback stays correct, including a mixed
insert-and-delete, because a wrong incremental view is much worse than a slow
one.

`Incremental.Make ()` is generative, so this module holds one graph for the
whole program. Fine for a demonstration, wrong for a library someone embeds;
the fix is to make it a functor over the state.

## Spike results

| # | spike | status |
|---|---|---|
| 4 | how big must `v` be? | **done** — 4 of 14 predicates need `opaque` (29%), and the projection finding above. `examples/predicates.ml` |
| 6 | semi-naive evaluation | **done** — 21.5× fewer tuples touched than the naive fixpoint on a 30-link chain |
| 7 | `Incremental` as a second interpreter | **done** — 751× on a one-tuple insert; the deletion boundary is real and documented |
| 8 | lazy automatic index selection | **done** — and it collapsed into index *building*, see above |
| 1 | OxCaml modes for relational contraction | **not attempted.** The project-local switch is a stock 5.3.0 compiler, and this spike needs OxCaml. The brief expects it to fail; the 30-minute budget is intact and unspent |

## Open questions, updated

- **Index maintenance under insertion** — partly answered. Insertion is
  maintained by delta; deletion falls back. The lazy-rebuild idea in the brief
  turned out to be unnecessary for the insert case and insufficient for the
  delete case, which is a Z-set problem instead.
- **Does `Incremental`'s granularity match relational change?** — yes,
  measured. `Set.symmetric_diff` on pair sets is the right unit, and it is
  cheap for exactly the reason `Incr_map`'s is: immutable structures share.
- **How often is `opaque` needed?** — 29% on this sample of fourteen, and three
  of the four are closable by adding ordinary scalar operations.
- **`let*` or comprehensions for the surface** — not attempted. The library
  surface is still the raw combinators.

## Not done

- No surface syntax layer (binding operators or comprehensions).
- No worst-case-optimal joins; the planner does binary joins only.
- Filter pushdown is not implemented — `where_` re-associates within a chain
  but is not pushed through `meet` or `fork`.
- No transients or uniqueness-mode builder. Bulk construction goes through
  `of_list`, which is fine at these sizes and is the next thing to measure if
  construction shows up in a profile.
- `group` returns a sorted list rather than a set type, which is a canonical
  set representation but types the nesting as `'b list`.
