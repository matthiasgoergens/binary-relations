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

## Attacking it rather than demonstrating it

Everything measured above is a case I chose, which shares every assumption the
implementation does and can therefore only agree with me. The two components
whose failure mode is a *wrong answer* rather than a slow one get the opposite
treatment:

- 400 randomly generated expression trees, each rewritten by `Plan.optimise`
  and re-run against the original.
- 300 rounds of random insert-and-delete on three inputs of a live graph, each
  checked against a from-scratch recomputation.

Both carry a **vacuity check**, because both have an obvious silent
degeneration: an optimiser that rewrites nothing and a composition node that
falls back to recomputing every time would each pass the correctness assertion
while meaning nothing at all. So the tests assert that the planner actually
rewrote most trees (335 of 400) and that the delta path was actually taken
(210 times against 128 fallbacks). `Incr.delta_updates` and
`Incr.full_recomputes` exist for no other reason.

`Plan.build` raises rather than falling back to a right-deep build when a
bracket and a chain disagree. That case is unreachable, but a planner that
silently emitted a different plan from the one it costed would still be
correct — and would make every measurement in this file a lie.

## Shrinking: what tapecheck buys, and why it is on a branch

The law suite runs `quickcheck_shrinker = Base_quickcheck.Shrinker.atomic`,
which is no shrinking at all — `Shrinker.int`, `bool` and `char` are literally
`atomic` in base_quickcheck, so a failing scalar is reported exactly as
generated. The cost showed up on the one law that genuinely failed here: the
counterexample came back unshrunk and the diagnosis was done by hand.

[tapecheck](https://github.com/matthiasgoergens/tapecheck) fixes that, and the
integration is **on the `tapecheck-shrinking` branch, deliberately not on
`main`**. Measured on this project's own generators:

| | `base_quickcheck` | tapecheck |
|---|---|---|
| a deliberately false law (composition commutes) | 24 pairs across all three inputs | `a=[(0,0)] b=[(0,5)] c=[]` — minimal |
| the law that actually failed here (`rdiv` Galois) | `a` 3 pairs, `b=[]`, `c` 5 pairs with a duplicate | `a=[] b=[] c=[(0,0)]` |

The second row is the one that matters: `a=[] b=[] c=[(0,0)]` is *exactly* the
minimal counterexample derived by hand above, so the shrinker would have handed
over the diagnosis — empty divisor, non-empty candidate — rather than leaving it
to be reasoned out. On the false law it also eliminated `c`, which the property
never mentions.

**The API is genuinely drop-in.** `Base_quickcheck.Test.run` → `Tape_test.run`
is a one-identifier change: same `(module S)`, same `~config`, same generators,
and the declared `Shrinker.atomic` is accepted and ignored as advertised.

**Why it is not on `main`.** tapecheck is not installable as an opam package —
its libraries have no `public_name` and cannot until the `splittable_random`
fork carrying `For_tape.attach` lands
([janestreet/splittable_random#2](https://github.com/janestreet/splittable_random/pull/2)).
So it has to be vendored, and it vendors its own `base_quickcheck` and
`splittable_random` under those exact library names. Any dune target that also
reaches the *installed* `base_quickcheck` then fails to resolve — and every
user of `Core` reaches it, transitively through `base_bigstring` → `int_repr` →
`base_quickcheck.ppx_quickcheck.runtime`. `(allow_overlapping_dependencies)`
gets past dune's conflict check and the linker then rejects it outright, with
duplicated `Base_quickcheck__Generator`, `Base_quickcheck__Test` and
`Splittable_random`.

That is a hard adoption blocker against exactly the audience tapecheck is for,
and it is worth recording that it was confirmed from outside the project rather
than inferred from its own tree. Carrying 512K of vendored Jane Street code in
a repo that otherwise builds from `base` and `sexplib0` is not a trade worth
making until the upstream fork lands; the branch keeps the work and the
evidence alive until then.

**What the attempt left behind on `main`, on its own merits.** Making `rel`
Core-free was a precondition for the experiment and is an improvement
regardless: `rel` now depends on `base` and `sexplib0` and nothing else,
`Incremental` — which forces `Core` — is isolated behind a separate `rel_incr`
library, and `rel` is a public, installable library. One trap found on the way
is worth knowing: `ppx_jane` bundles `ppx_quickcheck`, whose *runtime* is
`base_quickcheck`, so merely preprocessing a library with `ppx_jane` puts
`base_quickcheck` in its link closure. Narrowing to `ppx_sexp_conv` removed a
dependency that had nothing to do with the code.

Two smaller findings, both fixable upstream and both recorded on the branch:
`Tape_test.run`'s `?report` defaults to `` `Summary ``, which prints to stdout
on every call (47 lines for this suite) and whose `` `Silent `` alternative is
not in the README's usage section; and the summary line disagrees with the
result, printing `0 failing` on a run that returned a shrunk counterexample.

## Prior art: Kahl's relational semigroupoids

The brief lists this as reading priority 2 — "someone built this interface once
and wrote down what had to bend" — and it was not done before the code was.
Doing it afterwards turned out to be more useful than doing it first would have
been, because it became a check on decisions already made under constraint
rather than a source to copy.

**The citation in the brief is wrong in two ways.** It gives *Semigroupoid
Interfaces for Relation-Algebraic Programming in Haskell*, MPC 2006. MPC 2006
is LNCS 4014; this paper is **RelMiCS/AKA 2006, LNCS 4136, pp. 235–250**
([doi:10.1007/11828563_16](https://doi.org/10.1007/11828563_16)), and Kahl's own
publication list titles it *Semigroupoid Interfaces for Programming with
Relations in Haskell*. There is also an expanded journal version that the brief
does not mention and which is the more relevant one:

> Wolfram Kahl, ***Relational Semigroupoids: Abstract Relation-Algebraic
> Interfaces for Finite Relations between Infinite Types***, Journal of Logic
> and Algebraic Programming 76(1), 2008, 60–89.

That subtitle is this library's problem statement verbatim.

### The wall is the same one, and he names it

From the journal abstract: *finite maps or finite relations between infinite
sets **do not even form a category, since the necessary identities are not
finite***. The RATH page puts it concretely — a total identity map on `Integer`
cannot exist.

That is exactly what forced {!Eval} to have three constructors rather than one.
`id` is the diagonal of an unbounded type; it is not a value.

### Convergent, independently

His stated remedy is that the theory should provide *"operations that would
produce infinite results replaced with variants that preserve finiteness, but
still satisfy useful algebraic laws."*

That is, almost word for word, the principle this library arrived at without
having read him:

| infinite-producing operation | what this library does instead |
|---|---|
| `top`, complement | excluded; not finite values |
| `star` | `star_on_carrier` — reflexive on the carrier of the argument |
| residual `rdiv` | finite-carrier residual over the domains it can see |
| the laws for the above | restated in the restricted form that survives, in `Laws` |

The last row is the one I would have expected to be the novel part and is not.
Discovering that the textbook Galois connection is false here, and writing down
the carrier-restricted law that holds instead, is precisely "still satisfy
useful algebraic laws". Two independent arrivals at the same principle is
decent evidence the principle is forced by the domain rather than chosen.

### Where the designs genuinely diverge

Same wall, different exit.

- **Kahl removes the identity from the algebra.** A semigroupoid is a category
  without identities, so nothing in the structure ever demands a value that
  cannot exist. The cost is that every law mentioning `id` has to be restated
  in terms of domain/range partial identities, and the structure is weaker than
  a category.
- **This library keeps `id` and makes it non-enumerable.** `Corefl` represents
  it symbolically, it absorbs into the finite case on contact (composing with
  it is a filter), and only an operation that would actually have to enumerate
  it — `to_list`, `join`, `converse` of a function graph — raises `Unbounded`.

The trade is legible: Kahl buys totality at the cost of the category structure;
this buys the category structure at the cost of partiality. `id_left_unit` and
`id_right_unit` are stated in the ordinary way in `Laws` and pass, which they
could not be in a semigroupoid. Whether the partiality is acceptable depends on
whether the operations that raise are ones anybody writes, and the evidence so
far — 400 random expression trees, no `Unbounded` outside the tests written to
provoke it — is that they are not. **This is the one place a reviewer who knows
the literature will push, and the answer is now a considered disagreement
rather than an omission.**

### Two sharpenings

- **"No `top`" is a consequence of representation, not of relations.** RATH is
  BDD-based (via KURE). A BDD over a finite bit-encoded domain has complement
  and `top` for free — they are cheap and finite there. What excludes them here
  is the combination of *sets of pairs* and *unbounded element types*. Worth
  stating that way rather than as a fact about relation algebra.
- **There is prior art for M5 too, and it is not the same idea.** Kahl,
  *Dynamic Symbolic Optimisation for Relation-Algebraic Programming in Haskell*
  (MACIS 2006, pp. 92–99), builds a self-optimising evaluator for exactly the
  observation that "equivalent expressions with apparently similar structure may
  differ widely" in cost. But it optimises against *BDD heuristics* at runtime,
  not against cardinality statistics. The claim that immutability yields exact,
  never-stale statistics remains a distinct argument; it is now a distinct
  argument with a known neighbour rather than an unexamined one.

### What was actually read

The RelMiCS and JLAP abstracts, Kahl's publication list, and the RATH project
overview. **The paper bodies are paywalled and were not read**, so the Haskell
type-class definitions, the exact form of his finiteness-preserving variants,
and his laws are unverified here. Anything above about *his* interface is from
abstracts; anything about this library is from its code. Getting the JLAP
version through a library would be worth an hour before making any public claim
about how the two interfaces compare in detail.

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
