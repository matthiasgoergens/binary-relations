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

**What would make a purpose-built structure worth it — now measured, and the
answer is sharper than the guess.** The original note here supposed that
letting the indexes share the pair set's spine would help. Half of that is
now demonstrated and half is refuted.

The pair set is sorted lexicographically, so all pairs sharing a *left*
element are contiguous and their right elements strictly increasing — exactly
the precondition Base's sorted-input constructors want. Building the forward
index as one grouping pass instead of `n` separate `Map.update` calls is worth
**about 25%** (3 runs each, non-overlapping ranges):

| | before | after |
|---|---|---|
| forward index, 50 000 pairs | 10.2–10.7 ms | **7.2–8.5 ms** |
| backward index | 12.9–13.3 ms | 12.6–13.3 ms |

The backward index gets nothing, because the pairs are in the wrong order for
it. Reordering first *was* tried and **measured slower** — 13.1 ms to 18.4 ms —
since mapping to a fresh array and sorting it under polymorphic comparison
costs more than the tree insertions it saves. That attempt was reverted, and
the asymmetry in `Relation` is deliberate rather than an oversight.

So the useful conclusion is not "share the spine" but: **a layer-0 structure
would have to hold the pairs in both orders.** Then both directions are a
grouping pass and neither pays for a sort. That is a different and more
specific design than the one this file guessed at, and it now has a number
behind it: the two indexes together still cost more than constructing the
relation.

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

**Statistics are exact and never stale, but they are not free — and being
exact at the leaves turns out not to be the property that matters; see the M5
section above.**
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

## M5's justification was withdrawn, and the measurement agrees

The brief's planner section originally argued that immutability hands a planner
"perfect information for free", and M5 was built against that. The claim was
withdrawn upstream on 2026-08-01 on three counts, and the correction reached
this repo after the code did. Taking them in turn against what is actually
here:

**"Not free" — already found independently.** `Relation.stats` forces both
indexes; planning a three-leaf chain cold costs six index builds. That is
recorded above, and the first version of the planner measurement was unfair
precisely because it charged that cost to one side only. Immutability buys
*not stale*, not *cheap*. Conceded before the correction arrived.

**"Wrong statistics anyway" — the serious one, and it lands.** Join cardinality
depends on the correlation *between* two relations, not on any property of
either, and exact leaf statistics say nothing about it. Rather than take that on
authority it is now measured, in `test/main.ml`:

| shape | predicted | actual | |
|---|---|---|---|
| uniform join keys | 10 000 | 10 000 | 1.00× |
| skewed, hot keys aligned | 1 000 | 10 000 | **0.10×** |
| skewed, hot keys disjoint | 1 000 | 100 | **10.00×** |

The last two rows are the argument. Both right-hand relations have *identical*
per-relation statistics — cardinality 100, domain size 1, range size 100 — so
the cost model receives the same inputs in both cases and must return the same
number. The true answers differ by a factor of a hundred. No amount of exactness
at the leaves can close that gap, because the information needed is not in
either relation. The estimator is not imprecise here; it is reading the wrong
thing.

**"Memoisation mostly does not apply."** True of this implementation: every
derived relation is a fresh value, so the intermediates the interval DP most
wants to cost are exactly the ones with no cached statistics. `Plan` estimates
them with the textbook independence assumption, which is what the table above
is measuring.

### What this does and does not invalidate

The *measurement* of the planner stands: on a 500×500×1 chain, execution touches
1 502 tuples in the order written and 4 when planned. Re-association is a real
win and the algebraic simplifications — pushing `converse` to the leaves, unit
and absorbing elements — do not depend on estimates at all.

What does not stand is the *justification*: "exact statistics make planning
easier than in a real DBMS" is wrong, and a cost model over leaf statistics is
the wrong long-term shape. The brief now points at **worst-case-optimal joins
plus adaptive execution**, whose guarantees do not depend on estimate quality,
with the argument that at in-memory app-state scale the measurement a real DBMS
can only afford to estimate is affordable — so take it instead of guessing.

`Plan` as it stands is therefore best read as: correct, useful for
re-association and simplification, and resting on an estimator that is exact
under uniformity and an order of magnitude out under skew — in *both*
directions, so it cannot even be called conservative. That is a documented
limitation with a measurement attached rather than a claim. Replacing the DP
with a worst-case-optimal join is the next substantial piece of work on this
layer, and it is now the brief's stated M5.

## M5, second attempt: the prior art says do not replace the planner

The brief's revised M5 is "worst-case-optimal joins plus adaptive execution,
not a cost model over statistics". Searching the literature *while* starting on
it — the parallel rule, applied for once — changed the plan before any of it
was built.

**WCOJ is not a general improvement, and on this library's commonest query
shape it is a regression.** The Free Join authors say it plainly: WCOJ
algorithms "have been found to be less efficient than traditional binary join
plans on the typical acyclic queries found in practice", and on acyclic queries
a WCO plan is equivalent to a *left-deep* binary plan — worse than the *bushy*
plans the interval DP already produces. Yannakakis (1981) has given O(N + OUT)
for acyclic queries, by a series of pairwise joins, since before any of this.

A composition chain is a path, hence acyclic. So "replace the DP with WCOJ"
would have made the common case slower.

**Where a cycle actually comes from here.** This algebra has one everyday way
to write one: meet a composite with a base relation. `meet (a >> b) c` over a
common carrier is the triangle query. That is also the one shape where
re-association is powerless — a two-relation composition has a single
bracketing, so the DP has nothing to choose — and the whole cost sits in
materialising an intermediate the meet then discards.

**So the fix is to fuse, not to replace.** `Relation.meet_compose` computes
`(x >> y) ∧ z` without building `x >> y`: for each pair of `z`, ask whether
`x(u)` and `y⁻¹(w)` intersect. That is the leapfrog step of a
worst-case-optimal join, specialised to the shape that needs it, and it is the
direction Free Join argues for — start from a good binary plan and fuse where
it pays. `Plan` introduces it under a guard.

### Measured

| triangle over | edges | intermediate | output | tuples touched | |
|---|---|---|---|---|---|
| uniform random graph | 1 963 | 15 581 | 846 | 23 195 → 19 550 | 1.2× |
| one high-degree hub | 1 010 | 250 021 | 30 | 252 549 → 2 050 | **123.2×** |

**The win is under skew, and on uniform data there is essentially none.** That
is the same boundary the cardinality estimator failed at, in the same session:
uniform data hides both problems. It is worth stating as a general caution
about this library's benchmarks — a randomly generated regular graph is the
input least likely to reveal anything.

### The guard, and what it asks of the estimator

Fusing is a *loss* when the meet's other side is the larger one, so the rewrite
is conditional: fuse only when `z` is no bigger than the estimated size of
`x >> y`. Note how much weaker a demand this places on the cost model than the
withdrawn M5 argument did — it compares one estimate against one exact leaf
count and only needs the *ordering* to be right, not the magnitude. Given that
the estimator is an order of magnitude out under skew in both directions, a
rewrite that needed its absolute numbers would not be trustworthy; one that
needs a comparison is. Tested: on `meet (small >> small) big` the planner
declines to fuse.

### Still not done, and now measured

This is not a WCO join engine, and the gap has a number on it. On a hub graph:

| | unfused | fused | |
|---|---|---|---|
| triangle, `meet (a >> a) g` | 91 549 | 1 250 | **73.2×** |
| 4-cycle, `meet (a >> a >> a) g` | 278 499 | 271 900 | **1.0×** |

Fusion only removes the *outermost* composition, so on a longer chain the
inner `a >> a` is still materialised and almost nothing is saved. Both figures
are asserted in the suite, the second one deliberately — the gap should not be
allowed to close or widen silently.

**An attempt to close it made things worse, and the measurement said so.**
Replacing the materialise-then-probe step with a *structural* probe — walking
the term per pair of `z`, so no intermediate is ever built — measured **0.5×
on the triangle and 0.8× on the 4-cycle**, i.e. a regression. The reason is
amortisation: materialising `a >> a` once and building its index pays for
itself across every pair of `z`, whereas a per-pair walk redoes that work each
time. Reverted.

So the shape of a real fix is now clearer than "implement Generic Join": it has
to amortise. Meet-in-the-middle with a deliberately chosen split point —
materialise the cheaper half, probe the other — rather than either extreme.

That attempt also produced the turn's sharpest process lesson. The structural
version first reported **0 tuples touched**, because the new code probed
indexes directly and nothing charged the counter — the identical blindness that
had been fixed for set operations one commit earlier. An instrument has to be
extended every time work moves to a new code path, and the natural failure is
silence, which reads as a win.

## Prior art: Oliveira, products and coreflexives

Reading queue item 3, and unlike the Kahl episode this one was done *before*
building the next thing on top of `fork`. It produced three laws the suite did
not have, all of which pass — which is the useful outcome for a check on
existing code.

- **`Φq · Φp = Φq ∩ Φp`** (5.227): for coreflexives, composition and meet
  coincide. Worth having because `Eval` reaches the two through entirely
  separate code paths — `>>` conjoins the predicates, `meet` intersects — and
  nothing in the implementation forces them to agree. Now `Laws` does.
- **(5.225)/(5.226)**: a coreflexive on the left restricts inputs, on the right
  restricts outputs. Exactly `filter_dom` and `filter_rng`; the idempotence
  that follows is now checked.
- **×-fusion** (2.26), `⟨f, g⟩ · h = ⟨f · h, g · h⟩`. For functions this is an
  equality. For relations only one inclusion survives, and the suite now both
  asserts the inclusion and **exhibits a witness that it is strict**:

  ```
  c = {(0,1), (0,2)}   a = {(1,10)}   b = {(2,20)}
  c >> ⟨a, b⟩      = 0 pairs
  ⟨c >> a, c >> b⟩ = 1 pair
  ```

  The right-hand fork may use a different `c`-witness in each branch; the
  left-hand one must use the same. That is the non-cartesianness of Rel — until
  now a line in the ruled-out list — turned into a failing equality with a
  concrete counterexample. It is also why `fork-fst-restricted` needs its domain
  guard.

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
| residual `rdiv` | finite-carrier residual — his *restricted residual*, see below |
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

### The constructions have names, and one of them is his

The paper bodies are closed — verified, not assumed: OpenAlex reports
`oa_status: closed` for [doi:10.1016/j.jlap.2007.10.008](https://doi.org/10.1016/j.jlap.2007.10.008)
and Unpaywall independently returns `is_oa: false`. But the content is not
closed. Kahl's **RATH-Agda 2.2** is a freely downloadable literate Agda
development of exactly these theories
([`cas.mcmaster.ca/relmics/RATH-Agda/`](https://www.cas.mcmaster.ca/relmics/RATH-Agda/),
~2.4 MB PDF, 44k lines of extracted text) and it is a later and more complete
statement than either 2006 paper. Everything below is quoted from it. A local
copy, with the exact quoted lines and a note on how it was tracked down, is in
`~/prog/binary-relations-notes/rath-agda/` — kept out of this repo because the
documents are third-party.

**The finite-carrier residual is a known construct called a *restricted
residual*, and Kahl introduced it for precisely this reason.** RATH-Agda §15:

> Restricted residuals were first introduced by Kahl (2008) in the context of
> semigroupoids motivated by applications to finite relations between infinite
> sets, **where the residuals of finite relations are not necessarily finite
> again**. Restricted residuals restrict attention to the "interesting part" of
> residuals and preserve finiteness in that context.

That is the finding the property test produced here, arrived at from the other
direction. His mechanism is to *add an existence statement*:

```agda
(Q /● S) b c = (∀ a → Q a b → S a c) × ∃ (λ a → Q a b)
```

`rdiv` does the same thing by ranging `a` over `dom x` and `b` over `dom y` —
the universal condition, conjoined with existence witnesses. His
`dom-/● : dom (S ●/ R) ⊑ dom S` is the law form of that restriction.

**The two laws that replaced the false Galois connection are his two laws.**
From the derived-law list for restricted residuals:

| RATH-Agda | `Laws` in this repo |
|---|---|
| `/-universal′ : Q ⊑ S ●/ R → Q # R ⊑ S` | `rdiv-sound` |
| `●/-cancel-inner : ran T ⊑ dom S → T ⊑ (T # S) ●/ S` | `rdiv-maximal-on-carrier` |

Note the guard on the second: a range-in-domain containment, which is exactly
the `dom_ a >> c >> dom_ b` restriction I wrote after the unrestricted law
failed. Restricted residuals are defined in "ordered semigroupoids **with
domain**" — a domain operator is a prerequisite, and `dom_` is that operator.

**`plus` versus `star` is a structural distinction, not a workaround.**
RATH-Agda separates `KleeneSemigroupoid` — "Kleene categories without
identities … essentially a heterogeneous version of the *1-free Kleene
algebras* of Kozen (1998)" — carrying `TransClosOp` with `_⁺` only, from
`KleeneCategory`, which carries `starOp` and needs identities. Transitive
closure lives in the identity-free world; the star does not. That is the same
line this library found by noticing `plus` stays finite while `star` needs a
carrier, and it means `star_on_carrier` is the concession and `plus` is not one.

**No `top` anywhere.** Zero occurrences of a universal-relation constant in
44k lines of the development, consistent with excluding it here.

### What this changed

The names and citations are now in the code: `rdiv` is documented as a
restricted residual with Kahl's definition alongside it, the two laws in `Laws`
carry his names (`/-universal′`, `●/-cancel-inner`), and `plus` is marked as the
1-free fragment. Free to adopt, and for an artefact meant to be read by someone
who knows this field, using the field's names is most of the benefit of having
read it.

**One thing was not merely cosmetic.** Kahl's organising idea is that the
identity is where the subject divides — his whole hierarchy is built twice,
once with identities and once without — and this library already half-embodied
that without saying so. The signature ladder now starts one rung lower:

- `SEMIGROUPOID` — composition alone.
- `CATEGORY` — adds `id`, the operation that cannot be a value here.
- `SEMI_ALLEGORY` — converse and meet {e without} an identity, the largest
  fragment a backend with no representable identity can implement in full.
- `KLEENE_SEMIGROUPOID` — transitive closure, which needs no identity, against
  `KLEENE_ALLEGORY`, which adds `star` and does.

That last split is the one worth having. `plus` is finite whenever its argument
is, because the closure of a finite relation only adds pairs between elements
already present; `star` contains the identity on everything and is a finite
value only once restricted to a carrier. Before this, both looked like
compromises of the same kind and `NOTES.md` described them that way. They are
not: `star_on_carrier` is a concession and `plus` is not one, and the ladder now
says so in types rather than in prose.

It also improves the answer to the objection a reviewer will raise. "We raise
`Unbounded` sometimes" becomes "here is the fragment that needs no identity at
all, and here is precisely what an identity costs you" — which is a claim about
the design rather than an apology for it. `RELATIONS` is unchanged, so nothing
downstream moved.

## Spike results

| # | spike | status |
|---|---|---|
| 4 | how big must `v` be? | **done** — 4 of 14 predicates need `opaque` (29%), and the projection finding above. `examples/predicates.ml` |
| 6 | semi-naive evaluation | **done** — 16.0× fewer tuples touched than the naive fixpoint on a 30-link chain |
| 7 | `Incremental` as a second interpreter | **done** — 501× on a one-tuple insert; the deletion boundary is real and documented |
| 8 | lazy automatic index selection | **done** — and it collapsed into index *building*, see above |
| 1 | OxCaml modes for relational contraction | **done, negative, as expected.** Reachable once `rel` became Base-only. `once`/`unique` do not constrain a data-shaped term used twice; `once` does forbid a second use of a *closure*-shaped one — but the `copy` that contraction needs cannot then be written, because writing it requires exactly the second use being forbidden. The modality is affine and contraction is the rule affineness deletes; the way back in linear logic is `!`, whose OxCaml counterpart (`many`) restores unrestricted duplication rather than mediated duplication. Full write-up and probes in `~/prog/binary-relations-notes/spike1-oxcaml/` |

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

## Filter pushdown, measured before it was written

A coreflexive has no cardinality, so `info_of` returns `None` and the interval
DP treated it as a barrier: `a >> b >> where p` was planned exactly as written,
materialising all of `a >> b` and discarding most of it. The gap was measured
first, on a 400 × 800 chain with a filter keeping about 20 of 800 values:

| | tuples touched |
|---|---|
| as written, unplanned | 13 200 |
| filter bound to its neighbour by hand | 971 |
| **planner, after the change** | **971** — 13.6× |

The rewrite binds a coreflexive to whatever precedes it before the DP runs.
What makes it safe is that it needs *no estimate*: a filter only ever shrinks
what it is composed with, so meeting its neighbour first is essentially always
at least as good. Given how badly the estimates behave under skew, a rewrite
justified without them is worth more than one that needs them.

**Pushing a filter through a `fork` was measured and is a win — 4.4×** (36 000
tuples against 8 150), and it is now done. The contrast with `meet` is the
point, and it is structural rather than incidental: a fork *grows* its inputs
while a meet *shrinks* them, so filtering before a fork saves work on both
branches and filtering before a meet duplicates work the meet was about to
avoid. Same rewrite, opposite verdicts, decided by measurement.

**Pushing a filter through a `meet` was measured and is a loss**, so it is
deliberately not implemented: distributing `p >> (a ∧ b)` into
`(p >> a) ∧ (p >> b)` costs 8 025 tuples against 5 250 for the original,
because it filters two relations instead of one and the meet still has to
intersect the results. The suite asserts the negative so it cannot quietly
stop being true. `fork` remains unmeasured.

## The cost counter was blind to set operations

Found while measuring the `meet` case above, which reported 0 tuples on both
sides. `Relation.inter`, `union`, `diff` and `filter` never called `touch`, so
the counter — the unit every performance claim in this repo is stated in — saw
nothing for any of them.

Correcting it moved several published numbers, all of which have been updated:
the semi-naive closure win from 21.5× to **16.0×**, incremental maintenance
from 751× to **501×**, filter pushdown from 39.8× to **13.6×**. The fusion and
planner numbers barely moved, because those paths are dominated by composition,
which was always counted.

The charge is `min` of the two cardinalities rather than the sum. Base's set
operations are divide-and-conquer, about m·log(n/m + 1) for m ≤ n, so a union
against a singleton is logarithmic, not linear; charging the sum overstated
incremental maintenance by two orders of magnitude and made a steady-state
update look like 504 tuples when the real work is a handful. `min` still
understates by the log factor, which is the conservative direction for every
ratio claimed here.

The general lesson is worth more than the numbers: **an instrument that
silently reads zero for a whole class of work will flatter whichever side of a
comparison uses that work more.** The blind spot was found only because a
measurement came back 0 vs 0 and was too obviously degenerate to accept.

## The surface, and the fragment it covers

`Query` is the answer to the brief's open question, and it comes out on the
`let*` side rather than comprehensions. A query is a set of atoms — a relation
between two variables — plus the two variables the answer is about;
`compile` walks a path from source to target composing as it goes, and any
leftover atom whose ends are the answer's own endpoints becomes a `meet`.

Two things make it more than sugar. It compiles **to the algebra**, so nothing
below it is bypassed: the planner still runs, `id` is simplified away, converse
is pushed to leaves. And the way you write a *cycle* — `constrain` between two
already-bound variables — produces exactly `meet (a >> b) c`, the shape the
fusion rewrite handles, so the surface and the optimiser meet in the middle.

**Compilation is variable elimination**, which turned out to be the whole of
general conjunctive-query compilation for binary atoms. Three rules, one per
operation of the algebra: a dangling variable becomes a coreflexive on its
neighbour (a semi-join — this is what makes it Yannakakis-shaped rather than
nested-loop); a waypoint contracts by composition; parallel atoms merge by
meet. That reduces any series-parallel query graph to one edge between the
answer variables, which is a far wider fragment than the path-walking first
draft — a branching query now compiles to
`(manages >> (dom_(manages) >> dept))` instead of raising.

**The irreducible core is handled too, by branching rather than tabulation.**
A core where every non-answer variable has degree three or more cannot be
contracted. The textbook remedy is tabulation, which needs pair-typed
relations and hence variables carrying their own types — exactly the
type-level machinery the binary framing exists to avoid. The alternative keeps
everything monomorphic: pick such a variable, compute the finite set of values
it can take, solve once per value and join. Substituting a value turns each of
its atoms into a coreflexive on a neighbour, so the variable vanishes and
elimination resumes. That is variable-at-a-time evaluation — what a generic
join does.

It is guarded by `?max_candidates`, because the compiled term grows with the
candidate set, and computing candidates means *evaluating* the atoms at that
variable, which is why it is a last resort. Verified against brute-force
enumeration rather than against my own arithmetic, and the test asserts the
comparison is not vacuous — the first version of it compared two empty
relations, because the sample data was a tree and the query needed chords.

What is still refused: an answer variable that is both disconnected and
unconstrained, which would need a universal relation. If both answer variables
carry constraints the answer is the cross product of two finite sets, which is
an ordinary relation, so that case now works.

**Two of the three rules shipped broken in the first draft and the failure was
silent.** Each oriented its edges by `flip`, which allocates, and then filtered
the edge list by `phys_equal` against the *oriented copy* rather than the edge
actually in the list — so they reported progress while removing nothing, and
the reduction spun forever. The termination argument is sound (every rule
removes an edge), so the fix was to keep the originals for removal, and the
step counter that found it is now a permanent invariant check with a message
saying it indicates a bug in the rules rather than a hard query. Worth
recording because the bug is invisible to types, invisible to a quick reading,
and produces a hang rather than a wrong answer — and because I fixed one of
the three, verified that one, and assumed the other two had applied.

Atoms are `('e, 'e) Relation.t`: one element type per query. That covers the
confirmed business case and keeps variables monomorphic, which is what makes
the binding operators readable at all. A heterogeneous version needs variables
that carry their own types, and with them the type-level machinery the binary
framing exists to avoid.

## Not done

- The surface covers paths plus cycle-closing atoms; general conjunctive
  queries raise `Unsupported`.
- No worst-case-optimal joins; the planner does binary joins only.
- Filter pushdown through `meet`/`fork` is not implemented. Pushing a
  coreflexive inward through a composition chain **is**, and was worth 13.6×
  on the measured case — see below.
- **Transients: measured, and not worth building.** The brief budgets for an
  O(1)-in/out mutable builder behind an immutable interface. On 50 000 pairs
  (`bench/build.ml`): `of_list` 13.0 ms, and building the same relation by
  repeated `union` with a singleton 15.0 ms — **1.2×**, at 0.30 µs per insert.
  There is no per-insert rebuild for a transient to eliminate, because
  `Set.union` against a singleton is already O(log n) and shares structure.
  What the same benchmark does show is that the **first index build costs
  10.0 ms**, comparable to constructing the relation at all — so if anything on
  this layer is worth optimising it is the index, not construction. That is the
  purpose-built-layer-0 idea from the top of this file, now with a number
  attached rather than a hunch.
- `group` returns a sorted list rather than a set type, which is a canonical
  set representation but types the nesting as `'b list`.
