# rel — binary relations as first-class values

An OCaml library that makes **binary relations first-class immutable values**,
with **access-path independence** for ordinary in-memory data: you declare the
relation and write the query, and the library chooses and holds the indexes.

Codd's 1970 argument — that ordering, indexing and access-path dependence are
defects — applies verbatim to values in memory, because choosing
`(customer_id, order list) Map.t` *is* an access-path commitment. It privileges
one direction, it is a hand-chosen index, and a new query pattern means
reshaping the data and every call site with it.

- **For a Jane Street audience:** `Incr_map`, generalised from maps to relations.
- **Neutrally:** DataScript with static types.

The design and the reasoning behind it are in [`DESIGN.md`](./DESIGN.md), which
is the brief as written before any code existed.
[`NOTES.md`](./NOTES.md) records where the implementation departed from it and
why — including two things the brief expected that turned out not to hold, and
one place where a property test proved a textbook law false under the
constraints this library adopts.

## What is here

Five layers, bottom to top:

| | | |
|---|---|---|
| 0 | persistent sorted structures | `Core.Map` / `Core.Set` — [not purpose-built, and that is a finding](./NOTES.md#layer-0-not-built-and-that-is-the-finding) |
| 1 | the relation value | `lib/relation.ml` — pairs plus lazily built, memoised indexes and exact statistics |
| 2 | the algebra | `lib/algebra.ml` — semigroupoid → category → allegory → union → division → Kleene, plus products and the scalar language. The ladder starts below the category because [the identity is where the subject divides](./NOTES.md#what-this-changed) |
| 3 | interpreters | `lib/eval.ml`, `lib/symbolic.ml`, `lib/incr.ml` |
| 4 | planning | `lib/plan.ml` |
| 5 | the surface, with points | `lib/query.ml` — variables and binding operators that compile *to* the algebra |

and `lib/laws.ml`, which is the algebra's equational laws as a functor any
backend can run against itself.

A query is a functor over the signature, and interpreting it is applying it:

```ocaml
module Reachable_in_three (R : Algebra.RELATIONS) = struct
  open R
  let q ~a ~b ~c = a >> b >> c
end

module E = Reachable_in_three (Eval)     (* run it now                    *)
module S = Reachable_in_three (Symbolic) (* print it, plan it, rewrite it *)
module I = Reachable_in_three (Incr)     (* keep it live                  *)
```

The surface restores the variables without giving anything up: a query written
with binding operators compiles to a term in the algebra, so the planner, the
fusion rewrite and every interpreter still apply.

```ocaml
let reachable_dept =
  Query.compile (fun boss ->
    let open Query in
    let* report = step manages boss in
    let* d = step dept report in
    ret d)
(* compiles to ((id >> «4») >> «4»), planned to («4» >> «4») *)
```

Writing a *cycle* is what makes this more than sugar — it produces exactly the
shape the planner learned to fuse:

```ocaml
let triangles =
  Query.compile (fun x ->
    let open Query in
    let* y = step edges x in
    let* z = step edges y in
    let* () = constrain edges x z in   (* closes the cycle *)
    ret z)
(* compiles to (((id >> «5») >> «5») ∧ «5»), planned to ((«5» ⋈ «5») ∧ «5») *)
```

Filtering needs no combinator of its own — it is composition with a
coreflexive, and the predicate is written in a separate, smaller object
language so the planner can read it back:

```ocaml
let over_40 = of_relation people >> where_ (fun age -> age >. int_ 40)
(* prints as:  («4» >> where((x > 40))) *)
```

## What is measured

Everything below is asserted by the test suite as a measurement, not as a
comment. Numbers are tuples touched, from `Relation.tuples_touched`.

> **All figures below were re-measured on 2026-08-02** after the cost counter
> was found to be blind to `meet`, `union`, `diff` and `filter` — it charged
> nothing for any set operation, so every measurement involving one was
> understated. Several published numbers moved: the semi-naive closure win from
> 21.5× to 16.0×, incremental maintenance from 751× to 501×, filter pushdown
> from 39.8× to 13.6×. The counter now charges `min` of the two cardinalities,
> which matches Base's divide-and-conquer set operations far better than the
> sum and still understates by a log factor — deliberately, since that is the
> conservative direction for every ratio claimed here.


| claim | measurement |
|---|---|
| an index is built once and never invalidated | 1 build for 100 lookups; the second direction is a second build |
| converse does no index work | 0 additional builds over 100 lookups on the converse |
| semi-naive closure beats the naive fixpoint | 1 770 vs 28 305 on a 30-link chain (16.0×) |
| re-association beats the order written | 4 vs 1 502 on a 500×500×1 chain (376×) |
| maintaining a view beats recomputing it | 6 vs 3 004 on a one-tuple insert (501×) |
| an unchanged sibling subtree is not recomputed | 3 tuples in the steady state |
| the scalar language covers ordinary business predicates | 10 of 14; 4 need the escape hatch |
| fusing a meet into a composition, skewed triangle | 252 549 vs 2 050 tuples (123.2×) |
| three-way fusion of a skewed 4-cycle | 278 499 vs 1 250 tuples (222.8×) |
| binding a filter to its neighbour before planning | 13 200 vs 971 tuples (13.6×) |
| distributing a filter over a fork | 36 000 vs 8 150 tuples (4.4×) |

Two of those are the ones whose failure mode is a wrong answer rather than a
slow one, so they are attacked rather than demonstrated: 400 randomly generated
expression trees are rewritten by the planner and re-run against the original,
and 300 rounds of random insert-and-delete are checked against a from-scratch
recomputation. Both also assert they are not vacuous — the planner actually
rewrote 335 of the 400 trees, and the delta path was taken 210 times against
128 fallbacks. A no-op optimiser and a composition node that quietly recomputed
every time would both pass the correctness check and mean nothing.

The planner's own statistics cost one index build per relation — exact and
never stale is not the same as free, and
[`NOTES.md`](./NOTES.md#the-planner-refuses-rather-than-guesses) records how
the first version of that measurement was unfair and said the opposite.

More importantly, **the argument M5 was built on has since been withdrawn.**
Exact leaf statistics do not give good join estimates, because join cardinality
depends on the correlation *between* relations: two of the measured cases have
identical per-relation statistics and true results 100× apart. The
re-association win above is real, the justification for it was not, and the
brief now points at worst-case-optimal joins instead. See
[`NOTES.md`](./NOTES.md#m5s-justification-was-withdrawn-and-the-measurement-agrees).

## Building

`rel` itself needs only `base` and `sexplib0`. `Incremental` forces `Core`, so
it lives in a separate `rel_incr` library; the tests additionally use
`base_quickcheck`. There is no hand-rolled anything: no bespoke tree, no
bespoke test framework.

```
opam switch create . ocaml-base-compiler.5.3.0 --no-install
opam install --switch=. core incremental incr_map base_quickcheck ppx_jane
dune build
dune exec test/main.exe          # 96 checks, including 47 property-checked laws
dune exec examples/org_chart.exe # closure, both directions, division, live updates
dune exec examples/predicates.exe # spike 4: how big must the scalar language be?
```

The laws run with `Base_quickcheck.Shrinker.atomic`, i.e. no shrinking. A
branch, `tapecheck-shrinking`, swaps in
[tapecheck](https://github.com/matthiasgoergens/tapecheck)'s choice-tape
engine, which on the one law that genuinely failed during development reduces
the counterexample from nine noisy pairs to `a=[] b=[] c=[(0,0)]` — the minimal
one. It is a branch rather than the default because tapecheck is not yet
installable and vendors its own `base_quickcheck`, which cannot share a dune
scope with `Core`. See
[`NOTES.md`](./NOTES.md#shrinking-what-tapecheck-buys-and-why-it-is-on-a-branch).

## Status

M0–M5 of the brief are in. The library works, the demo works, and the
differentiator works.

Not done, with reasons in [`NOTES.md`](./NOTES.md#not-done): no surface syntax
layer, no general worst-case-optimal join (one cyclic shape is fused, longer
cycles still materialise), no filter pushdown through `meet`/`fork`, and no
transients. All five live spikes are now closed; spike 1 came out negative, as
the brief predicted.
