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
| 0 | persistent sorted structures | `Base.Map` / `Base.Set` — [not purpose-built, and that is a finding](./NOTES.md#layer-0-not-built-and-that-is-the-finding) |
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
(* compiles to («4» >> «4») *)
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
(* compiles to ((«5» >> «5») ∧ «5»), planned to ((«5» ⋈ «5») ∧ «5») *)
```

Filtering needs no combinator of its own — it is composition with a
coreflexive, and the predicate is written in a separate, smaller object
language so the planner can read it back:

```ocaml
let over_40 = of_relation people >> where_ (fun age -> age >. int_ 40)
(* prints as:  («4» >> where((x > 40))) *)
```

## What is measured

Everything below is asserted by the test suite. **Ratios are wall-clock, mean
± sd over 10 runs** (`bench/headline.exe`); the suite additionally asserts them
in `Relation.tuples_touched`, an internal counter.

> **The counter is not a cost model, and an audit caught this repo treating it
> as one.** It counts tuples scanned and produced and charges nothing for the
> per-tuple constants — set allocation, index probes, intersections — so it
> flatters probe-heavy work over allocation-heavy work. Where it agrees with
> the clock, both are quoted; where it does not, the clock wins and the
> discrepancy is shown, because the discrepancy is the interesting part.

| claim | wall clock | counter |
|---|---|---|
| semi-naive closure beats the naive fixpoint | **14.9×** (2.634 ± 0.058 → 0.247 ± 0.105 ms) | 16.0× |
| fusing a meet into a composition, skewed triangle | **69.1×** (25.080 ± 0.605 → 0.362 ± 0.030 ms) | 123.2× |
| three-way fusion of a skewed 4-cycle | **13.0×** (62.543 ± 1.499 → 5.064 ± 0.082 ms) | 222.8× |
| re-association, *given a plan* | **818×** (0.159 ± 0.017 → ~0.000 ms) | 376× |
| re-association, **end to end including planning** | **0.93× — a wash** | not measured before |
| an index is built once and never invalidated | — | 1 build for 100 lookups |
| converse does no index work | — | 0 additional builds |
| the scalar language covers ordinary business predicates | — | 10 of 14 need no escape hatch |

Two of those rows deserve reading twice. The 4-cycle fusion is a real 13×, not
the 223× the counter reported — the counter is 17× optimistic there, because
the fused path does many small index probes it barely charges for. And
**planning does not pay for itself at this size**: re-association is worth 818×
once you have a plan, and computing the plan costs about what it saves, so a
caller who builds, plans and runs once sees nothing. That distinction was never
published before the audit, and it is the honest headline for a 500-pair
relation.

## Building

`rel` itself needs only `base` and `sexplib0`. `Incremental` forces `Core`, so
it lives in a separate `rel_incr` library; the tests additionally use
`base_quickcheck`. There is no hand-rolled anything: no bespoke tree, no
bespoke test framework.

```
opam switch create . ocaml-base-compiler.5.3.0 --no-install
opam install --switch=. core incremental incr_map base_quickcheck ppx_jane
dune build
dune exec test/main.exe          # 136 checks, including 50 property-checked laws
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

All five live spikes are closed; spike 1 came out negative, as the brief
predicted.

Not done, with reasons in [`NOTES.md`](./NOTES.md#not-done):

- **No general worst-case-optimal join.** Cycles of length two and three fuse;
  a longer chain, or a cycle built through `fork`, still materialises.
- **Filter pushdown is partial by measurement, not by omission.** Into a
  composition chain and through a `fork`, yes. Through a `meet`, no — it was
  measured and is a *loss*, because a fork grows its inputs while a meet
  shrinks them.
- **No transients**, also by measurement: bulk and one-at-a-time construction
  are within 1.2× of each other, so there is no per-insert rebuild for a
  transient to remove.
- **The surface covers a fragment.** Paths, cycle-closing atoms, and cores
  resolved by bounded branching; a disconnected *and* unconstrained answer
  variable still raises.
