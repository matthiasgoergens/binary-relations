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
why — including two places where the brief was wrong, and one where a property
test proved a textbook law false under the constraints this library adopts.

## What is here

Five layers, bottom to top:

| | | |
|---|---|---|
| 0 | persistent sorted structures | `Core.Map` / `Core.Set` — [not purpose-built, and that is a finding](./NOTES.md#layer-0-not-built-and-that-is-the-finding) |
| 1 | the relation value | `lib/relation.ml` — pairs plus lazily built, memoised indexes and exact statistics |
| 2 | the algebra | `lib/algebra.ml` — category → allegory → union → division → Kleene, plus products and the scalar language |
| 3 | interpreters | `lib/eval.ml`, `lib/symbolic.ml`, `lib/incr.ml` |
| 4 | planning | `lib/plan.ml` |

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

| claim | measurement |
|---|---|
| an index is built once and never invalidated | 1 build for 100 lookups; the second direction is a second build |
| converse does no index work | 0 additional builds over 100 lookups on the converse |
| semi-naive closure beats the naive fixpoint | 900 vs 19 315 on a 30-link chain (21.5×) |
| planning on exact statistics beats the order written | 4 vs 1 502 on a 500×500×1 chain (376×) |
| maintaining a view beats recomputing it | 4 vs 3 004 on a one-tuple insert (751×) |
| an unchanged sibling subtree is not recomputed | 2 tuples in the steady state |
| the scalar language covers ordinary business predicates | 10 of 14; 4 need the escape hatch |

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

## Building

Needs OCaml 5.3 with `core`, `incremental` and `base_quickcheck`. There is no
hand-rolled anything: no bespoke tree, no bespoke test framework.

```
opam switch create . ocaml-base-compiler.5.3.0 --no-install
opam install --switch=. core incremental incr_map base_quickcheck ppx_jane
dune build
dune exec test/main.exe          # 96 checks, including 47 property-checked laws
dune exec examples/org_chart.exe # closure, both directions, division, live updates
dune exec examples/predicates.exe # spike 4: how big must the scalar language be?
```

## Status

M0–M5 of the brief are in. The library works, the demo works, and the
differentiator works.

Not done, with reasons in [`NOTES.md`](./NOTES.md#not-done): no surface syntax
layer, no worst-case-optimal joins, no filter pushdown through `meet`/`fork`,
no transients, and spike 1 (OxCaml modes for relational contraction) is
unattempted because this switch is a stock compiler — the brief expects that
spike to fail and its 30-minute budget is intact.
