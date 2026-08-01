# DataScript — read as calibration for the relations project

Reading item 0 from `binary-relations.md`, done 2026-08-01. Source actually
read: `tonsky/datascript` at master, cloned and inspected — not a summary of
docs. ~7.7k lines of Clojure total (`db.cljc` 1931, `query.cljc` 1019,
`query_v3.cljc` 975).

**Verdict up front: the design stands, and the reading paid for itself twice.**
Once by confirming the storage model is more or less forced, and once by showing
exactly where the gaps are — which is where a new project has something to add.

---

## The finding that matters: DataScript *is* the binary relational model

A datom is `[e a v tx]`. Fix the attribute `a`, and what remains is a set of
`(entity, value)` pairs — **a binary relation `a ⊆ E × V`**. A DataScript
database is therefore precisely *a collection of named binary relations*, stored
as one union with the name carried as a column.

That is Abrial's and NIAM's binary data model, shipped and in production for a
decade. The tradition this whole thread started from did not die; it went to
the client-side application-state layer and quietly won there.

**Where our design differs is exactly one axis: attributes are dynamic.** In
DataScript `a` is a runtime keyword and the schema is data. In the design we
have been sketching, each binary relation is a *statically typed value*
`Rel a b`. So:

> **Our project ≈ DataScript with static types**, plus the things below.

That is the calibration. It is a narrower and more honest claim than "a
generalised relational algebra", and it is a better pitch.

---

## Architecture, as actually implemented

- **A database is a record of three persistent sorted sets** — `eavt`, `aevt`,
  `avet` — plus schema, `max-eid`, `max-tx`, a reverse schema and caches
  (`defrecord-updatable DB` in `db.cljc:674`). Nothing more. The whole "database"
  is three indexes over the same datoms.
- **They had to write their own data structure.** The indexes are
  `me.tonsky.persistent-sorted-set` (a separate library, B-tree backed), not
  Clojure's built-in sorted set — it needed efficient slicing/seeking and
  storage hooks. **The persistent structure is the hard part and it got factored
  out into its own project.** Budget accordingly.
- **Transients, on all three indexes, per transaction** (`db.cljc:655-663`:
  `(update :eavt transient)` … `persistent!`). This is direct confirmation of
  the "transients are the shape to copy" recommendation, from the reference
  implementation, arrived at independently.
- **Even the immutable datom has mutable fields.** `deftype Datom` carries
  `^:unsynchronized-mutable idx` and `_hash` (`db.cljc:180`) — caches inside an
  immutable value. The immutable-interface/mutable-implementation pattern is not
  a purity compromise, it is what shipping looks like.
- **Index selection is a `case-tree` over which of `e a v tx` are bound**
  (`-search`, ~`db.cljc:718-750`). Roughly forty lines dispatch to `eavt`,
  `aevt` or `avet` and fall back to filtering. **Codd's access-path independence,
  implemented directly and compactly.** Worth reading in full; it is the clearest
  small statement of the idea in any codebase I have seen.
- **The query engine has a section literally headed `;; Relation algebra`**
  (`query.cljc:101`), built on `defrecord Relation [attrs tuples]` where `attrs`
  maps query variables to *positions* and tuples are object arrays. So it is a
  hybrid: **named at the API, positional underneath** — the same conclusion this
  project reached from the other direction.
- **Reactivity is a callback list.** `conn` is an atom plus `:listeners`;
  `listen!`/`unlisten!` register callbacks that receive a transaction report
  (`conn.cljc:159-169`). That is all.

---

## The gaps — where a new project would actually add something

This is the part worth having read the source for. All four follow from things
already decided in `binary-relations.md`.

1. **There is no query planner.** Joins are `hash-join` (`query.cljc:345`)
   folded over the clauses **in the order written** (`query.cljc:463`). So the
   "goal ordering is semantically load-bearing" problem pinned on miniKanren is
   present here too — milder, since it costs bad plans rather than divergence,
   but present. A cost-based or worst-case-optimal join layer is a real
   differentiator, not a nice-to-have.
2. **Index selection is a human decision.** The `avet` index is **opt-in per
   attribute** via `:db/index` in the schema (`(if (indexing? db a) …)`).
   Under our immutability axiom an index is a *pure function of the relation*,
   so it could be built lazily on first use and memoised — no schema
   declaration, no human choice. That improvement falls straight out of the
   axioms and is a concrete, demonstrable win.
3. **No types at all.** Attributes are runtime keywords. The entire
   type-checking value proposition is unclaimed — and it is unclaimed precisely
   because the model is dynamic, not because typing it is hard. `Rel a b` needs
   two type parameters.
4. **No incremental views.** `listen!` hands you a transaction report and you
   recompute whatever you like, yourself. There is no mechanism for a derived
   relation that stays live. See the Jane Street section — this is the gap that
   matters most for the chosen host.

Also worth noting: **two query engines exist** (`query.cljc` and
`query_v3.cljc`, ~1k lines each). Query evaluation was the hard part and they
iterated on it. Expect the same.

---

## Ecosystem — who actually uses it

Production users, from the project's own list and corroborating searches:

- **Roam Research** — networked-thought note-taking
- **Logseq** — local-first outliner notebook
- **Athens Research**, **Hulunote** — same category
- **Precursor** — collaborative prototyping
- **PartsBox** — electronic parts management
- **Cognician** — coaching platform; **LightMesh** — datacenter management
- **Zetawar** — turn-based strategy game; plus assorted smaller apps

**The pattern is informative.** The flagship uses are knowledge-management and
outliner tools, where the relational/graph shape *is* the product, plus a
handful of line-of-business apps. So DataScript is proven at **application-state
scale in a browser**, not at analytics scale. That matches its own stated
intent ("cheap to create, quick to query and ephemeral") and it is the right
scale to target first — it is also, notably, exactly the "ordinary business
logic over in-memory values" target.

---

## The Jane Street angle

Given that OCaml/OxCaml is now the chosen host and the audience is explicit,
the relevant house libraries are:

- **`Incremental`** — Jane Street's self-adjusting-computation library
  (Acar-inspired): a graph of nodes where a node's value is a function of its
  parents, and changing an input recomputes exactly the descendants.
- **`Incr_map`** — incremental operations on map-like structures
  (`unordered_fold`, incremental `map`, `join`), which works by **diffing maps
  efficiently via `Map.symmetric_diff`**.

The mechanism is the point: `symmetric_diff` is cheap **because the maps are
immutable and share structure**. That is our axiom, already load-bearing in
their stack.

Which gives the sharpest available framing for this audience:

> **Relations as first-class immutable values — `Incr_map`, generalised from
> maps to relations.**

Two concrete consequences for the design:

- **It un-demotes the incremental-views thread.** IVM was filed as an optional
  optimisation for the versioned case. In this ecosystem incremental derived
  views are the *house style* — `Incremental`, `Incr_map`, `Incr_dom`, Bonsai
  are all built on it. It moves back up.
- **`Incremental` should be one of the tagless-final interpreters.** This is the
  best argument yet for the multi-interpretation architecture, and it is the
  demo: *one* relational program, interpreted as (a) a one-shot evaluator and
  (b) an `Incremental` graph that stays live as inputs change. Nothing in
  DataScript does this, and nothing in the OCaml ecosystem does it relationally.

Note also that this repo already carries a Jane Street thread
(`outreach/`, `splittable_random#2`), so a second OCaml artefact aimed at the
same audience is coherent rather than scattered.

---

## What changes in the plan

Nothing structural. Three adjustments:

1. **Lazy automatic index selection moves up** from implied to a headline
   feature, because DataScript makes it a human decision and immutability makes
   the automatic version sound.
2. **Incremental views move up**, from a demoted optimisation to the flagship
   second interpreter, because of the host and audience.
3. **Query planning is a real gap**, not a refinement — the reference
   implementation folds joins in clause order.

Reading list position: item 0 done. Next is `chyp`, then `pdbc.pdf` on
products and coreflexives, then Kahl's MPC 2006 Haskell interface — the last
of which now matters more, since it is the closest thing to the typed-relations
interface that DataScript deliberately does not have.
