# Binary relations as the basis of a relational algebra

Status: **research note, no project yet.** The work will get its own repo.
This file exists so the reading does not have to be redone.

Question from Matthias: *"I remember a paper about using binary relations as
the basis for building a more generalised relational algebra. What happened to
that?"* — with the remembered selling points being no named columns, and a
better fit for a type system or proof assistant.

Research caveat, stated up front: `WebFetch` returned 403 on every host in this
session (arXiv, Wikipedia, `wiki.haskell.org`, `di.uminho.pt` — all of them),
and direct `curl` is blocked by the same egress allowlist. **Everything below
comes from search-result snippets and titles, not from reading the papers.**
Bibliographic details are reliable; claims about what a paper *argues* are
second-hand unless marked otherwise. Anything load-bearing should be re-read
before it is built on.

---

## Identified

Matthias found it: the paper linked from
[HaskellWiki, *Relational algebra*](https://wiki.haskell.org/Relational_algebra),
namely `http://www.di.uminho.pt/~jno/ps/_.pdf` —

> **J.N. Oliveira, *Functional dependency theory made 'simpler'*.** Technical
> Report DI-PURe-05.01.01, DI/CCTC, Universidade do Minho, 2005. Published as
> **[*First Steps in Pointfree Functional Dependency Theory*](https://www.researchgate.net/publication/238475005_First_Steps_in_Pointfree_Functional_Dependency_Theory)**.

The sentence that is presumably the memory:

> *"Contrary to the intuition that a binary relation is just a particular case
> of n-ary relation, this research shows the effectiveness of the former in
> 'explaining' and reasoning about the latter."*

It rephrases Codd's functional-dependency theory in the **binary-relation
pointfree calculus**, and the theory "becomes simpler and more general, thanks
to the calculus of *simplicity* and *coreflexivity*" — elegant expressions in
place of lengthy formulae, calculation in place of pointwise proof. It came out
of a concrete itch, not a grand programme: Joost Visser's *Spreadsheets under
Scrutiny* talk, and wanting refinement laws for spreadsheet normalisation.

So this is **candidate 2 below — the allegory / Algebra-of-Programming line**,
not the string-diagram line. The rest of this note stands; the ranking was
wrong and the disambiguating question ("did it have pictures?") was the right
one to ask.

Two practical notes on the link itself:

- `_.pdf` is Oliveira's rolling *current-draft* filename, not a stable
  identifier — there is a different `_.pdf` under `~jno/tmp/` today, also
  the FD paper. **Whatever is at that URL now may not be the 2005 report.**
  Cite the tech-report number or the published title, and keep a local copy.
- The HaskellWiki page's own gloss is "a concise and deep approach", and it
  points onward at Oliveira's homepage and other papers — which is the right
  next hop, since the FD paper is a *first step* by its own title.

---

## The short answer

There is no single paper. There are **four separate traditions** that all start
from "binary relations, composed, no attribute names", and they had four very
different fates. Three are alive; the database-facing one lost and stayed lost,
for a reason that is precise and worth knowing.

And the precise reason is the most useful thing found:

> **Tarski's calculus of binary relations is strictly weaker than Codd's
> algebra.** Its expressive power is exactly the three-variable fragment of
> first-order logic (FO³). Codd's n-ary relational algebra is complete for
> (domain-independent) FO.

So "binary relations are enough" is *false as stated* — that is why the binary
model lost the database argument in the 1970s, and it is not a matter of taste
or tooling. You get the expressiveness back only by adding structure: pairing /
tabulation (the allegory route), or extra diagrammatic connectives (the 2024–25
route). Any design starting from "just use binary relations" has to pay this
bill explicitly. **This is the single fact to carry into the later project.**

**Refinement now that the paper is identified.** The FO³ bound is a fact about
*bare* Tarski relation algebra. Oliveira is not working in bare TRA — he works
in an allegory with **products**: splits `⟨R,S⟩`, projections `π₁ π₂`,
coreflexives for restriction. An n-ary relation is a binary relation into a
product type, and a "column" is a projection. So his framework has already paid
the bill, and pays it in the cheapest available currency. That is why he can
claim binary relations *explain* n-ary ones rather than merely encode them.
The cost does not vanish, it changes shape: it reappears as **plumbing** —
fork-and-project combinators standing in for the names you gave up. *(This
paragraph is reasoning from the calculus's standard structure, not from a
snippet — verify against `pdbc.pdf` chapter 5 before building on it.)*

---

## Which paper was it? — ranked

**1. The cartesian-bicategory / string-diagram line (most likely).**
Bonchi, Seeber, Sobociński, *Graphical Conjunctive Queries*, CSL 2018
([Dagstuhl](https://drops.dagstuhl.de/opus/volltexte/2018/9680), arXiv
1804.07626). Rebuilds conjunctive queries as string diagrams over binary
relations; query containment is axiomatised *exactly* by Carboni & Walters'
**cartesian bicategories of relations**. No attribute names anywhere — wires
carry position. Complete axiomatisation, which is the "fits a proof assistant"
property. This matches all three of the remembered selling points at once.

Its continuation is the direct answer to "what happened to that": it **grew into
full first-order logic.**
- *Diagrammatic Algebra of First Order Logic*, Bonchi, Di Giorgio, Sobociński,
  **LICS 2024** ([DOI](https://dl.acm.org/doi/10.1145/3661814.3662078), arXiv
  2401.07055)
- *The Calculus of Neo-Peircean Relations*, arXiv **2505.05306** (May 2025) —
  "a string diagrammatic extension of the calculus of binary relations with the
  same expressivity as first order logic and a complete axiomatisation",
  obtained by combining *cartesian* and *linear* bicategories.
- Also in the neighbourhood: *Deconstructing the Calculus of Relations with Tape
  Diagrams* (arXiv 2210.09950), *String Diagrams for Regular Logic* (2009.06836).

The stated reason the syntax had to go diagrammatic is worth quoting because it
bears directly on the library question: *"by moving from traditional syntax
(cartesian) to a diagrammatic one (monoidal), it is possible to have complete
axiomatisations for the full calculus."* Read that as a warning — the thing that
made it work is **two-dimensional notation**, which is precisely what a textual
library cannot have.

**2. The allegory / Algebra-of-Programming line.** Freyd & Scedrov's allegories;
Bird & de Moor, *Algebra of Programming* (1997); J.N. Oliveira, *Program Design
by Calculation* ([PDF, Univ. Minho](https://www.di.uminho.pt/~jno/ps/pdbc.pdf))
— **still a live draft, last updated February 2026.** Relations are typed arrows
`A ~> B`; composition, converse, meet, residuals; the modular law does the work.
This is the tradition that most literally says "binary relations, typed, no
column names, good for calculation".

**3. Relational lattices** (Tropashko & Spight): reduce Codd's six operators to
**two** — natural join and inner union — as lattice meet and join. Genuinely "a
more generalised relational algebra". But it *keeps* named attributes, so it
fails the no-names half of the memory. Fate below.

**4. The 1970s binary data model**: Abrial, *Data Semantics* (IFIP, 1974);
Nijssen's "binary modeling" (1975–76) → NIAM → **Object-Role Modeling** (Halpin,
1989; book 3rd ed. 2008). This is the one that actually competed with Codd and
lost commercially.

If the memory is of something read recently and it felt like PL rather than
databases, it is almost certainly (1). If it felt like a book or lecture notes
with lots of equational proofs, (2).

---

## What happened to each

| line | fate |
|---|---|
| Cartesian bicategories / string diagrams | **Thriving.** CSL 2018 → LICS 2024 → arXiv 2505.05306 (2025). Went from conjunctive queries to full FO with a complete axiomatisation. |
| Allegories / AoP / point-free calculation | **Alive, slow, academic.** The line Matthias was remembering — full arc below. Oliveira's book still in draft after ~20 years (Feb 2026). Never crossed into industry. |
| Relational lattices | **Ran into a wall.** Litak, Mikulás & Hidders axiomatised them and found they "do not seem to fit anywhere into the rather well investigated landscape of equational theories of lattices"; with the header constant the **quasiequational theory is undecidable**, and embeddability into relational lattices is undecidable (arXiv 1607.02988). Santocanale, *Relational Lattices via Duality*, continued it. Beautiful, but the metatheory is hostile. |
| Binary data model (Abrial/NIAM) | **Lost the database war, won elsewhere.** Abrial's model fed into Chen's ER model and into **Z and B**. NIAM became ORM, which survives as a *modelling* notation, not a query algebra. |
| Tarski's calculus itself | **Survives inside graph/tree query languages.** Regular path queries, XPath and SPARQL are identifiable with fragments of TRA. So the binary calculus did win — just in graph databases, where the data genuinely is binary edges. |

The venue for all of this is **RAMiCS** (Relational and Algebraic Methods in
Computer Science, since 1994). RAMiCS 2026 was Będlewo, April 7–10, 2026:
**18 papers accepted from 23 submissions.** That number is the honest measure of
the field's size — this is a small, durable community, not a growth area.

---

## What happened to *that* paper specifically

A clean four-step arc, and the endpoint is not where you would guess.

**1. 2005 — the paper.** FD theory in the binary pointfree calculus.
TR DI-PURe-05.01.01 → *First Steps in Pointfree Functional Dependency Theory*.

**2. Late 2000s — absorbed into data refinement, not pursued as database
theory.** Oliveira did not go on to build "a relational algebra". He folded the
FD machinery into a general calculus of **data-representation change**:
*[Transforming Data by Calculation](https://link.springer.com/chapter/10.1007/978-3-540-88643-3_4)*
(GTTSE 2007/09), with the *no loss / no confusion* principle for
representations, and
*[Extended Static Checking by Calculation Using the Pointfree Transform](https://link.springer.com/chapter/10.1007/978-3-642-03153-3_5)*
(LerNet 2008/09). The Minho **2LT** two-level-transformation tooling is the
implementation side. So the FD result became a lemma inside a refinement
calculus. Databases were the example, not the target.

**3. 2012–2015 — he generalised the base structure instead: relations became
matrices.** This is the real answer to "what happened to it".
- *Towards a Linear Algebra of Programming*, **Formal Aspects of Computing
  24(4–6):433–458, 2012**
- Macedo & Oliveira, *[Typing Linear Algebra: A Biproduct-Oriented Approach](https://arxiv.org/pdf/1312.4818)*,
  **Science of Computer Programming 78(11):2160–2191, 2013**
- *[A Linear Algebra Approach to OLAP](https://link.springer.com/article/10.1007/s00165-014-0316-9)*,
  Formal Aspects of Computing, 2015 — and the talk title says the thesis
  plainly: *"Do the middle letters of OLAP stand for Linear Algebra?"*
- *[Preparing Relational Algebra for "Just Good Enough" Hardware](https://link.springer.com/chapter/10.1007/978-3-319-06251-8_8)*,
  RAMiCS 2014

The move: a binary relation is a Boolean matrix; keep the typed point-free
calculus and swap the Booleans for an arbitrary **semiring**, and you get
probabilistic, weighted and OLAP settings for free. Note this is *the same
generalisation axis* as Kepner's associative arrays, reached from the opposite
direction — from program calculation rather than from big-data systems.

**4. Now — it is a chapter, not a programme.** Everything above rolls up into
*Program Design by Calculation*, draft last updated **February 2026**.

**And the convergence worth flagging.** The 2025 JFP theoretical pearl
*[Point-free calculational proofs and program derivation in linear algebra using
a graphical syntax](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/pointfree-calculational-proofs-and-program-derivation-in-linear-algebra-using-a-graphical-syntax/44175D6BFE57C9906F2D50B4D51F915E)*
(Mota, Paixão & Martelotte, UFRJ/IMPA — **not** Oliveira's group) does
point-free linear-algebra calculation in **string diagrams**. So the two
independent traditions in this note — Oliveira's typed point-free calculus and
Bonchi/Sobociński's cartesian bicategories — have both ended up at
semiring-generalised relations *and* at two-dimensional syntax, without
importing it from each other. That is weak but genuine evidence that the 2-D
notation is doing real work rather than being a stylistic preference of one
school. It sharpens caution 2 below from "a worry" to "twice-observed".

---

## The proof-assistant half of the memory is the strongest part

This is where the binary framing has actually paid off, and there is shipped
code:

- **Damien Pous, `coq-relation-algebra`** ([GitHub](https://github.com/damien-pous/relation-algebra),
  [page](https://perso.ens-lyon.fr/damien.pous/ra/), on opam; Rocq port written
  up at [hal-05007316](https://hal.science/hal-05007316v1)). Covers everything
  from partially ordered monoids up to **residuated Kleene allegories** and KAT.
  The design note that matters for us: *"algebraic structures are generalized in
  a categorical way, with composition typed like in categories, allowing the
  library to reach heterogeneous models like rectangular matrices or
  heterogeneous binary relations, where most operations are partial."* That is
  exactly the claim "binary relations fit a type system better" — cashed out and
  working. Ships **axiom-free decision procedures** for KA and KAT.
- **Wolfram Kahl, RATH-Agda** — dependently-typed formalisation of category and
  allegory theory in Agda (*Dependently-Typed Formalisation of Relation-Algebraic
  Abstractions*, RAMiCS 2011; RATH-Agda 2.0.0, 2014, ~456pp of literate output).
  Kahl's summary is blunt and relevant: this style works in Agda *"far beyond
  what can be achieved even in Haskell."*
- Kahl also did the Haskell version: **Semigroupoid Interfaces for
  Relation-Algebraic Programming in Haskell**, MPC 2006 — a point-free
  relation-algebraic interface over ordinary Haskell collections, with the
  theory generalised from categories to **semigroupoids** specifically to make
  the interface fit. That paper is the closest existing thing to the library
  Matthias wants, and it should be read first.

So: the memory is right, and the receipt is Pous's library plus Kahl's.

---

## Bearing on "relations as first-class values, ideally as a library"

**The type is easy, the plumbing is the problem.** `Rel a b` gives you
`id`, `(∘)`, `converse`, `(∧)`, `(∨)`, `⊥`, `⊤`, residuals — a clean typeclass
tower ending at allegory / residuated Kleene allegory, and Pous already has the
lattice of structures worked out. What you do *not* get for free is what named
columns were invented to provide: reaching a value three joins away without
manually routing it. In the binary world that routing is copy (`Δ : a ~> (a,a)`)
and discard (`! : a ~> ()`), which is fine in a string diagram and turns into
combinator soup in text. Oliveira's whole "pointfree transform" exists to move
back and forth between the two styles, which is itself evidence that neither
style alone is usable.

**Recovering n-ary relations from binary ones** goes through tabulation — in a
tabular allegory every relation is a tabulation of a pair of functions, which is
what turns `A ~> B` into "a set of pairs" and lets `A ~> (B, C)` stand in for a
ternary relation. *(Recalled, not verified in this session — check Freyd &
Scedrov before relying on it.)* Practically: columns become projections lifted
to relations, and "join on a shared column" becomes fork-then-meet.

**Prior art for the language-integration side**, which is a different tradition
and worth not reinventing:
- **Datafun** (Arntzenius & Krishnaswami) — functional Datalog, first-class
  relations, monotonicity tracked *in the type system*. The closest thing to
  "relations as first-class values with a real type discipline".
- **Flix** — Datalog programs as first-class values that can be stored, passed
  and returned; extends Datalog from relations to lattices. *Flix: A Design for
  Language-Integrated Datalog*, **OOPSLA/PACMPL 2025**
  ([DOI](https://dl.acm.org/doi/10.1145/3763126)). Their "inject–program–query"
  pattern is a concrete answer to how relation values compose with ordinary code.
- **Rel** (RelationalAI), SIGMOD 2025 companion / arXiv 2504.10323 — the
  opposite bet: a whole language rather than a library, explicitly to avoid the
  "query sublanguage embedded in a host language" split.
- **Fixen** ([fixen-lang.org](https://fixen-lang.org/guides/getting-started/00-what-is-fpop/)) —
  "fixed-point-oriented programming": named relations plus Datalog-style rules,
  compiled to Haskell, with optimisation (processing order, indexing) as
  directives separate from the logic. The same design cell as Datafun/Flix —
  lattice-valued facts, monotonicity, Kleene iteration — as a code generator
  rather than a library. Reads as supply-side (a research vehicle) rather than
  evidence of demand. Their two-rule Dijkstra is the cleanest illustration yet
  of why lattice-valued relations are the missing capability here: shortest
  path is `min`-aggregation under recursion, which a set-valued algebra cannot
  express, and which is exactly the extension flagged below for "when
  aggregation has to interact with recursion".
- **Associative arrays / D4M** (Kepner) — every relation is a semiring-valued
  binary map; claims to unify SQL, NoSQL and NewSQL under one algebra.
  Implemented in Python, Julia and Matlab/Octave, so there is running code. A
  genuinely different generalisation axis (vary the semiring) from the ones above.
- **Ampersand** (Joosten) — relation algebra as an actual *typed programming
  language* with a compiler, used in two large Dutch government projects; *Relation
  Algebra as programming language using the Ampersand compiler*, JLAMP 100 (2018);
  [`ampersand` on Hackage](https://hackage.haskell.org/package/ampersand). This
  is the existence proof that the point-free relational style can be shipped —
  and the place to look for what it cost.
- **Alloy** — relations of arbitrary (but uniform) arity, dot-join generalised
  beyond the binary case. Useful as a data point that a "relations are the only
  values" language is usable by non-specialists.

**Host language, if it becomes a library.** Kahl's two papers bracket the answer:
Haskell needed semigroupoids and still fell short; Agda was comfortable. So the
honest shortlist is Agda / Idris / **Lean 4** / Rocq. Lean 4 is the interesting
one and does not appear anywhere in the literature found — it is a proof
assistant *and* a real programming language *and* has the metaprogramming to give
relational notation a decent surface syntax. Worth a look before defaulting to
Haskell.

---

## Design constraint from Matthias: point-free is the core, not the surface

Stated 2026-08-01: the point-free framing is **for theory, backend and proofs.
Not for the user interface.** That is a two-layer design — pointful/named
surface, point-free core — and it changes the risk picture substantially. Most
of what follows was written before this was clear; the parts it invalidates are
marked.

**It is what the tradition already does.** Oliveira's "**pointfree transform**"
*is* the pointwise ↔ point-free translation, and it is the method of the
ESC-by-calculation paper: state and read the thing pointwise, calculate on it
point-free. So the split is not a compromise imposed on the calculus from
outside — it is how the calculus is actually used by the people who built it.
It is also, incidentally, the standard database architecture: SQL surface,
algebra core, and nobody reads the plan.

**The 2-D worry largely dissolves for a backend.** The reason string diagrams
kept appearing is that they are the *human-facing* syntax for free symmetric
monoidal categories. Combinatorially they are just **typed hypergraphs**:
Bonchi, Gadducci, Kissinger, Sobociński & Zanasi's *String Diagram Rewrite
Theory* [I](https://arxiv.org/pdf/2012.01847) /
[II](https://arxiv.org/pdf/2104.14686) /
[III](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/string-diagram-rewrite-theory-iii-confluence-with-and-without-frobenius/F6E1207A100A9F1CFB48FFBAEC785F61)
establishes that diagram rewriting modulo the SMC laws is exactly **double-
pushout rewriting of hypergraphs** subject to a convexity condition, with
confluence theory to match. A backend can hold the hypergraph and never draw
anything. There is running code:
[**chyp**](https://github.com/akissinger/chyp) (Kissinger — an interactive
prover for free SMCs over a signature, over cospans of hypergraphs, and it
**works with conventional term syntax *and* diagrams**, which is precisely the
two-layer arrangement), [**DisCoPy**](https://docs.discopy.org/en/main/)
(Python; `Diagram` and `Hypergraph` structures, rewriting, functors), and
Cartographer.

**And the pointful surface over point-free combinators is a solved problem in
Haskell.** Ross Paterson, *[A New Notation for Arrows](https://www.staff.city.ac.uk/~ross/papers/notation.pdf)*
(ICFP 2001) — `proc` notation, limited application and abstraction for things
that cannot be factored as functions, translated to plain combinators by a
preprocessor that "produces quite optimized output". Cleaner theory in Lindley,
Wadler & Yallop, *[The Arrow Calculus](https://homepages.inf.ed.ac.uk/wadler/papers/arrows/arrows.pdf)*.
`Rel a b` should support `arr` (every function is a relation), `first`,
`ArrowChoice` and `ArrowPlus` (union); `ArrowApply` it will not have, since Rel
is not cartesian closed. *(Instance claims are reasoning, not verified — check
before relying.)* If that holds, GHC's arrow notation is a ready-made pointful
surface, and its known clunkiness is survivable when it is not the thing users
type every day.

**The payoff of the point-free core is decidability, and it is already built.**
Pous's `relation-algebra` ships axiom-free decision procedures for KA and KAT
that operate on exactly this kind of term. A point-free core is what makes
"is this rewrite sound?" a question a machine can answer.

**Where the risk moves to.** Two places, both concrete:

1. **The translation, in the usual compiler way** — errors, and debugging, now
   happen in a representation the user never wrote. Mapping a core-level
   failure back to surface names is the classic hard part, and it is *worse*
   here than in SQL because point-free plumbing deliberately erases the names.
2. **Optimisation must work modulo the monoidal laws.** This is the sharp one:
   the whole reason SDRT needed convex DPO rewriting on hypergraphs is that
   naive term rewriting on point-free terms does **not** correctly implement
   rewriting modulo SMC structure. If the core is a term tree and the rewrites
   are pattern matches on it, that is a known-wrong design. Budget for the
   hypergraph representation from the start, or reuse chyp/DisCoPy.

## Second constraint: an EDSL, with host type checking

Stated 2026-08-01: it should be an **EDSL** that interacts seamlessly with the
host language, and **host type checking must work**. Matthias suggests Oleg's
tagless-final work as the frame. That is a good fit, for a reason more specific
than "tagless-final is nice".

**The point-free calculus is already in tagless-final shape.** A final embedding
is a typeclass whose methods are the object language's combinators; the
relational calculus *is* a set of typed combinators. So there is no encoding
step — the object language and the class signature are the same thing:

```haskell
class Category r where  id :: r a a;  (.) :: r b c -> r a b -> r a c
class Category r => Allegory r where
  converse :: r a b -> r b a
  (/\)     :: r a b -> r a b -> r a b     -- modular law governs the interaction
```

Reuse **Pous's structure lattice** (partially ordered monoid → allegory →
division allegory → residuated Kleene allegory → KAT) as the *class hierarchy* —
he has already worked out which axioms buy which operations, and the classes
should be cut on those joints so that a backend can advertise exactly what it
supports. Kahl's MPC 2006 Haskell interface is the same idea done once already,
and the reason it needed **semigroupoids** rather than categories is exactly the
kind of detail this reuse is meant to inherit rather than rediscover.

**The three legs are three interpretations.** Theory, backend and proofs stop
being separate artefacts: one program, interpreted as an evaluator over finite
relations, as a hypergraph for rewriting, and as a proof obligation. This is the
tagless-final selling point and it lines up exactly with what is wanted here.
Kiselyov's claim is the one that answers the type-checking requirement directly:
final interpreters "need no advanced type-system features such as GADTs,
dependent types, or intensional type analysis", yet the metalanguage's type
system statically assures each object program is well-typed and closed, and each
interpreter type-preserving **by construction**.

**On the usual objection — corrected by Matthias, 2026-08-01.** The standard
complaint is that you cannot pattern-match on a final embedding. That is not
the situation: **you get a term tree from a final encoding for free, as one
more interpreter** — the one whose `repr` is an algebraic data type mirroring
the class. Initial and final encodings are inter-convertible; Kiselyov treats
the "seemingly impossible pattern-matching" explicitly. Availability of a term
tree was never the issue.

It is even cheaper here than in general, and for a reason worth noticing:
**the core has no binders.** Initial↔final round trips are fiddly exactly where
HOAS or de Bruijn are involved, and this object language is first-order
point-free combinators — binders exist only in the *surface* elaboration and
are gone by the time anything reaches the class signature. So the term-tree
interpreter is a plain ADT with one constructor per method, written
mechanically.

*Qualification added later, once predicates were settled:* this holds of the
**relational** layer only. If the scalar/predicate language `v` uses HOAS —
`v a -> v Bool`, which is the recommendation below — then *that* layer does
have binders, and its term-tree interpreter needs the usual fresh-variable
supply. Still routine, but it is not free the way the relational layer is, and
the stratification is what confines the cost to the small language.

What survives, and it is a smaller and more precise claim: materialising is
free, but *which* materialisation you rewrite in is still a real choice, and
the term tree is the wrong one — **not because you cannot pattern-match it,
but because pattern-matching it is unsound for this algebra**, where rewriting
has to be modulo the monoidal laws. So the architecture is: tagless-final is
the typed front door, and the term tree and the hypergraph are two
materialising interpretations on equal footing. Pick the hypergraph for
rewriting on soundness grounds; the term tree remains useful for everything
that is genuinely syntactic (printing, hashing, serialising, tests). Going back
is the ordinary tagless-final move — re-interpret into whatever `repr` the
caller wanted. Kiselyov's compositional-interpreter transformations still cover
the cheap local cases without materialising anything.

### The constraint that will actually bite: Rel is not cartesian

This is the load-bearing fact for an EDSL, and it is easy to get wrong because
the notation lies. In **Rel**, the cartesian product of sets is the *monoidal
tensor*, **not** the categorical product: a relation `A ↝ B ⊗ C` is strictly
more than a pair of relations `A ↝ B` and `A ↝ C`. The monoidal unit `{*}` is
not the terminal object, so Rel is not even semicartesian. Copy and discard
exist but are **not natural**. (The actual categorical product and coproduct in
Rel are both disjoint union — a biproduct.) Four consequences:

1. **Compiling-to-categories does not apply as-is.** Conal Elliott's
   [`concat`](http://conal.net/papers/compiling-to-categories/) and
   con-kitty's [`categorifier`](https://github.com/con-kitty/categorifier)
   interpret Haskell into *any cartesian closed category*. Rel is not one. There
   is some traced-monoidal support, but CCC is the design centre, so "write host
   lambdas and let a plugin categorify them" is not the free lunch it looks like.
2. **No `ArrowApply`** — that needs closure Rel does not have. Plain
   `Arrow`/`proc` is fine and is in fact exactly the right expressive ceiling:
   first-order plumbing, no higher-order relation application.
3. **Variable reuse must elaborate to an explicit copy node, and non-use to
   discard**, precisely because copy and discard are not natural. So the surface
   language behaves like a **linear/affine calculus with explicit contraction
   and weakening** — which is the same fact, seen from the syntax side, as
   conjunctive queries corresponding to cartesian *bi*categories rather than
   cartesian categories. Practically: a comprehension surface where every
   variable is a wire and the elaborator inserts the copies.
4. **Two different products in the API, and conflating them will cause bugs**:
   `⊗` (set product — what tuples and "columns" use) and `⊕` (disjoint union —
   the actual biproduct). Do not call both of them "product".

### Why the binary framing earns its keep here specifically

This is the concrete cash value of the original intuition. Named-column
relational EDSLs pay for the names in type-level machinery: Rel8's own
description is that it uses "a lot of type level magic" while *aiming* for
predictable inference — type-level strings, generics, HList-alikes, row
polymorphism. `Rel a b` needs **two type parameters and nothing else**. Columns
are components of host product types, so host tuples do the work that type-level
label machinery does elsewhere. That is a real and large simplification, and it
is the strongest single argument for the binary framing in an EDSL setting.

**The bill, stated plainly**, because it lands on the thing Matthias asked for:
type checking will *work*, but the **errors will be bad**. A mistake shows up as
a nested-product shape mismatch — `((a,b),c)` against `(a,(b,c))` — where a
named system would have said "you forgot to join on customer id". Tagless-final
adds its own well-known error problem on top: polymorphic `repr` produces
ambiguous types and long instance contexts. Worth designing against from day
one rather than discovering: newtype the wire types so they are not bare tuples,
and consider carrying a phantom label purely so diagnostics can name something
the core has deliberately erased.

**Host language.** Haskell and OCaml are Oleg's own ground and both work; OCaml's
module system is a genuinely good fit for the class hierarchy. Lean 4 remains
the alternative worth a look *if* the proofs leg should be native rather than
exported — macros for the surface, dependent types for wire shapes, and the
decision procedures living in the same language as the programs.

## Third constraint: point-free was only inspiration — keep the points if it pays

Stated 2026-08-01, in response to the type-error problem: the point-free work
was for inspiration, and if it does not buy anything, keep the variables. This
is the right call, and it costs less than the preceding sections imply, because
**two axes that this note has been treating as one are actually independent**:

| axis | what it buys | do we need it? |
|---|---|---|
| **binary / unnamed** relations, `Rel a b` | two type parameters instead of type-level label machinery — the whole type-checking win | **yes, this is the point** |
| **point-free** notation | equational calculation without capture/α bookkeeping; input format for KA/KAT decision procedures | only locally |

Everything Matthias wanted from the original memory sits in the first row.
Nothing in it requires the second. `Rel a b` with variables in the surface is
still `Rel a b`.

**And the two designs turn out to be the same design.** The hypergraph core is
not a point-free artefact. The hypergraph *of a conjunctive query* is defined
with **vertices = the variables in the body** and one hyperedge per atom
carrying the variables it mentions; Chandra–Merlin containment is a
homomorphism of exactly those hypergraphs. Bonchi et al. say the same thing
from the other side: their syntax "does not have explicit variables", and free
variables are "mirrored by **dangling wires**". So wires *are* variables. String
diagrams are not a way of eliminating points — they are a way of **putting the
points back** while keeping the algebra, which is also what allegory products
and projections do. Keeping the points and using the hypergraph core are one
choice, not two.

**This upgrades the rewriting story rather than abandoning it.** The earlier
caution — rewriting must be modulo the monoidal laws, so a term tree is the
wrong core — re-expresses in the pointful world as **conjunctive query
containment, the chase, and ordinary query optimisation**. Same mathematics,
vastly better tooling: decades of database engineering, known complexity,
working implementations, and people who can be hired. Convex DPO rewriting on
hypergraphs is the categorical presentation of the same object with a far
thinner ecosystem. Prefer the database presentation and borrow the categorical
one for proofs.

**It also fixes the caution that landed on the stated requirement.** With
variables, the join variable has a *name*, so diagnostics can cite it. The
`((a,b),c)` versus `(a,(b,c))` failure mode was a consequence of tuple plumbing
standing in for names — drop the plumbing and most of it goes. The mitigations
in the previous section (newtyped wires, phantom labels) become optional
polish rather than load-bearing.

**What to actually keep from the point-free literature**, notation aside:

- **The algebra** — which operators and which axioms. Pous's structure lattice
  (allegory → division allegory → residuated Kleene allegory → KAT) is the
  design document for the class hierarchy, and it does not care what the
  surface looks like.
- **The typing discipline** — relations as typed arrows with a source and a
  target. This is the actual content of "binary relations fit a type system".
- **The laws as executable oracles** — modular law, converse laws, residual
  adjunctions. Property tests, whatever the notation.
- **Point-free as an internal normal form, locally.** Where a decision
  procedure or a machine-checked proof needs it — the KA/KAT fragment is the
  obvious case — translate into it for that step. Oliveira's pointfree
  transform is exactly this move, used deliberately and not globally.

**The likely surface, then: monad comprehensions.** Comprehension notation is
syntactic sugar for chained Kleisli composition, and over the powerset monad on
`Set` it is precisely set comprehension — so `Rel a b ≅ a -> Set b` gives a
surface that is already native in the host and type-checks with no notation
machinery at all. That line is very well developed: Trinder & Wadler → Buneman
et al. → Wong's normalisation → the **Kleisli** system and **Links**, i.e. the
whole language-integrated-query tradition.

**The boundary to check early:** the monadic/comprehension fragment naturally
covers select–project–join–union — positive relational algebra. **Difference,
negation and the residuals do not come from the monad** and have to be added as
primitives, at which point normalisation results stop applying automatically.
Find out where that line falls before committing to comprehensions as *the*
surface rather than one of several. *(Structural claim, not verified against a
source this session.)*

**Consequently, promote a paper this note demoted.** Gibbons, Henglein, Hinze &
Wu, *Relational Algebra by Way of Adjunctions* (ICFP 2018, Distinguished Paper)
was filed below as "adjacent, not a match" *because* it keeps points and works
with comprehensions over bags. Under the new constraint that is precisely the
recommendation: it is the pointful, comprehension-based, Haskell-typed account,
with adjunctions explaining join and grouping and graded monads explaining
indexing. **Read it early.**

## Host-language fit

Asked 2026-08-01. Rating what the *EDSL* needs, which after the decisions above
is: a two-parameter type `Rel a b`; a class/signature hierarchy cut on Pous's
joints; a comprehension-ish pointful surface; several interpretations of one
program; and somewhere to put the laws.

| host | fit | the one thing that decides it |
|---|---|---|
| **Haskell** | **high** | tagless-final is native and Kahl already built this here once |
| **OCaml / OxCaml** | **high** | signatures instead of classes ⇒ *legible errors*, the one caution that landed on the requirement |
| **Lean 4** | **high ceiling, high cost** | laws become theorems instead of property tests |
| **Rust** | **medium** | GATs make it possible; you pay encoding noise everywhere else pays nothing |
| **Python** | **medium, and better than expected** | `Rel[A, B]` is exactly what Python generics do well — but no HKT, hard stop |

**Haskell.** `class Rel (r :: * -> * -> *)` needs higher kinds, which are free
here; `MonadComprehensions` gives the pointful surface as a language extension;
`proc` notation is there if the point-free layer is ever wanted. The decisive
argument is not a feature though — **Kahl built the relation-algebraic interface
in Haskell in 2006 and wrote down what had to bend** (semigroupoids rather than
categories). Starting anywhere else means rediscovering that. Weakness is
exactly the caution already flagged: polymorphic `repr` produces ambiguous
types and long instance contexts, and no dependent types means shape reasoning
stays in tuples.

**OCaml / OxCaml.** Oleg's other home ground, and tagless-final there is done
with **module signatures and functors** rather than type classes. More verbose
at use sites, but the error story is much better — checking a module against a
signature produces a comprehensible mismatch, where constraint solving produces
a wall. Given that bad diagnostics are the main cost of this design, that is a
real argument, not a stylistic one. GADTs are available for the initial-encoding
interpreter, and `let*` binding operators give the monadic surface.

OxCaml adds three things that are on-topic to a suspicious degree:
**comprehensions** as an actual language extension (set-builder notation for
lists and arrays — the surface, for free); **modes**, including a *linear*
modality; and unboxed types plus stack allocation for a backend. The modes
point is tempting because the surface language wants a linear/affine discipline
with explicit contraction — but **that is almost certainly a false friend**:
modes were designed for memory safety and at-most-once invocation, not as a
resource discipline for a DSL's variables, and there is no evidence they can
express "this relational variable is used twice, insert a copy". Worth thirty
minutes to disprove, not more. General OxCaml caveat: it is a branch, with the
tooling and ecosystem risk that implies.

**Lean 4.** The highest ceiling. Dependent types, typeclasses with higher
kinds, and a real macro/elaboration system, so the surface can be *syntax*
rather than an encoding of syntax. The distinguishing feature is the proof leg:
laws become theorems rather than property tests, and decision procedures in the
Pous style could live in the same language as the programs they decide — the
one host where "theory, backend, proofs" is genuinely one artefact. Costs are
equally real: thin ecosystem for data backends, runtime performance, and
elaboration/typeclass debugging as a skill of its own. Right choice if this is
primarily a theory-and-proofs project with a demonstration backend; wrong one
if it is primarily a working query library.

**Rust.** GATs (1.65+) made final-style embedding practical and people do it —
there are worked write-ups of tagless-final in Rust, and a `lifted` crate for
the HKT encoding. Genuine strengths: proc macros can give a real surface
syntax, and the backend can be fast. Genuine costs: no native higher kinds, so
every `repr`-polymorphic signature carries encoding noise; coherence and orphan
rules make "many interpreters" less free than elsewhere; lifetimes leak into
combinator types; no `do`-notation, so comprehensions must be a macro. Possible
and increasingly done — you just pay in every signature.

### Python — the interesting one

**The headline is a convergence.** Python's type system is bad at exactly one
thing this design already threw away, and good at exactly what it kept.
`Rel[A, B]` is a plain two-parameter generic — PEP 695 syntax, supported by
every checker — and composition types cleanly with a method-level parameter:

```python
class Rel[A, B]:
    def __matmul__[C](self, other: "Rel[B, C]") -> "Rel[A, C]": ...
    def __invert__(self) -> "Rel[B, A]": ...          # converse
    def __and__(self, other: "Rel[A, B]") -> "Rel[A, B]": ...
```

Named-column relations would need row polymorphism or extensible records, which
Python has never had and which is why typed DataFrames (pandas-stubs, pandera)
are perennially painful. **So the decision that started this whole thread —
drop the column names — is precisely the decision that makes Python viable.**

Two further things Python is unusually good at here: **operator overloading**
(`@` for composition and it even reads correctly, `~` for converse, `&`/`|` for
meet and join, `<=` for inclusion) gives a legible algebra surface with no
macros at all; and **comprehensions are native set-builder notation**.

**The scalar language `v` is also unusually pleasant in Python** — an `Expr[T]`
class with overloaded comparison and arithmetic operators is exactly how Ibis,
polars and SQLAlchemy build their predicate DSLs, and it needs no HKT, so this
part of the design does not hit Python's wall. It has one concrete wart worth
knowing in advance: **overloading `__eq__` to return `Expr[bool]` rather than a
`bool` breaks hashing and the `in` operator** for those objects, and every
library in this space has hit it (polars issue #4069 is the same complaint).
Plan for `Expr` objects being unhashable, or give equality a named method and
leave `==` alone.

**The hard wall: no higher-kinded types.** A program polymorphic in `repr` —
the central tagless-final move — cannot be typed in Python. This is not a
maturity gap; the typing *specification* has no such notion, and `ty` listing
"higher-kinded generics" among its unimplemented advanced features is a symptom
rather than the cause. The consequence is concrete: **go initial, not final.**
Build one symbolic `Rel[A, B]` term type and have interpreters consume it.
Object programs still type-check; what is lost is the "one program, many
statically-checked interpretations" property, which was a stated attraction.
That is a real loss and should be priced, not glossed.

**Second obstacle: comprehensions cannot be intercepted without tricks.**
List/set/dict comprehensions are eager; **generator expressions are lazy**
(corrected by Matthias — and that laziness is exactly what makes Pony's trick
possible, since the genexp object can be handed over before it runs). But lazy
or not, what you hold is a *value*, not syntax. Capturing one as a query means
decompiling bytecode — which **PonyORM genuinely does**: a
visitor over bytecode instructions with an AST-valued stack, reassembling the
generator expression into an AST and thence SQL. So the precedent exists and
works, but it is version-fragile in the way that ruins a library's decade. The
alternative is the operator/method-chaining surface — no interception needed,
and it is what Ibis, SQLAlchemy and polars do. Take that unless the
comprehension surface is worth a bytecode dependency.

**Checkers.** Nothing here needs an exotic feature, which is the point: the
design lives inside the well-supported subset, so mypy, pyright and pyrefly
should all cope, and `ty` mostly. Current sensible default is **pyright in
strict mode** as primary with `ty` as a fast pre-commit path; mypy if its
plugin ecosystem is needed. Worth an early spike that type-checks the same
twenty-line `Rel` skeleton under all four, since disagreement between checkers
on variance and method-level type parameters is where this would actually break.

**Verdict on Python:** a good *demonstration and teaching* host, and a
plausible production one for a runtime-evaluated backend. Not the host for the
proof leg, and not the host if statically-checked multiple interpretations
matter.

## miniKanren, and where the target actually sits

Asked 2026-08-01, with the observation that miniKanren looked impractical for
simple business logic. That reading is correct, and for structural reasons —
this is a mismatch of evaluation model, not a difficulty of the notation.

Order the "relations as first-class" designs by how much **search** you are
buying:

| | relations are | evaluation | runs backwards | terminates |
|---|---|---|---|---|
| Codd / relational algebra | finite sets of ground tuples | set-at-a-time, planned | no | always |
| Datalog | + least fixpoint | semi-naive, bottom-up | no | guaranteed (no function symbols) |
| Datafun / Flix | + host language | as Datalog | no | guaranteed by monotonicity types |
| miniKanren / Prolog | goals over an open term space | goal-at-a-time interleaved search | **yes** | **not guaranteed** |

**Why the bottom row is wrong for this target.** Four things, none of them
about cleverness:

1. **Search versus evaluation.** miniKanren *solves*; relational algebra
   *evaluates*. Business logic over data you already have does not use the
   backwards-running power, so you pay the search tax for nothing.
2. **Goal ordering is semantically load-bearing.** The literature is explicit:
   termination depends on subgoal order, the same relation can be "dramatically
   slower in some modes and not terminate in others", and the fix is reordering
   by groundedness — i.e. hand-optimising the plan, which is exactly the job a
   query planner exists to take away.
3. **No aggregation, awkward negation.** Counts, sums, group-by and "customers
   with *no* orders" are the substance of business logic. Difference is
   primitive in Codd; negation in miniKanren is disequality constraints
   (cKanren) and is delicate; aggregation is absent.
4. **No indexes, no planner, no set-at-a-time anything.** Datalog engines do
   semi-naive evaluation, indexing and worst-case-optimal joins. miniKanren is
   a metacircular search.

Put positively: **Datalog is roughly miniKanren minus the features that made it
impractical here** — drop function symbols and open-term unification, evaluate
bottom-up set-at-a-time, and you trade running-backwards for guaranteed
termination and a planner. That is why Flix, Datafun, Soufflé and RelationalAI
all live in rows 2–3 and nothing serious for business logic lives in row 4.

**Two things worth taking from it anyway.**

- **The surface syntax is the same family.** The conjunctive-query-with-variables
  surface settled on above *is* logic-programming-shaped: a rule body with
  shared variables. What differs is only the engine underneath. So the pleasant
  part of miniKanren — writing relations rather than functions and letting
  shared variables do the joining — is available without any of the search.
- **Converse is the tractable fragment of "running backwards".** A binary
  relation has no privileged direction, so `R˘` gives directional freedom
  outright. The difference is that miniKanren's bidirectionality ranges over an
  unbounded term space and therefore costs search, whereas converse over finite
  relations costs *an index on the other side*. Same benefit, bounded price.
  **This is a good argument for the binary framing** and it is worth making
  explicitly when the project gets written up.

### Termination: Dhall, Datalog and miniKanren are three different mechanisms

Asked 2026-08-01: is miniKanren's ordering/termination problem the same shape as
what Dhall does for finiteness? **No — and the difference tells you which
technique is available here.**

| | mechanism | recursion? | what is guaranteed |
|---|---|---|---|
| **Dhall** | strong normalization of a total typed λ-calculus — the language simply lacks the constructs that could diverge | **none** (Church-encode if you must) | static and data-independent: every expression has a normal form |
| **Datalog** | finite Herbrand universe (no function symbols) + monotone least fixpoint | yes | the fixpoint exists and is reached in finitely many steps |
| **Datafun** | monotonicity tracked **in the type system**; monotonicity makes the fixpoint unique, and it is reached finitely if the semilattice has no infinite ascending chains | yes | as Datalog, but carried by types |
| **miniKanren** | — | yes | nothing; divergence is a property of the program *and* which arguments are ground |

So Dhall does not solve an ordering problem — it removes recursion, leaving
nothing to order. miniKanren has both recursion and search. The kinship
Matthias is sensing is real but sits one level up: both Dhall and Datalog
**restrict the language so that a global property becomes a theorem instead of
a hope**, and that is the right technique here. They just restrict different
things.

Which matters, because this project **needs** recursion — transitive closure is
org charts and bill-of-materials. So Dhall's answer (drop recursion) is
unavailable, and Datalog's (drop function symbols, get a finite domain) is the
standard one. **Datafun is the combination: Dhall's style of guarantee with
Datalog's power**, since monotonicity lives in the types rather than in a
syntactic side-condition. That is a specific reason to read Datafun carefully,
not a general recommendation.

One caveat applies to all three — but **stated more fairly than I first put it**
(Matthias, 2026-08-01). "Termination is not tractability" is true and was
uncharitable: Dhall's actual claim is about *accidents*, and their wording is
that you are "much less likely to **accidentally** create a configuration file
that loops indefinitely". That is the real value, and it transfers. The class
of bugs removed is the accidental one — a typo, a mis-ordered recursion, a base
case that never fires. What remains is deliberate or pathological blowup, which
is a much smaller and more visible category.

**And Datalog is strictly better than Dhall on this axis**, which is worth
noticing because it argues for row 2 again:

| | accidental divergence | cost legibility |
|---|---|---|
| Dhall | impossible | poor — an innocuous term can be astronomically expensive, with nothing in the syntax to warn you |
| Datalog | impossible | **good** — data complexity is polynomial with the exponent bounded by rule width, so the query shape tells you the cost |

So Datalog gives the accident-proofing *and* a cost model you can read off the
query. That is exactly what a planner needs, and it is also why the `opaque`
escape hatch for predicates is the thing that breaks the guarantee: an opaque
host function is a hole in the cost model, not just in the optimiser.

## What to take from Datalog

Flagged by Matthias as worth taking inspiration from — agreed, and it is the
row of the table this project actually lives in. Concretely:

- **Recursion with a termination guarantee**, by the finite-domain argument
  above. This is the capability plain Codd lacks and the reason to go past row 1.
- **Semi-naive evaluation** — only derive from facts that are new this round.
  It is the cheap ancestor of the DBSP/differential-dataflow incrementalisation
  already flagged as the interesting engineering, and worth implementing first
  because it is a page of code rather than a paper.
- **Stratified negation** as the disciplined answer to "customers with *no*
  orders" — precisely the case miniKanren fumbles.
- **Lattice-valued Datalog** (Flix) for when aggregation has to interact with
  recursion, which is the classic Datalog weak point: shortest-path and
  provenance want a semiring, not a set. Note this is the *same* generalisation
  axis Oliveira and Kepner both took — vary the semiring — arrived at a third
  time from a third direction.
- **The two existing language-integrated designs**, which are the direct prior
  art for this project and should be read before designing anything:
  **Datafun** (fixpoints in a functional language, monotonicity in the types)
  and **Flix** (Datalog programs as first-class values, with the
  inject–program–query pattern for making relations compose with ordinary code).
- Engine-side, if it ever gets that far: worst-case-optimal joins and **egglog**
  (Datalog plus equality saturation), which is where the rewriting layer and the
  query layer turn out to be the same machine.

## What Codd's examples imply once the data is in memory

Matthias's framing: exactly Codd's 1970 examples, with the recognition that the
concerns apply to ordinary in-memory values, not just shared data banks. That
framing is sharper than "a query language in your program", and it points at a
different headline feature.

Codd named three dependencies to be removed: **ordering dependence**,
**indexing dependence** and **access path dependence**. The in-memory analogue
is immediate and is something every program does:

> Choosing `dict[CustomerId, list[Order]]` **is** an access-path commitment.
> It privileges one traversal direction, it is an index chosen by hand, and
> when a new query pattern shows up the data structure gets reshaped and every
> call site with it.

Codd's claim was that this coupling is a defect and the fix is to state the
query and let something else choose the path. Applied to in-memory data, the
value proposition of the library is therefore **access-path independence for
ordinary collections** — declare `Rel[Customer, Order]`, let the library hold
whichever indexes the query load implies, and change queries without reshaping
data.

Two consequences worth writing down now:

- **The interesting engineering is index *selection*, and — with the constraint
  in the next section — not maintenance.** The algebra is the understood part;
  choosing and holding the right access paths is not. See below for why
  maintenance mostly drops out.
- **Transitive closure is not academic decoration.** Org charts,
  bill-of-materials and reachability are ordinary business logic, and they are
  exactly what plain Codd cannot express and Datalog can. That is where the
  Kleene star in Pous's structure lattice — residuated *Kleene* allegory —
  earns its place rather than being inherited for completeness. It is also the
  boundary where row 1 stops being enough and row 2 is needed.

## Two assumptions made explicit: everything in memory, relations immutable

Stated 2026-08-01. Both were implicit; both are load-bearing enough to be
axioms rather than assumptions. **This corrects an over-claim above** — I said
the interesting engineering was index *maintenance* and pointed at incremental
view maintenance. Under immutability that is mostly the wrong target.

**Immutability is what makes the whole equational agenda legitimate.** Every law
in this note — allegory laws, rewriting modulo anything, plan choice, common
subexpression elimination — needs referential transparency. With mutable
relations, `r ∪ s` cannot be safely reordered, cached or shared, and the algebra
becomes decorative. So this is not a simplifying convenience; it is the premise
that lets the theory be used at all. Worth saying out loud in the eventual
README.

Four things follow directly:

1. **Index selection replaces index maintenance.** An index of an immutable
   relation is a *pure function of that relation*, so it can be computed lazily
   on first use, memoised on the value, and **never invalidated**. That deletes
   the entire hard half of the problem. `r.index_by(π)` is a cache, not a
   subscription.
2. **Derived relations can be thunks.** `r @ s` builds a plan; observation
   forces it. Safe precisely because nothing underneath can move.
3. **Hash-consing and memoisation are sound for free.** Equal queries over equal
   inputs give equal results, so interning relations makes equality cheap and
   makes cross-program CSE valid. This is dangerous under mutation and free here.
4. **Codd's loop closes properly.** The relation is the *value*; indexes are
   derived caches chosen lazily. A program then **cannot** depend on the access
   path, because the access path is not part of the value. That is
   access-path independence achieved by construction rather than by discipline.

**Where IVM legitimately comes back — demoted, not deleted.** DBSP is
*stream*-based: it computes over a stream of versions. A sequence of immutable
relations **is** that stream. So if the program derives a view once from one
base, skip IVM entirely; if it recomputes derived relations across successive
versions — event logs, per-transaction recompute, undo, time travel, all common
in exactly the business logic being targeted — then IVM is the optimisation for
"derive from a *slightly different* immutable input", and immutability makes it
sound by construction instead of requiring change-tracking machinery. Keep
[DBSP](https://www.vldb.org/pvldb/vol16/p1601-budiu.pdf) (Budiu, Chajed,
McSherry, Ryzhyk & Tannen, VLDB 2023 best paper) filed as a known optimisation
rather than as the headline.

**The cost is allocation.** Persistent structures with structural sharing, plus
a lazily built index per access pattern, is more memory and more GC pressure
than mutating in place. For in-memory business logic that is usually the right
trade, but it is the real one and it should be measured rather than assumed.

### Immutable interface, mutable implementation

Matthias, 2026-08-01: conceptually immutable, but efficient insertion is needed
in practice — via linear types, or copy-on-write in Python. That is exactly the
right move, and it is a well-populated design space rather than a hope. The
pattern is always the same: **value semantics at the interface, in-place update
when the compiler or runtime can prove the value is uniquely referenced.**

| host | mechanism | maturity |
|---|---|---|
| **Rust** | ownership and `&mut`; `Rc::make_mut` *is* copy-on-write | native — the whole language is this technique |
| **OxCaml** | the **uniqueness** mode — "values with only a single reference pointing to them" | designed for exactly this |
| **Lean 4** | reference counting with destructive update when the count is 1 — [*Counting Immutable Beans*](https://arxiv.org/abs/1908.05647) (Ullrich & de Moura, IFL 2019), plus borrowed references to cut RC traffic | **built into the runtime** |
| **Haskell** | `ST` + freeze/thaw, or [`linear-base`](https://hackage.haskell.org/package/linear-base) — `Data.Array.Mutable.Linear` gives a *pure* API over in-place mutation, gated by `%1->` | works; an extra library and a discipline |
| **Python** | refcount CoW — mutate in place when `sys.getrefcount()` says you are the only holder | real (CPython does it for `str +=`) but fragile and unspecified |
| **Clojure / DataScript** | **transients** — an O(1) mutable view of a persistent collection, `persistent!` to seal, benchmarked 2–3× faster for bulk building | battle-tested, and in the very system recommended as reading item 0 |

Three things follow:

1. **Transients are the shape to copy**, whatever the host. Not "a mutable
   relation type" but *a mutable builder for one*, entered and left in O(1),
   with the immutable value as the only thing that escapes. It keeps the
   equational story intact — the laws hold of the values, and the builder is
   never observable.
2. **This re-ranks the hosts a third time.** Rust, OxCaml and **Lean 4** all
   get this for free or nearly so; Lean in particular is better placed than the
   earlier table credited, since its runtime was built for precisely this and
   the proof leg was already its argument. Haskell needs `linear-base` or `ST`.
   Python's version is the weakest and least specified.
3. **Note the OxCaml distinction.** Modes-for-uniqueness is squarely what modes
   were designed for and is a *solid* argument. Modes-for-relational-contraction
   (spike 1) is speculative and expected to fail. Two very different claims that
   should not be allowed to borrow credibility from each other.

**The real cost is not the insert, it is the indexes.** Inserting one tuple into
a relation carrying three cached indexes means touching three structures.
Transients help with the bulk-build case and not at all with the
one-insert-at-a-time case, so the interesting question is whether index
maintenance can be made lazy too — rebuild on next use rather than on insert.
That is a design question worth settling early, and it is the point where the
demoted IVM literature might come back after all.

**And there is prior art of exactly this shape.**
[**DataScript**](https://github.com/tonsky/datascript) is an *immutable
in-memory database and Datalog query engine* built on persistent data
structures, whose own description is that it is "more like data structures than
databases (think Hashmap)" — cheap to create, ephemeral, meant as a building
block for applications tracking a lot of state. Its stated payoff is precisely
the immutability one: track state evolution, rewind to any point, always render
a consistent state. That is this project with different technology choices —
untyped Clojure, Datalog-shaped rather than binary-relation-shaped. **Read it
before building anything**; it is the closest existing artefact and it has been
in production use for years. Datomic is the same idea at database scale.

## Higher-order operations: fmap, filter, msum — do they type?

Asked 2026-08-01. **Short answer: yes, and more cleanly than in the
named-column world — with one recurring wart and one hard limit.** Everything
below stays within a two-parameter type constructor, so it types in every host
in the table, Python included.

**`Rel` is a profunctor, and that covers fmap.** Post-composing with the graph
of a function is `rmap`; pre-composing is `lmap`:

```haskell
rmap :: (b -> c) -> Rel a b -> Rel a c      -- rmap f r = fun f . r
lmap :: (a' -> a) -> Rel a b -> Rel a' b    -- lmap g r = r . fun g
```

Projection is just `rmap fst`. Add `Strong` (via `⊗`) and `Choice` (via `⊕`)
and the Haskell `profunctors` vocabulary names most of what is needed — reuse
the names. Nothing here needs a kind beyond `* -> * -> *`, so in Python it is
`def rmap[C](self, f: Callable[[B], C]) -> "Rel[A, C]"`, which checks fine.

**`filter` needs no combinator at all.** A filter is a **coreflexive** — a
sub-relation of the identity — and filtering is composition with it:
`r . Φ_p` restricts the source, `Φ_q . r` the target. This is literally the
"simplicity and coreflexivity" machinery from the Oliveira paper that started
the thread, and it is a small elegance win: the binary framing gets restriction
for free from composition rather than as a primitive.

**On predicate opacity — corrected by Matthias, 2026-08-01.** I framed this as
the sharpest tension in the design. It is much less than that, because the
tagless-final answer is the obvious one and I skipped it: the predicate is not
`a -> Bool` but **`v a -> v Bool`** for a suitably restricted `v`. HOAS in the
usual final style — encode binders as host functions over *object-language*
terms rather than over host values. Then the symbolic interpreter recovers the
structure the standard way, by instantiating `v` at the AST type and applying
the function to a fresh variable, and the planner sees everything: pushdown and
index selection both work. This is exactly what Opaleye and Rel8 do with
`Expr a` — "SQL expressions of type `a`" — and what LINQ does with expression
trees.

**And "appropriately restricted" is carrying real weight.** `v` should be a
*separate, smaller* language than `Rel`: scalars, comparisons, arithmetic — not
the relational class. If `v` could embed relations you would need relations as
values inside relations, i.e. the internal hom that Rel does not have. So the
architecture is **two stratified object languages** bridged by coreflexives:

```haskell
where_ :: (v a -> v Bool) -> Rel a a      -- coreflexive from a scalar predicate
```

The stratification is not a restriction imposed for tidiness — it is what keeps
the relational layer first-order and therefore keeps the no-internal-hom limit
from ever being hit. Worth stating as a design rule.

**What actually remains of the cost**, which is real but small:

1. **Host *syntax*, not host *functions*.** You write predicates with host
   lambdas and host operators, but out of `v`'s vocabulary — so an existing
   `myBusinessRule :: Customer -> Bool` does not just drop in. Predicates must
   be re-expressed. That is the residue of the "seamless" requirement, and it
   is the honest cost.
2. **An escape hatch is needed, and should be visible.** Provide
   `opaque :: (a -> Bool) -> v a -> v Bool` so arbitrary host functions *can*
   be used, with the planner treating them as black boxes. Then opacity is paid
   for only where it is used, and shows up in the plan rather than silently.
3. **The object language grows.** `v` needs arithmetic, comparison, string
   operations. This is how LINQ and Opaleye end up with large surface areas.
   Known cost, not a blocker, but it is where the bulk of the tedious work is.

**`msum` — right idea, wrong class.** Union with `∅` is a monoid, so
`Alternative`/`ArrowPlus` type fine. But union is *idempotent and commutative*
and, with `∩`, forms a lattice — and `Monoid` **under-specifies precisely the
laws the optimiser will rely on**. Define `JoinSemilattice`/`Lattice` classes
instead of reusing `Monoid`. Also note `Rel a` is not usefully a monad in `b`:
the monad is `Set`, and `Rel a b ≅ a -> Set b` is its Kleisli arrow, so the
`msum` you want is a semilattice fold, not `MonadPlus`.

**Group-by and nesting: power transpose.** `Λ` turns `Rel a b` into a function
`a -> Set b` — set-valued functions being exactly the power-transposes of
binary relations — which is what makes `groupBy :: Rel a b -> Rel a (Set b)`
type. This needs one more rung, a **power allegory**. The reference is Oliveira
& Rodrigues, *[Transposing Relations: from Maybe Functions to Hash
Tables](https://www.di.uminho.pt/~jno/ps/mpc04.pdf)* (MPC 2004) — and note the
subtitle: it is already the bridge from relations to concrete data-structure
representation, which is the access-path-independence agenda under another
name. Nested relations themselves are fine and well studied (nested relational
calculus).

**The hard limit: no internal hom.** Rel is not cartesian closed, so you cannot
curry a relation — there is no relation whose *values* are relations you can
then compose with. Nesting (`Rel a (Set b)`) is fine; function space is not.
Practically this means higher-order combinators live in the **host**, building
relations, while the object language stays first-order. That is what an EDSL is
anyway, and it is worth reading as a feature: a first-order object language is
what keeps optimisation tractable.

**The wart: `Ord`, and it cuts against Haskell specifically.** `Data.Set`
cannot be a `Functor` or `Monad` in Haskell because its operations carry `Ord`
constraints — the **constrained-monad problem** (Sculthorpe, Bracker, Giorgidze
& Gill, [ICFP 2013](https://ku-fpg.github.io/files/Sculthorpe-13-ConstrainedMonad.pdf)).
For us it lands exactly on the class signature: the *evaluator* interpretation
needs `Ord b` for `rmap`, the *symbolic* interpretation does not. Put `Ord` in
the class and every interpreter pays; leave it out and the evaluator cannot be
written. Options are the ICFP'13 normal-form restructuring, `ConstraintKinds`-
indexed classes, or a trie/list representation.

Per host, and **this is a second independent argument for OCaml**:

| host | how the `Ord` wart lands |
|---|---|
| **OCaml** | functorised modules pass the comparison explicitly — the problem does not arise |
| **Rust** | an `Ord` bound on the impl; routine |
| **Python** | no static constraint, so it is a runtime concern only |
| **Lean** | carries `Ord`/`DecidableEq` instances, no purity pressure |
| **Haskell** | **the one host where this is genuinely annoying** |

Net effect on the earlier ranking: Haskell and OCaml are closer than that table
implied. Haskell keeps the Kahl precedent; OCaml now has two independent
arguments (legible errors from signature checking, and no constrained-monad
problem).

## Where this probably goes wrong

Written down now, while it is still cheap to abandon.

1. **FO³.** Repeating it because it is the one that kills naive versions: the
   bare calculus of binary relations cannot express everything Codd's algebra
   can. Any design must say explicitly where its pairing comes from. Oliveira's
   answer — products and projections in an allegory — is the one to copy, and
   the plumbing it costs is the thing to measure early.
2. ~~**The fix is two-dimensional**~~ — **downgraded.** Diagrams are the
   human-facing syntax for a structure that is combinatorially a hypergraph, so
   a backend can hold the hypergraph and never render it. What survives is
   sharper and narrower: rewriting must be **modulo** the monoidal laws (convex
   DPO on hypergraphs), not term rewriting on a syntax tree.
3. ~~**Point-free unreadability**~~ — **withdrawn**, given that point-free is
   the core and not the surface. It was the strongest objection to the
   single-layer reading and it does not apply. What is left of it: Ampersand is
   still worth a look, but now as evidence about *surface* design, since it is
   the one system that made users write relation algebra directly.
4. **Small field.** 23 submissions to RAMiCS 2026. Expect thin tooling, few
   collaborators, and papers that assume a lot of category theory.
4b. **Type errors, not type checking, are the EDSL risk.** The types will be
   sound and the checker will do its job; what degrades is diagnosis, because
   the design erases the names errors would otherwise cite. This is the one
   caution that lands squarely on the stated requirement, so it deserves a
   deliberate answer rather than a hope.
5. **Two of the four traditions hit metatheoretic walls** (relational lattices:
   undecidable; binary data model: superseded). Prior probability on "this is
   easy and everyone missed it" should be low.

Per the working pattern from the tapecheck sessions: before building any of it,
read Pous's library and Kahl's Haskell interface. Four for four last time.

---

## Timeboxed spikes — open items

Small, bounded, each with a stated budget and a stated way to fail. Kept here
rather than in a project repo because there is no project repo yet.

**Host decided 2026-08-01: OCaml/OxCaml first.** Spikes 2, 3 and 5 are therefore
**parked**, not cancelled — they become live again only if the host changes.
Live now: 1, 4, 6, and 7–8 below.

| # | spike | budget | done when |
|---|---|---|---|
| 7 | **`Incremental` as a second interpreter.** Take one trivial derived relation (a join of two base relations) and build it twice: once as a one-shot evaluator, once as an `Incremental` graph that updates when a base relation changes. This is the demo the whole pitch rests on; find out early if it is awkward. | 1 day | both interpreters run the same program, and the incremental one demonstrably recomputes less |
| 8 | **Lazy automatic index selection.** On an immutable relation, build an index on first use keyed by access pattern and memoise it on the value. DataScript makes this a human `:db/index` decision; immutability should make the automatic version sound. | half a day | a query that would table-scan instead hits a lazily built index, with no declaration |
| 1 | **OxCaml modes for relational contraction.** Can the linear modality express "this variable is used twice, insert a copy"? Prior expectation: **no** — modes are for memory safety and at-most-once invocation, not a DSL resource discipline. | **30 min** | disproved, or a one-paragraph sketch of how it would work |
| 2 | **Python checker agreement.** Type-check the same ~20-line `Rel[A, B]` skeleton — composition via method-level `[C]`, converse, meet — under mypy, pyright, pyrefly and ty. | 1–2 h | four verdicts recorded; disagreement on variance and method-level type params is the thing being looked for |
| 3 | **Both Python surfaces, prototyped.** (a) operator/method-chaining, Ibis-style; (b) generator-expression capture, Pony-style bytecode decompilation. Compare on the same three queries. | half a day | one is clearly better, or the cost of supporting both is known |
| 4 | **How big does `v` have to be?** (Reframed — the `v a -> v Bool` answer settles the opacity question; what is left is scope.) Take a dozen realistic business predicates and see how many need only comparisons and arithmetic, how many need the `opaque` escape hatch, and what that implies for `v`'s surface area. | half a day | `v`'s minimum vocabulary is written down, with the escape-hatch rate measured |
| 5 | **`Ord`/constrained-monad, in Haskell only.** Write `rmap` for the evaluator and the symbolic interpreter under one class and see how bad it actually is. | 2 h | either a working encoding or a concrete reason OCaml wins |
| 6 | **Semi-naive evaluation.** Implement it for transitive closure over an in-memory relation. It is a page of code and it is the cheap ancestor of DBSP. | half a day | org-chart reachability works and is incremental |

## Parked — suggestions kept for later

Recorded 2026-08-01 at Matthias's request; none of these are dead, they are
just not next.

- **Other hosts, with the case for each preserved.** *Lean 4* — three arguments
  (laws become theorems; the runtime does immutable-with-in-place natively via
  *Counting Immutable Beans*; macros give real surface syntax); the natural home
  if this ever becomes primarily a theory-and-proofs artefact. *Haskell* — the
  safe middle with Kahl's MPC 2006 precedent, held back by the `Ord`/
  constrained-monad wart landing on the class signature. *Python* — a good
  demonstration and teaching host, viable precisely because `Rel[A, B]` is a
  two-parameter generic, blocked from the full design by the absence of
  higher-kinded types (must go initial, not final).
- **The skeleton, whenever the project repo exists.** Class hierarchy cut on
  Pous's joints; two interpreters (symbolic AST + naive evaluator over finite
  sets) and later a third (`Incremental`); the stratified scalar language `v`
  with `where_ :: (v a -> v Bool) -> Rel a a`; semi-naive transitive closure as
  the first real capability, since it is what plain Codd cannot do and it is
  the confirmed business-logic case; property tests generated from the laws.
- **Scaffolding that repo** — offered, not yet taken up.
- **Query planning as a differentiator.** DataScript folds joins in clause
  order. Worst-case-optimal joins and a cost model are a real gap, but they are
  a second-phase concern, after the algebra and the interpreters exist.
- **Prototype both Python surfaces** (operator-chaining vs generator-expression
  capture) — explicitly deferred by Matthias to "later", and now doubly parked
  by the host decision.

## Next reading, in order

Resolved, so this is a reading list rather than a question. Reordered for the
two-layer design: 0 is new and now comes first.

0. **[DataScript](https://github.com/tonsky/datascript)** — an immutable
   in-memory relational store on persistent data structures, in production for
   years. Same premises, different technology. Cheapest possible calibration of
   what this project is and is not.
0b. **[chyp](https://github.com/akissinger/chyp)** — a working prover for free
   SMCs that already carries *both* a term syntax and a diagram syntax over one
   hypergraph core. Whatever gets built, this is the closest existing shape;
   read it before designing the core representation.
1. **`pdbc.pdf`, the chapters on relations and on products/coreflexives** —
   the mature form of the 2005 paper, and the place the plumbing question gets
   answered one way or the other. Start here, not with the 2005 report.
2. **Kahl, *Semigroupoid Interfaces for Relation-Algebraic Programming in
   Haskell* (MPC 2006)** — someone already built this library in a language
   without dependent types and wrote down what had to bend. Cheapest possible
   look at the failure modes.
3. **Macedo & Oliveira, *Typing Linear Algebra* (SCP 2013)** — read only if the
   semiring generalisation is wanted. It is a strictly larger project.
4. **Pous's `relation-algebra`** — for the structure lattice (which axioms
   buy which operations) even if the host language ends up not being Rocq.

## Sources

- [Graphical Conjunctive Queries (CSL 2018)](https://drops.dagstuhl.de/opus/volltexte/2018/9680)
- [Diagrammatic Algebra of First Order Logic (LICS 2024)](https://dl.acm.org/doi/10.1145/3661814.3662078) · [UCL copy](https://discovery.ucl.ac.uk/10198353/1/LICS24-40.pdf)
- [The calculus of neo-Peircean relations (arXiv 2505.05306)](https://arxiv.org/abs/2505.05306)
- [Preservation theorems for Tarski's relation algebra (arXiv 2305.04656)](https://arxiv.org/pdf/2305.04656) — FO³, and TRA fragments in RPQ/XPath/SPARQL
- **[HaskellWiki, Relational algebra](https://wiki.haskell.org/Relational_algebra)** — where the trail started
- **[Oliveira, First Steps in Pointfree Functional Dependency Theory](https://www.researchgate.net/publication/238475005_First_Steps_in_Pointfree_Functional_Dependency_Theory)** = *Functional dependency theory made 'simpler'*, TR DI-PURe-05.01.01, Univ. Minho, 2005 — **the paper**. Draft copies live at `~jno/ps/_.pdf` and [`~jno/tmp/_.pdf`](https://www.di.uminho.pt/~jno/tmp/_.pdf); neither filename is stable.
- [Oliveira, Program Design by Calculation](https://www.di.uminho.pt/~jno/ps/pdbc.pdf) — draft, Feb 2026
- [Oliveira, Transforming Data by Calculation (GTTSE)](https://link.springer.com/chapter/10.1007/978-3-540-88643-3_4) · [Extended Static Checking by Calculation Using the Pointfree Transform](https://link.springer.com/chapter/10.1007/978-3-642-03153-3_5)
- [Macedo & Oliveira, Typing Linear Algebra: A Biproduct-Oriented Approach (arXiv 1312.4818)](https://arxiv.org/pdf/1312.4818) · [A Linear Algebra Approach to OLAP (FAC 2015)](https://link.springer.com/article/10.1007/s00165-014-0316-9) · [Preparing Relational Algebra for "Just Good Enough" Hardware (RAMiCS 2014)](https://link.springer.com/chapter/10.1007/978-3-319-06251-8_8)
- [Mota, Paixão & Martelotte, Point-free calculational proofs and program derivation in linear algebra using a graphical syntax (JFP 2025)](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/pointfree-calculational-proofs-and-program-derivation-in-linear-algebra-using-a-graphical-syntax/44175D6BFE57C9906F2D50B4D51F915E)
- [Bird & de Moor, Algebra of Programming](https://dl.acm.org/doi/book/10.5555/248932)
- [Pous, relation-algebra for Coq/Rocq](https://github.com/damien-pous/relation-algebra) · [project page](https://perso.ens-lyon.fr/damien.pous/ra/) · [Rocq paper](https://hal.science/hal-05007316v1)
- [Kahl, Dependently-Typed Formalisation of Relation-Algebraic Abstractions (RATH-Agda)](https://link.springer.com/chapter/10.1007/978-3-642-21070-9_18)
- [Kahl, Semigroupoid Interfaces for Relation-Algebraic Programming in Haskell (MPC 2006)](https://link.springer.com/chapter/10.1007/11828563_16)
- [Litak, Mikulás & Hidders, Relational lattices: from databases to universal algebra](https://www.sciencedirect.com/science/article/pii/S2352220815001455) · [undecidability, arXiv 1607.02988](https://arxiv.org/abs/1607.02988) · [Santocanale, Relational Lattices via Duality](https://inria.hal.science/hal-01446027/document)
- [Tropashko, Relational Algebra as non-Distributive Lattice (arXiv cs/0501053)](https://arxiv.org/pdf/cs/0501053) · [Relational Lattice Foundation for Algebraic Logic (arXiv 0902.3532)](https://arxiv.org/pdf/0902.3532)
- [RAMiCS 2026](https://ramics-conf.github.io/2026/) · [proceedings](https://link.springer.com/book/10.1007/978-3-032-22469-9)
- [Datafun: a functional Datalog](https://www.cl.cam.ac.uk/~nk480/datafun.pdf)
- [Flix: A Design for Language-Integrated Datalog (OOPSLA 2025)](https://dl.acm.org/doi/10.1145/3763126) · [PDF](https://plg.uwaterloo.ca/~olhotak/pubs/oopsla25b.pdf)
- [Rel: A Programming Language for Relational Data (SIGMOD 2025 companion)](https://dl.acm.org/doi/10.1145/3722212.3724450) · [arXiv 2504.10323](https://arxiv.org/abs/2504.10323)
- [Joosten, Relation Algebra as programming language using the Ampersand compiler (JLAMP 2018)](https://www.sciencedirect.com/science/article/pii/S2352220817301499) · [Hackage](https://hackage.haskell.org/package/ampersand)
- [Kepner et al., Associative Arrays (arXiv 1501.05709)](https://arxiv.org/pdf/1501.05709) · [Associative Array Model of SQL, NoSQL, NewSQL (arXiv 1606.05797)](https://arxiv.org/pdf/1606.05797)
- **[Gibbons, Henglein, Hinze & Wu, Relational Algebra by Way of Adjunctions (ICFP 2018)](https://www.cs.ox.ac.uk/jeremy.gibbons/publications/reladj.pdf)** — filed as "adjacent" while point-free was assumed; **promoted** once points are kept, since it is the pointful comprehension-based Haskell-typed account
- [Trinder & Wadler → Buneman et al., Monad Comprehensions: A Versatile Representation for Queries](https://link.springer.com/chapter/10.1007/978-3-662-05372-0_12) · [Gibbons, Comprehending Ringads](https://www.cs.ox.ac.uk/jeremy.gibbons/publications/ringads.pdf) · [Effective Quotation: relating approaches to language-integrated query](https://arxiv.org/pdf/1310.4780)
- [Chandra–Merlin containment as hypergraph homomorphism (lecture notes)](https://pages.cs.wisc.edu/~paris/cs838-s16/lecture-notes/lecture2.pdf) · [Conjunctive query containment revisited](http://chekuri.cs.illinois.edu/papers/conjunctive_tcs.pdf) — the pointful presentation of the same object as the diagrams
- [Practical Alloy — relational logic primer](https://practicalalloy.github.io/chapters/structural-topics/topics/relational-logic/index.html)

miniKanren, and the in-memory framing:

- [Codd, A Relational Model of Data for Large Shared Data Banks (1970)](https://www.engineering.upenn.edu/~zives/03f/cis550/codd.pdf) — the three dependencies: ordering, indexing, access path
- [cKanren: miniKanren with Constraints](https://www.schemeworkshop.org/2011/papers/Alvis2011.pdf) · [A Complexity Study for Interleaving Search](https://minikanren.org/workshop/2021/minikanren-2021-final7.pdf) · [An Empirical Study of Partial Deduction for miniKanren](https://minikanren.org/workshop/2020/minikanren-2020-paper2.pdf) — goal-ordering and termination, from the community itself
- [DBSP: Automatic Incremental View Maintenance for Rich Query Languages (VLDB 2023)](https://www.vldb.org/pvldb/vol16/p1601-budiu.pdf) · [SIGMOD Record version](https://dl.acm.org/doi/10.1145/3665252.3665271) · [Recent Increments in Incremental View Maintenance (arXiv 2404.17679)](https://arxiv.org/pdf/2404.17679)

EDSL construction:

- [Kiselyov, Tagless-Final Style — index](https://okmij.org/ftp/tagless-final/index.html) · [Typed Tagless Final Interpreters (lecture notes)](https://okmij.org/ftp/tagless-final/course/lecture.pdf) · [Carette, Kiselyov & Shan, Finally Tagless, Partially Evaluated (JFP 19(5), 2009)](https://okmij.org/ftp/tagless-final/JFP.pdf)
- [Elliott, Compiling to Categories (ICFP 2017)](http://conal.net/papers/compiling-to-categories/compiling-to-categories.pdf) · [`concat`](https://github.com/compiling-to-categories/concat) · [`categorifier`](https://github.com/con-kitty/categorifier) — needs a CCC, which Rel is not
- [Axioms for the category of sets and relations (TAC 44:10)](http://www.tac.mta.ca/tac/volumes/44/10/44-10.pdf) — for the not-cartesian facts
- [Rel8](https://rel8.readthedocs.io/) · [Opaleye](https://hackage.haskell.org/package/opaleye) — the named-column comparison point

Two-layer design (pointful surface, point-free core):

- [Paterson, A New Notation for Arrows (ICFP 2001)](https://www.staff.city.ac.uk/~ross/papers/notation.pdf) · [Lindley, Wadler & Yallop, The Arrow Calculus](https://homepages.inf.ed.ac.uk/wadler/papers/arrows/arrows.pdf)
- String Diagram Rewrite Theory [I (arXiv 2012.01847)](https://arxiv.org/pdf/2012.01847) · [II (arXiv 2104.14686)](https://arxiv.org/pdf/2104.14686) · [III (MSCS)](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/string-diagram-rewrite-theory-iii-confluence-with-and-without-frobenius/F6E1207A100A9F1CFB48FFBAEC785F61) — diagrams as typed hypergraphs, convex DPO rewriting
- [chyp — interactive prover for SMCs, term syntax + diagrams](https://github.com/akissinger/chyp) · [DisCoPy](https://docs.discopy.org/en/main/) ([arXiv 2005.02975](https://arxiv.org/pdf/2005.02975))
- [An Introduction to String Diagrams for Computer Scientists (arXiv 2305.08768)](https://arxiv.org/pdf/2305.08768)
