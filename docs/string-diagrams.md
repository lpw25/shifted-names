# Adjustments as string diagrams, and where they stop fitting

## With a fixed pattern of label equalities

Fix which labels are equal and which are disjoint, as in a standard
interpretation. Then an adjustment `a : Γ → Δ` sends each variable of
`Γ` to a variable or term over `Δ`. That is a morphism of the free
cartesian category on the term and adjustment atoms, drawn from `Δ` up
to `Γ`:

- **Wires and boxes.** The wires are variables. Term and adjustment
  atoms are boxes.
- **Copy and discard.** `Δ`'s wires may be copied (used several times)
  and discarded (not used). These form the comonoid of a cartesian
  category, natural with respect to every box.
- **Labels.** Each label is an ordered bundle of wires, `h₀` the
  leftmost. Equal labels are the same bundle; disjoint labels are
  different bundles.

The steps are then:

| Step | Diagram |
|---|---|
| `⟦ \ h as _ ⟧` | a new leftmost wire in `h`'s bundle in `Δ`, discarded; the rest of the bundle passes through, one place to the right |
| an entry sending `h` to a term `u` | `Γ`'s leftmost `h` wire is produced by `u`'s box, fed from `Δ`; the rest passes one place to the left |
| `⟦ h as v; g as v \ g as v ⟧` | `Δ`'s `g` wire is copied to feed `Γ`'s `g` and `h` |
| `⟦ g \| a ⟧` | `a`, with `g`'s leftmost wire passing beside it |

The normaliser's rules are then standard laws:

| Normaliser rule | Law |
|---|---|
| cancellation: `⟦ \ h as _ ⟧` then an entry on `h` | the entry's box is attached to a discarded wire, so naturality of discard deletes it |
| eta: a dead entry | the same law at a distance: the wire the box produces reaches no input |
| absorption, the identity renaming | the wire goes straight through |
| entries with equal targets commute | the copy comonoid is commutative and associative |
| steps on ordered labels commute | interchange: they act on different bundles |
| `⟦ g \| ⟦ \ h ⟧ ⟧ = ⟦ \ h ⟧` for ordered `g, h` | functoriality of `⊗`: identity beside a map on another bundle |

**For a fixed pattern there are no "tests" and no order between them.**
A diagram is a graph, and normalising it is ordinary term-graph
normalisation. Dead entries are simply boxes disconnected from the
inputs, visible without any group reduction.

## The difficult example, pattern by pattern

The example with facts (`docs/separation.md`): fact `g < h`, `m`
related to neither. In each pattern the two words give the same diagram,
by a different law:

- **`m` disjoint from `g` and `h`:** `⟦ \ h as _ ⟧` passes `m`'s bundle
  untouched, by interchange. The earlier entry on `m` after
  `⟦ \ h as _ ⟧` then takes the same wire as the later one, which
  becomes disconnected and is deleted by discard.
- **`m` the same bundle as `g`:** the later entry on `m` takes a wire
  the entry on `g` already took. Disconnected again, so deleted.
- **`m` the same bundle as `h`:** then `m`'s bundle is disjoint from
  `g`'s, and the two entries act on different bundles, so interchange
  applies.

No single diagram rewrite covers all three. The same holds for the
14-step example: `z` and `b` the same bundle, or not.

## What does not fit

Our models leave open whether unordered labels share wires, and how. In
the zero-set models a variable may sit in several bundles at unrelated
places. So the wiring itself depends on the model. A string diagram
fixes the wiring, so it cannot express "for every way the bundles
overlap".

Everything difficult (tests, their order, rule 4) lives exactly there.
Each follows a single input through bundles whose relationship is
unknown.

An earlier version of this file proposed inverse monoids for this part,
and warned that rule 4 might be undecidable. Both are withdrawn. The
warning rested on one sentence of an abstract about arbitrary
presentations, and our question is about the finitely many points a
word visits.

## A better fit: models as graphs, and the chase

**A model is a graph.**

- **Nodes** are variables.
- **Edges:** each label `h` gives a function `sh_h` (`⟦ \ h as _ ⟧`),
  its left inverse `un_h`, and a Boolean `Z_h` ("index 0 of `h`").
- **Axioms:** those of `zmodel` and `zcons` in `theories/Core/ZModel.v`.

Every one of those axioms is a **conditional equation**: equations
implying an equation. For example:

| Axiom | Form |
|---|---|
| `un_h (sh_h y) = y` | equation |
| `Z_h (sh_h y) = false` | equation |
| `Z_h v = false ⇒ sh_h (un_h v) = v` | conditional |
| `sh_g (sh_h y) = sh_h (sh_g y)` for ordered `g, h` | equation |
| the lift law: `Z_g v = true ⇒ sh_h v = v` for ordered `g, h` | conditional |

Theories of conditional equations are Horn theories (in categorical
terms, cartesian or essentially algebraic). They have free models. In
databases and graph rewriting the free model is computed by the
**chase**: rules that add the nodes and edges an axiom asks for, and
merge the nodes an equation identifies. Two references:

- Meyers, Spivak and Wisnesky show the chase computes finite free
  models of cartesian theories ([arXiv:2205.02425]).
- Brown, Patterson, Hanks and Fairbanks do DPO rewriting directly on
  such graphs (C-sets) ([arXiv:2111.03784]).

The congruence closure in `docs/zero-sets.md` (firing, loops, moving
the fact, functions) is this chase, restricted to the points a word
visits. Rule by rule:

- **firing** is the lift law;
- **moving the fact** is the commutation equation plus congruence;
- **functions** are congruence and `un_h (sh_h y) = y`.

**A branch of a decision list** fixes which of its tests fire. Write it
as Boolean equations at the tests' points:

- `Z_g P = true` for a test that fires;
- `Z_g P = false` for one that does not.

The branch happens in some model only if the chase of its equations
never derives `true = false`.

### The same thing as graph rewriting: the point graph and folding

**The point graph.** Run a word on one generic input `y`.

- **Nodes** are the points it visits: `y` moved by each prefix of the
  word.
- **Edges:** each step adds an edge labelled by its label, from a point
  `P` to `sh_h P`.
- **Tests:** each test is a mark on a node, with its label, target and
  place in the order.

This graph does not depend on how labels overlap. A model and an input
give a graph homomorphism from it into the model's graph. The
homomorphism is non-injective exactly where the model makes two points
equal. So a fixed overlap pattern is a quotient of the point graph,
and the string diagram above, read along `y`'s wire, is that quotient.
In graph-rewriting terms this is a non-injective match (Habel, Müller
and Plump).

**The normaliser's rules are rewrites of the point graph:**

| Normaliser rule | Rewrite |
|---|---|
| cancellation | **fold**: two `h`-edges into the same node are merged, and so are their sources |
| steps on ordered labels commute | **square completion**: the point graph lives in the cube complex of positions |
| eta (dead entries) | an entry at `Q` whose `h`-edge into `Q` already exists folds into it. Its test is dead, since `Z_h (sh_h R) = false` |
| same-target swap | test marks with equal targets are not ordered against each other |
| rule 4 | **conditional loop**: a firing test on `g` at `P` puts a `k`-loop at `P` for each `k` ordered against `g`; then fold |
| a fixed overlap | a quotient of the point graph |

The first rule is **Stallings folding**: the graph rewriting that
merges two same-labelled edges at a vertex, and their other ends.

- It is confluent: the folded graph does not depend on the order of
  folds.
- Touikan folds any connected labelled graph with `V` vertices and `E`
  edges in `O(E + (V + E) log* V)` time, using union-find
  ([arXiv:0805.2348], Theorem 1.6).

Our folds are the "functions" rule of the closure in both directions:
two edges out of a node with the same label, or two edges into it.

**Eta in one pass.** Folding gives the one-pass eta pass that
`docs/performance.md` plans. Process the word left to right. An entry
is dead exactly when the `h`-edge into its node already exists, that
is, when its wall has already been crossed. With positions kept as
hash-consed normal forms, "already exists" is one dictionary lookup on
the wall key. No reductions are repeated.

**The whole normaliser is one rewriting system.** The rewrites are:

- fold;
- complete squares;
- add lift-law loops in a branch, then fold.

Then read the normal word off the folded graph. The separate passes of
the current design (reduce, eta, re-sort, repeat) are one confluent
system computed in one sweep. The remaining questions are about this
graph:

- the order of test marks: "behind" and "crossing" are positions of
  walls, which are hyperplanes of the cube complex;
- which pairs of marks rule 4 lets swap.

### The two difficult examples are three chase steps each

**The facts example** (`docs/separation.md`: fact `g < h`, `m`
unrelated). The tests `t` and `t'` may swap when the branch "`u` does
not fire, `t` and `t'` do" is impossible:

```
Z_m (sh_h v) = false      (u does not fire)
Z_g v = true              (t fires)
Z_m v = true              (t' fires)

lift law, g < h:  sh_h v = v
congruence:       Z_m (sh_h v) = Z_m v = true      contradicts u
```

**The 14-step example** (`docs/zero-sets.md`: `b` ordered against `m`).
`t` tests `g` at `y`, `t'` tests `m` at `sh_z y`, and the earlier `u`
tests `g` at `un_z (sh_b (sh_z y))`:

```
Z_m (sh_z y) = true                   (t' fires)
lift law, b against m:  sh_b (sh_z y) = sh_z y
congruence:             un_z (sh_b (sh_z y)) = un_z (sh_z y) = y
so u's point is y, and Z_g y = true (t fires)   contradicts u not firing
```

There is no case split on how labels overlap. The overlap is whatever
the chase has merged so far.

### Where example 2 falls

Example 2 (`docs/labels.md`) holds in standard interpretations because
"`k` shares a variable with `x`, so it shares none with `m`". As an
axiom:

```
sh_k v ≠ v ∧ sh_x v ≠ v ∧ sh_k w ≠ w ∧ sh_m w ≠ w  ⇒  false
```

The premises are disequations, so this is not a conditional equation.
It is a four-way disjunction, which the chase cannot apply. So the line
already drawn has a precise form:

- **Kept:** consequences of conditional equations. These are decided
  by the chase, with no case split.
- **Left out:** consequences that also need disjunctive axioms, such as
  "equal or disjoint" between labels. Example 2 needs one.

*Correction (see "Rule 4 needs a case split too" below):* this line is
right about the axioms but misplaces rule 4. The chase decides each
branch of a decision list with conditional equations only. Concluding
that two decision lists are equal also uses a case split on which tests
fire, and that is excluded middle on `Z`.

The same line appears in name-passing calculi:

- **Late bisimilarity** is the analogue of standard interpretations. It
  needs excluded middle on whether two names are equal.
- **Open bisimilarity** is the analogue of our choice. It drops excluded
  middle, and is characterised by an intuitionistic modal logic
  ([Ahn, Horne and Tiu, CONCUR 2017]):
  - Its Kripke worlds are processes with their history, ordered by
    substitution instance. A Kripke model over that order is a
    presheaf, the free cocompletion.
  - Their example, `τ.[x = y]τ + τ + τ.τ` against `τ + τ.τ`, is equal
    only by assuming `∀x, y. x = y ∨ x ≠ y`. That is the shape of
    example 2.
  - For presheaf models of name-passing in general, see
    [Fiore and Staton, I&C 2006].

### A tested candidate for a stronger equality, and why it fails

A search (scratch `opt2/`) looked for an extra equality that would make
rule 4 local. The best candidate, E1, says: for distinct labels `h` and
`m`, every index-0 variable of `m` is index 0 of `h` or fixed by
`⟦ \ h as _ ⟧`. As an axiom:

```
Z_m v = true  ⇒  Z_h v = true  ∨  sh_h v = v
```

That is a disjunction, so E1 is not a conditional equation, and the
search found the consequences that line predicts:

- **It works for the three examples.** The facts example, the 14-step
  example and `r1`/`r2` all become checks at a single point.
- **It adds a new case split.** Even without facts, a new identity
  holds only by a case split on whether the input is index 0 of `k`.
  This is the same kind as examples 1 and 2.
- **It is NP-hard with facts.** Deciding whether a test can fire
  encodes SAT. The search checked this for two variables, with both a
  satisfiable and an unsatisfiable formula, and found an explicit
  zero-set countermodel for the unsatisfiable case.
- **The safe half does nothing for rule 4.** That half, "a weakening
  never moves a variable into `Z_m` from outside", is a dead-entry rule.

So a stronger equality only helps by adding a disjunctive axiom, and
that brings case splits. Rule 4 stays as the chase.

## Rule 4 in the family of conditional folds

Notation: `W g` is `⟦ \ g as _ ⟧`, and `E g` is an entry on `g` (a
test).

**The family.** Every rule of the closure has the form "these marks
imply these folds". Three members matter:

| Rule | Premise | Conclusion | Status |
|---|---|---|---|
| wall transport | none | `Z_g` is unchanged along steps on labels ordered against `g` | already used: tests are per wall |
| dead entry (eta) | none | a node with an incoming `h`-edge has `Z_h = false` | already used |
| rule 4 | a firing test on `g` at `P` | loops at `P` for every label ordered against `g` | the costly one |

**What rule 4 concludes.** Rule 4 is a *conditional duplicate*. The
duplicate rule says that a later test on a wall an earlier entry
already crossed never fires. Rule 4 says the same thing in the branch
where some test `t` fires: after `t`'s loops are folded in, an earlier
test `u` sits on the same wall as a later test `t'`, so `t'` cannot be
the first to fire. Hence `t` and `t'` may swap.

**The cheap subset: one-sided instances.** In these, the folds from one
of the two tests already put `u` on the other test's wall. They need
one closure per test, not per pair:

- for each test `t`, fold `t`'s loops;
- read off which earlier tests now share a wall with later tests.

That is `k` closures of `O(n log* n)` each, which is quadratic in
total. Exhaustive check (scratch `opt1/rank2.py`), counting every pair
of tests that rule 4 forces:

| Labels | Facts | Steps | Instances | One-sided |
|---|---|---|---|---|
| `g, h, m` | `g < h` | up to 7 | 100 | all |
| `a, b, c, d` | `a < b, c < d` | up to 6 | 32 | all |
| `a, b, c` | `a < c` | up to 6 | 8 | all |

**Measure walls, not points.** On points rather than walls some of
these looked joint, for example "`W a`, then `W b`, then a test on
`m`" with `b` ordered against `m`. On walls they are one-sided, because
`b` is stripped from the end of the wall. No instance in these runs was
forced by a single test alone, which would make that test dead.

**Joint instances exist** in longer words. Take `a < g` and `b < m`:

```
W b ⨾ W a ⨾ E m (u) ⨾ W m ⨾ E a ⨾ E b ⨾ E g (t) ⨾ W g ⨾ E m (t') ⨾ W m
```

- `t` and `t'` test the start.
- `u` tests the point after `W b ⨾ W a`.
- If both fire, `b` fixes the start (by `t'`) and then `a` fixes it
  (by `t`), so `u` is at the start and fires.
- Either loop alone is not enough, since `a` is not stripped from
  `m`'s wall.

There is a 17-step version with `t` and `t'` at different points, using
a third label `c`:

```
W c ⨾ W b ⨾ E c ⨾ W a ⨾ W c ⨾ E m (u) ⨾ W m ⨾ E c ⨾ E a ⨾ W c ⨾ E b ⨾ E c
  ⨾ E g (t) ⨾ W g ⨾ W c ⨾ E m (t') ⨾ W m
```

In both, the walk to `u` uses one test's loop and then, in the middle
of the walk, the other's. A loop used only at the end is always
stripped by the wall.

**Which models have rule 4.** An earlier version of this section
claimed that every model of the normaliser's equations satisfies rule
4. That is false: the term model, adjustments modulo the normaliser's
own equations, satisfies every equation, and in it the two sides of a
rule-4 instance are different normal forms.

A later version said absorption and the lift law were "eta laws for
tests". That was an artefact of the zero-set encoding. There a target
naming `g`'s index `i` is read relative to the consumed variable:
`zread g i v` is the consumed variable's `i`-th successor if `v` is at
index 0 of `g`, and the designated one's otherwise. That makes
`⟦ g as v \ g as v ⟧` look like a test, and the proof of
`za_lift_ordered` a case split.

In interleaved models a target is a fixed variable (`iz_read`), and
the lift law `⟦ g | ⟦ \ h as _ ⟧ ⟧ = ⟦ \ h as _ ⟧` is just ordered
commutation. The items `g as v` and `h as _` commute, and a step on `h`
leaves `g`'s variables alone because ordered labels have disjoint
streams.

**What rule 4 actually uses.** In interleaved models, for an input `x`:

- `t` fires means `x` is `g₀`; `t'` fires means `x` is `m₀`;
- if both fire, `x` is on `g`'s stream, so `⟦ \ h as _ ⟧` fixes it
  (`h` is ordered against `g`). Then `u`, which asks whether
  `⟦ \ h as _ ⟧ x` is `m₀`, fires.

So `[u, t, t']` and `[u, t', t]` agree on every input. This uses only:

- **extensionality:** adjustments are functions on variables, equal
  when equal on each one;
- **disjointness of ordered labels:** the same fact ordered commutation
  rests on.

Every model in which adjustments act on variables has rule 4. Dropping
it means a non-extensional model, such as the term model.

**Why the normaliser does not find rule 4.** The equality holds input
by input: an input that passes `t` and `t'` also passes `u`, which comes
earlier. The normaliser rewrites words, and each rewrite is local: it
looks at adjacent steps, or steps that commute together. No rewrite
lets a later test (`t`) tell it something about an earlier one (`u`).
Whether rule 4 can be derived from the normaliser's equations used in
both directions is not known. The input-by-input argument does not
give such a derivation.

The same gap between rewriting and extensional equality is known for
sum types in the typed lambda-calculus. There, eta for sums is
non-local, and rewriting that only contracts is incomplete:

- Lindley (TLCA 2007) gives a non-local rewriting theory for it.
- Scherer (POPL 2017) decides it by *saturation*: case-split on each
  sum as early as it becomes available.

The analogue for us is to consider each test at the first point where
the walk could make it.

**Non-extensional models of sums, and the analogue for us.** Models of
sums without eta get it by giving the sum inhabitants that are neither
left nor right:

- **Normalisation by evaluation.** Abel and Sattler (arXiv:1902.06097)
  use presheaves over contexts with a *cover monad*. A variable of sum
  type is an unknown. When evaluation needs to know which side it is,
  it asks an oracle, and the value becomes a case tree whose nodes are
  those questions. With the free cover monad nothing more is
  identified: "it does not matter in which order the questions are
  asked (commuting case splits), and whether the same question is
  asked several times (redundant case splits)" are listed as
  refinements. Full eta needs sheaves: Altenkirch, Dybjer, Hofmann and
  Scott (LICS 2001) add a Grothendieck topology in which left and right
  cover the sum.
- **Domain models** add `⊥`. **Cubical models** give higher inductive
  types formal composition constructors. Both are extra inhabitants of
  the same kind.

The pattern is a presheaf-style model with case trees, quotiented by
exactly the case-tree equations wanted. Eta is the sheaf condition,
which says you may split before you are asked.

**For us:**

- **The input** is an unknown variable.
- **Each entry with a term target** asks the oracle "is the current
  position at index 0 of `g`?". "Yes" ends the branch with the target.
  "No" continues, and the answer is recorded at the new stage.
- **Recorded answers propagate forward** along the walk. For example,
  after "`P` is index 0 of `g`", steps on `h` fix `P`.
- **A meaning is a case tree.** Two words are equal when their trees
  are equal modulo the equations we choose: redundant questions dropped
  (dead and duplicate tests), questions with the same answer commuting
  (the same-target swap), and ordered commutation.
- **No question is answered before it is asked.** So rule 4, which uses
  `t`'s answer at `u`, earlier in the word, does not hold.

**Open:** deciding joint instances below cubic cost. A candidate is
congruence closure that records, for each merge, the tests it depends
on, keeping only sets of at most two (proof-producing congruence
closure). Done naively that is still `k²` labels per merge.

## What this changes

- **Rule 4 is part of any extensional spec.** It follows from
  extensionality and disjointness of ordered labels. Only a
  non-extensional spec, such as the term model, avoids it.
- **Completeness of the closure** (the "corner lemma" in
  `docs/zero-sets.md`) has a standard shape. The chase is complete for
  free models, so two things remain to prove:
  - restricting the chase to visited points loses nothing: the nodes
    the chase adds off the word, such as corners of commuting squares,
    never merge visited points;
  - a branch the chase leaves consistent still has a model when every
    remaining `Z` is set to `true` or `false`.
- **The implementation is folding.** Union-find over the visited
  points, with square completion and lift-law loops. Each closure costs
  `O(n log* n)` (Touikan).
- **The cost, partly.** One-sided rule-4 instances need one closure per
  test, which is quadratic in total. Joint instances still need one per
  pair.

[arXiv:2205.02425]: https://arxiv.org/abs/2205.02425
[arXiv:2111.03784]: https://arxiv.org/abs/2111.03784
[arXiv:0805.2348]: https://arxiv.org/abs/0805.2348
[Ahn, Horne and Tiu, CONCUR 2017]: https://strathprints.strath.ac.uk/87704/1/Ahn-etal-CONCUR-2017-A-characterisation-of-open-bisimilarity-using-an-intuitionistic-modal-logic.pdf
[Fiore and Staton, I&C 2006]: https://www.cs.ox.ac.uk/publications/publication15273-abstract.html
