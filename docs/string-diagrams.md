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

## What this changes

- **The spec has a precise form.** Equal in every model of a
  conditional-equational theory, with the Boolean sort two-valued.
- **Completeness of the closure** (the "corner lemma" in
  `docs/zero-sets.md`) has a standard shape. The chase is complete for
  free models, so two things remain to prove:
  - restricting the chase to visited points loses nothing: the nodes
    the chase adds off the word, such as corners of commuting squares,
    never merge visited points;
  - a branch the chase leaves consistent still has a model when every
    remaining `Z` is set to `true` or `false`.
- **The implementation is an e-graph.** A union-find over the visited
  points, with conditional rewrites for the lift law and commutation,
  is congruence closure: `O(n log n)` per closure (Downey, Sethi and
  Tarjan).
- **Not changed: the cost.** Asking about every pair of tests is still
  `k²` closures.

[arXiv:2205.02425]: https://arxiv.org/abs/2205.02425
[arXiv:2111.03784]: https://arxiv.org/abs/2111.03784
[Ahn, Horne and Tiu, CONCUR 2017]: https://strathprints.strath.ac.uk/87704/1/Ahn-etal-CONCUR-2017-A-characterisation-of-open-bisimilarity-using-an-intuitionistic-modal-logic.pdf
[Fiore and Staton, I&C 2006]: https://www.cs.ox.ac.uk/publications/publication15273-abstract.html
