# Labels that may coincide

Working notes towards a canonical form that meets
`docs/normaliser-spec.md` when label atoms may denote the same label.
Everything is written with the library's context forms. Earlier
versions of these notes used an ad hoc notation; it is gone.

## The two building blocks

The part of a normal form that acts on named variables is built from
two kinds of step. Here `σ` is the rest of the adjustment: the
identity, or something stuck at an adjustment atom.

- **Weakening first:** `⟦ \ x ⟧ ⨾ σ` sends `xᵢ` to what `σ` gives for
  `xᵢ₊₁`, and every other variable to what `σ` gives for it.
- **Substitution in front:** `⟦ x := u | σ ⟧` sends `x₀` to `u`, `xᵢ₊₁`
  to what `σ` gives for `xᵢ`, and every other variable to what `σ`
  gives for it. The term `u` is not passed through `σ`.

Several substitutions in front are written as one form, innermost
first: `⟦ x := u; y := v | σ ⟧ = ⟦ x := u | ⟦ y := v | σ ⟧ ⟧`.

For one label, every composite of these steps has the form
`⟦ x := u₁; …; x := uₖ | ⟦ \ x ⟧ ⨾ … ⨾ ⟦ \ x ⟧ ⨾ σ ⟧`: substitutions
in front, then weakenings. The only rule needed to reach that form is
`⟦ \ x ⟧ ⨾ ⟦ x := u | σ ⟧ = σ`.

## Two identities that hold only by a case split

Below, `x`, `y`, `k`, `m` are label atoms and `u`, `v`, `c` are term
atoms.

**Example 1.**

```
L = ⟦ \ x ⟧ ⨾ ⟦ \ y ⟧ ⨾ ⟦ x := u; y := v ⟧
R = ⟦ \ y ⟧ ⨾ ⟦ \ x ⟧ ⨾ ⟦ y := v; x := u ⟧
```

- **Standard interpretations.** Both are `⟦⟧`. If `x ≠ y`, each
  weakening is undone by its substitution. If `x = y`, the two
  weakenings are undone by the two substitutions.
- **The offset model.** In the model currently in the spec, `y` may
  start at `x₁` (`yᵢ = xᵢ₊₁`). Then `L` and `R` both send `x₀` to `v`
  and leave every other variable alone. In every placement of `x` and
  `y`, `L = R`, but for different reasons in each case: `y` below `x`,
  equal, or above.

**Example 2.** With a fact `x < m`, and `k` related to neither:

```
W(u) = ⟦ \ x ⟧ ⨾ ⟦ \ k ⟧ ⨾ ⟦ m := c; k := v; x := u ⟧
```

`W(u)` does not depend on `u`, in every standard interpretation and in
every offset model:

- **`k` shares `x`'s variables.** Then it cannot share `m`'s, so
  `⟦ \ k ⟧` is undone by `k := v`, and then `⟦ \ x ⟧` by `x := u`.
- **Otherwise.** `x`'s variables see only `⟦ \ x ⟧` undone by
  `x := u`.

The argument uses "`k` shares variables with `x` and with `m`, so `x`
and `m` share variables", which the fact rules out.

## A wider class of models: labels as sequences of variables

**Model.** A model chooses:

- a set of variables;
- for each label `h`, an infinite sequence of distinct variables, which
  is what `h₀, h₁, …` mean;
- a strict partial order on labels.

**Restrictions.**

- The facts hold in the order, and concrete labels are ordered as
  strings.
- Labels that are ordered have disjoint sequences.
- Nothing else is assumed. Labels that are not ordered may share any
  variables, in any arrangement.

**Operations.** Each operation reads `h₀, h₁, …` as `h`'s sequence and
leaves variables outside it alone.

- **Standard interpretations** give each label its own sequence, and
  equal labels the same one.
- **Offset models** are the case where `y`'s sequence is a tail of
  `x`'s.

**Laws kept.**

- Every law about a single label holds, because each label's
  operations act on its own sequence exactly as in a standard
  interpretation.
- Operations on ordered labels commute, because their sequences are
  disjoint.
- Facts are transitive, because the order is.

**Example 1 fails.** Take `x = (A, B, C₂, C₃, …)` and
`y = (B, A, C₂, C₃, …)`, so `x₀ = y₁ = A` and `x₁ = y₀ = B`.

- **`L` sends `A` to `u`.**
  - `⟦ \ x ⟧` takes `A = x₀` to `x₁ = B`.
  - `⟦ \ y ⟧` takes `B = y₀` to `y₁ = A`.
  - `x := u` takes `A = x₀` to `u`.
- **`R` sends `A` to `B`.**
  - `⟦ \ y ⟧` takes `A = y₁` to `y₂ = C₂`.
  - `⟦ \ x ⟧` takes `C₂` to `C₃`.
  - `y := v` passes `C₃ = y₃` on as `y₂ = C₂`.
  - `x := u` passes `C₂ = x₂` on as `x₁ = B`.

**Example 2 fails.** Let `k` alternate between `x`'s and `m`'s
variables: `k = (x₀, m₀, x₁, m₁, …)`. Then `W(u)` sends `x₀` to `u`:

- `⟦ \ x ⟧` takes `x₀` to `x₁`;
- `⟦ \ k ⟧` takes `x₁ = k₂` to `k₃ = m₁`;
- `m := c` passes `m₁` on as `m₀`;
- `k := v` passes `m₀ = k₁` on as `k₀ = x₀`;
- `x := u` sends `x₀` to `u`.

## Algebraic reading

For each label `x`, the steps `⟦ \ x ⟧ ⨾ –` and `⟦ x := u | – ⟧`
generate a monoid with the one relation
`⟦ \ x ⟧ ⨾ ⟦ x := u | σ ⟧ = σ`. Take their *graph product* over the
graph "ordered": the free product, plus commutation of steps on
ordered labels.

- **Conjecture.** With an adjustment atom at the end, two composites
  of steps are equal in every model of the wider class exactly when
  they are equal in the graph product. With the identity at the end,
  absorption is added: `⟦ x := u | ⟦ \ x ⟧ ⨾ τ ⟧ = τ` when `τ` sends
  `x₀` to `u` in every model.
- **Consequence.** Graph products have a normal form theorem: reduced
  sequences of syllables are unique up to swapping adjacent syllables
  on ordered labels (Green, *Graph products of groups*, 1990; Veloso
  da Costa, *Graph products of monoids*, Semigroup Forum 2001). Their
  lexicographic normal forms would be the canonical form.
- **What remains to prove.** Two different elements of the graph
  product must differ in some model. Models that overlap only one
  pair of labels at a time do not suffice: in example 2, every such
  model ignores `u`.
