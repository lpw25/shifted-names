# Labels that may coincide

Working notes towards a canonical form that meets
`docs/normaliser-spec.md` when label atoms may denote the same label.
Everything is written with the library's context forms. Earlier
versions of these notes used an ad hoc notation; it is gone.

## What adjustments are built from

Every adjustment expression (`aexp` / `texp` / `pexp` of
`Core/Normalise.v`) is a sequence of *steps* in front of the identity.
The bound label `·` is one more label, ordered against every named
one. There are three kinds of step:

- **An input entry in front:** `⟦ x := t | τ ⟧`, or `⟦ x as a | τ ⟧`
  for a variable. It sends `x₀` to the target `t`, `xᵢ₊₁` to what `τ`
  gives for `xᵢ`, and every other variable to what `τ` gives for it.
  `t` is in the output scope of the whole adjustment and is not passed
  through `τ`.
- **A weakening in front:** `⟦ \ x ⟧ ⨾ τ`. It sends `xᵢ` to what `τ`
  gives for `xᵢ₊₁`, and every other variable to what `τ` gives for it.
- **An adjustment atom in front:** `σ ⨾ τ`.

A **target** is one of:

- a variable `yⱼ`;
- a term atom with a payload, `u[ρ]`, where `ρ` is again a sequence of
  steps in front of the identity, possibly starting with a payload
  atom (`PComp a p` is `p` then `a`);
- a target sent through a weakening, `TShiftE`.

**Each constructor as steps:**

| Constructor | As steps |
|---|---|
| `⟦⟧` (`AId`) | no steps |
| `σ` (`AAtom`) | the atom step, then nothing |
| input entry (`AInner`) | the entry step in front |
| output entry (`AOuter`), `a ⨾ ⟦ \ x ⟧` | `a`'s steps, then a weakening at the end; `a`'s targets are sent through it |
| lift `⟦ x \| a ⟧` (`ALift`) | `⟦ x := x₀ \| a ⨾ ⟦ \ x ⟧ ⟧` |
| `a ⨾ b` (`ACompose`) | `a`'s steps, then `b`'s; `a`'s targets are sent through `b` |

An output weakening after an atom is a weakening in front of what
follows it. So no separate output-side step is needed.

**Where labels meet besides the order of steps.** Sending the target
`yⱼ` through `⟦ \ x ⟧`:

- gives `yⱼ₊₁` when `y` is `x`;
- leaves `yⱼ` alone when `x` and `y` are ordered;
- otherwise cannot be resolved. The target stays "`yⱼ` sent through
  what follows" (`TShiftE`, or `apply_var` in the output).

So a target can name a variable at an earlier point of the sequence.

**Rules every model satisfies.**

1. **Cancellation:** `⟦ \ x ⟧ ⨾ ⟦ x := t | τ ⟧ = τ`.
2. **Absorption:** `⟦ x := t | ⟦ \ x ⟧ ⨾ τ ⟧ = τ` when `τ` sends `x₀`
   to `t` in every model. The identity renaming
   `⟦ x as a | Γ \ x as a | Γ ⟧ = ⟦⟧` is an instance.
3. **Commutation:** entries and weakenings on ordered labels commute.
   An atom commutes with nothing.
4. **Targets:** two targets are interchangeable when they are equal in
   every model, which is the same question one level down.

The single-label laws all follow from these. For example,
`⟦ x | σ ⟧ ⨾ ⟦ x | τ ⟧ = ⟦ x | σ ⨾ τ ⟧` is cancellation of the middle
`⟦ \ x ⟧ ⨾ ⟦ x := x₀ | … ⟧`.

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

Ignore targets for a moment, treating each one as a distinct letter.
Then the steps form the *graph product*, over the graph "ordered", of:

- for each label `x`, the monoid of its entries and weakenings with
  the cancellation rule;
- for each adjustment atom, a free monoid.

The graph product is their free product, plus commutation of steps on
ordered labels.

- **Conjecture.** Two sequences of steps ending in an atom are equal
  in every interleaved model exactly when they are equal in this graph
  product, with targets compared by rule 4. With the identity at the
  end, absorption is added.
- **Consequence.** Graph products have a normal form theorem: reduced
  sequences of syllables are unique up to swapping adjacent syllables
  on ordered labels (Green, *Graph products of groups*, 1990; Veloso
  da Costa, *Graph products of monoids*, Semigroup Forum 2001). Their
  lexicographic normal forms would give the canonical form.
- **What the targets add.** A target that names a variable at an
  earlier point in the sequence ties two positions of the sequence
  together. Reordering steps must move such a target's reference point
  along with them. The normal form theorem has to be checked with this
  in place. Absorption depends on targets too.
- **What remains to prove.** Two different elements must differ in
  some model. Models that overlap only one pair of labels at a time do
  not suffice: in example 2, every such model ignores `u`.
