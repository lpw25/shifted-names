# Specification of the normaliser

What `names` must do. Every design and every proof is checked against
this list. A theorem that does not imply the requirements below, as
stated, does not count.

## Inputs

- **Adjustment expressions.** `aexp` / `texp` / `pexp` of
  `Core/Normalise.v` (identity, adjustment atoms `σ`, composition,
  outer and inner pushes, lifts, variables, terms `u[p]` with payloads,
  payload atoms, payload composition and shifts), plus `share`.
- **Labels:**
  - the bound label `·`;
  - concrete labels (strings);
  - label atoms: Coq terms of type `label` that are not concrete.
- **Facts in context** about label atoms (`x < y`).
- **Term atoms, adjustment atoms and payload atoms:** opaque Coq terms.

## Meaning and equality

The normaliser is specified against a class of *models* that is wider
than the standard interpretations. A label atom may start partway along
another label's variables.

- **Model.** A model `M` chooses:
  - a set of *streams*, with a strict order on them;
  - for each label expression `h`, a stream `str h` and an offset
    `off h : nat`;
  - a value for each term, adjustment and payload atom, over the
    model's positions (below).
- **Restrictions on a model.**
  - Concrete labels have offset 0. Distinct concrete labels have
    distinct streams, ordered as the labels are.
  - The bound label has offset 0 and a stream of its own.
  - Each fact `x < y` holds as `str x < str y`. In particular, labels
    ordered by a fact never share a stream.
  - Nothing else is assumed. Two label atoms may share a stream at any
    offsets, and a label atom may share a concrete label's stream.
- **Positions.** A *position* is a pair `(s, n)` of a stream and a
  number. The variable `(h, i)` denotes the position
  `(str h, off h + i)`.
- **Windows.** The *window* of `h` is the set of positions
  `(str h, n)` with `n ≥ off h`. The position `(str h, off h + i)` has
  *index* `i` in the window.
- **Operations.** An operation on label `h` acts on the window of `h`
  as the standard operation acts on the variables of `h`, by window
  index. It acts on every position outside the window as the standard
  operation acts on variables of other labels. In particular, the
  positions of `str h` below `off h` are treated like variables of
  another label. For example:
  - a push of `e` on `h` in front of `a` sends index 0 of the window to
    `e`, index `i+1` to what `a` gives at index `i`, and every position
    outside the window to what `a` gives there;
  - `↑h` sends index `i` of the window to index `i+1`, and leaves every
    position outside the window alone.
- **Standard interpretations** are the models where each label has its
  own stream, equal labels share one, and every offset is 0. Every
  standard interpretation consistent with the facts is a model.
- **Equality.** Two expressions are *equal* when they denote the same
  map from positions to results in **every** model.
- **Payloads without a payload atom** observe only named positions
  (`Unique.feq`).

**What this gives up.** Equality in every model implies equality in
every standard interpretation. The converse fails only for identities
that need every label at offset 0. For example, with

```
c_x = ⟦ x as a; x as a | Γ \ x as a | Γ ⟧
```

`c_x ⨾ c_y` and `c_y ⨾ c_x` are equal in every standard
interpretation, by a case split on whether `x = y`. They differ in the
model where `y` starts at `x₁`. The normaliser need not identify such
terms.

**What it keeps.** Every law about a single label holds, including
the identity renaming `⟦ x as a | Γ \ x as a | Γ ⟧ = ⟦⟧`. Operations
on labels ordered by a fact commute. Identities that come from equal
entries still hold and must be identified; for example
`P_y(u) D_x P_y(u) = D_x P_y(u) P_y(u)` in the notation of
`docs/labels.md`.

## Requirements

1. **Sound.** The output equals the input in every model. In
   particular, it equals the input under every standard interpretation
   consistent with the facts.
2. **Canonical.** Inputs equal in every model give syntactically
   identical output terms. There is no quotient. Equal means in every
   model, not in one.
3. **Independent of the interpretation.** The normaliser reads
   only the input term, the facts, and the order of atoms in the proof
   context. It never assumes anything about the values of atoms.
4. **Valid output syntax.** Every subterm of the output that stands for
   an adjustment is an adjustment. Constructs beyond the current syntax
   are allowed only if they denote adjustments. Examples:
   - `share` is allowed;
   - an entry "the variable `z` sent through an adjustment"
     (`apply_var`) is allowed;
   - per-label tails are not.
5. **Readable output.** Payloads are shown as nested substitutions.
   Repeated payloads and tails are written once with `share`.
6. **Idempotent.** Normalising an output gives it back unchanged.
7. **Ordering.** Wherever the output needs an order the meaning does
   not fix, it comes from the facts and the context order of atoms.
   This keeps it consistent within one run of `names`.
8. **Sharing and size.**
   - **Output size:** linear in the input size, for inputs whose
     `share`s are well behaved: every use of a `share`-bound
     adjustment has the same continuation after it, up to leading
     shifts.
   - **Other inputs:** no promise.
   - **Own output:** the output is itself well behaved.
   - **Share-free inputs:** they stay in the well-behaved fragment
     under every operation a user applies.
9. **No expansion.** The algorithm never unfolds sharing. A tree form
   may appear in the specification and proofs, never in the algorithm.
10. **Proved, not checked.** Canonicity and soundness are theorems.
    No runtime checks stand in for proofs.
11. **Time.** Time bounds are argued on paper. Sizes are mechanised.

## Theorem shapes

With `canon` a function of the expression, the facts and the context
order only:

- `canon_sound : forall M, model F M -> den M (output (canon e)) = den M e`
- `canon_complete : (forall M, model F M -> den M e1 = den M e2) -> canon e1 = canon e2`
- `std_model : forall I, consistent F I -> model F (std I)`, with
  `den (std I) e` agreeing with the real semantics `aeden` under `I`.

`std_model` turns `canon_sound` into soundness for the real semantics.
`den` may be reached through a free model only if the free model is
shown adequate for that quantification over models.

## Consequences to keep in mind

- Operations on labels that are not known to be distinct must keep
  their relative order, inputs dropped as well as entries pushed.
  For example, `↑x ; ⟦y := v | ⟦x := u⟧⟧` means `⟦y := v⟧` when
  `x ≠ y` and `⟦z := u⟧` when `x = y = z`. Per-label structures are
  therefore only valid for labels known to be distinct.
- Completeness must use models in which labels overlap. One
  injective interpretation does not determine equality.
- Two variables of labels that may share a stream can compare three
  ways (below, at, above), not two.

## Status against this specification

`Core/GForm.v`, `Core/GEval.v` and `Core/GCanon.v` prove canonicity
for a single interpretation with distinct labels (`NoDup labs`).

- **Requirement 2:** not met; equality there is under one
  interpretation only, not in every model.
- **Requirement 3:** not met; `canon` takes `lenv`.
- **What carries over:** the treatment of entries, payloads, factored
  shifts, the phantom filler and sharing. The per-label lists of a
  node do not.
