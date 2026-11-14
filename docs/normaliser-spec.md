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

- **Interpretation.** An interpretation gives every atom a value: a
  label for each label atom, an adjustment for each adjustment atom, and
  so on. It must be *consistent with the facts*.
- **Equality.** Two expressions are *equal* when they denote the same
  adjustment under **every** interpretation.
- **No distinctness assumption.** Two different label atoms may be
  interpreted as the same label, and a label atom may be interpreted as
  any concrete label, unless a fact rules it out. Only these
  distinctions are always known:
  - distinct concrete labels are different;
  - the bound label differs from every named label;
  - labels ordered by a fact are different.
- **Payloads without a payload atom** observe only named variables
  (`Unique.feq`).

## Requirements

1. **Sound.** The output equals the input under every interpretation
   consistent with the facts.
2. **Canonical.** Equal inputs give syntactically identical output
   terms. There is no quotient. Equal means under every interpretation,
   not under one.
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

- `canon_sound : forall I, consistent F I -> den I (output (canon e)) = den I e`
- `canon_complete : (forall I, consistent F I -> den I e1 = den I e2) -> canon e1 = canon e2`

Here `den` is the real semantics (`aeden`). It may be reached through
a free model only if the free model is shown adequate for that
quantification over interpretations.

## Consequences to keep in mind

- Operations on labels that are not known to be distinct must keep
  their relative order, inputs dropped as well as entries pushed.
  For example, `↑x ; ⟦y := v | ⟦x := u⟧⟧` means `⟦y := v⟧` when
  `x ≠ y` and `⟦z := u⟧` when `x = y = z`. Per-label structures are
  therefore only valid for labels known to be distinct.
- Completeness must use interpretations that identify labels. One
  injective interpretation does not determine equality.

## Status against this specification

`Core/GForm.v`, `Core/GEval.v` and `Core/GCanon.v` prove canonicity
for a single interpretation with distinct labels (`NoDup labs`).

- **Requirement 2:** not met; equality there is under one
  interpretation only.
- **Requirement 3:** not met; `canon` takes `lenv`.
- **What carries over:** the treatment of entries, payloads, factored
  shifts, the phantom filler and sharing. The per-label lists of a
  node do not.
