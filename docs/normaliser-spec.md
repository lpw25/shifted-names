# Specification of the normaliser

What `names` must do. Every design and every proof is checked against
this list. A theorem that does not imply the requirements below, as
stated, does not count.

## Inputs

- **Adjustment expressions.** `aexp` / `texp` of `Core/Normalise.v`
  (identity, adjustment atoms `σ`, composition, outer and inner pushes,
  lifts, variables, terms `u[p]` whose payload `p` is again an
  adjustment expression, look-ups and shifts), plus `share`.
- **Labels:**
  - the bound label `·`;
  - concrete labels (strings);
  - label atoms: Coq terms of type `label` that are not concrete.
- **Facts in context** about label atoms (`x < y`).
- **Term atoms and adjustment atoms:** opaque Coq terms.

## Meaning and equality

The normaliser is specified against a class of *models* that is wider
than the standard interpretations. A label denotes a sequence of
distinct variables. Labels not known to be distinct may share
variables, in any arrangement.

- **Model.** A model `M` chooses:
  - a set of *variables*;
  - for each label expression `h`, an infinite sequence of distinct
    variables, which is what `h₀, h₁, …` denote;
  - a strict partial order on label expressions;
  - a value for each term and adjustment atom, over the model's
    variables.
- **Restrictions on a model.**
  - Each fact `x < y` holds in the order, and concrete labels are
    ordered as strings.
  - The bound label is ordered against every named label.
  - Labels that are ordered have disjoint sequences.
  - Nothing else is assumed. Labels that are not ordered may share any
    variables, in any arrangement.
- **Operations.** An operation on label `h` reads `h₀, h₁, …` as `h`'s
  sequence. It acts on that sequence as the standard operation acts on
  the variables of `h`, and on every other variable as the standard
  operation acts on variables of other labels. For example:
  - `⟦ h := t | a ⟧` sends `h₀` to `t`, `hᵢ₊₁` to what `a` gives for
    `hᵢ`, and every other variable to what `a` gives for it;
  - `⟦ \ h ⟧` sends `hᵢ` to `hᵢ₊₁` and leaves every other variable
    alone.
- **Standard interpretations** are the models where each label has its
  own sequence and equal labels share one. Every standard
  interpretation consistent with the facts is a model.
- **Equality.** Two expressions are *equal* when they denote the same
  map from variables to results in **every** model.
- **Payloads** are adjustments of their term's variables, bound and
  named alike: a term with a payload means the term read in the
  environment the payload gives.

**What this gives up.** Equality in every model implies equality in
every standard interpretation. The converse fails for identities that
hold only by a case split on how labels relate. Examples:

- **Two labels.** `⟦ \ x ⟧ ⨾ ⟦ \ y ⟧ ⨾ ⟦ x := u; y := v ⟧` and
  `⟦ \ y ⟧ ⨾ ⟦ \ x ⟧ ⨾ ⟦ y := v; x := u ⟧` are both `⟦⟧` in every
  standard interpretation. They differ when `x = (A, B, …)` and
  `y = (B, A, …)`.
- **Transitivity.** With a fact `x < m`,
  `⟦ \ x ⟧ ⨾ ⟦ \ k ⟧ ⨾ ⟦ m := c; k := v; x := u ⟧` does not depend
  on `u` in any standard interpretation. It does when `k` alternates
  between `x`'s and `m`'s variables.

The normaliser need not identify such terms. `docs/labels.md` has the
details.

**What it keeps.**

- Every law about a single label holds, including the identity
  renaming `⟦ x as a | Γ \ x as a | Γ ⟧ = ⟦⟧`.
- Operations on ordered labels commute.
- Facts are transitive.

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
  For example, `⟦ \ x ⟧ ⨾ ⟦ y := v; x := u ⟧` means `⟦ y := v ⟧`
  when `x ≠ y`, and `⟦ x := u ⟧` when `x = y`. Per-label structures are
  therefore only valid for labels known to be distinct.
- Completeness must use models in which labels overlap. One
  injective interpretation does not determine equality.
- Two variables of labels that are not ordered may be equal in one
  model and different in another, whatever their indices.

## Status against this specification

`HNorm` (`docs/comprehension.md`, `docs/hnorm.md`) decides equality in
every comprehension model consistent with the facts
(`HRefine.hn_eq_order_correct`), and is sound for the library's own
adjustments (`HConcrete.hn_eq_t_sound`). It is not complete for them:
labels the facts leave unordered may still be distinct there, and
deciding that would take an exponential case analysis.
