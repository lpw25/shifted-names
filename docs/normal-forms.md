# Normal forms of adjustments

Status: specification in progress. The normaliser (`Core/Normalise.v`)
does not yet meet all of it; `tests/fuzz` finds the cases where it does
not.

## Expressions

An adjustment expression is built from adjustment atoms `σ`, the
identity, composition, output entries (`push_outer h`), input entries
(`push_inner h t`) and lifts (`⇑ₕ`). Targets `t` are variables `h₍ᵢ₎` or
terms `u⟨ρ⟩`: a term atom `u` with a payload adjustment `ρ`, which is
applied only to `u`'s named variables. Labels are the bound label `·`,
concrete labels, and label atoms, ordered by the facts in context.

Two expressions are *equal* when they denote the same adjustment for
every interpretation of their atoms (consistent with the facts). The
normal form is meant to be a complete invariant: equal expressions have
the same normal form.

## Words

A normal form is a *word*

    S₀ ∘ ⇑ᴸ¹σ₁ ∘ S₁ ∘ … ∘ ⇑ᴸⁿσₙ ∘ Sₙ

of segments `Sᵢ` and atoms `σᵢ` under multisets of lifts `Lᵢ`. A segment
is a context form with the identity tail: per label, in label order, the
targets of its first inputs and its number of outputs, with no
transparent last entry. Write `Vᵢ` for the variables `⇑ᴸⁱ` passes
through: `h₍₀₎ … h₍ₖ₋₁₎` for each `h` lifted `k` times.

The conditions:

1. **Segments are canonical** (ordered, distinct labels, trimmed).
2. **Only `S₀` has terms.** `S₁ … Sₙ` are renamings. A term to the right
   of an atom moves into a payload on its left:
   `σ ∘ push_inner g u⟨ρ⟩ X = push_inner g u⟨σ ∘ ρ⟩ (σ ∘ X)`.
3. **The segment right of a lifted atom is in lift position.** Let
   `Pᵢ` be the inputs of `Sᵢ` that it sends into `Vᵢ`. Then
   - every variable of `Vᵢ` is reached by `Sᵢ` (an unreached one moves
     left as a shift: `⇑ₕσ ∘ shiftₕ = shiftₕ ∘ σ`);
   - `Lᵢ` lifts each label `g` exactly as many times as `Pᵢ` has inputs
     labelled `g`;
   - `Sᵢ` sends the `j`-th input of `Pᵢ` labelled `g` (in index order) to
     `g₍ⱼ₎`.

   So the renaming of the passed-through variables, any merging of them,
   and the choice of which labels are lifted all live in `Sᵢ₋₁`. In the
   common case `Sᵢ` takes each lifted variable from itself; then
   `⟦ x | σ ⟧ ∘ ⟦ · \ x ⟧` and `⟦ · \ x ⟧ ∘ ⟦ · | σ ⟧` have the same normal
   form, `⟦ · \ x ⟧ ∘ ⇑.σ`.
4. **Payloads are normal for what they mean.** A payload word is applied
   to named variables only, so its last segment's bound-label inputs do
   not matter: condition 3 for its last atom counts named inputs only
   (so a lift by `·` there becomes a shift), and the last segment has no
   bound-label entry. Payload words satisfy 1–4 themselves.

## Display

Lifts are shown grouped: a run `⇑ₕσ₁ ∘ ⇑ₕS ∘ ⇑ₕσ₂` is shown as
`⟦ h | σ₁ ∘ S ∘ σ₂ ⟧`, so `⟦ · | a ⟧ ∘ ⟦ · | b ⟧` is shown as
`⟦ · | a ∘ b ⟧`. Grouping is decided from the word, so it adds no
choices.

## Uniqueness

To be proved: two words satisfying 1–4 that denote the same adjustment
for every interpretation of their atoms are equal.
