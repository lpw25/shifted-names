# Normal forms of adjustments

Composition is written `⨾`, in diagrammatic order: `a ⨾ b` is `a`, then
`b`, so `t [a] [b] = t [a ⨾ b]`.

## Expressions

An adjustment expression is built from adjustment atoms `σ`, the
identity, composition, output entries (`push_outer h`), input entries
(`push_inner h t`) and lifts (`⇑ₕ`). Targets `t` are variables `h₍ᵢ₎` or
terms `u⟨ρ⟩`: a term atom `u` with a payload adjustment `ρ`, applied only
to `u`'s named variables. Labels are the bound label `·`, concrete
labels, and label atoms, ordered by the facts in context.

Two expressions are *equal* when they denote the same adjustment for
every interpretation of their atoms (consistent with the facts). The
normal form is meant to be a complete invariant: equal expressions have
the same normal form.

## Words

Internally a normal form is a *word*

    U₀ ⨾ ⇑ᴸ¹σ₁ ⨾ U₁ ⨾ ⇑ᴸ²σ₂ ⨾ … ⨾ ⇑ᴸⁿσₙ ⨾ Uₙ

of segments `Uᵢ` and atoms `σᵢ` under multisets of lifts `Lᵢ`. A segment
is a context form with the identity tail: per label, in label order, the
targets of its first inputs and its number of outputs, with no
transparent last entry. Write `Vᵢ` for the variables `⇑ᴸⁱ` passes
around `σᵢ`: `h₍₀₎ … h₍ₖ₋₁₎` for each `h` lifted `k` times.

The conditions:

1. **Segments are canonical** (ordered, distinct labels, trimmed).
2. **The segment before a lifted atom is in lift position.** Let `Pᵢ` be
   the inputs `Uᵢ₋₁` sends into `Vᵢ`. Then every variable of `Vᵢ` is
   reached; `Lᵢ` lifts each label `g` as many times as `Pᵢ` has inputs
   labelled `g`; and `Uᵢ₋₁` sends the `j`-th input of `Pᵢ` labelled `g`
   to `g₍ⱼ₎`. So the renaming of passed-around variables, merging them,
   and which labels are lifted all live in the segment after the atom:
   `⟦ y \ x ⟧ ⨾ ⟦ x | σ ⟧` is `⟦ y | Γ \ x | Γ[σ] ⟧`.
3. **Terms stay before atoms.** A term the segment before an atom
   substitutes stays there (`⟦ x := u ⟧ ⨾ σ`). A term after an atom, on a
   variable passed around it, whose payload starts with that atom, is
   moved before it.
4. **Payloads are normal for what they mean.** A payload word is applied
   to named variables only: condition 2 for its first atom counts named
   inputs only, and its first segment has no bound-label entry. Payload
   words satisfy 1–4 themselves.

## Expressions shown

A word is shown as a sequence of context forms

    B₀ ⨾ F₁ ⨾ B₁ ⨾ … ⨾ Fₖ ⨾ Bₖ

- Each `Fⱼ` is a form `⟦ I | Γ \ O | Γ[σ ⨾ … ⨾ σ'] ⟧` whose tail is a
  maximal run of atoms with the same lifts and the identity between
  them. Its inputs `I` are the variables passed around the run.
- The segment after a run is split into the part on the variables passed
  around it, which gives the form's outputs `O`, and the part on the
  run's outputs, which is the separate form `Bⱼ` (left out when it is
  the identity). The split is not made when the second part would put an
  output of the run underneath one of the form's outputs of the same
  label (`⟦ x | σ ⟧ ⨾ ⟦ y \ x ⟧`); the segment is then shown whole.
- A form with no entries is shown as its tail.

So forms join where they share known variables, and stay apart where the
later one only acts on what the earlier one's tail produced:
`⟦ x | σ ⟧ ⨾ ⟦ x \ y ⟧ ⨾ ⟦ y | τ ⟧` is `⟦ x | Γ \ y | Γ[σ ⨾ τ] ⟧`, while
`⟦ x | σ ⟧ ⨾ ⟦ y \ z ⟧` stays as it is.

## Uniqueness

To be proved: two words satisfying 1–4 that denote the same adjustment
for every interpretation of their atoms are equal; and the evaluation of
a variable by `names` succeeds whenever its result does not depend on the
interpretation of the atoms.
