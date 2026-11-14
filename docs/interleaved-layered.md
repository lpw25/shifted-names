# The layered form with interleaved labels

How the layered normal form (`docs/normal-forms.md`,
`docs/design-nf2.md`) extends to the models of
`docs/normaliser-spec.md`, where a label denotes a sequence of
variables and labels that are not ordered may share variables.

## What the layered form is

- **A word** is a list of segments and atoms under lifts:
  `S₁ ⨾ S₂ ⨾ ⇑ᴸσ ⨾ S₃ ⨾ …`.
- **A segment** is a context form with the identity tail, stored per
  label in label order (`SEnt h ts m r`): the targets of the first
  inputs of `h`, then its number of outputs.
- **A term** in a segment has the rest of the word as its payload.
  A named substitution is a renaming to a bound variable followed by an
  instantiation:
  `⟦ x := u; y := v ⟧ = ⟦ x; y \ ·; · ⟧ ⨾ ⟦ · := u ⟧ ⨾ ⟦ · := v ⟧`.
  Which term sees what is decided by the renamings between
  instantiations.
- **Conditions** (`lnf`, `LayeredUnique.v`) fix one word among the
  equal ones:
  - *kind*: every segment has a term, or is a renaming that ends the
    word or stands before an atom in lift position;
  - *order*: a term stands in the last segment whose rest is its
    payload;
  - *routes*: a variable goes on as the least named variable of the
    rest with the same result;
  - *bound variables*: they are used and numbered by first use.
- **Uniqueness** (`lw_unique`, `line_unique`) goes through the free
  model `Unique.fres` by peeling atoms from the front.
- **Adequacy** (`lw_adequacy`): words equal under every interpretation
  are equal in the free model.

## Where it assumes labels are known to be distinct

1. **The free model** is defined in one interpretation (`fs` compares
   `lden h` with the variable's label). Uniqueness assumes that
   interpretation is injective on the labels involved (`Hinj`).
2. **Segments** store entries per label, sorted. That is only valid
   when every two labels of a segment are ordered. For unordered `x`
   and `y`, the input entries of `x` and `y` interleave, and their
   order matters.
3. **Lifts** around an atom are per-label counts. `⟦ x; y | σ ⟧` and
   `⟦ y; x | σ ⟧` differ when `x` and `y` are not ordered.
4. **Routes** pick the least variable in the interpretation's label
   order.
5. **The normaliser** gives up (`lcmp` returns `None`) when it needs
   an order the facts do not give.

## The extension

**Segments keep their form, with one more condition: the labels of a
segment are pairwise ordered.** An interleaving of unordered labels is
written as consecutive segments, connected through bound variables,
which are ordered against every named label:

```
⟦ x \ y ⟧         = ⟦ x \ · ⟧ ⨾ ⟦ · \ y ⟧
⟦ x; y | σ ⟧      = ⟦ x \ · ⟧ ⨾ ⟦ ·; y | σ ⟧ ⨾ ⟦ · \ x ⟧
⟦ \ x ⟧ ⨾ ⟦ y := u ⟧ = ⟦ \ x ⟧ ⨾ ⟦ y \ · ⟧ ⨾ ⟦ · := u ⟧
```

This is how the layered form already handles terms: the bound label
carries a variable from where it is chosen to where it is used. Points
2 and 3 then need nothing new in the data. Lifts stay per-label counts
over pairwise ordered labels.

**Kind.** A renaming segment may now also stand before a segment it
cannot be merged with. Two segments can be merged when their
composite is a segment whose labels are pairwise ordered. The
condition has to say which merges are taken when only part of one
segment could move into the other. This is the main new design
question.

**The free model** becomes independent of any interpretation:

- variables are a label expression and an index;
- a segment applied to `gⱼ`:
  - gives the usual result when its entry for the same label
    expression applies;
  - passes `gⱼ` on unchanged when every label of the segment is
    ordered against `g`;
  - otherwise is *stuck*: a new result `FMeet` recording the segment
    entry met, the variable, and the continuation. This is the
    counterpart of `FStuck` for atoms.

**Routes** use a fixed total order on label expressions: the facts,
then concrete labels as strings, then label atoms in context order.
Only the choice among variables with equal results depends on it.

**Uniqueness** keeps its structure. Peeling from the front gets one
new case: two words whose first difference is at a meet. Equal
`FMeet` results give the same entry and the same continuation, as
equal `FStuck` results do for atoms.

**Adequacy** is where the interleaved models do the work. It takes
words equal in every model to equal free meanings. As for atoms, the
argument picks a model that tags the finitely many stuck points a
comparison meets. At a meet of `gⱼ` with an entry on `h`, the model
chooses whether `gⱼ` is in `h`'s sequence, and where. Because labels
that are not ordered may share variables in any arrangement, these
choices can be made independently at each meet. With
stream-and-offset models they could not.

## Order of work

1. The interpretation-free model and `FMeet`, with soundness against
   the models of the spec.
2. `lnf` with pairwise ordered segments and the new kind condition;
   `lw_unique` for it.
3. Adequacy against interleaved models.
4. The normaliser: `lnorm` and `canon` building such words, never
   giving up for lack of an order.
5. Then the shared form of `docs/design-nf2.md` (branches, `share`,
   runs) on top, as before.

## Status

**Done (`Core/IModel.v`, no admits).**

- Interleaved models.
- The meaning of expressions in a model, with atoms left free.
- In a standard interpretation, the meaning is the old free meaning
  `GEval.fa` (`std_fa_all`).
- Laws: the identity renaming, cancellation, commutation of weakenings
  on ordered labels.
- The two-label example: it agrees in every standard interpretation
  (`ex_std_agree`) and differs in an interleaved model (`ex_differ`).

## The key lemma, and where it stands

Uniqueness over interleaved models needs, at its core, the following.
Take sequences of steps — entries `⟦ h := t | – ⟧` and weakenings
`⟦ \ h ⟧ ⨾ –` — in front of an atom, with each entry's target a
distinct symbol. Call a sequence *reduced* when no weakening is
followed by an entry on the same label with only steps on ordered
labels between.

> **Lemma.** Two reduced sequences that agree in every interleaved
> model are the same up to swapping adjacent steps on ordered labels.

**Stripping from the right**, the end next to the atom, works for both
kinds of step:

- *A weakening last:* the atom's results are read through `⟦ \ h ⟧`,
  which is injective, so the rests agree.
- *An entry last:* its target is a distinct symbol, so the positions
  where it shows are known, and the rests agree.

**Stripping from the left** works for an entry. It fails for a
weakening: `⟦ \ h ⟧` hides what the rest does at `h₀` in every model.

**Which steps can be last is visible in the models, for weakenings.**
`⟦ \ h ⟧` can be moved to the end exactly when the atom is never
applied at `h₀`, in any model. The proof steers one variable backwards
from `h₀` through the sequence, building the model as it goes:

- **Transfers.** At a step on a label `g` not ordered against the
  variable's current label, the model may make the current variable
  also `g`'s variable at a large fresh index. From then on only `g`'s
  steps move it, and it cannot reach `g₀` before the sequence ends.
- **When it dies.** The variable is lost only at a weakening while at
  index 0. Reducedness then forces that weakening to be the last step
  on a label not ordered against `h`.

**Open.** The same for entries: if `⟦ h := t | – ⟧` can be last in one
sequence, it can be last in the other. With that, the lemma follows by
stripping from the right. Steering should give it too: route the
variable that shows `t` through a step that the other sequence has
after the entry. That is the next thing to prove. After it come
repeated targets (variables and terms can repeat) and absorption at
the identity.
