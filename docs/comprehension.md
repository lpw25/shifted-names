# Comprehension models

A generic class of models for adjustments over label expressions, in the
style of categories with families. Adjustments are read as maps *into*
contexts, not as functions on variables. Nothing in the reading is a
test, and the only eta law is eta for pairing.

## The class

A comprehension model consists of:

- **The ambient context.** An object `U`: the context of all names. The
  syntax does not type adjustments by their named items, so every
  adjustment is an endomorphism of `U`.
- **Comprehensions.** For each label `h`, an isomorphism
  `c_h : U ≅ U × A`, where `A` is the object of values:
  - its projections are `p_h : U → U` and `q_h : U → A`;
  - its inverse is pairing, `⟨σ, t⟩_h`.
- **Ordered labels commute.** For labels the facts order, `c_g` and
  `c_h` commute: the composite `U ≅ U × A × A` is the same either way,
  up to the swap.
- **The bound label `·`** is ordered against every named label.
- **Nothing else.** Labels the facts leave unordered get no axioms.
  Atoms are free.

The constructors of `aexp` are read as follows. `ACompose a b`, with `b`
acting first on a variable, is `b ∘ a`. A word `s₁ ⨾ … ⨾ sₙ` is
`s₁ ∘ … ∘ sₙ`.

| Syntax | Meaning |
|---|---|
| `AOuter h a` (output entry, `⟦ \ h as _ ⟧`) | `a ∘ p_h` |
| `AInner h t a` (input entry) | `⟨a, t⟩_h` |
| `ALift h a`, that is `⟦ h \| a ⟧` | `⟨a ∘ p_h, q_h⟩_h` |
| `TVarE h i`, the name `hᵢ` | `q_h ∘ p_hⁱ` |
| `TShiftE h t` | `t ∘ p_h` |

## Composition

Every adjustment is an endomorphism of `U`, and composition is
composition in `End(U)`.

**Direction.** An adjustment sends each input name to a result over its
output. So it is a morphism from its output context to its input
context, the direction of substitutions. `ACompose a b`, with `b`
acting first on a variable, is `b ∘ a`:

- `b` gives each input name a result over `b`'s output;
- precomposing `a` substitutes `a`'s results into those.

Terms are maps `U → A`. Substituting `σ` into a term `t` is `t ∘ σ`.

Equivalently, a model is a monoid `End(U)` acting on terms, with, for
each label `h`:

- an element `p_h` of `End(U)` and a term `q_h`;
- a pairing `⟨σ, t⟩_h`;

satisfying these laws, which are the substitution laws of the
σ-calculus (Abadi, Cardelli, Curien and Lévy), one copy per label:

```
p_h ∘ ⟨σ, t⟩_h = σ
q_h ∘ ⟨σ, t⟩_h = t
⟨p_h, q_h⟩_h = id
⟨σ, t⟩_h ∘ τ = ⟨σ ∘ τ, t ∘ τ⟩_h
```

Ordered labels add their commutation. Composites reduce by these
equations. `p_h ∘ ⟨σ, t⟩_k` for unordered `h ≠ k` matches none of them
and stays as it is: that is a stuck lookup.

**In the set instances,** an adjustment acts on environments of its
output and gives environments of its input. So `s₁ ⨾ … ⨾ sₙ` applies
`sₙ` to the environment first and `s₁` last.

## The normaliser's laws are the laws of pairing

| Law | Why it holds |
|---|---|
| cancellation: `⟦ \ h as _ ⟧` then an entry on `h` | `p_h ∘ ⟨σ, t⟩_h = σ` |
| absorption: `⟦ h as v \ h as v ⟧ = ⟦⟧` | `⟨p_h, q_h⟩_h = id` |
| lift composition | functoriality of `σ ↦ ⟨σ ∘ p_h, q_h⟩_h` |
| steps on ordered labels commute; the lift law `⟦ g \| ⟦ \ h as _ ⟧ ⟧ = ⟦ \ h as _ ⟧` | `c_g` and `c_h` commute |
| a lookup of `hᵢ` passes steps on labels ordered against `h` | the same |

A lookup of `hᵢ` through a step on an unordered label is stuck: no
equation applies. That is exactly what `HNorm`'s stuck lookups do.

## Instances

- **Standard interpretations.** Labels are equal or disjoint.
- **Interleaved models** (`Core/IModel.v`).
  - Take `U` to be the environments `ρ : V → A`, with
    `c_h(ρ) = (ρ ∘ sh_h, ρ(h₀))`.
  - This is a bijection, because `sh_h` maps `V` one to one onto every
    variable except `h₀`.
  - Ordered labels have disjoint sequences, so their comprehensions
    commute.

  So every equation that holds in all comprehension models holds in
  every interleaved model and every standard interpretation.
- **Zero-set models are not instances.** A label with several index-0
  variables has no single head `q_h`.
- **Generic instances** (`proto/comprehension/gmodel2.py`).
  - Each label pops a tape, after an invertible linear mixing of the
    leading cells of a few tapes.
  - Labels the facts order get disjoint tapes and mixing regions.
  - Here a label's head can be "partly" another label's, which is the
    "between equal and not equal" that interleaved models cannot
    express.

## What holds and what does not

Separated means "the two words differ in some generic instance". Counts
are out of 300 random instances.

| Pair | Standard | Comprehension |
|---|---|---|
| the facts example (rule 4, one-sided) | equal | separated (227) |
| the joint rule-4 example | equal | separated (123) |
| example 1 of `docs/labels.md` | equal | separated (287) |
| example 2 | equal | separated (160) |
| `t1`/`t2` (`HEtaGap`, equal targets) | equal | separated (279) |
| `r1`/`r2` (`HEtaGap`) | equal | separated (275) |
| `f1`/`f2` (`HNormGap`) | equal | separated (249) |
| cancellation, the lift law, ordered commutation | equal | equal (0) |

**`HNorm` alone matches comprehension models exactly** on every word
checked. In each run below, every word is normalised by `HNorm` in Coq
against one shared table. The resulting classes are then compared with
the meanings in 40 random generic instances, at two environments each.

| Labels | Facts | Steps | Words | `HNorm` classes | Unsound classes | Classes merged by every instance |
|---|---|---|---|---|---|---|
| `a, b` | none | up to 5; weakenings and entries to `·`, `·¹` | 5,695 | 5,695 | 0 | 0 |
| `g, h, m` | `g < h` | up to 4; the same | 5,845 | 3,900 | 0 | 0 |
| `a, b` | none | up to 4; also targets `k₀`, `k₁` and lifts `⟦ l \| ⟦ \ k as _ ⟧ ⟧` | 35,301 | 26,999 | 0 | 0 |
| `g, h, m` | `g < h` | up to 3; the same | 26,650 | 17,248 | 0 | 0 |

"Unsound" counts classes containing words of different meaning.
"Merged" counts pairs of classes with the same meaning in every
sampled instance.

**The decision-based eta pass of `HEta` is not sound here.** On random
words, the Python version of it (`mc/nfthm2.norm`) changes the meaning
in about 1% of cases. For example, it treats the last entry of
`W d ⨾ E b ⨾ W b ⨾ E d(t)` as dead and drops its target. When `b`'s
comprehension mixes `d`'s tape, the target matters.

## Consequences

- **Rule 4 is not part of this spec**, and neither are the same-target
  swap or the decision-based eta pass. The costly part of the canonical
  form disappears.
- **The old gaps were artefacts.** `HNorm` keeps apart `r1`/`r2`,
  `t1`/`t2` and `f1`/`f2`, which looked like failures of canonicity over
  interleaved models. Comprehension models separate all three.
- **Cases are gone.** Examples 1 and 2 are not identities, as intended,
  and no case split on label overlap is needed anywhere.

## The theorems (`Core/CNorm.v`, `Comp.v`, `CSound.v`, `CComplete.v`, `HRefine.v`)

All closed under the global context (no axioms). `F` is the order of
the facts, and the completeness half assumes that `lt_known F` is
irreflexive and transitive.

| File | Content |
|---|---|
| `Comp.v` | comprehension models (`cmodel`, `ccons`), the meaning `ca` of expressions, `cequal` |
| `CNorm.v` | `HNorm`'s algorithm on plain lists, with stuck lookups made canonical (`relnf`, below) |
| `CSound.v` | `cn_sound`: equal normal forms imply equal in every comprehension model |
| `CComplete.v` | the term model on normal words (`tmodel`); `cn_complete`; `cn_eq_correct : cn_eq F a b = true <-> cequal F a b` |
| `HRefine.v` | hash-consed words read as `CNorm` words; `hn_eq_cn : hn_eq F a b = cn_eq F a b`; `hn_eq_correct : hn_eq F a b = true <-> cequal F a b` |

**The term model.** Environments are normal words, values are values:

- `cpop h` is `pushW h`;
- `chd h` is `lookup h 0`;
- `cpush h` is `pushE h`;
- an atom conses its step;
- a term atom is the term with its cleaned payload.

Normal words are sorted, with no weakening followed by an entry on the
same label (cancellation) and no absorbable entry. The laws of a
comprehension model are then lemmas about the normaliser's operations,
and an expression means its own normal form there. That is
completeness.

**A fix to `HNorm` that completeness needed.** A lookup stuck at a step
used to keep the whole rest of the word. A later step on a label `h`
known distinct from the looked-up `g`, behind steps that commute with
`h`, does not affect the lookup. For example, with `g < h` and `k < h`,
`⟦ k | ⟦ \ h as _ ⟧ ⟧ ⨾ ⟦ \ g as _ ⟧ ⨾ E h(·)` equals `⟦ \ g as _ ⟧`,
but the stuck value kept the entry on `h`, so the absorption check
failed. On words of up to 3 steps with these facts, `HNorm` missed
1,504 identities. Now a stuck lookup keeps only the steps that can
affect it (`relnf`), and `HNorm` matches the generic models exactly
there (10,023 classes).

**Cost of the fix.** A stuck lookup now scans the rest of its word.
Families with no stuck lookups are unchanged. Nested lifts over label
atoms, where every lookup is stuck, become quadratic:

| Nested lifts | old | new |
|---|---|---|
| 1,024, eight label atoms | 0.054 s | 1.09 s |
| 1,024, 1,024 label atoms | 0.17 s | 4.7 s (label atoms are unary numbers, so each comparison grows with `n`) |

## Segments need reads placed among their outputs (`Core/XRead.v`)

`Normalise.v`'s segments record, per label, the input targets and the
number of outputs, and a target `h₀` is a name of the segment's
output. With unordered labels that is not enough.

Take facts `g < k`, `g < l`, `k < l`, with `h` ordered against none of
them. Let `C = ⟦ g as v; h as v \ h as v ⟧`, which copies `h₀` into
`g`. Put the weakenings of `k` and `l` on either side of `C`:

| Word | Where `g`'s read of `h₀` sits |
|---|---|
| `X1 = ⟦ \ l as _ ⟧ ⨾ C ⨾ ⟦ \ k as _ ⟧` | below `k`, above `l` |
| `X2 = C ⨾ ⟦ \ k as _ ⟧ ⨾ ⟦ \ l as _ ⟧` | below both |
| `X3 = ⟦ \ k as _ ⟧ ⨾ ⟦ \ l as _ ⟧ ⨾ C` | above both |
| `X4 = ⟦ \ k as _ ⟧ ⨾ C ⨾ ⟦ \ l as _ ⟧` | below `l`, above `k` |

All four have one input on `g` reading `h₀` and one weakening each of
`k` and `l`, and the weakenings commute with each other. They are
pairwise different in comprehension models: `XRead.v` proves it from
`cn_eq_correct`, with no axioms. A segment holding only targets and
output counts would identify all four.

So a target in a form must say where it is read among the form's
outputs. With that, each of the four is a single form (`CForm.v`
below): outputs `k` and `l`, and the input on `g` reading `h₀` at
depth 1, 2, 0 and 1 respectively (in `X4` the outputs are in the order
`l`, `k`, kept there by the read between them).

## Context forms and a left-to-right pass (`Core/CForm.v`)

**Forms.** A context form `⟦ I \ O ⟧` has outputs `O`, popped in order,
and inputs `I`, each pushed with a target. A target is a term, or a name
`zᵢ` read at depth `d`: after the first `d` outputs are popped. Depth
`0` is a name of the form's own output; a read exactly at an output is
that output's slot; depth `length O` is a name of the identity tail.

**Expressions as forms** (`of_exp`). An expression is a word of forms
and lifted atoms:

| Syntax | Form |
|---|---|
| `⟦ \ h as _ ⟧` | one output `h`, no inputs |
| input entry on `h` with target `t` | one input `h ↦ t` (a target under weakenings reads them as restored outputs) |
| `⟦ h \| F ⟧` for a form `F` | output `h` on top of `F`'s outputs, input `h ↦ h₀` (depth 0), `F`'s reads one deeper |
| `⟦ h \| a ⟧` for an atom | the atom, lifted |

So a lift of a form is a form. `of_exp_sound`: the word means what the
expression does.

**The pass** (`run`), left to right over the word:

- **Compose** adjacent forms `F₁ ⨾ F₂` (`compose`). `F₁`'s outputs, in
  order, meet `F₂`'s inputs: an output cancels the first input on its
  own label, passes inputs on labels ordered against it, and otherwise
  is blocked. The outputs that pass all of `F₂`'s inputs go below `F₂`'s
  outputs. `F₁`'s reads are followed the same way: through `F₂`'s inputs
  (becoming an input's target, or passing), then as reads in the new
  outputs.
- **Move single items on** (`transfer`) when `F₁ ⨾ F₂` is blocked. An
  output of `F₁` that commutes with the outputs above it, and that no
  read above it needs, moves into `F₂`. An input of `F₁` that commutes
  with the inputs inside it and with `F₁`'s outputs moves into `F₂` too:
  its read is taken back to `F₁`'s output and then followed through
  `F₂` like a read in `compose`.
- **Tidy** a form (`tidy`):
  - sort inputs and outputs on ordered labels (a read between two
    outputs can pin their order);
  - take each read as early as it can be;
  - drop an input that restores an output, with that output, when both
    can move to the inside (`absorb`; this is the lift law and
    absorption).

Every step is sound in every comprehension model consistent with the
facts (`compose_sound`, `transfer_sound`, `tidy_sound`, `run_sound`).
Then `cf_eq` runs the pass and `CNorm`, and `cf_eq_correct : cf_eq F a b
= true <-> cequal F a b`. Closed under the global context.

**Examples** (`CForm.Examples`, by computation), with facts `g < h`,
`k < h`, `m < h`:

- `W1` and `W2` both give `⟦ g ↦ m₀ read below k; h ↦ ·₀ \ k as _ ⟧`.
- `Y1 = RE g g₀ ⨾ RE h g₀ ⨾ ⟦ \ k as _ ⟧` and `Y2 = RE g h₀ ⨾ RE h g₀ ⨾
  ⟦ \ k as _ ⟧` give one form.
- `⟦ \ g as _ ⟧ ⨾ ⟦ k | ⟦ \ h as _ ⟧ ⟧` and `⟦ \ g as _ ⟧ ⨾ ⟦ \ h as _ ⟧`
  give one form (the lift law).

**Tested, not proved: the pass removes the need for `relnf`.** A Python
copy of the pass, then `HNorm` without `relnf`, gives exactly the classes
of `HNorm` with `relnf` on every word of:

| Labels | Facts | Steps | Lifts | Classes |
|---|---|---|---|---|
| `g, h, k` | `g < h`, `k < h` | up to 3 | yes | 10,023 |
| `g, h, k, m` | `g < h`, `k < h`, `m < h` | up to 3 | no | 44,138 |
| `a, b, c` | `a < b`, `b < c` | up to 3 | yes | 4,279 |
| `a, b` | none | up to 4 | yes | 26,999 |
| `g, h, m` | `g < h` | up to 3 | yes | 17,248 |
| `a, b, c, d` | `a < c`, `b < c`, `c < d` | up to 2 | yes | 1,266 |

These words have no terms and no atoms, so the term and atom cases of
the pass are covered by the soundness proofs only.

## Cost of the pass (`proto/comprehension/rforms.py`)

The pass of `CForm.v` (and `forms.py`) re-tidies the whole form after
every merge, rewrites every read of the left form in `compose`, and tries
every item when two forms are blocked: cubic on a word that builds one
form, quartic in the worst case.

`rforms.py` is the same pass reworked so that a step only touches what
moves:

- **Order.** The expression is processed from its end, as `HNorm` does.
  Each new form enters on the left of the settled word, and its outputs
  and inputs move right, form by form, as far as they go. Items still
  only move right.
- **Placing.** A form that receives items places only those: new outputs
  and inputs by insertion, new reads taken as early as they go, new
  restores absorbed. Sorting a merged form is never redone from scratch.
- **Moving on.** Only items that just arrived in a form are tried against
  the next one. A boundary is looked at again in full only when an input
  of the form to its right is cancelled, or the form to its left loses an
  input.
- **Lifts.** A chain of lifts is applied in one go, absorbing restores
  innermost first, so nested lifts do not copy the lifted form once per
  lift.
- **Absorption** takes a restore whose read reaches its output through
  outputs it commutes with (the old check wanted the read exactly at the
  output, and missed the lift law once sorting had moved the output down;
  `CForm.absorb_at` has the same gap).

**Bound.** A new item passes each settled item at most once; a boundary is
looked at again in full at most once per input that disappears, at a cost
of the size of the form on its left. So the comparisons are proportional
to the moves made, plus `O(m)` per disappearing input: `O(n²)` in the
worst case. (The prototype also memmoves Python lists in place, which is
`O(m)` per step in C.)

**Measured** (doubling `n`; seconds at the largest `n`):

| Family | Growth | Time | Moves |
|---|---|---|---|
| copies along an ordered chain with weakenings (one form) | ×4 | 0.29 s at 1,600 steps | quadratic |
| `HNorm` (no `relnf`) on the same words | ×5 | 0.40 s | |
| nested lifts, unordered labels | ×2 | 0.003 s at 800 | 0 |
| nested lifts, ordered labels (all absorbed) | ×2 | 0.005 s at 800 | 0 |
| weakenings on unordered labels | ×2 | 0.021 s at 4,000 | 0 |
| copies on unordered labels (all blocked) | ×2 | 0.035 s at 4,000 | linear |
| random words over 8 labels | ×2 | 0.013 s at 800 | linear |

The chain is quadratic because each weakening passes all the inputs of
the form, as `HNorm`'s insertion does on the same words.

`rforms_check.py`: the reworked pass, then `HNorm` without `relnf`, gives
exactly the classes of `HNorm` with `relnf` on all six test sets above.

## The reworked pass in Coq (`Core/CRun.v`)

`CRun.v` is `rforms.py` in Coq. An `iform` is a `CForm.form` with ids for
its outputs and inputs (binary `positive`s), so that the pass knows which
items are new. Every operation computes its form with operations of
`CForm` or new ones proved here, and moves the ids along; the ids only
decide what is tried, so soundness does not depend on them.

| Part | Definitions | Soundness |
|---|---|---|
| placing by insertion | `iswap`, `ioswap`, `place_in_inward`, `place_out_up`, ... | `iswap_sound`, `place_*_sound` |
| reads taken as early as they go | `reread` | `reread_sound` |
| absorption through commuting outputs | `slot_go`, `absorb2`, `iabsorb`, `absorb_new` | `absorb2_sound`, ... |
| composing, with ids | `icompose` | `icompose_sound` |
| one item moved on | `imove`, `try_ids`, `moves` | `imove_sound`, `moves_sound` |
| the word | `step`, `settle` (binary fuel), `insert` | `step_sound`, `settle_sound`, `insert_sound` |
| lifts at once | `lift_n` (`= fold_right lift_f`), `lift_many` | `lift_n_eq`, `lift_many_sound` |
| expressions, from the end | `rnorm`, `peel`, `rrun` | `rnorm_sound`, `rrun_sound` |
| the decision | `cr_eq` (the pass, then `CNorm`) | `cr_eq_correct : cr_eq F a b = true <-> cequal F a b` |

All closed under the global context.

**Same results as the prototype.** On 2,410 words (every word of up to 2
steps over `g, h, k` with `g < h`, `k < h`, lifts included, and 1,500
random ones of 3 steps), `rrun` gives exactly the forms of `rforms.py`.
`CRun.Examples` checks `W1`/`W2`, `Y1`/`Y2`, the lift law
`⟦ \ g as _ ⟧ ⨾ ⟦ k | ⟦ \ h as _ ⟧ ⟧ = ⟦ \ g as _ ⟧ ⨾ ⟦ \ h as _ ⟧`, and
`⟦ h | ⟦ \ g as _ ⟧ ⟧ = ⟦ \ g as _ ⟧` (which `CForm.run` misses).

**Cost under `vm_compute`**, 8 labels, doubling `n`:

| Family | `n` | Time | Growth |
|---|---|---|---|
| nested lifts | 2,000 | 0.69 s | ×3 to ×5 |
| weakenings | 4,000 | 2.7 s | ×4 |
| copies | 4,000 | 0.56 s | ×3.5 |

These are quadratic where the Python pass is linear, for two reasons of
representation, not of the algorithm:

- new outputs go at the bottom of a form, which is the end of a list, so
  each `compose` copies the form's outputs (Python appends in place);
- inputs and outputs are reached by position (`nth_error`, `swap_at`,
  `remove_at`), linear in the position, where Python indexes in constant
  time. In the worst case (an item bubbling far through a large form)
  this makes a swap linear and the pass cubic.

With label atoms numbered up to `n` (`LAtom n` is unary), comparisons also
grow with `n`, as for `HNorm`.

## A representation without the quadratic lists (`Core/CRun2.v`)

`CRun2.v` keeps `CRun.v`'s algorithm and changes the representation:

- an `eform` holds its outputs bottom-first (`ob`), so new outputs are
  pushed at the head, with a cached count `ol`;
- ids live next to the outputs and inputs they name;
- the reads at each depth are counted in a `PositiveMap`, so an output
  swap needs no scan of the inputs;
- composition, reads and placement are native. The rarer steps (moves,
  absorption at a slot) go through `CRun`'s representation via `of_i` and
  `to_i`.

`rrun2_sound` gives `wden M (rrun2 F e) x = ca e x` under the invariant
`ok` (the cached count is right; no input reads deeper than the outputs).
`cr2_eq_correct` follows by `CNorm` completeness. It is closed under the
global context.

`rrun2` agrees with the Python pass on 2,410 words. Under `vm_compute`, 8
labels, `n` = 1,000 / 2,000 / 4,000:

| Family | `rrun2` | `rrun` |
|---|---|---|
| weakenings | 0.03 / 0.12 / 0.47 s | 0.17 / 0.67 / 2.57 s |
| copies | 0.03 / 0.05 / 0.17 s | 0.02 / 0.04 / 0.09 s |
| nested lifts | 0.11 / 0.48 / 1.74 s | — |

Nested lifts remain quadratic for two reasons:

- `List.rev` is the naive, quadratic reversal;
- depths are unary, and under `n` lifts the `n` restores read depths
  `0 … n-1`, so they alone have size `n²`.

## The pass with binary depths, on the specification alone (`Core/CSpec.v`, `Core/CRunN.v`)

**`CSpec.v`** holds the specification:

- forms and targets, and their reading as expressions (`of_exp`, `wexp`);
- their meaning in a comprehension model (`fden`, `wden`) and the
  semantic lemmas about it;
- `liftsem` and its laws;
- generic list helpers.

`CForm.v` re-exports it, so `CForm`, `CRun` and `CRun2` are unchanged.

**`CRunN.v`** is the pass to keep. It changes `CRun2`'s representation in
three ways:

- depths, name indices and the output count are binary (`N`). List
  positions stay `nat`, since each is used to walk a list that far;
- lists are reversed with `rev'` (linear);
- the outputs passed in a composition are kept newest first, with their
  count.

`CRunN` imports only `CSpec`. Every step is proved sound against `fden`
directly: reads, swaps, composition, absorbing a restore, moving an
output or input on, and lifts (against `fold_right lift_f`).

- `rrunN_sound` gives `wden M (rrunN F e) x = ca e x`.
- `crN_eq_correct` follows by `CNorm` completeness and is closed under the
  global context.
- `CRunN.v` builds in a copy of the theory with `CForm.v`, `CRun.v` and
  `CRun2.v` deleted.

`rrunN` agrees with the Python pass (and with `rrun2`) on 2,410 words.

**Cost under `vm_compute`**, 8 labels, timing the binary result
(`rnormN`; converting it back to unary is itself quadratic for nested
lifts):

| Family | `n` = 8,000 / 16,000 / 32,000 |
|---|---|
| nested lifts | 0.04 / 0.10 / 0.15 s |
| a lift over `n` weakenings | 0.09 / 0.19 / 0.31 s |
| `n` lifted compositions | 0.48 / 0.98 / 2.0 s |

| Family | `n` = 2,000 / 4,000 / 8,000 |
|---|---|
| weakenings | 0.03 / 0.06 / 0.10 s |
| copies | 0.04 / 0.08 / 0.14 s |
| nested lifts, `rnorm2` | 0.41 / 1.57 / 5.87 s |
| nested lifts, `rnormN` | 0.01 / 0.02 / 0.04 s |

All are linear. Label atoms (`LAtom n`) are still unary throughout the
codebase.

**Adversarial families.** 8 labels with `a0 < … < a7`, `n` = 250 / 500 /
1,000, binary result. "Python" is `rforms.py` on the same family.

| Family | `rnormN` | Python |
|---|---|---|
| lifts whose restores are all absorbed | 0.08 / 0.26 / 1.0 s (×4) | 0.004 / 0.016 / 0.058 s (×4) |
| weakenings composed with entries | 0.11 / 0.45 / 1.7 s (×4) | 0.049 / 0.18 / 0.78 s (×4) |
| entries composed with weakenings | 0.14 / 0.52 / 2.2 s (×4) | 0.030 / 0.12 / 0.52 s (×4) |
| payload entries composed with weakenings | 0.15 / 0.49 / 1.9 s (×4) | — |
| lifts with some restores kept | 0.15 / 0.61 / 2.6 s (×4; was ×7) | 0.014 / 0.059 / 0.24 s (×4) |
| copy chain with weakenings | 0.021 / 0.04 / 0.081 s | — |
| a weakening through blocked forms | 0.007 / 0.01 / 0.02 s | — |

Two of these were cubic and are now quadratic:

- `bset_in` compared every input position with `p` in unary;
- `bslot_go` reached each output with `nth_error`.

The quadratic families are quadratic in the Python pass too: outputs and
inputs are placed by insertion into sorted lists, and every absorbed
restore re-places the outputs below it.

Lifts with kept restores were cubic too. After each absorbed restore
the outputs below are re-placed, and each output swap scanned every
input. Two shortcuts were tried in Python and rejected, because they
change normal forms (1–2 of 4,000 random expressions):

- skipping that placement during a lift chain;
- placing all outputs once after the chain.

Instead, when a placement first needs a swap, it turns the inputs into
a map from keys to inputs and a map from depths to the keys of the reads
there (`imap`). A swap (`sswap`) then updates only the reads at its
depth; it is proved to do what `swap_in_b` does to the list. The family
is now quadratic, as in Python.

**What still costs.** Each insertion still scans the whole form somewhere:

- placement by insertion;
- `iabsorb_b` converting the form on every absorption attempt (about 60%
  of the time for weakenings composed with entries);
- the composition scans.

A label summary built at each composition did not help, since building
it costs as much as the scan it saves. These would need summaries kept
in the form itself, such as counts or positions per label.

## Still open

- **The order hypotheses.** Irreflexivity and transitivity of
  `lt_known F` are assumed. They should follow from consistent facts,
  but are not proved for `order_of`.
- **`TNorm` has the same stuck-lookup problem** and is not fixed.
- **The eta pass of `HEta` is not sound** for comprehension models and
  should not be used with `HNorm`.
- **Cost:** stuck lookups could be made cheaper, for example by
  memoising `relnf` per label and cell.
- **Superseded passes, which can now be deleted:**
  - `CForm.v`'s own pass (`run`, `cf_eq`): sound but cubic; it misses the
    lift law once sorting has moved the lifted output down, and its `tidy`
    can stop after one bubble pass;
  - `CRun.v`;
  - `CRun2.v`.

  Nothing in `CSpec` or `CRunN` depends on them.
- **Label atoms are unary** (`LAtom n`), across the codebase.
