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

As words of single steps these are already as far right as the
moves below take them: the weakening of `l` cannot pass `C`, because
`C`'s target reads `h`, which the weakening of `l` may affect. So the
order of the steps keeps the information, and nothing extra is needed
in the representation.

## A left-to-right pass (`Core/LPass.v`)

Words of single steps, each target read where its step stands:
`RW h` is `⟦ \ h as _ ⟧`, `RE g t` is an input entry on `g` with target
`t` (so `RE g (TVarE h 0)` copies `h₀` into `g`), and `RO e` is any other
expression, which nothing passes.

The pass moves weakenings and entries whose target is a name to the
right. Write `s₁ ⨾ s₂ → s₂' ⨾ s₁'` for `s₁` moving past `s₂`, with `s₂`'s
label `g` sorting before `s₁`'s label `h` (so they commute):

| Move | Condition | Sound because |
|---|---|---|
| `⟦ \ h as _ ⟧ ⨾ RE h t → ε` | | `p_h ∘ ⟨σ, t⟩_h = σ` |
| `⟦ \ h as _ ⟧ ⨾ ⟦ \ g as _ ⟧ → ⟦ \ g as _ ⟧ ⨾ ⟦ \ h as _ ⟧` | | pops commute |
| `⟦ \ h as _ ⟧ ⨾ RE g t → RE g t' ⨾ ⟦ \ h as _ ⟧` | `t` does not read `h₀`; `t' ∘ p_h = t` | `p_h` commutes with the push on `g` |
| `RE h a ⨾ ⟦ \ g as _ ⟧ → ⟦ \ g as _ ⟧ ⨾ RE h a'` | `a' = a ∘ p_g` is a name | the same |
| `RE h a ⨾ RE g t → RE g t' ⨾ RE h a'` | `a'` is `a` read through the entry on `g`; `t' = t ∘ p_h` | pushes commute |
| `RE g x₀ ⨾ RE x t → RE g t' ⨾ RE x t` | `t' = t ∘ p_x` | `q_x ∘ ⟨σ, t⟩_x = t` |

Shifting a name past `p_g` changes its index if it is on `g` and leaves
it alone if its label is ordered against `g`. A name on a label
unordered with `g` cannot be shifted, which is what stops a move. A term
target shifted past `p_h` gets `p_h` at the end of its payload.

Each row is a lemma in every comprehension model consistent with the
facts (`swap_sound`, `subst_sound`), so the pass keeps the meaning
(`pass_sound`, `lpass_cequal`).

The pass is an insertion: each step, from the last, moves right into the
steps after it, as far as it goes.

**The examples that needed `relnf`.** With facts `g < h`, `k < h`,
`m < h`:

- `W1 = RE h ·₀ ⨾ RE g m₀ ⨾ ⟦ \ k as _ ⟧` and `W2`, with the first two
  swapped, both become `RE g m₀ ⨾ ⟦ \ k as _ ⟧ ⨾ RE h ·₀`.
- `Y1 = RE g g₀ ⨾ RE h g₀ ⨾ ⟦ \ k as _ ⟧` and `Y2 = RE g h₀ ⨾ RE h g₀ ⨾
  ⟦ \ k as _ ⟧` both become `Y1`: the copy of `h₀` takes the entry on
  `h`'s target (the last row).

Both are proved by computation in `LPass.Examples`. `Y` is the first
case the pass missed without the last row.

**Tested, not proved: the pass removes the need for `relnf`.** Run the
pass, then `HNorm` without `relnf` (`proto/comprehension/pnorm.py`
with `fix=False`), and compare with `HNorm` with `relnf` on every word.
The two give the same classes on:

| Labels | Facts | Steps |
|---|---|---|
| `g, h, k, m` | `g < h`, `k < h`, `m < h` | up to 3, no lifts |
| `g, h, k` | `g < h`, `k < h` | up to 3, no lifts |
| `a, b, c` | `a < b`, `b < c` | up to 3, no lifts |

With lifts (`⟦ l | ⟦ \ k as _ ⟧ ⟧`) it does not: on `g, h, k` with
`g < h`, `k < h`, up to 3 steps, 567 classes of the fixed normaliser
are split. The pass treats a lift as an opaque step. A lift
`⟦ k | a ⟧` is an entry on `k` whose target `k₀` is read after `a` and a
weakening of `k`, not where the entry stands, so it is not a single
step of this word.

## Still open

- **The order hypotheses.** Irreflexivity and transitivity of
  `lt_known F` are assumed. They should follow from consistent facts,
  but are not proved for `order_of`.
- **`TNorm` has the same stuck-lookup problem** and is not fixed.
- **The eta pass of `HEta` is not sound** for comprehension models and
  should not be used with `HNorm`.
- **Cost:** stuck lookups could be made cheaper, for example by
  memoising `relnf` per label and cell.
