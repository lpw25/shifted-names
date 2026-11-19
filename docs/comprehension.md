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

## Not yet done

- **Term atoms with payloads (`TBindE`), and adjustment atoms**, are not
  yet in the tests. A term atom should be a map `U → A` that ignores the
  bound label: that is `bound_off`.
- **Soundness in Coq.** A record of comprehension models, the
  interpretation of `aexp`, and a lemma for each rule of `HNorm`, as
  `ZModel.v` does for zero-set models.
- **Completeness: canonicity of `HNorm` for this class.** Two expressions
  with different normal forms should differ in some comprehension model.
  The natural proof is normalisation by evaluation. Show that `HNorm`'s
  normal forms form a comprehension model, the free one, or embed
  injectively into a generic instance.
