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
- **Interleaved models.**
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
| `t1`/`t2` (equal targets) | equal | separated (279) |
| `r1`/`r2` | equal | separated (275) |
| `f1`/`f2` | equal | separated (249) |
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

**The decision-based eta pass we tried (`HEta`, since removed) is not sound here.** On random
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
| `CNorm.v` | `HNorm`'s algorithm on plain lists; a lookup gives a variable with a payload when it cannot get past a step (`follow`, below) |
| `CSound.v` | `cn_sound`: equal normal forms imply equal in every comprehension model |
| `CComplete.v` | the term model on normal words (`tmodel`); `cn_complete`; `cn_eq_correct : cn_eq F a b = true <-> cequal F a b` |
| `HRefine.v` | hash-consed words read as `CNorm` words; `hn_eq_cn : hn_eq F a b = cn_eq F a b`; `hn_eq_correct : hn_eq F a b = true <-> cequal F a b`; `hn_eq_order_correct`, the same for `F = order_of l` with no hypothesis on the order |
| `HConcrete.v` | the library's adjustments form a comprehension model consistent with facts that hold, so `HNorm` is sound for them (`hn_eq_t_sound`) |
| `KnownOrder.v` | the order `order_of l` builds is transitive and irreflexive when the facts `l` hold under some interpretation of the labels (`order_of_trans`, `order_of_irrefl`) |

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
1,504 identities.

Now a lookup is one function, `follow`, in both `CNorm` and `HNorm`. It
follows `hᵢ` through the word as `apply_var` follows a variable through
an adjustment. It passes a step that cannot affect `hᵢ`: one on a label
known distinct from `h` and sorting after the label of every step kept
so far, which can therefore be moved in front of the kept steps. (In a
normal word this is the same as known distinct from every kept label: a
passed step's label always sorts after them. If it sorted before a kept
label, it would be independent of everything between, so sortedness
would have put it first. Checked on 2.5 million words.) Until a step is
kept, a step on `h` moves the index or, as an entry for `h₀`, gives the
value. Any other step is kept, and the value is then the variable `hᵢ`
with the kept steps as its payload (`VLook h i w`), hash-consed in
`HNorm`. An atom is kept with everything after it. The payload needs no
further normalisation: the kept steps of a normal word form a normal
word, since a step is passed only when it is ordered against every kept
step around it. `HNorm` matches the generic models exactly on these
words (10,023 classes), and `cn_complete` proves it in general.

**Cost of the fix.** A lookup that keeps a step now scans the rest of its word.
Families with no stuck lookups are unchanged. Nested lifts over label
atoms, where every lookup is stuck, become quadratic:

| Nested lifts | old | new |
|---|---|---|
| 1,024, eight label atoms | 0.054 s | 1.09 s |
| 1,024, 1,024 label atoms | 0.17 s | 4.7 s (label atoms are unary numbers, so each comparison grows with `n`) |

## A context-form pass before `HNorm` (removed)

We also built a left-to-right pass that rewrote a word into context
forms before `HNorm` saw it (`XRead.v`, `CForm.v`, `CRun.v`, `CRun2.v`,
`CSpec.v`, `CRunN.v`; Python `proto/comprehension/forms.py`,
`rforms.py`). It was proved sound, and its cubic cases were fixed, but
running it first rarely paid: it helped only where it merged most of the
word away, and elsewhere `HNorm` still did its work on the pass's
output. The pass has been removed; the measurements below are kept for
the record.

## Canonicity and cost

**Canonicity.** Checked against meaning in sampled generic models with
`proto/comprehension/pipe_check.py`, length 4 on `g, h, k` (`g < h`,
`k < h`), `g, h, m` (`g < h`) and `a < b < c`, with lifts (780,391
words each), and every set at length 3:

| Pipeline | Unsound | Missed |
|---|---|---|
| `HNorm` alone | 0 | 0 |
| the pass, then `HNorm` | 0 | 0 |
| the pass, then the old `HNorm`, whose payload was the whole rest of the word | 0 | 40 (all on `g, h, k`) |

The misses of the last pipeline are not the pass's to fix. In each,
`HNorm` gets a lookup stuck at a step on a label not ordered against
the read's. It records the variable together with the rest of the word,
which includes a step the pass legitimately moved there but that cannot
affect the read (for example a weakening of `h` in a stuck lookup of
`k₀`, with `k < h`). `follow` passes such a step, as `apply_var` would
once it has been moved in front of the kept steps. An earlier rule in `rforms.py` that worked around one case
(redirecting reads of an output's slot) has been removed.

**Cost** under `vm_compute`, 8 labels (`a0 < … < a7` unless noted),
`n` = 250 / 500 / 1,000. "Pass" is `rnormN`; "pass, then `HNorm`" is
`HNorm.norm` on `crN_form`.

| Family | `HNorm` alone | Pass alone | Pass, then `HNorm` |
|---|---|---|---|
| renamings (copy then weaken the source) | 0.009 / 0.016 / 0.031 s | 0.015 / 0.029 / 0.058 s | 0.016 / 0.030 / 0.059 s |
| renamings, no facts | 0.093 / 0.37 / 1.50 s | 0.011 / 0.020 / 0.040 s | 0.11 / 0.44 / 1.57 s |
| lifts, restores absorbed | 0.14 / 0.79 / 3.63 s | 0.15 / 0.29 / 1.19 s | 0.075 / 0.31 / 1.25 s |
| weakenings composed with entries | 0.45 / 2.19 / 11.6 s | 0.15 / 0.63 / 2.73 s | 0.48 / 2.43 / 11.5 s |
| entries composed with weakenings | 0.085 / 0.40 / 2.36 s | 0.22 / 0.87 / 3.53 s | 0.53 / 2.90 / 12.8 s |
| payload entries composed with weakenings | 0.091 / 0.37 / 2.11 s | 0.19 / 0.96 / 3.24 s | exponential: 0.24 s at `n` = 16, 1.8 s at 20 |
| lifts over payload entries | 0.14 / 0.87 / 4.19 s | 0.15 / 0.67 / 2.80 s | 0.62 / 3.13 / 23.6 s |
| copy chain with weakenings | 0.21 / 0.87 / 3.45 s | 0.025 / 0.049 / 0.10 s | 0.43 / 1.73 / 6.35 s |
| a weakening through blocked forms, no facts | 0.022 / 0.090 / 0.30 s | 0.005 / 0.009 / 0.019 s | 0.029 / 0.096 / 0.41 s |

**Labels and the order table.** Label atoms carry binary numbers (`N`).
The known order (`Normalise.lt_known`) is the fixed order (concrete labels
by the string order, the bound label last) and the facts, followed
transitively. The facts are worked out once (`order_of`):

- the facts between atoms are the edges of a graph, and for each atom the
  atoms reachable from it are found by a depth-first search, bounded by
  the number of edges, and kept as a map keyed by binary keys;
- each atom gets `up`, the least concrete label the facts put above it
  or above an atom it reaches, and `down`, the greatest concrete label
  the facts put below it or below an atom that reaches it;
- each atom's row of the table also holds every atom `b` with
  `up a ≤ down b` (then `a < up a ≤ down b < b`).

Two atoms are one lookup in the table; an atom and a concrete label are
one string comparison with the atom's `up` or `down`; two concrete
labels are compared by the string order, which facts that hold cannot
add to. Building it costs O(A (A + E)) for A atoms and E facts, plus one
string comparison for each pair of an `up` and a `down`.

Normalisation makes tens of millions of comparisons, so the lookups are
kept lean: atoms are keyed by `xI` of their number (no carry, unlike
`N.succ_pos`, which cost 20% on the eight-label families); only atoms
with edges, or with a concrete label directly above them, get a row (a
row for every atom of a fact made `advN` 50% slower, the extra hits
walking deeper than early misses); and the rows and the `up` bounds are
separate maps rather than a map of pairs (10% on `absorbL` and the copy
chain). Strings are compared in one pass (`lab_cmp`: each character
once, its bits from the top, proved to agree with `is_less_than_label`,
which compares each character twice, and with `String.eqb` first in
`leb_lab`): that took the mixed `advL` from 8.6 s to 3.9 s at 133. With
the same knowledge as atoms (the formerly concrete labels chained by
facts) the work is identical, so what remained was the cost of each
comparison: 4.6 µs for an atom and a concrete label before, 1.9 µs
after, against 1.1 µs for two atoms. `lcmp` compares two concrete
labels with a single `lab_cmp` (0.85 µs rather than 2.7 µs; `lcmp_eq`
relates it to the plain definition). The extracted library never orders
labels: it only tests them for equality, which extracts to OCaml's
string equality. With unary
atoms and an L × L table of lists closed under transitivity, building the
table took 330 s for about 400 labels and each comparison cost O(L).

**Many labels, atoms and concrete.** `order_of` and the whole decision
(`hn_eq`'s normalisation with the order built in the same `vm_compute`),
for the many-label families of `hcost.py` at `m` = 10 / 33 / 133 (about
`3m` labels and up to `5m` facts). "Atoms": every label an atom.
"Concrete, facts": every label concrete, strings chosen so the facts hold.
"Mixed": about two thirds of the labels concrete, the rest atoms.

Each cell: the whole decision at `m` = 33 / 133, and in brackets
`order_of` alone at 133.

| Family | Atoms | Concrete, facts | Mixed |
|---|---|---|---|
| `manyB` | 0.008 / 0.10 s (0.001) | 0.018 / 0.36 s (0.001) | 0.012 / 0.18 s (0.001) |
| `advL` | 0.066 / 4.7 s (0.19) | 0.010 / 0.11 s (0.005) | 0.067 / 3.9 s (0.03) |
| `advC` | 0.034 / 2.1 s (0.25) | 0.010 / 0.13 s (0.006) | 0.057 / 1.9 s (0.03) |
| `advR` | 0.046 / 3.0 s (0.22) | 0.017 / 0.30 s (0.006) | 0.049 / 2.7 s (0.03) |
| `advN` | 0.030 / 1.6 s (0.38) | 0.009 / 0.13 s (0.010) | 0.030 / 0.62 s (0.33) |

All are under 0.01 s at 10. An earlier version kept the mentioned
concrete labels as nodes of the graph, chained in string order, and had
to find a concrete label's node in every comparison: by scanning the
mentioned labels, the mixed `advL` took 478 s at 133 and the concrete one
10 s; with a search tree and a map keyed by the string's bits, 11.4 s and
0.20 s. Timing `order_of` as a separate definition overstates it:
reading the table back as a term loses the sharing between rows.

**End to end.** `KnownOrder` proves the search finds exactly the atoms
reachable from its start, so the table is reachability or `up a ≤ down b`
(`otab_iff`), and `up` and `down` only tighten along a path (`up_path`,
`down_path`). When the facts hold under some interpretation of the
labels, an atom's `down` is below its `up`, and the known order is
transitive and irreflexive (`order_of_trans`, `order_of_irrefl`). Hence
`HRefine.hn_eq_order_correct`: for such facts `l`,
`hn_eq (order_of l) a b = true` exactly when `a` and `b` are equal in
every comprehension model consistent with `order_of l`. Closed under the
global context.

`HNorm`'s lookups test a step against the maximal kept labels only (the
frontier, an antichain, so never more than the width `w` of the order);
labels kept since the last test wait in a pending list and are merged
only when a step has to be tested (`decide`, `mergef`). A lookup costs
O(n·w), and normalisation O(n²·w). They used to test against every kept
step, which made the copy chain cubic (109 s at 1,000): there most
lookups keep about half the word, on a handful of labels. Orders with an
antichain of about `n` labels are still cubic (`hcost.py`: `advL`,
`advC`, `advR`).

- **Pass first rarely pays.** It helps only where it merges most of the
  word away (absorbed lifts, 3×). Elsewhere `HNorm` still does its work on
  the pass's output, and is as slow or slower.
- **Payloads blow up.** Each composition copies the right-hand form into
  every payload passing through it, unshared, so the pass's output grows
  exponentially. Payloads need `HNorm`'s sharing.
- **`HNorm`'s own costs are the bottleneck.** It is quadratic on most
  families, even where the pass alone is linear. On the copy chain each
  lookup that keeps a step walks to the end of the word to build its
  payload.

## Still open

- **Showing normal forms, applying to a variable, materialising
  payloads.** The `names` tactic decides equations with `HNorm`
  (`HConcrete.hn_eq_t_sound`), but still uses the layered normaliser
  (`Layered`, `Canon`, `LEval`) to show a normal form as context forms
  (`names_rewrite`, checked by `HNorm`), to read off where an adjustment
  sends a variable (`names_var_eq`, with `lapply_result_sound`), and to
  materialise payloads. Porting these to `HNorm`'s words would let the
  layered normaliser go.
- **Cost:** lookups that keep a step could be made cheaper, for example
  by memoising their payloads per label and cell.
