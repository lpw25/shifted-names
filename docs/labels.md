# Labels that may coincide

Working notes towards a canonical form that meets
`docs/normaliser-spec.md` when label atoms may denote the same label.

**Superseded criterion.** These notes quantify over standard
interpretations. The spec now uses the wider class of models in which
a label may start partway along another label's stream. Under those
models, identities that need a case split on label equality (such as
`c_x ⨾ c_y = c_y ⨾ c_x`) no longer hold and need not be identified.
The identities below are re-checked against the models in "Which of
these hold in the models of the spec".

## The setting

The bound label is always distinct from named labels, so only the
named part of a node is affected. That part is a word over two kinds
of letter, read left to right, followed by a uniform base (the
identity, or stuck at an atom):

- `P_h(e)`: push the entry `e` on label `h`;
- `D_h`: drop an input of label `h`.

**Meaning.** Fix an interpretation `I`. Its classes are the sets of
label expressions with the same value. For each class `c`, keep the
letters whose label is in `c`. This *projection* is a one-label word.
It acts on the stream of results for that class, applied right to
left: `P(e)` is "cons `e`" and `D` is "tail". The base supplies
`base_c(i)`. Two words are equal when every class of every consistent
interpretation gets the same stream.

**One-label words.** The normal form is `P(e₁)…P(e_k) D^m`:

- `D P(e) = ε`;
- `P(e) D w = w` exactly when `e` is what `w` gives at index 0
  (absorption, generalised).

## Identities that hold in every interpretation

Here `x` and `y` are label atoms with no facts relating them.

1. **Known-distinct labels commute.** Operations on labels that are
   known distinct (facts, concrete labels) commute.
2. **Drops commute.** `D_h D_g = D_g D_h`.
3. **Cancellation.** `D_h u P_h(e) = u` when no letter of `u` has a
   label that may equal `h`.
4. **Pushes with equal entries commute.** `P_x(e) P_y(e') = P_y(e') P_x(e)`
   when `e` and `e'` are equal in every interpretation with `x = y`.
   For example `P_x(x₀) P_y(y₀) = P_y(y₀) P_x(x₀)`.
5. **A push and a drop can commute, depending on the rest.**
   `P_y(e) D_x w = D_x P_y(e) w` when `e` equals what `w` gives at
   index 0 of the merged class in every interpretation with `x = y`.
   For example `P_y(u) D_x P_y(u) = D_x P_y(u) P_y(u)`.
6. **Absorption.** `P_h(e) u D_h w = u w` when no letter of `u` may
   share `h`'s label and `e` equals what `u w` gives at `h₀` in every
   interpretation.

### Which of these hold in the models of the spec

In a model, a letter on `h` acts on `h`'s window. Write `a`, `b` for
the offsets of `x` and `y` on a shared stream, and `F` for what the
rest of the word gives, as a function of the stream position:

- `P_h(e) F` sends `off h` to `e`, `p > off h` to `F(p−1)`, and
  `p < off h` to `F(p)`;
- `D_h F` sends `p ≥ off h` to `F(p+1)`, and `p < off h` to `F(p)`.

Taking `a = 0`, `b = 1` (or the reverse) and the identity base
`F(p) = p` gives:

| Identity | In every model? | Counterexample |
|---|---|---|
| 1. known-distinct labels commute | yes: they never share a stream | |
| 2. drops commute | only for known-distinct labels | `a = 0`, `b = 1`: `D_x D_y` gives `[2, 3, 4, …]`, `D_y D_x` gives `[1, 3, 4, …]` |
| 3. cancellation | yes: one window, and `u` acts on other streams | |
| 4. pushes with equal entries commute | only for known-distinct labels | `a = 0`, `b = 1`: `P_x(e) P_y(e')` gives `[e, 0, e', …]`, `P_y(e') P_x(e)` gives `[e, e', 0, …]`; they agree only if `e' = 0`, and `e' = y₀` is position 1 |
| 5. push and drop commute in context | no | `b = 0`, `a = 1`: `P_y(u) D_x P_y(u)` gives `[u, u, 1, 2, …]`, `D_x P_y(u) P_y(u)` gives `[u, 0, 1, 2, …]` (it holds when `a ≤ b`) |
| 6. absorption | yes: one window, and `u` acts on other streams | |

So between labels that may overlap, the identities left are the
single-window ones (cancellation and absorption) and commutation of
letters on known-distinct labels. The coincidence identities that made
the core lemma hard (4 and 5) are gone, and so is 2.

**The conjecture fails in the offset models.** The natural conjecture
was: two words with no cancellation or absorption left are equal in
every model exactly when they are equal as traces, with dependence
"the labels are not known distinct". Two counterexamples refute it.
Each is an identity that holds in every offset model only by a case
split on how the labels are placed.

1. **Two labels.** `D_x D_y P_x(e) P_y(f) = D_y D_x P_y(f) P_x(e)`
   in every offset model:
   - `a < b`: both put `f` at position `b−1` and are the identity
     elsewhere;
   - `a = b`: both are the identity;
   - `a > b`: both put `e` at position `a−1`.

   Both words are reduced, and no commutation relates them.
2. **Transitivity.** With a fact `x < m` and `k` unrelated to both,
   `w(e) = D_x D_k P_m(c) P_k(f) P_x(e)` does not depend on `e`:
   - `k` on `x`'s stream: `m` is elsewhere, so `D_k P_k(f)` cancels,
     then `D_x P_x(e)`;
   - `k` on `m`'s stream, or on its own: `x`'s stream sees only
     `D_x P_x(e)`.

   It relies on "`k` shares a stream with `x` and with `m`" forcing
   `x` and `m` onto one stream.

### A wider class: interleaved labels

**Model.** A model chooses:

- a set of positions;
- for each label, an injective enumeration `ι_h : nat → positions`;
- a strict partial order on labels.

**Restrictions.**

- Facts hold in the order, and concrete labels are ordered as strings.
- Labels that are ordered have disjoint enumerations.
- Nothing else is assumed. Unordered labels may share any positions,
  in any order.

**Operations.** An operation on `h` acts on the positions `ι_h(0),
ι_h(1), …` as the standard operation acts on `h₀, h₁, …`, and leaves
every other position alone. The offset models are the special case
where each `ι_h` is a tail of a stream.

**Checks.**

- **Laws kept.** Single-label laws and commutation of ordered labels
  still hold, for the same reasons as before. Transitivity of facts
  still gives disjointness, because the order is transitive.
- **Example 1.** With `ι_x = (A, B, C₃, C₄, …)` and
  `ι_y = (B, A, C₃, C₄, …)`, the left side sends `A ↦ e` and
  `B ↦ F(A)`, and the right side sends `A ↦ F(B)` and `B ↦ f`. They
  differ.
- **Example 2.** With `ι_k = (X₀, M₀, X₁, M₁, …)` interleaving `x`'s
  and `m`'s positions, `w(e)` sends `X₀ ↦ e`. So `e` is visible.

**Algebraic reading.** For each label `h`, let `M_h` be the monoid
generated by `P_h(e)` and `D_h` with `D_h P_h(e) = 1`. The
*graph product* of the `M_h`, over the graph "known distinct", is
their free product with ordered labels commuting.

- **Conjecture:** with an atom as base, equality in every interleaved
  model is exactly equality in this graph product. With the identity
  as base, absorption is added.
- **Normal forms.** Graph products have a normal form theorem: reduced
  syllable sequences are unique up to commuting independent syllables
  (Green, *Graph products of groups*, 1990; Veloso da Costa, *Graph
  products of monoids*, Semigroup Forum 2001). Their lexicographic
  normal forms would be the canonical form.
- **What remains to prove** is that the interleaved models are
  faithful: two different elements of the graph product differ in
  some model. Projections onto pairs of labels do not suffice
  (example 2 has the same pair projections for every `e`). The
  distinguishing model has to overlap several labels at once.

### Notes for standard interpretations

Some things never commute: a drop and a push on labels that may be
equal (`D_x P_y(v) P_x(u)` means `⟦y := v⟧` when `x ≠ y` and
`⟦z := u⟧` when `x = y = z`), and pushes whose entries differ when the
labels coincide.

## The proposed canonical form and its core lemma

- **Canonical form.** The shortest equivalent word, and among those
  the least in a fixed order. Labels are ordered by the facts, then
  the context order; pushes come before drops.
- **Computing it.** Apply 3 and 6 to reach a shortest word. Then sort
  by adjacent swaps that are valid in context (1, 2, 4, 5). Each swap
  is decided locally, with entries compared under the identification
  of the two labels: a recursive call with one label atom fewer.
- **Core lemma.** Two equivalent shortest words are connected by
  adjacent swaps, each of which keeps the meaning. Without it, the
  sort can stop at different words for equal meanings.

## Where the proof stands

**Generic case: plausible, not proved.** Assume no coincidences
between values: entries never equal each other or base values in any
interpretation. Then only identities 1–3 remain, and the claim
becomes:

> Two equivalent words with no cancellation (3) are equivalent as
> traces, under the dependence "the labels may be equal".

Lexicographic normal forms of traces then give canonicity.

- **Approach.** The projection lemma for traces reduces this to pairs
  of labels that may be equal. For each such pair, the interpretation
  that identifies just that pair and the all-distinct interpretation
  together should determine the order of that pair's letters.
- **Difficulty.** In one interpretation a push can be invisible
  because a drop cancels it, while it is visible in the other. For
  example, in `D_x P_y(b) P_x(e)` the entry `e` shows only when
  `x = y`. Recovering the order needs a case analysis that is not yet
  written.

**Coincidences: open.** Identities 4–6 depend on values being equal,
and 5 and 6 depend on the rest of the word. With them, equivalence is
no longer trace equivalence.

- **What is missing.** I have no proof yet that equivalent shortest
  words are connected by valid adjacent swaps once coincidences
  occur, and no counterexample.
- **Fallback.** If the lemma fails, the canonical form has to be
  defined differently, for example by choosing the first letter from
  the meaning. That runs into a different problem: when the first
  letter is a drop, the rest is not determined by the meaning.
