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

**Conjecture (to prove).** In the models, two words with no
cancellation or absorption left are equal exactly when they are equal
as traces, with dependence "the labels are not known distinct".

- **Proof idea.** For a pair `x`, `y` that may overlap, the models
  with `x`, `y` on one stream at offsets far apart (in either order),
  equal, and on separate streams together pin down the order of their
  letters.
- **What it gives.** The lexicographic normal form of traces is then
  canonical, and the remaining comparisons are entry equalities in
  every model, computed recursively.

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
