# Labels that may coincide

Working notes towards a canonical form that meets
`docs/normaliser-spec.md` when label atoms may denote the same label.

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
