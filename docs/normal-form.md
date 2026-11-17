# The normal form theorem for distinct targets

A proof on paper, for segments (the steps between two atoms) whose
targets are distinct opaque values. With the separation argument of
`docs/zero-sets.md`, it shows that `HNorm` plus the eta pass is
canonical for such segments over zero-set models. This needs two fixes
to the eta pass, below.

Notation:

- `A` is the group with one generator per label, where labels the
  facts order commute.
- `W g` is `⟦ \ g as _ ⟧`.
- `E g(v)` is an entry on `g` with target `v`.

## The theorem

A word is **normal** when:

1. **Sorted.** Adjacent steps on ordered labels come in the order of
   the facts.
2. **No cancellation left.** `W g` is never directly followed by an
   entry on `g`.
3. **No dead pair left.**
   - A dead entry on `g` is never directly followed by `W g`.
   - Every dead entry has the canonical target.

The **key** of a word is:

- its end position in `A`;
- its live tests: for each, the wall and the target;
- their order, up to swapping two tests whose walls cross.

**Theorem.** Two normal words with the same key are the same word.

With the separation argument, two words equal in every zero-set model
have the same key:

- **End position:** the model where nothing fires.
- **Live tests and targets:** one model per test.
- **Order:** one model per pair. Pairs whose walls are nested are
  ordered the same way in every word anyway, and crossing pairs are
  exactly the swaps the key allows.

So their normal forms coincide.

## Proof

**Step 1: sorted words are the lexicographic normal forms.** Two words
are *trace-equivalent* when they differ by swapping adjacent steps on
ordered labels. Each class has one lexicographically least word. A word
is that least word exactly when it has no factor `b u a` such that:

- `a` sorts before `b`;
- `a` commutes with `b` and with every step of `u`.

Sorted words have no such factor, because the facts are transitive:

- The last step of `u` is next to `a` and ordered with it, so it sorts
  before `a`.
- Going back through `u`, each step is ordered with `a`. If one sorted
  after `a`, it would sort after its right neighbour, which is ordered
  with it and next to it. That is impossible in a sorted word.
- So every step of `u` sorts before `a`, hence before `b`. The first
  one is then next to `b`, ordered with it and sorting before it,
  which is again impossible.

The same chain argument shows that in a sorted word:

- a cancellable `W g … E g`, with only steps commuting with `g` in
  between, is adjacent;
- so is a dead pair `E g … W g`.

So conditions 2 and 3 hold up to trace equivalence, not just for
adjacent steps.

**Step 2: a bigger group.** Let `Ã` be the right-angled Artin group
with these generators:

- the labels;
- one new generator `τ(g, v)` for each live test on `g` with target
  `v`.

`τ(g, v)` commutes with every label ordered against `g`, and with
`τ(h, w)` when `h` is ordered against `g`. Map a word to `Ã` by:

| Step | Image |
|---|---|
| `W g` | `g` |
| dead `E g` | `g⁻¹` |
| live `E g(v)` | `τ(g, v) · g⁻¹` |

A live test followed by `W g` becomes `τ(g, v) · g⁻¹ · g`, which
cancels to `τ(g, v)`.

**Step 3: normal words map to reduced words.** By Step 1, a pair
`x … x⁻¹` that could cancel in `Ã` is, in the original word, one of:

- a cancellation;
- a dead pair;
- a live test followed by its `W g`, which is already cancelled.

`τ(g, v)` does not commute with `g`. So it blocks every other
cancellation across it.

**Step 4: the key determines the element of `Ã`.** Let `Pᵢ` be the
position of the `i`-th live test and `x` the end position. Then

```
image of the word  =  P₁ τ₁ P₁⁻¹ · P₂ τ₂ P₂⁻¹ ⋯ Pₙ τₙ Pₙ⁻¹ · x
```

Each factor `Pᵢ τᵢ Pᵢ⁻¹` depends only on the wall:

- moving `Pᵢ` within the wall multiplies it by labels that commute
  with `τᵢ`.

Two factors for crossing walls commute:

- both can be written with a common position `Z`, as `Z τᵢ Z⁻¹` and
  `Z τⱼ Z⁻¹`;
- `τᵢ` and `τⱼ` commute, because crossing walls have ordered labels.

So words with the same key have the same image in `Ã`.

**Step 5: reduced words are equal up to commutation.** In a
right-angled Artin group, two reduced words for the same element differ
only by swapping adjacent commuting letters (the standard solution of
the word problem). So the images of two normal words with the same key
are trace-equivalent.

**Step 6: back to steps.** From a reduced word in `Ã` the original word
is recovered:

- a `τ(g, v)` whose next letter not commuting with it is `g⁻¹` comes
  from a live entry;
- any other `τ(g, v)` comes from a live test followed by `W g`.

This is unambiguous for normal words. A live test, then `W g`, then
steps commuting with `g`, then an entry on `g` would contain a
cancellable `W g … E g`, which normal words do not have (Step 1).

Trace-equivalent images therefore come from trace-equivalent words. By
Step 1, two trace-equivalent sorted words are identical. ∎

## Two fixes to the eta pass

1. **Re-sort after removing.** Removing a dead pair can make two steps
   on ordered labels adjacent in the wrong order. The pass must push
   the steps through `HNorm` again (sorting, cancelling, absorbing),
   and repeat until nothing changes. Without this, a search over words
   with the fact `a < c` found 25 pairs with the same key and different
   outputs, for example `Wa Wb Wa Ec Wc` and `Wa Wb Ec Wc Wa`. With it
   there were none: all words of up to 7 steps with `a < c`, and of up
   to 8 steps with `g < h`.
2. **Stop dropping steps from stuck lookups.** In zero-set models,
   steps on labels ordered against the looked-up label can move it
   (`docs/zero-sets.md`). Dropping bound-label steps from payloads with
   no payload atom stays.

## Repeated targets

The proof uses distinct targets in Step 4. With repeated targets, two
tests with the same target may swap even when their walls do not cross,
and the image in `Ã` changes. The normaliser then has to choose one
order of tests, and produce the word for it. That is the remaining
part, together with values that are terms or stuck lookups, and
segments joined by atoms.
