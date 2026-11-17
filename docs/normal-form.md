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

With repeated targets the meaning fixes less than the key. Two live
tests may swap when:

- **their walls cross**: they never both fire; or
- **they have the same target**: whichever fires first gives the same
  result.

The meaning still fixes three things. By the separation models:

- the end position;
- the live tests with their targets;
- the order of every pair with different targets whose walls do not
  cross.

Conversely, two orders that agree on those pairs give the same result on
every input: the first test to fire in each order, if their targets
differ, is a pair that fires together, so its walls do not cross and
both orders agree on it.

**Which orders a word can have.** A word can put its tests in any order
in which no test comes before a test it is behind. Test `u` is *behind*
`t` when `u`'s wall is on the far side of `t`'s wall from the start; any
path to `u` then crosses `t`'s wall first.

### The canonical order

Among the orders the word allows, take the least, for a fixed order on
tests (label, then wall, then target), subject to:

- the order of the word on pairs with different targets whose walls do
  not cross;
- a test before every test behind it.

Pairs whose walls cross are left free. This depends only on the meaning.

### Printing a word for it

Let `P(t)` be the point of `t`'s wall closest to the start. It is the
position with every trailing step on a label ordered against `t`'s label
removed. Print:

```
geodesic to P(t₁) ⨾ E g₁(v₁) ⨾ W g₁ ⨾ geodesic to P(t₂) ⨾ … ⨾ geodesic to the end
```

Here each geodesic is a reduced word, its entries get the canonical
target, and each test is an entry followed by a weakening. Then
normalise. By the theorem above, the result depends only on the
meaning.

**Why the printed word has exactly these live tests.** Take a wall `H`
crossed by the geodesic from `P(tᵢ)` to `P(tᵢ₊₁)`. It separates the
start from exactly one of the two points.

- **`H` separates the start from `P(tᵢ₊₁)`.** Then it separates the
  start from all of `tᵢ₊₁`'s wall, because the closest point is a gate.
  The original word reached that wall, so it crossed `H`, away from the
  start:
  - if that first crossing was an entry, `H` is a live test with
    `tᵢ₊₁` behind it. So it was printed earlier, and this crossing is
    dead;
  - if it was a weakening, this crossing is a weakening too.
- **`H` separates the start from `P(tᵢ)`.** Then this crossing goes back
  towards the start, the other way from the earlier crossing that got
  there. So it is either a weakening or a dead entry.

The geodesic to the end is the same: every wall it crosses away from the
start was crossed by the original word. Finally, the entry printed for
`tᵢ` is the first crossing of its wall. An earlier crossing would put an
earlier point behind `tᵢ`, against the order.

**Checked** (scratch `mc/reptgt.py`). For all words below, the printed
normal forms are equal exactly when the meanings (as above) are:

| Labels | Facts | Steps | Targets | Words | Meanings |
|---|---|---|---|---|---|
| `a, b` | none | up to 7 | one | 9,231 | 8,938 |
| `a, b` | none | up to 6 | two | 29,823 | 29,169 |
| `a, b, c` | none | up to 5 | one | 6,547 | 6,508 |
| `a, b, c` | `a < c` | up to 5 | two | 27,768 | 27,548 |
| `a, b, c` | `a < c` | up to 6 | one | 17,689 | 17,464 |
| `a, b, c` | `a < c, b < c` | up to 5 | two | 11,270 | 11,178 |
| `a, b, c` | `a < b < c` | up to 6 | two | 9,740 | 9,740 |
| `g, h, m` | `g < h` | up to 6 | one | 17,689 | 17,464 |

The first count agrees with the number of distinct meanings that the
earlier search over models found for those words.

**Cost.** Deciding crossing and behind for a pair is linear in the
positions, so this is cubic in the worst case. It only needs to run when
two live tests have the same target.

## Still open

- **Values that are terms, stuck lookups or variables.** The theory
  here treats targets as opaque. With variable targets, a test can be
  redundant because its target is what the rest of the word gives
  anyway (absorption). A stuck lookup's word is observed on one input,
  of a known label.
- **Segments joined by atoms.** After an atom the rest is observed on
  every variable, so each segment is separate. This needs writing out.
- **Mechanising** the separation models and the two proofs above.
