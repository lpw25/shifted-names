# The simple hash-consed normaliser

An experiment (`Core/HNorm.v`): the simplest version of the design in
`docs/nf-design.md`, checked for its bounds and timed against the
existing normaliser. Nothing in it is proved yet.

## The form

A normal form is a word of steps, kept sorted and reduced as in
`docs/nf-design.md`:

- `SE h v`: an input entry on `h` with value `v`;
- `SW h`: a weakening on `h`;
- `SA a`: an adjustment atom.

**Values are absolute.** A value is one of:

- a variable of the scope at the end of the word;
- a term with the id of its payload word;
- a lookup stuck at the first step of a word, given by its id.

**Storage.** Words are linked lists, hash-consed:

- each cell is a step and the id of the word after it;
- equal cells get one id;
- the empty word has id 1.

Two adjustments are equal exactly when their words have the same id.

## The algorithm

An expression is normalised from right to left: `norm e K` is `e`, then
the word `K`.

**Constructs.**

| Construct | Normal form |
|---|---|
| `a ⨾ b` (`b` first) | `norm b (norm a K)` |
| an atom | a cell in front of `K` |
| an output entry on `h` | a weakening on `h` pushed onto `K`, then `a` on top |
| an input entry `h := t` | the value of `t` against `K`, then `a` on top of `K`, then the entry pushed |
| a lift `⟦ h \| a ⟧` | the entry `h := (h₀ looked up in K)` pushed on top of `a`, with `a` on top of a weakening on `h` pushed onto `K` |

**Values.**

- A variable target is looked up in `K`.
- A term's payload expression is normalised on top of `K`. Its id is
  the value's payload.

**Pushing a step on `h`.** The step walks down the word past steps on
labels known distinct from `h`, to the first step on `h`, on a label
not known distinct from `h`, or an atom.

- A weakening that reaches an entry on `h` cancels with it.
- An entry that reaches a weakening on `h` is absorbed when its value
  is what the rest gives `h₀`.
- Otherwise the step is inserted in sorted position: past the steps on
  labels known distinct from `h` that sort before it.

The cells in front of the edit are rebuilt, and the rest is shared.

**Looking up `hᵢ`.** Walk down the word, adjusting the index at steps
on `h`, until it reaches an entry at index 0 (its value), the end (the
variable), or a step where it is stuck (a stuck lookup).

## Bounds

Here `n` is the size of an expression without `share`.

- **Every word has length `O(n)`.** Each input construct adds at most
  one step.
- **Each construct costs `O(n)`.** It does a constant number of walks
  and rebuilds the cells in front of one edit. Each hash-consing
  operation is one table lookup.
- **Payloads add nothing extra.** A term's payload expression is part
  of the input, and is normalised once, on top of the current word.

So time and the number of cells built are `O(n²)` (up to the table's
logarithm). The output, the cells reachable from the result, is
`O(n²)` in the worst case.

**Example of the worst case.** A word of `n` entries on labels known
distinct, sorted in the reverse of the order they are added. Each new
entry is then inserted at the end, so every suffix is a different word.
That word is reachable when terms refer to every suffix, as in a chain
of substitutions with that order.

**With `share`.** A shared expression used with one continuation is
normalised once if compositions are memoised on the pair (expression,
continuation). Memoisation is not implemented yet, and no benchmark
uses `share`.

## Results

The same families as in `docs/normal-forms.md`. Time is for normalising
both sides and comparing, with `vm_compute`, in seconds. "Size" is the
number of cells reachable from the result (cells built in total, in
brackets, where it differs).

Columns:

- **new:** `HNorm.hn_eq`;
- **layered:** the current decision, `LEval.nf_eq_t`;
- **tree:** the tree normal form, `LEval.tnorm`, the form of the original
  implementation.

"—" means not run, and "> 120" means stopped after 120 s.

| Family | Normaliser | 16 | 64 | 256 | 1024 |
|---|---|---|---|---|---|
| chain of substitutions, left- vs right-nested | new | — | 0.015 | 0.12 | 1.6 |
| | layered | — | 0.007 | 0.031 | 0.28 |
| | tree | 0.096 | > 120 | — | — |
| the same chain, labels sorted against the order of addition | new | — | 0.035 | 0.73 | 27.8 |
| | layered | — | 0.007 | 0.027 | 0.27 |
| | tree | 0.094 | > 120 | — | — |
| substitutions for one name | new | — | 0.004 | 0.017 | 0.13 |
| | layered | — | 0.009 | 0.026 | 0.23 |
| | tree | 0.064 | > 120 | — | — |
| an atom after each substitution | new | — | 0.003 | 0.013 | 0.12 |
| | layered | — | 0.006 | 0.017 | 0.15 |
| | tree | 1.1 | > 120 | — | — |
| weakenings of distinct names | new | — | 0.014 | 0.13 | 1.4 |
| | layered | — | 0.012 | 0.094 | 1.3 |
| | tree | 0.003 | 0.011 | 0.13 | — |
| one substitution under nested lifts | new | — | 0.058 | 0.77 | 15.2 |
| | layered | — | 0.11 | 2.2 | 90.7 |
| | tree | 0.023 | 0.12 | 2.2 | — |
| one simultaneous substitution | new | — | 0.009 | 0.11 | 1.5 |
| | layered | — | 0.007 | 0.015 | 0.12 |
| | tree | 0.005 | 0.006 | 0.063 | — |
| a term whose payload is the chain, then the chain | new | — | 0.016 | 0.19 | 2.4 |
| | layered | — | 0.063 | 0.77 | 10.9 |
| | tree | 0.19 | > 120 | — | — |
| a chain under nested lifts, then a substitution for each | new | — | 0.022 | 0.23 | 3.1 |
| | layered | — | 0.099 | 1.9 | 68.8 |
| | tree | 0.10 | > 120 | — | — |

Size of the new normal form, in cells reachable from the result (and
built in total, where that differs):

| Family | 64 | 256 | 1024 |
|---|---|---|---|
| chain, either nesting | 64 | 256 | 1024 |
| chain sorted against the order of addition | 2080 | 32896 | 524800 |
| substitutions for one name | 64 | 256 | 1024 |
| an atom after each substitution | 128 | 512 | 2048 |
| weakenings of distinct names | 64 | 256 | 1024 |
| nested lifts | 65 (4163) | 257 (65795) | 1027 (912577) |
| simultaneous substitution | 64 | 256 | 1024 |
| payload is the chain | 65 | 257 | 1025 |
| chain under nested lifts | 128 | 512 | 1525 (2051) |

**Reading the results.**

- **Every comparison was decided correctly.** The new normaliser
  answered `true` on every pair, as the other two do.
- **The new normaliser is quadratic, as predicted.**
  - *Worst case:* only the chain with labels sorted against the order
    of addition reaches the worst-case output size: `n(n+1)/2` cells.
    Its time at 1024 is 28 s.
  - *Nested lifts:* the reachable output stays linear, but `Θ(n²)`
    cells are built and dropped along the way. That is because each new
    step is inserted after all the earlier ones.
- **Against the layered form**, the new normaliser is:
  - *faster* where the layered form is cubic: nested lifts, terms whose
    payload is a chain, and substitutions under lifts. At 1024 steps
    that is 6 to 22 times faster;
  - *slower* where the layered form is linear: chains and wide
    substitutions, by 6 to 13 times at 1024;
  - *about 100 times slower* on the worst-case chain.
- **The tree form is exponential** on chains (either order), substitutions
  for one name, atoms between substitutions, payload chains and
  substitutions under lifts. It gives
  up before 64 steps on each. Where it has no terms to duplicate
  (weakenings, lifts, wide substitutions) it is about as fast as the
  others.
- **The new form covers more.** It handles labels the facts do not
  order, where the layered form gives up (`lcmp` returns `None`).

## Re-normalising the output

Tactics are often run on their own output, so each normaliser was also
timed on the result of normalising.

- **new:** `HNorm.renorm` takes the cells reachable from the two normal
  forms and rebuilds each one once, on a fresh table, with the same
  pushes as normalisation. In every run that finished, a third pass gave
  back the same normal form (it is idempotent).
- **layered:** the canonical layered words are read back as
  expressions, each segment as one context and non-empty payloads as
  compositions, and given to `LEval.nf_eq_t`. In every run the readback
  was equal to the original expression.

Time in seconds, with the first normalisation's time at 1024 for
comparison. "> 600" means the whole file, both normalisations
included, was stopped after 600 s.

| Family | Normaliser | 64 | 256 | 1024 | first time, 1024 |
|---|---|---|---|---|---|
| chain, either nesting | new | 0.004 | 0.054 | 0.73 | 1.6 |
| | layered | 0.006 | 0.028 | 0.23 | 0.28 |
| chain sorted against the order of addition | new | 0.15 | 5.5 | > 600 | 27.8 |
| | layered | 0.005 | 0.029 | 0.22 | 0.27 |
| chain in a random label order | new | 0.062 | 3.4 | > 600 | 13.9 |
| | layered | 0.002 | 0.084 | 0.16 | 5.4 |
| substitutions for one name | new | 0.000 | 0.003 | 0.050 | 0.13 |
| | layered | 0.004 | 0.026 | 0.22 | 0.23 |
| an atom after each substitution | new | 0.000 | 0.002 | 0.009 | 0.12 |
| | layered | 0.004 | 0.022 | 0.16 | 0.15 |
| weakenings of distinct names | new | 0.003 | 0.044 | 0.71 | 1.4 |
| | layered | 0.016 | 0.21 | 3.1 | 1.3 |
| nested lifts | new | 0.004 | 0.049 | 0.76 | 15.2 |
| | layered | 0.46 | 11.4 | 369 | 90.7 |
| simultaneous substitution | new | 0.004 | 0.056 | 0.67 | 1.5 |
| | layered | 0.000 | 0.006 | 0.070 | 0.12 |
| payload is the chain | new | 0.004 | 0.052 | 0.74 | 2.4 |
| | layered | 0.005 | 0.034 | 0.22 | 10.9 |
| chain under nested lifts | new | 0.009 | 0.10 | 1.3 | 3.1 |
| | layered | 0.006 | 0.031 | 0.22 | 68.8 |

The chain in a random label order, first normalisation (sizes as in
the size table):

| Normaliser | 64 | 256 | 1024 |
|---|---|---|---|
| new | 0.042 | 0.65 | 13.9 |
| new, cells reachable | 1069 | 17014 | 260393 |
| layered | 0.029 | 0.34 | 5.4 |

**Reading the results.**

- **Re-normalising is cheap for the new normaliser, except in the bad
  case.** Wherever the output is linear, the second pass takes 0.01 to
  1.3 s at 1024. That is less than the first pass, and for nested lifts
  it is 20 times less, because the discarded intermediates are not
  rebuilt.
- **The bad case gets worse.** The second pass on the worst-case chain
  is cubic: 5.5 s at 256, against 0.73 s the first time. At 1024 it did
  not finish.
- **A random label order is nearly as bad.** Its output is about `n²/4`
  cells (260393 at 1024, against 524800 for the worst order). That is
  what the inversion count predicts, so the bad case is the typical
  case for chains (next section).
- **The layered form's second pass is cheap on chains, but worse where
  it was already cubic.** It is cheap on chains and payloads, because
  its readback has one context per segment. On nested lifts it is
  4 times slower again, 369 s at 1024.
- **An explicit composition in a payload is expensive for the layered
  form.** A first readback wrote empty payloads as `AId ⨾ ·`. That made
  the simultaneous substitution 600 times slower (72 s at 1024, against
  0.07). The layered form pays a full composition for each payload
  that is a composition.

## Where the bad case comes from

**One form causes it.** Pushing a step costs the number of steps it walks
past, and those are the steps on known-distinct labels that sort before
it. Summed over a normalisation, that is the number of *inversions*
between the order steps are added in and the sorted order. This is
exactly insertion sort.

- *Time* is quadratic whenever there are many inversions.
- *Output size* is quadratic only when the intermediate words stay
  reachable as well. That happens when terms are normalised on top of
  the current word (a chain of substitutions with payloads) or when a
  lookup gets stuck in it.
- Nested lifts have the inversions without the reachable intermediates.
  So they are quadratic in time but linear in size.
- Re-normalising the worst case is cubic: each of the `n²/2` reachable
  cells is pushed again, and each push walks up to `n` steps.

**It is the typical case, not a rare one.** A random order of labels
has about `n²/4` inversions, like insertion sort on random input. The
order users introduce labels in has nothing to do with the facts
order, so random-looking orders are what to expect. The chain in a
random label order bears this out: about `n²/4` cells (above).

## What can be done about it

**A pre-pass does not help with size.** In this representation the
normal form of the worst-case chain *is* `n²/2` cells. The form is a
function of the meaning, so no order of work avoids building it. A
pre-pass that batches consecutive pushes which commute, and merges them
in, would fix time only where the intermediates are thrown away
(nested lifts).

**The sort direction is a free choice.** The proof that sorted words
are unique needs a transitive order whose comparability is "known
distinct". The reverse of the facts order is one too. Choosing the
direction that matches how labels are usually created would fix
one-directional patterns, but not random ones.

**An arbitrary order such as a hash is *not* allowed.** With
`d < a < b`, where `d` and `b` are not comparable, the words `b d a` and
`a b d` are both sorted and equal. Sorting needs the facts order (or
its reverse).

**The better fix is to change the representation, not the pivot.**

- Suppose the facts order is total on the labels in a stretch of word
  between barriers (atoms, and pairs of labels not known distinct). In
  a sorted word, adjacent steps on different labels are in increasing
  order, so all the steps on one label are together.
- The stretch is then exactly a **finite map from labels to the stack
  of steps on that label**. A push only touches its own label's stack:
  cancellation and absorption happen at the top of it.
- Any canonical map structure works, because the sort order is needed
  only for printing. A hash-consed binary trie keyed by the label's
  interned id has a shape that depends only on the map. Its depth is
  the length of the key, a worst-case bound rather than an expected
  one. This is the canonical trie of Appel and Leroy, "Efficient
  extensional binary tries", used in CompCert's `PTree`.
- The objections to hashed Cartesian trees in `docs/nf-design.md` §2
  were periodic words and bounds that are only expected. They do not
  apply. The keys are distinct labels, not positions in a sequence,
  and the bound is deterministic.
- On the worst-case chain, each push is one map insertion that copies
  one path. Time and size become `O(n log n)`.

**What this does not cover.** Stretches where the facts order is only
partial. A step on `h` can walk past steps on `a₁ … aₙ` that are all
below `h` but not comparable with each other. Their order is fixed,
so they are not a map. The Cartier–Foata normal form (levels of
pairwise-commuting steps, each level a map) is the natural
generalisation. Whether cancellation stays local in it is not yet
checked.

## How far a uniqueness proof is

Every approach needs the same three parts:

1. **The core lemma:** two different reduced sorted words differ in
   some consistent finite interleaved model. This is the blocked-match
   lemma of `docs/nf-design.md`, and the same lemma was left open for
   the layered form over interleaved models. The hard cases are steps
   kept apart by a label not known distinct (blocked matches) and
   stuck lookups. For these, the model has to make the unknown label
   overlap just enough to tell the words apart. `IFinite.v` gives the
   model constructions, but the lemma is not yet stated precisely in
   Coq.
2. **The algorithm produces reduced sorted words, and is sound.** This
   follows the pattern of the existing soundness proofs. The paper
   argument that edits never cascade does most of the preservation
   work.
3. **The storage is faithful.** Equal ids mean equal unshared words.

For the hash-consed list form, part 3 is a routine invariant of the
table, and the form is a plain word. That makes it the easiest
candidate for a first complete proof: prove part 1 for unshared words
and lift it through the table.

The map version adds trie canonicity, which is known and already
mechanised (CompCert). The locally-consistent-parsing version adds a
large verification effort for part 3.

None of them is close while part 1 is open.
