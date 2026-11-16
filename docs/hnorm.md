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
labels that sort before `h`. It stops at the first step on `h`, on a
label not known distinct from `h`, on a label that sorts after `h`, or
at an atom.

- **Stopping at a label after `h` is safe.** In a sorted word, no step
  on `h` can come after such a step while every step in between is on
  a label known distinct from `h`. This is the argument that sorted
  words are unique.
- A weakening that reaches an entry on `h` cancels with it.
- An entry that reaches a weakening on `h` is absorbed when its value
  is what the rest gives `h₀`.
- Otherwise the step goes where it stopped. That is its sorted
  position, so the walk costs exactly the number of steps it is
  inserted after.

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
both sides and comparing, with `vm_compute`, in seconds. The "new"
rows are after the fix to `stop` described under "Why the second pass
was cubic". "Size" is the
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
| chain of substitutions, left- vs right-nested | new | — | 0.004 | 0.019 | 0.20 |
| | layered | — | 0.007 | 0.031 | 0.28 |
| | tree | 0.096 | > 120 | — | — |
| the same chain, labels sorted against the order of addition | new | — | 0.021 | 0.61 | 26.5 |
| | layered | — | 0.007 | 0.027 | 0.27 |
| | tree | 0.094 | > 120 | — | — |
| substitutions for one name | new | — | 0.006 | 0.016 | 0.13 |
| | layered | — | 0.009 | 0.026 | 0.23 |
| | tree | 0.064 | > 120 | — | — |
| an atom after each substitution | new | — | 0.004 | 0.013 | 0.14 |
| | layered | — | 0.006 | 0.017 | 0.15 |
| | tree | 1.1 | > 120 | — | — |
| weakenings of distinct names | new | — | 0.003 | 0.012 | 0.096 |
| | layered | — | 0.012 | 0.094 | 1.3 |
| | tree | 0.003 | 0.011 | 0.13 | — |
| one substitution under nested lifts | new | — | 0.044 | 0.65 | 14.4 |
| | layered | — | 0.11 | 2.2 | 90.7 |
| | tree | 0.023 | 0.12 | 2.2 | — |
| one simultaneous substitution | new | — | 0.003 | 0.012 | 0.15 |
| | layered | — | 0.007 | 0.015 | 0.12 |
| | tree | 0.005 | 0.006 | 0.063 | — |
| a term whose payload is the chain, then the chain | new | — | 0.004 | 0.026 | 0.30 |
| | layered | — | 0.063 | 0.77 | 10.9 |
| | tree | 0.19 | > 120 | — | — |
| a chain under nested lifts, then a substitution for each | new | — | 0.007 | 0.029 | 0.37 |
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
  - *Worst case:* only the chains whose labels are not added in sorted
    order go beyond linear output. Sorted against the order of
    addition: `n(n+1)/2` cells, 26.5 s at 1024. In a random order:
    about `n²/4` cells, 14.4 s.
  - *Nested lifts:* the reachable output stays linear, but `Θ(n²)`
    cells are built and dropped along the way, 14.4 s at 1024. That is
    because each new step is inserted after all the earlier ones.
- **Against the layered form**, the new normaliser is:
  - *about as fast or faster* on every family with linear output: 0.1
    to 0.4 s at 1024. The layered form takes 0.12 to 1.3 s where it is
    linear (it is slightly faster only on the simultaneous
    substitution: 0.12 s against 0.15 s), and 11 to 69 s where it is
    cubic (payload chains, substitutions under lifts);
  - *6 times faster* on nested lifts (14 s against 91 s), even though
    it builds quadratically many cells there;
  - *slower* on chains whose labels are not added in sorted order:
    about 100 times on the worst order, 3 times on a random order.
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
comparison. The two quadratic chains at 1024 were timed inside one
evaluation with the first pass, by subtraction (see below).

| Family | Normaliser | 64 | 256 | 1024 | first time, 1024 |
|---|---|---|---|---|---|
| chain, either nesting | new | 0.000 | 0.012 | 0.043 | 0.20 |
| | layered | 0.006 | 0.028 | 0.23 | 0.28 |
| chain sorted against the order of addition | new | 0.015 | 0.42 | 17.5 | 26.5 |
| | layered | 0.005 | 0.029 | 0.22 | 0.27 |
| chain in a random label order | new | 0.007 | 0.16 | 3.6 | 14.4 |
| | layered | 0.002 | 0.084 | 0.16 | 5.4 |
| substitutions for one name | new | 0.000 | 0.005 | 0.040 | 0.13 |
| | layered | 0.004 | 0.026 | 0.22 | 0.23 |
| an atom after each substitution | new | 0.000 | 0.002 | 0.009 | 0.14 |
| | layered | 0.004 | 0.022 | 0.16 | 0.15 |
| weakenings of distinct names | new | 0.000 | 0.002 | 0.007 | 0.096 |
| | layered | 0.016 | 0.21 | 3.1 | 1.3 |
| nested lifts | new | 0.000 | 0.003 | 0.032 | 14.4 |
| | layered | 0.46 | 11.4 | 369 | 90.7 |
| simultaneous substitution | new | 0.000 | 0.001 | 0.006 | 0.15 |
| | layered | 0.000 | 0.006 | 0.070 | 0.12 |
| payload is the chain | new | 0.000 | 0.005 | 0.046 | 0.30 |
| | layered | 0.005 | 0.034 | 0.22 | 10.9 |
| chain under nested lifts | new | 0.001 | 0.007 | 0.052 | 0.37 |
| | layered | 0.006 | 0.031 | 0.22 | 68.8 |

The chain in a random label order, first normalisation (sizes as in
the size table):

| Normaliser | 64 | 256 | 1024 |
|---|---|---|---|
| new | 0.041 | 0.59 | 14.4 |
| new, cells reachable | 1069 | 17014 | 260393 |
| layered | 0.029 | 0.34 | 5.4 |

**Reading the results.**

- **Re-normalising is cheap for the new normaliser.** Wherever the
  output is linear, the second pass takes 0.006 to 0.05 s at 1024. That
  is 3 to 20 times less than the first pass, and for nested lifts 450
  times less, because the discarded intermediates are not rebuilt.
- **The bad case is `n² log n` on the second pass too:** 17.5 s at 1024
  for the worst order, 3.6 s for a random order. Before the fix below
  it was cubic (5.5 s at 256, and it did not finish at 1024).
- **A random label order is nearly as bad as the worst.** Its output is
  about `n²/4` cells (260393 at 1024, against 524800 for the worst
  order). That is what the inversion count predicts, so the bad case
  is the typical case for chains (see "Where the bad case comes from").
- **The layered form's second pass is cheap on chains, but worse where
  it was already cubic.** It is cheap on chains and payloads, because
  its readback has one context per segment. On nested lifts it is
  4 times slower again, 369 s at 1024.
- **An explicit composition in a payload is expensive for the layered
  form.** A first readback wrote empty payloads as `AId ⨾ ·`. That made
  the simultaneous substitution 600 times slower (72 s at 1024, against
  0.07). The layered form pays a full composition for each payload
  that is a composition.

### Why the second pass was cubic, and the fix

On re-normalisation every step is already in sorted position, so the
insertion walk (`sorted_at`) is 0 for every cell. Counting the other
walks over the cells of the worst-case chain:

| n | cells | `stop` walk | insertion walk | payload scans in `clean` |
|---|---|---|---|---|
| 64 | 2080 | 43680 | 0 | 43680 |
| 128 | 8256 | 349504 | 0 | 349504 |
| 256 | 32896 | 2796160 | 0 | 2796160 |

Both are `n³/6`. Neither comes from the form; both were implementation
waste:

- **`stop` walked to the end of the stretch of known-distinct steps**,
  looking for a step on the same label to cancel with. It now stops at
  the first label that sorts after `h`. That is safe in a sorted word
  (see the algorithm), and it makes the walk equal to the insertion
  walk.
- **`clean` re-scanned a payload at every cell holding the term.** In
  the worst-case chain, `n²/2` cells hold `n` terms. The cleaned
  payload is now memoised by the payload's id.

After the fix, every cell costs one bucket scan in the hash-cons table
(about `1.5 n²` in total) and finite-map operations of depth `log n`.
So both passes are `Θ(n² log n)` on the worst-case chain, one
`log n` above its output size.

| Worst-case chain | 64 | 256 | 1024 |
|---|---|---|---|
| second pass, before | 0.15 | 5.5 | > 600 |
| second pass, after | 0.015 | 0.42 | 17.5 |
| first pass, after | 0.021 | 0.61 | 26.5 |

At 1024 the second pass was timed inside the same evaluation as the
first, by subtracting (47.4 s − 29.9 s). Saving a 525k-cell normal form
as a Coq definition costs more than either pass, and that is what had
timed out.

The fix to `stop` also helps the first pass wherever there is a long
stretch of known-distinct labels. The chain in addition order went
from 1.6 s to 0.20 s at 1024.

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

## The trie as a term

**Why the current constructors cannot share a trie node.** A word
prints as steps in front of the identity: `⟦ x := t | τ ⟧`,
`⟦ \ x ⟧ ⨾ τ` and `σ ⨾ τ`. The only thing `share` can name is a whole
adjustment, which is a step sequence *together with its tail*. So
`share` can only share suffixes, and the hash-consed linked list is
exactly what it can print. A trie node is a set of steps *without* the
tail: the left subtree, one label's stack and the right subtree. It
sits in front of different things in different words.

**An encoding with what exists costs too much.**
`⟦ x := t | τ ⟧` is `τ` lifted over `x`, then `⟦ x := t ⟧`. A trie node
could therefore print as one child lifted over every label of the
other child. That is `O(n log n)` lift constructors over the whole
trie, none of them shareable. Nested lifts are also the slowest thing
for both normalisers to read back.

**The constructors that would help: shareable step sequences.** A new
sort `Δ` of *context fragments*, the steps of a context without its
tail:

```
Δ ::= ∅                (no steps)
    | x := t           (an input entry)
    | \ x              (a weakening)
    | Δ₁ ; Δ₂          (Δ₁'s steps, then Δ₂'s)
    | a shared fragment
```

There is one new adjustment form, `⟦ Δ | τ ⟧`: `Δ`'s steps in front of
`τ`. Notes on this sort:

- **`;` is plain concatenation of steps.** It needs no side condition.
  Steps on one label keep their order, so it means the same for any
  labels. The normaliser only ever joins fragments on known-distinct
  labels, but the API does not need to know that.
- **It is first order.** A target in an entry is in the output scope of
  the whole adjustment and is not passed through the tail. So a
  fragment means the same whatever it is put in front of: a list of
  steps, not a function of the tail.
- **The existing context forms are special cases.** `⟦ x := u; y := v | τ ⟧`
  already has an entry list. What is new is naming a fragment once and
  splicing it into several entry lists.

**Printing a normal form.**

- A word is a list of *runs*. Each run is a stretch of steps on
  mutually ordered labels, and the runs are separated by barriers:
  atoms, and steps on labels not known distinct. The list prints as
  now, `⟦ Δ_run | barrier ⨾ ⟦ Δ_run' | … ⟧ ⟧`, with `share` on
  suffixes.
- Each trie node prints as a shared fragment
  `Δ_node = Δ_left ; Δ_stack ; Δ_right`, where `Δ_stack` holds the
  steps on the node's label.
- Payloads name whole words, and stuck lookups `y⟨N⟩` name suffixes
  starting at a barrier. Both are shareable adjustments already.

**Reading it back.** Fragments can be memoised by identity like
adjustments, so a printed trie is rebuilt node by node. Re-normalising
printed output stays linear in its size.

**Canonical across tactic calls.** `names; reflexivity` compares the
printed terms, so the trie's shape must not depend on a table's
history: interned ids will not do. The key has to be a fixed
injective encoding of the label expression, such as its constructor
and string bits. A path-compressed binary trie (Patricia tree) on that
encoding has a shape that depends only on the set of keys. Its depth
is at most the key length and at most the number of keys. Key order
is unrelated to the facts order, which is fine because steps on
known-distinct labels commute.

- *Caveat:* abstract labels are keyed by their atom index from
  reification. The shape then depends on that indexing, as it does for
  any reflexive tactic. Both sides of one goal share an indexing.

**Partial orders.** Where the facts order only partly orders the labels
of a stretch, runs are shorter, and steps that walk past several runs
still cost one step per run. The Cartier–Foata form (levels of
pairwise-commuting steps, each level a trie) is the candidate
generalisation, not yet checked.

### Bound labels as the interface

**Later finding:** this works only for targets that cannot see the
bound label, and the new constructor above is needed after all. See
`docs/tnorm.md`, "Printing a trie".

The bound label `·` is known distinct from every named label, so it
can carry the interface between pieces. (Below, `a ⨾ b` runs `a` first. `ACompose a b` runs `b` first,
so `a ⨾ b` is `ACompose b a`.)

For a fragment `Δ` with `k` entries, let `pos(x)` be the position of
`x`'s entry, and define:

- `Ren(Δ)`: each entry `x := t` becomes `x := ·_pos(x)`, weakenings
  are kept, and the tail is `⟦ \ · ⟧ᵏ`. It moves `Δ`'s inputs onto
  bound positions and shifts the bound label up by `k`.
- `T(Δ) = ⟦ · := t₀ ; … ; · := t_{k−1} ⟧`: the targets, in position
  order, on the bound label.

Then, when the tail `τ` does not touch the bound label,

```
⟦ Δ | τ ⟧ = Ren(Δ) ⨾ τ ⨾ T(Δ)
```

Both pieces concatenate by plain composition, with positions local to
each piece:

```
Ren(A ; B) = Ren(B) ⨾ Ren(A)        T(A ; B) = T(A) ⨾ T(B)
```

`Ren(B) ⨾ Ren(A)` puts `A`'s positions first. `T(A)`'s entries are
sent through nothing, and `T(B)`'s named targets pass through `T(A)`
unchanged. So a trie node prints as **two shared adjustments of
constant size**, `Ren(node)` and `T(node)`, built from its children's.
Checked with `hn_eq` on two entries (scratch test `BL.v`):

| Check | Result |
|---|---|
| `⟦ x := u; y := v \| τ ⟧ = Ren ⨾ τ ⨾ T`, for `τ` = `⟦⟧`, a substitution on `z`, a weakening on `z` | true |
| the same with the composition reversed | false |
| `Ren(x ; y) = Ren(y) ⨾ Ren(x)` | true |
| `T(x ; y) = T(x) ⨾ T(y)` | true |
| `τ` an atom, a lift of an atom, or a substitution whose target is `·₀` | false |
| the last two, with `τ` lifted over `·` twice | true |

**When the tail does touch the bound label** (atoms, or targets that
mention `·`), it has to be lifted over `·` `k` times. The lifts nest,
so `lift^{k+1} τ = ⟦ · | lift^k τ ⟧`. All the words that share a tail
then share one chain of lifts, as long as the longest run in front of
that tail.

**Reading it back is the open part.** The normaliser sees `T(root)` as
a stack of `n` entries on `·`, and `Ren(root)` as `n` lookups into it.
Done step by step, that is a lookup of depth up to `n` for each entry,
so quadratic again. It needs either a stack on `·` with indexed
lookup, or recognition of the pattern `Ren(Δ) ⨾ τ ⨾ T(Δ)` so that it
rebuilds `Δ` directly. A dedicated fragment constructor would make
this trivial, which is the trade-off against needing no new
constructors.

## Edits from a base

**Contexts make deep edits shallow.** Within a run of steps on
known-distinct labels:

- inserting an entry anywhere is a push at the front, `⟦ x := t | W ⟧`,
  because it commutes into place;
- deleting the entry on `x` is a weakening at the front,
  `⟦ \ x ⟧ ⨾ W`, because it commutes to the entry and cancels.

The sorted list cannot use either fact, which is why it has to copy.

**On the worst-case chain this is linear with existing constructors.**
Each payload word `W_k` is the root `W_n` with the entries `k+1 … n`
deleted. So `W_k = D_k ⨾ W_n` with `D_k = ⟦ \ x_{k+1} ⟧ ⨾ D_{k+1}`, a
chain of weakenings sharing suffixes, `O(n)` in all.

**The hard part is canonicity, not size.** The printed form must be a
function of the meaning, because `reflexivity` compares printed terms.
So "which word is each word an edit of" must be chosen canonically,
not taken from the history of the normalisation.

- *One base for everything* (a median) is not enough. On the chain,
  edits from any single base add up to `Θ(n²)`. The edits have to
  share with each other.
- *Each word as an edit of another needed word* is a spanning tree in
  edit space. A minimum spanning tree with canonical tie-breaking is
  a function of the set of needed words, and on the chain it is the
  chain itself. Done naively it costs a comparison per pair of needed
  words. Optimal sharing (Steiner points that are not needed words)
  is NP-hard in general.
- Edits reach only into the first run. Below a barrier the word has to
  be rebuilt up to the barrier, so the units are runs, with suffix
  sharing between them as now.

**How this relates to the trie.** A persistent canonical trie *is* a
representation by edits: two words one edit apart share all but
`O(log n)` nodes. Its canonicity is free, because its shape is a
function of its content, but an edit costs `O(log n)` instead of
`O(1)`. Explicit edit scripts cost `O(1)` an edit, but need a
canonical choice of base. A combination is possible: tries internally
to decide equality, and edit scripts, chosen from the tries, for
printing.

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
