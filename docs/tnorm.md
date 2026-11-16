# Tries: printing them, and a normaliser built on them

Follows `docs/hnorm.md`. The aim is a normal form whose quadratic case
(chains of substitutions whose labels are not added in sorted order)
becomes `O(n log n)`, together with a printed form that keeps that size
and can be read back at the same cost.

Notation: `a ⨾ b` runs `a` first. `ACompose a b` runs `b` first, so
`a ⨾ b` is `ACompose b a`.

## Printing a trie

A *run* is a stretch of steps on mutually ordered labels between
barriers. It is stored as a trie from labels to the stack of steps on
each label. Printing it means printing each trie node once, as a
shared piece that does not depend on what the node sits in front of.
Three ways were tried.

### 1. The bound label as the interface

`⟦ Δ | τ ⟧ = Ren(Δ) ⨾ τ ⨾ T(Δ)`, where:

- `Ren(Δ)` sends each label of `Δ` to a position on the bound label;
- `T(Δ)` substitutes the targets for those positions.

`Ren` pieces concatenate by plain composition, because their targets
are variables that should be shifted. The difficulty is the `T` pieces.
`T(A) ⨾ T(B)` sends `A`'s targets through `T(B)`'s substitutions. That
is harmless only if the targets cannot see the bound label.

**A target can see the bound label when:**

1. it is a bound variable `·ᵢ` of the output scope;
2. its payload contains an adjustment atom, whose outputs may mention
   `·`;
3. it is a stuck lookup.

Checked with `hn_eq` (scratch test `BL2.v`):

| Check | Result |
|---|---|
| `T(a ; b) = T(a) ⨾ T(b)`, plain targets | true |
| the same, payloads containing an atom | **false** |
| the same, a bound-variable target | **false** |
| `T(a ; b) = ⟦ · \| T(b) ⟧ ⨾ T(a)`, both cases | true |
| the sensitive piece placed last: `T(b ; a) = T(b) ⨾ T(a)` with only `a` sensitive | true |

So when both children are sensitive, the second child has to be lifted
over the first child's size: `T(A ; B) = ⟦ ·^|A| | T(B) ⟧ ⨾ T(A)`.

**This blows up.** In a persistent trie, an insertion creates a new
node at each level of its path. A new node whose second child is new
needs a fresh chain of `|A|` lifts. On a random insertion order that is
`Θ(n)` per insertion, so `Θ(n²)` overall. It is the common case: in a
chain of substitutions followed by an atom, every payload contains the
atom.

**A counted lift `⟦ ·ᵏ | σ ⟧` as one constructor would fix the size,
but not the reading back.** The normal form of `⟦ ·ᵏ | σ ⟧` has `Θ(k)`
steps when `σ` touches `·`, so a normaliser reading the printed output
step by step pays the `Σ k` again. It would have to recognise the
encoding and rebuild the trie directly.

### 2. Edits from a base

Within a run, contexts express edits anywhere in `O(1)`, with existing
constructors:

- **insertion:** `⟦ x := t | W ⟧`. The target is in the output scope
  of the whole adjustment, so it is not sent through `W`;
- **deletion:** `⟦ \ x ⟧ ⨾ W`.

Reading back is linear, memoising on shared references. The problem is
choosing, canonically, which word each word is an edit of:

- **Rules local to one word collapse into the sorted list.** An example
  is "the word without its last key", which is quadratic on the
  worst-order chain.
- **A minimum spanning tree over the needed words in edit distance is
  canonical, but costs.** With canonical tie-breaking it depends only
  on the set of words, but it needs a distance per pair: quadratic in
  the number of words, which is `n` on a chain.
- **The optimum is worse still.** Allowing intermediate words that are
  not needed is a Steiner tree, NP-hard in general.

I did not find a cheap canonical rule.

### 3. Context fragments (a new constructor): this works

A sort of *fragments*, the steps of a context without its tail:

```
Δ ::= x := t | \ x | Δ₁ ; Δ₂ | a shared fragment
```

There is one adjustment form, `⟦ Δ | τ ⟧`. Its properties:

- **No side conditions.** `;` is concatenation, so it means the same
  for any labels.
- **No context dependence.** Targets are in the output scope of the
  whole adjustment, as for an input entry, so a fragment means the same
  wherever it is used.
- **Constant size per node.** A trie node prints as
  `Δ_left ; Δ_right`, a stack cell as `step ; Δ_rest`, a run as
  `⟦ Δ | τ ⟧`.
- **Cheap to read back.** A fragment is read into a trie by union,
  memoised per shared fragment. On printed output the two sides of a
  union have disjoint keys, so it costs `O(key length)` per node.

In the context-form syntax, this means letting a context's entry list
be named with `share` and spliced into other entry lists.

## The trie normaliser (`Core/TNorm.v`)

### The form

A word is one of:

- empty;
- a **run** (a trie) in front of a word that does not start with a
  run;
- a **barrier step** in front of a word. Barriers are adjustment atoms,
  and steps on label atoms.

The trie is keyed by the label's bits, most significant first. Keys:

- a concrete label is `0` followed by its characters, each as `1` and
  8 bits, then `0`;
- the bound label is `1`.

So the trie's in-order is the label order: string order, then the
bound label. That respects requirement 7 of the spec: the printed order
comes from the order of the labels.

There are no empty branches, so the shape depends only on the keys.
Stack cells, trie nodes and words are all hash-consed, so equal normal
forms have equal ids.

The algorithm is `HNorm`'s, with the walk replaced:

- a step on a ground label goes straight to its label's stack;
- it cancels against the top of the stack, is absorbed by it, or is
  pushed onto it.

### Limits of this version

- **Label atoms are barriers.** Steps on label atoms never pass other
  steps, even when facts would allow it. This is sound but incomplete:
  of the 37 sanity checks run against `HNorm`, the one that needs a fact `x < y` between
  label atoms (the substitution lemma) is answered `false`.
- **The trie is not path-compressed.** Its depth is the key length, 20
  for the two-letter labels of the benchmarks, so each push builds
  about 20 nodes. A path-compressed (Patricia) trie would build
  `O(log n)`.
- **Absorption inside a fragment is conservative.** When the reader
  builds a fragment's stacks, absorption checks that would need the
  tail are answered "no". Printed fragments are already reduced, so
  this never matters on printed output, but it would for hand-written
  fragments.

### The printer and the reader

`print` writes one definition per reachable word, stack cell and
binary trie node. Unary trie nodes are skipped. `nx` normalises the
printed syntax, memoising each reference with its continuation.

- `tn_reread` reads the printed output on a fresh table.
- `tn_idem` reads it on the normaliser's own table and checks that the
  same ids come back.

## Results

RESULTS
