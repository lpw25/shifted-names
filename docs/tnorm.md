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

### 4. Adjustments only: a frame of targets per tail (fails)

Requirement: every shared definition is an adjustment (no fragments).

**The idea.** All the words with the same tail `X` (a *group*) share one
frame of targets. The distinct targets of the group's runs get
positions `0 … N−1` on the bound label, and a run `Δ` in front of `X`
prints as

```
Sh_N ⨾ R(Δ) ⨾ ⟦ ·ᴺ | X ⟧ ⨾ T_X
```

The four pieces:

- `Sh_N = ⟦ \ · ⟧ᴺ` moves the real bound variables past the frame.
- `R(Δ)` sends each label to its target's position. Its pieces commute,
  because their targets are bound variables the other pieces leave
  alone, so it is a tree of compositions following the trie.
- `⟦ ·ᴺ | X ⟧` is the tail lifted `N` times, so it leaves the frame
  alone.
- `T_X = ⟦ · := u₀; …; · := u_{N−1} ⟧` puts the targets in. It comes
  last, so the targets pass through nothing, and targets that can see
  the bound label are no problem.

**It is correct.** Checked with `hn_eq` (scratch test `GF.v`): a run of
three entries is printed this way and compared with the plain form.

| Case | Result |
|---|---|
| a target whose payload contains an atom, and a bound-variable target | true |
| tails: the identity, an atom, an atom then an entry whose target is `·₁`, a weakening of `·` then an atom | true for each |
| controls: wrong positions, or the tail not lifted | false |

**Its size looks fine.** Per group it costs `N` for `T_X`, `N` for the
lifted tail, and one definition per trie node for `R`.

**It is cyclic.** A frame shared by a group holds the targets of *all*
the group's runs, and those targets' payloads are often other words of
the same group. In a chain of substitutions, the word `W_k` is in the
same group (tail `⟦⟧`) as `W_{k+1}`, whose new target `u_{k+1}[W_k]` has
`W_k` as its payload. So `W_k`'s printed form refers to `T_X`, which
refers to `W_k`. Inlining the printed form did not terminate.

**Acyclic frames do not fix it.** A word may only use a frame whose
targets do not depend on it. So the frames have to be nested, one per
point in the dependency order. Nested frames run into one of two
problems:

- If they grow at the bottom, positions are stable, but the frames are
  lists sharing prefixes, which lists cannot do. Each frame costs its
  length, so the total is quadratic.
- If they grow at the top, they share suffixes, but every position
  moves when a target is added. Moving a piece's positions by `d` is
  either `d` lifts, or a shift that also moves the real bound variables
  passing through.

### Why adjustments alone do not suffice

Every construct that lets a target skip what comes after it acts on one
target or one variable at a time:

- an input entry `⟦ x := t | τ ⟧` lets one target skip `τ`;
- a lift `⟦ x | τ ⟧` lets one variable skip `τ`.

Composition sends targets through what follows. In a tree of pieces
that carry targets, at each node one side's targets must skip the other
side's substitutions. That costs the size of the other side, unless the
targets cannot see what they pass through.

In a persistent trie, a new version creates a node at each level of
its path. When such a node's skipped side is the new one, it pays that
size again, which is `Θ(n)` per insertion in the worst case.

**What is enough: a counted lift `⟦ ·ᵏ | σ ⟧`** (σ under `k` binders,
`k` a number). It is an adjustment, not a fragment. With it, everything
is constant size per trie node, using the bound label as the
interface:

```
⟦ Δ | X ⟧    = Ren(Δ) ⨾ ⟦ ·^|Δ| | X ⟧ ⨾ T(Δ)
T(A ; B)     = ⟦ ·^|A| | T(B) ⟧ ⨾ T(A)
Ren(A ; B)   = Ren(B) ⨾ Ren(A)
```

- **It is acyclic.** `T(node)` holds only the node's own targets, and a
  target's payload cannot contain the target's own entry.
- **It is correct.** Checked for `k = 1` and `k = 2`, where `⟦ ·ᵏ | σ ⟧`
  is written as nested lifts: `BL.v` and `BL2.v`.

**This does not meet the bound: reading it back is the problem.**
Normalised step by step, `T(node)` becomes a stack of `|node|` entries
on the bound label, and building those for every version is quadratic.
Recognising this shape in the reader does not help in general. The
same structure can be written in many other ways, by users or by other
tactics, and every variant the reader misses is quadratic. So the
bound cannot come from recognising a printing scheme.

The underlying mistake is that the output is not in the well-behaved
fragment of the spec (requirement 8: the output must itself be well
behaved). A trie printed as shared pieces uses a piece under many
different continuations: a node's left child is followed by different
right children in different versions. That holds for fragments, for
bound-label pieces with or without a counted lift, and for weakening
trees. The normaliser has no reason to read such sharing in
`O(n log n)`.

**What the spec allows.** Sharing where every use of a shared
adjustment has the same continuation (up to leading shifts). A
normaliser that memoises each shared adjustment with its continuation
reads that in time linear in its size, with no knowledge of how it was
produced. With that sharing, a printed normal form is a DAG of
sequences of front edits, each ending in a shared word:

- an entry `⟦ x := t | W ⟧`;
- a deletion `⟦ \ x ⟧ ⨾ W`;
- an atom `σ ⨾ W`.

So the trie can only be internal. Printing has to express each needed
word as a short edit of another needed word, or of a shared suffix:
the "edits from a base" approach of section 2.

**Small output is possible in principle.** The normaliser's own history
is such a structure: each word it builds is one edit of an earlier
one. That gives `O(n)` edits in total, for an input of size `n` in the
well-behaved fragment. What is missing is a **canonical** choice of the
structure (which word is an edit of which), computed in `O(n log n)`
and with `O(n log n)` total size.

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

Same families as `docs/hnorm.md`, normalising both sides and comparing,
with `vm_compute`. Times are in seconds.

Columns:

- **trie:** `TNorm`;
- **list:** `HNorm` after the fix to `stop`;
- **layered:** `LEval.nf_eq_t`.

"Second pass" is normalising the printed output again:

- trie: `tn_reread`, on a fresh table;
- list: `renorm`;
- layered: its readback.

Output size, one side:

- trie: printed definitions;
- list: reachable cells.

Every comparison was decided correctly. For the trie, every printed
output read back to the same ids on the normaliser's own table
(`tn_idem`), and to equal ids for both sides on a fresh table
(`tn_reread`).

At 1024:

| Family | first, trie | first, list | first, layered | second, trie | second, list | second, layered | size, trie | size, list |
|---|---|---|---|---|---|---|---|---|
| chain of substitutions | 0.60 | 0.20 | 0.28 | 1.67 | 0.043 | 0.23 | 7917 | 1024 |
| chain, labels sorted against the order of addition | **0.66** | 26.5 | 0.27 | **1.21** | 17.5 | 0.22 | **6962** | 524800 |
| chain, random label order | **1.03** | 8.4 | 0.50 | **1.96** | 3.6 | 0.17 | **11467** | 260393 |
| substitutions for one name | 0.52 | 0.13 | 0.23 | 0.62 | 0.040 | 0.22 | 2048 | 1024 |
| an atom after each substitution | 0.74 | 0.14 | 0.15 | 0.39 | 0.009 | 0.16 | 3072 | 2048 |
| weakenings of distinct names | 0.50 | 0.096 | 1.3 | 0.68 | 0.007 | 3.1 | 2048 | 1024 |
| one substitution under nested lifts | 1.05 | 14.4 | 90.7 | 0.47 | 0.032 | 369 | 2051 | 1027 |
| one simultaneous substitution | 0.63 | 0.15 | 0.12 | 0.50 | 0.006 | 0.070 | 2048 | 1024 |
| a term whose payload is the chain | 0.98 | 0.30 | 10.9 | 1.21 | 0.046 | 0.22 | 7920 | 1025 |
| a chain under nested lifts | 1.83 | 0.37 | 68.8 | 1.33 | 0.052 | 0.22 | 7928 | 1525 |

Scaling of the trie normaliser, first pass:

| Family | 64 | 256 | 1024 |
|---|---|---|---|
| chain of substitutions | 0.025 | 0.12 | 0.60 |
| chain, worst order | 0.025 | 0.13 | 0.66 |
| chain, random order | 0.041 | 0.16 | 1.03 |
| a chain under nested lifts | 0.094 | 0.44 | 1.83 |
| printed definitions, chain, random order | 446 | 2308 | 11467 |

**Reading the results.**

- **The quadratic case is gone.** On the worst-order chain the trie
  normaliser is 40 times faster than the list (0.66 s against 26.5 s),
  and its output is 75 times smaller (6962 definitions against 524800
  cells). On a random order it is 8 times faster and 23 times smaller.
  Both passes now grow like `n log n` on every family.
- **No family is slow.** The first pass is 0.5 to 1.8 s at 1024 on
  every family, and so is the second. The layered form's cubic cases
  (nested lifts, payload chains, chains under lifts) take 1 to 2 s
  instead of 11 to 91 s, and 0.5 to 1.3 s instead of up to 369 s for
  the second pass.
- **The price is a constant factor.** Where the list is linear, the trie
  is 3 to 5 times slower on the first pass and prints 1.5 to 8 times
  more definitions.
  - *Time:* the trie is not path-compressed. Each push rebuilds a path
    of about 20 nodes (the key length for two-letter labels), where
    the list rebuilds about one cell.
  - *Size:* on chains, each payload word is a different trie, so each
    step adds a path's worth of binary nodes. That is the `log n` in
    `n log n`, about 8 definitions per step at 1024.
- **The second pass is slower than the list's.** Reading a fragment
  rebuilds, for each printed node, the path from the root of the trie
  down to it. The list's second pass on a linear output is nearly free,
  because every cell goes straight to the front.

**What would improve it, in order of expected gain:**

1. **A path-compressed trie (Patricia).** Each push would build
   `O(log n)` nodes instead of 20, and the printed form would not
   change.
2. **Reading fragments at their depth.** If a printed trie node carried
   its bit position, the reader could rebuild it in `O(1)`, without the
   path from the root.
3. **Label atoms with facts.** These could use Cartier–Foata levels (as
   noted in `docs/hnorm.md`). They are barriers for now, which makes
   this normaliser incomplete there.
