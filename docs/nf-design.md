# A normal form built from contexts, composition and sharing

A fresh start, designed together. Nothing here is settled. It records
the ideas agreed so far, a worked example, and an analysis of what
works and what does not.

## The constructs

Adjustments are built from three things:

- **context forms:** `⟦ I | Γ \ O | Γ[σ] ⟧`;
- **composition:** `a ⨾ b` is `a`, then `b`;
- **sharing:** `share r := a in b`.

One extension is needed. An output variable may carry a payload, just
as a term does. `y⟨N⟩` means "the output variable `y`, sent through
`N`". It is how `apply_var` is written.

## The ideas

1. **Maximal sharing.** Sharing is found while the normal form is
   built (hash-consing). In principle every `share` could be inlined,
   but that is expensive. Shared adjustments are kept to the side, so
   that adjustments used *linearly* do not make the algorithm
   exponential.
2. **Right to left.** Compositions are written sequentially and
   processed from the right. Normalise the piece applied second, then
   put the piece applied first on top of it.
3. **Post-composition pushes into the output context.** In
   `⟦ I | Γ \ O | Γ[σ] ⟧ ⨾ N`, `N` meets `O`: `O`'s entries are the
   variables `N` receives. Each output entry `y` becomes `y⟨N⟩`, and the
   tail `Γ[σ]` has `N` applied after it. Through a `share` for `N`
   nothing is duplicated. `I` is untouched; its entries still name
   slots of `O`. Composition is thereby reduced to sharing, and what
   remains is to normalise context forms with payloads on their outputs.
4. **Sorting.** In input and output contexts, entries on labels known
   to be distinct are sorted into the order the facts give them.
   Entries on labels not known to be distinct stay where they are.
5. **Tail expansion.** A context form in a tail is expanded into the
   surrounding context form.

## Normalising a context with payloads on its outputs

**Matching.** `N`'s input context meets the `y⟨N⟩` entries and the
tail.

- An input entry of `N` whose variable is an output `y` of the
  context is matched with it. The slot's value becomes that entry's
  target, and the entry leaves `N`.
- An input entry whose variable is a tail variable is expanded into
  the surrounding input context.
- An entry can do neither when it is on a label not known to be
  distinct from the outputs it would have to get past. Then the match
  is **blocked**, and the payload stays: `y⟨N⟩`, with `N` shared.

**Lookups.** A slot value `y⟨N⟩` is pushed into `N` as far as it goes.

- It passes entries on labels known to be distinct from `y`.
- It stops at an entry that takes `y` (the value is that entry's
  target).
- Otherwise it stops at the first entry on a label not known to be
  distinct, or at an atom.

**Slots.** Several input entries may name one slot, and that is where
merges show. Two slots with the same value are one slot. A slot no
input names may be dropped, or kept (see below).

**Absorption.** An input entry whose slot's value is what the tail
gives that input anyway is the identity, and is removed. The identity
renaming `⟦ x as a | Γ \ x as a | Γ ⟧ = ⟦⟧` is an instance.

**Payloads of terms.** A term `u⟨ρ⟩` in a slot becomes `u⟨ρ ⨾ N⟩`.
This is a composition, normalised recursively and memoised on the pair
`(ρ, N)`. A payload with no payload atom observes only named variables,
so its bound-label part must be removed canonically.

**Atoms and lifts.**

- A tail ending in an atom keeps it: `Γ[σ ⨾ M]`, with `M` the normal
  form after the atom.
- A lift `⟦ x | σ ⟧` is `⟦ x \ x | Γ[σ] ⟧`: the lifted input goes to an
  output, which then receives the payload of whatever comes after.

## A worked example: a blocked weakening

`⟦ \ x ⟧ ⨾ N`, with `N = ⟦ y := u ⟧` and `x`, `y` not known to be
distinct.

1. **Push** `N` into the output context:
   `⟦ | Γ \ x⟨N⟩ | Γ⟨N⟩ ⟧`.
2. **Try to expand `N`.** Its one input entry, `y := u`, takes `y₀` of
   `N`'s input. That `y₀` is the output `x` when `y₀ = x₀`, and a tail
   variable otherwise. Which one depends on the model, so the entry
   can be neither matched nor expanded. Both `x⟨N⟩` and `Γ⟨N⟩` stay,
   with `N` shared. The normal form is the composition itself, written
   with payloads.
3. **What `x⟨N⟩` records** is what `N` does at `x₀`: exactly the
   information that no input of `⟦ \ x ⟧ ⨾ N` can reach.
   - **When `N`'s first entry is on `x` itself** (among entries on
     labels not known to be distinct from `x`), matching consumes it,
     and the hidden information disappears with it. That is correct:
     `⟦ \ x ⟧ ⨾ ⟦ x := t | M ⟧ = M`.
   - **When the match is blocked**, as here by `y`, what `N` does at
     `x₀` is visible in other models. In this example `u` appears at
     `y₀` whenever `y₀ ≠ x₀`.

So no special rule is needed for slots no input names. Keeping or
dropping `x⟨N⟩` is the same, because it is determined by `Γ⟨N⟩`,
which contains `N`. This rests on the lemma below.

> **Blocked-match lemma (to prove).** When a match is blocked, `N` is
> determined by what the whole form does in every model.

## Analysis

### Relation to the old tree normal form

This is very close to the *tree* normal form of `docs/normal-forms.md`
(`Core/Normal.v`, `Core/Unique.v`), with a table for sharing.

- **What the tree form was.** A word of segments and lifted atoms.
  Every term is in the last segment, and a term's payload holds
  everything that happens to its names afterwards, atoms included.
- **Compared with this design.** Pushing `N` into outputs and terms
  makes every payload hold "everything after", and expanding tails
  flattens segments. That is the tree form.
- **What was proved.** The tree form is canonical: `nf_unique` and
  `tnorm_complete`, in one interpretation with distinct labels. Its
  problem was size. Unshared, a chain of `n` substitutions has a tree
  of size `2ⁿ`.
- **What `docs/literature-review.md` found.** It looked at exactly
  "the tree form plus maximal sharing" ("Correction: the proposal is
  not linear") and found that it is not linear. Your memory is right:
  canonical, but the wrong asymptotics. The reason is next.

### Problem: flattening loses compositions

Take a chain of substitutions on labels the facts order,

```
⟦ x₁ := u₁ ⟧ ⨾ ⟦ x₂ := u₂ ⟧ ⨾ … ⨾ ⟦ x_L := u_L ⟧
```

with `x_L < … < x₂ < x₁`, the reverse of the composition order.

- **Building it.** Right to left, step `k` gives
  `N_k = ⟦ x_k := u_k⟨N_{k+1}⟩ ; … ; x_L := u_L ⟧`, flattened and
  sorted.
- **Every suffix is a node.** `u_k`'s payload is `N_{k+1}`, so every
  suffix `N_{k+1}` must exist as its own node.
- **Sorting puts the new entry at the end.** With this order the new
  entry `x_k` comes last. A list shares a suffix, not a prefix, so
  `N_k` cannot reuse `N_{k+1}`'s entries.

The total is `Θ(L²)` for an input of size `O(L)`, with no `share` in
the input. That breaks requirement 8 of `docs/normaliser-spec.md`.

The cause is the combination of three ideas: expanding tails
(flattening), sorting, and payloads that are explicit references to
suffixes. The layered form kept compositions, letting a term's payload
be "the rest of the line" implicitly. That is why it was linear.

**Possible fixes.**

- **Share contexts by structure.** Store a context so that adding one
  entry rebuilds only `O(log L)` nodes wherever it lands, in a
  structure whose shape is canonical.
  - *Concrete labels:* tries keyed by label have a canonical shape,
    as in `Core/Repr.v`.
  - *Label atoms:* they have no keys. A run of entries on pairwise
    known-distinct labels is totally ordered by the facts. A treap
    whose priorities are a hash of the label has a canonical shape,
    but its bounds are only expected bounds.
  - *Labels not known to be distinct:* their order matters, so they
    cannot go in such a structure at all.
- **Let the printer fold tails back.** Keep flat contexts internally,
  but print `N_k` as `⟦ x_k := u_k⟨N_{k+1}⟩ | N_{k+1} ⟧` when it is
  `N_{k+1}` plus one entry. That is a valid adjustment, since entries
  on known-distinct labels commute. It is canonical if the choice is a
  function of the graph.
  - *Printed size:* this fixes it.
  - *Internal size:* it does not fix this, and nor does it fix the
    time to build the nodes.

### What definitely works

**Tail expansion never gets stuck.** In `⟦ I | Γ \ O | Γ[C] ⟧` with
`C` a context form:

- `C`'s inputs consume what is left after `I`;
- `C`'s outputs sit outside `O`.

In steps, every entry still comes before every weakening. So the
result is always one context form, and blocking can only appear where
an `N` is attached to outputs.

**Sorting gives a unique representative.** Call a sequence *sorted*
when no two adjacent entries are on known-distinct labels in the wrong
order. Two sorted sequences that differ only by swapping adjacent
entries on known-distinct labels are equal.

The proof uses the fact that "known distinct" means "comparable in a
transitive order". Suppose `w₁ = a w₁'` and `w₂ = b w₂'` with `a ≠ b`.

1. **Where `a` sits in `w₂`.** Since `a` can move to the front of
   `w₂`, write `w₂ = b c₁ … c_m a …`, where `b` and every `cᵢ` are
   comparable with `a`.
2. **Everything before `a` in `w₂` is below `a`.**
   - Sortedness of `(c_m, a)` gives `c_m < a`.
   - If `c_{m−1} > a`, then `c_{m−1} > a > c_m`. By transitivity
     `c_{m−1}` and `c_m` are comparable and adjacent in the wrong
     order, which is impossible. So `c_{m−1} < a`.
   - Repeating this down to `b` gives `b < a`.
3. **Symmetrically, `a < b`.** The same argument on `w₁` gives `a < b`,
   a contradiction.

Entries on one label are never swapped, so equal labels cause no
trouble.

**Lookups are canonical given canonical nodes.** Pushing a lookup down
to the first node where it is stuck is deterministic. If the nodes are
canonical, two lookups with the same meaning end at the same node with
the same variable.

**Matching and absorption are sound.** They are cancellation and the
identity renaming, valid in every model.

### What needs proof

1. **The blocked-match lemma.** I believe it because of the label that
   blocks the match. Say `N`'s first entry is on `y`, not known to be
   distinct from `x`. In models where `y` shares variables with `x`
   only away from `x₀`, inputs reach that entry by routes other than
   `x₀`. The same holds for later entries reached through it. This is
   the "escape" argument from `docs/interleaved-layered.md`. It should
   be simpler here: targets are absolute, and matching has already
   removed every entry that could cancel.
2. **Completeness of the rules.** Is every identity that holds in all
   interleaved models a consequence of the rules? These are sorting,
   matching, absorption, lookups and slot sharing. The new risk is
   coincidences between a stuck lookup `y⟨N⟩` and some other
   expression of the same value.
3. **Canonicity of the tree part.** The old `nf_unique` argument
   should carry over for everything that does not involve blocked
   matches. It has to be redone over interleaved models rather than
   one interpretation.

### Other points

- **`share` in the input.** Memoising compositions on node pairs keeps
  a well-behaved `share` (the same continuation at every use) from
  being recomputed. A `share` used with different continuations gets
  one composite per continuation. The spec makes no promise there, and
  `docs/literature-review.md` shows the size can then be exponential.
- **The bound label** is one more label, known distinct from every
  named one.
- **Readable output.** The printer has to show contexts with payloads
  on outputs, `share` for nodes used twice, and lifts where the
  pattern `⟦ x \ x | Γ[σ] ⟧` occurs.

## Later discussion

### A single structure for all of a context's entries

- **The data.** A context's input entries are its canonical (sorted)
  word. They are stored in an order-preserving balanced tree, so
  entries on labels not known to be distinct can live in the same
  structure.
- **Runs.** Maximal runs of entries whose labels are pairwise known
  distinct may be grouped, each run stored sorted.
- **Summaries.** Each node records enough about the labels below it to
  find, in `O(log n)`, where an operation on `x` stops: the first
  entry on a label not known distinct from `x`.
- **Targets are absolute**, so the entries an operation passes are not
  changed. An edit is local.

### Edits never cascade

The worry was that removing or inserting an entry leaves two
comparable entries adjacent and out of order, and that fixing them
causes further moves. The edits that operations make never need more
than one move. The proofs use only one fact: "known distinct" means
"comparable in a transitive order".

**Removal where an operation stops.** An operation on `x` passes a
prefix `A`, all of whose entries are comparable with `x`, and removes
the entry `e` on `x` that follows. Write `w = A e B`; the claim is that
`A B` is sorted.

- `A` and `B` are sorted, so only the junction between the last entry
  `a` of `A` and the first entry `b` of `B` needs checking.
- `a` is comparable with `x` and sits next to `e`, so `a < x`.
- Suppose `a > b`. Then `b < a < x`, so `b` is comparable with `x` and
  `b < x`.
- But `b` sits right after `e`, so sortedness of `w` forbids `b < x`.
  So `a > b` is impossible, and `A B` is sorted.

**Removal by absorption.** Absorption removes an entry `e` on `x` that
is followed only by entries comparable with `x`. This is the mirror
case: `b > x`. If `a < x`, then `a < b`. If `a` is incomparable with
`x`, then `a > b` would give `a > x`.

**Insertion.** A new entry `f` is put at the front and moves right past
entries comparable with it and smaller. It stops at an entry
incomparable with it or larger.

- Its new neighbours are in order by construction.
- Taking it out of the front leaves no new adjacency.
- Merging a composed context's own entries in this way, one at a time,
  costs `O(log n)` each. That is proportional to the size of the input
  that was added.

**Matching outputs.** Matching against a lift and a weakening, such as
`⟦ h | ⟦ \ h ⟧ ⟧`, is a sequence of removals where an operation stops
and insertions at the front. Each step is one of the cases above.

**The case that does cascade does not arise.** Take `w = a e b b₂`
with `e` incomparable with its neighbours, and `b < b₂ < a`. Removing
`e` makes `b` and then `b₂` move past `a`. In general a whole run moves
past another. But no operation removes an entry that is incomparable
with both its neighbours: removals happen only where an operation stops
and by absorption.

### Printing shared versions: name the large one

The suggestion: give a name to one large adjustment, and get the
others by composing it with weakenings or similar.

- **Every version made by an operation has this form**, because the
  version *is* the operation composed with the original:
  - `⟦ \ x ⟧ ⨾ N` is `N` with its first `x`-entry removed;
  - `⟦ h | ⟦ \ h ⟧ ⟧ ⨾ N` removes the second `h`-entry;
  - `⟦ f | N ⟧` adds `f`. This is equal to `N` with `f` inserted,
    because `f` only moves past entries it commutes with.
- **Removals only happen where operations stop**, so a prefix of
  weakenings and lifts can always reach them.
- **Printed size.** The original is printed once, and each version is
  a prefix whose size is the number of changes.
- **Open: which large adjustment to name.** The choice must be a
  function of the canonical graph, not of the history.
  - A natural choice: for each node, the base that gives the smallest
    prefix among named nodes, with ties broken by a fixed order.
  - Hash-consed trees make the differences between versions cheap to
    find where they share subtrees. Finding the best base among all
    nodes is still a search.

## Detailed design

A first full version of the design above, so that it can be checked
piece by piece.

### 1. What a normal form is

A normal form is a **sorted, reduced word of steps**.

**Steps.**

- `E_h(v)`: an input entry on label `h` with value `v`.
- `W_h`: a weakening on `h`.
- `A(σ)`: an adjustment atom.

Runs of equal consecutive steps are kept as one step with a count, as
in `docs/design-nf2.md`. A lift around an atom is
`E_x(x₀) · A(σ) · W_x`, where the value `x₀` is the variable `W_x`
creates.

**Meaning.** In a model, an input variable passes the steps from left
to right.

- `E_h(v)` gives `v` if the variable is `h₀`. Otherwise the variable
  continues, unshifted along `h`.
- `W_h` shifts the variable along `h`.
- `A(σ)` is stuck, with the rest of the word as its continuation.

**Values are absolute.** They live in the scope at the end of the
word. A value is one of:

- a variable `(g, i)` of that scope;
- a term `u⟨P⟩`, optionally with a payload atom, where `P` is a normal
  form;
- a stuck lookup `y⟨X⟩`, where `X` is a normal form and `y` a variable
  of its input. In practice `X` is a suffix of a word.

**Reduced** means all of the following.

- **No cancellation:** no `W_h` is followed by an `E_h` with only steps
  on labels known distinct from `h` between them.
- **No absorption:** no `E_h(v)` is followed by a `W_h`, with only steps
  on labels known distinct from `h` between them, when `v` is what the
  rest of the word gives `h₀` after that `W_h`.
- **Lookups are pushed down:** every lookup is pushed as far as it goes,
  so equal values are equal syntax.
- **No unobservable payload steps:** a payload with no payload atom
  observes only named variables, so it has no steps on the bound label
  before its first atom.

**Sorted** means two things.

- No two adjacent steps on labels known distinct from each other are in
  the wrong order. That covers entries and weakenings alike, ordered by
  the facts.
- Steps on the same label never swap, and atoms swap with nothing.

Uniqueness of the sorted representative is proved above ("Sorting gives
a unique representative").

**Printing.** Context forms are only how a word is printed: a maximal
block of entries followed by a maximal block of weakenings is one
context form.

### 2. Storage

Each word is a balanced binary tree with its steps at the leaves, in
order. Nodes are hash-consed: equal content and equal children give one
node.

**What the tree needs.**

- Its shape must be a function of the word alone. Then equal words are
  one node, and hash-consing gives canonicity.
- Split, concatenate, insert and delete must each create `O(log n)`
  new nodes.

**Choice for now: a Cartesian tree.**

- *Shape:* the priority of a step is a structural hash of its content,
  including the hashes of the words it refers to. This needs no
  identifiers that depend on how the word was built. The Cartesian tree
  of a sequence of priorities is unique, with ties broken leftmost.
- *Expected cost:* depth is `O(log n)` while the hashes behave randomly.
- *Weakness:* a long periodic stretch (`a b a b …`) has repeated
  priorities and degrades to a path. Runs remove only the trivial case,
  where equal steps are adjacent.
- *Deterministic alternative:* locally consistent parsing (Mehlhorn,
  Sundar and Uhrig) handles periodicity, with worst-case
  `O(log n · log* n)` per edit. It is the fallback if mechanised bounds
  must be worst case.

**Node fields:** left child, step, right child, size, hash and summary.

### 3. Summaries

Searches need to know, for a subtree, whether an operation on a
variable of label `h` passes all of it. Passing means two things. Every
step is on a label known distinct from `h`, or on `h` itself. And the
variable's index along `h` never reaches 0 at an `E_h` or a `W_h`
inside the subtree.

**Summary of a subtree.**

- Whether it contains an atom step.
- Its labels, split in two:
  - a bitset of label atoms, indexed by their context position;
  - a set of concrete labels, as a hash-consed trie.
- For each label in it: the number of `E` and `W` steps, and the lowest
  index along that label reached inside the subtree, measured relative
  to the index on entry.

**The query.** Combine the subtree's label sets with precomputed sets
of labels not known distinct from `h`. Use the per-label counts for
`h`.

**Cost.** A summary is a map over the labels present. With few labels
(the usual case) it is constant. In general, merging summaries along a
path costs up to `O(log n · ℓ)` per edit, for `ℓ` distinct labels. This
is open item 2 below.

### 4. Operations

`n` is the size of the word acted on.

**Lookup `(g, i)` in `w`.** Descend using the summaries to the first
step where the variable stops:

- an `E_g` reached at index 0 gives its value;
- a step on a label not known distinct from `g`, or an atom, leaves a
  stuck lookup. Its node is the suffix of `w` from that step, split off
  in `O(log n)`.

This is an eliminator: no new data except the suffix.

**Removal where an operation stops.** `O(log n)`. Proved to need no
reordering.

**Insertion with a move.** `O(log n)`. Also proved to need no further
reordering.

**Composing an input context `c` with a normal form `N`.** Right to
left, `c` is small and `N` may be large and shared.

1. **Values.** Each value of `c` gets `N` pushed into it.
   - A variable becomes a lookup in `N`.
   - A term `u⟨P⟩` becomes `u⟨P ⨾ N⟩`, memoised on the pair of nodes.
2. **Weakenings.** `c`'s weakenings move into `N`, innermost first.
   Each one searches for the first step on its label, or on a label not
   known distinct from it.
   - If that step is an `E` on its label at index 0, both are removed
     (cancellation).
   - Otherwise it is blocked. It stays, inserted in sorted position
     among the steps before the blocking one: it moves right past
     comparable smaller steps.
3. **Entries.** `c`'s entries are inserted, last first. Each moves right
   past comparable smaller steps. At each insertion point, check for
   absorption: one search and one lookup.
4. **Result.** The tree that results. `N`'s own steps are never
   copied: only paths change.

*Cost:* `O(|c| · log n)` tree operations, plus the memoised payload
compositions.

**Composing two normal forms `M ⨾ N`.** This arises inside payloads.

- *What it does:* every value of `M` changes, so `M`'s steps are
  rebuilt. Costs are `O(|M| · log |N|)`.
- *Memoisation:* it is memoised on the pair of nodes. Within the
  well-behaved fragment each pair occurs once.

**An atom.** `σ ⨾ N` is the step `A(σ)` concatenated in front of `N`.

### 5. Printing

**Named words.** A word is named if it is used twice or more, as a
payload or as the target of a lookup, or if it serves as a base (below).

**Bases.** A word `w` is printed as `p ⨾ B`, where `B` is named and `p`
is a short context of entries, weakenings and lifts. Otherwise `w` is
printed in full.

Examples:

- `N_k` is `⟦ x_k := u_k⟨N_{k+1}⟩ | N_{k+1} ⟧`;
- the `k`-th payload of the deletion example is `⟦ \ x_k ⟧ ⨾ n`.

**The choice of base must be a function of the graph.** Proposal: the
named `B` that minimises `|p|`, with ties broken by size and then hash.
An index over the named words' subtrees can make the search fast, but
it must find the exact minimum to stay canonical. This is open item 4
below.

### 6. What is established and what is open

**Established (on paper):**

- sorted words are unique representatives;
- the edits operations make are local, with no cascades;
- tree shape is canonical, given deterministic structural hashing;
- composition with an input context costs `O(|c| log n)` tree
  operations and never copies `N`.

The quadratic examples become linear:

- the chain of substitutions: each step adds one entry to a shared
  tree;
- the deletion example: each `⟦ \ x_k ⟧ ⨾ n` is one removal from `n`'s
  tree.

**Open:**

1. **Uniqueness of the normal form.** Two sorted, reduced words that
   agree in every interleaved model are equal. This is the
   blocked-match lemma in its general form. It is still the central
   risk, and the data structure does not touch it.
2. **The cost of summaries with many labels.**
3. **Periodic words with Cartesian trees.** Either show they cannot
   arise in normal forms beyond runs, or switch to locally consistent
   parsing.
4. **Choosing bases for printing.** Canonically and fast.
5. **Printing lookups readably.** `y⟨X⟩` where `X` is a suffix of a word
   being printed should print as a reference into that word, not as a
   separate copy.
