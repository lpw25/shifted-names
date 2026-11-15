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
