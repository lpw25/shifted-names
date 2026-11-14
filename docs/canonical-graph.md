# A canonical graph for adjustments

Goal: a graph structure that represents an adjustment uniquely while
keeping sharing. Turning it into syntax canonically is a separate step,
done afterwards.

## The string diagram

Read an adjustment as a string diagram.

- **Wires** are variables. The input context is on top, the output
  context at the bottom. Ports are named by `rvar`: a label and an
  index.
- **A term box** `(u, b)` has one input: the variable it is
  substituted for. It has a bundle of outputs: the free variables of
  `u`.
- **An atom box** `a` has a bundle of inputs and a bundle of outputs:
  all variables of its source and target contexts.
- **Merging and discarding.** Several wires may enter one port
  (a renaming identifies variables). An output port may receive no wire
  (weakening).

The free model (`Unique.fres`) *is* this diagram, unfolded into a tree:

| Free model | Diagram |
|---|---|
| `FVar y` | the wire reaches output `y` |
| `FTerm u b k` | the wire enters term box `(u, b)`, whose outputs are wired by `k` |
| `FStuck a z k` | the wire enters port `z` of atom box `a`, whose outputs are wired by `k` |

## The graph

Collapse the free model: nodes are hash-consed by their meaning.

- **Continuation node** `C`. For each label, a list of targets for
  indices `0 … n−1`, then a uniform tail. The tail is either
  `i ↦ output (l, i + m)` or `i ↦ port (l, i − L)` of one atom box.
  Labels with no entries are not stored.
- **Target:** an output variable, a term box `(u, b, C')`, or a port
  `z` of an atom box `(a, C')`.
- **Box:** a term box is `(u, b, C')` and an atom box is `(a, C')`,
  where `C'` wires the box's outputs.
- **Payloads without a payload atom.** For `FTerm u None k`, only the
  named part of `k` is observable. The node stores the named part only,
  with no bound entries.

Local encoding rules: runs are maximal, the tail starts as early as
possible, and labels are kept in a fixed order. Per-label lists are
cons lists, so a suffix is shared: a node `C` and `↑ ⨾ C` share their
lists.

**Uniqueness.** A node is a function of its meaning, by construction.
Hash-consing makes equal meanings the same node. No tie-breaking is
involved.

The old conditions disappear:

| Old condition | In the graph |
|---|---|
| routes | identified variables are wires into the same port |
| bound numbering, users | output ports are named by the meaning |
| phantoms | unobservable ports are not stored |
| order within a stretch, no-hop, tails | there are no layers to place things in |

The examples that needed tie-breaking:

- **Hop.** `⟦x | σ⟧ ⨾ ⟦x := u⟨σ⟩⟧ = ⟦x := u⟧ ⨾ σ` gives one graph:
  `x ↦ (u, ·, C_σ)`, and the rest is the tail at box `(σ, end)`.
  `C_σ` has the same tail.
- **The symmetric pair** `{x ↦ u1⟨k1⟩, x' ↦ u2⟨k2⟩}`: two term
  boxes, each with its own continuation node. Nothing has to be
  ordered.
- **A chain of `L` substitutions** `κᵢ = ⟦x := uᵢ⟧ ⨾ κᵢ₊₁`: the
  `x` list of `κᵢ` is `cons (uᵢ, ·, κᵢ₊₁) (x list of κᵢ₊₁)`. That is
  O(1) per layer, so linear.

## Sizes

**Without `share`.** O(1) new list cells per entry an input segment
creates, plus the label map. With a balanced map on labels this is
O(n log m), where `m` is the number of labels.

**Risk: an edit at a large index.** `xᵢ := u` copies the cells of
`x`'s list before position `i`. Runs make an untouched prefix one cell.
But a run of edits at increasing depths copies earlier edits, which is
quadratic. A canonical balanced sequence would fix this at a log
factor; plain cons lists are simpler.

**With `share`.** The graph itself can be exponential.
`share x := ⟦y := u⟧ in x ⨾ … ⨾ x` (2^k copies) has 2^k distinct
continuations `κᵢ`, a chain where `κᵢ = F(κᵢ₊₁)`, with
`F(X) = {y: cons (u, ·, X) (X.y), …}`. `X` occurs twice in `F`, but
in the graph it is a single node, so `F` is a one-hole *graph context*.

So with `share` the graph must be stored compressed:

- one-hole graph contexts compose, so a chain of them is a word over
  contexts, compressed by recompression (`F^(2^k)` becomes O(k));
- splitting the graph into such contexts canonically could use the
  dominator tree of the graph, which is unique;
- the dominator tree is then a tree of one-hole fragments, compressed
  by tree recompression.

Open: computing this from the compressed input without unfolding.

## Turning it into syntax (later)

Each node and box becomes an expression. A continuation node becomes an
explicit-environment construct (per label: a list of targets, then a
tail). A box used more than once gets a `share`. A compressed chain
becomes nested `share`s of its contexts.

Two constructs are needed beyond `share`:

- an explicit environment whose entries can be "port `z` of atom box
  `(a, C')`";
- a term with an explicit payload node.

Both denote adjustments.

## Open questions

1. Plain cons lists, or canonical balanced sequences (a log factor,
   no quadratic case)?
2. The canonical compression of the graph with `share`: dominator
   splitting plus recompression, computed from the compressed input.
3. Whether reading the graph back gives readable syntax, compared
   with the line form.

## The well-behaved fragment of `share`

`share` exists so that payloads can be shown as nested substitutions
without writing the same payload or tail twice. We do not restrict the
language. We promise good performance on a fragment, and `names` only
produces terms in that fragment.

**The condition.** `share r := a in b` is well behaved when every use
of `r` in `b` has the *same continuation after it*: nothing is composed
after one use that is not composed after all of them. Then `r` denotes
one node of the graph, and the graph is no bigger than the term.

**Once per path is not enough.**

    r₀ := a
    rₖ := ⟦x := u[rₖ₋₁ ⨾ c₁], y := v[rₖ₋₁ ⨾ c₂]⟧

Every path uses each `rᵢ` once. But a term in `rₖ` has, as payload,
`rᵢ` composed with every word of length `k − i` over `{c₁, c₂}`. That
is 2^k distinct continuations, so the meaning needs a grammar again.

**Payload and tail together are fine.** In context forms a pushed term
is not composed with the tail (`rpush_inner` is cons). So
`⟦x := u[r] | r⟧` sends `x` to `u[r]` and every other input through
`r`. Each path passes through `r` once, with nothing after it: one
node. It would be `r ⨾ r` only if a term's payload were composed with
the tail, as in the old line form, where a payload is "the rest".

**Closure.** The fragment is closed under:

- composing a whole well-behaved term with anything, which adds the
  same continuation to every use;
- lifting a whole term;
- using a whole term as a payload;
- copying a term, which copies its binders, so the copies are
  separate `share`s.

The output of `names` is the graph printed with a `share` per node that
has two or more parents. Every use of such a `share` is a payload or
tail position, so the output is in the fragment. A user who starts
without `share` therefore stays in the fragment whatever they do.

**Lifts.** A use under a lift inside `b` gets `↑` composed after it,
and other uses do not. Shifts commute, so this is quadratic at worst,
not exponential. It stays one node if shifts are labels on graph edges,
in co-de Bruijn style: a continuation is a core node plus a thinning,
with the core using all its outputs.

**Constructs needed:**

- per-label tails (`⟦ x: … | r₁ ; y: … | r₂ ⟧`), because the lists of
  one node can share suffixes with different nodes;
- an entry stuck at an atom: "port `z` of `a ⨾ r`".

**Outside the fragment.** No size guarantee. Inputs that need a
grammar (`share x₂ := x₁ ⨾ x₁`) still normalise correctly, but can be
exponential.

**Remaining risk.** A lookup or edit at a large index walks the cells
before it.

## Not enforced

The fragment is not enforced by types: tail bindings with a rank-2
block were considered and rejected. `share` stays as it is. Good
performance is promised only for well-behaved uses, and `names` only
produces well-behaved terms.

## The well-behaved fragment, precisely

**Syntax.** The syntax is `aexp`, `texp` and `pexp` of
`Core/Normalise.v`, plus `share r := a in b` on `aexp` and variables
`r`. The meanings below are those of `aeden`, `teden` and `peden`:

| Expression | Meaning |
|---|---|
| `ACompose a b` | `a ∘ b`: `b` first, then `a` |
| `AInner h t a` | cons: the pushed term is *not* composed with `a` |
| `AOuter h a` | `a`, then `↑h` |
| `ALift h a` | push `h₀`, then `a`, then `↑h` |
| `TBindE u p` | the term `u[p]` |
| `TShiftE h t` | `t`, then `↑h` on a variable result |
| `PComp a p` | `a ∘ p`: `p` first, then `a`. A nested substitution `u[p][a]` is `TBindE u (PComp a p)` |
| `PShift h p` | `p`, then `↑h` |

**Continuations of occurrences.** A continuation `K` is a list of
adjustments, applied after the occurrence in order. `occ e K` is the
multiset of pairs `(r, K')`, one per occurrence of a `share` variable
`r` in `e`, where `e` itself has continuation `K`:

    occ r K                  = {(r, K)}
    occ AId K = occ (AAtom n) K = ∅
    occ (ACompose a b) K     = occ b (a :: K) ∪ occ a K
    occ (AInner h t a) K     = occT t K ∪ occ a K
    occ (AOuter h a) K       = occ a (↑h :: K)
    occ (ALift h a) K        = occ a (↑h :: K)
    occ (share r := a in b) K = (occ b K without r) ∪ ⋃ {occ a K' | (r, K') ∈ occ b K}

    occT (TVarE h i) K       = ∅
    occT (TBindE u p) K      = occP p K
    occT (TShiftE h t) K     = occT t (↑h :: K)

    occP PId K = occP (PAtom n) K = ∅
    occP (PComp a p) K       = occP p (a :: K) ∪ occ a K
    occP (PShift h p) K      = occP p (↑h :: K)

An occurrence inside the bound adjustment of an inner `share` is
counted once for each use of that inner variable, with that use's
continuation.

**Definition.** `share r := a in b` is *well behaved* when all
continuations in `{K | (r, K) ∈ occ b []}` are equal, up to a leading
list of shifts. An expression is well behaved when every `share` in it
is.

Nested substitutions are covered:

- `⟦x := u[r] | r⟧` (`AInner x (TBindE u (PComp r PId)) r`): both
  uses have continuation `[]`.
- `⟦x := u[r][a] | a ∘ r⟧`: both uses have continuation `[a]`.
- `u[r][a]` next to a bare `r`: the continuations are `[a]` and `[]`.
  This is not well behaved, and it is exactly the shape of the
  exponential example.

**Closure.** A whole expression `e` gets the same continuation
appended to all its occurrences. That holds for composition on either
side, lift, outer, use as a payload `u[e]` or `u[p][e]`, and shifting.
`share`s inside `e` compare continuations relative to their own body,
so they stay well behaved. Copying `e` copies its binders. So
well-behaved terms are closed under everything a user can do without
writing `share`.

**Output of `names`.** The graph printed with one `share` per node
with two or more parents. Inside a `share` body, flat forms nest only
through payloads and tails, never under composition. So every use has
continuation `[]`, except for slot shifts in tails, which are leading
shifts. The output is therefore well behaved.

**Claim to establish.** On a well-behaved input of size `n`, the graph
has O(n) nodes when all continuations are exactly equal. A use with a
leading shift `↑ᵏ` denotes `r ∘ ↑ᵏ ∘ K`, which is a different node
unless shifts are carried on edges. Either the bound gets a factor for
the number of distinct leading shifts, or shifts must be edge labels.
Not yet settled.

## Prototype (`proto/`)

An executable model of the design. See `proto/README.md`.

### Representation

- **Per-label lists of entries.** An entry is `V l i`, a term
  `T u b R`, or `S a z R`, stuck at an atom. A list ends in one of:
  - `nilv l`: the identity, `j ↦ V l j`;
  - `nils l a R m`: `j ↦ S a (l, j+m) R`;
  - `nilp`: the bound inputs of a payload with no payload atom. They
    are not observable, and `nilp` has no outputs.
- **Nodes.** A node is a list for each label.
- **Hash-consing.** Everything is hash-consed.
- **References carry a post-shift.** A reference is `(s, object)`,
  where `s` gives a count of `↑` per label, applied to outputs. Every
  object is stored *factored*: its least output index is 0 on each
  label it outputs. So `C` and `C ∘ ↑` are one object.
- **Canonical lists.** A cons cell that repeats what its nil would give
  is absorbed into the nil, so the explicit prefix is as short as
  possible.
- **Evaluation.** `ev a K` computes "`a`, then `K`". It is memoised on
  the core of `K`, using `ev a (K ∘ s) = ev a K ∘ s`.

### Results

- **Soundness and canonicity.** On 32,000 random expressions with the
  final code (20,000 of depth 4 and 12,000 of depth 3, with `share`,
  lifts, atoms, payload atoms and the bound label), the graph means
  what the expression means. Equal meanings give the same graph:
  across 16,000 distinct meanings, the number of graphs always equals
  the number of meanings.
- **Idempotence.** On 7,000 random expressions,
  `graph (print (graph e)) = graph e`, with the same meaning.
- **Sizes** (graph objects; evaluations):

  | Family | Result |
  |---|---|
  | chain of `L` substitutions | linear |
  | `L` lifted atoms then a substitution | linear |
  | well-behaved `share`: payload and tail, `⟦x := u[r] \| r⟧` | linear |
  | well-behaved up to leading shifts: payload and `⟦· \| r⟧` | linear |
  | the same, composed after a continuation sensitive to shifts | Θ(k²) |
  | not well behaved: `u[r][c₁], v[r][c₂]` | exponential |
  | insertions at depth `i` (lifts written in unary) | linear in the graph; evaluations linear in the (quadratic) input |

  The Θ(k²) case is inherent: the meaning has that many distinct
  sub-continuations. It cannot arise from a share-free history. The
  graph depends only on the meaning, and a share-free expression of
  size `n` has an O(n) graph.
- **Histories.** Start share-free, then repeatedly normalise and apply
  a random operation: compose either side, lift, outer, use as a
  payload, or push. The meaning is checked at every step. Over 6
  histories of 120 steps, evaluations stay below 2.5 × the share-free
  size of the history, and graph size below 8 ×. The maxima are
  reached early, when the history is small.

### Two things the prototype found

- **The phantom filler matters.** The unobservable bound inputs of a
  payload without a payload atom must be a filler with no outputs
  (`nilp`). Filling them with the identity is not invariant under
  shifts. That made one meaning have two graphs, and made a
  well-behaved family quadratic.
- **Printing is free, but the obvious choice is not linear.**
  Canonicity only needs the printer to be a deterministic function of
  the graph. Insisting on one context form `⟦ cells | tail ⟧` per node
  duplicates list cells that the graph shares per label. The printer
  therefore:
  - uses `⟦ cells | tail ⟧` only when none of the stripped cells is
    shared;
  - otherwise prints label by label (`⟦x: …; y: …⟧`, the new
    per-label construct);
  - refers to a shared list through a node whose list it is;
  - shares every object referenced twice or more.

  Output is then linear. Examples:

      ⟦x := u0⟧ ∘ σ0                    ↦  ⟦x := u0 | id⟧ ∘ σ0
      ⟦x := u0⟧ ∘ ⟦x := u1⟧ ∘ ⟦x := u0⟧  ↦  share k0 := ⟦x: u0, …id⟧ in
                                            share k1 := ⟦x: u1[k0], …k0⟧ in
                                            ⟦x: u0[k1], …k1⟧

## Open points

1. **Order of labels in the output.** Distinct label expressions are
   assumed to denote distinct labels (as in `BUnique.Hinj`), so the
   graph keys lists by label expression. The *printed* order of labels
   must not depend on how reification numbered the label atoms. Two
   label atoms that the facts do not order need some other order, for
   example their position in the proof context.
2. **Compact lists.** Lifts with binary counts need runs in the lists
   (`Run c k`), or a deep lift costs its count. This is task 7.
3. **New constructs in the output syntax:**
   - the per-label form `⟦x: entries, …tail; y: …⟧`;
   - an entry stuck at an atom, `z via (R ∘ σ)`.

   Both denote adjustments.

## Plan for the mechanisation

The graph is a tree in the specification (Coq data has no sharing) and
a hash-consed table in the implementation.

1. **`Core/GForm.v`.** The canonical encoding as inductive types:
   entries, lists with shifted tails, nodes, and references with
   post-shifts. Its meaning is a `fres` function. Local canonicity is
   factoring, absorbed nils and `nilp`. **Uniqueness:** two canonical
   encodings with `feq` meanings are equal. This replaces `BUnique`
   with a local, structural induction.
2. **`Core/GEval.v`.** `ev` on trees, and its soundness: its meaning
   is the meaning of the expression. With uniqueness this gives
   canonicity, so `names; reflexivity` decides equality.
3. **`Core/GTable.v`.** The hash-consed table: interning by structural
   key, and evaluation memoised on (expression, core of the
   continuation). Refinement: unfolding the table gives the tree of
   step 2. Time bounds on paper.
4. **`Core/GPrint.v`.** The printer, from the table to an expression
   with `share`. It depends only on the unfolded tree. Soundness: the
   printed expression means the graph.
5. **Integration.** Integrate with `names`, remove the old modules
   (`Unique`, `Normal`, `Complete`, `Merge`, `LayeredOrder`, `Canon*`,
   `Retarget`, `Canonical`, `LFree`, `LEval`, `Layered*`, `BUnique`),
   and update the docs.

## Mechanisation status

Proved in Coq, with no admits or axioms (`Print Assumptions` closed),
about 2,200 lines:

- **`Core/GForm.v`.** The canonical encoding:
  - entries, per-label lists with a shift on every tail, nodes whose
    lists each carry a shift, and references with a post-shift;
  - its meaning in the free model (`fres`);
  - local canonicity conditions: factored shifts, no cell absorbable
    into its nil, and `LNilP` for the unobservable bound inputs of
    payloads without a payload atom;
  - **`gref_unique`**: canonical encodings with the same meaning are
    equal;
  - decidable equality.
- **`Core/GEval.v`.** The free meaning `fa` of expressions
  (`aexp`/`texp`/`pexp`), a raw evaluator, and **`ev_sound`**: the raw
  evaluation means `fa`.
- **`Core/GCanon.v`.** Canonicalisation:
  - syntactic output labels that agree with the free model;
  - the cell and node cases, factoring shifts and absorbing cells;
  - **`canon_all`**: the result is canonical and means the same;
  - **`canon_complete`**: expressions with the same free meaning have
    the same canonical form.

What the proof changed in the design:

- **Each list of a node carries its own shift.** One node can shift
  an output label differently in different lists.
- **Entries store the variable itself, not a label position.**
- **Canonicalisation is a separate function on raw encodings.** It is
  not built into the evaluator's constructors. The existence proof is
  `cell_spec` and `node_spec`, not one condition per tie-break.

Still to do:

1. Store label expressions (`lexp`) instead of their denotations, so
   that the canonical form is the same term for every interpretation
   of label atoms. Distinct label expressions are assumed to denote
   distinct labels.
2. Link `fa` to the real semantics (`aeden`), as `Unique.adequacy`
   does for words, so that `canon` decides equality of adjustments.
3. `share` in the reified expressions, and the efficient implementation
   (hash-consed table, evaluation memoised per continuation), refining
   the tree specification.
4. The printer, integration with `names`, and removing the old
   modules.
