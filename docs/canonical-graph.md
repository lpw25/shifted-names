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
