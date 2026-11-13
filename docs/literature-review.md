# Normal forms with sharing: what the literature does

A short note for discussion before any more proofs. The question: why
does the canonical form of `docs/design-nf2.md` need so many tie-breaking
rules (order, routes, phantoms, no-hop, levels, users), and does known
work do this more simply under our constraints:

- the output is a concrete term, and equal meanings give syntactically
  equal terms (no quotient);
- the algorithm never expands sharing (the tree form is not the base);
- the output size is linear in the input.

Grabmayer–Rochel, Condoluci et al. and McBride were read in full for
this note; the others from their abstracts and introductions.

## The lines of work

### 1. Maximal sharing with a concrete readback

Grabmayer and Rochel, *Maximal sharing in the λ-calculus with letrec*
([arXiv 1401.1460](https://arxiv.org/abs/1401.1460), implementation
[maxsharing](https://hackage.haskell.org/package/maxsharing-1.0.3);
follow-up [arXiv 1902.02010](https://arxiv.org/pdf/1902.02010.pdf)).

- **Method.** Translate the term to a higher-order term graph: each
  vertex carries an *abstraction prefix*, the binders in scope. Then
  implement it as a first-order term graph by putting *scope
  delimiter* vertices `S` on the edges where the prefix shrinks; an `S`
  is an explicit weakening, with a backlink to the binder it closes.
  Collapse by bisimulation (DFA minimisation, O(n log n)), then read
  back.
- **Scope must be minimal.** Maximal sharing and uniqueness both need
  *eager scope*: every vertex's prefix is as short as possible
  (Prop. 4.11: eager-scope prefixes on a graph are unique). Otherwise
  equal subterms in different scopes are not merged. This is
  co-de Bruijn's discipline (§3) under another name.
- **Readback.** A DFS spanning tree of the collapsed graph, then local
  synthesis rules bottom-up along it. They say plainly that the
  placement of `let`s has freedom (let-floating preserves the graph) and
  that the readback rules *decide* it. The readback is a function of
  the graph, but it is sensitive to the sharing of `S` vertices: it can
  emit `let`s that are mere aliases, which they remove afterwards.
- **Concrete canonical terms:** yes: `rb ∘ collapse ∘ ⟦·⟧` sends
  unfolding-equal terms to the same term.
- **Expansion and size:** nothing is unfolded, but the first-order
  graph is **O(n²)**, and the bound is tight (Lemma 7.1, Fig. 18):
  unary scope delimiters repeat a weakening at every edge where it
  happens. With "S-unsharing" the output is O(n log n); the whole
  method is O(n² log n).
- **Point for us:**
  - Canonicity is not a predicate on syntax with a uniqueness theorem.
    It is the image of one function (readback ∘ collapse). Where a
    shared thing is placed is a decision the readback makes, not a
    condition the normal form must satisfy.
  - Weakenings as unary nodes cost a factor of n. To stay linear,
    shifts must be data on edges (a count or a thinning), not nodes.

### 2. Deciding sharing equality without a normal form

Condoluci, Accattoli and Sacerdoti Coen, *Sharing equality is linear*
(PPDP 2019, [paper](https://cs.paperswithcode.com/paper/sharing-equality-is-linear)).

- **Method.** λ-graphs: DAGs in locally nameless style, where a bound
  variable node points back to its binder and every path from the root
  to a variable passes its binder (*domination*). Sharing equality is
  bisimilarity plus conditions on free variables. It is decided in
  linear time, as in Paterson–Wegman unification. The algorithm keeps a
  canonical element for each class and never has to merge two classes.
- **Concrete canonical terms:** no. It decides equality. Picking a
  representative per class is the readback problem of §1.
- **Expansion:** none, linear.
- **Limit that matters to us.** They state that representations where
  "every subterm is paired with an environment, representing a delayed
  substitution" (closures, as in abstract machines with local
  environments) *cannot be compared directly*. They must first be
  translated to one global environment, which they leave as future
  work. Our terms `u⟨payload⟩` are exactly such closures.
- **Point for us:** comparing shared structure without unfolding has a
  linear, local algorithm (a node pair at a time) when sharing is
  global. For delayed substitutions there is no off-the-shelf answer.

### 3. Hashing modulo α and co-de Bruijn

- Maziarz, Ellis, Lawrence, Fitzgibbon and Peyton Jones, *Hashing
  modulo α-equivalence* (PLDI 2021, [arXiv 2105.02856](https://arxiv.org/pdf/2105.02856)).
  Each subterm gets a summary in two parts: its structure without
  variable identities, and a map from free variables to the positions
  where they occur. Summaries combine bottom-up, in O(n log² n).
- McBride, *Everybody's got to be somewhere* (MSFP 2018,
  [arXiv 1807.04085](https://arxiv.org/abs/1807.04085v1)). In the
  co-de Bruijn representation each subterm is in exactly the scope of
  its own support. A thinning (an order-preserving weakening) sits on
  each edge, and at each node the children's thinnings must cover the
  node's scope. Weakenings are put as near the root as possible, which
  is the opposite choice from de Bruijn's. Uniqueness "comes for free":
  thinnings form a category in which the needed morphisms are unique.
  A substitution is a *partition* of its source scope into passive
  variables (thinned through) and active ones (with images). Applying
  it to a term whose support is all passive is just a thinning, with no
  traversal.
- **Concrete canonical terms:** co-de Bruijn, yes. Every term has
  exactly one representation, and the "cover" condition is local to a
  node. Hashing gives a hash, not a term.
- **Expansion:** none. The thinnings are data on edges.
- **Point for us:** a subterm in its own minimal scope, with the
  renaming kept on the edge, makes sharing modulo renaming free. Two
  uses of one core under different shifts are one node. Our conditions
  on the users of bound slots, phantoms and "every bound variable used,
  numbered by first use" look like a positional reinvention of
  co-de Bruijn covers.

### 4. Normal forms of substitution expressions

- Schäfer, Smolka and Tebbi, *Completeness and decidability of de
  Bruijn substitution algebra in Coq* (CPP 2015,
  [pdf](https://www.ps.uni-saarland.de/Publications/documents/SchaeferEtAl_2015_Completeness.pdf)),
  and the σ-calculus line (Abadi, Cardelli, Curien and Lévy, λσ; and
  the σSP calculi with metavariables).
  - **Method.** Substitution expressions are normalised by pushing
    composition inwards: `(t · s) ∘ r = t[r] · (s ∘ r)`. A normal
    substitution is a cons list ending in `↑ᵏ` or `↑ᵏ ∘ X`.
  - **Concrete canonical terms:** yes, and the decision procedure is
    complete.
  - **Expansion:** yes. `r` is copied into every closure. This is our
    free model (`fres`): `FTerm u b k` is a closure `u[k]` with its
    payload fully composed. It is a tree form.
- Related: [Explicit weakening (arXiv 2412.03124)](https://arxiv.org/pdf/2412.03124),
  and the renaming-category normal forms in
  [arXiv 2301.11842](https://arxiv.org/pdf/2301.11842). Not read in
  full.
- **Point for us:** there is one canonical unshared normal form, and
  it is well understood. All our difficulty comes from sharing. For
  example, the no-hop example `⟦ x | σ ⟧ ⨾ ⟦ x := u⟨σ⟩ ⟧ = ⟦ x := u ⟧ ⨾ σ`
  is the single σ-normal form `u[σ] · σ`, with `σ` used twice.

### 5. String diagrams and term graphs

- Corradini and Gadducci, *An algebraic presentation of term graphs,
  via gs-monoidal categories* (1999). Term graphs (DAGs with explicit
  sharing) are exactly the arrows of the free gs-monoidal category:
  terms with copy and discard, without the naturality equations that
  would identify a shared term with its copies.
- Bonchi, Gadducci, Kissinger, Sobociński and Zanasi, *String diagram
  rewrite theory I–III* (2016–2022). String diagrams for symmetric
  monoidal categories correspond to hypergraphs (cospans), taken up to
  isomorphism.
- **Concrete canonical terms:** the canonical object is a graph up to
  isomorphism. A concrete term needs a canonical labelling. For general
  hypergraphs that is as hard as graph isomorphism. For a rooted DAG
  with ordered successors it is easy: number the nodes in depth-first
  order from the root.
- **Expansion:** none.
- **Point for us:** our expressions are rooted and ordered, so we are in
  the easy case. "Free structure = graph; concrete form = a fixed
  traversal" is the standard answer. Being a gs-monoidal (not cartesian)
  term, a term with `share` still records how much is shared. A normal
  form must pick an amount of sharing, and maximal sharing is the only
  canonical choice.

## What this suggests is wrong with our normal form

The current form puts three different things into one positional
syntax:

1. the meaning: the σ-normal form, our `fres`;
2. which parts of it are shared: a closure's payload is "the rest of the
   line", or a branch;
3. local compression: runs, lifts, tail shifts.

Item 2 is encoded by where a term stands in the line. One meaning
often has several placements (before or after an atom, in a branch or
in the line, routed to one variable or another). Each such pair needs a
rule to rule one out, and a uniqueness proof that covers every pair.
That is where order, no-hop, phantoms, routes, levels and users come
from. It also explains why uniqueness was provable while existence is
still open: the rules have to be shown jointly satisfiable, and the
algorithm has to hit exactly them (estimated at 8–15k lines).

Every line of work above separates the three. Grabmayer–Rochel also
show what goes wrong otherwise: if scope is not kept minimal, sharing
is lost; if weakenings are unary nodes, the size becomes quadratic.

- **Nodes are meanings.** Use hash-consing or a collapse over a graph
  whose nodes stand for σ-normal substitutions and closures, with local
  compression inside the node alphabet (runs, `k` lifts as one number),
  and with renamings on edges in co-de Bruijn style. Building it never
  unfolds: composing with a renaming relabels an edge, and composing
  with a shared node yields one new node per pair actually reached.
- **Sharing is the collapse.** Two nodes are equal iff they have equal
  labels and equal children, checked locally. Maximal sharing is the
  canonical choice.
- **Syntax is the readback.** A deterministic function from the
  collapsed graph to our concrete syntax. It emits one `share` per
  node with two or more parents, placed at the lowest point that
  dominates all its uses, in depth-first order. It recognises patterns
  such as `0 · (σ ∘ ↑) ↦ lift σ`. Placement rules such as no-hop become
  facts about what the readback does, not conditions to check.

### What canonicity would then cost to prove

Define the specification on the finite unshared form, which we have as
the old tree normaliser:

    canon e := readback (maxshare (tree_nf e))

Here `maxshare` is defined on trees: a subtree is shared iff it occurs
twice. Uniqueness then holds by definition: `canon` is a function of
`tree_nf e`, which is a function of the meaning. The proof obligations
are:

1. **Soundness:** the denotation of `canon e` is the meaning of `e`.
   The readback is a printer, so this is induction on the graph.
2. **Agreement:** the linear algorithm (hash-consing on the shared
   input, then readback) returns exactly `canon e`. This is a
   simulation proof: the algorithm's node ids stand for subtrees, and
   two ids are equal iff their subtrees are.
3. **Size:** the graph is linear in the input, provided shifts are
   counts on edges rather than unary nodes (see §1). The pairs reached when
   composing are bounded as for the current line form.

Expansion appears only in the specification and the proofs, never at
run time. That respects "the tree form is not the base" for the
algorithm. The spec needs the tree form to be finite with decidable
equality, which our functional `fres` is not. The old tree normaliser's
output is.

## Correction: the proposal is not linear

1. **The specification.** `maxshare (tree_nf e)` goes through the
   unshared form, which is exponential in `e`. A specification may be
   exponential, but its *output* must still be small, and this one's is
   not.

2. **Flattening loses compositions.** The σ-normal form pushes
   composition into every closure. A chain of `L` layers, each
   substituting for a different variable, has `L` different suffix
   substitutions of size up to `L`. Their maximally shared form is
   Θ(L²): flattening loses the composition, which is exactly what the
   line keeps.

3. **Sharing a composition makes it worse.** Take
   `share x₁ := a ⨾ b in share x₂ := x₁ ⨾ x₁ in … xₖ ⨾ xₖ` with atoms
   `a` and `b`. Its meaning is the word `(a b)^(2^k)` of stuck atoms.
   Neither the flattened tree nor the current line can share it: the
   line lists its atoms one by one. So the current design is not
   linear on this input either.

### A general obstruction

Restrict to atoms, composition and `share`. Atoms do not interact, so
an expression means a word over atoms, and expressions are exactly
straight-line programs (SLPs) for words.

Suppose `canon` runs in polynomial time and always has size at most
`c · |e|`, with `share` counted once. Then for every word `w`,
`|canon w| ≤ c · g(w)`, where `g(w)` is the size of the smallest SLP
for `w`. Running `canon` on the explicit word gives a polynomial-time
`c`-approximation of the smallest grammar problem.

- That is NP-hard below 8569/8568 (Charikar et al., *The smallest
  grammar problem*, 2005).
- For any constant `c`, it is open; the best known ratio is
  O(log(N/g)).

So "canonical, linear-size, `share` in input and output" is at least as
hard as a long-open problem. The known canonical encodings of
compressed words are within log factors, not linear: signature
encodings (Mehlhorn, Sundar and Uhrig) and recompression (Jeż). These
two references are from memory and not checked.

### Bounds must not compound

Any bound of the form `|canon e| ≤ c · |e|` with `c > 1` compounds.
Let `o = canon e` and feed `share x := o in x ⨾ x` back in: its size is
`|o| + O(1)`, so `k` rounds allow `c^k` growth. Restricting the inputs
(only linear where `share` binds no composition of atoms) is worse:
`canon`'s own output shares line suffixes containing atoms, so a second
run has no bound at all.

A bound that survives iteration is stated against an intrinsic measure
of the *meaning*, the smallest representation `g`, not against the
input. `share x := o in x ⨾ x` raises `g` by `O(1)`, so nothing
compounds. For the atom word this is the smallest-grammar setting:

- `c · g` is the open problem above;
- canonical encodings achieve `O(g · polylog N)`: locally consistent
  parsing and signature encodings, which are history independent;
  `O(g log(N/g))` by recompression. These references are from memory,
  not checked, and the canonicity of recompression in particular needs
  checking.

So the realistic goal is the following:

- **(b′)** `|canon e| ≤ C · g(e) · log N(e)`, where `g` is the smallest
  representation with `share` and `N` is the unfolded size;
- canonical, so `names; reflexivity` decides equality;
- non-compounding.

## Open questions

- **Closures.** None of the papers handles sharing through delayed
  substitutions; Condoluci et al. name it as open. Our `u⟨payload⟩` is
  a closure whose payload is itself shared. The graph approach covers
  it only if a payload is a node like any other (a substitution value
  in minimal scope), so that `u⟨σ⟩` and `u⟨σ'⟩` share iff `σ` and `σ'`
  are the same node.

- **Sharing modulo renaming.** A shared core used under different shifts
  should be one node. That needs a canonical scope for each core:
  co-de Bruijn thinnings for bound variables, plus something for named
  labels, whose renamings need not preserve order. This is the part
  most specific to shifted names, and the one I am least sure of.
- **Readback target.** Can every collapsed graph be printed in the
  current adjustment syntax, with lifts, runs and tails, in linear size?
  Or does the syntax need a more direct `share`/`let` form?
- **Node alphabet.** Which local compressions (runs, binary lift
  counts) go into node labels, so that the graph stays linear when lift
  counts are given in binary.
- **What is kept.** `Normalise.v` and the free model are kept. Most of
  `BUnique.v` would become unnecessary: its conditions describe a
  placement policy that the readback would fix instead. `CanonW` and
  `CanonBr` would be replaced by the readback.

## Canonical compression of words (log factor accepted)

Checked against the papers; theorem numbers are those of the arXiv
versions.

- **Jeż, recompression** ([arXiv 1301.5842](https://arxiv.org/abs/1301.5842)).
  `TtoG` alternates two steps:
  - compress every maximal block `aᵏ`;
  - compress the pairs `ab` with `a ∈ Σℓ` and `b ∈ Σr`.

  The partition comes from `GreedyPairs` (Alg. 2). It is deterministic,
  and it reads only pair counts in the current word and an order on
  letters, which is first occurrence in the word (Lemma 1). The cover
  guarantee (≥ ¼ of pairs, Lemma 4) holds for any letter order.
  Theorem 2 bounds the size by `O(g log(N/g))` in the worst case.
  Naming each new letter structurally (as the pair or block it
  replaces) therefore makes the output a function of the word alone:
  **canonical, deterministic, within a log factor.** Caveat: TtoG runs
  on the uncompressed word.
- **Restricted recompression** (Kociumaka, Navarro and Prezza,
  [arXiv 1910.02151](https://arxiv.org/abs/1910.02151), Construction
  V.6, Theorem V.18).
  - Symbols are named structurally, `A = Σ ∪ A×A ∪ A×ℕ≥2`, which is
    exactly hash-consing.
  - Size `O(δ log(N/δ))` (≤ `O(g log N)`).
  - The partition is uniformly random, so a fixed seeded hash gives the
    bound only in expectation. That is not usable for a mechanised
    worst-case bound.
  - Kempa and Kociumaka ([arXiv 2308.03635](https://arxiv.org/abs/2308.03635),
    Cor. 5.23) derandomise it at an extra log factor.
- **Signature encodings** (Nishimoto et al.,
  [arXiv 1605.01488](https://arxiv.org/abs/1605.01488)). Deterministic
  coin tossing reads the integer IDs of symbols, and the IDs depend on
  insertion order (§5). So the *shape* of the grammar is not canonical.
  Avoid.
- **Trees.**
  - Top DAGs (Bille et al., [arXiv 1304.5702](https://arxiv.org/abs/1304.5702))
    are canonical, but merges ignore labels. They are within `O(log n)`
    of the minimal DAG (Thm 2), not of tree grammars.
  - Tree recompression (Jeż and Lohrey,
    [arXiv 1309.4958](https://arxiv.org/abs/1309.4958), Thm 1) is
    `O(r g log(n/g))` and canonical by the same argument as for words,
    but defined on uncompressed trees.

**Inference, not stated in any paper.** Run recompression on an SLP
instead of the word (as Jeż does for compressed pattern matching), and
choose each partition by `GreedyPairs` on the *word's* pair counts and
first-occurrence order. Both are computable from the SLP. Every phase
then makes exactly the choices `TtoG` would make on the word. The
result is the same canonical grammar, with Theorem 2's bound, in time
polynomial in the input SLP and `log N`. This needs checking: that the
proof of Theorem 2 uses nothing but Lemma 4, and the cost of
first-occurrence order and pair counts on an SLP.

**For our normal form.** The atom word of a line becomes a recompression
grammar. The open part is everything that is not a word: segments
interact with neighbouring atoms (lifts, terms hopping), and a term's
payload is a *suffix* of the line. A suffix is not a symbol of the
grammar; it is a path through it. Payload sharing therefore has to be
expressed as "suffix of a grammar symbol". A balanced grammar (depth
`O(log N)`, Ganardi, Jeż and Lohrey,
[arXiv 1902.03568](https://arxiv.org/abs/1902.03568)) makes each suffix
a list of `O(log N)` symbols. That is a log factor per distinct payload
start, which is within budget.
