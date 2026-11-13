# Normal forms with sharing: what the literature does

A short note for discussion before any more proofs. The question: why
does the canonical form of `docs/design-nf2.md` need so many tie-breaking
rules (order, routes, phantoms, no-hop, levels, users), and does known
work do this more simply under our constraints:

- the output is a concrete term, and equal meanings give syntactically
  equal terms (no quotient);
- the algorithm never expands sharing (the tree form is not the base);
- the output size is linear in the input.

Caveat: arxiv.org is not reachable from this session, so the summaries
of arXiv papers come from abstracts and earlier knowledge, not from a
fresh reading.

## The lines of work

### 1. Maximal sharing with a concrete readback

Grabmayer and Rochel, *Maximal sharing in the λ-calculus with letrec*
([arXiv 1401.1460](https://arxiv.org/abs/1401.1460), implementation
[maxsharing](https://hackage.haskell.org/package/maxsharing-1.0.3);
follow-up [arXiv 1902.02010](https://arxiv.org/pdf/1902.02010.pdf)).

- **Method.** Translate the term to a first-order term graph (scope is
  recorded by "abstraction prefixes" on nodes). Collapse the graph by
  bisimulation, as in DFA minimisation (Hopcroft, O(n log n)). Read the
  collapsed graph back as a λletrec term.
- **Concrete canonical terms:** yes. The collapse is unique up to
  isomorphism, and the readback is a deterministic function of an
  ordered graph, so equal meanings give the same term. A `letrec` is
  placed at the lowest scope that covers all its uses.
- **Expansion:** none. The graph is linear in the input, and the
  collapse never unfolds.
- **Point for us:** canonicity is not a predicate on syntax with a
  uniqueness theorem. It is the image of one function (readback ∘
  collapse). Where a shared thing is placed is a decision the readback
  makes, not a condition the normal form must satisfy.

### 2. Deciding sharing equality without a normal form

Condoluci, Accattoli and Sacerdoti Coen, *Sharing equality is linear*
(PPDP 2019, [paper](https://cs.paperswithcode.com/paper/sharing-equality-is-linear)).

- **Method.** λ-terms as DAGs (variables are nodes, binders point to
  them). Equality of the unfoldings is decided in linear time, in the
  style of Paterson–Wegman unification: union-find over nodes, plus a
  check that the merges respect scope.
- **Concrete canonical terms:** not directly. It decides equality. The
  equivalence classes it builds give a canonical form once each class
  has a canonical representative, which is the readback problem of §1.
- **Expansion:** none, linear.
- **Point for us:** the hard part, comparing shared structure without
  unfolding, has a linear algorithm that is local (a node pair at a
  time). It needs no global positional conditions.

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
  is the opposite choice from de Bruijn's.
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

Every line of work above separates the three:

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
3. **Size:** the graph is linear in the input. The pairs reached when
   composing are bounded as for the current line form.

Expansion appears only in the specification and the proofs, never at
run time. That respects "the tree form is not the base" for the
algorithm. The spec needs the tree form to be finite with decidable
equality, which our functional `fres` is not. The old tree normaliser's
output is.

## Open questions

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
