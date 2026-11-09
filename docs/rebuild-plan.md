# Rebuild plan: substitutions with good extraction

This plan records the design agreed after the review of Relative.v, the
extraction review, and the cost discussion. It supersedes the term-layer
parts of D10/D11 in `implementation-plan.md` (the adjustment core of
D9–D11 stays).

## Goals

- Users define their syntax as an indexed inductive `term : nat → Type`
  and write **one** function, a Relative.v-style Kleisli extension, plus a
  handful of laws proved by routine induction.
- The library gives `subst : adj (term 0) N M → term N → term M` with all
  the substitution laws, for every syntax.
- Payloads and their lazy adjustments are invisible to users.
- No fuel anywhere: not at runtime, not in goals.
- Goals only ever contain `subst a t` / `apply a ...` on canonical
  adjustments, so equality of adjustments decides equality of stuck forms.
- Extracted OCaml looks like hand-written code: binary numbers, native
  labels, no runtime validity checks, and costs proportional to the data
  touched.

## Design

### The user interface (Relative.v with an extension witness)

```coq
Inductive ext (N M : nat) : nat -> nat -> Type :=
| ext_here : ext N M N M
| ext_under {K L} : ext N M K L -> ext N M (S K) (S L).

Definition morph N M := forall K L, ext N M K L -> var K -> term L.
```

The user provides, as a module of type `SYNTAX`:

- `term : nat -> Type`, `tvar : var N -> term N`;
- `kleisli : morph N M -> ext N M K L -> term K -> term L`, structural on
  terms, going under a binder with `ext_under`;
- laws (each a routine induction on terms):
  - `kleisli_var`: `kleisli f e (tvar v) = f _ _ e v`;
  - `kleisli_ext`: pointwise-equal morphisms give equal results;
  - `kleisli_unshift`: re-basing the witness (`morph_extend` in Relative.v);
  - `kleisli_unit`: the identity morphism is the identity;
  - `kleisli_assoc`: Kleisli composition (relative-monad associativity).

### The library side (a functor over `SYNTAX`)

- `apply a : morph N M` for `a : adj (term 0) N M`, defined by
  **structural recursion on the nested adjustment**: lookups take a
  continuation (`get_with`, `nth_with`), so a payload's adjustment is a
  visible subterm. Going under binders is offset arithmetic on
  `ext_depth e`: O(1) per variable, no `lift` computed.
- `subst a t := kleisli (apply a) ext_here t`.
- Exported rewrite rules, as if `apply` reduced on the witness to lifts:
  - `kleisli (apply a) (ext_under e) t = kleisli (apply (lift a)) (shift e) t`;
  - `kleisli (apply a) ext_here t = subst a t`.
  With `cbn` these give `subst a (tlam b) = tlam (subst (lift a) b)` for
  any binder constructor, without per-syntax rules.
- For reasoning, a fuel-based *reference* lookup on `lift^d a` (never
  extracted, never in goals) and one lemma equating it with `apply`.
- Laws: `subst identity t = t`, `subst a (subst b t) = subst (compose a b) t`,
  the lookup equations, open/close/instantiate.
- `apply` and its helpers live inside the library where their definitions
  are visible to the guard checker; users see the interface. (Sealing behind
  a module type is a later step; for now `simpl never`.)

### Extraction

- A library file `Extraction.v`: `nat` and `ext` to Zarith (`ext_depth` is
  the identity on the extracted number), realizers for the `Nat`
  comparisons we use, native strings.
- Labels carry their trie key, computed once.
- Rule: no `if check then x else default` on computational paths; proofs
  come from types (convoy patterns, SProp arguments), never from runtime
  tests.

### Core performance

- **Back-links** (item 5): each output slot knows which inputs refer to it,
  so the strip check is O(1) and stripping costs the references it
  renumbers. Implemented as derived data kept alongside the canonical data,
  with fast operations proved equal to the reference ones.
- **Payload weakening tags** (item 6): per-label weakening tags on the nodes
  of the payload-holding structure, normalised so that each tag is the
  largest weakening common to everything below it. Named `push_outer` bumps
  the root tag: O(log n). Inserting a payload re-factors one path.
- Dropped: the bound-reference positions index (traversals no longer lift).

## Stages

Each stage ends with a green build, a commit and a push.

1. **Term interface and substitution** (`Core/Syntax.v`, `Core/Subst.v`):
   `ext`, `morph`, `SYNTAX`, the structural `apply`, `subst`, the rewrite
   rules, the reference lookup and the substitution laws.
2. **λ example** on the new interface: an indexed inductive with its
   `kleisli` and laws; remove the raw `LambdaCore`; tests for the rewrite
   view (`subst a (tlam b)` etc.).
3. **Extraction**: `Extraction.v`, label keys, extract the λ substitution,
   read the OCaml, compile it against Zarith and run a smoke test.
4. **Back-links** in the flat core, with fast `push_inner`/strip proved equal
   to the reference versions.
5. **Payload weakening tags** in the nested layer, with their canonical form.
6. Re-check extraction and costs; update the design docs.

## Status

- **Stage 1 (done).** `Core/Lookup.v`, `Core/Syntax.v`, `Core/Subst.v`.
  `apply` is structural (continuation lookups whose location proofs are
  strict propositions, so the guard checker sees payload adjustments as
  subterms and scoping proofs need no runtime test). Proved: the
  characterisation of `apply` by the raw lookup, `kleisli_apply_under`
  (offset to lift) and `kleisli_apply_here` (fold), `subst_identity`,
  `subst_compose` (through payloads, by induction on nesting depth with
  the user's associativity and re-basing laws). The user interface's
  re-basing law is `kleisli_rebase` (general witness composition) rather
  than a one-step unshift.
- **Stage 2 (done).** `Examples/Lambda.v`: the λ-calculus as an indexed
  family with one `kleisli` and five short law proofs; binder equations by
  `cbn` plus the library rule, including nested binders; open/close
  inverse laws; instantiation. The raw `LambdaCore.v` is gone.
- **Stage 3 (done).** `Extraction/Extraction.v` and
  `tests/extraction/run.sh`. Findings:
  - declare the scope of a syntax as a *non-uniform parameter*
    (`Inductive tm (N : nat) := ... | tlam (b : tm (S N))`), not an index:
    constructors then store no scope, and `kleisli` needs no convoy
    pattern; erasing indices with `Extraction Implicit` instead is unsafe
    because `kleisli` computes the index at binders;
  - label keys are computed by an OCaml realizer of `string_key` rather
    than precomputed in labels (same cost class, much smaller change);
  - the extracted `subst` is plain recursion with Zarith offsets and
    continuation lookups; the smoke test checks open/close round trips and
    instantiation under binders.

### Stage 4 design (in progress)

- **Sequences (`Core/Braun.v`, done).** Braun trees, specified by the list
  they denote (`to_list`); canonical (`canonical`); cons/tail, snoc/unsnoc,
  nth/update in O(log n); structural folds `ball`/`bmax` for recursion
  through nested payloads.
- **Per-label targets are Braun trees (done).** An entry holds a plain tree
  (a record with a strict balance field cannot appear in a nested inductive:
  positivity fails), and balance is part of `keys_ok`/`normal`. Proofs
  reason about the list a label's targets denote (`find` gives that list);
  computation uses the tree operations directly. Each operation is specified
  by its effect on the denoted lists. `Subst.apply` looks targets up with a
  Braun continuation lookup (`Lookup.nth_with`), O(log n), and `Extraction.v`
  realizes `Nat.even`/`Nat.div2` on Zarith.
- **Back-links (done).** Each entry records, for each of its output slots
  (innermost first), the inputs referring to it: a trie from the referring
  label's key to the set of positions counted from the back of that label's
  targets (stable under cons). They are determined by the targets
  ([refers]); [relink] computes them from scratch and [linked] checks them
  (by comparing with [relink]); [canonical] takes [linked] for both sides
  and compares back-links through [backs_unique]. Operations:
  - `push_outer` appends an empty set for the new slot: O(log n);
  - `push_inner` (`cons_linked`) adds one back-link, then checks the
    innermost slot's set against the singleton of the new input
    (`strip_check`, O(log n)). If `a` is normal at most one strip is needed,
    and only when `h` had no inputs (`push_inner_spec`), so `strip_sole`
    removes the input and the slot and retargets exactly the inputs listed
    in the remaining slots' back-links. Cost: O(log n + k_h + r_h log n)
    for `k_h` slots of `h` and `r_h` references to them;
  - `compose`, `restrict` and the expanding case of `push_inner_var` (a
    variable beyond the explicit slots) rebuild back-links with `relink`,
    O(S log S). Making expansion incremental would need the positions of
    the expanded label's inputs to shift, O(len); not done yet.
- **Remaining runtime costs seen in the extraction:** compose's
  normalisation still runs the reference-scanning `strip_ok` under a fuel
  bound (per-slot back-links could replace it); `npush_outer` maps `pshift`
  over every payload (stage 5).
- **Public `Bind` takes a closed term (done).** The indexed `target` is
  `Rename w | Bind u`; `Bind u` stands for the payload `(u, identity)`.
  Payload adjustments no longer appear in what users write, and nothing on
  the computational path tests normality at runtime (`psel` is no longer
  extracted).
- **Cheap fixes to fold in:** `comp_entry` maps over the targets instead of
  indexing them; identity payloads are returned without traversal.

## Stage 5 (design): direct references with weakening counts

This replaces the slot core (design D9) and the back-links of stage 4.

### Summary

- **Targets name output variables directly.** There are no slots, slot
  counts, back-links, expansion or renumbering. Per label, an entry holds
  explicit targets for `h₀ … h₍len−1₎` and a pass-through shift `c`
  (`hᵢ ↦ h₍ᵢ₊c₎` for `i ≥ len`). The normal form is local: the last target
  is not `h₍len−1+c₎`.
- **Weakening is lazy.** Every node carries, per label, a weakening count:
  how far the outputs used below it start above its parent's. These counts
  are the only thinnings stored on nodes. Everything else (gaps between used
  variables, renamings) lives at the leaves.

### Which thinnings are applied lazily

Only operations other than composition need to be lazy. On the image (the
used outputs of a label) they act at the front:

| Operation | Effect on the image | Effect on existing subtrees |
|---|---|---|
| weaken `y` | cons 0 | +1 on `y` |
| lift `y` | cons 1 (the new leaf uses `y₀`) | +1 on `y` |
| extend with `yⱼ` | uses `j` | none |
| extend with a term | the payload uses every named label from 0 | none |
| strip | none (the variable stays used by pass-through) | none |

So the thinnings ever applied lazily to existing structure are weakenings
`0ᵏ1^∞`, i.e. counts. Composition is eager (its cost is paid anyway) and
pushes changes to the leaves, pruned by the counts.

The larger class "finite prefix, then identity" was rejected. It lets nodes
record any gap pattern below the last use (so leaves end up holding
nothing), and a finite image has no largest factor in it.

### Factorisation

**Lemma.** Every non-empty `I ⊆ ℕ` decomposes uniquely as
`I = k + J` with `0 ∈ J`; namely `k = min I`. An empty image (a label not
used below) imposes no constraint.

So the canonical count at a node is the minimum used index below it, minus
its parent's. Composition of counts is addition.

### Count maps

A node's counts form a total map from labels to `option nat` (`None` means
the label is unused below). It is stored as a default plus exceptions:
`{ def : option nat ; exc : trie (option nat) }`, with every exception
different from the default, so it is canonical.

- A variable leaf `yⱼ`: default `None`, exception `y ↦ j` (relative).
- A payload: default `Some 0` (every named label used from 0), exception
  `None ↦ None` (closed terms use no bound variables), plus positive
  exceptions for weakenings.
- A node: the pointwise minimum of its children, with `None` as ∞; each
  child stores its counts relative to the node.

Operations are pointwise (`min`, `add`, `sub`). Pushing a count onto a
sibling with no counts of its own shares the map, so it is O(1). Otherwise
the merge walks the smaller side (small-into-large).

Factoring counts inside the label trie (a minimum at each label-trie node)
would make bulk weakenings of many labels O(1). None of our operations
needs it: the only "every label" default is the payload's, which is 0. It
stays an option if the API gains bulk weakenings.

### Representation

```
adj        = { root : counts            -- ω: per-label weakening of the whole adjustment
             ; entries : annotated trie of entry }   -- node counts relative to the parent
entry h    = { targets : skew sequence of target    -- inputs h₀ …, front first
             ; len : nat                             -- cached
             ; c : Z }                               -- pass-through shift, relative
target     = Var y j                                 -- j relative to the counts above
           | Bind u ρ                                -- ρ's root counts relative to the parent
```

- **The root.** A label without an entry is the identity relative to the
  root counts, so it uses its outputs from relative 0. Hence `ω` is the
  global weakening per label, and weaken is O(|y|) at the root.
- **Payloads.** `ρ` has no bound entry, and its root counts take the place
  of the leaf's counts.
- **Skew sequences.** Okasaki's skew-binary random-access lists, with a
  spine of cons cells carrying counts. `cons x` puts `x` at the root of the
  front tree, so the subtrees beneath keep their counts, and the rest of the
  list is one cell.

### Invariants (the normal form)

- The trie is keyed by label key; trees are canonical by construction.
- An entry is present iff `len > 0 ∨ c ≠ 0`.
- The last target of `h` is not `h₍len−1+c₎`.
- Every node's counts are the minimum over uses below (variable leaves,
  pass-through starts `len + c`, payload root counts), relative to its
  parent, as canonical count maps.
- Payload adjustments have no `None` entry and satisfy the same invariants.
- Exceptions in count maps are keys of labels.

Each part is determined by the meaning, so the representation is
canonical (Leibniz).

### Operations and costs

`|y|` is the length of label `y`'s key: the cost of one lookup in a count
map or the label trie.

| Operation | What it does | Cost |
|---|---|---|
| lookup `hᵢ` | trie path, sequence path; add the `y`-counts along the path | O(\|h\| + log n), plus O(\|y\|) per node with a positive `y`-count |
| weaken `y` | root `y`-count +1 (upward) | O(\|y\|) |
| extend with `yⱼ` | cons a leaf; where `j` is below a node's minimum, the difference goes to the sibling | O((\|h\| + log n) · \|y\|) |
| extend with a term | cons a payload; the named counts on the path move down to the siblings (downward) | O(\|h\|) + O(1), plus merges charged to earlier weakenings |
| lift `y` | weaken, then extend with `y₀` | as extend |
| strip | local check at the end of the label's list | O(log n) |
| compose | eager; a subtree whose minimum clears a shifted region is moved by its count alone; payloads `(u, a ∘ ρ)` recurse structurally (no fuel) | proportional to the parts `a` affects |

**Building.** Each weakening is pushed at most once per path, and pushes
onto siblings without counts share maps. Building by weakenings and extends
costs O((weakenings + extends) · log n), plus a small-into-large merge term.
The skew-list merges are amortised, so a program that keeps forking one old
version can repeat an expensive merge.

### Stages

1. `Core/Counts.v`: the factorisation lemma; count maps with their
   canonical form and pointwise operations.
2. `Core/Skew.v`: skew sequences with a spine and a count map on every node.
3. The annotated label trie.
4. The core: representation, meaning, invariants, canonicity.
5. Point operations: identity, weaken, extend, lift, lookup.
6. Composition and restriction.
7. Port `Adjustment`, `Laws`, `Scoped`, `Indexed`, `Subst`, the λ example and
   extraction; delete the slot core, back-links and `Braun.v`.

## Stage 6 (design): pruned eager composition

Stages 1–5 are done (`Counts`, `Skew`, `ATrie`, `Repr`, `Point`), with no
admits: identity, weaken, extend and lift each have a meaning theorem and
keep the normal form; lookup is `napply`.

### `a` as a pure shift above thresholds

Write `a`'s entry for `y` as `(len_y, p_y)` over root `w` (no entry:
`(0, 0)`). For an absolute input `y_j` with `j ≥ θ_y := len_y`,
`a(y_j) = y_(j − θ_y + τ_y)` where `τ_y := w_y + p_y`. So `a` acts on
everything at or above the thresholds `θ` as `unshift τ ∘ shift θ`, two
count maps. `θ` has exceptions only at labels whose entry has targets.

### The traversal

`a ∘ b` recurses structurally over `b`: the label trie, each entry's skew
sequence, and payloads (no fuel), carrying

- the absolute base of the current node, and
- the **blocking map**: `θ` restricted to the labels whose minimum use below
  the node is under its threshold.

At each node the blocking map is filtered by the node's counts. Counts only
grow downwards, so a label leaves the blocking map at most once per path.
When the map is empty, the node is **moved**: its absolute counts become
`M − θ + τ`, and nothing below it is visited. Otherwise leaves are looked up
in `a`, payloads become `(u, restrict (a ∘ ρ))`, and node counts are
recomputed bottom-up with the smart constructors. Mapped subtrees come back
relative to base 0, and the parent rebases them.

Per label `h`:

- **Entry in `b`.** Map its targets. Its pass-through starts at absolute
  `s = B_h + p`:
  - if `s ≥ θ_h`, the composite pass-through is `s − θ_h + τ_h`;
  - otherwise `a`'s targets `s … θ_h − 1` are appended. That rebuilds `h`'s
    sequence, and the pass-through becomes `τ_h`.

  If the last composite target is now where pass-through would send it, the
  entry is stripped (check O(log n); rebuild only when it fires). A pure
  shift is injective, so moved parts never create a new strip.
- **Entry only in `a`.** `a`'s entry with its first `W_h` targets dropped
  (skew drop, O(log n)).
- **Neither.** The identity, relative to `τ + W`. As in `lower`, where the
  new root drops below that, a gap entry is added.

### Costs

- `|blocking| · |y|` per visited node;
- one lookup in `a` per visited leaf;
- a rebuild of `h`'s sequence only for labels whose pass-through reaches
  `a`'s targets;
- O(log n) per entry of `a` (drops and merging into the trie).

Composing with a weakening or a lift visits only the paths to uses below the
thresholds.

### Order of work

1. `Skew.v`: the pruned map over skew sequences (smart constructors with
   absolute children, the blocking filter, and the spec
   `klist (map) = map F (klist s)` under a pruning-soundness hypothesis).
   Also drop and snoc-by-rebuild.
2. `ATrie.v`: the pruned map and merge over the label trie.
3. `Compose.v`: composition, `restrict`, the recursive normal form, and the
   meaning and canonicity theorems.
