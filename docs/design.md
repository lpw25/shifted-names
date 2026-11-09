# Design: substitutions with good extraction

This document describes the current development in `theories/`: what users
write, how adjustments are represented, how the operations work, and what
they cost. The history of the design is in `design-history.md` and in the
git log.

## Goals

- Users define their syntax as an indexed inductive `term : nat → Type`
  and write **one** function, a Relative.v-style Kleisli extension, plus a
  handful of laws proved by routine induction.
- The library gives `subst : adj (term 0) N M → term N → term M` with all
  the substitution laws, for every syntax.
- Payloads and their lazy adjustments are invisible to users.
- No fuel anywhere: not at runtime, not in goals.
- Adjustments are canonical: equal meaning implies Leibniz equality, so
  goals only ever contain `subst a t` on canonical adjustments.
- Extracted OCaml looks like hand-written code: binary numbers, native
  labels, no runtime validity checks, and costs proportional to the data
  touched.

## The user interface

```coq
Inductive ext (N M : nat) : nat -> nat -> Type :=
| ext_here : ext N M N M
| ext_under {K L} : ext N M K L -> ext N M (S K) (S L).

Definition morph N M := forall K L, ext N M K L -> var K -> term L.
```

A syntax is a module of type `SYNTAX` (`Core/Syntax.v`):

- `term : nat -> Type` and `tvar : var N -> term N`;
- `kleisli : morph N M -> ext N M K L -> term K -> term L`, structural on
  terms, going under a binder with `ext_under`;
- its laws, each a routine induction on terms: `kleisli_var`,
  `kleisli_ext` (pointwise-equal morphisms), `kleisli_rebase` (witness
  composition), `kleisli_unit` and `kleisli_assoc`.

Declare the scope as a non-uniform *parameter*
(`Inductive tm (N : nat) := ... | tlam (b : tm (S N))`), not an index.
Constructors then store no scope, and `kleisli` needs no convoy pattern.

The functor `Subst` (`Core/Subst.v`) gives:

- `apply a : morph N M`, by structural recursion on the adjustment;
- `subst a t := kleisli (apply a) ext_here t`;
- rewrite rules that make `subst a (tlam b) = tlam (subst (lift a) b)` hold
  by `cbn`, for any binder constructor;
- `subst_identity` and `subst_compose`.

`Examples/Lambda.v` is a complete client: the λ-calculus with open, close
and instantiation and their inverse laws.

## Representation

`Core/Repr.v`. Targets name output variables directly. The only thinnings
stored on nodes are weakenings, kept as counts.

```
nadj    = NAdj (root : counts) (entries : atrie entry)
entry   = Entry h (targets : kseq target) (len : nat) (p : nat)
target  = TVar y j        -- j relative to the counts above
        | TBind u ρ       -- a closed term with a pending adjustment ρ
```

- **An entry for label `h`** sends `hᵢ` to its `i`-th target for `i < len`,
  and to `h₍ᵢ₋len₊p₎` (relative to the base) beyond: pass-through.
- **Counts** (`Counts.v`). A count map is a default plus exceptions: per
  label, `None` (unused below) or how far the outputs used below start
  above the parent's base. Every non-empty set of indices factors uniquely
  as `k + J` with `0 ∈ J`, and weakenings compose by addition, so counts
  are canonical. A count map carries a strict proof that no exception
  repeats the default, so every count map is canonical.
- **Annotated structures** (`Based.v`, `Skew.v`, `ATrie.v`). Every node of
  the label trie and of each skew-binary tree carries the minimum of the
  counts below it, relative to its parent. Elements are stored relative to
  the base of the node holding them, so moving a subtree only changes its
  top. A skew sequence keeps one base at its head, and the trees of its
  spine are all stored relative to it.
- **The root** is the global weakening. A label without an entry is the
  identity relative to it, so weakening is an O(1)-path update at the root.
- **Payloads.** `ρ` in `TBind u ρ` has no entry for the bound label, and its
  root takes the place of a leaf's counts.

### Normal form

`nlocal` (Repr.v) is the one-level normal form:

- entries are keyed by their label;
- an entry is present iff it is not the identity relative to the root;
- the last target is not what pass-through would give (strip);
- every node's counts are exactly the minimum below;
- gap entries record labels whose root count is not attained.

`nwf` (Deep.v) is this at every level, through payloads. It is *defined* as
a structural boolean check `nwfc`, so a proof of it lives in SProp
(`Strict.v`). Records pairing an adjustment with that proof are equal
exactly when their data are equal. Each part of the normal form is
determined by the meaning (`napply`), which gives canonicity.

## Operations

### Point operations (`Point.v`)

- `nidentity`: an empty trie over the uniform root.
- `weaken h a`: add 1 to the root's `h`-count.
- `extend h t a`: cons `t` onto `h`'s targets. The root is lowered to the
  minimum with `t`'s uses (`lower`), and everything below moves up by the
  difference, which `cexcess` computes from `t`'s labels alone; gap entries
  are added where needed. Then `t` goes onto `h`'s entry. For a variable
  target the label trie is updated incrementally (`ATrie.aupd`):
  - on the way down, each node on the path is lowered to an envelope the new
    entry stays above (`y_j` and `h_0`), moving its children up at those
    labels only;
  - on the way up, each node's counts are recomputed at the labels `h` and
    `y` from its children (`araise`);
  - the entry's frame is known only lazily, so the target is shifted into
    it with `ldval`.
  A payload target uses every named label, so it goes through `aupdate`,
  which rebuilds the path. Consing onto the entry's skew sequence lowers
  the head base at `t`'s labels and moves the O(log n) trees by the
  difference; only merging two trees builds a new node over them.
- `lift h a := extend h (TVar h 0) (weaken h a)`.

Each has a meaning theorem and keeps `nwf`.

### Composition (`Compose.v`)

`compose a b` is `b` followed by `a`. A variable result goes where `a` sends
it, and a payload `(u, ρ)` becomes `(u, a ∘ ρ)`, where only `ρ`'s named
labels matter.

**`a` as a pure shift above thresholds.** Let `a`'s entry for `y` be
`(len_y, p_y)` over root `w` (with no entry, `(0, 0)`). Then, for an absolute
input `y_j` with `j ≥ θ_y := len_y`, `a(y_j) = y_(j − θ_y + τ_y)`, where
`τ_y := w_y + p_y`. So above the thresholds `θ`, `a` acts as
`unshift τ ∘ shift θ`, given by two count maps.

**The traversal** recurses structurally over `b`'s trie, its sequences and
its payloads (no fuel). It carries the absolute base and the *blocking
map*: the thresholds of the labels whose minimum use below the node is
under them (`Prune.v`).

- When the blocking map is empty, the node is **moved**: only its counts
  change, and nothing below it is visited.
- Otherwise:
  - leaves are looked up in `a`;
  - payloads recurse with the payload flag, which skips the bound label;
  - counts are rebuilt with the smart constructors.

Per label `h`:

- **Entry in `b`, pass-through start `s` at or above `θ_h`.** Map the
  targets. The composite pass-through is `s − θ_h + τ_h`.
- **Entry in `b`, `s` below `θ_h`.** `b`'s mapped targets are consed onto
  `a`'s targets from `s` on (`kapp`, after an O(log n) skew drop `kdrop`),
  and the pass-through becomes `τ_h`.
- **Entry only in `a`.** `a`'s entry with its first `W_h` targets dropped
  (`kdrop`, O(log n)).
- **Neither.** The identity relative to `τ + W`, with a gap entry where the
  new root drops below it.

A composite whose last target equals pass-through is stripped. The check is
O(log n), and the entry is rebuilt only when the strip fires.

`compose_spec`: for `nwf` inputs, the composite is `nwf` and means
`rcomp a ∘ napply b`. It is proved by strong induction on nesting depth.

### Lookup and substitution (`Lookup.v`, `Subst.v`)

`aget_with` and `knth_with` pass what they find to a continuation, with
its location as a strict proposition. The guard checker therefore sees a
found payload's adjustment as a subterm, so `apply` recurses structurally
into payloads. Scoping proofs are built from the location proofs, so
nothing is tested at runtime.

The base a lookup reaches is the sum of the counts on its path. It is kept
as a **lazy base** (`lbase`): an absolute map, with node counts and payload
roots stacked on top. `ldval` reads one label's count of it, and
`lcounts`, its meaning, appears only in specifications. A variable lookup
never merges count maps.

Under `d` binders, `apply` does offset arithmetic on `d`; it never computes
a `lift`.

## Costs

Notation:

- `|y|`: the length of label `y`'s key (one count-map or trie lookup);
- `n`: the size of the adjustment;
- `m`: the number of exceptions in the count maps involved.

**Count-map operations.** A pointwise operation (`Trie.mmerge`, with a
mode per operation and default) only walks the overlap of the two maps'
exceptions. Exceptions that only one map has are kept or dropped whole
when the other map's default allows it, which it does for the defaults
`None` and `Some 0` that occur, except that `cadd` and `cplus` map the side
whose other default is `Some 0`. So an operation with a small map, like a
single label's count or a delta at a few labels, costs O(size of the small
map · its key lengths).

| Operation | Cost |
|---|---|
| `apply` on a variable (lookup) | O((\|h\| + log n) · \|y\|): trie path, sequence path, then one label read off the lazy base |
| `apply` on a payload result | the lookup, then `kleisli` over the payload term, looking up its variables lazily over the payload's base |
| weaken `y` | O(\|y\|) at the root |
| extend `h` with a variable `y_j` | O((\|h\| + log n) · (\|h\| + \|y\|)): the root and the trie path patched at `h` and `y`, the cons onto `h`'s sequence; plus, amortised, merging two trees of the sequence |
| extend `h` with a payload | O(\|h\| · m): the payload uses every named label, so the root drops everywhere and the path is rebuilt |
| lift `y` | as weaken plus extend with `y_0` |
| compose | below |

A cons that merges two trees of the sequence builds a node over them,
whose counts cover both. That is amortised (a merge of size `w` happens
once every `w` conses), and a program that keeps consing onto one old
version can repeat an expensive merge.

Composition costs:

- a's thresholds, `τ` and the blocking tree, once: O(|a| log |a|);
- per visited node: filtering the blocking map, O(|blocking| · |y|), plus
  the smart constructors' count merges, which walk the overlap of the
  children's maps;
- per visited leaf: one lookup in `a`;
- per `b`-entry whose pass-through reaches `a`'s targets: O(len of the
  `b` entry + log n);
- per level, that is the top and each **visited** payload: finishing the
  composite costs O(|a| · (log n + m)). This covers adding `a`-only entries
  (O(log n) each, by `kdrop`), the identity starts, identity removal and
  gaps.

Composing with a weakening or a lift visits only the paths to uses below
the thresholds.

Overall, composition costs O((P + 1) · E_a · c + V · c′ + L · ℓ), with
`E_a` the number of `a`'s entries, `P` the visited payloads of `b`, `V` and
`L` the visited nodes and leaves, `ℓ` a lookup in `a`, and `c`, `c′` the
per-entry and per-node costs above.

**Known cost above the ideal:** a visited payload costs O(|a|) to finish.
Its composite `a ∘ ρ` contains `a`'s entries, which are rebuilt rather than
shared with `a`'s trie. Sharing would only help in typical cases: the root
is a global minimum, and when the composite discards part of `a` (a dropped
prefix holding a payload target, which uses every named label), the root
can change at any number of labels, which then all have to be checked.
So the worst case is O((P + 1) · E_a) under this normal form either way.

## Extraction

`Extraction/Extraction.v`:

- `nat` and extension witnesses become Zarith integers; `ext_depth` is the
  identity;
- realizers for the `Nat` comparisons, `div2`, `min`, and the key functions
  `string_key` and `key_label` on native strings;
- the lookups' type-only section variables are erased.

`tests/extraction/run.sh` extracts the λ example's substitution, compiles it
against Zarith and runs a smoke test (open/close round trips, instantiation
under binders, key round trips).

## Status

Everything above is implemented and proved with no admits. `Print
Assumptions` is closed for:

- `compose_spec`;
- `subst_compose` and `subst_identity` (through the λ example's
  `subst_subst` and `subst_id`);
- `topen_tclose` and `tclose_topen`.
