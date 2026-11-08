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
  bound (per-slot back-links could replace it); `rto_padj` tests normality
  and back-links at runtime (`psel`), which goes when `Bind` takes a closed
  term; `npush_outer` maps `pshift` over every payload (stage 5).
- **Cheap fixes to fold in:** `comp_entry` maps over the targets instead of
  indexing them; identity payloads are returned without traversal.
