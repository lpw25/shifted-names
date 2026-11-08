# Shifted names: implementation plan

This plan takes the design consolidated in
[`design-history.md`](design-history.md) (sections 7, 8 and 10) to a finished
development. The early stages are concrete. The later ones, which integrate
the new core back into a full shifted-names library, are deliberately loose,
because decisions made earlier will reshape them.

## Goals

- A core of **adjustments**: renamings and substitutions on shifted names with
  a canonical representation. Extensional equality is Leibniz equality, so
  plain `rewrite` and `reflexivity` work and setoid rewriting is not needed.
- Good asymptotics for the core operations (apply, compose, normalise,
  equality), using canonical persistent maps instead of lists.
- A reflective normaliser for expressions built from these operations.
- On top of that, terms, an indexed (scoped) layer, contexts, and the
  `examples/Lambda.v` client from `master` as the acceptance test.

**Non-goals for now:** the effect-system extras from the OCaml variant
(`Unknown`/`Top`, `Meet`, residuals, factors), and backwards compatibility with
any old branch.

## Ground rules

- **Toolchain:** Rocq 9.x (stdlib as a separate package); see
  [Environment](#environment). Build with `dune` (`rocq` stanzas) or
  `_RocqProject` + `rocq makefile`; whichever we pick, CI runs it.
- **Where the work lives:**
  - a new branch started from `adjustments`;
  - new code under `theories/` with logical path `ShiftedNames`;
  - old `src/` files are kept only as reference until they are superseded,
    then deleted;
  - the old branches stay untouched as history.
- **Proof style:**
  - Canonical data is a record of raw data plus an SProp proof of
    normality, as in `next-unindexed`'s `Renaming.v`.
  - Every equation is stated with `=`. No `Proper` instances in the core.
  - No `Admitted` on `main`; work in progress lives on branches.
- **Executable from the start:** every operation is a Gallina function that
  computes with `cbn`/`vm_compute` on closed data, with `Example … :=
  eq_refl` tests alongside.

---

## Key design decisions

### D1. Per-label adjustments

This is the representation from design history §7.4. For each label `l`
(an `option label`, where `None` is the anonymous de Bruijn label):

- `inc l`: a list of length *j* of targets for `l₍₀₎ … l₍ⱼ₋₁₎`. Each target is
  `Rename (l', i')` with `i' < out l'`, or `Bind p`.
- `out l`: a count *k* of fresh outer slots.
- Every other `l₍ᵢ₎` with `i ≥ j` maps to `l₍ᵢ₋ⱼ₊ₖ₎`.

Normality means:

- no label has an empty `inc` entry or a zero `out` entry, so absent means
  trivial;
- no `inc l` ends in a transparent entry `Rename (l, out l − 1)`;
- every target is in range.

Renamings are adjustments whose payload type is `Empty_set`.

### D2. Canonical maps: Appel & Leroy's extensional binary tries

The paper is **Andrew W. Appel and Xavier Leroy, "Efficient Extensional Binary
Tries", Journal of Automated Reasoning 67 (2023)**, also arXiv 2110.05063. It
gives a trie over `positive` keys whose representation is canonical *by
construction*:

```coq
Inductive tree' (A : Type) :=
| Node001 : tree' A -> tree' A        | Node010 : A -> tree' A
| Node011 : A -> tree' A -> tree' A   | Node100 : tree' A -> tree' A
| Node101 : tree' A -> tree' A -> tree' A
| Node110 : tree' A -> A -> tree' A   | Node111 : tree' A -> A -> tree' A -> tree' A.
Inductive tree (A : Type) := Empty | Nodes (m : tree' A).
```

Empty subtrees are unrepresentable, so
`(∀ k, get k m₁ = get k m₂) → m₁ = m₂` holds without any well-formedness
invariant. That is the property we want: an adjustment's canonicity then
reduces to canonicity of its per-label entries. Operations are logarithmic in
the key size, and `combine`/`map_filter` are linear and preserve
canonicity. This is the representation behind CompCert's `lib/Maps.v`
(`PTree`) since about 2021.

Options, in order of preference:

1. **Write our own** small module (a few hundred lines) following the paper,
   behind a module interface: `get`, `set`, `remove`, `combine`, `map_filter`,
   `fold`, `elements`, `extensionality`. It has no dependencies and we can tune
   its computational behaviour; for example, it can be made to reduce with `cbn`
   on concrete keys.
2. **Vendor CompCert's `lib/Maps.v`.** Its `PTree` module is the
   paper's implementation, with `PTree.extensionality` at line 626 of the
   current file. Unlike most of CompCert, files in `lib/` are dual-licensed
   under the INRIA non-commercial licence and **LGPL 2.1+**, so copying and
   adapting it is fine. The file is CompCert-flavoured (its own `Coqlib`,
   `ZMap`/`IMap`/`PMap` variants), so it would need trimming. It is a good
   reference even if we take option 1.
3. **Use stdpp's `gmap`/`Pmap`.** I believe stdpp's `Pmap` was rewritten on the
   same canonical representation around 2022, but verify this. It brings a
   large dependency and its own tactic conventions.

**Keys.** Use an injective encoding `option label → positive`: `None ↦ 1`, and
a string goes bitwise into a positive behind a tag bit. This makes the
hand-written ascii order in `Label.v` unnecessary. The map's key order replaces
the sorted lists that phase 5 struggled with.

### D3. Symbolic labels (the main risk)

Real proofs mention labels that are variables (`∀ x y, x ≠ y → …`).
`get (enc x) m` does not compute when `x` is abstract, and the sorted lists
had the same problem. Neither gives normalisation of symbolic expressions for
free. The plan:

- **Closed data** computes: tests, concrete examples, and the normaliser's
  internal workings.
- **Symbolic data** is handled in two ways:
  - by a small set of rewrite lemmas with `≠`/`=` side conditions on labels,
    with a `case_labels` tactic for the splits. This is the approach of
    `master` and `VarEquations.v`.
  - later, by the reflective normaliser (Stage 8). It reifies labels to atoms,
    computes with them as symbolic keys, and emits label-disequality side
    conditions.

**Spike this in Stage 2.** Before building on tries, check that a goal like
`apply (compose (open x) (close y)) z = …` with symbolic `x y z` can be driven
to a normal form by rewriting with side conditions. If the trie layer makes
that painful, consider exposing per-label *views* (`get_label l a`) as the only
interface the rewriting layer sees.

### D4. Per-label entry lists stay lists

The number of indices of one label touched by an adjustment is small, so `inc l`
stays a `list`. Lists are canonical with no extra work, and the trailing
transparent-entry condition is easy to state on them. Revisit only if profiling
says otherwise.

---

## Stages

Each stage has a deliverable and an exit criterion. Stages 0–4 are the first
milestone. Together they discharge the whole TODO list on `adjustments`
(428f1a4).

### Stage 0: environment and skeleton

- Rocq toolchain installed and reproducible; see [Environment](#environment).
- Build files, `theories/` layout, CI building on push, and a `README` stating
  the goal and pointing at the docs.
- Smoke test: build `Label.v` and `Var.v` from `adjustments`, plus the
  "probably builds" files from `next-unindexed`. This also confirms the claims
  in design history §9.

**Exit:** `make`/`dune build` of an empty `theories/` succeeds locally and in
CI.

### Stage 1: canonical maps (`theories/Map/`)

- `PTree`-style tries per D2, with the core lemmas: gss, gso, gempty, `combine`,
  `map_filter`, `extensionality`, and `fold`/`elements` with their specs.
- Key encodings: `positive` ↔ `option label` (injective, with a decoder or at
  least `enc_inj`), plus a `label_eq_dec` that computes.
- Tests: `Example`s by `vm_compute` / `reflexivity`.

**Exit:** `extensionality` is proved, and a benchmark-style `Example` with a few
thousand entries evaluates quickly under `vm_compute`.

### Stage 2: variables and the symbolic-label spike (`theories/Var.v`)

- Port `var := {v_label_opt; v_nat}`, `shift_var`/`unshift_var` and
  push/pop from `adjustments`/`next-unindexed`.
- Port only the `VarEquations.v` lemmas we need: the `case_vars` reductions
  and maybe the transpositions. The Coxeter material is probably unnecessary
  with composition by lookup.
- **Spike for D3:** prototype the rewrite-with-side-conditions workflow on a
  handful of symbolic goals before committing to the trie interface.

**Exit:** the spike's example goals are solved by a short tactic, or we have
a revised D3.

### Stage 3: raw renamings, computationally (`theories/RawAdjustment.v`)

- The raw data per D1, with payload type `P` (instantiated to `Empty_set` for
  now).
- Functions:
  - `wf : raw P → bool` (targets in range);
  - `apply : raw P → var → var + P`;
  - `normalize`;
  - `compose`, following OCaml 4ae82a85 `Simplified.compose`: lookup through
    the outer adjustment, append leftovers, then normalise;
  - `identity`;
  - smart constructors for the primitive operations (open, close, shift,
    rename, swap, weaken, and bound-variable variants).
- Executable tests that compose concrete adjustments and compare the results
  with `reflexivity`.

**Exit:** all functions are defined and computing, and the tests pass.

### Stage 4: canonicity and the user-facing type (`theories/Adjustment.v`)

- Write a **paper proof of canonicity first** (design history §7.3), then
  formalise it.
- Lemmas:
  - `apply_normalize : apply (normalize a) = apply a` (pointwise);
  - `normalize_normal`;
  - `apply_compose : apply (compose a b) v = apply a ∘ apply b` (pointwise,
    `Rename` case);
  - **canonicity**: `normal a → normal b → (∀ v, apply a v = apply b v) → a = b`.
- The type: `Record adjustment P := { raw : raw P; normal : is_normal raw }`,
  where `is_normal` is SProp-valued via `if … then sUnit else sEmpty`.
- From these, identity and associativity follow by canonicity, with no
  structural induction needed. Also derive "rewrite with any pointwise equation"
  lemmas.

**Exit:** the identity and associativity laws, and `apply_compose`, are proved
with `=`. This is the first milestone.

### Stage 5: the equational theory of renamings

- Express open, close, shift, rename, swap and weaken as adjustments, and
  state the classic laws from `master`'s `Var.v` and `Relative.v` (the
  `rw_ren_*` family, `swap_*`) as Leibniz equations. Most become
  `canonicity + case analysis`.
- Hint database and a `simpl_adjustments` tactic; the D3 workflow made robust.
- Optional: per-label view lemmas so users never see tries.

**Exit:** the renaming fragment of `master`'s lemma set is reproved, with no
setoids.

### Stage 6: substitutions

- Fix the term interface:
  - unindexed syntax with binders;
  - variables are `var`;
  - a `subst : adjustment term → term → term` with relative-monad-like laws.

  `Relative.v` on `master` and `Term.v` on `next` are the prior art. Probably
  start with a concrete λ-calculus, then generalise to a module type or
  typeclass.
- Composition for `Bind` payloads: `compose a b` must apply `a` to `b`'s
  payloads. This is the one structural difference from the OCaml version
  (design history §7.4 item 5).
- Redo Stage 4's laws for substitutions; canonicity carries over pointwise.

### Stage 7: term-level operations

- `[σ] t`, `open x t`, `close x t` and bind on terms, with the Leibniz versions
  of `master`'s term lemmas (`rw_push_open`, `rw_apply_comp`, …) and
  `next`'s `combine_open_renaming_close` family.

### Stage 8: the reflective normaliser

- A syntax of expressions over adjustments and term operations, with label and
  variable atoms; `denote`; `normalize` computing over symbolic keys; and
  soundness `denote (normalize e) = denote e` under generated label
  disequalities.
- A tactic `names` that reifies, normalises, and leaves side conditions for
  `congruence`/`easy`.
- Measure it against `master`'s `autorewrite`-based tactic on the same
  examples.

### Stage 9: the indexed layer

- SProp predicates for "uses at most *N* bound variables" on vars, terms and
  adjustments. Scoped types such as `term N := {t : term & wf N t}` (or a
  primitive-projection record), with equality still Leibniz because the proof
  component is SProp.
- Show that the operations preserve scoping, and give the indexed API
  (`open : term (S N) → term N`, …) as thin wrappers.

### Stage 10: contexts and the client

- Port `Context.v` (contexts keyed by shifted names, context morphisms
  `Γ =[σ]=> Δ`).
- Port `examples/Lambda.v`: STLC with universal `LAM`, weakening, substitution,
  Barendregt's lemma and CPS type preservation. **This is the acceptance
  test.**
- Port the TyDE examples, and compare proof size and run time with `master`.

### Stage 11: write-up

- Update the docs, clean up old `src/`, and possibly a paper or talk following
  the 2019 TyDE one.

---

## Risks and open questions

- **Symbolic labels (D3)** are the main technical risk. They decide how much
  of Stages 5 and 8 is pleasant.
- **Canonicity might need extra conditions** that the OCaml code never needed,
  because it never proved anything. The paper proof in Stage 4 resolves this
  early.
- **The term interface (Stage 6):** whether to go generic too early or stay
  concrete. Prefer concrete first.
- **Indexed vs unindexed for the user:** whether users mostly see the indexed
  layer (Stage 9) or the unindexed one. This decides how much polish each gets.

## What to reuse from the old branches

| Need | Source |
|---|---|
| `var`, labels, push/pop | `adjustments`: `src/Var.v`, `src/Label.v`; `next-unindexed`: `src/Var.v` |
| Case-split and reduction tactics on vars | `next-unindexed`: `src/VarEquations.v` (`case_vars`, `reduce_*`) |
| SProp-normalised record pattern, canonicity proof style | `next-unindexed`: `src/Renaming.v` (`is_normalized_equivalence_equal`), `src/ClosingEquations.v` |
| Composition and normalisation algorithms | `lpw25/ocaml` 4ae82a85: `typing/effect.ml`, `Adjustment.Simplified` |
| Lemma statements to reprove | `master`: `src/Var.v`, `src/Relative.v`, `TyDE-2019/Names.v` |
| Term interface | `master`: `src/Relative.v`; `next`: `src/Term.v` |
| Client and acceptance test | `master`: `examples/Lambda.v`, `src/Context.v` |

## Environment

See the section added to this file once the environment is set up
(Stage 0).
