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
- A **context form** for adjustments that has a normal form even when the
  relationship between some labels is unknown. It is the basis for printing,
  parsing and the reflective normaliser.
- A reflective normaliser, ideally proved to produce an actual normal form.
- **An indexed (scoped) user-facing library.** The unindexed core exists only to
  make our own proofs easier and must not leak into the public API.
- Terms, contexts, and the `examples/Lambda.v` client from `master` as the
  acceptance test.

**Non-goals for now:** the effect-system extras from the OCaml variant
(`Unknown`/`Top`, `Meet`, residuals, factors), and backwards compatibility with
any old branch.

## Ground rules

- **Toolchain:** Rocq 9.x (stdlib as a separate package); see
  [Environment](#environment). Build with `dune` (`rocq` stanzas) or
  `_RocqProject` + `rocq makefile`; whichever we pick, CI runs it.
- **No dependencies** beyond Rocq and its stdlib. In particular, we write our
  own canonical trie rather than using CompCert or stdpp.
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
- **Encapsulation:**
  - The unindexed core lives in internal modules.
  - Public modules expose only indexed types, operations, lemmas and tactics.
  - Users never need to unfold through the public layer to the core. The
    sealing mechanism (sealed `Module Type`s, opaque definitions, or private
    namespaces) is fixed in Stage 8 and then applied everywhere.

---

## Key design decisions

### D1. Per-label adjustments (the underlying representation)

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

This representation is efficient and easy to prove things about. It needs
concrete labels to compute.

### D2. Our own canonical maps: Appel & Leroy's extensional binary tries

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
invariant. An adjustment's canonicity then reduces to canonicity of its
per-label entries. Operations are logarithmic in the key size, and
`combine`/`map_filter` are linear and preserve canonicity.

**We write our own module** (a few hundred lines) following the paper, behind
a small interface: `get`, `set`, `remove`, `combine`, `map_filter`, `fold`,
`elements`, `extensionality`. It must compute well with `cbn` and `vm_compute`
on concrete keys. CompCert's `lib/Maps.v` (`PTree`, LGPL 2.1+) is the paper's
implementation and is useful as a reading reference; we do not depend on it.

**Keys:** an injective encoding `option label → positive`: `None ↦ 1`, and a
string goes bitwise into a positive behind a tag bit.

### D3. Symbolic labels: the context form

Real proofs mention labels that are variables (`∀ x y, …`), and the per-label
representation cannot compute with them. Instead of forcing symbolic goals
through it, we add a second representation of the *same* adjustments.

**Context form.** An adjustment is written as:

- an **input context**: an ordered list of entries `(l, b)`, innermost first,
  where `b` is either a reference to an entry of the output context (renaming)
  or a payload term (substitution);
- an **output context**: an ordered list of labels;
- an **implicit tail**: everything beyond the input context maps to everything
  beyond the output context.

`x₍ᵢ₎` resolves by counting the entries labelled `x`:

- if the input context has more than `i` entries labelled `x`, it is the
  `(i+1)`-th of them;
- otherwise it is in the tail, shifted by the number of `x`s in each context.

This is how the OCaml `parse ~outer ~inner` already presents adjustments.

**Reordering needs ordering facts.** Two adjacent input entries with labels
`x` and `y` can be swapped only if `x ≠ y` is known, because swapping changes
which entry `x₍₀₎` refers to. The same holds for output entries.

**Normal form with partial knowledge.**

- Reorder adjacent entries only when their labels are related by a *known*
  strict order `x < y`, and then always into ascending order.
- Leave entries whose labels have no known relation in place.
- Also drop transparent entries, the D1 condition read in context form.

**Why `<` and not `≠`.** Knowing only `x ≠ y` makes both orders legal, so there
is no canonical choice. Knowing `x < y` picks one. So side conditions and
hypotheses throughout the library are stated with the strict order `<` on
labels, a total order that computes on concrete labels, rather than with `≠`.

**Roles.**

- The context form is **not** the underlying representation: it is less
  efficient and harder to prove things about.
- It is the basis for **printing and parsing**. Notations parse to it, and
  results print from it, so users see contexts, not tries.
- It is the basis for the **reflective normaliser** (Stage 9): reified
  expressions with label atoms are normalised in context form under the
  hypotheses `x < y` available in the goal.
- **Target theorem:** normalised context forms are unique. If two normal forms
  denote the same adjustment under every instantiation of the atoms consistent
  with the known `<` facts, they are syntactically equal. Soundness alone is
  the fallback, but we aim for this.
- **Bridge:** for concrete labels, a fully sorted normal context form
  corresponds one-to-one with a normal D1 adjustment. `to_context` and
  `of_context` are proved inverse there.

### D4. Per-label entry lists stay lists

The number of indices of one label touched by an adjustment is small, so `inc l`
stays a `list`. Lists are canonical with no extra work, and the trailing
transparent-entry condition is easy to state on them. Revisit only if profiling
says otherwise.

### D5. Users see only the indexed form

Scoped terms and adjustments (indexed by the number of bound names), built as
the unindexed core plus SProp well-scopedness proofs, are the only thing in
the public API. The unindexed core is an implementation device for our proofs.
Consequences:

- Every public lemma is stated on indexed types.
- The normaliser tactic works on indexed goals and goes through the core
  internally.
- Printing shows indexed objects in context form.
- Stages 5–7 build internal theory; Stage 8 builds the public surface.

---

## Stages

Each stage has a deliverable and an exit criterion. Stages 0–4 are the first
milestone. Together they discharge the whole TODO list on `adjustments`
(428f1a4).

### Stage 0: environment and skeleton

- The Rocq toolchain is set up; see [Environment](#environment).
- Build files, `theories/` layout (separate `Core/` (internal) and public
  directories from the start), CI building on push, and a `README` stating the
  goal and pointing at the docs.

**Exit:** the build of an empty `theories/` succeeds locally and in CI.

### Stage 1: canonical maps (`theories/Core/Trie.v`)

- Our own Appel–Leroy trie per D2, with the core lemmas: gss, gso, gempty,
  `combine`, `map_filter`, `extensionality`, and `fold`/`elements` with their
  specs.
- Key encodings: `positive` ↔ `option label` (injective, with a decoder or at
  least `enc_inj`).
- Tests: `Example`s by `vm_compute` / `reflexivity`.

**Exit:** `extensionality` is proved, and an `Example` with a few thousand
entries evaluates quickly under `vm_compute`.

### Stage 2: labels and variables (`theories/Core/Label.v`, `Var.v`)

- **Labels:** a decidable strict total order `<` that computes on concrete
  labels, with its order lemmas. It is the vocabulary for all symbolic side
  conditions (D3). `Label.v` from `adjustments` is the starting point.
- **Variables:** port `var := {v_label_opt; v_nat}`, `shift_var`/`unshift_var`
  and push/pop from `adjustments`/`next-unindexed`. Port only the
  `VarEquations.v` lemmas we need, restating `≠` side conditions with `<` where
  that is the natural form.

**Exit:** the ported var lemmas are proved, with a `case_labels` tactic that
splits on `<`/`=`/`>`.

### Stage 3: raw adjustments, computationally (`theories/Core/RawAdjustment.v`)

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

### Stage 4: canonicity and the core type (`theories/Core/Adjustment.v`)

- Write a **paper proof of canonicity first** (design history §7.3), then
  formalise it.
- Lemmas:
  - `apply_normalize`;
  - `normalize_normal`;
  - `apply_compose` (pointwise);
  - **canonicity**: `normal a → normal b → (∀ v, apply a v = apply b v) → a = b`.
- The type: `Record adjustment P := { raw : raw P; normal : is_normal raw }`,
  where `is_normal` is SProp-valued.
- Identity and associativity follow by canonicity.

**Exit:** the identity and associativity laws, and `apply_compose`, are proved
with `=`. This is the first milestone.

### Stage 5: context form, printing and parsing (`theories/Core/Context.v`)

- The context-form syntax (D3), first with concrete labels, and its semantics
  as a function on variables.
- `to_context` (per-label → sorted context form) and `of_context`. Prove them
  inverse on normal forms, and prove that both preserve semantics.
- Notations: parse adjustment literals written as input/output contexts, and
  print adjustments back in that form. Design the concrete syntax here,
  perhaps modelled on the OCaml `outer`/`inner` lists.
- Context-form normalisation with *concrete* labels, as a first test of the
  normal-form proof structure that Stage 9 generalises.

**Exit:** `Check`/`Compute` on adjustments prints in context form, and literals
parse.

### Stage 6: the equational theory of renamings (internal)

- Express open, close, shift, rename, swap and weaken as adjustments, and
  state the classic laws from `master`'s `Var.v` and `Relative.v` (the
  `rw_ren_*` family, `swap_*`) as Leibniz equations with `<` side conditions.
  Most become `canonicity + case analysis`.
- A hint database and a provisional `simpl_adjustments` tactic. It is a
  stopgap until the normaliser exists.

**Exit:** the renaming fragment of `master`'s lemma set is reproved, with no
setoids.

### Stage 7: substitutions and terms (internal)

- Fix the internal term interface:
  - unindexed syntax with binders;
  - variables are `var`;
  - `subst : adjustment term → term → term` with relative-monad-like laws.

  `Relative.v` on `master` and `Term.v` on `next` are the prior art. Start with
  a concrete λ-calculus, then generalise.
- Composition for `Bind` payloads: `compose a b` must apply `a` to `b`'s
  payloads (design history §7.4 item 5). Redo Stage 4's laws for
  substitutions.
- Term-level operations `[σ] t`, `open x t`, `close x t` and bind, with the
  Leibniz versions of `master`'s term lemmas and `next`'s
  `combine_open_renaming_close` family.

### Stage 8: the indexed public layer

- SProp well-scopedness predicates on vars, terms and adjustments. Scoped
  types such as `term N` (primitive-projection records of core data plus SProp
  proof), so that equality stays Leibniz.
- Show that every operation preserves scoping, and give the public API
  (`open : term (S N) → term N`, `[σ] : term N → term M`, …) with all lemmas
  restated on indexed types.
- Fix the encapsulation mechanism (ground rules) and audit that nothing
  unindexed is reachable from the public modules.

**Exit:** the Stage 6 and 7 lemma sets are available in indexed form, and a
client file that imports only public modules can state and prove them.

### Stage 9: the reflective normaliser

- **Reification** of indexed goal expressions (adjustments, compositions,
  term operations) into a syntax with label atoms and the `<` facts found in
  the context.
- **Normalisation** in context form (D3): compute compositions by context
  manipulation, reorder only under known `<`, drop transparent entries.
- **Soundness:** `denote (normalize e) = denote e`.
- **Uniqueness of normal forms**, as stated in D3. This is the target theorem.
- **Tactic:** a `names` tactic for users that reifies, normalises both sides
  and closes or simplifies the goal, reporting missing `<` facts it would have
  needed.
- Measure it against `master`'s `autorewrite`-based tactic on the same
  examples.

### Stage 10: contexts and the client

- Port `Context.v` (typing contexts keyed by shifted names, context morphisms
  `Γ =[σ]=> Δ`) onto the indexed layer.
- Port `examples/Lambda.v`: STLC with universal `LAM`, weakening, substitution,
  Barendregt's lemma and CPS type preservation, using only public modules.
  **This is the acceptance test.**
- Port the TyDE examples, and compare proof size and run time with `master`.

### Stage 11: write-up

- Update the docs, clean up old `src/`, and possibly a paper or talk following
  the 2019 TyDE one.

---

## Risks and open questions

- **Uniqueness of context-form normal forms (D3)** under partial order
  knowledge is the main theoretical risk. Prove it first in the concrete case
  (Stage 5), then generalise (Stage 9). If it fails, soundness plus a useful
  normal-ish form is the fallback.
- **Canonicity might need extra conditions** that the OCaml code never needed,
  because it never proved anything. The paper proof in Stage 4 resolves this
  early.
- **The term interface (Stage 7):** whether to go generic too early or stay
  concrete. Prefer concrete first.
- **Leakage:** keeping the unindexed core fully hidden while letting the
  normaliser and printing work on indexed goals may need care with reduction
  behaviour (opaque vs transparent definitions under `vm_compute`).

## What to reuse from the old branches

| Need | Source |
|---|---|
| `var`, labels, label order, push/pop | `adjustments`: `src/Var.v`, `src/Label.v`; `next-unindexed`: `src/Var.v` |
| Case-split and reduction tactics on vars | `next-unindexed`: `src/VarEquations.v` (`case_vars`, `reduce_*`) |
| SProp-normalised record pattern, canonicity proof style | `next-unindexed`: `src/Renaming.v` (`is_normalized_equivalence_equal`), `src/ClosingEquations.v` |
| Composition and normalisation algorithms | `lpw25/ocaml` 4ae82a85: `typing/effect.ml`, `Adjustment.Simplified` |
| Context-form syntax (outer/inner) | `lpw25/ocaml` tip: `typing/effect.mli`, `Adjustment.parse`, `Adjustment.Desc` |
| Trie reference implementation (reading only) | CompCert `lib/Maps.v`, `PTree` |
| Lemma statements to reprove | `master`: `src/Var.v`, `src/Relative.v`, `TyDE-2019/Names.v` |
| Term interface | `master`: `src/Relative.v`; `next`: `src/Term.v` |
| Client and acceptance test | `master`: `examples/Lambda.v`, `src/Context.v` |

## Environment

**Toolchain:** Rocq 9.2.0 with stdlib 9.2.0, OCaml 4.14.1 and dune 3.14. The
native compiler is disabled (`vm_compute` works; `native_compute` falls back
to the VM).

**Cloud sessions** (claude.ai/code). Use the personal environment
`shifted-names`. Its setup script runs whenever a fresh container is built. It
installs Ubuntu's `ocaml-nox`, `ocaml-dune`, `libzarith-ocaml-dev` and
`ocaml-findlib`, then builds Rocq and the stdlib from the `V9.2.0` tags of
`github.com/rocq-prover/rocq` and `github.com/rocq-prover/stdlib`, installing
into `/usr/local`. This takes about 4 minutes. opam is not used because
`opam.ocaml.org` and GitHub release tarballs are not reachable from the cloud
network policy, but `git clone` from GitHub is.

**Locally:**

```bash
opam install rocq-prover.9.2.0
```

`rocq-prover` pulls in the matching stdlib.

**Quick check:**

```bash
rocq c -R src SNames src/Label.v
```

The old sources compile with deprecation warnings (`Require Import String` →
`From Stdlib Require Import String`). New code should use `From Stdlib`.
