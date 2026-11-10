# Shifted names

A Rocq library for name binding that combines locally nameless binders with
free names that carry a *shift index* (`x₍ᵢ₎` is "the `x` that is `i` binders
of `x` further out"), so that opening a binder never needs a freshness side
condition.

- [`docs/design-history.md`](docs/design-history.md) traces how the design
  evolved across the branches of this repository (and its use in an OCaml
  effect system).
- [`docs/design.md`](docs/design.md) describes the current
  design: the substitution interface, the representation of adjustments,
  composition and the costs of the operations.
- [`docs/implementation-plan.md`](docs/implementation-plan.md) is the
  overall plan, including the later stages (context form, normaliser).

## Layout

- `theories/Core/`: the internal, unindexed core, then the public layer:
  - `Trie.v`: canonical binary tries (Appel & Leroy), with extensionality.
  - `Counts.v`, `Based.v`: weakening counts (canonical count maps) and
    elements stored relative to a base.
  - `Skew.v`, `ATrie.v`: skew-binary sequences and label tries whose nodes
    carry weakening counts; `Prune.v`: maps over them that move a subtree
    by its counts alone when the function is a pure shift there.
  - `Repr.v`: the representation of adjustments (per-label targets naming
    output variables directly, weakenings applied lazily through counts),
    its meaning `napply` and its normal form; `Point.v`: identity, weaken,
    extend and lift; `Deep.v`: deep well-formedness as a structural check.
  - `Compose.v`: pruned eager composition and its correctness.
  - `Lookup.v`: lookups with continuations, used by substitution.
  - `Label.v`, `Var.v`: labels with trie keys, variables.
  - `Strict.v`: booleans as strict propositions.
  - `Adjustment.v`: raw adjustments `radj T`, records with an SProp proof of
    deep well-formedness so equality is Leibniz: `rapply`,
    `rextensionality` and the constructors (`ridentity`, `rcompose`,
    `rpush_inner`, `rpush_outer`, `rlift`).  Raw names carry an `r` prefix;
    the indexed layer takes the plain names.
  - `Laws.v`: the equational laws of the raw constructors.
  - `Scoped.v`: scoping of adjustments (from `N` to `M` bound variables),
    checked on the data, with preservation by every constructor.
  - `Indexed.v`: the public indexed types `adj T N M`, `var`, `padj`,
    `target`; context forms (`⟦ a as x | Γ \ b as x | Γ[σ] ⟧`, short
    `⟦ · | σ ⟧`), composition `∘`, and their laws.
  - `Normalise.v`, `Names.v`: the reflective normaliser and the `names`
    tactic, which proves equations between indexed adjustments.
  - `Syntax.v`, `Subst.v`: the interface a syntax implements (one Kleisli
    extension and its laws) and the substitution functor over it.
- `theories/Examples/Lambda.v`: the λ-calculus as a client of the library.
- `theories/Extraction/Extraction.v`: extraction settings (Zarith numbers,
  native strings); `tests/extraction/run.sh` extracts the λ example,
  compiles it and runs a smoke test.
- `theories/Tests/`: executable tests.
- `src/`, `examples/`, `TyDE-2019/`: the original 2019 development, kept for
  reference.

## Building

Requires Rocq 9.2 with its stdlib (`opam install rocq-prover.9.2.0`, or
`scripts/install-rocq.sh` to build from source on Ubuntu). Then:

```bash
make
```
