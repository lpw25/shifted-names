# Shifted names

A Rocq library for name binding that combines locally nameless binders with
free names that carry a *shift index* (`x₍ᵢ₎` is "the `x` that is `i` binders
of `x` further out"), so that opening a binder never needs a freshness side
condition.

- [`docs/design-history.md`](docs/design-history.md) traces how the design
  evolved across the branches of this repository (and its use in an OCaml
  effect system).
- [`docs/implementation-plan.md`](docs/implementation-plan.md) is the plan for
  the current development.

## Layout

- `theories/Core/`: the internal, unindexed core:
  - `Trie.v`: canonical binary tries (Appel & Leroy), with extensionality.
  - `Label.v`: labels, their strict order and trie keys.
  - `Var.v`: variables (a label plus a shift index).
  - `RawAdjustment.v`: per-label adjustments (renamings and substitutions):
    composition, normalisation and canonicity.
  - `Adjustment.v`: normal adjustments as a record with an SProp proof, so the
    laws hold up to Leibniz equality; the context-form constructors
    (`identity`, `push_inner`, `push_outer`); the primitive adjustments;
    lifting under a binder.
  - `Laws.v`: the equational laws of the constructors.
  - `CForm.v`: a concrete context-form datatype (groundwork for the
    normaliser).
- `theories/Examples/`: a concrete λ-calculus built on the core (a test
  instance; the library itself does not fix a term language):
  `LambdaCore.v` (unindexed terms and the substitution laws),
  `LambdaScope.v` (scoping), `Lambda.v` (scoped terms and substitutions).
- `theories/Tests/`: executable tests.
- `src/`, `examples/`, `TyDE-2019/`: the original 2019 development, kept for
  reference.

## Building

Requires Rocq 9.2 with its stdlib (`opam install rocq-prover.9.2.0`, or
`scripts/install-rocq.sh` to build from source on Ubuntu). Then:

```bash
make
```
