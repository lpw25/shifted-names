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
  - `Slots.v`: the flat canonical representation (per-label input targets
    and output slot counts), with `push_outer`, `push_inner` (any variable
    target), composition, restriction and the canonicity theorem; generic in
    the payload type.
  - `Nested.v`: payloads `(u, ρ)` of a closed term and a lazily applied
    adjustment; nested composition, payload canonicity, depth bounds.
  - `Adjustment.v`: the user-facing records (SProp normality, so equality is
    Leibniz), `apply`, extensionality and the context-form constructors
    (`identity`, `compose`, `push_inner`, `push_outer`, `lift`).
  - `Laws.v`: the equational laws of the constructors and the primitive
    adjustments (`shift`, `rename1`, `open`, `close`, `swap`, `subst1`).
  - `Scoped.v`: scoping of adjustments (from `N` to `M` bound variables),
    checked on the data, with preservation by every constructor.
  - `Indexed.v`: the public scoped types `sadj T N M`, `svar`, `spadj`,
    `starget`, their constructors and laws.
- `theories/Examples/`: a concrete λ-calculus built on the core (a test
  instance; the library itself does not fix a term language):
  `LambdaCore.v` (unindexed terms and the substitution laws) and `Lambda.v`
  (scoped terms `tm N` and substitutions on the public layer).
- `theories/Tests/`: executable tests.
- `src/`, `examples/`, `TyDE-2019/`: the original 2019 development, kept for
  reference.

## Building

Requires Rocq 9.2 with its stdlib (`opam install rocq-prover.9.2.0`, or
`scripts/install-rocq.sh` to build from source on Ubuntu). Then:

```bash
make
```
