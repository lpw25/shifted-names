# Segments as probes

Where the canonicity work stands after `docs/eta.md`. A *segment* is a
word of entries and weakenings between atoms. Everything here is about
segments; atoms separate them and reveal the rest of the word
completely.

## The meaning of a segment

**The group.** Let `A` be the right-angled Artin group on the labels:

- a weakening `⟦ \ g ⟧` is the letter `g`;
- an entry on `g` is `g⁻¹`;
- two labels commute exactly when the facts order them.

A word then traces a path in `A`. Its *position* after `t` steps is the
product of the first `t` letters.

**Extend each model.** Give every label fresh variables at negative
indices, belonging to that label only. Then:

- every label acts as a bijection, so `A` acts on the variables;
- a weakening is the action of `g` restricted to the old variables;
- an entry is the action of `g⁻¹`, except at `g₀`, which it would send
  to `g₋₁`: that is where it consumes.

**So a segment is its endpoint and a list of probes** (checked against
the step semantics on 540,000 cases; scratch `probe.py`):

- the *endpoint* `x` is the product of all its letters;
- each entry on `g` at position `X` with target `v` is a *probe*
  `(g, X, v)`. It catches the input `g₀·X⁻¹`;
- an input is consumed by the first probe that catches it, with that
  probe's target, and otherwise leaves at `y·x`.

**E-unitarity.** Two words with the same endpoint send every input
that neither consumes to the same place.

## The canonical form of a segment

- **The endpoint,** as a reduced word in `A`.
- **The live probes:**
  - drop dead probes: `(g, X)` is dead when `X` reduces to `Y·g·c` with
    `c` commuting with `g`. This is the characterisation of
    `docs/eta.md`;
  - drop a probe whose point equals an earlier probe's, meaning same
    label and same coset `X·C_g`, where `C_g` is the subgroup of
    letters commuting with `g`;
  - put them in the lexicographic normal form of the *trace*: two
    probes may swap unless they *conflict*, that is, unless their
    targets differ and some input can reach both.

**Two new identities, besides beta and eta:**

1. **Probes with equal targets commute.** Example:
   `E_a(v) ⨾ ⟦ \ a ⟧ ⨾ E_b(v) ⨾ ⟦ \ b ⟧ = E_b(v) ⨾ ⟦ \ b ⟧ ⨾ E_a(v) ⨾ ⟦ \ a ⟧`
   for unordered `a`, `b`, because each `E_g(v) ⨾ ⟦ \ g ⟧` is an
   idempotent. Repeated targets do arise: two contractions into the
   same variable, or the same term in two entries. The hash-consed
   normal form misses this. The search found 39 such pairs in two
   labels up to 6 steps.
2. **Probes that can never meet commute,** whatever their targets.

**Search** (scratch `pnf.py`). With a sampled approximation of "can
meet", this form has exactly as many keys as there are semantic
classes in every configuration tried, with repeated targets:

| Labels | Facts | Steps | Targets | Classes |
|---|---|---|---|---|
| two | none | up to 6 | one | 2,646 |
| two | none | up to 5 | two | 5,621 |
| three | none | up to 4 | two | 5,827 |
| three | `a < c` | up to 5 | two | 27,548 |
| three | `a < c, b < c` | up to 4 | two | 2,111 |
| three | `a < b < c` | up to 4 | two | 955 |

These words are too short for the next problem.

## Conflicts depend on context

Whether two probes may swap is not a property of the pair. It depends
on which earlier probes already catch their common inputs.

**Example** (`Core/HEtaGap.v`, distinct targets). Write `En h n` for
the entry sending `h₀` to `·ₙ`, and `W h` for `⟦ \ h ⟧`.

```
r1 = W b ⨾ W b ⨾ En a 5 ⨾ W a ⨾ En b 2 ⨾ En b 3 ⨾ En a 0 ⨾ W a ⨾ W b ⨾ En a 7 ⨾ W a
r2 = W b ⨾ W b ⨾ En a 5 ⨾ W a ⨾ En b 2 ⨾ En a 7 ⨾ W a ⨾ En b 3 ⨾ En a 0 ⨾ W a ⨾ W b
```

The live probes are the same three in both words:

| Probe | Label | Position | Point | Target |
|---|---|---|---|---|
| `k` | `a` | `bb` | `a₀·b⁻²` | 5 |
| `i` | `a` | `1` | `a₀` | 0 |
| `j` | `a` | `b` | `a₀·b⁻¹` | 7 |

- In `r1` they come in the order `k, i, j`; in `r2`, `k, j, i`.
- `i` and `j` meet exactly when `a₀` is not on `b`. Without `k`, the
  two orders differ.
- But whenever `a₀` is not on `b`, `k`'s point is `a₀` too, and `k`
  comes first in both.

So `r1` and `r2` are equal in every model (`r1_r2`). Yet `i` and `j`
conflict as a pair, so a pairwise trace normal form keeps them apart,
and so do `HNorm` and the eta pass (`he_r1_r2`). The same file proves
the simplest equal-target swap (`t1_t2`, `he_t1_t2`).

**What a canonical order needs.**

- The meaning of a probe list `L` is: for each model and each original
  input `y`, the target of the first probe that `y` realises.
- `p` may come next after an already-placed prefix `O` exactly when no
  model and input `y` has all of:
  - `y` realises `p`;
  - `y` realises nothing in `O`;
  - `y`'s first probe in `L` has a target other than `p`'s.
- With this test, the lexicographically least valid order is canonical
  by definition, and greedy choice finds it.
- If the current order is kept as a word, "`y`'s first probe in `L` is
  `q`" means that `y`'s walk along the word stays at non-negative
  indices up to `q`. The test is then, for each earlier `q` with a
  different target: is there a model with `y` caught by `q` whose point
  is also `p`'s point?

**This is a satisfiability question over models.**

- It is liveness (`docs/eta.md`) plus one identification of points.
- The exact solver (scratch `csolve.py`) decides it by search over
  partitions of label positions. No characterisation like the one for
  liveness is known, and its cost is unknown.
- The canonical probe set raises the same question: a probe live in
  one word may be replaced, in an equal word, by a different probe that
  catches the same inputs with the same target.

## When can two probes meet?

Without context: probes `(g, X)` and `(h, Y)` meet in a model when
`g₀·X⁻¹ = h₀·Y⁻¹` and that variable has a non-negative index.

**No simple rule decides it.** Two cheap sound tests suffice in every
search above:

- the same position on ordered labels;
- `X⁻¹Y` forcing the walk onto one chain.

But they are not complete. Here are two words, equal in all 3,009 test
models, with the same probes in different orders:

```
A = ⟦\a⟧⟦\a⟧⟦\b⟧ E_a(0) ⟦\a⟧ E_b(9) E_b(0) E_a(1) ⟦\a⟧⟦\b⟧⟦\b⟧
B = ⟦\a⟧⟦\a⟧ E_b(0) E_a(1) ⟦\a⟧⟦\b⟧⟦\b⟧ E_a(0) ⟦\a⟧
```

Here `E_g(v)` is an entry on `g` with target `v`.

- Probe `r` is at `aab` with target 0, and probe `p` at `aab⁻¹` with
  target 1. Their points are equal only when `a₀` is not on `b`, and
  then both are `a₋₂`, a negative index.
- The cheap tests do not see this, so they keep `A` and `B` apart.

## What this means for the plan

- **`HNorm` plus eta is not canonical** (`Core/HEtaGap.v`), with
  repeated targets and without.
- **A canonical form needs an order decided in context:** each step of
  the greedy order asks whether some model makes an input caught by one
  probe meet another probe's point.
- **Open:** a characterisation of that question, and its cost; whether
  the canonical probe set is determined the same way; and printing a
  reordered probe list as a word without adding live probes.
