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

## When can two probes meet?

**Only fresh catches matter.** An input whose walk to probe `p` dips
below index 0 is caught on the way, by a probe that is always earlier
in the list. That probe is a backward step on every path to `p`'s
position, a wall of the Cayley complex. So two probes conflict exactly
when some input reaches both without ever going negative.

**This reduces to one walk.** Probes `(g, X)` and `(h, Y)` can meet
exactly when the walk from `g₀` along `X⁻¹·Y` (the letters as written,
not reduced) can stay at non-negative indices and end at `h₀`.
Liveness is the special case without a target.

**An exact solver exists** (scratch `csolve.py`): it builds the model
lazily as a partition of label positions. It shows that sampling misses
real coincidences (26 of 3,160 pairs in two labels).

**No simple rule is enough.** Two cheap sound tests suffice in every
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
  target 1. They can meet only in models where `a₀` is not on `b`, and
  there the meeting point is `a₋₂`, a negative index.
- The cheap tests do not see this, so they keep `A` and `B` apart.
- The difference only matters because `r`'s target equals that of the
  probe `(b, aa)`, so the two can swap.

**A candidate decision procedure.**

- Any model where the walk reaches `h₀` makes `g₀·c = h₀`, for
  `c = X⁻¹Y` reduced.
- Take the most general model with that one identification, and check
  that the walk survives in it.
- In the model with no identification this gives exactly the liveness
  characterisation: the only variable at index 0 that the walk can
  meet is `g₀`. With the identification, `g₀` is fixed by
  `C_g ∪ c·C_h·c⁻¹`, so deciding survival needs membership in the
  subgroup that generates, and a consistency check.

Not yet worked out, implemented or proved.

## What this means for the plan

- **The hash-consed normal form plus eta is not canonical** once
  targets repeat.
- **A canonical form must order probes by exact conflict.** That needs
  the decision procedure above. Its cost, and whether the normaliser
  stays quadratic, are open.
- **The uniqueness proof** would go through the probe semantics:
  - E-unitarity;
  - liveness, the characterisation in `docs/eta.md`;
  - the meeting criterion;
  - constructing models in which given probes are realised apart or
    together.
