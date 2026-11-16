# Beta and eta for the hash-consed normal form

`HNorm` (`docs/hnorm.md`) applies the *beta*-like rules:

- cancellation: `⟦ \ h ⟧` then an entry on `h`;
- commutation of steps on labels ordered by the facts;
- lookups.

It is not canonical (`Core/HNormGap.v`). What it misses is an *eta*-like
rule, of which its absorption rule and `clean` are special cases.
The plan is to keep the beta normaliser as it is and add eta as a
second pass that creates no new beta redexes.

Notation as in `Core/Indexed.v`. In the examples, `a`, `b`, `c`, … are
label atoms, and `⟦ h as v; · as v \ · as v ⟧` is the entry sending
`h₀` to the existing variable `·₀`.

## The eta rule

An entry on `h` is **dead** when, in every model, no variable that
matters reaches `h₀` just before it. Then:

- **followed by a weakening on `h`:** the two steps do nothing on the
  variables that reach them, so both go. Absorption is the case where
  the target equals what reaches `h₀`; this is the case where nothing
  does;
- **otherwise:** the entry still shifts `h`, but its target is never
  used, so it gets a canonical target.

**Which variables matter** depends on how the word is used:

- **a whole result:** every input variable;
- **the payload of a term without a payload atom:** named inputs only.
  `clean`, which drops bound-label steps before the first atom, is this
  case;
- **the word of a stuck lookup:** only what the looked-up variable can
  reach. Example, with facts `h < c`, `g < c`, `y < c`:

  ```
  C = ⟦ c as v; · as v \ · as v ⟧        Y = ⟦ y as v; h as v \ h as v ⟧
  C ⨾ Y ⨾ ⟦ g := u ⟧  =  Y ⨾ C ⨾ ⟦ g := u ⟧
  ```

  `HNorm` gives the two sides lookups of `h₀` stuck at the step on `g`,
  and the words of those lookups differ by the step on `c`. But `h₀`'s
  walk can never reach `c`.

**After an atom everything matters again.** An atom's result carries
the rest of the word as a function, compared on every variable. So the
question only arises within a *segment*: from the start of the word,
or from the last atom, up to the entry.

## When is `h₀` unreachable?

Read a segment as a word in the right-angled Artin group whose
generators are the labels:

- a weakening `⟦ \ g ⟧` is `g`;
- an entry on `g` is `g⁻¹`;
- two labels commute exactly when the facts order them.

> **Characterisation (conjectured, checked).** `h₀` is unreachable
> just before step `i` of a segment, from every input, exactly when
> there is a weakening `⟦ \ h ⟧` at some step `t < i` such that the
> window `t+1 … i−1` reduces, in that group, to a word on labels
> ordered against `h` only.

**Why it is plausible.**

- **Easy direction.** Every cancelled pair acts as the identity, apart
  from consuming an index 0, which only kills a walk. Steps on labels
  ordered against `h` never move `h₀`. So a reducible window sends
  `h₀` back to itself or kills it, and the weakening at `t` leaves
  nothing there.
- **Other direction.** Steer: walk back from `h₀`, building the model
  as you go. At a step on a label not ordered against the current one,
  put the variable on that label at a fresh, large index. It then dies
  only at index 0 of `h`, and it returns to `h` exactly when the steps
  it passed reduce to nothing. That is the reduction in the group. Not
  yet written out as a proof.

**Evidence.** An exact solver (scratch `reach.py`) walks back from `h₀`
and searches every choice of model. It agrees with sampling 300 models
on every case tried:

| Labels | Facts | Steps | Cases |
|---|---|---|---|
| `a, b` | none | up to 5 | about 15,500 |
| `a, b, c` | `a < c` | up to 4 | about 22,400 |

The characterisation (scratch `hyp3.py`) agrees with the solver on
every case tried, about 680,000 in all:

| Labels | Facts | Steps |
|---|---|---|
| `a, b` | none | up to 6 |
| `a, b, c` | none; `a < c`; `a < c, b < c`; `a < b < c` | up to 5 |
| `a, b, c, d` | none; `a < c, b < d` | up to 4 |

Example, with `B = ⟦ b as v; · as v \ · as v ⟧` and
`A = ⟦ a as v; · as v \ · as v ⟧`:

- in `⟦ \ a ⟧ ⨾ B ⨾ ⟦ \ b ⟧ ⨾ A`, the window after `⟦ \ a ⟧` is
  `b⁻¹ b`, which is trivial, so `A` is dead;
- in `⟦ \ a ⟧ ⨾ ⟦ \ b ⟧ ⨾ A`, the window is `b`, which is not. Indeed a
  model where `b` overlaps `a` at an offset refills `a₀`.

## The second pass

Repeat until nothing changes, then give the dead entries that remain a
canonical target:

- remove a dead entry together with the weakening on its label right
  after it;
- cancel a weakening directly followed by an entry on its label (beta),
  where a removal has made them adjacent. Example:
  `⟦ \ a ⟧ ⨾ B ⨾ ⟦ \ b ⟧ ⨾ A ⨾ ⟦ \ a ⟧ ⨾ B`. Removing the dead pair
  `A ⨾ ⟦ \ a ⟧` makes `⟦ \ b ⟧ ⨾ B` adjacent, and that `B` was dead
  too.

Removing a pair that is the identity on every variable reaching it
does not change which other entries are dead, so the pass is
well-defined.

**Search** (scratch `eta.py`). Over sorted, reduced words with distinct
variables as targets, the pass leaves no two different words that
agree in all the sampled models, and no removal ever broke the sorting:

| Labels | Facts | Steps | Words after the pass | Collisions |
|---|---|---|---|---|
| `a, b` | none | up to 7 | 26,043 | 0 |
| `a, b, c` | none | up to 5 | 6,670 | 0 |
| `a, b, c` | `a < c` | up to 5 | 3,884 | 0 |

## Search over the normaliser's real outputs

`Core/HEta.v` implements the pass after `HNorm`, with the inputs that
matter per use:

- **all inputs** for whole results;
- **named inputs** for term payloads without a payload atom;
- **one variable** for stuck lookups. Before the first atom, a step on
  a label the walk can never be on goes. The walk can reach a label
  once a step on it comes while the walk may be on a label not ordered
  against it.

Absorption is checked again after the pass, against the eta-normal
lookup.

**The harness** (scratch `es/`):

- random expressions over label atoms `a, b, c` and the bound label,
  with terms, payloads, atoms and lifts;
- their meanings in about 30 finite interleaved models built from
  identification lists (`IFinite.v`), compared on 20 variables each and
  hashed;
- expressions with equal meanings in all of them must get the same
  normal form, and the other way round.

**The first runs** (3000 expressions in all) found two expressions,
`⟦ \ · ⟧` and a lift over `b` of a lift over `a`, that agree in every
model but got different normal forms. A lift's stuck lookup kept a step
on the bound label in its word, which the looked-up named variable can
never reach. The one-variable mode above fixes it, and with it the
stuck-lookup example.

**After the fix:**

| Facts | Expressions | Classes | Missed identities | Unsound |
|---|---|---|---|---|
| none | 1500 | 797 | 0 | 0 |
| `a < c` | 1500 | 991 | 0 | 0 |
| `a < c, b < c` | 1500 | 1005 | 0 | 0 |

## Still to do

1. **Real values and atoms.** Repeated targets, terms (whose payloads
   see the rest of the word), atoms between segments, and the bound
   label; then a search over `HNorm`'s actual outputs with the pass.
2. **The two other kinds of use.** A term's payload (named inputs only)
   and a stuck lookup's word (a single variable, walked forwards).
3. **Cost.** Deciding deadness by reducing every window is quadratic or
   worse. The reduction can be shared along the word, which needs
   working out.
4. **Proofs.** The other direction of the characterisation, then
   uniqueness of words normal for both beta and eta.
