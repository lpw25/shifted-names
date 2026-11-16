# The simple hash-consed normaliser

An experiment (`Core/HNorm.v`): the simplest version of the design in
`docs/nf-design.md`, checked for its bounds and timed against the
existing normaliser. Nothing in it is proved yet.

## The form

A normal form is a word of steps, kept sorted and reduced as in
`docs/nf-design.md`:

- `SE h v`: an input entry on `h` with value `v`;
- `SW h`: a weakening on `h`;
- `SA a`: an adjustment atom.

**Values are absolute.** A value is one of:

- a variable of the scope at the end of the word;
- a term with the id of its payload word;
- a lookup stuck at the first step of a word, given by its id.

**Storage.** Words are linked lists, hash-consed:

- each cell is a step and the id of the word after it;
- equal cells get one id;
- the empty word has id 1.

Two adjustments are equal exactly when their words have the same id.

## The algorithm

An expression is normalised from right to left: `norm e K` is `e`, then
the word `K`.

**Constructs.**

| Construct | Normal form |
|---|---|
| `a ⨾ b` (`b` first) | `norm b (norm a K)` |
| an atom | a cell in front of `K` |
| an output entry on `h` | a weakening on `h` pushed onto `K`, then `a` on top |
| an input entry `h := t` | the value of `t` against `K`, then `a` on top of `K`, then the entry pushed |
| a lift `⟦ h \| a ⟧` | the entry `h := (h₀ looked up in K)` pushed on top of `a`, with `a` on top of a weakening on `h` pushed onto `K` |

**Values.**

- A variable target is looked up in `K`.
- A term's payload expression is normalised on top of `K`. Its id is
  the value's payload.

**Pushing a step on `h`.** The step walks down the word past steps on
labels known distinct from `h`, to the first step on `h`, on a label
not known distinct from `h`, or an atom.

- A weakening that reaches an entry on `h` cancels with it.
- An entry that reaches a weakening on `h` is absorbed when its value
  is what the rest gives `h₀`.
- Otherwise the step is inserted in sorted position: past the steps on
  labels known distinct from `h` that sort before it.

The cells in front of the edit are rebuilt, and the rest is shared.

**Looking up `hᵢ`.** Walk down the word, adjusting the index at steps
on `h`, until it reaches an entry at index 0 (its value), the end (the
variable), or a step where it is stuck (a stuck lookup).

## Bounds

Here `n` is the size of an expression without `share`.

- **Every word has length `O(n)`.** Each input construct adds at most
  one step.
- **Each construct costs `O(n)`.** It does a constant number of walks
  and rebuilds the cells in front of one edit. Each hash-consing
  operation is one table lookup.
- **Payloads add nothing extra.** A term's payload expression is part
  of the input, and is normalised once, on top of the current word.

So time and the number of cells built are `O(n²)` (up to the table's
logarithm). The output, the cells reachable from the result, is
`O(n²)` in the worst case.

**Example of the worst case.** A word of `n` entries on labels known
distinct, sorted in the reverse of the order they are added. Each new
entry is then inserted at the end, so every suffix is a different word.
That word is reachable when terms refer to every suffix, as in a chain
of substitutions with that order.

**With `share`.** A shared expression used with one continuation is
normalised once if compositions are memoised on the pair (expression,
continuation). Memoisation is not implemented yet, and no benchmark
uses `share`.

## Results

The same families as in `docs/normal-forms.md`. Time is for normalising
both sides and comparing, with `vm_compute`, in seconds. "Size" is the
number of cells reachable from the result (cells built in total, in
brackets, where it differs).

Columns:

- **new:** `HNorm.hn_eq`;
- **layered:** the current decision, `LEval.nf_eq_t`;
- **tree:** the tree normal form, `LEval.tnorm`, the form of the original
  implementation.

"—" means not run, and "> 120" means stopped after 120 s.

| Family | Normaliser | 16 | 64 | 256 | 1024 |
|---|---|---|---|---|---|
| chain of substitutions, left- vs right-nested | new | — | 0.015 | 0.12 | 1.6 |
| | layered | — | 0.007 | 0.031 | 0.28 |
| | tree | 0.096 | > 120 | — | — |
| the same chain, labels sorted against the order of addition | new | — | 0.035 | 0.73 | 27.8 |
| | layered | — | 0.007 | 0.027 | 0.27 |
| | tree | 0.094 | > 120 | — | — |
| substitutions for one name | new | — | 0.004 | 0.017 | 0.13 |
| | layered | — | 0.009 | 0.026 | 0.23 |
| | tree | 0.064 | > 120 | — | — |
| an atom after each substitution | new | — | 0.003 | 0.013 | 0.12 |
| | layered | — | 0.006 | 0.017 | 0.15 |
| | tree | 1.1 | > 120 | — | — |
| weakenings of distinct names | new | — | 0.014 | 0.13 | 1.4 |
| | layered | — | 0.012 | 0.094 | 1.3 |
| | tree | 0.003 | 0.011 | 0.13 | — |
| one substitution under nested lifts | new | — | 0.058 | 0.77 | 15.2 |
| | layered | — | 0.11 | 2.2 | 90.7 |
| | tree | 0.023 | 0.12 | 2.2 | — |
| one simultaneous substitution | new | — | 0.009 | 0.11 | 1.5 |
| | layered | — | 0.007 | 0.015 | 0.12 |
| | tree | 0.005 | 0.006 | 0.063 | — |
| a term whose payload is the chain, then the chain | new | — | 0.016 | 0.19 | 2.4 |
| | layered | — | 0.063 | 0.77 | 10.9 |
| | tree | 0.19 | > 120 | — | — |
| a chain under nested lifts, then a substitution for each | new | — | 0.022 | 0.23 | 3.1 |
| | layered | — | 0.099 | 1.9 | 68.8 |
| | tree | 0.10 | > 120 | — | — |

Size of the new normal form, in cells reachable from the result (and
built in total, where that differs):

| Family | 64 | 256 | 1024 |
|---|---|---|---|
| chain, either nesting | 64 | 256 | 1024 |
| chain sorted against the order of addition | 2080 | 32896 | 524800 |
| substitutions for one name | 64 | 256 | 1024 |
| an atom after each substitution | 128 | 512 | 2048 |
| weakenings of distinct names | 64 | 256 | 1024 |
| nested lifts | 65 (4163) | 257 (65795) | 1027 (912577) |
| simultaneous substitution | 64 | 256 | 1024 |
| payload is the chain | 65 | 257 | 1025 |
| chain under nested lifts | 128 | 512 | 1525 (2051) |

**Reading the results.**

- **Every comparison was decided correctly.** The new normaliser
  answered `true` on every pair, as the other two do.
- **The new normaliser is quadratic, as predicted.**
  - *Worst case:* only the chain with labels sorted against the order
    of addition reaches the worst-case output size: `n(n+1)/2` cells.
    Its time at 1024 is 28 s.
  - *Nested lifts:* the reachable output stays linear, but `Θ(n²)`
    cells are built and dropped along the way. That is because each new
    step is inserted after all the earlier ones.
- **Against the layered form**, the new normaliser is:
  - *faster* where the layered form is cubic: nested lifts, terms whose
    payload is a chain, and substitutions under lifts. At 1024 steps
    that is 6 to 22 times faster;
  - *slower* where the layered form is linear: chains and wide
    substitutions, by 6 to 13 times at 1024;
  - *about 100 times slower* on the worst-case chain.
- **The tree form is exponential** on chains (either order), substitutions
  for one name, atoms between substitutions, payload chains and
  substitutions under lifts. It gives
  up before 64 steps on each. Where it has no terms to duplicate
  (weakenings, lifts, wide substitutions) it is about as fast as the
  others.
- **The new form covers more.** It handles labels the facts do not
  order, where the layered form gives up (`lcmp` returns `None`).
