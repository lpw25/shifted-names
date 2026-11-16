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

(Filled in below.)
