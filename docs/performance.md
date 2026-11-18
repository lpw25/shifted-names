# Cost of the canonical form for segments

`n` is the number of steps in a segment, `k ≤ n` the number of live
tests, `L` the number of labels. The aim is time below cubic, and
output size below cubic.

## Output size

The printed canonical word is:

- a geodesic from the start to the first test's point;
- each test, as an entry and a weakening;
- a geodesic between consecutive tests;
- a geodesic to the end.

Every point a segment visits is within `n` steps of the start, so each
geodesic has at most `2n` steps. The output is therefore at most
`2n·(k + 1) + 2k = O(n²)`. It is not cubic.

What is cubic, or worse, is the time to normalise that printed word
again: `HNorm` is quadratic in its input, and that input is `O(n²)`
long. So the printer must produce the normal word directly.

**With distinct targets,** the order of tests is the input's order, up
to swapping crossing walls. The normal word then never travels further
than the input between consecutive tests, so the output is at most `n`.

**With repeated targets,** a lexicographic order on tests can zigzag
between branches, which costs `O(n)` per switch. Choosing the order to
follow the geometry avoids most of that. Put the tests' points in a trie
of their normal forms: the hash-consed tree `TNorm` already builds.
Then take the order that a depth-first walk of the trie gives, subject
to the constraints of `docs/normal-form.md`. The walk's length is the
trie's size. That is `O(n)` when the points lie on few branches, and at
most `O(k·n)`.

## Time, phase by phase

| Phase | Now | Plan | Planned cost |
|---|---|---|---|
| Positions after each step | n² (`probes` recomputes) | Keep them as nodes of a hash-consed trie of sorted words. Each step extends the previous position, at `O(n)` for the sorted insertion. | n² |
| Wall of each step | n² or more | The wall's point is the position with trailing labels ordered against the step's label stripped, then hash-consed. | n² |
| Live or dead (eta) | n³ or more: each dead check reduces a window | A step is live when it is the first crossing of its wall: one dictionary pass. | n |
| Removing dead pairs, re-sorting | n² per pass, up to n passes | One right-to-left push of the word, removing a dead entry together with the weakening it meets. Deadness is a property of the wall, and removals do not change other steps' walls. | n² |
| "Behind" | k²·n | For each test, one scan along the walk, tracking which side of its wall each later point is on. The side changes exactly at crossings of that wall, which the wall keys identify. | n·k ≤ n² |
| Crossing walls | k²·n | Open: see below | ? |
| Canonical order, repeated targets | n⁴ | Precomputed constraints form a graph with at most `k²` edges. The order is a topological sort that prefers the trie's depth-first order. | k² ≤ n² |
| Forced firing (facts) | k²·n·L per greedy step | Open: see below | ? |
| Printing | n² words, then `HNorm`: n⁴ | Print the depth-first walk directly, as sorted pieces. | O(output) |

So everything except two pieces fits in `O(n²)`, and the eta pass in
particular needs no cubic step.

## Open pieces

**Crossing walls.** Tests `t` (on `g` at `P`) and `u` (on `h` at `Q`),
with `g` and `h` ordered, cross exactly when their carriers share a
point. Two convex sets in the cube complex meet unless some wall
separates them. That suggests a scan along the walk, as for "behind",
counting the walls between the two points whose labels are not ordered
against `g` or `h`. That is `O(n·L)` per starting test, so `O(n²·L)`
overall. I have not checked the details: walls with such labels need
not cross the carriers.

**Forced firing.** The closure for a pair of tests costs about `n·L`
with a worklist. Applying it to all pairs is cubic. Closures for single
tests are cheap in total, `O(n²·L)`, but a pair can need both facts at
once: a test on `m` at `a·b`, forced by tests on `g` and `m` at the
start, with `a` ordered against `g` and `b` against `m`. Two directions:

- show that pair effects only arise between tests whose points are
  linked through ordered labels, and that such pairs are few enough to
  bound the total;
- or restructure the canonical order so it never asks about all pairs,
  only about candidates that adjacent swaps could reach, with a bound on
  how many swaps can be needed.

I don't have either yet.

## Junctions in printing

Each piece a depth-first walk prints is sorted, but where a piece meets
a test, or the next piece, steps on ordered labels can be out of order.
Fixing that must cost no more than the pieces themselves. A step
crosses a junction only if it commutes with everything it passes, and
in a sorted word that is bounded by the run of mutually ordered labels
around the junction. I have not proved a bound.
