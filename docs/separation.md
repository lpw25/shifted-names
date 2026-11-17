# Canonicity over copied models: the proof attempt

The models are those of `docs/copied.md`. This is a proof on paper, for
segments (the steps between two atoms), with targets that are opaque
values. It goes through when there are no facts. With facts it gets
stuck, and the place where it does is a law the normaliser itself
relies on.

## Segments as decision lists

**The group.** Let `A` be the group with one generator per label, where
labels the facts order commute. A segment traces a path in `A`:
`⟦ \ g as _ ⟧` multiplies by `g`, an entry on `g` by `g⁻¹`. The
*position* of an entry is the product of the steps before it.

**Negative indices.** Give each copy of each label private variables at
negative indices, which no other label moves. Then every label acts as a
bijection on all variables, and `A` acts on them.

**The tests.** An entry on `g` at position `X` is the test "`v·X` is
index 0 of some copy of `g`". A segment on an input `v` gives the target
of the first test that holds. If none holds, it gives `v` moved by the
whole segment. Before the first test holds, the walk is the action of
`A`. It can only go negative by passing an entry at index 0, which is a
test that holds.

**Walls.** Two tests on `g` are *on the same wall* when their positions
differ by steps on labels ordered against `g`. Such steps fix every
copy of `g`, so tests on one wall always agree.

**Live tests.** A test is *live* when it is the first crossing of its
wall in the word. Otherwise it is one of:

- **dead:** an earlier `⟦ \ g as _ ⟧` crossed the wall. If the test
  held, `v` would reach a negative index of `g` just before that
  weakening, so an earlier test held. This is `docs/eta.md`'s
  condition, restated.
- **repeated:** an earlier entry crossed the wall, and that test agrees
  with this one.

So the first test that holds is always live. The meaning of a segment is
its end position and its live tests, in order, with their targets.

**Behind.** A test `u` is *behind* a test `t` when every path from the
start to `u`'s position crosses `t`'s wall away from the start. Then any
word containing `u` crosses `t`'s wall first. The first crossing is an
entry, so `t`'s wall is live there, before `u`. The order of `t` and `u`
is forced.

## What canonicity needs

Let `w1` and `w2` be equal in every copied model, and let `T` be the
walls of both. It is enough to have three kinds of model:

1. **None true.** No test of `T` holds. Then the end positions must
   agree.
2. **One true.** For each live `t`, a model where `t` holds and every
   other test that holds is behind `t`. Then both words have `t`'s wall
   live, with the same target.
3. **Two true.** For live `t`, `t'`, neither behind the other and not on
   ordered labels at one place, a model where both hold and every other
   test that holds is behind one of them. Then if their targets differ,
   both words order them the same way.

Given these, the live tests of the two words are the same, and every
pair whose order matters is ordered the same way in both. So the two
lists have the same lexicographically least order: the canonical form
is the same.

## No facts: the models exist

With no facts, `A` is free and its Cayley graph is a tree. Let `W` be
the tests to make true, none behind another. Build the model:

1. **The tree.** Take a large ball `B` of the tree around the start
   vertex `y`.
2. **Cut at each true test.** For each `t ∈ W` on `g` at `X`, remove the
   part of `B` on the far side of the edge from `X` to `X·g⁻¹`. Since no
   test of `W` is behind another, these parts are disjoint. Make `X`
   index 0 of a new copy of `g`, with private negative indices below it.
3. **Extend every line.** Every other line of label `k` through `B` is
   an interval. Extend it above and below with fresh variables on `k`
   only, down to a fresh index 0 outside `B`.
4. **Phases.** Where one vertex is index 0 for two labels, give the two
   copies one phase.

This is a copied model. Labels are unordered, so there is nothing to
check between them.

**What it does.**

- For a position not behind any `t ∈ W`, `y·X` is the vertex `X`. That
  vertex is index 0 of `k` exactly when `(k, X)` is in `W`.
- For a position behind `t`, the walk enters `t`'s private negative
  indices. Other labels fix those, so it can only come back out through
  `X` itself.
- Suppose such a test `u` is on `t`'s label and lands back on `X`. Then
  `u`'s position ends with that label, pointing back towards the start,
  so `u` is dead in every word.
- Otherwise `u` lands on a vertex that is not index 0 of `u`'s label.

So the three kinds of model exist, and **with no facts the normal form
plus the same-target swap is canonical**. Two parts are still open: the
step from the tree to arbitrary positions in words, and printing.

## With facts: where it gets stuck

With a fact `g < h`, steps on `h` must leave every copy of `g` alone.
Copied models make ordered labels share no variable. And the
normaliser's lookups pass a variable of `g` unchanged through
`⟦ \ h as _ ⟧`. That gives a three-way implication.

**Example.** Fact `g < h`, and `m` related to neither.

```
P  = ⟦ \ h as _ ⟧ ⨾ ⟦ m as v; ·; ·; · as v \ ·; ·; · as v ⟧ ⨾ ⟦ \ m as _ ⟧
   ⨾ ⟦ h as v; · as v \ · as v ⟧

w1 = P ⨾ ⟦ g as v; · as v \ · as v ⟧ ⨾ ⟦ \ g as _ ⟧
       ⨾ ⟦ m as v; ·; · as v \ ·; · as v ⟧ ⨾ ⟦ \ m as _ ⟧

w2 = P ⨾ ⟦ m as v; ·; · as v \ ·; · as v ⟧ ⨾ ⟦ \ m as _ ⟧
       ⨾ ⟦ g as v; · as v \ · as v ⟧ ⨾ ⟦ \ g as _ ⟧
```

`w1` asks three questions in turn:

1. is `⟦ \ h as _ ⟧ v` index 0 of `m`? If so, `· ²`;
2. is `v` index 0 of `g`? If so, `·`;
3. is `v` index 0 of `m`? If so, `· ¹`.

`w2` asks 1, 3, 2. The entry on `h` in `P` only moves the variable back.

The order of 2 and 3 matters only if `v` is index 0 of both `g` and
`m`. Then `⟦ \ h as _ ⟧` fixes `v`, because `v` is on `g`. So question
1 already said yes. Hence `w1 = w2` in every copied model, while without
`P` the two differ. The normaliser gives them different normal forms.

This is the clause "`t ∧ t'` implies `u`", with `t`, `t'` the tests at
the start position and `u` the test on `m` after `⟦ \ h as _ ⟧`. There
are longer ones of the same kind. One, with four tests, also needs a
`⟦ \ g as _ ⟧` that moves `v`.

**What it rests on.** "A step on `h` leaves every variable of `g` alone"
is not optional. It is what lets lookups pass steps on ordered labels,
and what lets entries on ordered labels commute. If `h` could move a
variable of `g` along `g`'s own sequence, there would be a variable at
index 0 of both, and the two entries there would not commute.

**A possible relaxation.** `h` might move a variable of copy `p` of `g`
to the same index of another copy `p'`: a phase shift. Then question 1
could see a different copy of `g` than `v` was on, and the implication
goes. Commutation survives if targets are read in the shifted phase. But
then a value like "index `i` of `g`" means different variables
depending on which ordered steps come after it. Lookups would have to
track that shift, which `HNorm`'s values do not.
