# Zero-set models

The model class proposed in place of copied models (`docs/copied.md`),
defined in `Core/ZModel.v`.

## Where the examples leave the normaliser

The normaliser treats each test as an independent atom. A *test* is an
entry asking "is the input, moved to this point, at index 0 of this
label?". The model arguments for the examples instead pin two states to
one variable, and then move other tests along that equation:

- **`r1`/`r2`** (`Core/HEtaGap.v`):
  - "`v` is `a`" and "`⟦ \ b as _ ⟧ v` is `a`", with `a` a single
    variable, give `⟦ \ b as _ ⟧ v = v`;
  - so `⟦ \ b as _ ⟧` applied twice also takes `v` to `a`.
- **The example with facts** (`docs/separation.md`):
  - "`v` is `g`", and `⟦ \ h as _ ⟧` fixes every variable of `g`, give
    `⟦ \ h as _ ⟧ v = v`;
  - so "`v` is `m`" becomes "`⟦ \ h as _ ⟧ v` is `m`".

The normaliser's own laws need much less:

- **Entries on ordered labels commute.** So labels the facts order have
  disjoint index-0 sets, and each maps the other's index-0 set onto
  itself. Nothing says it fixes that set.
- **Lookups, and the same-target swap.** A target such as `g`, read when
  nothing more specific is meant, must be one variable, fixed by steps
  on ordered labels.
- **The identity renaming** `⟦ g as a | Γ \ g as a | Γ ⟧ = ⟦⟧`. So a
  target naming `g`, read by an entry that consumed an index-0 variable
  of `g`, is that variable.

## The models

A zero-set model has:

- a set of variables;
- for each label `h`, an injection `⟦ \ h as _ ⟧`. The variables it
  misses are the *index-0 variables* of `h`, a set rather than one
  variable;
- for each label, one *designated* index-0 variable.

A target naming `gᵢ`, read by an entry that consumed `v`, means:

- `v` moved `i` times along `g`, if `v` is index 0 of `g`;
- the designated variable moved `i` times along `g`, otherwise.

**Consistency with the facts** (`zcons`). For labels `g`, `h` the facts
order:

- their weakenings commute;
- their index-0 sets are disjoint;
- each maps the other's index-0 set onto itself, and fixes the other's
  designated variable.

So steps on `h` may move the index-0 variables of `g` among themselves,
other than the designated one. Steps on the bound label fix every
variable not on it, and steps on named labels keep variables on or off
the bound label.

**Interleaved models are the case where each index-0 set has one
element.** They embed with the same meaning (`iz`, `iz_cons`,
`iz_za`).

**Proved in `Core/ZModel.v`:**

- cancellation (`za_cancel`);
- the identity renaming (`za_id_rename`);
- the same-target swap, with no extra condition (`ztest_comm`);
- for ordered labels:
  - commutation (`z_comm`, `z_un_sh`);
  - index 0 kept (`z_at0_h`, `z_at0_g`, `z_at0_h_un`);
  - disjoint index-0 sets (`z_disj`);
- reading a target commutes with steps on labels ordered against it
  (`zread_sh`). This is what lets a lookup pass them;
- the bound label's steps fix named variables (`z_bound_fix`,
  `z_bound_at0`).

**Not mechanised.** `HNorm`'s words carry absolute values. A value is
the target as read at the entry, then carried through the rest of the
word. When sorting moves an entry past a step on an ordered label, a
stuck lookup's value must still be read where it was computed. That is
the point in the word its stored suffix starts at, which can now be
before the entry. On paper this is consistent with every rewrite of
`HNorm` and the eta pass. There is no formal semantics for those words
yet.

**Two parts of the eta pass are unsound here, and go:**

- **Stuck lookups.** Steps on labels ordered against the looked-up
  label can move it, so they cannot be dropped from a stuck lookup's
  word. The pair of expressions this rule was added for is not an
  identity here.
- **Payloads without a payload atom.** Dropping bound-label steps stays
  sound, by the bound-label condition.

## Separation with facts

The plan of `docs/separation.md`: three kinds of model, built here from
the group itself.

**Negative indices.** Below each index-0 variable `z` of `h`, add
private variables `z₋₁, z₋₂, …`:

- steps on `h` move along them;
- steps on a label ordered against `h` map `z₋ₙ` to `(z')₋ₙ`, where
  `z'` is the image of `z`;
- steps on other labels fix them.

Then every label acts as a bijection, steps on ordered labels still
commute, and the group `A` acts. The meaning of a segment is its end
position and its tests, as before. The dead-entry and repeated-entry
arguments go through, because steps on ordered labels keep index 0 of
`g` in both directions.

**Walls.** These are the hyperplanes of the cube complex of `A` (its
Cayley graph, with a square for each pair of ordered labels).

- The wall of an entry on `g` at position `X` is the hyperplane dual
  to the edge from `X` to `X·g⁻¹`.
- Its *carrier* is the set of vertices `X·c` on the near side of that
  edge, for `c` a product of labels ordered against `g`.
- A test is live exactly when it is the first crossing of its wall.
- Test `u` is *behind* `t` when `u`'s position is on the far side of
  `t`'s wall.
- Two walls cross only when their labels are ordered. Then the two
  tests can never both hold: index-0 sets of ordered labels are
  disjoint.

**The model for a set `W` of walls to make true.** The walls in `W` must
not cross, and none may be behind another.

1. **Vertices.** Start from the Cayley graph of `A`, every label acting
   by right multiplication.
2. **Cut.** For each `t ∈ W`, on label `g`, remove the far side of its
   hyperplane. Make every carrier vertex of `t` an index-0 variable of
   `g`, with its private negative indices. The far sides are disjoint,
   because the walls do not cross and none is behind another.
3. **Designated variables.** Add, disjointly, a standard model with
   one sequence per label, for the designated variables.
4. **Input.** The input is the vertex `1`.

**Checks:**

- **Injections.** Each label's step is injective. It misses exactly the
  carrier vertices of cut walls on that label, plus the standard part's
  index 0.
- **Ordered labels.**
  - They commute, because the group does.
  - A carrier is closed under the labels ordered against its label, so
    those steps permute the index-0 variables of the cut label.
  - Index-0 sets of ordered labels are disjoint, because a vertex in
    both carriers would make the two walls cross.
  - The designated variables are fixed, because the standard part keeps
    ordered labels disjoint.

**What holds at the input.**

- **A position on the near side of every cut wall** is its own vertex.
  It is index 0 of `g` exactly when its wall is in `W`.
- **A position behind a cut wall `t`** reaches the negative indices of
  `t`. Whatever happens after that, the test there is behind `t`.
  Every word containing it has `t`'s wall live before it, so it is never
  the first test to hold.
- **With `W` empty**, nothing holds, and the input ends at the end
  position. So the end positions must agree.

So the three kinds of model exist with facts too. The example with
facts from `docs/separation.md` is not an identity here:

- take `t` = the test on `g` at `1` and `t'` = the test on `m` at `1`;
- the vertex `h` is in `t`'s carrier, because `h` is ordered against
  `g`;
- `h` is not in `t'`'s carrier, because `h` is not ordered against
  `m`;
- so the test on `m` after `⟦ \ h as _ ⟧` is false.

## What is left

1. **Write the separation argument out in full.** This covers walls
   and carriers in the cube complex, and the step from words to the
   cube complex. Everything here is a sketch.
2. **The normal form.** Equal meanings give the same end position, the
   same live tests and targets, and the same order on every pair that
   can both hold with different targets. The normaliser must turn that
   into one word:
   - with all targets distinct, the searches suggest `HNorm` plus the
     eta pass already does (no misses up to 10 steps over copied
     models). That needs a normal-form theorem for its words;
   - with repeated targets, it needs the same-target swap at any
     distance, and a canonical choice among the words that realise the
     same order: the printer.
3. **Segments and atoms**, and values that are terms or stuck lookups.
