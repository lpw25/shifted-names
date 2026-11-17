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
- each fixes every index-0 variable of the other.

An earlier version only asked each to map the other's index-0 set onto
itself, so that steps on `h` could move the index-0 variables of `g`
among themselves. That breaks a law the normaliser uses:
`⟦ g | ⟦ \ k ⟧ ⟧ = ⟦ \ k ⟧` for `k` ordered against `g`
(`za_lift_ordered`). The lift keeps an index-0 variable of `g` where it
is, and `⟦ \ k ⟧` would move it. `HNorm` gives both sides the same
normal form. Steps on the bound label fix every
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

## The example with facts is an identity

With that condition, the example with facts in `docs/separation.md` is
an identity in every zero-set model:

- if `v` is index 0 of `g`, `⟦ \ h as _ ⟧` fixes `v`;
- so "`v` is `m`" transports to "`⟦ \ h as _ ⟧ v` is `m`".

More generally, when a test on `g` at position `P` fires on `y`:

- every step on a label ordered against `g` fixes `y·P`;
- so `y·P·c·w = y·P·w` for every such `c` and every `w`.

Tests at positions that differ in this way then fire together. No model
of the normaliser's laws avoids this, so the normaliser itself has to
take it into account. The separation sketch that was here assumed the
earlier, wrong condition, and is withdrawn.

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
