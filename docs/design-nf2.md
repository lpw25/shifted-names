# The shared canonical form (design)

This is the normal form `names` moves to: linear in the size of the
input, with `share` in the input and in the output. It replaces the
layered word of `docs/normal-forms.md` (routes to the least variable,
unary entries, payloads with atoms kept as trees) and the tree normal
form.

## Status of the theory

`Core/BUnique.v` proves uniqueness for these conditions (`line_unique`,
no admits): canonical lines whose terms carry branches nested to any
depth, with the same free meaning, are equal. `Core/CanonBr.v` shows
the canonical words that `CanonW.canon` builds for the pure fragment
satisfy them.

Notes from the proof:

- The no-hop rule is stated on the free model and covers every lifted
  input of the atom, including those whose result comes from the base
  of a branch (a term of the line the branch reaches past its last
  atom). Without it two branch words over different bases can mean the
  same: a private term in one against a term of the line reached by a
  lift in the other. With it, the private form is the canonical one;
  when the line term is also used by the line, the canonical form keeps
  both (a private copy in the branch and the term in the line), which
  costs a constant per term.
- A term in a branch's first segment whose result in the other word is
  past an atom is excluded by the no-hop rule at that atom (`cross`);
  terms of one stretch are ordered by the rests they reach.
- Bound inputs of a payload without a payload atom are phantoms in the
  branch's first stretch: shifted past the real ones, never given an
  explicit target, never lifted.

## The algorithm with branches (to do)

Built from the right as `CanonW.canon`, over a base and a domain so the
same code canonicalises branch bodies:

1. A segment with branch terms: each branch body is canonicalised over
   its base (its tail, then the canonical rest); then the terms go in
   as now (join, new layer, swap), with classes, routes and the order
   taking branch payloads into account.
2. An atom: the terms its lifted inputs reach whose branch ends with
   this atom and its continuation hop in front of it; the rest of the
   line is re-routed so that the atom's lifts stay what they must be.

## Sizes

The size of an expression counts every constructor once and every number
(an index, a count of lifts, a term atom) at its binary length. `share`
counts its bound adjustment once, however often it is used.

## The form

A canonical form is a *line* and a table of *branches*.

- A **line** is a list of steps, as now: segments and atoms under lifts.
- A **segment** is per label (in label order) a list of *chunks* and a
  tail shift. A chunk is either a run `Run c k` (the next `k` inputs `i`
  go to `h₍ᵢ₊c₎`, `c` an integer) or one target (a variable of another
  label, or a term). Canonical chunk lists: runs are maximal (no two
  adjacent runs with the same shift, a variable of the entry's own label
  is always part of a run), no empty run, and the tail is not the shift
  of a final run. So `n` lifts by the bound label cost one run, not `n`
  targets.
- A **term** is a term atom `u`, an optional payload atom `b`, a
  reference to a branch `P` (or none), and a *tail* `A`: a renaming of
  bound variables only. Its payload is `P`, then `A`, then the rest of
  the line after the term's segment.
- A **branch** is a word whose last step is an atom; its terms have the
  rest of the branch, then the tail and the line, as payload. Branches
  are numbered in the order of their first use, and two terms with the
  same branch refer to the same entry. A branch is itself in the
  canonical form relative to what follows it.

Written as an adjustment, every suffix of the line used as a payload and
every branch is one `share`.

## Conditions

The conditions are stated on the free model (`Unique.fres`): `R r` is
what the rest `r` does to each variable. A term of a segment `S` with
rest `r` has a *branch word* `w`: a word `P` that is empty or ends with
an atom, then a tail `A`, a renaming that leaves named variables alone.
Its payload is `P`, then `A`, then `r`: in the free model `FTerm u b k`
with `k = flw P (fs A (R r))`. A term with an empty `P` is a pure term
(as in the proved fragment). For a segment `S` followed by `r`:

1. **Kind.** `S` has a term, or it is a renaming that ends the line or
   stands before an atom in lift position.
2. **Order.** For every term the rest reaches in its own stretch (no
   atom between), at rest `r_t`: `R r` is above `R r_t` in the order on
   what payloads do to named variables. (Terms in later stretches are
   below by depth.)
3. **Routes.** A named input that can go on as itself does; otherwise it
   goes to the least named variable of the rest with its result, and to
   a bound variable only when there is none (`route_id`).
4. **Bound variables.** Every bound variable of the rest is used,
   distinct ones have distinct results, numbered by first use.
5. **Branches.** `P` is in canonical form relative to its continuation
   `fs A (R r)`: the same conditions, recursively, with `R` taken over
   that continuation instead of the identity. `A` is routed as a payload
   tail (as `so_pay`). A pure term with no payload atom has `A` empty.
6. **No hop.** At an atom `LA L a` followed by `l1`: no term that `l1`
   sends a lifted input of the atom to, in `l1`'s first stretch, has as
   the last atom of its branch the atom `a` with the continuation the
   line has after `a`. Stated on the free model: with `k` the term's
   payload, `d` its depth and `n = natl l1`, the `(d - n)`-th atom met
   far along `lbig` in `k` is not `a` with continuation
   `fun z => R l1 (shiftL L z)`. Such a term would stand in front of the
   atom instead (`⟦ x | σ ⟧ ⨾ ⟦ x := u⟨σ⟩ ⟧ = ⟦ x := u ⟧ ⨾ σ`).

Rule 6 replaces the earlier "fewest atoms in `P` over every suffix of the
line". That rule is not enough: moving a term in front of an atom
changes the atom's lifts, so a hopped line need not have the unhopped
line's atom suffix, and a payload can fail to factor through every
suffix of the unhopped line while the hopped line still exists. What
the hop needs is that the stuck continuation after the branch's last
atom is the line's stuck continuation after the atom, which is what
rule 6 states.

**What a payload without a payload atom sees.** A term's payload with
no payload atom acts on named variables only (`feq` compares such
payloads there). In a branch of such a term, the bound inputs are
unobservable until the first atom. Bound variables reached only from
them are *phantoms*: in the first stretch of the branch the real bound
variables are numbered first, phantoms after them, and a segment does
nothing to a phantom but shift it (no explicit target, no lift). After
an atom every variable is observable again (a stuck result carries its
whole continuation). So the conditions take the number `p` of real
bound variables at the head (`None`: all real).

Rule 3 differs from the old `lnf`, which always routed to the least
variable. That forces an entry `x ↦ y` into every layer above a
renaming that makes `x` and `y` equal: size Θ(k·L) for `k` such
renamings under `L` layers. With rule 3 those layers need nothing.

## Uniqueness

`lw_unique` generalised to a base continuation `K` (the line: `FVar`; a
branch: `fs A (R r)`) and a head domain `p`. By induction from the
front, as now. What is new:

- **Branches with different bases** (`GBU`): two canonical words that
  are empty or end with an atom, with the same number of atoms, mean the
  same over bases `K` and `K'` (on the head domain): then they are equal
  and, with at least one atom, `K` and `K'` agree everywhere (the last
  atom's continuation is `K` up to its lifts, and lift position makes
  every lifted variable an input). This is the induction itself, with
  the conclusion carrying the bases.
- **The first layer** (`first_layer`): a term `x0` of the first segment
  `S` in `l` (rest `r`, `natl r = N`) and the term it reaches in `l'`
  at rest `r''`. By depth, `natoms P0 + N = natoms P'' + natl r''`.
  - Same stretch (`natl r'' = N`): `GBU` on the two branches gives
    `R r` and `R r''` equal on named variables; then as before: in `S'`
    itself, or the order gives `R r' > R r''`, and the symmetric term of
    `S'` closes a cycle.
  - Deeper (`natl r'' < N`): far along `lbig`, `k`'s atoms are `P0`'s
    then the line's; the line's atoms and their continuations are the
    same in `l` and `l'` (they are what `R l` does far along `lbig`). So
    the last atom of `P''` is the line atom of `l'` just before the term,
    with the line's continuation: rule 6 fails in `l'`.
- **Terms of one segment**: with the rest known equal, `GBU` with one
  base gives equal branches, and the tails are equal by their routes.

## Sizes

The size of an expression counts every constructor once and every number
(an index, a count of lifts, a term atom) at its binary length. `share`
counts its bound adjustment once, however often it is used.

## The form

A canonical form is a *line* and a table of *branches*.

- A **line** is a list of steps, as now: segments and atoms under lifts.
- A **segment** is per label (in label order) a list of *chunks* and a
  tail shift. A chunk is either a run `Run c k` (the next `k` inputs `i`
  go to `h₍ᵢ₊c₎`, `c` an integer) or one target (a variable of another
  label, or a term). Canonical chunk lists: runs are maximal (no two
  adjacent runs with the same shift, a variable of the entry's own label
  is always part of a run), no empty run, and the tail is not the shift
  of a final run. So `n` lifts by the bound label cost one run, not `n`
  targets.
- A **term** is a term atom `u`, an optional payload atom `b`, a
  reference to a branch `P` (or none), and a *tail* `A`: a renaming of
  bound variables only. Its payload is `P`, then `A`, then the rest of
  the line after the term's segment.
- A **branch** is a word whose last step is an atom; its terms have the
  rest of the branch, then the tail and the line, as payload. Branches
  are numbered in the order of their first use, and two terms with the
  same branch refer to the same entry. A branch is itself in the
  canonical form relative to what follows it.

Written as an adjustment, every suffix of the line used as a payload and
every branch is one `share`.

## Conditions

For a segment `S` followed by the rest `r`, as in `LayeredUnique.lnf`:

1. **Kind.** `S` has a term, or it is a renaming that ends the line or
   stands before an atom in lift position.
2. **Order.** The rest, as a payload, is above the post-branch payload
   (`A` then the rest) of every term it reaches.
3. **Routes.** A named input that can go on as itself does
   (its result is the result of the same variable of the rest); otherwise
   it goes to the least named variable of the rest with its result, and
   to a bound variable only when there is none.
4. **Bound variables.** Every bound variable of the rest is used,
   distinct ones have distinct results, and they are numbered by first
   use from the segment above. Variables carried through a layer keep
   their relative order, so they stay one run: this costs no size.
   (`Order.num_order`, numbering by results, is the proved alternative; it
   avoids renumbering below a new layer but makes ordering need the full
   results, so it is not cheaper.)
5. **Branches are minimal.** A term's payload is `P ⨾ A ⨾ R(r)` with the
   fewest atoms in `P` over every way of writing it with a suffix of the
   line. This one rule is both former conventions: anything a payload
   does after its last private atom besides renaming bound variables is
   on the line (*split*), and a term whose branch could end with an atom
   of the line stands before that atom (*hop*).

Rule 3 differs from the current `lnf`, which always routes to the least
variable. That forces an entry `x ↦ y` into every layer above a renaming
that makes `x` and `y` equal: size Θ(k·L) for `k` such renamings under
`L` layers. With rule 3 those layers need nothing.

## Uniqueness

By induction from the end of the line, as `lw_unique`. The new step is
rule 5: two decompositions `P ⨾ A ⨾ R(r_j)` and `P' ⨾ A' ⨾ R(r_j')` of one
payload with the fewest atoms have `natoms P = natoms P'`, so the deep
counts give `natl r_j = natl r_j'`; peeling the atoms of `P` and `P'` one
by one (`peel`) gives equal branches and equal continuations; the order
on the rests of one atom-free stretch of the line then gives `j = j'`, and
the routes give `A = A'`. Canonical chunking makes segments with equal
results equal.

## Size

Mechanised: the canonical form of an expression is at most a constant
times its size. Proved through the construction: each step of `lnorm`
and of `canon` is bounded by the size of what it reads plus the growth it
causes, and the growth is charged to input constructors (each at most a
constant number of times).

## Time

Paper only, in `docs/normal-forms.md`. The target is O(n²) overall: each
input step costs O(size of the current canonical form), with indices in
binary. Mechanised size facts bound each pass. What this rules out: an
operation that makes a pass over the rest at every layer it visits
(the recursion under a layer must not re-cons the whole rest at each
level), and recomputing the height of payloads from scratch (heights are
computed in one bottom-up pass, linear in the word). Faster than O(n²) is
later work.
