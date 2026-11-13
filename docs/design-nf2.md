# The shared canonical form (design)

This is the normal form `names` moves to: linear in the size of the
input, with `share` in the input and in the output. It replaces the
layered word of `docs/normal-forms.md` (routes to the least variable,
unary entries, payloads with atoms kept as trees) and the tree normal
form.

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
   distinct ones have distinct results, and they are numbered in the
   order of their results: a term before a variable or a stuck atom, then
   by the index of the variable reached (or the variable an atom is stuck
   on), then by the order `rgt` on results. This numbering depends on the
   rest only. Numbering by first use from the segment above, as now,
   makes one new layer on top renumber every layer below (Θ(L) per step).
   With this order a variable carried around lifts keeps its index, so a
   run of carried variables stays one run.
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

Paper only, in `docs/normal-forms.md`, from the mechanised size facts and
the data structures (binary indices, label comparisons from the facts
table, per-layer heights stored with the line so comparisons need not
recompute them).
