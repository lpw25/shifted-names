# Normal forms of adjustments

Composition is written `⨾`, in diagrammatic order: `a ⨾ b` is `a`, then
`b`, so `t [a] [b] = t [a ⨾ b]`.

## Status

The normal form of an adjustment is its *canonical layered word*: a list
of segments and lifted atoms in which a term is written once and has the
rest of the word as its payload. Its size is linear in the size of the
expression. `names` rewrites every adjustment to this word, shown as
context forms, so two adjustments are equal when `names` shows them the
same, and an equation between adjustments is proved by `names;
reflexivity`.

- `Core/Layered.v`: `lnorm` turns an expression into a layered word.
- `Core/Canonical.v`: `canon` puts a layered word in canonical form
  (with `Core/Keys.v`, `Core/Retarget.v`, `Core/Canon.v`, `Core/Merge.v`).
- `Core/LayeredUnique.v`, `Core/LayeredOrder.v`: the conditions `lnf`
  that make a layered word unique, and the proof that they do.

What is proved, and what is not:

- **Sound** (proved): the layered word of an expression means what the
  expression means (`lnorm_sound`), and the canonical word means what
  the word means (`canon_sound`). So every rewrite `names` makes is
  justified, whatever the canonical word is.
- **Unique** (proved, for the conditions): two words satisfying `lnf`
  that mean the same under every interpretation of the atoms are the
  same word (`lw_unique_real`).
- **Canonical** (not proved): that `canon` returns the same word for
  every two words that mean the same. It is tested: on 6350 random
  expressions, of depth 3 to 5, with and without atoms on the line and
  in payloads, bound labels and payload atoms, the canonical word of an
  expression is the canonical word of its tree written back as an
  expression, and of its own rendering. What is missing is the proof
  that the word `canon` returns satisfies `lnf`, and `lnf` itself for
  terms that keep an atom in their payload (see *What is left*).
- Some steps of `canon` are checked when it runs instead of proved:
  they build the pieces of a rearrangement and compare the composition
  of the pieces with what they replace (see *What is left*). A failed
  check leaves that step undone; it cannot make the result wrong.

The tree normal form of the earlier versions is the layered word
multiplied out (`expand`). It is still what `names` reads to
materialise payloads, and its theory is complete: the tree of an expression is normal (`tnorm_normal`), normal
trees are unique (`nf_unique`), so equal expressions have the same tree
(`tnorm_complete`). The decision `nf_eq_t` behind each rewrite compares
canonical words and, only if they differ, trees of up to 100000 nodes;
it is sound (`nf_eq_t_sound`).

The label order is dense with no least or greatest label (the end of a
string sorts just above `\000`), so facts `x < y` never force two label
variables to be equal. What the facts say about each pair of label
variables is worked out once per normalisation (`order_of`).

## Expressions and their meaning

An adjustment expression is built from adjustment atoms `σ`, the
identity, composition, output entries (`push_outer h`), input entries
(`push_inner h t`) and lifts (`⇑ₕ`). Targets `t` are variables `h₍ᵢ₎` or
terms `u⟨ρ⟩`: a term atom `u` with a payload adjustment `ρ`, applied only
to `u`'s named variables. Labels are the bound label `·`, concrete
labels, and label atoms, ordered by the facts in context.

Two expressions are *equal* when they denote the same adjustment for
every interpretation of their atoms (consistent with the facts).

## Layered words

A *segment* is a context form with the identity tail: per label, in
label order, the targets of its first inputs and its number of outputs.
A *layered word* is a list of segments and atoms under lifts,

    S₁ ⨾ S₂ ⨾ ⇑ᴸσ ⨾ S₃ ⨾ …

and means their composition. A term `u` in a segment is written without
a payload and has the rest of the word as its payload: in
`⟦ x := u ⟧ ⨾ ⟦ y := v ⟧` the names of `u` see `y := v`. A chain of
substitutions is its own layered word, where its tree has size `2ⁿ`.

Three facts make this work.

- A named substitution is a renaming to a bound variable followed by an
  instantiation of that bound variable, and the names of a term never
  see the bound label:

      ⟦ x := u; y := v ⟧  =  ⟦ x; y \ ·; · ⟧ ⨾ ⟦ · := u ⟧ ⨾ ⟦ · := v ⟧

  So which term sees what is decided by the renamings between the
  instantiations.
- A term whose payload ends with the step before it moves in front of
  that step:

      ⟦ x | ⟦ y := w ⟧ ⟧ ⨾ ⟦ x := u⟨ y := w ⟩ ⟧  =  ⟦ x := u ⟧ ⨾ ⟦ y := w ⟧
      ⟦ x | σ ⟧ ⨾ ⟦ x := u⟨σ⟩ ⟧  =  ⟦ x := u ⟧ ⨾ σ

- An atom that acts on the names of one term only cannot be a step of
  the word, because everything that enters a word goes through every
  later atom except the finitely many variables lifted around it. Such
  a term keeps a word of its own before the rest: in `⟦ h := u⟨τ⟩ ⟧ ⨾ σ`
  with nothing else going through `τ`, the payload of `u` is `τ`, then
  what the term's *tail* does to the variables `τ` gives out, then the
  rest. The same holds for a term whose payload ends in a payload atom.

### The conditions

A layered word has many equal rearrangements. The canonical one is
fixed by the conditions `lnf` of `Core/LayeredUnique.v`; for a segment
`S` followed by the rest `r`:

1. *Kind.* `S` is a canonical segment (labels in order, no identity
   entry, no entry ending in a transparent target). It has a term, or
   it is a renaming that ends the word or stands before an atom in lift
   position (the atom is lifted once for each input sent around it, the
   `j`-th such input of `g` going to `g₍ⱼ₎`).
2. *Order.* The rest, as a payload, is strictly above the payload of
   every term the rest sends a variable to, in an order on what
   payloads do to named variables. So a term stands in the *last*
   segment whose rest is its payload: two terms with the same payload
   are in one segment, and of two segments that do not see each other
   the order says which is first.
3. *Routes.* A variable goes on as the least named variable of the
   rest with the same result, and as a bound variable only when there
   is none.
4. *Bound variables.* Every bound variable of the rest is used,
   distinct ones have distinct results, and they are numbered in the
   order of the first variables sent to them.

`lw_unique`: two words satisfying the conditions with the same free
meaning are the same word. The order is a parameter (irreflexive up to
agreement on named variables, transitive); `Core/LayeredOrder.v` gives
one and `lw_unique_sz` is uniqueness with it. `canon` uses the height
of a payload (how deep the terms it reaches are) and then what it does
to each variable in turn (`above`).

`lnf` covers terms with the identity payload and terms with a payload
atom followed by a renaming of bound variables. For a term that keeps
an atom in a word of its own, `canon` uses the conventions below, which
`lnf` does not state yet.

- The word of the term ends with its last atom; what the payload does
  after that atom is the term's tail, a renaming of bound variables
  only. Anything else the payload does after its last atom is on the
  line, as segments after the term's (`tsplit`).
- A term whose word ends with the atom that stands in front of it on
  the line, and whose tail agrees with what the segments in between do
  to the variables that atom gives out, stands in front of the atom
  instead (the second law above, `hop_at`).

## The normaliser

### The fold

`Core/Layered.v`. `lnorm` folds over the expression from its last step,
putting one step in front of a word.

- A lift is a close before and an open after, with the steps between
  one level deeper under the bound label; a segment is lifted over all
  the bound variables above it in one pass (`slifts`).
- A term whose payload goes on with further steps is put in front of
  those steps, which stay in the word, and everything else goes around
  them (`bypass_step`).
- A term whose payload has an atom, or a lift by the bound label,
  keeps the whole payload as a tree (`ptree`).
- Input entries nested in one another whose targets take no payload are
  one segment, built directly (`spine`).
- A segment without terms joins the segment after it, or is settled
  through the atom after it.

### The canonical word

`Core/Canonical.v`. `canon` goes through the word from its end:
`ccons s K` is the canonical word of the segment `s` followed by the
canonical word `K`, and `catom` that of an atom followed by `K`.

- *Keys* (`Core/Keys.v`). `vfollow K v` follows a variable through `K`
  as far as a term, an atom it is not lifted around, or the end. Two
  variables with the same key have the same result (`vfollow_sound`).
  Routes are compared by keys, never by building payloads.
- *Routes and numbering* (`Core/Retarget.v`). `reroute_g` sends every
  variable target of a segment to the representative of its key in the
  rest, and `renum` drops the bound variables nothing is sent to and
  numbers the others in the order of first use. Both are maps over the
  targets of a segment, tails of terms included (`tmap`), done in one
  pass over the entries in label order.
- *Join.* `scan` finds the last segment of `K` before which `K` does
  nothing to named variables that its rest can tell from the identity.
  The terms of `s` belong there. If that segment has them already, `s`
  only needs the variables that reach them (`shared`). Otherwise they
  are carried there by bound variables through the segments in between
  (`thread`), and the segments passed are brought back to canonical
  routes and numbering (`rr_up`, `sweep`). Terms with a tail have the
  tail carried along (`tshift`); the ones that cannot be carried stay.
- *Swap.* When the first segment of `K` has its terms on bound
  variables and the order puts `s` behind it, `s` goes behind (`swap`),
  through an inverse of the renaming it passes.
- *Split.* A term whose tail is more than a renaming of bound variables
  gets a segment of its own, with the rest of its tail after it
  (`singles`, `split1`).
- *Hop.* In front of an atom, a term of one of the following segments
  whose word ends with that atom goes in front of it (`hop_at`), and
  the segments passed are consed again.
- Otherwise `s` is a new first segment with canonical routes and
  numbering (`iface`).

The cons is recursive (a join or a hop conses the segments it changed),
with a bound on the number of steps of four times the length of the
word plus a hundred. When the bound runs out the step in hand is put in
front as it is, which is sound; no input found needs more.

## What `names` shows

Each step of the canonical word is one context form: a segment as a
full form `⟦ I \ O ⟧` or, when its outputs are all positional, a short
form; an atom under lifts as `⟦ x; ·; … | σ ⟧`. Term atoms are shown as
they were written. The rewrite of an adjustment to what is shown is
proved by deciding the equation.

Not shown: a segment with a term that keeps an atom in its payload, or
whose payload ends in a payload atom. Context forms have no way to
write such a payload, and `names` leaves an adjustment whose canonical
word has one as it is written.

`names` also applies an adjustment to a concrete variable: the variable
is followed through the canonical word, and when it reaches a term the
payload shown is the rest of the word, canonical again (`lapply_rest`
in `Core/LEval.v`). Materialising payloads compares trees
(`lmat_eqb`).

## The tree

The tree normal form is a *word*

    U₀ ⨾ ⇑ᴸ¹σ₁ ⨾ U₁ ⨾ ⇑ᴸ²σ₂ ⨾ … ⨾ ⇑ᴸⁿσₙ ⨾ Uₙ

of segments and atoms under lifts, with every term in the last segment
and a payload that holds everything that happens to its names
afterwards, atoms included. Its conditions:

1. **Segments are canonical.**
2. **Terms are in the last segment only**; `U₀ … Uₙ₋₁` are renamings.
3. **The segment before a lifted atom is in lift position.**
4. **Payload words are normal for what they mean**: a payload word is
   applied to named variables only, satisfies 1–3, and has no entry for
   `·` in its first segment and no lift by `·` on its first atom.

Theorems, all proved:

1. *Normal.* The tree of an expression satisfies the conditions
   (`tnorm_normal`, from `fold_normal` and `expand_normal` in
   `Core/LNormal.v` and `Core/Normal.v`).
2. *Unique.* Two words satisfying them that mean the same under every
   interpretation of their atoms are equal (`nf_unique`, `free_to_real`,
   `adequacy` in `Core/Unique.v`).
3. *Complete.* Equal expressions have the same tree (`tnorm_complete`),
   provided some interpretation satisfies the facts.
4. *Evaluation.* Evaluating a variable through a tree succeeds exactly
   when its result does not depend on the interpretation of the atoms,
   provided every label comparison it makes is known (`wtrace_sound`,
   `stuck_word`).

Uniqueness goes through a *free model*, in which applying an adjustment
to a variable gives a variable, a term with its continuation, or
*stuck* (an atom applied at a variable, with its continuation). Words
that are equal under every real interpretation are equal in the free
model (adequacy: an interpretation is chosen that tags the finitely
many stuck points a comparison meets), and normal words with equal free
meanings are equal, by peeling the first atom. `LayeredUnique` uses the
same model for layered words, with a term's continuation being the rest
of the word.

Composition of trees settles a segment before a lifted atom in one
pass: the inputs sent around the atom or to a term are read off the
segment, the atom is lifted once for each, and what happens to them
goes in a segment after the atom. Nothing is checked by composing back.

## Cost

Measured with `vm_compute` on the reified expressions, both sides
normalised and compared; times in seconds. *Before* is the decision
before the canonical word (layered fold, trees where the words differ).

| | steps | before | now |
|---|---|---|---|
| chain of substitutions, nested to the left against nested to the right | 256 | 0.52 | 0.031 |
| | 1024 | 20 | 0.26 |
| the same chain with an atom after each substitution | 64 | over 100 | 0.004 |
| | 1024 | | 0.18 |
| substitutions for one name | 512 | 6.8 | 0.06 |
| weakenings of distinct names | 512 | 0.44 | 0.33 |
| | 1024 | | 1.4 |
| one substitution under nested lifts | 128 | 0.39 | 0.51 |
| | 256 | 2.2 | 2.5 |
| a chain under nested lifts, then a substitution for each | 128 | 0.56 | 0.38 |
| | 256 | 3.0 | 1.8 |
| one simultaneous substitution | 256 | 0.16 | 0.015 |
| | 1024 | 1.8 | 0.12 |
| a term whose payload is a chain, then the chain, against the chain, then the term | 128 | 0.20 | 0.22 |
| | 512 | 5.4 | 3.0 |
| | 1024 | 38 | |

In the number `n` of steps:

- *Chains*, with or without atoms: a step in front of a canonical word
  is one new segment, after a look at the first segment. Linear.
- *A term whose payload is a chain of the word* joins the segment at
  the end of that chain: each of the `n` terms is looked for `n`
  segments away, so quadratic; before, cubic. The look itself composes
  only the entries a segment touches into the renaming carried along
  (`sstep`), and a term found there is not carried (`shared`).
- *Wide segments.* A simultaneous substitution is built as one segment.
  Composing two segments is a merge of two sorted lists when the label
  orders are known (`smerge`), and the maps over targets walk the
  entries once.
- *Lifts.* A step under `d` lifts by the bound label is a segment with
  `d` bound variables sent to themselves; indices are unary numbers, so
  looking up the `d` targets costs `d²`, and `n` nested lifts cost
  `n³`, as before.

For the laws in the tests (two or three steps) the normaliser takes
under a millisecond; the time of `names` is unfolding the notation,
reifying, and the kernel.

## What is left

- **The proof that `canon` is canonical.** `lnf` of the word it
  returns, with `above` as the order, and `lnf` extended to terms that
  keep an atom in their payload with the conventions above. With
  `lw_unique_real` this gives: equal expressions have the same
  canonical word. The tree comparison in `nf_eq_t`, `Core/LNormal.v`
  and the bound on the tree size then have no use left.
- **Checks instead of proofs.** `swap`, `split1`, `singles`, the join
  that carries only some of the terms, and the hop (`hop_chk`) compose
  the segments they return and compare the result with what they
  replace; `renum` checks that its numbering covers the bound variables
  it renumbers. Each is a law about segments that wants its own proof,
  as `unterm` has (`unterm_sound`).
- **The bound on the steps of the cons** is not shown to be enough.
- **Showing terms that keep an atom in their payload** needs context
  forms that can write such a payload.
- **Materialising payloads** from the canonical word instead of the
  tree.
- **Nested lifts** in time quadratic in their depth: composing under
  the leading bound variables of a lifted segment without writing them
  out, or binary indices.
