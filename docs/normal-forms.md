# Normal forms of adjustments

Composition is written `⨾`, in diagrammatic order: `a ⨾ b` is `a`, then
`b`, so `t [a] [b] = t [a ⨾ b]`.

## Status

`names` computes with *layered words* (`Core/Layered.v`): a list of
segments and atoms in which a term is written once, where it is
substituted, and has the rest of the word as its payload. The normal
form of this file, a tree, is the layered word multiplied out
(`expand`).

- Sound: the layered word of an expression means what the expression
  means (`lnorm_sound`), and so does its tree (`tnorm_sound`).
- Theorem 1: the tree satisfies the conditions below (`tnorm_normal` in
  `Core/LEval.v`, from `fold_normal` and `expand_normal` in
  `Core/LNormal.v` and the operations keeping the conditions,
  `Core/Normal.v`).
- Theorem 2: `nf_unique` in the free model, with `free_to_real` and
  `adequacy` (`Core/Unique.v`).
- Theorem 3: `tnorm_complete`: expressions that mean the same have the
  same tree. The decision `nf_eq_t` compares the layered words and,
  when they differ, the trees; it is sound (`nf_eq_t_sound`) and
  answers `true` for equal expressions whenever it builds both trees,
  which it does up to 100000 nodes (`nf_eq_t_complete`).
- Theorem 4: `wtrace_sound` (`Core/Normalise.v`) and `stuck_word`
  (`Core/Complete.v`), for trees.

Everything `names` does reads the layered word (`Core/LEval.v`): the
decision, the result of a variable (followed through the word, without
multiplying out), the payload checks and materialising payloads. A
normal form is shown as its tree when the tree is small; otherwise
`names` leaves that adjustment as written.

What is not proved is that the layered word itself is unique: two
expressions that mean the same can get different words, and the
decision then needs their trees, which for a long chain of
substitutions are too large to build. See *Layered words* below for
the conditions under which layered words are unique (proved), and what
the normaliser lacks to meet them.

What the facts say about each pair of label variables is worked out
once per normalisation (`order_of`), so a label comparison is a lookup
rather than a search through the facts.

The label order is dense with no least or greatest label (the end of a
string sorts just above `\000`), so facts `x < y` never force two label
variables to be equal. Completeness takes one interpretation satisfying
the facts as a hypothesis: when the facts are contradictory there is
nothing to prove, and the context `names` runs in supplies one.

## Expressions and their meaning

An adjustment expression is built from adjustment atoms `σ`, the
identity, composition, output entries (`push_outer h`), input entries
(`push_inner h t`) and lifts (`⇑ₕ`). Targets `t` are variables `h₍ᵢ₎` or
terms `u⟨ρ⟩`: a term atom `u` with a payload adjustment `ρ`, applied only
to `u`'s named variables. Labels are the bound label `·`, concrete
labels, and label atoms, ordered by the facts in context.

Two expressions are *equal* when they denote the same adjustment for
every interpretation of their atoms (consistent with the facts). The
normal form is a complete invariant: equal expressions have the same
normal form.

## The normal form

A normal form is a *word*

    U₀ ⨾ ⇑ᴸ¹σ₁ ⨾ U₁ ⨾ ⇑ᴸ²σ₂ ⨾ … ⨾ ⇑ᴸⁿσₙ ⨾ Uₙ

of segments `Uᵢ` and atoms `σᵢ` under multisets of lifts `Lᵢ`; `Uᵢ₋₁` is
applied just before `σᵢ`. A segment is a context form with the identity
tail: per label, in label order, the targets of its first inputs and its
number of outputs. Write `Vᵢ` for the variables `⇑ᴸⁱ` passes around
`σᵢ`: `h₍₀₎ … h₍ₖ₋₁₎` for each `h` lifted `k` times.

The conditions:

1. **Segments are canonical**: labels in order and distinct; no entry is
   the identity; no entry ends with a transparent target (a last target
   `h₍ₘ₋₁₎` with `m` outputs is the same as no target and `m - 1`
   outputs).
2. **Terms are in the last segment only.** `U₀ … Uₙ₋₁` are renamings. A
   term substituted before an atom is carried past it: the input is
   passed around the atom, and the term sits in `Uₙ` with a payload that
   holds everything that happens to its names afterwards, atoms
   included.
3. **The segment before a lifted atom is in lift position.** Let `Pᵢ` be
   the inputs `Uᵢ₋₁` sends into `Vᵢ`. Then `Lᵢ` lifts each label `g`
   exactly as many times as `Pᵢ` has inputs labelled `g`, and `Uᵢ₋₁`
   sends the `j`-th input of `Pᵢ` labelled `g` (in index order) to
   `g₍ⱼ₎`. So which inputs are passed around `σᵢ` is read off `Uᵢ₋₁`,
   and what happens to them (renaming, merging, substituting) is in the
   segments after the atom.
4. **Payload words are normal for what they mean.** A payload word is
   applied to named variables only. It satisfies 1–3, and its first
   segment has no entry for `·` and its first atom no lift by `·` (no
   named input is passed around it as a `·` variable, by condition 3).

The normal form is internal. It is chosen to be the easiest form to
prove unique, not to be read.

## Settling in one pass

Composition meets `A' ⨾ ⇑ᴸσ ⨾ A` with `A'` not in lift position (in the
code's order, `A ∘ ⇑ᴸσ ∘ A'`). The settled form is computed directly
from the entries of `A'`:

- `P`: the inputs `A'` sends to a variable of `V` or to a term.
- `L'`: each label `g` lifted once per input of `P` labelled `g`.
- `U`: `A'` with the `j`-th input of `P` labelled `g` sent to `g₍ⱼ₎`,
  and every other target `z` re-indexed from `L` to `L'`
  (`shift_L' (unshift_L z)`).
- `Q`: per label `g`, the original targets of the inputs of `P` labelled
  `g`, in order, and `L`'s number of lifts by `g` as its outputs. A term
  target gets `⇑ᴸσ` composed into its payload.

Then `A' ⨾ ⇑ᴸσ ⨾ A = U ⨾ ⇑ᴸ'σ ⨾ (Q ⨾ A)`, and `U` is in lift position
for `L'` by construction. This covers a skipped passed-around variable
(it is not in `P`, so its lift goes and `Q` shifts), renaming, merging
and terms uniformly. There is no fuel and nothing is checked by
composing back.

This replaces the current loop of shift, pull, push and peel steps.

## What `names` shows

The expression `names` produces is a function of the normal form, so
equal adjustments are shown identically whatever that function does; it
needs no part in the uniqueness proof. Each rewrite to the shown
expression is proved by deciding the equation, as now. The function:

- A maximal run of atoms with the same lifts and the identity between
  them is the tail of one context form `⟦ I | Γ \ O | Γ[σ ⨾ … ⨾ σ'] ⟧`,
  whose inputs `I` are the variables passed around the run.
- The segment after a run is split into the part on the variables passed
  around it, which gives the form's outputs `O`, and the part on the
  run's outputs, which is a separate form (left out when it is the
  identity). The split is not made when the second part would put an
  output of the run underneath one of the form's outputs of the same
  label (`⟦ x | σ ⟧ ⨾ ⟦ y \ x ⟧`); the segment is then shown whole.
- A term whose payload starts with the atoms it was carried past is
  shown before them: `⟦ x := u ⟧ ⨾ σ`, not `⟦ x | σ ⟧ ⨾ ⟦ x := u⟨σ⟩ ⟧`.
- A form with no entries is shown as its tail.

So forms join where they share known variables and stay apart where the
later one only acts on what the earlier one's tail produced:
`⟦ x | σ ⟧ ⨾ ⟦ x \ y ⟧ ⨾ ⟦ y | τ ⟧` is `⟦ x | Γ \ y | Γ[σ ⨾ τ] ⟧`, while
`⟦ x | σ ⟧ ⨾ ⟦ y \ z ⟧` stays as it is.

## The theorems

1. *Normal.* If the normaliser returns a word, the word satisfies
   conditions 1–4. (It fails, rather than returning something else, when
   a label order it needs is unknown or its bound on payload depth runs
   out.) Proved, not checked at run time.
2. *Unique.* Two words satisfying 1–4 that denote the same adjustment
   for every interpretation of their atoms are equal.
3. *Complete.* Hence two expressions that are equal under every
   interpretation satisfying the facts, and that the normaliser
   normalises, have the same normal form, provided some interpretation
   satisfies the facts.
4. *Evaluation.* Evaluating a variable through a normal form succeeds
   exactly when its result does not depend on the interpretation of the
   atoms, provided every label comparison it makes is known from the
   facts. When it reaches a target, that target is the result under every
   interpretation; when it gets stuck at an atom, the result depends on
   the interpretation of the atoms even with the labels fixed.

   With a comparison unknown, evaluation gives up even where the result
   is determined: the adjustment that sends `x₀` to `y₀` and leaves every
   other `xⱼ` alone sends `z₁` to `z₁` whether or not `z` is `x`. Deciding
   such cases would mean evaluating under every consistent choice of
   which unknown labels are equal; instead, a fact or a case split on the
   labels resolves them.

## Plan of the proof

### The free model

Real adjustments are finitary: an adjustment sends only finitely many
variables of a label anywhere but along that label's tail, so no real
interpretation of an atom can tag every variable. The proof therefore
goes through a *free model*, in which applying an adjustment to a
variable gives one of

- a variable;
- a term `u` with its continuation `k`;
- *stuck*: atom `a` applied at variable `z`, with continuation `k`,

where a continuation is a function from variables to such results (what
the rest of the word does to whatever comes back; for a term, only its
values on named variables matter). Words are given a meaning in the
free model directly, by the same case analysis the real meaning
satisfies. A stuck result shows the atom, where it was applied, and the
whole of the rest, with no index bounds and no encoding.

### Steps

1. **Internal normal form.** Return terms to the last segment (undo
   "terms before atoms" in the normaliser; it becomes a display step).
2. **One-pass settle**, replacing the step loop, with its soundness
   proof. Needs the action of `⇑ᴸσ` on a variable in terms of
   multi-label shift and unshift, which later steps reuse.
3. **The predicate** for conditions 1–4, as a proposition.
4. **Normal** (theorem 1). One syntactic lemma: setting an entry keeps a
   segment canonical; every segment operation goes through it.
   Composing renamings gives a renaming. Lifting a word and pushing an
   input entry keep lift position. Settle gives lift position by
   construction. Payload normalisation gives condition 4.
5. **The free model**, the meaning of words in it, and: words equal in
   the free model are equal under every real interpretation (a relation
   between free results and real results, by induction on the word; no
   bounds).
6. **Unique in the free model** (done). For words satisfying 1–4 with
   equal free meanings, by induction on size, peeling the first atom:
   - far enough along a label, a word sends every variable through each
     of its atoms in turn, so the first atoms agree, and the number of
     atoms left in a continuation is determined by it;
   - an input is passed around `σ₁` in one word exactly when it is in
     the other: stuck at `σ₁`, a result has a continuation with all the
     remaining atoms, while a passed-around input that gets stuck later
     has fewer; by lift position the passed inputs give `L₁`;
   - where the inputs go shows `U₀` as a renaming, hence syntactically;
   - the rest of the word is determined on `V₁` by the passed inputs and
     elsewhere by the continuation of a stuck one, so the rests agree by
     induction;
   - with no atoms left, the segments agree entry by entry, and their
     terms' payload words by induction, using condition 4.
7. **Adequacy** (done). Words equal under every real interpretation
   are equal in the free model. Free results are compared on a finite
   list of probe variables at a time; free results that agree on every
   such list are equal. A comparison on a list meets finitely many stuck
   points, and an interpretation is chosen that tags exactly those:
   terms are tags (a term atom, an atom applied at a variable, a
   payload atom), an atom sends each stuck point to its tag with a
   payload that sends some names to the probes, and a payload atom
   sends a name to its tag and further names to the probes. Since
   whatever happens afterwards is composed into these payloads, the
   real results read back the free ones on the probes. This does not
   depend on conditions 1–4.
8. **Complete and evaluation** (theorems 3 and 4), from 4, 6 and 7 and
   the soundness of the normaliser. For evaluation: it fails exactly
   when the free result is stuck, and a stuck result changes with the
   interpretation of its atom.
9. **Display** as a function of the normal form, including terms before
   atoms.

The normaliser makes no run-time checks of label distinctness: its
soundness lemmas assume of their inputs, and prove of their outputs,
that every segment of a word, payload words included, has distinct
labels (`wdist` in `Core/Normalise.v`).

Not shown yet: a term whose payload adjustment ends in a payload atom,
or whose payload, once the atoms it was carried past are taken off, is
still more than one segment. `names` leaves such adjustments as they
are.

## Layered words

### The blow-up

Condition 2 puts every term in the last segment, with a payload holding
everything that happens to its names afterwards. In a chain of
substitutions

    ⟦ x₁ := u₁ ⟧ ⨾ ⟦ x₂ := u₂ ⟧ ⨾ … ⨾ ⟦ xₙ := uₙ ⟧

`u₁`'s payload is the normal form of the rest of the chain, which holds
`u₂` with its own payload, and so on: the tree has size about `2ⁿ`,
although the expression has size `n`. (An earlier version stored each
distinct payload once in a table; that is `n²` for a chain, and has
been removed.)

A layered word writes a term once, where it enters, and leaves to the
rest of the word whatever the rest does anyway: a chain is its own
layered word.

### Two facts

Checked with `names_eq`:

    ⟦ x := u ⟧  =  ⟦ x \ · ⟧ ⨾ ⟦ · := u ⟧
    ⟦ x := u; y := v ⟧  =  ⟦ x; y \ ·; · ⟧ ⨾ ⟦ · := u ⟧ ⨾ ⟦ · := v ⟧

A named substitution is a renaming to a bound variable followed by an
*instantiation* of that bound variable, and an instantiation touches
only the bound label, which the names of a term never see. So which
term sees what is decided by the renamings between instantiations
alone, and renamings compose without growing. Without atoms no payload
needs to contain a term: a term's payload is what the renamings after
it do to its names, with bound variables standing for the terms
instantiated later.

### The order is not forced

Where one term's payload mentions another, the first must come first.
Otherwise either order works. Both of these are
`⟦ a := u⟨ x := p ⟩; b := v⟨ x := q ⟩ ⟧`:

    ⟦ a; b \ ·; ·; x as w ⟧ ⨾ ⟦ · := u ⟧ ⨾ ⟦ x as c; · as d \ · as d; · as c; x as e ⟧
      ⨾ ⟦ · := v ⟧ ⨾ ⟦ x := q ⟧ ⨾ ⟦ · := p ⟧

and the same with `u`, `p` and `v`, `q` exchanged. A unique form has
to choose, and nothing in the adjustment makes the choice: the
conditions below take an order on payloads.

### Lifts and payloads

- Terms never see the bound label, so a lift is a close and an open
  around the word, and a substitution for the lifted name afterwards
  meets the open at the seam:

      ⟦ x | a ⟧  =  ⟦ x \ · ⟧ ⨾ ⟦ · | a ⟧ ⨾ ⟦ · \ x ⟧
      ⟦ y | a ⟧ ⨾ ⟦ y := v ⟧  =  ⟦ y \ · ⟧ ⨾ ⟦ · | a ⟧ ⨾ ⟦ · := v ⟧

- A term whose payload ends with the step before it moves in front of
  that step, one step at a time:

      ⟦ x | ⟦ y := w ⟧ ⟧ ⨾ ⟦ x := u⟨ y := w ⟩ ⟧  =  ⟦ x := u ⟧ ⨾ ⟦ y := w ⟧

- A term before an atom stays there: in `⟦ x := u ⟧ ⨾ σ` the atom is
  part of the rest. An atom that acts on the names of one term only
  cannot be a step of the word, because everything that enters a word
  goes through every later atom except the finitely many variables
  lifted around it: in `⟦ h := u⟨τ⟩ | σ ⟧` the term keeps `τ` in a
  payload of its own.

### The normaliser

`Core/Layered.v`. The normaliser needs one operation on layered words,
putting one step in front of a word, and folds over the expression
from its last step, whatever the nesting.

- A layered word is a list of segments and atoms; its meaning is their
  composition, so a term in a segment has the rest of the word after
  its payload.
- A lift is a close before and an open after, with the steps between
  one level deeper under the bound label (`lift_close_open`). A
  segment is lifted over all the bound variables above it in one pass
  (`slifts`).
- A term whose payload goes on with further steps is put in front of
  those steps, which stay in the word, and everything else goes around
  them: an input entry is undone by a weakening before it, and the
  variable an output entry creates is carried past it as a bound
  variable (`bypass_step`).
- A term whose payload has an atom, or a lift by the bound label,
  keeps the whole payload as a tree (`ptree`).
- A segment without terms joins the segment after it, or is settled
  through the atom after it as in the tree normal form.
- `lnorm_sound`: the layered word of an expression means what the
  expression means. The fold has a word for every expression, provided
  the order of the labels it has to compare is known. It compares more
  labels than the tree does: a payload's labels with the label
  substituted for, since both are entries of one segment
  (`⟦ z := w⟨ x := u ⟩ ⟧` needs the order of `x` and `z`).

### When layered words are unique

`Core/LayeredUnique.v` has the normal-form conditions and uniqueness,
for every layered word:

- The free meaning of a layered word is its steps one after the other,
  each with the rest as its continuation (`flw`); a term's continuation
  is the rest of the word.
- `lnf`, for a segment `S` followed by `r`:
  1. `S` is a canonical segment. A term of `S` has the identity
     payload, or a payload atom followed by a renaming of its bound
     variables only. `S` has a term, or is a renaming that ends the
     word or stands before an atom in lift position (condition 3 of the
     normal form above).
  2. The payload of `S`'s terms (the rest) is above the payload of
     every term the rest sends a variable to, in a strict order on what
     payloads do to named variables; a last segment that does nothing
     to named variables has a term (otherwise it is part of the segment
     before).
  3. A variable goes on as the least named variable of the rest with
     the same result, and as a bound variable only when there is none;
     the same for the bound variables of a term with a payload atom.
  4. Every bound variable of the rest is used; distinct ones have
     distinct results; and they are numbered in the order of the first
     variables sent to them.

  An atom has a canonical list of lifts.
- `lw_unique`: two words satisfying `lnf` with the same free meaning
  are the same word. `lw_unique_real`: so are two that mean the same
  under every interpretation of the atoms (`lw_adequacy`, as for
  words). The two words are compared from the front: the terms of the
  first segments have the rests as payloads, which makes the rests
  agree on named variables; conditions 3 and 4 then fix the segment,
  and the rests are compared in turn. The atom case is `Unique.peel`
  again.

`Core/LayeredOrder.v` has the order:

- A payload has at most one normal word (as a payload, in the sense of
  the normal form above), so any strict order on words is an order on
  payloads with what uniqueness needs (`gt_of`), and a total order on
  words puts any two payloads that have normal words in order
  (`gt_of_total`).
- `ord_sz` compares sizes first and then a serialisation of the words
  (`wcode`, shown injective). It is total. A word is above the payload
  words of the terms in it (`ord_sz_term`), so a term that sees a layer
  is above that layer and the usual step needs no comparison. Where two
  layers do not see each other the serialisation decides, which is the
  arbitrary choice a normal form has to make here.
- `lw_unique_sz`: uniqueness with this order, with no hypothesis left
  on it.

`segok_entry` shows the conditions of a substitution step in front of a
word, and `Tests/LayeredNfTests.v` uses it to show that a chain of two
substitutions satisfies `lnf` with `gt_sz`.

### What the normaliser lacks

The word the fold returns does not always satisfy `lnf`, and two
expressions that mean the same can get different words. Of the 93
equations decided while building the tests and examples, 90 have equal
words. The other three are the laws that relate a substitution in a
payload to the same substitution in the word, such as the third law
above: on its left the fold writes `w` twice, once for the lifted
substitution and once for the payload, where the conditions want it
once. These are decided on the trees.

What the fold lacks is the same in every case found: deciding that a
term does not belong in a new first layer. A term `u` put in front of a
word `K` with a payload `p` other than the identity has the payload
`p ⨾ K`. The fold always opens a new layer for it, with `p` written
between that layer and `K`. The conditions want `u` in the layer whose
rest means `p ⨾ K` on named variables, if there is one, and otherwise
in a new layer at the place the order gives. When the first segment of
`K` sends a named variable to a term, the new layer is above it and
nothing needs comparing; this is the case of a chain. When it does
not, `p` and the renamings of `K` have to be followed layer by layer
until a named variable reaches a term or the word ends:

1. it ends, or reaches a layer, with every named variable where the
   layer's rest has it: the term joins that layer, through a bound
   variable carried there;
2. a named variable reaches a term first: a new layer, and its place
   among the layers passed on the way is the order's to decide. These
   are families that do not see each other, and comparing them means
   comparing payloads as wholes.

With that, the fold also has to send variables with one result to one
variable, number bound variables by their sources, and drop bound
variables nothing uses any more (which can cascade down the word).
None of this is written.

### Cost

Measured with `vm_compute` on the reified expressions, both sides
normalised and compared; times in seconds. *Table* is the removed
normaliser that stored each payload once.

| | steps | table | layered |
|---|---|---|---|
| chain of substitutions, nested to the left against nested to the right | 64 | 0.032 | 0.007 |
| | 256 | 0.62 | 0.027 |
| | 1024 | | 0.20 |
| the same chain with an atom after each substitution | 16 | 1.0 | 0.003 |
| | 64 | over 250 | 0.007 |
| | 1024 | | 0.16 |
| substitutions for one name | 256 | 1.0 | 0.031 |
| weakenings of distinct names | 256 | 0.20 | 0.18 |
| | 1024 | | 1.3 |
| one substitution under nested lifts | 8 | 0.021 | 0.021 |
| | 64 | 0.064 | 0.19 |
| | 128 | 0.33 | 1.2 |
| one simultaneous substitution | 64 | 0.018 | 0.20 |
| | 128 | 0.12 | 0.68 |

In the number `n` of steps:

- *Chains.* A step in front of a layered word is one new segment:
  linear, in time and size, with or without atoms between the
  substitutions.
- *Wide segments.* Composing a segment into another looks up every
  target of the one in the other by walking its entries, and puts each
  entry back by walking again (`sgo`, `sfind`, `sset`). So composing
  costs the product of the two widths, and `n` weakenings of distinct
  names, which end in one segment of `n` entries, cost `n²`. A merge
  of the two sorted lists would be linear.
- *Lifts.* A step under `d` lifts is a segment with `d` bound
  variables sent to themselves. The `d` targets are looked up one by
  one when the segment is composed into the first segment of the word,
  `d` times its width, so `n` nested lifts cost `n³`. Composing under
  the first `d` bound targets of the word's first segment, without
  writing them out, would make this quadratic.
- *Where the two words differ*, the trees are built: exponential in
  the length of a chain. The decision gives up, and fails, when a tree
  passes 100000 nodes (`expand_c`): the third law above with a payload
  that is a chain of 14 substitutions takes 0.3 s, and with 16 fails.
  The removed normaliser decided it for 128 in 0.2 s.

In practice the normaliser is not where the time goes. For the laws in
the tests (two or three steps) `names_eq` takes 30 to 80 ms, of which
the normaliser is under 1 ms; the rest is unfolding the notation,
reifying, and the kernel. A chain of 48 substitutions over label
variables with 47 order hypotheses takes 2.1 s, of which the
normaliser is 1 ms and reifying 0.8 s (every label and term is looked
up in a list); it took 8.4 s before the order hypotheses were
collected in one pass and the order table computed by one closure.

Still to do:

- The fold canonical as described above and `lnf` of its result, so
  that equal expressions have equal words and no tree is needed.
- Composition under bound targets and a linear merge of segments.
- `ord_sz` puts layers of two families that do not see each other in
  size order, which interleaves them; an order that keeps a family
  together would give smaller words and fits the same construction.
