# Normal forms of adjustments

Composition is written `⨾`, in diagrammatic order: `a ⨾ b` is `a`, then
`b`, so `t [a] [b] = t [a ⨾ b]`.

## Status

Theorems 1–4 below are proved, for the normaliser `names` runs: it
stores normal forms in the shared form of the last section
(`Core/Shared.v`), and the normal form of this file is the unfolding of
what it stores.

- Theorem 1: `anorm_s_normal` (`Core/Shared.v`), from the operations
  keeping the conditions (`Core/Normal.v`).
- Theorem 2: `nf_unique` in the free model, with `free_to_real` and
  `adequacy` (`Core/Unique.v`).
- Theorem 3: `complete_sh` (`Core/Shared.v`), with soundness
  `nf_eq_sh_sound`.
- Theorem 4: `wtrace_sound` (`Core/Normalise.v`) and `eval_stuck`
  (`Core/Shared.v`).

Everything `names` computes reads the stored word (`Core/Eval.v`): the
decision, evaluating a variable, checking a payload, materialising
payloads. Only showing a normal form unfolds it, and only when the tree
is small; otherwise `names` leaves that adjustment as written. A chain
of sixteen substitutions is decided in well under a second.

What the facts say about each pair of label variables is worked out
once per normalisation (`order_of`), so a label comparison is a lookup
rather than a search through the facts.

A chain of compositions is normalised from its last step, whichever way
it is nested (`renest` in `Core/Normalise.v`; `names` calls the
normaliser through the `_r` functions of `Core/Eval.v`, which re-nest
first). Composing a short word before a long one gives the terms of the
short one the long one as payload, one definition; composing it after
gives every term of the long one a new payload. A chain of 48
substitutions written `(… ⨾ …) ⨾ …` took 1128 definitions and 7
seconds, and takes 47 definitions and 0.02 seconds; 250 take 0.4
seconds.


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

## Sharing

### The blow-up

Condition 2 puts every term in the last segment, with a payload holding
everything that happens to its names afterwards. In a chain of
substitutions

    ⟦ x₁ := u₁ ⟧ ⨾ ⟦ x₂ := u₂ ⟧ ⨾ … ⨾ ⟦ xₙ := uₙ ⟧

`u₁`'s payload is the normal form of the rest of the chain, which holds
`u₂` with its own payload, and so on: written out as a tree, the normal
form has size about `2ⁿ`, although the expression has size `n`.

### Why not share through the word itself

One could try to leave each term where it is substituted, with what
follows in the word acting on its names, so that later steps are written
once. This cannot be the general mechanism. An atom passes only finitely
many variables around it (its lifts), so everything that enters the word
at some point goes through every later atom. In

    ⟦ h := u⟨τ⟩ | σ ⟧

`u`'s names go through `τ` and the other inputs through `σ`; no single
sequence of atoms does both, so `τ` has to stay in `u`'s payload. Terms
inside such payloads can then only be shared with the main word, or
with each other, by reference. Canonical positions within the word also
need three separate tie-breaks (which position, which of several equal
payloads, a variable or a term), with examples of each in the history
of this file.

### Named payloads

The normal form already has references: payload atoms. A term whose
payload is not the identity is stored as the term with a *defined*
payload atom,

    u⟨β⟩      β := (w, b)

where `w` is a payload word, itself stored this way, and `b` is the
identity or a payload atom of the expression: `β` denotes `w ⨾ b`.
Definitions are kept in a table, and equal definitions get the same
atom. So a stored word is *flat* (every payload is the identity
followed by an atom) and each distinct payload is written once.

- The operations of the normaliser run unchanged on flat words, where a
  defined atom is as opaque as any payload atom. After each one, the
  result is flattened: a term `u⟨p ⨾ β⟩` with `β := (w, b)` gets the
  atom defined as the normal form of `p ⨾ w` for `b`, flattened in
  turn; results are remembered per `(β, p)`.
- The tree normal form of this file is the *unfolding* of the stored
  form, replacing defined atoms by their definitions. Conditions 1–4 and
  theorems 1–4 are about the unfolding and are unchanged.
- In one table, two flat words with the same unfolding are the same, so
  equality of normal forms is equality of stored words.
- Each term of the expression has one continuation, so there is at most
  one definition per term occurrence and operation, each of polynomial
  size: the chain above takes about `n²` space.

Steps (all done):

1. Normal forms are well scoped: every payload atom is below a bound
   (part of the predicate, kept by every operation).
2. The table, its meaning (definitions extend the payload environment),
   flattening, and the shared normaliser, with soundness
   (`norm_s_spec`, `nf_eq_sh_sound`): `names` decides equations with
   it. The defined atoms are numbered from above the payload atoms of
   the two expressions, so there is no side condition.
3. Unfolding: the unfolding of a stored word is a normal form with the
   same meaning (`unfold_spec`); in a table with no repeated and no
   identity definitions, flat words with the same unfolding are the
   same (`unfold_inj`); hence completeness for the shared decision
   (`complete_sh`).
4. Everything else reads the stored form (`Core/Eval.v`), and there is
   no tree normaliser. Evaluation and the payload checks
   (`apply_result_s`, `apply_bind_check_s`, `mat_eqb_s`) unfold
   nothing: a variable is the same in the stored word, and payloads are
   compared as atoms of one table. Display (`anorm_show`) unfolds on
   demand, and only when the tree has at most `show_budget` nodes.

## Layered form (proposed)

The stored form writes each payload once, but a payload still lists
everything that happens to its term's names: a chain of `n`
substitutions takes `n²` space, and as a tree `2ⁿ`. The layered form
writes a term once, where it enters, and leaves to the rest of the word
whatever the rest does anyway. It is meant to replace the normal form;
for now it is a function of the stored form (`Core/Layers.v`), used to
test the rule.

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

and the same with `u`, `p` and `v`, `q` exchanged. So terms that do
not depend on each other are put in one layer, each with a renaming
payload saying how it differs from the rest:

    ⟦ a := u⟨ x as c ⟩; b := v⟨ x as d ⟩ \ · as c; · as d ⟧ ⨾ ⟦ · := p; · := q ⟧

### The form

A *party* is the adjustment itself (the root) or a term occurring in
it with its payload; two occurrences of a term with the same payload
are one party. The word is built from its end. At each point there is
the rest `W` built so far, and each party not yet placed has a
*remainder* `K`: its payload is `K ⨾ W`.

The terms are placed in depth-first postorder from the root, so each
after the terms its payload mentions, and a family of terms together.
From a party, the terms it mentions are visited in order of how much
of their payload the party has itself, least first: the term that
continues the party (the next of a chain) is visited last and ends up
next to it.

Before a term is placed:

1. **An atom is shared** when every remaining party ends with it.
2. **What of the term's remainder another remaining party has is
   shared**: per label, the longest end of its entries that some other
   party's entries end with. Every party is then divided by the shared
   step. A party that has it loses it. A party that lacks it gets a
   *shield*: a renaming that steps over the shared entries, which the
   shared step undoes. A reference to an output that the shared step
   creates becomes a bound variable that the step *opens* (sends to
   that output) instead of creating the output from nothing.
3. **The term is placed**, with what is left of its remainder as its
   payload: renamings no other party has, and atoms not shared. With it
   are placed the terms that have nothing left of their remainder and
   are mentioned by a party still waiting for the term being placed;
   they would otherwise end up before steps they need to see through.

The root's remainder is the first step of the word. Shields are entries
like any other: the parties that lack a family's substitutions all get
the same shield, and it is shared among them once, when the first of
them is placed.

A term with no bound variables of its own coming in (no opaque payload
atom, no atom) has whatever the others agree on for the bound label.

Written out:

- A reference to a term not yet instantiated is a bound variable, from
  the first step that refers to it until its layer; bound variables in
  use are ordered by layer, the next innermost.
- A term referred to once, from a segment, with only instantiations
  between that segment and its layer, is written there: `⟦ x := u ⟧`
  rather than `⟦ x \ · ⟧ ⨾ ⟦ · := u ⟧`.
- Layers of instantiations in a row are one.

### Atoms

A term before an atom stays there: in `⟦ x := u ⟧ ⨾ σ` every party
ends with `σ`, so `σ` is shared and `u` has the identity payload. The
stored form instead carries `u` past the atom, as
`⟦ x | σ ⟧ ⨾ ⟦ x := u⟨σ⟩ ⟧`. Read from the stored form, a party in
which a variable is passed around the atom to a remaining term has the
atom if that term has it; the lift over that variable goes when the
atom is shared.

An atom that only some parties have stays in their payloads:
`⟦ h := u⟨τ⟩ | σ ⟧` keeps `τ` as `u`'s payload. Around a shared atom
the conditions on lifts (3 and 4 above) apply to the renamings as they
do now.

### What the prototype shows

`Core/Layers.v` computes the layered form of a stored word, as an
expression; `layers_check` normalises it again and compares
(`Tests/LayersTests.v`; `tests/fuzz/run.sh` for random expressions).
Sizes count entries, outputs, lifts, atoms and terms.

- Correct on some 2600 random expressions, including label variables
  whose order is partly unknown; the rule applied in every one.
- Linear where the stored form is quadratic and the tree exponential:

  | | expression | layered | stored |
  |---|---|---|---|
  | chain of 32 substitutions | 64 | 64 | 1552 |
  | the same with an atom after each (16) | 48 | 48 | 1376 |
  | chain of 16, then a renaming | 34 | 34 | 442 |
  | a term whose payload is a chain of 16, on a chain of 16 | 66 | 88 | 787 |
  | 3 terms with one chain of 8 as payload, 3 with another | 108 | 64 | 218 |
  | 8 terms, each with its own chain of 2 | 48 | 79 | 80 |

  A chain, with or without atoms, comes back as written.
- On random expressions the layered form is 15 to 50 percent smaller
  than the tree and 15 to 40 percent smaller than the stored form, and
  15 to 45 percent larger than the expression.

Two rules were tried and dropped:

- *Sharing only what every remaining party has.* Two families of terms
  with nothing in common then share nothing: the fourth row above came
  out as 338, quadratic. Hence shields.
- *Placing every term as soon as it can be*, or in plain postorder.
  The first carries terms with the identity payload across every other
  family through long-lived bound variables; the second leaves a term
  that has used up its payload in front of shields it must see through.
  Hence postorder with the terms that ride along.

### Computing it directly: not settled

The prototype computes the form from the stored form, which is the
quadratic thing it is meant to replace. A normal form has to be
computed directly: composing two layered words should cost about what
the seam costs.

What is established (the three laws are checked with `names_eq`):

- Terms never see the bound label, so a lift is a close and an open
  around the word, and a substitution for the lifted name afterwards
  meets the open at the seam:

      ⟦ x | a ⟧  =  ⟦ x \ · ⟧ ⨾ ⟦ · | a ⟧ ⨾ ⟦ · \ x ⟧
      ⟦ y | a ⟧ ⨾ ⟦ y := v ⟧  =  ⟦ y \ · ⟧ ⨾ ⟦ · | a ⟧ ⨾ ⟦ · := v ⟧

  A word that does not mention the bound label is its own lift over
  it, so neither costs more than the seam.
- A term whose payload ends with the step before it moves in front of
  that step, one step at a time:

      ⟦ x | ⟦ y := w ⟧ ⟧ ⨾ ⟦ x := u⟨ y := w ⟩ ⟧  =  ⟦ x := u ⟧ ⨾ ⟦ y := w ⟧

- Writing two layered words side by side and composing at the seam
  gives the prototype's form for 86 percent of random pairs (92 percent
  without the bound label). Two of the differences are in where the
  rule puts things and could be changed in the rule: an entry of the
  bound label next to the instantiation of a term that does not see it,
  and an atom shared only when what follows it sends variables to
  terms.

What stands in the way is not in the details of the rule:

- **Independent families.** When an adjustment has two families of
  terms that do not see each other, either can be the main line of the
  word, with the other's variables carried through it as bound
  variables. `⟦ y₁; y₂ | B ⟧ ⨾ C` with `B` and `C` chains is also
  `⟦ x₁; x₂; x₃ | C ⟧ ⨾ B`; composing at the seam gives two different
  words, and the prototype's form is a third (it keeps the last term
  of `B` for the end). A normal form has to choose, the choice cannot
  come from the order of composition, and no choice is determined by
  the adjustment itself: it has to be made by an order on labels or
  terms. Whenever composition creates such a pair, the word has to be
  laid out again, however far back the families go.
- **Equal terms.** Two parts of a word can be the same term with the
  same payload only because of what comes after both (`⟦ y := v;
  z := v ⟧` makes exchanging `y` and `z` before it invisible). So what
  is written early in a word is in normal form only relative to the
  rest, and a composition on the right can change that.

So there are three things the layered form could be:

1. *The normal form, with a global rule* (the prototype's, or another
   that fixes the choices above). Composition is concatenation and the
   seam when no choice arises, and a new layout when one does. The
   predicate, uniqueness and the operations are new: most of
   `Normalise.v`, `Normal.v`, `Unique.v`, `Complete.v` and `Shared.v`.
2. *A representation that is sound but not unique*: layered words kept
   reduced by the local laws above, with soundness proved. The decision
   compares the reduced words and, when they differ, falls back on the
   stored form. The normal form and theorems 1–4 stay as they are; the
   speed is there when both sides reduce to the same word, which the
   laws above cover, and not otherwise.
3. *What `names` shows*: the stored form stays the normal form and what
   everything is computed with, and the layered form (this prototype,
   a function of the stored form and so the same for equal adjustments)
   is how a large normal form is displayed, instead of leaving the
   adjustment as written.

The first is the one being built. The order of the terms is the global
choice, and the rule for it has to survive composition:

- *The order.* The word is built from its end. Among the terms all of
  whose mentioned terms are placed, the next placed is the one whose
  most recently placed mentioned term is the most recent; ties go by
  the term (`layers_k true` in the prototype). A term nobody mentions
  cannot change the choice between two others, so composing on the left
  never reorders the terms of the right-hand word: in 700 random
  compositions they stayed in order, and all but one time at the end of
  the word (postorder reordered them 4 times). A new term goes
  directly before the first term it mentions; usually that is the
  first term of the word.
- With this order, writing two words side by side and composing at the
  seam gives the canonical form for 92 percent of random pairs. The
  rest involve atoms under lifts.
- The normaliser needs one operation on layered words: putting one
  step in front of a word. It folds over the expression from its last
  step, whatever the nesting.

`Core/Layered.v` is this normaliser, built with its proofs. So far:

- A layered word is a list of segments and atoms; its meaning is their
  composition, so a term in a segment has the rest of the word after
  its payload.
- A lift is a close before and an open after, with the steps between
  one level deeper under the bound label (`lift_close_open`).
- A term whose payload goes on with further steps is put in front of
  those steps, which stay in the word, and everything else goes around
  them: an input entry is undone by a weakening before it, and the
  variable an output entry creates is carried past it as a bound
  variable (`bypass_step`).
- `lnorm_sound`: the layered word of an expression means what the
  expression means. Not covered: an atom, or a lift by the bound
  label, inside a payload (the fold then has no word).

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

### Where `names` uses it

`names_eq` computes the layered words of the two sides and compares
them (`nf_eq_l`, sound by `nf_eq_l_sound`). When they are the same the
equation is proved. When they differ, or the fold has no word for a
side, it decides on the stored form as before (`nf_eq_r`), which is
complete. So the decision is sound and complete, and the layered form
is its first attempt. Everything else (`names` showing a normal form,
applying an adjustment to a variable, materialising payloads) still
reads the stored form.

Of the 93 equations decided while building the tests and examples, 89
are proved by the layered words. The other four:

- Three are the laws that relate a substitution in a payload to the
  same substitution in the word, for example

      ⟦ x | ⟦ y := w ⟧ ⟧ ⨾ ⟦ x := u⟨ y := w ⟩ ⟧  =  ⟦ x := u ⟧ ⨾ ⟦ y := w ⟧

  The fold gives the two sides different words. On the left it writes
  `w` twice, once for the lifted substitution and once for the payload,
  where the form wants it once: the first `w` has the payload of the
  last layer and belongs there, and the bound variable that then
  carries `y` has the same result as `y` itself.
- One has labels whose order is not known
  (`⟦ z := w⟨ x := u; y := v ⟩ ⟧` with `z` unrelated to `x` and `y`).
  The layered word puts the weakenings of `x` and `y` in the segment of
  `z`, which has to be sorted; the stored form keeps the payload apart
  and never compares them. This is a property of the form, not of the
  fold.

### What is proved, and what is not

- Sound: `lnorm_sound`, `nf_eq_l_sound`.
- Unique: two words satisfying `lnf` that mean the same are the same
  (`lw_unique_real`, and `lw_unique_sz` with the order filled in).
- **Not proved, and not true of the fold as it is: that the word it
  returns satisfies `lnf`.** The three laws above are counterexamples.
  So uniqueness is a theorem about the form, and the fold is a sound
  way of computing a word that is often, not always, the normal one.

What the fold lacks is the same in every case found so far: deciding
that a term does not belong in a new first layer. A term `u` put in
front of a word `K` with a payload `p` other than the identity has the
payload `p ⨾ K`. The fold always opens a new layer for it, with `p`
written between that layer and `K`. The form wants `u` in the layer
whose rest means `p ⨾ K` on named variables, if there is one, and
otherwise in a new layer at the place the order gives. Finding that
layer means comparing what `p ⨾ K` and the rests of `K` do. When the
first segment of `K` sends a named variable to a term, the new layer
is above it and nothing needs comparing; this is the case of a chain.
When it does not, `p` and the renamings of `K` have to be followed
layer by layer until a named variable reaches a term or the word ends:

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
None of this is written. Until it is, and `lnf` is proved of the
result, the stored form cannot go.

### Cost

Measured with `vm_compute` on the reified expressions, both sides
normalised and compared; times in seconds. *Stored* is `nf_eq_r`,
*layered* is `nf_eq_l`.

| | steps | stored | layered |
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
| a law of the kind above, payload a chain | 128 | 0.17 | 0.16, words differ |

In the number `n` of steps:

- *Chains.* A step in front of a layered word is one new segment: the
  layered form is linear, in time and size. The stored form writes
  each payload once and is quadratic. With atoms the stored form
  carries every term past every atom and is far worse than quadratic;
  the layered form leaves terms where they are.
- *Wide segments.* Composing a segment into another looks up every
  target of the one in the other by walking its entries, and puts each
  entry back by walking again (`sgo`, `sfind`, `sset`). So composing
  costs the product of the two widths, and `n` weakenings of distinct
  names, which end in one segment of `n` entries, cost `n²` in both
  forms. A merge of the two sorted lists would be linear.
- *Lifts.* A step under `d` lifts is a segment with `d` bound
  variables sent to themselves. It was lifted once per lift, `d²` per
  step; it is now lifted in one pass (`slifts`), which made depth 128
  eight times faster. The `d` targets are still looked up one by one
  when the segment is composed into the first segment of the word,
  `d` times its width, so `n` nested lifts cost `n³`, where the stored
  form is quadratic: four times slower at depth 128, the same at depth
  8. Composing under the first `d` bound targets of the word's first
  segment, without writing them out, would make this quadratic too.
- *Where the fold is not canonical*, the layered attempt is wasted and
  the stored form decides: the cost of both.

In practice the normaliser is not where the time goes. For the laws in
the tests (two or three steps) `names_eq` takes 30 to 80 ms, of which
either normaliser is under 1 ms; the rest is unfolding the notation,
reifying, and the kernel. For a chain of `n` substitutions over label
variables with `n − 1` order hypotheses:

| `n` | `names_eq` | collecting the order hypotheses | reifying | the order table | layered | stored |
|---|---|---|---|---|---|---|
| 12 | 0.44 | 0.23 | 0.10 | 0.003 | 0.001 | 0.010 |
| 24 | 1.9 | 1.3 | 0.18 | 0.039 | 0.001 | 0.004 |
| 48 | 8.4 | 5.4 | 1.1 | 0.88 | 0.001 | 0.04 |

The last two columns are without the order table, which both need.

- `collect_fact_list` finds one hypothesis `label_lt x y` at a time and
  starts again from the first after each, reifying both labels by a
  search of the label list: more than quadratic in the number of
  hypotheses.
- `order_of` works out the order of every pair of label variables by
  following the facts from scratch for each pair; it grows fastest.
- Reification looks every label and term up in a list.

So for goals as they occur, the two normalisers cannot be told apart,
and for large goals over label variables the tactic's own bookkeeping
costs a thousand times more than either. The layered form matters for
long compositions over concrete labels and, most of all, for anything
with atoms between substitutions, where the stored form stops being
usable at a few dozen steps.

`names` itself (as opposed to `names_eq`) normalises each adjustment
on the stored form to show it, and then proves the two equal with
`names_eq`; it gains only in that second step.

Still to do, in the order it would pay off:

- The fold canonical as described above, `lnf` of its result, and then
  showing, applying and materialising from layered words, so that the
  stored form goes.
- Composition under bound targets and a linear merge of segments.
- `collect_fact_list` in one pass, and the order table by one closure.
- `ord_sz` puts layers of two families that do not see each other in
  size order, which interleaves them; an order that keeps a family
  together would give smaller words and fits the same construction.
