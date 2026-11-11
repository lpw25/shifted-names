# Normal forms of adjustments

Composition is written `⨾`, in diagrammatic order: `a ⨾ b` is `a`, then
`b`, so `t [a] [b] = t [a ⨾ b]`.

## Status

Theorems 1–4 below are proved, and the display (step 9) shows terms
before the atoms they were carried past. What remains is listed at the
end of the plan.

- Theorem 1: `anorm_normal` (`Core/Normal.v`).
- Theorem 2: `nf_unique` in the free model, with `free_to_real` and
  `adequacy` (`Core/Unique.v`).
- Theorem 3: `complete` (`Core/Complete.v`).
- Theorem 4: `wtrace_sound` (`Core/Normalise.v`) and `eval_stuck`
  (`Core/Complete.v`).

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

## Sharing (open)

### The blow-up

Condition 2 puts every term in the last segment, with a payload holding
everything that happens to its names afterwards. In a chain of
substitutions

    ⟦ x₁ := u₁ ⟧ ⨾ ⟦ x₂ := u₂ ⟧ ⨾ … ⨾ ⟦ xₙ := uₙ ⟧

`u₁`'s payload is the normal form of the rest of the chain, which holds
`u₂` with its own payload, and so on: the normal form has size about
`2ⁿ`, although the expression has size `n`. Normalising five steps takes
seconds and six takes minutes. The expression shares each later step
among all the earlier terms; the normal form copies it into each.

### Where a term can sit

A term `u` reached by an input could be placed at any segment along that
input's path, not only the last. Placed at segment `i`, with the rest of
the word after it `Rᵢ`, its payload `ρ` must satisfy `ρ ⨾ Rᵢ = k`, where
`k` is what happens to `u`'s names overall (in the free model, the
continuation of its result). The last segment always works (`R = id`,
`ρ = k`); that is the current choice. Sharing wants terms placed early,
with payloads that leave to the rest of the word whatever it would do
anyway. That leaves three choices, each of which the normal form must
make canonically.

### Choice 1: the payload at a given position

When the rest merges variables, several payloads give the same result.
With `R = ⟦ y as a; z as a \ z as a ⟧`, which sends `y₀` and `z₀` to
`z₀`, shifts the other `y`s down and leaves the other `z`s alone:

    ⟦ x := u⟨ z as a; y as a \ y as a; z as _ ⟩ ⟧ ⨾ R  =  ⟦ x := u ⟧ ⨾ R

The payload sends `z₀` to `y₀` and leaves everything else alone; after
`R` that is the same as doing nothing. A payload is determined only up
to the classes of results that the rest sends to the same place.

### Choice 2: a variable or a term

A class can contain both a variable and a term:

    ⟦ x as a \ w as a ⟧ ⨾ ⟦ w := u ⟧  =  ⟦ x := u⟨ \ w ⟩ \ w as _ ⟧ ⨾ ⟦ w := u ⟧  =  ⟦ x := u ⟧

On the left `x₀` is renamed to `w₀`, which the second step substitutes;
in the middle `x₀` is substituted directly, with a payload that adds a
`w` the second step then removes. A rule that prefers leaving work to
the rest of the word picks the left, and composing its two segments
gives `⟦ x := u ⟧`.

### Choice 3: the position

"As early as possible" is not well defined. In

    ⟦ x₁ := u₁ ⟧ ⨾ ⟦ x₂ := u₂ ⟧  =  ⟦ x₂ := u₂⟨ \ x₁ ⟩ ⟧ ⨾ ⟦ x₁ := u₁⟨ x₂ := u₂ ⟩ ⟧

`u₂` can sit first if its payload adds an `x₁` for the second step to
remove, but then `u₁`'s payload holds `u₂` again. And a term can sit at
two positions with the same payload: in `⟦ x := u ⟧ ⨾ ⟦ · := v ⟧` the
second step only touches the bound label, which a payload (applied to
named variables) never sees, so `u` can sit before it or after it.

### A candidate rule

1. Write each term as few times as possible: among the forms equal to
   the expression, take those whose payloads contain the fewest terms
   in total. In the chain each `uᵢ` is then written once, with the
   identity payload, before the step `⟦ xᵢ₊₁ := uᵢ₊₁ ⟧`.
2. Among those, put each term as late as possible. This settles the
   ties of choice 3 (`u` after `⟦ · := v ⟧`) and, when no later step
   acts on a term's names, gives the current form.
3. Within a class of choice 1 or 2, prefer leaving the term's variable
   alone; otherwise a variable over a term; otherwise the first variable
   in label then index order. For a term, apply the rule to its payload
   relative to what follows it.
4. Segment boundaries follow: two adjacent segments are composed unless
   that would copy a term of the later one into a payload of the
   earlier one.

The rule depends only on what the expression means, which is what
canonicity needs, and everything it compares can be decided on normal
forms. Evaluation decides where the rest of the word sends a variable,
and theorem 4 says it decides that exactly.

### What is open

- Whether the minimiser of rule 1 is unique once rules 2–3 are applied,
  or only after further tie-breaks, and how to compute it without
  searching. A natural candidate is to place each term just before the
  first later step that substitutes a term into its names. Neither is
  proved.
- Terms then sit in any segment. Condition 2 is replaced, condition 3
  (lift position) must route inputs to terms in the middle of the word,
  and the uniqueness proof's induction (peeling the first atom) must
  also peel term substitutions. In the free model they are like atoms
  that act on a single variable.
- Payload words then contain fewer terms, but the merging classes of
  rule 3 depend on the rest of the word, so payloads are normal only
  relative to their position. Theorem 1 must carry that context.

### The alternative: sharing in the computation

The current normal form can be kept, with its theorems, and computed
with sharing instead: in the chain, `u₁`'s payload is literally the
normal form of the rest, which also occurs in the word itself. Words
stored as graphs with shared nodes, normalisation memoised on its
subproblems, and equality decided by comparison memoised on pairs of
nodes would keep the chain polynomial (about `n²` distinct nodes). This
is engineering, plus a proof that the memo tables agree with the
functions they cache, but no new mathematics. Display would still need
the sharing-aware rendering of the previous section to show the result
compactly.
