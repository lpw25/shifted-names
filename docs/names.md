# `names`: its steps, what could be simpler, and how complete it is

This note covers three things:
- the steps the `names` tactic takes now;
- what could be simplified;
- what can be said about its completeness.

The design summary in `docs/design.md` covers the same pipeline more
briefly. The benchmark figures are in the last section.

## Vocabulary

**Adjustment.** An adjustment `a : adj T N M` sends each variable of
scope `N` to a *result*. A result is either:
- a variable of scope `M`; or
- a term `u : T K` together with a *payload* `ρ : adj T K M`, meaning
  "`u`, substituted by `ρ`".

The notation `x := u⟨| ρ ⟩` writes such an entry, and `x := u` is the
case where `ρ` is the identity.

**Normal form.** The normaliser (`HNorm`) represents an adjustment as a
*word*: a list of steps, each an entry, a weakening or an atom. Every
entry's payload is itself a word. Words are hash-consed in a state, so a
payload that occurs many times is stored once.

**Display.** The display (`HDisplay`) writes a word back as an expression
over context forms, `⨾` and shared definitions (`share r := … in`). It
has two ways to show entries:
- **One cell at a time.** An entry is shown over the rest of the word,
  with its payload visible: `⟦ x := u⟨| p ⟩ | rest ⟧`.
- **A run.** A run of entries whose payload is exactly the rest of the
  word after the run is shown as a composition, with no payloads visible:
  `⟦ x1 := u1; …; xk := uk ⟧ ⨾ rest`.

A cell that is referred to more than once is shown once, as a shared
definition.

## The steps

`names` makes one pass over the goal. Each step runs once, over the whole
goal, and its output needs nothing from the steps before it.

0. **The user's `cbn`.** This is not part of `names`. Substitution is the
   Kleisli extension of the library's `apply`, so `cbn` pushes it through
   the syntax's constructors, and `names` knows nothing about them.
1. **`names_pre`.** This rewrites with the monad laws a syntax's `Subst`
   functor adds:
   - **Going under a binder lifts the adjustment.** This puts what `cbn`
     leaves under a binder, a Kleisli extension at a shifted extension,
     back in the form `t [lift a]`.
   - **A substitution applied to a substitution fuses:** `t [a] [b] = t
     [a ⨾ b]`.

   The rewrites are plain `autorewrite`, with no setoid rewriting.
2. **`names_node`.** A substitution `t [a]` becomes the node `csubst L a
   t`, which carries the syntax's law `L` (`Names.SubstLaw`). What `cbn`
   leaves of a substitution into a variable becomes the node `csubst L a
   (tvar v)`.
3. **Normalise** (`names_norm`). This covers every node that is not inside
   an adjustment, and every other adjustment that is not inside one.
   Nodes on variables go first, one at a time. A shared adjustment is
   handled once. For each node `csubst L a t`:
   1. **Reify** `a` syntactically, with no reduction. Labels,
      adjustments and terms become atoms, and `share` definitions are
      kept. Terms are read with their scope. Order facts `label_lt x y`
      come from the context.
   2. **Convert** (`Conv.aconvn`). This acts on the terms *inside* `a`,
      the values of its entries:
      - a term that is a substitution, `x := u [c]`, becomes `u` with `c`
        in its payload;
      - a term that is a variable, `x := tvar w`, becomes a look-up of
        `w` through its payload.

      This goes all the way down: the terms of each `c` are converted
      too.
   3. **If `t` is a variable `v`**, normalise the converted expression and
      follow it from `v` once (`HNorm.follow`, through
      `HShow.hlook_show`). There are three outcomes:
      - a variable `w`, so the node becomes `tvar w`;
      - a term `u` with a payload `b`, so it becomes `csubst L b u`;
      - `w` looked up through the rest `b` of the word, say an atom, so
        it becomes `csubst L b (tvar w)`.

      The rewrite is the law's `sl_res`.
   4. **Otherwise**, normalise and display. The rewrite is the law's
      `sl_rel`, and it applies to the nodes with that adjustment only.

   An adjustment outside a node, such as one side of `a ⨾ b = c`, is
   reified, normalised and displayed the same way. It is not converted,
   because it has no law to justify that, and it is rewritten by equality
   (`adj_eq`).
4. **Materialise** (`names_mats`). Each term with a payload `u⟨| b ⟩` in a
   node's adjustment becomes the term `csubst L b u` with the identity
   payload (`sl_rel` again). Then the same happens in the nodes this
   makes.
5. **`names_apply`.** This handles `apply_var a v` left in the goal, for
   an adjustment of any family, with no law. It uses the same
   `hlook_show` as step 3.3.
6. **`names_post`.** The nodes go back to `t [a]`, and `t [⟦⟧] = t`.

**Why steps 1 and 3 both handle nested substitutions.** They handle
substitutions in different positions:
- **Step 1** handles a substitution applied to the *result* of another:
  `t [a] [b]`, the node's own term being a node.
- **Step 3.2** handles substitutions used as *values inside* an
  adjustment, as in `⟦ x := u [c] ⟧`.

Without step 1, `t [a] [b]` would stay as two nodes, each normalised on
its own, and `t [a] [b] = t [a ⨾ b]` would not be decided. Step 3 could
do the fusion instead, but that would need the composition law in
`SubstLaw`, and step 1 is needed anyway for the lifting rewrite. The two
are the same law, at the node and at a single variable:
- the per-variable form of `t [a] [b] = t [a ⨾ b]` is `nbase`, which says
  `u [c]` with payload `W` is `u` with payload `W ∘ c`;
- step 3.2 applies `nbase` with `W` the entry's payload.

**What the kernel checks.** Each rewrite's proof is built directly, as a
term:
- The normaliser's and display's results are checked by `vm_compute`
  casts.
- The reified expressions are checked against the goal by conversion.
  Their environments are Braun trees, so each lookup is logarithmic.
- Shared definitions are bound once (`chain_intro`).

### Why one pass is enough

- After step 3, no normalised adjustment has a term that is a
  substitution or a variable.
- A node on a variable becomes one of three things:
  - a variable;
  - a node whose term is neither a variable nor a substitution, and whose
    adjustment is part of a normal form;
  - a stuck node `csubst L b (tvar w)`, whose adjustment is part of a
    normal form and stops the look-up of `w` at once.
- The payloads of a normal form are themselves normal forms. So step 4
  makes only nodes that step 3 would leave unchanged.

Running `names` twice changes nothing in `Examples/Lambda.v`,
`Examples/STLC.v`, `Tests/NamesTests.v` and the stuck-lookup tests. This
was checked by running each file with a second `names` that fails on any
change. It is not proved.

## What could be simpler

### 1. Materialise what the display shows, in step 3

**What step 4 does now.** For a node, `mat_one` takes these steps:
1. Reify the node's adjustment, already in normal form after step 3.
2. Normalise it again.
3. Find the first entry of the *word* with a payload that is not the
   identity.
4. Display that payload on its own (`hmat_target`), and the rest with the
   entry's term replaced by a new term (`hmat_display`).
5. Render both, and rewrite.

It repeats this per payload, then recurses into the new nodes.

**What goes wrong.** Two things, both artefacts of doing this one
payload at a time on the word:
- **It materialises payloads the user never saw.** The normal form of
  `⟦x1 := f1⟧ ⨾ … ⨾ ⟦xn := fn⟧` gives entry `i` the payload "the
  substitutions after `i`". Every entry has a payload, but the display
  shows the word as a run, the composition itself, with none visible.
  Step 3 leaves the goal unchanged here. Step 4 still finds the payload
  of `x1` and writes it out as a term `f1 [⟦ x2 := … ⟧ …]`, which turns
  the compact composition into a context form with explicit terms.
- **It loses sharing.** The payload is displayed on its own, with fresh
  shared definitions. Once it is inside the term `f1 […]`, it is opaque
  to the normaliser. So the entries `x2, x3, …`, whose payloads are the
  same suffixes, each get their own copy, and the recursion into the new
  nodes materialises every copy again. The output has 2ⁿ − 1 entries.

Neither is necessary. The normal form shares every suffix, and the
display already writes it in linear size.

**The proposal.** Materialise after displaying, on the shown expression:
1. Every shown entry `x := u⟨| p ⟩` becomes `x := u [p]`.
2. The entries inside `p`, and inside the shared definitions, are
   materialised the same way.
3. A shared definition stays a shared definition, so `p = r`, a
   reference to one, becomes `u [r]`, with no copy.

This would happen in step 3, before rendering. The chain above has
nothing shown, so it stays exactly as written.

**Why no new law is needed.** The display shows a payload only on an
entry over the rest of the word, `AInner h (TBindE u p) rest`. Its other
forms are a run, an atom step or a weakening, composed *before* the
rest: `rcompose rest X`, where `X` is the run, atom or weakening. Since
`rapply (rcompose a b) v` applies `b` first, nothing is ever applied
after such an entry. So that variable's result is exactly `(u, p)`, and
materialising it is the existing base `matbase`: `u` with payload `p`
against `u [p]` with the identity. That holds:
- at the top of the expression;
- in a shared definition;
- inside a payload, where it is the same statement one level down
  (`DPay`).

**What it removes.** `mat_one`, `names_mats`, `HShow.hmat_target` /
`hmat_display` and the word-level proofs (`paid_matw`, `hmat_show_sound`,
`mat_bridge`): about 250 lines. A node then needs one reification and one
rewrite instead of one per payload.

### 2. One route for proving a normalisation

There are two ways a normalised adjustment is rewritten into the goal:
- **Inside a node** `csubst L a t`, by `sl_rel`. Its premise is a
  relation between `a` and its normal form, variable by variable, after
  conversion.
- **Elsewhere** (an adjustment equation, or an adjustment under an opaque
  function), by `adj_eq`. Its premise is plain equality of the two
  adjustments' raw representations.

Both call the same normaliser and display, but the proof plumbing is
duplicated: the lambda that assembles the soundness proof, the facts for
shared definitions and atoms, and the `share` chain. That is about 40
lines each in `conv_one` and `show_adj_with`. The second route could be
the first with no conversion and equality as the relation. This is a
tidy-up only.

### 3. `names_apply`

**What it is.** `names_apply` handles goals that mention `apply_var a v`
directly, for example in `Tests/NamesTests.v`:

```coq
apply_var (⟦ · \ x ⟧ : adj T (S N) N) bvar0 = Rename x
```

There, `T` is any family of terms with no substitution and no law.
Without a law there are no nodes, so this cannot go through step 3.

**What could change.** Its code repeats step 3.3's read-back and proof
assembly for the variable and term outcomes, about 50 lines. Two
options:
- share the read-back with step 3.3, parametrised by the final lemma;
- drop `apply_var` goals from `names`, since nothing outside the tests
  needs them.

### Smaller points

- **The law.** `SubstLaw` has three fields: `sl_var`, `sl_rel` and
  `sl_res`. `sl_rel` follows from `sl_res` given extensionality of
  substitution in the variables. That trades one field for another.
- **Ltac2 hygiene.** `Control.plus` leaves choice points: a later
  failure re-runs everything after every earlier `plus`, which is
  exponential. All uses are now `attempt`, built on `Control.case`, which
  leaves none. Any new code should use `attempt` too.

## Completeness

Completeness can be argued at three levels. Only the first is
mechanised.

### 1. Adjustments (mechanised)

For adjustment expressions built from context forms, `⨾`, `⟦⟧` and
atoms, the normaliser decides equality in every comprehension model
consistent with the order facts. This is `HRefine.hn_eq_order_correct`,
from `CSound.cn_sound` and `CComplete.cn_complete`; the term model is the
normaliser's own words.

The display is a function of the normal word. So when two sides of `a =
b` are equal in all such models, they have the same normal word and the
same display, and `names; reflexivity` closes the goal.

### 2. Substitutions on opaque terms (argued)

**The fragment.** Terms built from opaque term atoms `u : T K` (each with
its scope), literal variables, and substitution `t [a]`, with
adjustments as in level 1.

**The claim.** For two nodes on the same atom or on literal variables,
the outputs of `names` are syntactically equal exactly when the two sides
are equal in the free substitution algebra over the atoms. Being initial,
that algebra validates exactly the equations that hold in every syntax.

**The argument.**
- In the free algebra, a term is either a variable or an atom with a
  payload. A substitution into a term composes payloads; that is the
  base `nbase`. A substitution into a variable is the look-up; that is
  `vbase` and `sl_var`.
- So `u [a] = u [b]` holds exactly when `a` and `b` agree on each
  variable of `u`'s scope, with results compared hereditarily: a variable
  as a variable, an atom with a payload as the atom with an equal
  payload.
- Conversion (step 3.2) is the rewriting to that form. Payloads are
  adjustments, so "equal payloads" is level 1 again, applied
  hereditarily. The normaliser's words represent payloads by their own
  normal words, so the comparison is a comparison of words.
- For a node on a variable, `follow` computes the hereditary result
  itself: a variable, an atom with its normal payload, or a look-up
  stuck at an atom with the normal rest.
- Materialisation and display are functions of the word. Equal words
  give syntactically equal outputs, and unequal words differ in some
  model by level 1.

**What is missing for a proof.** A lemma that the free substitution
algebra and the converted comprehension term model agree. Roughly: the
conversion, `lawbase` and the three node rewrites give exactly the free
algebra's equations. The term model in `CComplete` is already the
explicit-substitution syntax in normal form, so this looks like one
induction on words. It is not done.

### 3. What is not covered, and why

- **Equations that need a case split on labels.**
  - *Example.* `⟦ x; y | a ⟧ = ⟦ y; x | a ⟧`, lifting `a` past a
    binder for `x` and one for `y`, in either order
    (`NamesTests.lift_free_comm_cases`). It holds for all `x` and `y`:
    - if `x = y`, the two sides are the same;
    - if not, lifts on different labels commute.

    But no single normal form covers both cases.
  - *Why.* The normaliser's models (comprehension models) allow two
    labels with no order fact between them to be unrelated, so steps on
    them do not commute. Concrete labels are always equal or ordered, so
    the equation holds in every concrete model but not in every
    comprehension model.
  - *Workaround.* The user case-splits with `label_compare_spec x y`,
    which adds `x = y`, `label_lt x y` or `label_lt y x` to the context,
    and `names` then decides each case. (Many equations that look as if
    they need this do not. For example, `t [⟦ x \ y ⟧] [⟦ y \ x ⟧] = t`
    and opening a binder as `y` and then renaming `y` to `x` both go
    through without a split, and `STLC.v` no longer case-splits.)
  - *Possible fix.* Do the case split inside `names`. That is at most
    three cases per pair of unordered labels that matter, so exponential
    in the number of such pairs.
- **Variables that are not written out.**
  - *Example.* `(tvar v) [⟦ x := u ⟧]` for `v : var N` a variable of the
    context. The result depends on whether `v` is `x`, which is not
    known.
  - *What happens.* The node is treated like a node on an opaque term:
    its adjustment is normalised, but the node is not evaluated. So
    `(tvar v) [a] = (tvar v) [b]` is decided when `a` and `b` have the
    same normal form. It is not decided when they agree only on the one
    variable `v`.
- **Substitutions under a binder that uses the bound variable.**
  - *Example.* `map (fun z => t [⟦ x := tvar z ⟧]) l`. The node
    `t [⟦ x := tvar z ⟧]` mentions the bound `z`.
  - *Why.* A rewrite cannot abstract a subterm that mentions a bound
    variable, so `names` only takes closed nodes. A node under a binder
    that does not mention the binder is fine.
  - *Possible fix.* Normalise under the binder by generalising over its
    variable, as `setoid_rewrite` does, but that is setoid rewriting.
- **Atoms equal only up to computation.**
  - *Example.* An atom `f (1 + 1)` against `f 2`.
  - *Why.* Atoms are compared syntactically: no reduction happens when
    reifying. So these two are different atoms, and an equation that
    needs them equal is not decided.
  - *Workaround.* The user normalises those subterms first.

## Benchmarks

The families below run on the current branch ("new") and on the commit
before the single-pass work (20ed942, "old").
`tests/bench/names/run.sh FAMILY N…` runs them. The goals have the form
`P (…) -> True`, so `names` has one rewrite to make. Times are tactic
time + `Qed`. A dash means not measured. "Rewrite by type" is the figure
before the variable-path fix described under "Problems found".

| family | n | new | old |
|---|---|---|---|
| D: chain of n singletons, adjustment only | 100 | 0.19 + 0.20 s | 0.44 + 0.12 s |
| | 1000 | 4.0 + 1.9 s | 4.5 + 2.4 s |
| PC: chain of n pairs | 50 | 1.1 + 1.0 s | 1.4 + 1.1 s |
| VR: a variable through n renamings | 300 | 1.6 + 0.23 s | 2.4 + 0.34 s |
| VT: a variable through n `x := tvar y` | 10 | 0.16 + 0.04 s | 35 s |
| | 100 | 0.78 + 0.57 s | — |
| | 300 | 2.5 + 3.0 s (rewrite by type: 18.5 s) | — |
| VA: as VT, ending in an atom (a stuck look-up) | 300 | 2.4 + 3.4 s | n = 5: 1.7 s |
| NS: substitutions nested n deep in a payload | 10 | 0.59 + 0.70 s | 2.8 + 2.0 s |
| | 30 | 3.4 + 5.1 s | — |
| SN: n nested substitutions on an opaque term | 3 / 5 / 7 | 0.25 / 0.87 / 3.1 s | n = 4: > 100 s |
| MO: n opaque subterms under one n-entry substitution | 3 / 5 / 7 | 0.47 / 3.1 / 23 s | 1.1 s / > 150 s |
| MV: n variables under one n-entry substitution | 3 / 5 / 7 | 0.35 / 1.0 / 4.0 s | 0.63 s / > 150 s |

Earlier recorded baselines were D100 at 0.46 + 0.35 s, D300 at 1.5 +
1.1 s and D1000 at 6.5 + 4.6 s.

**Problems found.**
- **Exponential backtracking (fixed).** `Control.plus` leaves a choice
  point, so a failure after it re-ran the code that followed every
  earlier `plus`, including the reifier's. This is what made the old
  version's VT and MO figures explode. All uses are now `attempt`, built
  on `Control.case`.
- **The type of a large proof (fixed).** The rewrite for a node on a
  variable took the type of its whole proof term. `Constr.type`
  type-checks it, which cost 6–7 s at VT 200. The proof is now asserted
  without a check and rewritten from the hypothesis, as the other
  rewrites already were (`rewrite_by`).
- **Exponential materialisation (not fixed).** This is behind SN, MO and
  MV. See "What could be simpler", section 1.
- **Superlinear deep nesting (not fixed).** NS is about n² on the tactic
  side and worse on `Qed`. On the tactic side, the term table compares a
  new term against the existing ones one at a time, by full syntactic
  comparison (`tbl_add`). Each nested substitution's whole term, all the
  levels below it, is entered as a term, so the comparisons add up to
  about n². Two ways to avoid this:
  - key the table so a lookup is not a scan;
  - do not enter a nested node's whole term: conversion needs only its
    base term and its reified adjustment, plus one fact tying the
    entry's term to them.

  I have not yet located the `Qed` cost. Conversion is linear in
  principle, so this is an artefact to be fixed, not a limit.
