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

   The rewrites are plain `autorewrite`, with no setoid rewriting.
2. **`names_node`.** A substitution `t [a]` becomes the node `csubst L a
   t`, which carries the syntax's law `L` (`Names.SubstLaw`). What `cbn`
   leaves of a substitution into a variable becomes the node `csubst L a
   (tvar v)`.
3. **Normalise** (`names_norm`). This covers every node that is not inside
   an adjustment, and every other adjustment that is not inside one.
   Nodes on variables go first. A shared adjustment is handled once.

   First, each chain of nodes `t [a₁] … [aₙ]` fuses into one node
   `t [a₁ ⨾ … ⨾ aₙ]`, with one application of `fch_fuse` per chain (the
   chain is data, `fchain`; the law's `sl_comp` proves the fusion).

   Each rewrite below is collected rather than made at once. At the end
   they are made together (`rewrite_many`): one traversal abstracts the
   goal over every occurrence, and one term `Q` gives the old goal from
   the new by an `eq_ind_r` per equation, with motives that mention
   only variables. A node inside another's term is rewritten in a
   further round. Before this, each rewrite traversed the goal and
   type-checked a motive the size of the goal.

   For each node `csubst L a t`:
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
      A node whose adjustment shows as the identity becomes its term
      (`sl_id`).
   5. **Materialise while rendering.** Each entry the display shows with
      a payload, `x := u⟨| r ⟩`, is rendered as `x := u [r]`, in the
      syntax's own substitution, in the shared definitions and payloads
      too; a shared definition stays one. The results of 3.3 are rendered
      the same way. See "What could be simpler", section 1.

   An adjustment outside a node, such as one side of `a ⨾ b = c`, is
   reified, normalised and displayed the same way. It is not converted
   or materialised, because it has no law to justify that, and it is
   rewritten by equality (`adj_eq`).
4. **`names_apply`.** This handles `apply_var a v` left in the goal, for
   an adjustment of any family, with no law. It uses the same
   `hlook_show` as step 3.3.
5. **`names_post`.** The nodes go back to `t [a]`. This needs no lemma:
   `csubst L a t` is the law's `sub` at `a t` by conversion. It is
   Ltac2's `change` with the pattern of a node, each match replaced by
   the body of `sub` (read once, by unfolding the constant `sub` on its
   own) at the match's `N M a t`; `change` finds the matches and checks
   the conversion itself. What step 3 rewrites to it already builds this
   way. A
   materialised term under a shared definition's binder is in the
   syntax's form too; step 3 reads it back as a node (`as_node`), so a
   second `names` sees the same goal.

**Nested substitutions, in two positions.** Step 3 handles both:
- a substitution applied to the *result* of another, `t [a] [b]`, the
  node's own term being a node, is fused first (`fch_fuse`, from the
  law's `sl_comp`);
- substitutions used as *values inside* an adjustment, as in
  `⟦ x := u [c] ⟧`, are converted (3.2).

Fusing used to be a rewrite in step 1 (`subst_compose`), one
`autorewrite` step per node, each traversing the goal: quadratic on a
chain. The two are the same law, at the node and at a single variable:
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
- Materialisation adds one theorem application per shared definition and
  one for the root (see below).
- The checks the VM makes are stated with the number of terms and atoms
  as numerals, not as `List.length` of the term table: otherwise the VM
  compiles every term in the table to count them.

**Keeping the proofs cheap to build and check.** Three rules, each found
by measuring (below):
- *No data in quotations.* Each proof's skeleton is a closed definition
  (`g_adj_mat`, `g_var_term`, …), elaborated and checked once when the
  library compiles, and applied to its data with `app`. Only its head is
  elaborated, with the syntax's type, which records the universe
  constraints. As Ltac2 quotations with the data antiquoted, the
  elaborator walked the term table and the facts as trees at every use.
- *Every large term written once.* The kernel types each argument of an
  application, with no memory of terms it has typed. The conversion
  facts are one lemma application each (`nf_cons`, `vf_cons`), and the
  term table, the labels and every tail of the facts' list are bound once
  by `let`s around them (`with_tails`); passed to each fact, the table
  was typed once per fact.
- *Types that match syntactically.* The kernel first compares a proof's
  type with the expected one syntactically, sharing included. If that
  fails it reduces, and its fast comparison of two closures walks them
  whole, with no shortcut for shared subterms. So statements about the
  facts use one named predicate (`nfactP`, `vfactP`), and each fact is a
  cons step (`nf_cons`) whose type is a literal instance, not `P x` for a
  predicate `P` (as `Forall_cons` would have it), which the kernel would
  reduce, walking the term table once per fact.

### Why one pass is enough

- After step 3, no normalised adjustment has a term that is a
  substitution or a variable.
- A node on a variable becomes one of three things:
  - a variable;
  - a node whose term is neither a variable nor a substitution, and whose
    adjustment is part of a normal form;
  - a stuck node `csubst L b (tvar w)`, whose adjustment is part of a
    normal form and stops the look-up of `w` at once.
- The payloads of a normal form are themselves normal forms. So
  materialising makes only nodes that step 3 would leave unchanged.

Running `names` twice changes nothing in `Examples/Lambda.v`,
`Examples/STLC.v`, `Tests/NamesTests.v` and the stuck-lookup tests. This
was checked by running each file with a second `names` that fails on any
change. It is not proved.

## What could be simpler

### 1. Materialising while displaying (done)

**What it is.** The renderer, which turns the displayed expression into
a Gallina term, can also produce it as *data*: `MatShow.madj`, a mirror
of the context forms, with a case for anything left as it is (an atom, a
shared variable). The data has two meanings:
- `mden`, the adjustment as shown, with `x := u⟨| r ⟩`;
- `mmat`, the same with each such entry as `x := u [r]` (the law's
  `sub`), except where something is applied after it: the side of `⨾`
  applied first, the tail of a context form with outputs, and a short
  form with a lift.

One theorem, proved once, relates the two meanings variable by variable
(`MatShow.mat_rel`). The goal gets the second meaning, built by Ltac2
(`dconv`, which writes `u [r]` in the syntax's own form). The proof
applies the theorem once to the root and once to each shared definition
(`def_rel`). The kernel checks each application by computing the two
meanings of the data.

The shared variables in the output stand for the *materialised*
definitions, while the display's proof needs each to equal its *shown*
definition. So `show_rel` (and `term_rel`, `look_rel` for nodes on
variables) accept shared variables that are only related to the shown
definitions. Their proofs build the shown definitions' values themselves
(`olds`), so those values never appear in a proof `names` makes. This
needs shared variables only where nothing is applied after them, and
each definition to use only the ones before it; `safeN` checks both, by
the VM. When it fails, the node is shown with its payloads.

Per node, the proof is the display's proof as before, with the shared
definitions bound once, plus one application of `mat_rel` per shared
definition and one for the root.

**What went wrong first.** Three earlier versions proved
materialisation piece by piece, and each was superlinear for the reasons
Gross et al. give for proof-producing rewriting (*Accelerating
Verified-Compiler Development with a Verified Rewriting Engine*,
appendix A):
- A post-pass with one lemma per constructor and per shared level. Each
  lemma took its subterms explicitly, so the proof restated the old and
  new adjustments about eleven times (their A.2 and A.3).
- Materialising in step 3 against the raw denotation `aedenB`. A raw
  adjustment cannot express `u [r]`, because `sub` needs a scoped
  adjustment, so each materialised term had to be a new entry in the
  term environment with its own fact. Sharing those by `let` made
  checking quadratic: the kernel substitutes into a `let` body's type once
  per `let` (their A.4).
- On the Ltac2 side, per-entry tables searched as lists, and `closenl`
  once per shared level.

The standard design, which this follows, keeps the denotation in the
domain where the transformation is a theorem, and makes each use one
theorem application checked by computation and conversion.

**Measured.** Tactic time + `Qed`, with and without materialising, on
the same code:

| family | n | materialising | not |
|---|---|---|---|
| PN (nested shared definitions) | 30 | 1.2 + 0.7 s | 1.1 + 0.6 s |
| | 60 | 3.6 + 1.7 s | 3.2 + 1.4 s |
| SN | 100 | 2.9 + 1.0 s | 2.7 + 1.0 s |
| NS | 30 | 1.4 + 1.1 s | 1.1 + 1.4 s |
| VA | 300 | 3.1 + 2.8 s | 2.3 + 3.6 s |

The earlier versions took 9.5 + 4.5 s (post-pass) and 22.7 + 15.2 s
(step 3 against the raw denotation) on PN 60.

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

The families below run on the current branch ("now"), on 86e4e1f
(before step 3 rewrote all nodes at once, step 5 became a conversion and
the proofs were built by the rules above) and on the commit before the
single-pass work (20ed942, "old").
`tests/bench/names/run.sh FAMILY N…` runs them. The goals have the form
`P (…) -> True`, so `names` has one rewrite to make. Times are tactic
time + `Qed`; for MO and MV, `cbn` comes first and is not counted. A dash
means not measured. "Rewrite by type" is the figure before the
variable-path fix described under "Problems found". Timings on this
machine vary by about 10% between runs.

| family | n | now | 86e4e1f | old |
|---|---|---|---|---|
| D: chain of n singletons, adjustment only | 100 | 0.18 + 0.16 s | 0.19 + 0.17 s | 0.44 + 0.12 s |
| | 1000 | 3.0 + 1.3 s | 3.3 + 1.7 s | 4.5 + 2.4 s |
| PC: chain of n pairs | 50 | 0.94 + 0.84 s | 0.98 + 0.94 s | 1.4 + 1.1 s |
| PN: an opaque term under a chain of n pairs | 30 | 0.65 + 0.40 s | 1.2 + 0.74 s | — |
| | 60 | 2.0 + 1.5 s | 3.6 + 1.7 s | — |
| VR: a variable through n renamings | 300 | 1.2 + 0.15 s | 1.6 + 0.20 s | 2.4 + 0.34 s |
| VT: a variable through n `x := tvar y` | 10 | 0.14 + 0.01 s | 0.15 + 0.04 s | 35 s |
| | 100 | 0.57 + 0.10 s | 0.68 + 0.47 s | — |
| | 300 | 1.6 + 0.41 s | 2.1 + 2.7 s (rewrite by type: 18.5 s) | — |
| VA: as VT, ending in an atom (a stuck look-up) | 300 | 1.5 + 0.45 s | 3.1 + 2.8 s | n = 5: 1.7 s |
| NS: substitutions nested n deep in a payload | 10 | 0.18 + 0.04 s | 0.29 + 0.10 s | 2.8 + 2.0 s |
| | 30 | 0.40 + 0.36 s | 1.4 + 1.1 s | — |
| | 60 | 1.6 + 1.2 s | 4.6 + 5.4 s | — |
| SN: n nested substitutions on an opaque term | 30 / 100 | 0.34 + 0.09 / 3.2 + 0.82 s | 0.54 + 0.21 / 2.9 + 1.0 s | n = 4: > 100 s |
| MO: n opaque subterms under one n-entry substitution | 10 / 20 | 0.81 + 0.08 / 3.2 + 0.33 s | 1.4 + 0.20 / 8.0 + 1.1 s | n = 7: > 150 s |
| MV: n variables under one n-entry substitution | 10 / 20 | 0.64 + 0.13 / 3.6 + 0.47 s | 1.5 + 0.31 / 8.5 + 1.4 s | n = 7: > 150 s |

Most of SN, MO and MV is now step 2 (`names_node`, `autorewrite`): SN
100 2.8 of 3.2 s, MO 20 2.4 of 3.2 s, MV 20 2.5 of 3.6 s.

Earlier recorded baselines were D100 at 0.46 + 0.35 s, D300 at 1.5 +
1.1 s and D1000 at 6.5 + 4.6 s.

**Problems found.**
- **Ltac2 traversals of labels (fixed).** Labels are string literals,
  and they are most of a goal: PN 60's goal after step 3 is 191k nodes,
  140k of them `String`, `Ascii`, `bool`, `positive` and `nat`
  constructors. An Ltac2 traversal costs 5–15 µs a node, so every pass
  over the goal (finding nodes, abstracting occurrences, `names_post`)
  now skips literals (`is_lit`).
- **`autorewrite` per node (open).** Each step of `autorewrite` finds
  one instance, abstracts its occurrences and type-checks a motive the
  size of the goal: 50–100 ms a step on SN 200, MO 20 and MV 20. Step 3
  no longer rewrites this way (above), and step 5 no longer rewrites at
  all; step 2 (`names_node`) still does, and is now most of SN, MO and
  MV. Batching it needs the language's law without going through the
  hint database.
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
- **Exponential materialisation (fixed).** This was behind SN, MO and
  MV. See "What could be simpler", section 1.
- **The VM compiling the term table (fixed).** The display's checks
  were stated with `List.length` of the term table, so the VM compiled
  every term to count them. NS's table holds its nested terms, so this
  was quadratic: NS 30's `Qed` went from 4.6 s to 1.1 s once the checks
  were stated with the counts as numerals (the kernel relates the two by
  conversion, which only walks the list).
- **Superlinear per-node rewriting (fixed in steps 3 and 5).** MO and MV
  grew faster than their output (MO 10 → 20: 1.7 → 9.4 s): each node was
  rewritten separately, and each rewrite traversed the goal. Step 3 now
  rewrites all nodes together; what remains is step 2 (above).
- **Elaborating quotations (fixed).** Building each proof as an Ltac2
  quotation with the term table and the facts antiquoted had the
  elaborator walk them as trees: 2.5 s of NS 60's 3.2 s in step 3. Now
  closed definitions (rules above).
- **Typing the term table per fact (fixed).** NS 60's `Qed` was 4.5 s, 3.3 s
  of it the conversion facts: the kernel typed the term table (quadratic
  as a tree, on NS) once per fact, and reduced each fact's predicate. Now
  1.2 s (rules above). The same fix took VT 300's `Qed` from 2.7 to 0.41 s
  and VA 300's from 2.8 to 0.45 s.
- **Superlinear deep nesting (fixed).** The `Qed` side was the VM issue
  and the per-fact typing above. On the tactic side, the term table
  compares a new term with each entry in turn (`tbl_add`; variables are
  keyed by name). Keying the rest was measured and is not worth it: the
  comparison is `Constr.equal`, native and fast, and a key computed in
  Ltac2 costs more than the scan (VT 300: reification 0.33 s in all).
