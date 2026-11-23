# `names`: its steps, what could be simpler, and how complete it is

This note covers three things:
- the steps the `names` tactic takes now;
- what could be simplified;
- what can be said about its completeness.

The design summary in `docs/design.md` covers the same pipeline more
briefly. The benchmark figures are in the last section.

## The steps

`names` makes one pass over the goal. Each step runs once, over the whole
goal, and its output needs nothing from the steps before it.

0. **The user's `cbn`.** This is not part of `names`. Substitution is the
   Kleisli extension of the library's `apply`, so `cbn` pushes it through
   the syntax's constructors, and `names` knows nothing about them.
1. **`names_pre`.** This rewrites with the monad laws a syntax's `Subst`
   functor adds:
   - going under a binder lifts the adjustment;
   - nested substitutions fuse: `t [a] [b] = t [a ⨾ b]`.

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
   2. **Convert** (`Conv.aconvn`).
      - A term that is a substitution `csubst L c u` becomes `u` with `c`
        in its payload.
      - A term that is a variable `tvar w` becomes a look-up of `w`
        through its payload.

      This goes all the way down: the terms of each `c` are converted
      too.
   3. **If `t` is a variable `v`**, normalise the converted expression
      (`HNorm.norm`) and follow it from `v` once (`HNorm.follow`, through
      `HShow.hlook_show`). There are three outcomes:
      - a variable `w`, so the node becomes `tvar w`;
      - a term `u` with a payload `b`, so it becomes `csubst L b u`;
      - `w` looked up through the rest `b` of the word, say an atom, so
        it becomes `csubst L b (tvar w)`.

      The rewrite is the law's `sl_res`.
   4. **Otherwise**, normalise and display the result with shared
      definitions (`HDisplay`). The rewrite is the law's `sl_rel`, and it
      applies to the nodes with that adjustment only.

   An adjustment outside a node is reified, normalised and displayed the
   same way. It is not converted, and it is rewritten by equality
   (`adj_eq`).
4. **Materialise** (`names_mats`). In each node, each term with a payload
   `u⟨| b ⟩` becomes the term `csubst L b u` with the identity payload
   (`sl_rel` again). Then the same happens in the nodes this makes.
5. **`names_apply`.** This handles `apply_var a v` left in the goal, for
   an adjustment of any family, with no law. It uses the same
   `hlook_show` as step 3.3.
6. **`names_post`.** The nodes go back to `t [a]`, and `t [⟦⟧] = t`.

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

1. **Materialise only the payloads the display shows.** This is the
   important one, because it is also a performance bug (see the
   benchmarks).
   - **The problem.** Step 4 works on the normaliser's word, not on the
     displayed expression, so it materialises payloads the user never
     sees. The normal form of `⟦x1 := f1⟧ ⨾ … ⨾ ⟦xn := fn⟧` has, on
     entry `i`, the payload "the substitutions after `i`". The display
     shows the word compactly, as the composition itself, with no
     payloads. Step 4 still finds the payload of `x1`, turns it into
     `f1 [⟦ x2 := … ⟧ …]`, and does the same again inside that payload.
     No sharing survives, so the output has 2ⁿ − 1 entries.
   - **The fix.** Make materialisation a function on the shown
     expression. Every `NBindE u p` with `p` not the identity becomes a
     new term `u [p]`, with the payload's own shown payloads materialised
     first. Shared definitions stay shared, so the new terms refer to
     them. This would happen inside step 3, before rendering, so a node
     needs one rewrite instead of one per payload. It would replace
     `mat_one`, `names_mats`, `HShow.hmat_target`/`hmat_display` and the
     word-level proofs (`paid_matw`, `hmat_show_sound`, `mat_bridge`):
     about 250 lines.
   - **The cost.** A shown payload can sit under a composition or a
     lift, as in `(u, W ∘ c)`. Materialising it there relates `(u, W ∘
     c)` to `(u [c], W)`. That is the materialising base with a context
     `W`, which `Conv.lawbase` does not have. One fix is to add it and
     prove it in `Subst` like `nbase_rv`; the catch is that well-scopedness
     of `W` has to be carried in the base. The other is to materialise
     only payloads in direct positions: inner entries of context forms,
     their tails, and shared definitions. Those need no new base, and
     they are what the display produces for payloads it shows.
2. **One reification per node.** If materialising is folded into step 3,
   each node is reified once and rewritten once. Steps 3 and 4 become one
   step, and the tactic is: pre-rewrite; per node, reify, convert,
   normalise (and follow, for a node on a variable), display,
   materialise, render, rewrite; post-rewrite.
3. **The two proof routes for normalising.**
   - A node is rewritten by `sl_rel` from a per-variable relation, after
     conversion.
   - A free adjustment is rewritten by `adj_eq` from a denotation
     equality, without conversion.

   They share the normaliser and display call but duplicate about 40
   lines of proof plumbing in `conv_one` and `show_adj_with`. A free
   adjustment could go through the node route with the trivial
   conversion and a relation that is equality.
4. **`names_apply`.** It duplicates `conv_one`'s variable path for the
   variable and term cases, about 50 lines, because it has no law. It
   could be the variable path with the conversion lists empty and a
   "law" for targets. Alternatively, `apply_var` goals could be dropped
   from `names`: only `Tests/NamesTests.v` uses them.
5. **The law.** `SubstLaw` has three fields: `sl_var`, `sl_rel` and
   `sl_res`. `sl_rel` follows from `sl_res` given extensionality of
   substitution in the variables. That trades one field for another, so
   there is little gain unless extensionality is wanted anyway.
6. **Ltac2 hygiene.** `Control.plus` leaves choice points: a later
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

What this does not cover:
- **Atoms are syntactic.** Two terms that are convertible but written
  differently are different atoms.
- **Labels are generic beyond the order facts.** A comprehension model may
  treat two labels of unknown order as unrelated. An equation that holds
  for all concrete labels only by cases (`x = y` or not) is not decided.
  `STLC.renaming1'` does this case split by hand with
  `label_compare_spec`. With an order fact for every pair of labels, I
  expect the concrete adjustments with generic atoms to separate
  different normal words. Then the comprehension-model completeness
  would carry over to the concrete semantics. That is not proved.

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

### 3. What `names` does not attempt

- Pushing substitutions through constructors. That is the user's `cbn`.
- Non-literal variables: `(tvar v) [a]` for a variable `v` in the
  context is a node on an atom, and is not evaluated.
- Nodes under a binder that uses the binder's variable (the candidates
  must be closed terms). An example is a substitution inside `fun x =>
  … t [a x] …`.
- Case splits on labels, as above.

## Benchmarks

The families below run on the current branch ("new") and on the commit
before the single-pass work (20ed942, "old"). The goals have the form `P
(…) -> True`, so `names` has one rewrite to make. Times are tactic time +
`Qed`. A dash means not measured. "Rewrite by type" is the figure before
the variable-path fix described under "Problems found".

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
  MV: the normaliser's word for a chain of n substitutions gives every
  entry the rest of the chain as its payload, and step 4 materialises
  all of them, with no sharing (see "What could be simpler", item 1).
  The normal form itself is linear: step 3 alone shows SN as the chain
  it is.
- **Superlinear deep nesting (not fixed).** At about n², NS is the one
  family with a clearly superlinear tactic time. Each nested node's term
  is compared and checked again in full: each `nest_fact` repeats a term
  of size up to n. VT's `Qed` (0.57 s at 100, 3.0 s at 300) is mildly
  superlinear too.
