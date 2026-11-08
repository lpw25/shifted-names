# Shifted names: design history and final design

This document reconstructs how the design evolved from the TyDE 2019 talk to the
last commit (July 2022), working from the code on each branch. Almost every
commit after the initial import is titled "WIP", so intent comes from comments in
the source. Where a point is my interpretation and not stated in the code, it is
marked *(inferred)*.

No Coq/Rocq toolchain was available in the environment where this was written,
so **nothing has been compiled**. Statements about what builds come from
checking identifiers against definitions by hand.

---

## 0. Summary

**What stayed constant throughout:**

- Bound variables are handled locally nameless: binders carry no names, and you
  open a body with a name before working under it.
- Free variables are a *name plus a shift index*: `x₍ᵢ₎` is "the `x` that is `i`
  binders of `x` further out". Opening with an `x` that is already in use is
  never a capture problem, because the old `x`s get shifted. As a result, typing
  rules can quantify over **all** names with no freshness side conditions.
- The goal is a rewrite system for renamings and substitutions with a usable
  normal form.

**How the design moved, in five phases:**

| Phase | Dates | Where | Core idea |
|---|---|---|---|
| 0 | 2019-09 – 2019-10 | `master` (`src/`, `TyDE-2019/Names.v`) | Terms indexed by bound-variable count. Renamings are a syntax tree `ren` (with `r_comp`) interpreted by `applyv`. Simplification is up to a pointwise relation `eqr`, so it needs setoid rewriting. |
| 1 | 2019-09-29 – 2020-02-09 | `next` (`Var2.v`, `Renaming2.v`) | Operations become edits on *environments*: functions out of index, name, level and var. Composition is removed from renaming syntax and computed instead. Still setoid throughout. |
| 2 | 2020-02-16 – 2020-07-05 | `next` (`Index.v`/`Name.v`/`Level.v`, then the `I*.v` files) | Commutation is organised as **operational transforms** and permutation-group relations. Normal-form target found: a **Dyck word** of pops then pushes. |
| 3 | 2020-07-05 – 2020-08-16 | `next` tip (`Var.v`, `Term.v`) | Concrete, level-indexed first-order datatypes `closing N M` / `renaming N M` with computable composition. **SProp** first used, for level bounds. Associativity proofs for indexed closings stall. |
| 4 | 2020-08-17 – 2021-01-31 | `next-unindexed` | **Indexing is dropped.** Bound variables become just another label (`None`). A single `pop_var`/`push_var` pair subsumes open, close, bind and weaken. Renamings are raw syntax plus an **SProp normalisation proof**, so equality is Leibniz. A canonicity theorem is proved. |
| 5 | 2022-07-20 | `adjustments` (one commit) | Restart of the renaming layer on top of phase 4. A renaming becomes two lists, *incoming* (pushes into numbered slots) and *outgoing* (pops from slots), with variables as `{label_opt; nat}`. Unfinished: the file stops mid-definition. |

**Status of the main goals:**

- The **reflection-based normaliser was never started.** No reification tactic or
  denotation function exists in any phase.
- The SProp idea of "build unindexed first, layer indexing on top" was put into
  practice in phase 4. The indexing layer itself was never written.
- Terms and substitutions were dropped from the build in phases 4 and 5.

**Branch topology:** the history is linear, so each later branch contains the
earlier ones.

```
master:          14aad3f ─ 54ae7ba ─ eb28b95 (TyDE Names.v) ─ 14bb7fc (merge tz18: ",," notations)
                              │
next:                         └─ b1644fa … e9f6a25   (2019-09-29 … 2020-08-16, 43 commits)
next-unindexed:                              └─ d15042e … f62e58a   (2020-08-17 … 2021-01-31)
adjustments:                                                 └─ 548e0df   (2022-07-20)
```

---

## 1. Phase 0: the original design (`master`, TyDE 2019)

The `master` branch holds the original design in two forms:

- **`src/`** (`Var.v`, `Relative.v`, `Morph.v`, `Context.v`) and
  `examples/Lambda.v`. These were imported on 2019-09-08 from the
  "effect-labels" repo.
- **`TyDE-2019/Names.v`**, the self-contained file from the talk (added
  2019-10-08). It is a simpler, concrete-term cut of the same design. Its
  comments and FIXMEs are a subset of `src/`'s, often word for word.

### Representation

```coq
Fixpoint level (V : nat) : Set := match V with 0 => Zero | S V => @Succ (level V) end.
Inductive var {V : nat} := free (name : string) (index : nat) | bound (v : level V).
Inductive term {V : nat} :=
| vv : @var V -> @term V | const : nat -> @term V
| lam : @term (S V) -> @term V | app : @term V -> @term V -> @term V.
```

- `level V` is a finite type with `V` elements built from nested options.
- `v0` is the innermost binder, so despite the name `level` it behaves like
  de Bruijn *index* 0.
- `src/Var.v` makes names a record, `Record name := mkname { n_string; n_index }`,
  with a coercion from `string`. That lets `open`/`close` act at any `x₍ᵢ₎`, not
  only `x₍₀₎`.

### Primitive operations on variables

| Operation | Type | What it does |
|---|---|---|
| `wkv` | `var V → var (S V)` | weakening |
| `openv a` | `var (S V) → var V` | `v0 ↦ a₀`, and `aᵢ ↦ aᵢ₊₁` |
| `closev a` | `var V → var (S V)` | inverse of `openv a` |
| `bindv` | `var (S V) → option (var V)` | `None` exactly at `v0` |

Derived operations:

- `shiftv a = openv a ∘ wkv`
- `renv a b = openv a ∘ closev b`
- `substv a = bindv ∘ closev a`

Case analysis goes through *views*:
`var_comparison a v := samev : … (free a 0) | diffv x : … (shiftv a x)`.

### Renamings as syntax

```coq
Inductive ren :=
| r_id | r_comp (r s : ren) | r_shift (b : string) (r : ren)
| r_rename (b : string) (r : ren) (a : string) | r_subst (t : @term 0) (r : ren) (a : string).
```

- Each constructor except `r_id`/`r_comp` is a balanced pair: close or weaken on
  the way in, open or bind on the way out, with `r` acting in between.
- `applyv : ren → var V → term V` interprets a renaming, and
  `apply r = map_term (applyv r)`.
- `is_renaming` / `applyrv` give a variable-to-variable interpretation for
  substitution-free renamings.

### Rewrite strategy

The comment states the strategy: *"group balanced pairs of operations into
'ren's; push opens/bind right and wk/close left; simplify rens"*.

- All lemmas go into one hint DB (`rw_names`; split into four DBs in `src/`).
- The tactic is `names := repeat (autorewrite with rw_names; cbn)`.
- Confluence is managed by hand:
  - critical-pair lemmas (`rw_ren_shift_subst_crit`);
  - `_comp` duplicates of every rule, because `r_comp` is normalised to be
    left-nested;
  - comments about moving `wkv` "carefully to avoid breaking confluence".

### Why it was slow, and why it needed setoid rewriting

1. **`ren` is a syntax tree, so distinct trees denote the same renaming.**
   Associativity, identity, `r_under x r_id ≈ r_id`, rename∘rename fusion and
   subst∘shift cancellation are all stated up to
   `eqr r s := ∀ V v, applyv r v = applyv s v`. Using them inside
   `apply r t`, or nested inside other `ren`s, needs `Proper` instances
   (`mor_applyv`, `mor_map_term`, `mor_r_comp`, …) and setoid rewriting.
2. **Generalising to any syntax uses `nset := nat → Set`.** `src/Relative.v` is
   generic over any syntax with `unit`/`kleisli` satisfying relative-monad laws.
   Its maps are `morph T N S M := ∀ V, T (N+V) → S (M+V)`. Because
   `N + S V ≠ S (N + V)` definitionally, `Morph.v` needs casts, `eq_dep`, UIP on
   `nat` and the fragile Ltac `inductT`/`popT`/`pushT`/`simplT`.
3. **Convertible but not syntactic forms.** `free x : var (S V)` is convertible
   to `wkv (free x)` but not syntactically equal, which needs explicit `change`
   loops ("FIXME: this again. Should we remove free?").

### Client side

`examples/Lambda.v` shows the payoff:

- STLC with `LAM : (∀ x, Γ & x ~ A ⊢ open x b ~ B) → Γ ⊢ lam b ~ A ⇒ B`.
- Weakening and substitution for arbitrary context morphisms `Γ =[r]=> Δ`, in a
  few lines each.
- Barendregt's substitution lemma in shifted form, with no freshness assumptions:
  `[L//y][N//x]M = [([L//y]N)//x][([^x]L)//y]M`.
- CPS type preservation, using fixed names `"k"`, `"x"`, `"f"` protected by
  shifts.

The library interface the later phases still need to support is this:
universally quantified binders plus `[r] t` with automatic simplification.

---

## 2. Phase 1: environments and composition-free renamings (Sep 2019 – Feb 2020)

**Files:** `src/Var2.v` (new) and `src/Renaming2.v` (created 2020-02-03), on
branch `next`.

### Environments instead of variables

Instead of functions on variables, the primary objects are **functions out of**
index, name, level and var, treated as data structures:

- `iindex` is a stream indexed by `index`.
- `iname` is a direct sum of streams, one per string.
- `ilevel` is a cons-list.
- `ivar` is a pair of an `iname` and an `ilevel`.

The primitive operations are edits on these: get, delete, insert, move, and
hd/tl/cons. Open and close become operations on the environment:

```coq
Definition open_ivar n (f : ivar N T M) : ivar (S N) T M :=
  pair_ivar (delete_iname n (fst_ivar f)) (cons_ilevel (get_iname n (fst_ivar f)) (snd_ivar f)).
Definition close_ivar n (f : ivar (S N) T M) : ivar N T M :=
  pair_ivar (insert_iname n (hd_ilevel (snd_ivar f)) (fst_ivar f)) (tl_ilevel (snd_ivar f)).
```

`weak_ivar` and `bind_ivar` are similar, and `rename`/`shift`/`subst` are
derived from these four.

Laws are stated pointwise up to `=m=` / `=km=` / `=p=` with `Add Parametric
Morphism` everywhere. Each law is duplicated as a plain-equality, fully applied
lemma (`eq_*_expand`).

Normalisation uses layered `rewrite_strat topdown` pipelines (`simpl_iindexs`,
`simpl_inames`, `simpl_ilevels`, `simpl_ivars`), which unfold derived
operations, simplify, then fold back. The author hit `rewrite_strat` and
morphism-resolution bugs; comments say "Alias the projections to avoid bug in
rewrite_strat" and "Work around apparent bug in morphism resolution".

### Commutation as operational transforms

The 2019-10-23 commit introduces a comment framing commutation lemmas with the
**operational transforms** IT/ET/XT from collaborative editing. In application
order:

```
o1 (o2 f) = XT(o2, o1) (ET(o1, o2) f)
```

From this comes a full matrix of `swap_X_ivar_Y_ivar` lemmas for X, Y in
{open, close, weak, bind, rename, shift, subst}.

### Composition-free renamings (`Renaming2.v`)

```coq
Inductive renaming (trm : Set) :=
| r_id | r_shift (b : name) (r : renaming trm)
| r_rename (b : name) (r : renaming trm) (a : name)
| r_subst (t : trm) (r : renaming trm) (a : name).
```

- `r_comp` is gone. Composition is now a **function** `compose_static`, built
  from `transfer_open_var`, which pushes one `open` through a renaming.
- `apply_static_ivar_compose` is proved (up to `=m=`).
- Associativity of `compose_static` was left incomplete: there are `admit`s and
  empty bullets.
- `r_subst` is ignored by the "static" interpreter.
- There is still no link from these operations to terms.

---

## 3. Phase 2: reified stream operations and the Dyck-word normal form (Feb – Jul 2020)

**Files:** `Index.v`, `Name.v`, `Level.v` (split from `Var2.v` on 2020-02-16);
from 2020-07-05 these are `IIndex.v`, `IName.v`, `ILevel.v`, `IVar.v`. "I"
marks the files about the `iX` environment types; it does not mean "indexed".

### Reified stream operations

Single stream edits are reified as values:

```coq
Inductive stream_op := insert | delete.
```

Then:

- `transpose_iindex_left/right` compute, as a table, the transformed indices
  needed to swap two operations.
- `normalize_iindex_*` handles non-unique representations.
- The permutation-group presentation is proved as lemmas with matching tactic
  notations:
  - σᵢσᵢ = 1 (`transpose_*_squared_left/right`)
  - the braid relation (`transpose_*_reverse_left/middle/right`)
- `Name.v` mirrors this per label.

This is *partial* reflection: the operations are first-order values and `cbn`
computes the transformed indices. There is still no reify tactic.

### The normal form

The key design insight is stated in `Var2.v` at 060cf20 (2020-06-25):

> Any sequence of operations … must have "well-balanced" push and pop
> operations. Treating pop operations as opening brackets, push operations as
> closing brackets and ignoring swap operations; the sequence must be a Dyck
> word. … allowing as "proper" transpositions three cases: (1) push·pop →
> push·swap·pop, (2) pop·pop·swap → pop·pop, (3) swap·push·push → push·push.
> The maximal elements of this pre-order are sequences consisting of a sequence
> of pop operations followed by a sequence of push operations.

Here, *pops* are `open`/`bind` and *pushes* are `close`/`weak`. **"All pops,
then all pushes, with swaps pushed to the boundary"** is the normal form that
every later design tries to represent canonically.

### Terms

`Trm.v`, which became `Term.v` on 2020-07-05, makes terms an abstract indexed
`nset` with relative-monad `unit`/`kleisli`. Operations are `kleisli` of
variable-level morphisms. Term.v also states the goal in Leibniz equality:

```coq
combine_open_renaming_close : open n1 ([r](close n2 t)) = [r; n1 <- n2] t
```

Several of these proofs are unfinished.

### The 2020-07-05 restructure

- A new, small `Var.v` defines the plain types (`name`, `level`, `var V`) and
  **concrete, computing** `open_var`, `close_var` and `weak_var` by pattern
  matching.
- The `I*` files are demoted to a specification layer. For example,
  `open_var_def : @Var.open_var n =m= open_ivar n` is proved there.
- The old `master` `Var.v` is kept as `VarOld.v` for `Relative.v`.

This is the start of moving from "setoid combinators" to "concrete functions
that compute".

---

## 4. Phase 3: concrete level-indexed normal forms (Jul – mid-Aug 2020, `next` tip)

`Var.v` grows to about 3,500 lines. On 2020-07-15 the `I*` files leave the
Makefile.

### First use of SProp

SProp first appears here, to make level bounds proof-irrelevant:

```coq
Inductive less_than : nat -> nat -> SProp := ...
Record level N := mklevel { l_nat : nat; l_less_than : less_than l_nat N }.
```

### The normal form as indexed datatypes

The Dyck normal form becomes indexed datatypes:

```coq
Inductive closing : nat -> nat -> Set :=            (* the "pushes" *)
| closing_id : closing 0 0
| closing_weak : level (S N) -> closing N M -> closing (S N) M
| closing_exchange : level (S N) -> closing N M -> level (S M) -> closing (S N) (S M)
| closing_close : level (S N) -> closing N M -> name -> closing (S N) M.
Inductive renaming (N : nat) : nat -> Set :=        (* "pops" over a closing *)
| renaming_closing : closing N M -> renaming N M
| renaming_shift : name -> renaming N M -> renaming N M
| renaming_open : name -> renaming N M -> level (S M) -> renaming N (S M)
| renaming_rename : name -> renaming N M -> name -> renaming N M.
```

Around these datatypes:

- Each constructor records the level it acts at, via the cyclic permutations
  `cycle_in_var`/`cycle_out_var`.
- Composition (`compose_closing`, `compose_renamings`) is computed by
  transposing operations through (`transpose_level_closing`, …).
- An indexed `substitution` datatype and its term-level application exist in
  `Term.v`.
- Operational-transform lemmas now live on `var` operations
  (`transpose_pushes_*`, `transpose_pops_*`, `transpose_push_pop_*`).

### Where it stalled

The last proved results are `apply_transpose_level_closing`. In
`RenamingEquations.v` at e9f6a25, the associativity of indexed `closing`
composition (`closing_associative`, with helpers `foo`, `bar`,
`transpose_leve_compose_closing`) is full of `admit`s and dangling bullets.
**This is where indexing became too painful.** The very next commit starts the
unindexed branch.

---

## 5. Phase 4: the unindexed design (`next-unindexed`, Aug 2020 – Jan 2021)

This phase carries out the SProp plan you remembered. Build a computational,
unindexed core whose normal forms are certified by SProp proofs. Layering the
indexing on top was left for later.

### 5.1 Variables: bound variables are just another label

Commits 08-17 to 09-09 (d15042e, e262f8c, 72b7818, 5084590, a1aa370), as at
f62e58a:

```coq
Definition label := string.                              (* Label.v, with a total order *)
Record name := mkname { n_label : label; n_index : index }.
Inductive var := free (n : name) | bound (l : level).    (* level := nat, no V index *)
Definition v_label_opt v := match v with bound _ => None | free n => Some (n_label n) end.
Definition v_nat v := match v with bound l => l | free n => n_index n end.
Definition mk_var (so : option label) n := ...
```

A bound variable is a variable with label `None`, and its "shift index" is its
de Bruijn number. Every operation is defined **uniformly** over labels:

- `shift_var v1 v2` (only touches `v2` if it has the same label and index ≥)
  and `unshift_var`.
- `pop_var` and `push_var`, using a "slot" carried by `option`:

```coq
Definition var_op N M := options N var -> options M var.     (* option^N var -> option^M var *)
Definition pop_var  v1 : var_op 1 0 := fun vo => match vo with None => v1 | Some v2 => shift_var v1 v2 end.
Definition push_var v1 : var_op 0 1 := fun v2 => if var_eqb v1 v2 then None else Some (unshift_var v1 v2).
Definition swap_var : var_op 2 2 := ...
```

So `open x`, `close x`, binding a de Bruijn variable and weakening all become
`pop`/`push` at a particular `var`. The separate constructors of earlier phases
(`open`/`bind`/`close`/`weak`/`cycle_in`/`cycle_out`/`exchange`) collapse into
two operations parameterised by a variable. *(inferred)* This is the "names +
de Bruijn indices" unification taken to its conclusion.

`Label.v` defines a hand-written lexicographic order on strings, with `None`
(bound) ordered after all `Some`. With it, variables are **totally ordered**
(`is_less_equal_var`, `is_less_than_var`), which is what lets normal forms be
*sorted* lists.

### 5.2 The equational theory of variables (`VarEquations.v`)

- Conditional reduction lemmas (`reduce_shift_var_ge`, `reduce_push_var_eq`,
  …) are driven by `case_vars v1 v2`, which splits on label equality and the
  trichotomy of indices.
- Identities: `pop_push_identity` (`pop_var v @ push_var v =v= 1`),
  `push_pop_identity` and `swap_swap_identity`.
- **Transpositions:** `transpose_pops`, `transpose_pushes` and
  `transpose_push_pop`. For example:
  `pop v1 ∘ ↑(pop v2) =v= pop (shift v1 v2) ∘ ↑(pop (unshift v2 v1)) ∘ swap`.
- The **Coxeter presentation** of the permutation group is stated in a comment
  and proved as lemmas: σᵢσⱼ = σⱼσᵢ for |i−j| > 1, σᵢ² = 1, and the braid
  relation.
- `reducible_transposed`: `shift_var v2 v1 = v3 ↔ v2 ≠ v3 ∧ unshift_var v2 v3 = v1`.
  The comment says this "seems like it should be in some sense complete" but
  forces stronger preconditions than necessary in places.

### 5.3 Closings (Aug 2020, later abandoned)

`Closing.v` and `ClosingEquations.v` implement the pattern on the push half:

```coq
Definition raw_closing := list (option var).
Record closing := mkclosing { c_raw : raw_closing; c_normalized : normalized_pushes c_raw }.
```

`closing_left_identity`, `closing_right_identity` and `closing_associative` are
proved with **plain `=`**. This is the first full demonstration that "raw syntax
+ SProp normality proof" gives Leibniz-equal canonical forms. These files were
written against an older `Var` API, were never updated, and left the Makefile
when renamings took over.

### 5.4 Renamings: raw syntax, a group, and a canonical form

`RawRenaming.v` defines the raw syntax:

```coq
Inductive raw_renaming :=
| raw_renaming_id
| raw_renaming_extend : var -> raw_renaming -> var -> raw_renaming.
Fixpoint apply_raw_renaming_var r : var_op 0 0 := match r with
| raw_renaming_id => var_op_id
| raw_renaming_extend vl r vr => pop_var vl @ lift_var_op (apply_raw_renaming_var r) @ push_var vr end.
```

`extend vl r vr` sends `vr ↦ vl`; on every other variable it is `r` conjugated by
unshift/shift. That is exactly one "push then pop" pair, the Dyck shape, with
the middle being `r`.

Composition is computed by `transpose_push_raw_renaming` and
`compose_raw_renaming`. Every extension is invertible, giving
`inverse_raw_renaming`.

`RawRenamingEquations.v` proves:

- `raw_renaming_associative` and the identity laws **by `=`**;
- `apply_compose_raw_renaming`;
- `raw_renaming_left_inverse` and `raw_renaming_right_inverse` up to
  `=rr=` (pointwise equality of the applied functions);
- `apply_raw_renaming_var_injective`;
- `swap_raw_renaming_extend`, the reordering equation the normal form has to
  quotient out.

Raw renamings therefore form a group of bijections on the variable space.

`Renaming.v` defines the normal form. It went through two attempts:

- **Dec 2020: "interesting/needed" extensions.** `is_interesting_*`,
  `raw_renaming_extend_boring`, and a normaliser `normalized_raw_renaming_extend`
  (an insertion sort that drops redundant extensions), packaged as:

  ```coq
  Record renaming := mk_renaming { r_raw : raw_renaming; r_normalized : normalized_raw_renaming r_raw }.
  ```

  `normalized_raw_renaming` is `if is_normalized … then sUnit else sEmpty`, so it
  lives in SProp. Two `renaming`s with equal `r_raw` are therefore
  definitionally equal.

- **Jan 2021: "normal" extensions (current).**
  - Right-hand variables are sorted in the total order (`is_all_ordered_raw_renaming`).
  - Each extension is *normal*:
    `¬ is_shifting_var vl (apply_raw_renaming_unmatched_var r vr)`. That is, it is
    not something the unmatched behaviour of `r` would already produce.
  - The last commit adds a parameter `vu` ("under"), exempting extensions below
    a bound.
  - It also adds completeness side conditions (`is_right_complete_under`,
    `is_left_complete_under`).

  The **canonicity theorem** is proved:

  ```coq
  Lemma is_normalized_equivalence_equal vu r1 r2 :
    is_normalized_raw_renaming vu r1 = true -> is_normalized_raw_renaming vu r2 = true ->
    is_right_complete_under vu r1 = true -> is_right_complete_under vu r2 = true ->
    r1 =rr= r2 -> r1 = r2.
  ```

  This is the theorem that turns extensional equality into syntactic equality,
  which is what removes the need for setoid rewriting.

What is missing at f62e58a:

- The normaliser and the `renaming` record (bottom half of `Renaming.v`) were
  not ported to the Jan 2021 definition. They still call
  `is_normalized_raw_renaming` with one argument and use deleted helpers
  (`is_less_equal_vars`, …).
- Closing code was pasted at the end of the file and not adapted.
- There is no `compose` on normalised renamings.
- Substitutions and terms are absent:
  - `Term.v` and `RenamingEquations.v` are stale indexed code;
  - `Context.v` is entirely commented out;
  - `examples/Lambda.v` imports the deleted `Relative.v`.

---

## 6. Phase 5: the July 2022 restart (`adjustments`, 548e0df)

This single commit deletes everything except `Label.v`, `Var.v` and
`RawRenaming.v`, and rewrites the latter two (73 and 164 lines).

### Variables are a plain record

```coq
Record var := mk_var { v_label_opt : option label; v_nat : nat }.
```

The free/bound split is gone entirely: `None` is the bound label. Notation
`"x"₍₂₎` is provided. `less_equal_var` gives a total order in SProp.

### A renaming is "push everything into slots, then pop everything out"

```coq
Definition incoming_item : Set := (option label) * nat.   (* (l, m): capture l₍₀₎ into slot m *)
Definition incoming := list incoming_item.
Definition outgoing_item := option label.                  (* pop slot 0 out as l₍₀₎ *)
Definition outgoing := list outgoing_item.
```

The intermediate state is `var + nat`: either a variable or an occupied slot.

- **Incoming item `(l, m)`.** It acts on an `inl v` with label `l`:
  - index 0 goes to slot `inr m`;
  - index `n+1` goes to `l₍ₙ₎`, an unshift.
- **Outgoing item `l`.** It acts as follows:
  - slot 0 becomes `l₍₀₎`;
  - slot `n+1` becomes slot `n`;
  - existing `l`s are shifted up.

```coq
Definition apply_renaming inc otg {H : incoming_is_less_than (List.length otg) inc} v :=
  match apply_outgoing otg (apply_incoming inc (inl v)) with
  | inl v' => v'
  | inr _ =>            (* <- file ends here *)
```

The SProp hypothesis `H`, through `apply_renaming_var_less_than`, shows that the
result can never be a slot. The missing branch is meant to be eliminated by
`sEmpty` *(inferred from that lemma)*.

### How this compares with phase 4 *(inferred)*

Phase 4 interleaved push/pop pairs (`extend vl r vr`) and needed a subtle
"normal extension" condition plus "under" and "completeness" side conditions to
get canonicity. Phase 5 separates the two halves completely:

- all pushes happen first;
- all pops happen after;
- the permutation between them is made explicit by slot numbers;
- pushes always capture index 0 and pops always create index 0.

This is the Dyck normal form from phase 2 represented directly. Fixing each
push and pop to index 0 removes most of the index arithmetic that the phase 4
normality predicates had to reason about. The canonical-form conditions (for
example, sorted incoming/outgoing lists, no push immediately undone by a pop of
the same label in the matching slot) are **not yet written**.

`RawRenamingEquations.vok` is still listed in the Makefile, but the file was
deleted in the same commit.

---

## 7. The final design, consolidated

This combines phase 4's proven infrastructure with phase 5's representation.

1. **Labels and variables.**
   - `label := string`, with a decidable total order.
   - `var := {v_label_opt : option label; v_nat : nat}`. `Some x` with index `i`
     is the free name `x₍ᵢ₎`; `None` with index `i` is bound variable `i`.
   - All variables are treated uniformly; there are no special bound-variable
     operations.
2. **Primitive operations.**
   - `shift_var v₁ v₂` and `unshift_var v₁ v₂` are the shift and unshift of `v₂`
     past `v₁`.
   - `push v` (capture `v` into a fresh slot, unshifting the rest) and `pop v`
     (release a slot as `v`, shifting the rest). They are inverse
     (`pop_push_identity`, `push_pop_identity`).
   - Locally nameless open, close, bind and weaken are all push/pop pairs at
     particular variables.
3. **Renamings in normal form.**
   - A renaming is a block of pushes followed by a block of pops, with an
     explicit slot permutation (phase 5), or equivalently a sorted chain of
     normal `extend`s (phase 4).
   - Composition is computed by transposing operations. The algebra is
     operational transforms and the Coxeter presentation of permutations,
     proved in `VarEquations.v`.
4. **Canonicity via SProp.**
   - A user-facing `renaming` is a record of the raw data plus an SProp proof
     that the data is normalised.
   - With a canonicity theorem (`r₁ =rr= r₂ → r₁ = r₂` for normalised data),
     extensional equality *is* Leibniz equality, so ordinary `rewrite` works.
   - Composition, identity, associativity and inverse laws hold by `=`. This
     works already for closings (`ClosingEquations.v`) and raw renamings.
5. **Planned on top, never written in the unindexed design.**
   - Substitutions: renamings plus binds of terms, as in phase 3's
     `substitution` datatype.
   - Terms via a relative monad.
   - An indexed layer in which `term N` / scoped variables are carved out of the
     unindexed ones by SProp predicates.
   - A reflective normaliser: reify a term-level expression of open, close,
     shift, `[r]`, …; normalise by computing `compose`; prove `denote ∘
     normalise = denote`.

---

## 8. State of the code by branch

| Branch / commit | Probably builds *(not compiled)* | Broken |
|---|---|---|
| `master` | Everything; there are no `admit`s. | — |
| `next` (e9f6a25) | `Var.v` up to `apply_transpose_level_closing` | `RenamingEquations.v` (indexed associativity, admits), stale `Term.v` |
| `next-unindexed` (f62e58a) | `Label.v`, `Var.v`, `VarEquations.v`, `RawRenaming.v`, `RawRenamingEquations.v`, plus `Renaming.v` lines 1 to about 753, including the canonicity theorem | Rest of `Renaming.v`, `Closing*.v` (old API), `RenamingEquations.v`, `Term.v`, `examples/Lambda.v` |
| `adjustments` (548e0df) | `Label.v`, `Var.v` | `RawRenaming.v` stops mid-definition; Makefile references a deleted file |

The code needs Coq ≥ 8.10 for `SProp`, `-vos`/`-vok` and `Declare Scope`. Any
recent Rocq release should work after minor updates, for example `Hint` locality
attributes and `String Notation` syntax.

## 9. Open questions to settle before finishing

1. **Phase 4 or phase 5 representation for renamings.** Phase 4 has a proved
   canonicity theorem but awkward side conditions. Phase 5 looks simpler but
   has no normality predicate or proofs yet. A good first task is to write the
   phase 5 normality predicate and check whether phase 4's canonicity proof
   structure transfers.
2. **Weakening and substitution.** Raw renamings are bijections on variables.
   Non-bijective operations (`wk`, bind/subst) need either slot-based
   substitutions (pops of terms) or a separate layer. Phase 3's indexed
   `substitution` datatype and phase 1's `r_subst` are the prior art.
3. **The indexing layer.** How scoped terms are recovered from unindexed ones:
   an SProp well-scopedness predicate on terms, and its preservation by
   normalised renamings.
4. **The reflective normaliser.** Its syntax of expressions, and whether it
   targets renamings, substitutions, or term-level operations directly.
5. **Re-establishing the client API** of `examples/Lambda.v` (`[r] t`,
   `Γ =[r]=> Δ`, universal `LAM`) on the new core. This is the acceptance test.

## Appendix: where to look

| Topic | Commit | File |
|---|---|---|
| Talk version | `master` | `TyDE-2019/Names.v` |
| Generic relative-monad version | `master` | `src/Relative.v`, `examples/Lambda.v` |
| Operational-transform comment | 218ce23 | `src/Var2.v` |
| Stream-op transposition and permutation lemmas | 4ca1c8a, 03b6db1 | `src/Index.v`, `src/Name.v` |
| Dyck-word normal-form comment | 060cf20 | `src/Var2.v`, around line 238 |
| Concrete indexed `closing`/`renaming` | 65b3fa1 | `src/Var.v` |
| Indexed associativity attempt | e9f6a25 | `src/RenamingEquations.v` |
| First SProp-normalised structure, proved associative | 2463294 – e262f8c | `src/Closing.v`, `src/ClosingEquations.v` |
| Coxeter/transposition theory on unified vars | f62e58a | `src/VarEquations.v`, around lines 580–910 |
| Raw renaming group | f62e58a | `src/RawRenaming.v`, `src/RawRenamingEquations.v` |
| Canonicity theorem | 0e3e616 – f62e58a | `src/Renaming.v`, around line 489 |
| Slot-based incoming/outgoing renamings | 548e0df | `src/RawRenaming.v`, `src/Var.v` |
