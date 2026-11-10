# Shifted names: implementation plan

This plan takes the design consolidated in
[`design-history.md`](design-history.md) (sections 7, 8 and 10) to a finished
development. The early stages are concrete. The later ones, which integrate
the new core back into a full shifted-names library, are deliberately loose,
because decisions made earlier will reshape them.

## Goals

- A core of **adjustments**: renamings and substitutions on shifted names with
  a canonical representation. Extensional equality is Leibniz equality, so
  plain `rewrite` and `reflexivity` work and setoid rewriting is not needed.
- Good asymptotics for the core operations (apply, compose, normalise,
  equality), using canonical persistent maps instead of lists.
- A **context form** for adjustments that has a normal form even when the
  relationship between some labels is unknown. It is the basis for printing,
  parsing and the reflective normaliser.
- A reflective normaliser, ideally proved to produce an actual normal form.
- **An indexed (scoped) user-facing library.** The unindexed core exists only to
  make our own proofs easier and must not leak into the public API.
- Terms, contexts, and the `examples/Lambda.v` client from `master` as the
  acceptance test.

**Non-goals for now:** the effect-system extras from the OCaml variant
(`Unknown`/`Top`, `Meet`, residuals, factors), and backwards compatibility with
any old branch.

## Ground rules

- **Toolchain:** Rocq 9.x (stdlib as a separate package); see
  [Environment](#environment). Build with `dune` (`rocq` stanzas) or
  `_RocqProject` + `rocq makefile`; whichever we pick, CI runs it.
- **No dependencies** beyond Rocq and its stdlib. In particular, we write our
  own canonical trie rather than using CompCert or stdpp.
- **Where the work lives:**
  - a new branch started from `adjustments`;
  - new code under `theories/` with logical path `ShiftedNames`;
  - old `src/` files are kept only as reference until they are superseded,
    then deleted;
  - the old branches stay untouched as history.
- **Proof style:**
  - Canonical data is a record of raw data plus an SProp proof of
    normality, as in `next-unindexed`'s `Renaming.v`.
  - Every equation is stated with `=`. No `Proper` instances in the core.
  - No `Admitted` on `main`; work in progress lives on branches.
- **Executable from the start:** every operation is a Gallina function that
  computes with `cbn`/`vm_compute` on closed data, with `Example … :=
  eq_refl` tests alongside.
- **Encapsulation:**
  - The unindexed core lives in internal modules.
  - Public modules expose only indexed types, operations, lemmas and tactics.
  - Users never need to unfold through the public layer to the core. The
    sealing mechanism (sealed `Module Type`s, opaque definitions, or private
    namespaces) is fixed in Stage 8 and then applied everywhere.

---

## Key design decisions

### D1. Per-label adjustments (the underlying representation)

This is the representation from design history §7.4. For each label `l`
(an `option label`, where `None` is the anonymous de Bruijn label):

- `inc l`: a list of length *j* of targets for `l₍₀₎ … l₍ⱼ₋₁₎`. Each target is
  `Rename (l', i')` with `i' < out l'`, or `Bind p`.
- `out l`: a count *k* of fresh outer slots.
- Every other `l₍ᵢ₎` with `i ≥ j` maps to `l₍ᵢ₋ⱼ₊ₖ₎`.

Normality means:

- no label has an empty `inc` entry or a zero `out` entry, so absent means
  trivial;
- no `inc l` ends in a transparent entry `Rename (l, out l − 1)`;
- every target is in range.

Renamings are adjustments whose payload type is `Empty_set`.

This representation is efficient and easy to prove things about. It needs
concrete labels to compute.

### D2. Our own canonical maps: Appel & Leroy's extensional binary tries

The paper is **Andrew W. Appel and Xavier Leroy, "Efficient Extensional Binary
Tries", Journal of Automated Reasoning 67 (2023)**, also arXiv 2110.05063. It
gives a trie over `positive` keys whose representation is canonical *by
construction*:

```coq
Inductive tree' (A : Type) :=
| Node001 : tree' A -> tree' A        | Node010 : A -> tree' A
| Node011 : A -> tree' A -> tree' A   | Node100 : tree' A -> tree' A
| Node101 : tree' A -> tree' A -> tree' A
| Node110 : tree' A -> A -> tree' A   | Node111 : tree' A -> A -> tree' A -> tree' A.
Inductive tree (A : Type) := Empty | Nodes (m : tree' A).
```

Empty subtrees are unrepresentable, so
`(∀ k, get k m₁ = get k m₂) → m₁ = m₂` holds without any well-formedness
invariant. An adjustment's canonicity then reduces to canonicity of its
per-label entries. Operations are logarithmic in the key size, and
`combine`/`map_filter` are linear and preserve canonicity.

**We write our own module** (a few hundred lines) following the paper, behind
a small interface: `get`, `set`, `remove`, `combine`, `map_filter`, `fold`,
`elements`, `extensionality`. It must compute well with `cbn` and `vm_compute`
on concrete keys. CompCert's `lib/Maps.v` (`PTree`, LGPL 2.1+) is the paper's
implementation and is useful as a reading reference; we do not depend on it.

**Keys:** an injective encoding `option label → positive`: `None ↦ 1`, and a
string goes bitwise into a positive behind a tag bit.

### D3. Symbolic labels: the context form

Real proofs mention labels that are variables (`∀ x y, …`), and the per-label
representation cannot compute with them. Instead of forcing symbolic goals
through it, we add a second representation of the *same* adjustments.

**Context form.** An adjustment is written as:

- an **input context**: an ordered list of entries `(l, b)`, innermost first,
  where `b` is either a reference to an entry of the output context (renaming)
  or a payload term (substitution);
- an **output context**: an ordered list of labels;
- an **implicit tail**: everything beyond the input context maps to everything
  beyond the output context.

`x₍ᵢ₎` resolves by counting the entries labelled `x`:

- if the input context has more than `i` entries labelled `x`, it is the
  `(i+1)`-th of them;
- otherwise it is in the tail, shifted by the number of `x`s in each context.

This is how the OCaml `parse ~outer ~inner` already presents adjustments.

**Reordering needs ordering facts.** Two adjacent input entries with labels
`x` and `y` can be swapped only if `x ≠ y` is known, because swapping changes
which entry `x₍₀₎` refers to. The same holds for output entries.

**Normal form with partial knowledge.**

- Reorder adjacent entries only when their labels are related by a *known*
  strict order `x < y`, and then always into ascending order.
- Leave entries whose labels have no known relation in place.
- Also drop transparent entries, the D1 condition read in context form.

**Why `<` and not `≠`.** Knowing only `x ≠ y` makes both orders legal, so there
is no canonical choice. Knowing `x < y` picks one. So side conditions and
hypotheses throughout the library are stated with the strict order `<` on
labels, a total order that computes on concrete labels, rather than with `≠`.

**Adjustment variables as tails.** Goals also mention adjustments that are
themselves variables (`∀ σ, …`). The context form must allow an adjustment
atom `σ` as the tail, and still have a normal form:

- `(I, O, σ)` means:
  - an input variable that matches an entry of `I` is resolved by that entry;
  - any other input variable is *unshifted* past `I` and given to `σ`;
  - `σ`'s result is *shifted* past `O`.

  With the implicit identity tail, this is the form above.
- **The binder case.** Moving an adjustment under a binder gives
  `⇑σ = ([None ↦ out₀], [None], σ)`: one input entry mapping to the one output
  entry, with the same label on both, which in practice is usually the
  anonymous label. Many proofs live entirely in this fragment, so it must
  normalise well. For example, `⇑σ ∘ ⇑τ` must normalise to `⇑(σ ∘ τ)`, since
  the output entry of `⇑τ` cancels exactly against the input entry of `⇑σ`.
- **In general**, composing two context forms cancels the inner one's output
  context against the outer one's input context. Entries that do not cancel
  cannot be pushed through an atom, because nothing is known about it. So the
  general normal form is a **word**: context segments alternating with atoms,
  `C₀ · σ₁ · C₁ · σ₂ · … · Cₙ`.
  - Each segment `Cᵢ` is itself normalised, with ordering only under known
    `<`.
  - Adjacent segments are cancelled as far as possible.
  - Atoms are opaque.
- **The uniqueness target extends to atoms:** equal under every instantiation of
  the label *and* adjustment variables (consistent with the known `<` facts)
  implies syntactically equal. The binder fragment (`⇑ⁿσ` and compositions of
  such) is the first case to get right, even if the general word case lags
  behind.

**Roles.**

- The context form is **not** the underlying representation: it is less
  efficient and harder to prove things about.
- It is the basis for **printing and parsing**. Notations parse to it, and
  results print from it, so users see contexts, not tries.
- It is the basis for the **reflective normaliser** (Stage 9): reified
  expressions with label atoms are normalised in context form under the
  hypotheses `x < y` available in the goal.
- **Target theorem:** normalised context forms are unique. If two normal forms
  denote the same adjustment under every instantiation of the atoms consistent
  with the known `<` facts, they are syntactically equal. Soundness alone is
  the fallback, but we aim for this.
- **Bridge:** for concrete labels, a fully sorted normal context form
  corresponds one-to-one with a normal D1 adjustment. `to_context` and
  `of_context` are proved inverse there.

### Why two representations

- **Proofs use the context form.** In proofs, adjustments tend to be small, or
  at least their non-symbolic part is: a few opened names, a lift or two around
  symbolic `σ`s. The context form handles those directly, symbolic labels and
  atoms included, and gives readable, canonical goals.
- **Extracted code uses the per-label map form.** Code extracted from the
  development (for example a compiler or type checker built on it) will meet
  adjustments of any size. Those need the right asymptotics, which the
  canonical trie representation (D1, D2) provides and a context list would not.

The two forms are related by `to_context` and `of_context`, proved inverse on
normal forms with concrete labels (Stage 5).

### D4. Per-label entries: lists for now, revisit for extraction

For now `inc l` is a `list`. Lists are canonical with no extra work, and the
trailing transparent-entry condition is easy to state on them. This is fine
while the development is driven by proofs.

**It is provisional.** A program that uses only a few labels, in the extreme
only the anonymous one, should get the same asymptotics as working directly
with de Bruijn indices. With lists:

- looking up `None₍ᵢ₎` is O(*i*);
- **lifting under a binder** (`⇑σ`, the hottest operation) is O(size of σ),
  because it adds an entry and shifts every target that refers to the
  anonymous label.

Options to revisit once Stages 3–4 are done and there is extracted code to
benchmark:

- **Canonical random access by index.** Per-label entries could be an
  extensional trie keyed by index (plus the length), or skew-binary
  random-access lists, which have a unique shape for each length. Either keeps
  canonicity and makes lookup logarithmic.
- **Cheap lifting.** For example, a per-label count of leading identity
  entries kept as a separate field, so `⇑` is O(1) or O(log). This changes the
  normality conditions: the core must not itself start with an identity entry
  for that label, so it needs to be designed together with canonicity.
- **Composition cost.** It should be compared with de Bruijn substitution
  composition, which is linear in the size of the substitution being mapped
  over.

Keep the per-label entry type behind a small interface from the start (`get`,
`length`, `push_front`, `map`, `last`/`drop_last`), so that this change is
local.

### D5. Users see context forms, never tries

Users work with adjustments through context-form constructors (`identity`,
`push_inner`, `push_outer`, with any adjustment as the tail) and their
equational laws. These should feel like the fundamental data structure.

They are implemented as functions on the trie form, which is efficient and
has proved extensional equality, and the trie form is never visible. The
normaliser reflects goals into a concrete context-form syntax (with symbolic
labels and adjustment variables), normalises there, and turns the result into
equalities between constructor terms.

**Typing contexts get the same treatment.** Their constructors make them look
like ordered lists (empty, extend with `x : A`), with lookup by shifted name.
Underneath, they are an efficient canonical map: per label, the list of
types, in a trie. Stage 10 builds them on the same infrastructure.

### D7. Substitutions in the trie form, and what the core needs from terms

**Representation (as implemented).** A substitution is an adjustment whose
targets are either `Rename w` or `Bind p`. A payload `p` is stored **already
in the outer scope**: it has had everything outside its entry applied to it.
This is your "after the rest of the adjustment".

- `apply a v` is a trie lookup plus a list index, with no work on payloads.
- `push_inner h t a` is O(log n + |entry for h|) and touches no payloads.
- Composition `compose a b` maps every target of `b` through `a`. For a
  `Bind p` that means applying `a` to `p` (`act a p` below).
- `push_outer h a` is composition with `shift h`, so it applies
  `act (shift h)` to **every payload** of `a`.

Because payloads are stored in normal form in the outer scope, the
representation stays canonical, and Leibniz equality is extensional equality.

**Asymptotics.** The expensive case is lifting under a binder,
`⇑σ = push_inner l l₀ (push_outer l σ)`. It costs O(#entries) trie work plus
one payload shift per payload. A traversal of depth `d` with a substitution
of `m` payloads therefore does `d·m` payload shifts.
- **Plain de Bruijn substitution** (σ as a function, `⇑σ` as a closure)
  instead pays only at variable occurrences.
- **Making payload shifts cheap** is in the term type's hands: for example,
  terms with a delayed top-level renaming make `act (shift h)` O(1).
- **The remaining O(m) per lift** in the trie is the D4 issue: a lazy
  "pending outer pushes" field or a per-entry stamp would help.
- **Canonicity is the catch.** Any lazy representation of payloads, such as
  storing `(p, pending)` pairs, breaks canonicity unless something
  normalises it. So laziness has to live either inside the payload type,
  behind `act`, or in a normalisation step that is not part of the
  canonical data. Open question.

**Decision: free lifting is justified by indexing, not tracked at runtime.**
There is no reference counting. Instead:
- **Core lemma.** `lift_free` (Laws.v) shows `lift sp l a = a` whenever `a`
  has no entry for `l`, no target mentioning `l`, and payloads unchanged by
  the shift.
- **Indexed layer.** Where the indices guarantee those conditions, it uses a
  "go under a binder" that does nothing, with a proof that it agrees with
  `lift` there. In the λ example (`theories/Examples/`), any closed
  substitution `s : sub 0 0` can be used at every scope (`at_scope`) with
  unchanged data, `lift (at_scope s) = at_scope s`. The traversal
  `subst_closed` never lifts, and `subst_closed_spec` says it equals the
  ordinary substitution.
- **User-facing substitutions** should be of this closed kind: free names to
  closed terms, as in `master`. The locally nameless operations (open,
  close, instantiate) are the only ones that genuinely change when lifted.

**Minimal requirements on terms (what the core actually uses).** None for
renamings (payload type `Empty_set`). For substitutions, the payload type
`P` needs only a **right action of adjustments**:

- `act : adjustment P → P → P`;
- `act_id : act identity p = p`;
- `act_comp : act a (act b p) = act (compose a b) p`, where `compose` uses
  `act a` on `b`'s payloads.

Every payload side condition in the constructor laws (`Laws.v`) follows from
these two. Examples:
- `compose_cancel` needs `act a p = act (push_inner h t a) (act (shift h) p)`;
- `lift_compose` needs `act` to commute with shifts.

No variable embedding, binders, induction principle or decidable equality is
required. That makes "terms" anything with such an action:
- a user's own inductive type with a hand-written substitution;
- a closure or environment representation;
- a type of types, for typing contexts;
- or even another adjustment.

**Optional extras, for the layers above:**
- `as_var : P → option var`. Used to normalise `Bind (var w)` into
  `Rename w`, so that two substitutions with the same action on terms are
  equal (the λ example needs this).
- `wf : nat → P → bool`, with `act` preserving it under scoped adjustments.
  This is needed by the indexed layer (D6).
- A Relative.v-style structure (var embedding, Kleisli extension over the
  user's own inductive type, monad laws). This is a convenience layer at the
  end of the dependency chain. It derives `act`, `act_id`, `act_comp`,
  `as_var` and `wf` from a small number of user proofs. Building terms by
  hand without it must remain easy.

### D8. Revised representation: abstract closed payloads and a thinning front

This supersedes the payload parts of D7. It came out of the discussion on
O(1) lifting and canonicity.

**The goals:**
- `lift` and weakening by a bound variable are O(1) for every adjustment;
- a lift built from constructors is the same value as `lift`;
- canonicity is structural;
- the core needs nothing from terms.

**Payloads are closed terms with a lazily applied adjustment.**
- A substitution target is `Rename v` or `Bind u ρ`. Here `u` is a term
  with no bound variables, opaque to the core, and `ρ` is an adjustment
  meaning "apply `ρ` to `u`".
- `ρ` is normalised to ignore its action on bound-variable inputs, since `u`
  has none.
- Equality compares `u` and `ρ` as data. Two payloads denoting equal terms
  through different representations are different values.
- The core never applies an adjustment to a term. Composition maps `b`'s
  payloads `(u, ρ)` to `(u, a ∘ ρ)`.
- Materialising a lookup result (applying `ρ` to `u`) is the business of the
  convenience layer.

**A thinning front for the anonymous label.**
- An adjustment is `θ ⊕ core`. `θ` is a keep/drop string read from the
  outside in; a keep wraps with `lift(·)` and a drop wraps with `shift ∘ ·`.
- So `θ` is *not* composed after `core`. Lifting a composite lifts both
  parts, so the front has to be a word of wrappers.
- Meaning, on bound variables:
  - the inputs `None₍ᵢ₎`, for `i` below the number of keeps, go to the
    positions of the keeps;
  - the drops are output slots nothing maps to;
  - `core`'s bound inputs and outputs are moved past the `θ` region;
  - `core`'s payloads are shifted by `|θ|`, whatever the keep/drop pattern.
- `lift` conses a keep and `push_outer None` conses a drop. Both are O(1),
  and payloads are untouched.
- `push_inner None None₀` on a drop-headed front turns the drop into a keep,
  so a lift built from constructors equals `lift`, in O(1).
- **Canonical form:**
  - absorb into the inner end of `θ` while `core` is `lift(core')` or
    `shift ∘ core'`, and `core` is not bound-free;
  - for a bound-free `core`, `θ` has no trailing keeps;
  - a payload `(u, ρ)` allows absorption exactly when `ρ` is itself
    drop-headed or mentions no bound variables. That is a structural check,
    since `u` has none.
- Payload adjustments `ρ` only ever act on free names, so their canonical
  form keeps only their total bound-variable shift and their free-name
  entries.
- Thinnings should be run-length encoded, so that "shift by `|θ|`" in a
  lookup is O(1).

**Structure.** Adjustments are nested (payloads contain adjustments), so
operations are nested fixpoints and canonicity is proved by nested
induction. The existing per-label trie core is reused as `core`.

**Stages:**
1. Thinnings.
2. The nested adjustment type and its structural operations.
3. The `(θ, core)` normal form, with pushing a thinning through an
   adjustment for composition, and the canonicity proof.

### D9. The final core representation (supersedes D8 and Encoded.v)

**Data.** For each label `h`, an entry with:
- `targets : list target`, where `targets[i]` says where the inner `h₍ᵢ₎`
  goes, and the head is the innermost variable, so `push_inner` is a cons;
- `out : nat`, the number of output slots for `h`.

A target is one of:
- `Slot h' l`: the `l`-th output slot for `h'`, counted from the innermost
  constructor, so it denotes `h'₍ₖ₋₁₋ₗ₎`, where `k` is `h'`'s slot count;
- `Bind u ρ`: a closed term `u` (opaque) with the adjustment `ρ` applied
  lazily.

The inner `h₍ᵢ₎` with `i ≥ |targets|` pass through to `h₍ᵢ₋|targets|+out₎`.

**Rule: explicit targets only land in slots.** As in the OCaml design, a
contraction with a variable that would otherwise pass through is written by
giving that variable an explicit entry too. So references never point
beyond the slots.

**Payloads.** *(Superseded by D10: payload adjustments are now ordinary
absolute adjustments.)* References inside a payload's `ρ`, to slots of the
top-level adjustment, use the same `Slot` form, counted against the
top-level slot counts. `ρ`'s own pass-through counts, for the named labels of `u`, are
stored as offsets (`Z`) from the top-level counts. `ρ` has no entry for
`None`, since `u` has no bound variables. Consequently `push_outer`, and so
`lift`, changes nothing inside any target or payload.

**Normal form**, for each entry `h`:
- it is stored at its own label's key;
- it is non-trivial;
- every `Slot h' l` anywhere, including inside payloads, has `l < out(h')`;
- *strip condition*: if the last target is `Slot h 0` (the innermost slot
  for `h`), then `Slot h 0` occurs at least once more somewhere else,
  including inside payloads. Otherwise the pair is transparent and is
  stripped.

**Semantics for canonicity.** Lookup returns a variable, or a payload with
its internal references resolved to absolute variables using the top-level
counts. The meaning of a payload depends on the counts, so resolving is part
of the semantics, not a representation layer.

**Why the normal form is canonical.**
- Call an outer `h₍ₘ₎` *pass-through-like* if exactly one inner variable maps
  to it, namely `h₍ₘ₋out₊|targets|₎`, and nothing inside a payload refers to
  it.
- **The tail is pass-through-like.** In a normal adjustment every `h₍ₘ₎`
  with `m ≥ out(h)` is pass-through-like: explicit targets and payload
  references only reach slots.
- **The innermost slot is not.** `h₍out₋₁₎` is not pass-through-like: it is
  either unreferenced, or referenced by something other than a lone last
  target (the strip condition).
- **So the counts are determined by the meaning:** `out(h)` is the least
  `M` such that every `h₍ₘ₎` with `m ≥ M` is pass-through-like, and
  `|targets|` follows from the pass-through offset.
- **And so is the rest:** the targets are the encodings of the lookup
  results under those counts, so two normal adjustments with the same
  meaning are equal entry by entry, and then by trie extensionality.

**Operations:**
- `push_outer h` is `out + 1`, O(log n).
- `push_inner h t` conses, then strips while the strip condition fails.
- Stripping `h`'s innermost slot renumbers the other references to `h`'s
  slots (`l ↦ l − 1`) and adjusts payload offsets for `h`. For `None`, the
  positions index lists exactly those references; named labels are scanned.
- Composition is defined directly on this form.

### D10. Nested payloads and the implemented core (supersedes D9's payload encoding)

Implemented in `Slots.v` (flat core, generic payload type), `Nested.v`
(payloads), `Adjustment.v` (user-facing records) and `Laws.v`.

**Payloads are absolute (option A).** A payload is `(u, ρ)`: `u : T` is the
user's term with no bound variables, opaque to the library, and `ρ` is an
ordinary canonical adjustment into the *outer* scope, with its own slots.
- `nadj T` is the nested inductive `NAdj : tree (entry (T * nadj T))`.
- *Payload-normal*: `ρ` has no `None` input entry, and if it has `None`
  output slots its innermost one is referenced. Payload adjustments are
  canonical for their *restricted* meaning, on free variables only
  (`pcanonical`).
- `restrict h a` (Slots.v) forgets `h` inputs: clear the entry, renormalise,
  then trim unreferenced innermost `h` slots. Payloads of a composite are
  restricted at `None`.
- Cost: named `push_outer` touches every payload (`pshift`, O(log n) each);
  `push_outer None` skips payloads with no `None` slots.

**Total `push_inner` (expansion).** Stripping can remove a slot that a later
`push_inner` wants to target (e.g. after `x₀ ↦ x₀` collapses to the
identity, `y₀ ↦ x₀` needs `x₀`'s slot back). `expand1 h a`, the inverse of
`strip_once`, re-materialises slots without changing meaning, so
`push_inner_var h w a` accepts *any* variable `w`. The representation rule
"explicit targets only land in slots" still holds; the user-facing
constructor has no side condition and no junk case.

**Composition.** `ncompose a b` maps `b`'s payload `(u, ρ)` to
`(u, restrict None (a ∘ ρ))`; recursion is by fuel set to the nesting depth
(`ndepth`), with `compose_ext` (by canonicity) giving fuel independence.
Proved: normality, semantics, identity laws, associativity.

**Raw API** (`Adjustment.v`): `radj T` and `rpadj T` are
records of nested data plus an SProp normality proof, so equality is Leibniz.
`rapply a v : var + (T * rpadj T)`; `rextensionality`; `ridentity`, `rcompose`,
`rpush_outer`, `rpush_inner h (RRename w | RBind u ρ)`, `rlift`; payload
operations `rpcompose`, `rpshift`.

**Laws** (`Laws.v`) need no payload side conditions, because weakening a
payload is composition with `rshift` (`rpshift_as_pcompose`), so
`rpush_outer h a = rcompose (rshift h) a`. Proved: entry commutation,
`rpush_outer_inner`, `rcompose_push_inner_r`, `rcompose_push_outer_l`,
`rcompose_cancel`, `rlift_identity`, `rlift_compose`, `rlift_free`.

**What terms must provide.** Nothing, for the core. Materialising a lookup
result `(u, ρ)` (applying `ρ` to `u`) is the term layer's job: a term-level
`act : radj T → term → term` recursing on terms and, at payloads, on
the strictly smaller nesting depth of `ρ`.

### D11. The indexed layer (Stage 8, as implemented)

Implemented in `Scoped.v` and `Indexed.v`; indices are plain `nat` (the
unindexed `radj` remains available for internal use).

**Naming.** The indexed public forms take the plain names (`adj`, `var`,
`padj`, `target`, `apply`, `identity`, `compose`, `lift`, ...); the raw
(unindexed) forms carry an `r` prefix (`radj`, `rvar`, `rpadj`, `rtarget`,
`rapply`, `ridentity`, `rcompose`, `rlift`, ..., and the raw laws, e.g.
`rcompose_assoc`). The same holds in the λ example (`term N` vs `rterm`).

- **Scoping is a property of adjustments alone**, because payload terms are
  closed. `scoped N M a`:
  - bound inputs `None₍ᵢ₎`, `i ≥ N`, pass through to `None₍ᵢ₋N₊M₎` (a fixed
    tail, so scoped adjustments stay canonical: `scoped_ext`);
  - every other input lands in a variable in scope `M`, or a payload whose
    adjustment has at most `M` bound outputs, recursively (`pscoped M`).
  It is checked on the data (`nscoped_top`) and proved equivalent to that
  meaning (`scoped_spec`, `pscoped_spec`).
- **Public types:** `var M`, `padj T M`, `target T M`, `adj T N M`,
  each a record with an SProp proof. Constructors: `identity`, `compose`,
  `weaken`/`sweaken_free x`, `extend t`/`scons_free x t`,
  `lift`/`slift_free x`, `pcompose`. Laws are inherited from `Laws.v`.
- **Closed adjustments:** `adj T 0 0` can be used at any scope with the same
  data (`at_scope`), and `lift (at_scope a) = at_scope a` (`lift_closed`).
- **Payload terms must be closed.** Substituting a non-variable term that
  mentions bound variables is not supported; open binders first.
- **Example:** `Examples/Lambda.v` builds `tm N` and
  `subst : sub N M → tm N → tm M` (with `sub N M = adj cterm N M`) and
  proves the constructor equations, identity, composition, instantiation
  and open/close laws.

### D12. The normaliser (Stage 9, as implemented)

Implemented in `Normalise.v` (syntax, normal forms, operations, soundness)
and `Names.v` (reification and the `names` tactic); see `design.md` for
the normal form. Decisions:

- **Indexed goals only, reflected through the raw layer.** `names` takes
  goals between indexed adjustments; they become raw goals by `adj_eq`,
  and the raw constructors are reified, so no dependent syntax is needed.
  Slot variables of context forms reach the raw layer as shifted
  variables, which the normaliser resolves with the label order.
- **Words with lifted atoms.** Instead of D3's alternating context
  segments and atoms with entries above the atoms, lifts are pushed onto
  the atoms: `⇑σ ∘ ⇑τ` and `⇑(σ ∘ τ)` both normalise to `⇑σ ∘ ⇑τ`, and the
  binder fragment needs no special treatment.
- **Partial order knowledge fails loudly.** Rather than D3's "leave
  unrelated entries in place", every label comparison must be known, so
  segments are always fully sorted and the tactic fails when an order fact
  is missing. A case split on `label_compare` supplies it.
- **Checks instead of invariants.** Operations check distinctness of
  segment labels (`sdistb`) and verify settling by composing back, so
  soundness needs no well-formedness invariant on normal forms.

Not yet done:
- the uniqueness theorem for normal forms;
- payload adjustments are compared as full words, with only the last
  segment's bound entry forgotten; equal payloads written differently
  under atoms can fail to match;
- `padj` goals and goals about `apply`/terms.

### D13. Context-form notation (as implemented)

In `Indexed.v`; the syntax is described in `design.md`. Decisions:

- **Slots are binders.** In the full form each output entry `a as x` is a
  Rocq binder over everything before it, inputs included. The grammar is
  left-recursive, so the innermost slot ends up deepest in the term;
  `octx_den` builds from the outermost slot in and gives each slot its
  variable in the final scope by probing the slots inside it.
- **Locality by PHOAS, printing first-order.** The notation elaborates the
  same syntax twice: as `forall V W, …` with slots of the abstract type
  `V` and the tail name of `W`, which type-checks only if every slot and
  tail name used is the form's own, and at `V := var M`, which is what
  the form computes and prints. (Rocq cannot print a notation whose term
  binds variables that do not appear in its syntax, so the checking copy
  is ignored by the printing notation.)
- **Tails** are written after `|` in both forms, because a bare name
  after `;` cannot be told from a bare label.
- **Positional entries** pair up innermost first; the numbers of
  positional inputs and outputs are indices, so a mismatch is a type
  error.
- **One input grammar, two forms.** Input entries build overloaded terms
  (type classes `CNil`, `CEnt`, `CBnd`, `CSub`, `CSubB`); after `\` they
  must be a full-form `ictx`, and otherwise the short form's `sctx`, which
  is a case (`OShort`, `OShortT`) of the full form's output context.
- **Payload contexts** `u⟨ … ⟩` say where a term's free names go; the
  default is the output tail, past the slots. They make single context
  forms complete.
- Everything users build is a context form (`lift`, `lift_free` are
  abbreviations); only `⟦⟧`, `∘` and the internal primitive entries are
  direct definitions.
- Labels: `label_lt`/`label_compare` on `label`; the `option label` order
  is internal (`olabel_lt`). Variables print with superscript indices.

### D14. `names` normalises (as implemented)

`names` rewrites adjustments in the goal to normal forms shown as context
forms, and reduces `apply_var` where the normal form gives the result; it
never closes a goal. Display is computed in Gallina (expansion so every
target is a slot, positional entries where the order allows, merging a
segment with the following lifted atom into a tailed form, short forms)
and rendered by refinement in Ltac; each rewrite is proved by deciding
the equation, so the display code needs no proof.

Not yet done: uniqueness of normal forms; `apply_var` only reduces when
the normal form is a single context form and the result is a variable;
payloads whose adjustment contains atoms are not displayed.

### D6. Users see only the indexed form

Scoped terms and adjustments (indexed by the number of bound names), built as
the unindexed core plus SProp well-scopedness proofs, are the only thing in
the public API. The unindexed core is an implementation device for our proofs.
Consequences:

- Every public lemma is stated on indexed types.
- The normaliser tactic works on indexed goals and goes through the core
  internally.
- Printing shows indexed objects in context form.
- Stages 5–7 build internal theory; Stage 8 builds the public surface.

---

## Stages

Each stage has a deliverable and an exit criterion. Stages 0–4 are the first
milestone. Together they discharge the whole TODO list on `adjustments`
(428f1a4).

### Stage 0: environment and skeleton

- The Rocq toolchain is set up; see [Environment](#environment).
- Build files, `theories/` layout (separate `Core/` (internal) and public
  directories from the start), CI building on push, and a `README` stating the
  goal and pointing at the docs.

**Exit:** the build of an empty `theories/` succeeds locally and in CI.

### Stage 1: canonical maps (`theories/Core/Trie.v`)

- Our own Appel–Leroy trie per D2, with the core lemmas: gss, gso, gempty,
  `combine`, `map_filter`, `extensionality`, and `fold`/`elements` with their
  specs.
- Key encodings: `positive` ↔ `option label` (injective, with a decoder or at
  least `enc_inj`).
- Tests: `Example`s by `vm_compute` / `reflexivity`.

**Exit:** `extensionality` is proved, and an `Example` with a few thousand
entries evaluates quickly under `vm_compute`.

### Stage 2: labels and variables (`theories/Core/Label.v`, `Var.v`)

- **Labels:** a decidable strict total order `<` that computes on concrete
  labels, with its order lemmas. It is the vocabulary for all symbolic side
  conditions (D3). `Label.v` from `adjustments` is the starting point.
- **Variables:** port `var := {v_label_opt; v_nat}`, `shift_var`/`unshift_var`
  and push/pop from `adjustments`/`next-unindexed`. Port only the
  `VarEquations.v` lemmas we need, restating `≠` side conditions with `<` where
  that is the natural form.

**Exit:** the ported var lemmas are proved, with a `case_labels` tactic that
splits on `<`/`=`/`>`.

### Stage 3: raw adjustments, computationally (`theories/Core/RawAdjustment.v`)

- The raw data per D1, with payload type `P` (instantiated to `Empty_set` for
  now).
- Functions:
  - `wf : raw P → bool` (targets in range);
  - `apply : raw P → var → var + P`;
  - `normalize`;
  - `compose`, following OCaml 4ae82a85 `Simplified.compose`: lookup through
    the outer adjustment, append leftovers, then normalise;
  - `identity`;
  - smart constructors for the primitive operations (open, close, shift,
    rename, swap, weaken, and bound-variable variants).
- Executable tests that compose concrete adjustments and compare the results
  with `reflexivity`.

**Exit:** all functions are defined and computing, and the tests pass.

### Stage 4: canonicity and the core type (`theories/Core/Adjustment.v`)

- Write a **paper proof of canonicity first** (design history §7.3), then
  formalise it.
- Lemmas:
  - `apply_normalize`;
  - `normalize_normal`;
  - `apply_compose` (pointwise);
  - **canonicity**: `normal a → normal b → (∀ v, apply a v = apply b v) → a = b`.
- The type: `Record adjustment P := { raw : raw P; normal : is_normal raw }`,
  where `is_normal` is SProp-valued.
- Identity and associativity follow by canonicity.

**Exit:** the identity and associativity laws, and `apply_compose`, are proved
with `=`. This is the first milestone.

### Stage 5: context-form constructors (`theories/Core/Adjustment.v`)

- Users see adjustments only through three **constructors**, all implemented
  as functions on the trie form:
  - `identity`, the empty context form with the identity tail;
  - `push_inner h t a`, which adds an input entry `h ↦ t` in front;
  - `push_outer h a`, which adds an output entry `h` in front.

  Any adjustment, in particular a variable, can be the tail. Lifting under a
  binder is `push_inner l l₍₀₎ (push_outer l σ)`.
- **The equational laws of the constructors**, stated with `=`. These are the
  rules the normaliser implements:
  - adjacent entries of different labels commute, stated with `<`;
  - `push_outer` moves inside `push_inner` (shifting the target);
  - composition cancels an output entry against an input entry;
  - composition distributes over the constructors;
  - transparent entries vanish.
- Notations and printing for the constructors, so goals read as contexts.
  Modelled on the OCaml `outer`/`inner` lists.
- The concrete context-form datatype (`CForm.v`) is **not** user-facing: it
  is the target syntax of the normaliser (Stage 9). The concrete-label
  version, with conversions to and from tries, is its first piece.

**Exit:** the constructor laws are proved, and goals built from constructors
print as contexts.

### Stage 6: the equational theory of renamings (internal)

- Express open, close, shift, rename, swap and weaken as adjustments, and
  state the classic laws from `master`'s `Var.v` and `Relative.v` (the
  `rw_ren_*` family, `swap_*`) as Leibniz equations with `<` side conditions.
  Most become `canonicity + case analysis`.
- A hint database and a provisional `simpl_adjustments` tactic. It is a
  stopgap until the normaliser exists.

**Exit:** the renaming fragment of `master`'s lemma set is reproved, with no
setoids.

### Stage 7: substitutions and terms (internal)

*Revised:* the core assumes only the payload action of D7. The λ-calculus in
`theories/Examples/` is a test instance, not part of the library. The
Relative.v-style convenience layer comes last.

- Fix the internal term interface:
  - unindexed syntax with binders;
  - variables are `var`;
  - `subst : adjustment term → term → term` with relative-monad-like laws.

  `Relative.v` on `master` and `Term.v` on `next` are the prior art. Start with
  a concrete λ-calculus, then generalise.
- Composition for `Bind` payloads: `compose a b` must apply `a` to `b`'s
  payloads (design history §7.4 item 5). Redo Stage 4's laws for
  substitutions.
- Term-level operations `[σ] t`, `open x t`, `close x t` and bind, with the
  Leibniz versions of `master`'s term lemmas and `next`'s
  `combine_open_renaming_close` family.

### Stage 8: the indexed public layer

- SProp well-scopedness predicates on vars, terms and adjustments. Scoped
  types such as `term N` (primitive-projection records of core data plus SProp
  proof), so that equality stays Leibniz.
- Show that every operation preserves scoping, and give the public API
  (`open : term (S N) → term N`, `[σ] : term N → term M`, …) with all lemmas
  restated on indexed types.
- Fix the encapsulation mechanism (ground rules) and audit that nothing
  unindexed is reachable from the public modules.

**Exit:** the Stage 6 and 7 lemma sets are available in indexed form, and a
client file that imports only public modules can state and prove them.

### Stage 9: the reflective normaliser

*Status:* soundness and the `names` tactic are done (D12); uniqueness and
the items listed under D12 remain.

- **Reification** of indexed goal expressions (adjustments, compositions,
  lifts, term operations) into a syntax with label atoms, **adjustment atoms**,
  and the `<` facts found in the context.
- **Normalisation** in context form (D3): compute compositions by cancelling
  output contexts against input contexts, reorder only under known `<`, drop
  transparent entries, and keep uncancellable parts as words around
  adjustment atoms.
- The binder fragment (`⇑ⁿσ`, with `⇑σ ∘ ⇑τ = ⇑(σ ∘ τ)` and friends) is the
  first milestone. The proofs in Stages 7–10 rely on it most.
- **Soundness:** `denote (normalize e) = denote e`.
- **Uniqueness of normal forms**, as stated in D3. This is the target theorem.
- **Tactic:** a `names` tactic for users that reifies, normalises both sides
  and closes or simplifies the goal, reporting missing `<` facts it would have
  needed.
- Measure it against `master`'s `autorewrite`-based tactic on the same
  examples.

### Stage 10: contexts and the client

- Typing contexts per D5: list-like constructors (empty, `Γ & x ~ A`) over a
  per-label trie, with lookup by shifted name, extensional equality, and
  context morphisms `Γ =[σ]=> Δ` on the indexed layer. Port the lemmas of
  `master`'s `Context.v`.
- Port `examples/Lambda.v`: STLC with universal `LAM`, weakening, substitution,
  Barendregt's lemma and CPS type preservation, using only public modules.
  **This is the acceptance test.**
- Port the TyDE examples, and compare proof size and run time with `master`.

### Stage 11: write-up

- Update the docs, clean up old `src/`, and possibly a paper or talk following
  the 2019 TyDE one.

---

## Risks and open questions

- **Uniqueness of context-form normal forms (D3)** under partial order
  knowledge is the main theoretical risk. Prove it first in the concrete case
  (Stage 5), then generalise (Stage 9). If it fails, soundness plus a useful
  normal-ish form is the fallback.
- **Normal forms with adjustment atoms.** Uniqueness for words of segments and
  atoms is harder than for a single context. Get the binder fragment fully
  right first.
- **Asymptotics of extracted code (D4):** lifting and index lookup with
  per-label lists are linear. Revisit the per-label entry representation
  before anyone builds a real program on the library.
- **Canonicity might need extra conditions** that the OCaml code never needed,
  because it never proved anything. The paper proof in Stage 4 resolves this
  early.
- **The term interface (Stage 7):** whether to go generic too early or stay
  concrete. Prefer concrete first.
- **Leakage:** keeping the unindexed core fully hidden while letting the
  normaliser and printing work on indexed goals may need care with reduction
  behaviour (opaque vs transparent definitions under `vm_compute`).

## What to reuse from the old branches

| Need | Source |
|---|---|
| `var`, labels, label order, push/pop | `adjustments`: `src/Var.v`, `src/Label.v`; `next-unindexed`: `src/Var.v` |
| Case-split and reduction tactics on vars | `next-unindexed`: `src/VarEquations.v` (`case_vars`, `reduce_*`) |
| SProp-normalised record pattern, canonicity proof style | `next-unindexed`: `src/Renaming.v` (`is_normalized_equivalence_equal`), `src/ClosingEquations.v` |
| Composition and normalisation algorithms | `lpw25/ocaml` 4ae82a85: `typing/effect.ml`, `Adjustment.Simplified` |
| Context-form syntax (outer/inner) | `lpw25/ocaml` tip: `typing/effect.mli`, `Adjustment.parse`, `Adjustment.Desc` |
| Trie reference implementation (reading only) | CompCert `lib/Maps.v`, `PTree` |
| Lemma statements to reprove | `master`: `src/Var.v`, `src/Relative.v`, `TyDE-2019/Names.v` |
| Term interface | `master`: `src/Relative.v`; `next`: `src/Term.v` |
| Client and acceptance test | `master`: `examples/Lambda.v`, `src/Context.v` |

## Environment

**Toolchain:** Rocq 9.2.0 with stdlib 9.2.0, OCaml 4.14.1 and dune 3.14. The
native compiler is disabled (`vm_compute` works; `native_compute` falls back
to the VM).

**Cloud sessions** (claude.ai/code). Use the personal environment
`shifted-names`. Its setup script runs whenever a fresh container is built. It
installs Ubuntu's `ocaml-nox`, `ocaml-dune`, `libzarith-ocaml-dev` and
`ocaml-findlib`, then builds Rocq and the stdlib from the `V9.2.0` tags of
`github.com/rocq-prover/rocq` and `github.com/rocq-prover/stdlib`, installing
into `/usr/local`. This takes about 4 minutes. opam is not used because
`opam.ocaml.org` and GitHub release tarballs are not reachable from the cloud
network policy, but `git clone` from GitHub is.

**Locally:**

```bash
opam install rocq-prover.9.2.0
```

`rocq-prover` pulls in the matching stdlib.

**Quick check:**

```bash
rocq c -R src SNames src/Label.v
```

The old sources compile with deprecation warnings (`Require Import String` →
`From Stdlib Require Import String`). New code should use `From Stdlib`.
