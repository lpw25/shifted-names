# A syntax as classes

A syntax gives the library (`Core/Syntax.v`):

- **`Kleisli P T`**: the Kleisli extension of a family `T` along morphisms
  into `P` (maps from variables to `P`-terms), going under binders with a
  witness `ext N M K L`;
- **`Syntax P`**: for the family `P` that has the variables, its variable
  constructor and the laws of its Kleisli extension;
- **`Family P T`**: for another family `T` over `P` (computations over
  values, terms over types, …), the laws of its Kleisli extension.

`Core/Subst.v` gives substitution for any `Syntax`, and `names` works on
it. A syntax declares its instances, and declares them canonical too:

```coq
#[export] Instance lambda_kleisli : Kleisli tm tm := {| Syntax.kleisli := @LambdaSyntax.kleisli |}.
#[export] Instance lambda_syntax : Syntax tm := {| Syntax.tvar := @tvar; … |}.
Canonical Structure lambda_kleisli.
Canonical Structure lambda_syntax.
```

## A second substitution

A family with its own `Kleisli` and `Family` instances over a syntax `P`
has `P`'s substitution: the library's `fam_law` is its law, and `names`
normalises it. System F (`Examples/SystemF.v`) has types `ty N` and
terms `tm N K`, with `N` type variables and `K` term variables; types
are a syntax, and terms are a family over types in their first scope,
one instance for each term scope `J`:

```coq
#[export] Instance tm_ty_kleisli J : Kleisli ty (fun K => tm K J) := {| Syntax.kleisli := @TmTy.tkleisli J |}.
#[export] Instance tm_ty_family J : Family ty (fun K => tm K J) := {| … |}.
Canonical Structure tm_ty_kleisli.
```

Written as the class's `kleisli`, the substitution `t [a]` of a term by
types would not elaborate: unification solves `T ?N` against `tm N K`
with `T := tm N`, the last index. The library's `kl_at` is the same
substitution, typed on `F N b` instead, for a type with two scopes
substituted in its first, and `t {{ a }}` is its notation:

```coq
Example tsub_fuse {N M P K} (a : tsub M P) (b : tsub N M) (t : tm N K) :
  t {{ b }} {{ a }} = t {{ b ⨾ a }}.
Proof. names; reflexivity. Qed.
```

`names` knows only the classes, not `kl_at`: `Subst.v` unfolds it,
and writes the family's substitutions back with it. For a family of
another shape (a third scope, or the substituted scope second), a user
defines their own version of `kl_at` and its notation the same way.

Term substitution in System F's terms needs one more thing: going under a
type binder, a substitution's payload terms are shifted in their type
scope, a map over payloads (next step).

## Why classes, and why canonical too

The families are parameters of the classes, not fields of a structure:

- **Types stay the user's own.** What the library computes has type
  `tm N`, not a structure's projection applied to the syntax, so a name
  for closed terms is a plain abbreviation, `Notation trm := (tm 0)`, and
  everything prints with it.
- **A family can have several substitutions**, one per family of what is
  substituted (term and type substitution over System F's terms). A
  canonical structure keeps one record per type; instance resolution finds
  an instance from both families.

Instance resolution finds the instances when a statement is elaborated.
It does not when `rewrite` or `apply` match a library lemma against a
goal: their instance arguments are still holes then, and unification
cannot see through a class's projection (`tvar`, `kleisli`) to the
syntax's own constructor or function while the instance is unknown.
Declaring the instances canonical fixes this: unification finds them from
the syntax's constructor (`tvar`) and Kleisli function (what `cbn`
leaves), keyed on those, which are distinct for each substitution.

Earlier versions: a module functor (lemmas stated per syntax, a rewrite
database for `names`), then a single canonical structure with the term
family as a field (types printed through the structure, one substitution
per type).

## What it costs the rest of a development

- **Inference**: one instance lookup when a statement mentioning
  substitution is elaborated, a canonical lookup when a lemma is matched
  against the syntax's own terms. The proof terms hold the instances as
  ordinary constants.
- **`cbn`** gives the same goals as before: it unfolds the instance and
  leaves the syntax's own Kleisli function and constructors.
- **The examples' proofs** are unchanged.
- **Aliases** (`Definition trm := tm 0`) work: unification unfolds them.

## What it gives `names`

`names` reads the syntax's law from the instances in the goal, so it
needs no rewrite database for nodes: step 0 writes the syntax's own
Kleisli function as the class's (one `change` per syntax, the syntaxes
found from the uses of `apply`), and step 2 is `change` (`t [a]` is the
node by conversion). See `docs/names.md`.

## Timings

On the same machine, in one session, against the single canonical
structure it replaces (compile time; `names` as tactic + `Qed`):

| | canonical structure | classes |
|---|---|---|
| `Subst.v` (the library itself) | 3.7 s | 4.4 s |
| `Lambda.v` | 2.3 s | 2.1 s |
| `STLC.v` | 1.2 s | 1.2 s |
| `NamesTests.v` | 2.1 s | 1.9 s |
| SN 100 | 0.91 + 0.18 s | 0.85 + 0.18 s |
| MO 20 | 1.65 + 0.11 s | 1.66 + 0.09 s |
| MV 20 | 2.26 + 0.44 s | 1.96 + 0.29 s |
| NS 60 | 0.92 + 1.9 s | 0.69 + 1.3 s |
| VT 300 | 1.48 + 0.55 s | 1.73 + 0.41 s |

Only the library's own file is slower to compile (elaborating it over
instances); users' files and `names` are the same within noise.
