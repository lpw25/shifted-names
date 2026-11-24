# A syntax as a canonical structure

A syntax is a structure `syntax` (`Core/Syntax.v`): its term family, the
variable constructor, the Kleisli extension and its laws. It used to be
the input of a functor, `Subst`; now `Core/Subst.v` is generic over any
`syntax`, and a syntax declares its structure canonical:

```coq
Canonical Structure lambda_syntax : syntax := {|
  Syntax.term := tm; Syntax.tvar := @tvar; Syntax.kleisli := @LambdaSyntax.kleisli; … |}.
```

The term family is a field, so this is the usual canonical-structure use:
elaborating `t [a]` with `t : tm N` unifies the structure's `term ?S N`
with `tm N`, and unification finds `?S` in the table of canonical
structures. The same happens when a library lemma, stated with the
structure's `tvar` or `kleisli`, is used with `rewrite` or `apply` on a
goal with the syntax's own constructor, or its own `kleisli` (what `cbn`
leaves): unification finds the structure from that constructor or
constant.

## Why not a type class

A first prototype made the syntax a class, with the term family as its
parameter. Instance resolution then found the instance for statements,
but `rewrite subst_tvar_eval` and `apply subst_tvar_rename` failed on
goals written with the constructor: unification cannot see through a
projection of an instance it does not yet know, and instance resolution
runs only after. Declaring the instance canonical as well fixed that; with
the term family a field, the canonical structure alone is enough, and
there is no proof search at all.

## What it costs the rest of a development

- **Inference** is a table lookup during unification, when the
  structure's projection meets the syntax's terms. The proof terms hold
  the structure as an ordinary constant; nothing searches.
- **Compile times** of the example and test files, with the functor and
  now (two runs each, about 10% noise): `Subst.v` 3.2 → 3.5 s, `Lambda.v`
  1.8 → 1.9 s, `STLC.v` 1.1 → 1.0 s, `CoreTests.v` 0.9 → 0.9 s,
  `NamesTests.v` 1.7 → 1.8 s. Each `names` call pays a few milliseconds for
  the folding step and for recording universe constraints.
- **`cbn`** gives exactly the same goals as with the functor: it unfolds
  the structure and leaves the syntax's own `kleisli` and constructors.
- **The examples' proofs** are unchanged (Lambda's syntax module is now
  plain, and its last line declares the structure).
- **Display**: a type computed by the library may print through the
  structure, e.g. `lambda_syntax M` for `tm M`.
- **Aliases** work: where the structure is looked up at an alias and not
  found, unification unfolds the alias and finds it at the syntax's type.
  So `Definition trm := tm 0` (closed terms, `Lambda.v`) or
  `Definition tmf := tm` can be used everywhere `tm` can, with `apply`,
  `rewrite`, `cbn` and `names`. Only an alias unification cannot unfold
  (opaque, or a new type wrapping the syntax's) needs its own canonical
  structure.
- **Inside the library**, statements and proofs over a generic structure
  fix it with local notations (`kleisli := kleisli (s:=Sy)`, and so on):
  unification has nothing to find it from where an argument's type is not
  yet known.

## What it gives `names`

`names` reads the syntax's law from the structure in the goal, so it no
longer needs a rewrite database for nodes:

- step 0 writes the syntax's own `kleisli` as the structure's
  (`syntax_fold`: the structures in the goal, from the uses of `apply`,
  and one `change` each);
- step 2 is `change`: `t [a]` is the node by conversion, and so is what
  `cbn` leaves of a substitution into a variable when the syntax's
  `kleisli` computes on variables (otherwise the lemma `apply_here_node`
  rewrites it). A chain `t [a] [b] …` is converted at once.

| family | functor | canonical structure |
|---|---|---|
| SN 100 | 3.2 + 0.82 s | 0.68 + 0.18 s |
| SN 200 | about 14 s | 2.0 + 0.34 s |
| MO 20 | 3.2 + 0.33 s | 1.3 + 0.06 s |
| MV 20 | 3.6 + 0.47 s | 1.4 + 0.36 s |
| NS 60 | 1.6 + 1.2 s | 0.69 + 1.2 s |
| VR 300 | 1.2 + 0.15 s | 1.0 + 0.12 s |
| VT 300 | 1.6 + 0.41 s | 1.4 + 0.45 s |
| VA 300 | 1.5 + 0.45 s | 1.3 + 0.51 s |
| PN 60, PC 50, D 1000 | | within noise |

## Still to do

- The lifting rewrites of step 1 (`names_pre`) are `autorewrite`; with the
  law and the syntax's `kleisli` known from the structure, they can move
  into reification. On MV they are now the largest step after
  normalising.
- `csubst` is still the node `names` works on internally; steps 0, 2 and
  5 reach it and leave it by `change`, with no proof.
