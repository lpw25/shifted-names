# Prototype: a syntax as a type class

This branch replaces the `Subst` functor with a class. A syntax is an
instance of `Syntax term` (`Syntax.v`): the variable constructor, the
Kleisli extension and its laws, the functor's former inputs. Everything
in `Subst.v` is generic over the instance (sections instead of a functor
body). A syntax declares the instance, and the same record as a canonical
structure:

```coq
#[export] Instance lambda_syntax : Syntax tm := {| … |}.
Canonical Structure lambda_syntax.
```

## What it costs the rest of a development

- **Instance resolution** happens when a term is elaborated (a statement,
  a tactic's argument). With one class and one instance per syntax it is
  one lookup. The proof terms hold the instance as an ordinary constant;
  nothing searches again, and the kernel never does.
- **Compile times** of the example and test files are unchanged (within
  noise): `Subst.v` 3.2 → 3.3 s, `Lambda.v` 1.8 → 1.6 s, `STLC.v` 1.1 →
  0.9 s, `CoreTests.v` 0.9 → 0.9 s, `NamesTests.v` 1.7 → 1.9 s (the last
  is `names` itself; see below).
- **`cbn`** gives exactly the same goals: it unfolds the instance and
  leaves the syntax's own `kleisli` and constructors, as with the functor.
- **The library's lemmas** are stated with the class's projections
  (`tvar`, `kleisli`). The goals have the syntax's own constructor (written
  by the user) or `kleisli` (left by `cbn`). Unification cannot see through
  a projection of an instance it does not yet know, so with the instance
  only, `rewrite subst_tvar_eval` and `apply subst_tvar_rename` failed on
  such goals (three places in the examples). Declaring the instance as a
  canonical structure fixes this: unification then finds the instance
  from the constructor or constant it is matched against. With it, every
  proof in the examples is as before.

## What it gives `names`

`names` finds the syntax's law from the instance in the goal, so it no
longer needs the hint database to turn substitutions into nodes:

- step 0 (new) writes the syntax's own `kleisli` as the class's
  (`syntax_fold`: the instances in the goal, from the uses of `apply`,
  and one `change` per syntax);
- step 2 is `change`: `t [a]` is the node by conversion, and so is what
  `cbn` leaves of a substitution into a variable when the syntax's
  `kleisli` computes on variables (otherwise the lemma `apply_here_node`
  rewrites it, as before). A chain `t [a] [b] …` is converted at once.

| family | functor | class |
|---|---|---|
| SN 100 | 3.2 + 0.82 s | 0.60 + 0.15 s |
| SN 200 | about 14 s | 1.4 + 0.36 s |
| MO 20 | 3.2 + 0.33 s | 1.3 + 0.06 s |
| MV 20 | 3.6 + 0.47 s | 1.4 + 0.23 s |
| NS 60 | 1.6 + 1.2 s | 0.57 + 1.0 s |
| VR 300 | 1.2 + 0.15 s | 0.72 + 0.10 s |
| VT 300 | 1.6 + 0.41 s | 1.2 + 0.44 s |
| VA 300 | 1.5 + 0.45 s | 1.3 + 0.48 s |
| PN 60, PC 50, D 1000 | | unchanged |

What remains of SN, MO and MV is mostly normalising, and on MV `names_pre`
(the lifting rewrites, still `autorewrite`; moving them into reification
is the next step this enables). Each `names` call pays a few milliseconds
for steps 0 and 2 on goals with no substitution (NamesTests).

## Not done in the prototype

- `csubst` is still the node `names` works on internally; steps 0 and 2
  and step 5 convert to and from it by `change`, with no proof.
- The `names_pre` rewrites (lifting under binders) are still
  `autorewrite`.
- The docs elsewhere still describe the functor.
