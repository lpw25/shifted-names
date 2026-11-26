# Several sorts of variable (design)

A design for syntaxes with any number of sorts of variable (types and terms
in System F, regions, values and computations, …), checked on System F in
`proto/sorts/Desc.v` (standalone; `rocq compile -R theories ShiftedNames
proto/sorts/Desc.v`). Nothing in the library uses it yet.

## What the user writes

Their own curried families, with plain constructors, one Kleisli function
per family and sort, and the laws (routine inductions). For System F:

```coq
Inductive ty (N : nat) := tyvar (v : var N) | tyarr (A B : ty N) | tyall (B : ty (S N)).
Inductive tm (N K : nat) := tmvar (v : var K) | lam (A : ty N) (b : tm N (S K))
                          | app (t u : tm N K) | tlam (b : tm (S N) K) | tapp (t : tm N K) (A : ty N).

Definition ty_in_tm : thin 1 2 := tkeep (tskip tdone).   (* types are sort 0 of terms *)

Fixpoint kl_tm f {O Ki Li} (e : vext 2 1 Bo Bi Mi O Ki Li) (t : tm (first O) Ki) : tm (first O) Li :=
  match t with
  | tmvar v => f O Ki Li e v
  | lam A u => lam A (kl_tm f (vunder e) u)          (* annotation untouched *)
  | app t u => app (kl_tm f e t) (kl_tm f e u)
  | tlam u => tlam (kl_tm f (vother 0 e) u)
  | tapp t A => tapp (kl_tm f e t) A
  end.
```

with `kl_ty` (types, the type sort) and `kl_tmty` (terms, the type sort: a
witness over the types' sort, the term scope an ordinary argument) alike.

## The interface

**Scopes.** `vec n` is `n` scopes (pairs with primitive projections, so
with eta); `get n i` and `upd n i k` read and replace sort `i`'s. The
library sees a curried family `F` through a vector by `uncurry n F`,
computed by recursion on `n`, so the user writes no view and the classes
can be indexed by the family itself.

**A family inside another** is over a thinning of its sorts, `thin m n`
(keep or skip each of the `n`); `merge th x r` puts the larger vector
together from the smaller one and the scopes of the sorts skipped.

**The descent witness.** Substituting sort `i`, the binders gone under are
one value

```coq
Inductive vext (n i : nat) (Bo : vec n) (Bi Mi : nat) : vec n -> nat -> nat -> Type :=
| vhere : vext n i Bo Bi Mi Bo Bi Mi
| vunder {O Ki Li} : vext n i Bo Bi Mi O Ki Li -> vext n i Bo Bi Mi O (S Ki) (S Li)
| vother (t : nat) {O Ki Li} : vext n i Bo Bi Mi O Ki Li -> vext n i Bo Bi Mi (upd n t (S (get n t O)) O) Ki Li.
```

`O` holds the other sorts' scopes, `Ki` and `Li` sort `i`'s input and
output. The family goes from `upd n i Ki O` to `upd n i Li O`: the other
sorts are visibly the same on both sides, so a Kleisli function never
visits what only contains them. `vother i` only changes `O`'s component
`i`, which is not used, so it needs no side condition. With one sort this
is `ext`.

Composing (`vapp`) and splitting through a middle scope (`vmid`, `vleft`,
`vright`) are plain recursions, with no casts: the two sides share `O`.

**Morphisms and Kleisli functions:**

```coq
morph n i P Bo Bi Mi := forall O Ki Li, vext n i Bo Bi Mi O Ki Li -> var Ki -> P (upd n i Li O)
sort_kl n i P := … f … (e : vext n i Bo Bi Mi O Ki Li), P (upd n i Ki O) -> P (upd n i Li O)
fam_kl n i P th T := … f … e (r : vec (skips th)),
  T (merge th (upd n i Ki O) r) -> T (merge th (upd n i Li O) r)
```

**Laws,** per family and sort: `var`, `ext`, `rebase` (along `vapp`),
`unit` and `assoc` (along `vleft`, `vright`), as for one sort. For System
F all of them are routine inductions (`ty_laws`, `tm_laws`, `tmty_laws`).

## One sort at a time: slices (`proto/sorts/Slice.v`)

With the other sorts' scopes fixed at `Bo`, sort `i` is a one-sorted syntax
of the library, on `fun K => P (upd n i K Bo)`: its Kleisli function is the
user's along the morphism *lifted* to the new witnesses, whose results are
weakened along the other sorts' binders crossed (`wk`, one `step` per
binder). So the library's `apply`, `Subst` and `names` apply unchanged.
`slice_laws` proves the library's laws from the user's, given two
hypotheses: a step keeps sort `i`'s variables (`step_var`), and weakening
commutes with the Kleisli function of a lifted morphism (`wk_kl`).

For System F (`proto/sorts/SliceF.v`): the step past a type binder shifts
the term's types (`shN 1`, by `kl_tmty`), past a term binder nothing.
`wk_kl`, the node lemma for `tlam` (substitution under a type binder is the
next slice's, along the morphism mapped by `shN 1`) and `shN 1` being a map
of syntaxes (`SyntaxMap`, for `pmap`) all come from one lemma: renaming
types by a shift commutes with substituting terms (`kl_commute`).
`proto/sorts/SliceFTest.v` registers the instances and checks `names` on
term substitution, under type binders included (`(tlam b) [a] = tlam (b
[pmap tsh a])`), as in `theories/Examples/SystemF.v`.

## Still to do

1. `kl_commute` and its renaming lemmas are System F's own (about 150
   lines). They are an instance of two generic laws: moving a Kleisli
   function of one sort past one of another (one law per pair of sorts,
   proved by the user by a routine induction), and a Kleisli function
   depending on its witness only through the morphism (naturality). With
   those, `wk_kl`, the node lemmas for binders of other sorts and the
   `SyntaxMap` instances would be derived generically.
2. Node lemmas: the slice's Kleisli function does not compute to the
   library's shape (`cbn` exposes the multi-sorted one), so the examples
   rewrite with node lemmas (`kleisli_tlam`, …) before `names`.
3. Weakening along several binders is done one step per binder; it could
   be batched.
4. The notation `t [a]` per sort, and moving a substitution of one sort
   past one of another in `names`.
