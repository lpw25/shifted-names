# Several sorts of variable (design)

A design for syntaxes with any number of sorts of variable (types and terms
in System F, regions, values and computations, …), checked on System F in
`proto/sorts/Focus.v` (`rocq compile -R theories ShiftedNames -Q proto/sorts
Proto proto/sorts/Focus.v`). Nothing in the library uses it yet.

## What the user writes

Their own curried families, with plain constructors, one Kleisli function
per family and sort, and the laws (routine inductions). Sorts are counted
from the left (System F: types 0, terms 1). For terms, substituting term
variables:

```coq
Fixpoint kl_tm {B M} (f : morph 1 0 (uncurry 2 tm) B M) {K L} (x : descent 1 0 B M K L)
    (t : tm @ K) : tm @ out K L :=
  match t with
  | tmvar v => f K L x v
  | lam A u => lam A (kl_tm f (under 1 x) u)     (* annotation untouched *)
  | app t u => app (kl_tm f x t) (kl_tm f x u)
  | tlam u => tlam (kl_tm f (under 0 x) u)
  | tapp t A => tapp (kl_tm f x t) A
  end.
```

and for terms substituting type variables, where the types inside are a
family over fewer sorts:

```coq
Fixpoint kl_tmty {B M : scopes 0 1} (f : morph 0 0 (uncurry 1 ty) _ _) {K L} (x : descent 0 1 B M K L)
    (t : tm @ K) : tm @ out K L :=
  match t with
  | tmvar v => tmvar v
  | lam A u => lam (kl_ty f x‹+ -› A) (kl_tmty f (under 1 x) u)
  | app t u => app (kl_tmty f x t) (kl_tmty f x u)
  | tlam u => tlam (kl_tmty f (under 0 x) u)
  | tapp t A => tapp (kl_tmty f x t) (kl_ty f x‹+ -› A)
  end.
```

`x‹+ -›` is the witness for the types inside: of the terms' sorts in order,
keep the first and skip the second. `f`'s bases are left for Coq to infer
from that use (they print as `B‹+-›`, `M‹+-›`).

The helpers, all of which compute away since the sorts are concrete:

* `F @ K`: the family `F` at the zipper of scopes `K`;
* `out K L`: the zipper `K` with `L`'s focus (the output of a
  substitution);
* `under t x`: the witness under a binder of sort `t`, whichever sort is
  focused;
* `x‹+ - …›`: the witness for a family inside another, saying which of the
  sorts, in order, it has, whichever sort is focused (split at the focus,
  the left part nearest first, by computation);
* `here`: the witness at the root (`kl_tm f here t`).

## A substitution is focused on its sort

A family over `n` sorts is seen through a vector of scopes (`uncurry`).
Substituting sort `i`, the scopes are a *zipper* (`scopes a b`): the `a` sorts
to the left of `i` (nearest first), `i`'s scope (the focus), and the `b`
sorts to the right; the family is at the zipper plugged back (`plug`,
putting the left part back onto the right one sort at a time).

The witness is a zipper of `ext`s (`descent a b B M K L`): the focus's input
and output scopes, and for each other sort its scope and the one on the
other side of a substitution of it. A Kleisli function goes from `K` to
`out K L`, `K` with the focus's output scope: the other sorts are the same
on both sides, so nothing containing only them is visited.

The focus is at a fixed place in the zipper, read by a projection, so
nothing is cut out of a vector or put back, and there are no casts:

* composing witnesses (rebase) is componentwise; splitting through a
  middle scope (assoc) is on the focus alone;
* a family inside another is focused on the same sort, over thinnings of
  each side; its morphism sees its part of the witness, componentwise;
* the order of binders of different sorts is not recorded, so it needs no
  law;
* moving the focus one sort along leaves the plugged vector the same by
  computation (`plug_right1`, `reflexivity` for any number of sorts).

## Morphisms, Kleisli functions, laws

```coq
morph a b P B M := forall K L, descent a b B M K L -> var (focus K) -> P (plug (out K L))
sort_kl a b P := … (f : morph a b P B M) … (x : descent a b B M K L), P (plug K) -> P (plug (out K L))
fam_kl a b P tl tr T := … (f : morph a b P (zrestr tl tr B) (zrestr tl tr M)) … (x : descent aT bT B M K L),
  T (plug K) -> T (plug (out K L))
```

Laws, per family and sort: `var`, `ext`, `rebase`, `unit`, `assoc`; all
routine inductions for System F (`ty_laws`, `tm_laws`, `tmty_laws`).

## Moving a substitution of one sort past one of another (`proto/sorts/Commute.v`)

Two sorts `i` left of `j` are two foci at once: a zipper with two holes
(`scopes2 a c d`: the `a` sorts left of `i`, `i`, the `c` sorts between, `j`,
the `d` sorts right of `j`). Seen from either hole it is a one-hole zipper
(`zi`, `zj`), and a two-hole zipper of `ext`s is a witness for either sort
(`wi`, `wj`); each substitution sees the other's `ext` read from the side it
is on (`flipx`, `flipy`). All of these are plain functions.

The two views plug to the same vector by computation only for a concrete
number of sorts between (for an abstract `c` even the vectors' lengths
differ as expressions), so the class is stated on the two-hole zipper
itself: both substitutions act on the family there (`T2`), and nothing
relates the views. The morphism of `j`'s sort mapped by a substitution of
`i`'s (`tmap`) is defined once, from the class:

```coq
Record commute kx ky := {
  move : forall B M h f K L (X : descent2 B M K L) t,
    kx _ _ h _ _ (flipy X) (ky _ _ f _ _ X t) = ky _ _ (tmap kx h f) _ _ (flipx X) (kx _ _ h _ _ X t) }.
```

The user registers their own two Kleisli functions, naming the two sorts
(sorts 0 and 1 of 2), and the law's proof is a library tactic (recursion on
the term; at a variable the views are unfolded, under a binder the witness
goes under):

```coq
Definition tm_types_terms := register 2 0 1 (uncurry 2 tm) (@kl_tmty) (@kl_tm).
Theorem tm_commute : commute tm_types_terms.
Proof. commute_proof. Qed.
```

`register` reads the morphisms of the first sort's substitution off the
user's function, so the mask is not repeated.

Checked on System F (types past terms) and on a family with a sort between
(types past terms, regions between: `tm3_commute`).

## Still to do

1. `apply` for a sort: the payloads weakened along the other sorts' binders
   by those sorts' Kleisli functions (moving the focus to each).
2. `names` on the multi-sorted machinery.
