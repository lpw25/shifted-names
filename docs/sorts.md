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
Fixpoint kl_tm {B M} (f : morph 1 0 (uncurry 2 tm) B M) {K L} (x : fwit 1 0 B M K L)
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
  | lam A u => lam (kl_ty f (ty_in_tm x) A) (kl_tmty f (under 1 x) u)
```

with `ty_in_tm := restrict tdone (tskip tdone)` (types keep nothing to the
left of their focus and skip the term sort to the right). The helpers, all
of which compute away since the sorts are concrete:

* `F @ K`: the family `F` at the zipper of scopes `K`;
* `out K L`: the zipper `K` with `L`'s focus (the output of a
  substitution);
* `under t x`: the witness under a binder of sort `t`, whichever sort is
  focused;
* `restrict tl tr x`: the witness for a family inside another, over some of
  the sorts on each side;
* `here`: the witness at the root (`kl_tm f here t`).

## A substitution is focused on its sort

A family over `n` sorts is seen through a vector of scopes (`uncurry`).
Substituting sort `i`, the scopes are a *zipper* (`zip a b`): the `a` sorts
to the left of `i` (nearest first), `i`'s scope (the focus), and the `b`
sorts to the right; the family is at the zipper plugged back (`plug`,
putting the left part back onto the right one sort at a time).

The witness is a zipper of `ext`s (`fwit a b B M K L`): the focus's input
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
morph a b P B M := forall K L, fwit a b B M K L -> var (focus K) -> P (plug (out K L))
sort_kl a b P := … (f : morph a b P B M) … (x : fwit a b B M K L), P (plug K) -> P (plug (out K L))
fam_kl a b P tl tr T := … (f : morph a b P (zrestr tl tr B) (zrestr tl tr M)) … (x : fwit aT bT B M K L),
  T (plug K) -> T (plug (out K L))
```

Laws, per family and sort: `var`, `ext`, `rebase`, `unit`, `assoc`; all
routine inductions for System F (`ty_laws`, `tm_laws`, `tmty_laws`).

## Moving a substitution of one sort past one of another

Each substitution has the other's `ext` in its context, read from the side
it is on (`ext_flip`). Moving a type substitution `h` past a term
substitution `f`, `f`'s results have their types substituted (`tmap h f`):

```coq
kl_tmty h (rw e0 (ext_flip e1)) (kl_tm f (lw e0 e1) t)
  = kl_tm (tmap h f) (lw (ext_flip e0) e1) (kl_tmty h (rw e0 e1) t)
```

Here `lw` and `rw` are the witnesses holding the type witness `e0` and the
term witness `e1`, focused on terms and on types. It is proved by the same
routine induction (`commute`).

## Still to do

1. The commuting law as a class over any family and pair of sorts (the two
   foci related by moving the focus), which `names` uses to put
   substitutions of different sorts in a canonical order.
2. `apply` for a sort: the payloads weakened along the other sorts' binders
   by those sorts' Kleisli functions (moving the focus to each).
3. `names` on the multi-sorted machinery.
