# Several sorts of variable (design)

A design for syntaxes with any number of sorts of variable (types and terms
in System F, regions, values and computations, …), checked on System F in
`proto/sorts/Focus.v` (`rocq compile -R theories ShiftedNames -Q proto/sorts
Proto proto/sorts/Focus.v`). Nothing in the library uses it yet.

## What the user writes

Their own curried families, with plain constructors, one Kleisli function
per family and sort, and the laws (routine inductions). For System F terms,
substituting term variables:

```coq
Fixpoint kl_tm f {C C' Ki Li} (w : cwit 1 0 B M C C') (e : ext Bi Mi Ki Li)
    (t : tm (first (first C)) Ki) : tm (first (first C)) Li :=
  match t with
  | tmvar v => f C C' Ki Li w e v
  | lam A u => lam A (kl_tm f w (ext_under e) u)     (* annotation untouched *)
  | app t u => app (kl_tm f w e t) (kl_tm f w e u)
  | tlam u => tlam (kl_tm f (cunder 0 w) e u)         (* under a type binder *)
  | tapp t A => tapp (kl_tm f w e t) A
  end.
```

with `kl_ty` (types) and `kl_tmty` (terms, substituting type variables)
alike.

## A substitution is focused on its sort

A family over `n` sorts is seen through a vector of scopes (`uncurry`).
Substituting sort `i`, the scopes are a *zipper*: the sorts to the left of
`i` (nearest first), `i`'s scope, and the sorts to the right; the family is
at the zipper plugged back (`plug`, putting the left part back onto the
right). Sort `i` of `n` is "`a` sorts to the left, `b` to the right".

The witness has the same shape: an `ext` for sort `i` (its input and output
scopes), and a context with an `ext` for each other sort (`cwit`: the
other sorts' scopes, and those on the other side of a substitution of
theirs). Under a binder of sort `i` the `ext` goes under; under one of
another sort `t`, the context does (`cunder t`, `t` counted from the left
as the user counts). A Kleisli function goes from `plug C Ki` to `plug C
Li`: the other sorts are the same context on both sides, so nothing
containing only them is visited.

Nothing is cut out of a vector or put back, so there are no casts:

* composing witnesses (rebase) is `ext_app` and componentwise on the
  context; splitting through a middle scope (assoc) is on the `ext` alone;
* a family inside another (types in terms) is focused on the same sort,
  over thinnings of the left and right contexts; its morphism sees its
  part of the context (`cwrestr`), componentwise;
* the order of binders of different sorts is not recorded, so it needs no
  law;
* moving the focus one sort along leaves the plugged vector the same by
  computation (`plug_move`, `reflexivity` for any number of sorts),
  because `plug` puts the left part back one sort at a time.

## Morphisms, Kleisli functions, laws

```coq
morph a b P B M Bi Mi := forall C C' Ki Li, cwit a b B M C C' -> ext Bi Mi Ki Li -> var Ki -> P (plug a b C Li)
sort_kl a b P := … f … (w : cwit a b B M C C') (e : ext Bi Mi Ki Li), P (plug a b C Ki) -> P (plug a b C Li)
fam_kl a b P tl tr T := … (f : morph a b P (crestr tl tr B) (crestr tl tr M) Bi Mi) … (w : cwit aT bT B M C C') e,
  T (plug aT bT C Ki) -> T (plug aT bT C Li)
```

Laws, per family and sort: `var`, `ext`, `rebase`, `unit`, `assoc`; all
routine inductions for System F (`ty_laws`, `tm_laws`, `tmty_laws`).

## Moving a substitution of one sort past one of another

Each substitution has the other's `ext` in its context, read from the side
it is on (`ext_flip`). Moving a type substitution `h` past a term
substitution `f`, `f`'s results have their types substituted (`tmap h f`):

```coq
kl_tmty h (rwit (ext_flip e1)) e0 (kl_tm f (lwit e0) e1 t)
  = kl_tm (tmap h f) (lwit (ext_flip e0)) e1 (kl_tmty h (rwit e1) e0 t)
```

proved by the same routine induction (`commute`).

## Still to do

1. The commuting law as a class over any family and pair of sorts (the two
   foci related by moving the focus), which `names` uses to put
   substitutions of different sorts in a canonical order.
2. `apply` for a sort: the payloads weakened along the other sorts' binders
   by those sorts' Kleisli functions (moving the focus to each).
3. `names` on the multi-sorted machinery.
