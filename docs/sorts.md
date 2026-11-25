# Several sorts of variable (design)

A proposal for syntaxes with several sorts of variable (types and terms in
System F, values and computations, …), checked on System F in
`proto/sorts/Sorts.v` (standalone; `rocq compile -R theories ShiftedNames
proto/sorts/Sorts.v`). Nothing in the library uses it yet.

## The scheme

**Scopes.** Each sort has its own scope. A user's families are indexed by
the scopes of the sorts they can contain, curried, in their own order:
`ty : nat -> Type` (types only contain type variables), `tm : nat -> nat ->
Type` (type scope, then term scope).

**A sort's carrier.** The family a sort's variables stand for (types for the
type sort, terms for the term sort), seen with that sort's scope first and
the other sorts' scopes `o : O` after: `O = unit` for types, `O = nat` (the
type scope) for terms, a product for more sorts.

```coq
Definition Ty (K : nat) (_ : unit) : Type := ty K.
Definition Tm (K : nat) (N : nat) : Type := tm N K.
```

**Witnesses.** Going under a binder of the sort being substituted: `ext N M K
L`, as now. Going under a binder of another sort: `olift o o'`, which for one
other sort is `ext G G J J`, the same witness with the base unchanged. The
other scope is then the same index on both sides of a Kleisli function, so
nothing needs casting.

```coq
Class Others (O : Type) := {
  olift : O -> O -> Type;
  ohere : forall o, olift o o;
  ocomp : forall {o1 o2 o3}, olift o1 o2 -> olift o2 o3 -> olift o1 o3 }.
```

**Morphisms** of a sort are liftable along both kinds of binder:

```coq
Definition morph (P : nat -> O -> Type) (N M : nat) (o : O) : Type :=
  forall K L, ext N M K L -> forall o', olift o o' -> var K -> P L o'.
```

**Kleisli functions, one per family and sort.** A family is seen over the
carrier's other scopes. Its own scopes that the carrier lacks are
parameters, like the term scope when substituting types in terms. System F's
three functions:

```coq
(* types, the type sort *)
Fixpoint kl_ty {N M} (f : morph Ty N M tt) {K L} (e : ext N M K L) (A : ty K) : ty L :=
  match A with
  | tyvar v => f K L e tt tt v
  | tyarr A B => tyarr (kl_ty f e A) (kl_ty f e B)
  | tyall B => tyall (kl_ty f (ext_under e) B)
  end.

(* terms, the type sort: types inside are a family with a smaller vector *)
Fixpoint kl_tmty {J N M} (f : morph Ty N M tt) {K L} (e : ext N M K L) (t : tm K J) : tm L J :=
  match t with
  | tmvar v => tmvar v
  | lam A b => lam (kl_ty f e A) (kl_tmty f e b)
  | app t u => app (kl_tmty f e t) (kl_tmty f e u)
  | tlam b => tlam (kl_tmty f (ext_under e) b)
  | tapp t A => tapp (kl_tmty f e t) (kl_ty f e A)
  end.

(* terms, the term sort: under a type binder only the witness moves *)
Fixpoint kl_tm {N M G} (f : morph Tm N M G) {K L} (e : ext N M K L) {J} (w : ext G G J J) (t : tm J K) : tm J L :=
  match t with
  | tmvar v => f K L e J w v
  | lam A b => lam A (kl_tm f (ext_under e) w b)
  | app t u => app (kl_tm f e w t) (kl_tm f e w u)
  | tlam b => tlam (kl_tm f e (ext_under w) b)
  | tapp t A => tapp (kl_tm f e w t) A
  end.
```

Nothing in them weakens anything, and nothing mentions adjustments.

**Laws, per family and sort.** These are the current five, `ext`, `rebase`,
`unit` and `assoc` (plus `var` for a sort's own carrier), with the
other-sort witness threaded through, and one new one:

```coq
kl f e (ocomp w1 w2) t = kl (orebase_m w1 f) e w2 t
  (* orebase_m w1 f := fun K L e o2 w2 v => f K L e o2 (ocomp w1 w2) v *)
```

For System F each law is a routine induction of one to three lines, for all
three functions (`ty_laws`, `tmty_laws`, `tm_laws` in the prototype). No
law relates the two sorts.

**What the library derives.**
- **Weakening a carrier along another sort's binders:** `oweak w u`, the
  carrier's Kleisli function for that sort along a weakening morphism built
  from the variable constructor alone. Its identity and composition laws
  follow from the user's laws (`oweak_here`, `oweak_comp` in the
  prototype).
- **`apply a` as a morphism of the new kind:** at a witness `w`, a payload
  `u` gives `kleisli (apply ρ) ext_here w (oweak w u)`. This is the only
  place anything is shifted.
- **Substituting under binders of another sort** is substituting along the
  mapped adjustment: `kleisli (apply a) e w t = kleisli (apply (pmap (oweak
  w) a)) e (ohere _) t`. This follows from `apply`'s definition, `orebase`
  and `oweak_comp`, with no further user law. `pmap` (now in `PMap.v`)
  becomes internal: `names`' nodes under such binders carry `pmap (oweak w)
  a`, and its reifier already pushes `pmap` into the adjustment.

**More sorts.** `O` is the product of the other scopes, and `olift`, `ohere`
and `ocomp` are componentwise. A user's Kleisli function moves the component
of the sort whose binder it crosses.

## Relating two sorts (optional)

Moving a substitution of one sort past one of another, for example a type
substitution past a term substitution, needs one law per pair of sorts. It
is what `names` needs to push one past the other and to normalise payloads
afterwards. For System F:

```coq
kl_tmty g E (kl_tm f e w u) = kl_tm (f ⋆ g) e w' (kl_tmty g E u)
```

Here `f ⋆ g` is `f` followed by `g`, and `E`, `w'` are `w` moved to the
bases of the type substitution. Moving a witness between bases is a library
function, by recursion on the witness. The variable case needs that moving
a witness there and back gives `f` the same argument, which is a library
lemma, so the user's proof is again an induction. This part is not in the
prototype yet.

## Open questions

1. **Notation and inference.** A sort's view of a family is a function
   (`fun K N => tm N K`), so `t [a]` with `t : tm N K` cannot find it by
   first-order unification. It needs one notation per position, like
   `kl_at` (substitution in the first or second scope of a two-scope
   family), or canonical structures keyed on each Kleisli function. This has
   to be tried.
2. **One-sorted syntaxes** get `unit` witnesses (`O = unit`). The laws then
   need a `destruct` of them, since `unit` has no eta. A wrapper could keep
   the current signatures for one sort.
3. **The relating law above:** its exact statement and the witness lemmas.
4. **Migration.** Lambda and STLC move to `O = unit`; System F is rewritten
   as above; `SyntaxMap` and `mmap` leave the user's side.
