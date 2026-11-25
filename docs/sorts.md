# Several sorts of variable (design)

A proposal for syntaxes with any number of sorts of variable (types and
terms in System F, regions, values and computations, …), generic over the
number of sorts, checked in
`proto/sorts/Sorts.v` (standalone; `rocq compile -R theories ShiftedNames
proto/sorts/Sorts.v`). Nothing in the library uses it yet.

## The scheme

**Scopes.** A family is indexed by a vector of nats, one scope per sort; a
sort is a position in the vector. `vec n` is `n` nats (pairs with eta,
ending in `unit`); `upd n i k` replaces sort `i`'s scope. The user's
families stay curried, and are seen through their vectors:

```coq
Definition Ty (x : vec 1) : Type := ty (first x).                    (* types: sort 0 *)
Definition Tm (x : vec 2) : Type := tm (first x) (first (second x)). (* terms: sorts 0 and 1 *)
```

A family inside another, types inside terms, is indexed by some of the
other's sorts, in order: a thinning `th : thin m n` (keep or skip each of
the `n` positions). `select th` picks its scopes from the larger vector, and
`timg th i` is where its sort `i` is among the `n`. In the three-sort
example, types are over (types, regions) and terms over (types, terms,
regions), with `tkeep (tskip (tkeep tdone))` between them.

**Witnesses.** Substituting sort `i`:
- `ext N M K L` for `i`'s own binders, as now;
- `lifts n i b j` for the other sorts' binders: one `ext Bt Bt Jt Jt` per
  other position `t` (`Bt` its base, `Jt` the scope reached, the base
  unchanged), computed from `n` and `i`. For System F's term sort it is one
  `ext` for types; for terms over types, terms and regions (term sort 1) it
  is two:

```coq
lifts 3 1 b (pair J (pair K (pair R tt)))
  = both (ext b0 b0 J J) (both unit (both (ext b2 b2 R R) unit))
```

`lhere` (no binders crossed) and `lcomp` (composition) are generic in `n`
and `i`.

**Morphisms** of sort `i` go into its carrier `P`, the family its variables
stand for, over the carrier's own vector of `n` sorts. They are liftable
along all of their binders:

```coq
Definition morph (P : vec n -> Type) (N M : nat) (b : vec n) : Type :=
  forall K L, ext N M K L -> forall j, lifts n i b j -> var K -> P (upd n i L j).
```

**Kleisli functions, one per family and sort.**
- The carrier's own: `P (upd n i K j) -> P (upd n i L j)`.
- Another family's, over a longer vector of `nT` sorts with the carrier's
  among them by `th`: `T (upd nT (timg th i) K jT) -> T (upd nT (timg th i)
  L jT)`, with the witness for the carrier's sorts taken through `select th
  jT`.

The user's functions thread the other sorts' witness, moving the component
of the sort whose binder they cross. System F's:

```coq
Fixpoint kl_ty {N M b} (f : morph 1 0 Ty N M b) {K L} (e : ext N M K L) j (w : lifts 1 0 b j)
    (A : ty K) : ty L := …            (* tyall: ext_under e *)

Fixpoint kl_tmty {J N M b} (f : morph 1 0 Ty N M b) {K L} (e : ext N M K L) j (w : lifts 1 0 b j)
    (t : tm K J) : tm L J := …        (* lam A u => lam (kl_ty f e j w A) (kl_tmty f e j w u) *)

Fixpoint kl_tm {N M b} (f : morph 2 1 Tm N M b) {K L} (e : ext N M K L) (J : nat) (r : vec 1)
    (w : lifts 2 1 b (pair J r)) (t : tm J K) : tm J L :=
  match t with
  | tmvar v => f K L e (pair J r) w v
  | lam A u => lam A (kl_tm f (ext_under e) J r w u)
  | tlam u => tlam (kl_tm f e (S J) r (pair (ext_under (first w)) (second w)) u)
  …
```

The three-sort example's term sort moves the type component under a type
binder and the region component under a region binder, in the same way.
Nothing in any of them weakens anything or mentions adjustments.

**Laws, per family and sort,** generic over the vectors and positions: the current `var`,
`ext`, `rebase`, `unit` and `assoc`, with the witness threaded through, and
one new law, `orebase`: the other sorts' witnesses compose,

```coq
kl f e (lcomp w1 w2) t = kl (orebase_m w1 f) e w2 t
```

For System F every law is a routine induction (`ty_laws`, `tmty_laws`,
`tm_laws`). Each needs the computed scope types unfolded first (`sc`) and
its induction hypotheses applied explicitly (`ih`). The library would
provide those two tactics. No law relates two sorts.

## What the library derives

- **Weakening a carrier along the other sorts' binders,** position by
  position: for each other sort `t` of the carrier's vector, the carrier's
  Kleisli function for `t` along a weakening morphism built from `t`'s
  variable constructor alone. For one other sort this is checked, with its
  identity and composition laws, in an earlier version of the prototype
  (commit e325b78). Generically over `n`, it is a recursion over the
  vector's positions; this is the next thing to write.
- **`apply a`** puts that weakening on each payload, at the witness it is
  given. It is the only place anything is shifted.
- **Substituting under binders of other sorts** is substituting along the
  mapped adjustment, `pmap (oweak w) a`. This follows from `apply`'s
  definition, `orebase` and weakening's composition, with no further law
  from the user. `names`' reifier already pushes `pmap`.

## Relating two sorts (optional)

Moving a substitution of one sort past one of another, for example a type
substitution past a term substitution, needs one law per pair of sorts. It
is what `names` needs to push one past the other and normalise payloads
afterwards. The law says the second sort's Kleisli function, applied after
the first's, is the first's along the composed morphism, applied after the
second's. Moving witnesses between bases is a library function. The user's
proof is again an induction. Not prototyped yet.

## Open questions

1. **Generic weakening,** as a recursion over the positions (above).
2. **Notation and inference:** `t [a]` on a `tm N K` must find the view
   `Tm` and the vector `pair N (pair K tt)`. That needs a notation per
   position, or canonical structures keyed on each Kleisli function. To be
   tried.
3. **Relating two sorts:** the exact statement and the witness lemmas.
4. **One-sorted syntaxes** are the case `n = 1`; their witness is `unit`,
   threaded through. A wrapper could keep the current signatures.
