# Several sorts of variable (design)

A proposal for syntaxes with any number of sorts of variable (types and
terms in System F, regions, values and computations, …), checked in
`proto/sorts/Sorts.v` (standalone; `rocq compile -R theories ShiftedNames
proto/sorts/Sorts.v`). Nothing in the library uses it yet.

## The scheme

Everything is generic over a type of sorts `S` with a boolean equality and
over lists of sorts. Nothing is specific to a number of sorts.

**Scopes.** A family is indexed by the scopes of a list of sorts, the sorts
it can contain: `scopes ss` is a tuple with one `nat` per sort of `ss`
(pairs with eta, ending in `unit`). `get ss s` and `upd ss s n` read and
replace sort `s`'s scope; `restrict ss ss'` gives the scopes of a sub-list.
The user's families stay curried; the library sees them through their
lists:

```coq
Definition Ty (x : scopes [TY]) : Type := ty (first x).
Definition Tm (x : scopes [TY; TM]) : Type := tm (first x) (first (second x)).
```

A family whose list is smaller than another's, types inside terms, is just
a family over its own list.

**Witnesses.** Substituting sort `s` uses two witnesses:
- `ext N M K L` for `s`'s own binders, as now;
- `lifts ss s b j` for the other sorts' binders: one `ext Gt Gt Jt Jt` per
  other sort `t` of the list (`Gt` its base, `Jt` the scope reached, the
  base unchanged), computed from the list.

For System F's term sort this is one `ext` for types. For a term sort
alongside types and regions it is two:

```coq
lifts [TY3; RG3; TM3] TM3 b (pair J (pair R r))
  = both (ext b_ty b_ty J J) (both (ext b_rg b_rg R R) (both unit unit))
```

`lhere` (no binders crossed) and `lcomp` (composition) are defined
componentwise, generically.

**Morphisms** of sort `s` go into its carrier `P`, the family its variables
stand for, over the carrier's own list `ss`. They are liftable along all of
that list's binders:

```coq
Definition morph (P : scopes ss -> Type) (N M : nat) (b : scopes ss) : Type :=
  forall K L, ext N M K L -> forall j, lifts ss s b j -> var K -> P (upd ss s L j).
```

**Kleisli functions, one per family and sort.**
- The carrier's own: `P (upd ss s K j) -> P (upd ss s L j)`.
- Another family's, over a longer list `ssT` that contains the carrier's:
  `T (upd ssT s K jT) -> T (upd ssT s L jT)`, with the witness for the
  carrier's sorts taken through `restrict ssT ss jT`.

The user's functions thread the other sorts' witness, moving the component
of the sort whose binder they cross. System F's:

```coq
Fixpoint kl_ty {N M b} (f : morph [TY] TY Ty N M b) {K L} (e : ext N M K L) j (w : lifts [TY] TY b j)
    (A : ty K) : ty L := …            (* tyall: ext_under e *)

Fixpoint kl_tmty {J N M b} (f : morph [TY] TY Ty N M b) {K L} (e : ext N M K L) j (w : lifts [TY] TY b j)
    (t : tm K J) : tm L J := …        (* lam A u => lam (kl_ty f e j w A) (kl_tmty f e j w u) *)

Fixpoint kl_tm {N M b} (f : morph [TY; TM] TM Tm N M b) {K L} (e : ext N M K L) (J : nat) (r : scopes [TM])
    (w : lifts [TY; TM] TM b (pair J r)) (t : tm J K) : tm J L :=
  match t with
  | tmvar v => f K L e (pair J r) w v
  | lam A u => lam A (kl_tm f (ext_under e) J r w u)
  | tlam u => tlam (kl_tm f e (S J) r (pair (ext_under (first w)) (second w)) u)
  …
```

The three-sort example's term sort moves the type component under a type
binder and the region component under a region binder, in the same way.
Nothing in any of them weakens anything or mentions adjustments.

**Laws, per family and sort,** generic over the lists: the current `var`,
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

- **Weakening a carrier along the other sorts' binders,** component by
  component: for each other sort `t` of the carrier's list, the carrier's
  Kleisli function for `t` along a weakening morphism built from `t`'s
  variable constructor alone. For one other sort this is checked, with its
  identity and composition laws, in the earlier version of the prototype
  (commit e325b78). Generically, each step must see `upd ss t (get ss t x)
  x` as `x`. That holds by computation for a concrete list, but not for a
  variable one. So the weakening is defined either by instances that
  recurse over the concrete list, or with one rewriting lemma per step.
  This is the next thing to settle.
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

1. **Generic weakening:** instances over the concrete list, or rewriting
   lemmas (above).
2. **Notation and inference:** `t [a]` on a `tm N K` must find the view
   `Tm` and the tuple `pair N (pair K tt)`. That needs a notation per
   position, or canonical structures keyed on each Kleisli function. To be
   tried.
3. **Relating two sorts:** the exact statement and the witness lemmas.
4. **One-sorted syntaxes** are the case of a one-sort list; their witness
   is `unit`, threaded through. A wrapper could keep the current signatures.
