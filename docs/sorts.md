# Several sorts of variable (design)

A design for syntaxes with any number of sorts of variable (types and terms
in System F, regions, values and computations, …), checked on System F in
`proto/sorts/Focus.v` (`rocq compile -R theories ShiftedNames -Q proto/sorts
Proto proto/sorts/Focus.v`). Nothing in the library uses it yet.

## What the user writes

Their own curried families, with plain constructors, one Kleisli function
per family and sort, and the laws (each by induction on the term). Sorts are counted
from the left (System F: types 0, terms 1). For terms, substituting term
variables:

```coq
Fixpoint kl_tm {B M} (f : morph 1 0 tm B M) {K L} (x : descent 1 0 B M K L)
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
Fixpoint kl_tmty {B M : scopes 0 1} (f : morph 0 0 ty _ _) {K L} (x : descent 0 1 B M K L)
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

The witness (`descent a b B M K L`) is a path of steps, in the order the
binders were gone under; a step is a zipper of `ext`s (`step a b B M K L`):
the focus's input and output scopes, and for each other sort its scope and
the one on the other side of a substitution of it. `under t x` adds a step
with one binder of sort `t`. A Kleisli function goes from `K` to `out K L`,
`K` with the focus's output scope: the other sorts are the same on both
sides, so nothing containing only them is visited.

The order of binders of different sorts is kept, so nothing relies on
binders of different sorts commuting (weakening a payload in `apply`
follows it, below).

The focus is at a fixed place in each step, read by a projection, so
nothing is cut out of a vector or put back, and there are no casts:

* composing witnesses (rebase) is appending paths; splitting through a
  middle scope (assoc) is on the focus alone, step by step;
* a family inside another is focused on the same sort, over thinnings of
  each side; its witness is the restriction of each step (a `pmap` over
  the path);
* moving the focus one sort along leaves the plugged vector the same by
  computation (`plug_right1`, `reflexivity` for any number of sorts).

## Morphisms, Kleisli functions, laws

```coq
morph a b F B M := forall K L, descent a b B M K L -> var (focus K) -> F @ out K L
sort_kl a b F := … (f : morph a b F B M) … (x : descent a b B M K L), F @ K -> F @ out K L
fam_kl a b F tl tr T := … (f : morph a b F (zrestr tl tr B) (zrestr tl tr M)) … (x : descent aT bT B M K L),
  T @ K -> T @ out K L
```

`F` is the user's own family (`ty`, `tm`), and the user's Kleisli function
itself (`@kl_ty`) is the `sort_kl`.

Laws, per family and sort: `var`, `ext`, `rebase`, `unit`, `assoc`. The user
proves each as a separate lemma about their own function, stated with the
scopes as numbers (`⟪ l | k | r ⟫`: the sorts left of the focus, nearest
first, the focus, the sorts right of it), and by plain induction:

```coq
Lemma kl_ty_assoc {B M} Mi (g : morph 0 0 ty (refocus B Mi) M) (f : morph 0 0 ty B (refocus M Mi)) :
  forall n (A : ty n) l (x : descent 0 0 B M ⟪[] | n | []⟫ ⟪[] | l | []⟫),
  kl_ty (comp_m 0 0 ty (@kl_ty) Mi g f) x A = kl_ty g (fright Mi x) (kl_ty f (fleft Mi x) A).
Proof. intros n A; induction A; intros; cbn; f_equal; easy. Qed.
```

The term comes before the output scope and the witness, which vary under
a binder, so `induction` generalises them. Unit is over `descent B B K K`
(the other sorts the same on both sides); rebase is
`kp (rebase_m x1 f) x t = kp f (fapp x1 x) t`. The lemmas are then packed
into the law record, by conversion alone:

```coq
Definition ty_laws : sort_laws 0 0 ty (fun K v => tyvar v) (@kl_ty) :=
  {| s_var _ _ _ _ _ _ _ := eq_refl; s_ext := @kl_ty_ext; s_rebase := @kl_ty_rebase;
     s_unit := kl_ty_unit; s_assoc := @kl_ty_assoc |}.
```

The record states each law over the scopes one sort at a time (`sall`),
which at concrete sorts computes to the lemma's `forall n …`; vectors
appear only there. `var` is a primitive record, so the unit law's variable
case holds by computation.

A family's laws also use its carrier's where it calls the carrier's
Kleisli function, from the carrier's record: ext and unit directly
(`kp_ext ty_laws`, `kp_unit ty_laws`), rebase and assoc through the
restriction (`rebase_restrict ty_laws`, `assoc_restrict ty_laws`;
restricting a path commutes with appending and splitting it, by induction
on the path). Each such case is one `simple apply` of one of them:

```coq
Lemma kl_tmty_rebase {B M : scopes 0 1} (f : morph_in ty_in_tm B M ty) {K1 L1} (x1 : descent 0 1 B M K1 L1) :
  forall n k (t : tm n k) n' l (x : descent 0 1 K1 L1 ⟪[] | n | [k]⟫ ⟪[] | n' | [l]⟫),
  kl_tmty (rebase_m 0 0 (restrict ty_in_tm x1) f) x t = kl_tmty f (fapp x1 x) t.
Proof. intros n k t; induction t; intros; cbn; f_equal; first [easy | simple apply (rebase_restrict ty_laws)]. Qed.
```

### All at once

`kleisli_induction` (and `kleisli_induction using ty_laws` for a family)
proves a whole law record, each law exactly as by hand:

```coq
Definition tm_laws : sort_laws 1 0 tm (fun K v => tmvar v) (@kl_tm).
Proof. kleisli_induction. Defined.

Definition tmty_laws : fam_laws 0 1 ty_in_tm ty (fun K v => tyvar v) (@kl_ty) tm (@kl_tmty).
Proof. kleisli_induction using ty_laws. Defined.
```

For each field it puts the record's statement into the hand-written
lemma's form (`cbn [sall vall]` unfolds the scopes to numbers, `cbn in t`
computes the term's type to `tm n k`), then does `induction t; intros; cbn;
f_equal` and closes each case by `easy` or one `simple apply` of one of the
carrier's four laws, tried in a fixed order. There is no search beyond
that, so a case either is one of those or the tactic fails on it, and the
user writes that law by hand instead.

It suffices when the Kleisli function is structural: its variable case is
the morphism at the witness; every other case is a constructor whose
arguments are each a recursive call at the witness or `under t` of it,
the carrier's Kleisli function at `x‹…›`, or the argument unchanged. After
`f_equal` each argument is then a goal of one of these kinds:
- both sides the same: `easy`;
- a recursive call: the induction hypothesis, its output scope and witness
  quantified, so `easy` instantiates them by matching (under a binder,
  `under t x`, whose scope is a plain zipper by computation);
- a call of the carrier: the carrier's law of the same name.
The variable case of each law is computation (unit's because `var` is a
primitive record).

Two `Arguments` declarations make `cbn` leave a family's goals over
`restrict_lr` and `zrestr`, the form the carrier's laws are stated in
(`restrict` and `zsub` unfold), so that `simple apply` matches them
syntactically.

### Mutually inductive families (`proto/sorts/CBPV.v`)

Call-by-push-value: values and computations are mutually inductive, with
one sort of variable (value variables). Values are that sort's family;
computations are an ordinary family (`fam_laws`) over the mask keeping
every sort, with values as their carrier. Restricting by a mask that keeps
every sort is the witness itself by computation (the thinning is `tid`,
which `restrict_lr` passes through), so `kl_comp` hands its own `x` to
`kl_val`, and the carrier's own laws apply as they are.

Nothing in the library is about mutual recursion. The two Kleisli
functions are mutually recursive, so the user proves each law of both at
once, by their mutual induction scheme (`Scheme … with …`, `Combined
Scheme`), one line each:

```coq
Lemma kl_vc_rebase {B M} (f : morph 0 0 val B M) {K1 L1} (x1 : descent 0 0 B M K1 L1) :
  forall n, (forall (v : val n) l (x : descent 0 0 K1 L1 ⟪[] | n | []⟫ ⟪[] | l | []⟫),
     kl_val (rebase_m 0 0 x1 f) x v = kl_val f (fapp x1 x) v)
  /\ (forall (c : comp n) l (x : descent 0 0 K1 L1 ⟪[] | n | []⟫ ⟪[] | l | []⟫),
     kl_comp (rebase_m 0 0 x1 f) x c = kl_comp f (fapp x1 x) c).
Proof. apply val_comp_mut; intros; cbn; f_equal; easy. Qed.
```

and each record takes its half (`s_rebase B M f K1 L1 x1 n := proj1
(kl_vc_rebase f x1 n)`, and `proj2` for the computations').

All at once, on the two records together:

```coq
Goal sort_laws 0 0 val (fun K v => vvar v) (@kl_val)
     /\ fam_laws 0 0 all_sorts val (fun K v => vvar v) (@kl_val) comp (@kl_comp).
Proof. kleisli_induction with val_comp_mut. Qed.
```

The tactic builds both records from four joint laws, each the
conjunction of the two families' (split back by `sall_proj1`,
`sall_proj2`), and proves each joint law by one `apply` of the scheme,
whose cases have both families' induction hypotheses, closed as for one
family.

## Moving a substitution of one sort past one of another (`proto/sorts/Commute.v`)

Two sorts `i` left of `j` are two foci at once: a zipper with two holes
(`scopes2 a c d`: the `a` sorts left of `i`, `i`, the `c` sorts between, `j`,
the `d` sorts right of `j`). Seen from either hole it is a one-hole zipper
(`zi`, `zj`). The witness is a path of two-hole zippers of `ext`s
(`descent2`), a witness for either sort step by step (`wi`, `wj`); each
substitution sees the other's `ext` read from the side it is on (`flipx`,
`flipy`). All of these are plain functions (maps over the path).

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
the term; at a variable, and at a family inside, the two sides' witnesses
are the same step by step, by induction on the path; under a binder the
witness goes under):

```coq
Definition tm_types_terms := register 2 0 1 (uncurry 2 tm) (@kl_tmty) (@kl_tm).
Theorem tm_commute : commute tm_types_terms.
Proof. commute_proof. Qed.
```

`register` reads the morphisms of the first sort's substitution off the
user's function, so the mask is not repeated. Going back from `j`'s view
(`unzj`, `unwj`) rebuilds the sorts between, whose vector ends in a unit
tail with no eta; the tail is taken from the zipper seen from, so the
result is the same zipper by computation.

Checked on System F (types past terms) and on a family with a sort between
(types past terms, regions between: `tm3_commute`).

## `apply` (`proto/sorts/Apply.v`)

The morphism of an adjustment of one sort: its payloads are terms of the
family at the other sorts' base scopes. It is the library's `ggapply`
(`gapply` over any descent and results, characterised once in `Subst.v`)
with: the depth is that of the sort's own `ext` in the descent (`main`,
folded over the steps); a variable result is built at the output scopes
directly; a payload result is weakened along the other sorts' binders
crossed, step by step in the descent's order (`wk`, a fold of `wks`).

Weakening along one step is a substitution of the other sort by a shift.
Both pieces come from what the user already wrote: the shift is a
morphism built from that sort's `tvar` (`shift_m`), and the substitution
is the user's own Kleisli function for it, taken from the registration of
the two sorts (`weaken_x`):

```coq
Definition wks_tm : forall K L K' L' (s : step 1 0 K L K' L') k, tm @ refocus K k -> tm @ refocus K' k :=
  weaken_x tm_types_terms ty (fun K v => tyvar v).
```

Type substitution has nothing to weaken. Checked by computation:
instantiating under a type binder shifts the payload's types, and type
substitution in terms under term and type binders. Proved from the generic
characterisation: the identity adjustment is the identity morphism, and
substituting by it is the identity (`apply2_identity`, `subst2_identity`);
going under a binder of the sort at the root is substituting by the lifted
adjustment (`kp_apply2_lift`, given that weakening along a step with only
the sort's own binder is the identity, `wks_focus`; for System F
`tm_apply_lift`, whose `wks_focus` is the unit law of `kl_tmty` since a
shift by none is the unit, `shift_m_0`).

## Still to do

1. The other laws of `apply`: going under a binder of another sort
   (payloads weakened; `PMap`'s lemma generalised to `ggapply`), and
   composition (`Subst.v`'s composition section generalised likewise).
2. Weakening along a step for families with more than two sorts: one
   `weaken_x` per other sort, in turn (`weaken_x` updates only its own
   sort's scope).
3. `names` on the multi-sorted machinery.
