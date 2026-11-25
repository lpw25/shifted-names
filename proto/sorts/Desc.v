(** * Prototype: one descent witness for any number of sorts

    Families are indexed directly by a vector of scopes.  Substituting
    sort [i], the binders gone under are one value, [vext n i B Mi K Li]:
    the input scopes [K] (a vector) and the substituted sort's output scope
    [Li].  The output scopes are [K] with [i]'s replaced by [Li], so the
    other sorts' scopes are visibly unchanged and nothing containing only
    them is visited.  Going under a binder of sort [i] ([vunder]) and of
    another sort ([vother]) are separate constructors.  Build with
      rocq compile -R theories ShiftedNames proto/sorts/Desc.v *)

From Stdlib Require Import Arith StrictProp.
From ShiftedNames.Core Require Import Strict Label Var Scoped Indexed.

Set Primitive Projections.
Record both (A B : Type) : Type := pair { first : A; second : B }.
Unset Primitive Projections.
Arguments pair {A B} first second.
Arguments first {A B} _.
Arguments second {A B} _.

(** ** Vectors of scopes *)

Fixpoint vec (n : nat) : Type := match n with 0 => unit | S n => both nat (vec n) end.

Fixpoint get (n i : nat) : vec n -> nat :=
  match n as n0 return vec n0 -> nat with
  | 0 => fun _ => 0
  | S n => fun x => match i with 0 => first x | S i => get n i (second x) end
  end.

Fixpoint upd (n i k : nat) : vec n -> vec n :=
  match n as n0 return vec n0 -> vec n0 with
  | 0 => fun x => x
  | S n => fun x => match i with 0 => pair k (second x) | S i => pair (first x) (upd n i k (second x)) end
  end.

(** A family inside another: which of the [n] sorts it has, in order. *)
Inductive thin : nat -> nat -> Type :=
| tdone : thin 0 0
| tkeep {m n} : thin m n -> thin (S m) (S n)
| tskip {m n} : thin m n -> thin m (S n).

Fixpoint select {m n} (th : thin m n) : vec n -> vec m :=
  match th in thin m0 n0 return vec n0 -> vec m0 with
  | tdone => fun _ => tt
  | tkeep th => fun x => pair (first x) (select th (second x))
  | tskip th => fun x => select th (second x)
  end.

Fixpoint timg {m n} (th : thin m n) (i : nat) : nat :=
  match th with
  | tdone => i
  | tkeep th => match i with 0 => 0 | S i => S (timg th i) end
  | tskip th => S (timg th i)
  end.

(** ** The descent witness

    Substituting sort [i] from base scopes [B] (a vector) to the base
    output scope [Mi]: under a binder of sort [i] its input and output
    scopes go up; under a binder of another sort [t], only [t]'s input
    scope (which is also its output scope).  With one sort this is [ext]. *)
Inductive vext (n i : nat) (B : vec n) (Mi : nat) : vec n -> nat -> Type :=
| vhere : vext n i B Mi B Mi
| vunder {K Li} : vext n i B Mi K Li -> vext n i B Mi (upd n i (S (get n i K)) K) (S Li)
| vother (t : nat) {K Li} : vext n i B Mi K Li -> Is_true_s (negb (Nat.eqb t i)) ->
    vext n i B Mi (upd n t (S (get n t K)) K) Li.

Arguments vhere {n i B Mi}.
Arguments vunder {n i B Mi K Li} e.
Arguments vother {n i B Mi} t {K Li} e Ht.

(** A morphism of sort [i] into its carrier [P]. *)
Definition morph (n i : nat) (P : vec n -> Type) (B : vec n) (Mi : nat) : Type :=
  forall K Li, vext n i B Mi K Li -> var (get n i K) -> P (upd n i Li K).

(** ** System F: the user's own curried families, seen through vectors

    The constructors are ordinary; the library sees each family through a
    one-line view.  Unification only matches nats (the view's projections
    reduce), never a vector against its components. *)

Inductive ty (N : nat) : Type :=
| tyvar (v : var N)
| tyarr (A B : ty N)
| tyall (B : ty (S N)).

Arguments tyvar {N} v.
Arguments tyarr {N} A B.
Arguments tyall {N} B.

(** [tm N K]: [N] type variables, [K] term variables. *)
Inductive tm (N K : nat) : Type :=
| tmvar (v : var K)
| lam (A : ty N) (b : tm N (S K))
| app (t u : tm N K)
| tlam (b : tm (S N) K)
| tapp (t : tm N K) (A : ty N).

Arguments tmvar {N K} v.
Arguments lam {N K} A b.
Arguments app {N K} t u.
Arguments tlam {N K} b.
Arguments tapp {N K} t A.

(** The views are the library's: a curried family seen through a vector,
    by recursion on the number of sorts. *)
Fixpoint arity (n : nat) : Type := match n with 0 => Type | S n => nat -> arity n end.

Fixpoint uncurry (n : nat) : arity n -> vec n -> Type :=
  match n as n0 return arity n0 -> vec n0 -> Type with
  | 0 => fun F _ => F
  | S n => fun F x => uncurry n (F (first x)) (second x)
  end.

Notation Ty := (uncurry 1 ty).
Notation Tm := (uncurry 2 tm).

(** Types are sort 0 of terms. *)
Definition ty_in_tm : thin 1 2 := tkeep (tskip tdone).

(** Types, the type sort. *)
Fixpoint kl_ty {B Mi} (f : morph 1 0 Ty B Mi) {K Li} (e : vext 1 0 B Mi K Li) (A : Ty K) : Ty (upd 1 0 Li K) :=
  match A with
  | tyvar v => f K Li e v
  | tyarr A A' => tyarr (kl_ty f e A) (kl_ty f e A')
  | tyall A => tyall (kl_ty f (vunder e) A)
  end.

(** Terms, the term sort: one witness, moved under every binder; the
    annotations are passed through untouched. *)
Fixpoint kl_tm {B Mi} (f : morph 2 1 Tm B Mi) {K Li} (e : vext 2 1 B Mi K Li) (t : Tm K) : Tm (upd 2 1 Li K) :=
  match t with
  | tmvar v => f K Li e v
  | lam A u => lam A (kl_tm f (vunder e) u)
  | app t u => app (kl_tm f e t) (kl_tm f e u)
  | tlam u => tlam (kl_tm f (vother 0 e stt) u)
  | tapp t A => tapp (kl_tm f e t) A
  end.

(** Terms, the type sort: the witness is over the types' sorts, and the
    term scope [J] is an ordinary argument (term binders change it). *)
Fixpoint kl_tmty {B Mi} (f : morph 1 0 Ty B Mi) {K Li} (e : vext 1 0 B Mi K Li) {J} (t : tm (first K) J)
    : tm Li J :=
  match t with
  | tmvar v => tmvar v
  | lam A u => lam (kl_ty f e A) (kl_tmty f e u)
  | app t u => app (kl_tmty f e t) (kl_tmty f e u)
  | tlam u => tlam (kl_tmty f (vunder e) u)
  | tapp t A => tapp (kl_tmty f e t) (kl_ty f e A)
  end.

(** What the library sees: the family's vector put back together from the
    carrier's scopes and the others ([merge], through the thinning). *)
Fixpoint skips {m n} (th : thin m n) : nat :=
  match th with tdone => 0 | tkeep th => skips th | tskip th => S (skips th) end.

Fixpoint merge {m n} (th : thin m n) : vec m -> vec (skips th) -> vec n :=
  match th in thin m0 n0 return vec m0 -> vec (skips th) -> vec n0 with
  | tdone => fun _ _ => tt
  | tkeep th => fun x r => pair (first x) (merge th (second x) r)
  | tskip th => fun x r => pair (first r) (merge th x (second r))
  end.

Definition fam_kl_tmty {B Mi} (f : morph 1 0 Ty B Mi) {K Li} (e : vext 1 0 B Mi K Li) (r : vec (skips ty_in_tm))
    (t : Tm (merge ty_in_tm K r)) : Tm (merge ty_in_tm (upd 1 0 Li K) r) :=
  kl_tmty f e t.

(** A law, by the usual induction. *)
Lemma kl_tm_ext {B Mi} (f g : morph 2 1 Tm B Mi) :
  (forall K Li e v, f K Li e v = g K Li e v) ->
  forall K Li (e : vext 2 1 B Mi K Li) t, kl_tm f e t = kl_tm g e t.
Proof.
  intros H K Li e t; destruct K as [N [J r]]; cbn [uncurry] in t; cbn in t.
  revert Li e; induction t; intros Li e; cbn; f_equal;
    try apply H; try apply IHt; try apply IHt1; try apply IHt2.
Qed.
