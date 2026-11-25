(** * Prototype: one descent witness for any number of sorts

    Families are indexed directly by a vector of scopes.  Substituting
    sort [i], the binders gone under are one value, [vext n i B Mi K Li]:
    the input scopes [K] (a vector) and the substituted sort's output scope
    [Li].  The output scopes are [K] with [i]'s replaced by [Li], so the
    other sorts' scopes are visibly unchanged and nothing containing only
    them is visited.  Build with
      rocq compile -R theories ShiftedNames proto/sorts/Desc.v *)

From Stdlib Require Import Arith.
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
    output scope [Mi]: under a binder of sort [t], [t]'s input scope goes
    up, and so does the output scope when [t] is [i].  With one sort this
    is [ext]. *)
Inductive vext (n i : nat) (B : vec n) (Mi : nat) : vec n -> nat -> Type :=
| vhere : vext n i B Mi B Mi
| vunder (t : nat) {K Li} : vext n i B Mi K Li ->
    vext n i B Mi (upd n t (S (get n t K)) K) (if Nat.eqb t i then S Li else Li).

Arguments vhere {n i B Mi}.
Arguments vunder {n i B Mi} t {K Li} e.

(** A morphism of sort [i] into its carrier [P]. *)
Definition morph (n i : nat) (P : vec n -> Type) (B : vec n) (Mi : nat) : Type :=
  forall K Li, vext n i B Mi K Li -> var (get n i K) -> P (upd n i Li K).

(** ** System F, indexed directly by vectors *)

Inductive ty (x : vec 1) : Type :=
| tyvar (v : var (first x))
| tyarr (A B : ty x)
| tyall (B : ty (pair (S (first x)) (second x))).

Arguments tyvar {x} v.
Arguments tyarr {x} A B.
Arguments tyall {x} B.

(** Types are sort 0 of terms. *)
Definition ty_in_tm : thin 1 2 := tkeep (tskip tdone).

Inductive tm (x : vec 2) : Type :=
| tmvar (v : var (first (second x)))
| lam (A : ty (select ty_in_tm x)) (b : tm (pair (first x) (pair (S (first (second x))) (second (second x)))))
| app (t u : tm x)
| tlam (b : tm (pair (S (first x)) (second x)))
| tapp (t : tm x) (A : ty (select ty_in_tm x)).

Arguments tmvar {x} v.
Arguments lam {x} A b.
Arguments app {x} t u.
Arguments tlam {x} b.
Arguments tapp {x} t A.

(** Types, the type sort. *)
Fixpoint kl_ty {B Mi} (f : morph 1 0 ty B Mi) {K Li} (e : vext 1 0 B Mi K Li) (A : ty K) : ty (upd 1 0 Li K) :=
  match A with
  | tyvar v => f K Li e v
  | tyarr A A' => tyarr (kl_ty f e A) (kl_ty f e A')
  | tyall A => tyall (x := upd 1 0 Li K) (kl_ty f (vunder 0 e) A)
  end.

(** Terms, the term sort: one witness, moved under every binder; the
    annotations are passed through untouched. *)
Fixpoint kl_tm {B Mi} (f : morph 2 1 tm B Mi) {K Li} (e : vext 2 1 B Mi K Li) (t : tm K) : tm (upd 2 1 Li K) :=
  match t with
  | tmvar v => f K Li e v
  | lam A u => lam (x := upd 2 1 Li K) A (kl_tm f (vunder 1 e) u)
  | app t u => app (kl_tm f e t) (kl_tm f e u)
  | tlam u => tlam (x := upd 2 1 Li K) (kl_tm f (vunder 0 e) u)
  | tapp t A => tapp (kl_tm f e t) A
  end.

(** Terms, the type sort, through the thinning: the witness is over the
    types' sorts; term binders leave it alone. *)
Fixpoint kl_tmty {B Mi} (f : morph 1 0 ty B Mi) {x Li} (t : tm x) (e : vext 1 0 B Mi (select ty_in_tm x) Li)
    : tm (upd 2 (timg ty_in_tm 0) Li x) :=
  match t with
  | tmvar v => tmvar (x := upd 2 0 Li x) v
  | lam A u => lam (x := upd 2 0 Li x) (kl_ty f e A) (kl_tmty f u e)
  | app t u => app (x := upd 2 0 Li x) (kl_tmty f t e) (kl_tmty f u e)
  | tlam u => tlam (x := upd 2 0 Li x) (kl_tmty f u (vunder 0 e))
  | tapp t A => tapp (x := upd 2 0 Li x) (kl_tmty f t e) (kl_ty f e A)
  end.

(** A law, by the usual induction: the witness's input vector is an
    index, so induction generalises over it. *)
Lemma kl_tm_ext {B Mi} (f g : morph 2 1 tm B Mi) :
  (forall K Li e v, f K Li e v = g K Li e v) ->
  forall K Li (e : vext 2 1 B Mi K Li) t, kl_tm f e t = kl_tm g e t.
Proof.
  intros H K Li e t; revert Li e; induction t; intros Li e; cbn; f_equal;
    try apply H; try apply IHt; try apply IHt1; try apply IHt2.
Qed.
