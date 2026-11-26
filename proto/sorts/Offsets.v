(** * Prototype: witnesses as the sort's own [ext] and the other sorts'
    binder counts (offsets)

    An alternative to [Desc]'s [vext]: the witness records only sort [i]'s
    descent ([ext]); the other sorts' binders crossed are counted in its
    type ([D]), and the family is at [vadd D Bo].  So the order of binders
    of different sorts is not recorded ([wother 0 (wunder e)] and [wunder
    (wother 0 e)] are the same: naturality is definitional), and a witness
    does not mention the base, so a morphism can be moved to another base
    with no cast ([tmap]).  Checked: System F's Kleisli functions as
    before, and the interaction law (type substitution moved past term
    substitution), by a routine induction.  Build with
      rocq compile -R theories ShiftedNames -Q proto/sorts Proto proto/sorts/Desc.v
      rocq compile -R theories ShiftedNames -Q proto/sorts Proto proto/sorts/Offsets.v *)

From Stdlib Require Import Arith Lia StrictProp.
From ShiftedNames.Core Require Import Strict Label Var Scoped Indexed.
From ShiftedNames.Core Require Syntax.
Import Syntax (ext, ext_here, ext_under, ext_app, ext_mid, ext_left, ext_right, ext_depth).
From Proto Require Import Desc.
Import Desc (vec, get, upd, uncurry, both, pair, first, second, ty, tm, tyvar, tyarr, tyall, tmvar, lam, app, tlam, tapp).

(* offsets added on the left: d + b *)
Fixpoint vadd (n : nat) : vec n -> vec n -> vec n :=
  match n as n0 return vec n0 -> vec n0 -> vec n0 with
  | 0 => fun _ y => y
  | S n => fun x y => pair (first x + first y) (vadd n (second x) (second y))
  end.

Fixpoint vzero (n : nat) : vec n := match n with 0 => tt | S n => pair 0 (vzero n) end.

Set Primitive Projections.
Record wit (n i : nat) (Bi Mi : nat) (D : vec n) (Ki Li : nat) := mkw { wext : ext Bi Mi Ki Li }.
Unset Primitive Projections.
Arguments mkw {n i Bi Mi D Ki Li} _.
Arguments wext {n i Bi Mi D Ki Li} _.

Definition wtop {n i Bi Mi} : wit n i Bi Mi (vzero n) Bi Mi := mkw ext_here.
Definition wunder {n i Bi Mi D Ki Li} (e : wit n i Bi Mi D Ki Li) : wit n i Bi Mi D (S Ki) (S Li) := mkw (ext_under (wext e)).
Definition wother {n i Bi Mi D Ki Li} (t : nat) (e : wit n i Bi Mi D Ki Li) : wit n i Bi Mi (upd n t (S (get n t D)) D) Ki Li := mkw (wext e).

Definition morph n i (P : vec n -> Type) (Bo : vec n) (Bi Mi : nat) : Type :=
  forall D Ki Li, wit n i Bi Mi D Ki Li -> var Ki -> P (upd n i Li (vadd n D Bo)).

(* naturality is definitional *)
Goal forall n i Bi Mi D Ki Li (e : wit n i Bi Mi D Ki Li), wother 0 (wunder e) = wunder (wother 0 e).
Proof. reflexivity. Qed.

Fixpoint kl_ty {Bo Bi Mi} (f : morph 1 0 (uncurry 1 ty) Bo Bi Mi) {D Ki Li} (e : wit 1 0 Bi Mi D Ki Li)
    (A : ty Ki) : ty Li :=
  match A with
  | tyvar v => f D Ki Li e v
  | tyarr A A' => tyarr (kl_ty f e A) (kl_ty f e A')
  | tyall A => tyall (kl_ty f (wunder e) A)
  end.

Fixpoint kl_tm {Bo Bi Mi} (f : morph 2 1 (uncurry 2 tm) Bo Bi Mi) {D Ki Li} (e : wit 2 1 Bi Mi D Ki Li)
    (t : tm (first D + first Bo) Ki) : tm (first D + first Bo) Li :=
  match t with
  | tmvar v => f D Ki Li e v
  | lam A u => lam A (kl_tm f (wunder e) u)
  | app t u => app (kl_tm f e t) (kl_tm f e u)
  | tlam u => tlam (kl_tm f (wother 0 e) u)
  | tapp t A => tapp (kl_tm f e t) A
  end.

Fixpoint kl_tmty {Bo Bi Mi} (f : morph 1 0 (uncurry 1 ty) Bo Bi Mi) {D Ki Li} (e : wit 1 0 Bi Mi D Ki Li)
    {J} (t : tm Ki J) : tm Li J :=
  match t with
  | tmvar v => tmvar v
  | lam A u => lam (kl_ty f e A) (kl_tmty f e u)
  | app t u => app (kl_tmty f e t) (kl_tmty f e u)
  | tlam u => tlam (kl_tmty f (wunder e) u)
  | tapp t A => tapp (kl_tmty f e t) (kl_ty f e A)
  end.

(* The type witness advanced past d more type binders. *)
Fixpoint wunders {n i Bi Mi D Ki Li} (d : nat) (e : wit n i Bi Mi D Ki Li) : wit n i Bi Mi D (d + Ki) (d + Li) :=
  match d with 0 => e | S d => wunder (wunders d e) end.

(* A term morphism mapped by a type substitution: the base's type scope changes. *)
Definition tmap {Bh Gs Gt Dh Ks Kt} (h : morph 1 0 (uncurry 1 ty) Bh Gs Gt) (eh : wit 1 0 Gs Gt Dh Ks Kt)
    {r Bi Mi} (f : morph 2 1 (uncurry 2 tm) (pair Ks r) Bi Mi) : morph 2 1 (uncurry 2 tm) (pair Kt r) Bi Mi :=
  fun D K L e v => kl_tmty h (wunders (first D) eh) (f D K L e v).

(* Interaction law, stated *)
Definition interaction := forall Bh Gs Gt Dh Ks Kt (h : morph 1 0 (uncurry 1 ty) Bh Gs Gt) (eh : wit 1 0 Gs Gt Dh Ks Kt)
    r Bi Mi (f : morph 2 1 (uncurry 2 tm) (pair Ks r) Bi Mi) D K L (e : wit 2 1 Bi Mi D K L) (t : tm (first D + Ks) K),
  kl_tmty h (wunders (first D) eh) (kl_tm f e t) = kl_tm (tmap h eh f) e (kl_tmty h (wunders (first D) eh) t).

Lemma interaction_holds : interaction.
Proof.
  intros Bh Gs Gt Dh Ks Kt h eh r Bi Mi f D K L e t; revert D K L e t; fix IH 5; intros D K L e t.
  destruct t; cbn [kl_tm kl_tmty]; f_equal; first [reflexivity | apply IH | exact (IH _ _ _ (wother 0 e) t)].
Qed.
