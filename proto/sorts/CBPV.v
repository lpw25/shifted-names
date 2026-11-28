(** * Prototype: call-by-push-value, mutually inductive families with one sort

    Values and computations are mutually inductive, with one sort of
    variable (value variables).  Values are that sort's family;
    computations are a family over all the same sorts (the mask keeping
    everything, whose restriction is the witness itself), with values as
    their carrier.  The two Kleisli functions are mutually recursive, so
    each law is proved of both at once, by mutual induction, and each
    family's record takes its half.
    Build with
      rocq compile -R theories ShiftedNames -Q proto/sorts Proto proto/sorts/Focus.v
      rocq compile -R theories ShiftedNames -Q proto/sorts Proto proto/sorts/CBPV.v *)

From ShiftedNames.Core Require Import Strict Label Var Scoped Indexed.
From Proto Require Import Focus.

Inductive val (N : nat) : Type :=
| vvar (v : var N)
| vunit
| vpair (a b : val N)
| vthunk (c : comp N)
with comp (N : nat) : Type :=
| cret (v : val N)
| cbind (c : comp N) (k : comp (S N))
| clam (c : comp (S N))
| capp (c : comp N) (v : val N)
| cforce (v : val N)
| csplit (v : val N) (c : comp (S (S N))).

Arguments vvar {N} v.
Arguments vunit {N}.
Arguments vpair {N} a b.
Arguments vthunk {N} c.
Arguments cret {N} v.
Arguments cbind {N} c k.
Arguments clam {N} c.
Arguments capp {N} c v.
Arguments cforce {N} v.
Arguments csplit {N} v c.

Scheme val_mut := Induction for val Sort Prop with comp_mut := Induction for comp Sort Prop.
Combined Scheme val_comp_mut from val_mut, comp_mut.

(** The user's two Kleisli functions, mutually recursive. *)
Fixpoint kl_val {B M} (f : morph 0 0 val B M) {K L} (x : descent 0 0 B M K L) (v : val @ K) : val @ out K L :=
  match v with
  | vvar v => f K L x v
  | vunit => vunit
  | vpair a b => vpair (kl_val f x a) (kl_val f x b)
  | vthunk c => vthunk (kl_comp f x c)
  end
with kl_comp {B M} (f : morph 0 0 val B M) {K L} (x : descent 0 0 B M K L) (c : comp @ K) : comp @ out K L :=
  match c with
  | cret v => cret (kl_val f x v)
  | cbind c k => cbind (kl_comp f x c) (kl_comp f (under 0 x) k)
  | clam c => clam (kl_comp f (under 0 x) c)
  | capp c v => capp (kl_comp f x c) (kl_val f x v)
  | cforce v => cforce (kl_val f x v)
  | csplit v c => csplit (kl_val f x v) (kl_comp f (under 0 (under 0 x)) c)
  end.

(** ** The laws by hand: each for both families, by mutual induction *)

Lemma kl_vc_ext {B M} (f g : morph 0 0 val B M) (H : forall K L x v, f K L x v = g K L x v) :
  forall n, (forall (v : val n) l (x : descent 0 0 B M ⟪[] | n | []⟫ ⟪[] | l | []⟫), kl_val f x v = kl_val g x v)
  /\ (forall (c : comp n) l (x : descent 0 0 B M ⟪[] | n | []⟫ ⟪[] | l | []⟫), kl_comp f x c = kl_comp g x c).
Proof. apply val_comp_mut; intros; cbn; f_equal; easy. Qed.

Lemma kl_vc_rebase {B M} (f : morph 0 0 val B M) {K1 L1} (x1 : descent 0 0 B M K1 L1) :
  forall n, (forall (v : val n) l (x : descent 0 0 K1 L1 ⟪[] | n | []⟫ ⟪[] | l | []⟫),
     kl_val (rebase_m 0 0 x1 f) x v = kl_val f (fapp x1 x) v)
  /\ (forall (c : comp n) l (x : descent 0 0 K1 L1 ⟪[] | n | []⟫ ⟪[] | l | []⟫),
     kl_comp (rebase_m 0 0 x1 f) x c = kl_comp f (fapp x1 x) c).
Proof. apply val_comp_mut; intros; cbn; f_equal; easy. Qed.

Lemma kl_vc_unit B :
  forall n, (forall (v : val n) (x : descent 0 0 B B ⟪[] | n | []⟫ ⟪[] | n | []⟫),
     kl_val (unit_m 0 0 val (fun K v => vvar v) (B := B) (M := B)) x v = v)
  /\ (forall (c : comp n) (x : descent 0 0 B B ⟪[] | n | []⟫ ⟪[] | n | []⟫),
     kl_comp (unit_m 0 0 val (fun K v => vvar v) (B := B) (M := B)) x c = c).
Proof. apply val_comp_mut; intros; cbn; f_equal; easy. Qed.

Lemma kl_vc_assoc {B M} Mi (g : morph 0 0 val (refocus B Mi) M) (f : morph 0 0 val B (refocus M Mi)) :
  forall n, (forall (v : val n) l (x : descent 0 0 B M ⟪[] | n | []⟫ ⟪[] | l | []⟫),
     kl_val (comp_m 0 0 val (@kl_val) Mi g f) x v = kl_val g (fright Mi x) (kl_val f (fleft Mi x) v))
  /\ (forall (c : comp n) l (x : descent 0 0 B M ⟪[] | n | []⟫ ⟪[] | l | []⟫),
     kl_comp (comp_m 0 0 val (@kl_val) Mi g f) x c = kl_comp g (fright Mi x) (kl_comp f (fleft Mi x) c)).
Proof. apply val_comp_mut; intros; cbn; f_equal; easy. Qed.

(** The computations' laws are a family's, over the mask keeping the one
    sort; each record takes its half of each lemma. *)
Definition all_sorts : mask := cons true nil.

Definition val_laws : sort_laws 0 0 val (fun K v => vvar v) (@kl_val) :=
  {| s_var _ _ _ _ _ _ _ := eq_refl;
     s_ext B M f g H n := proj1 (kl_vc_ext f g H n);
     s_rebase B M f K1 L1 x1 n := proj1 (kl_vc_rebase f x1 n);
     s_unit B n := proj1 (kl_vc_unit B n);
     s_assoc B M Mi g f n := proj1 (kl_vc_assoc Mi g f n) |}.

Definition comp_laws : fam_laws 0 0 all_sorts val (fun K v => vvar v) (@kl_val) comp (@kl_comp) :=
  Build_fam_laws 0 0 all_sorts val (fun K v => vvar v) (@kl_val) comp (@kl_comp)
    (fun B M f g H n => proj2 (kl_vc_ext f g H n))
    (fun B M f K1 L1 x1 n => proj2 (kl_vc_rebase f x1 n))
    (fun B n => proj2 (kl_vc_unit B n))
    (fun B M Mi g f n => proj2 (kl_vc_assoc (B := B) (M := M) Mi g f n)).

(** ** All at once *)

Goal sort_laws 0 0 val (fun K v => vvar v) (@kl_val) /\ fam_laws 0 0 all_sorts val (fun K v => vvar v) (@kl_val) comp (@kl_comp).
Proof. kleisli_induction with val_comp_mut. Qed.
