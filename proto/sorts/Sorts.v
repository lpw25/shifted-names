(** * Prototype: syntaxes with several sorts of variable

    Checks the scheme of [docs/sorts.md] on System F: types with one
    scope, terms with two, a Kleisli function for each sort, and the laws
    a user proves.  Standalone: only [Var] and the witnesses of [Syntax]
    are used.  Build with
      rocq compile -R theories ShiftedNames proto/sorts/Sorts.v *)

From Stdlib Require Import Arith Lia.
From ShiftedNames.Core Require Import Strict Label Var Scoped Indexed.
From ShiftedNames.Core Require Syntax.
Import Syntax (ext, ext_here, ext_under, ext_app, ext_mid, ext_left, ext_right, ext_var, ext_var_same).

(** ** The generic part *)

(** The scopes of the other sorts, and witnesses for going under their
    binders.  One sort: [unit]; one other sort: its scope, a witness
    [ext G G J J] (binders over the base [G], the base unchanged); more:
    products. *)
Class Others (O : Type) := {
  olift : O -> O -> Type;
  ohere : forall o, olift o o;
  ocomp : forall {o1 o2 o3}, olift o1 o2 -> olift o2 o3 -> olift o1 o3 }.

#[export] Instance others_none : Others unit := {| olift _ _ := unit; ohere _ := tt; ocomp _ _ _ _ _ := tt |}.
#[export] Instance others_one : Others nat :=
  {| olift G J := ext G G J J; ohere G := ext_here; ocomp _ _ _ w1 w2 := ext_app w1 w2 |}.

Section Generic.

Context {O : Type} {OS : Others O}.

(** A morphism of a sort, into its carrier [P] (the terms that sort's
    variables stand for, with the other sorts' scopes [o]): liftable
    along the sort's binders ([ext], as now) and along the other sorts'
    ([olift]). *)
Definition morph (P : nat -> O -> Type) (N M : nat) (o : O) : Type :=
  forall K L, ext N M K L -> forall o', olift o o' -> var K -> P L o'.

Definition rebase_m {P N M K L o} (e1 : ext N M K L) (f : morph P N M o) : morph P K L o :=
  fun K' L' e o' w v => f K' L' (ext_app e1 e) o' w v.

Definition orebase_m {P N M o o1} (w1 : olift o o1) (f : morph P N M o) : morph P N M o1 :=
  fun K L e o2 w2 v => f K L e o2 (ocomp w1 w2) v.

(** The Kleisli extension of a family [T] (over the same other scopes)
    along a sort's morphisms. *)
Record kleisli_of (P T : nat -> O -> Type) := mk_kleisli {
  kl : forall {N M o} (f : morph P N M o) {K L} (e : ext N M K L) {o'} (w : olift o o'), T K o' -> T L o' }.

Arguments kl {P T} k {N M o} f {K L} e {o'} w t.

(** A sort's syntax: its carrier, variables, Kleisli function and laws. *)
Record sort_laws (P : nat -> O -> Type) (tv : forall {N o}, var N -> P N o) (k : kleisli_of P P) : Prop := {
  s_var : forall N M o (f : morph P N M o) K L (e : ext N M K L) o' (w : olift o o') v,
    kl k f e w (tv v) = f K L e o' w v;
  s_ext : forall N M o (f g : morph P N M o),
    (forall K L e o' w v, f K L e o' w v = g K L e o' w v) ->
    forall K L (e : ext N M K L) o' (w : olift o o') t, kl k f e w t = kl k g e w t;
  s_rebase : forall N M o (f : morph P N M o) K L K' L' (e1 : ext N M K L) (e2 : ext K L K' L') o' (w : olift o o') t,
    kl k f (ext_app e1 e2) w t = kl k (rebase_m e1 f) e2 w t;
  s_orebase : forall N M o (f : morph P N M o) K L (e : ext N M K L) o1 o2 (w1 : olift o o1) (w2 : olift o1 o2) t,
    kl k f e (ocomp w1 w2) t = kl k (orebase_m w1 f) e w2 t;
  s_unit : forall N K (e : ext N N K K) o o' (w : olift o o') t,
    kl k (fun K L e o' w v => tv (ext_var e v)) e w t = t;
  s_assoc : forall N M P' o (g : morph P M P' o) (f : morph P N M o) K L (e : ext N P' K L) o' (w : olift o o') t,
    kl k (fun K L e o' w v => kl k g (ext_right M e) w (f K (ext_mid M e) (ext_left M e) o' w v)) e w t
    = kl k g (ext_right M e) w (kl k f (ext_left M e) w t) }.

(** Another family over the same sort: the same laws, along [P]'s
    morphisms. *)
Record family_laws (P T : nat -> O -> Type) (tv : forall {N o}, var N -> P N o) (kp : kleisli_of P P)
    (k : kleisli_of P T) : Prop := {
  f_ext : forall N M o (f g : morph P N M o),
    (forall K L e o' w v, f K L e o' w v = g K L e o' w v) ->
    forall K L (e : ext N M K L) o' (w : olift o o') t, kl k f e w t = kl k g e w t;
  f_rebase : forall N M o (f : morph P N M o) K L K' L' (e1 : ext N M K L) (e2 : ext K L K' L') o' (w : olift o o') t,
    kl k f (ext_app e1 e2) w t = kl k (rebase_m e1 f) e2 w t;
  f_orebase : forall N M o (f : morph P N M o) K L (e : ext N M K L) o1 o2 (w1 : olift o o1) (w2 : olift o1 o2) t,
    kl k f e (ocomp w1 w2) t = kl k (orebase_m w1 f) e w2 t;
  f_unit : forall N K (e : ext N N K K) o o' (w : olift o o') t,
    kl k (fun K L e o' w v => tv (ext_var e v)) e w t = t;
  f_assoc : forall N M P' o (g : morph P M P' o) (f : morph P N M o) K L (e : ext N P' K L) o' (w : olift o o') t,
    kl k (fun K L e o' w v => kl kp g (ext_right M e) w (f K (ext_mid M e) (ext_left M e) o' w v)) e w t
    = kl k g (ext_right M e) w (kl k f (ext_left M e) w t) }.

End Generic.

(** ** System F *)

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

(** *** The type sort: types only have it ([O] is [unit]) *)

Definition Ty (K : nat) (_ : unit) : Type := ty K.

Fixpoint kl_ty {N M} (f : morph Ty N M tt) {K L} (e : ext N M K L) (A : ty K) : ty L :=
  match A with
  | tyvar v => f K L e tt tt v
  | tyarr A B => tyarr (kl_ty f e A) (kl_ty f e B)
  | tyall B => tyall (kl_ty f (ext_under e) B)
  end.

Definition ty_k : kleisli_of Ty Ty := mk_kleisli Ty Ty (fun N M o f K L e o' w A => kl_ty f e A).

(** The type sort over terms: the term scope [J] is a parameter. *)
Definition TmTy (J : nat) (K : nat) (_ : unit) : Type := tm K J.

Fixpoint kl_tmty {J N M} (f : morph Ty N M tt) {K L} (e : ext N M K L) (t : tm K J) : tm L J :=
  match t with
  | tmvar v => tmvar v
  | lam A b => lam (kl_ty f e A) (kl_tmty f e b)
  | app t u => app (kl_tmty f e t) (kl_tmty f e u)
  | tlam b => tlam (kl_tmty f (ext_under e) b)
  | tapp t A => tapp (kl_tmty f e t) (kl_ty f e A)
  end.

Definition tmty_k J : kleisli_of Ty (TmTy J) := mk_kleisli Ty (TmTy J) (fun N M o f K L e o' w t => kl_tmty f e t).

(** *** The term sort: the other sort is types *)

(** Terms as the term sort sees them: the term scope first, the type
    scope as the other scope. *)
Definition Tm (K : nat) (N : nat) : Type := tm N K.

(** The morphism goes under type binders too ([ext_under w]); nothing
    here weakens anything. *)
Fixpoint kl_tm {N M G} (f : morph Tm N M G) {K L} (e : ext N M K L) {J} (w : ext G G J J) (t : tm J K) : tm J L :=
  match t with
  | tmvar v => f K L e J w v
  | lam A b => lam A (kl_tm f (ext_under e) w b)
  | app t u => app (kl_tm f e w t) (kl_tm f e w u)
  | tlam b => tlam (kl_tm f e (ext_under w) b)
  | tapp t A => tapp (kl_tm f e w t) A
  end.

Definition tm_k : kleisli_of Tm Tm := mk_kleisli Tm Tm (fun N M o f K L e o' w t => kl_tm f e w t).

(** ** The laws: routine inductions *)

Section TyLaws.

Lemma kl_ty_ext N M (f g : morph Ty N M tt) :
  (forall K L e o' w v, f K L e o' w v = g K L e o' w v) ->
  forall K L (e : ext N M K L) A, kl_ty f e A = kl_ty g e A.
Proof. intros H K L e A; revert L e; induction A; intros L e; cbn; f_equal; auto. Qed.

Lemma kl_ty_rebase N M (f : morph Ty N M tt) K L K' L' (e1 : ext N M K L) (e2 : ext K L K' L') A :
  kl_ty f (ext_app e1 e2) A = kl_ty (rebase_m e1 f) e2 A.
Proof. revert L' e2; induction A; intros L' e2; cbn; f_equal; auto; rewrite <- IHA; reflexivity. Qed.

Lemma kl_ty_unit N K (e : ext N N K K) A : kl_ty (fun K L e o' w v => tyvar (ext_var e v)) e A = A.
Proof. induction A; cbn; f_equal; auto; apply ext_var_same. Qed.

Lemma kl_ty_assoc N M P' (g : morph Ty M P' tt) (f : morph Ty N M tt) K L (e : ext N P' K L) A :
  kl_ty (fun K L e o' w v => kl_ty g (ext_right M e) (f K (ext_mid M e) (ext_left M e) o' w v)) e A
  = kl_ty g (ext_right M e) (kl_ty f (ext_left M e) A).
Proof.
  revert L e; induction A; intros L e; cbn; f_equal; auto; rewrite <- IHA; reflexivity.
Qed.

End TyLaws.

(** The other-sort witnesses of [Ty] are [unit]: the laws for them hold
    because there is nothing to say. *)
Theorem ty_laws : sort_laws Ty (fun N o v => tyvar v) ty_k.
Proof.
  split; cbn.
  - intros; destruct o', w; reflexivity.
  - intros N M o f g H K L e o' w t; destruct o; apply kl_ty_ext; exact H.
  - intros; apply kl_ty_rebase.
  - intros; apply kl_ty_ext; intros K' L' e' x y v; destruct x, y; reflexivity.
  - intros; apply kl_ty_unit.
  - intros N M P' o g f K L e o' w t; destruct o, o', w; apply kl_ty_assoc.
Qed.

Section TmTyLaws.

Lemma kl_tmty_ext J N M (f g : morph Ty N M tt) :
  (forall K L e o' w v, f K L e o' w v = g K L e o' w v) ->
  forall K L (e : ext N M K L) (t : tm K J), kl_tmty f e t = kl_tmty g e t.
Proof.
  intros H K L e t; revert L e; induction t; intros L e; cbn; f_equal; auto; apply kl_ty_ext; exact H.
Qed.

Lemma kl_tmty_rebase J N M (f : morph Ty N M tt) K L K' L' (e1 : ext N M K L) (e2 : ext K L K' L') (t : tm K' J) :
  kl_tmty f (ext_app e1 e2) t = kl_tmty (rebase_m e1 f) e2 t.
Proof.
  revert L' e2; induction t; intros L' e2; cbn; f_equal; auto; try apply kl_ty_rebase.
  rewrite <- IHt; reflexivity.
Qed.

Lemma kl_tmty_unit J N K (e : ext N N K K) (t : tm K J) :
  kl_tmty (fun K L e o' w v => tyvar (ext_var e v)) e t = t.
Proof. induction t; cbn; f_equal; auto; apply kl_ty_unit. Qed.

Lemma kl_tmty_assoc J N M P' (g : morph Ty M P' tt) (f : morph Ty N M tt) K L (e : ext N P' K L) (t : tm K J) :
  kl_tmty (fun K L e o' w v => kl_ty g (ext_right M e) (f K (ext_mid M e) (ext_left M e) o' w v)) e t
  = kl_tmty g (ext_right M e) (kl_tmty f (ext_left M e) t).
Proof.
  revert L e; induction t; intros L e; cbn; f_equal; auto; try apply kl_ty_assoc;
    rewrite <- IHt; reflexivity.
Qed.

End TmTyLaws.

Theorem tmty_laws J : family_laws Ty (TmTy J) (fun N o v => tyvar v) ty_k (tmty_k J).
Proof.
  split; cbn.
  - intros N M o f g H K L e o' w t; destruct o; apply kl_tmty_ext; exact H.
  - intros; apply kl_tmty_rebase.
  - intros; apply kl_tmty_ext; intros K' L' e' x y v; destruct x, y; reflexivity.
  - intros; apply kl_tmty_unit.
  - intros N M P' o g f K L e o' w t; destruct o, o', w; apply kl_tmty_assoc.
Qed.

Section TmLaws.

Lemma kl_tm_ext N M G (f g : morph Tm N M G) :
  (forall K L e o' w v, f K L e o' w v = g K L e o' w v) ->
  forall K L (e : ext N M K L) J (w : ext G G J J) t, kl_tm f e w t = kl_tm g e w t.
Proof. intros H K L e J w t; revert L e; induction t; intros L e; cbn; f_equal; auto. Qed.

Lemma kl_tm_rebase N M G (f : morph Tm N M G) K L K' L' (e1 : ext N M K L) (e2 : ext K L K' L') J (w : ext G G J J) t :
  kl_tm f (ext_app e1 e2) w t = kl_tm (rebase_m e1 f) e2 w t.
Proof. revert L' e2; induction t; intros L' e2; cbn; f_equal; auto; rewrite <- IHt; reflexivity. Qed.

(** Going under type binders composes with the witness it starts from. *)
Lemma kl_tm_orebase N M G (f : morph Tm N M G) K L (e : ext N M K L) J1 J2 (w1 : ext G G J1 J1) (w2 : ext J1 J1 J2 J2) t :
  kl_tm f e (ext_app w1 w2) t = kl_tm (orebase_m (OS := others_one) w1 f) e w2 t.
Proof.
  revert L e; induction t; intros L e; cbn; f_equal; auto.
  apply (IHt (ext_under w2) L e).
Qed.

Lemma kl_tm_unit N K (e : ext N N K K) G J (w : ext G G J J) t :
  kl_tm (fun K L e o' w v => tmvar (ext_var e v)) e w t = t.
Proof. induction t; cbn; f_equal; auto; apply ext_var_same. Qed.

Lemma kl_tm_assoc N M P' G (g : morph Tm M P' G) (f : morph Tm N M G) K L (e : ext N P' K L) J (w : ext G G J J) t :
  kl_tm (fun K L e o' w v => kl_tm g (ext_right M e) w (f K (ext_mid M e) (ext_left M e) o' w v)) e w t
  = kl_tm g (ext_right M e) w (kl_tm f (ext_left M e) w t).
Proof. revert L e; induction t; intros L e; cbn; f_equal; auto; rewrite <- IHt; reflexivity. Qed.

End TmLaws.

Theorem tm_laws : sort_laws Tm (fun K N v => tmvar v) tm_k.
Proof.
  split; cbn.
  - reflexivity.
  - intros; apply kl_tm_ext; assumption.
  - intros; apply kl_tm_rebase.
  - intros; apply kl_tm_orebase.
  - intros; apply kl_tm_unit.
  - intros; apply kl_tm_assoc.
Qed.

(** ** What the library builds from these

    The weakening of a carrier along the other sorts' binders, from the
    carrier's Kleisli function for that sort and a weakening morphism
    built from the variable constructor alone.  For terms, along type
    binders: [oweak w u] sees a term over type base [G] over [J], for
    [w : ext G G J J].  The library's [apply a] would put it on each
    payload, at the witness the morphism is given, so that substituting
    under a type binder needs no shifting in the user's code.  It needs
    only the laws above. *)

(** Bound variables at or above the [D] binders crossed move up by [d]. *)
Definition wk_raw (D d : nat) (v : rvar) : rvar :=
  match v_label v with
  | None => if Nat.ltb (v_index v) D then v else mk_rvar None (v_index v + d)
  | Some _ => v
  end.

Lemma wk_wf {G J K L} (w : ext G G J J) (e : ext G J K L) v :
  wf_var K v = true -> wf_var L (wk_raw (Syntax.ext_depth e) (Syntax.ext_depth w) v) = true.
Proof.
  pose proof (Syntax.ext_depth_K e); pose proof (Syntax.ext_depth_L e); pose proof (Syntax.ext_depth_K w).
  destruct v as [[x|] i]; unfold wk_raw, wf_var; cbn [v_label v_index]; [reflexivity|].
  intros Hi; apply Nat.ltb_lt in Hi.
  destruct (Nat.ltb i (Syntax.ext_depth e)) eqn:E; cbn [v_label v_index]; apply Nat.ltb_lt;
    [apply Nat.ltb_lt in E|apply Nat.ltb_ge in E]; lia.
Qed.

Definition wk_m {G J} (w : ext G G J J) : morph Ty G J tt :=
  fun K L e _ _ v => tyvar (mk_var (wk_raw (Syntax.ext_depth e) (Syntax.ext_depth w) (var_raw v))
                                   (Is_true_s_intro (wk_wf w e _ (Is_true_s_elim (var_ok v))))).

Definition oweak {G J K} (w : ext G G J J) (u : tm G K) : tm J K := kl_tmty (wk_m w) ext_here u.

Lemma oweak_here {G K} (u : tm G K) : oweak ext_here u = u.
Proof.
  unfold oweak; transitivity (kl_tmty (fun K L e o' w v => tyvar (ext_var e v)) ext_here u);
    [apply kl_tmty_ext|apply kl_tmty_unit].
  intros K' L' e o' w v; unfold wk_m; f_equal; apply var_eq; cbn [var_raw ext_var Syntax.ext_depth].
  destruct (var_raw v) as [[x|] i]; unfold wk_raw; cbn [v_label v_index]; [reflexivity|].
  destruct (Nat.ltb i (Syntax.ext_depth e)); [reflexivity|]; rewrite Nat.add_0_r; reflexivity.
Qed.

Lemma oweak_comp {G J1 J2 K} (w1 : ext G G J1 J1) (w2 : ext J1 J1 J2 J2) (u : tm G K) :
  oweak (ext_app w1 w2) u = oweak w2 (oweak w1 u).
Proof.
  unfold oweak; etransitivity; [|exact (kl_tmty_assoc K G J1 J2 (wk_m w2) (wk_m w1) G J2 ext_here u)].
  apply kl_tmty_ext; intros K' L' e o' w v; unfold wk_m; cbn [kl_ty]; f_equal; apply var_eq;
    cbn [var_raw].
  rewrite Syntax.ext_depth_right, Syntax.ext_depth_left, Syntax.ext_depth_app.
  destruct (var_raw v) as [[x|] i]; unfold wk_raw; cbn [v_label v_index]; [reflexivity|].
  destruct (Nat.ltb i (Syntax.ext_depth e)) eqn:E; cbn [v_label v_index]; rewrite ?E; [reflexivity|].
  apply Nat.ltb_ge in E.
  replace (Nat.ltb (i + Syntax.ext_depth w1) (Syntax.ext_depth e)) with false
    by (symmetry; apply Nat.ltb_ge; lia).
  f_equal; lia.
Qed.
