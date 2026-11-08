(** * Scoped λ-terms and substitutions (public layer)

    [tm N] is the type of λ-terms with at most [N] bound variables in scope
    and any free names.  [sub N M] is the type of substitutions from scope
    [N] to scope [M].  Users work only with these types, their constructor
    functions, and the laws below; the unindexed core is not visible.

    Terms:          [fvar x i], [bvar i], [app t1 t2], [lam b], [const n].
    Substitutions:  [sid], [cons_bound t σ], [cons_free x t σ],
                    [weak_bound σ], [weak_free x σ], [comp σ τ], and the
                    derived [lift σ], [open_sub x], [close_sub x].

    Equality on both types is Leibniz equality: two substitutions are equal
    exactly when they act the same on all in-scope variables. *)

From Stdlib Require Import Arith List Lia Bool StrictProp.
From ShiftedNames.Core Require Import Label Var RawAdjustment Adjustment Laws Scope.
From ShiftedNames.Core Require Lambda.
Import ListNotations.

Module L := ShiftedNames.Core.Lambda.

(** ** Terms *)

Record tm (N : nat) : Type :=
  mk_tm { tm_raw : L.term; tm_wf : Is_true_s (wf_term N tm_raw) }.

Arguments mk_tm {N} _ _.
Arguments tm_raw {N} _.
Arguments tm_wf {N} _.

Lemma tm_eq {N} (t1 t2 : tm N) : tm_raw t1 = tm_raw t2 -> t1 = t2.
Proof. destruct t1, t2; cbn; intros ->; reflexivity. Qed.

Lemma tm_wf_true {N} (t : tm N) : wf_term N (tm_raw t) = true.
Proof. apply Is_true_s_elim, tm_wf. Qed.

Definition fvar {N} (x : label) (i : nat) : tm N :=
  mk_tm (L.tvar (mk_var (Some x) i)) stt.

Definition bvar {N} (i : nat) (H : Is_true_s (Nat.ltb i N)) : tm N :=
  mk_tm (L.tvar (mk_var None i)) H.

Definition app {N} (t1 t2 : tm N) : tm N :=
  mk_tm (L.tapp (tm_raw t1) (tm_raw t2))
    (Is_true_s_intro (proj2 (andb_true_iff _ _) (conj (tm_wf_true t1) (tm_wf_true t2)))).

Definition lam {N} (b : tm (S N)) : tm N := mk_tm (L.tlam (tm_raw b)) (tm_wf b).

Definition const {N} (n : nat) : tm N := mk_tm (L.tconst n) stt.

(** The innermost bound variable. *)
Definition bvar0 {N} : tm (S N) := @bvar (S N) 0 stt.

(** ** Substitutions *)

Record sub (N M : nat) : Type :=
  mk_sub { sub_raw : adjustment L.term; sub_scoped : Is_true_s (scoped N M sub_raw) }.

Arguments mk_sub {N M} _ _.
Arguments sub_raw {N M} _.
Arguments sub_scoped {N M} _.

Lemma sub_eq {N M} (s1 s2 : sub N M) : sub_raw s1 = sub_raw s2 -> s1 = s2.
Proof. destruct s1, s2; cbn; intros ->; reflexivity. Qed.

Lemma sub_scoped_true {N M} (s : sub N M) : scoped N M (sub_raw s) = true.
Proof. apply Is_true_s_elim, sub_scoped. Qed.

(** Applying a substitution to a term. *)
Definition subst {N M} (s : sub N M) (t : tm N) : tm M :=
  mk_tm (L.subst (sub_raw s) (tm_raw t))
    (Is_true_s_intro
       (wf_subst N M _ _ (scoped_maps_ok _ _ _ (sub_scoped_true s)) (tm_wf_true t))).

Notation "⟦ s ⟧ t" := (subst s t) (at level 9, right associativity, format "⟦ s ⟧  t").

(** A term as the target of a substitution entry: variables are renamings,
    everything else is a payload. *)
Definition target_of (t : L.term) : target L.term :=
  match t with
  | L.tvar w => Rename w
  | _ => Bind t
  end.

Lemma target_ok_target_of M t : wf_term M t = true -> target_ok M (target_of t) = true.
Proof.
  destruct t; cbn [target_of target_ok target_result result_ok wf_term is_tvar];
    intro H; rewrite ?H; reflexivity.
Qed.

Definition sid {N} : sub N N := mk_sub identity (Is_true_s_intro (scoped_identity N)).

Definition cons_bound {N M} (t : tm M) (s : sub N M) : sub (S N) M :=
  mk_sub (push_inner None (target_of (tm_raw t)) (sub_raw s))
    (Is_true_s_intro
       (scoped_push_inner_bound N M _ _ (sub_scoped_true s)
          (target_ok_target_of M _ (tm_wf_true t)))).

Definition cons_free {N M} (x : label) (t : tm M) (s : sub N M) : sub N M :=
  mk_sub (push_inner (Some x) (target_of (tm_raw t)) (sub_raw s))
    (Is_true_s_intro
       (scoped_push_inner_free N M x _ _ (sub_scoped_true s)
          (target_ok_target_of M _ (tm_wf_true t)))).

Definition weak_bound {N M} (s : sub N M) : sub N (S M) :=
  mk_sub (push_outer L.shift_term None (sub_raw s))
    (Is_true_s_intro (scoped_push_outer_bound N M _ (sub_scoped_true s))).

Definition weak_free {N M} (x : label) (s : sub N M) : sub N M :=
  mk_sub (push_outer (shift_term_some x) (Some x) (sub_raw s))
    (Is_true_s_intro (scoped_push_outer_free N M x _ (sub_scoped_true s))).

Definition comp {N M K} (s : sub M K) (t : sub N M) : sub N K :=
  mk_sub (compose (L.subst (sub_raw s)) (sub_raw s) (sub_raw t))
    (Is_true_s_intro (scoped_compose N M K _ _ (sub_scoped_true s) (sub_scoped_true t))).

(** Moving a substitution under a binder. *)
Definition lift {N M} (s : sub N M) : sub (S N) (S M) := cons_bound bvar0 (weak_bound s).

(** Opening the innermost bound variable as the free name [x], and closing
    the innermost [x] into a bound variable. *)
Definition open_sub {N} (x : label) : sub (S N) N := cons_bound (fvar x 0) (weak_free x sid).
Definition close_sub {N} (x : label) : sub N (S N) := cons_free x bvar0 (weak_bound sid).

(** ** Substitution on term constructors *)

Lemma subst_app {N M} (s : sub N M) t1 t2 : ⟦s⟧ (app t1 t2) = app (⟦s⟧ t1) (⟦s⟧ t2).
Proof. apply tm_eq; reflexivity. Qed.

Lemma subst_const {N M} (s : sub N M) n : ⟦s⟧ (const n) = const n.
Proof. apply tm_eq; reflexivity. Qed.

(** The core's lifting coincides with [lift]. *)
Lemma lift_raw {N M} (s : sub N M) :
  sub_raw (lift s) = Adjustment.lift L.shift_term None (sub_raw s).
Proof. reflexivity. Qed.

Lemma subst_lam {N M} (s : sub N M) b : ⟦s⟧ (lam b) = lam (⟦lift s⟧ b).
Proof. apply tm_eq; reflexivity. Qed.

(** ** The substitution laws *)

Theorem subst_sid {N} (t : tm N) : ⟦sid⟧ t = t.
Proof. apply tm_eq; apply L.subst_identity. Qed.

Theorem subst_comp {N M K} (s : sub M K) (r : sub N M) t : ⟦s⟧ (⟦r⟧ t) = ⟦comp s r⟧ t.
Proof. apply tm_eq; apply L.subst_subst. Qed.

Theorem comp_sid_l {N M} (s : sub N M) : comp sid s = s.
Proof.
  apply sub_eq; cbn [comp sid sub_raw].
  apply compose_identity_l; apply L.subst_identity.
Qed.

Theorem comp_sid_r {N M} (s : sub N M) : comp s sid = s.
Proof. apply sub_eq; apply compose_identity_r. Qed.

Theorem comp_assoc {N M K J} (s1 : sub K J) (s2 : sub M K) (s3 : sub N M) :
  comp s1 (comp s2 s3) = comp (comp s1 s2) s3.
Proof.
  apply sub_eq; cbn [comp sub_raw].
  apply compose_assoc; [reflexivity|].
  intro p; apply L.subst_subst.
Qed.
