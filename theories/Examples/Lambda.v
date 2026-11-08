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
From ShiftedNames.Core Require Import Label Var RawAdjustment Adjustment Laws.
From ShiftedNames.Examples Require Import LambdaScope.
From ShiftedNames.Examples Require LambdaCore.
Import ListNotations.

Module L := ShiftedNames.Examples.LambdaCore.

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

(** ** Extensionality for substitutions *)

Lemma sub_ext {N M} (s1 s2 : sub N M) :
  (forall v, wf_var N v = true -> apply (sub_raw s1) v = apply (sub_raw s2) v) ->
  s1 = s2.
Proof.
  intro H; apply sub_eq, (scoped_ext N M); auto using sub_scoped_true.
Qed.

(** Payloads of scoped substitutions are never bare variables. *)
Lemma sub_payload_not_var {N M} (s : sub N M) w p :
  apply (sub_raw s) w = inr p -> is_tvar p = false.
Proof.
  intro Hw; pose proof (sub_scoped_true s) as Hs.
  apply scoped_spec in Hs as [Hin Hout].
  destruct w as [[x|] i].
  - specialize (Hin (mk_var (Some x) i) eq_refl); rewrite Hw in Hin.
    cbn in Hin; apply andb_true_iff in Hin as [_ Hin]; apply negb_true_iff, Hin.
  - destruct (Nat.lt_ge_cases i N) as [Hi|Hi].
    + specialize (Hin (mk_var None i) (proj2 (Nat.ltb_lt _ _) Hi)); rewrite Hw in Hin.
      cbn in Hin; apply andb_true_iff in Hin as [_ Hin]; apply negb_true_iff, Hin.
    + rewrite Hout in Hw by exact Hi; discriminate.
Qed.

Lemma target_result_of (t : L.term) :
  target_result (target_of t) = match t with L.tvar w => inl w | _ => inr t end.
Proof. destruct t; reflexivity. Qed.

Lemma target_of_subst {N M} (s : sub N M) (t : L.term) :
  target_result (target_of (L.subst (sub_raw s) t))
  = match target_result (target_of t) with
    | inl w => apply (sub_raw s) w
    | inr p => inr (L.subst (sub_raw s) p)
    end.
Proof.
  destruct t as [w| | |]; cbn [L.subst target_of target_result]; try reflexivity.
  destruct (apply (sub_raw s) w) as [u|p] eqn:E; [reflexivity|].
  apply sub_payload_not_var in E; destruct p; cbn in *; congruence.
Qed.

Lemma shift_term_tvar w : L.shift_term (L.tvar w) = L.tvar (shift_var (mk_var None 0) w).
Proof. unfold L.shift_term; cbn [L.rename]; rewrite apply_shift; reflexivity. Qed.

Lemma shift_some_tvar x w :
  shift_term_some x (L.tvar w) = L.tvar (shift_var (mk_var (Some x) 0) w).
Proof. unfold shift_term_some; cbn [L.rename]; rewrite apply_shift; reflexivity. Qed.

(** ** Laws of the substitution constructors *)

Theorem comp_cons_bound {N M K} (s : sub M K) (t : tm M) (r : sub N M) :
  comp s (cons_bound t r) = cons_bound (⟦s⟧ t) (comp s r).
Proof.
  apply sub_ext; intros v _; cbn [comp cons_bound sub_raw subst tm_raw].
  rewrite apply_compose, !apply_push_inner.
  destruct (var_eqb v (mk_var None 0)); [|rewrite apply_compose; reflexivity].
  rewrite target_of_subst; destruct (target_result _); reflexivity.
Qed.

Theorem comp_cons_free {N M K} (s : sub M K) x (t : tm M) (r : sub N M) :
  comp s (cons_free x t r) = cons_free x (⟦s⟧ t) (comp s r).
Proof.
  apply sub_ext; intros v _; cbn [comp cons_free sub_raw subst tm_raw].
  rewrite apply_compose, !apply_push_inner.
  destruct (var_eqb v (mk_var (Some x) 0)); [|rewrite apply_compose; reflexivity].
  rewrite target_of_subst; destruct (target_result _); reflexivity.
Qed.

Theorem comp_weak_bound {N M K} (s : sub M K) (r : sub N M) :
  comp (weak_bound s) r = weak_bound (comp s r).
Proof.
  apply sub_ext; intros v _; cbn [comp weak_bound sub_raw].
  rewrite apply_compose, !apply_push_outer, apply_compose.
  destruct (apply (sub_raw r) v) as [w|p]; [apply apply_push_outer|].
  f_equal; cbn [push_outer].
  change (L.subst (Adjustment.compose L.shift_term (shift None) (sub_raw s)) p
          = L.shift_term (L.subst (sub_raw s) p)).
  unfold L.shift_term at 2; rewrite L.rename_subst; f_equal; try reflexivity;
  f_equal; apply extensionality; intro w;
  rewrite L.apply_of_renaming, !apply_shift; reflexivity.
Qed.

Theorem comp_weak_free {N M K} (s : sub M K) x (r : sub N M) :
  comp (weak_free x s) r = weak_free x (comp s r).
Proof.
  apply sub_ext; intros v _; cbn [comp weak_free sub_raw].
  rewrite apply_compose, !apply_push_outer, apply_compose.
  destruct (apply (sub_raw r) v) as [w|p]; [apply apply_push_outer|].
  f_equal; cbn [push_outer].
  change (L.subst (Adjustment.compose (shift_term_some x) (shift (Some x)) (sub_raw s)) p
          = shift_term_some x (L.subst (sub_raw s) p)).
  unfold shift_term_some at 2; rewrite L.rename_subst; f_equal; try reflexivity;
  f_equal; apply extensionality; intro w;
  rewrite L.apply_of_renaming, !apply_shift; reflexivity.
Qed.

Theorem cancel_bound {N M K} (s : sub M K) (t : tm K) (r : sub N M) :
  comp (cons_bound t s) (weak_bound r) = comp s r.
Proof.
  apply sub_eq; cbn [comp cons_bound weak_bound sub_raw].
  apply compose_cancel; intro p.
  change (L.subst (sub_raw s) p
          = L.subst (sub_raw (cons_bound t s)) (L.shift_term p)).
  unfold L.shift_term; rewrite L.subst_rename; f_equal.
  apply extensionality; intro w.
  rewrite apply_compose, L.apply_of_renaming, apply_shift; cbn [cons_bound sub_raw].
  rewrite apply_push_inner.
  destruct w as [h i]; unfold var_eqb, shift_var, unshift_var; cbn [v_label v_index].
  case_vars.
Qed.

Theorem cancel_free {N M K} (s : sub M K) x (t : tm K) (r : sub N M) :
  comp (cons_free x t s) (weak_free x r) = comp s r.
Proof.
  apply sub_eq; cbn [comp cons_free weak_free sub_raw].
  apply compose_cancel; intro p.
  change (L.subst (sub_raw s) p
          = L.subst (sub_raw (cons_free x t s)) (shift_term_some x p)).
  unfold shift_term_some; rewrite L.subst_rename; f_equal.
  apply extensionality; intro w.
  rewrite apply_compose, L.apply_of_renaming, apply_shift; cbn [cons_free sub_raw].
  rewrite apply_push_inner.
  destruct w as [h i]; unfold var_eqb, shift_var, unshift_var; cbn [v_label v_index].
  case_vars.
Qed.

Theorem lift_sid {N} : lift (@sid N) = sid.
Proof. apply sub_eq; apply lift_identity. Qed.

Theorem lift_comp {N M K} (s : sub M K) (r : sub N M) :
  comp (lift s) (lift r) = lift (comp s r).
Proof.
  apply sub_eq; cbn [comp sub_raw]; rewrite !lift_raw.
  apply lift_compose; intro p.
  apply L.subst_shift_term.
Qed.

(** ** Substitution on variables *)

Lemma subst_bvar {N M} (s : sub N M) i H :
  ⟦s⟧ (bvar i H) = mk_tm (match apply (sub_raw s) (mk_var None i) with
                          | inl w => L.tvar w
                          | inr p => p
                          end) (tm_wf (⟦s⟧ (bvar i H))).
Proof. apply tm_eq; reflexivity. Qed.

Theorem subst_cons_bound_0 {N M} (t : tm M) (s : sub N M) :
  ⟦cons_bound t s⟧ bvar0 = t.
Proof.
  apply tm_eq; cbn [subst cons_bound sub_raw tm_raw bvar0 bvar L.subst].
  rewrite apply_push_inner; cbn [var_eqb v_label v_index label_eqb Nat.eqb andb].
  rewrite target_result_of; destruct (tm_raw t); reflexivity.
Qed.

Theorem subst_cons_bound_S {N M} (t : tm M) (s : sub N M) i H :
  ⟦cons_bound t s⟧ (@bvar (S N) (S i) H) = ⟦s⟧ (@bvar N i H).
Proof.
  apply tm_eq; cbn [subst cons_bound sub_raw tm_raw bvar L.subst].
  rewrite apply_push_inner; cbn [var_eqb v_label v_index label_eqb Nat.eqb andb].
  unfold unshift_var; cbn [v_label v_index label_eqb Nat.ltb Nat.leb andb].
  replace (S i - 1) with i by lia; reflexivity.
Qed.

Theorem subst_cons_bound_fvar {N M} (t : tm M) (s : sub N M) x i :
  ⟦cons_bound t s⟧ (fvar x i) = ⟦s⟧ (fvar x i).
Proof. apply tm_eq; cbn; rewrite apply_push_inner; reflexivity. Qed.

Theorem subst_cons_free_0 {N M} x (t : tm M) (s : sub N M) :
  ⟦cons_free x t s⟧ (fvar x 0) = t.
Proof.
  apply tm_eq; cbn [subst cons_free sub_raw tm_raw fvar L.subst].
  rewrite apply_push_inner; unfold var_eqb; cbn [v_label v_index Nat.eqb].
  rewrite label_eqb_refl; cbn [andb].
  rewrite target_result_of; destruct (tm_raw t); reflexivity.
Qed.

Theorem subst_cons_free_S {N M} x (t : tm M) (s : sub N M) i :
  ⟦cons_free x t s⟧ (fvar x (S i)) = ⟦s⟧ (fvar x i).
Proof.
  apply tm_eq; cbn [subst cons_free sub_raw tm_raw fvar L.subst].
  rewrite apply_push_inner; unfold var_eqb, unshift_var; cbn [v_label v_index Nat.eqb].
  rewrite label_eqb_refl; cbn [andb Nat.ltb Nat.leb].
  replace (S i - 1) with i by lia; reflexivity.
Qed.

Theorem subst_cons_free_other {N M} x y (t : tm M) (s : sub N M) i :
  x <> y -> ⟦cons_free x t s⟧ (fvar y i) = ⟦s⟧ (fvar y i).
Proof.
  intro Hne; apply tm_eq; cbn [subst cons_free sub_raw tm_raw fvar L.subst].
  rewrite apply_push_inner; unfold var_eqb, unshift_var; cbn [v_label v_index].
  rewrite (proj2 (label_eqb_neq (Some y) (Some x))) by congruence.
  rewrite (proj2 (label_eqb_neq (Some x) (Some y))) by congruence.
  reflexivity.
Qed.

Theorem subst_cons_free_bvar {N M} x (t : tm M) (s : sub N M) i H :
  ⟦cons_free x t s⟧ (bvar i H) = ⟦s⟧ (bvar i H).
Proof. apply tm_eq; cbn; rewrite apply_push_inner; reflexivity. Qed.

Theorem subst_weak_bound {N M} (s : sub N M) t :
  ⟦weak_bound s⟧ t = ⟦weak_bound sid⟧ (⟦s⟧ t).
Proof. rewrite subst_comp, comp_weak_bound, comp_sid_l; reflexivity. Qed.

Theorem subst_weak_free {N M} x (s : sub N M) t :
  ⟦weak_free x s⟧ t = ⟦weak_free x sid⟧ (⟦s⟧ t).
Proof. rewrite subst_comp, comp_weak_free, comp_sid_l; reflexivity. Qed.
