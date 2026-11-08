(** * Laws of the context-form constructors

    Equations between adjustments built from [identity], [push_inner],
    [push_outer] and [compose], all stated with [=].  They are the rules the
    normaliser implements: entries with different labels commute, output
    entries move inside input entries, composition cancels an output entry
    against an input entry, and composition distributes over the
    constructors.

    Payloads need no side conditions: weakening a payload adjustment is
    composing it with [shift] ([pshift_as_pcompose]). *)

From Stdlib Require Import Arith List Lia Bool.
From ShiftedNames.Core Require Import Label Var Nested Adjustment.
Import ListNotations.

Section Laws.

Context {T : Type}.

Implicit Types (a b c : adjustment T) (ρ : padj T) (v w : var) (h l : option label)
  (t : target T).

(** ** Primitive adjustments as context forms *)

(** [shift l]: weaken by one [l]; every [l₍ᵢ₎] becomes [l₍ᵢ₊₁₎]. *)
Definition shift l : adjustment T := push_outer l identity.

(** [rename1 l1 l2]: the innermost [l1] becomes a new innermost [l2]. *)
Definition rename1 l1 l2 : adjustment T :=
  push_inner l1 (Rename (mk_var l2 0)) (shift l2).

(** Opening a bound variable as [x], and closing [x] into a bound variable. *)
Definition open (x : label) : adjustment T := rename1 None (Some x).
Definition close (x : label) : adjustment T := rename1 (Some x) None.

(** [swap l] exchanges the two innermost [l]s. *)
Definition swap l : adjustment T :=
  push_inner l (Rename (mk_var l 1)) (push_inner l (Rename (mk_var l 0)) (push_outer l (shift l))).

(** [subst1 l u ρ]: the innermost [l] is replaced by the payload [(u, ρ)]. *)
Definition subst1 l (u : T) ρ : adjustment T := push_inner l (Bind u ρ) identity.

Lemma apply_shift l v : apply (shift l) v = inl (shift_var (mk_var l 0) v).
Proof. unfold shift; rewrite apply_push_outer, apply_identity; reflexivity. Qed.

Lemma apply_rename1 l1 l2 v :
  apply (rename1 l1 l2) v
  = if var_eqb v (mk_var l1 0) then inl (mk_var l2 0)
    else inl (shift_var (mk_var l2 0) (unshift_var (mk_var l1 0) v)).
Proof.
  unfold rename1; rewrite apply_push_inner, apply_shift.
  destruct (var_eqb v (mk_var l1 0)); reflexivity.
Qed.

Lemma apply_subst1 l u ρ v :
  apply (subst1 l u ρ) v
  = if var_eqb v (mk_var l 0) then inr (u, ρ) else inl (unshift_var (mk_var l 0) v).
Proof.
  unfold subst1; rewrite apply_push_inner, apply_identity.
  destruct (var_eqb v (mk_var l 0)); reflexivity.
Qed.

(** ** Payload adjustments *)

Definition papply ρ v : result T := apply (padj_adj ρ) v.

(** Payload adjustments are equal when they act the same on free
    variables. *)
Theorem pextensionality ρ1 ρ2 :
  (forall v, v_label v <> None -> papply ρ1 v = papply ρ2 v) -> ρ1 = ρ2.
Proof.
  intros H; apply padj_eq, pcanonical;
    try first [apply padj_nnormal|apply padj_pnormal].
  intros v Hv; unfold papply in H.
  rewrite <- (lower_apply (padj_adj ρ1)), <- (lower_apply (padj_adj ρ2)), H by exact Hv.
  reflexivity.
Qed.

Lemma papply_depth ρ v u ρ' :
  papply ρ v = inr (u, ρ') -> ndepth (padj_n ρ') < ndepth (padj_n ρ).
Proof.
  intros H; pose proof (f_equal lower H) as H'; unfold papply in H'.
  rewrite lower_apply in H'; cbn [lower adj_n padj_adj fst snd] in H'.
  destruct (padj_n ρ) as [m] eqn:E.
  apply (ndepth_binds m (u, padj_n ρ')), (Slots.binds_in_apply m v), H'.
Qed.

Lemma papply_pcompose a ρ v :
  v_label v <> None ->
  papply (pcompose a ρ) v
  = match papply ρ v with
    | inl w => apply a w
    | inr p => inr (fst p, pcompose a (snd p))
    end.
Proof.
  intros Hv; unfold papply.
  rewrite <- apply_compose; apply lower_inj; rewrite !lower_apply.
  cbn [adj_n padj_adj pcompose padj_n compose].
  apply napply_prestrict; [|exact Hv].
  apply nnormal_ncompose; [apply adj_ok_true|apply padj_nnormal].
Qed.

Lemma papply_pshift h ρ v :
  v_label v <> None ->
  papply (pshift_p h ρ) v
  = match papply ρ v with
    | inl w => inl (shift_var (mk_var h 0) w)
    | inr p => inr (fst p, pshift_p h (snd p))
    end.
Proof.
  intros Hv; unfold papply; apply lower_inj; rewrite lower_apply.
  cbn [adj_n padj_adj pshift_p padj_n].
  rewrite napply_pshift by (try apply (nnormal_normal _ (padj_nnormal ρ)); exact Hv).
  pose proof (lower_apply (padj_adj ρ) v) as L; cbn [adj_n padj_adj] in L; rewrite <- L.
  destruct (apply (padj_adj ρ) v) as [w|[u ρ']]; reflexivity.
Qed.

Lemma pshift_as_pcompose_depth h n :
  forall ρ, ndepth (padj_n ρ) <= n -> pshift_p h ρ = pcompose (shift h) ρ.
Proof.
  induction n as [|n IH]; intros ρ Hd; [pose proof (ndepth_pos (padj_n ρ)); lia|].
  apply pextensionality; intros v Hv.
  rewrite papply_pshift, papply_pcompose by exact Hv.
  destruct (papply ρ v) as [w|[u ρ']] eqn:E.
  - rewrite apply_shift; reflexivity.
  - pose proof (papply_depth _ _ _ _ E); cbn [fst snd].
    rewrite (IH ρ') by lia; reflexivity.
Qed.

Theorem pshift_as_pcompose h ρ : pshift_p h ρ = pcompose (shift h) ρ.
Proof. apply (pshift_as_pcompose_depth h (ndepth (padj_n ρ))); lia. Qed.

Theorem push_outer_as_compose h a : push_outer h a = compose (shift h) a.
Proof.
  apply extensionality; intro v.
  rewrite apply_push_outer, apply_compose.
  destruct (apply a v) as [w|[u ρ]].
  - rewrite apply_shift; reflexivity.
  - rewrite pshift_as_pcompose; reflexivity.
Qed.

(** ** Reordering entries *)

Lemma unshift_var_comm h1 h2 v :
  h1 <> h2 ->
  unshift_var (mk_var h1 0) (unshift_var (mk_var h2 0) v)
  = unshift_var (mk_var h2 0) (unshift_var (mk_var h1 0) v).
Proof. destruct v as [h i]; unfold unshift_var; intro; case_vars. Qed.

Lemma shift_var_comm h1 h2 v :
  shift_var (mk_var h1 0) (shift_var (mk_var h2 0) v)
  = shift_var (mk_var h2 0) (shift_var (mk_var h1 0) v).
Proof.
  destruct (label_eq_dec h1 h2) as [->|Hne]; [reflexivity|].
  destruct v as [h i]; unfold shift_var; case_vars.
Qed.

Theorem push_inner_comm h1 h2 t1 t2 a :
  h1 <> h2 ->
  push_inner h1 t1 (push_inner h2 t2 a) = push_inner h2 t2 (push_inner h1 t1 a).
Proof.
  intros Hne; apply extensionality; intro v.
  rewrite !apply_push_inner.
  destruct v as [h i]; unfold var_eqb, unshift_var; cbn [v_label v_index].
  case_vars; rewrite ?apply_push_inner; unfold var_eqb, unshift_var;
    cbn [v_label v_index]; case_vars.
Qed.

Lemma compose_shift_comm h1 h2 :
  compose (shift h1) (shift h2) = compose (shift h2) (shift h1).
Proof.
  apply extensionality; intro v.
  rewrite !apply_compose, !apply_shift; f_equal; apply shift_var_comm.
Qed.

Theorem push_outer_comm h1 h2 a :
  push_outer h1 (push_outer h2 a) = push_outer h2 (push_outer h1 a).
Proof.
  rewrite !(push_outer_as_compose _ (push_outer _ a)), !(push_outer_as_compose _ a).
  rewrite !compose_assoc, compose_shift_comm; reflexivity.
Qed.

(** Moving a target past a new output entry [h]. *)
Definition shift_target h t : target T :=
  match t with
  | Rename w => Rename (shift_var (mk_var h 0) w)
  | Bind u ρ => Bind u (pshift_p h ρ)
  end.

(** Output entries move inside input entries; the target is shifted past the
    output entry. *)
Theorem push_outer_inner h h' t a :
  push_outer h (push_inner h' t a) = push_inner h' (shift_target h t) (push_outer h a).
Proof.
  apply extensionality; intro v.
  rewrite apply_push_outer, !apply_push_inner.
  destruct (var_eqb v (mk_var h' 0)).
  - destruct t; reflexivity.
  - rewrite apply_push_outer; reflexivity.
Qed.

(** ** Composition *)

(** Sending a target through an adjustment. *)
Definition apply_target a t : target T :=
  match t with
  | Rename w =>
      match apply a w with
      | inl u => Rename u
      | inr p => Bind (fst p) (snd p)
      end
  | Bind u ρ => Bind u (pcompose a ρ)
  end.

Theorem compose_push_inner_r a h t b :
  compose a (push_inner h t b) = push_inner h (apply_target a t) (compose a b).
Proof.
  apply extensionality; intro v.
  rewrite apply_compose, !apply_push_inner.
  destruct (var_eqb v (mk_var h 0)).
  - destruct t as [w|u ρ]; cbn; [|reflexivity].
    destruct (apply a w) as [u|[u ρ]]; reflexivity.
  - rewrite apply_compose; reflexivity.
Qed.

Theorem compose_push_outer_l h a b :
  compose (push_outer h a) b = push_outer h (compose a b).
Proof. rewrite !push_outer_as_compose, compose_assoc; reflexivity. Qed.

Lemma compose_push_inner_shift h t a : compose (push_inner h t a) (shift h) = a.
Proof.
  apply extensionality; intro v.
  rewrite apply_compose, apply_shift, apply_push_inner.
  destruct (var_eqb_spec (shift_var (mk_var h 0) v) (mk_var h 0)) as [E|E].
  - exfalso; destruct v as [h' i]; unfold shift_var in E; revert E; case_vars.
  - rewrite unshift_shift_var; reflexivity.
Qed.

(** An output entry is cancelled by an input entry with the same label. *)
Theorem compose_cancel h t a b :
  compose (push_inner h t a) (push_outer h b) = compose a b.
Proof.
  rewrite push_outer_as_compose, compose_assoc, compose_push_inner_shift; reflexivity.
Qed.

Theorem compose_identity_push_outer h b :
  compose (push_outer h identity) b = push_outer h b.
Proof. rewrite compose_push_outer_l, compose_identity_l; reflexivity. Qed.

(** ** Lifting *)

Theorem lift_identity l : lift l (@identity T) = identity.
Proof.
  apply extensionality; intro v.
  rewrite apply_lift, apply_identity.
  destruct (var_eqb_spec v (mk_var l 0)) as [->|Hne]; [reflexivity|].
  rewrite apply_identity, shift_unshift_var by exact Hne; reflexivity.
Qed.

Lemma compose_lift_shift l a : compose (lift l a) (shift l) = compose (shift l) a.
Proof.
  unfold lift; rewrite compose_push_inner_shift, push_outer_as_compose; reflexivity.
Qed.

Theorem lift_compose l a b : compose (lift l a) (lift l b) = lift l (compose a b).
Proof.
  apply extensionality; intro v.
  rewrite apply_compose, !apply_lift.
  destruct (var_eqb_spec v (mk_var l 0)) as [->|Hne].
  - rewrite apply_lift, var_eqb_refl; reflexivity.
  - rewrite apply_compose.
    destruct (apply b (unshift_var (mk_var l 0) v)) as [w|[u ρ]].
    + rewrite apply_lift.
      destruct (var_eqb_spec (shift_var (mk_var l 0) w) (mk_var l 0)) as [Heq|Hw].
      * exfalso; destruct w as [h i]; unfold shift_var in Heq; cbn in Heq.
        revert Heq; case_vars.
      * rewrite unshift_shift_var; reflexivity.
    + cbn [fst snd]; rewrite !pshift_as_pcompose, !pcompose_compose, compose_lift_shift.
      reflexivity.
Qed.

(** Going under a binder is free when the adjustment does not touch the
    binder's label: no entry for [l], no result labelled [l] from another
    label, and payloads unchanged by the shift.  The indexed layer uses this
    to skip [lift] when the indices guarantee these conditions. *)
Theorem lift_free l a :
  (forall i, apply a (mk_var l i) = inl (mk_var l i)) ->
  (forall v w, v_label v <> l -> apply a v = inl w -> v_label w <> l) ->
  (forall v p, apply a v = inr p -> pshift_p l (snd p) = snd p) ->
  lift l a = a.
Proof.
  intros Hl Hw Hp; apply extensionality; intro v.
  rewrite apply_lift.
  destruct (var_eqb_spec v (mk_var l 0)) as [->|Hne]; [symmetry; apply Hl|].
  destruct v as [h i]; destruct (label_eq_dec h l) as [->|Hhl].
  - destruct i as [|i]; [exfalso; apply Hne; reflexivity|].
    unfold unshift_var; cbn [v_label v_index]; rewrite label_eqb_refl.
    cbn [andb Nat.ltb Nat.leb]; replace (S i - 1) with i by lia.
    rewrite !Hl; unfold shift_var; cbn [v_label v_index].
    rewrite label_eqb_refl; reflexivity.
  - unfold unshift_var; cbn [v_label v_index].
    rewrite (proj2 (label_eqb_neq l h)) by congruence; cbn [andb].
    destruct (apply a (mk_var h i)) as [w|p] eqn:E.
    + unfold shift_var; cbn [v_label v_index].
      rewrite (proj2 (label_eqb_neq l (v_label w)))
        by (intro H; apply (Hw (mk_var h i) w Hhl E); symmetry; exact H).
      reflexivity.
    + rewrite (Hp _ _ E); destruct p; reflexivity.
Qed.

(** ** The primitives as context forms *)

Theorem shift_as_push_outer l : shift l = push_outer l (@identity T).
Proof. reflexivity. Qed.

Theorem rename1_as_context l1 l2 :
  rename1 l1 l2 = push_inner l1 (Rename (mk_var l2 0)) (push_outer l2 (@identity T)).
Proof. reflexivity. Qed.

Theorem subst1_as_context l u ρ : subst1 l u ρ = push_inner l (Bind u ρ) (@identity T).
Proof. reflexivity. Qed.

End Laws.
