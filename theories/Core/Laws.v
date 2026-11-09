(** * Laws of the context-form constructors

    Equations between adjustments built from [ridentity], [rpush_inner],
    [rpush_outer] and [rcompose], all stated with [=].  They are the rules the
    normaliser implements: entries with different labels commute, output
    entries move inside input entries, composition cancels an output entry
    against an input entry, and composition distributes over the
    constructors.

    Payloads need no side conditions: weakening a payload adjustment is
    composing it with [rshift] ([rpshift_as_pcompose]). *)

From Stdlib Require Import Arith List Lia Bool.
From ShiftedNames.Core Require Import Label Var Adjustment.
Import ListNotations.

Section Laws.

Context {T : Type}.

Implicit Types (a b c : radj T) (ρ : rpadj T) (v w : rvar) (h l : option label)
  (t : rtarget T).

(** ** Primitive adjustments as context forms *)

(** [rshift l]: weaken by one [l]; every [l₍ᵢ₎] becomes [l₍ᵢ₊₁₎]. *)
Definition rshift l : radj T := rpush_outer l ridentity.

(** [rrename1 l1 l2]: the innermost [l1] becomes a new innermost [l2]. *)
Definition rrename1 l1 l2 : radj T :=
  rpush_inner l1 (RRename (mk_rvar l2 0)) (rshift l2).

(** Opening a bound variable as [x], and closing [x] into a bound variable. *)
Definition ropen (x : label) : radj T := rrename1 None (Some x).
Definition rclose (x : label) : radj T := rrename1 (Some x) None.

(** [rswap l] exchanges the two innermost [l]s. *)
Definition rswap l : radj T :=
  rpush_inner l (RRename (mk_rvar l 1)) (rpush_inner l (RRename (mk_rvar l 0)) (rpush_outer l (rshift l))).

(** [rsubst1 l u ρ]: the innermost [l] is replaced by the payload [(u, ρ)]. *)
Definition rsubst1 l (u : T) ρ : radj T := rpush_inner l (RBind u ρ) ridentity.

Lemma rapply_shift l v : rapply (rshift l) v = inl (shift_rvar (mk_rvar l 0) v).
Proof. unfold rshift; rewrite rapply_push_outer, rapply_identity; reflexivity. Qed.

Lemma rapply_rename1 l1 l2 v :
  rapply (rrename1 l1 l2) v
  = if rvar_eqb v (mk_rvar l1 0) then inl (mk_rvar l2 0)
    else inl (shift_rvar (mk_rvar l2 0) (unshift_rvar (mk_rvar l1 0) v)).
Proof.
  unfold rrename1; rewrite rapply_push_inner, rapply_shift.
  destruct (rvar_eqb v (mk_rvar l1 0)); reflexivity.
Qed.

Lemma rapply_subst1 l u ρ v :
  rapply (rsubst1 l u ρ) v
  = if rvar_eqb v (mk_rvar l 0) then inr (u, ρ) else inl (unshift_rvar (mk_rvar l 0) v).
Proof.
  unfold rsubst1; rewrite rapply_push_inner, rapply_identity.
  destruct (rvar_eqb v (mk_rvar l 0)); reflexivity.
Qed.

Lemma rpshift_as_pcompose_depth h n :
  forall ρ, rpdepth ρ < n -> rpshift h ρ = rpcompose (rshift h) ρ.
Proof.
  induction n as [|n IH]; intros ρ Hd; [lia|].
  apply rpextensionality; intros v Hv.
  rewrite rpapply_pshift, rpapply_pcompose by exact Hv.
  destruct (rpapply ρ v) as [w|[u ρ']] eqn:E.
  - rewrite rapply_shift; reflexivity.
  - pose proof (rpdepth_payload _ _ _ _ Hv E).
    rewrite (IH ρ') by lia; reflexivity.
Qed.

Theorem rpshift_as_pcompose h ρ : rpshift h ρ = rpcompose (rshift h) ρ.
Proof. apply (rpshift_as_pcompose_depth h (S (rpdepth ρ))); lia. Qed.

Theorem rpush_outer_as_compose h a : rpush_outer h a = rcompose (rshift h) a.
Proof.
  apply rextensionality; intro v.
  rewrite rapply_push_outer, rapply_compose.
  destruct (rapply a v) as [w|[u ρ]].
  - rewrite rapply_shift; reflexivity.
  - rewrite rpshift_as_pcompose; reflexivity.
Qed.

(** ** Reordering entries *)

Lemma unshift_rvar_comm h1 h2 v :
  h1 <> h2 ->
  unshift_rvar (mk_rvar h1 0) (unshift_rvar (mk_rvar h2 0) v)
  = unshift_rvar (mk_rvar h2 0) (unshift_rvar (mk_rvar h1 0) v).
Proof. destruct v as [h i]; unfold unshift_rvar; intro; case_vars. Qed.

Lemma shift_rvar_comm h1 h2 v :
  shift_rvar (mk_rvar h1 0) (shift_rvar (mk_rvar h2 0) v)
  = shift_rvar (mk_rvar h2 0) (shift_rvar (mk_rvar h1 0) v).
Proof.
  destruct (label_eq_dec h1 h2) as [->|Hne]; [reflexivity|].
  destruct v as [h i]; unfold shift_rvar; case_vars.
Qed.

Theorem rpush_inner_comm h1 h2 t1 t2 a :
  h1 <> h2 ->
  rpush_inner h1 t1 (rpush_inner h2 t2 a) = rpush_inner h2 t2 (rpush_inner h1 t1 a).
Proof.
  intros Hne; apply rextensionality; intro v.
  rewrite !rapply_push_inner.
  destruct v as [h i]; unfold rvar_eqb, unshift_rvar; cbn [v_label v_index].
  case_vars; rewrite ?rapply_push_inner; unfold rvar_eqb, unshift_rvar;
    cbn [v_label v_index]; case_vars.
Qed.

Lemma rcompose_shift_comm h1 h2 :
  rcompose (rshift h1) (rshift h2) = rcompose (rshift h2) (rshift h1).
Proof.
  apply rextensionality; intro v.
  rewrite !rapply_compose, !rapply_shift; f_equal; apply shift_rvar_comm.
Qed.

Theorem rpush_outer_comm h1 h2 a :
  rpush_outer h1 (rpush_outer h2 a) = rpush_outer h2 (rpush_outer h1 a).
Proof.
  rewrite !(rpush_outer_as_compose _ (rpush_outer _ a)), !(rpush_outer_as_compose _ a).
  rewrite !rcompose_assoc, rcompose_shift_comm; reflexivity.
Qed.

(** Moving a target past a new output entry [h]. *)
Definition rshift_target h t : rtarget T :=
  match t with
  | RRename w => RRename (shift_rvar (mk_rvar h 0) w)
  | RBind u ρ => RBind u (rpshift h ρ)
  end.

(** Output entries move inside input entries; the target is shifted past the
    output entry. *)
Theorem rpush_outer_inner h h' t a :
  rpush_outer h (rpush_inner h' t a) = rpush_inner h' (rshift_target h t) (rpush_outer h a).
Proof.
  apply rextensionality; intro v.
  rewrite rapply_push_outer, !rapply_push_inner.
  destruct (rvar_eqb v (mk_rvar h' 0)).
  - destruct t; reflexivity.
  - rewrite rapply_push_outer; reflexivity.
Qed.

(** ** Composition *)

(** Sending a target through an adjustment. *)
Definition rapply_target a t : rtarget T :=
  match t with
  | RRename w =>
      match rapply a w with
      | inl u => RRename u
      | inr p => RBind (fst p) (snd p)
      end
  | RBind u ρ => RBind u (rpcompose a ρ)
  end.

Theorem rcompose_push_inner_r a h t b :
  rcompose a (rpush_inner h t b) = rpush_inner h (rapply_target a t) (rcompose a b).
Proof.
  apply rextensionality; intro v.
  rewrite rapply_compose, !rapply_push_inner.
  destruct (rvar_eqb v (mk_rvar h 0)).
  - destruct t as [w|u ρ]; cbn; [|reflexivity].
    destruct (rapply a w) as [u|[u ρ]]; reflexivity.
  - rewrite rapply_compose; reflexivity.
Qed.

Theorem rcompose_push_outer_l h a b :
  rcompose (rpush_outer h a) b = rpush_outer h (rcompose a b).
Proof. rewrite !rpush_outer_as_compose, rcompose_assoc; reflexivity. Qed.

Lemma rcompose_push_inner_shift h t a : rcompose (rpush_inner h t a) (rshift h) = a.
Proof.
  apply rextensionality; intro v.
  rewrite rapply_compose, rapply_shift, rapply_push_inner.
  destruct (rvar_eqb_spec (shift_rvar (mk_rvar h 0) v) (mk_rvar h 0)) as [E|E].
  - exfalso; destruct v as [h' i]; unfold shift_rvar in E; revert E; case_vars.
  - rewrite unshift_shift_rvar; reflexivity.
Qed.

(** An output entry is cancelled by an input entry with the same label. *)
Theorem rcompose_cancel h t a b :
  rcompose (rpush_inner h t a) (rpush_outer h b) = rcompose a b.
Proof.
  rewrite rpush_outer_as_compose, rcompose_assoc, rcompose_push_inner_shift; reflexivity.
Qed.

Theorem rcompose_identity_push_outer h b :
  rcompose (rpush_outer h ridentity) b = rpush_outer h b.
Proof. rewrite rcompose_push_outer_l, rcompose_identity_l; reflexivity. Qed.

(** ** Lifting *)

Theorem rlift_identity l : rlift l (@ridentity T) = ridentity.
Proof.
  apply rextensionality; intro v.
  rewrite rapply_lift, rapply_identity.
  destruct (rvar_eqb_spec v (mk_rvar l 0)) as [->|Hne]; [reflexivity|].
  rewrite rapply_identity, shift_unshift_rvar by exact Hne; reflexivity.
Qed.

Lemma rcompose_lift_shift l a : rcompose (rlift l a) (rshift l) = rcompose (rshift l) a.
Proof.
  unfold rlift; rewrite rcompose_push_inner_shift, rpush_outer_as_compose; reflexivity.
Qed.

Theorem rlift_compose l a b : rcompose (rlift l a) (rlift l b) = rlift l (rcompose a b).
Proof.
  apply rextensionality; intro v.
  rewrite rapply_compose, !rapply_lift.
  destruct (rvar_eqb_spec v (mk_rvar l 0)) as [->|Hne].
  - rewrite rapply_lift, rvar_eqb_refl; reflexivity.
  - rewrite rapply_compose.
    destruct (rapply b (unshift_rvar (mk_rvar l 0) v)) as [w|[u ρ]].
    + rewrite rapply_lift.
      destruct (rvar_eqb_spec (shift_rvar (mk_rvar l 0) w) (mk_rvar l 0)) as [Heq|Hw].
      * exfalso; destruct w as [h i]; unfold shift_rvar in Heq; cbn in Heq.
        revert Heq; case_vars.
      * rewrite unshift_shift_rvar; reflexivity.
    + cbn [fst snd]; rewrite !rpshift_as_pcompose, !rpcompose_compose, rcompose_lift_shift.
      reflexivity.
Qed.

(** Going under a binder is free when the adjustment does not touch the
    binder's label: no entry for [l], no result labelled [l] from another
    label, and payloads unchanged by the shift.  The indexed layer uses this
    to skip [rlift] when the indices guarantee these conditions. *)
Theorem rlift_free l a :
  (forall i, rapply a (mk_rvar l i) = inl (mk_rvar l i)) ->
  (forall v w, v_label v <> l -> rapply a v = inl w -> v_label w <> l) ->
  (forall v p, rapply a v = inr p -> rpshift l (snd p) = snd p) ->
  rlift l a = a.
Proof.
  intros Hl Hw Hp; apply rextensionality; intro v.
  rewrite rapply_lift.
  destruct (rvar_eqb_spec v (mk_rvar l 0)) as [->|Hne]; [symmetry; apply Hl|].
  destruct v as [h i]; destruct (label_eq_dec h l) as [->|Hhl].
  - destruct i as [|i]; [exfalso; apply Hne; reflexivity|].
    unfold unshift_rvar; cbn [v_label v_index]; rewrite label_eqb_refl.
    cbn [andb Nat.ltb Nat.leb]; replace (S i - 1) with i by lia.
    rewrite !Hl; unfold shift_rvar; cbn [v_label v_index].
    rewrite label_eqb_refl; reflexivity.
  - unfold unshift_rvar; cbn [v_label v_index].
    rewrite (proj2 (label_eqb_neq l h)) by congruence; cbn [andb].
    destruct (rapply a (mk_rvar h i)) as [w|p] eqn:E.
    + unfold shift_rvar; cbn [v_label v_index].
      rewrite (proj2 (label_eqb_neq l (v_label w)))
        by (intro H; apply (Hw (mk_rvar h i) w Hhl E); symmetry; exact H).
      reflexivity.
    + destruct p as [u ρ]; pose proof (Hp _ _ E) as Hq; cbn [snd] in Hq; rewrite Hq; reflexivity.
Qed.

(** ** The primitives as context forms *)

Theorem rshift_as_push_outer l : rshift l = rpush_outer l (@ridentity T).
Proof. reflexivity. Qed.

Theorem rrename1_as_context l1 l2 :
  rrename1 l1 l2 = rpush_inner l1 (RRename (mk_rvar l2 0)) (rpush_outer l2 (@ridentity T)).
Proof. reflexivity. Qed.

Theorem rsubst1_as_context l u ρ : rsubst1 l u ρ = rpush_inner l (RBind u ρ) (@ridentity T).
Proof. reflexivity. Qed.

(** ** Opening and closing *)

Theorem rcompose_open_close x : rcompose (ropen x) (rclose x) = @ridentity T.
Proof.
  apply rextensionality; intro v.
  rewrite rapply_compose, rapply_identity; unfold ropen, rclose; rewrite !rapply_rename1.
  destruct v as [h i]; unfold rvar_eqb, shift_rvar, unshift_rvar; cbn [v_label v_index].
  case_vars; rewrite ?rapply_rename1; unfold rvar_eqb, shift_rvar, unshift_rvar;
    cbn [v_label v_index]; case_vars.
Qed.

Theorem rcompose_close_open x : rcompose (rclose x) (ropen x) = @ridentity T.
Proof.
  apply rextensionality; intro v.
  rewrite rapply_compose, rapply_identity; unfold ropen, rclose; rewrite !rapply_rename1.
  destruct v as [h i]; unfold rvar_eqb, shift_rvar, unshift_rvar; cbn [v_label v_index].
  case_vars; rewrite ?rapply_rename1; unfold rvar_eqb, shift_rvar, unshift_rvar;
    cbn [v_label v_index]; case_vars.
Qed.

End Laws.
