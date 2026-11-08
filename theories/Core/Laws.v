(** * Laws of the context-form constructors

    Equations between adjustments built from [identity], [push_inner],
    [push_outer] and [compose], all stated with [=].  They are the rules the
    normaliser implements: entries with different labels commute, output
    entries move inside input entries, composition cancels an output entry
    against an input entry, and composition distributes over the
    constructors.

    Payloads appear only through the functions passed to [compose] and
    [push_outer]; for renamings (no payloads) the side conditions on them are
    trivial. *)

From Stdlib Require Import Arith List Lia Bool.
From ShiftedNames.Core Require Import Label Var RawAdjustment Adjustment.
Import ListNotations.

Section Laws.

Context {P : Type}.

Implicit Types (a b : adjustment P) (v w : var) (h l : option label)
  (t : target P) (fp sp : P -> P).

(** Moving a target past a new output entry [h]. *)
Definition shift_target sp h t : target P :=
  match t with
  | Rename w => Rename (shift_var (mk_var h 0) w)
  | Bind p => Bind (sp p)
  end.

(** Sending a target through an adjustment. *)
Definition apply_target fp a t : target P :=
  match t with
  | Rename w =>
      match apply a w with
      | inl u => Rename u
      | inr p => Bind p
      end
  | Bind p => Bind (fp p)
  end.

Lemma target_result_shift_target sp h t :
  target_result (shift_target sp h t)
  = match target_result t with
    | inl w => inl (shift_var (mk_var h 0) w)
    | inr p => inr (sp p)
    end.
Proof. destruct t; reflexivity. Qed.

Lemma target_result_apply_target fp a t :
  target_result (apply_target fp a t)
  = match target_result t with
    | inl w => apply a w
    | inr p => inr (fp p)
    end.
Proof. destruct t as [w|p]; cbn; [destruct (apply a w)|]; reflexivity. Qed.

(** ** Reordering entries *)

Lemma unshift_var_comm h1 h2 v :
  h1 <> h2 ->
  unshift_var (mk_var h1 0) (unshift_var (mk_var h2 0) v)
  = unshift_var (mk_var h2 0) (unshift_var (mk_var h1 0) v).
Proof. destruct v as [h i]; unfold unshift_var; intro; case_vars. Qed.

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

Theorem push_outer_comm sp1 sp2 h1 h2 a :
  h1 <> h2 -> (forall p, sp1 (sp2 p) = sp2 (sp1 p)) ->
  push_outer sp1 h1 (push_outer sp2 h2 a) = push_outer sp2 h2 (push_outer sp1 h1 a).
Proof.
  intros Hne Hsp; apply extensionality; intro v.
  rewrite !apply_push_outer.
  destruct (apply a v) as [[h i]|p]; [|rewrite Hsp; reflexivity].
  unfold shift_var; cbn [v_label v_index]; case_vars.
Qed.

(** Output entries move inside input entries; the target is shifted past the
    output entry. *)
Theorem push_outer_inner sp h h' t a :
  push_outer sp h (push_inner h' t a)
  = push_inner h' (shift_target sp h t) (push_outer sp h a).
Proof.
  apply extensionality; intro v.
  rewrite apply_push_outer, !apply_push_inner.
  destruct (var_eqb v (mk_var h' 0)).
  - rewrite target_result_shift_target; reflexivity.
  - rewrite apply_push_outer; reflexivity.
Qed.

(** ** Composition *)

Theorem compose_push_inner_r fp a h t b :
  compose fp a (push_inner h t b) = push_inner h (apply_target fp a t) (compose fp a b).
Proof.
  apply extensionality; intro v.
  rewrite apply_compose, !apply_push_inner.
  destruct (var_eqb v (mk_var h 0)).
  - rewrite target_result_apply_target; reflexivity.
  - rewrite apply_compose; reflexivity.
Qed.

Theorem compose_push_outer_l fp fp' sp h a b :
  (forall p, fp p = sp (fp' p)) ->
  compose fp (push_outer sp h a) b = push_outer sp h (compose fp' a b).
Proof.
  intros Hfp; apply extensionality; intro v.
  rewrite apply_compose, !apply_push_outer, apply_compose.
  destruct (apply b v) as [w|p]; [apply apply_push_outer|rewrite Hfp; reflexivity].
Qed.

(** An output entry is cancelled by an input entry with the same label. *)
Theorem compose_cancel fp fp' sp h t a b :
  (forall p, fp' p = fp (sp p)) ->
  compose fp (push_inner h t a) (push_outer sp h b) = compose fp' a b.
Proof.
  intros Hfp; apply extensionality; intro v.
  rewrite !apply_compose, apply_push_outer.
  destruct (apply b v) as [[l i]|p]; [|rewrite Hfp; reflexivity].
  rewrite apply_push_inner.
  unfold var_eqb, shift_var, unshift_var; cbn [v_label v_index].
  case_vars.
Qed.

Theorem compose_identity_push_outer sp h b :
  compose sp (push_outer sp h identity) b = push_outer sp h b.
Proof.
  apply extensionality; intro v.
  rewrite apply_compose, !apply_push_outer.
  destruct (apply b v); [|reflexivity].
  rewrite apply_push_outer, apply_identity; reflexivity.
Qed.

(** ** Lifting *)

Theorem lift_identity sp l : lift sp l (@identity P) = identity.
Proof.
  apply extensionality; intro v.
  rewrite apply_lift, apply_identity.
  destruct (var_eqb_spec v (mk_var l 0)) as [->|Hne]; [reflexivity|].
  rewrite apply_identity, shift_unshift_var by exact Hne; reflexivity.
Qed.

Theorem lift_compose fp fp' sp l a b :
  (forall p, fp' (sp p) = sp (fp p)) ->
  compose fp' (lift sp l a) (lift sp l b) = lift sp l (compose fp a b).
Proof.
  intros Hsp; apply extensionality; intro v.
  rewrite apply_compose, !apply_lift.
  destruct (var_eqb_spec v (mk_var l 0)) as [->|Hne].
  - rewrite apply_lift, var_eqb_refl; reflexivity.
  - rewrite apply_compose.
    destruct (apply b (unshift_var (mk_var l 0) v)) as [w|p].
    + rewrite apply_lift.
      destruct (var_eqb_spec (shift_var (mk_var l 0) w) (mk_var l 0)) as [Heq|Hw].
      * exfalso; destruct w as [h i]; unfold shift_var in Heq; cbn in Heq.
        revert Heq; case_vars.
      * rewrite unshift_shift_var; reflexivity.
    + rewrite Hsp; reflexivity.
Qed.

Theorem map_payload_lift {Q} (f : P -> Q) sp sq l a :
  (forall p, f (sp p) = sq (f p)) ->
  map_payload f (lift sp l a) = lift sq l (map_payload f a).
Proof.
  intros Hf; apply extensionality; intro v.
  rewrite apply_map_payload, !apply_lift.
  destruct (var_eqb v (mk_var l 0)); [reflexivity|].
  rewrite apply_map_payload.
  destruct (apply a _); [reflexivity|rewrite Hf; reflexivity].
Qed.

(** ** The primitives as context forms *)

Theorem shift_as_push_outer sp l : shift l = push_outer sp l (@identity P).
Proof.
  apply extensionality; intro v.
  rewrite apply_shift, apply_push_outer, apply_identity; reflexivity.
Qed.

Theorem rename1_as_context sp l1 l2 :
  rename1 l1 l2 = push_inner l1 (Rename (mk_var l2 0)) (push_outer sp l2 (@identity P)).
Proof.
  apply extensionality; intro v.
  rewrite apply_rename1, apply_push_inner, apply_push_outer, apply_identity.
  destruct (var_eqb v (mk_var l1 0)); reflexivity.
Qed.

Theorem subst1_as_context l p : subst1 l p = push_inner l (Bind p) (@identity P).
Proof.
  apply extensionality; intro v.
  unfold subst1; rewrite apply_capture, apply_push_inner, apply_identity.
  reflexivity.
Qed.

End Laws.
