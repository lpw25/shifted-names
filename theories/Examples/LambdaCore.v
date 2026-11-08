(** * A concrete λ-calculus over shifted names (unindexed)

    Variables are shifted names; [tlam] binds the anonymous label (bound
    variables are [None₍ᵢ₎]).  Renaming and substitution act through
    adjustments, and the laws of the substitution calculus hold with
    Leibniz equality, by induction on terms plus the adjustment laws.

    This is the internal, unindexed layer; the user-facing layer will be
    scoped (see docs/implementation-plan.md, D6). *)

From Stdlib Require Import Arith List Lia Bool.
From ShiftedNames.Core Require Import Label Var RawAdjustment Adjustment Laws.

Inductive term : Type :=
| tvar (v : var)
| tconst (n : nat)
| tapp (t1 t2 : term)
| tlam (b : term).

(** ** Renaming *)

Definition renaming := adjustment Empty_set.

Fixpoint rename (r : renaming) (t : term) : term :=
  match t with
  | tvar v =>
      match apply r v with
      | inl w => tvar w
      | inr e => match e with end
      end
  | tconst n => tconst n
  | tapp t1 t2 => tapp (rename r t1) (rename r t2)
  | tlam b => tlam (rename (lift no_payload None r) b)
  end.

Definition rcompose (r1 r2 : renaming) : renaming := compose no_payload r1 r2.

Theorem rename_identity t : rename identity t = t.
Proof.
  induction t as [v|n|t1 IH1 t2 IH2|b IH]; cbn [rename].
  - rewrite apply_identity; reflexivity.
  - reflexivity.
  - rewrite IH1, IH2; reflexivity.
  - rewrite lift_identity, IH; reflexivity.
Qed.

Theorem rename_rename r1 r2 t :
  rename r1 (rename r2 t) = rename (rcompose r1 r2) t.
Proof.
  revert r1 r2; induction t as [v|n|t1 IH1 t2 IH2|b IH]; intros r1 r2;
    cbn [rename].
  - unfold rcompose; rewrite apply_compose.
    destruct (apply r2 v) as [w|[]]; reflexivity.
  - reflexivity.
  - rewrite IH1, IH2; reflexivity.
  - rewrite IH; unfold rcompose.
    rewrite (lift_compose no_payload) by (intros []); reflexivity.
Qed.

(** Lifting a renaming commutes with weakening by the binder. *)
Lemma lift_shift (r : renaming) :
  rcompose (lift no_payload None r) (shift None) = rcompose (shift None) r.
Proof.
  apply extensionality; intro v; unfold rcompose.
  rewrite !apply_compose, apply_shift, apply_lift.
  destruct (var_eqb_spec (shift_var (mk_var None 0) v) (mk_var None 0)) as [Heq|Hne].
  - exfalso; destruct v as [h i]; unfold shift_var in Heq; revert Heq; case_vars.
  - rewrite unshift_shift_var.
    destruct (apply r v) as [w|[]]; rewrite apply_shift; reflexivity.
Qed.

(** ** Substitution *)

Definition shift_term (t : term) : term := rename (shift None) t.

Fixpoint subst (s : adjustment term) (t : term) : term :=
  match t with
  | tvar v =>
      match apply s v with
      | inl w => tvar w
      | inr u => u
      end
  | tconst n => tconst n
  | tapp t1 t2 => tapp (subst s t1) (subst s t2)
  | tlam b => tlam (subst (lift shift_term None s) b)
  end.

Definition of_renaming (r : renaming) : adjustment term :=
  map_payload (fun e : Empty_set => match e with end) r.

Lemma apply_of_renaming r v :
  apply (of_renaming r) v = match apply r v with inl w => inl w | inr e => match e with end end.
Proof.
  unfold of_renaming; rewrite apply_map_payload.
  destruct (apply r v) as [w|[]]; reflexivity.
Qed.

Lemma lift_of_renaming r :
  lift shift_term None (of_renaming r) = of_renaming (lift no_payload None r).
Proof. symmetry; apply map_payload_lift; intros []. Qed.

Theorem subst_of_renaming r t : subst (of_renaming r) t = rename r t.
Proof.
  revert r; induction t as [v|n|t1 IH1 t2 IH2|b IH]; intro r; cbn [subst rename].
  - rewrite apply_of_renaming; destruct (apply r v) as [w|[]]; reflexivity.
  - reflexivity.
  - rewrite IH1, IH2; reflexivity.
  - rewrite lift_of_renaming, IH; reflexivity.
Qed.

Theorem subst_identity t : subst identity t = t.
Proof.
  induction t as [v|n|t1 IH1 t2 IH2|b IH]; cbn [subst].
  - rewrite apply_identity; reflexivity.
  - reflexivity.
  - rewrite IH1, IH2; reflexivity.
  - rewrite lift_identity, IH; reflexivity.
Qed.

Theorem rename_subst r s t :
  rename r (subst s t) = subst (compose (rename r) (of_renaming r) s) t.
Proof.
  revert r s; induction t as [v|n|t1 IH1 t2 IH2|b IH]; intros r s;
    cbn [subst rename].
  - rewrite apply_compose.
    destruct (apply s v) as [w|u]; [|reflexivity].
    cbn [rename]; rewrite apply_of_renaming.
    destruct (apply r w) as [w'|[]]; reflexivity.
  - reflexivity.
  - rewrite IH1, IH2; reflexivity.
  - rewrite IH; f_equal; f_equal.
    rewrite <- lift_of_renaming.
    apply lift_compose; intro p.
    unfold shift_term; rewrite !rename_rename, lift_shift; reflexivity.
Qed.

Theorem subst_rename s r t :
  subst s (rename r t) = subst (compose (fun u => u) s (of_renaming r)) t.
Proof.
  revert s r; induction t as [v|n|t1 IH1 t2 IH2|b IH]; intros s r;
    cbn [subst rename].
  - rewrite apply_compose, apply_of_renaming.
    destruct (apply r v) as [w|[]]; reflexivity.
  - reflexivity.
  - rewrite IH1, IH2; reflexivity.
  - rewrite IH; f_equal; f_equal.
    rewrite <- lift_of_renaming.
    apply lift_compose; intro p. reflexivity.
Qed.

(** Substituting under a binder commutes with weakening by it. *)
Lemma subst_shift_term s p :
  subst (lift shift_term None s) (shift_term p) = shift_term (subst s p).
Proof.
  change (shift_term p) with (rename (shift None) p).
  change (shift_term (subst s p)) with (rename (shift None) (subst s p)).
  rewrite subst_rename, rename_subst.
  f_equal; apply extensionality; intro v.
  rewrite !apply_compose, !apply_of_renaming, apply_shift.
  rewrite apply_lift.
  destruct (var_eqb_spec (shift_var (mk_var None 0) v) (mk_var None 0)) as [Heq|Hne].
  - exfalso; destruct v as [h i]; unfold shift_var in Heq; revert Heq; case_vars.
  - rewrite unshift_shift_var.
    destruct (apply s v) as [w|u]; [|reflexivity].
    rewrite apply_of_renaming, apply_shift; reflexivity.
Qed.

Theorem subst_subst s1 s2 t :
  subst s1 (subst s2 t) = subst (compose (subst s1) s1 s2) t.
Proof.
  revert s1 s2; induction t as [v|n|t1 IH1 t2 IH2|b IH]; intros s1 s2;
    cbn [subst].
  - rewrite apply_compose.
    destruct (apply s2 v) as [w|u]; reflexivity.
  - reflexivity.
  - rewrite IH1, IH2; reflexivity.
  - rewrite IH; f_equal; f_equal.
    apply lift_compose; intro p.
    apply subst_shift_term.
Qed.

(** ** Substitution without lifting

    [subst_nolift s] goes under binders without lifting [s].  It agrees with
    [subst s] whenever lifting [s] is free ([lift_free]); the indexed layer
    uses it when the indices guarantee that. *)

Fixpoint subst_nolift (s : adjustment term) (t : term) : term :=
  match t with
  | tvar v =>
      match apply s v with
      | inl w => tvar w
      | inr u => u
      end
  | tconst n => tconst n
  | tapp t1 t2 => tapp (subst_nolift s t1) (subst_nolift s t2)
  | tlam b => tlam (subst_nolift s b)
  end.

Theorem subst_nolift_spec s t :
  lift shift_term None s = s -> subst_nolift s t = subst s t.
Proof.
  intro Hs; induction t as [v|n|t1 IH1 t2 IH2|b IH]; cbn [subst_nolift subst];
    [reflexivity|reflexivity|rewrite IH1, IH2; reflexivity|].
  rewrite Hs, IH; reflexivity.
Qed.
