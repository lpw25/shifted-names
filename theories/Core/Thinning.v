(** * Thinnings

    A thinning is an order-preserving embedding of bound-variable indices,
    written as a string of keeps ([true]) and drops ([false]) read from the
    innermost variable outwards, followed implicitly by keeps forever:

    - [keep :: θ] maps [0] to [0] and [S i] to [S (θ i)] (going under a
      binder: [lift]);
    - [drop :: θ] maps [i] to [S (θ i)] (weakening by a bound variable).

    A thinning is canonical when it has no trailing keep; [tkeep] is the
    smart constructor that maintains this.  Canonical thinnings with the same
    action are equal ([thinning_canonical]). *)

From Stdlib Require Import Arith List Lia Bool.
From ShiftedNames.Core Require Import Label Var.
Import ListNotations.

Definition thinning := list bool.

Fixpoint thin (θ : thinning) (i : nat) : nat :=
  match θ with
  | [] => i
  | true :: θ' => match i with 0 => 0 | S i' => S (thin θ' i') end
  | false :: θ' => S (thin θ' i)
  end.

(** Canonical form: no trailing keep. *)
Fixpoint canonical_thinning (θ : thinning) : bool :=
  match θ with
  | [] => true
  | [true] => false
  | _ :: θ' => canonical_thinning θ'
  end.

Definition tkeep (θ : thinning) : thinning :=
  match θ with [] => [] | _ => true :: θ end.

Definition tdrop (θ : thinning) : thinning := false :: θ.

Lemma thin_tkeep θ i :
  thin (tkeep θ) i = match i with 0 => 0 | S i' => S (thin θ i') end.
Proof. destruct θ, i; reflexivity. Qed.

Lemma thin_tdrop θ i : thin (tdrop θ) i = S (thin θ i).
Proof. reflexivity. Qed.

Lemma canonical_tkeep θ : canonical_thinning θ = true -> canonical_thinning (tkeep θ) = true.
Proof. destruct θ as [|b θ]; [reflexivity|]; intro H; exact H. Qed.

Lemma canonical_tdrop θ : canonical_thinning θ = true -> canonical_thinning (tdrop θ) = true.
Proof. destruct θ as [|b θ]; [reflexivity|]; intro H; exact H. Qed.

Lemma canonical_cons_inv b θ :
  canonical_thinning (b :: θ) = true -> canonical_thinning θ = true.
Proof. destruct θ as [|b' θ]; [reflexivity|]; destruct b; intro H; exact H. Qed.

(** ** Composition: [tcompose θ1 θ2] is [θ2] followed by [θ1]. *)

Fixpoint tcompose (θ1 θ2 : thinning) {struct θ1} : thinning :=
  match θ1, θ2 with
  | [], _ => θ2
  | _, [] => θ1
  | false :: θ1', _ => tdrop (tcompose θ1' θ2)
  | true :: θ1', true :: θ2' => tkeep (tcompose θ1' θ2')
  | true :: θ1', false :: θ2' => tdrop (tcompose θ1' θ2')
  end.

Theorem thin_tcompose θ1 θ2 i : thin (tcompose θ1 θ2) i = thin θ1 (thin θ2 i).
Proof.
  revert θ2 i; induction θ1 as [|[|] θ1 IH]; intros θ2 i; [reflexivity| |].
  - destruct θ2 as [|[|] θ2]; [reflexivity| |].
    + cbn [tcompose]; rewrite thin_tkeep.
      destruct i; cbn [thin]; [reflexivity|rewrite IH; reflexivity].
    + cbn [tcompose]; rewrite thin_tdrop, IH; reflexivity.
  - cbn [tcompose]; destruct θ2; rewrite ?thin_tdrop, ?IH; reflexivity.
Qed.

Theorem canonical_tcompose θ1 θ2 :
  canonical_thinning θ1 = true -> canonical_thinning θ2 = true ->
  canonical_thinning (tcompose θ1 θ2) = true.
Proof.
  revert θ2; induction θ1 as [|[|] θ1 IH]; intros θ2 H1 H2; [exact H2| |].
  - destruct θ2 as [|[|] θ2]; [exact H1| |]; cbn [tcompose].
    + apply canonical_tkeep, IH; eapply canonical_cons_inv; eassumption.
    + apply canonical_tdrop, IH; eapply canonical_cons_inv; eassumption.
  - destruct θ2; cbn [tcompose]; apply canonical_tdrop.
    + apply canonical_cons_inv in H1; exact H1.
    + apply IH; [eapply canonical_cons_inv; eassumption|exact H2].
Qed.

(** ** Canonicity *)

Lemma thin_ge θ i : i <= thin θ i.
Proof.
  revert i; induction θ as [|[|] θ IH]; intro i; cbn [thin]; [lia| |].
  - destruct i; [lia|specialize (IH i); lia].
  - specialize (IH i); lia.
Qed.

(** A canonical non-empty thinning moves some index. *)
Lemma canonical_nonempty_moves θ :
  canonical_thinning θ = true -> θ <> [] -> exists i, thin θ i <> i.
Proof.
  induction θ as [|[|] θ IH]; intros Hc Hne; [contradiction| |].
  - destruct θ as [|b θ']; [discriminate|].
    destruct (IH Hc ltac:(discriminate)) as [i Hi].
    exists (S i); cbn [thin]; intro H; apply Hi; injection H; auto.
  - exists 0; cbn [thin]; pose proof (thin_ge θ 0); lia.
Qed.

Theorem thinning_canonical θ1 θ2 :
  canonical_thinning θ1 = true -> canonical_thinning θ2 = true ->
  (forall i, thin θ1 i = thin θ2 i) -> θ1 = θ2.
Proof.
  revert θ2; induction θ1 as [|b1 θ1 IH]; intros θ2 H1 H2 Heq.
  - destruct θ2 as [|b2 θ2]; [reflexivity|].
    destruct (canonical_nonempty_moves _ H2 ltac:(discriminate)) as [i Hi].
    exfalso; apply Hi; symmetry; apply Heq.
  - destruct θ2 as [|b2 θ2].
    + destruct (canonical_nonempty_moves _ H1 ltac:(discriminate)) as [i Hi].
      exfalso; apply Hi; apply Heq.
    + pose proof (canonical_cons_inv _ _ H1) as H1'.
      pose proof (canonical_cons_inv _ _ H2) as H2'.
      destruct b1, b2.
      * f_equal; apply IH; auto.
        intro i; specialize (Heq (S i)); cbn [thin] in Heq; injection Heq; auto.
      * specialize (Heq 0); cbn [thin] in Heq; discriminate.
      * specialize (Heq 0); cbn [thin] in Heq; discriminate.
      * f_equal; apply IH; auto.
        intro i; specialize (Heq i); cbn [thin] in Heq; injection Heq; auto.
Qed.

(** ** Action on variables: thinnings act on bound variables only. *)

Definition thin_var (θ : thinning) (v : var) : var :=
  match v_label v with
  | None => mk_var None (thin θ (v_index v))
  | Some _ => v
  end.

Lemma thin_var_tcompose θ1 θ2 v :
  thin_var (tcompose θ1 θ2) v = thin_var θ1 (thin_var θ2 v).
Proof.
  destruct v as [[x|] i]; unfold thin_var; cbn [v_label v_index]; [reflexivity|].
  rewrite thin_tcompose; reflexivity.
Qed.

Lemma thin_var_nil v : thin_var [] v = v.
Proof. destruct v as [[x|] i]; reflexivity. Qed.
