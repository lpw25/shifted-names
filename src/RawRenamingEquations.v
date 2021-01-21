Require Import Label PeanoNat Psatz Ring
        Compare_dec StrictProp  Setoid Morphisms.
Require Import Var VarEquations RawRenaming.

(* Raw renamings form a semigroup *)

Lemma raw_renaming_left_identity r :
  compose_raw_renaming raw_renaming_id r = r.
Proof. easy. Qed.

Lemma raw_renaming_right_identity r :
  compose_raw_renaming r raw_renaming_id = r.
Proof.
  induction r as [|vl r IHr vr]; cbn; try easy.
  rewrite IHr; easy.
Qed.

Fixpoint transpose_push_raw_renaming_push v r {struct r} :=
  match r with
  | raw_renaming_id => v
  | raw_renaming_extend vl r vr =>
    if var_eqb v vl then vr
    else shift_var vr
           (transpose_push_raw_renaming_push
              (unshift_var vl v) r)
  end.

Lemma rhs_push_transpose_push_raw_renaming v r :
  rhs_push (transpose_push_raw_renaming v r)
  = transpose_push_raw_renaming_push v r.
Proof.
  generalize dependent v.
  induction r as [|vl r IHr vr]; intros v; cbn; try easy.
  case_vars_eq v vl; try easy.
  rewrite IHr; easy.
Qed.

Fixpoint transpose_push_raw_renaming_raw_renaming
         v r {struct r} :=
  match r with
  | raw_renaming_id => raw_renaming_id
  | raw_renaming_extend vl r vr =>
    if var_eqb v vl then r
    else
      raw_renaming_extend
        (unshift_var v vl)
        (transpose_push_raw_renaming_raw_renaming
           (unshift_var vl v) r)
        (unshift_var
           (transpose_push_raw_renaming_push
              (unshift_var vl v) r)
           vr)

  end.

Lemma rhs_raw_renaming_transpose_push_raw_renaming v r :
  rhs_raw_renaming (transpose_push_raw_renaming v r)
  = transpose_push_raw_renaming_raw_renaming v r.
Proof.
  generalize dependent v.
  induction r as [|vl r IHr vr]; intros v; cbn; try easy.
  case_vars_eq v vl; try easy.
  rewrite rhs_push_transpose_push_raw_renaming, IHr; easy.
Qed.

Lemma renaming_rhs_eta r :
  r = mk_renaming_rhs (rhs_raw_renaming r) (rhs_push r).
Proof. easy. Qed.

Lemma transpose_push_raw_renaming_eta vo r :
  transpose_push_raw_renaming vo r
  = mk_renaming_rhs
      (transpose_push_raw_renaming_raw_renaming vo r)
      (transpose_push_raw_renaming_push vo r).
Proof.
  rewrite renaming_rhs_eta
    with (r := transpose_push_raw_renaming vo r).
  rewrite rhs_raw_renaming_transpose_push_raw_renaming.
  rewrite rhs_push_transpose_push_raw_renaming.
  easy.
Qed.

Lemma transpose_push_raw_renaming_reverse_right v1 v2 r :
  shift_var (transpose_push_raw_renaming_push v1 r)
    (transpose_push_raw_renaming_push v2
       (transpose_push_raw_renaming_raw_renaming v1 r)) =
  transpose_push_raw_renaming_push (shift_var v1 v2) r.
Proof.
  generalize dependent v1.
  generalize dependent v2.
  induction r as [|vl r IHr vr]; intros v2 v1; cbn; try easy.
  case_vars_eq v1 vl as Heq1 Hneq1.
  - rewrite var_eqb_false by apply irreducible_transposed_1.
    rewrite reducible_transposed_2 with (v1 := v2) by easy.
    easy.
  - case_vars_eq (shift_var v1 v2) vl as Heq2 Hneq2.
    + apply reducible_transposed_2 in Heq2 as Heq3;
        reduce_vars.
      apply transpose_pushes_squared_right.
    + apply irreducible_transposed_3 in Hneq2 as Hneq3;
        try easy; reduce_vars.
      rewrite transpose_pushes_reverse_right.
      rewrite IHr.
      rewrite transpose_push_push_pop_reverse_right
        by congruence; easy.
Qed.

Lemma transpose_push_raw_renaming_reverse_middle v1 v2 r :
  unshift_var
    (transpose_push_raw_renaming_push
       v1 (transpose_push_raw_renaming_raw_renaming v2 r))
    (transpose_push_raw_renaming_push v2 r)
  = transpose_push_raw_renaming_push
      (unshift_var v1 v2)
      (transpose_push_raw_renaming_raw_renaming
         (shift_var v2 v1) r).
Proof.
  generalize dependent v1.
  generalize dependent v2.
  induction r as [|vl r IHr vr]; intros v2 v1; cbn; try easy.
  case_vars_eq v2 vl as Heq1 Hneq1.
  - rewrite var_eqb_false
      by apply irreducible_transposed_1; cbn.
    rewrite var_eqb_true
      by apply transpose_reducible_push_pop.
    rewrite reducible_transposed_2
      with (v2 := v2) (v1 := v1) by easy.
    easy.
  - case_vars_eq (shift_var v2 v1) vl as Heq2 Hneq2.
    + apply reducible_transposed_2 in Heq2 as Heq3;
        reduce_vars.
      rewrite transpose_pushes_squared_left.
      rewrite <- transpose_reducible_push_pop.
      easy.
    + apply irreducible_transposed_3 in Hneq2 as Hneq3;
        try easy; reduce_vars.
      rewrite var_eqb_false
        by (apply transpose_irreducible_push_pop; easy).
      rewrite transpose_pushes_reverse_middle.
      rewrite IHr.
      rewrite transpose_push_raw_renaming_reverse_right.
      rewrite transpose_push_push_pop_reverse_middle.
      rewrite transpose_push_push_pop_reverse_right
        by congruence.
      easy.
Qed.

Lemma transpose_push_raw_renaming_reverse_left v1 v2 r :
  transpose_push_raw_renaming_raw_renaming v1
    (transpose_push_raw_renaming_raw_renaming v2 r)
  = transpose_push_raw_renaming_raw_renaming
      (unshift_var v1 v2)
      (transpose_push_raw_renaming_raw_renaming
         (shift_var v2 v1) r).
Proof.
  generalize dependent v1.
  generalize dependent v2.
  induction r as [|vl r IHr vr]; intros v2 v1; cbn; try easy.
  case_vars_eq v2 vl as Heq1 Hneq1.
  - rewrite var_eqb_false
      by apply irreducible_transposed_1; cbn.
    rewrite var_eqb_true
      by apply transpose_reducible_push_pop.
    rewrite reducible_transposed_2
      with (v2 := v2) (v1 := v1) by easy.
    easy.
  - case_vars_eq (shift_var v2 v1) vl as Heq2 Hneq2.
    + apply reducible_transposed_2 in Heq2 as Heq3;
        reduce_vars.
      rewrite <- transpose_reducible_push_pop.
      easy.
    + apply irreducible_transposed_3 in Hneq2 as Hneq3;
        try easy; reduce_vars.
      rewrite var_eqb_false
        by (apply transpose_irreducible_push_pop; easy).
      rewrite transpose_push_push_pop_reverse_left.
      rewrite IHr.
      rewrite <- transpose_pushes_reverse_left
        with (v3 := vr).
      rewrite transpose_push_raw_renaming_reverse_right.
      rewrite transpose_push_raw_renaming_reverse_middle.
      rewrite transpose_push_push_pop_reverse_middle.
      rewrite transpose_push_push_pop_reverse_right
        by congruence.
      easy.
Qed.

Lemma transpose_push_compose_raw_renaming_push r1 r2 v :
  transpose_push_raw_renaming_push
    v (compose_raw_renaming r1 r2)
  = transpose_push_raw_renaming_push
      (transpose_push_raw_renaming_push v r1) r2.
Proof.
  generalize dependent v.
  generalize dependent r2.
  induction r1 as [|vl r1 IHr1 vr]; intros v2 v1; cbn; try easy.
  rewrite rhs_push_transpose_push_raw_renaming,
    rhs_raw_renaming_transpose_push_raw_renaming.
  case_vars_eq v1 vl; try easy.
  rewrite IHr1.
  apply transpose_push_raw_renaming_reverse_right.
Qed.

Lemma transpose_push_compose_raw_renaming_raw_renaming r1 r2 v :
  transpose_push_raw_renaming_raw_renaming
    v (compose_raw_renaming r1 r2)
  = compose_raw_renaming
      (transpose_push_raw_renaming_raw_renaming v r1)
      (transpose_push_raw_renaming_raw_renaming
         (transpose_push_raw_renaming_push v r1) r2).
Proof.
  generalize dependent v.
  generalize dependent r2.
  induction r1 as [|vl r1 IHr1 vr]; intros r2 v; cbn; try easy.
  rewrite rhs_push_transpose_push_raw_renaming,
    rhs_raw_renaming_transpose_push_raw_renaming.
  case_vars_eq v vl; try easy.
  rewrite IHr1.
  rewrite transpose_push_raw_renaming_reverse_left.
  rewrite transpose_push_compose_raw_renaming_push.
  rewrite transpose_push_raw_renaming_reverse_middle.
  rewrite rhs_push_transpose_push_raw_renaming,
    rhs_raw_renaming_transpose_push_raw_renaming.
  easy.
Qed.

Lemma raw_renaming_associative r1 r2 r3 :
  compose_raw_renaming r1 (compose_raw_renaming r2 r3)
  = compose_raw_renaming (compose_raw_renaming r1 r2) r3.
Proof.
  generalize dependent r2.
  generalize dependent r3.
  induction r1; cbn; intros r3 r2; try easy.
  rewrite !rhs_push_transpose_push_raw_renaming,
    !rhs_raw_renaming_transpose_push_raw_renaming.
  rewrite transpose_push_compose_raw_renaming_raw_renaming.
  rewrite IHr1.
  rewrite transpose_push_compose_raw_renaming_push.
  easy.
Qed.

(* Composition of matching extensions *)

Lemma compose_raw_renaming_extend v1 r1 v2 r2 v3 :
  compose_raw_renaming
    (raw_renaming_extend v1 r1 v2)
    (raw_renaming_extend v2 r2 v3)
  = raw_renaming_extend v1 (compose_raw_renaming r1 r2) v3.
Proof.
  cbn; rewrite var_eqb_true by easy; cbn.
  easy.
Qed.

(* [apply_raw_renaming] is a semigroup action *)

Definition apply_renaming_rhs_var r : var_op 0 1 :=
  lift_var_op (apply_raw_renaming_var (rhs_raw_renaming r))
  @ push_var (rhs_push r).
Arguments apply_renaming_rhs_var r /.

Lemma apply_transpose_push_raw_renaming v r :
  push_var v
  @ apply_raw_renaming_var r
  =v=
  apply_renaming_rhs_var (transpose_push_raw_renaming v r).
Proof.
  generalize dependent v.
  induction r as [|vl r IHr vr]; intros v; cbn.
  - simplify_var_ops; easy.
  - case_vars_eq v vl.
    + rewrite push_pop_identity'; easy.
    + rewrite transpose_push_pop' by easy.
      simplify_var_ops.
      rewrite <- lift_var_op_compose'.
      rewrite IHr; cbn; simplify_var_ops.
      rewrite transpose_swap_lifted'.
      rewrite transpose_pushes.
      rewrite swap_swap_identity'.
      easy.
Qed.

Lemma apply_compose_raw_renaming r1 r2 :
  apply_raw_renaming_var (compose_raw_renaming r1 r2)
  =v= apply_raw_renaming_var r1 @ apply_raw_renaming_var r2.
Proof.
  generalize dependent r2.
  induction r1 as [|vl r1 IHr1 vr]; intros r2; cbn; try easy.
  rewrite IHr1; simplify_var_ops.
  rewrite apply_transpose_push_raw_renaming.
  easy.
Qed.

Lemma apply_compose_raw_renaming' {N} r1 r2 (op : var_op N 0) :
  apply_raw_renaming_var (compose_raw_renaming r1 r2) @ op
  =v= apply_raw_renaming_var r1
      @ (apply_raw_renaming_var r2 @ op).
Proof.
  rewrite apply_compose_raw_renaming, var_op_associative.
  easy.
Qed.

Lemma apply_compose_raw_renaming_v r1 r2 v :
  apply_raw_renaming_var (compose_raw_renaming r1 r2) v
  = apply_raw_renaming_var r1 (apply_raw_renaming_var r2 v).
Proof. apply apply_compose_raw_renaming. Qed.

Lemma apply_inverse_raw_renaming_left r :
  apply_raw_renaming_var (inverse_raw_renaming r)
  @ apply_raw_renaming_var r
  =v= 1.
Proof.
  induction r as [|vl r IHr vr];
    cbn; try easy; simplify_var_ops.
  rewrite push_pop_identity'.
  rewrite <- lift_var_op_compose'.
  rewrite IHr; simplify_var_ops.
  rewrite pop_push_identity.
  easy.
Qed.

Lemma apply_inverse_raw_renaming_left' {N} r (op : var_op N 0) :
  apply_raw_renaming_var (inverse_raw_renaming r)
  @ (apply_raw_renaming_var r @ op)
  =v= op.
Proof.
  rewrite var_op_associative, apply_inverse_raw_renaming_left,
    var_op_left_identity.
  easy.
Qed.

Lemma apply_inverse_raw_renaming_left_v r v :
  apply_raw_renaming_var (inverse_raw_renaming r)
    (apply_raw_renaming_var r v) = v.
Proof. apply apply_inverse_raw_renaming_left. Qed.

Lemma apply_inverse_raw_renaming_right r :
  apply_raw_renaming_var r
  @ apply_raw_renaming_var (inverse_raw_renaming r)
  =v= 1.
Proof.
  induction r as [|vl r IHr vr];
    cbn; try easy; simplify_var_ops.
  rewrite push_pop_identity'.
  rewrite <- lift_var_op_compose'.
  rewrite IHr; simplify_var_ops.
  rewrite pop_push_identity.
  easy.
Qed.

Lemma apply_inverse_raw_renaming_right' {N} r (op : var_op N 0) :
  apply_raw_renaming_var r
  @ (apply_raw_renaming_var (inverse_raw_renaming r) @ op)
  =v= op.
Proof.
  rewrite var_op_associative, apply_inverse_raw_renaming_right,
    var_op_left_identity.
  easy.
Qed.

Lemma apply_inverse_raw_renaming_right_v r v :
  apply_raw_renaming_var r
    (apply_raw_renaming_var (inverse_raw_renaming r) v)
  = v.
Proof. apply apply_inverse_raw_renaming_right. Qed.

Lemma apply_raw_renaming_var_injective r v1 v2 :
  apply_raw_renaming_var r v1
  = apply_raw_renaming_var r v2 ->
  v1 = v2.
Proof.
  intros Heq.
  rewrite <- (apply_inverse_raw_renaming_left_v r v1).
  rewrite Heq.
  apply apply_inverse_raw_renaming_left_v.
Qed.


(* Define equivalence of [raw_renaming] in terms of
   [apply_raw_renaming] *)

Definition equivalent_raw_renaming : relation raw_renaming :=
  fun r1 r2 =>
    apply_raw_renaming_var r1
    =v= apply_raw_renaming_var r2.

Notation "r1 =rr= r2" :=
  (equivalent_raw_renaming r1 r2) (at level 70).

Instance equivalent_raw_renaming_equiv :
  Equivalence equivalent_raw_renaming.
Proof.
  apply @Build_Equivalence; try easy.
  intros op1 op2 op3 Heq1 Heq2 v.
  rewrite Heq1, Heq2; easy.
Qed.

Add Parametric Morphism : raw_renaming_extend
    with signature eq ==> equivalent_raw_renaming ==> eq
                     ==> equivalent_raw_renaming
      as raw_renaming_extend_mor.
  unfold equivalent_raw_renaming; intros * Heq *; cbn.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism : apply_raw_renaming_var
    with signature equivalent_raw_renaming ==> @eq_var_op 0 0
      as apply_raw_renaming_var_mor.
  intros * Heq v; rewrite Heq; easy.
Qed.

Add Parametric Morphism : compose_raw_renaming
    with signature equivalent_raw_renaming
                     ==> equivalent_raw_renaming
                     ==> equivalent_raw_renaming
      as compose_raw_renaming_mor.
  intros * Heq1 * Heq2; unfold equivalent_raw_renaming.
  rewrite! apply_compose_raw_renaming; cbn.
  rewrite Heq1, Heq2; easy.
Qed.

Add Parametric Morphism : inverse_raw_renaming
    with signature equivalent_raw_renaming
                     ==> equivalent_raw_renaming
      as inverse_raw_renaming_mor.
  unfold equivalent_raw_renaming; intros * Heq.
  rewrite <- apply_inverse_raw_renaming_left'.
  rewrite <- Heq.
  rewrite apply_inverse_raw_renaming_right.
  easy.
Qed.

(* Under this equivalence raw_renamings form a group *)

Lemma raw_renaming_left_inverse r :
  compose_raw_renaming (inverse_raw_renaming r) r
  =rr= raw_renaming_id.
Proof.
  unfold equivalent_raw_renaming.
  rewrite apply_compose_raw_renaming.
  rewrite apply_inverse_raw_renaming_left.
  easy.
Qed.

Lemma raw_renaming_right_inverse r :
  compose_raw_renaming r (inverse_raw_renaming r)
  =rr= raw_renaming_id.
Proof.
  unfold equivalent_raw_renaming.
  rewrite apply_compose_raw_renaming.
  rewrite apply_inverse_raw_renaming_right.
  easy.
Qed.

(* Extensions can be reordered under the equivalence *)

Lemma swap_raw_renaming_extend v1 v2 r v3 v4 :
  raw_renaming_extend
    v1 (raw_renaming_extend v2 r v3) v4
  =rr= raw_renaming_extend
         (shift_var v1 v2)
         (raw_renaming_extend
            (unshift_var v2 v1) r (unshift_var v3 v4))
         (shift_var v4 v3).
Proof.
  unfold equivalent_raw_renaming; cbn; simplify_var_ops.
  rewrite transpose_pops', transpose_pushes,
    transpose_swap_lifted', swap_swap_identity'.
  easy.
Qed.
