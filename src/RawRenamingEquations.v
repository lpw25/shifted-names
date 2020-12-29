Require Import Label PeanoNat Psatz Ring Compare_dec StrictProp.
Require Import Var VarEquations RawRenaming.

(* Properties of raw renaming composition *)

Definition apply_renaming_rhs_var r : var_op 0 1 :=
  lift_var_op (apply_raw_renaming_var (rhs_raw_renaming r))
  @ push_var (rhs_push r).
Arguments apply_renaming_rhs_var r /.

(* TODO: move to var equations *)
Lemma lift_var_op_compose'
      {L N M O} (op1 : var_op N M) (op2 : var_op L N)
      (op3 : var_op O (S L)) :
  lift_var_op (op1 @ op2) @ op3
  =v= lift_var_op op1 @ (lift_var_op op2 @ op3).
Proof.
  rewrite var_op_associative.
  rewrite lift_var_op_compose.
  rewrite <- var_op_associative.
  easy.
Qed.

(* TODO: move to var equations *)
Ltac case_vars_eq v1 v2 :=
  let Hneql := fresh "Hneql" in
  change (var_eqb v1 v2)
    with (if var_dec v1 v2 then true else false);
  destruct (var_dec v1 v2) as [<-|Hneql]; cbn.

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
  case_vars_eq v1 vl.
  - rewrite transpose_op_reducing_push_pop.

  case_var_zero vo1.
  - rewrite transpose_push_reducing_push_pop; easy.
  - rewrite transpose_push_normalized_pushes_cons_push; cbn.
    case_var_zero vo2.
    + apply transpose_pushes_squared_right.
    + rewrite transpose_pushes_reverse_right.
      rewrite IHr.
      rewrite transpose_push_push_pop_zero_reverse_right
        by easy.
      easy.
Qed.

Lemma transpose_push_raw_closing_reverse_middle vo1 vo2 r :
  unshift_var_opt
    (transpose_push_raw_closing_push
       vo1 (transpose_push_raw_closing_raw_closing vo2 r))
    (transpose_push_raw_closing_push vo2 r)
  = transpose_push_raw_closing_push
      (unshift_var_opt vo1 vo2)
      (transpose_push_raw_closing_raw_closing
         (shift_var_opt vo2 vo1) r).
Proof.
  generalize dependent vo1.
  generalize dependent vo2.
  induction r as [|vo3 r]; intros vo2 vo1; cbn; try easy.
  case_var_zero vo2.
  - rewrite transpose_push_normalized_pushes_cons_push; cbn.
    rewrite transpose_push_push_zero_left; cbn.
    rewrite transpose_push_reducing_push_pop; easy.
  - rewrite transpose_push_normalized_pushes_cons_push; cbn.
    case_var_zero vo1.
    + rewrite transpose_pushes_squared_left.
      destruct vo2; easy.
    + rewrite transpose_push_normalized_pushes_cons_push;
        cbn; reduce_var_zero.
      rewrite transpose_pushes_reverse_middle.
      rewrite IHr.
      rewrite transpose_push_push_pop_zero_reverse_middle.
      rewrite transpose_push_raw_closing_reverse_right.
      rewrite transpose_push_push_pop_zero_reverse_right
        by easy.
      easy.
Qed.

Lemma transpose_push_raw_closing_reverse_left vo1 vo2 r :
  transpose_push_raw_closing_raw_closing vo1
    (transpose_push_raw_closing_raw_closing vo2 r)
  = transpose_push_raw_closing_raw_closing
      (unshift_var_opt vo1 vo2)
      (transpose_push_raw_closing_raw_closing
         (shift_var_opt vo2 vo1) r).
Proof.
  generalize dependent vo1.
  generalize dependent vo2.
  induction r as [|vo3 r]; intros vo2 vo1; cbn; try easy.
  case_var_zero vo2.
  - rewrite
      transpose_push_normalized_pushes_cons_raw_closing; cbn.
    rewrite transpose_push_push_zero_left; cbn.
    rewrite transpose_push_reducing_push_pop; easy.
  - rewrite
      transpose_push_normalized_pushes_cons_raw_closing; cbn.
    case_var_zero vo1.
    + destruct vo2; easy.
    + rewrite
        transpose_push_normalized_pushes_cons_raw_closing;
        cbn; reduce_var_zero.
      rewrite <- transpose_pushes_reverse_left.
      rewrite transpose_push_raw_closing_reverse_right.
      rewrite transpose_push_raw_closing_reverse_middle.
      rewrite IHr.
      rewrite transpose_push_push_pop_zero_reverse_middle.
      rewrite transpose_push_push_pop_zero_reverse_right
        by easy.
      easy.
Qed.

Lemma transpose_push_compose_raw_closing_push r1 r2 vo :
  transpose_push_raw_closing_push
    vo (compose_raw_closing r1 r2)
  = transpose_push_raw_closing_push
      (transpose_push_raw_closing_push vo r1) r2.
Proof.
  generalize dependent vo.
  generalize dependent r2.
  induction r1 as [|vo' r1]; intros r2 vo; cbn; try easy.
  rewrite rhs_push_transpose_push_raw_closing,
    rhs_raw_closing_transpose_push_raw_closing.
  rewrite transpose_push_normalized_pushes_cons_push; cbn.
  case_var_zero vo; try easy.
  rewrite IHr1.
  apply transpose_push_raw_closing_reverse_right.
Qed.

Lemma transpose_push_compose_raw_closing_raw_closing r1 r2 vo :
  normalized_pushes r2 ->
  transpose_push_raw_closing_raw_closing
    vo (compose_raw_closing r1 r2)
  = compose_raw_closing
      (transpose_push_raw_closing_raw_closing vo r1)
      (transpose_push_raw_closing_raw_closing
         (transpose_push_raw_closing_push vo r1) r2).
Proof.
  generalize dependent vo.
  generalize dependent r2.
  induction r1 as [|vo' r1]; intros r2 vo Hnorm; cbn; try easy.
  rewrite rhs_push_transpose_push_raw_closing,
    rhs_raw_closing_transpose_push_raw_closing.
  rewrite
    transpose_push_normalized_pushes_cons_raw_closing; cbn.
  case_var_zero vo; try easy.
  rewrite IHr1;
    try (apply transpose_push_raw_closing_raw_closing_normalized;
         easy).
  rewrite transpose_push_raw_closing_reverse_left.
  rewrite transpose_push_compose_raw_closing_push.
  rewrite transpose_push_raw_closing_reverse_middle.
  rewrite compose_normalized_pushes_cons;
    try (apply transpose_push_raw_closing_raw_closing_normalized;
         easy); cbn.
  rewrite rhs_push_transpose_push_raw_closing,
    rhs_raw_closing_transpose_push_raw_closing.
  easy.
Qed.

Lemma raw_closing_associative r1 r2 r3 :
  normalized_pushes r3 ->
  compose_raw_closing r1 (compose_raw_closing r2 r3)
  = compose_raw_closing (compose_raw_closing r1 r2) r3.
Proof.
  generalize dependent r2.
  generalize dependent r3.
  induction r1; cbn; intros r3 r2 Hnorm; try easy.
  rewrite compose_normalized_pushes_cons by easy; cbn.
  rewrite !rhs_push_transpose_push_raw_closing,
    !rhs_raw_closing_transpose_push_raw_closing.
  rewrite transpose_push_compose_raw_closing_raw_closing
    by easy.
  rewrite IHr1
    by (apply transpose_push_raw_closing_raw_closing_normalized;
        easy).
  rewrite transpose_push_compose_raw_closing_push.
  easy.
Qed.

Lemma closing_associative r1 r2 r3 :
  compose_closing r1 (compose_closing r2 r3)
  = compose_closing (compose_closing r1 r2) r3.
Proof.
  destruct r1, r2, r3.
  apply lift_closing_eq; cbn.
  apply raw_closing_associative; easy.
Qed.
