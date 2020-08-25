Require Import String PeanoNat Compare_dec
        StrictProp Setoid Morphisms.
Require Import Var VarEquations Closing.

Definition lift_closing_eq {c1 c2} :
  c1 = c2 -> forall {n1 n2},
    mkclosing c1 n1 = mkclosing c2 n2 :=
  fun Heq =>
    match Heq in eq _ c2'
          return
          forall {n1 n2}, mkclosing _ n1 = mkclosing c2' n2
    with
    | eq_refl => fun n1 n2 => eq_refl
    end.
Arguments lift_closing_eq {c1 c2} Heq {n1 n2}.

Lemma apply_normalized_raw_closing_push0 r op :
  apply_raw_closing_var
    (normalized_raw_closing_push0 r op)
  =v= apply_raw_closing_var (cons op r).
Proof.
  destruct op as [|[]|], r; try easy; cbn; simplify_var_ops.
  rewrite cycle_in_zero_identity; easy.
Qed.

Lemma normalized_raw_closing_push0_identity r op :
  normalized_raw_closing (cons op r) ->
  cons op r = normalized_raw_closing_push0 r op.
Proof. destruct op as [|[]|], r; easy. Qed.

Definition apply_closing_rhs_var r : var_op :=
  lift_var_op (apply_raw_closing_var (rhs_raw_closing r))
  @ apply_push_op_var (rhs_push r).

Lemma apply_closing_rhs_push0 r op :
  apply_closing_rhs_var (closing_rhs_push0 r op)
  =v= swap_var
      @ lift_var_op (apply_closing_rhs_var r)
      @ apply_push_op_var op.
Proof.
  unfold apply_closing_rhs_var; cbn.
  rewrite apply_normalized_raw_closing_push0; cbn; simplify_var_ops.
  rewrite transpose_swap_lifted'.
  rewrite transpose_pushes with (op1 := rhs_push r).
  rewrite swap_swap_identity'.
  easy.
Qed.

Lemma apply_raw_closing_var_add_cycle_out r :
  apply_raw_closing_var r
  =v= apply_pop_op_var (cycle_out_op 0) @ apply_raw_closing_var r.
Proof.
  rewrite cycle_out_zero_identity; simplify_var_ops; easy.
Qed.

Lemma apply_transpose_push_raw_closing op r :
  apply_push_op_var op @ apply_raw_closing_var r
  =v=
  apply_closing_rhs_var (transpose_push_raw_closing op r).
Proof.
  generalize dependent op.
  induction r; intro l';
    rewrite apply_raw_closing_var_add_cycle_out;
    cbn; simplify_var_ops.
  - unfold apply_closing_rhs_var; cbn; simplify_var_ops.
    rewrite cycle_out_zero_identity; easy.
  - destruct (is_zero_push_op l') eqn:Heq.
    + destruct l' as [|[]|]; try easy; cbn.
      rewrite cycle_in_cycle_out_identity'; easy.
    + rewrite var_op_associative.
      fold (apply_pop_op_var (cycle_out_op 0)).
      rewrite transpose_push_pop by (destruct l' as [|[]|]; easy).
      rewrite apply_closing_rhs_push0; cbn.
      rewrite <- IHr; cbn.
      destruct l' as [|[]|]; cbn;
        rewrite cycle_out_zero_identity; simplify_var_ops; easy.
Qed.

Lemma apply_compose_raw_closing r1 r2 :
  apply_raw_closing_var (compose_raw_closing r1 r2)
  =v= apply_raw_closing_var r1 @ apply_raw_closing_var r2.
Proof.
  generalize dependent r2.
  induction r1 as [|op r1]; intro r2; cbn; try easy.
  simplify_var_ops.
  rewrite apply_normalized_raw_closing_push0; cbn.
  rewrite apply_transpose_push_raw_closing, IHr1.
  simplify_var_ops; easy.
Qed.

Lemma apply_compose_closing r1 r2 :
  apply_closing_var (compose_closing r1 r2)
  =v= apply_closing_var r1 @ apply_closing_var r2.
Proof.
  apply apply_compose_raw_closing.
Qed.

Lemma raw_closing_left_identity r :
  compose_raw_closing nil r = r.
Proof. easy. Qed.

Lemma closing_left_identity r :
  compose_closing closing_id r = r.
Proof. easy. Qed.

Lemma raw_closing_right_identity r :
  normalized_raw_closing r ->
  compose_raw_closing r nil = r.
Proof.
  induction r as [|op r]; intros Hnorm; cbn; try easy.
  - rewrite normalized_raw_closing_push0_identity
      by easy.
    rewrite IHr; cbn in *; try easy.
    destruct op as [|[]|], r; easy.
Qed.

Lemma closing_right_identity r :
  compose_closing r closing_id = r.
Proof.
  destruct r.
  apply lift_closing_eq; cbn.
  apply raw_closing_right_identity; easy.
Qed.

Fixpoint transpose_push_raw_closing_push op r {struct r} :=
  match r with
  | raw_closing_id => op
  | raw_closing_weak0 r =>
    match op with
    | weak_op =>
      transpose_push_raw_closing_push weak_op r
    | cycle_in_op 0 => weak_op
    | cycle_in_op (S l') =>
      transpose_push_raw_closing_push (cycle_in_op l') r
    | close_op n =>
      transpose_push_raw_closing_push (close_op n) r
    end
  | raw_closing_exchange0 r l2 =>
    shift_level_push l2
      (match op with
       | weak_op =>
         transpose_push_raw_closing_push weak_op r
       | cycle_in_op 0 => cycle_in_op l2
       | cycle_in_op (S l') =>
         transpose_push_raw_closing_push (cycle_in_op l') r
       | close_op n =>
         transpose_push_raw_closing_push (close_op n) r)
    end


    match l with
    | 0 => cycle_in_op l2
    | S l' =>
      shift_level_push l2
        (transpose_level_raw_closing_push l' r)
    end
  | raw_closing_close0 r n =>
    match l with
    | 0 => close_op n
    | S l' =>
      shift_name_push n
        (transpose_level_raw_closing_push l' r)
    end
  end.

Lemma rhs_push_transpose_level_raw_closing l r :
  rhs_push (transpose_level_raw_closing l r)
  = transpose_level_raw_closing_push l r.
Proof.
  generalize dependent l.
  induction r; try easy; intros l'; destruct l';
    cbn; try easy.
  - rewrite <- IHr.
    destruct (transpose_level_raw_closing l' r) as [? []];
      easy.
  - rewrite <- IHr.
    destruct (transpose_level_raw_closing l' r) as [? []];
      easy.
Qed.

Fixpoint transpose_name_raw_closing_push n r :=
  match r with
  | raw_closing_id => (close_op n)
  | raw_closing_weak0 r =>
    transpose_name_raw_closing_push n r
  | raw_closing_exchange0 r l =>
    shift_level_push l
      (transpose_name_raw_closing_push n r)
  | raw_closing_close0 r n2 =>
    shift_name_push n2
      (transpose_name_raw_closing_push n r)
  end.

Lemma rhs_push_transpose_name_raw_closing n r :
  rhs_push (transpose_name_raw_closing n r)
  = transpose_name_raw_closing_push n r.
Proof.
  induction r; cbn; try easy.
  - rewrite <- IHr.
    destruct (transpose_name_raw_closing n r) as [? []];
      easy.
  - rewrite <- IHr.
    destruct (transpose_name_raw_closing n r) as [? []];
      easy.
Qed.

Definition transpose_push_raw_closing_push p r :=
  match p with
  | weak_op => weak_op
  | cycle_in_op l => transpose_level_raw_closing_push l r
  | close_op n => transpose_name_raw_closing_push n r
  end.

Lemma transpose_level_push_normalized_raw_closing_exchange0
      l1 r l2 :
  transpose_level_raw_closing_push l1
    (normalized_raw_closing_exchange0 r l2)
  = transpose_level_raw_closing_push l1
      (raw_closing_exchange0 r l2).
Proof.
  destruct l2, r; cbn; try easy.
  destruct l1; easy.
Qed.

Lemma transpose_name_push_normalized_raw_closing_exchange0
      n r l :
  transpose_name_raw_closing_push n
    (normalized_raw_closing_exchange0 r l)
  = transpose_name_raw_closing_push n
      (raw_closing_exchange0 r l).
Proof. destruct l, r; easy. Qed.

Lemma transpose_level_push_compose_exchange0 l1 l2 r1 r2 :
  transpose_level_raw_closing_push (S l1)
    (compose_raw_closing (raw_closing_exchange0 r1 l2) r2)
= shift_push (transpose_level_raw_closing_push l2 r2)
    (transpose_level_raw_closing_push l1
       (compose_raw_closing r1
          (rhs_raw_closing
             (transpose_level_raw_closing l2 r2)))).
Proof.
  cbn; rewrite rhs_push_transpose_level_raw_closing.
  destruct (transpose_level_raw_closing_push l2 r2);
    try rewrite
      transpose_level_push_normalized_raw_closing_exchange0;
    easy.
Qed.

Lemma transpose_level_push_compose_close0 l n r1 r2 :
  transpose_level_raw_closing_push (S l)
    (compose_raw_closing (raw_closing_close0 r1 n) r2)
  = shift_push (transpose_name_raw_closing_push n r2)
      (transpose_level_raw_closing_push l
        (compose_raw_closing r1
           (rhs_raw_closing
              (transpose_name_raw_closing n r2)))).
Proof.
  cbn; rewrite rhs_push_transpose_name_raw_closing.
  destruct (transpose_name_raw_closing_push n r2);
    try rewrite
      transpose_level_push_normalized_raw_closing_exchange0;
    easy.
Qed.

Lemma shift_push_weak op :
  shift_push op weak_op = weak_op.
Proof. destruct op; easy. Qed.

Definition unshift_push_level op l :=
  match op with
  | weak_op => l
  | cycle_in_op l' => unshift_level l' l
  | close_op _ => l
  end.

Definition unshift_push_name op n :=
  match op with
  | weak_op => n
  | cycle_in_op _ => n
  | close_op n' => unshift_name n' n
  end.

Lemma shift_level_succ l1 l2 :
  shift_level (S l1) (S l2)
  = S (shift_level l1 l2).
Proof. case_levels l1 l2. Qed.

Lemma foz r l :
  rhs_raw_closing (closing_rhs_exchange0 r l)
  = normalized_raw_closing_exchange0
      (rhs_raw_closing r)
      (unshift_push_level (rhs_push r) l).
Proof. destruct r as [? []]; easy. Qed.

Lemma foz2 r n :
  rhs_raw_closing (closing_rhs_close0 r n)
  = raw_closing_close0
      (rhs_raw_closing r)
      (unshift_push_name (rhs_push r) n).
Proof. destruct r as [? []]; easy. Qed.

Lemma foo_exchange l1 l2 r :
  shift_push (transpose_level_raw_closing_push l1 r)
    (transpose_level_raw_closing_push l2
       (rhs_raw_closing
          (transpose_level_raw_closing l1 r))) =
  transpose_level_raw_closing_push (shift_level l1 l2) r.
Proof.
  generalize dependent l1.
  generalize dependent l2.
  induction r; intros l2 l1; cbn; try easy.
  - destruct l1; cbn; try easy.
    destruct l2; cbn;
      try rewrite shift_push_weak; try easy.
    rewrite IHr, shift_level_succ; easy.
  - destruct l1; cbn; try easy.
    rewrite foz,
      rhs_push_transpose_level_raw_closing,
      transpose_level_push_normalized_raw_closing_exchange0; cbn.
    destruct l2; cbn.
    + destruct (transpose_level_raw_closing_push l1 r);
        cbn; try easy.
      rewrite transpose_cycle_ins_squared_right; easy.
    + rewrite shift_level_succ.
      rewrite <- IHr.
      destruct (transpose_level_raw_closing_push l1 r),
        (transpose_level_raw_closing_push l2
          (rhs_raw_closing
             (transpose_level_raw_closing l1 r))); try easy; cbn.
      rewrite transpose_cycle_ins_reverse_right; easy.
  - destruct l1; cbn; try easy.
    rewrite foz2, rhs_push_transpose_level_raw_closing; cbn.
    destruct l2; cbn.
    + destruct (transpose_level_raw_closing_push l1 r);
        cbn; try easy.
      rewrite transpose_closes_squared_right; easy.
    + rewrite shift_level_succ.
      rewrite <- IHr.
      destruct (transpose_level_raw_closing_push l1 r),
        (transpose_level_raw_closing_push l2
          (rhs_raw_closing
             (transpose_level_raw_closing l1 r))); try easy; cbn.
      rewrite transpose_closes_reverse_right; easy.
Qed.

Lemma foo_close l n r :
  shift_push (transpose_level_raw_closing_push l r)
    (transpose_name_raw_closing_push n
       (rhs_raw_closing
          (transpose_level_raw_closing l r))) =
  transpose_name_raw_closing_push n r.
Proof.
  generalize dependent l.
  generalize dependent n.
  induction r; intros n' l'; cbn; try easy.
  - destruct l'; cbn; easy.
  - destruct l'; cbn; try easy.
    rewrite foz,
      rhs_push_transpose_level_raw_closing,
      transpose_name_push_normalized_raw_closing_exchange0;
      cbn.
    rewrite <- IHr with (l := l').
    destruct (transpose_level_raw_closing_push l' r),
      (transpose_name_raw_closing_push n'
         (rhs_raw_closing
            (transpose_level_raw_closing l' r))); cbn; try easy.
    rewrite transpose_cycle_ins_reverse_right.
    easy.
  - destruct l'; cbn; try easy.
    rewrite foz2, rhs_push_transpose_level_raw_closing; cbn.
    rewrite <- IHr with (l := l').
    destruct (transpose_level_raw_closing_push l' r),
      (transpose_name_raw_closing_push n'
         (rhs_raw_closing
            (transpose_level_raw_closing l' r))); cbn; try easy.
    rewrite transpose_closes_reverse_right.
    easy.
Qed.

Lemma foo l r op :
  shift_push (transpose_level_raw_closing_push l r)
    (transpose_push_raw_closing_push op
       (rhs_raw_closing (transpose_level_raw_closing l r))) =
  transpose_push_raw_closing_push (shift_level_push l op) r.
Proof.
  destruct op; cbn.
  - rewrite shift_push_weak; easy.
  - apply foo_exchange.
  - apply foo_close.
Qed.

Lemma foo2_exchange n l r :
  shift_push (transpose_name_raw_closing_push n r)
      (transpose_level_raw_closing_push l
         (rhs_raw_closing
            (transpose_name_raw_closing n r))) =
    transpose_level_raw_closing_push l r.
Proof.
  generalize dependent l.
  induction r; intros l'; cbn; try easy.
  - destruct l'; try rewrite shift_push_weak; easy.
  - rewrite foz,
      rhs_push_transpose_name_raw_closing,
      transpose_level_push_normalized_raw_closing_exchange0;
      cbn.
    destruct l'.
    + destruct (transpose_name_raw_closing_push n r);
        cbn; try easy.
      rewrite transpose_cycle_ins_squared_right; easy.
    + rewrite <- IHr.
      destruct (transpose_name_raw_closing_push n r),
        (transpose_level_raw_closing_push l'
          (rhs_raw_closing (transpose_name_raw_closing n r)));
        cbn; try easy.
      rewrite transpose_cycle_ins_reverse_right; easy.
  - rewrite foz2, rhs_push_transpose_name_raw_closing; cbn.
    destruct l'.
    + destruct (transpose_name_raw_closing_push n r);
        cbn; try easy.
      rewrite transpose_closes_squared_right; easy.
    + rewrite <- IHr.
      destruct (transpose_name_raw_closing_push n r),
        (transpose_level_raw_closing_push l'
          (rhs_raw_closing (transpose_name_raw_closing n r)));
        cbn; try easy.
      rewrite transpose_closes_reverse_right; easy.
Qed.

Lemma foo2 n r op :
  shift_push (transpose_name_raw_closing_push n r)
    (transpose_push_raw_closing_push op
       (rhs_raw_closing
          (transpose_name_raw_closing n r))) =
  transpose_push_raw_closing_push (shift_name_push n op) r.
Proof.
  destruct op; cbn.
  - rewrite shift_push_weak; easy.
  - 

Lemma transpose_level_compose_raw_closing_push r1 r2 l :
  transpose_level_raw_closing_push
    l (compose_raw_closing r1 r2)
  = transpose_push_raw_closing_push
      (transpose_level_raw_closing_push l r1) r2.
Proof.
  generalize dependent l.
  generalize dependent r2.
  induction r1; intros r2 l'; try easy.
  - destruct l'; cbn; try easy.
  - destruct l'.
    + cbn; rewrite rhs_push_transpose_level_raw_closing; cbn.
      destruct (transpose_level_raw_closing_push l r2);
        try rewrite
          transpose_level_push_normalized_raw_closing_exchange0;
        easy.
    + rewrite transpose_level_push_compose_exchange0, IHr1; cbn.
      apply foo.
  - destruct l'.
    + cbn; rewrite rhs_push_transpose_name_raw_closing; cbn.
      destruct (transpose_name_raw_closing_push n r2);
        try rewrite
          transpose_level_push_normalized_raw_closing_exchange0;
        easy.
    + rewrite transpose_level_push_compose_close0, IHr1; cbn.
      apply foo.

Lemma transpose_level_compose_raw_closing r1 r2 l :
  transpose_level_raw_closing l (compose_raw_closing r1 r2)
  = compose_closing_rhs_raw_closing
      (transpose_level_raw_closing l r1) r2.
Proof.
  generalize dependent O.
  induction r1; intros O r2; cbn; try easy.
  - exfalso; apply (level_zero_empty l).
  - unfold level_sdec; destruct (level_dec l_0 l) as [|neq];
      subst; cbn; try easy.
    inversion_level (unshift_level_neq l_0 l (squash neq)).
    rewrite IHr1.
    admit.
  - destruct (transpose_level_closing r2 l0) eqn:Heqrl; cbn.
    + unfold level_sdec; destruct (level_dec l_0 l) as [|neq];
        subst; cbn; try solve [rewrite Heqrl; easy].
      inversion_level (unshift_level_neq l_0 l (squash neq)).
      rewrite IHr1.
      admit.
    + unfold level_sdec; destruct (level_dec l_0 l) as [|neq];
        subst; cbn; try solve [rewrite Heqrl; easy].
      inversion_level (unshift_level_neq l_0 l (squash neq)).
      rewrite IHr1.
      admit.
    + unfold level_sdec; destruct (level_dec l_0 l) as [|neq];
        subst; cbn; try solve [rewrite Heqrl; easy].
      inversion_level (unshift_level_neq l_0 l (squash neq)).
      rewrite IHr1.
      admit.
  - destruct (transpose_name_closing r2 n) eqn:Heqrn; cbn.
    + exfalso. admit.
    + exfalso. admit.
    + unfold level_sdec; destruct (level_dec l_0 l) as [|neq];
        subst; cbn; try solve [rewrite Heqrn; easy].
      inversion_level (unshift_level_neq l_0 l (squash neq)).
      rewrite IHr1.
      admit.
Qed.

Lemma closing_associative {N M O L}
      (r1 : closing N M) (r2 : closing M O) (r3 : closing O L) :
  compose_closing r1 (compose_closing r2 r3)
  = compose_closing (compose_closing r1 r2) r3.
Proof.
  induction r1; cbn; try easy.
  - rewrite IHr1; easy.
  - 

Inductive closing : nat -> nat -> Set :=
| closing_nil : closing 0 0
| closing_weak0 : forall N M,
  closing N M -> closing (S N) M
| closing_exchange0 : forall N M,
    closing N M -> level (S M) -> closing (S N) (S M)
| closing_close0 : forall N M,
    closing N M -> name -> closing (S N) M.
