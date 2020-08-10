Require Import String PeanoNat Compare_dec
        StrictProp Setoid Morphisms.
Require Import Morph Var VarEquations Renaming.

(* Properties of closing composition *)

Definition apply_closing_rhs_var {N M} (r : closing_rhs N M)
  : morph var M var (S N) :=
  match r in closing_rhs _ M return morph _ M _ _ with
  | @closing_rhs_weak_rhs _ M r =>
      lift_morph_var (apply_closing_var r)
      @ morph_extend_by M (@weak_var)
  | @closing_rhs_exchange_rhs _ M r l2 =>
      lift_morph_var (apply_closing_var r)
      @ @cycle_in_var (S M) l2
  | @closing_rhs_close_rhs _ M r n =>
      lift_morph_var (apply_closing_var r)
      @ morph_extend_by M (@close_var n)
  end.

Lemma apply_closing_rhs_zero_weak N M
      (r : closing_rhs N M) :
  apply_closing_rhs_var (closing_rhs_zero_weak r)
  =m= morph_extend_by N (@swap_var)
      @ lift_morph_var (apply_closing_rhs_var r)
      @ morph_extend_by M (@weak_var).
Proof.
  destruct r; cbn.
  - simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes weak_op weak_op at 1.
    easy.
  - simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes weak_op (cycle_in_op l).
    easy.
  - simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes weak_op (close_op n).
    easy.
Qed.

Lemma apply_closing_rhs_zero_exchange N M
      (r : closing_rhs N M) (l2 : level (S M)):
  apply_closing_rhs_var (closing_rhs_zero_exchange r l2)
  =m= morph_extend_by N (@swap_var)
      @ lift_morph_var (apply_closing_rhs_var r)
      @ (@cycle_in_var (S M) l2).
Proof.
  destruct r; cbn.
  - simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes (cycle_in_op l2) weak_op.
    easy.
  - simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes (cycle_in_op l) (cycle_in_op l2).
    rewrite swap_swap_identity'.
    easy.
  - simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes (cycle_in_op l2) (close_op n).
    easy.
Qed.

Lemma apply_closing_rhs_zero_close N M
      (r : closing_rhs N M) n :
  apply_closing_rhs_var (closing_rhs_zero_close r n)
  =m= morph_extend_by N (@swap_var)
      @ lift_morph_var (apply_closing_rhs_var r)
      @ morph_extend_by M (@close_var n).
Proof.
  destruct r; cbn.
  - simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes (close_op n) weak_op.
    easy.
  - simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes (close_op n) (cycle_in_op l).
    easy.
  - simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes (close_op _) (close_op n).
    rewrite swap_swap_identity'.
    easy.
Qed.

Definition apply_closing_var_with_cycle_out {N M}
           (r : closing N M) : morph var M var N :=
  match r in closing N M return morph var M var N with
  | closing_nil =>
    apply_closing_var closing_nil
  | closing_zero_weak r =>
    (@cycle_out_var _ l_0)
    @ apply_closing_var (closing_zero_weak r)
  | closing_zero_exchange r l =>
    (@cycle_out_var _ l_0)
    @ apply_closing_var (closing_zero_exchange r l)
  | closing_zero_close r n =>
    (@cycle_out_var _ l_0)
    @ apply_closing_var (closing_zero_close r n)
  end.

Lemma apply_closing_var_add_cycle_out {N M} (r : closing N M) :
  apply_closing_var r =m= apply_closing_var_with_cycle_out r.
Proof.
  induction r; cbn;
    try rewrite cycle_out_zero_identity; simplify_var_morphs; easy.
Qed.

Lemma apply_transpose_level_closing_aux N M
      (r : closing N M) (l : level N):
  morph_id_to_succ_pred l
  @ (@cycle_in_var _ l)
  @ apply_closing_var r
  =m=
  apply_closing_rhs_var (transpose_level_closing r l).
Proof.
  generalize dependent l.
  induction r; intro l'; rewrite apply_closing_var_add_cycle_out;
    cbn; try rewrite morph_left_identity.
  - exfalso; apply (level_zero_empty l').
  - unfold level_sdec.
    destruct (level_dec l_0 l'); subst; cbn.
    + rewrite morph_associative.
      rewrite cycle_in_cycle_out_identity.
      easy.
    + inversion_level (unshift_level_neq l_0 l' (squash n)).
      rewrite morph_associative.
      transpose_push_pop (cycle_in_op l') (cycle_out_op l_0).
      rewrite cycle_out_zero_identity.
      rewrite apply_closing_rhs_zero_weak; cbn.
      rewrite <- IHr; cbn.
      simplify_var_morphs.
      easy.
  - unfold level_sdec.
    destruct (level_dec l_0 l'); subst; cbn.
    + rewrite morph_associative.
      rewrite cycle_in_cycle_out_identity.
      easy.
    + inversion_level (unshift_level_neq l_0 l' (squash n)).
      rewrite morph_associative.
      transpose_push_pop (cycle_in_op l') (cycle_out_op l_0).
      rewrite cycle_out_zero_identity.
      rewrite apply_closing_rhs_zero_exchange; cbn.
      rewrite <- IHr; cbn.
      simplify_var_morphs.
      easy.
  - unfold level_sdec.
    destruct (level_dec l_0 l'); subst; cbn.
    + rewrite morph_associative.
      rewrite cycle_in_cycle_out_identity.
      easy.
    + inversion_level (unshift_level_neq l_0 l' (squash n0)).
      rewrite morph_associative.
      transpose_push_pop (cycle_in_op l') (cycle_out_op l_0).
      rewrite cycle_out_zero_identity.
      rewrite apply_closing_rhs_zero_close; cbn.
      rewrite <- IHr; cbn.
      simplify_var_morphs.
      easy.
Qed.

Lemma apply_transpose_level_closing N M
      (r : closing (S N) M) (l : level (S N)):
  (@cycle_in_var _ l) @ apply_closing_var r
  =m=
  apply_closing_rhs_var (transpose_level_closing r l).
Proof.
  rewrite <- apply_transpose_level_closing_aux.
  easy.
Qed.

Lemma transpose_closing_weak {N M} (r : closing N M) :
  lift_morph_var (apply_closing_var r)
  @ morph_extend_by M (@weak_var)
  =m= morph_extend_by N (@weak_var)
      @ apply_closing_var r.
Proof.
  induction r; rewrite apply_closing_var_add_cycle_out;
    cbn; simplify_var_morphs; try easy.
  - rewrite morph_associative
      with (g := @cycle_out_var _ _).
    transpose_push_pop weak_op (cycle_out_op l_0).
    simplify_var_morphs.
    rewrite morph_associative
      with (g := lift_morph_var (apply_closing_var r)).
    rewrite <- lift_morph_var_compose.
    rewrite <- IHr.
    simplify_var_morphs.
    rewrite morph_associative
      with (f := morph_extend_by N (@swap_var)).
    rewrite transpose_swap_lifted.
    simplify_var_morphs.
    transpose_pushes weak_op weak_op at 1.
    easy.
  - rewrite morph_associative with (g := @cycle_out_var _ l_0).
    transpose_push_pop weak_op (cycle_out_op l_0).
    transpose_pushes (cycle_in_op l) weak_op.
    rewrite morph_associative
      with (g := morph_extend_by M (@swap_var)).
    rewrite <- transpose_swap_lifted.
    simplify_var_morphs.
    rewrite morph_associative
      with (g := lift_morph_var (apply_closing_var r)).
    rewrite <- lift_morph_var_compose.
    rewrite <- IHr.
    simplify_var_morphs.
    easy.
  - rewrite morph_associative with (g := @cycle_out_var _ l_0).
    transpose_push_pop weak_op (cycle_out_op l_0).
    transpose_pushes (close_op n) weak_op.
    rewrite morph_associative
      with (g := morph_extend_by M (@swap_var)).
    rewrite <- transpose_swap_lifted.
    simplify_var_morphs.
    rewrite morph_associative
      with (g := lift_morph_var (apply_closing_var r)).
    rewrite <- lift_morph_var_compose.
    rewrite <- IHr.
    simplify_var_morphs.
    easy.
Qed.

Lemma apply_transpose_name_closing N M
      (r : closing N M) n:
  morph_extend_by N (@close_var n) @ apply_closing_var r
  =m=
  apply_closing_rhs_var (transpose_name_closing r n).
Proof.
  induction r; rewrite apply_closing_var_add_cycle_out;
    cbn; simplify_var_morphs; try easy.
  - rewrite apply_closing_rhs_zero_weak, <- IHr;
      cbn; simplify_var_morphs.
    rewrite morph_associative with (g := @cycle_out_var _ l_0).
    transpose_push_pop (close_op n) (cycle_out_op l_0).
    rewrite cycle_out_zero_identity.
    simplify_var_morphs.
    easy.
  - rewrite apply_closing_rhs_zero_exchange, <- IHr;
      cbn; simplify_var_morphs.
    rewrite morph_associative with (g := @cycle_out_var _ l_0).
    transpose_push_pop (close_op n) (cycle_out_op l_0).
    rewrite cycle_out_zero_identity.
    simplify_var_morphs.
    easy.
  - rewrite apply_closing_rhs_zero_close, <- IHr;
      cbn; simplify_var_morphs.
    rewrite morph_associative with (g := @cycle_out_var _ l_0).
    transpose_push_pop (close_op n) (cycle_out_op l_0).
    rewrite cycle_out_zero_identity.
    simplify_var_morphs.
    easy.
Qed.

Lemma apply_compose_closing {N M O}
    (r1 : closing O N) (r2 : closing N M) :
  apply_closing_var (compose_closing r1 r2)
  =m= apply_closing_var r1 @ apply_closing_var r2.
Proof.
  generalize dependent M.
  induction r1; intros M' r2; cbn; try easy.
  - rewrite IHr1; simplify_var_morphs.
    setoid_rewrite transpose_closing_weak.
    easy.
  - simplify_var_morphs.
    rewrite apply_transpose_level_closing.
    destruct (transpose_level_closing r2 l); cbn;
      rewrite IHr1; simplify_var_morphs; easy.
  - simplify_var_morphs.
    setoid_rewrite apply_transpose_name_closing.
    destruct (transpose_name_closing r2 n); cbn;
      rewrite IHr1; simplify_var_morphs; easy.
Qed.

Lemma transpose_level_id {N} (l : level (S N)) :
  transpose_level_closing closing_id l
  = closing_rhs_exchange_rhs closing_id l.
Proof.
  induction N; cbn in *; unfold level_sdec in *.
  - destruct (level_dec l_0 l) as [eql|neql].
    + rewrite eql; easy.
    + exfalso.
      apply (level_zero_empty
               (unshift_level_neq l_0 l (squash neql))).
  - destruct (level_dec l_0 l) as [eql|neql].
    + rewrite eql; easy.
    + rewrite IHN.
      unfold closing_rhs_zero_exchange.
      rewrite shift_level_unshift_level_neq_identity.
      easy.
Qed.

Lemma transpose_name_id {N} n :
  transpose_name_closing (@closing_id N) n
  = closing_rhs_close_rhs closing_id n.
Proof.
  induction N; cbn; try rewrite IHN; easy.
Qed.

Lemma closing_left_identity {N M} (r : closing N M) :
  compose_closing closing_id r = r.
Proof.
  induction r; cbn; try rewrite IHr; easy.
Qed.

Lemma closing_right_identity {N M} (r : closing N M) :
  compose_closing r closing_id = r.
Proof.
  induction r; try easy.
  - cbn; rewrite IHr; easy.
  - remember (@closing_id (S M)) as c; cbn; subst.
    rewrite transpose_level_id, IHr; easy.
  - remember (@closing_id (S M)) as c; cbn; subst.
    rewrite transpose_name_id, IHr; easy.
Qed.
