Require Import String PeanoNat Compare_dec
        StrictProp Setoid Morphisms.
Require Import Morph Var VarEquations Renaming.

(* Properties of composition *)

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

Lemma apply_closing_rhs_weak N M
      (l : level N) (r : closing_rhs (pred N) M) :
  apply_closing_rhs_var (closing_rhs_weak l r)
  =m= lift_morph_var (@cycle_out_var N l)
      @ lift_morph_var (morph_id_from_succ_pred l)
      @ morph_extend_by (pred N) (@swap_var)
      @ lift_morph_var (apply_closing_rhs_var r)
      @ morph_extend_by M (@weak_var).
Proof.
  destruct r; cbn.
  - inversion_level l.
    simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes weak_op weak_op at 1.
    easy.
  - inversion_level l.
    simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes weak_op (cycle_in_op l0).
    easy.
  - inversion_level l.
    simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes weak_op (close_op n).
    easy.
Qed.

Lemma apply_closing_rhs_exchange N M
      (l1 : level N) (r : closing_rhs (pred N) M)
      (l2 : level (S M)):
  apply_closing_rhs_var (closing_rhs_exchange l1 r l2)
  =m= lift_morph_var (@cycle_out_var N l1)
      @ lift_morph_var (morph_id_from_succ_pred l1)
      @ morph_extend_by (pred N) (@swap_var)
      @ lift_morph_var (apply_closing_rhs_var r)
      @ (@cycle_in_var (S M) l2).
Proof.
  destruct r; cbn.
  - inversion_level l1.
    simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes (cycle_in_op l2) weak_op.
    easy.
  - inversion_level l1.
    simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes (cycle_in_op l) (cycle_in_op l2).
    rewrite swap_swap_identity'.
    easy.
  - inversion_level l1.
    simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes (cycle_in_op l2) (close_op n).
    easy.
Qed.

Lemma apply_closing_rhs_close N M
      (l : level N) (r : closing_rhs (pred N) M) n :
  apply_closing_rhs_var (closing_rhs_close l r n)
  =m= lift_morph_var (@cycle_out_var N l)
      @ lift_morph_var (morph_id_from_succ_pred l)
      @ morph_extend_by (pred N) (@swap_var)
      @ lift_morph_var (apply_closing_rhs_var r)
      @ morph_extend_by M (@close_var n).
Proof.
  destruct r; cbn.
  - inversion_level l.
    simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes (close_op n) weak_op.
    easy.
  - inversion_level l.
    simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes (close_op n) (cycle_in_op l0).
    easy.
  - inversion_level l.
    simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes (close_op _) (close_op n).
    rewrite swap_swap_identity'.
    easy.
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
  induction r; intro l'; cbn; try rewrite morph_left_identity.
  - exfalso; apply (level_zero_empty l').
  - unfold level_sdec.
    destruct (level_dec l' l); subst; cbn.
    + rewrite morph_associative.
      rewrite cycle_in_cycle_out_identity.
      rewrite morph_left_identity.
      easy.
    + inversion_level (unshift_level_neq l' l (squash n)).
      rewrite apply_closing_rhs_weak; cbn.
      rewrite <- IHr; cbn.
      simplify_var_morphs.
      rewrite morph_associative.
      transpose_push_pop (cycle_in_op l') (cycle_out_op l).
      easy.
  - unfold level_sdec.
    destruct (level_dec l' l); subst; cbn.
    + rewrite cycle_in_cycle_out_identity'.
      easy.
    + inversion_level (unshift_level_neq l' l (squash n)).
      rewrite apply_closing_rhs_exchange; cbn.
      rewrite <- IHr; cbn.
      simplify_var_morphs.
      rewrite morph_associative.
      transpose_push_pop (cycle_in_op l') (cycle_out_op l).
      easy.
  - unfold level_sdec.
    destruct (level_dec l' l); subst; cbn.
    + rewrite cycle_in_cycle_out_identity'.
      easy.
    + inversion_level (unshift_level_neq l' l (squash n0)).
      rewrite apply_closing_rhs_close; cbn.
      rewrite <- IHr; cbn.
      simplify_var_morphs.
      rewrite morph_associative.
      transpose_push_pop (cycle_in_op l') (cycle_out_op l).
      easy.
Qed.

Lemma apply_transpose_level_closing N M
      (r : closing (S N) M) (l : level (S N)):
  (@cycle_in_var _ l) @ apply_closing_var r
  =m=
  apply_closing_rhs_var (transpose_level_closing r l).
Proof.
  rewrite <- apply_transpose_level_closing_aux; cbn.
  rewrite morph_left_identity.
  easy.
Qed.
