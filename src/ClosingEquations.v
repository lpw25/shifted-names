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

(* Tactic for simplifying comparisons with [zero_var_opt] *)

Lemma reduce_var_opt_eqb_zero_neq vo :
  vo <> zero_var_opt ->
  var_opt_eqb vo zero_var_opt = false.
Proof.
  intros; unfold var_opt_eqb.
  destruct (var_opt_dec vo zero_var_opt); easy.
Qed.

Lemma reduce_var_opt_eqb_zero_shift vo1 vo2 :
  var_opt_eqb (shift_var_opt vo1 vo2) zero_var_opt
  = andb
      (var_opt_eqb vo2 zero_var_opt)
      (negb (var_opt_eqb vo1 zero_var_opt)).
Proof.
  destruct vo1 as [v1|], vo2 as [v2|]; cbn; try easy.
  - case_var v1 as n1 l1; case_var v2 as n2 l2; cbn; try easy.
    + rewrite Bool.andb_true_r; easy.
    + case_levels l1 l2.
      * case_level l2; easy.
      * rewrite Bool.andb_negb_r; easy.
      * case_level l1.
        rewrite Bool.andb_true_r; easy.
  - rewrite Bool.andb_true_r; easy.
Qed.

Lemma reduce_var_opt_eqb_zero_unshift vo1 vo2 :
  vo1 <> zero_var_opt ->
  vo2 <> zero_var_opt ->
  var_opt_eqb (unshift_var_opt vo1 vo2) zero_var_opt = false.
Proof.
  intros.
  destruct vo1 as [v1|], vo2 as [v2|]; cbn; try easy.
  - case_var v1 as n1 l1; case_var v2 as n2 l2;
      cbn; try easy.
    + apply reduce_var_opt_eqb_zero_neq; easy.
    + case_levels l1 l2;
        try apply reduce_var_opt_eqb_zero_neq; try easy.
      case_level l2 as l2.
      case_level l2; try easy.
      case_level l1; easy.
  - case_var v2 as n2 v2; try easy.
    apply reduce_var_opt_eqb_zero_neq; easy.
Qed.

Hint Rewrite reduce_var_opt_eqb_zero_shift
     Bool.andb_true_r Bool.andb_false_r : reduce_var_zero.

Hint Rewrite reduce_var_opt_eqb_zero_neq
     reduce_var_opt_eqb_zero_unshift
     using (cbn; congruence) : reduce_var_zero.

Ltac reduce_var_zero :=
  try repeat
      (autorewrite with reduce_var_zero; cbn in *);
  try repeat
    ((rewrite_strat (bottomup (hints reduce_var_zero)));
     cbn in *).

Ltac case_var_zero vo :=
  destruct (var_opt_dec vo zero_var_opt);
    [replace vo with zero_var_opt by easy|];
    reduce_var_zero.

(* Applying [closing_push] and friends *)

Lemma apply_normalized_pushes_cons vo r :
  apply_raw_closing_var (normalized_pushes_cons vo r)
  =v= apply_raw_closing_var (cons vo r).
Proof.
  unfold normalized_pushes_cons; cbn.
  case_var_zero vo; destruct r; cbn; try easy.
  simplify_var_ops.
  rewrite push_zero_identity; easy.
Qed.

Lemma apply_raw_closing_var_add_cycle_out r :
  apply_raw_closing_var r
  =v= pop_var zero_var @ apply_raw_closing_var r.
Proof.
  rewrite pop_zero_identity; simplify_var_ops; easy.
Qed.

Lemma apply_raw_closing_hd_tl r :
  apply_raw_closing_var r
  =v= lift_var_op (apply_raw_closing_var (raw_closing_tl r))
      @ push_var (raw_closing_hd r).
Proof.
  induction r; cbn; try easy.
  simplify_var_ops.
  rewrite push_zero_identity; easy.
Qed.

Lemma apply_raw_closing_cons l vo r :
  apply_raw_closing_var (raw_closing_cons l vo r)
  =v= pop_var (bound l)
      @ lift_var_op (apply_raw_closing_var r)
      @ push_var vo.
Proof.
  rewrite apply_raw_closing_var_add_cycle_out
    with (r := r); simplify_var_ops.
  generalize dependent vo.
  generalize dependent r.
  induction l; intros r vo; cbn.
  - rewrite apply_normalized_pushes_cons; cbn.
    rewrite pop_zero_identity; simplify_var_ops.
    easy.
  - rewrite apply_normalized_pushes_cons; cbn.
    rewrite apply_raw_closing_hd_tl with (r := r).
    rewrite IHl; simplify_var_ops.
    rewrite transpose_pushes with (vo2 := vo).
    rewrite <- transpose_swap_lifted'.
    fold (pop_var (bound 0)).
    rewrite (transpose_pops' (bound (S l))).
    rewrite swap_swap_identity'; cbn.
    rewrite pop_zero_identity; simplify_var_ops.
    easy.
Qed.

Lemma apply_closing_cons l vo r :
  apply_closing_var (closing_cons l vo r)
  =v= pop_var (bound l)
      @ lift_var_op (apply_closing_var r)
      @ push_var vo.
Proof.
  destruct r; cbn.
  apply apply_raw_closing_cons.
Qed.

Lemma apply_closing_weak l r :
  apply_closing_var (closing_weak l r)
  =v= cycle_out_var l
      @ lift_var_op (apply_closing_var r)
      @ weak_var.
Proof. apply apply_closing_cons. Qed.

Lemma apply_closing_exchange l1 l2 r :
  apply_closing_var (closing_exchange l1 l2 r)
  =v= cycle_out_var l1
      @ lift_var_op (apply_closing_var r)
      @ cycle_in_var l2.
Proof. apply apply_closing_cons. Qed.

Lemma apply_closing_close l n r :
  apply_closing_var (closing_close l n r)
  =v= cycle_out_var l
      @ lift_var_op (apply_closing_var r)
      @ close_var n.
Proof. apply apply_closing_cons. Qed.

(* Properties of composition *)

Lemma normalized_raw_closing_push0_identity vo r :
  normalized_pushes (cons vo r) ->
  cons vo r = normalized_pushes_cons vo r.
Proof.
  unfold normalized_pushes_cons.
  case_var_zero vo; destruct r; easy.
Qed.

Definition apply_closing_rhs_var r : var_op :=
  lift_var_op (apply_raw_closing_var (rhs_raw_closing r))
  @ push_var (rhs_push r).

Lemma apply_closing_rhs_push0 vo r :
  apply_closing_rhs_var (closing_rhs_cons0 vo r)
  =v= swap_var
      @ lift_var_op (apply_closing_rhs_var r)
      @ push_var vo.
Proof.
  unfold apply_closing_rhs_var; cbn.
  rewrite apply_normalized_pushes_cons;
    cbn; simplify_var_ops.
  rewrite transpose_swap_lifted'.
  rewrite transpose_pushes with (vo1 := rhs_push r).
  rewrite swap_swap_identity'.
  easy.
Qed.

Lemma apply_transpose_push_raw_closing vo r :
  push_var vo @ apply_raw_closing_var r
  =v=
  apply_closing_rhs_var (transpose_push_raw_closing vo r).
Proof.
  generalize dependent vo.
  induction r; intro vo';
    rewrite apply_raw_closing_var_add_cycle_out;
    cbn; simplify_var_ops.
  - unfold apply_closing_rhs_var; cbn; simplify_var_ops.
    rewrite pop_zero_identity; easy.
  - case_var_zero vo'.
    + rewrite push_pop_identity' with (v := zero_var); easy.
    + fold (pop_var (bound 0)).
      rewrite transpose_push_pop' by easy.
      rewrite apply_closing_rhs_push0; cbn.
      rewrite <- IHr; cbn.
      rewrite transpose_push_pop_zero_left.
      rewrite pop_zero_identity.
      simplify_var_ops; easy.
Qed.

Lemma apply_compose_raw_closing r1 r2 :
  apply_raw_closing_var (compose_raw_closing r1 r2)
  =v= apply_raw_closing_var r1 @ apply_raw_closing_var r2.
Proof.
  generalize dependent r2.
  induction r1 as [|vo r1]; intro r2; cbn; try easy.
  simplify_var_ops.
  rewrite apply_normalized_pushes_cons; cbn.
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
  normalized_pushes r ->
  compose_raw_closing r nil = r.
Proof.
  induction r as [|vo r]; intros Hnorm; cbn; try easy.
  rewrite normalized_raw_closing_push0_identity
    by easy.
  rewrite IHr; cbn in *; try easy.
  apply normalized_pushes_from_cons in Hnorm.
  easy.
Qed.

Lemma closing_right_identity r :
  compose_closing r closing_id = r.
Proof.
  destruct r.
  apply lift_closing_eq; cbn.
  apply raw_closing_right_identity; easy.
Qed.

Fixpoint transpose_push_raw_closing_push vo r {struct r} :=
  match r with
  | nil => vo
  | cons vo' r =>
    if var_opt_eqb vo zero_var_opt then vo'
    else shift_var_opt vo'
           (transpose_push_raw_closing_push
              (unshift_var_var_opt zero_var vo) r)
  end.

Lemma rhs_push_transpose_push_raw_closing vo r :
  rhs_push (transpose_push_raw_closing vo r)
  = transpose_push_raw_closing_push vo r.
Proof.
  generalize dependent vo.
  induction r as [|vo' r]; intros vo; cbn; try easy.
  case_var_zero vo; try easy.
  rewrite IHr; easy.
Qed.

Fixpoint transpose_push_raw_closing_raw_closing
         vo r {struct r} :=
  match r with
  | nil => nil
  | cons vo' r =>
    if var_opt_eqb vo zero_var_opt then r
    else
      normalized_pushes_cons
        (unshift_var_opt
           (transpose_push_raw_closing_push
              (unshift_var_var_opt zero_var vo) r)
           vo')
        (transpose_push_raw_closing_raw_closing
           (unshift_var_var_opt zero_var vo) r)
  end.

Lemma rhs_raw_closing_transpose_push_raw_closing vo r :
  rhs_raw_closing (transpose_push_raw_closing vo r)
  = transpose_push_raw_closing_raw_closing vo r.
Proof.
  generalize dependent vo.
  induction r as [|vo' r]; intros vo; cbn; try easy.
  case_var_zero vo; try easy.
  rewrite rhs_push_transpose_push_raw_closing, IHr; easy.
Qed.

Lemma closing_rhs_eta r :
  r = mk_closing_rhs (rhs_raw_closing r) (rhs_push r).
Proof. easy. Qed.

Lemma transpose_push_raw_closing_eta vo r :
  transpose_push_raw_closing vo r
  = mk_closing_rhs
      (transpose_push_raw_closing_raw_closing vo r)
      (transpose_push_raw_closing_push vo r).
Proof.
  rewrite closing_rhs_eta
    with (r := transpose_push_raw_closing vo r).
  rewrite rhs_raw_closing_transpose_push_raw_closing.
  rewrite rhs_push_transpose_push_raw_closing.
  easy.
Qed.

Lemma transpose_push_raw_closing_raw_closing_normalized vo r :
  normalized_pushes r ->
  normalized_pushes
    (transpose_push_raw_closing_raw_closing vo r).
Proof.
  rewrite <- rhs_raw_closing_transpose_push_raw_closing.
  apply transpose_push_raw_closing_normalized; easy.
Qed.

Lemma transpose_push_normalized_pushes_cons_push
      vo1 r vo2 :
  transpose_push_raw_closing_push vo1
    (normalized_pushes_cons vo2 r)
  = transpose_push_raw_closing_push vo1 (cons vo2 r).
Proof.
  unfold normalized_pushes_cons.
  case_var_zero vo2; destruct r; cbn;
    case_var_zero vo1; try easy.
  rewrite transpose_push_reducing_pop_push; try easy.
  unfold zero_var_opt, zero_var in *; congruence.
Qed.

Lemma transpose_push_normalized_pushes_cons_raw_closing
      vo1 r vo2 :
  transpose_push_raw_closing_raw_closing vo1
    (normalized_pushes_cons vo2 r)
  = transpose_push_raw_closing_raw_closing vo1 (cons vo2 r).
Proof.
  unfold normalized_pushes_cons.
  case_var_zero vo2; destruct r; cbn;
    case_var_zero vo1; try easy.
  rewrite transpose_push_push_zero_left; easy.
Qed.

Lemma compose_normalized_pushes_cons r1 vo r2 :
  normalized_pushes r2 ->
  compose_raw_closing (normalized_pushes_cons vo r1) r2
  = compose_raw_closing (cons vo r1) r2.
Proof.
  unfold normalized_pushes_cons.
  case_var_zero vo; destruct r1; cbn; try easy.
  induction r2 as [|vo' r2]; cbn in *; try easy.
  unfold normalized_pushes_cons.
  case_var_zero vo'; destruct r2; cbn; easy.
Qed.

Lemma transpose_push_raw_closing_reverse_right vo1 vo2 r :
  shift_var_opt (transpose_push_raw_closing_push vo1 r)
    (transpose_push_raw_closing_push vo2
       (transpose_push_raw_closing_raw_closing vo1 r)) =
  transpose_push_raw_closing_push (shift_var_opt vo1 vo2) r.
Proof.
  generalize dependent vo1.
  generalize dependent vo2.
  induction r as [|vo3 r]; intros vo2 vo1; cbn; try easy.
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
