Require Import Label PeanoNat Compare_dec
        Psatz Setoid Morphisms.
Require Import Var.

(* Beta reduction for the record view of variables *)

Lemma reduce_v_label_opt_beta so n :
  v_label_opt (mk_var so n) = so.
Proof. destruct so; easy. Qed.

Lemma reduce_v_nat_beta so n :
  v_nat (mk_var so n) = n.
Proof. destruct so; easy. Qed.

Lemma reduce_v_label_opt_succ_beta v :
  v_label_opt (succ_var v) = v_label_opt v.
Proof. apply reduce_v_label_opt_beta. Qed.

Lemma reduce_v_nat_succ_beta v :
  v_nat (succ_var v) = S (v_nat v).
Proof. apply reduce_v_nat_beta. Qed.

Lemma reduce_v_label_opt_pred_beta v :
  v_label_opt (pred_var v) = v_label_opt v.
Proof. apply reduce_v_label_opt_beta. Qed.

Lemma reduce_v_nat_pred_beta v :
  v_nat (pred_var v) = pred (v_nat v).
Proof. apply reduce_v_nat_beta. Qed.

Lemma reduce_v_label_opt_shift_beta v1 v2 :
  v_label_opt (shift_var v1 v2) = v_label_opt v2.
Proof.
  destruct v1 as [n1|], v2 as [n2|]; cbn; try easy.
  unfold shift_name.
  destruct (label_dec (n_label n1) (n_label n2)); try easy.
  destruct (le_gt_dec (n_index n1) (n_index n2)); easy.
Qed.

Lemma reduce_v_label_opt_unshift_beta v1 v2 :
  v_label_opt (unshift_var v1 v2) = v_label_opt v2.
Proof.
  destruct v1 as [n1|], v2 as [n2|]; cbn; try easy.
  unfold unshift_name.
  destruct (label_dec (n_label n1) (n_label n2)); try easy.
  destruct (le_gt_dec (n_index n2) (n_index n1)); easy.
Qed.

Hint Rewrite reduce_v_label_opt_beta reduce_v_nat_beta
     reduce_v_label_opt_succ_beta reduce_v_nat_succ_beta
     reduce_v_label_opt_pred_beta reduce_v_nat_pred_beta
     reduce_v_label_opt_shift_beta reduce_v_label_opt_unshift_beta
  : reduce_vars_beta.

Ltac reduce_vars_beta :=
  try repeat (autorewrite with reduce_vars_beta; cbn).

Tactic Notation "reduce_vars_beta" "in" hyp(H) :=
  try repeat (autorewrite with reduce_vars_beta in H; cbn in H).

(* Reducing operations on variables based on their
   "record" fields. *)

Lemma reduce_shift_var_distinct v1 v2 :
  v_label_opt v1 <> v_label_opt v2 ->
  shift_var v1 v2 = v2.
Proof.
  unfold shift_var, shift_name, shift_level.
  destruct v1 as [n1|], v2 as [n2|]; try easy.
  destruct (label_dec (n_label n1) (n_label n2));
    cbn; congruence.
Qed.

Lemma reduce_shift_var_ge v1 v2 :
  v_label_opt v1 = v_label_opt v2 ->
  v_nat v1 <= v_nat v2 ->
  shift_var v1 v2 = succ_var v2.
Proof.
  unfold shift_var, shift_name, shift_level.
  destruct v1 as [n1|l1], v2 as [n2|l2]; try easy.
  - destruct (label_dec (n_label n1) (n_label n2)); cbn;
      try congruence.
    destruct (le_gt_dec (n_index n1) (n_index n2));
      try easy; lia.
  - destruct (le_gt_dec l1 l2); cbn; try easy; lia.
Qed.

Lemma reduce_shift_var_lt v1 v2 :
  v_label_opt v1 = v_label_opt v2 ->
  S (v_nat v2) <= v_nat v1 ->
  shift_var v1 v2 = v2.
Proof.
  unfold shift_var, shift_name, shift_level.
  destruct v1 as [n1|l1], v2 as [n2|l2]; try easy.
  - destruct (label_dec (n_label n1) (n_label n2)); cbn;
      try congruence.
    destruct (le_gt_dec (n_index n1) (n_index n2));
      try easy; lia.
  - destruct (le_gt_dec l1 l2); cbn; try easy; lia.
Qed.

Lemma reduce_unshift_var_distinct v1 v2 :
  v_label_opt v1 <> v_label_opt v2 ->
  unshift_var v1 v2 = v2.
Proof.
  unfold unshift_var, unshift_name, unshift_level.
  destruct v1 as [n1|l1], v2 as [n2|l2]; try easy.
  destruct (label_dec (n_label n1) (n_label n2)); cbn;
    congruence.
Qed.

Lemma reduce_unshift_var_gt v1 v2 :
  v_label_opt v1 = v_label_opt v2 ->
  S (v_nat v1) <= v_nat v2 ->
  unshift_var v1 v2 = pred_var v2.
Proof.
  unfold unshift_var, unshift_name, unshift_level.
  destruct v1 as [n1|l1], v2 as [n2|l2]; try easy.
  - destruct (label_dec (n_label n1) (n_label n2)); cbn;
      try congruence.
    destruct (le_gt_dec (n_index n2) (n_index n1));
      try easy; lia.
  - destruct (le_gt_dec l2 l1); cbn; try easy; lia.
Qed.

Lemma reduce_unshift_var_le v1 v2 :
  v_label_opt v1 = v_label_opt v2 ->
  v_nat v2 <= v_nat v1 ->
  unshift_var v1 v2 = v2.
Proof.
  unfold unshift_var, unshift_name, unshift_level.
  destruct v1 as [n1|l1], v2 as [n2|l2]; try easy.
  - destruct (label_dec (n_label n1) (n_label n2));
      try congruence.
    destruct (le_gt_dec (n_index n2) (n_index n1)); cbn;
      try easy; lia.
  - destruct (le_gt_dec l2 l1); cbn; try easy; lia.
Qed.

Lemma reduce_pop_var_bound_zero v1 v2 :
  v_label_opt v2 = None ->
  v_nat v2 = 0 ->
  pop_var v1 v2 = v1.
Proof. destruct v1 as [n1|l1], v2 as [n2|[|l2]]; easy. Qed.

Lemma reduce_pop_var_free v1 v2 :
  v_label_opt v2 <> None ->
  pop_var v1 v2 = shift_var v1 v2.
Proof. destruct v1 as [n1|l1], v2 as [n2|l2]; easy. Qed.

Lemma reduce_pop_var_bound_nonzero v1 v2 :
  v_label_opt v2 = None ->
  v_nat v2 <> 0 ->
  pop_var v1 v2 = shift_var v1 (pred_var v2).
Proof.
  destruct v1 as [n1|l1], v2 as [n2|[|l2]]; easy.
Qed.

Lemma reduce_push_var_none v :
  push_var None v = shift_var zero_var v.
Proof. destruct v as [n|l]; easy. Qed.

Lemma reduce_push_var_some_eq v1 v2 :
  v_label_opt v1 = v_label_opt v2 ->
  v_nat v1 = v_nat v2 ->
  push_var (Some v1) v2 = zero_var.
Proof.
  intros Heq1 Heq2; rewrite (lift_var_eq Heq1 Heq2).
  unfold push_var, var_opt_var_eqb.
  destruct (var_opt_var_dec (Some v2) v2); easy.
Qed.

Lemma reduce_push_var_some_distinct v1 v2 :
  v_label_opt v1 <> v_label_opt v2 ->
  push_var (Some v1) v2 = shift_var zero_var v2.
Proof.
  intros.
  rewrite <- reduce_unshift_var_distinct
    with (v1 := v1) (v2 := shift_var zero_var v2)
    by (reduce_vars_beta; easy).
  unfold push_var, var_opt_var_eqb.
  destruct (var_opt_var_dec (Some v1) v2);
    try congruence; easy.
Qed.

Lemma reduce_push_var_some_neq v1 v2 :
  v_label_opt v1 = v_label_opt v2 ->
  v_nat v1 <> v_nat v2 ->
  push_var (Some v1) v2
  = unshift_var v1 (shift_var zero_var v2).
Proof.
  intros; unfold push_var, var_opt_var_eqb.
  destruct (var_opt_var_dec (Some v1) v2);
    try congruence; easy.
Qed.

Lemma reduce_swap_var_free v :
  v_label_opt v <> None ->
  swap_var v = v.
Proof. destruct v as [n|l]; easy. Qed.

Lemma reduce_swap_var_bound_zero v :
  v_label_opt v = None ->
  v_nat v = 0 ->
  swap_var v = succ_var zero_var.
Proof. destruct v as [n|[|l]]; easy. Qed.

Lemma reduce_swap_var_bound_one v :
  v_label_opt v = None ->
  v_nat v = 1 ->
  swap_var v = zero_var.
Proof. destruct v as [n|[|[|l]]]; easy. Qed.

Lemma reduce_swap_var_bound_gt_one v :
  v_label_opt v = None ->
  v_nat v > 1 ->
  swap_var v = v.
Proof. destruct v as [n|[|[|l]]]; cbn; try easy; lia. Qed.

Lemma reduce_pred_var_succ_var v :
  pred_var (succ_var v) = v.
Proof.
  unfold pred_var, succ_var.
  apply lift_var_eq; reduce_vars_beta; easy.
Qed.

Lemma reduce_succ_var_pred_var v :
  0 < v_nat v ->
  succ_var (pred_var v) = v.
Proof.
  intros; unfold pred_var, succ_var.
  apply lift_var_eq; reduce_vars_beta; try easy; lia.
Qed.

Lemma reduce_lift_var_op_bound_zero op v :
  v_label_opt v = None ->
  v_nat v = 0 ->
  lift_var_op op v = v.
Proof. destruct v as [n|l]; cbn; intros; subst; easy. Qed.

Lemma reduce_lift_var_op_free op v :
  v_label_opt v <> None ->
  lift_var_op op v = shift_var zero_var (op v).
Proof. destruct v as [n|l]; easy. Qed.

Lemma reduce_lift_var_op_bound_nonzero op v :
  v_label_opt v = None ->
  v_nat v <> 0 ->
  lift_var_op op v
  = shift_var zero_var (op (unshift_var zero_var v)).
Proof. destruct v as [n|[|l]]; easy. Qed.

Ltac solve_v_label_opt_equation :=
  reduce_vars_beta; congruence.

Ltac solve_v_label_opt_and_v_nat_equation :=
  reduce_vars_beta; try congruence; lia.

Hint Rewrite reduce_v_label_opt_beta reduce_v_nat_beta
     reduce_v_label_opt_succ_beta reduce_v_nat_succ_beta
     reduce_v_label_opt_pred_beta reduce_v_nat_pred_beta
     reduce_v_label_opt_shift_beta reduce_v_label_opt_unshift_beta
     reduce_push_var_none reduce_pred_var_succ_var
  : reduce_vars.

Hint Rewrite reduce_shift_var_distinct
     reduce_unshift_var_distinct reduce_pop_var_free
     reduce_push_var_some_distinct reduce_swap_var_free
     reduce_lift_var_op_free
     using solve_v_label_opt_equation : reduce_vars.

Hint Rewrite reduce_shift_var_ge reduce_shift_var_lt
     reduce_unshift_var_le reduce_unshift_var_gt
     reduce_pop_var_bound_zero reduce_pop_var_bound_nonzero
     reduce_push_var_some_eq reduce_push_var_some_neq
     reduce_swap_var_bound_zero reduce_swap_var_bound_one
     reduce_swap_var_bound_gt_one reduce_succ_var_pred_var
     reduce_lift_var_op_bound_zero
     reduce_lift_var_op_bound_nonzero
     using solve_v_label_opt_and_v_nat_equation : reduce_vars.

Ltac reduce_vars :=
  try repeat
      (autorewrite with reduce_vars; cbn);
  try repeat
    ((rewrite_strat (bottomup (hints reduce_vars))); cbn).

(* Useful lemma *)
Lemma red_var_neq v1 v2 :
  v_label_opt v1 = v_label_opt v2 ->
  v1 <> v2 <-> v_nat v1 <> v_nat v2.
Proof.
  intro Heq1; split.
  - intros Hneq Heq2; apply Hneq.
    rewrite (eta_expand_var v1).
    rewrite (eta_expand_var v2).
    rewrite Heq1, Heq2; easy.
  - intros Hneq Heq2; apply Hneq.
    rewrite Heq2; easy.
Qed.

Hint Rewrite red_var_neq using (cbn; congruence) : red_var_neq.

(* Case split on the order of the var parameters. *)
Ltac case_vars v1 v2 :=
  let Heql := fresh "Heql" in
  let Hneql := fresh "Hneql" in
  destruct (label_opt_dec (v_label_opt v1) (v_label_opt v2))
    as [Heql|Hneql];
    [replace (v_label_opt v2) with (v_label_opt v1) by apply Heql;
     autorewrite with red_var_neq in *;
     let Hltn := fresh "Hltn" in
     let Heqn := fresh "Heqn" in
     let Hgtn := fresh "Hgtn" in
     destruct (Compare_dec.lt_eq_lt_dec (v_nat v1) (v_nat v2))
        as [[Hltn|Heqn]|Hgtn];
     [reduce_vars_beta in Hltn
     |replace v2 with v1
       by apply (@lift_var_eq v1 v2 Heql Heqn);
      reduce_vars_beta in Heqn|
      reduce_vars_beta in Hgtn];
     reduce_vars_beta in Heql
    | reduce_vars_beta in Hneql];
    reduce_vars;
    try rewrite (eta_reduce_var v1);
    try rewrite (eta_reduce_var v2);
    try solve [exfalso; try congruence; try lia].

Ltac case_var_zero v :=
  case_vars zero_var v.

Ltac case_var_one v :=
  case_vars (succ_var zero_var) v.

(* Identities *)

Lemma pop_zero_identity :
  pop_var zero_var =v= 1.
Proof.
  intros v.
  case_var_zero v; easy.
Qed.

Lemma push_zero_identity :
  push_var (Some zero_var) =v= 1.
Proof.
  intros v.
  case_var_zero v; easy.
Qed.

Lemma pop_push_identity v :
  pop_var v @ push_var (Some v) =v= 1.
Proof.
  intros v'.
  case_vars v v'; try easy;
    case_var_zero v'; easy.
Qed.

Lemma pop_push_identity' v op :
  pop_var v @ (push_var (Some v) @ op) =v= op.
Proof.
  rewrite var_op_associative, pop_push_identity,
    var_op_left_identity.
  easy.
Qed.

Lemma push_pop_identity v :
  push_var (Some v) @ pop_var v =v= 1.
Proof.
  intros v'.
  case_var_zero v'; try easy;
    case_vars v v'; easy.
Qed.

Lemma push_pop_identity' v op :
  push_var (Some v) @ (pop_var v @ op) =v= op.
Proof.
  rewrite var_op_associative,
    push_pop_identity, var_op_left_identity.
  easy.
Qed.

Lemma swap_swap_identity :
  swap_var @ swap_var =v= 1.
Proof.
  intros v.
  case_var_zero v; try easy.
  case_var_one v; easy.
Qed.

Lemma swap_swap_identity' op :
  swap_var @ (swap_var @ op) =v= op.
Proof.
  rewrite var_op_associative,
    swap_swap_identity, var_op_left_identity.
  easy.
Qed.

(* [lift_var_op] distributes over composition and identity *)

Lemma lift_var_op_compose op1 op2 :
  lift_var_op (op1 @ op2)
  =v= lift_var_op op1 @ lift_var_op op2.
Proof.
  intros v.
  case_var_zero v; try easy.
  - case_var_zero (op2 (pred_var v)); easy.
  - case_var_zero (op2 v); easy.
Qed.

Lemma lift_var_op_id :
  lift_var_op 1 =v= 1.
Proof.
  intros v.
  case_var_zero v; easy.
Qed.

(* Tactic to simplify compositions of var operations *)

Hint Rewrite <- var_op_associative
  : normalize_var_op_compose.
Hint Rewrite var_op_left_identity var_op_right_identity
  : normalize_var_op_compose.

Hint Rewrite @lift_var_op_id @lift_var_op_compose
  : push_lift_var_op.

Ltac simplify_var_ops :=
  autorewrite with push_lift_var_op;
  autorewrite with normalize_var_op_compose.

(* [swap_var] transposes with lifted morphisms *)

Lemma transpose_swap_lifted op :
  swap_var @ lift_var_op (lift_var_op op)
  =v= lift_var_op (lift_var_op op) @ swap_var.
Proof.
  intros v.
  case_var_zero v; try easy.
  - case_var_one v; try easy.
    case_var_zero (op (pred_var (pred_var v))); easy.
  - case_var_zero (op v); easy.
Qed.

Lemma transpose_swap_lifted' op1 op2 :
  swap_var @ (lift_var_op (lift_var_op op1) @ op2)
  =v= lift_var_op (lift_var_op op1) @ (swap_var @ op2).
Proof.
  rewrite var_op_associative.
  rewrite transpose_swap_lifted.
  rewrite <- var_op_associative.
  easy.
Qed.

(* Transposing pop operations

   We wish to reason about transposing "pop" operations (i.e.
   [cycle_out] and [open]).  These operations are not commutative,
   however they can be transposed by applying [shift] and [unshift]
   transformations to them.

   This situation is very close to that studied by the "operational
   transforms" literature in the context of collaborative text
   editors. However, rather than define the "ET" and "IT"
   transformations for our operations as they do, we will use a
   slightly different formulation.
 *)

Lemma transpose_pops v1 v2 :
  pop_var v1 @ lift_var_op (pop_var v2)
  =v= pop_var (shift_var v1 v2)
      @ lift_var_op (pop_var (unshift_var v2 v1))
      @ swap_var.
Proof.
  intros v3.
  case_var_zero v3; case_var_one v3.
  - case_vars v1 v2.
    + case_vars (pred_var (pred_var v3)) v1; try easy.
      case_vars (pred_var (pred_var v3)) v2; easy.
    + case_vars (pred_var (pred_var v3)) v1; easy.
    + case_vars (pred_var v3) v1; try easy.
      case_vars (pred_var (pred_var v3)) v2; try easy.
    + case_vars (pred_var (pred_var v3)) v1; easy.
  - case_var_zero v2; easy.
  - case_vars v1 v2; case_var_zero v1; easy.
  - case_vars v2 v1;
      case_vars v3 v2; try easy.
    + case_vars v3 (pred_var v1); easy.
    + case_vars v3 (pred_var v1); easy.
    + case_vars v1 v3; easy.
Qed.

Lemma transpose_pops' v1 v2 op :
  pop_var v1 @ lift_var_op (pop_var v2) @ op
  =v= pop_var (shift_var v1 v2)
      @ lift_var_op (pop_var (unshift_var v2 v1))
      @ swap_var @ op.
Proof.
  rewrite var_op_associative.
  rewrite transpose_pops.
  rewrite <- var_op_associative.
  easy.
Qed.

(* Permutations of pop operations

   Beyond transposing pairs of pop operations, we wish to reason
   about arbitrary permutations of sequences of pop operations.

   Given a sequence of n pop operations, rewriting with
   [transpose_pushes] essentially gives us transpositions σᵢ
   which swap the ith and (i+1)th operations. The group of
   permutations of n operations can be generated from these
   transpositions and the following equations:

   1) σᵢ ∘ σⱼ = σⱼ ∘ σᵢ where |i - j| > 1

   2) σᵢ ∘ σᵢ = 1

   3) σᵢ ∘ σᵢ₊₁ ∘ σᵢ = σᵢ₊₁ ∘ σᵢ ∘ σᵢ₊₁

   The first equation follows automatically since rewriting
   with [transpose_pops] only affects the operations that
   are transposed.

   Lemmas [transpose_pops_squared_left] and
   [transpose_pops_squared_right] below are equivalent to
   the second equation.

   Lemmas [transpose_pops_reverse_left],
   [transpose_pops_reverse_middle] and
   [transpose_pops_reverse_right] below are equivalent to
   the third equation.
 *)

Lemma transpose_pops_squared_left v1 v2 :
  shift_var (shift_var v1 v2) (unshift_var v2 v1) = v1.
Proof. case_vars v1 v2; easy. Qed.

Lemma transpose_pops_squared_right v1 v2 :
  unshift_var (unshift_var v2 v1) (shift_var v1 v2) = v2.
Proof. case_vars v1 v2; easy. Qed.

Lemma transpose_pops_reverse_left v1 v2 v3 :
  shift_var
    (shift_var v1 v2)
    (shift_var (unshift_var v2 v1) v3)
  = shift_var v1 (shift_var v2 v3).
Proof.
  case_vars v2 v1; case_vars v3 v2; try easy.
  - case_vars (pred_var v1) v3; easy.
  - case_vars (pred_var v1) v3; easy.
  - case_vars v1 v3; easy.
Qed.

Lemma transpose_pops_reverse_middle v1 v2 v3 :
  shift_var
    (unshift_var (shift_var v2 v3) v1)
    (unshift_var v3 v2)
  = unshift_var
      (shift_var (unshift_var v2 v1) v3)
      (shift_var v1 v2).
Proof.
  case_vars v2 v1; case_vars v3 v2; try easy.
  - case_vars (pred_var v1) v3; easy.
  - case_vars (pred_var v1) v3; easy.
  - case_vars v1 v3; easy.
Qed.

Lemma transpose_pops_reverse_right v1 v2 v3 :
  unshift_var
    (unshift_var v3 v2)
    (unshift_var (shift_var v2 v3) v1)
  = unshift_var v3
      (unshift_var v2 v1).
Proof.
  case_vars v2 v1; case_vars v3 v2; try easy.
  - case_vars (pred_var v1) v3; easy.
  - case_vars (pred_var v1) v3; easy.
  - case_vars v1 v3; easy.
Qed.

(* Permutations of "push" operations. As with the pop
   operations, we want to reason about permutations of the
   "push" operations (i.e. weak, close and cycle_in). As with
   pops, we define arbitrary transpositions and then the
   equations on those transpositions required to define the
   full group of permutations. *)

Lemma transpose_pushes vo1 vo2 :
  lift_var_op (push_var vo1) @ push_var vo2
  =v= swap_var
      @ lift_var_op (push_var (unshift_var_opt vo1 vo2))
      @ push_var (shift_var_opt vo2 vo1).
Proof.
  intros v3.
  destruct vo1 as [v1|], vo2 as [v2|]; simplify_var_ops; cbn.
  - case_var_zero v3; case_vars v1 v2; case_vars v3 v1; try easy;
      case_vars v3 v2; try easy;
        case_vars (pred_var v3) v1; easy.
  - case_var_zero v3; case_vars v1 v3; easy.
  - case_var_zero v3; case_vars v2 v3; easy.
  - case_var_zero v3; easy.
Qed.

Lemma transpose_pushes' vo1 vo2 op :
  lift_var_op (push_var vo1) @ push_var vo2 @ op
  =v= swap_var
      @ lift_var_op (push_var (unshift_var_opt vo1 vo2))
      @ push_var (shift_var_opt vo2 vo1)
      @ op.
Proof.
  rewrite var_op_associative.
  rewrite transpose_pushes.
  rewrite <- var_op_associative.
  easy.
Qed.


Lemma transpose_pushes_squared_left vo1 vo2 :
  unshift_var_opt
    (unshift_var_opt vo1 vo2) (shift_var_opt vo2 vo1)
  = vo1.
Proof.
  destruct vo1 as [v1|], vo2 as [v2|]; cbn; try easy.
  rewrite transpose_pops_squared_right; easy.
Qed.

Lemma transpose_pushes_squared_right vo1 vo2 :
  shift_var_opt
    (shift_var_opt vo2 vo1) (unshift_var_opt vo1 vo2)
  = vo2.
Proof.
  destruct vo1 as [v1|], vo2 as [v2|]; cbn; try easy.
  rewrite transpose_pops_squared_left; easy.
Qed.

Lemma transpose_pushes_reverse_left vo1 vo2 vo3 :
  unshift_var_opt (unshift_var_opt vo1 vo2)
    (unshift_var_opt (shift_var_opt vo2 vo1) vo3)
  = unshift_var_opt vo1 (unshift_var_opt vo2 vo3).
Proof.
  destruct vo1 as [v1|], vo2 as [v2|], vo3 as [v3|];
    cbn in *; try easy.
  rewrite transpose_pops_reverse_right; easy.
Qed.

Lemma transpose_pushes_reverse_middle vo1 vo2 vo3 :
  unshift_var_opt
    (shift_var_opt (unshift_var_opt vo2 vo3) vo1)
    (shift_var_opt vo3 vo2)
  = shift_var_opt
      (unshift_var_opt (shift_var_opt vo2 vo1) vo3)
      (unshift_var_opt vo1 vo2).
Proof.
  destruct vo1 as [v1|], vo2 as [v2|], vo3 as [v3|];
    cbn in *; try easy.
  rewrite transpose_pops_reverse_middle; easy.
Qed.

Lemma transpose_pushes_reverse_right vo1 vo2 vo3 :
  shift_var_opt
    (shift_var_opt vo3 vo2)
    (shift_var_opt (unshift_var_opt vo2 vo3) vo1)
  = shift_var_opt vo3 (shift_var_opt vo2 vo1).
Proof.
  destruct vo1 as [v1|], vo2 as [v2|], vo3 as [v3|];
    cbn in *; try easy.
  rewrite transpose_pops_reverse_left; easy.
Qed.

(* Moving pushes in front of pops.

   We also wish to reason about moving pushes in front of
   pops.  This will not work if the pop and the push reduce
   to the identity, so we need that an inequality as a
   precondition on transposition.

   Since we will be ignoring the inverse case of moving pops
   in front of pushes, we will not have the full group of
   permutations, but some of the "reverse" equations are
   still relevant.  *)

Lemma transpose_push_pop vo1 v2 :
  vo1 <> Some v2 ->
  push_var vo1 @ pop_var v2
  =v= lift_var_op (pop_var (unshift_var_opt_var vo1 v2))
      @ swap_var
      @ lift_var_op (push_var (unshift_var_var_opt v2 vo1)).
Proof.
  intros Hirr v3.
  destruct vo1 as [v1|]; simplify_var_ops; cbn.
  - assert (v1 <> v2) by congruence.
    case_var_zero v3; case_vars v1 v2.
    + case_vars (pred_var v3) v1; try easy.
      case_vars (pred_var v3) v2; easy.
    + case_vars v3 v1; try easy.
      case_vars (pred_var v3) v2; easy.
    + case_vars (pred_var v3) v1; easy.
    + case_vars v3 v2; easy.
    + case_vars v3 v2; easy.
    + case_vars v3 v2; easy.
    + case_vars v3 v1; try easy.
      case_vars v3 v2; easy.
    + case_vars (pred_var v1) v3; try easy.
      case_vars v3 v2; easy.
    + case_vars v3 v1; easy.
  - case_var_zero v3; easy.
Qed.

Lemma transpose_push_pop' vo1 v2 op :
  vo1 <> Some v2 ->
  push_var vo1 @ pop_var v2 @ op
  =v= lift_var_op (pop_var (unshift_var_opt_var vo1 v2))
      @ swap_var
      @ lift_var_op (push_var (unshift_var_var_opt v2 vo1))
      @ op.
Proof.
  intros Hneq.
  rewrite var_op_associative.
  rewrite transpose_push_pop by easy.
  rewrite <- var_op_associative.
  easy.
Qed.

Lemma transpose_push_push_pop_reverse_left vo1 vo2 v3 :
  unshift_var_opt_var
    (unshift_var_opt vo1 vo2)
    (unshift_var_opt_var (shift_var_opt vo2 vo1) v3)
  = unshift_var_opt_var vo1 (unshift_var_opt_var vo2 v3).
Proof.
  destruct vo1 as [v1|], vo2 as [v2|]; cbn; try easy.
  rewrite transpose_pops_reverse_right; easy.
Qed.

Lemma transpose_push_push_pop_reverse_middle_aux v1 v2 v3 :
  unshift_var
    (unshift_var (unshift_var v2 v3) v1)
    (unshift_var v3 v2)
  = unshift_var
      (unshift_var (shift_var v2 v1) v3)
      (unshift_var v1 v2).
Proof.
  case_vars v2 v1; case_vars v3 v2; try easy.
  - case_vars (pred_var v3) v1; easy.
  - case_vars (pred_var v3) v1; easy.
  - case_vars v1 v3; easy.
Qed.

Lemma transpose_push_push_pop_reverse_middle vo1 vo2 v3 :
  unshift_var_opt
    (unshift_var_var_opt
       (unshift_var_opt_var vo2 v3) vo1)
    (unshift_var_var_opt v3 vo2)
  = unshift_var_var_opt
      (unshift_var_opt_var (shift_var_opt vo2 vo1) v3)
      (unshift_var_opt vo1 vo2).
Proof.
  destruct vo1 as [v1|], vo2 as [v2|]; cbn; try easy.
  rewrite transpose_push_push_pop_reverse_middle_aux; easy.
Qed.

Lemma transpose_push_push_pop_reverse_right_aux v1 v2 v3 :
  v1 <> unshift_var v2 v3 ->
  shift_var
    (unshift_var v3 v2)
      (unshift_var (unshift_var v2 v3) v1)
  = unshift_var v3 (shift_var v2 v1).
Proof.
  case_vars v2 v1; case_vars v3 v2; try easy.
  - case_vars (pred_var v3) v1; easy.
  - case_vars v1 v3; easy.
Qed.

Lemma transpose_push_push_pop_reverse_right vo1 vo2 v3 :
  vo1 <> Some (unshift_var_opt_var vo2 v3) ->
  shift_var_opt
    (unshift_var_var_opt v3 vo2)
      (unshift_var_var_opt (unshift_var_opt_var vo2 v3) vo1)
  = unshift_var_var_opt v3 (shift_var_opt vo2 vo1).
Proof.
  destruct vo1 as [v1|], vo2 as [v2|];
    cbn; try easy; intros.
  rewrite transpose_push_push_pop_reverse_right_aux; try easy;
    congruence.
Qed.

Lemma transpose_push_pop_pop_reverse_left vo1 v2 v3 :
  (unshift_var_var_opt v2 vo1) <> Some v3 ->
  shift_var
    (unshift_var_opt_var vo1 v2)
    (unshift_var_opt_var (unshift_var_var_opt v2 vo1) v3)
  = unshift_var_opt_var vo1 (shift_var v2 v3).
Proof.
  destruct vo1 as [v1|]; cbn; try easy; intros.
  rewrite transpose_push_push_pop_reverse_right_aux; try easy;
    congruence.
Qed.

Lemma transpose_push_pop_pop_reverse_middle vo1 v2 v3 :
  unshift_var_opt_var
    (unshift_var_var_opt (shift_var v2 v3) vo1)
    (unshift_var v3 v2)
  = unshift_var
      (unshift_var_opt_var (unshift_var_var_opt v2 vo1) v3)
      (unshift_var_opt_var vo1 v2).
Proof.
  destruct vo1 as [v1|]; cbn; try easy.
  rewrite transpose_push_push_pop_reverse_middle_aux; easy.
Qed.

Lemma transpose_push_pop_pop_reverse_right vo1 v2 v3 :
  unshift_var_var_opt
    (unshift_var v3 v2)
    (unshift_var_var_opt (shift_var v2 v3) vo1)
  = unshift_var_var_opt v3 (unshift_var_var_opt v2 vo1).
Proof.
  destruct vo1 as [v1|]; cbn; try easy.
  rewrite transpose_pops_reverse_right; easy.
Qed.

(* In addition to the equalities between permutations, we
   also need to show that permutations commute with reducing
   operations.

   Given a sequence of n operations opₙ, such that:

     opᵢ₊₁ . opᵢ₊₂ = 1

   then:

     σᵢ ∘ σᵢ₊₁ = 1

   and:

     σᵢ₊₂ ∘ σᵢ₊₁ = 1

   In other words, if two operations reduce to the identity
   then transposing an operation over both of them in
   either direction is equivalent to doing nothing.
*)

Lemma transpose_reducing_push_pop_aux v1 v2 :
  unshift_var v1 (shift_var v1 v2) = v2.
Proof. case_vars v1 v2; easy. Qed.

Lemma transpose_reducing_pop_push_aux v1 v2 :
  v1 <> v2 ->
  shift_var v1 (unshift_var v1 v2) = v2.
Proof. case_vars v1 v2; easy. Qed.

(* Moving a pop backwards over a reducing pop and push *)
Lemma transpose_pop_reducing_pop_push v1 v2 :
  v1 <> v2 ->
  shift_var v1 (unshift_var_opt_var (Some v1) v2) = v2.
Proof.
  intros Hneq; cbn.
  rewrite transpose_reducing_pop_push_aux by easy.
  easy.
Qed.

(* Moving a pop backwards over a reducing push and pop *)
Lemma transpose_pop_reducing_push_pop v1 v2 :
  unshift_var_opt_var (Some v1) (shift_var v1 v2) = v2.
Proof.
  apply transpose_reducing_push_pop_aux.
Qed.

(* Moving a push forwards over a reducing pop and push *)
Lemma transpose_push_reducing_pop_push v1 vo2 :
  Some v1 <> vo2 ->
  shift_var_opt (Some v1) (unshift_var_var_opt v1 vo2) = vo2.
Proof.
  intros Hneq.
  destruct vo2; cbn; try easy.
  rewrite transpose_reducing_pop_push_aux by congruence.
  easy.
Qed.

(* Moving a push forwards over a reducing push and pop *)
Lemma transpose_push_reducing_push_pop v1 vo2 :
  unshift_var_var_opt v1 (shift_var_opt (Some v1) vo2) = vo2.
Proof.
  destruct vo2; cbn; try easy.
  rewrite transpose_reducing_push_pop_aux by congruence.
  easy.
Qed.
