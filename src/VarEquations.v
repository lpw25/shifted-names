Require Import Label PeanoNat Compare_dec
        Psatz Setoid Morphisms.
Require Import Var.

(* Eta expansion for the record view of variables *)

Definition eta_expand_var v :
  v = mk_var (v_label_opt v) (v_nat v).
Proof. destruct v; easy. Qed.

Definition eta_reduce_var v :
  mk_var (v_label_opt v) (v_nat v) = v.
Proof. destruct v; easy. Qed.

Definition lift_var_eq {v1 v2} :
  v_label_opt v1 = v_label_opt v2 ->
  v_nat v1 = v_nat v2 ->
  v1 = v2.
Proof.
  intros Heq1 Heq2.
  rewrite (eta_expand_var v1), Heq1, Heq2, (eta_reduce_var v2).
  easy.
Qed.

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

(* Useful lemmas for variable inequalities *)
Lemma red_var_neq v1 v2 :
  v_label_opt v1 = v_label_opt v2 ->
  v1 <> v2 <-> v_nat v1 <> v_nat v2.
Proof.
  intro Heq1; split.
  - intros Hneq; contradict Hneq.
    rewrite (eta_expand_var v1).
    rewrite (eta_expand_var v2).
    congruence.
  - congruence.
Qed.

Lemma v_nat_neq v1 v2 :
  v_nat v1 <> v_nat v2 ->
  v1 <> v2.
Proof. congruence. Qed.

Lemma v_label_opt_neq v1 v2 :
  v_label_opt v1 <> v_label_opt v2 ->
  v1 <> v2.
Proof. congruence. Qed.

(* Useful lemmas for variable equality *)

Lemma var_eqb_true v1 v2 :
  v1 = v2 ->
  var_eqb v1 v2 = true.
Proof. unfold var_eqb; destruct var_dec; easy. Qed.

Lemma var_eqb_false v1 v2 :
  v1 <> v2 ->
  var_eqb v1 v2 = false.
Proof. unfold var_eqb; destruct var_dec; easy. Qed.

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

Lemma reduce_pop_var_none v1 :
  pop_var v1 None = v1.
Proof. easy. Qed.

Lemma reduce_pop_var_some v1 v2 :
  pop_var v1 (Some v2) = shift_var v1 v2.
Proof. easy. Qed.

Lemma reduce_push_var_eq v1 v2 :
  v_label_opt v1 = v_label_opt v2 ->
  v_nat v1 = v_nat v2 ->
  push_var v1 v2 = None.
Proof.
  intros Heq1 Heq2; rewrite (lift_var_eq Heq1 Heq2).
  unfold push_var, var_eqb.
  destruct (var_dec v2 v2); easy.
Qed.

Lemma reduce_push_var_neq v1 v2 :
  v1 <> v2 ->
  push_var v1 v2 = Some (unshift_var v1 v2).
Proof.
  intros; unfold push_var, var_eqb.
  destruct (var_dec v1 v2); try congruence; easy.
Qed.

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

Lemma reduce_is_shifting_var_distinct v1 v2 :
  v_label_opt v1 <> v_label_opt v2 ->
  is_shifting_var v1 v2 = false.
Proof.
  unfold is_shifting_var, label_opt_eqb.
  destruct (label_opt_dec (v_label_opt v1) (v_label_opt v2));
    easy.
Qed.

Lemma reduce_is_shifting_var_ge v1 v2 :
  v_label_opt v1 = v_label_opt v2 ->
  v_nat v1 <= v_nat v2 ->
  is_shifting_var v1 v2 = true.
Proof.
  unfold is_shifting_var; intros Heq Hge.
  rewrite Heq, label_opt_eqb_reflexive, Bool.andb_true_l.
  apply leb_correct; easy.
Qed.

Lemma reduce_is_shifting_var_lt v1 v2 :
  v_label_opt v1 = v_label_opt v2 ->
  S (v_nat v2) <= v_nat v1 ->
  is_shifting_var v1 v2 = false.
Proof.
  unfold is_shifting_var; intros Heq Hlt.
  rewrite Heq, label_opt_eqb_reflexive, Bool.andb_true_l.
  apply leb_iff_conv; easy.
Qed.

Lemma reduce_is_unshifting_var_distinct v1 v2 :
  v_label_opt v1 <> v_label_opt v2 ->
  is_unshifting_var v1 v2 = false.
Proof.
  unfold is_unshifting_var, label_opt_eqb.
  destruct (label_opt_dec (v_label_opt v1) (v_label_opt v2));
    easy.
Qed.

Lemma reduce_is_unshifting_var_gt v1 v2 :
  v_label_opt v1 = v_label_opt v2 ->
  v_nat v1 < v_nat v2 ->
  is_unshifting_var v1 v2 = true.
Proof.
  unfold is_unshifting_var; intros Heq Hge.
  rewrite Heq, label_opt_eqb_reflexive, Bool.andb_true_l.
  apply leb_correct; easy.
Qed.

Lemma reduce_is_unshifting_var_le v1 v2 :
  v_label_opt v1 = v_label_opt v2 ->
  v_nat v2 <= v_nat v1 ->
  is_unshifting_var v1 v2 = false.
Proof.
  unfold is_unshifting_var; intros Heq Hlt.
  rewrite Heq, label_opt_eqb_reflexive, Bool.andb_true_l.
  apply leb_iff_conv; lia.
Qed.

Lemma reduce_is_less_equal_var_distinct v1 v2 :
  v_label_opt v1 <> v_label_opt v2 ->
  is_less_equal_var v1 v2
  = is_less_than_label_opt (v_label_opt v1) (v_label_opt v2).
Proof.
  unfold is_less_equal_var, label_opt_eqb; intros Hneq.
  rewrite reduce_is_shifting_var_distinct by easy.
  rewrite Bool.orb_false_r; easy.
Qed.

Lemma reduce_is_less_equal_var_indistinct v1 v2 :
  v_label_opt v1 = v_label_opt v2 ->
  is_less_equal_var v1 v2 = is_shifting_var v1 v2.
Proof.
  unfold is_less_equal_var; intros Heq.
  rewrite Heq, is_less_than_label_opt_irreflexive.
  rewrite Bool.orb_false_l; easy.
Qed.

Lemma reduce_is_less_than_var_distinct v1 v2 :
  v_label_opt v1 <> v_label_opt v2 ->
  is_less_than_var v1 v2
  = is_less_than_label_opt (v_label_opt v1) (v_label_opt v2).
Proof.
  unfold is_less_than_var, label_opt_eqb; intros Hneq.
  rewrite reduce_is_unshifting_var_distinct by easy.
  rewrite Bool.orb_false_r; easy.
Qed.

Lemma reduce_is_less_than_var_indistinct v1 v2 :
  v_label_opt v1 = v_label_opt v2 ->
  is_less_than_var v1 v2 = is_unshifting_var v1 v2.
Proof.
  unfold is_less_than_var; intros Heq.
  rewrite Heq, is_less_than_label_opt_irreflexive.
  rewrite Bool.orb_false_l; easy.
Qed.

Lemma reduce_var_eqb_eq v1 v2 :
  v_label_opt v1 = v_label_opt v2 ->
  v_nat v1 = v_nat v2 ->
  var_eqb v1 v2 = true.
Proof.
  unfold var_eqb; intros.
  destruct var_dec;
    try rewrite red_var_neq in * by easy; easy.
Qed.

Lemma reduce_var_eqb_neq v1 v2 :
  v1 <> v2 ->
  var_eqb v1 v2 = false.
Proof.
  unfold var_eqb; intros.
  destruct var_dec; congruence.
Qed.

Ltac solve_v_label_opt_equation :=
  try congruence; reduce_vars_beta; congruence.

Ltac solve_v_label_opt_and_v_nat_equation :=
  try congruence; reduce_vars_beta; try congruence; lia.

Ltac solve_var_neq :=
  try congruence;
  try solve [apply v_nat_neq;
             solve_v_label_opt_and_v_nat_equation];
  solve [apply v_label_opt_neq; solve_v_label_opt_equation].

Hint Rewrite reduce_v_label_opt_beta reduce_v_nat_beta
     reduce_v_label_opt_succ_beta reduce_v_nat_succ_beta
     reduce_v_label_opt_pred_beta reduce_v_nat_pred_beta
     reduce_v_label_opt_shift_beta reduce_v_label_opt_unshift_beta
     reduce_pred_var_succ_var reduce_pop_var_none reduce_pop_var_some
  : reduce_vars.

Hint Rewrite reduce_shift_var_distinct
     reduce_unshift_var_distinct
     reduce_is_shifting_var_distinct
     reduce_is_unshifting_var_distinct
     reduce_is_less_equal_var_distinct
     reduce_is_less_equal_var_indistinct
     reduce_is_less_than_var_distinct
     reduce_is_less_than_var_indistinct
     using solve_v_label_opt_equation : reduce_vars.

Hint Rewrite reduce_shift_var_ge reduce_shift_var_lt
     reduce_unshift_var_le reduce_unshift_var_gt
     reduce_push_var_eq
     reduce_succ_var_pred_var
     reduce_is_shifting_var_ge reduce_is_shifting_var_lt
     reduce_is_unshifting_var_gt reduce_is_unshifting_var_le
     reduce_var_eqb_eq
     using solve_v_label_opt_and_v_nat_equation : reduce_vars.

Hint Rewrite reduce_push_var_neq reduce_var_eqb_neq
     using solve_var_neq : reduce_vars.

Ltac reduce_vars :=
  try repeat
      (autorewrite with reduce_vars in *; cbn in *);
  try repeat
    ((rewrite_strat (bottomup (hints reduce_vars))); cbn).

Hint Rewrite red_var_neq
     using solve_v_label_opt_equation : red_var_neq.

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

(* Case split on the order of a var and an optional var *)

Tactic Notation "case_var_var_opt" constr(v1) constr(vo2) "as" simple_intropattern(v2) :=
  destruct vo2 as [v2|];
    [case_vars v1 v2 |reduce_vars].

Tactic Notation "case_var_var_opt" constr(v1) constr(vo2) :=
  let v2 := fresh "v" in
  case_var_var_opt v1 vo2 as v2.

(* Case split on an optional var *)

Tactic Notation "case_var_opt" constr(vo)
       "as" simple_intropattern(v) :=
  destruct vo as [v|]; reduce_vars.

Tactic Notation "case_var_opt" constr(vo) :=
  let v := fresh "v" in
  case_var_opt vo as v.

(* Case split on an optional optional var *)

Tactic Notation "case_var_opt_opt" constr(vo) "as" simple_intropattern(v) :=
  destruct vo as [[v|]|]; reduce_vars.

Tactic Notation "case_var_opt_opt" constr(vo) :=
  let v := fresh "v" in
  case_var_opt_opt vo as v.

(* Case split on the equality of the var parameters. *)
Tactic Notation "case_vars_eq" constr(v1) constr(v2)
       "as" simple_intropattern(Heql) simple_intropattern(Hneql) :=
  destruct (var_dec v1 v2) as [Heql|Hneql];
    [replace v2 with v1 by apply Heql;
     autorewrite with red_var_neq in *;
     reduce_vars_beta in Heql
    |reduce_vars_beta in Hneql];
    reduce_vars;
    try rewrite (eta_reduce_var v1);
    try rewrite (eta_reduce_var v2);
    try solve [exfalso; try congruence; try lia].

Tactic Notation "case_vars_eq" constr(v1) constr(v2) :=
  let Heql := fresh "Heql" in
  let Hneql := fresh "Hneql" in
  case_vars_eq v1 v2 as Heql Hneql.

(* Identities *)

Lemma pop_push_identity v :
  pop_var v @ push_var v =v= 1.
Proof.
  intros v'.
  case_vars v v'; easy.
Qed.

Lemma pop_push_identity' {N} v (op : var_op N 0) :
  pop_var v @ (push_var v @ op) =v= op.
Proof.
  rewrite var_op_associative, pop_push_identity,
    var_op_left_identity.
  easy.
Qed.

Lemma push_pop_identity v :
  push_var v @ pop_var v =v= 1.
Proof.
  intros v'.
  case_var_var_opt v v'; easy.
Qed.

Lemma push_pop_identity' {N} v (op : var_op N 1) :
  push_var v @ (pop_var v @ op) =v= op.
Proof.
  rewrite var_op_associative,
    push_pop_identity, var_op_left_identity.
  easy.
Qed.

Lemma swap_swap_identity :
  swap_var @ swap_var =v= 1.
Proof.
  intros v.
  case_var_opt_opt v; easy.
Qed.

Lemma swap_swap_identity' {N} (op : var_op N 2) :
  swap_var @ (swap_var @ op) =v= op.
Proof.
  rewrite var_op_associative,
    swap_swap_identity, var_op_left_identity.
  easy.
Qed.

(* [lift_var_op] distributes over composition and identity *)

Lemma lift_var_op_compose
      {N M O} (op1 : var_op M O) (op2 : var_op N M) :
  lift_var_op (op1 @ op2)
  =v= lift_var_op op1 @ lift_var_op op2.
Proof.
  intros vo.
  case_var_opt vo; easy.
Qed.

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

Lemma lift_var_op_id {N} :
  @lift_var_op N N 1 =v= 1.
Proof.
  intros vo.
  case_var_opt vo; easy.
Qed.

(* Tactic to simplify compositions of var operations *)

Hint Rewrite <- @var_op_associative
  : normalize_var_op_compose.
Hint Rewrite @var_op_left_identity @var_op_right_identity
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
  intros vo.
  case_var_opt_opt vo; easy.
Qed.

Lemma transpose_swap_lifted' op1 {N} (op2 : var_op N 2) :
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
  intros vo3.
  case_var_opt_opt vo3 as v3; try easy;
    case_vars v1 v2; try easy;
      case_vars (unshift_var v2 v1) v3; try easy;
        case_vars v3 v2; easy.
Qed.

Lemma transpose_pops' v1 v2 {N} (op : var_op N 2) :
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
  case_vars v2 v1;
    case_vars (unshift_var v2 v1) v3; try easy;
      case_vars v3 v2; easy.
Qed.

Lemma transpose_pops_reverse_middle v1 v2 v3 :
  shift_var
    (unshift_var (shift_var v2 v3) v1)
    (unshift_var v3 v2)
  = unshift_var
      (shift_var (unshift_var v2 v1) v3)
      (shift_var v1 v2).
Proof.
  case_vars v2 v1;
    case_vars (unshift_var v2 v1) v3; try easy;
      case_vars v3 v2; easy.
Qed.

Lemma transpose_pops_reverse_right v1 v2 v3 :
  unshift_var
    (unshift_var v3 v2)
    (unshift_var (shift_var v2 v3) v1)
  = unshift_var v3
      (unshift_var v2 v1).
Proof.
  case_vars v2 v1;
    case_vars (unshift_var v2 v1) v3; try easy;
      case_vars v3 v2; easy.
Qed.

(* Permutations of "push" operations. As with the pop
   operations, we want to reason about permutations of the
   "push" operations (i.e. weak, close and cycle_in). As with
   pops, we define arbitrary transpositions and then the
   equations on those transpositions required to define the
   full group of permutations. *)

Lemma transpose_pushes v1 v2 :
  lift_var_op (push_var v1) @ push_var v2
  =v= swap_var
      @ lift_var_op (push_var (unshift_var v1 v2))
      @ push_var (shift_var v2 v1).
Proof.
  intros v3.
  case_vars v1 v2;
    case_vars (shift_var v2 v1) v3; try easy;
      case_vars v2 v3; easy.
Qed.

Lemma transpose_pushes' v1 v2 {N} (op : var_op N 0) :
  lift_var_op (push_var v1) @ push_var v2 @ op
  =v= swap_var
      @ lift_var_op (push_var (unshift_var v1 v2))
      @ push_var (shift_var v2 v1)
      @ op.
Proof.
  rewrite var_op_associative.
  rewrite transpose_pushes.
  rewrite <- var_op_associative.
  easy.
Qed.

Lemma transpose_pushes_squared_left v1 v2 :
  unshift_var (unshift_var v1 v2) (shift_var v2 v1) = v1.
Proof.
  apply transpose_pops_squared_right.
Qed.

Lemma transpose_pushes_squared_right v1 v2 :
  shift_var (shift_var v2 v1) (unshift_var v1 v2) = v2.
Proof.
  apply transpose_pops_squared_left.
Qed.

Lemma transpose_pushes_reverse_left v1 v2 v3 :
  unshift_var (unshift_var v1 v2)
    (unshift_var (shift_var v2 v1) v3)
  = unshift_var v1 (unshift_var v2 v3).
Proof.
  apply transpose_pops_reverse_right.
Qed.

Lemma transpose_pushes_reverse_middle v1 v2 v3 :
  unshift_var
    (shift_var (unshift_var v2 v3) v1)
    (shift_var v3 v2)
  = shift_var
      (unshift_var (shift_var v2 v1) v3)
      (unshift_var v1 v2).
Proof.
  rewrite transpose_pops_reverse_middle; easy.
Qed.

Lemma transpose_pushes_reverse_right v1 v2 v3 :
  shift_var
    (shift_var v3 v2)
    (shift_var (unshift_var v2 v3) v1)
  = shift_var v3 (shift_var v2 v1).
Proof.
  apply transpose_pops_reverse_left.
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

Lemma transpose_push_pop v1 v2 :
  v1 <> v2 ->
  push_var v1 @ pop_var v2
  =v= lift_var_op (pop_var (unshift_var v1 v2))
      @ swap_var
      @ lift_var_op (push_var (unshift_var v2 v1)).
Proof.
  intros Hirr vo3.
  case_vars v1 v2;
    case_var_var_opt (unshift_var v2 v1) vo3 as v3; try easy;
      case_vars v2 v3; easy.
Qed.

Lemma transpose_push_pop' v1 v2 {N} (op : var_op N 1) :
  v1 <> v2 ->
  push_var v1 @ pop_var v2 @ op
  =v= lift_var_op (pop_var (unshift_var v1 v2))
      @ swap_var
      @ lift_var_op (push_var (unshift_var v2 v1))
      @ op.
Proof.
  intros Hneq.
  rewrite var_op_associative.
  rewrite transpose_push_pop by easy.
  rewrite <- var_op_associative.
  easy.
Qed.

Lemma transpose_push_push_pop_reverse_left v1 v2 v3 :
  unshift_var
    (unshift_var v1 v2) (unshift_var (shift_var v2 v1) v3)
  = unshift_var v1 (unshift_var v2 v3).
Proof.
  apply transpose_pops_reverse_right.
Qed.

Lemma transpose_push_push_pop_reverse_middle v1 v2 v3 :
  unshift_var
    (unshift_var (unshift_var v2 v3) v1)
    (unshift_var v3 v2)
  = unshift_var
      (unshift_var (shift_var v2 v1) v3)
      (unshift_var v1 v2).
Proof.
  case_vars v1 v2;
    case_vars (shift_var v2 v1) v3; try easy;
      case_vars v2 v3; easy.
Qed.

Lemma transpose_push_push_pop_reverse_right v1 v2 v3 :
  v1 <> unshift_var v2 v3 ->
  shift_var
    (unshift_var v3 v2)
      (unshift_var (unshift_var v2 v3) v1)
  = unshift_var v3 (shift_var v2 v1).
Proof.
  case_vars v1 v2;
    case_vars (shift_var v2 v1) v3; try easy;
      case_vars v2 v3; easy.
Qed.

Lemma transpose_push_pop_pop_reverse_left v1 v2 v3 :
  v3 <> unshift_var v2 v1 ->
  shift_var
    (unshift_var v1 v2) (unshift_var (unshift_var v2 v1) v3)
  = unshift_var v1 (shift_var v2 v3).
Proof.
  apply transpose_push_push_pop_reverse_right.
Qed.

Lemma transpose_push_pop_pop_reverse_middle v1 v2 v3 :
  unshift_var
    (unshift_var (shift_var v2 v3) v1) (unshift_var v3 v2)
  = unshift_var
      (unshift_var (unshift_var v2 v1) v3)
      (unshift_var v1 v2).
Proof.
  rewrite transpose_push_push_pop_reverse_middle; easy.
Qed.

Lemma transpose_push_pop_pop_reverse_right v1 v2 v3 :
  unshift_var
    (unshift_var v3 v2) (unshift_var (shift_var v2 v3) v1)
  = unshift_var v3 (unshift_var v2 v1).
Proof.
  apply transpose_pops_reverse_right.
Qed.

(* In addition to the equalities between permutations, we
   also need to show that permutations commute with reducing
   operations.

   Given a sequence of n operations opₙ:

     ... . opᵢ . opᵢ₊₁ . opᵢ₊₂ . ...

   after performing σᵢ we have:

     ... . op'ᵢ₊₁ . op'ᵢ . opᵢ₊₂ . ...

   If:

     op'ᵢ . opᵢ₊₂ = 1

   Then, we could have instead performed σᵢ₊₁ to get:

     ... . opᵢ . op"ᵢ₊₂ . op"ᵢ₊₁ . ...

   such that:

     opᵢ . op"ᵢ₊₂ = 1

   and:

     op'ᵢ₊₁ = op"ᵢ₊₁

   In other words, if two operations can reduce to the
   identity after a permutation makes them adjacent then it
   doesn't matter which permutation we use to make them
   adjacent.

   Regardless of our choice of operations, this property is
   equivalent to showing that [shift_var] and [unshift_var]
   are inverses (when they are both valid).

   This property seems like it should be in some sense
   complete, but due to the possiblity that transpositions
   might be invalid there are some manipulations of
   permutations and reductions that can not be proved from
   this property alone without ending up with stronger
   pre-conditions than necessary.  *)

Lemma reducible_transposed v1 v2 v3 :
  shift_var v2 v1 = v3 <-> v2 <> v3 /\ unshift_var v2 v3 = v1.
Proof.
  split.
  - intros <-; split.
    + case_vars v2 v1; try congruence; lia.
    + case_vars v2 v1; easy.
  - intros [Hneq <-].
    case_vars v2 v3; easy.
Qed.

(* More convenient forms *)
Lemma reducible_transposed_1 v1 v2 v3 :
  shift_var v2 v1 = v3 -> v2 <> v3.
Proof. rewrite reducible_transposed; easy. Qed.

Lemma reducible_transposed_2 v1 v2 v3 :
  shift_var v2 v1 = v3 ->
  unshift_var v2 v3 = v1.
Proof. rewrite reducible_transposed; easy. Qed.

Lemma reducible_transposed_3 v1 v2 v3 :
  v2 <> v3 ->
  unshift_var v2 v3 = v1 ->
  shift_var v2 v1 = v3.
Proof. rewrite reducible_transposed; easy. Qed.

Lemma irreducible_transposed_1 v1 v2 :
  shift_var v2 v1 <> v2.
Proof. rewrite reducible_transposed; easy. Qed.

Lemma irreducible_transposed_2 v1 v2 v3 :
  unshift_var v2 v3 <> v1 ->
  shift_var v2 v1 <> v3.
Proof. rewrite reducible_transposed; easy. Qed.

Lemma irreducible_transposed_3 v1 v2 v3 :
  v2 <> v3 ->
  shift_var v2 v1 <> v3 ->
  unshift_var v2 v3 <> v1.
Proof.
  rewrite reducible_transposed.
  intros Hneq Hn; contradict Hn; easy.
Qed.

(* Corollary: moving a reducible pair of push and
   pop operations over third operation leaves them
   reducible. *)
Lemma transpose_reducible_push_pop v1 v2 :
  unshift_var v1 v2 = unshift_var (shift_var v2 v1) v2.
Proof.
  symmetry.
  apply reducible_transposed_2.
  apply transpose_pushes_squared_right.
Qed.

(* Corollary: moving an irreducible pair of push and
   pop operations over third operation leaves them
   irreducible. *)
Lemma transpose_irreducible_push_pop v1 v2 v3 :
  v2 <> v3 ->
  shift_var v2 v1 <> v3 ->
  unshift_var v1 v2 <> unshift_var (shift_var v2 v1) v3.
Proof.
  intros Hneq1 Hneq2.
  rewrite transpose_reducible_push_pop.
  apply irreducible_transposed_3.
  - apply irreducible_transposed_1.
  - rewrite reducible_transposed_3 with (v3 := v3)
      by congruence.
    congruence.
Qed.

(* Given an irreducible pair of pop and push operations
   nested within a reducible pair of pop and push
   operations, reversing the nesting and reducing the
   reducible pair leaves an irreducible pair.

   This is not a corollary of the above property. Proving it
   from that property would require the stronger
   pre-condition [v1 = shift_var v2 (unshift_var v3 v4)]. *)
Lemma transpose_irreducible_pop_push_nested v1 v2 v3 v4:
  v2 <> v3 ->
  unshift_var v2 v1 = unshift_var v3 v4 ->
  shift_var v1 v2 <> shift_var v4 v3.
Proof.
  intros Hneq Heq.
  destruct (label_opt_dec (v_label_opt v2) (v_label_opt v3)).
  - case_vars v2 v1; case_vars v3 v4; subst;
      autorewrite with reduce_vars_beta in *;
      try easy; try congruence; lia.
  - apply v_label_opt_neq; reduce_vars_beta; easy.
Qed.

(* [is_shifting] is a partial ordering *)

Definition is_shifting_var_reflexive v :
  is_shifting_var v v = true.
Proof.
  reduce_vars; easy.
Qed.

Definition is_shifting_var_antisymmetric v1 v2 :
  is_shifting_var v1 v2 = true ->
  is_shifting_var v2 v1 = true ->
  v1 = v2.
Proof.
  case_vars v1 v2; easy.
Qed.

Definition is_shifting_var_transitive v1 v2 v3 :
  is_shifting_var v1 v2 = true ->
  is_shifting_var v2 v3 = true ->
  is_shifting_var v1 v3 = true.
Proof.
  case_vars v1 v2; try easy.
  case_vars v2 v3; easy.
Qed.

(* [is_shifting_var] is total on indistinct vars. *)

Definition is_shifting_var_total_indistinct v1 v2 :
  v_label_opt v1 = v_label_opt v2 ->
  is_shifting_var v1 v2 = false ->
  is_shifting_var v2 v1 = true.
Proof. case_vars v1 v2; easy. Qed.

(* [is_shifting_var] determines the behaviour of [shift_var]. *)

Lemma is_shifting_true_shift v1 v2 :
  is_shifting_var v1 v2 = true ->
  shift_var v1 v2 = succ_var v2.
Proof.
  case_vars v1 v2; easy.
Qed.

Lemma is_shifting_false_shift v1 v2 :
  is_shifting_var v1 v2 = false ->
  shift_var v1 v2 = v2.
Proof.
  case_vars v1 v2; easy.
Qed.

(* A variable shifts its successor *)
Lemma is_shifting_succ_var v :
  is_shifting_var v (succ_var v) = true.
Proof. reduce_vars; easy. Qed.

(* [is_shifting_var] is not affected by transposing
   the variables over an operation *)

(* If [is_shifting_var] holds for two operations after a
   permutation makes them adjacent then it doesn't matter
   which permutation we use to make them adjacent. *)
Lemma transposed_is_shifting_var v1 v2 v3 :
  is_shifting_var (unshift_var v3 v1) v2
  = is_shifting_var v1 (shift_var v3 v2).
Proof.
  case_vars v1 v3;
    case_vars v2 v3; try easy;
      case_vars v1 (shift_var v3 v2); easy.
Qed.

(* [is_shifting_var] applied to [shift_var] and [unshift_var] *)

Lemma is_shifting_var_shift_var v1 v2 v3 :
  is_shifting_var (shift_var v3 v1) (shift_var v3 v2)
  = is_shifting_var v1 v2.
Proof.
  rewrite <- transposed_is_shifting_var.
  rewrite reducible_transposed_2 with (v1 := v1) by easy.
  easy.
Qed.

Lemma is_shifting_var_unshift_var v1 v2 v3 :
  is_shifting_var v1 v2 = true ->
  is_shifting_var
    (unshift_var v3 v1) (unshift_var v3 v2) = true.
Proof.
  case_vars v1 v2; try easy;
    case_vars v3 v1; try easy;
      case_vars v3 v2; try easy.
Qed.

(* [is_unshifting_var] implies [is_shifting_var] *)

Lemma is_unshifting_var_is_shifting_var v1 v2 :
  is_unshifting_var v1 v2 = true ->
  is_shifting_var v1 v2 = true.
Proof.
  unfold is_shifting_var, is_unshifting_var.
  rewrite! Bool.andb_true_iff.
  intros [Heq Hlt]; split; try easy.
  apply leb_complete in Hlt.
  apply leb_correct; lia.
Qed.

(* [is_unshifting] is a strict partial ordering *)

Definition is_unshifting_var_asymmetric v1 v2 :
  is_unshifting_var v1 v2 = true ->
  is_unshifting_var v2 v1 = false.
Proof.
  case_vars v1 v2; easy.
Qed.

Lemma is_unshifting_shifting_var_transitive v1 v2 v3 :
  is_unshifting_var v1 v2 = true ->
  is_shifting_var v2 v3 = true ->
  is_unshifting_var v1 v3 = true.
Proof.
  case_vars v1 v2; try easy;
    case_vars v2 v3; easy.
Qed.

Definition is_unshifting_var_transitive v1 v2 v3 :
  is_unshifting_var v1 v2 = true ->
  is_unshifting_var v2 v3 = true ->
  is_unshifting_var v1 v3 = true.
Proof.
  intros.
  apply is_unshifting_shifting_var_transitive with v2;
    try easy.
  apply is_unshifting_var_is_shifting_var; easy.
Qed.

Lemma is_unshifting_false_is_shifting_var_transitive v1 v2 v3 :
  is_unshifting_var v2 v1 = false ->
  is_shifting_var v2 v3 = true ->
  is_unshifting_var v3 v1 = false.
Proof.
  case_vars v1 v3; try easy;
    case_vars v2 v3; easy.
Qed.

Lemma is_unshifting_var_irreflexive v :
  is_unshifting_var v v = false.
Proof.
  destruct is_unshifting_var eqn:Heq1; try easy.
  apply is_unshifting_var_asymmetric in Heq1 as Heq2.
  congruence.
Qed.

(* [is_unshifting_var] is total on indistinct vars. *)

Definition is_unshifting_var_total_indistinct v1 v2 :
  v_label_opt v1 = v_label_opt v2 ->
  is_unshifting_var v1 v2 = false ->
  is_unshifting_var v2 v1 = false ->
  v1 = v2.
Proof. case_vars v1 v2; easy. Qed.

(* [is_unshifting_var] determines the behaviour of [unshift_var]. *)

Lemma is_unshifting_true_shift v1 v2 :
  is_unshifting_var v1 v2 = true ->
  unshift_var v1 v2 = pred_var v2.
Proof.
  case_vars v1 v2; easy.
Qed.

Lemma is_unshifting_false_shift v1 v2 :
  is_unshifting_var v1 v2 = false ->
  unshift_var v1 v2 = v2.
Proof.
  case_vars v1 v2; easy.
Qed.

(* A variable unshifts its successor *)
Lemma is_unshifting_succ_var_true v :
  is_unshifting_var v (succ_var v) = true.
Proof. reduce_vars; easy. Qed.

(* No variable unshifts a zero variable *)
Lemma is_unshifting_zero_var_false v1 v2 :
  v_nat v2 = 0 ->
  is_unshifting_var v1 v2 = false.
Proof. case_vars v1 v2; try easy; lia. Qed.

(* Useful corollary *)
Lemma is_unshifting_succ_var_false v1 v2 :
  is_unshifting_var v1 v2 = false ->
  is_unshifting_var (succ_var v1) v2 = false.
Proof.
  destruct (is_unshifting_var (succ_var v1) v2) eqn:Heq;
    try easy.
  apply is_unshifting_var_transitive
    with (v1 := v1) in Heq; try congruence.
  apply is_unshifting_succ_var_true.
Qed.

(* [is_unshifting_var] applied to [unshift_var] and [shift_var] *)

Lemma is_unshifting_var_unshift_var v1 v2 v3 :
  is_unshifting_var v1 v2 = false ->
  is_unshifting_var
    (unshift_var v3 v1) (unshift_var v3 v2) = false.
Proof.
  case_vars v1 v2; try easy;
    case_vars v1 v3; try easy;
      case_vars v3 v2; easy.
Qed.

Lemma is_unshifting_var_unshift_var_true v1 v2 v3 :
  v1 <> v3 ->
  is_unshifting_var v1 v2 = true ->
  is_unshifting_var
    (unshift_var v3 v1) (unshift_var v3 v2) = true.
Proof.
  case_vars v1 v2; try easy;
    case_vars v1 v3; try easy;
      case_vars v3 v2; easy.
Qed.

Lemma is_unshifting_var_shift_var v1 v2 v3 :
  is_unshifting_var (shift_var v3 v1) (shift_var v3 v2)
  = is_unshifting_var v1 v2.
Proof.
  case_vars v1 v2; try easy;
    case_vars v3 v1; try easy;
      case_vars v3 v2; easy.
Qed.

(* [is_less_equal_var] is a total ordering *)

Definition is_less_equal_var_reflexive v :
  is_less_equal_var v v = true.
Proof.
  reduce_vars; easy.
Qed.

Definition is_less_equal_var_antisymmetric v1 v2 :
  is_less_equal_var v1 v2 = true ->
  is_less_equal_var v2 v1 = true ->
  v1 = v2.
Proof.
  case_vars v1 v2; try easy.
  intros Heq1 Heq2.
  apply is_less_than_label_opt_asymmetric in Heq1.
  congruence.
Qed.

Definition is_less_equal_var_total v1 v2 :
  is_less_equal_var v1 v2 = false ->
  is_less_equal_var v2 v1 = true.
Proof.
  case_vars v1 v2; try easy.
  intros Heq1.
  destruct (is_less_than_label_opt
              (v_label_opt v2) (v_label_opt v1))
    eqn:Heq2; try easy.
  apply is_less_than_label_opt_total in Heq2; easy.
Qed.

Definition is_less_equal_var_transitive v1 v2 v3 :
  is_less_equal_var v1 v2 = true ->
  is_less_equal_var v2 v3 = true ->
  is_less_equal_var v1 v3 = true.
Proof.
  case_vars v1 v2; try easy;
    case_vars v2 v3; try easy; try congruence.
  unfold is_less_equal_var.
  rewrite! Bool.orb_true_iff; left.
  apply is_less_than_label_opt_transitive
    with (v_label_opt v2); easy.
Qed.

(* [is_less_than_var] implies [is_less_equal_var] *)

Lemma is_less_than_var_is_less_equal_var v1 v2 :
  is_less_than_var v1 v2 = true ->
  is_less_equal_var v1 v2 = true.
Proof.
  unfold is_less_than_var, is_less_equal_var.
  rewrite! Bool.orb_true_iff.
  intros [Heq|Hlt]; [left|right]; try easy.
  apply is_unshifting_var_is_shifting_var; easy.
Qed.

(* [is_less_than_var] is a strict total ordering *)

Lemma is_less_than_var_asymmetric v1 v2 :
  is_less_than_var v1 v2 = true ->
  is_less_than_var v2 v1 = false.
Proof.
  case_vars v1 v2; try easy.
  apply is_less_than_label_opt_asymmetric; easy.
Qed.

Lemma is_less_than_var_total v1 v2 :
  is_less_than_var v1 v2 = false ->
  is_less_than_var v2 v1 = false ->
  v1 = v2.
Proof.
  case_vars v1 v2; try easy; intros.
  absurd (v_label_opt v1 = v_label_opt v2); try easy.
  apply is_less_than_label_opt_total; easy.
Qed.

Lemma is_less_than_less_equal_var_transitive v1 v2 v3 :
  is_less_than_var v1 v2 = true ->
  is_less_equal_var v2 v3 = true ->
  is_less_than_var v1 v3 = true.
Proof.
  case_vars v1 v2; try easy;
    case_vars v2 v3; try easy; try congruence.
  unfold is_less_than_var.
  rewrite Bool.orb_true_iff; left.
  apply is_less_than_label_opt_transitive
    with (v_label_opt v2); easy.
Qed.

Lemma is_less_than_var_transitive v1 v2 v3 :
  is_less_than_var v1 v2 = true ->
  is_less_than_var v2 v3 = true ->
  is_less_than_var v1 v3 = true.
Proof.
  intros.
  apply is_less_than_less_equal_var_transitive with v2;
    try easy.
  apply is_less_than_var_is_less_equal_var; easy.
Qed.

Lemma is_less_than_var_irreflexive v :
  is_less_than_var v v = false.
Proof.
  destruct (is_less_than_var v v) eqn:Heq1; try easy.
  apply is_less_than_var_asymmetric in Heq1 as Heq2.
  congruence.
Qed.

(* [is_less_than] implies not [is_unshifting] *)

Lemma is_less_than_not_unshifting v1 v2 :
  is_less_than_var v1 v2 = true ->
  is_unshifting_var v2 v1 = false.
Proof. case_vars v1 v2; easy. Qed.


(* Orderings on shift and unshift *)

Lemma is_less_equal_var_shift_r v1 v2 :
  is_less_equal_var v2 (shift_var v1 v2) = true.
Proof. case_vars v1 v2; easy. Qed.

Lemma is_less_equal_var_shift_l v1 v2 :
  is_less_equal_var v1 (shift_var v1 v2)
  = is_less_equal_var v1 v2.
Proof. case_vars v1 v2; easy. Qed.

Lemma is_less_equal_var_unshift_r v1 v2 :
  is_less_equal_var (unshift_var v1 v2) v2 = true.
Proof. case_vars v1 v2; easy. Qed.

Lemma is_less_equal_var_unshift_l v1 v2 :
  is_less_equal_var v1 (unshift_var v1 v2)
  = is_less_equal_var v1 v2.
Proof. case_vars v1 v2; easy. Qed.

(* Successor applied to shift and unshift *)

Lemma succ_var_shift_var v1 v2 :
  succ_var (shift_var v1 v2)
  = shift_var (succ_var v1) (succ_var v2).
Proof. case_vars v1 v2; easy. Qed.

Lemma succ_var_unshift_var v1 v2 :
  succ_var (unshift_var v1 v2)
  = unshift_var (succ_var v1) (succ_var v2).
Proof. case_vars v1 v2; easy. Qed.

Lemma succ_var_shift_var_neq v1 v2 :
  v1 <> succ_var v2 ->
  succ_var (shift_var v1 v2)
  = shift_var v1 (succ_var v2).
Proof.
  case_vars v1 v2; try easy.
  case_vars v1 (succ_var v2); congruence.
Qed.

Lemma succ_var_unshift_var_neq v1 v2 :
  v1 <> v2 ->
  succ_var (unshift_var v1 v2)
  = unshift_var v1 (succ_var v2).
Proof. case_vars v1 v2; easy. Qed.
