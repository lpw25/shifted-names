Require Import String PeanoNat Compare_dec
        Psatz Setoid Morphisms.
Require Import Var.

(* Reasoning about shifts and unshifts of names *)

Lemma reduce_shift_name_distinct n1 n2 :
  n_string n1 <> n_string n2 ->
  shift_name n1 n2 = n2.
Proof.
  intros; unfold shift_name.
  destruct (string_dec (n_string n1) (n_string n2)); subst;
    try contradiction; easy.
Qed.

Lemma reduce_shift_name_ge n1 n2 :
  n_string n1 = n_string n2 ->
  n_index n1 <= n_index n2 ->
  shift_name n1 n2 = n_S n2.
Proof.
  intros; unfold shift_name.
  destruct (string_dec (n_string n1) (n_string n2));
    try contradiction.
  destruct (le_gt_dec (n_index n1) (n_index n2));
    try easy; lia.
Qed.

Lemma reduce_shift_name_lt n1 n2 :
  n_string n1 = n_string n2 ->
  S (n_index n2) <= n_index n1 ->
  shift_name n1 n2 = n2.
Proof.
  intros; unfold shift_name.
  destruct (string_dec (n_string n1) (n_string n2));
    try contradiction.
  destruct (le_gt_dec (n_index n1) (n_index n2));
    try easy; lia.
Qed.

Lemma reduce_unshift_name_distinct n1 n2 :
  n_string n1 <> n_string n2 ->
  unshift_name n1 n2 = n2.
Proof.
  intros; unfold unshift_name.
  destruct (string_dec (n_string n1) (n_string n2)); subst;
    try contradiction; easy.
Qed.

Lemma reduce_unshift_name_gt n1 n2 :
  n_string n1 = n_string n2 ->
  S (n_index n1) <= n_index n2 ->
  unshift_name n1 n2 = mkname (n_string n2) (pred (n_index n2)).
Proof.
  intros; unfold unshift_name.
  destruct (string_dec (n_string n1) (n_string n2));
    try contradiction.
  destruct (le_gt_dec (n_index n2) (n_index n1));
    try easy; lia.
Qed.

Lemma reduce_unshift_name_le n1 n2 :
  n_string n1 = n_string n2 ->
  n_index n2 <= n_index n1 ->
  unshift_name n1 n2 = n2.
Proof.
  intros; unfold unshift_name.
  destruct (string_dec (n_string n1) (n_string n2));
    try contradiction.
  destruct (le_gt_dec (n_index n2) (n_index n1));
    try easy; lia.
Qed.

Lemma reduce_name_eqb_distinct n1 n2 :
  n_string n1 <> n_string n2 ->
  name_eqb n1 n2 = false.
Proof.
  intros; unfold name_eqb.
  destruct (name_dec n1 n2); try easy.
  destruct n1, n2; cbn in *; subst.
  congruence.
Qed.

Lemma reduce_name_eqb_eq n1 n2 :
  n_string n1 = n_string n2 ->
  n_index n1 = n_index n2 ->
  name_eqb n1 n2 = true.
Proof.
  intros; unfold name_eqb.
  destruct (name_dec n1 n2); try easy.
  destruct n1, n2; cbn in *; subst.
  contradiction.
Qed.

Lemma reduce_name_eqb_neq n1 n2 :
  n_index n1 <> n_index n2 ->
  name_eqb n1 n2 = false.
Proof.
  intros; unfold name_eqb.
  destruct (name_dec n1 n2); try easy.
  destruct n1, n2; cbn in *; subst.
  congruence.
Qed.

Lemma reduce_close_var_distinct n1 n2 :
  n_string n1 <> n_string n2 ->
  close_var n1 (free n2) = free n2.
Proof.
  intros; unfold close_var.
  rewrite reduce_name_eqb_distinct by easy.
  rewrite reduce_unshift_name_distinct by easy.
  easy.
Qed.

Lemma reduce_close_var_lt n1 n2 :
  n_string n1 = n_string n2 ->
  n_index n2 < n_index n1 ->
  close_var n1 (free n2) = free n2.
Proof.
  intros; unfold close_var.
  rewrite reduce_name_eqb_neq by lia.
  rewrite reduce_unshift_name_le by (try congruence; lia).
  easy.
Qed.

Lemma reduce_close_var_eq n1 n2 :
  n_string n1 = n_string n2 ->
  n_index n1 = n_index n2 ->
  close_var n1 (free n2) = bound 0.
Proof.
  intros; unfold close_var.
  rewrite reduce_name_eqb_eq by congruence.
  easy.
Qed.

Lemma reduce_close_var_gt n1 n2 :
  n_string n1 = n_string n2 ->
  n_index n1 < n_index n2 ->
  close_var n1 (free n2)
  = free (mkname (n_string n2) (pred (n_index n2))).
Proof.
  intros; unfold close_var.
  rewrite reduce_name_eqb_neq by lia.
  rewrite reduce_unshift_name_gt by (try congruence; lia).
  easy.
Qed.

Hint Rewrite reduce_shift_name_distinct
     reduce_unshift_name_distinct
     reduce_name_eqb_distinct
     @reduce_close_var_distinct
     using (cbn; congruence) : reduce_names.

Hint Rewrite reduce_shift_name_ge reduce_shift_name_lt
     reduce_unshift_name_le reduce_unshift_name_gt
     reduce_name_eqb_eq reduce_name_eqb_neq
     @reduce_close_var_lt @reduce_close_var_eq
     @reduce_close_var_gt
     using (cbn; try congruence; lia) : reduce_names.

Ltac reduce_names :=
  try repeat
      (autorewrite with reduce_names; cbn in *);
  try repeat
    ((rewrite_strat (bottomup (hints reduce_names))); cbn in *).

Lemma reduce_non_zero_name {i} n :
  i < n_index n ->
  mkname (n_string n) (S (pred (n_index n))) = n.
Proof.
  intros; destruct n as [s i2], i2; cbn in *; easy.
Qed.

(* Useful lemma *)
Lemma red_name_neq n1 n2 :
  n_string n1 = n_string n2 ->
  n1 <> n2 <-> n_index n1 <> n_index n2.
Proof.
  intro Heq1; split.
  - intros Hneq Heq2; apply Hneq.
    eta_expand_name n1.
    rewrite Heq1, Heq2; easy.
  - intros Hneq Heq2; apply Hneq.
    rewrite Heq2; easy.
Qed.

Hint Rewrite red_name_neq using (cbn; congruence) : red_name_neq.

(* Case split on the order of the name parameters. *)
Ltac case_names n1 n2 :=
  destruct (string_dec (n_string n1) (n_string n2));
    [replace (n_string n2) with (n_string n1) by easy;
     autorewrite with red_name_neq in *;
     destruct (Compare_dec.lt_eq_lt_dec (n_index n1) (n_index n2))
        as [[|]|];
     [replace n2
        with (mkname (n_string n2) (S (pred (n_index n2))))
       by (apply (@reduce_non_zero_name (n_index n1)); easy);
      reduce_names;
      replace (mkname (n_string n2) (S (pred (n_index n2))))
        with n2
       by (symmetry;
           apply (@reduce_non_zero_name (n_index n1)); easy)
     |replace n2 with n1
        by (change n1 with (mkname (n_string n1) (n_index n1));
            change n2 with (mkname (n_string n2) (n_index n2));
            congruence);
      reduce_names
     |replace n1
        with (mkname (n_string n1) (S (pred (n_index n1))))
       by (apply (@reduce_non_zero_name (n_index n2)); easy);
      reduce_names;
      replace (mkname (n_string n1) (S (pred (n_index n1))))
        with n1
       by (symmetry;
           apply (@reduce_non_zero_name (n_index n2)); easy)]
    |reduce_names];
    change (mkname (n_string n1) (n_index n1)) with n1;
    change (mkname (n_string n2) (n_index n2)) with n2;
    try contradiction; try lia.

Tactic Notation "case_name" constr(n)
       "as" simple_intropattern(ns) simple_intropattern(ni) :=
  let n' := fresh "n" in
  let Heqn := fresh "Heqn" in
  remember n as n' eqn:Heqn;
  symmetry in Heqn;
  destruct n' as [ns [|ni]]; cbn in *;
    reduce_names; try lia.

Tactic Notation "case_name" constr(n) :=
  let ns := fresh "ns" in
  let ni := fresh "ni" in
  case_name n as ns ni.

(* Reasoning about shifts and unshifts of levels *)

Lemma reduce_shift_level_ge l1 l2 :
  l1 <= l2 ->
  shift_level l1 l2 = S l2.
Proof.
  intros; unfold shift_level.
  destruct (le_gt_dec l1 l2); try easy; lia.
Qed.

Lemma reduce_shift_level_lt l1 l2 :
  S l2 <= l1 ->
  shift_level l1 l2 = l2.
Proof.
  intros; unfold shift_level.
  destruct (le_gt_dec l1 l2); try easy; lia.
Qed.

Lemma reduce_unshift_level_gt l1 l2 :
  S l1 <= l2 ->
  unshift_level l1 l2 = pred l2.
Proof.
  intros; unfold unshift_level.
  destruct (le_gt_dec l2 l1); try easy; lia.
Qed.

Lemma reduce_unshift_level_le l1 l2 :
  l2 <= l1 ->
  unshift_level l1 l2 = l2.
Proof.
  intros; unfold unshift_level.
  destruct (le_gt_dec l2 l1); try easy; lia.
Qed.

Lemma reduce_level_eqb_eq l1 l2 :
  l1 = l2 ->
  level_eqb l1 l2 = true.
Proof.
  intros; unfold level_eqb, level_dec.
  destruct (Nat.eq_dec l1 l2); easy.
Qed.

Lemma reduce_level_eqb_neq l1 l2 :
  l1 <> l2 ->
  level_eqb l1 l2 = false.
Proof.
  intros; unfold level_eqb, level_dec.
  destruct (Nat.eq_dec l1 l2); easy.
Qed.

Lemma reduce_cycle_in_level_lt l1 l2 :
  l2 < l1 ->
  cycle_in_level l1 l2 = S l2.
Proof.
  intros; unfold cycle_in_level.
  rewrite reduce_level_eqb_neq by lia.
  rewrite reduce_unshift_level_le by lia.
   easy.
Qed.

Lemma reduce_cycle_in_level_eq l1 l2 :
  l1 = l2 ->
  cycle_in_level l1 l2 = 0.
Proof.
  intros; unfold cycle_in_level.
  rewrite reduce_level_eqb_eq by lia.
  easy.
Qed.

Lemma reduce_cycle_in_level_gt l1 l2 :
  l1 < l2 ->
  cycle_in_level l1 l2 = l2.
Proof.
  intros; unfold cycle_in_level.
  rewrite reduce_level_eqb_neq by lia.
  rewrite reduce_unshift_level_gt by lia.
  easy.
Qed.

Hint Rewrite reduce_shift_level_ge reduce_shift_level_lt
     reduce_unshift_level_le reduce_unshift_level_gt
     reduce_level_eqb_eq reduce_level_eqb_neq
     @reduce_cycle_in_level_lt @reduce_cycle_in_level_eq
     @reduce_cycle_in_level_gt
     using (cbn; lia) : reduce_levels.

Ltac reduce_levels :=
  try repeat
      (autorewrite with reduce_levels; cbn in *);
  try repeat
    ((rewrite_strat (bottomup (hints reduce_levels))); cbn in *).

(* Case split on the order of the level parameters. *)
Ltac case_levels l1 l2 :=
  let Heq := fresh "Heq" in
  destruct (Compare_dec.lt_eq_lt_dec l1 l2)
    as [[|Heq]|];
  [|replace l2 with l1 by easy|];
  reduce_levels; try lia.

(* Case split on a level *)
Tactic Notation "case_level" constr(l)
       "as" simple_intropattern(l') :=
  destruct l as [|l']; cbn in *;
    reduce_levels; try lia.

Tactic Notation "case_level" constr(l) :=
  let l' := fresh "l" in
  case_level l as l'.

(* Case split on a variable *)
Tactic Notation "case_var" constr(v)
       "as" simple_intropattern(n) simple_intropattern(l) :=
  destruct v as [n|l]; cbn in *.

Tactic Notation "case_var" constr(v) :=
  let n := fresh "n" in
  let l := fresh "l" in
  case_var v as n l.

Tactic Notation "case_var" :=
  match goal with
  | |- context
         [match ?v with
          | free _ => _
          | bound _ => _
          end] => case_var v
  end.

Tactic Notation "case_var"
       "as" simple_intropattern(n) simple_intropattern(l) :=
  match goal with
  | |- context
         [match ?v with
          | free _ => _
          | bound _ => _
          end] => case_var v as n l
  end.

(* Identities *)

Lemma pop_zero_identity :
  pop_var zero_var =v= 1.
Proof.
  intros v.
  case_var v as ? l; try easy.
  case_level l; easy.
Qed.

Lemma push_zero_identity :
  push_var zero_var_opt =v= 1.
Proof.
  intros v.
  case_var v as ? l; try easy.
  case_level l; easy.
Qed.

Lemma pop_push_identity v :
  pop_var v @ push_var (Some v) =v= 1.
Proof.
  intros v'.
  case_var v; case_var v' as n' l'; try easy.
  - case_names n n'; easy.
  - case_levels l l'; try easy.
    case_level l'; easy.
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
  case_var v; case_var v' as n' l'; try easy.
  - case_names n n'; easy.
  - case_level l'; try easy.
    case_names n n; easy.
  - case_level l' as l''; try easy.
    case_levels l l''; easy.
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
  case_var v as ? l; try easy.
  unfold swap_level.
  case_level l as l'; try easy.
  case_level l'; easy.
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
  case_var v as n l.
  - case_var (op2 (free n)); easy.
  - case_level l as l'; try easy.
    case_var (op2 (bound l')); easy.
Qed.

Lemma lift_var_op_id :
  lift_var_op 1 =v= 1.
Proof.
  intros v.
  case_var v as n l; try easy.
  case_level l; easy.
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
  case_var v as n l.
  - case_var (op (free n)); easy.
  - case_level l as l'; try easy.
    case_level l'; try easy.
    case_var (op (bound l)); easy.
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

Lemma transpose_pops v1 v2:
  pop_var v1 @ lift_var_op (pop_var v2)
  =v= pop_var (shift_var v1 v2)
      @ lift_var_op (pop_var (unshift_var v2 v1))
      @ swap_var.
Proof.
  intros v.
  destruct v1 as [n1|l1], v2 as [n2|l2];
    simplify_var_ops; cbn.
  - case_var v as n3 l.
    + case_names n1 n2.
      * case_names n1 n3; try easy.
        case_names n2 n3; try congruence;
          case_name n2; case_name n3; try easy.
      * case_names n1 n3; easy.
      * case_names n1 (n_S n3); try easy.
        case_names n2 n3; easy.
      * case_names n2 n3; try easy.
        case_names n1 n3; easy.
    + case_level l as l; try easy.
      * case_names n1 n2; easy.
      * case_level l; easy.
  - case_var v; try easy.
    case_level l as l; try easy.
    case_level l as l; easy.
  - case_var v; try easy.
    case_level l as l; try easy.
    case_level l as l; easy.
  - case_var v as n3 l3; try easy.
    unfold cycle_out_var, cycle_out_level.
    case_level l3 as l3; try easy.
    + case_levels l1 l2; try easy.
      case_level l1; easy.
    + case_level l3 as l3; try easy.
      case_levels l1 l2;
        case_levels l2 l3; try easy.
      * case_levels l1 l3; easy.
      * case_levels (S l3) l1; try easy.
      * case_levels (S l2) l1; easy.
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
Proof.
  destruct v1 as [n1|l1], v2 as [n2|l2]; cbn; try easy.
  - case_names n1 n2; easy.
  - case_levels l1 l2; try easy.
    case_level l1; easy.
Qed.

Lemma transpose_pops_squared_right v1 v2 :
  unshift_var (unshift_var v2 v1) (shift_var v1 v2) = v2.
Proof.
  destruct v1 as [n1|l1], v2 as [n2|l2]; cbn; try easy.
  - case_names n1 n2; easy.
  - case_levels l2 l1; easy.
Qed.

Lemma transpose_pops_reverse_left v1 v2 v3 :
  shift_var
    (shift_var v1 v2)
    (shift_var (unshift_var v2 v1) v3)
  = shift_var v1 (shift_var v2 v3).
Proof.
  destruct v1 as [n1|l1], v2 as [n2|l2], v3 as [n3|l3];
    cbn in *; try easy.
  - case_names n2 n1.
    + case_names n1 (n_S n3); try easy.
      case_names n2 n3; easy.
    + case_names n2 n3; easy.
    + case_names n1 n3; try easy.
      case_names n2 n3; try congruence.
      * case_name n2; try easy.
      * case_name n3; try easy.
    + case_names n2 n3; try easy.
      case_names n1 n3; easy.
  - case_levels l1 l2.
    + case_levels l1 (S l3); try easy.
      case_levels l2 l3; easy.
    + case_levels l2 l3; easy.
    + case_levels l1 (S l3); try easy.
      case_levels l2 l3; easy.
Qed.

Lemma transpose_pops_reverse_middle v1 v2 v3 :
  shift_var
    (unshift_var (shift_var v2 v3) v1)
    (unshift_var v3 v2)
  = unshift_var
      (shift_var (unshift_var v2 v1) v3)
      (shift_var v1 v2).
Proof.
  destruct v1 as [n1|l1], v2 as [n2|l2], v3 as [n3|l3];
    cbn in *; try easy.
  - case_names n2 n3.
    + case_names n1 n2; try easy.
      case_names n1 (n_S n3); try easy; congruence.
    + case_names n1 (n_S n2); easy.
    + case_names n1 n2; try easy.
      * case_names n1 n3; try congruence; easy.
      * case_name n1; easy.
    + case_names n1 n2; try easy.
      case_names n1 n3; easy.
  - case_levels l1 l2.
    + case_levels l2 l3;
        case_levels l3 l1; try easy;
          case_level l2; easy.
    + case_levels l1 l3; try easy.
      case_level l1; easy.
    + case_levels l2 l3; try easy;
        case_levels (S l3) l1; easy.
Qed.

Lemma transpose_pops_reverse_right v1 v2 v3 :
  unshift_var
    (unshift_var v3 v2)
    (unshift_var (shift_var v2 v3) v1)
  = unshift_var v3
      (unshift_var v2 v1).
Proof.
  destruct v1 as [n1|l1], v2 as [n2|l2], v3 as [n3|l3];
    cbn in *; try easy.
  - case_names n3 n2;
      case_names n2 n1; try easy.
    + case_names n3 n1; try easy.
      congruence.
    + case_names (n_S n3) n1; easy.
    + case_names (n_S n3) n1; easy.
    + case_names n3 n1; easy.
  - case_levels l3 l2;
      case_levels l2 l1; try easy.
    + case_levels l3 l1; easy.
    + case_levels (S l3) l1; easy.
    + case_levels (S l3) l1; easy.
Qed.

(* Permutations of "push" operations. As with the pop
   operations, we want to reason about permutations of the
   "push" operations (i.e. weak, close and cycle_in). As with
   pops, we define arbitrary transpositions and then the
   equations on those transpositions required to define the
   full group of permutations. *)

Lemma transpose_pushes vo1 vo2 :
  lift_var_op (push_var vo1)
  @ push_var vo2
  =v= swap_var
      @ lift_var_op (push_var (unshift_var_opt vo1 vo2))
      @ push_var (shift_var_opt vo2 vo1).
Proof.
  intros v.
  destruct vo1 as [[n1|l1]|], vo2 as [[n2|l2]|];
    simplify_var_ops; cbn;
    case_var v as n3 l3; try easy.
  - case_names n1 n2.
    + case_names n2 n3; try easy.
      case_names n1 n3; try easy.
      congruence.
    + case_names n1 n3; try easy.
      case_names (n_S n1) n3; easy.
    + case_names n2 n3; try easy.
      case_names (n_S n1) n3; easy.
    + case_names n2 n3; try easy.
      case_names n1 n3; easy.
  - case_names n1 n3; easy.
  - case_levels l2 l3; try easy.
    case_level l3; easy.
  - case_names n1 n3; easy.
  - case_names n2 n3; easy.
  - case_level (cycle_in_level l1 l3); easy.
  - case_levels l2 l1.
    + case_levels l2 l3; try easy.
      case_level l3 as l3'.
      case_levels l1 l3'; try easy.
      case_level l3'; easy.
    + case_levels l2 l3; try easy.
      case_level l3 as l3'.
      case_levels l2 l3'; try easy.
      case_level l3'; easy.
    + case_levels l2 l3; try easy.
      * case_level l3 as l3'.
        case_level l3'; easy.
      * case_level l2; easy.
      * case_levels l1 l3; try easy.
        case_level l3; easy.
  - case_levels l1 l3; try easy.
    case_level l3; easy.
  - case_names n2 n3; easy.
  - case_levels l2 l3; try easy.
    case_level l3; easy.
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
  intros Hirr v.
  destruct vo1 as [[n1|l1]|], v2 as [n2|l2];
    simplify_var_ops; cbn; case_var v as n l; try easy.
  - assert (n1 <> n2) by congruence.
    case_names n2 n1.
    + case_names n2 n; try easy.
      * case_names n1 (n_S n); try congruence; try easy.
        case_name n; easy.
      * case_names n1 (n_S n2); try congruence; easy.
    + case_names n2 n; try easy.
      * case_name n2; easy.
      * case_names n1 n; easy.
    + case_names n2 n; try easy.
      case_names n1 n; easy.
  - assert (n1 <> n2) by congruence.
    case_level l; try easy.
    case_names n1 n2; try easy.
  - case_names n1 n; easy.
  - case_level l; easy.
  - case_level l as l; try easy.
    case_levels l1 l; try easy.
    case_level l; easy.
  - assert (l1 <> l2) by congruence.
    unfold cycle_out_var, cycle_out_level.
    case_level l as l.
    + case_levels l1 l2; try easy.
      case_level l2; easy.
    + case_levels l1 l2.
      * { case_levels l2 l.
          - case_level l; easy.
          - case_level l2; easy.
          - case_levels l1 l; try easy.
            case_level l; easy. }
      * { case_levels l1 (S l); try easy.
          - case_level l; easy.
          - case_levels l2 l; easy. }
  - case_level l; easy.
  - unfold cycle_out_var, cycle_out_level.
    case_level l; easy.
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
  destruct v1 as [n1|l1], v2 as [n2|l2], v3 as [n3|l3];
    cbn; try easy.
  - case_names n3 n2.
    + case_names n2 n1; try easy.
      case_names n1 n3; easy.
    + case_names n3 n1; easy.
    + case_names n2 n1; try easy;
        case_names n3 (n_S n1); try easy; congruence.
    + case_names n2 n1; try easy.
      case_names n3 n1; easy.
  - case_levels l1 l2.
    + case_levels l2 l3; try easy.
      case_levels l3 l1; easy.
    + case_levels (S l1) l3; easy.
    + case_levels l2 l3; try easy.
      case_levels (S l1) l3; easy.
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
  destruct v1 as [n1|l1], v2 as [n2|l2], v3 as [n3|l3];
    cbn; try easy; intros.
  - assert (n1 <> unshift_name n2 n3) as Hneq by congruence.
    generalize Hneq.
    case_names n2 n3; intros.
    + case_names (n_S n1) n3; try easy.
      case_names n1 n2; try congruence; try easy.
      case_name n1; easy.
    + case_names n1 n3; try easy.
    + case_names n1 n3; try easy.
      case_names n1 n2; try easy.
      case_name n1; easy.
    + case_names n1 n3; try easy.
      case_names n1 n2; easy.
  - assert (l1 <> unshift_level l2 l3) as Hneq by congruence.
    generalize Hneq.
    case_levels l2 l3; intros.
    + case_levels (S l1) l3; try easy.
      case_levels l1 l2; try easy.
      case_level l1; easy.
    + case_levels l1 l3; try easy.
      case_level l1; easy.
    + case_levels l1 l3; try easy.
      case_levels l1 l2; try easy;
        case_level l1; easy.
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
Proof.
  case_var v1 as n1 l1; case_var v2 as n2 l2; cbn; try easy.
  - case_names n1 n2; easy.
  - case_levels l1 l2; easy.
Qed.

Lemma transpose_reducing_pop_push_aux v1 v2 :
  v1 <> v2 ->
  shift_var v1 (unshift_var v1 v2) = v2.
Proof.
  intros.
  case_var v1 as n1 l1; case_var v2 as n2 l2; cbn; try easy.
  - assert (n1 <> n2) by congruence.
    case_names n1 n2; easy.
  - assert (l1 <> l2) by congruence.
    case_levels l1 l2; try easy.
    case_level l2; easy.
Qed.

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

(* Transpositions of [pop_var zero_var] and [push_var
   zero_var_opt].

   Some transpositions on pop zero and push zero are the
   identity, which we show below so that we can avoid doing
   them.

   This also simplifies some of the equations on
   transpotions, and it is useful to have the specialised
   forms of these equations.*)

(* Transposing pop zero backwards over a pop *)
Lemma transpose_pop_pop_zero_left v :
  unshift_var v zero_var = zero_var.
Proof. case_var v; easy. Qed.

(* Transposing pop zero backwards over a push *)
Lemma transpose_push_pop_zero_left vo :
  unshift_var_opt_var vo zero_var = zero_var.
Proof.
  destruct vo as [v|]; cbn; try easy.
  apply transpose_pop_pop_zero_left.
Qed.

(* Transposing push zero backwards over a pop *)
Lemma transpose_pop_push_zero_left v :
  unshift_var_var_opt v zero_var_opt = zero_var_opt.
Proof. cbn; rewrite transpose_pop_pop_zero_left; easy. Qed.

(* Transposing push zero backwards over a push *)
Lemma transpose_push_push_zero_left vo :
  unshift_var_opt vo zero_var_opt = zero_var_opt.
Proof.
  destruct vo as [v|]; cbn; try easy.
  rewrite transpose_pop_pop_zero_left; easy.
Qed.

Lemma transpose_push_push_pop_zero_reverse_middle vo1 vo2 :
  unshift_var_opt (unshift_var_var_opt zero_var vo1)
    (unshift_var_var_opt zero_var vo2)
  = unshift_var_var_opt zero_var (unshift_var_opt vo1 vo2).
Proof.
  pose
    (transpose_push_push_pop_reverse_middle vo1 vo2 zero_var)
    as Hrw.
  rewrite transpose_push_pop_zero_left in Hrw.
  rewrite transpose_push_pop_zero_left in Hrw.
  apply Hrw.
Qed.

Lemma transpose_push_push_pop_zero_reverse_right vo1 vo2 :
  vo1 <> zero_var_opt ->
  shift_var_opt
    (unshift_var_var_opt zero_var vo2)
      (unshift_var_var_opt zero_var vo1)
  = unshift_var_var_opt zero_var (shift_var_opt vo2 vo1).
Proof.
  intros.
  rewrite <- transpose_push_push_pop_reverse_right;
    rewrite transpose_push_pop_zero_left; easy.
Qed.
