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

Lemma cycle_in_zero_identity :
  cycle_in_var 0 =v= 1.
Proof.
  intros v.
  case_var v as ? l2; try easy.
  case_level l2; easy.
Qed.

Lemma cycle_out_zero_identity :
  cycle_out_var 0 =v= 1.
Proof.
  intros v.
  case_var v as ? l2; try easy.
  unfold cycle_out_level.
  case_level l2; easy.
Qed.

Lemma open_close_identity n :
  open_var n @ close_var n =v= 1.
Proof.
  intros v; unfold open_var, close_var.
  case_var v as n2 ?; try easy.
  case_names n n2; easy.
Qed.

Lemma open_close_identity' n op :
  open_var n @ (close_var n @ op) =v= op.
Proof.
  rewrite var_op_associative, open_close_identity,
    var_op_left_identity.
  easy.
Qed.

Lemma close_open_identity n :
  close_var n @ open_var n =v= 1.
Proof.
  intros v; unfold open_var, close_var.
  case_var v as n2 l2.
  - case_names n n2; easy.
  - case_level l2; try easy.
    case_names n n; easy.
Qed.

Lemma close_open_identity' n op :
  close_var n @ (open_var n @ op) =v= op.
Proof.
  rewrite var_op_associative,
    close_open_identity, var_op_left_identity.
  easy.
Qed.

Lemma cycle_in_cycle_out_identity l :
  cycle_in_var l @ cycle_out_var l =v= 1.
Proof.
  intros v.
  case_var v as ? l2; try easy.
  unfold cycle_out_level.
  case_level l2 as l2'; try easy.
  case_levels l l2'; easy.
Qed.

Lemma cycle_in_cycle_out_identity' l op :
  cycle_in_var l @ (cycle_out_var l @ op) =v= op.
Proof.
  rewrite var_op_associative, cycle_in_cycle_out_identity,
    var_op_left_identity.
  easy.
Qed.

Lemma cycle_out_cycle_in_identity l :
  cycle_out_var l @ cycle_in_var l =v= 1.
Proof.
  intros v.
  case_var v as ? l2; try easy.
  unfold cycle_in_level, cycle_out_level.
  case_levels l l2; try easy.
  case_level l2; easy.
Qed.

Lemma cycle_out_cycle_in_identity' l op :
  cycle_out_var l @ (cycle_in_var l @ op) =v= op.
Proof.
  rewrite var_op_associative, cycle_out_cycle_in_identity,
    var_op_left_identity.
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

Lemma unshift_level_shift_level_identity l1 l2 :
  unshift_level l1 (shift_level l1 l2) = l2.
Proof. case_levels l1 l2. Qed.

Lemma shift_level_unshift_level_neq_identity l1 l2 :
  l1 <> l2 ->
  shift_level l1 (unshift_level l1 l2) = l2.
Proof. case_levels l1 l2. Qed.

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

(* Transposing push operations

   We wish to reason about transposing "push" operations (i.e. [weak],
   [cycle_in] and [close]).  These operations are not commutative,
   however they can be transposed by applying [shift] and [unshift]
   transformations to them.

   This situation is very close to that studied by the "operational
   transforms" literature in the context of collaborative text
   editors. However, rather than define the "ET" and "IT"
   transformations for our operations as they do, we will use a slightly
   different formulation.
 *)

Lemma transpose_pushes op1 op2 :
  lift_var_op (apply_push_op_var op1)
  @ apply_push_op_var op2
  =v= swap_var
      @ lift_var_op (apply_push_op_var (unshift_push op1 op2))
      @ apply_push_op_var (shift_push op2 op1).
Proof.
  intros v.
  destruct op1 as [|l1|n1], op2 as [|l2|n2];
    simplify_var_ops; cbn;
    case_var v as n3 l3; try easy.
  - case_levels l2 l3; try easy.
    case_level l3; easy.
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
  - case_names n2 n3; easy.
  - case_levels l1 l3; try easy.
    case_level l3; easy.
  - case_names n1 n3; easy.
  - case_names n1 n3; easy.
  - case_levels l2 l3; try easy.
    case_level l3; easy.
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
Qed.

(* Permutations of push operations

   Beyond transposing pairs of push operations, we wish to reason
   about arbitrary permutations of sequences of push operations.

   Given a sequence of n push operations, rewriting with
   [transpose_pushes] essentially gives us transpositions σᵢ
   which swap the ith and (i+1)th operations. The group of
   permutations of n operations can be generated from these
   transpositions and the following equations:

   1) σᵢ ∘ σⱼ = σⱼ ∘ σᵢ where |i - j| > 1

   2) σᵢ ∘ σᵢ = 1

   3) σᵢ ∘ σᵢ₊₁ ∘ σᵢ = σᵢ₊₁ ∘ σᵢ ∘ σᵢ₊₁

   The first equation follows automatically since rewriting
   with [transpose_pushes] only affects the operations that
   are transposed.

   Lemmas [transpose_pushes_squared_left] and
   [transpose_pushes_squared_right] below are equivalent to
   the second equation.

   Lemmas [transpose_pushes_reverse_left],
   [transpose_pushes_reverse_middle] and
   [transpose_pushes_reverse_right] below are equivalent to
   the third equation.
 *)

Lemma transpose_pushes_squared_left op1 op2 :
  unshift_push (unshift_push op1 op2) (shift_push op2 op1) = op1.
Proof.
  destruct op1 as [|l1|n1], op2 as [|l2|n2]; cbn; try easy.
  - case_levels l1 l2; easy.
  - case_names n1 n2; easy.
Qed.

Lemma transpose_pushes_squared_right op1 op2 :
  shift_push (shift_push op2 op1) (unshift_push op1 op2) = op2.
Proof.
  destruct op1 as [|l1|n1], op2 as [|l2|n2]; cbn; try easy.
  - case_levels l1 l2; try easy.
    case_level l2; easy.
  - case_names n1 n2; easy.
Qed.

Lemma transpose_cycle_ins_reverse_left l1 l2 l3 :
  unshift_level (unshift_level l1 l2)
    (unshift_level (shift_level l2 l1) l3)
  = unshift_level l1 (unshift_level l2 l3).
Proof.
  case_levels l1 l2;
    case_levels l2 l3; try easy.
  - case_levels l1 l3; easy.
  - case_levels (S l1) l3; easy.
  - case_levels (S l1) l3; easy.
Qed.

Lemma transpose_closes_reverse_left n1 n2 n3 :
  unshift_name (unshift_name n1 n2)
    (unshift_name (shift_name n2 n1) n3)
  = unshift_name n1 (unshift_name n2 n3).
Proof.
  case_names n1 n2;
    case_names n2 n3; try easy.
  - case_names n1 n3; try easy.
    congruence.
  - case_names (n_S n1) n3; easy.
  - case_names (n_S n1) n3; easy.
  - case_names n1 n3; easy.
Qed.

Lemma transpose_pushes_reverse_left op1 op2 op3 :
  unshift_push (unshift_push op1 op2)
    (unshift_push (shift_push op2 op1) op3)
  = unshift_push op1 (unshift_push op2 op3).
Proof.
  destruct op1 as [|l1|n1], op2 as [|l2|n2], op3 as [|l3|n3];
    cbn in *; try easy.
  - rewrite transpose_cycle_ins_reverse_left; easy.
  - rewrite transpose_closes_reverse_left; easy.
Qed.

Lemma transpose_cycle_ins_reverse_middle l1 l2 l3 :
  unshift_level
    (shift_level (unshift_level l2 l3) l1)
    (shift_level l3 l2)
  = shift_level
      (unshift_level (shift_level l2 l1) l3)
      (unshift_level l1 l2).
Proof.
  case_levels l1 l2.
  - case_levels l2 l3;
      case_levels l3 l1; try easy;
        case_level l2; easy.
  - case_levels (S l1) l3; easy.
  - case_levels l2 l3; try easy.
    case_levels (S l1) l3; easy.
Qed.

Lemma transpose_closes_reverse_middle n1 n2 n3 :
  unshift_name
    (shift_name (unshift_name n2 n3) n1)
    (shift_name n3 n2)
  = shift_name
      (unshift_name (shift_name n2 n1) n3)
      (unshift_name n1 n2).
Proof.
  case_names n1 n2.
  - case_names n2 n3;
      case_names n3 n1; try congruence; try easy;
        case_name n2; easy.
  - case_names (n_S n1) n3; easy.
  - case_names n2 n3; try easy.
    case_names (n_S n1) n3; try congruence; easy.
  - case_names n2 n3; try easy.
    case_names n1 n3; easy.
Qed.

Lemma transpose_pushes_reverse_middle op1 op2 op3 :
  unshift_push
    (shift_push (unshift_push op2 op3) op1)
    (shift_push op3 op2)
  = shift_push
      (unshift_push (shift_push op2 op1) op3)
      (unshift_push op1 op2).
Proof.
  destruct op1 as [|l1|n1], op2 as [|l2|n2], op3 as [|l3|n3];
    cbn in *; try easy.
  - rewrite transpose_cycle_ins_reverse_middle; easy.
  - rewrite transpose_closes_reverse_middle; easy.
Qed.

Lemma transpose_cycle_ins_reverse_right l1 l2 l3 :
  shift_level
    (shift_level l3 l2)
    (shift_level (unshift_level l2 l3) l1)
  = shift_level l3 (shift_level l2 l1).
Proof.
  case_levels l2 l3.
  - case_levels (S l1) l3; try easy.
    case_levels l1 l2; easy.
  - case_levels l1 l2; easy.
  - case_levels l1 l3; try easy.
    case_levels l1 l2; easy.
Qed.

Lemma transpose_closes_reverse_right n1 n2 n3 :
  shift_name
    (shift_name n3 n2)
    (shift_name (unshift_name n2 n3) n1)
  = shift_name n3 (shift_name n2 n1).
Proof.
  case_names n2 n3.
  - case_names (n_S n1) n3; try easy.
    case_names n1 n2; easy.
  - case_names n1 n2; easy.
  - case_names n1 n3; try easy.
    case_names n1 n2; try congruence;
      case_name n1; try easy.
  - case_names n1 n2; try easy.
    case_names n1 n3; easy.
Qed.

Lemma transpose_pushes_reverse_right op1 op2 op3 :
  shift_push
    (shift_push op3 op2)
    (shift_push (unshift_push op2 op3) op1)
  = shift_push op3 (shift_push op2 op1).
Proof.
  destruct op1 as [|l1|n1], op2 as [|l2|n2], op3 as [|l3|n3];
    cbn in *; try easy.
  - rewrite transpose_cycle_ins_reverse_right; easy.
  - rewrite transpose_closes_reverse_right; easy.
Qed.

(* Permutations of "pop" operations. As with the push
   operations, we want to reason about permutations of the
   "pop" operations (i.e. open and cycle_out). As with
   pushes, we define arbitrary transpositions and then the
   equations on those transpositions required to define the
   full group of permutations. *)

Lemma transpose_pops op1 op2:
  apply_pop_op_var op1
  @ lift_var_op (apply_pop_op_var op2)
  =v= apply_pop_op_var (shift_pop op1 op2)
      @ lift_var_op (apply_pop_op_var (unshift_pop op2 op1))
      @ swap_var.
Proof.
  intros v.
  destruct op1 as [l1|n1], op2 as [l2|n2];
    simplify_var_ops; cbn.
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
  - case_var v; try easy.
    case_level l as l; try easy.
    case_level l as l; easy.
  - case_var v; try easy.
    case_level l as l; try easy.
    case_level l as l; easy.
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
Qed.

Lemma transpose_pops_squared_left op1 op2 :
  shift_pop (shift_pop op1 op2) (unshift_pop op2 op1) = op1.
Proof.
  destruct op1 as [l1|n1], op2 as [l2|n2]; cbn; try easy.
  - case_levels l1 l2; try easy.
    case_level l1; easy.
  - case_names n1 n2; easy.
Qed.

Lemma transpose_pops_squared_right op1 op2 :
  unshift_pop (unshift_pop op2 op1) (shift_pop op1 op2) = op2.
Proof.
  destruct op1 as [l1|n1], op2 as [l2|n2]; cbn; try easy.
  - case_levels l2 l1; easy.
  - case_names n1 n2; easy.
Qed.

Lemma transpose_cycle_outs_reverse_left l1 l2 l3 :
  shift_level (shift_level l1 l2)
    (shift_level (unshift_level l2 l1) l3)
  = shift_level l1 (shift_level l2 l3).
Proof.
  apply transpose_cycle_ins_reverse_right.
Qed.

Lemma transpose_opens_reverse_left n1 n2 n3 :
  shift_name (shift_name n1 n2)
    (shift_name (unshift_name n2 n1) n3)
  = shift_name n1 (shift_name n2 n3).
Proof.
  apply transpose_closes_reverse_right.
Qed.

Lemma transpose_pops_reverse_left op1 op2 op3 :
  shift_pop
    (shift_pop op1 op2)
    (shift_pop (unshift_pop op2 op1) op3)
  = shift_pop op1
      (shift_pop op2 op3).
Proof.
  destruct op1 as [l1|n1], op2 as [l2|n2], op3 as [l3|n3];
    cbn in *; try easy.
  - rewrite transpose_cycle_outs_reverse_left; easy.
  - rewrite transpose_opens_reverse_left; easy.
Qed.

Lemma transpose_cycle_outs_reverse_middle l1 l2 l3 :
    shift_level (unshift_level (shift_level l2 l3) l1)
                (unshift_level l3 l2)
    = unshift_level (shift_level (unshift_level l2 l1) l3)
                    (shift_level l1 l2).
Proof.
  symmetry.
  apply transpose_cycle_ins_reverse_middle.
Qed.

Lemma transpose_opens_reverse_middle n1 n2 n3 :
  shift_name (unshift_name (shift_name n2 n3) n1)
             (unshift_name n3 n2)
  = unshift_name (shift_name (unshift_name n2 n1) n3)
                 (shift_name n1 n2).
Proof.
  symmetry.
  apply transpose_closes_reverse_middle.
Qed.

Lemma transpose_pops_reverse_middle op1 op2 op3 :
  shift_pop
    (unshift_pop (shift_pop op2 op3) op1)
    (unshift_pop op3 op2)
  = unshift_pop
      (shift_pop (unshift_pop op2 op1) op3)
      (shift_pop op1 op2).
Proof.
  destruct op1 as [l1|n1], op2 as [l2|n2], op3 as [l3|n3];
    cbn in *; try easy.
  - rewrite transpose_cycle_outs_reverse_middle; easy.
  - rewrite transpose_opens_reverse_middle; easy.
Qed.

Lemma transpose_cycle_outs_reverse_right l1 l2 l3 :
  unshift_level (unshift_level l3 l2)
       (unshift_level (shift_level l2 l3) l1)
  = unshift_level l3 (unshift_level l2 l1).
Proof.
  apply transpose_cycle_ins_reverse_left.
Qed.

Lemma transpose_opens_reverse_right n1 n2 n3 :
  unshift_name (unshift_name n3 n2)
    (unshift_name (shift_name n2 n3) n1)
  = unshift_name n3 (unshift_name n2 n1).
Proof.
  apply transpose_closes_reverse_left.
Qed.

Lemma transpose_pops_reverse_right op1 op2 op3 :
  unshift_pop
    (unshift_pop op3 op2)
    (unshift_pop (shift_pop op2 op3) op1)
  = unshift_pop op3
      (unshift_pop op2 op1).
Proof.
  destruct op1 as [l1|n1], op2 as [l2|n2], op3 as [l3|n3];
    cbn in *; try easy.
  - rewrite transpose_cycle_outs_reverse_right; easy.
  - rewrite transpose_opens_reverse_right; easy.
Qed.

(* Moving pushes in front of pops.

   We also wish to reason about moving pushes in front of
   pops.  This will not work if the pop and the push reduce
   to the identity, so we need [irreducible_push_pop_ops] as
   a precondition on transposition.

   Since we will be ignoring the inverse case of moving pops
   in front of pushes, we will not have the full group of
   permutations, but some of the "reverse" equations are
   still relevant.  *)

Lemma transpose_push_pop op1 op2 :
  irreducible_push_pop op1 op2 ->
  apply_push_op_var op1 @ apply_pop_op_var op2
  =v= lift_var_op (apply_pop_op_var (unshift_push_pop op1 op2))
      @ swap_var
      @ lift_var_op (apply_push_op_var (unshift_pop_push op2 op1)).
Proof.
  intros Hirr v.
  destruct op1 as [|l1|n1], op2 as [l2|n2];
    simplify_var_ops; cbn; case_var v as n l; try easy.
  - case_level l; easy.
  - case_level l; easy.
  - unfold cycle_out_var, cycle_out_level.
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
  - case_level l as l; try easy.
    case_levels l1 l; try easy.
    case_level l; easy.
  - case_names n1 n; easy.
  - unfold cycle_out_var, cycle_out_level.
    case_level l; easy.
  - case_names n2 n1.
    + case_names n2 n; try easy.
      * case_names n1 (n_S n); try congruence; try easy.
        case_name n; easy.
      * case_names n1 (n_S n2); try congruence; easy.
    + case_names n2 n; try easy.
      * case_name n2; easy.
      * case_names n1 n; easy.
    + case_names n2 n; try easy.
      case_names n1 n; easy.
  - case_level l; try easy.
    case_names n1 n2; easy.
Qed.

Lemma transpose_cycle_in_cycle_in_cycle_out_reverse_left l1 l2 l3 :
  unshift_level (unshift_level l1 l2)
    (unshift_level (shift_level l2 l1) l3)
  = unshift_level l1 (unshift_level l2 l3).
Proof.
  apply transpose_cycle_ins_reverse_left.
Qed.

Lemma transpose_close_close_open_reverse_left n1 n2 n3 :
  unshift_name (unshift_name n1 n2)
    (unshift_name (shift_name n2 n1) n3)
  = unshift_name n1 (unshift_name n2 n3).
Proof.
  apply transpose_closes_reverse_left.
Qed.

Lemma transpose_push_push_pop_reverse_left op1 op2 op3 :
  unshift_push_pop
    (unshift_push op1 op2)
    (unshift_push_pop (shift_push op2 op1) op3)
  = unshift_push_pop op1 (unshift_push_pop op2 op3).
Proof.
  destruct op1 as [|l1|n1], op2 as [|l2|n2], op3 as [l3|n3];
    cbn in *; try easy; intros.
  - rewrite transpose_cycle_in_cycle_in_cycle_out_reverse_left;
      easy.
  - rewrite transpose_close_close_open_reverse_left; easy.
Qed.

Lemma transpose_cycle_in_cycle_in_cycle_out_reverse_middle l1 l2 l3 :
  unshift_level
    (unshift_level (unshift_level l2 l3) l1)
    (unshift_level l3 l2) =
  unshift_level
    (unshift_level (shift_level l2 l1) l3)
    (unshift_level l1 l2).
Proof.
  case_levels l1 l2.
  - case_levels l2 l3; try easy.
    case_levels l3 l1; easy.
  - case_levels (S l1) l3; easy.
  - case_levels l2 l3; try easy.
    case_levels (S l1) l3; easy.
Qed.

Lemma transpose_close_close_open_reverse_middle n1 n2 n3 :
  unshift_name (unshift_name (unshift_name n2 n3) n1)
               (unshift_name n3 n2)
  = unshift_name (unshift_name (shift_name n2 n1) n3)
                 (unshift_name n1 n2).
Proof.
  case_names n1 n2.
  - case_names n2 n3; try easy.
    case_names n3 n1; easy.
  - case_names (n_S n1) n3; easy.
  - case_names n2 n3; try easy.
    case_names (n_S n1) n3; easy.
  - case_names n2 n3; try easy.
    case_names n1 n3; easy.
Qed.

Lemma transpose_push_push_pop_reverse_middle op1 op2 op3 :
  unshift_push
    (unshift_pop_push
       (unshift_push_pop op2 op3) op1)
    (unshift_pop_push op3 op2)
  = unshift_pop_push
      (unshift_push_pop (shift_push op2 op1) op3)
      (unshift_push op1 op2).
Proof.
  destruct op1 as [|l1|n1], op2 as [|l2|n2], op3 as [l3|n3];
    cbn in *; try easy; intros.
  - rewrite transpose_cycle_in_cycle_in_cycle_out_reverse_middle;
      easy.
  - rewrite transpose_close_close_open_reverse_middle; easy.
Qed.

Lemma transpose_cycle_in_cycle_in_cycle_out_reverse_right l1 l2 l3 :
  l1 <> unshift_level l2 l3 ->
  shift_level (unshift_level l3 l2)
    (unshift_level (unshift_level l2 l3) l1) =
  unshift_level l3 (shift_level l2 l1).
Proof.
  case_levels l2 l1.
  - case_levels l2 l3.
    case_levels (S l1) l3.
  - case_levels l2 l3.
  - case_levels l2 l3.
    case_levels l1 l3.
Qed.

Lemma transpose_close_close_open_reverse_right n1 n2 n3 :
  n1 <> unshift_name n2 n3 ->
  shift_name (unshift_name n3 n2)
             (unshift_name (unshift_name n2 n3) n1)
  = unshift_name n3 (shift_name n2 n1).
Proof.
  case_names n2 n3.
  - case_names (n_S n1) n3; try easy.
    case_names n1 n2; try congruence; try easy.
    case_name n1; easy.
  - case_names n1 n3; try easy.
  - case_names n1 n3; try easy.
    case_names n1 n2; try easy.
    case_name n1; easy.
  - case_names n1 n3; try easy.
    case_names n1 n2; easy.
Qed.

Lemma transpose_push_push_pop_reverse_right op1 op2 op3 :
  irreducible_push_pop op1 (unshift_push_pop op2 op3) ->
  shift_push
    (unshift_pop_push op3 op2)
      (unshift_pop_push (unshift_push_pop op2 op3) op1)
  = unshift_pop_push op3 (shift_push op2 op1).
Proof.
  destruct op1 as [|l1|n1], op2 as [|l2|n2], op3 as [l3|n3];
    cbn in *; try easy; intros.
  - rewrite transpose_cycle_in_cycle_in_cycle_out_reverse_right;
      easy.
  - rewrite transpose_close_close_open_reverse_right; easy.
Qed.

Lemma transpose_cycle_in_cycle_out_cycle_out_reverse_left l1 l2 l3 :
  unshift_level l2 l1 <> l3 ->
  shift_level (unshift_level l1 l2)
    (unshift_level (unshift_level l2 l1) l3)
  = unshift_level l1 (shift_level l2 l3).
Proof.
  intros.
  apply transpose_cycle_in_cycle_in_cycle_out_reverse_right.
  congruence.
Qed.

Lemma transpose_close_open_open_reverse_left n1 n2 n3 :
  unshift_name n2 n1 <> n3 ->
  shift_name (unshift_name n1 n2)
             (unshift_name (unshift_name n2 n1) n3)
  = unshift_name n1 (shift_name n2 n3).
Proof.
  intros.
  apply transpose_close_close_open_reverse_right.
  congruence.
Qed.

Lemma transpose_push_pop_pop_reverse_left op1 op2 op3 :
  irreducible_push_pop (unshift_pop_push op2 op1) op3 ->
  shift_pop
    (unshift_push_pop op1 op2)
    (unshift_push_pop (unshift_pop_push op2 op1) op3)
  = unshift_push_pop op1 (shift_pop op2 op3).
Proof.
  destruct op1 as [|l1|n1], op2 as [l2|n2], op3 as [l3|n3];
    cbn in *; try easy; intros.
  - rewrite transpose_cycle_in_cycle_out_cycle_out_reverse_left;
      easy.
  - rewrite transpose_close_open_open_reverse_left; easy.
Qed.

Lemma transpose_cycle_in_cycle_out_cycle_out_reverse_middle
      l1 l2 l3 :
  unshift_level
    (unshift_level (shift_level l2 l3) l1)
    (unshift_level l3 l2)
  = unshift_level
      (unshift_level (unshift_level l2 l1) l3)
      (unshift_level l1 l2).
Proof.
  intros; symmetry.
  apply transpose_cycle_in_cycle_in_cycle_out_reverse_middle.
Qed.

Lemma transpose_close_open_open_reverse_middle n1 n2 n3 :
  unshift_name (unshift_name (shift_name n2 n3) n1)
               (unshift_name n3 n2)
  = unshift_name
      (unshift_name (unshift_name n2 n1) n3)
      (unshift_name n1 n2).
Proof.
  symmetry.
  apply transpose_close_close_open_reverse_middle.
Qed.

Lemma transpose_push_pop_pop_reverse_middle op1 op2 op3 :
  unshift_push_pop
    (unshift_pop_push (shift_pop op2 op3) op1)
    (unshift_pop op3 op2)
  = unshift_pop
      (unshift_push_pop (unshift_pop_push op2 op1) op3)
      (unshift_push_pop op1 op2).
Proof.
  destruct op1 as [|l1|n1], op2 as [l2|n2], op3 as [l3|n3];
    cbn in *; try easy; intros.
  - rewrite transpose_cycle_in_cycle_out_cycle_out_reverse_middle;
      easy.
  - rewrite transpose_close_open_open_reverse_middle; easy.
Qed.

Lemma transpose_cycle_in_cycle_out_cycle_out_reverse_right
      l1 l2 l3 :
  unshift_level (unshift_level l3 l2)
    (unshift_level (shift_level l2 l3) l1)
  = unshift_level l3 (unshift_level l2 l1).
Proof.
  intros.
  apply transpose_cycle_in_cycle_in_cycle_out_reverse_left.
Qed.

Lemma transpose_close_open_open_reverse_right n1 n2 n3 :
  unshift_name (unshift_name n3 n2)
               (unshift_name (shift_name n2 n3) n1)
  = unshift_name n3 (unshift_name n2 n1).
Proof.
  apply transpose_close_close_open_reverse_left.
Qed.

Lemma transpose_push_pop_pop_reverse_right op1 op2 op3 :
  unshift_pop_push
    (unshift_pop op3 op2)
    (unshift_pop_push (shift_pop op2 op3) op1)
  = unshift_pop_push op3 (unshift_pop_push op2 op1).
Proof.
  destruct op1 as [|l1|n1], op2 as [l2|n2], op3 as [l3|n3];
    cbn in *; try easy; intros.
  - rewrite transpose_cycle_in_cycle_out_cycle_out_reverse_right;
      easy.
  - rewrite transpose_close_open_open_reverse_right; easy.
Qed.
