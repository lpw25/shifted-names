Require Import String PeanoNat Compare_dec
        Psatz StrictProp Setoid Morphisms.
Require Import Morph Var.

(* Inequalities can be unsquashed *)

Lemma sneq_neq {A} {x y : A} :
  Squash (x <> y) -> x <> y.
Proof.
  intros Hsneq Heq.
  apply sEmpty_rec; destruct Hsneq; contradiction.
Qed.

(* Inversion on the index of a level *)
Ltac inversion_level l :=
  let l' := fresh "l'" in
  let Heql := fresh "Heql" in
  remember l as l' eqn:Heql;
  match type of l' with
  | level ?N =>
    let N' := eval cbn in N in
    destruct N';
      [exfalso; apply (level_zero_empty l')|]
  end;
  first [rewrite Heql|destruct (eq_sym Heql)]; clear Heql;
  try clear l'; cbn in *; eta_reduce_levels.

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

Lemma reduce_close_var_distinct {V} n1 n2 :
  n_string n1 <> n_string n2 ->
  @close_var n1 V (free n2) = free n2.
Proof.
  intros; unfold close_var.
  rewrite reduce_name_eqb_distinct by easy.
  rewrite reduce_unshift_name_distinct by easy.
  easy.
Qed.

Lemma reduce_close_var_lt {V} n1 n2 :
  n_string n1 = n_string n2 ->
  n_index n2 < n_index n1 ->
  @close_var n1 V (free n2) = free n2.
Proof.
  intros; unfold close_var.
  rewrite reduce_name_eqb_neq by lia.
  rewrite reduce_unshift_name_le by (try congruence; lia).
  easy.
Qed.

Lemma reduce_close_var_eq {V} n1 n2 :
  n_string n1 = n_string n2 ->
  n_index n1 = n_index n2 ->
  @close_var n1 V (free n2) = bound l_0.
Proof.
  intros; unfold close_var.
  rewrite reduce_name_eqb_eq by congruence.
  easy.
Qed.

Lemma reduce_close_var_gt {V} n1 n2 :
  n_string n1 = n_string n2 ->
  n_index n1 < n_index n2 ->
  @close_var n1 V (free n2)
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

Lemma reduce_shift_level_ge {N} (l1 : level N) l2 :
  l_nat l1 <= l_nat l2 ->
  shift_level l1 l2 = l_S' l2.
Proof.
  intros; unfold shift_level.
  destruct (le_gt_dec (l_nat l1) (l_nat l2));
    try easy; lia.
Qed.

Lemma reduce_shift_level_lt {N} (l1 : level N) l2 :
  S (l_nat l2) <= l_nat l1 ->
  shift_level l1 l2 = level_extend' l2.
Proof.
  intros; unfold shift_level.
  destruct (le_gt_dec (l_nat l1) (l_nat l2));
    try easy; lia.
Qed.

Lemma reduce_unshift_level_gt {N} (l1 : level N) l2 :
  S (l_nat l1) <= l_nat l2 ->
  forall (le : S (l_nat l1) <= l_nat l2),
  @unshift_level (S N) l1 l2
  = mklevel (pred (l_nat l2))
            (less_than_pred_le le (l_less_than l2)).
Proof.
  intros; unfold unshift_level.
  destruct (le_gt_dec (l_nat l2) (l_nat l1));
    try easy; lia.
Qed.

Lemma reduce_unshift_level_le {N} (l1 : level N) l2 :
  l_nat l2 <= l_nat l1 ->
  forall (le : l_nat l2 <= l_nat l1),
  @unshift_level (S N) l1 l2
  = mklevel (l_nat l2) (less_than_le le (l_less_than l1)).
Proof.
  intros; unfold unshift_level.
  destruct (le_gt_dec (l_nat l2) (l_nat l1));
    try easy; lia.
Qed.

Lemma reduce_unshift_level_neq_gt {N}
      (l1 : level N) l2 (sneq : Squash (l1 <> l2)) :
  S (l_nat l1) <= l_nat l2 ->
  forall (le : S (l_nat l1) <= l_nat l2),
  unshift_level_neq l1 l2 sneq
  = mklevel (pred (l_nat l2))
            (less_than_pred_le le (l_less_than l2)).
Proof.
  intros; unfold unshift_level_neq.
  destruct (le_gt_dec (l_nat l2) (l_nat l1));
    try easy; lia.
Qed.

Lemma reduce_unshift_level_neq_le {N}
      (l1 : level N) l2 (sneq : Squash (l1 <> l2)) :
  l_nat l2 <= l_nat l1 ->
  forall (le : l_nat l2 <= l_nat l1),
  unshift_level_neq l1 l2 sneq =
    mklevel (l_nat l2)
      (less_than_le_sneq le (l_nat_sinjective sneq)
         (l_less_than l1)).
Proof.
  intros; unfold unshift_level_neq.
  destruct (le_gt_dec (l_nat l2) (l_nat l1));
    try easy; lia.
Qed.

Lemma reduce_level_sdec_eq {N} (l1 : level N) l2 :
  forall (eql : l_nat l1 = l_nat l2),
  level_sdec l1 l2 = sleft (squash (lift_level_eq eql)).
Proof.
  intros; unfold level_sdec, level_dec.
  destruct (Nat.eq_dec (l_nat l1) (l_nat l2)) as [eql2|neql]; easy.
Qed.

Lemma reduce_level_sdec_neq {N} (l1 : level N) l2 :
  forall (neql : l_nat l1 <> l_nat l2),
  level_sdec l1 l2 = sright (squash (lift_level_neq neql)).
Proof.
  intros; unfold level_sdec, level_dec.
  destruct (Nat.eq_dec (l_nat l1) (l_nat l2)); easy.
Qed.

Lemma reduce_cycle_in_level_lt {N V} (l1 : level N) l2 :
  l_nat l2 < l_nat l1 ->
  forall (lt : l_nat l2 < l_nat l1),
  @cycle_in_level N l1 V l2
  = mklevel (S (l_nat l2))
      (less_than_le lt (less_than_extend_by V (l_less_than l1))).
Proof.
  intros; unfold cycle_in_level.
  (rewrite_strat (innermost reduce_level_sdec_neq));
    try (cbn in *; lia).
  (rewrite_strat (innermost reduce_unshift_level_le));
    try (cbn in *; lia).
   easy.
Qed.

Lemma reduce_cycle_in_level_eq {N V} (l1 : level N) l2 :
  l_nat l1 = l_nat l2 ->
  @cycle_in_level N l1 V l2
  = l_0' (squash (level_extend_by V l1)).
Proof.
  intros; unfold cycle_in_level.
  (rewrite_strat (innermost reduce_level_sdec_eq));
    try (cbn in *; lia).
  easy.
Qed.

Lemma reduce_cycle_in_level_gt {N V} (l1 : level N) l2 :
  l_nat l1 < l_nat l2 ->
  @cycle_in_level N l1 V l2 = l2.
Proof.
  intros; unfold cycle_in_level.
  (rewrite_strat (innermost reduce_level_sdec_neq));
    try (cbn in *; lia).
  unshelve (rewrite_strat (innermost reduce_unshift_level_gt));
    try (cbn in *; lia).
  easy.
Qed.

Hint Rewrite @reduce_shift_level_ge @reduce_shift_level_lt
     @reduce_cycle_in_level_eq @reduce_cycle_in_level_gt
     using (cbn in *; lia)
  : reduce_levels.

Hint Rewrite @reduce_unshift_level_gt @reduce_unshift_level_le
     @reduce_unshift_level_neq_gt @reduce_unshift_level_neq_le
     @reduce_cycle_in_level_lt
     using (cbn in *; lia)
  : reduce_levels_le.

Definition reduce_level_irrelevant {N} (l : level N) :
  forall (lt : less_than (l_nat l) N),
    mklevel (l_nat l) lt = l :=
  fun _ => eq_refl.

Hint Rewrite @reduce_level_irrelevant : reduce_level_irrelevant.

Ltac reduce_levels_rewrite :=
  autorewrite with reduce_levels;
  try
    (let le := fresh "le" in
     unshelve
       (eassert (_ <= _) as le by shelve;
        rewrite (reduce_unshift_level_le _ _ le le) in *);
       [> cbn in *; lia|]);
  try
    (let le := fresh "le" in
     unshelve
       (eassert (_ <= _) as le by shelve;
        rewrite (reduce_unshift_level_gt _ _ le le) in *);
       [> cbn in *; lia|]);
  try
    (let le := fresh "le" in
     unshelve
       (eassert (_ <= _) as le by shelve;
        rewrite (reduce_unshift_level_neq_le _ _ _ le le) in *);
       [> cbn in *; lia|]);
  try
    (let le := fresh "le" in
     unshelve
       (eassert (_ <= _) as le by shelve;
        rewrite (reduce_unshift_level_neq_gt _ _ _ le le) in *);
       [> cbn in *; lia|]);
  try
    (let le := fresh "le" in
     unshelve
       (eassert (_ <= _) as le by shelve;
        rewrite (reduce_cycle_in_level_lt _ _ le le) in *);
       [> cbn in *; lia|]);
  try
    (let eql := fresh "eql" in
     unshelve
       (eassert (_ = (_ : nat)) as eql by shelve;
        rewrite (reduce_level_sdec_eq _ _ eql) in *);
       [> cbn in *; lia|]);
  try
    (let neql := fresh "neql" in
     unshelve
       (eassert (_ <> (_ : nat)) as neql by shelve;
        rewrite (reduce_level_sdec_neq _ _ neql) in *);
       [> cbn in *; lia|]).

Ltac reduce_levels_rewrite_strat :=
  try (rewrite_strat (topdown (hints reduce_levels)));
  try
    (let le := fresh "le" in
     unshelve
       (eassert (_ <= _) as le by shelve;
        unshelve
          (rewrite_strat (innermost (hints reduce_levels_le)));
        try apply le);
     [> cbn in *; lia |]).

Ltac reduce_levels_match_rewrite :=
  match goal with
  | |- context [shift_level ?l1 ?l2] =>
    let le := fresh "le" in
    let Hrw := fresh "Hrw" in
    first
      [assert (l_nat l1 <= l_nat l2)
        as le by (cbn in *; lia);
       pose (reduce_shift_level_ge l1 l2 le) as Hrw
      |assert (S (l_nat l2) <= l_nat l1)
        as le by (cbn in *; lia);
       pose (reduce_shift_level_lt l1 l2 le) as Hrw];
    rewrite Hrw;
    clear Hrw
  | |- context [unshift_level ?l1 ?l2] =>
    let le := fresh "le" in
    let Hrw := fresh "Hrw" in
    first
      [assert (l_nat l2 <= l_nat l1)
        as le by (cbn in *; lia);
       pose (reduce_unshift_level_le l1 l2 le le) as Hrw
      |assert (S (l_nat l1) <= l_nat l2)
        as le by (cbn in *; lia);
       pose (reduce_unshift_level_gt l1 l2 le le) as Hrw];
    rewrite Hrw;
    clear Hrw
  | |- context [unshift_level_neq ?l1 ?l2 ?neq] =>
    let le := fresh "le" in
    let Hrw := fresh "Hrw" in
    first
      [assert (l_nat l2 <= l_nat l1)
        as le by (cbn in *; lia);
       pose (reduce_unshift_level_neq_le l1 l2 neq le le)
         as Hrw
      |assert (S (l_nat l1) <= l_nat l2)
        as le by (cbn in *; lia);
       pose (reduce_unshift_level_neq_gt l1 l2 neq le le)
         as Hrw];
    rewrite Hrw;
    clear Hrw
  | _ => idtac
  end.

Ltac reduce_levels :=
  try repeat
      (cbn in *; reduce_levels_rewrite_strat;
       reduce_levels_rewrite; reduce_levels_match_rewrite);
  autorewrite with reduce_level_irrelevant in *.

(* Case split on the order of the level parameters. *)
Ltac case_levels l1 l2 :=
  let Heq := fresh "Heq" in
  destruct (Compare_dec.lt_eq_lt_dec (l_nat l1) (l_nat l2))
    as [[|Heq]|];
  [|replace l2
      with (mklevel (l_nat l1)
             (less_than_cast (eq_sym Heq) (l_less_than l2)))
      by (apply lift_level_eq; easy);
    replace (l_nat l2) with (l_nat l1) by easy;
    cbn in Heq;
    try
      (destruct (Heq);
       match goal with
       | |- context [l2] => fail 1
       | _ => idtac
       end)|];
  reduce_levels;
  change (mklevel (l_nat l1) (l_less_than l1)) with l1;
  change (mklevel (l_nat l2) (l_less_than l2)) with l2;
  try lia.

(* Case split on a level *)
Tactic Notation "case_level" constr(l)
       "as" simple_intropattern(ln) simple_intropattern(lt) :=
  let l' := fresh "l" in
  let Heql := fresh "Heql" in
  remember l as l' eqn:Heql;
  symmetry in Heql;
  destruct l' as [[|ln] lt]; cbn in *;
    reduce_levels; try lia.

Tactic Notation "case_level" constr(l) :=
  let ln := fresh "ln" in
  let lt := fresh "lt" in
  case_level l as ln lt.

(* Case split on a variable *)
Tactic Notation "case_var" constr(v)
       "as" simple_intropattern(n) simple_intropattern(l) :=
  destruct v as [n|l]; cbn in *; eta_reduce_levels.

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

Lemma cycle_in_zero_identity {N} :
  @cycle_in_var (S N) l_0 =m= 1.
Proof.
  intros V v.
  case_var v as ? l2; try easy.
  unfold cycle_in_level.
  case_level l2 as ln2 lt2; easy.
Qed.

Lemma cycle_out_zero_identity {N} :
  @cycle_out_var (S N) l_0 =m= 1.
Proof.
  intros V v.
  case_var v as ? l2; try easy.
  unfold cycle_out_level.
  case_level l2 as ln2 lt2; easy.
Qed.

Lemma open_close_identity {N} (n : name) :
  morph_extend_by N (@open_var n)
  @ morph_extend_by N (@close_var n) =m= 1.
Proof.
  intros V v; unfold open_var, close_var.
  case_var v as n2 ?; try easy.
  case_names n n2; easy.
Qed.

Lemma open_close_identity' {N M} (n : name) (m : morph var M var N) :
  morph_extend_by N (@open_var n)
  @ (morph_extend_by N (@close_var n) @ m) =m= m.
Proof.
  rewrite morph_associative.
  rewrite open_close_identity.
  rewrite morph_left_identity.
  easy.
Qed.

Lemma close_open_identity {N} (n : name) :
  morph_extend_by N (@close_var n)
  @ morph_extend_by N (@open_var n) =m= 1.
Proof.
  intros V v; unfold open_var, close_var.
  case_var v as n2 l2.
  - case_names n n2; easy.
  - case_level l2; try easy.
    case_names n n; easy.
Qed.

Lemma close_open_identity' {N M} (n : name)
      (m : morph var M var (S N)) :
  morph_extend_by N (@close_var n)
  @ (morph_extend_by N (@open_var n) @ m) =m= m.
Proof.
  rewrite morph_associative.
  rewrite close_open_identity.
  rewrite morph_left_identity.
  easy.
Qed.

Lemma cycle_in_cycle_out_identity {N} (l : level N) :
  @cycle_in_var _ l @ @cycle_out_var _ l =m= 1.
Proof.
  intros V v.
  case_var v as ? l2; try easy.
  unfold cycle_in_level, cycle_out_level.
  case_level l2 as ln2 lt2; try easy.
  case_levels
    (mklevel (l_nat l)
             (less_than_extend_by V (l_less_than l)))
    (mklevel ln2 (less_than_pred lt2)); easy.
Qed.

Lemma cycle_in_cycle_out_identity' {N M} (l : level N)
      (m : morph var M var N) :
  @cycle_in_var _ l @ (@cycle_out_var _ l @ m) =m= m.
Proof.
  rewrite morph_associative.
  rewrite cycle_in_cycle_out_identity.
  rewrite morph_left_identity.
  easy.
Qed.

Lemma cycle_out_cycle_in_identity {N} (l : level N) :
  @cycle_out_var _ l @ @cycle_in_var _ l =m= 1.
Proof.
  intros V v.
  case_var v as ? l2; try easy.
  unfold cycle_in_level, cycle_out_level.
  case_levels l l2; try easy.
  case_level l2; easy.
Qed.

Lemma cycle_out_cycle_in_identity' {N M} (l : level N)
      (m : morph var M var N) :
  @cycle_out_var _ l @ (@cycle_in_var _ l @ m) =m= m.
Proof.
  rewrite morph_associative.
  rewrite cycle_out_cycle_in_identity.
  rewrite morph_left_identity.
  easy.
Qed.

Lemma swap_swap_identity {N} :
  morph_extend_by N (@swap_var)
  @ morph_extend_by N (@swap_var) =m= 1.
Proof.
  intros V v.
  case_var v as ? l; try easy.
  unfold swap_level.
  case_level l as ln lt; try easy.
  destruct ln; easy.
Qed.

Lemma swap_swap_identity' {N M} (m : morph var M var (2 + N)) :
  morph_extend_by N (@swap_var)
  @ (morph_extend_by N (@swap_var) @ m) =m= m.
Proof.
  rewrite morph_associative.
  rewrite swap_swap_identity.
  rewrite morph_left_identity.
  easy.
Qed.

Lemma unshift_level_neq_shift_level_identity
      {N} (l1 : level N) (l2 : level (pred N)) irr :
  @unshift_level_neq N l1 (shift_level l1 l2) irr = l2.
Proof.
  remember (shift_level l1 l2) as ls12 eqn:Heq;
    generalize dependent Heq.
  case_levels l1 l2;
    intro; subst; reduce_levels; easy.
Qed.

Lemma shift_level_unshift_level_neq_identity
      {N} (l1 : level N) (l2 : level N) irr :
  shift_level l1 (unshift_level_neq l1 l2 irr) = l2.
Proof.
  apply sneq_neq in irr as Hneq.
  inversion_level l1.
  case_levels l1 l2; try easy.
  - case_level l2; easy.
  - apply l_nat_injective in Hneq; contradiction.
Qed.

(* [lift_morph_var] distributes over composition and identity *)

Lemma lift_morph_var_compose {N M O}
      (m1 : morph var N var M) (m2 : morph var O var N) :
  lift_morph_var (m1 @ m2)
  =m= lift_morph_var m1 @ lift_morph_var m2.
Proof.
  intros V v.
  case_var v as n l.
  - case_var (m2 V (free n)); easy.
  - case_level l; try easy.
    case_var
      (m2 V (bound (@mklevel (O + V) ln (less_than_pred lt))));
      easy.
Qed.

Lemma lift_morph_var_id {N} :
  @lift_morph_var N N 1 =m= 1.
Proof.
  intros V v.
  case_var v as n l; try easy.
  case_level l; easy.
Qed.

(* Tactic to simplify compositions of var operations *)

Hint Rewrite <- morph_associative
  : normalize_morph_compose.
Hint Rewrite morph_left_identity morph_right_identity
  : normalize_morph_compose.

Hint Rewrite @lift_morph_var_id @lift_morph_var_compose
  : push_lift_morph_var.

Ltac simplify_var_morphs :=
  autorewrite with push_lift_morph_var;
  autorewrite with normalize_morph_compose.

(* [swap_var] transposes with lifted morphisms *)

Lemma transpose_swap_lifted N M m :
  morph_extend_by N (@swap_var)
  @ lift_morph_var (lift_morph_var m)
  =m= lift_morph_var (lift_morph_var m)
      @ morph_extend_by M (@swap_var).
Proof.
  intros V v.
  case_var v as n l.
  - case_var (m V (free n)); easy.
  - case_level l as ln lt; try easy.
    destruct ln; cbn; try easy.
    case_var
      (m V (@bound (M + V)
         (@mklevel (M + V) ln
            (less_than_pred (less_than_pred lt)))));
      easy.
Qed.

Lemma transpose_swap_lifted' {N M O} m1
      (m2 : morph var O var (S (S M))) :
  morph_extend_by N (@swap_var)
  @ (lift_morph_var (lift_morph_var m1) @ m2)
  =m= lift_morph_var (lift_morph_var m1)
      @ (morph_extend_by M (@swap_var) @ m2).
Proof.
  rewrite morph_associative.
  setoid_rewrite transpose_swap_lifted.
  rewrite <- morph_associative.
  easy.
Qed.

Definition morph_id_to_succ_pred {N} :
  level N -> morph var N var (S (pred N)) :=
  match N return level N -> morph _ N _ (S (pred N)) with
  | 0 => fun l => False_rec _ (level_zero_empty l)
  | S N => fun _ => morph_id
  end.

Definition morph_id_from_succ_pred {N} :
  level N -> morph var (S (pred N)) var N :=
  match N return level N -> morph _ (S (pred N)) _ N with
  | 0 => fun l => False_rec _ (level_zero_empty l)
  | S N => fun _ => morph_id
  end.

(* Transposing push operations

   We wish to reason about transposing "push" operations
   (i.e. [weak], [cycle_in] and [close]).
   These operations are not commutative, however they can be
   transposed by applying transformations to them.

   This situation is very close to that studied by the "operational
   transforms" literature in the context of collaborative text
   editors. However, rather than define the "ET" and "IT"
   transformations for our operations as they do, we will use a
   slightly different formulation.

   We define two transformations on operations:

     transpose_pushes_left(op1, op2)

     transpose_pushes_right(op2, op1)

   such that:

     lift_morph_var op1
     @ op2
     = swap_var
       @ lift_morph_var (transpose_pushes_left(op1, op2))
       @ (transpose_pushes_right(op2, op1)) *)

Inductive push_op (N : nat) : (nat -> nat) -> Type :=
| weak_op : push_op N (fun x => x)
| cycle_in_op : level N -> push_op N pred
| close_op : name -> push_op N (fun x => x).
Arguments weak_op {N}.
Arguments cycle_in_op {N}.
Arguments close_op {N}.

Definition apply_push_op_var {N f} (op : push_op N f)
  : morph var N var (S (f N)) :=
  match op in push_op _ f return morph _ _ _ (S (f N)) with
  | weak_op => morph_extend_by N (@weak_var)
  | cycle_in_op l =>
    morph_id_to_succ_pred l
    @ @cycle_in_var _ l
  | close_op n => morph_extend_by N (@close_var n)
  end.

Definition transpose_pushes_left {N f1 f2}
           (op1 : push_op (f2 N) f1) (op2 : push_op N f2) :
  push_op (f1 N) f2 :=
  match op2 in push_op _ f2, op1 in push_op _ f1
        return push_op (f1 N) f2
  with
  | weak_op, weak_op => weak_op
  | weak_op, cycle_in_op l => weak_op
  | weak_op, close_op n => weak_op
  | cycle_in_op l, weak_op => cycle_in_op l
  | cycle_in_op l2, cycle_in_op l1 =>
    cycle_in_op (unshift_level l1 l2)
  | cycle_in_op l, close_op n => cycle_in_op l
  | close_op n, weak_op => close_op n
  | close_op n, cycle_in_op l => close_op n
  | close_op n2, close_op n1 =>
    close_op (unshift_name n1 n2)
  end.

Definition transpose_pushes_right {N f1 f2}
           (op2 : push_op N f2) (op1 : push_op (f2 N) f1) :
  push_op N f1 :=
  match op2 in push_op _ f2, op1 in push_op _ f1
        return push_op N f1
  with
  | weak_op, weak_op => weak_op
  | weak_op, cycle_in_op l => cycle_in_op l
  | weak_op, close_op n => close_op n
  | cycle_in_op l, weak_op => weak_op
  | cycle_in_op l2, cycle_in_op l1 =>
    cycle_in_op (shift_level l2 l1)
  | cycle_in_op l, close_op n => close_op n
  | close_op n, weak_op => weak_op
  | close_op n, cycle_in_op l => cycle_in_op l
  | close_op n2, close_op n1 =>
    close_op (shift_name n2 n1)
  end.

Definition transpose_pushes_indices {N M O f1 f2}
  (op1 : push_op N f1) (op2 : push_op M f2)
  : morph var (f2 (f1 O)) var (f1 (f2 O)) :=
    match op2 in push_op _ f2, op1 in push_op _ f1
        return morph var (f2 (f1 O)) var (f1 (f2 O))
    with
    | weak_op, weak_op => 1
    | weak_op, cycle_in_op l => 1
    | weak_op, close_op n => 1
    | cycle_in_op l, weak_op => 1
    | cycle_in_op l1, cycle_in_op l2 => 1
    | cycle_in_op l, close_op n => 1
    | close_op n, weak_op => 1
    | close_op n, cycle_in_op l => 1
    | close_op n1, close_op n2 => 1
    end.

Lemma transpose_pushes {N f1 f2}
  (op1 : push_op (f2 N) f1) (op2 : push_op N f2) :
  lift_morph_var (apply_push_op_var op1)
  @ apply_push_op_var op2
  =m= lift_morph_var
        (lift_morph_var
           (transpose_pushes_indices op1 op2))
      @ morph_extend_by (f2 (f1 N)) (@swap_var)
      @ lift_morph_var
          (apply_push_op_var (transpose_pushes_left op1 op2))
      @ apply_push_op_var (transpose_pushes_right op2 op1).
Proof.
  intros V v.
  destruct op1 as [|l1|n1], op2 as [|l2|n2];
    simplify_var_morphs; cbn;
    case_var v as n3 l3; try easy.
  - case_var as ? l4; try easy.
    case_level l4; easy.
  - case_var as ? l4; try easy.
    case_level l4; easy.
  - case_var; try easy.
    case_level l; easy.
  - case_var as ? l4; try easy.
    case_level l4; easy.
  - case_var as ? l4; try easy.
    case_level l4; easy.
  - inversion_level l2.
    inversion_level l1.
    easy.
  - inversion_level l2.
    inversion_level l1.
    case_levels l2 l3.
    + case_level l3 as ln3 lt3.
      case_levels l2 l1.
      * case_levels l1 (mklevel ln3 (less_than_pred lt3));
          try easy.
        destruct ln3; easy.
      * case_levels l2 (mklevel ln3 (less_than_pred lt3));
          try easy.
        destruct ln3; easy.
      * destruct ln3; try lia; easy.
    + case_levels l2 l1; try easy.
      case_level l2; easy.
    + case_levels l1 l3; try easy.
      * case_level l3; easy.
      * case_levels l2 l1; easy.
  - inversion_level l1.
    case_names n2 n3; easy.
  - inversion_level l1.
    case_level (cycle_in_level l1 l3); easy.
  - case_var; try easy.
    case_level l; easy.
  - inversion_level l2.
    case_names n1 n3; easy.
  - inversion_level l2.
    case_level (cycle_in_level l2 l3); easy.
  - case_names n2 n3.
    + case_names n1 (mkname (n_string n3) (pred (n_index n3)));
        try easy.
      case_names n1 n2; easy.
    + case_names n2 n1; easy.
    + case_names n1 n3; try easy.
      case_names n1 n2; try easy.
      congruence.
    + case_names n1 n3; try easy.
      case_names n1 n2; easy.
Qed.

Tactic Notation
  "transpose_pushes" open_constr(op1) open_constr(op2) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_pushes op1 op2) as Hrw;
      cbn in Hrw;
      autorewrite with push_lift_morph_var in Hrw;
      autorewrite with normalize_morph_compose in Hrw;
      rewrite Hrw; clear Hrw.

Tactic Notation
  "transpose_pushes" open_constr(op1) open_constr(op2)
    "at" occurrences(occ) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_pushes op1 op2) as Hrw;
      cbn in Hrw;
      autorewrite with push_lift_morph_var in Hrw;
      autorewrite with normalize_morph_compose in Hrw;
      rewrite Hrw at occ; clear Hrw.

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

Lemma transpose_cycle_ins_squared_left {N} (l1 : level N) l2 :
  unshift_level (@unshift_level (S N) l1 l2) (shift_level l2 l1)
  = l1.
Proof.
  case_levels l1 l2; easy.
Qed.

Lemma transpose_closes_squared_left n1 n2 :
  unshift_name (unshift_name n1 n2) (shift_name n2 n1)
  = n1.
Proof.
  case_names n1 n2; easy.
Qed.

Lemma transpose_pushes_squared_left {N f1 f2}
      (op1 : push_op (f2 N) f1) (op2 : push_op N f2) :
    transpose_pushes_left
      (transpose_pushes_left op1 op2)
      (transpose_pushes_right op2 op1)
    = op1.
Proof.
  destruct op1 as [|l1|n1], op2 as [|l2|n2]; cbn; try easy.
  - inversion_level l2.
    rewrite transpose_cycle_ins_squared_left; easy.
  - rewrite transpose_closes_squared_left; easy.
Qed.

Lemma transpose_cycle_ins_squared_right {N} l1 (l2 : level (S N)) :
  shift_level (@shift_level (S N) l2 l1) (unshift_level l1 l2)
  = l2.
Proof.
  case_levels l2 l1; try easy.
  case_level l2; easy.
Qed.

Lemma transpose_closes_squared_right n1 n2 :
  shift_name (shift_name n2 n1) (unshift_name n1 n2) = n2.
Proof.
  case_names n2 n1; easy.
Qed.

Lemma transpose_pushes_squared_right {N f1 f2}
      (op1 : push_op (f2 N) f1) (op2 : push_op N f2) :
    transpose_pushes_right
      (transpose_pushes_right op2 op1)
      (transpose_pushes_left op1 op2)
    = op2.
Proof.
  destruct op1 as [|l1|n1], op2 as [|l2|n2]; cbn; try easy.
  - inversion_level l2; inversion_level l1.
    rewrite @transpose_cycle_ins_squared_right; easy.
  - rewrite transpose_closes_squared_right; easy.
Qed.

Definition transpose_pushes_indices_op {N M O f1 f2 f3}
           (op1 : push_op N f1)
           (op2 : push_op M f2)
  : push_op (f1 (f2 O)) f3 -> push_op (f2 (f1 O)) f3 :=
    match op1 in push_op _ f1, op2 in push_op _ f2
        return push_op (f1 (f2 O)) f3 -> push_op (f2 (f1 O)) f3
    with
    | weak_op, weak_op => fun op => op
    | weak_op, cycle_in_op l => fun op => op
    | weak_op, close_op n => fun op => op
    | cycle_in_op l, weak_op => fun op => op
    | cycle_in_op l1, cycle_in_op l2 => fun op => op
    | cycle_in_op l, close_op n => fun op => op
    | close_op n, weak_op => fun op => op
    | close_op n, cycle_in_op l => fun op => op
    | close_op n1, close_op n2 => fun op => op
    end.

Lemma transpose_cycle_ins_reverse_left {N} (l1 : level N) l2 l3 :
  unshift_level (@unshift_level (S N) l1 l2)
    (@unshift_level (S (S N)) (shift_level l2 l1) l3)
  = @unshift_level (S N) l1 (@unshift_level (S (S N)) l2 l3).
Proof.
  case_levels l1 l2;
    case_levels l2 l3; try easy.
  - case_levels l1 l3; easy.
  - case_levels (l_S l1) l3; easy.
  - case_levels (l_S l1) l3; easy.
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

Lemma transpose_pushes_reverse_left {N f1 f2 f3}
      (op1 : push_op (f2 (f3 N)) f1)
      (op2 : push_op (f3 N) f2) (op3 : push_op N f3) :
    transpose_pushes_left
      (transpose_pushes_indices_op op1 op3
        (transpose_pushes_left op1 op2))
      (transpose_pushes_left
        (transpose_pushes_right op2 op1) op3)
    = transpose_pushes_indices_op op1 op2
        (transpose_pushes_left
          (transpose_pushes_indices_op op2 op3 op1)
          (transpose_pushes_left op2 op3)).
Proof.
  destruct op1 as [|l1|n1], op2 as [|l2|n2], op3 as [|l3|n3];
    cbn in *; try easy.
  - inversion_level l3; inversion_level l2; inversion_level l1.
    rewrite transpose_cycle_ins_reverse_left; easy.
  - rewrite transpose_closes_reverse_left; easy.
Qed.

Lemma transpose_cycle_ins_reverse_middle {N}
      (l1 : level N) (l2 : level (S N)) (l3 : level (S (S N))) :
  unshift_level
       (shift_level (@unshift_level (S (S N)) l2 l3) l1)
       (shift_level l3 l2) =
  shift_level
    (@unshift_level (S (S N)) (shift_level l2 l1) l3)
    (@unshift_level (S N) l1 l2).
Proof.
  case_levels l1 l2.
  - case_levels l2 l3;
      case_levels l3 l1; try easy;
        case_level l2; easy.
  - case_levels (l_S l1) l3; easy.
  - case_levels l2 l3; try easy.
    case_levels (l_S l1) l3; easy.
Qed.

Lemma transpose_closes_reverse_middle n1 n2 n3 :
  unshift_name (shift_name (unshift_name n2 n3) n1)
               (shift_name n3 n2)
  = shift_name (unshift_name (shift_name n2 n1) n3)
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

Lemma transpose_pushes_reverse_middle {N f1 f2 f3}
      (op1 : push_op (f2 (f3 N)) f1)
      (op2 : push_op (f3 N) f2) (op3 : push_op N f3) :
  transpose_pushes_left
    (transpose_pushes_right
       (transpose_pushes_left op2 op3)
       (transpose_pushes_indices_op op2 op3 op1))
    (transpose_pushes_right op3 op2)
  = transpose_pushes_right
      (transpose_pushes_left
         (transpose_pushes_right op2 op1) op3)
      (transpose_pushes_indices_op op1 op3
        (transpose_pushes_left op1 op2)).
Proof.
  destruct op1 as [|l1|n1], op2 as [|l2|n2], op3 as [|l3|n3];
    cbn in *; try easy.
  - inversion_level l3; inversion_level l2; inversion_level l1.
    rewrite @transpose_cycle_ins_reverse_middle; easy.
  - rewrite transpose_closes_reverse_middle; easy.
Qed.

Lemma transpose_cycle_ins_reverse_right {N}
      l1 l2 (l3 : level (S N)) :
  shift_level (shift_level l3 l2)
              (shift_level (unshift_level l2 l3) l1)
  = shift_level l3 (shift_level l2 l1).
Proof.
  case_levels l2 l3.
  - case_levels (l_S l1) l3; try easy.
    case_levels l1 l2; easy.
  - case_levels l1 l2; easy.
  - case_levels l1 l3; try easy.
    case_levels l1 l2; easy.
Qed.

Lemma transpose_closes_reverse_right n1 n2 n3 :
  shift_name (shift_name n3 n2)
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

Lemma transpose_pushes_reverse_right  {N f1 f2 f3}
      (op1 : push_op (f2 (f3 N)) f1)
      (op2 : push_op (f3 N) f2) (op3 : push_op N f3) :
    transpose_pushes_right
      (transpose_pushes_right op3 op2)
      (transpose_pushes_right
        (transpose_pushes_left op2 op3)
        (transpose_pushes_indices_op op2 op3 op1))
    = transpose_pushes_right op3
        (transpose_pushes_right op2 op1).
Proof.
  destruct op1 as [|l1|n1], op2 as [|l2|n2], op3 as [|l3|n3];
    cbn in *; try easy.
  - inversion_level l3; inversion_level l2; inversion_level l1.
    rewrite @transpose_cycle_ins_reverse_right; easy.
  - rewrite transpose_closes_reverse_right; easy.
Qed.

(* Permutations of "pop" operations. As with the push
   operations, we want to reason about permutations of the
   "pop" operations (i.e. open and cycle_out). As with
   pushes, we define arbitrary transpositions and then the
   equations on those transpositions required to define the
   full group of permutations. *)

Inductive pop_op (N : nat) : (nat -> nat) -> Type :=
| cycle_out_op : level N -> pop_op N pred
| open_op : name -> pop_op N (fun x => x).
Arguments cycle_out_op {N}.
Arguments open_op {N}.

Definition apply_pop_op_var {N f} (op : pop_op N f)
  : morph var (S (f N)) var N :=
  match op in pop_op _ f return morph var (S (f N)) _ _ with
  | cycle_out_op l =>
    @cycle_out_var _ l
    @ morph_id_from_succ_pred l
  | open_op n => morph_extend_by N (@open_var n)
  end.

Definition transpose_pops_left {N f1 f2}
           (op1 : pop_op N f1) (op2 : pop_op (f1 N) f2) :
  pop_op N f2 :=
  match op1 in pop_op _ f1, op2 in pop_op _ f2
        return pop_op N f2
  with
  | cycle_out_op l1, cycle_out_op l2 =>
    cycle_out_op (shift_level l1 l2)
  | cycle_out_op l, open_op n => open_op n
  | open_op n, cycle_out_op l => cycle_out_op l
  | open_op n1, open_op n2 => open_op (shift_name n1 n2)
  end.

Definition transpose_pops_right {N f1 f2}
            (op2 : pop_op (f1 N) f2) (op1 : pop_op N f1) :
  pop_op (f2 N) f1 :=
  match op1 in pop_op _ f1, op2 in pop_op _ f2
        return pop_op (f2 N) f1
  with
  | cycle_out_op l1, cycle_out_op l2 =>
    cycle_out_op (unshift_level l2 l1)
  | cycle_out_op l, open_op n => cycle_out_op l
  | open_op n, cycle_out_op l => open_op n
  | open_op n1, open_op n2 => open_op (unshift_name n2 n1)
  end.

Definition transpose_pops_indices {N M O f1 f2}
           (op1 : pop_op N f1) (op2 : pop_op M f2)
  : morph var (f2 (f1 O)) var (f1 (f2 O)) :=
    match op2 in pop_op _ f2, op1 in pop_op _ f1
        return morph var (f2 (f1 O)) var (f1 (f2 O))
    with
    | cycle_out_op l1, cycle_out_op l2 => 1
    | cycle_out_op l, open_op n => 1
    | open_op n, cycle_out_op l => 1
    | open_op n1, open_op n2 => 1
    end.

Lemma transpose_pops {N f1 f2}
      (op1 : pop_op N f1) (op2 : pop_op (f1 N) f2)  :
  apply_pop_op_var op1
  @ lift_morph_var (apply_pop_op_var op2)
  =m= apply_pop_op_var (transpose_pops_left op1 op2)
      @ lift_morph_var
          (apply_pop_op_var (transpose_pops_right op2 op1))
      @ morph_extend_by (f1 (f2 N)) (@swap_var)
      @ lift_morph_var
          (lift_morph_var
            (transpose_pops_indices op1 op2)).
Proof.
  intros V v.
  destruct op1 as [l1|n1], op2 as [l2|n2];
    simplify_var_morphs; cbn.
  - inversion_level l1; inversion_level l2.
    case_var v as n3 l3; try easy.
    unfold cycle_out_var, cycle_out_level.
    case_level l3 as [|ln3] lt3.
    + case_levels l1 l2; try easy.
      case_level l1; easy.
    + case_levels l1 l2; easy.
    + case_levels l2
        (mklevel ln3 (less_than_pred (less_than_pred lt3))).
      * case_levels l1 l2; try easy.
        case_level l1.
        case_levels
          (mklevel ln (less_than_pred
                         (less_than_extend_by V lt)))
          (mklevel ln3 (less_than_pred (less_than_pred lt3)));
          easy.
      * case_levels l1 (l_S l2); easy.
      * case_levels l1
          (mklevel ln3 (less_than_pred (less_than_pred lt3)));
          try easy.
        case_levels l1 l2; easy.
  - inversion_level l1.
    case_var v; try easy.
    case_level l as [|ln] lt; easy.
  - inversion_level l2.
    case_var v; try easy.
    case_level l as [|ln] lt; easy.
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
    + case_level l as [|ln] lt; try easy.
      case_names n1 n2; easy.
Qed.

Tactic Notation
  "transpose_pops" open_constr(op1) open_constr(op2) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_pops op1 op2) as Hrw;
      cbn in Hrw;
      autorewrite with push_lift_morph_var in Hrw;
      autorewrite with normalize_morph_compose in Hrw;
      rewrite Hrw; clear Hrw.

Tactic Notation
  "transpose_pops" open_constr(op1) open_constr(op2)
    "at" occurrences(occ) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_pops op1 op2) as Hrw;
      cbn in Hrw;
      autorewrite with push_lift_morph_var in Hrw;
      autorewrite with normalize_morph_compose in Hrw;
      rewrite Hrw at occ; clear Hrw.

Lemma transpose_cycle_outs_squared_left {N}
      (l1 : level (S N)) l2 :
  shift_level (shift_level l1 l2) (unshift_level l2 l1)
  = l1.
Proof.
  case_levels l1 l2; try easy.
  case_level l1; easy.
Qed.

Lemma transpose_opens_squared_left n1 n2 :
  shift_name (shift_name n1 n2) (unshift_name n2 n1)
  = n1.
Proof.
  case_names n1 n2; easy.
Qed.

Lemma transpose_pops_squared_left {N f1 f2}
      (op1 : pop_op N f1) (op2 : pop_op (f1 N) f2)  :
    transpose_pops_left
      (transpose_pops_left op1 op2)
      (transpose_pops_right op2 op1)
    = op1.
Proof.
  destruct op1 as [l1|n1], op2 as [l2|n2]; cbn; try easy.
  - inversion_level l1; inversion_level l2.
    rewrite @transpose_cycle_outs_squared_left; easy.
  - rewrite transpose_opens_squared_left; easy.
Qed.

Lemma transpose_cycle_outs_squared_right {N}
      l1 (l2 : level (S N)) :
  unshift_level (@unshift_level (S (S N)) l2 l1) (shift_level l1 l2)
  = l2.
Proof.
  case_levels l2 l1; easy.
Qed.

Lemma transpose_opens_squared_right n1 n2 :
  unshift_name (unshift_name n2 n1) (shift_name n1 n2) = n2.
Proof.
  case_names n2 n1; easy.
Qed.

Lemma transpose_pops_squared_right {N f1 f2}
      (op1 : pop_op N f1) (op2 : pop_op (f1 N) f2)  :
    transpose_pops_right
      (transpose_pops_right op2 op1)
      (transpose_pops_left op1 op2)
    = op2.
Proof.
  destruct op1 as [l1|n1], op2 as [l2|n2]; cbn; try easy.
  - inversion_level l1; inversion_level l2.
    rewrite @transpose_cycle_outs_squared_right; easy.
  - rewrite transpose_opens_squared_right; easy.
Qed.

Definition transpose_pops_indices_op {N M O f1 f2 f3}
           (op1 : pop_op N f1)
           (op2 : pop_op M f2)
  : pop_op (f1 (f2 O)) f3 -> pop_op (f2 (f1 O)) f3 :=
    match op1 in pop_op _ f1, op2 in pop_op _ f2
        return pop_op (f1 (f2 O)) f3 -> pop_op (f2 (f1 O)) f3
    with
    | cycle_out_op l1, cycle_out_op l2 => fun op => op
    | cycle_out_op l, open_op n => fun op => op
    | open_op n, cycle_out_op l => fun op => op
    | open_op n1, open_op n2 => fun op => op
    end.

Lemma transpose_cycle_outs_reverse_left {N}
      (l1 : level (S N)) l2 l3 :
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

Lemma transpose_pops_reverse_left {N f1 f2 f3}
      (op1 : pop_op N f1) (op2 : pop_op (f1 N) f2)
      (op3 : pop_op (f2 (f1 N)) f3) :
    transpose_pops_left
      (transpose_pops_left op1 op2)
      (transpose_pops_left
        (transpose_pops_right op2 op1)
        (transpose_pops_indices_op op2 op1 op3))
    = transpose_pops_left op1
        (transpose_pops_left op2 op3).
Proof.
  destruct op1 as [l1|n1], op2 as [l2|n2], op3 as [l3|n3];
    cbn in *; try easy.
  - inversion_level l1; inversion_level l2; inversion_level l3.
    rewrite @transpose_cycle_outs_reverse_left; easy.
  - rewrite transpose_opens_reverse_left; easy.
Qed.

Lemma transpose_cycle_outs_reverse_middle {N}
      (l1 : level (S (S N))) (l2 : level (S N)) (l3 : level N) :
    @shift_level (S N)
       (@unshift_level (S (S N)) (shift_level l2 l3) l1)
                (@unshift_level (S N) l3 l2)
    = unshift_level (shift_level
                       (@unshift_level (S (S N)) l2 l1) l3)
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

Lemma transpose_pops_reverse_middle {N f1 f2 f3}
      (op1 : pop_op N f1) (op2 : pop_op (f1 N) f2)
      (op3 : pop_op (f2 (f1 N)) f3) :
  transpose_pops_left
    (transpose_pops_right
       (transpose_pops_left op2 op3) op1)
    (transpose_pops_indices_op op3 op1
       (transpose_pops_right op3 op2))
  = transpose_pops_right
      (transpose_pops_left
         (transpose_pops_right op2 op1)
         (transpose_pops_indices_op op2 op1 op3))
      (transpose_pops_left op1 op2).
Proof.
  destruct op1 as [l1|n1], op2 as [l2|n2], op3 as [l3|n3];
    cbn in *; try easy.
  - inversion_level l1; inversion_level l2; inversion_level l3.
    rewrite @transpose_cycle_outs_reverse_middle; easy.
  - rewrite transpose_opens_reverse_middle; easy.
Qed.

Lemma transpose_cycle_outs_reverse_right {N}
      (l1 : level (S (S N)))
      (l2 : level (S N)) (l3 : level N) :
  unshift_level (@unshift_level (S N) l3 l2)
       (@unshift_level (S (S N)) (shift_level l2 l3) l1)
  = @unshift_level (S N) l3 (@unshift_level (S (S N)) l2 l1).
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

Lemma transpose_pops_reverse_right {N f1 f2 f3}
      (op1 : pop_op N f1) (op2 : pop_op (f1 N) f2)
      (op3 : pop_op (f2 (f1 N)) f3) :
    transpose_pops_right
      (transpose_pops_indices_op op3 op1
         (transpose_pops_right op3 op2))
      (transpose_pops_right
        (transpose_pops_left op2 op3) op1)
    = transpose_pops_indices_op op3 op2
        (transpose_pops_right
          (transpose_pops_indices_op op2 op1 op3)
          (transpose_pops_right op2 op1)).
Proof.
  destruct op1 as [l1|n1], op2 as [l2|n2], op3 as [l3|n3];
    cbn in *; try easy.
  - inversion_level l1; inversion_level l2; inversion_level l3.
    rewrite @transpose_cycle_outs_reverse_right; easy.
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

Definition irreducible_push_pop_ops {N f1 f2}
           (op1 : push_op N f1) (op2 : pop_op N f2) :
  SProp :=
  match op1, op2 with
  | weak_op, cycle_out_op l => sUnit
  | weak_op, open_op n => sUnit
  | cycle_in_op l1, cycle_out_op l2 => Squash (l1 <> l2)
  | cycle_in_op l, open_op n => sUnit
  | close_op n, cycle_out_op l => sUnit
  | close_op n1, open_op n2 => Squash (n1 <> n2)
  end.

Definition transpose_push_pop_left {N f1 f2}
           (op1 : push_op N f1) (op2 : pop_op N f2) :
  irreducible_push_pop_ops op1 op2 -> pop_op (f1 N) f2 :=
  match op1 in push_op _ f1, op2 in pop_op _ f2
        return irreducible_push_pop_ops op1 op2
               -> pop_op (f1 N) f2
  with
  | weak_op, cycle_out_op l =>
    fun _ => cycle_out_op l
  | weak_op, open_op n =>
    fun _ => open_op n
  | cycle_in_op l1, cycle_out_op l2 =>
    fun neql => cycle_out_op
                  (unshift_level_neq l1 l2 neql)
  | cycle_in_op l, open_op n =>
    fun _ => open_op n
  | close_op n, cycle_out_op l =>
    fun _ => cycle_out_op l
  | close_op n1, open_op n2 =>
    fun _ => open_op (unshift_name n1 n2)
  end.

Definition transpose_push_pop_right {N f1 f2}
            (op2 : pop_op N f2) (op1 : push_op N f1) :
  irreducible_push_pop_ops op1 op2 -> push_op (f2 N) f1 :=
  match op2 in pop_op _ f2, op1 in push_op _ f1
        return irreducible_push_pop_ops op1 op2 ->
               push_op (f2 N) f1
  with
  | cycle_out_op l, weak_op => fun _ => weak_op
  | cycle_out_op l2, cycle_in_op l1 =>
    fun neql =>
      cycle_in_op (unshift_level_neq l2 l1 (sneq_sym neql))
  | cycle_out_op l, close_op n => fun _ => close_op n
  | open_op n, weak_op => fun _ => weak_op
  | open_op n, cycle_in_op l => fun _ => cycle_in_op l
  | open_op n2, close_op n1 =>
    fun _ => close_op (unshift_name n2 n1)
  end.

Definition transpose_push_pop_indices {N M O f1 f2}
           (op1 : push_op N f1) (op2 : pop_op M f2)
  : morph var (f1 (f2 O)) var (f2 (f1 O)) :=
    match op2 in pop_op _ f2, op1 in push_op _ f1
        return morph var (f1 (f2 O)) var (f2 (f1 O))
    with
    | cycle_out_op l1, weak_op => 1
    | cycle_out_op l1, cycle_in_op l2 => 1
    | cycle_out_op l, close_op n => 1
    | open_op n, weak_op => 1
    | open_op n, cycle_in_op l => 1
    | open_op n1, close_op n2 => 1
    end.

Lemma transpose_push_pop {N f1 f2}
      (op1 : push_op N f1) (op2 : pop_op N f2) :
  forall (irr : irreducible_push_pop_ops op1 op2),
  apply_push_op_var op1
  @ apply_pop_op_var op2
  =m= lift_morph_var
        (apply_pop_op_var (transpose_push_pop_left op1 op2 irr))
      @ lift_morph_var
          (lift_morph_var
            (transpose_push_pop_indices op1 op2))
      @ morph_extend_by (f1 (f2 N)) (@swap_var)
      @ lift_morph_var
          (apply_push_op_var (transpose_push_pop_right op2 op1 irr)).
Proof.
  intros Hirr V v.
  destruct op1 as [|l1|n1] eqn:Heqop1, op2 as [l2|n2] eqn:Heqop2;
    simplify_var_morphs; cbn; case_var v as n l; try easy.
  - case_level l; easy.
  - case_level l; easy.
  - inversion_level l2.
    inversion_level (unshift_level_neq l2 l1 (sneq_sym Hirr)).
    easy.
  - inversion_level l2.
    inversion_level (unshift_level_neq l1 l2 Hirr).
    unfold cycle_out_var, cycle_out_level.
    apply sneq_neq in Hirr as Hneq.
    case_level l.
    + case_levels l1 l2; try easy.
      * case_level l2; easy.
      * apply l_nat_injective in Hneq; contradiction.
    + case_levels l1 l2.
      * { case_levels l2 (mklevel ln (less_than_pred lt)).
          - destruct ln; try lia; cbn.
            case_levels l2 (mklevel (S ln) (less_than_pred lt));
              easy.
          - case_level l2; easy.
          - case_levels l1
              (mklevel ln (less_than_pred lt)); try easy.
            destruct ln; try lia; cbn.
            case_levels l2 (mklevel (S ln) (less_than_pred lt));
              easy. }
      * apply l_nat_injective in Hneq; contradiction.
      * { case_levels l1 (mklevel (S ln) lt); try easy.
          - destruct ln; try lia; cbn.
            case_levels l2
              (mklevel ln (less_than_pred (less_than_pred lt)));
              easy.
          - case_levels l2
              (mklevel ln (less_than_pred lt)); easy. }
  - inversion_level l1; easy.
  - inversion_level l1.
    case_level l; try easy.
    case_levels l1 (mklevel ln (less_than_pred lt)); try easy.
    destruct ln; try lia; easy.
  - inversion_level l2.
    case_names n1 n; easy.
  - inversion_level l2.
    unfold cycle_out_var, cycle_out_level.
    case_level l; easy.
  - apply sneq_neq in Hirr as Hneq.
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
  - apply sneq_neq in Hirr as Hneq.
    case_level l; try easy.
    case_names n1 n2; easy.
Qed.

Tactic Notation
  "transpose_push_pop" open_constr(op1) open_constr(op2) :=
  let irr := fresh "irr" in
  assert (irreducible_push_pop_ops op1 op2) as irr
    by (try easy; try solve [apply squash; congruence]);
  cbn in irr;
  let Hrw := fresh "Hrw" in
  epose (transpose_push_pop op1 op2 irr) as Hrw; cbn in Hrw;
  autorewrite with push_lift_morph_var in Hrw;
  autorewrite with normalize_morph_compose in Hrw;
  setoid_rewrite Hrw; clear Hrw.

Tactic Notation
  "transpose_push_pop" open_constr(op1) open_constr(op2)
    "at" occurrences(occ) :=
  let irr := fresh "irr" in
  assert (irreducible_push_pop_ops op1 op2) as irr
    by (try easy; try solve [apply squash; congruence]);
  cbn in irr;
  let Hrw := fresh "Hrw" in
  epose (transpose_push_pop op1 op2 irr) as Hrw; cbn in Hrw;
  autorewrite with push_lift_morph_var in Hrw;
  autorewrite with normalize_morph_compose in Hrw;
  setoid_rewrite Hrw at occ; clear Hrw.

Definition transpose_push_push_pop_indices_op
           {N M O f1 f2 f3}
           (op1 : push_op N f1)
           (op2 : push_op M f2)
  : pop_op (f1 (f2 O)) f3 -> pop_op (f2 (f1 O)) f3 :=
    match op1 in push_op _ f1, op2 in push_op _ f2
        return pop_op (f1 (f2 O)) f3 -> pop_op (f2 (f1 O)) f3
    with
    | weak_op, weak_op => fun op => op
    | weak_op, cycle_in_op l => fun op => op
    | weak_op, close_op n => fun op => op
    | cycle_in_op l, weak_op => fun op => op
    | cycle_in_op l1, cycle_in_op l2 => fun op => op
    | cycle_in_op l, close_op n => fun op => op
    | close_op n, weak_op => fun op => op
    | close_op n, cycle_in_op l => fun op => op
    | close_op n1, close_op n2 => fun op => op
    end.

Definition transpose_pop_push_push_indices_op
           {N M O f1 f2 f3}
           (op1 : pop_op N f1)
           (op2 : push_op M f2)
  : push_op (f1 (f2 O)) f3 -> push_op (f2 (f1 O)) f3 :=
    match op1 in pop_op _ f1, op2 in push_op _ f2
        return push_op (f1 (f2 O)) f3 -> push_op (f2 (f1 O)) f3
    with
    | cycle_out_op l, weak_op => fun op => op
    | cycle_out_op l1, cycle_in_op l2 => fun op => op
    | cycle_out_op l, close_op n => fun op => op
    | open_op n, weak_op => fun op => op
    | open_op n, cycle_in_op l => fun op => op
    | open_op n2, close_op n1 => fun op => op
    end.

Lemma transpose_cycle_in_cycle_in_cycle_out_reverse_left
      {N} (l1 : level N) l2 l3 :
  forall
    (irr1 : Squash (@shift_level (S N) l2 l1 <> l3))
    (irr2 : Squash
              (@unshift_level (S N) l1 l2 <>
               unshift_level_neq
                 (shift_level l2 l1) l3 irr1))
    (irr3 : Squash (l2 <> l3))
    (irr4 : Squash (l1 <> unshift_level_neq l2 l3 irr3)),
    @unshift_level_neq N (@unshift_level (S N) l1 l2)
      (@unshift_level_neq (S N) (shift_level l2 l1) l3 irr1) irr2
    = @unshift_level_neq N
        l1 (unshift_level_neq l2 l3 irr3) irr4.
Proof.
  intros.
  remember (unshift_level_neq l2 l3 irr3) as lu23 eqn:Heq;
    generalize dependent Heq.
  remember (unshift_level_neq (shift_level l2 l1) l3 irr1)
    as lu213 eqn:Heq;
    generalize dependent Heq.
  remember (@unshift_level (S N) l1 l2) as lu12 eqn:Heq;
    generalize dependent Heq.
  remember (shift_level l2 l1) as ls21 eqn:Heq;
    generalize dependent Heq.
  case_levels l2 l1;
    case_levels ls21 l3;
      case_levels l2 l3;
        intros; subst; reduce_levels; try easy; try lia.
Qed.

Lemma transpose_close_close_open_reverse_left n1 n2 n3 :
  unshift_name (unshift_name n1 n2)
    (unshift_name (shift_name n2 n1) n3)
  = unshift_name n1 (unshift_name n2 n3).
Proof.
  apply transpose_closes_reverse_left.
Qed.

Lemma transpose_push_push_pop_reverse_left {N f1 f2 f3}
      (op1 : push_op (f2 N) f1) (op2 : push_op N f2)
      (op3 : pop_op N f3) :
    forall
      (irr1 : irreducible_push_pop_ops
                (transpose_pushes_right op2 op1) op3)
      (irr2 : irreducible_push_pop_ops
                (transpose_pushes_left op1 op2)
                (transpose_push_pop_left
                   (transpose_pushes_right op2 op1) op3
                   irr1))
      (irr3 : irreducible_push_pop_ops op2 op3)
      (irr4 : irreducible_push_pop_ops op1
                (transpose_push_pop_left op2 op3 irr3)),
    transpose_push_pop_left
      (transpose_pushes_left op1 op2)
      (transpose_push_pop_left
        (transpose_pushes_right op2 op1) op3 irr1)
      irr2
    = transpose_push_push_pop_indices_op op1 op2
        (transpose_push_pop_left op1
          (transpose_push_pop_left op2 op3 irr3) irr4).
Proof.
  destruct op1 as [|l1|n1], op2 as [|l2|n2], op3 as [l3|n3];
    cbn in *; try easy; intros.
  - inversion_level l2; inversion_level l1.
    erewrite
      @transpose_cycle_in_cycle_in_cycle_out_reverse_left;
      easy.
  - rewrite transpose_close_close_open_reverse_left; easy.
Qed.

Lemma transpose_cycle_in_cycle_in_cycle_out_reverse_middle {N}
      (l1 : level N) (l2 : level (S N)) (l3 : level (S N)) :
  forall (irr1 : Squash (l2 <> l3))
         (irr2 : Squash (unshift_level_neq l2 l3 irr1 <> l1))
         (irr3 : Squash (shift_level l2 l1 <> l3))
         (irr4 : Squash
                   (unshift_level_neq (shift_level l2 l1) l3
                                      irr3
                    <> @unshift_level (S N) l1 l2)),
    @unshift_level N
      (unshift_level_neq (unshift_level_neq l2 l3 irr1)
         l1 irr2)
      (unshift_level_neq l3 l2 (sneq_sym irr1)) =
    unshift_level_neq
      (unshift_level_neq (shift_level l2 l1) l3 irr3)
      (@unshift_level (S N) l1 l2) irr4.
Proof.
  intros; inversion_level l1.
  remember (unshift_level_neq l2 l3 irr1) as lu23 eqn:Heq;
    generalize dependent Heq.
  remember (unshift_level_neq (shift_level l2 l1) l3 irr3)
    as lu213 eqn:Heq;
    generalize dependent Heq.
  remember (@shift_level (S (S N)) l2 l1) as ls21 eqn:Heq;
    generalize dependent Heq.
  remember (@unshift_level (S (S N)) l1 l2) as lu12 eqn:Heq;
    generalize dependent Heq.
  case_levels l2 l1;
    case_levels ls21 l3;
      case_levels l2 l3;
        intros; subst; reduce_levels; try easy; try lia.
  - case_levels (l_S l1) l2; easy.
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

Lemma transpose_push_push_pop_reverse_middle {N f1 f2 f3}
      (op1 : push_op (f2 N) f1) (op2 : push_op N f2)
      (op3 : pop_op N f3) :
    forall
      (irr1 : irreducible_push_pop_ops op2 op3)
      (irr2 : irreducible_push_pop_ops op1
                (transpose_push_pop_left op2 op3 irr1))
      (irr3 : irreducible_push_pop_ops
                (transpose_pushes_right op2 op1) op3)
      (irr4 : irreducible_push_pop_ops
                (transpose_pushes_left op1 op2)
                (transpose_push_pop_left
                   (transpose_pushes_right op2 op1) op3
                   irr3)),
  transpose_pushes_left
    (transpose_pop_push_push_indices_op op3 op2
      (transpose_push_pop_right
         (transpose_push_pop_left op2 op3 irr1) op1 irr2))
    (transpose_push_pop_right op3 op2 irr1)
  = transpose_pop_push_push_indices_op op3 op1
      (transpose_push_pop_right
        (transpose_push_pop_left
           (transpose_pushes_right op2 op1) op3 irr3)
        (transpose_pushes_left op1 op2) irr4).
Proof.
  destruct op1 as [|l1|n1], op2 as [|l2|n2], op3 as [l3|n3];
    cbn in *; try easy; intros.
  - inversion_level l2; inversion_level l1.
    erewrite
      @transpose_cycle_in_cycle_in_cycle_out_reverse_middle;
      easy.
  - rewrite transpose_close_close_open_reverse_middle; easy.
Qed.

Lemma transpose_cycle_in_cycle_in_cycle_out_reverse_right {N}
      l1 l2 (l3 : level (S N)) :
  forall
    (irr1 : Squash (l2 <> l3))
    (irr2 : Squash (unshift_level_neq l2 l3 irr1 <> l1))
    (irr3 : Squash (l3 <> shift_level l2 l1)),
  @shift_level N (unshift_level_neq l3 l2 (sneq_sym irr1))
    (@unshift_level_neq N (unshift_level_neq l2 l3 irr1)
                       l1 irr2) =
  unshift_level_neq l3 (shift_level l2 l1) irr3.
Proof.
  intros; inversion_level l1.
  remember (unshift_level_neq l2 l3 irr1) as lu23 eqn:Heq;
    generalize dependent Heq.
  remember (@shift_level (S (S N)) l2 l1) as ls21 eqn:Heq;
    generalize dependent Heq.
  apply sneq_neq in irr1 as Hneq1.
  apply sneq_neq in irr2 as Hneq2.
  case_levels l2 l1;
    case_levels ls21 l3;
      case_levels l2 l3;
        intros; subst; reduce_levels; try easy; try lia.
  - case_level l1; easy.
  - case_level l1; easy.
  - case_level l1; easy.
  - apply l_nat_injective in Hneq1; contradiction.
  - case_level l1; easy.
  - apply l_nat_injective in Hneq2; cbn in Hneq2; lia.
Qed.

Lemma transpose_close_close_open_reverse_right n1 n2 n3 :
  Squash (n2 <> n3) ->
  Squash (n1 <> unshift_name n2 n3) ->
  shift_name (unshift_name n3 n2)
             (unshift_name (unshift_name n2 n3) n1)
  = unshift_name n3 (shift_name n2 n1).
Proof.
  intros Hneq1 Hneq2.
  apply sneq_neq in Hneq1.
  apply sneq_neq in Hneq2.
  generalize dependent Hneq2.
  case_names n2 n3.
  - case_names (n_S n1) n3; try easy.
    case_names n1 n2; try congruence; try easy.
    case_name n1; easy.
  - case_names n1 n3; try easy.
    case_names n1 n2; try easy.
    case_name n1; easy.
  - case_names n1 n3; try easy.
    case_names n1 n2; easy.
Qed.

Lemma transpose_push_push_pop_reverse_right {N f1 f2 f3}
      (op1 : push_op (f2 N) f1) (op2 : push_op N f2)
      (op3 : pop_op N f3) :
  forall
    (irr1 : irreducible_push_pop_ops op2 op3)
    (irr2 : irreducible_push_pop_ops op1
              (transpose_push_pop_left op2 op3 irr1))
    (irr3 : irreducible_push_pop_ops
              (transpose_pushes_right op2 op1) op3),
    transpose_pushes_right
      (transpose_push_pop_right op3 op2 irr1)
      (transpose_pop_push_push_indices_op op3 op2
        (transpose_push_pop_right
          (transpose_push_pop_left op2 op3 irr1) op1 irr2))
    = transpose_push_pop_right op3
        (transpose_pushes_right op2 op1) irr3.
Proof.
  destruct op1 as [|l1|n1], op2 as [|l2|n2], op3 as [l3|n3];
    cbn in *; try easy; intros.
  - inversion_level l2; inversion_level l1.
    erewrite
      @transpose_cycle_in_cycle_in_cycle_out_reverse_right;
      easy.
  - rewrite transpose_close_close_open_reverse_right; easy.
Qed.

Definition transpose_pop_pop_push_indices_op
           {N M O f1 f2 f3}
           (op1 : pop_op N f1)
           (op2 : pop_op M f2)
  : push_op (f1 (f2 O)) f3 -> push_op (f2 (f1 O)) f3 :=
    match op1 in pop_op _ f1, op2 in pop_op _ f2
        return push_op (f1 (f2 O)) f3 -> push_op (f2 (f1 O)) f3
    with
    | cycle_out_op l1, cycle_out_op l2 => fun op => op
    | cycle_out_op l, open_op n => fun op => op
    | open_op n, cycle_out_op l => fun op => op
    | open_op n1, open_op n2 => fun op => op
    end.

Definition transpose_push_pop_pop_indices_op
           {N M O f1 f2 f3}
           (op1 : push_op N f1)
           (op2 : pop_op M f2)
  : pop_op (f1 (f2 O)) f3 -> pop_op (f2 (f1 O)) f3 :=
    match op1 in push_op _ f1, op2 in pop_op _ f2
        return pop_op (f1 (f2 O)) f3 -> pop_op (f2 (f1 O)) f3
    with
    | weak_op, cycle_out_op l => fun op => op
    | weak_op, open_op n => fun op => op
    | cycle_in_op l1, cycle_out_op l2 => fun op => op
    | cycle_in_op l, open_op n => fun op => op
    | close_op n, cycle_out_op l => fun op => op
    | close_op n1, open_op n2 => fun op => op
    end.

Lemma transpose_cycle_in_cycle_out_cycle_out_reverse_left {N}
      (l1 : level (S N)) l2 (l3 : level N) :
  forall
  (irr1 : Squash (l1 <> l2))
  (irr2 : Squash (unshift_level_neq l2 l1 (sneq_sym irr1) <> l3))
  (irr3 : Squash (l1 <> shift_level l2 l3)),
    @shift_level N (unshift_level_neq l1 l2 irr1)
       (unshift_level_neq
          (unshift_level_neq l2 l1 (sneq_sym irr1)) l3
          irr2)
    = unshift_level_neq l1 (shift_level l2 l3) irr3.
Proof.
  intros.
  apply transpose_cycle_in_cycle_in_cycle_out_reverse_right
    with (irr4 := sneq_sym irr1).
Qed.


Lemma transpose_close_open_open_reverse_left n1 n2 n3 :
  Squash (n1 <> n2) ->
  Squash (unshift_name n2 n1 <> n3) ->
  shift_name (unshift_name n1 n2)
             (unshift_name (unshift_name n2 n1) n3)
  = unshift_name n1 (shift_name n2 n3).
Proof.
  intros.
  apply transpose_close_close_open_reverse_right;
    apply sneq_sym; easy.
Qed.

Lemma transpose_push_pop_pop_reverse_left {N f1 f2 f3}
      (op1 : push_op N f1)
      (op2 : pop_op N f2) (op3 : pop_op (f2 N) f3) :
  forall (irr1 : irreducible_push_pop_ops op1 op2)
         (irr2 : irreducible_push_pop_ops
                   (transpose_push_pop_right op2 op1 irr1) op3)
         (irr3 : irreducible_push_pop_ops op1
                   (transpose_pops_left op2 op3)),
    transpose_pops_left
      (transpose_push_pop_left op1 op2 irr1)
      (transpose_push_pop_pop_indices_op op1 op2
        (transpose_push_pop_left
          (transpose_push_pop_right op2 op1 irr1) op3 irr2))
    = transpose_push_pop_left op1
        (transpose_pops_left op2 op3) irr3.
Proof.
  destruct op1 as [|l1|n1], op2 as [l2|n2], op3 as [l3|n3];
    cbn in *; try easy; intros.
  - inversion_level l1; inversion_level l3.
    erewrite @transpose_cycle_in_cycle_out_cycle_out_reverse_left;
      easy.
  - rewrite transpose_close_open_open_reverse_left; easy.
Qed.

Lemma transpose_cycle_in_cycle_out_cycle_out_reverse_middle {N}
      (l1 : level (S N)) (l2 : level (S N)) (l3 : level N) :
  forall
  (irr1 : Squash (l1 <> shift_level l2 l3))
  (irr2 : Squash (unshift_level_neq (shift_level l2 l3) l1
            (sneq_sym irr1) <> @unshift_level (S N) l3 l2))
  (irr3 : Squash (l1 <> l2))
  (irr4 : Squash (unshift_level_neq l2 l1 (sneq_sym irr3) <> l3)),
    @unshift_level_neq N
       (unshift_level_neq (shift_level l2 l3) l1 (sneq_sym irr1))
       (@unshift_level (S N) l3 l2) irr2
    = unshift_level
        (unshift_level_neq
           (unshift_level_neq l2 l1 (sneq_sym irr3)) l3 irr4)
        (unshift_level_neq l1 l2 irr3).
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

Lemma transpose_push_pop_pop_reverse_middle {N f1 f2 f3}
      (op1 : push_op N f1)
      (op2 : pop_op N f2) (op3 : pop_op (f2 N) f3) :
  forall (irr1 : irreducible_push_pop_ops op1
                   (transpose_pops_left op2 op3))
         (irr2 : irreducible_push_pop_ops
                   (transpose_push_pop_right
                      (transpose_pops_left op2 op3) op1 irr1)
                   (transpose_pops_right op3 op2))
         (irr3 : irreducible_push_pop_ops op1 op2)
         (irr4 : irreducible_push_pop_ops
                   (transpose_push_pop_right op2 op1 irr3) op3),
  transpose_push_pop_pop_indices_op op1 op3
    (transpose_push_pop_left
       (transpose_push_pop_right
          (transpose_pops_left op2 op3) op1 irr1)
       (transpose_pops_right op3 op2) irr2)
  = transpose_pops_right
      (transpose_push_pop_pop_indices_op op1 op2
        (transpose_push_pop_left
           (transpose_push_pop_right op2 op1 irr3) op3 irr4))
      (transpose_push_pop_left op1 op2 irr3).
Proof.
  destruct op1 as [|l1|n1], op2 as [l2|n2], op3 as [l3|n3];
    cbn in *; try easy; intros.
  - inversion_level l1; inversion_level l3.
    erewrite transpose_cycle_in_cycle_out_cycle_out_reverse_middle;
      easy.
  - rewrite transpose_close_open_open_reverse_middle; easy.
Qed.

Lemma transpose_cycle_in_cycle_out_cycle_out_reverse_right {N}
      l1 l2 (l3 : level N) :
  forall (irr1 : Squash (l1 <> @shift_level (S N) l2 l3))
         (irr2 : Squash
                   (unshift_level_neq
                      (shift_level l2 l3) l1 (sneq_sym irr1)
                    <> @unshift_level (S N) l3 l2))
         (irr3 : Squash (l1 <> l2))
         (irr4 : Squash
                   (unshift_level_neq l2 l1 (sneq_sym irr3) <> l3)),
  @unshift_level_neq N (@unshift_level (S N) l3 l2)
    (unshift_level_neq (shift_level l2 l3) l1 (sneq_sym irr1))
    (sneq_sym irr2)
  = unshift_level_neq l3
      (unshift_level_neq l2 l1 (sneq_sym irr3))
      (sneq_sym irr4).
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

Lemma transpose_push_pop_pop_reverse_right {N f1 f2 f3}
      (op1 : push_op N f1)
      (op2 : pop_op N f2) (op3 : pop_op (f2 N) f3) :
  forall (irr1 : irreducible_push_pop_ops op1
                   (transpose_pops_left op2 op3))
         (irr2 : irreducible_push_pop_ops
                   (transpose_push_pop_right
                      (transpose_pops_left op2 op3) op1 irr1)
                   (transpose_pops_right op3 op2))
         (irr3 : irreducible_push_pop_ops op1 op2)
         (irr4 : irreducible_push_pop_ops
                   (transpose_push_pop_right op2 op1 irr3) op3),
    transpose_push_pop_right
      (transpose_pops_right op3 op2)
      (transpose_push_pop_right
        (transpose_pops_left op2 op3) op1 irr1)
      irr2
    = transpose_pop_pop_push_indices_op op3 op2
        (transpose_push_pop_right op3
          (transpose_push_pop_right op2 op1 irr3) irr4).
Proof.
  destruct op1 as [|l1|n1], op2 as [l2|n2], op3 as [l3|n3];
    cbn in *; try easy; intros.
  - inversion_level l1; inversion_level l3.
    erewrite
      @transpose_cycle_in_cycle_out_cycle_out_reverse_right;
      easy.
  - rewrite transpose_close_open_open_reverse_right; easy.
Qed.
