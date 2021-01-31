Require Import Label PeanoNat Psatz Ring Compare_dec StrictProp.
Require Import Var VarEquations RawRenaming RawRenamingEquations.

Fixpoint apply_raw_renaming_unmatched_var r v {struct r} :=
  match r with
  | raw_renaming_id => v
  | raw_renaming_extend vl r vr =>
    shift_var
      vl (apply_raw_renaming_unmatched_var r (unshift_var vr v))
  end.

Definition is_normal_raw_renaming_extension vl r vr :=
  negb (is_shifting_var
          vl (apply_raw_renaming_unmatched_var r vr)).

Definition is_normal_or_under_raw_renaming_extension
           vu vl r vr :=
  orb (is_unshifting_var vr vu)
      (is_normal_raw_renaming_extension vl r vr).

Fixpoint is_all_normal_or_under_raw_renaming vu r :=
  match r with
  | raw_renaming_id => true
  | raw_renaming_extend vl r' vr =>
    andb
      (is_normal_or_under_raw_renaming_extension vu vl r' vr)
      (is_all_normal_or_under_raw_renaming
         (unshift_var vr vu) r')
  end.

Definition is_less_equal_raw_renaming_var vu r :=
  match r with
  | raw_renaming_id => true
  | raw_renaming_extend _ _ v' => is_less_equal_var vu v'
  end.

Fixpoint is_all_ordered_raw_renaming r :=
  match r with
  | raw_renaming_id => true
  | raw_renaming_extend vl r' vr =>
    andb
      (is_less_equal_raw_renaming_var vr r')
      (is_all_ordered_raw_renaming r')
  end.

Definition is_normalized_raw_renaming vu r :=
  andb
    (is_all_normal_or_under_raw_renaming vu r)
    (is_all_ordered_raw_renaming r).

Lemma is_all_normal_normalized vu r :
  is_normalized_raw_renaming vu r = true ->
  is_all_normal_or_under_raw_renaming vu r = true.
Proof.
  unfold is_normalized_raw_renaming.
  rewrite Bool.andb_true_iff; easy.
Qed.

Lemma is_all_ordered_normalized vu r :
  is_normalized_raw_renaming vu r = true ->
  is_all_ordered_raw_renaming r = true.
Proof.
  unfold is_normalized_raw_renaming.
  rewrite Bool.andb_true_iff; easy.
Qed.

Lemma is_normalized_raw_renaming_extend vu vl r vr :
  is_normalized_raw_renaming vu (raw_renaming_extend vl r vr)
  = andb
      (is_normalized_raw_renaming (unshift_var vr vu) r)
      (andb
         (is_normal_or_under_raw_renaming_extension
            vu vl r vr)
         (is_less_equal_raw_renaming_var vr r)).
Proof.
  unfold is_normalized_raw_renaming; cbn; ring.
Qed.

Lemma is_normalized_raw_renaming_from_extend vu vl r vr :
  is_normalized_raw_renaming
    vu (raw_renaming_extend vl r vr) = true ->
  is_normalized_raw_renaming (unshift_var vr vu) r = true.
Proof.
  rewrite is_normalized_raw_renaming_extend.
  rewrite! Bool.andb_true_iff.
  easy.
Qed.

Lemma is_all_normal_raw_renaming_normal_extension vu vl r vr :
  is_all_normal_or_under_raw_renaming vu
    (raw_renaming_extend vl r vr) = true ->
  is_normal_or_under_raw_renaming_extension vu vl r vr = true.
Proof. cbn; rewrite Bool.andb_true_iff; easy. Qed.

Lemma apply_normal_raw_renaming_unmatched_var vu r v :
  is_all_normal_or_under_raw_renaming vu r = true ->
  is_unshifting_var v vu = false ->
  (apply_raw_renaming_unmatched_var r v
   = apply_raw_renaming_var r v)
  \/ ((apply_raw_renaming_unmatched_var r v
       = apply_raw_renaming_unmatched_var r (succ_var v))
      /\ (is_shifting_var
            (apply_raw_renaming_var r v)
            (apply_raw_renaming_unmatched_var r v)
          = false)).
Proof.
  generalize dependent v.
  generalize dependent vu.
  induction r as [|vl r IHr vr]; cbn; intros vu v Heq Hu.
  - left; easy.
  - rewrite Bool.andb_true_iff in Heq; destruct Heq as [Heq1 Heq2].
    case_vars_eq v vr.
    + right; split; try easy; subst.
      unfold is_normal_or_under_raw_renaming_extension in Heq1.
      rewrite Bool.orb_true_iff in Heq1.
      destruct Heq1 as [?|Heq1]; try congruence.
      unfold is_normal_raw_renaming_extension in Heq1.
      rewrite Bool.negb_true_iff in Heq1.
      rewrite is_shifting_false_shift; easy.
    + apply is_unshifting_var_unshift_var
        with (v3 := vr) in Hu.
      destruct
        (IHr (unshift_var vr vu) (unshift_var vr v) Heq2 Hu)
        as [Heq3|[Heq3 Heq4]]; [left|right;split].
      * rewrite Heq3; easy.
      * rewrite Heq3.
        rewrite succ_var_unshift_var_neq by congruence.
        easy.
      * rewrite is_shifting_var_shift_var.
        easy.
Qed.

Fixpoint raw_renaming_matched_limit r lo :=
  match r with
  | raw_renaming_id => 0
  | raw_renaming_extend _ r vr =>
    if label_opt_eqb (v_label_opt vr) lo then
      S (max (raw_renaming_matched_limit r lo) (v_nat vr))
    else
      raw_renaming_matched_limit r lo
  end.

Lemma unmatched_raw_renaming_matched_limit r v :
  v_nat v >= raw_renaming_matched_limit r (v_label_opt v) ->
  apply_raw_renaming_var r v
  = apply_raw_renaming_unmatched_var r v.
Proof.
  rewrite eta_expand_var with v.
  generalize dependent (v_nat v).
  induction r as [|vl r IHr vr]; cbn; intros n; try easy.
  case_vars_eq (mk_var (v_label_opt v) n) vr; intros Hlt.
  - rewrite label_opt_eqb_reflexive in Hlt; lia.
  - unfold label_opt_eqb in Hlt; destruct label_opt_dec;
      reduce_vars.
    + rewrite eta_expand_var
        with (v := pred_var (mk_var (v_label_opt v) n));
        reduce_vars_beta.
      rewrite IHr; try easy; reduce_vars_beta; lia.
    + rewrite IHr; reduce_vars_beta; easy.
Qed.

Lemma normal_raw_renaming_ind vu r v1 :
  forall (P : var -> Prop),
    is_all_normal_or_under_raw_renaming vu r = true ->
    is_unshifting_var v1 vu = false ->
    (forall v2,
        is_unshifting_var v2 vu = false ->
        (apply_raw_renaming_unmatched_var r v2
         = apply_raw_renaming_var r v2) -> P v2) ->
    (forall v3,
        is_unshifting_var v3 vu = false ->
        (apply_raw_renaming_unmatched_var r v3
         = apply_raw_renaming_unmatched_var r (succ_var v3)) ->
        (is_shifting_var
           (apply_raw_renaming_var r v3)
           (apply_raw_renaming_unmatched_var r v3)
         = false) ->
        P (succ_var v3) ->
        P v3) ->
    P v1.
Proof.
  intros P Heq1 Hu Hb Hi.
  remember
    (Nat.sub (raw_renaming_matched_limit r (v_label_opt v1))
             (v_nat v1)) as m eqn:Heq2.
  generalize dependent v1.
  induction m; intros v1 Hu Heq2.
  - apply Hb; try easy; symmetry.
    apply unmatched_raw_renaming_matched_limit; lia.
  - destruct (apply_normal_raw_renaming_unmatched_var vu r v1)
      as [Heq3|[Heq3 Heq4]]; try easy.
    + apply Hb; easy.
    + apply Hi; try easy.
      apply is_unshifting_succ_var_false in Hu.
      apply IHm; reduce_vars; try easy; lia.
Qed.

Lemma shifting_apply_raw_renaming_unmatched_var r v1 v2 :
  is_shifting_var v1 v2 = true ->
  is_shifting_var
    (apply_raw_renaming_unmatched_var r v1)
    (apply_raw_renaming_unmatched_var r v2) = true.
Proof.
  generalize dependent v1.
  generalize dependent v2.
  induction r as [|vl r IHr vr];
    cbn; intros v2 v1 Heq; try easy.
  rewrite is_shifting_var_shift_var.
  apply IHr.
  apply is_shifting_var_unshift_var; easy.
Qed.

Lemma shifting_unmatched_var vu r v1 v2 :
  is_all_normal_or_under_raw_renaming vu r = true ->
  is_unshifting_var v1 vu = false ->
  apply_raw_renaming_unmatched_var r v1
  = apply_raw_renaming_var r v1 ->
  is_shifting_var v1 v2 = true ->
  (apply_raw_renaming_var r v1
   = apply_raw_renaming_var r v2)
  \/ (is_shifting_var
       (apply_raw_renaming_var r v2)
       (apply_raw_renaming_var r v1) = false).
Proof.
  intros Heq1 Hu1 Heq2 Heq3.
  apply is_unshifting_false_is_shifting_var_transitive
    with (v3 := v2) in Hu1 as Hu2; try easy.
  apply (shifting_apply_raw_renaming_unmatched_var r) in Heq3.
  destruct (apply_normal_raw_renaming_unmatched_var vu r v2)
    as [Heq4|[Heq4 Heq5]]; try easy.
  - rewrite <- Heq2, <- Heq4.
    destruct (is_shifting_var
                (apply_raw_renaming_unmatched_var r v2)
                (apply_raw_renaming_unmatched_var r v1)) eqn:Heq5.
    + left; apply is_shifting_var_antisymmetric; easy.
    + right; easy.
  - right; rewrite <- Heq2.
    destruct (is_shifting_var
                (apply_raw_renaming_var r v2)
                (apply_raw_renaming_unmatched_var r v1)) eqn:Heq6;
      try easy.
    apply is_shifting_var_transitive
      with (v1 := apply_raw_renaming_var r v2) in Heq3; try easy.
    congruence.
Qed.

Lemma shifting_inv_matched_var vu r v1 v2 :
  is_all_normal_or_under_raw_renaming vu r = true ->
  is_unshifting_var v1 vu = false ->
  apply_raw_renaming_unmatched_var r v1
  = apply_raw_renaming_var r v2 ->
  is_shifting_var v1 v2 = true.
Proof.
  intros Heq1 Hu.
  apply (normal_raw_renaming_ind vu r v1); try easy.
  - intros v3 Hu2 Heq2 Heq3.
    rewrite Heq2 in Heq3.
    apply apply_raw_renaming_var_injective in Heq3 as <-.
    apply is_shifting_var_reflexive.
  - intros v3 Hu2 Heq2 Heq3 Heq4 Heq5.
    rewrite Heq2 in Heq5.
    specialize (Heq4 Heq5).
    apply is_shifting_var_transitive with (succ_var v3); try easy.
    apply is_shifting_succ_var.
Qed.

Lemma indistinct_apply_raw_renaming_unmatched_var r v :
  v_label_opt (apply_raw_renaming_unmatched_var r v)
  = v_label_opt v.
Proof.
  generalize dependent v.
  induction r as [|vl r IHr vr]; intros v;
    cbn; try easy; reduce_vars_beta.
  rewrite IHr; reduce_vars_beta.
  easy.
Qed.

Lemma equivalent_matched_raw_renaming vu r1 r2 v :
  is_all_normal_or_under_raw_renaming vu r1 = true ->
  is_all_normal_or_under_raw_renaming vu r2 = true ->
  is_unshifting_var v vu = false ->
  (r1 =rr= r2) ->
  (apply_raw_renaming_unmatched_var r1 v
   = apply_raw_renaming_var r1 v) ->
  (apply_raw_renaming_unmatched_var r2 v
   = apply_raw_renaming_var r2 v).
Proof.
  intros Heq1 Heq2 Hu Heq3 Heq4.
  destruct (apply_normal_raw_renaming_unmatched_var vu r2 v)
    as [Heq5|[Heq5 Heq6]]; try easy.
  assert (is_shifting_var v
            (apply_raw_renaming_var (inverse_raw_renaming r2)
               (apply_raw_renaming_unmatched_var r2 v)) = true)
    as Heq7
    by (apply shifting_inv_matched_var with (vu := vu) (r := r2);
          try rewrite apply_inverse_raw_renaming_right_v; easy).
  apply shifting_unmatched_var
    with (vu := vu) (r := r1) in Heq7; try easy.
  destruct Heq7 as [Heq7|Heq7].
  - rewrite (Heq3 (apply_raw_renaming_var _ _)) in Heq7.
    rewrite apply_inverse_raw_renaming_right_v in Heq7.
    congruence.
  - rewrite (Heq3 (apply_raw_renaming_var _ _)) in Heq7.
    rewrite apply_inverse_raw_renaming_right_v in Heq7.
    apply is_shifting_var_total_indistinct in Heq7;
      try congruence.
    rewrite <- Heq4.
    rewrite! indistinct_apply_raw_renaming_unmatched_var.
    easy.
Qed.

Lemma equivalent_apply_raw_renaming_unmatched_var vu r1 r2 :
  is_all_normal_or_under_raw_renaming vu r1 = true ->
  is_all_normal_or_under_raw_renaming vu r2 = true ->
  (r1 =rr= r2) ->
  forall v,
    is_unshifting_var v vu = false ->
    apply_raw_renaming_unmatched_var r1 v
    = apply_raw_renaming_unmatched_var r2 v.
Proof.
  intros Heq1 Heq2 Heq3 v Hu.
  apply (normal_raw_renaming_ind vu r1 v); try easy.
  - intros v2 Hu2 Heq4.
    destruct (apply_normal_raw_renaming_unmatched_var vu r2 v2)
      as [Heq5|[Heq5 Heq6]]; try easy.
    + rewrite Heq4, Heq5, Heq3; easy.
    + apply equivalent_matched_raw_renaming
        with (vu := vu) (r2 := r2) in Heq4; try easy.
      rewrite Heq4 in Heq6.
      pose is_shifting_var_reflexive.
      congruence.
  - intros v2 Hu2 Heq4 Heq5 Heq6.
    destruct (apply_normal_raw_renaming_unmatched_var vu r2 v2)
      as [Heq7|[Heq7 Heq8]]; try easy.
    + apply equivalent_matched_raw_renaming
        with (vu := vu) (r2 := r1) in Heq7; try easy.
      rewrite Heq7 in Heq5.
      pose is_shifting_var_reflexive.
      congruence.
    + rewrite Heq4, Heq7.
      apply Heq6.
Qed.

Definition is_less_than_raw_renaming_var v r :=
  match r with
  | raw_renaming_id => true
  | raw_renaming_extend _ _ v' => is_less_than_var v v'
  end.

Lemma is_less_than_raw_renaming_var_extend v v' r :
  is_less_equal_raw_renaming_var v' r = true ->
  is_less_than_var v v' = true ->
  is_less_than_raw_renaming_var v r = true.
Proof.
  intros Heq1 Heq2.
  destruct r as [|vl' r vr']; cbn in *;try easy.
  apply is_less_than_less_equal_var_transitive with v'; easy.
Qed.

Lemma apply_normalized_raw_renaming_unmatched_var r v :
  is_all_ordered_raw_renaming r = true ->
  is_less_than_raw_renaming_var v r = true ->
  apply_raw_renaming_var r v
  = apply_raw_renaming_unmatched_var r v.
Proof.
  intros Heq1 Heq2.
  induction r as [|vl' r IHr vr']; cbn in *; try easy.
  rewrite Bool.andb_true_iff in Heq1; destruct Heq1.
  case_vars vr' v; rewrite IHr; try easy;
    apply is_less_than_raw_renaming_var_extend with vr';
      reduce_vars; easy.
Qed.

Lemma equivalence_from_extend vl vr r1 r2 :
  raw_renaming_extend vl r1 vr
  =rr= raw_renaming_extend vl r2 vr ->
  r1 =rr= r2.
Proof.
  intros Heq1 v.
  specialize (Heq1 (shift_var vr v)).
  assert (shift_var vr v <> vr)
    by apply irreducible_transposed_1.
  reduce_vars.
  rewrite reducible_transposed_2 with (v1 := v) in Heq1
    by easy.
  apply reducible_transposed_2 in Heq1.
  rewrite reducible_transposed_2
    with (v1 := apply_raw_renaming_var r2 v) in Heq1
    by easy.
  congruence.
Qed.

Lemma is_normalized_less_than_not_equivalent
      vu vl1 r1 vr1 r2 :
  is_normalized_raw_renaming vu
    (raw_renaming_extend vl1 r1 vr1) = true ->
  is_normalized_raw_renaming vu r2 = true ->
  is_unshifting_var vr1 vu = false ->
  is_less_than_raw_renaming_var vr1 r2 = true ->
  not (raw_renaming_extend vl1 r1 vr1 =rr= r2).
Proof.
  intros Heq1 Heq2 Hu Heq3 Heq4.
  apply is_all_ordered_normalized in Heq1 as Heq5.
  apply is_all_ordered_normalized in Heq2 as Heq6.
  apply is_all_normal_normalized in Heq1 as Heq7.
  apply is_all_normal_normalized in Heq2 as Heq8.
  apply is_unshifting_succ_var_false in Hu as Hu2.
  specialize (Heq4 vr1) as Heq9.
  rewrite apply_normalized_raw_renaming_unmatched_var
    with (r := r2) in Heq9 by easy.
  apply equivalent_apply_raw_renaming_unmatched_var
    with (vu := vu) (v := succ_var vr1) in Heq4; try easy.
  apply is_all_normal_raw_renaming_normal_extension
    in Heq7 as Heq10.
  unfold is_normal_or_under_raw_renaming_extension,
    is_normal_raw_renaming_extension in Heq10;
    rewrite Bool.orb_true_iff, Bool.negb_true_iff in Heq10.
  destruct Heq10 as [?|Heq10]; try congruence.
  reduce_vars.
  rewrite is_shifting_false_shift in Heq4 by easy.
  rewrite Heq9 in Heq10.
  rewrite Heq4 in Heq10.
  contradict Heq10.
  rewrite Bool.not_false_iff_true.
  apply shifting_apply_raw_renaming_unmatched_var.
  apply is_shifting_succ_var.
Qed.

Fixpoint is_right_complete_under v r :=
  match r with
  | raw_renaming_id => Nat.eqb (v_nat v) 0
  | raw_renaming_extend vl r' vr =>
    is_right_complete_under (unshift_var vr v) r'
  end.

Fixpoint is_left_complete_under v r :=
  match r with
  | raw_renaming_id => Nat.eqb (v_nat v) 0
  | raw_renaming_extend vl r' vr =>
    is_left_complete_under (unshift_var vl v) r'
  end.

Lemma is_right_complete_ordered_not_less_than vu v r :
  is_right_complete_under vu r = true ->
  is_all_ordered_raw_renaming r = true ->
  is_unshifting_var v vu = true ->
  is_less_than_raw_renaming_var v r = true ->
  False.
Proof.
  generalize dependent vu.
  generalize dependent v.
  induction r as [|vl r IHr vr]; cbn; intros v vu Heq1 Heq2 Hu Heq3.
  - rewrite Nat.eqb_eq in Heq1.
    rewrite is_unshifting_zero_var_false in Hu by easy.
    easy.
  - rewrite Bool.andb_true_iff in Heq2;
      destruct Heq2 as [Heq4 Heq2].
    apply is_less_than_raw_renaming_var_extend
      with (v := v) in Heq4; try easy.
    apply IHr
      with (vu := unshift_var vr vu) (v := v); try easy.
    apply is_unshifting_var_unshift_var_true
      with (v3 := vr) in Hu.
    * rewrite is_unshifting_false_shift in Hu; try easy.
      apply is_less_than_not_unshifting; easy.
    * contradict Heq3; rewrite Bool.not_true_iff_false; subst.
      apply is_less_than_var_irreflexive.
Qed.

Lemma is_normalized_and_complete_less_than_not_equivalent
      vu vl1 r1 vr1 r2 :
  is_normalized_raw_renaming vu
    (raw_renaming_extend vl1 r1 vr1) = true ->
  is_normalized_raw_renaming vu r2 = true ->
  is_right_complete_under vu r2 = true ->
  is_less_than_raw_renaming_var vr1 r2 = true ->
  not (raw_renaming_extend vl1 r1 vr1 =rr= r2).
Proof.
  intros Heq1 Heq2 Heq3 Heq4.
  destruct (is_unshifting_var vr1 vu) eqn:Heq5.
  - exfalso.
    apply is_right_complete_ordered_not_less_than
      with (vu := vu) (r := r2) (v := vr1); try easy.
    apply is_all_ordered_normalized with (vu := vu); easy.
  - apply is_normalized_less_than_not_equivalent
      with (vu := vu); try easy.
Qed.

Lemma is_normalized_equivalence_equal vu r1 r2 :
  is_normalized_raw_renaming vu r1 = true ->
  is_normalized_raw_renaming vu r2 = true ->
  is_right_complete_under vu r1 = true ->
  is_right_complete_under vu r2 = true ->
  r1 =rr= r2 ->
  r1 = r2.
Proof.
  generalize dependent vu.
  generalize dependent r2.
  induction r1 as [|vl1 r1 IHr vr1];
    intros r2 vu Heq1 Heq2 Heq3 Heq4 Heq5;
    destruct r2 as [|vl2 r2 vr2]; try easy.
  - absurd (raw_renaming_extend vl2 r2 vr2 =rr= raw_renaming_id);
      try easy.
    apply is_normalized_and_complete_less_than_not_equivalent
      with (vu := vu); easy.
  - absurd (raw_renaming_extend vl1 r1 vr1 =rr= raw_renaming_id);
      try easy.
    apply is_normalized_and_complete_less_than_not_equivalent
      with (vu := vu); easy.
  - destruct (is_less_than_var vr1 vr2) eqn:Heq6.
    + absurd (raw_renaming_extend vl1 r1 vr1
              =rr= raw_renaming_extend vl2 r2 vr2); try easy.
      apply is_normalized_and_complete_less_than_not_equivalent
        with (vu := vu); easy.
    + destruct (is_less_than_var vr2 vr1) eqn:Heq7.
      * absurd (raw_renaming_extend vl2 r2 vr2
              =rr= raw_renaming_extend vl1 r1 vr1); try easy.
        apply is_normalized_and_complete_less_than_not_equivalent
          with (vu := vu); easy.
      * apply (is_less_than_var_total _ _ Heq6) in Heq7 as <-.
        specialize (Heq5 vr1) as Heq8; reduce_vars; subst.
        apply is_normalized_raw_renaming_from_extend in Heq1.
        apply is_normalized_raw_renaming_from_extend in Heq2.
        rewrite IHr
          with (vu := unshift_var vr1 vu) (r2 := r2); try easy.
        apply equivalence_from_extend with (vl := vl2) (vr := vr1).
        easy.
Qed.

Fixpoint is_interesting_raw_renaming_extension vl r vr :=
  match r with
  | raw_renaming_id => negb (var_eqb vl vr)
  | raw_renaming_extend vl' r vr' =>
      is_interesting_raw_renaming_extension
         (unshift_var vl' vl) r (unshift_var vr' vr)
  end.

Fixpoint is_needed_raw_renaming_extension vl r :=
  match r with
  | raw_renaming_id => false
  | raw_renaming_extend vl' r vr' =>
    (orb
       (is_shifting_var vl vl')
       (is_needed_raw_renaming_extension (unshift_var vl' vl) r))
  end.

Definition is_needed_or_interesting_raw_renaming_extension
           vl r vr :=
  (orb
     (is_needed_raw_renaming_extension vl r)
     (is_interesting_raw_renaming_extension vl r vr)).
Arguments is_needed_or_interesting_raw_renaming_extension vl r vr /.

Fixpoint is_all_needed_or_interesting_raw_renaming r :=
  match r with
  | raw_renaming_id => true
  | raw_renaming_extend vl r' vr =>
    andb
      (is_needed_or_interesting_raw_renaming_extension vl r' vr)
      (is_all_needed_or_interesting_raw_renaming r')
  end.

Lemma is_all_needed_or_interesting_raw_renaming_from_extend
      {vl r vr} :
  is_all_needed_or_interesting_raw_renaming
    (raw_renaming_extend vl r vr) = true ->
  is_all_needed_or_interesting_raw_renaming r = true.
Proof.
  destruct r; cbn;
    try rewrite Bool.andb_true_iff; easy.
Qed.

Fixpoint raw_renaming_extend_boring vl r vr :=
  match r with
  | raw_renaming_id =>
      if (var_eqb vl vr) then Some r
      else None
  | raw_renaming_extend vl' r vr' =>
    match is_shifting_var vl vl' with
    | true => None
    | false =>
      match raw_renaming_extend_boring
              (unshift_var vl' vl) r (unshift_var vr' vr)
      with
      | None => None
      | Some r =>
        Some (raw_renaming_extend
                (shift_var vl vl') r (shift_var vr vr'))
      end
    end
  end.

Lemma is_needed_or_interesting_raw_renaming_extend_boring_none
      vl r vr :
  raw_renaming_extend_boring vl r vr = None ->
  is_needed_or_interesting_raw_renaming_extension vl r vr = true.
Proof.
  generalize dependent vl.
  generalize dependent vr.
  induction r as [|vl' r IHr vr']; cbn; intros vr vl Heq.
  - destruct var_eqb; easy.
  - destruct is_shifting_var; try easy.
    apply IHr.
    destruct (raw_renaming_extend_boring
                (unshift_var vl' vl) r (unshift_var vr' vr));
      easy.
Qed.

Lemma is_interesting_raw_renaming_extend_boring_some_ind r1 :
  forall r2 vl1 vl2 vr1 vr2,
  is_interesting_raw_renaming_extension vl1 r1 vr1 = true ->
  raw_renaming_extend_boring
    (unshift_var vl1 vl2) r1 (unshift_var vr1 vr2) = Some r2 ->
  is_interesting_raw_renaming_extension
    (shift_var vl2 vl1) r2 (shift_var vr2 vr1) = true.
Proof.
  induction r1 as [|vl3 r1 IHr1 vr3]; cbn; intros * Heq1 Heq2.
  - case_vars_eq vl1 vr1.
    case_vars_eq
      (unshift_var vl1 vl2) (unshift_var vr1 vr2).
    injection Heq2 as <-; cbn.
    apply Bool.negb_true_iff, var_eqb_false.
    apply transpose_irreducible_pop_push_nested; try easy.
  - destruct (is_shifting_var (unshift_var vl1 vl2) vl3) eqn:Heq3;
      try easy.
    destruct raw_renaming_extend_boring eqn:Heq4; try easy.
    injection Heq2 as <-; cbn.
    rewrite <- transpose_pops_reverse_middle.
    rewrite transpose_pushes_reverse_middle.
    apply IHr1; try easy.
    rewrite transpose_pops_reverse_right.
    rewrite transpose_pushes_reverse_left.
    easy.
Qed.

Lemma is_needed_raw_renaming_extend_boring_some_ind r1 :
  forall r2 vl1 vl2 vr,
  is_needed_raw_renaming_extension vl1 r1 = true ->
  raw_renaming_extend_boring
    (unshift_var vl1 vl2) r1 vr = Some r2 ->
  is_needed_raw_renaming_extension (shift_var vl2 vl1) r2 = true.
Proof.
  induction r1 as [|vl3 r1 IHr1 vr3];
    cbn; intros * Heq1 Heq2; try easy.
  destruct (is_shifting_var (unshift_var vl1 vl2) vl3) eqn:Heq3;
    try easy.
  destruct raw_renaming_extend_boring eqn:Heq4; try easy.
  injection Heq2 as <-; cbn.
  rewrite Bool.orb_true_iff in *.
  destruct Heq1 as [Heq1|Heq1]; [left|right].
  - rewrite <- transposed_is_shifting_var.
    rewrite transpose_pushes_squared_left; easy.
  - rewrite <- transpose_pops_reverse_middle.
    apply IHr1 with (vr := unshift_var vr3 vr); try easy.
    rewrite transpose_pops_reverse_right.
    easy.
Qed.

Lemma is_needed_or_interesting_raw_renaming_extend_boring_some
      vl r1 vr r2 :
  is_all_needed_or_interesting_raw_renaming r1 = true ->
  raw_renaming_extend_boring vl r1 vr = Some r2 ->
  is_all_needed_or_interesting_raw_renaming r2 = true.
Proof.
  generalize dependent vl.
  generalize dependent vr.
  generalize dependent r2.
  induction r1 as [|vl2 r1 ? vr2]; cbn;
    intros r2 vr vl Heq1 Heq2.
  - destruct var_eqb; try easy.
    injection Heq2 as <-; easy.
  - destruct is_shifting_var; try easy.
    destruct raw_renaming_extend_boring eqn:Heq3; try easy.
    injection Heq2 as <-; cbn.
    rewrite! Bool.andb_true_iff, Bool.orb_true_iff in *.
    destruct Heq1 as [Heq1 Heq4]; split; [destruct Heq1|].
    + left.
      apply is_needed_raw_renaming_extend_boring_some_ind
        with (r1 := r1) (vr := unshift_var vr2 vr); easy.
    + right.
      apply is_interesting_raw_renaming_extend_boring_some_ind
        with (r1 := r1); easy.
    + apply IHr1
        with (vl := unshift_var vl2 vl) (vr := unshift_var vr2 vr);
        easy.
Qed.

Definition interesting_raw_renaming_extend vl r vr :=
  match raw_renaming_extend_boring vl r vr with
  | Some r => r
  | None => raw_renaming_extend vl r vr
  end.

Lemma is_all_needed_or_interesting_raw_renaming_extend vl r vr :
  is_all_needed_or_interesting_raw_renaming r = true ->
  is_all_needed_or_interesting_raw_renaming
    (interesting_raw_renaming_extend vl r vr) = true.
Proof.
  intro Heq1; unfold interesting_raw_renaming_extend.
  destruct (raw_renaming_extend_boring vl r vr) eqn:Heq2; cbn.
  - apply is_needed_or_interesting_raw_renaming_extend_boring_some
      in Heq2; easy.
  - rewrite Bool.andb_true_iff; split; try easy.
    apply is_needed_or_interesting_raw_renaming_extend_boring_none;
      easy.
Qed.

Lemma is_interesting_interesting_raw_renaming_extend_ind r1 :
  forall vl1 vr1 r2 vl2 vr2,
    raw_renaming_extend_boring vl1 r1 vr1 = Some r2 ->
    is_interesting_raw_renaming_extension
           (unshift_var vl1 vl2) r1 (unshift_var vr1 vr2) = true ->
    is_interesting_raw_renaming_extension vl2 r2 vr2 = true.
Proof.
  induction r1 as [|vl3 r1 IHr1 vr3]; cbn; intros * Heq1 Heq2.
  - case_vars_eq vl1 vr1.
    injection Heq1 as <-; cbn.
    case_vars_eq (unshift_var vl1 vl2) (unshift_var vr1 vr2);
      easy.
  - destruct (is_shifting_var vl1 vl3); try easy.
    destruct raw_renaming_extend_boring eqn:Heq4; try easy.
    injection Heq1 as <-; cbn.
    apply IHr1 with (vl2 := unshift_var (shift_var vl1 vl3) vl2)
        (vr2 := unshift_var (shift_var vr1 vr3) vr2)
        in Heq4; try easy.
    rewrite transpose_pops_reverse_right.
    rewrite transpose_pushes_reverse_left.
    easy.
Qed.

Lemma is_interesting_interesting_raw_renaming_extend
      vl1 r vr1 vl2 vr2 :
  is_interesting_raw_renaming_extension
    vl2 (raw_renaming_extend vl1 r vr1) vr2 = true ->
  is_interesting_raw_renaming_extension
    vl2 (interesting_raw_renaming_extend vl1 r vr1) vr2 = true.
Proof.
  unfold interesting_raw_renaming_extend.
  destruct raw_renaming_extend_boring eqn:Heq1;
    cbn; intros Heq2; try easy.
  apply is_interesting_interesting_raw_renaming_extend_ind
    with (r1 := r) (vl1 := vl1) (vr1 := vr1); easy.
Qed.

Lemma is_all_ordered_raw_renaming_from_extend {vl r vr} :
  is_all_ordered_raw_renaming
    (raw_renaming_extend vl r vr) = true ->
  is_all_ordered_raw_renaming r = true.
Proof.
  destruct r; cbn;
    try rewrite Bool.andb_true_iff; easy.
Qed.

(* TODO : move to var equations *)
Lemma succ_var_monotonic v1 v2 :
  is_shifting_var (succ_var v1) (succ_var v2)
  = is_shifting_var v1 v2.
Proof.
  case_vars v1 v2; easy.
Qed.

(* TODO : move to var equations *)
Lemma is_less_equal_shift v1 v2 v3 :
  is_less_equal_var
    (shift_var v3 v1) (shift_var (unshift_var v1 v3) v2)
  = is_less_equal_var v1 v2.
Proof.
  case_vars v1 v3;
    case_vars (unshift_var v1 v3) v2; try easy.
  apply succ_var_monotonic.
Qed.

Lemma is_ordered_raw_renaming_less_equal_var v1 v2 r :
  is_ordered_raw_renaming_var v1 r = true ->
  is_less_equal_var v2 v1 = true ->
  is_ordered_raw_renaming_var v2 r = true.
Proof.
  destruct r; cbn; intros Heq1 Heq2; try easy.
  apply is_less_equal_var_transitive with (v2 := v1); easy.
Qed.

Lemma is_ordered_raw_renaming_extend_boring_some_ind r1 :
  forall vl1 vr1 r2 vr2,
    raw_renaming_extend_boring
      vl1 r1 (unshift_var vr1 vr2) = Some r2 ->
    is_ordered_raw_renaming_var (shift_var vr2 vr1) r2
    = is_ordered_raw_renaming_var vr1 r1.
Proof.
  destruct r1 as [|vl3 r3 vr3]; cbn; intros * Heq1.
  - case_vars_eq vl1 (unshift_var vr1 vr2).
    injection Heq1 as <-; easy.
  - destruct is_shifting_var; try easy.
    destruct raw_renaming_extend_boring eqn:Heq2; try easy.
    injection Heq1 as <-; cbn.
    apply is_less_equal_shift.
Qed.

Lemma is_ordered_raw_renaming_extend_boring_some vl r vr r' :
  raw_renaming_extend_boring vl r vr = Some r' ->
  is_all_ordered_raw_renaming r = true ->
  is_all_ordered_raw_renaming r' = true.
Proof.
  generalize dependent vl.
  generalize dependent vr.
  generalize dependent r'.
  induction r as [|vl' r IHr vr'];
    cbn; intros r' vr vl Heq1 Heq2.
  - destruct var_eqb; try easy.
    injection Heq1 as <-; easy.
  - destruct is_shifting_var; try easy.
    destruct raw_renaming_extend_boring eqn:Heq3; try easy.
    injection Heq1 as <-; cbn.
    rewrite Bool.andb_true_iff in Heq2.
    destruct Heq2 as [Heq2 Heq5].
    rewrite is_ordered_raw_renaming_extend_boring_some_ind
      with (r1 := r) (vl1 := unshift_var vl' vl); try easy.
    rewrite Heq2; cbn.
    apply IHr
      with (vl := unshift_var vl' vl) (vr := unshift_var vr' vr);
      easy.
Qed.

Lemma is_all_ordered_interesting_raw_renaming_extend vl r vr :
  is_all_ordered_raw_renaming
    (raw_renaming_extend vl r vr) = true ->
  is_all_ordered_raw_renaming
    (interesting_raw_renaming_extend vl r vr) = true.
Proof.
  unfold interesting_raw_renaming_extend.
  destruct raw_renaming_extend_boring eqn:Heq2;
    cbn; intros Heq1; try easy.
  rewrite Bool.andb_true_iff in Heq1.
  destruct Heq1 as [Heq1 Heq3].
  apply is_ordered_raw_renaming_extend_boring_some in Heq2; easy.
Qed.

Lemma is_ordered_interesting_raw_renaming_extend_ind r1 :
  forall vl1 vr1 r2 vr2,
    raw_renaming_extend_boring vl1 r1 vr1 = Some r2 ->
    is_less_equal_var vr2 vr1 = true ->
    is_ordered_raw_renaming_var vr2 r1 = true ->
    is_ordered_raw_renaming_var vr2 r2 = true.
Proof.
  destruct r1 as [|vl3 r vr3]; cbn; intros * Heq1 Heq2 Heq3.
  - case_vars_eq vl1 vr1.
    injection Heq1 as <-; easy.
  - destruct is_shifting_var; try easy.
    destruct raw_renaming_extend_boring; try easy.
    injection Heq1 as <-; cbn.
    apply is_less_equal_var_transitive with vr3; try easy.
    apply is_less_equal_var_shift_r.
Qed.

Lemma is_ordered_interesting_raw_renaming_extend
      vl1 r vr1 vr2 :
  is_less_equal_var vr2 vr1 = true ->
  is_ordered_raw_renaming_var vr2 r = true ->
  is_ordered_raw_renaming_var
    vr2 (interesting_raw_renaming_extend vl1 r vr1) = true.
Proof.
  unfold interesting_raw_renaming_extend.
  destruct raw_renaming_extend_boring eqn:Heq1;
    cbn; intros Heq2 Heq3; try easy.
  apply is_ordered_interesting_raw_renaming_extend_ind
    with (r1 := r) (vl1 := vl1) (vr1 := vr1); easy.
Qed.

Definition normalized_raw_renaming r :=
  if is_normalized_raw_renaming r then sUnit else sEmpty.

Lemma normalized_raw_renaming_from_extend {vl r vr} :
  normalized_raw_renaming (raw_renaming_extend vl r vr) ->
  normalized_raw_renaming r.
Proof.
  unfold normalized_raw_renaming; cbn.
  destruct is_normalized_raw_renaming eqn:Heq; try easy.
  rewrite (is_normalized_raw_renaming_from_extend Heq); easy.
Qed.

Lemma is_normalized_interesting_raw_renaming_extend vl r vr :
  is_normalized_raw_renaming r = true ->
  is_ordered_raw_renaming_var vr r = true ->
  is_normalized_raw_renaming
    (interesting_raw_renaming_extend vl r vr) = true.
Proof.
  (* TODO: use is_all_normal_normalized? *)
  unfold is_normalized_raw_renaming.
  rewrite! Bool.andb_true_iff.
  intros [Heq1 Heq2] Heq3.
  split.
  - apply is_all_needed_or_interesting_raw_renaming_extend; easy.
  - apply is_all_ordered_interesting_raw_renaming_extend; cbn.
    rewrite! Bool.andb_true_iff; easy.
Qed.

Fixpoint normalized_raw_renaming_extend vl r vr :=
  match r with
  | raw_renaming_id => interesting_raw_renaming_extend vl r vr
  | raw_renaming_extend vl' r' vr' =>
    if is_less_equal_var vr vr' then
      interesting_raw_renaming_extend vl r vr
    else
      raw_renaming_extend
        (shift_var vl vl')
        (normalized_raw_renaming_extend
           (unshift_var vl' vl) r' (unshift_var vr' vr))
        (shift_var vr vr')
  end.

Lemma is_interesting_normalized_raw_renaming_extend
      vl1 r1 vr1 vl2 vr2 :
  is_interesting_raw_renaming_extension
    vl2 (raw_renaming_extend vl1 r1 vr1) vr2 = true ->
  is_interesting_raw_renaming_extension
    vl2 (normalized_raw_renaming_extend vl1 r1 vr1) vr2 = true.
Proof.
  generalize dependent vr2.
  generalize dependent vl2.
  generalize dependent vr1.
  generalize dependent vl1.
  induction r1 as [|vl3 r2 IHr vr3]; cbn; intros * Heq1.
  - apply is_interesting_interesting_raw_renaming_extend; easy.
  - destruct is_less_equal_var; cbn.
    + apply is_interesting_interesting_raw_renaming_extend; easy.
    + rewrite IHr; cbn; try easy.
      rewrite transpose_pops_reverse_right.
      rewrite transpose_pushes_reverse_left; easy.
Qed.

Lemma is_all_needed_or_interesting_normalized_raw_renaming_extend
      vl r vr :
  is_all_needed_or_interesting_raw_renaming r = true ->
  is_all_needed_or_interesting_raw_renaming
    (normalized_raw_renaming_extend vl r vr) = true.
Proof.
  generalize dependent vr.
  generalize dependent vl.
  induction r as [|vl' r IHr vr']; cbn; intros vl vr Heq1.
  - apply is_all_needed_or_interesting_raw_renaming_extend; easy.
  - destruct is_less_equal_var eqn:Heq3; cbn.
    + apply is_all_needed_or_interesting_raw_renaming_extend; easy.
    + rewrite Bool.andb_true_iff, Bool.orb_true_iff in *.
      destruct Heq1 as [Heq1 Heq2]; split; auto.
      destruct Heq1.
      * left.
        admit.
      * right.
        apply is_interesting_normalized_raw_renaming_extend; cbn.
        rewrite transpose_pops_squared_right.
        rewrite transpose_pushes_squared_left; easy.
Qed.

Lemma is_ordered_normalized_raw_renaming_extend vl1 r1 vr1 vl2 :
  is_less_equal_vars vl2 vl1 = true ->
  is_ordered_raw_renaming_var vl2 r1 = true ->
  is_ordered_raw_renaming_var
    vl2 (normalized_raw_renaming_extend vl1 r1 vr1) = true.
Proof.
  generalize dependent vl2.
  generalize dependent vr1.
  generalize dependent vl1.
  destruct r1 as [|vl3 r2 vr3]; cbn; intros * Heq1 Heq2.
  - apply is_ordered_interesting_raw_renaming_extend; easy.
  - destruct (is_less_equal_vars vl1 vl3); cbn.
    + apply is_ordered_interesting_raw_renaming_extend; easy.
    + apply is_less_equal_vars_transitive with vl3; try easy.
      apply is_less_equal_vars_shift_r.
Qed.

(* TODO : move to var equations *)
Lemma shift_less_equal v1 v2 :
  is_less_equal_vars v1 v2 = false ->
  shift_var v1 v2 = v2.
Proof.
  case_vars v1 v2; easy.
Qed.

Lemma is_all_ordered_normalized_raw_renaming_extend vl r vr :
  is_all_ordered_raw_renaming r = true ->
  is_all_ordered_raw_renaming
    (normalized_raw_renaming_extend vl r vr) = true.
Proof.
  generalize dependent vr.
  generalize dependent vl.
  induction r as [|vl' r IHr vr']; cbn; intros vl vr Heq1.
  - apply is_all_ordered_interesting_raw_renaming_extend; easy.
  - destruct is_less_equal_vars eqn:Heq3; cbn.
    + apply is_all_ordered_interesting_raw_renaming_extend; cbn.
      rewrite Heq3; easy.
    + rewrite Bool.andb_true_iff in Heq1.
      destruct Heq1 as [Heq1 Heq2].
      rewrite! Bool.andb_true_iff; split; auto.
      apply is_ordered_normalized_raw_renaming_extend;
        rewrite shift_less_equal by easy; try easy.
      rewrite is_less_equal_vars_unshift_l.
      apply is_less_than_vars_total; easy.
Qed.

Lemma is_normalized_normalized_raw_renaming_extend vl r vr :
  is_normalized_raw_renaming r = true ->
  is_normalized_raw_renaming
    (normalized_raw_renaming_extend vl r vr) = true.
Proof.
  (* TODO: use is_all_normal_normalized? *)
  unfold is_normalized_raw_renaming; intros Heq.
  rewrite Bool.andb_true_iff in Heq.
  destruct Heq as [Heq1 Heq2].
  rewrite Bool.andb_true_iff; split.
  - apply is_all_interesting_normalized_raw_renaming_extend; easy.
  - apply is_all_ordered_normalized_raw_renaming_extend; easy.
Qed.

Lemma normalized_normalized_raw_renaming_extend vl r vr :
  normalized_raw_renaming r ->
  normalized_raw_renaming
    (normalized_raw_renaming_extend vl r vr).
Proof.
  unfold normalized_raw_renaming.
  destruct (is_normalized_raw_renaming r) eqn:Heq1; try easy.
  destruct
    (is_normalized_raw_renaming
       (normalized_raw_renaming_extend vl r vr)) eqn:Heq2;
    try easy.
  apply is_normalized_normalized_raw_renaming_extend
    with (vl := vl) (vr := vr) in Heq1.
  rewrite Heq1 in Heq2.
  discriminate.
Qed.

Set Primitive Projections.
Record renaming :=
  mk_renaming {
      r_raw : raw_renaming;
      r_normalized : normalized_raw_renaming r_raw
    }.
Add Printing Constructor renaming.
Unset Primitive Projections.

Definition renaming_id : renaming :=
  mk_renaming raw_renaming_id stt.

Definition renaming_extend vl r vr : renaming :=
  mk_renaming
    (normalized_raw_renaming_extend vl (r_raw r) vr)
    (normalized_normalized_raw_renaming_extend
       vl (r_raw r) vr (r_normalized r)).

Definition apply_renaming_var r :=
  apply_raw_renaming_var (r_raw r).

Set Primitive Projections.
Record renaming_rhs :=
  mk_renaming_rhs {
      rhs_raw_renaming : raw_renaming;
      rhs_var : var
    }.
Add Printing Constructor renaming_rhs.
Unset Primitive Projections.

Definition is_normalized_renaming_rhs r :=
  is_normalized_raw_renaming (rhs_raw_renaming r).

Definition is_ordered_renaming_rhs_var v r :=
  is_ordered_raw_renaming_var v (rhs_raw_renaming r).

Definition renaming_rhs_extend vl r vr :=
  mk_renaming_rhs
    (interesting_raw_renaming_extend vl
        (rhs_raw_renaming r)
        (unshift_var (rhs_var r) vr))
    (shift_var vr (rhs_var r)).

Lemma is_normalized_renaming_rhs_extend {vl r vr} :
  is_normalized_renaming_rhs r = true ->
  is_ordered_renaming_rhs_var vl r = true ->
  is_normalized_renaming_rhs (renaming_rhs_extend vl r vr) = true.
Proof.
  apply is_normalized_interesting_raw_renaming_extend.
Qed.

Fixpoint transpose_push_raw_renaming v r {struct r} :=
  match r with
  | raw_renaming_id => mk_renaming_rhs raw_renaming_id v
  | raw_renaming_extend vl r vr =>
    if var_eqb v vl then mk_renaming_rhs r vr
    else renaming_rhs_extend
           (unshift_var v vl)
           (transpose_push_raw_renaming (unshift_var vl v) r)
           vr
  end.

Lemma transpose_push_raw_closing_normalized {vo r} :
  normalized_pushes r ->
  normalized_closing_rhs
    (transpose_push_raw_closing vo r).
Proof.
  generalize dependent vo.
  induction r as [|vo' r]; intros vo norm; try easy; cbn.
  apply normalized_pushes_from_cons in norm.
  destruct (var_opt_eqb vo zero_var_opt); try easy.
  apply closing_rhs_cons0_normalized.
  apply IHr; easy.
Qed.

Fixpoint compose_raw_closing r1 r2 :=
  match r1 with
  | nil => r2
  | cons vo r1 =>
    let rhs := transpose_push_raw_closing vo r2 in
    normalized_pushes_cons
      (rhs_push rhs)
      (compose_raw_closing r1 (rhs_raw_closing rhs))
  end.

Lemma compose_raw_closing_normalized {r1 r2} :
  normalized_pushes r1 ->
  normalized_pushes r2 ->
  normalized_pushes (compose_raw_closing r1 r2).
Proof.
  generalize dependent r2.
  induction r1 as [|vo]; intros r2 norm1 norm2; try easy.
  apply normalized_pushes_from_cons in norm1; cbn.
  apply normalized_pushes_cons_normalized.
  apply IHr1; try easy.
  apply transpose_push_raw_closing_normalized; easy.
Qed.

Definition compose_closing r1 r2 :=
  mkclosing
    (compose_raw_closing (c_raw r1) (c_raw r2))
    (compose_raw_closing_normalized
       (c_normalized r1) (c_normalized r2)).
