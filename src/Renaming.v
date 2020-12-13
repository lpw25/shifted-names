Require Import Label PeanoNat Psatz Compare_dec StrictProp.
Require Import Var VarEquations.

Inductive raw_renaming :=
  | raw_renaming_id : raw_renaming
  | raw_renaming_extend :
      var -> raw_renaming -> var -> raw_renaming.

Fixpoint is_interesting_raw_renaming_extension vl r vr :=
  match r with
  | raw_renaming_id => negb (var_eqb vl vr)
  | raw_renaming_extend vl' r vr' =>
    is_interesting_raw_renaming_extension
      (unshift_var vl' vl) r (unshift_var vr' vr)
  end.

Fixpoint is_all_interesting_raw_renaming r :=
  match r with
  | raw_renaming_id => true
  | raw_renaming_extend vl r' vr =>
    andb
      (is_interesting_raw_renaming_extension vl r' vr)
      (is_all_interesting_raw_renaming r')
  end.

Lemma is_all_interesting_raw_renaming_from_extend {vl r vr} :
  is_all_interesting_raw_renaming
    (raw_renaming_extend vl r vr) = true ->
  is_all_interesting_raw_renaming r = true.
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
    match raw_renaming_extend_boring
              (unshift_var vl' vl) r (unshift_var vr' vr)
    with
    | None => None
    | Some r =>
      Some (raw_renaming_extend
              (shift_var vl vl') r (shift_var vr vr'))
    end
  end.

Lemma is_interesting_raw_renaming_extend_boring_none vl r vr :
  raw_renaming_extend_boring vl r vr = None ->
  is_interesting_raw_renaming_extension vl r vr = true.
Proof.
  generalize dependent vl.
  generalize dependent vr.
  induction r as [|vl' r IHr vr']; cbn; intros vr vl Heq.
  - destruct (var_eqb vl vr); easy.
  - apply IHr.
    destruct (raw_renaming_extend_boring
                (unshift_var vl' vl) r (unshift_var vr' vr));
      easy.
Qed.

(* TODO move to VarEquations.v *)
Lemma succ_var_injective v1 v2 :
  v1 <> v2 ->
  succ_var v1 <> succ_var v2.
Proof.
  intros Hneq Heq; apply Hneq.
  replace v1 with (pred_var (succ_var v1))
    by (reduce_vars; easy).
  replace v2 with (pred_var (succ_var v2))
    by (reduce_vars; easy).
  congruence.
Qed.

Lemma mk_var_label_injective v1 v2 :
  v_label_opt v1 <> v_label_opt v2 ->
  v1 <> v2.
Proof.
  intros Hneq Heq; apply Hneq.
  rewrite Heq; easy.
Qed.

Lemma var_eqb_false v1 v2 :
  (var_eqb v1 v2 = false) <-> v1 <> v2.
Proof.
  unfold var_eqb.
  destruct (var_dec v1 v2); easy.
Qed.

Lemma var_eqb_true v1 v2 :
  (var_eqb v1 v2 = true) <-> v1 = v2.
Proof.
  unfold var_eqb.
  destruct (var_dec v1 v2); easy.
Qed.

Lemma shift_neq vl1 vl2 vr1 vr2 :
  vl1 <> vr1 ->
  unshift_var vl1 vl2 = unshift_var vr1 vr2 ->
  shift_var vl2 vl1 <> shift_var vr2 vr1.
Proof.
  intros Hneq Heq.
  destruct (label_opt_dec (v_label_opt vl1) (v_label_opt vr1)).
  - case_vars vl1 vl2; case_vars vr1 vr2; subst;
      autorewrite with reduce_vars_beta in *;
      try easy; try congruence;
        solve [rewrite red_var_neq
                by solve_v_label_opt_equation;
               reduce_vars_beta; lia].
  - apply mk_var_label_injective; reduce_vars_beta; easy.
Qed.

Lemma is_interesting_raw_renaming_extend_boring_some_ind
      r1 :
  forall r2 vl1 vl2 vr1 vr2,
  is_interesting_raw_renaming_extension vl1 r1 vr1 = true ->
  raw_renaming_extend_boring
    (unshift_var vl1 vl2) r1 (unshift_var vr1 vr2) = Some r2 ->
  is_interesting_raw_renaming_extension
    (shift_var vl2 vl1) r2 (shift_var vr2 vr1) = true.
Proof.
  induction r1 as [|vl5 r1 IHr1 vr5]; cbn; intros * Heq1 Heq2.
  - destruct
      (var_eqb (unshift_var vl1 vl2) (unshift_var vr1 vr2))
      eqn:Heq3; try easy.
    injection Heq2 as <-; cbn.
    rewrite Bool.negb_true_iff, var_eqb_false, var_eqb_true in *.
    apply shift_neq; easy.
  - destruct raw_renaming_extend_boring eqn:Heq3; try easy.
    injection Heq2 as <-; cbn.
    rewrite <- transpose_pops_reverse_middle.
    rewrite transpose_pushes_reverse_middle.
    apply IHr1; try easy.
    rewrite transpose_pops_reverse_right.
    rewrite transpose_pushes_reverse_left.
    easy.
Qed.

Lemma is_interesting_raw_renaming_extend_boring_some vl r1 vr r2 :
  is_all_interesting_raw_renaming r1 = true ->
  raw_renaming_extend_boring vl r1 vr = Some r2 ->
  is_all_interesting_raw_renaming r2 = true.
Proof.
  generalize dependent vl.
  generalize dependent vr.
  generalize dependent r2.
  induction r1 as [|vl2 r1 ? vr2]; cbn;
    intros r2 vr vl Heq1 Heq2.
  - destruct var_eqb; try easy.
    injection Heq2 as <-; easy.
  - rewrite Bool.andb_true_iff in Heq1;
      destruct Heq1 as [Heq1 Heq3].
    destruct raw_renaming_extend_boring eqn:Heq4; try easy.
    injection Heq2 as <-; cbn.
    rewrite Bool.andb_true_iff; split.
    + apply is_interesting_raw_renaming_extend_boring_some_ind
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

Lemma is_all_interesing_raw_renaming_extend vl r vr :
  is_all_interesting_raw_renaming r = true ->
  is_all_interesting_raw_renaming
    (interesting_raw_renaming_extend vl r vr) = true.
Proof.
  intro Heq1; unfold interesting_raw_renaming_extend.
  destruct (raw_renaming_extend_boring vl r vr) eqn:Heq2; cbn.
  - apply is_interesting_raw_renaming_extend_boring_some
      in Heq2; easy.
  - rewrite Bool.andb_true_iff; split; try easy.
    apply is_interesting_raw_renaming_extend_boring_none; easy.
Qed.

Definition is_ordered_raw_renaming_var v r :=
  match r with
  | raw_renaming_id => true
  | raw_renaming_extend v' _ _ => is_less_equal_vars v v'
  end.

Fixpoint is_all_ordered_raw_renaming r :=
  match r with
  | raw_renaming_id => true
  | raw_renaming_extend vl r' vr =>
    andb
      (is_ordered_raw_renaming_var vl r')
      (is_all_ordered_raw_renaming r')
  end.

Lemma is_all_ordered_raw_renaming_from_extend {vl r vr} :
  is_all_ordered_raw_renaming
    (raw_renaming_extend vl r vr) = true ->
  is_all_ordered_raw_renaming r = true.
Proof.
  destruct r; cbn;
    try rewrite Bool.andb_true_iff; easy.
Qed.

(* TODO : move to var equations *)
Lemma monotonic_succ_var v1 v2 :
  is_less_equal_vars v1 v2 = true ->
  is_less_equal_vars (succ_var v1) (succ_var v2) = true.
Proof.
  case_vars v1 v2; easy.
Qed.

(* TODO : move to var equations *)
Lemma is_less_equal_shift v1 v2 v3 :
  is_less_equal_vars v1 v2 = true ->
  is_less_equal_vars
    (shift_var v3 v1) (shift_var (unshift_var v1 v3) v2) = true.
Proof.
  case_vars v1 v3;
    case_vars (unshift_var v1 v3) v2; try easy.
  apply monotonic_succ_var.
Qed.

Lemma is_ordered_raw_renaming_extend_boring_some_ind r1 :
  forall r2 vl1 vl2 vr1 vr2,
  is_ordered_raw_renaming_var vl1 r1 = true ->
  raw_renaming_extend_boring
    (unshift_var vl1 vl2) r1 (unshift_var vr1 vr2) = Some r2 ->
  is_ordered_raw_renaming_var (shift_var vl2 vl1) r2 = true.
Proof.
  induction r1 as [|vl3 r3 IHr vr3]; cbn;
    intros * Heq1 Heq2.
  - destruct var_eqb; try easy.
    injection Heq2 as <-; easy.
  - destruct raw_renaming_extend_boring; try easy.
    injection Heq2 as <-; cbn.
    apply is_less_equal_shift; easy.
Qed.

Lemma is_ordered_raw_renaming_less_equal_var v1 v2 r :
  is_ordered_raw_renaming_var v1 r = true ->
  is_less_equal_vars v2 v1 = true ->
  is_ordered_raw_renaming_var v2 r = true.
Proof.
  destruct r; cbn; intros Heq1 Heq2; try easy.
  apply is_less_equal_vars_transitive with (v2 := v1); easy.
Qed.

Lemma is_ordered_raw_renaming_extend_boring_some vl r vr r' :
  is_all_ordered_raw_renaming r = true ->
  is_ordered_raw_renaming_var vl r = true ->
  raw_renaming_extend_boring vl r vr = Some r' ->
  is_all_ordered_raw_renaming r' = true.
Proof.
  generalize dependent vl.
  generalize dependent vr.
  generalize dependent r'.
  induction r as [|vl' r IHr vr']; cbn;
    intros r' vr vl Heq1 Heq2 Heq3.
  - destruct var_eqb; try easy.
    injection Heq3 as <-; easy.
  - rewrite Bool.andb_true_iff in Heq1;
      destruct Heq1 as [Heq1 Heq4].
    destruct raw_renaming_extend_boring eqn:Heq5; try easy.
    injection Heq3 as <-; cbn.
    rewrite Bool.andb_true_iff; split.
    + apply is_ordered_raw_renaming_extend_boring_some_ind
        with (r1 := r) (vr1 := vr') (vr2 := vr); easy.
    + apply IHr
        with (vl := unshift_var vl' vl) (vr := unshift_var vr' vr);
        try easy.
      apply is_ordered_raw_renaming_less_equal_var
        with (v1 := vl'); try easy.
      apply is_less_equal_vars_transitive with (v2 := vl); try easy.
      apply is_less_equal_vars_unshift_r.
Qed.

Lemma is_all_ordered_raw_renaming_extend vl r vr :
  is_all_ordered_raw_renaming r = true ->
  is_ordered_raw_renaming_var vl r = true ->
  is_all_ordered_raw_renaming
    (interesting_raw_renaming_extend vl r vr) = true.
Proof.
  intros Heq1 Heq2.
  unfold interesting_raw_renaming_extend.
  destruct raw_renaming_extend_boring
    eqn:Heq3; cbn; try rewrite Bool.andb_true_iff; try easy.
  apply is_ordered_raw_renaming_extend_boring_some
    with (vl := vl) (r := r) (vr := vr); easy.
Qed.

Definition is_normalized_raw_renaming r :=
  andb
    (is_all_interesting_raw_renaming r)
    (is_all_ordered_raw_renaming r).

Definition normalized_raw_renaming r :=
  if is_normalized_raw_renaming r then sUnit else sEmpty.

Lemma is_normalized_raw_renaming_from_extend {vl r vr} :
  is_normalized_raw_renaming (raw_renaming_extend vl r vr) = true ->
  is_normalized_raw_renaming r = true.
Proof.
  cbn.
  destruct (is_normalized_raw_renaming r); try easy.
  rewrite !Bool.andb_false_r; easy.
Qed.

Lemma normalized_raw_renaming_from_extend {vl r vr} :
  normalized_raw_renaming (raw_renaming_extend vl r vr) ->
  normalized_raw_renaming r.
Proof.
  unfold normalized_raw_renaming; cbn.
  destruct (is_normalized_raw_renaming r); try easy.
  rewrite !Bool.andb_false_r; easy.
Qed.

Lemma is_normalized_raw_renaming_extend_boring_none
      r vl1 vl2 vr1 vr2 :
  is_normalized_raw_renaming (raw_renaming_extend vl2 r vr2)
  = true ->
  raw_renaming_extend_boring
    vl1 (raw_renaming_extend vl2 r vr2) vr1 = None ->
  is_less_equal_vars vl1 vl2 = true ->
  is_normalized_raw_renaming
    (raw_renaming_extend vl1 (raw_renaming_extend vl2 r vr2) vr1)
    = true.
Proof.
  intros Heq1 Heq2 Heq3; cbn in *.
  rewrite Heq3, Heq1.
  rewrite is_interesting_raw_renaming_extend_boring_none; try easy.
  destruct (raw_renaming_extend_boring (unshift_var vl2 vl1) r
             (unshift_var vr2 vr1)); easy.
Qed.

Lemma is_normalized_raw_renaming_extend_boring_some
           vl r vr r' :
  is_normalized_raw_renaming r = true ->
  raw_renaming_extend_boring vl r vr = Some r' ->
  is_normalized_raw_renaming r' = true.
Proof.
  generalize dependent vl.
  generalize dependent vr.
  generalize dependent r'.
  induction r as [|vl' r IHr vr']; cbn;
    intros r' vr vl Heq1 Heq2.
  - destruct (var_eqb vl vr); try easy.
    replace r' with (raw_renaming_id) by congruence.
    easy.
  - destruct (is_ordered_raw_renaming_var vl' r)
      eqn:Heq4; try easy.
    destruct (is_interesting_raw_renaming_extension vl' r vr')
      eqn:Heq5; try easy.
    destruct (is_normalized_raw_renaming r)
      eqn:Heq6; try easy.
    destruct (raw_renaming_extend_boring
                (unshift_var vl' vl) r (unshift_var vr' vr))
      as [r''|] eqn:Heq7; try easy.
    replace r'
      with (raw_renaming_extend (shift_var vl vl')
              r'' (shift_var vr vr'))
      by congruence; cbn.
    replace (is_normalized_raw_renaming r'') with true
      by (symmetry;
          apply IHr with (vl := unshift_var vl' vl)
            (vr := unshift_var vr' vr); easy).
    rewrite is_ordered_raw_renaming_extend_boring_shift
      with (r1 := r) (vr1 := vr') (vr2 := vr) by easy.
    admit.
Admitted.
(*
    rewrite (is_interesting_raw_renaming_extend_boring_shift
               Heq5 Heq7).
    easy.
Qed.
*)

Lemma is_normalized_interesting_raw_renaming_extend vl r vr :
  is_normalized_raw_renaming r = true ->
  is_ordered_raw_renaming_var vl r = true ->
  is_normalized_raw_renaming
    (interesting_raw_renaming_extend vl r vr) = true.
Proof.
  intros Heq1 Heq2; unfold interesting_raw_renaming_extend.
  destruct (raw_renaming_extend_boring vl r vr) as [r'|] eqn:Heq3.
  - apply is_normalized_raw_renaming_extend_boring_some
      with (vl := vl) (r := r) (vr := vr); easy.
  - cbn; rewrite Heq1, Heq2.
    rewrite is_interesting_raw_renaming_extend_boring_none by easy.
    easy.
Qed.

Fixpoint normalized_raw_renaming_extend vl r vr :=
  match r with
  | raw_renaming_id => interesting_raw_renaming_extend vl r vr
  | raw_renaming_extend vl' r' vr' =>
    if is_less_equal_vars vl vl' then
      interesting_raw_renaming_extend vl r vr
    else
      raw_renaming_extend
        (shift_var vl vl')
        (normalized_raw_renaming_extend
           (unshift_var vl' vl) r' (unshift_var vr' vr))
        (shift_var vr vr')
  end.

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


Lemma is_interesting_interesting_raw_renaming_extend_shift_ind
      r1 :
  forall r2 vl1 vl2 vl3 vl4 vr1 vr2 vr3 vr4,
  is_interesting_raw_renaming_extension vl1 r1 vr1 = true ->
  vl3 = unshift_var vl1 vl2 ->
  vr3 = unshift_var vr1 vr2 ->
  r2 = interesting_raw_renaming_extend vl3 r1 vr3 ->
  vl4 = shift_var vl2 vl1 ->
  vr4 = shift_var vr2 vr1 ->
  is_interesting_raw_renaming_extension vl4 r2 vr4 = true.
Proof.
  intros * Heq1 -> -> -> -> ->.
  unfold interesting_raw_renaming_extend.
  destruct
      (raw_renaming_extend_boring
         (unshift_var vl1 vl2) r1
         (unshift_var vr1 vr2))
      as [r2|] eqn:Heq2; try easy.
  - apply (@is_interesting_raw_renaming_extend_boring_shift r1); easy.
  - 

  induction r1 as [|vl5 r1 IHr1 vr5]; cbn;
    unfold interesting_raw_renaming_extend;

Qed.

Lemma is_interesting_raw_renaming_extend_boring_shift
      {r1 r2 vl1 vl2 vr1 vr2} :
  is_interesting_raw_renaming_extension vl1 r1 vr1 = true ->
  raw_renaming_extend_boring
    (unshift_var vl1 vl2) r1 (unshift_var vr1 vr2) = Some r2 ->
  is_interesting_raw_renaming_extension
    (shift_var vl2 vl1) r2 (shift_var vr2 vr1) = true.
Proof.
  intros Heq1 Heq2.
  apply (is_interesting_raw_renaming_extend_boring_shift_ind
           r1 r2 vl1 vl2 _ _ vr1 vr2 _ _ Heq1 eq_refl eq_refl Heq2
           eq_refl eq_refl).
Qed.

Lemma is_interesting_normalized_raw_renaming_extend_shift_ind
      r1 :
  forall vl1 vl2 vl3 vl4 vr1 vr2 vr3 vr4,
  is_interesting_raw_renaming_extension vl1 r1 vr1 = true ->
  vl3 = unshift_var vl1 vl2 ->
  vr3 = unshift_var vr1 vr2 ->
  vl4 = shift_var vl2 vl1 ->
  vr4 = shift_var vr2 vr1 ->
  is_interesting_raw_renaming_extension
    vl4 (normalized_raw_renaming_extend vl3 r1 vr3) vr4 = true.
Proof.
  induction r1 as [|vl5 r1 IHr1 vr5];
    cbn -[interesting_raw_renaming_extend];
    intros * Heq1 -> -> -> ->.
  - destruct
      (raw_renaming_extend_boring
        (unshift_var vl1 vl2) raw_renaming_id
        (unshift_var vr1 vr2)) as [r2|] eqn:Heq2.
    + apply (@is_interesting_raw_renaming_extend_boring_shift
               raw_renaming_id); easy.
    + cbn; rewrite transpose_pushes_squared_left,
        transpose_pops_squared_right; easy.
  - destruct (is_less_equal_vars (unshift_var vl1 vl2) vl5) eqn:Heq2.
    + destruct
        (raw_renaming_extend_boring
          (unshift_var vl1 vl2)
          (raw_renaming_extend vl5 r1 vr5)
          (unshift_var vr1 vr2)) as [r2|] eqn:Heq3.
      * apply (@is_interesting_raw_renaming_extend_boring_shift
                 (raw_renaming_extend vl5 r1 vr5)); easy.
      * 

destruct
      (var_eqb (unshift_var vl1 vl2) (unshift_var vr1 vr2))
      eqn:Heq3; cbn;
      rewrite Bool.negb_true_iff, var_eqb_false, ?var_eqb_true in *.
    + apply shift_neq; easy.
    + 
  - 
    + destruct
        (raw_renaming_extend_boring
           (unshift_var vl5 (unshift_var vl1 vl2)) r1
           (unshift_var vr5 (unshift_var vr1 vr2)))
        as [r2|] eqn:Heq3.
      * admit.
      * 

    eapply IHr1
      with (vl1 := unshift_var vl5 vl1)
           (vr1 := unshift_var vr5 vr1)
           (vl2 := unshift_var (shift_var vl1 vl5) vl2)
           (vr2 := unshift_var (shift_var vr1 vr5) vr2)
           (vl3 := unshift_var vl5 (unshift_var vl1 vl2))
           (vr3 := unshift_var vr5 (unshift_var vr1 vr2));
      try easy.
    + rewrite transpose_pops_reverse_right; easy.
    + rewrite transpose_pushes_reverse_left; easy.
    + rewrite transpose_pops_reverse_middle; easy.
    + rewrite transpose_pushes_reverse_middle; easy.

  - 

Lemma normalized_raw_renaming_extend_normalized vl r vr :
  normalized_raw_renaming r ->
  normalized_raw_renaming
    (normalized_raw_renaming_extend vl r vr).
Proof.
  unfold normalized_raw_renaming.
  destruct (is_normalized_raw_renaming r) eqn:Heq1;
    try easy; intros _.
  generalize dependent vl.
  generalize dependent vr.
  induction r as [|vl' r IHr vr']; intros vr vl.
  - cbn; destruct var_eqb eqn:Heq2; cbn; try easy.
    rewrite Heq2; easy.
  - unfold normalized_raw_renaming_extend.
    fold normalized_raw_renaming_extend.
    destruct (is_less_equal_vars vl vl') eqn:Heq6.
    + destruct (raw_renaming_extend_boring
                  vl (raw_renaming_extend vl' r vr') vr)
               eqn:Heq7.
      * rewrite is_normalized_raw_renaming_extend_boring_some
          with (r := raw_renaming_extend vl' r vr')
               (vl := vl) (vr := vr); easy.
      * rewrite is_normalized_raw_renaming_extend_boring_none
          with (r := r) (vl1 := vl) (vl2 := vl')
               (vr1 := vr) (vr2 := vr'); try easy.
    + apply is_normalized_raw_renaming_from_extend in Heq1 as Heq2.
      specialize
        (IHr Heq2 (unshift_var vr' vr) (unshift_var vl' vl)).
      destruct (is_normalized_raw_renaming
                  (normalized_raw_renaming_extend
                     (unshift_var vl' vl) r (unshift_var vr' vr)))
               eqn:Heq7; try easy.
Qed.

Definition var_opt_geb vo1 vo2 :=
  match vo1, vo2 with
  | free n1, free n2 -> name_geb n1 n2
  | bound l1, bound l1 -> level_geb l1 l2
  | free _, bound _ -> false
  | bound _, free _ -> false
  end.


Definition var_nonzero vo :=
    negb (var_opt_eqb vo zero_var_opt) = true.

Lemma var_nonzero_shift vo1 vo2 :
  var_nonzero vo2 ->
  var_nonzero (shift_var_opt vo1 vo2).
Proof.
  destruct vo1 as [[n1|[|l1]]|], vo2 as [[n2|[|l2]]|];
    cbn; try easy.
  unfold shift_level.
  destruct (le_gt_dec (S l1) (S l2)); easy.
Qed.

Lemma var_nonzero_unshift vo1 vo2 vo3 :
  (var_nonzero vo1 -> var_nonzero vo2) ->
  var_nonzero (unshift_var_opt vo3 vo1) ->
  var_nonzero (unshift_var_opt vo3 vo2).
Proof.
  destruct vo1 as [[n1|[|l1]]|], vo2 as [[n2|[|l2]]|],
    vo3 as [[n3|[|l3]]|]; cbn; try easy.

Lemma is_normalized_raw_renaming_entry_greater so vo1 vo2 r :
  (var_nonzero vo1 -> var_nonzero vo2) ->
  is_normalized_raw_renaming_entry so vo1 r = true ->
  is_normalized_raw_renaming_entry so vo2 r = true.
Proof.
  generalize dependent vo1.
  generalize dependent vo2.
  induction r as [|so2 vo3]; intros vo2 vo1; cbn; try easy.
  destruct (label_opt_eqb so so2); try easy.
  intros Himp.
  apply IHr.


Lemma var_nonzero_unshift vo1 vo2 :
  var_nonzero (unshift_var_opt vo1 vo2) ->
  var_nonzero vo1 \/ var_nonzero vo2
Proof.
  split; intros H.
  - destruct vo1 as [[n1|[|l1]]|], vo2 as [[n2|[|l2]]|];
      cbn; try easy; destruct H; try easy.

  split.

Lemma is_normalized_raw_renaming_entry_unshift_shift
           so vo1 vo2 vo3 r :
  is_normalized_raw_renaming_entry so
    (unshift_var_opt vo3 vo1) r = true ->
  is_normalized_raw_renaming_entry so
    (unshift_var_opt (shift_var_opt vo2 vo3) vo1) r = true.
Proof.
  induction r as [|so2 vo4]; cbn.
  - admit.
  - destruct (label_opt_eqb so so2); try easy.
    

Lemma raw_renaming_cons_null_entry_preserves_entries
           so1 vo1 r1 r2 so2 vo2 :
  is_normalized_raw_renaming_entry so1 vo1 r1 = true ->
  raw_renaming_cons_null_entry so2 vo2 r1 = Some r2 ->
  is_normalized_raw_renaming_entry so1 vo1 r2 = true.
Proof.
  generalize dependent vo1.
  generalize dependent vo2.
  generalize dependent r2.
  induction r1 as [|so3 vo3]; intros r2 vo2 vo1; cbn.
  - destruct (var_opt_eqb vo2 zero_var_opt); try easy; intros.
    assert (r2 = raw_renaming_nil) as Hrw by congruence.
    rewrite Hrw; easy.
  - destruct (label_opt_eqb so2 so3) eqn:Heq1; try easy.
    destruct (raw_renaming_cons_null_entry so2
                (unshift_var_opt vo3 vo2) r1) eqn:Heq2; try easy.
    intros;
      assert (r2 = raw_renaming_cons so3 (shift_var_opt vo2 vo3) r)
      as Hrw by congruence; rewrite Hrw; cbn.
    destruct (label_opt_eqb so1 so3); try easy.
    apply IHr1 with (vo2 := unshift_var_opt vo3 vo2); try easy.

Lemma raw_renaming_cons_null_entry_some so vo r r' :
  normalized_raw_renaming r ->
  raw_renaming_cons_null_entry so vo r = Some r' ->
  normalized_raw_renaming r'.
  generalize dependent so.
  generalize dependent vo.
  generalize dependent r'.
  induction r as [|so' vo' r]; intros r' vo so; cbn.
  - destruct (var_opt_eqb vo zero_var_opt); try easy.
    intros; assert (r' = raw_renaming_nil)
      as Hrw by congruence.
    rewrite Hrw; easy.
  - destruct (label_opt_eqb so so'); try easy.
    destruct (raw_renaming_cons_null_entry so
                (unshift_var_opt vo' vo) r) eqn:Heq;
      try easy.
    apply IHr in Heq.
    
Qed.

Lemma raw_renaming_cons_null_entry_none so vo r r' :
  raw_renaming_cons_null_entry so vo r = None ->
  is_normalized_raw_renaming_entry so vo r.
Qed.

Lemma normalized_raw_renaming_cons_normalized
           {so vo r} :
  normalized_raw_renaming r ->
  normalized_raw_renaming
    (normalized_raw_renaming_cons so vo r).
Proof. destruct vo as [[|[]]|], r; easy. Qed.

Definition closing_cons0 vo r :=
  mkclosing
    (normalized_pushes_cons vo (c_raw r))
    (normalized_pushes_cons_normalized
       (c_normalized r)).

Definition closing_weak0 r :=
  closing_cons0 None r.

Definition closing_exchange0 r l :=
  closing_cons0 (Some (bound l)) r.

Definition closing_close0 r n :=
  closing_cons0 (Some (free n)) r.

Definition raw_closing_hd r :=
  match r with
  | nil => zero_var_opt
  | cons vo' _ => vo'
  end.

Definition raw_closing_tl (r : raw_closing) :=
  match r with
  | nil => nil
  | cons _ r' => r'
  end.

Fixpoint raw_closing_cons l vo r :=
  match l with
  | 0 => normalized_pushes_cons vo r
  | S l =>
    normalized_pushes_cons
      (shift_var_opt vo (raw_closing_hd r))
      (raw_closing_cons
         l (unshift_var_opt (raw_closing_hd r) vo)
         (raw_closing_tl r))
  end.

Lemma raw_closing_cons_normalized {l vo r} :
  normalized_pushes r ->
  normalized_pushes (raw_closing_cons l vo r).
Proof.
  generalize dependent vo.
  generalize dependent r.
  induction l; cbn; intros r vo Hnorm;
    apply normalized_pushes_cons_normalized; try easy.
  apply IHl.
  destruct r as [|vo' r]; try easy.
  apply normalized_pushes_from_cons in Hnorm; easy.
Qed.

Definition closing_cons l vo r :=
  mkclosing
    (raw_closing_cons l vo (c_raw r))
    (raw_closing_cons_normalized (c_normalized r)).

Definition closing_weak l r :=
  closing_cons l None r.

Definition closing_exchange l1 l2 r :=
  closing_cons l1 (Some (bound l2)) r.

Definition closing_close l n r :=
  closing_cons l (Some (free n)) r.

Fixpoint closing_weak_n N : closing :=
  match N with
  | 0 => closing_id
  | S N => closing_weak 0 (closing_weak_n N)
  end.

Fixpoint closing_weakening N M : closing :=
  match N with
  | 0 => closing_weak_n M
  | S N => closing_exchange 0 0 (closing_weakening N M)
  end.

Fixpoint apply_raw_closing_var r : var_op :=
  match r with
  | nil => var_op_id
  | cons vo r =>
    lift_var_op (apply_raw_closing_var r) @ push_var vo
  end.

Definition apply_closing_var r :=
  apply_raw_closing_var (c_raw r).

Set Primitive Projections.
Record closing_rhs :=
  mk_closing_rhs {
      rhs_raw_closing : raw_closing;
      rhs_push : option var
    }.
Add Printing Constructor closing_rhs.
Unset Primitive Projections.

Definition normalized_closing_rhs r :=
  normalized_pushes (rhs_raw_closing r).

Definition closing_rhs_cons0 vo r :=
  mk_closing_rhs
    (normalized_pushes_cons
       (unshift_var_opt (rhs_push r) vo)
       (rhs_raw_closing r))
    (shift_var_opt vo (rhs_push r)).

Definition closing_rhs_weak0 r :=
  closing_rhs_cons0 None r.

Definition closing_rhs_exchange0 l r :=
  closing_rhs_cons0 (Some (bound l)) r.

Definition closing_rhs_close0 n r :=
  closing_rhs_cons0 (Some (free n)) r.

Lemma closing_rhs_cons0_normalized {vo r} :
  normalized_closing_rhs r ->
  normalized_closing_rhs (closing_rhs_cons0 vo r).
Proof.
  destruct r as [? []]; cbn;
    apply normalized_pushes_cons_normalized;
    easy.
Qed.

Fixpoint transpose_push_raw_closing vo r {struct r} :=
  match r with
  | nil => mk_closing_rhs nil vo
  | cons vo' r =>
    if var_opt_eqb vo zero_var_opt then mk_closing_rhs r vo'
    else closing_rhs_cons0 vo'
           (transpose_push_raw_closing
              (unshift_var_var_opt zero_var vo) r)
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
