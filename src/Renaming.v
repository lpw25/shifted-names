Require Import Label PeanoNat Psatz Ring Compare_dec StrictProp.
Require Import Var VarEquations.

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

Lemma is_all_interesting_raw_renaming_extend vl r vr :
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

Lemma is_interesting_interesting_raw_renaming_extend_ind r1 :
  forall vl1 vr1 r2 vl2 vr2,
    raw_renaming_extend_boring vl1 r1 vr1 = Some r2 ->
    is_interesting_raw_renaming_extension
           (unshift_var vl1 vl2) r1 (unshift_var vr1 vr2) = true ->
    is_interesting_raw_renaming_extension vl2 r2 vr2 = true.
Proof.
  induction r1 as [|vl3 r1 IHr1 vr3]; cbn; intros * Heq1 Heq2.
  - destruct (var_eqb vl1 vr1) eqn:Heq3; try easy.
    injection Heq1 as <-; cbn.
    rewrite Bool.negb_true_iff, var_eqb_false, var_eqb_true in *.
    intros Heq4; subst; easy.
  - destruct raw_renaming_extend_boring eqn:Heq3; try easy.
    injection Heq1 as <-; cbn.
    eapply IHr1 with (vl2 := unshift_var (shift_var vl1 vl3) vl2)
      (vr2 := unshift_var (shift_var vr1 vr3) vr2)
      in Heq3; try easy.
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
Lemma succ_var_monotonic v1 v2 :
  is_less_equal_vars (succ_var v1) (succ_var v2)
  = is_less_equal_vars v1 v2.
Proof.
  case_vars v1 v2; easy.
Qed.

(* TODO : move to var equations *)
Lemma is_less_equal_shift v1 v2 v3 :
  is_less_equal_vars
    (shift_var v3 v1) (shift_var (unshift_var v1 v3) v2)
  = is_less_equal_vars v1 v2.
Proof.
  case_vars v1 v3;
    case_vars (unshift_var v1 v3) v2; try easy.
  apply succ_var_monotonic.
Qed.

Lemma is_ordered_raw_renaming_less_equal_var v1 v2 r :
  is_ordered_raw_renaming_var v1 r = true ->
  is_less_equal_vars v2 v1 = true ->
  is_ordered_raw_renaming_var v2 r = true.
Proof.
  destruct r; cbn; intros Heq1 Heq2; try easy.
  apply is_less_equal_vars_transitive with (v2 := v1); easy.
Qed.

Lemma is_ordered_raw_renaming_extend_boring_some_ind r1 :
  forall vl1 vr1 r2 vl2,
    raw_renaming_extend_boring
      (unshift_var vl1 vl2) r1 vr1 = Some r2 ->
    is_ordered_raw_renaming_var (shift_var vl2 vl1) r2
    = is_ordered_raw_renaming_var vl1 r1.
Proof.
  destruct r1 as [|vl3 r3 vr3]; cbn; intros * Heq1.
  - destruct var_eqb; try easy.
    injection Heq1 as <-; easy.
  - destruct raw_renaming_extend_boring eqn:Heq2; try easy.
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
  - destruct raw_renaming_extend_boring eqn:Heq3; try easy.
    injection Heq1 as <-; cbn.
    rewrite Bool.andb_true_iff in Heq2.
    destruct Heq2 as [Heq2 Heq5].
    rewrite is_ordered_raw_renaming_extend_boring_some_ind
      with (r1 := r) (vr1 := unshift_var vr' vr); try easy.
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
  forall vl1 vr1 r2 vl2,
    raw_renaming_extend_boring vl1 r1 vr1 = Some r2 ->
    is_less_equal_vars vl2 vl1 = true ->
    is_ordered_raw_renaming_var vl2 r1 = true ->
    is_ordered_raw_renaming_var vl2 r2 = true.
Proof.
  destruct r1 as [|vl3 r vr3]; cbn; intros * Heq1 Heq2 Heq3.
  - destruct var_eqb; try easy.
    injection Heq1 as <-; easy.
  - destruct raw_renaming_extend_boring; try easy.
    injection Heq1 as <-; cbn.
    apply is_less_equal_vars_transitive with vl3; try easy.
    apply is_less_equal_vars_shift_r.
Qed.

Lemma is_ordered_interesting_raw_renaming_extend
      vl1 r vr1 vl2 :
  is_less_equal_vars vl2 vl1 = true ->
  is_ordered_raw_renaming_var vl2 r = true ->
  is_ordered_raw_renaming_var
    vl2 (interesting_raw_renaming_extend vl1 r vr1) = true.
Proof.
  unfold interesting_raw_renaming_extend.
  destruct raw_renaming_extend_boring eqn:Heq1;
    cbn; intros Heq2 Heq3; try easy.
  apply is_ordered_interesting_raw_renaming_extend_ind
    with (r1 := r) (vl1 := vl1) (vr1 := vr1); easy.
Qed.

Definition is_normalized_raw_renaming r :=
  andb
    (is_all_interesting_raw_renaming r)
    (is_all_ordered_raw_renaming r).

Definition normalized_raw_renaming r :=
  if is_normalized_raw_renaming r then sUnit else sEmpty.

Lemma is_normalized_raw_renaming_extend vl r vr :
  is_normalized_raw_renaming (raw_renaming_extend vl r vr)
  = andb
      (is_normalized_raw_renaming r)
      (andb
         (is_interesting_raw_renaming_extension vl r vr)
         (is_ordered_raw_renaming_var vl r)).
Proof.
  unfold is_normalized_raw_renaming; cbn; ring.
Qed.

Lemma is_normalized_raw_renaming_from_extend {vl r vr} :
  is_normalized_raw_renaming (raw_renaming_extend vl r vr) = true ->
  is_normalized_raw_renaming r = true.
Proof.
  rewrite is_normalized_raw_renaming_extend.
  rewrite! Bool.andb_true_iff.
  easy.
Qed.

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
  is_ordered_raw_renaming_var vl r = true ->
  is_normalized_raw_renaming
    (interesting_raw_renaming_extend vl r vr) = true.
Proof.
  unfold is_normalized_raw_renaming.
  rewrite! Bool.andb_true_iff.
  intros [Heq1 Heq2] Heq3.
  split.
  - apply is_all_interesting_raw_renaming_extend; easy.
  - apply is_all_ordered_interesting_raw_renaming_extend; cbn.
    rewrite! Bool.andb_true_iff; easy.
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
  - destruct is_less_equal_vars; cbn.
    + apply is_interesting_interesting_raw_renaming_extend; easy.
    + rewrite IHr; cbn; try easy.
      rewrite transpose_pops_reverse_right.
      rewrite transpose_pushes_reverse_left; easy.
Qed.

Lemma is_all_interesting_normalized_raw_renaming_extend vl r vr :
  is_all_interesting_raw_renaming r = true ->
  is_all_interesting_raw_renaming
    (normalized_raw_renaming_extend vl r vr) = true.
Proof.
  generalize dependent vr.
  generalize dependent vl.
  induction r as [|vl' r IHr vr']; cbn; intros vl vr Heq1.
  - apply is_all_interesting_raw_renaming_extend; easy.
  - destruct is_less_equal_vars eqn:Heq3; cbn.
    + apply is_all_interesting_raw_renaming_extend; easy.
    + rewrite Bool.andb_true_iff in Heq1.
      destruct Heq1 as [Heq1 Heq2].
      rewrite! Bool.andb_true_iff; split; auto.
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