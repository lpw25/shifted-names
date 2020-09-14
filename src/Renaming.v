Require Import Label PeanoNat Psatz Compare_dec StrictProp.
Require Import Var.

Inductive raw_renaming :=
  | raw_renaming_id : raw_renaming
  | raw_renaming_extend :
      var -> raw_renaming -> option var -> raw_renaming.

Fixpoint is_interesting_raw_renaming_extension v r vo :=
  match r with
  | raw_renaming_id => negb (var_opt_var_eqb vo v)
  | raw_renaming_extend v' r vo' =>
    is_interesting_raw_renaming_extension
      (unshift_var v' v) r (unshift_var_opt vo' vo)
  end.

Definition is_ordered_raw_renaming_var r v :=
  match r with
  | raw_renaming_id => true
  | raw_renaming_extend v' _ _ => is_less_equal_vars v' v
  end.

Fixpoint is_normalized_raw_renaming r :=
  match r with
  | raw_renaming_id => true
  | raw_renaming_extend v r vo =>
    andb (is_ordered_raw_renaming_var r v)
         (andb (is_interesting_raw_renaming_extension v r vo)
               (is_normalized_raw_renaming r))
  end.

Definition normalized_raw_renaming r :=
  if is_normalized_raw_renaming r then sUnit else sEmpty.

Definition normalized_raw_renaming_from_extend {v r vo} :
  normalized_raw_renaming (raw_renaming_extend v r vo) ->
  normalized_raw_renaming r.
Proof.
  unfold normalized_raw_renaming; cbn.
  destruct (is_normalized_raw_renaming r); try easy.
  rewrite !Bool.andb_false_r; easy.
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

Fixpoint raw_renaming_extend_boring v r vo :=
  match r with
  | raw_renaming_id =>
      if (var_opt_var_eqb vo v) then Some r
      else None
  | raw_renaming_extend v' r vo' =>
    match raw_renaming_extend_boring
              (unshift_var v' v) r (unshift_var_opt vo' vo)
    with
    | None => None
    | Some r =>
      Some (raw_renaming_extend
              (shift_var v v') r (shift_var_opt vo vo'))
    end
  end.

Definition is_interesting_raw_renaming_extend_boring_none v r vo :
  raw_renaming_extend_boring v r vo = None ->
  is_interesting_raw_renaming_extension v r vo = true.
Proof.
  generalize dependent v.
  generalize dependent vo.
  induction r as [|v' r IHr vo']; cbn; intros vo v Heq.
  - destruct (var_opt_var_eqb vo v); easy.
  - apply IHr.
    destruct (raw_renaming_extend_boring
                (unshift_var v' v) r (unshift_var_opt vo' vo));
      easy.
Defined.

Definition v_label_opt_shift v1 v2 :
  v_label_opt (shift_var v1 v2) = v_label_opt v2.
Proof.
  destruct v1 as [n1|], v2 as [n2|]; cbn; try easy.
  unfold shift_name.
  destruct (label_dec (n_label n1) (n_label n2)); try easy.
  destruct (le_gt_dec (n_index n1) (n_index n2)); easy.
Defined.
(*
Definition is_ordered_vars_shift v1 v2 v3 :
  is_ordered_vars v3 v1 = true ->
  is_ordered_vars
    (shift_var (unshift_var v1 v2) v3) (shift_var v2 v1) = true.
Proof.
  unfold is_ordered_vars.
  rewrite !v_label_opt_shift.
  destruct
    (is_less_than_label_opt (v_label_opt v3) (v_label_opt v1));
    try easy.
  unfold label_opt_eqb.
  destruct (label_opt_dec (v_label_opt v3) (v_label_opt v1));
    try easy.
  rewrite !Bool.orb_false_l, !Bool.andb_true_l; intros Heq2.
  destruct v1 as [n1|l1], v2 as [n2|l2], v3 as [n3|l3]; cbn in *;
    try easy.
  - apply leb_correct; apply leb_complete in Heq2.
    assert (n_label n3 = n_label n1) by congruence.
    unfold shift_name, unshift_name.
    destruct (label_dec (n_label n1) (n_label n2));
      destruct (label_dec (n_label n2) (n_label n1)); cbn;
        try congruence.
    destruct (le_gt_dec (n_index n2) (n_index n1)).
    + destruct (label_dec (n_label n2) (n_label n3));
        destruct (le_gt_dec (n_index n2) (n_index n3)); cbn; lia.
    + destruct label_dec; try easy.
      destruct le_gt_dec; try easy.
      cbn in *.
      destruct (n_index n2); cbn in *; try lia.
      assert (i < S (n_index n3)) by lia.
      destruct n1, n2, n3; cbn in *; subst.
      destruct n_index1.
      * admit.
      * 
*)
(*
Definition is_ordered_raw_renaming_extend_boring_shift
           r1 r2 v1 v2 vo1 vo2 :
  is_ordered_raw_renaming_var r1 v1 = true ->
  raw_renaming_extend_boring
    (unshift_var v1 v2) r1 (unshift_var_opt vo1 vo2)
  = Some r2 ->
  is_ordered_raw_renaming_var r2 (shift_var v2 v1) = true.
Proof.
  generalize dependent v1.
  generalize dependent v2.
  generalize dependent vo1.
  generalize dependent vo2.
  generalize dependent r2.
  induction r1 as [|v3 r3 IHr vo3]; cbn;
    intros r2 vo2 vo1 v2 v1 Heq1 Heq2.
  - destruct var_opt_var_eqb; try easy.
    replace r2 with raw_renaming_id by congruence; easy.
  - destruct
      (raw_renaming_extend_boring
         (unshift_var v3 (unshift_var v1 v2)) r3
         (unshift_var_opt vo3 (unshift_var_opt vo1 vo2)));
      try easy.
    replace r2
      with (raw_renaming_extend
              (shift_var (unshift_var v1 v2) v3) r
              (shift_var_opt (unshift_var_opt vo1 vo2) vo3))
      by congruence; cbn.
    

Defined
*)

Definition is_ordered_raw_renaming_transitive r v1 v2 :
  is_ordered_raw_renaming_var r v1 = true ->
  is_less_equal_vars v1 v2 = true ->
  is_ordered_raw_renaming_var r v2 = true.
Proof.
  intros Heq1 Heq2.
  destruct r; cbn in *; try easy.
  apply is_less_equal_vars_transitive with (v2 := v1); easy.
Qed.

Definition is_ordered_unshift r v1 v2 :
  is_ordered_raw_renaming_var r v1 = true ->
  is_ordered_vars v1 v2 = true ->
  is_ordered_raw_renaming_var r (unshift_var v1 v2) = true.
Proof.
  intros Heq1 Heq2.
  destruct v1 as [n1|l1], v2 as [n2|l2]; cbn; try easy.
  - unfold unshift_name.
    destruct label_dec.
    + admit.
    + 

Definition is_normalized_raw_renaming_extend_boring_some
           v r vo r' :
  is_normalized_raw_renaming r = true ->
  is_ordered_raw_renaming_var r v = true ->
  raw_renaming_extend_boring v r vo = Some r' ->
  is_normalized_raw_renaming r' = true.
Proof.
  generalize dependent v.
  generalize dependent vo.
  generalize dependent r'.
  induction r as [|v' r IHr vo']; cbn;
    intros r' vo v Heq1 Heq2 Heq3.
  - destruct (var_opt_var_eqb vo v); try easy.
    replace r' with (raw_renaming_id) by congruence.
    easy.
  - destruct (is_ordered_raw_renaming_var r v')
      eqn:Heq4; try easy.
    destruct (is_interesting_raw_renaming_extension v' r vo')
      eqn:Heq5; try easy.
    destruct (is_normalized_raw_renaming r)
      eqn:Heq6; try easy.
    destruct (raw_renaming_extend_boring
                (unshift_var v' v) r (unshift_var_opt vo' vo))
      as [r''|] eqn:Heq7; try easy.
    replace r'
      with (raw_renaming_extend (shift_var v v')
              r'' (shift_var_opt vo vo'))
      by congruence; cbn.
    replace (is_normalized_raw_renaming r'') with true.
    admit.
symmetry. apply IHr with (v := unshift_var v' v)
           (vo := unshift_var_opt vo' vo). 
easy.


      by (symmetry; apply IHr with (v := unshift_var v' v)
           (vo := unshift_var_opt vo' vo); easy).
    

    + eapply IHr.

    apply IHr in Heq2.

Defined.



Fixpoint normalized_raw_renaming_extend v r vo :=
  match r with
  | raw_renaming_id => raw_renaming_extend v r vo
  | raw_renaming_extend v' r' vo' =>
    if is_ordered_vars v' v then
      match raw_renaming_extend_boring v r vo with
      | Some r => r
      | None => raw_renaming_extend v r vo
      end
    else
      raw_renaming_extend
        (shift_var v v')
        (normalized_raw_renaming_extend
           (unshift_var v' v) r' (unshift_var_opt vo' vo))
        (shift_var_opt vo vo')
  end.

Definition var_opt_geb vo1 vo2 :=
  match vo1, vo2 with
  | free n1, free n2 -> name_geb n1 n2
  | bound l1, bound l1 -> level_geb l1 l2
  | free _, bound _ -> false
  | bound _, free _ -> false
  end.


Definition var_nonzero vo :=
    negb (var_opt_eqb vo zero_var_opt) = true.

Definition var_nonzero_shift vo1 vo2 :
  var_nonzero vo2 ->
  var_nonzero (shift_var_opt vo1 vo2).
Proof.
  destruct vo1 as [[n1|[|l1]]|], vo2 as [[n2|[|l2]]|];
    cbn; try easy.
  unfold shift_level.
  destruct (le_gt_dec (S l1) (S l2)); easy.
Defined.

Definition var_nonzero_unshift vo1 vo2 vo3 :
  (var_nonzero vo1 -> var_nonzero vo2) ->
  var_nonzero (unshift_var_opt vo3 vo1) ->
  var_nonzero (unshift_var_opt vo3 vo2).
Proof.
  destruct vo1 as [[n1|[|l1]]|], vo2 as [[n2|[|l2]]|],
    vo3 as [[n3|[|l3]]|]; cbn; try easy.

Definition is_normalized_raw_renaming_entry_greater so vo1 vo2 r :
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


Definition var_nonzero_unshift vo1 vo2 :
  var_nonzero (unshift_var_opt vo1 vo2) ->
  var_nonzero vo1 \/ var_nonzero vo2
Proof.
  split; intros H.
  - destruct vo1 as [[n1|[|l1]]|], vo2 as [[n2|[|l2]]|];
      cbn; try easy; destruct H; try easy.

  split.

Definition is_normalized_raw_renaming_entry_unshift_shift
           so vo1 vo2 vo3 r :
  is_normalized_raw_renaming_entry so
    (unshift_var_opt vo3 vo1) r = true ->
  is_normalized_raw_renaming_entry so
    (unshift_var_opt (shift_var_opt vo2 vo3) vo1) r = true.
Proof.
  induction r as [|so2 vo4]; cbn.
  - admit.
  - destruct (label_opt_eqb so so2); try easy.
    

Definition raw_renaming_cons_null_entry_preserves_entries
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

Definition raw_renaming_cons_null_entry_some so vo r r' :
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
    
Defined.

Definition raw_renaming_cons_null_entry_none so vo r r' :
  raw_renaming_cons_null_entry so vo r = None ->
  is_normalized_raw_renaming_entry so vo r.
Defined.

Definition normalized_raw_renaming_cons_normalized
           {so vo r} :
  normalized_raw_renaming r ->
  normalized_raw_renaming
    (normalized_raw_renaming_cons so vo r).
Proof. destruct vo as [[|[]]|], r; easy. Defined.

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

Definition raw_closing_cons_normalized {l vo r} :
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
Defined.

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

Definition closing_rhs_cons0_normalized {vo r} :
  normalized_closing_rhs r ->
  normalized_closing_rhs (closing_rhs_cons0 vo r).
Proof.
  destruct r as [? []]; cbn;
    apply normalized_pushes_cons_normalized;
    easy.
Defined.

Fixpoint transpose_push_raw_closing vo r {struct r} :=
  match r with
  | nil => mk_closing_rhs nil vo
  | cons vo' r =>
    if var_opt_eqb vo zero_var_opt then mk_closing_rhs r vo'
    else closing_rhs_cons0 vo'
           (transpose_push_raw_closing
              (unshift_var_var_opt zero_var vo) r)
  end.

Definition transpose_push_raw_closing_normalized {vo r} :
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
Defined.

Fixpoint compose_raw_closing r1 r2 :=
  match r1 with
  | nil => r2
  | cons vo r1 =>
    let rhs := transpose_push_raw_closing vo r2 in
    normalized_pushes_cons
      (rhs_push rhs)
      (compose_raw_closing r1 (rhs_raw_closing rhs))
  end.

Definition compose_raw_closing_normalized {r1 r2} :
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
Defined.

Definition compose_closing r1 r2 :=
  mkclosing
    (compose_raw_closing (c_raw r1) (c_raw r2))
    (compose_raw_closing_normalized
       (c_normalized r1) (c_normalized r2)).
