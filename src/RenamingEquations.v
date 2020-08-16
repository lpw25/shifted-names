Require Import String PeanoNat Compare_dec
        StrictProp Setoid Morphisms.
Require Import Morph Var VarEquations Renaming.

(* Properties of closing composition *)

Definition apply_closing_rhs_var {N M} (r : closing_rhs N M)
  : morph var M var (S N) :=
  match r in closing_rhs _ M return morph _ M _ _ with
  | @closing_rhs_weak_rhs _ M r =>
      lift_morph_var (apply_closing_var r)
      @ morph_extend_by M (@weak_var)
  | @closing_rhs_exchange_rhs _ M r l2 =>
      lift_morph_var (apply_closing_var r)
      @ @cycle_in_var (S M) l2
  | @closing_rhs_close_rhs _ M r n =>
      lift_morph_var (apply_closing_var r)
      @ morph_extend_by M (@close_var n)
  end.

Lemma apply_closing_rhs_zero_weak N M
      (r : closing_rhs N M) :
  apply_closing_rhs_var (closing_rhs_zero_weak r)
  =m= morph_extend_by N (@swap_var)
      @ lift_morph_var (apply_closing_rhs_var r)
      @ morph_extend_by M (@weak_var).
Proof.
  destruct r; cbn.
  - simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes weak_op weak_op at 1.
    easy.
  - simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes weak_op (cycle_in_op l).
    easy.
  - simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes weak_op (close_op n).
    easy.
Qed.

Lemma apply_closing_rhs_zero_exchange N M
      (r : closing_rhs N M) (l2 : level (S M)):
  apply_closing_rhs_var (closing_rhs_zero_exchange r l2)
  =m= morph_extend_by N (@swap_var)
      @ lift_morph_var (apply_closing_rhs_var r)
      @ (@cycle_in_var (S M) l2).
Proof.
  destruct r; cbn.
  - simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes (cycle_in_op l2) weak_op.
    easy.
  - simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes (cycle_in_op l) (cycle_in_op l2).
    rewrite swap_swap_identity'.
    easy.
  - simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes (cycle_in_op l2) (close_op n).
    easy.
Qed.

Lemma apply_closing_rhs_zero_close N M
      (r : closing_rhs N M) n :
  apply_closing_rhs_var (closing_rhs_zero_close r n)
  =m= morph_extend_by N (@swap_var)
      @ lift_morph_var (apply_closing_rhs_var r)
      @ morph_extend_by M (@close_var n).
Proof.
  destruct r; cbn.
  - simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes (close_op n) weak_op.
    easy.
  - simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes (close_op n) (cycle_in_op l).
    easy.
  - simplify_var_morphs.
    setoid_rewrite transpose_swap_lifted'.
    transpose_pushes (close_op _) (close_op n).
    rewrite swap_swap_identity'.
    easy.
Qed.

Definition apply_closing_var_with_cycle_out {N M}
           (r : closing N M) : morph var M var N :=
  match r in closing N M return morph var M var N with
  | closing_nil =>
    apply_closing_var closing_nil
  | closing_zero_weak r =>
    (@cycle_out_var _ l_0)
    @ apply_closing_var (closing_zero_weak r)
  | closing_zero_exchange r l =>
    (@cycle_out_var _ l_0)
    @ apply_closing_var (closing_zero_exchange r l)
  | closing_zero_close r n =>
    (@cycle_out_var _ l_0)
    @ apply_closing_var (closing_zero_close r n)
  end.

Lemma apply_closing_var_add_cycle_out {N M} (r : closing N M) :
  apply_closing_var r =m= apply_closing_var_with_cycle_out r.
Proof.
  induction r; cbn;
    try rewrite cycle_out_zero_identity; simplify_var_morphs; easy.
Qed.

Lemma apply_transpose_level_closing_aux N M
      (r : closing N M) (l : level N):
  morph_id_to_succ_pred l
  @ (@cycle_in_var _ l)
  @ apply_closing_var r
  =m=
  apply_closing_rhs_var (transpose_level_closing r l).
Proof.
  generalize dependent l.
  induction r; intro l'; rewrite apply_closing_var_add_cycle_out;
    cbn; try rewrite morph_left_identity.
  - exfalso; apply (level_zero_empty l').
  - unfold level_sdec.
    destruct (level_dec l_0 l') as [|neq]; subst; cbn.
    + rewrite morph_associative.
      rewrite cycle_in_cycle_out_identity.
      easy.
    + inversion_level (unshift_level_neq l_0 l' (squash neq)).
      rewrite morph_associative.
      transpose_push_pop (cycle_in_op l') (cycle_out_op l_0).
      rewrite cycle_out_zero_identity.
      rewrite apply_closing_rhs_zero_weak; cbn.
      rewrite <- IHr; cbn.
      simplify_var_morphs.
      easy.
  - unfold level_sdec.
    destruct (level_dec l_0 l') as [|neq]; subst; cbn.
    + rewrite morph_associative.
      rewrite cycle_in_cycle_out_identity.
      easy.
    + inversion_level (unshift_level_neq l_0 l' (squash neq)).
      rewrite morph_associative.
      transpose_push_pop (cycle_in_op l') (cycle_out_op l_0).
      rewrite cycle_out_zero_identity.
      rewrite apply_closing_rhs_zero_exchange; cbn.
      rewrite <- IHr; cbn.
      simplify_var_morphs.
      easy.
  - unfold level_sdec.
    destruct (level_dec l_0 l') as [|neq]; subst; cbn.
    + rewrite morph_associative.
      rewrite cycle_in_cycle_out_identity.
      easy.
    + inversion_level (unshift_level_neq l_0 l' (squash neq)).
      rewrite morph_associative.
      transpose_push_pop (cycle_in_op l') (cycle_out_op l_0).
      rewrite cycle_out_zero_identity.
      rewrite apply_closing_rhs_zero_close; cbn.
      rewrite <- IHr; cbn.
      simplify_var_morphs.
      easy.
Qed.

Lemma apply_transpose_level_closing N M
      (r : closing (S N) M) (l : level (S N)):
  (@cycle_in_var _ l) @ apply_closing_var r
  =m=
  apply_closing_rhs_var (transpose_level_closing r l).
Proof.
  rewrite <- apply_transpose_level_closing_aux.
  easy.
Qed.

Lemma transpose_closing_weak {N M} (r : closing N M) :
  lift_morph_var (apply_closing_var r)
  @ morph_extend_by M (@weak_var)
  =m= morph_extend_by N (@weak_var)
      @ apply_closing_var r.
Proof.
  induction r; rewrite apply_closing_var_add_cycle_out;
    cbn; simplify_var_morphs; try easy.
  - rewrite morph_associative
      with (g := @cycle_out_var _ _).
    transpose_push_pop weak_op (cycle_out_op l_0).
    simplify_var_morphs.
    rewrite morph_associative
      with (g := lift_morph_var (apply_closing_var r)).
    rewrite <- lift_morph_var_compose.
    rewrite <- IHr.
    simplify_var_morphs.
    rewrite morph_associative
      with (f := morph_extend_by N (@swap_var)).
    rewrite transpose_swap_lifted.
    simplify_var_morphs.
    transpose_pushes weak_op weak_op at 1.
    easy.
  - rewrite morph_associative with (g := @cycle_out_var _ l_0).
    transpose_push_pop weak_op (cycle_out_op l_0).
    transpose_pushes (cycle_in_op l) weak_op.
    rewrite morph_associative
      with (g := morph_extend_by M (@swap_var)).
    rewrite <- transpose_swap_lifted.
    simplify_var_morphs.
    rewrite morph_associative
      with (g := lift_morph_var (apply_closing_var r)).
    rewrite <- lift_morph_var_compose.
    rewrite <- IHr.
    simplify_var_morphs.
    easy.
  - rewrite morph_associative with (g := @cycle_out_var _ l_0).
    transpose_push_pop weak_op (cycle_out_op l_0).
    transpose_pushes (close_op n) weak_op.
    rewrite morph_associative
      with (g := morph_extend_by M (@swap_var)).
    rewrite <- transpose_swap_lifted.
    simplify_var_morphs.
    rewrite morph_associative
      with (g := lift_morph_var (apply_closing_var r)).
    rewrite <- lift_morph_var_compose.
    rewrite <- IHr.
    simplify_var_morphs.
    easy.
Qed.

Lemma apply_transpose_name_closing N M
      (r : closing N M) n:
  morph_extend_by N (@close_var n) @ apply_closing_var r
  =m=
  apply_closing_rhs_var (transpose_name_closing r n).
Proof.
  induction r; rewrite apply_closing_var_add_cycle_out;
    cbn; simplify_var_morphs; try easy.
  - rewrite apply_closing_rhs_zero_weak, <- IHr;
      cbn; simplify_var_morphs.
    rewrite morph_associative with (g := @cycle_out_var _ l_0).
    transpose_push_pop (close_op n) (cycle_out_op l_0).
    rewrite cycle_out_zero_identity.
    simplify_var_morphs.
    easy.
  - rewrite apply_closing_rhs_zero_exchange, <- IHr;
      cbn; simplify_var_morphs.
    rewrite morph_associative with (g := @cycle_out_var _ l_0).
    transpose_push_pop (close_op n) (cycle_out_op l_0).
    rewrite cycle_out_zero_identity.
    simplify_var_morphs.
    easy.
  - rewrite apply_closing_rhs_zero_close, <- IHr;
      cbn; simplify_var_morphs.
    rewrite morph_associative with (g := @cycle_out_var _ l_0).
    transpose_push_pop (close_op n) (cycle_out_op l_0).
    rewrite cycle_out_zero_identity.
    simplify_var_morphs.
    easy.
Qed.

Lemma apply_compose_closing {N M O}
    (r1 : closing O N) (r2 : closing N M) :
  apply_closing_var (compose_closing r1 r2)
  =m= apply_closing_var r1 @ apply_closing_var r2.
Proof.
  generalize dependent M.
  induction r1; intros M' r2; cbn; try easy.
  - rewrite IHr1; simplify_var_morphs.
    setoid_rewrite transpose_closing_weak.
    easy.
  - simplify_var_morphs.
    rewrite apply_transpose_level_closing.
    destruct (transpose_level_closing r2 l); cbn;
      rewrite IHr1; simplify_var_morphs; easy.
  - simplify_var_morphs.
    setoid_rewrite apply_transpose_name_closing.
    destruct (transpose_name_closing r2 n); cbn;
      rewrite IHr1; simplify_var_morphs; easy.
Qed.

Lemma transpose_level_id {N} (l : level (S N)) :
  transpose_level_closing closing_id l
  = closing_rhs_exchange_rhs closing_id l.
Proof.
  induction N; cbn in *; unfold level_sdec in *.
  - destruct (level_dec l_0 l) as [eql|neql].
    + rewrite eql; easy.
    + exfalso.
      apply (level_zero_empty
               (unshift_level_neq l_0 l (squash neql))).
  - destruct (level_dec l_0 l) as [eql|neql].
    + rewrite eql; easy.
    + rewrite IHN.
      unfold closing_rhs_zero_exchange.
      rewrite shift_level_unshift_level_neq_identity.
      easy.
Qed.

Lemma transpose_name_id {N} n :
  transpose_name_closing (@closing_id N) n
  = closing_rhs_close_rhs closing_id n.
Proof.
  induction N; cbn; try rewrite IHN; easy.
Qed.

Lemma closing_left_identity {N M} (r : closing N M) :
  compose_closing closing_id r = r.
Proof.
  induction r; cbn; try rewrite IHr; easy.
Qed.

Lemma closing_right_identity {N M} (r : closing N M) :
  compose_closing r closing_id = r.
Proof.
  induction r; try easy.
  - cbn; rewrite IHr; easy.
  - remember (@closing_id (S M)) as c; cbn; subst.
    rewrite transpose_level_id, IHr; easy.
  - remember (@closing_id (S M)) as c; cbn; subst.
    rewrite transpose_name_id, IHr; easy.
Qed.

Definition project_closing_rhs_f {N M} (r : closing_rhs N M)
  : nat -> nat :=
  match r with
  | closing_rhs_weak_rhs _ => (fun N => N)
  | closing_rhs_exchange_rhs _ _ => pred
  | closing_rhs_close_rhs _ _ => (fun N => N)
  end.

Definition project_closing_rhs_closing {N M}
           (r : closing_rhs N M) :=
  match r in closing_rhs _ M
        return closing N (project_closing_rhs_f r M)
  with
  | closing_rhs_weak_rhs r => r
  | closing_rhs_exchange_rhs r _ => r
  | closing_rhs_close_rhs r _ => r
  end.

Definition project_closing_rhs_push {N M}
           (r : closing_rhs N M) :=
  match r in closing_rhs _ M
        return push_op M (project_closing_rhs_f r)
  with
  | closing_rhs_weak_rhs r => weak_op
  | closing_rhs_exchange_rhs r l => cycle_in_op l
  | closing_rhs_close_rhs r n => close_op n
  end.

Definition make_closing_rhs {N M f}
           (p : push_op M f)
  : closing N (f M) -> closing_rhs N M :=
  match p in push_op _ f
        return closing _ (f _) -> closing_rhs _ _
  with
  | weak_op => fun r => closing_rhs_weak_rhs r
  | @cycle_in_op _ l =>
    (match M return level M -> closing _ (pred M) -> closing_rhs _ M with
    | 0 => fun l => False_rect _ (level_zero_empty l)
    | S M' =>
      fun l r => @closing_rhs_exchange_rhs N M' r l
     end) l
  | close_op n => fun r => closing_rhs_close_rhs r n
  end.

Definition transpose_push_closing {N M f}
           (r : closing N M) (p : push_op N f)
  : closing_rhs (f N) M :=
  match p in push_op _ f return closing_rhs (f N) M with
  | weak_op => closing_rhs_weak_rhs r
  | cycle_in_op l => transpose_level_closing r l
  | close_op n => transpose_name_closing r n
  end.

Definition project_closing_rhs_f_zero_weak {N M}
           (r : closing_rhs N M) :
  project_closing_rhs_f (closing_rhs_zero_weak r)
  = project_closing_rhs_f r.
Proof. destruct r; easy. Defined.

Definition project_closing_rhs_f_zero_exchange {N M}
      (r : closing_rhs N M) l :
  project_closing_rhs_f (closing_rhs_zero_exchange r l)
  = project_closing_rhs_f r.
Proof. destruct r; easy. Defined.

Definition project_closing_rhs_f_zero_close {N M}
      (r : closing_rhs N M) n :
  project_closing_rhs_f (closing_rhs_zero_close r n)
  = project_closing_rhs_f r.
Proof. destruct r; easy. Defined.

Lemma project_closing_rhs_push_zero_weak {N M} (r : closing_rhs N M) :
  project_closing_rhs_push (closing_rhs_zero_weak r)
  = eq_rect_r _ (project_closing_rhs_push r)
      (project_closing_rhs_f_zero_weak r).
Proof. destruct r; easy. Defined.

Definition shift_level_push_op {M f}
           (l : level (S M)) (p : push_op M f) :=
  match p in push_op _ f return push_op _ f with
  | weak_op => weak_op
  | cycle_in_op l' => cycle_in_op (shift_level l l')
  | close_op n => close_op n
  end.

Lemma project_closing_rhs_push_zero_exchange {N M}
      (r : closing_rhs N M) l :
  project_closing_rhs_push (closing_rhs_zero_exchange r l)
  = eq_rect_r _
      (shift_level_push_op l (project_closing_rhs_push r))
      (project_closing_rhs_f_zero_exchange r l).
Proof. destruct r; easy. Qed.

Definition shift_name_push_op {M f}
           (n : name) (p : push_op M f) :=
  match p in push_op _ f return push_op _ f with
  | weak_op => weak_op
  | cycle_in_op l => cycle_in_op l
  | close_op n' => close_op (shift_name n n')
  end.

Lemma project_closing_rhs_push_zero_close {N M}
      (r : closing_rhs N M) n :
  project_closing_rhs_push (closing_rhs_zero_close r n)
  = eq_rect_r _
      (shift_name_push_op n (project_closing_rhs_push r))
      (project_closing_rhs_f_zero_close r n).
Proof. destruct r; easy. Qed.

(*
Lemma transpose_level_compose_closing_f {N M O}
      (r1 : closing N M) (r2 : closing M O) l :
  project_closing_rhs_f
    (transpose_level_closing (compose_closing r1 r2) l)
  = project_closing_rhs_f
      (transpose_push_closing r2
         (project_closing_rhs_push (transpose_level_closing r1 l))).
Proof.
  induction r1; cbn.
  - exfalso; apply (level_zero_empty l).
  - unfold level_sdec; destruct (level_dec l_0 l) as [|neq];
      subst; cbn; try easy.
    inversion_level (unshift_level_neq l_0 l (squash neq)).
    rewrite project_closing_rhs_f_zero_weak.
    rewrite IHr1.
    rewrite project_closing_rhs_push_zero_weak.
    destruct
      (transpose_level_closing r1
         (unshift_level_neq l_0 l (squash neq))); easy.
  - unfold level_sdec; destruct (level_dec l_0 l) as [|neq];
      subst; cbn.
    + destruct (transpose_level_closing r2 l0); easy.
    + inversion_level (unshift_level_neq l_0 l (squash neq)).
      rewrite project_closing_rhs_push_zero_exchange.
*)

Definition compose_closing_closing_rhs {N M O}
           (r1 : closing N M) (r2 : closing_rhs M O):=
  match r2 with
  | closing_rhs_weak_rhs r2 =>
    closing_rhs_weak_rhs (compose_closing r1 r2)
  | closing_rhs_exchange_rhs r2 l =>
    closing_rhs_exchange_rhs (compose_closing r1 r2) l
  | closing_rhs_close_rhs r2 n =>
    closing_rhs_close_rhs (compose_closing r1 r2) n
  end.

Definition compose_closing_rhs_closing {N M O}
           (r1 : closing_rhs N M) :=
  match r1 in (closing_rhs _ M) return
        closing M O -> closing_rhs N O with
  | closing_rhs_weak_rhs r1 =>
    fun r2 => closing_rhs_weak_rhs (compose_closing r1 r2)
  | closing_rhs_exchange_rhs r1 l =>
    fun r2 =>
      compose_closing_closing_rhs
        r1 (transpose_level_closing r2 l)
  | closing_rhs_close_rhs r1 n =>
    fun r2 =>
      compose_closing_closing_rhs
        r1 (transpose_name_closing r2 n)
  end.

Definition closing_rhs_exchange_rhs' {N M} :
  closing N (pred M) -> level M -> closing_rhs N M :=
  match M
    return closing _ (pred M) -> level M -> closing_rhs _ M
  with
  | 0 => fun r l => False_rect _ (level_zero_empty l)
  | S M => closing_rhs_exchange_rhs
  end.

Lemma bar {N M O}
   (r1 : closing N (pred (pred M)))
   (r2 : closing M O) l1 l2 l3 :
  forall (r3 : closing (pred M) (pred O)),
  transpose_level_closing r2 l2
  = closing_rhs_exchange_rhs' r3 l3 ->
  closing_rhs_zero_exchange
    (compose_closing_closing_rhs r1
       (transpose_level_closing r3 l1)) (level_succ_pred l3) =
  compose_closing_closing_rhs
    (closing_zero_exchange r1
        (level_succ_pred (unshift_level l1 l2)))
    (transpose_level_closing r2 (shift_level l2 l1)).
Proof.
  intros r3 Heq.
  induction r2.


Lemma foo {N M O}
  (r1 : closing_rhs N M) (r2 : closing (S M) (S O)) l1 l2 :
  forall (r3 : closing M O),
  transpose_level_closing r2 l1
  = closing_rhs_exchange_rhs r3 l2 ->
  closing_rhs_zero_exchange
    (compose_closing_rhs_closing r1 r3) l2 =
  compose_closing_rhs_closing
    (closing_rhs_zero_exchange r1 l1) r2.
Proof.
  intros r3 Heq.
  destruct r1; cbn.
  - admit.
  - 


Lemma transpose_leve_compose_closing {N M O}
      (r1 : closing N M) (r2 : closing M O) (l : level N) :
  transpose_level_closing (compose_closing r1 r2) l
  = compose_closing_rhs_closing
      (transpose_level_closing r1 l) r2.
Proof.
  generalize dependent O.
  induction r1; intros O r2; cbn; try easy.
  - exfalso; apply (level_zero_empty l).
  - unfold level_sdec; destruct (level_dec l_0 l) as [|neq];
      subst; cbn; try easy.
    inversion_level (unshift_level_neq l_0 l (squash neq)).
    rewrite IHr1.
    admit.
  - destruct (transpose_level_closing r2 l0) eqn:Heqrl; cbn.
    + unfold level_sdec; destruct (level_dec l_0 l) as [|neq];
        subst; cbn; try solve [rewrite Heqrl; easy].
      inversion_level (unshift_level_neq l_0 l (squash neq)).
      rewrite IHr1.
      admit.
    + unfold level_sdec; destruct (level_dec l_0 l) as [|neq];
        subst; cbn; try solve [rewrite Heqrl; easy].
      inversion_level (unshift_level_neq l_0 l (squash neq)).
      rewrite IHr1.
      admit.
    + unfold level_sdec; destruct (level_dec l_0 l) as [|neq];
        subst; cbn; try solve [rewrite Heqrl; easy].
      inversion_level (unshift_level_neq l_0 l (squash neq)).
      rewrite IHr1.
      admit.
  - destruct (transpose_name_closing r2 n) eqn:Heqrn; cbn.
    + exfalso. admit.
    + exfalso. admit.
    + unfold level_sdec; destruct (level_dec l_0 l) as [|neq];
        subst; cbn; try solve [rewrite Heqrn; easy].
      inversion_level (unshift_level_neq l_0 l (squash neq)).
      rewrite IHr1.
      admit.
Qed.

Lemma closing_associative {N M O L}
      (r1 : closing N M) (r2 : closing M O) (r3 : closing O L) :
  compose_closing r1 (compose_closing r2 r3)
  = compose_closing (compose_closing r1 r2) r3.
Proof.
  induction r1; cbn; try easy.
  - rewrite IHr1; easy.
  - 

Inductive closing : nat -> nat -> Set :=
| closing_nil : closing 0 0
| closing_zero_weak : forall N M,
  closing N M -> closing (S N) M
| closing_zero_exchange : forall N M,
    closing N M -> level (S M) -> closing (S N) (S M)
| closing_zero_close : forall N M,
    closing N M -> name -> closing (S N) M.
