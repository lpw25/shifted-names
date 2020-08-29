Require Import String PeanoNat Compare_dec StrictProp.
Require Import Morph Var.

Definition raw_closing := list (option var).

Definition is_raw_closing_nil (r : raw_closing) :=
  match r with
  | nil => true
  | _ => false
  end.

Fixpoint normalized_raw_closing r :=
  match r with
  | nil => sUnit
  | cons vo r =>
    if andb (var_opt_eqb vo zero_var_opt)
            (is_raw_closing_nil r)
    then sEmpty
    else normalized_raw_closing r
  end.

Definition normalized_raw_closing_from_cons {r vo} :
  normalized_raw_closing (cons vo r) ->
  normalized_raw_closing r.
Proof. destruct vo as [[|[]]|], r; easy. Defined.

Set Primitive Projections.
Record closing :=
  mkclosing {
      c_raw : raw_closing;
      c_normalized : normalized_raw_closing c_raw
    }.
Add Printing Constructor closing.
Unset Primitive Projections.

Definition closing_id : closing :=
  mkclosing nil stt.

Definition normalized_raw_closing_push0 r vo :=
  if andb (var_opt_eqb vo zero_var_opt)
          (is_raw_closing_nil r)
  then nil
  else cons vo r.

Definition normalized_raw_closing_push0_normalized {r vo} :
  normalized_raw_closing r ->
  normalized_raw_closing (normalized_raw_closing_push0 r vo).
Proof. destruct vo as [[|[]]|], r; easy. Defined.

Definition closing_push0 r vo :=
  mkclosing
    (normalized_raw_closing_push0 (c_raw r) vo)
    (normalized_raw_closing_push0_normalized
       (c_normalized r)).

Definition closing_weak0 r :=
  closing_push0 r None.

Definition closing_exchange0 r l :=
  closing_push0 r (Some (bound l)).

Definition closing_close0 r n :=
  closing_push0 r (Some (free n)).

Fixpoint closing_push l r vo :=
  match l with
  | 0 => closing_push0 r vo
  | S l =>
    match r with
    | mkclosing nil norm =>
      closing_push0
        (closing_push l r (unshift_var_opt zero_var_opt vo))
        (shift_var_opt vo zero_var_opt)
    | mkclosing (cons vo' r) norm =>
      closing_push0
        (closing_push l
           (mkclosing r (normalized_raw_closing_from_cons norm))
           (unshift_var_opt vo' vo))
        (shift_var_opt vo vo')
    end
  end.

Definition closing_weak l r :=
  closing_push l r None.

Definition closing_exchange l1 r l2 :=
  closing_push l1 r (Some (bound l2)).

Definition closing_close l r n :=
  closing_push l r (Some (free n)).

Fixpoint closing_weak_n N : closing :=
  match N with
  | 0 => closing_id
  | S N => closing_weak 0 (closing_weak_n N)
  end.

Fixpoint closing_weakening N M : closing :=
  match N with
  | 0 => closing_weak_n M
  | S N => closing_exchange 0 (closing_weakening N M) 0
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
  normalized_raw_closing (rhs_raw_closing r).

Definition closing_rhs_push0 r vo :=
  mk_closing_rhs
    (normalized_raw_closing_push0 (rhs_raw_closing r)
       (unshift_var_opt (rhs_push r) vo))
    (shift_var_opt vo (rhs_push r)).

Definition closing_rhs_weak0 r :=
  closing_rhs_push0 r None.

Definition closing_rhs_exchange0 r l :=
  closing_rhs_push0 r (Some (bound l)).

Definition closing_rhs_close0 r n :=
  closing_rhs_push0 r (Some (free n)).

Definition closing_rhs_push0_normalized {r vo} :
  normalized_closing_rhs r ->
  normalized_closing_rhs
    (closing_rhs_push0 r vo).
Proof.
  destruct r as [? []]; cbn;
    apply normalized_raw_closing_push0_normalized;
    easy.
Defined.

Fixpoint transpose_push_raw_closing vo r {struct r} :=
  match r with
  | nil => mk_closing_rhs nil vo
  | cons vo' r =>
    if var_opt_eqb vo zero_var_opt then mk_closing_rhs r vo'
    else closing_rhs_push0
           (transpose_push_raw_closing
              (unshift_var_var_opt zero_var vo) r)
           vo'
  end.

Definition transpose_push_raw_closing_normalized {vo r} :
  normalized_raw_closing r ->
  normalized_closing_rhs
    (transpose_push_raw_closing vo r).
Proof.
  generalize dependent vo.
  induction r as [|vo' r]; intros vo norm; try easy; cbn.
  apply normalized_raw_closing_from_cons in norm.
  destruct (var_opt_eqb vo zero_var_opt); try easy.
  apply closing_rhs_push0_normalized.
  apply IHr; easy.
Defined.

Fixpoint compose_raw_closing r1 r2 :=
  match r1 with
  | nil => r2
  | cons vo r1 =>
    let rhs := transpose_push_raw_closing vo r2 in
    normalized_raw_closing_push0
      (compose_raw_closing r1 (rhs_raw_closing rhs))
      (rhs_push rhs)
  end.

Definition compose_raw_closing_normalized {r1 r2} :
  normalized_raw_closing r1 ->
  normalized_raw_closing r2 ->
  normalized_raw_closing (compose_raw_closing r1 r2).
Proof.
  generalize dependent r2.
  induction r1 as [|vo]; intros r2 norm1 norm2; try easy.
  apply normalized_raw_closing_from_cons in norm1; cbn.
  apply normalized_raw_closing_push0_normalized.
  apply IHr1; try easy.
  apply transpose_push_raw_closing_normalized; easy.
Defined.

Definition compose_closing r1 r2 :=
  mkclosing
    (compose_raw_closing (c_raw r1) (c_raw r2))
    (compose_raw_closing_normalized
       (c_normalized r1) (c_normalized r2)).
