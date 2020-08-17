Require Import String PeanoNat Compare_dec StrictProp.
Require Import Morph Var.

Inductive raw_closing : Set :=
| raw_closing_id : raw_closing
| raw_closing_zero_weak :
    raw_closing -> raw_closing
| raw_closing_zero_exchange :
    raw_closing -> level -> raw_closing
| raw_closing_zero_close :
    raw_closing -> name -> raw_closing.

Fixpoint normalized_raw_closing id r :=
  match r with
  | raw_closing_id => id
  | raw_closing_zero_weak r => normalized_raw_closing sUnit r
  | raw_closing_zero_exchange r l =>
    normalized_raw_closing
      (match l with
       | 0 => sEmpty
       | S _ => sUnit
       end) r
  | raw_closing_zero_close r n => normalized_raw_closing sUnit r
  end.

Definition normalized_raw_closing_weaken {r} :
  normalized_raw_closing sEmpty r ->
  normalized_raw_closing sUnit r.
Proof.
  destruct r; easy.
Qed.

Definition normalized_raw_closing_from_exchange {id r l} :
  normalized_raw_closing id (raw_closing_zero_exchange r l) ->
  normalized_raw_closing sUnit r.
Proof.
  cbn; destruct l; try easy.
  apply normalized_raw_closing_weaken.
Qed.

Set Primitive Projections.
Record closing :=
  mkclosing {
      c_raw : raw_closing;
      c_normalized : normalized_raw_closing sUnit c_raw
    }.
Add Printing Constructor closing.
Unset Primitive Projections.

Definition closing_id : closing :=
  mkclosing raw_closing_id stt.

Definition closing_zero_weak r : closing :=
  mkclosing (raw_closing_zero_weak (c_raw r))
            (c_normalized r).

Definition normalized_raw_closing_zero_exchange r l :=
  match l with
  | 0 =>
    match r with
    | raw_closing_id => raw_closing_id
    | _ => raw_closing_zero_exchange r l
    end
  | S _ => raw_closing_zero_exchange r l
  end.

Definition normalized_raw_closing_zero_exchange_normalized
           {r l} :
  normalized_raw_closing sUnit r ->
  normalized_raw_closing sUnit
    (normalized_raw_closing_zero_exchange r l).
Proof.
  intros; destruct l, r; easy.
Qed.

Definition closing_zero_exchange r l :=
  mkclosing
    (normalized_raw_closing_zero_exchange (c_raw r) l)
    (normalized_raw_closing_zero_exchange_normalized
       (c_normalized r)).

Definition closing_zero_close r n : closing :=
  mkclosing (raw_closing_zero_close (c_raw r) n)
            (c_normalized r).

Fixpoint closing_weak l r :=
  match l with
  | 0 => closing_zero_weak r
  | S l =>
    match r with
    | mkclosing (raw_closing_id) norm =>
      closing_zero_exchange (closing_weak l r) 0
    | mkclosing (raw_closing_zero_weak r) norm =>
      closing_zero_weak
        (closing_weak l (mkclosing r norm))
    | mkclosing (raw_closing_zero_exchange r l2) norm =>
      closing_zero_exchange
        (closing_weak l
           (mkclosing r
              (normalized_raw_closing_from_exchange norm)))
        l2
    | mkclosing (raw_closing_zero_close r n) norm =>
      closing_zero_close
        (closing_weak l (mkclosing r norm))
        n
    end
  end.

Fixpoint closing_exchange l1 r l2 :=
  match l1 with
  | 0 => closing_zero_exchange r l2
  | S l1 =>
    match r with
    | mkclosing (raw_closing_id) norm =>
      closing_zero_exchange
        (closing_exchange l1 r (unshift_level 0 l2))
        (shift_level l2 0)
    | mkclosing (raw_closing_zero_weak r) norm =>
      closing_zero_weak
        (closing_exchange l1 (mkclosing r norm) l2)
    | mkclosing (raw_closing_zero_exchange r l3) norm =>
      closing_zero_exchange
        (closing_exchange l1
           (mkclosing r
              (normalized_raw_closing_from_exchange norm))
           (unshift_level l3 l2))
        (shift_level l2 l3)
    | mkclosing (raw_closing_zero_close r n) norm =>
      closing_zero_close
        (closing_exchange l1 (mkclosing r norm) l2)
        n
    end
  end.

Fixpoint closing_close l r n :=
  match l with
  | 0 => closing_zero_close r n
  | S l =>
    match r with
    | mkclosing (raw_closing_id) norm =>
      closing_zero_exchange (closing_close l r n) 0
    | mkclosing (raw_closing_zero_weak r) norm =>
      closing_zero_weak
        (closing_close l (mkclosing r norm) n)
    | mkclosing (raw_closing_zero_exchange r l2) norm =>
      closing_zero_exchange
        (closing_close l
           (mkclosing r
              (normalized_raw_closing_from_exchange norm)) n)
        l2
    | mkclosing (raw_closing_zero_close r n2) norm =>
      closing_zero_close
        (closing_close
           l (mkclosing r norm) (unshift_name n2 n))
        (shift_name n n2)
    end
  end.

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
  | raw_closing_id => var_op_id
  | raw_closing_zero_weak r =>
      lift_var_op (apply_raw_closing_var r) @ weak_var
  | raw_closing_zero_exchange r l =>
      lift_var_op (apply_raw_closing_var r) @ cycle_in_var l
  | raw_closing_zero_close r n =>
      lift_var_op (apply_raw_closing_var r) @ close_var n
  end.

Definition apply_closing_var r :=
  apply_raw_closing_var (c_raw r).

Inductive raw_closing_rhs : Set :=
| raw_closing_rhs_weak_rhs : raw_closing -> raw_closing_rhs
| raw_closing_rhs_exchange_rhs :
    raw_closing -> level -> raw_closing_rhs
| raw_closing_rhs_close_rhs :
    raw_closing -> name -> raw_closing_rhs.

Definition normalized_raw_closing_rhs r :=
  match r with
  | raw_closing_rhs_weak_rhs r =>
    normalized_raw_closing sUnit r
  | raw_closing_rhs_exchange_rhs r l =>
    normalized_raw_closing sUnit r
  | raw_closing_rhs_close_rhs r n =>
    normalized_raw_closing sUnit r
  end.

Definition raw_closing_rhs_zero_weak r :=
  match r with
  | raw_closing_rhs_weak_rhs r =>
    raw_closing_rhs_weak_rhs (raw_closing_zero_weak r)
  | raw_closing_rhs_exchange_rhs r l =>
    raw_closing_rhs_exchange_rhs (raw_closing_zero_weak r) l
  | raw_closing_rhs_close_rhs r n =>
    raw_closing_rhs_close_rhs (raw_closing_zero_weak r) n
  end.
Arguments raw_closing_rhs_zero_weak r : simpl nomatch.

Definition raw_closing_rhs_zero_exchange r l :=
  match r with
  | raw_closing_rhs_weak_rhs r =>
    raw_closing_rhs_weak_rhs
      (normalized_raw_closing_zero_exchange r l)
  | raw_closing_rhs_exchange_rhs r l2 =>
    raw_closing_rhs_exchange_rhs
      (normalized_raw_closing_zero_exchange
         r (unshift_level l2 l))
      (shift_level l l2)
  | raw_closing_rhs_close_rhs r n =>
    raw_closing_rhs_close_rhs
      (normalized_raw_closing_zero_exchange r l) n
  end.
Arguments raw_closing_rhs_zero_exchange r l : simpl nomatch.

Definition raw_closing_rhs_zero_close r n :=
  match r with
  | raw_closing_rhs_weak_rhs r =>
    raw_closing_rhs_weak_rhs (raw_closing_zero_close r n)
  | raw_closing_rhs_exchange_rhs r l =>
    raw_closing_rhs_exchange_rhs
      (raw_closing_zero_close r n) l
  | raw_closing_rhs_close_rhs r n2 =>
    raw_closing_rhs_close_rhs
      (raw_closing_zero_close r (unshift_name n2 n))
      (shift_name n n2)
  end.
Arguments raw_closing_rhs_zero_close r n : simpl nomatch.

Definition raw_closing_rhs_zero_weak_normalized {r} :
  normalized_raw_closing_rhs r ->
  normalized_raw_closing_rhs
    (raw_closing_rhs_zero_weak r).
Proof. destruct r; easy. Defined.

Definition raw_closing_rhs_zero_exchange_normalized {r l} :
  normalized_raw_closing_rhs r ->
  normalized_raw_closing_rhs
    (raw_closing_rhs_zero_exchange r l).
Proof.
  destruct r; cbn; intros;
    apply normalized_raw_closing_zero_exchange_normalized;
    easy.
Defined.

Definition raw_closing_rhs_zero_close_normalized {r n} :
  normalized_raw_closing_rhs r ->
  normalized_raw_closing_rhs
    (raw_closing_rhs_zero_close r n).
Proof. destruct r; easy. Defined.

Fixpoint transpose_level_raw_closing l r {struct r} :=
  match r with
  | raw_closing_id =>
    raw_closing_rhs_exchange_rhs raw_closing_id l
  | raw_closing_zero_weak r =>
    match l with
    | 0 => raw_closing_rhs_weak_rhs r
    | S l' =>
      raw_closing_rhs_zero_weak
        (transpose_level_raw_closing l' r)
    end
  | raw_closing_zero_exchange r l2 =>
    match l with
    | 0 => raw_closing_rhs_exchange_rhs r l2
    | S l' =>
      raw_closing_rhs_zero_exchange
        (transpose_level_raw_closing l' r) l2
    end
  | raw_closing_zero_close r n =>
    match l with
    | 0 => raw_closing_rhs_close_rhs r n
    | S l' =>
      raw_closing_rhs_zero_close
        (transpose_level_raw_closing l' r) n
    end
  end.

Definition transpose_level_raw_closing_normalized {l r} :
  normalized_raw_closing sUnit r ->
  normalized_raw_closing_rhs
    (transpose_level_raw_closing l r).
Proof.
  generalize dependent l.
  induction r; intro l'; destruct l'; cbn; intros; try easy.
  - apply raw_closing_rhs_zero_weak_normalized.
    apply IHr; easy.
  - destruct l; try easy.
    apply normalized_raw_closing_weaken; easy.
  - apply raw_closing_rhs_zero_exchange_normalized.
    apply IHr.
    destruct l; try easy.
    apply normalized_raw_closing_weaken; easy.
  - apply raw_closing_rhs_zero_close_normalized.
    apply IHr; easy.
Qed.

Fixpoint transpose_name_raw_closing n r :=
  match r with
  | raw_closing_id =>
    raw_closing_rhs_close_rhs raw_closing_id n
  | raw_closing_zero_weak r =>
      raw_closing_rhs_zero_weak
        (transpose_name_raw_closing n r)
  | raw_closing_zero_exchange r l =>
      raw_closing_rhs_zero_exchange
        (transpose_name_raw_closing n r) l
  | raw_closing_zero_close r n2 =>
      raw_closing_rhs_zero_close
        (transpose_name_raw_closing n r) n2
  end.

Definition transpose_name_raw_closing_normalized {n r} :
  normalized_raw_closing sUnit r ->
  normalized_raw_closing_rhs
    (transpose_name_raw_closing n r).
Proof.
  induction r; cbn; intros; try easy.
  - apply raw_closing_rhs_zero_weak_normalized.
    apply IHr; easy.
  - apply raw_closing_rhs_zero_exchange_normalized.
    apply IHr.
    destruct l; try easy.
    apply normalized_raw_closing_weaken; easy.
  - apply raw_closing_rhs_zero_close_normalized.
    apply IHr; easy.
Qed.

Fixpoint compose_raw_closing r1 r2 :=
  match r1 with
  | raw_closing_id => r2
  | raw_closing_zero_weak r1 =>
    raw_closing_zero_weak (compose_raw_closing r1 r2)
  | raw_closing_zero_exchange r1 l2 =>
    match transpose_level_raw_closing l2 r2 with
    | raw_closing_rhs_weak_rhs r2 =>
        raw_closing_zero_weak (compose_raw_closing r1 r2)
    | raw_closing_rhs_exchange_rhs r2 l2 =>
      normalized_raw_closing_zero_exchange
        (compose_raw_closing r1 r2) l2
    | raw_closing_rhs_close_rhs r2 n =>
      raw_closing_zero_close (compose_raw_closing r1 r2) n
    end
  | raw_closing_zero_close r1 n =>
    match transpose_name_raw_closing n r2 with
    | raw_closing_rhs_weak_rhs r2 =>
      raw_closing_zero_weak (compose_raw_closing r1 r2)
    | raw_closing_rhs_exchange_rhs r2 l2 =>
      normalized_raw_closing_zero_exchange
        (compose_raw_closing r1 r2) l2
    | raw_closing_rhs_close_rhs r2 n =>
      raw_closing_zero_close (compose_raw_closing r1 r2) n
    end
  end.

Definition compose_raw_closing_normalized {r1 r2} :
  normalized_raw_closing sUnit r1 ->
  normalized_raw_closing sUnit r2 ->
  normalized_raw_closing sUnit (compose_raw_closing r1 r2).
Proof.
  generalize dependent r2.
  induction r1; intros; cbn in *; try easy.
  - apply IHr1; easy.
  - assert (normalized_raw_closing_rhs
              (transpose_level_raw_closing l r2))
      by (apply transpose_level_raw_closing_normalized;
          easy).
    assert (normalized_raw_closing sUnit r1)
      by (destruct l; try easy;
          apply normalized_raw_closing_weaken; easy).
    destruct (transpose_level_raw_closing l r2); cbn in *.
    + apply IHr1; easy.
    + apply normalized_raw_closing_zero_exchange_normalized.
      apply IHr1; easy.
    + apply IHr1; easy.
  - assert (normalized_raw_closing_rhs
              (transpose_name_raw_closing n r2))
      by (apply transpose_name_raw_closing_normalized;
          easy).
    destruct (transpose_name_raw_closing n r2); cbn in *.
    + apply IHr1; easy.
    + apply normalized_raw_closing_zero_exchange_normalized.
      apply IHr1; easy.
    + apply IHr1; easy.
Defined.

Definition compose_closing r1 r2 :=
  mkclosing
    (compose_raw_closing (c_raw r1) (c_raw r2))
    (compose_raw_closing_normalized
       (c_normalized r1) (c_normalized r2)).
