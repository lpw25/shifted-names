Require Import String PeanoNat Compare_dec StrictProp.
Require Import Var.

Definition raw_closing := list (option var).

Definition is_pushes_nil (r : list (option var)) :=
  match r with
  | nil => true
  | _ => false
  end.

Fixpoint is_normalized_pushes r :=
  match r with
  | nil => true
  | cons vo r =>
    if andb (var_opt_eqb vo zero_var_opt) (is_pushes_nil r)
    then false
    else is_normalized_pushes r
  end.

Definition normalized_pushes r :=
  if is_normalized_pushes r then sUnit
  else sEmpty.

Definition normalized_pushes_from_cons {r vo} :
  normalized_pushes (cons vo r) ->
  normalized_pushes r.
Proof. destruct vo as [[|[]]|], r; easy. Defined.

Set Primitive Projections.
Record closing :=
  mkclosing {
      c_raw : raw_closing;
      c_normalized : normalized_pushes c_raw
    }.
Add Printing Constructor closing.
Unset Primitive Projections.

Definition closing_id : closing :=
  mkclosing nil stt.

Definition normalized_pushes_cons vo r :=
  if andb (var_opt_eqb vo zero_var_opt)
          (is_pushes_nil r)
  then nil
  else cons vo r.

Definition normalized_pushes_cons_normalized {vo r} :
  normalized_pushes r ->
  normalized_pushes (normalized_pushes_cons vo r).
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
