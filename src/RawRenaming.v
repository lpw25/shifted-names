Require Import Label PeanoNat Psatz Ring Compare_dec StrictProp.
Require Import Var VarEquations.

Inductive raw_renaming :=
  | raw_renaming_id : raw_renaming
  | raw_renaming_extend :
      var -> raw_renaming -> var -> raw_renaming.

Fixpoint apply_raw_renaming_var r : var_op 0 0 :=
  match r with
  | raw_renaming_id => var_op_id
  | raw_renaming_extend vl r vr =>
    pop_var vl @ lift_var_op (apply_raw_renaming_var r) @ push_var vr
  end.

Set Primitive Projections.
Record renaming_rhs :=
  mk_renaming_rhs {
      rhs_raw_renaming : raw_renaming;
      rhs_push : var
    }.
Add Printing Constructor renaming_rhs.
Unset Primitive Projections.

Definition renaming_rhs_extend vl r vr :=
  mk_renaming_rhs
    (raw_renaming_extend vl
        (rhs_raw_renaming r)
        (unshift_var (rhs_push r) vr))
    (shift_var vr (rhs_push r)).

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

Fixpoint compose_raw_renaming r1 r2 :=
  match r1 with
  | raw_renaming_id => r2
  | raw_renaming_extend vl r1 vr =>
    let rhs := transpose_push_raw_renaming vr r2 in
    raw_renaming_extend
      vl
      (compose_raw_renaming r1 (rhs_raw_renaming rhs))
      (rhs_push rhs)
  end.

Fixpoint inverse_raw_renaming r :=
  match r with
  | raw_renaming_id => r
  | raw_renaming_extend vl r vr =>
      raw_renaming_extend vr (inverse_raw_renaming r) vl
  end.
