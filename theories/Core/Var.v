(** * Variables

    A variable is a label together with a shift index: [mk_var (Some s) i] is
    the free name [s₍ᵢ₎], "the [s] that is [i] binders of [s] further out",
    and [mk_var None i] is the bound (de Bruijn) variable [i].  All labels,
    including the anonymous one, are treated uniformly. *)

From Stdlib Require Import Arith Bool Lia.
From ShiftedNames.Core Require Import Label.

Set Primitive Projections.
Record var := mk_var { v_label : option label; v_index : nat }.
Unset Primitive Projections.
Add Printing Constructor var.

Definition var_eqb (v1 v2 : var) : bool :=
  label_eqb (v_label v1) (v_label v2) && Nat.eqb (v_index v1) (v_index v2).

Lemma var_eqb_spec v1 v2 : reflect (v1 = v2) (var_eqb v1 v2).
Proof.
  destruct v1 as [l1 i1], v2 as [l2 i2]; unfold var_eqb; cbn.
  destruct (label_eqb_spec l1 l2) as [<-|Hl]; cbn.
  - destruct (Nat.eqb_spec i1 i2) as [<-|Hi]; constructor; congruence.
  - constructor; congruence.
Qed.

Definition var_eq_dec (v1 v2 : var) : {v1 = v2} + {v1 <> v2}.
Proof. destruct (var_eqb_spec v1 v2); [left|right]; assumption. Defined.

Lemma var_eta v : v = mk_var (v_label v) (v_index v).
Proof. reflexivity. Qed.

(** ** Shifting

    [shift_var v1 v2] is [v2] seen from a scope with one more variable [v1]
    in front of it: if [v2] has the same label as [v1] and an index at least
    as large, its index goes up by one.  [unshift_var v1 v2] is the partial
    inverse, removing [v1]. *)

Definition shift_var (v1 v2 : var) : var :=
  if label_eqb (v_label v1) (v_label v2) && Nat.leb (v_index v1) (v_index v2)
  then mk_var (v_label v2) (S (v_index v2))
  else v2.

Definition unshift_var (v1 v2 : var) : var :=
  if label_eqb (v_label v1) (v_label v2) && Nat.ltb (v_index v1) (v_index v2)
  then mk_var (v_label v2) (v_index v2 - 1)
  else v2.

(** [case_vars] splits on every label equality and index comparison in
    the goal and its hypotheses, then tries to close the resulting goals. *)
Ltac case_vars_step :=
  match goal with
  | |- context [label_eqb ?a ?b] =>
      destruct (label_eqb_spec a b); try subst a
  | |- context [Nat.leb ?a ?b] => destruct (Nat.leb_spec a b)
  | |- context [Nat.ltb ?a ?b] => destruct (Nat.ltb_spec a b)
  | |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b)
  | H : context [label_eqb ?a ?b] |- _ =>
      destruct (label_eqb_spec a b); try subst a
  | H : context [Nat.leb ?a ?b] |- _ => destruct (Nat.leb_spec a b)
  | H : context [Nat.ltb ?a ?b] |- _ => destruct (Nat.ltb_spec a b)
  end.

Ltac case_vars :=
  repeat (cbn [v_label v_index andb orb negb] in *; case_vars_step);
  cbn [v_label v_index andb orb negb] in *;
  try solve [ reflexivity | lia | congruence
            | f_equal; first [ lia | congruence ]
            | f_equal; f_equal; first [ lia | congruence ] ].

Lemma unshift_shift_var v1 v2 : unshift_var v1 (shift_var v1 v2) = v2.
Proof.
  destruct v1 as [l1 i1], v2 as [l2 i2]; unfold shift_var, unshift_var.
  case_vars.
Qed.

Lemma shift_unshift_var v1 v2 :
  v2 <> v1 -> shift_var v1 (unshift_var v1 v2) = v2.
Proof.
  destruct v1 as [l1 i1], v2 as [l2 i2]; unfold shift_var, unshift_var.
  intro Hne; case_vars.
  exfalso; apply Hne; f_equal; lia.
Qed.
