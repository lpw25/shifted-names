(** * Variables

    A variable is a label together with a shift index: [mk_rvar (Some s) i] is
    the free name [s₍ᵢ₎], "the [s] that is [i] binders of [s] further out",
    and [mk_rvar None i] is the bound (de Bruijn) variable [i].  All labels,
    including the anonymous one, are treated uniformly. *)

From Stdlib Require Import Arith Bool Lia.
From ShiftedNames.Core Require Import Label.

Set Primitive Projections.
Record rvar := mk_rvar { v_label : option label; v_index : nat }.
Unset Primitive Projections.
Add Printing Constructor rvar.

Definition rvar_eqb (v1 v2 : rvar) : bool :=
  label_eqb (v_label v1) (v_label v2) && Nat.eqb (v_index v1) (v_index v2).

Lemma rvar_eqb_spec v1 v2 : reflect (v1 = v2) (rvar_eqb v1 v2).
Proof.
  destruct v1 as [l1 i1], v2 as [l2 i2]; unfold rvar_eqb; cbn.
  destruct (label_eqb_spec l1 l2) as [<-|Hl]; cbn.
  - destruct (Nat.eqb_spec i1 i2) as [<-|Hi]; constructor; congruence.
  - constructor; congruence.
Qed.

Lemma rvar_eqb_refl v : rvar_eqb v v = true.
Proof. destruct (rvar_eqb_spec v v); congruence. Qed.

Definition rvar_eq_dec (v1 v2 : rvar) : {v1 = v2} + {v1 <> v2}.
Proof. destruct (rvar_eqb_spec v1 v2); [left|right]; assumption. Defined.

Lemma rvar_eta v : v = mk_rvar (v_label v) (v_index v).
Proof. reflexivity. Qed.

(** ** Shifting

    [shift_rvar v1 v2] is [v2] seen from a scope with one more variable [v1]
    in front of it: if [v2] has the same label as [v1] and an index at least
    as large, its index goes up by one.  [unshift_rvar v1 v2] is the partial
    inverse, removing [v1]. *)

Definition shift_rvar (v1 v2 : rvar) : rvar :=
  if label_eqb (v_label v1) (v_label v2) && Nat.leb (v_index v1) (v_index v2)
  then mk_rvar (v_label v2) (S (v_index v2))
  else v2.

Definition unshift_rvar (v1 v2 : rvar) : rvar :=
  if label_eqb (v_label v1) (v_label v2) && Nat.ltb (v_index v1) (v_index v2)
  then mk_rvar (v_label v2) (v_index v2 - 1)
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

Lemma unshift_shift_rvar v1 v2 : unshift_rvar v1 (shift_rvar v1 v2) = v2.
Proof.
  destruct v1 as [l1 i1], v2 as [l2 i2]; unfold shift_rvar, unshift_rvar.
  case_vars.
Qed.

Lemma shift_unshift_rvar v1 v2 :
  v2 <> v1 -> shift_rvar v1 (unshift_rvar v1 v2) = v2.
Proof.
  destruct v1 as [l1 i1], v2 as [l2 i2]; unfold shift_rvar, unshift_rvar.
  intro Hne; case_vars.
  exfalso; apply Hne; f_equal; lia.
Qed.
