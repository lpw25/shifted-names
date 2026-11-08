(** * Variables

    A variable is a label together with a shift index: [mk_var (Some s) i] is
    the free name [s₍ᵢ₎], "the [s] that is [i] binders of [s] further out",
    and [mk_var None i] is the bound (de Bruijn) variable [i].  All labels,
    including the anonymous one, are treated uniformly. *)

From Stdlib Require Import Arith Bool.
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
