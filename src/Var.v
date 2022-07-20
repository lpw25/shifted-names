Require Import Label String PeanoNat Compare_dec
        StrictProp Setoid Morphisms.

(* Variables are a pair of an optional label and a nat *)

Set Primitive Projections.
Record var :=
  mk_var { v_label_opt : option label; v_nat : nat }.
Add Printing Constructor var.
Unset Primitive Projections.

Definition var_of_string (s : string) := mk_var (Some s) 0.
Coercion var_of_string : string >-> var.

Declare Scope var_scope.
Delimit Scope var_scope with var.
Bind Scope var_scope with var.
Arguments mk_var lo%var_scope n : rename.

String Notation string string_of_list_byte list_byte_of_string
  : var_scope.
Notation "s ₍₁₎" :=
  (mk_var (Some s) 1) (at level 9, format "s '₍₁₎'")
  : var_scope.
Notation "s ₍₂₎" :=
  (mk_var (Some s) 2) (at level 9, format "s '₍₂₎'")
  : var_scope.
Notation "s ₍₃₎" :=
  (mk_var (Some s) 3) (at level 9, format "s '₍₃₎'")
  : var_scope.
Notation "s ₍₄₎" :=
  (mk_var (Some s) 4) (at level 9, format "s '₍₄₎'")
  : var_scope.
Notation "s ₍₅₎" :=
  (mk_var (Some s) 5) (at level 9, format "s '₍₅₎'")
  : var_scope.
Notation "s ₍₆₎" :=
  (mk_var (Some s) 6) (at level 9, format "s '₍₆₎'")
  : var_scope.
Notation "s ₍₇₎" :=
  (mk_var (Some s) 7) (at level 9, format "s '₍₇₎'")
  : var_scope.
Notation "s ₍₈₎" :=
  (mk_var (Some s) 8) (at level 9, format "s '₍₈₎'")
  : var_scope.
Notation "s ₍₉₎" :=
  (mk_var s 9) (at level 9, format "s '₍₉₎'")
  : var_scope.

Definition var_dec (v1 v2 : var) : {v1 = v2} + {v1 <> v2}.
  decide equality.
  - apply Nat.eq_dec.
  - apply label_opt_dec.
Defined.

Definition var_eqb v1 v2 : bool :=
  match var_dec v1 v2 with
  | left _ => true
  | right _ => false
  end.

(* Total ordering on vars *)

Definition is_less_equal_var v1 v2 :=
  orb
    (is_less_than_label_opt (v_label_opt v1) (v_label_opt v2))
    (andb
       (label_opt_eqb (v_label_opt v1) (v_label_opt v2))
       (leb (v_nat v1) (v_nat v2))).

Definition less_equal_var v1 v2 :=
  if is_less_equal_var v1 v2 then sUnit
  else sEmpty.
