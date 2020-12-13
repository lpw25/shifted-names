Require Import Label String PeanoNat Compare_dec
        StrictProp Setoid Morphisms.

(* Name indices are [nat]s *)

Definition index := nat.

Definition index_dec := Nat.eq_dec.

(* Free names are a pair of a string and an index *)

Set Primitive Projections.
Record name := mkname { n_label : label; n_index : index }.
Add Printing Constructor name.
Unset Primitive Projections.

Definition name_of_string (s : string) := mkname s 0.
Coercion name_of_string : string >-> name.

Declare Scope name_scope.
Delimit Scope name_scope with name.
Bind Scope name_scope with name.
Arguments mkname n%name_scope i : rename.

String Notation string string_of_list_byte list_byte_of_string
  : name_scope.
Notation "s ₍₁₎" :=
  (mkname s 1) (at level 9, format "s '₍₁₎'")
  : name_scope.
Notation "s ₍₂₎" :=
  (mkname s 2) (at level 9, format "s '₍₂₎'")
  : name_scope.
Notation "s ₍₃₎" :=
  (mkname s 3) (at level 9, format "s '₍₃₎'")
  : name_scope.
Notation "s ₍₄₎" :=
  (mkname s 4) (at level 9, format "s '₍₄₎'")
  : name_scope.
Notation "s ₍₅₎" :=
  (mkname s 5) (at level 9, format "s '₍₅₎'")
  : name_scope.
Notation "s ₍₆₎" :=
  (mkname s 6) (at level 9, format "s '₍₆₎'")
  : name_scope.
Notation "s ₍₇₎" :=
  (mkname s 7) (at level 9, format "s '₍₇₎'")
  : name_scope.
Notation "s ₍₈₎" :=
  (mkname s 8) (at level 9, format "s '₍₈₎'")
  : name_scope.
Notation "s ₍₉₎" :=
  (mkname s 9) (at level 9, format "s '₍₉₎'")
  : name_scope.

Definition name_dec (n1 n2 : name) : {n1 = n2} + {n1 <> n2}.
  decide equality.
  - apply index_dec.
  - apply label_dec.
Defined.

Definition name_eqb n1 n2 : bool :=
  match name_dec n1 n2 with
  | left _ => true
  | right _ => false
  end.

Definition shift_name n1 n2 :=
  if label_dec (n_label n1) (n_label n2) then
    if le_gt_dec (n_index n1) (n_index n2) then
      (mkname (n_label n2) (S (n_index n2)))
    else n2
  else n2.
Arguments shift_name n1 n2 : simpl nomatch.

Definition unshift_name n1 n2 :=
  if label_dec (n_label n1) (n_label n2) then
    if Compare_dec.le_gt_dec (n_index n2) (n_index n1) then n2
    else mkname (n_label n2) (pred (n_index n2))
  else n2.
Arguments unshift_name n1 n2 : simpl nomatch.

(* Levels are nats *)

Definition level := nat.

Definition level_dec := Nat.eq_dec.

Definition level_eqb l1 l2 : bool :=
  match level_dec l1 l2 with
  | left _ => true
  | right _ => false
  end.

Definition shift_level (l1 l2 : level) : level :=
  if le_gt_dec l1 l2 then S l2
  else l2.
Arguments shift_level l1 l2 : simpl nomatch.

Definition unshift_level (l1 l2 : level) : level :=
  match Compare_dec.le_gt_dec l2 l1 with
  | left le => l2
  | right le => pred l2
  end.
Arguments unshift_level l1 l2 : simpl nomatch.

(* Variables are either free names or bound levels *)

Inductive var :=
| free (n : name)
| bound (l : level).

Definition var_dec (v1 v2 : var) : {v1 = v2} + {v1 <> v2}.
  decide equality.
  - apply name_dec.
  - apply level_dec.
Defined.

Definition var_eqb v1 v2 : bool :=
  match var_dec v1 v2 with
  | left _ => true
  | right _ => false
  end.

Definition var_opt_dec (vo1 vo2 : option var)
  : {vo1 = vo2} + {vo1 <> vo2}.
  decide equality.
  apply var_dec.
Defined.

Definition var_opt_eqb vo1 vo2 : bool :=
  match var_opt_dec vo1 vo2 with
  | left _ => true
  | right _ => false
  end.

Definition var_opt_var_dec (vo1 : option var) (v2 : var)
  : {vo1 = Some v2} + {vo1 <> Some v2}.
  decide equality.
  apply var_dec.
Defined.

Definition var_opt_var_eqb vo1 v2 : bool :=
  match var_opt_var_dec vo1 v2 with
  | left _ => true
  | right _ => false
  end.

Definition v_label_opt vo :=
  match vo with
  | bound _ => None
  | free n => Some (n_label n)
  end.

Definition v_nat v :=
  match v with
  | bound l => l
  | free n => n_index n
  end.

Definition mk_var so n :=
  match so with
  | None => bound n
  | Some s => free (mkname s n)
  end.

Definition succ_var v :=
  (mk_var (v_label_opt v) (S (v_nat v))).
Arguments succ_var v /.
Arguments succ_var v : simpl never.

Definition pred_var v :=
  (mk_var (v_label_opt v) (pred (v_nat v))).
Arguments pred_var v /.
Arguments pred_var v : simpl never.

(* Utilities for manipulating
   [option^n var -> option^m var] *)

Fixpoint options N A :=
  match N with
  | 0 => A
  | S N => option (options N A)
  end.

Definition var_op N M := options N var -> options M var.

Declare Scope var_op_scope.
Delimit Scope var_op_scope with var_op.
Bind Scope var_op_scope with var_op.

Definition var_op_id {N} : var_op N N :=
  (fun v => v).
Arguments var_op_id {N} v /.

Notation " 1 " := var_op_id : var_op_scope.

Definition var_op_compose {N M O} :
  var_op M O -> var_op N M -> var_op N O :=
  fun op1 op2 => fun v => op1 (op2 v).
Arguments var_op_compose {N M O} op1 op2 v /.

Notation "op1 @ op2" := (var_op_compose op1 op2)
    (at level 60, right associativity)
  : var_op_scope.

Lemma var_op_left_identity {N M} :
  forall (op : var_op N M),
    (1 @ op = op)%var_op.
Proof. reflexivity. Qed.

Lemma var_op_right_identity {N M} :
  forall (op : var_op N M),
    (op @ 1 = op)%var_op.
Proof. reflexivity. Qed.

Lemma var_op_associative {N M O P} :
  forall (op1 : var_op O P)
         (op2 : var_op M O)
         (op3 : var_op N M),
    (op1 @ (op2 @ op3) = (op1 @ op2) @ op3)%var_op.
Proof. reflexivity. Qed.

Definition lift_var_op {N M} :
  var_op N M -> var_op (S N) (S M) :=
  fun op vo =>
      match vo with
      | None => None
      | Some v => Some (op v)
      end.

Definition eq_var_op {N M} : relation (var_op N M) :=
  @pointwise_relation (options N var) (options M var) eq.

Notation "f =v= g" :=
  (eq_var_op (f)%var_op (g)%var_op) (at level 70).

Instance eq_var_op_equiv {N M} :
  Equivalence (@eq_var_op N M).
Proof.
  apply @Build_Equivalence; try easy.
  intros op1 op2 op3 Heq1 Heq2 v.
  rewrite Heq1, Heq2; easy.
Qed.

Add Parametric Morphism {N M O} : (@var_op_compose N M O)
    with signature eq_var_op ==> eq_var_op ==> eq_var_op
      as var_op_compose_mor.
  intros * Heq1 * Heq2 v; unfold var_op_compose.
  rewrite Heq1, Heq2; easy.
Qed.

Add Parametric Morphism {N M} : (@lift_var_op N M)
    with signature eq_var_op ==> eq_var_op
      as lift_var_op_mor.
  intros * Heq1 [v|]; unfold lift_var_op;
    try rewrite Heq1; easy.
Qed.

(* Core operations on vars *)

Definition shift_var v1 v2 :=
  match v1, v2 with
  | bound l1, bound l2 => bound (shift_level l1 l2)
  | bound l, free n => free n
  | free n, bound l => bound l
  | free n1, free n2 => free (shift_name n1 n2)
  end.
Arguments shift_var !v1 !v2.

Definition unshift_var v1 v2 :=
  match v1, v2 with
  | bound l1, bound l2 => bound (unshift_level l1 l2)
  | free n, bound l => bound l
  | bound l, free n => free n
  | free n1, free n2 => free (unshift_name n1 n2)
  end.
Arguments unshift_var !v1 !v2.

Definition pop_var v1 : var_op 1 0 :=
  fun vo2 =>
    match vo2 with
    | None => v1
    | Some v2 => shift_var v1 v2
    end.
Arguments pop_var v1 vo2 : simpl never.

Definition push_var v1 : var_op 0 1 :=
  fun v2 =>
    if var_eqb v1 v2 then None
    else Some (unshift_var v1 v2).
Arguments push_var v1 v2 : simpl never.

Definition swap_var : var_op 2 2 :=
  fun voo =>
    match voo with
    | None => Some None
    | Some None => None
    | Some (Some v) => Some (Some v)
    end.
Arguments swap_var voo : simpl nomatch.

(* Total ordering on vars *)

Definition is_less_equal_vars v1 v2 :=
  orb
    (is_less_than_label_opt (v_label_opt v1) (v_label_opt v2))
    (andb
       (label_opt_eqb (v_label_opt v1) (v_label_opt v2))
       (leb (v_nat v1) (v_nat v2))).

