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

Ltac eta_reduce_name n :=
  change (mkname (n_label n) (n_index n)) with n.

Ltac eta_reduce_names :=
  try repeat
      match goal with
      | |- context [mkname (n_label ?n) (n_index ?n)] =>
        eta_reduce_name n
      end.

Ltac eta_expand_name n :=
  change n with (mkname (n_label n) (n_index n)).

Definition n_S n :=
  (mkname (n_label n) (S (n_index n))).
Arguments n_S n /.

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
    if le_gt_dec (n_index n1) (n_index n2) then n_S n2
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

Definition cycle_out_level (l1 l2 : level) : level :=
  match l2 with
  | 0 => l1
  | S l2' => shift_level l1 l2'
  end.
Arguments cycle_out_level l1 l2 : simpl nomatch.

Definition cycle_in_level (l1 l2 : level) : level :=
  if level_eqb l1 l2 then 0
  else unshift_level l1 (S l2).
Arguments cycle_in_level l1 l2 : simpl nomatch.

Definition swap_level (l : level) : level :=
  match l with
  | 0 => 1
  | 1 => 0
  | l => l
  end.
Arguments swap_level l : simpl nomatch.

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

Definition var_opt_dec (v1 v2 : option var)
  : {v1 = v2} + {v1 <> v2}.
  decide equality.
  apply var_dec.
Defined.

Definition var_opt_eqb v1 v2 : bool :=
  match var_opt_dec v1 v2 with
  | left _ => true
  | right _ => false
  end.

Definition zero_var := bound 0.

Definition zero_var_opt := Some (bound 0).

Definition open_var n v :=
  match v with
  | free n2 => free (shift_name n n2)
  | bound 0 => free n
  | bound (S l') => bound l'
  end.
Arguments open_var n v : simpl nomatch.

Definition close_var n v :=
  match v with
  | free n2 =>
    if name_eqb n n2 then bound 0
    else free (unshift_name n n2)
  | bound l => bound (S l)
  end.
Arguments close_var n v : simpl nomatch.

Definition weak_var v :=
  match v with
  | free n => free n
  | bound l => bound (S l)
  end.
Arguments weak_var v : simpl nomatch.

Definition cycle_out_var l v :=
  match v with
  | free n => free n
  | bound l2 => bound (cycle_out_level l l2)
  end.
Arguments cycle_out_var l v : simpl nomatch.

Definition cycle_in_var l v :=
  match v with
  | free n => free n
  | bound l2 => bound (cycle_in_level l l2)
  end.
Arguments cycle_in_var l v : simpl nomatch.

Definition swap_var v :=
  match v with
  | free n => free n
  | bound l => bound (swap_level l)
  end.
Arguments swap_var v : simpl nomatch.

(* Utilities for manipulating [var -> var]*)

Definition var_op := var -> var.

Declare Scope var_op_scope.
Delimit Scope var_op_scope with var_op.
Bind Scope var_op_scope with var_op.

Definition var_op_id : var_op :=
  (fun v => v).
Arguments var_op_id v /.

Notation " 1 " := var_op_id : var_op_scope.

Definition var_op_compose :
  var_op -> var_op -> var_op :=
  fun op1 op2 => fun v => op1 (op2 v).
Arguments var_op_compose op1 op2 v /.

Notation "op1 @ op2" := (var_op_compose op1 op2)
    (at level 60, right associativity)
  : var_op_scope.

Lemma var_op_left_identity :
  forall (op : var_op),
    (1 @ op = op)%var_op.
Proof. reflexivity. Qed.

Lemma var_op_right_identity :
  forall (op : var_op),
    (op @ 1 = op)%var_op.
Proof. reflexivity. Qed.

Lemma var_op_associative :
  forall (op1 op2 op3 : var_op),
    (op1 @ (op2 @ op3) = (op1 @ op2) @ op3)%var_op.
Proof. reflexivity. Qed.

Definition eq_var_op : relation var_op :=
  @pointwise_relation var var eq.

Notation "f =v= g" :=
  (eq_var_op (f)%var_op (g)%var_op) (at level 70).

Instance eq_var_op_equiv :
  Equivalence eq_var_op.
Proof.
  apply @Build_Equivalence; try easy.
  intros op1 op2 op3 Heq1 Heq2 v.
  rewrite Heq1, Heq2; easy.
Qed.

Add Parametric Morphism : var_op_compose
    with signature eq_var_op ==> eq_var_op ==> eq_var_op
      as var_op_compose_mor.
  intros * Heq1 * Heq2 v; unfold var_op_compose.
  rewrite Heq1, Heq2; easy.
Qed.

(* Lift [var -> var] function to avoid [bound 0] *)

Definition lift_var_op (op : var_op) : var_op :=
  fun v =>
    match v with
    | free n =>
      match op (free n) with
      | free n => free n
      | bound l => bound (S l)
      end
    | bound 0 => bound 0
    | bound (S l) =>
      match op (bound l) with
      | free n => free n
      | bound l => bound (S l)
      end
    end.

Add Parametric Morphism : lift_var_op
    with signature (eq_var_op ==> eq_var_op)
      as lift_var_op_mor.
  intros * Heq v; unfold lift_var_op.
  destruct v as [n|[|l]]; try rewrite Heq; easy.
Qed.

(* The core operations can be split into "pushes" that
   move things onto the "stack" of bound variables and
   "pops" that move things off of the stack of bound
   variables. *)

Definition pop_var v : var_op :=
  match v with
  | bound l => cycle_out_var l
  | free n => open_var n
  end.

Definition push_var vo : var_op :=
  match vo with
  | None => weak_var
  | Some (bound l) => cycle_in_var l
  | Some (free n) => close_var n
  end.

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

Definition shift_var_opt vo1 vo2 :=
  match vo1, vo2 with
  | None, vo2 => vo2
  | vo1, None => vo2
  | Some v1, Some v2 => Some (shift_var v1 v2)
  end.
Arguments shift_var_opt !vo1 !vo2.

Definition unshift_var_opt vo1 vo2 :=
  match vo1, vo2 with
  | None, vo2 => vo2
  | vo1, None => vo2
  | Some v1, Some v2 => Some (unshift_var v1 v2)
  end.
Arguments unshift_var_opt !vo1 !vo2.

Definition unshift_var_opt_var vo1 v2 :=
  match vo1 with
  | None => v2
  | Some v1 => unshift_var v1 v2
  end.
Arguments unshift_var_opt_var !vo1 v2.

Definition unshift_var_var_opt v1 vo2 :=
  match vo2 with
  | None => None
  | Some v2 => Some (unshift_var v1 v2)
  end.
Arguments unshift_var_var_opt v1 !vo2.
