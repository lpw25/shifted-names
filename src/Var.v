Require Import String PeanoNat Compare_dec
        StrictProp Setoid Morphisms.
Require Import Morph.
Arguments string_dec !s1 !s2.

(* Some utilities for working with SProp *)

Inductive ssumbool (A B:SProp) : Set :=
  | sleft : A -> ssumbool A B
  | sright : B -> ssumbool A B.
Arguments sleft {A B} a.
Arguments sright {A B} b.


Definition sneq_sym {A} {x y : A} :
  Squash (x <> y) -> Squash (y <> x) :=
  fun sneq =>
    match sneq with
    | squash neq => squash (fun eql => neq (eq_sym eql))
    end.
Arguments sneq_sym {A} {x} {y} sneq : simpl never.

(* Name indices are [nat]s *)

Definition index := nat.

Definition index_dec := Nat.eq_dec.

(* Free names are a pair of a string and an index *)

Set Primitive Projections.
Record name := mkname { n_string : string; n_index : index }.
Add Printing Constructor name.
Unset Primitive Projections.

Definition name_of_string s := mkname s 0.
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
  change (mkname (n_string n) (n_index n)) with n.

Ltac eta_reduce_names :=
  try repeat
      match goal with
      | |- context [mkname (n_string ?n) (n_index ?n)] =>
        eta_reduce_name n
      end.

Ltac eta_expand_name n :=
  change n with (mkname (n_string n) (n_index n)).

Definition n_S n :=
  (mkname (n_string n) (S (n_index n))).
Arguments n_S n /.

Definition name_dec n1 n2 : {n1 = n2} + {n1 <> n2} :=
  match string_dec (n_string n1) (n_string n2) with
  | left s_eql =>
    match index_dec (n_index n1) (n_index n2) with
    | left i_eql =>
      left
        (eq_trans (f_equal (fun s => mkname s (n_index n1)) s_eql)
             (f_equal (fun i => mkname (n_string n2) i) i_eql))
    | right i_neql =>
      right (fun eql =>
             i_neql (eq_ind_r
                       (fun n => n_index n = n_index n2)
                       eq_refl eql))
    end
  | right s_neql =>
      right (fun eql =>
             s_neql (eq_ind_r
                       (fun n => n_string n = n_string n2)
                       eq_refl eql))
  end.

Definition name_eqb n1 n2 : bool :=
  match name_dec n1 n2 with
  | left _ => true
  | right _ => false
  end.

Definition shift_name n1 n2 :=
  if string_dec (n_string n1) (n_string n2) then
    if le_gt_dec (n_index n1) (n_index n2) then n_S n2
    else n2
  else n2.
Arguments shift_name n1 n2 : simpl nomatch.

Definition unshift_name n1 n2 :=
  if string_dec (n_string n1) (n_string n2) then
    if Compare_dec.le_gt_dec (n_index n2) (n_index n1) then n2
    else mkname (n_string n2) (pred (n_index n2))
  else n2.
Arguments unshift_name n1 n2 : simpl nomatch.

(* Bound variables are represented by a level *)

Inductive less_than : nat -> nat -> SProp :=
 | less_than_zero :
     forall N, less_than 0 (S N)
 | less_than_succ :
     forall N M, less_than N M -> less_than (S N) (S M).
Arguments less_than_zero {N}.
Arguments less_than_succ {N M} lt.

Notation lt_0 := less_than_zero.
Notation lt_S := less_than_succ.

Notation lt_1 := (lt_S lt_0).
Notation lt_2 := (lt_S lt_1).
Notation lt_3 := (lt_S lt_2).
Notation lt_4 := (lt_S lt_3).
Notation lt_5 := (lt_S lt_4).
Notation lt_6 := (lt_S lt_5).
Notation lt_7 := (lt_S lt_6).
Notation lt_8 := (lt_S lt_7).
Notation lt_9 := (lt_S lt_8).

Fixpoint less_than_extend {N M} (lt : less_than N M) :
  less_than N (S M) :=
  match lt in less_than N M return less_than N (S M) with
  | lt_0 => lt_0
  | lt_S lt' => lt_S (less_than_extend lt')
  end.

Fixpoint less_than_extend_by {N M} V (lt : less_than N M) :
  less_than N (M + V) :=
  match lt in less_than N M return less_than N (M + V) with
  | lt_0 => lt_0
  | lt_S lt' => lt_S (less_than_extend_by V lt')
  end.

Definition lt_0_empty {N} : less_than N 0 -> False.
  intro Hlt.
  apply sEmpty_rec.
  inversion Hlt.
Defined.

Definition lt_0' {N M}
  : less_than N M -> less_than 0 M :=
  match M return less_than _ M
                 -> less_than _ M with
  | 0 => fun l => False_sind _ (lt_0_empty l)
  | S M => fun l => lt_0
  end.

Definition lt_S' {N M}
  : less_than N (pred M) -> less_than (S N) M :=
  match M return less_than _ (pred M)
                 -> less_than _ M with
  | 0 => fun l => False_sind _ (lt_0_empty l)
  | S M => fun l => lt_S l
  end.

Definition less_than_extend' {N M} :
  less_than N (pred M) -> less_than N M :=
  match M return less_than _ (pred M)
                 -> less_than _ M with
  | 0 => fun l => False_sind _ (lt_0_empty l)
  | S M => fun l => less_than_extend l
  end.

Definition less_than_pred {N M} (lt : less_than (S M) N)
  : less_than M (pred N).
  inversion lt.
  easy.
Defined.

Definition less_than_pred_le {N M O} :
   S N <= M ->
   less_than M O ->
   less_than (pred M) (pred O).
  intros Hle Hlt.
  destruct Hle.
  - apply (less_than_pred Hlt).
  - apply (less_than_pred Hlt).
Defined.

Definition less_than_le {N M O} :
  N <= M ->
  less_than M O ->
  less_than N O.
  intros Hle.
  generalize dependent O.
  induction Hle.
  - intros O Hlt; exact Hlt.
  - intros O Hlt.
    apply IHHle.
    inversion Hlt as [|? ? Hlt2].
    apply less_than_extend.
    apply Hlt2.
Defined.

Definition less_than_le_sneq {N M O} :
  N <= M ->
  Squash (M <> N) ->
  less_than M O ->
  less_than N (pred O).
  intros Hle [Hneq].
  assert (N < M) as Hle2.
  { inversion Hle.
    - subst; easy.
    - apply le_n_S.
      easy. }
  clear Hle Hneq.
  generalize dependent O.
  induction Hle2.
  - intros O Hlt.
    inversion Hlt as [|? ? Hlt2].
    apply Hlt2.
  - intros O Hlt.
    apply IHHle2.
    inversion Hlt as [|? ? Hlt2].
    subst.
    apply less_than_extend.
    apply Hlt2.
Defined.

Definition less_than_cast {N M O} :
  N = M ->
  less_than N O ->
  less_than M O :=
  fun Heq =>
    match Heq in eq _ M
          return _ -> less_than M _
    with
    | eq_refl => fun l => l
    end.

Definition less_than_succ_pred_le {N M O} :
   S N <= M ->
   less_than M O ->
   less_than (S (pred M)) O.
  intros Hle Hlt.
  destruct M; easy.
Defined.

Definition less_than_succ_pred {N M} :
  less_than N M ->
  less_than N (S (pred M)).
  intros Hlt.
  destruct M; easy.
Defined.
Arguments less_than_succ_pred {N !M} lt.

Set Primitive Projections.
Record level N := mklevel { l_nat : nat; l_less_than : less_than l_nat N }.
Add Printing Constructor level.
Unset Primitive Projections.
Arguments mklevel {N} l_nat l_less_than.
Arguments l_nat {N} l.
Arguments l_less_than {N} l.

Ltac eta_reduce_level l :=
  change (mklevel (l_nat l) (l_less_than l)) with l.

Ltac eta_reduce_levels :=
  try repeat
      match goal with
      | |- context [mklevel (l_nat ?l) (l_less_than ?l)] =>
        eta_reduce_level l
      end.

Ltac eta_expand_level l :=
  change l with (mklevel (l_nat l) (l_less_than l)).

Definition lift_level_eq {N M O} :
  forall (Heq : N = M) (lt1 : less_than N O) (lt2 : less_than M O),
    mklevel N lt1 = mklevel M lt2 :=
  fun Heq =>
    match Heq in eq _ M'
          return
          forall (lt1 : less_than N O) (lt2 : less_than M' O),
            mklevel _ lt1 = mklevel M' lt2
    with
    | eq_refl => fun lt1 lt2 => eq_refl
    end.
Arguments lift_level_eq {N M O} Heq {lt1 lt2}.

Definition lift_level_neq {N M O}
  (Hneq : N <> M) (lt1 : less_than N O) (lt2 : less_than M O) :
  mklevel N lt1 <> mklevel M lt2 :=
  fun Heq => Hneq (f_equal l_nat Heq).
Arguments lift_level_neq {N M O} Hneq {lt1 lt2}.

Definition l_nat_injective {N} {l1 l2 : level N} :
  l1 <> l2 ->
  l_nat l1 <> l_nat l2 :=
  fun Hneq Heq =>
    Hneq (lift_level_eq Heq).

Definition l_nat_sinjective {N} {l1 l2 : level N} :
  Squash (l1 <> l2) ->
  Squash (l_nat l1 <> l_nat l2) :=
  fun Hsneq =>
    match Hsneq with
    | squash Hneq =>
      squash (l_nat_injective Hneq)
    end.

Notation l_0 := (mklevel 0 lt_0).
Notation l_S l :=
  (mklevel (S (l_nat l)) (lt_S (l_less_than l))).

Notation l_1 := (mklevel 1 lt_1).
Notation l_2 := (mklevel 2 lt_2).
Notation l_3 := (mklevel 3 lt_3).
Notation l_4 := (mklevel 4 lt_4).
Notation l_5 := (mklevel 5 lt_5).
Notation l_6 := (mklevel 6 lt_6).
Notation l_7 := (mklevel 7 lt_7).
Notation l_8 := (mklevel 8 lt_8).
Notation l_9 := (mklevel 9 lt_9).

Definition level_extend {N} : level N -> level (S N) :=
  fun l => mklevel (l_nat l) (less_than_extend (l_less_than l)).
Arguments level_extend {N} l /.

Definition level_extend_by {N} V : level N -> level (N + V) :=
  fun l => mklevel (l_nat l) (less_than_extend_by V (l_less_than l)).
Arguments level_extend_by {N} V l /.

Definition l_0' {N} (l : Squash (level N)) : level N :=
  mklevel 0 (match l with
             | squash l => lt_0' (l_less_than l)
             end).

Definition l_S' {N} (l : level (pred N)) : level N :=
  mklevel (S (l_nat l)) (lt_S' (l_less_than l)).
Arguments l_S' {N} l /.

Definition level_extend' {N} : level (pred N) -> level N :=
  fun l => mklevel (l_nat l) (less_than_extend' (l_less_than l)).
Arguments level_extend' {N} l /.

Definition level_zero_empty : level 0 -> False :=
  fun l => lt_0_empty (l_less_than l).

Definition level_dec {N} (l1 : level N) (l2 : level N) :
    {l1 = l2} + {l1 <> l2} :=
  match Nat.eq_dec (l_nat l1) (l_nat l2) with
  | left Heq =>
    left (lift_level_eq Heq)
  | right Hneq =>
    right (lift_level_neq Hneq)
  end.

Definition level_sdec {N} (l1 : level N) (l2 : level N) :
    ssumbool (Squash (l1 = l2)) (Squash (l1 <> l2)) :=
  match level_dec l1 l2 with
  | left Heq => sleft (squash Heq)
  | right Hneq => sright (squash Hneq)
  end.

Definition level_succ_pred {N} (l : level N) :=
  mklevel (l_nat l) (less_than_succ_pred (l_less_than l)).
Arguments level_succ_pred {N} l /.

Definition shift_level {N}
           (l1 : level N) (l2 : level (pred N)) : level N :=
  if le_gt_dec (l_nat l1) (l_nat l2) then l_S' l2
  else level_extend' l2.
Arguments shift_level {N} l1 l2 : simpl nomatch.

Definition unshift_level {N} (l1 : level (pred N)) (l2 : level N) : level (pred N) :=
  match Compare_dec.le_gt_dec (l_nat l2) (l_nat l1) with
  | left le =>
    mklevel (l_nat l2)
            (less_than_le le (l_less_than l1))
  | right le =>
    mklevel (pred (l_nat l2))
            (less_than_pred_le le (l_less_than l2))
  end.
Arguments unshift_level {N} l1 l2 : simpl nomatch.

Definition unshift_level_neq {N}
         (l1 : level N) (l2 : level N)
  : Squash (l1 <> l2) -> level (pred N) :=
  match Compare_dec.le_gt_dec (l_nat l2) (l_nat l1) with
  | left le =>
    fun sneql =>
      mklevel (l_nat l2)
              (less_than_le_sneq le
                 (l_nat_sinjective sneql)
                 (l_less_than l1))
  | right le =>
    fun sneql =>
      mklevel (pred (l_nat l2))
              (less_than_pred_le le (l_less_than l2))
  end.
Arguments unshift_level_neq {N} l1 l2 Hneq : simpl nomatch.

Definition cycle_out_level {N}
  : level N -> morph level N level N :=
  fun l1 V l2 =>
    match l2 with
    | mklevel 0 _ => level_extend_by V l1
    | mklevel (S l2') lt' =>
      shift_level (level_extend_by V l1)
                  (mklevel l2' (less_than_pred lt'))
    end.
Arguments cycle_out_level {N} l1 {V} l2 : simpl nomatch.

Definition cycle_in_level {N}
  : level N -> morph level N level N :=
  fun l1 V l2 =>
    if level_sdec (level_extend_by V l1) l2 then
      l_0' (squash (level_extend_by V l1))
    else @unshift_level (S N + V)
           (level_extend_by V l1) (l_S l2).
Arguments cycle_in_level {N} l1 {V} l2 : simpl nomatch.

Definition swap_level
  : morph level 2 level 2 :=
  fun V l =>
    match l with
    | mklevel 0 _ => l_1
    | mklevel 1 _ => l_0
    | l => l
    end.
Arguments swap_level {V} l : simpl nomatch.

(* Variables are either free names or bound levels *)

Inductive var (V : nat) :=
| free (n : name)
| bound (l : level V).

Arguments free {V} n.
Arguments bound {V} l.

Definition open_var n : morph var 1 var 0 :=
  fun V v =>
    match v with
    | free n2 => free (shift_name n n2)
    | bound (mklevel 0 _) => free n
    | bound (mklevel (S l') lt') =>
      bound (mklevel l' (less_than_pred lt'))
    end.
Arguments open_var n {V} v : simpl nomatch.

Definition close_var n : morph var 0 var 1 :=
  fun V v =>
    match v with
    | free n2 =>
      if name_eqb n n2 then bound l_0
      else free (unshift_name n n2)
    | bound l => bound (l_S l)
    end.
Arguments close_var n {V} v : simpl nomatch.

Definition weak_var : morph var 0 var 1 :=
  fun V v =>
    match v with
    | free n => free n
    | bound l => bound (l_S l)
    end.
Arguments weak_var {V} v : simpl nomatch.

Definition cycle_out_var {N} (l : level N) : morph var N var N :=
  fun V v =>
    match v with
    | free n => free n
    | bound l2 => bound (cycle_out_level l l2)
    end.
Arguments cycle_out_var {N} l {V} v : simpl nomatch.

Definition cycle_in_var {N} (l : level N) : morph var N var N :=
  fun V v =>
    match v with
    | free n => free n
    | bound l2 => bound (cycle_in_level l l2)
    end.
Arguments cycle_in_var {N} l {V} v : simpl nomatch.

Definition swap_var : morph var 2 var 2 :=
  fun V v =>
    match v with
    | free n => free n
    | bound l => bound (swap_level l)
    end.
Arguments swap_var {V} v : simpl nomatch.

Definition lift_morph_var {N M} (m : morph var M var N) :
  morph var (S M) var (S N) :=
  fun V v =>
    match v with
    | free n =>
      match m V (free n) with
      | free n => free n
      | bound l => bound (l_S l)
      end
    | bound (mklevel 0 _) => bound l_0
    | bound (mklevel (S l) lt') =>
      match m V (bound (mklevel l (less_than_pred lt'))) with
      | free n => free n
      | bound l => bound (l_S l)
      end
    end.

Add Parametric Morphism {N M} : (@lift_morph_var N M)
    with signature (eq_morph ==> eq_morph)
      as lift_morph_var_mor.
  intros * Heq V v; unfold lift_morph_var.
  destruct v as [n|[[|ln] lt]]; try rewrite Heq; easy.
Qed.
