Require Import String Omega StrictProp.
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
    if le_gt_dec (n_index n1) (n_index n2) then
      mkname (n_string n2) (S (n_index n2))
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

Definition less_than_le_neq {N M O} :
  N <= M ->
  M <> N ->
  less_than M (S O) ->
  less_than N O.
  intros Hle Hneq.
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

Set Primitive Projections.
Record level N := mklevel { l_nat : nat; l_less_than : less_than l_nat N }.
Add Printing Constructor level.
Unset Primitive Projections.
Arguments mklevel {N} l_nat l_less_than.
Arguments l_nat {N} l.
Arguments l_less_than {N} l.

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

Definition shift_level {N}
           (l1 : level N) (l2 : level (pred N)) : level N :=
  if le_gt_dec (l_nat l1) (l_nat l2) then l_S' l2
  else level_extend' l2.
Arguments shift_level {N} l1 l2 : simpl nomatch.

Definition unshift_level {N} (l1 : level N) (l2 : level (S N)) : level N :=
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
         (l1 : level (S N)) (l2 : level (S N))
  : Squash (l1 <> l2) -> level N :=
  match Compare_dec.le_gt_dec (l_nat l2) (l_nat l1) with
  | left le =>
    fun sneql =>
      mklevel (l_nat l2)
              (match sneql with
               | squash neql =>
                 less_than_le_neq le
                   (l_nat_injective neql)
                   (l_less_than l1)
               end)
  | right le =>
    fun sneql =>
      mklevel (pred (l_nat l2))
              (less_than_pred_le le (l_less_than l2))
  end.
Arguments unshift_level_neq {N} l1 l2 Hneq : simpl nomatch.

Definition cycle_in_level {N}
  : level N -> morph level N level N :=
  fun l1 V l2 =>
    match l2 with
    | mklevel 0 _ => level_extend_by V l1
    | mklevel (S l2') lt' =>
      shift_level (level_extend_by V l1)
                  (mklevel l2' (less_than_pred lt'))
    end.
Arguments cycle_in_level {N} l1 {V} l2 : simpl nomatch.

Definition cycle_out_level {N}
  : level N -> morph level N level N :=
  fun l1 V l2 =>
    if level_sdec (level_extend_by V l1) l2 then
      l_0' (squash (level_extend_by V l1))
    else (unshift_level (level_extend_by V l1) (l_S l2)).
Arguments cycle_out_level {N} l1 {V} l2 : simpl nomatch.

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

Definition cycle_in_var {N} (l : level N) : morph var N var N :=
  fun V v =>
    match v with
    | free n => free n
    | bound l2 => bound (cycle_in_level l l2)
    end.
Arguments cycle_in_var {N} l {V} v : simpl nomatch.

Definition cycle_out_var {N} (l : level N) : morph var N var N :=
  fun V v =>
    match v with
    | free n => free n
    | bound l2 => bound (cycle_out_level l l2)
    end.
Arguments cycle_out_var {N} l {V} v : simpl nomatch.

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

(* Algebra of operations on [var] *)

Inductive closing : nat -> nat -> Set :=
| closing_id : closing 0 0
| closing_weak : forall N M,
    level (S N) -> closing N M -> closing (S N) M
| closing_swap : forall N M,
    level (S N) -> closing N M -> level (S M) -> closing (S N) (S M)
| closing_close : forall N M,
    level (S N) -> closing N M -> name -> closing (S N) M.

Arguments closing_weak {N} {M} l r.
Arguments closing_swap {N} {M} l1 r l2.
Arguments closing_close {N} {M} l r n.

Fixpoint closing_weak_n {N} : closing N 0 :=
  match N return closing N _ with
  | 0 => closing_id
  | S N => closing_weak l_0 closing_weak_n
  end.

Fixpoint closing_weakening {N M} : closing (N + M) N :=
  match N return closing (N + _) N with
  | 0 => closing_weak_n
  | S N => closing_swap l_0 closing_weakening l_0
  end.

Fixpoint closing_id_n {N} : closing N N :=
  match N return closing N N with
  | 0 => closing_id
  | S N => closing_swap l_0 closing_id_n l_0
  end.

Inductive renaming (N : nat) : nat -> Set :=
| renaming_closing : forall M, closing N M -> renaming N M
| renaming_shift : forall M,
    name -> renaming N M -> renaming N M
| renaming_open : forall M,
    name -> renaming N M -> level (S M) ->
    renaming N (S M)
| renaming_rename : forall M,
    name -> renaming N M -> name -> renaming N M.

Arguments renaming_closing {N} {M} r.
Arguments renaming_shift {N} {M} n r.
Arguments renaming_open {N} {M} n r l.
Arguments renaming_rename {N} {M} n1 r n2.

Definition renaming_id :=
  renaming_closing closing_id.

Definition renaming_id_n {N} : renaming N N :=
  renaming_closing closing_id_n.

Fixpoint renaming_weak {N M}
         (l : level (S N)) (r : renaming N M) :
  renaming (S N) M :=
  match r in renaming _ M
        return renaming _ M
  with
  | renaming_closing r =>
    renaming_closing (closing_weak l r)
  | renaming_shift n r =>
    renaming_shift n (renaming_weak l r)
  | @renaming_open _ M n r l' =>
    renaming_open n (renaming_weak l r) l'
  | renaming_rename n1 r n2 =>
    renaming_rename n1 (renaming_weak l r) n2
  end.

Fixpoint renaming_swap {N M}
         (l1 : level (S N)) (r : renaming N M) :
  level (S M) -> renaming (S N) (S M) :=
  match r in renaming _ M
        return level (S M) -> renaming _ (S M)
  with
  | renaming_closing r =>
    fun l2 => renaming_closing (closing_swap l1 r l2)
  | renaming_shift n r =>
    fun l2 => renaming_shift n (renaming_swap l1 r l2)
  | @renaming_open _ M n r l =>
    fun l2 =>
      renaming_open
        n (renaming_swap l1 r (unshift_level l l2))
        (shift_level l2 l)
  | renaming_rename n1 r n2 =>
    fun l2 =>
      renaming_rename n1 (renaming_swap l1 r l2) n2
  end.

Fixpoint renaming_close {N M}
         (l : level (S N)) (r : renaming N M) (n : name) :
  renaming (S N) M :=
  match r in renaming _ M
        return renaming _ M
  with
  | renaming_closing r =>
    renaming_closing (closing_close l r n)
  | renaming_shift n' r =>
    renaming_shift n' (renaming_close l r n)
  | @renaming_open _ M n' r l' =>
    renaming_open n' (renaming_close l r n) l'
  | renaming_rename n1 r n2 =>
    renaming_rename
      n1 (renaming_close l r (unshift_name n2 n))
      (shift_name n n2)
  end.

Fixpoint apply_closing_var {N M} (r : closing N M)
  : morph var M var N :=
  match r in closing N M return morph _ M _ N with
  | closing_id => morph_id
  | @closing_weak N M l r =>
      (@cycle_out_var (S N) l)
      @ lift_morph_var (apply_closing_var r)
      @ morph_extend_by M (@weak_var)
  | @closing_swap N M l1 r l2 =>
        (@cycle_out_var (S N) l1)
      @ lift_morph_var (apply_closing_var r)
      @ @cycle_in_var (S M) l2
  | @closing_close N M l r n =>
        (@cycle_out_var (S N) l)
      @ lift_morph_var (apply_closing_var r)
      @ morph_extend_by M (@close_var n)
  end.

Fixpoint apply_renaming_var {N M}
         (r : renaming N M)
  : morph var M var N :=
  match r in renaming _ M
        return morph _ M _ _ with
  | renaming_closing r => apply_closing_var r
  | @renaming_shift _ M n r =>
      morph_extend_by N (@open_var n)
      @ lift_morph_var (apply_renaming_var r)
      @ morph_extend_by M (@weak_var)
  | @renaming_open _ M n r l =>
      morph_extend_by N (@open_var n)
      @ lift_morph_var (apply_renaming_var r)
      @ @cycle_in_var (S M) l
  | @renaming_rename _ M n1 r n2 =>
      morph_extend_by N (@open_var n1)
      @ lift_morph_var (apply_renaming_var r)
      @ morph_extend_by M (@close_var n2)
  end.

Inductive closing_rhs (N : nat) : nat -> Set :=
| closing_rhs_weak_rhs : forall M,
    closing N M -> closing_rhs N M
| closing_rhs_swap_rhs : forall M,
    closing N M -> level (S M) -> closing_rhs N (S M)
| closing_rhs_close_rhs : forall M,
    closing N M -> name -> closing_rhs N M.

Arguments closing_rhs_weak_rhs {N} {M} r.
Arguments closing_rhs_swap_rhs {N} {M} r l.
Arguments closing_rhs_close_rhs {N} {M} r n.

Definition closing_rhs_weak {N M}
  : level N -> closing_rhs (pred N) M -> closing_rhs N M :=
  match N
        return level N -> closing_rhs (pred N) _ -> closing_rhs N _
  with
  | 0 => fun l1 => False_rec _ (level_zero_empty l1)
  | S N' =>
    fun l1 r =>
      match r in closing_rhs _ M
            return closing_rhs (S N') M with
      | closing_rhs_weak_rhs r =>
        closing_rhs_weak_rhs (closing_weak l1 r)
      | closing_rhs_swap_rhs r l =>
        closing_rhs_swap_rhs (closing_weak l1 r) l
      | closing_rhs_close_rhs r n =>
        closing_rhs_close_rhs (closing_weak l1 r) n
      end
  end.

Definition closing_rhs_swap {N M}
  : level N -> closing_rhs (pred N) M
    -> level (S M) -> closing_rhs N (S M) :=
  match N
        return level N -> closing_rhs (pred N) _ ->
               _ -> closing_rhs N _
  with
  | 0 => fun l1 => False_rec _ (level_zero_empty l1)
  | S N' =>
    fun l1 r =>
      match r in closing_rhs _ M
            return level (S M) -> closing_rhs (S N') (S M) with
      | closing_rhs_weak_rhs r =>
        fun l2 => closing_rhs_weak_rhs (closing_swap l1 r l2)
      | closing_rhs_swap_rhs r l =>
        fun l2 =>
          closing_rhs_swap_rhs (closing_swap l1 r (unshift_level l l2))
                          (shift_level l2 l)
      | closing_rhs_close_rhs r n =>
        fun l2 => closing_rhs_close_rhs (closing_swap l1 r l2) n
      end
  end.

Definition closing_rhs_close {N M}
  : level N -> closing_rhs (pred N) M
    -> name -> closing_rhs N M :=
  match N
        return level N -> closing_rhs (pred N) _ ->
               _ -> closing_rhs N _
  with
  | 0 => fun l1 => False_rec _ (level_zero_empty l1)
  | S N' =>
    fun l1 r =>
      match r in closing_rhs _ M
            return _ -> closing_rhs _ M with
      | closing_rhs_weak_rhs r =>
        fun n1 => closing_rhs_weak_rhs (closing_close l1 r n1)
      | closing_rhs_swap_rhs r l =>
        fun n1 => closing_rhs_swap_rhs (closing_close l1 r n1) l
      | closing_rhs_close_rhs r n =>
        fun n1 =>
          closing_rhs_close_rhs (closing_close l1 r (unshift_name n n1))
                           (shift_name n1 n)
      end
  end.

Fixpoint transpose_level_closing {N M}
         (r : closing N M)
  : level N -> closing_rhs (pred N) M :=
  match r in closing N M
        return level N -> closing_rhs (pred N) M
  with
  | closing_id => fun l => False_rec _ (level_zero_empty l)
  | @closing_weak N' M' l1 r =>
    fun l =>
      match level_sdec l l1 with
      | sleft _ => closing_rhs_weak_rhs r
      | sright neq =>
        closing_rhs_weak
          (unshift_level_neq l l1 neq)
          (transpose_level_closing
             r (unshift_level_neq l1 l (sneq_sym neq)))
      end
  | closing_swap l1 r l2 =>
    fun l =>
      match level_sdec l l1 with
      | sleft _ => closing_rhs_swap_rhs r l2
      | sright neq =>
        closing_rhs_swap
          (unshift_level_neq l l1 neq)
          (transpose_level_closing
             r (unshift_level_neq l1 l (sneq_sym neq)))
          l2
      end
  | closing_close l1 r n =>
    fun l =>
      match level_sdec l l1 with
      | sleft _ => closing_rhs_close_rhs r n
      | sright neq =>
        closing_rhs_close
          (unshift_level_neq l l1 neq)
          (transpose_level_closing
             r (unshift_level_neq l1 l (sneq_sym neq)))
          n
      end
  end.

Definition transpose_level_closing' {N M}
         (r : closing (S N) M) l
  : closing_rhs N M :=
  transpose_level_closing r l.

Fixpoint transpose_name_closing {N M}
         (r : closing N M) n : closing_rhs N M :=
  match r in closing N M return closing_rhs N M with
  | closing_id => closing_rhs_close_rhs closing_id n
  | closing_weak l1 r =>
      closing_rhs_weak
        l1 (transpose_name_closing r n)
  | closing_swap l1 r l2 =>
      closing_rhs_swap
        l1 (transpose_name_closing r n) l2
  | closing_close l1 r n2 =>
      closing_rhs_close
        l1 (transpose_name_closing r n) n2
  end.

Fixpoint compose_closing {N M O}
         (r1 : closing O N) {struct r1}
  : closing N M -> closing O M :=
  match r1 in closing O' N'
        return closing N' _ -> closing O' _
  with
  | closing_id => fun r2 => r2
  | closing_weak l r1 =>
    fun r2 => closing_weak l (compose_closing r1 r2)
  | closing_swap l1 r1 l2 =>
    fun r2 =>
      match transpose_level_closing r2 l2 in closing_rhs _ M
            return closing _ M
       with
      | closing_rhs_weak_rhs r2 =>
          closing_weak l1 (compose_closing r1 r2)
      | closing_rhs_swap_rhs r2 l2 =>
          closing_swap l1 (compose_closing r1 r2) l2
      | closing_rhs_close_rhs r2 n =>
          closing_close l1 (compose_closing r1 r2) n
      end
  | @closing_close O'' N'' l r1 n =>
    fun (r2 : closing N'' M) =>
      match transpose_name_closing r2 n
            in closing_rhs _ M return closing _ M
      with
      | closing_rhs_weak_rhs r2 =>
          closing_weak l (compose_closing r1 r2)
      | closing_rhs_swap_rhs r2 l2 =>
          closing_swap l (compose_closing r1 r2) l2
      | closing_rhs_close_rhs r2 n =>
          closing_close l (compose_closing r1 r2) n
      end
  end.

Inductive renaming_rhs (N : nat) : nat -> Set :=
| renaming_rhs_shift_rhs : forall M,
    renaming N M -> renaming_rhs N M
| renaming_rhs_open_rhs : forall M,
    renaming N M -> level (S M) ->
    renaming_rhs N (S M)
| renaming_rhs_rename_rhs : forall M,
    renaming N M -> name ->
    renaming_rhs N M.

Arguments renaming_rhs_shift_rhs {N} {M} r.
Arguments renaming_rhs_open_rhs {N} {M} r l.
Arguments renaming_rhs_rename_rhs {N} {M} r n.

Definition renaming_rhs_shift {N M}
          n1 (r : renaming_rhs N M)
  : renaming_rhs N M :=
  match r in renaming_rhs _ M
        return renaming_rhs _ M with
  | renaming_rhs_shift_rhs r =>
      renaming_rhs_shift_rhs
        (renaming_shift n1 r)
  | renaming_rhs_open_rhs r l =>
      renaming_rhs_open_rhs
        (renaming_shift n1 r) l
  | renaming_rhs_rename_rhs r n =>
      renaming_rhs_rename_rhs
        (renaming_shift n1 r) n
  end.

Definition renaming_rhs_open {N M}
           n1 (r : renaming_rhs N M)
  : level (S M) -> renaming_rhs N (S M) :=
  match r in renaming_rhs _ M
        return level (S M) ->
               renaming_rhs _ (S M)
  with
  | renaming_rhs_shift_rhs r =>
    fun l1 =>
      renaming_rhs_shift_rhs
        (renaming_open n1 r l1)
  | renaming_rhs_open_rhs r l =>
    fun l1 =>
      renaming_rhs_open_rhs
        (renaming_open n1 r (unshift_level l l1))
        (shift_level l1 l)
  | renaming_rhs_rename_rhs r n =>
    fun l1 =>
      renaming_rhs_rename_rhs
        (renaming_open n1 r l1) n
  end.

Definition renaming_rhs_rename {N M}
           n1 (r : renaming_rhs N M) n2
  : renaming_rhs N M :=
  match r in renaming_rhs _ M
        return renaming_rhs _ M
  with
  | renaming_rhs_shift_rhs r =>
    renaming_rhs_shift_rhs
      (renaming_rename n1 r n2)
  | renaming_rhs_open_rhs r l =>
    renaming_rhs_open_rhs
      (renaming_rename n1 r n2) l
  | renaming_rhs_rename_rhs r n =>
    renaming_rhs_rename_rhs
      (renaming_rename n1 r (unshift_name n n2))
      (shift_name n2 n)
  end.

Fixpoint transpose_level_renaming {N M}
         l (r : renaming N M)
  : renaming_rhs (pred N) M :=
  match r in renaming _ M
        return renaming_rhs _ M
  with
  | renaming_closing r =>
      match transpose_level_closing r l
            in closing_rhs _ M'
            return renaming_rhs _ M'
      with
      | closing_rhs_weak_rhs r =>
        renaming_rhs_shift_rhs
          (renaming_closing r)
      | closing_rhs_swap_rhs r l =>
        renaming_rhs_open_rhs
          (renaming_closing r) l
      | closing_rhs_close_rhs r n =>
        renaming_rhs_rename_rhs
          (renaming_closing r) n
      end
  | renaming_shift n1 r =>
      renaming_rhs_shift n1
        (transpose_level_renaming l r)
  | renaming_open n1 r l2 =>
      renaming_rhs_open
        n1 (transpose_level_renaming l r) l2
  | renaming_rename n1 r n2 =>
      renaming_rhs_rename
        n1 (transpose_level_renaming l r) n2
  end.

Fixpoint transpose_name_renaming {N M}
         n (r : renaming N M)
  : renaming_rhs N M :=
  match r in renaming _ M
        return renaming_rhs _ M
  with
  | renaming_closing r =>
    match transpose_name_closing r n
          in closing_rhs _ M'
          return renaming_rhs _ M'
    with
    | closing_rhs_weak_rhs r =>
      renaming_rhs_shift_rhs
        (renaming_closing r)
    | closing_rhs_swap_rhs r l =>
      renaming_rhs_open_rhs
        (renaming_closing r) l
    | closing_rhs_close_rhs r n =>
      renaming_rhs_rename_rhs
        (renaming_closing r) n
    end
  | renaming_shift n1 r =>
    if name_eqb n n1 then
      renaming_rhs_shift_rhs r
    else
      renaming_rhs_shift
        (unshift_name n n1)
        (transpose_name_renaming (unshift_name n1 n) r)
  | renaming_open n1 r l2 =>
    if name_eqb n n1 then
      renaming_rhs_open_rhs r l2
    else
      renaming_rhs_open
        (unshift_name n n1)
        (transpose_name_renaming (unshift_name n1 n) r) l2
  | renaming_rename n1 r n2 =>
    if name_eqb n n1 then
      renaming_rhs_rename_rhs r n2
    else
      renaming_rhs_rename
        (unshift_name n n1)
        (transpose_name_renaming (unshift_name n1 n) r) n2
  end.

Fixpoint compose_closing_renaming {N M O}
         (r1 : closing O N) {struct r1}
  : renaming N M -> renaming O M :=
  match r1 in closing O' N'
        return renaming N' _ -> renaming O' _
  with
  | closing_id => fun r2 => r2
  | closing_weak l r1 =>
    fun r2 =>
      renaming_weak l
        (compose_closing_renaming r1 r2)
  | closing_swap l1 r1 l2 =>
    fun r2 =>
      match transpose_level_renaming l2 r2
             in renaming_rhs _ M
             return renaming _ M
      with
      | renaming_rhs_shift_rhs r2 =>
          renaming_weak
            l1 (compose_closing_renaming r1 r2)
      | renaming_rhs_open_rhs r2 l2 =>
          renaming_swap
            l1 (compose_closing_renaming r1 r2) l2
      | renaming_rhs_rename_rhs r2 n =>
          renaming_close
            l1 (compose_closing_renaming r1 r2) n
      end
  | closing_close l r1 n =>
    fun r2 =>
      match transpose_name_renaming n r2
            in renaming_rhs _ M
            return renaming _ M
       with
      | renaming_rhs_shift_rhs r2 =>
          renaming_weak
            l (compose_closing_renaming r1 r2)
      | renaming_rhs_open_rhs r2 l2 =>
          renaming_swap
            l (compose_closing_renaming r1 r2) l2
      | renaming_rhs_rename_rhs r2 n =>
          renaming_close
            l (compose_closing_renaming r1 r2) n
      end
  end.

Fixpoint compose_renamings {N M O} (r1 : renaming O N) {struct r1}
  : renaming N M -> renaming O M :=
  match r1 in renaming _ N'
        return renaming N' _ -> _
  with
  | renaming_closing r1 =>
    fun r2 =>
      compose_closing_renaming r1 r2
  | renaming_shift n r1 =>
    fun r2 =>
      renaming_shift n (compose_renamings r1 r2)
  | renaming_open n r1 l =>
    fun r2 =>
      match transpose_level_renaming l r2
             in renaming_rhs _ M
             return renaming _ M
      with
      | renaming_rhs_shift_rhs r2 =>
          renaming_shift
            n (compose_renamings r1 r2)
      | renaming_rhs_open_rhs r2 l2 =>
          renaming_open
            n (compose_renamings r1 r2) l2
      | renaming_rhs_rename_rhs r2 n2 =>
          renaming_rename
            n (compose_renamings r1 r2) n2
      end
  | renaming_rename n1 r1 n2 =>
    fun r2 =>
      match transpose_name_renaming n2 r2
            in renaming_rhs _ M
            return renaming _ M
       with
      | renaming_rhs_shift_rhs r2 =>
          renaming_shift
            n1 (compose_renamings r1 r2)
      | renaming_rhs_open_rhs r2 l =>
          renaming_open
            n1 (compose_renamings r1 r2) l
      | renaming_rhs_rename_rhs r2 n3 =>
          renaming_rename
            n1 (compose_renamings r1 r2) n3
      end
  end.

(* Reasoning about shifts and unshifts of names *)

Lemma reduce_shift_name_distinct n1 n2 :
  n_string n1 <> n_string n2 ->
  shift_name n1 n2 = n2.
Proof.
  intros; unfold shift_name.
  destruct (string_dec (n_string n1) (n_string n2)); subst;
    try contradiction; easy.
Qed.

Lemma reduce_shift_name_ge n1 n2 :
  n_string n1 = n_string n2 ->
  n_index n1 <= n_index n2 ->
  shift_name n1 n2 = mkname (n_string n2) (S (n_index n2)).
Proof.
  intros; unfold shift_name.
  destruct (string_dec (n_string n1) (n_string n2));
    try contradiction.
  destruct (le_gt_dec (n_index n1) (n_index n2));
    try easy; omega.
Qed.

Lemma reduce_shift_name_lt n1 n2 :
  n_string n1 = n_string n2 ->
  S (n_index n2) <= n_index n1 ->
  shift_name n1 n2 = n2.
Proof.
  intros; unfold shift_name.
  destruct (string_dec (n_string n1) (n_string n2));
    try contradiction.
  destruct (le_gt_dec (n_index n1) (n_index n2));
    try easy; omega.
Qed.

Lemma reduce_unshift_name_distinct n1 n2 :
  n_string n1 <> n_string n2 ->
  unshift_name n1 n2 = n2.
Proof.
  intros; unfold unshift_name.
  destruct (string_dec (n_string n1) (n_string n2)); subst;
    try contradiction; easy.
Qed.

Lemma reduce_unshift_name_gt n1 n2 :
  n_string n1 = n_string n2 ->
  S (n_index n1) <= n_index n2 ->
  unshift_name n1 n2 = mkname (n_string n2) (pred (n_index n2)).
Proof.
  intros; unfold unshift_name.
  destruct (string_dec (n_string n1) (n_string n2));
    try contradiction.
  destruct (le_gt_dec (n_index n2) (n_index n1));
    try easy; omega.
Qed.

Lemma reduce_unshift_name_le n1 n2 :
  n_string n1 = n_string n2 ->
  n_index n2 <= n_index n1 ->
  unshift_name n1 n2 = n2.
Proof.
  intros; unfold unshift_name.
  destruct (string_dec (n_string n1) (n_string n2));
    try contradiction.
  destruct (le_gt_dec (n_index n2) (n_index n1));
    try easy; omega.
Qed.

Lemma reduce_name_eqb_distinct n1 n2 :
  n_string n1 <> n_string n2 ->
  name_eqb n1 n2 = false.
Proof.
  intros; unfold name_eqb.
  destruct (name_dec n1 n2); try easy.
  destruct n1, n2; cbn in *; subst.
  congruence.
Qed.

Lemma reduce_name_eqb_eq n1 n2 :
  n_string n1 = n_string n2 ->
  n_index n1 = n_index n2 ->
  name_eqb n1 n2 = true.
Proof.
  intros; unfold name_eqb.
  destruct (name_dec n1 n2); try easy.
  destruct n1, n2; cbn in *; subst.
  contradiction.
Qed.

Lemma reduce_name_eqb_neq n1 n2 :
  n_index n1 <> n_index n2 ->
  name_eqb n1 n2 = false.
Proof.
  intros; unfold name_eqb.
  destruct (name_dec n1 n2); try easy.
  destruct n1, n2; cbn in *; subst.
  congruence.
Qed.

Hint Rewrite reduce_shift_name_distinct
     reduce_unshift_name_distinct
     reduce_name_eqb_distinct
     using (cbn; congruence) : reduce_names.

Hint Rewrite reduce_shift_name_ge reduce_shift_name_lt
     reduce_unshift_name_le reduce_unshift_name_gt
     reduce_name_eqb_eq reduce_name_eqb_neq
     using (cbn; try congruence; omega) : reduce_names.

Ltac reduce_names :=
  autorewrite with reduce_names in *; cbn in *.

Lemma reduce_non_zero_name {i} n :
  i < n_index n ->
  mkname (n_string n) (S (pred (n_index n))) = n.
Proof.
  intros; destruct n as [s i2], i2; cbn in *; easy.
Qed.

(* Useful lemma *)
Lemma red_name_neq n1 n2 :
  n_string n1 = n_string n2 ->
  n1 <> n2 <-> n_index n1 <> n_index n2.
Proof.
  intro Heq1; split.
  - intros Hneq Heq2; apply Hneq.
    change n1 with (mkname (n_string n1) (n_index n1)).
    rewrite Heq1, Heq2; easy.
  - intros Hneq Heq2; apply Hneq.
    rewrite Heq2; easy.
Qed.

Hint Rewrite red_name_neq using (cbn; congruence) : red_name_neq.

(* Case split on the order of the name parameters. *)
Ltac case_name n1 n2 :=
  destruct (string_dec (n_string n1) (n_string n2));
    [replace (n_string n2) with (n_string n1) by easy;
     autorewrite with red_name_neq in *;
     destruct (Compare_dec.lt_eq_lt_dec (n_index n1) (n_index n2))
        as [[|]|];
     [replace n2
        with (mkname (n_string n2) (S (pred (n_index n2))))
       by (apply (@reduce_non_zero_name (n_index n1)); easy)
     |replace n2 with n1
        by (change n1 with (mkname (n_string n1) (n_index n1));
            change n2 with (mkname (n_string n2) (n_index n2));
            congruence)
     |replace n1
        with (mkname (n_string n1) (S (pred (n_index n1))))
       by (apply (@reduce_non_zero_name (n_index n2)); easy) ]
    |];
    reduce_names;
    change (mkname (n_string n1) (n_index n1)) with n1;
    change (mkname (n_string n2) (n_index n2)) with n2;
    try contradiction; try omega.

Lemma open_close_identity (n : name) :
  @open_var n @ @close_var n =m= 1.
Proof.
  intros V v; unfold open_var, close_var.
  destruct v as [n2|?]; cbn; try easy.
  case_name n n2; easy.
Qed.

Lemma close_open_identity (n : name) :
  @close_var n @ @open_var n =m= 1.
Proof.
  intros V v; unfold open_var, close_var.
  destruct v as [n2|l2]; cbn.
  - case_name n n2; easy.
  - destruct l2 as [n3 lt2]; cbn in *.
    destruct n3; try easy.
    case_name n n; easy.
Qed.

(* Reasoning about shifts and unshifts of levels *)

Lemma reduce_shift_level_ge {N} (l1 : level N) l2 :
  l_nat l1 <= l_nat l2 ->
  shift_level l1 l2 = l_S' l2.
Proof.
  intros; unfold shift_level.
  destruct (le_gt_dec (l_nat l1) (l_nat l2));
    try easy; omega.
Qed.

Lemma reduce_shift_level_lt {N} (l1 : level N) l2 :
  S (l_nat l2) <= l_nat l1 ->
  shift_level l1 l2 = level_extend' l2.
Proof.
  intros; unfold shift_level.
  destruct (le_gt_dec (l_nat l1) (l_nat l2));
    try easy; omega.
Qed.

Lemma reduce_unshift_level_gt {N} (l1 : level N) l2 :
  forall (le : S (l_nat l1) <= l_nat l2),
  unshift_level l1 l2
  = mklevel (pred (l_nat l2))
            (less_than_pred_le le (l_less_than l2)).
Proof.
  intros; unfold unshift_level.
  destruct (le_gt_dec (l_nat l2) (l_nat l1));
    try easy; omega.
Qed.

Lemma reduce_unshift_level_le {N} (l1 : level N) l2 :
  forall (le : l_nat l2 <= l_nat l1),
  unshift_level l1 l2
  = mklevel (l_nat l2) (less_than_le le (l_less_than l1)).
Proof.
  intros; unfold unshift_level.
  destruct (le_gt_dec (l_nat l2) (l_nat l1));
    try easy; omega.
Qed.

Lemma reduce_unshift_level_neq_gt {N}
      (l1 : level (S N)) l2 (neq : l1 <> l2) :
  forall (le : S (l_nat l1) <= l_nat l2),
  unshift_level_neq l1 l2 (squash neq)
  = mklevel (pred (l_nat l2))
            (less_than_pred_le le (l_less_than l2)).
Proof.
  intros; unfold unshift_level_neq.
  destruct (le_gt_dec (l_nat l2) (l_nat l1));
    try easy; omega.
Qed.

Lemma reduce_unshift_level_neq_le {N}
      (l1 : level (S N)) l2 (neq : l1 <> l2) :
  forall (le : l_nat l2 <= l_nat l1),
  unshift_level_neq l1 l2 (squash neq) =
    mklevel (l_nat l2)
      (less_than_le_neq le (l_nat_injective neq)
         (l_less_than l1)).
Proof.
  intros; unfold unshift_level_neq.
  destruct (le_gt_dec (l_nat l2) (l_nat l1));
    try easy; omega.
Qed.

Lemma reduce_level_sdec_eq {N} (l1 : level N) l2 :
  forall (eql : l_nat l1 = l_nat l2),
  level_sdec l1 l2 = sleft (squash (lift_level_eq eql)).
Proof.
  intros; unfold level_sdec, level_dec.
  destruct (Nat.eq_dec (l_nat l1) (l_nat l2)) as [eql2|neql]; easy.
Qed.

Lemma reduce_level_sdec_neq {N} (l1 : level N) l2 :
  forall (neql : l_nat l1 <> l_nat l2),
  level_sdec l1 l2 = sright (squash (lift_level_neq neql)).
Proof.
  intros; unfold level_sdec, level_dec.
  destruct (Nat.eq_dec (l_nat l1) (l_nat l2)) as [eql|neql2]; easy.
Qed.

Definition reduce_level_irrelevant {N} (l : level N) :
  forall (lt : less_than (l_nat l) N),
    mklevel (l_nat l) lt = l :=
  fun _ => eq_refl.

Hint Rewrite @reduce_level_irrelevant : reduce_level_irrelevant.

Ltac reduce_levels_step :=
  cbn;
  try rewrite @reduce_shift_level_ge by (cbn in *; omega);
  try rewrite @reduce_shift_level_lt by (cbn in *; omega);
  try
    (unshelve
       (eassert (_ <= _) as le by shelve;
        rewrite (reduce_unshift_level_le _ _ le) in *);
       [> cbn in *; omega|]);
  try
    (unshelve
       (eassert (_ <= _) as le by shelve;
        rewrite (reduce_unshift_level_gt _ _ le) in *);
       [> cbn in *; omega|]);
  try
    (unshelve
       (eassert (_ <= _) as le by shelve;
        rewrite (reduce_unshift_level_neq_le _ _ _ le) in *);
       [> cbn in *; omega|]);
  try
    (unshelve
       (eassert (_ <= _) as le by shelve;
        rewrite (reduce_unshift_level_neq_gt _ _ _ le) in *);
       [> cbn in *; omega|]);
  try
    (unshelve
       (eassert (_ = (_ : nat)) as eql by shelve;
        rewrite (reduce_level_sdec_eq _ _ eql) in *);
       [> cbn in *; omega|]);
  try
    (unshelve
       (eassert (_ <> (_ : nat)) as neql by shelve;
        rewrite (reduce_level_sdec_neq _ _ neql) in *);
       [> cbn in *; omega|]).

Ltac reduce_levels :=
  try repeat reduce_levels_step;
  cbn in *; autorewrite with reduce_level_irrelevant.

(* Case split on the order of the level parameters. *)
Ltac case_level l1 l2 :=
  let Heq := fresh "Heq" in
  destruct (Compare_dec.lt_eq_lt_dec (l_nat l1) (l_nat l2))
    as [[|Heq]|];
  [|replace l2
      with (mklevel (l_nat l1)
             (less_than_cast (eq_sym Heq) (l_less_than l2)))
      by (apply lift_level_eq; easy);
    replace (l_nat l2) with (l_nat l1) by easy;
    cbn in Heq;
    try destruct (Heq)|];
  reduce_levels; try omega.

Lemma cycle_in_cycle_out_identity N (l : level N) :
  @cycle_in_var _ l @ @cycle_out_var _ l =m= 1.
Proof.
  intros V v.
  destruct v as [?|l2]; cbn; try easy.
  unfold cycle_in_level, cycle_out_level.
  case_level l l2; try easy.
  destruct l2 as [n2 lt2]; cbn in *.
  destruct n2; reduce_levels; easy.
Qed.

Lemma cycle_out_cycle_in_identity N (l : level N) :
  @cycle_out_var _ l @ @cycle_in_var _ l =m= 1.
Proof.
  intros V v.
  destruct v as [?|l2]; cbn; try easy.
  unfold cycle_in_level, cycle_out_level.
  destruct l as [n1 lt1]; cbn in *.
  destruct l2 as [n2 lt2]; cbn in *.
  destruct n2; reduce_levels; try easy.
  case_level
    (mklevel n1 (less_than_extend_by V lt1))
    (mklevel n2 (less_than_pred lt2)); easy.
Qed.

Definition apply_closing_rhs_var {N M} (r : closing_rhs N M)
  : morph var M var (S N) :=
  match r in closing_rhs _ M return morph _ M _ _ with
  | @closing_rhs_weak_rhs _ M r =>
      lift_morph_var (apply_closing_var r)
      @ morph_extend_by M (@weak_var)
  | @closing_rhs_swap_rhs _ M r l2 =>
      lift_morph_var (apply_closing_var r)
      @ @cycle_in_var (S M) l2
  | @closing_rhs_close_rhs _ M r n =>
      lift_morph_var (apply_closing_var r)
      @ morph_extend_by M (@close_var n)
  end.

Definition morph_id_succ_pred {N} :
  level N -> morph var N var (S (pred N)) :=
  match N return level N -> morph _ N _ (S (pred N)) with
  | 0 => fun l => False_rec _ (level_zero_empty l)
  | S N => fun _ => morph_id
  end.

Lemma apply_transpose_level_closing_aux N M
      (r : closing N M) (l : level N):
  morph_id_succ_pred l
  @ (@cycle_in_var _ l)
  @ apply_closing_var r
  =m=
  apply_closing_rhs_var (transpose_level_closing r l).
Proof.
  induction r; cbn; try rewrite morph_left_identity.
  - exfalso; apply (level_zero_empty l).
  - destruct (level_dec l l0); subst; cbn.
    + admit.
    + destruct N.
      * admit.
      * admit.
  - destruct (level_dec l l1); subst; cbn.
    + admit.
    + destruct N.
      * admit.
      * admit.
  - destruct (level_dec l l1); subst; cbn.
    + admit.
    + destruct N.
      * admit.
      * admit.
Admitted.

Lemma apply_transpose_level_closing N M
      (r : closing (S N) M) (l : level (S N)):
  (@cycle_in_var _ l)
  @ apply_closing_var r
  =m=
  apply_closing_rhs_var (transpose_level_closing r l).
Proof.
  rewrite <- apply_transpose_level_closing_aux; cbn.
  rewrite morph_left_identity.
  easy.
Qed.

Inductive substitution (term : nset) (N : nat) : nat -> Set :=
| substitution_renaming : forall M,
    renaming N M -> substitution term N M
| substitution_bind : forall M,
    term N -> substitution term N M -> level (S M) ->
    substitution term N (S M)
| substitution_subst : forall M,
    term N -> substitution term N M ->
    name -> substitution term N M.

Arguments substitution_renaming {term} {N} {M} r.
Arguments substitution_bind {term} {N} {M} t r l.
Arguments substitution_subst {term} {N} {M} t r n.

(*

Declare Scope ren_scope.
Delimit Scope ren_scope with ren.

Notation "r ; ^ a" := (r_shift a r)
  (at level 47, left associativity) : ren_scope.
Notation "r ; a <- b" := (r_rename a r b)
  (at level 47, left associativity, a at next level)
  : ren_scope.
Notation "r ; u // a" := (r_subst u r a)
  (at level 47, left associativity, u at next level)
  : ren_scope.
Notation "r ; a" := (r_rename a r a)
  (at level 47, left associativity) : ren_scope.
Notation "^ a" := (r_shift a r_id)
  (at level 47, left associativity) : ren_scope.
Notation "a <- b" := (r_rename a r_id b)
  (at level 47, left associativity) : ren_scope.
Notation "u // a" := (r_subst u r_id a)
  (at level 47, left associativity) : ren_scope.

*)
