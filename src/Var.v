Require Import String Omega StrictProp.
Require Import Morph.
Arguments string_dec !s1 !s2.

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
Bind Scope string_scope with name.

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

Definition Zero := Empty_set.

Inductive Succ {S : Set} : Set := succ0 | succS (s : S).

Fixpoint level (V : nat) : Set :=
  match V with
  | 0 => Zero
  | S V => @Succ (level V)
  end.
Arguments level V : simpl never.

Definition l0 {V} : level (S V) := succ0.
Definition lS {V} : level V -> level (S V) := succS.

Fixpoint level_extend {V} : level V -> level (S V) :=
  match V return level V -> level (S V) with
  | 0 => fun l => Empty_set_rec _ l
  | S V =>
    fun l =>
      match l with
      | succ0 => l0
      | succS s => lS (@level_extend V s)
      end
  end.
Arguments level_extend {V} !l.

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
    | bound succ0 => free n
    | bound (succS l) => bound l
    end.
Arguments open_var n {V} v : simpl nomatch.

Definition close_var n : morph var 0 var 1 :=
  fun V v =>
    match v with
    | free n2 =>
      if name_dec n n2 then bound l0
      else free (unshift_name n n2)
    | bound l => bound (lS l)
    end.
Arguments close_var n {V} v : simpl nomatch.

Definition weak_var : morph var 0 var 1 :=
  fun V v =>
    match v with
    | free n => free n
    | bound l => bound (lS l)
    end.
Arguments weak_var {V} v : simpl nomatch.

(* Algebra of operations on [var 0] *)

Inductive renaming (term : nset) :=
| r_id
| r_shift (n : name) (r : renaming term)
| r_rename (n1 : name) (r : renaming term) (n2 : name)
| r_subst (t : term 0) (r : renaming term) (n : name).

Arguments r_id {term}.
Arguments r_shift {term} n r.
Arguments r_rename {term} n1 r n2.
Arguments r_subst {term} t r n.

(* Left-hand sides of renamings *)

Inductive pop (term : nset) : Type :=
| p_open : name -> pop term
| p_bind : term 0 -> pop term.
Arguments p_open {term} n.
Arguments p_bind {term} t.

Definition r_pop_weak {term} (p : @pop term) r :=
  match p with
  | p_open n => @r_shift term n r
  | p_bind _ => r
  end.
Arguments r_pop_weak {term} !p r.

Definition r_pop_close {term} (p : @pop term) r n :=
  match p with
  | p_open n2 => @r_rename term n2 r n
  | p_bind t => r_subst t r n
  end.
Arguments r_pop_close {term} !p r n.

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

Fixpoint static {term} (r : renaming term) : SProp :=
  match r with
  | r_id => sUnit
  | r_shift b r => static r
  | r_rename b r a => static r
  | r_subst u r a => sEmpty
  end.

Fixpoint apply_renaming_var {term} (r : renaming term)
  : static r -> morph var 0 var 0 :=
  match r return static r -> morph var 0 var 0 with
  | r_id => fun _ => morph_id
  | r_shift n r =>
    fun s =>
      (@open_var n
       @ morph_extend (apply_renaming_var r s)
       @ @weak_var)%morph
  | r_rename n1 r n2 =>
    fun s =>
      (@open_var n1
       @ morph_extend (apply_renaming_var r s)
       @ @close_var n2)%morph
  | r_subst t r n => sEmpty_rect _
  end.
