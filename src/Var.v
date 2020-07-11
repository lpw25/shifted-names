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

Inductive Succ (S : Set) : Set := succ0 | succS (s : S).
Arguments succ0 {S}.
Arguments succS {S} s.

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

Fixpoint level_extend_by {N} V : level N -> level (N + V) :=
  match N return level N -> level (N + V) with
  | 0 => fun l => Empty_set_rec _ l
  | S N =>
    fun l =>
      match l with
      | succ0 => l0
      | succS s => lS (@level_extend_by N V s)
      end
  end.
Arguments level_extend_by {N} V !l.

Fixpoint lSn N {V} : level V -> level (N + V) :=
  fun l =>
    match N with
    | 0 => l
    | S N => lS (lSn N l)
    end.

Definition is_succS {N} (l : level (S N)) :=
  match l with
  | succ0 => False
  | succS _ => True
  end.

Definition discriminate_level {N} (l : level N) :
  succ0 <> succS l :=
  fun eql =>
    eq_ind (succS l) is_succS I succ0 (eq_sym eql).

Definition inv_succS {N} l1 (l2 : level (S N)) :=
  match l2 with
  | succS l2' => l1 = l2'
  | succ0 => False
  end.

Definition injective_succS {N} (l1 l2 : level N) :
  succS l1 = succS l2 -> l1 = l2 :=
  fun eql =>
    eq_ind (succS l1) (inv_succS l1) eq_refl (succS l2) eql.

Definition level_one_eq {l1 l2 : level 1} : l1 = l2 :=
  match l1, l2 return l1 = l2 with
  | succ0, succ0 => eq_refl
  | succS l1', _ =>
    Empty_set_ind (fun _ => succS l1' = l2) l1'
  | _, succS l2' =>
    Empty_set_ind (fun _ => succ0 = succS l2') l2'
  end.

Fixpoint level_dec {N} :
  forall (l1 : level N) (l2 : level N),
    {l1 = l2} + {l1 <> l2} :=
  match N return
        forall (l1 : level N) (l2 : level N),
          {l1 = l2} + {l1 <> l2}
  with
  | 0 =>
    fun (l1 : level 0) l2 =>
      Empty_set_rec (fun l => {l = l2} + {l <> l2}) l1
  | S N =>
    fun l1 l2 =>
      match l1 return {l1 = l2} + {l1 <> l2} with
      | succ0 =>
        match l2 return {succ0 = l2} + {succ0 <> l2} with
        | succ0 => left eq_refl
        | succS l2' => right (discriminate_level l2')
        end
      | succS l1' =>
        match l2 return {lS l1' = l2} + {lS l1' <> l2} with
        | succ0 =>
          right (fun eql => discriminate_level l1' (eq_sym eql))
        | succS l2' =>
          match level_dec l1' l2' with
          | left eql => left (f_equal lS eql)
          | right neql =>
            right (fun eql => neql (injective_succS l1' l2' eql))
          end
        end
      end
  end.

Fixpoint shift_level {N}
  : level (S N) -> level N -> level (S N) :=
  match N return level (S N) -> level N -> level (S N) with
  | 0 => fun l1 l2 => Empty_set_rec _ l2
  | S _ =>
    fun l1 l2 =>
      match l1 with
      | succ0 => lS l2
      | succS l1' =>
        match l2 with
        | succ0 => level_extend l2
        | succS l2' => lS (shift_level l1' l2')
        end
      end
    end.
Arguments shift_level {N} l1 l2 : simpl nomatch.

Fixpoint unshift_level {N} :
  level N -> level (S N) -> level N :=
  match N return level N -> level (S N) -> level N with
  | 0 => fun l1 => Empty_set_rec _ l1
  | S N' =>
    fun l1 l2 =>
      match l1, l2 with
      | _, succ0 => l0
      | succ0, succS l2' => l2'
      | succS l1, succS l2 => lS (unshift_level l1 l2)
      end
  end.
Arguments unshift_level {N} l1 l2 : simpl nomatch, rename.

Definition pred_level {N} :
  level (S (S N)) -> level (S N) :=
  fun l =>
    match l with
    | succ0 => succ0
    | succS l => l
    end.

Fixpoint unshift_level_neq {N} :
  forall (l1 : level (S N)) (l2 : level (S N)),
    l1 <> l2 -> level N :=
  match N return
        forall (l1 : level (S N)) (l2 : level (S N)),
          l1 <> l2 -> level N
  with
  | 0 =>
    fun l1 l2 neq => False_rec _ (neq level_one_eq)
  | S N =>
    fun l1 l2 =>
      match l1, l2 return l1 <> l2 -> level (S N) with
      | _, succ0 => fun _ => succ0
      | succ0, succS l2' => fun _ => l2'
      | succS l1, succS l2 =>
        fun neq =>
          lS (unshift_level_neq l1 l2
                (fun eq => neq (f_equal succS eq)))
      end
  end.

Arguments unshift_level {N} l1 l2 : simpl nomatch, rename.

Definition cycle_in_level {N} :=
  match N return level N -> morph level N level N with
  | 0 => fun l => Empty_set_rec _ l
  | S N =>
    fun l1 V l2 =>
      match l2 with
      | succ0 => level_extend_by V l1
      | succS l2 => shift_level (level_extend_by V l1) l2
      end
  end.
Arguments cycle_in_level {N} l1 {V} l2 : simpl nomatch.

Definition cycle_out_level {N} :=
  match N return level N -> morph level N level N with
  | 0 => fun l => Empty_set_rec _ l
  | S N' =>
    fun l1 V l2 =>
      if level_dec (level_extend_by V l1) l2 then l0
      else (unshift_level (level_extend_by V l1) (lS l2))
  end.
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
      | bound l => bound (lS l)
      end
    | bound succ0 => bound l0
    | bound (succS l) =>
      match m V (bound l) with
      | free n => free n
      | bound l => bound (lS l)
      end
    end.

(* Algebra of operations on [var] *)

Inductive pushes : nat -> nat -> Set :=
| pushes_id : pushes 0 0
| pushes_weak : forall N M,
    level (S N) -> pushes N M -> pushes (S N) M
| pushes_swap : forall N M,
    level (S N) -> pushes N M -> level (S M) -> pushes (S N) (S M)
| pushes_close : forall N M,
    level (S N) -> pushes N M -> name -> pushes (S N) M.

Arguments pushes_weak {N} {M} l r.
Arguments pushes_swap {N} {M} l1 r l2.
Arguments pushes_close {N} {M} l r n.

Fixpoint pushes_weak_n {N} : pushes N 0 :=
  match N return pushes N 0 with
  | 0 => pushes_id
  | S N => pushes_weak l0 pushes_weak_n
  end.

Fixpoint pushes_weakening {N M} : pushes (N + M) N :=
  match N return pushes (N + M) N with
  | 0 => pushes_weak_n
  | S N => pushes_swap l0 pushes_weakening l0
  end.

Fixpoint pushes_id_n {N} : pushes N N :=
  match N return pushes N N with
  | 0 => pushes_id
  | S N => pushes_swap l0 pushes_id_n l0
  end.

Inductive static_renaming (N : nat) : nat -> Set :=
| static_renaming_pushes : forall M, pushes N M -> static_renaming N M
| static_renaming_shift : forall M,
    name -> static_renaming N M -> static_renaming N M
| static_renaming_open : forall M,
    name -> static_renaming N M -> level (S M) ->
    static_renaming N (S M)
| static_renaming_rename : forall M,
    name -> static_renaming N M -> name -> static_renaming N M.

Arguments static_renaming_pushes {N} {M} r.
Arguments static_renaming_shift {N} {M} n r.
Arguments static_renaming_open {N} {M} n r l.
Arguments static_renaming_rename {N} {M} n1 r n2.

Definition static_renaming_id :=
  static_renaming_pushes pushes_id.

Fixpoint static_renaming_weak {N M}
         (l : level (S N)) (r : static_renaming N M) :
  static_renaming (S N) M :=
  match r in static_renaming _ M
        return static_renaming (S N) M
  with
  | static_renaming_pushes r =>
    static_renaming_pushes (pushes_weak l r)
  | static_renaming_shift n r =>
    static_renaming_shift n (static_renaming_weak l r)
  | @static_renaming_open _ M n r l' =>
    static_renaming_open n (static_renaming_weak l r) l'
  | static_renaming_rename n1 r n2 =>
    static_renaming_rename n1 (static_renaming_weak l r) n2
  end.

Fixpoint static_renaming_swap {N M}
         (l1 : level (S N)) (r : static_renaming N M) :
  level (S M) -> static_renaming (S N) (S M) :=
  match r in static_renaming _ M
        return level (S M) -> static_renaming (S N) (S M)
  with
  | static_renaming_pushes r =>
    fun l2 => static_renaming_pushes (pushes_swap l1 r l2)
  | static_renaming_shift n r =>
    fun l2 => static_renaming_shift n (static_renaming_swap l1 r l2)
  | @static_renaming_open _ M n r l =>
    fun l2 =>
      static_renaming_open
        n (static_renaming_swap l1 r (unshift_level l l2))
        (shift_level l2 l)
  | static_renaming_rename n1 r n2 =>
    fun l2 =>
      static_renaming_rename n1 (static_renaming_swap l1 r l2) n2
  end.

Fixpoint static_renaming_close {N M}
         (l : level (S N)) (r : static_renaming N M) (n : name) :
  static_renaming (S N) M :=
  match r in static_renaming _ M
        return static_renaming (S N) M
  with
  | static_renaming_pushes r =>
    static_renaming_pushes (pushes_close l r n)
  | static_renaming_shift n' r =>
    static_renaming_shift n' (static_renaming_close l r n)
  | @static_renaming_open _ M n' r l' =>
    static_renaming_open n' (static_renaming_close l r n) l'
  | static_renaming_rename n1 r n2 =>
    static_renaming_rename
      n1 (static_renaming_close l r (unshift_name n2 n))
      (shift_name n n2)
  end.

Fixpoint apply_pushes_var {N M} (r : pushes N M)
  : morph var M var N :=
  match r in pushes N M return morph var M var N with
  | pushes_id => morph_id
  | @pushes_weak N M l r =>
      (@cycle_out_var (S N) l)
      @ lift_morph_var (apply_pushes_var r)
      @ morph_extend_by M (@weak_var)
  | @pushes_swap N M l1 r l2 =>
        (@cycle_out_var (S N) l1)
      @ lift_morph_var (apply_pushes_var r)
      @ @cycle_in_var (S M) l2
  | @pushes_close N M l r n =>
        (@cycle_out_var (S N) l)
      @ lift_morph_var (apply_pushes_var r)
      @ morph_extend_by M (@close_var n)
  end.

Fixpoint apply_static_renaming_var {N M}
         (r : static_renaming N M)
  : morph var M var N :=
  match r in static_renaming _ M
        return morph var M var N with
  | static_renaming_pushes r => apply_pushes_var r
  | @static_renaming_shift _ M n r =>
      morph_extend_by N (@open_var n)
      @ lift_morph_var (apply_static_renaming_var r)
      @ morph_extend_by M (@weak_var)
  | @static_renaming_open _ M n r l =>
      morph_extend_by N (@open_var n)
      @ lift_morph_var (apply_static_renaming_var r)
      @ @cycle_in_var (S M) l
  | @static_renaming_rename _ M n1 r n2 =>
      morph_extend_by N (@open_var n1)
      @ lift_morph_var (apply_static_renaming_var r)
      @ morph_extend_by M (@close_var n2)
  end.

Inductive pushes_rhs : nat -> nat -> Set :=
| pushes_rhs_weak : forall N M,
    pushes N M -> pushes_rhs (S N) M
| pushes_rhs_swap : forall N M,
    pushes N M -> level (S M) -> pushes_rhs (S N) (S M)
| pushes_rhs_close : forall N M,
    pushes N M -> name -> pushes_rhs (S N) M.

Arguments pushes_rhs_weak {N} {M} r.
Arguments pushes_rhs_swap {N} {M} r l.
Arguments pushes_rhs_close {N} {M} r n.

Definition pushes_rhs_add_weak {N M} (r : pushes_rhs N M)
  : level N -> pushes_rhs (S N) M :=
  match r in pushes_rhs N M
        return level N -> pushes_rhs (S N) M with
  | pushes_rhs_weak r =>
    fun l1 => pushes_rhs_weak (pushes_weak l1 r)
  | pushes_rhs_swap r l =>
    fun l1 => pushes_rhs_swap (pushes_weak l1 r) l
  | pushes_rhs_close r n =>
    fun l1 => pushes_rhs_close (pushes_weak l1 r) n
  end.

Definition pushes_rhs_add_swap {N M} (r : pushes_rhs N M)
  : level N -> level (S M) -> pushes_rhs (S N) (S M) :=
  match r in pushes_rhs N M
        return level N -> level (S M) -> pushes_rhs (S N) (S M) with
  | pushes_rhs_weak r =>
    fun l1 l2 => pushes_rhs_weak (pushes_swap l1 r l2)
  | pushes_rhs_swap r l =>
    fun l1 l2 =>
      pushes_rhs_swap (pushes_swap l1 r (unshift_level l l2))
                      (shift_level l2 l)
  | pushes_rhs_close r n =>
    fun l1 l2 => pushes_rhs_close (pushes_swap l1 r l2) n
  end.

Definition pushes_rhs_add_close {N M} (r : pushes_rhs N M)
  : level N -> name -> pushes_rhs (S N) M :=
  match r in pushes_rhs N M
        return level N -> name -> pushes_rhs (S N) M with
  | pushes_rhs_weak r =>
    fun l1 n1 => pushes_rhs_weak (pushes_close l1 r n1)
  | pushes_rhs_swap r l =>
    fun l1 n1 => pushes_rhs_swap (pushes_close l1 r n1) l
  | pushes_rhs_close r n =>
    fun l1 n1 =>
      pushes_rhs_close (pushes_close l1 r (unshift_name n n1))
                       (shift_name n1 n)
  end.

Fixpoint transpose_level_pushes {N M}
         (r : pushes N M) : level N -> pushes_rhs N M :=
  match r in pushes N M return level N -> pushes_rhs N M with
  | pushes_id => fun l => Empty_set_rec _ l
  | pushes_weak l1 r =>
    fun l =>
      if level_dec l l1 then pushes_rhs_weak r
      else
        pushes_rhs_add_weak
          (transpose_level_pushes r (unshift_level l1 l))
          (unshift_level l l1) r
  | pushes_swap l1 r l2 =>
    fun l =>
      if level_dec l l1 then pushes_rhs_swap r l2
      else
        pushes_rhs_add_swap
          (transpose_level_pushes r (unshift_level l1 l))
          (unshift_level l l1) r l2
  | pushes_close l1 r n =>
    fun l =>
      if level_dec l l1 then pushes_rhs_close r n
      else
        pushes_rhs_add_close
          (transpose_level_pushes r (unshift_level l1 l))
          (unshift_level l l1) r n
  end.

Fixpoint transpose_level_pushes_left {N M}
         (l : level N) (r : pushes N M) :=
  match r with
  | pushes_id => pushes_id
  | pushes_weak l2 r =>
      if level_dec l l2 then r
      else transpose_level

Fixpoint compose_pushes {N M O}
         (r1 : pushes O N) (r2 : pushes N M) : pushes O M :=
  match r1 with
  | pushes_id => r2
  | pushes_weak l r1 =>
    pushes_weak l (compose_pushes r1 r2)
  | pushes_swap l1 r1 l2 =>
    
  | pushes_close l r1 n =>



Inductive renaming (term : nset) (N : nat) : nat -> Set :=
| renaming_static : forall M, static_renaming N M -> renaming term N M
| renaming_bind : forall M,
    term N -> renaming term N M -> level (S M) ->
    renaming term N (S M)
| renaming_subst : forall M,
    term N -> renaming term N M -> name -> renaming term N M.

Arguments renaming_static {term} {N} {M} r.
Arguments renaming_bind {term} {N} {M} t r l.
Arguments renaming_subst {term} {N} {M} t r n.

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
