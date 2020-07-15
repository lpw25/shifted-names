Require Import String Omega StrictProp.
Require Import Morph.
Arguments string_dec !s1 !s2.

(* Useful conversion *)

Definition neq_sym {A} {x y : A} :
  x <> y -> y <> x :=
  fun neq eql => neq (eq_sym eql).

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

Inductive less_than : nat -> nat -> SProp :=
 | less_than_zero :
     forall N, less_than 0 (S N)
 | less_than_succ :
     forall N M, less_than N M -> less_than (S N) (S M).
Arguments less_than_zero {N}.
Arguments less_than_succ {N M} lt.

Fixpoint less_than_extend {N M} (lt : less_than N M) :
  less_than N (S M) :=
  match lt in less_than N M return less_than N (S M) with
  | less_than_zero => less_than_zero
  | less_than_succ lt' => less_than_succ (less_than_extend lt')
  end.

Fixpoint less_than_extend_by {N M} V (lt : less_than N M) :
  less_than N (M + V) :=
  match lt in less_than N M return less_than N (M + V) with
  | less_than_zero => less_than_zero
  | less_than_succ lt' => less_than_succ (less_than_extend_by V lt')
  end.

Definition less_than_zero_empty {N} : less_than N 0 -> False.
  intro Hlt.
  apply sEmpty_rec.
  inversion Hlt.
Defined.

Definition less_than_zero' {N M}
  : less_than N M -> less_than 0 M :=
  match M return less_than _ M
                 -> less_than _ M with
  | 0 => fun l => False_sind _ (less_than_zero_empty l)
  | S M => fun l => less_than_zero
  end.

Definition less_than_succ' {N M}
  : less_than N (pred M) -> less_than (S N) M :=
  match M return less_than _ (pred M)
                 -> less_than _ M with
  | 0 => fun l => False_sind _ (less_than_zero_empty l)
  | S M => fun l => less_than_succ l
  end.

Definition less_than_extend' {N M} :
  less_than N (pred M) -> less_than N M :=
  match M return less_than _ (pred M)
                 -> less_than _ M with
  | 0 => fun l => False_sind _ (less_than_zero_empty l)
  | S M => fun l => less_than_extend l
  end.

Definition less_than_pred {N M} (lt : less_than (S M) N)
  : less_than M (pred N).
  inversion lt.
  easy.
Defined.

Definition less_than_pred_le {N M O} :
   S N <= M ->
   less_than M (S O) ->
   less_than (pred M) O.
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

Set Primitive Projections.
Record level N := mklevel { l_nat : nat; l_less_than : less_than l_nat N }.
Add Printing Constructor level.
Unset Primitive Projections.
Arguments mklevel {N} l_nat l_less_than.
Arguments l_nat {N} l.
Arguments l_less_than {N} l.

Definition lift_level_eq {N M O} :
  forall (Heq : N = M) (lt : less_than N O),
    mklevel N lt = mklevel M (less_than_cast Heq lt) :=
  fun Heq =>
    match Heq in eq _ M'
          return
          forall (lt : less_than N O),
            mklevel _ lt = mklevel M' (less_than_cast Heq lt)
    with
    | eq_refl => fun lt => eq_refl
    end.
Arguments lift_level_eq {N M O} Heq {lt}.

Definition l_nat_injective {N} {l1 l2 : level N} :
  l1 <> l2 ->
  l_nat l1 <> l_nat l2 :=
  fun Hneq Heq =>
    Hneq (lift_level_eq Heq).

Definition l0 {N} : level (S N) := mklevel 0 less_than_zero.
Definition lS {N} (l : level N) : level (S N) :=
  mklevel (S (l_nat l)) (less_than_succ (l_less_than l)).

Definition level_extend {N} : level N -> level (S N) :=
  fun l => mklevel (l_nat l) (less_than_extend (l_less_than l)).
Arguments level_extend {N} l.

Definition level_extend_by {N} V : level N -> level (N + V) :=
  fun l => mklevel (l_nat l) (less_than_extend_by V (l_less_than l)).
Arguments level_extend_by {N} V l.

Definition l0' {N} (l : Squash (level N)) : level N :=
  mklevel 0 (match l with
             | squash l => less_than_zero' (l_less_than l)
             end).

Definition lS' {N} (l : level (pred N)) : level N :=
  mklevel (S (l_nat l)) (less_than_succ' (l_less_than l)).

Definition level_extend' {N} : level (pred N) -> level N :=
  fun l => mklevel (l_nat l) (less_than_extend' (l_less_than l)).
Arguments level_extend' {N} l.

Definition level_zero_empty : level 0 -> False :=
  fun l => less_than_zero_empty (l_less_than l).

Definition level_dec {N} (l1 : level N) (l2 : level N) :
    {l1 = l2} + {l1 <> l2} :=
  match Nat.eq_dec (l_nat l1) (l_nat l2) with
  | left Heq =>
    left (lift_level_eq Heq)
  | right Hneq =>
    right (fun Heq => Hneq (f_equal l_nat Heq))
  end.

Definition shift_level {N}
           (l1 : level N) (l2 : level (pred N)) : level N :=
  if le_gt_dec (l_nat l1) (l_nat l2) then lS' l2
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
    if level_dec (level_extend_by V l1) l2 then
      l0' (squash (level_extend_by V l1))
    else (unshift_level (level_extend_by V l1) (lS l2)).
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
    | bound (mklevel 0 _) => bound l0
    | bound (mklevel (S l) lt') =>
      match m V (bound (mklevel l (less_than_pred lt'))) with
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
  match N return pushes N _ with
  | 0 => pushes_id
  | S N => pushes_weak l0 pushes_weak_n
  end.

Fixpoint pushes_weakening {N M} : pushes (N + M) N :=
  match N return pushes (N + _) N with
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
        return static_renaming _ M
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
        return level (S M) -> static_renaming _ (S M)
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
        return static_renaming _ M
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
  match r in pushes N M return morph _ M _ N with
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
        return morph _ M _ _ with
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

Inductive pushes_rhs (N : nat) : nat -> Set :=
| pushes_rhs_weak_rhs : forall M,
    pushes N M -> pushes_rhs N M
| pushes_rhs_swap_rhs : forall M,
    pushes N M -> level (S M) -> pushes_rhs N (S M)
| pushes_rhs_close_rhs : forall M,
    pushes N M -> name -> pushes_rhs N M.

Arguments pushes_rhs_weak_rhs {N} {M} r.
Arguments pushes_rhs_swap_rhs {N} {M} r l.
Arguments pushes_rhs_close_rhs {N} {M} r n.

Definition pushes_rhs_weak {N M}
  : level N -> pushes_rhs (pred N) M -> pushes_rhs N M :=
  match N
        return level N -> pushes_rhs (pred N) _ -> pushes_rhs N _
  with
  | 0 => fun l1 => False_rec _ (level_zero_empty l1)
  | S N' =>
    fun l1 r =>
      match r in pushes_rhs _ M
            return pushes_rhs (S N') M with
      | pushes_rhs_weak_rhs r =>
        pushes_rhs_weak_rhs (pushes_weak l1 r)
      | pushes_rhs_swap_rhs r l =>
        pushes_rhs_swap_rhs (pushes_weak l1 r) l
      | pushes_rhs_close_rhs r n =>
        pushes_rhs_close_rhs (pushes_weak l1 r) n
      end
  end.

Definition pushes_rhs_swap {N M}
  : level N -> pushes_rhs (pred N) M
    -> level (S M) -> pushes_rhs N (S M) :=
  match N
        return level N -> pushes_rhs (pred N) _ ->
               _ -> pushes_rhs N _
  with
  | 0 => fun l1 => False_rec _ (level_zero_empty l1)
  | S N' =>
    fun l1 r =>
      match r in pushes_rhs _ M
            return level (S M) -> pushes_rhs (S N') (S M) with
      | pushes_rhs_weak_rhs r =>
        fun l2 => pushes_rhs_weak_rhs (pushes_swap l1 r l2)
      | pushes_rhs_swap_rhs r l =>
        fun l2 =>
          pushes_rhs_swap_rhs (pushes_swap l1 r (unshift_level l l2))
                          (shift_level l2 l)
      | pushes_rhs_close_rhs r n =>
        fun l2 => pushes_rhs_close_rhs (pushes_swap l1 r l2) n
      end
  end.

Definition pushes_rhs_close {N M}
  : level N -> pushes_rhs (pred N) M
    -> name -> pushes_rhs N M :=
  match N
        return level N -> pushes_rhs (pred N) _ ->
               _ -> pushes_rhs N _
  with
  | 0 => fun l1 => False_rec _ (level_zero_empty l1)
  | S N' =>
    fun l1 r =>
      match r in pushes_rhs _ M
            return _ -> pushes_rhs _ M with
      | pushes_rhs_weak_rhs r =>
        fun n1 => pushes_rhs_weak_rhs (pushes_close l1 r n1)
      | pushes_rhs_swap_rhs r l =>
        fun n1 => pushes_rhs_swap_rhs (pushes_close l1 r n1) l
      | pushes_rhs_close_rhs r n =>
        fun n1 =>
          pushes_rhs_close_rhs (pushes_close l1 r (unshift_name n n1))
                           (shift_name n1 n)
      end
  end.

Fixpoint transpose_level_pushes {N M}
         (r : pushes N M)
  : level N -> pushes_rhs (pred N) M :=
  match r in pushes N M
        return level N -> pushes_rhs (pred N) M
  with
  | pushes_id => fun l => False_rec _ (level_zero_empty l)
  | @pushes_weak N' M' l1 r =>
    fun l =>
      match level_dec l l1 with
      | left _ => pushes_rhs_weak_rhs r
      | right neq =>
        pushes_rhs_weak
          (unshift_level_neq l l1 (squash neq))
          (transpose_level_pushes
             r (unshift_level_neq l1 l (squash (neq_sym neq))))
      end
  | pushes_swap l1 r l2 =>
    fun l =>
      match level_dec l l1 with
      | left _ => pushes_rhs_swap_rhs r l2
      | right neq =>
        pushes_rhs_swap
          (unshift_level_neq l l1 (squash neq))
          (transpose_level_pushes
             r (unshift_level_neq l1 l (squash (neq_sym neq))))
          l2
      end
  | pushes_close l1 r n =>
    fun l =>
      match level_dec l l1 with
      | left _ => pushes_rhs_close_rhs r n
      | right neq =>
        pushes_rhs_close
          (unshift_level_neq l l1 (squash neq))
          (transpose_level_pushes
             r (unshift_level_neq l1 l (squash (neq_sym neq))))
          n
      end
  end.

Fixpoint transpose_name_pushes {N M}
         (r : pushes N M) n : pushes_rhs N M :=
  match r in pushes N M return pushes_rhs N M with
  | pushes_id => pushes_rhs_close_rhs pushes_id n
  | pushes_weak l1 r =>
      pushes_rhs_weak
        l1 (transpose_name_pushes r n)
  | pushes_swap l1 r l2 =>
      pushes_rhs_swap
        l1 (transpose_name_pushes r n) l2
  | pushes_close l1 r n2 =>
      pushes_rhs_close
        l1 (transpose_name_pushes r n) n2
  end.

Fixpoint compose_pushes {N M O}
         (r1 : pushes O N) {struct r1}
  : pushes N M -> pushes O M :=
  match r1 in pushes O' N'
        return pushes N' _ -> pushes O' _
  with
  | pushes_id => fun r2 => r2
  | pushes_weak l r1 =>
    fun r2 => pushes_weak l (compose_pushes r1 r2)
  | pushes_swap l1 r1 l2 =>
    fun r2 =>
      match transpose_level_pushes r2 l2 in pushes_rhs _ M
            return pushes _ M
       with
      | pushes_rhs_weak_rhs r2 =>
          pushes_weak l1 (compose_pushes r1 r2)
      | pushes_rhs_swap_rhs r2 l2 =>
          pushes_swap l1 (compose_pushes r1 r2) l2
      | pushes_rhs_close_rhs r2 n =>
          pushes_close l1 (compose_pushes r1 r2) n
      end
  | @pushes_close O'' N'' l r1 n =>
    fun (r2 : pushes N'' M) =>
      match transpose_name_pushes r2 n
            in pushes_rhs _ M return pushes _ M
      with
      | pushes_rhs_weak_rhs r2 =>
          pushes_weak l (compose_pushes r1 r2)
      | pushes_rhs_swap_rhs r2 l2 =>
          pushes_swap l (compose_pushes r1 r2) l2
      | pushes_rhs_close_rhs r2 n =>
          pushes_close l (compose_pushes r1 r2) n
      end
  end.

Inductive static_renaming_rhs (N : nat) : nat -> Set :=
| static_renaming_rhs_shift_rhs : forall M,
    static_renaming N M -> static_renaming_rhs N M
| static_renaming_rhs_open_rhs : forall M,
    static_renaming N M -> level (S M) ->
    static_renaming_rhs N (S M)
| static_renaming_rhs_rename_rhs : forall M,
    static_renaming N M -> name ->
    static_renaming_rhs N M.

Arguments static_renaming_rhs_shift_rhs {N} {M} r.
Arguments static_renaming_rhs_open_rhs {N} {M} r l.
Arguments static_renaming_rhs_rename_rhs {N} {M} r n.

Definition static_renaming_rhs_shift {N M}
          n1 (r : static_renaming_rhs N M)
  : static_renaming_rhs N M :=
  match r in static_renaming_rhs _ M
        return static_renaming_rhs _ M with
  | static_renaming_rhs_shift_rhs r =>
      static_renaming_rhs_shift_rhs
        (static_renaming_shift n1 r)
  | static_renaming_rhs_open_rhs r l =>
      static_renaming_rhs_open_rhs
        (static_renaming_shift n1 r) l
  | static_renaming_rhs_rename_rhs r n =>
      static_renaming_rhs_rename_rhs
        (static_renaming_shift n1 r) n
  end.

Definition static_renaming_rhs_open {N M}
           n1 (r : static_renaming_rhs N M)
  : level (S M) -> static_renaming_rhs N (S M) :=
  match r in static_renaming_rhs _ M
        return level (S M) ->
               static_renaming_rhs _ (S M)
  with
  | static_renaming_rhs_shift_rhs r =>
    fun l1 =>
      static_renaming_rhs_shift_rhs
        (static_renaming_open n1 r l1)
  | static_renaming_rhs_open_rhs r l =>
    fun l1 =>
      static_renaming_rhs_open_rhs
        (static_renaming_open n1 r (unshift_level l l1))
        (shift_level l1 l)
  | static_renaming_rhs_rename_rhs r n =>
    fun l1 =>
      static_renaming_rhs_rename_rhs
        (static_renaming_open n1 r l1) n
  end.

Definition static_renaming_rhs_rename {N M}
           n1 (r : static_renaming_rhs N M) n2
  : static_renaming_rhs N M :=
  match r in static_renaming_rhs _ M
        return static_renaming_rhs _ M
  with
  | static_renaming_rhs_shift_rhs r =>
    static_renaming_rhs_shift_rhs
      (static_renaming_rename n1 r n2)
  | static_renaming_rhs_open_rhs r l =>
    static_renaming_rhs_open_rhs
      (static_renaming_rename n1 r n2) l
  | static_renaming_rhs_rename_rhs r n =>
    static_renaming_rhs_rename_rhs
      (static_renaming_rename n1 r (unshift_name n n2))
      (shift_name n2 n)
  end.

Fixpoint transpose_level_static_renaming {N M}
         l (r : static_renaming N M)
  : static_renaming_rhs (pred N) M :=
  match r in static_renaming _ M
        return static_renaming_rhs _ M
  with
  | static_renaming_pushes r =>
      match transpose_level_pushes r l
            in pushes_rhs _ M'
            return static_renaming_rhs _ M'
      with
      | pushes_rhs_weak_rhs r =>
        static_renaming_rhs_shift_rhs
          (static_renaming_pushes r)
      | pushes_rhs_swap_rhs r l =>
        static_renaming_rhs_open_rhs
          (static_renaming_pushes r) l
      | pushes_rhs_close_rhs r n =>
        static_renaming_rhs_rename_rhs
          (static_renaming_pushes r) n
      end
  | static_renaming_shift n1 r =>
      static_renaming_rhs_shift n1
        (transpose_level_static_renaming l r)
  | static_renaming_open n1 r l2 =>
      static_renaming_rhs_open
        n1 (transpose_level_static_renaming l r) l2
  | static_renaming_rename n1 r n2 =>
      static_renaming_rhs_rename
        n1 (transpose_level_static_renaming l r) n2
  end.

Fixpoint transpose_name_static_renaming {N M}
         n (r : static_renaming N M)
  : static_renaming_rhs N M :=
  match r in static_renaming _ M
        return static_renaming_rhs _ M
  with
  | static_renaming_pushes r =>
    match transpose_name_pushes r n
          in pushes_rhs _ M'
          return static_renaming_rhs _ M'
    with
    | pushes_rhs_weak_rhs r =>
      static_renaming_rhs_shift_rhs
        (static_renaming_pushes r)
    | pushes_rhs_swap_rhs r l =>
      static_renaming_rhs_open_rhs
        (static_renaming_pushes r) l
    | pushes_rhs_close_rhs r n =>
      static_renaming_rhs_rename_rhs
        (static_renaming_pushes r) n
    end
  | static_renaming_shift n1 r =>
    if name_dec n n1 then
      static_renaming_rhs_shift_rhs r
    else
      static_renaming_rhs_shift
        (unshift_name n n1)
        (transpose_name_static_renaming (unshift_name n1 n) r)
  | static_renaming_open n1 r l2 =>
    if name_dec n n1 then
      static_renaming_rhs_open_rhs r l2
    else
      static_renaming_rhs_open
        (unshift_name n n1)
        (transpose_name_static_renaming (unshift_name n1 n) r) l2
  | static_renaming_rename n1 r n2 =>
    if name_dec n n1 then
      static_renaming_rhs_rename_rhs r n2
    else
      static_renaming_rhs_rename
        (unshift_name n n1)
        (transpose_name_static_renaming (unshift_name n1 n) r) n2
  end.

Fixpoint compose_pushes_static_renaming {N M O}
         (r1 : pushes O N) {struct r1}
  : static_renaming N M -> static_renaming O M :=
  match r1 in pushes O' N'
        return static_renaming N' _ -> static_renaming O' _
  with
  | pushes_id => fun r2 => r2
  | pushes_weak l r1 =>
    fun r2 =>
      static_renaming_weak l
        (compose_pushes_static_renaming r1 r2)
  | pushes_swap l1 r1 l2 =>
    fun r2 =>
      match transpose_level_static_renaming l2 r2
             in static_renaming_rhs _ M
             return static_renaming _ M
      with
      | static_renaming_rhs_shift_rhs r2 =>
          static_renaming_weak
            l1 (compose_pushes_static_renaming r1 r2)
      | static_renaming_rhs_open_rhs r2 l2 =>
          static_renaming_swap
            l1 (compose_pushes_static_renaming r1 r2) l2
      | static_renaming_rhs_rename_rhs r2 n =>
          static_renaming_close
            l1 (compose_pushes_static_renaming r1 r2) n
      end
  | pushes_close l r1 n =>
    fun r2 =>
      match transpose_name_static_renaming n r2
            in static_renaming_rhs _ M
            return static_renaming _ M
       with
      | static_renaming_rhs_shift_rhs r2 =>
          static_renaming_weak
            l (compose_pushes_static_renaming r1 r2)
      | static_renaming_rhs_open_rhs r2 l2 =>
          static_renaming_swap
            l (compose_pushes_static_renaming r1 r2) l2
      | static_renaming_rhs_rename_rhs r2 n =>
          static_renaming_close
            l (compose_pushes_static_renaming r1 r2) n
      end
  end.

Fixpoint compose_static_renamings {N M O}
         (r1 : static_renaming O N) {struct r1}
  : static_renaming N M -> static_renaming O M :=
  match r1 in static_renaming _ N'
        return static_renaming N' _ -> _
  with
  | static_renaming_pushes r1 =>
    fun r2 =>
      compose_pushes_static_renaming r1 r2
  | static_renaming_shift n r1 =>
    fun r2 =>
      static_renaming_shift n (compose_static_renamings r1 r2)
  | static_renaming_open n r1 l =>
    fun r2 =>
      match transpose_level_static_renaming l r2
             in static_renaming_rhs _ M
             return static_renaming _ M
      with
      | static_renaming_rhs_shift_rhs r2 =>
          static_renaming_shift
            n (compose_static_renamings r1 r2)
      | static_renaming_rhs_open_rhs r2 l2 =>
          static_renaming_open
            n (compose_static_renamings r1 r2) l2
      | static_renaming_rhs_rename_rhs r2 n2 =>
          static_renaming_rename
            n (compose_static_renamings r1 r2) n2
      end
  | static_renaming_rename n1 r1 n2 =>
    fun r2 =>
      match transpose_name_static_renaming n2 r2
            in static_renaming_rhs _ M
            return static_renaming _ M
       with
      | static_renaming_rhs_shift_rhs r2 =>
          static_renaming_shift
            n1 (compose_static_renamings r1 r2)
      | static_renaming_rhs_open_rhs r2 l =>
          static_renaming_open
            n1 (compose_static_renamings r1 r2) l
      | static_renaming_rhs_rename_rhs r2 n3 =>
          static_renaming_rename
            n1 (compose_static_renamings r1 r2) n3
      end
  end.

Inductive renaming (term : nset) (N : nat) : nat -> Set :=
| renaming_static : forall M,
    static_renaming N M -> renaming term N M
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
