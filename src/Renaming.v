Require Import String PeanoNat Compare_dec StrictProp.
Require Import Morph Var.

(* Algebra of operations on [var] *)

Inductive closing : nat -> nat -> Set :=
| closing_id : closing 0 0
| closing_weak : forall N M,
    level (S N) -> closing N M -> closing (S N) M
| closing_exchange : forall N M,
    level (S N) -> closing N M -> level (S M) -> closing (S N) (S M)
| closing_close : forall N M,
    level (S N) -> closing N M -> name -> closing (S N) M.

Arguments closing_weak {N} {M} l r.
Arguments closing_exchange {N} {M} l1 r l2.
Arguments closing_close {N} {M} l r n.

Fixpoint closing_weak_n {N} : closing N 0 :=
  match N return closing N _ with
  | 0 => closing_id
  | S N => closing_weak l_0 closing_weak_n
  end.

Fixpoint closing_weakening {N M} : closing (N + M) N :=
  match N return closing (N + _) N with
  | 0 => closing_weak_n
  | S N => closing_exchange l_0 closing_weakening l_0
  end.

Fixpoint closing_id_n {N} : closing N N :=
  match N return closing N N with
  | 0 => closing_id
  | S N => closing_exchange l_0 closing_id_n l_0
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

Fixpoint renaming_exchange {N M}
         (l1 : level (S N)) (r : renaming N M) :
  level (S M) -> renaming (S N) (S M) :=
  match r in renaming _ M
        return level (S M) -> renaming _ (S M)
  with
  | renaming_closing r =>
    fun l2 => renaming_closing (closing_exchange l1 r l2)
  | renaming_shift n r =>
    fun l2 => renaming_shift n (renaming_exchange l1 r l2)
  | @renaming_open _ M n r l =>
    fun l2 =>
      renaming_open
        n (renaming_exchange l1 r
             (@unshift_level (S (S M)) l l2))
        (shift_level l2 l)
  | renaming_rename n1 r n2 =>
    fun l2 =>
      renaming_rename n1 (renaming_exchange l1 r l2) n2
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
  | @closing_exchange N M l1 r l2 =>
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
| closing_rhs_exchange_rhs : forall M,
    closing N M -> level (S M) -> closing_rhs N (S M)
| closing_rhs_close_rhs : forall M,
    closing N M -> name -> closing_rhs N M.

Arguments closing_rhs_weak_rhs {N} {M} r.
Arguments closing_rhs_exchange_rhs {N} {M} r l.
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
      | closing_rhs_exchange_rhs r l =>
        closing_rhs_exchange_rhs (closing_weak l1 r) l
      | closing_rhs_close_rhs r n =>
        closing_rhs_close_rhs (closing_weak l1 r) n
      end
  end.
Arguments closing_rhs_weak {N M} l r : simpl nomatch.

Definition closing_rhs_exchange {N M}
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
        fun l2 => closing_rhs_weak_rhs (closing_exchange l1 r l2)
      | @closing_rhs_exchange_rhs _ M' r l =>
        fun l2 =>
          closing_rhs_exchange_rhs
            (closing_exchange l1 r
               (@unshift_level (S (S M')) l l2))
            (shift_level l2 l)
      | closing_rhs_close_rhs r n =>
        fun l2 => closing_rhs_close_rhs (closing_exchange l1 r l2) n
      end
  end.
Arguments closing_rhs_exchange {N M} l1 r l2 : simpl nomatch.

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
      | closing_rhs_exchange_rhs r l =>
        fun n1 => closing_rhs_exchange_rhs (closing_close l1 r n1) l
      | closing_rhs_close_rhs r n =>
        fun n1 =>
          closing_rhs_close_rhs (closing_close l1 r (unshift_name n n1))
                           (shift_name n1 n)
      end
  end.
Arguments closing_rhs_close {N M} l r n : simpl nomatch.

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
  | closing_exchange l1 r l2 =>
    fun l =>
      match level_sdec l l1 with
      | sleft _ => closing_rhs_exchange_rhs r l2
      | sright neq =>
        closing_rhs_exchange
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
  | closing_exchange l1 r l2 =>
      closing_rhs_exchange
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
  | closing_exchange l1 r1 l2 =>
    fun r2 =>
      match transpose_level_closing r2 l2 in closing_rhs _ M
            return closing _ M
       with
      | closing_rhs_weak_rhs r2 =>
          closing_weak l1 (compose_closing r1 r2)
      | closing_rhs_exchange_rhs r2 l2 =>
          closing_exchange l1 (compose_closing r1 r2) l2
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
      | closing_rhs_exchange_rhs r2 l2 =>
          closing_exchange l (compose_closing r1 r2) l2
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
  | @renaming_rhs_open_rhs _ M' r l =>
    fun l1 =>
      renaming_rhs_open_rhs
        (renaming_open n1 r (@unshift_level (S (S M')) l l1))
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
      | closing_rhs_exchange_rhs r l =>
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
    | closing_rhs_exchange_rhs r l =>
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
  | closing_exchange l1 r1 l2 =>
    fun r2 =>
      match transpose_level_renaming l2 r2
             in renaming_rhs _ M
             return renaming _ M
      with
      | renaming_rhs_shift_rhs r2 =>
          renaming_weak
            l1 (compose_closing_renaming r1 r2)
      | renaming_rhs_open_rhs r2 l2 =>
          renaming_exchange
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
          renaming_exchange
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
