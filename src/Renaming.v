Require Import String PeanoNat Compare_dec StrictProp.
Require Import Morph Var.

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

Definition renaming_nil :=
  renaming_closing closing_nil.

Definition renaming_id {N} : renaming N N :=
  renaming_closing closing_id.

Fixpoint renaming_zero_weak {N M} (r : renaming N M) :
  renaming (S N) M :=
  match r in renaming _ M
        return renaming _ M
  with
  | renaming_closing r =>
    renaming_closing (closing_zero_weak r)
  | renaming_shift n r =>
    renaming_shift n (renaming_zero_weak r)
  | @renaming_open _ M n r l =>
    renaming_open n (renaming_zero_weak r) l
  | renaming_rename n1 r n2 =>
    renaming_rename n1 (renaming_zero_weak r) n2
  end.

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

Fixpoint renaming_zero_exchange {N M}
         (r : renaming N M) :
  level (S M) -> renaming (S N) (S M) :=
  match r in renaming _ M
        return level (S M) -> renaming _ (S M)
  with
  | renaming_closing r =>
    fun l2 => renaming_closing (closing_zero_exchange r l2)
  | renaming_shift n r =>
    fun l2 => renaming_shift n (renaming_zero_exchange r l2)
  | @renaming_open _ M n r l =>
    fun l2 =>
      renaming_open
        n (renaming_zero_exchange r
             (@unshift_level (S (S M)) l l2))
        (shift_level l2 l)
  | renaming_rename n1 r n2 =>
    fun l2 =>
      renaming_rename n1 (renaming_zero_exchange r l2) n2
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

Fixpoint renaming_zero_close {N M}
         (r : renaming N M) (n : name) :
  renaming (S N) M :=
  match r in renaming _ M
        return renaming _ M
  with
  | renaming_closing r =>
    renaming_closing (closing_zero_close r n)
  | renaming_shift n' r =>
    renaming_shift n' (renaming_zero_close r n)
  | @renaming_open _ M n' r l' =>
    renaming_open n' (renaming_zero_close r n) l'
  | renaming_rename n1 r n2 =>
    renaming_rename
      n1 (renaming_zero_close r (unshift_name n2 n))
      (shift_name n n2)
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
  | closing_nil => fun r2 => r2
  | closing_zero_weak r1 =>
    fun r2 =>
      renaming_zero_weak
        (compose_closing_renaming r1 r2)
  | closing_zero_exchange r1 l2 =>
    fun r2 =>
      match transpose_level_renaming l2 r2
             in renaming_rhs _ M
             return renaming _ M
      with
      | renaming_rhs_shift_rhs r2 =>
          renaming_zero_weak
            (compose_closing_renaming r1 r2)
      | renaming_rhs_open_rhs r2 l2 =>
          renaming_zero_exchange
            (compose_closing_renaming r1 r2) l2
      | renaming_rhs_rename_rhs r2 n =>
          renaming_zero_close
            (compose_closing_renaming r1 r2) n
      end
  | closing_zero_close r1 n =>
    fun r2 =>
      match transpose_name_renaming n r2
            in renaming_rhs _ M
            return renaming _ M
       with
      | renaming_rhs_shift_rhs r2 =>
          renaming_zero_weak
            (compose_closing_renaming r1 r2)
      | renaming_rhs_open_rhs r2 l2 =>
          renaming_zero_exchange
            (compose_closing_renaming r1 r2) l2
      | renaming_rhs_rename_rhs r2 n =>
          renaming_zero_close
            (compose_closing_renaming r1 r2) n
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
