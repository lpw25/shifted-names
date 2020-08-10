Require Import String Omega Setoid Morphisms.
Require Import Morph Var VarEquations Renaming RenamingEquations.
Set Loose Hint Behavior "Strict".

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

Module Type Relative_monad.

  Parameter term : nset.

  Parameter unit : forall {N}, morph var N term N.

  Parameter kleisli :
    forall {N M},
      morph var N term M ->
      morph term N term M.

  Parameter left_identity :
    forall N M (f : morph var N term M),
      kleisli f @ unit =m= f.

  Parameter right_identity :
    forall N, kleisli (@unit N) =m= 1.

  Parameter associativity :
    forall N M L
      (f : morph var N term M)
      (g : morph var M term L),
      (kleisli g) @ (kleisli f)
      =m= kleisli (kleisli g @ f).

  Parameter extensional :
    forall N M (f g : morph var N term M),
      f =m= g ->
      kleisli f =m= kleisli g.

  Parameter unit_extend :
    forall N,
      morph_extend (@unit N) =m= unit.

  Parameter kleisli_extend :
    forall N M (f : morph var N term M),
      morph_extend (kleisli f)
      =m= kleisli (morph_extend f).

End Relative_monad.

Module MakeTerm (T : Relative_monad).

  Import T.

  Arguments unit N {V} v.

  Definition apply_closing_k {N M} (r : closing N M)
  : morph var M term N :=
    @unit N @ apply_closing_var r.

  Definition apply_closing {N M} (r : closing N M)
  : morph term M term N :=
    kleisli (apply_closing_k r).

  Definition apply_renaming_k {N M}
             (r : renaming N M)
  : morph var M term N :=
    @unit N @ apply_renaming_var r.

  Definition apply_renaming {N M}
             (r : renaming N M)
  : morph term M term N :=
    kleisli (apply_renaming_k r).

  Definition bind_k {N} (t : term N)
    : morph var (S N) term N :=
    fun {V} v =>
      match v with
      | free n => unit N (free n)
      | bound (mklevel 0 _) =>
        morph_apply_zero (apply_closing closing_weakening) t
      | bound (mklevel (S l) lt) =>
        unit N (bound (mklevel l (less_than_pred lt)))
      end.
  Arguments bind_k {N} t {V} v : simpl nomatch.

  Definition lift_morph_k {N M} (m : morph var M term N) :
    morph var (S M) term (S N) :=
    fun V v =>
      match v with
      | free n =>
        apply_closing
          (closing_weak l_0 closing_id) V (m V (free n))
      | bound (mklevel 0 _) => unit (S N) (bound l_0)
      | bound (mklevel (S l) lt) =>
        apply_closing
          (closing_weak l_0 closing_id) V
          (m V (bound (mklevel l (less_than_pred lt))))
      end.

  Fixpoint apply_substitution_k {N M}
           (r : substitution term N M)
  : morph var M term N :=
  match r in substitution _ _ M
        return morph var M term N with
  | substitution_renaming r => apply_renaming_k r
  | @substitution_bind _ _ M t r l =>
      kleisli (@bind_k N t)
      @ lift_morph_k (apply_substitution_k r)
      @ @cycle_in_var (S M) l
  | @substitution_subst _ _ M t r n =>
      kleisli (@bind_k N t)
      @ lift_morph_k (apply_substitution_k r)
      @ morph_extend_by M (@close_var n)
  end.

  Definition apply_substitution {N M}
             (r : substitution term N M)
  : morph term M term N :=
    kleisli (apply_substitution_k r).

  Definition substitution_nil : substitution term 0 0 :=
    substitution_renaming (renaming_nil).
  Arguments substitution_nil : simpl never.

  Definition substitution_id {N} : substitution term N N :=
    substitution_renaming (renaming_id).
  Arguments substitution_id {N} : simpl never.

  Fixpoint substitution_weak {N M}
           (l1 : level (S N)) (r : substitution term N M) :
    substitution term (S N) M :=
    match r with
    | substitution_renaming r =>
        substitution_renaming (renaming_weak l1 r)
    | substitution_bind t r l =>
        substitution_bind
          (morph_apply_zero
             (apply_closing
                (closing_weak l1 closing_id)) t)
          (substitution_weak l1 r) l
    | substitution_subst t r n =>
        substitution_subst
          (morph_apply_zero
             (apply_closing
                (closing_weak l1 closing_id)) t)
          (substitution_weak l1 r) n
    end.

  Fixpoint substitution_swap {N M}
           (l1 : level (S N)) (r : substitution term N M) :
    level (S M) -> substitution term (S N) (S M) :=
    match r with
    | substitution_renaming r =>
      fun l2 =>
        substitution_renaming (renaming_exchange l1 r l2)
    | @substitution_bind _ _ M' t r l =>
      fun l2 =>
        substitution_bind
          (morph_apply_zero
             (apply_closing
                (closing_weak l1 closing_id)) t)
          (substitution_swap l1 r
             (@unshift_level (S (S M')) l l2))
          (shift_level l2 l)
    | substitution_subst t r n =>
      fun l2 =>
        substitution_subst
          (morph_apply_zero
             (apply_closing
                (closing_weak l1 closing_id)) t)
          (substitution_swap l1 r l2) n
    end.

  Fixpoint substitution_close {N M}
           (l : level (S N)) (r : substitution term N M) n :
    substitution term (S N) M :=
    match r with
    | substitution_renaming r =>
        substitution_renaming (renaming_close l r n)
    | substitution_bind t r l' =>
        substitution_bind
          (morph_apply_zero
             (apply_closing
                (closing_weak l closing_id)) t)
          (substitution_close l r n) l'
    | substitution_subst t r n' =>
        substitution_subst
          (morph_apply_zero
             (apply_closing
                (closing_weak l closing_id)) t)
          (substitution_close l r (unshift_name n' n))
          (shift_name n n')
    end.

  Fixpoint substitution_shift {N M}
           n (r : substitution term N M) :
    substitution term N M :=
    match r with
    | substitution_renaming r =>
        substitution_renaming (renaming_shift n r)
    | substitution_bind t r l =>
        substitution_bind
          (morph_apply_zero
             (apply_renaming
                (renaming_shift n renaming_id)) t)
          (substitution_shift n r) l
    | substitution_subst t r n' =>
        substitution_subst
          (morph_apply_zero
             (apply_renaming
                (renaming_shift n renaming_id)) t)
          (substitution_shift n r) n'
    end.

  Fixpoint substitution_open {N M}
           n (r : substitution term N M) :
    level (S M) -> substitution term N (S M) :=
    match r with
    | substitution_renaming r =>
      fun l =>
        substitution_renaming (renaming_open n r l)
    | @substitution_bind _ _ M' t r l' =>
      fun l =>
        substitution_bind
          (morph_apply_zero
             (apply_renaming
                (renaming_shift n renaming_id)) t)
          (substitution_open n r
             (@unshift_level (S (S M')) l' l))
          (shift_level l l')
    | substitution_subst t r n' =>
      fun l =>
        substitution_subst
          (morph_apply_zero
             (apply_renaming
                (renaming_shift n renaming_id)) t)
          (substitution_open n r l) n'
    end.

  Fixpoint substitution_rename {N M}
           n1 (r : substitution term N M) n2 :
    substitution term N M :=
    match r with
    | substitution_renaming r =>
        substitution_renaming (renaming_rename n1 r n2)
    | substitution_bind t r l =>
        substitution_bind
          (morph_apply_zero
             (apply_renaming
                (renaming_shift n1 renaming_id)) t)
          (substitution_rename n1 r n2) l
    | substitution_subst t r n' =>
        substitution_subst
          (morph_apply_zero
             (apply_renaming
                (renaming_shift n1 renaming_id)) t)
          (substitution_rename n1 r (unshift_name n' n2))
          (shift_name n2 n')
    end.

  Fixpoint compose_substitution_renaming {N M O}
         (r1 : substitution term O N) {struct r1}
  : renaming N M -> substitution term O M :=
  match r1 with
  | substitution_renaming r1 =>
    fun r2 =>
      substitution_renaming (compose_renamings r1 r2)
  | substitution_bind t r1 l =>
    fun r2 =>
      match transpose_level_renaming l r2
             in renaming_rhs _ M
             return substitution _ _ M
      with
      | renaming_rhs_shift_rhs r2 =>
          compose_substitution_renaming r1 r2
      | renaming_rhs_open_rhs r2 l =>
          substitution_bind
            t (compose_substitution_renaming r1 r2) l
      | renaming_rhs_rename_rhs r2 n =>
          substitution_subst
            t (compose_substitution_renaming r1 r2) n
      end
  | substitution_subst t r1 n =>
    fun r2 =>
      match transpose_name_renaming n r2
            in renaming_rhs _ M
            return substitution _ _ M
       with
      | renaming_rhs_shift_rhs r2 =>
        compose_substitution_renaming r1 r2
      | renaming_rhs_open_rhs r2 l =>
          substitution_bind
            t (compose_substitution_renaming r1 r2) l
      | renaming_rhs_rename_rhs r2 n =>
          substitution_subst
            t (compose_substitution_renaming r1 r2) n
      end
  end.

  Fixpoint compose_substitutions {N M O}
           (r1 : substitution term O N)
           (r2 : substitution term N M)
    : substitution term O M :=
    match r2 with
    | substitution_renaming r2 =>
      compose_substitution_renaming r1 r2
    | substitution_bind t r2 l =>
      substitution_bind
        (morph_apply_zero (apply_substitution r1) t)
        (compose_substitutions r1 r2)
        l
    | substitution_subst t r2 n =>
      substitution_subst
        (morph_apply_zero (apply_substitution r1) t)
        (compose_substitutions r1 r2)
        n
    end.

  Add Parametric Morphism {N M} : (@kleisli N M)
    with signature eq_morph ==> eq_morph
    as kleisli_mor.
    intros * Heq V n.
    apply extensional; easy.
  Qed.

End MakeTerm.
