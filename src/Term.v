Require Import String Omega Setoid Morphisms.
Require Import Morph IIndex IName ILevel IVar Var.
Set Loose Hint Behavior "Strict".

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

  Definition apply_pushes_k {N M} (r : pushes N M)
  : morph var M term N :=
    @unit N @ apply_pushes_var r.

  Definition apply_pushes {N M} (r : pushes N M)
  : morph term M term N :=
    kleisli (apply_pushes_k r).

  Definition apply_static_renaming_k {N M}
             (r : static_renaming N M)
  : morph var M term N :=
    @unit N @ apply_static_renaming_var r.

  Definition apply_static_renaming {N M}
             (r : static_renaming N M)
  : morph term M term N :=
    kleisli (apply_static_renaming_k r).

  Definition bind_k {N} (t : term N) : morph var (S N) term N :=
    fun {V} v =>
      match v with
      | free n => unit N (free n)
      | bound succ0 =>
        morph_apply_zero (apply_pushes weaken_var_n_pushes) t
      | bound (succS l) => unit N (bound l)
      end.
  Arguments bind_k {N} t {V} v : simpl nomatch.

  Definition lift_morph_k {N M} (m : morph var M term N) :
    morph var (S M) term (S N) :=
    fun V v =>
      match v with
      | free n =>
        apply_pushes (r_weak l0 (r_idN N)) V (m V (free n))
      | bound succ0 => unit (S N) (bound l0)
      | bound (succS l) =>
        apply_pushes (r_weak l0 (r_idN N)) V (m V (bound l))
      end.

  Fixpoint apply_renaming_k {N M} (r : renaming term N M)
  : morph var M term N :=
  match r in renaming _ _ M
        return morph var M term N with
  | r_static r => apply_static_renaming_k r
  | @r_bind _ _ M t r l =>
      kleisli (@bind_k N t)
      @ lift_morph_k (apply_renaming_k r)
      @ @cycle_in_var (S M) l
  | @r_subst _ _ M t r n =>
      kleisli (@bind_k N t)
      @ lift_morph_k (apply_renaming_k r)
      @ morph_extend_by M (@close_var n)
  end.

  Definition renaming_id : renaming term 0 0 :=
    r_static (r_pushes r_id).
  Arguments renaming_id : simpl never.

  Fixpoint renaming_swap {N M}
           (l1 : level (S N)) (r : renaming term N M) :
    level (S M) -> renaming term (S N) (S M) :=
    match r with
    | r_static r =>
      fun l2 => r_static (static_renaming_swap l1 r l2)
    | r_bind t r l =>
      fun l2 =>
        r_bind (morph_apply_zero
                  (apply_pushes (r_weak l1 (r_idN N))) t)
               (renaming_swap l1 r (unshift_level l l2))
               (shift_level l2 l)
    | r_subst t r n =>
      fun l2 =>
        r_subst (morph_apply_zero
                   (apply_pushes (r_weak l1 (r_idN N))) t)
                (renaming_swap l1 r l2) n
    end.

    level (S N) -> pushes N M -> level (S M) -> pushes (S N) (S M)

  renaming_open : forall M,
    name -> static_renaming N M -> level (S M) ->
  renaming_close : forall N M,
    level (S N) -> pushes N M -> name -> pushes (S N) M.
  renaming_weak :
    level (S N) -> pushes N M -> pushes (S N) M
  renaming_bind : forall M,
    term N -> renaming term N M -> level (S M) ->
    renaming term N (S M)

  renaming_shift : forall M,
    name -> static_renaming N M -> static_renaming N M
    static_renaming N (S M)
  renaming_rename : forall M,
    name -> static_renaming N M -> name -> static_renaming N M
  renaming_subst : forall M,
    term N -> renaming term N M -> name -> renaming term N (S M).



  Definition open_k n : morph var 1 term 0 :=
    @unit 0 @ @open_var n.
  Arguments open_k n {V} v /.

  Definition open n := kleisli (@open_k n).
  Arguments open n {V} t.

  Definition close_k n : morph var 0 term 1 :=
    @unit 1 @ @close_var n.
  Arguments close_k n {V} v /.

  Definition close n := kleisli (@close_k n).
  Arguments close n {V} t.

  Definition weak_k : morph var 0 term 1 :=
    @unit 1 @ @weak_var.
  Arguments weak_k {V} v /.

  Definition weak := kleisli (@weak_k).
  Arguments weak {V} t.

  Fixpoint weaken (t : term 0) V : term (0 + V) :=
    match V with
    | 0 => t
    | S V => @weak V (@weaken t V)
    end.
  Arguments weaken t {V}.

  Definition bind_k t : morph var 1 term 0 :=
    fun {V} v =>
      match v with
      | free n => unit 0 (free n)
      | bound succ0 => weaken t
      | bound (succS l) => unit 0 (bound l)
      end.
  Arguments bind_k t {V} v : simpl nomatch.

  Definition bind t := kleisli (@bind_k t).
  Arguments bind t {V} s.

  Add Parametric Morphism {N M} : (@kleisli N M)
    with signature eq_morph ==> eq_morph
    as kleisli_mor.
    intros * Heq V n; unfold fst_ivar.
    apply extensional; easy.
  Qed.

  (* [reducible r n] always equals [I], but this
     is only true definitionally when [apply_renaming_k r (free n)]
     is definitionally equal to a simpler expression.
     This relies on the lack of definitional eta for [True]. *)
  Fixpoint reducible (r : renaming term) {V} (v : var V)
    : True :=
      match r with
      | r_id => I
      | r_shift n r => reducible r v
      | r_rename n1 r n2 =>
          match v with
          | bound _ => I
          | free n =>
            if name_dec n n2 then I
            else @reducible r V (free (unshift_name n2 n))
          end
      | r_subst t r n1 =>
          match v with
          | bound _ => I
          | free n =>
            if name_dec n n1 then I
            else @reducible r V (free (unshift_name n1 n))
          end
      end.

  Fixpoint apply_renaming_k (r : renaming term)
  : morph var 0 term 0 :=
        fun V v =>
          match reducible r v with
          | I =>
            match r with
            | r_id => unit 0 v
            | r_shift n r =>
              open n (apply_renaming_k r (S V) (weak_var v))
            | r_rename n1 r n2 =>
              open n1 (apply_renaming_k r (S V) (close_var n2 v))
            | r_subst t r n =>
              bind t (apply_renaming_k r (S V) (close_var n v))
            end
          end.
  Arguments apply_renaming_k r {V} v : simpl nomatch.

  Definition apply_renaming r :=
    kleisli (@apply_renaming_k r).
  Arguments apply_renaming r {V} t.

  Notation "[ r ] t" :=
    (apply_renaming r%ren t)
      (at level 65).

  Fixpoint transpose_opens_open_left ns n :=
    match ns with
    | nil => n
    | cons n2 ns =>
      transpose_opens_open_left ns (shift_name n2 n)
    end.

  Fixpoint transpose_opens_bind_left ns (t : term 0) :=
    match ns with
    | nil => t
    | cons n ns =>
      transpose_opens_bind_left ns (open n (weak t))
    end.

  Fixpoint transpose_opens_renaming_open_left
           ns (r : renaming term) n :=
    match r with
    | r_id => p_open (transpose_opens_open_left ns n)
    | r_shift n2 r =>
      transpose_opens_renaming_open_left (cons n2 ns) r n
    | r_rename n2 r n3 =>
      if name_dec n n3 then
        p_open (transpose_opens_open_left ns n2)
      else
        transpose_opens_renaming_open_left
          (cons n2 ns) r (unshift_name n3 n)
    | r_subst t r n2 =>
      if name_dec n n2 then
        p_bind (transpose_opens_bind_left ns t)
      else
        transpose_opens_renaming_open_left ns r (unshift_name n2 n)
    end.
  Arguments transpose_opens_renaming_open_left ns r n
    : simpl nomatch.

  Definition transpose_open_pop_right (p : pop term) n :=
    match p with
    | p_open n2 => unshift_name n2 n
    | p_bind _ => n
    end.

  Fixpoint transpose_renaming_open_right n (r : renaming term) :=
    match r with
    | r_id => r
    | r_shift n2 r =>
      r_shift
        (transpose_open_pop_right
           (transpose_opens_renaming_open_left nil r n) n2)
        (transpose_renaming_open_right n r)
    | r_rename n2 r n3 =>
      if name_dec n n3 then r
      else
        r_rename
          (transpose_open_pop_right
             (transpose_opens_renaming_open_left
                nil r (unshift_name n3 n)) n2)
          (transpose_renaming_open_right (unshift_name n3 n) r)
          (unshift_name n n3)
    | r_subst t r n2 =>
      if name_dec n n2 then r
      else
        r_subst
          t (transpose_renaming_open_right (unshift_name n2 n) r)
          (unshift_name n n2)
    end.
  Arguments transpose_renaming_open_right n r
    : simpl nomatch.

  Fixpoint compose_renaming
           (r1 : renaming term) (r2 : renaming term) :=
    match r2 with
    | r_id => r1
    | r_shift n r2 =>
      match transpose_opens_renaming_open_left nil r1 n with
      | p_open n' =>
        r_shift n'
          (compose_renaming (transpose_renaming_open_right n r1) r2)
      | p_bind _ =>
          compose_renaming (transpose_renaming_open_right n r1) r2
      end
    | r_rename n1 r2 n2 =>
      match transpose_opens_renaming_open_left nil r1 n1 with
      | p_open n1' =>
        r_rename n1'
          (compose_renaming (transpose_renaming_open_right n1 r1) r2) n2
      | p_bind t =>
        r_subst t
          (compose_renaming (transpose_renaming_open_right n1 r1) r2) n2
      end
    | r_subst t r2 n =>
      r_subst (apply_renaming r1 t) (compose_renaming r1 r2) n
    end.
  Arguments compose_renaming r1 r2 : simpl nomatch.

  Notation "r1 @ r2" := (compose_renaming r1 r2) : ren_scope.

  (* Reductions *)

  Lemma red_transpose_opens_renaming_open_left_rename_eq
        ns n1 r n2 n3 :
    n2 = n3 ->
    transpose_opens_renaming_open_left ns (r_rename n1 r n2) n3
    = p_open (transpose_opens_open_left ns n1).
  Proof.
    unfold transpose_opens_renaming_open_left.
    fold transpose_opens_renaming_open_left.
    destruct (name_dec n3 n2); congruence.
  Qed.

  Lemma red_transpose_opens_renaming_open_left_rename_neq
        ns n1 r n2 n3 :
    n2 <> n3 ->
    transpose_opens_renaming_open_left ns (r_rename n1 r n2) n3
    = transpose_opens_renaming_open_left
        (cons n1 ns) r (unshift_name n2 n3).
  Proof.
    unfold transpose_opens_renaming_open_left.
    fold transpose_opens_renaming_open_left.
    destruct (name_dec n3 n2); congruence.
  Qed.

  Lemma red_transpose_opens_renaming_open_left_subst_eq
        ns t r n1 n2 :
    n1 = n2 ->
    transpose_opens_renaming_open_left ns (r_subst t r n1) n2
    = p_bind (transpose_opens_bind_left ns t).
  Proof.
    unfold transpose_opens_renaming_open_left.
    fold transpose_opens_renaming_open_left.
    destruct (name_dec n2 n1); congruence.
  Qed.

  Lemma red_transpose_opens_renaming_open_left_subst_neq
        ns t r n1 n2 :
    n1 <> n2 ->
    transpose_opens_renaming_open_left ns (r_subst t r n1) n2
    = transpose_opens_renaming_open_left ns r (unshift_name n1 n2).
  Proof.
    unfold transpose_opens_renaming_open_left.
    fold transpose_opens_renaming_open_left.
    destruct (name_dec n2 n1); congruence.
  Qed.

  Lemma red_transpose_renaming_open_right_rename_eq
    n1 n2 r n3 :
    n1 = n3 ->
    transpose_renaming_open_right n1 (r_rename n2 r n3) = r.
  Proof.
    unfold transpose_renaming_open_right.
    fold transpose_renaming_open_right.
    destruct (name_dec n1 n3); congruence.
  Qed.

  Lemma red_transpose_renaming_open_right_rename_neq
    n1 n2 r n3 :
    n1 <> n3 ->
    transpose_renaming_open_right n1 (r_rename n2 r n3)
    = r_rename
        (transpose_open_pop_right
           (transpose_opens_renaming_open_left
              nil r (unshift_name n3 n1)) n2)
        (transpose_renaming_open_right (unshift_name n3 n1) r)
        (unshift_name n1 n3).
  Proof.
    unfold transpose_renaming_open_right.
    fold transpose_renaming_open_right.
    destruct (name_dec n1 n3); congruence.
  Qed.

  Lemma red_transpose_renaming_open_right_subst_eq
        n1 t r n2 :
    n1 = n2 ->
    transpose_renaming_open_right n1 (r_subst t r n2) = r.
  Proof.
    unfold transpose_renaming_open_right.
    fold transpose_renaming_open_right.
    destruct (name_dec n1 n2); congruence.
  Qed.

  Lemma red_transpose_renaming_open_right_subst_neq
        n1 t r n2 :
    n1 <> n2 ->
    transpose_renaming_open_right n1 (r_subst t r n2)
    = r_subst t
        (transpose_renaming_open_right (unshift_name n2 n1) r)
        (unshift_name n1 n2).
  Proof.
    unfold transpose_renaming_open_right.
    fold transpose_renaming_open_right.
    destruct (name_dec n1 n2); congruence.
  Qed.

  Lemma red_compose_renaming_shift r1 n r2 :
    compose_renaming r1 (r_shift n r2)
    = r_pop_weak
        (transpose_opens_renaming_open_left nil r1 n)
        (compose_renaming (transpose_renaming_open_right n r1) r2).
  Proof. easy. Qed.

  Lemma red_compose_renaming_rename r1 n1 r2 n2 :
    compose_renaming r1 (r_rename n1 r2 n2)
    = r_pop_close
        (transpose_opens_renaming_open_left nil r1 n1)
        (compose_renaming (transpose_renaming_open_right n1 r1) r2)
        n2.
  Proof. easy. Qed.

  Hint Rewrite red_transpose_opens_renaming_open_left_rename_eq
       red_transpose_opens_renaming_open_left_rename_neq
       red_transpose_opens_renaming_open_left_subst_eq
       red_transpose_opens_renaming_open_left_subst_neq
       red_transpose_renaming_open_right_rename_eq
       red_transpose_renaming_open_right_rename_neq
       red_transpose_renaming_open_right_subst_eq
       red_transpose_renaming_open_right_subst_neq
    using (cbn; congruence) : reduce_renamings.

  Hint Rewrite red_compose_renaming_shift
       red_compose_renaming_rename : reduce_renamings.

  Ltac reduce_renamings :=
    autorewrite with reduce_renamings;
    repeat progress
      (try (rewrite_strat topdown (hints reduce_renamings)); cbn).

  (* Represent operations using the [ivar] primitives. *)
  Module AsIVars.

    Lemma open_k_def n :
      @open_k n =m= open_ivar n (@unit 0).
    Proof.
      rewrite open_ivar_as_composition.
      unfold open_k; autorewrite with var_ops_as_ivars.
      easy.
    Qed.

    Lemma close_k_def n :
      @close_k n =m= close_ivar n (@unit 1).
    Proof.
      rewrite close_ivar_as_composition.
      unfold close_k; autorewrite with var_ops_as_ivars.
      easy.
    Qed.

    Lemma weak_k_def :
      @weak_k =m= weak_ivar (@unit 1).
    Proof.
      rewrite weak_ivar_as_composition.
      easy.
    Qed.

    Lemma bind_k_def t :
      @bind_k t = bind_ivar (@weaken t) (@unit 0).
    Proof. easy. Qed.

    Lemma open_def n :
      @open n =m= kleisli (open_ivar n (@unit 0)).
    Proof.
      unfold open; rewrite open_k_def; easy.
    Qed.

    Lemma close_def n :
      @close n =m= kleisli (close_ivar n (@unit 1)).
    Proof.
      unfold close; rewrite close_k_def; easy.
    Qed.

    Lemma weak_def :
      @weak =m= kleisli (weak_ivar (@unit 1)).
    Proof.
      unfold weak; rewrite weak_k_def; easy.
    Qed.

    Lemma bind_def t :
    @bind t = kleisli (bind_ivar (@weaken t) (@unit 0)).
    Proof. easy. Qed.

    Lemma apply_renaming_k_id_def :
      @apply_renaming_k r_id =m= @unit 0.
    Proof. easy. Qed.

    Lemma apply_renaming_k_shift_def n r :
      @apply_renaming_k (r_shift n r)
      =m= kleisli (open_ivar n (@unit 0))
          @ morph_extend (@apply_renaming_k r)
          @ IVar.weak_var.
    Proof.
      intros V v; cbn.
      unfold apply_renaming_k; fold apply_renaming_k.
      destruct (reducible (r_shift n r) v).
      rewrite open_def, weak_var_def.
      easy.
    Qed.

    Lemma apply_renaming_k_rename_def n1 r n2 :
      @apply_renaming_k (r_rename n1 r n2)
      =m= kleisli (open_ivar n1 (@unit 0))
          @ morph_extend (@apply_renaming_k r)
          @ IVar.close_var n2.
    Proof.
      intros V v; cbn.
      unfold apply_renaming_k; fold apply_renaming_k.
      destruct (reducible (r_rename n1 r n2) v).
      rewrite open_def, close_var_def.
      easy.
    Qed.

    Lemma apply_renaming_k_subst_def t r n :
      @apply_renaming_k (r_subst t r n)
      =m= kleisli (bind_ivar (@weaken t) (@unit 0))
          @ morph_extend (@apply_renaming_k r)
          @ IVar.close_var n.
    Proof.
      intros V v; cbn.
      unfold apply_renaming_k; fold apply_renaming_k.
      destruct (reducible (r_subst t r n) v).
      rewrite bind_def, close_var_def.
      easy.
    Qed.

    Lemma apply_renaming_id_def :
      @apply_renaming r_id =m= 1.
    Proof.
      unfold apply_renaming.
      rewrite apply_renaming_k_id_def, right_identity.
      easy.
    Qed.

    Lemma apply_renaming_shift_def n r :
      @apply_renaming (r_shift n r)
      =m= kleisli (open_ivar n (@unit 0))
          @ kleisli (morph_extend (@apply_renaming_k r))
          @ kleisli (weak_ivar (@unit 1)).
    Proof.
      unfold apply_renaming.
      rewrite apply_renaming_k_shift_def,
        !associativity, weak_ivar_as_composition,
        morph_associative with (g := @unit 1), left_identity.
      easy.
    Qed.

    Lemma apply_renaming_rename_def n1 r n2 :
      @apply_renaming (r_rename n1 r n2)
      =m= kleisli (open_ivar n1 (@unit 0))
          @ kleisli (morph_extend (@apply_renaming_k r))
          @ kleisli (close_ivar n2 (@unit 1)).
    Proof.
      unfold apply_renaming.
      rewrite apply_renaming_k_rename_def,
        !associativity, close_ivar_as_composition,
        morph_associative with (g := @unit 1), left_identity.
      easy.
    Qed.

    Lemma apply_renaming_subst_def t r n :
      @apply_renaming (r_subst t r n)
      =m= kleisli (bind_ivar (@weaken t) (@unit 0))
          @ kleisli (morph_extend (@apply_renaming_k r))
          @ kleisli (close_ivar n (@unit 1)).
    Proof.
      unfold apply_renaming.
      rewrite apply_renaming_k_subst_def,
        !associativity, close_ivar_as_composition,
        morph_associative with (g := @unit 1), left_identity.
      easy.
    Qed.

    Hint Rewrite open_k_def close_k_def weak_k_def bind_k_def
         open_def close_def weak_def bind_def
         apply_renaming_k_id_def
         apply_renaming_k_shift_def
         apply_renaming_k_rename_def
         apply_renaming_k_subst_def
         apply_renaming_id_def
         apply_renaming_shift_def
         apply_renaming_rename_def
         apply_renaming_subst_def
      : term_ops_as_ivars.

    Lemma weaken_extend t :
      pnset_extend (@weaken t)
      =p= morph_apply
            (kleisli (weak_ivar (@unit 1)))
            (@weaken t).
    Proof.
      intro V; cbn; autorewrite with term_ops_as_ivars; easy.
    Qed.

    Hint Rewrite @left_identity @right_identity
         @associativity @unit_extend @kleisli_extend
         @weaken_extend
         @morph_apply_compose @morph_apply_id
         @pair_ivar_compose_distribute
         @fst_ivar_compose_distribute
         @snd_ivar_compose_distribute
         @open_ivar_compose_distribute
         @close_ivar_compose_distribute
         @weak_ivar_compose_distribute
         @bind_ivar_compose_distribute
         @swap_ivar_compose_distribute
         @pair_ivar_extend @fst_ivar_extend
         @snd_ivar_extend @open_ivar_extend
         @close_ivar_extend @weak_ivar_extend
         @bind_ivar_extend @swap_ivar_extend
      : simpl_terms_as_ivars.

    Hint Rewrite <- @open_ivar_as_composition
        @close_ivar_as_composition @weak_ivar_as_composition
      : simpl_terms_as_ivars.

    Ltac simpl_terms_as_ivars :=
      autorewrite with var_ops_as_ivars term_ops_as_ivars;
      autorewrite with simpl_terms_as_ivars;
      repeat progress
        (cbn;
         try (rewrite_strat topdown
                (hints simpl_terms_as_ivars))).

    Lemma snd_ivar_apply_renaming_k r :
      snd_ivar (@apply_renaming_k r)
      =m= snd_ivar (@unit 0).
    Proof.
      induction r; simpl_terms_as_ivars.
      - easy.
      - rewrite <- ivar_eta with (f := @apply_renaming_k r).
        rewrite IHr.
        simpl_terms_as_ivars; simpl_ivars; easy.
      - rewrite <- ivar_eta with (f := @apply_renaming_k r).
        rewrite IHr.
        simpl_terms_as_ivars; simpl_ivars; easy.
      - rewrite <- ivar_eta with (f := @apply_renaming_k r).
        rewrite IHr.
        simpl_terms_as_ivars; simpl_ivars; easy.
    Qed.

    Lemma apply_renaming_k_pair_eta r :
      @apply_renaming_k r
      =m= pair_ivar (fst_ivar (@apply_renaming_k r))
                    (snd_ivar (@unit 0)).
    Proof.
      rewrite <- snd_ivar_apply_renaming_k.
      simpl_ivars; easy.
    Qed.

  End AsIVars.

  Import AsIVars.

  (* Normalization *)

  Lemma combine_open_renaming_close N n1 r n2 (t : term N):
    open n1 ([r](close n2 t))
    = [r; n1 <- n2] t.
  Proof.
    unfold open, close, apply_renaming at 1.
    simpl_terms_as_ivars.
Qed.

  Lemma combine_open_renaming_weak N n r (t : term N) :
    open n ([r](weak t))
    = [r; ^n] t.
  Proof. easy. Qed.

  Lemma combine_bind_renaming_close N t1 r n (t2 : term N) :
    bind t1 ([r](close n t2))
    = [r; t1 // n] t2.
  Proof. easy. Qed.

  Lemma combine_bind_renaming_weak N t1 r (t2 : term N) :
    bind t1 ([r](weak t2))
    = [r] t2.
  Proof.
    simpl_terms_as_ivars.
    

  (* Simplification *)


  Lemma transpose_open_pop n p :
    @open n @ morph_extend (apply_pop p)
    =m= apply_pop (transpose_open_pop_left n p)
        @ morph_extend (@open (transpose_open_pop_right p n)).
  Proof.
    destruct p; cbn.
    - simpl_terms_as_ivars.
      transpose_ivar_pop_pop (open _) (open _).
    autorewrite with unfold_terms.
    autorewrite with simpl_terms.
    transpose_ivar_pop_pop (open n0) (open n).

Definition apply_pop (op : pop term)
  : morph term 1 term 0 :=
  match op with
  | p_open n => @open n
  | p_bind t => @bind t
  end.
Arguments apply_pop !op.

Definition transpose_renaming_bind (r : renaming term) t :
  pop term * renaming term :=
  pair (p_bind (apply_renaming r 0 t)) r.

Definition transpose_renaming_pop (r : renaming term) p :
  pop term * renaming term :=
  match p with
  | p_open n => transpose_renaming_open r n
  | p_bind t => transpose_renaming_bind r t
  end.

Lemma snd_apply_static_ivar {N T M} (r : renaming T)
      (f : ivar N T M) :
  snd_ivar (apply_static_ivar r f) = snd_ivar f.
Proof.
  generalize dependent M.
  generalize dependent N.
  induction r; intros N M f; cbn.
  - easy.
  - simpl_ivars_pointwise.
    rewrite IHr; easy.
  - simpl_ivars_pointwise.
    rewrite IHr; easy.
  - easy.
Qed.

Lemma fst_apply_static_ivar {N T M} (r : renaming T)
      (f : ivar N T M) (g : ivar N T M) :
  fst_ivar f =km= fst_ivar g ->
  fst_ivar (apply_static_ivar r f)
  =km= fst_ivar (apply_static_ivar r g).
Proof.
  generalize dependent M.
  generalize dependent N.
  induction r; intros N M f g Heq; cbn.
  - easy.
  - simpl_ivars_pointwise.
    apply IHr.
    simpl_ivars_pointwise.
    rewrite Heq; easy.
  - simpl_ivars_pointwise.
    rewrite snd_apply_static_ivar, snd_apply_static_ivar.
    simpl_ivars_pointwise.
    rewrite Heq.
    rewrite IHr with (g := open_ivar b g); try easy.
    simpl_ivars_pointwise.
    rewrite Heq; easy.
  - apply IHr; easy.
Qed.

Lemma transpose_swap_ivar_apply_static_ivar {N T M}
      (r : renaming T)
      (f : ivar (S (S N)) T M) :
  swap_ivar (apply_static_ivar r f)
  =m= apply_static_ivar r (swap_ivar f).
Proof.
  unfold swap_ivar; symmetry.
  rewrite <- ivar_eta_pointwise.
  rewrite snd_apply_static_ivar, snd_apply_static_ivar.
  rewrite fst_apply_static_ivar with (g := f) by easy.
  simpl_ivars_pointwise.
  easy.
Qed.

Lemma transfer_open_var_spec {T} (r : renaming T) n :
  forall {N M} (f : ivar N T M),
  open_ivar n (apply_static_ivar r f)
  =m= apply_static_ivar
        (snd (transfer_open_var r n))
        (open_ivar (fst (transfer_open_var r n)) f).
Proof.
  generalize dependent n.
  induction r; intros c N M f; cbn in *.
  - easy.
  - rewrite transpose_open_ivar_weak_ivar_pointwise.
    rewrite IHr.
    rewrite transpose_swap_ivar_apply_static_ivar.
    rewrite transpose_open_ivar_open_ivar_pointwise.
    easy.
  - remember (name_eqb c n) as eq_ca eqn:Hca.
    symmetry in Hca.
    destruct eq_ca.
    + apply name_eqb_eq in Hca; subst.
      simpl_ivars_pointwise.
      easy.
    + apply name_eqb_neq in Hca.
      rewrite transpose_open_ivar_close_ivar_pointwise
        by easy.
      rewrite IHr.
      rewrite transpose_swap_ivar_apply_static_ivar.
      rewrite transpose_open_ivar_open_ivar_pointwise.
      easy.
  - rewrite IHr.
    easy.
Qed.

Lemma compose_static_left_identity {T} (r : renaming T) :
  compose_static r_id r = r.
Proof. easy. Qed.

Lemma compose_static_right_identity {T} (r : renaming T) :
  compose_static r r_id = r.
Proof.
  induction r; cbn; try rewrite IHr; easy.
Qed.

(*
Lemma transfer_open_var_shift_name {T} (r : renaming T) a b :
  fst (transfer_open_var r (shift_name a b))
  = shift_name (fst (transfer_open_var r a))
      (fst (transfer_open_var (snd (transfer_open_var r a)) b)).
Proof.
  generalize dependent b.
  generalize dependent a.
  induction r; intros c d; cbn.
  - easy.
  - rewrite IHr.
    rewrite transpose_shift_name_shift_name.
    easy.
  - remember (name_eqb c a) as eq_ca eqn:Hca.
    symmetry in Hca.
    remember (name_eqb (shift_name c d) a) as eq_da eqn:Hda.
    symmetry in Hda.
    destruct eq_ca, eq_da; cbn.
    + apply name_eqb_eq in Hca.
      apply name_eqb_eq in Hda; subst.
      contradict Hda.
      apply shift_name_neq.
    + apply name_eqb_eq in Hca; subst.
      simpl_names; easy.
    + apply name_eqb_neq in Hca.
      apply name_eqb_eq in Hda; subst.
      simpl_names.
      easy.
    + apply name_eqb_neq in Hca.
      apply name_eqb_neq in Hda.
      remember (name_eqb d (unshift_name c a))
        as dca eqn:Hdca.
      symmetry in Hdca.
      destruct dca.
      * rewrite name_eqb_eq in Hdca; subst.
        contradict Hda.
        simpl_names; easy.
      * rewrite name_eqb_neq in Hdca.
        simpl_names; cbn.
        rewrite <- transpose_shift_name_shift_name.
        rewrite <- IHr.
        rewrite transpose_unshift_name_shift_name by easy.
        easy.
  - apply IHr.
Qed.

Lemma transfer_open_var_unshift_name {T} (r : renaming T) a b :
  fst (transfer_open_var
         (snd (transfer_open_var r (shift_name a b)))
         (unshift_name b a))
  = unshift_name
      (fst (transfer_open_var (snd (transfer_open_var r a)) b))
      (fst (transfer_open_var r a)).
Proof.
  generalize dependent b.
  generalize dependent a.
  induction r; intros c d; cbn.
  - easy.
  - rewrite IHr.
    rewrite transfer_open_var_shift_name.
    remember (fst
          (transfer_open_var
             (snd (transfer_open_var r c)) d)) as e.
    remember (fst (transfer_open_var r c)) as f.
    rewrite transpose_shift_name_unshift_name.

    

    easy.
  - remember (name_eqb c a) as eq_ca eqn:Hca.
    symmetry in Hca.
    remember (name_eqb (shift_name c d) a) as eq_da eqn:Hda.
    symmetry in Hda.
    destruct eq_ca, eq_da; cbn.
    + apply name_eqb_eq in Hca.
      apply name_eqb_eq in Hda; subst.
      contradict Hda.
      apply shift_name_neq.
    + apply name_eqb_eq in Hca; subst.
      simpl_names; easy.
    + apply name_eqb_neq in Hca.
      apply name_eqb_eq in Hda; subst.
      simpl_names.
      easy.
    + apply name_eqb_neq in Hca.
      apply name_eqb_neq in Hda.
      remember (name_eqb d (unshift_name c a))
        as dca eqn:Hdca.
      symmetry in Hdca.
      destruct dca.
      * rewrite name_eqb_eq in Hdca; subst.
        contradict Hda.
        simpl_names; easy.
      * rewrite name_eqb_neq in Hdca.
        simpl_names; cbn.
        rewrite <- transpose_shift_name_shift_name.
        rewrite <- IHr.
        rewrite transpose_unshift_name_shift_name by easy.
        easy.
  - apply IHr.

*)
Lemma transfer_open_var_compose_static_fst {T}
      (r s : renaming T) a :
   fst (transfer_open_var (compose_static r s) a)
   = fst (transfer_open_var s (fst (transfer_open_var r a))).
Proof.
  generalize dependent a.
  generalize dependent s.
  induction r; intros s c; cbn.
  - easy.
  - rewrite IHr.
    rewrite transfer_open_var_open_var.
    easy.
  - remember (name_eqb c a) as ca eqn:Hca.
    symmetry in Hca.
    destruct ca.
    + rewrite name_eqb_eq in Hca; subst.
      easy.
    + rewrite IHr.
      simpl_ivars.
      rewrite transfer_open_var_open_var.
      easy.
  - apply IHr.
Qed.

Lemma transfer_open_var_compose_static_snd {T}
      (r s : renaming T) a :
  snd (transfer_open_var (compose_static r s) a)
  = compose_static (snd (transfer_open_var r a))
      (snd (transfer_open_var s (fst (transfer_open_var r a)))).
Proof.
  generalize dependent a.
  generalize dependent s.
  induction r; intros s c; cbn.
  - easy.
  - f_equal.
    + rewrite transfer_open_var_compose_static_fst.
    rewrite IHr.
    
    easy.
  - remember (name_eqb c a) as ca eqn:Hca.
    symmetry in Hca.
    destruct ca.
    + rewrite name_eqb_eq in Hca; subst.
      easy.
    + rewrite IHr.
      simpl_ivars.
      rewrite transfer_open_var_open_var.
      easy.
  - apply IHr.
Qed.

Lemma compose_static_associative {T} (r s t : renaming T) :
  compose_static r (compose_static s t)
  = compose_static (compose_static r s) t.
Proof.
  generalize dependent s.
  generalize dependent t.
  induction r; intros u s; cbn.
  - easy.
  - rewrite transfer_open_var_compose_static.
    rewrite <- IHr.
    f_equal.
  -
  - rewrite IHr; easy.
Qed.

Lemma apply_static_ivar_compose {T N T M} (r : renaming T) s
      (f : ivar N T M) :
  apply_static_ivar (compose_static r s) f
  =m= apply_static_ivar r (apply_static_ivar s f).
Proof.
  generalize dependent M.
  generalize dependent T.
  generalize dependent N.
  generalize dependent s.
  induction r; intros s N T M f; cbn.
  - easy.
  - rewrite transfer_open_var_spec by eassumption.
    rewrite <- IHr.
    easy.
  - rewrite transfer_open_var_spec by eassumption.
    rewrite <- IHr.
    easy.
  - easy.
Qed.

Lemma apply_static_ivar_as_composition {T N T M} (r : renaming T)
      (f : ivar N T M) :
  apply_static_ivar r f =m=
  f @ (morph_extend_by N (apply_static_var r)).
Proof.
  generalize dependent M.
  generalize dependent T.
  generalize dependent N.
  induction r; intros N T M f; cbn.
  - rewrite morph_extend_by_id.
    easy.
  - rewrite morph_extend_by_compose, morph_extend_by_compose.
    rewrite weak_ivar_as_composition, open_ivar_as_composition.
    rewrite IHr; cbn.
    easy.
  - rewrite morph_extend_by_compose, morph_extend_by_compose.
    rewrite close_ivar_as_composition, open_ivar_as_composition.
    rewrite IHr.
    easy.
  - apply IHr.
Qed.

Lemma apply_static_var_spec {T} (r : renaming T) :
  apply_static_var r =m= apply_static_ivar r 1.
Proof.
  induction r; cbn.
  - easy.
  - rewrite weak_ivar_as_composition, open_ivar_as_composition,
      apply_static_ivar_as_composition.
    easy.
  - rewrite close_ivar_as_composition, open_ivar_as_composition,
      apply_static_ivar_as_composition.
    easy.
  - easy.
Qed.

Lemma apply_static_ivar_compose_distribute {T N T M R L}
      (r : renaming T) (f : ivar N T M) (g : morph T M R L) :
  g @ (apply_static_ivar r f)
  =m= apply_static_ivar r (g @ f).
Proof.
  intros V v.
  rewrite apply_static_ivar_as_composition.
  rewrite morph_associative.
  rewrite <- apply_static_ivar_as_composition.
  easy.
Qed.

Lemma apply_static_var_compose {T N T M} (r : renaming T) s
      (f : ivar N T M) :
  apply_static_var (compose_static r s)
  =m= (apply_static_var s) @ (apply_static_var r).
Proof.
  rewrite apply_static_var_spec.
  rewrite apply_static_ivar_compose.
  rewrite apply_static_ivar_as_composition, apply_static_ivar_as_composition.
  easy.
Qed.

End TermLemmas.
