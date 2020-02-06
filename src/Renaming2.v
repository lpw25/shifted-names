Require Import Setoid Morphisms Morph Var2.

(* Algebra of operations on [var 0] *)
Inductive renaming (trm : Set) :=
| r_id
| r_shift (b : name) (r : renaming trm)
| r_rename (b : name) (r : renaming trm) (a : name)
| r_subst (t : trm) (r : renaming trm) (a : name).

Arguments r_id {trm}.
Arguments r_shift {trm} b r.
Arguments r_rename {trm} b r a.
Arguments r_subst {trm} t r a.

Declare Scope ren_scope.
Notation "r , ^ a" := (r_shift a r)
  (at level 47, left associativity) : ren_scope.
Notation "r , a <- b" := (r_rename a r b)
  (at level 47, left associativity, a at next level) : ren_scope.
Notation "r , u // a" := (r_subst u r a)
  (at level 47, left associativity, u at next level) : ren_scope.
Notation "^ a" := (r_shift a r_id)
  (at level 47, left associativity) : ren_scope.
Notation "a <- b" := (r_rename a r_id b)
  (at level 47, left associativity) : ren_scope.
Notation "u // a" := (r_subst u r_id a)
  (at level 47, left associativity) : ren_scope.
Notation "r , a" := (r_rename a r a)
  (at level 47, left associativity) : ren_scope.

Delimit Scope ren_scope with ren.

Fixpoint static {trm : Set} (r : renaming trm) : Prop :=
  match r with
  | r_id => True
  | r_shift b r => static r
  | r_rename b r a => static r
  | r_subst u r a => False
  end.

Fixpoint apply_static_ivar {trm} (r : renaming trm)
         {N T M} (f : ivar N T M) : ivar N T M :=
  match r with
  | r_id => f
  | r_shift b r =>
      weak_ivar (apply_static_ivar r (open_ivar b f))
  | r_rename b r a =>
      close_ivar a (apply_static_ivar r (open_ivar b f))
  | r_subst _ r _ => apply_static_ivar r f
  end.

Add Parametric Morphism {trm r N} {T : nset} {M}
  : (@apply_static_ivar trm r N T M)
    with signature eq_morph ==> eq_morph
    as sapply_ivar_mor.
  generalize dependent M.
  generalize dependent T.
  generalize dependent N.
  induction r; intros * Heq; cbn.
  - easy.
  - rewrite IHr with (y := open_ivar b y) by (rewrite Heq; easy).
    easy.
  - rewrite IHr with (y := open_ivar b y) by (rewrite Heq; easy).
    easy.
  - rewrite IHr with (y := y) by (rewrite Heq; easy).
    easy.
Qed.

Lemma snd_apply_static_ivar {trm N T M} (r : renaming trm)
      (f : ivar N T M) :
  snd_ivar (apply_static_ivar r f) = snd_ivar f.
Proof.
  generalize dependent M.
  generalize dependent T.
  generalize dependent N.
  induction r; intros N T M f; cbn.
  - easy.
  - simpl_ivars_pointwise.
    rewrite IHr; easy.
  - simpl_ivars_pointwise.
    rewrite IHr; easy.
  - easy.
Qed.

Lemma fst_apply_static_ivar {trm N T M} (r : renaming trm)
      (f : ivar N T M) (g : ivar N T M) :
  fst_ivar f =km= fst_ivar g ->
  fst_ivar (apply_static_ivar r f)
  =km= fst_ivar (apply_static_ivar r g).
Proof.
  generalize dependent M.
  generalize dependent T.
  generalize dependent N.
  induction r; intros N T M f g Heq; cbn.
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

Lemma swap_apply_static_ivar_transpose_ivar {trm N T M}
      (r : renaming trm)
      (f : ivar (S (S N)) T M) :
  apply_static_ivar r (transpose_ivar f)
  =m= transpose_ivar (apply_static_ivar r f).
Proof.
  rewrite <- ivar_eta_pointwise.
  unfold transpose_ivar.
  rewrite snd_apply_static_ivar, snd_apply_static_ivar.
  rewrite fst_apply_static_ivar with (g := f) by easy.
  simpl_ivars_pointwise.
  easy.
Qed.

Fixpoint transfer_open_var {trm} (r : renaming trm) (a : name) :
  name * renaming trm :=
  match r with
  | r_id => pair a r_id
  | r_shift b r =>
      let ar' := transfer_open_var r a in
      pair (shift_name b (fst ar'))
           (r_shift (unshift_name (fst ar') b) (snd ar'))
  | r_rename c r b =>
      match name_eqb a b with
      | true => pair c r
      | false =>
        let ar' := transfer_open_var r (unshift_name b a) in
        pair (shift_name c (fst ar'))
             (r_rename (unshift_name (fst ar') c)
                       (snd ar')
                       (unshift_name a b))
      end
  | r_subst t r b =>
        let ar' := transfer_open_var r a in
        pair (fst ar') (r_subst t (snd ar')  b)
  end.

Lemma transfer_open_var_spec {trm} (r : renaming trm) a :
  forall {N T M} (f : ivar N T M),
  open_ivar a (apply_static_ivar r f)
  =m= apply_static_ivar
        (snd (transfer_open_var r a))
        (open_ivar (fst (transfer_open_var r a)) f).
Proof.
  generalize dependent a.
  induction r; intros c N T M f; cbn in *.
  - easy.
  - rewrite swap_open_ivar_weak_ivar_pointwise.
    rewrite IHr.
    rewrite <- swap_apply_static_ivar_transpose_ivar.
    rewrite swap_open_ivar_open_ivar_pointwise.
    easy.
  - remember (name_eqb c a) as eq_ca eqn:Hca.
    symmetry in Hca.
    destruct eq_ca.
    + apply name_eqb_eq in Hca; subst.
      simpl_ivars_pointwise.
      easy.
    + apply name_eqb_neq in Hca.
      rewrite swap_open_ivar_close_ivar_pointwise by easy.
      rewrite IHr.
      rewrite <- swap_apply_static_ivar_transpose_ivar.
      rewrite swap_open_ivar_open_ivar_pointwise.
      easy.
  - rewrite IHr.
    easy.
Qed.

Fixpoint compose_static {trm}
         (r : renaming trm) (s : renaming trm) :=
  match r with
  | r_id => s
  | r_shift a r =>
    let as' := transfer_open_var s a in
    let r' := compose_static r (snd as') in
    r_shift (fst as') r'
  | r_rename a r b =>
    let as' := transfer_open_var s a in
    let r' := compose_static r (snd as') in
    r_rename (fst as') r' b
  | r_subst t r a =>
    let r' := compose_static r s in
    r_subst t r' a
  end.

Lemma compose_static_left_identity {trm} (r : renaming trm) :
  compose_static r_id r = r.
Proof. easy. Qed.

Lemma compose_static_right_identity {trm} (r : renaming trm) :
  compose_static r r_id = r.
Proof.
  induction r; cbn.
  - easy.
  - rewrite IHr; easy.
  - rewrite IHr; easy.
  - rewrite IHr; easy.
Qed.

Lemma transfer_open_var_compose_static {trm} (r s : renaming trm) a :
   fst (transfer_open_var (compose_static r s) a)
   = fst (transfer_open_var s (fst (transfer_open_var r a))).
Proof.
  generalize dependent a.
  generalize dependent s.
  induction r; intros s c; cbn.
  - easy.
  - rewrite IHr.
Qed.

Lemma compose_static_associative {trm} (r s t : renaming trm) :
  compose_static r (compose_static s t)
  = compose_static (compose_static r s) t.
Proof.
  induction r; cbn.
  - easy.
  -
  -
  - rewrite IHr; easy.
Qed.

Lemma apply_static_ivar_compose {trm N T M} (r : renaming trm) s
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

Fixpoint apply_static_var {trm} (r : renaming trm) : ivar 0 var 0 :=
  match r with
  | r_id => 1
  | r_shift b r =>
    (open_var b) @ (morph_extend (apply_static_var r)) @ weak_var
  | r_rename b r a =>
    (open_var b) @ (morph_extend (apply_static_var r)) @ (close_var a)
  | r_subst _ r _ => apply_static_var r
  end.

Lemma apply_static_ivar_as_composition {trm N T M} (r : renaming trm)
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

Lemma apply_static_var_spec {trm} (r : renaming trm) :
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

Lemma apply_static_ivar_compose_distribute {trm N T M R L}
      (r : renaming trm) (f : ivar N T M) (g : morph T M R L) :
  g @ (apply_static_ivar r f)
  =m= apply_static_ivar r (g @ f).
Proof.
  intros V v.
  rewrite apply_static_ivar_as_composition.
  rewrite morph_associative.
  rewrite <- apply_static_ivar_as_composition.
  easy.
Qed.

Lemma apply_static_var_compose {trm N T M} (r : renaming trm) s
      (f : ivar N T M) :
  apply_static_var (compose_static r s)
  =m= (apply_static_var s) @ (apply_static_var r).
Proof.
  rewrite apply_static_var_spec.
  rewrite apply_static_ivar_compose.
  rewrite apply_static_ivar_as_composition, apply_static_ivar_as_composition.
  easy.
Qed.
