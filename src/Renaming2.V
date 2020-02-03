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

Fixpoint apply_static_ivar {trm} (r : renaming trm) :
  forall (sr : static r) {N T M} (f : ivar N T M), ivar N T M :=
  match r with
  | r_id => fun sr _ _ _ f => f
  | r_shift b r =>
    fun (sr : static (r_shift b r)) _ _ _ f =>
      weak_ivar (apply_static_ivar r sr (open_ivar b f))
  | r_rename b r a =>
    fun (sr : static (r_rename b r a)) _ _ _ f =>
      close_ivar a (apply_static_ivar r sr (open_ivar b f))
  | r_subst _ _ _ =>
      fun (sr : static (r_subst _ _ _)) _ _ _ _ => False_rec _ sr
  end.

Add Parametric Morphism {trm r sr N} {T : nset} {M}
  : (@apply_static_ivar trm r sr N T M)
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
  - easy.
Qed.

Lemma snd_apply_static_ivar {trm N T M} (r : renaming trm) sr
      (f : ivar N T M) :
  snd_ivar (apply_static_ivar r sr f) = snd_ivar f.
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

Lemma fst_apply_static_ivar {trm N T M} (r : renaming trm) sr
      (f : ivar N T M) (g : ivar N T M) :
  fst_ivar f =km= fst_ivar g ->
  fst_ivar (apply_static_ivar r sr f) =km= fst_ivar (apply_static_ivar r sr g).
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
  - easy.
Qed.

Lemma swap_apply_static_ivar_transpose_ivar {trm N T M} (r : renaming trm) sr
      (f : ivar (S (S N)) T M) :
  apply_static_ivar r sr (transpose_ivar f)
  =m= transpose_ivar (apply_static_ivar r sr f).
Proof.
  rewrite <- ivar_eta_pointwise.
  unfold transpose_ivar.
  rewrite snd_apply_static_ivar, snd_apply_static_ivar.
  rewrite fst_apply_static_ivar with (g := f) by easy.
  simpl_ivars_pointwise.
  easy.
Qed.

Fixpoint transfer_open_var {trm} (r : renaming trm)
  : forall (sr : static r) (a : name), name * renaming trm :=
  match r with
  | r_id => fun sr a => pair a r_id
  | r_shift b r =>
      fun (sr : static (r_shift b r)) a =>
        let (a', r') := transfer_open_var r sr a in
        pair (shift_name b a') (r_shift (unshift_name a' b) r')
  | r_rename c r b =>
      fun sr a =>
        match name_eqb a b with
        | true => pair c r
        | false =>
          let (a', r') := transfer_open_var r sr (unshift_name b a) in
          pair (shift_name c a')
               (r_rename (unshift_name a' c) r' (unshift_name a b))
        end
  | r_subst _ _ _ => False_rec _
  end.

Lemma transfer_open_var_spec {trm} (r : renaming trm) sr r' sr' a a' :
  pair a' r' = transfer_open_var r sr a ->
  forall {N T M} (f : ivar N T M),
  open_ivar a (apply_static_ivar r sr f)
  =m= apply_static_ivar r' sr' (open_ivar a' f).
Proof.
  generalize dependent r'.
  generalize dependent a'.
  generalize dependent a.
  induction r; intros c c' r' sr' Hcr' N T M f; cbn in *.
  - inversion Hcr'; subst; easy.
  - remember (transfer_open_var r sr c) as cr'' eqn:Hcr''.
    destruct cr'' as [c'' r''].
    inversion Hcr'; subst; cbn.
    specialize (IHr sr c c'' r'' sr' Hcr'').
    rewrite swap_open_ivar_weak_ivar_pointwise.
    rewrite IHr.
    rewrite <- swap_apply_static_ivar_transpose_ivar.
    rewrite swap_open_ivar_open_ivar_pointwise.
    easy.
  - remember (transfer_open_var r sr (unshift_name a c))
      as cr'' eqn:Hcr''.
    remember (name_eqb c a) as ca eqn:Hca.
    symmetry in Hca.
    destruct ca.
    + destruct cr'' as [c'' r''].
      inversion Hcr'; subst; cbn.
      apply name_eqb_eq in Hca; subst.
      simpl_ivars_pointwise.
      easy.
    + destruct cr'' as [c'' r''].
      inversion Hcr'; subst; cbn.
      specialize (IHr (unshift_name a c) c'' r'' Hcr'').
      apply name_eqb_neq in Hca.
      rewrite swap_open_ivar_close_ivar_pointwise by easy.
      rewrite IHr.
      rewrite <- swap_apply_static_ivar_transpose_ivar.
      rewrite swap_open_ivar_open_ivar_pointwise.
      easy.
Qed.

Fixpoint scompose (r : srenaming) (s : srenaming) :=
  match r with
  | sr_id => s
  | sr_shift a r =>
    let (a', s') := transfer_open_var s a in
    let r' := scompose r s' in
    sr_shift a' r'
  | sr_rename a r b =>
    let (a', s') := transfer_open_var s a in
    let r' := scompose r s' in
    sr_rename a' r' b
  end.

Lemma apply_static_ivar_scompose {N T M} r s (f : ivar N T M) :
  apply_static_ivar (scompose r s) f
  =m= apply_static_ivar r (apply_static_ivar s f).
Proof.
  generalize dependent M.
  generalize dependent T.
  generalize dependent N.
  generalize dependent s.
  induction r; intros s N T M f; cbn.
  - easy.
  - remember (transfer_open_var s b) as bs' eqn:Hbs'.
    destruct bs' as [b' s']; cbn.
    rewrite transfer_open_var_spec by eassumption.
    rewrite <- IHr.
    easy.
  - remember (transfer_open_var s b) as bs' eqn:Hbs'.
    destruct bs' as [b' s']; cbn.
    rewrite transfer_open_var_spec by eassumption.
    rewrite <- IHr.
    easy.
Qed.

Fixpoint apply_static_var (r : srenaming) : ivar 0 var 0 :=
  match r with
  | sr_id => 1
  | sr_shift b r =>
    (open_var b) @ (morph_extend (apply_static_var r)) @ weak_var
  | sr_rename b r a =>
    (open_var b) @ (morph_extend (apply_static_var r)) @ (close_var a)
  end.

Lemma apply_static_ivar_as_map {N T M} r (f : ivar N T M) :
  apply_static_ivar r f =m=
  map_ivar (morph_extend_by N (apply_static_var r)) f.
Proof.
  generalize dependent M.
  generalize dependent T.
  generalize dependent N.
  induction r; intros N T M f; cbn.
  - rewrite morph_extend_by_id.
    easy.
  - rewrite morph_extend_by_compose, morph_extend_by_compose.
    rewrite map_ivar_compose, map_ivar_compose.
    rewrite weak_ivar_as_map, open_ivar_as_map.
    rewrite IHr; cbn.
    easy.
  - rewrite morph_extend_by_compose, morph_extend_by_compose.
    rewrite map_ivar_compose, map_ivar_compose.
    rewrite close_ivar_as_map, open_ivar_as_map.
    rewrite IHr.
    easy.
Qed.

Lemma apply_static_var_spec r :
  apply_static_var r =m= apply_static_ivar r 1.
Proof.
  induction r; cbn.
  - easy.
  - rewrite weak_ivar_as_map, open_ivar_as_map, apply_static_ivar_as_map.
    easy.
  - rewrite close_ivar_as_map, open_ivar_as_map, apply_static_ivar_as_map.
    easy.
Qed.

Lemma apply_static_var_scompose {N T M} r s (f : ivar N T M) :
  apply_static_var (scompose r s)
  =m= (apply_static_var s) @ (apply_static_var r).
Proof.
  rewrite apply_static_var_spec.
  rewrite apply_static_ivar_scompose.
  rewrite apply_static_ivar_as_map, apply_static_ivar_as_map.
  easy.
Qed.
