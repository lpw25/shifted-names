Require Import Setoid Morphisms StrictProp
        Morph Index Name Level Var2.

(* Algebra of operations on [var 0] *)
Inductive renaming (trm : nset) :=
| r_id
| r_shift (b : name) (r : renaming trm)
| r_rename (b : name) (r : renaming trm) (a : name)
| r_subst (t : trm 0) (r : renaming trm) (a : name).

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

(*
Delimit Scope ren_scope with ren.
*)

Section Apply.

  Context {trm : nset}.

  Variable unit : forall {N}, ivar N (@trm) N.

  Variable kleisli :
    forall {N M},
      ivar N (@trm) M ->
      morph (@trm) N (@trm) M.

  Fixpoint apply_renaming (r : renaming trm) {N M}
  : static r -> ivar N T M -> ivar N T M :=
  match r return static r -> ivar N T M -> ivar N T M with
  | r_id => fun _ f => f
  | r_shift b r =>
      fun s f =>
        weak_ivar (apply_static_ivar r s (open_ivar b f))
  | r_rename b r a =>
      fun s f =>
        close_ivar a (apply_static_ivar r s (open_ivar b f))
  | r_subst _ r _ => sEmpty_rect _
  end.
  Arguments apply_static_ivar {T} r {N M} s f.

End Apply.

Section RenamingRelativeMonad.

  Parameter term : forall {V : nat}, Set.

  Parameter unit : forall {N}, morph (@var) N (@term) N.

  Parameter kleisli :
    forall {N M},
      morph (@var) N (@term) M ->
      morph (@term) N (@term) M.

  Axiom left_identity :
    forall N M (f : morph (@var) N (@term) M) V t,
      kleisli f V (unit V t) = f V t.

  Axiom right_identity :
    forall N V (t : @term (N + V)),
      kleisli unit V t = t.

  Axiom associativity :
    forall N M L
      (f : morph (@var) N (@term) M)
      (g : morph (@var) M (@term) L) V t,
      kleisli (fun V' t' => kleisli g V' (f V' t')) V t
      = kleisli g V (kleisli f V t).

  Axiom unit_extend :
    forall N V v,
      morph_extend (@unit N) V v = unit V v.

  Axiom kleisli_extend :
    forall N M (f : morph (@var) N (@term) M) V t,
      morph_extend (kleisli f) V t
      = kleisli (morph_extend f) V t.

  Axiom extensional :
    forall N M (f g : morph (@var) N (@term) M) V t,
      (forall V t, f V t = g V t) ->
      kleisli f V t = kleisli g V t.




Fixpoint static {T : nset} (r : renaming T) : SProp :=
  match r with
  | r_id => sUnit
  | r_shift b r => static r
  | r_rename b r a => static r
  | r_subst u r a => sEmpty
  end.

Fixpoint apply_static_ivar {T} (r : renaming T) {N M}
  : static r -> ivar N T M -> ivar N T M :=
  match r return static r -> ivar N T M -> ivar N T M with
  | r_id => fun _ f => f
  | r_shift b r =>
      fun s f =>
        weak_ivar (apply_static_ivar r s (open_ivar b f))
  | r_rename b r a =>
      fun s f =>
        close_ivar a (apply_static_ivar r s (open_ivar b f))
  | r_subst _ r _ => sEmpty_rect _
  end.
Arguments apply_static_ivar {T} r {N M} s f.

Add Parametric Morphism {T r N M s}
  : (@apply_static_ivar T r N M s)
    with signature eq_morph ==> eq_morph
    as sapply_ivar_mor.
  generalize dependent M.
  generalize dependent N.
  induction r; intros * Heq; cbn.
  - easy.
  - rewrite IHr with (y := open_ivar b y)
      by (rewrite Heq; easy).
    easy.
  - rewrite IHr with (y := open_ivar b y)
      by (rewrite Heq; easy).
    easy.
  - easy.
Qed.

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

Fixpoint transfer_open_var {T} (r : renaming T) (a : name) :
  name * renaming T :=
  match r with
  | r_id => pair a r_id
  | r_shift b r =>
      let ar' := transfer_open_var r a in
      pair (shift_below_name b (fst ar'))
           (r_shift (unshift_name (fst ar') b) (snd ar'))
  | r_rename c r b =>
      match name_eqb a b with
      | true => pair c r
      | false =>
        let ar' := transfer_open_var r (unshift_name b a) in
        pair (shift_below_name c (fst ar'))
             (r_rename (unshift_name (fst ar') c)
                       (snd ar')
                       (unshift_name a b))
      end
  | r_subst t r b =>
        let ar' := transfer_open_var r a in
        pair (fst ar') (r_subst t (snd ar')  b)
  end.

Lemma transfer_open_var_spec {T} (r : renaming T) a :
  forall {N M} (f : ivar N T M),
  open_ivar a (apply_static_ivar r f)
  =m= apply_static_ivar
        (snd (transfer_open_var r a))
        (open_ivar (fst (transfer_open_var r a)) f).
Proof.
  generalize dependent a.
  induction r; intros c N M f; cbn in *.
  - easy.
  - rewrite transpose_open_ivar_weak_ivar_pointwise.
    rewrite IHr.
    rewrite transpose_swap_ivar_apply_static_ivar.
    rewrite transpose_open_ivar_open_ivar_pointwise.
    easy.
  - remember (name_eqb c a) as eq_ca eqn:Hca.
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

Fixpoint compose_static {T}
         (r : renaming T) (s : renaming T) :=
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

Fixpoint apply_static_var {T} (r : renaming T) : ivar 0 var 0 :=
  match r with
  | r_id => 1
  | r_shift b r =>
    (open_var b) @ (morph_extend (apply_static_var r)) @ weak_var
  | r_rename b r a =>
    (open_var b) @ (morph_extend (apply_static_var r)) @ (close_var a)
  | r_subst _ r _ => apply_static_var r
  end.

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
