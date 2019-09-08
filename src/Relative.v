Require Import String Morph Var Context.
Require Setoid Morphisms.

Module Type Term.

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

End Term.

Module Renamings (T : Term).

  Import T.

  Definition openm a :=
    unit @ ((@openv a : morph (@var) 1 (@var) 0)).

  Definition open a := kleisli (openm a).

  Definition closem a :=
    unit @ ((@closev a : morph (@var) 0 (@var) 1)).

  Definition close a := kleisli (closem a).

  Definition wkm :=
    unit @ (@wkv : morph (@var) 0 (@var) 1).

  Definition wk := kleisli wkm.

  Fixpoint wkn {V} (t : @term 0) :=
    match V with
    | 0 => t
    | S V => wk V (@wkn V t)
    end.

  Definition bindm (u : @term 0) : morph (@var) 1 (@term) 0 :=
    fun V v =>
      match bindv v with
      | Some v => @unit 0 V v
      | None => wkn u
      end.

  Definition bind u := kleisli (@bindm u).

  Arguments openm a {V} v /.
  Arguments open a {V} !t.
  Arguments closem a {V} v /.
  Arguments close a {V} !t.
  Arguments wkm {V} v /.
  Arguments wk {V} !t.
  Arguments bindm u {V} !v.
  Arguments bind u {V} !t.

  Definition ren := @renaming (@term 0).

  Fixpoint applyv (r : ren) : morph (@var) 0 (@term) 0 :=
    match r with
    | r_id => unit
    | r_comp r s =>
      (kleisli (applyv r))
        @ (applyv s)
    | r_shift b r =>
      (@open b)
        @ (kleisli (morph_extend (applyv r)))
        @ (@wkm)
    | r_rename b r a =>
      (@open b)
        @ (kleisli (morph_extend (applyv r)))
        @ (@closem a)
    | r_subst u r a =>
      (@bind u)
        @ (kleisli (morph_extend (applyv r)))
        @ (@closem a)
    end.

  Arguments applyv !r {V} t /.

  Notation "[ r ] t" := (kleisli (@applyv (r)%ren) _ t)
    (at level 60, right associativity) : term_scope.
  Bind Scope term_scope with term.
  Open Scope term_scope.

  Lemma unit_extend_0 : forall V t,
    @unit 0 (S V) t = @unit 1 V t.
  Proof.
    intros.
    replace (@unit 0 (S V) t)
      with (morph_extend (@unit 0) V t) by reflexivity.
    rewrite unit_extend.
    reflexivity.
  Qed.

  Lemma kleisli_extend_00 : forall V f t,
    @kleisli 0 0 f (S V) t
    = @kleisli 1 1 (morph_extend f) V t.
  Proof.
    intros.
    replace (@kleisli 0 0 f (S V) t)
      with (morph_extend (@kleisli 0 0 f) V t)
      by reflexivity.
    rewrite kleisli_extend.
    reflexivity.
  Qed.

  Lemma right_identity_ext :
    forall N V (t : @term (N + V)) f,
      (forall V' v', f V' v' = unit V' v') ->
      kleisli f V t = t.
  Proof.
    intros * Heq.
    rewrite extensional with (g := unit);
      auto using right_identity.
  Qed.

  Ltac simpl_term t :=
    match t with
    | @kleisli ?N _ _ ?V (@kleisli _ ?N _ ?V _) =>
      rewrite <- associativity
    | @kleisli 0 0 _ (S _) _ =>
      rewrite kleisli_extend_00
    | @kleisli ?N _ _ ?V (@unit ?N ?V _) =>
      rewrite left_identity
    | @kleisli ?N ?N (@unit ?N) ?V _ =>
      rewrite right_identity
    | @unit 0 (S _) _ =>
      rewrite unit_extend_0
    | morph_compose _ _ _ _ => unfold morph_compose
    | morph_compose _ _ => unfold morph_compose; intros
    | @open _ _ _ => unfold open
    | @openm _ _ _ => unfold openm
    | @close _ _ _ => unfold close
    | @closem _ _ _ => unfold closem
    | @wk _ _ => unfold wk
    | @wkm _ _ => unfold wkm
    | @bind _ _ _ => unfold bind
    | @bindm _ _ _ => unfold bindm
    | kleisli _ _ ?t' =>
      simpl_term t'
    end.

  Ltac simpl_term_eq_step :=
    match goal with
    | |- ?t1 = _ => simpl_term t1; cbn
    | |- _ = ?t2 => simpl_term t2; cbn
    | |- @kleisli ?N ?M _ ?V ?t = @kleisli ?N ?M _ ?V ?t =>
      apply (extensional N M); intros; cbn
    | |- @kleisli ?N ?N _ _ ?t = ?t =>
      apply (right_identity_ext N); intros; cbn
    | |- ?t = @kleisli ?N ?N _ _ ?t =>
      symmetry; apply (right_identity_ext N); intros;
      symmetry; cbn
    | |- _ = _ =>
        progress autorewrite with rw_names rw_vars; cbn
    end.

  Ltac simpl_term_eq :=
    cbn; repeat simpl_term_eq_step; try reflexivity.

  Lemma rw_close_open a :
    forall {V} (t : @term (S V)), close a (open a t) = t.
  Proof.
    intros.
    simpl_term_eq.
  Qed.

  Lemma rw_open_close a :
    forall {V} (t : @term V), open a (close a t) = t.
  Proof.
    intros.
    simpl_term_eq.
  Qed.

  Lemma rw_bind_wk u :
    forall {V} (t : @term V), bind u (wk t) = t.
  Proof.
    intros.
    simpl_term_eq.
  Qed.

  Lemma rw_bindm_wkv u :
    forall {V} (v : @var V), bindm u (wkv v) = @unit 0 V v.
  Proof.
    intros.
    simpl_term_eq.
  Qed.

  Hint Rewrite @rw_close_open @rw_open_close @rw_bind_wk
       @rw_bindm_wkv
    : rw_renaming.
 
  (* identity and composition for apply *)
  Lemma rw_apply_id {V} (t : @term V) : [r_id] t = t.
  Proof. simpl_term_eq. Qed.

  Lemma rw_apply_comp r s {V} (t : @term V) :
    [r] [s] t = [r;s] t.
  Proof. simpl_term_eq. Qed.

  Hint Rewrite @rw_apply_id @rw_apply_comp : rw_renaming.

  (* Simple rewritings on applyv and shiftv (more later) *)
  Lemma rw_applyv_bound r : forall {V} (v : level V),
    @applyv r V (bound v) = @unit 0 V (bound v).
  Proof.
    intros.
    generalize dependent V.
    induction r; intros; simpl_term_eq.
    - rewrite IHr2; simpl_term_eq.
      rewrite IHr1; simpl_term_eq.
    - rewrite IHr; simpl_term_eq.  
    - rewrite IHr; simpl_term_eq.
    - rewrite IHr; simpl_term_eq.
  Qed.

  Hint Rewrite @rw_applyv_bound : rw_renaming.

  (* Rewrite to do the following:
      - group balanced pairs of operations into 'ren's
      - push opens/bind right and wk/close left
      - simplify rens *)

  Lemma rw_group_rename a b {V} (t : @term V) :
    open a (close b t) = [a <- b] t.
  Proof. simpl_term_eq. Qed.

  Lemma rw_group_shift a {V} (t : @term V) :
    open a (wk t) = [^a] t.
  Proof. simpl_term_eq. Qed.

  Lemma rw_group_subst u a {V} (t : @term V) :
    bind u (close a t) = [u // a] t.
  Proof. simpl_term_eq. Qed.

  Hint Rewrite @rw_group_rename @rw_group_shift
       @rw_group_subst
    : rw_renaming.

  (* fold operations *)

  Lemma rw_fold_open a {V} (t : @term (1 + V)) :
    kleisli (@openm a) V t = open a t.
  Proof. easy. Qed.

  Lemma rw_fold_close a {V} (t : @term V) :
    kleisli (@closem a) V t = close a t.
  Proof. easy. Qed.

  Lemma rw_fold_wk {V} (t : @term V) :
    kleisli (@wkm) V t = wk t.
  Proof. easy. Qed.

  Lemma rw_fold_bind u {V} (t : @term (1 + V)) :
    kleisli (@bindm u) V t = bind u t.
  Proof. easy. Qed.

  Hint Rewrite @rw_fold_open @rw_fold_close @rw_fold_wk
       @rw_fold_bind
    : rw_renaming.

  (* wk commutes with shift *)
  Lemma rw_shift_wk b {V} (t : @term V) :
    [^b] (wk t) = wk ([^b] t).
  Proof.
    simpl_term_eq.
    rewrite swap_shiftv_wkv.
    simpl_term_eq.
  Qed.

  Hint Rewrite @rw_shift_wk : rw_renaming.

  (* wk commutes with apply.
     Somewhat harder to prove than I'd expect *)
  Lemma rw_applyv_wkv r : forall {V} (v : @var V),
      applyv r (wkv v) = wk (applyv r v).
  Proof.
    induction r; intros; cbn.
    - simpl_term_eq.
    - rewrite IHr2; simpl_term_eq.
      rewrite IHr1; simpl_term_eq.
    - simpl_term_eq.
      repeat rewrite IHr; simpl_term_eq.
      rewrite swap_shiftv_wkv.
      simpl_term_eq.
    - destruct (compare_vars a v); simpl_term_eq.
      + autorewrite with rw_renaming.
        simpl_term_eq.
      + repeat rewrite IHr.      
        simpl_term_eq.
        rewrite swap_shiftv_wkv.
        simpl_term_eq.
    - destruct (compare_vars a v); simpl_term_eq.
      + autorewrite with rw_renaming.
        simpl_term_eq.
      + repeat rewrite IHr; simpl_term_eq.
  Qed.

  (* FIXME where? *)
  Lemma applyt_is_applyv :
    forall r (rn : total r) {V} (v : @var V),
      applyv r v = unit V (applyt r rn v).
  Proof.
    induction r; cbn; intuition; simpl_term_eq.
    - erewrite IHr2; simpl_term_eq. 
      erewrite IHr1; simpl_term_eq.
    - erewrite IHr; simpl_term_eq.
    - erewrite IHr; simpl_term_eq.
  Qed.

  Lemma applyt_related (A : Set) (Γ Δ : @context A) :
    forall r (rl : Γ =[r]=> Δ) {V} (v : @var V),
      applyv r v = unit V (applyt r (relates_total rl) v).
  Proof.
    intros.
    rewrite applyt_is_applyv with (rn := relates_total rl).
    reflexivity.
  Qed.

  Lemma rw_apply_wk r {V} (t : @term V) :
    kleisli (@applyv r) (S V) (wk t) = wk ([r] t).
  Proof.
    simpl_term_eq.
    apply rw_applyv_wkv.
  Qed.

  Lemma rw_apply_wkn r {V} (t : @term 0) :
    [r] (@wkn V t) = @wkn V ([r] t).
  Proof.
    induction V; cbn; try easy.
    rewrite rw_apply_wk.
    rewrite IHV.
    reflexivity.
  Qed.

  Hint Rewrite @rw_applyv_wkv @rw_apply_wk @rw_apply_wkn
    : rw_renaming.

  Lemma rw_applyv_wkv_free r {a V} :
    applyv r (@free (S V) a) = wk (applyv r (@free V a)).
  Proof.
    change (@free (S V) a) with (wkv (@free V a)).
    apply rw_applyv_wkv.
  Qed.

  Hint Rewrite @rw_applyv_wkv_free : rw_renaming.

  Lemma comm_bind_apply u : forall {V} (t : @term (S V)) r,
    [r] (bind u t) = bind ([r] u) ([r] t).
  Proof.
    intros.
    simpl_term_eq.
    destruct (compare_l0 t0); simpl_term_eq;
      autorewrite with rw_renaming; simpl_term_eq.
  Qed.

  (* FIXME: maybe this should just be "names"? *)
  Lemma rw_close_shift a r {V} (t : @term V) :
    close a ([r, ^a] t) = wk ([r] t).
  Proof.
    simpl_term_eq; autorewrite with rw_renaming; simpl_term_eq.
  Qed.
  Lemma rw_subst_open u r b {V} (t : @term (S V)) :
    [r, u // b] (open b t) = bind u ([r] t).
  Proof. simpl_term_eq. Qed.
  Lemma rw_rename_open a b {V} (t : @term (S V)) :
    [a <- b] (open b t) = open a t.
  Proof. simpl_term_eq. Qed.
  Hint Rewrite @rw_close_shift @rw_subst_open @rw_rename_open : rw_renaming.

  (* FIXME: lots of applyt rewritings below here *)

  (* FIXME: not great, tbh *)

  (* Commuting bind with apply.
     It seems more natural to make
       bind (r u) . r  --> r . bind u
     since bind is similar to open, and open moves right.
     But that rule breaks confluence, and isn't very useful
     as bind doesn't show up in terms. So, binds move left
     instead. *)
  Lemma rw_push_bind u r {V} (t : @term (S V)) :
    [r] (bind u t) = bind ([r] u) ([r] t).
  Proof. apply comm_bind_apply. Qed.
  (* Shifts go the other way.
     This is confluent/terminating because shift doesn't simplify to apply (?) *)
  Lemma rw_push_bind_shift u r s a {V} (t : @term (S V)) :
    bind ([r, ^a] u) ([s, ^ a] t) =
    [^a] (bind ([r]u) ([s]t)).
  Proof.
    rewrite comm_bind_apply.
    autorewrite with rw_renaming; simpl_term_eq.
    autorewrite with rw_renaming; simpl_term_eq.
    destruct (compare_l0 t1); simpl_term_eq.
    f_equal.
    simpl_term_eq.
    autorewrite with rw_renaming; simpl_term_eq.
  Qed.
  Lemma rw_push_bind_shiftvu v a {V} (t : @term (S V)) :
    bind (@unit 0 0 (shiftv a v)) ([^a] t)
    = [^a] (bind (unit 0 v) t).
  Proof.
    replace (unit 0 (shiftv a v)) with ([^a] (unit 0 v))
      by simpl_term_eq.
    rewrite rw_push_bind_shift.
    autorewrite with rw_renaming; easy.
  Qed.

  Hint Rewrite
    @rw_push_bind @rw_push_bind_shift @rw_push_bind_shiftvu
    : rw_renaming.

  (* Morphisms. *)
  Import Setoid Morphisms.

(* FIXME: is it better to define eqr over all vars or just free ones? *)
  Definition eqr (r s : ren) : Prop :=
    forall V (v : @var V),
      applyv r v = applyv s v.

  Instance eqr_Equivalence : Equivalence eqr.
  Proof.
    split; red; unfold eqr; auto.
    intros. etransitivity; eauto.
  Qed.

  Instance mor_applyv : Proper
    (eqr ==> forall_relation (fun _ => (eq ==> eq))) applyv.
  Proof. intros r s Hrs V v v' <-. auto. Qed.

  Instance mor_kleisli : Proper
    (forall_relation (fun _ => (eq ==> eq))
    ==> forall_relation (fun _ => (eq ==> eq)))
    (@kleisli 0 0).
  Proof.
    intros r s Hrs V a b <-.
    simpl_term_eq.
    apply Hrs; reflexivity.
  Qed.

  Ltac easy_eqr :=
    repeat intro; simpl_term_eq;
    repeat
      match goal with
      | [ H : _ |- _ ] =>
        rewrite H; clear H; simpl_term_eq
      end.

  Instance mor_r_comp : Proper
    (eqr ==> eqr ==> eqr) r_comp. easy_eqr. Qed.
  Instance mor_r_shift : Proper
    (eq ==> eqr ==> eqr) r_shift. easy_eqr. Qed.
  Instance mor_r_rename : Proper
    (eq ==> eqr ==> eq ==> eqr) r_rename. easy_eqr. Qed.
  Instance mor_r_subst : Proper
    (eq ==> eqr ==> eq ==> eqr) r_subst. easy_eqr. Qed.

  Lemma rw_ren_id_comp r : eqr (r_comp r_id r) r.
  Proof. easy_eqr. Qed.
  Lemma rw_ren_comp_id r : eqr (r_comp r r_id) r.
  Proof. easy_eqr. Qed.
  Lemma rw_ren_comp_assoc r s t :
    eqr (r_comp r (r_comp s t)) (r_comp (r_comp r s) t).
  Proof. easy_eqr. Qed.
  Lemma rw_ren_under_id x :
    eqr (r_rename x r_id x) r_id.
  Proof. easy_eqr. Qed.
  Lemma rw_ren_rename_rename c b a r s :
    eqr (r_comp (r_rename c r b) (r_rename b s a))
        (r_rename c (r_comp r s) a).
  Proof. easy_eqr. Qed.
  Lemma rw_ren_rename_rename_comp l c b a r s :
    eqr (r_comp (r_comp l (r_rename c r b)) (r_rename b s a))
        (r_comp l (r_rename c (r_comp r s) a)).
  Proof. easy_eqr. Qed.
  Lemma rw_ren_rename_shift c b r s :
    eqr (r_comp (r_rename c r b) (r_shift b s))
        (r_shift c (r_comp r s)).
  Proof. easy_eqr. Qed.
   Lemma rw_ren_rename_shift_comp l c b r s :
    eqr (r_comp (r_comp l (r_rename c r b)) (r_shift b s))
        (r_comp l (r_shift c (r_comp r s))).
  Proof. easy_eqr. Qed.
  Lemma rw_ren_subst_rename u r a s b :
    eqr (r_comp (r_subst u r a) (r_rename a s b))
        (r_subst u (r_comp r s) b).
  Proof. easy_eqr. Qed.
  Lemma rw_ren_subst_rename_comp l u r a s b :
    eqr (r_comp (r_comp l (r_subst u r a)) (r_rename a s b))
        (r_comp l (r_subst u (r_comp r s) b)).
  Proof. easy_eqr. Qed.
  Lemma rw_ren_subst_shift u r a s :
    eqr (r_comp (r_subst u r a) (r_shift a s))
        (r_comp r s).
  Proof.
    repeat intro; simpl_term_eq.
    (* FIXME: this again. Should we remove free?
       Should we do this automatically?
       Should we define eqr in terms of all vars,
       not just free ones? *)
    repeat match goal with
    | |- context C [@free (S ?v) ?x] =>
    change (@free (S v) x) with (@wkv v (free x)) end.
    autorewrite with rw_renaming; simpl_term_eq.
    autorewrite with rw_renaming; simpl_term_eq.
  Qed.
  Lemma rw_ren_subst_shift_comp l u r a s :
    eqr (r_comp (r_comp l (r_subst u r a)) (r_shift a s))
        (r_comp l (r_comp r s)).
  Proof.
    repeat intro; simpl_term_eq.
    repeat match goal with
    | |- context C [@free (S ?v) ?x] =>
      change (@free (S v) x) with (@wkv v (free x)) end.
    autorewrite with rw_renaming; simpl_term_eq.
    autorewrite with rw_renaming; simpl_term_eq.
  Qed.
  Lemma rw_ren_shift_any a r s :
    eqr (r_comp (r_shift a r) s) (r_shift a (r_comp r s)).
  Proof.
    repeat intro; simpl_term_eq.
    autorewrite with rw_renaming; simpl_term_eq.
  Qed.
  Lemma rw_ren_shift_any_comp l a r s :
    eqr (r_comp (r_comp l (r_shift a r)) s)
        (r_comp l (r_shift a (r_comp r s))).
  Proof.
    repeat intro; simpl_term_eq.
    autorewrite with rw_renaming; simpl_term_eq.
  Qed.
  Lemma rw_ren_any_subst r u s x :
    eqr (r_comp r (r_subst u s x))
        (r_subst ([r] u) (r_comp r s) x).
  Proof. 
    repeat intro; simpl_term_eq.
    destruct (compare_l0 t); simpl_term_eq;
      autorewrite with rw_renaming; simpl_term_eq.
  Qed.

  (* No _comp version required for any_subst *)
  (* Ensure crit pair of rw_ren_shift_any and
     rw_ren_any_subst is confluent *)
  Lemma rw_ren_shift_subst_crit a u r b :
    eqr (r_subst ([^a] u) (r_shift a r) b)
        (r_shift a (r_subst u r b)).
  Proof.
    Set Printing Implicit.
    repeat intro; simpl_term_eq.
    autorewrite with rw_renaming.
    repeat rewrite <- rw_apply_comp.
    repeat rewrite rw_apply_id.
    rewrite rw_push_bind_shift.
    repeat rewrite rw_apply_id.
    replace (bind u (@applyv r (S V) (closev b v)))
      with (@applyv (r_subst u r b) V v)
      by simpl_term_eq.
    replace (bind u (@applyv r (S (S V)) (closev b (wkv v))))
      with (@applyv (r_subst u r b) (S V) (wkv v))
      by simpl_term_eq.
    rewrite rw_applyv_wkv.
    simpl_term_eq.
  Qed.

  Hint Rewrite
    @rw_ren_id_comp
    @rw_ren_comp_id
    @rw_ren_comp_assoc
    @rw_ren_under_id
    @rw_ren_rename_rename
    @rw_ren_rename_rename_comp
    @rw_ren_rename_shift
    @rw_ren_rename_shift_comp
    @rw_ren_subst_rename
    @rw_ren_subst_rename_comp
    @rw_ren_subst_shift
    @rw_ren_subst_shift_comp
    @rw_ren_shift_any
    @rw_ren_shift_any_comp
    @rw_ren_any_subst
    @rw_ren_shift_subst_crit : rw_renaming.

  (* Commuting open and close with apply *)
  
  Lemma rw_push_open a r {V} (t : @term (S V)) :
    open a ([r] t) = [r, a] (open a t).
  Proof. simpl_term_eq. Qed.
  Lemma rw_push_close a r {V} (t : @term V) :
    [r] (close a t) = close a ([r, a] t).
  Proof.  simpl_term_eq. Qed.
  Hint Rewrite @rw_push_open @rw_push_close : rw_renaming.

  Arguments term / {V}.

  Arguments unit {N} / V t.

  Arguments kleisli {N M} f V !t /.

  Ltac names :=
    repeat progress
      (cbn; autorewrite with rw_renaming rw_vars rw_names).

  Tactic Notation "names" "in" hyp(H) :=
    repeat progress
      (cbn in H; autorewrite with rw_renaming in H).

  Lemma swap_subst_subst_distinct {x y}
        (Hd : distinct_names x y) {u v R} :
    eqr (r_subst u (r_subst v R x) y)
        (r_subst v (r_subst u R y) x).
  Proof.
    intros V p. simpl_term_eq.
    rewrite (swap_close_close Hd).
    destruct (closev y (closev x _)) as [?|[|[|?]]];
      names; simpl_term_eq.
  Qed.

End Renamings.
