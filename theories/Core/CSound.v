(** * The normaliser is sound for comprehension models

    The meaning of a word, of a value and of a step in a comprehension
    model ([Comp]); every operation of [CNorm] keeps the meaning; so two
    expressions with the same normal form are equal in every model
    consistent with the facts ([cn_sound]). *)

From Stdlib Require Import List Bool.
From ShiftedNames.Core Require Import Label Normalise CNorm Comp.
Import ListNotations.

Section Sem.

Variable M : cmodel.
Local Notation U := (cU M).
Local Notation A := (cA M).

(** Values are read at the end of the word: [x] is the environment there. *)
Fixpoint vden (v : cval) (x : U) {struct v} : A :=
  let fix wd (w : cword) (x : U) {struct w} : U :=
    match w with
    | [] => x
    | s :: w' =>
        match s with
        | SE h v => cpush h (wd w' x) (vden v x)
        | SW h => cpop h (wd w' x)
        | SA a => catom a (wd w' x)
        end
    end in
  match v with
  | VVar h i => cname h i x
  | VTerm u b p => cterm u b (wd p x)
  | VLook h i w => cname h i (wd w x)
  end.

(** One step, in front of the environment [y], values read at [x]. *)
Definition sden (s : cstep) (y x : U) : U :=
  match s with
  | SE h v => cpush h y (vden v x)
  | SW h => cpop h y
  | SA a => catom a y
  end.

Fixpoint wden (w : cword) (x : U) : U :=
  match w with [] => x | s :: w' => sden s (wden w' x) x end.

(** The steps [p] in front of [y], values read at [x]. *)
Fixpoint wpre (p : cword) (y x : U) : U :=
  match p with [] => y | s :: p' => sden s (wpre p' y x) x end.

(** The word semantics [vden] uses inside, by name. *)
Definition wdv : cword -> U -> U :=
  fix wd (w : cword) (x : U) {struct w} : U :=
    match w with
    | [] => x
    | s :: w' =>
        match s with
        | SE h v => cpush h (wd w' x) (vden v x)
        | SW h => cpop h (wd w' x)
        | SA a => catom a (wd w' x)
        end
    end.

Lemma wdv_wden w x : wdv w x = wden w x.
Proof. induction w as [|s w IH]; [reflexivity|]; destruct s; cbn [wden sden]; rewrite <- IH; reflexivity. Qed.

Lemma vden_look h i w x : vden (VLook h i w) x = cname h i (wden w x).
Proof. rewrite <- wdv_wden; reflexivity. Qed.

Lemma vden_term u b w x : vden (VTerm u b w) x = cterm u b (wden w x).
Proof. rewrite <- wdv_wden; reflexivity. Qed.

Lemma vden_var h i x : vden (VVar h i) x = cname h i x.
Proof. reflexivity. Qed.

Lemma wden_app p q x : wden (p ++ q) x = wpre p (wden q x) x.
Proof. induction p as [|s p IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma wpre_app p q y x : wpre (p ++ q) y x = wpre p (wpre q y x) x.
Proof. induction p as [|s p IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma iter_succ_r {B} n (f : B -> B) z : iter (S n) f z = iter n f (f z).
Proof. induction n as [|n IH]; cbn; [reflexivity|]; cbn in IH; rewrite IH; reflexivity. Qed.

Lemma cname_push h i (y : U) t : cname h (S i) (cpush h y t) = cname h i y.
Proof. unfold cname; rewrite iter_succ_r, cpop_push; reflexivity. Qed.

Lemma cname_push0 h (y : U) t : cname h 0 (cpush h y t) = t.
Proof. unfold cname; cbn; apply chd_push. Qed.

Lemma cname_pop h i (y : U) : cname h i (cpop h y) = cname h (S i) y.
Proof. unfold cname; rewrite iter_succ_r; reflexivity. Qed.

Lemma cname0 h (y : U) : cname h 0 y = chd h y.
Proof. reflexivity. Qed.

(** ** Steps on labels the facts show distinct *)

Variable F : order.
Hypothesis HM : ccons F M.

Lemma kd_known g h : kd F g h = true -> known_distinct F g h.
Proof.
  unfold kd; rewrite lcmp_eq; unfold lcmp_spec; destruct (lexp_eqb g h); [discriminate|].
  destruct (lt_known F g h) eqn:E1; [intros _; left; exact E1|].
  destruct (lt_known F h g) eqn:E2; [intros _; right; exact E2|discriminate].
Qed.

Lemma before_known g h : before F g h = true -> known_distinct F g h.
Proof.
  unfold before; rewrite lcmp_eq; unfold lcmp_spec; destruct (lexp_eqb g h); [discriminate|].
  destruct (lt_known F g h) eqn:E1; [intros _; left; exact E1|].
  destruct (lt_known F h g); discriminate.
Qed.

(** A step on a label known distinct from [h]. *)
Definition sdist (h : lexp) (s : cstep) : Prop :=
  exists l, slabel s = Some l /\ known_distinct F l h.

Lemma sdist_pop h s y x : sdist h s -> cpop h (sden s y x) = sden s (cpop h y) x.
Proof.
  intros [l [E D]]; destruct s as [g v|g|a]; cbn in E |- *; try discriminate; injection E as ->.
  - apply (kd_pop_push F M HM h l (known_distinct_sym F _ _ D)).
  - apply (kd_pops F M HM h l (known_distinct_sym F _ _ D)).
Qed.

Lemma sdist_push h s y x t : sdist h s -> cpush h (sden s y x) t = sden s (cpush h y t) x.
Proof.
  intros [l [E D]]; destruct s as [g v|g|a]; cbn in E |- *; try discriminate; injection E as ->.
  - apply (kd_push_push F M HM h l (known_distinct_sym F _ _ D)).
  - symmetry; apply (kd_pop_push F M HM l h D).
Qed.

Lemma sdist_chd h s y x : sdist h s -> chd h (sden s y x) = chd h y.
Proof.
  intros [l [E D]]; destruct s as [g v|g|a]; cbn in E |- *; try discriminate; injection E as ->.
  - apply (kd_hd_push F M HM h l (known_distinct_sym F _ _ D)).
  - apply (kd_pops F M HM l h D).
Qed.

Lemma sdist_pops h s i y x : sdist h s -> iter i (cpop h) (sden s y x) = sden s (iter i (cpop h) y) x.
Proof. intros D; induction i as [|i IH]; cbn; [reflexivity|rewrite IH; apply sdist_pop, D]. Qed.

Lemma sdist_cname h s i y x : sdist h s -> cname h i (sden s y x) = cname h i y.
Proof. intros D; unfold cname; rewrite sdist_pops by exact D; apply sdist_chd, D. Qed.

Lemma wpre_pop h p y x : Forall (sdist h) p -> cpop h (wpre p y x) = wpre p (cpop h y) x.
Proof.
  induction p as [|s p IH]; intros D; cbn; [reflexivity|].
  inversion D; subst; rewrite sdist_pop by assumption; rewrite IH by assumption; reflexivity.
Qed.

Lemma wpre_push h p y x t : Forall (sdist h) p -> cpush h (wpre p y x) t = wpre p (cpush h y t) x.
Proof.
  induction p as [|s p IH]; intros D; cbn; [reflexivity|].
  inversion D; subst; rewrite sdist_push by assumption; rewrite IH by assumption; reflexivity.
Qed.

Lemma wpre_cname h i p y x : Forall (sdist h) p -> cname h i (wpre p y x) = cname h i y.
Proof.
  induction p as [|s p IH]; intros D; cbn; [reflexivity|].
  inversion D; subst; rewrite sdist_cname by assumption; apply IH; assumption.
Qed.

(** Two steps on labels known distinct commute. *)

Lemma sden_comm s t y x l :
  slabel s = Some l -> sdist l t -> sden t (sden s y x) x = sden s (sden t y x) x.
Proof.
  intros Es D; destruct s as [g v|g|a]; cbn in Es |- *; try discriminate; injection Es as ->.
  - rewrite sdist_push by exact D; reflexivity.
  - rewrite sdist_pop by exact D; reflexivity.
Qed.

(** A step on a label known distinct from those of [p] passes it. *)
Lemma wpre_comm s l p y x :
  slabel s = Some l -> Forall (sdist l) p -> wpre p (sden s y x) x = sden s (wpre p y x) x.
Proof.
  intros Es; induction p as [|t p IH]; intros D; cbn; [reflexivity|].
  inversion D; subst; rewrite IH by assumption; apply (sden_comm s t _ x l Es); assumption.
Qed.

(** ** Following a variable *)

(** A step [follow] passes does not affect [hᵢ] behind the kept steps
    [pre]. *)
Lemma pass_sound h i pre s l y x :
  slabel s = Some l -> kd F h l = true -> Forall (sdist l) pre ->
  cname h i (wpre pre (sden s y x) x) = cname h i (wpre pre y x).
Proof.
  intros Es K D; rewrite (wpre_comm s l pre y x Es D).
  apply sdist_cname; exists l; split; [exact Es|apply known_distinct_sym, kd_known, K].
Qed.

Lemma forallb_sbef_sdist l kept : forallb (sbef F l) kept = true -> Forall (sdist l) (rev kept).
Proof.
  intros Hk; apply Forall_rev; rewrite forallb_forall in Hk; rewrite Forall_forall; intros t Ht.
  specialize (Hk t Ht); unfold sbef in Hk; destruct (slabel t) as [m|] eqn:Em; [|discriminate].
  exists m; split; [exact Em|apply before_known, Hk].
Qed.

Lemma follow_sound h w : forall i kept x,
  vden (follow F h i kept w) x = cname h i (wden (rev kept ++ w) x).
Proof.
  induction w as [|s w IH]; intros i kept x.
  - destruct kept as [|t kept]; [reflexivity|]; cbn [follow]; rewrite vden_look, app_nil_r; reflexivity.
  - assert (Pass : forall l, slabel s = Some l -> passes F h l kept = true ->
      vden (follow F h i kept w) x = cname h i (wden (rev kept ++ s :: w) x)).
    { intros l El P; unfold passes in P; apply andb_true_iff in P as [P1 P2].
      rewrite IH, !wden_app; cbn [wden]; symmetry; apply (pass_sound h i _ s l); [exact El|exact P1|].
      apply forallb_sbef_sdist, P2. }
    assert (Keep : vden (follow F h i (s :: kept) w) x = cname h i (wden (rev kept ++ s :: w) x)).
    { rewrite IH; cbn [rev]; rewrite <- app_assoc; reflexivity. }
    destruct s as [g v|g|a]; cbn [follow].
    + destruct (passes F h g kept) eqn:P; [apply (Pass g eq_refl P)|].
      destruct kept as [|t kept']; [|exact Keep].
      destruct (lexp_eqb g h) eqn:E; [|exact Keep].
      apply lexp_eqb_eq in E; subst g; cbn [rev app wden sden]; destruct i as [|i].
      * rewrite cname_push0; reflexivity.
      * rewrite cname_push, IH; reflexivity.
    + destruct (passes F h g kept) eqn:P; [apply (Pass g eq_refl P)|].
      destruct kept as [|t kept']; [|exact Keep].
      destruct (lexp_eqb g h) eqn:E; [|exact Keep].
      apply lexp_eqb_eq in E; subst g; cbn [rev app wden sden]; rewrite cname_pop, IH; reflexivity.
    + rewrite vden_look, rev_append_rev; reflexivity.
Qed.

(** ** Lookups *)

Lemma lookup_sound h w i x : vden (lookup F h i w) x = cname h i (wden w x).
Proof. apply (follow_sound h w i [] x). Qed.

(** ** Pushing steps *)

Lemma stop_spec h w : forall p r, stop F h w = (p, r) ->
  w = p ++ r /\ Forall (fun s => exists g, slabel s = Some g /\ before F g h = true) p.
Proof.
  induction w as [|s w IH]; intros p r E; cbn in E.
  - injection E as <- <-; split; [reflexivity|constructor].
  - destruct s as [g v|g|a].
    + destruct (before F g h) eqn:B; [|injection E as <- <-; split; [reflexivity|constructor]].
      destruct (stop F h w) as [p' r'] eqn:E'; injection E as <- <-.
      destruct (IH p' r' eq_refl) as [-> Hp]; split; [reflexivity|].
      constructor; [exists g; split; [reflexivity|exact B]|exact Hp].
    + destruct (before F g h) eqn:B; [|injection E as <- <-; split; [reflexivity|constructor]].
      destruct (stop F h w) as [p' r'] eqn:E'; injection E as <- <-.
      destruct (IH p' r' eq_refl) as [-> Hp]; split; [reflexivity|].
      constructor; [exists g; split; [reflexivity|exact B]|exact Hp].
    + injection E as <- <-; split; [reflexivity|constructor].
Qed.

Lemma before_sdist h p : Forall (fun s => exists g, slabel s = Some g /\ before F g h = true) p -> Forall (sdist h) p.
Proof.
  intros H; eapply Forall_impl; [|exact H]; intros s [g [E B]]; exists g; split; [exact E|apply before_known, B].
Qed.

Lemma pushW_sound h w x : wden (pushW F h w) x = cpop h (wden w x).
Proof.
  unfold pushW; destruct (stop F h w) as [p r] eqn:E; destruct (stop_spec h w p r E) as [-> Hp].
  apply before_sdist in Hp; rewrite wden_app, wpre_pop by exact Hp.
  assert (D : wden (p ++ SW h :: r) x = wpre p (cpop h (wden r x)) x) by (rewrite wden_app; reflexivity).
  destruct r as [|[g v|g|a] r']; try exact D.
  destruct (lexp_eqb g h) eqn:G; [|exact D].
  apply lexp_eqb_eq in G; subst g; rewrite wden_app; cbn [wden sden]; rewrite cpop_push; reflexivity.
Qed.

Lemma pushE_sound h v w x : wden (pushE F h v w) x = cpush h (wden w x) (vden v x).
Proof.
  unfold pushE; destruct (stop F h w) as [p r] eqn:E; destruct (stop_spec h w p r E) as [-> Hp].
  apply before_sdist in Hp; rewrite wden_app, wpre_push by exact Hp.
  assert (D : wden (p ++ SE h v :: r) x = wpre p (cpush h (wden r x) (vden v x)) x) by (rewrite wden_app; reflexivity).
  destruct r as [|[g v'|g|a] r']; try exact D.
  destruct (lexp_eqb g h && val_eqb v (lookup F h 0 r')) eqn:G; [|exact D].
  apply andb_true_iff in G as [G1 G2]; apply lexp_eqb_eq in G1; apply val_eqb_eq in G2; subst g v.
  rewrite wden_app; cbn [wden sden]; f_equal.
  rewrite lookup_sound, cname0; symmetry; apply cpush_pop.
Qed.

(** ** Payloads *)

Lemma lt_known_bound g : g <> LNone -> lt_known F g LNone = true.
Proof.
  intros Hg; unfold lt_known; destruct g; [contradiction|reflexivity|reflexivity].
Qed.

Lemma cterm_push u (y : U) t : cterm u None (cpush LNone y t) = cterm u None y.
Proof. rewrite <- (proj2 HM u (cpush LNone y t)), cpop_push; reflexivity. Qed.

Definition named (s : cstep) : Prop := exists l, slabel s = Some l /\ l <> LNone.

Lemma named_sdist p : Forall named p -> Forall (sdist LNone) p.
Proof.
  intros H; eapply Forall_impl; [|exact H]; intros s [l [E N]]; exists l; split; [exact E|left; apply lt_known_bound, N].
Qed.

Lemma unbound_sound u w : forall pre x, Forall named pre ->
  cterm u None (wpre pre (wden (unbound w) x) x) = cterm u None (wpre pre (wden w x) x).
Proof.
  induction w as [|s w IH]; intros pre x Hp; [reflexivity|].
  assert (Drop : forall s', slabel s' = Some LNone ->
    cterm u None (wpre pre (wden (unbound w) x) x) = cterm u None (wpre pre (sden s' (wden w x) x) x)).
  { intros s' Es; rewrite IH by exact Hp.
    rewrite (wpre_comm s' LNone pre _ x Es) by (apply named_sdist, Hp).
    destruct s' as [g v|g|a]; cbn in Es |- *; try discriminate; injection Es as ->;
      [rewrite cterm_push|rewrite (proj2 HM)]; reflexivity. }
  assert (Keep : forall l, l <> LNone -> forall s', slabel s' = Some l ->
    cterm u None (wpre pre (wden (s' :: unbound w) x) x) = cterm u None (wpre pre (sden s' (wden w x) x) x)).
  { intros l Hl s' Es; cbn [wden].
    pose proof (IH (pre ++ [s']) x) as E; rewrite !wpre_app in E; cbn [wpre] in E; apply E.
    apply Forall_app; split; [exact Hp|constructor; [exists l; split; [exact Es|exact Hl]|constructor]]. }
  destruct s as [g v|g|a]; [destruct g as [|c|n]|destruct g as [|c|n]|reflexivity]; cbn [unbound].
  - apply (Drop (SE LNone v)); reflexivity.
  - apply (Keep (LCon c)); [discriminate|reflexivity].
  - apply (Keep (LAtom n)); [discriminate|reflexivity].
  - apply (Drop (SW LNone)); reflexivity.
  - apply (Keep (LCon c)); [discriminate|reflexivity].
  - apply (Keep (LAtom n)); [discriminate|reflexivity].
Qed.

Lemma clean_sound u b w x : cterm u b (wden (clean b w) x) = cterm u b (wden w x).
Proof.
  destruct b as [n|]; [reflexivity|]; cbn [clean].
  apply (unbound_sound u w [] x); constructor.
Qed.

(** ** The normaliser *)

Theorem norm_sound_all :
  (forall a K x, wden (norm F a K) x = ca a (wden K x))
  /\ (forall t K x, vden (tval F t K) x = ct t (wden K x))
  /\ (forall p K x, wden (pnorm F p K) x = cp p (wden K x)).
Proof.
  apply exp_mind; intros; cbn [norm tval pnorm ca ct cp].
  - reflexivity.
  - reflexivity.
  - rewrite H0, H; reflexivity.
  - rewrite H, pushW_sound; reflexivity.
  - rewrite pushE_sound, H0, H; reflexivity.
  - rewrite pushE_sound, H, pushW_sound, lookup_sound; reflexivity.
  - apply lookup_sound.
  - rewrite vden_term, clean_sound, H; reflexivity.
  - destruct (is_bind t); [apply H|rewrite H, pushW_sound; reflexivity].
  - rewrite lookup_sound, H; reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite H0, H; reflexivity.
  - rewrite H, pushW_sound; reflexivity.
Qed.

Lemma norm_meaning a (x : U) : wden (norm F a []) x = ca a x.
Proof. apply (proj1 norm_sound_all). Qed.

End Sem.

Arguments vden {M} v x.
Arguments wden {M} w x.

(** Same normal form, same meaning in every comprehension model. *)
Theorem cn_sound F a b : norm F a [] = norm F b [] -> cequal F a b.
Proof.
  intros E M HM x; rewrite <- (norm_meaning M F HM a x), <- (norm_meaning M F HM b x), E; reflexivity.
Qed.
