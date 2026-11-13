(** * Ingredients of completeness

    For theorems 3 and 4 of [docs/normal-forms.md], which are
    [complete_sh] and [eval_stuck] in [Core/Shared.v].

    From an interpretation satisfying the facts another is built that
    gives distinct label expressions distinct labels (the label order is
    dense, so each label variable can be moved into the gap just above
    its value).  Under it normal forms are well formed for the free
    model, so that two with the same meaning are equal in the free model
    (adequacy) and so equal (uniqueness). *)

From Stdlib Require Import Arith List Lia Bool Ascii String.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Unique Normal.
Import ListNotations.

(** ** Label interpretations giving distinct expressions distinct labels *)

Fixpoint set_nth (l : list label) (n : nat) (x : label) : list label :=
  match n, l with
  | 0, [] => [x]
  | 0, _ :: r => x :: r
  | S n, [] => EmptyString :: set_nth [] n x
  | S n, a :: r => a :: set_nth r n x
  end.

Lemma nth_set_nth l n x m : nth m (set_nth l n x) EmptyString = if Nat.eqb m n then x else nth m l EmptyString.
Proof.
  revert l m; induction n as [|n IH]; intros [|a r] [|m]; cbn [set_nth nth Nat.eqb]; try reflexivity;
    try (destruct m; reflexivity).
  - rewrite IH; destruct (Nat.eqb m n); [reflexivity|destruct m; reflexivity].
  - apply IH.
Qed.

(** Above any label, below every value above it in a finite list. *)
Lemma gap (vals : list (option label)) (sv : label) :
  exists w, olabel_lt (Some sv) (Some w) /\ forall u, In u vals -> olabel_lt (Some sv) u -> olabel_lt (Some w) u.
Proof.
  induction vals as [|u vals IH].
  - exists (String.append sv (String "255"%char EmptyString)); split; [apply label_lt_above|intros u []].
  - destruct IH as [w0 [H0 Hall]].
    destruct u as [su|]; [|exists w0; split; [exact H0|intros u [<-|Hu] Hl; [reflexivity|apply Hall; assumption]]].
    destruct (olabel_ltb (Some sv) (Some su)) eqn:E1;
      [|exists w0; split; [exact H0|intros u [<-|Hu] Hl; [unfold olabel_lt in Hl; congruence|apply Hall; assumption]]].
    destruct (olabel_ltb (Some w0) (Some su)) eqn:E2;
      [exists w0; split; [exact H0|intros u [<-|Hu] Hl; [exact E2|apply Hall; assumption]]|].
    destruct (label_lt_dense sv su E1) as [w [Hw1 Hw2]]; exists w; split; [exact Hw1|].
    assert (Hle : olabel_lt (Some w) (Some w0)).
    { destruct (olabel_trichotomy (Some w0) (Some su)) as [H|[H|H]]; [unfold olabel_lt in H; congruence| |].
      - injection H as ->; exact Hw2.
      - exact (olabel_lt_trans (Some w) (Some su) (Some w0) Hw2 H). }
    intros u [<-|Hu] Hl; [exact Hw2|exact (olabel_lt_trans _ _ _ Hle (Hall u Hu Hl))].
Qed.

Section Inj.

Variable F : list (lexp * lexp).
(** The label expressions in play, including those of the facts. *)
Variable S : list lexp.
Hypothesis HFS : forall x y, In (x, y) F -> In x S /\ In y S.

Definition fresh (lenv : list label) (h : lexp) : Prop :=
  forall h', In h' S -> lden lenv h' = lden lenv h -> h' = h.

Lemma lden_set lenv n w h :
  lden (set_nth lenv n w) h = match h with LAtom m => if Nat.eqb m n then Some w else lden lenv h | _ => lden lenv h end.
Proof. destruct h as [|s|m]; [reflexivity|reflexivity|cbn; rewrite nth_set_nth; destruct (Nat.eqb m n); reflexivity]. Qed.

Lemma move lenv n : lfacts_ok lenv F ->
  exists lenv', lfacts_ok lenv' F /\ fresh lenv' (LAtom n) /\ forall m, m <> n -> nth m lenv' EmptyString = nth m lenv EmptyString.
Proof.
  intros HF; set (sv := nth n lenv EmptyString).
  destruct (gap (map (lden lenv) S) sv) as [w [Hw Hall]].
  assert (Hv : forall h, In h S -> lden lenv h = Some w -> False).
  { intros h Hh E; pose proof (Hall _ (in_map _ _ _ Hh)) as H; rewrite E in H.
    exact (olabel_lt_irrefl _ (H Hw)). }
  exists (set_nth lenv n w); split; [|split].
  - unfold lfacts_ok in *; rewrite Forall_forall in *; intros [x y] Hxy; pose proof (HF _ Hxy) as Hl; cbn in Hl |- *.
    destruct (HFS x y Hxy) as [Hx Hy]; rewrite !lden_set.
    assert (Hn : forall h, (match h with LAtom m => if Nat.eqb m n then Some w else lden lenv h | _ => lden lenv h end)
                           = if lexp_eqb h (LAtom n) then Some w else lden lenv h).
    { intros [|s|m]; [reflexivity|reflexivity|cbn; reflexivity]. }
    rewrite !Hn.
    destruct (lexp_eqb x (LAtom n)) eqn:Ex; [apply lexp_eqb_eq in Ex; subst x|];
      (destruct (lexp_eqb y (LAtom n)) eqn:Ey; [apply lexp_eqb_eq in Ey; subst y|]).
    + exfalso; exact (olabel_lt_irrefl _ Hl).
    + apply Hall; [apply in_map, Hy|exact Hl].
    + exact (olabel_lt_trans _ _ _ Hl Hw).
    + exact Hl.
  - intros h' Hh' E; rewrite !lden_set, Nat.eqb_refl in E.
    destruct h' as [|s|m]; [discriminate|exfalso; exact (Hv _ Hh' E)|].
    destruct (Nat.eqb_spec m n) as [->|_]; [reflexivity|exfalso; exact (Hv _ Hh' E)].
  - intros m Hm; rewrite nth_set_nth; destruct (Nat.eqb_spec m n); [contradiction|reflexivity].
Qed.

Lemma lden_same l0 l1 n h : (forall m, m <> n -> nth m l1 EmptyString = nth m l0 EmptyString) -> h <> LAtom n ->
  lden l1 h = lden l0 h.
Proof. intros H Hh; destruct h as [|s|m]; [reflexivity|reflexivity|cbn; rewrite H; [reflexivity|congruence]]. Qed.

Lemma move_all lenv ns : lfacts_ok lenv F -> (forall n, In n ns -> In (LAtom n) S) ->
  exists lenv', lfacts_ok lenv' F /\ forall n, In n ns -> fresh lenv' (LAtom n).
Proof.
  revert lenv; induction ns as [|n ns IH]; intros lenv HF Hns; [exists lenv; split; [exact HF|intros n []]|].
  destruct (IH lenv HF (fun m Hm => Hns m (or_intror Hm))) as [l0 [HF0 Hf0]].
  destruct (move l0 n HF0) as [l1 [HF1 [Hf1 Hsame]]]; exists l1; split; [exact HF1|].
  intros m [<-|Hm]; [exact Hf1|].
  destruct (Nat.eq_dec m n) as [->|Hmn]; [exact Hf1|].
  assert (Em : lden l1 (LAtom m) = lden l0 (LAtom m)) by (apply (lden_same l0 l1 n); [exact Hsame|congruence]).
  intros h' Hh' E; rewrite Em in E.
  destruct (lexp_eqb h' (LAtom n)) eqn:Eh; [apply lexp_eqb_eq in Eh; subst h'|].
  - exfalso; apply Hmn.
    assert (LAtom m = LAtom n) as Emn by (apply Hf1; [apply Hns; right; exact Hm|rewrite Em; symmetry; exact E]).
    injection Emn as ->; reflexivity.
  - assert (Hne : h' <> LAtom n) by (intros ->; rewrite (proj2 (lexp_eqb_eq _ _) eq_refl) in Eh; discriminate).
    rewrite (lden_same l0 l1 n h' Hsame Hne) in E; exact (Hf0 m Hm h' Hh' E).
Qed.

Fixpoint atoms (hs : list lexp) : list nat :=
  match hs with [] => [] | LAtom n :: r => n :: atoms r | _ :: r => atoms r end.

Lemma atoms_in n hs : In n (atoms hs) -> In (LAtom n) hs.
Proof.
  induction hs as [|h hs IH]; [intros []|]; destruct h as [|s|m]; cbn [atoms];
    try (intros H; right; apply IH, H).
  intros [->|H]; [left; reflexivity|right; apply IH, H].
Qed.

Lemma atoms_of n hs : In (LAtom n) hs -> In n (atoms hs).
Proof.
  induction hs as [|h hs IH]; [intros []|]; intros [E|H]; [subst h; left; reflexivity|].
  destruct h as [|s|m]; cbn [atoms]; [apply IH, H|apply IH, H|right; apply IH, H].
Qed.

(** From any interpretation satisfying the facts, one that also gives
    distinct label expressions distinct labels. *)
Theorem distinct_interp lenv : lfacts_ok lenv F ->
  exists lenv', lfacts_ok lenv' F /\ forall h h', In h S -> In h' S -> lden lenv' h = lden lenv' h' -> h = h'.
Proof.
  intros HF; destruct (move_all lenv (atoms S) HF (fun n Hn => atoms_in n S Hn)) as [l [HFl Hf]].
  exists l; split; [exact HFl|]; intros h h' Hh Hh' E.
  destruct h as [|s|n]; [|destruct h' as [|s'|n']|].
  - destruct h' as [|s'|n']; [reflexivity|discriminate|discriminate].
  - discriminate.
  - injection E as ->; reflexivity.
  - apply (Hf n' (atoms_of _ _ Hh') (LCon s) Hh); exact E.
  - symmetry; apply (Hf n (atoms_of _ _ Hh) h' Hh'); symmetry; exact E.
Qed.

End Inj.

(** ** Term atoms of a word *)

Fixpoint tmax (t : ntgt) : nat :=
  match t with NVar _ _ => 0 | NBind u wp _ => Nat.max (S u) (wmax wp) end
with tlmax (ts : tlist) : nat :=
  match ts with TNil => 0 | TCons t r => Nat.max (tmax t) (tlmax r) end
with smax (s : seg) : nat :=
  match s with SNil => 0 | SEnt _ ts _ r => Nat.max (tlmax ts) (smax r) end
with wmax (w : word) : nat :=
  match w with WEnd s => smax s | WAtom s _ _ w | WLay s w => Nat.max (smax s) (wmax w) end.

Section Ok.

Variable lenv : list label.
Variable labs : list lexp.
Variable npa : nat.
Variable nt : nat.

Lemma oks_shape s : sshape lenv labs false s -> forall h ts m r, s = SEnt h ts m r -> sget lenv (lden lenv h) r = None.
Proof.
  intros [Hs _] h ts m r ->; cbn [sents] in Hs; inversion Hs as [|e l Hsr Hall]; subst.
  apply sget_above; rewrite Forall_forall in Hall; exact Hall.
Qed.

Lemma sshape_tail nm h ts m r : sshape lenv labs nm (SEnt h ts m r) -> sshape lenv labs nm r.
Proof. intros [Hs Ho]; cbn [sents] in Hs, Ho; inversion Hs; inversion Ho; split; assumption. Qed.

Lemma normal_ok :
  (forall t, tnf lenv labs npa t -> tmax t <= nt -> okt lenv (tenvT nt) t)
  /\ (forall ts, tlnf lenv labs npa ts -> tlmax ts <= nt -> okts lenv (tenvT nt) ts)
  /\ (forall s, sshape lenv labs false s -> snf lenv labs npa s -> smax s <= nt -> oks lenv (tenvT nt) s)
  /\ (forall w nm, wnf lenv labs npa nm w -> wmax w <= nt -> okw lenv (tenvT nt) w).
Proof.
  apply nf_mind; cbn [tmax tlmax smax wmax Unique.tnf Unique.tlnf Unique.snf okt okts oks Unique.okw].
  - intros; exact I.
  - intros u w IH b [_ Hw] Hm; split; [unfold tenvT; rewrite length_map, length_seq; lia|apply (IH _ Hw); lia].
  - intros; exact I.
  - intros t IHt r IHr [Ht Hr] Hm; split; [apply IHt; [exact Ht|lia]|apply IHr; [exact Hr|lia]].
  - intros; exact I.
  - intros h ts IHts m r IHr Hs [Hts Hr] Hm; split; [exact (oks_shape _ Hs _ _ _ _ eq_refl)|split].
    + apply IHts; [exact Hts|lia].
    + apply IHr; [exact (sshape_tail _ _ _ _ _ Hs)|exact Hr|lia].
  - intros s IH nm [Hs Hn] Hm; apply IH; [eapply sshape_weak, Hs|exact Hn|exact Hm].
  - intros s IHs L a w IHw nm [Hs [Hn [_ Hr]]] Hm; split; [apply IHs; [exact Hs|exact Hn|lia]|].
    apply (IHw nm); [apply rnf_wnf, Hr|lia].
  - intros s _ w _ nm [].
Qed.

End Ok.

(** ** Evaluating a variable

    Theorem 4 of [docs/normal-forms.md], for evaluations whose label
    comparisons are all known: [wtrace] reaches a target exactly when the
    result is the same under every interpretation.  When it reaches a
    target, the result is that target ([wtrace_sound]).  When it gets
    stuck at an atom, the result depends on the interpretation of the
    atoms, even with the labels fixed ([stuck_word], and [eval_stuck] in
    [Core/Shared.v]). *)

Section Eval.

Variable lenv : list label.
Variable F : order.
Hypothesis HF : facts_ok lenv F.

Lemma seg_tgt_free Sg h i t K :
  seg_tgt F Sg h i = Some t -> fs lenv Sg K (mk_rvar (lden lenv h) i) = ft lenv t K.
Proof.
  unfold seg_tgt.
  destruct (sfind F h Sg) as [r|] eqn:Ef; [|discriminate]; apply (sfind_sound lenv F HF) in Ef.
  rewrite fs_get; unfold fget; cbn [v_label v_index]; rewrite <- Ef.
  destruct r as [[ts m]|]; intros H; injection H as <-; [|reflexivity].
  destruct (Nat.ltb_spec i (tlen ts)) as [Hi|Hi].
  - apply ftl_lt, Hi.
  - rewrite ftl_ge by exact Hi; reflexivity.
Qed.

Lemma wtrace_free w : forall h i K,
  (forall t, wtrace F w h i = Some (Some t) -> fw lenv w K (mk_rvar (lden lenv h) i) = ft lenv t K)
  /\ (wtrace F w h i = Some None -> exists a z k, fw lenv w K (mk_rvar (lden lenv h) i) = FStuck a z k).
Proof.
  induction w as [Sg|Sg L a w IH|Sg w IH] using word_spine; intros h i K; cbn [wtrace fw]; [| |split; discriminate].
  - destruct (seg_tgt F Sg h i) as [t'|] eqn:E; [|split; discriminate].
    split; [intros t H; injection H as <-; apply seg_tgt_free, E|discriminate].
  - set (K' := latom lenv L a (fun y => fs lenv Sg K y)).
    destruct (IH h i K') as [IH1 IH2].
    destruct (wtrace F w h i) as [[[h1 j1|u wp b]|]|]; try (split; discriminate).
    + rewrite (IH1 _ eq_refl); cbn [ft]; unfold K', latom; cbn [v_label v_index].
      destruct (lcnt F h1 L) as [c|] eqn:EL; [|split; discriminate].
      rewrite (lcnt_sound lenv F HF h1 L c EL).
      destruct (Nat.ltb_spec j1 c) as [Hj|Hj].
      * destruct (seg_tgt F Sg h1 j1) as [t'|] eqn:Es; [|split; discriminate].
        split; [intros t H; injection H as <-; apply seg_tgt_free, Es|discriminate].
      * split; [discriminate|intros _; eexists _, _, _; reflexivity].
    + split; [discriminate|intros _; exact (IH2 eq_refl)].
Qed.

End Eval.

(** A normal form that means [e] and whose evaluation at a variable is
    stuck: no target is the result under every interpretation. *)
Theorem stuck_word lenv labs N F ntm e w h i :
  facts_ok lenv F -> wnf lenv labs N false w ->
  (forall (T : Type) (tenv : list T) aenv penv, ntm <= List.length tenv ->
     wden lenv tenv aenv penv w = aeden lenv tenv aenv penv e) ->
  wtrace F w h i = Some None ->
  ~ exists t, forall (T : Type) (tenv : list T) aenv penv, ntm <= List.length tenv ->
      rapply (aeden lenv tenv aenv penv e) (mk_rvar (lden lenv h) i) = rtarget_result (tden lenv tenv aenv penv t).
Proof.
  intros HF Hw E Hs [t Ht].
  destruct (proj2 (wtrace_free lenv F HF w h i FVar) Hs) as [a [z [k Ef]]].
  set (nt := Nat.max ntm (wmax w)).
  assert (Hok : okw lenv (tenvT nt) w) by (apply (proj2 (proj2 (proj2 (normal_ok lenv labs N nt))) w false Hw); lia).
  assert (Hnt : ntm <= List.length (tenvT nt)) by (unfold tenvT; rewrite length_map, length_seq; lia).
  set (Λ := [v_label z]); set (N' := S (v_index z)); set (na := S a).
  set (aenv := aenvT [] Λ N' na); set (penv := penvT [] 1).
  assert (HK : forall y, realises (tenvT nt) aenv penv (FVar y) (rapply ridentity y))
    by (intros y; cbn [realises]; apply rapply_identity).
  pose proof (proj2 (proj2 (proj2 (fw_real lenv (tenvT nt) aenv penv))) w Hok FVar ridentity (mk_rvar (lden lenv h) i) HK) as R.
  rewrite rcompose_identity_l, Ef in R.
  destruct (real_stuck [] Λ N' na 1 nt a z k _ ltac:(unfold na; lia) (or_introl eq_refl) ltac:(unfold N'; lia) R) as [Kr [_ Er]].
  pose proof (Ht tag (tenvT nt) aenv penv Hnt) as E2.
  rewrite <- (E tag (tenvT nt) aenv penv Hnt), Er in E2.
  destruct t as [h' j|u wp b]; cbn [tden rtarget_result] in E2; [discriminate|].
  destruct (nth_error (tenvT nt) u) as [x|] eqn:Ex; [|discriminate].
  apply tenvT_nth in Ex; subst x; apply inr_pair in E2; destruct E2 as [E2 _]; discriminate.
Qed.
