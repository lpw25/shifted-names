(** * The operations of the normaliser keep normal forms

    For theorem 1 of [docs/normal-forms.md]: each operation the
    normaliser is built from returns a word satisfying the normal-form
    conditions [wnf] of [Core/Unique.v] when its arguments do.  Nothing
    is checked at run time. *)

From Stdlib Require Import Arith List Lia Bool Sorted.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Unique.
Import ListNotations.

Section Normal.

Variable lenv : list label.
Variable labs : list lexp.
Variable npa : nat.
Variable F : order.
Hypothesis HF : facts_ok lenv F.
Variable ntm : nat.

Local Notation lden := (lden lenv).
Local Notation ekey := (ekey lenv).
Local Notation sshape := (sshape lenv labs).
Local Notation eshape := (eshape lenv labs).
Local Notation tnf := (tnf lenv labs npa).
Local Notation snf := (snf lenv labs npa).
Local Notation wnf := (wnf lenv labs npa).
Local Notation bok := (bok npa).
Local Notation rnf := (rnf lenv labs).
Local Notation sren := (sren labs).
Local Notation lok := (lok lenv labs).

Definition ssorted (es : list (lexp * list ntgt * nat)) : Prop :=
  StronglySorted (fun e e' => olabel_lt (ekey e) (ekey e')) es.

Definition known (h : lexp) (e : lexp * list ntgt * nat) : Prop :=
  exists c, lcmp F h (fst (fst e)) = Some c /\ c <> Eq.

(** ** Segments *)

Lemma sdel_shape h s s' : sdel F h s = Some s' ->
  (forall e, In e (sents s') -> In e (sents s) /\ known h e) /\ (ssorted (sents s) -> ssorted (sents s')).
Proof.
  revert s'; induction s as [|h' ts m r IH] using seg_spine; intros s'; cbn [sdel].
  - intros H; injection H as <-; split; [intros e []|intros _; constructor].
  - destruct (lcmp F h h') as [c|] eqn:Ec; [|discriminate].
    destruct c.
    + intros H; destruct (IH _ H) as [H1 H2]; split.
      * intros e He; destruct (H1 e He) as [Hi Hk]; split; [right; exact Hi|exact Hk].
      * intros Hs; inversion Hs; apply H2; assumption.
    + destruct (sdel F h r) as [r'|] eqn:Er; [|discriminate]; intros H; injection H as <-.
      destruct (IH _ eq_refl) as [H1 H2]; split.
      * intros e [<-|He]; [split; [left; reflexivity|exists Lt; split; [exact Ec|discriminate]]|].
        destruct (H1 e He) as [Hi Hk]; split; [right; exact Hi|exact Hk].
      * intros Hs; inversion Hs as [|e l Hsr Hall]; subst; constructor; [apply H2, Hsr|].
        rewrite Forall_forall in *; intros e He; apply Hall, H1, He.
    + destruct (sdel F h r) as [r'|] eqn:Er; [|discriminate]; intros H; injection H as <-.
      destruct (IH _ eq_refl) as [H1 H2]; split.
      * intros e [<-|He]; [split; [left; reflexivity|exists Gt; split; [exact Ec|discriminate]]|].
        destruct (H1 e He) as [Hi Hk]; split; [right; exact Hi|exact Hk].
      * intros Hs; inversion Hs as [|e l Hsr Hall]; subst; constructor; [apply H2, Hsr|].
        rewrite Forall_forall in *; intros e He; apply Hall, H1, He.
Qed.

Lemma sput_shape h ts m s : (forall e, In e (sents s) -> known h e) ->
  (forall e, In e (sents (sput F h ts m s)) <-> e = (h, tl_list ts, m) \/ In e (sents s))
  /\ (ssorted (sents s) -> ssorted (sents (sput F h ts m s))).
Proof.
  induction s as [|h' ts' m' r IH] using seg_spine; intros Hk; cbn [sput].
  - split; [intros e; cbn; split; [intros [E|[]]; left; symmetry; exact E|intros [E|[]]; left; symmetry; exact E]|].
    intros _; repeat constructor.
  - destruct (Hk _ (or_introl eq_refl)) as [c [Ec Hc]]; cbn [fst] in Ec; rewrite Ec.
    pose proof (lcmp_sound lenv F HF _ _ _ Ec) as Hcs.
    destruct c; [contradiction| |].
    + split; [intros e; cbn [sents]; split; [intros [E|E]; [left; symmetry; exact E|right; exact E]|intros [E|E]; [left; symmetry; exact E|right; exact E]]|].
      intros Hs; constructor; [exact Hs|]; cbn [sents]; constructor; [exact Hcs|].
      inversion Hs as [|e l Hsr Hall]; subst; rewrite Forall_forall in *.
      intros e He; exact (olabel_lt_trans _ _ _ Hcs (Hall e He)).
    + assert (Hk' : forall e, In e (sents r) -> known h e) by (intros e He; apply Hk; right; exact He).
      destruct (IH Hk') as [H1 H2]; split.
      * intros e; cbn [sents]; cbn [In]; rewrite (H1 e); split.
        -- intros [E|[E|E]]; [right; left; exact E|left; exact E|right; right; exact E].
        -- intros [E|[E|E]]; [right; left; exact E|left; exact E|right; right; exact E].
      * intros Hs; cbn [sents] in *; inversion Hs as [|e l Hsr Hall]; subst; constructor; [apply H2, Hsr|].
        rewrite Forall_forall in *; intros e He; apply H1 in He as [->|He]; [exact Hcs|apply Hall, He].
Qed.

Lemma trim_spec h rts m : forall rts' m', trim h rts m = (rts', m') ->
  trimmed h (rev rts') m' /\ (forall t, In t rts' -> In t rts).
Proof.
  revert m; induction rts as [|x r IH]; intros m rts' m' E; cbn [trim] in E.
  - injection E as <- <-; split; [exact I|intros t []].
  - assert (Hkeep : trim h (x :: r) m = (x :: r, m) -> rts' = x :: r -> m' = m ->
                    (forall h' j m0, x = NVar h' j -> m = S m0 -> lexp_eqb h' h && Nat.eqb j m0 = false) ->
                    trimmed h (rev rts') m' /\ (forall t, In t rts' -> In t (x :: r))).
    { intros _ -> -> Hx; split; [|intros t Ht; exact Ht].
      unfold trimmed; cbn [rev]; rewrite last_last.
      destruct (rev r ++ [x]) eqn:Ex; [destruct (rev r); discriminate|].
      destruct x as [h' j|u w b]; [|exact I]; destruct m as [|m0]; [exact I|].
      intros [-> ->]; specialize (Hx _ _ _ eq_refl eq_refl); rewrite (proj2 (lexp_eqb_eq h h) eq_refl), Nat.eqb_refl in Hx; discriminate. }
    destruct x as [h' j|u w b].
    + destruct m as [|m0].
      * injection E as <- <-; apply Hkeep; [reflexivity|reflexivity|reflexivity|intros ? ? ? _ E; discriminate].
      * destruct (lexp_eqb h' h && Nat.eqb j m0) eqn:Eb.
        -- destruct (IH _ _ _ E) as [H1 H2]; split; [exact H1|intros t Ht; right; apply H2, Ht].
        -- injection E as <- <-; apply Hkeep; [cbn; rewrite Eb; reflexivity|reflexivity|reflexivity|].
           intros h0 j0 m1 E1 E2; injection E1 as <- <-; injection E2 as <-; exact Eb.
    + injection E as <- <-; apply Hkeep; [reflexivity|reflexivity|reflexivity|intros ? ? ? E; discriminate].
Qed.
Lemma sents_tgts s t : In t (stgts s) <-> exists h xs m, In (h, xs, m) (sents s) /\ In t xs.
Proof.
  unfold stgts; rewrite in_flat_map; split.
  - intros [[[h xs] m] [He Ht]]; exists h, xs, m; split; assumption.
  - intros [h [xs [m [He Ht]]]]; exists (h, xs, m); split; assumption.
Qed.

Lemma sset_shape nm h ts m s s' : sset F h ts m s = Some s' -> sshape nm s ->
  (In h labs \/ (tl_list ts = [] /\ m = 0)) -> (nm = true -> lden h <> None) ->
  sshape nm s'
  /\ (forall e, In e (sents s') -> In e (sents s) \/ fst (fst e) = h)
  /\ (forall t, In t (stgts s') -> In t (stgts s) \/ In t (tl_list ts))
  /\ (tl_list ts = [] -> m = 0 -> forall e, In e (sents s') -> In e (sents s)).
Proof.
  rewrite sset_unfold; intros E [Hs Ho] Hh Hnm.
  destruct (sdel F h s) as [s0|] eqn:Ed; [|discriminate].
  destruct (sdel_shape _ _ _ Ed) as [Hs0 Hsort0].
  destruct (trim h (rev (tl_list ts)) m) as [rts m'] eqn:Et.
  destruct (trim_spec _ _ _ _ _ Et) as [Htr Hin].
  assert (Hold : forall e, In e (sents s0) -> eshape nm e)
    by (intros e He; rewrite Forall_forall in Ho; apply Ho, (proj1 (Hs0 e He))).
  assert (Ht0 : forall t, In t (stgts s0) -> In t (stgts s)).
  { intros t; rewrite !sents_tgts; intros [h0 [xs [m0 [He Ht]]]]; exists h0, xs, m0.
    split; [apply (proj1 (Hs0 _ He))|exact Ht]. }
  assert (Hcase : s' = s0 \/ (s' = sput F h (tl_of (rev rts)) m' s0 /\ (rts <> [] \/ m' <> 0))).
  { destruct rts as [|x rts]; [destruct m' as [|m']|]; injection E as <-; [left; reflexivity|right|right].
    - split; [reflexivity|right; discriminate].
    - split; [reflexivity|left; discriminate]. }
  destruct Hcase as [->|[-> Hne]].
  - split; [split; [apply Hsort0, Hs|apply Forall_forall, Hold]|].
    split; [intros e He; left; apply (proj1 (Hs0 e He))|].
    split; [intros t Ht; left; apply Ht0, Ht|].
    intros _ _ e He; apply (proj1 (Hs0 e He)).
  - destruct (sput_shape h (tl_of (rev rts)) m' s0 (fun e He => proj2 (Hs0 e He))) as [Hput Hsort].
    split; [split; [apply Hsort, Hsort0, Hs|]|].
    + apply Forall_forall; intros e He; apply Hput in He as [->|He]; [|apply Hold, He].
      cbn [Unique.eshape]; rewrite tl_list_of; refine (conj _ (conj Htr (conj _ Hnm))).
      { destruct Hh as [Hh|[Hts Hm]]; [exact Hh|exfalso]; rewrite Hts, Hm in Et; cbn in Et; injection Et as <- <-.
        destruct Hne as [Hne|Hne]; apply Hne; reflexivity. }
      destruct Hne as [Hne|Hne]; [left; intros E'; apply Hne; rewrite <- (rev_involutive rts), E'; reflexivity|right; exact Hne].
    + split; [intros e He; apply Hput in He as [->|He]; [right; reflexivity|left; apply (proj1 (Hs0 e He))]|].
      split.
      * intros t Ht; apply sents_tgts in Ht as [h0 [xs [m0 [He Ht]]]]; apply Hput in He as [E'|He].
        -- injection E' as -> -> ->; right; rewrite tl_list_of, <- in_rev in Ht.
           apply Hin in Ht; rewrite <- in_rev in Ht; exact Ht.
        -- left; apply Ht0, sents_tgts; exists h0, xs, m0; split; assumption.
      * intros Hts Hm; exfalso; rewrite Hts, Hm in Et; cbn in Et; injection Et as <- <-.
        destruct Hne as [Hne|Hne]; apply Hne; reflexivity.
Qed.

Lemma sbuild_shape es s : sbuild F es = Some s ->
  (forall h xs m, In (h, (xs, m)) es -> In h labs) ->
  sshape false s
  /\ (forall t, In t (stgts s) -> exists h xs m, In (h, (xs, m)) es /\ In t xs)
  /\ (forall g, (forall h xs m, In (h, (xs, m)) es -> h = g -> xs = [] /\ m = 0) ->
      forall e, In e (sents s) -> fst (fst e) <> g).
Proof.
  revert s; induction es as [|[h [xs m]] es IH]; intros s; cbn [sbuild].
  - intros H _; injection H as <-; split; [split; constructor|split; [intros t []|intros g _ e []]].
  - destruct (sbuild F es) as [s0|] eqn:E0; [|discriminate]; intros E Hl.
    destruct (IH s0 eq_refl (fun h0 xs0 m0 Hi => Hl h0 xs0 m0 (or_intror Hi))) as [Hs0 [Ht0 Hg0]].
    destruct (sset_shape false h (tl_of xs) m s0 s E Hs0 (or_introl (Hl h xs m (or_introl eq_refl))) ltac:(discriminate))
      as [Hs [He [Ht Hid]]].
    split; [exact Hs|split].
    + intros t Hin; destruct (Ht t Hin) as [Hin'|Hin'].
      * destruct (Ht0 t Hin') as [h0 [xs0 [m0 [Hi Hi']]]]; exists h0, xs0, m0; split; [right; exact Hi|exact Hi'].
      * rewrite tl_list_of in Hin'; exists h, xs, m; split; [left; reflexivity|exact Hin'].
    + intros g Hg e Hin.
      assert (Hg0' : forall h0 xs0 m0, In (h0, (xs0, m0)) es -> h0 = g -> xs0 = [] /\ m0 = 0)
        by (intros ? ? ? Hi; apply Hg; right; exact Hi).
      destruct (lexp_eqb h g) eqn:Ehg.
      * apply lexp_eqb_eq in Ehg; subst g; destruct (Hg h xs m (or_introl eq_refl) eq_refl) as [-> ->].
        apply (Hg0 h Hg0'), (Hid eq_refl eq_refl), Hin.
      * destruct (He e Hin) as [Hin'|Ee]; [apply (Hg0 g Hg0'), Hin'|].
        rewrite Ee; intros E'; subst g; rewrite (proj2 (lexp_eqb_eq h h) eq_refl) in Ehg; discriminate.
Qed.

Lemma lden_none h : lden h = None -> h = LNone.
Proof. destruct h; cbn; congruence. Qed.

Lemma sdrop_none_sents s e : In e (sents (sdrop_none s)) -> In e (sents s) /\ fst (fst e) <> LNone.
Proof.
  induction s as [|h ts m r IH] using seg_spine; [intros []|]; destruct h as [|x|n]; cbn [sdrop_none sents].
  - intros He; destruct (IH He) as [H1 H2]; split; [right; exact H1|exact H2].
  - intros [<-|He]; [split; [left; reflexivity|discriminate]|destruct (IH He) as [H1 H2]; split; [right; exact H1|exact H2]].
  - intros [<-|He]; [split; [left; reflexivity|discriminate]|destruct (IH He) as [H1 H2]; split; [right; exact H1|exact H2]].
Qed.

Lemma sdrop_none_shape s : sshape false s ->
  sshape true (sdrop_none s) /\ (forall t, In t (stgts (sdrop_none s)) -> In t (stgts s)).
Proof.
  intros [Hs Ho]; split; [split|].
  - induction s as [|h ts m r IH] using seg_spine; [constructor|]; cbn [sents] in Hs, Ho.
    inversion Hs as [|e l Hsr Hall]; inversion Ho as [|e' l' He Hor]; subst.
    destruct h as [|x|n]; cbn [sdrop_none sents]; [apply IH; assumption| |];
      (constructor; [apply IH; assumption|]); rewrite Forall_forall in *; intros e Hi; apply Hall, (sdrop_none_sents _ _ Hi).
  - apply Forall_forall; intros [[h xs] m] Hi; destruct (sdrop_none_sents _ _ Hi) as [Hi' Hn].
    rewrite Forall_forall in Ho; destruct (Ho _ Hi') as [A [B [C _]]]; refine (conj A (conj B (conj C _))).
    intros _ E; apply Hn, lden_none, E.
  - intros t; rewrite !sents_tgts; intros [h [xs [m [Hi Ht]]]]; exists h, xs, m; split; [apply (sdrop_none_sents _ _ Hi)|exact Ht].
Qed.

Lemma sshape_labs nm s : sshape nm s -> forall h xs m, In (h, xs, m) (sents s) -> In h labs.
Proof. intros [_ Ho] h xs m Hi; rewrite Forall_forall in Ho; exact (proj1 (Ho _ Hi)). Qed.

Lemma snf_iff s : snf s <-> (forall t, In t (stgts s) -> tnf t).
Proof.
  split; [apply snf_in|]; induction s as [|h ts m r IH] using seg_spine; cbn [Unique.snf]; [intros _; exact I|].
  intros H; split; [|apply IH; intros t Ht; apply H; rewrite stgts_cons; apply in_or_app; right; exact Ht].
  assert (H' : forall t, In t (tl_list ts) -> tnf t) by (intros t Ht; apply H; rewrite stgts_cons; apply in_or_app; left; exact Ht).
  clear H IH; induction ts as [|t r' IH] using tlist_spine; cbn [Unique.tlnf]; [exact I|].
  split; [apply H'; left; reflexivity|apply IH; intros t' Ht'; apply H'; right; exact Ht'].
Qed.

(** ** Composition *)

Lemma tapp_var_in S h i t : tapp F ntm S (NVar h i) = Some t -> (exists j, t = NVar h j) \/ In t (stgts S).
Proof.
  rewrite tapp_var; destruct (sfind F h S) as [[[ts m]|]|] eqn:Ef;
    [|intros H; injection H as <-; left; eexists; reflexivity|discriminate].
  apply (sfind_sound lenv F HF) in Ef.
  destruct (i <? tlen ts) eqn:Ei; intros H; injection H as <-; [right|left; eexists; reflexivity].
  apply (sget_tgts _ (lden h) S ts m (eq_sym Ef)), tnth_in, Nat.ltb_lt, Ei.
Qed.

Lemma tlapp_in S ts ts' : tlapp F ntm S ts = Some ts' ->
  forall t, In t (tl_list ts') -> exists t0, In t0 (tl_list ts) /\ tapp F ntm S t0 = Some t.
Proof.
  revert ts'; induction ts as [|t0 r IH] using tlist_spine; intros ts'; [cbn [tlapp]|rewrite tlapp_cons].
  - intros H; injection H as <-; intros t [].
  - destruct (tapp F ntm S t0) as [t1|] eqn:E1; [|discriminate].
    destruct (tlapp F ntm S r) as [r'|] eqn:E2; [|discriminate]; intros H; injection H as <-.
    intros t [<-|Ht]; [exists t0; split; [left; reflexivity|exact E1]|].
    destruct (IH _ eq_refl t Ht) as [t2 [Hi E]]; exists t2; split; [right; exact Hi|exact E].
Qed.

Lemma sgo_spec S U R : sgo F ntm S U = Some R -> sshape false S ->
  (forall h xs m, In (h, xs, m) (sents U) -> In h labs) ->
  sshape false R
  /\ (forall t, In t (stgts R) -> In t (stgts S) \/ exists t0, In t0 (stgts U) /\ tapp F ntm S t0 = Some t).
Proof.
  revert R; induction U as [|h ts m r IH] using seg_spine; intros R; [cbn [sgo]|rewrite sgo_ent].
  - intros H HS _; injection H as <-; split; [exact HS|intros t Ht; left; exact Ht].
  - destruct (sgo F ntm S r) as [R0|] eqn:E0; [|discriminate].
    destruct (tlapp F ntm S ts) as [ts'|] eqn:E1; [|discriminate].
    destruct (sfind F h S) as [e|] eqn:E2; [|discriminate].
    destruct (ofe e) as [tsS mS] eqn:Eo; intros E HS Hl.
    destruct (IH R0 eq_refl HS (fun h0 xs0 m0 Hi => Hl h0 xs0 m0 (or_intror Hi))) as [Hs0 Ht0].
    destruct (sset_shape false _ _ _ _ _ E Hs0 (or_introl (Hl h _ m (or_introl eq_refl))) ltac:(discriminate)) as [Hs [_ [Ht _]]].
    split; [exact Hs|]; intros t Hin; destruct (Ht t Hin) as [Hin'|Hin'].
    + destruct (Ht0 t Hin') as [H'|[t0 [Hi Et]]]; [left; exact H'|].
      right; exists t0; split; [rewrite stgts_cons; apply in_or_app; right; exact Hi|exact Et].
    + rewrite tcat_list in Hin'; apply in_app_or in Hin' as [Hin'|Hin'].
      * destruct (tlapp_in _ _ _ E1 t Hin') as [t0 [Hi Et]]; right; exists t0.
        split; [rewrite stgts_cons; apply in_or_app; left; exact Hi|exact Et].
      * left; apply tskip_list_in in Hin'.
        apply (sfind_sound lenv F HF) in E2; destruct e as [[ts0 m0]|]; cbn [ofe] in Eo; injection Eo as <- <-;
          [|destruct Hin'].
        apply (sget_tgts _ (lden h) S _ _ (eq_sym E2) _ Hin').
Qed.

Lemma sdrop_none_id s : sshape true s -> sdrop_none s = s.
Proof.
  induction s as [|h ts m r IH] using seg_spine; [reflexivity|]; intros [Hs Ho]; cbn [sents] in Hs, Ho.
  inversion Hs as [|e0 l0 Hsr Hall]; inversion Ho as [|e l He Hor]; subst; cbn [Unique.eshape] in He.
  destruct h as [|x|n]; [exfalso; apply (proj2 (proj2 (proj2 He)) eq_refl); reflexivity| |];
    cbn [sdrop_none]; f_equal; apply IH; split; assumption.
Qed.

Lemma pnorm_rnf w : rnf true w -> pnorm w = w.
Proof.
  induction w as [U|s L a w IH|s w IH] using word_spine; cbn [Unique.rnf pnorm]; [| |intros []].
  - intros [H _]; f_equal; apply sdrop_none_id, H.
  - intros [_ [_ [_ H]]]; f_equal; apply IH, H.
Qed.

Section CompNormal.

Variable S : seg.
Hypothesis HS : sshape false S.
Hypothesis HSn : snf S.

Lemma comp_normal :
  (forall t, tnf t -> forall t', tapp F ntm S t = Some t' -> tnf t')
  /\ (forall ts, forall t, In t (tl_list ts) -> tnf t -> forall t', tapp F ntm S t = Some t' -> tnf t')
  /\ (forall s, forall t, In t (stgts s) -> tnf t -> forall t', tapp F ntm S t = Some t' -> tnf t')
  /\ (forall w nm, wnf nm w -> forall w', wapp F ntm S w = Some w' -> wnf nm (if nm then pnorm w' else w')).
Proof.
  apply nf_mind.
  - intros h i Hh t' E; destruct (tapp_var_in _ _ _ _ E) as [[j ->]|Hin]; [exact Hh|apply (snf_in _ _ _ _ HSn _ Hin)].
  - intros u w IH b Hw t'; rewrite tapp_bind; destruct (u <? ntm); [|discriminate].
    destruct (wapp F ntm S w) as [w'|] eqn:E; [|discriminate]; intros H; injection H as <-.
    destruct Hw as [Hb Hw]; split; [exact Hb|].
    specialize (IH (match b with None => true | Some _ => false end) Hw w' eq_refl); destruct b; exact IH.
  - intros t [].
  - intros t IHt r IHr t0 [<-|Hin]; [exact IHt|apply IHr, Hin].
  - intros t [].
  - intros h ts IHts m r IHr t Hin; rewrite stgts_cons in Hin; apply in_app_or in Hin as [Hin|Hin];
      [apply IHts, Hin|apply IHr, Hin].
  - intros U IH nm [Hs Hn] w'; rewrite wapp_end.
    destruct (sgo F ntm S U) as [U'|] eqn:E; [|discriminate]; intros H; injection H as <-.
    destruct (sgo_spec _ _ _ E HS (sshape_labs _ _ Hs)) as [Hs' Ht'].
    assert (Hn' : snf U').
    { apply snf_iff; intros t Ht; destruct (Ht' t Ht) as [Hin|[t0 [Hi Et]]];
        [apply (snf_in _ _ _ _ HSn _ Hin)|apply (IH t0 Hi (snf_in _ _ _ _ Hn _ Hi) t Et)]. }
    destruct nm; cbn [pnorm Unique.wnf].
    + destruct (sdrop_none_shape _ Hs') as [Hs'' Ht'']; split; [exact Hs''|].
      apply snf_iff; intros t Ht; apply (snf_in _ _ _ _ Hn'), Ht'', Ht.
    + split; assumption.
  - intros U IHs L a w IHw nm [Hs [Hn [Ha Hr]]] w'; rewrite wapp_atom.
    destruct (sgo F ntm S U) as [U'|] eqn:E; [|discriminate]; intros H; injection H as <-.
    destruct (sgo_spec _ _ _ E HS (sshape_labs _ _ Hs)) as [Hs' Ht'].
    assert (Hn' : snf U').
    { apply snf_iff; intros t Ht; destruct (Ht' t Ht) as [Hin|[t0 [Hi Et]]];
        [apply (snf_in _ _ _ _ HSn _ Hin)|apply (IHs t0 Hi (snf_in _ _ _ _ Hn _ Hi) t Et)]. }
    destruct nm; cbn [pnorm Unique.wnf]; [rewrite (pnorm_rnf w Hr)|]; (split; [exact Hs'|split; [exact Hn'|split; [exact Ha|exact Hr]]]).
  - intros U _ w _ nm [].
Qed.

End CompNormal.

Lemma scomp_normal A Q R : scomp F ntm A Q = Some R -> sshape false A -> snf A -> sshape false Q -> snf Q ->
  sshape false R /\ snf R.
Proof.
  unfold scomp; intros E HA HAn HQ HQn.
  destruct (sgo_spec _ _ _ E HA (sshape_labs _ _ HQ)) as [Hs Ht]; split; [exact Hs|].
  apply snf_iff; intros t Hin; destruct (Ht t Hin) as [H|[t0 [Hi Et]]]; [apply (snf_in _ _ _ _ HAn _ H)|].
  apply (proj1 (proj2 (proj2 (comp_normal A HA HAn))) Q t0 Hi (snf_in _ _ _ _ HQn _ Hi) t Et).
Qed.

Lemma scomp_ren A Q R : scomp F ntm A Q = Some R -> sshape false A -> sren A -> sshape false Q -> sren Q ->
  sshape false R /\ sren R.
Proof.
  unfold scomp; intros E HA HAr HQ HQr.
  destruct (sgo_spec _ _ _ E HA (sshape_labs _ _ HQ)) as [Hs Ht]; split; [exact Hs|].
  unfold Unique.sren in *; rewrite Forall_forall in HAr, HQr |- *; intros t Hin.
  destruct (Ht t Hin) as [H|[t0 [Hi Et]]]; [apply HAr, H|]; pose proof (HQr _ Hi) as H0.
  destruct t0 as [h i|]; [|contradiction].
  destruct (tapp_var_in _ _ _ _ Et) as [[j ->]|H]; [exact H0|apply HAr, H].
Qed.

Lemma wcons_normal S w w' : wcons F ntm S w = Some w' -> sshape false S -> snf S -> wnf false w -> wnf false w'.
Proof.
  unfold wcons; intros E HS HSn Hw.
  exact (proj2 (proj2 (proj2 (comp_normal S HS HSn))) w false Hw w' E).
Qed.

(** ** Lifts *)

Lemma ladd_spec h n L L' : ladd F h n L = Some L' ->
  (forall l, lc lenv l L' = (if label_eqb (lden h) l then n else 0) + lc lenv l L)
  /\ (forall p, In p L' -> fst p = h \/ exists p0, In p0 L /\ fst p0 = fst p)
  /\ (lok L -> In h labs -> n <> 0 -> lok L').
Proof.
  revert L'; induction L as [|[h' n'] L0 IH]; intros L'; cbn [ladd].
  - intros H; injection H as <-; split; [intros l; cbn [lc]; lia|split].
    + intros p [<-|[]]; left; reflexivity.
    + intros _ Hh Hn; split; [repeat constructor|constructor; [split; assumption|constructor]].
  - destruct (lcmp F h h') as [c|] eqn:Ec; [|discriminate].
    pose proof (lcmp_sound lenv F HF _ _ _ Ec) as Hc; destruct c; cbn [cmp_holds] in Hc.
    + subst h'; intros H; injection H as <-; split; [intros l; rewrite !lc_cons; destruct (label_eqb _ _); lia|split].
      * intros p [<-|Hp]; [left; reflexivity|right; exists p; split; [right; exact Hp|reflexivity]].
      * intros [Hs Ho] _ _; inversion Hs as [|x l Hsr Hall]; inversion Ho as [|y l' [Hh Hn'] Hor]; subst.
        split; [constructor; [exact Hsr|exact Hall]|constructor; [split; [exact Hh|cbn in *; lia]|exact Hor]].
    + intros H; injection H as <-; split; [intros l; rewrite !lc_cons; lia|split].
      * intros p [<-|Hp]; [left; reflexivity|right; exists p; split; [exact Hp|reflexivity]].
      * intros [Hs Ho] Hh Hn; split; [constructor; [exact Hs|]|constructor; [split; assumption|exact Ho]].
        constructor; [exact Hc|]; inversion Hs as [|x l Hsr Hall]; subst; rewrite Forall_forall in *.
        intros p Hp; exact (olabel_lt_trans _ _ _ Hc (Hall p Hp)).
    + destruct (ladd F h n L0) as [L''|] eqn:E; [|discriminate]; intros H; injection H as <-.
      destruct (IH _ eq_refl) as [H1 [H2 H3]]; split; [intros l; rewrite !lc_cons, H1; lia|split].
      * intros p [<-|Hp]; [right; exists (h', n'); split; [left; reflexivity|reflexivity]|].
        destruct (H2 p Hp) as [E'|[p0 [Hi E']]]; [left; exact E'|right; exists p0; split; [right; exact Hi|exact E']].
      * intros HL Hh Hn; destruct (H3 (lok_tail _ _ _ _ HL) Hh Hn) as [Hs' Ho']; destruct HL as [Hs Ho].
        inversion Hs as [|x l Hsr Hall]; inversion Ho as [|y l' Hy Hor]; subst; rewrite Forall_forall in Hall.
        split; [constructor; [exact Hs'|]|constructor; [exact Hy|exact Ho']].
        apply Forall_forall; intros p Hp; destruct (H2 p Hp) as [E'|[p0 [Hi E']]]; cbn [fst].
        -- rewrite E'; exact Hc.
        -- rewrite <- E'; exact (Hall p0 Hi).
Qed.

Lemma lbuild_spec es L : lbuild F es = Some L ->
  (forall l, lc lenv l L = lc lenv l es) /\ ((forall p, In p es -> In (fst p) labs) -> lok L).
Proof.
  revert L; induction es as [|[h n] es IH]; intros L; cbn [lbuild].
  - intros H; injection H as <-; split; [reflexivity|intros _; split; constructor].
  - destruct (lbuild F es) as [L0|] eqn:E0; [|discriminate]; destruct (IH _ eq_refl) as [H1 H2].
    destruct (Nat.eqb_spec n 0) as [->|Hn].
    + intros H; injection H as <-; split; [intros l; rewrite lc_cons, H1; destruct (label_eqb _ _); lia|].
      intros Hl; apply H2; intros p Hp; apply Hl; right; exact Hp.
    + intros H; destruct (ladd_spec _ _ _ _ H) as [A [_ C]]; split; [intros l; rewrite A, lc_cons, H1; reflexivity|].
      intros Hl; apply C; [apply H2; intros p Hp; apply Hl; right; exact Hp|apply (Hl (h, n)); left; reflexivity|exact Hn].
Qed.

(** ** Counting *)

Fixpoint cnt (p : nat -> bool) (n : nat) : nat :=
  match n with 0 => 0 | S n => cnt p n + (if p n then 1 else 0) end.

Lemma cnt_ext p q n : (forall i, i < n -> p i = q i) -> cnt p n = cnt q n.
Proof. induction n as [|n IH]; intros H; [reflexivity|]; cbn [cnt]; rewrite IH, (H n) by (try (intros i Hi; apply H); lia); reflexivity. Qed.

Lemma cnt_stable p n m : (forall i, n <= i -> p i = false) -> n <= m -> cnt p m = cnt p n.
Proof.
  intros H Hm; induction m as [|m IH]; [assert (n = 0) as -> by lia; reflexivity|].
  destruct (Nat.eq_dec n (S m)) as [->|Hne]; [reflexivity|].
  cbn [cnt]; rewrite (H m) by lia; rewrite IH by lia; lia.
Qed.

Lemma cnt_ivt p n j : j < cnt p n -> exists i, i < n /\ p i = true /\ cnt p i = j.
Proof.
  induction n as [|n IH]; cbn [cnt]; [lia|]; intros Hj.
  destruct (Nat.lt_ge_cases j (cnt p n)) as [Hlt|Hge].
  - destruct (IH Hlt) as [i [Hi H]]; exists i; split; [lia|exact H].
  - destruct (p n) eqn:Ep; [|lia]; exists n; split; [lia|split; [exact Ep|lia]].
Qed.

Lemma filter_lt_cnt p R i : List.length (filter (fun q => q <? i) (filter p (seq 0 R))) = cnt p (Nat.min i R).
Proof.
  induction R as [|R IH]; [rewrite Nat.min_0_r; reflexivity|].
  rewrite seq_S, !filter_app, length_app, IH; cbn [Nat.add].
  destruct (Nat.le_gt_cases i R) as [Hi|Hi].
  - rewrite (Nat.min_l i R Hi), (Nat.min_l i (S R)) by lia.
    cbn [filter]; destruct (p R); cbn [filter]; cbv beta; [destruct (Nat.ltb_spec R i)|]; cbn [List.length]; lia.
  - rewrite (Nat.min_r i R), (Nat.min_r i (S R)) by lia; cbn [cnt].
    cbn [filter]; destruct (p R); cbn [filter]; cbv beta; [destruct (Nat.ltb_spec R i)|]; cbn [List.length]; lia.
Qed.

Lemma filter_cnt p R : List.length (filter p (seq 0 R)) = cnt p R.
Proof.
  induction R as [|R IH]; [reflexivity|].
  rewrite seq_S, filter_app, length_app, IH; cbn [Nat.add cnt filter]; destruct (p R); cbn [List.length]; lia.
Qed.

Lemma cntV_cnt U L g i : cntV lenv U L g i = cnt (fun i' => inVb lenv L (sv lenv U (mk_rvar g i'))) i.
Proof. induction i as [|i IH]; [reflexivity|]; cbn [cntV cnt]; rewrite IH; reflexivity. Qed.

(** ** Renamings in the real model *)

Local Notation tenvU := (@nil unit).
Local Notation aenvU := (@nil (radj unit)).
Local Notation penvU := (@nil (rpadj unit)).

Lemma esem_sv {T} (tenv : list T) aenv penv s l j :
  sren s -> esem lenv tenv aenv penv l (sget lenv l s) j = inl (sv lenv s (mk_rvar l j)).
Proof.
  intros Hr; unfold sv; cbn [v_label v_index]; destruct (sget lenv l s) as [[ts m]|] eqn:E; cbn [esem]; [|reflexivity].
  destruct (j <? tlen ts) eqn:Ej; [|reflexivity].
  pose proof (proj1 (Forall_forall _ _) Hr _ (sget_tgts _ _ _ _ _ E _ (tnth_in _ _ (proj1 (Nat.ltb_lt _ _) Ej)))) as Ht.
  destruct (tnth ts j); [reflexivity|contradiction].
Qed.

Lemma sshape_dist nm s : sshape nm s -> sdist lenv s.
Proof.
  induction s as [|h ts m r IH] using seg_spine; [intros _; exact I|]; intros [Hs Ho]; cbn [sents] in Hs, Ho.
  inversion Hs as [|e l Hsr Hall]; inversion Ho; subst; split; [|apply IH; split; assumption].
  apply sget_above; rewrite Forall_forall in Hall; exact Hall.
Qed.

Lemma rapply_sv {T} (tenv : list T) aenv penv s v :
  sshape false s -> sren s -> rapply (sden lenv tenv aenv penv s) v = inl (sv lenv s v).
Proof.
  intros Hs Hr; rewrite rapply_sden by exact (sshape_dist _ _ Hs); destruct v as [l j]; apply esem_sv, Hr.
Qed.

(** ** Words *)

Lemma wnf_false nm w : wnf nm w -> wnf false w.
Proof.
  destruct nm; [|exact (fun H => H)].
  assert (Hr : forall w, rnf true w -> rnf false w).
  { induction w0 as [U|s0 L a w0 IH|s0 w0 IH] using word_spine; cbn [Unique.rnf]; [| |intros []].
    - intros [H1 H2]; split; [eapply sshape_weak, H1|exact H2].
    - intros [H1 [H2 [[A [B _]] H3]]]; refine (conj H1 (conj H2 (conj (conj A (conj B _)) (IH H3)))); discriminate. }
  destruct w as [U|s0 L a w|s0 w]; cbn [Unique.wnf]; [| |intros []].
  - intros [H1 H2]; split; [eapply sshape_weak, H1|exact H2].
  - intros [H1 [H2 [[A [B _]] H3]]]; refine (conj H1 (conj H2 (conj (conj A (conj B _)) (Hr _ H3)))); discriminate.
Qed.

Lemma sren_snf s : sren s -> snf s.
Proof.
  intros Hr; apply snf_iff; intros t Ht; unfold Unique.sren in Hr; rewrite Forall_forall in Hr.
  pose proof (Hr t Ht) as H; destruct t; [exact H|contradiction].
Qed.

Lemma rnf_wnf nm w : rnf nm w -> wnf nm w.
Proof.
  destruct w as [U|s0 L a w|s0 w]; cbn [Unique.rnf Unique.wnf]; [| |intros []].
  - intros [H1 H2]; split; [exact H1|apply sren_snf, H2].
  - intros [H1 [H2 [H3 H4]]]; refine (conj H1 (conj (sren_snf _ H2) (conj H3 H4))).
Qed.

Lemma cnt_all p n : (forall i, i < n -> p i = true) -> cnt p n = n.
Proof. induction n as [|n IH]; intros H; [reflexivity|]; cbn [cnt]; rewrite IH, (H n) by (try (intros; apply H); lia); lia. Qed.

Lemma lpos_nil L : lpos lenv SNil L.
Proof.
  split.
  - intros g i Hv; unfold sv in *; cbn [sget v_label v_index] in *; rewrite cntV_cnt; f_equal.
    unfold sv; cbn [sget]; symmetry; apply cnt_all; intros i' Hi'; unfold inVb in *; cbn [v_label v_index] in *.
    apply Nat.ltb_lt in Hv; apply Nat.ltb_lt; lia.
  - intros g j Hj; exists j; reflexivity.
Qed.

Lemma atom_word L a : lok L -> wnf false (WAtom SNil L a (WEnd SNil)).
Proof.
  intros HL; cbn [Unique.wnf Unique.rnf]; refine (conj (conj (SSorted_nil _) (Forall_nil _)) (conj I (conj _ (conj (conj (SSorted_nil _) (Forall_nil _)) (Forall_nil _))))).
  refine (conj HL (conj (lpos_nil L) _)); discriminate.
Qed.

Lemma seg_labels_in s : sshape false s -> snf s -> forall k, In k (seg_labels s) -> In k labs.
Proof.
  intros Hs Hn; pose proof (proj1 (snf_iff s) Hn) as Hn'; clear Hn; rename Hn' into Hn; revert Hs Hn; induction s as [|h ts m r IH] using seg_spine; [intros _ _ k []|].
  intros [Hs Ho] Hn k Hk; cbn [sents] in Hs, Ho; inversion Hs as [|e0 l0 Hsr Hall]; inversion Ho as [|e l He Hor]; subst.
  cbn [seg_labels] in Hk; destruct Hk as [<-|Hk]; [exact (proj1 He)|]; apply in_app_or in Hk as [Hk|Hk].
  - apply in_flat_map in Hk as [t [Ht Hk]]; destruct t as [h' j|]; [|destruct Hk]; destruct Hk as [<-|[]].
    exact (Hn (NVar h' j) ltac:(rewrite stgts_cons; apply in_or_app; left; exact Ht)).
  - apply (IH (conj Hsr Hor)); [intros t Ht; apply Hn; rewrite stgts_cons; apply in_or_app; right; exact Ht|exact Hk].
Qed.

Lemma sshape_true_of s : sshape false s -> (forall e, In e (sents s) -> fst (fst e) <> LNone) -> sshape true s.
Proof.
  intros [Hs Ho] Hn; split; [exact Hs|]; apply Forall_forall; intros [[h xs] m] Hi; rewrite Forall_forall in Ho.
  destruct (Ho _ Hi) as [A [B [C _]]]; refine (conj A (conj B (conj C _))); intros _ E; apply (Hn _ Hi), lden_none, E.
Qed.

Section Settle.

Variable wc : word -> word -> option word.
Variable pn : option nat -> word -> option word.
Hypothesis Hwc : forall w1 w2 w, wnf false w1 -> wnf false w2 -> wc w1 w2 = Some w -> wnf false w.
Hypothesis Hpn : forall b w w', wnf false w -> pn b w = Some w' -> wnf (match b with None => true | Some _ => false end) w'.

Lemma otq_normal a L t t' : lok L -> tnf t -> otq ntm wc pn a L t = Some t' -> tnf t'.
Proof.
  intros HL Ht; destruct t as [h i|u w b]; cbn [otq]; [intros H; injection H as <-; exact Ht|].
  destruct (u <? ntm); [|discriminate].
  destruct (wc (WAtom SNil L a (WEnd SNil)) w) as [w'|] eqn:E1; [|discriminate].
  destruct (pn b w') as [w''|] eqn:E2; [|discriminate]; intros H; injection H as <-.
  destruct Ht as [Hb Ht]; split; [exact Hb|]; apply (Hpn b w' w''); [|exact E2].
  exact (Hwc _ _ _ (atom_word L a HL) (wnf_false _ _ Ht) E1).
Qed.

Theorem settle1_normal a A L U A' L' U' :
  sshape false A -> snf A -> lok L -> sshape false U -> snf U ->
  settle1 F ntm wc pn a A L U = Some (A', L', U') ->
  sshape false A' /\ snf A' /\ lok L' /\ sshape false U' /\ sren U' /\ lpos lenv U' L'
  /\ (entd F U LNone = ([], lsum LNone L) -> sshape true U' /\ lc lenv None L' = 0).
Proof.
  intros HA HAn HL HU HUn.
  pose proof (sshape_dist false U HU) as Ed; unfold settle1.
  destruct (linss F (map fst L ++ seg_labels U) []) as [hs|] eqn:Eh; [|discriminate].
  destruct (linss_spec lenv F HF _ _ _ Eh) as [Hin Hdist].
  assert (Hd : ldist lenv hs) by (apply Hdist; intros x y []).
  assert (Hn : NoDup hs) by (apply (linss_nodup lenv F HF _ _ _ Eh); constructor).
  assert (HLk : forall k, In k (map fst L) -> In k hs) by (intros k Hk; apply Hin; left; apply in_or_app; left; exact Hk).
  assert (HUk : forall k, In k (seg_labels U) -> In k hs) by (intros k Hk; apply Hin; left; apply in_or_app; right; exact Hk).
  assert (Hhs : forall g, In g hs -> In g labs).
  { intros g Hg; apply Hin in Hg as [Hg|[]]; apply in_app_or in Hg as [Hg|Hg].
    - apply in_map_iff in Hg as [[h n] [<- Hp]]; destruct HL as [_ Ho]; rewrite Forall_forall in Ho; exact (proj1 (Ho _ Hp)).
    - exact (seg_labels_in _ HU HUn _ Hg). }
  pose proof (linss_sfind lenv F HF L U hs Eh) as Hf.
  destruct (omap (qent F ntm wc pn a L U) hs) as [qs|] eqn:Eq; [|discriminate].
  destruct (sbuild F (map (u'ent F L U) hs)) as [U1|] eqn:EU; [|discriminate].
  destruct (lbuild F (map (fun g => (g, olp F L U g)) hs)) as [L1|] eqn:EL; [|discriminate].
  destruct (sbuild F qs) as [Q|] eqn:EQ; [|discriminate].
  destruct (scomp F ntm A Q) as [A1|] eqn:EA; [|discriminate].
  intros H; injection H as <- <- <-.
  assert (Heta : forall g, fst (u'ent F L U g) = g) by (intros g; unfold u'ent; destruct (entd F U g); reflexivity).
  (* The targets before the atom. *)
  assert (Hotg : forall g i, In g hs -> tnf (otg F U g i)).
  { intros g i Hg; unfold otg, entd; destruct (sfind F g U) as [[[ts m]|]|] eqn:E; cbn [fst snd List.length];
      [|destruct (Nat.ltb_spec i 0); [lia|exact (Hhs g Hg)]|destruct (Nat.ltb_spec i 0); [lia|exact (Hhs g Hg)]].
    destruct (Nat.ltb_spec i (List.length (tl_list ts))) as [Hi|Hi]; [|exact (Hhs g Hg)].
    apply (snf_in _ _ _ _ HUn); apply (sfind_sound lenv F HF) in E.
    apply (sget_tgts _ (lden g) U ts m (eq_sym E)), nth_In, Hi. }
  (* Q, and the segment before it. *)
  assert (HQ : sshape false Q /\ snf Q).
  { pose proof (omap_f2 _ _ _ Eq) as H2.
    assert (Hq : forall q, In q qs -> exists g, In g hs /\ qent F ntm wc pn a L U g = Some q)
      by (intros q Hq; exact (Forall2_in_r _ _ _ _ H2 Hq)).
    destruct (sbuild_shape _ _ EQ) as [Hs [Ht _]].
    - intros h xs m Hi; destruct (Hq _ Hi) as [g [Hg E]]; unfold qent in E; revert E.
      destruct (omap (fun i => otq ntm wc pn a L (otg F U g i)) (oP F L U g)); [|discriminate].
      intros E; injection E as <- _ _; exact (Hhs g Hg).
    - split; [exact Hs|]; apply snf_iff; intros t Hin'; destruct (Ht t Hin') as [h [xs [m [Hi Hx]]]].
      destruct (Hq _ Hi) as [g [Hg E]]; unfold qent in E; revert E.
      destruct (omap (fun i => otq ntm wc pn a L (otg F U g i)) (oP F L U g)) as [ts|] eqn:Eo; [|discriminate].
      intros E; injection E as _ <- _.
      destruct (Forall2_in_r _ _ _ _ (omap_f2 _ _ _ Eo) Hx) as [i [_ Et]].
      exact (otq_normal _ _ _ _ HL (Hotg g i Hg) Et). }
  destruct (scomp_normal _ _ _ EA HA HAn (proj1 HQ) (proj2 HQ)) as [HA1 HA1n].
  (* The lifts. *)
  destruct (lbuild_spec _ _ EL) as [HLc HLok].
  assert (HL1 : lok L1).
  { apply HLok; intros p Hp; apply in_map_iff in Hp as [g [<- Hg]]; exact (Hhs g Hg). }
  (* The segment after the atom. *)
  destruct (sbuild_shape _ _ EU) as [HU1 [HU1t HU1g]].
  { intros h xs m Hi; apply in_map_iff in Hi as [g [E Hg]]; pose proof (Heta g) as Eg; rewrite E in Eg; cbn [fst] in Eg; subst h; exact (Hhs g Hg). }
  assert (HU1r : sren U1).
  { unfold Unique.sren; apply Forall_forall; intros t Ht; destruct (HU1t t Ht) as [h [xs [m [Hi Hx]]]].
    apply in_map_iff in Hi as [g [E Hg]]; unfold u'ent in E; destruct (entd F U g) as [xs0 m0] eqn:Ee.
    injection E as _ <- _; apply in_map_iff in Hx as [i [<- _]].
    destruct (inP L (otg F U g i)) eqn:Ep; [exact (Hhs g Hg)|].
    destruct (otg F U g i) as [h' j|] eqn:Eo; [|discriminate]; cbn [oreidx].
    exact (Hhs _ (otg_label lenv F HF U hs HUk Hf g i h' j Hg Eo)). }
  assert (HsvU1 : forall l j, inl (sv lenv U1 (mk_rvar l j)) = esl lenv tenvU aenvU penvU l (map (u'ent F L U) hs) j).
  { intros l j; rewrite <- (esem_sv tenvU aenvU penvU _ _ _ HU1r); apply (proj2 (sbuild_sem lenv tenvU aenvU penvU F HF 0 (le_n 0) _ _ EU)). }
  assert (Hsv_in : forall g i, In g hs -> sv lenv U1 (mk_rvar (lden g) i) = tvar lenv (u'tgt F L U g i)).
  { intros g i Hg; pose proof (HsvU1 (lden g) i) as E; rewrite (U'_in lenv tenvU aenvU penvU F 0 (le_n 0) L U hs Hd g i Hg) in E.
    unfold u'tgt in *; destruct (inP L (otg F U g i)) eqn:Ep.
    - cbn [tden rtarget_result] in E; injection E as E; exact E.
    - destruct (otg F U g i) as [h j|] eqn:Eo; [|discriminate]; cbn [oreidx tden rtarget_result] in E.
      injection E as E; exact E. }
  assert (Hsv_out : forall l j, (forall g, In g hs -> lden g <> l) -> sv lenv U1 (mk_rvar l j) = mk_rvar l j).
  { intros l j Hl; pose proof (HsvU1 l j) as E; rewrite (U'_out lenv tenvU aenvU penvU F L U hs l j Hl) in E.
    injection E as E; exact E. }
  assert (Hlc_in : forall g, In g hs -> lc lenv (lden g) L1 = olp F L U g).
  { intros g Hg; rewrite HLc; apply (lc_map lenv tenvU 0 (le_n 0) (olp F L U) hs g Hd Hn Hg). }
  assert (Hlc_out : forall l, (forall g, In g hs -> lden g <> l) -> lc lenv l L1 = 0).
  { intros l Hl; rewrite HLc; apply (lc_out lenv hs _ l); [|exact Hl].
    intros k Hk; rewrite map_map in Hk; cbn in Hk; rewrite map_id in Hk; exact Hk. }
  assert (HinV : forall g i, In g hs -> inVb lenv L1 (sv lenv U1 (mk_rvar (lden g) i)) = inP L (otg F U g i)).
  { intros g i Hg; rewrite (Hsv_in g i Hg); unfold u'tgt, inVb.
    destruct (inP L (otg F U g i)) eqn:Ep.
    - cbn [tvar v_label v_index]; rewrite (Hlc_in g Hg); apply Nat.ltb_lt.
      exact (proj2 (oP_pos tenvU F 0 (le_n 0) L U hs g i Hg Ep)).
    - destruct (otg F U g i) as [h j|] eqn:Eo; [|discriminate]; cbn [oreidx tvar v_label v_index].
      cbn [inP] in Ep; apply Nat.ltb_ge in Ep.
      rewrite (Hlc_in h (otg_label lenv F HF U hs HUk Hf g i h j Hg Eo)); apply Nat.ltb_ge; lia. }
  assert (Hopos : forall g i, In g hs -> opos F L U g i = cnt (fun i' => inP L (otg F U g i')) i).
  { intros g i Hg; unfold opos, oP; rewrite filter_lt_cnt.
    destruct (Nat.le_ge_cases i (orng F L U g)) as [Hi|Hi]; [rewrite Nat.min_l by exact Hi; reflexivity|].
    rewrite Nat.min_r by exact Hi; symmetry; apply cnt_stable; [|exact Hi].
    intros i' Hi'; exact (proj2 (otg_tail tenvU F 0 (le_n 0) L U hs g i' Hg Hi')). }
  assert (Hcnt : forall g i, In g hs -> cntV lenv U1 L1 (lden g) i = opos F L U g i).
  { intros g i Hg; rewrite cntV_cnt, Hopos by exact Hg; apply cnt_ext; intros i' _; apply HinV, Hg. }
  assert (Hcase : forall l, (exists g, In g hs /\ lden g = l) \/ (forall g, In g hs -> lden g <> l)).
  { intros l; destruct (existsb (fun g => label_eqb (lden g) l) hs) eqn:Ex.
    - left; apply existsb_exists in Ex as [g [Hg El]]; apply label_eqb_eq in El; exists g; split; assumption.
    - right; intros g Hg E; subst l.
      rewrite (proj2 (existsb_exists _ _) (ex_intro _ g (conj Hg (label_eqb_refl _)))) in Ex; discriminate. }
  refine (conj HA1 (conj HA1n (conj HL1 (conj HU1 (conj HU1r (conj _ _)))))).
  - split.
    + intros l j Hv; destruct (Hcase l) as [[g [Hg <-]]|Hl].
      * rewrite HinV in Hv by exact Hg; rewrite (Hsv_in g j Hg); unfold u'tgt; rewrite Hv; cbn [tvar].
        rewrite Hcnt by exact Hg; reflexivity.
      * rewrite (Hsv_out l j Hl) in Hv; unfold inVb in Hv; cbn [v_index v_label] in Hv.
        rewrite (Hlc_out l Hl) in Hv; destruct j; discriminate.
    + intros l j Hj; destruct (Hcase l) as [[g [Hg <-]]|Hl]; [|rewrite (Hlc_out l Hl) in Hj; lia].
      rewrite (Hlc_in g Hg) in Hj; unfold olp, oP in Hj; rewrite filter_cnt in Hj.
      destruct (cnt_ivt _ _ _ Hj) as [i [_ [Hp Hc]]]; exists i.
      rewrite (Hsv_in g i Hg); unfold u'tgt; rewrite Hp; cbn [tvar]; rewrite Hopos, Hc by exact Hg; reflexivity.
  - intros HeN.
    assert (Horng : orng F L U LNone = 0) by (unfold orng; rewrite HeN; cbn [List.length]; lia).
    assert (Holp0 : olp F L U LNone = 0) by (unfold olp, oP; rewrite Horng; reflexivity).
    assert (Hu0 : u'ent F L U LNone = (LNone, ([], 0))).
    { unfold u'ent; rewrite HeN, Horng, Holp0; cbn [seq map List.length]; f_equal; f_equal; lia. }
    split.
    + apply sshape_true_of; [exact HU1|]; apply HU1g; intros h xs m Hi Ehn; subst h.
      apply in_map_iff in Hi as [g [E Hg]]; pose proof (Heta g) as Eg; rewrite E in Eg; cbn [fst] in Eg; subst g.
      rewrite Hu0 in E; injection E as <- <-; split; reflexivity.
    + destruct (Hcase None) as [[g [Hg Eg]]|Hl]; [|apply Hlc_out, Hl].
      apply lden_none in Eg; subst g; change (lc lenv None L1 = 0) with (lc lenv (lden LNone) L1 = 0); rewrite (Hlc_in LNone Hg); exact Holp0.
Qed.

Theorem settle_normal nm A L a w w' : sshape false A -> snf A -> lok L ->
  (if isend w then wnf false w /\ (nm = true -> entd F (whead w) LNone = ([], lsum LNone L)) else wnf nm w) ->
  settle F ntm wc pn A L a w = Some w' -> wnf nm w'.
Proof.
  intros HA HAn HL Hw; unfold settle.
  destruct (settle1 F ntm wc pn a A L (whead w)) as [[[A' L'] U']|] eqn:E; [|discriminate]; intros H; injection H as <-.
  assert (Hh : sshape false (whead w) /\ snf (whead w)).
  { destruct w as [s0|s0 L0 a0 w0|s0 w0]; cbn [isend whead] in *; [| |cbn [Unique.wnf] in Hw; destruct Hw].
    - destruct Hw as [[Hs Hn] _]; split; assumption.
    - destruct Hw as [Hs [Hn _]]; split; assumption. }
  destruct (settle1_normal _ _ _ _ _ _ _ HA HAn HL (proj1 Hh) (proj2 Hh) E) as [HA' [HA'n [HL' [HU' [HU'r [Hp Hnm]]]]]].
  destruct w as [s0|s0 L0 a0 w0|s0 w0]; cbn [isend whead wsethead] in *; cbn [Unique.wnf Unique.rnf]; [| |cbn [Unique.wnf] in Hw; destruct Hw].
  - destruct Hw as [_ Hc].
    refine (conj HA' (conj HA'n (conj (conj HL' (conj Hp _)) (conj _ HU'r)))).
    + intros Et _; exact (proj2 (Hnm (Hc Et))).
    + destruct nm; [exact (proj1 (Hnm (Hc eq_refl)))|exact HU'].
  - destruct Hw as [_ [_ [Ha Hr]]].
    refine (conj HA' (conj HA'n (conj (conj HL' (conj Hp _)) (conj HU' (conj HU'r (conj Ha Hr)))))).
    intros _ E'; discriminate E'.
Qed.

Lemma settle_atom A L a w w' : settle F ntm wc pn A L a w = Some w' -> isend w' = false.
Proof. unfold settle; destruct (settle1 _ _ _ _ _ _ _ _) as [[[? ?] ?]|]; [|discriminate]; intros H; injection H as <-; reflexivity. Qed.

Lemma pnormf_atom w w' : pnormf F ntm wc pn w = Some w' -> isend w = false -> isend w' = false.
Proof.
  destruct w as [s0|A L a w|s0 w]; [intros _ E; discriminate E| |cbn [pnormf]; discriminate]; cbn [pnormf]; intros H _.
  destruct w as [s|A' L' a' w1|s1 w1]; [| |cbn [pnormf] in H; discriminate H].
  - destruct (pfinal F L s); [exact (settle_atom _ _ _ _ _ H)|discriminate].
  - destruct (pnormf F ntm wc pn (WAtom A' L' a' w1)); [exact (settle_atom _ _ _ _ _ H)|discriminate].
Qed.

Lemma lsum_above h L : (forall p, In p L -> olabel_lt (lden h) (lden (fst p))) -> lsum h L = 0.
Proof.
  induction L as [|[h' n] L IH]; intros H; [reflexivity|]; cbn [lsum].
  rewrite IH by (intros p Hp; apply H; right; exact Hp).
  destruct (lexp_eqb h h') eqn:E; [|reflexivity]; apply lexp_eqb_eq in E; subst h'.
  exfalso; exact (olabel_lt_irrefl _ (H (h, n) (or_introl eq_refl))).
Qed.

Lemma lcount_lsum h L : lok L -> lcount h L = lsum h L.
Proof.
  induction L as [|[h' n] L IH]; intros HL; [reflexivity|]; cbn [lcount lsum].
  destruct (lexp_eqb h h') eqn:E; [|apply IH, (lok_tail _ _ _ _ HL)].
  apply lexp_eqb_eq in E; subst h'; rewrite lsum_above; [lia|].
  destruct HL as [Hs _]; inversion Hs as [|x l Hsr Hall]; subst; rewrite Forall_forall in Hall; exact Hall.
Qed.

Lemma lcount_in h L : lok L -> lcount h L <> 0 -> In h labs.
Proof.
  induction L as [|[h' n] L IH]; intros HL Hn; [cbn in Hn; lia|]; cbn [lcount] in Hn.
  destruct (lexp_eqb h h') eqn:E; [apply lexp_eqb_eq in E; subst h'; exact (proj1 (lok_head _ _ _ _ _ HL))|].
  apply IH; [apply (lok_tail _ _ _ _ HL)|exact Hn].
Qed.

Lemma sfind_none s : sfind F LNone s = Some (sget lenv None s).
Proof.
  induction s as [|h ts m r IH] using seg_spine; [reflexivity|]; cbn [sfind sget].
  assert (Hc : exists c, lcmp F LNone h = Some c).
  { unfold lcmp; destruct (lexp_eqb LNone h) eqn:E; [eexists; reflexivity|].
    destruct (lt_known F LNone h); [eexists; reflexivity|].
    destruct h; [discriminate E| |]; unfold lt_known, lt_list; destruct (List.length (ofacts F)); cbn; eexists; reflexivity. }
  destruct Hc as [c Ec]; rewrite Ec; pose proof (lcmp_sound lenv F HF _ _ _ Ec) as Hs.
  destruct c; cbn [cmp_holds] in Hs.
  - subst h; reflexivity.
  - rewrite (proj2 (label_eqb_neq _ _)); [exact IH|]; intros E; rewrite E in Hs; exact (olabel_lt_irrefl _ Hs).
  - rewrite (proj2 (label_eqb_neq _ _)); [exact IH|]; intros E; rewrite E in Hs; exact (olabel_lt_irrefl _ Hs).
Qed.

Lemma sset_none_entd k s s' : sset F LNone TNil k s = Some s' -> entd F s' LNone = ([], k).
Proof.
  rewrite sset_unfold; destruct (sdel F LNone s) as [s0|] eqn:Ed; [|discriminate].
  pose proof (sdel_sound lenv F HF _ _ _ Ed None) as H0; cbn [lden] in H0; rewrite label_eqb_refl in H0.
  cbn [tl_list rev trim]; unfold entd; destruct k as [|k]; intros H; injection H as <-; rewrite sfind_none.
  - rewrite H0; reflexivity.
  - destruct (sput_sound lenv F LNone TNil (S k) s0 H0) as [H1 _].
    rewrite (H1 None); cbn [lden]; rewrite label_eqb_refl; reflexivity.
Qed.

Lemma pnormf_normal w : wnf false w -> forall w', pnormf F ntm wc pn w = Some w' -> wnf true w'.
Proof.
  induction w as [s|A L a w IH|s w IH] using word_spine; cbn [pnormf]; [| |intros []].
  - intros [Hs Hn] w' H; injection H as <-; cbn [Unique.wnf].
    destruct (sdrop_none_shape _ Hs) as [Hs' Ht']; split; [exact Hs'|].
    apply snf_iff; intros t Ht; apply (snf_in _ _ _ _ Hn), Ht', Ht.
  - intros Hw w'; destruct Hw as [HA [HAn [[HL [Hp _]] Hr]]].
    destruct w as [s|A' L' a' w1|s1 w1]; [| |cbn [Unique.rnf] in Hr; destruct Hr].
    + unfold pfinal.
      destruct (sset F LNone TNil (lcount LNone L) s) as [s'|] eqn:Es; [|discriminate]; intros H.
      cbn [Unique.rnf] in Hr; destruct Hr as [Hs Hsr].
      apply (settle_normal true A L a (WEnd s') w' HA HAn HL); [|exact H].
      cbn [isend whead]; split.
      * assert (Hl : In LNone labs \/ (tl_list TNil = [] /\ lcount LNone L = 0)).
        { destruct (Nat.eq_dec (lcount LNone L) 0) as [E|E]; [right; split; [reflexivity|exact E]|left].
          exact (lcount_in _ _ HL E). }
        destruct (sset_shape false _ _ _ _ _ Es Hs Hl ltac:(discriminate)) as [Hs' [_ [Ht _]]].
        split; [exact Hs'|]; apply snf_iff; intros t Hin; destruct (Ht t Hin) as [Hin'|[]].
        apply (snf_in _ _ _ _ (sren_snf _ Hsr)), Hin'.
      * intros _; rewrite (sset_none_entd _ _ _ Es), (lcount_lsum _ _ HL); reflexivity.
    + destruct (pnormf F ntm wc pn (WAtom A' L' a' w1)) as [w''|] eqn:E; [|discriminate]; intros H.
      apply (settle_normal true A L a w'' w' HA HAn HL); [|exact H].
      rewrite (pnormf_atom _ _ E eq_refl).
      apply (IH (rnf_wnf _ _ Hr) w''); first [exact E|reflexivity].
Qed.

Lemma wcomp_with_normal w1 : wnf false w1 -> forall w2 w, wnf false w2 -> wcomp_with F ntm wc pn w1 w2 = Some w -> wnf false w.
Proof.
  induction w1 as [A|A L a w1 IH|A w1 IH] using word_spine; cbn [wcomp_with]; [| |intros []].
  - intros [HA HAn] w2 w Hw2 H; exact (wcons_normal _ _ _ H HA HAn Hw2).
  - intros [HA [HAn [[HL _] Hr]]] w2 w Hw2.
    destruct (wcomp_with F ntm wc pn w1 w2) as [w'|] eqn:E; [|discriminate]; intros H.
    pose proof (IH (rnf_wnf _ _ Hr) w2 w' Hw2 E) as Hw'.
    apply (settle_normal false A L a w' w HA HAn HL); [|exact H].
    destruct (isend w'); [split; [exact Hw'|intros E'; discriminate E']|exact Hw'].
Qed.

End Settle.

Lemma wops_normal n :
  (forall w1 w2 w, wnf false w1 -> wnf false w2 -> fst (wops F ntm n) w1 w2 = Some w -> wnf false w)
  /\ (forall b w w', wnf false w -> snd (wops F ntm n) b w = Some w' ->
                     wnf (match b with None => true | Some _ => false end) w').
Proof.
  induction n as [|n [IHc IHp]]; [split; intros; discriminate|]; cbn [wops].
  destruct (wops F ntm n) as [wc pn] eqn:Ew; cbn [fst snd] in *; split.
  - intros w1 w2 w H1 H2 H; exact (wcomp_with_normal wc pn IHc IHp w1 H1 w2 w H2 H).
  - intros [m|] w w' Hw H; cbn [bnormf] in H; [injection H as <-; exact Hw|].
    exact (pnormf_normal wc pn IHc IHp w Hw w' H).
Qed.

Lemma wcomp_normal w1 w2 w : wnf false w1 -> wnf false w2 -> wcomp F ntm w1 w2 = Some w -> wnf false w.
Proof. exact (proj1 (wops_normal 64) w1 w2 w). Qed.

Lemma pnormw_normal b w w' : wnf false w -> pnormw F ntm b w = Some w' ->
  wnf (match b with None => true | Some _ => false end) w'.
Proof. exact (proj2 (wops_normal 64) b w w'). Qed.

(** ** Lifting and pushing *)

Lemma shseg_shape h : In h labs -> sshape false (shseg h 1) /\ sren (shseg h 1).
Proof.
  intros Hh; split; [split|constructor].
  - constructor; constructor.
  - constructor; [|constructor]; cbn [Unique.eshape].
    split; [exact Hh|split; [exact I|split; [right; discriminate|intros E; discriminate E]]].
Qed.

Lemma sfront_spec h t s s' : sfront F h t s = Some s' -> sshape false s -> In h labs ->
  sshape false s' /\ (forall t', In t' (stgts s') -> t' = t \/ In t' (stgts s)).
Proof.
  unfold sfront.
  destruct (sfind F h s) as [e|] eqn:Ef; [|discriminate]; destruct (ofe e) as [ts m] eqn:Eo; intros E Hs Hh.
  destruct (sset_shape false _ _ _ _ _ E Hs (or_introl Hh) ltac:(discriminate)) as [Hs' [_ [Ht _]]].
  split; [exact Hs'|]; intros t' Hin; destruct (Ht t' Hin) as [H|H]; [right; exact H|].
  destruct H as [<-|H]; [left; reflexivity|right].
  apply (sfind_sound lenv F HF) in Ef; destruct e as [[ts0 m0]|]; cbn [ofe] in Eo; injection Eo as <- <-; [|destruct H].
  apply (sget_tgts _ (lden h) s _ _ (eq_sym Ef) _ H).
Qed.

Lemma slift_ren h s s' : slift F ntm h s = Some s' -> sshape false s -> sren s -> In h labs -> sshape false s' /\ sren s'.
Proof.
  unfold slift; destruct (scomp F ntm (shseg h 1) s) as [s1|] eqn:E1; [|discriminate]; intros E Hs Hr Hh.
  destruct (shseg_shape h Hh) as [Hsh Hshr].
  destruct (scomp_ren _ _ _ E1 Hsh Hshr Hs Hr) as [Hs1 Hr1].
  destruct (sfront_spec _ _ _ _ E Hs1 Hh) as [Hs' Ht']; split; [exact Hs'|].
  unfold Unique.sren in *; rewrite Forall_forall in *; intros t Ht; destruct (Ht' t Ht) as [->|H]; [exact Hh|apply Hr1, H].
Qed.

Lemma slift_normal h s s' : slift F ntm h s = Some s' -> sshape false s -> snf s -> In h labs -> sshape false s' /\ snf s'.
Proof.
  unfold slift; destruct (scomp F ntm (shseg h 1) s) as [s1|] eqn:E1; [|discriminate]; intros E Hs Hn Hh.
  destruct (shseg_shape h Hh) as [Hsh Hshr].
  destruct (scomp_normal _ _ _ E1 Hsh (sren_snf _ Hshr) Hs Hn) as [Hs1 Hn1].
  destruct (sfront_spec _ _ _ _ E Hs1 Hh) as [Hs' Ht']; split; [exact Hs'|].
  apply snf_iff; intros t Ht; destruct (Ht' t Ht) as [->|H]; [exact Hh|apply (snf_in _ _ _ _ Hn1), H].
Qed.

Local Notation tenvR := (repeat tt ntm).

Lemma stgts_stargets s : stgts s = stargets s.
Proof. induction s as [|h ts m r IH] using seg_spine; [reflexivity|]; rewrite stgts_cons, IH; reflexivity. Qed.

Lemma ren_dd s : sshape false s -> sren s -> sdistd lenv s.
Proof.
  intros Hs Hr; apply (proj2 (sdistd_iff lenv s)); split; [exact (sshape_dist _ _ Hs)|].
  intros t Ht; rewrite <- stgts_stargets in Ht; unfold Unique.sren in Hr; rewrite Forall_forall in Hr.
  pose proof (Hr t Ht) as H; destruct t; [exact I|contradiction].
Qed.

Lemma sv_slift h s s' v : slift F ntm h s = Some s' -> sshape false s -> sren s -> sshape false s' -> sren s' ->
  sv lenv s' v = if rvar_eqb v (mk_rvar (lden h) 0) then v
                 else shift_rvar (mk_rvar (lden h) 0) (sv lenv s (unshift_rvar (mk_rvar (lden h) 0) v)).
Proof.
  intros E Hs Hr Hs' Hr'.
  pose proof (proj2 (slift_sound lenv tenvR aenvU penvU F HF ntm (eq_ind_r (fun n => ntm <= n) (le_n ntm) (repeat_length tt ntm)) h s s' (ren_dd s Hs Hr) E)) as Hd.
  pose proof (f_equal (fun a => rapply a v) Hd) as E'; cbv beta in E'.
  rewrite rapply_lift, !(rapply_sv tenvR aenvU penvU) in E' by assumption.
  destruct (rvar_eqb v (mk_rvar (lden h) 0)); injection E' as E'; exact E'.
Qed.

Lemma cnt_succ p q i : q 0 = true -> (forall k, q (S k) = p k) -> cnt q (S i) = S (cnt p i).
Proof.
  intros H0 HS; induction i as [|i IH]; cbn [cnt]; [rewrite H0; reflexivity|].
  cbn [cnt] in IH; rewrite IH, HS; lia.
Qed.

Lemma lpos_lift h s s' L L' : In h labs -> sshape false s -> sren s -> sshape false s' -> sren s' ->
  slift F ntm h s = Some s' -> ladd F h 1 L = Some L' -> lpos lenv s L -> lpos lenv s' L'.
Proof.
  intros Hh Hs Hr Hs' Hr' E EL [Hp1 Hp2].
  set (g0 := lden h).
  assert (Hlc : forall l, lc lenv l L' = (if label_eqb g0 l then 1 else 0) + lc lenv l L) by apply (ladd_spec _ _ _ _ EL).
  assert (Hsh : forall y, inVb lenv L' (shift_rvar (mk_rvar g0 0) y) = inVb lenv L y).
  { intros [l i]; unfold inVb, shift_rvar; cbn [v_label v_index]; rewrite Hlc.
    destruct (label_eqb_spec g0 l) as [<-|Hne].
    - rewrite label_eqb_refl; cbn [andb Nat.leb v_label v_index].
      destruct (Nat.ltb_spec i (lc lenv g0 L)), (Nat.ltb_spec (S i) (1 + lc lenv g0 L)); lia || reflexivity.
    - cbn [andb v_label v_index]; rewrite (proj2 (label_eqb_neq _ _) Hne); reflexivity. }
  assert (Hsv0 : sv lenv s' (mk_rvar g0 0) = mk_rvar g0 0)
    by (rewrite (sv_slift _ _ _ _ E Hs Hr Hs' Hr'), rvar_eqb_refl; reflexivity).
  assert (HsvS : forall k, sv lenv s' (mk_rvar g0 (S k)) = shift_rvar (mk_rvar g0 0) (sv lenv s (mk_rvar g0 k))).
  { intros k; rewrite (sv_slift _ _ _ _ E Hs Hr Hs' Hr'); fold g0.
    destruct (rvar_eqb_spec (mk_rvar g0 (S k)) (mk_rvar g0 0)) as [E'|_]; [discriminate E'|].
    unfold unshift_rvar; cbn [v_label v_index]; rewrite label_eqb_refl; cbn [andb Nat.ltb Nat.leb].
    replace (S k - 1) with k by lia; reflexivity. }
  assert (Hsvo : forall l i, l <> g0 -> sv lenv s' (mk_rvar l i) = shift_rvar (mk_rvar g0 0) (sv lenv s (mk_rvar l i))).
  { intros l i Hl; rewrite (sv_slift _ _ _ _ E Hs Hr Hs' Hr'); fold g0.
    destruct (rvar_eqb_spec (mk_rvar l i) (mk_rvar g0 0)) as [E'|_]; [injection E' as E'; contradiction|].
    unfold unshift_rvar; cbn [v_label v_index]; rewrite (proj2 (label_eqb_neq _ _) (not_eq_sym Hl)); reflexivity. }
  assert (Hshl : forall l i, l <> g0 -> shift_rvar (mk_rvar g0 0) (mk_rvar l i) = mk_rvar l i)
    by (intros l i Hl; unfold shift_rvar; cbn [v_label v_index]; rewrite (proj2 (label_eqb_neq _ _) (not_eq_sym Hl)); reflexivity).
  assert (Hshg : forall i, shift_rvar (mk_rvar g0 0) (mk_rvar g0 i) = mk_rvar g0 (S i))
    by (intros i; unfold shift_rvar; cbn [v_label v_index]; rewrite label_eqb_refl; reflexivity).
  assert (Hc0 : forall i, cntV lenv s' L' g0 (S i) = S (cntV lenv s L g0 i)).
  { intros i; rewrite !cntV_cnt; apply cnt_succ.
    - rewrite Hsv0; unfold inVb; cbn [v_label v_index]; rewrite Hlc, label_eqb_refl; reflexivity.
    - intros k; rewrite HsvS, Hsh; reflexivity. }
  assert (Hco : forall l i, l <> g0 -> cntV lenv s' L' l i = cntV lenv s L l i).
  { intros l i Hl; rewrite !cntV_cnt; apply cnt_ext; intros k _; rewrite Hsvo, Hsh by exact Hl; reflexivity. }
  split.
  - intros l i Hv; destruct (label_eqb_spec l g0) as [->|Hl].
    + destruct i as [|i]; [rewrite Hsv0; reflexivity|].
      rewrite HsvS, Hsh in Hv; rewrite HsvS, (Hp1 _ _ Hv), Hshg, Hc0; reflexivity.
    + rewrite (Hsvo l i Hl), Hsh in Hv; rewrite (Hsvo l i Hl), (Hp1 _ _ Hv), (Hshl l _ Hl), Hco by exact Hl; reflexivity.
  - intros l j Hj; rewrite Hlc in Hj; destruct (label_eqb_spec g0 l) as [<-|Hl].
    + destruct j as [|j]; [exists 0; exact Hsv0|].
      destruct (Hp2 g0 j ltac:(lia)) as [k Ek]; exists (S k); rewrite HsvS, Ek, Hshg; reflexivity.
    + destruct (Hp2 l j ltac:(lia)) as [i Ei]; exists i.
      rewrite (Hsvo l i (not_eq_sym Hl)), Ei, (Hshl l j (not_eq_sym Hl)); reflexivity.
Qed.

Lemma whead_lift h w w' : wlift F ntm h w = Some w' -> slift F ntm h (whead w) = Some (whead w').
Proof.
  destruct w as [s|s L a w|s w]; cbn [wlift whead]; [| |discriminate].
  - destruct (slift F ntm h s); [intros H; injection H as <-; reflexivity|discriminate].
  - destruct (slift F ntm h s), (ladd F h 1 L), (wlift F ntm h w); try discriminate; intros H; injection H as <-; reflexivity.
Qed.

Lemma whead_shape nm w : rnf nm w -> sshape false (whead w) /\ sren (whead w).
Proof.
  destruct w as [U|s L a w|s w]; cbn [Unique.rnf whead]; [| |intros []].
  - intros [H1 H2]; split; [eapply sshape_weak, H1|exact H2].
  - intros [H1 [H2 _]]; split; assumption.
Qed.

Lemma rnf_lift h w : In h labs -> rnf false w -> forall w', wlift F ntm h w = Some w' -> rnf false w'.
Proof.
  intros Hh; induction w as [U|s L a w IH|s w IH] using word_spine; cbn [wlift]; [| |intros []].
  - intros [Hs Hr] w'; destruct (slift F ntm h U) as [U'|] eqn:E; [|discriminate]; intros H; injection H as <-.
    exact (slift_ren _ _ _ E Hs Hr Hh).
  - intros [Hs [Hr [[HL [Hp _]] Hw]]] w'.
    destruct (slift F ntm h s) as [s'|] eqn:Es; [|discriminate].
    destruct (ladd F h 1 L) as [L'|] eqn:EL; [|discriminate].
    destruct (wlift F ntm h w) as [w1|] eqn:Ew; [|discriminate]; intros H; injection H as <-.
    destruct (slift_ren _ _ _ Es Hs Hr Hh) as [Hs' Hr'].
    pose proof (IH Hw w1 eq_refl) as Hw1.
    destruct (whead_shape _ _ Hw) as [Hh0 Hr0]; destruct (whead_shape _ _ Hw1) as [Hh1 Hr1].
    refine (conj Hs' (conj Hr' (conj (conj _ (conj _ _)) Hw1))).
    + exact (proj2 (proj2 (ladd_spec _ _ _ _ EL)) HL Hh ltac:(discriminate)).
    + exact (lpos_lift _ _ _ _ _ Hh Hh0 Hr0 Hh1 Hr1 (whead_lift _ _ _ Ew) EL Hp).
    + intros E'; discriminate E'.
Qed.

Lemma wlift_normal h w w' : In h labs -> wnf false w -> wlift F ntm h w = Some w' -> wnf false w'.
Proof.
  intros Hh; destruct w as [s|s L a w|s w]; cbn [wlift]; [| |intros []].
  - intros [Hs Hn]; destruct (slift F ntm h s) as [s'|] eqn:E; [|discriminate]; intros H; injection H as <-.
    exact (slift_normal _ _ _ E Hs Hn Hh).
  - intros [Hs [Hn [[HL [Hp _]] Hw]]].
    destruct (slift F ntm h s) as [s'|] eqn:Es; [|discriminate].
    destruct (ladd F h 1 L) as [L'|] eqn:EL; [|discriminate].
    destruct (wlift F ntm h w) as [w1|] eqn:Ew; [|discriminate]; intros H; injection H as <-.
    destruct (slift_normal _ _ _ Es Hs Hn Hh) as [Hs' Hn'].
    pose proof (rnf_lift h w Hh Hw w1 Ew) as Hw1.
    destruct (whead_shape _ _ Hw) as [Hh0 Hr0]; destruct (whead_shape _ _ Hw1) as [Hh1 Hr1].
    refine (conj Hs' (conj Hn' (conj (conj _ (conj _ _)) Hw1))).
    + exact (proj2 (proj2 (ladd_spec _ _ _ _ EL)) HL Hh ltac:(discriminate)).
    + exact (lpos_lift _ _ _ _ _ Hh Hh0 Hr0 Hh1 Hr1 (whead_lift _ _ _ Ew) EL Hp).
    + intros E'; discriminate E'.
Qed.

Lemma wpush_normal h t w w' : In h labs -> tnf t -> wnf false w -> wpush F ntm h t w = Some w' -> wnf false w'.
Proof.
  intros Hh Ht; destruct w as [s|s L a w|s w]; cbn [wpush]; [| |intros []].
  - intros [Hs Hn]; destruct (sfront F h t s) as [s'|] eqn:E; [|discriminate]; intros H; injection H as <-.
    destruct (sfront_spec _ _ _ _ E Hs Hh) as [Hs' Ht']; split; [exact Hs'|].
    apply snf_iff; intros t' Hin; destruct (Ht' t' Hin) as [->|H]; [exact Ht|apply (snf_in _ _ _ _ Hn), H].
  - intros [Hs [Hn [[HL [Hp _]] Hw]]].
    destruct (sfront F h t s) as [s'|] eqn:Es; [|discriminate].
    destruct (ladd F h 1 L) as [L'|] eqn:EL; [|discriminate].
    destruct (wlift F ntm h w) as [w1|] eqn:Ew; [|discriminate]; intros H; injection H as <-.
    destruct (sfront_spec _ _ _ _ Es Hs Hh) as [Hs' Ht'].
    pose proof (rnf_lift h w Hh Hw w1 Ew) as Hw1.
    destruct (whead_shape _ _ Hw) as [Hh0 Hr0]; destruct (whead_shape _ _ Hw1) as [Hh1 Hr1].
    refine (conj Hs' (conj _ (conj (conj _ (conj _ _)) Hw1))).
    + apply snf_iff; intros t' Hin; destruct (Ht' t' Hin) as [->|H]; [exact Ht|apply (snf_in _ _ _ _ Hn), H].
    + exact (proj2 (proj2 (ladd_spec _ _ _ _ EL)) HL Hh ltac:(discriminate)).
    + exact (lpos_lift _ _ _ _ _ Hh Hh0 Hr0 Hh1 Hr1 (whead_lift _ _ _ Ew) EL Hp).
    + intros E'; discriminate E'.
Qed.

Lemma wouter_normal h w w' : In h labs -> wnf false w -> wouter F ntm h w = Some w' -> wnf false w'.
Proof.
  intros Hh Hw E; destruct (shseg_shape h Hh) as [Hs Hr].
  exact (wcons_normal _ _ _ E Hs (sren_snf _ Hr) Hw).
Qed.

(** ** The labels and payload atoms of an expression *)

Fixpoint alabs (e : aexp) : list lexp :=
  match e with
  | AId | AAtom _ => []
  | ACompose a b => alabs a ++ alabs b
  | AOuter h a | ALift h a => h :: alabs a
  | AInner h t a => h :: tlabs t ++ alabs a
  end
with tlabs (t : texp) : list lexp :=
  match t with
  | TVarE h _ => [h]
  | TBindE _ p => plabs p
  | TShiftE h t => h :: tlabs t
  end
with plabs (p : pexp) : list lexp :=
  match p with
  | PId | PAtom _ => []
  | PComp a p => alabs a ++ plabs p
  | PShift h p => h :: plabs p
  end.

(** The payload atoms of an expression are in scope. *)
Fixpoint ascope (e : aexp) : Prop :=
  match e with
  | AId | AAtom _ => True
  | ACompose a b => ascope a /\ ascope b
  | AOuter _ a | ALift _ a => ascope a
  | AInner _ t a => tscope t /\ ascope a
  end
with tscope (t : texp) : Prop :=
  match t with
  | TVarE _ _ => True
  | TBindE _ p => pscope p
  | TShiftE _ t => tscope t
  end
with pscope (p : pexp) : Prop :=
  match p with
  | PId => True
  | PAtom n => n < npa
  | PComp a p => ascope a /\ pscope p
  | PShift _ p => pscope p
  end.

End Normal.

(** A bound that puts all the payload atoms of an expression in scope. *)
Fixpoint apmax (e : aexp) : nat :=
  match e with
  | AId | AAtom _ => 0
  | ACompose a b => Nat.max (apmax a) (apmax b)
  | AOuter _ a | ALift _ a => apmax a
  | AInner _ t a => Nat.max (tpmax t) (apmax a)
  end
with tpmax (t : texp) : nat :=
  match t with
  | TVarE _ _ => 0
  | TBindE _ p => ppmax p
  | TShiftE _ t => tpmax t
  end
with ppmax (p : pexp) : nat :=
  match p with
  | PId => 0
  | PAtom n => S n
  | PComp a p => Nat.max (apmax a) (ppmax p)
  | PShift _ p => ppmax p
  end.

Lemma scope_max N :
  (forall e, apmax e <= N -> ascope N e) /\ (forall t, tpmax t <= N -> tscope N t) /\ (forall p, ppmax p <= N -> pscope N p).
Proof.
  apply exp_mind; cbn [apmax tpmax ppmax ascope tscope pscope]; intros; try exact I; try split; auto; try lia;
    match goal with H : _ |- _ => apply H; lia end.
Qed.

