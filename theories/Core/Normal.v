(** * The normaliser's output is in normal form

    Theorem 1 of [docs/normal-forms.md]: whatever the normaliser returns
    satisfies the normal-form conditions [wnf] of [Core/Unique.v].
    Nothing is checked at run time: each operation is shown to keep the
    conditions. *)

From Stdlib Require Import Arith List Lia Bool Sorted.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Unique.
Import ListNotations.

Section Normal.

Variable lenv : list label.
Variable labs : list lexp.
Variable F : list (lexp * lexp).
Hypothesis HF : facts_ok lenv F.
Variable ntm : nat.

Local Notation lden := (lden lenv).
Local Notation ekey := (ekey lenv).
Local Notation sshape := (sshape lenv labs).
Local Notation eshape := (eshape lenv labs).
Local Notation tnf := (tnf lenv labs).
Local Notation snf := (snf lenv labs).
Local Notation wnf := (wnf lenv labs).
Local Notation rnf := (rnf lenv labs).
Local Notation sren := (sren labs).
Local Notation lok := (lok lenv labs).

Definition ssorted (es : list (lexp * list ntgt * nat)) : Prop :=
  StronglySorted (fun e e' => olabel_lt (ekey e) (ekey e')) es.

Definition known (h : lexp) (e : lexp * list ntgt * nat) : Prop :=
  exists c, lcmp F h (fst (fst e)) = Some c /\ c <> Eq.

Lemma ekey_eq e : ekey e = lden (fst (fst e)).
Proof. destruct e as [[h xs] m]; reflexivity. Qed.

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

Lemma sset_shape nm h ts m s s' : sset F h ts m s = Some s' -> sshape nm s -> In h labs -> (nm = true -> lden h <> None) ->
  sshape nm s'
  /\ (forall e, In e (sents s') -> In e (sents s) \/ fst (fst e) = h)
  /\ (forall t, In t (stgts s') -> In t (stgts s) \/ In t (tl_list ts))
  /\ (tl_list ts = [] -> m = 0 -> forall e, In e (sents s') -> In e (sents s)).
Proof.
  unfold sset; intros E [Hs Ho] Hh Hnm.
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
      cbn [Unique.eshape]; rewrite tl_list_of; refine (conj Hh (conj Htr (conj _ Hnm))).
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
    destruct (sset_shape false h (tl_of xs) m s0 s E Hs0 (Hl h xs m (or_introl eq_refl)) ltac:(discriminate))
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

Lemma tcat_list a b : tl_list (tcat a b) = tl_list a ++ tl_list b.
Proof. induction a as [|t r IH] using tlist_spine; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma tskip_in n ts t : In t (tl_list (tskip n ts)) -> In t (tl_list ts).
Proof.
  revert ts; induction n as [|n IH]; intros [|t0 r] H; cbn [tskip] in H; try exact H.
  cbn [tl_list In]; right; apply (IH r), H.
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
    destruct (sset_shape false _ _ _ _ _ E Hs0 (Hl h _ m (or_introl eq_refl)) ltac:(discriminate)) as [Hs [_ [Ht _]]].
    split; [exact Hs|]; intros t Hin; destruct (Ht t Hin) as [Hin'|Hin'].
    + destruct (Ht0 t Hin') as [H'|[t0 [Hi Et]]]; [left; exact H'|].
      right; exists t0; split; [rewrite stgts_cons; apply in_or_app; right; exact Hi|exact Et].
    + rewrite tcat_list in Hin'; apply in_app_or in Hin' as [Hin'|Hin'].
      * destruct (tlapp_in _ _ _ E1 t Hin') as [t0 [Hi Et]]; right; exists t0.
        split; [rewrite stgts_cons; apply in_or_app; left; exact Hi|exact Et].
      * left; apply tskip_in in Hin'.
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
  induction w as [U|s L a w IH] using word_spine; cbn [Unique.rnf pnorm].
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
  - intros h i Hh t' E; destruct (tapp_var_in _ _ _ _ E) as [[j ->]|Hin]; [exact Hh|apply (snf_in _ _ _ HSn _ Hin)].
  - intros u w IH b Hw t'; rewrite tapp_bind; destruct (u <? ntm); [|discriminate].
    destruct (wapp F ntm S w) as [w'|] eqn:E; [|discriminate]; intros H; injection H as <-.
    specialize (IH (match b with None => true | Some _ => false end) Hw w' eq_refl); destruct b; exact IH.
  - intros t [].
  - intros t IHt r IHr t0 [<-|Hin]; [exact IHt|apply IHr, Hin].
  - intros t [].
  - intros h ts IHts m r IHr t Hin; rewrite stgts_cons in Hin; apply in_app_or in Hin as [Hin|Hin];
      [apply IHts, Hin|apply IHr, Hin].
  - intros U IH nm [Hs Hn] w'; rewrite wapp_end; destruct (sdistb F U); [|discriminate].
    destruct (sgo F ntm S U) as [U'|] eqn:E; [|discriminate]; intros H; injection H as <-.
    destruct (sgo_spec _ _ _ E HS (sshape_labs _ _ Hs)) as [Hs' Ht'].
    assert (Hn' : snf U').
    { apply snf_iff; intros t Ht; destruct (Ht' t Ht) as [Hin|[t0 [Hi Et]]];
        [apply (snf_in _ _ _ HSn _ Hin)|apply (IH t0 Hi (snf_in _ _ _ Hn _ Hi) t Et)]. }
    destruct nm; cbn [pnorm Unique.wnf].
    + destruct (sdrop_none_shape _ Hs') as [Hs'' Ht'']; split; [exact Hs''|].
      apply snf_iff; intros t Ht; apply (snf_in _ _ _ Hn'), Ht'', Ht.
    + split; assumption.
  - intros U IHs L a w IHw nm [Hs [Hn [Ha Hr]]] w'; rewrite wapp_atom; destruct (sdistb F U); [|discriminate].
    destruct (sgo F ntm S U) as [U'|] eqn:E; [|discriminate]; intros H; injection H as <-.
    destruct (sgo_spec _ _ _ E HS (sshape_labs _ _ Hs)) as [Hs' Ht'].
    assert (Hn' : snf U').
    { apply snf_iff; intros t Ht; destruct (Ht' t Ht) as [Hin|[t0 [Hi Et]]];
        [apply (snf_in _ _ _ HSn _ Hin)|apply (IHs t0 Hi (snf_in _ _ _ Hn _ Hi) t Et)]. }
    destruct nm; cbn [pnorm Unique.wnf]; [rewrite (pnorm_rnf w Hr)|]; (split; [exact Hs'|split; [exact Hn'|split; [exact Ha|exact Hr]]]).
Qed.

End CompNormal.

Lemma scomp_normal A Q R : scomp F ntm A Q = Some R -> sshape false A -> snf A -> sshape false Q -> snf Q ->
  sshape false R /\ snf R.
Proof.
  unfold scomp; destruct (sdistb F A && sdistb F Q); [|discriminate]; intros E HA HAn HQ HQn.
  destruct (sgo_spec _ _ _ E HA (sshape_labs _ _ HQ)) as [Hs Ht]; split; [exact Hs|].
  apply snf_iff; intros t Hin; destruct (Ht t Hin) as [H|[t0 [Hi Et]]]; [apply (snf_in _ _ _ HAn _ H)|].
  apply (proj1 (proj2 (proj2 (comp_normal A HA HAn))) Q t0 Hi (snf_in _ _ _ HQn _ Hi) t Et).
Qed.

Lemma scomp_ren A Q R : scomp F ntm A Q = Some R -> sshape false A -> sren A -> sshape false Q -> sren Q ->
  sshape false R /\ sren R.
Proof.
  unfold scomp; destruct (sdistb F A && sdistb F Q); [|discriminate]; intros E HA HAr HQ HQr.
  destruct (sgo_spec _ _ _ E HA (sshape_labs _ _ HQ)) as [Hs Ht]; split; [exact Hs|].
  unfold Unique.sren in *; rewrite Forall_forall in HAr, HQr |- *; intros t Hin.
  destruct (Ht t Hin) as [H|[t0 [Hi Et]]]; [apply HAr, H|]; pose proof (HQr _ Hi) as H0.
  destruct t0 as [h i|]; [|contradiction].
  destruct (tapp_var_in _ _ _ _ Et) as [[j ->]|H]; [exact H0|apply HAr, H].
Qed.

Lemma wcons_normal S w w' : wcons F ntm S w = Some w' -> sshape false S -> snf S -> wnf false w -> wnf false w'.
Proof.
  unfold wcons; destruct (sdistb F S); [|discriminate]; intros E HS HSn Hw.
  exact (proj2 (proj2 (proj2 (comp_normal S HS HSn))) w false Hw w' E).
Qed.

End Normal.
