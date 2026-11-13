(** * The layered fold returns normal segments, and its tree is normal

    Every step of the word [Layered.fold] returns is a canonical segment
    or an atom with a canonical list of lifts, so the word multiplied out
    ([expand]) satisfies the normal-form conditions [wnf] of [Unique].
    With uniqueness of normal forms this makes the decision of [LEval]
    complete whenever it gets to compare the trees. *)

From Stdlib Require Import Arith List Lia Bool Sorted.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Unique Normal Layered LayeredUnique.
Import ListNotations.

Section LNormal.

Variable lenv : list label.
Variable labs : list lexp.
Variable npa : nat.
Variable F : order.
Hypothesis HF : facts_ok lenv F.
Variable ntm : nat.
Hypothesis Hnone : In LNone labs.

Local Notation lden := (lden lenv).
Local Notation sshape := (sshape lenv labs).
Local Notation tnf := (tnf lenv labs npa).
Local Notation snf := (snf lenv labs npa).
Local Notation wnf := (wnf lenv labs npa).
Local Notation bok := (bok npa).
Local Notation rnf := (rnf lenv labs).
Local Notation sren := (sren labs).
Local Notation lok := (lok lenv labs).

Definition segN (s : seg) : Prop := sshape false s /\ snf s.

Definition stepN (x : lstep) : Prop :=
  match x with
  | LS s => segN s
  | LA L a => wnf false (WAtom SNil L a (WEnd SNil))
  end.

Definition lwnf (l : lword) : Prop := Forall stepN l.

Definition nok (s : option seg) : Prop := forall s0, s = Some s0 -> segN s0.

Lemma segN_nil : segN SNil.
Proof. split; [split; constructor|exact I]. Qed.

Lemma shsegN h k : In h labs -> k <> 0 -> segN (shseg h k).
Proof.
  intros Hh Hk; split; [split|split; exact I].
  - constructor; constructor.
  - constructor; [|constructor]; cbn [Unique.eshape].
    split; [exact Hh|split; [exact I|split; [right; exact Hk|intros E; discriminate E]]].
Qed.

Lemma nok_some s : segN s -> nok (Some s).
Proof. intros H s0 E; injection E as <-; exact H. Qed.

Lemma idts_tgts n : forall i t, In t (tl_list (idts i n)) -> exists j, t = NVar LNone j.
Proof.
  induction n as [|n IH]; intros i t; cbn; [intros []|].
  intros [<-|H]; [exists i; reflexivity|exact (IH _ _ H)].
Qed.

Lemma slifts_normal d s s' : segN s -> slifts F ntm d s = Some s' -> segN s'.
Proof.
  intros [Hs Hn]; unfold slifts; destruct d as [|d0]; [intros H; injection H as <-; split; assumption|].
  set (d := S d0).
  destruct (scomp F ntm (shseg LNone d) s) as [s1|] eqn:E; [|discriminate].
  destruct (shsegN LNone d Hnone ltac:(discriminate)) as [Hsh Hshn].
  destruct (scomp_normal lenv labs npa F HF ntm _ _ _ E Hsh Hshn Hs Hn) as [Hs1 Hn1].
  destruct (sfind F LNone s1) as [e|] eqn:Ef; [|discriminate]; destruct (ofe e) as [ts m] eqn:Eo; intros H.
  destruct (sset_shape lenv labs F HF false _ _ _ _ _ H Hs1 (or_introl Hnone) ltac:(discriminate)) as [Hs' [_ [Ht _]]].
  split; [exact Hs'|]; apply snf_iff; intros t Hin; destruct (Ht t Hin) as [Hi|Hi]; [exact (snf_in _ _ _ _ Hn1 _ Hi)|].
  rewrite tcat_list in Hi; apply in_app_or in Hi as [Hi|Hi].
  - destruct (idts_tgts _ _ _ Hi) as [j ->]; exact Hnone.
  - apply (sfind_sound lenv F HF) in Ef; destruct e as [[ts0 m0]|]; cbn [ofe] in Eo; injection Eo as <- <-; [|destruct Hi].
    exact (snf_in _ _ _ _ Hn1 _ (sget_tgts _ _ s1 _ _ (eq_sym Ef) _ Hi)).
Qed.

Lemma nok_slift h s : In h labs -> nok s -> nok (obind s (slift F ntm h)).
Proof.
  intros Hh H s0; destruct s as [s1|]; [|discriminate]; cbn [obind]; intros E.
  destruct (H s1 eq_refl) as [A B]; exact (slift_normal lenv labs npa F HF ntm _ _ _ E A B Hh).
Qed.

Lemma nok_slifts d s : nok s -> nok (obind s (slifts F ntm d)).
Proof.
  intros H s0; destruct s as [s1|]; [|discriminate]; cbn [obind]; intros E.
  exact (slifts_normal d s1 s0 (H s1 eq_refl) E).
Qed.

Lemma nok_glifts G : incl G labs -> forall s, nok s -> nok (obind s (glifts F ntm G)).
Proof.
  induction G as [|g G IH]; intros HG s H.
  - intros s0 E; destruct s as [s1|]; [|discriminate]; injection E as <-; exact (H s1 eq_refl).
  - intros s0 E; destruct s as [s1|]; [|discriminate]; cbn [obind glifts] in E.
    refine (IH (fun x Hx => HG x (or_intror Hx)) (slift F ntm g s1) _ s0 E).
    exact (nok_slift g (Some s1) (HG g (or_introl eq_refl)) H).
Qed.

Lemma nok_front h t s : In h labs -> tnf t -> segN s -> nok (sfront F h t s).
Proof.
  intros Hh Ht [Hs Hn] s0 E; destruct (sfront_spec lenv labs F HF _ _ _ _ E Hs Hh) as [A B]; split; [exact A|].
  apply snf_iff; intros t' Hin; destruct (B t' Hin) as [->|Hi]; [exact Ht|exact (snf_in _ _ _ _ Hn _ Hi)].
Qed.

Lemma nok_entry h t : In h labs -> tnf t -> nok (entry F h t).
Proof. intros Hh Ht; exact (nok_front h t SNil Hh Ht segN_nil). Qed.

Lemma nok_close h : In h labs -> nok (close_seg F h).
Proof. intros Hh; exact (nok_front h (NVar LNone 0) _ Hh Hnone (shsegN LNone 1 Hnone ltac:(discriminate))). Qed.

Lemma nok_open h : In h labs -> nok (open_seg F h).
Proof. intros Hh; exact (nok_front LNone (NVar h 0) _ Hnone Hh (shsegN h 1 Hh ltac:(discriminate))). Qed.

Lemma lpreN U r : segN U -> lwnf r -> lwnf (lpre U ++ r).
Proof. intros HU Hr; destruct U; [exact Hr|constructor; assumption]. Qed.

Lemma atomN L a : lok L -> stepN (LA L a).
Proof.
  intros HL; cbn [stepN Unique.wnf Unique.rnf].
  refine (conj (proj1 segN_nil) (conj I (conj (conj HL (conj (lpos_nil lenv L) _)) (conj (proj1 segN_nil) _)))).
  - intros E; discriminate E.
  - constructor.
Qed.

Lemma cons_seg_normal K : forall s K', segN s -> lwnf K -> cons_seg F ntm s K = Some K' -> lwnf K'.
Proof.
  induction K as [|[s1|L a] K IH]; intros s K' Hs HK; cbn [cons_seg].
  - intros H; injection H as <-; rewrite <- (app_nil_r (lpre s)); exact (lpreN s [] Hs HK).
  - inversion HK as [|? ? H1 HK']; subst.
    destruct (negb (has_terms s) || (bound_only s1 && no_atoms s)).
    + destruct (scomp F ntm s1 s) as [s'|] eqn:E; [|discriminate].
      pose proof (scomp_normal lenv labs npa F HF ntm _ _ _ E (proj1 H1) (proj2 H1) (proj1 Hs) (proj2 Hs)) as Hs'.
      destruct s'; intros H; injection H as <-; [exact HK'|constructor; [exact Hs'|exact HK']].
    + intros H; injection H as <-; constructor; [exact Hs|exact HK].
  - inversion HK as [|? ? H1 HK']; subst.
    destruct (has_terms s); [intros H; injection H as <-; constructor; [exact Hs|exact HK]|].
    destruct (wcomp F ntm (WAtom SNil L a (WEnd SNil)) (WEnd s)) as [[s0|s' L' a' [U|s2 L2 a2 w2|s5 w5]|s4 w4]|] eqn:E;
      [intros H; discriminate H| |intros H; discriminate H|intros H; discriminate H|intros H; discriminate H|intros H; discriminate H].
    pose proof (wcomp_normal lenv labs npa F HF ntm (WAtom SNil L a (WEnd SNil)) (WEnd s) _ H1 Hs E) as Hw.
    destruct Hw as [A [B [[C _] [D D']]]].
    destruct (cons_seg F ntm s' K) as [K''|] eqn:E2; [|discriminate]; cbn [obind]; intros H; injection H as <-.
    apply lpreN; [split; [exact D|exact (sren_snf lenv labs npa _ D')]|].
    constructor; [exact (atomN L' a' C)|exact (IH s' K'' (conj A B) HK' E2)].
Qed.

Lemma cons_lifted_normal d s K K' : nok s -> lwnf K -> cons_lifted F ntm d s K = Some K' -> lwnf K'.
Proof.
  intros Hs HK; unfold cons_lifted; destruct s as [s0|]; [|discriminate]; cbn [obind].
  destruct (slifts F ntm d s0) as [s1|] eqn:E; [|discriminate]; cbn [obind].
  exact (cons_seg_normal K s1 K' (slifts_normal d s0 s1 (Hs s0 eq_refl) E) HK).
Qed.

Definition keeps (k : nat -> lword -> option lword) : Prop :=
  forall d K K', lwnf K -> k d K = Some K' -> lwnf K'.

Lemma under_normal G : incl G labs -> forall d k K K', keeps k -> lwnf K -> under F ntm G d k K = Some K' -> lwnf K'.
Proof.
  induction G as [|g G IH]; intros HG d k K K' Hk HK; cbn [under]; [apply Hk, HK|].
  apply (IH (fun x Hx => HG x (or_intror Hx))); [|exact HK].
  intros d' K0 K1 HK0.
  destruct (cons_lifted F ntm d' (open_seg F g) K0) as [Ka|] eqn:Ea; [|discriminate]; cbn [obind].
  destruct (k (S d') Ka) as [Kb|] eqn:Eb; [|discriminate]; cbn [obind]; intros Ec.
  pose proof (cons_lifted_normal _ _ _ _ (nok_open g (HG g (or_introl eq_refl))) HK0 Ea) as Ha.
  exact (cons_lifted_normal _ _ _ _ (nok_close g (HG g (or_introl eq_refl))) (Hk _ _ _ Ha Eb) Ec).
Qed.

Lemma bouter_normal d w h G g next K K' : In h labs -> In g labs -> incl G labs -> keeps next -> lwnf K ->
  bouter F ntm d w h G g next K = Some K' -> lwnf K'.
Proof.
  intros Hh Hg HG Hn HK; unfold bouter.
  destruct (cons_lifted F ntm (d + w) (obind (entry F LNone (NVar g 0)) (glifts F ntm G)) K) as [K1|] eqn:E1; [|discriminate].
  cbn [obind].
  destruct (cons_lifted F ntm (d + w + 1) (glifts F ntm G (shseg g 1)) K1) as [K2|] eqn:E2; [|discriminate]; cbn [obind].
  destruct (next (w + 1) K2) as [K3|] eqn:E3; [|discriminate]; cbn [obind].
  pose proof (cons_lifted_normal _ _ _ _ (nok_glifts G HG _ (nok_entry LNone (NVar g 0) Hnone Hg)) HK E1) as H1.
  pose proof (cons_lifted_normal _ _ _ _
                (nok_glifts G HG (Some (shseg g 1)) (nok_some _ (shsegN g 1 Hg ltac:(discriminate)))) H1 E2) as H2.
  pose proof (Hn _ _ _ H2 E3) as H3.
  destruct (is_bound g); [intros H; injection H as <-; exact H3|].
  apply cons_lifted_normal; [|exact H3].
  apply (nok_slift h _ Hh), nok_slifts, (nok_glifts G HG), nok_close, Hg.
Qed.

Lemma tvar_labs t g i : Layered.tvar F t = Some (g, i) -> In g (tlabs t).
Proof.
  revert g i; induction t as [g0 i0|u p|h t IH]; intros g i; cbn [Layered.tvar tlabs].
  - intros H; injection H as <- <-; left; reflexivity.
  - discriminate.
  - destruct (Layered.tvar F t) as [[g1 i1]|]; [|discriminate].
    destruct (lcmp F h g1) as [[| |]|]; try discriminate; intros H; injection H as <- <-; right; exact (IH _ _ eq_refl).
Qed.

Lemma expand_normal l : forall w, lwnf l -> expand F ntm l = Some w -> wnf false w.
Proof.
  induction l as [|[s|L a] r IH]; intros w Hl; cbn [expand].
  - intros H; injection H as <-; exact segN_nil.
  - inversion Hl as [|? ? Hs Hr]; subst.
    destruct (expand F ntm r) as [w0|] eqn:E; [|discriminate]; cbn [obind]; intros H.
    exact (wcomp_normal lenv labs npa F HF ntm w0 (WEnd s) w (IH w0 Hr eq_refl) Hs H).
  - inversion Hl as [|? ? Hs Hr]; subst.
    destruct (expand F ntm r) as [w0|] eqn:E; [|discriminate]; cbn [obind]; intros H.
    exact (wcomp_normal lenv labs npa F HF ntm w0 (WAtom SNil L a (WEnd SNil)) w (IH w0 Hr eq_refl) Hs H).
Qed.

Lemma simple_tnf t tg : incl (tlabs t) labs -> simple F ntm t = Some tg -> tnf tg.
Proof.
  intros Hl; destruct t as [g i|u p|h t']; cbn [simple].
  - intros H; injection H as <-; apply Hl; left; reflexivity.
  - destruct p; try discriminate; destruct (u <? ntm); [|discriminate]; intros H; injection H as <-.
    split; [exact I|split; [split; constructor|exact I]].
  - destruct (Layered.tvar F (TShiftE h t')) as [[g i]|] eqn:Ev; [|discriminate]; intros H; injection H as <-.
    exact (Hl _ (tvar_labs _ _ _ Ev)).
Qed.

Lemma spine_normal e : forall s b, incl (alabs e) labs -> spine F ntm e = Some (s, b) -> segN s.
Proof.
  induction e as [|n|a1 IH1 a2 IH2|g a IH|h t a IH|g a IH]; intros s b Hl; cbn [spine]; try discriminate.
  - intros H; injection H as <- <-; exact segN_nil.
  - destruct (simple F ntm t) as [tg|] eqn:Et; [|discriminate].
    destruct (spine F ntm a) as [[s0 b0]|] eqn:Ea; [|discriminate].
    assert (Hh : In h labs) by (apply Hl; left; reflexivity).
    pose proof (simple_tnf t tg (fun x Hx => Hl x (or_intror (in_or_app _ _ _ (or_introl Hx)))) Et) as Htg.
    pose proof (IH s0 b0 (fun x Hx => Hl x (or_intror (in_or_app _ _ _ (or_intror Hx)))) eq_refl) as H0.
    match goal with |- (if ?X then _ else _) = _ -> _ => destruct X eqn:Eb end.
    + apply andb_true_iff in Eb as [_ Eb]; intros H; injection H as <- <-.
      destruct H0 as [[Hso Hsh] Hnf]; split; [split|].
      * change (sents (SEnt h (TCons tg TNil) 0 s0)) with ((h, [tg], 0) :: sents s0).
        constructor; [exact Hso|].
        destruct s0 as [|g ts m r]; [constructor|].
        destruct (lcmp F h g) as [[| |]|] eqn:Ec; try discriminate.
        pose proof (lcmp_sound lenv F HF _ _ _ Ec) as Hlt; cbn in Hlt.
        change (sents (SEnt g ts m r)) with ((g, tl_list ts, m) :: sents r) in Hso |- *.
        inversion Hso as [|? ? Hso' Hfa]; subst.
        constructor; [exact Hlt|].
        eapply Forall_impl; [|exact Hfa]; intros e He; exact (olabel_lt_trans _ _ _ Hlt He).
      * change (sents (SEnt h (TCons tg TNil) 0 s0)) with ((h, [tg], 0) :: sents s0).
        constructor; [|exact Hsh].
        split; [exact Hh|split; [unfold trimmed; cbn; destruct tg; exact I|split; [left; discriminate|discriminate]]].
      * apply snf_iff; intros t' Ht'; rewrite stgts_cons in Ht'; cbn in Ht'.
        destruct Ht' as [<-|Ht']; [exact Htg|exact (snf_in _ _ _ _ Hnf _ Ht')].
    + destruct (sfront F h tg s0) as [s'|] eqn:Ef; [|discriminate]; cbn [option_map]; intros H; injection H as <- <-.
      exact (nok_front h tg s0 Hh Htg H0 s' Ef).
Qed.

Theorem fold_normal :
  (forall e, incl (alabs e) labs -> ascope npa e ->
     (forall d K K', lwnf K -> fold F ntm d e K = Some K' -> lwnf K')
     /\ (forall d w h G inner K K', In h labs -> incl G labs -> keeps inner -> lwnf K ->
           byp F ntm d w h G e inner K = Some K' -> lwnf K'))
  /\ (forall t, incl (tlabs t) labs -> tscope npa t ->
        forall d G h K K', In h labs -> incl G labs -> lwnf K -> centry F ntm d G h t K = Some K' -> lwnf K')
  /\ (forall p, incl (plabs p) labs -> pscope npa p ->
        (forall d w h u K K', In h labs -> lwnf K -> cterm F ntm d w h u p K = Some K' -> lwnf K')
        /\ (forall w b, ptree F ntm p = Some (w, b) -> bok b /\ wnf (match b with None => true | Some _ => false end) w)).
Proof.
  apply exp_mind.
  - (* AId *) intros _ _; split.
    + intros d K K' HK H; injection H as <-; exact HK.
    + intros d w h G inner K K' _ _ Hi HK H; exact (Hi _ _ _ HK H).
  - (* AAtom *) intros n _ _; split.
    + intros d K K' HK H; injection H as <-; constructor; [|exact HK].
      apply atomN; destruct d; [split; constructor|].
      split; [constructor; constructor|constructor; [split; [exact Hnone|discriminate]|constructor]].
    + intros d w h G inner K K' _ _ _ _ H; discriminate H.
  - (* ACompose *) intros a IHa b IHb Hl [Sa Sb].
    destruct (IHa (fun x Hx => Hl x (in_or_app _ _ _ (or_introl Hx))) Sa) as [Fa Ba].
    destruct (IHb (fun x Hx => Hl x (in_or_app _ _ _ (or_intror Hx))) Sb) as [Fb Bb]; split.
    + intros d K K' HK; rewrite fold_compose.
      destruct (fold F ntm d a K) as [K1|] eqn:E1; [|discriminate]; cbn [obind]; intros H.
      exact (Fb _ _ _ (Fa _ _ _ HK E1) H).
    + intros d w h G inner K K' Hh HG Hi HK H; change (byp F ntm d w h G a (fun w' K0 => byp F ntm d w' h G b inner K0) K = Some K') in H.
      refine (Ba d w h G _ K K' Hh HG _ HK H); intros w' K0 K1 HK0 H0; exact (Bb d w' h G inner K0 K1 Hh HG Hi HK0 H0).
  - (* AOuter *) intros g a IHa Hl Sa.
    assert (Hg : In g labs) by (apply Hl; left; reflexivity).
    destruct (IHa (fun x Hx => Hl x (or_intror Hx)) Sa) as [Fa Ba]; split.
    + intros d K K' HK; rewrite fold_outer.
      destruct (cons_lifted F ntm d (Some (shseg g 1)) K) as [K1|] eqn:E1; [|discriminate]; cbn [obind]; intros H.
      exact (Fa _ _ _ (cons_lifted_normal _ _ _ _ (nok_some _ (shsegN g 1 Hg ltac:(discriminate))) HK E1) H).
    + intros d w h G inner K K' Hh HG Hi HK H; change (bouter F ntm d w h G g (fun w' K0 => byp F ntm d w' h G a inner K0) K = Some K') in H.
      refine (bouter_normal d w h G g _ K K' Hh Hg HG _ HK H); intros w' K0 K1 HK0 H0; exact (Ba d w' h G inner K0 K1 Hh HG Hi HK0 H0).
  - (* AInner *) intros g t IHt a IHa Hl [St Sa].
    assert (Hg : In g labs) by (apply Hl; left; reflexivity).
    pose proof (IHt (fun x Hx => Hl x (or_intror (in_or_app _ _ _ (or_introl Hx)))) St) as Ct.
    destruct (IHa (fun x Hx => Hl x (or_intror (in_or_app _ _ _ (or_intror Hx)))) Sa) as [Fa Ba]; split.
    + intros d K K' HK; rewrite fold_inner.
      destruct (spine F ntm (AInner g t a)) as [[s b]|] eqn:Esp;
        [intros H; exact (cons_lifted_normal _ _ _ _ (nok_some s (spine_normal _ s b Hl Esp)) HK H)|].
      destruct (centry F ntm d [] g t K) as [K1|] eqn:E1; [|discriminate]; cbn [obind].
      pose proof (Ct d [] g K K1 Hg (fun x Hx => match Hx with end) HK E1) as H1.
      destruct (is_bound g); [exact (Fa _ _ _ H1)|].
      destruct (cons_lifted F ntm d (open_seg F g) K1) as [K2|] eqn:E2; [|discriminate]; cbn [obind].
      destruct (fold F ntm (S d) a K2) as [K3|] eqn:E3; [|discriminate]; cbn [obind]; intros H.
      pose proof (cons_lifted_normal _ _ _ _ (nok_open g Hg) H1 E2) as H2.
      exact (cons_lifted_normal _ _ _ _ (nok_close g Hg) (Fa _ _ _ H2 E3) H).
    + intros d w h G inner K K' Hh HG Hi HK; rewrite byp_inner.
      destruct (is_bound g); [discriminate|].
      destruct (centry F ntm (d + w) G g t K) as [K1|] eqn:E1; [|discriminate]; cbn [obind].
      assert (HG' : incl (g :: G) labs) by (intros x [<-|Hx]; [exact Hg|exact (HG x Hx)]).
      destruct (byp F ntm d w h (g :: G) a inner K1) as [K2|] eqn:E2; [|discriminate]; cbn [obind]; intros H.
      pose proof (Ct (d + w) G g K K1 Hg HG HK E1) as H1.
      pose proof (Ba d w h (g :: G) inner K1 K2 Hh HG' Hi H1 E2) as H2.
      refine (cons_lifted_normal _ _ _ _ _ H2 H).
      apply (nok_slift h _ Hh), nok_slifts, (nok_glifts G HG (Some (shseg g 1))), nok_some, shsegN; [exact Hg|discriminate].
  - (* ALift *) intros g a IHa Hl Sa.
    assert (Hg : In g labs) by (apply Hl; left; reflexivity).
    destruct (IHa (fun x Hx => Hl x (or_intror Hx)) Sa) as [Fa Ba]; split.
    + intros d K K' HK; rewrite fold_lift.
      destruct (is_bound g); [exact (Fa _ _ _ HK)|].
      destruct (cons_lifted F ntm d (open_seg F g) K) as [K2|] eqn:E2; [|discriminate]; cbn [obind].
      destruct (fold F ntm (S d) a K2) as [K3|] eqn:E3; [|discriminate]; cbn [obind]; intros H.
      pose proof (cons_lifted_normal _ _ _ _ (nok_open g Hg) HK E2) as H2.
      exact (cons_lifted_normal _ _ _ _ (nok_close g Hg) (Fa _ _ _ H2 E3) H).
    + intros d w h G inner K K' Hh HG Hi HK; rewrite byp_lift.
      destruct (is_bound g); [discriminate|].
      assert (HG' : incl (g :: G) labs) by (intros x [<-|Hx]; [exact Hg|exact (HG x Hx)]).
      exact (Ba d w h (g :: G) inner K K' Hh HG' Hi HK).
  - (* TVarE *) intros g i Hl _ d G h K K' Hh HG HK H; rewrite centry_var in H.
    refine (cons_lifted_normal _ _ _ _ (nok_glifts G HG _ (nok_entry h (NVar g i) Hh _)) HK H).
    apply Hl; left; reflexivity.
  - (* TBindE *) intros u p IHp Hl Sp d G h K K' Hh HG HK; rewrite centry_bind.
    destruct (IHp Hl Sp) as [Cp Tp].
    destruct (u <? ntm); [|discriminate].
    destruct (phard p).
    + destruct (ptree F ntm p) as [[w b]|] eqn:Ep; [|discriminate]; intros H.
      exact (cons_lifted_normal _ _ _ _ (nok_glifts G HG _ (nok_entry h (NBind u w b) Hh (Tp w b eq_refl))) HK H).
    + intros H; refine (under_normal G HG d _ K K' _ HK H); intros d' K0 K1 HK0 H0; exact (Cp d' 0 h u K0 K1 Hh HK0 H0).
  - (* TShiftE *) intros g t _ Hl _ d G h K K' Hh HG HK H; rewrite centry_shift in H.
    destruct (Layered.tvar F (TShiftE g t)) as [[g' i]|] eqn:Ev; [|discriminate H].
    refine (cons_lifted_normal _ _ _ _ (nok_glifts G HG _ (nok_entry h (NVar g' i) Hh _)) HK H).
    exact (Hl _ (tvar_labs _ _ _ Ev)).
  - (* PId *) intros _ _; split.
    + intros d w h u K K' Hh HK H; rewrite cterm_id in H.
      refine (cons_lifted_normal _ _ _ _ (nok_entry h _ Hh _) HK H); split; [exact I|split; [split; constructor|exact I]].
    + intros w b H; change (Some (WEnd SNil, @None nat) = Some (w, b)) in H; injection H as <- <-.
      split; [exact I|split; [split; constructor|exact I]].
  - (* PAtom *) intros n _ Sn; split.
    + intros d w h u K K' Hh HK H; rewrite cterm_atom in H.
      refine (cons_lifted_normal _ _ _ _ (nok_entry h _ Hh _) HK H); split; [exact Sn|].
      destruct w; [exact segN_nil|exact (shsegN LNone (S w) Hnone ltac:(discriminate))].
    + intros w b H; change (Some (WEnd SNil, Some n) = Some (w, b)) in H; injection H as <- <-.
      split; [exact Sn|exact segN_nil].
  - (* PComp *) intros a IHa p IHp Hl [Sa Sp].
    destruct (IHa (fun x Hx => Hl x (in_or_app _ _ _ (or_introl Hx))) Sa) as [Fa Ba].
    destruct (IHp (fun x Hx => Hl x (in_or_app _ _ _ (or_intror Hx))) Sp) as [Cp Tp]; split.
    + intros d w h u K K' Hh HK H; change (byp F ntm d w h [] a (fun w' K0 => cterm F ntm d w' h u p K0) K = Some K') in H.
      refine (Ba d w h [] _ K K' Hh (fun x Hx => match Hx with end) _ HK H); intros w' K0 K1 HK0 H0; exact (Cp d w' h u K0 K1 Hh HK0 H0).
    + intros w b; rewrite ptree_comp.
      destruct (ptree F ntm p) as [[w' b']|] eqn:Ep; [|discriminate].
      destruct (fold F ntm 0 a []) as [l|] eqn:El; [|discriminate].
      destruct (expand F ntm l) as [wa|] eqn:Ex; [|discriminate].
      destruct (wcomp F ntm wa w') as [w0|] eqn:Ec; [|discriminate]; cbn [obind].
      destruct (pnormw F ntm b' w0) as [w1|] eqn:En; [|discriminate]; intros H; injection H as <- <-.
      destruct (Tp w' b' eq_refl) as [Hb Hw'].
      pose proof (expand_normal l wa (Fa 0 [] l (Forall_nil _) El) Ex) as Hwa.
      pose proof (wcomp_normal lenv labs npa F HF ntm wa w' w0 Hwa (wnf_false lenv labs npa _ _ Hw') Ec) as Hw0.
      split; [exact Hb|exact (pnormw_normal lenv labs npa F HF ntm _ _ _ Hw0 En)].
  - (* PShift *) intros g p IHp Hl Sp.
    assert (Hg : In g labs) by (apply Hl; left; reflexivity).
    destruct (IHp (fun x Hx => Hl x (or_intror Hx)) Sp) as [Cp Tp]; split.
    + intros d w h u K K' Hh HK H; change (bouter F ntm d w h [] g (fun w' K0 => cterm F ntm d w' h u p K0) K = Some K') in H.
      refine (bouter_normal d w h [] g _ K K' Hh Hg (fun x Hx => match Hx with end) _ HK H); intros w' K0 K1 HK0 H0; exact (Cp d w' h u K0 K1 Hh HK0 H0).
    + intros w b; rewrite ptree_shift.
      destruct (ptree F ntm p) as [[w' b']|] eqn:Ep; [|discriminate].
      destruct (wcomp F ntm (WEnd (shseg g 1)) w') as [w0|] eqn:Ec; [|discriminate]; cbn [obind].
      destruct (pnormw F ntm b' w0) as [w1|] eqn:En; [|discriminate]; intros H; injection H as <- <-.
      destruct (Tp w' b' eq_refl) as [Hb Hw'].
      pose proof (wcomp_normal lenv labs npa F HF ntm (WEnd (shseg g 1)) w' w0 (shsegN g 1 Hg ltac:(discriminate)) (wnf_false lenv labs npa _ _ Hw') Ec) as Hw0.
      split; [exact Hb|exact (pnormw_normal lenv labs npa F HF ntm _ _ _ Hw0 En)].
Qed.

Theorem lnorm_normal e l : incl (alabs e) labs -> ascope npa e -> lnorm F ntm e = Some l -> lwnf l.
Proof. intros Hl Sc H; exact (proj1 (proj1 fold_normal e Hl Sc) 0 [] l (Forall_nil _) H). Qed.

End LNormal.
