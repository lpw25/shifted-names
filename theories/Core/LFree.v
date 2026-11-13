(** * Following a variable through a layered word, in the free model

    [dfollow l h i] follows the variable [h₍ᵢ₎] through the word [l] to
    what it reaches: a variable at the end ([DV]), a term of a segment
    ([DT t d], [d] the length of the rest after that segment), or an
    atom it is not lifted around ([DS a g j d], stuck as [g₍ⱼ₎], [d] the
    length of the rest after the atom).  [dfollow_sound] says what that
    is in the free model ([LayeredUnique.R]).

    The canonical word ([CanonF]) compares results and payloads by what
    [dfollow] finds. *)

From Stdlib Require Import Arith List Lia Bool.
From ShiftedNames.Core Require Import Label Var Adjustment Normalise Unique Layered LayeredUnique Order.
Import ListNotations.

Inductive desc : Type :=
| DV (h : lexp) (i : nat)
| DT (t : ntgt) (d : nat)
| DS (a : nat) (h : lexp) (j d : nat).

(** The last [d] steps of a word. *)
Definition suf (l : lword) (d : nat) : lword := skipn (List.length l - d) l.

Lemma suf_all l : suf l (List.length l) = l.
Proof. unfold suf; rewrite Nat.sub_diag; reflexivity. Qed.

Lemma suf_cons x r d : d <= List.length r -> suf (x :: r) d = suf r d.
Proof.
  intros Hd; unfold suf; cbn [List.length]; replace (S (List.length r) - d) with (S (List.length r - d)) by lia.
  reflexivity.
Qed.

Lemma suf_len l d : d <= List.length l -> List.length (suf l d) = d.
Proof. intros Hd; unfold suf; rewrite length_skipn; lia. Qed.

Lemma suf_suf l d e : e <= d -> d <= List.length l -> suf (suf l d) e = suf l e.
Proof.
  intros He Hd; unfold suf at 1; rewrite (suf_len l d Hd); unfold suf; rewrite skipn_skipn; f_equal; lia.
Qed.

Section Follow.

Variable F : order.

Fixpoint dfollow (l : lword) (h : lexp) (i : nat) : option desc :=
  match l with
  | [] => Some (DV h i)
  | LS s :: r =>
      match seg_tgt F s h i with
      | Some (NVar g j) => dfollow r g j
      | Some t => Some (DT t (List.length r))
      | None => None
      end
  | LA L a :: r =>
      match lcnt F h L with
      | Some c => if i <? c then dfollow r h i else Some (DS a h (i - c) (List.length r))
      | None => None
      end
  end.

End Follow.

Section Sound.

Variable lenv : list label.
Variable F : order.
Hypothesis HF : facts_ok lenv F.

Local Notation lden := (lden lenv).
Local Notation R := (R lenv).
Local Notation fs := (fs lenv).
Local Notation ft := (ft lenv).

Lemma R_seg s r v : R (LS s :: r) v = fs s (R r) v.
Proof. reflexivity. Qed.

Lemma R_atom L a r v : R (LA L a :: r) v = latom lenv L a (R r) v.
Proof. reflexivity. Qed.

Lemma seg_tgt_free s h i t K : seg_tgt F s h i = Some t -> fs s K (mk_rvar (lden h) i) = ft t K.
Proof.
  unfold seg_tgt; destruct (sfind F h s) as [e|] eqn:Ef; [|discriminate].
  apply (sfind_sound lenv F HF) in Ef; rewrite (fs_get lenv); unfold fget; cbn [v_label v_index]; rewrite <- Ef.
  destruct e as [[ts m]|]; intros H; injection H as <-; [|reflexivity].
  destruct (Nat.ltb_spec i (tlen ts)) as [Hi|Hi].
  - apply (ftl_lt lenv), Hi.
  - rewrite (ftl_ge lenv) by exact Hi; reflexivity.
Qed.

Lemma seg_tgt_in s h i t : seg_tgt F s h i = Some t -> (exists j, t = NVar h j) \/ In t (stgts s).
Proof.
  unfold seg_tgt; destruct (sfind F h s) as [e|] eqn:Ef; [|discriminate].
  apply (sfind_sound lenv F HF) in Ef.
  destruct e as [[ts m]|]; intros H; injection H as <-; [|left; eexists; reflexivity].
  destruct (Nat.ltb_spec i (tlen ts)) as [Hi|Hi]; [|left; eexists; reflexivity].
  right; apply (sget_tgts lenv _ s ts m (eq_sym Ef)), tnth_in, Hi.
Qed.

Theorem dfollow_sound l : forall h i x, dfollow F l h i = Some x ->
  match x with
  | DV g j => R l (mk_rvar (lden h) i) = FVar (mk_rvar (lden g) j)
  | DT t d =>
      d < List.length l /\ is_term t = true
      /\ exists s, suf l (S d) = LS s :: suf l d /\ In t (stgts s) /\ R l (mk_rvar (lden h) i) = ft t (R (suf l d))
                   /\ exists h' i', seg_tgt F s h' i' = Some t
  | DS a g j d =>
      d < List.length l
      /\ exists L, suf l (S d) = LA L a :: suf l d
                   /\ R l (mk_rvar (lden h) i) = FStuck a (mk_rvar (lden g) j) (fun y => R (suf l d) (shiftL lenv L y))
  end.
Proof.
  induction l as [|[s|L a] r IH]; intros h i x; cbn [dfollow].
  - intros H; injection H as <-; reflexivity.
  - destruct (seg_tgt F s h i) as [t|] eqn:Et; [|discriminate].
    pose proof (seg_tgt_free s h i t (R r) Et) as Ef.
    assert (Hlen : List.length r < List.length (LS s :: r)) by (cbn; lia).
    assert (Hsuf : suf (LS s :: r) (S (List.length r)) = LS s :: suf (LS s :: r) (List.length r)).
    { change (S (List.length r)) with (List.length (LS s :: r)); rewrite suf_all, (suf_cons _ _ _ (le_n _)), suf_all.
      reflexivity. }
    destruct t as [g j|u w b].
    + intros H; specialize (IH g j x H); destruct x as [g' j'|t d|a g' j' d].
      * rewrite R_seg, Ef; exact IH.
      * destruct IH as [Hd [Ht [s' [E1 [E2 [E3 E4]]]]]]; split; [cbn; lia|split; [exact Ht|]].
        exists s'; rewrite !suf_cons by lia; split; [exact E1|split; [exact E2|split; [|exact E4]]].
        rewrite R_seg, Ef; exact E3.
      * destruct IH as [Hd [L [E1 E2]]]; split; [cbn; lia|].
        exists L; rewrite !suf_cons by lia; split; [exact E1|].
        rewrite R_seg, Ef; exact E2.
    + intros H; injection H as <-; split; [exact Hlen|split; [reflexivity|]].
      exists s; rewrite Hsuf; split; [reflexivity|].
      destruct (seg_tgt_in s h i _ Et) as [[j E]|Hin]; [discriminate E|split; [exact Hin|]].
      split; [rewrite (suf_cons _ _ _ (le_n _)), suf_all, R_seg; exact Ef|exists h, i; exact Et].
  - destruct (lcnt F h L) as [c|] eqn:Ec; [|discriminate].
    pose proof (lcnt_sound lenv F HF _ _ _ Ec) as Hc.
    destruct (Nat.ltb_spec i c) as [Hi|Hi].
    + intros H; specialize (IH h i x H).
      assert (Ea : R (LA L a :: r) (mk_rvar (lden h) i) = R r (mk_rvar (lden h) i)).
      { rewrite R_atom; unfold latom; cbn [v_label v_index]; rewrite Hc, (proj2 (Nat.ltb_lt _ _) Hi); reflexivity. }
      destruct x as [g' j'|t d|a' g' j' d].
      * rewrite Ea; exact IH.
      * destruct IH as [Hd [Ht [s' [E1 [E2 [E3 E4]]]]]]; split; [cbn; lia|split; [exact Ht|]].
        exists s'; rewrite !suf_cons by lia; split; [exact E1|split; [exact E2|split; [|exact E4]]]; rewrite Ea; exact E3.
      * destruct IH as [Hd [L' [E1 E2]]]; split; [cbn; lia|].
        exists L'; rewrite !suf_cons by lia; split; [exact E1|]; rewrite Ea; exact E2.
    + intros H; injection H as <-; split; [cbn; lia|].
      exists L; split.
      * change (S (List.length r)) with (List.length (LA L a :: r)); rewrite suf_all, (suf_cons _ _ _ (le_n _)), suf_all.
        reflexivity.
      * rewrite (suf_cons _ _ _ (le_n _)), suf_all, R_atom; unfold latom; cbn [v_label v_index].
        rewrite Hc, (proj2 (Nat.ltb_ge _ _) Hi); reflexivity.
Qed.

End Sound.

(** ** In a word in normal form *)

Section Normal.

Variable lenv : list label.
Variable labs : list lexp.
Variable F : order.
Hypothesis HF : facts_ok lenv F.

Local Notation lden := (lden lenv).
Local Notation R := (R lenv).
Local Notation lnf := (lnf lenv labs gtP).
Local Notation sterm := (sterm lenv).

Lemma seg_tgt_sres s h i t : seg_tgt F s h i = Some t -> sres lenv s (mk_rvar (lden h) i) = tres lenv t.
Proof.
  unfold seg_tgt, sres; cbn [v_label v_index]; destruct (sfind F h s) as [e|] eqn:Ef; [|discriminate].
  apply (sfind_sound lenv F HF) in Ef; rewrite <- Ef.
  destruct e as [[ts m]|]; intros H; injection H as <-; [|reflexivity].
  destruct (tlen ts) as [|n] eqn:En; [cbn; reflexivity|].
  destruct (Nat.ltb_spec i (S n)) as [Hi|Hi]; reflexivity.
Qed.

Lemma term_sterm s h i u w b : seg_tgt F s h i = Some (NBind u w b) -> sterm s.
Proof. intros E; exists (mk_rvar (lden h) i); rewrite (seg_tgt_sres _ _ _ _ E); eexists; reflexivity. Qed.

Lemma natl_suf l : forall d, natl (suf l d) <= natl l.
Proof.
  induction l as [|x r IH]; intros d; [unfold suf; cbn; destruct d; cbn; lia|].
  destruct (Nat.le_gt_cases d (List.length r)) as [Hd|Hd].
  - rewrite suf_cons by exact Hd; pose proof (IH d); destruct x; cbn [natl]; lia.
  - unfold suf; replace (List.length (x :: r) - d) with 0 by (cbn [List.length]; lia); cbn [skipn]; apply le_n.
Qed.

(** The rest of a segment with terms. *)
Definition tpos (K : lword) (d : nat) : Prop :=
  d < List.length K /\ exists s, suf K (S d) = LS s :: suf K d /\ sterm s.

Lemma gtP_deep k k' d d' : deep d k -> deep d' k' -> d' < d -> gtP k k'.
Proof. intros H H' Hlt; left; exists d, d'; auto. Qed.

Lemma tpos_cons x r d : d < List.length r -> tpos (x :: r) d -> tpos r d.
Proof.
  intros Hd [_ [s [E Hs]]]; split; [exact Hd|exists s; split; [|exact Hs]].
  rewrite !suf_cons in E by lia; exact E.
Qed.

(** The payloads of the layers decrease. *)
Lemma tpos_last s r : sterm s -> tpos (LS s :: r) (List.length r).
Proof.
  intros Hs; split; [cbn; lia|exists s; split; [|exact Hs]].
  change (S (List.length r)) with (List.length (LS s :: r)); rewrite suf_all, (suf_cons _ _ _ (le_n _)), suf_all.
  reflexivity.
Qed.

Lemma tpos_head x r : tpos (x :: r) (List.length r) -> exists s, x = LS s /\ sterm s.
Proof.
  intros [_ [s [E Hs]]]; change (S (List.length r)) with (List.length (x :: r)) in E.
  rewrite suf_all in E; injection E as -> _; exists s; auto.
Qed.

Theorem layers_dec K : lnf K -> forall d1 d2, tpos K d1 -> tpos K d2 -> d2 < d1 -> gtP (R (suf K d1)) (R (suf K d2)).
Proof.
  induction K as [|x r IH]; intros HK d1 d2 H1 H2 Hlt; [destruct H1 as [H _]; cbn in H; lia|].
  assert (Hr : lnf r) by (destruct x as [s|L a]; [exact (proj1 (proj2 HK))|exact (proj2 HK)]).
  pose proof (proj1 H1) as Hd1; pose proof (proj1 H2) as Hd2; cbn [List.length] in Hd1, Hd2.
  destruct (Nat.lt_ge_cases d1 (List.length r)) as [Hd1r|Hd1r].
  { rewrite !suf_cons by lia; apply IH; [exact Hr|apply (tpos_cons x); [exact Hd1r|exact H1]| |lia].
    apply (tpos_cons x); [lia|exact H2]. }
  assert (d1 = List.length r) as -> by lia.
  destruct (tpos_head _ _ H1) as [s1 [-> Hs1]].
  rewrite (suf_cons _ _ _ (le_n _)), suf_all, (suf_cons _ _ _ (Nat.lt_le_incl _ _ Hlt)).
  assert (H2r : tpos r d2) by (apply (tpos_cons (LS s1)); [exact Hlt|exact H2]).
  destruct HK as [_ [_ [[_ HS]|[_ [Hren _]]]]]; [|exfalso; exact (sren_noterm lenv labs _ Hren Hs1)].
  assert (Hdeep : forall r2, natl r2 < natl r -> d2 <= List.length r2 -> suf r d2 = suf r2 d2 -> gtP (R r) (R (suf r d2))).
  { intros r2 Hn Hle E; rewrite E; apply (gtP_deep _ _ (natl r) (natl (suf r2 d2)) (deep_R lenv r) (deep_R lenv _)).
    pose proof (natl_suf r2 d2); lia. }
  destruct r as [|[s2|L a] r2]; [cbn in Hlt; lia| |].
  - destruct Hr as [Hn2 [Hr2 [[Hs2 HS2]|[_ [Hren2 [->|[L [a [r3 [-> _]]]]]]]]]].
    + assert (G : gtP (R (LS s2 :: r2)) (R r2)).
      { destruct Hs2 as [y [[[u b] s] Ey]].
        pose proof (sres_pure lenv labs s2 y (so_pure _ _ _ _ _ HS2)) as Hp; rewrite Ey in Hp.
        assert (ER : R (LS s2 :: r2) y = FTerm u b (fun z => fs lenv s (R r2) z)).
        { rewrite (R_cons lenv labs _ _ (so_pure _ _ _ _ _ HS2)); unfold res; rewrite Ey; reflexivity. }
        pose proof (so_order _ _ _ _ _ HS y u b _ ER) as G.
        exact (gtP_keq _ _ _ _ (keq_refl _) (pay_keq lenv labs b s (R r2) Hp) G). }
      destruct (Nat.eq_dec d2 (List.length r2)) as [->|Hne].
      * rewrite (suf_cons _ _ _ (le_n _)), suf_all; exact G.
      * refine (gtP_trans _ _ _ G _).
        assert (Hr' : lnf (LS s2 :: r2)) by (split; [exact Hn2|split; [exact Hr2|left; split; assumption]]).
        pose proof (IH Hr' _ _ (tpos_last s2 r2 Hs2) H2r ltac:(cbn in Hlt; lia)) as G'.
        rewrite (suf_cons _ _ _ (le_n _)), suf_all in G'; exact G'.
    + exfalso; destruct H2r as [Hd [s [E Hs]]]; cbn in Hd; assert (d2 = 0) as -> by lia.
      cbn in E; injection E as ->; exact (sren_noterm lenv labs _ Hren2 Hs).
    + destruct (Nat.eq_dec d2 (S (List.length r3))) as [->|Hne].
      * exfalso; destruct (tpos_head _ _ H2r) as [s [E Hs]]; injection E as ->; exact (sren_noterm lenv labs _ Hren2 Hs).
      * apply (Hdeep r3); [cbn; lia|cbn in Hlt; lia|rewrite !suf_cons by (cbn in *; lia); reflexivity].
  - apply (Hdeep r2); [cbn; lia|cbn in Hlt; lia|rewrite suf_cons by (cbn in *; lia); reflexivity].
Qed.

(** ** Comparing results *)

Definition lexcmp (h h' : lexp) (i i' : nat) : option comparison :=
  match lcmp F h h' with Some Eq => Some (Nat.compare i i') | Some c => Some c | None => None end.

(** Results found in one word in normal form: terms with the identity
    payload adjustment, by term atom and then layer. *)
Definition dcmp (x y : desc) : option comparison :=
  match x, y with
  | DV h i, DV h' i' => lexcmp h h' i i'
  | DV _ _, _ => Some Lt
  | DT _ _, DV _ _ => Some Gt
  | DT t d, DT t' d' =>
      match t, t' with
      | NBind u (WEnd SNil) None, NBind u' (WEnd SNil) None =>
          Some (match Nat.compare u u' with Eq => Nat.compare d d' | c => c end)
      | _, _ => None
      end
  | DT _ _, DS _ _ _ _ => Some Lt
  | DS a h j d, DS a' h' j' d' =>
      match Nat.compare a a' with
      | Eq => match Nat.compare d d' with Eq => lexcmp h h' j j' | c => Some c end
      | c => Some c
      end
  | DS _ _ _ _, _ => Some Gt
  end.

Lemma lexcmp_sound h h' i i' c : lexcmp h h' i i' = Some c ->
  match c with
  | Eq => h = h' /\ i = i'
  | Lt => vlt (mk_rvar (lden h) i) (mk_rvar (lden h') i')
  | Gt => vlt (mk_rvar (lden h') i') (mk_rvar (lden h) i)
  end.
Proof.
  unfold lexcmp; destruct (lcmp F h h') as [c0|] eqn:E; [|discriminate].
  pose proof (lcmp_sound lenv F HF _ _ _ E) as Hc; destruct c0; cbn in Hc; intros H; injection H as <-.
  - subst h'; destruct (Nat.compare_spec i i') as [->|Hl|Hl]; [split; reflexivity|right; split; [reflexivity|exact Hl]|].
    right; split; [reflexivity|exact Hl].
  - left; exact Hc.
  - left; exact Hc.
Qed.

Lemma natl_suf_lt K d d' L a : d' < d -> d <= List.length K -> suf K (S d') = LA L a :: suf K d' ->
  natl (suf K d') < natl (suf K d).
Proof.
  intros Hlt Hd E; rewrite <- (suf_suf K d (S d') ltac:(lia) Hd) in E.
  pose proof (natl_suf (suf K d) (S d')) as H; rewrite E in H; cbn [natl] in H; lia.
Qed.

Lemma deep_cont l L : deep (natl l) (fun y => R l (shiftL lenv L y)).
Proof. exact (deep_shift lenv _ L _ (deep_R lenv l)). Qed.

Theorem dcmp_sound K e1 e2 g i g' i' x x' :
  lnf K -> e1 <= List.length K -> e2 <= List.length K ->
  dfollow F (suf K e1) g i = Some x -> dfollow F (suf K e2) g' i' = Some x' ->
  match dcmp x x' with
  | Some Eq => feq (R (suf K e1) (mk_rvar (lden g) i)) (R (suf K e2) (mk_rvar (lden g') i'))
  | Some Gt => rgt false (R (suf K e1) (mk_rvar (lden g) i)) (R (suf K e2) (mk_rvar (lden g') i'))
  | Some Lt => rgt false (R (suf K e2) (mk_rvar (lden g') i')) (R (suf K e1) (mk_rvar (lden g) i))
  | None => True
  end.
Proof.
  intros HK He1 He2 E1 E2.
  pose proof (dfollow_sound lenv F HF _ _ _ _ E1) as S1; pose proof (dfollow_sound lenv F HF _ _ _ _ E2) as S2.
  rewrite (suf_len K e1 He1) in S1; rewrite (suf_len K e2 He2) in S2.
  destruct x as [h j|t d|a h j d]; destruct x' as [h' j'|t' d'|a' h' j' d']; cbn [dcmp].
  (* DV DV *)
  - rewrite S1, S2.
    destruct (lexcmp h h' j j') as [c|] eqn:Ec; [|exact I]; apply lexcmp_sound in Ec.
    destruct c; [destruct Ec as [-> ->]; reflexivity|exact Ec|exact Ec].
  (* DV DT *)
  - rewrite S1; destruct S2 as [_ [Ht' [s' [_ [_ [Ef' _]]]]]]; rewrite Ef'.
    destruct t' as [|u' w' b']; [discriminate Ht'|exact I].
  (* DV DS *)
  - rewrite S1; destruct S2 as [_ [L' [_ Ef']]]; rewrite Ef'; exact I.
  (* DT DV *)
  - rewrite S2; destruct S1 as [_ [Ht [s [_ [_ [Ef _]]]]]]; rewrite Ef.
    destruct t as [|u w b]; [discriminate Ht|exact I].
  - destruct S1 as [Hd [Ht [s [Es [Hin [Ef [h1 [i1 Et]]]]]]]]; destruct S2 as [Hd' [Ht' [s' [Es' [Hin' [Ef' [h2 [i2 Et']]]]]]]].
    rewrite Ef, Ef'.
    destruct t as [|u [N|] [n|]]; try exact I; destruct N; try exact I;
      destruct t' as [|u' [N'|] [n'|]]; try exact I; destruct N'; try exact I.
    rewrite (suf_suf K e1 d ltac:(lia) He1) in *; rewrite (suf_suf K e2 d' ltac:(lia) He2) in *.
    rewrite (suf_suf K e1 (S d) ltac:(lia) He1) in Es; rewrite (suf_suf K e2 (S d') ltac:(lia) He2) in Es'.
    assert (T1 : tpos K d) by (split; [lia|exists s; split; [exact Es|exact (term_sterm _ _ _ _ _ _ Et)]]).
    assert (T2 : tpos K d') by (split; [lia|exists s'; split; [exact Es'|exact (term_sterm _ _ _ _ _ _ Et')]]).
    cbn [ft fw fs].
    destruct (Nat.compare_spec u u') as [<-|Hu|Hu]; [|left; exact Hu|left; exact Hu].
    destruct (Nat.compare_spec d d') as [<-|Hl|Hl].
    + cbn [feq]; repeat split; intros y _; apply feq_refl.
    + right; split; [reflexivity|right; split; [reflexivity|]].
      exact (layers_dec K HK d' d T2 T1 Hl).
    + right; split; [reflexivity|right; split; [reflexivity|]].
      exact (layers_dec K HK d d' T1 T2 Hl).
  (* DT DS *)
  - destruct S1 as [_ [Ht [s [_ [_ [Ef _]]]]]]; rewrite Ef; destruct S2 as [_ [L' [_ Ef']]]; rewrite Ef'.
    destruct t as [|u w b]; [discriminate Ht|exact I].
  (* DS DV *)
  - rewrite S2; destruct S1 as [_ [L [_ Ef]]]; rewrite Ef; exact I.
  (* DS DT *)
  - destruct S2 as [_ [Ht' [s' [_ [_ [Ef' _]]]]]]; rewrite Ef'; destruct S1 as [_ [L [_ Ef]]]; rewrite Ef.
    destruct t' as [|u' w' b']; [discriminate Ht'|exact I].
  (* DS DS *)
  - destruct S1 as [Hd [L [Es Ef]]]; destruct S2 as [Hd' [L' [Es' Ef']]]; rewrite Ef, Ef'; cbn [rgt].
    rewrite (suf_suf K e1 d ltac:(lia) He1), (suf_suf K e1 (S d) ltac:(lia) He1) in *.
    rewrite (suf_suf K e2 d' ltac:(lia) He2), (suf_suf K e2 (S d') ltac:(lia) He2) in *.
    destruct (Nat.compare_spec a a') as [<-|Ha|Ha]; [|left; exact Ha|left; exact Ha].
    destruct (Nat.compare_spec d d') as [<-|Hl|Hl].
    + rewrite Es in Es'; injection Es' as <-.
      destruct (lexcmp h h' j j') as [c|] eqn:Ec; [|exact I]; apply lexcmp_sound in Ec.
      destruct c.
      * destruct Ec as [-> ->]; apply feq_refl.
      * right; split; [reflexivity|right; split; [intros y _; apply feq_refl|exact Ec]].
      * right; split; [reflexivity|right; split; [intros y _; apply feq_refl|exact Ec]].
    + right; split; [reflexivity|left; left].
      exists (natl (suf K d')), (natl (suf K d)); split; [apply deep_cont|split; [apply deep_cont|]].
      exact (natl_suf_lt K d' d L a Hl ltac:(lia) Es).
    + right; split; [reflexivity|left; left].
      exists (natl (suf K d)), (natl (suf K d')); split; [apply deep_cont|split; [apply deep_cont|]].
      exact (natl_suf_lt K d d' L' a Hl ltac:(lia) Es').
Qed.

End Normal.
