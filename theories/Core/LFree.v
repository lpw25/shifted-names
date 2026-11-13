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
From ShiftedNames.Core Require Import Label Var Adjustment Normalise Unique Layered LayeredUnique Order Canon.
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

(** ** Far along a label *)

Fixpoint ssum (s : seg) : nat := match s with SNil => 0 | SEnt _ ts _ r => tlen ts + ssum r end.
Fixpoint lsum (L : list (lexp * nat)) : nat := match L with [] => 0 | (_, n) :: L' => n + lsum L' end.

(** Beyond [wB l] along any label, nothing in [l] is explicit. *)
Fixpoint wB (l : lword) : nat :=
  match l with [] => 0 | LS s :: r => ssum s + wB r | LA L _ :: r => lsum L + wB r end.

(** The first atom of a word, with the length of the rest after it. *)
Fixpoint firstatom (l : lword) : option (list (lexp * nat) * nat * nat) :=
  match l with
  | [] => None
  | LS _ :: r => firstatom r
  | LA L a :: r => Some (L, a, List.length r)
  end.

Section Far.

Variable lenv : list label.

Local Notation R := (R lenv).

Lemma sget_ssum s l ts m : sget lenv l s = Some (ts, m) -> tlen ts <= ssum s.
Proof.
  induction s as [|h ts' m' r IH] using seg_spine; cbn [sget ssum]; [discriminate|].
  destruct (label_eqb (lden lenv h) l); [intros E; injection E as <- <-; lia|intros E; pose proof (IH E); lia].
Qed.

Lemma lc_lsum l L : lc lenv l L <= lsum L.
Proof. induction L as [|[h n] L IH]; cbn [lc lsum]; [lia|destruct (label_eqb _ _); lia]. Qed.

Theorem far l : forall h, exists p q, q <= wB l /\ forall i, wB l <= i ->
  match firstatom l with
  | None => R l (mk_rvar h i) = FVar (mk_rvar h (i - q + p))
  | Some (L, a, d) =>
      d < List.length l /\ suf l (S d) = LA L a :: suf l d
      /\ R l (mk_rvar h i) = FStuck a (mk_rvar h (i - q + p)) (fun y => R (suf l d) (shiftL lenv L y))
  end.
Proof.
  induction l as [|[s|L a] r IH]; intros h.
  - exists 0, 0; split; [lia|intros i _; cbn; do 2 f_equal; lia].
  - destruct (IH h) as [p [q [Hq H]]].
    destruct (sget lenv h s) as [[ts m]|] eqn:Eg.
    + exists (m + p), (tlen ts + q); split; [pose proof (sget_ssum _ _ _ _ Eg); cbn [wB]; lia|].
      intros i Hi; pose proof (sget_ssum _ _ _ _ Eg) as Hs; cbn [wB] in Hi.
      assert (Ef : R (LS s :: r) (mk_rvar h i) = R r (mk_rvar h (i - tlen ts + m))).
      { rewrite (R_seg lenv); rewrite (fs_get lenv); unfold fget; cbn [v_label v_index]; rewrite Eg.
        apply (ftl_ge lenv); lia. }
      specialize (H (i - tlen ts + m) ltac:(lia)); cbn [firstatom]; destruct (firstatom r) as [[[L a] d]|].
      * destruct H as [Hd [Es Hr]]; split; [cbn; lia|]; rewrite !suf_cons by lia.
        split; [exact Es|rewrite Ef, Hr; do 2 f_equal; lia].
      * rewrite Ef, H; do 2 f_equal; lia.
    + exists p, q; split; [cbn [wB]; lia|]; intros i Hi; cbn [wB] in Hi.
      assert (Ef : R (LS s :: r) (mk_rvar h i) = R r (mk_rvar h i)).
      { rewrite (R_seg lenv); rewrite (fs_get lenv); unfold fget; cbn [v_label v_index]; rewrite Eg; reflexivity. }
      specialize (H i ltac:(lia)); cbn [firstatom]; destruct (firstatom r) as [[[L a] d]|].
      * destruct H as [Hd [Es Hr]]; split; [cbn; lia|]; rewrite !suf_cons by lia.
        split; [exact Es|rewrite Ef, Hr; reflexivity].
      * rewrite Ef, H; reflexivity.
  - exists 0, (lc lenv h L); split; [pose proof (lc_lsum h L); cbn [wB]; lia|].
    intros i Hi; pose proof (lc_lsum h L); cbn [wB] in Hi; cbn [firstatom].
    split; [cbn; lia|].
    replace (suf (LA L a :: r) (List.length r)) with r by (rewrite (suf_cons _ _ _ (le_n _)), suf_all; reflexivity).
    split; [change (S (List.length r)) with (List.length (LA L a :: r)); rewrite suf_all; reflexivity|].
    rewrite (R_atom lenv); unfold latom; cbn [v_label v_index].
    rewrite (proj2 (Nat.ltb_ge _ _)) by lia; do 2 f_equal; lia.
Qed.

End Far.

(** ** How deep the terms go *)

(** The first bound in [c] for a label. *)
Definition rbx (c : list (lexp * nat)) (h : lexp) : nat :=
  match find (fun p => lexp_eqb (fst p) h) c with Some p => snd p | None => 0 end.

Fixpoint omax (xs : list (option nat)) : option nat :=
  match xs with
  | [] => Some 0
  | x :: r => match x, omax r with Some a, Some b => Some (Nat.max a b) | _, _ => None end
  end.

(** The bounds after a segment: for a label with an entry, the outputs
    its inputs from the bound on go to. *)
Fixpoint cbound (c : list (lexp * nat)) (s : seg) : list (lexp * nat) :=
  match s with
  | SNil => c
  | SEnt h ts m s' => (h, Nat.max (tlen ts) (rbx c h) - tlen ts + m) :: cbound c s'
  end.

Definition isall (all : bool) (h : lexp) : bool := all || negb (lexp_eqb h LNone).

Section Depth.

Variable F : order.

Definition tdep (vd : lexp -> nat -> option nat) (tm : option nat) (t : ntgt) : option nat :=
  match t with
  | NVar g j => vd g j
  | NBind _ (WEnd SNil) None => tm
  | _ => None
  end.

Fixpoint ehd (vd : lexp -> nat -> option nat) (tm : option nat) (all : bool) (c : list (lexp * nat)) (s : seg)
  : list (option nat) :=
  match s with
  | SNil => []
  | SEnt h ts m s' =>
      (if isall all h then map (fun i => tdep vd tm (tnth ts i)) (seq (rbx c h) (tlen ts - rbx c h)) else [])
      ++ ehd vd tm all c s'
  end.

(** [vdepth l h i]: how deep the terms of what [l] does to [h₍ᵢ₎] go.
    [hreg l all c]: the most, for the variables (named ones, or all) of
    each label [g] from [rbx c g] on. *)
Fixpoint vdepth (l : lword) (h : lexp) (i : nat) {struct l} : option nat :=
  match l with
  | [] => Some 0
  | LS s :: r =>
      match seg_tgt F s h i with
      | Some (NVar g j) => vdepth r g j
      | Some (NBind _ (WEnd SNil) None) => option_map S (hreg r false [])
      | _ => None
      end
  | LA L a :: r =>
      match lcnt F h L with
      | Some c => if i <? c then vdepth r h i else hreg r true L
      | None => None
      end
  end
with hreg (l : lword) (all : bool) (c : list (lexp * nat)) {struct l} : option nat :=
  match l with
  | [] => Some 0
  | LS s :: r =>
      omax (hreg r all (cbound c s) :: ehd (vdepth r) (option_map S (hreg r false [])) all c s)
  | LA L a :: r =>
      omax (hreg r true L
            :: flat_map (fun p => if isall all (fst p) then map (vdepth r (fst p)) (seq (rbx c (fst p)) (snd p - rbx c (fst p)))
                                  else []) L)
  end.

End Depth.

Section DepthSound.

Variable lenv : list label.
Variable labs : list lexp.
Hypothesis Hinj : forall h h', In h labs -> In h' labs -> lden lenv h = lden lenv h' -> h = h'.
Variable F : order.
Hypothesis HF : facts_ok lenv F.

Local Notation lden := (lden lenv).
Local Notation R := (R lenv).

Definition rb (c : list (lexp * nat)) (l : option label) : nat :=
  match find (fun p => label_eqb (lden (fst p)) l) c with Some p => snd p | None => 0 end.

Lemma lexp_eqb_lden h h' : In h labs -> In h' labs -> lexp_eqb h h' = label_eqb (lden h) (lden h').
Proof.
  intros Hh Hh'; destruct (lexp_eqb h h') eqn:E.
  - apply lexp_eqb_eq in E; subst h'; symmetry; apply label_eqb_refl.
  - symmetry; apply label_eqb_neq; intros El; pose proof (Hinj h h' Hh Hh' El) as E'; subst h'.
    rewrite (proj2 (lexp_eqb_eq h h) eq_refl) in E; discriminate E.
Qed.

Lemma rbx_rb c h : (forall p, In p c -> In (fst p) labs) -> In h labs -> rbx c h = rb c (lden h).
Proof.
  intros Hc Hh; unfold rbx, rb; induction c as [|p c IH]; [reflexivity|]; cbn [find].
  rewrite (lexp_eqb_lden (fst p) h (Hc p (or_introl eq_refl)) Hh).
  destruct (label_eqb _ _); [reflexivity|apply IH; intros q Hq; apply Hc; right; exact Hq].
Qed.

Lemma rb_cons h v c l : rb ((h, v) :: c) l = if label_eqb (lden h) l then v else rb c l.
Proof. unfold rb; cbn [find fst snd]; destruct (label_eqb _ _); reflexivity. Qed.

Lemma omax_spec xs n : omax xs = Some n -> forall m, Forall (fun x => exists k, x = Some k /\ k <= m) xs <-> n <= m.
Proof.
  revert n; induction xs as [|x xs IH]; intros n; cbn [omax].
  - intros H; injection H as <-; intros m; split; [lia|constructor].
  - destruct x as [a|]; [|discriminate]; destruct (omax xs) as [b|]; [|discriminate].
    intros H; injection H as <-; intros m; rewrite Forall_cons_iff, (IH b eq_refl m).
    split; [intros [[k [E Hk]] Hb]; injection E as <-; lia|intros Hm; split; [exists a; split; [reflexivity|lia]|lia]].
Qed.

Lemma isall_dom all h i : isall all h = true <-> dom all (mk_rvar (lden h) i).
Proof.
  unfold isall, dom; cbn [v_label]; destruct all; cbn [orb]; [split; [left; reflexivity|reflexivity]|].
  destruct h; cbn [lexp_eqb negb Normalise.lden].
  - split; [discriminate|intros [H|H]; [discriminate H|destruct (H eq_refl)]].
  - split; [intros _; right; discriminate|reflexivity].
  - split; [intros _; right; discriminate|reflexivity].
Qed.

Lemma rb_cbound c s l : (forall p, In p c -> In (fst p) labs) -> (forall h ts m, In (h, ts, m) (ents s) -> In h labs) ->
  rb (cbound c s) l = match sget lenv l s with Some (ts, m) => Nat.max (tlen ts) (rb c l) - tlen ts + m | None => rb c l end.
Proof.
  intros Hc; induction s as [|h ts m s' IH] using seg_spine; intros Hs; [reflexivity|].
  cbn [cbound Normalise.sget]; rewrite rb_cons.
  destruct (label_eqb_spec (lden h) l) as [<-|Hne].
  - rewrite (rbx_rb c h Hc (Hs h ts m (or_introl eq_refl))); reflexivity.
  - apply IH; intros h' ts' m' Hin; exact (Hs h' ts' m' (or_intror Hin)).
Qed.

Lemma sget_ents' l s : forall ts m, sget lenv l s = Some (ts, m) -> exists g, In (g, ts, m) (ents s) /\ lden g = l.
Proof.
  induction s as [|h ts0 m0 r IH] using seg_spine; intros ts m; cbn [Normalise.sget ents]; [discriminate|].
  destruct (label_eqb_spec (lden h) l) as [E|E].
  - intros H; injection H as <- <-; exists h; split; [left; reflexivity|exact E].
  - intros H; destruct (IH ts m H) as [g [H1 H2]]; exists g; split; [right; exact H1|exact H2].
Qed.

Lemma ents_sget s h ts m : sdist lenv s -> In (h, ts, m) (ents s) -> sget lenv (lden h) s = Some (ts, m).
Proof.
  induction s as [|h' ts' m' r IH] using seg_spine; cbn [ents]; [intros _ []|]; intros [Hn Hd] [E|Hin].
  - injection E as -> -> ->; cbn [Normalise.sget]; rewrite label_eqb_refl; reflexivity.
  - cbn [Normalise.sget]; pose proof (IH Hd Hin) as E.
    destruct (label_eqb_spec (lden h') (lden h)) as [Eh|_]; [|exact E].
    rewrite Eh, E in Hn; discriminate Hn.
Qed.

(** The variables of a region, through a segment. *)
Lemma seg_reg s c all m K :
  sdist lenv s -> (forall h ts m, In (h, ts, m) (ents s) -> In h labs) -> (forall p, In p c -> In (fst p) labs) ->
  (forall y, dom all y -> rb c (v_label y) <= v_index y -> dle m (fs lenv s K y)) <->
  ((forall h ts m', In (h, ts, m') (ents s) -> isall all h = true -> forall i, rbx c h <= i < tlen ts ->
      dle m (ft lenv (tnth ts i) K))
   /\ (forall y, dom all y -> rb (cbound c s) (v_label y) <= v_index y -> dle m (K y))).
Proof.
  intros Hd Hs Hc; split.
  - intros H; split.
    + intros h ts m' Hin Ha i Hi.
      pose proof (ents_sget _ _ _ _ Hd Hin) as Eg.
      assert (Hy : dom all (mk_rvar (lden h) i)) by (apply isall_dom, Ha).
      specialize (H (mk_rvar (lden h) i) Hy); cbn [v_label v_index] in H.
      rewrite <- (rbx_rb c h Hc (Hs _ _ _ Hin)) in H; specialize (H (proj1 Hi)).
      rewrite (fs_get lenv) in H; unfold fget in H; cbn [v_label v_index] in H; rewrite Eg in H.
      rewrite (ftl_lt lenv) in H by exact (proj2 Hi); exact H.
    + intros [l j] Hy Hj; cbn [v_label v_index] in Hj; rewrite (rb_cbound c s l Hc Hs) in Hj.
      destruct (sget lenv l s) as [[ts m']|] eqn:Eg.
      * specialize (H (mk_rvar l (j - m' + tlen ts)) Hy); cbn [v_label v_index] in H.
        rewrite (fs_get lenv) in H; unfold fget in H; cbn [v_label v_index] in H; rewrite Eg in H.
        rewrite (ftl_ge lenv) in H by lia.
        replace (j - m' + tlen ts - tlen ts + m') with j in H by lia; apply H; lia.
      * specialize (H (mk_rvar l j) Hy Hj); rewrite (fs_get lenv) in H; unfold fget in H; cbn [v_label v_index] in H.
        rewrite Eg in H; exact H.
  - intros [H1 H2] [l j] Hy Hj; cbn [v_label v_index] in Hj; rewrite (fs_get lenv); unfold fget; cbn [v_label v_index].
    destruct (sget lenv l s) as [[ts m']|] eqn:Eg.
    + destruct (Nat.ltb_spec j (tlen ts)) as [Hlt|Hge].
      * rewrite (ftl_lt lenv) by exact Hlt.
        destruct (sget_ents' l s ts m' Eg) as [g [Hin <-]].
        apply (H1 g ts m' Hin); [apply (isall_dom all g j), Hy|].
        rewrite (rbx_rb c g Hc (Hs _ _ _ Hin)); lia.
      * rewrite (ftl_ge lenv) by exact Hge; apply H2; [exact Hy|].
        cbn [v_label v_index]; rewrite (rb_cbound c s l Hc Hs), Eg; lia.
    + apply H2; [exact Hy|cbn [v_label v_index]; rewrite (rb_cbound c s l Hc Hs), Eg; exact Hj].
Qed.

Lemma omax_some xs n : omax xs = Some n -> forall x, In x xs -> exists k, x = Some k.
Proof.
  revert n; induction xs as [|y xs IH]; intros n; cbn [omax]; [intros _ x []|].
  destruct y as [a|]; [|discriminate]; destruct (omax xs) as [b|] eqn:E; [|discriminate].
  intros _ x [<-|Hx]; [exists a; reflexivity|exact (IH b eq_refl x Hx)].
Qed.

Lemma ehd_forall (P : option nat -> Prop) vd tm all c s :
  Forall P (ehd vd tm all c s)
  <-> (forall h ts m, In (h, ts, m) (ents s) -> isall all h = true -> forall i, rbx c h <= i < tlen ts ->
         P (tdep vd tm (tnth ts i))).
Proof.
  induction s as [|h ts m s' IH] using seg_spine; cbn [ehd ents].
  - split; [intros _ h ts m []|intros _; constructor].
  - rewrite Forall_app, IH; split.
    + intros [H1 H2] h' ts' m' [E|Hin]; [injection E as <- <- <-|exact (H2 h' ts' m' Hin)].
      intros Ha i Hi; rewrite Ha in H1; rewrite Forall_map, Forall_forall in H1.
      apply H1, in_seq; lia.
    + intros H; split; [|intros h' ts' m' Hin; exact (H h' ts' m' (or_intror Hin))].
      destruct (isall all h) eqn:Ha; [|constructor].
      rewrite Forall_map, Forall_forall; intros i Hi; apply in_seq in Hi.
      apply (H h ts m (or_introl eq_refl) Ha); lia.
Qed.

Definition sgood (s : seg) : Prop := sdist lenv s /\ forall h ts m, In (h, ts, m) (ents s) -> In h labs.
Definition Lgood (L : list (lexp * nat)) : Prop :=
  (forall p, In p L -> In (fst p) labs) /\ NoDup (map (fun p => lden (fst p)) L).
Definition lgood (l : lword) : Prop := Forall (fun x => match x with LS s => sgood s | LA L _ => Lgood L end) l.

Lemma rb_lc L l : NoDup (map (fun p => lden (fst p)) L) -> rb L l = lc lenv l L.
Proof.
  induction L as [|[h n] L IH]; intros Hd; [reflexivity|]; inversion Hd as [|? ? Hn Hd']; subst.
  rewrite rb_cons; cbn [lc]; destruct (label_eqb_spec (lden h) l) as [<-|Hne]; [|rewrite IH by exact Hd'; lia].
  assert (lc lenv (lden h) L = 0) as ->; [|lia].
  clear IH Hd' Hd; revert Hn; induction L as [|[h' n'] L IH]; intros Hn; [reflexivity|]; cbn [lc]; cbn [map fst] in Hn.
  destruct (label_eqb_spec (lden h') (lden h)) as [E|_]; [destruct Hn; left; exact E|].
  apply IH; intros H; apply Hn; right; exact H.
Qed.

Lemma lc_in L h n : NoDup (map (fun p => lden (fst p)) L) -> In (h, n) L -> lc lenv (lden h) L = n.
Proof.
  intros Hd Hin; rewrite <- rb_lc by exact Hd; clear -Hd Hin.
  induction L as [|[h' n'] L IH]; [destruct Hin|]; inversion Hd as [|? ? Hn Hd']; subst; rewrite rb_cons.
  destruct Hin as [E|Hin]; [injection E as -> ->; rewrite label_eqb_refl; reflexivity|].
  destruct (label_eqb_spec (lden h') (lden h)) as [E|_]; [|exact (IH Hd' Hin)].
  exfalso; apply Hn; rewrite E; apply (in_map (fun p => lden (fst p))) in Hin; exact Hin.
Qed.

Lemma lc_pos L l : 0 < lc lenv l L -> exists h n, In (h, n) L /\ lden h = l.
Proof.
  induction L as [|[h n] L IH]; cbn [lc]; [lia|]; destruct (label_eqb_spec (lden h) l) as [E|_].
  - intros _; exists h, n; split; [left; reflexivity|exact E].
  - intros H; destruct (IH H) as [h' [n' [H1 H2]]]; exists h', n'; split; [right; exact H1|exact H2].
Qed.

Lemma ok_iff (x : option nat) n m : x = Some n -> ((exists k, x = Some k /\ k <= m) <-> n <= m).
Proof. intros ->; split; [intros [k [E Hk]]; injection E as <-; exact Hk|intros H; exists n; auto]. Qed.

Theorem depth_exact l : lgood l ->
  (forall h i n, vdepth F l h i = Some n -> forall m, dle m (R l (mk_rvar (lden h) i)) <-> n <= m)
  /\ (forall all c n, (forall p, In p c -> In (fst p) labs) -> hreg F l all c = Some n ->
        forall m, (forall y, dom all y -> rb c (v_label y) <= v_index y -> dle m (R l y)) <-> n <= m).
Proof.
  induction l as [|[s|L a] r IH]; intros Hl.
  - split; [intros h i n H; injection H as <-; intros m; cbn; split; [lia|tauto]|].
    intros all c n _ H; injection H as <-; intros m; cbn; split; [lia|tauto].
  - inversion Hl as [|? ? Hs0 Hr]; subst; destruct Hs0 as [Hsd Hsl]; destruct (IH Hr) as [V Hg].
    assert (Tm : forall u n, option_map S (hreg F r false []) = Some n ->
                   forall m, dle m (ft lenv (NBind u (WEnd SNil) None) (R r)) <-> n <= m).
    { intros u n E m; destruct (hreg F r false []) as [n0|] eqn:Eh; [|discriminate]; injection E as <-.
      pose proof (Hg false [] n0 (fun p H => match H with end) Eh) as G.
      destruct m as [|m]; cbn [ft dle]; [split; [tauto|lia]|].
      rewrite <- Nat.succ_le_mono, <- (G m); split; intros H y Hy; [intros _; apply H, Hy|apply H; [exact Hy|unfold rb; cbn; lia]]. }
    assert (Td : forall t k, tdep (vdepth F r) (option_map S (hreg F r false [])) t = Some k ->
                   forall m, dle m (ft lenv t (R r)) <-> k <= m).
    { intros [g j|u [[|? ? ? ?]|? ? ? ?] [?|]] k; cbn [tdep]; try discriminate.
      - intros E m; exact (V g j k E m).
      - exact (Tm u k). }
    split.
    + intros h i n; cbn [vdepth]; destruct (seg_tgt F s h i) as [t|] eqn:Et; [|discriminate].
      intros E m; rewrite (R_seg lenv), (seg_tgt_free lenv F HF _ _ _ _ _ Et).
      destruct t as [g j|u [[|? ? ? ?]|? ? ? ?] [?|]]; try discriminate; [exact (V g j n E m)|exact (Tm u n E m)].
    + intros all c n Hc; cbn [hreg]; intros E m.
      assert (Hsome := omax_some _ _ E).
      destruct (hreg F r all (cbound c s)) as [n1|] eqn:E1; [|destruct (Hsome None (or_introl eq_refl)); discriminate].
      rewrite <- (omax_spec _ _ E m), Forall_cons_iff, (ok_iff _ _ m eq_refl).
      assert (Hc' : forall p, In p (cbound c s) -> In (fst p) labs).
      { clear -Hc Hsl; induction s as [|h ts mm s' IHs] using seg_spine; [exact Hc|].
        intros p [<-|Hp]; [exact (Hsl h ts mm (or_introl eq_refl))|].
        apply IHs; [intros h' ts' m' Hin; exact (Hsl h' ts' m' (or_intror Hin))|exact Hp]. }
      setoid_rewrite (R_seg lenv); rewrite (seg_reg s c all m (R r) Hsd Hsl Hc), (Hg all _ n1 Hc' E1 m), ehd_forall.
      split; [intros [H1 H2]; split; [exact H2|]|intros [H2 H1]; split; [|exact H2]].
      * intros h ts mm Hin Ha i Hi.
        assert (Hx : In (tdep (vdepth F r) (option_map S (hreg F r false [])) (tnth ts i))
                        (ehd (vdepth F r) (option_map S (hreg F r false [])) all c s)).
        { clear -Hin Ha Hi; induction s as [|h' ts' m' s' IHs] using seg_spine; [destruct Hin|]; cbn [ehd ents] in *.
          apply in_or_app; destruct Hin as [E|Hin]; [injection E as <- <- <-; left; rewrite Ha|right; exact (IHs Hin)].
          apply (in_map (fun j => tdep (vdepth F r) (option_map S (hreg F r false [])) (tnth ts' j))), in_seq; lia. }
        destruct (Hsome _ (or_intror Hx)) as [k Ek]; exists k; split; [exact Ek|].
        apply (Td _ k Ek m), (H1 h ts mm Hin Ha i Hi).
      * intros h ts mm Hin Ha i Hi; destruct (H1 h ts mm Hin Ha i Hi) as [k [Ek Hk]].
        apply (Td _ k Ek m), Hk.
  - inversion Hl as [|? ? HL0 Hr]; subst; destruct HL0 as [HLl HLd]; destruct (IH Hr) as [V Hg].
    assert (St : forall n z, hreg F r true L = Some n ->
                   forall m, dle m (FStuck a z (fun y => R r (shiftL lenv L y))) <-> n <= m).
    { intros n z E m; rewrite <- (Hg true L n HLl E m); cbn [dle]; split.
      - intros H [l j] _ Hj; cbn [v_label v_index] in Hj; rewrite rb_lc in Hj by exact HLd.
        specialize (H (mk_rvar l (j - lc lenv l L))); unfold shiftL in H; cbn [v_label v_index] in H.
        replace (j - lc lenv l L + lc lenv l L) with j in H by lia; exact H.
      - intros H [l j]; apply H; [left; reflexivity|]; unfold shiftL; cbn [v_label v_index].
        rewrite rb_lc by exact HLd; lia. }
    split.
    + intros h i n; cbn [vdepth]; destruct (lcnt F h L) as [c|] eqn:Ec; [|discriminate].
      pose proof (lcnt_sound lenv F HF _ _ _ Ec) as Hc; intros E m.
      rewrite (R_atom lenv); unfold latom; cbn [v_label v_index]; rewrite Hc.
      destruct (Nat.ltb_spec i c) as [Hi|Hi]; [exact (V h i n E m)|exact (St n _ E m)].
    + intros all c n Hc; cbn [hreg]; intros E m.
      assert (Hsome := omax_some _ _ E).
      destruct (hreg F r true L) as [n1|] eqn:E1; [|destruct (Hsome None (or_introl eq_refl)); discriminate].
      rewrite <- (omax_spec _ _ E m), Forall_cons_iff, (ok_iff _ _ m eq_refl), <- (St n1 (mk_rvar lbig 0) eq_refl m).
      rewrite Forall_flat_map; setoid_rewrite (R_atom lenv); split.
      * intros H; split.
        -- set (B := Nat.max (rb c lbig) (lc lenv lbig L)).
           specialize (H (mk_rvar lbig B) (dom_big _ _) ltac:(cbn [v_label v_index]; unfold B; lia)).
           unfold latom in H; cbn [v_label v_index] in H; rewrite (proj2 (Nat.ltb_ge _ _)) in H by (unfold B; lia).
           exact H.
        -- apply Forall_forall; intros [h n'] Hp; cbn [fst snd].
           destruct (isall all h) eqn:Ha; [|constructor].
           apply Forall_forall; intros x Hx; apply in_map_iff in Hx as [i [<- Hi]]; apply in_seq in Hi.
           assert (Hh : In h labs) by exact (HLl _ Hp).
           specialize (H (mk_rvar (lden h) i) (proj1 (isall_dom all h i) Ha)).
           cbn [v_label v_index] in H; rewrite <- (rbx_rb c h Hc Hh) in H; specialize (H ltac:(lia)).
           unfold latom in H; cbn [v_label v_index] in H; rewrite (lc_in L h n' HLd Hp), (proj2 (Nat.ltb_lt _ _)) in H by lia.
           destruct (vdepth F r h i) as [k|] eqn:Ek.
           ++ exists k; split; [reflexivity|]; apply (V h i k Ek m), H.
           ++ exfalso; destruct (Hsome None) as [? Hn]; [right; apply in_flat_map; exists (h, n'); split; [exact Hp|]|discriminate Hn].
              cbn [fst snd]; rewrite Ha; rewrite <- Ek; apply in_map, in_seq; lia.
      * intros [Hst Hlift] [l j] Hy Hj; unfold latom; cbn [v_label v_index] in *.
        destruct (Nat.ltb_spec j (lc lenv l L)) as [Hlt|Hge]; [|cbn [dle] in Hst |- *; exact Hst].
        destruct (lc_pos L l ltac:(lia)) as [h [n' [Hp <-]]].
        rewrite Forall_forall in Hlift; specialize (Hlift (h, n') Hp); cbn [fst snd] in Hlift.
        assert (Ha : isall all h = true) by (apply (isall_dom all h j), Hy).
        rewrite Ha, Forall_map, Forall_forall in Hlift.
        rewrite (lc_in L h n' HLd Hp) in Hlt.
        assert (Hh : In h labs) by exact (HLl _ Hp).
        destruct (Hlift j ltac:(apply in_seq; rewrite (rbx_rb c h Hc Hh); lia)) as [k [Ek Hk]].
        apply (V h j k Ek m), Hk.
Qed.

End DepthSound.
