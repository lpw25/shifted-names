(** * The canonical word

    [canon l]: the word [l] in the normal form [LayeredUnique.lnf], built
    from the right: an atom goes in front as it is, a segment [s] in
    front of the canonical word [K] goes as [rcons sa (bcore T K)], where
    [T] are the terms of [s] and [sa] is [s] with its terms replaced by
    the first bound variables.  [canon_ok]: the result is in normal form
    and means the same; [canon_unique]: words that mean the same have
    the same canonical word. *)

From Stdlib Require Import Arith List Lia Bool Sorted.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Unique Normal Layered LayeredUnique Order
  Canon Retarget LFree CanonF CanonR CanonB.
Import ListNotations.

Section Canon.

Variable F : order.
Variable labs : list lexp.
Variable ntm : nat.

(** Targets with the terms numbered from [c] and bound variables shifted
    by [n]. *)
Fixpoint rn_ts (n c : nat) (xs : list ntgt) : list ntgt :=
  match xs with
  | [] => []
  | NBind _ _ _ :: r => NVar LNone c :: rn_ts n (S c) r
  | NVar LNone j :: r => NVar LNone (n + j) :: rn_ts n c r
  | t :: r => t :: rn_ts n c r
  end.

Definition cntt (xs : list ntgt) : nat := List.length (filter is_term xs).

Fixpoint sa_es (n c : nat) (es : list (lexp * tlist * nat)) : list (lexp * (list ntgt * nat)) :=
  match es with
  | [] => []
  | (h, ts, m) :: r =>
      (h, (rn_ts n c (tl_list ts), if lexp_eqb h LNone then n + m else m)) :: sa_es n (c + cntt (tl_list ts)) r
  end.

Definition terms (s : seg) : list ntgt := flat_map (fun e => filter is_term (tl_list (snd (fst e)))) (ents s).

Definition sa (n : nat) (s : seg) : option seg := sbuild F (sa_es n 0 (ents s) ++ [(LNone, ([], n))]).

Definition cseg (s : seg) (K : lword) : option lword :=
  match terms s with
  | [] => rcons F ntm s K
  | T => match sa (List.length T) s, bcore F ntm (S (List.length K)) T K with
         | Some s', Some Y => rcons F ntm s' Y
         | _, _ => None
         end
  end.

Fixpoint canon (l : lword) : option lword :=
  match l with
  | [] => Some []
  | LS s :: r => obind (canon r) (cseg s)
  | LA L a :: r => option_map (cons (LA L a)) (canon r)
  end.

End Canon.

Section CanonOk.

Variable lenv : list label.
Variable labs : list lexp.
Hypothesis Hinj : forall h h', In h labs -> In h' labs -> lden lenv h = lden lenv h' -> h = h'.
Hypothesis HN : In LNone labs.
Variable ntm : nat.
Variable F : order.
Hypothesis HF : facts_ok lenv F.
Hypothesis Htot : forall a b, In a labs -> In b labs -> lcmp F a b <> None.

Local Notation lden := (lden lenv).
Local Notation R := (R lenv).
Local Notation fs := (fs lenv).
Local Notation sres := (sres lenv).
Local Notation sp1 := (sp1 lenv labs ntm).
Local Notation tp1 := (tp1 labs ntm).
Local Notation lw1 := (lw1 lenv labs ntm).
Local Notation lnf := (lnf lenv labs gtP).

Lemma rn_ts_len n xs : forall c, List.length (rn_ts n c xs) = List.length xs.
Proof. induction xs as [|[[|y|y] j|u w b] xs IH]; intros c; cbn; f_equal; auto. Qed.

Lemma rn_ts_nth n xs : forall c i, i < List.length xs ->
  nth i (rn_ts n c xs) (NVar LNone 0) =
  match nth i xs (NVar LNone 0) with
  | NBind _ _ _ => NVar LNone (c + cntt (firstn i xs))
  | NVar LNone j => NVar LNone (n + j)
  | t => t
  end.
Proof.
  induction xs as [|t xs IH]; intros c i Hi; [cbn in Hi; lia|].
  destruct i as [|i].
  - destruct t as [[|y|y] j|u w b]; cbn; try reflexivity; unfold cntt; cbn; f_equal; lia.
  - cbn [List.length] in Hi; destruct t as [[|y|y] j|u w b]; cbn [rn_ts nth firstn];
      rewrite (IH _ i ltac:(lia)); destruct (nth i xs (NVar LNone 0)) as [[|z|z] k|u' w' b']; try reflexivity;
      unfold cntt; cbn [filter is_term List.length]; f_equal; lia.
Qed.

Lemma filter_nth xs i : i < List.length xs -> is_term (nth i xs (NVar LNone 0)) = true ->
  nth (cntt (firstn i xs)) (filter is_term xs) (NVar LNone 0) = nth i xs (NVar LNone 0) /\ cntt (firstn i xs) < cntt xs.
Proof.
  revert i; induction xs as [|t xs IH]; intros i Hi Ht; [cbn in Hi; lia|].
  destruct i as [|i]; unfold cntt in *; cbn [nth firstn filter] in *.
  - rewrite Ht; cbn; split; [reflexivity|lia].
  - cbn [List.length] in Hi; destruct (IH i ltac:(lia) Ht) as [A B].
    destruct (is_term t); cbn [List.length nth]; split; [exact A|lia|exact A|lia].
Qed.

Lemma sa_es_find n l es : forall c,
  match find (fun e => label_eqb (lden (fst (fst e))) l) es with
  | Some (h, ts, m) =>
      exists A B, flat_map (fun e => filter is_term (tl_list (snd (fst e)))) es = A ++ filter is_term (tl_list ts) ++ B
        /\ find (fun e => label_eqb (lden (fst e)) l) (sa_es n c es)
           = Some (h, (rn_ts n (c + List.length A) (tl_list ts), if lexp_eqb h LNone then n + m else m))
  | None => find (fun e => label_eqb (lden (fst e)) l) (sa_es n c es) = None
  end.
Proof.
  induction es as [|[[h ts] m] es IH]; intros c; cbn [find sa_es fst flat_map snd]; [reflexivity|].
  destruct (label_eqb (lden h) l) eqn:E.
  - exists [], (flat_map (fun e => filter is_term (tl_list (snd (fst e)))) es); split; [reflexivity|].
    cbn [List.length]; rewrite Nat.add_0_r; reflexivity.
  - specialize (IH (c + cntt (tl_list ts))).
    destruct (find (fun e => label_eqb (lden (fst (fst e))) l) es) as [[[h' ts'] m']|]; [|exact IH].
    destruct IH as [A [B [E1 E2]]]; exists (filter is_term (tl_list ts) ++ A), B; split.
    + rewrite E1, app_assoc; reflexivity.
    + rewrite E2, length_app; unfold cntt; do 4 f_equal; lia.
Qed.

Definition tterm' := tterm ntm.

Lemma terms_tterm s : sp1 s -> Forall tterm' (terms s).
Proof.
  intros HS; apply Forall_forall; intros t Ht; unfold terms in Ht; apply in_flat_map in Ht as [[[h ts] m] [He Ht]].
  apply filter_In in Ht as [Ht Et]; pose proof (proj1 (Forall_forall _ _) (proj2 HS) t (ents_stgts s h ts m t He Ht)) as Hp.
  destruct t; [discriminate Et|exact Hp].
Qed.

Lemma terms_nil s : sp1 s -> terms s = [] -> sren labs s.
Proof.
  intros HS E; apply (noterms_sren lenv labs ntm s HS); unfold has_terms; rewrite <- stgts_stargets.
  destruct (existsb is_term (stgts s)) eqn:Ex; [exfalso|reflexivity].
  apply existsb_exists in Ex as [t [Hin Ht]].
  assert (G : forall s', In t (stgts s') -> is_term t = true -> In t (terms s')).
  { intros s'; induction s' as [|h ts m r IH] using seg_spine; [intros []|]; rewrite stgts_cons.
    intros H Ht'; apply in_app_or in H as [H|H]; unfold terms; cbn [ents flat_map fst snd]; apply in_or_app;
      [left; apply filter_In; split; assumption|right; exact (IH H Ht')]. }
  pose proof (G s Hin Ht) as H; rewrite E in H; destruct H.
Qed.

Theorem sa_ok s s' : sp1 s -> sa F (List.length (terms s)) s = Some s' ->
  sshape lenv labs false s' /\ sren labs s' /\
  forall x, match sres s x with
            | inl y => sres s' x = inl (match v_label y with None => mk_rvar None (List.length (terms s) + v_index y) | Some _ => y end)
            | inr tm => exists i, i < List.length (terms s) /\ sres s' x = inl (mk_rvar None i)
                                  /\ tres lenv (nth i (terms s) (NVar LNone 0)) = inr tm
            end.
Proof.
  intros HS E; set (n := List.length (terms s)) in *; unfold sa in E.
  assert (Hlab : forall h ts m, In (h, ts, m) (ents s) -> In h labs).
  { intros h ts m Hin; apply (sshape_labs lenv labs false s (proj1 HS) h (tl_list ts) m).
    rewrite <- ents_sents; apply (in_map (fun e => (fst (fst e), tl_list (snd (fst e)), snd e)) _ _ Hin). }
  assert (Htp : forall h ts m, In (h, ts, m) (ents s) -> forall t, In t (tl_list ts) -> tp1 t).
  { intros h ts m He t Ht; exact (proj1 (Forall_forall _ _) (proj2 HS) t (ents_stgts s h ts m t He Ht)). }
  assert (Rt : forall xs c, (forall t, In t xs -> tp1 t) -> forall t, In t (rn_ts n c xs) -> ren_target labs t).
  { induction xs as [|t0 xs IH]; intros c Hx t Ht; [destruct Ht|].
    pose proof (Hx t0 (or_introl eq_refl)) as H0.
    destruct t0 as [[|y|y] j|u w b]; cbn [rn_ts In] in Ht; destruct Ht as [<-|Ht];
      try exact HN; try exact H0; exact (IH _ (fun t' H => Hx t' (or_intror H)) t Ht). }
  assert (Hes : forall es c, (forall h ts m, In (h, ts, m) es -> In (h, ts, m) (ents s)) ->
                  forall h xs m, In (h, (xs, m)) (sa_es n c es) -> In h labs /\ forall t, In t xs -> ren_target labs t).
  { induction es as [|[[h ts] m] es IH]; intros c Hsub h' xs m' Hin; [destruct Hin|].
    cbn [sa_es] in Hin; destruct Hin as [Eh|Hin]; [|exact (IH _ (fun h0 ts0 m0 H => Hsub h0 ts0 m0 (or_intror H)) _ _ _ Hin)].
    injection Eh as <- <- <-; pose proof (Hsub h ts m (or_introl eq_refl)) as He.
    split; [exact (Hlab _ _ _ He)|exact (Rt _ c (Htp _ _ _ He))]. }
  destruct (sbuild_shape lenv labs F HF _ _ E) as [Hs [Hts _]].
  { intros h xs m Hin; apply in_app_or in Hin as [Hin|[Eh|[]]]; [exact (proj1 (Hes _ 0 (fun _ _ _ H => H) _ _ _ Hin))|].
    injection Eh as <- _ _; exact HN. }
  split; [exact Hs|split].
  { apply Forall_forall; intros t Hin; destruct (Hts t Hin) as [h [xs [m [He Hx]]]].
    apply in_app_or in He as [He|[Eh|[]]]; [exact (proj2 (Hes _ 0 (fun _ _ _ H => H) _ _ _ He) t Hx)|].
    injection Eh as <- <- <-; destruct Hx. }
  intros [l i]; rewrite (sres_ents lenv s l i).
  pose proof (sa_es_find n l (ents s) 0) as Hf.
  rewrite (sres_sbuild lenv F HF _ _ E l i).
  destruct (find (fun e => label_eqb (lden (fst (fst e))) l) (ents s)) as [[[h ts] m]|] eqn:Ef.
  - destruct Hf as [A [B [Et Ef']]]; rewrite (find_app_some _ _ _ _ Ef').
    apply find_some in Ef as [Eh Hin]; cbn [fst] in Eh; apply label_eqb_eq in Eh; subst l.
    fold (terms s) in Et; cbn [Nat.add].
    assert (Hn : lexp_eqb h LNone = true <-> lden h = None).
    { split; [intros H; apply lexp_eqb_eq in H; subst; reflexivity|intros H; rewrite (lden_none lenv h H); reflexivity]. }
    unfold etgt; rewrite rn_ts_len; destruct (Nat.ltb_spec i (List.length (tl_list ts))) as [Hi|Hi].
    + rewrite (rn_ts_nth n _ _ i Hi).
      pose proof (Htp _ _ _ Hin _ (nth_In _ (NVar LNone 0) Hi)) as Hp.
      destruct (nth i (tl_list ts) (NVar LNone 0)) as [[|y|y] j|u w b] eqn:Et0; cbn [tres v_label v_index Normalise.lden];
        try reflexivity.
      exists (List.length A + cntt (firstn i (tl_list ts))).
      destruct (filter_nth (tl_list ts) i Hi ltac:(rewrite Et0; reflexivity)) as [F1 F2].
      split; [subst n; rewrite Et, !length_app; unfold cntt in *; lia|split; [reflexivity|]].
      rewrite Et, app_nth2 by lia; replace (List.length A + cntt (firstn i (tl_list ts)) - List.length A) with (cntt (firstn i (tl_list ts))) by lia.
      rewrite app_nth1 by (unfold cntt in F2; exact F2); rewrite F1, Et0; reflexivity.
    + cbn [v_label v_index]; destruct (lexp_eqb h LNone) eqn:Eq.
      * assert (H0 : lden h = None) by (apply lexp_eqb_eq in Eq; subst; reflexivity); rewrite H0; do 2 f_equal; lia.
      * destruct (lden h) eqn:H0; [reflexivity|]; rewrite (lden_none lenv h H0) in Eq; discriminate Eq.
  - rewrite (find_app_none _ _ _ Hf); cbn [find fst].
    destruct l as [x|]; cbn [Normalise.lden label_eqb v_label v_index]; [reflexivity|].
    unfold etgt; cbn; do 2 f_equal; lia.
Qed.

Lemma sa_sem s s' E K : sp1 s -> sa F (List.length (terms s)) s = Some s' -> ET F (terms s) = Some E ->
  forall v, feq (fs s' (fs E (R K)) v) (fs s (R K) v).
Proof.
  intros HS Es EE v; destruct (sa_ok s s' HS Es) as [_ [Hr Hspec]].
  destruct (ET_ok lenv labs HN ntm F HF (terms s) E (terms_tterm s HS) EE) as [HE HEs].
  rewrite (fs_ren lenv labs s' _ v Hr), (res_free lenv labs ntm s _ v HS), (res_free lenv labs ntm E _ _ HE).
  specialize (Hspec v); pose proof (sres_ren lenv labs s' v Hr) as Hsv.
  destruct (sres s v) as [[[x|] j]|[[u b] s0]].
  - rewrite Hspec in Hsv; injection Hsv as <-; rewrite HEs; apply feq_refl.
  - rewrite Hspec in Hsv; injection Hsv as <-; cbn [v_label v_index]; rewrite HEs.
    rewrite (proj2 (Nat.ltb_ge _ _)) by lia; replace (List.length (terms s) + j - List.length (terms s)) with j by lia.
    apply feq_refl.
  - destruct Hspec as [i [Hi [Hs' Et]]]; rewrite Hs' in Hsv; injection Hsv as <-; rewrite HEs.
    rewrite (proj2 (Nat.ltb_lt _ _) Hi), Et; apply feq_refl.
Qed.

Lemma bcore_ET fuel T K Y : bcore F ntm fuel T K = Some Y -> exists E, ET F T = Some E.
Proof. destruct fuel; cbn [bcore]; [discriminate|]; destruct (ET F T) as [E|]; [eauto|discriminate]. Qed.

Theorem cseg_ok s K K' : lnf K -> lw1 K -> sp1 s -> cseg F ntm s K = Some K' ->
  lnf K' /\ lw1 K' /\ forall v, feq (R K' v) (R (LS s :: K) v).
Proof.
  intros Hl Hw HS; unfold cseg; destruct (terms s) as [|t T'] eqn:Et.
  - exact (rcons_ok lenv labs Hinj HN ntm F HF K s K' Hl Hw (proj1 HS) (terms_nil s HS Et)).
  - rewrite <- Et; destruct (sa F (List.length (terms s)) s) as [s'|] eqn:Es; [|discriminate].
    destruct (bcore F ntm (S (List.length K)) (terms s) K) as [Y|] eqn:EY; [|discriminate]; intros EK.
    destruct (bcore_ET _ _ _ _ EY) as [E EE].
    assert (Hne : terms s <> []) by (rewrite Et; discriminate).
    destruct (bcore_ok lenv labs Hinj HN ntm F HF Htot _ _ K Y E (terms_tterm s HS) Hne Hl Hw EE EY) as [HlY [HwY SemY]].
    destruct (sa_ok s s' HS Es) as [Hs' [Hr' _]].
    destruct (rcons_ok lenv labs Hinj HN ntm F HF Y s' K' HlY HwY Hs' Hr' EK) as [A [B C]].
    split; [exact A|split; [exact B|intros v]].
    refine (feq_trans _ _ _ (C v) _); rewrite !(R_seg lenv).
    refine (feq_trans _ _ _ (fs_cong lenv labs ntm s' _ _ v (sren_sp1 lenv labs ntm s' Hs' Hr') SemY) _).
    exact (sa_sem s s' E K HS Es EE v).
Qed.

Theorem canon_ok l : forall K, lw1 l -> canon F ntm l = Some K -> lnf K /\ lw1 K /\ forall v, feq (R K v) (R l v).
Proof.
  induction l as [|[s|L a] r IH]; intros K Hw; cbn [canon].
  - intros E; injection E as <-; split; [exact I|split; [constructor|intros v; apply feq_refl]].
  - inversion Hw as [|? ? HS Hr]; subst.
    destruct (canon F ntm r) as [K0|] eqn:E0; [|discriminate]; cbn [obind]; intros E.
    destruct (IH K0 Hr eq_refl) as [Hl0 [Hw0 Sem0]].
    destruct (cseg_ok s K0 K Hl0 Hw0 HS E) as [A [B C]].
    split; [exact A|split; [exact B|intros v]].
    exact (feq_trans _ _ _ (C v) (R_cong lenv labs ntm (LS s) _ _ HS Sem0 v)).
  - inversion Hw as [|? ? HL Hr]; subst.
    destruct (canon F ntm r) as [K0|] eqn:E0; [|discriminate]; cbn [option_map]; intros E; injection E as <-.
    destruct (IH K0 Hr eq_refl) as [Hl0 [Hw0 Sem0]].
    split; [split; assumption|split; [constructor; assumption|]].
    exact (R_cong lenv labs ntm (LA L a) _ _ I Sem0).
Qed.

(** Words that mean the same have the same canonical word. *)
Theorem canon_unique l m Kl Km : lw1 l -> lw1 m ->
  (forall aenv penv, lwden lenv (tenvT ntm) aenv penv l = lwden lenv (tenvT ntm) aenv penv m) ->
  canon F ntm l = Some Kl -> canon F ntm m = Some Km -> Kl = Km.
Proof.
  intros Hl Hm Heq El Em.
  destruct (canon_ok l Kl Hl El) as [Al [_ Cl]]; destruct (canon_ok m Km Hm Em) as [Am [_ Cm]].
  pose proof (lw_adequacy lenv ntm l m (lw1_lwok lenv labs ntm l Hl) (lw1_lwok lenv labs ntm m Hm) Heq) as Ad.
  apply (lw_unique lenv labs Hinj gtP gtP_irrefl gtP_trans gtP_keq Kl Km Al Am).
  intros v; exact (feq_trans _ _ _ (Cl v) (feq_trans _ _ _ (Ad v) (feq_sym _ _ (Cm v)))).
Qed.

(** And the canonical word means the same as the word. *)
Theorem canon_sound aenv penv l K : lw1 l -> canon F ntm l = Some K ->
  lwden lenv (tenvT ntm) aenv penv K = lwden lenv (tenvT ntm) aenv penv l.
Proof.
  intros Hw E; destruct (canon_ok l K Hw E) as [_ [HK Sem]].
  exact (lw_real lenv (tenvT ntm) aenv penv K l (lw1_lwok lenv labs ntm K HK) (lw1_lwok lenv labs ntm l Hw) Sem).
Qed.

End CanonOk.
