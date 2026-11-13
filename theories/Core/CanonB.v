(** * Terms onto a canonical word

    [layer Z W]: a segment with terms in front of the canonical word [W],
    as a new layer: its targets go to their representatives in [W], its
    bound targets are renumbered, and the renumbering goes into [W].
    [bcore T W]: bound variables instantiated with terms, in front of
    [W]: the terms join the first layer, go on top of it, or go under
    it. *)

From Stdlib Require Import Arith List Lia Bool Sorted.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Unique Normal Layered LayeredUnique Order
  Canon Retarget LFree CanonF CanonR.
Import ListNotations.

Section Layer.

Variable F : order.
Variable labs : list lexp.
Variable ntm : nat.

Definition layer (Z : seg) (W : lword) : option lword :=
  match reroute F labs W Z with
  | Some Z' =>
      match W with
      | [] => Some [LS Z']
      | _ =>
          match renum1 F Z' with
          | Some (S'', io) => obind (match io with SNil => Some W | _ => rcons F ntm io W end) (fixlast F ntm S'')
          | None => None
          end
      end
  | None => None
  end.

End Layer.

Section LayerOk.

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
Local Notation lw1 := (lw1 lenv labs ntm).
Local Notation lnf := (lnf lenv labs gtP).
Local Notation segok := (segok lenv labs gtP).

Theorem layer_ok Z W K' : lnf W -> lw1 W -> sp1 Z -> sterm lenv Z ->
  (forall y u b k, R W y = FTerm u b k -> gtP (R W) k) ->
  layer F labs ntm Z W = Some K' -> lnf K' /\ lw1 K' /\ forall v, feq (R K' v) (R (LS Z :: W) v).
Proof.
  intros Hl Hw HZ HZt Hor; unfold layer.
  destruct (reroute F labs W Z) as [Z'|] eqn:ER; [|discriminate].
  destruct (reroute_ok lenv labs Hinj ntm F HF Htot W Z Z' Hw HZ ER) as [HZ' Hres].
  assert (Sem0 : forall v, feq (fs Z' (R W) v) (fs Z (R W) v)).
  { intros v; rewrite (res_free lenv labs ntm Z' _ v HZ'), (res_free lenv labs ntm Z _ v HZ), Hres.
    destruct (sres Z v) as [y|[[u b] s']]; cbn [rvres]; [exact (rv_feq lenv labs Hinj ntm F HF Htot W Hl Hw HN y)|apply feq_refl]. }
  assert (HZ't : sterm lenv Z') by (destruct HZt as [x [t Ex]]; exists x, t; rewrite Hres, Ex; reflexivity).
  assert (Hne : forall X, sterm lenv X -> X <> SNil) by (intros X [x [t E]] ->; discriminate E).
  destruct W as [|st Wr].
  - intros E; injection E as <-.
    split; [split; [exact (Hne Z' HZ't)|split; [exact I|left; split; [exact HZ't|exact (segok_nil lenv labs ntm Z' HZ')]]]|].
    split; [exact (lw1_one lenv labs ntm Z' HZ')|intros v; exact (Sem0 v)].
  - destruct (renum1 F Z') as [[S'' io]|] eqn:EN; [|discriminate].
    destruct (renum1_shape lenv labs ntm F HF Z' S'' io HN HZ' EN) as [HS'' [Hios Hior]].
    assert (HS''t : sterm lenv S'').
    { destruct HZ't as [x [t Ex]]; exists x, t; rewrite (renum1_comp lenv F HF Z' S'' io EN x) in Ex.
      destruct (sres S'' x) as [y|t']; [|exact Ex].
      rewrite (sres_ren lenv labs io _ Hior) in Ex; discriminate Ex. }
    assert (HK1' : forall K1', (match io with SNil => Some (st :: Wr) | _ => rcons F ntm io (st :: Wr) end) = Some K1' ->
                     lnf K1' /\ lw1 K1' /\ forall v, feq (R K1' v) (fs io (R (st :: Wr)) v)).
    { intros K1' E1; destruct io as [|h ts m r].
      - injection E1 as <-; split; [exact Hl|split; [exact Hw|intros v; rewrite (fs_nil lenv labs); apply feq_refl]].
      - exact (rcons_ok lenv labs Hinj HN ntm F HF _ _ K1' Hl Hw Hios Hior E1). }
    match goal with |- obind ?X _ = _ -> _ => destruct X as [K1'|] eqn:E1 end;
      [|cbn [obind]; intros H; discriminate H]; cbn [obind]; intros EF.
    destruct (HK1' K1' E1) as [HlK1' [HwK1' Sem1]].
    assert (Hro : forall x y, sres Z' x = inl y -> routed (R (st :: Wr)) y).
    { intros x y e; rewrite Hres in e; destruct (sres Z x) as [y0|t]; cbn [rvres] in e; [|discriminate].
      injection e as <-; exact (rv_routed lenv labs Hinj ntm F HF Htot _ Hl Hw HN y0). }
    assert (Hbi : forall y y', bound y -> bound y' -> (exists x, sres Z' x = inl y) -> (exists x', sres Z' x' = inl y') ->
                    feq (R (st :: Wr) y) (R (st :: Wr) y') -> y = y').
    { intros y y' Hy Hy' [x e] [x' e']; rewrite Hres in e, e'.
      destruct (sres Z x) as [y0|t]; cbn [rvres] in e; [|discriminate]; injection e as <-.
      destruct (sres Z x') as [y0'|t]; cbn [rvres] in e'; [|discriminate]; injection e' as <-.
      exact (rv_inj lenv labs Hinj ntm F HF Htot _ Hl Hw HN y0 y0' Hy Hy'). }
    destruct (fixlast_ok lenv labs Hinj ntm F HF S'' K1' K' HS'' HS''t HlK1' HwK1'
                (fun Hlast => segok_renum lenv labs HN ntm F HF Z' S'' io (st :: Wr) K1' HZ' Hro Hor Hbi EN Sem1 Hlast) EF)
      as [A [B C]].
    split; [exact A|split; [exact B|intros v]].
    apply (feq_trans _ _ _ (C v)); rewrite (R_seg lenv S'' K1' v), (R_seg lenv Z (st :: Wr) v).
    apply (feq_trans _ _ _ (fs_cong lenv labs ntm S'' _ _ v HS'' Sem1)).
    apply (feq_trans _ _ _ (feq_sym _ _ (renum1_free lenv labs ntm F HF Z' S'' io HN HZ' EN _ v))).
    exact (Sem0 v).
Qed.

End LayerOk.

(** ** Bound variables instantiated with terms *)

Section Bcore.

Variable F : order.
Variable labs : list lexp.
Variable ntm : nat.

(** [h₍ᵢ₎ ↦ Tᵢ] on bound variables below [|T|], the others shifted down. *)
Definition ET (T : list ntgt) : option seg := sbuild F [(LNone, (T, 0))].

(** The terms joined to the bound entry of the first layer [S1]. *)
Definition join (T : list ntgt) (S1 : seg) : option seg :=
  let '(xs, m) := bent F S1 in
  sbuild F ((LNone, (T ++ tl_list xs, m)) :: map (fun e => (fst (fst e), (tl_list (snd (fst e)), snd e))) (ents S1)).

Fixpoint bcore (fuel : nat) (T : list ntgt) (K : lword) {struct fuel} : option lword :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match ET T with
      | None => None
      | Some E =>
          match K with
          | LS S1 :: K1 =>
              if has_terms S1 then
                match pcmp F K (List.length K) (List.length K1) with
                | Some Eq => option_map (fun J => LS J :: K1) (join T S1)
                | Some Gt => layer F labs ntm E K
                | _ => None
                end
              else layer F labs ntm E K
          | _ => layer F labs ntm E K
          end
      end
  end.

End Bcore.

Section BcoreOk.

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
Local Notation segok := (segok lenv labs gtP).

Definition tterm (t : ntgt) : Prop := match t with NBind u w b => w = WEnd SNil /\ b = None /\ u < ntm | _ => False end.

Lemma ET_ok T E : Forall tterm T -> ET F T = Some E ->
  sp1 E /\ forall l i, sres E (mk_rvar l i) =
    match l with None => if i <? List.length T then tres lenv (nth i T (NVar LNone 0)) else inl (mk_rvar None (i - List.length T))
               | Some _ => inl (mk_rvar l i) end.
Proof.
  intros HT EE; split.
  - destruct (sbuild_shape lenv labs F HF _ _ EE) as [Hs [Ht _]]; [intros h xs m [Eh|[]]; injection Eh as <- _ _; exact HN|].
    split; [exact Hs|apply Forall_forall; intros t Hin; destruct (Ht t Hin) as [h [xs [m [[Eh|[]] Hx]]]]].
    injection Eh as <- <- <-; pose proof (proj1 (Forall_forall _ _) HT t Hx) as H; destruct t; [destruct H|exact H].
  - intros l i; rewrite (sres_sbuild lenv F HF _ _ EE l i); cbn [find fst].
    destruct l as [x|]; cbn [label_eqb Normalise.lden]; [reflexivity|].
    unfold etgt; destruct (i <? List.length T); [reflexivity|do 2 f_equal; lia].
Qed.

Lemma sp1_tterm T : Forall tterm T -> Forall tp1 T.
Proof. intros H; eapply Forall_impl; [|exact H]; intros [h j|u w b]; cbn; tauto. Qed.

Lemma lw1_lgood W : lw1 W -> lgood lenv labs W.
Proof.
  intros Hw; eapply Forall_impl; [|exact Hw]; intros [s|L a]; cbn.
  - intros Hs; split; [exact (sshape_dist lenv labs _ _ (proj1 Hs))|].
    intros h ts m Hin; apply (sshape_labs lenv labs false s (proj1 Hs) h (tl_list ts) m).
    rewrite <- ents_sents; apply (in_map (fun e => (fst (fst e), tl_list (snd (fst e)), snd e)) _ _ Hin).
  - intros [Hso Hf]; split; [intros p Hp; exact (proj1 (proj1 (Forall_forall _ _) Hf p Hp))|].
    clear Hf; induction L as [|p L IH]; [constructor|]; inversion Hso as [|? ? Hs Hall]; subst; constructor; [|exact (IH Hs)].
    intros Hin; apply in_map_iff in Hin as [q [Eq Hq]]; pose proof (proj1 (Forall_forall _ _) Hall q Hq) as H; cbn in H.
    rewrite Eq in H; exact (olabel_lt_irrefl _ H).
Qed.

(** What a word whose first step has no terms sends to a term has a
    smaller payload. *)
Lemma hor_noterm K : lnf K -> lw1 K -> (match K with LS S1 :: _ => has_terms S1 = false | _ => True end) ->
  forall y u b k, R K y = FTerm u b k -> gtP (R K) k.
Proof.
  intros Hl Hw Hk y u b k E.
  assert (Atom : forall L a K2 z, lnf K2 -> R (LA L a :: K2) z = FTerm u b k -> exists e, e < natl (LA L a :: K2) /\ deep e k).
  { intros L a K2 z H2 Ez; rewrite (R_atom lenv) in Ez; unfold latom in Ez; destruct (_ <? _); [|discriminate Ez].
    destruct (tdeep lenv labs gtP K2 H2 z u b k Ez) as [e [He Hd]]; exists e; split; [cbn [natl]; lia|exact Hd]. }
  assert (Fin : forall e, e < natl K -> deep e k -> gtP (R K) k) by (intros e He Hd; exact (gtP_deep _ _ _ _ (deep_R lenv K) Hd He)).
  destruct K as [|[S1|L a] K1]; [discriminate E| |destruct (Atom L a K1 y (proj2 Hl) E) as [e [He Hd]]; exact (Fin e He Hd)].
  inversion Hw as [|? ? HS Hw1]; subst; destruct Hl as [_ [Hl1 [[[x [t Ex]] _]|[_ [Hren Hr]]]]].
  - exfalso; rewrite (sres_ren lenv labs S1 x (noterms_sren lenv labs ntm S1 HS Hk)) in Ex; discriminate Ex.
  - rewrite (R_seg lenv), (fs_ren lenv labs S1 _ y Hren) in E.
    destruct Hr as [->|[L [a [K2 [-> _]]]]]; [discriminate E|].
    destruct (Atom L a K2 _ (proj2 Hl1) E) as [e [He Hd]]; exact (Fin e He Hd).
Qed.

Lemma hor_gt S1 K1 : lnf (LS S1 :: K1) -> lw1 (LS S1 :: K1) -> has_terms S1 = true -> gtP (R (LS S1 :: K1)) (R K1) ->
  forall y u b k, R (LS S1 :: K1) y = FTerm u b k -> gtP (R (LS S1 :: K1)) k.
Proof.
  intros Hl Hw Ht Hgt y u b k E; inversion Hw as [|? ? HS _]; subst.
  destruct Hl as [_ [_ [[_ HSo]|[_ [Hren _]]]]]; [|rewrite (sren_noterms labs S1 Hren) in Ht; discriminate].
  rewrite (R_seg lenv), (res_free lenv labs ntm S1 _ y HS) in E.
  destruct (sres S1 y) as [y'|[[u' b'] s']] eqn:Ey.
  - exact (gtP_trans _ _ _ Hgt (so_order _ _ _ _ _ HSo y' u b k E)).
  - injection E as <- <- <-; apply (gtP_keq _ _ (R K1) _ (keq_refl _)); [apply keq_refl|exact Hgt].
Qed.

Lemma join_sres T S1 J : sp1 S1 -> join F T S1 = Some J -> forall l i,
  sres J (mk_rvar l i) = match l with
                         | None => if i <? List.length T then tres lenv (nth i T (NVar LNone 0)) else sres S1 (mk_rvar None (i - List.length T))
                         | Some _ => sres S1 (mk_rvar l i)
                         end.
Proof.
  intros HS; unfold join; pose proof (bent_find lenv F HF S1) as Eb.
  destruct (bent F S1) as [xs m]; intros E l i; rewrite (sres_sbuild lenv F HF _ _ E l i); cbn [find fst].
  destruct l as [x|]; cbn [label_eqb Normalise.lden].
  - rewrite (find_map_lab lenv (fun e => (fst (fst e), (tl_list (snd (fst e)), snd e))) (fun e => fst (fst e)) fst (ents S1))
      by (intros e; reflexivity).
    rewrite (sres_ents lenv S1 (Some x) i).
    destruct (find (fun e : lexp * tlist * nat => label_eqb (lden (fst (fst e))) (Some x)) (ents S1)) as [[[h ts] m']|]; reflexivity.
  - rewrite (sres_ents lenv S1 None (i - List.length T)).
    destruct (find (fun e => label_eqb (lden (fst (fst e))) None) (ents S1)) as [[[h ts] m']|] eqn:Ef;
      injection Eb as -> ->; unfold etgt; rewrite length_app; cbn [tl_list List.length].
    + apply find_some in Ef as [Eh _]; cbn [fst] in Eh; apply label_eqb_eq in Eh; rewrite Eh.
      destruct (Nat.ltb_spec i (List.length T)) as [H1|H1]; [rewrite (proj2 (Nat.ltb_lt _ _)) by lia; rewrite app_nth1 by exact H1; reflexivity|].
      rewrite app_nth2 by exact H1; destruct (Nat.ltb_spec (i - List.length T) (List.length (tl_list ts))) as [H2|H2].
      * rewrite (proj2 (Nat.ltb_lt _ _)) by lia; reflexivity.
      * rewrite (proj2 (Nat.ltb_ge _ _)) by lia; do 2 f_equal; lia.
    + destruct (Nat.ltb_spec i (List.length T)) as [H1|H1]; [rewrite (proj2 (Nat.ltb_lt _ _)) by lia; rewrite app_nth1 by exact H1; reflexivity|].
      rewrite (proj2 (Nat.ltb_ge _ _)) by lia; do 2 f_equal; lia.
Qed.

Lemma join_ok T S1 K1 J : Forall tterm T -> T <> [] -> sp1 S1 -> segok S1 K1 -> join F T S1 = Some J ->
  sp1 J /\ sterm lenv J /\ segok J K1.
Proof.
  intros HT Hne HS HSo E; pose proof (join_sres T S1 J HS E) as Hj.
  set (n := List.length T) in *.
  assert (HJ : sp1 J).
  { unfold join in E; destruct (bent F S1) as [xs m] eqn:Eb.
    pose proof (bent_find lenv F HF S1) as Eb'; rewrite Eb in Eb'.
    assert (Hlab : forall h ts m0, In (h, ts, m0) (ents S1) -> In h labs).
    { intros h ts m0 Hin; apply (sshape_labs lenv labs false S1 (proj1 HS) h (tl_list ts) m0).
      rewrite <- ents_sents; apply (in_map (fun e => (fst (fst e), tl_list (snd (fst e)), snd e)) _ _ Hin). }
    destruct (sbuild_shape lenv labs F HF _ _ E) as [Hs [Ht _]].
    { intros h xs0 m0 [Eh|Hin]; [injection Eh as <- _ _; exact HN|].
      apply in_map_iff in Hin as [[[h' ts'] m'] [Eh Hin]]; injection Eh as <- _ _; exact (Hlab _ _ _ Hin). }
    split; [exact Hs|apply Forall_forall; intros t Hin; destruct (Ht t Hin) as [h [xs0 [m0 [He Hx]]]]].
    destruct He as [Eh|He].
    - injection Eh as <- <- <-; apply in_app_or in Hx as [Hx|Hx]; [exact (proj1 (Forall_forall _ _) (sp1_tterm T HT) t Hx)|].
      destruct (find (fun e => label_eqb (lden (fst (fst e))) None) (ents S1)) as [[[h' ts'] m']|] eqn:Ef;
        injection Eb' as -> ->; [|destruct Hx].
      apply find_some in Ef as [_ Hin']; exact (proj1 (Forall_forall _ _) (proj2 HS) t (ents_stgts S1 _ _ _ t Hin' Hx)).
    - apply in_map_iff in He as [[[h' ts'] m'] [Eh He]]; injection Eh as <- <- <-.
      exact (proj1 (Forall_forall _ _) (proj2 HS) t (ents_stgts S1 _ _ _ t He Hx)). }
  set (sg := fun x : rvar => match v_label x with None => mk_rvar None (v_index x - n) | Some _ => x end).
  set (tau := fun x : rvar => match v_label x with None => mk_rvar None (n + v_index x) | Some _ => x end).
  assert (Hjs : forall x y, sres J x = inl y -> sres S1 (sg x) = inl y /\ x = tau (sg x)).
  { intros [[l|] i] y e; rewrite Hj in e; unfold sg, tau; cbn [v_label v_index]; [split; [exact e|reflexivity]|].
    destruct (Nat.ltb_spec i n) as [Hi|Hi].
    - exfalso; pose proof (proj1 (Forall_forall _ _) HT _ (nth_In T (NVar LNone 0) Hi)) as Ht.
      destruct (nth i T (NVar LNone 0)); [destruct Ht|discriminate e].
    - split; [exact e|f_equal; lia]. }
  assert (Hsj : forall z y, sres S1 z = inl y -> sres J (tau z) = inl y).
  { intros [[l|] i] y e; unfold tau; cbn [v_label v_index]; rewrite Hj; [exact e|].
    rewrite (proj2 (Nat.ltb_ge _ _)) by lia; replace (n + i - n) with i by lia; exact e. }
  assert (Vt : forall a b, vlt a b -> vlt (tau a) (tau b)).
  { intros [la ia] [lb ib] [H|[El H]]; unfold tau, vlt; cbn [v_label v_index] in *.
    - left; destruct la, lb; exact H.
    - right; subst lb; destruct la; cbn; split; [reflexivity|lia|reflexivity|lia]. }
  split; [exact HJ|split].
  - destruct T as [|t T']; [destruct (Hne eq_refl)|].
    exists (mk_rvar None 0); rewrite Hj; cbn [List.length nth]; inversion HT as [|? ? Ht _]; subst.
    destruct t as [|u w b]; [destruct Ht|eexists; reflexivity].
  - destruct HSo as [Hsh Hp Hord Hlast Hroute Hpay Hhit Hbinj Hsrc]; split.
    + exact (proj1 HJ).
    + exact (sp1_spure _ _ _ _ HJ).
    + exact Hord.
    + exact Hlast.
    + intros x y e; exact (Hroute _ _ (proj1 (Hjs x y e))).
    + intros x u n0 s0 i e; pose proof (sres_pure1 lenv labs ntm J x HJ) as P; rewrite e in P; destruct P as [P _]; discriminate P.
    + intros Hr y Hy; destruct (Hhit Hr y Hy) as [z Ez]; exists (tau z); exact (Hsj z y Ez).
    + exact Hbinj.
    + intros Hr x x' i j e e' Hij.
      destruct (Hsrc Hr (sg x) (sg x') i j (proj1 (Hjs _ _ e)) (proj1 (Hjs _ _ e')) Hij) as [x0 [E0 Hm]].
      exists (tau x0); split; [exact (Hsj _ _ E0)|].
      intros x'' e''; destruct (Hjs _ _ e'') as [E2 Ex]; rewrite Ex; exact (Vt _ _ (Hm _ E2)).
Qed.

Lemma join_sem T S1 K1 J E : Forall tterm T -> sp1 S1 -> join F T S1 = Some J -> ET F T = Some E ->
  keq (R (LS S1 :: K1)) (R K1) -> sp1 J -> forall v, feq (R (LS J :: K1) v) (R (LS E :: LS S1 :: K1) v).
Proof.
  intros HT HS EJ EE Hk HJ [l i]; destruct (ET_ok T E HT EE) as [HE HEs].
  rewrite (R_seg lenv J), (R_seg lenv E), (res_free lenv labs ntm J _ _ HJ), (res_free lenv labs ntm E _ _ HE).
  rewrite (join_sres T S1 J HS EJ), HEs; destruct l as [x|].
  - rewrite (R_seg lenv S1), (res_free lenv labs ntm S1 _ _ HS); destruct (sres S1 (mk_rvar (Some x) i)) as [y|[[u b] s']]; apply feq_refl.
  - destruct (i <? List.length T) eqn:Ei.
    + apply Nat.ltb_lt in Ei; pose proof (proj1 (Forall_forall _ _) HT _ (nth_In T (NVar LNone 0) Ei)) as Ht.
      destruct (nth i T (NVar LNone 0)) as [|u w b]; [destruct Ht|destruct Ht as [-> [-> _]]]; cbn [tres feq].
      split; [reflexivity|split; [reflexivity|intros y Hy; exact (feq_sym _ _ (Hk y (Hy eq_refl)))]].
    + rewrite (R_seg lenv S1), (res_free lenv labs ntm S1 _ _ HS).
      destruct (sres S1 (mk_rvar None (i - List.length T))) as [y|[[u b] s']]; apply feq_refl.
Qed.

Theorem bcore_ok fuel T K K' E : Forall tterm T -> T <> [] -> lnf K -> lw1 K -> ET F T = Some E ->
  bcore F labs ntm fuel T K = Some K' -> lnf K' /\ lw1 K' /\ forall v, feq (R K' v) (R (LS E :: K) v).
Proof.
  intros HT Hne Hl Hw EE; destruct fuel as [|fuel']; [discriminate|cbn [bcore]; rewrite EE].
  destruct (ET_ok T E HT EE) as [HE HEs].
  assert (HEt : sterm lenv E).
  { destruct T as [|t T']; [destruct (Hne eq_refl)|]; exists (mk_rvar None 0); rewrite HEs; cbn [List.length nth Nat.ltb].
    inversion HT as [|? ? Ht _]; subst; destruct t as [|u w b]; [destruct Ht|eexists; reflexivity]. }
  assert (New : forall K0, lnf K0 -> lw1 K0 -> (forall y u b k, R K0 y = FTerm u b k -> gtP (R K0) k) ->
                  layer F labs ntm E K0 = Some K' -> lnf K' /\ lw1 K' /\ forall v, feq (R K' v) (R (LS E :: K0) v)).
  { intros K0 H1 H2 H3 H4; exact (layer_ok lenv labs Hinj HN ntm F HF Htot E K0 K' H1 H2 HE HEt H3 H4). }
  destruct K as [|[S1|L a] K1]; [exact (New _ Hl Hw (hor_noterm _ Hl Hw I))| |exact (New _ Hl Hw (hor_noterm _ Hl Hw I))].
  destruct (has_terms S1) eqn:Ht; [|exact (New _ Hl Hw (hor_noterm _ Hl Hw Ht))].
  assert (Suf1 : suf (LS S1 :: K1) (List.length (LS S1 :: K1)) = LS S1 :: K1) by apply suf_all.
  assert (Suf2 : suf (LS S1 :: K1) (List.length K1) = K1) by (rewrite (suf_cons _ _ _ (le_n _)); apply suf_all).
  destruct (pcmp F (LS S1 :: K1) (List.length (LS S1 :: K1)) (List.length K1)) as [c|] eqn:Ec; [|discriminate].
  pose proof (pcmp_sound lenv labs Hinj F HF (LS S1 :: K1) (List.length (LS S1 :: K1)) (List.length K1) c Hl (lw1_lgood _ Hw) (le_n _) ltac:(cbn; lia) Ec) as Hc.
  rewrite Suf1, Suf2 in Hc.
  destruct c; [| |exact (New _ Hl Hw (hor_gt S1 K1 Hl Hw Ht Hc))]; [|discriminate].
  destruct (join F T S1) as [J|] eqn:EJ; [|discriminate]; cbn [option_map]; intros EK; injection EK as <-.
  inversion Hw as [|? ? HS HK1]; subst.
  destruct Hl as [_ [Hl1 [[_ HSo]|[_ [Hren _]]]]]; [|rewrite (sren_noterms labs S1 Hren) in Ht; discriminate].
  destruct (join_ok T S1 K1 J HT Hne HS HSo EJ) as [HJ [HJt HJo]].
  split; [split; [intros ->; destruct HJt as [x [t Ex]]; discriminate Ex|split; [exact Hl1|left; split; assumption]]|].
  split; [constructor; assumption|exact (join_sem T S1 K1 J E HT HS EJ EE Hc HJ)].
Qed.

End BcoreOk.
