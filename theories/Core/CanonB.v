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
