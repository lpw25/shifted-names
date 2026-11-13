(** * The canonical words of [CanonW] satisfy the conditions with branches

    A word in the normal form [LayeredUnique.lnf] whose terms are all pure
    ([lw1]) satisfies [BUnique.lnfB]: its terms have empty branches, its
    domain is everything, and the no-hop rule holds because no payload has
    more atoms than the line after it. *)

From Stdlib Require Import Arith List Lia Bool Sorted.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Unique Normal Layered LayeredUnique Order
  BUnique Canon Retarget LFree CanonF CanonR CanonB CanonW.
Import ListNotations.

Section Bridge.

Variable lenv : list label.
Variable labs : list lexp.
Variable ntm : nat.

Local Notation R := (LayeredUnique.R lenv).
Local Notation flw := (flw lenv).
Local Notation lnf := (lnf lenv labs gtP route_id (num_first lenv)).
Local Notation sp1 := (sp1 lenv labs ntm).
Local Notation lw1 := (lw1 lenv labs ntm).

Lemma psok_nil : psok lenv labs SNil.
Proof. split; [exact (conj (Sorted.SSorted_nil _) (Forall_nil _))|split; [exact (Forall_nil _)|intros v _; reflexivity]]. Qed.

Lemma sp1_bres s x u b w : sp1 s -> bres lenv s x = inr (u, b, w) -> w = WEnd SNil /\ b = None.
Proof.
  intros [_ Ht] E; unfold bres in E; destruct (Normalise.sget lenv (v_label x) s) as [[ts m]|] eqn:Eg; [|discriminate E].
  destruct (Nat.ltb_spec (v_index x) (tlen ts)) as [Hi|Hi]; [|discriminate E].
  pose proof (proj1 (Forall_forall _ _) Ht _ (sget_tgts lenv _ _ _ _ Eg _ (tnth_in _ _ Hi))) as Hp.
  destruct (tnth ts (v_index x)) as [h j|u' w' b']; cbn [btres] in E; [discriminate E|injection E as <- <- <-].
  destruct Hp as [-> [-> _]]; split; reflexivity.
Qed.

Lemma lw1_treach r y rt u b w : lw1 r -> treach lenv r y = Some (rt, (u, b, w)) -> w = WEnd SNil /\ b = None.
Proof.
  revert y; induction r as [|[s|L a] r IH]; intros y Hw E; cbn [treach] in E; try discriminate.
  inversion Hw as [|? ? Hs Hr]; subst.
  destruct (bres lenv s y) as [y'|t] eqn:Ey; [exact (IH _ Hr E)|injection E as -> ->].
  exact (sp1_bres _ _ _ _ _ Hs Ey).
Qed.

Lemma sres_bres_inr s : sterm lenv s -> btrm lenv s.
Proof.
  intros [v [[[u b] s'] E]]; exists v; unfold LayeredUnique.sres, bres in *.
  destruct (Normalise.sget lenv (v_label v) s) as [[ts m]|]; [|discriminate E].
  destruct (v_index v <? tlen ts); [|discriminate E].
  destruct (tnth ts (v_index v)) as [h j|u' w b']; [discriminate E|eexists; reflexivity].
Qed.

Theorem lnf_lnfB l : lnf l -> lw1 l -> lnfB lenv labs gtP route_id 0 FVar None l.
Proof.
  induction l as [|[s|L a] r IH]; intros Hl Hw; cbn [BUnique.lnfB BUnique.lnfL]; [exact I| |].
  - inversion Hw as [|? ? Hs Hr]; subst; destruct Hl as [Hne [Hlr Hc]].
    split; [exact Hne|exists None; split; [exact (IH Hlr Hr)|]].
    destruct Hc as [[Ht HS]|[Hsh [Hren Hend]]].
    + left; split; [exact (sres_bres_inr s Ht)|].
      destruct HS as [A B C D E G H I0 J]; constructor.
      * exact A.
      * apply Forall_forall; intros t Hin; pose proof (proj1 (Forall_forall _ _) (proj2 Hs) t Hin) as Ht'.
        destruct t; cbn in *; tauto.
      * intros y rt [[u b] w] Et; destruct (lw1_treach r y rt u b w Hr Et) as [-> ->].
        destruct (treach_term lenv r FVar y rt u None (WEnd SNil) Et) as [Ey _].
        exact (C y u None _ Ey).
      * intros G0 EG Hk; exact (sres_bres_inr G0 (D G0 EG Hk)).
      * intros x y _ Ex; apply E; apply bres_sres, Ex.
      * intros; exact I.
      * exact I.
      * intros Hne' y Hy _; destruct (H Hne' y Hy) as [x Ex]; exists x; split; [exact I|apply bres_sres, Ex].
      * exact I0.
      * exact J.
      * intros x u b w Ex; destruct (sp1_bres s x u b w Hs Ex) as [-> ->].
        split; [exact I|split; [exact psok_nil|split; [intros [H0|H0]; [destruct (H0 eq_refl)|destruct (H0 eq_refl)]|]]].
        split; [intros _ _; reflexivity|intros H0; destruct (H0 eq_refl)].
    + right; split; [exact Hsh|split; [exact Hren|split; [exact I|split; [intros; exact I|]]]].
      destruct Hend as [->|[L [a [r2 [-> Hp]]]]]; [left; reflexivity|right; exists L, a, r2].
      split; [reflexivity|split; [exact Hp|intros y _ _ H0; destruct (H0 eq_refl)]].
  - inversion Hw as [|? ? HL Hr]; subst; destruct Hl as [HLok Hlr].
    split; [exact HLok|split; [exact I|split; [exact (IH Hlr Hr)|]]].
    intros y u b k d e _ Ey Hd He Hlt.
    assert (He0 : e = 0) by exact (deep_unique _ _ _ _ He deep_FVar (fun i => feq_refl _)); subst e.
    destruct (tdeep lenv labs gtP route_id (num_first lenv) r Hlr y u b k Ey) as [d' [Hd' Hdk]].
    assert (d = d') by exact (deep_unique _ _ _ _ Hd Hdk (fun i => feq_refl _)); lia.
Qed.

End Bridge.
