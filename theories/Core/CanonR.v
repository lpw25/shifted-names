(** * Classes of variables in a canonical word

    In a word in the normal form [LayeredUnique.lnf], two variables mean
    the same exactly when they reach the same target of the first
    segment with terms ([follow1_char]).  The canonical word uses this
    to send each variable to the least variable that means the same. *)

From Stdlib Require Import Arith List Lia Bool Sorted.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Unique Normal Layered LayeredUnique Order
  Canon Retarget LFree CanonF.
Import ListNotations.

Section Follow1.

Variable F : order.

(** Follow [h₍ᵢ₎] through renamings and atoms to the first segment with
    terms, and take its target there. *)
Fixpoint follow1 (l : lword) (h : lexp) (i : nat) : option desc :=
  match l with
  | [] => Some (DV h i)
  | LS s :: r =>
      match seg_tgt F s h i with
      | Some t =>
          if has_terms s then Some (DT t (List.length r))
          else match t with NVar g j => follow1 r g j | NBind _ _ _ => None end
      | None => None
      end
  | LA L a :: r =>
      match lcnt F h L with
      | Some c => if i <? c then follow1 r h i else Some (DS a h (i - c) (List.length r))
      | None => None
      end
  end.

End Follow1.

Section Char.

Variable lenv : list label.
Variable labs : list lexp.
Hypothesis Hinj : forall h h', In h labs -> In h' labs -> lden lenv h = lden lenv h' -> h = h'.
Variable ntm : nat.
Variable F : order.
Hypothesis HF : facts_ok lenv F.

Local Notation lden := (lden lenv).
Local Notation R := (R lenv).
Local Notation fs := (fs lenv).
Local Notation ft := (ft lenv).
Local Notation sres := (sres lenv).
Local Notation sp1 := (sp1 lenv labs ntm).
Local Notation tp1 := (tp1 labs ntm).
Local Notation lw1 := (lw1 lenv labs ntm).
Local Notation lnf := (lnf lenv labs gtP).
Local Notation segok := (segok lenv labs gtP).

Lemma follow1_lt l : forall h i d, follow1 F l h i = Some d ->
  match d with DV _ _ => True | DT _ e => e < List.length l | DS _ _ _ e => e < List.length l end.
Proof.
  induction l as [|[s|L a] r IH]; intros h i d; cbn [follow1].
  - intros E; injection E as <-; exact I.
  - destruct (seg_tgt F s h i) as [t|]; [|discriminate]; destruct (has_terms s).
    + intros E; injection E as <-; cbn; lia.
    + destruct t as [g j|]; [|discriminate]; intros E; specialize (IH _ _ _ E); destruct d; cbn in *; try lia; exact I.
  - destruct (lcnt F h L) as [c|]; [|discriminate]; destruct (i <? c).
    + intros E; specialize (IH _ _ _ E); destruct d; cbn in *; try lia; exact I.
    + intros E; injection E as <-; cbn; lia.
Qed.

(** Two targets of a segment with terms in normal form mean the same
    after the rest only if they are the same. *)
Lemma tgt_char s r t t' : segok s r ->
  (exists x, sres s x = tres lenv t) -> (exists x', sres s x' = tres lenv t') -> tp1 t -> tp1 t' ->
  (feq (ft t (R r)) (ft t' (R r)) <-> t = t').
Proof.
  intros HS [x Ex] [x' Ex'] Ht Ht'; split; [|intros <-; apply feq_refl].
  destruct HS as [_ _ Hord _ Hroute _ _ Hbinj _].
  assert (Tv : forall g j u w b, tp1 (NBind u w b) -> ~ feq (R r (mk_rvar (lden g) j)) (ft (NBind u w b) (R r))).
  { intros g j u w b [-> [-> _]] Fe; cbn [ft] in Fe.
    destruct (R r (mk_rvar (lden g) j)) as [|u0 b0 k0|] eqn:E0; cbn [feq] in Fe; try contradiction.
    destruct Fe as [_ [-> Fk]].
    apply (gtP_irrefl (R r) k0); [|exact (Hord _ _ _ _ E0)].
    intros z Hz; apply feq_sym; refine (feq_trans _ _ _ (Fk z (fun _ => Hz)) _); cbn [fw]; rewrite (fs_nil lenv labs); apply feq_refl. }
  destruct t as [g j|u w b], t' as [g' j'|u' w' b']; cbn [ft].
  - intros Fe; cbn [tres] in Ex, Ex'.
    destruct (Hroute _ _ Ex) as [Rn Rb]; destruct (Hroute _ _ Ex') as [Rn' Rb'].
    set (y := mk_rvar (lden g) j) in *; set (y' := mk_rvar (lden g') j') in *.
    assert (Ey : y = y').
    { destruct (named_or_bound y) as [Hy|Hy], (named_or_bound y') as [Hy'|Hy'].
      - destruct (vlt_total y y') as [Hl|[E|Hl]]; [|exact E|].
        + destruct (Rn' Hy' y Hy Fe Hl).
        + destruct (Rn Hy y' Hy' (feq_sym _ _ Fe) Hl).
      - destruct (Rb' Hy' y Hy Fe).
      - destruct (Rb Hy y' Hy' (feq_sym _ _ Fe)).
      - exact (Hbinj _ _ Hy Hy' Fe). }
    unfold y, y' in Ey; injection Ey as Eg ->; rewrite (Hinj g g' Ht Ht' Eg); reflexivity.
  - intros Fe; destruct (Tv g j u' w' b' Ht' Fe).
  - intros Fe; destruct (Tv g' j' u w b Ht (feq_sym _ _ Fe)).
  - destruct Ht as [-> [-> _]], Ht' as [-> [-> _]]; cbn [feq]; intros [-> _]; reflexivity.
Qed.

Lemma stuck_mix r L a y z : ~ feq (R r y) (FStuck a z (fun y => R r (shiftL lenv L y))).
Proof.
  intros Fe; destruct (R r y) as [|u b k|a0 z0 k0] eqn:E; cbn [feq] in Fe; try contradiction.
  destruct Fe as [_ [_ Fk]].
  destruct (nstuck_R lenv r y a0 z0 k0 E) as [d [Hd Hk]].
  pose proof (deep_shift lenv _ L _ (deep_R lenv r)) as Hk'.
  pose proof (deep_unique d (natl r) k0 _ Hk Hk' (fun i => Fk (mk_rvar lbig i))); lia.
Qed.

Theorem follow1_char W : lnf W -> lw1 W -> forall h i h' i' d d', In h labs -> In h' labs ->
  follow1 F W h i = Some d -> follow1 F W h' i' = Some d' ->
  (feq (R W (mk_rvar (lden h) i)) (R W (mk_rvar (lden h') i')) <-> d = d').
Proof.
  induction W as [|[s|L a] r IH]; intros Hl Hw h i h' i' d d' Hh Hh'; cbn [follow1].
  - intros E E'; injection E as <-; injection E' as <-; unfold LayeredUnique.R; cbn [flw feq]; split.
    + intros Ev; injection Ev as Eh ->; rewrite (Hinj h h' Hh Hh' Eh); reflexivity.
    + intros Ed; injection Ed as -> ->; reflexivity.
  - inversion Hw as [|? ? Hs Hr]; subst; destruct Hl as [_ [Hlr Hor]].
    destruct (seg_tgt F s h i) as [t|] eqn:Et; [|discriminate].
    destruct (seg_tgt F s h' i') as [t'|] eqn:Et'; [|discriminate].
    rewrite !(R_seg lenv), (seg_tgt_free lenv F HF s h i t _ Et), (seg_tgt_free lenv F HF s h' i' t' _ Et').
    assert (Hp : forall g k u, seg_tgt F s g k = Some u -> In g labs -> tp1 u).
    { intros g k u E Hg; destruct (seg_tgt_in lenv F HF s g k u E) as [[j ->]|H]; [exact Hg|].
      exact (proj1 (Forall_forall _ _) (proj2 Hs) u H). }
    destruct (has_terms s) eqn:Ht.
    + intros E E'; injection E as <-; injection E' as <-.
      destruct Hor as [[_ HS]|[_ [Hren _]]]; [|rewrite (sren_noterms labs s Hren) in Ht; discriminate].
      rewrite (tgt_char s r t t' HS (ex_intro _ _ (seg_tgt_sres lenv F HF s h i t Et))
                 (ex_intro _ _ (seg_tgt_sres lenv F HF s h' i' t' Et')) (Hp _ _ _ Et Hh) (Hp _ _ _ Et' Hh')).
      split; [intros ->; reflexivity|intros E; injection E as ->; reflexivity].
    + destruct t as [g j|]; [|discriminate]; destruct t' as [g' j'|]; [|discriminate]; intros E E'; cbn [ft].
      exact (IH Hlr Hr g j g' j' d d' (Hp _ _ _ Et Hh) (Hp _ _ _ Et' Hh') E E').
  - inversion Hw as [|? ? HL Hr]; subst; destruct Hl as [_ Hlr].
    destruct (lcnt F h L) as [c|] eqn:Ec; [|discriminate]; destruct (lcnt F h' L) as [c'|] eqn:Ec'; [|discriminate].
    rewrite !(R_atom lenv); unfold latom; cbn [v_label v_index].
    rewrite (lcnt_sound lenv F HF _ _ _ Ec), (lcnt_sound lenv F HF _ _ _ Ec').
    destruct (i <? c) eqn:E1, (i' <? c') eqn:E2.
    + exact (IH Hlr Hr h i h' i' d d' Hh Hh').
    + intros E E'; injection E' as <-; split; [intros Fe; destruct (stuck_mix _ _ _ _ _ Fe)|intros ->].
      pose proof (follow1_lt r _ _ _ E) as H; cbn in H; lia.
    + intros E E'; injection E as <-; split; [intros Fe; destruct (stuck_mix _ _ _ _ _ (feq_sym _ _ Fe))|intros <-].
      pose proof (follow1_lt r _ _ _ E') as H; cbn in H; lia.
    + intros E E'; injection E as <-; injection E' as <-; cbn [feq]; split.
      * intros [_ [Ez _]]; injection Ez as Eh Ei; rewrite (Hinj h h' Hh Hh' Eh) in *; rewrite Ei; reflexivity.
      * intros Ed; injection Ed as -> Ei; rewrite Ei; split; [reflexivity|split; [reflexivity|intros y; apply feq_refl]].
Qed.

End Char.
