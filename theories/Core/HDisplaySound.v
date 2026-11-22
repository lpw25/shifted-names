(** * The display means the word

    [HDisplay.display] turns a normal form into an expression with
    shared definitions.  Here: in every comprehension model consistent
    with the facts, the expression means the word, given that each
    shared definition's atom means the definition ([display_sound]).

    The steps of the display are proved in the model directly on the
    words [HRefine] reads off the table ([RId], [RWord]):
    - [relw]: the word up to a suffix, read relative to it;
    - [unw]: the word without a final pop;
    - each rule of [dbody], with references to cells read through an
      environment [ρ] that agrees with the cells already shown;
    - [assemble], which inlines references and keeps shared ones. *)

From Stdlib Require Import List PArith NArith Bool FMapPositive Arith Lia.
From ShiftedNames.Core Require Import Label Normalise KnownOrder Comp CSound HRefine.
From ShiftedNames.Core Require HNorm CNorm HDisplay.
Import ListNotations.

Section Sound.

Variable F : order.
Hypothesis Hirr : forall a, lt_known F a a = false.
Hypothesis Htrans : forall a b c, lt_known F a b = true -> lt_known F b c = true -> lt_known F a c = true.
Variable M : cmodel.
Hypothesis HM : ccons F M.

Local Notation U := (cU M).
Local Notation wden := (@wden M).
Local Notation vden := (@vden M).
Local Notation sden := (@sden M).
Local Notation wpre := (CSound.wpre M).

(** ** Reading words *)

Lemma RId_one T cw : Inv T -> RId T 1 cw -> cw = [].
Proof.
  intros I H; inversion H as [|i s t cs cw' Hc _ _]; [reflexivity|].
  destruct (inv_next T I 1 _ Hc) as [_ N]; contradiction.
Qed.

Lemma hword_spec T : Inv T -> forall i cw, RId T i cw ->
  forall fuel, (Pos.to_nat i <= fuel)%nat ->
  RWord T (HDisplay.hword T fuel i) cw /\ HNorm.wid (HDisplay.hword T fuel i) = i.
Proof.
  intros I i cw H; induction H as [|i s t cs cw Hc Hs Ht IH]; intros fuel Hf.
  - destruct fuel; cbn; split; (apply RWNil || reflexivity).
  - destruct fuel as [|f]; [lia|]; cbn [HDisplay.hword].
    destruct (inv_next T I i _ Hc) as [_ N1].
    replace (Pos.eqb i 1) with false by (symmetry; apply Pos.eqb_neq, N1).
    unfold HDisplay.cell; fold (cellof T i); rewrite Hc.
    pose proof (inv_tail T I i s t Hc) as Lt.
    destruct (IH f ltac:(lia)) as [R E].
    split; [|reflexivity]; apply RWCons; [rewrite E; exact Hc|exact Hs|exact R].
Qed.

Lemma hw_spec T i cw : Inv T -> RId T i cw -> RWord T (HDisplay.hw T i) cw /\ HNorm.wid (HDisplay.hw T i) = i.
Proof. intros I H; apply (hword_spec T I i cw H); lia. Qed.

Lemma RId_func T i cw cw' : Inv T -> RId T i cw -> RId T i cw' -> cw = cw'.
Proof. intros I H1 H2; apply (proj1 (R_func T I) i cw H1 cw' H2). Qed.

Lemma RId_mono T T' i cw : Ext T T' -> RId T i cw -> RId T' i cw.
Proof. intros X H; apply (proj1 (R_mono T T' X)), H. Qed.

Lemma RStep_mono T T' x cx : Ext T T' -> RStep T x cx -> RStep T' x cx.
Proof. intros X H; apply (proj1 (proj2 (R_mono T T' X))), H. Qed.

Lemma RVal_mono T T' v cv : Ext T T' -> RVal T v cv -> RVal T' v cv.
Proof. intros X H; apply (proj2 (proj2 (R_mono T T' X))), H. Qed.

(** ** Relative to a suffix *)

Section Rel.

Variables (s : positive) (cs : CNorm.cword).

Definition RelMemo T (m : HDisplay.memo) : Prop :=
  forall p p', PositiveMap.find p m = Some p' ->
    exists cp cp', RId T p cp /\ RId T p' cp' /\ forall c, wden cp c = wden cp' (wden cs c).

Lemma RelMemo_mono T T' m : Ext T T' -> RelMemo T m -> RelMemo T' m.
Proof.
  intros X H p p' E; destruct (H p p' E) as [cp [cp' [H1 [H2 H3]]]].
  exists cp, cp'; split; [apply (RId_mono _ _ _ _ X H1)|split; [apply (RId_mono _ _ _ _ X H2)|exact H3]].
Qed.

Lemma relw_S f w T m : HDisplay.relw F s (S f) w T m =
  match w with
  | [] => if Pos.eqb s 1 then Some ([], T, m) else None
  | (x, i) :: w' =>
      if Pos.eqb i s then Some ([], T, m)
      else match HDisplay.relst F s f x T m with
           | Some (x', T1, m1) =>
               match HDisplay.relw F s f w' T1 m1 with
               | Some (w1, T2, m2) => let '(w2, T3) := HNorm.hcons x' w1 T2 in Some (w2, T3, m2)
               | None => None
               end
           | None => None
           end
  end.
Proof. reflexivity. Qed.

Lemma relst_S f x T m : HDisplay.relst F s (S f) x T m =
  match x with
  | HNorm.SE h v => match HDisplay.relv F s f v T m with Some (v', T1, m1) => Some (HNorm.SE h v', T1, m1) | None => None end
  | _ => Some (x, T, m)
  end.
Proof. reflexivity. Qed.

Lemma relv_S f v T m : HDisplay.relv F s (S f) v T m =
  match v with
  | HNorm.VLook g j x => if Pos.eqb x s then Some (HNorm.VVar g j, T, m) else None
  | HNorm.VVar g j => let '(v', T1) := HNorm.lookup F g j (HDisplay.hw T s) T in
                      if HNorm.val_eqb v' v then Some (v, T1, m) else None
  | HNorm.VTerm u None p =>
      match PositiveMap.find p m with
      | Some p' => Some (HNorm.VTerm u None p', T, m)
      | None =>
          match HDisplay.relw F s f (HDisplay.hw T p) T m with
          | Some (w', T1, m1) => Some (HNorm.VTerm u None (HNorm.wid w'), T1, PositiveMap.add p (HNorm.wid w') m1)
          | None => None
          end
      end
  | HNorm.VTerm _ (Some _) _ => None
  end.
Proof. reflexivity. Qed.

Lemma rel_spec : forall fuel,
  (forall w T m w' T' m' cw, Inv T -> RId T s cs -> RelMemo T m -> RWord T w cw ->
     HDisplay.relw F s fuel w T m = Some (w', T', m') ->
     Inv T' /\ Ext T T' /\ RelMemo T' m' /\ exists cw', RWord T' w' cw' /\ forall c, wden cw c = wden cw' (wden cs c))
  /\ (forall x T m x' T' m' cx, Inv T -> RId T s cs -> RelMemo T m -> RStep T x cx ->
     HDisplay.relst F s fuel x T m = Some (x', T', m') ->
     Inv T' /\ Ext T T' /\ RelMemo T' m' /\ exists cx', RStep T' x' cx' /\ forall y c, sden cx y c = sden cx' y (wden cs c))
  /\ (forall v T m v' T' m' cv, Inv T -> RId T s cs -> RelMemo T m -> RVal T v cv ->
     HDisplay.relv F s fuel v T m = Some (v', T', m') ->
     Inv T' /\ Ext T T' /\ RelMemo T' m' /\ exists cv', RVal T' v' cv' /\ forall c, vden cv c = vden cv' (wden cs c)).
Proof.
  induction fuel as [|f IH]; [repeat split; intros; discriminate|].
  destruct IH as [IHw [IHs IHv]]; split; [|split].
  - intros w T m w' T' m' cw I Hs Hm Hw E; rewrite relw_S in E.
    destruct w as [|[x i] w0].
    + destruct (Pos.eqb s 1) eqn:Es; [apply Pos.eqb_eq in Es|discriminate]; cbv iota beta zeta in E; injection E as <- <- <-.
      rewrite Es in Hs; inversion Hw; subst; pose proof (RId_one T cs I Hs) as ->.
      split; [exact I|split; [apply Ext_refl|split; [exact Hm|exists []; split; [apply RWNil|reflexivity]]]].
    + destruct (Pos.eqb i s) eqn:Ei.
      * apply Pos.eqb_eq in Ei; subst i; cbv iota beta zeta in E; injection E as <- <- <-.
        pose proof (RWord_RId T _ _ Hw) as Hi; cbn [HNorm.wid] in Hi.
        pose proof (RId_func T s _ _ I Hi Hs) as ->.
        split; [exact I|split; [apply Ext_refl|split; [exact Hm|exists []; split; [apply RWNil|reflexivity]]]].
      * inversion Hw as [|x0 i0 w1 cx cw0 Hc Hx Hw0]; subst.
        destruct (HDisplay.relst F s f x T m) as [[[x' T1] m1]|] eqn:E1; [|cbv iota beta zeta in E; discriminate].
        destruct (IHs x T m x' T1 m1 cx I Hs Hm Hx E1) as [I1 [X1 [Hm1 [cx' [Hx' Sx]]]]].
        destruct (HDisplay.relw F s f w0 T1 m1) as [[[w1 T2] m2]|] eqn:E2; [|cbv iota beta zeta in E; discriminate].
        destruct (IHw w0 T1 m1 w1 T2 m2 cw0 I1 (RId_mono _ _ _ _ X1 Hs) Hm1 (RWord_mono _ _ X1 _ _ Hw0) E2)
          as [I2 [X2 [Hm2 [cw1 [Hw1 Sw]]]]].
        destruct (HNorm.hcons x' w1 T2) as [w2 T3] eqn:E3; cbv iota beta zeta in E; injection E as <- <- <-.
        destruct (hcons_spec T2 x' w1 cx' cw1 w2 T3 I2 (RStep_mono _ _ _ _ X2 Hx') Hw1 E3) as [I3 [X3 Hw2]].
        split; [exact I3|split; [apply (Ext_trans _ _ _ X1 (Ext_trans _ _ _ X2 X3))|split]].
        { apply (RelMemo_mono _ _ _ X3 Hm2). }
        exists (cx' :: cw1); split; [exact Hw2|]; intros c; cbn [CSound.wden].
        rewrite Sw; apply Sx.
  - intros x T m x' T' m' cx I Hs Hm Hx E; rewrite relst_S in E.
    destruct x as [h v|h|a].
    + destruct (HDisplay.relv F s f v T m) as [[[v' T1] m1]|] eqn:E1; [|cbv iota beta zeta in E; discriminate]; cbv iota beta zeta in E; injection E as <- <- <-.
      inversion Hx as [h0 v0 cv Hv| |]; subst.
      destruct (IHv v T m v' T1 m1 cv I Hs Hm Hv E1) as [I1 [X1 [Hm1 [cv' [Hv' Sv]]]]].
      split; [exact I1|split; [exact X1|split; [exact Hm1|]]].
      exists (CNorm.SE h cv'); split; [constructor; exact Hv'|]; intros y c; cbn [CSound.sden]; rewrite Sv; reflexivity.
    + cbv iota beta zeta in E; injection E as <- <- <-; split; [exact I|split; [apply Ext_refl|split; [exact Hm|]]].
      exists cx; split; [exact Hx|]; intros y c; inversion Hx; subst; reflexivity.
    + cbv iota beta zeta in E; injection E as <- <- <-; split; [exact I|split; [apply Ext_refl|split; [exact Hm|]]].
      exists cx; split; [exact Hx|]; intros y c; inversion Hx; subst; reflexivity.
  - intros v T m v' T' m' cv I Hs Hm Hv E; rewrite relv_S in E.
    destruct v as [g j|u [b|] p|g j x].
    + destruct (HNorm.lookup F g j (HDisplay.hw T s) T) as [v1 T1] eqn:El.
      destruct (HNorm.val_eqb v1 (HNorm.VVar g j)) eqn:Ev; [|cbv iota beta zeta in E; discriminate]; apply hval_eqb_eq in Ev; subst v1.
      cbv iota beta zeta in E; injection E as <- <- <-.
      destruct (hw_spec T s cs I Hs) as [Hws _].
      destruct (lookup_spec F Hirr Htrans T g _ cs I Hws j _ T1 El) as [I1 [X1 Rl]].
      inversion Hv; subst; assert (El' : CNorm.VVar g j = CNorm.lookup F g j cs) by (inversion Rl; auto).
      split; [exact I1|split; [exact X1|split; [apply (RelMemo_mono _ _ _ X1 Hm)|]]].
      exists (CNorm.VVar g j); split; [constructor|]; intros c.
      pose proof (lookup_sound M F HM g cs j c) as L; rewrite <- El' in L; cbn in L |- *.
      exact L.
    + discriminate.
    + inversion Hv as [|u0 b0 p0 cp Hp|]; subst.
      destruct (PositiveMap.find p m) as [p'|] eqn:Fm.
      * cbv iota beta zeta in E; injection E as <- <- <-; destruct (Hm p p' Fm) as [cp0 [cp' [H1 [H2 H3]]]].
        pose proof (RId_func T p _ _ I Hp H1) as ->.
        split; [exact I|split; [apply Ext_refl|split; [exact Hm|]]].
        exists (CNorm.VTerm u None cp'); split; [constructor; exact H2|]; intros c.
        rewrite !CSound.vden_term, H3; reflexivity.
      * destruct (hw_spec T p cp I Hp) as [Hwp _].
        destruct (HDisplay.relw F s f (HDisplay.hw T p) T m) as [[[w' T1] m1]|] eqn:E1; [|cbv iota beta zeta in E; discriminate].
        cbv iota beta zeta in E; injection E as <- <- <-.
        destruct (IHw _ T m w' T1 m1 cp I Hs Hm Hwp E1) as [I1 [X1 [Hm1 [cw' [Hw' Sw]]]]].
        split; [exact I1|split; [exact X1|split]].
        { intros q q' Eq; destruct (Pos.eq_dec q p) as [->|Nq].
          - rewrite PositiveMap.gss in Eq; injection Eq as <-.
            exists cp, cw'; split; [apply (RId_mono _ _ _ _ X1 Hp)|split; [apply RWord_RId, Hw'|exact Sw]].
          - rewrite PositiveMap.gso in Eq by exact Nq; apply Hm1, Eq. }
        exists (CNorm.VTerm u None cw'); split; [constructor; apply RWord_RId, Hw'|]; intros c.
        rewrite !CSound.vden_term, Sw; reflexivity.
    + destruct (Pos.eqb x s) eqn:Ex; [apply Pos.eqb_eq in Ex; subst x|discriminate]; cbv iota beta zeta in E; injection E as <- <- <-.
      inversion Hv as [| |g0 j0 x0 cx Hx]; subst.
      pose proof (RId_func T s _ _ I Hx Hs) as ->.
      split; [exact I|split; [apply Ext_refl|split; [exact Hm|]]].
      exists (CNorm.VVar g j); split; [constructor|]; intros c.
      rewrite CSound.vden_look, CSound.vden_var; reflexivity.
Qed.

End Rel.

(** ** Without a final pop *)

Lemma kd_dist g h : HNorm.kd F h g = true -> known_distinct F h g.
Proof. intros K; apply (kd_known F), K. Qed.

Lemma cname_other h g j (c : U) : HNorm.kd F h g = true -> cname h j (cpop g c) = cname h j c.
Proof.
  intros K; apply (sdist_cname M F HM h (CNorm.SW g) j c c).
  exists g; split; [reflexivity|apply known_distinct_sym, kd_dist, K].
Qed.

Section Unlift.

Variable g : lexp.

Lemma unw_S f w T m : HDisplay.unw F g (S f) w T m =
  match w with
  | [] => None
  | (x, _) :: w' =>
      if match x with HNorm.SW h => lexp_eqb h g && HDisplay.all_sw_kd F g w' | _ => false end then Some (w', T, m)
      else match HDisplay.unst F g f x T m with
           | Some (x', T1, m1) =>
               match HDisplay.unw F g f w' T1 m1 with
               | Some (w1, T2, m2) => let '(w2, T3) := HNorm.hcons x' w1 T2 in Some (w2, T3, m2)
               | None => None
               end
           | None => None
           end
  end.
Proof. reflexivity. Qed.

Lemma unall_S f w T m : HDisplay.unall F g (S f) w T m =
  match w with
  | [] => Some ([], T, m)
  | (x, _) :: w' =>
      match HDisplay.unst F g f x T m with
      | Some (x', T1, m1) =>
          match HDisplay.unall F g f w' T1 m1 with
          | Some (w1, T2, m2) => let '(w2, T3) := HNorm.hcons x' w1 T2 in Some (w2, T3, m2)
          | None => None
          end
      | None => None
      end
  end.
Proof. reflexivity. Qed.

Lemma unst_S f x T m : HDisplay.unst F g (S f) x T m =
  match x with
  | HNorm.SE h v => match HDisplay.unv F g f v T m with Some (v', T1, m1) => Some (HNorm.SE h v', T1, m1) | None => None end
  | _ => Some (x, T, m)
  end.
Proof. reflexivity. Qed.

Lemma unv_S f v T m : HDisplay.unv F g (S f) v T m =
  match v with
  | HNorm.VVar h j =>
      if lexp_eqb h g then match j with 0 => None | S j' => Some (HNorm.VVar h j', T, m) end
      else if HNorm.kd F h g then Some (v, T, m) else None
  | HNorm.VLook h j x =>
      match PositiveMap.find (xO x) m with
      | Some x' => Some (HNorm.VLook h j x', T, m)
      | None =>
          match HDisplay.unw F g f (HDisplay.hw T x) T m with
          | Some (w', T1, m1) => Some (HNorm.VLook h j (HNorm.wid w'), T1, PositiveMap.add (xO x) (HNorm.wid w') m1)
          | None => None
          end
      end
  | HNorm.VTerm u None p =>
      match PositiveMap.find (xI p) m with
      | Some p' => Some (HNorm.VTerm u None p', T, m)
      | None =>
          let w := HDisplay.hw T p in
          let r := match HDisplay.unw F g f w T m with
                   | Some r => Some r
                   | None => if lexp_eqb g LNone && HDisplay.named_only w then HDisplay.unall F g f w T m else None
                   end in
          match r with
          | Some (w', T1, m1) => Some (HNorm.VTerm u None (HNorm.wid w'), T1, PositiveMap.add (xI p) (HNorm.wid w') m1)
          | None => None
          end
      end
  | HNorm.VTerm _ (Some _) _ => None
  end.
Proof. reflexivity. Qed.

Definition UnMemo T (m : HDisplay.memo) : Prop :=
  forall k k', PositiveMap.find k m = Some k' ->
    match k with
    | xO x => exists cx cx', RId T x cx /\ RId T k' cx' /\ forall c, wden cx c = wden cx' (cpop g c)
    | xI p => exists cp cp', RId T p cp /\ RId T k' cp' /\
                forall u c, cterm u None (wden cp c) = cterm u None (wden cp' (cpop g c))
    | xH => True
    end.

Lemma UnMemo_mono T T' m : Ext T T' -> UnMemo T m -> UnMemo T' m.
Proof.
  intros X H k k' E; specialize (H k k' E); destruct k as [x|p|]; [| |exact I];
    destruct H as [c1 [c2 [H1 [H2 H3]]]]; exists c1, c2;
    (split; [apply (RId_mono _ _ _ _ X H1)|split; [apply (RId_mono _ _ _ _ X H2)|exact H3]]).
Qed.

Lemma UnMemo_add_I T m p p' : UnMemo T m ->
  (exists cp cp', RId T p cp /\ RId T p' cp' /\ forall u c, cterm u None (wden cp c) = cterm u None (wden cp' (cpop g c))) ->
  UnMemo T (PositiveMap.add (xI p) p' m).
Proof.
  intros H N k k' E; destruct (Pos.eq_dec k (xI p)) as [->|Nk].
  - rewrite PositiveMap.gss in E; injection E as <-; exact N.
  - rewrite PositiveMap.gso in E by exact Nk; apply H, E.
Qed.

Lemma UnMemo_add_O T m x x' : UnMemo T m ->
  (exists cx cx', RId T x cx /\ RId T x' cx' /\ forall c, wden cx c = wden cx' (cpop g c)) ->
  UnMemo T (PositiveMap.add (xO x) x' m).
Proof.
  intros H N k k' E; destruct (Pos.eq_dec k (xO x)) as [->|Nk].
  - rewrite PositiveMap.gss in E; injection E as <-; exact N.
  - rewrite PositiveMap.gso in E by exact Nk; apply H, E.
Qed.

Lemma all_sw_kd_pop w cw T : RWord T w cw -> HDisplay.all_sw_kd F g w = true ->
  forall c, cpop g (wden cw c) = wden cw (cpop g c).
Proof.
  intros H; induction H as [|x i w cx cw Hc Hx Hw IH]; intros A c; [reflexivity|].
  destruct x as [h v|h|a]; cbn [HDisplay.all_sw_kd] in A; try discriminate.
  apply andb_true_iff in A as [K A]; inversion Hx; subst; cbn [CSound.wden CSound.sden].
  rewrite <- IH by exact A.
  destruct (kd_pops F M HM h g (kd_dist g h K) (wden cw c)) as [E _]; symmetry; exact E.
Qed.

Lemma named_pop T w cw : RWord T w cw -> HDisplay.named_only w = true ->
  Forall (fun s => exists h, CNorm.slabel s = Some h /\ h <> LNone) cw.
Proof.
  intros H; induction H as [|x i w cx cw Hc Hx Hw IH]; intros A; [constructor|].
  destruct x as [h v|h|a]; cbn [HDisplay.named_only] in A; try discriminate;
    apply andb_true_iff in A as [N A]; apply negb_true_iff, lexp_eqb_false_iff in N;
    inversion Hx; subst; (constructor; [exists h; split; [reflexivity|exact N]|apply IH, A]).
Qed.

Lemma pop_bound_named h (y : U) t : h <> LNone -> cpop LNone (cpush h y t) = cpush h (cpop LNone y) t.
Proof. intros N; apply (kd_pop_push F M HM); right; apply (lt_known_bound F), N. Qed.

Lemma pops_bound_named h (y : U) : h <> LNone -> cpop LNone (cpop h y) = cpop h (cpop LNone y).
Proof. intros N; apply (kd_pops F M HM); right; apply (lt_known_bound F), N. Qed.

Lemma un_spec : forall fuel,
  (forall w T m w' T' m' cw, Inv T -> UnMemo T m -> RWord T w cw ->
     HDisplay.unw F g fuel w T m = Some (w', T', m') ->
     Inv T' /\ Ext T T' /\ UnMemo T' m' /\ exists cw', RWord T' w' cw' /\ forall c, wden cw c = wden cw' (cpop g c))
  /\ (forall w T m w' T' m' cw, Inv T -> UnMemo T m -> RWord T w cw -> g = LNone ->
     Forall (fun s => exists h, CNorm.slabel s = Some h /\ h <> LNone) cw ->
     HDisplay.unall F g fuel w T m = Some (w', T', m') ->
     Inv T' /\ Ext T T' /\ UnMemo T' m' /\ exists cw', RWord T' w' cw' /\ (forall c, wden cw' (cpop g c) = cpop g (wden cw c))
       /\ Forall (fun s => exists h, CNorm.slabel s = Some h /\ h <> LNone) cw')
  /\ (forall x T m x' T' m' cx, Inv T -> UnMemo T m -> RStep T x cx ->
     HDisplay.unst F g fuel x T m = Some (x', T', m') ->
     Inv T' /\ Ext T T' /\ UnMemo T' m' /\ exists cx', RStep T' x' cx' /\ CNorm.slabel cx' = CNorm.slabel cx /\
       forall y c, sden cx y c = sden cx' y (cpop g c))
  /\ (forall v T m v' T' m' cv, Inv T -> UnMemo T m -> RVal T v cv ->
     HDisplay.unv F g fuel v T m = Some (v', T', m') ->
     Inv T' /\ Ext T T' /\ UnMemo T' m' /\ exists cv', RVal T' v' cv' /\ forall c, vden cv c = vden cv' (cpop g c)).
Proof.
  induction fuel as [|f IH]; [repeat split; intros; discriminate|].
  destruct IH as [IHw [IHa [IHs IHv]]]; split; [|split; [|split]].
  - intros w T m w' T' m' cw I Hm Hw E; rewrite unw_S in E.
    destruct w as [|[x i] w0]; [discriminate|].
    inversion Hw as [|x0 i0 w1 cx cw0 Hc Hx Hw0]; subst.
    destruct (match x with HNorm.SW h => lexp_eqb h g && HDisplay.all_sw_kd F g w0 | _ => false end) eqn:B.
    + injection E as <- <- <-.
      destruct x as [h v|h|a]; try discriminate; apply andb_true_iff in B as [Bh B]; apply lexp_eqb_eq in Bh; subst h.
      split; [exact I|split; [apply Ext_refl|split; [exact Hm|exists cw0; split; [exact Hw0|]]]].
      intros c; inversion Hx; subst; cbn [CSound.wden CSound.sden]; apply (all_sw_kd_pop w0 cw0 T Hw0 B).
    + destruct (HDisplay.unst F g f x T m) as [[[x' T1] m1]|] eqn:E1; [|cbv iota beta zeta in E; discriminate].
      destruct (IHs x T m x' T1 m1 cx I Hm Hx E1) as [I1 [X1 [Hm1 [cx' [Hx' [_ Sx]]]]]].
      destruct (HDisplay.unw F g f w0 T1 m1) as [[[w2 T2] m2]|] eqn:E2; [|cbv iota beta zeta in E; discriminate].
      destruct (IHw w0 T1 m1 w2 T2 m2 cw0 I1 Hm1 (RWord_mono _ _ X1 _ _ Hw0) E2) as [I2 [X2 [Hm2 [cw2 [Hw2 Sw]]]]].
      destruct (HNorm.hcons x' w2 T2) as [w3 T3] eqn:E3; cbv iota beta zeta in E; injection E as <- <- <-.
      destruct (hcons_spec T2 x' w2 cx' cw2 w3 T3 I2 (RStep_mono _ _ _ _ X2 Hx') Hw2 E3) as [I3 [X3 Hw3]].
      split; [exact I3|split; [apply (Ext_trans _ _ _ X1 (Ext_trans _ _ _ X2 X3))|split; [apply (UnMemo_mono _ _ _ X3 Hm2)|]]].
      exists (cx' :: cw2); split; [exact Hw3|]; intros c; cbn [CSound.wden]; rewrite Sw; apply Sx.
  - intros w T m w' T' m' cw I Hm Hw Hg Hn E; rewrite unall_S in E.
    destruct w as [|[x i] w0].
    + injection E as <- <- <-; inversion Hw; subst.
      split; [exact I|split; [apply Ext_refl|split; [exact Hm|exists []; split; [apply RWNil|split; [reflexivity|constructor]]]]].
    + inversion Hw as [|x0 i0 w1 cx cw0 Hc Hx Hw0]; subst; inversion Hn as [|? ? Hl Hn0]; subst.
      destruct (HDisplay.unst F g f x T m) as [[[x' T1] m1]|] eqn:E1; [|cbv iota beta zeta in E; discriminate].
      destruct (IHs x T m x' T1 m1 cx I Hm Hx E1) as [I1 [X1 [Hm1 [cx' [Hx' [Lx Sx]]]]]].
      destruct (HDisplay.unall F g f w0 T1 m1) as [[[w2 T2] m2]|] eqn:E2; [|cbv iota beta zeta in E; discriminate].
      destruct (IHa w0 T1 m1 w2 T2 m2 cw0 I1 Hm1 (RWord_mono _ _ X1 _ _ Hw0) Hg Hn0 E2) as [I2 [X2 [Hm2 [cw2 [Hw2 [Sw Hn2]]]]]].
      destruct (HNorm.hcons x' w2 T2) as [w3 T3] eqn:E3; cbv iota beta zeta in E; injection E as <- <- <-.
      destruct (hcons_spec T2 x' w2 cx' cw2 w3 T3 I2 (RStep_mono _ _ _ _ X2 Hx') Hw2 E3) as [I3 [X3 Hw3]].
      split; [exact I3|split; [apply (Ext_trans _ _ _ X1 (Ext_trans _ _ _ X2 X3))|split; [apply (UnMemo_mono _ _ _ X3 Hm2)|]]].
      exists (cx' :: cw2); split; [exact Hw3|split; [|constructor; [rewrite Lx; exact Hl|exact Hn2]]].
      intros c; cbn [CSound.wden]; rewrite Sw.
      destruct Hl as [h [Lh Nh]]; rewrite (Sx (wden cw0 c) c); rewrite Hg.
      rewrite <- Lx in Lh; destruct cx' as [h' v'|h'|a']; cbn in Lh |- *; [injection Lh as ->|injection Lh as ->|discriminate].
      * symmetry; apply pop_bound_named; exact Nh.
      * symmetry; apply pops_bound_named, Nh.
  - intros x T m x' T' m' cx I Hm Hx E; rewrite unst_S in E.
    destruct x as [h v|h|a].
    + destruct (HDisplay.unv F g f v T m) as [[[v' T1] m1]|] eqn:E1; [|cbv iota beta zeta in E; discriminate].
      cbv iota beta zeta in E; injection E as <- <- <-; inversion Hx as [h0 v0 cv Hv| |]; subst.
      destruct (IHv v T m v' T1 m1 cv I Hm Hv E1) as [I1 [X1 [Hm1 [cv' [Hv' Sv]]]]].
      split; [exact I1|split; [exact X1|split; [exact Hm1|]]].
      exists (CNorm.SE h cv'); split; [constructor; exact Hv'|split; [reflexivity|]]; intros y c; cbn [CSound.sden]; rewrite Sv; reflexivity.
    + injection E as <- <- <-; split; [exact I|split; [apply Ext_refl|split; [exact Hm|]]].
      exists cx; split; [exact Hx|split; [reflexivity|]]; intros y c; inversion Hx; subst; reflexivity.
    + injection E as <- <- <-; split; [exact I|split; [apply Ext_refl|split; [exact Hm|]]].
      exists cx; split; [exact Hx|split; [reflexivity|]]; intros y c; inversion Hx; subst; reflexivity.
  - intros v T m v' T' m' cv I Hm Hv E; rewrite unv_S in E.
    destruct v as [h j|u [b|] p|h j x].
    + inversion Hv; subst.
      destruct (lexp_eqb h g) eqn:Eh.
      * apply lexp_eqb_eq in Eh; subst h; destruct j as [|j]; [discriminate|]; injection E as <- <- <-.
        split; [exact I|split; [apply Ext_refl|split; [exact Hm|]]].
        exists (CNorm.VVar g j); split; [constructor|]; intros c; cbn [CSound.vden].
        symmetry; apply (cname_pop M).
      * destruct (HNorm.kd F h g) eqn:K; [|discriminate]; injection E as <- <- <-.
        split; [exact I|split; [apply Ext_refl|split; [exact Hm|]]].
        exists (CNorm.VVar h j); split; [constructor|]; intros c; cbn [CSound.vden].
        symmetry; apply cname_other, K.
    + discriminate.
    + inversion Hv as [|u0 b0 p0 cp Hp|]; subst.
      destruct (PositiveMap.find (xI p) m) as [p'|] eqn:Fm.
      * injection E as <- <- <-; destruct (Hm (xI p) p' Fm) as [cp0 [cp' [H1 [H2 H3]]]].
        pose proof (RId_func T p _ _ I Hp H1) as ->.
        split; [exact I|split; [apply Ext_refl|split; [exact Hm|]]].
        exists (CNorm.VTerm u None cp'); split; [constructor; exact H2|]; intros c.
        rewrite !CSound.vden_term; apply H3.
      * destruct (hw_spec T p cp I Hp) as [Hwp _]; cbv zeta in E.
        destruct (HDisplay.unw F g f (HDisplay.hw T p) T m) as [[[w1 T1] m1]|] eqn:E1.
        -- cbv iota beta zeta in E; injection E as <- <- <-.
           destruct (IHw _ T m w1 T1 m1 cp I Hm Hwp E1) as [I1 [X1 [Hm1 [cw1 [Hw1 Sw]]]]].
           split; [exact I1|split; [exact X1|split]].
           { apply UnMemo_add_I; [exact Hm1|].
             exists cp, cw1; split; [apply (RId_mono _ _ _ _ X1 Hp)|split; [apply RWord_RId, Hw1|]].
             intros u0 c; rewrite Sw; reflexivity. }
           exists (CNorm.VTerm u None cw1); split; [constructor; apply RWord_RId, Hw1|]; intros c.
           rewrite !CSound.vden_term, Sw; reflexivity.
        -- cbv iota beta zeta in E.
           destruct (lexp_eqb g LNone && HDisplay.named_only (HDisplay.hw T p)) eqn:B; [|discriminate].
           apply andb_true_iff in B as [Bg Bn]; apply lexp_eqb_eq in Bg.
           destruct (HDisplay.unall F g f (HDisplay.hw T p) T m) as [[[w1 T1] m1]|] eqn:E2; [|discriminate].
           injection E as <- <- <-.
           destruct (IHa _ T m w1 T1 m1 cp I Hm Hwp Bg (named_pop T _ cp Hwp Bn) E2) as [I1 [X1 [Hm1 [cw1 [Hw1 [Sw _]]]]]].
           assert (St : forall u0 c, cterm u0 None (wden cp c) = cterm u0 None (wden cw1 (cpop g c))).
           { intros u0 c; rewrite Sw, Bg; symmetry; apply (proj2 HM). }
           split; [exact I1|split; [exact X1|split]].
           { apply UnMemo_add_I; [exact Hm1|].
             exists cp, cw1; split; [apply (RId_mono _ _ _ _ X1 Hp)|split; [apply RWord_RId, Hw1|exact St]]. }
           exists (CNorm.VTerm u None cw1); split; [constructor; apply RWord_RId, Hw1|]; intros c.
           rewrite !CSound.vden_term; apply St.
    + inversion Hv as [| |h0 j0 x0 cx Hx]; subst.
      destruct (PositiveMap.find (xO x) m) as [x'|] eqn:Fm.
      * injection E as <- <- <-; destruct (Hm (xO x) x' Fm) as [cx0 [cx' [H1 [H2 H3]]]].
        pose proof (RId_func T x _ _ I Hx H1) as ->.
        split; [exact I|split; [apply Ext_refl|split; [exact Hm|]]].
        exists (CNorm.VLook h j cx'); split; [constructor; exact H2|]; intros c.
        rewrite !CSound.vden_look, H3; reflexivity.
      * destruct (hw_spec T x cx I Hx) as [Hwx _].
        destruct (HDisplay.unw F g f (HDisplay.hw T x) T m) as [[[w1 T1] m1]|] eqn:E1; [|cbv iota beta zeta in E; discriminate].
        cbv iota beta zeta in E; injection E as <- <- <-.
        destruct (IHw _ T m w1 T1 m1 cx I Hm Hwx E1) as [I1 [X1 [Hm1 [cw1 [Hw1 Sw]]]]].
        split; [exact I1|split; [exact X1|split]].
        { apply UnMemo_add_O; [exact Hm1|].
          exists cx, cw1; split; [apply (RId_mono _ _ _ _ X1 Hx)|split; [apply RWord_RId, Hw1|exact Sw]]. }
        exists (CNorm.VLook h j cw1); split; [constructor; apply RWord_RId, Hw1|]; intros c.
        rewrite !CSound.vden_look, Sw; reflexivity.
Qed.

End Unlift.

(** ** The rules, in the model *)

(** Entries and their readings. *)
Definition REnts T (es : list (lexp * HNorm.val)) (ces : CNorm.cword) : Prop :=
  Forall2 (fun hv cs => RStep T (HNorm.SE (fst hv) (snd hv)) cs) es ces.

Lemma REnts_mono T T' es ces : Ext T T' -> REnts T es ces -> REnts T' es ces.
Proof. intros X H; eapply Forall2_impl; [|exact H]; intros a b; apply RStep_mono, X. Qed.

Lemma take_se_spec T w cw es R : RWord T w cw -> HDisplay.take_se w = (es, R) ->
  exists ces cR, cw = ces ++ cR /\ REnts T es ces /\ RWord T R cR.
Proof.
  intros H; revert es R; induction H as [|x i w cx cw Hc Hx Hw IH]; intros es R E.
  - injection E as <- <-; exists [], []; split; [reflexivity|split; [constructor|apply RWNil]].
  - destruct x as [h v|h|a]; cbn [HDisplay.take_se] in E.
    + destruct (HDisplay.take_se w) as [l r] eqn:E1; injection E as <- <-.
      destruct (IH l r eq_refl) as [ces [cR [-> [He HR]]]].
      exists (cx :: ces), cR; split; [reflexivity|split; [constructor; [exact Hx|exact He]|exact HR]].
    + injection E as <- <-; exists [], (cx :: cw); split; [reflexivity|split; [constructor|apply RWCons; assumption]].
    + injection E as <- <-; exists [], (cx :: cw); split; [reflexivity|split; [constructor|apply RWCons; assumption]].
Qed.

Lemma take_sw_spec T w cw hs R : RWord T w cw -> HDisplay.take_sw w = (hs, R) ->
  exists cR, cw = map CNorm.SW hs ++ cR /\ RWord T R cR.
Proof.
  intros H; revert hs R; induction H as [|x i w cx cw Hc Hx Hw IH]; intros hs R E.
  - injection E as <- <-; exists []; split; [reflexivity|apply RWNil].
  - destruct x as [h v|h|a]; cbn [HDisplay.take_sw] in E.
    + injection E as <- <-; exists (cx :: cw); split; [reflexivity|apply RWCons; assumption].
    + destruct (HDisplay.take_sw w) as [l r] eqn:E1; injection E as <- <-.
      destruct (IH l r eq_refl) as [cR [-> HR]]; inversion Hx; subst.
      exists cR; split; [reflexivity|exact HR].
    + injection E as <- <-; exists (cx :: cw); split; [reflexivity|apply RWCons; assumption].
Qed.

Lemma wids_RId T R cR z : Inv T -> RWord T R cR -> In z (HDisplay.wids R) -> exists cz, RId T z cz.
Proof.
  intros I H; induction H as [|y i w cy cw Hc Hy Hw IH]; cbn; [contradiction|].
  intros [<-|Hin]; [|apply IH, Hin].
  exists (cy :: cw); apply (RCons T i y (HNorm.wid w)); [exact Hc|exact Hy|apply RWord_RId, Hw].
Qed.

(** Moving entries in front of entries on labels known distinct. *)
Lemma split_pay_spec T p cp : forall es ces seen cpre ts rest,
  Inv T -> RId T p cp -> REnts T es ces ->
  Forall (fun s => exists l, CNorm.slabel s = Some l /\ In l seen) cpre ->
  HDisplay.split_pay F p seen es = (ts, rest) ->
  exists crest, REnts T rest crest /\
    forall Y c, wpre (cpre ++ ces) Y c =
      wpre (map (fun '(h, u) => CNorm.SE h (CNorm.VTerm u None cp)) ts ++ cpre ++ crest) Y c.
Proof.
  induction es as [|[h v] es IH]; intros ces seen cpre ts rest I Hp He Hpre E; inversion He as [|? cs ? ces' Hs He']; subst.
  - cbn in E; injection E as <- <-; exists []; split; [constructor|intros; rewrite !app_nil_r; reflexivity].
  - cbn [HDisplay.split_pay] in E.
    destruct (match HDisplay.tpay v with
              | Some (u, q) => if Pos.eqb p q && forallb (fun k => HNorm.kd F k h) seen then Some u else None
              | None => None end) as [u|] eqn:Tk.
    + destruct (HDisplay.split_pay F p seen es) as [ts' rest'] eqn:E1; injection E as <- <-.
      destruct v as [g j|u0 [b|] q|g j x]; cbn [HDisplay.tpay] in Tk; try discriminate.
      destruct (Pos.eqb p q && forallb (fun k => HNorm.kd F k h) seen) eqn:B; [|discriminate]; injection Tk as ->.
      apply andb_true_iff in B as [Bq Bk]; apply Pos.eqb_eq in Bq; subst q.
      inversion Hs as [h0 v0 cv Hv| |]; subst; inversion Hv as [|u1 b1 p1 cq Hq|]; subst.
      pose proof (RId_func T p _ _ I Hq Hp) as ->.
      destruct (IH ces' seen cpre ts' rest' I Hp He' Hpre E1) as [crest [Hr S]].
      exists crest; split; [exact Hr|]; intros Y c.
      rewrite wpre_app; cbn [CSound.wpre]; rewrite (wpre_comm M F HM (CNorm.SE h (CNorm.VTerm u None cp)) h cpre).
      * rewrite <- wpre_app, S; reflexivity.
      * reflexivity.
      * eapply Forall_impl; [|exact Hpre]; intros t [l [Lt Il]]; exists l; split; [exact Lt|].
        rewrite forallb_forall in Bk; apply kd_dist, Bk, Il.
    + destruct (HDisplay.split_pay F p (h :: seen) es) as [ts' rest'] eqn:E1; injection E as <- <-.
      assert (Hpre' : Forall (fun s => exists l, CNorm.slabel s = Some l /\ In l (h :: seen)) (cpre ++ [cs])).
      { apply Forall_app; split.
        - eapply Forall_impl; [|exact Hpre]; intros t [l [Lt Il]]; exists l; split; [exact Lt|right; exact Il].
        - constructor; [|constructor]; inversion Hs; subst; exists h; split; [reflexivity|left; reflexivity]. }
      destruct (IH ces' (h :: seen) (cpre ++ [cs]) ts' rest' I Hp He' Hpre' E1) as [crest [Hr S]].
      exists (cs :: crest); split; [constructor; [exact Hs|exact Hr]|]; intros Y c.
      replace (cpre ++ cs :: ces') with ((cpre ++ [cs]) ++ ces') by (rewrite <- app_assoc; reflexivity).
      rewrite S, <- app_assoc; reflexivity.
Qed.

Lemma strip_to_spec T a1 cR : Inv T -> RId T a1 cR -> forall w cw pre, RWord T w cw ->
  HDisplay.strip_to a1 w = Some pre -> exists cpre, REnts T pre cpre /\ cw = cpre ++ cR.
Proof.
  intros I Ha w cw pre H; revert pre; induction H as [|x i w cx cw Hc Hx Hw IH]; intros pre E; cbn [HDisplay.strip_to] in E.
  - destruct (Pos.eqb a1 1) eqn:E1; [apply Pos.eqb_eq in E1; subst a1|discriminate]; injection E as <-.
    exists []; split; [constructor|]; rewrite (RId_one T cR I Ha); reflexivity.
  - destruct (Pos.eqb i a1) eqn:E1.
    + apply Pos.eqb_eq in E1; subst i; injection E as <-; exists []; split; [constructor|].
      apply (RId_func T a1 _ _ I); [apply (RCons T a1 x (HNorm.wid w)); [exact Hc|exact Hx|apply RWord_RId, Hw]|exact Ha].
    + destruct x as [h v|h|a]; [|discriminate|discriminate].
      destruct (HDisplay.strip_to a1 w) as [l|] eqn:E2; [|discriminate]; injection E as <-.
      destruct (IH l eq_refl) as [cpre [Hp ->]].
      exists (cx :: cpre); split; [constructor; [exact Hx|exact Hp]|reflexivity].
Qed.

Lemma entries_eqb_eq a b : HDisplay.entries_eqb a b = true -> a = b.
Proof.
  revert b; induction a as [|[h v] a IH]; intros [|[k u] b] E; cbn in E; try discriminate; [reflexivity|].
  apply andb_true_iff in E as [E1 E2]; apply andb_true_iff in E1 as [Eh Ev].
  apply lexp_eqb_eq in Eh; apply hval_eqb_eq in Ev; subst; f_equal; apply IH, E2.
Qed.

Lemma REnts_func T es c1 c2 : Inv T -> REnts T es c1 -> REnts T es c2 -> c1 = c2.
Proof.
  intros I H1; revert c2; induction H1 as [|hv cs es ces Hs H IH]; intros c2 H2; inversion H2; subst; [reflexivity|].
  f_equal; [apply (proj1 (proj2 (R_func T I)) _ _ Hs _ H3)|apply IH, H5].
Qed.

(** The form [⟦ hᵢ := uᵢ ⟧] as a word: terms with the identity payload. *)
Definition sform_c (ts : list (lexp * nat)) : CNorm.cword :=
  map (fun '(h, u) => CNorm.SE h (CNorm.VTerm u None [])) ts.

Lemma wden_wpre w (x : U) : wden w x = wpre w x x.
Proof. induction w as [|t w IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma sform_wpre ts cp (c Z : U) :
  wpre (map (fun '(h, u) => CNorm.SE h (CNorm.VTerm u None cp)) ts) Z c = wpre (sform_c ts) Z (wden cp c).
Proof.
  induction ts as [|[h u] ts IH]; cbn [map CSound.wpre sform_c]; [reflexivity|].
  cbn [CSound.sden]; rewrite IH, !CSound.vden_term; reflexivity.
Qed.

Lemma split_pay_cell T q : forall es ces seen t0 ts0 rest, Inv T -> REnts T es ces ->
  HDisplay.split_pay F q seen es = (t0 :: ts0, rest) -> exists cq, RId T q cq.
Proof.
  induction es as [|[h v] es IH]; intros ces seen t0 ts0 rest I He E; [discriminate|].
  inversion He as [|? cs ? ces' Hs He']; subst; cbn [HDisplay.split_pay] in E.
  destruct (match HDisplay.tpay v with
            | Some (u, q') => if Pos.eqb q q' && forallb (fun k => HNorm.kd F k h) seen then Some u else None
            | None => None end) as [u|] eqn:Tk.
  - destruct v as [g j|u0 [b|] q'|g j x]; cbn [HDisplay.tpay] in Tk; try discriminate.
    destruct (Pos.eqb q q') eqn:Bq; [|discriminate]; apply Pos.eqb_eq in Bq; subst q'.
    inversion Hs as [h0 v0 cv Hv| |]; subst; inversion Hv as [|u1 b1 p1 cq Hq|]; subst; exists cq; exact Hq.
  - destruct (HDisplay.split_pay F q (h :: seen) es) as [ts' rest'] eqn:E1; injection E as Ets _; subst ts'.
    apply (IH ces' (h :: seen) t0 ts0 rest' I He' E1).
Qed.

Lemma factor_spec T a1 cR es ces ts p : Inv T -> RId T a1 cR -> REnts T es ces ->
  HDisplay.find_factor F T a1 es es = Some (ts, p) ->
  exists cp, RId T p cp /\ forall c, wden (ces ++ cR) c = wden (sform_c ts) (wden cp c).
Proof.
  intros I Ha He; generalize es at 2; intros l E; induction l as [|[h v] l IH]; cbn [HDisplay.find_factor] in E; [discriminate|].
  destruct (HDisplay.tpay v) as [[u q]|] eqn:Tq; [|apply IH, E].
  destruct (HDisplay.split_pay F q [] es) as [ts' rest] eqn:Es.
  destruct ts' as [|t0 ts0]; [apply IH, E|].
  destruct (HDisplay.strip_to a1 (HDisplay.hw T q)) as [pre|] eqn:St; [|apply IH, E].
  destruct (HDisplay.entries_eqb pre rest) eqn:Eq; [|apply IH, E].
  injection E as <- <-; apply entries_eqb_eq in Eq; subst pre.
  destruct (split_pay_cell T q es ces [] _ _ _ I He Es) as [cq Hq].
  destruct (hw_spec T q cq I Hq) as [Hwq _].
  destruct (strip_to_spec T a1 cR I Ha _ _ rest Hwq St) as [cpre [Hpre ->]].
  destruct (split_pay_spec T q _ es ces [] [] _ rest I Hq He (Forall_nil _) Es) as [crest [Hr S]].
  pose proof (REnts_func T rest _ _ I Hpre Hr) as <-.
  exists (cpre ++ cR); split; [exact Hq|]; intros c.
  rewrite wden_app; change ces with ([] ++ ces); rewrite S, app_nil_l, wpre_app, <- wden_app.
  rewrite sform_wpre; symmetry; apply wden_wpre.
Qed.


Lemma unents_spec g f : forall es ces R' cR' T m B T' m', Inv T -> UnMemo g T m -> REnts T es ces -> RWord T R' cR' ->
  HDisplay.unents F g f es R' T m = Some (B, T', m') ->
  Inv T' /\ Ext T T' /\ UnMemo g T' m' /\ exists ces', RWord T' B (ces' ++ cR') /\ forall Y c, wpre ces Y c = wpre ces' Y (cpop g c).
Proof.
  induction es as [|[h v] es IH]; intros ces R' cR' T m B T' m' I Hm He HR E; cbn [HDisplay.unents] in E.
  - injection E as <- <- <-; inversion He; subst.
    split; [exact I|split; [apply Ext_refl|split; [exact Hm|exists []; split; [exact HR|reflexivity]]]].
  - inversion He as [|? cs ? ces0 Hs He0]; subst; inversion Hs as [h0 v0 cv Hv| |]; subst.
    destruct (HDisplay.unv F g f v T m) as [[[v' T1] m1]|] eqn:E1; [|discriminate].
    destruct (proj2 (proj2 (proj2 (un_spec g f))) v T m v' T1 m1 cv I Hm Hv E1) as [I1 [X1 [Hm1 [cv' [Hv' Sv]]]]].
    destruct (HDisplay.unents F g f es R' T1 m1) as [[[w1 T2] m2]|] eqn:E2; [|discriminate].
    destruct (IH ces0 R' cR' T1 m1 w1 T2 m2 I1 Hm1 (REnts_mono _ _ _ _ X1 He0) (RWord_mono _ _ X1 _ _ HR) E2)
      as [I2 [X2 [Hm2 [ces1 [Hw1 Sw]]]]].
    destruct (HNorm.hcons (HNorm.SE h v') w1 T2) as [w2 T3] eqn:E3; injection E as <- <- <-.
    destruct (hcons_spec T2 _ w1 (CNorm.SE h cv') _ w2 T3 I2 (RStep_mono _ _ _ _ X2 (RSE _ h v' cv' Hv')) Hw1 E3) as [I3 [X3 Hw3]].
    split; [exact I3|split; [apply (Ext_trans _ _ _ X1 (Ext_trans _ _ _ X2 X3))|split; [apply (UnMemo_mono g _ _ _ X3 Hm2)|]]].
    exists (CNorm.SE h cv' :: ces1); split; [exact Hw3|]; intros Y c; cbn [CSound.wpre CSound.sden].
    rewrite Sw, Sv; reflexivity.
Qed.

Lemma find_lift_spec T : forall es seen pre ces cpre R cR x g B T', Inv T ->
  REnts T (rev pre) cpre -> Forall (fun s => exists l, CNorm.slabel s = Some l /\ In l seen) cpre ->
  REnts T es ces -> RWord T R cR -> HDisplay.find_lift F T seen pre es R = Some (x, g, B, T') ->
  Inv T' /\ Ext T T' /\ exists cB, RWord T' B cB /\
    forall c, wden (cpre ++ ces ++ cR) c = cpush x (wden cB (cpop g c)) (cname g 0 c).
Proof.
  induction es as [|[h v] es IH]; intros seen pre ces cpre R cR x g B T' I Hpre Hseen He HR E; [discriminate|].
  inversion He as [|? cs ? ces0 Hs He0]; subst; cbn [HDisplay.find_lift] in E.
  assert (Hnext : HDisplay.find_lift F T (h :: seen) ((h, v) :: pre) es R = Some (x, g, B, T') ->
    Inv T' /\ Ext T T' /\ exists cB, RWord T' B cB /\
      forall c, wden (cpre ++ cs :: ces0 ++ cR) c = cpush x (wden cB (cpop g c)) (cname g 0 c)).
  { intros En.
    assert (Hpre' : REnts T (rev ((h, v) :: pre)) (cpre ++ [cs])) by (cbn [rev]; apply Forall2_app; [exact Hpre|constructor; [exact Hs|constructor]]).
    assert (Hseen' : Forall (fun s => exists l, CNorm.slabel s = Some l /\ In l (h :: seen)) (cpre ++ [cs])).
    { apply Forall_app; split.
      - eapply Forall_impl; [|exact Hseen]; intros t [l [Lt Il]]; exists l; split; [exact Lt|right; exact Il].
      - constructor; [|constructor]; inversion Hs; subst; exists h; split; [reflexivity|left; reflexivity]. }
    destruct (IH (h :: seen) ((h, v) :: pre) ces0 (cpre ++ [cs]) R cR x g B T' I Hpre' Hseen' He0 HR En) as [I1 [X1 [cB [HB S]]]].
    split; [exact I1|split; [exact X1|exists cB; split; [exact HB|]]]; intros c; rewrite <- S, <- app_assoc; reflexivity. }
  destruct v as [g0 [|j]|u b p|g0 j y]; try (apply Hnext, E).
  destruct (forallb (fun k => HNorm.kd F k h) seen) eqn:K; [|apply Hnext, E].
  destruct (HDisplay.unw F g0 (HDisplay.fuel_of T) R T (PositiveMap.empty _)) as [[[R' T1] m1]|] eqn:E1; [|apply Hnext, E].
  destruct (HDisplay.unents F g0 (HDisplay.fuel_of T) (rev pre ++ es) R' T1 m1) as [[[B' T2] m2]|] eqn:E2; [|apply Hnext, E].
  injection E as <- <- <- <-.
  assert (Hm0 : UnMemo g0 T (PositiveMap.empty _)) by (intros k k' Ek; rewrite PositiveMap.gempty in Ek; discriminate).
  destruct (proj1 (un_spec g0 (HDisplay.fuel_of T)) R T _ R' T1 m1 cR I Hm0 HR E1) as [I1 [X1 [Hm1 [cR' [HR' SR]]]]].
  assert (He' : REnts T1 (rev pre ++ es) (cpre ++ ces0)) by (apply (REnts_mono T); [exact X1|apply Forall2_app; assumption]).
  destruct (unents_spec g0 _ _ _ R' cR' T1 m1 B' T2 m2 I1 Hm1 He' HR' E2) as [I2 [X2 [_ [ces' [HB SB]]]]].
  split; [exact I2|split; [apply (Ext_trans _ _ _ X1 X2)|]].
  exists (ces' ++ cR'); split; [exact HB|]; intros c.
  inversion Hs as [h1 v1 cv Hv| |]; subst; inversion Hv; subst.
  rewrite wden_app, <- app_comm_cons; cbn [CSound.wden].
  rewrite (wpre_comm M F HM (CNorm.SE h (CNorm.VVar g0 0)) h cpre); [|reflexivity|].
  - cbn [CSound.sden CSound.vden]; f_equal.
    rewrite wden_app, <- wpre_app, SR, SB, <- wden_app; reflexivity.
  - eapply Forall_impl; [|exact Hseen]; intros t [l [Lt Il]]; exists l; split; [exact Lt|].
    rewrite forallb_forall in K; apply kd_dist, K, Il.
Qed.

Lemma split_cand_in R es x : HDisplay.split_cand R es = Some x -> In x R.
Proof.
  induction es as [|[h v] es IH]; cbn; [discriminate|].
  destruct v as [g j|u [b|] p|g j y]; try apply IH.
  - destruct (existsb (Pos.eqb p) R) eqn:Ex; [|apply IH].
    intros E; injection E as <-; apply existsb_exists in Ex as [z [Hz Ez]]; apply Pos.eqb_eq in Ez; subst; exact Hz.
  - destruct (existsb (Pos.eqb y) R) eqn:Ex; [|apply IH].
    intros E; injection E as <-; apply existsb_exists in Ex as [z [Hz Ez]]; apply Pos.eqb_eq in Ez; subst; exact Hz.
Qed.

Lemma find_split_spec T W cW R cR es x W1 T1 : Inv T -> RWord T W cW -> RWord T R cR ->
  HDisplay.find_split F T W R es = Some (x, W1, T1) ->
  Inv T1 /\ Ext T T1 /\ exists cx cW1, RId T1 x cx /\ RWord T1 W1 cW1 /\ forall c, wden cW c = wden cW1 (wden cx c).
Proof.
  intros I HW HR E; unfold HDisplay.find_split in E.
  destruct (HDisplay.split_cand (HDisplay.wids R) es) as [y|] eqn:Ec; [|discriminate].
  destruct (HDisplay.relw F y (HDisplay.fuel_of T) W T (PositiveMap.empty _)) as [[[W' T'] m']|] eqn:Er; [|discriminate].
  injection E as <- <- <-.
  destruct (wids_RId T R cR y I HR (split_cand_in _ _ _ Ec)) as [cy Hy].
  assert (Hm : RelMemo cy T (PositiveMap.empty _)) by (intros k k' Ek; rewrite PositiveMap.gempty in Ek; discriminate).
  destruct (proj1 (rel_spec y cy (HDisplay.fuel_of T)) W T _ W' T' m' cW I Hy Hm HW Er) as [I1 [X1 [_ [cW1 [HW1 S]]]]].
  split; [exact I1|split; [exact X1|exists cy, cW1; split; [apply (RId_mono _ _ _ _ X1 Hy)|split; [exact HW1|exact S]]]].
Qed.


(** ** Showing cells *)

Variable base : nat.

(** References to cells, [base + k], read through [ρ]. *)
Definition upd (ρ : nat -> U -> U) : cmodel :=
  mk_cmodel U (cA M) (@cpop M) (@chd M) (@cpush M) (cpop_push M) (chd_push M) (cpush_pop M)
    (fun n x => if Nat.leb base n then ρ (n - base) x else catom n x) (@cterm M).

Definition dden (ρ : nat -> U -> U) (d : aexp) (c : U) : U := @ca (upd ρ) d c.

Lemma dden_acomp ρ r x c : dden ρ (HDisplay.acomp r x) c = dden ρ x (dden ρ r c).
Proof. destruct r; reflexivity. Qed.

Lemma wpre_sw hs (Y x x' : U) : wpre (map CNorm.SW hs) Y x = wpre (map CNorm.SW hs) Y x'.
Proof. induction hs as [|h hs IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma dden_weak ρ hs (Y : U) : dden ρ (HDisplay.weak hs) Y = wpre (map CNorm.SW hs) Y Y.
Proof.
  unfold HDisplay.weak, dden.
  assert (G : forall a Z, @ca (upd ρ) (fold_left (fun a h => AOuter h a) hs a) Z = @ca (upd ρ) a (wpre (map CNorm.SW hs) Z Z)).
  { induction hs as [|h hs IH]; intros a Z; cbn [fold_left map CSound.wpre]; [reflexivity|].
    rewrite IH; reflexivity. }
  apply G.
Qed.

Lemma dden_sform ρ ts (Y : U) : dden ρ (HDisplay.sform ts) Y = wden (sform_c ts) Y.
Proof.
  induction ts as [|[h u] ts IH]; [reflexivity|].
  change (cpush h (dden ρ (HDisplay.sform ts) Y) (cterm u None Y)
          = cpush h (wden (sform_c ts) Y) (vden (CNorm.VTerm u None []) Y)).
  rewrite IH, CSound.vden_term; reflexivity.
Qed.



Lemma dref_S f i D : HDisplay.dref F base (S f) i D =
  if Pos.eqb i 1 then Some (AId, D)
  else match PositiveMap.find i (HDisplay.dmemo D) with
       | Some k => Some (AAtom (base + k), D)
       | None =>
           match HDisplay.dbody F base f i D with
           | Some (d, D1) =>
               match PositiveMap.find i (HDisplay.dmemo D1) with
               | Some k => Some (AAtom (base + k), D1)
               | None =>
                   Some (AAtom (base + HDisplay.dn D1),
                         HDisplay.mk_dstate (HDisplay.dT D1) (PositiveMap.add i (HDisplay.dn D1) (HDisplay.dmemo D1))
                           (d :: HDisplay.ddefs D1) (S (HDisplay.dn D1)))
               end
           | None => None
           end
       end.
Proof. reflexivity. Qed.

Lemma dbody_S f i D : HDisplay.dbody F base (S f) i D =
  match HDisplay.hw (HDisplay.dT D) i with
  | [] => Some (AId, D)
  | (HNorm.SA a, _) :: R =>
      if Nat.ltb a base then
        match HDisplay.dref F base f (HNorm.wid R) D with Some (r, D1) => Some (HDisplay.acomp r (AAtom a), D1) | None => None end
      else None
  | (HNorm.SW _, _) :: _ =>
      let '(hs, R) := HDisplay.take_sw (HDisplay.hw (HDisplay.dT D) i) in
      match HDisplay.dref F base f (HNorm.wid R) D with Some (r, D1) => Some (HDisplay.acomp r (HDisplay.weak hs), D1) | None => None end
  | (HNorm.SE _ _, _) :: _ =>
      let '(es, R) := HDisplay.take_se (HDisplay.hw (HDisplay.dT D) i) in
      match HDisplay.find_factor F (HDisplay.dT D) (HNorm.wid R) es es with
      | Some (ts, p) => match HDisplay.dref F base f p D with Some (r, D1) => Some (HDisplay.acomp r (HDisplay.sform ts), D1) | None => None end
      | None =>
          match HDisplay.find_split F (HDisplay.dT D) (HDisplay.hw (HDisplay.dT D) i) R es with
          | Some (x, W1, T1) =>
              match HDisplay.dref F base f x (HDisplay.setT D T1) with
              | Some (r2, D1) =>
                  match HDisplay.dref F base f (HNorm.wid W1) D1 with Some (r1, D2) => Some (HDisplay.acomp r2 r1, D2) | None => None end
              | None => None
              end
          | None =>
              match HDisplay.find_lift F (HDisplay.dT D) [] [] es R with
              | Some (x, g, B, T1) =>
                  match HDisplay.dref F base f (HNorm.wid B) (HDisplay.setT D T1) with
                  | Some (rb, D1) => Some (AInner x (TVarE g 0) (AOuter g rb), D1)
                  | None => None
                  end
              | None => HDisplay.dabs F base f es R D
              end
          end
      end
  end.
Proof. reflexivity. Qed.

Lemma dabs_S f es R D : HDisplay.dabs F base (S f) es R D =
  match es with
  | [] => HDisplay.dref F base f (HNorm.wid R) D
  | (h, v) :: es' =>
      match match v with
            | HNorm.VVar g j => Some (TVarE g j, D)
            | HNorm.VTerm u None p =>
                match HDisplay.dref F base f p D with Some (r, D1) => Some (TBindE u (PComp r PId), D1) | None => None end
            | HNorm.VLook g j x =>
                match HDisplay.dref F base f x D with Some (r, D1) => Some (TLookE g j r, D1) | None => None end
            | HNorm.VTerm _ (Some _) _ => None
            end with
      | Some (t, D1) => match HDisplay.dabs F base f es' R D1 with Some (a, D2) => Some (AInner h t a, D2) | None => None end
      | None => None
      end
  end.
Proof. reflexivity. Qed.

(** All atoms below [n]: real atoms below [base], references below [n]. *)
Fixpoint alt (n : nat) (d : aexp) : Prop :=
  match d with
  | AId => True
  | AAtom a => a < n
  | ACompose a b => alt n a /\ alt n b
  | AOuter _ a | ALift _ a => alt n a
  | AInner _ t a => tlt n t /\ alt n a
  end
with tlt (n : nat) (t : texp) : Prop :=
  match t with
  | TVarE _ _ => True
  | TBindE _ p => plt n p
  | TShiftE _ t => tlt n t
  | TLookE _ _ a => alt n a
  end
with plt (n : nat) (p : pexp) : Prop :=
  match p with
  | PId | PAtom _ => True
  | PComp a p => alt n a /\ plt n p
  | PShift _ p => plt n p
  end.

Lemma alt_mono n n' : n <= n' ->
  (forall d, alt n d -> alt n' d) /\ (forall t, tlt n t -> tlt n' t) /\ (forall p, plt n p -> plt n' p).
Proof. intros L; apply exp_mind; cbn; intros; try tauto; lia. Qed.

Lemma alt_acomp n r x : alt n r -> alt n x -> alt n (HDisplay.acomp r x).
Proof. destruct r; cbn; tauto. Qed.

Lemma alt_weak n hs : alt n (HDisplay.weak hs).
Proof.
  unfold HDisplay.weak; assert (G : forall a, alt n a -> alt n (fold_left (fun a h => AOuter h a) hs a)).
  { induction hs as [|h hs IH]; intros a H; cbn; [exact H|apply IH, H]. }
  apply G; exact I.
Qed.

Lemma alt_sform n ts : alt n (HDisplay.sform ts).
Proof. induction ts as [|[h u] ts IH]; cbn; tauto. Qed.

(** An environment agrees with the cells shown before [n]. *)
Definition Agree (D : HDisplay.dstate) (ρ : nat -> U -> U) (n : nat) : Prop :=
  forall i k, PositiveMap.find i (HDisplay.dmemo D) = Some k -> k < n ->
    forall ci, RId (HDisplay.dT D) i ci -> forall c, ρ k c = wden ci c.

Record DInv (D : HDisplay.dstate) : Prop := {
  di_inv : Inv (HDisplay.dT D);
  di_len : length (HDisplay.ddefs D) = HDisplay.dn D;
  di_memo : forall i k, PositiveMap.find i (HDisplay.dmemo D) = Some k ->
    k < HDisplay.dn D /\ (exists ci, RId (HDisplay.dT D) i ci) /\
    exists d, nth_error (rev (HDisplay.ddefs D)) k = Some d /\ alt (base + k) d /\
      forall ρ, Agree D ρ k -> forall ci, RId (HDisplay.dT D) i ci -> forall c, dden ρ d c = wden ci c;
  di_onto : forall k, k < HDisplay.dn D -> exists i, PositiveMap.find i (HDisplay.dmemo D) = Some k
}.

Definition DExt (D D' : HDisplay.dstate) : Prop :=
  Ext (HDisplay.dT D) (HDisplay.dT D') /\
  (forall i k, PositiveMap.find i (HDisplay.dmemo D) = Some k -> PositiveMap.find i (HDisplay.dmemo D') = Some k) /\
  HDisplay.dn D <= HDisplay.dn D' /\
  (forall k d, nth_error (rev (HDisplay.ddefs D)) k = Some d -> nth_error (rev (HDisplay.ddefs D')) k = Some d).

Lemma DExt_refl D : DExt D D.
Proof. split; [apply Ext_refl|split; [auto|split; auto]]. Qed.

Lemma DExt_trans D1 D2 D3 : DExt D1 D2 -> DExt D2 D3 -> DExt D1 D3.
Proof.
  intros [X1 [M1 [N1 L1]]] [X2 [M2 [N2 L2]]].
  split; [apply (Ext_trans _ _ _ X1 X2)|split; [auto|split; [lia|auto]]].
Qed.

Lemma Agree_mono D D' ρ n : DExt D D' -> Agree D' ρ n -> Agree D ρ n.
Proof.
  intros [X [Mm _]] A i k E L ci H c; apply (A i k (Mm i k E) L ci (RId_mono _ _ _ _ X H)).
Qed.

(** A reading in a later table is the one in the earlier table. *)
Lemma RId_later T T' i ci ci' : Inv T' -> Ext T T' -> RId T i ci -> RId T' i ci' -> ci' = ci.
Proof. intros I X H H'; apply (RId_func T' i _ _ I H' (RId_mono _ _ _ _ X H)). Qed.

Lemma DInv_setT D T' : DInv D -> Inv T' -> Ext (HDisplay.dT D) T' -> DInv (HDisplay.setT D T') /\ DExt D (HDisplay.setT D T').
Proof.
  intros [I L Mm On] I' X; split; [|split; [exact X|split; [auto|split; auto]]].
  constructor; cbn; [exact I'|exact L| |exact On].
  intros i k E; destruct (Mm i k E) as [Lk [[ci Hi] [d [Hd [Ad Sd]]]]].
  split; [exact Lk|split; [exists ci; apply (RId_mono _ _ _ _ X Hi)|exists d; split; [exact Hd|split; [exact Ad|]]]].
  intros ρ A ci' Hi' c; rewrite (RId_later _ _ i ci ci' I' X Hi Hi').
  apply Sd; [|exact Hi]; intros i' k' E' L' cj Hj c'; apply (A i' k' E' L' cj (RId_mono _ _ _ _ X Hj)).
Qed.


Lemma Agree_le D ρ n n' : n <= n' -> Agree D ρ n' -> Agree D ρ n.
Proof. intros L A i k E Lk; apply (A i k E); lia. Qed.

Lemma Agree_of D D' ρ : DExt D D' -> Agree D' ρ (HDisplay.dn D') -> Agree D ρ (HDisplay.dn D).
Proof. intros X A; apply (Agree_mono D D' ρ _ X), (Agree_le _ _ _ _ (proj1 (proj2 (proj2 X))) A). Qed.

Lemma ref_hit D i k : DInv D -> PositiveMap.find i (HDisplay.dmemo D) = Some k ->
  alt (base + HDisplay.dn D) (AAtom (base + k)) /\
  forall ρ, Agree D ρ (HDisplay.dn D) -> forall ci, RId (HDisplay.dT D) i ci -> forall c, dden ρ (AAtom (base + k)) c = wden ci c.
Proof.
  intros DI E; destruct (di_memo D DI i k E) as [Lk _]; split; [cbn; lia|].
  intros ρ A ci H c; unfold dden; cbn [ca upd catom].
  replace (Nat.leb base (base + k)) with true by (symmetry; apply Nat.leb_le; lia).
  replace (base + k - base) with k by lia; apply (A i k E Lk ci H c).
Qed.

Lemma add_spec D1 i d : DInv D1 -> PositiveMap.find i (HDisplay.dmemo D1) = None ->
  (exists ci, RId (HDisplay.dT D1) i ci) -> alt (base + HDisplay.dn D1) d ->
  (forall ρ, Agree D1 ρ (HDisplay.dn D1) -> forall ci, RId (HDisplay.dT D1) i ci -> forall c, dden ρ d c = wden ci c) ->
  let D' := HDisplay.mk_dstate (HDisplay.dT D1) (PositiveMap.add i (HDisplay.dn D1) (HDisplay.dmemo D1))
              (d :: HDisplay.ddefs D1) (S (HDisplay.dn D1)) in
  DInv D' /\ DExt D1 D'.
Proof.
  intros [I L Mm On] N Hi Ad Sd D'.
  assert (Lr : length (rev (HDisplay.ddefs D1)) = HDisplay.dn D1) by (rewrite length_rev; exact L).
  assert (Old : forall k d0, nth_error (rev (HDisplay.ddefs D1)) k = Some d0 ->
                  nth_error (rev (HDisplay.ddefs D')) k = Some d0).
  { intros k d0 E; cbn [D' HDisplay.ddefs rev]; rewrite nth_error_app1; [exact E|].
    apply nth_error_Some; rewrite E; discriminate. }
  assert (Mi : forall i' k, PositiveMap.find i' (HDisplay.dmemo D1) = Some k -> PositiveMap.find i' (HDisplay.dmemo D') = Some k).
  { intros i' k E; cbn [D' HDisplay.dmemo]; rewrite PositiveMap.gso; [exact E|intros ->; congruence]. }
  assert (AD : forall ρ n, Agree D' ρ n -> Agree D1 ρ n).
  { intros ρ n A i' k E Lk ci H c; apply (A i' k (Mi i' k E) Lk ci H c). }
  split; [|split; [apply Ext_refl|split; [exact Mi|split; [cbn; lia|exact Old]]]].
  constructor; cbn [D' HDisplay.dT HDisplay.ddefs HDisplay.dn HDisplay.dmemo]; [exact I|cbn; rewrite L; reflexivity| |].
  - intros i' k E; destruct (Pos.eq_dec i' i) as [->|Ni].
    + rewrite PositiveMap.gss in E; injection E as <-.
      split; [lia|split; [exact Hi|exists d; split; [|split; [exact Ad|]]]].
      * cbn [rev]; rewrite nth_error_app2 by lia; rewrite Lr, Nat.sub_diag; reflexivity.
      * intros ρ A; apply Sd; intros i'' k'' E'' L'' ci H c; apply (A i'' k'' (Mi _ _ E'') L'' ci H c).
    + rewrite PositiveMap.gso in E by exact Ni.
      destruct (Mm i' k E) as [Lk [Hc [d0 [Hd [Ad0 Sd0]]]]].
      split; [lia|split; [exact Hc|exists d0; split; [apply (Old k d0 Hd)|split; [exact Ad0|]]]].
      intros ρ A; apply Sd0, (AD ρ k A).
  - intros k Lk; destruct (Nat.eq_dec k (HDisplay.dn D1)) as [->|Nk].
    + exists i; apply PositiveMap.gss.
    + destruct (On k ltac:(lia)) as [i' E]; exists i'; rewrite PositiveMap.gso; [exact E|intros ->; congruence].
Qed.

Lemma dden_atom_real ρ a (Y : U) : a < base -> dden ρ (AAtom a) Y = catom a Y.
Proof.
  intros L; unfold dden; cbn [ca upd catom].
  replace (Nat.leb base a) with false by (symmetry; apply Nat.leb_gt, L); reflexivity.
Qed.

Lemma disp_spec : forall fuel,
  (forall i D r D', DInv D -> (exists ci, RId (HDisplay.dT D) i ci) -> HDisplay.dref F base fuel i D = Some (r, D') ->
     DInv D' /\ DExt D D' /\ alt (base + HDisplay.dn D') r /\
     forall ρ, Agree D' ρ (HDisplay.dn D') -> forall ci, RId (HDisplay.dT D') i ci -> forall c, dden ρ r c = wden ci c)
  /\ (forall i D r D', DInv D -> (exists ci, RId (HDisplay.dT D) i ci) -> HDisplay.dbody F base fuel i D = Some (r, D') ->
     DInv D' /\ DExt D D' /\ alt (base + HDisplay.dn D') r /\
     forall ρ, Agree D' ρ (HDisplay.dn D') -> forall ci, RId (HDisplay.dT D') i ci -> forall c, dden ρ r c = wden ci c)
  /\ (forall es R D a D' ces cR, DInv D -> REnts (HDisplay.dT D) es ces -> RWord (HDisplay.dT D) R cR ->
     HDisplay.dabs F base fuel es R D = Some (a, D') ->
     DInv D' /\ DExt D D' /\ alt (base + HDisplay.dn D') a /\
     forall ρ, Agree D' ρ (HDisplay.dn D') -> forall c, dden ρ a c = wden (ces ++ cR) c).
Proof.
  induction fuel as [|f IH]; [repeat split; intros; discriminate|].
  destruct IH as [IHr [IHb IHa]]; split; [|split].
  - (* dref *)
    intros i D r D' DI [ci Hi] E; rewrite dref_S in E.
    destruct (Pos.eqb i 1) eqn:E1.
    + apply Pos.eqb_eq in E1; subst i; injection E as <- <-.
      split; [exact DI|split; [apply DExt_refl|split; [exact I|]]].
      intros ρ A ci' H c; rewrite (RId_one _ _ (di_inv _ DI) H); reflexivity.
    + destruct (PositiveMap.find i (HDisplay.dmemo D)) as [k|] eqn:Fm.
      * injection E as <- <-; destruct (ref_hit D i k DI Fm) as [Ak Sk].
        split; [exact DI|split; [apply DExt_refl|split; [exact Ak|exact Sk]]].
      * destruct (HDisplay.dbody F base f i D) as [[d D1]|] eqn:Eb; [|discriminate].
        destruct (IHb i D d D1 DI (ex_intro _ ci Hi) Eb) as [DI1 [X1 [Ad Sd]]].
        destruct (PositiveMap.find i (HDisplay.dmemo D1)) as [k|] eqn:Fm1.
        -- injection E as <- <-; destruct (ref_hit D1 i k DI1 Fm1) as [Ak Sk].
           split; [exact DI1|split; [exact X1|split; [exact Ak|exact Sk]]].
        -- injection E as <- <-.
           assert (Hi1 : exists ci, RId (HDisplay.dT D1) i ci) by (exists ci; apply (RId_mono _ _ _ _ (proj1 X1) Hi)).
           destruct (add_spec D1 i d DI1 Fm1 Hi1 Ad Sd) as [DI2 X2].
           split; [exact DI2|split; [apply (DExt_trans _ _ _ X1 X2)|]].
           assert (Fi : PositiveMap.find i (HDisplay.dmemo (HDisplay.mk_dstate (HDisplay.dT D1)
                      (PositiveMap.add i (HDisplay.dn D1) (HDisplay.dmemo D1)) (d :: HDisplay.ddefs D1) (S (HDisplay.dn D1))))
                      = Some (HDisplay.dn D1)) by apply PositiveMap.gss.
           apply (ref_hit _ i _ DI2 Fi).
  - (* dbody *)
    intros i D r D' DI [ci Hi] E; rewrite dbody_S in E.
    pose proof (di_inv D DI) as I.
    destruct (hw_spec (HDisplay.dT D) i ci I Hi) as [HW _].
    destruct (HDisplay.hw (HDisplay.dT D) i) as [|[x j] R] eqn:EW.
    + injection E as <- <-; inversion HW; subst.
      split; [exact DI|split; [apply DExt_refl|split; [exact Logic.I|]]].
      intros ρ A ci' H c; rewrite (RId_func _ i _ _ I H Hi); reflexivity.
    + assert (Later : forall D2 ci', DExt D D2 -> DInv D2 -> RId (HDisplay.dT D2) i ci' -> ci' = ci).
      { intros D2 ci' X2 DI2 H'; apply (RId_later _ _ i ci ci' (di_inv _ DI2) (proj1 X2) Hi H'). }
      destruct x as [h v|h|a].
      * (* entries *)
        destruct (HDisplay.take_se ((HNorm.SE h v, j) :: R)) as [es R0] eqn:Et.
        destruct (take_se_spec _ _ ci es R0 HW Et) as [ces [cR [Eci [He HR]]]].
        destruct (HDisplay.find_factor F (HDisplay.dT D) (HNorm.wid R0) es es) as [[ts p]|] eqn:Ef.
        { destruct (factor_spec _ _ cR es ces ts p I (RWord_RId _ _ _ HR) He Ef) as [cp [Hp Sem]].
          destruct (HDisplay.dref F base f p D) as [[r1 D1]|] eqn:Er; [|discriminate]; injection E as <- <-.
          destruct (IHr p D r1 D1 DI (ex_intro _ cp Hp) Er) as [DI1 [X1 [A1 S1]]].
          split; [exact DI1|split; [exact X1|split; [apply alt_acomp; [exact A1|apply alt_sform]|]]].
          intros ρ A ci' H c; rewrite (Later D1 ci' X1 DI1 H), Eci, dden_acomp, dden_sform, Sem.
          rewrite (S1 ρ A cp (RId_mono _ _ _ _ (proj1 X1) Hp) c); reflexivity. }
        destruct (HDisplay.find_split F (HDisplay.dT D) ((HNorm.SE h v, j) :: R) R0 es) as [[[y W1] T1]|] eqn:Es.
        { destruct (find_split_spec _ _ ci R0 cR es y W1 T1 I HW HR Es) as [I1 [X1 [cy [cW1 [Hy [HW1 Sem]]]]]].
          destruct (DInv_setT D T1 DI I1 X1) as [DIs Xs].
          destruct (HDisplay.dref F base f y (HDisplay.setT D T1)) as [[r2 D1]|] eqn:Er2; [|discriminate].
          destruct (IHr y _ r2 D1 DIs (ex_intro _ cy Hy) Er2) as [DI1 [X2 [A2 S2]]].
          destruct (HDisplay.dref F base f (HNorm.wid W1) D1) as [[r1 D2]|] eqn:Er1; [|discriminate]; injection E as <- <-.
          assert (H1 : RId (HDisplay.dT D1) (HNorm.wid W1) cW1) by apply (RId_mono _ _ _ _ (proj1 X2)), RWord_RId, HW1.
          destruct (IHr _ D1 r1 D2 DI1 (ex_intro _ cW1 H1) Er1) as [DI2 [X3 [A1 S1]]].
          pose proof (DExt_trans _ _ _ Xs (DExt_trans _ _ _ X2 X3)) as X.
          split; [exact DI2|split; [exact X|split]].
          { apply alt_acomp; [|exact A1].
            apply (proj1 (alt_mono (base + HDisplay.dn D1) (base + HDisplay.dn D2) ltac:(pose proof (proj1 (proj2 (proj2 X3))); lia))), A2. }
          intros ρ A ci' H c; rewrite (Later D2 ci' X DI2 H), dden_acomp.
          rewrite (S2 ρ (Agree_of _ _ ρ X3 A) cy (RId_mono _ _ _ _ (proj1 X2) Hy) c).
          rewrite (S1 ρ A cW1 (RId_mono _ _ _ _ (proj1 X3) H1)); symmetry; apply Sem. }
        destruct (HDisplay.find_lift F (HDisplay.dT D) [] [] es R0) as [[[[y g] B] T1]|] eqn:El.
        { destruct (find_lift_spec _ es [] [] ces [] R0 cR y g B T1 I (Forall2_nil _) (Forall_nil _) He HR El)
            as [I1 [X1 [cB [HB Sem]]]].
          destruct (DInv_setT D T1 DI I1 X1) as [DIs Xs].
          destruct (HDisplay.dref F base f (HNorm.wid B) (HDisplay.setT D T1)) as [[rb D1]|] eqn:Erb; [|discriminate].
          injection E as <- <-.
          destruct (IHr _ _ rb D1 DIs (ex_intro _ cB (RWord_RId _ _ _ HB)) Erb) as [DI1 [X2 [Ab Sb]]].
          pose proof (DExt_trans _ _ _ Xs X2) as X.
          split; [exact DI1|split; [exact X|split; [cbn; tauto|]]].
          intros ρ A ci' H c; rewrite (Later D1 ci' X DI1 H), Eci, (Sem c : wden (ces ++ cR) c = _).
          change (cpush y (dden ρ rb (cpop g c)) (cname g 0 c) = cpush y (wden cB (cpop g c)) (cname g 0 c)).
          rewrite (Sb ρ A cB (RId_mono _ _ _ _ (proj1 X2) (RWord_RId _ _ _ HB))); reflexivity. }
        destruct (IHa es R0 D r D' ces cR DI He HR E) as [DI1 [X1 [A1 S1]]].
        split; [exact DI1|split; [exact X1|split; [exact A1|]]].
        intros ρ A ci' H c; rewrite (Later D' ci' X1 DI1 H), Eci; apply S1, A.
      * (* weakenings *)
        destruct (HDisplay.take_sw ((HNorm.SW h, j) :: R)) as [hs R0] eqn:Et.
        destruct (take_sw_spec _ _ ci hs R0 HW Et) as [cR [Eci HR]].
        destruct (HDisplay.dref F base f (HNorm.wid R0) D) as [[r1 D1]|] eqn:Er; [|discriminate]; injection E as <- <-.
        destruct (IHr _ D r1 D1 DI (ex_intro _ cR (RWord_RId _ _ _ HR)) Er) as [DI1 [X1 [A1 S1]]].
        split; [exact DI1|split; [exact X1|split; [apply alt_acomp; [exact A1|apply alt_weak]|]]].
        intros ρ A ci' H c; rewrite (Later D1 ci' X1 DI1 H), Eci, dden_acomp, dden_weak, wden_app.
        rewrite (S1 ρ A cR (RId_mono _ _ _ _ (proj1 X1) (RWord_RId _ _ _ HR))); apply wpre_sw.
      * (* an atom *)
        destruct (Nat.ltb a base) eqn:La; [apply Nat.ltb_lt in La|discriminate].
        inversion HW as [|x0 i0 w0 cx cR Hc Hx HR]; subst.
        destruct (HDisplay.dref F base f (HNorm.wid R) D) as [[r1 D1]|] eqn:Er; [|discriminate]; injection E as <- <-.
        destruct (IHr _ D r1 D1 DI (ex_intro _ cR (RWord_RId _ _ _ HR)) Er) as [DI1 [X1 [A1 S1]]].
        split; [exact DI1|split; [exact X1|split; [apply alt_acomp; [exact A1|cbn; lia]|]]].
        intros ρ A ci' H c; rewrite (Later D1 ci' X1 DI1 H), dden_acomp, dden_atom_real by exact La.
        inversion Hx; subst; cbn [CSound.wden CSound.sden].
        rewrite (S1 ρ A cR (RId_mono _ _ _ _ (proj1 X1) (RWord_RId _ _ _ HR))); reflexivity.
  - (* dabs *)
    intros es R D a D' ces cR DI He HR E; rewrite dabs_S in E.
    destruct es as [|[h v] es].
    + inversion He; subst.
      destruct (IHr _ D a D' DI (ex_intro _ cR (RWord_RId _ _ _ HR)) E) as [DI1 [X1 [A1 S1]]].
      split; [exact DI1|split; [exact X1|split; [exact A1|]]].
      intros ρ A c; apply (S1 ρ A cR (RId_mono _ _ _ _ (proj1 X1) (RWord_RId _ _ _ HR))).
    + inversion He as [|? cs ? ces0 Hs He0]; subst; inversion Hs as [h0 v0 cv Hv| |]; subst.
      assert (Step : forall t D1 a0 D2, DInv D1 -> DExt D D1 ->
                HDisplay.dabs F base f es R D1 = Some (a0, D2) -> tlt (base + HDisplay.dn D1) t ->
                (forall ρ, Agree D1 ρ (HDisplay.dn D1) -> forall c, @ct (upd ρ) t c = vden cv c) ->
                DInv D2 /\ DExt D D2 /\ alt (base + HDisplay.dn D2) (AInner h t a0) /\
                forall ρ, Agree D2 ρ (HDisplay.dn D2) -> forall c, dden ρ (AInner h t a0) c = wden (CNorm.SE h cv :: ces0 ++ cR) c).
      { intros t D1 a0 D2 DI1 X1 Ea At St.
        destruct (IHa es R D1 a0 D2 ces0 cR DI1 (REnts_mono _ _ _ _ (proj1 X1) He0) (RWord_mono _ _ (proj1 X1) _ _ HR) Ea)
          as [DI2 [X2 [A2 S2]]].
        split; [exact DI2|split; [apply (DExt_trans _ _ _ X1 X2)|split]].
        - cbn; split; [|exact A2].
          apply (proj1 (proj2 (alt_mono (base + HDisplay.dn D1) (base + HDisplay.dn D2) ltac:(pose proof (proj1 (proj2 (proj2 X2))); lia)))), At.
        - intros ρ A c; change (cpush h (dden ρ a0 c) (@ct (upd ρ) t c) = wden (CNorm.SE h cv :: ces0 ++ cR) c).
          rewrite (S2 ρ A c), (St ρ (Agree_of _ _ ρ X2 A) c); reflexivity. }
      destruct v as [g j0|u [b|] p|g j0 x].
      * destruct (HDisplay.dabs F base f es R D) as [[a0 D2]|] eqn:Ea; [|discriminate]; injection E as <- <-.
        apply (Step (TVarE g j0) D a0 D2 DI (DExt_refl D) Ea Logic.I).
        intros ρ _ c; inversion Hv; subst; reflexivity.
      * discriminate.
      * inversion Hv as [|u0 b0 p0 cp Hp|]; subst.
        destruct (HDisplay.dref F base f p D) as [[r1 D1]|] eqn:Er; [|discriminate].
        destruct (IHr p D r1 D1 DI (ex_intro _ cp Hp) Er) as [DI1 [X1 [A1 S1]]].
        destruct (HDisplay.dabs F base f es R D1) as [[a0 D2]|] eqn:Ea; [|discriminate]; injection E as <- <-.
        apply (Step _ D1 a0 D2 DI1 X1 Ea); [cbn; tauto|].
        intros ρ A c; rewrite CSound.vden_term; change (cterm u None (dden ρ r1 c) = cterm u None (wden cp c)).
        rewrite (S1 ρ A cp (RId_mono _ _ _ _ (proj1 X1) Hp)); reflexivity.
      * inversion Hv as [| |g0 j1 x0 cx Hx]; subst.
        destruct (HDisplay.dref F base f x D) as [[r1 D1]|] eqn:Er; [|discriminate].
        destruct (IHr x D r1 D1 DI (ex_intro _ cx Hx) Er) as [DI1 [X1 [A1 S1]]].
        destruct (HDisplay.dabs F base f es R D1) as [[a0 D2]|] eqn:Ea; [|discriminate]; injection E as <- <-.
        apply (Step _ D1 a0 D2 DI1 X1 Ea); [exact A1|].
        intros ρ A c; rewrite CSound.vden_look; change (cname g j0 (dden ρ r1 c) = cname g j0 (wden cx c)).
        rewrite (S1 ρ A cx (RId_mono _ _ _ _ (proj1 X1) Hx)); reflexivity.
Qed.


(** ** Sharing *)

Lemma is_bind_tsub σ t : CNorm.is_bind (HDisplay.tsub base σ t) = CNorm.is_bind t.
Proof. induction t; cbn; auto. Qed.

Lemma fpb_psub σ p : fpb (HDisplay.psub base σ p) = fpb p.
Proof. induction p; cbn; auto. Qed.

(** Replacing references by expressions is reading them through what the
    expressions mean. *)
Lemma asub_ca σ :
  (forall d (c : U), @ca M (HDisplay.asub base σ d) c = dden (fun j y => @ca M (σ j) y) d c)
  /\ (forall t (c : U), @ct M (HDisplay.tsub base σ t) c = @ct (upd (fun j y => @ca M (σ j) y)) t c)
  /\ (forall p (c : U), @cp M (HDisplay.psub base σ p) c = @cp (upd (fun j y => @ca M (σ j) y)) p c).
Proof.
  unfold dden; apply exp_mind; intros; simpl.
  - reflexivity.
  - destruct (Nat.leb base n); reflexivity.
  - rewrite H, H0; reflexivity.
  - rewrite H; reflexivity.
  - rewrite H, H0; reflexivity.
  - rewrite H; reflexivity.
  - reflexivity.
  - rewrite fpb_psub, H; reflexivity.
  - rewrite is_bind_tsub; destruct (CNorm.is_bind t); apply H.
  - rewrite H; reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite H, H0; reflexivity.
  - rewrite H; reflexivity.
Qed.

(** Two substitutions agreeing below [n] agree on expressions whose
    references are below [n]. *)
Lemma asub_ext n σ σ' : (forall j, base + j < n -> σ j = σ' j) ->
  (forall d, alt n d -> HDisplay.asub base σ d = HDisplay.asub base σ' d)
  /\ (forall t, tlt n t -> HDisplay.tsub base σ t = HDisplay.tsub base σ' t)
  /\ (forall p, plt n p -> HDisplay.psub base σ p = HDisplay.psub base σ' p).
Proof.
  intros E; apply exp_mind; intros; cbn [HDisplay.asub HDisplay.tsub HDisplay.psub alt tlt plt] in *;
    try (f_equal; tauto); try reflexivity.
  destruct (Nat.leb base n0) eqn:L; [apply Nat.leb_le in L; apply E; lia|reflexivity].
Qed.

Lemma assemble_go_spec shr cnt : forall ds k out shared out' shared',
  HDisplay.assemble_go base shr cnt k ds out shared = (out', shared') -> length out = k ->
  (exists ext, out' = out ++ ext) /\ (exists sext, shared' = shared ++ sext) /\ length out' = k + length ds /\
  forall j d, nth_error ds j = Some d -> alt (base + (k + j)) d ->
    forall σ, (forall j', j' < k + j -> σ j' = nth j' out' AId) ->
    nth (k + j) out' AId = HDisplay.asub base σ d \/
    exists sh, nth (k + j) out' AId = AAtom (base + sh) /\ nth_error shared' sh = Some (HDisplay.asub base σ d).
Proof.
  induction ds as [|d ds IH]; intros k out shared out' shared' E Lk; cbn [HDisplay.assemble_go] in E.
  - injection E as <- <-; split; [exists []; rewrite app_nil_r; reflexivity|split; [exists []; rewrite app_nil_r; reflexivity|]].
    split; [cbn; lia|]; intros j d Hd; destruct j; discriminate.
  - set (d' := HDisplay.asub base (fun j => nth j out AId) d) in E.
    assert (Gen : forall x sh0, HDisplay.assemble_go base shr cnt (S k) ds (out ++ [x]) sh0 = (out', shared') ->
              (x = d' \/ exists sh, x = AAtom (base + sh) /\ exists sext, shared' = sh0 ++ sext /\ nth_error shared' sh = Some d') ->
              (exists ext, out' = out ++ ext) /\ (exists sext, shared' = sh0 ++ sext) /\ length out' = k + length (d :: ds) /\
              forall j d0, nth_error (d :: ds) j = Some d0 -> alt (base + (k + j)) d0 ->
                forall σ, (forall j', j' < k + j -> σ j' = nth j' out' AId) ->
                nth (k + j) out' AId = HDisplay.asub base σ d0 \/
                exists sh, nth (k + j) out' AId = AAtom (base + sh) /\ nth_error shared' sh = Some (HDisplay.asub base σ d0)).
    { intros x sh0 Ex Hx.
      destruct (IH (S k) (out ++ [x]) sh0 out' shared' Ex ltac:(rewrite length_app; cbn; lia))
        as [[ext Eo] [[sext Es] [Lo Sp]]].
      split; [exists (x :: ext); rewrite Eo, <- app_assoc; reflexivity|split; [exists sext; exact Es|split; [cbn; lia|]]].
      intros [|j] d0 Hd0 Ad σ Hσ.
      - cbn in Hd0; injection Hd0 as <-.
        assert (Nx : nth (k + 0) out' AId = x) by (rewrite Eo, <- app_assoc, app_nth2 by lia; rewrite Lk, Nat.add_0_r, Nat.sub_diag; reflexivity).
        assert (Sd : d' = HDisplay.asub base σ d).
        { assert (Ag : forall j', base + j' < base + (k + 0) -> nth j' out AId = σ j').
          { intros j' Lj; rewrite Hσ by lia; rewrite Eo, <- app_assoc, app_nth1 by lia; reflexivity. }
          apply (proj1 (asub_ext _ _ _ Ag)), Ad. }
        rewrite Nx, <- Sd; destruct Hx as [->|[sh [-> [sext' [_ Hs]]]]]; [left; reflexivity|right; exists sh; split; [reflexivity|exact Hs]].
      - cbn in Hd0; replace (k + S j) with (S k + j) by lia.
        apply (Sp j d0 Hd0); [replace (base + (S k + j)) with (base + (k + S j)) by lia; exact Ad|].
        intros j' Lj; apply Hσ; lia. }
    destruct (shr && Nat.leb 2 _ && negb (HDisplay.trivial d')) eqn:B.
    + destruct (Gen _ _ E) as [Eo [[sext Es] R]].
      * right; exists (length shared); split; [reflexivity|].
        destruct (IH (S k) _ _ out' shared' E ltac:(rewrite length_app; cbn; lia)) as [_ [[sext Es] _]].
        exists sext; split; [exact Es|].
        rewrite Es, nth_error_app1 by (rewrite length_app; cbn; lia); rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity.
      * split; [exact Eo|split; [exists (d' :: sext); rewrite Es, <- app_assoc; reflexivity|exact R]].
    + apply (Gen _ _ E); left; reflexivity.
Qed.

Lemma comp_l_ca (N : cmodel) x y (c : cU N) : @ca N (HDisplay.comp_l x y) c = @ca N (ACompose x y) c.
Proof.
  revert y c; induction x; intros y c; try reflexivity.
  cbn [HDisplay.comp_l]; rewrite IHx1; cbn [ca]; rewrite IHx2; reflexivity.
Qed.

Lemma lassoc_ca (N : cmodel) :
  (forall d (c : cU N), @ca N (HDisplay.lassoc d) c = @ca N d c)
  /\ (forall t (c : cU N), @ct N (HDisplay.tlassoc t) c = @ct N t c /\ CNorm.is_bind (HDisplay.tlassoc t) = CNorm.is_bind t)
  /\ (forall p (c : cU N), @cp N (HDisplay.plassoc p) c = @cp N p c /\ fpb (HDisplay.plassoc p) = fpb p).
Proof.
  apply exp_mind; intros; cbn [HDisplay.lassoc HDisplay.tlassoc HDisplay.plassoc]; try (split; reflexivity); try reflexivity.
  - rewrite comp_l_ca; cbn [ca]; rewrite H, H0; reflexivity.
  - cbn [ca]; rewrite H; reflexivity.
  - cbn [ca]; rewrite (proj1 (H c)), H0; reflexivity.
  - cbn [ca]; rewrite H; reflexivity.
  - cbn [ct]; destruct (H c) as [E1 E2]; rewrite E1, E2; split; reflexivity.
  - cbn [ct CNorm.is_bind]; destruct (H c) as [_ B]; rewrite B; split; [|reflexivity].
    destruct (CNorm.is_bind t); [apply (proj1 (H c))|apply (proj1 (H _))].
  - cbn [ct]; rewrite H; split; reflexivity.
  - cbn [cp fpb]; destruct (H0 (@ca N a c)) as [E1 E2]; rewrite H, E1, E2; split; reflexivity.
  - cbn [cp fpb]; destruct (H (cpop h c)) as [E1 E2]; rewrite E1, E2; split; reflexivity.
Qed.

(** ** The display means the word *)

Theorem display_sound0 shr T i shared root ci : Inv T -> RId T i ci ->
  (match HDisplay.dref F base (4 * Pos.to_nat (HNorm.next T) + 16) i (HDisplay.dstart T) with
   | Some (r, D) => Some (HDisplay.assemble base shr r D) | None => None end) = Some (shared, root) ->
  (forall s d, nth_error shared s = Some d -> forall x, catom (base + s) x = @ca M d x) ->
  forall c, @ca M root c = wden ci c.
Proof.
  intros I Hi E HS.
  destruct (HDisplay.dref F base _ i (HDisplay.dstart T)) as [[r D]|] eqn:Er; [|discriminate]; injection E as E.
  assert (DI0 : DInv (HDisplay.dstart T)).
  { constructor; cbn; [exact I|reflexivity| |intros k L; lia].
    intros i' k E'; rewrite PositiveMap.gempty in E'; discriminate. }
  destruct (proj1 (disp_spec _) i _ r D DI0 (ex_intro _ ci Hi) Er) as [DI [X [Ar Sr]]].
  unfold HDisplay.assemble in E.
  destruct (HDisplay.assemble_go base shr _ 0 (rev (HDisplay.ddefs D)) [] []) as [out sh] eqn:Eg; injection E as <- <-.
  destruct (assemble_go_spec shr _ _ 0 [] [] out sh Eg eq_refl) as [_ [_ [_ Sg]]].
  set (σ := fun j => nth j out AId).
  assert (Claim : forall j, j < HDisplay.dn D -> forall i' ci', PositiveMap.find i' (HDisplay.dmemo D) = Some j ->
                    RId (HDisplay.dT D) i' ci' -> forall c, @ca M (σ j) c = wden ci' c).
  { intros j; induction j as [j IHj] using (well_founded_induction lt_wf); intros Lj i' ci' Fj H' c.
    destruct (di_memo D DI i' j Fj) as [_ [_ [d [Hd [Ad Sd]]]]].
    assert (Ag : Agree D (fun j' y => @ca M (σ j') y) j).
    { intros i'' k'' F'' L'' ci'' H'' c''; apply (IHj k'' L'' ltac:(lia) i'' ci'' F'' H''). }
    destruct (Sg j d Hd Ad σ (fun j' _ => eq_refl)) as [Eo|[s0 [Eo Es]]]; cbn [Nat.add] in Eo; unfold σ at 1; rewrite Eo.
    - rewrite (proj1 (asub_ca σ)); apply (Sd _ Ag ci' H').
    - cbn [ca]; rewrite (HS s0 _ Es c), (proj1 (asub_ca σ)); apply (Sd _ Ag ci' H'). }
  intros c; rewrite (proj1 (asub_ca σ)).
  apply (Sr _); [|apply (RId_mono _ _ _ _ (proj1 X) Hi)].
  intros i' k F' L' ci' H' c'; apply (Claim k L' i' ci' F' H').
Qed.


Theorem display_s_sound shr T i shared root ci : Inv T -> RId T i ci ->
  HDisplay.display_s F base shr T i = Some (shared, root) ->
  (forall s d, nth_error shared s = Some d -> forall x, catom (base + s) x = @ca M d x) ->
  forall c, @ca M root c = wden ci c.
Proof.
  intros I Hi E HS; unfold HDisplay.display_s in E.
  destruct (HDisplay.dref F base _ i (HDisplay.dstart T)) as [[r D]|] eqn:Er; [|discriminate].
  destruct (HDisplay.assemble base shr r D) as [sh0 r0] eqn:Ea; injection E as <- <-.
  intros c; rewrite (proj1 (lassoc_ca M)).
  apply (display_sound0 shr T i sh0 r0 ci I Hi); [rewrite Er, Ea; reflexivity|].
  intros s d Hd x; rewrite (HS s (HDisplay.lassoc d)) by (rewrite nth_error_map, Hd; reflexivity).
  apply (proj1 (lassoc_ca M)).
Qed.

Theorem display_sound T i shared root ci : Inv T -> RId T i ci ->
  HDisplay.display F base T i = Some (shared, root) ->
  (forall s d, nth_error shared s = Some d -> forall x, catom (base + s) x = @ca M d x) ->
  forall c, @ca M root c = wden ci c.
Proof. apply display_s_sound. Qed.

End Sound.
