(** * The shared normaliser computes the unshared one

    [HNorm] is [CNorm] with hash-consing.  A hash-consed word stands for
    the [CNorm] word read off its cells through the table ([RWord],
    [RId]); under the table's invariants ([Inv]) this reading is a
    function and is injective, and each operation of [HNorm] reads as the
    corresponding one of [CNorm].  So [hn_eq] is [cn_eq] ([hn_eq_cn]),
    and decides equality in comprehension models ([hn_eq_correct]). *)

From Stdlib Require Import String List PArith NArith Arith Bool FMapPositive Lia.
From ShiftedNames.Core Require Import Label Normalise GEval.
From ShiftedNames.Core Require HNorm CNorm.
From ShiftedNames.Core Require Import Comp CSound CComplete.
Import ListNotations.

(** ** Equality of shared values and steps *)

Lemma hval_eqb_eq a b : HNorm.val_eqb a b = true <-> a = b.
Proof.
  destruct a as [h i|u o p|h i x], b as [h' i'|u' o' p'|h' i' x']; cbn; try (split; intros H; congruence);
    rewrite ?andb_true_iff, ?lexp_eqb_eq, ?Nat.eqb_eq, ?Pos.eqb_eq.
  - split; [intros [-> ->]; reflexivity|intros E; injection E as -> ->; auto].
  - assert (O : HNorm.oeqb o o' = true <-> o = o').
    { destruct o, o'; cbn; split; intros H; try discriminate; try reflexivity.
      - apply Nat.eqb_eq in H; subst; reflexivity.
      - injection H as ->; apply Nat.eqb_refl. }
    rewrite O; split; [intros [[-> ->] ->]; reflexivity|intros E; injection E as -> -> ->; auto].
  - split; [intros [[-> ->] ->]; reflexivity|intros E; injection E as -> -> ->; auto].
Qed.

Lemma hstep_eqb_eq a b : HNorm.step_eqb a b = true <-> a = b.
Proof.
  destruct a as [h v|h|n], b as [h' v'|h'|n']; cbn; try (split; intros H; congruence);
    rewrite ?andb_true_iff, ?lexp_eqb_eq, ?Nat.eqb_eq, ?hval_eqb_eq.
  - split; [intros [-> ->]; reflexivity|intros E; injection E as -> ->; auto].
  - split; [intros ->; reflexivity|intros E; injection E as ->; auto].
  - split; [intros ->; reflexivity|intros E; injection E as ->; auto].
Qed.

Section Refine.

Variable F : order.
Hypothesis Hirr : forall a, lt_known F a a = false.
Hypothesis Htrans : forall a b c, lt_known F a b = true -> lt_known F b c = true -> lt_known F a c = true.

Lemma kd_same a b : HNorm.kd F a b = CNorm.kd F a b.
Proof. reflexivity. Qed.

Lemma before_same a b : HNorm.before F a b = CNorm.before F a b.
Proof. reflexivity. Qed.

(** ** Reading shared words *)

Definition cellof (S : HNorm.st) (i : positive) : option (HNorm.step * positive) := PositiveMap.find i (HNorm.cells S).

Inductive RId (S : HNorm.st) : positive -> CNorm.cword -> Prop :=
| RNil : RId S 1 []
| RCons i s t cs cw : cellof S i = Some (s, t) -> RStep S s cs -> RId S t cw -> RId S i (cs :: cw)
with RStep (S : HNorm.st) : HNorm.step -> CNorm.cstep -> Prop :=
| RSE h v cv : RVal S v cv -> RStep S (HNorm.SE h v) (CNorm.SE h cv)
| RSW h : RStep S (HNorm.SW h) (CNorm.SW h)
| RSA a : RStep S (HNorm.SA a) (CNorm.SA a)
with RVal (S : HNorm.st) : HNorm.val -> CNorm.cval -> Prop :=
| RVVar h i : RVal S (HNorm.VVar h i) (CNorm.VVar h i)
| RVTerm u b p cw : RId S p cw -> RVal S (HNorm.VTerm u b p) (CNorm.VTerm u b cw)
| RVLook h i x cw : RId S x cw -> RVal S (HNorm.VLook h i x) (CNorm.VLook h i cw).

Scheme RId_mind := Induction for RId Sort Prop
with RStep_mind := Induction for RStep Sort Prop
with RVal_mind := Induction for RVal Sort Prop.
Combined Scheme R_mind from RId_mind, RStep_mind, RVal_mind.

(** A word, cell by cell. *)
Inductive RWord (S : HNorm.st) : HNorm.word -> CNorm.cword -> Prop :=
| RWNil : RWord S [] []
| RWCons s i w cs cw : cellof S i = Some (s, HNorm.wid w) -> RStep S s cs -> RWord S w cw ->
    RWord S ((s, i) :: w) (cs :: cw).

Lemma RWord_RId S w cw : RWord S w cw -> RId S (HNorm.wid w) cw.
Proof. intros H; induction H as [|s i w cs cw Hc Hs Hw IH]; cbn; [apply RNil|apply (RCons S i s (HNorm.wid w)); assumption]. Qed.

(** ** The table's invariants *)

Record Inv (S : HNorm.st) : Prop := {
  inv_next : forall i c, cellof S i = Some c -> (i < HNorm.next S)%positive /\ i <> 1%positive;
  inv_next2 : (1 < HNorm.next S)%positive;
  inv_uniq : forall i j c, cellof S i = Some c -> cellof S j = Some c -> i = j;
  inv_sound : forall t l s i, PositiveMap.find t (HNorm.tab S) = Some l -> In (s, i) l -> cellof S i = Some (s, t);
  inv_compl : forall i s t, cellof S i = Some (s, t) ->
    exists l, PositiveMap.find t (HNorm.tab S) = Some l /\ In (s, i) l
}.

Lemma Inv_st0 : Inv HNorm.st0.
Proof.
  constructor; unfold cellof; cbn; intros; rewrite ?PositiveMap.gempty in *; try discriminate; try lia.
Qed.

(** The table only grows. *)
Definition Ext (S S' : HNorm.st) : Prop := forall i c, cellof S i = Some c -> cellof S' i = Some c.

Lemma Ext_refl S : Ext S S.
Proof. intros i c H; exact H. Qed.

Lemma Ext_trans S1 S2 S3 : Ext S1 S2 -> Ext S2 S3 -> Ext S1 S3.
Proof. intros H1 H2 i c H; apply H2, H1, H. Qed.

Lemma R_mono S S' : Ext S S' ->
  (forall i cw, RId S i cw -> RId S' i cw)
  /\ (forall s cs, RStep S s cs -> RStep S' s cs)
  /\ (forall v cv, RVal S v cv -> RVal S' v cv).
Proof.
  intros E; apply (R_mind S (fun i cw _ => RId S' i cw) (fun s cs _ => RStep S' s cs) (fun v cv _ => RVal S' v cv));
    intros; econstructor; eauto.
Qed.

Lemma RWord_mono S S' : Ext S S' -> forall w cw, RWord S w cw -> RWord S' w cw.
Proof.
  intros E w cw H; induction H as [|s i w cs cw Hc Hs Hw IH].
  - apply RWNil.
  - apply RWCons; [apply E, Hc|apply (proj1 (proj2 (R_mono S S' E))), Hs|exact IH].
Qed.

(** The reading is a function. *)
Lemma R_func S : Inv S ->
  (forall i cw, RId S i cw -> forall cw', RId S i cw' -> cw = cw')
  /\ (forall s cs, RStep S s cs -> forall cs', RStep S s cs' -> cs = cs')
  /\ (forall v cv, RVal S v cv -> forall cv', RVal S v cv' -> cv = cv').
Proof.
  intros I.
  apply (R_mind S (fun i cw _ => forall cw', RId S i cw' -> cw = cw')
                  (fun s cs _ => forall cs', RStep S s cs' -> cs = cs')
                  (fun v cv _ => forall cv', RVal S v cv' -> cv = cv')); intros.
  - inversion H; subst; [reflexivity|].
    destruct (inv_next S I 1 _ H0) as [_ N]; contradiction.
  - inversion H1; subst.
    + destruct (inv_next S I 1 _ e) as [_ N]; contradiction.
    + rewrite e in H2; injection H2 as -> ->; f_equal; auto.
  - inversion H0; subst; f_equal; auto.
  - inversion H; reflexivity.
  - inversion H; reflexivity.
  - inversion H; reflexivity.
  - inversion H0; subst; f_equal; auto.
  - inversion H0; subst; f_equal; auto.
Qed.

(** And it is injective: equal readings, equal ids. *)
Lemma R_inj S : Inv S ->
  (forall i cw, RId S i cw -> forall j, RId S j cw -> i = j)
  /\ (forall s cs, RStep S s cs -> forall s', RStep S s' cs -> s = s')
  /\ (forall v cv, RVal S v cv -> forall v', RVal S v' cv -> v = v').
Proof.
  intros I.
  apply (R_mind S (fun i cw _ => forall j, RId S j cw -> i = j)
                  (fun s cs _ => forall s', RStep S s' cs -> s = s')
                  (fun v cv _ => forall v', RVal S v' cv -> v = v')); intros.
  - inversion H; reflexivity.
  - inversion H1 as [|j' s' t' cs' cw' Hc' Hs' Ht']; subst.
    pose proof (H0 _ Ht') as <-; pose proof (H _ Hs') as <-.
    apply (inv_uniq S I i j (s, t)); [exact e|exact Hc'].
  - inversion H0; subst; f_equal; auto.
  - inversion H; reflexivity.
  - inversion H; reflexivity.
  - inversion H; reflexivity.
  - inversion H0; subst; f_equal; auto.
  - inversion H0; subst; f_equal; auto.
Qed.

(** ** Hash-consing *)

Lemma Inv_fresh S : Inv S -> cellof S (HNorm.next S) = None.
Proof.
  intros I; destruct (cellof S (HNorm.next S)) as [c|] eqn:E; [|reflexivity].
  destruct (inv_next S I _ _ E) as [L _]; lia.
Qed.

Lemma hcons_spec S s w cs cw w' S' :
  Inv S -> RStep S s cs -> RWord S w cw -> HNorm.hcons s w S = (w', S') ->
  Inv S' /\ Ext S S' /\ RWord S' w' (cs :: cw).
Proof.
  intros I Hs Hw E; unfold HNorm.hcons in E.
  set (t := HNorm.wid w) in E.
  set (bucket := match PositiveMap.find t (HNorm.tab S) with Some l => l | None => [] end) in E.
  destruct (find (fun p => HNorm.step_eqb (fst p) s) bucket) as [[s' i]|] eqn:Fd.
  - injection E as <- <-.
    apply find_some in Fd as [In1 Eq1]; cbn in Eq1; apply hstep_eqb_eq in Eq1; subst s'.
    assert (C : cellof S i = Some (s, t)).
    { unfold bucket in In1; destruct (PositiveMap.find t (HNorm.tab S)) as [l|] eqn:Ft; [|contradiction].
      apply (inv_sound S I t l s i Ft In1). }
    split; [exact I|split; [apply Ext_refl|]]; apply RWCons; assumption.
  - injection E as <- <-.
    set (i := HNorm.next S).
    assert (Fr : cellof S i = None) by (apply Inv_fresh, I).
    assert (X : Ext S (HNorm.mk_st (PositiveMap.add t ((s, i) :: bucket) (HNorm.tab S))
                       (PositiveMap.add i (s, t) (HNorm.cells S)) (Pos.succ i))).
    { intros j c Hj; unfold cellof in *; cbn; rewrite PositiveMap.gso; [exact Hj|intros ->; congruence]. }
    split; [|split; [exact X|apply RWCons; [unfold cellof; cbn; apply PositiveMap.gss| |];
                                       [apply (proj1 (proj2 (R_mono _ _ X))), Hs|apply (RWord_mono _ _ X), Hw]]].
    constructor; unfold cellof; cbn.
    + intros j c Hj; destruct (Pos.eq_dec j i) as [->|N]; [split; [lia|]; pose proof (inv_next2 S I); lia|].
      rewrite PositiveMap.gso in Hj by exact N; destruct (inv_next S I j c Hj); split; [lia|assumption].
    + pose proof (inv_next2 S I); lia.
    + intros j k c Hj Hk.
      destruct (Pos.eq_dec j i) as [->|Nj], (Pos.eq_dec k i) as [->|Nk]; [reflexivity| | |].
      * rewrite PositiveMap.gss in Hj; rewrite PositiveMap.gso in Hk by exact Nk; injection Hj as <-.
        destruct (inv_compl S I k s t Hk) as [l [Fl Il]].
        assert (Bl : bucket = l) by (unfold bucket; rewrite Fl; reflexivity); subst l.
        pose proof (find_none _ _ Fd _ Il) as Z; cbn in Z; rewrite (proj2 (hstep_eqb_eq s s) eq_refl) in Z; discriminate.
      * rewrite PositiveMap.gss in Hk; rewrite PositiveMap.gso in Hj by exact Nj; injection Hk as <-.
        destruct (inv_compl S I j s t Hj) as [l [Fl Il]].
        assert (Bl : bucket = l) by (unfold bucket; rewrite Fl; reflexivity); subst l.
        pose proof (find_none _ _ Fd _ Il) as Z; cbn in Z; rewrite (proj2 (hstep_eqb_eq s s) eq_refl) in Z; discriminate.
      * rewrite PositiveMap.gso in Hj, Hk by assumption; apply (inv_uniq S I j k c Hj Hk).
    + intros t' l s'' j Ft' Ij.
      destruct (Pos.eq_dec t' t) as [->|Nt].
      * rewrite PositiveMap.gss in Ft'; injection Ft' as <-; destruct Ij as [Ej|Ij].
        -- injection Ej as <- <-; apply PositiveMap.gss.
        -- unfold bucket in Ij; destruct (PositiveMap.find t (HNorm.tab S)) as [l0|] eqn:F0; [|contradiction].
           pose proof (inv_sound S I t l0 s'' j F0 Ij) as Cj; apply X, Cj.
      * rewrite PositiveMap.gso in Ft' by exact Nt; apply X, (inv_sound S I t' l s'' j Ft' Ij).
    + intros j s'' t' Hj; destruct (Pos.eq_dec j i) as [->|Nj].
      * rewrite PositiveMap.gss in Hj; injection Hj as <- <-; exists ((s, i) :: bucket); split; [apply PositiveMap.gss|left; reflexivity].
      * rewrite PositiveMap.gso in Hj by exact Nj; destruct (inv_compl S I j s'' t' Hj) as [l [Fl Il]].
        destruct (Pos.eq_dec t' t) as [->|Nt].
        -- exists ((s, i) :: bucket); split; [apply PositiveMap.gss|right; unfold bucket; rewrite Fl; exact Il].
        -- exists l; split; [rewrite PositiveMap.gso by exact Nt; exact Fl|exact Il].
Qed.

Lemma Forall2_mono S S' p cp : Ext S S' -> Forall2 (RStep S) p cp -> Forall2 (RStep S') p cp.
Proof. intros X H; eapply Forall2_impl; [|exact H]; intros a b; apply (proj1 (proj2 (R_mono S S' X))). Qed.

Lemma rebuild_spec pre : forall cpre S w cw w' S',
  Inv S -> Forall2 (RStep S) pre cpre -> RWord S w cw -> HNorm.rebuild pre w S = (w', S') ->
  Inv S' /\ Ext S S' /\ RWord S' w' (cpre ++ cw).
Proof.
  induction pre as [|s pre IH]; intros cpre S w cw w' S' I Hp Hw E; cbn in E.
  - injection E as <- <-; inversion Hp; subst; split; [exact I|split; [apply Ext_refl|exact Hw]].
  - inversion Hp as [|? cs ? cpre' Hs Hp']; subst.
    destruct (HNorm.rebuild pre w S) as [w1 S1] eqn:E1.
    destruct (IH cpre' S w cw w1 S1 I Hp' Hw E1) as [I1 [X1 Hw1]].
    destruct (hcons_spec S1 s w1 cs (cpre' ++ cw) w' S' I1 (proj1 (proj2 (R_mono _ _ X1)) _ _ Hs) Hw1 E) as [I2 [X2 Hw2]].
    split; [exact I2|split; [apply (Ext_trans _ _ _ X1 X2)|exact Hw2]].
Qed.

Lemma place_spec s p r cs cp cr S w' S' :
  Inv S -> RStep S s cs -> Forall2 (RStep S) p cp -> RWord S r cr -> HNorm.place s p r S = (w', S') ->
  Inv S' /\ Ext S S' /\ RWord S' w' (cp ++ cs :: cr).
Proof.
  intros I Hs Hp Hr E; unfold HNorm.place in E; destruct (HNorm.hcons s r S) as [r1 S1] eqn:E1.
  destruct (hcons_spec S s r cs cr r1 S1 I Hs Hr E1) as [I1 [X1 Hr1]].
  destruct (rebuild_spec p cp S1 r1 (cs :: cr) w' S' I1 (Forall2_mono _ _ _ _ X1 Hp) Hr1 E) as [I2 [X2 H2]].
  split; [exact I2|split; [apply (Ext_trans _ _ _ X1 X2)|exact H2]].
Qed.

(** ** The operations *)

Definition hlabel (s : HNorm.step) : option lexp :=
  match s with HNorm.SE h _ | HNorm.SW h => Some h | HNorm.SA _ => None end.

Lemma RStep_label S s cs : RStep S s cs -> hlabel s = CNorm.slabel cs.
Proof. intros H; inversion H; reflexivity. Qed.

Lemma stop_rel S h w cw : RWord S w cw ->
  Forall2 (RStep S) (fst (HNorm.stop F h w)) (fst (CNorm.stop F h cw))
  /\ RWord S (snd (HNorm.stop F h w)) (snd (CNorm.stop F h cw)).
Proof.
  intros H; induction H as [|s i w cs cw Hc Hs Hw IH]; cbn [HNorm.stop CNorm.stop].
  - split; [constructor|constructor].
  - inversion Hs; subst; cbn [fst snd].
    + destruct (HNorm.before F h0 h) eqn:B; rewrite <- before_same, B.
      * destruct (HNorm.stop F h w) as [p r], (CNorm.stop F h cw) as [cp cr]; cbn in IH |- *.
        destruct IH as [IH1 IH2]; split; [constructor; [exact Hs|exact IH1]|exact IH2].
      * split; [constructor|apply RWCons; assumption].
    + destruct (HNorm.before F h0 h) eqn:B; rewrite <- before_same, B.
      * destruct (HNorm.stop F h w) as [p r], (CNorm.stop F h cw) as [cp cr]; cbn in IH |- *.
        destruct IH as [IH1 IH2]; split; [constructor; [exact Hs|exact IH1]|exact IH2].
      * split; [constructor|apply RWCons; assumption].
    + split; [constructor|apply RWCons; assumption].
Qed.

Lemma Forall2_rev_RStep S p cp : Forall2 (RStep S) p cp -> Forall2 (RStep S) (rev p) (rev cp).
Proof.
  induction 1 as [|s cs p cp Hs Hp IH]; cbn [rev]; [constructor|].
  apply Forall2_app; [exact IH|constructor; [exact Hs|constructor]].
Qed.

Lemma lexp_eqb_refl' a : lexp_eqb a a = true.
Proof. apply lexp_eqb_eq; reflexivity. Qed.

Lemma lexp_eqb_false_iff a b : lexp_eqb a b = false <-> a <> b.
Proof.
  split; intros H. - intros E; apply lexp_eqb_eq in E; congruence.
  - destruct (lexp_eqb a b) eqn:E; [apply lexp_eqb_eq in E; contradiction|reflexivity].
Qed.

(** The frontier passes or fails a label as the kept steps do. *)
Definition FrOf (fr : list lexp) (ckept : CNorm.cword) : Prop :=
  forall l, forallb (fun m => CNorm.before F m l) fr = forallb (CNorm.sbef F l) ckept.

Lemma FrOf_nil : FrOf [] [].
Proof. intros l; reflexivity. Qed.

Lemma before_trans a b c : CNorm.before F a b = true -> CNorm.before F b c = true -> CNorm.before F a c = true.
Proof.
  unfold CNorm.before, lcmp.
  destruct (lexp_eqb a b) eqn:Eab; [discriminate|]; destruct (lt_known F a b) eqn:Lab; [|destruct (lt_known F b a); discriminate].
  destruct (lexp_eqb b c) eqn:Ebc; [discriminate|]; destruct (lt_known F b c) eqn:Lbc; [|destruct (lt_known F c b); discriminate].
  intros _ _; pose proof (Htrans a b c Lab Lbc) as Lac.
  destruct (lexp_eqb a c) eqn:Eac; [|rewrite Lac; reflexivity].
  apply lexp_eqb_eq in Eac; subst c; rewrite Hirr in Lac; discriminate.
Qed.

Lemma FrOf_cons L ckept g cs : FrOf L ckept -> CNorm.slabel cs = Some g -> FrOf (g :: L) (cs :: ckept).
Proof. intros H Eg l; cbn [forallb]; unfold CNorm.sbef at 1; rewrite Eg, H; reflexivity. Qed.

Lemma addf_go_none y fr : HNorm.addf_go F y fr = None ->
  exists m, In m fr /\ (y = m \/ CNorm.before F y m = true).
Proof.
  induction fr as [|m r IH]; cbn [HNorm.addf_go]; [discriminate|].
  destruct (lcmp F y m) as [[| |]|] eqn:C; intros E.
  - exists m; split; [left; reflexivity|left].
    unfold lcmp in C; destruct (lexp_eqb y m) eqn:Q; [apply lexp_eqb_eq, Q|].
    destruct (lt_known F y m); [discriminate|destruct (lt_known F m y); discriminate].
  - exists m; split; [left; reflexivity|right; unfold CNorm.before; rewrite C; reflexivity].
  - destruct (IH E) as [m' [I' H']]; exists m'; split; [right; exact I'|exact H'].
  - destruct (HNorm.addf_go F y r) eqn:E'; [discriminate|].
    destruct (IH eq_refl) as [m' [I' H']]; exists m'; split; [right; exact I'|exact H'].
Qed.

Lemma addf_go_some y fr : forall r, HNorm.addf_go F y fr = Some r -> forall l, CNorm.before F y l = true ->
  forallb (fun m => CNorm.before F m l) r = forallb (fun m => CNorm.before F m l) fr.
Proof.
  induction fr as [|m fr IH]; intros r E l By; cbn [HNorm.addf_go] in E; [injection E as <-; reflexivity|].
  destruct (lcmp F y m) as [[| |]|] eqn:C; [discriminate|discriminate| |].
  - assert (Bm : CNorm.before F m y = true).
    { unfold lcmp in C; unfold CNorm.before, lcmp.
      destruct (lexp_eqb y m) eqn:Q; [discriminate|]; destruct (lt_known F y m); [discriminate|].
      destruct (lt_known F m y) eqn:L; [|discriminate].
      assert (Q' : lexp_eqb m y = false) by (apply lexp_eqb_false_iff; intros ->; rewrite lexp_eqb_refl' in Q; discriminate).
      rewrite Q'; reflexivity. }
    cbn [forallb]; rewrite (before_trans m y l Bm By), (IH r E l By); reflexivity.
  - destruct (HNorm.addf_go F y fr) as [r'|] eqn:E'; [|discriminate]; injection E as <-.
    cbn [forallb]; rewrite (IH r' eq_refl l By); reflexivity.
Qed.

Lemma addf_ok y fr l :
  forallb (fun m => CNorm.before F m l) (HNorm.addf F y fr) = CNorm.before F y l && forallb (fun m => CNorm.before F m l) fr.
Proof.
  unfold HNorm.addf; destruct (HNorm.addf_go F y fr) as [r|] eqn:E.
  - cbn [forallb]; destruct (CNorm.before F y l) eqn:By; [|reflexivity].
    rewrite (addf_go_some y fr r E l By); reflexivity.
  - destruct (addf_go_none y fr E) as [m [Im Hm]].
    destruct (forallb (fun m => CNorm.before F m l) fr) eqn:A; [|rewrite andb_false_r; reflexivity].
    rewrite forallb_forall in A; pose proof (A m Im) as Am; rewrite andb_true_r; symmetry.
    destruct Hm as [->|Hm]; [exact Am|apply (before_trans y m l Hm Am)].
Qed.

Lemma mergef_ok pend : forall fr l,
  forallb (fun m => CNorm.before F m l) (HNorm.mergef F pend fr) = forallb (fun m => CNorm.before F m l) (pend ++ fr).
Proof.
  induction pend as [|y p IH]; intros fr l; [reflexivity|].
  cbn [HNorm.mergef app forallb]; rewrite IH, !forallb_app, addf_ok.
  destruct (CNorm.before F y l), (forallb (fun m => CNorm.before F m l) p); reflexivity.
Qed.

Lemma decide_rel h l fr pend ckept : FrOf (pend ++ fr) ckept ->
  let '(p, fr1, pend1) := HNorm.decide F h l fr pend in
  p = CNorm.passes F h l ckept /\ FrOf (pend1 ++ fr1) ckept.
Proof.
  intros H; unfold HNorm.decide, CNorm.passes; change (HNorm.kd F h l) with (CNorm.kd F h l).
  change (HNorm.before F) with (CNorm.before F).
  destruct (CNorm.kd F h l); cbn [andb]; [|split; [reflexivity|exact H]].
  split; [rewrite mergef_ok; apply H|intros m; cbn [app]; rewrite mergef_ok; apply H].
Qed.

Lemma Forall2_skipn {A B} (R : A -> B -> Prop) n : forall p q, Forall2 R p q -> Forall2 R (skipn n p) (skipn n q).
Proof. induction n as [|n IH]; intros p q H; [exact H|destruct H; [constructor|apply IH, H0]]. Qed.

Lemma follow_stuck S h i kept ckept n mark cmark cw v S' :
  Inv S -> Forall2 (RStep S) kept ckept -> RWord S mark cmark -> cmark = rev (firstn n ckept) ++ cw ->
  HNorm.payload h i kept n mark S = (v, S') ->
  Inv S' /\ Ext S S' /\ RVal S' v (CNorm.VLook h i (rev ckept ++ cw)).
Proof.
  intros I Hk Hm Em E; unfold HNorm.payload in E.
  destruct (HNorm.rebuild (rev (skipn n kept)) mark S) as [r S1] eqn:Er; injection E as <- <-.
  destruct (rebuild_spec (rev (skipn n kept)) (rev (skipn n ckept)) S mark cmark r S1 I
              (Forall2_rev_RStep S _ _ (Forall2_skipn _ n _ _ Hk)) Hm Er) as [I1 [X1 H1]].
  split; [exact I1|split; [exact X1|constructor; apply RWord_RId]].
  rewrite Em, app_assoc, <- rev_app_distr, firstn_skipn in H1; exact H1.
Qed.

Lemma follow_spec S h w cw : Inv S -> RWord S w cw -> forall i kept ckept fr pend n mark cmark v S',
  Forall2 (RStep S) kept ckept -> FrOf (pend ++ fr) ckept -> RWord S mark cmark -> cmark = rev (firstn n ckept) ++ cw ->
  HNorm.follow F h i kept fr pend n mark w S = (v, S') ->
  Inv S' /\ Ext S S' /\ RVal S' v (CNorm.follow F h i ckept cw).
Proof.
  intros I H; induction H as [|s x w cs cw Hc Hs Hw IH]; intros i kept ckept fr pend n mark cmark v S' Hk Hl Hm Em E.
  - destruct Hk as [|t ct kept ckept Ht Hk']; cbn [HNorm.follow CNorm.follow] in E |- *.
    + injection E as <- <-; split; [exact I|split; [apply Ext_refl|constructor]].
    + pose proof (follow_stuck S h i (t :: kept) (ct :: ckept) n mark cmark [] v S' I (Forall2_cons _ _ Ht Hk') Hm Em E) as R.
      rewrite app_nil_r in R; exact R.
  - assert (Next : forall i' kept' ckept' fr' pend', Forall2 (RStep S) kept' ckept' -> FrOf (pend' ++ fr') ckept' ->
      HNorm.follow F h i' kept' fr' pend' 0 w w S = (v, S') -> Inv S' /\ Ext S S' /\ RVal S' v (CNorm.follow F h i' ckept' cw))
      by (intros i' kept' ckept' fr' pend' Hk2 Hl2 E2; apply (IH i' kept' ckept' fr' pend' 0 w cw v S' Hk2 Hl2 Hw eq_refl E2)).
    assert (Atom : forall a, s = HNorm.SA a -> cs = CNorm.SA a ->
      HNorm.payload h i kept n mark S = (v, S') -> Inv S' /\ Ext S S' /\ RVal S' v (CNorm.VLook h i (rev_append ckept (cs :: cw)))).
    { intros a -> -> E2; rewrite rev_append_rev; apply (follow_stuck S h i kept ckept n mark cmark _ v S' I Hk Hm Em E2). }
    assert (First : forall g, CNorm.slabel cs = Some g -> HNorm.follow F h i [s] [] [g] 1 mark w S = (v, S') ->
      ckept = [] -> Inv S' /\ Ext S S' /\ RVal S' v (CNorm.follow F h i [cs] cw)).
    { intros g Eg E2 ->; apply (IH i _ _ [] [g] 1 mark cmark v S' (Forall2_cons _ _ Hs (Forall2_nil _)) (FrOf_cons _ _ g cs FrOf_nil Eg) Hm);
        [|exact E2].
      rewrite Em; destruct n; reflexivity. }
    assert (Keep : forall g fr1 pend1, CNorm.slabel cs = Some g -> FrOf (pend1 ++ fr1) ckept ->
      HNorm.follow F h i (s :: kept) fr1 (g :: pend1) (Datatypes.S n) mark w S = (v, S') ->
      Inv S' /\ Ext S S' /\ RVal S' v (CNorm.follow F h i (cs :: ckept) cw)).
    { intros g fr1 pend1 Eg Hl1 E2.
      apply (IH i _ _ fr1 (g :: pend1) (Datatypes.S n) mark cmark v S' (Forall2_cons _ _ Hs Hk) (FrOf_cons _ _ g cs Hl1 Eg) Hm);
        [|exact E2].
      rewrite Em; cbn [firstn rev]; destruct ckept; [destruct n; reflexivity|rewrite <- app_assoc; reflexivity]. }
    inversion Hs as [g v0 cv Hv|g|a]; subst s cs; cbn [HNorm.follow CNorm.follow] in E |- *;
      [| |apply (Atom a eq_refl eq_refl E)];
      pose proof (decide_rel h g fr pend ckept Hl) as D;
      destruct (HNorm.decide F h g fr pend) as [[p fr1] pend1]; destruct D as [-> Hl1];
      (destruct (CNorm.passes F h g ckept); [apply (Next i _ _ _ _ Hk Hl1 E)|]);
      (destruct Hk as [|t ct kept' ckept' Ht Hk'];
       [|apply (Keep g fr1 pend1 eq_refl Hl1 E)]).
    + destruct (lexp_eqb g h); [|apply (First g eq_refl E eq_refl)].
      destruct i as [|i]; [injection E as <- <-; split; [exact I|split; [apply Ext_refl|exact Hv]]|].
      apply (Next i [] [] [] [] (Forall2_nil _) FrOf_nil E).
    + destruct (lexp_eqb g h); [apply (Next (Datatypes.S i) [] [] [] [] (Forall2_nil _) FrOf_nil E)|apply (First g eq_refl E eq_refl)].
Qed.

Lemma lookup_spec S h w cw : Inv S -> RWord S w cw -> forall i v S',
  HNorm.lookup F h i w S = (v, S') -> Inv S' /\ Ext S S' /\ RVal S' v (CNorm.lookup F h i cw).
Proof. intros I H i v S' E; apply (follow_spec S h w cw I H i [] [] [] [] 0 w cw v S' (Forall2_nil _) FrOf_nil H eq_refl E). Qed.

Lemma pushW_spec S h w cw w' S' : Inv S -> RWord S w cw -> HNorm.pushW F h w S = (w', S') ->
  Inv S' /\ Ext S S' /\ RWord S' w' (CNorm.pushW F h cw).
Proof.
  intros I Hw E; destruct (stop_rel S h w cw Hw) as [Hp Hr].
  unfold HNorm.pushW in E; unfold CNorm.pushW.
  destruct (HNorm.stop F h w) as [p r], (CNorm.stop F h cw) as [cp cr]; cbn [fst snd] in Hp, Hr.
  destruct Hr as [|s i r' cs cr' Hc Hs Hr'].
  - apply (place_spec (HNorm.SW h) p [] (CNorm.SW h) cp [] S w' S' I (RSW S h) Hp (RWNil S) E).
  - inversion Hs as [g v cv Hv|g|a]; subst.
    + destruct (lexp_eqb g h).
      * apply (rebuild_spec p cp S r' cr' w' S' I Hp Hr' E).
      * apply (place_spec (HNorm.SW h) p _ (CNorm.SW h) cp _ S w' S' I (RSW S h) Hp (RWCons S _ i r' _ cr' Hc Hs Hr') E).
    + apply (place_spec (HNorm.SW h) p _ (CNorm.SW h) cp _ S w' S' I (RSW S h) Hp (RWCons S _ i r' _ cr' Hc Hs Hr') E).
    + apply (place_spec (HNorm.SW h) p _ (CNorm.SW h) cp _ S w' S' I (RSW S h) Hp (RWCons S _ i r' _ cr' Hc Hs Hr') E).
Qed.

Lemma pushE_spec S h v cv w cw w' S' : Inv S -> RVal S v cv -> RWord S w cw -> HNorm.pushE F h v w S = (w', S') ->
  Inv S' /\ Ext S S' /\ RWord S' w' (CNorm.pushE F h cv cw).
Proof.
  intros I Hv Hw E; destruct (stop_rel S h w cw Hw) as [Hp Hr].
  unfold HNorm.pushE in E; unfold CNorm.pushE.
  destruct (HNorm.stop F h w) as [p r], (CNorm.stop F h cw) as [cp cr]; cbn [fst snd] in Hp, Hr.
  assert (Pl : forall S0 r0 cr0, Inv S0 -> Ext S S0 -> RWord S0 r0 cr0 -> HNorm.place (HNorm.SE h v) p r0 S0 = (w', S') ->
     Inv S' /\ Ext S S' /\ RWord S' w' (cp ++ CNorm.SE h cv :: cr0)).
  { intros S0 r0 cr0 I0 X0 H0 E0.
    destruct (place_spec (HNorm.SE h v) p r0 (CNorm.SE h cv) cp cr0 S0 w' S' I0
                (RSE S0 h v cv (proj2 (proj2 (R_mono _ _ X0)) _ _ Hv)) (Forall2_mono _ _ _ _ X0 Hp) H0 E0) as [I1 [X1 H1]].
    split; [exact I1|split; [apply (Ext_trans _ _ _ X0 X1)|exact H1]]. }
  destruct Hr as [|s i r' cs cr' Hc Hs Hr'].
  - apply (Pl S [] [] I (Ext_refl S) (RWNil S) E).
  - assert (Hr : RWord S ((s, i) :: r') (cs :: cr')) by (apply RWCons; assumption).
    inversion Hs as [g v0 cv0 Hv0|g|a]; subst.
    + apply (Pl S _ _ I (Ext_refl S) Hr E).
    + destruct (lexp_eqb g h) eqn:G; cbn [andb]; [|apply (Pl S _ _ I (Ext_refl S) Hr E)].
      destruct (HNorm.lookup F h 0 r' S) as [v' S1] eqn:El.
      destruct (lookup_spec S h r' cr' I Hr' 0 v' S1 El) as [I1 [X1 Hv']].
      assert (Hv1 : RVal S1 v cv) by (apply (proj2 (proj2 (R_mono _ _ X1))), Hv).
      assert (B : HNorm.val_eqb v v' = CNorm.val_eqb cv (CNorm.lookup F h 0 cr')).
      { apply eq_iff_eq_true; rewrite hval_eqb_eq, CNorm.val_eqb_eq; split.
        - intros <-; apply (proj2 (proj2 (R_func S1 I1)) _ _ Hv1 _ Hv').
        - intros Ec; rewrite <- Ec in Hv'; apply (proj2 (proj2 (R_inj S1 I1)) _ _ Hv1 _ Hv'). }
      rewrite <- B; destruct (HNorm.val_eqb v v').
      * destruct (rebuild_spec p cp S1 r' cr' w' S' I1 (Forall2_mono _ _ _ _ X1 Hp) (RWord_mono _ _ X1 _ _ Hr') E)
          as [I2 [X2 H2]].
        split; [exact I2|split; [apply (Ext_trans _ _ _ X1 X2)|exact H2]].
      * apply (Pl S1 _ _ I1 X1 (RWord_mono _ _ X1 _ _ Hr) E).
    + apply (Pl S _ _ I (Ext_refl S) Hr E).
Qed.

(** ** Payloads *)

Lemma unbound_rel S w cw : RWord S w cw ->
  exists cp cb, Forall2 (RStep S) (fst (HNorm.unbound w)) cp /\ RWord S (snd (HNorm.unbound w)) cb
    /\ CNorm.unbound cw = cp ++ cb.
Proof.
  intros H; induction H as [|s i w cs cw Hc Hs Hw IH].
  - exists [], []; repeat split; constructor.
  - destruct IH as [cp [cb [H1 [H2 H3]]]].
    assert (Keep : CNorm.unbound (cs :: cw) = cs :: CNorm.unbound cw ->
      HNorm.unbound ((s, i) :: w) = (s :: fst (HNorm.unbound w), snd (HNorm.unbound w)) ->
      exists cp cb, Forall2 (RStep S) (fst (HNorm.unbound ((s, i) :: w))) cp
        /\ RWord S (snd (HNorm.unbound ((s, i) :: w))) cb /\ CNorm.unbound (cs :: cw) = cp ++ cb).
    { intros Ec Eh; rewrite Ec, Eh, H3; exists (cs :: cp), cb; cbn; repeat split; [constructor; assumption|exact H2]. }
    inversion Hs as [g v cv Hv|g|a]; subst.
    + destruct g as [|c|n].
      * exists cp, cb; cbn [HNorm.unbound CNorm.unbound]; auto.
      * apply Keep; [reflexivity|cbn; destruct (HNorm.unbound w); reflexivity].
      * apply Keep; [reflexivity|cbn; destruct (HNorm.unbound w); reflexivity].
    + destruct g as [|c|n].
      * exists cp, cb; cbn [HNorm.unbound CNorm.unbound]; auto.
      * apply Keep; [reflexivity|cbn; destruct (HNorm.unbound w); reflexivity].
      * apply Keep; [reflexivity|cbn; destruct (HNorm.unbound w); reflexivity].
    + exists [], (CNorm.SA a :: cw); cbn; repeat split; [constructor|apply RWCons; assumption].
Qed.

Lemma has_unbound_rel S w cw : RWord S w cw -> HNorm.has_unbound w = false -> CNorm.unbound cw = cw.
Proof.
  intros H; induction H as [|s i w cs cw Hc Hs Hw IH]; intros Hn; [reflexivity|].
  inversion Hs as [g v cv Hv|g|a]; subst; cbn [HNorm.has_unbound] in Hn; [destruct g as [|c|n]|destruct g as [|c|n]|];
    try discriminate; cbn [CNorm.unbound]; try rewrite IH by exact Hn; reflexivity.
Qed.

Lemma clean_spec S b w cw w' S' : Inv S -> RWord S w cw -> HNorm.clean b w S = (w', S') ->
  Inv S' /\ Ext S S' /\ RWord S' w' (CNorm.clean b cw).
Proof.
  intros I Hw E; destruct b as [n|]; cbn [HNorm.clean CNorm.clean] in E |- *.
  - injection E as <- <-; split; [exact I|split; [apply Ext_refl|exact Hw]].
  - destruct (HNorm.has_unbound w) eqn:Hn.
    + destruct (unbound_rel S w cw Hw) as [cp [cb [H1 [H2 H3]]]]; rewrite H3.
      destruct (HNorm.unbound w) as [p r]; cbn [fst snd] in H1, H2.
      apply (rebuild_spec p cp S r cb w' S' I H1 H2 E).
    + injection E as <- <-; rewrite (has_unbound_rel S w cw Hw Hn).
      split; [exact I|split; [apply Ext_refl|exact Hw]].
Qed.

(** ** The normaliser *)

Lemma is_bind_same t : HNorm.is_bind t = CNorm.is_bind t.
Proof. induction t; cbn; auto. Qed.

Theorem norm_spec_all :
  (forall a K S cK w' S', Inv S -> RWord S K cK -> HNorm.norm F a K S = (w', S') ->
     Inv S' /\ Ext S S' /\ RWord S' w' (CNorm.norm F a cK))
  /\ (forall t K S cK v S', Inv S -> RWord S K cK -> HNorm.tval F t K S = (v, S') ->
     Inv S' /\ Ext S S' /\ RVal S' v (CNorm.tval F t cK))
  /\ (forall p K S cK w' S', Inv S -> RWord S K cK -> HNorm.pnorm F p K S = (w', S') ->
     Inv S' /\ Ext S S' /\ RWord S' w' (CNorm.pnorm F p cK)).
Proof.
  apply exp_mind; intros; cbn [HNorm.norm HNorm.tval HNorm.pnorm CNorm.norm CNorm.tval CNorm.pnorm] in *.
  - injection H1 as <- <-; split; [exact H|split; [apply Ext_refl|exact H0]].
  - apply (hcons_spec S _ K _ cK w' S' H (RSA S n) H0 H1).
  - destruct (HNorm.norm F a K S) as [K1 S1] eqn:E1.
    destruct (H K S cK K1 S1 H1 H2 E1) as [I1 [X1 R1]].
    destruct (H0 K1 S1 _ w' S' I1 R1 H3) as [I2 [X2 R2]].
    split; [exact I2|split; [apply (Ext_trans _ _ _ X1 X2)|exact R2]].
  - destruct (HNorm.pushW F h K S) as [K1 S1] eqn:E1.
    destruct (pushW_spec S h K cK K1 S1 H0 H1 E1) as [I1 [X1 R1]].
    destruct (H K1 S1 _ w' S' I1 R1 H2) as [I2 [X2 R2]].
    split; [exact I2|split; [apply (Ext_trans _ _ _ X1 X2)|exact R2]].
  - destruct (HNorm.tval F t K S) as [v S1] eqn:E1.
    destruct (H K S cK v S1 H1 H2 E1) as [I1 [X1 R1]].
    destruct (HNorm.norm F a K S1) as [K1 S2] eqn:E2.
    destruct (H0 K S1 cK K1 S2 I1 (RWord_mono _ _ X1 _ _ H2) E2) as [I2 [X2 R2]].
    destruct (pushE_spec S2 h v _ K1 _ w' S' I2 (proj2 (proj2 (R_mono _ _ X2)) _ _ R1) R2 H3) as [I3 [X3 R3]].
    split; [exact I3|split; [apply (Ext_trans _ _ _ X1 (Ext_trans _ _ _ X2 X3))|exact R3]].
  - destruct (HNorm.lookup F h 0 K S) as [v S0] eqn:E0.
    destruct (lookup_spec S h K cK H0 H1 0 v S0 E0) as [I0 [X0 R0]].
    destruct (HNorm.pushW F h K S0) as [K1 S1] eqn:E1.
    destruct (pushW_spec S0 h K cK K1 S1 I0 (RWord_mono _ _ X0 _ _ H1) E1) as [I1 [X1 R1]].
    destruct (HNorm.norm F a K1 S1) as [K2 S2] eqn:E2.
    destruct (H K1 S1 _ K2 S2 I1 R1 E2) as [I2 [X2 R2]].
    pose proof (Ext_trans _ _ _ X1 X2) as X12.
    destruct (pushE_spec S2 h v _ K2 _ w' S' I2 (proj2 (proj2 (R_mono _ _ X12)) _ _ R0) R2 H2) as [I3 [X3 R3]].
    split; [exact I3|split; [apply (Ext_trans _ _ _ X0 (Ext_trans _ _ _ X12 X3))|exact R3]].
  - apply (lookup_spec S h K cK H H0 i v S' H1).
  - destruct (HNorm.pnorm F p K S) as [P S1] eqn:E1.
    destruct (H K S cK P S1 H0 H1 E1) as [I1 [X1 R1]].
    destruct (HNorm.clean (fpb p) P S1) as [P' S2] eqn:E2.
    destruct (clean_spec S1 (fpb p) P _ P' S2 I1 R1 E2) as [I2 [X2 R2]].
    injection H2 as <- <-; split; [exact I2|split; [apply (Ext_trans _ _ _ X1 X2)|constructor; apply RWord_RId, R2]].
  - rewrite is_bind_same in H2; destruct (CNorm.is_bind t); [apply (H K S cK v S' H0 H1 H2)|].
    destruct (HNorm.pushW F h K S) as [K1 S1] eqn:E1.
    destruct (pushW_spec S h K cK K1 S1 H0 H1 E1) as [I1 [X1 R1]].
    destruct (H K1 S1 _ v S' I1 R1 H2) as [I2 [X2 R2]].
    split; [exact I2|split; [apply (Ext_trans _ _ _ X1 X2)|exact R2]].
  - injection H1 as <- <-; split; [exact H|split; [apply Ext_refl|exact H0]].
  - injection H1 as <- <-; split; [exact H|split; [apply Ext_refl|exact H0]].
  - destruct (HNorm.norm F a K S) as [K1 S1] eqn:E1.
    destruct (H K S cK K1 S1 H1 H2 E1) as [I1 [X1 R1]].
    destruct (H0 K1 S1 _ w' S' I1 R1 H3) as [I2 [X2 R2]].
    split; [exact I2|split; [apply (Ext_trans _ _ _ X1 X2)|exact R2]].
  - destruct (HNorm.pushW F h K S) as [K1 S1] eqn:E1.
    destruct (pushW_spec S h K cK K1 S1 H0 H1 E1) as [I1 [X1 R1]].
    destruct (H K1 S1 _ w' S' I1 R1 H2) as [I2 [X2 R2]].
    split; [exact I2|split; [apply (Ext_trans _ _ _ X1 X2)|exact R2]].
Qed.

(** The shared decision is the unshared one. *)
Theorem hn_eq_cn e1 e2 : HNorm.hn_eq F e1 e2 = CNorm.cn_eq F e1 e2.
Proof.
  unfold HNorm.hn_eq.
  destruct (HNorm.norm F e1 [] HNorm.st0) as [w1 S1] eqn:E1.
  destruct (proj1 norm_spec_all e1 [] HNorm.st0 [] w1 S1 Inv_st0 (RWNil _) E1) as [I1 [_ R1]].
  destruct (HNorm.norm F e2 [] S1) as [w2 S2] eqn:E2.
  destruct (proj1 norm_spec_all e2 [] S1 [] w2 S2 I1 (RWNil _) E2) as [I2 [X2 R2]].
  apply (RWord_mono _ _ X2) in R1.
  apply eq_iff_eq_true; rewrite Pos.eqb_eq, CNorm.cn_eq_iff; split.
  - intros Ew; apply (proj1 (R_func S2 I2) _ _ (RWord_RId _ _ _ R1)); rewrite Ew; apply RWord_RId, R2.
  - intros Ec; rewrite Ec in R1; apply (proj1 (R_inj S2 I2) _ _ (RWord_RId _ _ _ R1)), RWord_RId, R2.
Qed.

End Refine.

(** [hn_eq] decides equality in comprehension models, when the facts
    form a strict order. *)
Theorem hn_eq_correct F :
  (forall a, lt_known F a a = false) ->
  (forall a b c, lt_known F a b = true -> lt_known F b c = true -> lt_known F a c = true) ->
  forall e1 e2, HNorm.hn_eq F e1 e2 = true <-> cequal F e1 e2.
Proof. intros Hirr Htrans e1 e2; rewrite (hn_eq_cn F Hirr Htrans); apply cn_eq_correct; assumption. Qed.

