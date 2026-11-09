(** * Deep well-formedness

    An adjustment is deeply well formed when it is in normal form at every
    level: its payloads, made absolute, are named-only normal forms, and so
    on down.  This is decided by a structural check [nwfc], so that a proof
    of it can be kept in SProp and still be used; [nwf] is that check
    succeeding, and the lemmas below give its meaning: the one-level normal
    form, finitely many labels moved, and every payload result deeply well
    formed in turn. *)

From Stdlib Require Import PArith Arith Lia List Bool.
From ShiftedNames.Core Require Import Trie Label Var Counts Based Skew ATrie Repr Point.
Import ListNotations.

(** ** Checking every element, with its base *)

Section Folds.

Context {X : Type} {BX : Based X} {LX : BasedLaws X}.

Variable F : counts -> X -> bool.

Fixpoint ktallF (B : counts) (t : ktree X) : bool :=
  match t with
  | KLeaf x => F B x
  | KNode a x l r => let P := cadd B a in F P x && ktallF P l && ktallF P r
  end.

Fixpoint kallF (B : counts) (s : kseq X) : bool :=
  match s with
  | KNil => true
  | KCons a _ t s' => let P := cadd B a in ktallF P t && kallF P s'
  end.

Fixpoint aallF (B : counts) (t : atrie X) : bool :=
  match t with
  | AEmpty => true
  | ANode a l o r =>
      let P := cadd B a in
      match o with Some x => F P x | None => true end && aallF P l && aallF P r
  end.

(** [F] looks at an element stored relative to a base; [G] at it made
    absolute. *)
Variable G : X -> bool.
Hypothesis HF : forall B x, F B x = G (unshift B x).

Lemma allF_node B a (L : list X) :
  (forall k, cget a k = lmin (map (unshift a) L) k) ->
  (forall y, In y L -> G (unshift (cadd B a) y) = true)
  <-> (forall z, In z (map (unshift a) L) -> G (unshift B z) = true).
Proof.
  intros Ha; split.
  - intros H z Hz; apply in_map_iff in Hz as [y [<- Hy]]; rewrite (unshift_cadd B a L y Ha Hy); apply H, Hy.
  - intros H y Hy; rewrite <- (unshift_cadd B a L y Ha Hy); apply H, in_map, Hy.
Qed.

Lemma ktallF_spec t : forall B,
  ktinv t -> ktallF B t = true <-> forall y, In y (ktlist t) -> G (unshift B y) = true.
Proof.
  induction t as [x|a x l IHl r IHr]; intros B Ht; cbn [ktallF ktlist].
  - rewrite HF; split; [intros H y [<-|[]]; exact H|intros H; apply H; left; reflexivity].
  - destruct Ht as [Ha [_ [_ [Hl Hr]]]]; cbn [ktann ktlist] in Ha.
    rewrite <- (allF_node B a _ Ha), !andb_true_iff, HF, IHl, IHr by assumption.
    split.
    + intros [[Hx Hl'] Hr'] y [<-|Hy]; [exact Hx|apply in_app_or in Hy as [Hy|Hy]; auto].
    + intros H; split; [split; [apply H; left; reflexivity|]|]; intros y Hy; apply H; right; apply in_or_app; auto.
Qed.

Lemma kallF_spec s : forall B,
  kinv s -> kallF B s = true <-> forall y, In y (klist s) -> G (unshift B y) = true.
Proof.
  induction s as [|a w t s IH]; intros B Hs; cbn [kallF klist].
  - split; [intros _ y []|reflexivity].
  - destruct Hs as [Ha [_ [Ht Hs]]]; cbn [ksann klist] in Ha.
    rewrite <- (allF_node B a _ Ha), andb_true_iff, ktallF_spec, IH by assumption.
    split; [intros [H1 H2] y Hy; apply in_app_or in Hy as [Hy|Hy]; auto|].
    intros H; split; intros y Hy; apply H, in_or_app; auto.
Qed.

Lemma aallF_spec t : forall B,
  ainv t -> aallF B t = true <-> forall y, In y (aelems t) -> G (unshift B y) = true.
Proof.
  induction t as [|a l IHl o r IHr]; intros B Ht; cbn [aallF aelems].
  - split; [intros _ y []|reflexivity].
  - destruct Ht as [Ha [_ [_ [_ [Hl Hr]]]]]; cbn [aelems] in Ha.
    rewrite <- (allF_node B a _ Ha), !andb_true_iff, IHl, IHr by assumption.
    assert (Ho : (match o with Some x => F (cadd B a) x | None => true end) = true
                 <-> forall y, In y (oelems o) -> G (unshift (cadd B a) y) = true)
      by (destruct o as [x|]; cbn; [rewrite HF; split; [intros H y [<-|[]]; exact H|intros H; apply H; left; reflexivity]
                                   |split; [intros _ y []|reflexivity]]).
    rewrite Ho; split.
    + intros [[Ho' Hl'] Hr'] y Hy; apply in_app_or in Hy as [Hy|Hy]; [auto|apply in_app_or in Hy as [Hy|Hy]; auto].
    + intros H; split; [split|]; intros y Hy; apply H; apply in_or_app; [right; apply in_or_app; left
                                                                      |left|right; apply in_or_app; right]; exact Hy.
Qed.

End Folds.

Section Deep.

Context {T : Type}.

Local Notation nadj := (@nadj T).
Local Notation result := (@result T).
Local Notation entry := (@entry T).
Local Notation target := (@target T).

(** ** Nesting depth, for induction through payloads *)

Fixpoint ktmax {X} (f : X -> nat) (t : ktree X) : nat :=
  match t with KLeaf x => f x | KNode _ x l r => Nat.max (f x) (Nat.max (ktmax f l) (ktmax f r)) end.

Fixpoint kmaxs {X} (f : X -> nat) (s : kseq X) : nat :=
  match s with KNil => 0 | KCons _ _ t s' => Nat.max (ktmax f t) (kmaxs f s') end.

Fixpoint amax {X} (f : X -> nat) (t : atrie X) : nat :=
  match t with
  | AEmpty => 0
  | ANode _ l o r => Nat.max (amax f l) (Nat.max (match o with Some x => f x | None => 0 end) (amax f r))
  end.

Fixpoint tnest (t : target) : nat :=
  match t with TVar _ _ => 0 | TBind _ rho => S (nnest rho) end
with nnest (b : nadj) : nat :=
  match b with NAdj _ es => amax (fun e => match e with Entry _ ts _ _ => kmaxs tnest ts end) es end.

Definition enest (e : entry) : nat := match e with Entry _ ts _ _ => kmaxs tnest ts end.

Section Depth.

Context {X : Type} {BX : Based X}.
Variable f : X -> nat.
Hypothesis Hf : forall d x, f (unshift d x) = f x.

Lemma ktmax_in t : forall x, In x (ktlist t) -> f x <= ktmax f t.
Proof.
  induction t as [y|c y l IHl r IHr]; cbn [ktlist ktmax]; [intros x [<-|[]]; lia|].
  intros x Hin; apply in_map_iff in Hin as [x0 [<- Hin]]; rewrite Hf.
  destruct Hin as [<-|Hin]; [lia|apply in_app_or in Hin as [Hin|Hin]; [specialize (IHl _ Hin)|specialize (IHr _ Hin)]; lia].
Qed.

Lemma kmaxs_in s : forall x, In x (klist s) -> f x <= kmaxs f s.
Proof.
  induction s as [|c w t s IH]; cbn [klist kmaxs]; [intros x []|].
  intros x Hin; apply in_map_iff in Hin as [x0 [<- Hin]]; rewrite Hf.
  apply in_app_or in Hin as [Hin|Hin]; [pose proof (ktmax_in t x0 Hin)|specialize (IH _ Hin)]; lia.
Qed.

Lemma amax_in t : forall x, In x (aelems t) -> f x <= amax f t.
Proof.
  induction t as [|c l IHl o r IHr]; cbn [aelems amax]; [intros x []|].
  intros x Hin; apply in_map_iff in Hin as [x0 [<- Hin]]; rewrite Hf.
  apply in_app_or in Hin as [Hin|Hin]; [specialize (IHl _ Hin); lia|].
  apply in_app_or in Hin as [Hin|Hin]; [destruct o as [y|]; [destruct Hin as [<-|[]]; lia|destruct Hin]|].
  specialize (IHr _ Hin); lia.
Qed.

End Depth.

Lemma tnest_unshift d (t : target) : tnest (unshift d t) = tnest t.
Proof. destruct t as [y j|u [r es]]; reflexivity. Qed.

Lemma kmaxs_klift d (ts : kseq target) : kmaxs tnest (klift d ts) = kmaxs tnest ts.
Proof. destruct ts; reflexivity. Qed.

Lemma enest_unshift d (e : entry) : enest (unshift d e) = enest e.
Proof. destruct e as [h ts len p]; cbn; apply kmaxs_klift. Qed.

Lemma nnest_es r (es : atrie entry) : nnest (NAdj r es) = amax enest es.
Proof. reflexivity. Qed.

Theorem nest_napply (b : nadj) v u rho :
  (forall k e, aget k (nentries b) = Some e -> kgood (etargets e)) ->
  napply b v = inr (u, rho) -> nnest rho < nnest b.
Proof.
  destruct b as [w es]; intros HG; cbn [napply nentries] in *; rewrite nnest_es.
  destruct (aget _ es) as [e|] eqn:E; [|discriminate].
  pose proof (amax_in enest enest_unshift es e (aget_in _ _ _ E)) as He.
  pose proof (HG _ _ E) as G.
  destruct e as [h ts len p]; cbn [eapply enest etargets] in *.
  destruct (Nat.ltb _ _); [|discriminate].
  destruct (knth ts _) as [t|] eqn:Et; [|discriminate].
  pose proof (kmaxs_in tnest tnest_unshift ts t (knth_in _ _ _ G Et)) as Ht.
  destruct t as [y j|u' [r es']]; cbn in *; [discriminate|]; intros [= -> <-]; cbn in Ht; rewrite !nnest_es in *; change (S (amax enest es') <= kmaxs tnest ts) in Ht; lia.
Qed.


Lemma target_result Q r (es : atrie entry) k h ts len p i t :
  nlocal Q (NAdj r es) -> aget k es = Some (Entry h ts len p) -> knth ts i = Some t ->
  napply (NAdj r es) (mk_rvar h i) = tresult (tunshift r t) /\ Q h = true.
Proof.
  intros Hl E Et; pose proof Hl as [_ [_ [_ [Hent _]]]].
  destruct (Hent _ _ E) as [[Hk [G [Hlen _]]] [HQ _]]; cbn [elabel] in HQ.
  split; [|exact HQ].
  cbn [napply v_label v_index]; rewrite Hk, E; cbn [eapply].
  assert (Hi : i < len)
    by (rewrite <- Hlen, (klength_spec _ (kgood_shape _ G)); apply nth_error_Some;
        rewrite <- knth_spec by apply (kgood_shape _ G); rewrite Et; discriminate).
  destruct (Nat.ltb_spec i len); [rewrite Et; reflexivity|lia].
Qed.


(** ** The check *)

(** [nwfc pay rt b] checks [b] with its root counts read through [rt]: the
    identity at the top, adding the base for a payload. *)
Fixpoint nwfc (pay : bool) (rt : counts -> counts) (b : nadj) {struct b} : bool :=
  match b with
  | NAdj r es =>
      let R := rt r in
      nlocalb pay (NAdj R es) && oeqb (c_def R) (Some 0)
      && aallF (fun B e =>
                  match e with
                  | Entry _ ts _ _ =>
                      kallF (fun B' t => match t with
                                         | TVar _ _ => true
                                         | TBind _ rho => nwfc true (cadd B') rho
                                         end) B ts
                  end) R es
  end.

(** Deeply well formed: [pay] says it is a payload's adjustment. *)
Definition nwf (pay : bool) (b : nadj) : Prop := nwfc pay (fun r => r) b = true.

Definition tcheck (B : counts) (t : target) : bool :=
  match t with TVar _ _ => true | TBind _ rho => nwfc true (cadd B) rho end.

Definition echeck (B : counts) (e : entry) : bool :=
  match e with Entry _ ts _ _ => kallF tcheck B ts end.

Lemma nwfc_eq pay rt r es :
  nwfc pay rt (NAdj r es)
  = nlocalb pay (NAdj (rt r) es) && oeqb (c_def (rt r)) (Some 0) && aallF echeck (rt r) es.
Proof. reflexivity. Qed.

Lemma tcheck_unshift B t : tcheck B t = tcheck cnone (unshift B t).
Proof.
  destruct t as [y j|u [r es]]; [reflexivity|]; cbn [tcheck unshift target_based tunshift].
  rewrite !nwfc_eq, (cadd_cnone (cadd B r)) by apply cwf_cmap2; reflexivity.
Qed.

Lemma echeck_unshift B e : echeck B e = echeck cnone (unshift B e).
Proof.
  destruct e as [h [|a w t s] len p]; [reflexivity|]; cbn [echeck unshift entry_based eunshift klift kallF].
  rewrite (cadd_cnone (cadd B a)) by apply cwf_cmap2; reflexivity.
Qed.

Lemma tcheck_payload u r es : cwf r -> tcheck cnone (TBind u (NAdj r es)) = true <-> nwf true (NAdj r es).
Proof. intros Cr; cbn [tcheck]; unfold nwf; rewrite !nwfc_eq, cadd_cnone by exact Cr; reflexivity. Qed.

(** ** What [nwf] means *)

Lemma nwf_local pay b : nwf pay b -> nlocal (Qof pay) b.
Proof.
  destruct b as [r es]; unfold nwf; rewrite nwfc_eq; cbv beta; intros H.
  apply andb_prop in H as [H _]; apply andb_prop in H as [H _]; apply nlocalb_spec, H.
Qed.

Lemma nwf_fin pay b : nwf pay b -> nfin b.
Proof.
  destruct b as [r es]; unfold nwf; rewrite nwfc_eq; cbv beta; intros H.
  apply andb_prop in H as [H _]; apply andb_prop in H as [_ H]; apply oeqb_spec, H.
Qed.

(** The payload checks, as a statement about the entries made absolute. *)
Lemma nwf_targets pay r (es : atrie entry) :
  nlocal (Qof pay) (NAdj r es) ->
  aallF echeck r es = true
  <-> forall k e, aget k es = Some e ->
      forall t, In t (klist (klift r (etargets e))) -> tcheck cnone t = true.
Proof.
  intros Hl; pose proof Hl as [Hes _].
  rewrite (aallF_spec echeck (echeck cnone) (fun B x => echeck_unshift B x) es r Hes).
  assert (Hent : forall e, In e (aelems es) ->
                 (echeck cnone (unshift r e) = true
                  <-> forall t, In t (klist (klift r (etargets e))) -> tcheck cnone t = true)).
  { intros e He; destruct (aelems_aget es e He) as [k E].
    pose proof Hl as [_ [_ [_ [Hent _]]]]; destruct (Hent k e E) as [Hok _].
    destruct e as [h ts len p]; destruct Hok as [_ [G _]].
    cbn [unshift entry_based eunshift echeck etargets].
    rewrite (kallF_spec tcheck (tcheck cnone) (fun B x => tcheck_unshift B x) _ cnone (kinv_klift r ts (kgood_inv _ G))).
    split; intros H t Ht; specialize (H t Ht).
    - rewrite tcheck_unshift; exact H.
    - rewrite <- tcheck_unshift; exact H. }
  split.
  - intros H k e E; apply Hent; [apply (aget_in _ _ _ E)|apply H, (aget_in _ _ _ E)].
  - intros H e He; apply Hent; [exact He|]; destruct (aelems_aget es e He) as [k E]; apply (H k e E).
Qed.

Lemma nwf_payload pay b v u rho :
  nwf pay b -> Qof pay (v_label v) = true -> napply b v = inr (u, rho) -> nwf true rho.
Proof.
  intros Hw _ E; pose proof (nwf_local pay b Hw) as Hl.
  destruct b as [r es]; unfold nwf in Hw; rewrite nwfc_eq in Hw; cbv beta in Hw; apply andb_prop in Hw as [_ Hw].
  pose proof (proj1 (nwf_targets pay r es Hl) Hw) as Hw2; clear Hw; rename Hw2 into Hw.
  cbn [napply] in E; destruct (aget _ es) as [e|] eqn:Ek; [|discriminate].
  pose proof Hl as [_ [_ [_ [Hent _]]]]; destruct (Hent _ e Ek) as [Hok _].
  destruct e as [h ts len p]; destruct Hok as [_ [G _]]; cbn [eapply] in E.
  destruct (Nat.ltb _ _); [|discriminate].
  destruct (knth ts _) as [t0|] eqn:Et; [|discriminate].
  destruct (tunshift r t0) as [y j|u' [r' es']] eqn:Eu; cbn [tresult] in E; [discriminate|injection E as -> <-].
  apply (tcheck_payload u); [|rewrite <- Eu; apply (Hw _ _ Ek); cbn [etargets];
                               rewrite klist_klift by apply kgood_inv, G; apply in_map, (knth_in _ _ _ G Et)].
  destruct t0 as [y j|u0 [r0 es0]]; cbn in Eu; [discriminate|injection Eu as _ <- _; apply cwf_cmap2].
Qed.

Lemma nwf_intro pay b :
  nlocal (Qof pay) b -> nfin b ->
  (forall v u rho, Qof pay (v_label v) = true -> napply b v = inr (u, rho) -> nwf true rho) ->
  nwf pay b.
Proof.
  intros Hl Hf Hp; destruct b as [r es]; unfold nwf; rewrite nwfc_eq; cbv beta.
  unfold nfin in Hf; cbn [nroot] in Hf; rewrite (proj2 (nlocalb_spec pay _) Hl), (proj2 (oeqb_spec _ _) Hf); cbn [andb].
  apply (nwf_targets pay r es Hl); intros k e E t Ht.
  pose proof Hl as [_ [_ [_ [Hent _]]]]; destruct (Hent k e E) as [Hok [HQ _]].
  destruct e as [h ts len p]; destruct Hok as [_ [G _]]; cbn [etargets elabel] in *.
  rewrite klist_klift in Ht by apply kgood_inv, G; apply in_map_iff in Ht as [t0 [<- Ht0]].
  destruct (In_nth_error _ _ Ht0) as [i Ei].
  assert (Et : knth ts i = Some t0) by (rewrite knth_spec by apply kgood_shape, G; exact Ei).
  destruct (target_result _ r es k h ts len p i t0 Hl E Et) as [Hn _].
  destruct t0 as [y j|u0 [r0 es0]]; [reflexivity|]; cbn [tunshift tresult] in Hn |- *.
  apply (tcheck_payload u0); [apply cwf_cmap2|apply (Hp (mk_rvar h i) u0 _ HQ Hn)].
Qed.

End Deep.
