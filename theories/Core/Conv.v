(** * Nested substitutions and variables, converted before normalising

    [names] turns, in an adjustment it substitutes with, a term that is a
    substitution [u [c]] into the term [u] with [c] in its payload, and a
    term that is a variable [w] into a look-up of [w] through the term's
    payload, before normalising: the normaliser then works on the
    payloads.  After normalising it turns payloads [u⟨c⟩] back into
    substitutions [u [c]].

    The terms form a family [term : nat -> Type] (a term of [term K] has
    the variables of scope [K]), with variables [tv] and substitution
    [sub]; the raw results hold terms of any scope, [{K & term K}].  The
    laws a syntax gives for this are about results related in these ways
    ([lawbase]), also inside payloads and in steps ([drel]):
    - [matbase]: [u] with the payload [c] against [u [c]] with the
      identity payload;
    - [nbase]: [u [c]] with a payload [W] against [u] with [W ∘ c];
    - [vbase]: the variable [w] with a payload [W] against where [W]
      sends [w].
    Here: the conversion of reified adjustments ([aconv]), and that it
    gives an adjustment whose results are related to the original's
    ([conv_sound]). *)

From Stdlib Require Import List Arith Lia NArith.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Scoped Indexed Normalise HShow Braun HShowB.
Import ListNotations.

Section Bases.

Context {term : nat -> Type}.
Variable tv : forall K, var K -> term K.
Variable sub : forall K M, adj term K M -> term K -> term M.

Local Notation P := {K & term K}.

Definition matbase (r r' : rresult P) : Prop :=
  exists K M (u : term K) (c : adj term K M),
    r = inr (existT term K u, adj_raw c) /\ r' = inr (existT term M (sub K M c u), ridentity).

Definition nbase (r r' : rresult P) : Prop :=
  exists K M (u : term K) (c : adj term K M) W,
    r = inr (existT term M (sub K M c u), W) /\ r' = inr (existT term K u, rcompose W (adj_raw c)).

Definition vbase (r r' : rresult P) : Prop :=
  exists K (w : var K) (W : radj P), r = inr (existT term K (tv K w), W) /\ r' = rapply W (var_raw w).

Definition lawbase (r r' : rresult P) : Prop := matbase r r' \/ nbase r r' \/ vbase r r'.

(** ** Composing after related results *)

Definition rcomp (A : radj P) (r : rresult P) : rresult P :=
  match r with inl w => rapply A w | inr (u, ρ) => inr (u, rcompose A ρ) end.

Lemma rcomp_rapply A B v : rcomp A (rapply B v) = rapply (rcompose A B) v.
Proof. rewrite rapply_compose; reflexivity. Qed.

Lemma rlift_rcomp h A v : rapply (rlift h A) v
  = if rvar_eqb v (mk_rvar h 0) then inl v else rcomp (rshift h) (rapply A (unshift_rvar (mk_rvar h 0) v)).
Proof.
  rewrite rapply_lift; destruct (rvar_eqb v _); [reflexivity|].
  destruct (rapply A _) as [w|[u ρ]]; cbn [rcomp]; [rewrite rapply_shift|rewrite rpush_outer_as_compose]; reflexivity.
Qed.

Lemma drel_rcomp (B : rresult P -> rresult P -> Prop) :
  (forall A r r', B r r' -> B (rcomp A r) (rcomp A r')) ->
  forall r r', drel B r r' -> forall A, drel B (rcomp A r) (rcomp A r').
Proof.
  intros HB r r' H; induction H as [r|r r' Hb|u W W' ρ _ IH|r r' r'' _ IH1 _ IH2]; intros A.
  - apply DEq.
  - apply DBase, HB, Hb.
  - cbn [rcomp]; rewrite !rcompose_assoc; apply DPay; intros v.
    rewrite <- !rcomp_rapply; apply IH.
  - eapply DTrans; [apply IH1|apply IH2].
Qed.

Lemma drel_rcomp_l (B : rresult P -> rresult P -> Prop) A A' r :
  (forall v, drel B (rapply A v) (rapply A' v)) -> drel B (rcomp A r) (rcomp A' r).
Proof. intros H; destruct r as [w|[u ρ]]; [apply H|apply DPay, H]. Qed.

Lemma drel_rcomp2 (B : rresult P -> rresult P -> Prop) :
  (forall A r r', B r r' -> B (rcomp A r) (rcomp A r')) ->
  forall A A' r r', (forall v, drel B (rapply A v) (rapply A' v)) -> drel B r r' -> drel B (rcomp A r) (rcomp A' r').
Proof. intros HB A A' r r' HA H; eapply DTrans; [apply (drel_rcomp B HB _ _ H)|apply drel_rcomp_l, HA]. Qed.

(** The bases [names] converts with are kept by composing after. *)
Definition cbase (r r' : rresult P) : Prop := nbase r r' \/ vbase r r'.

Lemma cbase_rcomp A r r' : cbase r r' -> cbase (rcomp A r) (rcomp A r').
Proof.
  intros [[K [M [u [c [W [-> ->]]]]]]|[K [w [W [-> ->]]]]]; cbn [rcomp].
  - left; exists K, M, u, c, (rcompose A W); rewrite <- rcompose_assoc; split; reflexivity.
  - right; exists K, w, (rcompose A W); rewrite rcomp_rapply; split; reflexivity.
Qed.

Lemma cbase_lawbase r r' : cbase r r' -> lawbase r r'.
Proof. intros [H|H]; [right; left|right; right]; exact H. Qed.

End Bases.

(** ** The conversion *)

Fixpoint nlook {X} (k : N) (l : list (N * X)) : option X :=
  match l with [] => None | (k', x) :: l' => if N.eqb k' k then Some x else nlook k l' end.

Lemma nlook_in {X} k (l : list (N * X)) x : nlook k l = Some x -> In (k, x) l.
Proof.
  induction l as [|[k' y] l IH]; cbn; [discriminate|].
  destruct (N.eqb_spec k' k) as [->|]; [intros E; injection E as ->; left; reflexivity|intros E; right; apply IH, E].
Qed.

Section Conv.

(** [nf]: terms [k] that are [u_k' [c]], with [c] reified as [C]; [vf]:
    terms [k] that are the variable [hᵢ]. *)
Variable nf : list (N * (N * aexpN)).
Variable vf : list (N * (lexp * N)).

(** [cC]: the conversion of the nested payloads [C]. *)
Variable cC : aexpN -> aexpN.

Definition tbind (u : N) (p : aexpN) : texpN :=
  match nlook u vf with Some (h, i) => NLookE h i p | None => NBindE u p end.

Fixpoint aconv (e : aexpN) : aexpN :=
  match e with
  | NId => NId
  | NAtom n => NAtom n
  | NCompose a b => NCompose (aconv a) (aconv b)
  | NOuter h a => NOuter h (aconv a)
  | NInner h t a => NInner h (tconv t) (aconv a)
  | NLift h a => NLift h (aconv a)
  end
with tconv (t : texpN) : texpN :=
  match t with
  | NVarE h i => NVarE h i
  | NBindE u p =>
      let p' := aconv p in
      match nlook u nf with
      | Some (u', C) => tbind u' (NCompose p' (cC C))
      | None => tbind u p'
      end
  | NShiftE h t => NShiftE h t
  | NLookE h i a => NLookE h i (aconv a)
  end.

Context {term : nat -> Type}.
Variable tv : forall K, var K -> term K.
Variable sub : forall K M, adj term K M -> term K -> term M.
Local Notation P := {K & term K}.
Variables (Le : braun label) (Te : braun P) (Ae : braun (radj P)).

Local Notation den := (aedenB Le Te Ae).
Local Notation tden := (tedenB Le Te Ae).

Hypothesis Hnf : Forall (fun '(k, (k', C)) => exists K M (c : adj term K M) (u : term K),
                          adj_raw c = den C /\ bnth Te k' = Some (existT term K u)
                          /\ bnth Te k = Some (existT term M (sub K M c u))) nf.
Hypothesis Hvf : Forall (fun '(k, (h, i)) => exists K (w : var K),
                          bnth Te k = Some (existT term K (tv K w)) /\ var_raw w = mk_rvar (ldenB Le h) (N.to_nat i)) vf.

Local Notation B := (cbase tv sub).


Lemma tres_bind u p : rtarget_result (tden (NBindE u p))
  = match bnth Te u with Some x => inr (x, den p) | None => inl (mk_rvar None 0) end.
Proof. cbn [tedenB]; destruct (bnth Te u); reflexivity. Qed.

Lemma tres_look h i a : rtarget_result (tden (NLookE h i a)) = rapply (den a) (mk_rvar (ldenB Le h) (N.to_nat i)).
Proof.
  change (tden (NLookE h i a)) with (rapply_target (den a) (RRename (mk_rvar (ldenB Le h) (N.to_nat i)))).
  unfold rapply_target; destruct (rapply _ _) as [w|[u ρ]]; reflexivity.
Qed.

Hypothesis HcC : forall C v, drel B (rapply (den C) v) (rapply (den (cC C)) v).

(** A term [u] with the payload [p], against [tbind u p]. *)
Lemma tbind_sound u p : drel B (rtarget_result (tden (NBindE u p))) (rtarget_result (tden (tbind u p))).
Proof.
  unfold tbind; destruct (nlook u vf) as [[h i]|] eqn:Ev; [|apply DEq].
  pose proof (nlook_in _ _ _ Ev) as Hin; rewrite Forall_forall in Hvf.
  destruct (Hvf _ Hin) as [K [w [Ew Hw]]].
  rewrite tres_bind, Ew; apply DBase; right.
  exists K, w, (den p); split; [reflexivity|].
  rewrite tres_look, Hw; reflexivity.
Qed.

Theorem conv_sound :
  (forall e v, drel B (rapply (den e) v) (rapply (den (aconv e)) v))
  /\ (forall t, drel B (rtarget_result (tden t)) (rtarget_result (tden (tconv t)))).
Proof.
  pose proof (cbase_rcomp tv sub) as HB.
  apply expN_mind.
  - intros v; apply DEq.
  - intros n v; apply DEq.
  - intros a IHa b IHb v; cbn [aconv aedenB]; rewrite <- !rcomp_rapply; apply drel_rcomp2; [exact HB|exact IHa|apply IHb].
  - intros h a IH v; cbn [aconv aedenB]; rewrite !rpush_outer_as_compose, <- !rcomp_rapply.
    apply (drel_rcomp B HB), IH.
  - intros h t IHt a IHa v; cbn [aconv aedenB]; rewrite !rapply_push_inner.
    destruct (rvar_eqb v _); [apply IHt|apply IHa].
  - intros h a IH v; cbn [aconv aedenB]; rewrite !rlift_rcomp.
    destruct (rvar_eqb v _); [apply DEq|apply (drel_rcomp B HB), IH].
  - intros h i; apply DEq.
  - intros u p IH; cbn [tconv].
    (* the payload converted first *)
    assert (Hp : forall x, drel B (inr (x, den p)) (inr (x, den (aconv p)))).
    { intros x; rewrite <- (rcompose_identity_r (den p)), <- (rcompose_identity_r (den (aconv p))).
      apply DPay, IH. }
    destruct (nlook u nf) as [[u' C]|] eqn:En; (eapply DTrans; [|apply tbind_sound]).
    + pose proof (nlook_in _ _ _ En) as Hin; rewrite Forall_forall in Hnf.
      destruct (Hnf _ Hin) as [K [M [c [x' [Ec [Ex' Ex]]]]]].
      rewrite !tres_bind, Ex, Ex'; eapply DTrans; [apply Hp|].
      eapply DTrans; [apply DBase; left; exists K, M, x', c, (den (aconv p)); split; reflexivity|].
      cbn [aedenB]; rewrite Ec, <- (rcompose_identity_r (rcompose _ (den C))), <- (rcompose_identity_r (rcompose _ (den (cC C)))).
      apply DPay; intros v; rewrite <- !rcomp_rapply.
      apply (drel_rcomp B (cbase_rcomp tv sub)), HcC.
    + rewrite !tres_bind; destruct (bnth Te u); [apply Hp|apply DEq].
  - intros h t _; apply DEq.
  - intros h i a IH; cbn [tconv]; rewrite !tres_look; apply IH.
Qed.

End Conv.

(** Conversion to depth [f]: the nested payloads converted to depth
    [f - 1]. *)
Fixpoint aconvn (nf : list (N * (N * aexpN))) (vf : list (N * (lexp * N))) (f : nat) : aexpN -> aexpN :=
  match f with
  | O => aconv nf vf (fun C => C)
  | S f => aconv nf vf (aconvn nf vf f)
  end.

Theorem aconvn_sound nf vf {term} (tv : forall K, var K -> term K) (sub : forall K M, adj term K M -> term K -> term M)
    Le Te Ae :
  Forall (fun '(k, (k', C)) => exists K M (c : adj term K M) (u : term K),
            adj_raw c = aedenB Le Te Ae C /\ bnth Te k' = Some (existT term K u)
            /\ bnth Te k = Some (existT term M (sub K M c u))) nf ->
  Forall (fun '(k, (h, i)) => exists K (w : var K),
            bnth Te k = Some (existT term K (tv K w)) /\ var_raw w = mk_rvar (ldenB Le h) (N.to_nat i)) vf ->
  forall f e v, drel (cbase tv sub) (rapply (aedenB Le Te Ae e) v) (rapply (aedenB Le Te Ae (aconvn nf vf f e)) v).
Proof.
  intros Hn Hv f; induction f as [|f IH]; cbn [aconvn].
  - apply (conv_sound nf vf (fun C => C) tv sub Le Te Ae Hn Hv (fun C v => DEq _ _)).
  - apply (conv_sound nf vf (aconvn nf vf f) tv sub Le Te Ae Hn Hv IH).
Qed.
