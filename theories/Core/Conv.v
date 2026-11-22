(** * Nested substitutions and variables, converted before normalising

    [names] turns, in an adjustment it substitutes with, a term that is a
    substitution [u [c]] into the closed scope into the term [u] with [c]
    in its payload, and a term that is a variable [w] into a look-up of
    [w] through the term's payload, before normalising: the normaliser
    then works on the payloads.  After normalising it turns closed
    payloads [u⟨c ∘ id⟩] back into substitutions [u [c]].

    The laws a syntax gives for this are about results related in these
    ways ([lawbase]), also inside payloads and in steps ([drel]):
    - [matbase]: [u] with the payload [c ∘ id] against [u [c]];
    - [nbase]: [u [c]] with a payload [W ∘ id] against [u] with
      [W ∘ (c ∘ id)];
    - [vbase]: the variable [w] with a payload [W ∘ id] against where [W]
      sends [w].
    Here: the conversion of reified adjustments ([aconv]), and that it
    gives an adjustment whose results are related to the original's
    ([conv_sound]). *)

From Stdlib Require Import List Arith Lia NArith.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Scoped Indexed Normalise HShow Braun HShowB.
Import ListNotations.

Section Bases.

Context {T : Type}.
Variable var0 : var 0 -> T.
Variable g : rpadj T -> T -> T.

Definition matbase (r r' : rresult T) : Prop :=
  exists u (c : adj T 0 0), r = inr (u, rpcompose (adj_raw c) rpidentity)
    /\ r' = inr (g (rpcompose (adj_raw c) rpidentity) u, rpidentity).

Definition nbase (r r' : rresult T) : Prop :=
  exists u (c : adj T 0 0) W, r = inr (g (rpcompose (adj_raw c) rpidentity) u, rpcompose W rpidentity)
    /\ r' = inr (u, rpcompose W (rpcompose (adj_raw c) rpidentity)).

Definition vbase (r r' : rresult T) : Prop :=
  exists (w : var 0) (W : radj T), r = inr (var0 w, rpcompose W rpidentity) /\ r' = rapply W (var_raw w).

Definition lawbase (r r' : rresult T) : Prop := matbase r r' \/ nbase r r' \/ vbase r r'.

(** ** Composing after related results *)

Definition rcomp (A : radj T) (r : rresult T) : rresult T :=
  match r with inl w => rapply A w | inr (u, ρ) => inr (u, rpcompose A ρ) end.

Lemma rcomp_rapply A B v : rcomp A (rapply B v) = rapply (rcompose A B) v.
Proof. rewrite rapply_compose; reflexivity. Qed.

Lemma rlift_rcomp h A v : rapply (rlift h A) v
  = if rvar_eqb v (mk_rvar h 0) then inl v else rcomp (rshift h) (rapply A (unshift_rvar (mk_rvar h 0) v)).
Proof.
  rewrite rapply_lift; destruct (rvar_eqb v _); [reflexivity|].
  destruct (rapply A _) as [w|[u ρ]]; cbn [rcomp]; [rewrite rapply_shift|rewrite rpshift_as_pcompose]; reflexivity.
Qed.

Lemma drel_rcomp (B : rresult T -> rresult T -> Prop) :
  (forall A r r', B r r' -> B (rcomp A r) (rcomp A r')) ->
  forall r r', drel B r r' -> forall A, drel B (rcomp A r) (rcomp A r').
Proof.
  intros HB r r' H; induction H as [r|r r' Hb|u W W' ρ _ IH|r r' r'' _ IH1 _ IH2]; intros A.
  - apply DEq.
  - apply DBase, HB, Hb.
  - cbn [rcomp]; rewrite !rpcompose_compose; apply DPay; intros v.
    rewrite <- !rcomp_rapply; apply IH.
  - eapply DTrans; [apply IH1|apply IH2].
Qed.

Lemma drel_rcomp_l (B : rresult T -> rresult T -> Prop) A A' r :
  (forall v, drel B (rapply A v) (rapply A' v)) -> drel B (rcomp A r) (rcomp A' r).
Proof. intros H; destruct r as [w|[u ρ]]; [apply H|apply DPay, H]. Qed.

Lemma drel_rcomp2 (B : rresult T -> rresult T -> Prop) :
  (forall A r r', B r r' -> B (rcomp A r) (rcomp A r')) ->
  forall A A' r r', (forall v, drel B (rapply A v) (rapply A' v)) -> drel B r r' -> drel B (rcomp A r) (rcomp A' r').
Proof. intros HB A A' r r' HA H; eapply DTrans; [apply (drel_rcomp B HB _ _ H)|apply drel_rcomp_l, HA]. Qed.

(** The bases [names] converts with are kept by composing after. *)
Definition cbase (r r' : rresult T) : Prop := nbase r r' \/ vbase r r'.

Lemma cbase_rcomp A r r' : cbase r r' -> cbase (rcomp A r) (rcomp A r').
Proof.
  intros [[u [c [W [-> ->]]]]|[w [W [-> ->]]]]; cbn [rcomp].
  - left; exists u, c, (rcompose A W); rewrite !rpcompose_compose; split; reflexivity.
  - right; exists w, (rcompose A W); rewrite rpcompose_compose, rcomp_rapply; split; reflexivity.
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

(** A payload [W ∘ id], as [W]. *)
Fixpoint pfun (p : pexpN) : option aexpN :=
  match p with
  | NPId => Some NId
  | NPAtom _ => None
  | NPComp a q => option_map (NCompose a) (pfun q)
  | NPShift h q => option_map (NOuter h) (pfun q)
  end.

Section Conv.

(** [nf]: terms [k] that are [u_k' [c]], with [c] reified as [C]; [vf]:
    terms [k] that are the variable [hᵢ]. *)
Variable nf : list (N * (N * aexpN)).
Variable vf : list (N * (lexp * N)).

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
      let p' := pconv p in
      match nlook u nf with
      | Some (u', C) => match pfun p' with Some A => NBindE u' (NPComp A (NPComp C NPId)) | None => NBindE u p' end
      | None =>
          match nlook u vf with
          | Some (h, i) => match pfun p' with Some A => NLookE h i A | None => NBindE u p' end
          | None => NBindE u p'
          end
      end
  | NShiftE h t => NShiftE h t
  | NLookE h i a => NLookE h i (aconv a)
  end
with pconv (p : pexpN) : pexpN :=
  match p with
  | NPId => NPId
  | NPAtom n => NPAtom n
  | NPComp a q => NPComp (aconv a) (pconv q)
  | NPShift h q => NPShift h (pconv q)
  end.

Context {T : Type}.
Variable var0 : var 0 -> T.
Variable g : rpadj T -> T -> T.
Variables (Le : braun label) (Te : braun T) (Ae : braun (radj T)) (Pe : braun (rpadj T)).

Local Notation den := (aedenB Le Te Ae Pe).
Local Notation tden := (tedenB Le Te Ae Pe).
Local Notation pden := (pedenB Le Te Ae Pe).

Lemma pfun_den p A : pfun p = Some A -> pden p = rpcompose (den A) rpidentity.
Proof.
  revert A; induction p as [|n|a q IH|h q IH]; cbn [pfun]; intros A E; try discriminate.
  - injection E as <-; cbn [aedenB pedenB]; symmetry; apply rpcompose_identity.
  - destruct (pfun q) as [A0|]; [|discriminate]; injection E as <-.
    cbn [aedenB pedenB]; rewrite (IH _ eq_refl), rpcompose_compose; reflexivity.
  - destruct (pfun q) as [A0|]; [|discriminate]; injection E as <-.
    cbn [aedenB pedenB]; rewrite (IH _ eq_refl), rpshift_as_pcompose, rpcompose_compose, rpush_outer_as_compose.
    reflexivity.
Qed.

Hypothesis Hnf : Forall (fun '(k, (k', C)) => exists (c : adj T 0 0) u,
                          adj_raw c = den C /\ bnth Te k' = Some u /\ bnth Te k = Some (g (rpcompose (adj_raw c) rpidentity) u)) nf.
Hypothesis Hvf : Forall (fun '(k, (h, i)) => exists w : var 0,
                          bnth Te k = Some (var0 w) /\ var_raw w = mk_rvar (ldenB Le h) (N.to_nat i)) vf.

Local Notation B := (cbase var0 g).

Lemma tres_bind u p : rtarget_result (tden (NBindE u p))
  = match bnth Te u with Some x => inr (x, pden p) | None => inl (mk_rvar None 0) end.
Proof. cbn [tedenB]; destruct (bnth Te u); reflexivity. Qed.

Lemma tres_look h i a : rtarget_result (tden (NLookE h i a)) = rapply (den a) (mk_rvar (ldenB Le h) (N.to_nat i)).
Proof.
  change (tden (NLookE h i a)) with (rapply_target (den a) (RRename (mk_rvar (ldenB Le h) (N.to_nat i)))).
  unfold rapply_target; destruct (rapply _ _) as [w|[u ρ]]; reflexivity.
Qed.

Theorem conv_sound :
  (forall e v, drel B (rapply (den e) v) (rapply (den (aconv e)) v))
  /\ (forall t, drel B (rtarget_result (tden t)) (rtarget_result (tden (tconv t))))
  /\ (forall p u, drel B (inr (u, pden p)) (inr (u, pden (pconv p)))).
Proof.
  pose proof (cbase_rcomp var0 g) as HB.
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
    destruct (nlook u nf) as [[u' C]|] eqn:En.
    + destruct (pfun (pconv p)) as [A|] eqn:Ep; [|rewrite !tres_bind; destruct (bnth Te u); [apply IH|apply DEq]].
      pose proof (nlook_in _ _ _ En) as Hin; rewrite Forall_forall in Hnf.
      destruct (Hnf _ Hin) as [c [x' [Ec [Ex' Ex]]]].
      rewrite !tres_bind, Ex, Ex'; eapply DTrans; [apply IH|].
      rewrite (pfun_den _ _ Ep); apply DBase; left.
      exists x', c, (den A); split; [reflexivity|].
      cbn [pedenB aedenB]; rewrite Ec; reflexivity.
    + destruct (nlook u vf) as [[h i]|] eqn:Ev.
      * destruct (pfun (pconv p)) as [A|] eqn:Ep; [|rewrite !tres_bind; destruct (bnth Te u); [apply IH|apply DEq]].
        pose proof (nlook_in _ _ _ Ev) as Hin; rewrite Forall_forall in Hvf.
        destruct (Hvf _ Hin) as [w [Ew Hw]].
        rewrite tres_bind, Ew; eapply DTrans; [apply IH|].
        rewrite (pfun_den _ _ Ep); apply DBase; right.
        exists w, (den A); split; [reflexivity|].
        rewrite tres_look, Hw; reflexivity.
      * rewrite !tres_bind; destruct (bnth Te u); [apply IH|apply DEq].
  - intros h t _; apply DEq.
  - intros h i a IH; cbn [tconv]; rewrite !tres_look; apply IH.
  - intros u; apply DEq.
  - intros n u; apply DEq.
  - intros a IHa q IHq u; cbn [pconv pedenB].
    change (drel B (rcomp (den a) (inr (u, pden q))) (rcomp (den (aconv a)) (inr (u, pden (pconv q))))).
    apply drel_rcomp2; [exact HB|exact IHa|apply IHq].
  - intros h q IH u; cbn [pconv pedenB]; rewrite !rpshift_as_pcompose.
    change (drel B (rcomp (rshift (ldenB Le h)) (inr (u, pden q))) (rcomp (rshift (ldenB Le h)) (inr (u, pden (pconv q))))).
    apply (drel_rcomp B HB), IH.
Qed.

End Conv.
