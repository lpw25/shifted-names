(** * Reading layered words

    What [names] needs besides the decision: the result of a variable,
    the normal form as a tree when it is small enough to show, and the
    comparisons behind payloads that are shown or materialised.  All of
    it is computed from the layered word of [Layered]; a tree is the
    word multiplied out ([expand]). *)

From Stdlib Require Import Arith List Lia Bool NArith.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Shared Eval Layered.
Import ListNotations.

Section Defs.

Variable F : order.
Variable ntm : nat.

(** Following a variable through a layered word: the target it reaches
    and the rest of the word after that step. *)
Fixpoint ltgt (l : lword) (h : lexp) (i : nat) : option (ntgt * lword) :=
  match l with
  | [] => Some (NVar h i, [])
  | LS s :: r =>
      match seg_tgt F s h i with
      | Some (NVar g j) => ltgt r g j
      | Some t => Some (t, r)
      | None => None
      end
  | LA L a :: r =>
      match wtgt F (WAtom SNil L a (WEnd SNil)) h i with
      | Some (NVar g j) => ltgt r g j
      | _ => None
      end
  end.

Definition lapply_result (e : aexp) (h : lexp) (i : nat) : option (lexp * nat) :=
  match lnorm F ntm e with
  | Some l => match ltgt l h i with Some (NVar h' j, _) => Some (h', j) | _ => None end
  | None => None
  end.

(** The normal form as a tree. *)
Definition tnorm (e : aexp) : option word := obind (lnorm F ntm e) (expand F ntm).

(** What the rest of a word is as a payload. *)
Definition rest_pay (r : lword) : option word :=
  match expand F ntm r with Some w => Some (pnorm w) | None => None end.

(** A variable sent to a term, checked against the reified adjustment
    [eb] its payload was shown as. *)
Definition lapply_bind_check (e : aexp) (h : lexp) (i : nat) (eb : aexp) : option nat :=
  match lnorm F ntm e with
  | Some l =>
      match ltgt l h i with
      | Some (NBind u (WEnd SNil) None, r) =>
          match rest_pay r, tnorm eb with
          | Some p, Some wb => if word_eqb p (pnorm wb) then Some u else None
          | _, _ => None
          end
      | _ => None
      end
  | None => None
  end.

(** Materialised payloads: see [Eval.mat_eqb_s]. *)
Fixpoint lfacts (facts : list (nat * nat * aexp)) : option (list (nat * ntgt)) :=
  match facts with
  | [] => Some []
  | (k, u, eb) :: r =>
      if u <? ntm then
        match tnorm eb, lfacts r with
        | Some w, Some l => Some ((k, NBind u (pnorm w) None) :: l)
        | _, _ => None
        end
      else None
  end.

Definition lmat_eqb (facts : list (nat * nat * aexp)) (e e' : aexp) : bool :=
  match tnorm e, tnorm e', lfacts facts with
  | Some (WEnd S1), Some (WEnd S2), Some l => smat_s ntm l S1 S2
  | _, _, _ => false
  end.

(** ** Size *)

(** The size of a tree. *)
Fixpoint tsz (t : ntgt) : N :=
  match t with
  | NVar _ _ => 1%N
  | NBind _ (WEnd SNil) _ => 1%N
  | NBind _ w _ => (1 + wsz w)%N
  end
with tlsz (ts : tlist) : N :=
  match ts with TNil => 0%N | TCons t r => (tsz t + tlsz r)%N end
with ssz (s : seg) : N :=
  match s with SNil => 0%N | SEnt _ ts _ r => (1 + tlsz ts + ssz r)%N end
with wsz (w : word) : N :=
  match w with WEnd s => (1 + ssz s)%N | WAtom s _ _ w' => (1 + ssz s + wsz w')%N end.

(** An estimate of the size of the tree of a layered word, without
    multiplying out: every term of a segment gets the rest.  It stops
    counting at [cap]. *)
Fixpoint ntms (ts : tlist) : N :=
  match ts with
  | TNil => 0%N
  | TCons (NBind _ _ _) r => (1 + ntms r)%N
  | TCons _ r => ntms r
  end.

Fixpoint sntms (s : seg) : N :=
  match s with SNil => 0%N | SEnt _ ts _ r => (ntms ts + sntms r)%N end.

Definition cap : N := 20000%N.

Fixpoint lest (l : lword) : N :=
  match l with
  | [] => 1%N
  | LS s :: r => N.min cap (ssz s + (1 + sntms s) * lest r)
  | LA _ _ :: r => N.min cap (2 + lest r)
  end.

Definition expand_small (budget : N) (l : lword) : option word :=
  if (lest l <? cap)%N then
    match expand F ntm l with
    | Some w => if (wsz w <=? budget)%N then Some w else None
    | None => None
    end
  else None.

Definition lshow (e : aexp) : shown :=
  match lnorm F ntm e with
  | Some l =>
      if (lest l <? cap)%N then
        match expand F ntm l with
        | Some w => if (wsz w <=? show_budget)%N then ShWord w else ShLarge
        | None => ShNone
        end
      else ShLarge
  | None => ShNone
  end.

(** The decision: the layered words are the same, or, when both are
    small enough to multiply out, their trees are. *)
Definition nf_eq_t (e1 e2 : aexp) : bool :=
  match lnorm F ntm e1, lnorm F ntm e2 with
  | Some l1, Some l2 =>
      if lword_eqb l1 l2 then true
      else if (lest l1 <? cap)%N then
        if (lest l2 <? cap)%N then
          match expand F ntm l1, expand F ntm l2 with
          | Some w1, Some w2 => word_eqb w1 w2
          | _, _ => false
          end
        else false
      else false
  | _, _ => false
  end.

(** A variable sent to a term whose payload ends with the identity: the
    term and the payload as a tree, for [names] to show. *)
Definition lapply_payload (e : aexp) (h : lexp) (i : nat) : option (nat * word) :=
  match lnorm F ntm e with
  | Some l =>
      match ltgt l h i with
      | Some (NBind u (WEnd SNil) None, r) =>
          match expand_small show_budget r with Some w => Some (u, pnorm w) | None => None end
      | _ => None
      end
  | None => None
  end.

End Defs.

Section Sound.

Context {T : Type}.
Variable lenv : list label.
Variable tenv : list T.
Variable aenv : list (radj T).
Variable penv : list (rpadj T).
Variable F : order.
Hypothesis HF : facts_ok lenv F.
Variable ntm : nat.
Hypothesis Hntm : ntm <= List.length tenv.

Local Notation lden := (lden lenv).
Local Notation tden := (tden lenv tenv aenv penv).
Local Notation sden := (sden lenv tenv aenv penv).
Local Notation wden := (wden lenv tenv aenv penv).
Local Notation aeden := (aeden lenv tenv aenv penv).
Local Notation lwden := (lwden lenv tenv aenv penv).
Local Notation lwdist := (lwdist lenv).

Lemma lnorm_dist e l : lnorm F ntm e = Some l -> lwdist l.
Proof.
  intros H; exact (proj1 (proj1 (proj1 (sound lenv tenv aenv penv F HF ntm Hntm) e) 0 [] l (Forall_nil _) H)).
Qed.

Lemma ltgt_sound l : forall h i t r, lwdist l -> ltgt F l h i = Some (t, r) ->
  lwdist r /\ rapply (lwden l) (mk_rvar (lden h) i) = cres (lwden r) (rtarget_result (tden t)).
Proof.
  induction l as [|[s|L a] l IH]; intros h i t r Hl; cbn [ltgt].
  - intros H; injection H as <- <-; split; [exact Hl|]; cbn [Layered.lwden Normalise.tden rtarget_result cres]; reflexivity.
  - inversion Hl as [|? ? Hs Hr]; subst.
    destruct (seg_tgt F s h i) as [t0|] eqn:E; [|discriminate].
    destruct (seg_tgt_sound lenv tenv aenv penv F HF s h i t0 Hs E) as [_ D].
    cbn [Layered.lwden]; rewrite rapply_compose_cres, D.
    destruct t0 as [g j|u w b].
    + intros H; destruct (IH g j t r Hr H) as [A B]; split; [exact A|].
      cbn [Normalise.tden rtarget_result cres]; exact B.
    + intros H; injection H as <- <-; split; [exact Hr|reflexivity].
  - inversion Hl as [|? ? _ Hr]; subst.
    destruct (wtgt F (WAtom SNil L a (WEnd SNil)) h i) as [[g j|]|] eqn:E; try discriminate.
    assert (Hd : wdist lenv (WAtom SNil L a (WEnd SNil))) by (cbn; repeat split; exact I).
    destruct (wtgt_sound lenv tenv aenv penv F HF ntm Hntm _ h i _ Hd E) as [_ D].
    assert (Ew : wden (WAtom SNil L a (WEnd SNil)) = lifts lenv L (aden aenv a)).
    { rewrite wden_atom, wden_end; change (sden SNil) with (@ridentity T).
      rewrite rcompose_identity_l, rcompose_identity_r; reflexivity. }
    rewrite Ew in D.
    intros H; destruct (IH g j t r Hr H) as [A B]; split; [exact A|].
    cbn [Layered.lwden]; rewrite rapply_compose_cres, D; cbn [Normalise.tden rtarget_result cres]; exact B.
Qed.

Theorem lapply_result_sound e h i h' j :
  lapply_result F ntm e h i = Some (h', j) ->
  rapply (aeden e) (mk_rvar (lden h) i) = inl (mk_rvar (lden h') j).
Proof.
  unfold lapply_result; destruct (lnorm F ntm e) as [l|] eqn:E; [|discriminate].
  destruct (ltgt F l h i) as [[[g k|] r]|] eqn:Et; try discriminate; intros H; injection H as <- <-.
  destruct (ltgt_sound l h i _ _ (lnorm_dist e l E) Et) as [_ D].
  rewrite <- (lnorm_sound lenv tenv aenv penv F HF ntm Hntm e l E), D.
  destruct r as [|x r].
  - cbn [Layered.lwden Normalise.tden rtarget_result cres]; apply rapply_identity.
  - revert Et; clear; revert h i; induction l as [|[s|L a] l IH]; intros h i; cbn [ltgt].
    + discriminate.
    + destruct (seg_tgt F s h i) as [[g0 j0|]|]; [apply IH|discriminate|discriminate].
    + destruct (wtgt F (WAtom SNil L a (WEnd SNil)) h i) as [[g0 j0|]|]; [apply IH|discriminate|discriminate].
Qed.

Lemma tnorm_sound e w : tnorm F ntm e = Some w -> wdist lenv w /\ wden w = aeden e.
Proof.
  unfold tnorm; destruct (lnorm F ntm e) as [l|] eqn:E; [|discriminate]; cbn [obind]; intros H.
  destruct (expand_sound lenv tenv aenv penv F HF ntm Hntm l w (lnorm_dist e l E) H) as [A B].
  split; [exact A|]; rewrite B; exact (lnorm_sound lenv tenv aenv penv F HF ntm Hntm e l E).
Qed.

Lemma pnorm_pay w : rpcompose (wden (pnorm w)) rpidentity = rpcompose (wden w) (@rpidentity T).
Proof. symmetry; apply rpcompose_named, named_pnorm. Qed.

Theorem lapply_bind_sound e h i eb u x :
  lapply_bind_check F ntm e h i eb = Some u -> nth_error tenv u = Some x ->
  rapply (aeden e) (mk_rvar (lden h) i) = inr (x, rpcompose (aeden eb) rpidentity).
Proof.
  unfold lapply_bind_check; destruct (lnorm F ntm e) as [l|] eqn:E; [|discriminate].
  destruct (ltgt F l h i) as [[[|u0 [[|]|] [|]] r]|] eqn:Et; try discriminate.
  unfold rest_pay; destruct (expand F ntm r) as [wr|] eqn:Er; [|discriminate].
  destruct (tnorm F ntm eb) as [wb|] eqn:Eb; [|discriminate].
  destruct (word_eqb (pnorm wr) (pnorm wb)) eqn:Eq; [|discriminate]; intros H; injection H as <-; intros Hx.
  apply (proj2 (proj2 (proj2 nf_eqb_eq))) in Eq.
  destruct (ltgt_sound l h i _ _ (lnorm_dist e l E) Et) as [Hr D].
  destruct (expand_sound lenv tenv aenv penv F HF ntm Hntm r wr Hr Er) as [_ Dr].
  destruct (tnorm_sound eb wb Eb) as [_ Db].
  rewrite <- (lnorm_sound lenv tenv aenv penv F HF ntm Hntm e l E), D.
  rewrite (tden_bind lenv tenv aenv penv _ _ _ _ Hx); cbn [rtarget_result cres bden].
  rewrite wden_end; change (sden SNil) with (@ridentity T); rewrite rpcompose_identity.
  rewrite <- Dr, <- Db, <- (pnorm_pay wr), <- (pnorm_pay wb), Eq; reflexivity.
Qed.

Theorem nf_eq_t_sound e1 e2 : nf_eq_t F ntm e1 e2 = true -> aeden e1 = aeden e2.
Proof.
  unfold nf_eq_t; destruct (lnorm F ntm e1) as [l1|] eqn:E1; [|discriminate].
  destruct (lnorm F ntm e2) as [l2|] eqn:E2; [|discriminate].
  rewrite <- (lnorm_sound lenv tenv aenv penv F HF ntm Hntm e1 l1 E1),
          <- (lnorm_sound lenv tenv aenv penv F HF ntm Hntm e2 l2 E2).
  destruct (lword_eqb l1 l2) eqn:El; [intros _; apply lword_eqb_eq in El; subst; reflexivity|].
  destruct (lest l1 <? cap)%N; [|discriminate]; destruct (lest l2 <? cap)%N; [|discriminate].
  destruct (expand F ntm l1) as [w1|] eqn:X1; [|discriminate].
  destruct (expand F ntm l2) as [w2|] eqn:X2; [|discriminate]; intros Hw.
  apply (proj2 (proj2 (proj2 nf_eqb_eq))) in Hw; subst w2.
  rewrite <- (proj2 (expand_sound lenv tenv aenv penv F HF ntm Hntm l1 w1 (lnorm_dist e1 l1 E1) X1)).
  exact (proj2 (expand_sound lenv tenv aenv penv F HF ntm Hntm l2 w1 (lnorm_dist e2 l2 E2) X2)).
Qed.

Section Mat.

Variable g : rpadj T -> T -> T.
Variable facts : list (nat * nat * aexp).
Hypothesis Hfacts : Forall (fun f => let '(k, u, eb) := f in
  forall y, nth_error tenv u = Some y -> nth_error tenv k = Some (g (rpcompose (aeden eb) rpidentity) y)) facts.

Lemma lfacts_spec fs : forall l, lfacts F ntm fs = Some l ->
  forall k tk, nfind l k = Some tk ->
    exists u eb y, mfind fs k = Some (u, eb) /\ nth_error tenv u = Some y
      /\ tden tk = RBind y (rpcompose (aeden eb) rpidentity).
Proof.
  induction fs as [|[[k0 u0] eb0] fs IH]; intros l; cbn [lfacts].
  - intros H; injection H as <-; discriminate.
  - destruct (u0 <? ntm) eqn:Eu; [|discriminate]; apply Nat.ltb_lt in Eu.
    destruct (tnorm F ntm eb0) as [w|] eqn:Ew; [|discriminate].
    destruct (lfacts F ntm fs) as [l0|] eqn:El; [|discriminate]; intros H; injection H as <-.
    intros k tk; cbn [nfind mfind]; destruct (Nat.eqb k k0); [|exact (IH l0 eq_refl k tk)].
    intros H; injection H as <-.
    destruct (nth_error tenv u0) as [y|] eqn:Ey; [|apply nth_error_None in Ey; lia].
    exists u0, eb0, y; refine (conj eq_refl (conj Ey _)).
    rewrite (tden_bind lenv tenv aenv penv _ _ _ _ Ey); cbn [bden].
    rewrite pnorm_pay, (proj2 (tnorm_sound eb0 w Ew)); reflexivity.
Qed.

Theorem lmat_sound e e' :
  lmat_eqb F ntm facts e e' = true -> forall v, mrel g (rapply (aeden e) v) (rapply (aeden e') v).
Proof.
  unfold lmat_eqb; destruct (tnorm F ntm e) as [[S1|]|] eqn:E1; try discriminate.
  destruct (tnorm F ntm e') as [[S2|]|] eqn:E2; try discriminate.
  destruct (lfacts F ntm facts) as [l|] eqn:E3; [|discriminate]; intros Hm.
  destruct (tnorm_sound e _ E1) as [HD D1]; destruct (tnorm_sound e' _ E2) as [HD' D2].
  rewrite <- D1, <- D2, !wden_end.
  pose proof (sdistd_sdist lenv _ HD) as Hd; pose proof (sdistd_sdist lenv _ HD') as Hd'; intros [lab j].
  rewrite !rapply_sden by assumption.
  cbn [v_label v_index]; pose proof (smat_s_get lenv _ _ _ _ lab Hm) as Hg.
  destruct (sget lenv lab S1) as [[ts m]|] eqn:Eg, (sget lenv lab S2) as [[ts' m']|]; try contradiction; [|left; reflexivity].
  destruct Hg as [Ht <-]; cbn [esem]; rewrite <- (tlmat_s_len _ _ _ _ Ht).
  destruct (j <? tlen ts) eqn:Ej; [|left; reflexivity].
  apply (tmat_s_sound lenv tenv aenv penv ntm g facts Hfacts penv l _ _ (lfacts_spec facts l E3)).
  apply (tlmat_s_nth tenv ntm Hntm); [exact Ht|apply Nat.ltb_lt, Ej].
Qed.

End Mat.

End Sound.
