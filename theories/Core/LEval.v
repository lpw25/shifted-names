(** * Reading layered words

    What [names] needs besides the decision: the result of a variable,
    the normal form as a tree when it is small enough to show, and the
    comparisons behind payloads that are shown or materialised.  All of
    it is computed from the layered word of [Layered]; a tree is the
    word multiplied out ([expand]). *)

From Stdlib Require Import Arith List Lia Bool NArith.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Unique Normal Complete Layered Canon LNormal.
Import ListNotations.

(** Larger normal forms are not shown: as a tree, a chain of
    substitutions doubles with each step. *)
Definition show_budget : N := 250%N.

Inductive shown : Type :=
| ShNone
| ShLarge
| ShWord (w : word).

(** ** Materialised payloads

    Two adjustments that are the same except that, where the first sends
    a variable to a term [u⟨w⟩], the second sends it to a term atom [k]
    with the identity payload adjustment, where [k] is [u] with the
    payload adjustment applied ([facts]: [(k, u, eb)], [eb] the reified
    adjustment the payload was shown as).  The first adjustment must
    have [u] with the tree of [eb] as payload where the second has [k]. *)
Fixpoint nfind (l : list (nat * ntgt)) (k : nat) : option ntgt :=
  match l with [] => None | (k', t) :: r => if Nat.eqb k k' then Some t else nfind r k end.

Definition tmat_s (ntm : nat) (l : list (nat * ntgt)) (t t' : ntgt) : bool :=
  if ntgt_eqb t t' then true
  else match t' with
       | NBind k (WEnd SNil) None =>
           match nfind l k with Some tk => ntgt_eqb t tk && (k <? ntm) | None => false end
       | _ => false
       end.

Fixpoint tlmat_s (ntm : nat) (l : list (nat * ntgt)) (ts ts' : tlist) : bool :=
  match ts, ts' with
  | TNil, TNil => true
  | TCons t r, TCons t' r' => tmat_s ntm l t t' && tlmat_s ntm l r r'
  | _, _ => false
  end.

Fixpoint smat_s (ntm : nat) (l : list (nat * ntgt)) (s s' : seg) : bool :=
  match s, s' with
  | SNil, SNil => true
  | SEnt h ts m r, SEnt h' ts' m' r' =>
      lexp_eqb h h' && tlmat_s ntm l ts ts' && Nat.eqb m m' && smat_s ntm l r r'
  | _, _ => false
  end.

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
(** The canonical layered word of an expression. *)
Definition lcanon (e : aexp) : option lword := obind (lnorm F ntm e) (canon F ntm).

(** The rest of a word as a payload: without what it does to the bound
    variables it starts with. *)
Definition lrestrict (r : lword) : option lword :=
  match r with
  | LS s1 :: K => ccons F ntm (4 * List.length r + 100) (sdrop_none s1) K
  | _ => Some r
  end.

(** A variable sent to a term: the term and the rest of the word after
    it, for [names] to show as the payload. *)
Definition lapply_rest (e : aexp) (h : lexp) (i : nat) : option (nat * lword) :=
  match lcanon e with
  | Some l =>
      match ltgt l h i with
      | Some (NBind u (WEnd SNil) None, r) => option_map (pair u) (lrestrict r)
      | _ => None
      end
  | None => None
  end.

(** ... checked against the reified adjustment [eb] it was shown as. *)
Definition lapply_bind_check (e : aexp) (h : lexp) (i : nat) (eb : aexp) : option nat :=
  match lapply_rest e h i, lcanon eb with
  | Some (u, r), Some lb => if lword_eqb lb r then Some u else None
  | _, _ => None
  end.

(** The facts, with the payloads as trees. *)
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

(** Multiplying out, giving up when the tree of a rest of the word has
    more than [c] nodes. *)
Fixpoint expand_c (c : N) (l : lword) : option word :=
  match l with
  | [] => Some (WEnd SNil)
  | x :: r =>
      match expand_c c r with
      | Some w =>
          match wcomp F ntm w (match x with LS s => WEnd s | LA L a => WAtom SNil L a (WEnd SNil) end) with
          | Some w' => if (wsz w' <=? c)%N then Some w' else None
          | None => None
          end
      | None => None
      end
  end.

(** The trees the decision is willing to build. *)
Definition cap : N := 100000%N.

Definition lshow (e : aexp) : shown :=
  match lnorm F ntm e with
  | Some l =>
      match expand_c (20 * show_budget) l with
      | Some w => if (wsz w <=? show_budget)%N then ShWord w else ShLarge
      | None => ShLarge
      end
  | None => ShNone
  end.

(** The decision: the layered words are the same, or, when both trees
    are small enough to build, the trees are. *)
Definition nf_eq_t (e1 e2 : aexp) : bool :=
  match lnorm F ntm e1, lnorm F ntm e2 with
  | Some l1, Some l2 =>
      if match canon F ntm l1, canon F ntm l2 with Some c1, Some c2 => lword_eqb c1 c2 | _, _ => false end then true
      else match expand_c cap l1, expand_c cap l2 with
           | Some w1, Some w2 => word_eqb w1 w2
           | _, _ => false
           end
  | _, _ => false
  end.

(** A variable sent to a term whose payload ends with the identity: the
    term and the payload as a tree, for [names] to show. *)
Definition lapply_payload (e : aexp) (h : lexp) (i : nat) : option (nat * word) :=
  match lnorm F ntm e with
  | Some l =>
      match ltgt l h i with
      | Some (NBind u (WEnd SNil) None, r) =>
          match expand_c show_budget r with Some w => Some (u, pnorm w) | None => None end
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

Lemma expand_c_some c l : forall w, expand_c F ntm c l = Some w -> expand F ntm l = Some w.
Proof.
  induction l as [|x r IH]; intros w; cbn [expand_c expand]; [exact (fun H => H)|].
  destruct (expand_c F ntm c r) as [w0|]; [|discriminate]; rewrite (IH w0 eq_refl).
  destruct x as [s|L a]; cbn [obind];
    (match goal with |- context [wcomp F ntm w0 ?y] => destruct (wcomp F ntm w0 y) as [w'|] end; [|discriminate]);
    (destruct (wsz w' <=? c)%N; [exact (fun H => H)|discriminate]).
Qed.

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

Lemma lcanon_sound e l : lcanon F ntm e = Some l -> lwdist l /\ lwden l = aeden e.
Proof.
  unfold lcanon; destruct (lnorm F ntm e) as [l0|] eqn:E; [|discriminate]; cbn [obind]; intros H.
  destruct (canon_sound lenv tenv aenv penv F HF ntm Hntm l0 l (lnorm_dist e l0 E) H) as [A B].
  split; [exact A|]; rewrite B; exact (lnorm_sound lenv tenv aenv penv F HF ntm Hntm e l0 E).
Qed.

Lemma lrestrict_sound r r' : lwdist r -> lrestrict F ntm r = Some r' ->
  rpcompose (lwden r') rpidentity = rpcompose (lwden r) (@rpidentity T).
Proof.
  intros Hr; destruct r as [|[s1|L a] K]; cbn [lrestrict]; try (intros H; injection H as <-; reflexivity).
  inversion Hr as [|? ? Hs1 HK]; subst; intros H.
  destruct (ccons_sound lenv tenv aenv penv F HF ntm Hntm _ _ K r' (sdrop_dd lenv _ Hs1) HK H) as [_ D].
  rewrite D; cbn [Layered.lwden]; apply rpcompose_named; intros v Hv.
  rewrite !rapply_compose_cres, (named_sdrop_none lenv tenv aenv penv s1 v Hv); reflexivity.
Qed.

Theorem lapply_bind_sound e h i eb u x :
  lapply_bind_check F ntm e h i eb = Some u -> nth_error tenv u = Some x ->
  rapply (aeden e) (mk_rvar (lden h) i) = inr (x, rpcompose (aeden eb) rpidentity).
Proof.
  unfold lapply_bind_check, lapply_rest; destruct (lcanon F ntm e) as [l|] eqn:E; [|discriminate].
  destruct (ltgt F l h i) as [[[|u0 [[|]|] [|]] r]|] eqn:Et; try discriminate.
  destruct (lrestrict F ntm r) as [r'|] eqn:Er; [|discriminate]; cbn [option_map].
  destruct (lcanon F ntm eb) as [lb|] eqn:Eb; [|discriminate].
  destruct (lword_eqb lb r') eqn:Eq; [|discriminate]; intros H; injection H as <-; intros Hx.
  apply lword_eqb_eq in Eq; subst lb.
  destruct (lcanon_sound e l E) as [Hl Dl]; destruct (lcanon_sound eb r' Eb) as [_ Db].
  destruct (ltgt_sound l h i _ _ Hl Et) as [Hr D].
  rewrite <- Dl, D, (tden_bind lenv tenv aenv penv _ _ _ _ Hx); cbn [rtarget_result cres bden].
  rewrite wden_end; change (sden SNil) with (@ridentity T); rewrite rpcompose_identity.
  rewrite <- Db, (lrestrict_sound r r' Hr Er); reflexivity.
Qed.


Theorem nf_eq_t_sound e1 e2 : nf_eq_t F ntm e1 e2 = true -> aeden e1 = aeden e2.
Proof.
  unfold nf_eq_t; destruct (lnorm F ntm e1) as [l1|] eqn:E1; [|discriminate].
  destruct (lnorm F ntm e2) as [l2|] eqn:E2; [|discriminate].
  rewrite <- (lnorm_sound lenv tenv aenv penv F HF ntm Hntm e1 l1 E1),
          <- (lnorm_sound lenv tenv aenv penv F HF ntm Hntm e2 l2 E2).
  destruct (match canon F ntm l1, canon F ntm l2 with Some c1, Some c2 => lword_eqb c1 c2 | _, _ => false end) eqn:El.
  { intros _; destruct (canon F ntm l1) as [c1|] eqn:C1; [|discriminate El].
    destruct (canon F ntm l2) as [c2|] eqn:C2; [|discriminate El].
    apply lword_eqb_eq in El; subst c2.
    rewrite <- (proj2 (canon_sound lenv tenv aenv penv F HF ntm Hntm l1 c1 (lnorm_dist e1 l1 E1) C1)).
    exact (proj2 (canon_sound lenv tenv aenv penv F HF ntm Hntm l2 c1 (lnorm_dist e2 l2 E2) C2)). }
  destruct (expand_c F ntm cap l1) as [w1|] eqn:X1; [|discriminate].
  destruct (expand_c F ntm cap l2) as [w2|] eqn:X2; [|discriminate]; intros Hw.
  apply expand_c_some in X1, X2.
  apply (proj2 (proj2 (proj2 nf_eqb_eq))) in Hw; subst w2.
  rewrite <- (proj2 (expand_sound lenv tenv aenv penv F HF ntm Hntm l1 w1 (lnorm_dist e1 l1 E1) X1)).
  exact (proj2 (expand_sound lenv tenv aenv penv F HF ntm Hntm l2 w1 (lnorm_dist e2 l2 E2) X2)).
Qed.

Lemma tlmat_s_len l ts ts' : tlmat_s ntm l ts ts' = true -> tlen ts = tlen ts'.
Proof.
  revert ts'; induction ts as [|t r IH] using tlist_spine; intros [|t' r']; cbn; try discriminate; [reflexivity|].
  intros H; apply andb_true_iff in H as [_ H]; rewrite (IH _ H); reflexivity.
Qed.

Lemma tlmat_s_nth l ts ts' j :
  tlmat_s ntm l ts ts' = true -> j < tlen ts -> tmat_s ntm l (tnth ts j) (tnth ts' j) = true.
Proof.
  revert ts' j; induction ts as [|t r IH] using tlist_spine; intros [|t' r'] j; cbn; try discriminate; [lia|].
  intros H Hj; apply andb_true_iff in H as [H1 H2]; destruct j; [exact H1|apply IH; [exact H2|lia]].
Qed.

Lemma smat_s_get l s s' lab : smat_s ntm l s s' = true ->
  match sget lenv lab s, sget lenv lab s' with
  | Some (ts, m), Some (ts', m') => tlmat_s ntm l ts ts' = true /\ m = m'
  | None, None => True
  | _, _ => False
  end.
Proof.
  revert s'; induction s as [|h ts m r IH] using seg_spine; intros [|h' ts' m' r']; cbn [smat_s]; try discriminate; [cbn; tauto|].
  intros H; apply andb_true_iff in H as [H H4]; apply andb_true_iff in H as [H H3]; apply andb_true_iff in H as [H1 H2].
  apply lexp_eqb_eq in H1; apply Nat.eqb_eq in H3; subst h' m'; cbn [sget].
  destruct (label_eqb (lden h) lab); [split; [exact H2|reflexivity]|apply IH, H4].
Qed.

Section Mat.

Variable g : rpadj T -> T -> T.
Variable facts : list (nat * nat * aexp).
Hypothesis Hfacts : Forall (fun f => let '(k, u, eb) := f in
  forall y, nth_error tenv u = Some y -> nth_error tenv k = Some (g (rpcompose (aeden eb) rpidentity) y)) facts.

Lemma tmat_s_sound l t t' :
  (forall k tk, nfind l k = Some tk ->
     exists u eb y, mfind facts k = Some (u, eb) /\ nth_error tenv u = Some y
       /\ tden tk = RBind y (rpcompose (aeden eb) rpidentity)) ->
  tmat_s ntm l t t' = true -> mrel g (rtarget_result (tden t)) (rtarget_result (tden t')).
Proof.
  intros Hfind; unfold tmat_s; destruct (ntgt_eqb t t') eqn:E; cbn [orb].
  { intros _; left; apply (proj1 nf_eqb_eq) in E; subst; reflexivity. }
  destruct t' as [|k [[|]|] [b'|]]; try discriminate.
  destruct (nfind l k) as [tk|] eqn:Ef; [|discriminate]; intros H; apply andb_true_iff in H as [H1 H2].
  apply (proj1 nf_eqb_eq) in H1; subst tk.
  destruct (Hfind k t Ef) as [u [eb [y [Em [Ey Dt]]]]].
  right; exists y, (rpcompose (aeden eb) rpidentity); rewrite Dt; split; [reflexivity|].
  rewrite (tden_bind lenv tenv aenv penv _ _ _ _ (mfind_fact lenv tenv aenv penv g facts Hfacts _ _ _ _ Em Ey)).
  cbn [rtarget_result]; do 2 f_equal; exact (rpcompose_identity _).
Qed.

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
  cbn [v_label v_index]; pose proof (smat_s_get _ _ _ lab Hm) as Hg.
  destruct (sget lenv lab S1) as [[ts m]|] eqn:Eg, (sget lenv lab S2) as [[ts' m']|]; try contradiction; [|left; reflexivity].
  destruct Hg as [Ht <-]; cbn [esem]; rewrite <- (tlmat_s_len _ _ _ Ht).
  destruct (j <? tlen ts) eqn:Ej; [|left; reflexivity].
  apply (tmat_s_sound l _ _ (lfacts_spec facts l E3)).
  apply tlmat_s_nth; [exact Ht|apply Nat.ltb_lt, Ej].
Qed.

End Mat.

End Sound.

Lemma lifts_eqb_refl L : lifts_eqb L L = true.
Proof.
  induction L as [|[h n] L IH]; cbn [lifts_eqb]; [reflexivity|].
  rewrite (proj2 (lexp_eqb_eq h h) eq_refl), Nat.eqb_refl, IH; reflexivity.
Qed.

Lemma nf_eqb_refl :
  (forall t, ntgt_eqb t t = true) /\ (forall ts, tlist_eqb ts ts = true) /\ (forall s, seg_eqb s s = true)
  /\ (forall w, word_eqb w w = true).
Proof.
  apply nf_mind.
  - intros h i; cbn [ntgt_eqb]; rewrite (proj2 (lexp_eqb_eq h h) eq_refl), Nat.eqb_refl; reflexivity.
  - intros u w IH b; cbn [ntgt_eqb]; fold word_eqb; rewrite Nat.eqb_refl, IH; destruct b as [n|]; [apply Nat.eqb_refl|reflexivity].
  - reflexivity.
  - intros t IHt r IHr; cbn [tlist_eqb]; fold ntgt_eqb tlist_eqb; rewrite IHt, IHr; reflexivity.
  - reflexivity.
  - intros h ts IHts m r IHr; cbn [seg_eqb]; fold tlist_eqb seg_eqb.
    rewrite (proj2 (lexp_eqb_eq h h) eq_refl), IHts, Nat.eqb_refl, IHr; reflexivity.
  - intros s IH; exact IH.
  - intros s IHs L a w IHw; cbn [word_eqb]; fold seg_eqb word_eqb; rewrite IHs, lifts_eqb_refl, Nat.eqb_refl, IHw; reflexivity.
Qed.

(** ** The tree is the normal form, and the decision is complete

    The tree of an expression satisfies the normal-form conditions, so
    two expressions that mean the same under every interpretation have
    the same tree; the decision then answers [true] whenever both trees
    are small enough for it to compute them. *)

Theorem tnorm_normal lenv labs F ntm N e w :
  facts_ok lenv F -> In LNone labs -> incl (alabs e) labs -> apmax e <= N ->
  tnorm F ntm e = Some w -> wnf lenv labs N false w.
Proof.
  intros HF Hn Hl HN; unfold tnorm; destruct (lnorm F ntm e) as [l|] eqn:E; [|discriminate]; cbn [obind]; intros H.
  refine (expand_normal lenv labs N F HF ntm l w _ H).
  exact (lnorm_normal lenv labs N F HF ntm Hn e l Hl (proj1 (scope_max N) e HN) E).
Qed.

Theorem tnorm_complete lenv l ntm e1 e2 w1 w2 :
  lfacts_ok lenv l ->
  (forall lenv' (T : Type) (tenv : list T) aenv penv, lfacts_ok lenv' l -> ntm <= List.length tenv ->
     aeden lenv' tenv aenv penv e1 = aeden lenv' tenv aenv penv e2) ->
  tnorm (order_of l) ntm e1 = Some w1 -> tnorm (order_of l) ntm e2 = Some w2 -> w1 = w2.
Proof.
  intros HF Heq E1 E2.
  set (N := Nat.max (apmax e1) (apmax e2)).
  set (S := LNone :: alabs e1 ++ alabs e2 ++ flat_map (fun p => [fst p; snd p]) l).
  assert (HFS : forall x y, In (x, y) l -> In x S /\ In y S).
  { intros x y Hxy; split; right; apply in_or_app; right; apply in_or_app; right; apply in_flat_map; exists (x, y);
      (split; [exact Hxy|cbn; tauto]). }
  destruct (distinct_interp l S HFS lenv HF) as [le [HFl0 Hinj]].
  pose proof (order_of_ok le l HFl0) as HFl; set (F := order_of l) in *.
  assert (Hl1 : incl (alabs e1) S) by (intros x Hx; right; apply in_or_app; left; exact Hx).
  assert (Hl2 : incl (alabs e2) S) by (intros x Hx; right; apply in_or_app; right; apply in_or_app; left; exact Hx).
  assert (H1 : wnf le S N false w1) by (apply (tnorm_normal le S F ntm N e1 w1 HFl (or_introl eq_refl) Hl1); [unfold N; lia|exact E1]).
  assert (H2 : wnf le S N false w2) by (apply (tnorm_normal le S F ntm N e2 w2 HFl (or_introl eq_refl) Hl2); [unfold N; lia|exact E2]).
  set (nt := Nat.max ntm (Nat.max (wmax w1) (wmax w2))).
  assert (Hnt : ntm <= List.length (tenvT nt)) by (unfold tenvT; rewrite length_map, length_seq; lia).
  apply (nf_unique le S N Hinj w1 w2 H1 H2), (adequacy le nt w1 w2).
  - apply (proj2 (proj2 (proj2 (normal_ok le S N nt))) w1 false H1); lia.
  - apply (proj2 (proj2 (proj2 (normal_ok le S N nt))) w2 false H2); lia.
  - intros aenv penv.
    rewrite (proj2 (tnorm_sound le (tenvT nt) aenv penv F HFl ntm Hnt e1 w1 E1)).
    rewrite (proj2 (tnorm_sound le (tenvT nt) aenv penv F HFl ntm Hnt e2 w2 E2)).
    apply Heq; assumption.
Qed.

(** The decision: when both sides have a word whose tree it builds, it
    answers [true] for expressions that mean the same. *)
Theorem nf_eq_t_complete lenv l ntm e1 e2 l1 l2 :
  lfacts_ok lenv l ->
  (forall lenv' (T : Type) (tenv : list T) aenv penv, lfacts_ok lenv' l -> ntm <= List.length tenv ->
     aeden lenv' tenv aenv penv e1 = aeden lenv' tenv aenv penv e2) ->
  lnorm (order_of l) ntm e1 = Some l1 -> lnorm (order_of l) ntm e2 = Some l2 ->
  expand_c (order_of l) ntm cap l1 <> None -> expand_c (order_of l) ntm cap l2 <> None ->
  nf_eq_t (order_of l) ntm e1 e2 = true.
Proof.
  intros HF Heq E1 E2 X1 X2; unfold nf_eq_t; rewrite E1, E2.
  destruct (match canon (order_of l) ntm l1, canon (order_of l) ntm l2 with
            | Some c1, Some c2 => lword_eqb c1 c2 | _, _ => false end); [reflexivity|].
  destruct (expand_c (order_of l) ntm cap l1) as [w1|] eqn:Ew1; [|contradiction].
  destruct (expand_c (order_of l) ntm cap l2) as [w2|] eqn:Ew2; [|contradiction].
  apply expand_c_some in Ew1, Ew2.
  assert (T1 : tnorm (order_of l) ntm e1 = Some w1) by (unfold tnorm; rewrite E1; exact Ew1).
  assert (T2 : tnorm (order_of l) ntm e2 = Some w2) by (unfold tnorm; rewrite E2; exact Ew2).
  rewrite (tnorm_complete lenv l ntm e1 e2 w1 w2 HF Heq T1 T2); apply (proj2 (proj2 (proj2 nf_eqb_refl))).
Qed.
