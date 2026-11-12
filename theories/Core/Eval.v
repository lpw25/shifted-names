(** * Evaluation and display from the shared normal form

    What [names] reads off a normal form, from the stored word of
    [Shared]: the variable an adjustment sends a variable to
    ([apply_result_s]), and a check that it sends one to a term with a
    given payload ([apply_bind_check_s]).  Neither unfolds anything: a
    variable is the same in the stored word and in its unfolding, and
    two payloads are compared as atoms of one table.

    For display, the stored word is unfolded on demand, and only when the
    result is small ([anorm_show]): the tree can be exponentially larger
    than the stored word.  Display is not verified; what [names] shows is
    proved equal to what it started from by the decision. *)

From Stdlib Require Import Arith List Lia Bool NArith.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Unique Normal Complete Shared.
Import ListNotations.

(** ** Evaluation *)

Definition apply_result_s (F : list (lexp * lexp)) (ntm : nat) (e : aexp) (h : lexp) (i : nat) : option (lexp * nat) :=
  match anorm_s (apmax e) F ntm e (mk_sst [] []) with
  | Some (_, w) => match wtgt F w h i with Some (NVar h' j) => Some (h', j) | _ => None end
  | None => None
  end.

(** A variable sent to a term, checked against the reified adjustment
    [eb] its payload was shown as: [u] with the payload [eb] is the same
    stored term. *)
Definition apply_bind_check_s (F : list (lexp * lexp)) (ntm : nat) (e : aexp) (h : lexp) (i : nat) (eb : aexp) : option nat :=
  let N := Nat.max (apmax e) (apmax eb) in
  match anorm_s N F ntm e (mk_sst [] []) with
  | Some (st1, w) =>
      match wtgt F w h i with
      | Some (NBind u p b) =>
          match tnorm_s N F ntm (TBindE u (PComp eb PId)) st1 with
          | Some (_, t') => if ntgt_eqb (NBind u p b) t' then Some u else None
          | None => None
          end
      | _ => None
      end
  | None => None
  end.

(** ** Materialised payloads

    Two adjustments that are the same except that, where the first sends
    a variable to a term [u⟨w⟩], the second sends it to a term atom [k]
    with the identity payload adjustment, where [k] is [u] with the
    payload adjustment applied ([facts]: [(k, u, eb)], [eb] the reified
    adjustment the payload was shown as).  Both are normalised in one
    table, and so is [u] with the payload [eb] for each fact: the first
    adjustment must have that stored term where the second has [k]. *)

Fixpoint fpmax (facts : list (nat * nat * aexp)) : nat :=
  match facts with [] => 0 | (_, _, eb) :: r => Nat.max (apmax eb) (fpmax r) end.

Fixpoint nfacts (N : nat) (F : list (lexp * lexp)) (ntm : nat) (facts : list (nat * nat * aexp)) (st : sst)
  : option (sst * list (nat * ntgt)) :=
  match facts with
  | [] => Some (st, [])
  | (k, u, eb) :: r =>
      match tnorm_s N F ntm (TBindE u (PComp eb PId)) st with
      | Some (st1, tk) =>
          match nfacts N F ntm r st1 with Some (st2, l) => Some (st2, (k, tk) :: l) | None => None end
      | None => None
      end
  end.

Fixpoint nfind (l : list (nat * ntgt)) (k : nat) : option ntgt :=
  match l with [] => None | (k', t) :: r => if Nat.eqb k k' then Some t else nfind r k end.

Definition tmat_s (ntm : nat) (l : list (nat * ntgt)) (t t' : ntgt) : bool :=
  ntgt_eqb t t'
  || match t' with
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

Definition mat_eqb_s (F : list (lexp * lexp)) (ntm : nat) (facts : list (nat * nat * aexp)) (e e' : aexp) : bool :=
  let N := Nat.max (apmax e) (Nat.max (apmax e') (fpmax facts)) in
  match anorm_s N F ntm e (mk_sst [] []) with
  | Some (st1, WEnd S1) =>
      match anorm_s N F ntm e' st1 with
      | Some (st2, WEnd S2) =>
          match nfacts N F ntm facts st2 with
          | Some (_, l) => smat_s ntm l S1 S2
          | None => false
          end
      | _ => false
      end
  | _ => false
  end.

Section Sound.

Context {T : Type}.
Variable lenv : list label.
Variable tenv : list T.
Variable aenv : list (radj T).
Variable penv : list (rpadj T).
Variable F : list (lexp * lexp).
Hypothesis HF : facts_ok lenv F.
Variable ntm : nat.
Hypothesis Hntm : ntm <= List.length tenv.

Local Notation aeden := (aeden lenv tenv aenv).
Local Notation wden := (wden lenv tenv aenv).
Local Notation tden := (tden lenv tenv aenv).
Local Notation lden := (lden lenv).

Theorem apply_result_s_sound e h i h' j :
  apply_result_s F ntm e h i = Some (h', j) ->
  rapply (aeden penv e) (mk_rvar (lden h) i) = inl (mk_rvar (lden h') j).
Proof.
  unfold apply_result_s; destruct (anorm_s (apmax e) F ntm e (mk_sst [] [])) as [[st w]|] eqn:E; [|discriminate].
  destruct (wtgt F w h i) as [[h1 j1|]|] eqn:Et; try discriminate; intros H; injection H as <- <-.
  destruct (pad_spec (apmax e) penv) as [P [HP Hag]].
  pose proof (proj1 (scope_max (apmax e)) e (le_n _)) as Sc.
  rewrite <- (proj1 (eden_agree lenv tenv aenv (apmax e) P penv Hag) e Sc).
  rewrite <- HP in E, Sc.
  assert (Hi0 : inv lenv tenv aenv P (alabs e) (mk_sst [] [])) by (split; [exact I|constructor]).
  destruct (proj1 (norm_s_spec lenv tenv aenv P (alabs e) F HF ntm Hntm) e (incl_refl _) Sc _ _ _ Hi0 E) as [_ [_ [Hw D]]].
  rewrite <- D, (proj2 (wtgt_sound lenv tenv aenv _ F HF ntm Hntm w h i _ (wnf_dist _ _ _ _ _ Hw) Et)); reflexivity.
Qed.

Theorem apply_bind_s_sound e h i eb u x :
  apply_bind_check_s F ntm e h i eb = Some u -> nth_error tenv u = Some x ->
  rapply (aeden penv e) (mk_rvar (lden h) i) = inr (x, rpcompose (aeden penv eb) rpidentity).
Proof.
  unfold apply_bind_check_s; set (N := Nat.max (apmax e) (apmax eb)).
  destruct (anorm_s N F ntm e (mk_sst [] [])) as [[st1 w]|] eqn:E; [|discriminate].
  destruct (wtgt F w h i) as [[|u0 p b]|] eqn:Et; try discriminate.
  destruct (tnorm_s N F ntm (TBindE u0 (PComp eb PId)) st1) as [[st2 t']|] eqn:Eb; [|discriminate].
  destruct (ntgt_eqb (NBind u0 p b) t') eqn:Eq; [|discriminate]; intros H; injection H as <-; intros Hx.
  apply (proj1 nf_eqb_eq) in Eq; subst t'.
  destruct (pad_spec N penv) as [P [HP Hag]].
  assert (S1 : ascope N e) by (apply (proj1 (scope_max N)); unfold N; lia).
  assert (S2 : ascope N eb) by (apply (proj1 (scope_max N)); unfold N; lia).
  rewrite <- (proj1 (eden_agree lenv tenv aenv N P penv Hag) e S1), <- (proj1 (eden_agree lenv tenv aenv N P penv Hag) eb S2).
  rewrite <- HP in E, Eb, S1, S2.
  set (labs := alabs e ++ alabs eb).
  assert (Hi0 : inv lenv tenv aenv P labs (mk_sst [] [])) by (split; [exact I|constructor]).
  assert (Hl1 : incl (alabs e) labs) by (intros y Hy; apply in_or_app; left; exact Hy).
  assert (Hl2 : incl (tlabs (TBindE u0 (PComp eb PId))) labs).
  { intros y Hy; apply in_or_app; right; change (In y (alabs eb ++ [])) in Hy; rewrite app_nil_r in Hy; exact Hy. }
  destruct (proj1 (norm_s_spec lenv tenv aenv P labs F HF ntm Hntm) e Hl1 S1 _ _ _ Hi0 E) as [Hi1 [_ [Hw D]]].
  destruct (proj1 (proj2 (norm_s_spec lenv tenv aenv P labs F HF ntm Hntm)) (TBindE u0 (PComp eb PId)) Hl2 (conj S2 I)
              _ _ _ Hi1 Eb) as [_ [Hx2 [_ Dt]]].
  rewrite <- D, <- (wden_up lenv tenv aenv P labs ntm Hntm _ _ _ _ Hx2 Hw).
  rewrite (proj2 (wtgt_sound lenv tenv aenv _ F HF ntm Hntm w h i _ (wnf_dist _ _ _ _ _ Hw) Et)), Dt.
  rewrite teden_bind, Hx; reflexivity.
Qed.

(** *** Materialised payloads *)

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

Lemma fpmax_in fs k u eb : In (k, u, eb) fs -> apmax eb <= fpmax fs.
Proof.
  induction fs as [|[[k' u'] eb'] r IH]; [intros []|]; cbn [fpmax]; intros [H|H]; [injection H as _ _ ->; lia|].
  pose proof (IH H); lia.
Qed.

Lemma mfind_in fs k u eb : mfind fs k = Some (u, eb) -> In (k, u, eb) fs.
Proof.
  induction fs as [|[[k' u'] eb'] r IH]; cbn [mfind]; [discriminate|].
  destruct (Nat.eqb_spec k k') as [->|_]; [intros H; injection H as -> ->; left; reflexivity|intros H; right; exact (IH H)].
Qed.

(** The stored term of each fact means [u] with the payload [eb], in
    every later table. *)
Lemma nfacts_spec (P : list (rpadj T)) labs fs : forall st st' l,
  (forall k u eb, In (k, u, eb) fs -> incl (alabs eb) labs /\ ascope (List.length P) eb) ->
  inv lenv tenv aenv P labs st -> nfacts (List.length P) F ntm fs st = Some (st', l) ->
  inv lenv tenv aenv P labs st' /\ extends (sdefs st) (sdefs st')
  /\ forall k tk, nfind l k = Some tk ->
       exists u eb y, mfind fs k = Some (u, eb) /\ nth_error tenv u = Some y
         /\ forall ds, extends (sdefs st') ds ->
              tden (ext lenv tenv aenv P ds) tk = RBind y (rpcompose (aeden P eb) rpidentity).
Proof.
  induction fs as [|[[k0 u0] eb0] r IH]; intros st st' l Hfs Hi; cbn [nfacts].
  { intros H; injection H as <- <-; refine (conj Hi (conj (extends_refl _) _)); intros k tk H; discriminate H. }
  destruct (tnorm_s (List.length P) F ntm (TBindE u0 (PComp eb0 PId)) st) as [[st1 t0]|] eqn:E0; [|discriminate].
  destruct (nfacts (List.length P) F ntm r st1) as [[st2 l']|] eqn:Er; [|discriminate]; intros H; injection H as <- <-.
  destruct (Hfs k0 u0 eb0 (or_introl eq_refl)) as [Hl0 Hs0].
  assert (Hu : u0 < ntm).
  { rewrite tnorm_s_bind in E0; destruct (Nat.ltb_spec u0 ntm) as [Hu|]; [exact Hu|discriminate]. }
  destruct (nth_error tenv u0) as [y0|] eqn:Ey; [|apply nth_error_None in Ey; lia].
  assert (Hl0' : incl (tlabs (TBindE u0 (PComp eb0 PId))) labs).
  { intros y Hy; change (In y (alabs eb0 ++ [])) in Hy; rewrite app_nil_r in Hy; exact (Hl0 y Hy). }
  destruct (proj1 (proj2 (norm_s_spec lenv tenv aenv P labs F HF ntm Hntm)) (TBindE u0 (PComp eb0 PId)) Hl0' (conj Hs0 I)
              _ _ _ Hi E0) as [Hi1 [Hx1 [Ht0 Dt]]].
  destruct (IH st1 st2 l' (fun k u eb H => Hfs k u eb (or_intror H)) Hi1 Er) as [Hi2 [Hx2 Hfind]].
  refine (conj Hi2 (conj (extends_trans _ _ _ Hx1 Hx2) _)); intros k tk; cbn [nfind mfind].
  destruct (Nat.eqb_spec k k0) as [->|_].
  - intros H; injection H as <-; exists u0, eb0, y0; refine (conj eq_refl (conj Ey _)); intros ds Hds.
    rewrite (tden_up lenv tenv aenv P labs ntm Hntm _ _ _ (extends_trans _ _ _ Hx2 Hds) Ht0), Dt, teden_bind, Ey.
    reflexivity.
  - intros H; destruct (Hfind k tk H) as [u [eb [y [A [B C]]]]]; exists u, eb, y; exact (conj A (conj B C)).
Qed.

Section Mat.

Variable g : rpadj T -> T -> T.
Variable facts : list (nat * nat * aexp).
Hypothesis Hfacts : Forall (fun f => let '(k, u, eb) := f in
  forall y, nth_error tenv u = Some y -> nth_error tenv k = Some (g (rpcompose (aeden penv eb) rpidentity) y)) facts.

Lemma tmat_s_sound (P3 : list (rpadj T)) l t t' :
  (forall k tk, nfind l k = Some tk ->
     exists u eb y, mfind facts k = Some (u, eb) /\ nth_error tenv u = Some y
       /\ tden P3 tk = RBind y (rpcompose (aeden penv eb) rpidentity)) ->
  tmat_s ntm l t t' = true -> mrel g (rtarget_result (tden P3 t)) (rtarget_result (tden P3 t')).
Proof.
  intros Hfind; unfold tmat_s; destruct (ntgt_eqb t t') eqn:E; cbn [orb].
  { intros _; left; apply (proj1 nf_eqb_eq) in E; subst; reflexivity. }
  destruct t' as [|k [[|]|] [b'|]]; try discriminate.
  destruct (nfind l k) as [tk|] eqn:Ef; [|discriminate]; intros H; apply andb_true_iff in H as [H1 H2].
  apply (proj1 nf_eqb_eq) in H1; subst tk.
  destruct (Hfind k t Ef) as [u [eb [y [Em [Ey Dt]]]]].
  right; exists y, (rpcompose (aeden penv eb) rpidentity); rewrite Dt; split; [reflexivity|].
  rewrite (tden_bind lenv tenv aenv P3 _ _ _ _ (mfind_fact lenv tenv aenv penv g facts Hfacts _ _ _ _ Em Ey)).
  cbn [rtarget_result]; do 2 f_equal; exact (rpcompose_identity _).
Qed.

Theorem mat_s_sound e e' :
  mat_eqb_s F ntm facts e e' = true -> forall v, mrel g (rapply (aeden penv e) v) (rapply (aeden penv e') v).
Proof.
  unfold mat_eqb_s; set (N := Nat.max (apmax e) (Nat.max (apmax e') (fpmax facts))).
  destruct (anorm_s N F ntm e (mk_sst [] [])) as [[st1 [S1|]]|] eqn:E1; try discriminate.
  destruct (anorm_s N F ntm e' st1) as [[st2 [S2|]]|] eqn:E2; try discriminate.
  destruct (nfacts N F ntm facts st2) as [[st3 l]|] eqn:E3; [|discriminate]; intros Hm.
  destruct (pad_spec N penv) as [P [HP Hag]].
  assert (Sc1 : ascope N e) by (apply (proj1 (scope_max N)); unfold N; lia).
  assert (Sc2 : ascope N e') by (apply (proj1 (scope_max N)); unfold N; lia).
  assert (Scf : forall k u eb, In (k, u, eb) facts -> ascope N eb).
  { intros k u eb H; apply (proj1 (scope_max N)); pose proof (fpmax_in _ _ _ _ H); unfold N; lia. }
  rewrite <- (proj1 (eden_agree lenv tenv aenv N P penv Hag) e Sc1), <- (proj1 (eden_agree lenv tenv aenv N P penv Hag) e' Sc2).
  set (labs := alabs e ++ alabs e' ++ flat_map (fun f => alabs (snd f)) facts).
  assert (Hl1 : incl (alabs e) labs) by (intros y Hy; apply in_or_app; left; exact Hy).
  assert (Hl2 : incl (alabs e') labs) by (intros y Hy; apply in_or_app; right; apply in_or_app; left; exact Hy).
  assert (Hfs : forall k u eb, In (k, u, eb) facts -> incl (alabs eb) labs /\ ascope (List.length P) eb).
  { intros k u eb H; split; [|rewrite HP; exact (Scf k u eb H)].
    intros y Hy; apply in_or_app; right; apply in_or_app; right; apply in_flat_map; exists (k, u, eb); exact (conj H Hy). }
  assert (Hi0 : inv lenv tenv aenv P labs (mk_sst [] [])) by (split; [exact I|constructor]).
  pose proof Sc1 as Sc1'; pose proof Sc2 as Sc2'; rewrite <- HP in E1, E2, E3, Sc1', Sc2'.
  destruct (proj1 (norm_s_spec lenv tenv aenv P labs F HF ntm Hntm) e Hl1 Sc1' _ _ _ Hi0 E1) as [Hi1 [_ [Hw1 D1]]].
  destruct (proj1 (norm_s_spec lenv tenv aenv P labs F HF ntm Hntm) e' Hl2 Sc2' _ _ _ Hi1 E2) as [Hi2 [Hx2 [Hw2 D2]]].
  destruct (nfacts_spec P labs facts st2 st3 l Hfs Hi2 E3) as [Hi3 [Hx3 Hfind]].
  set (P3 := ext lenv tenv aenv P (sdefs st3)).
  assert (D1' : wden P3 (WEnd S1) = aeden P e).
  { unfold P3; rewrite (wden_up lenv tenv aenv P labs ntm Hntm _ _ _ _ (extends_trans _ _ _ Hx2 Hx3) Hw1); exact D1. }
  assert (D2' : wden P3 (WEnd S2) = aeden P e').
  { unfold P3; rewrite (wden_up lenv tenv aenv P labs ntm Hntm _ _ _ _ Hx3 Hw2); exact D2. }
  assert (Hfind' : forall k tk, nfind l k = Some tk ->
            exists u eb y, mfind facts k = Some (u, eb) /\ nth_error tenv u = Some y
              /\ tden P3 tk = RBind y (rpcompose (aeden penv eb) rpidentity)).
  { intros k tk H; destruct (Hfind k tk H) as [u [eb [y [A [B C]]]]]; exists u, eb, y; refine (conj A (conj B _)).
    unfold P3; rewrite (C _ (extends_refl _)).
    rewrite (proj1 (eden_agree lenv tenv aenv N P penv Hag) eb (Scf k u eb (mfind_in _ _ _ _ A))); reflexivity. }
  rewrite <- D1', <- D2', !wden_end.
  pose proof (wnf_dist _ _ _ _ _ Hw1) as HD; pose proof (wnf_dist _ _ _ _ _ Hw2) as HD'.
  pose proof (sdistd_sdist lenv _ HD) as Hd; pose proof (sdistd_sdist lenv _ HD') as Hd'; intros [lab j].
  rewrite !rapply_sden by assumption.
  cbn [v_label v_index]; pose proof (smat_s_get _ _ _ lab Hm) as Hg.
  destruct (sget lenv lab S1) as [[ts m]|] eqn:Eg, (sget lenv lab S2) as [[ts' m']|]; try contradiction; [|left; reflexivity].
  destruct Hg as [Ht <-]; cbn [esem]; rewrite <- (tlmat_s_len _ _ _ Ht).
  destruct (j <? tlen ts) eqn:Ej; [|left; reflexivity].
  apply (tmat_s_sound P3 l _ _ Hfind'), tlmat_s_nth; [exact Ht|apply Nat.ltb_lt, Ej].
Qed.

End Mat.

End Sound.

(** ** Unfolding for display *)

Section Show.

Variable np : nat.

Section One.

Variable rec : word -> word.
Variable ds : list pdef.

Definition unfd_t (t : ntgt) : ntgt :=
  match t with
  | NBind u p (Some β) =>
      if β <? np then t else match dget ds (β - np) with Some (w, b) => NBind u (rec w) b | None => t end
  | _ => t
  end.

Fixpoint unfd_ts (ts : tlist) : tlist :=
  match ts with TNil => TNil | TCons t r => TCons (unfd_t t) (unfd_ts r) end.

Fixpoint unfd_s (s : seg) : seg :=
  match s with SNil => SNil | SEnt h ts m r => SEnt h (unfd_ts ts) m (unfd_s r) end.

Definition unfd_w (w : word) : word :=
  match w with WEnd s => WEnd (unfd_s s) | WAtom s L a w' => WAtom (unfd_s s) L a w' end.

End One.

(** Only the definitions the word refers to are unfolded. *)
Fixpoint unfd (fuel : nat) (ds : list pdef) (w : word) : word :=
  match fuel with 0 => w | S f => unfd_w (unfd f ds) ds w end.

(** The size of the unfolding, without unfolding. *)
Definition dsz (zs : list N) (k : nat) : N := nth (List.length zs - 1 - k) zs 0%N.

Definition tsz_u (zs : list N) (t : ntgt) : N :=
  match t with
  | NBind _ _ (Some β) => if β <? np then 1%N else (1 + dsz zs (β - np))%N
  | _ => 1%N
  end.

Fixpoint tlsz_u (zs : list N) (ts : tlist) : N :=
  match ts with TNil => 0%N | TCons t r => (tsz_u zs t + tlsz_u zs r)%N end.

Fixpoint ssz_u (zs : list N) (s : seg) : N :=
  match s with SNil => 0%N | SEnt _ ts _ r => (1 + tlsz_u zs ts + ssz_u zs r)%N end.

Fixpoint wsz_r (w : word) : N :=
  match w with WEnd s => (1 + ssz_u [] s)%N | WAtom s _ _ w' => (1 + ssz_u [] s + wsz_r w')%N end.

Definition wsz_u (zs : list N) (w : word) : N :=
  match w with WEnd s => (1 + ssz_u zs s)%N | WAtom s _ _ w' => (1 + ssz_u zs s + wsz_r w')%N end.

Fixpoint usz (ds : list pdef) : list N :=
  match ds with
  | [] => []
  | (w, _) :: r => let zs := usz r in wsz_u zs w :: zs
  end.

Definition unfold_small (budget : N) (ds : list pdef) (w : word) : option word :=
  if (wsz_u (usz ds) w <=? budget)%N then Some (unfd (List.length ds) ds w) else None.

End Show.

(** Larger normal forms are not shown: a chain of substitutions doubles
    with each step. *)
Definition show_budget : N := 250%N.

(** The normal form as a tree, when it is small enough to show. *)
Inductive shown : Type :=
| ShNone
| ShLarge
| ShWord (w : word).

Definition anorm_show (F : list (lexp * lexp)) (ntm : nat) (e : aexp) : shown :=
  match anorm_s (apmax e) F ntm e (mk_sst [] []) with
  | Some (st, w) =>
      match unfold_small (apmax e) show_budget (sdefs st) w with Some w' => ShWord w' | None => ShLarge end
  | None => ShNone
  end.

(** A variable sent to a term whose payload ends with the identity: the
    term and the payload word, for [names] to show the word. *)
Definition apply_payload_s (F : list (lexp * lexp)) (ntm : nat) (e : aexp) (h : lexp) (i : nat) : option (nat * word) :=
  match anorm_s (apmax e) F ntm e (mk_sst [] []) with
  | Some (st, w) =>
      match wtgt F w h i with
      | Some (NBind u p None) => Some (u, p)
      | Some (NBind u _ (Some β)) =>
          if β <? apmax e then None
          else match dget (sdefs st) (β - apmax e) with
               | Some (w0, None) =>
                   match unfold_small (apmax e) show_budget (sdefs st) w0 with
                   | Some wp => Some (u, wp)
                   | None => None
                   end
               | _ => None
               end
      | _ => None
      end
  | None => None
  end.
