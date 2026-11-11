(** * Uniqueness of normal forms

    Normal forms that mean the same are the same.  This file builds the
    proof in stages (see [docs/normal-forms.md]): first segments whose
    targets are variables. *)

From Stdlib Require Import Arith List Lia Bool Sorted.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise.
Import ListNotations.

Section Unique.

Context {T : Type}.
Variable lenv : list label.
Variable tenv : list T.
Variable aenv : list (radj T).
Variable penv : list (rpadj T).

Local Notation lden := (lden lenv).
Local Notation tden := (tden lenv tenv aenv penv).
Local Notation sden := (sden lenv tenv aenv penv).
Local Notation sget := (sget lenv).
Local Notation esem := (esem lenv tenv aenv penv).
Local Notation lsem := (lsem lenv tenv aenv penv).

(** ** Entries *)

(** The label expressions in play denote distinct labels. *)
Variable labs : list lexp.
Hypothesis Hinj : forall h h', In h labs -> In h' labs -> lden h = lden h' -> h = h'.

Definition ren_target (t : ntgt) : Prop := match t with NVar h _ => In h labs | NBind _ _ _ => False end.

(** An entry of [h] is trimmed: its last target is not the transparent
    [h₍ₘ₋₁₎]. *)
Definition trimmed (h : lexp) (xs : list ntgt) (m : nat) : Prop :=
  match last xs (NVar LNone 0), xs, m with
  | _, [], _ => True
  | NVar h' j, _, S m' => ~ (h' = h /\ j = m')
  | _, _, _ => True
  end.

Lemma lsem_var l xs m j h i :
  j < List.length xs -> nth j xs (NVar LNone 0) = NVar h i -> lsem l xs m j = inl (mk_rvar (lden h) i).
Proof. intros Hj E; unfold lsem; rewrite (proj2 (Nat.ltb_lt _ _) Hj), E; reflexivity. Qed.

Lemma lsem_tail l xs m j : List.length xs <= j -> lsem l xs m j = inl (mk_rvar l (j - List.length xs + m)).
Proof. intros Hj; unfold lsem; destruct (Nat.ltb_spec j (List.length xs)); [lia|reflexivity]. Qed.

Lemma ren_nth xs j : Forall ren_target xs -> j < List.length xs ->
  exists h i, nth j xs (NVar LNone 0) = NVar h i /\ In h labs.
Proof.
  intros Hr Hj; pose proof (proj1 (Forall_forall _ _) Hr (nth j xs (NVar LNone 0)) (nth_In _ _ Hj)) as H.
  destruct (nth j xs (NVar LNone 0)) as [h i|]; [exists h, i; split; [reflexivity|exact H]|contradiction].
Qed.

Lemma trimmed_last h xs m x :
  trimmed h (xs ++ [x]) m -> forall h' j, x = NVar h' j -> m = S j -> h' <> h.
Proof.
  unfold trimmed; rewrite last_last; intros Ht h' j -> -> E; subst h'.
  destruct (xs ++ _) eqn:Ex; [destruct xs; discriminate|]; apply Ht; split; reflexivity.
Qed.

(** One entry against a longer one: the longer one would be transparent at
    its end. *)
Lemma lsem_short h xs m ys m' :
  In h labs -> Forall ren_target ys -> trimmed h ys m' ->
  List.length xs < List.length ys ->
  (forall j, lsem (lden h) xs m j = lsem (lden h) ys m' j) -> False.
Proof.
  intros Hh Hr Ht Hlt Heq.
  destruct (@exists_last _ ys) as [ys0 [x Ey]]; [destruct ys; cbn in Hlt; [lia|discriminate]|].
  subst ys; rewrite length_app in Hlt; cbn in Hlt.
  set (n := List.length ys0) in *.
  pose proof (Heq n) as E1; pose proof (Heq (n + 1)) as E2.
  rewrite lsem_tail in E1 by lia; rewrite lsem_tail in E2 by lia.
  rewrite (lsem_tail _ (ys0 ++ [x])) in E2 by (rewrite length_app; cbn; lia).
  assert (Hx : nth n (ys0 ++ [x]) (NVar LNone 0) = x) by (rewrite app_nth2 by (unfold n; lia); unfold n; rewrite Nat.sub_diag; reflexivity).
  destruct (ren_nth (ys0 ++ [x]) n Hr) as [h' [i [Ex Hh']]]; [rewrite length_app; cbn; lia|].
  rewrite (lsem_var _ _ _ _ h' i) in E1 by (try (rewrite length_app; cbn; lia); exact Ex).
  rewrite Hx in Ex; subst x.
  injection E1 as E1a E1b; injection E2 as E2b.
  rewrite length_app in E2b; cbn [Datatypes.length] in E2b.
  apply (trimmed_last h ys0 m' (NVar h' i) Ht h' i eq_refl); [unfold n in *; lia|].
  apply Hinj; [exact Hh'|exact Hh|symmetry; exact E1a].
Qed.

Theorem lsem_unique h xs m ys m' :
  In h labs -> Forall ren_target xs -> Forall ren_target ys -> trimmed h xs m -> trimmed h ys m' ->
  (forall j, lsem (lden h) xs m j = lsem (lden h) ys m' j) -> xs = ys /\ m = m'.
Proof.
  intros Hh Hrx Hry Htx Hty Heq.
  destruct (Nat.lt_trichotomy (List.length xs) (List.length ys)) as [Hlt|[Hle|Hlt]].
  - exfalso; exact (lsem_short h xs m ys m' Hh Hry Hty Hlt Heq).
  - split.
    + apply (nth_ext _ _ (NVar LNone 0) (NVar LNone 0) Hle); intros j Hj.
      destruct (ren_nth xs j Hrx Hj) as [h1 [i1 [E1 H1]]].
      destruct (ren_nth ys j Hry ltac:(lia)) as [h2 [i2 [E2 H2]]].
      pose proof (Heq j) as E; rewrite (lsem_var _ _ _ _ _ _ Hj E1), (lsem_var _ _ _ _ h2 i2) in E by (lia || exact E2).
      injection E as Eh Ei; rewrite E1, E2, (Hinj _ _ H1 H2 Eh), Ei; reflexivity.
    + pose proof (Heq (List.length xs)) as E; rewrite !lsem_tail in E by lia.
      injection E as E; lia.
  - exfalso; exact (lsem_short h ys m' xs m Hh Hrx Htx Hlt (fun j => eq_sym (Heq j))).
Qed.

(** A trimmed entry that is not empty is not the identity. *)
Lemma lsem_not_id h xs m :
  In h labs -> Forall ren_target xs -> trimmed h xs m -> (xs <> [] \/ m <> 0) ->
  ~ (forall j, lsem (lden h) xs m j = inl (mk_rvar (lden h) j)).
Proof.
  intros Hh Hr Ht Hne Heq.
  assert (Hid : forall j, lsem (lden h) xs m j = lsem (lden h) [] 0 j)
    by (intros j; rewrite Heq; unfold lsem; cbn; f_equal; f_equal; lia).
  destruct xs as [|x xs].
  - destruct Hne as [Hne|Hne]; [congruence|]; pose proof (Hid 0) as E; unfold lsem in E; cbn in E.
    injection E; lia.
  - exact (lsem_short h [] 0 (x :: xs) m Hh Hr Ht ltac:(cbn; lia) (fun j => eq_sym (Hid j))).
Qed.

(** ** Segments whose targets are variables *)

Fixpoint sents (s : seg) : list (lexp * list ntgt * nat) :=
  match s with SNil => [] | SEnt h ts m r => (h, tl_list ts, m) :: sents r end.

Definition ekey (e : lexp * list ntgt * nat) : option label := let '(h, _, _) := e in lden h.

Definition entry_ok (e : lexp * list ntgt * nat) : Prop :=
  let '(h, xs, m) := e in In h labs /\ Forall ren_target xs /\ trimmed h xs m /\ (xs <> [] \/ m <> 0).

Definition seg_ok (s : seg) : Prop :=
  StronglySorted (fun e e' => olabel_lt (ekey e) (ekey e')) (sents s) /\ Forall entry_ok (sents s).

Lemma sget_in l s ts m : sget l s = Some (ts, m) -> exists h, In (h, tl_list ts, m) (sents s) /\ lden h = l.
Proof.
  induction s as [|h ts' m' r IH] using seg_spine; cbn [sget sents]; [discriminate|].
  destruct (label_eqb_spec (lden h) l) as [E|_].
  - intros H; injection H as <- <-; exists h; split; [left; reflexivity|exact E].
  - intros H; destruct (IH H) as [h0 [Hi E]]; exists h0; split; [right; exact Hi|exact E].
Qed.

Lemma sget_above l s : (forall e, In e (sents s) -> olabel_lt l (ekey e)) -> sget l s = None.
Proof.
  induction s as [|h ts m r IH] using seg_spine; cbn [sget sents]; [reflexivity|]; intros H.
  destruct (label_eqb_spec (lden h) l) as [E|_].
  - exfalso; apply (olabel_lt_irrefl l); pose proof (H _ (or_introl eq_refl)) as Hl; cbn in Hl; rewrite E in Hl; exact Hl.
  - apply IH; intros e He; apply H; right; exact He.
Qed.

Lemma entry_not_id h xs m l : entry_ok (h, xs, m) -> lden h = l ->
  ~ (forall j, esem l (Some (tl_of xs, m)) j = esem l None j).
Proof.
  intros [Hh [Hr [Ht Hne]]] <- Heq; apply (lsem_not_id h xs m Hh Hr Ht Hne); intros j.
  pose proof (Heq j) as E; rewrite esem_lsem, tl_list_of in E; exact E.
Qed.

Theorem seg_unique s s' : seg_ok s -> seg_ok s' ->
  (forall l j, esem l (sget l s) j = esem l (sget l s') j) -> s = s'.
Proof.
  revert s'; induction s as [|h ts m r IH] using seg_spine; intros s' [Hs Ho] [Hs' Ho'] Heq;
    destruct s' as [|h' ts' m' r']; [reflexivity| | |].
  - exfalso; inversion Ho' as [|e l He]; subst.
    apply (entry_not_id h' (tl_list ts') m' (lden h') He eq_refl); intros j.
    rewrite tl_of_list; pose proof (Heq (lden h') j) as E; cbn [sget] in E; rewrite label_eqb_refl in E; symmetry; exact E.
  - exfalso; inversion Ho as [|e l He]; subst.
    apply (entry_not_id h (tl_list ts) m (lden h) He eq_refl); intros j.
    rewrite tl_of_list; pose proof (Heq (lden h) j) as E; cbn [sget] in E; rewrite label_eqb_refl in E; exact E.
  - cbn [sents] in *; inversion Hs as [|e l Hsr Hall]; inversion Hs' as [|e' l' Hsr' Hall']; subst.
    inversion Ho as [|e l He Hor]; inversion Ho' as [|e' l' He' Hor']; subst.
    rewrite Forall_forall in Hall, Hall'.
    destruct (olabel_trichotomy (lden h) (lden h')) as [Hlt|[Eh|Hlt]].
    + exfalso; apply (entry_not_id h (tl_list ts) m (lden h) He eq_refl); intros j.
      rewrite tl_of_list; pose proof (Heq (lden h) j) as E; cbn [sget] in E; rewrite label_eqb_refl in E; rewrite E.
      destruct (label_eqb_spec (lden h') (lden h)) as [E'|_]; [rewrite E' in Hlt; destruct (olabel_lt_irrefl _ Hlt)|].
      rewrite sget_above; [reflexivity|]; intros e0 Hi; exact (olabel_lt_trans _ _ _ Hlt (Hall' e0 Hi)).
    + destruct He as [Hh [Hr [Ht _]]]; destruct He' as [Hh' [Hr' [Ht' _]]].
      assert (Ehh : h = h') by (apply Hinj; assumption); subst h'.
      assert (Ee : tl_list ts = tl_list ts' /\ m = m').
      { apply (lsem_unique h _ _ _ _ Hh Hr Hr' Ht Ht'); intros j.
        rewrite <- !esem_lsem; pose proof (Heq (lden h) j) as E; cbn [sget] in E; rewrite label_eqb_refl in E; exact E. }
      destruct Ee as [Et <-]; rewrite <- (tl_of_list ts), <- (tl_of_list ts'), Et; f_equal.
      apply IH; [split; assumption|split; assumption|]; intros l j.
      pose proof (Heq l j) as E; cbn [sget] in E.
      destruct (label_eqb_spec (lden h) l) as [<-|_]; [|exact E].
      rewrite !sget_above; [reflexivity| |]; intros e0 Hi; [apply Hall'|apply Hall]; exact Hi.
    + exfalso; apply (entry_not_id h' (tl_list ts') m' (lden h') He' eq_refl); intros j.
      rewrite tl_of_list; pose proof (Heq (lden h') j) as E; cbn [sget] in E; rewrite label_eqb_refl in E; rewrite <- E.
      destruct (label_eqb_spec (lden h) (lden h')) as [E'|_]; [rewrite E' in Hlt; destruct (olabel_lt_irrefl _ Hlt)|].
      rewrite sget_above; [reflexivity|]; intros e0 Hi; exact (olabel_lt_trans _ _ _ Hlt (Hall e0 Hi)).
Qed.

End Unique.

(** ** The free model

    Applying a word to a variable in the free model gives a variable, a
    term with what happens to its names afterwards, or an atom stuck at a
    variable with what happens to the atom's outputs afterwards.  Words
    equal in the free model are equal under every interpretation. *)

Inductive fres : Type :=
| FVar (v : rvar)
| FTerm (u : nat) (b : option nat) (k : rvar -> fres)
| FStuck (a : nat) (z : rvar) (k : rvar -> fres).

Section Free.

Variable lenv : list label.
Local Notation lden := (lden lenv).

Definition shiftL (L : list (lexp * nat)) (y : rvar) : rvar :=
  mk_rvar (v_label y) (v_index y + lc lenv (v_label y) L).

(** A lifted atom applied to [x], then [K]. *)
Definition latom (L : list (lexp * nat)) (a : nat) (K : rvar -> fres) (x : rvar) : fres :=
  if v_index x <? lc lenv (v_label x) L then K x
  else FStuck a (mk_rvar (v_label x) (v_index x - lc lenv (v_label x) L)) (fun y => K (shiftL L y)).

Fixpoint fw (w : word) (K : rvar -> fres) (v : rvar) {struct w} : fres :=
  match w with
  | WEnd Sg => fs Sg K v
  | WAtom Sg L a w' => fw w' (latom L a (fun y => fs Sg K y)) v
  end
with fs (Sg : seg) (K : rvar -> fres) (v : rvar) {struct Sg} : fres :=
  match Sg with
  | SNil => K v
  | SEnt h ts m r => if label_eqb (lden h) (v_label v) then ftl ts (lden h) m K (v_index v) else fs r K v
  end
with ftl (ts : tlist) (l : option label) (m : nat) (K : rvar -> fres) (i : nat) {struct ts} : fres :=
  match ts with
  | TNil => K (mk_rvar l (i + m))
  | TCons t r => match i with 0 => ft t K | S i' => ftl r l m K i' end
  end
with ft (t : ntgt) (K : rvar -> fres) {struct t} : fres :=
  match t with
  | NVar h j => K (mk_rvar (lden h) j)
  | NBind u wp b => FTerm u b (fun x => fw wp K x)
  end.

(** Free results that agree; a term with the identity payload adjustment
    is compared on named variables only. *)
Fixpoint feq (f g : fres) : Prop :=
  match f, g with
  | FVar v, FVar v' => v = v'
  | FTerm u b k, FTerm u' b' k' =>
      u = u' /\ b = b' /\ forall y, (b = None -> v_label y <> None) -> feq (k y) (k' y)
  | FStuck a z k, FStuck a' z' k' => a = a' /\ z = z' /\ forall y, feq (k y) (k' y)
  | _, _ => False
  end.

Context {T : Type}.
Variable tenv : list T.
Variable aenv : list (radj T).
Variable penv : list (rpadj T).

Local Notation wden := (wden lenv tenv aenv penv).
Local Notation sden := (sden lenv tenv aenv penv).
Local Notation tden := (tden lenv tenv aenv penv).

(** The real results a free result stands for. *)
Fixpoint realises (f : fres) (r : rresult T) : Prop :=
  match f with
  | FVar v => r = inl v
  | FTerm u None k =>
      exists Kr x, nth_error tenv u = Some x /\ (forall y, v_label y <> None -> realises (k y) (rapply Kr y))
                   /\ r = inr (x, rpcompose Kr rpidentity)
  | FTerm u (Some n) k =>
      exists Kr x, nth_error tenv u = Some x /\ (forall y, realises (k y) (rapply Kr y))
                   /\ r = inr (x, rpcompose Kr (nth n penv rpidentity))
  | FStuck a z k =>
      exists Kr, (forall y, realises (k y) (rapply Kr y)) /\ r = cres Kr (rapply (aden aenv a) z)
  end.

Lemma realises_unique f : forall r1 r2, realises f r1 -> realises f r2 -> r1 = r2.
Proof.
  induction f as [v|u [n|] k IH|a z k IH]; cbn [realises]; intros r1 r2.
  - intros -> ->; reflexivity.
  - intros [K1 [x1 [E1 [H1 ->]]]] [K2 [x2 [E2 [H2 ->]]]]; rewrite E1 in E2; injection E2 as <-.
    assert (K1 = K2) as -> by (apply rextensionality; intros y; apply (IH y); [apply H1|apply H2]); reflexivity.
  - intros [K1 [x1 [E1 [H1 ->]]]] [K2 [x2 [E2 [H2 ->]]]]; rewrite E1 in E2; injection E2 as <-.
    do 2 f_equal; apply rpcompose_named; intros y Hy; apply (IH y); [apply H1, Hy|apply H2, Hy].
  - intros [K1 [H1 ->]] [K2 [H2 ->]].
    assert (K1 = K2) as -> by (apply rextensionality; intros y; apply (IH y); [apply H1|apply H2]); reflexivity.
Qed.

Lemma realises_feq f : forall g r, feq f g -> realises f r -> realises g r.
Proof.
  induction f as [v|u b k IH|a z k IH]; intros [v'|u' b' k'|a' z' k'] r; cbn [feq]; try contradiction.
  - intros <- H; exact H.
  - intros [<- [<- Hk]]; destruct b as [n|]; cbn [realises].
    + intros [Kr [x [E [H ->]]]]; exists Kr, x; split; [exact E|split; [|reflexivity]].
      intros y; apply (IH y); [apply Hk; discriminate|apply H].
    + intros [Kr [x [E [H ->]]]]; exists Kr, x; split; [exact E|split; [|reflexivity]].
      intros y Hy; apply (IH y); [apply Hk; intros _; exact Hy|apply H, Hy].
  - intros [<- [<- Hk]] [Kr [H ->]]; exists Kr; split; [|reflexivity].
    intros y; apply (IH y); [apply Hk|apply H].
Qed.

(** Well-formed words: segments with distinct labels, terms in range. *)
Fixpoint okt (t : ntgt) : Prop :=
  match t with NVar _ _ => True | NBind u wp _ => u < List.length tenv /\ okw wp end
with okts (ts : tlist) : Prop :=
  match ts with TNil => True | TCons t r => okt t /\ okts r end
with oks (s : seg) : Prop :=
  match s with SNil => True | SEnt h ts _ r => sget lenv (lden h) r = None /\ okts ts /\ oks r end
with okw (w : word) : Prop :=
  match w with WEnd s => oks s | WAtom s _ _ w => oks s /\ okw w end.

Lemma oks_sdist s : oks s -> sdist lenv s.
Proof. induction s as [|h ts m r IH] using seg_spine; cbn; [tauto|intros [H1 [_ H2]]; split; [exact H1|apply IH, H2]]. Qed.

Lemma esem_cons l t r m i :
  esem lenv tenv aenv penv l (Some (TCons t r, m)) (S i) = esem lenv tenv aenv penv l (Some (r, m)) i.
Proof.
  cbn [esem tlen tnth]; change (S i <? S (tlen r)) with (i <? tlen r).
  destruct (i <? tlen r); [reflexivity|do 2 f_equal; lia].
Qed.

Lemma fw_real :
  (forall t, okt t -> forall K Kr, (forall y, realises (K y) (rapply Kr y)) ->
     realises (ft t K) (cres Kr (rtarget_result (tden t))))
  /\ (forall ts, okts ts -> forall l m K Kr i, (forall y, realises (K y) (rapply Kr y)) ->
     realises (ftl ts l m K i) (cres Kr (esem lenv tenv aenv penv l (Some (ts, m)) i)))
  /\ (forall s, oks s -> forall K Kr v, (forall y, realises (K y) (rapply Kr y)) ->
     realises (fs s K v) (cres Kr (esem lenv tenv aenv penv (v_label v) (sget lenv (v_label v) s) (v_index v))))
  /\ (forall w, okw w -> forall K Kr v, (forall y, realises (K y) (rapply Kr y)) ->
     realises (fw w K v) (rapply (rcompose Kr (wden w)) v)).
Proof.
  apply nf_mind.
  - intros h j _ K Kr HK; cbn [ft tden rtarget_result cres]; apply HK.
  - intros u wp IH b [Hu Hok] K Kr HK; cbn [ft].
    destruct (nth_error tenv u) as [x|] eqn:Ex; [|apply nth_error_None in Ex; lia].
    rewrite (tden_bind lenv tenv aenv penv _ _ _ _ Ex); cbn [rtarget_result cres].
    destruct b as [n|]; cbn [realises bden]; exists (rcompose Kr (wden wp)), x; (split; [exact Ex|split]).
    + intros y; exact (IH Hok K Kr y HK).
    + rewrite rpcompose_compose; reflexivity.
    + intros y _; exact (IH Hok K Kr y HK).
    + rewrite rpcompose_compose; reflexivity.
  - intros _ l m K Kr i HK; cbn [ftl esem tlen]; replace (i <? 0) with false by (destruct i; reflexivity).
    cbn [cres]; replace (i - 0 + m) with (i + m) by lia; apply HK.
  - intros t IHt r IHr [Ht Hr] l m K Kr i HK; cbn [ftl].
    destruct i as [|i].
    + cbn [esem tlen tnth]; apply IHt; assumption.
    + rewrite esem_cons; apply IHr; assumption.
  - intros _ K Kr v HK; cbn [fs sget esem cres]; destruct v; apply HK.
  - intros h ts IHts m r IHr [_ [Hts Hr]] K Kr v HK; cbn [fs sget].
    destruct (label_eqb (lden h) (v_label v)) eqn:E.
    + apply label_eqb_eq in E || (destruct (label_eqb_spec (lden h) (v_label v)) as [E'|]; [|discriminate]).
      all: try (rewrite E || rewrite E'); apply IHts; assumption.
    + apply IHr; assumption.
  - intros s IHs Hs K Kr v HK; rewrite wden_end, rapply_compose_cres, rapply_sden by (apply oks_sdist, Hs).
    apply IHs; assumption.
  - intros s IHs L a w IHw [Hs Hw] K Kr v HK.
    rewrite wden_atom, !rcompose_assoc.
    apply IHw; [exact Hw|]; intros x; destruct x as [l i].
    rewrite rapply_compose_cres, (lifts_apply lenv tenv _ (le_n _)); unfold latom; cbn [v_label v_index].
    destruct (i <? lc lenv l L).
    + cbn [cres]; rewrite rapply_compose_cres, rapply_sden by (apply oks_sdist, Hs); apply IHs; assumption.
    + cbn [realises]; exists (rcompose (rcompose Kr (sden s)) (SH lenv L)); split.
      * intros y; destruct y as [ly iy]; rewrite rapply_compose_cres, (SH_apply lenv tenv _ (le_n _)); cbn [cres].
        rewrite rapply_compose_cres, rapply_sden by (apply oks_sdist, Hs); apply IHs; assumption.
      * rewrite cres_compose; reflexivity.
Qed.

Theorem free_to_real w1 w2 : okw w1 -> okw w2 ->
  (forall v, feq (fw w1 FVar v) (fw w2 FVar v)) -> wden w1 = wden w2.
Proof.
  intros H1 H2 Heq; apply rextensionality; intros v.
  assert (HK : forall y, realises (FVar y) (rapply (@ridentity T) y)) by (intros y; cbn [realises]; apply rapply_identity).
  pose proof (proj2 (proj2 (proj2 fw_real)) w1 H1 FVar ridentity v HK) as R1.
  pose proof (proj2 (proj2 (proj2 fw_real)) w2 H2 FVar ridentity v HK) as R2.
  rewrite rcompose_identity_l in R1, R2.
  exact (realises_unique _ _ _ (realises_feq _ _ _ (Heq v) R1) R2).
Qed.

End Free.
