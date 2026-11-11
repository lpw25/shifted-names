(** * Uniqueness of normal forms

    Normal forms that mean the same are the same (see
    [docs/normal-forms.md]).  The proof goes through a free model:
    applying a word to a variable gives a variable, a term with what
    happens to its names afterwards, or an atom stuck at a variable with
    what happens to the atom's outputs afterwards.

    - Words equal in the free model are equal under every interpretation
      ([free_to_real]).
    - Words satisfying the normal-form conditions ([wnf]) that are equal
      in the free model are equal ([nf_unique]). *)

From Stdlib Require Import Arith List Lia Bool Sorted String.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise.
Import ListNotations.

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


Lemma feq_refl f : feq f f.
Proof. induction f as [v|u b k IH|a z k IH]; cbn [feq]; repeat split; auto. Qed.

Lemma feq_sym f : forall g, feq f g -> feq g f.
Proof.
  induction f as [v|u b k IH|a z k IH]; intros [v'|u' b' k'|a' z' k']; cbn [feq];
    try (intros []; fail).
  - intros ->; reflexivity.
  - intros [<- [<- H]]; repeat split; intros y Hy; apply IH, H, Hy.
  - intros [<- [<- H]]; repeat split; intros y; apply IH, H.
Qed.

Lemma feq_trans f : forall g h, feq f g -> feq g h -> feq f h.
Proof.
  induction f as [v|u b k IH|a z k IH]; intros [v'|u' b' k'|a' z' k'] [v''|u'' b'' k''|a'' z'' k''];
    cbn [feq]; try (intros []; fail); try (intros _ []; fail).
  - intros -> ->; reflexivity.
  - intros [<- [<- H]] [<- [<- H']]; repeat split; intros y Hy; apply (IH y (k' y)); [apply H, Hy|apply H', Hy].
  - intros [<- [<- H]] [<- [<- H']]; repeat split; intros y; apply (IH y (k' y)); [apply H|apply H'].
Qed.

Section Real.

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

End Real.

(** ** Uniqueness in the free model *)

Section Unique.

(** The label expressions in play denote distinct labels. *)
Variable labs : list lexp.
Hypothesis Hinj : forall h h', In h labs -> In h' labs -> lden h = lden h' -> h = h'.

(** *** Entries *)

Definition fget (l : option label) (s : seg) (K : rvar -> fres) (j : nat) : fres :=
  match sget lenv l s with Some (ts, m) => ftl ts l m K j | None => K (mk_rvar l j) end.

Lemma fs_get s K v : fs s K v = fget (v_label v) s K (v_index v).
Proof.
  unfold fget; induction s as [|h ts m r IH] using seg_spine; cbn [fs sget]; [destruct v; reflexivity|].
  destruct (label_eqb_spec (lden h) (v_label v)) as [E|_]; [rewrite E; reflexivity|exact IH].
Qed.

Lemma fget_cons l h ts m r K j :
  fget l (SEnt h ts m r) K j = if label_eqb (lden h) l then ftl ts (lden h) m K j else fget l r K j.
Proof. unfold fget; cbn [sget]; destruct (label_eqb_spec (lden h) l) as [<-|_]; reflexivity. Qed.

Lemma ftl_lt ts l m K i : i < tlen ts -> ftl ts l m K i = ft (tnth ts i) K.
Proof.
  revert i; induction ts as [|t r IH] using tlist_spine; intros i Hi; cbn [tlen] in Hi; [lia|].
  destruct i as [|i]; cbn [ftl tnth]; [reflexivity|apply IH; lia].
Qed.

Lemma ftl_ge ts l m K i : tlen ts <= i -> ftl ts l m K i = K (mk_rvar l (i - tlen ts + m)).
Proof.
  revert i; induction ts as [|t r IH] using tlist_spine; intros i Hi; cbn [tlen] in *.
  - cbn [ftl]; do 2 f_equal; lia.
  - destruct i as [|i]; [lia|cbn [ftl]]; rewrite IH by lia; do 2 f_equal; lia.
Qed.

Lemma tlen_of xs : tlen (tl_of xs) = List.length xs.
Proof. rewrite tlen_list, tl_list_of; reflexivity. Qed.

Lemma tnth_of xs j : tnth (tl_of xs) j = nth j xs (NVar LNone 0).
Proof. rewrite tnth_list, tl_list_of; reflexivity. Qed.

(** An entry of [h] is trimmed: its last target is not the transparent
    [h₍ₘ₋₁₎]. *)
Definition trimmed (h : lexp) (xs : list ntgt) (m : nat) : Prop :=
  match last xs (NVar LNone 0), xs, m with
  | _, [], _ => True
  | NVar h' j, _, S m' => ~ (h' = h /\ j = m')
  | _, _, _ => True
  end.

Lemma trimmed_last h xs m x :
  trimmed h (xs ++ [x]) m -> forall h' j, x = NVar h' j -> m = S j -> h' <> h.
Proof.
  unfold trimmed; rewrite last_last; intros Ht h' j -> -> E; subst h'.
  destruct (xs ++ _) eqn:Ex; [destruct xs; discriminate|]; apply Ht; split; reflexivity.
Qed.

Lemma fvar_tgt t l j : feq (FVar (mk_rvar l j)) (ft t FVar) -> exists h, t = NVar h j /\ lden h = l.
Proof.
  destruct t as [h i|u w b]; cbn [ft feq]; [|intros []].
  intros E; injection E as -> ->; exists h; split; reflexivity.
Qed.

(** One entry against a longer one: the longer one would be transparent at
    its end. *)
Lemma ent_short (P : ntgt -> Prop) (HV : forall h j, P (NVar h j) -> In h labs) h xs m ys m' :
  In h labs -> Forall P ys -> trimmed h ys m' -> List.length xs < List.length ys ->
  (forall j, feq (ftl (tl_of xs) (lden h) m FVar j) (ftl (tl_of ys) (lden h) m' FVar j)) -> False.
Proof.
  intros Hh Hp Ht Hlt Heq.
  destruct (@exists_last _ ys) as [ys0 [x Ey]]; [destruct ys; cbn in Hlt; [lia|discriminate]|].
  subst ys; rewrite length_app in Hlt; cbn in Hlt.
  pose proof (Heq (List.length ys0)) as E1; pose proof (Heq (List.length ys0 + 1)) as E2.
  rewrite ftl_ge in E1 by (rewrite tlen_of; lia); rewrite tlen_of in E1.
  rewrite ftl_lt, tnth_of in E1 by (rewrite tlen_of, length_app; cbn; lia).
  rewrite app_nth2, Nat.sub_diag in E1 by lia; cbn [nth] in E1.
  rewrite !ftl_ge in E2 by (rewrite tlen_of; try rewrite length_app; cbn; lia).
  rewrite !tlen_of, length_app in E2; change (List.length [_]) with 1 in E2; cbn [feq] in E2; injection E2 as E2.
  destruct (fvar_tgt _ _ _ E1) as [h' [-> Eh]].
  apply (trimmed_last h ys0 m' _ Ht h' _ eq_refl); [lia|].
  apply Hinj; [|exact Hh|exact Eh].
  rewrite Forall_forall in Hp; apply (HV h' (List.length ys0 - List.length xs + m)), Hp, in_or_app; right; left; reflexivity.
Qed.

Lemma ent_unique (P1 P2 : ntgt -> Prop)
  (HP : forall t t', P1 t -> P2 t' -> feq (ft t FVar) (ft t' FVar) -> t = t')
  (HV1 : forall h j, P1 (NVar h j) -> In h labs) (HV2 : forall h j, P2 (NVar h j) -> In h labs) h xs m ys m' :
  In h labs -> Forall P1 xs -> Forall P2 ys -> trimmed h xs m -> trimmed h ys m' ->
  (forall j, feq (ftl (tl_of xs) (lden h) m FVar j) (ftl (tl_of ys) (lden h) m' FVar j)) -> xs = ys /\ m = m'.
Proof.
  intros Hh H1 H2 Ht1 Ht2 Heq.
  destruct (Nat.lt_trichotomy (List.length xs) (List.length ys)) as [Hlt|[Hle|Hlt]].
  - exfalso; exact (ent_short P2 HV2 h xs m ys m' Hh H2 Ht2 Hlt Heq).
  - split.
    + apply (nth_ext _ _ (NVar LNone 0) (NVar LNone 0) Hle); intros j Hj.
      pose proof (Heq j) as E; rewrite !ftl_lt, !tnth_of in E by (rewrite tlen_of; lia).
      rewrite Forall_forall in H1, H2.
      apply HP; [apply H1, nth_In; lia|apply H2, nth_In; lia|exact E].
    + pose proof (Heq (List.length xs)) as E; rewrite !ftl_ge in E by (rewrite tlen_of; lia).
      cbn [feq] in E; rewrite !tlen_of in E; injection E as E; lia.
  - exfalso; apply (ent_short P1 HV1 h ys m' xs m Hh H1 Ht1 Hlt); intros j; apply feq_sym, Heq.
Qed.

Lemma ent_not_id (P : ntgt -> Prop) (HV : forall h j, P (NVar h j) -> In h labs) h xs m :
  In h labs -> Forall P xs -> trimmed h xs m -> (xs <> [] \/ m <> 0) ->
  ~ (forall j, feq (ftl (tl_of xs) (lden h) m FVar j) (FVar (mk_rvar (lden h) j))).
Proof.
  intros Hh Hp Ht Hne Heq; destruct xs as [|x xs].
  - destruct Hne as [Hne|Hne]; [congruence|]; pose proof (Heq 0) as E; cbn [tl_of ftl feq] in E.
    injection E as E; lia.
  - apply (ent_short P HV h [] 0 (x :: xs) m Hh Hp Ht ltac:(cbn; lia)); intros j.
    apply feq_sym; replace (ftl (tl_of []) (lden h) 0 FVar j) with (FVar (mk_rvar (lden h) j))
      by (cbn [tl_of ftl]; rewrite Nat.add_0_r; reflexivity); apply Heq.
Qed.

(** *** Segments *)

Fixpoint sents (s : seg) : list (lexp * list ntgt * nat) :=
  match s with SNil => [] | SEnt h ts m r => (h, tl_list ts, m) :: sents r end.

Definition ekey (e : lexp * list ntgt * nat) : option label := let '(h, _, _) := e in lden h.

(** Canonical segments: labels in order and distinct, no entry the
    identity, no entry ending with a transparent target; applied to named
    variables only ([nm]), no entry for the bound label. *)
Definition eshape (nm : bool) (e : lexp * list ntgt * nat) : Prop :=
  let '(h, xs, m) := e in In h labs /\ trimmed h xs m /\ (xs <> [] \/ m <> 0) /\ (nm = true -> lden h <> None).

Definition sshape (nm : bool) (s : seg) : Prop :=
  StronglySorted (fun e e' => olabel_lt (ekey e) (ekey e')) (sents s) /\ Forall (eshape nm) (sents s).

Definition stgts (s : seg) : list ntgt := flat_map (fun e => let '(_, xs, _) := e in xs) (sents s).

Lemma stgts_cons h ts m r : stgts (SEnt h ts m r) = tl_list ts ++ stgts r.
Proof. reflexivity. Qed.

Lemma sget_above l s : (forall e, In e (sents s) -> olabel_lt l (ekey e)) -> sget lenv l s = None.
Proof.
  induction s as [|h ts m r IH] using seg_spine; cbn [sget sents]; [reflexivity|]; intros H.
  destruct (label_eqb_spec (lden h) l) as [E|_].
  - exfalso; apply (olabel_lt_irrefl l); pose proof (H _ (or_introl eq_refl)) as Hl; cbn in Hl; rewrite E in Hl; exact Hl.
  - apply IH; intros e He; apply H; right; exact He.
Qed.

Lemma sget_tgts l s ts m : sget lenv l s = Some (ts, m) -> forall t, In t (tl_list ts) -> In t (stgts s).
Proof.
  induction s as [|h ts' m' r IH] using seg_spine; cbn [sget]; [discriminate|]; rewrite stgts_cons.
  destruct (label_eqb (lden h) l).
  - intros E; injection E as -> ->; intros t Ht; apply in_or_app; left; exact Ht.
  - intros E t Ht; apply in_or_app; right; exact (IH E t Ht).
Qed.

Section SegUnique.

Variables P1 P2 : ntgt -> Prop.
Hypothesis HP : forall t t', P1 t -> P2 t' -> feq (ft t FVar) (ft t' FVar) -> t = t'.
Hypothesis HV1 : forall h j, P1 (NVar h j) -> In h labs.
Hypothesis HV2 : forall h j, P2 (NVar h j) -> In h labs.

Lemma fget_nil l K j : fget l SNil K j = K (mk_rvar l j).
Proof. reflexivity. Qed.

Theorem seg_unique s s' : sshape false s -> sshape false s' -> Forall P1 (stgts s) -> Forall P2 (stgts s') ->
  (forall l j, feq (fget l s FVar j) (fget l s' FVar j)) -> s = s'.
Proof.
  revert s'; induction s as [|h ts m r IH] using seg_spine; intros s' [Hs Ho] [Hs' Ho'] Hp Hp' Heq;
    destruct s' as [|h' ts' m' r']; [reflexivity| | |].
  - exfalso; cbn [sents] in Ho'; inversion Ho' as [|e l He]; subst; cbn [eshape] in He.
    destruct He as [Hh [Ht [Hne _]]]; rewrite stgts_cons, Forall_app in Hp'.
    apply (ent_not_id P2 HV2 h' (tl_list ts') m' Hh (proj1 Hp') Ht Hne); intros j.
    rewrite tl_of_list; pose proof (Heq (lden h') j) as E; rewrite fget_cons, label_eqb_refl, fget_nil in E.
    apply feq_sym; exact E.
  - exfalso; cbn [sents] in Ho; inversion Ho as [|e l He]; subst; cbn [eshape] in He.
    destruct He as [Hh [Ht [Hne _]]]; rewrite stgts_cons, Forall_app in Hp.
    apply (ent_not_id P1 HV1 h (tl_list ts) m Hh (proj1 Hp) Ht Hne); intros j.
    rewrite tl_of_list; pose proof (Heq (lden h) j) as E; rewrite fget_cons, label_eqb_refl, fget_nil in E.
    exact E.
  - cbn [sents] in *; inversion Hs as [|e l Hsr Hall]; inversion Hs' as [|e' l' Hsr' Hall']; subst.
    inversion Ho as [|e l He Hor]; inversion Ho' as [|e' l' He' Hor']; subst.
    rewrite Forall_forall in Hall, Hall'; cbn [eshape] in He, He'.
    rewrite stgts_cons, Forall_app in Hp, Hp'.
    destruct (olabel_trichotomy (lden h) (lden h')) as [Hlt|[Eh|Hlt]].
    + exfalso; destruct He as [Hh [Ht [Hne _]]].
      apply (ent_not_id P1 HV1 h (tl_list ts) m Hh (proj1 Hp) Ht Hne); intros j.
      rewrite tl_of_list; pose proof (Heq (lden h) j) as E; rewrite !fget_cons, label_eqb_refl in E.
      apply (feq_trans _ _ _ E).
      destruct (label_eqb_spec (lden h') (lden h)) as [E'|_]; [rewrite E' in Hlt; destruct (olabel_lt_irrefl _ Hlt)|].
      unfold fget; rewrite sget_above; [apply feq_refl|]; intros e0 Hi; exact (olabel_lt_trans _ _ _ Hlt (Hall' e0 Hi)).
    + destruct He as [Hh [Ht _]]; destruct He' as [Hh' [Ht' _]].
      assert (Ehh : h = h') by (apply Hinj; assumption); subst h'.
      assert (Ee : tl_list ts = tl_list ts' /\ m = m').
      { apply (ent_unique P1 P2 HP HV1 HV2 h _ _ _ _ Hh (proj1 Hp) (proj1 Hp') Ht Ht'); intros j.
        rewrite !tl_of_list; pose proof (Heq (lden h) j) as E; rewrite !fget_cons, label_eqb_refl in E; exact E. }
      destruct Ee as [Et <-]; rewrite <- (tl_of_list ts), <- (tl_of_list ts'), Et; f_equal.
      apply IH; [split; assumption|split; assumption|exact (proj2 Hp)|exact (proj2 Hp')|]; intros l j.
      pose proof (Heq l j) as E; rewrite !fget_cons in E.
      destruct (label_eqb_spec (lden h) l) as [<-|_]; [|exact E].
      unfold fget; rewrite !sget_above; [apply feq_refl| |]; intros e0 Hi; [apply Hall'|apply Hall]; exact Hi.
    + exfalso; destruct He' as [Hh [Ht [Hne _]]].
      apply (ent_not_id P2 HV2 h' (tl_list ts') m' Hh (proj1 Hp') Ht Hne); intros j.
      rewrite tl_of_list; pose proof (Heq (lden h') j) as E; rewrite !fget_cons, label_eqb_refl in E.
      apply feq_sym in E; apply (feq_trans _ _ _ E).
      destruct (label_eqb_spec (lden h) (lden h')) as [E'|_]; [rewrite E' in Hlt; destruct (olabel_lt_irrefl _ Hlt)|].
      unfold fget; rewrite sget_above; [apply feq_refl|]; intros e0 Hi; exact (olabel_lt_trans _ _ _ Hlt (Hall e0 Hi)).
Qed.

(** Applied to named variables only. *)
Definition obs (nm : bool) (v : rvar) : Prop := nm = true -> v_label v <> None.

Lemma sshape_weak nm s : sshape nm s -> sshape false s.
Proof.
  intros [H1 H2]; split; [exact H1|]; eapply Forall_impl; [|exact H2].
  intros [[h xs] m] [A [B [C _]]]; refine (conj A (conj B (conj C _))); discriminate.
Qed.

Lemma sget_none s : sshape true s -> sget lenv None s = None.
Proof.
  induction s as [|h ts m r IH] using seg_spine; cbn [sget]; [reflexivity|]; intros [Hs Ho].
  cbn [sents] in Hs, Ho; inversion Hs as [|e0 l0 Hsr Hall]; inversion Ho as [|e l He Hor]; subst; cbn [eshape] in He.
  rewrite (proj2 (label_eqb_neq _ _)) by (apply He; reflexivity); apply IH; split; assumption.
Qed.

Theorem seg_unique_nm nm s s' : sshape nm s -> sshape nm s' -> Forall P1 (stgts s) -> Forall P2 (stgts s') ->
  (forall l j, obs nm (mk_rvar l j) -> feq (fget l s FVar j) (fget l s' FVar j)) -> s = s'.
Proof.
  intros Hs Hs' Hp Hp' Heq; apply seg_unique; [eapply sshape_weak, Hs|eapply sshape_weak, Hs'|exact Hp|exact Hp'|].
  intros l j; destruct nm; [|apply Heq; discriminate].
  destruct l as [x|]; [apply Heq; intros _; discriminate|].
  unfold fget; rewrite !sget_none by assumption; apply feq_refl.
Qed.

End SegUnique.

(** *** Renamings *)

Definition ren_target (t : ntgt) : Prop := match t with NVar h _ => In h labs | NBind _ _ _ => False end.

Definition sren (s : seg) : Prop := Forall ren_target (stgts s).

Definition tvar (t : ntgt) : rvar := match t with NVar h j => mk_rvar (lden h) j | NBind _ _ _ => mk_rvar None 0 end.

(** Where a renaming segment sends a variable. *)
Definition sv (s : seg) (v : rvar) : rvar :=
  match sget lenv (v_label v) s with
  | Some (ts, m) =>
      if v_index v <? tlen ts then tvar (tnth ts (v_index v)) else mk_rvar (v_label v) (v_index v - tlen ts + m)
  | None => v
  end.

Lemma tnth_in ts i : i < tlen ts -> In (tnth ts i) (tl_list ts).
Proof. rewrite tnth_list, tlen_list; apply nth_In. Qed.

Lemma fs_ren s K v : sren s -> fs s K v = K (sv s v).
Proof.
  intros Hr; rewrite fs_get; unfold fget, sv.
  destruct (sget lenv (v_label v) s) as [[ts m]|] eqn:E; [|destruct v; reflexivity].
  destruct (Nat.ltb_spec (v_index v) (tlen ts)) as [Hi|Hi]; [|apply ftl_ge, Hi].
  rewrite ftl_lt by exact Hi.
  pose proof (proj1 (Forall_forall _ _) Hr _ (sget_tgts _ _ _ _ E _ (tnth_in _ _ Hi))) as Ht.
  destruct (tnth ts (v_index v)) as [h j|]; [reflexivity|contradiction].
Qed.

Lemma fget_ren s l j : sren s -> fget l s FVar j = FVar (sv s (mk_rvar l j)).
Proof.
  intros Hr; change (fget l s FVar j) with (fget (v_label (mk_rvar l j)) s FVar (v_index (mk_rvar l j))).
  rewrite <- fs_get; apply fs_ren, Hr.
Qed.

Theorem ren_unique nm s s' : sshape nm s -> sshape nm s' -> sren s -> sren s' ->
  (forall v, obs nm v -> sv s v = sv s' v) -> s = s'.
Proof.
  intros Hs Hs' Hr Hr' Heq; apply (seg_unique_nm ren_target ren_target) with nm; try assumption.
  - intros [h j|] [h' j'|]; cbn [ren_target ft feq]; try contradiction.
    intros Hh Hh' E; injection E as Eh ->; f_equal; apply Hinj; assumption.
  - intros h j H; exact H.
  - intros h j H; exact H.
  - intros l j Hv; rewrite !fget_ren by assumption; cbn [feq]; apply Heq, Hv.
Qed.

(** *** Lifts *)

Definition lok (L : list (lexp * nat)) : Prop :=
  StronglySorted (fun p p' => olabel_lt (lden (fst p)) (lden (fst p'))) L
  /\ Forall (fun p => In (fst p) labs /\ snd p <> 0) L.

Lemma lc_cons l h n L : lc lenv l ((h, n) :: L) = (if label_eqb (lden h) l then n else 0) + lc lenv l L.
Proof. reflexivity. Qed.

Lemma lc_above l L : (forall p, In p L -> olabel_lt l (lden (fst p))) -> lc lenv l L = 0.
Proof.
  induction L as [|[h n] L IH]; intros H; [reflexivity|].
  rewrite lc_cons, IH by (intros p Hp; apply H; right; exact Hp).
  destruct (label_eqb_spec (lden h) l) as [E|_]; [|reflexivity].
  exfalso; apply (olabel_lt_irrefl l); pose proof (H _ (or_introl eq_refl)) as Hl; cbn in Hl; rewrite E in Hl; exact Hl.
Qed.

Lemma lok_tail p L : lok (p :: L) -> lok L.
Proof. intros [Hs Ho]; inversion Hs; inversion Ho; subst; split; assumption. Qed.

Lemma lc_head h n L : lok ((h, n) :: L) -> lc lenv (lden h) ((h, n) :: L) = n.
Proof.
  intros [Hs _]; inversion Hs as [|p q _ Hall]; subst; rewrite lc_cons, label_eqb_refl, lc_above; [lia|].
  rewrite Forall_forall in Hall; intros p Hp; exact (Hall p Hp).
Qed.

Lemma lc_lt l h n L : lok ((h, n) :: L) -> olabel_lt l (lden h) -> lc lenv l ((h, n) :: L) = 0.
Proof.
  intros [Hs _] Hl; inversion Hs as [|p q _ Hall]; subst; rewrite Forall_forall in Hall; apply lc_above.
  intros p [<-|Hp]; [exact Hl|exact (olabel_lt_trans _ _ _ Hl (Hall p Hp))].
Qed.

Lemma lok_head h n L : lok ((h, n) :: L) -> In h labs /\ n <> 0.
Proof. intros [_ Ho]; inversion Ho as [|p q H]; exact H. Qed.

Lemma lifts_unique L : forall L', lok L -> lok L' -> (forall l, lc lenv l L = lc lenv l L') -> L = L'.
Proof.
  induction L as [|[h n] L IH]; intros [|[h' n'] L'] HL HL' Heq; [reflexivity| | |].
  - exfalso; pose proof (Heq (lden h')) as E; rewrite (lc_head _ _ _ HL') in E; cbn [lc] in E.
    destruct (lok_head _ _ _ HL'); lia.
  - exfalso; pose proof (Heq (lden h)) as E; rewrite (lc_head _ _ _ HL) in E; cbn [lc] in E.
    destruct (lok_head _ _ _ HL); lia.
  - destruct (olabel_trichotomy (lden h) (lden h')) as [Hlt|[Eh|Hlt]].
    + exfalso; pose proof (Heq (lden h)) as E; rewrite (lc_head _ _ _ HL), (lc_lt _ _ _ _ HL' Hlt) in E.
      destruct (lok_head _ _ _ HL); lia.
    + assert (h = h') as <- by (apply Hinj; [apply (lok_head _ _ _ HL)|apply (lok_head _ _ _ HL')|exact Eh]).
      pose proof (Heq (lden h)) as E; rewrite (lc_head _ _ _ HL), (lc_head _ _ _ HL') in E; subst n'.
      f_equal; apply IH; [eapply lok_tail, HL|eapply lok_tail, HL'|]; intros l.
      pose proof (Heq l) as E; rewrite !lc_cons in E; lia.
    + exfalso; pose proof (Heq (lden h')) as E; rewrite (lc_head _ _ _ HL'), (lc_lt _ _ _ _ HL Hlt) in E.
      destruct (lok_head _ _ _ HL'); lia.
Qed.

(** *** Lift position

    The variables a lift passes around an atom are [V]; the inputs the
    segment before the atom sends into [V] are, per label [g], sent in
    order to [g₍₀₎], [g₍₁₎], ...: the [j]-th of them, in index order,
    to [g₍ⱼ₎]. *)

Definition inVb (L : list (lexp * nat)) (y : rvar) : bool := v_index y <? lc lenv (v_label y) L.

Fixpoint cntV (U : seg) (L : list (lexp * nat)) (g : option label) (i : nat) : nat :=
  match i with 0 => 0 | S i => cntV U L g i + (if inVb L (sv U (mk_rvar g i)) then 1 else 0) end.

Definition lpos (U : seg) (L : list (lexp * nat)) : Prop :=
  (forall g i, inVb L (sv U (mk_rvar g i)) = true -> sv U (mk_rvar g i) = mk_rvar g (cntV U L g i))
  /\ (forall g j, j < lc lenv g L -> exists i, sv U (mk_rvar g i) = mk_rvar g j).

(** *** The normal-form conditions *)

Definition isend (w : word) : bool := match w with WEnd _ => true | WAtom _ _ _ _ => false end.

(** An atom under [L] after the word [w]. *)
Definition aok (nm : bool) (L : list (lexp * nat)) (w : word) : Prop :=
  lok L /\ lpos (whead w) L /\ (nm = true -> isend w = true -> lc lenv None L = 0).

(** Words of renamings. *)
Fixpoint rnf (nm : bool) (w : word) : Prop :=
  match w with
  | WEnd U => sshape nm U /\ sren U
  | WAtom s L a w' => sshape false s /\ sren s /\ aok nm L w' /\ rnf nm w'
  end.

(** Normal forms; [wnf true] for payload words applied to named variables
    only. *)
Fixpoint tnf (t : ntgt) : Prop :=
  match t with
  | NVar h _ => In h labs
  | NBind _ wp b => wnf (match b with None => true | Some _ => false end) wp
  end
with tlnf (ts : tlist) : Prop := match ts with TNil => True | TCons t r => tnf t /\ tlnf r end
with snf (s : seg) : Prop := match s with SNil => True | SEnt _ ts _ r => tlnf ts /\ snf r end
with wnf (nm : bool) (w : word) : Prop :=
  match w with
  | WEnd s => sshape nm s /\ snf s
  | WAtom s L a w' => sshape false s /\ snf s /\ aok nm L w' /\ rnf nm w'
  end.

Lemma snf_in s : snf s -> forall t, In t (stgts s) -> tnf t.
Proof.
  induction s as [|h ts m r IH] using seg_spine; cbn [snf]; [intros _ t []|]; intros [Hts Hr] t Ht.
  rewrite stgts_cons in Ht; apply in_app_or in Ht as [Ht|Ht]; [|exact (IH Hr t Ht)].
  clear IH Hr; induction ts as [|t' r' IH] using tlist_spine; cbn in Ht, Hts; [contradiction|].
  destruct Ht as [<-|Ht]; [exact (proj1 Hts)|exact (IH (proj2 Hts) Ht)].
Qed.

(** *** Sizes *)

Fixpoint tsz (t : ntgt) : nat := match t with NVar _ _ => 1 | NBind _ w _ => S (wsz w) end
with tlsz (ts : tlist) : nat := match ts with TNil => 0 | TCons t r => tsz t + tlsz r end
with ssz (s : seg) : nat := match s with SNil => 0 | SEnt _ ts _ r => tlsz ts + ssz r end
with wsz (w : word) : nat := match w with WEnd s => S (ssz s) | WAtom s _ _ w => S (ssz s + wsz w) end.

Lemma stgts_sz s t : In t (stgts s) -> tsz t <= ssz s.
Proof.
  induction s as [|h ts m r IH] using seg_spine; [intros []|]; rewrite stgts_cons; cbn [ssz].
  intros Ht; apply in_app_or in Ht as [Ht|Ht]; [|specialize (IH Ht); lia].
  enough (tsz t <= tlsz ts) by lia; clear IH; induction ts as [|t' r' IH] using tlist_spine; cbn in *; [contradiction|].
  destruct Ht as [<-|Ht]; [lia|specialize (IH Ht); lia].
Qed.

(** *** Peeling the first atom *)

Fixpoint natoms (w : word) : nat := match w with WEnd _ => 0 | WAtom _ _ _ w => S (natoms w) end.

(** [W] after [⇑ᴸσ] after [U]. *)
Fixpoint wsnoc (W : word) (L : list (lexp * nat)) (a : nat) (U : seg) : word :=
  match W with
  | WEnd s => WAtom s L a (WEnd U)
  | WAtom s L' a' W' => WAtom s L' a' (wsnoc W' L a U)
  end.

Lemma word_view w : isend w = false -> exists W L a U, w = wsnoc W L a U.
Proof.
  induction w as [s|s L a w IH] using word_spine; [discriminate|]; intros _.
  destruct w as [U|s' L' a' w'].
  - exists (WEnd s), L, a, U; reflexivity.
  - destruct (IH eq_refl) as [W [L1 [a1 [U1 E]]]]; rewrite E; exists (WAtom s L a W), L1, a1, U1; reflexivity.
Qed.

Lemma fw_snoc W L a U K v : fw (wsnoc W L a U) K v = fs U (latom L a (fun y => fw W K y)) v.
Proof.
  revert K; induction W as [s|s L' a' W IH] using word_spine; intros K; [reflexivity|].
  exact (IH (latom L' a' (fun y => fs s K y))).
Qed.

Lemma wsz_snoc W L a U : wsz W < wsz (wsnoc W L a U).
Proof. induction W as [s|s L' a' W IH] using word_spine; cbn [wsnoc wsz]; lia. Qed.

Lemma whead_snoc W L a U : whead (wsnoc W L a U) = whead W.
Proof. destruct W; reflexivity. Qed.

Lemma rnf_snoc nm W L a U : rnf nm (wsnoc W L a U) ->
  rnf false W /\ sshape nm U /\ sren U /\ lok L /\ lpos U L /\ (nm = true -> lc lenv None L = 0).
Proof.
  induction W as [s|s L' a' W IH] using word_spine; cbn [wsnoc rnf].
  - intros [Hs [Hr [[Hl [Hp Hn]] [HU HrU]]]].
    refine (conj (conj Hs Hr) (conj HU (conj HrU (conj Hl (conj Hp _))))); intros E; apply Hn; [exact E|reflexivity].
  - intros [Hs [Hr [[Hl [Hp _]] Hw]]]; destruct (IH Hw) as [HW Hrest]; split; [|exact Hrest].
    rewrite whead_snoc in Hp; refine (conj Hs (conj Hr (conj (conj Hl (conj Hp _)) HW))); intros E; discriminate E.
Qed.

Lemma wnf_snoc nm W L a U : wnf nm (wsnoc W L a U) ->
  wnf false W /\ sshape nm U /\ sren U /\ lok L /\ lpos U L /\ (nm = true -> lc lenv None L = 0).
Proof.
  destruct W as [s|s L' a' W]; cbn [wsnoc wnf].
  - intros [Hs [Hn [[Hl [Hp Hn']] [HU HrU]]]].
    refine (conj (conj Hs Hn) (conj HU (conj HrU (conj Hl (conj Hp _))))); intros E; apply Hn'; [exact E|reflexivity].
  - intros [Hs [Hn [[Hl [Hp _]] Hw]]]; destruct (rnf_snoc _ _ _ _ _ Hw) as [HW Hrest]; split; [|exact Hrest].
    rewrite whead_snoc in Hp; refine (conj Hs (conj Hn (conj (conj Hl (conj Hp _)) HW))); intros E; discriminate E.
Qed.

(** *** How many atoms are left

    Far enough along a named label, a word sends every variable through
    each of its atoms in turn; the number of atoms is read off what it
    does there. *)

Definition lbig : option label := Some EmptyString.

Lemma obs_big nm i : obs nm (mk_rvar lbig i).
Proof. intros _ E; discriminate E. Qed.

Fixpoint deep (d : nat) (k : rvar -> fres) : Prop :=
  match d with
  | 0 => exists B, forall i, B <= i -> exists y, k (mk_rvar lbig i) = FVar y
  | S d => exists B a, forall i, B <= i -> exists z k', k (mk_rvar lbig i) = FStuck a z k' /\ deep d k'
  end.

Lemma deep_unique d : forall d' k k', deep d k -> deep d' k' ->
  (forall i, feq (k (mk_rvar lbig i)) (k' (mk_rvar lbig i))) -> d = d'.
Proof.
  induction d as [|d IH]; intros [|d'] k k' Hk Hk' E; cbn [deep] in Hk, Hk'.
  - reflexivity.
  - exfalso; destruct Hk as [B H]; destruct Hk' as [B' [a' H']].
    destruct (H (B + B') ltac:(lia)) as [y Ey]; destruct (H' (B + B') ltac:(lia)) as [z [k2 [Ez _]]].
    pose proof (E (B + B')) as E'; rewrite Ey, Ez in E'; exact E'.
  - exfalso; destruct Hk as [B [a H]]; destruct Hk' as [B' H'].
    destruct (H (B + B') ltac:(lia)) as [z [k1 [Ez _]]]; destruct (H' (B + B') ltac:(lia)) as [y Ey].
    pose proof (E (B + B')) as E'; rewrite Ey, Ez in E'; exact E'.
  - destruct Hk as [B [a H]]; destruct Hk' as [B' [a' H']].
    destruct (H (B + B') ltac:(lia)) as [z [k1 [Ez Hk1]]]; destruct (H' (B + B') ltac:(lia)) as [z' [k2 [Ez' Hk2]]].
    pose proof (E (B + B')) as E'; rewrite Ez, Ez' in E'; cbn [feq] in E'; destruct E' as [_ [_ Ek]].
    f_equal; apply (IH d' k1 k2 Hk1 Hk2); intros i; apply Ek.
Qed.

Lemma fs_big s K l N : exists B, forall i, B <= i -> exists j, N <= j /\ fs s K (mk_rvar l i) = K (mk_rvar l j).
Proof.
  destruct (sget lenv l s) as [[ts m]|] eqn:E.
  - exists (N + tlen ts); intros i Hi; exists (i - tlen ts + m); split; [lia|].
    rewrite fs_get; unfold fget; cbn [v_label v_index]; rewrite E; apply ftl_ge; lia.
  - exists N; intros i Hi; exists i; split; [exact Hi|].
    rewrite fs_get; unfold fget; cbn [v_label v_index]; rewrite E; reflexivity.
Qed.

Lemma deep_FVar : deep 0 FVar.
Proof. exists 0; intros i _; exists (mk_rvar lbig i); reflexivity. Qed.

Lemma deep_fs d s K : deep d K -> deep d (fun v => fs s K v).
Proof.
  destruct d as [|d]; cbn [deep].
  - intros [B H]; destruct (fs_big s K lbig B) as [B' HB]; exists B'; intros i Hi.
    destruct (HB i Hi) as [j [Hj E]]; rewrite E; apply H, Hj.
  - intros [B [a H]]; destruct (fs_big s K lbig B) as [B' HB]; exists B', a; intros i Hi.
    destruct (HB i Hi) as [j [Hj E]]; rewrite E; apply H, Hj.
Qed.

Lemma deep_shift d L K : deep d K -> deep d (fun y => K (shiftL L y)).
Proof.
  destruct d as [|d]; cbn [deep]; [intros [B H]; exists B|intros [B [a H]]; exists B, a];
    intros i Hi; unfold shiftL; cbn [v_label v_index]; apply H; lia.
Qed.

Lemma deep_latom d L a K : deep d K -> deep (S d) (latom L a K).
Proof.
  intros Hd; cbn [deep]; exists (lc lenv lbig L), a; intros i Hi; unfold latom; cbn [v_label v_index].
  rewrite (proj2 (Nat.ltb_ge _ _) Hi); eexists _, _; split; [reflexivity|apply deep_shift, Hd].
Qed.

Lemma deep_fw w : forall d K, deep d K -> deep (natoms w + d) (fun v => fw w K v).
Proof.
  induction w as [s|s L a w IH] using word_spine; intros d K Hd; cbn [natoms].
  - apply deep_fs, Hd.
  - replace (S (natoms w) + d) with (natoms w + S d) by lia.
    exact (IH (S d) (latom L a (fun y => fs s K y)) (deep_latom _ _ _ _ (deep_fs _ _ _ Hd))).
Qed.

(** A result stuck in [K] has fewer than [e] atoms left. *)
Definition nstuck (e : nat) (K : rvar -> fres) : Prop :=
  forall y a z k, K y = FStuck a z k -> exists d, d < e /\ deep d k.

Lemma nstuck_FVar : nstuck 0 FVar.
Proof. intros y a z k E; discriminate. Qed.

Lemma nstuck_fs e s K : nstuck e K -> nstuck e (fun v => fs s K v).
Proof.
  intros HK y a z k E; cbv beta in E; rewrite fs_get in E; unfold fget in E.
  destruct (sget lenv (v_label y) s) as [[ts m]|]; [|exact (HK _ _ _ _ E)].
  destruct (Nat.ltb_spec (v_index y) (tlen ts)) as [Hi|Hi].
  - rewrite ftl_lt in E by exact Hi; destruct (tnth ts (v_index y)); cbn [ft] in E; [exact (HK _ _ _ _ E)|discriminate].
  - rewrite ftl_ge in E by exact Hi; exact (HK _ _ _ _ E).
Qed.

Lemma nstuck_latom e L a K : nstuck e K -> deep e K -> nstuck (S e) (latom L a K).
Proof.
  intros HK Hd y a' z k E; unfold latom in E; destruct (_ <? _).
  - destruct (HK _ _ _ _ E) as [d [Hd' Hk]]; exists d; split; [lia|exact Hk].
  - injection E as _ _ <-; exists e; split; [lia|apply deep_shift, Hd].
Qed.

Lemma nstuck_fw w : forall e K, nstuck e K -> deep e K -> nstuck (natoms w + e) (fun v => fw w K v).
Proof.
  induction w as [s|s L a w IH] using word_spine; intros e K Hn Hd; cbn [natoms].
  - apply nstuck_fs, Hn.
  - replace (S (natoms w) + e) with (natoms w + S e) by lia.
    exact (IH (S e) (latom L a (fun y => fs s K y))
             (nstuck_latom _ _ _ _ (nstuck_fs _ _ _ Hn) (deep_fs _ _ _ Hd)) (deep_latom _ _ _ _ (deep_fs _ _ _ Hd))).
Qed.

Lemma sv_big U l N : sren U -> exists B, forall i, B <= i -> exists j, N <= j /\ sv U (mk_rvar l i) = mk_rvar l j.
Proof.
  intros Hr; destruct (fs_big U FVar l N) as [B HB]; exists B; intros i Hi.
  destruct (HB i Hi) as [j [Hj E]]; exists j; split; [exact Hj|].
  rewrite fs_ren in E by exact Hr; injection E as E; exact E.
Qed.

Definition unsh (L : list (lexp * nat)) (y : rvar) : rvar :=
  mk_rvar (v_label y) (v_index y - lc lenv (v_label y) L).

(** The first atom, its lifts and the segment before it are determined,
    and so is what the rest of the word does. *)
Lemma peel nm W1 L1 a1 U1 W2 L2 a2 U2 :
  sshape nm U1 -> sren U1 -> lok L1 -> lpos U1 L1 -> (nm = true -> lc lenv None L1 = 0) ->
  sshape nm U2 -> sren U2 -> lok L2 -> lpos U2 L2 -> (nm = true -> lc lenv None L2 = 0) ->
  (forall v, obs nm v -> feq (fw (wsnoc W1 L1 a1 U1) FVar v) (fw (wsnoc W2 L2 a2 U2) FVar v)) ->
  U1 = U2 /\ L1 = L2 /\ a1 = a2 /\ forall y, feq (fw W1 FVar y) (fw W2 FVar y).
Proof.
  intros Hs1 Hr1 Hl1 Hp1 Hn1 Hs2 Hr2 Hl2 Hp2 Hn2 Heq.
  set (R1 := fun y => fw W1 FVar y); set (R2 := fun y => fw W2 FVar y).
  assert (H : forall v, obs nm v -> feq (latom L1 a1 R1 (sv U1 v)) (latom L2 a2 R2 (sv U2 v))).
  { intros v Hv; pose proof (Heq v Hv) as E; rewrite !fw_snoc, !fs_ren in E by assumption; exact E. }
  (* The atoms, and what follows them. *)
  destruct (sv_big U1 lbig (lc lenv lbig L1) Hr1) as [B1 HB1].
  destruct (sv_big U2 lbig (lc lenv lbig L2) Hr2) as [B2 HB2].
  destruct (HB1 (B1 + B2) ltac:(lia)) as [j1 [Hj1 E1]]; destruct (HB2 (B1 + B2) ltac:(lia)) as [j2 [Hj2 E2]].
  pose proof (H _ (obs_big nm (B1 + B2))) as Hb; rewrite E1, E2 in Hb; unfold latom in Hb; cbn [v_label v_index] in Hb.
  rewrite (proj2 (Nat.ltb_ge _ _) Hj1), (proj2 (Nat.ltb_ge _ _) Hj2) in Hb; cbn [feq] in Hb.
  destruct Hb as [<- [_ Hk]].
  assert (Hd1 : deep (natoms W1) (fun y => R1 (shiftL L1 y))).
  { apply deep_shift; unfold R1; rewrite <- (Nat.add_0_r (natoms W1)); apply deep_fw, deep_FVar. }
  assert (Hd2 : deep (natoms W2) (fun y => R2 (shiftL L2 y))).
  { apply deep_shift; unfold R2; rewrite <- (Nat.add_0_r (natoms W2)); apply deep_fw, deep_FVar. }
  assert (En : natoms W1 = natoms W2) by (apply (deep_unique _ _ _ _ Hd1 Hd2); intros i; apply Hk).
  assert (Hst1 : nstuck (natoms W1) R1).
  { unfold R1; rewrite <- (Nat.add_0_r (natoms W1)); apply nstuck_fw; [apply nstuck_FVar|apply deep_FVar]. }
  assert (Hst2 : nstuck (natoms W2) R2).
  { unfold R2; rewrite <- (Nat.add_0_r (natoms W2)); apply nstuck_fw; [apply nstuck_FVar|apply deep_FVar]. }
  (* Each input is passed around the atom in both words or stuck at it in both. *)
  assert (HB : forall v, obs nm v ->
    (inVb L1 (sv U1 v) = true /\ inVb L2 (sv U2 v) = true /\ feq (R1 (sv U1 v)) (R2 (sv U2 v)))
    \/ (inVb L1 (sv U1 v) = false /\ inVb L2 (sv U2 v) = false /\ unsh L1 (sv U1 v) = unsh L2 (sv U2 v))).
  { intros v Hv; pose proof (H v Hv) as E; unfold latom in E; unfold inVb.
    destruct (v_index (sv U1 v) <? _) eqn:Ei1, (v_index (sv U2 v) <? _) eqn:Ei2.
    - left; auto.
    - exfalso; destruct (R1 (sv U1 v)) as [| |a z k] eqn:ER; cbn [feq] in E; try contradiction.
      destruct E as [_ [_ Ek]]; destruct (Hst1 _ _ _ _ ER) as [d [Hd Hdk]].
      assert (d = natoms W2) by (apply (deep_unique _ _ _ _ Hdk Hd2); intros i; apply Ek); lia.
    - exfalso; destruct (R2 (sv U2 v)) as [| |a z k] eqn:ER; cbn [feq] in E; try contradiction.
      destruct E as [_ [_ Ek]]; destruct (Hst2 _ _ _ _ ER) as [d [Hd Hdk]].
      assert (natoms W1 = d) by (apply (deep_unique _ _ _ _ Hd1 Hdk); intros i; apply Ek); lia.
    - right; cbn [feq] in E; destruct E as [_ [Ez _]]; auto. }
  assert (Hcnt : forall g i, obs nm (mk_rvar g 0) -> cntV U1 L1 g i = cntV U2 L2 g i).
  { intros g i Hg; induction i as [|i IHi]; [reflexivity|]; cbn [cntV]; rewrite IHi.
    destruct (HB (mk_rvar g i) Hg) as [[-> [-> _]]|[-> [-> _]]]; reflexivity. }
  (* The lifts. *)
  assert (Hle : forall l j, obs nm (mk_rvar l 0) -> j < lc lenv l L1 -> j < lc lenv l L2).
  { intros l j Hl Hj; destruct (proj2 Hp1 l j Hj) as [i Ei].
    destruct (HB (mk_rvar l i) Hl) as [[E1' [E2' _]]|[E1' _]].
    - rewrite (proj1 Hp1 l i E1') in Ei; injection Ei as <-.
      pose proof (proj1 Hp2 l i E2') as E; rewrite E in E2'; unfold inVb in E2'; cbn [v_label v_index] in E2'.
      rewrite Hcnt by exact Hl; apply Nat.ltb_lt, E2'.
    - rewrite Ei in E1'; unfold inVb in E1'; cbn [v_label v_index] in E1'; apply Nat.ltb_ge in E1'; lia. }
  assert (Hle' : forall l j, obs nm (mk_rvar l 0) -> j < lc lenv l L2 -> j < lc lenv l L1).
  { intros l j Hl Hj; destruct (proj2 Hp2 l j Hj) as [i Ei].
    destruct (HB (mk_rvar l i) Hl) as [[E1' [E2' _]]|[_ [E2' _]]].
    - rewrite (proj1 Hp2 l i E2') in Ei; injection Ei as <-.
      pose proof (proj1 Hp1 l i E1') as E; rewrite E in E1'; unfold inVb in E1'; cbn [v_label v_index] in E1'.
      rewrite Hcnt in E1' by exact Hl; apply Nat.ltb_lt, E1'.
    - rewrite Ei in E2'; unfold inVb in E2'; cbn [v_label v_index] in E2'; apply Nat.ltb_ge in E2'; lia. }
  assert (Hob : forall l, obs nm (mk_rvar l 0) \/ (lc lenv l L1 = 0 /\ lc lenv l L2 = 0)).
  { intros l; destruct nm; [destruct l as [x|]|].
    - left; intros _ E; discriminate E.
    - right; split; [apply Hn1|apply Hn2]; reflexivity.
    - left; intros E; discriminate E. }
  assert (Hlc : forall l, lc lenv l L1 = lc lenv l L2).
  { intros l; destruct (Hob l) as [Ho|[-> ->]]; [|reflexivity].
    destruct (Nat.lt_trichotomy (lc lenv l L1) (lc lenv l L2)) as [Hlt|[E|Hlt]];
      [specialize (Hle' _ _ Ho Hlt); lia|exact E|specialize (Hle _ _ Ho Hlt); lia]. }
  assert (EL : L1 = L2) by (apply lifts_unique; assumption); subst L2.
  (* The segment before the atom. *)
  assert (Hsv : forall v, obs nm v -> sv U1 v = sv U2 v).
  { intros [g i] Hv; destruct (HB _ Hv) as [[E1' [E2' _]]|[E1' [E2' Eu]]].
    - rewrite (proj1 Hp1 g i E1'), (proj1 Hp2 g i E2'), Hcnt by exact Hv; reflexivity.
    - unfold inVb, unsh in *; destruct (sv U1 (mk_rvar g i)) as [l1 i1], (sv U2 (mk_rvar g i)) as [l2 i2].
      cbn [v_label v_index] in *; injection Eu as -> Ei; apply Nat.ltb_ge in E1', E2'; f_equal; lia. }
  assert (EU : U1 = U2) by (apply (ren_unique nm); assumption); subst U2.
  (* The rest. *)
  split; [reflexivity|split; [reflexivity|split; [reflexivity|]]].
  intros [l j]; change (feq (R1 (mk_rvar l j)) (R2 (mk_rvar l j))).
  destruct (Nat.ltb_spec j (lc lenv l L1)) as [Hj|Hj].
  - destruct (proj2 Hp1 l j Hj) as [i Ei].
    assert (Hv : obs nm (mk_rvar l i)).
    { destruct nm; [|discriminate]; intros _ El; cbn [v_label] in El; subst l; rewrite Hn1 in Hj by reflexivity; lia. }
    destruct (HB _ Hv) as [[_ [_ E]]|[E _]]; rewrite Ei in E; [exact E|].
    unfold inVb in E; cbn [v_label v_index] in E; apply Nat.ltb_ge in E; lia.
  - pose proof (Hk (mk_rvar l (j - lc lenv l L1))) as E; unfold shiftL in E; cbn [v_label v_index] in E.
    replace (j - lc lenv l L1 + lc lenv l L1) with j in E by lia; exact E.
Qed.

(** *** Uniqueness *)

Theorem nf_unique_n n : forall w1 w2 nm, wsz w1 <= n -> wnf nm w1 -> wnf nm w2 ->
  (forall v, obs nm v -> feq (fw w1 FVar v) (fw w2 FVar v)) -> w1 = w2.
Proof.
  induction n as [|n IH]; intros w1 w2 nm Hsz H1 H2 Heq; [destruct w1; cbn in Hsz; lia|].
  destruct (isend w1) eqn:Ew1, (isend w2) eqn:Ew2.
  - destruct w1 as [s1|]; [|discriminate]; destruct w2 as [s2|]; [|discriminate].
    destruct H1 as [Hs1 Hn1]; destruct H2 as [Hs2 Hn2]; f_equal.
    refine (seg_unique_nm (fun t => In t (stgts s1) /\ tnf t) tnf _ _ _ nm s1 s2 Hs1 Hs2 _ _ _).
    + intros t t' [Ht Hnt] Hnt' E.
      destruct t as [h j|u wp b], t' as [h' j'|u' wp' b']; cbn [ft feq tnf] in E, Hnt, Hnt'; try contradiction.
      * injection E as Eh ->; f_equal; apply Hinj; assumption.
      * destruct E as [<- [<- Ek]]; f_equal.
        apply (IH wp wp' (match b with None => true | Some _ => false end)); try assumption.
        -- pose proof (stgts_sz s1 _ Ht) as Hs; cbn [tsz wsz] in Hs, Hsz; lia.
        -- intros y Hy; apply Ek; intros Eb; subst b; apply Hy; reflexivity.
    + intros h j [_ H]; exact H.
    + intros h j H; exact H.
    + apply Forall_forall; intros t Ht; split; [exact Ht|exact (snf_in s1 Hn1 t Ht)].
    + apply Forall_forall; intros t Ht; exact (snf_in s2 Hn2 t Ht).
    + intros l j Hl; pose proof (Heq (mk_rvar l j) Hl) as E; cbn [fw] in E; rewrite !fs_get in E; exact E.
  - destruct w1 as [s1|]; [|discriminate]; destruct (word_view w2 Ew2) as [W2 [L2 [a2 [U2 ->]]]].
    destruct (wnf_snoc _ _ _ _ _ H2) as [_ [_ [Hr2 _]]]; exfalso.
    destruct (fs_big s1 FVar lbig 0) as [B1 HB1]; destruct (sv_big U2 lbig (lc lenv lbig L2) Hr2) as [B2 HB2].
    destruct (HB1 (B1 + B2) ltac:(lia)) as [j1 [_ E1]]; destruct (HB2 (B1 + B2) ltac:(lia)) as [j2 [Hj2 E2]].
    pose proof (Heq (mk_rvar lbig (B1 + B2)) (obs_big _ _)) as E.
    rewrite fw_snoc, fs_ren in E by exact Hr2; cbn [fw] in E; rewrite E1, E2 in E.
    unfold latom in E; cbn [v_label v_index] in E; rewrite (proj2 (Nat.ltb_ge _ _) Hj2) in E; exact E.
  - destruct w2 as [s2|]; [|discriminate]; destruct (word_view w1 Ew1) as [W1 [L1 [a1 [U1 ->]]]].
    destruct (wnf_snoc _ _ _ _ _ H1) as [_ [_ [Hr1 _]]]; exfalso.
    destruct (fs_big s2 FVar lbig 0) as [B1 HB1]; destruct (sv_big U1 lbig (lc lenv lbig L1) Hr1) as [B2 HB2].
    destruct (HB1 (B1 + B2) ltac:(lia)) as [j1 [_ E1]]; destruct (HB2 (B1 + B2) ltac:(lia)) as [j2 [Hj2 E2]].
    pose proof (Heq (mk_rvar lbig (B1 + B2)) (obs_big _ _)) as E.
    rewrite fw_snoc, fs_ren in E by exact Hr1; cbn [fw] in E; rewrite E1, E2 in E.
    unfold latom in E; cbn [v_label v_index] in E; rewrite (proj2 (Nat.ltb_ge _ _) Hj2) in E; exact E.
  - destruct (word_view w1 Ew1) as [W1 [L1 [a1 [U1 ->]]]]; destruct (word_view w2 Ew2) as [W2 [L2 [a2 [U2 ->]]]].
    destruct (wnf_snoc _ _ _ _ _ H1) as [HW1 [Hs1 [Hr1 [Hl1 [Hp1 Hn1]]]]].
    destruct (wnf_snoc _ _ _ _ _ H2) as [HW2 [Hs2 [Hr2 [Hl2 [Hp2 Hn2]]]]].
    destruct (peel nm W1 L1 a1 U1 W2 L2 a2 U2 Hs1 Hr1 Hl1 Hp1 Hn1 Hs2 Hr2 Hl2 Hp2 Hn2 Heq) as [<- [<- [<- HR]]].
    f_equal; apply (IH W1 W2 false); [pose proof (wsz_snoc W1 L1 a1 U1); lia|exact HW1|exact HW2|].
    intros v _; apply HR.
Qed.

Theorem nf_unique w1 w2 : wnf false w1 -> wnf false w2 ->
  (forall v, feq (fw w1 FVar v) (fw w2 FVar v)) -> w1 = w2.
Proof. intros H1 H2 Heq; apply (nf_unique_n (wsz w1) w1 w2 false (le_n _) H1 H2); intros v _; apply Heq. Qed.

End Unique.

End Free.
