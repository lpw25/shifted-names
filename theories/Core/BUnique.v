(** * Canonical words with branches are unique

    The canonical form of [docs/design-nf2.md]: a layered word whose terms
    carry a branch word.  A term of a segment with rest [r] is
    [NBind u w b]: its payload is the branch [wbody w] (empty, or ending
    with an atom), then the tail [wtail w] (a renaming that leaves named
    variables alone), then [r].  The conditions are those of
    [LayeredUnique.lnf] made relative to a base continuation [K] (the
    line: [FVar]; a branch: its tail then the rest), over a domain of
    observable inputs, with the order taken within a stretch and with the
    no-hop rule at atoms.

    This file: the meaning of targets with branches, and the atoms met far
    along [lbig] ([stuck_at]), which is what the no-hop rule and the
    uniqueness argument look at. *)

From Stdlib Require Import Arith List Lia Bool.
From ShiftedNames.Core Require Import Label Var Adjustment Normalise Unique Layered LayeredUnique.
Import ListNotations.

Lemma list_eq_dec_nil {A} (l : list A) : l = [] \/ l <> [].
Proof. destruct l; [left; reflexivity|right; discriminate]. Qed.

Lemma opt_cases {A} (o : option A) : o = None \/ exists a, o = Some a.
Proof. destruct o; [right; eexists; reflexivity|left; reflexivity]. Qed.

Section Basics.

Variable lenv : list label.

Local Notation lden := (lden lenv).
Local Notation fs := (fs lenv).
Local Notation ft := (ft lenv).
Local Notation fw := (fw lenv).
Local Notation ftl := (ftl lenv).
Local Notation flw := (flw lenv).
Local Notation sget := (sget lenv).
Local Notation latom := (latom lenv).
Local Notation shiftL := (shiftL lenv).
Local Notation lc := (lc lenv).

(** ** Targets with their branch words *)

Definition btres (t : ntgt) : rvar + (nat * option nat * word) :=
  match t with
  | NVar h j => inl (mk_rvar (lden h) j)
  | NBind u w b => inr (u, b, w)
  end.

Definition bres (Sg : seg) (v : rvar) : rvar + (nat * option nat * word) :=
  match sget (v_label v) Sg with
  | Some (ts, m) =>
      if v_index v <? tlen ts then btres (tnth ts (v_index v))
      else inl (mk_rvar (v_label v) (v_index v - tlen ts + m))
  | None => inl v
  end.

Lemma fs_bres Sg K v :
  fs Sg K v = match bres Sg v with inl y => K y | inr (u, b, w) => FTerm u b (fun z => fw w K z) end.
Proof.
  rewrite (fs_get lenv); unfold fget, bres.
  destruct (sget (v_label v) Sg) as [[ts m]|]; [|destruct v; reflexivity].
  destruct (Nat.ltb_spec (v_index v) (tlen ts)) as [Hi|Hi].
  - rewrite (ftl_lt lenv) by exact Hi; destruct (tnth ts (v_index v)); reflexivity.
  - rewrite (ftl_ge lenv) by exact Hi; reflexivity.
Qed.

Lemma bres_sres Sg v y : bres Sg v = inl y <-> LayeredUnique.sres lenv Sg v = inl y.
Proof.
  unfold bres, LayeredUnique.sres; destruct (sget (v_label v) Sg) as [[ts m]|]; [|split; congruence].
  destruct (v_index v <? tlen ts); [|split; congruence].
  destruct (tnth ts (v_index v)); cbn; split; congruence.
Qed.

Lemma bres_ren labs Sg v : sren labs Sg -> bres Sg v = inl (sv lenv Sg v).
Proof.
  intros Hr; unfold bres, sv.
  destruct (sget (v_label v) Sg) as [[ts m]|] eqn:E; [|reflexivity].
  destruct (Nat.ltb_spec (v_index v) (tlen ts)) as [Hlt|Hge]; [|reflexivity].
  pose proof (proj1 (Forall_forall _ _) Hr _ (sget_tgts lenv _ _ _ _ E _ (tnth_in _ _ Hlt))) as Ht.
  destruct (tnth ts (v_index v)) as [h j|]; [reflexivity|destruct Ht].
Qed.

(** A segment has a term. *)
Definition btrm (Sg : seg) : Prop := exists v t, bres Sg v = inr t.

Lemma sren_nobtrm labs Sg : sren labs Sg -> ~ btrm Sg.
Proof. intros Hr [v [t E]]; rewrite (bres_ren _ _ _ Hr) in E; discriminate E. Qed.

(** ** Branch words as layered words *)

Fixpoint wl (w : word) : lword :=
  match w with
  | WEnd s => pre s
  | WAtom s L a w' => wl w' ++ LA L a :: pre s
  | WLay s w' => wl w' ++ [LS s]
  end.

(** The tail: the last segment, after the last atom. *)
Definition wtail (w : word) : seg := match w with WEnd s | WAtom s _ _ _ | WLay s _ => s end.

(** The branch: everything before the tail. *)
Definition wbody (w : word) : lword :=
  match w with WEnd _ => [] | WAtom _ L a w' => wl w' ++ [LA L a] | WLay _ w' => wl w' end.

Lemma flw_app l1 l2 K : flw (l1 ++ l2) K = flw l1 (flw l2 K).
Proof. induction l1 as [|[s|L a] l1 IH]; cbn [app flw]; [reflexivity|rewrite IH; reflexivity|rewrite IH; reflexivity]. Qed.

Lemma flw_pre s K : flw (pre s) K = fs s K.
Proof. destruct s; reflexivity. Qed.

Lemma fw_wl w : forall K, fw w K = flw (wl w) K.
Proof.
  induction w as [s|s L a w IH|s w IH] using word_spine; intros K; cbn [Unique.fw wl].
  - rewrite flw_pre; reflexivity.
  - rewrite IH, flw_app; cbn [flw]; rewrite flw_pre; reflexivity.
  - rewrite IH, flw_app; reflexivity.
Qed.

Lemma fw_body w K : fw w K = flw (wbody w) (fs (wtail w) K).
Proof.
  destruct w as [s|s L a w|s w]; cbn [Unique.fw wbody wtail].
  - reflexivity.
  - rewrite fw_wl, flw_app; reflexivity.
  - apply fw_wl.
Qed.

(** A word ends with an atom. *)
Definition lend (l : lword) : Prop := exists l0 L a, l = l0 ++ [LA L a].

(** Branch words: no layer boundary at the top, and layers only between
    non-empty segments, so that [wl] forgets nothing. *)
Fixpoint wok (w : word) : Prop :=
  match w with
  | WEnd _ => True
  | WAtom _ _ _ w' => wok w'
  | WLay s w' => s <> SNil /\ whead w' <> SNil /\ wok w'
  end.

Definition wtop (w : word) : Prop := match w with WLay _ _ => False | _ => wok w end.

Lemma wbody_shape w : wtop w -> wbody w = [] \/ lend (wbody w).
Proof. destruct w as [s|s L a w|s w]; cbn [wtop wbody]; [left; reflexivity|right; eexists _, _, _; reflexivity|tauto]. Qed.

(** ** The atoms met far along [lbig]

    [stuck_at k j a c]: far along [lbig], the [j]-th atom met is [a], and
    what follows it is [c]. *)

Fixpoint stuck_at (k : rvar -> fres) (j : nat) (a : nat) (c : rvar -> fres) {struct j} : Prop :=
  match j with
  | 0 => False
  | S j' =>
      exists B a0, forall i, B <= i -> exists z k', k (mk_rvar lbig i) = FStuck a0 z k' /\
        match j' with 0 => a0 = a /\ forall y, feq (k' y) (c y) | _ => stuck_at k' j' a c end
  end.

(** What matters is what is met far along: [k] at far indices is [k'] at
    far indices. *)
Definition far_of (k k' : rvar -> fres) : Prop :=
  forall N, exists B, forall i, B <= i -> exists j, N <= j /\ feq (k (mk_rvar lbig i)) (k' (mk_rvar lbig j)).

Lemma stuck_at_cont j : forall k a c, stuck_at k j a c ->
  forall c', (forall y, feq (c y) (c' y)) -> stuck_at k j a c'.
Proof.
  induction j as [|j IH]; intros k a c H c' Hc; [destruct H|].
  destruct H as [B [a0 H]]; exists B, a0; intros i Hi; destruct (H i Hi) as [z [k' [E H']]].
  exists z, k'; split; [exact E|]; destruct j as [|j].
  - destruct H' as [-> H']; split; [reflexivity|intros y; exact (feq_trans _ _ _ (H' y) (Hc y))].
  - exact (IH _ _ _ H' _ Hc).
Qed.

Lemma stuck_at_feq_fn j : forall k k' a c, (forall y, feq (k y) (k' y)) -> stuck_at k' j a c -> stuck_at k j a c.
Proof.
  induction j as [|j IH]; intros k k' a c E H; [destruct H|].
  destruct H as [B [a0 H]]; exists B, a0; intros i Hi; destruct (H i Hi) as [z [k1 [E1 H1]]].
  pose proof (E (mk_rvar lbig i)) as F; rewrite E1 in F.
  destruct (k (mk_rvar lbig i)) as [| |a1 z1 k2] eqn:Ek; cbn [feq] in F; try contradiction.
  destruct F as [-> [-> Fk]]; exists z, k2; split; [reflexivity|]; destruct j as [|j].
  - destruct H1 as [-> H1]; split; [reflexivity|intros y; exact (feq_trans _ _ _ (Fk y) (H1 y))].
  - exact (IH _ _ _ _ Fk H1).
Qed.

Lemma stuck_at_far_of j k k' a c : far_of k k' -> stuck_at k' j a c -> stuck_at k j a c.
Proof.
  destruct j as [|j]; [intros _ []|]; intros Hf [B [a0 H]].
  destruct (Hf B) as [B' HB]; exists B', a0; intros i Hi; destruct (HB i Hi) as [j' [Hj F]].
  destruct (H j' Hj) as [z [k1 [E1 H1]]]; rewrite E1 in F.
  destruct (k (mk_rvar lbig i)) as [| |a1 z1 k2] eqn:Ek; cbn [feq] in F; try contradiction.
  destruct F as [-> [_ Fk]]; exists z1, k2; split; [reflexivity|]; destruct j as [|j].
  - destruct H1 as [-> H1]; split; [reflexivity|intros y; exact (feq_trans _ _ _ (Fk y) (H1 y))].
  - exact (stuck_at_feq_fn _ _ _ _ _ Fk H1).
Qed.

(** The atom met and what follows it are determined. *)
Lemma stuck_at_det j : forall k a c a' c', stuck_at k j a c -> stuck_at k j a' c' ->
  a = a' /\ forall y, feq (c y) (c' y).
Proof.
  induction j as [|j IH]; intros k a c a' c' H H'; [destruct H|].
  destruct H as [B [a0 H]]; destruct H' as [B' [a0' H']].
  destruct (H (B + B') ltac:(lia)) as [z [k1 [E1 H1]]]; destruct (H' (B + B') ltac:(lia)) as [z' [k1' [E1' H1']]].
  rewrite E1 in E1'; injection E1' as <- <- <-; destruct j as [|j].
  - destruct H1 as [<- H1]; destruct H1' as [<- H1']; split; [reflexivity|].
    intros y; exact (feq_trans _ _ _ (feq_sym _ _ (H1 y)) (H1' y)).
  - exact (IH _ _ _ _ _ H1 H1').
Qed.

Lemma far_of_fs s K : far_of (fun v => fs s K v) K.
Proof.
  intros N; destruct (fs_big lenv s K lbig N) as [B HB]; exists B; intros i Hi.
  destruct (HB i Hi) as [j [Hj E]]; exists j; split; [exact Hj|]; rewrite E; apply feq_refl.
Qed.

Lemma far_of_refl k : far_of k k.
Proof. intros N; exists N; intros i Hi; exists i; split; [exact Hi|apply feq_refl]. Qed.

Lemma stuck_at_fs j s K a c : stuck_at K j a c -> stuck_at (fun v => fs s K v) j a c.
Proof. apply stuck_at_far_of, far_of_fs. Qed.

Lemma stuck_at_shift j L K a c : stuck_at K j a c -> stuck_at (fun y => K (shiftL L y)) j a c.
Proof.
  apply stuck_at_far_of; intros N; exists N; intros i Hi; exists (i + lc lbig L); split; [lia|].
  unfold shiftL; cbn [v_label v_index]; apply feq_refl.
Qed.

Lemma stuck_at_latom1 L a K : stuck_at (latom L a K) 1 a (fun z => K (shiftL L z)).
Proof.
  exists (lc lbig L), a; intros i Hi; unfold latom; cbn [v_label v_index].
  rewrite (proj2 (Nat.ltb_ge _ _) Hi); eexists _, _; split; [reflexivity|].
  split; [reflexivity|intros y; apply feq_refl].
Qed.

Lemma stuck_at_latomS j L a0 K a c : stuck_at K j a c -> stuck_at (latom L a0 K) (S j) a c.
Proof.
  intros H; destruct j as [|j]; [destruct H|].
  exists (lc lbig L), a0; intros i Hi; unfold latom; cbn [v_label v_index].
  rewrite (proj2 (Nat.ltb_ge _ _) Hi); eexists _, _; split; [reflexivity|].
  exact (stuck_at_shift _ _ _ _ _ H).
Qed.

(** Far along, a word's atoms come first, then those of what follows. *)
Lemma stuck_at_base l : forall K j a c, stuck_at K j a c -> stuck_at (fun v => flw l K v) (natl l + j) a c.
Proof.
  induction l as [|[s|L a0] r IH]; intros K j a c H; cbn [natl flw].
  - exact H.
  - exact (stuck_at_fs _ _ _ _ _ (IH _ _ _ _ H)).
  - exact (stuck_at_latomS _ _ _ _ _ _ (IH _ _ _ _ H)).
Qed.

Lemma stuck_at_atom l1 L a l2 K :
  stuck_at (fun v => flw (l1 ++ LA L a :: l2) K v) (S (natl l1)) a (fun z => flw l2 K (shiftL L z)).
Proof.
  induction l1 as [|[s|L0 a0] r IH]; cbn [app natl flw].
  - exact (stuck_at_latom1 L a (fun z => flw l2 K z)).
  - exact (stuck_at_fs _ _ _ _ _ IH).
  - exact (stuck_at_latomS _ _ _ _ _ _ IH).
Qed.

Lemma natl_app l1 l2 : natl (l1 ++ l2) = natl l1 + natl l2.
Proof. induction l1 as [|[s|L a] r IH]; cbn [app natl]; [reflexivity|exact IH|rewrite IH; reflexivity]. Qed.

(** The [j]-th atom of a word, counting from its front. *)
Lemma atom_at l j : 1 <= j <= natl l ->
  exists l1 L a l2, l = l1 ++ LA L a :: l2 /\ natl l1 = j - 1.
Proof.
  revert j; induction l as [|[s|L a] r IH]; intros j Hj; cbn [natl] in Hj; [lia| |].
  - destruct (IH j Hj) as [l1 [L [a [l2 [-> E]]]]]; exists (LS s :: l1), L, a, l2; split; [reflexivity|exact E].
  - destruct (Nat.eq_dec j 1) as [->|Hne].
    + exists [], L, a, r; split; reflexivity.
    + destruct (IH (j - 1) ltac:(lia)) as [l1 [L1 [a1 [l2 [-> E]]]]].
      exists (LA L a :: l1), L1, a1, l2; split; [reflexivity|cbn [natl]; lia].
Qed.

End Basics.

(** ** Segments are determined by what they do to each variable *)

Section SegExt.

Variable lenv : list label.
Variable labs : list lexp.
Hypothesis Hinj : forall h h', In h labs -> In h' labs -> lden lenv h = lden lenv h' -> h = h'.

Local Notation lden := (lden lenv).
Local Notation sget := (sget lenv).
Local Notation bres := (bres lenv).

Definition eres (l : option label) (xs : list ntgt) (m j : nat) : rvar + (nat * option nat * word) :=
  if j <? List.length xs then btres lenv (nth j xs (NVar LNone 0)) else inl (mk_rvar l (j - List.length xs + m)).

Definition tlab (t : ntgt) : Prop := match t with NVar h _ => In h labs | NBind _ _ _ => True end.

Lemma btres_inj t t' : tlab t -> tlab t' -> btres lenv t = btres lenv t' -> t = t'.
Proof.
  destruct t as [h j|u w b], t' as [h' j'|u' w' b']; cbn [btres tlab]; try discriminate.
  - intros Hh Hh' E; injection E as E ->; rewrite (Hinj h h' Hh Hh' E); reflexivity.
  - intros _ _ E; injection E as -> -> ->; reflexivity.
Qed.

Lemma eres_short h xs m ys m' :
  In h labs -> Forall tlab ys -> trimmed h ys m' -> List.length xs < List.length ys ->
  (forall j, eres (lden h) xs m j = eres (lden h) ys m' j) -> False.
Proof.
  intros Hh Hp Ht Hlt Heq.
  destruct (@exists_last _ ys) as [ys0 [x Ey]]; [destruct ys; cbn in Hlt; [lia|discriminate]|].
  subst ys; rewrite length_app in Hlt; cbn in Hlt.
  pose proof (Heq (List.length ys0)) as E1; pose proof (Heq (List.length ys0 + 1)) as E2.
  unfold eres in E1, E2; rewrite length_app in E1, E2; cbn [List.length] in E1, E2.
  rewrite (proj2 (Nat.ltb_ge _ _)) in E1 by lia; rewrite (proj2 (Nat.ltb_lt _ _)) in E1 by lia.
  rewrite app_nth2, Nat.sub_diag in E1 by lia; cbn [nth] in E1.
  rewrite !(proj2 (Nat.ltb_ge _ _)) in E2 by lia; injection E2 as E2.
  destruct x as [h' j|u w b]; cbn [btres] in E1; [|discriminate E1]; injection E1 as Eh Ej.
  apply (trimmed_last h ys0 m' _ Ht h' j eq_refl); [lia|].
  apply Hinj; [|exact Hh|exact (eq_sym Eh)].
  rewrite Forall_forall in Hp; apply (Hp (NVar h' j)), in_or_app; right; left; reflexivity.
Qed.

Lemma eres_unique h xs m ys m' :
  In h labs -> Forall tlab xs -> Forall tlab ys -> trimmed h xs m -> trimmed h ys m' ->
  (forall j, eres (lden h) xs m j = eres (lden h) ys m' j) -> xs = ys /\ m = m'.
Proof.
  intros Hh H1 H2 Ht1 Ht2 Heq.
  destruct (Nat.lt_trichotomy (List.length xs) (List.length ys)) as [Hlt|[Hle|Hlt]].
  - exfalso; exact (eres_short h xs m ys m' Hh H2 Ht2 Hlt Heq).
  - split.
    + apply (nth_ext _ _ (NVar LNone 0) (NVar LNone 0) Hle); intros j Hj.
      pose proof (Heq j) as E; unfold eres in E; rewrite !(proj2 (Nat.ltb_lt _ _)) in E by lia.
      rewrite Forall_forall in H1, H2; apply btres_inj; [apply H1, nth_In; lia|apply H2, nth_In; lia|exact E].
    + pose proof (Heq (List.length xs)) as E; unfold eres in E; rewrite !(proj2 (Nat.ltb_ge _ _)) in E by lia.
      injection E as E; lia.
  - exfalso; apply (eres_short h ys m' xs m Hh H1 Ht1 Hlt); intros j; symmetry; apply Heq.
Qed.

Lemma eres_not_id h ys m :
  In h labs -> Forall tlab ys -> trimmed h ys m -> (ys <> [] \/ m <> 0) ->
  ~ (forall j, eres (lden h) ys m j = inl (mk_rvar (lden h) j)).
Proof.
  intros Hh Hp Ht Hne Heq; destruct ys as [|y ys].
  - destruct Hne as [Hne|Hne]; [congruence|]; pose proof (Heq 0) as E; unfold eres in E; cbn in E.
    injection E as E; lia.
  - apply (eres_short h [] 0 (y :: ys) m Hh Hp Ht ltac:(cbn; lia)); intros j.
    rewrite Heq; unfold eres; cbn [List.length]; rewrite (proj2 (Nat.ltb_ge j 0)) by lia; do 2 f_equal; lia.
Qed.

Lemma bres_eres Sg l j :
  bres Sg (mk_rvar l j) = match sget l Sg with Some (ts, m) => eres l (tl_list ts) m j | None => inl (mk_rvar l j) end.
Proof.
  unfold bres, eres; cbn [v_label v_index]; destruct (sget l Sg) as [[ts m]|]; [|reflexivity].
  rewrite <- tlen_list, <- tnth_list; reflexivity.
Qed.

Lemma sget_cons_eq l h ts m r :
  sget l (SEnt h ts m r) = if label_eqb (lden h) l then Some (ts, m) else sget l r.
Proof. reflexivity. Qed.

Theorem seg_ext Sg Sg' : sshape lenv labs false Sg -> sshape lenv labs false Sg' ->
  Forall tlab (stgts Sg) -> Forall tlab (stgts Sg') -> (forall x, bres Sg x = bres Sg' x) -> Sg = Sg'.
Proof.
  assert (Heq' : forall Sg Sg', (forall x, bres Sg x = bres Sg' x) ->
            forall l j, (match sget l Sg with Some (ts, m) => eres l (tl_list ts) m j | None => inl (mk_rvar l j) end)
                      = (match sget l Sg' with Some (ts, m) => eres l (tl_list ts) m j | None => inl (mk_rvar l j) end)).
  { intros S1 S2 H l j; rewrite <- !bres_eres; apply H. }
  intros Hs Hs' Hp Hp' Heq; specialize (Heq' _ _ Heq); clear Heq.
  revert Sg' Hs Hs' Hp Hp' Heq'; induction Sg as [|h ts m r IH] using seg_spine;
    intros Sg' [Hs Ho] [Hs' Ho'] Hp Hp' Heq; destruct Sg' as [|h' ts' m' r']; [reflexivity| | |].
  - exfalso; cbn [sents] in Ho'; inversion Ho' as [|e l He]; subst; cbn [eshape] in He.
    destruct He as [Hh [Ht [Hne _]]]; rewrite stgts_cons, Forall_app in Hp'.
    apply (eres_not_id h' (tl_list ts') m' Hh (proj1 Hp') Ht Hne); intros j.
    pose proof (Heq (lden h') j) as E; rewrite sget_cons_eq, label_eqb_refl in E; symmetry; exact E.
  - exfalso; cbn [sents] in Ho; inversion Ho as [|e l He]; subst; cbn [eshape] in He.
    destruct He as [Hh [Ht [Hne _]]]; rewrite stgts_cons, Forall_app in Hp.
    apply (eres_not_id h (tl_list ts) m Hh (proj1 Hp) Ht Hne); intros j.
    pose proof (Heq (lden h) j) as E; rewrite sget_cons_eq, label_eqb_refl in E; exact E.
  - cbn [sents] in *; inversion Hs as [|e l Hsr Hall]; inversion Hs' as [|e' l' Hsr' Hall']; subst.
    inversion Ho as [|e l He Hor]; inversion Ho' as [|e' l' He' Hor']; subst.
    rewrite Forall_forall in Hall, Hall'; cbn [eshape] in He, He'.
    rewrite stgts_cons, Forall_app in Hp, Hp'.
    destruct (olabel_trichotomy (lden h) (lden h')) as [Hlt|[Eh|Hlt]].
    + exfalso; destruct He as [Hh [Ht [Hne _]]].
      apply (eres_not_id h (tl_list ts) m Hh (proj1 Hp) Ht Hne); intros j.
      pose proof (Heq (lden h) j) as E; rewrite !sget_cons_eq, label_eqb_refl in E; rewrite E.
      destruct (label_eqb_spec (lden h') (lden h)) as [E'|_]; [rewrite E' in Hlt; destruct (olabel_lt_irrefl _ Hlt)|].
      rewrite (sget_above lenv); [reflexivity|]; intros e0 Hi; exact (olabel_lt_trans _ _ _ Hlt (Hall' e0 Hi)).
    + destruct He as [Hh [Ht _]]; destruct He' as [Hh' [Ht' _]].
      assert (Ehh : h = h') by (apply Hinj; assumption); subst h'.
      assert (Ee : tl_list ts = tl_list ts' /\ m = m').
      { apply (eres_unique h _ _ _ _ Hh (proj1 Hp) (proj1 Hp') Ht Ht'); intros j.
        pose proof (Heq (lden h) j) as E; rewrite !sget_cons_eq, label_eqb_refl in E; exact E. }
      destruct Ee as [Et <-]; rewrite <- (tl_of_list ts), <- (tl_of_list ts'), Et; f_equal.
      apply IH; [split; assumption|split; assumption|exact (proj2 Hp)|exact (proj2 Hp')|]; intros l j.
      pose proof (Heq l j) as E; rewrite !sget_cons_eq in E.
      destruct (label_eqb_spec (lden h) l) as [<-|_]; [|exact E].
      rewrite !(sget_above lenv); [reflexivity| |]; intros e0 Hi; first [apply Hall; exact Hi|apply Hall'; exact Hi].
    + exfalso; destruct He' as [Hh [Ht [Hne _]]].
      apply (eres_not_id h' (tl_list ts') m' Hh (proj1 Hp') Ht Hne); intros j.
      pose proof (Heq (lden h') j) as E; rewrite !sget_cons_eq, label_eqb_refl in E; rewrite <- E.
      destruct (label_eqb_spec (lden h) (lden h')) as [E'|_]; [rewrite E' in Hlt; destruct (olabel_lt_irrefl _ Hlt)|].
      rewrite (sget_above lenv); [reflexivity|]; intros e0 Hi; exact (olabel_lt_trans _ _ _ Hlt (Hall e0 Hi)).
Qed.

End SegExt.

(** ** The conditions *)

Section Conditions.

Variable lenv : list label.
Variable labs : list lexp.

Local Notation lden := (lden lenv).
Local Notation fs := (fs lenv).
Local Notation fw := (fw lenv).
Local Notation flw := (flw lenv).
Local Notation bres := (bres lenv).
Local Notation shiftL := (shiftL lenv).
Local Notation lc := (lc lenv).

Variable gt : (rvar -> fres) -> (rvar -> fres) -> Prop.
Variable route : (rvar -> fres) -> rvar -> rvar -> Prop.

(** The inputs that are observed: all, or the named ones and the first
    [n] bound ones (the others are phantoms: bound inputs of a payload
    without a payload atom, before its first atom). *)
Definition dom (p : option nat) (v : rvar) : Prop :=
  match p with None => True | Some n => named v \/ v_index v < n end.

(** Phantoms are only shifted. *)
Definition phant (p p' : option nat) (Sg : seg) : Prop :=
  match p, p' with
  | None, None => True
  | Some n, Some n' => forall i, bres Sg (mk_rvar None (n + i)) = inl (mk_rvar None (n' + i))
  | _, _ => False
  end.

(** Where the variable [y] is sent to a term in the first stretch of [r]:
    the rest after that term's segment, and the term. *)
Fixpoint treach (r : lword) (y : rvar) : option (lword * (nat * option nat * word)) :=
  match r with
  | LS s :: r' => match bres s y with inl y' => treach r' y' | inr t => Some (r', t) end
  | _ => None
  end.

(** No hop: a term that the rest after an atom sends a lifted input to
    does not have, as the last atom of its branch, this atom with what the
    line does after it. *)
Definition nohop (K : rvar -> fres) (L : list (lexp * nat)) (a : nat) (r : lword) : Prop :=
  forall y u b k d e, v_index y < lc (v_label y) L -> flw r K y = FTerm u b k -> deep d k -> deep e K ->
    natl r + e < d -> ~ stuck_at k (d - natl r - e) a (fun z => flw r K (shiftL L z)).

Definition bdom (b : option nat) : option nat := match b with None => Some 0 | Some _ => None end.

(** A term's branch word, over [K0], what follows the term's segment. *)
Definition brok (bp : (rvar -> fres) -> option nat -> lword -> Prop) (K0 : rvar -> fres) (b : option nat) (w : word) : Prop :=
  wtop w /\ psok lenv labs (wtail w)
  /\ ((b <> None \/ wbody w <> []) -> forall i, routed K0 (sv lenv (wtail w) (mk_rvar None i)))
  /\ (b = None -> wbody w = [] -> wtail w = SNil)
  /\ (wbody w <> [] -> bp (fs (wtail w) K0) (bdom b) (wbody w)).

(** What uses a bound variable of the rest: an input of the segment, or
    the tail of a term whose payload sees bound variables. *)
Inductive user : Type := UIn (x : rvar) | UTl (x : rvar) (i : nat).

Definition live (b : option nat) (w : word) : Prop := b <> None \/ wbody w <> [].

Definition uhit (Sg : seg) (a : user) (j : nat) : Prop :=
  match a with
  | UIn x => bres Sg x = inl (mk_rvar None j)
  | UTl x i => exists u b w, bres Sg x = inr (u, b, w) /\ live b w /\ sv lenv (wtail w) (mk_rvar None i) = mk_rvar None j
  end.

(** Users in order: observed inputs, then tails, then phantoms. *)
Definition ult (p : option nat) (a a' : user) : Prop :=
  match a, a' with
  | UIn x, UIn x' => (dom p x /\ ~ dom p x') \/ ((dom p x <-> dom p x') /\ vlt x x')
  | UIn x, UTl _ _ => dom p x
  | UTl _ _, UIn x' => ~ dom p x'
  | UTl x i, UTl x' i' => vlt x x' \/ (x = x' /\ i < i')
  end.

(** Bound variables of the rest are numbered by their first user. *)
Definition unum (p : option nat) (Sg : seg) : Prop :=
  forall a a' i j, uhit Sg a i -> uhit Sg a' j -> i < j ->
    exists a0, uhit Sg a0 i /\ forall a'', uhit Sg a'' j -> ult p a0 a''.

Record bsegok (bp : (rvar -> fres) -> option nat -> lword -> Prop) (K : rvar -> fres) (p p' : option nat)
    (Sg : seg) (r : lword) : Prop := {
  bo_shape : sshape lenv labs false Sg;
  bo_tlab : Forall (tlab labs) (stgts Sg);
  bo_order : forall y rt t, treach r y = Some (rt, t) -> gt (flw r K) (flw rt K);
  bo_last : forall G, r = [LS G] -> keq (flw r K) K -> btrm lenv G;
  bo_route : forall x y, dom p x -> bres Sg x = inl y -> route (flw r K) x y;
  bo_real : forall x y, dom p x -> bres Sg x = inl y -> dom p' y;
  bo_phant : phant p p' Sg;
  bo_hit : r <> [] -> forall j, dom p' (mk_rvar None j) ->
    (exists x, dom p x /\ bres Sg x = inl (mk_rvar None j)) \/ (exists x i, uhit Sg (UTl x i) j);
  bo_treal : forall x i j, uhit Sg (UTl x i) j -> dom p' (mk_rvar None j);
  bo_binj : binj (flw r K);
  bo_num : r <> [] -> unum p Sg;
  bo_br : forall x u b w, bres Sg x = inr (u, b, w) -> brok bp (flw r K) b w
}.

(** A renaming segment: at the end of the line, or in lift position
    before an atom. *)
Definition renok (p p' : option nat) (Sg : seg) (r : lword) : Prop :=
  sshape lenv labs false Sg /\ sren labs Sg /\ phant p p' Sg
  /\ (forall x y, dom p x -> bres Sg x = inl y -> dom p' y)
  /\ (r = [] \/ exists L a r2, r = LA L a :: r2 /\ lpos lenv Sg L
        /\ forall y, bound y -> dom p' y -> p' <> None -> exists x, dom p x /\ bres Sg x = inl y).

Fixpoint lnfL (bp : (rvar -> fres) -> option nat -> lword -> Prop) (K : rvar -> fres) (p : option nat) (l : lword)
    {struct l} : Prop :=
  match l with
  | [] => True
  | LS Sg :: r =>
      Sg <> SNil /\ exists p', lnfL bp K p' r /\ ((btrm lenv Sg /\ bsegok bp K p p' Sg r) \/ renok p p' Sg r)
  | LA L a :: r =>
      lok lenv labs L /\ (match p with None => True | Some n => lc None L <= n end)
      /\ lnfL bp K None r /\ nohop K L a r
  end.

(** [n] bounds how deep branches nest. *)
Fixpoint lnfB (n : nat) (K : rvar -> fres) (p : option nat) (l : lword) {struct n} : Prop :=
  lnfL (match n with 0 => fun _ _ _ => False | S n' => lnfB n' end) K p l.

End Conditions.

(** ** Facts about the conditions *)

Section Facts.

Variable lenv : list label.
Variable labs : list lexp.

Local Notation lden := (lden lenv).
Local Notation fs := (fs lenv).
Local Notation fw := (fw lenv).
Local Notation flw := (flw lenv).
Local Notation bres := (bres lenv).
Local Notation shiftL := (shiftL lenv).
Local Notation lc := (lc lenv).
Local Notation latom := (latom lenv).

Lemma far_of_trans k1 k2 k3 : far_of k1 k2 -> far_of k2 k3 -> far_of k1 k3.
Proof.
  intros H12 H23 N; destruct (H23 N) as [B2 HB2]; destruct (H12 B2) as [B1 HB1]; exists B1; intros i Hi.
  destruct (HB1 i Hi) as [j [Hj F1]]; destruct (HB2 j Hj) as [j' [Hj' F2]]; exists j'; split; [exact Hj'|].
  exact (feq_trans _ _ _ F1 F2).
Qed.

Lemma far_of_feq k k' : (forall i, feq (k (mk_rvar lbig i)) (k' (mk_rvar lbig i))) -> far_of k k'.
Proof. intros H N; exists N; intros i Hi; exists i; split; [exact Hi|apply H]. Qed.

Lemma deep_feq d : forall k k', (forall i, feq (k (mk_rvar lbig i)) (k' (mk_rvar lbig i))) -> deep d k -> deep d k'.
Proof.
  destruct d as [|d]; intros k k' E; cbn [deep].
  - intros [B H]; exists B; intros i Hi; destruct (H i Hi) as [y Ey]; pose proof (E i) as F; rewrite Ey in F.
    destruct (k' (mk_rvar lbig i)) as [y'| |]; cbn [feq] in F; [exists y'; reflexivity|contradiction|contradiction].
  - intros [B [a H]]; exists B, a; intros i Hi; destruct (H i Hi) as [z [k1 [Ek Hd]]]; pose proof (E i) as F.
    rewrite Ek in F; destruct (k' (mk_rvar lbig i)) as [| |a' z' k1'] eqn:Ek'; cbn [feq] in F; try contradiction.
    destruct F as [<- [<- F]]; exists z, k1'; split; [reflexivity|].
    clear -F Hd; revert k1 k1' F Hd; induction d as [|d IH]; intros k1 k1' F; cbn [deep].
    + intros [B H]; exists B; intros i Hi; destruct (H i Hi) as [y Ey]; pose proof (F (mk_rvar lbig i)) as G; rewrite Ey in G.
      destruct (k1' (mk_rvar lbig i)) as [y'| |]; cbn [feq] in G; [exists y'; reflexivity|contradiction|contradiction].
    + intros [B [a H]]; exists B, a; intros i Hi; destruct (H i Hi) as [z [k2 [Ek Hd]]].
      pose proof (F (mk_rvar lbig i)) as G; rewrite Ek in G.
      destruct (k1' (mk_rvar lbig i)) as [| |a' z' k2']; cbn [feq] in G; try contradiction.
      destruct G as [<- [<- G]]; exists z, k2'; split; [reflexivity|exact (IH _ _ G Hd)].
Qed.

(** Where a term that a word sends a variable to comes from: a segment of
    its first stretch, a lifted input of an atom, or what follows the
    word. *)
Lemma flw_ls s r K y : flw (LS s :: r) K y = fs s (flw r K) y.
Proof. reflexivity. Qed.

Lemma treach_term r K y rt u b w : treach lenv r y = Some (rt, (u, b, w)) ->
  flw r K y = FTerm u b (fw w (flw rt K)) /\ natl rt = natl r
  /\ exists r0, r = r0 ++ rt /\ Forall (fun st => match st with LS _ => True | LA _ _ => False end) r0.
Proof.
  revert y; induction r as [|[s|L a] r IH]; intros y; cbn [treach]; try discriminate.
  rewrite flw_ls, fs_bres; destruct (bres s y) as [y'|[[u' b'] w']].
  - intros H; destruct (IH y' H) as [E [En [r0 [Er Hr0]]]]; split; [exact E|split; [exact En|]].
    exists (LS s :: r0); split; [rewrite Er; reflexivity|constructor; [exact I|exact Hr0]].
  - intros H; injection H as <- <- <- <-; split; [reflexivity|split; [reflexivity|]].
    exists [LS s]; split; [reflexivity|constructor; [exact I|constructor]].
Qed.

Lemma far_of_segs r0 rt K : Forall (fun st => match st with LS _ => True | LA _ _ => False end) r0 ->
  far_of (flw (r0 ++ rt) K) (flw rt K).
Proof.
  induction r0 as [|[s|L a] r0 IH]; intros H; cbn [app].
  - apply far_of_refl.
  - inversion H as [|? ? _ H']; subst; exact (far_of_trans _ _ _ (far_of_fs lenv s _) (IH H')).
  - inversion H as [|? ? Hc _]; destruct Hc.
Qed.

Lemma tsrc m K x u b k : flw m K x = FTerm u b k ->
  (exists rt w, treach lenv m x = Some (rt, (u, b, w)) /\ k = fw w (flw rt K))
  \/ (exists m1 L a l1 y, m = m1 ++ LA L a :: l1 /\ natl m1 = 0 /\ v_index y < lc (v_label y) L
        /\ flw l1 K y = FTerm u b k)
  \/ (natl m = 0 /\ exists y, K y = FTerm u b k).
Proof.
  revert x; induction m as [|[s|L a] r IH]; intros x E.
  - right; right; split; [reflexivity|exists x; exact E].
  - rewrite flw_ls, fs_bres in E; cbn [treach natl].
    destruct (bres s x) as [y|[[u' b'] w']].
    + destruct (IH y E) as [H|[[m1 [L [a [l1 [y' [-> [Hm [Hy E']]]]]]]]|H]].
      * left; exact H.
      * right; left; exists (LS s :: m1), L, a, l1, y'; repeat split; assumption.
      * right; right; exact H.
    + injection E as <- <- <-; left; exists r, w'; split; reflexivity.
  - cbn [flw] in E; unfold Unique.latom in E.
    destruct (Nat.ltb_spec (v_index x) (lc (v_label x) L)) as [Hl|Hl]; [|discriminate E].
    right; left; exists [], L, a, r, x; repeat split; [exact Hl|exact E].
Qed.

End Facts.

Section Facts2.

Variable lenv : list label.
Variable labs : list lexp.
Variable gt : (rvar -> fres) -> (rvar -> fres) -> Prop.
Variable route : (rvar -> fres) -> rvar -> rvar -> Prop.

Local Notation fs := (fs lenv).
Local Notation fw := (fw lenv).
Local Notation flw := (flw lenv).
Local Notation bres := (bres lenv).
Local Notation shiftL := (shiftL lenv).
Local Notation lc := (lc lenv).

(** The free meaning depends on the continuation only up to [feq]. *)
Lemma f_cong :
  (forall t K1 K2, (forall y, feq (K1 y) (K2 y)) -> feq (Unique.ft lenv t K1) (Unique.ft lenv t K2))
  /\ (forall ts l m K1 K2 i, (forall y, feq (K1 y) (K2 y)) -> feq (Unique.ftl lenv ts l m K1 i) (Unique.ftl lenv ts l m K2 i))
  /\ (forall s K1 K2 v, (forall y, feq (K1 y) (K2 y)) -> feq (fs s K1 v) (fs s K2 v))
  /\ (forall w K1 K2 v, (forall y, feq (K1 y) (K2 y)) -> feq (fw w K1 v) (fw w K2 v)).
Proof.
  apply nf_mind.
  - intros h j K1 K2 H; apply H.
  - intros u w IH b K1 K2 H; cbn [Unique.ft feq]; split; [reflexivity|split; [reflexivity|]]; intros y _; apply IH, H.
  - intros l m K1 K2 i H; apply H.
  - intros t IHt r IHr l m K1 K2 [|i] H; [apply IHt, H|apply IHr, H].
  - intros K1 K2 v H; apply H.
  - intros h ts IHts m r IHr K1 K2 v H; cbn [Unique.fs]; destruct (label_eqb _ _); [apply IHts, H|apply IHr, H].
  - intros s IH K1 K2 v H; apply IH, H.
  - intros s IHs L a w IHw K1 K2 v H; cbn [Unique.fw]; apply IHw; intros y; unfold Unique.latom.
    destruct (_ <? _); [apply IHs, H|cbn [feq]; split; [reflexivity|split; [reflexivity|]]; intros z; apply IHs, H].
  - intros s IHs w IHw K1 K2 v H; cbn [Unique.fw]; apply IHw; intros y; apply IHs, H.
Qed.

Lemma flw_cong l : forall K1 K2 v, (forall y, feq (K1 y) (K2 y)) -> feq (flw l K1 v) (flw l K2 v).
Proof.
  induction l as [|[s|L a] r IH]; intros K1 K2 v H; cbn [flw].
  - apply H.
  - apply (proj1 (proj2 (proj2 f_cong))); intros y; apply IH, H.
  - unfold Unique.latom; destruct (_ <? _); [apply IH, H|cbn [feq]; split; [reflexivity|split; [reflexivity|]]; intros z; apply IH, H].
Qed.

(** *** Branch words are determined by their body and tail *)

Lemma wl_head w : wok w -> whead w <> SNil -> exists l0, wl w = l0 ++ [LS (whead w)].
Proof.
  destruct w as [s|s L a w|s w]; cbn [wl whead wok]; intros _ Hs.
  - exists []; destruct s; [destruct (Hs eq_refl)|reflexivity].
  - exists (wl w ++ [LA L a]); destruct s; [destruct (Hs eq_refl)|]; rewrite <- app_assoc; reflexivity.
  - exists (wl w); reflexivity.
Qed.

Lemma wl_atom s L a w : wl (WAtom s L a w) =
  match s with SNil => wl w ++ [LA L a] | _ => (wl w ++ [LA L a]) ++ [LS s] end.
Proof. cbn [wl]; destruct s; [reflexivity|rewrite <- app_assoc; reflexivity]. Qed.

Lemma snoc_neq {A} (l1 l2 : list A) x y : x <> y -> l1 ++ [x] <> l2 ++ [y].
Proof. intros H E; apply app_inj_tail in E; exact (H (proj2 E)). Qed.

Ltac lenx E := solve [apply (f_equal (@List.length lstep)) in E; cbn in E; rewrite ?length_app in E; cbn in E; lia
  | apply (snoc_neq [] _ _ _ ltac:(discriminate)) in E; destruct E
  | apply eq_sym, (snoc_neq [] _ _ _ ltac:(discriminate)) in E; destruct E
  | match type of E with context [wl ?w0] =>
      destruct (wl w0); cbn in E; [discriminate E|];
      apply (f_equal (@List.length lstep)) in E; cbn in E; rewrite ?length_app in E; cbn in E; lia end].

Lemma wl_inj w : forall w', wok w -> wok w' -> wl w = wl w' -> w = w'.
Proof.
  induction w as [s|s L a w IH|s w IH] using word_spine; intros w' Hw Hw' E;
    destruct w' as [s'|s' L' a' w'|s' w']; try rewrite !wl_atom in E; cbn [wl wok] in *.
  - destruct s, s'; cbn in E; congruence.
  - exfalso; destruct s as [|h ts m r], s' as [|h' ts' m' r']; cbn [pre] in E; lenx E.
  - exfalso; destruct Hw' as [_ [Hh Hw2]]; destruct (wl_head w' Hw2 Hh) as [l0 El]; rewrite El in E.
    destruct s as [|h ts m r]; cbn [pre] in E; lenx E.
  - exfalso; destruct s as [|h ts m r], s' as [|h' ts' m' r']; cbn [pre] in E; lenx E.
  - destruct s as [|h ts m r], s' as [|h' ts' m' r']; cbn beta iota in E.
    + apply app_inj_tail in E as [E E']; injection E' as -> ->; f_equal; apply IH; assumption.
    + exfalso; apply app_inj_tail in E as [_ E]; discriminate E.
    + exfalso; apply app_inj_tail in E as [_ E]; discriminate E.
    + apply app_inj_tail in E as [E E']; injection E' as -> -> -> ->; apply app_inj_tail in E as [E E'].
      injection E' as -> ->; f_equal; apply IH; assumption.
  - exfalso; destruct Hw' as [_ [Hh Hw2]]; destruct (wl_head w' Hw2 Hh) as [l0 El]; rewrite El in E.
    destruct s as [|h ts m r]; cbn beta iota in E.
    + apply app_inj_tail in E as [_ E]; discriminate E.
    + apply app_inj_tail in E as [E _]; apply app_inj_tail in E as [_ E]; discriminate E.
  - exfalso; destruct Hw as [_ [Hh Hw2]]; destruct (wl_head w Hw2 Hh) as [l0 El]; rewrite El in E.
    destruct s' as [|h ts m r]; cbn [pre] in E; lenx E.
  - exfalso; destruct Hw as [_ [Hh Hw2]]; destruct (wl_head w Hw2 Hh) as [l0 El]; rewrite El in E.
    destruct s' as [|h ts m r]; cbn beta iota in E.
    + apply app_inj_tail in E as [_ E]; discriminate E.
    + apply app_inj_tail in E as [E _]; apply app_inj_tail in E as [_ E]; discriminate E.
  - apply app_inj_tail in E as [E E']; injection E' as ->; f_equal; apply IH; tauto.
Qed.

Lemma w_inj w w' : wtop w -> wtop w' -> wbody w = wbody w' -> wtail w = wtail w' -> w = w'.
Proof.
  destruct w as [s|s L a w|s w], w' as [s'|s' L' a' w'|s' w']; cbn [wtop wbody wtail]; try tauto.
  - intros _ _ _ ->; reflexivity.
  - intros _ _ E; destruct (wl w'); discriminate E.
  - intros _ _ E; destruct (wl w); discriminate E.
  - intros Hw Hw' E ->; apply app_inj_tail in E as [E E']; injection E' as -> ->; f_equal; apply wl_inj; assumption.
Qed.

(** *** What the conditions give *)

Lemma nohop_at bp K p m1 L a l1 :
  lnfL lenv labs gt route bp K p (m1 ++ LA L a :: l1) -> nohop lenv K L a l1.
Proof.
  revert p; induction m1 as [|[s|L0 a0] m1 IH]; intros p H; cbn [app lnfL] in H.
  - tauto.
  - destruct H as [_ [p' [H _]]]; exact (IH _ H).
  - destruct H as [_ [_ [H _]]]; exact (IH _ H).
Qed.

Lemma treach_brok bp K p l y rt u b w :
  lnfL lenv labs gt route bp K p l -> treach lenv l y = Some (rt, (u, b, w)) -> brok lenv labs bp (flw rt K) b w.
Proof.
  revert p y; induction l as [|[s|L a] r IH]; intros p y H E; cbn [treach] in E; try discriminate.
  destruct H as [_ [p' [Hr [[_ HS]|[_ [Hren _]]]]]].
  - destruct (bres s y) as [y'|t] eqn:Ey; [exact (IH _ _ Hr E)|injection E as -> ->].
    exact (bo_br _ _ _ _ _ _ _ _ _ _ HS y u b w Ey).
  - rewrite (bres_ren lenv labs s y Hren) in E; exact (IH _ _ Hr E).
Qed.

Lemma phant_dom p p' Sg x t : phant lenv p p' Sg -> bres Sg x = inr t -> dom p x.
Proof.
  destruct p as [n|]; [|intros _ _; exact I]; destruct p' as [n'|]; [|intros []].
  intros Hp E; destruct (named_or_bound x) as [Hx|Hx]; [left; exact Hx|right].
  destruct (Nat.lt_ge_cases (v_index x) n) as [Hi|Hi]; [exact Hi|exfalso].
  destruct x as [l i]; unfold bound in Hx; cbn in Hx, Hi; subst l.
  pose proof (Hp (i - n)) as E'; replace (n + (i - n)) with i in E' by lia; rewrite E in E'; discriminate E'.
Qed.

Lemma lend_cons st r : lend (st :: r) -> r <> [] -> lend r.
Proof.
  intros [l0 [L [a E]]] Hr; destruct l0 as [|st0 l0]; cbn in E; injection E as _ E; [congruence|].
  exists l0, L, a; exact E.
Qed.

Lemma lend_natl l : lend l -> 1 <= natl l.
Proof. intros [l0 [L [a ->]]]; rewrite natl_app; cbn; lia. Qed.

Lemma lend_nil : ~ lend [].
Proof. intros [l0 [L [a E]]]; destruct l0; discriminate E. Qed.

Lemma deep_fw_body w K e : deep e K -> deep (natl (wbody w) + e) (fw w K).
Proof. intros H; rewrite fw_body; apply deep_flw, deep_fs, H. Qed.

Lemma nstuck_fw_body w K e : nstuck e K -> deep e K -> nstuck (natl (wbody w) + e) (fw w K).
Proof. intros Hn Hd; rewrite fw_body; apply nstuck_flw; [apply nstuck_fs, Hn|apply deep_fs, Hd]. Qed.

(** *** A term in the first stretch of one word against one past an atom
    of the other

    Far along [lbig] the payload meets its branch's atoms, then the atoms
    of the first word; the latter are the atoms of the second word, with
    the same continuations.  So the branch of the term in the second word
    ends with the atom it is lifted around, with that atom's continuation:
    the no-hop rule fails there. *)

Lemma cross bp' K K' p' l m e x u b w rt u' b' k' m1 L a l1 y :
  lnfL lenv labs gt route bp' K' p' m -> natl l = natl m -> deep e K -> deep e K' ->
  (forall i, feq (flw l K (mk_rvar lbig i)) (flw m K' (mk_rvar lbig i))) ->
  treach lenv l x = Some (rt, (u, b, w)) -> wtop w ->
  m = m1 ++ LA L a :: l1 -> natl m1 = 0 -> v_index y < lc (v_label y) L -> flw l1 K' y = FTerm u' b' k' ->
  feq (FTerm u b (fw w (flw rt K))) (FTerm u' b' k') -> False.
Proof.
  intros Hm Hn He He' E Ht Hw Em Hm1 Hy Ek F.
  destruct (treach_term lenv l K x rt u b w Ht) as [_ [Hnr [r0 [Er Hr0]]]].
  assert (Hnm : natl m = S (natl l1)) by (rewrite Em, natl_app; cbn [natl]; lia).
  (* The first atom of [m], and of [l]. *)
  set (cm := fun z => flw l1 K' (shiftL L z)).
  assert (Sm : stuck_at (flw m K') 1 a cm).
  { rewrite Em; pose proof (stuck_at_atom lenv m1 L a l1 K') as S; rewrite Hm1 in S; exact S. }
  assert (Sl : stuck_at (flw l K) 1 a cm) by exact (stuck_at_far_of _ _ _ _ _ (far_of_feq _ _ E) Sm).
  assert (Srt : stuck_at (flw rt K) 1 a cm).
  { destruct (atom_at rt 1 ltac:(lia)) as [rt1 [L' [a' [rt2 [Ert Hrt1]]]]].
    pose proof (stuck_at_atom lenv rt1 L' a' rt2 K) as S; rewrite <- Ert in S.
    replace (Datatypes.S (natl rt1)) with 1 in S by lia.
    assert (Hf : far_of (flw l K) (flw rt K)) by (rewrite Er; exact (far_of_segs lenv r0 rt K Hr0)).
    pose proof (stuck_at_far_of _ _ _ _ _ Hf S) as S'.
    destruct (stuck_at_det _ _ _ _ _ _ S' Sl) as [-> Hc].
    exact (stuck_at_cont _ _ _ _ S _ Hc). }
  (* What the term meets far along. *)
  set (P := wbody w).
  assert (Sk : stuck_at (fw w (flw rt K)) (natl P + 1) a cm).
  { rewrite fw_body; exact (stuck_at_base lenv P _ 1 a cm (stuck_at_fs lenv 1 _ _ _ _ Srt)). }
  cbn [feq] in F; destruct F as [<- [<- Fk]].
  assert (Fb : forall i, feq (fw w (flw rt K) (mk_rvar lbig i)) (k' (mk_rvar lbig i))) by (intros i; apply Fk; intros _; discriminate).
  assert (Sk' : stuck_at k' (natl P + 1) a cm).
  { refine (stuck_at_far_of _ _ _ _ _ _ Sk); intros N; exists N; intros i Hi; exists i; split; [exact Hi|].
    apply feq_sym, Fb. }
  assert (Dk' : deep (natl P + natl rt + e) k').
  { apply (deep_feq _ _ _ Fb); replace (natl P + natl rt + e) with (natl (wbody w) + (natl rt + e)) by (unfold P; lia).
    apply deep_fw_body, deep_flw, He. }
  apply (nohop_at bp' K' p' m1 L a l1 ltac:(rewrite <- Em; exact Hm) y u b k' (natl P + natl rt + e) e Hy Ek Dk' He');
    [lia|].
  replace (natl P + natl rt + e - natl l1 - e) with (natl P + 1) by lia; exact Sk'.
Qed.


End Facts2.

(** ** Uniqueness *)

Section Main.

Variable lenv : list label.
Variable labs : list lexp.
Hypothesis Hinj : forall h h', In h labs -> In h' labs -> lden lenv h = lden lenv h' -> h = h'.

Local Notation fs := (fs lenv).
Local Notation fw := (fw lenv).
Local Notation flw := (flw lenv).
Local Notation bres := (bres lenv).
Local Notation shiftL := (shiftL lenv).
Local Notation lc := (lc lenv).
Local Notation sv := (sv lenv).

Variable gt : (rvar -> fres) -> (rvar -> fres) -> Prop.
Hypothesis gt_irrefl : forall k k', keq k k' -> ~ gt k k'.
Hypothesis gt_trans : forall k1 k2 k3, gt k1 k2 -> gt k2 k3 -> gt k1 k3.
Hypothesis gt_keq : forall k1 k1' k2 k2', keq k1 k1' -> keq k2 k2' -> gt k1 k2 -> gt k1' k2'.
Variable route : (rvar -> fres) -> rvar -> rvar -> Prop.
Hypothesis route_uniq : forall k k' x y y', keq k k' -> route k x y -> route k' x y' ->
  feq (k y) (k' y') -> named y -> y = y'.

(** Branches one level down are unique. *)
Variable bp : (rvar -> fres) -> option nat -> lword -> Prop.
Hypothesis IHb : forall l m K K' p e, bp K p l -> bp K' p m -> natl l = natl m ->
  deep e K -> nstuck e K -> deep e K' -> nstuck e K' -> lend l -> lend m ->
  (forall v, dom p v -> feq (flw l K v) (flw m K' v)) -> l = m /\ forall v, feq (K v) (K' v).

Local Notation lnfL := (lnfL lenv labs gt route bp).
Local Notation brok := (brok lenv labs bp).

Lemma psok_keq s K : psok lenv labs s -> keq (fs s K) K.
Proof. intros [_ [Hr Hn]] y Hy; rewrite (fs_ren lenv labs) by exact Hr; rewrite (Hn y Hy); apply feq_refl. Qed.

(** Two terms with the same result: the same term, branch and, on named
    variables, what follows them. *)
Lemma term_keq K0 K0' e0 u b w u' b' w' :
  brok K0 b w -> brok K0' b' w' -> deep e0 K0 -> nstuck e0 K0 -> deep e0 K0' -> nstuck e0 K0' ->
  feq (FTerm u b (fw w K0)) (FTerm u' b' (fw w' K0')) ->
  u = u' /\ b = b' /\ wbody w = wbody w' /\ keq K0 K0'
  /\ (wbody w <> [] -> forall v, feq (fs (wtail w) K0 v) (fs (wtail w') K0' v)).
Proof.
  intros [Hw [HA [_ [_ Hb]]]] [Hw' [HA' [_ [_ Hb']]]] Hd Hn Hd' Hn' F.
  cbn [feq] in F; destruct F as [<- [<- Hk]]; rewrite !fw_body in Hk.
  assert (En : natl (wbody w) = natl (wbody w')).
  { pose proof (deep_flw lenv (wbody w) _ _ (deep_fs lenv _ (wtail w) _ Hd)) as D1.
    pose proof (deep_flw lenv (wbody w') _ _ (deep_fs lenv _ (wtail w') _ Hd')) as D2.
    assert (E : natl (wbody w) + e0 = natl (wbody w') + e0)
      by (apply (deep_unique _ _ _ _ D1 D2); intros i; apply Hk; intros _; discriminate).
    lia. }
  destruct (wbody_shape w Hw) as [Hp|Hp], (wbody_shape w' Hw') as [Hp'|Hp'].
  - split; [reflexivity|split; [reflexivity|split; [congruence|split; [|intros H; congruence]]]].
    intros y Hy; pose proof (Hk y (fun _ => Hy)) as F; rewrite Hp, Hp' in F; cbn [flw] in F.
    exact (feq_trans _ _ _ (feq_sym _ _ (psok_keq _ _ HA y Hy)) (feq_trans _ _ _ F (psok_keq _ _ HA' y Hy))).
  - exfalso; pose proof (lend_natl _ Hp'); rewrite Hp in En; cbn in En; lia.
  - exfalso; pose proof (lend_natl _ Hp); rewrite Hp' in En; cbn in En; lia.
  - assert (Hne : wbody w <> []) by (intros E; rewrite E in Hp; exact (lend_nil Hp)).
    assert (Hne' : wbody w' <> []) by (intros E; rewrite E in Hp'; exact (lend_nil Hp')).
    destruct (IHb (wbody w) (wbody w') (fs (wtail w) K0) (fs (wtail w') K0') (bdom b) e0 (Hb Hne) (Hb' Hne') En
                (deep_fs lenv _ _ _ Hd) (nstuck_fs lenv _ _ _ Hn) (deep_fs lenv _ _ _ Hd') (nstuck_fs lenv _ _ _ Hn') Hp Hp')
      as [Eb Ek].
    + intros v Hv; apply Hk; intros ->; cbn [bdom dom] in Hv; destruct Hv as [Hv|Hv]; [exact Hv|lia].
    + split; [reflexivity|split; [reflexivity|split; [exact Eb|split; [|intros _; exact Ek]]]].
      intros y Hy; exact (feq_trans _ _ _ (feq_sym _ _ (psok_keq _ _ HA y Hy)) (feq_trans _ _ _ (Ek y) (psok_keq _ _ HA' y Hy))).
Qed.

(** When the term's payload sees bound variables, what follows the
    branch is the same everywhere. *)
Lemma term_full K0 K0' e0 u b w u' b' w' :
  brok K0 b w -> brok K0' b' w' -> deep e0 K0 -> nstuck e0 K0 -> deep e0 K0' -> nstuck e0 K0' ->
  feq (FTerm u b (fw w K0)) (FTerm u' b' (fw w' K0')) -> live b w ->
  forall v, feq (fs (wtail w) K0 v) (fs (wtail w') K0' v).
Proof.
  intros Hb Hb' Hd Hn Hd' Hn' F Hl.
  destruct (term_keq _ _ _ _ _ _ _ _ _ Hb Hb' Hd Hn Hd' Hn' F) as [<- [<- [Ew [_ Ht]]]].
  destruct (list_eq_dec_nil (wbody w)) as [E0|E0]; [|exact (Ht E0)].
  destruct Hl as [Hl|Hl]; [|destruct (Hl E0)].
  intros v; cbn [feq] in F; destruct F as [_ [_ Fk]]; pose proof (Fk v (fun H => False_ind _ (Hl H))) as Fv.
  rewrite !fw_body, <- Ew, E0 in Fv; exact Fv.
Qed.

(** *** Two words that begin with a segment with a term *)

Section Layer1.

Variables (K K' : rvar -> fres) (p p1 p2 : option nat) (e : nat) (Sg Sg' : seg) (r r' : lword).
Hypothesis Hl : lnfL K p (LS Sg :: r).
Hypothesis Hm : lnfL K' p (LS Sg' :: r').
Hypothesis HS : bsegok lenv labs gt route bp K p p1 Sg r.
Hypothesis Hr : lnfL K p1 r.
Hypothesis HS' : bsegok lenv labs gt route bp K' p p2 Sg' r'.
Hypothesis Hr' : lnfL K' p2 r'.
Hypothesis Hn : natl r = natl r'.
Hypothesis Hd : deep e K.
Hypothesis Hs : nstuck e K.
Hypothesis Hd' : deep e K'.
Hypothesis Hs' : nstuck e K'.
Hypothesis Hbase : (K = FVar /\ K' = FVar) \/ (lend (LS Sg :: r) /\ lend (LS Sg' :: r')).
Hypothesis E : forall v, dom p v -> feq (fs Sg (flw r K) v) (fs Sg' (flw r' K') v).

Lemma nat0 : natl r = 0 -> K = FVar /\ K' = FVar.
Proof.
  intros H; destruct Hbase as [B|[B _]]; [exact B|exfalso].
  pose proof (lend_natl _ B) as N; cbn [natl] in N; lia.
Qed.

Lemma Ebig i : feq (flw (LS Sg :: r) K (mk_rvar lbig i)) (flw (LS Sg' :: r') K' (mk_rvar lbig i)).
Proof. apply E; destruct p; [left; apply named_big|exact I]. Qed.

(** Where the term of [Sg] at [x] is in the other word. *)
Lemma locate x u b w : bres Sg x = inr (u, b, w) ->
  (exists u' b' w', bres Sg' x = inr (u', b', w') /\ keq (flw r K) (flw r' K'))
  \/ (exists y rt' t', bres Sg' x = inl y /\ treach lenv r' y = Some (rt', t') /\ keq (flw r K) (flw rt' K')).
Proof.
  intros Ex; pose proof (bo_br _ _ _ _ _ _ _ _ _ _ HS x u b w Ex) as Hb.
  pose proof (E x (phant_dom lenv _ _ _ _ _ (bo_phant _ _ _ _ _ _ _ _ _ _ HS) Ex)) as F.
  rewrite fs_bres, Ex in F; change (fs Sg' (flw r' K') x) with (flw (LS Sg' :: r') K' x) in F.
  destruct (flw (LS Sg' :: r') K' x) as [|u2 b2 k2|] eqn:Em; cbn [feq] in F; try contradiction.
  assert (Fm : feq (FTerm u b (fw w (flw r K))) (FTerm u2 b2 k2)) by exact F.
  destruct (tsrc lenv _ _ _ _ _ _ Em) as [[rt' [w2 [Et Ek]]]|[[m1 [L [a [l1 [y [Em1 [Hm1 [Hy Ey]]]]]]]]|[Hz [y Ey]]]].
  - subst k2; cbn [treach] in Et.
    assert (D0 : deep (natl r + e) (flw r K)) by (apply deep_flw, Hd).
    assert (N0 : nstuck (natl r + e) (flw r K)) by (apply nstuck_flw; assumption).
    destruct (bres Sg' x) as [y|t] eqn:Ey.
    + right; exists y, rt', (u2, b2, w2); split; [reflexivity|split; [exact Et|]].
      destruct (treach_term lenv r' K' y rt' u2 b2 w2 Et) as [_ [Hnr _]].
      assert (D1 : deep (natl r + e) (flw rt' K')) by (rewrite Hn, <- Hnr; apply deep_flw, Hd').
      assert (N1 : nstuck (natl r + e) (flw rt' K')) by (rewrite Hn, <- Hnr; apply nstuck_flw; assumption).
      exact (proj1 (proj2 (proj2 (proj2 (term_keq _ _ _ _ _ _ _ _ _ Hb (treach_brok lenv labs gt route bp K' p2 r' y rt' u2 b2 w2 Hr' Et)
               D0 N0 D1 N1 Fm))))).
    + injection Et as <- ->; left; exists u2, b2, w2; split; [reflexivity|].
      assert (D1 : deep (natl r + e) (flw r' K')) by (rewrite Hn; apply deep_flw, Hd').
      assert (N1 : nstuck (natl r + e) (flw r' K')) by (rewrite Hn; apply nstuck_flw; assumption).
      exact (proj1 (proj2 (proj2 (proj2 (term_keq _ _ _ _ _ _ _ _ _ Hb (bo_br _ _ _ _ _ _ _ _ _ _ HS' x u2 b2 w2 Ey)
               D0 N0 D1 N1 Fm))))).
  - exfalso; refine (cross lenv labs gt route bp K K' p (LS Sg :: r) (LS Sg' :: r') e x u b w r u2 b2 k2 m1 L a l1 y
                       Hm ltac:(cbn [natl]; exact Hn) Hd Hd' Ebig _ (proj1 Hb) Em1 Hm1 Hy Ey Fm).
    cbn [treach]; rewrite Ex; reflexivity.
  - exfalso; cbn [natl] in Hz; destruct (nat0 ltac:(lia)) as [_ ->]; discriminate Ey.
Qed.

End Layer1.

Lemma base_sym K K' (l m : lword) : (K = FVar /\ K' = FVar) \/ (lend l /\ lend m) -> (K' = FVar /\ K = FVar) \/ (lend m /\ lend l).
Proof. tauto. Qed.

(** What follows the first segment is the same on named variables. *)
Lemma first_layer K K' p p1 p2 e Sg Sg' r r' :
  lnfL K p (LS Sg :: r) -> lnfL K' p (LS Sg' :: r') ->
  bsegok lenv labs gt route bp K p p1 Sg r -> lnfL K p1 r ->
  bsegok lenv labs gt route bp K' p p2 Sg' r' -> lnfL K' p2 r' ->
  natl r = natl r' -> deep e K -> nstuck e K -> deep e K' -> nstuck e K' ->
  (K = FVar /\ K' = FVar) \/ (lend (LS Sg :: r) /\ lend (LS Sg' :: r')) ->
  (forall v, dom p v -> feq (fs Sg (flw r K) v) (fs Sg' (flw r' K') v)) ->
  btrm lenv Sg -> btrm lenv Sg' -> keq (flw r K) (flw r' K').
Proof.
  intros Hl Hm HS Hr HS' Hr' Hn Hd Hs Hd' Hs' Hb E [x0 [[[u0 b0] w0] E0]] [x1 [[[u1 b1] w1] E1]].
  assert (E' : forall v, dom p v -> feq (fs Sg' (flw r' K') v) (fs Sg (flw r K) v)) by (intros v Hv; apply feq_sym, E, Hv).
  destruct (locate K K' p p1 p2 e Sg Sg' r r' Hl Hm HS HS' Hr' Hn Hd Hs Hd' Hs' Hb E x0 u0 b0 w0 E0)
    as [[_ [_ [_ [_ K0]]]]|[y0 [rt0 [t0 [_ [T0 K0]]]]]]; [exact K0|].
  destruct (locate K' K p p2 p1 e Sg' Sg r' r Hm Hl HS' HS Hr (eq_sym Hn) Hd' Hs' Hd Hs (base_sym _ _ _ _ Hb) E' x1 u1 b1 w1 E1)
    as [[_ [_ [_ [_ K1]]]]|[y1 [rt1 [t1 [_ [T1 K1]]]]]]; [exact (keq_sym _ _ K1)|].
  exfalso.
  pose proof (bo_order _ _ _ _ _ _ _ _ _ _ HS' y0 rt0 t0 T0) as G0.
  pose proof (bo_order _ _ _ _ _ _ _ _ _ _ HS y1 rt1 t1 T1) as G1.
  apply (gt_irrefl (flw r K) (flw r K) (keq_refl _)).
  apply (gt_trans _ (flw r' K')); [exact (gt_keq _ _ _ _ (keq_refl _) (keq_sym _ _ K1) G1)|].
  exact (gt_keq _ _ _ _ (keq_refl _) (keq_sym _ _ K0) G0).
Qed.

Section Layer2.

Variables (K K' : rvar -> fres) (p p1 p2 : option nat) (e : nat) (Sg Sg' : seg) (r r' : lword).
Hypothesis Hl : lnfL K p (LS Sg :: r).
Hypothesis Hm : lnfL K' p (LS Sg' :: r').
Hypothesis HS : bsegok lenv labs gt route bp K p p1 Sg r.
Hypothesis Hr : lnfL K p1 r.
Hypothesis HS' : bsegok lenv labs gt route bp K' p p2 Sg' r'.
Hypothesis Hr' : lnfL K' p2 r'.
Hypothesis Hn : natl r = natl r'.
Hypothesis Hd : deep e K.
Hypothesis Hs : nstuck e K.
Hypothesis Hd' : deep e K'.
Hypothesis Hs' : nstuck e K'.
Hypothesis Hbase : (K = FVar /\ K' = FVar) \/ (lend (LS Sg :: r) /\ lend (LS Sg' :: r')).
Hypothesis E : forall v, dom p v -> feq (fs Sg (flw r K) v) (fs Sg' (flw r' K') v).
Hypothesis Hk : keq (flw r K) (flw r' K').

(** A variable that goes on as a variable in one word does so in the
    other, with the same result. *)
Lemma var_var x y : dom p x -> bres Sg x = inl y -> exists y', bres Sg' x = inl y' /\ feq (flw r K y) (flw r' K' y').
Proof.
  intros Hx Ex; pose proof (E x Hx) as F; rewrite !fs_bres, Ex in F.
  destruct (bres Sg' x) as [y'|[[u' b'] w']] eqn:Ex'; [exists y'; split; [reflexivity|exact F]|exfalso].
  destruct (flw r K y) as [|u b k|] eqn:Ey; cbn [feq] in F; try contradiction.
  assert (Fm : feq (FTerm u b k) (FTerm u' b' (fw w' (flw r' K')))) by exact F.
  pose proof (bo_br _ _ _ _ _ _ _ _ _ _ HS' x u' b' w' Ex') as Hb'.
  destruct (tsrc lenv _ _ _ _ _ _ Ey) as [[rt [w [Et ->]]]|[[m1 [L [a [l1 [y1 [Em1 [Hm1 [Hy Ey1]]]]]]]]|[Hz [y1 Ey1]]]].
  - destruct (treach_term lenv r K y rt u b w Et) as [_ [Hnr _]].
    assert (D0 : deep (natl r + e) (flw rt K)) by (rewrite <- Hnr; apply deep_flw, Hd).
    assert (N0 : nstuck (natl r + e) (flw rt K)) by (rewrite <- Hnr; apply nstuck_flw; assumption).
    assert (D1 : deep (natl r + e) (flw r' K')) by (rewrite Hn; apply deep_flw, Hd').
    assert (N1 : nstuck (natl r + e) (flw r' K')) by (rewrite Hn; apply nstuck_flw; assumption).
    pose proof (proj1 (proj2 (proj2 (proj2 (term_keq _ _ _ _ _ _ _ _ _
                  (treach_brok lenv labs gt route bp K p1 r y rt u b w Hr Et) Hb' D0 N0 D1 N1 Fm))))) as Kt.
    pose proof (bo_order _ _ _ _ _ _ _ _ _ _ HS y rt (u, b, w) Et) as G.
    exact (gt_irrefl _ _ (keq_refl _) (gt_keq _ _ _ _ Hk Kt G)).
  - apply (cross lenv labs gt route bp K' K p (LS Sg' :: r') (LS Sg :: r) e x u' b' w' r' u b k (LS Sg :: m1) L a l1 y1
             Hl ltac:(cbn [natl]; symmetry; exact Hn) Hd' Hd).
    + intros i; apply feq_sym, E; destruct p; [left; apply named_big|exact I].
    + cbn [treach]; rewrite Ex'; reflexivity.
    + exact (proj1 Hb').
    + rewrite Em1; reflexivity.
    + exact Hm1.
    + exact Hy.
    + exact Ey1.
    + exact (feq_sym _ _ Fm).
  - destruct Hbase as [[-> _]|[B _]]; [discriminate Ey1|].
    pose proof (lend_natl _ B) as N; cbn [natl] in N; lia.
Qed.

Lemma var_named x y : dom p x -> bres Sg x = inl y -> named y -> bres Sg' x = inl y.
Proof.
  intros Hx Ex Hy; destruct (var_var x y Hx Ex) as [y' [Ex' F]]; rewrite Ex'; f_equal.
  symmetry; exact (route_uniq _ _ x y y' Hk (bo_route _ _ _ _ _ _ _ _ _ _ HS x y Hx Ex)
                     (bo_route _ _ _ _ _ _ _ _ _ _ HS' x y' Hx Ex') F Hy).
Qed.

End Layer2.


Lemma dom_dec p x : dom p x \/ ~ dom p x.
Proof.
  destruct p as [n|]; [|left; exact I]; cbn [dom].
  destruct (v_label x) eqn:El; [left; left; unfold named; rewrite El; discriminate|].
  destruct (Nat.lt_ge_cases (v_index x) n) as [H|H]; [left; right; exact H|right].
  intros [H'|H']; [apply H'; exact El|lia].
Qed.

Lemma nondom p x : ~ dom p x -> exists n a, p = Some n /\ x = mk_rvar None (n + a).
Proof.
  destruct p as [n|]; [|intros H; destruct (H I)]; intros H; exists n, (v_index x - n); split; [reflexivity|].
  destruct x as [[l|] i]; cbn [dom v_label v_index] in *.
  - exfalso; apply H; left; discriminate.
  - f_equal; destruct (Nat.lt_ge_cases i n) as [Hi|Hi]; [exfalso; apply H; right; exact Hi|lia].
Qed.

Lemma phant_some p p1 Sg n : phant lenv p p1 Sg -> p = Some n ->
  exists n1, p1 = Some n1 /\ forall a, bres Sg (mk_rvar None (n + a)) = inl (mk_rvar None (n1 + a)).
Proof. intros H ->; destruct p1 as [n1|]; [exists n1; split; [reflexivity|exact H]|destruct H]. Qed.

Lemma phant_none p p1 Sg : phant lenv p p1 Sg -> p = None -> p1 = None.
Proof. intros H ->; destruct p1; [destruct H|reflexivity]. Qed.

Lemma num_conv Sg k : num_first lenv Sg k ->
  forall x x' i j, bres Sg x = inl (mk_rvar None i) -> bres Sg x' = inl (mk_rvar None j) -> i < j ->
    exists x0, bres Sg x0 = inl (mk_rvar None i) /\ forall x'', bres Sg x'' = inl (mk_rvar None j) -> vlt x0 x''.
Proof.
  intros H x x' i j E1 E2 Hij; apply bres_sres in E1, E2; destruct (H x x' i j E1 E2 Hij) as [x0 [E0 H0]].
  exists x0; split; [apply bres_sres, E0|intros x'' E''; apply H0, bres_sres, E''].
Qed.


(** The rests are both empty or both not. *)
Lemma rnil K K' p p1 p2 e Sg Sg' r r' :
  bsegok lenv labs gt route bp K p p1 Sg r -> 
  bsegok lenv labs gt route bp K' p p2 Sg' r' -> lnfL K' p2 r' ->
  natl r = natl r' -> deep e K -> deep e K' -> nstuck e K' ->
  (K = FVar /\ K' = FVar) \/ (lend (LS Sg :: r) /\ lend (LS Sg' :: r')) ->
  (forall v, dom p v -> feq (fs Sg (flw r K) v) (fs Sg' (flw r' K') v)) ->
  keq (flw r K) (flw r' K') -> r = [] -> r' = [].
Proof.
  intros HS HS' Hr' Hn Hd Hd' Hs' Hbase E Hk Er.
  destruct r' as [|[G|L a] r3']; [reflexivity| |exfalso; subst r; cbn [natl] in Hn; lia]; exfalso.
  assert (Hne : LS G :: r3' <> []) by discriminate.
  subst r; destruct Hbase as [[EK EK']|[B _]]; [|destruct B as [l0 [L [a B]]]; destruct l0 as [|? [|]]; discriminate B].
  assert (Hk' : keq FVar (flw (LS G :: r3') K')) by (intros y Hy; pose proof (Hk y Hy) as F; rewrite EK in F; exact F).
  destruct Hr' as [_ [p3 [Hr3 [[HtG HG]|[_ [HrG [_ [_ [->|[L [a [r2 [Er3 _]]]]]]]]]]]]].
  - destruct HtG as [x2 [[[u2 b2] w2] E2]].
    pose proof (phant_dom lenv _ _ _ _ _ (bo_phant _ _ _ _ _ _ _ _ _ _ HG) E2) as Hx2.
    assert (Et2 : treach lenv (LS G :: r3') x2 = Some (r3', (u2, b2, w2))) by (cbn [treach]; rewrite E2; reflexivity).
    pose proof (bo_order _ _ _ _ _ _ _ _ _ _ HS' x2 r3' _ Et2) as Gt.
    destruct (named_or_bound x2) as [Hn2|Hb2].
    + pose proof (Hk' x2 Hn2) as F; cbn [flw] in F; rewrite fs_bres, E2 in F; destruct F.
    + destruct x2 as [l2 j2]; unfold bound in Hb2; cbn in Hb2; subst l2.
      assert (He : e = 0) by (rewrite EK in Hd; exact (deep_unique _ _ _ _ Hd deep_FVar (fun i => feq_refl _))).
      destruct (bo_hit _ _ _ _ _ _ _ _ _ _ HS' Hne j2 Hx2) as [[x [Hx Ex]]|[x [i [u' [b' [w' [Ex' [Hlv Ei]]]]]]]].
      2:{ pose proof (E x (phant_dom lenv _ _ _ _ _ (bo_phant _ _ _ _ _ _ _ _ _ _ HS') Ex')) as F.
          rewrite (fs_bres lenv Sg'), Ex' in F; rewrite EK, (fs_bres lenv Sg) in F.
          destruct (bres Sg x) as [y|[[u b] w]] eqn:Ex0; cbn [feq] in F; [destruct F|].
          assert (D1 : deep 0 (flw (LS G :: r3') K')) by (replace 0 with (natl (LS G :: r3') + e) by (cbn [natl] in Hn |- *; lia); apply deep_flw, Hd').
          assert (N1 : nstuck 0 (flw (LS G :: r3') K')) by (replace 0 with (natl (LS G :: r3') + e) by (cbn [natl] in Hn |- *; lia); apply nstuck_flw; assumption).
          assert (Hb0 : brok FVar b w) by (pose proof (bo_br _ _ _ _ _ _ _ _ _ _ HS x u b w Ex0) as B; rewrite EK in B; exact B).
          pose proof (bo_br _ _ _ _ _ _ _ _ _ _ HS' x u' b' w' Ex') as Hb1.
          destruct (term_keq FVar _ 0 u b w u' b' w' Hb0 Hb1 deep_FVar nstuck_FVar D1 N1 F) as [_ [Eb [Ew _]]].
          assert (Hlv0 : live b w) by (rewrite Eb; destruct Hlv as [Hl|Hl]; [left; exact Hl|right; rewrite Ew; exact Hl]).
          pose proof (term_full FVar _ 0 u b w u' b' w' Hb0 Hb1 deep_FVar nstuck_FVar D1 N1 F Hlv0 (mk_rvar None i)) as Fi.
          rewrite !(fs_ren lenv labs) in Fi by first [exact (proj1 (proj2 (proj1 (proj2 Hb0))))|exact (proj1 (proj2 (proj1 (proj2 Hb1))))].
          rewrite Ei in Fi; cbn [flw] in Fi; rewrite (fs_bres lenv G), E2 in Fi; exact Fi. }
      pose proof (E x Hx) as F; rewrite (fs_bres lenv Sg'), Ex in F; cbn [flw] in F.
      rewrite (fs_bres lenv G (flw r3' K') (mk_rvar None j2)), E2 in F.
      rewrite EK in F; rewrite (fs_bres lenv Sg) in F.
      destruct (bres Sg x) as [y|[[u b] w]] eqn:Ex0; cbn [feq] in F; [destruct F|].
      assert (D1 : deep 0 (flw r3' K')) by (replace 0 with (natl r3' + e) by (cbn [natl] in Hn; lia); apply deep_flw, Hd').
      assert (N1 : nstuck 0 (flw r3' K')) by (replace 0 with (natl r3' + e) by (cbn [natl] in Hn; lia); apply nstuck_flw; assumption).
      assert (Hb0 : brok FVar b w) by (pose proof (bo_br _ _ _ _ _ _ _ _ _ _ HS x u b w Ex0) as B; rewrite EK in B; exact B).
      pose proof (proj1 (proj2 (proj2 (proj2 (term_keq FVar (flw r3' K') 0 u b w u2 b2 w2 Hb0
                    (bo_br _ _ _ _ _ _ _ _ _ _ HG _ u2 b2 w2 E2) deep_FVar nstuck_FVar D1 N1 F))))) as K3.
      exact (gt_irrefl _ _ (keq_refl _) (gt_keq _ _ _ _ (keq_sym _ _ Hk') (keq_sym _ _ K3) Gt)).
  - assert (HrG' : ~ btrm lenv G) by exact (sren_nobtrm lenv labs G HrG).
    apply HrG'; refine (bo_last _ _ _ _ _ _ _ _ _ _ HS' G eq_refl _).
    intros y Hy; apply keq_sym in Hk'; rewrite EK' in Hk' |- *; exact (Hk' y Hy).
  - subst r3'; cbn [natl] in Hn; lia.
Qed.

(** Numbering classes in the order of their first users, over any order. *)
Lemma class_index_g {A : Type} (lt : A -> A -> Prop) (lt_asym : forall a b, lt a b -> lt b a -> False)
  (f f' : A -> nat -> Prop) :
  (forall x i j, f' x i -> f' x j -> i = j) ->
  (forall x i, f x i -> exists i', f' x i') -> (forall x i', f' x i' -> exists i, f x i) ->
  (forall x x0 i i' j', f x i -> f x0 i -> f' x i' -> f' x0 j' -> i' = j') ->
  (forall x x0 i' i j, f' x i' -> f' x0 i' -> f x i -> f x0 j -> i = j) ->
  (forall i, exists x, f x i) -> (forall i, exists x, f' x i) ->
  (forall x x' i j, f x i -> f x' j -> i < j -> exists x0, f x0 i /\ forall x'', f x'' j -> lt x0 x'') ->
  (forall x x' i j, f' x i -> f' x' j -> i < j -> exists x0, f' x0 i /\ forall x'', f' x'' j -> lt x0 x'') ->
  forall n x, f x n -> f' x n.
Proof.
  intros Hfun Ha Ha' Hb Hb' Hs Hs' Hsrc Hsrc' n.
  induction n as [n IH] using lt_wf_ind; intros x Hx.
  destruct (Ha x n Hx) as [n' Hx'].
  destruct (Nat.lt_trichotomy n' n) as [Hlt|[->|Hgt]]; [exfalso|exact Hx'|exfalso].
  - destruct (Hs n') as [x1 H1]; pose proof (IH n' Hlt x1 H1) as H1'.
    pose proof (Hb' x x1 n' n n' Hx' H1' Hx H1); lia.
  - destruct (Hs' n) as [x2 H2']; destruct (Ha' x2 n H2') as [k H2].
    destruct (Nat.lt_trichotomy k n) as [Hk|[->|Hk]].
    + pose proof (Hfun x2 _ _ H2' (IH k Hk x2 H2)); lia.
    + pose proof (Hb x x2 n n' n Hx H2 Hx' H2'); lia.
    + destruct (Hsrc x x2 n k Hx H2 Hk) as [x0 [H0 Hall]].
      destruct (Hsrc' x2 x n n' H2' Hx' Hgt) as [x0' [H0' Hall']].
      destruct (Ha x0 n H0) as [q Hq]; pose proof (Hb x x0 n n' q Hx H0 Hx' Hq) as <-.
      destruct (Ha' x0' n H0') as [p0 Hp0]; pose proof (Hb' x2 x0' n k p0 H2' H0' H2 Hp0) as <-.
      exact (lt_asym _ _ (Hall x0' Hp0) (Hall' x0 Hq)).
Qed.

Lemma ult_asym p a b : ult p a b -> ult p b a -> False.
Proof.
  destruct a as [x|x i], b as [x'|x' i']; cbn [ult].
  - intros [[A B]|[A B]] [[C D]|[C D]]; [tauto|tauto|tauto|exact (vlt_asym _ _ B D)].
  - intros A B; exact (B A).
  - intros A B; exact (A B).
  - intros [A|[Ex A]] [B|[Ex' B]].
    + exact (vlt_asym _ _ A B).
    + subst x'; exact (vlt_irrefl _ A).
    + subst x'; exact (vlt_irrefl _ B).
    + lia.
Qed.

Section Layer3.

Variables (K K' : rvar -> fres) (p p1 p2 : option nat) (e : nat) (Sg Sg' : seg) (r r' : lword).
Hypothesis Hl : lnfL K p (LS Sg :: r).
Hypothesis Hm : lnfL K' p (LS Sg' :: r').
Hypothesis HS : bsegok lenv labs gt route bp K p p1 Sg r.
Hypothesis Hr : lnfL K p1 r.
Hypothesis HS' : bsegok lenv labs gt route bp K' p p2 Sg' r'.
Hypothesis Hr' : lnfL K' p2 r'.
Hypothesis Hn : natl r = natl r'.
Hypothesis Hd : deep e K.
Hypothesis Hs : nstuck e K.
Hypothesis Hd' : deep e K'.
Hypothesis Hs' : nstuck e K'.
Hypothesis Hbase : (K = FVar /\ K' = FVar) \/ (lend (LS Sg :: r) /\ lend (LS Sg' :: r')).
Hypothesis Hp : p <> None -> lend (LS Sg :: r).
Hypothesis E : forall v, dom p v -> feq (fs Sg (flw r K) v) (fs Sg' (flw r' K') v).
Hypothesis Ht : btrm lenv Sg.
Hypothesis Ht' : btrm lenv Sg'.

Let E' : forall v, dom p v -> feq (fs Sg' (flw r' K') v) (fs Sg (flw r K) v).
Proof. intros v Hv; apply feq_sym, E, Hv. Qed.

Let Hk : keq (flw r K) (flw r' K').
Proof. exact (first_layer K K' p p1 p2 e Sg Sg' r r' Hl Hm HS Hr HS' Hr' Hn Hd Hs Hd' Hs' Hbase E Ht Ht'). Qed.

Let VV := var_var K K' p p1 p2 e Sg Sg' r r' Hl Hm HS Hr HS' Hn Hd Hs Hd' Hs' Hbase E Hk.
Let VV' := var_var K' K p p2 p1 e Sg' Sg r' r Hm Hl HS' Hr' HS (eq_sym Hn) Hd' Hs' Hd Hs (base_sym _ _ _ _ Hbase) E' (keq_sym _ _ Hk).
Let VN := var_named K K' p p1 p2 e Sg Sg' r r' Hl Hm HS Hr HS' Hn Hd Hs Hd' Hs' Hbase E Hk.
Let VN' := var_named K' K p p2 p1 e Sg' Sg r' r Hm Hl HS' Hr' HS (eq_sym Hn) Hd' Hs' Hd Hs (base_sym _ _ _ _ Hbase) E' (keq_sym _ _ Hk).

Lemma var_bound x y : dom p x -> bres Sg x = inl y -> bound y ->
  exists y', bres Sg' x = inl y' /\ bound y' /\ feq (flw r K y) (flw r' K' y').
Proof.
  intros Hx Ex Hy; destruct (VV x y Hx Ex) as [y' [Ex' F]].
  exists y'; split; [exact Ex'|split; [|exact F]].
  destruct (named_or_bound y') as [Hn'|Hb]; [exfalso|exact Hb].
  pose proof (VN' x y' Hx Ex' Hn') as E2; rewrite Ex in E2; injection E2 as ->; exact (Hn' Hy).
Qed.

Lemma var_bound' x y : dom p x -> bres Sg' x = inl y -> bound y ->
  exists y', bres Sg x = inl y' /\ bound y' /\ feq (flw r' K' y) (flw r K y').
Proof.
  intros Hx Ex Hy; destruct (VV' x y Hx Ex) as [y' [Ex' F]].
  exists y'; split; [exact Ex'|split; [|exact F]].
  destruct (named_or_bound y') as [Hn'|Hb]; [exfalso|exact Hb].
  pose proof (VN x y' Hx Ex' Hn') as E2; rewrite Ex in E2; injection E2 as ->; exact (Hn' Hy).
Qed.

Hypothesis Hne : r <> [].
Let Hne' : r' <> [].
Proof.
  intros E0; apply Hne; exact (rnil K' K p p2 p1 e Sg' Sg r' r HS' HS Hr (eq_sym Hn) Hd' Hd Hs
    (base_sym _ _ _ _ Hbase) E' (keq_sym _ _ Hk) E0).
Qed.

(** The terms of [Sg] are terms of [Sg'], with the same branch and, when
    the payload sees bound variables, the same tail over the rest. *)
Lemma terms_here x u b w : bres Sg x = inr (u, b, w) ->
  exists w', bres Sg' x = inr (u, b, w') /\ wbody w = wbody w'
    /\ (live b w -> forall v, feq (fs (wtail w) (flw r K) v) (fs (wtail w') (flw r' K') v)).
Proof.
  intros Ex; pose proof (bo_br _ _ _ _ _ _ _ _ _ _ HS x u b w Ex) as Hb.
  assert (D0 : deep (natl r + e) (flw r K)) by (apply deep_flw, Hd).
  assert (N0 : nstuck (natl r + e) (flw r K)) by (apply nstuck_flw; assumption).
  destruct (locate K K' p p1 p2 e Sg Sg' r r' Hl Hm HS HS' Hr' Hn Hd Hs Hd' Hs' Hbase E x u b w Ex)
    as [[u' [b' [w' [Ex' _]]]]|[y [rt' [t' [Ey [Et Kt]]]]]].
  - pose proof (bo_br _ _ _ _ _ _ _ _ _ _ HS' x u' b' w' Ex') as Hb'.
    assert (D1 : deep (natl r + e) (flw r' K')) by (rewrite Hn; apply deep_flw, Hd').
    assert (N1 : nstuck (natl r + e) (flw r' K')) by (rewrite Hn; apply nstuck_flw; assumption).
    pose proof (E x (phant_dom lenv _ _ _ _ _ (bo_phant _ _ _ _ _ _ _ _ _ _ HS) Ex)) as F; rewrite !fs_bres, Ex, Ex' in F.
    destruct (term_keq _ _ _ _ _ _ _ _ _ Hb Hb' D0 N0 D1 N1 F) as [<- [<- [Ew _]]].
    exists w'; split; [exact Ex'|split; [exact Ew|]].
    exact (term_full _ _ _ _ _ _ _ _ _ Hb Hb' D0 N0 D1 N1 F).
  - exfalso; destruct t' as [[u2 b2] w2].
    pose proof (bo_order _ _ _ _ _ _ _ _ _ _ HS' y rt' _ Et) as G.
    exact (gt_irrefl _ _ (keq_refl _) (gt_keq _ _ _ _ (keq_refl _) (keq_trans _ _ _ (keq_sym _ _ Kt) Hk) G)).
Qed.

Lemma terms_here' x u b w : bres Sg' x = inr (u, b, w) ->
  exists w', bres Sg x = inr (u, b, w') /\ wbody w = wbody w'
    /\ (live b w -> forall v, feq (fs (wtail w) (flw r' K') v) (fs (wtail w') (flw r K) v)).
Proof.
  intros Ex; pose proof (bo_br _ _ _ _ _ _ _ _ _ _ HS' x u b w Ex) as Hb.
  assert (D0 : deep (natl r + e) (flw r' K')) by (rewrite Hn; apply deep_flw, Hd').
  assert (N0 : nstuck (natl r + e) (flw r' K')) by (rewrite Hn; apply nstuck_flw; assumption).
  destruct (locate K' K p p2 p1 e Sg' Sg r' r Hm Hl HS' HS Hr (eq_sym Hn) Hd' Hs' Hd Hs (base_sym _ _ _ _ Hbase) E' x u b w Ex)
    as [[u' [b' [w' [Ex' _]]]]|[y [rt' [t' [Ey [Et Kt]]]]]].
  - pose proof (bo_br _ _ _ _ _ _ _ _ _ _ HS x u' b' w' Ex') as Hb'.
    assert (D1 : deep (natl r + e) (flw r K)) by (apply deep_flw, Hd).
    assert (N1 : nstuck (natl r + e) (flw r K)) by (apply nstuck_flw; assumption).
    pose proof (E' x (phant_dom lenv _ _ _ _ _ (bo_phant _ _ _ _ _ _ _ _ _ _ HS') Ex)) as F; rewrite !fs_bres, Ex, Ex' in F.
    destruct (term_keq _ _ _ _ _ _ _ _ _ Hb Hb' D0 N0 D1 N1 F) as [<- [<- [Ew _]]].
    exists w'; split; [exact Ex'|split; [exact Ew|]].
    exact (term_full _ _ _ _ _ _ _ _ _ Hb Hb' D0 N0 D1 N1 F).
  - exfalso; destruct t' as [[u2 b2] w2].
    pose proof (bo_order _ _ _ _ _ _ _ _ _ _ HS y rt' _ Et) as G.
    exact (gt_irrefl _ _ (keq_refl _) (gt_keq _ _ _ _ (keq_refl _) (keq_trans _ _ _ (keq_sym _ _ Kt) (keq_sym _ _ Hk)) G)).
Qed.

(** A tail user hits a bound variable in both words, with the same
    result. *)
Lemma tail_val x i j : uhit lenv Sg (UTl x i) j ->
  exists j', uhit lenv Sg' (UTl x i) j' /\ feq (flw r K (mk_rvar None j)) (flw r' K' (mk_rvar None j')).
Proof.
  intros [u [b [w [Ex [Hlv Ej]]]]].
  destruct (terms_here x u b w Ex) as [w' [Ex' [Ew Htl]]].
  pose proof (bo_br _ _ _ _ _ _ _ _ _ _ HS x u b w Ex) as [_ [HA [HrA _]]].
  pose proof (bo_br _ _ _ _ _ _ _ _ _ _ HS' x u b w' Ex') as [_ [HA' _]].
  pose proof (Htl Hlv (mk_rvar None i)) as F.
  rewrite !(fs_ren lenv labs) in F by first [exact (proj1 (proj2 HA))|exact (proj1 (proj2 HA'))]; rewrite Ej in F.
  destruct (sv (wtail w') (mk_rvar None i)) as [[l'|] j'] eqn:Ej'.
  - exfalso; destruct (HrA Hlv i) as [_ Hb]; rewrite Ej in Hb.
    apply (Hb eq_refl (mk_rvar (Some l') j') ltac:(discriminate)).
    exact (feq_trans _ _ _ (Hk (mk_rvar (Some l') j') ltac:(discriminate)) (feq_sym _ _ F)).
  - exists j'; split; [exists u, b, w'; split; [exact Ex'|split; [destruct Hlv as [Hl0|Hl0]; [left; exact Hl0|right; rewrite <- Ew; exact Hl0]|exact Ej']]|exact F].
Qed.

Lemma tail_val' x i j : uhit lenv Sg' (UTl x i) j ->
  exists j', uhit lenv Sg (UTl x i) j' /\ feq (flw r' K' (mk_rvar None j)) (flw r K (mk_rvar None j')).
Proof.
  intros [u [b [w [Ex [Hlv Ej]]]]].
  destruct (terms_here' x u b w Ex) as [w' [Ex' [Ew Htl]]].
  pose proof (bo_br _ _ _ _ _ _ _ _ _ _ HS' x u b w Ex) as [_ [HA [HrA _]]].
  pose proof (bo_br _ _ _ _ _ _ _ _ _ _ HS x u b w' Ex') as [_ [HA' _]].
  pose proof (Htl Hlv (mk_rvar None i)) as F.
  rewrite !(fs_ren lenv labs) in F by first [exact (proj1 (proj2 HA))|exact (proj1 (proj2 HA'))]; rewrite Ej in F.
  destruct (sv (wtail w') (mk_rvar None i)) as [[l'|] j'] eqn:Ej'.
  - exfalso; destruct (HrA Hlv i) as [_ Hb]; rewrite Ej in Hb.
    apply (Hb eq_refl (mk_rvar (Some l') j') ltac:(discriminate)).
    exact (feq_trans _ _ _ (feq_sym _ _ (Hk (mk_rvar (Some l') j') ltac:(discriminate))) (feq_sym _ _ F)).
  - exists j'; split; [exists u, b, w'; split; [exact Ex'|split; [destruct Hlv as [Hl0|Hl0]; [left; exact Hl0|right; rewrite <- Ew; exact Hl0]|exact Ej']]|exact F].
Qed.

Lemma uhit_fun Sg0 a i j : uhit lenv Sg0 a i -> uhit lenv Sg0 a j -> i = j.
Proof.
  destruct a as [x|x i0]; cbn [uhit].
  - intros H1 H2; rewrite H1 in H2; injection H2 as H2; exact H2.
  - intros [u [b [w [E1 [_ F1]]]]] [u' [b' [w' [E2 [_ F2]]]]]; rewrite E1 in E2; injection E2 as <- <- <-.
    rewrite F1 in F2; injection F2 as F2; exact F2.
Qed.

(** Bound variables are numbered the same. *)
Lemma numbering : forall n a, uhit lenv Sg a n -> uhit lenv Sg' a n.
Proof.
  pose proof (bo_phant _ _ _ _ _ _ _ _ _ _ HS) as P1; pose proof (bo_phant _ _ _ _ _ _ _ _ _ _ HS') as P2.
  assert (Hph : forall x, ~ dom p x -> exists n n1 n2 a, p = Some n /\ p1 = Some n1 /\ p2 = Some n2 /\ x = mk_rvar None (n + a)
             /\ bres Sg x = inl (mk_rvar None (n1 + a)) /\ bres Sg' x = inl (mk_rvar None (n2 + a))).
  { intros x Hx; destruct (nondom p x Hx) as [n [a [-> ->]]].
    destruct (phant_some _ _ _ n P1 eq_refl) as [n1 [-> H1]]; destruct (phant_some _ _ _ n P2 eq_refl) as [n2 [-> H2]].
    exists n, n1, n2, a; repeat split; [apply H1|apply H2]. }
  (* What an observed user hits has the same result in both words. *)
  assert (Val : forall a i i', (match a with UIn x => dom p x | UTl _ _ => True end) ->
            uhit lenv Sg a i -> uhit lenv Sg' a i' -> feq (flw r K (mk_rvar None i)) (flw r' K' (mk_rvar None i'))).
  { intros [x|x i0] i i' Ho H1 H2.
    - destruct (VV x _ Ho H1) as [y1 [E1 F1]]; cbn [uhit] in H2; rewrite H2 in E1; injection E1 as <-; exact F1.
    - destruct (tail_val x i0 i H1) as [j' [H2' F]]; rewrite (uhit_fun _ _ _ _ H2 H2'); exact F. }
  assert (Val' : forall a i i', (match a with UIn x => dom p x | UTl _ _ => True end) ->
            uhit lenv Sg' a i -> uhit lenv Sg a i' -> feq (flw r' K' (mk_rvar None i)) (flw r K (mk_rvar None i'))).
  { intros [x|x i0] i i' Ho H1 H2.
    - destruct (VV' x _ Ho H1) as [y1 [E1 F1]]; cbn [uhit] in H2; rewrite H2 in E1; injection E1 as <-; exact F1.
    - destruct (tail_val' x i0 i H1) as [j' [H2' F]]; rewrite (uhit_fun _ _ _ _ H2 H2'); exact F. }
  (* An observed user hits an observed bound variable. *)
  assert (Real : forall q Sg0 a i, phant lenv p q Sg0 -> (forall x y, dom p x -> bres Sg0 x = inl y -> dom q y) ->
            (forall x i0 j, uhit lenv Sg0 (UTl x i0) j -> dom q (mk_rvar None j)) ->
            (match a with UIn x => dom p x | UTl _ _ => True end) -> uhit lenv Sg0 a i -> dom q (mk_rvar None i)).
  { intros q Sg0 [x|x i0] i _ R1 R2 Ho H; [exact (R1 x _ Ho H)|exact (R2 x i0 i H)]. }
  assert (Obs : forall a, (match a with UIn x => dom p x | UTl _ _ => True end) \/ exists x, a = UIn x /\ ~ dom p x).
  { intros [x|x i0]; [destruct (dom_dec p x) as [H|H]; [left; exact H|right; exists x; split; [reflexivity|exact H]]|left; exact I]. }
  assert (Phd : forall q n1 i, q = Some n1 -> dom q (mk_rvar None i) -> i < n1).
  { intros q n1 i -> [H|H]; [destruct (H eq_refl)|exact H]. }
  apply (class_index_g (ult p) (ult_asym p) (uhit lenv Sg) (uhit lenv Sg')).
  - intros a i j; apply uhit_fun.
  - intros a i Hi; destruct (Obs a) as [Ho|[x [-> Hx]]].
    + destruct a as [x|x i0].
      * cbn [uhit] in Hi; destruct (var_bound x _ Ho Hi eq_refl) as [[l' i'] [Ex' [Hb' _]]]; unfold bound in Hb'; cbn in Hb'; subst l'.
        exists i'; exact Ex'.
      * destruct (tail_val x i0 i Hi) as [j' [H _]]; exists j'; exact H.
    + destruct (Hph x Hx) as [n [n1 [n2 [a [_ [_ [_ [_ [_ E2]]]]]]]]]; exists (n2 + a); exact E2.
  - intros a i Hi; destruct (Obs a) as [Ho|[x [-> Hx]]].
    + destruct a as [x|x i0].
      * cbn [uhit] in Hi; destruct (var_bound' x _ Ho Hi eq_refl) as [[l' i'] [Ex' [Hb' _]]]; unfold bound in Hb'; cbn in Hb'; subst l'.
        exists i'; exact Ex'.
      * destruct (tail_val' x i0 i Hi) as [j' [H _]]; exists j'; exact H.
    + destruct (Hph x Hx) as [n [n1 [n2 [a [_ [_ [_ [_ [E1 _]]]]]]]]]; exists (n1 + a); exact E1.
  - intros a a0 i i' j' H1 H2 H1' H2'.
    destruct (Obs a) as [Ho|[x [-> Hx]]], (Obs a0) as [Ho0|[x0 [-> Hx0]]].
    + pose proof (bo_binj _ _ _ _ _ _ _ _ _ _ HS' (mk_rvar None i') (mk_rvar None j') eq_refl eq_refl
                    (feq_trans _ _ _ (feq_sym _ _ (Val a i i' Ho H1 H1')) (Val a0 i j' Ho0 H2 H2'))) as Ei.
      injection Ei as Ei; exact Ei.
    + exfalso; destruct (Hph x0 Hx0) as [n [n1 [n2 [a1 [_ [Ep1 [_ [_ [E1 _]]]]]]]]]; cbn [uhit] in H2; rewrite H2 in E1.
      injection E1 as ->; pose proof (Real _ _ a _ P1 (bo_real _ _ _ _ _ _ _ _ _ _ HS) (bo_treal _ _ _ _ _ _ _ _ _ _ HS) Ho H1) as R1.
      pose proof (Phd _ _ _ Ep1 R1); lia.
    + exfalso; destruct (Hph x Hx) as [n [n1 [n2 [a1 [_ [Ep1 [_ [_ [E1 _]]]]]]]]]; cbn [uhit] in H1; rewrite H1 in E1.
      injection E1 as ->; pose proof (Real _ _ a0 _ P1 (bo_real _ _ _ _ _ _ _ _ _ _ HS) (bo_treal _ _ _ _ _ _ _ _ _ _ HS) Ho0 H2) as R1.
      pose proof (Phd _ _ _ Ep1 R1); lia.
    + destruct (Hph x Hx) as [n [n1 [n2 [a1 [Ep [Ep1 [_ [Ex [E1 _]]]]]]]]].
      destruct (Hph x0 Hx0) as [n' [n1' [n2' [a0' [Ep' [Ep1' [_ [Ex0 [E1' _]]]]]]]]].
      rewrite Ep in Ep'; injection Ep' as <-; rewrite Ep1 in Ep1'; injection Ep1' as <-.
      cbn [uhit] in H1, H2; rewrite H1 in E1; rewrite H2 in E1'; injection E1 as E1; injection E1' as E1'.
      assert (x = x0) as <- by (rewrite Ex, Ex0; f_equal; f_equal; lia).
      exact (uhit_fun _ _ _ _ H1' H2').
  - intros a a0 i' i j H1' H2' H1 H2.
    destruct (Obs a) as [Ho|[x [-> Hx]]], (Obs a0) as [Ho0|[x0 [-> Hx0]]].
    + pose proof (bo_binj _ _ _ _ _ _ _ _ _ _ HS (mk_rvar None i) (mk_rvar None j) eq_refl eq_refl
                    (feq_trans _ _ _ (feq_sym _ _ (Val' a i' i Ho H1' H1)) (Val' a0 i' j Ho0 H2' H2))) as Ei.
      injection Ei as Ei; exact Ei.
    + exfalso; destruct (Hph x0 Hx0) as [n [n1 [n2 [a1 [_ [_ [Ep2 [_ [_ E1]]]]]]]]]; cbn [uhit] in H2'; rewrite H2' in E1.
      injection E1 as ->; pose proof (Real _ _ a _ P2 (bo_real _ _ _ _ _ _ _ _ _ _ HS') (bo_treal _ _ _ _ _ _ _ _ _ _ HS') Ho H1') as R1.
      pose proof (Phd _ _ _ Ep2 R1); lia.
    + exfalso; destruct (Hph x Hx) as [n [n1 [n2 [a1 [_ [_ [Ep2 [_ [_ E1]]]]]]]]]; cbn [uhit] in H1'; rewrite H1' in E1.
      injection E1 as ->; pose proof (Real _ _ a0 _ P2 (bo_real _ _ _ _ _ _ _ _ _ _ HS') (bo_treal _ _ _ _ _ _ _ _ _ _ HS') Ho0 H2') as R1.
      pose proof (Phd _ _ _ Ep2 R1); lia.
    + destruct (Hph x Hx) as [n [n1 [n2 [a1 [Ep [_ [Ep2 [Ex [_ E1]]]]]]]]].
      destruct (Hph x0 Hx0) as [n' [n1' [n2' [a0' [Ep' [_ [Ep2' [Ex0 [_ E1']]]]]]]]].
      rewrite Ep in Ep'; injection Ep' as <-; rewrite Ep2 in Ep2'; injection Ep2' as <-.
      cbn [uhit] in H1', H2'; rewrite H1' in E1; rewrite H2' in E1'; injection E1 as E1; injection E1' as E1'.
      assert (x = x0) as <- by (rewrite Ex, Ex0; f_equal; f_equal; lia).
      exact (uhit_fun _ _ _ _ H1 H2).
  - intros i; destruct (dom_dec p1 (mk_rvar None i)) as [Hi|Hi].
    + destruct (bo_hit _ _ _ _ _ _ _ _ _ _ HS Hne i Hi) as [[x [_ Ex]]|[x [i0 H]]]; [exists (UIn x); exact Ex|exists (UTl x i0); exact H].
    + destruct (nondom p1 _ Hi) as [n1 [a [Ep1 Ei]]].
      destruct (opt_cases p) as [Ep|[n Ep]]; [rewrite (phant_none _ _ _ P1 Ep) in Ep1; discriminate Ep1|].
      destruct (phant_some _ _ _ n P1 Ep) as [n1' [Ep1' H1]]; rewrite Ep1 in Ep1'; injection Ep1' as <-.
      exists (UIn (mk_rvar None (n + a))); cbn [uhit]; rewrite H1; injection Ei as Ei; rewrite Ei; reflexivity.
  - intros i; destruct (dom_dec p2 (mk_rvar None i)) as [Hi|Hi].
    + destruct (bo_hit _ _ _ _ _ _ _ _ _ _ HS' Hne' i Hi) as [[x [_ Ex]]|[x [i0 H]]]; [exists (UIn x); exact Ex|exists (UTl x i0); exact H].
    + destruct (nondom p2 _ Hi) as [n2 [a [Ep2 Ei]]].
      destruct (opt_cases p) as [Ep|[n Ep]]; [rewrite (phant_none _ _ _ P2 Ep) in Ep2; discriminate Ep2|].
      destruct (phant_some _ _ _ n P2 Ep) as [n2' [Ep2' H2]]; rewrite Ep2 in Ep2'; injection Ep2' as <-.
      exists (UIn (mk_rvar None (n + a))); cbn [uhit]; rewrite H2; injection Ei as Ei; rewrite Ei; reflexivity.
  - exact (bo_num _ _ _ _ _ _ _ _ _ _ HS Hne).
  - exact (bo_num _ _ _ _ _ _ _ _ _ _ HS' Hne').
Qed.

Lemma doms : p1 = p2.
Proof.
  pose proof (bo_phant _ _ _ _ _ _ _ _ _ _ HS) as P1; pose proof (bo_phant _ _ _ _ _ _ _ _ _ _ HS') as P2.
  destruct (opt_cases p) as [Ep|[n Ep]]; [rewrite (phant_none _ _ _ P1 Ep), (phant_none _ _ _ P2 Ep); reflexivity|].
  destruct (phant_some _ _ _ n P1 Ep) as [n1 [Ep1 H1]]; destruct (phant_some _ _ _ n P2 Ep) as [n2 [Ep2 H2]].
  pose proof (numbering _ (UIn _) (H1 0)) as E2; cbn [uhit] in E2; rewrite H2 in E2; injection E2 as E2; rewrite Ep1, Ep2; f_equal; lia.
Qed.

Lemma var_same x y : dom p x -> bres Sg x = inl y -> bres Sg' x = inl y.
Proof.
  intros Hx Ex; destruct (named_or_bound y) as [Hy|Hy]; [exact (VN x y Hx Ex Hy)|].
  destruct y as [l i]; unfold bound in Hy; cbn in Hy; subst l; exact (numbering i (UIn x) Ex).
Qed.

Lemma rest_eq v : dom p1 v -> feq (flw r K v) (flw r' K' v).
Proof.
  intros Hv; destruct (named_or_bound v) as [Hn0|Hb]; [exact (Hk v Hn0)|].
  destruct v as [l j]; unfold bound in Hb; cbn in Hb; subst l.
  destruct (bo_hit _ _ _ _ _ _ _ _ _ _ HS Hne j Hv) as [[x [Hx Ex]]|[x [i Hu]]].
  - pose proof (E x Hx) as F; rewrite !fs_bres, Ex, (var_same x _ Hx Ex) in F; exact F.
  - destruct (tail_val x i j Hu) as [j' [Hu' F]]; rewrite (uhit_fun _ _ _ _ Hu' (numbering j _ Hu)) in F; exact F.
Qed.

End Layer3.

Lemma routed_feq k k' y : (forall v, feq (k v) (k' v)) -> routed k' y -> routed k y.
Proof.
  intros H [H1 H2]; split.
  - intros Hy y' Hy' F; apply (H1 Hy y' Hy'); exact (feq_trans _ _ _ (feq_sym _ _ (H y')) (feq_trans _ _ _ F (H y))).
  - intros Hy y' Hy' F; apply (H2 Hy y' Hy'); exact (feq_trans _ _ _ (feq_sym _ _ (H y')) (feq_trans _ _ _ F (H y))).
Qed.

(** With the rest known, the segments are the same. *)
Lemma seg_final K K' p p1 e Sg Sg' r :
  bsegok lenv labs gt route bp K p p1 Sg r -> bsegok lenv labs gt route bp K' p p1 Sg' r ->
  deep e K -> nstuck e K -> deep e K' -> nstuck e K' ->
  (forall v, feq (flw r K v) (flw r K' v)) ->
  (forall x y, dom p x -> bres Sg x = inl y -> bres Sg' x = inl y) ->
  (forall x y, dom p x -> bres Sg' x = inl y -> bres Sg x = inl y) ->
  (forall v, dom p v -> feq (fs Sg (flw r K) v) (fs Sg' (flw r K') v)) ->
  Sg = Sg'.
Proof.
  intros HS HS' Hd Hs Hd' Hs' Hbk Hv Hv' E.
  apply (seg_ext lenv labs Hinj); [exact (bo_shape _ _ _ _ _ _ _ _ _ _ HS)|exact (bo_shape _ _ _ _ _ _ _ _ _ _ HS')
    |exact (bo_tlab _ _ _ _ _ _ _ _ _ _ HS)|exact (bo_tlab _ _ _ _ _ _ _ _ _ _ HS')|]; intros x.
  destruct (dom_dec p x) as [Hx|Hx].
  - destruct (bres Sg x) as [y|[[u b] w]] eqn:Ex; [symmetry; exact (Hv x y Hx Ex)|].
    destruct (bres Sg' x) as [y'|[[u' b'] w']] eqn:Ex'; [rewrite (Hv' x y' Hx Ex') in Ex; discriminate Ex|].
    pose proof (E x Hx) as F; rewrite !fs_bres, Ex, Ex' in F.
    pose proof (bo_br _ _ _ _ _ _ _ _ _ _ HS x u b w Ex) as Hb.
    pose proof (bo_br _ _ _ _ _ _ _ _ _ _ HS' x u' b' w' Ex') as Hb'.
    assert (D0 : deep (natl r + e) (flw r K)) by (apply deep_flw, Hd).
    assert (N0 : nstuck (natl r + e) (flw r K)) by (apply nstuck_flw; assumption).
    assert (D1 : deep (natl r + e) (flw r K')) by (apply deep_flw, Hd').
    assert (N1 : nstuck (natl r + e) (flw r K')) by (apply nstuck_flw; assumption).
    destruct (term_keq _ _ _ _ _ _ _ _ _ Hb Hb' D0 N0 D1 N1 F) as [<- [<- [Ebw [_ Htl]]]].
    destruct Hb as [Hw [HA [HrA [HnA _]]]]; destruct Hb' as [Hw' [HA' [HrA' [HnA' _]]]].
    assert (Etl : wtail w = wtail w').
    { destruct (opt_cases b) as [Eb|[n Eb]]; [destruct (list_eq_dec_nil (wbody w)) as [Ew|Ew]|].
      - rewrite (HnA Eb Ew), (HnA' Eb (eq_trans (eq_sym Ebw) Ew)); reflexivity.
      - apply (pay_unique lenv labs Hinj _ _ (flw r K) HA HA' (bo_binj _ _ _ _ _ _ _ _ _ _ HS));
          [apply HrA; right; exact Ew|intros i; apply (routed_feq _ _ _ Hbk), HrA'; right; rewrite <- Ebw; exact Ew|].
        intros z; apply (feq_trans _ _ _ (Htl Ew z)).
        apply (proj1 (proj2 (proj2 (f_cong lenv)))); intros y; apply feq_sym, Hbk.
      - assert (Bn : b <> None) by (rewrite Eb; discriminate).
        apply (pay_unique lenv labs Hinj _ _ (flw r K) HA HA' (bo_binj _ _ _ _ _ _ _ _ _ _ HS));
          [apply HrA; left; exact Bn|intros i; apply (routed_feq _ _ _ Hbk), HrA'; left; exact Bn|].
        destruct (list_eq_dec_nil (wbody w)) as [Ew|Ew].
        + intros z; cbn [feq] in F; destruct F as [_ [_ Fk]].
          pose proof (Fk z (fun H => False_ind _ (Bn H))) as Fz; rewrite !fw_body, <- Ebw, Ew in Fz; cbn [flw] in Fz.
          apply (feq_trans _ _ _ Fz); apply (proj1 (proj2 (proj2 (f_cong lenv)))); intros y; apply feq_sym, Hbk.
        + intros z; apply (feq_trans _ _ _ (Htl Ew z)).
          apply (proj1 (proj2 (proj2 (f_cong lenv)))); intros y; apply feq_sym, Hbk. }
    rewrite (w_inj w w' Hw Hw' Ebw Etl); reflexivity.
  - destruct (nondom p x Hx) as [n [a [Ep ->]]].
    destruct (phant_some _ _ _ n (bo_phant _ _ _ _ _ _ _ _ _ _ HS) Ep) as [n1 [Ep1 H1]].
    destruct (phant_some _ _ _ n (bo_phant _ _ _ _ _ _ _ _ _ _ HS') Ep) as [n1' [Ep1' H1']].
    rewrite Ep1 in Ep1'; injection Ep1' as <-; rewrite H1, H1'; reflexivity.
Qed.

(** *** A renaming and an atom at the head, observed on [dom p] *)

Definition ldom (p : option nat) (L : list (lexp * nat)) : Prop :=
  match p with None => True | Some n => lc None L <= n end.

Lemma lpos_label U L g i : lpos lenv U L -> inVb lenv L (sv U (mk_rvar g i)) = true -> v_label (sv U (mk_rvar g i)) = g.
Proof. intros [H _] E; rewrite (H g i E); reflexivity. Qed.

Lemma peel_dom p p1 p2 U1 L1 a1 R1 n1 U2 L2 a2 R2 n2 :
  sshape lenv labs false U1 -> sren labs U1 -> lok lenv labs L1 -> lpos lenv U1 L1 -> phant lenv p p1 U1 ->
  (forall x y, dom p x -> bres U1 x = inl y -> dom p1 y) ->
  (forall y, bound y -> dom p1 y -> p1 <> None -> exists x, dom p x /\ bres U1 x = inl y) -> ldom p1 L1 ->
  sshape lenv labs false U2 -> sren labs U2 -> lok lenv labs L2 -> lpos lenv U2 L2 -> phant lenv p p2 U2 ->
  (forall x y, dom p x -> bres U2 x = inl y -> dom p2 y) ->
  (forall y, bound y -> dom p2 y -> p2 <> None -> exists x, dom p x /\ bres U2 x = inl y) -> ldom p2 L2 ->
  deep n1 R1 -> nstuck n1 R1 -> deep n2 R2 -> nstuck n2 R2 ->
  (forall v, dom p v -> feq (Unique.latom lenv L1 a1 R1 (sv U1 v)) (Unique.latom lenv L2 a2 R2 (sv U2 v))) ->
  U1 = U2 /\ L1 = L2 /\ a1 = a2 /\ p1 = p2 /\ forall y, feq (R1 y) (R2 y).
Proof.
  intros Hs1 Hr1 Hl1 Hp1 Ph1 Re1 Hi1 Ld1 Hs2 Hr2 Hl2 Hp2 Ph2 Re2 Hi2 Ld2 Hd1' Hst1 Hd2' Hst2 H.
  assert (Sv1 : forall x, bres U1 x = inl (sv U1 x)) by (intros x; exact (bres_ren lenv labs U1 x Hr1)).
  assert (Sv2 : forall x, bres U2 x = inl (sv U2 x)) by (intros x; exact (bres_ren lenv labs U2 x Hr2)).
  assert (Hdb : forall B, dom p (mk_rvar lbig B)) by (intros B; destruct p; [left; apply named_big|exact I]).
  destruct (sv_big lenv labs U1 lbig (lc lbig L1) Hr1) as [B1 HB1].
  destruct (sv_big lenv labs U2 lbig (lc lbig L2) Hr2) as [B2 HB2].
  destruct (HB1 (B1 + B2) ltac:(lia)) as [j1 [Hj1 E1]]; destruct (HB2 (B1 + B2) ltac:(lia)) as [j2 [Hj2 E2]].
  pose proof (H _ (Hdb (B1 + B2))) as Hb; rewrite E1, E2 in Hb; unfold Unique.latom in Hb; cbn [v_label v_index] in Hb.
  rewrite (proj2 (Nat.ltb_ge _ _) Hj1), (proj2 (Nat.ltb_ge _ _) Hj2) in Hb; cbn [feq] in Hb.
  destruct Hb as [<- [_ Hk]].
  assert (Hd1 : deep n1 (fun y => R1 (shiftL L1 y))) by exact (deep_shift lenv _ L1 _ Hd1').
  assert (Hd2 : deep n2 (fun y => R2 (shiftL L2 y))) by exact (deep_shift lenv _ L2 _ Hd2').
  assert (En : n1 = n2) by (apply (deep_unique _ _ _ _ Hd1 Hd2); intros i; apply Hk).
  (* Phantoms are not lifted. *)
  assert (Hph : forall q U L v, phant lenv p q U -> ldom q L -> ~ dom p v -> sren labs U ->
            inVb lenv L (sv U v) = false /\ exists n n' a, p = Some n /\ q = Some n' /\ v = mk_rvar None (n + a)
              /\ sv U v = mk_rvar None (n' + a)).
  { intros q U L v Ph Ld Hv Hr; destruct (nondom p v Hv) as [n [a [Ep ->]]].
    destruct (phant_some _ _ _ n Ph Ep) as [n' [Eq Hq]]; pose proof (Hq a) as Ea.
    rewrite (bres_ren lenv labs U _ Hr) in Ea; injection Ea as Ea; rewrite Ea.
    split; [|exists n, n', a; repeat split; assumption].
    unfold inVb; cbn [v_label v_index]; rewrite Eq in Ld; cbn [ldom] in Ld; apply Nat.ltb_ge; lia. }
  assert (HB : forall v, dom p v ->
    (inVb lenv L1 (sv U1 v) = true /\ inVb lenv L2 (sv U2 v) = true /\ feq (R1 (sv U1 v)) (R2 (sv U2 v)))
    \/ (inVb lenv L1 (sv U1 v) = false /\ inVb lenv L2 (sv U2 v) = false
        /\ unsh lenv L1 (sv U1 v) = unsh lenv L2 (sv U2 v))).
  { intros v Hv; pose proof (H v Hv) as E; unfold Unique.latom in E; unfold inVb.
    destruct (v_index (sv U1 v) <? _) eqn:Ei1, (v_index (sv U2 v) <? _) eqn:Ei2.
    - left; auto.
    - exfalso; destruct (R1 (sv U1 v)) as [| |a z k] eqn:ER; cbn [feq] in E; try contradiction.
      destruct E as [_ [_ Ek]]; destruct (Hst1 _ _ _ _ ER) as [d [Hd Hdk]].
      assert (d = n2) by (apply (deep_unique _ _ _ _ Hdk Hd2); intros i; apply Ek); lia.
    - exfalso; destruct (R2 (sv U2 v)) as [| |a z k] eqn:ER; cbn [feq] in E; try contradiction.
      destruct E as [_ [_ Ek]]; destruct (Hst2 _ _ _ _ ER) as [d [Hd Hdk]].
      assert (n1 = d) by (apply (deep_unique _ _ _ _ Hd1 Hdk); intros i; apply Ek); lia.
    - right; cbn [feq] in E; destruct E as [_ [Ez _]]; auto. }
  assert (Hcnt : forall g i, cntV lenv U1 L1 g i = cntV lenv U2 L2 g i).
  { intros g i; induction i as [|i IHi]; [reflexivity|]; cbn [cntV]; rewrite IHi.
    destruct (dom_dec p (mk_rvar g i)) as [Hv|Hv].
    - destruct (HB (mk_rvar g i) Hv) as [[-> [-> _]]|[-> [-> _]]]; reflexivity.
    - rewrite (proj1 (Hph _ _ _ _ Ph1 Ld1 Hv Hr1)), (proj1 (Hph _ _ _ _ Ph2 Ld2 Hv Hr2)); reflexivity. }
  (* A lifted position is reached by an observed input. *)
  assert (Hreach : forall U L q, sren labs U -> lpos lenv U L -> ldom q L -> phant lenv p q U ->
            (forall y, bound y -> dom q y -> q <> None -> exists x, dom p x /\ bres U x = inl y) ->
            forall l j, j < lc l L -> exists i, dom p (mk_rvar l i) /\ sv U (mk_rvar l i) = mk_rvar l j).
  { intros U L q Hr Hp Ld Phq Hi l j Hj; destruct l as [x|].
    - destruct (proj2 Hp _ j Hj) as [i Ei]; exists i; split; [|exact Ei].
      destruct p; [left; discriminate|exact I].
    - destruct (opt_cases q) as [Eq|[nq Eq]].
      { destruct (proj2 Hp _ j Hj) as [i Ei]; exists i; split; [|exact Ei].
        destruct (opt_cases p) as [Ep|[n Ep]]; [rewrite Ep; exact I|].
        destruct (phant_some _ _ _ n Phq Ep) as [n' [Eq' _]]; rewrite Eq in Eq'; discriminate Eq'. }
      assert (Dq : dom q (mk_rvar None j)) by (rewrite Eq in Ld |- *; right; cbn [ldom] in Ld; cbn; lia).
      destruct (Hi (mk_rvar None j) eq_refl Dq ltac:(rewrite Eq; discriminate)) as [[g i] [Hx Ex]];
        rewrite (bres_ren lenv labs U _ Hr) in Ex; injection Ex as Ex.
      assert (Eg : g = None).
      { assert (Hin : inVb lenv L (sv U (mk_rvar g i)) = true) by (rewrite Ex; unfold inVb; apply Nat.ltb_lt, Hj).
        rewrite <- (lpos_label U L g i Hp Hin), Ex; reflexivity. }
      subst g; exists i; split; [exact Hx|exact Ex]. }
  assert (Hle : forall l j, j < lc l L1 -> j < lc l L2).
  { intros l j Hj; destruct (Hreach U1 L1 p1 Hr1 Hp1 Ld1 Ph1 Hi1 l j Hj) as [i [Hv Ei]].
    destruct (HB (mk_rvar l i) Hv) as [[E1' [E2' _]]|[E1' _]].
    - rewrite (proj1 Hp1 l i E1') in Ei; injection Ei as <-.
      pose proof (proj1 Hp2 l i E2') as E; rewrite E in E2'; unfold inVb in E2'; cbn [v_label v_index] in E2'.
      rewrite Hcnt; apply Nat.ltb_lt, E2'.
    - rewrite Ei in E1'; unfold inVb in E1'; cbn [v_label v_index] in E1'; apply Nat.ltb_ge in E1'; lia. }
  assert (Hle' : forall l j, j < lc l L2 -> j < lc l L1).
  { intros l j Hj; destruct (Hreach U2 L2 p2 Hr2 Hp2 Ld2 Ph2 Hi2 l j Hj) as [i [Hv Ei]].
    destruct (HB (mk_rvar l i) Hv) as [[E1' [E2' _]]|[_ [E2' _]]].
    - rewrite (proj1 Hp2 l i E2') in Ei; injection Ei as <-.
      pose proof (proj1 Hp1 l i E1') as E; rewrite E in E1'; unfold inVb in E1'; cbn [v_label v_index] in E1'.
      rewrite Hcnt in E1'; apply Nat.ltb_lt, E1'.
    - rewrite Ei in E2'; unfold inVb in E2'; cbn [v_label v_index] in E2'; apply Nat.ltb_ge in E2'; lia. }
  assert (Hlc : forall l, lc l L1 = lc l L2).
  { intros l; destruct (Nat.lt_trichotomy (lc l L1) (lc l L2)) as [Hlt|[E|Hlt]];
      [specialize (Hle' _ _ Hlt); lia|exact E|specialize (Hle _ _ Hlt); lia]. }
  assert (EL : L1 = L2) by (apply (lifts_unique lenv labs Hinj); assumption); subst L2.
  assert (Hsv : forall v, dom p v -> sv U1 v = sv U2 v).
  { intros [g i] Hv; destruct (HB _ Hv) as [[E1' [E2' _]]|[E1' [E2' Eu]]].
    - rewrite (proj1 Hp1 g i E1'), (proj1 Hp2 g i E2'), Hcnt; reflexivity.
    - unfold inVb, unsh in *; destruct (sv U1 (mk_rvar g i)) as [l1 i1], (sv U2 (mk_rvar g i)) as [l2 i2].
      cbn [v_label v_index] in *; injection Eu as -> Ei; apply Nat.ltb_ge in E1', E2'; f_equal; lia. }
  (* The observed bound outputs are the same, so the domains are. *)
  assert (Hp12 : p1 = p2).
  { destruct (opt_cases p) as [Ep|[n Ep]];
      [rewrite (phant_none _ _ _ Ph1 Ep), (phant_none _ _ _ Ph2 Ep); reflexivity|].
    destruct (phant_some _ _ _ n Ph1 Ep) as [m1 [Eq1 _]]; destruct (phant_some _ _ _ n Ph2 Ep) as [m2 [Eq2 _]].
    rewrite Eq1, Eq2; f_equal.
    assert (Hd12 : forall j, j < m1 -> j < m2).
    { intros j Hj; destruct (Hi1 (mk_rvar None j) eq_refl ltac:(rewrite Eq1; right; exact Hj) ltac:(rewrite Eq1; discriminate)) as [x [Hx Ex]].
      rewrite Sv1 in Ex; injection Ex as Ex; pose proof (Re2 x _ Hx (Sv2 x)) as R2'.
      rewrite <- (Hsv x Hx), Ex, Eq2 in R2'; destruct R2' as [R2'|R2']; [destruct (R2' eq_refl)|exact R2']. }
    assert (Hd21 : forall j, j < m2 -> j < m1).
    { intros j Hj; destruct (Hi2 (mk_rvar None j) eq_refl ltac:(rewrite Eq2; right; exact Hj) ltac:(rewrite Eq2; discriminate)) as [x [Hx Ex]].
      rewrite Sv2 in Ex; injection Ex as Ex; pose proof (Re1 x _ Hx (Sv1 x)) as R1'.
      rewrite (Hsv x Hx), Ex, Eq1 in R1'; destruct R1' as [R1'|R1']; [destruct (R1' eq_refl)|exact R1']. }
    destruct (Nat.lt_trichotomy m1 m2) as [Hlt|[E|Hlt]]; [specialize (Hd21 _ Hlt); lia|exact E|specialize (Hd12 _ Hlt); lia]. }
  subst p2.
  assert (Hsv' : forall v, sv U1 v = sv U2 v).
  { intros v; destruct (dom_dec p v) as [Hv|Hv]; [exact (Hsv v Hv)|].
    destruct (Hph _ _ _ _ Ph1 Ld1 Hv Hr1) as [_ [n [n' [a [Ep [Eq [Ev E1']]]]]]].
    destruct (Hph _ _ _ _ Ph2 Ld2 Hv Hr2) as [_ [n0 [n0' [a0 [Ep0 [Eq0 [Ev0 E2']]]]]]].
    rewrite E1', E2'; rewrite Eq in Eq0; injection Eq0 as <-; rewrite Ep in Ep0; injection Ep0 as <-.
    rewrite Ev in Ev0; injection Ev0 as Ea; f_equal; lia. }
  assert (EU : U1 = U2) by (apply (ren_unique lenv labs Hinj false); try assumption; intros v _; apply Hsv'); subst U2.
  split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity|]]]].
  intros [l j]; destruct (Nat.ltb_spec j (lc l L1)) as [Hj|Hj].
  - destruct (Hreach U1 L1 p1 Hr1 Hp1 Ld1 Ph1 Hi1 l j Hj) as [i [Hv Ei]].
    destruct (HB _ Hv) as [[_ [_ E]]|[E _]]; rewrite Ei in E; [exact E|].
    unfold inVb in E; cbn [v_label v_index] in E; apply Nat.ltb_ge in E; lia.
  - pose proof (Hk (mk_rvar l (j - lc l L1))) as E; unfold shiftL in E; cbn [v_label v_index] in E.
    replace (j - lc l L1 + lc l L1) with j in E by lia; exact E.
Qed.

(** *** How a word begins *)

Lemma phant_nil p : phant lenv p p SNil.
Proof. destruct p as [n|]; [intros i; reflexivity|exact I]. Qed.

Lemma bres_nil x : bres SNil x = inl x.
Proof. reflexivity. Qed.

Lemma head_b K p l : lnfL K p l ->
  (exists Sg r p', l = LS Sg :: r /\ btrm lenv Sg /\ bsegok lenv labs gt route bp K p p' Sg r /\ lnfL K p' r)
  \/ (exists U p', l = pre U /\ sshape lenv labs false U /\ sren labs U /\ phant lenv p p' U
        /\ (forall x y, dom p x -> bres U x = inl y -> dom p' y))
  \/ (exists U p' L a r2, l = pre U ++ LA L a :: r2 /\ sshape lenv labs false U /\ sren labs U /\ lpos lenv U L
        /\ phant lenv p p' U /\ (forall x y, dom p x -> bres U x = inl y -> dom p' y)
        /\ (forall y, bound y -> dom p' y -> p' <> None -> exists x, dom p x /\ bres U x = inl y)
        /\ lok lenv labs L /\ ldom p' L /\ lnfL K None r2 /\ nohop lenv K L a r2).
Proof.
  assert (Rn : forall x y, dom p x -> bres SNil x = inl y -> dom p y) by (intros x y Hx E; rewrite bres_nil in E; injection E as <-; exact Hx).
  assert (Hn0 : forall y, bound y -> dom p y -> exists x, dom p x /\ bres SNil y = inl y) by (intros y _ Hy; exists y; split; [exact Hy|reflexivity]).
  destruct l as [|[Sg|L a] r]; cbn [lnfL].
  - intros _; right; left; exists SNil, p; split; [reflexivity|].
    split; [exact (conj (Sorted.SSorted_nil _) (Forall_nil _))|split; [exact (Forall_nil _)|split; [apply phant_nil|exact Rn]]].
  - intros [Hne [p' [Hr [[Ht HS]|[Hs [Hren [Hph [Hre [->|[L [a [r2 [-> [Hp Hh]]]]]]]]]]]]]].
    + left; exists Sg, r, p'; auto.
    + right; left; exists Sg, p'; split; [destruct Sg; [destruct (Hne eq_refl)|reflexivity]|auto].
    + right; right; exists Sg, p', L, a, r2; split; [destruct Sg; [destruct (Hne eq_refl)|reflexivity]|].
      cbn [lnfL] in Hr; destruct Hr as [HL [Hld [Hr2 Hnh]]].
      exact (conj Hs (conj Hren (conj Hp (conj Hph (conj Hre (conj Hh (conj HL (conj Hld (conj Hr2 Hnh))))))))).
  - intros [HL [Hld [Hr Hnh]]]; right; right; exists SNil, p, L, a, r; split; [reflexivity|].
    split; [exact (conj (Sorted.SSorted_nil _) (Forall_nil _))|split; [exact (Forall_nil _)|split; [apply (lpos_nil lenv)|split; [apply phant_nil|]]]].
    split; [exact Rn|split; [intros y Hy Hd _; exists y; split; [exact Hd|reflexivity]|]].
    split; [exact HL|split; [exact Hld|split; [exact Hr|exact Hnh]]].
Qed.

Lemma flw_head U L a r2 K v : sren labs U ->
  flw (pre U ++ LA L a :: r2) K v = Unique.latom lenv L a (flw r2 K) (sv U v).
Proof. intros Hr; rewrite flw_app, flw_pre; cbn [flw]; apply (fs_ren lenv labs), Hr. Qed.

Lemma natl_preU U r : natl (pre U ++ r) = natl r.
Proof. destruct U; reflexivity. Qed.

Lemma natl_pre0 U : natl (pre U) = 0.
Proof. destruct U; reflexivity. Qed.

(** *** Uniqueness by induction on the length *)

Theorem lu N : forall l m K K' p e, List.length l < N -> lnfL K p l -> lnfL K' p m -> natl l = natl m ->
  deep e K -> nstuck e K -> deep e K' -> nstuck e K' ->
  ((K = FVar /\ K' = FVar) \/ ((l = [] \/ lend l) /\ (m = [] \/ lend m))) ->
  (p <> None -> lend l /\ lend m) ->
  (forall v, dom p v -> feq (flw l K v) (flw m K' v)) ->
  l = m /\ (lend l -> forall v, feq (K v) (K' v)).
Proof.
  induction N as [|N IH]; intros l m K K' p e Hlen Hl Hm Hn Hd Hs Hd' Hs' Hbase Hpl E; [lia|].
  assert (E' : forall v, dom p v -> feq (flw m K' v) (flw l K v)) by (intros v Hv; apply feq_sym, E, Hv).
  assert (Hdb : forall B, dom p (mk_rvar lbig B)) by (intros B; destruct p; [left; apply named_big|exact I]).
  (* A word that ends with a renaming has neither terms nor atoms, so the base is FVar. *)
  assert (Pre : forall U (l0 : lword), l0 = pre U -> U <> SNil -> ~ lend l0)
    by (intros U l0 -> HU [l1 [L [a E1]]]; destruct U; [destruct (HU eq_refl)|]; destruct l1 as [|? [|]]; discriminate E1).
  destruct (head_b K p l Hl) as [[Sg [r [p1 [-> [Ht [HS Hr]]]]]]|[[U [p1 [-> [HsU [HrU [PhU ReU]]]]]]|[U [p1 [L [a [r2 [-> [HsU [HrU [HpU [PhU [ReU [HiU [HL [HLd [Hr2 Hnh]]]]]]]]]]]]]]]]];
  destruct (head_b K' p m Hm) as [[Sg' [r' [p2 [-> [Ht' [HS' Hr']]]]]]|[[U' [p2 [-> [HsU' [HrU' [PhU' ReU']]]]]]|[U' [p2 [L' [a' [r2' [-> [HsU' [HrU' [HpU' [PhU' [ReU' [HiU' [HL' [HLd' [Hr2' Hnh']]]]]]]]]]]]]]]]].
  - (* Two segments with terms. *)
    cbn [natl] in Hn.
    assert (Hp1 : p <> None -> lend (LS Sg :: r)) by (intros H; exact (proj1 (Hpl H))).
    assert (Hp2 : p <> None -> lend (LS Sg' :: r')) by (intros H; exact (proj2 (Hpl H))).
    assert (Hb2 : (K = FVar /\ K' = FVar) \/ (lend (LS Sg :: r) /\ lend (LS Sg' :: r'))).
    { destruct Hbase as [B|[[B1|B1] [B2|B2]]]; [left; exact B|discriminate B1|discriminate B1|discriminate B2|right; split; assumption]. }
    assert (E1 : forall v, dom p v -> feq (fs Sg (flw r K) v) (fs Sg' (flw r' K') v)) by exact E.
    assert (E1' : forall v, dom p v -> feq (fs Sg' (flw r' K') v) (fs Sg (flw r K) v)) by exact E'.
    pose proof (first_layer K K' p p1 p2 e Sg Sg' r r' Hl Hm HS Hr HS' Hr' Hn Hd Hs Hd' Hs' Hb2 E1 Ht Ht') as Hk.
    destruct (list_eq_dec_nil r) as [Er|Hne].
    + (* The last segment of a line. *)
      pose proof (rnil K K' p p1 p2 e Sg Sg' r r' HS HS' Hr' Hn Hd Hd' Hs' Hb2 E1 Hk Er) as Er'.
      subst r r'.
      destruct Hb2 as [[-> ->]|[B _]]; [|exfalso; destruct B as [l1 [L [a B]]]; destruct l1 as [|? [|]]; discriminate B].
      assert (Ep : p = None) by (destruct p; [exfalso; destruct (Hpl ltac:(discriminate)) as [B _];
                                 destruct B as [l1 [L [a B]]]; destruct l1 as [|? [|]]; discriminate B|reflexivity]).
      assert (Hvs : forall x y, dom p x -> bres Sg x = inl y -> bres Sg' x = inl y).
      { intros x y Hx Ex; destruct (var_var FVar FVar p p1 p2 e Sg Sg' [] [] Hl Hm HS Hr HS' Hn Hd Hs Hd' Hs'
                                     (or_introl (conj eq_refl eq_refl)) E1 Hk x y Hx Ex) as [y' [Ex' F]].
        cbn [flw feq] in F; subst y'; exact Ex'. }
      assert (Hvs' : forall x y, dom p x -> bres Sg' x = inl y -> bres Sg x = inl y).
      { intros x y Hx Ex; destruct (var_var FVar FVar p p2 p1 e Sg' Sg [] [] Hm Hl HS' Hr' HS eq_refl Hd' Hs' Hd Hs
                                     (or_introl (conj eq_refl eq_refl)) E1' (keq_sym _ _ Hk) x y Hx Ex) as [y' [Ex' F]].
        cbn [flw feq] in F; subst y'; exact Ex'. }
      assert (Ep12 : p1 = p2) by (subst p; rewrite (phant_none _ _ _ (bo_phant _ _ _ _ _ _ _ _ _ _ HS) eq_refl),
                                   (phant_none _ _ _ (bo_phant _ _ _ _ _ _ _ _ _ _ HS') eq_refl); reflexivity).
      subst p2.
      rewrite (seg_final FVar FVar p p1 e Sg Sg' [] HS HS' Hd Hs Hd' Hs' (fun v => feq_refl _) Hvs Hvs' E1).
      split; [reflexivity|intros B; exfalso; destruct B as [l1 [L [a B]]]; destruct l1 as [|? [|]]; discriminate B].
    + assert (Hne' : r' <> []).
      { intros E0; apply Hne; exact (rnil K' K p p2 p1 e Sg' Sg r' r HS' HS Hr (eq_sym Hn) Hd' Hd Hs
                                       (base_sym _ _ _ _ Hb2) E1' (keq_sym _ _ Hk) E0). }
      pose proof (doms K K' p p1 p2 e Sg Sg' r r' Hl Hm HS Hr HS' Hr' Hn Hd Hs Hd' Hs' Hb2 Hp1 E1 Ht Ht' Hne) as Ep12.
      subst p2.
      destruct (IH r r' K K' p1 e ltac:(cbn [List.length] in Hlen; lia) Hr Hr' Hn Hd Hs Hd' Hs') as [Err HK].
      * destruct Hb2 as [B|[B1 B2]]; [left; exact B|right; split; right; [exact (lend_cons _ _ B1 Hne)|exact (lend_cons _ _ B2 Hne')]].
      * intros H; assert (Hp0 : p <> None).
        { intros ->; rewrite (phant_none _ _ _ (bo_phant _ _ _ _ _ _ _ _ _ _ HS) eq_refl) in H; exact (H eq_refl). }
        destruct (Hpl Hp0) as [B1 B2]; split; [exact (lend_cons _ _ B1 Hne)|exact (lend_cons _ _ B2 Hne')].
      * exact (rest_eq K K' p p1 p1 e Sg Sg' r r' Hl Hm HS Hr HS' Hr' Hn Hd Hs Hd' Hs' Hb2 Hp1 E1 Ht Ht' Hne).
      * subst r'.
        assert (Hbk : forall v, feq (flw r K v) (flw r K' v)).
        { destruct Hb2 as [[-> ->]|[B1 _]]; [intros v; apply feq_refl|].
          intros v; apply flw_cong, HK, (lend_cons _ _ B1 Hne). }
        pose proof (var_same K K' p p1 p1 e Sg Sg' r r Hl Hm HS Hr HS' Hr' Hn Hd Hs Hd' Hs' Hb2 Hp1 E1 Ht Ht' Hne) as Hvs.
        pose proof (var_same K' K p p1 p1 e Sg' Sg r r Hm Hl HS' Hr' HS Hr (eq_sym Hn) Hd' Hs' Hd Hs
                      (base_sym _ _ _ _ Hb2) Hp2 E1' Ht' Ht Hne') as Hvs'.
        rewrite (seg_final K K' p p1 e Sg Sg' r HS HS' Hd Hs Hd' Hs' Hbk Hvs Hvs' E1).
        split; [reflexivity|intros B; apply HK, (lend_cons _ _ B Hne)].
  - (* A segment with a term against a renaming at the end. *)
    exfalso; destruct Ht as [x [[[u b] w] Ex]].
    pose proof (E x (phant_dom lenv _ _ _ _ _ (bo_phant _ _ _ _ _ _ _ _ _ _ HS) Ex)) as F.
    cbn [flw] in F; rewrite fs_bres, Ex, flw_pre, (fs_ren lenv labs _ _ _ HrU') in F.
    assert (HK' : K' = FVar).
    { destruct Hbase as [[_ HK']|[[Bl|Bl] _]]; [exact HK'|discriminate Bl|].
      pose proof (lend_natl _ Bl) as Nl; rewrite Hn in Nl; destruct U'; cbn in Nl; lia. }
    rewrite HK' in F; destruct F.
  - (* A segment with a term against an atom. *)
    exfalso; destruct Ht as [x [[[u b] w] Ex]].
    pose proof (bo_br _ _ _ _ _ _ _ _ _ _ HS x u b w Ex) as Hb.
    pose proof (E x (phant_dom lenv _ _ _ _ _ (bo_phant _ _ _ _ _ _ _ _ _ _ HS) Ex)) as F.
    rewrite (flw_head U' L' a' r2' K' x HrU') in F; cbn [flw] in F; rewrite fs_bres, Ex in F.
    unfold Unique.latom in F; destruct (Nat.ltb_spec (v_index (sv U' x)) (lc (v_label (sv U' x)) L')) as [Hy|Hy];
      [|destruct F].
    destruct (flw r2' K' (sv U' x)) as [|u2 b2 k2|] eqn:Ey; cbn [feq] in F; try contradiction.
    refine (cross lenv labs gt route bp K K' p (LS Sg :: r) (pre U' ++ LA L' a' :: r2') e x u b w r u2 b2 k2
              (pre U') L' a' r2' (sv U' x) Hm Hn Hd Hd' (fun i => E _ (Hdb i)) _ (proj1 Hb) eq_refl
              (natl_pre0 U') Hy Ey F).
    cbn [treach]; rewrite Ex; reflexivity.
  - (* A renaming at the end against a segment with a term. *)
    exfalso; destruct Ht' as [x [[[u b] w] Ex]].
    pose proof (E' x (phant_dom lenv _ _ _ _ _ (bo_phant _ _ _ _ _ _ _ _ _ _ HS') Ex)) as F.
    cbn [flw] in F; rewrite fs_bres, Ex, flw_pre, (fs_ren lenv labs _ _ _ HrU) in F.
    assert (HK : K = FVar).
    { destruct Hbase as [[HK _]|[_ [Bm|Bm]]]; [exact HK|discriminate Bm|].
      pose proof (lend_natl _ Bm) as Nl; rewrite <- Hn in Nl; destruct U; cbn in Nl; lia. }
    rewrite HK in F; destruct F.
  - (* Two renamings at the end. *)
    destruct (list_eq_dec_nil (pre U)) as [EU|NU].
    + assert (EU' : pre U' = []).
      { destruct (list_eq_dec_nil (pre U')) as [EU'|NU']; [exact EU'|exfalso].
        destruct U as [|h ts m0 r0]; [|discriminate EU]; destruct U' as [|h' ts' m' r'0]; [destruct (NU' eq_refl)|].
        destruct Hbase as [[-> ->]|[_ [Bm|Bm]]]; [|discriminate Bm|exact (Pre (SEnt h' ts' m' r'0) _ eq_refl ltac:(discriminate) Bm)].
        assert (Ep : p = None) by (destruct p; [destruct (Hpl ltac:(discriminate)) as [B _]; destruct (lend_nil B)|reflexivity]).
        assert (H0 : SNil = SEnt h' ts' m' r'0).
        { apply (ren_unique lenv labs Hinj false); try assumption; intros v _.
          pose proof (E v ltac:(rewrite Ep; exact I)) as F; cbn [flw pre] in F.
          rewrite (fs_ren lenv labs _ _ _ HrU') in F; cbn [feq] in F; exact F. }
        discriminate H0. }
      rewrite EU, EU'; split; [reflexivity|intros B; destruct (lend_nil B)].
    + assert (HKK : K = FVar /\ K' = FVar).
      { destruct Hbase as [B|[[Bl|Bl] _]]; [exact B|exact (False_ind _ (NU Bl))|].
        exfalso; apply (Pre U _ eq_refl); [intros ->; exact (NU eq_refl)|exact Bl]. }
      destruct HKK as [-> ->].
      assert (Ep : p = None).
      { destruct p; [|reflexivity]; destruct (Hpl ltac:(discriminate)) as [B _].
        exfalso; apply (Pre U _ eq_refl); [intros ->; exact (NU eq_refl)|exact B]. }
      assert (EU : U = U').
      { apply (ren_unique lenv labs Hinj false); try assumption; intros v _.
        pose proof (E v ltac:(rewrite Ep; exact I)) as F; rewrite !flw_pre, !(fs_ren lenv labs) in F by assumption.
        cbn [feq] in F; exact F. }
      subst U'; split; [reflexivity|intros B; exfalso; apply (Pre U _ eq_refl); [intros ->; exact (NU eq_refl)|exact B]].
  - (* A renaming at the end against an atom. *)
    exfalso; rewrite natl_pre0, natl_preU in Hn; cbn [natl] in Hn; lia.
  - (* An atom against a segment with a term. *)
    exfalso; destruct Ht' as [x [[[u b] w] Ex]].
    pose proof (bo_br _ _ _ _ _ _ _ _ _ _ HS' x u b w Ex) as Hb.
    pose proof (E' x (phant_dom lenv _ _ _ _ _ (bo_phant _ _ _ _ _ _ _ _ _ _ HS') Ex)) as F.
    rewrite (flw_head U L a r2 K x HrU) in F; cbn [flw] in F; rewrite fs_bres, Ex in F.
    unfold Unique.latom in F; destruct (Nat.ltb_spec (v_index (sv U x)) (lc (v_label (sv U x)) L)) as [Hy|Hy];
      [|destruct F].
    destruct (flw r2 K (sv U x)) as [|u2 b2 k2|] eqn:Ey; cbn [feq] in F; try contradiction.
    refine (cross lenv labs gt route bp K' K p (LS Sg' :: r') (pre U ++ LA L a :: r2) e x u b w r' u2 b2 k2
              (pre U) L a r2 (sv U x) Hl (eq_sym Hn) Hd' Hd (fun i => E' _ (Hdb i)) _ (proj1 Hb) eq_refl
              (natl_pre0 U) Hy Ey F).
    cbn [treach]; rewrite Ex; reflexivity.
  - (* An atom against a renaming at the end. *)
    exfalso; rewrite natl_pre0, natl_preU in Hn; cbn [natl] in Hn; lia.
  - (* Two atoms. *)
    rewrite !natl_preU in Hn; cbn [natl] in Hn; injection Hn as Hn.
    destruct (peel_dom p p1 p2 U L a (flw r2 K) (natl r2 + e) U' L' a' (flw r2' K') (natl r2' + e)
                HsU HrU HL HpU PhU ReU HiU HLd HsU' HrU' HL' HpU' PhU' ReU' HiU' HLd'
                (deep_flw lenv _ _ _ Hd) (nstuck_flw lenv _ _ _ Hs Hd) (deep_flw lenv _ _ _ Hd') (nstuck_flw lenv _ _ _ Hs' Hd'))
      as [<- [<- [<- [<- HR]]]].
    { intros v Hv; pose proof (E v Hv) as F; rewrite !flw_head in F by assumption; exact F. }
    assert (Hlen2 : List.length r2 < N) by (rewrite length_app in Hlen; cbn [List.length] in Hlen; lia).
    assert (Hb2 : (K = FVar /\ K' = FVar) \/ ((r2 = [] \/ lend r2) /\ (r2' = [] \/ lend r2'))).
    { destruct Hbase as [B|[[Bl|Bl] [Bm|Bm]]]; [left; exact B| | | |].
      - destruct U; discriminate Bl.
      - destruct U; discriminate Bl.
      - destruct U; discriminate Bm.
      - right; split.
        + destruct (list_eq_dec_nil r2) as [->|Ne]; [left; reflexivity|right].
          destruct Bl as [l1 [L1 [a1 Bl]]]; destruct (@exists_last _ r2 Ne) as [r3 [st Er3]]; rewrite Er3 in Bl |- *.
          rewrite app_comm_cons, app_assoc in Bl; apply app_inj_tail in Bl as [_ ->]; exists r3, L1, a1; reflexivity.
        + destruct (list_eq_dec_nil r2') as [->|Ne]; [left; reflexivity|right].
          destruct Bm as [l1 [L1 [a1 Bm]]]; destruct (@exists_last _ r2' Ne) as [r3 [st Er3]]; rewrite Er3 in Bm |- *.
          rewrite app_comm_cons, app_assoc in Bm; apply app_inj_tail in Bm as [_ ->]; exists r3, L1, a1; reflexivity. }
    destruct (IH r2 r2' K K' None e Hlen2 Hr2 Hr2' Hn Hd Hs Hd' Hs' Hb2 (fun H => False_ind _ (H eq_refl))
                (fun v _ => HR v)) as [<- HK].
    split; [reflexivity|]; intros B.
    destruct (list_eq_dec_nil r2) as [->|Ne]; [exact HR|].
    apply HK; destruct B as [l1 [L1 [a1 B]]]; destruct (@exists_last _ r2 Ne) as [r3 [st Er3]]; rewrite Er3 in B |- *.
    rewrite app_comm_cons, app_assoc in B; apply app_inj_tail in B as [_ ->]; exists r3, L1, a1; reflexivity.
Qed.

End Main.

(** ** Uniqueness of canonical words with branches *)

Section Final.

Variable lenv : list label.
Variable labs : list lexp.
Hypothesis Hinj : forall h h', In h labs -> In h' labs -> lden lenv h = lden lenv h' -> h = h'.
Variable gt : (rvar -> fres) -> (rvar -> fres) -> Prop.
Hypothesis gt_irrefl : forall k k', keq k k' -> ~ gt k k'.
Hypothesis gt_trans : forall k1 k2 k3, gt k1 k2 -> gt k2 k3 -> gt k1 k3.
Hypothesis gt_keq : forall k1 k1' k2 k2', keq k1 k1' -> keq k2 k2' -> gt k1 k2 -> gt k1' k2'.
Variable route : (rvar -> fres) -> rvar -> rvar -> Prop.
Hypothesis route_uniq : forall k k' x y y', keq k k' -> route k x y -> route k' x y' ->
  feq (k y) (k' y') -> named y -> y = y'.

Local Notation lnfB := (lnfB lenv labs gt route).
Local Notation flw := (flw lenv).

Theorem bu n : forall l m K K' p e, lnfB n K p l -> lnfB n K' p m -> natl l = natl m ->
  deep e K -> nstuck e K -> deep e K' -> nstuck e K' ->
  ((K = FVar /\ K' = FVar) \/ ((l = [] \/ lend l) /\ (m = [] \/ lend m))) ->
  (p <> None -> lend l /\ lend m) ->
  (forall v, dom p v -> feq (flw l K v) (flw m K' v)) ->
  l = m /\ (lend l -> forall v, feq (K v) (K' v)).
Proof.
  induction n as [|n IH]; intros l m K K' p e Hl Hm; cbn [lnfB] in Hl, Hm.
  - exact (lu lenv labs Hinj gt gt_irrefl gt_trans gt_keq route route_uniq (fun _ _ _ => False)
             (fun _ _ _ _ _ _ H => False_ind _ H) (S (List.length l)) l m K K' p e (Nat.lt_succ_diag_r _) Hl Hm).
  - refine (lu lenv labs Hinj gt gt_irrefl gt_trans gt_keq route route_uniq (lnfB n) _
             (S (List.length l)) l m K K' p e (Nat.lt_succ_diag_r _) Hl Hm).
    intros l0 m0 K0 K0' p0 e0 H0 H0' Hn Hd Hs Hd' Hs' B0 B0' E0.
    destruct (IH l0 m0 K0 K0' p0 e0 H0 H0' Hn Hd Hs Hd' Hs' (or_intror (conj (or_intror B0) (or_intror B0')))
                (fun _ => conj B0 B0') E0) as [Eq HK].
    split; [exact Eq|exact (HK B0)].
Qed.

(** Branches nest at most [n] deep; more room changes nothing. *)
Lemma bsegok_mono (bp bp' : (rvar -> fres) -> option nat -> lword -> Prop) K p p' Sg r :
  (forall K p l, bp K p l -> bp' K p l) ->
  bsegok lenv labs gt route bp K p p' Sg r -> bsegok lenv labs gt route bp' K p p' Sg r.
Proof.
  intros Hb HS; destruct HS; constructor; try assumption.
  intros x u b w E; destruct (bo_br0 x u b w E) as [A [B [C [D G]]]].
  split; [exact A|split; [exact B|split; [exact C|split; [exact D|intros H; exact (Hb _ _ _ (G H))]]]].
Qed.

Lemma lnfL_mono (bp bp' : (rvar -> fres) -> option nat -> lword -> Prop) :
  (forall K p l, bp K p l -> bp' K p l) ->
  forall l K p, lnfL lenv labs gt route bp K p l -> lnfL lenv labs gt route bp' K p l.
Proof.
  intros Hb l; induction l as [|st r IH]; intros K p; [exact (fun H => H)|].
  destruct st as [s|L a]; cbn [lnfL].
  - intros [Hne [p' [Hr Hc]]]; split; [exact Hne|exists p'; split; [exact (IH _ _ Hr)|]].
    destruct Hc as [[Ht HS]|Hren]; [left; split; [exact Ht|exact (bsegok_mono bp bp' _ _ _ _ _ Hb HS)]|right; exact Hren].
  - intros [A [B [C D]]]; split; [exact A|split; [exact B|split; [exact (IH _ _ C)|exact D]]].
Qed.

Lemma lnfB_mono n : forall n' K p l, n <= n' -> lnfB n K p l -> lnfB n' K p l.
Proof.
  induction n as [|n IH]; intros [|n'] K p l Hle; cbn [lnfB]; try lia.
  - apply lnfL_mono; intros _ _ _ [].
  - apply lnfL_mono; intros _ _ _ [].
  - apply lnfL_mono; intros K0 p0 l0; apply IH; lia.
Qed.

(** Canonical lines that mean the same in the free model are the same. *)
Theorem line_unique n n' l m : lnfB n FVar None l -> lnfB n' FVar None m ->
  (forall v, feq (flw l FVar v) (flw m FVar v)) -> l = m.
Proof.
  intros Hl Hm E.
  apply (bu (Nat.max n n') l m FVar FVar None 0); try apply deep_FVar; try apply nstuck_FVar.
  - exact (lnfB_mono n _ _ _ _ (Nat.le_max_l _ _) Hl).
  - exact (lnfB_mono n' _ _ _ _ (Nat.le_max_r _ _) Hm).
  - apply (deep_unique _ _ _ _ (deep_R lenv l) (deep_R lenv m)); intros i; apply E.
  - left; split; reflexivity.
  - intros H; destruct (H eq_refl).
  - intros v _; apply E.
Qed.

End Final.
