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

Record bsegok (bp : (rvar -> fres) -> option nat -> lword -> Prop) (K : rvar -> fres) (p p' : option nat)
    (Sg : seg) (r : lword) : Prop := {
  bo_shape : sshape lenv labs false Sg;
  bo_tlab : Forall (tlab labs) (stgts Sg);
  bo_order : forall y rt t, treach r y = Some (rt, t) -> gt (flw r K) (flw rt K);
  bo_last : forall G, r = [LS G] -> keq (flw r K) K -> btrm lenv G;
  bo_route : forall x y, dom p x -> bres Sg x = inl y -> route (flw r K) x y;
  bo_real : forall x y, dom p x -> bres Sg x = inl y -> dom p' y;
  bo_phant : phant p p' Sg;
  bo_hit : r <> [] -> forall y, bound y -> dom p' y -> exists x, dom p x /\ bres Sg x = inl y;
  bo_binj : binj (flw r K);
  bo_num : r <> [] -> num_first lenv Sg (flw r K);
  bo_br : forall x u b w, bres Sg x = inr (u, b, w) -> brok bp (flw r K) b w
}.

(** A renaming segment: at the end of the line, or in lift position
    before an atom. *)
Definition renok (p p' : option nat) (Sg : seg) (r : lword) : Prop :=
  sshape lenv labs false Sg /\ sren labs Sg /\ phant p p' Sg
  /\ (forall x y, dom p x -> bres Sg x = inl y -> dom p' y)
  /\ (r = [] \/ exists L a r2, r = LA L a :: r2 /\ lpos lenv Sg L
        /\ forall y, bound y -> dom p' y -> exists x, dom p x /\ bres Sg x = inl y).

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
