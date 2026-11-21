(** * The known order built from facts is a strict order

    [Normalise.order_of] works out, for each label atom, the atoms the
    facts put above it, by a search over the edges they give, and checks
    that what it found is closed under those edges.  Here: what a search
    finds is reachable ([search_path]), so with the check the table is
    transitive ([tmem_trans]); the known order is then irreflexive when
    the facts hold under some interpretation of the labels
    ([order_of_irrefl]) and transitive when the facts are between label
    atoms ([order_of_trans]).  Those are the hypotheses of
    [HRefine.hn_eq_correct]. *)

From Stdlib Require Import List Bool NArith PArith FMapPositive String.
From ShiftedNames.Core Require Import Label Normalise.
Import ListNotations.

Section Graph.

Variable adj : PositiveMap.t (list N).

(** A non-empty path along the edges. *)
Inductive path (a : N) : N -> Prop :=
| PStep w : In w (succs adj a) -> path a w
| PNext u w : path a u -> In w (succs adj u) -> path a w.

(** Every atom found is stored under its own key. *)
Definition keyed (T : PositiveMap.t N) : Prop := forall p x, PositiveMap.find p T = Some x -> p = akey x.

Lemma search_keyed fuel : forall stack seen, keyed seen -> keyed (search adj fuel stack seen).
Proof.
  induction fuel as [|f IH]; intros stack seen H; [exact H|]; destruct stack as [|u st]; cbn [search]; [exact H|].
  destruct (PositiveMap.find (akey u) seen); apply IH; [exact H|].
  intros p x; destruct (Pos.eq_dec p (akey u)) as [->|Ne].
  - rewrite PositiveMap.gss; intros E; injection E as <-; reflexivity.
  - rewrite PositiveMap.gso by exact Ne; apply H.
Qed.

Lemma inset_iff T j : inset T j = true <-> PositiveMap.find (akey j) T <> None.
Proof. unfold inset; destruct (PositiveMap.find (akey j) T); split; intros H; try discriminate; try reflexivity; congruence. Qed.

Lemma search_path a fuel : forall v, inset (search adj fuel (succs adj a) (PositiveMap.empty _)) v = true -> path a v.
Proof.
  intros v H; apply inset_iff in H; revert v H; apply (search_inv (path a) adj).
  - intros u w Hu Hw; exact (PNext a u w Hu Hw).
  - rewrite Forall_forall; intros w Hw; exact (PStep a w Hw).
  - intros v; rewrite PositiveMap.gempty; intros H; contradiction.
Qed.

Lemma closed_at_spec p T : closed_at adj p T = true -> keyed T ->
  (forall w, In w (psuccs adj p) -> inset T w = true)
  /\ (forall v w, inset T v = true -> In w (succs adj v) -> inset T w = true).
Proof.
  unfold closed_at; destruct (forallb (inset T) (psuccs adj p)) eqn:E1; [|discriminate]; intros E2 HK.
  rewrite forallb_forall in E1, E2; split; [exact E1|].
  intros v w Hv Hw; apply inset_iff in Hv.
  destruct (PositiveMap.find (akey v) T) as [x|] eqn:Ex; [|contradiction].
  pose proof (HK _ _ Ex) as Ekx; apply akey_inj in Ekx; subst x.
  apply PositiveMap.elements_correct in Ex; specialize (E2 _ Ex); cbn in E2.
  rewrite forallb_forall in E2; apply E2, Hw.
Qed.

Lemma path_closed a T : (forall w, In w (succs adj a) -> inset T w = true) ->
  (forall v w, inset T v = true -> In w (succs adj v) -> inset T w = true) ->
  forall w, path a w -> inset T w = true.
Proof. intros H1 H2 w P; induction P as [w Hw|u w P IH Hw]; [apply H1, Hw|apply (H2 u w IH Hw)]. Qed.

(** With the check, the table is transitive. *)
Lemma tmem_trans f : let t := PositiveMap.mapi (fun _ st => search adj f st (PositiveMap.empty _)) adj in
  closed adj t = true -> forall i j k, tmem t i j = true -> tmem t j k = true -> tmem t i k = true.
Proof.
  intros t C i j k; unfold tmem, t; rewrite !PositiveMap.gmapi; unfold option_map.
  destruct (PositiveMap.find (akey i) adj) as [si|] eqn:Ei; [|discriminate].
  destruct (PositiveMap.find (akey j) adj) as [sj|] eqn:Ej; [|discriminate].
  intros Hij Hjk.
  assert (Pjk : path j k) by (apply (search_path j f k); unfold succs; rewrite Ej; exact Hjk).
  set (Ti := search adj f si (PositiveMap.empty _)) in *.
  assert (Ci : closed_at adj (akey i) Ti = true).
  { unfold closed in C; rewrite forallb_forall in C.
    assert (In (akey i, Ti) (PositiveMap.elements t)).
    { apply PositiveMap.elements_correct; unfold t; rewrite PositiveMap.gmapi, Ei; reflexivity. }
    exact (C _ H). }
  assert (Ki : keyed Ti) by (apply search_keyed; intros p x; rewrite PositiveMap.gempty; discriminate).
  destruct (closed_at_spec _ _ Ci Ki) as [_ H2].
  apply (path_closed j Ti); [|exact H2|exact Pjk].
  intros w Hw; exact (H2 j w Hij Hw).
Qed.

End Graph.

(** ** The known order *)

Definition is_atom (a : lexp) : bool := match a with LAtom _ => true | _ => false end.

(** Facts between label atoms only. *)
Definition atom_facts (l : list (lexp * lexp)) : bool :=
  forallb (fun '(x, y) => match x, y with LAtom _, LAtom _ => true | _, _ => false end) l.

(** With facts between atoms, following them says nothing about a pair
    that is not two atoms beyond the concrete order. *)
Lemma lt_reach_atoms l (Hl : atom_facts l = true) fuel : forall a b,
  is_atom a && is_atom b = false -> lt_reach l fuel a b = lt_base a b.
Proof.
  induction fuel as [|f IH]; intros a b Hab; cbn [lt_reach]; destruct (lt_base a b) eqn:Eb; try reflexivity.
  apply not_true_iff_false; intros H; apply existsb_exists in H as [[x y] [Hin H]].
  unfold atom_facts in Hl; rewrite forallb_forall in Hl; specialize (Hl _ Hin); cbn in Hl.
  destruct x as [| |i], y as [| |j]; try discriminate Hl.
  destruct a as [|s|a'], b as [|t|b']; simpl in H, Hab, Eb; try discriminate.
  rewrite IH in H by reflexivity; simpl in H; destruct (N.eqb i a'); discriminate.
Qed.

Lemma lt_known_other l (Hl : atom_facts l = true) a b :
  is_atom a && is_atom b = false -> lt_known (order_of l) a b = lt_base a b.
Proof.
  intros H; destruct a as [| |i], b as [| |j]; try discriminate H;
    unfold lt_known, lt_list; unfold order_of; cbn [ofacts]; apply lt_reach_atoms; assumption.
Qed.

Lemma order_of_trans l : atom_facts l = true ->
  forall a b c, lt_known (order_of l) a b = true -> lt_known (order_of l) b c = true -> lt_known (order_of l) a c = true.
Proof.
  intros Hl a b c.
  destruct a as [|s|i], b as [|t|j], c as [|u|k]; intros H1 H2;
    try (rewrite (lt_known_other l Hl) in H1 by reflexivity);
    try (rewrite (lt_known_other l Hl) in H2 by reflexivity);
    try (rewrite (lt_known_other l Hl) by reflexivity);
    cbn [lt_base] in *; try discriminate; try reflexivity.
  - apply (is_less_than_label_transitive s t u H1 H2).
  - unfold lt_known, order_of in *; cbn [otab] in *.
    destruct (closed _ _) eqn:C; [|discriminate].
    exact (tmem_trans _ _ C i j k H1 H2).
Qed.

Lemma order_of_irrefl l lenv : lfacts_ok lenv l -> forall a, lt_known (order_of l) a a = false.
Proof.
  intros Hl a; destruct (lt_known (order_of l) a a) eqn:E; [exfalso|reflexivity].
  exact (olabel_lt_irrefl _ (lt_known_sound lenv (order_of l) (order_of_ok lenv l Hl) a a E)).
Qed.
