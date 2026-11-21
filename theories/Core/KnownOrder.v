(** * The known order built from facts is a strict order

    [Normalise.order_of] works out, for each label atom, the atoms the
    facts put above it, by a depth-first search over the edges they give.
    Here: the search finds exactly the atoms reachable from its start
    ([visit_complete], [reach_inv]), so the table is transitive
    ([order_of_tmem_trans]); the known order is then irreflexive when the
    facts hold under some interpretation of the labels ([order_of_irrefl])
    and transitive when they are between label atoms ([order_of_trans]).
    Those are the hypotheses of [HRefine.hn_eq_correct]. *)

From Stdlib Require Import List Bool NArith PArith FMapPositive String Lia.
From ShiftedNames.Core Require Import Label Normalise.
Import ListNotations.

Section Graph.

Variable adj : PositiveMap.t (list N).

(** A non-empty path along the edges. *)
Inductive path (a : N) : N -> Prop :=
| PStep w : In w (succs adj a) -> path a w
| PNext u w : path a u -> In w (succs adj u) -> path a w.

Lemma path_trans a b c : path a b -> path b c -> path a c.
Proof.
  intros Pab Pbc; induction Pbc as [w Hw|u w _ IH Hw]; [exact (PNext a b w Pab Hw)|exact (PNext a u w IH Hw)].
Qed.

(** *** What a search finds is reachable *)

Lemma reach_path a n : forall v,
  inset (fold_left (fun s w => visit adj n w s) (succs adj a) (PositiveMap.empty _)) v = true -> path a v.
Proof.
  apply (reach_inv adj (path a)); [intros u w Hu Hw; exact (PNext a u w Hu Hw)|].
  rewrite Forall_forall; intros w Hw; exact (PStep a w Hw).
Qed.

(** *** Everything reachable is found *)

Definition U : list N := nodes adj.

Lemma succs_nodes x w : In w (succs adj x) -> In w U.
Proof.
  unfold succs; destruct (PositiveMap.find (akey x) adj) as [l|] eqn:E; [|intros []]; intros Hw.
  apply PositiveMap.elements_correct in E; unfold U, nodes; apply in_concat; exists l; split; [|exact Hw].
  apply in_map_iff; exists (akey x, l); split; [reflexivity|exact E].
Qed.

(** The atoms of [U] not yet found. *)
Definition count (s : PositiveMap.t unit) : nat := List.length (filter (fun x => negb (inset s x)) U).

Lemma filter_le (p q : N -> bool) l : (forall x, q x = true -> p x = true) -> List.length (filter q l) <= List.length (filter p l).
Proof.
  intros H; induction l as [|x l IH]; cbn [filter]; [lia|].
  destruct (q x) eqn:Eq; [rewrite (H x Eq); cbn [List.length]; lia|destruct (p x); cbn [List.length]; lia].
Qed.

Lemma filter_lt (p q : N -> bool) l : (forall x, q x = true -> p x = true) ->
  forall y, In y l -> p y = true -> q y = false -> List.length (filter q l) < List.length (filter p l).
Proof.
  intros H; induction l as [|x l IH]; intros y Hy Hp Hq; [destruct Hy|]; cbn [filter].
  pose proof (filter_le p q l H) as Le.
  destruct Hy as [<-|Hy]; [rewrite Hp, Hq; cbn [List.length]; lia|].
  specialize (IH y Hy Hp Hq).
  destruct (q x) eqn:Eq; [rewrite (H x Eq); cbn [List.length]; lia|destruct (p x); cbn [List.length]; lia].
Qed.

Definition sub (s r : PositiveMap.t unit) : Prop := forall x, inset s x = true -> inset r x = true.

Lemma count_mono s r : sub s r -> count r <= count s.
Proof.
  intros H; apply filter_le; intros x Hx; apply negb_true_iff in Hx; apply negb_true_iff.
  destruct (inset s x) eqn:E; [rewrite (H x E) in Hx; discriminate|reflexivity].
Qed.

Lemma count_add v s : In v U -> inset s v = false -> count (PositiveMap.add (akey v) tt s) < count s.
Proof.
  intros Hv Hs; apply (filter_lt _ _ U) with (y := v); [| |rewrite Hs; reflexivity|rewrite inset_add, N.eqb_refl; reflexivity].
  - intros x; rewrite inset_add; destruct (N.eqb x v); [discriminate|auto].
  - exact Hv.
Qed.

Lemma count_le s : count s <= List.length U.
Proof. unfold count; induction U as [|x l IH]; cbn [filter]; [lia|destruct (negb _); cbn [List.length]; lia]. Qed.

(** What a visit marks, beyond [s], has its successors marked. *)
Definition closed_new (s r : PositiveMap.t unit) : Prop :=
  forall x w, inset r x = true -> inset s x = false -> In w (succs adj x) -> inset r w = true.

Definition visits_ok (n : nat) : Prop := forall v s, In v U -> count s <= n ->
  sub s (visit adj n v s) /\ inset (visit adj n v s) v = true /\ closed_new s (visit adj n v s).

Lemma fold_complete n : visits_ok n -> forall ws s, (forall w, In w ws -> In w U) -> count s <= n ->
  let r := fold_left (fun s w => visit adj n w s) ws s in
  sub s r /\ (forall w, In w ws -> inset r w = true) /\ closed_new s r.
Proof.
  intros VC; induction ws as [|w ws IH]; intros s Hws Hc; cbn [fold_left].
  - split; [intros x Hx; exact Hx|split; [intros w []|intros x w Hx Hn; rewrite Hx in Hn; discriminate]].
  - destruct (VC w s (Hws w (or_introl eq_refl)) Hc) as [S1 [W1 C1]].
    set (r1 := visit adj n w s) in *.
    assert (Hc1 : count r1 <= n) by (pose proof (count_mono s r1 S1); lia).
    destruct (IH r1 (fun x Hx => Hws x (or_intror Hx)) Hc1) as [S2 [W2 C2]].
    split; [intros x Hx; apply S2, S1, Hx|split].
    + intros x [<-|Hx]; [apply S2, W1|apply W2, Hx].
    + intros x u Hx Hn Hu; destruct (inset r1 x) eqn:E1; [apply S2, (C1 x u E1 Hn Hu)|apply (C2 x u Hx E1 Hu)].
Qed.

Lemma visit_complete n : visits_ok n.
Proof.
  induction n as [|n IH]; intros v s Hv Hc; cbn [visit].
  - destruct (inset s v) eqn:E; [|pose proof (count_add v s Hv E); lia].
    split; [intros x Hx; exact Hx|split; [reflexivity|intros x w Hx Hn; rewrite Hx in Hn; discriminate]].
  - destruct (PositiveMap.find (akey v) s) eqn:F.
    + assert (E : inset s v = true) by (unfold inset; rewrite F; reflexivity).
      split; [intros x Hx; exact Hx|split; [exact E|intros x w Hx Hn; rewrite Hx in Hn; discriminate]].
    + assert (E : inset s v = false) by (unfold inset; rewrite F; reflexivity).
      pose proof (count_add v s Hv E) as Lt.
      set (s0 := PositiveMap.add (akey v) tt s) in *.
      assert (Hc0 : count s0 <= n) by lia.
      destruct (fold_complete n IH (succs adj v) s0 (succs_nodes v) Hc0) as [S2 [W2 C2]].
      assert (Hs0 : forall x, inset s0 x = if N.eqb x v then true else inset s x) by (intros x; apply inset_add).
      split; [|split].
      * intros x Hx; apply S2; rewrite Hs0, Hx; destruct (N.eqb x v); reflexivity.
      * apply S2; rewrite Hs0, N.eqb_refl; reflexivity.
      * intros x w Hx Hn Hw; destruct (N.eqb_spec x v) as [->|Ne]; [apply W2, Hw|].
        apply (C2 x w Hx); [rewrite Hs0; destruct (N.eqb_spec x v); [contradiction|exact Hn]|exact Hw].
Qed.

Lemma reach_complete a n : List.length U <= n -> forall k, path a k ->
  inset (fold_left (fun s w => visit adj n w s) (succs adj a) (PositiveMap.empty _)) k = true.
Proof.
  intros Hn; set (r := fold_left _ _ _).
  assert (Hc : count (PositiveMap.empty unit) <= n) by (pose proof (count_le (PositiveMap.empty unit)); lia).
  destruct (fold_complete n (visit_complete n) (succs adj a) _ (succs_nodes a) Hc) as [_ [W C]].
  intros k P; induction P as [w Hw|u w _ IHp Hw]; [apply W, Hw|].
  apply (C u w IHp); [unfold inset; rewrite PositiveMap.gempty; reflexivity|exact Hw].
Qed.

End Graph.

(** The table is transitive. *)
Lemma order_of_tmem_trans l i j k :
  otab (order_of l) i j = true -> otab (order_of l) j k = true -> otab (order_of l) i k = true.
Proof.
  unfold order_of; cbn [otab]; unfold tmem; rewrite !PositiveMap.gmapi; unfold option_map.
  set (adj := edges l); set (n := List.length (nodes adj)).
  destruct (PositiveMap.find (akey i) adj) as [si|] eqn:Ei; [|discriminate].
  destruct (PositiveMap.find (akey j) adj) as [sj|] eqn:Ej; [|discriminate].
  assert (Si : si = succs adj i) by (unfold succs; rewrite Ei; reflexivity).
  assert (Sj : sj = succs adj j) by (unfold succs; rewrite Ej; reflexivity).
  rewrite Si, Sj; intros Hij Hjk.
  apply (reach_complete adj i n (le_n _)).
  exact (path_trans adj i j k (reach_path adj i n j Hij) (reach_path adj j n k Hjk)).
Qed.

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
  - exact (order_of_tmem_trans l i j k H1 H2).
Qed.

Lemma order_of_irrefl l lenv : lfacts_ok lenv l -> forall a, lt_known (order_of l) a a = false.
Proof.
  intros Hl a; destruct (lt_known (order_of l) a a) eqn:E; [exfalso|reflexivity].
  exact (olabel_lt_irrefl _ (lt_known_sound lenv (order_of l) (order_of_ok lenv l Hl) a a E)).
Qed.
