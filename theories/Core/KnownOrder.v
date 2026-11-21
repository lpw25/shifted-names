(** * The known order built from facts is a strict order

    [Normalise.order_of] works out, for each label atom, the atoms the
    facts put above it, by a depth-first search over the edges between
    atoms, and the least concrete label above it and the greatest below.
    Here: the search finds exactly the atoms reachable from its start
    ([visit_complete], [reach_inv]); the table is reachability, or the
    first atom's [up] at or below the second's [down] ([otab_iff]); [up]
    and [down] only tighten along a path ([up_path], [down_path]).  With
    facts that hold under some interpretation of the labels, [down a] is
    below [up a], and the known order is transitive and irreflexive
    ([order_of_trans], [order_of_irrefl]).  Those are the hypotheses of
    [HRefine.hn_eq_correct]. *)

From Stdlib Require Import Arith List Bool NArith PArith FMapPositive String Lia.
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
    + assert (E : inset s v = true) by (unfold inset, mem; rewrite F; reflexivity).
      split; [intros x Hx; exact Hx|split; [exact E|intros x w Hx Hn; rewrite Hx in Hn; discriminate]].
    + assert (E : inset s v = false) by (unfold inset, mem; rewrite F; reflexivity).
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
  apply (C u w IHp); [unfold inset, mem; rewrite PositiveMap.gempty; reflexivity|exact Hw].
Qed.

End Graph.

Lemma path_has adj a x : path adj a x -> exists st, PositiveMap.find (akey a) adj = Some st.
Proof.
  intros P; assert (Hf : exists w, In w (succs adj a)) by (induction P as [w Hw|u w _ IH _]; [exists w; exact Hw|exact IH]).
  destruct Hf as [w Hw]; unfold succs in Hw; destruct (PositiveMap.find (akey a) adj) as [st|]; [exists st; reflexivity|destruct Hw].
Qed.

(** ** The fields of [order_of l] *)

Section Known.

Variable l : list (lexp * lexp).

Let adj := edges l.
Let n := List.length (nodes adj).
Let rows := rows_of adj n.
Let d0 := bmap true (dups l).
Let dd := bmap false (ddowns l).
Let dm := bmap false (downs dd rows).

Let up a := oup (order_of l) (akey a).
Let down b := odown (order_of l) (akey b).

Lemma oup_eq a : up a = match PositiveMap.find (akey a) rows with Some row => upval d0 (akey a) row | None => None end.
Proof.
  unfold up, order_of; cbn [oup]; unfold tup; rewrite PositiveMap.gmapi, tab_of_find; unfold rows, d0, n, adj.
  destruct (PositiveMap.find (akey a) _); reflexivity.
Qed.

Lemma odown_eq b : down b = PositiveMap.find (akey b) dm.
Proof. reflexivity. Qed.

Lemma otab_eq a b : otab (order_of l) (akey a) (akey b) =
  match PositiveMap.find (akey a) rows with
  | Some row => mem (akey b) (extend (upval d0 (akey a) row) (PositiveMap.elements dm) row)
  | None => false
  end.
Proof.
  unfold order_of; cbn [otab]; unfold tmem; rewrite PositiveMap.gmapi, tab_of_find; unfold rows, d0, dm, dd, n, adj.
  destruct (PositiveMap.find (akey a) _); reflexivity.
Qed.

Lemma rows_akeyed : akeyed rows.
Proof. exact (proj1 (rows_keyed adj n (edges_keyed l))). Qed.

Lemma row_akeyed k row : PositiveMap.find k rows = Some row -> akeyed row.
Proof. exact (proj2 (rows_keyed adj n (edges_keyed l)) k row). Qed.

(** A row is exactly what is reachable. *)
Lemma row_iff a row : PositiveMap.find (akey a) rows = Some row -> forall x, inset row x = true <-> path adj a x.
Proof.
  unfold rows; rewrite rows_of_find; destruct (PositiveMap.find (akey a) adj); [|discriminate].
  intros E; injection E as <-; intros x; split; [apply reach_path|apply (reach_complete adj a n (le_n _))].
Qed.

Lemma path_row a x : path adj a x -> exists row, PositiveMap.find (akey a) rows = Some row /\ inset row x = true.
Proof.
  intros P; destruct (path_has adj a x P) as [st E].
  assert (Er : exists row, PositiveMap.find (akey a) rows = Some row) by (unfold rows; rewrite rows_of_find, E; eexists; reflexivity).
  destruct Er as [row Er]; exists row; split; [exact Er|apply (row_iff a row Er), P].
Qed.

Lemma otab_iff a b : otab (order_of l) (akey a) (akey b) = true <->
  path adj a b \/ exists u d, up a = Some u /\ down b = Some d /\ leb_lab u d = true.
Proof.
  rewrite otab_eq; split.
  - destruct (PositiveMap.find (akey a) rows) as [row|] eqn:Er; [|discriminate].
    intros H; apply extend_mem in H as [H|[u [d [Eu [Hd Hl]]]]]; [left; apply (row_iff a row Er), H|right].
    exists u, d; split; [rewrite oup_eq, Er; exact Eu|split; [apply PositiveMap.elements_complete, Hd|exact Hl]].
  - intros [P|[u [d [Eu [Ed Hl]]]]].
    + destruct (path_row a b P) as [row [Er Hr]]; rewrite Er; apply extend_mem; left; exact Hr.
    + rewrite oup_eq in Eu; destruct (PositiveMap.find (akey a) rows) as [row|]; [|discriminate].
      apply extend_mem; right; exists u, d; split; [exact Eu|split; [apply PositiveMap.elements_correct, Ed|exact Hl]].
Qed.

(** [up] and [down] only tighten along a path. *)
Lemma up_path a b mb : path adj a b -> up b = Some mb -> exists ma, up a = Some ma /\ leb_lab ma mb = true.
Proof.
  intros P Eb; rewrite oup_eq in Eb; destruct (PositiveMap.find (akey b) rows) as [rb|] eqn:Erb; [|discriminate].
  assert (Hx : exists x, PositiveMap.find (akey x) d0 = Some mb /\ path adj a x).
  { destruct (pick_fold_sound true _ _ _ Eb) as [E|E]; [exists b; split; [exact E|exact P]|].
    apply in_map_iff in E as [kt [E Hkt]]; exists (nkey (fst kt)); rewrite (elements_key rb kt (row_akeyed _ _ Erb) Hkt); split; [exact E|].
    apply (path_trans adj a b); [exact P|apply (row_iff b rb Erb), (elements_row rb kt (row_akeyed _ _ Erb) Hkt)]. }
  destruct Hx as [x [Ex Px]]; destruct (path_row a x Px) as [ra [Era Hx]].
  destruct (pick_fold_best true (map (fun kt => PositiveMap.find (fst kt) d0) (PositiveMap.elements ra)) (PositiveMap.find (akey a) d0) mb)
    as [ma [Ema Hma]].
  { right; apply in_map_iff; exists (akey x, tt); split; [exact Ex|apply row_elements, Hx]. }
  exists ma; split; [rewrite oup_eq, Era; exact Ema|exact Hma].
Qed.

Lemma down_path a b ma : path adj a b -> down a = Some ma -> exists mb, down b = Some mb /\ leb_lab ma mb = true.
Proof.
  intros P Ea; rewrite odown_eq in Ea; apply bmap_sound in Ea; unfold downs in Ea.
  (* an atom [x] with [ma] directly below it, at or below [a] *)
  assert (Hx : exists x, PositiveMap.find (akey x) dd = Some ma /\ path adj x b).
  { apply in_app_or in Ea as [H|H].
    - exists a; split; [apply PositiveMap.elements_complete, H|exact P].
    - apply in_flat_map in H as [[k row] [Hin H]]; apply PositiveMap.elements_complete in Hin.
      pose proof (rows_akeyed k row Hin) as Ek'; pose proof (row_akeyed k row Hin) as K.
      exists (nkey k); rewrite Ek'; destruct (PositiveMap.find k dd) as [c|] eqn:Ec; [|destruct H].
      apply in_map_iff in H as [kt [E Hkt]]; injection E as Ek <-; split; [reflexivity|].
      pose proof (elements_row row kt K Hkt) as Hr; rewrite Ek, nkey_akey in Hr.
      rewrite <- Ek' in Hin; exact (path_trans adj _ a b ((proj1 (row_iff _ row Hin a)) Hr) P). }
  destruct Hx as [x [Ex Px]]; destruct (path_row x b Px) as [row [Er Hb]].
  destruct (bmap_best false (downs dd rows) (akey b) ma) as [mb [Emb Hmb]]; [|exists mb; split; [exact Emb|exact Hmb]].
  unfold downs; apply in_or_app; right; apply in_flat_map; exists (akey x, row); split; [apply PositiveMap.elements_correct, Er|].
  rewrite Ex; apply in_map_iff; exists (akey b, tt); split; [reflexivity|apply row_elements, Hb].
Qed.

End Known.

Lemma lt_base_trans a b c : lt_base a b = true -> lt_base b c = true -> lt_base a c = true.
Proof.
  destruct a as [|s|i], b as [|t|j], c as [|u|k]; cbn; try discriminate; try reflexivity.
  apply is_less_than_label_transitive.
Qed.

(** ** The known order is a strict order *)

(** With facts that hold, an atom's [down] is below its [up]. *)
Lemma down_up l lenv : lfacts_ok lenv l -> forall b d u,
  odown (order_of l) (akey b) = Some d -> oup (order_of l) (akey b) = Some u -> label_lt d u.
Proof.
  intros Hl b d u Ed Eu; destruct (order_of_ok lenv l Hl) as [_ [_ [Hu Hd]]].
  exact (olabel_lt_trans _ _ _ (Hd b d Ed) (Hu b u Eu)).
Qed.

Lemma order_of_trans l lenv : lfacts_ok lenv l -> forall a b c,
  lt_known (order_of l) a b = true -> lt_known (order_of l) b c = true -> lt_known (order_of l) a c = true.
Proof.
  intros Hl a b c; set (F := order_of l).
  assert (DU := down_up l lenv Hl); fold F in DU.
  destruct a as [|s|i], b as [|t|j], c as [|r|k]; unfold lt_known; cbn [lt_base]; intros H1 H2;
    try discriminate; try reflexivity.
  - (* C C C *) exact (is_less_than_label_transitive _ _ _ H1 H2).
  - (* C C A *) destruct (odown F (akey k)) as [d|]; [|discriminate]; exact (lt_leb _ _ (lt_leb_trans _ _ _ H1 H2)).
  - (* C A C *) destruct (odown F (akey j)) as [d|] eqn:Ed; [|discriminate]; destruct (oup F (akey j)) as [u|] eqn:Eu; [|discriminate].
    exact (lt_leb_trans _ _ _ (leb_lt_trans _ _ _ H1 (DU j d u Ed Eu)) H2).
  - (* C A A *) destruct (odown F (akey j)) as [d|] eqn:Ed; [|discriminate].
    apply otab_iff in H2 as [P|[u [d' [Eu [Ed' Hl']]]]].
    + destruct (down_path l j k d P Ed) as [d' [Ed' Hd]]; fold F in Ed'; rewrite Ed'; exact (leb_lab_trans _ _ _ H1 Hd).
    + fold F in Eu, Ed'; rewrite Ed'; apply lt_leb, (lt_leb_trans _ _ _ (leb_lt_trans _ _ _ H1 (DU j d u Ed Eu)) Hl').
  - (* A C C *) destruct (oup F (akey i)) as [u|]; [|discriminate]; exact (lt_leb _ _ (leb_lt_trans _ _ _ H1 H2)).
  - (* A C A *) destruct (oup F (akey i)) as [u|] eqn:Eu; [|discriminate]; destruct (odown F (akey k)) as [d|] eqn:Ed; [|discriminate].
    apply otab_iff; right; exists u, d; split; [exact Eu|split; [exact Ed|exact (leb_lab_trans _ _ _ H1 H2)]].
  - (* A A C *) destruct (oup F (akey j)) as [u'|] eqn:Eu'; [|discriminate].
    apply otab_iff in H1 as [P|[u [d [Eu [Ed Hl']]]]].
    + destruct (up_path l i j u' P Eu') as [u [Eu Hu]]; fold F in Eu; rewrite Eu; exact (leb_lab_trans _ _ _ Hu H2).
    + fold F in Eu, Ed; rewrite Eu; apply lt_leb, (leb_lt_trans _ _ _ Hl' (lt_leb_trans _ _ _ (DU j d u' Ed Eu') H2)).
  - (* A A A *) apply otab_iff; apply otab_iff in H1, H2.
    destruct H1 as [P1|[u [d [Eu [Ed Hl1]]]]], H2 as [P2|[u' [d' [Eu' [Ed' Hl2]]]]].
    + left; exact (path_trans _ _ _ _ P1 P2).
    + right; destruct (up_path l i j u' P1 Eu') as [u [Eu Hu]]; exists u, d'; split; [exact Eu|split; [exact Ed'|exact (leb_lab_trans _ _ _ Hu Hl2)]].
    + right; destruct (down_path l j k d P2 Ed) as [d' [Ed' Hd]]; exists u, d'; split; [exact Eu|split; [exact Ed'|exact (leb_lab_trans _ _ _ Hl1 Hd)]].
    + right; exists u, d'; split; [exact Eu|split; [exact Ed'|]].
      fold F in Ed, Eu'; exact (lt_leb _ _ (leb_lt_trans _ _ _ Hl1 (lt_leb_trans _ _ _ (DU j d u' Ed Eu') Hl2))).
Qed.

Lemma order_of_irrefl l lenv : lfacts_ok lenv l -> forall a, lt_known (order_of l) a a = false.
Proof.
  intros Hl a; destruct (lt_known (order_of l) a a) eqn:E; [exfalso|reflexivity].
  exact (olabel_lt_irrefl _ (lt_known_sound lenv (order_of l) (order_of_ok lenv l Hl) a a E)).
Qed.
