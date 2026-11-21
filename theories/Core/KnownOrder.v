(** * The known order built from facts is a strict order

    [Normalise.order_of] works out, for each label atom, the atoms the
    facts put above it, by a depth-first search over the edges they give.
    Here: the search finds exactly the nodes reachable from its start
    ([visit_complete], [reach_inv]), so the table is reachability
    ([otab_path], [path_otab]); with the chain of mentioned concrete
    labels, the known order is then transitive ([order_of_trans]), and it
    is irreflexive when the facts hold under some interpretation of the
    labels ([order_of_irrefl]).  Those are the hypotheses of
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

(** Edges only grow. *)
Lemma succs_addedge adj u v x w : In w (succs adj x) -> In w (succs (addedge u v adj) x).
Proof. intros H; rewrite succs_add; destruct (N.eqb_spec x u) as [->|_]; [right; exact H|exact H]. Qed.

(** ** The table of [order_of l] *)

Section Known.

Variable l : list (lexp * lexp).

Let cs := fact_cons l.
Let adj := edges l cs.
Let n := List.length (nodes adj).

Lemma otab_order_of u v : otab (order_of l) (akey u) (akey v) =
  match PositiveMap.find (akey u) adj with
  | Some _ => inset (fold_left (fun s w => visit adj n w s) (succs adj u) (PositiveMap.empty _)) v
  | None => false
  end.
Proof.
  unfold order_of; cbn [otab]; unfold tmem; rewrite PositiveMap.gmapi; unfold option_map.
  fold cs adj n; destruct (PositiveMap.find (akey u) adj) as [st|] eqn:E; [|reflexivity].
  unfold succs; rewrite E; reflexivity.
Qed.

(** The table is exactly reachability. *)
Lemma otab_path u v : otab (order_of l) (akey u) (akey v) = true -> path adj u v.
Proof.
  rewrite otab_order_of; destruct (PositiveMap.find (akey u) adj); [|discriminate].
  apply (reach_path adj u n v).
Qed.

Lemma path_otab u v : path adj u v -> otab (order_of l) (akey u) (akey v) = true.
Proof.
  intros P; rewrite otab_order_of.
  destruct (PositiveMap.find (akey u) adj) eqn:E; [apply (reach_complete adj u n (le_n _)), P|].
  exfalso; assert (Hf : exists w, In w (succs adj u)).
  { induction P as [w Hw|x w _ IH _]; [exists w; exact Hw|exact IH]. }
  destruct Hf as [w Hw]; unfold succs in Hw; rewrite E in Hw; destruct Hw.
Qed.

Lemma otab_trans u v w : otab (order_of l) (akey u) (akey v) = true -> otab (order_of l) (akey v) (akey w) = true -> otab (order_of l) (akey u) (akey w) = true.
Proof. intros H1 H2; apply path_otab, (path_trans adj u v w); apply otab_path; assumption. Qed.

(** *** The concrete labels *)

Lemma chain_cons k c d r a : chain k (c :: d :: r) a = chain (S k) (d :: r) (addedge (cnode k) (cnode (S k)) a).
Proof. reflexivity. Qed.

Lemma chain_succs : forall r k a x w, In w (succs a x) -> In w (succs (chain k r a) x).
Proof.
  induction r as [|c r IH]; intros k a x w H; [exact H|]; destruct r as [|d r']; [exact H|].
  rewrite chain_cons; apply IH, succs_addedge, H.
Qed.

Lemma chain_edge : forall r k a i, S i < List.length r -> In (cnode (k + S i)) (succs (chain k r a) (cnode (k + i))).
Proof.
  induction r as [|c r IH]; intros k a i Hi; cbn [List.length] in Hi; [lia|].
  destruct r as [|d r']; cbn [List.length] in Hi; [lia|]; rewrite chain_cons.
  destruct i as [|i].
  - apply chain_succs; rewrite succs_add, Nat.add_0_r, N.eqb_refl, Nat.add_1_r; left; reflexivity.
  - replace (k + S (S i)) with (S k + S i) by lia; replace (k + S i) with (S k + i) by lia.
    apply IH; cbn [List.length]; lia.
Qed.

Lemma facts_succs k0 : forall a x w, In w (succs a x) ->
  In w (succs (fold_left (fun adj '(x, y) =>
    match fnode cs x, fnode cs y with Some u, Some v => addedge u v adj | _, _ => adj end) k0 a) x).
Proof.
  induction k0 as [|[x y] k0 IH]; intros a x0 w H; [exact H|]; cbn [fold_left]; apply IH.
  destruct (fnode cs x), (fnode cs y); try exact H; apply succs_addedge, H.
Qed.

Lemma cs_path k m : k < m -> m < List.length cs -> path adj (cnode k) (cnode m).
Proof.
  intros Hkm Hm; induction m as [|m IH]; [lia|].
  assert (E : In (cnode (S m)) (succs adj (cnode m))).
  { unfold adj, edges; apply facts_succs; pose proof (chain_edge cs 0 (PositiveMap.empty _) m Hm) as H; exact H. }
  destruct (Nat.eq_dec k m) as [->|Ne]; [exact (PStep adj _ _ E)|].
  apply (PNext adj _ (cnode m)); [apply IH; lia|exact E].
Qed.

Lemma cs_le k m : k <= m -> m < List.length cs -> cnode k = cnode m \/ otab (order_of l) (akey (cnode k)) (akey (cnode m)) = true.
Proof.
  intros H Hm; destruct (Nat.eq_dec k m) as [->|Ne]; [left; reflexivity|right].
  apply path_otab, cs_path; lia.
Qed.

Lemma sorted_nth : forall r, sorted_lab r -> forall i j, i < j -> j < List.length r ->
  label_lt (nth i r EmptyString) (nth j r EmptyString).
Proof.
  induction r as [|a r IH]; intros Hs i j Hij Hj; cbn [List.length] in Hj; [lia|].
  destruct r as [|b r']; cbn [List.length] in Hj; [lia|]; destruct Hs as [Hab Hs].
  destruct i as [|i]; destruct j as [|j]; try lia; cbn [nth].
  - destruct j as [|j]; [exact Hab|]; apply (label_lt_trans _ b); [exact Hab|].
    apply (IH Hs 0 (S j)); cbn [List.length]; lia.
  - apply (IH Hs i j); cbn [List.length]; lia.
Qed.

Lemma leb_lab_iff s t : leb_lab s t = true <-> s = t \/ label_lt s t.
Proof.
  unfold leb_lab; destruct (String.eqb_spec s t) as [->|Ne]; [split; [left; reflexivity|reflexivity]|].
  split; [intros H; right; exact H|intros [E|H]; [contradiction|exact H]].
Qed.

Lemma leb_lt_trans a b c : label_lt a b -> leb_lab b c = true -> leb_lab a c = true.
Proof. intros H1 H2; apply leb_lab_iff in H2 as [<-|H2]; apply leb_lab_iff; right; [exact H1|exact (label_lt_trans _ _ _ H1 H2)]. Qed.

Lemma leb_lt_trans' a b c : leb_lab a b = true -> label_lt b c -> leb_lab a c = true.
Proof. intros H1 H2; apply leb_lab_iff in H1 as [->|H1]; apply leb_lab_iff; right; [exact H2|exact (label_lt_trans _ _ _ H1 H2)]. Qed.

Lemma idx_lo_len s r k : idx_lo s r = Some k -> k < List.length r.
Proof.
  revert k; induction r as [|c r IH]; intros k; cbn [idx_lo]; [discriminate|].
  destruct (leb_lab s c); [intros E; injection E as <-; cbn; lia|].
  destruct (idx_lo s r) as [k'|]; [cbn; intros E; injection E as <-; cbn [List.length]; specialize (IH k' eq_refl); lia|discriminate].
Qed.

Lemma idx_lo_first s r j : j < List.length r -> leb_lab s (nth j r EmptyString) = true ->
  exists k, idx_lo s r = Some k /\ k <= j.
Proof.
  revert j; induction r as [|c r IH]; intros j Hj H; cbn [List.length] in Hj; [lia|]; cbn [idx_lo].
  destruct (leb_lab s c) eqn:L; [exists 0; split; [reflexivity|lia]|].
  destruct j as [|j]; [cbn in H; congruence|].
  destruct (IH j ltac:(lia) H) as [k [E Hk]]; rewrite E; exists (S k); split; [reflexivity|lia].
Qed.

Lemma idx_hi_len s r k : idx_hi s r = Some k -> k < List.length r.
Proof.
  revert k; induction r as [|c r IH]; intros k; cbn [idx_hi]; [discriminate|].
  destruct (idx_hi s r) as [k'|]; [intros E; injection E as <-; cbn [List.length]; specialize (IH k' eq_refl); lia|].
  destruct (leb_lab c s); [intros E; injection E as <-; cbn; lia|discriminate].
Qed.

Lemma idx_hi_last s r j : j < List.length r -> leb_lab (nth j r EmptyString) s = true ->
  exists k, idx_hi s r = Some k /\ j <= k.
Proof.
  revert j; induction r as [|c r IH]; intros j Hj H; cbn [List.length] in Hj; [lia|]; cbn [idx_hi].
  destruct j as [|j].
  - cbn in H; destruct (idx_hi s r) as [k|]; [exists (S k); split; [reflexivity|lia]|rewrite H; exists 0; split; [reflexivity|lia]].
  - destruct (IH j ltac:(lia) H) as [k [E Hk]]; rewrite E; exists (S k); split; [reflexivity|lia].
Qed.

(** [ohi b] is at or below [olo b], along the order. *)
Lemma hi_lo b u v : ohi (order_of l) b = Some v -> olo (order_of l) b = Some u -> v = u \/ otab (order_of l) (akey v) (akey u) = true.
Proof.
  destruct b as [|s|j]; cbn [ohi olo]; [discriminate| |intros E1 E2; rewrite E1 in E2; injection E2 as ->; left; reflexivity].
  unfold order_of at 1 2; cbn [ocs]; fold cs.
  destruct (idx_hi s cs) as [kh|] eqn:Eh; [|discriminate]; destruct (idx_lo s cs) as [kl|] eqn:El; [|discriminate].
  cbn; intros E1 E2; injection E1 as <-; injection E2 as <-.
  apply cs_le; [|apply (idx_lo_len _ _ _ El)].
  destruct (Nat.le_gt_cases kh kl) as [Le|Gt]; [exact Le|exfalso].
  pose proof (idx_hi_spec _ _ _ Eh) as H1; pose proof (idx_lo_spec _ _ _ El) as H2.
  pose proof (sorted_nth cs (fact_cons_sorted l) kl kh Gt (idx_hi_len _ _ _ Eh)) as H3.
  assert (H4 : label_lt s (nth kh cs EmptyString))
    by (apply leb_lab_iff in H2 as [E|H2]; [rewrite E; exact H3|exact (label_lt_trans _ _ _ H2 H3)]).
  apply leb_lab_iff in H1 as [E|H1].
  - rewrite E in H4; exact (label_lt_irrefl _ H4).
  - exact (label_lt_irrefl _ (label_lt_trans _ _ _ H4 H1)).
Qed.

(** Going down to a smaller concrete label keeps [olo] at or below. *)
Lemma lo_down s t u : label_lt s t -> olo (order_of l) (LCon t) = Some u ->
  exists u', olo (order_of l) (LCon s) = Some u' /\ (u' = u \/ otab (order_of l) (akey u') (akey u) = true).
Proof.
  cbn [olo]; unfold order_of at 1 2; cbn [ocs]; fold cs.
  intros Hst; destruct (idx_lo t cs) as [kt|] eqn:Et; [|discriminate]; cbn; intros E; injection E as <-.
  pose proof (idx_lo_len _ _ _ Et) as Lt.
  destruct (idx_lo_first s cs kt Lt (leb_lt_trans _ _ _ Hst (idx_lo_spec _ _ _ Et))) as [ks [Es Hk]].
  rewrite Es; exists (cnode ks); split; [reflexivity|apply cs_le; assumption].
Qed.

(** Going up to a greater concrete label keeps [ohi] at or above. *)
Lemma hi_up s t v : label_lt s t -> ohi (order_of l) (LCon s) = Some v ->
  exists v', ohi (order_of l) (LCon t) = Some v' /\ (v = v' \/ otab (order_of l) (akey v) (akey v') = true).
Proof.
  cbn [ohi]; unfold order_of at 1 2; cbn [ocs]; fold cs.
  intros Hst; destruct (idx_hi s cs) as [ks|] eqn:Es; [|discriminate]; cbn; intros E; injection E as <-.
  pose proof (idx_hi_len _ _ _ Es) as Ls.
  destruct (idx_hi_last t cs ks Ls (leb_lt_trans' _ _ _ (idx_hi_spec _ _ _ Es) Hst)) as [kt [Et Hk]].
  rewrite Et; exists (cnode kt); split; [reflexivity|apply cs_le; [exact Hk|apply (idx_hi_len _ _ _ Et)]].
Qed.

End Known.

Lemma lt_base_trans a b c : lt_base a b = true -> lt_base b c = true -> lt_base a c = true.
Proof.
  destruct a as [|s|i], b as [|t|j], c as [|u|k]; cbn; try discriminate; try reflexivity.
  apply is_less_than_label_transitive.
Qed.

(** ** The known order is a strict order *)

Lemma order_of_trans l a b c :
  lt_known (order_of l) a b = true -> lt_known (order_of l) b c = true -> lt_known (order_of l) a c = true.
Proof.
  set (F := order_of l); rewrite !lt_known_gen; unfold lt_gen.
  destruct (lt_base a b) eqn:B1, (lt_base b c) eqn:B2; intros H1 H2.
  - rewrite (lt_base_trans a b c B1 B2); reflexivity.
  - destruct (olo F b) as [u2|] eqn:Eu2; [|discriminate]; destruct (ohi F c) as [v2|] eqn:Ev2; [|discriminate].
    destruct (lt_base a c); [reflexivity|].
    destruct a as [|s|i], b as [|t|j]; cbn [lt_base] in B1; try discriminate B1; cbn [olo] in Eu2; try discriminate Eu2.
    destruct (lo_down l s t u2 B1 Eu2) as [u' [Eu' [<-|R]]]; fold F in Eu'; rewrite Eu'; [exact H2|].
    exact (otab_trans l _ _ _ R H2).
  - destruct (olo F a) as [u1|] eqn:Eu1; [|discriminate]; destruct (ohi F b) as [v1|] eqn:Ev1; [|discriminate].
    destruct (lt_base a c) eqn:B3; [reflexivity|].
    destruct b as [|t|j], c as [|u|k]; cbn [lt_base] in B2; try discriminate B2;
      try (destruct a as [|s|i]; cbn [lt_base olo] in B3, Eu1; discriminate).
    destruct (hi_up l t u v1 B2 Ev1) as [v' [Ev' [<-|R]]]; fold F in Ev'; rewrite Ev'; [exact H1|].
    exact (otab_trans l _ _ _ H1 R).
  - destruct (olo F a) as [u1|] eqn:Eu1; [|discriminate]; destruct (ohi F b) as [v1|] eqn:Ev1; [|discriminate].
    destruct (olo F b) as [u2|] eqn:Eu2; [|discriminate]; destruct (ohi F c) as [v2|] eqn:Ev2; [|discriminate].
    destruct (lt_base a c); [reflexivity|].
    destruct (hi_lo l b u2 v1 Ev1 Eu2) as [<-|R]; [exact (otab_trans l _ _ _ H1 H2)|].
    exact (otab_trans l _ _ _ (otab_trans l _ _ _ H1 R) H2).
Qed.

Lemma order_of_irrefl l lenv : lfacts_ok lenv l -> forall a, lt_known (order_of l) a a = false.
Proof.
  intros Hl a; destruct (lt_known (order_of l) a a) eqn:E; [exfalso|reflexivity].
  exact (olabel_lt_irrefl _ (lt_known_sound lenv (order_of l) (order_of_ok lenv l Hl) a a E)).
Qed.
