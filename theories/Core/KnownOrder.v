(** * The known order built from facts is a strict order

    [Normalise.order_of] works out, for each label atom, the atoms the
    facts put above it, by a depth-first search over the edges they give.
    Here: the search finds exactly the nodes reachable from its start
    ([visit_complete], [reach_inv]), so the table is reachability
    ([otab_path], [path_otab]); with the chain of mentioned concrete
    labels, the known order is then transitive and irreflexive when the
    facts hold under some interpretation of the labels ([order_of_trans],
    [order_of_irrefl]).  Those are the hypotheses of
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

(** A set closed under the edges holds everything reachable from a node whose successors it holds. *)
Definition closed (s : PositiveMap.t unit) : Prop :=
  forall x w, inset s x = true -> In w (succs adj x) -> inset s w = true.

Lemma closed_path s a : closed s -> (forall w, In w (succs adj a) -> inset s w = true) -> forall v, path a v -> inset s v = true.
Proof. intros C W v P; induction P as [w Hw|u w _ IH Hw]; [apply W, Hw|apply (C u w IH Hw)]. Qed.

Lemma fold_closed n : List.length U <= n -> forall ws s, (forall w, In w ws -> In w U) -> closed s ->
  closed (fold_left (fun s w => visit adj n w s) ws s) /\ forall w, In w ws -> inset (fold_left (fun s w => visit adj n w s) ws s) w = true.
Proof.
  intros Hn ws s Hws Cs.
  assert (Hc : count s <= n) by (pose proof (count_le s); lia).
  destruct (fold_complete n (visit_complete n) ws s Hws Hc) as [S [W C]]; split; [|exact W].
  intros x w Hx Hw; destruct (inset s x) eqn:E; [apply S, (Cs x w E Hw)|apply (C x w Hx E Hw)].
Qed.

Lemma closed_empty : closed (PositiveMap.empty unit).
Proof. intros x w H; unfold inset in H; rewrite PositiveMap.gempty in H; discriminate. Qed.

(** The rows of [crows] are closed and hold their label's successors. *)
Lemma crows_complete n : List.length U <= n -> forall r k,
  closed (fst (crows adj n k r))
  /\ forall j, j < List.length r -> exists row, PositiveMap.find (akey (cnode (k + j))) (snd (crows adj n k r)) = Some row
       /\ closed row /\ forall w, In w (succs adj (cnode (k + j))) -> inset row w = true.
Proof.
  intros Hn; induction r as [|c r IH]; intros k; cbn [crows fst snd].
  - split; [exact closed_empty|intros j Hj; cbn in Hj; lia].
  - destruct (IH (S k)) as [Cr Ht]; destruct (crows adj n (S k) r) as [row t]; cbn [fst snd] in Cr, Ht |- *.
    destruct (fold_closed n Hn (succs adj (cnode k)) row (succs_nodes (cnode k)) Cr) as [C' W'].
    split; [exact C'|]; intros j Hj.
    destruct j as [|j]; [rewrite Nat.add_0_r, PositiveMap.gss; eexists; split; [reflexivity|split; [exact C'|exact W']]|].
    rewrite PositiveMap.gso; [|intros E; apply akey_inj, cnode_inj in E; lia].
    replace (k + S j) with (S k + j) by lia; apply Ht; cbn [List.length] in Hj; lia.
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
    match fnode (cmap 0 cs (PositiveMap.empty _)) x, fnode (cmap 0 cs (PositiveMap.empty _)) y with
    | Some u, Some v => addedge u v adj | _, _ => adj end) k0 a) x).
Proof.
  induction k0 as [|[x y] k0 IH]; intros a x0 w H; [exact H|]; cbn [fold_left]; apply IH.
  destruct (fnode (cmap 0 cs (PositiveMap.empty N)) x), (fnode (cmap 0 cs (PositiveMap.empty N)) y); try exact H; apply succs_addedge, H.
Qed.

Lemma cs_path k m : k < m -> m < List.length cs -> path adj (cnode k) (cnode m).
Proof.
  intros Hkm Hm; induction m as [|m IH]; [lia|].
  assert (E : In (cnode (S m)) (succs adj (cnode m))).
  { unfold adj, edges; apply facts_succs; pose proof (chain_edge cs 0 (PositiveMap.empty _) m Hm) as H; exact H. }
  destruct (Nat.eq_dec k m) as [->|Ne]; [exact (PStep adj _ _ E)|].
  apply (PNext adj _ (cnode m)); [apply IH; lia|exact E].
Qed.

Let ct := snd (crows adj n 0 cs).

Lemma otab_order_of u v : otab (order_of l) (akey u) (akey v) =
  match PositiveMap.find (akey u) adj with
  | Some _ =>
      match PositiveMap.find (akey u) ct with
      | Some row => inset row v
      | None => inset (fold_left (fun s w => visit adj n w s) (succs adj u) (PositiveMap.empty _)) v
      end
  | None => false
  end.
Proof.
  unfold order_of; cbn [otab]; unfold tmem; rewrite PositiveMap.gmapi; unfold option_map.
  fold cs adj n ct; destruct (PositiveMap.find (akey u) adj) as [st|] eqn:E; [|reflexivity].
  destruct (PositiveMap.find (akey u) ct); [reflexivity|]; unfold succs; rewrite E; reflexivity.
Qed.

(** The table is exactly reachability. *)
Lemma otab_path u v : otab (order_of l) (akey u) (akey v) = true -> path adj u v.
Proof.
  rewrite otab_order_of; destruct (PositiveMap.find (akey u) adj); [|discriminate].
  destruct (PositiveMap.find (akey u) ct) as [row|] eqn:Er; [|apply (reach_path adj u n v)].
  destruct (crows_inv (path adj) adj n (fun a x w Ha Hw => PNext adj a x w Ha Hw) (fun x w Hw => PStep adj x w Hw) cs 0)
    as [_ Ht].
  { intros j w Hj; cbn [Nat.add]; intros P; exact (path_trans adj _ _ _ (cs_path j (S j) (Nat.lt_succ_diag_r j) Hj) P). }
  destruct (Ht _ _ Er) as [k [_ [Ek Hv]]]; apply akey_inj in Ek; subst u; exact (Hv v).
Qed.

Lemma path_otab u v : path adj u v -> otab (order_of l) (akey u) (akey v) = true.
Proof.
  intros P; rewrite otab_order_of.
  destruct (PositiveMap.find (akey u) adj) eqn:E.
  - destruct (PositiveMap.find (akey u) ct) as [row|] eqn:Er; [|apply (reach_complete adj u n (le_n _)), P].
    destruct (crows_inv (fun _ _ => True) adj n (fun _ _ _ _ _ => I) (fun _ _ _ => I) cs 0 (fun _ _ _ _ => I)) as [_ Ht].
    destruct (Ht _ _ Er) as [k [Hk [Ek _]]]; apply akey_inj in Ek; subst u.
    destruct (proj2 (crows_complete adj n (le_n _) cs 0) k Hk) as [row' [Er' [C W]]].
    unfold ct in Er; rewrite Er' in Er; injection Er as <-; exact (closed_path adj row' _ C W v P).
  - exfalso; assert (Hf : exists w, In w (succs adj u)).
    { induction P as [w Hw|x w _ IH _]; [exists w; exact Hw|exact IH]. }
    destruct Hf as [w Hw]; unfold succs in Hw; rewrite E in Hw; destruct Hw.
Qed.

Lemma otab_trans u v w : otab (order_of l) (akey u) (akey v) = true -> otab (order_of l) (akey v) (akey w) = true -> otab (order_of l) (akey u) (akey w) = true.
Proof. intros H1 H2; apply path_otab, (path_trans adj u v w); apply otab_path; assumption. Qed.

Lemma cs_le k m : k <= m -> m < List.length cs -> cnode k = cnode m \/ otab (order_of l) (akey (cnode k)) (akey (cnode m)) = true.
Proof.
  intros H Hm; destruct (Nat.eq_dec k m) as [->|Ne]; [left; reflexivity|right].
  apply path_otab, cs_path; lia.
Qed.

(** The map and the tree find what the scans of the list find. *)
Lemma olo_con s : olo (order_of l) (LCon s) = option_map cnode (idx_lo s cs).
Proof. exact (proj1 (clo_chi_ok cs (fact_cons_sorted l) s)). Qed.

Lemma ohi_con s : ohi (order_of l) (LCon s) = option_map cnode (idx_hi s cs).
Proof. exact (proj2 (clo_chi_ok cs (fact_cons_sorted l) s)). Qed.

(** [ohi b] is at or below [olo b], along the order. *)
Lemma hi_lo b u v : ohi (order_of l) b = Some v -> olo (order_of l) b = Some u -> v = u \/ otab (order_of l) (akey v) (akey u) = true.
Proof.
  destruct b as [|s|j]; [discriminate| |cbn [ohi olo]; intros E1 E2; rewrite E1 in E2; injection E2 as ->; left; reflexivity].
  rewrite olo_con, ohi_con.
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
  rewrite !olo_con.
  intros Hst; destruct (idx_lo t cs) as [kt|] eqn:Et; [|discriminate]; cbn; intros E; injection E as <-.
  pose proof (idx_lo_len _ _ _ Et) as Lt.
  destruct (idx_lo_first s cs kt Lt (leb_lt_trans _ _ _ Hst (idx_lo_spec _ _ _ Et))) as [ks [Es Hk]].
  rewrite Es; exists (cnode ks); split; [reflexivity|apply cs_le; assumption].
Qed.

(** Going up to a greater concrete label keeps [ohi] at or above. *)
Lemma hi_up s t v : label_lt s t -> ohi (order_of l) (LCon s) = Some v ->
  exists v', ohi (order_of l) (LCon t) = Some v' /\ (v = v' \/ otab (order_of l) (akey v) (akey v') = true).
Proof.
  rewrite !ohi_con.
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

Lemma gen_trans l a b c :
  lt_gen (order_of l) a b = true -> lt_gen (order_of l) b c = true -> lt_gen (order_of l) a c = true.
Proof.
  set (F := order_of l); unfold lt_gen.
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

(** Unless both are concrete, [lt_known] is [lt_gen]. *)
Lemma lt_known_eq_gen F a b : (forall s t, a = LCon s -> b = LCon t -> False) -> lt_known F a b = lt_gen F a b.
Proof.
  intros N; destruct a as [|s|i], b as [|t|j]; try reflexivity; [exfalso; exact (N s t eq_refl eq_refl)|].
  unfold lt_known, lt_gen; cbn; rewrite !atom_key_akey; reflexivity.
Qed.

(** Transitive, given facts that hold: two concrete labels are compared by
    the fixed order, which a path between them through other labels agrees
    with when the facts hold. *)
Lemma order_of_trans l lenv : lfacts_ok lenv l -> forall a b c,
  lt_known (order_of l) a b = true -> lt_known (order_of l) b c = true -> lt_known (order_of l) a c = true.
Proof.
  intros Hl a b c H1 H2; apply lt_known_gen in H1, H2; pose proof (gen_trans l a b c H1 H2) as H.
  destruct a as [|s|i], c as [|u|k]; try (rewrite lt_known_eq_gen; [exact H|intros ? ? E1 E2; discriminate]).
  exact (lt_gen_sound lenv (order_of l) (order_of_ok lenv l Hl) _ _ H).
Qed.

Lemma order_of_irrefl l lenv : lfacts_ok lenv l -> forall a, lt_known (order_of l) a a = false.
Proof.
  intros Hl a; destruct (lt_known (order_of l) a a) eqn:E; [exfalso|reflexivity].
  exact (olabel_lt_irrefl _ (lt_known_sound lenv (order_of l) (order_of_ok lenv l Hl) a a E)).
Qed.
