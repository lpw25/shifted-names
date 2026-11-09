(** * Skew sequences with weakening counts

    Sequences that grow at the front, as in Okasaki's skew-binary
    random-access lists: a spine of cells, each holding a complete binary
    ktree whose size is [2ᵏ⁺¹ − 1], with an element at every ktree node.
    [kcons] is O(1) (it builds at most one node from the two front trees),
    and indexing is O(log n).

    Every ktree node and spine cell carries a count map: how far the uses of
    everything below it start above its parent's base (Counts.v).  Elements
    are stored relative to the base of the node that holds them.  The
    sequence is generic in its elements, which only need to say what they
    use and how to move between bases.

    Canonicity: [kcons] is the only way to build a sequence, so a sequence
    built by [kcons] (one that satisfies [kcanon]) is determined by the list
    it denotes. *)

From Stdlib Require Import PArith Arith Lia List Bool.
From ShiftedNames.Core Require Import Trie Counts Based.
Import ListNotations.

Section Skew.

Context {X : Type} {BX : Based X} {LX : BasedLaws X}.

(** ** Representation *)

Inductive ktree : Type :=
| KLeaf (x : X)
| KNode (a : counts) (x : X) (l r : ktree).

Inductive kseq : Type :=
| KNil
| KCons (a : counts) (w : nat) (t : ktree) (s : kseq).

Definition ktann (t : ktree) : counts :=
  match t with KLeaf x => uses x | KNode a _ _ _ => a end.

Definition ksann (s : kseq) : counts :=
  match s with KNil => cnone | KCons a _ _ _ => a end.

(** The elements denoted, relative to the parent's base (trees in
    preorder, so every subtree is a contiguous range). *)
Fixpoint ktlist (t : ktree) : list X :=
  match t with
  | KLeaf x => [x]
  | KNode a x l r => map (unshift a) (x :: ktlist l ++ ktlist r)
  end.

Fixpoint klist (s : kseq) : list X :=
  match s with
  | KNil => []
  | KCons a _ t s' => map (unshift a) (ktlist t ++ klist s')
  end.

(** Moving a whole ktree or sequence to a base [d] higher or lower: only the
    top changes. *)
Definition ktrebase (d : counts) (t : ktree) : ktree :=
  match t with KLeaf x => KLeaf (shift d x) | KNode a x l r => KNode (csub a d) x l r end.

Definition ktlift (d : counts) (t : ktree) : ktree :=
  match t with KLeaf x => KLeaf (unshift d x) | KNode a x l r => KNode (cadd d a) x l r end.

Definition krebase (d : counts) (s : kseq) : kseq :=
  match s with KNil => KNil | KCons a w t s' => KCons (csub a d) w t s' end.

Definition klift (d : counts) (s : kseq) : kseq :=
  match s with KNil => KNil | KCons a w t s' => KCons (cadd d a) w t s' end.

(** Building a node: its counts are the minimum of what is below. *)
Definition ktnode (x : X) (t1 t2 : ktree) : ktree :=
  let m := cmin (uses x) (cmin (ktann t1) (ktann t2)) in
  KNode m (shift m x) (ktrebase m t1) (ktrebase m t2).

Definition kcell (w : nat) (t : ktree) (s : kseq) : kseq :=
  let m := cmin (ktann t) (ksann s) in
  KCons m w (ktrebase m t) (krebase m s).

Definition kcons (x : X) (s : kseq) : kseq :=
  match s with
  | KCons a1 w1 t1 (KCons a2 w2 t2 s') =>
      if Nat.eqb w1 w2
      then kcell (S (w1 + w2)) (ktnode x (ktlift a1 t1) (ktlift a1 (ktlift a2 t2)))
                 (klift a1 (klift a2 s'))
      else kcell 1 (KLeaf x) s
  | _ => kcell 1 (KLeaf x) s
  end.

Definition kof_list (l : list X) : kseq := fold_right kcons KNil l.

(** Indexing; [w] is the size of the ktree. *)
Fixpoint ktnth (w : nat) (t : ktree) (i : nat) : option X :=
  match t with
  | KLeaf x => match i with 0 => Some x | S _ => None end
  | KNode a x l r =>
      let w' := Nat.div2 w in
      match i with
      | 0 => Some (unshift a x)
      | S j => option_map (unshift a) (if Nat.ltb j w' then ktnth w' l j else ktnth w' r (j - w'))
      end
  end.

Fixpoint knth (s : kseq) (i : nat) : option X :=
  match s with
  | KNil => None
  | KCons a w t s' => option_map (unshift a) (if Nat.ltb i w then ktnth w t i else knth s' (i - w))
  end.

Fixpoint klength (s : kseq) : nat :=
  match s with KNil => 0 | KCons _ w _ s' => w + klength s' end.

(** ** Invariants *)

(** Every node's counts are the minimum over what it denotes, and stored
    elements are well formed. *)
Fixpoint ktinv (t : ktree) : Prop :=
  (forall k, cget (ktann t) k = lmin (ktlist t) k)
  /\ match t with
     | KLeaf x => eok x
     | KNode _ x l r => eok x /\ ktinv l /\ ktinv r
     end.

Fixpoint kinv (s : kseq) : Prop :=
  (forall k, cget (ksann s) k = lmin (klist s) k)
  /\ match s with
     | KNil => True
     | KCons _ _ t s' => ktinv t /\ kinv s'
     end.

(** Sizes: a ktree of size [w] has children of size [div2 w]. *)
Fixpoint ktshape (w : nat) (t : ktree) : Prop :=
  match t with
  | KLeaf _ => w = 1
  | KNode _ _ l r => exists w', w = S (w' + w') /\ ktshape w' l /\ ktshape w' r
  end.

Fixpoint kshape (s : kseq) : Prop :=
  match s with
  | KNil => True
  | KCons _ w t s' => ktshape w t /\ kshape s'
  end.

(** Built by [kcons]. *)
Definition kcanon (s : kseq) : Prop := s = kof_list (klist s).

(** ** Trees *)

Lemma ktinv_ann t : ktinv t -> forall k, cget (ktann t) k = lmin (ktlist t) k.
Proof. destruct t; cbn [ktinv]; tauto. Qed.

Lemma ktinv_ok t : ktinv t -> forall e, In e (ktlist t) -> eok e.
Proof.
  induction t as [x|a x l IHl r IHr]; cbn [ktinv ktlist].
  - intros [_ H] e [<-|[]]; exact H.
  - intros [_ [Hx [Hl Hr]]] e Hin; apply in_map_iff in Hin as [e' [<- Hin]].
    apply ok_unshift; destruct Hin as [<-|Hin]; [exact Hx|].
    apply in_app_or in Hin as [Hin|Hin]; [apply IHl|apply IHr]; assumption.
Qed.



(** ** Trees *)

Lemma ktinv_node_ok a x l r :
  ktinv (KNode a x l r) -> forall e, In e (x :: ktlist l ++ ktlist r) -> eok e.
Proof.
  intros [_ [Hx [Hl Hr]]] e [<-|Hin]; [exact Hx|].
  apply in_app_or in Hin as [Hin|Hin]; [apply (ktinv_ok l Hl)|apply (ktinv_ok r Hr)]; exact Hin.
Qed.

Lemma ktlist_ktrebase m t : ktinv t -> cle m (ktann t) -> ktlist (ktrebase m t) = map (shift m) (ktlist t).
Proof.
  destruct t as [x|a x l r]; intros Ht Hm; [reflexivity|].
  apply (rebase_list a); [apply (ktinv_ann _ Ht)|apply (ktinv_node_ok _ _ _ _ Ht)|exact Hm].
Qed.

Lemma ktinv_ktrebase m t : ktinv t -> cle m (ktann t) -> ktinv (ktrebase m t).
Proof.
  intros Ht Hm; pose proof (ktlist_ktrebase m t Ht Hm) as Hl.
  destruct t as [x|a x l r]; cbn [ktrebase ktinv ktann] in *.
  - destruct Ht as [_ Hx]; split; [intro k; cbn [ktlist]; rewrite lmin_single; reflexivity|apply ok_shift, Hx].
  - destruct Ht as [Ha Hs]; split; [|exact Hs]; intro k.
    rewrite Hl, lmin_shift, cget_csub, Ha; reflexivity.
Qed.

Lemma ktlist_ktlift d t : ktinv t -> ktlist (ktlift d t) = map (unshift d) (ktlist t).
Proof.
  destruct t as [x|a x l r]; intros Ht; [reflexivity|].
  apply (lift_list a), (ktinv_ann _ Ht).
Qed.

Lemma ktinv_ktlift d t : ktinv t -> ktinv (ktlift d t).
Proof.
  intros Ht; pose proof (ktlist_ktlift d t Ht) as Hl.
  destruct t as [x|a x l r]; cbn [ktlift ktinv ktann] in *.
  - destruct Ht as [_ Hx]; split; [intro k; cbn [ktlist]; rewrite lmin_single; reflexivity|apply ok_unshift, Hx].
  - destruct Ht as [Ha Hs]; split; [|exact Hs]; intro k.
    rewrite Hl, lmin_unshift, cget_cadd, Ha; reflexivity.
Qed.

Lemma ktlist_ktnode x t1 t2 :
  eok x -> ktinv t1 -> ktinv t2 -> ktlist (ktnode x t1 t2) = x :: ktlist t1 ++ ktlist t2.
Proof.
  intros Hx H1 H2; unfold ktnode; set (m := cmin (uses x) (cmin (ktann t1) (ktann t2))).
  cbn [ktlist]; rewrite !ktlist_ktrebase by (assumption || apply cle_min3_2 || apply cle_min3_3).
  cbn [map]; rewrite map_app, !map_map.
  f_equal; [apply unshift_shift; [exact Hx|apply cle_min3_1]|f_equal; apply map_id_in].
  - intros e Hin; apply unshift_shift; [apply (ktinv_ok _ H1 _ Hin)|].
    apply (cle_mem m (ktann t1) (ktlist t1)); [apply cle_min3_2|apply ktinv_ann, H1|exact Hin].
  - intros e Hin; apply unshift_shift; [apply (ktinv_ok _ H2 _ Hin)|].
    apply (cle_mem m (ktann t2) (ktlist t2)); [apply cle_min3_3|apply ktinv_ann, H2|exact Hin].
Qed.

Lemma ktinv_ktnode x t1 t2 : eok x -> ktinv t1 -> ktinv t2 -> ktinv (ktnode x t1 t2).
Proof.
  intros Hx H1 H2; pose proof (ktlist_ktnode x t1 t2 Hx H1 H2) as Hl.
  unfold ktnode in *; set (m := cmin (uses x) (cmin (ktann t1) (ktann t2))) in *.
  cbn [ktinv ktann]; split; [|split; [apply ok_shift, Hx|split; apply ktinv_ktrebase]];
    try assumption; try apply cle_min3_2; try apply cle_min3_3.
  intro k; rewrite Hl; cbn [lmin fold_right]; fold (lmin (ktlist t1 ++ ktlist t2) k).
  rewrite lmin_app, <- !ktinv_ann by assumption; unfold m; rewrite !cget_cmin; reflexivity.
Qed.

(** ** Sequences *)

Lemma kinv_ann s : kinv s -> forall k, cget (ksann s) k = lmin (klist s) k.
Proof. destruct s; cbn [kinv]; tauto. Qed.

Lemma kinv_ok s : kinv s -> forall e, In e (klist s) -> eok e.
Proof.
  induction s as [|a w t s IH]; cbn [kinv klist]; [intros _ _ []|].
  intros [_ [Ht Hs]] e Hin; apply in_map_iff in Hin as [e' [<- Hin]]; apply ok_unshift.
  apply in_app_or in Hin as [Hin|Hin]; [apply (ktinv_ok t Ht)|apply IH]; assumption.
Qed.

Lemma kinv_cell_ok a w t s :
  kinv (KCons a w t s) -> forall e, In e (ktlist t ++ klist s) -> eok e.
Proof.
  intros [_ [Ht Hs]] e Hin.
  apply in_app_or in Hin as [Hin|Hin]; [apply (ktinv_ok t Ht)|apply (kinv_ok s Hs)]; exact Hin.
Qed.

Lemma klist_krebase m s : kinv s -> cle m (ksann s) -> klist (krebase m s) = map (shift m) (klist s).
Proof.
  destruct s as [|a w t s]; intros Hs Hm; [reflexivity|].
  apply (rebase_list a); [apply (kinv_ann _ Hs)|apply (kinv_cell_ok _ _ _ _ Hs)|exact Hm].
Qed.

Lemma kinv_krebase m s : kinv s -> cle m (ksann s) -> kinv (krebase m s).
Proof.
  intros Hs Hm; pose proof (klist_krebase m s Hs Hm) as Hl.
  destruct s as [|a w t s]; [exact Hs|]; cbn [krebase kinv ksann] in *.
  destruct Hs as [Ha Hs]; split; [|exact Hs]; intro k.
  rewrite Hl, lmin_shift, cget_csub, Ha; reflexivity.
Qed.

Lemma klist_klift d s : kinv s -> klist (klift d s) = map (unshift d) (klist s).
Proof.
  destruct s as [|a w t s]; intros Hs; [reflexivity|].
  apply (lift_list a), (kinv_ann _ Hs).
Qed.

Lemma kinv_klift d s : kinv s -> kinv (klift d s).
Proof.
  intros Hs; pose proof (klist_klift d s Hs) as Hl.
  destruct s as [|a w t s]; [exact Hs|]; cbn [klift kinv ksann] in *.
  destruct Hs as [Ha Hs]; split; [|exact Hs]; intro k.
  rewrite Hl, lmin_unshift, cget_cadd, Ha; reflexivity.
Qed.

Lemma klist_kcell w t s : ktinv t -> kinv s -> klist (kcell w t s) = ktlist t ++ klist s.
Proof.
  intros Ht Hs; unfold kcell; set (m := cmin (ktann t) (ksann s)); cbn [klist].
  rewrite ktlist_ktrebase, klist_krebase by (assumption || apply cle_cmin_l || apply cle_cmin_r).
  rewrite map_app, !map_map; f_equal; apply map_id_in.
  - intros e Hin; apply unshift_shift; [apply (ktinv_ok _ Ht _ Hin)|].
    apply (cle_mem m (ktann t) (ktlist t)); [apply cle_cmin_l|apply ktinv_ann, Ht|exact Hin].
  - intros e Hin; apply unshift_shift; [apply (kinv_ok _ Hs _ Hin)|].
    apply (cle_mem m (ksann s) (klist s)); [apply cle_cmin_r|apply kinv_ann, Hs|exact Hin].
Qed.

Lemma kinv_kcell w t s : ktinv t -> kinv s -> kinv (kcell w t s).
Proof.
  intros Ht Hs; pose proof (klist_kcell w t s Ht Hs) as Hl.
  unfold kcell in *; set (m := cmin (ktann t) (ksann s)) in *.
  cbn [kinv ksann]; split; [|split; [apply ktinv_ktrebase|apply kinv_krebase]];
    try assumption; try apply cle_cmin_l; try apply cle_cmin_r.
  intro k; rewrite Hl, lmin_app, <- ktinv_ann, <- kinv_ann by assumption.
  unfold m; rewrite cget_cmin; reflexivity.
Qed.

(** ** [kcons] *)

Theorem kcons_spec x s : eok x -> kinv s -> klist (kcons x s) = x :: klist s /\ kinv (kcons x s).
Proof.
  intros Hx Hs.
  assert (Hleaf : ktinv (KLeaf x)) by (split; [intro k; cbn [ktlist]; rewrite lmin_single; reflexivity|exact Hx]).
  assert (Hdef : klist (kcell 1 (KLeaf x) s) = x :: klist s /\ kinv (kcell 1 (KLeaf x) s))
    by (split; [rewrite klist_kcell by assumption; reflexivity|apply kinv_kcell; assumption]).
  destruct s as [|a1 w1 t1 [|a2 w2 t2 s']]; cbn [kcons]; try exact Hdef.
  destruct (Nat.eqb w1 w2); [|exact Hdef].
  destruct Hs as [Ha1 [Ht1 [Ha2 [Ht2 Hs']]]].
  assert (T1 : ktinv (ktlift a1 t1)) by (apply ktinv_ktlift, Ht1).
  assert (T2 : ktinv (ktlift a1 (ktlift a2 t2))) by (apply ktinv_ktlift, ktinv_ktlift, Ht2).
  assert (S' : kinv (klift a1 (klift a2 s'))) by (apply kinv_klift, kinv_klift, Hs').
  assert (T : ktinv (ktnode x (ktlift a1 t1) (ktlift a1 (ktlift a2 t2)))) by (apply ktinv_ktnode; assumption).
  split; [|apply kinv_kcell; assumption].
  rewrite klist_kcell, ktlist_ktnode, !ktlist_ktlift, !klist_klift by (assumption || apply ktinv_ktlift, Ht2 || apply kinv_klift, Hs').
  cbn [klist]; rewrite !map_app; cbn [app]; rewrite <- app_assoc; reflexivity.
Qed.

Lemma ktshape_ktrebase m w t : ktshape w t -> ktshape w (ktrebase m t).
Proof. destruct t; exact (fun H => H). Qed.

Lemma ktshape_ktlift d w t : ktshape w t -> ktshape w (ktlift d t).
Proof. destruct t; exact (fun H => H). Qed.

Lemma kshape_krebase m s : kshape s -> kshape (krebase m s).
Proof. destruct s; exact (fun H => H). Qed.

Lemma kshape_klift d s : kshape s -> kshape (klift d s).
Proof. destruct s; exact (fun H => H). Qed.

Lemma kshape_kcons x s : kshape s -> kshape (kcons x s).
Proof.
  intros Hs.
  assert (Hdef : kshape (kcell 1 (KLeaf x) s))
    by (split; [reflexivity|apply kshape_krebase, Hs]).
  destruct s as [|a1 w1 t1 [|a2 w2 t2 s']]; cbn [kcons]; try exact Hdef.
  destruct (Nat.eqb_spec w1 w2) as [<-|]; [|exact Hdef].
  destruct Hs as [H1 [H2 Hs']]; split.
  - cbn; exists w1; split; [reflexivity|].
    split; apply ktshape_ktrebase; apply ktshape_ktlift; [|apply ktshape_ktlift]; assumption.
  - apply kshape_krebase, kshape_klift, kshape_klift, Hs'.
Qed.

(** ** Building from a list, and canonicity *)

Theorem kof_list_spec l :
  (forall e, In e l -> eok e) ->
  klist (kof_list l) = l /\ kinv (kof_list l) /\ kshape (kof_list l).
Proof.
  induction l as [|x l IH]; intros Hok; [repeat split; intros k; reflexivity|].
  destruct IH as [H1 [H2 H3]]; [intros e He; apply Hok; right; exact He|].
  cbn [kof_list fold_right]; fold (kof_list l).
  destruct (kcons_spec x (kof_list l) (Hok x (or_introl eq_refl)) H2) as [E Hs].
  rewrite E, H1; repeat split; [exact Hs|apply kshape_kcons, H3].
Qed.

Theorem kcanonical s1 s2 : kcanon s1 -> kcanon s2 -> klist s1 = klist s2 -> s1 = s2.
Proof. unfold kcanon; intros H1 H2 E; rewrite H1, E; symmetry; exact H2. Qed.

(** Well-formed sequences: built by [kcons] from well-formed elements. *)
Definition kgood (s : kseq) : Prop := kcanon s /\ kinv s.

Lemma kgood_nil : kgood KNil.
Proof. split; [reflexivity|split; [intro k; reflexivity|exact I]]. Qed.

Theorem kgood_kcons x s : eok x -> kgood s -> kgood (kcons x s) /\ klist (kcons x s) = x :: klist s.
Proof.
  intros Hx [Hc Hs]; destruct (kcons_spec x s Hx Hs) as [E Hs'].
  split; [split; [|exact Hs']|exact E].
  unfold kcanon; rewrite E; cbn [kof_list fold_right]; fold (kof_list (klist s)).
  rewrite <- Hc; reflexivity.
Qed.

Theorem kgood_of_list l : (forall e, In e l -> eok e) -> kgood (kof_list l) /\ klist (kof_list l) = l.
Proof.
  intros Hok; destruct (kof_list_spec l Hok) as [E [Hs _]].
  split; [split; [unfold kcanon; rewrite E; reflexivity|exact Hs]|exact E].
Qed.

Lemma kgood_shape s : kgood s -> kshape s.
Proof.
  intros [Hc Hs]; rewrite Hc; apply (kof_list_spec (klist s) (kinv_ok s Hs)).
Qed.

(** ** Indexing *)

Lemma div2_succ_double n : Nat.div2 (S (n + n)) = n.
Proof. replace (n + n) with (2 * n) by lia; apply Nat.div2_succ_double. Qed.

Lemma ktlength w t : ktshape w t -> length (ktlist t) = w.
Proof.
  revert w; induction t as [x|a x l IHl r IHr]; cbn; [intros w ->; reflexivity|].
  intros w [w' [-> [Hl Hr]]]; rewrite length_map; cbn; rewrite length_app, (IHl _ Hl), (IHr _ Hr); reflexivity.
Qed.

Theorem ktnth_spec w t i : ktshape w t -> ktnth w t i = nth_error (ktlist t) i.
Proof.
  revert w i; induction t as [x|a x l IHl r IHr]; intros w i Hw; cbn [ktnth ktlist].
  - destruct i as [|[|i]]; reflexivity.
  - destruct Hw as [w' [-> [Hl Hr]]]; rewrite div2_succ_double.
    destruct i as [|j]; [reflexivity|].
    rewrite nth_error_map; cbn [nth_error]; f_equal.
    destruct (Nat.ltb_spec j w') as [Hj|Hj].
    + rewrite nth_error_app1 by (rewrite (ktlength _ _ Hl); exact Hj); apply IHl, Hl.
    + rewrite nth_error_app2, (ktlength _ _ Hl) by (rewrite (ktlength _ _ Hl); exact Hj); apply IHr, Hr.
Qed.

Lemma klength_spec s : kshape s -> klength s = length (klist s).
Proof.
  induction s as [|a w t s IH]; cbn; [reflexivity|].
  intros [Ht Hs]; rewrite length_map, length_app, (ktlength _ _ Ht), IH by exact Hs; reflexivity.
Qed.

Theorem knth_spec s i : kshape s -> knth s i = nth_error (klist s) i.
Proof.
  revert i; induction s as [|a w t s IH]; intros i Hs; cbn [knth klist];
    [destruct i; reflexivity|].
  destruct Hs as [Ht Hs]; rewrite nth_error_map; f_equal.
  destruct (Nat.ltb_spec i w) as [Hi|Hi].
  - rewrite nth_error_app1 by (rewrite (ktlength _ _ Ht); exact Hi); apply ktnth_spec, Ht.
  - rewrite nth_error_app2, (ktlength _ _ Ht) by (rewrite (ktlength _ _ Ht); exact Hi); apply IH, Hs.
Qed.

End Skew.
