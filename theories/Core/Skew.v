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
     | KNode a x l r => cwf a /\ eok x /\ ktinv l /\ ktinv r
     end.

Fixpoint kinv (s : kseq) : Prop :=
  (forall k, cget (ksann s) k = lmin (klist s) k)
  /\ match s with
     | KNil => True
     | KCons a _ t s' => cwf a /\ ktinv t /\ kinv s'
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

(** The sizes of the spine's trees, and the ones [kcons] produces: two
    equal front trees merge under a new node. *)
Fixpoint kweights (s : kseq) : list nat :=
  match s with KNil => [] | KCons _ w _ s' => w :: kweights s' end.

Definition wcons (ws : list nat) : list nat :=
  match ws with
  | w1 :: w2 :: ws' => if Nat.eqb w1 w2 then S (w1 + w2) :: ws' else 1 :: ws
  | _ => 1 :: ws
  end.

Definition cweights (n : nat) : list nat := Nat.iter n wcons [].

(** Canonical: the spine is the one [kcons] builds for the length. *)
Definition kcanon (s : kseq) : Prop := kweights s = cweights (klength s).

(** ** Trees *)

Lemma ktinv_ann t : ktinv t -> forall k, cget (ktann t) k = lmin (ktlist t) k.
Proof. destruct t; cbn [ktinv]; tauto. Qed.

Lemma ktinv_ok t : ktinv t -> forall e, In e (ktlist t) -> eok e.
Proof.
  induction t as [x|a x l IHl r IHr]; cbn [ktinv ktlist].
  - intros [_ H] e [<-|[]]; exact H.
  - intros [_ [_ [Hx [Hl Hr]]]] e Hin; apply in_map_iff in Hin as [e' [<- Hin]].
    apply ok_unshift; destruct Hin as [<-|Hin]; [exact Hx|].
    apply in_app_or in Hin as [Hin|Hin]; [apply IHl|apply IHr]; assumption.
Qed.



(** ** Trees *)

Lemma ktinv_node_ok a x l r :
  ktinv (KNode a x l r) -> forall e, In e (x :: ktlist l ++ ktlist r) -> eok e.
Proof.
  intros [_ [_ [Hx [Hl Hr]]]] e [<-|Hin]; [exact Hx|].
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
  - destruct Ht as [Ha [_ Hs]]; split; [|split; [apply cwf_cmap2|exact Hs]]; intro k.
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
  - destruct Ht as [Ha [_ Hs]]; split; [|split; [apply cwf_cmap2|exact Hs]]; intro k.
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
  cbn [ktinv ktann]; split; [|split; [apply cwf_cmap2|split; [apply ok_shift, Hx|split; apply ktinv_ktrebase]]];
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
  intros [_ [_ [Ht Hs]]] e Hin; apply in_map_iff in Hin as [e' [<- Hin]]; apply ok_unshift.
  apply in_app_or in Hin as [Hin|Hin]; [apply (ktinv_ok t Ht)|apply IH]; assumption.
Qed.

Lemma kinv_cell_ok a w t s :
  kinv (KCons a w t s) -> forall e, In e (ktlist t ++ klist s) -> eok e.
Proof.
  intros [_ [_ [Ht Hs]]] e Hin.
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
  destruct Hs as [Ha [_ Hs]]; split; [|split; [apply cwf_cmap2|exact Hs]]; intro k.
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
  destruct Hs as [Ha [_ Hs]]; split; [|split; [apply cwf_cmap2|exact Hs]]; intro k.
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
  cbn [kinv ksann]; split; [|split; [apply cwf_cmap2|split; [apply ktinv_ktrebase|apply kinv_krebase]]];
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
  destruct Hs as [Ha1 [Ca1 [Ht1 [Ha2 [Ca2 [Ht2 Hs']]]]]].
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

(** ** Canonicity *)

Lemma kweights_kcell w t s : kweights (kcell w t s) = w :: kweights s.
Proof. destruct s; reflexivity. Qed.

Lemma kweights_krebase d s : kweights (krebase d s) = kweights s.
Proof. destruct s; reflexivity. Qed.

Lemma kweights_klift d s : kweights (klift d s) = kweights s.
Proof. destruct s; reflexivity. Qed.

Lemma klength_weights s : klength s = fold_right Nat.add 0 (kweights s).
Proof. induction s; cbn; congruence. Qed.

Lemma kweights_kcons x s : kweights (kcons x s) = wcons (kweights s).
Proof.
  destruct s as [|a1 w1 t1 [|a2 w2 t2 s']]; cbn [kcons]; try apply kweights_kcell.
  cbn [kweights wcons]; destruct (Nat.eqb w1 w2); rewrite kweights_kcell;
    [rewrite kweights_klift, kweights_klift|]; reflexivity.
Qed.

Lemma sum_wcons ws : fold_right Nat.add 0 (wcons ws) = S (fold_right Nat.add 0 ws).
Proof.
  destruct ws as [|w1 [|w2 ws]]; cbn; try lia.
  destruct (Nat.eqb w1 w2); cbn; lia.
Qed.

Lemma klength_kcons x s : klength (kcons x s) = S (klength s).
Proof. rewrite !klength_weights, kweights_kcons; apply sum_wcons. Qed.

Lemma kcanon_kcons x s : kcanon s -> kcanon (kcons x s).
Proof.
  unfold kcanon; intros H; rewrite kweights_kcons, klength_kcons, H; reflexivity.
Qed.

Lemma ktshape_pos w t : ktshape w t -> 1 <= w.
Proof. destruct t; cbn; [lia|intros [w' [-> _]]; lia]. Qed.

Theorem ktcanonical t1 t2 w :
  ktinv t1 -> ktinv t2 -> ktshape w t1 -> ktshape w t2 -> ktlist t1 = ktlist t2 -> t1 = t2.
Proof.
  revert t2 w; induction t1 as [x1|a1 x1 l1 IHl r1 IHr]; intros [x2|a2 x2 l2 r2] w H1 H2 S1 S2 E.
  - injection E as ->; reflexivity.
  - exfalso; cbn in S1, S2; destruct S2 as [w' [Hw [Sl _]]]; pose proof (ktshape_pos _ _ Sl); lia.
  - exfalso; cbn in S1, S2; destruct S1 as [w' [Hw [Sl _]]]; pose proof (ktshape_pos _ _ Sl); lia.
  - cbn in S1, S2; destruct S1 as [w1 [Hw1 [Sl1 Sr1]]], S2 as [w2 [Hw2 [Sl2 Sr2]]].
    assert (w1 = w2) as <- by lia.
    assert (Ha : a1 = a2).
    { apply counts_ext; [apply H1|apply H2|]; intro k.
      transitivity (lmin (ktlist (KNode a1 x1 l1 r1)) k); [apply (ktinv_ann _ H1)|].
      rewrite E; symmetry; apply (ktinv_ann _ H2). }
    subst a2; cbn [ktlist] in E.
    apply (map_inj_ok (unshift a1) eok) in E;
      [|intros x y Hx Hy; apply unshift_inj; assumption
       |apply (ktinv_node_ok _ _ _ _ H1)|apply (ktinv_node_ok _ _ _ _ H2)].
    injection E as -> E.
    destruct H1 as [_ [_ [_ [Hl1 Hr1]]]], H2 as [_ [_ [_ [Hl2 Hr2]]]].
    apply app_inj_length in E as [El Er];
      [|rewrite (ktlength _ _ Sl1), (ktlength _ _ Sl2); reflexivity].
    f_equal; [apply (IHl l2 w1)|apply (IHr r2 w1)]; assumption.
Qed.

(** Well-formed sequences. *)
Definition kgood (s : kseq) : Prop := kinv s /\ kshape s /\ kcanon s.

Lemma kgood_shape s : kgood s -> kshape s.
Proof. intros [_ [H _]]; exact H. Qed.

Lemma kgood_inv s : kgood s -> kinv s.
Proof. intros [H _]; exact H. Qed.

Lemma kgood_nil : kgood KNil.
Proof. split; [split; [intro k; reflexivity|exact I]|split; reflexivity]. Qed.

Theorem kgood_kcons x s : eok x -> kgood s -> kgood (kcons x s) /\ klist (kcons x s) = x :: klist s.
Proof.
  intros Hx [Hs [Hsh Hc]]; destruct (kcons_spec x s Hx Hs) as [E Hs'].
  split; [split; [exact Hs'|split; [apply kshape_kcons, Hsh|apply kcanon_kcons, Hc]]|exact E].
Qed.

Theorem kcanonical s1 s2 : kgood s1 -> kgood s2 -> klist s1 = klist s2 -> s1 = s2.
Proof.
  intros G1 G2 E.
  assert (Hw : kweights s1 = kweights s2).
  { destruct G1 as [_ [S1 C1]], G2 as [_ [S2 C2]]; rewrite C1, C2, !klength_spec, E by assumption.
    reflexivity. }
  destruct G1 as [H1 [S1 _]], G2 as [H2 [S2 _]].
  revert s2 H2 S2 E Hw; induction s1 as [|a1 w1 t1 s1 IH]; intros [|a2 w2 t2 s2] H2 S2 E Hw;
    try discriminate; [reflexivity|].
  injection Hw as <- Hw.
  assert (Ha : a1 = a2).
  { apply counts_ext; [apply H1|apply H2|]; intro k.
    transitivity (lmin (klist (KCons a1 w1 t1 s1)) k); [apply (kinv_ann _ H1)|].
    rewrite E; symmetry; apply (kinv_ann _ H2). }
  subst a2; cbn [klist] in E.
  apply (map_inj_ok (unshift a1) eok) in E;
    [|intros x y Hx Hy; apply unshift_inj; assumption
     |apply (kinv_cell_ok _ _ _ _ H1)|apply (kinv_cell_ok _ _ _ _ H2)].
  destruct H1 as [_ [_ [Ht1 Hs1]]], H2 as [_ [_ [Ht2 Hs2]]], S1 as [St1 Ss1], S2 as [St2 Ss2].
  apply app_inj_length in E as [Et Es];
    [|rewrite (ktlength _ _ St1), (ktlength _ _ St2); reflexivity].
  f_equal; [apply (ktcanonical _ _ w1); assumption|apply IH; assumption].
Qed.

Lemma kgood_krebase m s : kgood s -> cle m (ksann s) -> kgood (krebase m s).
Proof.
  intros [Hs [Hsh Hc]] Hm; split; [apply kinv_krebase; assumption|split; [apply kshape_krebase, Hsh|]].
  unfold kcanon in *; rewrite kweights_krebase, !klength_weights, kweights_krebase.
  rewrite <- klength_weights; exact Hc.
Qed.

Lemma kgood_klift d s : kgood s -> kgood (klift d s).
Proof.
  intros [Hs [Hsh Hc]]; split; [apply kinv_klift, Hs|split; [apply kshape_klift, Hsh|]].
  unfold kcanon in *; rewrite kweights_klift, !klength_weights, kweights_klift.
  rewrite <- klength_weights; exact Hc.
Qed.

(** Putting a list in front of a sequence, and building from a list. *)
Definition kapp (l : list X) (s : kseq) : kseq := fold_right kcons s l.

Definition kof_list (l : list X) : kseq := kapp l KNil.

(** Taking a shift off the top of a sequence keeps it well formed. *)
Lemma kgood_unlift d s : kgood (klift d s) -> cwf (ksann s) -> kgood s.
Proof.
  destruct s as [|a w t s']; [intros _ _; apply kgood_nil|].
  intros [[Ha [_ [Ht Hs]]] [Hsh Hc]] Cw; cbn [ksann] in Cw.
  split; [|split; [exact Hsh|exact Hc]].
  split; [|split; [exact Cw|split; assumption]].
  intro k; specialize (Ha k); cbn [ksann klist klift] in Ha |- *.
  rewrite lmin_unshift in Ha |- *; rewrite cget_cadd in Ha.
  destruct (cget a k) as [x|], (lmin (ktlist t ++ klist s') k) as [n|]; cbn in Ha |- *;
    try reflexivity; try discriminate;
    try (injection Ha as Ha; f_equal; destruct (cget d k); lia);
    destruct (cget d k); discriminate.
Qed.

Theorem kgood_kapp l s : (forall e, In e l -> eok e) -> kgood s ->
  kgood (kapp l s) /\ klist (kapp l s) = l ++ klist s.
Proof.
  intros Hok G; induction l as [|x l IH]; [split; [exact G|reflexivity]|].
  destruct IH as [G1 E]; [intros e He; apply Hok; right; exact He|].
  cbn [kapp fold_right]; fold (kapp l s).
  destruct (kgood_kcons x (kapp l s) (Hok x (or_introl eq_refl)) G1) as [G' E'].
  split; [exact G'|rewrite E', E; reflexivity].
Qed.

Theorem kgood_of_list l : (forall e, In e l -> eok e) -> kgood (kof_list l) /\ klist (kof_list l) = l.
Proof.
  intros Hok; destruct (kgood_kapp l KNil Hok kgood_nil) as [G E].
  split; [exact G|unfold kof_list; rewrite E, app_nil_r; reflexivity].
Qed.

(** ** Dropping a prefix

    [kdrop s i] is [s] without its first [i] elements, in O(log n): the
    cells before the one holding index [i] are skipped, and inside that
    cell's tree the path to [i] is followed, keeping the right subtrees it
    passes as new cells.  The result is the sequence [kcons] builds. *)

Fixpoint ktdrop (w : nat) (t : ktree) (i : nat) (acc : kseq) : kseq :=
  match t with
  | KLeaf _ => match i with 0 => kcell 1 t acc | S _ => acc end
  | KNode a x l r =>
      match i with
      | 0 => kcell w t acc
      | S j =>
          let w' := Nat.div2 w in
          if Nat.ltb j w' then ktdrop w' (ktlift a l) j (kcell w' (ktlift a r) acc)
          else ktdrop w' (ktlift a r) (j - w') acc
      end
  end.

Fixpoint kdrop (s : kseq) (i : nat) : kseq :=
  match s with
  | KNil => KNil
  | KCons a w t s' =>
      if Nat.ltb i w then klift a (ktdrop w t i s') else klift a (kdrop s' (i - w))
  end.

Lemma ktdrop_spec w t : ktshape w t -> ktinv t -> forall i acc, i < w -> kinv acc ->
  kinv (ktdrop w t i acc) /\ klist (ktdrop w t i acc) = skipn i (ktlist t) ++ klist acc.
Proof.
  revert t; induction w as [w IH] using (well_founded_induction lt_wf).
  intros [x|a x l r] Hw Ht i acc Hi Hacc.
  - cbn in Hw; subst w; destruct i as [|i]; [|lia]; cbn [ktdrop].
    split; [apply kinv_kcell|apply klist_kcell]; assumption.
  - destruct Hw as [w' [-> [Hl Hr]]]; destruct i as [|j].
    + cbn [ktdrop]; split; [apply kinv_kcell|apply klist_kcell]; assumption.
    + destruct Ht as [_ [_ [_ [Tl Tr]]]].
      assert (Tl' : ktinv (ktlift a l)) by (apply ktinv_ktlift, Tl).
      assert (Tr' : ktinv (ktlift a r)) by (apply ktinv_ktlift, Tr).
      cbn [ktdrop ktlist]; rewrite div2_succ_double, skipn_map; cbn [skipn].
      destruct (Nat.ltb_spec j w') as [Hj|Hj].
      * assert (Hc : kinv (kcell w' (ktlift a r) acc)) by (apply kinv_kcell; assumption).
        destruct (IH w' ltac:(lia) _ (ktshape_ktlift a w' l Hl) Tl' j _ Hj Hc) as [I E].
        split; [exact I|]; rewrite E, klist_kcell, !ktlist_ktlift by assumption.
        rewrite skipn_app, (ktlength _ _ Hl), skipn_map, !map_app, <- app_assoc.
        replace (j - w') with 0 by lia; reflexivity.
      * destruct (IH w' ltac:(lia) _ (ktshape_ktlift a w' r Hr) Tr' (j - w') acc ltac:(lia) Hacc) as [I E].
        split; [exact I|]; rewrite E, ktlist_ktlift by assumption.
        rewrite skipn_app, (ktlength _ _ Hl), (skipn_all2 (ktlist l)) by (rewrite (ktlength _ _ Hl); lia).
        rewrite skipn_map; reflexivity.
Qed.

Lemma kdrop_spec s : kinv s -> kshape s -> forall i,
  kinv (kdrop s i) /\ klist (kdrop s i) = skipn i (klist s).
Proof.
  induction s as [|a w t s IH]; intros Hs Hsh i; [split; [exact Hs|destruct i; reflexivity]|].
  destruct Hs as [_ [_ [Ht Hs]]], Hsh as [Hw Hsh]; cbn [kdrop klist].
  destruct (Nat.ltb_spec i w) as [Hi|Hi].
  - destruct (ktdrop_spec w t Hw Ht i s Hi Hs) as [I E].
    split; [apply kinv_klift, I|rewrite klist_klift, E, skipn_map, skipn_app by exact I].
    rewrite (ktlength _ _ Hw); replace (i - w) with 0 by lia; cbn [skipn]; rewrite map_app; reflexivity.
  - destruct (IH Hs Hsh (i - w)) as [I E].
    split; [apply kinv_klift, I|rewrite klist_klift, E, skipn_map, skipn_app by exact I].
    rewrite (ktlength _ _ Hw), (skipn_all2 (ktlist t)) by (rewrite (ktlength _ _ Hw); exact Hi); reflexivity.
Qed.

Lemma ktdrop_shape w t : ktshape w t -> forall i acc, i < w -> kshape acc -> kshape (ktdrop w t i acc).
Proof.
  revert t; induction w as [w IH] using (well_founded_induction lt_wf).
  intros [x|a x l r] Hw i acc Hi Hacc.
  - cbn in Hw; subst w; destruct i as [|i]; [|lia]; split; [reflexivity|apply kshape_krebase, Hacc].
  - destruct i as [|j]; [split; [apply ktshape_ktrebase, Hw|apply kshape_krebase, Hacc]|].
    destruct Hw as [w' [-> [Hl Hr]]]; cbn [ktdrop]; rewrite div2_succ_double.
    destruct (Nat.ltb_spec j w') as [Hj|Hj].
    + apply IH; [lia|apply ktshape_ktlift, Hl|exact Hj|].
      split; [apply ktshape_ktrebase, ktshape_ktlift, Hr|apply kshape_krebase, Hacc].
    + apply IH; [lia|apply ktshape_ktlift, Hr|lia|exact Hacc].
Qed.

Lemma kdrop_shape s : kshape s -> forall i, kshape (kdrop s i).
Proof.
  induction s as [|a w t s IH]; intros Hsh i; [exact I|].
  destruct Hsh as [Hw Hsh]; cbn [kdrop]; destruct (Nat.ltb_spec i w) as [Hi|Hi];
    apply kshape_klift; [apply ktdrop_shape; assumption|apply IH, Hsh].
Qed.

(** Weights: dropping one element undoes [wcons]. *)
Definition wtail (ws : list nat) : list nat :=
  match ws with
  | [] => []
  | 1 :: ws' => ws'
  | S w :: ws' => Nat.div2 w :: Nat.div2 w :: ws'
  | 0 :: ws' => ws'
  end.

Lemma wcons_pos ws : (forall w, In w ws -> 1 <= w) -> forall w, In w (wcons ws) -> 1 <= w.
Proof.
  intros H; destruct ws as [|w1 [|w2 ws]]; cbn [wcons].
  - intros w [<-|[]]; lia.
  - intros w [<-|Hin]; [lia|apply H, Hin].
  - destruct (Nat.eqb w1 w2); intros w [<-|Hin]; try lia; apply H; [right; right; exact Hin|exact Hin].
Qed.

Lemma cweights_pos n : forall w, In w (cweights n) -> 1 <= w.
Proof.
  induction n as [|n IH]; [intros w []|].
  unfold cweights; cbn [Nat.iter]; apply wcons_pos, IH.
Qed.

Lemma iter_add {A} (f : A -> A) i j x : Nat.iter (i + j) f x = Nat.iter i f (Nat.iter j f x).
Proof.
  induction i as [|i IH]; [reflexivity|].
  change (f (Nat.iter (i + j) f x) = f (Nat.iter i f (Nat.iter j f x))); rewrite IH; reflexivity.
Qed.

Lemma iter_succ_r {A} (f : A -> A) n x : Nat.iter (S n) f x = Nat.iter n f (f x).
Proof. rewrite <- Nat.add_1_r, iter_add; reflexivity. Qed.

Lemma wtail_node v ws : 1 <= v -> wtail (S (v + v) :: ws) = v :: v :: ws.
Proof.
  intros Hv; destruct v as [|v]; [lia|].
  change (wtail (S (S v + S v) :: ws)) with (Nat.div2 (S v + S v) :: Nat.div2 (S v + S v) :: ws).
  replace (S v + S v) with (2 * S v) by lia; rewrite Nat.div2_double; reflexivity.
Qed.

Lemma wtail_wcons ws : (forall w, In w ws -> 1 <= w) -> wtail (wcons ws) = ws.
Proof.
  intros H; destruct ws as [|w1 [|w2 ws]]; cbn [wcons]; try reflexivity.
  destruct (Nat.eqb_spec w1 w2) as [<-|]; [|reflexivity].
  assert (1 <= w1) by (apply H; left; reflexivity).
  apply wtail_node; assumption.
Qed.

Lemma wtail_cweights n : wtail (cweights (S n)) = cweights n.
Proof. unfold cweights; cbn [Nat.iter]; apply wtail_wcons, cweights_pos. Qed.

Lemma wtail_iter_cweights i n : Nat.iter i wtail (cweights n) = cweights (n - i).
Proof.
  induction i as [|i IH]; [rewrite Nat.sub_0_r; reflexivity|].
  change (wtail (Nat.iter i wtail (cweights n)) = cweights (n - S i)).
  rewrite IH; destruct (n - i) as [|m] eqn:E; [replace (n - S i) with 0 by lia; reflexivity|].
  rewrite wtail_cweights; f_equal; lia.
Qed.

Lemma wtail_tree w t ws : ktshape w t -> Nat.iter w wtail (w :: ws) = ws.
Proof.
  revert w ws; induction t as [x|a x l IHl r IHr]; intros w ws Hw; [cbn in Hw; subst w; reflexivity|].
  destruct Hw as [w' [-> [Hl Hr]]].
  rewrite iter_succ_r, wtail_node, iter_add by apply (ktshape_pos _ _ Hl).
  rewrite (IHl _ _ Hl); apply (IHr _ _ Hr).
Qed.

Lemma ktdrop_weights w t : ktshape w t -> forall i acc, i < w ->
  kweights (ktdrop w t i acc) = Nat.iter i wtail (w :: kweights acc).
Proof.
  revert t; induction w as [w IH] using (well_founded_induction lt_wf).
  intros [x|a x l r] Hw i acc Hi.
  - cbn in Hw; subst w; destruct i as [|i]; [apply kweights_kcell|lia].
  - destruct i as [|j]; [apply kweights_kcell|].
    destruct Hw as [w' [-> [Hl Hr]]]; cbn [ktdrop]; rewrite div2_succ_double.
    rewrite iter_succ_r, wtail_node by apply (ktshape_pos _ _ Hl).
    destruct (Nat.ltb_spec j w') as [Hj|Hj].
    + rewrite (IH w' ltac:(lia) _ (ktshape_ktlift a _ l Hl) j _ Hj), kweights_kcell; reflexivity.
    + rewrite (IH w' ltac:(lia) _ (ktshape_ktlift a _ r Hr) (j - w') _ ltac:(lia)).
      rewrite <- (wtail_tree _ _ (w' :: kweights acc) Hl) at 1; rewrite <- iter_add; f_equal; lia.
Qed.

Lemma kdrop_weights s : kshape s -> forall i, kweights (kdrop s i) = Nat.iter i wtail (kweights s).
Proof.
  induction s as [|a w t s IH]; intros Hsh i.
  - cbn [kdrop kweights]; induction i as [|i IHi]; [reflexivity|].
    change (Nat.iter (S i) wtail []) with (wtail (Nat.iter i wtail [])); rewrite <- IHi; reflexivity.
  - destruct Hsh as [Hw Hsh]; cbn [kdrop kweights].
    destruct (Nat.ltb_spec i w) as [Hi|Hi]; rewrite kweights_klift;
      [apply ktdrop_weights; assumption|].
    rewrite IH by exact Hsh; rewrite <- (wtail_tree _ _ (kweights s) Hw) at 1.
    rewrite <- iter_add; f_equal; lia.
Qed.

Theorem kgood_kdrop s i : kgood s -> kgood (kdrop s i) /\ klist (kdrop s i) = skipn i (klist s).
Proof.
  intros [Hs [Hsh Hc]]; destruct (kdrop_spec s Hs Hsh i) as [I E].
  split; [|exact E]; split; [exact I|split; [apply kdrop_shape, Hsh|]].
  unfold kcanon in *; rewrite kdrop_weights, Hc, wtail_iter_cweights by exact Hsh.
  rewrite !klength_spec, E, length_skipn by (exact Hsh || apply kdrop_shape, Hsh); reflexivity.
Qed.

(** ** Deciding well-formedness *)

Section Decide.

Variable eokb : X -> bool.
Hypothesis eokb_spec : forall x, eokb x = true <-> eok x.

Fixpoint ktinvb (t : ktree) : bool :=
  match t with
  | KLeaf x => eokb x
  | KNode a x l r => cwfb a && ceqb a (lminc (ktlist t)) && eokb x && ktinvb l && ktinvb r
  end.

Lemma ktinvb_spec t : ktinvb t = true <-> ktinv t.
Proof.
  induction t as [x|a x l IHl r IHr]; cbn [ktinvb ktinv ktann].
  - rewrite eokb_spec; split; [intros H; split; [intro k; cbn [ktlist]; rewrite lmin_single; reflexivity|exact H]|intros [_ H]; exact H].
  - rewrite !andb_true_iff, cwfb_spec, eokb_spec, IHl, IHr.
    split.
    + intros [[[[Hw Ha] Hx] Hl] Hr]; split; [apply (ceqb_lminc a _ Hw), Ha|tauto].
    + intros [Ha [Hw [Hx [Hl Hr]]]]; repeat split; try assumption; apply (ceqb_lminc a _ Hw), Ha.
Qed.

Fixpoint kinvb (s : kseq) : bool :=
  match s with
  | KNil => true
  | KCons a _ t s' => cwfb a && ceqb a (lminc (klist s)) && ktinvb t && kinvb s'
  end.

Lemma kinvb_spec s : kinvb s = true <-> kinv s.
Proof.
  induction s as [|a w t s IH]; cbn [kinvb kinv ksann].
  - split; [intros _; split; [intro k; reflexivity|exact I]|reflexivity].
  - rewrite !andb_true_iff, cwfb_spec, ktinvb_spec, IH.
    split.
    + intros [[[Hw Ha] Ht] Hs]; split; [apply (ceqb_lminc a _ Hw), Ha|tauto].
    + intros [Ha [Hw [Ht Hs]]]; repeat split; try assumption; apply (ceqb_lminc a _ Hw), Ha.
Qed.

Fixpoint ktshapeb (w : nat) (t : ktree) : bool :=
  match t with
  | KLeaf _ => Nat.eqb w 1
  | KNode _ _ l r =>
      let w' := Nat.div2 (w - 1) in Nat.eqb w (S (w' + w')) && ktshapeb w' l && ktshapeb w' r
  end.

Lemma ktshapeb_spec t : forall w, ktshapeb w t = true <-> ktshape w t.
Proof.
  induction t as [x|a x l IHl r IHr]; intros w; cbn [ktshapeb ktshape]; [apply Nat.eqb_eq|].
  rewrite !andb_true_iff, Nat.eqb_eq, IHl, IHr; split.
  - intros [[Hw Hl] Hr]; eauto.
  - intros [w' [-> [Hl Hr]]].
    replace (S (w' + w') - 1) with (2 * w') by lia; rewrite Nat.div2_double.
    auto.
Qed.

Fixpoint kshapeb (s : kseq) : bool :=
  match s with KNil => true | KCons _ w t s' => ktshapeb w t && kshapeb s' end.

Lemma kshapeb_spec s : kshapeb s = true <-> kshape s.
Proof.
  induction s as [|a w t s IH]; cbn [kshapeb kshape]; [split; [intros _; exact I|reflexivity]|].
  rewrite andb_true_iff, ktshapeb_spec, IH; reflexivity.
Qed.

Definition kcanonb (s : kseq) : bool :=
  if list_eq_dec Nat.eq_dec (kweights s) (cweights (klength s)) then true else false.

Lemma kcanonb_spec s : kcanonb s = true <-> kcanon s.
Proof. unfold kcanonb, kcanon; destruct (list_eq_dec _ _ _); split; congruence. Qed.

Definition kgoodb (s : kseq) : bool := kinvb s && kshapeb s && kcanonb s.

Lemma kgoodb_spec s : kgoodb s = true <-> kgood s.
Proof. unfold kgoodb, kgood; rewrite !andb_true_iff, kinvb_spec, kshapeb_spec, kcanonb_spec; tauto. Qed.

End Decide.

End Skew.

Arguments ktree : clear implicits.
Arguments kseq : clear implicits.
