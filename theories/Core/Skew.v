(** * Skew sequences with weakening counts

    Sequences that grow at the front, as in Okasaki's skew-binary
    random-access lists: a spine of complete binary trees, each of size
    [2ᵏ⁺¹ − 1] with an element at every node.  [kcons] builds at most one
    node, from the two front trees, and indexing is O(log n).

    Every tree node carries a count map: how far the uses of everything
    below it start above its parent's base (Counts.v).  Elements are stored
    relative to the base of the node that holds them.  The trees of the
    spine are all stored relative to one base, kept at the head of the
    sequence, so consing an element only lowers that base at the labels the
    element uses and moves each of the O(log n) trees by the difference.
    The sequence is generic in its elements, which only need to say what
    they use and how to move between bases.

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

(** The trees of a sequence with their sizes, front first. *)
Inductive kspine : Type :=
| SNil
| SCons (w : nat) (t : ktree) (s : kspine).

(** A sequence: empty, or a base (relative to the parent's) and a
    non-empty spine whose trees are stored relative to it. *)
Inductive kseq : Type :=
| KNil
| KSeq (a : counts) (w : nat) (t : ktree) (s : kspine).

Definition ktann (t : ktree) : counts :=
  match t with KLeaf x => uses x | KNode a _ _ _ => a end.

Definition ksann (s : kseq) : counts :=
  match s with KNil => cnone | KSeq a _ _ _ => a end.

(** The elements denoted, relative to the parent's base (trees in
    preorder, so every subtree is a contiguous range). *)
Fixpoint ktlist (t : ktree) : list X :=
  match t with
  | KLeaf x => [x]
  | KNode a x l r => map (unshift a) (x :: ktlist l ++ ktlist r)
  end.

Fixpoint splist (s : kspine) : list X :=
  match s with SNil => [] | SCons _ t s' => ktlist t ++ splist s' end.

Definition klist (s : kseq) : list X :=
  match s with KNil => [] | KSeq a w t s' => map (unshift a) (splist (SCons w t s')) end.

(** Moving a whole tree, spine or sequence to a base [d] higher or lower:
    only the tops change. *)
Definition ktrebase (d : counts) (t : ktree) : ktree :=
  match t with KLeaf x => KLeaf (shift d x) | KNode a x l r => KNode (csub a d) x l r end.

Definition ktlift (d : counts) (t : ktree) : ktree :=
  match t with KLeaf x => KLeaf (unshift d x) | KNode a x l r => KNode (cadd d a) x l r end.

Fixpoint sprebase (d : counts) (s : kspine) : kspine :=
  match s with SNil => SNil | SCons w t s' => SCons w (ktrebase d t) (sprebase d s') end.

Fixpoint splift (d : counts) (s : kspine) : kspine :=
  match s with SNil => SNil | SCons w t s' => SCons w (ktlift d t) (splift d s') end.

Definition krebase (d : counts) (s : kseq) : kseq :=
  match s with KNil => KNil | KSeq a w t s' => KSeq (csub a d) w t s' end.

Definition klift (d : counts) (s : kseq) : kseq :=
  match s with KNil => KNil | KSeq a w t s' => KSeq (cadd d a) w t s' end.

(** Building a node: its counts are the minimum of what is below. *)
Definition ktnode (x : X) (t1 t2 : ktree) : ktree :=
  let m := cmin (uses x) (cmin (ktann t1) (ktann t2)) in
  KNode m (shift m x) (ktrebase m t1) (ktrebase m t2).

(** The minimum over a spine's trees. *)
Fixpoint spann (s : kspine) : counts :=
  match s with SNil => cnone | SCons _ t s' => cmin (ktann t) (spann s') end.

(** A sequence from a spine whose trees are relative to the parent's base:
    the base is their minimum. *)
Definition kmk (s : kspine) : kseq :=
  match s with
  | SNil => KNil
  | SCons w t s' =>
      let m := cmin (ktann t) (spann s') in KSeq m w (ktrebase m t) (sprebase m s')
  end.

(** Consing: the base drops to cover [x], the trees move up by the
    difference ([cexcess], which only involves the labels [x] uses), and
    two front trees of the same size merge under a new node. *)
Definition kcons (x : X) (s : kseq) : kseq :=
  match s with
  | KNil => kmk (SCons 1 (KLeaf x) SNil)
  | KSeq a w1 t1 s' =>
      let a' := cmin a (uses x) in
      let d := cexcess a (uses x) in
      let x' := shift a' x in
      let t1' := ktlift d t1 in
      match splift d s' with
      | SCons w2 t2 s'' =>
          if Nat.eqb w1 w2 then KSeq a' (S (w1 + w2)) (ktnode x' t1' t2) s''
          else KSeq a' 1 (KLeaf x') (SCons w1 t1' (SCons w2 t2 s''))
      | SNil => KSeq a' 1 (KLeaf x') (SCons w1 t1' SNil)
      end
  end.

(** Indexing; [w] is the size of the tree. *)
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

Fixpoint spnth (s : kspine) (i : nat) : option X :=
  match s with
  | SNil => None
  | SCons w t s' => if Nat.ltb i w then ktnth w t i else spnth s' (i - w)
  end.

Definition knth (s : kseq) (i : nat) : option X :=
  match s with KNil => None | KSeq a w t s' => option_map (unshift a) (spnth (SCons w t s') i) end.

Fixpoint splength (s : kspine) : nat :=
  match s with SNil => 0 | SCons w _ s' => w + splength s' end.

Definition klength (s : kseq) : nat :=
  match s with KNil => 0 | KSeq _ w _ s' => w + splength s' end.

(** ** Invariants *)

(** Every node's counts are the minimum over what it denotes, and stored
    elements are well formed. *)
Fixpoint ktinv (t : ktree) : Prop :=
  (forall k, cget (ktann t) k = lmin (ktlist t) k)
  /\ match t with
     | KLeaf x => eok x
     | KNode a x l r => cwf a /\ eok x /\ ktinv l /\ ktinv r
     end.

Fixpoint spinv (s : kspine) : Prop :=
  match s with SNil => True | SCons _ t s' => ktinv t /\ spinv s' end.

Definition kinv (s : kseq) : Prop :=
  (forall k, cget (ksann s) k = lmin (klist s) k)
  /\ match s with
     | KNil => True
     | KSeq a _ t s' => cwf a /\ ktinv t /\ spinv s'
     end.

(** Sizes: a tree of size [w] has children of size [div2 w]. *)
Fixpoint ktshape (w : nat) (t : ktree) : Prop :=
  match t with
  | KLeaf _ => w = 1
  | KNode _ _ l r => exists w', w = S (w' + w') /\ ktshape w' l /\ ktshape w' r
  end.

Fixpoint spshape (s : kspine) : Prop :=
  match s with SNil => True | SCons w t s' => ktshape w t /\ spshape s' end.

Definition kshape (s : kseq) : Prop :=
  match s with KNil => True | KSeq _ w t s' => ktshape w t /\ spshape s' end.

(** The sizes of the spine's trees, and the ones [kcons] produces: two
    equal front trees merge under a new node. *)
Fixpoint spweights (s : kspine) : list nat :=
  match s with SNil => [] | SCons w _ s' => w :: spweights s' end.

Definition kweights (s : kseq) : list nat :=
  match s with KNil => [] | KSeq _ w _ s' => w :: spweights s' end.

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
    cbn [ksann]; rewrite Hl, lmin_unshift, cget_cadd, Ha; reflexivity.
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

(** ** Spines *)

Lemma spinv_ok s : spinv s -> forall e, In e (splist s) -> eok e.
Proof.
  induction s as [|w t s IH]; cbn [spinv splist]; [intros _ _ []|].
  intros [Ht Hs] e Hin; apply in_app_or in Hin as [Hin|Hin]; [apply (ktinv_ok t Ht)|apply IH]; assumption.
Qed.

Lemma spann_spec s : spinv s -> forall k, cget (spann s) k = lmin (splist s) k.
Proof.
  induction s as [|w t s IH]; cbn [spinv splist spann]; [reflexivity|].
  intros [Ht Hs] k; rewrite cget_cmin, lmin_app, ktinv_ann, IH by assumption; reflexivity.
Qed.

Lemma splist_splift d s : spinv s -> splist (splift d s) = map (unshift d) (splist s).
Proof.
  induction s as [|w t s IH]; cbn [spinv splist splift]; [reflexivity|].
  intros [Ht Hs]; rewrite ktlist_ktlift, IH, map_app by assumption; reflexivity.
Qed.

Lemma spinv_splift d s : spinv s -> spinv (splift d s).
Proof.
  induction s as [|w t s IH]; cbn [spinv splift]; [tauto|].
  intros [Ht Hs]; split; [apply ktinv_ktlift, Ht|apply IH, Hs].
Qed.

Lemma splist_sprebase m s : spinv s -> cle m (spann s) -> splist (sprebase m s) = map (shift m) (splist s).
Proof.
  induction s as [|w t s IH]; cbn [spinv splist sprebase spann]; [reflexivity|].
  intros [Ht Hs] Hm; rewrite ktlist_ktrebase, IH, map_app;
    [reflexivity|exact Hs|apply (cle_cmin_inv_r _ _ _ Hm)|exact Ht|apply (cle_cmin_inv_l _ _ _ Hm)].
Qed.

Lemma spinv_sprebase m s : spinv s -> cle m (spann s) -> spinv (sprebase m s).
Proof.
  induction s as [|w t s IH]; cbn [spinv sprebase spann]; [tauto|].
  intros [Ht Hs] Hm; split; [apply ktinv_ktrebase; [exact Ht|apply (cle_cmin_inv_l _ _ _ Hm)]|].
  apply IH; [exact Hs|apply (cle_cmin_inv_r _ _ _ Hm)].
Qed.

Lemma spweights_splift d s : spweights (splift d s) = spweights s.
Proof. induction s; cbn; congruence. Qed.

Lemma spweights_sprebase d s : spweights (sprebase d s) = spweights s.
Proof. induction s; cbn; congruence. Qed.

Lemma ktshape_ktrebase m w t : ktshape w t -> ktshape w (ktrebase m t).
Proof. destruct t; exact (fun H => H). Qed.

Lemma ktshape_ktlift d w t : ktshape w t -> ktshape w (ktlift d t).
Proof. destruct t; exact (fun H => H). Qed.

Lemma spshape_splift d s : spshape s -> spshape (splift d s).
Proof. induction s; cbn; [tauto|]; intros [H1 H2]; split; [apply ktshape_ktlift|apply IHs]; assumption. Qed.

Lemma spshape_sprebase d s : spshape s -> spshape (sprebase d s).
Proof. induction s; cbn; [tauto|]; intros [H1 H2]; split; [apply ktshape_ktrebase|apply IHs]; assumption. Qed.

(** ** Sequences *)

Lemma kinv_ann s : kinv s -> forall k, cget (ksann s) k = lmin (klist s) k.
Proof. intros [H _]; exact H. Qed.

Lemma kinv_spine a w t s : kinv (KSeq a w t s) -> spinv (SCons w t s).
Proof. intros [_ [_ [Ht Hs]]]; split; assumption. Qed.

Lemma kinv_cell_ok a w t s : kinv (KSeq a w t s) -> forall e, In e (splist (SCons w t s)) -> eok e.
Proof. intros H; apply spinv_ok, (kinv_spine _ _ _ _ H). Qed.

Lemma kinv_ok s : kinv s -> forall e, In e (klist s) -> eok e.
Proof.
  destruct s as [|a w t s]; [intros _ _ []|]; intros Hs e Hin; cbn [klist] in Hin.
  apply in_map_iff in Hin as [e' [<- Hin]]; apply ok_unshift, (kinv_cell_ok _ _ _ _ Hs _ Hin).
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
  cbn [ksann]; rewrite Hl, lmin_shift, cget_csub, Ha; reflexivity.
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
  cbn [ksann]; rewrite Hl, lmin_unshift, cget_cadd, Ha; reflexivity.
Qed.

Lemma cle_refl c : cle c c.
Proof. intros k n m E1 E2; rewrite E1 in E2; injection E2 as ->; lia. Qed.

(** [kmk] *)
Theorem kmk_spec s : spinv s -> kinv (kmk s) /\ klist (kmk s) = splist s.
Proof.
  destruct s as [|w t s]; intros Hs; [split; [split; [intro k; reflexivity|exact I]|reflexivity]|].
  pose proof (spann_spec _ Hs) as Hann; cbn [spann] in Hann.
  destruct Hs as [Ht Hs]; cbn [kmk]; set (m := cmin (ktann t) (spann s)) in *.
  assert (Hm : cle m (spann (SCons w t s))) by apply cle_refl.
  pose proof (splist_sprebase m (SCons w t s) (conj Ht Hs) Hm) as E.
  assert (El : klist (KSeq m w (ktrebase m t) (sprebase m s)) = splist (SCons w t s)).
  { change (map (unshift m) (splist (sprebase m (SCons w t s))) = splist (SCons w t s)).
    rewrite E, map_map; apply map_id_in; intros e Hin.
    apply unshift_shift; [apply (spinv_ok (SCons w t s) (conj Ht Hs) _ Hin)|].
    apply (cle_mem m m (splist (SCons w t s))); [apply cle_refl|exact Hann|exact Hin]. }
  split; [|exact El].
  split; [intro k; rewrite El; apply Hann|split; [apply cwf_cmap2|]].
  pose proof (spinv_sprebase m (SCons w t s) (conj Ht Hs) Hm) as H; exact H.
Qed.

Lemma kweights_kmk s : kweights (kmk s) = spweights s.
Proof. destruct s; cbn; [reflexivity|rewrite spweights_sprebase; reflexivity]. Qed.

Lemma kshape_kmk s : spshape s -> kshape (kmk s).
Proof. destruct s; cbn; [tauto|]; intros [H1 H2]; split; [apply ktshape_ktrebase|apply spshape_sprebase]; assumption. Qed.

(** ** [kcons] *)

Lemma omin_comm a b : omin a b = omin b a.
Proof. destruct a, b; cbn; try reflexivity; f_equal; lia. Qed.

Theorem kcons_spec x s : eok x -> kinv s -> klist (kcons x s) = x :: klist s /\ kinv (kcons x s).
Proof.
  intros Hx Hs; destruct s as [|a w1 t1 s'].
  - assert (Hl : spinv (SCons 1 (KLeaf x) SNil))
      by (split; [split; [intro k; cbn [ktlist]; rewrite lmin_single; reflexivity|exact Hx]|exact I]).
    destruct (kmk_spec _ Hl) as [H E]; split; [exact E|exact H].
  - pose proof (kinv_cell_ok _ _ _ _ Hs) as Hok; pose proof (kinv_ann _ Hs) as Ha.
    destruct Hs as [_ [Cw [Ht1 Hs']]]; cbn [ksann klist] in Ha.
    set (L := splist (SCons w1 t1 s')) in *.
    set (a' := cmin a (uses x)); set (d := cexcess a (uses x)).
    assert (HL : map (unshift a') (map (unshift d) L) = map (unshift a) L).
    { rewrite map_map; apply map_ext_in; intros e Hin; rewrite unshift_unshift; apply unshift_ext.
      intros k Hk; rewrite dval_cplus; apply dval_cexcess, (uses_below a L Ha e k Hin Hk). }
    assert (Hx' : eok (shift a' x)) by apply ok_shift, Hx.
    assert (Ux : unshift a' (shift a' x) = x) by (apply unshift_shift; [exact Hx|apply cle_cmin_r]).
    assert (Hleaf : ktinv (KLeaf (shift a' x)))
      by (split; [intro k; cbn [ktlist]; rewrite lmin_single; reflexivity|exact Hx']).
    assert (Ht1' : ktinv (ktlift d t1)) by apply ktinv_ktlift, Ht1.
    assert (Hs'' : spinv (splift d s')) by apply spinv_splift, Hs'.
    assert (E1 : ktlist (ktlift d t1) ++ splist (splift d s') = map (unshift d) L)
      by (unfold L; cbn [splist]; rewrite ktlist_ktlift, splist_splift, map_app by assumption; reflexivity).
    (* the new list, whichever way the spine is built *)
    assert (Hgen : forall w t sp,
               ktinv t -> spinv sp -> ktlist t ++ splist sp = shift a' x :: map (unshift d) L ->
               klist (KSeq a' w t sp) = x :: map (unshift a) L /\ kinv (KSeq a' w t sp)).
    { intros w t sp Ht Hsp E; cbn [klist splist]; rewrite E; cbn [map]; rewrite Ux, HL.
      split; [reflexivity|]; split; [|split; [apply cwf_cmap2|split; assumption]].
      intro k; cbn [ksann klist splist]; rewrite E; cbn [map]; rewrite Ux, HL.
      change (lmin (x :: map (unshift a) L) k) with (omin (cget (uses x) k) (lmin (map (unshift a) L) k)).
      rewrite <- Ha; unfold a'; rewrite cget_cmin; apply omin_comm. }
    cbn [kcons]; fold a' d; destruct s' as [|w2 t2 s2]; cbn [splift] in *.
    + apply Hgen; [exact Hleaf|split; [exact Ht1'|exact I]|].
      cbn [splist]; rewrite <- E1; cbn [splist]; reflexivity.
    + destruct Hs'' as [Ht2' Hs2']; destruct (Nat.eqb w1 w2).
      * apply Hgen; [apply ktinv_ktnode; assumption|exact Hs2'|].
        rewrite ktlist_ktnode by assumption; cbn [app]; f_equal; rewrite <- E1; cbn [splist].
        rewrite app_assoc; reflexivity.
      * apply Hgen; [exact Hleaf|split; [exact Ht1'|split; assumption]|].
        cbn [splist]; rewrite <- E1; cbn [splist]; reflexivity.
Qed.

Lemma kshape_kcons x s : kshape s -> kshape (kcons x s).
Proof.
  destruct s as [|a w1 t1 [|w2 t2 s2]]; cbn [kcons kmk kshape splift spshape]; [intros _; split; reflexivity| |].
  - intros [H1 _]; split; [reflexivity|split; [apply ktshape_ktlift, H1|exact I]].
  - intros [H1 [H2 H3]]; destruct (Nat.eqb_spec w1 w2) as [<-|].
    + split; [|apply spshape_splift, H3].
      exists w1; split; [reflexivity|]; split; apply ktshape_ktrebase, ktshape_ktlift; assumption.
    + split; [reflexivity|split; [apply ktshape_ktlift, H1|split; [apply ktshape_ktlift, H2|apply spshape_splift, H3]]].
Qed.

Lemma kweights_kcons x s : kweights (kcons x s) = wcons (kweights s).
Proof.
  destruct s as [|a w1 t1 [|w2 t2 s2]]; cbn [kcons kmk kweights splift spweights wcons]; try reflexivity.
  destruct (Nat.eqb w1 w2); cbn [kweights spweights]; rewrite ?spweights_splift; reflexivity.
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


Lemma splength_spec s : spshape s -> splength s = length (splist s).
Proof.
  induction s as [|w t s IH]; cbn; [reflexivity|].
  intros [Ht Hs]; rewrite length_app, (ktlength _ _ Ht), IH by exact Hs; reflexivity.
Qed.

Lemma klength_spec s : kshape s -> klength s = length (klist s).
Proof.
  destruct s as [|a w t s]; [reflexivity|]; intros Hs; cbn [klength klist].
  rewrite length_map; apply (splength_spec (SCons w t s) Hs).
Qed.

Lemma spnth_spec s i : spshape s -> spnth s i = nth_error (splist s) i.
Proof.
  revert i; induction s as [|w t s IH]; intros i Hs; cbn [spnth splist]; [destruct i; reflexivity|].
  destruct Hs as [Ht Hs]; destruct (Nat.ltb_spec i w) as [Hi|Hi].
  - rewrite nth_error_app1 by (rewrite (ktlength _ _ Ht); exact Hi); apply ktnth_spec, Ht.
  - rewrite nth_error_app2, (ktlength _ _ Ht) by (rewrite (ktlength _ _ Ht); exact Hi); apply IH, Hs.
Qed.

Theorem knth_spec s i : kshape s -> knth s i = nth_error (klist s) i.
Proof.
  destruct s as [|a w t s]; intros Hs; [destruct i; reflexivity|]; cbn [knth klist].
  rewrite nth_error_map, (spnth_spec (SCons w t s) i Hs); reflexivity.
Qed.

(** ** Canonicity *)

Lemma kweights_krebase d s : kweights (krebase d s) = kweights s.
Proof. destruct s; reflexivity. Qed.

Lemma kweights_klift d s : kweights (klift d s) = kweights s.
Proof. destruct s; reflexivity. Qed.

Lemma kshape_krebase m s : kshape s -> kshape (krebase m s).
Proof. destruct s; exact (fun H => H). Qed.

Lemma kshape_klift d s : kshape s -> kshape (klift d s).
Proof. destruct s; exact (fun H => H). Qed.

Lemma klength_weights s : klength s = fold_right Nat.add 0 (kweights s).
Proof.
  destruct s as [|a w t s]; [reflexivity|]; cbn [klength kweights fold_right]; f_equal.
  induction s; cbn; congruence.
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

Lemma spcanonical s1 : forall s2,
  spinv s1 -> spinv s2 -> spshape s1 -> spshape s2 -> spweights s1 = spweights s2 ->
  splist s1 = splist s2 -> s1 = s2.
Proof.
  induction s1 as [|w1 t1 s1 IH]; intros [|w2 t2 s2] H1 H2 S1 S2 Hw E; try discriminate; [reflexivity|].
  injection Hw as <- Hw; destruct H1 as [Ht1 Hs1], H2 as [Ht2 Hs2], S1 as [St1 Ss1], S2 as [St2 Ss2].
  cbn [splist] in E; apply app_inj_length in E as [Et Es];
    [|rewrite (ktlength _ _ St1), (ktlength _ _ St2); reflexivity].
  f_equal; [apply (ktcanonical _ _ w1); assumption|apply IH; assumption].
Qed.

Theorem kcanonical s1 s2 : kgood s1 -> kgood s2 -> klist s1 = klist s2 -> s1 = s2.
Proof.
  intros G1 G2 E.
  assert (Hw : kweights s1 = kweights s2).
  { destruct G1 as [_ [S1 C1]], G2 as [_ [S2 C2]]; rewrite C1, C2, !klength_spec, E by assumption.
    reflexivity. }
  destruct G1 as [H1 [S1 _]], G2 as [H2 [S2 _]].
  destruct s1 as [|a1 w1 t1 s1], s2 as [|a2 w2 t2 s2]; try discriminate; [reflexivity|].
  assert (Ha : a1 = a2).
  { apply counts_ext; [apply H1|apply H2|]; intro k.
    transitivity (lmin (klist (KSeq a1 w1 t1 s1)) k); [apply (kinv_ann _ H1)|].
    rewrite E; symmetry; apply (kinv_ann _ H2). }
  subst a2; cbn [klist] in E.
  apply (map_inj_ok (unshift a1) eok) in E;
    [|intros x y Hx Hy; apply unshift_inj; assumption
     |apply (kinv_cell_ok _ _ _ _ H1)|apply (kinv_cell_ok _ _ _ _ H2)].
  assert (Hs : SCons w1 t1 s1 = SCons w2 t2 s2)
    by (apply spcanonical; try assumption; apply kinv_spine with a1; assumption).
  injection Hs as -> -> ->; reflexivity.
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
  destruct (cget a k) as [x|], (lmin (splist (SCons w t s')) k) as [n|]; cbn in Ha |- *;
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

    [kdrop s i] is [s] without its first [i] elements: the trees before the
    one holding index [i] are skipped, and inside that tree the path to [i]
    is followed, keeping the right subtrees it passes as new trees.  The
    base is then recomputed over the O(log n) trees left.  The result is the
    sequence [kcons] builds. *)

Fixpoint ktdrop (w : nat) (t : ktree) (i : nat) (acc : kspine) : kspine :=
  match t with
  | KLeaf _ => match i with 0 => SCons 1 t acc | S _ => acc end
  | KNode a x l r =>
      match i with
      | 0 => SCons w t acc
      | S j =>
          let w' := Nat.div2 w in
          if Nat.ltb j w' then ktdrop w' (ktlift a l) j (SCons w' (ktlift a r) acc)
          else ktdrop w' (ktlift a r) (j - w') acc
      end
  end.

Fixpoint spdrop (s : kspine) (i : nat) : kspine :=
  match s with
  | SNil => SNil
  | SCons w t s' => if Nat.ltb i w then ktdrop w t i s' else spdrop s' (i - w)
  end.

Definition kdrop (s : kseq) (i : nat) : kseq :=
  match s with KNil => KNil | KSeq a w t s' => klift a (kmk (spdrop (SCons w t s') i)) end.

Lemma ktdrop_spec w t : ktshape w t -> ktinv t -> forall i acc, i < w -> spinv acc ->
  spinv (ktdrop w t i acc) /\ splist (ktdrop w t i acc) = skipn i (ktlist t) ++ splist acc.
Proof.
  revert t; induction w as [w IH] using (well_founded_induction lt_wf).
  intros [x|a x l r] Hw Ht i acc Hi Hacc.
  - cbn in Hw; subst w; destruct i as [|i]; [|lia]; cbn [ktdrop].
    split; [split; assumption|reflexivity].
  - destruct Hw as [w' [-> [Hl Hr]]]; destruct i as [|j].
    + cbn [ktdrop]; split; [split; assumption|reflexivity].
    + destruct Ht as [_ [_ [_ [Tl Tr]]]].
      assert (Tl' : ktinv (ktlift a l)) by (apply ktinv_ktlift, Tl).
      assert (Tr' : ktinv (ktlift a r)) by (apply ktinv_ktlift, Tr).
      cbn [ktdrop ktlist]; rewrite div2_succ_double, skipn_map; cbn [skipn].
      destruct (Nat.ltb_spec j w') as [Hj|Hj].
      * destruct (IH w' ltac:(lia) _ (ktshape_ktlift a w' l Hl) Tl' j (SCons w' (ktlift a r) acc) Hj
                   (conj Tr' Hacc)) as [I E].
        split; [exact I|]; rewrite E; cbn [splist]; rewrite !ktlist_ktlift by assumption.
        rewrite skipn_app, (ktlength _ _ Hl), skipn_map, !map_app, <- app_assoc.
        replace (j - w') with 0 by lia; reflexivity.
      * destruct (IH w' ltac:(lia) _ (ktshape_ktlift a w' r Hr) Tr' (j - w') acc ltac:(lia) Hacc) as [I E].
        split; [exact I|]; rewrite E, ktlist_ktlift by assumption.
        rewrite skipn_app, (ktlength _ _ Hl), (skipn_all2 (ktlist l)) by (rewrite (ktlength _ _ Hl); lia).
        rewrite skipn_map; reflexivity.
Qed.

Lemma spdrop_spec s : spinv s -> spshape s -> forall i,
  spinv (spdrop s i) /\ splist (spdrop s i) = skipn i (splist s).
Proof.
  induction s as [|w t s IH]; intros Hs Hsh i; [split; [exact I|destruct i; reflexivity]|].
  destruct Hs as [Ht Hs], Hsh as [Hw Hsh]; cbn [spdrop splist].
  destruct (Nat.ltb_spec i w) as [Hi|Hi].
  - destruct (ktdrop_spec w t Hw Ht i s Hi Hs) as [I E]; split; [exact I|rewrite E, skipn_app].
    rewrite (ktlength _ _ Hw); replace (i - w) with 0 by lia; reflexivity.
  - destruct (IH Hs Hsh (i - w)) as [I E]; split; [exact I|rewrite E, skipn_app].
    rewrite (ktlength _ _ Hw), (skipn_all2 (ktlist t)) by (rewrite (ktlength _ _ Hw); exact Hi); reflexivity.
Qed.

Lemma ktdrop_shape w t : ktshape w t -> forall i acc, i < w -> spshape acc -> spshape (ktdrop w t i acc).
Proof.
  revert t; induction w as [w IH] using (well_founded_induction lt_wf).
  intros [x|a x l r] Hw i acc Hi Hacc.
  - cbn in Hw; subst w; destruct i as [|i]; [|lia]; split; [reflexivity|exact Hacc].
  - destruct i as [|j]; [split; [exact Hw|exact Hacc]|].
    destruct Hw as [w' [-> [Hl Hr]]]; cbn [ktdrop]; rewrite div2_succ_double.
    destruct (Nat.ltb_spec j w') as [Hj|Hj].
    + apply IH; [lia|apply ktshape_ktlift, Hl|exact Hj|].
      split; [apply ktshape_ktlift, Hr|exact Hacc].
    + apply IH; [lia|apply ktshape_ktlift, Hr|lia|exact Hacc].
Qed.

Lemma spdrop_shape s : spshape s -> forall i, spshape (spdrop s i).
Proof.
  induction s as [|w t s IH]; intros Hsh i; [exact I|].
  destruct Hsh as [Hw Hsh]; cbn [spdrop]; destruct (Nat.ltb_spec i w) as [Hi|Hi];
    [apply ktdrop_shape; assumption|apply IH, Hsh].
Qed.

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
  spweights (ktdrop w t i acc) = Nat.iter i wtail (w :: spweights acc).
Proof.
  revert t; induction w as [w IH] using (well_founded_induction lt_wf).
  intros [x|a x l r] Hw i acc Hi.
  - cbn in Hw; subst w; destruct i as [|i]; [reflexivity|lia].
  - destruct i as [|j]; [reflexivity|].
    destruct Hw as [w' [-> [Hl Hr]]]; cbn [ktdrop]; rewrite div2_succ_double.
    rewrite iter_succ_r, wtail_node by apply (ktshape_pos _ _ Hl).
    destruct (Nat.ltb_spec j w') as [Hj|Hj].
    + rewrite (IH w' ltac:(lia) _ (ktshape_ktlift a _ l Hl) j _ Hj); reflexivity.
    + rewrite (IH w' ltac:(lia) _ (ktshape_ktlift a _ r Hr) (j - w') _ ltac:(lia)).
      rewrite <- (wtail_tree _ _ (w' :: spweights acc) Hl) at 1; rewrite <- iter_add; f_equal; lia.
Qed.

Lemma spdrop_weights s : spshape s -> forall i, spweights (spdrop s i) = Nat.iter i wtail (spweights s).
Proof.
  induction s as [|w t s IH]; intros Hsh i.
  - cbn [spdrop spweights]; induction i as [|i IHi]; [reflexivity|].
    change (Nat.iter (S i) wtail []) with (wtail (Nat.iter i wtail [])); rewrite <- IHi; reflexivity.
  - destruct Hsh as [Hw Hsh]; cbn [spdrop spweights].
    destruct (Nat.ltb_spec i w) as [Hi|Hi]; [apply ktdrop_weights; assumption|].
    rewrite IH by exact Hsh; rewrite <- (wtail_tree _ _ (spweights s) Hw) at 1.
    rewrite <- iter_add; f_equal; lia.
Qed.

Theorem kgood_kdrop s i : kgood s -> kgood (kdrop s i) /\ klist (kdrop s i) = skipn i (klist s).
Proof.
  intros [Hs [Hsh Hc]]; destruct s as [|a w t s']; [split; [apply kgood_nil|destruct i; reflexivity]|].
  pose proof (kinv_spine _ _ _ _ Hs) as Hsp; cbn [kdrop].
  destruct (spdrop_spec _ Hsp Hsh i) as [I E].
  destruct (kmk_spec _ I) as [I2 E2].
  assert (E3 : klist (klift a (kmk (spdrop (SCons w t s') i))) = skipn i (klist (KSeq a w t s'))).
  { rewrite klist_klift, E2, E by exact I2; cbn [klist]; rewrite skipn_map; reflexivity. }
  split; [|exact E3].
  split; [apply kinv_klift, I2|split; [apply kshape_klift, kshape_kmk, spdrop_shape, Hsh|]].
  unfold kcanon in *; rewrite kweights_klift, kweights_kmk, spdrop_weights by exact Hsh.
  change (spweights (SCons w t s')) with (kweights (KSeq a w t s')); rewrite Hc, wtail_iter_cweights.
  rewrite !klength_spec, E3, length_skipn
    by (exact Hsh || apply kshape_klift, kshape_kmk, spdrop_shape, Hsh); reflexivity.
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


Fixpoint spinvb (s : kspine) : bool :=
  match s with SNil => true | SCons _ t s' => ktinvb t && spinvb s' end.

Lemma spinvb_spec s : spinvb s = true <-> spinv s.
Proof.
  induction s as [|w t s IH]; cbn [spinvb spinv]; [split; [intros _; exact I|reflexivity]|].
  rewrite andb_true_iff, ktinvb_spec, IH; reflexivity.
Qed.

Definition kinvb (s : kseq) : bool :=
  match s with
  | KNil => true
  | KSeq a _ t s' => cwfb a && ceqb a (lminc (klist s)) && ktinvb t && spinvb s'
  end.

Lemma kinvb_spec s : kinvb s = true <-> kinv s.
Proof.
  destruct s as [|a w t s]; cbn [kinvb kinv ksann].
  - split; [intros _; split; [intro k; reflexivity|exact I]|reflexivity].
  - rewrite !andb_true_iff, cwfb_spec, ktinvb_spec, spinvb_spec.
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


Fixpoint spshapeb (s : kspine) : bool :=
  match s with SNil => true | SCons w t s' => ktshapeb w t && spshapeb s' end.

Lemma spshapeb_spec s : spshapeb s = true <-> spshape s.
Proof.
  induction s as [|w t s IH]; cbn [spshapeb spshape]; [split; [intros _; exact I|reflexivity]|].
  rewrite andb_true_iff, ktshapeb_spec, IH; reflexivity.
Qed.

Definition kshapeb (s : kseq) : bool :=
  match s with KNil => true | KSeq _ w t s' => ktshapeb w t && spshapeb s' end.

Lemma kshapeb_spec s : kshapeb s = true <-> kshape s.
Proof.
  destruct s as [|a w t s]; cbn [kshapeb kshape]; [split; [intros _; exact I|reflexivity]|].
  rewrite andb_true_iff, ktshapeb_spec, spshapeb_spec; reflexivity.
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
Arguments kspine : clear implicits.
Arguments kseq : clear implicits.
