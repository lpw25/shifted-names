(** * Skew sequences with weakening counts

    Sequences that grow at the front, as in Okasaki's skew-binary
    random-access lists: a spine of cells, each holding a complete binary
    tree whose size is [2ᵏ⁺¹ − 1], with an element at every tree node.
    [cons] is O(1) (it builds at most one node from the two front trees),
    and indexing is O(log n).

    Every tree node and spine cell carries a count map: how far the uses of
    everything below it start above its parent's base (Counts.v).  Elements
    are stored relative to the base of the node that holds them.  The
    sequence is generic in its elements, which only need to say what they
    use and how to move between bases.

    Canonicity: [cons] is the only way to build a sequence, so a sequence
    built by [cons] (one that satisfies [canon]) is determined by the list
    it denotes. *)

From Stdlib Require Import PArith Arith Lia List Bool.
From ShiftedNames.Core Require Import Trie Counts.
Import ListNotations.

Lemma map_id_in {A} (f : A -> A) l : (forall x, In x l -> f x = x) -> map f l = l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|]; cbn [map].
  rewrite (H x (or_introl eq_refl)), IH; [reflexivity|].
  intros y Hy; apply H; right; exact Hy.
Qed.

(** ** What elements must provide *)

Section Skew.

Context {X : Type}.

(** What an element uses, relative to its own base. *)
Variable uses : X -> counts.

(** [shift d x] expresses [x] relative to a base [d] higher; [unshift d x]
    relative to a base [d] lower. *)
Variables shift unshift : counts -> X -> X.

(** Well-formed elements. *)
Variable ok : X -> Prop.

Hypothesis ok_shift : forall d x, ok x -> ok (shift d x).
Hypothesis ok_unshift : forall d x, ok x -> ok (unshift d x).
Hypothesis shift_unshift : forall d x, ok x -> shift d (unshift d x) = x.
Hypothesis unshift_shift : forall d x, ok x -> cle d (uses x) -> unshift d (shift d x) = x.
Hypothesis unshift_unshift : forall d1 d2 x, unshift d1 (unshift d2 x) = unshift (cplus d1 d2) x.
Hypothesis unshift_ext : forall d d' x,
  (forall k, cget (uses x) k <> None -> dval d k = dval d' k) -> unshift d x = unshift d' x.
Hypothesis uses_unshift : forall d x k,
  cget (uses (unshift d x)) k = oadd (cget d k) (cget (uses x) k).
Hypothesis uses_shift : forall d x k,
  cget (uses (shift d x)) k = osub (cget (uses x) k) (cget d k).

(** ** Representation *)

Inductive tree : Type :=
| TLeaf (x : X)
| TNode (a : counts) (x : X) (l r : tree).

Inductive seq : Type :=
| SNil
| SCons (a : counts) (w : nat) (t : tree) (s : seq).

Definition tann (t : tree) : counts :=
  match t with TLeaf x => uses x | TNode a _ _ _ => a end.

Definition sann (s : seq) : counts :=
  match s with SNil => cnone | SCons a _ _ _ => a end.

(** The elements denoted, relative to the parent's base (trees in
    preorder, so every subtree is a contiguous range). *)
Fixpoint tlist (t : tree) : list X :=
  match t with
  | TLeaf x => [x]
  | TNode a x l r => map (unshift a) (x :: tlist l ++ tlist r)
  end.

Fixpoint slist (s : seq) : list X :=
  match s with
  | SNil => []
  | SCons a _ t s' => map (unshift a) (tlist t ++ slist s')
  end.

(** Moving a whole tree or sequence to a base [d] higher or lower: only the
    top changes. *)
Definition trebase (d : counts) (t : tree) : tree :=
  match t with TLeaf x => TLeaf (shift d x) | TNode a x l r => TNode (csub a d) x l r end.

Definition tlift (d : counts) (t : tree) : tree :=
  match t with TLeaf x => TLeaf (unshift d x) | TNode a x l r => TNode (cadd d a) x l r end.

Definition srebase (d : counts) (s : seq) : seq :=
  match s with SNil => SNil | SCons a w t s' => SCons (csub a d) w t s' end.

Definition slift (d : counts) (s : seq) : seq :=
  match s with SNil => SNil | SCons a w t s' => SCons (cadd d a) w t s' end.

(** Building a node: its counts are the minimum of what is below. *)
Definition tnode (x : X) (t1 t2 : tree) : tree :=
  let m := cmin (uses x) (cmin (tann t1) (tann t2)) in
  TNode m (shift m x) (trebase m t1) (trebase m t2).

Definition scell (w : nat) (t : tree) (s : seq) : seq :=
  let m := cmin (tann t) (sann s) in
  SCons m w (trebase m t) (srebase m s).

Definition cons (x : X) (s : seq) : seq :=
  match s with
  | SCons a1 w1 t1 (SCons a2 w2 t2 s') =>
      if Nat.eqb w1 w2
      then scell (S (w1 + w2)) (tnode x (tlift a1 t1) (tlift a1 (tlift a2 t2)))
                 (slift a1 (slift a2 s'))
      else scell 1 (TLeaf x) s
  | _ => scell 1 (TLeaf x) s
  end.

Definition of_list (l : list X) : seq := fold_right cons SNil l.

(** Indexing; [w] is the size of the tree. *)
Fixpoint tnth (w : nat) (t : tree) (i : nat) : option X :=
  match t with
  | TLeaf x => match i with 0 => Some x | S _ => None end
  | TNode a x l r =>
      let w' := Nat.div2 w in
      match i with
      | 0 => Some (unshift a x)
      | S j => option_map (unshift a) (if Nat.ltb j w' then tnth w' l j else tnth w' r (j - w'))
      end
  end.

Fixpoint snth (s : seq) (i : nat) : option X :=
  match s with
  | SNil => None
  | SCons a w t s' => option_map (unshift a) (if Nat.ltb i w then tnth w t i else snth s' (i - w))
  end.

Fixpoint slength (s : seq) : nat :=
  match s with SNil => 0 | SCons _ w _ s' => w + slength s' end.

(** ** Invariants *)

(** The minimum use of a list of elements (with [None] as ∞). *)
Definition lmin (l : list X) (k : positive) : option nat :=
  fold_right (fun e acc => omin (cget (uses e) k) acc) None l.

(** Every node's counts are the minimum over what it denotes, and stored
    elements are well formed. *)
Fixpoint tinv (t : tree) : Prop :=
  (forall k, cget (tann t) k = lmin (tlist t) k)
  /\ match t with
     | TLeaf x => ok x
     | TNode _ x l r => ok x /\ tinv l /\ tinv r
     end.

Fixpoint sinv (s : seq) : Prop :=
  (forall k, cget (sann s) k = lmin (slist s) k)
  /\ match s with
     | SNil => True
     | SCons _ _ t s' => tinv t /\ sinv s'
     end.

(** Sizes: a tree of size [w] has children of size [div2 w]. *)
Fixpoint tshape (w : nat) (t : tree) : Prop :=
  match t with
  | TLeaf _ => w = 1
  | TNode _ _ l r => exists w', w = S (w' + w') /\ tshape w' l /\ tshape w' r
  end.

Fixpoint sshape (s : seq) : Prop :=
  match s with
  | SNil => True
  | SCons _ w t s' => tshape w t /\ sshape s'
  end.

(** Built by [cons]. *)
Definition canon (s : seq) : Prop := s = of_list (slist s).

(** ** Lemmas about minima *)

Lemma lmin_app l1 l2 k : lmin (l1 ++ l2) k = omin (lmin l1 k) (lmin l2 k).
Proof.
  induction l1 as [|e l1 IH]; [reflexivity|].
  change (omin (cget (uses e) k) (lmin (l1 ++ l2) k)
          = omin (omin (cget (uses e) k) (lmin l1 k)) (lmin l2 k)).
  rewrite IH; destruct (cget (uses e) k), (lmin l1 k), (lmin l2 k); cbn; f_equal; lia.
Qed.

Lemma lmin_unshift d l k : lmin (map (unshift d) l) k = oadd (cget d k) (lmin l k).
Proof.
  induction l as [|e l IH]; [destruct (cget d k); reflexivity|].
  change (omin (cget (uses (unshift d e)) k) (lmin (map (unshift d) l) k)
          = oadd (cget d k) (omin (cget (uses e) k) (lmin l k))).
  rewrite IH, uses_unshift, oadd_omin; reflexivity.
Qed.

Lemma lmin_shift d l k : lmin (map (shift d) l) k = osub (lmin l k) (cget d k).
Proof.
  induction l as [|e l IH]; [reflexivity|].
  change (omin (cget (uses (shift d e)) k) (lmin (map (shift d) l) k)
          = osub (omin (cget (uses e) k) (lmin l k)) (cget d k)).
  rewrite IH, uses_shift, osub_omin; reflexivity.
Qed.

Lemma lmin_le l e k m : In e l -> cget (uses e) k = Some m -> exists n, lmin l k = Some n /\ n <= m.
Proof.
  induction l as [|e' l IH]; [intros []|].
  change (lmin (e' :: l) k) with (omin (cget (uses e') k) (lmin l k)).
  intros [->|Hin] Hm.
  - rewrite Hm; destruct (lmin l k) as [p|]; cbn [omin]; eexists; (split; [reflexivity|lia]).
  - destruct (IH Hin Hm) as [n [Hn Hle]]; rewrite Hn.
    destruct (cget (uses e') k) as [p|]; cbn [omin]; eexists; (split; [reflexivity|lia]).
Qed.

Lemma lmin_some l e k : In e l -> cget (uses e) k <> None -> lmin l k <> None.
Proof.
  intros Hin Hu; destruct (cget (uses e) k) as [m|] eqn:E; [|contradiction].
  destruct (lmin_le l e k m Hin E) as [n [Hn _]]; congruence.
Qed.

Lemma cle_lmin d l e : (forall k, cget d k = lmin l k) -> In e l -> cle d (uses e).
Proof.
  intros Hd Hin k n m Hn Hm; rewrite Hd in Hn.
  destruct (lmin_le l e k m Hin Hm) as [n' [Hn' Hle]]; congruence.
Qed.

Lemma cle_cmin_l a b : cle (cmin a b) a.
Proof.
  intros k n m; rewrite cget_cmin; destruct (cget a k), (cget b k); cbn;
    intros [= <-] [= <-]; lia.
Qed.

Lemma cle_cmin_r a b : cle (cmin a b) b.
Proof.
  intros k n m; rewrite cget_cmin; destruct (cget a k), (cget b k); cbn;
    intros [= <-] [= <-]; lia.
Qed.

Lemma cle_trans a b c : cle a b -> (forall k, cget a k <> None -> cget b k <> None) -> cle b c -> cle a c.
Proof.
  intros H1 Hd H2 k n m Ha Hc.
  destruct (cget b k) as [p|] eqn:Eb; [|exfalso; apply (Hd k); congruence].
  specialize (H1 k n p Ha Eb); specialize (H2 k p m Eb Hc); lia.
Qed.

(** ** Trees *)

Lemma tinv_ann t : tinv t -> forall k, cget (tann t) k = lmin (tlist t) k.
Proof. destruct t; cbn [tinv]; tauto. Qed.

Lemma tinv_ok t : tinv t -> forall e, In e (tlist t) -> ok e.
Proof.
  induction t as [x|a x l IHl r IHr]; cbn [tinv tlist].
  - intros [_ H] e [<-|[]]; exact H.
  - intros [_ [Hx [Hl Hr]]] e Hin; apply in_map_iff in Hin as [e' [<- Hin]].
    apply ok_unshift; destruct Hin as [<-|Hin]; [exact Hx|].
    apply in_app_or in Hin as [Hin|Hin]; [apply IHl|apply IHr]; assumption.
Qed.

Lemma lmin_single e k : lmin [e] k = cget (uses e) k.
Proof. cbn; destruct (cget (uses e) k); reflexivity. Qed.

(** A minimum below [a] is below every element counted in [a]. *)
Lemma cle_mem m a L e :
  cle m a -> (forall k, cget a k = lmin L k) -> In e L -> cle m (uses e).
Proof.
  intros Hm Ha Hin k n q Hn Hq.
  destruct (lmin_le L e k q Hin Hq) as [p [Hp Hle]].
  rewrite <- Ha in Hp; specialize (Hm k n p Hn Hp); lia.
Qed.

Lemma cle_min3_1 u a b : cle (cmin u (cmin a b)) u.
Proof.
  intros k n m; rewrite !cget_cmin; destruct (cget u k), (cget a k), (cget b k); cbn;
    intros [= <-] [= <-]; lia.
Qed.

Lemma cle_min3_2 u a b : cle (cmin u (cmin a b)) a.
Proof.
  intros k n m; rewrite !cget_cmin; destruct (cget u k), (cget a k), (cget b k); cbn;
    intros [= <-] [= <-]; lia.
Qed.

Lemma cle_min3_3 u a b : cle (cmin u (cmin a b)) b.
Proof.
  intros k n m; rewrite !cget_cmin; destruct (cget u k), (cget a k), (cget b k); cbn;
    intros [= <-] [= <-]; lia.
Qed.

(** ** Moving lists of elements between bases *)

Section Lists.

Variables (a : counts) (L : list X).
Hypothesis Ha : forall k, cget a k = lmin (map (unshift a) L) k.
Hypothesis Hok : forall e, In e L -> ok e.

Lemma uses_below e k : In e L -> cget (uses e) k <> None -> cget a k <> None.
Proof.
  intros Hin Hu; rewrite Ha; apply (lmin_some _ (unshift a e)); [apply in_map, Hin|].
  rewrite uses_unshift; intro H; apply oadd_none in H; contradiction.
Qed.

(** Raising the base of the top by [m]. *)
Lemma rebase_list m :
  cle m a -> map (unshift (csub a m)) L = map (shift m) (map (unshift a) L).
Proof.
  intros Hm; rewrite map_map; apply map_ext_in; intros e Hin.
  assert (unshift a e = unshift m (unshift (csub a m) e)) as ->.
  { rewrite unshift_unshift; apply unshift_ext; intros k Hk.
    rewrite dval_cplus; unfold dval; rewrite cget_csub.
    destruct (cget a k) as [p|] eqn:E; [|exfalso; apply (uses_below e k Hin Hk), E].
    destruct (cget m k) as [n|] eqn:F; cbn; [specialize (Hm k n p F E)|]; lia. }
  symmetry; apply shift_unshift, ok_unshift, Hok, Hin.
Qed.

(** Lowering the base of the top by [d]. *)
Lemma lift_list d : map (unshift (cadd d a)) L = map (unshift d) (map (unshift a) L).
Proof.
  rewrite map_map; apply map_ext_in; intros e Hin; rewrite unshift_unshift.
  apply unshift_ext; intros k Hk; rewrite dval_cplus; unfold dval; rewrite cget_cadd.
  destruct (cget a k) as [p|] eqn:E; [|exfalso; apply (uses_below e k Hin Hk), E].
  destruct (cget d k); reflexivity.
Qed.

End Lists.

(** ** Trees *)

Lemma tinv_node_ok a x l r :
  tinv (TNode a x l r) -> forall e, In e (x :: tlist l ++ tlist r) -> ok e.
Proof.
  intros [_ [Hx [Hl Hr]]] e [<-|Hin]; [exact Hx|].
  apply in_app_or in Hin as [Hin|Hin]; [apply (tinv_ok l Hl)|apply (tinv_ok r Hr)]; exact Hin.
Qed.

Lemma tlist_trebase m t : tinv t -> cle m (tann t) -> tlist (trebase m t) = map (shift m) (tlist t).
Proof.
  destruct t as [x|a x l r]; intros Ht Hm; [reflexivity|].
  apply (rebase_list a); [apply (tinv_ann _ Ht)|apply (tinv_node_ok _ _ _ _ Ht)|exact Hm].
Qed.

Lemma tinv_trebase m t : tinv t -> cle m (tann t) -> tinv (trebase m t).
Proof.
  intros Ht Hm; pose proof (tlist_trebase m t Ht Hm) as Hl.
  destruct t as [x|a x l r]; cbn [trebase tinv tann] in *.
  - destruct Ht as [_ Hx]; split; [intro k; cbn [tlist]; rewrite lmin_single; reflexivity|apply ok_shift, Hx].
  - destruct Ht as [Ha Hs]; split; [|exact Hs]; intro k.
    rewrite Hl, lmin_shift, cget_csub, Ha; reflexivity.
Qed.

Lemma tlist_tlift d t : tinv t -> tlist (tlift d t) = map (unshift d) (tlist t).
Proof.
  destruct t as [x|a x l r]; intros Ht; [reflexivity|].
  apply (lift_list a), (tinv_ann _ Ht).
Qed.

Lemma tinv_tlift d t : tinv t -> tinv (tlift d t).
Proof.
  intros Ht; pose proof (tlist_tlift d t Ht) as Hl.
  destruct t as [x|a x l r]; cbn [tlift tinv tann] in *.
  - destruct Ht as [_ Hx]; split; [intro k; cbn [tlist]; rewrite lmin_single; reflexivity|apply ok_unshift, Hx].
  - destruct Ht as [Ha Hs]; split; [|exact Hs]; intro k.
    rewrite Hl, lmin_unshift, cget_cadd, Ha; reflexivity.
Qed.

Lemma tlist_tnode x t1 t2 :
  ok x -> tinv t1 -> tinv t2 -> tlist (tnode x t1 t2) = x :: tlist t1 ++ tlist t2.
Proof.
  intros Hx H1 H2; unfold tnode; set (m := cmin (uses x) (cmin (tann t1) (tann t2))).
  cbn [tlist]; rewrite !tlist_trebase by (assumption || apply cle_min3_2 || apply cle_min3_3).
  cbn [map]; rewrite map_app, !map_map.
  f_equal; [apply unshift_shift; [exact Hx|apply cle_min3_1]|f_equal; apply map_id_in].
  - intros e Hin; apply unshift_shift; [apply (tinv_ok _ H1 _ Hin)|].
    apply (cle_mem m (tann t1) (tlist t1)); [apply cle_min3_2|apply tinv_ann, H1|exact Hin].
  - intros e Hin; apply unshift_shift; [apply (tinv_ok _ H2 _ Hin)|].
    apply (cle_mem m (tann t2) (tlist t2)); [apply cle_min3_3|apply tinv_ann, H2|exact Hin].
Qed.

Lemma tinv_tnode x t1 t2 : ok x -> tinv t1 -> tinv t2 -> tinv (tnode x t1 t2).
Proof.
  intros Hx H1 H2; pose proof (tlist_tnode x t1 t2 Hx H1 H2) as Hl.
  unfold tnode in *; set (m := cmin (uses x) (cmin (tann t1) (tann t2))) in *.
  cbn [tinv tann]; split; [|split; [apply ok_shift, Hx|split; apply tinv_trebase]];
    try assumption; try apply cle_min3_2; try apply cle_min3_3.
  intro k; rewrite Hl; cbn [lmin fold_right]; fold (lmin (tlist t1 ++ tlist t2) k).
  rewrite lmin_app, <- !tinv_ann by assumption; unfold m; rewrite !cget_cmin; reflexivity.
Qed.

(** ** Sequences *)

Lemma sinv_ann s : sinv s -> forall k, cget (sann s) k = lmin (slist s) k.
Proof. destruct s; cbn [sinv]; tauto. Qed.

Lemma sinv_ok s : sinv s -> forall e, In e (slist s) -> ok e.
Proof.
  induction s as [|a w t s IH]; cbn [sinv slist]; [intros _ _ []|].
  intros [_ [Ht Hs]] e Hin; apply in_map_iff in Hin as [e' [<- Hin]]; apply ok_unshift.
  apply in_app_or in Hin as [Hin|Hin]; [apply (tinv_ok t Ht)|apply IH]; assumption.
Qed.

Lemma sinv_cell_ok a w t s :
  sinv (SCons a w t s) -> forall e, In e (tlist t ++ slist s) -> ok e.
Proof.
  intros [_ [Ht Hs]] e Hin.
  apply in_app_or in Hin as [Hin|Hin]; [apply (tinv_ok t Ht)|apply (sinv_ok s Hs)]; exact Hin.
Qed.

Lemma slist_srebase m s : sinv s -> cle m (sann s) -> slist (srebase m s) = map (shift m) (slist s).
Proof.
  destruct s as [|a w t s]; intros Hs Hm; [reflexivity|].
  apply (rebase_list a); [apply (sinv_ann _ Hs)|apply (sinv_cell_ok _ _ _ _ Hs)|exact Hm].
Qed.

Lemma sinv_srebase m s : sinv s -> cle m (sann s) -> sinv (srebase m s).
Proof.
  intros Hs Hm; pose proof (slist_srebase m s Hs Hm) as Hl.
  destruct s as [|a w t s]; [exact Hs|]; cbn [srebase sinv sann] in *.
  destruct Hs as [Ha Hs]; split; [|exact Hs]; intro k.
  rewrite Hl, lmin_shift, cget_csub, Ha; reflexivity.
Qed.

Lemma slist_slift d s : sinv s -> slist (slift d s) = map (unshift d) (slist s).
Proof.
  destruct s as [|a w t s]; intros Hs; [reflexivity|].
  apply (lift_list a), (sinv_ann _ Hs).
Qed.

Lemma sinv_slift d s : sinv s -> sinv (slift d s).
Proof.
  intros Hs; pose proof (slist_slift d s Hs) as Hl.
  destruct s as [|a w t s]; [exact Hs|]; cbn [slift sinv sann] in *.
  destruct Hs as [Ha Hs]; split; [|exact Hs]; intro k.
  rewrite Hl, lmin_unshift, cget_cadd, Ha; reflexivity.
Qed.

Lemma slist_scell w t s : tinv t -> sinv s -> slist (scell w t s) = tlist t ++ slist s.
Proof.
  intros Ht Hs; unfold scell; set (m := cmin (tann t) (sann s)); cbn [slist].
  rewrite tlist_trebase, slist_srebase by (assumption || apply cle_cmin_l || apply cle_cmin_r).
  rewrite map_app, !map_map; f_equal; apply map_id_in.
  - intros e Hin; apply unshift_shift; [apply (tinv_ok _ Ht _ Hin)|].
    apply (cle_mem m (tann t) (tlist t)); [apply cle_cmin_l|apply tinv_ann, Ht|exact Hin].
  - intros e Hin; apply unshift_shift; [apply (sinv_ok _ Hs _ Hin)|].
    apply (cle_mem m (sann s) (slist s)); [apply cle_cmin_r|apply sinv_ann, Hs|exact Hin].
Qed.

Lemma sinv_scell w t s : tinv t -> sinv s -> sinv (scell w t s).
Proof.
  intros Ht Hs; pose proof (slist_scell w t s Ht Hs) as Hl.
  unfold scell in *; set (m := cmin (tann t) (sann s)) in *.
  cbn [sinv sann]; split; [|split; [apply tinv_trebase|apply sinv_srebase]];
    try assumption; try apply cle_cmin_l; try apply cle_cmin_r.
  intro k; rewrite Hl, lmin_app, <- tinv_ann, <- sinv_ann by assumption.
  unfold m; rewrite cget_cmin; reflexivity.
Qed.

(** ** [cons] *)

Theorem cons_spec x s : ok x -> sinv s -> slist (cons x s) = x :: slist s /\ sinv (cons x s).
Proof.
  intros Hx Hs.
  assert (Hleaf : tinv (TLeaf x)) by (split; [intro k; cbn [tlist]; rewrite lmin_single; reflexivity|exact Hx]).
  assert (Hdef : slist (scell 1 (TLeaf x) s) = x :: slist s /\ sinv (scell 1 (TLeaf x) s))
    by (split; [rewrite slist_scell by assumption; reflexivity|apply sinv_scell; assumption]).
  destruct s as [|a1 w1 t1 [|a2 w2 t2 s']]; cbn [cons]; try exact Hdef.
  destruct (Nat.eqb w1 w2); [|exact Hdef].
  destruct Hs as [Ha1 [Ht1 [Ha2 [Ht2 Hs']]]].
  assert (T1 : tinv (tlift a1 t1)) by (apply tinv_tlift, Ht1).
  assert (T2 : tinv (tlift a1 (tlift a2 t2))) by (apply tinv_tlift, tinv_tlift, Ht2).
  assert (S' : sinv (slift a1 (slift a2 s'))) by (apply sinv_slift, sinv_slift, Hs').
  assert (T : tinv (tnode x (tlift a1 t1) (tlift a1 (tlift a2 t2)))) by (apply tinv_tnode; assumption).
  split; [|apply sinv_scell; assumption].
  rewrite slist_scell, tlist_tnode, !tlist_tlift, !slist_slift by (assumption || apply tinv_tlift, Ht2 || apply sinv_slift, Hs').
  cbn [slist]; rewrite !map_app; cbn [app]; rewrite <- app_assoc; reflexivity.
Qed.

Lemma tshape_trebase m w t : tshape w t -> tshape w (trebase m t).
Proof. destruct t; exact (fun H => H). Qed.

Lemma tshape_tlift d w t : tshape w t -> tshape w (tlift d t).
Proof. destruct t; exact (fun H => H). Qed.

Lemma sshape_srebase m s : sshape s -> sshape (srebase m s).
Proof. destruct s; exact (fun H => H). Qed.

Lemma sshape_slift d s : sshape s -> sshape (slift d s).
Proof. destruct s; exact (fun H => H). Qed.

Lemma sshape_cons x s : sshape s -> sshape (cons x s).
Proof.
  intros Hs.
  assert (Hdef : sshape (scell 1 (TLeaf x) s))
    by (split; [reflexivity|apply sshape_srebase, Hs]).
  destruct s as [|a1 w1 t1 [|a2 w2 t2 s']]; cbn [cons]; try exact Hdef.
  destruct (Nat.eqb_spec w1 w2) as [<-|]; [|exact Hdef].
  destruct Hs as [H1 [H2 Hs']]; split.
  - cbn; exists w1; split; [reflexivity|].
    split; apply tshape_trebase; apply tshape_tlift; [|apply tshape_tlift]; assumption.
  - apply sshape_srebase, sshape_slift, sshape_slift, Hs'.
Qed.

(** ** Building from a list, and canonicity *)

Theorem of_list_spec l :
  (forall e, In e l -> ok e) ->
  slist (of_list l) = l /\ sinv (of_list l) /\ sshape (of_list l).
Proof.
  induction l as [|x l IH]; intros Hok; [repeat split; intros k; reflexivity|].
  destruct IH as [H1 [H2 H3]]; [intros e He; apply Hok; right; exact He|].
  cbn [of_list fold_right]; fold (of_list l).
  destruct (cons_spec x (of_list l) (Hok x (or_introl eq_refl)) H2) as [E Hs].
  rewrite E, H1; repeat split; [exact Hs|apply sshape_cons, H3].
Qed.

Theorem canonical s1 s2 : canon s1 -> canon s2 -> slist s1 = slist s2 -> s1 = s2.
Proof. unfold canon; intros H1 H2 E; rewrite H1, E; symmetry; exact H2. Qed.

(** Well-formed sequences: built by [cons] from well-formed elements. *)
Definition good (s : seq) : Prop := canon s /\ sinv s.

Lemma good_nil : good SNil.
Proof. split; [reflexivity|split; [intro k; reflexivity|exact I]]. Qed.

Theorem good_cons x s : ok x -> good s -> good (cons x s) /\ slist (cons x s) = x :: slist s.
Proof.
  intros Hx [Hc Hs]; destruct (cons_spec x s Hx Hs) as [E Hs'].
  split; [split; [|exact Hs']|exact E].
  unfold canon; rewrite E; cbn [of_list fold_right]; fold (of_list (slist s)).
  rewrite <- Hc; reflexivity.
Qed.

Theorem good_of_list l : (forall e, In e l -> ok e) -> good (of_list l) /\ slist (of_list l) = l.
Proof.
  intros Hok; destruct (of_list_spec l Hok) as [E [Hs _]].
  split; [split; [unfold canon; rewrite E; reflexivity|exact Hs]|exact E].
Qed.

Lemma good_shape s : good s -> sshape s.
Proof.
  intros [Hc Hs]; rewrite Hc; apply (of_list_spec (slist s) (sinv_ok s Hs)).
Qed.

(** ** Indexing *)

Lemma div2_succ_double n : Nat.div2 (S (n + n)) = n.
Proof. replace (n + n) with (2 * n) by lia; apply Nat.div2_succ_double. Qed.

Lemma tlength w t : tshape w t -> length (tlist t) = w.
Proof.
  revert w; induction t as [x|a x l IHl r IHr]; cbn; [intros w ->; reflexivity|].
  intros w [w' [-> [Hl Hr]]]; rewrite length_map; cbn; rewrite length_app, (IHl _ Hl), (IHr _ Hr); reflexivity.
Qed.

Theorem tnth_spec w t i : tshape w t -> tnth w t i = nth_error (tlist t) i.
Proof.
  revert w i; induction t as [x|a x l IHl r IHr]; intros w i Hw; cbn [tnth tlist].
  - destruct i as [|[|i]]; reflexivity.
  - destruct Hw as [w' [-> [Hl Hr]]]; rewrite div2_succ_double.
    destruct i as [|j]; [reflexivity|].
    rewrite nth_error_map; cbn [nth_error]; f_equal.
    destruct (Nat.ltb_spec j w') as [Hj|Hj].
    + rewrite nth_error_app1 by (rewrite (tlength _ _ Hl); exact Hj); apply IHl, Hl.
    + rewrite nth_error_app2, (tlength _ _ Hl) by (rewrite (tlength _ _ Hl); exact Hj); apply IHr, Hr.
Qed.

Lemma slength_spec s : sshape s -> slength s = length (slist s).
Proof.
  induction s as [|a w t s IH]; cbn; [reflexivity|].
  intros [Ht Hs]; rewrite length_map, length_app, (tlength _ _ Ht), IH by exact Hs; reflexivity.
Qed.

Theorem snth_spec s i : sshape s -> snth s i = nth_error (slist s) i.
Proof.
  revert i; induction s as [|a w t s IH]; intros i Hs; cbn [snth slist];
    [destruct i; reflexivity|].
  destruct Hs as [Ht Hs]; rewrite nth_error_map; f_equal.
  destruct (Nat.ltb_spec i w) as [Hi|Hi].
  - rewrite nth_error_app1 by (rewrite (tlength _ _ Ht); exact Hi); apply tnth_spec, Ht.
  - rewrite nth_error_app2, (tlength _ _ Ht) by (rewrite (tlength _ _ Ht); exact Hi); apply IH, Hs.
Qed.

End Skew.
