(** * Weakening counts

    The only thinnings stored on the nodes of an adjustment are weakenings
    [0ᵏ1^∞]: "the outputs used below start [k] further up".  A weakening is
    just a count, and weakenings compose by addition.  This file gives

    - the factorisation property that makes counts canonical: the largest
      weakening that factors out of a non-empty set of indices is its
      minimum;
    - count maps: for each key (a label), the count, or [None] when the
      label is not used at all.  They are stored as a default plus
      exceptions that differ from it, which makes them canonical, and every
      operation on them is pointwise. *)

From Stdlib Require Import PArith Arith Lia Bool.
From ShiftedNames.Core Require Import Trie.

(** ** Factorisation of weakenings *)

Section Factor.

Variable I : nat -> Prop.

(** A set with a least element [m] is [m + J] for [J] containing [0]. *)
Lemma weak_factor_exists m :
  I m -> (forall i, I i -> m <= i) ->
  (forall i, I i <-> exists j, I (m + j) /\ i = m + j) /\ I (m + 0).
Proof.
  intros Hm Hmin; split; [|rewrite Nat.add_0_r; exact Hm].
  intros i; split.
  - intros Hi; exists (i - m); pose proof (Hmin i Hi).
    replace (m + (i - m)) with i by lia; auto.
  - intros [j [Hj ->]]; exact Hj.
Qed.

(** And that decomposition is unique: the weakening is the minimum. *)
Lemma weak_factor_unique k (J : nat -> Prop) m :
  (forall i, I i <-> exists j, J j /\ i = k + j) -> J 0 ->
  I m -> (forall i, I i -> m <= i) -> k = m.
Proof.
  intros HI HJ Hm Hmin.
  assert (I k) by (apply HI; exists 0; split; [exact HJ|lia]).
  apply HI in Hm as [j [_ ->]]; specialize (Hmin _ H); lia.
Qed.

End Factor.

(** ** Counts with "unused" *)

(** [None] is an unused label: it imposes no constraint, so it is the unit
    of [omin]. *)
Definition omin (a b : option nat) : option nat :=
  match a, b with
  | None, _ => b
  | _, None => a
  | Some x, Some y => Some (Nat.min x y)
  end.

(** Pushing a parent's count [d] into a child: only labels the child uses
    move. *)
Definition oadd (d c : option nat) : option nat :=
  match c with
  | None => None
  | Some y => Some (match d with Some x => x | None => 0 end + y)
  end.

(** A child's count relative to its parent's. *)
Definition osub (c base : option nat) : option nat :=
  match c with
  | None => None
  | Some y => Some (y - match base with Some x => x | None => 0 end)
  end.

Definition oeqb (a b : option nat) : bool :=
  match a, b with
  | Some x, Some y => Nat.eqb x y
  | None, None => true
  | _, _ => false
  end.

Lemma oeqb_spec a b : oeqb a b = true <-> a = b.
Proof.
  destruct a as [x|], b as [y|]; cbn; try (split; [discriminate|intros [=]]).
  - rewrite Nat.eqb_eq; split; [intros ->|intros [= ->]]; reflexivity.
  - split; reflexivity.
Qed.

Lemma oeqb_refl a : oeqb a a = true.
Proof. apply oeqb_spec; reflexivity. Qed.

(** ** Count maps *)

Record counts : Type := mk_counts { c_def : option nat; c_exc : tree (option nat) }.

Definition cget (c : counts) (k : positive) : option nat :=
  match get k (c_exc c) with Some v => v | None => c_def c end.

(** Canonical form: no exception repeats the default. *)
Definition cwf (c : counts) : Prop :=
  forall k v, get k (c_exc c) = Some v -> v <> c_def c.

(** *** A key outside two tries *)

Section Fresh.

Context {A : Type}.

Fixpoint rdepth' (m : tree' A) : nat :=
  match m with
  | Node001 r | Node011 _ r | Node101 _ r | Node111 _ _ r => S (rdepth' r)
  | _ => 0
  end.

Definition rdepth (m : tree A) : nat :=
  match m with Empty => 0 | Nodes m' => rdepth' m' end.

Fixpoint ikey (n : nat) : positive :=
  match n with 0 => xH | S n => xI (ikey n) end.

Lemma get_ikey (m : tree A) n : rdepth m < n -> get (ikey n) m = None.
Proof.
  destruct m as [|m]; [reflexivity|]; cbn [rdepth get].
  revert n; induction m; intros [|n] Hn; cbn in *; try lia; try reflexivity;
    apply IHm || apply IHm2; lia.
Qed.

End Fresh.

Definition fresh {A B} (m1 : tree A) (m2 : tree B) : positive :=
  ikey (S (rdepth m1 + rdepth m2)).

Lemma fresh_l {A B} (m1 : tree A) (m2 : tree B) : get (fresh m1 m2) m1 = None.
Proof. apply get_ikey; lia. Qed.

Lemma fresh_r {A B} (m1 : tree A) (m2 : tree B) : get (fresh m1 m2) m2 = None.
Proof. apply get_ikey; lia. Qed.

(** *** Canonicity *)

Theorem counts_ext c1 c2 :
  cwf c1 -> cwf c2 -> (forall k, cget c1 k = cget c2 k) -> c1 = c2.
Proof.
  destruct c1 as [d1 e1], c2 as [d2 e2]; unfold cwf, cget; cbn; intros W1 W2 H.
  assert (Hd : d1 = d2).
  { specialize (H (fresh e1 e2)); rewrite fresh_l, fresh_r in H; exact H. }
  subst d2; f_equal; apply extensionality; intro k; specialize (H k).
  destruct (get k e1) as [v1|] eqn:E1, (get k e2) as [v2|] eqn:E2.
  - f_equal; exact H.
  - exfalso; apply (W1 _ _ E1), H.
  - exfalso; apply (W2 _ _ E2); symmetry; exact H.
  - reflexivity.
Qed.

(** *** Pointwise operations *)

Definition cmap2_at (f : option nat -> option nat -> option nat) (c1 c2 : counts)
  (_ : positive) (o1 o2 : option (option nat)) : option (option nat) :=
  let v := f (match o1 with Some v => v | None => c_def c1 end)
             (match o2 with Some v => v | None => c_def c2 end) in
  if oeqb v (f (c_def c1) (c_def c2)) then None else Some v.

Definition cmap2 (f : option nat -> option nat -> option nat) (c1 c2 : counts) : counts :=
  mk_counts (f (c_def c1) (c_def c2)) (merge (cmap2_at f c1 c2) (c_exc c1) (c_exc c2)).

Lemma cmap2_none f c1 c2 k : cmap2_at f c1 c2 k None None = None.
Proof. unfold cmap2_at; cbv beta zeta; rewrite oeqb_refl; reflexivity. Qed.

Lemma cget_cmap2 f c1 c2 k : cget (cmap2 f c1 c2) k = f (cget c1 k) (cget c2 k).
Proof.
  unfold cmap2, cget; cbn [c_def c_exc]; rewrite get_merge by apply cmap2_none.
  unfold cmap2_at; destruct (get k (c_exc c1)), (get k (c_exc c2)); cbv beta zeta;
    match goal with |- context [oeqb ?v ?d] =>
      destruct (oeqb v d) eqn:E; [apply oeqb_spec in E; symmetry; exact E|reflexivity]
    end.
Qed.

Lemma cwf_cmap2 f c1 c2 : cwf (cmap2 f c1 c2).
Proof.
  intros k v; unfold cmap2; cbn [c_def c_exc]; rewrite get_merge by apply cmap2_none.
  unfold cmap2_at; cbv beta zeta; intros H Hv.
  destruct (get k (c_exc c1)), (get k (c_exc c2));
    match type of H with
    | (if oeqb ?w ?d then None else Some _) = Some _ =>
        destruct (oeqb w d) eqn:E; [discriminate|injection H as <-];
        rewrite (proj2 (oeqb_spec _ _) Hv) in E; discriminate
    end.
Qed.

Definition cmin : counts -> counts -> counts := cmap2 omin.
Definition cadd : counts -> counts -> counts := cmap2 oadd.
Definition csub : counts -> counts -> counts := cmap2 osub.

Lemma cget_cmin c1 c2 k : cget (cmin c1 c2) k = omin (cget c1 k) (cget c2 k).
Proof. apply cget_cmap2. Qed.

Lemma cget_cadd d c k : cget (cadd d c) k = oadd (cget d k) (cget c k).
Proof. apply cget_cmap2. Qed.

Lemma cget_csub c b k : cget (csub c b) k = osub (cget c k) (cget b k).
Proof. apply cget_cmap2. Qed.

(** *** Basic maps *)

(** Nothing used. *)
Definition cnone : counts := mk_counts None Empty.

(** Only [k], from [n]. *)
Definition cone (k : positive) (n : nat) : counts := mk_counts None (set k (Some n) Empty).

Lemma cwf_cnone : cwf cnone.
Proof. intros k v H; cbn in H; discriminate. Qed.

Lemma cwf_cone k n : cwf (cone k n).
Proof.
  intros k' v; unfold cone; cbn; rewrite get_set.
  destruct (Pos.eqb k' k); [intros [= <-]; discriminate|rewrite get_Empty; discriminate].
Qed.

Lemma cget_cnone k : cget cnone k = None.
Proof. reflexivity. Qed.

Lemma cget_cone k n k' : cget (cone k n) k' = if Pos.eqb k' k then Some n else None.
Proof.
  unfold cget, cone; cbn; rewrite get_set.
  destruct (Pos.eqb k' k); [reflexivity|rewrite get_Empty; reflexivity].
Qed.

(** ** Factoring a node's counts out of its children

    A node's count for a label is the minimum over its children; each child
    then stores its counts relative to the node. *)

Lemma omin_le a b x : omin a b = Some x -> forall y, a = Some y \/ b = Some y -> x <= y.
Proof.
  destruct a as [p|], b as [q|]; cbn; intros [= <-] y [[= <-]|[= <-]]; lia.
Qed.

(** Adding the node's counts back gives the child. *)
Lemma oadd_osub_omin a b : oadd (omin a b) (osub a (omin a b)) = a.
Proof. destruct a as [p|], b as [q|]; cbn; f_equal; lia. Qed.

(** After factoring, the children's minimum is 0 wherever a label is used. *)
Lemma omin_osub a b :
  omin (osub a (omin a b)) (osub b (omin a b))
  = match omin a b with Some _ => Some 0 | None => None end.
Proof. destruct a as [p|], b as [q|]; cbn; f_equal; lia. Qed.

Lemma cget_factor_l a b k : cget (cadd (cmin a b) (csub a (cmin a b))) k = cget a k.
Proof. rewrite cget_cadd, cget_csub, cget_cmin; apply oadd_osub_omin. Qed.

Lemma cget_factor_r a b k : cget (cadd (cmin a b) (csub b (cmin a b))) k = cget b k.
Proof.
  rewrite cget_cadd, cget_csub, cget_cmin.
  destruct (cget a k) as [p|], (cget b k) as [q|]; cbn; f_equal; lia.
Qed.

Lemma cget_factor_min a b k :
  cget (cmin (csub a (cmin a b)) (csub b (cmin a b))) k
  = match cget (cmin a b) k with Some _ => Some 0 | None => None end.
Proof. rewrite !cget_cmin, !cget_csub, cget_cmin; apply omin_osub. Qed.

(** ** Counts as deltas

    Moving data between bases uses a count map as a delta: an unused label
    then counts as 0. *)

Definition oval (a : option nat) : nat := match a with Some n => n | None => 0 end.

Definition dval (d : counts) (k : positive) : nat := oval (cget d k).

(** Adding two deltas. *)
Definition oplus (a b : option nat) : option nat :=
  match a, b with None, None => None | _, _ => Some (oval a + oval b) end.

Definition cplus : counts -> counts -> counts := cmap2 oplus.

Lemma cget_cplus a b k : cget (cplus a b) k = oplus (cget a k) (cget b k).
Proof. apply cget_cmap2. Qed.

Lemma dval_cplus a b k : dval (cplus a b) k = dval a k + dval b k.
Proof. unfold dval; rewrite cget_cplus; destruct (cget a k), (cget b k); reflexivity. Qed.

(** [d] is below [c] wherever both are used. *)
Definition cle (d c : counts) : Prop :=
  forall k n m, cget d k = Some n -> cget c k = Some m -> n <= m.

(** ** Arithmetic on optional counts *)

Lemma oadd_omin d a b : oadd d (omin a b) = omin (oadd d a) (oadd d b).
Proof. destruct d, a, b; cbn; f_equal; lia. Qed.

Lemma osub_omin a b d : osub (omin a b) d = omin (osub a d) (osub b d).
Proof. destruct a, b, d; cbn; f_equal; lia. Qed.

Lemma oadd_oadd d1 d2 c : oadd d1 (oadd d2 c) = oadd (oplus d1 d2) c.
Proof. destruct d1, d2, c; cbn; f_equal; lia. Qed.

Lemma omin_none_l a b : omin a b = None -> a = None.
Proof. destruct a, b; cbn; congruence. Qed.

Lemma omin_none_r a b : omin a b = None -> b = None.
Proof. destruct a, b; cbn; congruence. Qed.

Lemma oadd_none d c : oadd d c = None <-> c = None.
Proof. destruct c; cbn; split; congruence. Qed.

(** ** Equations between count maps *)

Lemma csub_cadd d r : cwf r -> csub (cadd d r) d = r.
Proof.
  intros Hr; apply counts_ext; [apply cwf_cmap2|exact Hr|]; intro k.
  rewrite cget_csub, cget_cadd; destruct (cget d k), (cget r k); cbn; f_equal; lia.
Qed.

Lemma cadd_csub d r : cwf r -> cle d r -> cadd d (csub r d) = r.
Proof.
  intros Hr Hle; apply counts_ext; [apply cwf_cmap2|exact Hr|]; intro k.
  rewrite cget_cadd, cget_csub.
  destruct (cget d k) as [n|] eqn:Ed, (cget r k) as [m|] eqn:Er; cbn; try reflexivity.
  - specialize (Hle k n m Ed Er); f_equal; lia.
  - f_equal; lia.
Qed.

Lemma cadd_cadd d1 d2 r : cadd d1 (cadd d2 r) = cadd (cplus d1 d2) r.
Proof.
  apply counts_ext; try apply cwf_cmap2; intro k.
  rewrite !cget_cadd, cget_cplus; apply oadd_oadd.
Qed.

Lemma cadd_ext d d' r :
  (forall k, cget r k <> None -> dval d k = dval d' k) -> cadd d r = cadd d' r.
Proof.
  intros H; apply counts_ext; try apply cwf_cmap2; intro k.
  rewrite !cget_cadd; destruct (cget r k) as [m|] eqn:E; [|reflexivity].
  specialize (H k ltac:(congruence)); unfold dval in H.
  destruct (cget d k), (cget d' k); cbn in *; subst; reflexivity.
Qed.

Lemma cle_cmin_inv_l d x y : cle d (cmin x y) -> cle d x.
Proof.
  intros H k n m Hd Hx; specialize (H k n); rewrite cget_cmin, Hx in H.
  destruct (cget y k) as [q|]; cbn in H; [specialize (H _ Hd eq_refl); lia|apply (H m Hd eq_refl)].
Qed.

Lemma cle_cmin_inv_r d x y : cle d (cmin x y) -> cle d y.
Proof.
  intros H k n m Hd Hy; specialize (H k n); rewrite cget_cmin, Hy in H.
  destruct (cget x k) as [q|]; cbn in H; [specialize (H _ Hd eq_refl); lia|apply (H m Hd eq_refl)].
Qed.

Lemma dval_le_cle d k n : cle d (cone k n) -> dval d k <= n.
Proof.
  intros H; unfold dval; destruct (cget d k) as [m|] eqn:E; cbn; [|lia].
  apply (H k m n E); rewrite cget_cone, Pos.eqb_refl; reflexivity.
Qed.
