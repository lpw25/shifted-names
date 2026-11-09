(** * Weakening counts

    The only thinnings stored on the nodes of an adjustment are weakenings
    [0ᵏ1^∞]: "the outputs used below start [k] further up".  A weakening is
    just a count, and weakenings compose by addition.  This file gives

    - the factorisation property that makes counts canonical: the largest
      weakening that factors out of a non-empty set of indices is its
      minimum;
    - count maps: for each key (a label), the count, or [None] when the
      label is not used at all.  They are stored as a default plus
      exceptions that differ from it, which makes them canonical (a count
      map carries a strict proof of this), and every operation on them is
      pointwise.  An operation only looks inside the subtrees of exceptions
      where both maps have some, when the other map's default makes it
      keep or drop the rest whole. *)

From Stdlib Require Import PArith Arith Lia Bool StrictProp.
From ShiftedNames.Core Require Import Strict Trie.

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

(** An optional count as a delta: unused counts as 0. *)
Definition oval (a : option nat) : nat := match a with Some n => n | None => 0 end.

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

(** Canonical form: no exception repeats the default. *)
Definition cwfr (d : option nat) (e : tree (option nat)) : bool := tall (fun v => negb (oeqb v d)) e.

Record counts : Type :=
  mk_counts { c_def : option nat; c_exc : tree (option nat); c_ok : Is_true_s (cwfr c_def c_exc) }.

Definition cget (c : counts) (k : positive) : option nat :=
  match get k (c_exc c) with Some v => v | None => c_def c end.

Definition cwf (c : counts) : Prop :=
  forall k v, get k (c_exc c) = Some v -> v <> c_def c.

Lemma cwfr_spec d e : cwfr d e = true <-> forall k v, get k e = Some v -> v <> d.
Proof.
  unfold cwfr; rewrite tall_spec; split; intros H k v E; specialize (H k v E).
  - rewrite negb_true_iff in H; intros Hv; rewrite Hv, oeqb_refl in H; discriminate.
  - apply negb_true_iff; destruct (oeqb v d) eqn:Ev; [apply oeqb_spec in Ev; contradiction|reflexivity].
Qed.

Lemma cwf_all c : cwf c.
Proof. unfold cwf; apply cwfr_spec, Is_true_s_elim, c_ok. Qed.

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
  destruct c1 as [d1 e1 p1], c2 as [d2 e2 p2]; unfold cwf, cget; cbn; intros W1 W2 H.
  assert (Hd : d1 = d2).
  { specialize (H (fresh e1 e2)); rewrite fresh_l, fresh_r in H; exact H. }
  subst d2; assert (He : e1 = e2); [|subst e2; reflexivity].
  apply extensionality; intro k; specialize (H k).
  destruct (get k e1) as [v1|] eqn:E1, (get k e2) as [v2|] eqn:E2.
  - f_equal; exact H.
  - exfalso; apply (W1 _ _ E1), H.
  - exfalso; apply (W2 _ _ E2); symmetry; exact H.
  - reflexivity.
Qed.

(** *** Pointwise operations

    An operation says, for each default of the other map, whether it keeps
    the values of exceptions that only one map has ([MKeep]), sends them
    all to the result's default ([MDrop]), or has to map them ([MMap]).
    Keeping or dropping costs nothing, so the cost of an operation is the
    overlap of the two maps' exceptions plus the sides it maps. *)

Inductive mode := MKeep | MDrop | MMap.

Record cop : Type := {
  cop_f : option nat -> option nat -> option nat;
  cop_l : option nat -> mode;   (* exceptions of the left map only, by the right default *)
  cop_r : option nat -> mode;   (* exceptions of the right map only, by the left default *)
  cop_lk : forall d v, cop_l d = MKeep -> cop_f v d = v;
  cop_ld : forall d v w, cop_l d = MDrop -> cop_f v d = cop_f w d;
  cop_rk : forall d v, cop_r d = MKeep -> cop_f d v = v;
  cop_rd : forall d v w, cop_r d = MDrop -> cop_f d v = cop_f d w }.

Definition cmap2_at (f : option nat -> option nat -> option nat) (d1 d2 : option nat)
  (o1 o2 : option (option nat)) : option (option nat) :=
  let v := f (match o1 with Some v => v | None => d1 end)
             (match o2 with Some v => v | None => d2 end) in
  if oeqb v (f d1 d2) then None else Some v.

Lemma cmap2_none f d1 d2 : cmap2_at f d1 d2 None None = None.
Proof. unfold cmap2_at; cbv beta zeta; rewrite oeqb_refl; reflexivity. Qed.

Definition cside (m : mode) (g : option nat -> option (option nat)) (t : tree (option nat)) : tree (option nat) :=
  match m with MKeep => t | MDrop => Empty | MMap => map_filter (fun _ v => g v) t end.

Definition cmap2_exc (o : cop) (d1 d2 : option nat) (e1 e2 : tree (option nat)) : tree (option nat) :=
  let g := cmap2_at (cop_f o) d1 d2 in
  mmerge g (cside (cop_l o d2) (fun v => g (Some v) None)) (cside (cop_r o d1) (fun v => g None (Some v))) e1 e2.

Lemma get_cmap2_exc o d1 d2 e1 e2 :
  cwfr d1 e1 = true -> cwfr d2 e2 = true ->
  forall k, get k (cmap2_exc o d1 d2 e1 e2) = cmap2_at (cop_f o) d1 d2 (get k e1) (get k e2).
Proof.
  intros W1 W2; rewrite cwfr_spec in W1, W2; unfold cmap2_exc.
  refine (get_mmerge _ _ _ (fun v => v <> d1) (fun v => v <> d2) _ _ _ _ W1 W2).
  - intros m Hm i; destruct (cop_l o d2) eqn:M; cbn [cside].
    + destruct (get i m) as [v|] eqn:E; [|symmetry; apply cmap2_none].
      unfold cmap2_at; rewrite !(cop_lk o d2 _ M).
      destruct (oeqb v d1) eqn:Ev; [apply oeqb_spec in Ev; contradiction (Hm i v E)|reflexivity].
    + rewrite get_Empty; destruct (get i m) as [v|]; [|symmetry; apply cmap2_none].
      unfold cmap2_at; rewrite (cop_ld o d2 v d1 M), oeqb_refl; reflexivity.
    + rewrite get_map_filter; destruct (get i m); [reflexivity|symmetry; apply cmap2_none].
  - intros m Hm i; destruct (cop_r o d1) eqn:M; cbn [cside].
    + destruct (get i m) as [v|] eqn:E; [|symmetry; apply cmap2_none].
      unfold cmap2_at; rewrite !(cop_rk o d1 _ M).
      destruct (oeqb v d2) eqn:Ev; [apply oeqb_spec in Ev; contradiction (Hm i v E)|reflexivity].
    + rewrite get_Empty; destruct (get i m) as [v|]; [|symmetry; apply cmap2_none].
      unfold cmap2_at; rewrite (cop_rd o d1 v d2 M), oeqb_refl; reflexivity.
    + rewrite get_map_filter; destruct (get i m); [reflexivity|symmetry; apply cmap2_none].
Qed.

Lemma cmap2_ok_eq o c1 c2 :
  cwfr (cop_f o (c_def c1) (c_def c2)) (cmap2_exc o (c_def c1) (c_def c2) (c_exc c1) (c_exc c2)) = true.
Proof.
  apply cwfr_spec; intros k v E.
  rewrite get_cmap2_exc in E by apply Is_true_s_elim, c_ok.
  unfold cmap2_at in E; cbv zeta in E.
  match type of E with (if oeqb ?w ?d then None else Some _) = Some _ =>
    destruct (oeqb w d) eqn:Eq; [discriminate|injection E as <-]; intros H; rewrite H, oeqb_refl in Eq; discriminate
  end.
Qed.

(** The canonicity proofs reduce to [stt] when the check computes, so that
    closed count maps can be compared by computation. *)
Definition cmap2_ok o c1 c2 := Is_true_s_intro (cmap2_ok_eq o c1 c2).

Definition cmap2 (o : cop) (c1 c2 : counts) : counts :=
  mk_counts (cop_f o (c_def c1) (c_def c2)) (cmap2_exc o (c_def c1) (c_def c2) (c_exc c1) (c_exc c2)) (cmap2_ok o c1 c2).

Lemma get_cmap2 o c1 c2 k :
  get k (c_exc (cmap2 o c1 c2)) = cmap2_at (cop_f o) (c_def c1) (c_def c2) (get k (c_exc c1)) (get k (c_exc c2)).
Proof. apply get_cmap2_exc; apply Is_true_s_elim, c_ok. Qed.

Lemma cget_cmap2 o c1 c2 k : cget (cmap2 o c1 c2) k = cop_f o (cget c1 k) (cget c2 k).
Proof.
  unfold cget; rewrite get_cmap2; cbn [c_def].
  unfold cmap2_at; destruct (get k (c_exc c1)), (get k (c_exc c2)); cbv beta zeta;
    match goal with |- context [oeqb ?v ?d] =>
      destruct (oeqb v d) eqn:E; [apply oeqb_spec in E; symmetry; exact E|reflexivity]
    end.
Qed.

Lemma cwf_cmap2 o c1 c2 : cwf (cmap2 o c1 c2).
Proof. apply cwf_all. Qed.

(** The operations.  Defaults are [None] or [Some 0] in practice, and
    for those every operation keeps or drops, except [cadd] and [cplus],
    which map the side whose other default is [Some 0]. *)

Definition zmode (d : option nat) : mode := match d with None | Some 0 => MKeep | _ => MMap end.

Ltac cop_solve :=
  let d := fresh "d" in let H := fresh "H" in
  intros d; intros;
  match goal with H : _ = _ |- _ => destruct d as [[|?]|]; cbn in H; try discriminate end;
  repeat match goal with o : option nat |- _ => destruct o end; cbn; try reflexivity; f_equal; lia.

Definition cop_min : cop.
Proof.
  refine {| cop_f := omin;
            cop_l := fun d => match d with None => MKeep | Some 0 => MDrop | _ => MMap end;
            cop_r := fun d => match d with None => MKeep | Some 0 => MDrop | _ => MMap end |};
    cop_solve.
Defined.

Definition cop_add : cop.
Proof.
  refine {| cop_f := oadd;
            cop_l := fun d => match d with None => MDrop | _ => MMap end;
            cop_r := zmode |}; cop_solve.
Defined.

Definition cop_sub : cop.
Proof.
  refine {| cop_f := osub;
            cop_l := zmode;
            cop_r := fun d => match d with None | Some 0 => MDrop | _ => MMap end |}; cop_solve.
Defined.

Definition cmin : counts -> counts -> counts := cmap2 cop_min.
Definition cadd : counts -> counts -> counts := cmap2 cop_add.
Definition csub : counts -> counts -> counts := cmap2 cop_sub.

Lemma cget_cmin c1 c2 k : cget (cmin c1 c2) k = omin (cget c1 k) (cget c2 k).
Proof. apply cget_cmap2. Qed.

Lemma cget_cadd d c k : cget (cadd d c) k = oadd (cget d k) (cget c k).
Proof. apply cget_cmap2. Qed.

Lemma cget_csub c b k : cget (csub c b) k = osub (cget c k) (cget b k).
Proof. apply cget_cmap2. Qed.

(** *** Basic maps *)

(** Nothing used. *)
Definition cnone : counts := mk_counts None Empty (Is_true_s_intro eq_refl).

Lemma cone_ok_eq k n :
  cwfr None (set k (Some n) Empty) = true.
Proof.
  apply cwfr_spec; intros k' v; rewrite get_set.
  destruct (Pos.eqb k' k); [intros [= <-]; discriminate|rewrite get_Empty; discriminate].
Qed.

Definition cone_ok k n := Is_true_s_intro (cone_ok_eq k n).

(** Only [k], from [n]. *)
Definition cone (k : positive) (n : nat) : counts := mk_counts None (set k (Some n) Empty) (cone_ok k n).

Lemma cwf_cnone : cwf cnone.
Proof. apply cwf_all. Qed.

Lemma cwf_cone k n : cwf (cone k n).
Proof. apply cwf_all. Qed.

Lemma cget_cnone k : cget cnone k = None.
Proof. reflexivity. Qed.

Lemma cget_cone k n k' : cget (cone k n) k' = if Pos.eqb k' k then Some n else None.
Proof.
  unfold cget, cone; cbn; rewrite get_set.
  destruct (Pos.eqb k' k); [reflexivity|rewrite get_Empty; reflexivity].
Qed.

(** How far [a] is above [u], where [u] is used: lowering [a] to
    [cmin a u] moves what is stored relative to [a] up by this much.  It
    only looks at [u]'s exceptions when both defaults are [None] or
    [Some 0]. *)
Definition oexcess (v u : option nat) : option nat :=
  match u with
  | None => None
  | Some y => match oval v - y with 0 => None | n => Some n end
  end.

Definition cop_excess : cop.
Proof.
  refine {| cop_f := oexcess;
            cop_l := fun d => match d with None => MDrop | _ => MMap end;
            cop_r := fun d => match d with None | Some 0 => MDrop | _ => MMap end |}; cop_solve.
Defined.

Definition cexcess : counts -> counts -> counts := cmap2 cop_excess.


(** *** From a map of counts *)

Lemma csome_ok_eq (t : tree nat) : cwfr None (map_filter (fun _ n => Some (Some n)) t) = true.
Proof.
  apply cwfr_spec; intros k v; rewrite get_map_filter.
  destruct (get k t); [intros [= <-]; discriminate|discriminate].
Qed.

Definition csome_ok t := Is_true_s_intro (csome_ok_eq t).

(** The labels of [t] at their counts, every other label unused. *)
Definition csome (t : tree nat) : counts := mk_counts None (map_filter (fun _ n => Some (Some n)) t) (csome_ok t).

Lemma cget_csome t k : cget (csome t) k = get k t.
Proof. unfold cget, csome; cbn [c_exc c_def]; rewrite get_map_filter; destruct (get k t); reflexivity. Qed.

(** *** Setting one key *)

Lemma cset_ok_eq c k v :
  cwfr (c_def c) (if oeqb v (c_def c) then remove k (c_exc c) else set k v (c_exc c)) = true.
Proof.
  apply cwfr_spec; intros k' v'; pose proof (cwf_all c k') as Hc.
  destruct (oeqb v (c_def c)) eqn:E.
  - rewrite get_remove; destruct (Pos.eqb k' k); [discriminate|apply Hc].
  - rewrite get_set; destruct (Pos.eqb k' k); [intros [= <-] H; rewrite H, oeqb_refl in E; discriminate|apply Hc].
Qed.

Definition cset_ok c k v := Is_true_s_intro (cset_ok_eq c k v).

(** O(|k|). *)
Definition cset (c : counts) (k : positive) (v : option nat) : counts :=
  mk_counts (c_def c) (if oeqb v (c_def c) then remove k (c_exc c) else set k v (c_exc c)) (cset_ok c k v).

Lemma cget_cset c k v k' : cget (cset c k v) k' = if Pos.eqb k' k then v else cget c k'.
Proof.
  unfold cset, cget; cbn [c_exc c_def].
  destruct (oeqb v (c_def c)) eqn:E; [rewrite get_remove|rewrite get_set];
    destruct (Pos.eqb k' k); try reflexivity.
  apply oeqb_spec in E; symmetry; exact E.
Qed.

Lemma cwf_cset c k v : cwf c -> cwf (cset c k v).
Proof. intros _; apply cwf_all. Qed.

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


Definition dval (d : counts) (k : positive) : nat := oval (cget d k).

(** Adding two deltas. *)
Definition oplus (a b : option nat) : option nat :=
  match a, b with None, None => None | _, _ => Some (oval a + oval b) end.

Definition cop_plus : cop.
Proof.
  refine {| cop_f := oplus;
            cop_l := fun d => match d with None => MKeep | _ => MMap end;
            cop_r := fun d => match d with None => MKeep | _ => MMap end |}; cop_solve.
Defined.

Definition cplus : counts -> counts -> counts := cmap2 cop_plus.

(** Two count maps as totals: an unused label counts as 0. *)
Definition cop_total : cop.
Proof.
  refine {| cop_f := fun x y => Some (oval x + oval y); cop_l := fun _ => MMap; cop_r := fun _ => MMap |};
    intros; discriminate.
Defined.

Definition ctotal : counts -> counts -> counts := cmap2 cop_total.

Lemma cget_ctotal c1 c2 k : cget (ctotal c1 c2) k = Some (oval (cget c1 k) + oval (cget c2 k)).
Proof. apply cget_cmap2. Qed.

Lemma cget_cplus a b k : cget (cplus a b) k = oplus (cget a k) (cget b k).
Proof. apply cget_cmap2. Qed.

Lemma dval_cplus a b k : dval (cplus a b) k = dval a k + dval b k.
Proof. unfold dval; rewrite cget_cplus; destruct (cget a k), (cget b k); reflexivity. Qed.

Lemma dval_cexcess a u k :
  cget a k <> None -> dval (cmin a u) k + dval (cexcess a u) k = dval a k.
Proof.
  unfold dval; rewrite cget_cmin; unfold cexcess; rewrite cget_cmap2; cbn [cop_f cop_excess oexcess].
  destruct (cget a k) as [x|]; [intros _|intros H; contradiction].
  destruct (cget u k) as [y|]; cbn; [|lia].
  destruct (x - y) eqn:E; cbn; lia.
Qed.

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

(** ** Keys beyond a trie *)

Fixpoint tdepth' {A} (m : tree' A) : nat :=
  match m with
  | Node001 r | Node011 _ r => S (tdepth' r)
  | Node100 l | Node110 l _ => S (tdepth' l)
  | Node101 l r | Node111 l _ r => S (Nat.max (tdepth' l) (tdepth' r))
  | Node010 _ => 0
  end.

Definition tdepth {A} (m : tree A) : nat := match m with Empty => 0 | Nodes m' => tdepth' m' end.

Lemma get_deep {A} (m : tree A) k : S (tdepth m) < Pos.size_nat k -> get k m = None.
Proof.
  destruct m as [|m]; [reflexivity|]; cbn [tdepth get].
  revert k; induction m; intros [k|k|] Hk; cbn [get' tdepth' Pos.size_nat] in *; try reflexivity;
    try lia; try (apply IHm; lia); try (apply IHm1; lia); try (apply IHm2; lia).
Qed.

(** Adding nothing. *)
Lemma cadd_cnone c : cwf c -> cadd cnone c = c.
Proof.
  intros Hc; apply counts_ext; [apply cwf_cmap2|exact Hc|].
  intro k; rewrite cget_cadd, cget_cnone; destruct (cget c k); reflexivity.
Qed.

(** ** Deciding the invariants

    The invariants are decided by boolean checks, so that a proof of one can
    be kept in SProp (as [Is_true_s]) and still be used. *)

Definition ceqb (c1 c2 : counts) : bool :=
  oeqb (c_def c1) (c_def c2) && teqb oeqb (c_exc c1) (c_exc c2).

Lemma ceqb_spec c1 c2 : ceqb c1 c2 = true <-> c1 = c2.
Proof.
  destruct c1 as [d1 e1], c2 as [d2 e2]; unfold ceqb; cbn [c_def c_exc].
  rewrite andb_true_iff, oeqb_spec, (teqb_spec oeqb oeqb_spec).
  split; [intros [-> ->]; reflexivity|intros [= -> ->]; split; reflexivity].
Qed.

Definition cwfb (c : counts) : bool := cwfr (c_def c) (c_exc c).

Lemma cwfb_spec c : cwfb c = true <-> cwf c.
Proof. apply cwfr_spec. Qed.

(** Pointwise equality of canonical count maps is equality. *)
Lemma ceqb_ext c1 c2 :
  cwf c1 -> cwf c2 -> ceqb c1 c2 = true <-> (forall k, cget c1 k = cget c2 k).
Proof.
  intros W1 W2; rewrite ceqb_spec; split; [intros ->; reflexivity|apply counts_ext; assumption].
Qed.
