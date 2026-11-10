(** * Binary tries with weakening counts

    A trie over [positive] keys (the shape of Trie.v: [xO] left, [xI] right)
    whose every node carries a count map: how far the uses of everything
    below it start above its parent's base (Counts.v).  Elements are stored
    relative to the base of the node that holds them, so moving a whole
    subtrie to another base only changes its top.

    Canonicity: empty subtries are never represented as nodes, and every
    count map is the minimum over what is below, so a well-formed trie is
    determined by its lookups ([acanonical]). *)

From Stdlib Require Import PArith Arith Lia List Bool.
From ShiftedNames.Core Require Import Trie Counts Based.
Import ListNotations.

Section ATrie.

Context {X : Type} {BX : Based X} {LX : BasedLaws X}.

Inductive atrie : Type :=
| AEmpty
| ANode (a : counts) (l : atrie) (o : option X) (r : atrie).

Definition aann (t : atrie) : counts :=
  match t with AEmpty => cnone | ANode a _ _ _ => a end.

Definition oelems (o : option X) : list X :=
  match o with Some x => [x] | None => [] end.

Definition ouses (o : option X) : counts :=
  match o with Some x => uses x | None => cnone end.

(** Everything stored, relative to the parent's base. *)
Fixpoint aelems (t : atrie) : list X :=
  match t with
  | AEmpty => []
  | ANode a l o r => map (unshift a) (aelems l ++ oelems o ++ aelems r)
  end.

(** Lookup, relative to the parent's base. *)
Fixpoint aget (k : positive) (t : atrie) {struct t} : option X :=
  match t with
  | AEmpty => None
  | ANode a l o r =>
      option_map (unshift a)
        (match k with xH => o | xO k' => aget k' l | xI k' => aget k' r end)
  end.

(** Whether [k] has an element, without moving it to the parent's base. *)
Fixpoint amem (k : positive) (t : atrie) {struct t} : bool :=
  match t with
  | AEmpty => false
  | ANode _ l o r =>
      match k with
      | xH => match o with Some _ => true | None => false end
      | xO k' => amem k' l
      | xI k' => amem k' r
      end
  end.

Lemma amem_spec k t : amem k t = match aget k t with Some _ => true | None => false end.
Proof.
  revert k; induction t as [|a l IHl o r IHr]; intros k; [reflexivity|].
  destruct k as [k|k|]; cbn [amem aget]; [rewrite IHr|rewrite IHl|]; [destruct (aget k r)|destruct (aget k l)|destruct o];
    reflexivity.
Qed.

Definition arebase (d : counts) (t : atrie) : atrie :=
  match t with AEmpty => AEmpty | ANode a l o r => ANode (csub a d) l o r end.

Definition alift (d : counts) (t : atrie) : atrie :=
  match t with AEmpty => AEmpty | ANode a l o r => ANode (cadd d a) l o r end.

(** Building a node from aparts relative to the parent: its counts are the
    minimum of what is below. *)
Definition amk (l : atrie) (o : option X) (r : atrie) : atrie :=
  match l, o, r with
  | AEmpty, None, AEmpty => AEmpty
  | _, _, _ =>
      let m := cmin (aann l) (cmin (ouses o) (aann r)) in
      ANode m (arebase m l) (option_map (shift m) o) (arebase m r)
  end.

(** A node's aparts, relative to the parent. *)
Definition aparts (t : atrie) : atrie * option X * atrie :=
  match t with
  | AEmpty => (AEmpty, None, AEmpty)
  | ANode a l o r => (alift a l, option_map (unshift a) o, alift a r)
  end.

(** Changing the element at [k]; [f] sees and returns elements relative to
    the parent's base. *)
Fixpoint aupdate (k : positive) (f : option X -> option X) (t : atrie) {struct k} : atrie :=
  match aparts t with
  | (l, o, r) =>
      match k with
      | xH => amk l (f o) r
      | xO k' => amk (aupdate k' f l) o r
      | xI k' => amk l o (aupdate k' f r)
      end
  end.

(** ** Invariant *)

Definition anonempty (l : atrie) (o : option X) (r : atrie) : Prop :=
  match l, o, r with AEmpty, None, AEmpty => False | _, _, _ => True end.

Fixpoint ainv (t : atrie) : Prop :=
  match t with
  | AEmpty => True
  | ANode a l o r =>
      (forall k, cget a k = lmin (aelems t) k) /\ anonempty l o r /\ ainv l /\ ainv r
  end.

Lemma ainv_ann t : ainv t -> forall k, cget (aann t) k = lmin (aelems t) k.
Proof. destruct t; cbn [ainv aann]; [reflexivity|tauto]. Qed.



(** ** Lookups and elements *)

Lemma omap_some (f : X -> X) o y : option_map f o = Some y -> exists x, o = Some x /\ y = f x.
Proof. destruct o as [x|]; cbn; [intros [= <-]; eauto|discriminate]. Qed.

Definition asub (k : positive) (l : atrie) (o : option X) (r : atrie) : option X :=
  match k with xH => o | xO k' => aget k' l | xI k' => aget k' r end.

Lemma aget_in k t e : aget k t = Some e -> In e (aelems t).
Proof.
  revert k e; induction t as [|a l IHl o r IHr]; intros k e; cbn [aget aelems]; [intros H; discriminate|].
  intros H; apply omap_some in H as [e' [He ->]]; apply in_map.
  destruct k as [k|k|]; cbn in He.
  - apply in_or_app; right; apply in_or_app; right; apply (IHr _ _ He).
  - apply in_or_app; left; apply (IHl _ _ He).
  - apply in_or_app; right; apply in_or_app; left; destruct o; [injection He as ->; left; reflexivity|discriminate].
Qed.

Lemma asub_in k l o r e : asub k l o r = Some e -> In e (aelems l ++ oelems o ++ aelems r).
Proof.
  destruct k as [k|k|]; cbn [asub]; intros He.
  - apply in_or_app; right; apply in_or_app; right; apply (aget_in _ _ _ He).
  - apply in_or_app; left; apply (aget_in _ _ _ He).
  - apply in_or_app; right; apply in_or_app; left; destruct o; [injection He as ->; left; reflexivity|discriminate].
Qed.

Lemma aelems_aget t e : In e (aelems t) -> exists k, aget k t = Some e.
Proof.
  revert e; induction t as [|a l IHl o r IHr]; intros e; cbn [aelems]; [intros []|].
  intros Hin; apply in_map_iff in Hin as [e' [<- Hin]].
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (IHl _ Hin) as [k Hk]; exists (xO k); cbn; rewrite Hk; reflexivity.
  - apply in_app_or in Hin as [Hin|Hin].
    + exists xH; destruct o; [destruct Hin as [<-|[]]; reflexivity|destruct Hin].
    + destruct (IHr _ Hin) as [k Hk]; exists (xI k); cbn; rewrite Hk; reflexivity.
Qed.

(** ** Moving subtries between bases *)

Lemma ainv_node_ann a l o r :
  ainv (ANode a l o r) -> forall k, cget a k = lmin (map (unshift a) (aelems l ++ oelems o ++ aelems r)) k.
Proof. intros [H _]; exact H. Qed.

Lemma aget_arebase m t k :
  ainv t -> cle m (aann t) -> aget k (arebase m t) = option_map (shift m) (aget k t).
Proof.
  destruct t as [|a l o r]; intros Ht Hm; [reflexivity|]; cbn [arebase aget].
  fold (asub k l o r); destruct (asub k l o r) as [e|] eqn:E; [|reflexivity]; cbn [option_map].
  f_equal; apply (rebase_one a _ (ainv_node_ann _ _ _ _ Ht)); [exact Hm|].
  apply (asub_in k l o r e E).
Qed.

Lemma aelems_arebase m t :
  ainv t -> cle m (aann t) -> aelems (arebase m t) = map (shift m) (aelems t).
Proof.
  destruct t as [|a l o r]; intros Ht Hm; [reflexivity|].
  apply (rebase_list a); [apply (ainv_node_ann _ _ _ _ Ht)|exact Hm].
Qed.

Lemma ainv_arebase m t : ainv t -> cle m (aann t) -> ainv (arebase m t).
Proof.
  intros Ht Hm; pose proof (aelems_arebase m t Ht Hm) as He.
  destruct t as [|a l o r]; [exact I|]; cbn [arebase ainv] in *.
  destruct Ht as [Ha Hs]; split; [|exact Hs]; intro k.
  rewrite He, lmin_shift, cget_csub, Ha; reflexivity.
Qed.

Lemma aget_alift d t k : ainv t -> aget k (alift d t) = option_map (unshift d) (aget k t).
Proof.
  destruct t as [|a l o r]; intros Ht; [reflexivity|]; cbn [alift aget].
  fold (asub k l o r); destruct (asub k l o r) as [e|] eqn:E; [|reflexivity]; cbn [option_map].
  f_equal; apply (lift_one a _ (ainv_node_ann _ _ _ _ Ht)), (asub_in k l o r e E).
Qed.

Lemma aelems_alift d t : ainv t -> aelems (alift d t) = map (unshift d) (aelems t).
Proof.
  destruct t as [|a l o r]; intros Ht; [reflexivity|].
  apply (lift_list a), (ainv_node_ann _ _ _ _ Ht).
Qed.

Lemma ainv_alift d t : ainv t -> ainv (alift d t).
Proof.
  intros Ht; pose proof (aelems_alift d t Ht) as He.
  destruct t as [|a l o r]; [exact I|]; cbn [alift ainv] in *.
  destruct Ht as [Ha Hs]; split; [|exact Hs]; intro k.
  rewrite He, lmin_unshift, cget_cadd, Ha; reflexivity.
Qed.

(** ** Building nodes *)

Definition amknode (l : atrie) (o : option X) (r : atrie) : atrie :=
  let m := cmin (aann l) (cmin (ouses o) (aann r)) in
  ANode m (arebase m l) (option_map (shift m) o) (arebase m r).

Lemma amk_amknode l o r : anonempty l o r -> amk l o r = amknode l o r.
Proof. destruct l, o, r; cbn; tauto. Qed.

Lemma lmin_oelems o k : lmin (oelems o) k = cget (ouses o) k.
Proof. destruct o; [apply lmin_single|reflexivity]. Qed.

Lemma cle_ouses m o e : cle m (ouses o) -> In e (oelems o) -> cle m (uses e).
Proof. destruct o; [intros H [<-|[]]; exact H|intros _ []]. Qed.

Definition anm (l : atrie) (o : option X) (r : atrie) : counts :=
  cmin (aann l) (cmin (ouses o) (aann r)).

Lemma omap_aback (f g : X -> X) o : (forall x, o = Some x -> f (g x) = x) -> option_map f (option_map g o) = o.
Proof. destruct o as [x|]; cbn; [intros H; rewrite (H x eq_refl); reflexivity|reflexivity]. Qed.

Lemma aback_l l o r e : ainv l -> In e (aelems l) -> unshift (anm l o r) (shift (anm l o r) e) = e.
Proof.
  intros Hl Hin; apply unshift_shift.
  apply (cle_mem _ (aann l) (aelems l)); [apply cle_min3_1|apply ainv_ann, Hl|exact Hin].
Qed.

Lemma aback_r l o r e : ainv r -> In e (aelems r) -> unshift (anm l o r) (shift (anm l o r) e) = e.
Proof.
  intros Hr Hin; apply unshift_shift.
  apply (cle_mem _ (aann r) (aelems r)); [apply cle_min3_3|apply ainv_ann, Hr|exact Hin].
Qed.

Lemma aback_o l o r x : o = Some x -> unshift (anm l o r) (shift (anm l o r) x) = x.
Proof. intros ->; apply unshift_shift, cle_min3_2. Qed.

Lemma aelems_amknode l o r :
  ainv l -> ainv r -> aelems (amknode l o r) = aelems l ++ oelems o ++ aelems r.
Proof.
  intros Hl Hr; unfold amknode; fold (anm l o r); cbn [aelems].
  rewrite !aelems_arebase by (assumption || apply cle_min3_1 || apply cle_min3_3).
  rewrite !map_app, !map_map; f_equal; [apply map_id_in; intros; apply aback_l; assumption|f_equal].
  - destruct o as [x|]; [cbn; f_equal; apply aback_o; reflexivity|reflexivity].
  - apply map_id_in; intros; apply aback_r; assumption.
Qed.

Lemma aget_amknode l o r k : ainv l -> ainv r -> aget k (amknode l o r) = asub k l o r.
Proof.
  intros Hl Hr; unfold amknode; fold (anm l o r); cbn [aget]; destruct k as [k|k|]; cbn [asub].
  - rewrite aget_arebase by (assumption || apply cle_min3_3).
    destruct (aget k r) as [e|] eqn:E; [|reflexivity]; cbn; f_equal; apply aback_r, (aget_in _ _ _ E); assumption.
  - rewrite aget_arebase by (assumption || apply cle_min3_1).
    destruct (aget k l) as [e|] eqn:E; [|reflexivity]; cbn; f_equal; apply aback_l, (aget_in _ _ _ E); assumption.
  - destruct o as [x|]; [cbn; f_equal; apply aback_o; reflexivity|reflexivity].
Qed.

Lemma ainv_amknode l o r : ainv l -> ainv r -> anonempty l o r -> ainv (amknode l o r).
Proof.
  intros Hl Hr Hne; pose proof (aelems_amknode l o r Hl Hr) as He.
  unfold amknode in *; fold (anm l o r) in *.
  cbn [ainv]; split; [|split; [|split]].
  - intro k; rewrite He, !lmin_app, lmin_oelems, <- !ainv_ann by assumption.
    unfold anm; rewrite !cget_cmin; reflexivity.
  - destruct l, o, r; cbn in *; tauto.
  - apply ainv_arebase; [exact Hl|apply cle_min3_1].
  - apply ainv_arebase; [exact Hr|apply cle_min3_3].
Qed.

Theorem amk_spec l o r :
  ainv l -> ainv r ->
  ainv (amk l o r) /\ aelems (amk l o r) = aelems l ++ oelems o ++ aelems r
  /\ forall k, aget k (amk l o r) = asub k l o r.
Proof.
  intros Hl Hr.
  assert (Hne : anonempty l o r \/ (l = AEmpty /\ o = None /\ r = AEmpty))
    by (destruct l, o, r; cbn; auto).
  destruct Hne as [Hne|[-> [-> ->]]].
  - rewrite amk_amknode by exact Hne.
    split; [apply ainv_amknode; assumption|split; [apply aelems_amknode|intro k; apply aget_amknode]; assumption].
  - split; [exact I|split; [reflexivity|intros [k|k|]; reflexivity]].
Qed.

(** ** Updates *)

Lemma aparts_spec t :
  ainv t ->
  match aparts t with
  | (l, o, r) => ainv l /\ ainv r /\ forall k, aget k t = asub k l o r
  end.
Proof.
  destruct t as [|a l o r]; cbn [aparts].
  - intros _; repeat split; intros [k|k|]; reflexivity.
  - intros Ht; pose proof Ht as [_ [_ [Hl Hr]]].
    split; [apply ainv_alift, Hl|split; [apply ainv_alift, Hr|]].
    intros [k|k|]; cbn [aget asub]; rewrite ?aget_alift by assumption; reflexivity.
Qed.

Theorem aupdate_spec k f t :
  ainv t ->
  ainv (aupdate k f t)
  /\ forall k', aget k' (aupdate k f t) = if Pos.eqb k' k then f (aget k t) else aget k' t.
Proof.
  revert t; induction k as [k IH|k IH|]; intros t Ht; cbn [aupdate];
    pose proof (aparts_spec t Ht) as P; destruct (aparts t) as [[l o] r];
    destruct P as [Hl [Hr Hg]].
  - destruct (IH r Hr) as [Hr' Hg'].
    destruct (amk_spec l o (aupdate k f r) Hl Hr') as [H1 [_ H3]].
    split; [exact H1|]; intros k'; rewrite H3, !Hg.
    destruct k' as [k'|k'|]; cbn [asub Pos.eqb]; [rewrite Hg'|reflexivity|reflexivity].
    reflexivity.
  - destruct (IH l Hl) as [Hl' Hg'].
    destruct (amk_spec (aupdate k f l) o r Hl' Hr) as [H1 [_ H3]].
    split; [exact H1|]; intros k'; rewrite H3, !Hg.
    destruct k' as [k'|k'|]; cbn [asub Pos.eqb]; [reflexivity|rewrite Hg'|reflexivity].
    reflexivity.
  - destruct (amk_spec l (f o) r Hl Hr) as [H1 [_ H3]].
    split; [exact H1|]; intros k'; rewrite H3, !Hg.
    destruct k' as [k'|k'|]; reflexivity.
Qed.

(** ** Incremental updates

    [aupdate] rebuilds every node on the path from its children, which
    costs the size of their count maps.  When the caller knows which labels
    the change can affect, the path can instead be patched at those labels
    only:

    - on the way down, each node is lowered to an envelope [E] (relative to
      the node's parent) that the new element's uses are known to stay
      above, moving its children and element up by the difference
      ([cexcess], only at [E]'s labels), so nothing below goes negative;
    - on the way up, each node's counts are recomputed at the labels [D]
      from its children, and the children and element are moved by the
      change ([araise]).

    [f B o] computes the new element from the old one, both stored over
    the lazy base [B] (Counts.v). *)

Definition amin3 (l : atrie) (o : option X) (r : atrie) (k : positive) : option nat :=
  omin (cget (aann l) k) (omin (cget (ouses o) k) (cget (aann r) k)).

(** A node over [l o r], stored relative to the base [a1], whose counts
    are only wrong at the labels [D]: [e] is how far the minimum below has
    moved up at those labels. *)
Definition araise_e (D : list positive) (l : atrie) (o : option X) (r : atrie) : counts :=
  fold_left (fun c k => cset c k (amin3 l o r k)) D cnone.

Definition araise_a (D : list positive) (a1 : counts) (l : atrie) (o : option X) (r : atrie) : counts :=
  fold_left (fun c k => cset c k (match amin3 l o r k with
                                   | Some n => Some (oval (cget a1 k) + n)
                                   | None => None
                                   end)) D a1.

Definition araisenode (D : list positive) (a1 : counts) (l : atrie) (o : option X) (r : atrie) : atrie :=
  let e := araise_e D l o r in
  ANode (araise_a D a1 l o r) (arebase e l) (option_map (shift e) o) (arebase e r).

Definition araise (D : list positive) (a1 : counts) (l : atrie) (o : option X) (r : atrie) : atrie :=
  match l, o, r with
  | AEmpty, None, AEmpty => AEmpty
  | _, _, _ => araisenode D a1 l o r
  end.

Fixpoint aupd (k : positive) (f : lbase -> option X -> option X) (E : counts) (D : list positive)
  (B : lbase) (t : atrie) {struct k} : atrie :=
  match t with
  | AEmpty => aupdate k (f B) AEmpty
  | ANode a l o r =>
      let a1 := cmin a E in
      let d := cexcess a E in
      let l1 := alift d l in
      let o1 := option_map (unshift d) o in
      let r1 := alift d r in
      let B1 := LPlus B a1 in
      let E1 := csub E a1 in
      match k with
      | xH => araise D a1 l1 (f B1 o1) r1
      | xO k' => araise D a1 (aupd k' f E1 D B1 l1) o1 r1
      | xI k' => araise D a1 l1 o1 (aupd k' f E1 D B1 r1)
      end
  end.

Lemma cget_fold_cset (g : positive -> option nat) D : forall c q,
  cget (fold_left (fun c k => cset c k (g k)) D c) q = if existsb (Pos.eqb q) D then g q else cget c q.
Proof.
  induction D as [|k D IH]; intros c q; [reflexivity|]; cbn [fold_left existsb].
  rewrite IH, cget_cset; destruct (Pos.eqb_spec q k) as [->|]; cbn [orb];
    [destruct (existsb _ D); reflexivity|reflexivity].
Qed.

Lemma existsb_in q D : existsb (Pos.eqb q) D = true <-> In q D.
Proof.
  rewrite existsb_exists; split; [intros [k [Hk E]]; apply Pos.eqb_eq in E; subst; exact Hk|].
  intros H; exists q; split; [exact H|apply Pos.eqb_refl].
Qed.

Lemma amin3_lmin l o r k :
  ainv l -> ainv r -> amin3 l o r k = lmin (aelems l ++ oelems o ++ aelems r) k.
Proof.
  intros Hl Hr; unfold amin3; rewrite !lmin_app, lmin_oelems, <- !ainv_ann by assumption; reflexivity.
Qed.

Lemma araise_node D a1 l o r : anonempty l o r -> araise D a1 l o r = araisenode D a1 l o r.
Proof. destruct l, o, r; cbn; tauto. Qed.

Theorem araise_spec D a1 l o r :
  ainv l -> ainv r ->
  (forall k, ~ In k D -> amin3 l o r k = match cget a1 k with Some _ => Some 0 | None => None end) ->
  ainv (araise D a1 l o r)
  /\ (forall k, aget k (araise D a1 l o r) = option_map (unshift a1) (asub k l o r))
  /\ (forall k, ~ In k D -> cget (aann (araise D a1 l o r)) k = cget a1 k).
Proof.
  intros Hl Hr Hout.
  set (L := aelems l ++ oelems o ++ aelems r).
  assert (Hne : anonempty l o r \/ (l = AEmpty /\ o = None /\ r = AEmpty))
    by (destruct l, o, r; cbn; auto).
  destruct Hne as [Hne|[-> [-> ->]]].
  2:{ cbn [araise]; split; [exact I|split; [intros [k|k|]; reflexivity|]].
      intros k Hk; specialize (Hout k Hk); unfold amin3 in Hout; cbn in Hout.
      destruct (cget a1 k); [discriminate|reflexivity]. }
  rewrite araise_node by exact Hne; unfold araisenode.
  set (e := araise_e D l o r); set (a2 := araise_a D a1 l o r).
  assert (Ee : forall q, cget e q = if existsb (Pos.eqb q) D then amin3 l o r q else None)
    by (intro q; unfold e, araise_e; rewrite cget_fold_cset; reflexivity).
  assert (Ea2 : forall q, cget a2 q = if existsb (Pos.eqb q) D
                                       then match amin3 l o r q with Some n => Some (oval (cget a1 q) + n) | None => None end
                                       else cget a1 q)
    by (intro q; unfold a2, araise_a; rewrite cget_fold_cset; reflexivity).
  assert (Hmin : forall q, amin3 l o r q = lmin L q) by (intro q; apply amin3_lmin; assumption).
  assert (Hle : forall x, In x L -> cle e (uses x)).
  { intros x Hx q n m En Em; rewrite Ee in En; destruct (existsb _ D); [|discriminate].
    rewrite Hmin in En; destruct (lmin_le L x q m Hx Em) as [n' [E' Hn']]; congruence. }
  assert (Hlel : cle e (aann l)).
  { intros q n m En Em; rewrite Ee in En; destruct (existsb _ D); [|discriminate].
    unfold amin3 in En; rewrite Em in En; destruct (cget (ouses o) q), (cget (aann r) q); cbn in En;
      injection En as <-; lia. }
  assert (Hler : cle e (aann r)).
  { intros q n m En Em; rewrite Ee in En; destruct (existsb _ D); [|discriminate].
    unfold amin3 in En; rewrite Em in En; destruct (cget (aann l) q), (cget (ouses o) q); cbn in En;
      try (injection En as <-); lia. }
  assert (Hback : forall x, In x L -> unshift a2 (shift e x) = unshift a1 x).
  { intros x Hx.
    rewrite <- (unshift_shift e x (Hle x Hx)) at 2.
    rewrite unshift_unshift; apply unshift_ext; intros q Hq.
    rewrite uses_shift in Hq.
    rewrite dval_cplus; unfold dval; rewrite Ea2, Ee.
    destruct (cget (uses x) q) as [u|] eqn:Eu; [|contradiction Hq; reflexivity].
    destruct (lmin_le L x q u Hx Eu) as [n [En _]]; rewrite <- Hmin in En.
    destruct (existsb _ D); [rewrite En; cbn; lia|cbn; lia]. }
  assert (Hsub : forall k, asub k (arebase e l) (option_map (shift e) o) (arebase e r)
                           = option_map (shift e) (asub k l o r)).
  { intros [k|k|]; cbn [asub]; [apply aget_arebase; assumption|apply aget_arebase; assumption|reflexivity]. }
  assert (Hel : aelems (arebase e l) ++ oelems (option_map (shift e) o) ++ aelems (arebase e r) = map (shift e) L).
  { unfold L; rewrite !aelems_arebase, !map_app by assumption; f_equal; f_equal; destruct o; reflexivity. }
  split; [|split].
  - cbn [ainv]; split; [|split; [|split]].
    + intro q; cbn [aelems]; rewrite Hel, map_map, (map_ext_in _ _ L Hback), lmin_unshift, <- Hmin, Ea2.
      destruct (existsb (Pos.eqb q) D) eqn:Ex.
      * destruct (amin3 l o r q); [cbn; destruct (cget a1 q); reflexivity|reflexivity].
      * rewrite Hout by (intro H; apply existsb_in in H; congruence).
        destruct (cget a1 q); cbn; [f_equal; lia|reflexivity].
    + destruct l, o, r; cbn in Hne |- *; tauto.
    + apply ainv_arebase; assumption.
    + apply ainv_arebase; assumption.
  - intros k; cbn [aget]; fold (asub k (arebase e l) (option_map (shift e) o) (arebase e r)); rewrite Hsub.
    destruct (asub k l o r) as [x|] eqn:Ex; [|reflexivity]; cbn [option_map]; f_equal.
    apply Hback, (asub_in _ _ _ _ _ Ex).
  - intros q Hq; cbn [aann]; rewrite Ea2.
    destruct (existsb (Pos.eqb q) D) eqn:Ex; [apply existsb_in in Ex; contradiction|reflexivity].
Qed.

Lemma ouses_unshift d (o : option X) q :
  cget (ouses (option_map (unshift d) o)) q = oadd (cget d q) (cget (ouses o) q).
Proof. destruct o as [x|]; [apply uses_unshift|reflexivity]. Qed.

Lemma oadd_inj d x y : oadd d x = oadd d y -> x = y.
Proof. destruct x, y; cbn; try discriminate; [intros [= E]; f_equal; lia|reflexivity]. Qed.

Lemma aann_alift d t q : cget (aann (alift d t)) q = oadd (cget d q) (cget (aann t) q).
Proof. destruct t; cbn [alift aann]; [reflexivity|apply cget_cadd]. Qed.

(** A frame with the envelope above it. *)
Lemma frame_cle B' E' Eabs :
  (forall q, cget (cadd (lcounts B') E') q = cget Eabs q) -> cle (lcounts B') Eabs.
Proof.
  intros HE q b n Hb Hn; rewrite <- HE, cget_cadd, Hb in Hn.
  destruct (cget E' q); cbn in Hn; [injection Hn as <-; lia|discriminate].
Qed.

(** A trie with one element. *)
Lemma aann_single k (o : option X) t :
  ainv t -> (forall q, aget q t = if Pos.eqb q k then o else None) ->
  forall q, cget (aann t) q = cget (ouses o) q.
Proof.
  intros Ht Hg q; rewrite (ainv_ann t Ht); rewrite <- lmin_oelems; apply lmin_same_members.
  intros e; split; intros Hin.
  - destruct (aelems_aget t e Hin) as [k' Hk]; rewrite Hg in Hk.
    destruct (Pos.eqb k' k); [|discriminate]; subst o; left; reflexivity.
  - destruct o as [x|]; [destruct Hin as [<-|[]]|destruct Hin].
    apply (aget_in k); rewrite Hg, Pos.eqb_refl; reflexivity.
Qed.

Section Aupd.

(** [F] is the change, on elements made absolute; [f B o] computes it on
    [o] stored over the frame [B], as long as the frame is below the
    envelope [Eabs] and the element satisfies [Pa] (made absolute).  The
    change only affects uses at [D]. *)
Variables (f : lbase -> option X -> option X) (F : option X -> option X) (D : list positive)
  (Eabs : counts) (Pa : X -> Prop).
Hypothesis HfF : forall B' o, (forall x, o = Some x -> Pa (unshift (lcounts B') x)) ->
  cle (lcounts B') Eabs ->
  option_map (unshift (lcounts B')) (f B' o) = F (option_map (unshift (lcounts B')) o).
Hypothesis HFD : forall o, (forall x, o = Some x -> Pa x) ->
  forall q, ~ In q D -> cget (ouses (F o)) q = cget (ouses o) q.

Lemma frame_f B' E' o :
  (forall x, o = Some x -> Pa (unshift (lcounts B') x)) ->
  (forall q, cget (cadd (lcounts B') E') q = cget Eabs q) ->
  option_map (unshift (lcounts B')) (f B' o) = F (option_map (unshift (lcounts B')) o)
  /\ forall q, ~ In q D -> cget (ouses (f B' o)) q = cget (ouses o) q.
Proof.
  intros HP HE.
  assert (E1 : option_map (unshift (lcounts B')) (f B' o) = F (option_map (unshift (lcounts B')) o))
    by (apply HfF; [exact HP|apply (frame_cle B' E' Eabs HE)]).
  split; [exact E1|]; intros q Hq.
  assert (HPa : forall x, option_map (unshift (lcounts B')) o = Some x -> Pa x)
    by (intros x Ex; destruct o as [y|]; [injection Ex as <-; apply HP; reflexivity|discriminate]).
  pose proof (HFD _ HPa q Hq) as H; rewrite <- E1, !ouses_unshift in H; apply oadd_inj in H; exact H.
Qed.

Theorem aupd_spec k : forall E B t,
  ainv t ->
  (forall q, ~ In q D -> cget E q = None) ->
  (forall q, cget (cadd (lcounts B) E) q = cget Eabs q) ->
  (forall x, aget k t = Some x -> Pa (unshift (lcounts B) x)) ->
  ainv (aupd k f E D B t)
  /\ (forall q, q <> k -> aget q (aupd k f E D B t) = aget q t)
  /\ option_map (unshift (lcounts B)) (aget k (aupd k f E D B t))
     = F (option_map (unshift (lcounts B)) (aget k t))
  /\ (forall q, ~ In q D -> cget (aann (aupd k f E D B t)) q = cget (aann t) q).
Proof.
  induction k as [k IH|k IH|]; intros E B t Ht HED HE HPk.
  all: destruct t as [|a l o r].
  (* an empty trie: a path of new nodes *)
  1,3,5: cbn [aupd];
    destruct (frame_f B E None (fun x H => match H with end) HE) as [Ef Df];
    match goal with |- context [aupdate ?kk _ AEmpty] =>
      destruct (aupdate_spec kk (f B) AEmpty I) as [Hi Hg] end;
    (split; [exact Hi|split; [intros q Hq; rewrite Hg; apply Pos.eqb_neq in Hq; rewrite Hq; reflexivity|split]]);
    [rewrite Hg, Pos.eqb_refl; exact Ef
    |intros q Hq; rewrite (aann_single _ (f B None) _ Hi Hg); apply (Df q Hq)].
  all: pose proof (ainv_node_ann _ _ _ _ Ht) as Ha; destruct Ht as [_ [_ [Hl Hr]]].
  all: set (L := aelems l ++ oelems o ++ aelems r) in *.
  all: set (a1 := cmin a E); set (d := cexcess a E).
  all: assert (Hd_out : forall q, ~ In q D -> cget d q = None)
         by (intros q Hq; unfold d, cexcess; rewrite cget_cmap2, (HED q Hq); reflexivity).
  all: assert (Ha1_out : forall q, ~ In q D -> cget a1 q = cget a q)
         by (intros q Hq; unfold a1; rewrite cget_cmin, (HED q Hq); destruct (cget a q); reflexivity).
  all: assert (Hback : forall x, In x L -> unshift a1 (unshift d x) = unshift a x)
         by (intros x Hx; rewrite unshift_unshift; apply unshift_ext; intros q Hq;
             rewrite dval_cplus; apply dval_cexcess, (uses_below a L Ha x q Hx Hq)).
  all: assert (HE1 : forall q, cget (cadd (lcounts (LPlus B a1)) (csub E a1)) q = cget Eabs q)
         by (intro q; rewrite <- HE; cbn [lcounts]; rewrite !cget_cadd, cget_cplus, cget_csub;
             unfold a1; rewrite cget_cmin; destruct (cget E q) as [e|], (cget a q) as [x|], (cget (lcounts B) q);
             cbn; try reflexivity; f_equal; lia).
  all: assert (HED1 : forall q, ~ In q D -> cget (csub E a1) q = None)
         by (intros q Hq; rewrite cget_csub, (HED q Hq); reflexivity).
  all: assert (Hl1 : ainv (alift d l)) by apply ainv_alift, Hl.
  all: assert (Hr1 : ainv (alift d r)) by apply ainv_alift, Hr.
  (* outside [D], nothing below moved *)
  all: assert (Hout0 : forall q, ~ In q D ->
                 amin3 (alift d l) (option_map (unshift d) o) (alift d r) q
                 = match cget a1 q with Some _ => Some 0 | None => None end)
         by (intros q Hq; unfold amin3; rewrite !aann_alift, ouses_unshift, Hd_out, Ha1_out by exact Hq;
             pose proof (Ha q) as Eq; rewrite lmin_unshift in Eq; unfold L in Eq; rewrite <- (amin3_lmin l o r q Hl Hr) in Eq; unfold amin3 in *;
             destruct (cget (aann l) q) as [x|], (cget (ouses o) q) as [y|], (cget (aann r) q) as [z|], (cget a q) as [w|];
             cbn in Eq |- *; try discriminate; try reflexivity; injection Eq; intros; f_equal; lia).
  all: assert (InL : forall x, In x (aelems l) \/ o = Some x \/ In x (aelems r) -> In x L)
         by (intros x [H|[H|H]]; unfold L; apply in_or_app;
             [left; exact H|right; apply in_or_app; left; subst o; left; reflexivity
             |right; apply in_or_app; right; exact H]).
  all: assert (Same_l : forall q, option_map (unshift a1) (aget q (alift d l)) = aget (xO q) (ANode a l o r))
         by (intros q; cbn [aget asub]; rewrite aget_alift by exact Hl;
             destruct (aget q l) as [x|] eqn:Ex; [cbn; f_equal; apply Hback, InL; left; apply (aget_in _ _ _ Ex)|reflexivity]).
  all: assert (Same_r : forall q, option_map (unshift a1) (aget q (alift d r)) = aget (xI q) (ANode a l o r))
         by (intros q; cbn [aget asub]; rewrite aget_alift by exact Hr;
             destruct (aget q r) as [x|] eqn:Ex; [cbn; f_equal; apply Hback, InL; right; right; apply (aget_in _ _ _ Ex)|reflexivity]).
  all: assert (Same_o : option_map (unshift a1) (option_map (unshift d) o) = aget xH (ANode a l o r))
         by (cbn [aget asub]; destruct o as [x|]; [cbn; f_equal; apply Hback, InL; right; left; reflexivity|reflexivity]).
  all: assert (Back : forall y : option X, option_map (unshift (lcounts B)) (option_map (unshift a1) y)
                                       = option_map (unshift (lcounts (LPlus B a1))) y)
         by (intros y; cbn [lcounts]; apply omap_unshift2).
  all: cbn [aupd]; fold a1 d.
  - (* right *)
    assert (HP' : forall x, aget k (alift d r) = Some x -> Pa (unshift (lcounts (LPlus B a1)) x))
      by (intros x Ex; specialize (HPk (unshift a1 x)); rewrite <- Same_r, Ex in HPk;
          cbn [lcounts]; rewrite <- unshift_unshift; exact (HPk eq_refl)).
    destruct (IH (csub E a1) (LPlus B a1) (alift d r) Hr1 HED1 HE1 HP') as [Hi' [Hg' [Hk' Ha']]].
    set (r' := aupd k f (csub E a1) D (LPlus B a1) (alift d r)) in *.
    assert (Hout : forall q, ~ In q D -> amin3 (alift d l) (option_map (unshift d) o) r' q
                                         = match cget a1 q with Some _ => Some 0 | None => None end)
      by (intros q Hq; specialize (Hout0 q Hq); unfold amin3 in *; rewrite Ha' by exact Hq; exact Hout0).
    destruct (araise_spec D a1 (alift d l) (option_map (unshift d) o) r' Hl1 Hi' Hout) as [A1 [A2 A3]].
    split; [exact A1|split; [|split]].
    + intros [q|q|] Hq; rewrite A2; cbn [asub]; [rewrite Hg' by congruence|apply Same_l|apply Same_o]; apply Same_r.
    + rewrite A2; cbn [asub]; rewrite Back, Hk', <- Back, Same_r; reflexivity.
    + intros q Hq; rewrite A3 by exact Hq; apply Ha1_out, Hq.
  - (* left *)
    assert (HP' : forall x, aget k (alift d l) = Some x -> Pa (unshift (lcounts (LPlus B a1)) x))
      by (intros x Ex; specialize (HPk (unshift a1 x)); rewrite <- Same_l, Ex in HPk;
          cbn [lcounts]; rewrite <- unshift_unshift; exact (HPk eq_refl)).
    destruct (IH (csub E a1) (LPlus B a1) (alift d l) Hl1 HED1 HE1 HP') as [Hi' [Hg' [Hk' Ha']]].
    set (l' := aupd k f (csub E a1) D (LPlus B a1) (alift d l)) in *.
    assert (Hout : forall q, ~ In q D -> amin3 l' (option_map (unshift d) o) (alift d r) q
                                         = match cget a1 q with Some _ => Some 0 | None => None end)
      by (intros q Hq; specialize (Hout0 q Hq); unfold amin3 in *; rewrite Ha' by exact Hq; exact Hout0).
    destruct (araise_spec D a1 l' (option_map (unshift d) o) (alift d r) Hi' Hr1 Hout) as [A1 [A2 A3]].
    split; [exact A1|split; [|split]].
    + intros [q|q|] Hq; rewrite A2; cbn [asub]; [apply Same_r|rewrite Hg' by congruence; apply Same_l|apply Same_o].
    + rewrite A2; cbn [asub]; rewrite Back, Hk', <- Back, Same_l; reflexivity.
    + intros q Hq; rewrite A3 by exact Hq; apply Ha1_out, Hq.
  - (* here *)
    assert (HP' : forall x, option_map (unshift d) o = Some x -> Pa (unshift (lcounts (LPlus B a1)) x))
      by (intros x Ex; specialize (HPk (unshift a1 x)); rewrite <- Same_o, Ex in HPk;
          cbn [lcounts]; rewrite <- unshift_unshift; exact (HPk eq_refl)).
    destruct (frame_f (LPlus B a1) (csub E a1) (option_map (unshift d) o) HP' HE1) as [Ef Df].
    set (o' := f (LPlus B a1) (option_map (unshift d) o)) in *.
    assert (Hout : forall q, ~ In q D -> amin3 (alift d l) o' (alift d r) q
                                         = match cget a1 q with Some _ => Some 0 | None => None end)
      by (intros q Hq; specialize (Hout0 q Hq); unfold amin3 in *; rewrite Df by exact Hq; exact Hout0).
    destruct (araise_spec D a1 (alift d l) o' (alift d r) Hl1 Hr1 Hout) as [A1 [A2 A3]].
    split; [exact A1|split; [|split]].
    + intros [q|q|] Hq; rewrite A2; cbn [asub]; [apply Same_r|apply Same_l|congruence].
    + rewrite A2; cbn [asub]; rewrite Back, Ef, <- Back, Same_o; reflexivity.
    + intros q Hq; rewrite A3 by exact Hq; apply Ha1_out, Hq.
Qed.

End Aupd.

(** ** Canonicity *)

Lemma aelems_anonempty t : ainv t -> t <> AEmpty -> aelems t <> [].
Proof.
  induction t as [|a l IHl o r IHr]; [congruence|]; intros Ht _; cbn [aelems].
  destruct Ht as [_ [Hne [Hl Hr]]].
  intros E; apply map_eq_nil in E; apply app_eq_nil in E as [El E]; apply app_eq_nil in E as [Eo Er].
  destruct l; [|apply (IHl Hl ltac:(discriminate) El)].
  destruct r; [|apply (IHr Hr ltac:(discriminate) Er)].
  destruct o; [discriminate|exact Hne].
Qed.

Theorem acanonical t1 t2 : ainv t1 -> ainv t2 -> (forall k, aget k t1 = aget k t2) -> t1 = t2.
Proof.
  assert (Hkey : forall t, ainv t -> t <> AEmpty -> exists k e, aget k t = Some e).
  { intros t Ht Hne; destruct (aelems t) as [|e es] eqn:E; [contradiction (aelems_anonempty t Ht Hne)|].
    destruct (aelems_aget t e) as [k Hk]; [rewrite E; left; reflexivity|eauto]. }
  revert t2; induction t1 as [|a1 l1 IHl o1 r1 IHr]; intros [|a2 l2 o2 r2] H1 H2 Heq.
  - reflexivity.
  - destruct (Hkey _ H2 ltac:(discriminate)) as [k [e He]]; rewrite <- Heq in He; discriminate.
  - destruct (Hkey _ H1 ltac:(discriminate)) as [k [e He]]; rewrite Heq in He; discriminate.
  - assert (Ha : a1 = a2).
    { apply counts_ext; intro k.
      transitivity (lmin (aelems (ANode a1 l1 o1 r1)) k); [apply (ainv_ann _ H1)|].
      transitivity (lmin (aelems (ANode a2 l2 o2 r2)) k); [|symmetry; apply (ainv_ann _ H2)].
      apply lmin_same_members.
      intros e; split; intros Hin; [destruct (aelems_aget _ e Hin) as [k' Hk]; rewrite Heq in Hk
                                  |destruct (aelems_aget _ e Hin) as [k' Hk]; rewrite <- Heq in Hk];
        apply (aget_in k' _ e Hk). }
    subst a2.
    assert (Hsub : forall k, asub k l1 o1 r1 = asub k l2 o2 r2).
    { intros k; specialize (Heq k); cbn [aget] in Heq; fold (asub k l1 o1 r1) (asub k l2 o2 r2) in Heq.
      destruct (asub k l1 o1 r1) as [x|] eqn:E1, (asub k l2 o2 r2) as [y|] eqn:E2;
        cbn in Heq; try discriminate; [|reflexivity].
      injection Heq as Heq; f_equal; apply (unshift_inj a1), Heq. }
    destruct H1 as [_ [_ [Hl1 Hr1]]], H2 as [_ [_ [Hl2 Hr2]]].
    f_equal; [apply IHl; [assumption|assumption|intro k; apply (Hsub (xO k))]
             |apply (Hsub xH)
             |apply IHr; [assumption|assumption|intro k; apply (Hsub (xI k))]].
Qed.

(** ** The entries with their keys *)

Fixpoint akeyed (kf : positive -> positive) (t : atrie) : list (positive * X) :=
  match t with
  | AEmpty => []
  | ANode a l o r =>
      map (fun kx => (fst kx, unshift a (snd kx)))
          (match o with Some x => [(kf xH, x)] | None => [] end
           ++ akeyed (fun k => kf (xO k)) l ++ akeyed (fun k => kf (xI k)) r)
  end.

Lemma akeyed_spec t : forall kf k' x,
  In (k', x) (akeyed kf t) <-> exists k, k' = kf k /\ aget k t = Some x.
Proof.
  induction t as [|a l IHl o r IHr]; intros kf k' x; cbn [akeyed].
  - split; [intros []|intros [k [_ E]]; discriminate].
  - rewrite in_map_iff; split.
    + intros [[k0 x0] [E Hin]]; cbn in E; injection E as <- <-.
      apply in_app_or in Hin as [Hin|Hin].
      * destruct o as [y|]; [|destruct Hin]; destruct Hin as [[= <- <-]|[]].
        exists xH; split; reflexivity.
      * apply in_app_or in Hin as [Hin|Hin].
        -- apply IHl in Hin as [k [-> E]]; exists (xO k); split; [reflexivity|cbn; rewrite E; reflexivity].
        -- apply IHr in Hin as [k [-> E]]; exists (xI k); split; [reflexivity|cbn; rewrite E; reflexivity].
    + intros [k [-> E]]; cbn [aget] in E; destruct k as [k|k|].
      * destruct (aget k r) as [y|] eqn:Ey; [|discriminate]; cbn in E; injection E as <-.
        exists (kf (xI k), y); split; [reflexivity|].
        apply in_or_app; right; apply in_or_app; right; apply IHr; exists k; split; [reflexivity|exact Ey].
      * destruct (aget k l) as [y|] eqn:Ey; [|discriminate]; cbn in E; injection E as <-.
        exists (kf (xO k), y); split; [reflexivity|].
        apply in_or_app; right; apply in_or_app; left; apply IHl; exists k; split; [reflexivity|exact Ey].
      * destruct o as [y|]; [|discriminate]; cbn in E; injection E as <-.
        exists (kf xH, y); split; [reflexivity|apply in_or_app; left; left; reflexivity].
Qed.

Lemma akeyed_forallb (f : positive -> X -> bool) t :
  List.forallb (fun kx => f (fst kx) (snd kx)) (akeyed (fun k => k) t) = true
  <-> forall k x, aget k t = Some x -> f k x = true.
Proof.
  rewrite List.forallb_forall; split.
  - intros H k x E; apply (H (k, x)), akeyed_spec; exists k; split; [reflexivity|exact E].
  - intros H [k x] Hin; apply akeyed_spec in Hin as [k0 [-> E]]; apply H, E.
Qed.

(** ** Deciding the invariant *)

Section Decide.

Definition anonemptyb (l : atrie) (o : option X) (r : atrie) : bool :=
  match l, o, r with AEmpty, None, AEmpty => false | _, _, _ => true end.

Fixpoint ainvb (t : atrie) : bool :=
  match t with
  | AEmpty => true
  | ANode a l o r =>
      ceqb a (lminc (aelems t)) && anonemptyb l o r && ainvb l && ainvb r
  end.

Lemma ainvb_spec t : ainvb t = true <-> ainv t.
Proof.
  induction t as [|a l IHl o r IHr]; cbn [ainvb ainv]; [split; reflexivity|].
  assert (Hne : anonemptyb l o r = true <-> anonempty l o r)
    by (destruct l, o, r; cbn; split; (discriminate || tauto || (intros; exact I) || reflexivity)).
  rewrite !andb_true_iff, ceqb_lminc, Hne, IHl, IHr; tauto.
Qed.

End Decide.

End ATrie.

Arguments atrie : clear implicits.
