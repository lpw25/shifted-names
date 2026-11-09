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

Definition arebase (d : counts) (t : atrie) : atrie :=
  match t with AEmpty => AEmpty | ANode a l o r => ANode (csub a d) l o r end.

Definition alift (d : counts) (t : atrie) : atrie :=
  match t with AEmpty => AEmpty | ANode a l o r => ANode (cadd d a) l o r end.

(** Building a node from parts relative to the parent: its counts are the
    minimum of what is below. *)
Definition mk (l : atrie) (o : option X) (r : atrie) : atrie :=
  match l, o, r with
  | AEmpty, None, AEmpty => AEmpty
  | _, _, _ =>
      let m := cmin (aann l) (cmin (ouses o) (aann r)) in
      ANode m (arebase m l) (option_map (shift m) o) (arebase m r)
  end.

(** A node's parts, relative to the parent. *)
Definition parts (t : atrie) : atrie * option X * atrie :=
  match t with
  | AEmpty => (AEmpty, None, AEmpty)
  | ANode a l o r => (alift a l, option_map (unshift a) o, alift a r)
  end.

(** Changing the element at [k]; [f] sees and returns elements relative to
    the parent's base. *)
Fixpoint aupdate (k : positive) (f : option X -> option X) (t : atrie) {struct k} : atrie :=
  match parts t with
  | (l, o, r) =>
      match k with
      | xH => mk l (f o) r
      | xO k' => mk (aupdate k' f l) o r
      | xI k' => mk l o (aupdate k' f r)
      end
  end.

(** ** Invariant *)

Definition ook (o : option X) : Prop := match o with Some x => eok x | None => True end.

Definition nonempty (l : atrie) (o : option X) (r : atrie) : Prop :=
  match l, o, r with AEmpty, None, AEmpty => False | _, _, _ => True end.

Fixpoint ainv (t : atrie) : Prop :=
  match t with
  | AEmpty => True
  | ANode a l o r =>
      (forall k, cget a k = lmin (aelems t) k) /\ cwf a /\ nonempty l o r
      /\ ook o /\ ainv l /\ ainv r
  end.

Lemma ainv_ann t : ainv t -> forall k, cget (aann t) k = lmin (aelems t) k.
Proof. destruct t; cbn [ainv aann]; [reflexivity|tauto]. Qed.

Lemma ainv_ok t : ainv t -> forall e, In e (aelems t) -> eok e.
Proof.
  induction t as [|a l IHl o r IHr]; cbn [ainv aelems]; [intros _ _ []|].
  intros [_ [_ [_ [Ho [Hl Hr]]]]] e Hin; apply in_map_iff in Hin as [e' [<- Hin]].
  apply ok_unshift; apply in_app_or in Hin as [Hin|Hin]; [apply IHl; assumption|].
  apply in_app_or in Hin as [Hin|Hin]; [|apply IHr; assumption].
  destruct o; [destruct Hin as [<-|[]]; exact Ho|destruct Hin].
Qed.

Lemma ainv_parts_ok a l o r :
  ainv (ANode a l o r) -> forall e, In e (aelems l ++ oelems o ++ aelems r) -> eok e.
Proof.
  intros [_ [_ [_ [Ho [Hl Hr]]]]] e Hin.
  apply in_app_or in Hin as [Hin|Hin]; [apply (ainv_ok l Hl _ Hin)|].
  apply in_app_or in Hin as [Hin|Hin]; [|apply (ainv_ok r Hr _ Hin)].
  destruct o; [destruct Hin as [<-|[]]; exact Ho|destruct Hin].
Qed.

(** ** Lookups and elements *)

Lemma omap_some (f : X -> X) o y : option_map f o = Some y -> exists x, o = Some x /\ y = f x.
Proof. destruct o as [x|]; cbn; [intros [= <-]; eauto|discriminate]. Qed.

Definition sub (k : positive) (l : atrie) (o : option X) (r : atrie) : option X :=
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

Lemma sub_in k l o r e : sub k l o r = Some e -> In e (aelems l ++ oelems o ++ aelems r).
Proof.
  destruct k as [k|k|]; cbn [sub]; intros He.
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
  fold (sub k l o r); destruct (sub k l o r) as [e|] eqn:E; [|reflexivity]; cbn [option_map].
  f_equal; apply (rebase_one a _ (ainv_node_ann _ _ _ _ Ht) (ainv_parts_ok _ _ _ _ Ht)); [exact Hm|].
  apply (sub_in k l o r e E).
Qed.

Lemma aelems_arebase m t :
  ainv t -> cle m (aann t) -> aelems (arebase m t) = map (shift m) (aelems t).
Proof.
  destruct t as [|a l o r]; intros Ht Hm; [reflexivity|].
  apply (rebase_list a); [apply (ainv_node_ann _ _ _ _ Ht)|apply (ainv_parts_ok _ _ _ _ Ht)|exact Hm].
Qed.

Lemma ainv_arebase m t : ainv t -> cle m (aann t) -> ainv (arebase m t).
Proof.
  intros Ht Hm; pose proof (aelems_arebase m t Ht Hm) as He.
  destruct t as [|a l o r]; [exact I|]; cbn [arebase ainv] in *.
  destruct Ht as [Ha [_ Hs]]; split; [|split; [apply cwf_cmap2|exact Hs]]; intro k.
  rewrite He, lmin_shift, cget_csub, Ha; reflexivity.
Qed.

Lemma aget_alift d t k : ainv t -> aget k (alift d t) = option_map (unshift d) (aget k t).
Proof.
  destruct t as [|a l o r]; intros Ht; [reflexivity|]; cbn [alift aget].
  fold (sub k l o r); destruct (sub k l o r) as [e|] eqn:E; [|reflexivity]; cbn [option_map].
  f_equal; apply (lift_one a _ (ainv_node_ann _ _ _ _ Ht)), (sub_in k l o r e E).
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
  destruct Ht as [Ha [_ Hs]]; split; [|split; [apply cwf_cmap2|exact Hs]]; intro k.
  rewrite He, lmin_unshift, cget_cadd, Ha; reflexivity.
Qed.

(** ** Building nodes *)

Definition mknode (l : atrie) (o : option X) (r : atrie) : atrie :=
  let m := cmin (aann l) (cmin (ouses o) (aann r)) in
  ANode m (arebase m l) (option_map (shift m) o) (arebase m r).

Lemma mk_mknode l o r : nonempty l o r -> mk l o r = mknode l o r.
Proof. destruct l, o, r; cbn; tauto. Qed.

Lemma lmin_oelems o k : lmin (oelems o) k = cget (ouses o) k.
Proof. destruct o; [apply lmin_single|reflexivity]. Qed.

Lemma cle_ouses m o e : cle m (ouses o) -> In e (oelems o) -> cle m (uses e).
Proof. destruct o; [intros H [<-|[]]; exact H|intros _ []]. Qed.

Definition nm (l : atrie) (o : option X) (r : atrie) : counts :=
  cmin (aann l) (cmin (ouses o) (aann r)).

Lemma omap_back (f g : X -> X) o : (forall x, o = Some x -> f (g x) = x) -> option_map f (option_map g o) = o.
Proof. destruct o as [x|]; cbn; [intros H; rewrite (H x eq_refl); reflexivity|reflexivity]. Qed.

Lemma back_l l o r e : ainv l -> In e (aelems l) -> unshift (nm l o r) (shift (nm l o r) e) = e.
Proof.
  intros Hl Hin; apply unshift_shift; [apply (ainv_ok l Hl _ Hin)|].
  apply (cle_mem _ (aann l) (aelems l)); [apply cle_min3_1|apply ainv_ann, Hl|exact Hin].
Qed.

Lemma back_r l o r e : ainv r -> In e (aelems r) -> unshift (nm l o r) (shift (nm l o r) e) = e.
Proof.
  intros Hr Hin; apply unshift_shift; [apply (ainv_ok r Hr _ Hin)|].
  apply (cle_mem _ (aann r) (aelems r)); [apply cle_min3_3|apply ainv_ann, Hr|exact Hin].
Qed.

Lemma back_o l o r x : o = Some x -> eok x -> unshift (nm l o r) (shift (nm l o r) x) = x.
Proof. intros -> Hx; apply unshift_shift; [exact Hx|apply cle_min3_2]. Qed.

Lemma aelems_mknode l o r :
  ainv l -> ook o -> ainv r -> aelems (mknode l o r) = aelems l ++ oelems o ++ aelems r.
Proof.
  intros Hl Ho Hr; unfold mknode; fold (nm l o r); cbn [aelems].
  rewrite !aelems_arebase by (assumption || apply cle_min3_1 || apply cle_min3_3).
  rewrite !map_app, !map_map; f_equal; [apply map_id_in; intros; apply back_l; assumption|f_equal].
  - destruct o as [x|]; [cbn; f_equal; apply back_o; [reflexivity|exact Ho]|reflexivity].
  - apply map_id_in; intros; apply back_r; assumption.
Qed.

Lemma aget_mknode l o r k : ainv l -> ook o -> ainv r -> aget k (mknode l o r) = sub k l o r.
Proof.
  intros Hl Ho Hr; unfold mknode; fold (nm l o r); cbn [aget]; destruct k as [k|k|]; cbn [sub].
  - rewrite aget_arebase by (assumption || apply cle_min3_3).
    destruct (aget k r) as [e|] eqn:E; [|reflexivity]; cbn; f_equal; apply back_r, (aget_in _ _ _ E); assumption.
  - rewrite aget_arebase by (assumption || apply cle_min3_1).
    destruct (aget k l) as [e|] eqn:E; [|reflexivity]; cbn; f_equal; apply back_l, (aget_in _ _ _ E); assumption.
  - destruct o as [x|]; [cbn; f_equal; apply back_o; [reflexivity|exact Ho]|reflexivity].
Qed.

Lemma ainv_mknode l o r : ainv l -> ook o -> ainv r -> nonempty l o r -> ainv (mknode l o r).
Proof.
  intros Hl Ho Hr Hne; pose proof (aelems_mknode l o r Hl Ho Hr) as He.
  unfold mknode in *; fold (nm l o r) in *.
  cbn [ainv]; split; [|split; [apply cwf_cmap2|split; [|split; [|split]]]].
  - intro k; rewrite He, !lmin_app, lmin_oelems, <- !ainv_ann by assumption.
    unfold nm; rewrite !cget_cmin; reflexivity.
  - destruct l, o, r; cbn in *; tauto.
  - destruct o; cbn in *; [apply ok_shift, Ho|exact I].
  - apply ainv_arebase; [exact Hl|apply cle_min3_1].
  - apply ainv_arebase; [exact Hr|apply cle_min3_3].
Qed.

Theorem mk_spec l o r :
  ainv l -> ook o -> ainv r ->
  ainv (mk l o r) /\ aelems (mk l o r) = aelems l ++ oelems o ++ aelems r
  /\ forall k, aget k (mk l o r) = sub k l o r.
Proof.
  intros Hl Ho Hr.
  assert (Hne : nonempty l o r \/ (l = AEmpty /\ o = None /\ r = AEmpty))
    by (destruct l, o, r; cbn; auto).
  destruct Hne as [Hne|[-> [-> ->]]].
  - rewrite mk_mknode by exact Hne.
    split; [apply ainv_mknode; assumption|split; [apply aelems_mknode|intro k; apply aget_mknode]; assumption].
  - split; [exact I|split; [reflexivity|intros [k|k|]; reflexivity]].
Qed.

(** ** Updates *)

Lemma parts_spec t :
  ainv t ->
  match parts t with
  | (l, o, r) => ainv l /\ ook o /\ ainv r /\ forall k, aget k t = sub k l o r
  end.
Proof.
  destruct t as [|a l o r]; cbn [parts].
  - intros _; repeat split; intros [k|k|]; reflexivity.
  - intros Ht; pose proof Ht as [_ [_ [_ [Ho [Hl Hr]]]]].
    split; [apply ainv_alift, Hl|split; [destruct o; [apply ok_unshift, Ho|exact I]|split; [apply ainv_alift, Hr|]]].
    intros [k|k|]; cbn [aget sub]; rewrite ?aget_alift by assumption; reflexivity.
Qed.

Theorem aupdate_spec k f t :
  ainv t -> (forall o, ook o -> ook (f o)) ->
  ainv (aupdate k f t)
  /\ forall k', aget k' (aupdate k f t) = if Pos.eqb k' k then f (aget k t) else aget k' t.
Proof.
  revert t; induction k as [k IH|k IH|]; intros t Ht Hf; cbn [aupdate];
    pose proof (parts_spec t Ht) as P; destruct (parts t) as [[l o] r];
    destruct P as [Hl [Ho [Hr Hg]]].
  - destruct (IH r Hr Hf) as [Hr' Hg'].
    destruct (mk_spec l o (aupdate k f r) Hl Ho Hr') as [H1 [_ H3]].
    split; [exact H1|]; intros k'; rewrite H3, !Hg.
    destruct k' as [k'|k'|]; cbn [sub Pos.eqb]; [rewrite Hg'|reflexivity|reflexivity].
    reflexivity.
  - destruct (IH l Hl Hf) as [Hl' Hg'].
    destruct (mk_spec (aupdate k f l) o r Hl' Ho Hr) as [H1 [_ H3]].
    split; [exact H1|]; intros k'; rewrite H3, !Hg.
    destruct k' as [k'|k'|]; cbn [sub Pos.eqb]; [reflexivity|rewrite Hg'|reflexivity].
    reflexivity.
  - destruct (mk_spec l (f o) r Hl (Hf o Ho) Hr) as [H1 [_ H3]].
    split; [exact H1|]; intros k'; rewrite H3, !Hg.
    destruct k' as [k'|k'|]; reflexivity.
Qed.

(** ** Canonicity *)

Lemma unshift_inj d x y : eok x -> eok y -> unshift d x = unshift d y -> x = y.
Proof. intros Hx Hy E; rewrite <- (shift_unshift d x Hx), E; apply shift_unshift, Hy. Qed.

Lemma ainv_get_ok t k e : ainv t -> aget k t = Some e -> eok e.
Proof. intros Ht He; apply (ainv_ok t Ht), (aget_in k t e He). Qed.

Lemma aelems_nonempty t : ainv t -> t <> AEmpty -> aelems t <> [].
Proof.
  induction t as [|a l IHl o r IHr]; [congruence|]; intros Ht _; cbn [aelems].
  destruct Ht as [_ [_ [Hne [_ [Hl Hr]]]]].
  intros E; apply map_eq_nil in E; apply app_eq_nil in E as [El E]; apply app_eq_nil in E as [Eo Er].
  destruct l; [|apply (IHl Hl ltac:(discriminate) El)].
  destruct r; [|apply (IHr Hr ltac:(discriminate) Er)].
  destruct o; [discriminate|exact Hne].
Qed.

Theorem acanonical t1 t2 : ainv t1 -> ainv t2 -> (forall k, aget k t1 = aget k t2) -> t1 = t2.
Proof.
  assert (Hkey : forall t, ainv t -> t <> AEmpty -> exists k e, aget k t = Some e).
  { intros t Ht Hne; destruct (aelems t) as [|e es] eqn:E; [contradiction (aelems_nonempty t Ht Hne)|].
    destruct (aelems_aget t e) as [k Hk]; [rewrite E; left; reflexivity|eauto]. }
  revert t2; induction t1 as [|a1 l1 IHl o1 r1 IHr]; intros [|a2 l2 o2 r2] H1 H2 Heq.
  - reflexivity.
  - destruct (Hkey _ H2 ltac:(discriminate)) as [k [e He]]; rewrite <- Heq in He; discriminate.
  - destruct (Hkey _ H1 ltac:(discriminate)) as [k [e He]]; rewrite Heq in He; discriminate.
  - assert (Ha : a1 = a2).
    { apply counts_ext; [apply H1|apply H2|]; intro k.
      transitivity (lmin (aelems (ANode a1 l1 o1 r1)) k); [apply (ainv_ann _ H1)|].
      transitivity (lmin (aelems (ANode a2 l2 o2 r2)) k); [|symmetry; apply (ainv_ann _ H2)].
      apply lmin_same_members.
      intros e; split; intros Hin; [destruct (aelems_aget _ e Hin) as [k' Hk]; rewrite Heq in Hk
                                  |destruct (aelems_aget _ e Hin) as [k' Hk]; rewrite <- Heq in Hk];
        apply (aget_in k' _ e Hk). }
    subst a2.
    assert (Hsub : forall k, sub k l1 o1 r1 = sub k l2 o2 r2).
    { intros k; specialize (Heq k); cbn [aget] in Heq; fold (sub k l1 o1 r1) (sub k l2 o2 r2) in Heq.
      destruct (sub k l1 o1 r1) as [x|] eqn:E1, (sub k l2 o2 r2) as [y|] eqn:E2;
        cbn in Heq; try discriminate; [|reflexivity].
      injection Heq as Heq; f_equal; apply (unshift_inj a1); [| |exact Heq].
      - apply (ainv_parts_ok _ _ _ _ H1), (sub_in _ _ _ _ _ E1).
      - apply (ainv_parts_ok _ _ _ _ H2), (sub_in _ _ _ _ _ E2). }
    destruct H1 as [_ [_ [_ [_ [Hl1 Hr1]]]]], H2 as [_ [_ [_ [_ [Hl2 Hr2]]]]].
    f_equal; [apply IHl; [assumption|assumption|intro k; apply (Hsub (xO k))]
             |apply (Hsub xH)
             |apply IHr; [assumption|assumption|intro k; apply (Hsub (xI k))]].
Qed.

End ATrie.
