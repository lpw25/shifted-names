(** * Point operations on adjustments

    Identity, weakening, extension and lifting on the representation of
    Repr.v, each specified by its effect on the meaning ([napply]) and shown
    to keep the normal form. *)

From Stdlib Require Import PArith Arith Lia List Bool.
From ShiftedNames.Core Require Import Trie Label Var Counts Based Skew ATrie Repr.
Import ListNotations.

Section Point.

Context {T : Type}.

Local Notation nadj := (@nadj T).
Local Notation result := (@result T).
Local Notation entry := (@entry T).
Local Notation target := (@target T).

(** Every label matters at the top level. *)
Definition Qall : option label -> bool := fun _ => true.

(** ** Identity *)

Definition uniform0 : counts := mk_counts (Some 0) Empty.

Definition nidentity : nadj := NAdj uniform0 AEmpty.

Lemma cget_uniform0 k : cget uniform0 k = Some 0.
Proof. reflexivity. Qed.

Theorem nlocal_identity : nlocal Qall nidentity.
Proof.
  cbn [nlocal nidentity]; split; [exact I|split; [|split; [|split; [|split]]]].
  - intros k v H; cbn in H; discriminate.
  - intros k v H; cbn in H; discriminate.
  - intros k e H; cbn in H; discriminate.
  - intros l _; discriminate.
  - intros l H; discriminate.
Qed.

Theorem napply_identity v : napply nidentity v = inl v.
Proof. destruct v as [h i]; reflexivity. Qed.

(** ** Weakening: the outputs of [h] move up by one *)

Definition weaken (h : option label) (a : nadj) : nadj :=
  match a with NAdj w es => NAdj (cadd (cone (label_key h) 1) w) es end.

(** The effect on a result. *)
Definition rweaken (h : option label) (r : result) : result :=
  match r with
  | inl w => inl (if label_eqb (v_label w) h then mk_rvar h (S (v_index w)) else w)
  | inr (u, rho) => inr (u, NAdj (cadd (cone (label_key h) 1) (nroot rho)) (nentries rho))
  end.

Lemma dval_weaken h w k :
  cget w (label_key h) <> None ->
  dval (cadd (cone (label_key h) 1) w) k = (if Pos.eqb k (label_key h) then 1 else 0) + dval w k.
Proof.
  intros Hw; unfold dval; rewrite cget_cadd, cget_cone.
  destruct (cget w k) eqn:E; destruct (Pos.eqb_spec k (label_key h)) as [->|]; cbn; try reflexivity.
  contradiction.
Qed.

Lemma cadd_weaken h w r :
  cget w (label_key h) <> None ->
  cadd (cadd (cone (label_key h) 1) w) r = cadd (cone (label_key h) 1) (cadd w r).
Proof.
  intros Hw; apply counts_ext; try apply cwf_cmap2; intro k.
  rewrite !cget_cadd, cget_cone.
  destruct (cget r k) as [m|]; [|reflexivity].
  destruct (cget w k) eqn:E; destruct (Pos.eqb_spec k (label_key h)) as [->|]; cbn;
    try contradiction; f_equal; lia.
Qed.

Theorem napply_weaken h a v :
  nlocal Qall a -> napply (weaken h a) v = rweaken h (napply a v).
Proof.
  destruct a as [w es]; intros Ha; pose proof Ha as [_ [_ [_ [_ [HQ _]]]]].
  assert (Hw : cget w (label_key h) <> None) by (apply HQ; reflexivity).
  assert (Hvar : forall y n, inl (mk_rvar y (dval (cadd (cone (label_key h) 1) w) (label_key y) + n))
                             = rweaken h (inl (mk_rvar y (dval w (label_key y) + n))) :> result).
  { intros y n; cbn [rweaken v_label v_index]; rewrite dval_weaken by exact Hw.
    rewrite label_key_eqb; destruct (label_eqb_spec y h) as [->|]; reflexivity. }
  unfold napply, weaken; destruct (aget (label_key (v_label v)) es) as [[h' ts len p]|]; [|apply Hvar].
  cbn [eapply]; destruct (Nat.ltb (v_index v) len); [|apply Hvar].
  destruct (knth ts (v_index v)) as [[y j|u [r es']]|]; [|cbn [tunshift tresult]..|apply Hvar].
  - cbn [tunshift tresult]; apply (Hvar y j).
  - cbn [rweaken nroot nentries]; rewrite cadd_weaken by exact Hw; reflexivity.
Qed.

Theorem nlocal_weaken h a : nlocal Qall a -> nlocal Qall (weaken h a).
Proof.
  destruct a as [w es]; intros [Hes [Cw [Kw [Hent [HQ HnQ]]]]].
  split; [exact Hes|split; [apply cwf_cmap2|split; [apply keyed_cmap2; [apply keyed_cone|exact Kw]|]]].
  split; [exact Hent|split; [|intros l Hl; discriminate]].
  intros l _; rewrite cget_cadd; specialize (HQ l eq_refl).
  destruct (cget w (label_key l)); [discriminate|contradiction].
Qed.

(** ** Lowering the root counts

    When something new is used below the root counts, they drop.  The
    entries move up by the difference [d] (one change at the trie's root),
    and a label without an entry whose count drops gets an explicit
    pass-through entry: it is no longer the identity relative to the root. *)

Definition gap (k : positive) (n : nat) : option entry :=
  match key_label k with
  | Some l => if Pos.eqb (label_key l) k then Some (Entry l KNil 0 n) else None
  | None => None
  end.

Definition add_gap (es : atrie entry) (kv : positive * option nat) : atrie entry :=
  match kv with
  | (k, Some (S n)) =>
      match aget k es with Some _ => es | None => aupdate k (fun _ => gap k (S n)) es end
  | _ => es
  end.

Definition add_gaps (d : counts) (es : atrie entry) : atrie entry :=
  fold_left add_gap (elements (c_exc d)) es.

Definition lower (w' : counts) (a : nadj) : nadj :=
  match a with NAdj w es => let d := csub w w' in NAdj w' (add_gaps d (alift d es)) end.

Lemma ook_gap k n : ook (gap k n).
Proof.
  unfold gap; destruct (key_label k) as [l|]; [|exact I].
  destruct (Pos.eqb _ _); [intros k' v H; cbn in H; discriminate|exact I].
Qed.

Definition lookup {A} (k : positive) (L : list (positive * A)) : option A :=
  option_map snd (find (fun kv => Pos.eqb (fst kv) k) L).

Lemma lookup_elements {A} (m : tree A) k : lookup k (elements m) = get k m.
Proof.
  unfold lookup; destruct (find _ (elements m)) as [[k' v]|] eqn:E; cbn [option_map snd].
  - apply find_some in E as [Hin Hk]; cbn in Hk; apply Pos.eqb_eq in Hk; subst k'.
    symmetry; apply In_elements, Hin.
  - destruct (get k m) as [v|] eqn:G; [|reflexivity].
    apply In_elements in G; apply (find_none _ _ E) in G; cbn in G; rewrite Pos.eqb_refl in G; discriminate.
Qed.

Lemma add_gaps_list (L : list (positive * option nat)) es :
  ainv es -> NoDup (map fst L) ->
  ainv (fold_left add_gap L es)
  /\ forall k, aget k (fold_left add_gap L es)
               = match aget k es with
                 | Some e => Some e
                 | None => match lookup k L with Some (Some (S n)) => gap k (S n) | _ => None end
                 end.
Proof.
  revert es; induction L as [|[k' v] L IH]; intros es Hes Hnd; cbn [fold_left].
  - split; [exact Hes|intro k; destruct (aget k es); reflexivity].
  - inversion Hnd as [|? ? Hni Hnd']; subst.
    assert (H1 : ainv (add_gap es (k', v))
                 /\ forall k, aget k (add_gap es (k', v))
                              = if Pos.eqb k k'
                                then match v, aget k' es with
                                     | Some (S n), None => gap k' (S n)
                                     | _, o => o
                                     end
                                else aget k es).
    { cbn [add_gap]; destruct v as [[|n]|]; [| |]; cbn.
      - split; [exact Hes|intro k; destruct (Pos.eqb_spec k k') as [->|]; [destruct (aget k' es)|]; reflexivity].
      - destruct (aget k' es) as [e|] eqn:E.
        + split; [exact Hes|intro k; destruct (Pos.eqb_spec k k') as [->|]; [rewrite E|]; reflexivity].
        + destruct (aupdate_spec k' (fun _ => gap k' (S n)) es Hes (fun _ _ => ook_gap _ _)) as [Ha Hg].
          split; [exact Ha|intro k; rewrite Hg; destruct (Pos.eqb k k'); reflexivity].
      - split; [exact Hes|intro k; destruct (Pos.eqb_spec k k') as [->|]; [destruct (aget k' es)|]; reflexivity]. }
    destruct H1 as [Ha1 Hg1]; destruct (IH _ Ha1 Hnd') as [Ha2 Hg2]; split; [exact Ha2|].
    intro k; rewrite Hg2, Hg1; unfold lookup at 2; cbn [find fst].
    destruct (Pos.eqb_spec k k') as [->|Hne].
    + assert (Hl : lookup k' L = None).
      { unfold lookup; destruct (find _ L) as [[k'' v'']|] eqn:F; [|reflexivity].
        apply find_some in F as [Hin Hk]; cbn in Hk; apply Pos.eqb_eq in Hk; subst k''.
        exfalso; apply Hni; apply in_map_iff; exists (k', v''); auto. }
      cbn [option_map snd]; rewrite Hl.
      rewrite Pos.eqb_refl; cbn [option_map snd]; destruct v as [[|n]|], (aget k' es); try destruct (gap k' (S n)); reflexivity.
    + assert (Hne' : Pos.eqb k' k = false) by (apply Pos.eqb_neq; congruence).
      rewrite Hne'; reflexivity.
Qed.

Lemma aget_add_gaps d es k :
  ainv es ->
  ainv (add_gaps d es)
  /\ aget k (add_gaps d es)
     = match aget k es with
       | Some e => Some e
       | None => match get k (c_exc d) with Some (Some (S n)) => gap k (S n) | _ => None end
       end.
Proof.
  intros Hes; destruct (add_gaps_list (elements (c_exc d)) es Hes (elements_nodup _)) as [Ha Hg].
  split; [exact Ha|]; unfold add_gaps; rewrite Hg, lookup_elements; reflexivity.
Qed.

(** The counts split: what is left plus what moved. *)
Lemma dval_split w w' k :
  cle w' w -> (forall k, cget w k = None -> oval (cget w' k) = 0) ->
  dval w' k + dval (csub w w') k = dval w k.
Proof.
  intros Hle H0; unfold dval; rewrite cget_csub.
  destruct (cget w k) as [m|] eqn:Ew, (cget w' k) as [n|] eqn:Ew'; cbn.
  - specialize (Hle k n m Ew' Ew); lia.
  - lia.
  - specialize (H0 k Ew); rewrite Ew' in H0; cbn in H0; lia.
  - lia.
Qed.

Lemma knth_klift d (s : kseq target) i :
  kgood s -> knth (klift d s) i = option_map (unshift d) (knth s i).
Proof.
  intros G; rewrite knth_spec by (apply kshape_klift, kgood_shape, G).
  rewrite knth_spec by apply (kgood_shape _ G).
  rewrite klist_klift by apply (kgood_inv _ G); apply nth_error_map.
Qed.

Lemma knth_some (s : kseq target) i : kgood s -> i < klength s -> exists t, knth s i = Some t.
Proof.
  intros G Hi; rewrite knth_spec by apply (kgood_shape _ G).
  destruct (nth_error (klist s) i) as [t|] eqn:E; [eauto|].
  apply nth_error_None in E; rewrite (klength_spec _ (kgood_shape _ G)) in Hi; lia.
Qed.

Theorem napply_lower w es w' v :
  nlocal Qall (NAdj w es) -> cle w' w -> (forall k, cget w k = None -> oval (cget w' k) = 0) ->
  oval (c_def (csub w w')) = 0 ->
  napply (lower w' (NAdj w es)) v = napply (NAdj w es) v.
Proof.
  intros Ha Hle H0 Hdef; pose proof Ha as [Hes [_ [_ [Hent _]]]].
  set (d := csub w w'); pose proof (fun k => dval_split w w' k Hle H0) as Hs; fold d in Hs.
  unfold lower, napply; fold d.
  rewrite (proj2 (aget_add_gaps d (alift d es) _ (ainv_alift d es Hes))), aget_alift by exact Hes.
  set (l := v_label v); set (i := v_index v).
  destruct (aget (label_key l) es) as [e|] eqn:E; cbn [option_map].
  - destruct (Hent _ _ E) as [Hok _]; destruct e as [h ts len p].
    destruct Hok as [Hk [Hg [Hlen _]]]; cbn [unshift entry_based eunshift eapply].
    destruct (Nat.ltb_spec i len) as [Hi|Hi].
    + destruct (knth_some ts i Hg ltac:(lia)) as [t Et].
      rewrite knth_klift, Et by exact Hg; cbn [option_map].
      f_equal; change (tunshift w' (unshift d t) = tunshift w t).
      change (unshift w' (unshift d t) = unshift w t); rewrite unshift_unshift.
      apply unshift_ext; intros k _; rewrite dval_cplus; apply Hs.
    + f_equal; f_equal; specialize (Hs (label_key h)); lia.
  - assert (Hgap : forall n, cget d (label_key l) = Some n ->
                   inl (mk_rvar l (dval w' (label_key l) + (i - 0 + n))) = inl (mk_rvar l (dval w (label_key l) + i)) :> result).
    { intros n Hn; specialize (Hs (label_key l)); unfold dval at 2 in Hs; rewrite Hn in Hs; cbn in Hs.
      f_equal; f_equal; lia. }
    destruct (get (label_key l) (c_exc d)) as [[[|n]|]|] eqn:G.
    + f_equal; f_equal; specialize (Hs (label_key l)); unfold dval at 2 in Hs.
      unfold cget in Hs; rewrite G in Hs; cbn in Hs; lia.
    + unfold gap; rewrite key_label_spec, Pos.eqb_refl; cbn [eapply Nat.ltb].
      apply Hgap; unfold cget; rewrite G; reflexivity.
    + f_equal; f_equal; specialize (Hs (label_key l)); unfold dval at 2 in Hs.
      unfold cget in Hs; rewrite G in Hs; cbn in Hs; lia.
    + f_equal; f_equal; specialize (Hs (label_key l)); unfold dval at 2 in Hs.
      unfold cget in Hs; rewrite G in Hs; change (oval (c_def d) = 0) in Hdef; rewrite Hdef in Hs; lia.
Qed.

End Point.
