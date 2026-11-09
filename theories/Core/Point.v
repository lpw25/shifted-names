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

(** Lowering keeps every entry in normal form: a lifted entry's last
    target moves with its pass-through, and a gap entry has no targets. *)
Lemma entry_ok_lower w es w' :
  ainv es -> (forall k e, aget k es = Some e -> entry_ok k e) ->
  forall k e, aget k (nentries (lower w' (NAdj w es))) = Some e -> entry_ok k e.
Proof.
  intros Hes Hok k e; set (d := csub w w'); cbn [lower nentries]; fold d.
  rewrite (proj2 (aget_add_gaps d (alift d es) k (ainv_alift d es Hes))), aget_alift by exact Hes.
  destruct (aget k es) as [e0|] eqn:E; cbn [option_map].
  - intros [= <-]; destruct e0 as [h ts len p]; destruct (Hok _ _ E) as [Hk [Hg [Hl [Hn Hs]]]].
    cbn [unshift entry_based eunshift entry_ok]; split; [exact Hk|split; [apply kgood_klift, Hg|]].
    split; [rewrite <- Hl; unfold klength; destruct ts; reflexivity|split; [lia|]].
    intros [Hlen [Hp Ht]]; rewrite knth_klift in Ht by exact Hg.
    destruct (knth ts (pred len)) as [[y j|u [r es']]|] eqn:Et; cbn in Ht; try discriminate.
    injection Ht as -> Hj; destruct p as [|p]; [lia|].
    apply Hs; split; [exact Hlen|split; [lia|rewrite Et; f_equal; f_equal; lia]].
  - destruct (get k (c_exc d)) as [[[|n]|]|]; try discriminate.
    unfold gap; destruct (key_label k) as [l|]; [|discriminate].
    destruct (Pos.eqb_spec (label_key l) k) as [Hk|]; [|discriminate].
    intros [= <-]; cbn; split; [exact Hk|split; [apply kgood_nil|split; [reflexivity|split; lia]]].
Qed.

Lemma klength_klift d (s : kseq target) : klength (klift d s) = klength s.
Proof. destruct s; reflexivity. Qed.

(** ** Extension

    [extend h t a] sends [h_0] to [t] and [h_(i+1)] to where [a] sends
    [h_i].  The root counts drop to cover [t], then [t], relative to the new
    root, goes on the front of [h]'s targets.  If [h] had no targets and [t]
    is just where pass-through would send it, the pass-through shortens
    instead (the one-element strip). *)

Definition tvar_at (h : option label) (p : nat) (t : target) : bool :=
  match t with TVar y j => label_eqb y h && Nat.eqb j p | TBind _ _ => false end.

Definition econs (h : option label) (t : target) (o : option entry) : option entry :=
  match o with
  | Some (Entry _ ts (S len) p) => Some (Entry h (kcons t ts) (S (S len)) p)
  | Some (Entry _ _ 0 (S p')) =>
      if tvar_at h p' t
      then match p' with 0 => None | _ => Some (Entry h KNil 0 p') end
      else Some (Entry h (kcons t KNil) 1 (S p'))
  | _ => Some (Entry h (kcons t KNil) 1 0)
  end.

Definition extend (h : option label) (t : target) (a : nadj) : nadj :=
  let w' := cmin (nroot a) (tuses t) in
  match lower w' a with
  | NAdj _ es => NAdj w' (aupdate (label_key h) (econs h (tshift w' t)) es)
  end.

(** Where an optional entry for [h] sends [h_i]. *)
Definition oapply (w : counts) (h : option label) (o : option entry) (i : nat) : result :=
  match o with
  | None => inl (mk_rvar h (dval w (label_key h) + i))
  | Some e => eapply w e i
  end.

Lemma knth_kcons (t : target) s i :
  eok t -> kgood s -> knth (kcons t s) i = match i with 0 => Some t | S i' => knth s i' end.
Proof.
  intros Ht G; destruct (kgood_kcons t s Ht G) as [G' E].
  rewrite (knth_spec _ _ (kgood_shape _ G')), E; destruct i; [reflexivity|].
  symmetry; apply knth_spec, kgood_shape, G.
Qed.

Lemma klength_kcons_good (t : target) s : klength (kcons t s) = S (klength s).
Proof. apply klength_kcons. Qed.

Lemma entry_ok_econs h t o :
  eok t -> (forall e, o = Some e -> entry_ok (label_key h) e) ->
  forall e, econs h t o = Some e -> entry_ok (label_key h) e.
Proof.
  intros Ht Ho e; destruct o as [[h' ts [|len] [|p']]|]; cbn [econs].
  - intros [= <-]; split; [reflexivity|].
    split; [apply (kgood_kcons _ _ Ht kgood_nil)|].
    split; [reflexivity|split; [lia|cbn; lia]].
  - destruct (tvar_at h p' t) eqn:Tv.
    + destruct p' as [|p'']; [discriminate|]; intros [= <-]; split; [reflexivity|].
      split; [apply kgood_nil|split; [reflexivity|split; [lia|cbn; lia]]].
    + intros [= <-]; split; [reflexivity|].
      split; [apply (kgood_kcons _ _ Ht kgood_nil)|].
      split; [reflexivity|split; [lia|]].
      cbn [strip_ok pred]; change (kcell 1 (KLeaf t) KNil) with (kcons t KNil); rewrite knth_kcons by (exact Ht || apply kgood_nil).
      intros [_ [_ [= ->]]]; cbn in Tv; rewrite label_eqb_refl, Nat.eqb_refl in Tv; discriminate.
  - intros [= <-]; destruct (Ho _ eq_refl) as [Hk [Hg [Hl [_ Hs]]]].
    split; [reflexivity|split; [apply (kgood_kcons _ _ Ht Hg)|]].
    split; [rewrite klength_kcons, Hl; reflexivity|split; [lia|]].
    cbn [strip_ok pred]; rewrite knth_kcons by assumption.
    intros [_ [Hp Hn]]; apply Hs; cbn [pred] in *; split; [lia|split; [lia|]].
    apply label_key_inj in Hk; subst h'; exact Hn.
  - intros [= <-]; destruct (Ho _ eq_refl) as [Hk [Hg [Hl [_ Hs]]]].
    split; [reflexivity|split; [apply (kgood_kcons _ _ Ht Hg)|]].
    split; [rewrite klength_kcons, Hl; reflexivity|split; [lia|]].
    cbn [strip_ok pred]; rewrite knth_kcons by assumption.
    intros [_ [Hp Hn]]; apply Hs; cbn [pred] in *; split; [lia|split; [lia|]].
    apply label_key_inj in Hk; subst h'; exact Hn.
  - intros [= <-]; split; [reflexivity|].
    split; [apply (kgood_kcons _ _ Ht kgood_nil)|].
    split; [reflexivity|split; [lia|cbn; lia]].
Qed.

Lemma oapply_econs w h t o i :
  eok t -> (forall e, o = Some e -> entry_ok (label_key h) e) ->
  oapply w h (econs h t o) i
  = match i with 0 => tresult (tunshift w t) | S i' => oapply w h o i' end.
Proof.
  intros Ht Ho; destruct o as [[h' ts [|len] [|p']]|]; cbn [econs oapply].
  - cbn [eapply]; try change (kcell 1 (KLeaf t) KNil) with (kcons t KNil); rewrite knth_kcons by (exact Ht || apply kgood_nil).
    destruct i as [|i]; cbn [Nat.ltb Nat.leb]; [reflexivity|].
    destruct (Ho _ eq_refl) as [Hk _]; apply label_key_inj in Hk; subst h'.
    cbn [eapply Nat.ltb Nat.leb]; f_equal; f_equal; lia.
  - destruct (Ho _ eq_refl) as [Hk _]; apply label_key_inj in Hk; subst h'.
    destruct (tvar_at h p' t) eqn:Tv.
    + destruct t as [y j|]; cbn in Tv; [|discriminate].
      apply andb_prop in Tv as [Ty Tj]; apply label_eqb_eq in Ty; apply Nat.eqb_eq in Tj; subst y j.
      destruct p' as [|p''], i as [|i]; cbn [oapply eapply Nat.ltb Nat.leb tunshift tresult];
        f_equal; f_equal; lia.
    + cbn [oapply eapply]; try change (kcell 1 (KLeaf t) KNil) with (kcons t KNil); rewrite knth_kcons by (exact Ht || apply kgood_nil).
      destruct i as [|i]; cbn [Nat.ltb Nat.leb]; [reflexivity|]; f_equal; f_equal; lia.
  - destruct (Ho _ eq_refl) as [Hk [Hg [Hl _]]]; apply label_key_inj in Hk; subst h'.
    cbn [eapply]; rewrite knth_kcons by assumption.
    destruct i as [|i]; [reflexivity|].
    destruct (Nat.ltb_spec (S i) (S (S len))), (Nat.ltb_spec i (S len)); try lia.
    + destruct (knth_some ts i Hg ltac:(lia)) as [t' ->]; reflexivity.
    + f_equal; f_equal; lia.
  - destruct (Ho _ eq_refl) as [Hk [Hg [Hl _]]]; apply label_key_inj in Hk; subst h'.
    cbn [eapply]; rewrite knth_kcons by assumption.
    destruct i as [|i]; [reflexivity|].
    destruct (Nat.ltb_spec (S i) (S (S len))), (Nat.ltb_spec i (S len)); try lia.
    + destruct (knth_some ts i Hg ltac:(lia)) as [t' ->]; reflexivity.
    + f_equal; f_equal; lia.
  - cbn [eapply]; try change (kcell 1 (KLeaf t) KNil) with (kcons t KNil); rewrite knth_kcons by (exact Ht || apply kgood_nil).
    destruct i as [|i]; cbn [Nat.ltb Nat.leb]; [reflexivity|]; f_equal; f_equal; lia.
Qed.

Lemma ksann_kcons_cwf (t : target) s : cwf (ksann (kcons t s)).
Proof.
  unfold kcons; destruct s as [|a1 w1 t1 [|a2 w2 t2 s']]; try apply cwf_cmap2.
  destruct (Nat.eqb w1 w2); apply cwf_cmap2.
Qed.

Lemma ook_econs h t o : ook (econs h t o).
Proof.
  destruct o as [[h' ts [|len] [|p']]|]; cbn [econs]; try apply ksann_kcons_cwf.
  destruct (tvar_at h p' t); [destruct p'; [exact I|apply cwf_cnone]|apply ksann_kcons_cwf].
Qed.

Lemma napply_oapply w es v :
  napply (NAdj w es) v = oapply w (v_label v) (aget (label_key (v_label v)) es) (v_index v).
Proof. cbn [napply]; destruct (aget _ es); reflexivity. Qed.

(** At the top level every label is used, so the root counts are total. *)
Lemma nlocal_total w (es : atrie entry) : nlocal Qall (NAdj w es) -> forall k, cget w k <> None.
Proof.
  intros [_ [_ [Hkey [_ [Hq _]]]]] k; unfold cget.
  destruct (get k (c_exc w)) as [v|] eqn:E.
  - destruct (Hkey _ _ E) as [l ->]; specialize (Hq l eq_refl); unfold cget in Hq; rewrite E in Hq; exact Hq.
  - destruct (fresh_label (c_exc w) (c_exc w)) as [l [El _]].
    specialize (Hq l eq_refl); unfold cget in Hq; rewrite El in Hq; exact Hq.
Qed.

Lemma cle_cmin_l a b : cle (cmin a b) a.
Proof. intros k n m Hn Hm; rewrite cget_cmin in Hn; apply (omin_le _ _ _ Hn); left; exact Hm. Qed.

Lemma cle_cmin_r a b : cle (cmin a b) b.
Proof. intros k n m Hn Hm; rewrite cget_cmin in Hn; apply (omin_le _ _ _ Hn); right; exact Hm. Qed.

(** A target's uses are finitely many. *)
Definition tfinite (t : target) : Prop := c_def (tuses t) = None.

Lemma lower_cond w t :
  (forall k, cget w k <> None) -> tfinite t ->
  let w' := cmin w (tuses t) in
  cle w' w /\ (forall k, cget w k = None -> oval (cget w' k) = 0)
  /\ oval (c_def (csub w w')) = 0.
Proof.
  intros Hw Hf w'; split; [apply cle_cmin_l|split; [intros k E; exfalso; exact (Hw k E)|]].
  unfold w', csub, cmin, cmap2; cbn [c_def]; unfold tfinite in Hf; rewrite Hf.
  destruct (c_def w) as [n|]; cbn; [lia|reflexivity].
Qed.

Theorem napply_extend h t a v :
  nlocal Qall a -> tok t -> tfinite t ->
  napply (extend h t a) v
  = if rvar_eqb v (mk_rvar h 0) then tresult t else napply a (unshift_rvar (mk_rvar h 0) v).
Proof.
  destruct a as [w es]; intros Ha Ht Hf.
  destruct (lower_cond w t (nlocal_total w es Ha) Hf) as [Hle [H0 Hdef]].
  set (w' := cmin w (tuses t)) in *.
  pose proof Ha as [Hes [_ [_ [Hent _]]]].
  assert (Hlow : forall v, napply (lower w' (NAdj w es)) v = napply (NAdj w es) v)
    by (intro; apply napply_lower; assumption).
  assert (Hok' := entry_ok_lower w es w' Hes (fun k e E => proj1 (Hent k e E))).
  unfold extend; cbn [nroot]; fold w'.
  destruct (lower w' (NAdj w es)) as [w'' es'] eqn:L.
  assert (Hw'' : w'' = w') by (cbn in L; congruence); subst w''.
  assert (Hes' : ainv es')
    by (cbn in L; injection L as <-; apply (aget_add_gaps _ _ xH (ainv_alift _ _ Hes))).
  cbn [nentries] in Hok'.
  destruct (aupdate_spec (label_key h) (econs h (tshift w' t)) es' Hes' (fun o _ => ook_econs h _ o))
    as [_ Hg].
  rewrite napply_oapply, Hg, label_key_eqb.
  destruct v as [l i]; cbn [v_label v_index]; unfold rvar_eqb, unshift_rvar; cbn [v_label v_index].
  destruct (label_eqb_spec l h) as [->|Hne]; cbn [andb].
  - rewrite label_eqb_refl, oapply_econs.
    + destruct i as [|i]; cbn [Nat.eqb Nat.ltb Nat.leb andb].
      * f_equal; change (unshift w' (shift w' t) = t); apply unshift_shift; [exact Ht|apply cle_cmin_r].
      * rewrite <- Hlow, napply_oapply; cbn [v_label v_index]; f_equal; lia.
    + exact (ok_shift w' t Ht).
    + intros e E; apply (Hok' _ _ E).
  - rewrite (proj2 (label_eqb_neq h l)) by congruence; cbn [andb].
    rewrite <- Hlow, napply_oapply; reflexivity.
Qed.

(** ** Extension keeps the normal form *)

(** Some entry uses label [k]'s first output. *)
Lemma aann_zero (es : atrie entry) k :
  ainv es ->
  cget (aann es) k = Some 0
  <-> exists k2 e, aget k2 es = Some e /\ cget (uses e) k = Some 0.
Proof.
  intros Hes; rewrite (ainv_ann es Hes); split.
  - intros H; destruct (lmin_attained _ _ _ H) as [e [Hin He]].
    destruct (aelems_aget es e Hin) as [k2 E]; exists k2, e; split; [exact E|exact He].
  - intros [k2 [e [E He]]]; destruct (lmin_le _ e k 0 (aget_in _ _ _ E) He) as [n [Hn Hle]].
    rewrite Hn; f_equal; lia.
Qed.

Lemma omin_zero_l a b : a = Some 0 -> omin a b = Some 0.
Proof. intros ->; destruct b; cbn; [f_equal; lia|reflexivity]. Qed.

Lemma omin_zero_r a b : b = Some 0 -> omin a b = Some 0.
Proof. intros ->; destruct a; cbn; [f_equal; lia|reflexivity]. Qed.

Lemma omin_zero a b : omin a b = Some 0 -> a = Some 0 \/ b = Some 0.
Proof. destruct a as [x|], b as [y|]; cbn; intros H; try (left; congruence); try (right; congruence).
  injection H as H; destruct (Nat.min_spec x y) as [[_ E]|[_ E]]; rewrite E in H; subst; auto.
Qed.

Lemma ksann_kcons (t : target) s k :
  eok t -> kgood s -> cget (ksann (kcons t s)) k = omin (cget (tuses t) k) (cget (ksann s) k).
Proof.
  intros Ht G; destruct (kgood_kcons t s Ht G) as [G' E].
  rewrite !ksann_klist by assumption; rewrite E; reflexivity.
Qed.

Lemma ksann_empty (s : kseq target) k : kgood s -> klength s = 0 -> cget (ksann s) k = None.
Proof.
  intros G L; rewrite ksann_klist by exact G.
  rewrite <- (klength_klist s G) in L; destruct (klist s); [reflexivity|discriminate].
Qed.

(** A first output used by the old entry stays used. *)
Lemma econs_zero_old h t o k :
  eok t -> (forall e, o = Some e -> entry_ok (label_key h) e) ->
  cget (ouses o) k = Some 0 -> cget (ouses (econs h t o)) k = Some 0.
Proof.
  intros Ht Ho; destruct o as [[h' ts len p]|]; [|intros H; cbn in H; discriminate].
  destruct (Ho _ eq_refl) as [Hk [Hg [Hl _]]]; apply label_key_inj in Hk; subst h'.
  cbn [ouses uses entry_based euses]; rewrite cget_cmin; intros H0.
  destruct len as [|len].
  - rewrite (ksann_empty ts k Hg Hl) in H0; destruct p as [|p'].
    + cbn [econs ouses uses entry_based euses]; rewrite cget_cmin; apply omin_zero_l.
      rewrite cget_cone in *; destruct (Pos.eqb k _); [reflexivity|discriminate].
    + rewrite cget_cone in H0; destruct (Pos.eqb k _); cbn in H0; discriminate.
  - cbn [econs ouses uses entry_based euses]; rewrite cget_cmin, ksann_kcons by assumption.
    apply omin_zero in H0 as [H0|H0]; [apply omin_zero_l, H0|apply omin_zero_r, omin_zero_r, H0].
Qed.

(** The new target's first outputs are used, unless it was stripped away. *)
Lemma econs_zero_new h t o k :
  eok t -> (forall e, o = Some e -> entry_ok (label_key h) e) ->
  cget (tuses t) k = Some 0 ->
  cget (ouses (econs h t o)) k = Some 0 \/ (k = label_key h /\ econs h t o = None).
Proof.
  intros Ht Ho H0.
  destruct o as [[h' ts [|len] [|p']]|]; cbn [econs];
    try (left; cbn [ouses uses entry_based euses]; rewrite cget_cmin, ksann_kcons by (exact Ht || apply kgood_nil);
         apply omin_zero_r, omin_zero_l, H0).
  - destruct (tvar_at h p' t) eqn:Tv.
    + destruct t as [y j|]; cbn in Tv; [|discriminate].
      apply andb_prop in Tv as [Ty Tj]; apply label_eqb_eq in Ty; apply Nat.eqb_eq in Tj; subst y j.
      cbn in H0; rewrite cget_cone in H0.
      destruct (Pos.eqb_spec k (label_key h)) as [->|]; [|discriminate]; injection H0 as ->.
      right; split; reflexivity.
    + left; cbn [ouses uses entry_based euses]; rewrite cget_cmin, ksann_kcons by (exact Ht || apply kgood_nil).
      apply omin_zero_r, omin_zero_l, H0.
  - destruct (Ho _ eq_refl) as [_ [Hg _]].
    left; cbn [ouses uses entry_based euses]; rewrite cget_cmin, ksann_kcons by assumption.
    apply omin_zero_r, omin_zero_l, H0.
  - destruct (Ho _ eq_refl) as [_ [Hg _]].
    left; cbn [ouses uses entry_based euses]; rewrite cget_cmin, ksann_kcons by assumption.
    apply omin_zero_r, omin_zero_l, H0.
Qed.

Theorem nlocal_extend h t a :
  nlocal Qall a -> tok t -> tfinite t -> keyed (tuses t) -> nlocal Qall (extend h t a).
Proof.
  destruct a as [w es]; intros Ha Ht Hf Hk.
  pose proof (nlocal_total w es Ha) as Htot.
  pose proof Ha as [Hes [_ [Hkey [Hent _]]]].
  set (w' := cmin w (tuses t)); set (d := csub w w'); set (es' := add_gaps d (alift d es));
    set (t' := tshift w' t); set (kh := label_key h).
  assert (Hes' : ainv es') by apply (aget_add_gaps d (alift d es) xH (ainv_alift d es Hes)).
  assert (Hg' : forall k, aget k es'
                          = match aget k es with
                            | Some e => Some (unshift d e)
                            | None => match get k (c_exc d) with Some (Some (S n)) => gap k (S n) | _ => None end
                            end).
  { intro k; unfold es'; rewrite (proj2 (aget_add_gaps d (alift d es) k (ainv_alift d es Hes))), aget_alift by exact Hes.
    destruct (aget k es); reflexivity. }
  assert (Hok' : forall k e, aget k es' = Some e -> entry_ok k e)
    by exact (entry_ok_lower w es w' Hes (fun k e E => proj1 (Hent k e E))).
  assert (Ht' : eok t') by exact (ok_shift w' t Ht).
  assert (Hoh : forall e, aget kh es' = Some e -> entry_ok kh e) by (intro; apply Hok').
  destruct (aupdate_spec kh (econs h t') es' Hes' (fun o _ => ook_econs h t' o)) as [Hes'' Hg''].
  change (nlocal Qall (NAdj w' (aupdate kh (econs h t') es'))).
  set (es'' := aupdate kh (econs h t') es') in *.
  assert (Ekh : aget kh es'' = econs h t' (aget kh es')) by (rewrite Hg'', Pos.eqb_refl; reflexivity).
  split; [exact Hes''|split; [apply cwf_cmap2|split; [apply keyed_cmap2; assumption|split]]].
  2: { split; [|intros l Hl; discriminate].
       intros l _; unfold w'; rewrite cget_cmin; specialize (Htot (label_key l)).
       destruct (cget w _); [destruct (cget (tuses t) _); discriminate|contradiction]. }
  intros k e E; rewrite Hg'' in E; split; [|split; [reflexivity|]].
  { destruct (Pos.eqb_spec k kh) as [->|]; [exact (entry_ok_econs h t' _ Ht' Hoh e E)|exact (Hok' k e E)]. }
  apply (aann_zero es'' k Hes'').
  (* Where the root count does not drop, the old witness still serves. *)
  assert (Hold : cget d k = Some 0 -> exists k2 e2, aget k2 es'' = Some e2 /\ cget (uses e2) k = Some 0).
  { intros Hd; destruct (aget k es) as [e0|] eqn:E0.
    - destruct (Hent k e0 E0) as [_ [_ Z0]]; apply (aann_zero es k Hes) in Z0 as [k2 [e2 [E2 Z2]]].
      assert (Ze : cget (uses (unshift d e2)) k = Some 0) by (rewrite uses_unshift, Hd, Z2; reflexivity).
      assert (E2' : aget k2 es' = Some (unshift d e2)) by (rewrite Hg', E2; reflexivity).
      destruct (Pos.eqb_spec k2 kh) as [->|Hne].
      + assert (Z' := econs_zero_old h t' (aget kh es') k Ht' Hoh ltac:(rewrite E2'; exact Ze)).
        rewrite <- Ekh in Z'.
        destruct (aget kh es'') as [e3|] eqn:Ec; [|cbn in Z'; discriminate].
        exists kh, e3; split; [exact Ec|exact Z'].
      + exists k2, (unshift d e2); split; [|exact Ze].
        rewrite Hg''; apply Pos.eqb_neq in Hne; rewrite Hne; exact E2'.
    - assert (Hn : aget k es' = None).
      { rewrite Hg', E0; unfold cget in Hd; destruct (get k (c_exc d)) as [[[|n']|]|]; congruence. }
      destruct (Pos.eqb_spec k kh) as [->|]; [|rewrite Hn in E; discriminate].
      rewrite Hn in E; cbn [econs] in E; injection E as <-.
      exists kh, (Entry h (kcons t' KNil) 1 0); split; [rewrite Hg'', Pos.eqb_refl, Hn; reflexivity|].
      cbn [uses entry_based euses]; rewrite cget_cmin; apply omin_zero_l; apply cget_cone_same. }
  specialize (Htot k); destruct (cget w k) as [m|] eqn:Ew; [|contradiction].
  assert (Hu' : cget (tuses t') k = osub (cget (tuses t) k) (cget w' k)) by exact (uses_shift w' t k).
  assert (Hw' : cget w' k = omin (Some m) (cget (tuses t) k)) by (unfold w'; rewrite cget_cmin, Ew; reflexivity).
  assert (Hdk : cget d k = osub (Some m) (cget w' k)) by (unfold d; rewrite cget_csub, Ew; reflexivity).
  destruct (cget (tuses t) k) as [n|] eqn:Eu; [destruct (Nat.ltb_spec n m) as [Hnm|Hnm]|].
  - (* [t] uses [k] below the old root count: the new target is the witness *)
    assert (Z : cget (tuses t') k = Some 0) by (rewrite Hu', Hw'; cbn; f_equal; lia).
    destruct (econs_zero_new h t' (aget kh es') k Ht' Hoh Z) as [Z'|[-> En]].
    + rewrite <- Ekh in Z'.
      destruct (aget kh es'') as [e2|] eqn:Ec; [|cbn in Z'; discriminate].
      exists kh, e2; split; [exact Ec|exact Z'].
    + rewrite Pos.eqb_refl, En in E; discriminate.
  - apply Hold; rewrite Hdk, Hw'; cbn; f_equal; lia.
  - apply Hold; rewrite Hdk, Hw'; cbn; f_equal; lia.
Qed.

End Point.
