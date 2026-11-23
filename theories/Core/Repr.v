(** * The representation of adjustments

    Targets name output variables directly; weakenings are applied lazily
    through the counts on the nodes (Counts.v, Skew.v, ATrie.v).

    - A [target] is a variable [TVar y j] ([j] relative to the counts above
      it) or a payload [TBind u ρ]: a term [u] with a pending adjustment [ρ]
      of its variables, whose root counts are relative to the node above it.
    - An [entry] for label [h] holds the targets of [h₀ … h₍len−1₎] and the
      start [p] of the pass-through: [hᵢ ↦ h₍ᵢ₋len₊p₎] for [i ≥ len].
    - An adjustment [NAdj ω es] has root counts [ω] (per label, the
      weakening of the whole adjustment) and a trie of entries relative to
      [ω].  A label without an entry is the identity relative to [ω]. *)

From Stdlib Require Import PArith Arith Lia List Bool.
From ShiftedNames.Core Require Import Trie Label Var Counts Based Skew ATrie.
Import ListNotations.

Section Repr.

Context {T : Type}.

Inductive target : Type :=
| TVar (y : option label) (j : nat)
| TBind (u : T) (rho : nadj)
with nadj : Type :=
| NAdj (root : counts) (entries : atrie entry)
with entry : Type :=
| Entry (h : option label) (targets : kseq target) (len : nat) (p : nat).

Definition nroot (a : nadj) : counts := match a with NAdj r _ => r end.
Definition nentries (a : nadj) : atrie entry := match a with NAdj _ es => es end.

(** ** Targets relative to a base *)

Definition tuses (t : target) : counts :=
  match t with TVar y j => cone (label_key y) j | TBind _ rho => nroot rho end.

Definition tshift (d : counts) (t : target) : target :=
  match t with
  | TVar y j => TVar y (j - dval d (label_key y))
  | TBind u (NAdj r es) => TBind u (NAdj (csub r d) es)
  end.

Definition tunshift (d : counts) (t : target) : target :=
  match t with
  | TVar y j => TVar y (dval d (label_key y) + j)
  | TBind u (NAdj r es) => TBind u (NAdj (cadd d r) es)
  end.

#[export] Instance target_based : Based target :=
  {| uses := tuses; shift := tshift; unshift := tunshift |}.

Lemma cget_cone_same k n : cget (cone k n) k = Some n.
Proof. rewrite cget_cone, Pos.eqb_refl; reflexivity. Qed.

#[export] Instance target_laws : BasedLaws target.
Proof.
  split.
  - intros d [y j|u [r es]]; cbn; [f_equal; lia|rewrite csub_cadd; reflexivity].
  - intros d [y j|u [r es]]; cbn; intros Hle.
    + pose proof (dval_le_cle d _ j Hle); f_equal; lia.
    + rewrite cadd_csub by assumption; reflexivity.
  - intros d1 d2 [y j|u [r es]]; cbn; [rewrite dval_cplus; f_equal; lia|rewrite cadd_cadd; reflexivity].
  - intros d d' [y j|u [r es]]; cbn; intros H.
    + rewrite (H (label_key y)) by (rewrite cget_cone_same; discriminate); reflexivity.
    + rewrite (cadd_ext d d' r H); reflexivity.
  - intros d [y j|u [r es]] k; cbn; [|apply cget_cadd].
    rewrite !cget_cone; destruct (Pos.eqb_spec k (label_key y)) as [->|]; [|reflexivity].
    reflexivity.
  - intros d [y j|u [r es]] k; cbn; [|apply cget_csub].
    rewrite !cget_cone; destruct (Pos.eqb_spec k (label_key y)) as [->|]; [|reflexivity].
    reflexivity.
Qed.

(** ** Entries relative to a base *)

Definition elabel (e : entry) : option label := match e with Entry h _ _ _ => h end.
Definition etargets (e : entry) : kseq target := match e with Entry _ ts _ _ => ts end.
Definition elen (e : entry) : nat := match e with Entry _ _ len _ => len end.
Definition epass (e : entry) : nat := match e with Entry _ _ _ p => p end.

(** An entry uses its pass-through outputs and its targets. *)
Definition euses (e : entry) : counts :=
  match e with Entry h ts _ p => cmin (cone (label_key h) p) (ksann ts) end.

Definition eshift (d : counts) (e : entry) : entry :=
  match e with Entry h ts len p => Entry h (krebase d ts) len (p - dval d (label_key h)) end.

Definition eunshift (d : counts) (e : entry) : entry :=
  match e with Entry h ts len p => Entry h (klift d ts) len (dval d (label_key h) + p) end.

#[export] Instance entry_based : Based entry :=
  {| uses := euses; shift := eshift; unshift := eunshift |}.

Lemma ksann_krebase d (s : kseq target) k :
  cget (ksann (krebase d s)) k = osub (cget (ksann s) k) (cget d k).
Proof. destruct s; cbn [krebase ksann]; [reflexivity|apply cget_csub]. Qed.

Lemma ksann_klift d (s : kseq target) k :
  cget (ksann (klift d s)) k = oadd (cget d k) (cget (ksann s) k).
Proof. destruct s; cbn [klift ksann]; [destruct (cget d k); reflexivity|apply cget_cadd]. Qed.

#[export] Instance entry_laws : BasedLaws entry.
Proof.
  split.
  - intros d [h [|a w t s] len p]; cbn; f_equal; try lia.
    rewrite csub_cadd; reflexivity.
  - intros d [h [|a w t s] len p]; cbn [unshift shift uses entry_based eunshift eshift euses ksann klift krebase etargets];
      intros Hle; pose proof (dval_le_cle d _ p (cle_cmin_inv_l _ _ _ Hle)); f_equal; try lia.
    rewrite cadd_csub by apply (cle_cmin_inv_r _ _ _ Hle); reflexivity.
  - intros d1 d2 [h [|a w t s] len p]; cbn; rewrite dval_cplus; f_equal; try lia.
    rewrite cadd_cadd; reflexivity.
  - intros d d' [h [|a w t s] len p]; cbn [uses entry_based euses ksann]; intros H; cbn [uses entry_based euses ksann] in H;
      assert (Hp : dval d (label_key h) = dval d' (label_key h))
        by (apply H; rewrite cget_cmin, cget_cone_same; destruct (cget _ _); discriminate);
      cbn [unshift entry_based eunshift klift]; rewrite Hp; [reflexivity|].
    rewrite (cadd_ext d d' a); [reflexivity|]; intros k Hk; apply H.
    rewrite cget_cmin; destruct (cget (cone _ _) k), (cget a k); cbn; congruence.
  - intros d [h s len p] k; cbn [uses unshift entry_based euses eunshift].
    rewrite !cget_cmin, ksann_klift, oadd_omin; f_equal.
    rewrite !cget_cone; destruct (Pos.eqb_spec k (label_key h)) as [->|]; reflexivity.
  - intros d [h s len p] k; cbn [uses shift entry_based euses eshift].
    rewrite !cget_cmin, ksann_krebase, osub_omin; f_equal.
    rewrite !cget_cone; destruct (Pos.eqb_spec k (label_key h)) as [->|]; reflexivity.
Qed.

(** ** Meaning *)

Definition result : Type := (rvar + (T * nadj))%type.

Definition tresult (t : target) : result :=
  match t with TVar y j => inl (mk_rvar y j) | TBind u rho => inr (u, rho) end.

Definition ruses (r : result) : counts :=
  match r with inl w => cone (label_key (v_label w)) (v_index w) | inr (_, rho) => nroot rho end.

Lemma ruses_tresult t : ruses (tresult t) = tuses t.
Proof. destruct t; reflexivity. Qed.

(** An entry stored relative to base [w]: its [i]-th input. *)
Definition eapply (w : counts) (e : entry) (i : nat) : result :=
  match e with
  | Entry h ts len p =>
      if Nat.ltb i len
      then match knth ts i with
           | Some t => tresult (tunshift w t)
           | None => inl (mk_rvar h (dval w (label_key h) + i))   (* unreachable *)
           end
      else inl (mk_rvar h (dval w (label_key h) + (i - len + p)))
  end.

(** Where [a] sends [v], relative to the base [a] is stored at. *)
Definition napply (a : nadj) (v : rvar) : result :=
  match a with
  | NAdj w es =>
      match aget (label_key (v_label v)) es with
      | None => inl (mk_rvar (v_label v) (dval w (label_key (v_label v)) + v_index v))
      | Some e => eapply w e (v_index v)
      end
  end.

(** ** Normal form (one level) *)

(** The last explicit target is not where pass-through would send it. *)
Definition strip_ok (e : entry) : Prop :=
  match e with
  | Entry h ts len p => ~ (0 < len /\ 0 < p /\ knth ts (pred len) = Some (TVar h (pred p)))
  end.

Definition entry_ok (k : positive) (e : entry) : Prop :=
  match e with
  | Entry h ts len p =>
      label_key h = k /\ kgood ts /\ klength ts = len /\ (0 < len \/ 0 < p) /\ strip_ok e
  end.

(** Exceptions of a count map are at the keys of labels. *)
Definition keyed (c : counts) : Prop :=
  forall k v, get k (c_exc c) = Some v -> exists l, k = label_key l.

Lemma keyed_cmap2 f c1 c2 : keyed c1 -> keyed c2 -> keyed (cmap2 f c1 c2).
Proof.
  intros K1 K2 k v H; rewrite get_cmap2 in H.
  destruct (get k (c_exc c1)) as [v1|] eqn:E1; [apply (K1 _ _ E1)|].
  destruct (get k (c_exc c2)) as [v2|] eqn:E2; [apply (K2 _ _ E2)|].
  rewrite cmap2_none in H; discriminate.
Qed.

Lemma keyed_cone l n : keyed (cone (label_key l) n).
Proof.
  intros k v H; cbn in H; rewrite get_set in H.
  destruct (Pos.eqb_spec k (label_key l)) as [->|]; [eauto|rewrite get_Empty in H; discriminate].
Qed.

(** One-level normal form: the entries are well formed and their counts
    relative to the root, and every label has a root count. *)
Definition nlocal (a : nadj) : Prop :=
  match a with
  | NAdj w es =>
      ainv es /\ keyed w
      /\ (forall k e, aget k es = Some e -> entry_ok k e /\ cget (aann es) k = Some 0)
      /\ (forall l, cget w (label_key l) <> None)
  end.

(** ** Canonicity *)

Section Canonical.

(** *** Every result is above the root counts *)

Lemma kgood_entry w es k e : nlocal (NAdj w es) -> aget k es = Some e -> kgood (etargets e).
Proof.
  intros Ha He; destruct Ha as [_ [_ [Hent _]]].
  destruct (Hent k e He) as [Hok _]; destruct e as [h ts len p]; apply Hok.
Qed.

Lemma knth_in (ts : kseq target) i t : kgood ts -> knth ts i = Some t -> In t (klist ts).
Proof. intros Hg E; rewrite knth_spec in E by (apply kgood_shape, Hg); apply (nth_error_In _ _ E). Qed.

Lemma cle_result w es v :
  nlocal (NAdj w es) -> cle w (ruses (napply (NAdj w es) v)).
Proof.
  intros Ha; unfold napply; destruct (aget (label_key (v_label v)) es) as [e|] eqn:E.
  - destruct e as [h ts len p]; cbn [eapply].
    destruct (Nat.ltb (v_index v) len); [destruct (knth ts (v_index v)) as [t|] eqn:Et|].
    + rewrite ruses_tresult; intros k n m Hn; cbn [uses target_based] in *.
      change (tuses (tunshift w t)) with (uses (unshift w t)); rewrite uses_unshift, Hn.
      destruct (cget (uses t) k); cbn; [intros [= <-]; lia|discriminate].
    + intros k n m Hn; cbn; rewrite cget_cone.
      destruct (Pos.eqb_spec k (label_key h)) as [->|]; [intros [= <-]|discriminate].
      unfold dval; rewrite Hn; cbn; lia.
    + intros k n m Hn; cbn; rewrite cget_cone.
      destruct (Pos.eqb_spec k (label_key h)) as [->|]; [intros [= <-]|discriminate].
      unfold dval; rewrite Hn; cbn; lia.
  - intros k n m Hn; cbn; rewrite cget_cone.
    destruct (Pos.eqb_spec k (label_key (v_label v))) as [->|]; [intros [= <-]|discriminate].
    unfold dval; rewrite Hn; cbn; lia.
Qed.

Lemma omin_some0 a b : omin a b = Some 0 -> a = Some 0 \/ b = Some 0.
Proof.
  destruct a as [x|], b as [y|]; cbn; intros H; try discriminate; auto.
  injection H as H; destruct (Nat.min_spec x y) as [[_ E]|[_ E]]; rewrite E in H; subst; auto.
Qed.

Lemma klength_klist (ts : kseq target) : kgood ts -> length (klist ts) = klength ts.
Proof. intros Hg; symmetry; apply klength_spec, kgood_shape, Hg. Qed.

Lemma ksann_klist (ts : kseq target) k : kgood ts -> cget (ksann ts) k = lmin (klist ts) k.
Proof. intros G; apply (kinv_ann ts (kgood_inv _ G)). Qed.

(** The uses of an element below lift to the trie's counts. *)
Lemma aann_used (es : atrie entry) k e kl :
  ainv es -> aget k es = Some e -> cget (uses e) kl <> None -> cget (aann es) kl <> None.
Proof.
  intros Hes He Hu; rewrite (ainv_ann es Hes kl).
  apply (lmin_some _ e); [apply (aget_in k es e He)|exact Hu].
Qed.

(** A label with count 0 below the root is used by some input at the root
    count. *)
Lemma attained w es kl :
  nlocal (NAdj w es) -> cget (aann es) kl = Some 0 ->
  exists v, cget (ruses (napply (NAdj w es) v)) kl = Some (dval w kl).
Proof.
  intros Ha H0; pose proof Ha as [Hes [_ [Hent _]]].
  rewrite (ainv_ann es Hes) in H0; apply lmin_attained in H0 as [e [Hin He0]].
  destruct (aelems_aget es e Hin) as [k Hk].
  destruct (Hent _ _ Hk) as [Hok _]; destruct e as [h ts len p].
  destruct Hok as [Hkey [Hg [Hlen _]]]; subst k.
  cbn [uses entry_based euses] in He0; rewrite cget_cmin in He0.
  apply omin_some0 in He0 as [Hp|Ht].
  - rewrite cget_cone in Hp; destruct (Pos.eqb_spec kl (label_key h)) as [->|]; [|discriminate].
    injection Hp as ->; exists (mk_rvar h len).
    unfold napply; cbn [v_label v_index]; rewrite Hk; cbn [eapply].
    rewrite Nat.ltb_irrefl, Nat.sub_diag; cbn [ruses v_label v_index]; rewrite cget_cone_same; f_equal; lia.
  - rewrite ksann_klist in Ht by exact Hg; apply lmin_attained in Ht as [t [Hint Ht]].
    apply In_nth_error in Hint as [i Hi].
    assert (Hlt : i < len) by (rewrite <- Hlen, <- klength_klist by exact Hg; apply nth_error_Some; congruence).
    exists (mk_rvar h i).
    unfold napply; cbn [v_label v_index]; rewrite Hk; cbn [eapply].
    rewrite (proj2 (Nat.ltb_lt _ _) Hlt), knth_spec, Hi by (apply kgood_shape, Hg).
    rewrite ruses_tresult; change (tuses (tunshift w t)) with (uses (unshift w t)).
    rewrite uses_unshift, Ht; unfold dval; destruct (cget w kl); cbn; f_equal; lia.
Qed.

(** Every used root count is attained. *)
Lemma root_attained w es l n :
  nlocal (NAdj w es) -> cget w (label_key l) = Some n ->
  exists v, cget (ruses (napply (NAdj w es) v)) (label_key l) = Some n.
Proof.
  intros Ha Hn; pose proof Ha as [Hes [_ [Hent _]]].
  assert (Hd : dval w (label_key l) = n) by (unfold dval; rewrite Hn; reflexivity).
  destruct (aget (label_key l) es) as [e|] eqn:E.
  - destruct (Hent _ _ E) as [_ H0].
    destruct (attained w es _ Ha H0) as [v Hv]; rewrite Hd in Hv; eauto.
  - exists (mk_rvar l 0).
    unfold napply; cbn [v_label v_index]; rewrite E; cbn; rewrite cget_cone_same, Hd; f_equal; lia.
Qed.

(** The root counts are determined by the meaning. *)
Theorem root_determined a1 a2 :
  nlocal a1 -> nlocal a2 ->
  (forall v, napply a1 v = napply a2 v) ->
  forall l, cget (nroot a1) (label_key l) = cget (nroot a2) (label_key l).
Proof.
  destruct a1 as [w1 es1], a2 as [w2 es2]; cbn [nroot]; intros H1 H2 Heq l.
  destruct (cget w1 (label_key l)) as [n1|] eqn:E1, (cget w2 (label_key l)) as [n2|] eqn:E2.
  - f_equal; apply Nat.le_antisymm.
    + destruct (root_attained w2 es2 l n2 H2 E2) as [v Hv]; rewrite <- Heq in Hv.
      apply (cle_result w1 es1 v H1 _ _ _ E1 Hv).
    + destruct (root_attained w1 es1 l n1 H1 E1) as [v Hv]; rewrite Heq in Hv.
      apply (cle_result w2 es2 v H2 _ _ _ E2 Hv).
  - exfalso; apply (proj2 (proj2 (proj2 H2)) l E2).
  - exfalso; apply (proj2 (proj2 (proj2 H1)) l E1).
  - reflexivity.
Qed.

(** *** Explicit targets and pass-through, per label *)

Lemma decomp_unique (f : nat -> result) l len1 P1 L1 len2 P2 L2 :
  length L1 = len1 -> length L2 = len2 ->
  (forall i, f i = if Nat.ltb i len1 then nth i L1 (inl (mk_rvar l 0)) else inl (mk_rvar l (i - len1 + P1))) ->
  (forall i, f i = if Nat.ltb i len2 then nth i L2 (inl (mk_rvar l 0)) else inl (mk_rvar l (i - len2 + P2))) ->
  ~ (0 < len1 /\ 0 < P1 /\ f (pred len1) = inl (mk_rvar l (pred P1))) ->
  ~ (0 < len2 /\ 0 < P2 /\ f (pred len2) = inl (mk_rvar l (pred P2))) ->
  len1 = len2 /\ P1 = P2 /\ L1 = L2.
Proof.
  intros Hl1 Hl2 F1 F2 S1 S2.
  assert (Hoff : len2 + P1 = len1 + P2).
  { pose proof (F1 (len1 + len2)) as A; rewrite F2 in A.
    rewrite (proj2 (Nat.ltb_ge (len1 + len2) len1)), (proj2 (Nat.ltb_ge (len1 + len2) len2)) in A by lia.
    injection A as A; lia. }
  assert (Hlen : len1 = len2).
  { destruct (Nat.lt_trichotomy len1 len2) as [Hlt|[E|Hlt]]; [exfalso| exact E|exfalso].
    - apply S2; split; [lia|split; [lia|]].
      rewrite F1, (proj2 (Nat.ltb_ge _ _)) by lia; f_equal; f_equal; lia.
    - apply S1; split; [lia|split; [lia|]].
      rewrite F2, (proj2 (Nat.ltb_ge _ _)) by lia; f_equal; f_equal; lia. }
  rewrite <- Hlen in Hl2, F2, S2, Hoff |- *; split; [reflexivity|split; [lia|]].
  apply (nth_ext _ _ (inl (mk_rvar l 0)) (inl (mk_rvar l 0))); [congruence|].
  intros i Hi; pose proof (F1 i) as A; rewrite F2, (proj2 (Nat.ltb_lt _ _)) in A by lia.
  symmetry; exact A.
Qed.

Lemma nth_map_error {A B} (f : A -> B) (K : list A) i x d :
  nth_error K i = Some x -> nth i (map f K) d = f x.
Proof. intros H; apply nth_error_nth, map_nth_error, H. Qed.

(** Per label, an adjustment is explicit targets followed by pass-through. *)
Lemma view w es l :
  nlocal (NAdj w es) ->
  exists len P (L : list result),
    length L = len
    /\ (forall i, napply (NAdj w es) (mk_rvar l i)
                  = if Nat.ltb i len then nth i L (inl (mk_rvar l 0))
                    else inl (mk_rvar l (i - len + P)))
    /\ ~ (0 < len /\ 0 < P /\ napply (NAdj w es) (mk_rvar l (pred len)) = inl (mk_rvar l (pred P)))
    /\ match aget (label_key l) es with
       | None => len = 0 /\ P = dval w (label_key l)
       | Some e => elabel e = l /\ elen e = len /\ P = dval w (label_key l) + epass e
                   /\ L = map (fun t => tresult (tunshift w t)) (klist (etargets e))
       end.
Proof.
  intros Ha; pose proof Ha as [Hes [_ [Hent _]]].
  destruct (aget (label_key l) es) as [e|] eqn:E.
  - destruct (Hent _ _ E) as [Hok _]; destruct e as [h ts len p].
    destruct Hok as [Hk [Hg [Hlen [_ Hstrip]]]]; apply label_key_inj in Hk; subst h.
    set (g := fun t => tresult (tunshift w t)).
    assert (Hn : forall i, i < len -> exists t, knth ts i = Some t /\ nth_error (klist ts) i = Some t).
    { intros i Hi; rewrite knth_spec by (apply kgood_shape, Hg).
      destruct (nth_error (klist ts) i) as [t|] eqn:Ei; [eauto|].
      apply nth_error_None in Ei; rewrite klength_klist in Ei by exact Hg; lia. }
    exists len, (dval w (label_key l) + p), (map g (klist ts)).
    split; [rewrite length_map, klength_klist by exact Hg; exact Hlen|split; [|split]].
    + intros i; unfold napply; cbn [v_label v_index]; rewrite E; cbn [eapply].
      destruct (Nat.ltb_spec i len) as [Hi|Hi].
      * destruct (Hn i Hi) as [t [Et Ei]]; rewrite Et; symmetry; apply (nth_map_error g _ _ _ _ Ei).
      * f_equal; f_equal; lia.
    + intros [Hl0 [HP Hf]]; destruct (Hn (pred len) ltac:(lia)) as [t [Et _]].
      unfold napply in Hf; cbn [v_label v_index] in Hf; rewrite E in Hf; cbn [eapply] in Hf.
      rewrite (proj2 (Nat.ltb_lt _ _)) in Hf by lia; rewrite Et in Hf.
      destruct t as [y j|u [r es']]; cbn in Hf; [|discriminate].
      injection Hf as Hy Hj; subst y.
      destruct p as [|p]; [lia|].
      apply Hstrip; split; [exact Hl0|split; [lia|]]; rewrite Et; do 2 f_equal; cbn; lia.
    + cbn; repeat split; reflexivity.
  - exists 0, (dval w (label_key l)), []; split; [reflexivity|split; [|split]].
    + intros i; unfold napply; cbn [v_label v_index]; rewrite E; cbn; f_equal; f_equal; lia.
    + intros [H _]; lia.
    + split; reflexivity.
Qed.

Lemma tresult_inj (t1 t2 : target) : tresult t1 = tresult t2 -> t1 = t2.
Proof. destruct t1, t2; cbn; intros H; try discriminate; injection H; intros; subst; reflexivity. Qed.



Lemma entry_label w es k e : nlocal (NAdj w es) -> aget k es = Some e -> k = label_key (elabel e).
Proof.
  intros [_ [_ [Hent _]]] He; destruct (Hent _ _ He) as [Hok _].
  destruct e; destruct Hok as [Hk _]; symmetry; exact Hk.
Qed.

Lemma entry_nontrivial w es k e : nlocal (NAdj w es) -> aget k es = Some e -> 0 < elen e \/ 0 < epass e.
Proof.
  intros [_ [_ [Hent _]]] He; destruct (Hent _ _ He) as [Hok _].
  destruct e; destruct Hok as [_ [_ [_ [H _]]]]; exact H.
Qed.

(** Each label's entry is determined by the meaning, given the root counts. *)
Theorem entries_determined w es1 es2 :
  nlocal (NAdj w es1) -> nlocal (NAdj w es2) ->
  (forall v, napply (NAdj w es1) v = napply (NAdj w es2) v) ->
  forall l, aget (label_key l) es1 = aget (label_key l) es2.
Proof.
  intros H1 H2 Heq l.
  - destruct (view w es1 l H1) as [len1 [P1 [L1 [HL1 [F1 [S1 V1]]]]]].
    destruct (view w es2 l H2) as [len2 [P2 [L2 [HL2 [F2 [S2 V2]]]]]].
    assert (Hf : forall i, napply (NAdj w es1) (mk_rvar l i) = napply (NAdj w es2) (mk_rvar l i))
      by (intro i; apply Heq).
    destruct (decomp_unique (fun i => napply (NAdj w es1) (mk_rvar l i)) l len1 P1 L1 len2 P2 L2
                HL1 HL2 F1 (fun i => eq_trans (Hf i) (F2 i)) S1
                (fun H => S2 ltac:(destruct H as [A [B C]]; split; [exact A|split; [exact B|]];
                                     rewrite <- Hf; exact C)))
      as [<- [<- <-]].
    destruct (aget (label_key l) es1) as [e1|] eqn:E1, (aget (label_key l) es2) as [e2|] eqn:E2.
    + destruct V1 as [Hl1 [Hn1 [Hp1 HL]]], V2 as [Hl2 [Hn2 [Hp2 HL']]]; f_equal.
      assert (Hk1 := kgood_entry w es1 _ _ H1 E1); assert (Hk2 := kgood_entry w es2 _ _ H2 E2).
      destruct e1 as [h1 ts1 n1 p1], e2 as [h2 ts2 n2 p2]; cbn [elabel elen epass etargets] in *.
      subst h1 h2 n1 n2; assert (p1 = p2) as -> by lia.
      f_equal; apply kcanonical; [apply Hk1|apply Hk2|].
      apply (map_inj (fun t => tresult (tunshift w t))); [|congruence].
      intros x y E; apply tresult_inj in E; exact (unshift_inj (X:=target) w x y E).
    + exfalso; destruct V1 as [_ [Hn1 [Hp1 _]]], V2 as [Hn2 Hp2].
      destruct (entry_nontrivial w es1 _ _ H1 E1); lia.
    + exfalso; destruct V2 as [_ [Hn2 [Hp2 _]]], V1 as [Hn1 Hp1].
      destruct (entry_nontrivial w es2 _ _ H2 E2); lia.
    + reflexivity.
Qed.

(** *** A label whose key is outside any two tries *)

Fixpoint long_label (n : nat) : String.string :=
  match n with
  | 0 => String.EmptyString
  | S n => String.String (Ascii.Ascii false false false false false false false false) (long_label n)
  end.

Lemma size_push_ascii a p : Pos.size_nat (push_ascii a p) = 8 + Pos.size_nat p.
Proof. destruct a as [[] [] [] [] [] [] [] []]; reflexivity. Qed.

Lemma size_string_key s : Pos.size_nat (string_key s) = S (8 * String.length s).
Proof.
  induction s as [|a s IH]; [reflexivity|]; cbn [string_key String.length].
  rewrite size_push_ascii, IH; lia.
Qed.

Lemma fresh_label {A B} (m1 : tree A) (m2 : tree B) :
  exists l, get (label_key l) m1 = None /\ get (label_key l) m2 = None.
Proof.
  set (n := tdepth m1 + tdepth m2).
  assert (Hlen : String.length (long_label n) = n) by (induction n; cbn; congruence).
  exists (Some (long_label n)); split; apply get_deep; cbn [label_key Pos.size_nat];
    rewrite size_string_key, Hlen; unfold n; lia.
Qed.

(** A named label outside any finite set of tries. *)
Lemma fresh_label_list {A} (ms : list (tree A)) :
  exists s, forall m, In m ms -> get (label_key (Some s)) m = None.
Proof.
  set (n := S (fold_right (fun m acc => tdepth m + acc) 0 ms)).
  assert (Hlen : String.length (long_label n) = n) by (induction n; cbn; congruence).
  exists (long_label n); intros m Hm; apply get_deep; cbn [label_key Pos.size_nat].
  rewrite size_string_key, Hlen.
  assert (tdepth m <= fold_right (fun m acc => tdepth m + acc) 0 ms).
  { clear -Hm; induction ms as [|m' ms IH]; [destruct Hm|cbn; destruct Hm as [->|Hm]; [lia|specialize (IH Hm); lia]]. }
  unfold n; lia.
Qed.

(** *** Canonicity *)

Theorem ncanonical a1 a2 :
  nlocal a1 -> nlocal a2 ->
  (forall v, napply a1 v = napply a2 v) -> a1 = a2.
Proof.
  intros H1 H2 Heq; pose proof (root_determined a1 a2 H1 H2 Heq) as Hw.
  destruct a1 as [w1 es1], a2 as [w2 es2]; cbn [nroot] in Hw.
  assert (W : w1 = w2).
  { pose proof H1 as [_ [K1 _]]; pose proof H2 as [_ [K2 _]].
    apply counts_ext; intro k.
    destruct (get k (c_exc w1)) as [v1|] eqn:G1.
    { destruct (K1 _ _ G1) as [l ->]; apply Hw. }
    destruct (get k (c_exc w2)) as [v2|] eqn:G2.
    { destruct (K2 _ _ G2) as [l ->]; apply Hw. }
    destruct (fresh_label (c_exc w1) (c_exc w2)) as [l [F1 F2]].
    pose proof (Hw l) as E; unfold cget in E |- *; rewrite F1, F2 in E; rewrite G1, G2; exact E. }
  subst w2; f_equal; apply acanonical; [apply H1|apply H2|]; intro k.
  destruct (aget k es1) as [e1|] eqn:E1.
  - pose proof (entries_determined w1 es1 es2 H1 H2 Heq (elabel e1)) as D.
    rewrite <- (entry_label w1 es1 _ _ H1 E1), E1 in D; exact D.
  - destruct (aget k es2) as [e2|] eqn:E2; [|reflexivity].
    pose proof (entries_determined w1 es1 es2 H1 H2 Heq (elabel e2)) as D.
    rewrite <- (entry_label w1 es2 _ _ H2 E2), E1, E2 in D; exact D.
Qed.

End Canonical.

(** ** Deciding the one-level normal form *)

Definition is_label_key (k : positive) : bool :=
  match key_label k with Some l => Pos.eqb (label_key l) k | None => false end.

Lemma is_label_key_spec k : is_label_key k = true <-> exists l, k = label_key l.
Proof.
  unfold is_label_key; destruct (key_label k) as [l|] eqn:Kl.
  - rewrite Pos.eqb_eq; split; [intros <-; eauto|intros [l' ->]; rewrite key_label_spec in Kl; congruence].
  - split; [discriminate|intros [l' ->]; rewrite key_label_spec in Kl; discriminate].
Qed.

Definition keyedb (c : counts) : bool := forallb (fun k _ => is_label_key k) (c_exc c).

Lemma keyedb_spec c : keyedb c = true <-> keyed c.
Proof.
  unfold keyedb, keyed; rewrite forallb_spec; split; intros H k v E; apply is_label_key_spec, (H k v E).
Qed.

Definition strip_okb (e : entry) : bool :=
  match e with
  | Entry h ts len p =>
      negb (Nat.ltb 0 len && Nat.ltb 0 p
            && match knth ts (pred len) with
               | Some (TVar y j) => label_eqb y h && Nat.eqb j (pred p)
               | _ => false
               end)
  end.

Lemma strip_okb_spec e : strip_okb e = true <-> strip_ok e.
Proof.
  destruct e as [h ts len p]; cbn [strip_okb strip_ok].
  rewrite negb_true_iff; split.
  - intros H [Hl [Hp Hn]]; rewrite Hn in H; rewrite (proj2 (Nat.ltb_lt _ _) Hl), (proj2 (Nat.ltb_lt _ _) Hp) in H.
    rewrite label_eqb_refl, Nat.eqb_refl in H; discriminate.
  - intros H; destruct (Nat.ltb_spec 0 len), (Nat.ltb_spec 0 p); cbn [andb]; try reflexivity.
    destruct (knth ts (pred len)) as [[y j|u rho]|] eqn:Et; try reflexivity.
    destruct (label_eqb_spec y h) as [->|]; [|reflexivity]; destruct (Nat.eqb_spec j (pred p)) as [->|]; [|reflexivity].
    exfalso; apply H; auto.
Qed.

Definition entry_okb (k : positive) (e : entry) : bool :=
  match e with
  | Entry h ts len p =>
      Pos.eqb (label_key h) k && kgoodb ts && Nat.eqb (klength ts) len
      && (Nat.ltb 0 len || Nat.ltb 0 p) && strip_okb e
  end.

Lemma entry_okb_spec k e : entry_okb k e = true <-> entry_ok k e.
Proof.
  destruct e as [h ts len p]; cbn [entry_okb entry_ok].
  rewrite !andb_true_iff, orb_true_iff, Pos.eqb_eq, kgoodb_spec, Nat.eqb_eq,
    !Nat.ltb_lt, strip_okb_spec; tauto.
Qed.

Definition nlocalb (a : nadj) : bool :=
  match a with
  | NAdj w es =>
      ainvb es && keyedb w
      && List.forallb (fun kx => entry_okb (fst kx) (snd kx) && oeqb (cget (aann es) (fst kx)) (Some 0))
                      (akeyed (fun k => k) es)
      && negb (oeqb (c_def w) None)
      && forallb (fun k v => negb (oeqb v None)) (c_exc w)
  end.

Lemma oeqb_none o : negb (oeqb o None) = true <-> o <> None.
Proof. destruct o; cbn; split; congruence || (intros; reflexivity) || (intros H; contradiction). Qed.

Theorem nlocalb_spec a : nlocalb a = true <-> nlocal a.
Proof.
  destruct a as [w es]; cbn [nlocalb nlocal].
  rewrite !andb_true_iff, ainvb_spec, keyedb_spec, oeqb_none, forallb_spec.
  rewrite (akeyed_forallb (fun k e => entry_okb k e && oeqb (cget (aann es) k) (Some 0)) es).
  assert (Hent : (forall k x, aget k es = Some x ->
                   (entry_okb k x && oeqb (cget (aann es) k) (Some 0)) = true)
                 <-> (forall k e, aget k es = Some e -> entry_ok k e /\ cget (aann es) k = Some 0)).
  { split; intros H k e E; specialize (H k e E); rewrite !andb_true_iff, entry_okb_spec, oeqb_spec in *; tauto. }
  rewrite Hent; clear Hent.
  (* every label is used *)
  assert (Hused : keyed w ->
                  ((c_def w <> None /\ forall k v, get k (c_exc w) = Some v -> negb (oeqb v None) = true)
                   <-> (forall l, cget w (label_key l) <> None))).
  { intros Kw; split.
    - intros [Hd He] l; unfold cget; destruct (get (label_key l) (c_exc w)) as [v|] eqn:G; [|exact Hd].
      apply oeqb_none, (He _ _ G).
    - intros H; split.
      + destruct (fresh_label_list [c_exc w]) as [s Hs]; specialize (Hs _ (or_introl eq_refl)).
        specialize (H (Some s)); unfold cget in H; rewrite Hs in H; exact H.
      + intros k v G; apply oeqb_none; destruct (Kw k v G) as [l ->].
        specialize (H l); unfold cget in H; rewrite G in H; exact H. }
  split.
  - intros [[[[Ha Kw] He] Hd] Hx].
    exact (conj Ha (conj Kw (conj He (proj1 (Hused Kw) (conj Hd Hx))))).
  - intros [Ha [Kw [He Hq]]]; apply (Hused Kw) in Hq as [Hd Hx].
    exact (conj (conj (conj (conj Ha Kw) He) Hd) Hx).
Qed.

End Repr.
