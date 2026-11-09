(** * Composition

    [compose a b] is [b] followed by [a]: a variable [b] sends to [y] goes
    where [a] sends [y], and a payload [(u, rho)] becomes
    [(u, restrict (a ∘ rho))].

    The composition is eager but pruned (Prune.v).  Above the thresholds
    [th] (the lengths of [a]'s explicit targets), [a] is the pure shift
    [unshift tau ∘ shift th], so any part of [b] whose uses clear the
    thresholds is moved by its counts alone.  The rest is mapped leaf by
    leaf, and the result is put back into normal form:

    - entries of [a] for labels [b] has no entry for are added, dropped by
      [b]'s root counts;
    - the root counts are recomputed, from the trie's counts and the
      identity starts of the labels with no entry;
    - a label without an entry whose identity start is above the new root
      gets a gap entry, and then an entry that has become the identity
      relative to the new root is removed (the two touch different keys).

    Only the entries the traversal visited, and the labels of [a], can need
    removing; only the labels [b]'s root weakens can need a gap. *)

From Stdlib Require Import PArith Arith Lia List Bool.
From ShiftedNames.Core Require Import Trie Label Var Counts Based Skew ATrie Prune Repr Point.
Import ListNotations.

Section Compose.

Context {T : Type}.

Local Notation nadj := (@nadj T).
Local Notation result := (@result T).
Local Notation entry := (@entry T).
Local Notation target := (@target T).

(** ** Count map helpers *)

(** Setting one key, keeping the exceptions canonical. *)
Definition cset (c : counts) (k : positive) (v : option nat) : counts :=
  mk_counts (c_def c) (if oeqb v (c_def c) then remove k (c_exc c) else set k v (c_exc c)).

(** The pointwise sum of two count maps, as totals. *)
Definition ctotal (c1 c2 : counts) : counts :=
  cmap2 (fun x y => Some (oval x + oval y)) c1 c2.

(** ** What [a] looks like above the thresholds *)

Variable a : nadj.

Definition wa : counts := nroot a.
Definition esa : atrie entry := nentries a.

(** [a]'s entries, relative to its root. *)
Definition aentries : list entry := aelems esa.

Definition th_tree : tree nat :=
  fold_right (fun e m => match e with
                         | Entry h _ len _ => if Nat.eqb len 0 then m else set (label_key h) len m
                         end) Empty aentries.

Definition th : counts := mk_counts None (map_filter (fun _ n => Some (Some n)) th_tree).

Definition tau : counts :=
  fold_right (fun e c => match e with
                         | Entry h _ _ p => cset c (label_key h) (Some (dval wa (label_key h) + p))
                         end) wa aentries.

Definition thv (h : option label) : nat := dval th (label_key h).
Definition tauv (h : option label) : nat := dval tau (label_key h).

(** [a]'s explicit targets for [h] from absolute input [s] on, absolute. *)
Definition aextra (h : option label) (s : nat) : list target :=
  match aget (label_key h) esa with
  | Some (Entry _ tsa _ _) => map (tunshift wa) (skipn s (klist tsa))
  | None => []
  end.

(** [a]'s entry for [h] with its first [n] inputs dropped, absolute. *)
Definition adrop (h : option label) (n : nat) : option entry :=
  match aget (label_key h) esa with
  | Some (Entry _ tsa lena pa) =>
      let p := dval wa (label_key h) + pa in
      if Nat.ltb n lena
      then Some (Entry h (kof_list (map (tunshift wa) (skipn n (klist tsa)))) (lena - n) p)
      else Some (Entry h KNil 0 (p + (n - lena)))
  | None => None
  end.

(** ** Entries *)

Definition rtarget (r : result) : target :=
  match r with inl v => TVar (v_label v) (v_index v) | inr (u, rho) => TBind u rho end.

(** Stripping a reversed target list against pass-through [p]. *)
Fixpoint rstrip (h : option label) (R : list target) (p : nat) : list target * nat :=
  match R, p with
  | t :: R', S p' => if tvar_at h p' t then rstrip h R' p' else (R, p)
  | _, _ => (R, p)
  end.

(** An absolute entry, stripped: the last target is checked in O(log n),
    and the sequence is rebuilt only if it strips. *)
Definition estrip (h : option label) (ts : kseq target) (len p : nat) : entry :=
  match len, p with
  | S len', S p' =>
      match knth ts len' with
      | Some t =>
          if tvar_at h p' t
          then let (R, p2) := rstrip h (rev (klist ts)) p in
               Entry h (kof_list (rev R)) (length R) p2
          else Entry h ts len p
      | None => Entry h ts len p
      end
  | _, _ => Entry h ts len p
  end.

(** The composite of an entry whose targets [ts1] are already mapped
    (absolute); [s] is its absolute pass-through start. *)
Definition ecomp (h : option label) (ts1 : kseq target) (len s : nat) : entry :=
  if Nat.leb (thv h) s
  then estrip h ts1 len (s - thv h + tauv h)
  else let ex := aextra h s in
       estrip h (kof_list (klist ts1 ++ ex)) (len + length ex) (tauv h).

(** ** Putting the result in normal form *)

Definition bl0 : tree nat := th_tree.

(** Add [a]'s entries for labels the composite has no entry for. *)
Definition add_aonly (W : counts) (es : atrie entry) : atrie entry :=
  fold_right (fun e es =>
                let h := elabel e in
                match aget (label_key h) es with
                | Some _ => es
                | None => aupdate (label_key h) (fun _ => adrop h (dval W (label_key h))) es
                end) es aentries.

(** Identity starts of the labels with no entry of [a]. *)
Definition jstarts (W : counts) : counts :=
  fold_right (fun e c => cset c (label_key (elabel e)) None) (ctotal wa W) aentries.

(** Remove an entry that is the identity relative to the root. *)
Definition drop_ident (R : counts) (es : atrie entry) (k : positive) : atrie entry :=
  match aget k es with
  | Some (Entry _ KNil 0 p) =>
      if oeqb (cget R k) (Some p) then aupdate k (fun _ => None) es else es
  | _ => es
  end.

(** An absolute gap entry. *)
Definition agap (k : positive) (p : nat) : option entry :=
  match key_label k with
  | Some l => if Pos.eqb (label_key l) k then Some (Entry l KNil 0 p) else None
  | None => None
  end.

Definition add_gap_at (I R : counts) (es : atrie entry) (k : positive) : atrie entry :=
  match aget k es with
  | Some _ => es
  | None => if Nat.ltb (dval R k) (dval I k)
            then aupdate k (fun _ => agap k (dval I k)) es else es
  end.

Definition finish (W : counts) (es : atrie entry) (visited : list positive) : nadj :=
  let es1 := add_aonly W es in
  let R := cmin (aann es1) (jstarts W) in
  let keys_a := map (fun e => label_key (elabel e)) aentries in
  let I := ctotal wa W in
  let es2 := fold_left (add_gap_at I R) (map fst (elements (c_exc W))) es1 in
  let es3 := fold_left (drop_ident R) (visited ++ keys_a) es2 in
  NAdj R (arebase R es3).

(** Payloads only care about named labels: drop the bound label. *)
Definition restrict (c : nadj) : nadj :=
  match c with
  | NAdj R es =>
      let kN := label_key None in
      let es' := aupdate kN (fun _ => None) es in
      match cget (aann es') kN with
      | None => NAdj (cset R kN None) es'
      | Some n => NAdj (cset R kN (Some (dval R kN + n))) (arebase (cone kN n) es')
      end
  end.

(** ** The traversal *)

Fixpoint ncomp (b : nadj) (B : counts) {struct b} : nadj :=
  match b with
  | NAdj r es =>
      let tc := fun (B' : counts) (t : target) =>
                  match t with
                  | TVar y j => rtarget (napply a (mk_rvar y (dval B' (label_key y) + j)))
                  | TBind u rho => TBind u (restrict (ncomp rho B'))
                  end in
      let ec := fun (B' : counts) (e : entry) =>
                  match e with
                  | Entry h ts len p =>
                      ecomp h (kmap th tau tc bl0 B' ts) len (dval B' (label_key h) + p)
                  end in
      let P := cplus B r in
      finish (cadd B r) (atmap th tau ec bl0 P es) (@atvisit entry bl0 P (fun k => k) es)
  end.

Definition compose (b : nadj) : nadj := ncomp b cnone.

(** ** Proofs: count map helpers *)

Lemma cget_cset c k v k' : cget (cset c k v) k' = if Pos.eqb k' k then v else cget c k'.
Proof.
  unfold cset, cget; cbn [c_exc c_def].
  destruct (oeqb v (c_def c)) eqn:E; [rewrite get_remove|rewrite get_set];
    destruct (Pos.eqb k' k); try reflexivity.
  apply oeqb_spec in E; symmetry; exact E.
Qed.

Lemma cwf_cset c k v : cwf c -> cwf (cset c k v).
Proof.
  intros Hc k' v'; unfold cset; cbn [c_exc c_def].
  destruct (oeqb v (c_def c)) eqn:E.
  - rewrite get_remove; destruct (Pos.eqb k' k); [discriminate|apply Hc].
  - rewrite get_set; destruct (Pos.eqb k' k); [intros [= <-] H; rewrite H, oeqb_refl in E; discriminate|apply Hc].
Qed.

Lemma cget_ctotal c1 c2 k : cget (ctotal c1 c2) k = Some (oval (cget c1 k) + oval (cget c2 k)).
Proof. unfold ctotal; rewrite cget_cmap2; reflexivity. Qed.

(** ** Proofs: [a] above the thresholds *)

Hypothesis Ha : nlocal Qall a.

Lemma esa_key k e : aget k esa = Some e -> k = label_key (elabel e).
Proof. unfold esa; destruct a as [w es]; cbn; apply (entry_label Qall w es), Ha. Qed.

Lemma aentries_get e : In e aentries -> aget (label_key (elabel e)) esa = Some e.
Proof.
  intros Hin; destruct (aelems_aget esa e Hin) as [k E].
  rewrite <- (esa_key k e E); exact E.
Qed.

Lemma aentries_in k e : aget k esa = Some e -> In e aentries.
Proof. apply aget_in. Qed.

Lemma th_tree_spec k :
  get k th_tree = match aget k esa with
                  | Some (Entry _ _ len _) => if Nat.eqb len 0 then None else Some len
                  | None => None
                  end.
Proof.
  assert (H : forall L, (forall e, In e L -> In e aentries) ->
            get k (fold_right (fun e m => match e with
                                          | Entry h _ len _ => if Nat.eqb len 0 then m else set (label_key h) len m
                                          end) Empty L)
            = match aget k esa with
              | Some (Entry _ _ len _) =>
                  if existsb (fun e => Pos.eqb (label_key (elabel e)) k && negb (Nat.eqb (elen e) 0)) L
                  then Some len else None
              | _ => None
              end).
  { induction L as [|e L IH]; intros HL; cbn [fold_right existsb].
    - rewrite get_Empty; destruct (aget k esa) as [[]|]; reflexivity.
    - assert (IH' := IH ltac:(intros; apply HL; right; assumption)).
      destruct e as [h ts len p]; cbn [elabel elen].
      destruct (Nat.eqb_spec len 0) as [->|Hl]; cbn [negb andb orb].
      + rewrite andb_false_r; exact IH'.
      + rewrite get_set, andb_true_r, Pos.eqb_sym.
        destruct (Pos.eqb_spec (label_key h) k) as [<-|]; cbn [orb]; [|exact IH'].
        pose proof (aentries_get _ (HL _ (or_introl eq_refl))) as G; cbn [elabel] in G; rewrite G; reflexivity. }
  unfold th_tree; rewrite H by auto.
  destruct (aget k esa) as [[h ts len p]|] eqn:E; [|reflexivity].
  destruct (existsb _ aentries) eqn:X.
  - apply existsb_exists in X as [e [Hin He]]; apply andb_prop in He as [Hk Hlen].
    apply Pos.eqb_eq in Hk; subst k; rewrite (aentries_get e Hin) in E; injection E as ->.
    cbn in Hlen; destruct (Nat.eqb len 0); [discriminate|reflexivity].
  - destruct (Nat.eqb_spec len 0) as [|Hl]; [reflexivity|exfalso].
    assert (Hin := aentries_in _ _ E); pose proof (esa_key _ _ E) as Hk.
    assert (Hx : existsb (fun e => Pos.eqb (label_key (elabel e)) k && negb (Nat.eqb (elen e) 0)) aentries = true).
    { apply existsb_exists; exists (Entry h ts len p); split; [exact Hin|].
      cbn [elabel elen] in *; rewrite <- Hk, Pos.eqb_refl; destruct (Nat.eqb_spec len 0); [lia|reflexivity]. }
    congruence.
Qed.

Lemma cget_th k :
  cget th k = match aget k esa with
              | Some (Entry _ _ len _) => if Nat.eqb len 0 then None else Some len
              | None => None
              end.
Proof.
  unfold th, cget; cbn [c_exc c_def]; rewrite get_map_filter, th_tree_spec.
  destruct (aget k esa) as [[h ts len p]|]; [destruct (Nat.eqb len 0)|]; reflexivity.
Qed.

Lemma cget_tau k :
  cget tau k = match aget k esa with
               | Some (Entry _ _ _ p) => Some (dval wa k + p)
               | None => cget wa k
               end.
Proof.
  assert (H : forall L, (forall e, In e L -> In e aentries) ->
            cget (fold_right (fun e c => match e with
                                          | Entry h _ _ p => cset c (label_key h) (Some (dval wa (label_key h) + p))
                                          end) wa L) k
            = if existsb (fun e => Pos.eqb (label_key (elabel e)) k) L
              then match aget k esa with Some (Entry _ _ _ p) => Some (dval wa k + p) | None => cget wa k end
              else cget wa k).
  { induction L as [|e L IH]; intros HL; cbn [fold_right existsb]; [reflexivity|].
    destruct e as [h ts len p]; cbn [elabel]; rewrite cget_cset, Pos.eqb_sym.
    destruct (Pos.eqb_spec (label_key h) k) as [<-|]; cbn [orb].
    - pose proof (aentries_get _ (HL _ (or_introl eq_refl))) as G; cbn [elabel] in G; rewrite G; reflexivity.
    - apply IH; intros; apply HL; right; assumption. }
  unfold tau; rewrite H by auto.
  destruct (existsb _ aentries) eqn:X.
  - reflexivity.
  - destruct (aget k esa) as [e|] eqn:E; [exfalso|reflexivity].
    assert (Hx : existsb (fun e => Pos.eqb (label_key (elabel e)) k) aentries = true).
    { apply existsb_exists; exists e; split; [apply (aentries_in _ _ E)|].
      rewrite <- (esa_key _ _ E), Pos.eqb_refl; reflexivity. }
    congruence.
Qed.

(** Above its threshold, [a] is a pure shift. *)
Theorem napply_a_shift h j :
  thv h <= j -> napply a (mk_rvar h j) = inl (mk_rvar h (j - thv h + tauv h)).
Proof.
  unfold thv, tauv, dval; rewrite cget_th, cget_tau; unfold wa, esa.
  destruct a as [w es] eqn:Ea; cbn [napply v_label v_index wa nroot esa nentries] in *.
  destruct (aget (label_key h) es) as [[h' ts len p]|] eqn:E; intros Hj.
  - pose proof (entry_label Qall w es _ _ Ha E) as Hk; cbn in Hk; apply label_key_inj in Hk; subst h'.
    cbn [eapply]; destruct (Nat.eqb_spec len 0) as [->|Hl]; cbn [oval] in *.
    + destruct (Nat.ltb_spec j 0); [lia|]; f_equal; f_equal; lia.
    + destruct (Nat.ltb_spec j len); [lia|]; f_equal; f_equal; unfold dval; lia.
  - cbn [oval] in Hj |- *; f_equal; f_equal; unfold dval; lia.
Qed.

(** ** Proofs: absolute entries and stripping *)

(** Where a target list followed by pass-through [p] sends input [i]. *)
Definition lapp (h : option label) (L : list target) (p i : nat) : result :=
  if Nat.ltb i (length L)
  then match nth_error L i with Some t => tresult t | None => inl (mk_rvar h i) end
  else inl (mk_rvar h (i - length L + p)).

(** An absolute entry's meaning. *)
Definition eabs (e : entry) (i : nat) : result :=
  match e with Entry h ts _ p => lapp h (klist ts) p i end.

Lemma tvar_at_spec h p (t : target) : tvar_at h p t = true <-> t = TVar h p.
Proof.
  destruct t as [y j|u rho]; cbn; [|split; discriminate].
  rewrite andb_true_iff, label_eqb_eq, Nat.eqb_eq; split; [intros [-> ->]; reflexivity|intros [= -> ->]; auto].
Qed.

Lemma rstrip_spec h R p :
  forall R2 p2, rstrip h R p = (R2, p2) ->
  (forall i, lapp h (rev R2) p2 i = lapp h (rev R) p i)
  /\ ~ (exists t R' p', R2 = t :: R' /\ p2 = S p' /\ t = TVar h p').
Proof.
  revert p; induction R as [|t R IH]; intros p R2 p2 E; cbn [rstrip] in E.
  - destruct p; injection E as <- <-; (split; [reflexivity|intros [t [R' [p' [H _]]]]; discriminate]).
  - destruct p as [|p'].
    + injection E as <- <-; split; [reflexivity|intros [t' [R' [p' [_ [H _]]]]]; discriminate].
    + destruct (tvar_at h p' t) eqn:Tv.
      * apply tvar_at_spec in Tv; subst t.
        destruct (IH p' R2 p2 E) as [Hm Hn]; split; [|exact Hn].
        intro i; rewrite Hm; unfold lapp; cbn [rev]; rewrite length_app; cbn [length].
        destruct (Nat.ltb_spec i (length (rev R))), (Nat.ltb_spec i (length (rev R) + 1)); try lia.
        -- rewrite nth_error_app1 by lia; reflexivity.
        -- assert (i = length (rev R)) by lia; subst i.
           rewrite nth_error_app2, Nat.sub_diag by lia; cbn; f_equal; f_equal; lia.
        -- f_equal; f_equal; lia.
      * injection E as <- <-; split; [reflexivity|].
        intros [t' [R' [p'' [[= <- <-] [[= <-] ->]]]]].
        rewrite (proj2 (tvar_at_spec _ _ _) eq_refl) in Tv; discriminate.
Qed.

Lemma lapp_klist h ts p i : eabs (Entry h ts (klength ts) p) i = lapp h (klist ts) p i.
Proof. reflexivity. Qed.

Lemma kgood_targets_ok (ts : kseq target) : kgood ts -> forall t, In t (klist ts) -> eok t.
Proof. intros G; apply kinv_ok, kgood_inv, G. Qed.

Definition entry_good (h : option label) (e : entry) : Prop :=
  match e with
  | Entry h' ts len p => h' = h /\ kgood ts /\ klength ts = len /\ strip_ok e
  end.

Lemma kof_list_good (L : list target) :
  (forall t, In t L -> eok t) -> kgood (kof_list L) /\ klist (kof_list L) = L
  /\ klength (kof_list L) = length L.
Proof.
  intros H; destruct (kgood_of_list L H) as [G E]; split; [exact G|split; [exact E|]].
  rewrite klength_spec by apply (kgood_shape _ G); rewrite E; reflexivity.
Qed.

Theorem estrip_spec h ts p :
  kgood ts ->
  entry_good h (estrip h ts (klength ts) p)
  /\ forall i, eabs (estrip h ts (klength ts) p) i = lapp h (klist ts) p i.
Proof.
  intros G; pose proof (kgood_targets_ok ts G) as Hok.
  assert (Hl : klength ts = length (klist ts)) by (apply klength_spec, kgood_shape, G).
  assert (Hplain : strip_ok (Entry h ts (klength ts) p) ->
                   entry_good h (Entry h ts (klength ts) p)
                   /\ forall i, eabs (Entry h ts (klength ts) p) i = lapp h (klist ts) p i)
    by (intros Hs; split; [split; [reflexivity|split; [exact G|split; [reflexivity|exact Hs]]]|reflexivity]).
  unfold estrip; destruct (klength ts) as [|len'] eqn:El, p as [|p']; try (apply Hplain; cbn; lia).
  destruct (knth ts len') as [t|] eqn:Et.
  - destruct (tvar_at h p' t) eqn:Tv.
    + destruct (rstrip h (rev (klist ts)) (S p')) as [R p2] eqn:Er.
      destruct (rstrip_spec h _ _ R p2 Er) as [Hm Hn].
      assert (HokR : forall t, In t (rev R) -> eok t).
      { intros t' Ht'.
        (* [R] is a suffix of the reversed list *)
        assert (Hsuf : forall R0 q R1 q1, rstrip h R0 q = (R1, q1) -> forall x, In x R1 -> In x R0).
        { induction R0 as [|x0 R0 IH0]; intros q R1 q1 E x Hx; cbn [rstrip] in E.
          - destruct q; injection E as <- <-; exact Hx.
          - destruct q as [|q']; [injection E as <- <-; exact Hx|].
            destruct (tvar_at h q' x0); [right; apply (IH0 _ _ _ E _ Hx)|injection E as <- <-; exact Hx]. }
        assert (H1 : In t' R) by (apply in_rev; exact Ht').
        apply (Hsuf _ _ _ _ Er) in H1; apply Hok, in_rev, H1. }
      destruct (kof_list_good (rev R) HokR) as [G' [E' L']].
      split.
      * split; [reflexivity|split; [exact G'|split; [rewrite L', length_rev; reflexivity|]]].
        cbn [strip_ok]; intros [Hlen [Hp Hn']]; apply Hn.
        rewrite knth_spec in Hn' by apply (kgood_shape _ G'); rewrite E' in Hn'.
        destruct R as [|t0 R']; [cbn in Hlen; lia|].
        exists t0, R', (pred p2); split; [reflexivity|].
        cbn [rev length pred] in Hn'.
        rewrite nth_error_app2 in Hn' by (rewrite length_rev; lia).
        rewrite length_rev, Nat.sub_diag in Hn'; cbn in Hn'; injection Hn' as ->.
        split; [|reflexivity]; destruct p2; [lia|reflexivity].
      * intro i; cbn [eabs]; rewrite E', Hm, rev_involutive; reflexivity.
    + apply Hplain; cbn [strip_ok pred]; intros [_ [_ Hn]]; rewrite Et in Hn; injection Hn as ->.
      rewrite (proj2 (tvar_at_spec _ _ _) eq_refl) in Tv; discriminate.
  - apply Hplain; cbn [strip_ok pred]; intros [_ [_ Hn]]; rewrite Et in Hn; discriminate.
Qed.

(** ** Proofs: [a] on one label, as a list and a pass-through *)

Definition alist (h : option label) : list target :=
  match aget (label_key h) esa with
  | Some (Entry _ tsa _ _) => map (tunshift wa) (klist tsa)
  | None => []
  end.

Lemma esa_ok k e : aget k esa = Some e -> entry_ok k e.
Proof.
  unfold esa; destruct a as [w es]; cbn; intros E.
  destruct Ha as [_ [_ [_ [Hent _]]]]; apply (Hent _ _ E).
Qed.

Lemma alist_ok h t : In t (alist h) -> eok t.
Proof.
  unfold alist; destruct (aget (label_key h) esa) as [[h' tsa len p]|] eqn:E; [|intros []].
  intros Hin; apply in_map_iff in Hin as [t0 [<- Hin]].
  destruct (esa_ok _ _ E) as [_ [G _]].
  exact (ok_unshift wa t0 (kgood_targets_ok tsa G _ Hin)).
Qed.

Lemma length_alist h : length (alist h) = thv h.
Proof.
  unfold alist, thv, dval; rewrite cget_th.
  destruct (aget (label_key h) esa) as [[h' tsa len p]|] eqn:E; [|reflexivity].
  destruct (esa_ok _ _ E) as [_ [G [Hl _]]].
  rewrite length_map, <- (klength_spec _ (kgood_shape _ G)), Hl.
  destruct (Nat.eqb_spec len 0); cbn; lia.
Qed.

Theorem napply_a_lapp h j : napply a (mk_rvar h j) = lapp h (alist h) (tauv h) j.
Proof.
  unfold alist, tauv, dval; rewrite cget_tau.
  assert (Hn : napply a (mk_rvar h j)
               = match aget (label_key h) esa with
                 | None => inl (mk_rvar h (dval wa (label_key h) + j))
                 | Some e => eapply wa e j
                 end) by (unfold esa, wa; destruct a; reflexivity).
  rewrite Hn; destruct (aget (label_key h) esa) as [[h' tsa len p]|] eqn:E.
  - destruct (esa_ok _ _ E) as [Hk [G [Hl _]]]; apply label_key_inj in Hk; subst h'.
    assert (HL : length (klist tsa) = len) by (rewrite <- Hl; symmetry; apply klength_spec, kgood_shape, G).
    unfold lapp; cbn [eapply]; rewrite length_map, HL, nth_error_map, <- knth_spec by apply (kgood_shape _ G).
    destruct (Nat.ltb_spec j len); [|cbn [oval]; f_equal; f_equal; unfold dval; lia].
    destruct (knth_some tsa j G ltac:(lia)) as [t ->]; reflexivity.
  - unfold lapp; cbn [length]; destruct (Nat.ltb_spec j 0); [lia|]; f_equal; f_equal; unfold dval; lia.
Qed.

Lemma aextra_alist h s : aextra h s = skipn s (alist h).
Proof.
  unfold aextra, alist; destruct (aget (label_key h) esa) as [[]|]; [|destruct s]; try reflexivity.
  rewrite skipn_map; reflexivity.
Qed.

(** The composite of one entry: its mapped targets, then where [a] sends
    its pass-through. *)
Theorem ecomp_spec h ts1 s :
  kgood ts1 ->
  entry_good h (ecomp h ts1 (klength ts1) s)
  /\ forall i, eabs (ecomp h ts1 (klength ts1) s) i
               = if Nat.ltb i (klength ts1)
                 then lapp h (klist ts1) 0 i
                 else napply a (mk_rvar h (s + (i - klength ts1))).
Proof.
  intros G; assert (HL : klength ts1 = length (klist ts1)) by apply klength_spec, kgood_shape, G.
  unfold ecomp; destruct (Nat.leb_spec (thv h) s) as [Hs|Hs].
  - destruct (estrip_spec h ts1 (s - thv h + tauv h) G) as [Hg Hm]; split; [exact Hg|intro i].
    rewrite Hm; unfold lapp; rewrite <- HL.
    destruct (Nat.ltb_spec i (klength ts1)); [reflexivity|].
    rewrite napply_a_shift by lia; f_equal; f_equal; lia.
  - set (ex := aextra h s).
    assert (Hex : ex = skipn s (alist h)) by apply aextra_alist.
    assert (Hlex : length ex = thv h - s) by (rewrite Hex, length_skipn, length_alist; reflexivity).
    assert (Hok : forall t, In t (klist ts1 ++ ex) -> eok t).
    { intros t Ht; apply in_app_or in Ht as [Ht|Ht]; [apply (kgood_targets_ok _ G _ Ht)|].
      rewrite Hex in Ht; apply (alist_ok h).
      rewrite <- (firstn_skipn s (alist h)); apply in_or_app; right; exact Ht. }
    destruct (kof_list_good (klist ts1 ++ ex) Hok) as [G2 [E2 L2]].
    assert (Hlen : klength ts1 + length ex = klength (kof_list (klist ts1 ++ ex)))
      by (rewrite L2, length_app, HL; reflexivity).
    rewrite Hlen; destruct (estrip_spec h _ (tauv h) G2) as [Hg Hm]; split; [exact Hg|intro i].
    rewrite Hm, E2; unfold lapp; rewrite length_app, <- HL.
    destruct (Nat.ltb_spec i (klength ts1)) as [Hi|Hi].
    + destruct (Nat.ltb_spec i (klength ts1 + length ex)); [|lia].
      rewrite nth_error_app1 by lia; reflexivity.
    + rewrite napply_a_lapp; unfold lapp; rewrite length_alist.
      destruct (Nat.ltb_spec i (klength ts1 + length ex)), (Nat.ltb_spec (s + (i - klength ts1)) (thv h));
        try lia.
      * rewrite nth_error_app2 by lia; rewrite <- HL, Hex, nth_error_skipn.
        destruct (nth_error (alist h) _) eqn:En; [reflexivity|apply nth_error_None in En; rewrite length_alist in En; lia].
      * f_equal; f_equal; lia.
Qed.

(** An entry of [a] with its first [n] inputs dropped. *)
Theorem adrop_spec h n e :
  adrop h n = Some e ->
  entry_good h e /\ forall i, eabs e i = napply a (mk_rvar h (n + i)).
Proof.
  unfold adrop; destruct (aget (label_key h) esa) as [[h' tsa lena pa]|] eqn:E; [|discriminate].
  destruct (esa_ok _ _ E) as [Hk [G [Hl [_ Hs]]]]; apply label_key_inj in Hk; subst h'.
  assert (HL : length (klist tsa) = lena) by (rewrite <- Hl; symmetry; apply klength_spec, kgood_shape, G).
  assert (Hal : alist h = map (tunshift wa) (klist tsa)) by (unfold alist; rewrite E; reflexivity).
  assert (Hta : tauv h = dval wa (label_key h) + pa) by (unfold tauv, dval; rewrite cget_tau, E; reflexivity).
  destruct (Nat.ltb_spec n lena) as [Hn|Hn]; intros [= <-].
  - set (L := map (tunshift wa) (skipn n (klist tsa))).
    assert (Hok : forall t, In t L -> eok t).
    { intros t Ht; apply (alist_ok h); rewrite Hal; unfold L in Ht; rewrite <- skipn_map in Ht.
      rewrite <- (firstn_skipn n (map (tunshift wa) (klist tsa))); apply in_or_app; right; exact Ht. }
    destruct (kof_list_good L Hok) as [G2 [E2 L2]].
    assert (HLL : length L = lena - n) by (unfold L; rewrite length_map, length_skipn, HL; reflexivity).
    split.
    + split; [reflexivity|split; [exact G2|split; [rewrite L2; exact HLL|]]].
      cbn [strip_ok]; intros [Hlen [Hp Hlast]]; apply Hs; split; [lia|].
      rewrite knth_spec in Hlast by apply (kgood_shape _ G2); rewrite E2 in Hlast.
      unfold L in Hlast; rewrite nth_error_map, nth_error_skipn in Hlast.
      rewrite knth_spec by apply (kgood_shape _ G).
      replace (n + pred (lena - n)) with (pred lena) in Hlast by lia.
      destruct (nth_error (klist tsa) (pred lena)) as [[y j|u [r es]]|]; cbn in Hlast; try discriminate.
      injection Hlast as -> Hj; unfold dval in Hj, Hp.
      destruct pa as [|pa']; [cbn in Hj; lia|split; [lia|f_equal; f_equal; cbn; lia]].
    + intro i; cbn [eabs]; rewrite E2, napply_a_lapp, Hal; unfold lapp.
      rewrite HLL, length_map, HL; unfold L; rewrite nth_error_map, nth_error_skipn, nth_error_map.
      destruct (Nat.ltb_spec i (lena - n)), (Nat.ltb_spec (n + i) lena); try lia.
      * destruct (nth_error (klist tsa) (n + i)) eqn:En; [reflexivity|].
        apply nth_error_None in En; lia.
      * rewrite Hta; f_equal; f_equal; lia.
  - split.
    + split; [reflexivity|split; [apply kgood_nil|split; [reflexivity|cbn; lia]]].
    + intro i; cbn [eabs klist]; rewrite napply_a_lapp, Hal; unfold lapp.
      rewrite length_map, HL; cbn [length]; destruct (Nat.ltb_spec i 0); [lia|].
      destruct (Nat.ltb_spec (n + i) lena); [lia|]; rewrite Hta; f_equal; f_equal; lia.
Qed.

(** ** Proofs: the steps of [finish] *)

Lemma kgood_cwf (ts : kseq target) : kgood ts -> cwf (ksann ts).
Proof. intros [Hi _]; destruct ts as [|c w t s]; [apply cwf_cnone|destruct Hi as [_ [H _]]; exact H]. Qed.

Lemma entry_good_ok h e : entry_good h e -> eok e.
Proof. destruct e as [h' ts len p]; intros [_ [G _]]; apply kgood_cwf, G. Qed.

Lemma ook_adrop h n : ook (adrop h n).
Proof.
  destruct (adrop h n) as [e|] eqn:E; [|exact I].
  apply (entry_good_ok h), (proj1 (adrop_spec h n e E)).
Qed.

Theorem add_aonly_spec W es :
  ainv es ->
  ainv (add_aonly W es)
  /\ forall k, aget k (add_aonly W es)
               = match aget k es with
                 | Some e => Some e
                 | None => match aget k esa with
                           | Some ea => adrop (elabel ea) (dval W k)
                           | None => None
                           end
                 end.
Proof.
  intros Hes.
  assert (H : forall L, (forall e, In e L -> In e aentries) ->
            ainv (fold_right (fun e es =>
                                let h := elabel e in
                                match aget (label_key h) es with
                                | Some _ => es
                                | None => aupdate (label_key h) (fun _ => adrop h (dval W (label_key h))) es
                                end) es L)
            /\ forall k, aget k (fold_right (fun e es =>
                                let h := elabel e in
                                match aget (label_key h) es with
                                | Some _ => es
                                | None => aupdate (label_key h) (fun _ => adrop h (dval W (label_key h))) es
                                end) es L)
                         = match aget k es with
                           | Some e => Some e
                           | None => if existsb (fun e => Pos.eqb (label_key (elabel e)) k) L
                                     then match aget k esa with
                                          | Some ea => adrop (elabel ea) (dval W k)
                                          | None => None
                                          end
                                     else None
                           end).
  { induction L as [|e L IH]; intros HL; cbn [fold_right existsb].
    - split; [exact Hes|intro k; destruct (aget k es); reflexivity].
    - destruct (IH (fun e' H' => HL e' (or_intror H'))) as [Hi Hg].
      set (es' := fold_right _ es L) in *.
      pose proof (aentries_get e (HL e (or_introl eq_refl))) as Ge.
      destruct (aget (label_key (elabel e)) es') as [e0|] eqn:E0.
      + split; [exact Hi|intro k; rewrite Hg].
        destruct (Pos.eqb_spec (label_key (elabel e)) k) as [<-|]; cbn [orb]; [|reflexivity].
        rewrite Hg in E0; destruct (aget _ es) as [e1|]; [reflexivity|].
        destruct (existsb _ L); [rewrite Ge in E0 |- *; congruence|discriminate].
      + destruct (aupdate_spec (label_key (elabel e)) (fun _ => adrop (elabel e) (dval W (label_key (elabel e)))) es' Hi
                    (fun _ _ => ook_adrop _ _)) as [Ha' Hg'].
        split; [exact Ha'|intro k; rewrite Hg', Pos.eqb_sym].
        destruct (Pos.eqb_spec (label_key (elabel e)) k) as [<-|]; cbn [orb].
        * rewrite Hg in E0; rewrite Ge.
          destruct (aget _ es); [discriminate|reflexivity].
        * rewrite Hg; reflexivity. }
  destruct (H aentries (fun e H => H)) as [Hi Hg]; split; [exact Hi|intro k].
  unfold add_aonly; rewrite Hg; destruct (aget k es); [reflexivity|].
  destruct (existsb _ aentries) eqn:X; destruct (aget k esa) as [ea|] eqn:E; try reflexivity.
  exfalso; assert (Hx : existsb (fun e => Pos.eqb (label_key (elabel e)) k) aentries = true)
    by (apply existsb_exists; exists ea; split; [apply (aentries_in _ _ E)|rewrite <- (esa_key _ _ E), Pos.eqb_refl; reflexivity]).
  congruence.
Qed.

(** Folding per-key updates, each idempotent, over a list of keys. *)
Lemma fold_keyed (step : atrie entry -> positive -> atrie entry)
      (g : positive -> option entry -> option entry) :
  (forall es k, ainv es -> ainv (step es k)
                /\ forall k', aget k' (step es k) = if Pos.eqb k' k then g k (aget k es) else aget k' es) ->
  (forall k o, g k (g k o) = g k o) ->
  forall L es, ainv es ->
  ainv (fold_left step L es)
  /\ forall k', aget k' (fold_left step L es)
                = if existsb (Pos.eqb k') L then g k' (aget k' es) else aget k' es.
Proof.
  intros Hstep Hid L; induction L as [|k L IH]; intros es Hes; cbn [fold_left existsb].
  - split; [exact Hes|reflexivity].
  - destruct (Hstep es k Hes) as [H1 G1]; destruct (IH _ H1) as [H2 G2]; split; [exact H2|intro k'].
    rewrite G2, G1; destruct (Pos.eqb_spec k' k) as [->|]; cbn [orb].
    + destruct (existsb _ L); [apply Hid|reflexivity].
    + reflexivity.
Qed.

Definition dropf (R : counts) (k : positive) (o : option entry) : option entry :=
  match o with
  | Some (Entry _ KNil 0 p) => if oeqb (cget R k) (Some p) then None else o
  | _ => o
  end.

Lemma drop_ident_step R es k :
  ainv es -> ainv (drop_ident R es k)
  /\ forall k', aget k' (drop_ident R es k) = if Pos.eqb k' k then dropf R k (aget k es) else aget k' es.
Proof.
  intros Hes; unfold drop_ident, dropf.
  assert (Hsame : ainv es /\ forall k', aget k' es = if Pos.eqb k' k then aget k es else aget k' es)
    by (split; [exact Hes|intro k'; destruct (Pos.eqb_spec k' k) as [->|]; reflexivity]).
  destruct (aget k es) as [[h [|c w t s] [|len] p]|] eqn:E; try exact Hsame.
  destruct (oeqb (cget R k) (Some p)); [|exact Hsame].
  destruct (aupdate_spec k (fun _ => None) es Hes (fun _ _ => I)) as [Ha' Hg]; split; [exact Ha'|].
  intro k'; rewrite Hg; reflexivity.
Qed.

Lemma dropf_idem R k o : dropf R k (dropf R k o) = dropf R k o.
Proof.
  destruct o as [[h [|c w t s] [|len] p]|]; cbn; try reflexivity.
  destruct (oeqb (cget R k) (Some p)) eqn:E; cbn; [reflexivity|rewrite E; reflexivity].
Qed.

Definition gapf (I R : counts) (k : positive) (o : option entry) : option entry :=
  match o with
  | Some e => Some e
  | None => if Nat.ltb (dval R k) (dval I k) then agap k (dval I k) else None
  end.

Lemma ook_agap k p : ook (agap k p).
Proof.
  unfold agap; destruct (key_label k); [|exact I].
  destruct (Pos.eqb _ _); [apply cwf_cnone|exact I].
Qed.

Lemma add_gap_step I R es k :
  ainv es -> ainv (add_gap_at I R es k)
  /\ forall k', aget k' (add_gap_at I R es k) = if Pos.eqb k' k then gapf I R k (aget k es) else aget k' es.
Proof.
  intros Hes; unfold add_gap_at, gapf.
  assert (Hsame : ainv es /\ forall k', aget k' es = if Pos.eqb k' k then aget k es else aget k' es)
    by (split; [exact Hes|intro k'; destruct (Pos.eqb_spec k' k) as [->|]; reflexivity]).
  destruct (aget k es) as [e|] eqn:E; [exact Hsame|].
  destruct (Nat.ltb (dval R k) (dval I k)); [|exact Hsame].
  destruct (aupdate_spec k (fun _ => agap k (dval I k)) es Hes (fun _ _ => ook_agap _ _)) as [Ha' Hg].
  split; [exact Ha'|]; intro k'; rewrite Hg; reflexivity.
Qed.

Lemma gapf_idem I R k o : gapf I R k (gapf I R k o) = gapf I R k o.
Proof.
  destruct o as [e|]; [reflexivity|].
  change (gapf I R k None) with (if Nat.ltb (dval R k) (dval I k) then agap k (dval I k) else None).
  destruct (Nat.ltb (dval R k) (dval I k)) eqn:E.
  - destruct (agap k (dval I k)) eqn:Ag; [reflexivity|].
    change (gapf I R k None) with (if Nat.ltb (dval R k) (dval I k) then agap k (dval I k) else None).
    rewrite E, Ag; reflexivity.
  - change (gapf I R k None) with (if Nat.ltb (dval R k) (dval I k) then agap k (dval I k) else None).
    rewrite E; reflexivity.
Qed.

(** Rebasing an absolute entry onto counts below its uses. *)
Lemma eapply_eshift R h e i :
  entry_good h e -> cle R (uses e) -> eapply R (eshift R e) i = eabs e i.
Proof.
  destruct e as [h' ts len p]; intros [-> [G [Hl _]]] Hle; cbn [eshift eapply eabs lapp].
  pose proof (cle_cmin_inv_l _ _ _ Hle) as Hp; pose proof (cle_cmin_inv_r _ _ _ Hle) as Hts.
  apply dval_le_cle in Hp.
  assert (HL : length (klist ts) = len) by (rewrite <- Hl; symmetry; apply klength_spec, kgood_shape, G).
  unfold lapp; rewrite HL; destruct (Nat.ltb_spec i len) as [Hi|Hi]; [|f_equal; f_equal; lia].
  rewrite knth_spec by apply kshape_krebase, kgood_shape, G.
  rewrite klist_krebase by (apply kgood_inv, G || exact Hts).
  rewrite nth_error_map; destruct (nth_error (klist ts) i) as [t|] eqn:Et; cbn [option_map].
  - f_equal; change (unshift R (shift R t) = t); apply unshift_shift.
    + apply (kgood_targets_ok ts G), (nth_error_In _ _ Et).
    + apply (cle_mem _ (ksann ts) (klist ts)); [exact Hts|intro k; apply ksann_klist, G|apply (nth_error_In _ _ Et)].
  - apply nth_error_None in Et; lia.
Qed.

Lemma cle_aann R (t : atrie entry) :
  ainv t -> (forall k e, aget k t = Some e -> cle R (uses e)) -> cle R (aann t).
Proof.
  intros Ht H k n m Hn Hm; rewrite (ainv_ann t Ht) in Hm.
  destruct (lmin_attained _ _ _ Hm) as [e [Hin He]].
  destruct (aelems_aget t e Hin) as [k' E]; apply (H k' e E k n m Hn He).
Qed.

Lemma uses_le_aann (t : atrie entry) k e : ainv t -> aget k t = Some e -> cle (aann t) (uses e).
Proof.
  intros Ht E k' n m Hn Hm; rewrite (ainv_ann t Ht) in Hn.
  destruct (lmin_le _ e k' m (aget_in _ _ _ E) Hm) as [n' [En Hle]]; congruence.
Qed.

Lemma cle_cmin_elem (t : atrie entry) J k e :
  ainv t -> aget k t = Some e -> cle (cmin (aann t) J) (uses e).
Proof.
  intros Ht E k' n m Hn Hm; rewrite cget_cmin in Hn.
  rewrite (ainv_ann t Ht) in Hn.
  destruct (lmin_le _ e k' m (aget_in _ _ _ E) Hm) as [u [Eu Hle]]; rewrite Eu in Hn.
  destruct (cget J k'); cbn in Hn; injection Hn as <-; lia.
Qed.

Lemma in_keys_spec {A} (m : tree A) k : existsb (Pos.eqb k) (map fst (elements m)) = true <-> get k m <> None.
Proof.
  rewrite existsb_exists; split.
  - intros [k' [Hin Hk]]; apply Pos.eqb_eq in Hk; subst k'.
    apply in_map_iff in Hin as [[k' v] [Ek Hin]]; cbn in Ek; subst k'.
    apply In_elements in Hin; congruence.
  - intros H; destruct (get k m) as [v|] eqn:E; [|contradiction].
    exists k; split; [apply in_map_iff; exists (k, v); split; [reflexivity|apply In_elements, E]|apply Pos.eqb_refl].
Qed.

Lemma cget_jstarts W k :
  cget (jstarts W) k = match aget k esa with Some _ => None | None => cget (ctotal wa W) k end.
Proof.
  assert (H : forall L, (forall e, In e L -> In e aentries) ->
            cget (fold_right (fun e c => cset c (label_key (elabel e)) None) (ctotal wa W) L) k
            = if existsb (fun e => Pos.eqb (label_key (elabel e)) k) L then None else cget (ctotal wa W) k).
  { induction L as [|e L IH]; intros HL; cbn [fold_right existsb]; [reflexivity|].
    rewrite cget_cset, Pos.eqb_sym; destruct (Pos.eqb _ _); [reflexivity|].
    apply IH; intros; apply HL; right; assumption. }
  unfold jstarts; rewrite H by auto.
  destruct (existsb _ aentries) eqn:X.
  - apply existsb_exists in X as [e [Hin Hk]]; apply Pos.eqb_eq in Hk; subst k.
    rewrite (aentries_get e Hin); reflexivity.
  - destruct (aget k esa) as [e|] eqn:E; [exfalso|reflexivity].
    assert (Hx : existsb (fun e => Pos.eqb (label_key (elabel e)) k) aentries = true)
      by (apply existsb_exists; exists e; split; [apply (aentries_in _ _ E)|rewrite <- (esa_key _ _ E), Pos.eqb_refl; reflexivity]).
    congruence.
Qed.

End Compose.
