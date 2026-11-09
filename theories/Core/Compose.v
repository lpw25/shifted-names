(** * Composition

    [compose a b] is [b] followed by [a]: a variable [b] sends to [y] goes
    where [a] sends [y], and a payload [(u, rho)] becomes
    [(u, a ∘ rho)], where only [rho]'s named labels matter.

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
From ShiftedNames.Core Require Import Trie Label Var Counts Based Skew ATrie Prune Repr Point Deep.
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

(** In a payload ([pay]), the bound label's inputs do not matter: the
    composite gets no entry, identity start or gap for it. *)
Definition skipN (pay : bool) (k : positive) : bool := pay && Pos.eqb k (label_key None).

(** Add [a]'s entries for labels the composite has no entry for. *)
Definition add_aonly (pay : bool) (W : counts) (es : atrie entry) : atrie entry :=
  fold_right (fun e es =>
                let h := elabel e in
                if skipN pay (label_key h) then es else
                match aget (label_key h) es with
                | Some _ => es
                | None => aupdate (label_key h) (fun _ => adrop h (dval W (label_key h))) es
                end) es aentries.

(** Identity starts of the labels with no entry of [a]. *)
Definition jstarts (pay : bool) (W : counts) : counts :=
  let c := fold_right (fun e c => cset c (label_key (elabel e)) None) (ctotal wa W) aentries in
  if pay then cset c (label_key None) None else c.

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

Definition finish (pay : bool) (W : counts) (es : atrie entry) (visited : list positive) : nadj :=
  let es1 := add_aonly pay W es in
  let R := cmin (aann es1) (jstarts pay W) in
  let keys_a := map (fun e => label_key (elabel e)) aentries in
  let I := ctotal wa W in
  let WK := filter (fun k => negb (skipN pay k)) (map fst (elements (c_exc W))) in
  let es2 := fold_left (add_gap_at I R) WK es1 in
  let es3 := fold_left (drop_ident R) (visited ++ keys_a) es2 in
  NAdj R (arebase R es3).

(** ** The traversal *)

Fixpoint ncomp (pay : bool) (b : nadj) (B : counts) {struct b} : nadj :=
  match b with
  | NAdj r es =>
      let tc := fun (B' : counts) (t : target) =>
                  match t with
                  | TVar y j => rtarget (napply a (mk_rvar y (dval B' (label_key y) + j)))
                  | TBind u rho => TBind u (ncomp true rho B')
                  end in
      let ec := fun (B' : counts) (e : entry) =>
                  match e with
                  | Entry h ts len p =>
                      ecomp h (kmap th tau tc bl0 B' ts) len (dval B' (label_key h) + p)
                  end in
      let P := cadd B r in
      finish pay P (atmap th tau ec bl0 P es) (@atvisit entry bl0 P (fun k => k) es)
  end.

Definition compose (b : nadj) : nadj := ncomp false b cnone.

(** One level of the traversal, with the recursion through payloads named. *)
Definition tcF (B : counts) (t : target) : target :=
  match t with
  | TVar y j => rtarget (napply a (mk_rvar y (dval B (label_key y) + j)))
  | TBind u rho => TBind u (ncomp true rho B)
  end.

Definition ecF (B : counts) (e : entry) : entry :=
  match e with
  | Entry h ts len p => ecomp h (kmap th tau tcF bl0 B ts) len (dval B (label_key h) + p)
  end.

Lemma ncomp_eq pay r es B :
  ncomp pay (NAdj r es) B
  = finish pay (cadd B r) (atmap th tau ecF bl0 (cadd B r) es) (@atvisit entry bl0 (cadd B r) (fun k => k) es).
Proof. reflexivity. Qed.

(** ** Base independence *)

Lemma cget_cnone_dval k : dval cnone k = 0.
Proof. reflexivity. Qed.


Lemma kmap_rebase F bl B (ts : kseq target) :
  kmap th tau F bl B ts = kmap th tau F bl cnone (klift B ts).
Proof. destruct ts as [|c w t s]; [reflexivity|]; cbn [klift kmap]; rewrite cadd_cnone by apply cwf_cmap2; reflexivity. Qed.

Lemma ncomp_rebase pay r es B : ncomp pay (NAdj r es) B = ncomp pay (NAdj (cadd B r) es) cnone.
Proof. rewrite !ncomp_eq, (cadd_cnone (cadd B r)) by apply cwf_cmap2; reflexivity. Qed.

Lemma tcF_rebase B t : tcF B t = tcF cnone (unshift B t).
Proof. destruct t as [y j|u [r es]]; [reflexivity|]; cbn [tcF unshift target_based tunshift]; rewrite ncomp_rebase; reflexivity. Qed.

Lemma ecF_rebase B e : ecF B e = ecF cnone (unshift B e).
Proof. destruct e as [h ts len p]; cbn [ecF unshift entry_based eunshift]; rewrite kmap_rebase; reflexivity. Qed.

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

Theorem add_aonly_spec pay W es :
  ainv es ->
  ainv (add_aonly pay W es)
  /\ forall k, aget k (add_aonly pay W es)
               = match aget k es with
                 | Some e => Some e
                 | None => if skipN pay k then None else
                           match aget k esa with
                           | Some ea => adrop (elabel ea) (dval W k)
                           | None => None
                           end
                 end.
Proof.
  intros Hes.
  set (step := fun (e : entry) (es : atrie entry) =>
                 let h := elabel e in
                 if skipN pay (label_key h) then es else
                 match aget (label_key h) es with
                 | Some _ => es
                 | None => aupdate (label_key h) (fun _ => adrop h (dval W (label_key h))) es
                 end).
  assert (H : forall L, (forall e, In e L -> In e aentries) ->
            ainv (fold_right step es L)
            /\ forall k, aget k (fold_right step es L)
                         = match aget k es with
                           | Some e => Some e
                           | None => if existsb (fun e => Pos.eqb (label_key (elabel e)) k) L && negb (skipN pay k)
                                     then match aget k esa with
                                          | Some ea => adrop (elabel ea) (dval W k)
                                          | None => None
                                          end
                                     else None
                           end).
  { induction L as [|e L IH]; intros HL; cbn [fold_right existsb].
    - split; [exact Hes|intro k; destruct (aget k es); reflexivity].
    - destruct (IH (fun e' H' => HL e' (or_intror H'))) as [Hi Hg].
      set (es' := fold_right step es L) in *.
      pose proof (aentries_get e (HL e (or_introl eq_refl))) as Ge.
      change (step e es') with (if skipN pay (label_key (elabel e)) then es' else match aget (label_key (elabel e)) es' with Some _ => es' | None => aupdate (label_key (elabel e)) (fun _ => adrop (elabel e) (dval W (label_key (elabel e)))) es' end).
      destruct (skipN pay (label_key (elabel e))) eqn:Sk.
      + split; [exact Hi|intro k; rewrite Hg].
        destruct (Pos.eqb_spec (label_key (elabel e)) k) as [<-|]; cbn [orb]; [|reflexivity].
        rewrite Sk, !andb_false_r; reflexivity.
      + destruct (aget (label_key (elabel e)) es') as [e0|] eqn:E0.
        * split; [exact Hi|intro k; rewrite Hg].
          destruct (Pos.eqb_spec (label_key (elabel e)) k) as [<-|]; cbn [orb]; [|reflexivity].
          rewrite Sk; cbn [negb andb]; rewrite Hg, Sk, andb_true_r in E0.
          destruct (aget _ es) as [e1|]; [reflexivity|].
          destruct (existsb _ L); cbn [andb orb negb] in *; [reflexivity|discriminate].
        * destruct (aupdate_spec (label_key (elabel e)) (fun _ => adrop (elabel e) (dval W (label_key (elabel e)))) es' Hi
                      (fun _ _ => ook_adrop _ _)) as [Ha' Hg'].
          split; [exact Ha'|intro k; rewrite Hg', Pos.eqb_sym].
          destruct (Pos.eqb_spec (label_key (elabel e)) k) as [<-|]; cbn [orb].
          -- rewrite Hg in E0; rewrite Ge, Sk; cbn [negb andb].
             destruct (aget _ es); [discriminate|reflexivity].
          -- rewrite Hg; reflexivity. }
  destruct (H aentries (fun e H => H)) as [Hi Hg]; split; [exact Hi|intro k].
  unfold add_aonly; fold step; rewrite Hg; destruct (aget k es); [reflexivity|].
  destruct (skipN pay k); [rewrite andb_false_r; reflexivity|rewrite andb_true_r].
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

Lemma cget_jstarts pay W k :
  cget (jstarts pay W) k
  = if skipN pay k then None else match aget k esa with Some _ => None | None => cget (ctotal wa W) k end.
Proof.
  assert (H : forall L, (forall e, In e L -> In e aentries) ->
            cget (fold_right (fun e c => cset c (label_key (elabel e)) None) (ctotal wa W) L) k
            = if existsb (fun e => Pos.eqb (label_key (elabel e)) k) L then None else cget (ctotal wa W) k).
  { induction L as [|e L IH]; intros HL; cbn [fold_right existsb]; [reflexivity|].
    rewrite cget_cset, Pos.eqb_sym; destruct (Pos.eqb _ _); [reflexivity|].
    apply IH; intros; apply HL; right; assumption. }
  unfold jstarts, skipN.
  assert (Hc : forall c, cget (if pay then cset c (label_key None) None else c) k
                         = if pay && Pos.eqb k (label_key None) then None else cget c k)
    by (intro c; destruct pay; [rewrite cget_cset; reflexivity|reflexivity]).
  rewrite Hc, H by auto; destruct (pay && _); [reflexivity|].
  destruct (existsb _ aentries) eqn:X.
  - apply existsb_exists in X as [e [Hin Hk]]; apply Pos.eqb_eq in Hk; subst k.
    rewrite (aentries_get e Hin); reflexivity.
  - destruct (aget k esa) as [e|] eqn:E; [exfalso|reflexivity].
    assert (Hx : existsb (fun e => Pos.eqb (label_key (elabel e)) k) aentries = true)
      by (apply existsb_exists; exists e; split; [apply (aentries_in _ _ E)|rewrite <- (esa_key _ _ E), Pos.eqb_refl; reflexivity]).
    congruence.
Qed.

(** ** Keyed count maps *)


(** A count map that is the minimum over elements with keyed uses is keyed. *)
Lemma keyed_lmin {X} {BX : Based X} (L : list X) c :
  (forall e, In e L -> keyed (uses e)) -> (forall k, cget c k = lmin L k) -> cwf c -> keyed c.
Proof.
  intros HL Hc Hw k v E.
  assert (Hlab : ~ (exists l, k = label_key l) -> False).
  { intro Hn.
    assert (Hnot : forall e, In e L -> get k (c_exc (uses e)) = None)
      by (intros e He; destruct (get k (c_exc (uses e))) as [v'|] eqn:G; [exfalso; apply Hn, (HL e He k v' G)|reflexivity]).
    destruct (fresh_label_list (c_exc c :: map (fun e => c_exc (uses e)) L)) as [s0 Hl'].
    remember (Some s0) as l' eqn:El'.
    assert (Hc' : get (label_key l') (c_exc c) = None) by (apply Hl'; left; reflexivity).
    assert (Hl2 : forall e, In e L -> get (label_key l') (c_exc (uses e)) = None)
      by (intros e He; apply Hl'; right; apply (in_map (fun e => c_exc (uses e)) L e He)).
    assert (Hsame : lmin L k = lmin L (label_key l')).
    { clear -Hnot Hl2; induction L as [|e L IH]; [reflexivity|].
      unfold lmin; cbn [fold_right]; fold (lmin L k); fold (lmin L (label_key l')).
      rewrite IH by (intros; first [apply Hnot | apply Hl2]; right; assumption).
      f_equal; unfold cget; rewrite Hnot, Hl2 by (left; reflexivity); reflexivity. }
    rewrite <- !Hc in Hsame; unfold cget in Hsame; rewrite E, Hc' in Hsame.
    exact (Hw k v E Hsame). }
  destruct (key_label k) as [l|] eqn:Kl; [destruct (Pos.eqb_spec (label_key l) k) as [<-|Hne]; [eauto|]|];
    exfalso; apply Hlab; intros [l' ->]; rewrite key_label_spec in Kl; [injection Kl as ->; congruence|discriminate].
Qed.

(** ** [finish] *)

(** Where the composite sends [h_i], given the composite entries [es] of
    the labels [b] has an entry for (absolute) and [b]'s root [W]. *)
Definition cf (W : counts) (es : atrie entry) (h : option label) (i : nat) : result :=
  match aget (label_key h) es with
  | Some e => eabs e i
  | None => napply a (mk_rvar h (dval W (label_key h) + i))
  end.

Definition es_good (es : atrie entry) : Prop :=
  ainv es /\ forall k e, aget k es = Some e -> k = label_key (elabel e) /\ entry_good (elabel e) e.

(** Labels with no entry anywhere that [W] does not weaken are used no
    lower than their identity start. *)
Definition no_low (pay : bool) (W : counts) (es : atrie entry) : Prop :=
  forall k n, skipN pay k = false -> get k (c_exc W) = None -> aget k (add_aonly pay W es) = None ->
              cget (aann (add_aonly pay W es)) k = Some n -> dval (ctotal wa W) k <= n.

Lemma aget_add_aonly_good pay W es k e :
  es_good es -> aget k (add_aonly pay W es) = Some e ->
  k = label_key (elabel e) /\ entry_good (elabel e) e
  /\ forall i, eabs e i = cf W es (elabel e) i.
Proof.
  intros [Hes Hg] E; rewrite (proj2 (add_aonly_spec pay W es Hes)) in E.
  destruct (aget k es) as [e0|] eqn:E0.
  - injection E as <-; destruct (Hg _ _ E0) as [Hk Hgood]; split; [exact Hk|split; [exact Hgood|]].
    intro i; unfold cf; rewrite <- Hk, E0; reflexivity.
  - destruct (skipN pay k); [discriminate|].
    destruct (aget k esa) as [ea|] eqn:Ea; [|discriminate].
    pose proof (esa_key _ _ Ea) as Hk.
    destruct (adrop_spec _ _ _ E) as [Hgood Hm].
    assert (He : elabel e = elabel ea) by (destruct e; destruct Hgood as [-> _]; reflexivity).
    split; [rewrite He; exact Hk|split; [rewrite He; exact Hgood|]].
    intro i; unfold cf; rewrite He, <- Hk, E0, Hm, Hk; reflexivity.
Qed.


Section Finish.

Variables (pay : bool) (W : counts) (es : atrie entry) (vis : list positive).
Hypothesis Hgood : es_good es.

Definition es1 : atrie entry := add_aonly pay W es.
Definition R : counts := cmin (aann es1) (jstarts pay W).
Definition I : counts := ctotal wa W.
Definition WK : list positive := filter (fun k => negb (skipN pay k)) (map fst (elements (c_exc W))).
Definition D : list positive := vis ++ map (fun e => label_key (elabel e)) aentries.
Definition es2 : atrie entry := fold_left (add_gap_at I R) WK es1.
Definition es3 : atrie entry := fold_left (drop_ident R) D es2.

Lemma finish_eq : finish pay W es vis = NAdj R (arebase R es3).
Proof. reflexivity. Qed.

Lemma Hes : ainv es.
Proof. apply Hgood. Qed.

Lemma Hes1 : ainv es1.
Proof. apply (add_aonly_spec pay W es Hes). Qed.

Lemma Hg1 k : aget k es1 = match aget k es with
                            | Some e => Some e
                            | None => if skipN pay k then None else
                                      match aget k esa with
                                      | Some ea => adrop (elabel ea) (dval W k)
                                      | None => None
                                      end
                            end.
Proof. apply (add_aonly_spec pay W es Hes). Qed.

Lemma Hes2 : ainv es2.
Proof. apply (fold_keyed (add_gap_at I R) (gapf I R) (add_gap_step I R) (gapf_idem I R) WK es1 Hes1). Qed.

Lemma Hg2 k : aget k es2 = if existsb (Pos.eqb k) WK then gapf I R k (aget k es1) else aget k es1.
Proof. apply (fold_keyed (add_gap_at I R) (gapf I R) (add_gap_step I R) (gapf_idem I R) WK es1 Hes1). Qed.

Lemma Hes3 : ainv es3.
Proof. apply (fold_keyed (drop_ident R) (dropf R) (drop_ident_step R) (dropf_idem R) D es2 Hes2). Qed.

Lemma Hg3 k : aget k es3 = if existsb (Pos.eqb k) D then dropf R k (aget k es2) else aget k es2.
Proof. apply (fold_keyed (drop_ident R) (dropf R) (drop_ident_step R) (dropf_idem R) D es2 Hes2). Qed.

Lemma Hsrc k e : aget k es3 = Some e ->
                 aget k es1 = Some e
                 \/ (aget k es1 = None /\ dval R k < dval I k /\ agap k (dval I k) = Some e).
Proof.
  intros E; rewrite Hg3, Hg2 in E.
  destruct (aget k es1) as [e1|] eqn:E1.
  - left; destruct (existsb _ D), (existsb _ WK); cbn [gapf] in E; try (exact E).
    + unfold dropf in E; destruct e1 as [h1 [|c w t s] [|len] p]; try exact E.
      destruct (oeqb _ _); [discriminate|exact E].
    + unfold dropf in E; destruct e1 as [h1 [|c w t s] [|len] p]; try exact E.
      destruct (oeqb _ _); [discriminate|exact E].
  - right; split; [reflexivity|].
    destruct (existsb _ WK); cbn [gapf] in E; [|destruct (existsb _ D); discriminate].
    destruct (Nat.ltb_spec (dval R k) (dval I k)); [|destruct (existsb _ D); discriminate].
    split; [assumption|].
    destruct (existsb _ D); [|exact E].
    unfold dropf in E; destruct (agap k (dval I k)) as [[h1 [|c w t s] [|len] p]|] eqn:Ag; try exact E.
    destruct (oeqb _ _); [discriminate|exact E].
Qed.

Lemma Hgap k e : agap k (dval I k) = Some e -> e = Entry (elabel e) KNil 0 (dval I k) /\ k = label_key (elabel e).
Proof.
  intros Ag; unfold agap in Ag; destruct (key_label k) as [l|]; [|discriminate].
  destruct (Pos.eqb_spec (label_key l) k) as [Hl|]; [|discriminate]; injection Ag as <-.
  split; [reflexivity|symmetry; exact Hl].
Qed.

(** Every entry left is above the new root. *)
Lemma Hcle k e : aget k es3 = Some e -> cle R (uses e).
Proof.
  intros E; destruct (Hsrc k e E) as [E1|[_ [Hlt Ag]]]; [apply (cle_cmin_elem es1 _ k e Hes1 E1)|].
  destruct (Hgap k e Ag) as [He Hk]; rewrite He; rewrite He in Hk; cbn [elabel] in Hk.
  intros k' n m Hn Hm; cbn [uses entry_based euses ksann] in Hm.
  rewrite cget_cmin, cget_cnone, cget_cone in Hm; destruct (Pos.eqb_spec k' (label_key (elabel e))) as [->|];
    [|destruct (Some 0); discriminate].
  cbn in Hm; injection Hm as <-; rewrite <- Hk in Hn; unfold dval in Hlt |- *; rewrite Hn in Hlt; cbn in Hlt; lia.
Qed.

Lemma HR : cle R (aann es3).
Proof. apply cle_aann; [exact Hes3|exact Hcle]. Qed.

Theorem napply_finish h i :
  skipN pay (label_key h) = false -> no_low pay W es ->
  napply (finish pay W es vis) (mk_rvar h i) = cf W es h i.
Proof.
  intros Hh Hlow; rewrite finish_eq.
  pose proof Hes1 as Hes1; pose proof HR as HR; pose proof Hcle as Hcle; pose proof Hsrc as Hsrc;
    pose proof Hgap as Hgap; pose proof Hg1 as Hg1; pose proof Hg2 as Hg2; pose proof Hg3 as Hg3.
  set (kh := label_key h).
  (* labels with no entry anywhere *)
  assert (Hnone : aget kh es1 = None ->
                  aget kh es = None /\ aget kh esa = None /\ cf W es h i = inl (mk_rvar h (dval I kh + i))).
  { intros E1; rewrite Hg1 in E1; destruct (aget kh es) as [e0|] eqn:E0; [discriminate|].
    unfold kh in E1; rewrite Hh in E1; fold kh in E1.
    destruct (aget kh esa) as [ea|] eqn:Ea.
    - exfalso; unfold adrop in E1; rewrite <- (esa_key _ _ Ea), Ea in E1; destruct ea as [h1 tsa lena pa].
      destruct (Nat.ltb _ _); discriminate.
    - split; [reflexivity|split; [reflexivity|]].
      unfold cf; fold kh; rewrite E0, napply_a_lapp.
      unfold alist, lapp; fold kh; rewrite Ea; cbn [length Nat.ltb].
      destruct (Nat.ltb_spec (dval W kh + i) 0); [lia|].
      unfold tauv, I, dval; fold kh; rewrite cget_tau, Ea, cget_ctotal; cbn [oval].
      f_equal; f_equal; lia. }
  cbn [napply v_label v_index]; rewrite aget_arebase by (exact Hes3 || exact HR); fold kh.
  destruct (aget kh es3) as [e|] eqn:E3; cbn [option_map].
  - destruct (Hsrc kh e E3) as [E1|[E1 [Hlt Ag]]].
    + destruct (aget_add_aonly_good pay W es kh e Hgood E1) as [Hk [Hge Hm]].
      apply label_key_inj in Hk; rewrite <- Hk in Hge, Hm.
      change (shift R e) with (eshift R e); rewrite (eapply_eshift R h e i Hge (Hcle _ _ E3)), Hm; reflexivity.
    + destruct (Hgap kh e Ag) as [He Hk]; apply label_key_inj in Hk.
      destruct (Hnone E1) as [_ [_ ->]].
      assert (Hge : entry_good h e)
        by (rewrite He, <- Hk; split; [reflexivity|split; [apply kgood_nil|split; [reflexivity|cbn; lia]]]).
      change (shift R e) with (eshift R e); rewrite (eapply_eshift R h e i Hge (Hcle _ _ E3)), He; cbn [eabs lapp klist length Nat.ltb].
      unfold lapp; cbn [length]; destruct (Nat.ltb_spec i 0); [lia|]; f_equal; f_equal; [congruence|lia].
  - rewrite Hg3, Hg2 in E3.
    destruct (aget kh es1) as [e1|] eqn:E1.
    + (* dropped: it was the identity relative to the new root *)
      assert (Hd : exists h1 p, e1 = Entry h1 KNil 0 p /\ cget R kh = Some p).
      { destruct (existsb _ D), (existsb _ WK); cbn [gapf] in E3; try discriminate;
          unfold dropf in E3; destruct e1 as [h1 [|c w t s] [|len] p]; try discriminate;
          destruct (oeqb (cget R kh) (Some p)) eqn:Eq; try discriminate;
          apply oeqb_spec in Eq; eauto. }
      destruct Hd as [h1 [p [-> Hp]]].
      destruct (aget_add_aonly_good pay W es kh _ Hgood E1) as [Hk [_ Hm]]; cbn [elabel] in Hk, Hm.
      apply label_key_inj in Hk; subst h1; rewrite <- Hm; cbn [eabs lapp klist length Nat.ltb].
      destruct (Nat.ltb_spec i 0); [lia|]; unfold dval; rewrite Hp; cbn; f_equal; f_equal; lia.
    + destruct (Hnone eq_refl) as [_ [Ea ->]].
      assert (HJ : cget (jstarts pay W) kh = Some (dval I kh))
        by (rewrite cget_jstarts; unfold kh; rewrite Hh; fold kh; rewrite Ea; unfold I, dval; rewrite cget_ctotal; reflexivity).
      assert (HRI : dval R kh <= dval I kh)
        by (unfold R, dval at 1; rewrite cget_cmin, HJ; destruct (cget (aann es1) kh); cbn; lia).
      assert (HIR : dval I kh <= dval R kh).
      { destruct (existsb (Pos.eqb kh) WK) eqn:Hw.
        - cbn [gapf] in E3; destruct (Nat.ltb_spec (dval R kh) (dval I kh)) as [Hlt|]; [|assumption].
          exfalso; unfold agap, kh in E3; rewrite key_label_spec, Pos.eqb_refl in E3.
          unfold kh in *; destruct (existsb _ D); [|discriminate].
          unfold dropf in E3; destruct (oeqb _ _) eqn:Eq; [|discriminate].
          apply oeqb_spec in Eq; unfold dval in Hlt; rewrite Eq in Hlt; cbn [oval] in Hlt; unfold dval in Hlt; lia.
        - assert (Hw0 : get kh (c_exc W) = None).
          { destruct (get kh (c_exc W)) eqn:G; [exfalso|reflexivity].
            apply Bool.not_true_iff_false in Hw; apply Hw, existsb_exists; exists kh.
            split; [|apply Pos.eqb_refl]; apply filter_In; split; [|unfold kh; rewrite Hh; reflexivity].
            apply in_map_iff; exists (kh, o); split; [reflexivity|apply In_elements, G]. }
          unfold R, dval at 2; rewrite cget_cmin, HJ.
          destruct (cget (aann es1) kh) as [n|] eqn:Eu; cbn; [|lia].
          specialize (Hlow kh n Hh Hw0 E1 Eu); fold I in Hlow; lia. }
      f_equal; f_equal; lia.
Qed.

(** *** The normal form of [finish] *)

Lemma keyed_cset c k v : keyed c -> (exists l, k = label_key l) -> keyed (cset c k v).
Proof.
  intros Hc Hk k' v' E; unfold cset in E; cbn [c_exc] in E.
  destruct (oeqb v (c_def c)); [rewrite get_remove in E|rewrite get_set in E];
    destruct (Pos.eqb_spec k' k) as [->|]; try discriminate; try exact Hk; apply (Hc _ _ E).
Qed.

Lemma keyed_tunshift d (t : target) : keyed d -> keyed (tuses t) -> keyed (tuses (tunshift d t)).
Proof. destruct t as [y j|u [r es']]; cbn; intros Hd Ht; [apply keyed_cone|apply keyed_cmap2; assumption]. Qed.

Lemma keyed_ksann (ts : kseq target) : kgood ts -> (forall t, In t (klist ts) -> keyed (tuses t)) -> keyed (ksann ts).
Proof.
  intros G H; apply (keyed_lmin (klist ts)); [exact H|intro k; apply ksann_klist, G|apply kgood_cwf, G].
Qed.

Lemma keyed_entry h (ts : kseq target) len p :
  kgood ts -> (forall t, In t (klist ts) -> keyed (tuses t)) -> keyed (uses (Entry h ts len p)).
Proof. intros G H; apply keyed_cmap2; [apply keyed_cone|apply keyed_ksann; assumption]. Qed.

Lemma ainv_cwf_ann (t : atrie entry) : ainv t -> cwf (aann t).
Proof. destruct t; [intros _; apply cwf_cnone|intros [_ [H _]]; exact H]. Qed.

Hypothesis Hkey : forall k e, aget k es = Some e -> keyed (uses e).
Hypothesis HkW : keyed W.
Hypothesis HkA : forall k e, aget k esa = Some e -> forall t, In t (klist (etargets e)) -> keyed (tuses (tunshift wa t)).

Lemma keyed_wa : keyed wa.
Proof. unfold wa; destruct a as [w es']; destruct Ha as [_ [_ [Hk _]]]; exact Hk. Qed.

Lemma keyed_adrop h n e : adrop h n = Some e -> keyed (uses e).
Proof.
  intros E; pose proof (adrop_spec h n e E) as [Hg _].
  unfold adrop in E; destruct (aget (label_key h) esa) as [[h' tsa lena pa]|] eqn:Ea; [|discriminate].
  destruct (Nat.ltb n lena); injection E as <-; destruct Hg as [_ [G _]]; apply keyed_entry; try exact G.
  - intros t Ht; set (L := map (tunshift wa) (skipn n (klist tsa))) in *.
    assert (HokL : forall t, In t L -> eok t).
    { intros t' Ht'; apply (alist_ok h); unfold alist; rewrite Ea; unfold L in Ht'; rewrite <- skipn_map in Ht'.
      rewrite <- (firstn_skipn n (map (tunshift wa) (klist tsa))); apply in_or_app; right; exact Ht'. }
    rewrite (proj1 (proj2 (kof_list_good L HokL))) in Ht.
    apply in_map_iff in Ht as [t0 [<- Ht0]].
    apply (HkA _ _ Ea); cbn [etargets].
    rewrite <- (firstn_skipn n (klist tsa)); apply in_or_app; right; exact Ht0.
  - intros t [].
Qed.

Lemma keyed_es1 k e : aget k es1 = Some e -> keyed (uses e).
Proof.
  intros E; rewrite Hg1 in E; destruct (aget k es) as [e0|] eqn:E0; [injection E as <-; apply (Hkey _ _ E0)|].
  destruct (skipN pay k); [discriminate|].
  destruct (aget k esa) as [ea|]; [apply (keyed_adrop _ _ _ E)|discriminate].
Qed.

Lemma keyed_aann (t : atrie entry) : ainv t -> (forall k e, aget k t = Some e -> keyed (uses e)) -> keyed (aann t).
Proof.
  intros Ht H; apply (keyed_lmin (aelems t)); [|apply ainv_ann, Ht|apply ainv_cwf_ann, Ht].
  intros e He; destruct (aelems_aget t e He) as [k E]; apply (H _ _ E).
Qed.

Lemma keyed_jstarts : keyed (jstarts pay W).
Proof.
  unfold jstarts.
  assert (H : forall L, keyed (fold_right (fun (e : entry) c => cset c (label_key (elabel e)) None) (ctotal wa W) L))
    by (induction L as [|e L IH]; cbn [fold_right];
        [apply keyed_cmap2; [apply keyed_wa|exact HkW]|apply keyed_cset; [exact IH|eauto]]).
  destruct pay; [apply keyed_cset; [apply H|eauto]|apply H].
Qed.

Lemma keyed_R : keyed R.
Proof. apply keyed_cmap2; [apply keyed_aann; [exact Hes1|exact keyed_es1]|exact keyed_jstarts]. Qed.

Hypothesis Hfa : nfin a.
Hypothesis HW0 : c_def W = Some 0.

Lemma nfin_finish : nfin (finish pay W es vis).
Proof.
  rewrite finish_eq; unfold nfin, R; cbn [nroot].
  unfold cmin, cmap2; cbn [c_def].
  assert (HJ : c_def (jstarts pay W) = Some 0).
  { unfold jstarts.
    assert (Hd : forall L, c_def (fold_right (fun (e : entry) c => cset c (label_key (elabel e)) None) (ctotal wa W) L)
                           = Some (oval (c_def wa) + oval (c_def W)))
      by (induction L as [|e L IH]; [reflexivity|exact IH]).
    unfold nfin in Hfa; fold wa in Hfa.
    destruct pay; [unfold cset; cbn [c_def]|]; rewrite Hd, Hfa, HW0; reflexivity. }
  rewrite HJ; destruct (c_def (aann es1)); cbn; [f_equal; lia|reflexivity].
Qed.

Lemma klength0_nil (ts : kseq target) : kgood ts -> klength ts = 0 -> ts = KNil.
Proof.
  intros [_ [Hsh _]]; destruct ts as [|c w t s]; [reflexivity|]; cbn [klength]; intros H.
  destruct Hsh as [Ht _]; apply ktshape_pos in Ht; lia.
Qed.

Lemma es1_good k e : aget k es1 = Some e -> k = label_key (elabel e) /\ entry_good (elabel e) e.
Proof. intros E; destruct (aget_add_aonly_good pay W es k e Hgood E) as [Hk [Hg _]]; split; assumption. Qed.

(** A minimum of [es1] is still attained in [es3], unless it was attained
    only by an entry for that very label which was removed. *)
Lemma witness k u :
  cget (aann es1) k = Some u -> (aget k es3 <> None \/ aget k es1 = None) ->
  exists k' e', aget k' es3 = Some e' /\ cget (uses e') k = Some u.
Proof.
  intros Hu Hk; rewrite (ainv_ann es1 Hes1) in Hu.
  destruct (lmin_attained _ _ _ Hu) as [e [Hin He]].
  destruct (aelems_aget es1 e Hin) as [k' E1].
  destruct (aget k' es3) as [e3|] eqn:E3.
  - exists k', e3; split; [exact E3|].
    destruct (Hsrc k' e3 E3) as [E1'|[E1' _]]; [rewrite E1 in E1'; injection E1' as ->; exact He|congruence].
  - exfalso; rewrite Hg3, Hg2, E1 in E3.
    assert (Hd : exists h p, e = Entry h KNil 0 p).
    { destruct (existsb _ D), (existsb _ WK); cbn [gapf] in E3; try discriminate;
        unfold dropf in E3; destruct e as [h [|c w t s] [|len] p]; try discriminate; eauto. }
    destruct Hd as [h [p ->]].
    destruct (es1_good _ _ E1) as [Hk' _]; cbn [elabel] in Hk'.
    cbn [uses entry_based euses ksann] in He; rewrite cget_cmin, cget_cnone, cget_cone in He.
    destruct (Pos.eqb_spec k (label_key h)) as [->|]; [|destruct (Some 0); discriminate].
    rewrite <- Hk' in Hk; destruct Hk as [Hk|Hk]; [|congruence].
    apply Hk; rewrite Hg3, Hg2, E1.
    destruct (existsb _ D), (existsb _ WK); cbn [gapf] in E3 |- *; congruence.
Qed.

Hypothesis Hpay : pay = true -> aget (label_key None) es = None.
Hypothesis Hatt : forall k, skipN pay k = false -> aget k es <> None -> aget k esa = None ->
                    exists n, cget (aann es1) k = Some n /\ n <= dval I k.
Hypothesis Hvis : forall k h p, aget k es = Some (Entry h KNil 0 p) -> ~ In k vis -> aget k esa = None ->
                    dval I k < p.

Lemma uses_own k e : aget k es1 = Some e -> cget (uses e) k <> None.
Proof.
  intros E; destruct (es1_good _ _ E) as [Hk _]; destruct e as [h ts len p]; cbn [elabel] in Hk; subst k.
  cbn [uses entry_based euses]; rewrite cget_cmin, cget_cone_same; destruct (cget (ksann ts) _); discriminate.
Qed.

Lemma U_some k e : aget k es1 = Some e -> exists u, cget (aann es1) k = Some u.
Proof.
  intros E; destruct (cget (uses e) k) as [m|] eqn:Em; [|exfalso; exact (uses_own k e E Em)].
  rewrite (ainv_ann es1 Hes1); destruct (lmin_le _ e k m (aget_in _ _ _ E) Em) as [u [Eu _]]; eauto.
Qed.

Lemma J_cases k : cget (jstarts pay W) k = None \/ (cget (jstarts pay W) k = Some (dval I k)
                                                   /\ skipN pay k = false /\ aget k esa = None).
Proof.
  rewrite cget_jstarts; destruct (skipN pay k) eqn:Sk; [left; reflexivity|].
  destruct (aget k esa); [left; reflexivity|right].
  split; [unfold I, dval; rewrite cget_ctotal; reflexivity|split; reflexivity].
Qed.

(** At a label with an entry, the new root is the minimum over [es1]. *)
Lemma R_eq_U k : aget k es3 <> None -> exists u, cget (aann es1) k = Some u /\ cget R k = Some u.
Proof.
  intros H3; destruct (aget k es3) as [e3|] eqn:E3; [|contradiction].
  unfold R; rewrite cget_cmin.
  destruct (Hsrc k e3 E3) as [E1|[E1 [Hlt _]]].
  - destruct (U_some k e3 E1) as [u Eu]; exists u; split; [exact Eu|rewrite Eu].
    destruct (J_cases k) as [->|[-> [Sk Ea]]]; [reflexivity|].
    assert (Hes_k : aget k es <> None).
    { rewrite Hg1 in E1; destruct (aget k es); [discriminate|]; rewrite Sk, Ea in E1; discriminate. }
    destruct (Hatt k Sk Hes_k Ea) as [n [En Hn]]; rewrite Eu in En; injection En as <-.
    cbn; f_equal; lia.
  - assert (Sk : skipN pay k = false).
    { destruct (skipN pay k) eqn:Sk; [exfalso|reflexivity].
      assert (Hw : existsb (Pos.eqb k) WK = false).
      { apply Bool.not_true_iff_false; intros Hx; apply existsb_exists in Hx as [k' [Hin Hk']].
        apply Pos.eqb_eq in Hk'; subst k'; apply filter_In in Hin as [_ Hn]; rewrite Sk in Hn; discriminate. }
      rewrite Hg3, Hg2, Hw, E1 in E3; destruct (existsb _ D); cbn in E3; discriminate. }
    assert (Ea : aget k esa = None).
    { rewrite Hg1 in E1; destruct (aget k es); [discriminate|]; rewrite Sk in E1.
      destruct (aget k esa) as [ea|] eqn:Ea; [exfalso|reflexivity].
      unfold adrop in E1; rewrite <- (esa_key _ _ Ea), Ea in E1; destruct ea as [h1 tsa lena pa].
      destruct (Nat.ltb _ _); discriminate. }
    assert (HJ : cget (jstarts pay W) k = Some (dval I k))
      by (rewrite cget_jstarts, Sk, Ea; unfold I, dval; rewrite cget_ctotal; reflexivity).
    unfold R in Hlt; unfold dval at 1 in Hlt; rewrite cget_cmin, HJ in Hlt; rewrite HJ.
    destruct (cget (aann es1) k) as [u|] eqn:Eu; cbn in Hlt |- *; [|lia].
    exists u; split; [reflexivity|f_equal; lia].
Qed.

Lemma es3_good k e : aget k es3 = Some e -> k = label_key (elabel e) /\ entry_good (elabel e) e.
Proof.
  intros E; destruct (Hsrc k e E) as [E1|[_ [_ Ag]]]; [apply es1_good, E1|].
  destruct (Hgap k e Ag) as [He Hk]; split; [exact Hk|]; rewrite He; cbn [elabel entry_good].
  split; [reflexivity|split; [apply kgood_nil|split; [reflexivity|intros [Hc _]; lia]]].
Qed.

Lemma WK_skip k : existsb (Pos.eqb k) WK = true -> skipN pay k = false.
Proof.
  intros Hx; apply existsb_exists in Hx as [k' [Hin Hk']]; apply Pos.eqb_eq in Hk'; subst k'.
  apply filter_In in Hin as [_ Hn]; destruct (skipN pay k); [discriminate|reflexivity].
Qed.

Lemma es1_not_skipped k e : aget k es1 = Some e -> skipN pay k = false.
Proof.
  intros E; rewrite Hg1 in E; destruct (skipN pay k) eqn:Sk; [|reflexivity].
  exfalso; unfold skipN in Sk; apply andb_prop in Sk as [Hp Hk]; apply Pos.eqb_eq in Hk; subst k.
  rewrite (Hpay Hp) in E; discriminate.
Qed.

Lemma es3_not_skipped k e : aget k es3 = Some e -> skipN pay k = false.
Proof.
  intros E; destruct (Hsrc k e E) as [E1|[E1 _]]; [apply (es1_not_skipped _ _ E1)|].
  rewrite Hg3, Hg2, E1 in E.
  destruct (existsb (Pos.eqb k) WK) eqn:Hw; [apply WK_skip, Hw|].
  destruct (existsb _ D); cbn in E; discriminate.
Qed.

Lemma a_key_in_D k ea : aget k esa = Some ea -> existsb (Pos.eqb k) D = true.
Proof.
  intros Ea; apply existsb_exists; exists k; split; [|apply Pos.eqb_refl].
  apply in_or_app; right; apply in_map_iff; exists ea; split; [symmetry; apply (esa_key _ _ Ea)|apply (aentries_in _ _ Ea)].
Qed.

Lemma R_le_I k : skipN pay k = false -> aget k esa = None -> dval R k <= dval I k.
Proof.
  intros Sk Ea; unfold R, dval at 1; rewrite cget_cmin, cget_jstarts, Sk, Ea.
  unfold I, dval; rewrite cget_ctotal; destruct (cget (aann es1) k); cbn; lia.
Qed.

(** Every entry left moves something: after rebasing, it is not the identity. *)
Lemma es3_nontrivial k e : aget k es3 = Some e -> 0 < elen e \/ dval R k < epass e.
Proof.
  intros E; destruct (es3_good k e E) as [Hk Hge].
  destruct (R_eq_U k ltac:(rewrite E; discriminate)) as [u [Eu ER]].
  destruct (Hsrc k e E) as [E1|[_ [Hlt Ag]]].
  - destruct e as [h ts [|len] p]; [right|left; cbn; lia]; cbn [elen epass elabel] in *.
    destruct Hge as [_ [G [Hl _]]]; pose proof (klength0_nil ts G Hl) as ->.
    assert (Hle : u <= p).
    { pose proof (Hcle k _ E) as Hc; cbn [uses entry_based euses ksann] in Hc.
      apply (Hc k u p ER); rewrite cget_cmin, cget_cnone, Hk, cget_cone_same; reflexivity. }
    rewrite Hg3, Hg2, E1 in E.
    destruct (existsb (Pos.eqb k) D) eqn:HD.
    + destruct (existsb _ WK); cbn [gapf dropf] in E;
        destruct (oeqb (cget R k) (Some p)) eqn:Eq; try discriminate;
        (assert (u <> p) by (intros ->; rewrite ER, oeqb_refl in Eq; discriminate));
        unfold dval; rewrite ER; cbn; lia.
    + assert (Ea : aget k esa = None)
        by (destruct (aget k esa) as [ea|] eqn:Ea; [rewrite (a_key_in_D _ _ Ea) in HD; discriminate|reflexivity]).
      assert (Ees : aget k es = Some (Entry h KNil 0 p)).
      { rewrite Hg1 in E1; destruct (aget k es); [exact E1|]; destruct (skipN pay k); [discriminate|].
        rewrite Ea in E1; discriminate. }
      assert (Hnv : ~ In k vis).
      { intros Hin; assert (existsb (Pos.eqb k) D = true)
          by (apply existsb_exists; exists k; split; [apply in_or_app; left; exact Hin|apply Pos.eqb_refl]).
        congruence. }
      pose proof (Hvis _ _ _ Ees Hnv Ea) as Hv.
      pose proof (R_le_I k (es1_not_skipped _ _ E1) Ea); lia.
  - destruct (Hgap k e Ag) as [He _]; rewrite He; cbn [epass]; right; exact Hlt.
Qed.

Lemma strip_shift R0 h (ts : kseq target) len p :
  kgood ts -> cle R0 (uses (Entry h ts len p)) -> strip_ok (Entry h ts len p) ->
  strip_ok (eshift R0 (Entry h ts len p)).
Proof.
  intros G Hc Hs; cbn [eshift strip_ok]; intros [Hlen [Hp Hn]]; apply Hs.
  pose proof (cle_cmin_inv_l _ _ _ Hc) as Hpp; apply dval_le_cle in Hpp.
  pose proof (cle_cmin_inv_r _ _ _ Hc) as Hts.
  rewrite knth_spec in Hn by apply kshape_krebase, kgood_shape, G.
  rewrite klist_krebase in Hn by (apply kgood_inv, G || exact Hts).
  rewrite nth_error_map in Hn; rewrite knth_spec by apply kgood_shape, G.
  destruct (nth_error (klist ts) (pred len)) as [t|] eqn:Et; [|discriminate]; cbn in Hn.
  assert (Hct : cle R0 (uses t))
    by (apply (cle_mem _ (ksann ts) (klist ts)); [exact Hts|intro k; apply ksann_klist, G|apply (nth_error_In _ _ Et)]).
  destruct t as [y j|u [r es']]; cbn in Hn; [|discriminate].
  injection Hn as -> Hj.
  assert (dval R0 (label_key h) <= j)
    by (apply (dval_le_cle R0 (label_key h) j); exact Hct).
  split; [exact Hlen|split; [lia|f_equal; f_equal; lia]].
Qed.

Lemma lmin_none {X} {BX : Based X} (L : list X) k :
  (forall e, In e L -> cget (uses e) k = None) -> lmin L k = None.
Proof.
  induction L as [|e L IH]; intros H; [reflexivity|].
  unfold lmin; cbn [fold_right]; fold (lmin L k); rewrite H by (left; reflexivity).
  rewrite IH by (intros; apply H; right; assumption); reflexivity.
Qed.

Lemma ann_es4 k u :
  (aget k es3 <> None \/ aget k es1 = None) -> cget (aann es1) k = Some u -> cget R k = Some u ->
  cget (aann (arebase R es3)) k = Some 0.
Proof.
  intros Hk Eu ER; destruct (witness k u Eu Hk) as [k' [e' [E' He']]].
  assert (Hl : cget (aann es3) k = Some u).
  { pose proof (HR k u) as H'; rewrite (ainv_ann es3 Hes3) in H' |- *.
    destruct (lmin_le _ e' k u (aget_in _ _ _ E') He') as [n [En Hn]]; rewrite En.
    specialize (H' n ER En); f_equal; lia. }
  destruct es3 as [|c l o r] eqn:Ees3; [cbn in E'; discriminate|].
  cbn [arebase aann] in Hl |- *; rewrite cget_csub, Hl, ER; cbn; f_equal; lia.
Qed.

Theorem nlocal_finish : nlocal (Qof pay) (finish pay W es vis).
Proof.
  rewrite finish_eq; cbn [nlocal].
  assert (Hes4 : ainv (arebase R es3)) by (apply ainv_arebase; [exact Hes3|exact HR]).
  assert (Hget4 : forall k, aget k (arebase R es3) = option_map (shift R) (aget k es3))
    by (intro k; apply aget_arebase; [exact Hes3|exact HR]).
  split; [exact Hes4|split; [apply cwf_cmap2|split; [exact keyed_R|split; [|split]]]].
  - intros k e E; rewrite Hget4 in E.
    destruct (aget k es3) as [e3|] eqn:E3; [|discriminate]; injection E as <-.
    destruct (es3_good k e3 E3) as [Hk Hge].
    pose proof (es3_nontrivial k e3 E3) as Hnt; pose proof (Hcle k e3 E3) as Hc.
    split; [|split].
    + destruct e3 as [h ts len p]; cbn [elabel elen epass] in *; destruct Hge as [_ [G [Hl Hs]]].
      cbn [shift entry_based eshift entry_ok].
      split; [symmetry; exact Hk|].
      split; [apply kgood_krebase; [exact G|exact (cle_cmin_inv_r _ _ _ Hc)]|].
      split; [rewrite <- Hl; destruct ts; reflexivity|].
      split; [subst k; destruct Hnt as [Hn|Hn]; [left; exact Hn|right; lia]|].
      apply (strip_shift R h ts len p G Hc Hs).
    + unfold Qof; destruct (Bool.bool_dec pay true) as [Hp|Hp];
        [rewrite Hp|apply Bool.not_true_iff_false in Hp; rewrite Hp; reflexivity].
      pose proof (es3_not_skipped k e3 E3) as Sk; unfold skipN in Sk; rewrite Hk, Hp in Sk.
      change (Qnamed (elabel (eshift R e3)) = true); replace (elabel (eshift R e3)) with (elabel e3) by (destruct e3; reflexivity).
      destruct (elabel e3) as [s|]; [reflexivity|]; cbn [andb] in Sk; rewrite Pos.eqb_refl in Sk; discriminate.
    + destruct (R_eq_U k ltac:(rewrite E3; discriminate)) as [u [Eu ER]].
      apply (ann_es4 k u); [left; rewrite E3; discriminate|exact Eu|exact ER].
  - intros l Hl; unfold R; rewrite cget_cmin.
    destruct (J_cases (label_key l)) as [HJ|[HJ _]]; [|rewrite HJ; destruct (cget (aann es1) _); discriminate].
    rewrite cget_jstarts in HJ; destruct (skipN pay (label_key l)) eqn:Sk.
    + exfalso; unfold skipN in Sk; apply andb_prop in Sk as [Hp Hk]; apply Pos.eqb_eq, label_key_inj in Hk; subst l.
      unfold Qof in Hl; rewrite Hp in Hl; discriminate.
    + destruct (aget (label_key l) esa) as [ea|] eqn:Ea; [|unfold I in HJ; rewrite cget_ctotal in HJ; discriminate].
      assert (E1 : exists e1, aget (label_key l) es1 = Some e1).
      { rewrite Hg1; destruct (aget (label_key l) es) as [e0|]; [eauto|]; rewrite Sk, Ea.
        unfold adrop; rewrite <- (esa_key _ _ Ea), Ea; destruct ea as [h1 tsa lena pa].
        destruct (Nat.ltb _ _); eauto. }
      destruct E1 as [e1 E1]; destruct (U_some _ _ E1) as [u ->]; destruct (cget (jstarts pay W) _); discriminate.
  - intros l Hl; unfold Qof in Hl; destruct (Bool.bool_dec pay true) as [Hp|Hp];
      [rewrite Hp in Hl|apply Bool.not_true_iff_false in Hp; rewrite Hp in Hl; discriminate].
    destruct l as [s|]; [discriminate|].
    set (kN := label_key None).
    assert (Sk : skipN pay kN = true) by (unfold skipN; rewrite Hp, Pos.eqb_refl; reflexivity).
    assert (HJ : cget (jstarts pay W) kN = None) by (rewrite cget_jstarts, Sk; reflexivity).
    assert (E1 : aget kN es1 = None)
      by (destruct (aget kN es1) as [e1|] eqn:E1; [rewrite (es1_not_skipped _ _ E1) in Sk; discriminate|reflexivity]).
    assert (ER : cget R kN = cget (aann es1) kN) by (unfold R; rewrite cget_cmin, HJ; destruct (cget (aann es1) kN); reflexivity).
    destruct (cget (aann es1) kN) as [u|] eqn:Eu.
    + right; split; [rewrite ER; discriminate|].
      apply (ann_es4 kN u); [right; exact E1|exact Eu|rewrite ER; reflexivity].
    + left; split; [rewrite ER; reflexivity|].
      assert (H3 : cget (aann es3) kN = None).
      { rewrite (ainv_ann es3 Hes3); apply lmin_none; intros e He.
        destruct (aelems_aget es3 e He) as [k E3].
        destruct (Hsrc k e E3) as [E1'|[_ [_ Ag]]].
        - destruct (cget (uses e) kN) as [m|] eqn:Em; [|reflexivity]; exfalso.
          rewrite (ainv_ann es1 Hes1) in Eu.
          destruct (lmin_le _ e kN m (aget_in _ _ _ E1') Em) as [n [En _]]; congruence.
        - destruct (Hgap k e Ag) as [He' Hk]; rewrite He'; cbn [uses entry_based euses ksann].
          rewrite cget_cmin, cget_cnone, cget_cone.
          destruct (Pos.eqb_spec kN (label_key (elabel e))) as [Ek|]; [|destruct (Some 0); reflexivity].
          exfalso; rewrite <- Ek in Hk; subst k; rewrite (es3_not_skipped _ _ E3) in Sk; discriminate. }
      destruct es3 as [|c l o r] eqn:Ees3; [reflexivity|].
      cbn [arebase aann] in H3 |- *; rewrite cget_csub, H3; reflexivity.
Qed.

End Finish.

(** ** One level of the traversal *)

(** What composition does to a result of [b]. *)
Definition rcomp (r : result) : result :=
  match r with inl y => napply a y | inr (u, rho) => inr (u, ncomp true rho cnone) end.

Lemma tresult_rtarget r : tresult (rtarget r) = r.
Proof. destruct r as [[l i]|[u rho]]; reflexivity. Qed.

Lemma rcomp_tresult t : rcomp (tresult t) = tresult (tcF cnone t).
Proof. destruct t as [y j|u rho]; cbn [rcomp tresult tcF]; [rewrite tresult_rtarget; reflexivity|reflexivity]. Qed.

(** Above the thresholds a variable is just moved. *)
Lemma tcF_var_shift y j :
  clears th (TVar y j : target) -> tcF cnone (TVar y j) = unshift tau (shift th (TVar y j)).
Proof.
  intros Hc; cbn [tcF]; rewrite cget_cnone_dval; cbn [Nat.add].
  assert (Hj : thv y <= j).
  { unfold thv, dval; destruct (cget th (label_key y)) as [t|] eqn:Et; cbn [oval]; [|lia].
    apply (Hc (label_key y) t j Et); cbn; apply cget_cone_same. }
  rewrite napply_a_shift by exact Hj; cbn [rtarget v_label v_index unshift shift target_based tunshift tshift].
  unfold thv, tauv; f_equal; lia.
Qed.

Lemma unshift_cnone (t : target) : eok t -> unshift cnone t = t.
Proof.
  destruct t as [y j|u [r es]]; [reflexivity|]; cbn; intros Hr.
  rewrite cadd_cnone by exact Hr; reflexivity.
Qed.

Lemma napply_a_ok v u rho : napply a v = inr (u, rho) -> cwf (nroot rho).
Proof.
  assert (Hn : napply a v = match aget (label_key (v_label v)) esa with
                            | None => inl (mk_rvar (v_label v) (dval wa (label_key (v_label v)) + v_index v))
                            | Some e => eapply wa e (v_index v)
                            end) by (unfold esa, wa; destruct a; reflexivity).
  rewrite Hn; destruct (aget _ esa) as [e|] eqn:E; [|discriminate].
  destruct e as [h ts len p]; destruct (esa_ok _ _ E) as [_ [G _]]; cbn [eapply].
  destruct (Nat.ltb _ _); [|discriminate].
  destruct (knth ts _) as [t|] eqn:Et; [|discriminate].
  pose proof (kgood_targets_ok ts G t (knth_in _ _ _ G Et)) as Ht.
  pose proof (ok_unshift wa t Ht) as Ht'.
  destruct (tunshift wa t) as [y j|u' rho'] eqn:Eu; cbn; [discriminate|]; intros [= -> <-].
  change (eok (unshift wa t)) in Ht'; cbn [unshift target_based] in Ht'; rewrite Eu in Ht'; exact Ht'.
Qed.

Lemma tcF_ok B (t : target) : eok (tcF B t).
Proof.
  destruct t as [y j|u rho]; cbn [tcF].
  - destruct (napply a _) as [v|[u rho]] eqn:E; [exact Logic.I|apply (napply_a_ok _ _ _ E)].
  - destruct rho as [r es]; rewrite ncomp_eq; unfold finish; apply cwf_cmap2.
Qed.

Lemma estrip_noop h (ts : kseq target) len p :
  (forall t, knth ts (pred len) = Some t -> 0 < len -> 0 < p -> tvar_at h (pred p) t = false) ->
  estrip h ts len p = Entry h ts len p.
Proof.
  intros H; unfold estrip; destruct len as [|len'], p as [|p']; try reflexivity.
  destruct (knth ts len') as [t|] eqn:Et; [|reflexivity].
  pose proof (H t Et ltac:(lia) ltac:(lia)) as Hf; cbn [pred] in Hf; rewrite Hf; reflexivity.
Qed.

(** An entry above the thresholds is just moved. *)
Lemma ecF_moved h (ts : kseq target) len p :
  kgood ts -> klength ts = len -> strip_ok (Entry h ts len p) ->
  cle th (uses (Entry h ts len p)) ->
  (forall t, In t (klist ts) -> tcF cnone t = unshift tau (shift th t)) ->
  ecF cnone (Entry h ts len p) = unshift tau (shift th (Entry h ts len p)).
Proof.
  intros G Hl Hs Hc Ht.
  pose proof (cle_cmin_inv_l _ _ _ Hc) as Hp; apply dval_le_cle in Hp.
  pose proof (cle_cmin_inv_r _ _ _ Hc) as Hts.
  pose proof (kgood_targets_ok ts G) as Hok.
  (* the targets, mapped, are the moved sequence *)
  assert (Hk : kmap th tau tcF bl0 cnone ts = klift tau (krebase th ts)).
  { destruct (kgood_kmap th tau tcF (tcF cnone) (fun z => In z (klist ts))
                (fun B x _ _ => tcF_rebase B x)
                (fun z Hz Hin _ => Ht z Hin)
                (fun z _ _ => tcF_ok cnone z)
                bl0 cnone ts G) as [G1 E1].
    - intros z Hz k t0 m Ht0 Hm Hlt; exfalso.
      apply in_map_iff in Hz as [y [<- Hy]]; rewrite unshift_cnone in Hm by apply Hok, Hy.
      pose proof (cle_mem _ (ksann ts) (klist ts) y Hts (fun k => ksann_klist ts k G) Hy k t0 m Ht0 Hm); lia.
    - intros y Hy; rewrite unshift_cnone by apply Hok, Hy; exact Hy.
    - apply kcanonical; [exact G1|apply kgood_klift, kgood_krebase; assumption|].
      rewrite E1, klist_klift, klist_krebase
        by first [exact Hts | apply kgood_inv, kgood_krebase; assumption | apply kgood_inv; assumption].
      rewrite map_map; apply map_ext_in; intros y Hy; rewrite unshift_cnone by apply Hok, Hy.
      rewrite tcF_rebase, unshift_cnone by apply Hok, Hy; apply Ht, Hy. }
  cbn [ecF]; rewrite Hk, cget_cnone_dval; cbn [Nat.add].
  unfold ecomp; destruct (Nat.leb_spec (thv h) p) as [Hle|Hlt]; [|unfold thv in Hlt; lia].
  rewrite estrip_noop.
  - cbn [unshift shift entry_based eunshift eshift]; unfold thv, tauv; f_equal; lia.
  - intros t Et Hlen Hpp.
    rewrite knth_spec in Et by apply kshape_klift, kshape_krebase, kgood_shape, G.
    rewrite klist_klift, klist_krebase, nth_error_map, nth_error_map in Et
      by first [exact Hts | apply kgood_inv, kgood_krebase; assumption | apply kgood_inv; assumption].
    destruct (nth_error (klist ts) (pred len)) as [t0|] eqn:E0; [|discriminate]; injection Et as <-.
    apply Bool.not_true_iff_false; intros Tv; apply tvar_at_spec in Tv.
    destruct t0 as [y j|u rho]; [|destruct rho; discriminate]; cbn in Tv; injection Tv as -> Hj.
    assert (Hjt : dval th (label_key h) <= j)
      by (apply (dval_le_cle th (label_key h) j);
          exact (cle_mem th (ksann ts) (klist ts) (TVar h j) Hts (fun k => ksann_klist ts k G) (nth_error_In _ _ E0))).
    apply Hs; split; [lia|split; [unfold thv, tauv in *; lia|]].
    rewrite knth_spec by apply kgood_shape, G; rewrite E0; f_equal; f_equal; unfold thv, tauv in *; lia.
Qed.

(** ** Stripping only lowers uses *)

Lemma rstrip_le h R0 p : forall R p2, rstrip h R0 p = (R, p2) ->
  p2 <= p /\ forall x, In x R0 -> In x R \/ exists j, x = TVar h j /\ p2 <= j.
Proof.
  revert p; induction R0 as [|t R0 IH]; intros p R p2 E; cbn [rstrip] in E.
  - destruct p; injection E as <- <-; (split; [lia|intros x []]).
  - destruct p as [|p'].
    + injection E as <- <-; split; [lia|intros x Hx; left; exact Hx].
    + destruct (tvar_at h p' t) eqn:Tv.
      * apply tvar_at_spec in Tv; subst t; destruct (IH p' R p2 E) as [Hp Hin].
        split; [lia|intros x [<-|Hx]; [right; exists p'; split; [reflexivity|exact Hp]|apply Hin, Hx]].
      * injection E as <- <-; split; [lia|intros x Hx; left; exact Hx].
Qed.

Lemma uses_entry_klist h (ts : kseq target) len p k :
  kgood ts -> cget (uses (Entry h ts len p)) k = omin (cget (cone (label_key h) p) k) (lmin (klist ts) k).
Proof. intros G; cbn [uses entry_based euses]; rewrite cget_cmin, ksann_klist by exact G; reflexivity. Qed.

Lemma omin_some_or o1 o2 m : omin o1 o2 = Some m -> o1 = Some m \/ o2 = Some m.
Proof.
  destruct o1 as [x|], o2 as [y|]; cbn; intros H; auto.
  injection H as <-; destruct (Nat.min_spec x y) as [[_ ->]|[_ ->]]; auto.
Qed.

Lemma estrip_uses_le h (ts : kseq target) p k m :
  kgood ts -> cget (uses (Entry h ts (klength ts) p)) k = Some m ->
  exists m', cget (uses (estrip h ts (klength ts) p)) k = Some m' /\ m' <= m.
Proof.
  intros G Hm; unfold estrip.
  assert (Hsame : exists m', cget (uses (Entry h ts (klength ts) p)) k = Some m' /\ m' <= m)
    by (exists m; split; [exact Hm|lia]).
  destruct (klength ts) as [|len'] eqn:El, p as [|p']; try exact Hsame.
  destruct (knth ts len') as [t|] eqn:Et; [|exact Hsame].
  destruct (tvar_at h p' t); [|exact Hsame].
  destruct (rstrip h (rev (klist ts)) (S p')) as [R p2] eqn:Er.
  destruct (rstrip_le h _ _ R p2 Er) as [Hp Hin].
  assert (HokR : forall t, In t (rev R) -> eok t).
  { intros t' Ht'; apply in_rev in Ht'.
    assert (Hsuf : forall R0 q R1 q1, rstrip h R0 q = (R1, q1) -> forall x, In x R1 -> In x R0).
    { induction R0 as [|x0 R0 IH0]; intros q R1 q1 E x Hx; cbn [rstrip] in E.
      - destruct q; injection E as <- <-; exact Hx.
      - destruct q as [|q']; [injection E as <- <-; exact Hx|].
        destruct (tvar_at h q' x0); [right; apply (IH0 _ _ _ E _ Hx)|injection E as <- <-; exact Hx]. }
    apply (Hsuf _ _ _ _ Er), in_rev in Ht'; apply (kgood_targets_ok ts G), Ht'. }
  destruct (kof_list_good (rev R) HokR) as [G' [E' _]].
  rewrite uses_entry_klist by exact G'; rewrite E'.
  rewrite uses_entry_klist in Hm by exact G.
  rewrite cget_cone in Hm |- *.
  destruct (omin_some_or _ _ _ Hm) as [Hc|Hl].
  - destruct (Pos.eqb k (label_key h)); [|discriminate]; injection Hc as <-.
    exists (match lmin (rev R) k with Some n => Nat.min p2 n | None => p2 end).
    split; [destruct (lmin (rev R) k); reflexivity|destruct (lmin (rev R) k); lia].
  - destruct (lmin_attained _ _ _ Hl) as [x [Hx Ex]].
    destruct (Hin x (proj1 (in_rev _ _) Hx)) as [HxR|[j [-> Hj]]].
    + destruct (lmin_le (rev R) x k _ (proj1 (in_rev _ _) HxR) Ex) as [n [En Hn]]; rewrite En.
      destruct (Pos.eqb k (label_key h)); cbn; eexists; split; [reflexivity|lia|reflexivity|lia].
    + cbn in Ex; rewrite cget_cone in Ex; destruct (Pos.eqb_spec k (label_key h)) as [->|]; [|discriminate].
      injection Ex as <-.
      exists (match lmin (rev R) (label_key h) with Some n => Nat.min p2 n | None => p2 end).
      split; [destruct (lmin (rev R) _); reflexivity|destruct (lmin (rev R) _); lia].
Qed.

(** ** Deep well-formedness *)


(** [b] above the thresholds, moved by [a]'s pure shift. *)
Definition nmove (b : nadj) : nadj :=
  match b with NAdj r es => NAdj (cadd tau (csub r th)) es end.

(** A target of an entry of [b], made absolute, is a result of [b]. *)

(** ** Lower bounds on uses *)

Lemma rstrip_p2 h R0 p R p2 : rstrip h R0 p = (R, p2) -> p2 = p \/ In (TVar h p2) R0.
Proof.
  revert p; induction R0 as [|t R0 IH]; intros p E; cbn [rstrip] in E.
  - destruct p; injection E as <- <-; left; reflexivity.
  - destruct p as [|p']; [injection E as <- <-; left; reflexivity|].
    destruct (tvar_at h p' t) eqn:Tv; [|injection E as <- <-; left; reflexivity].
    apply tvar_at_spec in Tv; subst t.
    destruct (IH p' E) as [->|Hin]; right; [left; reflexivity|right; exact Hin].
Qed.

Lemma cle_entry_iff c h (ts : kseq target) len p :
  kgood ts ->
  cle c (uses (Entry h ts len p))
  <-> cle c (cone (label_key h) p) /\ forall t, In t (klist ts) -> cle c (uses t).
Proof.
  intros G; split.
  - intros H; split; [apply (cle_cmin_inv_l _ _ _ H)|].
    intros t Ht; apply (cle_mem c (ksann ts) (klist ts) t (cle_cmin_inv_r _ _ _ H) (fun k => ksann_klist ts k G) Ht).
  - intros [Hp Ht] k n m Hn Hm; rewrite uses_entry_klist in Hm by exact G.
    destruct (omin_some_or _ _ _ Hm) as [Hc|Hl]; [apply (Hp k n m Hn Hc)|].
    destruct (lmin_attained _ _ _ Hl) as [t [Hin Et]]; apply (Ht t Hin k n m Hn Et).
Qed.

Lemma estrip_ge c h (ts : kseq target) p :
  kgood ts -> cle c (uses (Entry h ts (klength ts) p)) -> cle c (uses (estrip h ts (klength ts) p)).
Proof.
  intros G Hc; unfold estrip.
  destruct (klength ts) as [|len'] eqn:El, p as [|p']; try exact Hc.
  destruct (knth ts len') as [t|] eqn:Et; [|exact Hc].
  destruct (tvar_at h p' t); [|exact Hc].
  destruct (rstrip h (rev (klist ts)) (S p')) as [R p2] eqn:Er.
  destruct (rstrip_le h _ _ R p2 Er) as [_ Hin].
  apply (cle_entry_iff c h ts _ _ G) in Hc as [Hp Ht].
  assert (HR : forall x, In x (rev R) -> In x (klist ts)).
  { intros x Hx; apply in_rev in Hx; apply in_rev.
    assert (Hsuf : forall R0 q R1 q1, rstrip h R0 q = (R1, q1) -> forall x, In x R1 -> In x R0).
    { induction R0 as [|x0 R0 IH0]; intros q R1 q1 E x' Hx'; cbn [rstrip] in E.
      - destruct q; injection E as <- <-; exact Hx'.
      - destruct q as [|q']; [injection E as <- <-; exact Hx'|].
        destruct (tvar_at h q' x0); [right; apply (IH0 _ _ _ E _ Hx')|injection E as <- <-; exact Hx']. }
    apply (Hsuf _ _ _ _ Er _ Hx). }
  assert (HokR : forall t, In t (rev R) -> eok t) by (intros t' Ht'; apply (kgood_targets_ok ts G), HR, Ht').
  destruct (kof_list_good (rev R) HokR) as [G' [E' _]].
  apply (cle_entry_iff c h _ _ _ G'); rewrite E'; split.
  - destruct (rstrip_p2 h _ _ R p2 Er) as [->|HT]; [exact Hp|].
    apply in_rev in HT; exact (Ht _ HT).
  - intros x Hx; apply Ht, HR, Hx.
Qed.

Lemma cle_cadd_self c u : (forall k, cget c k <> None) -> cle c (cadd c u).
Proof.
  intros Hc k n m Hn Hm; rewrite cget_cadd, Hn in Hm.
  destruct (cget u k); cbn in Hm; [injection Hm as <-; lia|discriminate].
Qed.

Lemma wa_total k : cget wa k <> None.
Proof. unfold wa; destruct a as [w es'] eqn:E; apply (nlocal_total w es' Ha). Qed.

Lemma tauv_ge h : dval wa (label_key h) <= tauv h.
Proof.
  unfold tauv, dval; rewrite cget_tau; destruct (aget (label_key h) esa) as [[h1 ts1 l1 p1]|]; cbn [oval]; [unfold dval; lia|lia].
Qed.

Lemma cle_wa_cone h p : dval wa (label_key h) <= p -> cle wa (cone (label_key h) p).
Proof.
  intros Hp k n m Hn Hm; rewrite cget_cone in Hm; destruct (Pos.eqb_spec k (label_key h)) as [->|]; [|discriminate].
  injection Hm as <-; unfold dval in Hp; rewrite Hn in Hp; exact Hp.
Qed.

Lemma tuses_rtarget (rs : result) : tuses (rtarget rs) = ruses rs.
Proof. destruct rs as [[l i]|[u rho]]; reflexivity. Qed.

Lemma cle_napply_a v : cle wa (uses (rtarget (napply a v))).
Proof.
  change (cle wa (tuses (rtarget (napply a v)))); rewrite tuses_rtarget.
  unfold wa; destruct a as [w es'] eqn:E; apply (cle_result Qall w es' v Ha).
Qed.

Lemma alist_ge h t : In t (alist h) -> cle wa (uses t).
Proof.
  unfold alist; destruct (aget (label_key h) esa) as [[h' tsa len p]|]; [|intros []].
  intros Hin; apply in_map_iff in Hin as [t0 [<- _]].
  change (cle wa (uses (unshift wa t0))); intros k n m Hn Hm; rewrite uses_unshift, Hn in Hm.
  destruct (cget (uses t0) k); cbn in Hm; [injection Hm as <-; lia|discriminate].
Qed.

Lemma ecomp_ge h ts1 s :
  kgood ts1 -> (forall t, In t (klist ts1) -> cle wa (uses t)) ->
  cle wa (uses (ecomp h ts1 (klength ts1) s)).
Proof.
  intros G Ht; assert (HL : klength ts1 = length (klist ts1)) by apply klength_spec, kgood_shape, G.
  pose proof (tauv_ge h) as Htv.
  unfold ecomp; destruct (Nat.leb_spec (thv h) s).
  - apply estrip_ge; [exact G|]; apply (cle_entry_iff wa h ts1 _ _ G); split; [apply cle_wa_cone; lia|exact Ht].
  - set (ex := aextra h s).
    assert (Hex : ex = skipn s (alist h)) by apply aextra_alist.
    assert (Hok : forall t, In t (klist ts1 ++ ex) -> eok t).
    { intros t Ht'; apply in_app_or in Ht' as [Ht'|Ht']; [apply (kgood_targets_ok _ G _ Ht')|].
      rewrite Hex in Ht'; apply (alist_ok h).
      rewrite <- (firstn_skipn s (alist h)); apply in_or_app; right; exact Ht'. }
    destruct (kof_list_good (klist ts1 ++ ex) Hok) as [G2 [E2 L2]].
    assert (Hlen : klength ts1 + length ex = klength (kof_list (klist ts1 ++ ex)))
      by (rewrite L2, length_app, HL; reflexivity).
    rewrite Hlen; apply estrip_ge; [exact G2|].
    apply (cle_entry_iff wa h _ _ _ G2); rewrite E2; split; [apply cle_wa_cone; exact Htv|].
    intros t Ht'; apply in_app_or in Ht' as [Ht'|Ht']; [apply Ht, Ht'|].
    rewrite Hex in Ht'; apply (alist_ge h).
    rewrite <- (firstn_skipn s (alist h)); apply in_or_app; right; exact Ht'.
Qed.

Lemma adrop_ge h n e : adrop h n = Some e -> cle wa (uses e).
Proof.
  intros E; pose proof (adrop_spec h n e E) as [Hg _].
  unfold adrop in E; destruct (aget (label_key h) esa) as [[h' tsa lena pa]|] eqn:Ea; [|discriminate].
  destruct (esa_ok _ _ Ea) as [Hk _]; apply label_key_inj in Hk; subst h'.
  assert (Hal : alist h = map (tunshift wa) (klist tsa)) by (unfold alist; rewrite Ea; reflexivity).
  assert (Hp : dval wa (label_key h) <= dval wa (label_key h) + pa) by lia.
  destruct (Nat.ltb n lena); injection E as <-; destruct Hg as [_ [G _]];
    apply (cle_entry_iff wa h _ _ _ G); split; try (apply cle_wa_cone; lia).
  - set (L := map (tunshift wa) (skipn n (klist tsa))) in *.
    assert (HokL : forall t, In t L -> eok t).
    { intros t' Ht'; apply (alist_ok h); rewrite Hal; unfold L in Ht'; rewrite <- skipn_map in Ht'.
      rewrite <- (firstn_skipn n (map (tunshift wa) (klist tsa))); apply in_or_app; right; exact Ht'. }
    rewrite (proj1 (proj2 (kof_list_good L HokL))); intros t Ht; apply (alist_ge h).
    rewrite Hal; unfold L in Ht; rewrite <- skipn_map in Ht.
    rewrite <- (firstn_skipn n (map (tunshift wa) (klist tsa))); apply in_or_app; right; exact Ht.
  - intros t [].
Qed.

Lemma rstrip_sub h R0 q R1 q1 : rstrip h R0 q = (R1, q1) -> forall x, In x R1 -> In x R0.
Proof.
  revert q; induction R0 as [|x0 R0 IH0]; intros q E x Hx; cbn [rstrip] in E.
  - destruct q; injection E as <- <-; exact Hx.
  - destruct q as [|q']; [injection E as <- <-; exact Hx|].
    destruct (tvar_at h q' x0); [right; apply (IH0 _ E _ Hx)|injection E as <- <-; exact Hx].
Qed.

(** Stripping keeps a subset of the targets. *)
Lemma estrip_targets h (ts : kseq target) p t :
  kgood ts -> In t (klist (etargets (estrip h ts (klength ts) p))) -> In t (klist ts).
Proof.
  intros G; unfold estrip.
  destruct (klength ts) as [|len'] eqn:El, p as [|p']; try (cbn; exact (fun H => H)).
  destruct (knth ts len') as [t0|] eqn:Et; [|cbn; exact (fun H => H)].
  destruct (tvar_at h p' t0); [|cbn; exact (fun H => H)].
  destruct (rstrip h (rev (klist ts)) (S p')) as [R p2] eqn:Er; cbn [etargets].
  assert (HokR : forall t, In t (rev R) -> eok t).
  { intros t' Ht'; apply in_rev in Ht'; apply (rstrip_sub _ _ _ _ _ Er), in_rev in Ht'.
    apply (kgood_targets_ok ts G), Ht'. }
  rewrite (proj1 (proj2 (kof_list_good (rev R) HokR))); intros Ht.
  apply in_rev in Ht; apply (rstrip_sub _ _ _ _ _ Er), in_rev in Ht; exact Ht.
Qed.

(** The targets of a composite entry: mapped ones, or [a]'s. *)
Lemma ecomp_targets h ts1 s t :
  kgood ts1 -> In t (klist (etargets (ecomp h ts1 (klength ts1) s))) -> In t (klist ts1) \/ In t (alist h).
Proof.
  intros G; assert (HL : klength ts1 = length (klist ts1)) by apply klength_spec, kgood_shape, G.
  unfold ecomp; destruct (Nat.leb (thv h) s).
  - intros Ht; left; apply (estrip_targets h ts1 _ t G Ht).
  - set (ex := aextra h s).
    assert (Hex : ex = skipn s (alist h)) by apply aextra_alist.
    assert (Hok : forall t, In t (klist ts1 ++ ex) -> eok t).
    { intros t' Ht'; apply in_app_or in Ht' as [Ht'|Ht']; [apply (kgood_targets_ok _ G _ Ht')|].
      rewrite Hex in Ht'; apply (alist_ok h).
      rewrite <- (firstn_skipn s (alist h)); apply in_or_app; right; exact Ht'. }
    destruct (kof_list_good (klist ts1 ++ ex) Hok) as [G2 [E2 L2]].
    assert (Hlen : klength ts1 + length ex = klength (kof_list (klist ts1 ++ ex)))
      by (rewrite L2, length_app, HL; reflexivity).
    rewrite Hlen; intros Ht; apply (estrip_targets h _ _ t G2) in Ht; rewrite E2 in Ht.
    apply in_app_or in Ht as [Ht|Ht]; [left; exact Ht|right].
    rewrite Hex in Ht; rewrite <- (firstn_skipn s (alist h)); apply in_or_app; right; exact Ht.
Qed.

(** ** Upper bounds on composite uses *)

Lemma ecomp_pre h ts1 s :
  kgood ts1 ->
  exists ts' p', kgood ts' /\ ecomp h ts1 (klength ts1) s = estrip h ts' (klength ts') p'
                 /\ (forall t, In t (klist ts1) -> In t (klist ts'))
                 /\ (thv h <= s -> p' = s - thv h + tauv h).
Proof.
  intros G; assert (HL : klength ts1 = length (klist ts1)) by apply klength_spec, kgood_shape, G.
  unfold ecomp; destruct (Nat.leb_spec (thv h) s) as [Hs|Hs].
  - exists ts1, (s - thv h + tauv h); split; [exact G|split; [reflexivity|split; [auto|auto]]].
  - set (ex := aextra h s).
    assert (Hex : ex = skipn s (alist h)) by apply aextra_alist.
    assert (Hok : forall t, In t (klist ts1 ++ ex) -> eok t).
    { intros t' Ht'; apply in_app_or in Ht' as [Ht'|Ht']; [apply (kgood_targets_ok _ G _ Ht')|].
      rewrite Hex in Ht'; apply (alist_ok h).
      rewrite <- (firstn_skipn s (alist h)); apply in_or_app; right; exact Ht'. }
    destruct (kof_list_good (klist ts1 ++ ex) Hok) as [G2 [E2 L2]].
    assert (Hlen : klength ts1 + length ex = klength (kof_list (klist ts1 ++ ex)))
      by (rewrite L2, length_app, HL; reflexivity).
    exists (kof_list (klist ts1 ++ ex)), (tauv h); split; [exact G2|split; [rewrite Hlen; reflexivity|split]].
    + intros t Ht; rewrite E2; apply in_or_app; left; exact Ht.
    + intros H; lia.
Qed.

Lemma ecomp_uses_target h ts1 s t k m :
  kgood ts1 -> In t (klist ts1) -> cget (uses t) k = Some m ->
  exists m', cget (uses (ecomp h ts1 (klength ts1) s)) k = Some m' /\ m' <= m.
Proof.
  intros G Ht Hm; destruct (ecomp_pre h ts1 s G) as [ts' [p' [G' [-> [Hsub _]]]]].
  assert (Hpre : exists m0, cget (uses (Entry h ts' (klength ts') p')) k = Some m0 /\ m0 <= m).
  { rewrite uses_entry_klist by exact G'.
    destruct (lmin_le _ t k m (Hsub t Ht) Hm) as [n [En Hn]]; rewrite En.
    destruct (cget (cone _ p') k); cbn; eexists; split; [reflexivity|lia|reflexivity|lia]. }
  destruct Hpre as [m0 [Em0 Hm0]]; destruct (estrip_uses_le h ts' p' k m0 G' Em0) as [m' [Em' Hm']].
  exists m'; split; [exact Em'|lia].
Qed.

Lemma ecomp_uses_pass h ts1 s :
  kgood ts1 -> thv h <= s ->
  exists m', cget (uses (ecomp h ts1 (klength ts1) s)) (label_key h) = Some m' /\ m' <= s - thv h + tauv h.
Proof.
  intros G Hs; destruct (ecomp_pre h ts1 s G) as [ts' [p' [G' [-> [_ Hp]]]]]; specialize (Hp Hs).
  assert (Hpre : exists m0, cget (uses (Entry h ts' (klength ts') p')) (label_key h) = Some m0 /\ m0 <= p').
  { rewrite uses_entry_klist, cget_cone_same by exact G'.
    destruct (lmin (klist ts') _); cbn; eexists; split; [reflexivity|lia|reflexivity|lia]. }
  destruct Hpre as [m0 [Em0 Hm0]]; destruct (estrip_uses_le h ts' p' _ m0 G' Em0) as [m' [Em' Hm']].
  exists m'; split; [exact Em'|lia].
Qed.

Lemma keyed_th : keyed th.
Proof.
  intros k v E; unfold th in E; cbn [c_exc] in E; rewrite get_map_filter, th_tree_spec in E.
  destruct (aget k esa) as [e|] eqn:Ea; [|discriminate].
  exists (elabel e); apply (esa_key _ _ Ea).
Qed.

Lemma keyed_tau : keyed tau.
Proof.
  unfold tau.
  assert (H : forall L, (forall e, In e L -> In e aentries) ->
            keyed (fold_right (fun (e : entry) c => match e with
                                          | Entry h _ _ p => cset c (label_key h) (Some (dval wa (label_key h) + p))
                                          end) wa L)).
  { induction L as [|e L IH]; intros HL; cbn [fold_right].
    - unfold wa; destruct a as [w es'] eqn:Ea; destruct Ha as [_ [_ [Hk _]]]; exact Hk.
    - destruct e as [h ts len p]; apply keyed_cset; [apply IH; intros; apply HL; right; assumption|eauto]. }
  apply H; auto.
Qed.

(** Where the root is unused, nothing below uses it. *)
Lemma root_covers Q w (es' : atrie entry) k :
  nlocal Q (NAdj w es') -> nfin (NAdj w es') -> cget w k = None ->
  forall k' e, aget k' es' = Some e -> cget (uses e) k = None.
Proof.
  intros Hl Hf Hw k' e E; pose proof Hl as [Hes [_ [Hkey [_ [HQ HnQ]]]]].
  destruct (cget (uses e) k) as [m|] eqn:Em; [exfalso|reflexivity].
  destruct (key_label k) as [l|] eqn:Kl.
  - destruct (Pos.eqb_spec (label_key l) k) as [<-|Hne].
    + destruct (Q l) eqn:Ql; [exact (HQ l Ql Hw)|].
      destruct (HnQ l Ql) as [[_ Ha']|[Hn _]]; [|contradiction].
      rewrite (ainv_ann es' Hes) in Ha'.
      destruct (lmin_le _ e _ m (aget_in _ _ _ E) Em) as [n [En _]]; congruence.
    + unfold cget in Hw; destruct (get k (c_exc w)) as [v|] eqn:G.
      * destruct (Hkey k v G) as [l' ->]; rewrite key_label_spec in Kl; injection Kl as ->; congruence.
      * unfold nfin in Hf; cbn [nroot] in Hf; congruence.
  - unfold cget in Hw; destruct (get k (c_exc w)) as [v|] eqn:G.
    + destruct (Hkey k v G) as [l' ->]; rewrite key_label_spec in Kl; discriminate.
    + unfold nfin in Hf; cbn [nroot] in Hf; congruence.
Qed.

(** ** The induction step *)

Section Step.

Variables (pay : bool) (r : counts) (es : atrie entry).
Local Notation b := (NAdj r es).
Hypothesis Hb : nwf pay b.

(** What is known of payload targets one level down. *)
Definition Pd_t (t : target) : Prop :=
  eok t /\ match t with TVar _ _ => True | TBind _ rho => nwf true rho /\ nnest rho < nnest b end.

Definition Pd_e (z : entry) : Prop :=
  match z with
  | Entry h ts len p => kgood ts /\ klength ts = len /\ strip_ok z /\ forall t, In t (klist ts) -> Pd_t t
  end.

Hypothesis IH3 : forall rho, nnest rho < nnest b -> nwf true rho -> cle th (nroot rho) ->
                 ncomp true rho cnone = nmove rho.

Lemma Hloc : nlocal (Qof pay) b.
Proof. apply nwf_local with (1 := Hb). Qed.

Lemma b_entries_good : forall k e, aget k (nentries b) = Some e -> kgood (etargets e).
Proof.
  intros k e E; pose proof Hloc as [_ [_ [_ [Hent _]]]].
  destruct (Hent k e E) as [Hok _]; destruct e as [h ts len p]; apply Hok.
Qed.

(** Every entry of [b], made absolute, satisfies [Pd_e]. *)
Lemma Pd_entries k e0 : aget k es = Some e0 -> Pd_e (unshift r e0).
Proof.
  intros E; pose proof Hloc as Hl; pose proof Hl as [_ [_ [_ [Hent _]]]].
  destruct e0 as [h ts len p]; destruct (Hent k _ E) as [[Hk [G [Hlen [Hnt Hs]]]] _].
  cbn [unshift entry_based eunshift Pd_e].
  split; [apply kgood_klift, G|split; [rewrite <- Hlen; destruct ts; reflexivity|split]].
  - cbn [strip_ok]; intros [Hlen' [Hp Ht]]; rewrite knth_klift in Ht by exact G.
    destruct (knth ts (pred len)) as [[y j|u [r' es']]|] eqn:Et; cbn in Ht; try discriminate.
    injection Ht as -> Hj; destruct p as [|p]; [lia|].
    apply Hs; split; [exact Hlen'|split; [lia|rewrite Et; f_equal; f_equal; lia]].
  - intros t Ht; rewrite klist_klift in Ht by apply kgood_inv, G.
    apply in_map_iff in Ht as [t0 [<- Ht0]].
    assert (Hok : eok t0) by apply (kgood_targets_ok ts G _ Ht0).
    split; [apply ok_unshift, Hok|].
    destruct (unshift r t0) as [y j|u rho] eqn:Eu; [exact Logic.I|].
    destruct (In_nth_error _ _ Ht0) as [i Ei].
    assert (Et : knth ts i = Some t0) by (rewrite knth_spec by apply kgood_shape, G; exact Ei).
    destruct (target_result _ r es k h ts len p i t0 Hl E Et) as [Hn HQ].
    change (tunshift r t0) with (unshift r t0) in Hn; rewrite Eu in Hn; cbn [tresult] in Hn.
    split; [apply (nwf_payload _ _ (mk_rvar h i) u rho Hb HQ Hn)|].
    apply (nest_napply b (mk_rvar h i) u rho b_entries_good Hn).
Qed.

(** Above the thresholds a target is moved. *)
Lemma HG_t t : eok t -> Pd_t t -> clears th t -> tcF cnone t = unshift tau (shift th t).
Proof.
  intros Hok [_ HP] Hc; destruct t as [y j|u rho]; [apply tcF_var_shift, Hc|].
  destruct HP as [Hw Hn]; cbn [tcF]; rewrite (IH3 rho Hn Hw Hc).
  destruct rho as [r' es']; reflexivity.
Qed.

Lemma sound_bl0 {X} {BX : Based X} (L : list X) : sound th bl0 L.
Proof.
  intros z _ k t m Ht _ _; unfold bl0; unfold th, cget in Ht; cbn [c_exc c_def] in Ht.
  rewrite get_map_filter in Ht; destruct (get k th_tree); [congruence|discriminate].
Qed.

(** The targets of an entry, mapped. *)
Lemma kmap_entry h (ts : kseq target) len p :
  Pd_e (Entry h ts len p) ->
  kgood (kmap th tau tcF bl0 cnone ts) /\ klist (kmap th tau tcF bl0 cnone ts) = map (tcF cnone) (klist ts).
Proof.
  intros [G [_ [_ HP]]].
  destruct (kgood_kmap th tau tcF (tcF cnone) Pd_t (fun B x _ _ => tcF_rebase B x)
              (fun z Hz HPz Hc => HG_t z Hz HPz Hc) (fun z _ _ => tcF_ok cnone z)
              bl0 cnone ts G (sound_bl0 _)) as [G1 E1].
  - intros y Hy; rewrite unshift_cnone by apply (HP y Hy); apply HP, Hy.
  - split; [exact G1|rewrite E1; apply map_ext_in; intros y Hy; rewrite unshift_cnone by apply (HP y Hy); reflexivity].
Qed.

Lemma ecF_good h ts len p :
  Pd_e (Entry h ts len p) -> entry_good h (ecF cnone (Entry h ts len p)).
Proof.
  intros HP; pose proof HP as [G [Hl _]]; destruct (kmap_entry h ts len p HP) as [G1 E1].
  cbn [ecF]; rewrite cget_cnone_dval; cbn [Nat.add].
  assert (Hl1 : klength (kmap th tau tcF bl0 cnone ts) = len).
  { rewrite (klength_spec _ (kgood_shape _ G1)), E1, length_map, <- Hl; symmetry; apply klength_spec, kgood_shape, G. }
  rewrite <- Hl1; apply (ecomp_spec h _ p G1).
Qed.

Lemma HG_e z : eok z -> Pd_e z -> clears th z -> ecF cnone z = unshift tau (shift th z).
Proof.
  intros Hok HP Hc; destruct z as [h ts len p]; pose proof HP as [G [Hl [Hs HPt]]].
  apply ecF_moved; try assumption.
  intros t Ht; apply HG_t; [apply HPt, Ht|apply HPt, Ht|].
  pose proof (cle_cmin_inv_r _ _ _ Hc) as Hts.
  exact (cle_mem th (ksann ts) (klist ts) t Hts (fun k => ksann_klist ts k G) Ht).
Qed.

Lemma HGok_e z : eok z -> Pd_e z -> eok (ecF cnone z).
Proof. intros _ HP; destruct z as [h ts len p]; apply (entry_good_ok h), ecF_good, HP. Qed.

(** The composite trie, absolute. *)
Definition esC : atrie entry := atmap th tau ecF bl0 r es.

Lemma esC_spec : ainv esC /\ forall k, aget k esC = option_map (fun y => ecF cnone (unshift r y)) (aget k es).
Proof.
  pose proof Hloc as [Hes _].
  apply (atmap_spec th tau ecF (ecF cnone) Pd_e (fun B x _ _ => ecF_rebase B x) HG_e HGok_e es bl0 r Hes (sound_bl0 _)).
  intros y Hy; destruct (aelems_aget es y Hy) as [k E]; apply (Pd_entries k y E).
Qed.

Lemma esC_entry k e0 :
  aget k es = Some e0 ->
  k = label_key (elabel e0)
  /\ entry_good (elabel e0) (ecF cnone (unshift r e0))
  /\ forall i, eabs (ecF cnone (unshift r e0)) i = rcomp (napply b (mk_rvar (elabel e0) i)).
Proof.
  intros E; pose proof Hloc as Hl; pose proof Hl as [_ [_ [_ [Hent _]]]].
  pose proof (Pd_entries k e0 E) as HP.
  destruct e0 as [h ts0 len p0]; destruct (Hent k _ E) as [[Hk [G0 [Hlen _]]] _]; cbn [elabel].
  split; [symmetry; exact Hk|split; [apply ecF_good, HP|]].
  intro i; cbn [unshift entry_based eunshift] in HP |- *.
  destruct (kmap_entry h _ len _ HP) as [G1 E1].
  assert (Hl1 : klength (kmap th tau tcF bl0 cnone (klift r ts0)) = len).
  { rewrite (klength_spec _ (kgood_shape _ G1)), E1, length_map, klist_klift, length_map by apply kgood_inv, G0.
    rewrite <- Hlen; symmetry; apply klength_spec, kgood_shape, G0. }
  cbn [ecF]; rewrite cget_cnone_dval; cbn [Nat.add]; rewrite <- Hl1.
  rewrite (proj2 (ecomp_spec h _ (dval r (label_key h) + p0) G1)), Hl1.
  cbn [napply v_label v_index]; rewrite Hk, E; cbn [eapply].
  destruct (Nat.ltb_spec i len) as [Hi|Hi].
  - unfold lapp; rewrite E1, length_map, klist_klift, length_map, nth_error_map, nth_error_map by apply kgood_inv, G0.
    rewrite knth_spec by apply kgood_shape, G0.
    destruct (nth_error (klist ts0) i) as [t0|] eqn:Et.
    + assert (Hi' : i < length (klist ts0)) by (apply nth_error_Some; rewrite Et; discriminate).
      destruct (Nat.ltb_spec i (length (klist ts0))); [|lia]; cbn [option_map].
      rewrite rcomp_tresult; reflexivity.
    + apply nth_error_None in Et; rewrite <- (klength_spec _ (kgood_shape _ G0)) in Et; lia.
  - cbn [rcomp]; f_equal; f_equal; rewrite Hk; lia.
Qed.

Lemma es_good_esC : es_good esC.
Proof.
  destruct esC_spec as [HesC HgC]; split; [exact HesC|].
  intros k e E; rewrite HgC in E; destruct (aget k es) as [e0|] eqn:E0; [|discriminate].
  cbn [option_map] in E; injection E as <-.
  destruct (esC_entry k e0 E0) as [Hk [Hg _]].
  assert (Hl : elabel (ecF cnone (unshift r e0)) = elabel e0)
    by (destruct (ecF cnone (unshift r e0)); destruct Hg as [-> _]; reflexivity).
  change (eunshift r e0) with (unshift r e0); rewrite Hl; split; assumption.
Qed.

Lemma cf_esC h i : cf r esC h i = rcomp (napply b (mk_rvar h i)).
Proof.
  unfold cf; rewrite (proj2 esC_spec).
  destruct (aget (label_key h) es) as [e0|] eqn:E0; cbn [option_map].
  - destruct (esC_entry _ e0 E0) as [Hk [_ Hm]]; apply label_key_inj in Hk; subst h; apply Hm.
  - cbn [napply v_label v_index]; rewrite E0; reflexivity.
Qed.

Lemma ncomp_b : ncomp pay b cnone = finish pay r esC (@atvisit entry bl0 r (fun k => k) es).
Proof.
  rewrite ncomp_eq; pose proof Hloc as [_ [Hcwf _]]; rewrite cadd_cnone by exact Hcwf; reflexivity.
Qed.

Theorem napply_ncomp_b v :
  Qof pay (v_label v) = true -> no_low pay r esC ->
  napply (ncomp pay b cnone) v = rcomp (napply b v).
Proof.
  intros HQ Hlow; destruct v as [h i]; cbn [v_label] in HQ.
  rewrite ncomp_b, napply_finish; [apply cf_esC|exact es_good_esC| |exact Hlow].
  unfold skipN; destruct pay eqn:Hp; [|reflexivity].
  destruct h as [s|]; [|discriminate].
  cbn [andb]; apply Pos.eqb_neq; intro E; apply label_key_inj in E; discriminate.
Qed.

Hypothesis IH4 : forall rho, nnest rho < nnest b -> nwf true rho -> cle wa (nroot (ncomp true rho cnone)).

Lemma tcF_ge t : Pd_t t -> cle wa (uses (tcF cnone t)).
Proof.
  intros [_ HP]; destruct t as [y j|u rho]; [apply cle_napply_a|].
  destruct HP as [Hw Hn]; apply (IH4 rho Hn Hw).
Qed.

Lemma ecF_ge z : Pd_e z -> cle wa (uses (ecF cnone z)).
Proof.
  intros HP; destruct z as [h ts len p]; pose proof HP as [G [Hl [_ HPt]]].
  destruct (kmap_entry h ts len p HP) as [G1 E1].
  assert (Hl1 : klength (kmap th tau tcF bl0 cnone ts) = len).
  { rewrite (klength_spec _ (kgood_shape _ G1)), E1, length_map, <- Hl; symmetry; apply klength_spec, kgood_shape, G. }
  cbn [ecF]; rewrite cget_cnone_dval; cbn [Nat.add]; rewrite <- Hl1.
  apply ecomp_ge; [exact G1|]; rewrite E1; intros t Ht; apply in_map_iff in Ht as [t0 [<- Ht0]].
  apply tcF_ge, HPt, Ht0.
Qed.

Lemma esC_ge k e : aget k esC = Some e -> cle wa (uses e).
Proof.
  intros E; rewrite (proj2 esC_spec) in E; destruct (aget k es) as [e0|] eqn:E0; [|discriminate].
  cbn [option_map] in E; injection E as <-; apply ecF_ge, (Pd_entries k e0 E0).
Qed.

Lemma es1_ge k e : aget k (es1 pay r esC) = Some e -> cle wa (uses e).
Proof.
  intros E; rewrite (Hg1 pay r esC es_good_esC) in E.
  destruct (aget k esC) as [e0|] eqn:E0; [injection E as <-; apply (esC_ge _ _ E0)|].
  destruct (skipN pay k); [discriminate|]; destruct (aget k esa); [apply (adrop_ge _ _ _ E)|discriminate].
Qed.

Lemma U_ge : cle wa (aann (es1 pay r esC)).
Proof. apply cle_aann; [apply (Hes1 pay r esC es_good_esC)|exact es1_ge]. Qed.

Lemma no_low_esC : no_low pay r esC.
Proof.
  intros k n _ Hw _ Hn; unfold dval; rewrite cget_ctotal; cbn [oval].
  pose proof (nwf_fin _ _ Hb) as Hf; unfold nfin in Hf; cbn [nroot] in Hf.
  assert (Hr : cget r k = Some 0) by (unfold cget; rewrite Hw; exact Hf).
  rewrite Hr; cbn [oval].
  destruct (cget wa k) as [w|] eqn:Ew; [|exfalso; exact (wa_total k Ew)].
  pose proof (U_ge k w n Ew Hn); cbn; lia.
Qed.

(** One level of [ncomp] means [b] followed by [a]. *)
Theorem napply_ncomp v :
  Qof pay (v_label v) = true -> napply (ncomp pay b cnone) v = rcomp (napply b v).
Proof. intros HQ; apply napply_ncomp_b; [exact HQ|exact no_low_esC]. Qed.

(** The new root is above [a]'s. *)
Theorem root_ge : cle wa (nroot (ncomp pay b cnone)).
Proof.
  rewrite ncomp_b, finish_eq; cbn [nroot]; unfold R.
  intros k n m Hn Hm; rewrite cget_cmin in Hm.
  destruct (omin_some_or _ _ _ Hm) as [Hu|Hj]; [apply (U_ge k n m Hn Hu)|].
  rewrite cget_jstarts in Hj; destruct (skipN pay k); [discriminate|].
  destruct (aget k esa); [discriminate|]; rewrite cget_ctotal, Hn in Hj; injection Hj as <-; cbn; lia.
Qed.

(** *** Keyedness *)

Hypothesis Hwa : nwf false a.
Hypothesis IH1 : forall rho, nnest rho < nnest b -> nwf true rho -> nlocal Qnamed (ncomp true rho cnone).

Lemma keyed_root Q (c : nadj) : nlocal Q c -> keyed (nroot c).
Proof. destruct c as [w es']; intros [_ [_ [Hk _]]]; exact Hk. Qed.

Lemma keyed_a_result v u rho : napply a v = inr (u, rho) -> keyed (nroot rho).
Proof. intros E; apply (keyed_root Qnamed), (nwf_local true), (nwf_payload false a v u rho Hwa eq_refl E). Qed.

Lemma keyed_a_target k e t :
  aget k esa = Some e -> In t (klist (etargets e)) -> keyed (tuses (tunshift wa t)).
Proof.
  intros Ea Ht; destruct e as [h ts len p]; cbn [etargets] in Ht.
  destruct (esa_ok _ _ Ea) as [Hk [G _]]; subst k.
  destruct (In_nth_error _ _ Ht) as [i Ei].
  assert (Et : knth ts i = Some t) by (rewrite knth_spec by apply kgood_shape, G; exact Ei).
  assert (Hn : napply a (mk_rvar h i) = tresult (tunshift wa t)).
  { unfold esa, wa in *; destruct a as [w es'] eqn:Eqa; cbn [nentries nroot] in *.
    apply (target_result Qall w es' _ h ts len p i t Ha Ea Et). }
  destruct (tunshift wa t) as [y j|u rho] eqn:Eu; [apply keyed_cone|].
  apply (keyed_a_result _ _ _ Hn).
Qed.

Lemma keyed_alist h t : In t (alist h) -> keyed (tuses t).
Proof.
  unfold alist; destruct (aget (label_key h) esa) as [e|] eqn:Ea; [|intros []].
  destruct e as [h' tsa len p]; intros Ht; apply in_map_iff in Ht as [t0 [<- Ht0]].
  apply (keyed_a_target _ _ _ Ea Ht0).
Qed.

Lemma keyed_tcF t : Pd_t t -> keyed (tuses (tcF cnone t)).
Proof.
  intros [_ HP]; destruct t as [y j|u rho]; cbn [tcF].
  - rewrite tuses_rtarget; destruct (napply a _) as [v|[u rho]] eqn:E; [apply keyed_cone|apply (keyed_a_result _ _ _ E)].
  - destruct HP as [Hw Hn]; apply (keyed_root Qnamed), IH1; assumption.
Qed.

Lemma keyed_esC k e : aget k esC = Some e -> keyed (uses e).
Proof.
  intros E; rewrite (proj2 esC_spec) in E; destruct (aget k es) as [e0|] eqn:E0; [|discriminate].
  cbn [option_map] in E; injection E as <-.
  pose proof (Pd_entries k e0 E0) as HP; destruct (esC_entry k e0 E0) as [_ [Hg _]].
  change (eunshift r e0) with (unshift r e0).
  set (z := unshift r e0) in *; destruct z as [h ts len p] eqn:Ez.
  pose proof HP as [G [Hl _]].
  destruct (kmap_entry h ts len p HP) as [G1 E1].
  assert (Hl1 : klength (kmap th tau tcF bl0 cnone ts) = len).
  { rewrite (klength_spec _ (kgood_shape _ G1)), E1, length_map, <- Hl; symmetry; apply klength_spec, kgood_shape, G. }
  change (ecF cnone (Entry h ts len p)) with (ecomp h (kmap th tau tcF bl0 cnone ts) len (0 + p)) in Hg |- *.
  cbn [Nat.add] in Hg |- *; rewrite <- Hl1 in Hg |- *.
  destruct (ecomp h _ (klength _) p) as [h' ts' len' p'] eqn:Ec; destruct Hg as [_ [G' _]].
  apply keyed_entry; [exact G'|]; intros t Ht.
  pose proof (ecomp_targets h _ p t G1) as Hc; rewrite Ec in Hc; cbn [etargets] in Hc.
  destruct (Hc Ht) as [Ht1|Ht1]; [rewrite E1 in Ht1; apply in_map_iff in Ht1 as [t0 [<- Ht0]]|apply (keyed_alist h t Ht1)].
  apply keyed_tcF; destruct HP as [_ [_ [_ HPt]]]; apply HPt, Ht0.
Qed.

Lemma Hpay_esC : pay = true -> aget (label_key None) esC = None.
Proof.
  intros Hp; rewrite (proj2 esC_spec); destruct (aget (label_key None) es) as [e0|] eqn:E0; [|reflexivity].
  exfalso; pose proof Hloc as [_ [_ [_ [Hent _]]]]; destruct (Hent _ _ E0) as [Hok [HQ _]].
  destruct e0 as [h ts len p]; destruct Hok as [Hk _]; apply label_key_inj in Hk; subst h.
  unfold Qof in HQ; rewrite Hp in HQ; discriminate.
Qed.

(** *** Unvisited entries were moved *)

Definition vis : list positive := @atvisit entry bl0 r (fun k => k) es.

Lemma Hvis_esC k h p :
  aget k esC = Some (Entry h KNil 0 p) -> ~ In k vis -> aget k esa = None -> dval (ctotal wa r) k < p.
Proof.
  intros E Hnv Ea; rewrite (proj2 esC_spec) in E.
  destruct (aget k es) as [e0|] eqn:E0; [|discriminate]; cbn [option_map] in E; injection E as E.
  pose proof Hloc as [Hes [_ [_ [Hent _]]]].
  pose proof (atvisit_spec th es bl0 r (fun k => k) k e0 Hes (sound_bl0 _) E0 Hnv) as Hc.
  rewrite HG_e in E; [|exact (ok_unshift r e0 (ainv_get_ok es k e0 Hes E0))|apply (Pd_entries k e0 E0)|exact Hc].
  destruct e0 as [h0 ts0 len0 p0]; destruct (Hent _ _ E0) as [[Hk [_ [_ [Hnt _]]]] _].
  cbn [unshift shift entry_based eunshift eshift] in E; injection E as -> Hts Hlen Hp; subst len0.
  destruct Hnt as [Hnt|Hnt]; [lia|].
  assert (Hth : dval th k = 0) by (unfold dval; rewrite cget_th, Ea; reflexivity).
  assert (Hta : dval tau k = dval wa k) by (unfold dval; rewrite cget_tau, Ea; reflexivity).
  rewrite Hk in Hp; rewrite Hth, Hta in Hp; unfold dval in *; rewrite cget_ctotal; cbn [oval]; lia.
Qed.

(** *** Labels [a] does not move are not pushed up too far *)

Hypothesis IH5 : forall rho, nnest rho < nnest b -> nwf true rho ->
                 forall k m, aget k esa = None -> cget (nroot rho) k = Some m ->
                 exists m', cget (nroot (ncomp true rho cnone)) k = Some m' /\ m' <= dval wa k + m.

Lemma tcF_bound t k m :
  Pd_t t -> aget k esa = None -> cget (uses t) k = Some m ->
  exists m', cget (uses (tcF cnone t)) k = Some m' /\ m' <= dval wa k + m.
Proof.
  intros [_ HP] Ea Hm; destruct t as [y j|u rho].
  - cbn in Hm; rewrite cget_cone in Hm; destruct (Pos.eqb_spec k (label_key y)) as [->|]; [|discriminate].
    injection Hm as <-; cbn [tcF]; rewrite cget_cnone_dval; cbn [Nat.add].
    assert (Ht0 : thv y = 0) by (unfold thv, dval; rewrite cget_th, Ea; reflexivity).
    assert (Hta : tauv y = dval wa (label_key y)) by (unfold tauv, dval; rewrite cget_tau, Ea; reflexivity).
    rewrite napply_a_shift by lia; cbn [rtarget v_label v_index uses target_based tuses].
    rewrite cget_cone_same; eexists; split; [reflexivity|lia].
  - destruct HP as [Hw Hn]; apply (IH5 rho Hn Hw k m Ea Hm).
Qed.

Lemma witness_bound k m :
  aget k esa = None -> cget r k = Some m -> cget (aann es) k = Some 0 ->
  exists n, cget (aann (es1 pay r esC)) k = Some n /\ n <= dval wa k + m.
Proof.
  intros Ea Hr Hz; pose proof Hloc as [Hes _].
  apply (aann_zero es k Hes) in Hz as [k2 [e2 [E2 Z2]]].
  pose proof (Pd_entries k2 e2 E2) as HP.
  assert (Hu : cget (uses (unshift r e2)) k = Some m) by (rewrite uses_unshift, Z2, Hr; cbn; f_equal; lia).
  set (z := unshift r e2) in *; destruct z as [h2 ts2 len2 p2] eqn:Ez.
  pose proof HP as [G2 [Hl2 _]].
  destruct (kmap_entry h2 ts2 len2 p2 HP) as [G1 E1].
  assert (Hl1 : klength (kmap th tau tcF bl0 cnone ts2) = len2).
  { rewrite (klength_spec _ (kgood_shape _ G1)), E1, length_map, <- Hl2; symmetry; apply klength_spec, kgood_shape, G2. }
  assert (Hc : exists m', cget (uses (ecF cnone (Entry h2 ts2 len2 p2))) k = Some m' /\ m' <= dval wa k + m).
  { change (ecF cnone (Entry h2 ts2 len2 p2)) with (ecomp h2 (kmap th tau tcF bl0 cnone ts2) len2 (0 + p2)).
    cbn [Nat.add]; rewrite <- Hl1.
    rewrite uses_entry_klist in Hu by exact G2.
    destruct (omin_some_or _ _ _ Hu) as [Hp|Ht].
    - rewrite cget_cone in Hp; destruct (Pos.eqb_spec k (label_key h2)) as [->|]; [|discriminate].
      injection Hp as <-.
      assert (Ht0 : thv h2 = 0) by (unfold thv, dval; rewrite cget_th, Ea; reflexivity).
      assert (Hta : tauv h2 = dval wa (label_key h2)) by (unfold tauv, dval; rewrite cget_tau, Ea; reflexivity).
      destruct (ecomp_uses_pass h2 _ p2 G1 ltac:(lia)) as [m' [Em' Hm']]; exists m'; split; [exact Em'|lia].
    - destruct (lmin_attained _ _ _ Ht) as [t [Hin Et]].
      destruct (tcF_bound t k m ltac:(destruct HP as [_ [_ [_ HPt]]]; apply HPt, Hin) Ea Et) as [m1 [Em1 Hm1]].
      destruct (ecomp_uses_target h2 _ p2 (tcF cnone t) k m1 G1 ltac:(rewrite E1; apply in_map, Hin) Em1)
        as [m' [Em' Hm']].
      exists m'; split; [exact Em'|lia]. }
  destruct Hc as [m' [Em' Hm']].
  assert (E1' : aget k2 (es1 pay r esC) = Some (ecF cnone (Entry h2 ts2 len2 p2))).
  { rewrite (Hg1 pay r esC es_good_esC), (proj2 esC_spec), E2; cbn [option_map].
    change (eunshift r e2) with (unshift r e2).
    first [rewrite Ez; reflexivity | rewrite <- Ez; reflexivity | reflexivity]. }
  rewrite (ainv_ann _ (Hes1 pay r esC es_good_esC)).
  destruct (lmin_le _ _ k m' (aget_in _ _ _ E1') Em') as [n [En Hn]].
  exists n; split; [exact En|lia].
Qed.

Lemma Hatt_esC k :
  skipN pay k = false -> aget k esC <> None -> aget k esa = None ->
  exists n, cget (aann (es1 pay r esC)) k = Some n /\ n <= dval (ctotal wa r) k.
Proof.
  intros _ HC Ea; rewrite (proj2 esC_spec) in HC.
  destruct (aget k es) as [e0|] eqn:E0; [|contradiction].
  pose proof Hloc as [_ [_ [_ [Hent [HQ _]]]]].
  destruct (Hent _ _ E0) as [Hok [HQe Hz]].
  assert (Hk : k = label_key (elabel e0)) by (destruct e0; destruct Hok as [Hk _]; symmetry; exact Hk).
  destruct (cget r k) as [m|] eqn:Hr; [|exfalso; rewrite Hk in Hr; exact (HQ _ HQe Hr)].
  destruct (witness_bound k m Ea Hr Hz) as [n [En Hn]].
  exists n; split; [exact En|unfold dval; rewrite cget_ctotal, Hr; cbn [oval]; unfold dval in Hn; lia].
Qed.

(** *** The normal form of one level *)

Lemma Hfa_wf : nfin a.
Proof. apply (nwf_fin false a Hwa). Qed.

Lemma HW0_b : c_def r = Some 0.
Proof. apply (nwf_fin _ _ Hb). Qed.

Lemma keyed_r : keyed r.
Proof. apply (keyed_root _ b Hloc). Qed.

Theorem nlocal_ncomp : nlocal (Qof pay) (ncomp pay b cnone).
Proof.
  rewrite ncomp_b; fold vis.
  apply (nlocal_finish pay r esC vis es_good_esC keyed_esC keyed_r (fun k e Ea t Ht => keyed_a_target k e t Ea Ht) Hfa_wf HW0_b
           Hpay_esC Hatt_esC Hvis_esC).
Qed.

Theorem nfin_ncomp : nfin (ncomp pay b cnone).
Proof. rewrite ncomp_b; apply nfin_finish; [exact Hfa_wf|exact HW0_b]. Qed.

(** The new root of a label [a] does not move is at most where [a] sends
    the old one. *)
Theorem root_le k m :
  aget k esa = None -> cget r k = Some m ->
  exists m', cget (nroot (ncomp pay b cnone)) k = Some m' /\ m' <= dval wa k + m.
Proof.
  intros Ea Hr; rewrite ncomp_b, finish_eq; cbn [nroot]; unfold R; rewrite cget_cmin, cget_jstarts.
  destruct (skipN pay k) eqn:Sk.
  - unfold skipN in Sk; apply andb_prop in Sk as [Hp Hk]; apply Pos.eqb_eq in Hk; subst k.
    pose proof Hloc as [_ [_ [_ [_ [_ HnQ]]]]].
    assert (HQ : Qof pay None = false) by (unfold Qof; rewrite Hp; reflexivity).
    destruct (HnQ None HQ) as [[Hn _]|[_ Hz]]; [rewrite Hr in Hn; discriminate|].
    destruct (witness_bound _ m Ea Hr Hz) as [n [En Hn]]; rewrite En; cbn [omin]; eexists; split; [reflexivity|lia].
  - rewrite Ea, cget_ctotal, Hr; cbn [oval].
    destruct (cget (aann (es1 pay r esC)) k); cbn; eexists; split; [reflexivity|unfold dval; lia|reflexivity|unfold dval; lia].
Qed.

(** *** Above the thresholds, a whole level is moved *)

Lemma nlocal_nmove : nlocal (Qof pay) (nmove b).
Proof.
  pose proof Hloc as [Hes [Hcwf [Hkey [Hent [HQ HnQ]]]]]; cbn [nmove nlocal].
  split; [exact Hes|split; [apply cwf_cmap2|split; [apply keyed_cmap2; [apply keyed_tau|apply keyed_cmap2; [exact Hkey|apply keyed_th]]|]]].
  split; [exact Hent|split].
  - intros l Hl; rewrite cget_cadd, cget_csub; specialize (HQ l Hl).
    destruct (cget r (label_key l)); [destruct (cget tau _), (cget th _); discriminate|contradiction].
  - intros l Hl; rewrite cget_cadd, cget_csub.
    destruct (HnQ l Hl) as [[Hn Ha']|[Hn Ha']]; [left; rewrite Hn; split; [destruct (cget tau _); reflexivity|exact Ha']|].
    right; split; [|exact Ha'].
    destruct (cget r (label_key l)); [destruct (cget tau _), (cget th _); discriminate|contradiction].
Qed.

Lemma dval_move k p : cget r k = Some p -> dval (cadd tau (csub r th)) k = dval tau k + (p - dval th k).
Proof. intros Hr; unfold dval; rewrite cget_cadd, cget_csub, Hr; destruct (cget th k), (cget tau k); reflexivity. Qed.

Lemma napply_nmove v :
  cle th r -> Qof pay (v_label v) = true -> napply (nmove b) v = rcomp (napply b v).
Proof.
  intros Hc HQv; pose proof Hloc as Hl; pose proof Hl as [Hes [_ [_ [Hent [HQ _]]]]].
  destruct v as [h i]; cbn [v_label v_index] in *; cbn [nmove napply v_label v_index].
  set (kh := label_key h).
  assert (Hr : exists q, cget r kh = Some q) by (destruct (cget r kh) eqn:E; [eauto|exfalso; exact (HQ h HQv E)]).
  destruct Hr as [q Hq].
  assert (Hthq : dval th kh <= q) by (unfold dval; destruct (cget th kh) as [t|] eqn:Et; cbn; [apply (Hc kh t q Et Hq)|lia]).
  assert (Hshift : forall j, q <= j -> napply a (mk_rvar h j) = inl (mk_rvar h (j - thv h + tauv h)))
    by (intros j Hj; apply napply_a_shift; unfold thv; fold kh; lia).
  destruct (aget kh es) as [e0|] eqn:E0.
  - destruct e0 as [h0 ts len p]; destruct (Hent _ _ E0) as [[Hk [G [Hlen _]]] _].
    apply label_key_inj in Hk; subst h0; cbn [eapply].
    destruct (Nat.ltb_spec i len) as [Hi|Hi].
    + destruct (knth_some ts i G ltac:(lia)) as [t0 Et]; rewrite Et.
      rewrite rcomp_tresult; f_equal.
      assert (Hin : In t0 (klist ts)) by apply (knth_in _ _ _ G Et).
      assert (Hok : eok t0) by apply (kgood_targets_ok ts G _ Hin).
      assert (Hcov : forall k, cget (uses t0) k <> None ->
                     exists p0, cget r k = Some p0 /\ cget r k = Some p0 /\ forall t, cget th k = Some t -> t <= p0).
      { intros k Hk; destruct (cget r k) as [p0|] eqn:Ek.
        - exists p0; split; [reflexivity|split; [reflexivity|intros t Et'; apply (Hc k t p0 Et' Ek)]].
        - exfalso; pose proof (root_covers _ r es k Hl HW0_b Ek kh _ E0) as Hn.
          rewrite uses_entry_klist in Hn by exact G.
          destruct (cget (uses t0) k) as [m|] eqn:Em; [|contradiction].
          destruct (lmin_le _ t0 k m Hin Em) as [n [En _]]; rewrite En in Hn.
          destruct (cget (cone _ p) k); discriminate. }
      assert (HPd : Pd_t (unshift r t0)).
      { pose proof (Pd_entries kh _ E0) as [_ [_ [_ HPt]]]; apply HPt; cbn [etargets unshift entry_based eunshift].
        rewrite klist_klift by apply kgood_inv, G; apply in_map, Hin. }
      change (tunshift r t0) with (unshift r t0); rewrite HG_t.
      * change (cadd tau (csub r th)) with (move th tau r); symmetry; exact (move_shift th tau r r t0 Hok Hcov).
      * apply ok_unshift, Hok.
      * exact HPd.
      * intros k t m Et' Em; rewrite uses_unshift in Em.
        destruct (cget (uses t0) k) as [u|] eqn:Eu; [|destruct (cget r k); discriminate].
        destruct (Hcov k ltac:(rewrite Eu; discriminate)) as [p0 [Ep _]]; rewrite Ep in Em; cbn in Em.
        injection Em as <-; specialize (Hc k t p0 Et' Ep); lia.
    + cbn [rcomp]; fold kh; unfold dval at 2; rewrite Hq; cbn [oval].
      rewrite Hshift by lia; rewrite (dval_move kh q Hq); unfold thv, tauv; fold kh; f_equal; f_equal; lia.
  - cbn [rcomp]; fold kh; unfold dval at 2; rewrite Hq; cbn [oval].
    rewrite Hshift by lia; rewrite (dval_move kh q Hq); unfold thv, tauv; fold kh; f_equal; f_equal; lia.
Qed.

Theorem ncomp_moved : cle th r -> ncomp pay b cnone = nmove b.
Proof.
  intros Hc; apply (ncanonical (Qof pay)); [exact nlocal_ncomp|exact nlocal_nmove|].
  intros v Hv; rewrite napply_ncomp, napply_nmove by assumption; reflexivity.
Qed.

(** *** Deep well-formedness *)

Hypothesis IH0 : forall rho, nnest rho < nnest b -> nwf true rho -> nwf true (ncomp true rho cnone).

Theorem nwf_ncomp : nwf pay (ncomp pay b cnone).
Proof.
  apply nwf_intro; [exact nlocal_ncomp|exact nfin_ncomp|].
  intros v u rho' Hv E; rewrite napply_ncomp in E by exact Hv.
  destruct (napply b v) as [y|[u0 rho]] eqn:Eb; cbn [rcomp] in E.
  - apply (nwf_payload false a y u rho' Hwa eq_refl E).
  - injection E as -> <-; apply IH0.
    + apply (nest_napply b v u rho b_entries_good Eb).
    + apply (nwf_payload _ _ v u rho Hb Hv Eb).
Qed.

End Step.

(** ** Composition is correct *)

Section Main.

Hypothesis Hwa : nwf false a.

Definition comp_ok (pay : bool) (b : nadj) : Prop :=
  nwf pay (ncomp pay b cnone)
  /\ (forall v, Qof pay (v_label v) = true -> napply (ncomp pay b cnone) v = rcomp (napply b v))
  /\ (cle th (nroot b) -> ncomp pay b cnone = nmove b)
  /\ cle wa (nroot (ncomp pay b cnone))
  /\ (forall k m, aget k esa = None -> cget (nroot b) k = Some m ->
      exists m', cget (nroot (ncomp pay b cnone)) k = Some m' /\ m' <= dval wa k + m).

Lemma comp_ok_lt n : forall pay b, nnest b < n -> nwf pay b -> comp_ok pay b.
Proof.
  induction n as [|n IHn]; intros pay [r es] Hn Hb; [lia|].
  assert (IH : forall rho, nnest rho < nnest (NAdj r es) -> nwf true rho -> comp_ok true rho)
    by (intros rho Hr Hw; apply IHn; [lia|exact Hw]).
  assert (IH0 : forall rho, nnest rho < nnest (NAdj r es) -> nwf true rho -> nwf true (ncomp true rho cnone))
    by (intros rho Hr Hw; apply (IH rho Hr Hw)).
  assert (IH1 : forall rho, nnest rho < nnest (NAdj r es) -> nwf true rho -> nlocal Qnamed (ncomp true rho cnone))
    by (intros rho Hr Hw; apply (nwf_local true), (IH rho Hr Hw)).
  assert (IH3 : forall rho, nnest rho < nnest (NAdj r es) -> nwf true rho -> cle th (nroot rho) ->
                ncomp true rho cnone = nmove rho)
    by (intros rho Hr Hw; apply (IH rho Hr Hw)).
  assert (IH4 : forall rho, nnest rho < nnest (NAdj r es) -> nwf true rho -> cle wa (nroot (ncomp true rho cnone)))
    by (intros rho Hr Hw; apply (IH rho Hr Hw)).
  assert (IH5 : forall rho, nnest rho < nnest (NAdj r es) -> nwf true rho ->
                forall k m, aget k esa = None -> cget (nroot rho) k = Some m ->
                exists m', cget (nroot (ncomp true rho cnone)) k = Some m' /\ m' <= dval wa k + m)
    by (intros rho Hr Hw; apply (IH rho Hr Hw)).
  split; [apply (nwf_ncomp pay r es Hb IH3 IH4 Hwa IH1 IH5 IH0)|].
  split; [intros v Hv; apply (napply_ncomp pay r es Hb IH3 IH4 v Hv)|].
  split; [apply (ncomp_moved pay r es Hb IH3 IH4 Hwa IH1 IH5)|].
  split; [apply (root_ge pay r es Hb IH3 IH4)|].
  intros k m Ea Hr; eapply root_le; eassumption.
Qed.

Theorem comp_correct pay b : nwf pay b -> comp_ok pay b.
Proof. apply (comp_ok_lt (S (nnest b))); lia. Qed.

End Main.


End Compose.

(** ** The top level *)

Theorem compose_spec {T} (a b : @nadj T) :
  nwf false a -> nwf false b ->
  nwf false (compose a b) /\ forall v, napply (compose a b) v = rcomp a (napply b v).
Proof.
  intros Ha Hb; destruct (comp_correct a (nwf_local _ _ Ha) Ha false b Hb) as [Hw [Hm _]].
  split; [exact Hw|intros v; apply Hm; reflexivity].
Qed.

(** * The point operations stay deeply well formed *)

Section PointWf.

Context {T : Type}.
Local Notation nadj := (@nadj T).
Local Notation entry := (@entry T).
Local Notation target := (@target T).

(** A payload result comes from a target of some entry, and moving the
    root moves the payload's root with it. *)
Lemma napply_root_payload W W' (es : atrie entry) v u rho' :
  napply (NAdj W' es) v = inr (u, rho') ->
  exists k e r0 es0, aget k es = Some e /\ knth (etargets e) (v_index v) = Some (TBind u (NAdj r0 es0))
                     /\ rho' = NAdj (cadd W' r0) es0
                     /\ napply (NAdj W es) v = inr (u, NAdj (cadd W r0) es0).
Proof.
  cbn [napply]; destruct (aget _ es) as [[h ts len p]|] eqn:E; [|discriminate].
  cbn [eapply]; destruct (Nat.ltb _ _); [|discriminate].
  destruct (knth ts _) as [[y j|u0 [r0 es0]]|] eqn:Et; cbn; try discriminate.
  intros [= -> <-]; do 4 eexists; split; [exact E|split; [exact Et|split; reflexivity]].
Qed.

Lemma cadd_assoc_covered d w r0 :
  (forall k, cget r0 k <> None -> cget w k <> None) -> cadd (cadd d w) r0 = cadd d (cadd w r0).
Proof.
  intros H; apply counts_ext; try apply cwf_cmap2; intro k; rewrite !cget_cadd.
  destruct (cget r0 k) as [x|] eqn:Er; [|destruct (cget w k), (cget d k); reflexivity].
  destruct (cget w k) as [y|] eqn:Ew; [|exfalso; apply (H k); congruence].
  destruct (cget d k); cbn; f_equal; lia.
Qed.

Lemma nwf_cadd n : forall pay w (es : atrie entry) d,
  nnest (NAdj w es) < n -> nwf pay (NAdj w es) -> keyed d -> c_def d = None -> nwf pay (NAdj (cadd d w) es).
Proof.
  induction n as [|n IH]; intros pay w es d Hn Hb Kd Dd; [lia|].
  pose proof (nwf_local _ _ Hb) as Hl; pose proof (nwf_fin _ _ Hb) as Hf.
  apply nwf_intro.
  - destruct Hl as [Hes [Cw [Kw [Hent [HQ HnQ]]]]].
    split; [exact Hes|split; [apply cwf_cmap2|split; [apply keyed_cmap2; assumption|split; [exact Hent|split]]]].
    + intros l Hq; rewrite cget_cadd; specialize (HQ l Hq); destruct (cget w _); [discriminate|contradiction].
    + intros l Hq; rewrite cget_cadd; destruct (HnQ l Hq) as [[-> H]|[H1 H]]; [left; split; [destruct (cget d _); reflexivity|exact H]|].
      right; split; [destruct (cget w _); [discriminate|contradiction]|exact H].
  - unfold nfin in *; cbn [nroot c_def cadd cmap2] in *; rewrite Dd, Hf; reflexivity.
  - intros v u rho' Hq E.
    destruct (napply_root_payload w _ es v u rho' E) as [k [e [r0 [es0 [Ek [Et [-> E0]]]]]]].
    assert (G : kgood (etargets e)).
    { destruct Hl as [_ [_ [_ [Hent _]]]]; destruct (Hent k e Ek) as [Hok _]; destruct e; apply Hok. }
    rewrite cadd_assoc_covered.
    + apply IH; [|exact (nwf_payload _ _ v u _ Hb Hq E0)|exact Kd|exact Dd].
      assert (HG : forall k' e', aget k' (nentries (NAdj w es)) = Some e' -> kgood (etargets e')).
      { intros k' e' E'; destruct Hl as [_ [_ [_ [Hent _]]]]; destruct (Hent k' e' E') as [Hok _]; destruct e'; apply Hok. }
      pose proof (nest_napply (NAdj w es) v u _ HG E0) as Hlt; cbn [nnest] in *; lia.
    + intros k' Hk' Hw.
      pose proof (root_covers (Qof pay) w es k' Hl Hf Hw k e Ek) as Hcv.
      destruct e as [h ts len p]; rewrite uses_entry_klist in Hcv by exact G.
      cbn [etargets] in Et; pose proof (knth_in _ _ _ G Et) as Hin.
      destruct (cget r0 k') as [x|] eqn:Ex; [|contradiction].
      change (cget (uses (TBind u (NAdj r0 es0) : target)) k' = Some x) in Ex.
      destruct (lmin_le (klist ts) _ k' x Hin Ex) as [m [Em _]]; rewrite Em in Hcv.
      destruct (cget (cone _ p) k'); discriminate.
Qed.

Theorem nwf_identity : nwf false (@nidentity T).
Proof.
  apply nwf_intro; [apply nlocal_identity|apply nfin_identity|].
  intros v u rho _ E; rewrite napply_identity in E; discriminate.
Qed.

Theorem nwf_weaken h (a : nadj) : nwf false a -> nwf false (weaken h a).
Proof.
  destruct a as [w es]; intros Ha; cbn [weaken].
  apply (nwf_cadd (S (nnest (NAdj w es)))); [cbn [nnest]; lia|exact Ha|apply keyed_cone|reflexivity].
Qed.

(** A target is deeply well formed: a payload's adjustment is a named-only
    normal form. *)
Definition twf (t : target) : Prop :=
  match t with TVar _ _ => True | TBind _ rho => nwf true rho end.

Theorem nwf_extend h (t : target) (a : nadj) :
  nwf false a -> twf t -> nwf false (extend h t a).
Proof.
  intros Ha Ht; pose proof (nwf_local _ _ Ha) as Hl; pose proof (nwf_fin _ _ Ha) as Hf.
  assert (Hok : tok t)
    by (destruct t as [y j|u [r es]]; [exact Logic.I|cbn in Ht; destruct (nwf_local _ _ Ht) as [_ [Hc _]]; exact Hc]).
  assert (Hk : keyed (tuses t))
    by (destruct t as [y j|u [r es]]; [apply keyed_cone|cbn in Ht; destruct (nwf_local _ _ Ht) as [_ [_ [Hk _]]]; exact Hk]).
  apply nwf_intro; [apply nlocal_extend; assumption|apply nfin_extend, Hf|].
  intros v u rho _ E; rewrite napply_extend in E by assumption.
  destruct (rvar_eqb v _).
  - destruct t as [y j|u' rho']; cbn in E; [discriminate|injection E as -> <-; exact Ht].
  - apply (nwf_payload _ _ _ u rho Ha eq_refl E).
Qed.

Theorem nwf_lift h (a : nadj) : nwf false a -> nwf false (lift h a).
Proof. intros Ha; apply nwf_extend; [apply nwf_weaken, Ha|exact Logic.I]. Qed.

End PointWf.
