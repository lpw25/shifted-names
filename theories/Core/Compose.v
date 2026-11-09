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
From ShiftedNames.Core Require Import Trie Label Var Counts Based Skew ATrie Prune Repr Point.
Import ListNotations.

Section Compose.

Context {T : Type}.

Local Notation nadj := (@nadj T).
Local Notation result := (@result T).
Local Notation entry := (@entry T).
Local Notation target := (@target T).

(** ** Nesting depth, for induction through payloads *)

Fixpoint ktmax {X} (f : X -> nat) (t : ktree X) : nat :=
  match t with KLeaf x => f x | KNode _ x l r => Nat.max (f x) (Nat.max (ktmax f l) (ktmax f r)) end.

Fixpoint kmaxs {X} (f : X -> nat) (s : kseq X) : nat :=
  match s with KNil => 0 | KCons _ _ t s' => Nat.max (ktmax f t) (kmaxs f s') end.

Fixpoint amax {X} (f : X -> nat) (t : atrie X) : nat :=
  match t with
  | AEmpty => 0
  | ANode _ l o r => Nat.max (amax f l) (Nat.max (match o with Some x => f x | None => 0 end) (amax f r))
  end.

Fixpoint tnest (t : target) : nat :=
  match t with TVar _ _ => 0 | TBind _ rho => S (nnest rho) end
with nnest (b : nadj) : nat :=
  match b with NAdj _ es => amax (fun e => match e with Entry _ ts _ _ => kmaxs tnest ts end) es end.

Definition enest (e : entry) : nat := match e with Entry _ ts _ _ => kmaxs tnest ts end.

Section Depth.

Context {X : Type} {BX : Based X}.
Variable f : X -> nat.
Hypothesis Hf : forall d x, f (unshift d x) = f x.

Lemma ktmax_in t : forall x, In x (ktlist t) -> f x <= ktmax f t.
Proof.
  induction t as [y|c y l IHl r IHr]; cbn [ktlist ktmax]; [intros x [<-|[]]; lia|].
  intros x Hin; apply in_map_iff in Hin as [x0 [<- Hin]]; rewrite Hf.
  destruct Hin as [<-|Hin]; [lia|apply in_app_or in Hin as [Hin|Hin]; [specialize (IHl _ Hin)|specialize (IHr _ Hin)]; lia].
Qed.

Lemma kmaxs_in s : forall x, In x (klist s) -> f x <= kmaxs f s.
Proof.
  induction s as [|c w t s IH]; cbn [klist kmaxs]; [intros x []|].
  intros x Hin; apply in_map_iff in Hin as [x0 [<- Hin]]; rewrite Hf.
  apply in_app_or in Hin as [Hin|Hin]; [pose proof (ktmax_in t x0 Hin)|specialize (IH _ Hin)]; lia.
Qed.

Lemma amax_in t : forall x, In x (aelems t) -> f x <= amax f t.
Proof.
  induction t as [|c l IHl o r IHr]; cbn [aelems amax]; [intros x []|].
  intros x Hin; apply in_map_iff in Hin as [x0 [<- Hin]]; rewrite Hf.
  apply in_app_or in Hin as [Hin|Hin]; [specialize (IHl _ Hin); lia|].
  apply in_app_or in Hin as [Hin|Hin]; [destruct o as [y|]; [destruct Hin as [<-|[]]; lia|destruct Hin]|].
  specialize (IHr _ Hin); lia.
Qed.

End Depth.

Lemma tnest_unshift d (t : target) : tnest (unshift d t) = tnest t.
Proof. destruct t as [y j|u [r es]]; reflexivity. Qed.

Lemma kmaxs_klift d (ts : kseq target) : kmaxs tnest (klift d ts) = kmaxs tnest ts.
Proof. destruct ts; reflexivity. Qed.

Lemma enest_unshift d (e : entry) : enest (unshift d e) = enest e.
Proof. destruct e as [h ts len p]; cbn; apply kmaxs_klift. Qed.

Lemma nnest_es r (es : atrie entry) : nnest (NAdj r es) = amax enest es.
Proof. reflexivity. Qed.

Theorem nest_napply (b : nadj) v u rho :
  (forall k e, aget k (nentries b) = Some e -> kgood (etargets e)) ->
  napply b v = inr (u, rho) -> nnest rho < nnest b.
Proof.
  destruct b as [w es]; intros HG; cbn [napply nentries] in *; rewrite nnest_es.
  destruct (aget _ es) as [e|] eqn:E; [|discriminate].
  pose proof (amax_in enest enest_unshift es e (aget_in _ _ _ E)) as He.
  pose proof (HG _ _ E) as G.
  destruct e as [h ts len p]; cbn [eapply enest etargets] in *.
  destruct (Nat.ltb _ _); [|discriminate].
  destruct (knth ts _) as [t|] eqn:Et; [|discriminate].
  pose proof (kmaxs_in tnest tnest_unshift ts t (knth_in _ _ _ G Et)) as Ht.
  destruct t as [y j|u' [r es']]; cbn in *; [discriminate|]; intros [= -> <-]; cbn in Ht; rewrite !nnest_es in *; change (S (amax enest es') <= kmaxs tnest ts) in Ht; lia.
Qed.

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

Lemma cadd_cnone c : cwf c -> cadd cnone c = c.
Proof.
  intros Hc; apply counts_ext; [apply cwf_cmap2|exact Hc|].
  intro k; rewrite cget_cadd, cget_cnone; destruct (cget c k); reflexivity.
Qed.

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

Lemma fresh_label_list {A} (ms : list (tree A)) :
  exists l, forall m, In m ms -> get (label_key l) m = None.
Proof.
  set (n := S (fold_right (fun m acc => tdepth m + acc) 0 ms)).
  assert (Hlen : String.length (long_label n) = n) by (induction n; cbn; congruence).
  exists (Some (long_label n)); intros m Hm; apply get_deep; cbn [label_key Pos.size_nat].
  rewrite size_string_key, Hlen.
  assert (tdepth m <= fold_right (fun m acc => tdepth m + acc) 0 ms).
  { clear -Hm; induction ms as [|m' ms IH]; [destruct Hm|cbn; destruct Hm as [->|Hm]; [lia|specialize (IH Hm); lia]]. }
  unfold n; lia.
Qed.

(** A count map that is the minimum over elements with keyed uses is keyed. *)
Lemma keyed_lmin {X} {BX : Based X} (L : list X) c :
  (forall e, In e L -> keyed (uses e)) -> (forall k, cget c k = lmin L k) -> cwf c -> keyed c.
Proof.
  intros HL Hc Hw k v E.
  assert (Hlab : ~ (exists l, k = label_key l) -> False).
  { intro Hn.
    assert (Hnot : forall e, In e L -> get k (c_exc (uses e)) = None)
      by (intros e He; destruct (get k (c_exc (uses e))) as [v'|] eqn:G; [exfalso; apply Hn, (HL e He k v' G)|reflexivity]).
    destruct (fresh_label_list (c_exc c :: map (fun e => c_exc (uses e)) L)) as [l' Hl'].
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

(** Which labels' inputs matter: all of them at the top, the named ones in
    a payload. *)
Definition Qnamed : option label -> bool := fun l => match l with Some _ => true | None => false end.
Definition Qof (pay : bool) : option label -> bool := if pay then Qnamed else Qall.

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
Hypothesis HkA : forall k e, aget k esa = Some e -> forall t, In t (klist (etargets e)) -> keyed (tuses t).

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
    apply keyed_tunshift; [apply keyed_wa|].
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

End Compose.
