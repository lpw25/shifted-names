(** * Tools for the canonical layered word

    Segments as lists of entries; composing two sorted segments in one
    pass ([fcomp]); a check that the labels of a segment are distinct
    ([sdistb]); a segment as a renaming followed by its terms on bound
    variables ([rents], [tfront]); carrying terms along a word by bound
    variables ([thread]); an inverse of a renaming ([sinv]).

    [Canonical] builds the canonical word with these. *)

From Stdlib Require Import Arith List Lia Bool.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Layered.
Import ListNotations.

Section Canon.

Variable F : order.
Variable ntm : nat.

(** ** Segments as lists of entries *)

Fixpoint ents (s : seg) : list (lexp * tlist * nat) :=
  match s with SNil => [] | SEnt h ts m r => (h, ts, m) :: ents r end.

Definition bent (s : seg) : tlist * nat := match sfind F LNone s with Some e => ofe e | None => (TNil, 0) end.

Definition mkseg (es : list (lexp * tlist * nat)) : option seg :=
  fold_right (fun '(h, ts, m) acc => obind acc (sset F h ts m)) (Some SNil) es.

Definition vars (l : list (lexp * nat)) : tlist := tl_of (map (fun v => NVar (fst v) (snd v)) l).
Definition bvars (l : list nat) : tlist := tl_of (map (NVar LNone) l).

Definition mem (j : nat) (l : list nat) : bool := existsb (Nat.eqb j) l.

(** ** Composing sorted segments

    [Normalise.scomp] puts each entry of the first segment applied into
    the other one by one.  When both are sorted this is a merge. *)
Definition mkent (h : lexp) (ts : tlist) (m : nat) (r : seg) : seg :=
  match trim h (rev (tl_list ts)) m with
  | ([], 0) => r
  | (rts, m') => SEnt h (tl_of (rev rts)) m' r
  end.

Definition comb (ts' : tlist) (m : nat) (tsS : tlist) (mS : nat) : tlist * nat :=
  (tcat ts' (tskip m tsS), if tlen tsS <=? m then m - tlen tsS + mS else mS).

Fixpoint smerge (S0 U cur : seg) {struct U} : option seg :=
  match U with
  | SNil => Some cur
  | SEnt h ts m r =>
      match tlapp F ntm S0 ts with
      | None => None
      | Some ts' =>
          (fix adv (cur : seg) : option seg :=
             match cur with
             | SNil => let '(x, k) := comb ts' m TNil 0 in option_map (mkent h x k) (smerge S0 r SNil)
             | SEnt g tsg mg rc =>
                 match lcmp F h g with
                 | Some Lt => let '(x, k) := comb ts' m TNil 0 in option_map (mkent h x k) (smerge S0 r cur)
                 | Some Eq => let '(x, k) := comb ts' m tsg mg in option_map (mkent h x k) (smerge S0 r rc)
                 | Some Gt => option_map (SEnt g tsg mg) (adv rc)
                 | None => None
                 end
             end) cur
      end
  end.

Fixpoint sortb (s : seg) : bool :=
  match s with
  | SNil => true
  | SEnt h _ _ r =>
      match r with
      | SNil => true
      | SEnt g _ _ _ => match lcmp F h g with Some Lt => sortb r | _ => false end
      end
  end.

Definition fcomp (S U : seg) : option seg :=
  if sortb S && sortb U then smerge S U S else scomp F ntm S U.

(** ** Distinct labels, checked

    The segments computed below are compared with what they replace by
    composing; for that their entries must have distinct labels, which
    holds when each label is known to be below the ones after it. *)
Fixpoint tdistb (t : ntgt) : bool :=
  match t with NVar _ _ => true | NBind _ w _ => wdistb w end
with tldistb (ts : tlist) : bool :=
  match ts with TNil => true | TCons t r => tdistb t && tldistb r end
with sdistb (s : seg) : bool :=
  match s with
  | SNil => true
  | SEnt h ts _ r =>
      match r with
      | SNil => tldistb ts
      | SEnt g _ _ _ => match lcmp F h g with Some Lt => tldistb ts && sdistb r | _ => false end
      end
  end
with wdistb (w : word) : bool :=
  match w with WEnd s => sdistb s | WAtom s _ _ w' => sdistb s && wdistb w' end.

(** The order on variables: by label, then index. *)
Definition vless (a b : lexp * nat) : bool :=
  match lcmp F (fst a) (fst b) with Some Lt => true | Some Eq => snd a <? snd b | _ => false end.

Definition vmin (l : list (lexp * nat)) : option (lexp * nat) :=
  fold_right (fun v acc => match acc with None => Some v | Some w => if vless v w then Some v else Some w end) None l.

Fixpoint findix (t : ntgt) (ts : tlist) (k : nat) : list nat :=
  match ts with TNil => [] | TCons t' r => (if ntgt_eqb t t' then [k] else []) ++ findix t r (S k) end.

(** The named inputs of [s1] with the target [t]. *)
Definition named_srcs (s1 : seg) (t : ntgt) : list (lexp * nat) :=
  flat_map (fun '(h, ts, m) => match h with LNone => [] | _ => map (fun k => (h, k)) (findix t ts 0) end) (ents s1)
  ++ match t with
     | NVar LNone _ => []
     | NVar g i =>
         match sfind F g s1 with
         | Some (Some (ts, m)) => if m <=? i then [(g, i - m + tlen ts)] else []
         | Some None => [(g, i)]
         | None => []
         end
     | _ => []
     end.

Definition veqb (a b : lexp * nat) : bool := lexp_eqb (fst a) (fst b) && Nat.eqb (snd a) (snd b).

(** The inputs that may not be their own representative. *)
Definition cands (s1 : seg) : list (lexp * nat) :=
  flat_map (fun '(h, ts, m) => map (fun k => (h, k)) (seq 0 (tlen ts))) (ents s1)
  ++ flat_map (fun t => match t with
                        | NVar g i => match sfind F g s1 with
                                      | Some (Some (ts, m)) => if m <=? i then [(g, i - m + tlen ts)] else []
                                      | Some None => [(g, i)]
                                      | None => []
                                      end
                        | _ => [] end) (stargets s1).

(** Bound variables below the default region, in the order they are
    first used. *)
Fixpoint nodup_nat (l : list nat) (seen : list nat) : list nat :=
  match l with [] => [] | x :: r => if mem x seen then nodup_nat r seen else x :: nodup_nat r (x :: seen) end.

Fixpoint index_of (x : nat) (l : list nat) (k : nat) : nat :=
  match l with [] => k | y :: r => if Nat.eqb x y then k else index_of x r (S k) end.

(** The terms of a segment replaced by the bound variables [0 ..], the
    other bound targets moved up. *)
Fixpoint rterms (ts : tlist) (k : nat) : tlist * list ntgt :=
  match ts with
  | TNil => (TNil, [])
  | TCons (NBind u w b) r => let '(r', T) := rterms r (S k) in (TCons (NVar LNone k) r', NBind u w b :: T)
  | TCons t r => let '(r', T) := rterms r k in (TCons t r', T)
  end.

Fixpoint rents (es : list (lexp * tlist * nat)) (k : nat) : list (lexp * tlist * nat) * list ntgt :=
  match es with
  | [] => ([], [])
  | (h, ts, m) :: r =>
      let '(ts', T) := rterms ts k in
      let '(r', T') := rents r (k + List.length T) in
      ((h, ts', m) :: r', T ++ T')
  end.

Definition nterms (s : seg) : nat := List.length (filter is_term (stargets s)).

Definition tfront (T : list ntgt) (s : seg) : option seg :=
  fold_right (fun t acc => obind acc (sfront F LNone t)) (Some s) T.

Definition is_pure (t : ntgt) : bool := match t with NBind u (WEnd SNil) None => u <? ntm | _ => false end.

Fixpoint thread (j : nat) (T : list ntgt) (K : lword) : option lword :=
  match j, K with
  | 1, LS s1 :: K' => option_map (fun x => LS x :: K') (tfront T s1)
  | S j', LS s1 :: K' =>
      match slifts F ntm (List.length T) s1, thread j' T K' with
      | Some a, Some b => Some (LS a :: b)
      | _, _ => None
      end
  | _, _ => None
  end.

Definition named_term (s : seg) : bool := has_terms (sdrop_none s).

(** ** Going behind the first layer *)

(** An inverse of a renaming of named variables; named outputs that
    nothing is sent to come back from fresh bound variables [R]. *)
Definition sinv (sg : seg) : option (seg * list ntgt) :=
  fold_right (fun '(g, ts, m) acc =>
    obind acc (fun '(a, R) =>
      let pre := map (fun i => (i, vmin (named_srcs sg (NVar g i)))) (seq 0 m) in
      let miss := filter (fun p => match snd p with None => true | _ => false end) pre in
      let tg := fun p => match snd p with
                         | Some (h, k) => NVar h k
                         | None => NVar LNone (List.length R + index_of (fst p) (map fst miss) 0)
                         end in
      match sset F g (tl_of (map tg pre)) (tlen ts) a with
      | Some a' => Some (a', R ++ map (fun p => NVar g (fst p)) miss)
      | None => None
      end)) (Some (SNil, [])) (ents sg).

Definition lcmp3 (a b : lexp) : comparison := match lcmp F a b with Some c => c | None => Eq end.

Fixpoint linsert (g : lexp) (l : list lexp) : list lexp :=
  match l with
  | [] => [g]
  | h :: r => match lcmp F g h with Some Lt => g :: l | Some Eq => l | _ => h :: linsert g r end
  end.

Definition wlabs (l : lword) : list lexp :=
  fold_right (fun x acc =>
    match x with
    | LS sg => fold_right (fun '(g, _, _) a => match g with LNone => a | _ => linsert g a end) acc (ents sg)
    | _ => acc
    end) [] l.

Definition wbound (l : lword) : nat :=
  fold_right (fun x acc => match x with LS sg => List.length (stargets sg) + acc | _ => acc end) 2 l.

(** ** In front of an atom

    A segment with terms in front of a lifted atom: the variables it
    sends around the atom are put in canonical form as above, among the
    variables the lifts pass around, and a bound variable that nothing
    reaches is one lift less.  The result is checked by composing. *)
Definition lcn (L : list (lexp * nat)) (g : lexp) : nat := match lcnt F g L with Some c => c | None => 0 end.

Definition setb (L : list (lexp * nat)) (c : nat) : list (lexp * nat) :=
  filter (fun p => negb (lexp_eqb (fst p) LNone)) L ++ match c with 0 => [] | _ => [(LNone, c)] end.

End Canon.

(** ** Soundness *)

Section Sound.

Context {T : Type}.
Variable lenv : list label.
Variable tenv : list T.
Variable aenv : list (radj T).
Variable penv : list (rpadj T).
Variable F : order.
Hypothesis HF : facts_ok lenv F.
Variable ntm : nat.
Hypothesis Hntm : ntm <= List.length tenv.

Local Notation lden := (lden lenv).
Local Notation tden := (tden lenv tenv aenv penv).
Local Notation sden := (sden lenv tenv aenv penv).
Local Notation wden := (wden lenv tenv aenv penv).
Local Notation sdistd := (sdistd lenv).
Local Notation tdist := (tdist lenv).
Local Notation tldist := (tldist lenv).
Local Notation wdist := (wdist lenv).
Local Notation lwden := (lwden lenv tenv aenv penv).
Local Notation lwdist := (lwdist lenv).


(** *** The merge *)

Local Notation esem := (esem lenv tenv aenv penv).

Fixpoint below (l : option label) (s : seg) : Prop :=
  match s with SNil => True | SEnt h _ _ r => olabel_lt l (lden h) /\ below l r end.

Fixpoint sorted (s : seg) : Prop :=
  match s with SNil => True | SEnt h _ _ r => below (lden h) r /\ sorted r end.

Lemma below_get l s : below l s -> sget lenv l s = None.
Proof.
  induction s as [|h ts m r IH] using seg_spine; [reflexivity|]; intros [H1 H2]; cbn [sget].
  destruct (label_eqb (lden h) l) eqn:E; [apply label_eqb_eq in E; subst; destruct (olabel_lt_irrefl _ H1)|exact (IH H2)].
Qed.

Lemma below_trans a b s : olabel_lt a b -> below b s -> below a s.
Proof.
  intros Hab; induction s as [|h ts m r IH] using seg_spine; [exact (fun H => H)|]; intros [H1 H2].
  split; [exact (olabel_lt_trans _ _ _ Hab H1)|exact (IH H2)].
Qed.

Lemma sortb_sound s : sortb F s = true -> sorted s.
Proof.
  induction s as [|h ts m r IH] using seg_spine; [intros _; exact I|]; cbn [sortb].
  destruct r as [|g tsg mg r']; [intros _; split; exact I|].
  destruct (lcmp F h g) as [[| |]|] eqn:E; try discriminate; intros H.
  pose proof (lcmp_sound lenv F HF _ _ _ E) as Hlt; cbn in Hlt.
  destruct (IH H) as [Hb Hs]; split; [|exact (conj Hb Hs)].
  split; [exact Hlt|exact (below_trans _ _ _ Hlt Hb)].
Qed.

Lemma distb_sound :
  (forall t, tdistb F t = true -> tdist t) /\ (forall ts, tldistb F ts = true -> tldist ts)
  /\ (forall s, sdistb F s = true -> sdistd s /\ sorted s) /\ (forall w, wdistb F w = true -> wdist w).
Proof.
  apply nf_mind.
  - intros h i _; exact I.
  - intros u w IH b H; exact (IH H).
  - intros _; exact I.
  - intros t IHt r IHr H; cbn [tldistb] in H; apply andb_true_iff in H as [H1 H2]; split; [exact (IHt H1)|exact (IHr H2)].
  - intros _; split; exact I.
  - intros h ts IHts m r IHr H; cbn [sdistb] in H.
    destruct r as [|g tsg mg r'].
    + split; [exact (conj eq_refl (conj (IHts H) I))|split; exact I].
    + destruct (lcmp F h g) as [[| |]|] eqn:E; try discriminate.
      apply andb_true_iff in H as [H1 H2]; destruct (IHr H2) as [Hd [Hb Hs]].
      pose proof (lcmp_sound lenv F HF _ _ _ E) as Hlt; cbn in Hlt.
      assert (Hbl : below (lden h) (SEnt g tsg mg r')) by (split; [exact Hlt|exact (below_trans _ _ _ Hlt Hb)]).
      split; [exact (conj (below_get _ _ Hbl) (conj (IHts H1) Hd))|exact (conj Hbl (conj Hb Hs))].
  - intros s IH H; exact (proj1 (IH H)).
  - intros s IHs L a w IHw H; cbn [wdistb] in H; apply andb_true_iff in H as [H1 H2]; split; [exact (proj1 (IHs H1))|exact (IHw H2)].
Qed.

Lemma sdistb_sound s : sdistb F s = true -> sdistd s.
Proof. intros H; exact (proj1 (proj1 (proj2 (proj2 distb_sound)) s H)). Qed.

Lemma mkent_spec h ts m r : below (lden h) r ->
  (forall l j, esem l (sget lenv l (mkent h ts m r)) j
               = if label_eqb (lden h) l then esem l (Some (ts, m)) j else esem l (sget lenv l r) j)
  /\ (forall b, olabel_lt b (lden h) -> below b r -> below b (mkent h ts m r))
  /\ (sorted r -> sorted (mkent h ts m r))
  /\ (sdistd r -> tldist ts -> sdistd (mkent h ts m r)).
Proof.
  intros Hb; unfold mkent; destruct (trim h (rev (tl_list ts)) m) as [rts m'] eqn:Et.
  assert (Hsem : forall j, esem (lden h) (Some (ts, m)) j = esem (lden h) (Some (tl_of (rev rts), m')) j).
  { intros j; rewrite !(esem_lsem lenv tenv aenv penv), tl_list_of; rewrite <- (rev_involutive (tl_list ts)) at 1.
    apply (trim_sound lenv tenv aenv penv ntm Hntm h _ _ _ _ Et). }
  assert (Hcons : (forall l j, esem l (sget lenv l (SEnt h (tl_of (rev rts)) m' r)) j
                               = if label_eqb (lden h) l then esem l (Some (ts, m)) j else esem l (sget lenv l r) j)
                  /\ (forall b, olabel_lt b (lden h) -> below b r -> below b (SEnt h (tl_of (rev rts)) m' r))
                  /\ (sorted r -> sorted (SEnt h (tl_of (rev rts)) m' r))
                  /\ (sdistd r -> tldist ts -> sdistd (SEnt h (tl_of (rev rts)) m' r))).
  { refine (conj _ (conj (fun b H1 H2 => conj H1 H2) (conj (fun H => conj Hb H) _))).
    - intros l j; cbn [sget]; destruct (label_eqb_spec (lden h) l) as [<-|]; [symmetry; apply Hsem|reflexivity].
    - intros Hr Hts; refine (conj (below_get _ _ Hb) (conj _ Hr)).
      apply (proj2 (tldist_iff lenv _)); intros t Ht; rewrite tl_list_of in Ht; apply in_rev in Ht.
      apply (proj1 (tldist_iff lenv ts) Hts); apply in_rev; exact (trim_tgts h _ _ _ _ Et t Ht). }
  destruct rts as [|x rts]; [destruct m' as [|m']|]; try exact Hcons.
  refine (conj _ (conj (fun b _ H => H) (conj (fun H => H) (fun H _ => H)))).
  intros l j; destruct (label_eqb_spec (lden h) l) as [<-|]; [|reflexivity].
  rewrite Hsem, (below_get _ _ Hb); cbn [rev tl_of]; first [apply (esem_none lenv tenv aenv penv ntm Hntm)|symmetry; apply (esem_none lenv tenv aenv penv ntm Hntm)].
Qed.

Section Merge.

Variable S0 : seg.
Hypothesis HS0 : sdistd S0.

Lemma ent_comp h ts ts' m tsS mS :
  tlen ts' = tlen ts ->
  (forall j, j < tlen ts -> rtarget_result (tden (tnth ts' j)) = cres (sden S0) (rtarget_result (tden (tnth ts j)))) ->
  ofe (sget lenv (lden h) S0) = (tsS, mS) ->
  forall j, esem (lden h) (Some (comb ts' m tsS mS)) j = cres (sden S0) (esem (lden h) (Some (ts, m)) j).
Proof.
  intros Hlen Hts0 Eo j; pose proof (sdistd_sdist lenv _ HS0) as HS'; unfold comb.
  rewrite !(esem_lsem lenv tenv aenv penv); unfold lsem; rewrite <- !tlen_list, <- !tnth_list, tlen_tcat, tlen_tskip, Hlen.
  destruct (Nat.ltb_spec j (tlen ts)) as [Hj|Hj].
  + rewrite (proj2 (Nat.ltb_lt _ _)) by lia; rewrite tnth_tcat, Hlen, (proj2 (Nat.ltb_lt _ _)) by exact Hj.
    apply Hts0, Hj.
  + cbn [cres]; rewrite (rapply_sden lenv tenv aenv penv) by exact HS'; cbn [v_label v_index].
    rewrite <- (esem_ofe lenv tenv aenv penv ntm Hntm), Eo.
    cbn [Normalise.esem]; rewrite tnth_tcat, Hlen, (proj2 (Nat.ltb_ge j (tlen ts)) Hj), tnth_tskip.
    destruct (Nat.ltb_spec (j - tlen ts + m) (tlen tsS)) as [Hk|Hk].
    * rewrite (proj2 (Nat.ltb_lt j (tlen ts + (tlen tsS - m)))) by lia; do 3 f_equal; lia.
    * rewrite (proj2 (Nat.ltb_ge j (tlen ts + (tlen tsS - m)))) by lia; do 2 f_equal.
      destruct (Nat.leb_spec (tlen tsS) m); lia.
Qed.

Lemma comb_dist ts' m tsS mS : tldist ts' -> tldist tsS -> tldist (fst (comb ts' m tsS mS)).
Proof.
  intros H1 H2; cbn [comb fst]; apply (proj2 (tldist_iff lenv _)); intros t Ht; rewrite tcat_list in Ht.
  apply in_app_or in Ht as [Ht|Ht]; [exact (proj1 (tldist_iff lenv ts') H1 t Ht)|].
  exact (proj1 (tldist_iff lenv tsS) H2 t (tskip_list_in _ _ _ Ht)).
Qed.

Definition mspec (U cur R : seg) : Prop :=
  sdistd R /\ sorted R /\ (forall b, below b U -> below b cur -> below b R)
  /\ forall l j, esem l (sget lenv l R) j
                 = match sget lenv l U with
                   | Some e => cres (sden S0) (esem l (Some e) j)
                   | None => esem l (sget lenv l cur) j
                   end.

Lemma smerge_spec U : forall cur R, sdistd U -> sorted U -> sdistd cur -> sorted cur ->
  (forall l, sget lenv l U <> None -> sget lenv l cur = sget lenv l S0) ->
  smerge F ntm S0 U cur = Some R -> mspec U cur R.
Proof.
  induction U as [|h ts m r IHU] using seg_spine; intros cur R HU HsU.
  { intros Hc HsC _ H; injection H as <-; refine (conj Hc (conj HsC (conj (fun b _ H => H) _))); intros l j; reflexivity. }
  destruct HU as [Hnr [Hts Hr]]; destruct HsU as [Hbr Hsr]; cbn [smerge].
  destruct (tlapp F ntm S0 ts) as [ts'|] eqn:Et; [|discriminate].
  destruct (proj1 (proj2 (comp_sound lenv tenv aenv penv F HF ntm Hntm S0 HS0)) ts ts' Hts Et) as [Hts' [Hlen Hts0]].
  assert (Hin : forall l, sget lenv l r <> None -> sget lenv l (SEnt h ts m r) <> None).
  { intros l H; cbn [sget]; destruct (label_eqb (lden h) l); [discriminate|exact H]. }
  assert (Hne : forall l, sget lenv l r <> None -> label_eqb (lden h) l = false).
  { intros l H; destruct (label_eqb (lden h) l) eqn:E; [|reflexivity].
    apply label_eqb_eq in E; subst l; rewrite (below_get _ _ Hbr) in H; contradiction. }
  (* putting the entry of [h], combined with the entry of [S0] *)
  assert (Hput : forall cur tsS mS cur' R0, ofe (sget lenv (lden h) S0) = (tsS, mS) -> tldist tsS ->
            below (lden h) cur' -> (forall b, below b cur -> below b cur') ->
            (forall l, label_eqb (lden h) l = false -> sget lenv l (SEnt h ts m r) = None -> sget lenv l cur' = sget lenv l cur) ->
            mspec r cur' R0 ->
            mspec (SEnt h ts m r) cur (mkent h (fst (comb ts' m tsS mS)) (snd (comb ts' m tsS mS)) R0)).
  { intros cur0 tsS mS cur' R0 Eo HtsS Hbc Hmono Hsame [Hd0 [Hs0 [Hb0 Hsem0]]].
    destruct (mkent_spec h (fst (comb ts' m tsS mS)) (snd (comb ts' m tsS mS)) R0 (Hb0 _ Hbr Hbc)) as [A [B [C D]]].
    refine (conj (D Hd0 (comb_dist _ _ _ _ Hts' HtsS)) (conj (C Hs0) (conj _ _))).
    - intros b [Hb1 Hb2] Hb3; exact (B b Hb1 (Hb0 b Hb2 (Hmono b Hb3))).
    - intros l j; rewrite A; cbn [sget]; destruct (label_eqb (lden h) l) eqn:El.
      + apply label_eqb_eq in El; subst l.
        rewrite <- surjective_pairing; exact (ent_comp h ts ts' m tsS mS Hlen Hts0 Eo j).
      + rewrite Hsem0; destruct (sget lenv l r) as [e|] eqn:Er; [reflexivity|].
        rewrite (Hsame l El); [reflexivity|]; cbn [sget]; rewrite El; exact Er. }
  revert R; induction cur as [|g tsg mg rc IHc] using seg_spine; intros R Hc HsC Hcur;
    (assert (Hh : sget lenv (lden h) S0 = sget lenv (lden h) _)
       by (symmetry; apply Hcur; cbn [sget]; rewrite label_eqb_refl; discriminate)).
  - unfold comb; destruct (smerge F ntm S0 r SNil) as [R0|] eqn:E0; [|discriminate]; intros H; injection H as <-.
    refine (Hput SNil TNil 0 SNil R0 _ I I (fun b H => H) (fun l _ _ => eq_refl) _); [rewrite Hh; reflexivity|].
    exact (IHU SNil R0 Hr Hsr I I (fun l H => Hcur l (Hin l H)) E0).
  - destruct Hc as [Hng [Htsg Hrc]]; destruct HsC as [Hbg Hsrc].
    destruct (lcmp F h g) as [[| |]|] eqn:Ec; [| | |discriminate].
    + pose proof (lcmp_sound lenv F HF _ _ _ Ec) as E; cbn in E; subst g.
      unfold comb; destruct (smerge F ntm S0 r rc) as [R0|] eqn:E0; [|discriminate]; intros H; injection H as <-.
      refine (Hput (SEnt h tsg mg rc) tsg mg rc R0 _ Htsg Hbg (fun b (H : below b (SEnt h tsg mg rc)) => proj2 H) _ _).
      * rewrite Hh; cbn [sget]; rewrite label_eqb_refl; reflexivity.
      * intros l El _; cbn [sget]; rewrite El; reflexivity.
      * refine (IHU rc R0 Hr Hsr Hrc Hsrc _ E0); intros l H.
        rewrite <- (Hcur l (Hin l H)); cbn [sget]; rewrite (Hne l H); reflexivity.
    + pose proof (lcmp_sound lenv F HF _ _ _ Ec) as Hlt; cbn in Hlt.
      assert (Hbc : below (lden h) (SEnt g tsg mg rc)) by (split; [exact Hlt|exact (below_trans _ _ _ Hlt Hbg)]).
      unfold comb; destruct (smerge F ntm S0 r (SEnt g tsg mg rc)) as [R0|] eqn:E0; [|discriminate]; intros H; injection H as <-.
      refine (Hput (SEnt g tsg mg rc) TNil 0 (SEnt g tsg mg rc) R0 _ I Hbc (fun b H => H) (fun l _ _ => eq_refl) _).
      * rewrite Hh, (below_get _ _ Hbc); reflexivity.
      * exact (IHU (SEnt g tsg mg rc) R0 Hr Hsr (conj Hng (conj Htsg Hrc)) (conj Hbg Hsrc) (fun l H => Hcur l (Hin l H)) E0).
    + pose proof (lcmp_sound lenv F HF _ _ _ Ec) as Hgt; cbn in Hgt.
      assert (HbU : below (lden g) (SEnt h ts m r)) by (split; [exact Hgt|exact (below_trans _ _ _ Hgt Hbr)]).
      assert (Hl : forall l, sget lenv l (SEnt h ts m r) <> None -> label_eqb (lden g) l = false).
      { intros l H; destruct (label_eqb (lden g) l) eqn:E; [|reflexivity].
        apply label_eqb_eq in E; subst l; rewrite (below_get _ _ HbU) in H; contradiction. }
      match goal with |- option_map _ ?x = _ -> _ => destruct x as [R1|] eqn:E1; [|discriminate] end.
      intros H; injection H as <-.
      assert (Hcur' : forall l, sget lenv l (SEnt h ts m r) <> None -> sget lenv l rc = sget lenv l S0).
      { intros l H; rewrite <- (Hcur l H); cbn [sget]; rewrite (Hl l H); reflexivity. }
      destruct (IHc R1 Hrc Hsrc Hcur' eq_refl) as [Hd1 [Hs1 [Hb1 Hsem1]]].
      pose proof (Hb1 _ HbU Hbg) as HbR.
      refine (conj (conj (below_get _ _ HbR) (conj Htsg Hd1)) (conj (conj HbR Hs1) (conj _ _))).
      * intros b HbUb [Hb2 Hb3]; exact (conj Hb2 (Hb1 b HbUb Hb3)).
      * intros l j; change (sget lenv l (SEnt g tsg mg R1)) with (if label_eqb (lden g) l then Some (tsg, mg) else sget lenv l R1).
        change (sget lenv l (SEnt g tsg mg rc)) with (if label_eqb (lden g) l then Some (tsg, mg) else sget lenv l rc).
        destruct (label_eqb (lden g) l) eqn:El; [|apply Hsem1].
        apply label_eqb_eq in El; subst l; rewrite (below_get _ _ HbU); reflexivity.
Qed.

Lemma smerge_sound U R : sdistd U -> sorted U -> sorted S0 -> smerge F ntm S0 U S0 = Some R ->
  sdistd R /\ sden R = rcompose (sden S0) (sden U).
Proof.
  intros HU HsU HsS H; destruct (smerge_spec U S0 R HU HsU HS0 HsS (fun _ _ => eq_refl) H) as [Hd [_ [_ Hsem]]].
  split; [exact Hd|]; apply rextensionality; intros [l j].
  rewrite rapply_compose_cres, !(rapply_sden lenv tenv aenv penv) by (apply sdistd_sdist; assumption).
  cbn [v_label v_index]; rewrite Hsem; destruct (sget lenv l U) as [e|]; [reflexivity|].
  cbn [Normalise.esem cres]; rewrite (rapply_sden lenv tenv aenv penv) by (apply sdistd_sdist; exact HS0); reflexivity.
Qed.

End Merge.

Lemma fcomp_sound A U R : sdistd A -> sdistd U -> fcomp F ntm A U = Some R ->
  sdistd R /\ sden R = rcompose (sden A) (sden U).
Proof.
  intros HA HU; unfold fcomp; destruct (sortb F A && sortb F U) eqn:E.
  - apply andb_true_iff in E as [E1 E2].
    exact (smerge_sound A HA U R HU (sortb_sound _ E2) (sortb_sound _ E1)).
  - exact (scomp_sound lenv tenv aenv penv F HF ntm Hntm A U R HA HU).
Qed.

(** Entries of the bound label in front of an adjustment. *)
Definition pins (ts : list (rtarget T)) (X : radj T) : radj T := fold_right (rpush_inner None) X ts.

Lemma pins_compose_l a ts X : rcompose a (pins ts X) = pins (map (rapply_target a) ts) (rcompose a X).
Proof. induction ts as [|t ts IH]; cbn [pins fold_right map]; [reflexivity|]; rewrite rcompose_push_inner_r; fold (pins ts X); rewrite IH; reflexivity. Qed.

Lemma pins_compose_r ts X B : pins ts (rcompose X B) = rcompose (pins ts X) (lifted (List.length ts) B).
Proof.
  induction ts as [|t ts IH]; cbn [pins fold_right length]; [reflexivity|].
  fold (pins ts (rcompose X B)); fold (pins ts X); rewrite IH, (rpush_inner_compose tenv ntm Hntm); reflexivity.
Qed.

Lemma tfront_sound Ts : forall s s', sdistd s -> Forall tdist Ts -> tfront F Ts s = Some s' ->
  sdistd s' /\ sden s' = pins (map tden Ts) (sden s).
Proof.
  induction Ts as [|t Ts IH]; intros s s' Hs HT; cbn [tfront fold_right].
  - intros H; injection H as <-; split; [exact Hs|reflexivity].
  - inversion HT as [|? ? Ht HT']; subst.
    fold (tfront F Ts s); destruct (tfront F Ts s) as [s0|] eqn:E; [|discriminate]; cbn [obind]; intros H.
    destruct (IH s s0 Hs HT' E) as [Hd0 D0].
    destruct (sfront_sound lenv tenv aenv penv F HF ntm Hntm LNone t s0 s' Hd0 Ht H) as [Hd D].
    split; [exact Hd|]; rewrite D, D0; reflexivity.
Qed.

Lemma thread_0 Ts K : thread F ntm 0 Ts K = None.
Proof. destruct K as [|[?|? ?] ?]; reflexivity. Qed.

Lemma thread_SS j Ts s1 K :
  thread F ntm (S (S j)) Ts (LS s1 :: K)
  = match slifts F ntm (List.length Ts) s1, thread F ntm (S j) Ts K with
    | Some a, Some b => Some (LS a :: b)
    | _, _ => None
    end.
Proof. reflexivity. Qed.

Lemma thread_nil j Ts : thread F ntm j Ts [] = None.
Proof. destruct j as [|[|j]]; reflexivity. Qed.

Lemma thread_atom j Ts L a K : thread F ntm j Ts (LA L a :: K) = None.
Proof. destruct j as [|[|j]]; reflexivity. Qed.

Lemma thread_sound j : forall Ts K Kp, lwdist K -> Forall tdist Ts -> thread F ntm j Ts K = Some Kp ->
  lwdist Kp /\ lwden Kp = pins (map (fun t => rapply_target (lwden (skipn j K)) (tden t)) Ts) (lwden K).
Proof.
  induction j as [|j IH]; intros Ts K Kp HK HT.
  { rewrite thread_0; discriminate. }
  destruct K as [|[s1|L a] K']; [rewrite thread_nil; discriminate| |rewrite thread_atom; discriminate].
  inversion HK as [|? ? Hs1 HK']; subst.
  destruct j as [|j].
  - cbn [thread]; destruct (tfront F Ts s1) as [x|] eqn:E; [|discriminate]; intros H; injection H as <-.
    destruct (tfront_sound Ts s1 x Hs1 HT E) as [Hx Dx]; split; [constructor; assumption|].
    cbn [Layered.lwden skipn]; rewrite Dx, pins_compose_l, map_map; reflexivity.
  - rewrite thread_SS; destruct (slifts F ntm (List.length Ts) s1) as [a|] eqn:Ea; [|discriminate].
    destruct (thread F ntm (S j) Ts K') as [b|] eqn:Eb; [|discriminate]; intros H; injection H as <-.
    destruct (slifts_sound lenv tenv aenv penv F HF ntm Hntm _ s1 a Hs1 Ea) as [Ha Da].
    destruct (IH Ts K' b HK' HT Eb) as [Hb Db]; split; [constructor; assumption|].
    cbn [Layered.lwden]; rewrite Db, Da.
    change (skipn (S (S j)) (LS s1 :: K')) with (skipn (S j) K').
    rewrite pins_compose_r, length_map; reflexivity.
Qed.

Lemma pure_target (A B : radj T) t : is_pure ntm t = true ->
  (forall v, v_label v <> None -> rapply A v = rapply B v) ->
  tdist t /\ rapply_target A (tden t) = rapply_target B (tden t).
Proof.
  destruct t as [|u [[|]|] [|]]; try discriminate; cbn [is_pure]; intros Hu Hn; apply Nat.ltb_lt in Hu.
  split; [exact I|].
  destruct (nth_error tenv u) as [y|] eqn:Ey; [|apply nth_error_None in Ey; lia].
  rewrite (tden_bind lenv tenv aenv penv u (WEnd SNil) None y Ey); cbn [rapply_target bden].
  rewrite (wden_id lenv tenv aenv penv), rpcompose_identity; f_equal; apply rpcompose_named, Hn.
Qed.

End Sound.
