(** * Classes of variables in a canonical word

    In a word in the normal form [LayeredUnique.lnf], two variables mean
    the same exactly when they reach the same target of the first
    segment with terms ([follow1_char]).  The canonical word uses this
    to send each variable to the least variable that means the same. *)

From Stdlib Require Import Arith List Lia Bool Sorted.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Unique Normal Layered LayeredUnique Order
  Canon Retarget LFree CanonF.
Import ListNotations.

Section Follow1.

Variable F : order.

(** Follow [h₍ᵢ₎] through renamings and atoms to the first segment with
    terms, and take its target there. *)
Fixpoint follow1 (l : lword) (h : lexp) (i : nat) : option desc :=
  match l with
  | [] => Some (DV h i)
  | LS s :: r =>
      match seg_tgt F s h i with
      | Some t =>
          if has_terms s then Some (DT t (List.length r))
          else match t with NVar g j => follow1 r g j | NBind _ _ _ => None end
      | None => None
      end
  | LA L a :: r =>
      match lcnt F h L with
      | Some c => if i <? c then follow1 r h i else Some (DS a h (i - c) (List.length r))
      | None => None
      end
  end.

End Follow1.

Section Char.

Variable lenv : list label.
Variable labs : list lexp.
Hypothesis Hinj : forall h h', In h labs -> In h' labs -> lden lenv h = lden lenv h' -> h = h'.
Variable ntm : nat.
Variable F : order.
Hypothesis HF : facts_ok lenv F.

Local Notation lden := (lden lenv).
Local Notation R := (R lenv).
Local Notation fs := (fs lenv).
Local Notation ft := (ft lenv).
Local Notation sres := (sres lenv).
Local Notation sp1 := (sp1 lenv labs ntm).
Local Notation tp1 := (tp1 labs ntm).
Local Notation lw1 := (lw1 lenv labs ntm).
Local Notation lnf := (lnf lenv labs gtP).
Local Notation segok := (segok lenv labs gtP).

Lemma follow1_lt l : forall h i d, follow1 F l h i = Some d ->
  match d with DV _ _ => True | DT _ e => e < List.length l | DS _ _ _ e => e < List.length l end.
Proof.
  induction l as [|[s|L a] r IH]; intros h i d; cbn [follow1].
  - intros E; injection E as <-; exact I.
  - destruct (seg_tgt F s h i) as [t|]; [|discriminate]; destruct (has_terms s).
    + intros E; injection E as <-; cbn; lia.
    + destruct t as [g j|]; [|discriminate]; intros E; specialize (IH _ _ _ E); destruct d; cbn in *; try lia; exact I.
  - destruct (lcnt F h L) as [c|]; [|discriminate]; destruct (i <? c).
    + intros E; specialize (IH _ _ _ E); destruct d; cbn in *; try lia; exact I.
    + intros E; injection E as <-; cbn; lia.
Qed.

(** Two targets of a segment with terms in normal form mean the same
    after the rest only if they are the same. *)
Lemma tgt_char s r t t' : segok s r ->
  (exists x, sres s x = tres lenv t) -> (exists x', sres s x' = tres lenv t') -> tp1 t -> tp1 t' ->
  (feq (ft t (R r)) (ft t' (R r)) <-> t = t').
Proof.
  intros HS [x Ex] [x' Ex'] Ht Ht'; split; [|intros <-; apply feq_refl].
  destruct HS as [_ _ Hord _ Hroute _ _ Hbinj _].
  assert (Tv : forall g j u w b, tp1 (NBind u w b) -> ~ feq (R r (mk_rvar (lden g) j)) (ft (NBind u w b) (R r))).
  { intros g j u w b [-> [-> _]] Fe; cbn [ft] in Fe.
    destruct (R r (mk_rvar (lden g) j)) as [|u0 b0 k0|] eqn:E0; cbn [feq] in Fe; try contradiction.
    destruct Fe as [_ [-> Fk]].
    apply (gtP_irrefl (R r) k0); [|exact (Hord _ _ _ _ E0)].
    intros z Hz; apply feq_sym; refine (feq_trans _ _ _ (Fk z (fun _ => Hz)) _); cbn [fw]; rewrite (fs_nil lenv labs); apply feq_refl. }
  destruct t as [g j|u w b], t' as [g' j'|u' w' b']; cbn [ft].
  - intros Fe; cbn [tres] in Ex, Ex'.
    destruct (Hroute _ _ Ex) as [Rn Rb]; destruct (Hroute _ _ Ex') as [Rn' Rb'].
    set (y := mk_rvar (lden g) j) in *; set (y' := mk_rvar (lden g') j') in *.
    assert (Ey : y = y').
    { destruct (named_or_bound y) as [Hy|Hy], (named_or_bound y') as [Hy'|Hy'].
      - destruct (vlt_total y y') as [Hl|[E|Hl]]; [|exact E|].
        + destruct (Rn' Hy' y Hy Fe Hl).
        + destruct (Rn Hy y' Hy' (feq_sym _ _ Fe) Hl).
      - destruct (Rb' Hy' y Hy Fe).
      - destruct (Rb Hy y' Hy' (feq_sym _ _ Fe)).
      - exact (Hbinj _ _ Hy Hy' Fe). }
    unfold y, y' in Ey; injection Ey as Eg ->; rewrite (Hinj g g' Ht Ht' Eg); reflexivity.
  - intros Fe; destruct (Tv g j u' w' b' Ht' Fe).
  - intros Fe; destruct (Tv g' j' u w b Ht (feq_sym _ _ Fe)).
  - destruct Ht as [-> [-> _]], Ht' as [-> [-> _]]; cbn [feq]; intros [-> _]; reflexivity.
Qed.

Lemma stuck_mix r L a y z : ~ feq (R r y) (FStuck a z (fun y => R r (shiftL lenv L y))).
Proof.
  intros Fe; destruct (R r y) as [|u b k|a0 z0 k0] eqn:E; cbn [feq] in Fe; try contradiction.
  destruct Fe as [_ [_ Fk]].
  destruct (nstuck_R lenv r y a0 z0 k0 E) as [d [Hd Hk]].
  pose proof (deep_shift lenv _ L _ (deep_R lenv r)) as Hk'.
  pose proof (deep_unique d (natl r) k0 _ Hk Hk' (fun i => Fk (mk_rvar lbig i))); lia.
Qed.

Theorem follow1_char W : lnf W -> lw1 W -> forall h i h' i' d d', In h labs -> In h' labs ->
  follow1 F W h i = Some d -> follow1 F W h' i' = Some d' ->
  (feq (R W (mk_rvar (lden h) i)) (R W (mk_rvar (lden h') i')) <-> d = d').
Proof.
  induction W as [|[s|L a] r IH]; intros Hl Hw h i h' i' d d' Hh Hh'; cbn [follow1].
  - intros E E'; injection E as <-; injection E' as <-; unfold LayeredUnique.R; cbn [flw feq]; split.
    + intros Ev; injection Ev as Eh ->; rewrite (Hinj h h' Hh Hh' Eh); reflexivity.
    + intros Ed; injection Ed as -> ->; reflexivity.
  - inversion Hw as [|? ? Hs Hr]; subst; destruct Hl as [_ [Hlr Hor]].
    destruct (seg_tgt F s h i) as [t|] eqn:Et; [|discriminate].
    destruct (seg_tgt F s h' i') as [t'|] eqn:Et'; [|discriminate].
    rewrite !(R_seg lenv), (seg_tgt_free lenv F HF s h i t _ Et), (seg_tgt_free lenv F HF s h' i' t' _ Et').
    assert (Hp : forall g k u, seg_tgt F s g k = Some u -> In g labs -> tp1 u).
    { intros g k u E Hg; destruct (seg_tgt_in lenv F HF s g k u E) as [[j ->]|H]; [exact Hg|].
      exact (proj1 (Forall_forall _ _) (proj2 Hs) u H). }
    destruct (has_terms s) eqn:Ht.
    + intros E E'; injection E as <-; injection E' as <-.
      destruct Hor as [[_ HS]|[_ [Hren _]]]; [|rewrite (sren_noterms labs s Hren) in Ht; discriminate].
      rewrite (tgt_char s r t t' HS (ex_intro _ _ (seg_tgt_sres lenv F HF s h i t Et))
                 (ex_intro _ _ (seg_tgt_sres lenv F HF s h' i' t' Et')) (Hp _ _ _ Et Hh) (Hp _ _ _ Et' Hh')).
      split; [intros ->; reflexivity|intros E; injection E as ->; reflexivity].
    + destruct t as [g j|]; [|discriminate]; destruct t' as [g' j'|]; [|discriminate]; intros E E'; cbn [ft].
      exact (IH Hlr Hr g j g' j' d d' (Hp _ _ _ Et Hh) (Hp _ _ _ Et' Hh') E E').
  - inversion Hw as [|? ? HL Hr]; subst; destruct Hl as [_ Hlr].
    destruct (lcnt F h L) as [c|] eqn:Ec; [|discriminate]; destruct (lcnt F h' L) as [c'|] eqn:Ec'; [|discriminate].
    rewrite !(R_atom lenv); unfold latom; cbn [v_label v_index].
    rewrite (lcnt_sound lenv F HF _ _ _ Ec), (lcnt_sound lenv F HF _ _ _ Ec').
    destruct (i <? c) eqn:E1, (i' <? c') eqn:E2.
    + exact (IH Hlr Hr h i h' i' d d' Hh Hh').
    + intros E E'; injection E' as <-; split; [intros Fe; destruct (stuck_mix _ _ _ _ _ Fe)|intros ->].
      pose proof (follow1_lt r _ _ _ E) as H; cbn in H; lia.
    + intros E E'; injection E as <-; split; [intros Fe; destruct (stuck_mix _ _ _ _ _ (feq_sym _ _ Fe))|intros <-].
      pose proof (follow1_lt r _ _ _ E') as H; cbn in H; lia.
    + intros E E'; injection E as <-; injection E' as <-; cbn [feq]; split.
      * intros [_ [Ez _]]; injection Ez as Eh Ei; rewrite (Hinj h h' Hh Hh' Eh) in *; rewrite Ei; reflexivity.
      * intros Ed; injection Ed as -> Ei; rewrite Ei; split; [reflexivity|split; [reflexivity|intros y; apply feq_refl]].
Qed.

End Char.

(** ** The variables to look at *)

Section Reps.

Variable F : order.
Variable labs : list lexp.

Definition tkey_eqb (t t' : ntgt) : bool :=
  match t, t' with
  | NVar h j, NVar h' j' => lexp_eqb h h' && (j =? j')
  | NBind u _ _, NBind u' _ _ => u =? u'
  | _, _ => false
  end.

Definition desc_eqb (d d' : desc) : bool :=
  match d, d' with
  | DV h i, DV h' i' => lexp_eqb h h' && (i =? i')
  | DT t e, DT t' e' => tkey_eqb t t' && (e =? e')
  | DS a h j e, DS a' h' j' e' => (a =? a') && lexp_eqb h h' && (j =? j') && (e =? e')
  | _, _ => false
  end.

(** The variable a result is about. *)
Definition dvar (d : desc) : option (lexp * nat) :=
  match d with
  | DV h i => Some (h, i)
  | DT (NVar h j) _ => Some (h, j)
  | DT _ _ => None
  | DS _ h j _ => Some (h, j)
  end.

(** Beyond [w] along [h], [follow1] goes to [h₍ᵢ₋q₊p₎], always in the
    same way. *)
Fixpoint gen1 (l : lword) (h : lexp) : option (nat * nat * nat) :=
  match l with
  | [] => Some (0, 0, 0)
  | LS s :: r =>
      match sfind F h s with
      | Some (Some (ts, m)) =>
          if has_terms s then Some (tlen ts, tlen ts, m)
          else match gen1 r h with Some (w, q, p) => Some (tlen ts + w, tlen ts + q, m + p) | None => None end
      | Some None => if has_terms s then Some (0, 0, 0) else gen1 r h
      | None => None
      end
  | LA L a :: r => match lcnt F h L with Some c => Some (c, c, 0) | None => None end
  end.

Definition smalls (W : lword) : list (lexp * nat) :=
  flat_map (fun h => match gen1 W h with Some (w, _, _) => map (fun i => (h, i)) (seq 0 w) | None => [] end) labs.

(** The variable far along a label that reaches what [x] reaches, if any. *)
Definition invgen (W : lword) (x : lexp * nat) : list (lexp * nat) :=
  match follow1 F W (fst x) (snd x) with
  | Some d =>
      match dvar d with
      | Some (g, j) => match gen1 W g with Some (w, q, p) => if p <=? j then [(g, j + q - p)] else [] | None => [] end
      | None => []
      end
  | None => []
  end.

Definition rdom (W : lword) : list (lexp * nat) := smalls W ++ flat_map (invgen W) (smalls W).

Definition keyed (W : lword) : list ((lexp * nat) * desc) :=
  flat_map (fun x => match follow1 F W (fst x) (snd x) with Some d => [(x, d)] | None => [] end) (rdom W).

Definition vltb (x y : lexp * nat) : bool :=
  match lcmp F (fst x) (fst y) with Some Lt => true | Some Eq => snd x <? snd y | _ => false end.

Definition vmin (x : lexp * nat) (l : list (lexp * nat)) : lexp * nat :=
  fold_left (fun m z => if vltb z m then z else m) l x.

(** The least variable that means the same as [x]. *)
Definition rep (W : lword) (x : lexp * nat) : lexp * nat :=
  match follow1 F W (fst x) (snd x) with
  | Some d => vmin x (map fst (filter (fun e => desc_eqb (snd e) d) (keyed W)))
  | None => x
  end.

End Reps.

(** ** Sending the targets of a segment to their representatives *)

Section Reroute.

Variable F : order.
Variable labs : list lexp.

(** Beyond [rbound W h] along [h], every variable is its own representative. *)
Definition rbound (W : lword) (h : lexp) : nat :=
  fold_left (fun acc x => if lexp_eqb (fst x) h then Nat.max acc (S (snd x)) else acc) (rdom F labs W) 0.

Definition rr_tgt (W : lword) (t : ntgt) : ntgt :=
  match t with NVar h j => let '(g, k) := rep F labs W (h, j) in NVar g k | _ => t end.

Definition rr_ent (W : lword) (e : lexp * tlist * nat) : lexp * (list ntgt * nat) :=
  let '(h, ts, m) := e in
  let B := rbound W h in
  (h, (map (rr_tgt W) (tl_list ts ++ map (fun k => NVar h (m + k)) (seq 0 (B - m))), m + (B - m))).

Definition rr_new (W : lword) (h : lexp) : lexp * (list ntgt * nat) :=
  let B := rbound W h in (h, (map (rr_tgt W) (map (fun k => NVar h k) (seq 0 B)), B)).

Definition reroute (W : lword) (Z : seg) : option seg :=
  sbuild F (map (rr_ent W) (ents Z) ++ map (rr_new W) (map fst (rdom F labs W))).

End Reroute.

Section RepSound.

Variable lenv : list label.
Variable labs : list lexp.
Hypothesis Hinj : forall h h', In h labs -> In h' labs -> lden lenv h = lden lenv h' -> h = h'.
Variable ntm : nat.
Variable F : order.
Hypothesis HF : facts_ok lenv F.
Hypothesis Htot : forall a b, In a labs -> In b labs -> lcmp F a b <> None.

Local Notation lden := (lden lenv).
Local Notation R := (R lenv).
Local Notation sp1 := (sp1 lenv labs ntm).
Local Notation tp1 := (tp1 labs ntm).
Local Notation lw1 := (lw1 lenv labs ntm).

Definition dok (d : desc) : Prop :=
  match d with DT (NBind _ w b) _ => w = WEnd SNil /\ b = None | _ => True end.

Lemma desc_eqb_spec d d' : dok d -> dok d' -> desc_eqb d d' = true <-> d = d'.
Proof.
  intros Hd Hd'; destruct d as [h i|t e|a h j e], d' as [h' i'|t' e'|a' h' j' e']; cbn [desc_eqb];
    try (split; [discriminate|intros E; discriminate E]).
  - rewrite andb_true_iff, lexp_eqb_eq, Nat.eqb_eq; split; [intros [-> ->]; reflexivity|intros E; injection E as -> ->; auto].
  - rewrite andb_true_iff, Nat.eqb_eq.
    destruct t as [g k|u w b], t' as [g' k'|u' w' b']; cbn [tkey_eqb];
      try (split; [intros [H _]; discriminate H|intros E; discriminate E]).
    + rewrite andb_true_iff, lexp_eqb_eq, Nat.eqb_eq; split; [intros [[-> ->] ->]; reflexivity|].
      intros E; injection E as -> -> ->; auto.
    + cbn in Hd, Hd'; destruct Hd as [-> ->], Hd' as [-> ->]; rewrite Nat.eqb_eq.
      split; [intros [-> ->]; reflexivity|intros E; injection E as -> ->; auto].
  - rewrite !andb_true_iff, lexp_eqb_eq, !Nat.eqb_eq.
    split; [intros [[[-> ->] ->] ->]; reflexivity|intros E; injection E as -> -> -> ->; auto].
Qed.

Lemma gen1_spec W : forall h w q p, gen1 F W h = Some (w, q, p) ->
  q <= w /\ exists f : nat -> desc, (forall j, dvar (f j) = Some (h, j)) /\ forall i, w <= i -> follow1 F W h i = Some (f (i - q + p)).
Proof.
  induction W as [|[s|L a] r IH]; intros h w q p; cbn [gen1].
  - intros E; injection E as <- <- <-; split; [lia|exists (fun j => DV h j); split; [reflexivity|]].
    intros i _; cbn; do 2 f_equal; lia.
  - destruct (sfind F h s) as [[[ts m]|]|] eqn:Ef; [| |discriminate].
    + destruct (has_terms s) eqn:Ht.
      * intros E; injection E as <- <- <-; split; [lia|exists (fun j => DT (NVar h j) (List.length r)); split; [reflexivity|]].
        intros i Hi; cbn [follow1]; unfold seg_tgt; rewrite Ef, Ht, (proj2 (Nat.ltb_ge _ _) Hi); reflexivity.
      * destruct (gen1 F r h) as [[[w0 q0] p0]|] eqn:Eg; [|discriminate]; intros E; injection E as <- <- <-.
        destruct (IH h w0 q0 p0 Eg) as [Hq [f [Hf Hr]]]; split; [lia|exists f; split; [exact Hf|]].
        intros i Hi; cbn [follow1]; unfold seg_tgt; rewrite Ef, Ht, (proj2 (Nat.ltb_ge _ _)) by lia.
        rewrite (Hr (i - tlen ts + m) ltac:(lia)); do 2 f_equal; lia.
    + destruct (has_terms s) eqn:Ht.
      * intros E; injection E as <- <- <-; split; [lia|exists (fun j => DT (NVar h j) (List.length r)); split; [reflexivity|]].
        intros i _; cbn [follow1]; unfold seg_tgt; rewrite Ef, Ht; do 3 f_equal; lia.
      * intros E; destruct (IH h w q p E) as [Hq [f [Hf Hr]]]; split; [exact Hq|exists f; split; [exact Hf|]].
        intros i Hi; cbn [follow1]; unfold seg_tgt; rewrite Ef, Ht; exact (Hr i Hi).
  - destruct (lcnt F h L) as [c|] eqn:Ec; [|discriminate]; intros E; injection E as <- <- <-.
    split; [lia|exists (fun j => DS a h j (List.length r)); split; [reflexivity|]].
    intros i Hi; cbn [follow1]; rewrite Ec, (proj2 (Nat.ltb_ge _ _) Hi); do 2 f_equal; lia.
Qed.

Lemma sfind_total s h : (forall g xs m, In (g, xs, m) (sents s) -> In g labs) -> In h labs -> sfind F h s <> None.
Proof.
  intros Hs Hh; induction s as [|g ts m r IH] using seg_spine; cbn [sfind]; [discriminate|].
  pose proof (Htot h g Hh (Hs g _ m (or_introl eq_refl))) as Hc.
  destruct (lcmp F h g) as [[]|]; [discriminate| | |destruct (Hc eq_refl)];
    apply IH; intros g' xs m' Hi; exact (Hs g' xs m' (or_intror Hi)).
Qed.

Lemma lcnt_total L h : Forall (fun p => In (fst p) labs /\ snd p <> 0) L -> In h labs -> lcnt F h L <> None.
Proof.
  intros HL Hh; induction L as [|[g n] L IH]; cbn [lcnt]; [discriminate|]; inversion HL as [|? ? [Hg _] HL']; subst.
  pose proof (Htot h g Hh Hg) as Hc; specialize (IH HL').
  destruct (lcmp F h g) as [[]|]; [| | |destruct (Hc eq_refl)]; destruct (lcnt F h L); try discriminate; destruct (IH eq_refl).
Qed.

Lemma seg_tgt_total s h i : sp1 s -> In h labs -> exists t, seg_tgt F s h i = Some t /\ tp1 t.
Proof.
  intros Hs Hh; destruct (seg_tgt F s h i) as [t|] eqn:E.
  - exists t; split; [reflexivity|]; destruct (seg_tgt_in lenv F HF s h i t E) as [[j ->]|H]; [exact Hh|].
    exact (proj1 (Forall_forall _ _) (proj2 Hs) t H).
  - exfalso; unfold seg_tgt in E; destruct (sfind F h s) as [[[ts m]|]|] eqn:Ef; try discriminate.
    exact (sfind_total s h (sshape_labs lenv labs false s (proj1 Hs)) Hh Ef).
Qed.

Definition dlab (d : desc) : Prop := match dvar d with Some (g, _) => In g labs | None => True end.

Lemma follow1_total W : lw1 W -> forall h i, In h labs -> exists d, follow1 F W h i = Some d /\ dok d /\ dlab d.
Proof.
  induction W as [|[s|L a] r IH]; intros Hw h i Hh; cbn [follow1].
  - exists (DV h i); split; [reflexivity|split; [exact I|exact Hh]].
  - inversion Hw as [|? ? Hs Hr]; subst.
    destruct (seg_tgt_total s h i Hs Hh) as [t [Et Ht]]; rewrite Et.
    destruct (has_terms s) eqn:Hts.
    + exists (DT t (List.length r)); split; [reflexivity|].
      destruct t as [g j|u w b]; [split; [exact I|exact Ht]|split; [destruct Ht as [-> [-> _]]; split; reflexivity|exact I]].
    + destruct t as [g j|u w b]; [exact (IH Hr g j Ht)|exfalso].
      destruct (seg_tgt_in lenv F HF s h i _ Et) as [[j E]|Hin]; [discriminate E|].
      unfold has_terms in Hts; rewrite <- stgts_stargets in Hts.
      assert (existsb is_term (stgts s) = true) by (apply existsb_exists; exists (NBind u w b); split; [exact Hin|reflexivity]).
      congruence.
  - inversion Hw as [|? ? HL Hr]; subst.
    destruct (lcnt F h L) as [c|] eqn:Ec; [|destruct (lcnt_total L h (proj2 HL) Hh Ec)].
    destruct (i <? c); [exact (IH Hr h i Hh)|].
    exists (DS a h (i - c) (List.length r)); split; [reflexivity|split; [exact I|exact Hh]].
Qed.

Lemma gen1_total W h : lw1 W -> In h labs -> exists w q p, gen1 F W h = Some (w, q, p).
Proof.
  intros Hw Hh; induction W as [|[s|L a] r IH]; cbn [gen1]; [eauto|inversion Hw as [|? ? Hs Hr]; subst|].
  - destruct (sfind F h s) as [[[ts m]|]|] eqn:Ef.
    + destruct (has_terms s); [eauto|]; destruct (IH Hr) as [w [q [p ->]]]; eauto.
    + destruct (has_terms s); [eauto|exact (IH Hr)].
    + destruct (sfind_total s h (sshape_labs lenv labs false s (proj1 Hs)) Hh Ef).
  - inversion Hw as [|? ? HL Hr]; subst.
    destruct (lcnt F h L) as [c|] eqn:Ec; [eauto|destruct (lcnt_total L h (proj2 HL) Hh Ec)].
Qed.

(** Two variables that reach the same, one far along its label, are both
    among the variables looked at. *)
Lemma rdom_complete W x y : lw1 W -> In (fst x) labs -> In (fst y) labs -> x <> y ->
  follow1 F W (fst x) (snd x) = follow1 F W (fst y) (snd y) -> follow1 F W (fst x) (snd x) <> None ->
  In x (rdom F labs W).
Proof.
  intros Hw Hx Hy Hne E Hs; destruct x as [hx ix], y as [hy iy]; cbn [fst snd] in *.
  destruct (gen1_total W hx Hw Hx) as [w [q [p Eg]]].
  assert (Hsm : forall h i w0 q0 p0, In h labs -> gen1 F W h = Some (w0, q0, p0) -> i < w0 -> In (h, i) (smalls F labs W)).
  { intros h i w0 q0 p0 Hh E0 Hi; unfold smalls; apply in_flat_map; exists h; split; [exact Hh|].
    rewrite E0; apply in_map, in_seq; lia. }
  unfold rdom; apply in_or_app.
  destruct (Nat.lt_ge_cases ix w) as [Hi|Hi]; [left; exact (Hsm _ _ _ _ _ Hx Eg Hi)|right].
  destruct (gen1_spec W hx w q p Eg) as [Hq [f [Hf Hr]]].
  destruct (gen1_total W hy Hw Hy) as [w' [q' [p' Eg']]].
  destruct (gen1_spec W hy w' q' p' Eg') as [Hq' [f' [Hf' Hr']]].
  rewrite (Hr ix Hi) in E.
  destruct (Nat.lt_ge_cases iy w') as [Hi'|Hi'].
  - apply in_flat_map; exists (hy, iy); split; [exact (Hsm _ _ _ _ _ Hy Eg' Hi')|].
    unfold invgen; cbn [fst snd]; rewrite <- E, Hf, Eg, (proj2 (Nat.leb_le _ _)) by lia.
    left; f_equal; lia.
  - exfalso; rewrite (Hr' iy Hi') in E; injection E as E.
    pose proof (Hf (ix - q + p)) as A; rewrite E, Hf' in A; injection A as <- A.
    rewrite Eg in Eg'; injection Eg' as <- <- <-; apply Hne; f_equal; lia.
Qed.

Definition pv (x : lexp * nat) : rvar := mk_rvar (lden (fst x)) (snd x).

Lemma vltb_spec x y : In (fst x) labs -> In (fst y) labs -> vltb F x y = true <-> vlt (pv x) (pv y).
Proof.
  intros Hx Hy; unfold vltb, pv; destruct (lcmp F (fst x) (fst y)) as [c|] eqn:E; [|destruct (Htot _ _ Hx Hy E)].
  pose proof (lcmp_sound lenv F HF _ _ _ E) as Hc; destruct c; cbn in Hc.
  - rewrite Hc, Nat.ltb_lt; unfold vlt; cbn [v_label v_index]; split; [intros H; right; split; [reflexivity|exact H]|].
    intros [H|[_ H]]; [destruct (olabel_lt_irrefl _ H)|exact H].
  - split; [intros _; left; exact Hc|reflexivity].
  - split; [discriminate|intros H; exfalso; refine (vlt_asym _ _ H _); left; exact Hc].
Qed.

Lemma vmin_spec l : forall x, (forall z, In z (x :: l) -> In (fst z) labs) ->
  In (vmin F x l) (x :: l) /\ forall z, In z (x :: l) -> ~ vlt (pv z) (pv (vmin F x l)).
Proof.
  induction l as [|z l IH]; intros x Hl; cbn [vmin fold_left].
  - split; [left; reflexivity|intros z [<-|[]]; apply vlt_irrefl].
  - set (m := if vltb F z x then z else x).
    assert (Hm : In m (x :: z :: l)) by (unfold m; destruct (vltb F z x); [right; left|left]; reflexivity).
    destruct (IH m ltac:(intros z' [<-|H]; apply Hl; [exact Hm|right; right; exact H])) as [Hin Hmin].
    change (fold_left _ l m) with (vmin F m l).
    split; [destruct Hin as [<-|H]; [exact Hm|right; right; exact H]|].
    pose proof (Hmin m (or_introl eq_refl)) as Hmm.
    assert (Vx : In (fst x) labs) by (apply Hl; left; reflexivity).
    assert (Vz : In (fst z) labs) by (apply Hl; right; left; reflexivity).
    intros z' [<-|[<-|H]]; [| |exact (Hmin z' (or_intror H))].
    + unfold m in Hmm; destruct (vltb F z x) eqn:Ez; [|exact Hmm].
      apply (vltb_spec z x Vz Vx) in Ez; intros Hv; exact (Hmm (vlt_trans _ _ _ Ez Hv)).
    + unfold m in Hmm; destruct (vltb F z x) eqn:Ez; [exact Hmm|].
      assert (Nz : ~ vlt (pv z) (pv x)) by (intros Hv; apply (vltb_spec z x Vz Vx) in Hv; congruence).
      intros Hv; destruct (vlt_total (pv x) (pv (vmin F m l))) as [H|[H|H]]; [exact (Hmm H)| |].
      * rewrite <- H in Hv; exact (Nz Hv).
      * exact (Nz (vlt_trans _ _ _ Hv H)).
Qed.

Lemma pair_dec (x y : lexp * nat) : x = y \/ x <> y.
Proof.
  destruct x as [h i], y as [h' i']; destruct (lexp_eqb h h') eqn:E.
  - apply lexp_eqb_eq in E; subst; destruct (Nat.eq_dec i i') as [->|N]; [left; reflexivity|right; congruence].
  - right; intros H; injection H as -> ->; rewrite (proj2 (lexp_eqb_eq h' h') eq_refl) in E; discriminate.
Qed.

Lemma keyed_in W x d : In (x, d) (keyed F labs W) <-> In x (rdom F labs W) /\ follow1 F W (fst x) (snd x) = Some d.
Proof.
  unfold keyed; rewrite in_flat_map; split.
  - intros [y [Hy Hin]]; destruct (follow1 F W (fst y) (snd y)) as [dy|] eqn:E; [|destruct Hin].
    destruct Hin as [Hin|[]]; injection Hin as <- <-; split; assumption.
  - intros [Hx E]; exists x; split; [exact Hx|]; rewrite E; left; reflexivity.
Qed.

Lemma rdom_labs W : lw1 W -> forall x, In x (rdom F labs W) -> In (fst x) labs.
Proof.
  intros Hw x Hx.
  assert (Hs : forall y, In y (smalls F labs W) -> In (fst y) labs).
  { intros y Hy; unfold smalls in Hy; apply in_flat_map in Hy as [h [Hh Hy]].
    destruct (gen1 F W h) as [[[w q] p]|]; [|destruct Hy]; apply in_map_iff in Hy as [i [<- _]]; exact Hh. }
  unfold rdom in Hx; apply in_app_or in Hx as [Hx|Hx]; [exact (Hs x Hx)|].
  apply in_flat_map in Hx as [y [Hy Hx]]; unfold invgen in Hx.
  destruct (follow1_total W Hw (fst y) (snd y) (Hs y Hy)) as [d [Ed [_ Hd]]]; rewrite Ed in Hx.
  unfold dlab in Hd; destruct (dvar d) as [[g j]|]; [|destruct Hx].
  destruct (gen1 F W g) as [[[w q] p]|]; [|destruct Hx]; destruct (p <=? j); [|destruct Hx].
  destruct Hx as [<-|[]]; exact Hd.
Qed.

Theorem rep_spec W x d : lw1 W -> In (fst x) labs -> follow1 F W (fst x) (snd x) = Some d ->
  In (fst (rep F labs W x)) labs /\ follow1 F W (fst (rep F labs W x)) (snd (rep F labs W x)) = Some d
  /\ forall y, In (fst y) labs -> follow1 F W (fst y) (snd y) = Some d -> ~ vlt (pv y) (pv (rep F labs W x)).
Proof.
  intros Hw Hx Ex.
  destruct (follow1_total W Hw (fst x) (snd x) Hx) as [d0 [E0 [Hd _]]]; rewrite Ex in E0; injection E0 as <-.
  set (L := map fst (filter (fun e => desc_eqb (snd e) d) (keyed F labs W))).
  assert (HL : forall z, In z L -> In (fst z) labs /\ follow1 F W (fst z) (snd z) = Some d).
  { intros z Hz; unfold L in Hz; apply in_map_iff in Hz as [[z' dz] [<- Hz]]; apply filter_In in Hz as [Hz Eq].
    apply keyed_in in Hz as [Hz Ez]; cbn [fst snd] in *.
    pose proof (rdom_labs W Hw z' Hz) as Hzl; split; [exact Hzl|].
    destruct (follow1_total W Hw (fst z') (snd z') Hzl) as [dz' [Ez' [Hdz _]]]; rewrite Ez in Ez'; injection Ez' as <-.
    rewrite (proj1 (desc_eqb_spec dz d Hdz Hd) Eq) in Ez; exact Ez. }
  assert (Hall : forall z, In z (x :: L) -> In (fst z) labs /\ follow1 F W (fst z) (snd z) = Some d).
  { intros z [<-|Hz]; [split; assumption|exact (HL z Hz)]. }
  unfold rep; rewrite Ex; fold L.
  destruct (vmin_spec L x (fun z Hz => proj1 (Hall z Hz))) as [Hin Hmin].
  split; [exact (proj1 (Hall _ Hin))|split; [exact (proj2 (Hall _ Hin))|]].
  intros y Hy Ey; apply Hmin.
  destruct (pair_dec y x) as [->|Hne]; [left; reflexivity|right].
  assert (Hyd : In y (rdom F labs W)) by (refine (rdom_complete W y x Hw Hy Hx Hne _ _); [rewrite Ey, Ex; reflexivity|rewrite Ey; discriminate]).
  unfold L; apply in_map_iff; exists (y, d); split; [reflexivity|apply filter_In; split].
  - apply keyed_in; split; assumption.
  - apply (desc_eqb_spec d d Hd Hd); reflexivity.
Qed.

Lemma ments_labs W : lw1 W -> forall g, In g (ments W) -> In g labs.
Proof.
  induction W as [|[s0|L a] r IH]; intros Hw g; cbn [ments]; [intros []|inversion Hw as [|? ? Hs Hr]; subst|].
  - intros H; apply in_app_or in H as [H|H]; [|exact (IH Hr g H)].
    apply filter_In in H as [H _]; apply in_map_iff in H as [[[h ts] m] [<- He]].
    apply (sshape_labs lenv labs false s0 (proj1 Hs) h (tl_list ts) m).
    rewrite <- (ents_sents s0); apply (in_map (fun e => (fst (fst e), tl_list (snd (fst e)), snd e))) in He; exact He.
  - inversion Hw as [|? ? HL Hr]; subst; intros H; apply in_app_or in H as [H|H]; [|exact (IH Hr g H)].
    apply filter_In in H as [H _]; apply in_map_iff in H as [[h n] [<- He]].
    exact (proj1 (proj1 (Forall_forall _ _) (proj2 HL) _ He)).
Qed.

Definition llab (l : option label) : Prop := exists g, In g labs /\ lden g = l.

Lemma val_lab W : lw1 W -> forall h i, In h labs ->
  match R W (mk_rvar (lden h) i) with FVar z => llab (v_label z) | FStuck _ z _ => llab (v_label z) | _ => True end.
Proof.
  induction W as [|[s0|L a] r IH]; intros Hw h i Hh.
  - exists h; split; [exact Hh|reflexivity].
  - inversion Hw as [|? ? Hs Hr]; subst; rewrite (R_seg lenv).
    destruct (seg_tgt_total s0 h i Hs Hh) as [t [Et Ht]]; rewrite (seg_tgt_free lenv F HF s0 h i t _ Et).
    destruct t as [g j|u w b]; [exact (IH Hr g j Ht)|exact I].
  - inversion Hw as [|? ? HL Hr]; subst; rewrite (R_atom lenv); unfold latom; cbn [v_label v_index].
    destruct (_ <? _); [exact (IH Hr h i Hh)|exists h; split; [exact Hh|reflexivity]].
Qed.

(** A variable that means the same as one of the labels has one of the labels. *)
Lemma feq_lab W y h i : lw1 W -> In h labs -> In LNone labs -> feq (R W y) (R W (mk_rvar (lden h) i)) -> llab (v_label y).
Proof.
  intros Hw Hh HN Fe; destruct y as [l k]; cbn [v_label].
  destruct l as [x|]; [|exists LNone; split; [exact HN|reflexivity]].
  destruct (existsb (fun g => label_eqb (lden g) (Some x)) labs) eqn:Ex.
  - apply existsb_exists in Ex as [g [Hg Eg]]; exists g; split; [exact Hg|apply label_eqb_eq, Eg].
  - exfalso.
    assert (Hm : ~ In (Some x) (map lden (ments W))).
    { intros Hin; apply in_map_iff in Hin as [g [Eg Hg]].
      assert (existsb (fun g => label_eqb (lden g) (Some x)) labs = true)
        by (apply existsb_exists; exists g; split; [exact (ments_labs W Hw g Hg)|rewrite Eg; apply label_eqb_refl]).
      congruence. }
    assert (Nl : ~ llab (Some x)).
    { intros [g [Hg Eg]]; assert (existsb (fun g => label_eqb (lden g) (Some x)) labs = true)
        by (apply existsb_exists; exists g; split; [exact Hg|rewrite Eg; apply label_eqb_refl]).
      congruence. }
    pose proof (val_lab W Hw h i Hh) as V.
    rewrite (unmentioned lenv W (Some x) k ltac:(discriminate) Hm) in Fe.
    destruct (firstatom W) as [[[L a] d]|];
      destruct (R W (mk_rvar (lden h) i)) as [z|u b k'|a' z k']; cbn [feq] in Fe; try contradiction.
    + destruct Fe as [_ [<- _]]; exact (Nl V).
    + subst z; exact (Nl V).
Qed.

Lemma pv_inj x y : In (fst x) labs -> In (fst y) labs -> pv x = pv y -> x = y.
Proof.
  destruct x as [h i], y as [h' i']; unfold pv; cbn [fst snd]; intros Hh Hh' E; injection E as Eh ->.
  rewrite (Hinj h h' Hh Hh' Eh); reflexivity.
Qed.

(** The representative means the same, is where the variable must go,
    and is the same for variables that mean the same. *)
Theorem rep_ok W x : lnf lenv labs gtP W -> lw1 W -> In LNone labs -> In (fst x) labs ->
  In (fst (rep F labs W x)) labs /\ feq (R W (pv (rep F labs W x))) (R W (pv x)) /\ routed (R W) (pv (rep F labs W x))
  /\ forall x', In (fst x') labs -> feq (R W (pv x')) (R W (pv x)) -> rep F labs W x' = rep F labs W x.
Proof.
  intros Hl Hw HN Hx.
  destruct (follow1_total W Hw (fst x) (snd x) Hx) as [d [Ed _]].
  destruct (rep_spec W x d Hw Hx Ed) as [Hr [Er Hmin]].
  set (r := rep F labs W x) in *.
  assert (Ch : forall y, In (fst y) labs -> follow1 F W (fst y) (snd y) = Some d <-> feq (R W (pv y)) (R W (pv x))).
  { intros y Hy; destruct (follow1_total W Hw (fst y) (snd y) Hy) as [dy [Ey _]]; rewrite Ey.
    rewrite (follow1_char lenv labs Hinj ntm F HF W Hl Hw (fst y) (snd y) (fst x) (snd x) dy d Hy Hx Ey Ed).
    split; [intros H; injection H as ->; reflexivity|intros ->; reflexivity]. }
  assert (Hcl : forall y', feq (R W y') (R W (pv r)) -> exists y, y' = pv y /\ In (fst y) labs /\ follow1 F W (fst y) (snd y) = Some d).
  { intros y' Fe; destruct (feq_lab W y' (fst r) (snd r) Hw Hr HN Fe) as [g [Hg Eg]].
    exists (g, v_index y'); split; [destruct y'; unfold pv; cbn in *; rewrite Eg; reflexivity|split; [exact Hg|]].
    apply Ch; [exact Hg|]; refine (feq_trans _ _ _ _ (proj1 (Ch r Hr) Er)).
    replace (pv (g, v_index y')) with y' by (destruct y'; unfold pv; cbn in *; rewrite Eg; reflexivity); exact Fe. }
  split; [exact Hr|split; [exact (proj1 (Ch r Hr) Er)|split]].
  - split.
    + intros _ y' _ Fe; destruct (Hcl y' Fe) as [y [-> [Hy Ey]]]; exact (Hmin y Hy Ey).
    + intros Hb y' Hy' Fe; destruct (Hcl y' Fe) as [y [-> [Hy Ey]]]; apply (Hmin y Hy Ey).
      left; unfold olabel_lt; unfold bound in Hb; unfold named in Hy'; rewrite Hb.
      destruct (v_label (pv y)) as [lx|]; [reflexivity|destruct (Hy' eq_refl)].
  - intros x' Hx' Fe; apply Ch in Fe; [|exact Hx'].
    destruct (rep_spec W x' d Hw Hx' Fe) as [Hr' [Er' Hmin']].
    apply pv_inj; [exact Hr'|exact Hr|].
    destruct (vlt_total (pv (rep F labs W x')) (pv r)) as [H|[H|H]]; [destruct (Hmin _ Hr' Er' H)|exact H|destruct (Hmin' _ Hr Er H)].
Qed.

Lemma rep_id W x : lw1 W -> In (fst x) labs -> ~ In x (rdom F labs W) -> rep F labs W x = x.
Proof.
  intros Hw Hx Hn; destruct (follow1_total W Hw (fst x) (snd x) Hx) as [d [Ed [Hd _]]].
  unfold rep; rewrite Ed.
  destruct (map fst (filter (fun e => desc_eqb (snd e) d) (keyed F labs W))) as [|z L] eqn:EL; [reflexivity|exfalso].
  assert (Hz : In z (map fst (filter (fun e => desc_eqb (snd e) d) (keyed F labs W)))) by (rewrite EL; left; reflexivity).
  apply in_map_iff in Hz as [[z' dz] [<- Hz]]; apply filter_In in Hz as [Hz Eq]; apply keyed_in in Hz as [Hz Ez].
  cbn [fst snd] in *; pose proof (rdom_labs W Hw z' Hz) as Hzl.
  destruct (follow1_total W Hw (fst z') (snd z') Hzl) as [dz' [Ez' [Hdz _]]]; rewrite Ez in Ez'; injection Ez' as <-.
  rewrite (proj1 (desc_eqb_spec dz d Hdz Hd) Eq) in Ez.
  destruct (pair_dec x z') as [->|Hne]; [exact (Hn Hz)|].
  apply Hn, (rdom_complete W x z' Hw Hx Hzl Hne); [rewrite Ed, Ez; reflexivity|rewrite Ed; discriminate].
Qed.

Lemma rbound_spec W h i : In (h, i) (rdom F labs W) -> i < rbound F labs W h.
Proof.
  unfold rbound; generalize 0; intros a0 Hin.
  assert (G : forall l acc, (forall x, In x l -> lexp_eqb (fst x) h = true -> snd x < S (snd x)) ->
            acc <= fold_left (fun acc x => if lexp_eqb (fst x) h then Nat.max acc (S (snd x)) else acc) l acc
            /\ forall x, In x l -> lexp_eqb (fst x) h = true ->
                 S (snd x) <= fold_left (fun acc x => if lexp_eqb (fst x) h then Nat.max acc (S (snd x)) else acc) l acc).
  { induction l as [|y l IH]; intros acc _; cbn [fold_left]; [split; [lia|intros x []]|].
    destruct (IH (if lexp_eqb (fst y) h then Nat.max acc (S (snd y)) else acc) (fun x _ _ => Nat.lt_succ_diag_r _)) as [A B].
    split; [revert A; destruct (lexp_eqb (fst y) h); intros A; lia|].
    intros x [<-|Hx] Ex; [rewrite Ex in A |- *; pose proof (Nat.le_max_r acc (S (snd y))); lia|exact (B x Hx Ex)]. }
  destruct (G (rdom F labs W) a0 (fun x _ _ => Nat.lt_succ_diag_r _)) as [_ B].
  specialize (B (h, i) Hin (proj2 (lexp_eqb_eq h h) eq_refl)); cbn [snd] in B; lia.
Qed.

Definition rv (W : lword) (y : rvar) : rvar :=
  match find (fun g => label_eqb (lden g) (v_label y)) labs with
  | Some g => pv (rep F labs W (g, v_index y))
  | None => y
  end.

Lemma rv_pv W g k : In g labs -> rv W (pv (g, k)) = pv (rep F labs W (g, k)).
Proof.
  intros Hg; unfold rv, pv; cbn [fst snd v_label v_index].
  destruct (find (fun g' => label_eqb (lden g') (lden g)) labs) as [g'|] eqn:E.
  - apply find_some in E as [E Hg']; apply label_eqb_eq in E; rewrite (Hinj g' g Hg' Hg E); reflexivity.
  - exfalso; pose proof (find_none _ _ _ E Hg) as H; cbn in H; rewrite label_eqb_refl in H; discriminate.
Qed.

Definition rvres (W : lword) (r : rvar + tm) : rvar + tm := match r with inl y => inl (rv W y) | inr t => inr t end.

Lemma nth_map_lt {A B} (f : A -> B) l i da db : i < List.length l -> nth i (map f l) db = f (nth i l da).
Proof. intros Hi; rewrite (nth_indep _ db (f da)) by (rewrite length_map; exact Hi); apply map_nth. Qed.

Lemma rr_tgt_tres W t : lw1 W -> tp1 t -> tres lenv (rr_tgt F labs W t) = rvres W (tres lenv t) /\ tp1 (rr_tgt F labs W t).
Proof.
  intros Hw Ht; destruct t as [g j|u w b]; [|split; [reflexivity|exact Ht]]; cbn [rr_tgt].
  destruct (follow1_total W Hw g j Ht) as [d [Ed _]].
  destruct (rep_spec W (g, j) d Hw Ht Ed) as [Hr _].
  destruct (rep F labs W (g, j)) as [g' k'] eqn:Er; cbn [tres rvres].
  change (mk_rvar (lden g) j) with (pv (g, j)); rewrite (rv_pv W g j Ht), Er; split; [reflexivity|exact Hr].
Qed.

Lemma rr_ent_etgt W h ts m i : lw1 W -> In h labs -> Forall tp1 (tl_list ts) ->
  etgt lenv h (fst (snd (rr_ent F labs W (h, ts, m)))) (snd (snd (rr_ent F labs W (h, ts, m)))) i
  = rvres W (etgt lenv h (tl_list ts) m i).
Proof.
  intros Hw Hh Hts; cbn [rr_ent fst snd]; set (B := rbound F labs W h); set (xs := tl_list ts) in *.
  unfold etgt; rewrite length_map, length_app, length_map, length_seq.
  destruct (Nat.ltb_spec i (List.length xs)) as [H1|H1].
  - rewrite (proj2 (Nat.ltb_lt _ _)) by lia.
    rewrite (nth_map_lt _ _ _ (NVar LNone 0)) by (rewrite length_app, length_map, length_seq; lia).
    rewrite app_nth1 by exact H1.
    exact (proj1 (rr_tgt_tres W _ Hw (proj1 (Forall_forall _ _) Hts _ (nth_In _ _ H1)))).
  - destruct (Nat.ltb_spec i (List.length xs + (B - m))) as [H2|H2].
    + rewrite (nth_map_lt _ _ _ (NVar LNone 0)) by (rewrite length_app, length_map, length_seq; lia).
      rewrite app_nth2 by exact H1.
      rewrite (nth_map_lt _ _ _ 0) by (rewrite length_seq; lia); rewrite seq_nth by lia.
      rewrite (proj1 (rr_tgt_tres W (NVar h (m + (0 + (i - List.length xs)))) Hw Hh)); cbn [tres rvres].
      do 3 f_equal; lia.
    + cbn [rvres]; f_equal.
      change (mk_rvar (lden h) (i - List.length xs + m)) with (pv (h, i - List.length xs + m)).
      rewrite (rv_pv W h _ Hh), rep_id; [unfold pv; cbn; f_equal; lia|exact Hw|exact Hh|].
      intros Hin; pose proof (rbound_spec W h _ Hin); unfold B in *; lia.
Qed.

Lemma rr_new_etgt W h i : lw1 W -> In h labs ->
  etgt lenv h (fst (snd (rr_new F labs W h))) (snd (snd (rr_new F labs W h))) i = inl (rv W (pv (h, i))).
Proof.
  intros Hw Hh; cbn [rr_new fst snd]; set (B := rbound F labs W h); unfold etgt; rewrite !length_map, length_seq.
  destruct (Nat.ltb_spec i B) as [H1|H1].
  - rewrite (nth_map_lt _ _ _ (NVar LNone 0)) by (rewrite length_map, length_seq; lia).
    rewrite (nth_map_lt _ _ _ 0) by (rewrite length_seq; lia); rewrite seq_nth by lia.
    exact (proj1 (rr_tgt_tres W (NVar h (0 + i)) Hw Hh)).
  - f_equal; rewrite (rv_pv W h i Hh), rep_id; [unfold pv; cbn; f_equal; lia|exact Hw|exact Hh|].
    intros Hin; pose proof (rbound_spec W h _ Hin); unfold B in *; lia.
Qed.

Theorem reroute_ok W Z Z' : lw1 W -> sp1 Z -> reroute F labs W Z = Some Z' ->
  sp1 Z' /\ forall x, sres lenv Z' x = rvres W (sres lenv Z x).
Proof.
  intros Hw HZ E.
  assert (HlZ : forall h ts m, In (h, ts, m) (ents Z) -> In h labs).
  { intros h ts m Hin; apply (sshape_labs lenv labs false Z (proj1 HZ) h (tl_list ts) m).
    rewrite <- ents_sents; apply (in_map (fun e => (fst (fst e), tl_list (snd (fst e)), snd e)) _ _ Hin). }
  assert (HtZ : forall h ts m, In (h, ts, m) (ents Z) -> Forall tp1 (tl_list ts)).
  { intros h ts m Hin; apply Forall_forall; intros t Ht.
    exact (proj1 (Forall_forall _ _) (proj2 HZ) t (ents_stgts Z h ts m t Hin Ht)). }
  split.
  - destruct (sbuild_shape lenv labs F HF _ _ E) as [Hs [Ht _]].
    { intros h xs m Hin; apply in_app_or in Hin as [Hin|Hin]; apply in_map_iff in Hin as [e [Ee Hin]].
      - destruct e as [[h' ts'] m']; cbn [rr_ent] in Ee; injection Ee as <- _ _; exact (HlZ _ _ _ Hin).
      - unfold rr_new in Ee; injection Ee as <- _ _; apply in_map_iff in Hin as [x [<- Hx]]; exact (rdom_labs W Hw x Hx). }
    split; [exact Hs|apply Forall_forall; intros t Hin; destruct (Ht t Hin) as [h [xs [m [He Hx]]]]].
    apply in_app_or in He as [He|He]; apply in_map_iff in He as [e [Ee He]].
    + destruct e as [[h' ts'] m']; cbn [rr_ent] in Ee; injection Ee as <- <- <-.
      apply in_map_iff in Hx as [t0 [<- Hx]]; apply (rr_tgt_tres W t0 Hw); apply in_app_or in Hx as [Hx|Hx].
      * exact (proj1 (Forall_forall _ _) (HtZ _ _ _ He) t0 Hx).
      * apply in_map_iff in Hx as [k [<- _]]; exact (HlZ _ _ _ He).
    + unfold rr_new in Ee; injection Ee as <- <- <-; apply in_map_iff in He as [x [<- Hx0]].
      apply in_map_iff in Hx as [t0 [<- Hx]]; apply in_map_iff in Hx as [k [<- _]].
      apply (rr_tgt_tres W _ Hw); exact (rdom_labs W Hw x Hx0).
  - intros [l i]; rewrite (sres_sbuild lenv F HF _ _ E l i), (sres_ents lenv Z l i).
    pose proof (find_map_lab lenv (rr_ent F labs W) (fun e => fst (fst e)) fst (ents Z) l
                  (fun e => match e with (h, ts, m) => eq_refl end)) as Fm.
    destruct (find (fun e => label_eqb (lden (fst (fst e))) l) (ents Z)) as [[[h ts] m]|] eqn:Ef.
    + cbn [option_map] in Fm; rewrite (find_app_some _ _ _ _ Fm).
      apply find_some in Ef as [_ Hin].
      destruct (rr_ent F labs W (h, ts, m)) as [h' [xs' m']] eqn:Er.
      pose proof (rr_ent_etgt W h ts m i Hw (HlZ _ _ _ Hin) (HtZ _ _ _ Hin)) as R1; rewrite Er in R1; cbn [fst snd] in R1.
      assert (h' = h) as -> by (cbn [rr_ent] in Er; injection Er as <- _ _; reflexivity); exact R1.
    + cbn [option_map] in Fm; rewrite (find_app_none _ _ _ Fm).
      rewrite (find_map_lab lenv (rr_new F labs W) (fun h => h) fst _ l) by (intros h; reflexivity).
      destruct (find (fun h => label_eqb (lden h) l) (map fst (rdom F labs W))) as [h|] eqn:Eh.
      * apply find_some in Eh as [Eh Hin]; apply label_eqb_eq in Eh; subst l; cbn [option_map].
        apply in_map_iff in Hin as [x [<- Hx]].
        exact (rr_new_etgt W (fst x) i Hw (rdom_labs W Hw x Hx)).
      * cbn [rvres]; f_equal; unfold rv; cbn [v_label v_index].
        destruct (find (fun g => label_eqb (lden g) l) labs) as [g|] eqn:Eg; [|reflexivity].
        apply find_some in Eg as [Eg Hg]; apply label_eqb_eq in Eg; subst l.
        rewrite rep_id; [reflexivity|exact Hw|exact Hg|].
        intros Hin; pose proof (find_none _ _ _ Eh (in_map fst _ (g, i) Hin)) as H; cbn in H.
        rewrite label_eqb_refl in H; discriminate.
Qed.

End RepSound.
