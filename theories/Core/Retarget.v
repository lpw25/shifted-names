(** * Mapping the variables a segment sends things to

    [tmap f nbf dl extra s] replaces every variable target of [s], and
    of the tails of its terms, by its image under [f].  For each label
    [g], the first [nbf g] default targets are made explicit first, and
    bound variables from [nbf ·] on move down by [dl].

    Two uses: sending variables to the representative of their key in
    the rest of the word ([reroute_g]), and numbering the bound variables
    between two segments in the order they are first used ([renum]). *)

From Stdlib Require Import Arith List Lia Bool.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Layered Canon Keys.
Import ListNotations.

(** The tail of a term whose payload has an atom of its own or a payload
    atom: what the bound variables after it go on as. *)
Definition ttail (t : ntgt) : option seg :=
  match t with
  | NBind _ (WEnd N) (Some _) => Some N
  | NBind _ (WAtom A _ _ _) _ => Some A
  | _ => None
  end.

Definition tset (t : ntgt) (A' : seg) : ntgt :=
  match t with
  | NBind u (WEnd _) (Some n) => NBind u (WEnd A') (Some n)
  | NBind u (WAtom _ L a w) b => NBind u (WAtom A' L a w) b
  | _ => t
  end.

Fixpoint bvs (l : list ntgt) : list nat :=
  match l with NVar LNone j :: l' => j :: bvs l' | _ :: l' => bvs l' | [] => [] end.

Fixpoint omapl {A B} (f : A -> option B) (l : list A) : option (list B) :=
  match l with
  | [] => Some []
  | x :: r => match f x, omapl f r with Some y, Some ys => Some (y :: ys) | _, _ => None end
  end.

Fixpoint nodup_l (l : list lexp) (seen : list lexp) : list lexp :=
  match l with
  | [] => []
  | x :: r => if existsb (lexp_eqb x) seen then nodup_l r seen else x :: nodup_l r (x :: seen)
  end.

Definition expl (g : lexp) (ts : list ntgt) (m k : nat) : list ntgt := ts ++ map (NVar g) (seq m k).

Definition rtv (f : lexp -> nat -> option (lexp * nat)) (t : ntgt) : option ntgt :=
  match t with
  | NVar g i => option_map (fun p => NVar (fst p) (snd p)) (f g i)
  | _ => None
  end.

Section Retarget.

Variable F : order.
Variable ntm : nat.

(** A tail that only renames bound variables. *)
Definition settled_tail (A : seg) : bool :=
  negb (has_terms A) && match sdrop_none A with SNil => true | _ => false end.

Definition bpart (A : seg) : seg := match bent F A with (TNil, 0) => SNil | (ts, m) => SEnt LNone ts m SNil end.

Definition tail_map (f : lexp -> nat -> option (lexp * nat)) (nb dl : nat) (A : seg) : option seg :=
  match sfind F LNone A with
  | Some e =>
      let '(ts, m) := ofe e in
      let k := nb - m in
      obind (omapl (rtv f) (expl LNone (tl_list ts) m k)) (fun l => sset F LNone (tl_of l) (m + k - dl) SNil)
  | None => None
  end.

Definition tm_t (f : lexp -> nat -> option (lexp * nat)) (nb dl : nat) (t : ntgt) : option ntgt :=
  match t with
  | NVar _ _ => rtv f t
  | NBind u (WEnd SNil) None => if u <? ntm then Some t else None
  | NBind u _ _ =>
      if u <? ntm then
        match ttail t with
        | Some A => if settled_tail A then option_map (tset t) (tail_map f nb dl A) else None
        | None => None
        end
      else None
  end.

Definition tmap (f : lexp -> nat -> option (lexp * nat)) (nbf : lexp -> nat) (dl : nat) (extra : list lexp) (s : seg)
  : option seg :=
  obind (omapl (fun g =>
           match sfind F g s with
           | Some e =>
               let '(ts, m) := ofe e in
               let k := nbf g - m in
               option_map (fun l => (g, tl_of l, m + k - match g with LNone => dl | _ => 0 end))
                          (omapl (tm_t f (nbf LNone) dl) (expl g (tl_list ts) m k))
           | None => None
           end) (nodup_l (LNone :: seg_labels s ++ extra) [])) (mkseg F).

End Retarget.

(** ** Lists *)

Lemma omapl_nth {A B} (f : A -> option B) : forall l l', omapl f l = Some l' ->
  List.length l' = List.length l
  /\ forall j d d', j < List.length l -> f (nth j l d) = Some (nth j l' d').
Proof.
  induction l as [|x r IH]; intros l'; cbn [omapl].
  - intros H; injection H as <-; split; [reflexivity|intros j d d' Hj; cbn in Hj; lia].
  - destruct (f x) as [y|] eqn:Ex; [|discriminate]; destruct (omapl f r) as [ys|] eqn:Er; [|discriminate].
    intros H; injection H as <-; destruct (IH ys eq_refl) as [Hl Hn]; split; [cbn; lia|].
    intros [|j] d d' Hj; cbn [nth]; [exact Ex|apply Hn; cbn in Hj; lia].
Qed.

Lemma omapl_in {A B} (f : A -> option B) : forall l l' y, omapl f l = Some l' -> In y l' -> exists x, In x l /\ f x = Some y.
Proof.
  induction l as [|x r IH]; intros l' y; cbn [omapl].
  - intros H; injection H as <-; intros [].
  - destruct (f x) as [y0|] eqn:Ex; [|discriminate]; destruct (omapl f r) as [ys|] eqn:Er; [|discriminate].
    intros H; injection H as <-; intros [<-|Hin]; [exists x; split; [left; reflexivity|exact Ex]|].
    destruct (IH ys y eq_refl Hin) as [x0 [H1 H2]]; exists x0; split; [right; exact H1|exact H2].
Qed.

Lemma nodup_l_in x : forall l seen, In x l -> existsb (lexp_eqb x) seen = true \/ In x (nodup_l l seen).
Proof.
  induction l as [|y r IH]; intros seen; [intros []|]; cbn [nodup_l].
  intros [->|Hin].
  - destruct (existsb (lexp_eqb x) seen) eqn:E; [left; reflexivity|right; left; reflexivity].
  - destruct (existsb (lexp_eqb y) seen) eqn:E; [exact (IH seen Hin)|].
    destruct (IH (y :: seen) Hin) as [H|H]; [|right; right; exact H].
    cbn [existsb] in H; apply orb_true_iff in H as [H|H]; [|left; exact H].
    apply lexp_eqb_eq in H; subst y; right; left; reflexivity.
Qed.

Lemma nodup_l_in0 x l : In x l -> In x (nodup_l l []).
Proof. intros H; destruct (nodup_l_in x l [] H) as [E|E]; [discriminate E|exact E]. Qed.

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
Local Notation sget := (sget lenv).
Local Notation sdist := (sdist lenv).
Local Notation sdistd := (sdistd lenv).
Local Notation tdist := (tdist lenv).
Local Notation tldist := (tldist lenv).
Local Notation esem := (esem lenv tenv aenv penv).
Local Notation lsem := (lsem lenv tenv aenv penv).

(** *** A segment built from a list of entries *)

Fixpoint efind (l : option label) (es : list (lexp * tlist * nat)) : option (tlist * nat) :=
  match es with
  | [] => None
  | (h, ts, m) :: r => if label_eqb (lden h) l then Some (ts, m) else efind l r
  end.

Lemma mkseg_spec es : forall s, mkseg F es = Some s -> Forall (fun e => tldist (snd (fst e))) es ->
  sdistd s /\ forall l j, esem l (sget l s) j = esem l (efind l es) j.
Proof.
  induction es as [|[[h ts] m] r IH]; intros s; unfold mkseg; cbn [fold_right].
  - intros H _; injection H as <-; split; [exact I|reflexivity].
  - fold (mkseg F r); destruct (mkseg F r) as [s0|] eqn:E0; [|discriminate]; cbn [obind]; intros H HT.
    inversion HT as [|? ? Ht HT']; subst; cbn [fst snd] in Ht.
    destruct (IH s0 eq_refl HT') as [Hd0 Hs0].
    destruct (sset_sound lenv tenv aenv penv F HF ntm Hntm h ts m s0 s (sdistd_sdist lenv _ Hd0) H) as [_ Hs].
    split; [exact (sset_dd lenv tenv aenv penv F HF ntm Hntm h ts m s0 s Hd0 Ht H)|].
    intros l j; rewrite Hs; cbn [efind]; destruct (label_eqb (lden h) l); [reflexivity|apply Hs0].
Qed.

Lemma tldist_of l : Forall tdist l -> tldist (tl_of l).
Proof. induction 1 as [|t r Ht _ IH]; cbn; [exact I|split; assumption]. Qed.

Lemma tldist_list ts : tldist ts -> Forall tdist (tl_list ts).
Proof. induction ts as [|t r IH] using tlist_spine; cbn; [constructor|intros [Ht Hr]; constructor; [exact Ht|exact (IH Hr)]]. Qed.

(** *** The relation between a target and its image *)

Variables X Y : radj T.
Variable f : lexp -> nat -> option (lexp * nat).
Variable nb dl : nat.
Hypothesis Hf : forall g i p, f g i = Some p ->
  rapply X (mk_rvar (lden (fst p)) (snd p)) = rapply Y (mk_rvar (lden g) i).
Hypothesis Hn : forall v, v_label v <> None -> rapply X v = rapply Y v.
Hypothesis Hb : forall i, nb <= i -> rapply X (mk_rvar None (i - dl)) = rapply Y (mk_rvar None i).
Hypothesis Hdl : dl <= nb.

Definition trel (t t' : ntgt) : Prop :=
  cres X (rtarget_result (tden t')) = cres Y (rtarget_result (tden t)).

Lemma rtv_rel t t' : rtv f t = Some t' -> tdist t' /\ trel t t'.
Proof.
  destruct t as [g i|u w b]; cbn [rtv]; [|discriminate].
  destruct (f g i) as [p|] eqn:E; [|discriminate]; cbn [option_map]; intros H; injection H as <-.
  split; [exact I|]; unfold trel; cbn [Normalise.tden rtarget_result cres]; exact (Hf g i p E).
Qed.

(** The default targets from [nbl] on, moved down by [d]. *)
Definition dflt (g : lexp) (nbl d : nat) : Prop :=
  forall i, nbl <= i -> rapply X (mk_rvar (lden g) (i - d)) = rapply Y (mk_rvar (lden g) i).

Lemma lsem_rel (h : ntgt -> option ntgt) g ts m k d l' :
  omapl h (expl g ts m k) = Some l' ->
  (forall t t', h t = Some t' -> trel t t') ->
  dflt g (m + k) d -> d <= m + k ->
  forall j, cres X (lsem (lden g) l' (m + k - d) j) = cres Y (lsem (lden g) ts m j).
Proof.
  intros E Hh Hd Hle j; destruct (omapl_nth h _ _ E) as [Hlen Hnth].
  unfold expl in Hlen, Hnth; rewrite length_app, length_map, length_seq in Hlen, Hnth.
  unfold Normalise.lsem; rewrite Hlen.
  destruct (Nat.ltb_spec j (List.length ts + k)) as [Hj|Hj].
  - pose proof (Hh _ _ (Hnth j (NVar LNone 0) (NVar LNone 0) Hj)) as R; unfold trel in R; rewrite R.
    destruct (Nat.ltb_spec j (List.length ts)) as [Hj2|Hj2].
    + rewrite app_nth1 by exact Hj2; reflexivity.
    + rewrite app_nth2 by exact Hj2.
      rewrite (nth_indep _ (NVar LNone 0) (NVar g 0)) by (rewrite length_map, length_seq; lia).
      rewrite (map_nth (NVar g)), seq_nth by lia; cbn [Normalise.tden rtarget_result].
      do 3 f_equal; lia.
  - destruct (Nat.ltb_spec j (List.length ts)) as [Hj2|Hj2]; [lia|]; cbn [cres].
    replace (j - (List.length ts + k) + (m + k - d)) with (j - List.length ts + m - d) by lia.
    apply Hd; lia.
Qed.

(** A tail and its image. *)
Lemma tail_map_rel A A' : sdistd A -> settled_tail A = true -> tail_map F f nb dl A = Some A' ->
  sdistd A' /\ rcompose X (sden A') = rcompose Y (sden A).
Proof.
  intros HA Hst; unfold tail_map.
  destruct (sfind F LNone A) as [e|] eqn:Ef; [|discriminate].
  pose proof (sfind_sound lenv F HF _ _ _ Ef) as He; cbn [Normalise.lden] in He.
  destruct (ofe e) as [ts m] eqn:Eo.
  destruct (omapl (rtv f) (expl LNone (tl_list ts) m (nb - m))) as [l'|] eqn:El; [|discriminate]; cbn [obind].
  intros Hs.
  assert (Hl' : Forall tdist l').
  { apply Forall_forall; intros y Hy; destruct (omapl_in _ _ _ _ El Hy) as [x [_ Hx]]; exact (proj1 (rtv_rel _ _ Hx)). }
  pose proof (sset_dd lenv tenv aenv penv F HF ntm Hntm LNone (tl_of l') _ SNil A' I (tldist_of _ Hl') Hs) as HA'.
  split; [exact HA'|].
  destruct (sset_sound lenv tenv aenv penv F HF ntm Hntm LNone (tl_of l') _ SNil A' I Hs) as [_ Hsem].
  apply rextensionality; intros [l j]; rewrite !rapply_compose_cres.
  rewrite !(rapply_sden lenv tenv aenv penv) by (apply sdistd_sdist; assumption); cbn [v_label v_index].
  rewrite Hsem; cbn [Normalise.lden]; destruct l as [x|]; cbn [label_eqb].
  - assert (E : esem (Some x) (sget (Some x) A) j = inl (mk_rvar (Some x) j)).
    { pose proof (rapply_sden lenv tenv aenv penv A (mk_rvar (Some x) j) (sdistd_sdist lenv _ HA)) as R.
      cbn [v_label v_index] in R; rewrite <- R.
      rewrite (named_sdrop_none lenv tenv aenv penv A (mk_rvar (Some x) j)) by discriminate.
      unfold settled_tail in Hst; apply andb_true_iff in Hst as [_ Hst].
      destruct (sdrop_none A); [|discriminate]; apply rapply_identity. }
    rewrite E; cbn [Normalise.sget Normalise.esem cres]; apply Hn; discriminate.
  - rewrite <- He, <- (esem_ofe lenv tenv aenv penv ntm Hntm None e j), Eo, !(esem_lsem lenv tenv aenv penv), tl_list_of.
    apply (lsem_rel (rtv f) LNone (tl_list ts) m (nb - m) dl l' El).
    + intros t t' Ht; exact (proj2 (rtv_rel _ _ Ht)).
    + intros i Hi; apply Hb; lia.
    + lia.
Qed.

(** A term whose tail is replaced by an equivalent one. *)
Lemma tset_rel t A A' : ttail t = Some A -> tdist t ->
  (exists u w b, t = NBind u w b /\ u < ntm) ->
  sdistd A' -> rcompose X (sden A') = rcompose Y (sden A) ->
  tdist (tset t A') /\ trel t (tset t A').
Proof.
  intros Et Hd [u [w [b [-> Hu]]]] HA' E; unfold trel.
  destruct (nth_error tenv u) as [y|] eqn:Ey; [|apply nth_error_None in Ey; lia].
  destruct w as [N|A0 L a w0]; cbn [ttail] in Et.
  - destruct b as [n|]; [|discriminate]; injection Et as ->; cbn [tset].
    split; [exact HA'|].
    rewrite !(tden_bind lenv tenv aenv penv _ _ _ y Ey); cbn [rtarget_result cres].
    rewrite !rpcompose_compose, !wden_end, E; reflexivity.
  - injection Et as ->; cbn [tset]; destruct Hd as [_ Hw0].
    split; [split; assumption|].
    rewrite !(tden_bind lenv tenv aenv penv _ _ _ y Ey); cbn [rtarget_result cres].
    rewrite !rpcompose_compose, !wden_atom, !rcompose_assoc, E; reflexivity.
Qed.

Lemma tm_t_rel t t' : tdist t -> tm_t F ntm f nb dl t = Some t' -> tdist t' /\ trel t t'.
Proof.
  intros Hd; destruct t as [g i|u w b].
  - exact (rtv_rel _ _).
  - assert (Hgen : (if u <? ntm then
                      match ttail (NBind u w b) with
                      | Some A => if settled_tail A then option_map (tset (NBind u w b)) (tail_map F f nb dl A) else None
                      | None => None
                      end
                    else None) = Some t' -> tdist t' /\ trel (NBind u w b) t').
    { destruct (Nat.ltb_spec u ntm) as [Hu|Hu]; [|discriminate].
      destruct (ttail (NBind u w b)) as [A|] eqn:Et; [|discriminate].
      destruct (settled_tail A) eqn:Es; [|discriminate].
      destruct (tail_map F f nb dl A) as [A'|] eqn:Em; [|discriminate]; cbn [option_map]; intros H; injection H as <-.
      assert (HA : sdistd A).
      { destruct w as [N|A0 L a w0]; cbn [ttail] in Et; [destruct b; [injection Et as <-; exact Hd|discriminate]|].
        injection Et as <-; exact (proj1 Hd). }
      destruct (tail_map_rel A A' HA Es Em) as [HA' E].
      exact (tset_rel _ A A' Et Hd (ex_intro _ u (ex_intro _ w (ex_intro _ b (conj eq_refl Hu)))) HA' E). }
    destruct w as [[|h ts m r]|A L a w0]; try exact Hgen.
    destruct b as [n|]; [exact Hgen|]; cbn [tm_t].
    destruct (Nat.ltb_spec u ntm) as [Hu|Hu]; [|discriminate]; intros H; injection H as <-.
    split; [exact I|]; unfold trel.
    destruct (nth_error tenv u) as [y|] eqn:Ey; [|apply nth_error_None in Ey; lia].
    rewrite (tden_bind lenv tenv aenv penv u (WEnd SNil) None y Ey); cbn [rtarget_result cres bden].
    rewrite (wden_id lenv tenv aenv penv), !rpcompose_identity; f_equal; f_equal; apply rpcompose_named, Hn.
Qed.

Lemma efind_omapl (G : lexp -> option (lexp * tlist * nat)) l :
  (forall g e, G g = Some e -> fst (fst e) = g) ->
  forall labs es, omapl G labs = Some es ->
  (efind l es = None /\ forall g, In g labs -> lden g <> l)
  \/ (exists g ts m, In g labs /\ lden g = l /\ G g = Some (g, ts, m) /\ efind l es = Some (ts, m)).
Proof.
  intros HG; induction labs as [|g r IH]; intros es; cbn [omapl].
  - intros H; injection H as <-; left; split; [reflexivity|intros g []].
  - destruct (G g) as [[[h ts] m]|] eqn:Eg; [|discriminate].
    destruct (omapl G r) as [es'|] eqn:Er; [|discriminate]; intros H; injection H as <-.
    pose proof (HG _ _ Eg) as Eh; cbn [fst] in Eh; subst h; cbn [efind].
    destruct (label_eqb_spec (lden g) l) as [E|E].
    + right; exists g, ts, m; split; [left; reflexivity|split; [exact E|split; [exact Eg|reflexivity]]].
    + destruct (IH es' eq_refl) as [[H1 H2]|[g' [ts' [m' [H1 [H2 [H3 H4]]]]]]].
      * left; split; [exact H1|]; intros g' [<-|Hin]; [exact E|exact (H2 g' Hin)].
      * right; exists g', ts', m'; split; [right; exact H1|split; [exact H2|split; [exact H3|exact H4]]].
Qed.

Theorem tmap_rel nbf extra s s' : nbf LNone = nb -> sdistd s -> tmap F ntm f nbf dl extra s = Some s' ->
  sdistd s' /\ forall v, cres X (rapply (sden s') v) = cres Y (rapply (sden s) v).
Proof.
  intros Enb Hs; unfold tmap.
  set (G := fun g => match sfind F g s with
                     | Some e => let '(ts, m) := ofe e in
                                 let k := nbf g - m in
                                 option_map (fun l => (g, tl_of l, m + k - match g with LNone => dl | _ => 0 end))
                                            (omapl (tm_t F ntm f (nbf LNone) dl) (expl g (tl_list ts) m k))
                     | None => None
                     end).
  set (labs := nodup_l (LNone :: seg_labels s ++ extra) []).
  change (obind (omapl G labs) (mkseg F) = Some s' ->
          sdistd s' /\ forall v, cres X (rapply (sden s') v) = cres Y (rapply (sden s) v)).
  destruct (omapl G labs) as [es|] eqn:Ees; [|discriminate]; cbn [obind]; intros Hmk.
  assert (HGl : forall g e, G g = Some e -> fst (fst e) = g).
  { intros g e; unfold G; destruct (sfind F g s) as [e0|]; [|discriminate]; destruct (ofe e0) as [ts m].
    cbn zeta; destruct (omapl (tm_t F ntm f (nbf LNone) dl) _) as [l0|]; cbn [option_map]; [|discriminate].
    intros H; inversion H; reflexivity. }
  (* what an entry of the result is *)
  assert (HGe : forall g ts' m', G g = Some (g, ts', m') ->
            tldist ts' /\ forall j, cres X (esem (lden g) (Some (ts', m')) j) = cres Y (esem (lden g) (sget (lden g) s) j)).
  { intros g ts' m'; unfold G; destruct (sfind F g s) as [e|] eqn:Ef; [|discriminate].
    pose proof (sfind_sound lenv F HF _ _ _ Ef) as He; destruct (ofe e) as [ts m] eqn:Eo; cbn zeta.
    destruct (omapl (tm_t F ntm f (nbf LNone) dl) (expl g (tl_list ts) m (nbf g - m))) as [l'|] eqn:El; [|discriminate].
    cbn [option_map]; intros H; injection H as <- <-.
    assert (Hts : Forall tdist (tl_list ts)).
    { destruct e as [[ts0 m0]|]; cbn [ofe] in Eo; injection Eo as <- <-; [|constructor].
      apply Forall_forall; intros t Ht; symmetry in He.
      exact (proj2 (proj1 (sdistd_iff lenv s) Hs) t (sget_stargets lenv _ _ _ _ He t Ht)). }
    assert (Hex : forall t t', In t (expl g (tl_list ts) m (nbf g - m)) ->
              tm_t F ntm f (nbf LNone) dl t = Some t' -> tdist t' /\ trel t t').
    { intros t t' Hin; rewrite Enb; apply tm_t_rel.
      unfold expl in Hin; apply in_app_or in Hin as [Hin|Hin]; [exact (proj1 (Forall_forall _ _) Hts t Hin)|].
      apply in_map_iff in Hin as [i [<- _]]; exact I. }
    split.
    - apply tldist_of, Forall_forall; intros y Hy; destruct (omapl_in _ _ _ _ El Hy) as [x [Hx1 Hx2]].
      exact (proj1 (Hex x y Hx1 Hx2)).
    - intros j; rewrite <- He, <- (esem_ofe lenv tenv aenv penv ntm Hntm (lden g) e j), Eo.
      rewrite !(esem_lsem lenv tenv aenv penv), tl_list_of.
      (* the per-element relation only matters for the elements of the list *)
      destruct (omapl_nth _ _ _ El) as [Hlen Hnth].
      set (d := match g with LNone => dl | _ => 0 end).
      assert (Hd : dflt g (m + (nbf g - m)) d /\ d <= m + (nbf g - m)).
      { unfold dflt, d; destruct g as [|x|n]; cbn [Normalise.lden].
        - split; [intros i Hi; apply Hb; lia|lia].
        - split; [intros i Hi; rewrite Nat.sub_0_r; apply Hn; discriminate|lia].
        - split; [intros i Hi; rewrite Nat.sub_0_r; apply Hn; discriminate|lia]. }
      unfold Normalise.lsem; rewrite Hlen; unfold expl in Hlen, Hnth |- *.
      rewrite length_app, length_map, length_seq in Hnth |- *.
      destruct (Nat.ltb_spec j (List.length (tl_list ts) + (nbf g - m))) as [Hj|Hj].
      + pose proof (Hnth j (NVar LNone 0) (NVar LNone 0) Hj) as Ej.
        assert (Hin : In (nth j (tl_list ts ++ map (NVar g) (seq m (nbf g - m))) (NVar LNone 0))
                         (expl g (tl_list ts) m (nbf g - m))).
        { apply nth_In; unfold expl; rewrite length_app, length_map, length_seq; exact Hj. }
        pose proof (proj2 (Hex _ _ Hin Ej)) as R; unfold trel in R; rewrite R.
        destruct (Nat.ltb_spec j (List.length (tl_list ts))) as [Hj2|Hj2].
        * rewrite app_nth1 by exact Hj2; reflexivity.
        * rewrite app_nth2 by exact Hj2.
          rewrite (nth_indep _ (NVar LNone 0) (NVar g 0)) by (rewrite length_map, length_seq; lia).
          rewrite (map_nth (NVar g)), seq_nth by lia; cbn [Normalise.tden rtarget_result].
          do 3 f_equal; lia.
      + destruct (Nat.ltb_spec j (List.length (tl_list ts))) as [Hj2|Hj2]; [lia|]; cbn [cres].
        replace (j - (List.length (tl_list ts) + (nbf g - m)) + (m + (nbf g - m) - d))
          with (j - List.length (tl_list ts) + m - d) by lia.
        apply (proj1 Hd); lia. }
  assert (HT : Forall (fun e => tldist (snd (fst e))) es).
  { apply Forall_forall; intros [[h ts] m] Hin; cbn [fst snd].
    destruct (omapl_in _ _ _ _ Ees Hin) as [g [_ Hg]]; pose proof (HGl _ _ Hg) as E; cbn [fst] in E; subst h.
    exact (proj1 (HGe _ _ _ Hg)). }
  destruct (mkseg_spec es s' Hmk HT) as [Hs' Hsem]; split; [exact Hs'|].
  intros [l j]; rewrite !(rapply_sden lenv tenv aenv penv) by (apply sdistd_sdist; assumption).
  cbn [v_label v_index]; rewrite Hsem.
  destruct (efind_omapl G l HGl labs es Ees) as [[E1 E2]|[g [ts [m [H1 [H2 [H3 H4]]]]]]].
  - rewrite E1.
    assert (El : sget l s = None).
    { destruct (sget l s) as [[ts m]|] eqn:Eg; [|reflexivity]; exfalso.
      destruct (sget_label lenv l s ts m Eg) as [h [Hh [Hl _]]].
      apply (E2 h); [|exact Hl]; apply nodup_l_in0; right; apply in_or_app; left; exact Hh. }
    rewrite El; cbn [Normalise.esem cres]; apply Hn; cbn [v_label].
    intros ->; apply (E2 LNone); [apply nodup_l_in0; left; reflexivity|reflexivity].
  - rewrite H4; subst l; exact (proj2 (HGe _ _ _ H3) j).
Qed.

End Sound.

(** ** The two uses *)

Section Routes.

Variable F : order.
Variable ntm : nat.

(** Every variable target goes on as the representative of its key in
    the word [K] that follows. *)
Definition reroute_g (s : seg) (K : lword) : option seg :=
  match kmap_g F K with
  | [] => Some s
  | km =>
      let f := fun g i => Some (match find (fun p => veqb (fst p) (g, i)) km with Some p => snd p | None => (g, i) end) in
      let nbf := fun g => fold_right (fun p acc => if lexp_eqb (fst (fst p)) g then Nat.max (S (snd (fst p))) acc else acc) 0 km in
      tmap F ntm f nbf 0 (map (fun p => fst (fst p)) km) s
  end.

(** The bound variables that the targets of a segment mention. *)
Fixpoint thits (ts : list ntgt) : list nat :=
  match ts with
  | [] => []
  | NVar LNone j :: r => j :: thits r
  | NVar _ _ :: r => thits r
  | t :: r => match ttail t with Some A => bvs (tl_list (fst (bent F A))) | None => [] end ++ thits r
  end.

(** The bound variables below [M] that a segment sends something to, in
    the order they are first used; the ones nothing is sent to are left
    out.  The segment with them numbered in that order, and the renaming
    [io] from the new numbers to the old ones: [s] is [io ∘ s'].
    [clim] is the number of bound variables that may be renumbered (in
    front of a lifted atom, the ones its lifts pass around), [n1] the
    number of bound variables the next segment has an entry for. *)
Definition renum (clim : option nat) (n1 : nat) (s : seg) : option (seg * seg) :=
  let m := snd (bent F s) in
  let Mf := fold_right (fun t acc => match ttail t with Some A => Nat.max (snd (bent F A)) acc | None => acc end)
              (fold_right (fun j acc => Nat.max (S j) acc) (Nat.max m n1) (thits (stargets s))) (stargets s) in
  let hits := flat_map (fun t => match t with
                                 | NVar LNone j => [j]
                                 | NVar _ _ => []
                                 | _ => match ttail t with
                                        | Some A => bvs (tl_list (fst (bent F A))) ++ seq (snd (bent F A)) (Mf - snd (bent F A))
                                        | None => []
                                        end
                                 end) (stargets s) in
  let M := match clim with Some c => Nat.min c Mf | None => Mf end in
  let ord := nodup_nat (filter (fun j => j <? M) (hits ++ seq m (Mf - m))) [] in
  if list_eq_dec Nat.eq_dec ord (seq 0 M) then Some (s, SNil)
  else if negb (List.length ord <=? M) then Some (s, SNil)
  else
    let dl := M - List.length ord in
    let f := fun g i => match g with
                        | LNone => if i <? M then (if mem i ord then Some (LNone, index_of i ord 0) else None)
                                   else Some (LNone, i - dl)
                        | _ => Some (g, i)
                        end in
    match tmap F ntm f (fun g => match g with LNone => M | _ => 0 end) dl [] s, mkseg F [(LNone, bvars ord, M)] with
    | Some s', Some io => Some (s', io)
    | _, _ => Some (s, SNil)
    end.

End Routes.

Lemma vmin_in F l : forall w, vmin F l = Some w -> In w l.
Proof.
  induction l as [|v r IH]; intros w; unfold vmin; cbn [fold_right]; [discriminate|].
  fold (vmin F r); destruct (vmin F r) as [w0|].
  - destruct (vless F v w0); intros H; injection H as <-; [left; reflexivity|right; apply IH; reflexivity].
  - intros H; injection H as <-; left; reflexivity.
Qed.

Lemma veqb_eq a b : veqb a b = true -> a = b.
Proof.
  destruct a as [g i], b as [g' i']; unfold veqb; cbn [fst snd]; intros H.
  apply andb_true_iff in H as [H1 H2]; apply lexp_eqb_eq in H1; apply Nat.eqb_eq in H2; subst; reflexivity.
Qed.

Lemma lexp_eqb_refl g : lexp_eqb g g = true.
Proof. destruct g as [|s|n]; cbn; [reflexivity|apply String.eqb_refl|apply Nat.eqb_refl]. Qed.

Lemma veqb_refl a : veqb a a = true.
Proof. destruct a as [g i]; unfold veqb; cbn [fst snd]; rewrite lexp_eqb_refl, Nat.eqb_refl; reflexivity. Qed.

Lemma kmap_g_keys F K v w : In (v, w) (kmap_g F K) ->
  v = w \/ exists k, vfollow F K (fst v) (snd v) = Some k /\ vfollow F K (fst w) (snd w) = Some k.
Proof.
  unfold kmap_g; set (keyed := map (fun v => (v, vfollow F K (fst v) (snd v))) (nodup_v (kcands F K) [])).
  intros H; apply filter_In in H as [H _]; apply in_map_iff in H as [vk [E Hvk]]; injection E as <- <-.
  assert (Hk : forall p, In p keyed -> snd p = vfollow F K (fst (fst p)) (snd (fst p))).
  { intros p Hp; apply in_map_iff in Hp as [x [<- _]]; reflexivity. }
  assert (Hgen : forall p, In p keyed -> okey_eqb (snd p) (snd vk) = true ->
            exists k, vfollow F K (fst (fst vk)) (snd (fst vk)) = Some k /\ vfollow F K (fst (fst p)) (snd (fst p)) = Some k).
  { intros p Hp Eq; apply okey_eqb_eq in Eq as [k [E1 E2]]; exists k.
    rewrite <- (Hk vk Hvk), <- (Hk p Hp); split; assumption. }
  destruct (vmin F _) as [w0|] eqn:Em.
  - apply vmin_in in Em; apply in_map_iff in Em as [p [<- Hp]]; apply filter_In in Hp as [Hp Hq].
    apply andb_true_iff in Hq as [_ Hq]; right; exact (Hgen p Hp Hq).
  - destruct (filter (fun p => lexp_eqb (fst (fst p)) LNone && okey_eqb (snd p) (snd vk)) keyed) as [|p r] eqn:Ef;
      [left; reflexivity|].
    assert (Hp : In p (filter (fun p => lexp_eqb (fst (fst p)) LNone && okey_eqb (snd p) (snd vk)) keyed))
      by (rewrite Ef; left; reflexivity).
    apply filter_In in Hp as [Hp Hq]; apply andb_true_iff in Hq as [_ Hq]; right; exact (Hgen p Hp Hq).
Qed.

Lemma index_of_spec x l : mem x l = true -> forall k,
  k <= index_of x l k /\ index_of x l k < k + List.length l /\ nth (index_of x l k - k) l 0 = x.
Proof.
  induction l as [|y r IH]; [discriminate|]; unfold mem; cbn [existsb index_of List.length]; intros H k.
  destruct (Nat.eqb_spec x y) as [->|Hne]; [replace (k - k) with 0 by lia; cbn; repeat split; lia|].
  cbn [orb] in H; destruct (IH H (S k)) as [H1 [H2 H3]]; split; [lia|split; [lia|]].
  replace (index_of x r (S k) - k) with (S (index_of x r (S k) - S k)) by lia; exact H3.
Qed.

Section RoutesSound.

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
Local Notation sden := (sden lenv tenv aenv penv).
Local Notation sdistd := (sdistd lenv).
Local Notation lwden := (lwden lenv tenv aenv penv).
Local Notation lwdist := (lwdist lenv).

Theorem reroute_g_sound s K s' : sdistd s -> lwdist K -> reroute_g F ntm s K = Some s' ->
  sdistd s' /\ rcompose (lwden K) (sden s') = rcompose (lwden K) (sden s).
Proof.
  intros Hs HK; unfold reroute_g; destruct (kmap_g F K) as [|p0 km0] eqn:Ek.
  { intros H; injection H as <-; split; [exact Hs|reflexivity]. }
  set (km := p0 :: km0) in *; intros H.
  set (f := fun g i => Some (match find (fun p => veqb (fst p) (g, i)) km with Some p => snd p | None => (g, i) end)) in H.
  set (nbf := fun g => fold_right (fun p acc => if lexp_eqb (fst (fst p)) g then Nat.max (S (snd (fst p))) acc else acc) 0 km) in H.
  assert (Hf : forall g i p, f g i = Some p ->
            rapply (lwden K) (mk_rvar (lden (fst p)) (snd p)) = rapply (lwden K) (mk_rvar (lden g) i)).
  { intros g i p E; unfold f in E.
    destruct (find (fun p => veqb (fst p) (g, i)) km) as [q|] eqn:Efd; injection E as <-; [|reflexivity].
    apply find_some in Efd as [Hq Ev]; apply veqb_eq in Ev; destruct q as [v w]; cbn [fst snd] in *; subst v.
    rewrite <- Ek in Hq; destruct (kmap_g_keys F K _ _ Hq) as [<-|[k [E1 E2]]]; [reflexivity|].
    symmetry; exact (vfollow_sound lenv tenv aenv penv F HF ntm Hntm K HK _ _ _ _ k E1 E2). }
  destruct (tmap_rel lenv tenv aenv penv F HF ntm Hntm (lwden K) (lwden K) f (nbf LNone) 0 Hf
              (fun _ _ => eq_refl) (fun i _ => f_equal (fun j => rapply (lwden K) (mk_rvar None j)) (Nat.sub_0_r i))
              (Nat.le_0_l _) nbf _ s s' eq_refl Hs H) as [Hs' Hrel].
  split; [exact Hs'|]; apply rextensionality; intros v; rewrite !rapply_compose_cres; apply Hrel.
Qed.

Theorem renum_sound clim n1 s s' io : sdistd s -> renum F ntm clim n1 s = Some (s', io) ->
  sdistd s' /\ sdistd io /\ rcompose (sden io) (sden s') = sden s.
Proof.
  intros Hs; unfold renum.
  assert (Hid : Some (s, SNil) = Some (s', io) -> sdistd s' /\ sdistd io /\ rcompose (sden io) (sden s') = sden s).
  { intros H; injection H as <- <-; split; [exact Hs|split; [exact I|]].
    change (sden SNil) with (@ridentity T); apply rcompose_identity_l. }
  set (m := snd (bent F s)).
  set (Mf := fold_right _ _ (stargets s)).
  set (hits := flat_map _ (stargets s)).
  set (M := match clim with Some c => Nat.min c Mf | None => Mf end).
  set (ord := nodup_nat (filter (fun j => j <? M) (hits ++ seq m (Mf - m))) []).
  destruct (list_eq_dec Nat.eq_dec ord (seq 0 M)); [exact Hid|].
  destruct (Nat.leb_spec (List.length ord) M) as [Hlen|Hlen]; cbn [negb]; [|exact Hid].
  set (dl := M - List.length ord).
  set (f := fun g i => match g with
                       | LNone => if i <? M then (if mem i ord then Some (LNone, index_of i ord 0) else None)
                                  else Some (LNone, i - dl)
                       | _ => Some (g, i)
                       end).
  destruct (tmap F ntm f _ dl [] s) as [s0|] eqn:Et; [|exact Hid].
  destruct (mkseg F [(LNone, bvars ord, M)]) as [io0|] eqn:Eio; [|exact Hid].
  intros H; injection H as <- <-.
  assert (Hbv : tldist lenv (bvars ord)).
  { unfold bvars; apply tldist_of, Forall_forall; intros t Ht; apply in_map_iff in Ht as [j [<- _]]; exact I. }
  assert (HFa : Forall (fun e : lexp * tlist * nat => tldist lenv (snd (fst e))) [(LNone, bvars ord, M)])
    by (constructor; [exact Hbv|constructor]).
  destruct (mkseg_spec lenv tenv aenv penv F HF ntm Hntm _ io0 Eio HFa) as [Hio Hsem].
  assert (Hio_b : forall k, rapply (sden io0) (mk_rvar None k)
                    = inl (mk_rvar None (if k <? List.length ord then nth k ord 0 else k - List.length ord + M))).
  { intros k; rewrite (rapply_sden lenv tenv aenv penv) by (apply sdistd_sdist; exact Hio); cbn [v_label v_index].
    rewrite Hsem; cbn [efind Normalise.lden label_eqb]; rewrite (esem_lsem lenv tenv aenv penv).
    unfold bvars; rewrite tl_list_of; unfold Normalise.lsem; rewrite length_map.
    destruct (k <? List.length ord) eqn:Ek; [|reflexivity].
    change (NVar LNone 0) with ((NVar LNone) 0); rewrite (map_nth (NVar LNone)); reflexivity. }
  assert (Hio_n : forall v, v_label v <> None -> rapply (sden io0) v = inl v).
  { intros [[x|] j] Hv; [|destruct (Hv eq_refl)].
    rewrite (rapply_sden lenv tenv aenv penv) by (apply sdistd_sdist; exact Hio); cbn [v_label v_index].
    rewrite Hsem; reflexivity. }
  assert (Hf : forall g i p, f g i = Some p ->
            rapply (sden io0) (mk_rvar (lden (fst p)) (snd p)) = rapply (@ridentity T) (mk_rvar (lden g) i)).
  { intros g i p; rewrite rapply_identity; unfold f; destruct g as [|x|n0].
    - cbn [Normalise.lden]; destruct (Nat.ltb_spec i M) as [Hi|Hi].
      + destruct (mem i ord) eqn:Em; [|discriminate]; intros E; injection E as <-; cbn [fst snd Normalise.lden].
        destruct (index_of_spec i ord Em 0) as [_ [H2 H3]]; rewrite Hio_b.
        rewrite (proj2 (Nat.ltb_lt _ _)) by lia; rewrite Nat.sub_0_r in H3; rewrite H3; reflexivity.
      + intros E; injection E as <-; cbn [fst snd Normalise.lden]; rewrite Hio_b.
        destruct (Nat.ltb_spec (i - dl) (List.length ord)) as [Hc|Hc]; [unfold dl in Hc; lia|].
        do 2 f_equal; unfold dl; lia.
    - intros E; injection E as <-; apply Hio_n; discriminate.
    - intros E; injection E as <-; apply Hio_n; discriminate. }
  destruct (tmap_rel lenv tenv aenv penv F HF ntm Hntm (sden io0) ridentity f M dl Hf
              (fun v Hv => eq_trans (Hio_n v Hv) (eq_sym (rapply_identity v)))) with (nbf := fun g => match g with LNone => M | _ => 0 end) (extra := @nil lexp) (s := s) (s' := s0) as [Hs0 Hrel];
    try assumption; try reflexivity.
  - intros i Hi; rewrite Hio_b, rapply_identity.
    destruct (Nat.ltb_spec (i - dl) (List.length ord)) as [Hc|Hc]; [unfold dl in Hc; lia|].
    do 2 f_equal; unfold dl; lia.
  - unfold dl; lia.
  - split; [exact Hs0|split; [exact Hio|]].
    apply rextensionality; intros v; rewrite rapply_compose_cres, Hrel; apply cres_id.
Qed.

End RoutesSound.
