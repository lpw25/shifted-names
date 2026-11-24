(** * Maps over payloads

    [pmap h a] is the adjustment [a] with every payload term [u] (at every
    depth) replaced by [h u]: what an adjustment of one family becomes in
    another, along a map [h] that keeps scopes.  Under a binder of another
    sort (a type binder over terms), a substitution's payloads are mapped
    by the weakening of that sort.

    The map is structural on the representation, so it keeps everything
    but the terms: the counts, the shapes, the entries.  Its action is the
    original's with the terms mapped ([napply_nmap]), and it commutes with
    the operations on adjustments (by extensionality, [rextensionality]). *)

From Stdlib Require Import PArith NArith Arith Lia List Bool StrictProp.
From ShiftedNames.Core Require Import Normalise HShow Braun HShowB Trie Label Var Counts Based Skew ATrie Repr Point
  Deep Adjustment Laws Scoped Indexed Syntax Subst.
Import ListNotations.

(** ** Maps over the containers *)

Section Maps.

Context {X Y : Type} (g : X -> Y).

Fixpoint ktmap (t : ktree X) : ktree Y :=
  match t with KLeaf x => KLeaf (g x) | KNode a x l r => KNode a (g x) (ktmap l) (ktmap r) end.

Fixpoint spmap (s : kspine X) : kspine Y :=
  match s with SNil => SNil | SCons w t s' => SCons w (ktmap t) (spmap s') end.

Definition kmap (s : kseq X) : kseq Y :=
  match s with KNil => KNil | KSeq a w t s' => KSeq a w (ktmap t) (spmap s') end.

Fixpoint amap (t : atrie X) : atrie Y :=
  match t with AEmpty => AEmpty | ANode a l o r => ANode a (amap l) (option_map g o) (amap r) end.

End Maps.

Section MapLaws.

Context {X Y : Type} {BX : Based X} {BY : Based Y} (g : X -> Y).
Hypothesis g_uses : forall x, uses (g x) = uses x.
Hypothesis g_unshift : forall d x, g (unshift d x) = unshift d (g x).

Lemma lminc_map l : lminc (map g l) = lminc l.
Proof. induction l as [|x l IH]; [reflexivity|]; unfold lminc in *; cbn [map fold_right]; rewrite g_uses, IH; reflexivity. Qed.

Lemma map_unshift_g a l : map (unshift a) (map g l) = map g (map (unshift a) l).
Proof. rewrite !map_map; apply map_ext; intros; symmetry; apply g_unshift. Qed.

Lemma option_map_unshift_g a o : option_map (unshift a) (option_map g o) = option_map g (option_map (unshift a) o).
Proof. destruct o; cbn; [rewrite g_unshift|]; reflexivity. Qed.

Lemma ktlist_map t : ktlist (ktmap g t) = map g (ktlist t).
Proof.
  induction t as [x|a x l IHl r IHr]; cbn [ktlist ktmap]; [reflexivity|].
  rewrite IHl, IHr, <- map_app.
  change (g x :: map g (ktlist l ++ ktlist r)) with (map g (x :: ktlist l ++ ktlist r)); apply map_unshift_g.
Qed.

Lemma splist_map s : splist (spmap g s) = map g (splist s).
Proof. induction s as [|w t s IH]; cbn [splist spmap]; [reflexivity|]; rewrite ktlist_map, IH, map_app; reflexivity. Qed.

Lemma klist_map s : klist (kmap g s) = map g (klist s).
Proof.
  destruct s as [|a w t s]; [reflexivity|]; cbn [klist kmap].
  change (SCons w (ktmap g t) (spmap g s)) with (spmap g (SCons w t s)); rewrite splist_map; apply map_unshift_g.
Qed.

Lemma aelems_map t : aelems (amap g t) = map g (aelems t).
Proof.
  induction t as [|a l IHl o r IHr]; cbn [aelems amap]; [reflexivity|].
  rewrite IHl, IHr; replace (oelems (option_map g o)) with (map g (oelems o)) by (destruct o; reflexivity).
  rewrite <- !map_app; apply map_unshift_g.
Qed.

Lemma ksann_map s : ksann (kmap g s) = ksann s.
Proof. destruct s; reflexivity. Qed.

Lemma aann_map t : aann (amap g t) = aann t.
Proof. destruct t; reflexivity. Qed.

Lemma ktnth_map t : forall w i, ktnth w (ktmap g t) i = option_map g (ktnth w t i).
Proof.
  induction t as [x|a x l IHl r IHr]; intros w i; cbn [ktnth ktmap]; [destruct i; reflexivity|].
  destruct i as [|j]; [cbn; rewrite g_unshift; reflexivity|].
  destruct (Nat.ltb j (Nat.div2 w)); [rewrite IHl|rewrite IHr]; apply option_map_unshift_g.
Qed.

Lemma spnth_map s : forall i, spnth (spmap g s) i = option_map g (spnth s i).
Proof.
  induction s as [|w t s IH]; intros i; cbn [spnth spmap]; [reflexivity|].
  destruct (Nat.ltb i w); [apply ktnth_map|apply IH].
Qed.

Lemma knth_map s i : knth (kmap g s) i = option_map g (knth s i).
Proof.
  destruct s as [|a w t s]; [reflexivity|]; cbn [knth kmap].
  change (SCons w (ktmap g t) (spmap g s)) with (spmap g (SCons w t s)); rewrite spnth_map; apply option_map_unshift_g.
Qed.

Lemma aget_map k t : aget k (amap g t) = option_map g (aget k t).
Proof.
  revert k; induction t as [|a l IHl o r IHr]; intros k; cbn [aget amap]; [reflexivity|].
  destruct k as [k|k|]; [rewrite IHr|rewrite IHl|]; apply option_map_unshift_g.
Qed.

Lemma klength_map s : klength (kmap g s) = klength s.
Proof.
  destruct s as [|a w t s]; [reflexivity|]; cbn [klength kmap]; f_equal.
  induction s as [|w' t' s IH]; cbn; [reflexivity|]; rewrite IH; reflexivity.
Qed.

Lemma kweights_map s : kweights (kmap g s) = kweights s.
Proof.
  destruct s as [|a w t s]; [reflexivity|]; cbn [kweights kmap]; f_equal.
  induction s as [|w' t' s IH]; cbn; [reflexivity|]; rewrite IH; reflexivity.
Qed.

Lemma ktinvb_map t : ktinvb (ktmap g t) = ktinvb t.
Proof.
  induction t as [x|a x l IHl r IHr]; [reflexivity|].
  cbn [ktmap]; cbn [ktinvb].
  change (KNode a (g x) (ktmap g l) (ktmap g r)) with (ktmap g (KNode a x l r)).
  rewrite ktlist_map, lminc_map, IHl, IHr; reflexivity.
Qed.

Lemma spinvb_map s : spinvb (spmap g s) = spinvb s.
Proof. induction s as [|w t s IH]; cbn [spinvb spmap]; [reflexivity|]; rewrite ktinvb_map, IH; reflexivity. Qed.

Lemma kinvb_map s : kinvb (kmap g s) = kinvb s.
Proof.
  destruct s as [|a w t s]; [reflexivity|].
  cbn [kmap]; cbn [kinvb].
  change (KSeq a w (ktmap g t) (spmap g s)) with (kmap g (KSeq a w t s)).
  rewrite klist_map, lminc_map, ktinvb_map, spinvb_map; reflexivity.
Qed.

Lemma ktshapeb_map t : forall w, ktshapeb w (ktmap g t) = ktshapeb w t.
Proof. induction t as [x|a x l IHl r IHr]; intros w; cbn [ktshapeb ktmap]; [reflexivity|]; rewrite IHl, IHr; reflexivity. Qed.

Lemma kshapeb_map s : kshapeb (kmap g s) = kshapeb s.
Proof.
  destruct s as [|a w t s]; [reflexivity|]; cbn [kshapeb kmap]; rewrite ktshapeb_map; f_equal.
  induction s as [|w' t' s IH]; cbn; [reflexivity|]; rewrite ktshapeb_map, IH; reflexivity.
Qed.

Lemma kgoodb_map s : kgoodb (kmap g s) = kgoodb s.
Proof. unfold kgoodb, kcanonb; rewrite kinvb_map, kshapeb_map, kweights_map, klength_map; reflexivity. Qed.

Lemma anonemptyb_map l o r : anonemptyb (amap g l) (option_map g o) (amap g r) = anonemptyb l o r.
Proof. destruct l, o, r; reflexivity. Qed.

Lemma ainvb_map t : ainvb (amap g t) = ainvb t.
Proof.
  induction t as [|a l IHl o r IHr]; [reflexivity|].
  cbn [amap]; cbn [ainvb].
  change (ANode a (amap g l) (option_map g o) (amap g r)) with (amap g (ANode a l o r)).
  rewrite aelems_map, lminc_map, anonemptyb_map, IHl, IHr; reflexivity.
Qed.

Lemma akeyed_map t : forall kf, akeyed kf (amap g t) = map (fun kx => (fst kx, g (snd kx))) (akeyed kf t).
Proof.
  induction t as [|a l IHl o r IHr]; intros kf; cbn [akeyed amap]; [reflexivity|].
  rewrite IHl, IHr.
  replace (match option_map g o with Some x => [(kf xH, x)] | None => [] end)
    with (map (fun kx => (fst kx, g (snd kx))) (match o with Some x => [(kf xH, x)] | None => [] end))
    by (destruct o; reflexivity).
  rewrite <- !map_app, !map_map; apply map_ext; intros [k x]; cbn; rewrite g_unshift; reflexivity.
Qed.

(** The folds of [Deep], over a map: transparent, so that a proof by
    recursion through payloads can call itself in [H]. *)
Section Folds.
Variables (F : counts -> X -> bool) (F' : counts -> Y -> bool).
Hypothesis H : forall B x, F' B (g x) = F B x.

Fixpoint ktallF_map (t : ktree X) : forall B, ktallF F' B (ktmap g t) = ktallF F B t.
Proof.
  destruct t as [x|a x l r]; intros B; cbn [ktallF ktmap]; [apply H|].
  rewrite H, (ktallF_map l), (ktallF_map r); reflexivity.
Defined.

Fixpoint spallF_map (s : kspine X) : forall B, spallF F' B (spmap g s) = spallF F B s.
Proof.
  destruct s as [|w t s]; intros B; cbn [spallF spmap]; [reflexivity|].
  rewrite ktallF_map, (spallF_map s); reflexivity.
Defined.

Definition kallF_map (s : kseq X) B : kallF F' B (kmap g s) = kallF F B s.
Proof. destruct s as [|a w t s]; cbn [kallF kmap]; [reflexivity|]; rewrite ktallF_map, spallF_map; reflexivity. Defined.

Fixpoint aallF_map (t : atrie X) : forall B, aallF F' B (amap g t) = aallF F B t.
Proof.
  destruct t as [|a l o r]; intros B; cbn [aallF amap]; [reflexivity|].
  rewrite (aallF_map l), (aallF_map r); destruct o; cbn [option_map]; [rewrite H|]; reflexivity.
Defined.

End Folds.

End MapLaws.

(** ** The map on the representation *)

Section NMap.

Context {A B : Type} (f : A -> B).

Fixpoint tmap (t : @Repr.target A) : @Repr.target B :=
  match t with TVar y j => TVar y j | TBind u rho => TBind (f u) (nmap rho) end
with nmap (a : @nadj A) : @nadj B :=
  match a with
  | NAdj r es => NAdj r (amap (fun e => match e with Entry h ts len p => Entry h (kmap tmap ts) len p end) es)
  end.

Definition emap (e : @entry A) : @entry B := match e with Entry h ts len p => Entry h (kmap tmap ts) len p end.

Lemma nmap_eq r es : nmap (NAdj r es) = NAdj r (amap emap es).
Proof. reflexivity. Qed.

Lemma tmap_uses t : uses (tmap t) = uses t.
Proof. destruct t as [y j|u [r es]]; reflexivity. Qed.

Lemma tmap_unshift d t : tmap (unshift d t) = unshift d (tmap t).
Proof. destruct t as [y j|u [r es]]; reflexivity. Qed.

Lemma kmap_klift d (s : kseq (@Repr.target A)) : kmap tmap (klift d s) = klift d (kmap tmap s).
Proof. destruct s; reflexivity. Qed.

Lemma emap_uses e : uses (emap e) = uses e.
Proof. destruct e as [h ts len p]; cbn [emap uses entry_based euses]; rewrite ksann_map; reflexivity. Qed.

Lemma emap_unshift d e : emap (unshift d e) = unshift d (emap e).
Proof. destruct e as [h ts len p]; cbn [emap unshift entry_based eunshift]; rewrite kmap_klift; reflexivity. Qed.

Definition resmap (r : @result A) : @result B :=
  match r with inl w => inl w | inr (u, rho) => inr (f u, nmap rho) end.

Lemma tresult_map t : tresult (tmap t) = resmap (tresult t).
Proof. destruct t; reflexivity. Qed.

Theorem napply_nmap a v : napply (nmap a) v = resmap (napply a v).
Proof.
  destruct a as [w es]; rewrite nmap_eq; cbn [napply].
  rewrite (aget_map emap emap_unshift); destruct (aget _ es) as [e|]; cbn [option_map]; [|reflexivity].
  destruct e as [h ts len p]; cbn [emap eapply].
  destruct (Nat.ltb _ _); [|reflexivity].
  rewrite (knth_map tmap tmap_unshift); destruct (knth ts _) as [t|]; cbn [option_map]; [|reflexivity].
  replace (tunshift w (tmap t)) with (tmap (tunshift w t)) by (destruct t as [y j|u [r0 es0]]; reflexivity).
  apply tresult_map.
Qed.

Lemma nroot_map a : nroot (nmap a) = nroot a.
Proof. destruct a; reflexivity. Qed.

Lemma strip_okb_map e : strip_okb (emap e) = strip_okb e.
Proof.
  destruct e as [h ts len p]; cbn [emap strip_okb].
  rewrite (knth_map tmap tmap_unshift); destruct (knth ts _) as [[y j|u rho]|]; reflexivity.
Qed.

Lemma entry_okb_map k e : entry_okb k (emap e) = entry_okb k e.
Proof.
  pose proof (strip_okb_map e) as Hs.
  destruct e as [h ts len p]; cbn [emap entry_okb] in *.
  rewrite (kgoodb_map tmap tmap_uses tmap_unshift), (klength_map tmap), Hs; reflexivity.
Qed.

Lemma forallb_map' {X0 Y0} (p : Y0 -> bool) (q : X0 -> Y0) l : List.forallb p (map q l) = List.forallb (fun x => p (q x)) l.
Proof. induction l as [|x l IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma nlocalb_map r es : nlocalb (NAdj r (amap emap es)) = nlocalb (NAdj r es).
Proof.
  cbn [nlocalb].
  rewrite (ainvb_map emap emap_uses emap_unshift), (akeyed_map emap emap_unshift), aann_map, forallb_map'.
  f_equal; f_equal; f_equal; induction (akeyed (fun k => k) es) as [|[k e] l IH]; [reflexivity|].
  cbn in IH |- *; rewrite entry_okb_map, IH; reflexivity.
Qed.

Theorem nwfc_nmap : forall a rt, nwfc rt (nmap a) = nwfc rt a.
Proof.
  fix IH 1; intros [r es] rt.
  rewrite nmap_eq, !nwfc_eq, nlocalb_map; f_equal.
  apply aallF_map; intros B0 [h ts len p]; cbn [emap].
  apply kallF_map; intros B1 [y j|u rho]; cbn [tmap]; [reflexivity|apply IH].
Qed.

Section Scoped.

Context {SA : TermScope A} {SB : TermScope B}.
Hypothesis f_scope : forall u, tscope (f u) = tscope u.

Lemma scoped_tail_nmap N M a : scoped_tail N M (nmap a) = scoped_tail N M a.
Proof.
  destruct a as [r es]; rewrite nmap_eq; cbn [scoped_tail].
  rewrite (aget_map emap emap_unshift); destruct (aget _ es) as [[h ts len p]|]; reflexivity.
Qed.

Theorem pscopedc_nmap : forall a M rt, pscopedc M rt (nmap a) = pscopedc M rt a.
Proof.
  fix IH 1; intros [r es] M rt.
  rewrite nmap_eq, !pscopedc_eq.
  apply aallF_map; intros B0 [h ts len p]; cbn [emap].
  apply kallF_map; intros B1 [[y|] j|u rho]; try reflexivity.
  change (tmap (TBind u rho)) with (TBind (f u) (nmap rho)).
  cbn [tscope_t]; rewrite f_scope, IH; f_equal.
  destruct rho as [r0 es0]; rewrite nmap_eq; cbn [scoped_tail].
  rewrite (aget_map emap emap_unshift); destruct (aget _ es0) as [[h0 ts0 len0 p0]|]; reflexivity.
Qed.

End Scoped.

End NMap.

(** ** On adjustments *)

Section RMap.

Context {A B : Type} (f : A -> B).

Definition rmap (a : radj A) : radj B :=
  mk_radj (nmap f (radj_n a)) (Is_true_s_intro (eq_trans (nwfc_nmap f _ _) (Is_true_s_elim (radj_ok a)))).

Definition rresmap (r : rresult A) : rresult B :=
  match r with inl w => inl w | inr (u, ρ) => inr (f u, rmap ρ) end.

Definition rtmap (t : rtarget A) : rtarget B :=
  match t with RRename w => RRename w | RBind u ρ => RBind (f u) (rmap ρ) end.

Lemma rto_adj_nmap x : rto_adj (nmap f x) = rmap (rto_adj x).
Proof. apply radj_eq; cbn [radj_n rmap rto_adj]; unfold asel; rewrite nwfc_nmap; destruct (nwfc _ x); reflexivity. Qed.

Theorem rapply_rmap a v : rapply (rmap a) v = rresmap (rapply a v).
Proof.
  unfold rapply; cbn [radj_n rmap]; rewrite napply_nmap.
  destruct (napply (radj_n a) v) as [w|[u x]]; cbn [resmap rpack rresmap]; [reflexivity|rewrite rto_adj_nmap; reflexivity].
Qed.

Theorem rmap_identity : rmap ridentity = ridentity.
Proof. apply radj_eq; reflexivity. Qed.

Lemma rmap_compose_depth a n : forall b, rdepth b < n -> rmap (rcompose a b) = rcompose (rmap a) (rmap b).
Proof.
  induction n as [|n IH]; intros b Hd; [lia|].
  apply rextensionality; intros v; rewrite rapply_rmap, !rapply_compose, rapply_rmap.
  destruct (rapply b v) as [w|[u ρ]] eqn:E; cbn [rresmap]; [rewrite rapply_rmap; reflexivity|].
  rewrite IH; [reflexivity|]; pose proof (rdepth_payload b v u ρ E); lia.
Qed.

Theorem rmap_compose a b : rmap (rcompose a b) = rcompose (rmap a) (rmap b).
Proof. apply (rmap_compose_depth a (S (rdepth b))); lia. Qed.

Lemma rmap_push_outer_depth h n : forall a, rdepth a < n -> rmap (rpush_outer h a) = rpush_outer h (rmap a).
Proof.
  induction n as [|n IH]; intros a Hd; [lia|].
  apply rextensionality; intros v; rewrite rapply_rmap, !rapply_push_outer, rapply_rmap.
  destruct (rapply a v) as [w|[u ρ]] eqn:E; cbn [rresmap]; [reflexivity|].
  rewrite IH; [reflexivity|]; pose proof (rdepth_payload a v u ρ E); lia.
Qed.

Theorem rmap_push_outer h a : rmap (rpush_outer h a) = rpush_outer h (rmap a).
Proof. apply (rmap_push_outer_depth h (S (rdepth a))); lia. Qed.

Theorem rmap_push_inner h t a : rmap (rpush_inner h t a) = rpush_inner h (rtmap t) (rmap a).
Proof.
  apply rextensionality; intros v; rewrite rapply_rmap, !rapply_push_inner.
  destruct (rvar_eqb v _); [destruct t; reflexivity|symmetry; apply rapply_rmap].
Qed.

Theorem rmap_lift h a : rmap (rlift h a) = rlift h (rmap a).
Proof. unfold rlift; rewrite rmap_push_inner, rmap_push_outer; reflexivity. Qed.

Theorem rtmap_shift h t : rtmap (rshift_target h t) = rshift_target h (rtmap t).
Proof. destruct t; cbn [rtmap rshift_target]; [reflexivity|rewrite rmap_push_outer; reflexivity]. Qed.

Theorem rtmap_apply_target a t : rtmap (rapply_target a t) = rapply_target (rmap a) (rtmap t).
Proof.
  destruct t as [w|u ρ]; cbn [rapply_target rtmap]; [|rewrite rmap_compose; reflexivity].
  rewrite rapply_rmap; destruct (rapply a w) as [x|[u ρ]]; reflexivity.
Qed.

End RMap.

(** ** The denotation of expressions, over a map

    [names] reads [pmap h a] as a shared definition: [a] reified on its
    own, its terms and atoms then put, mapped, at the end of the node's
    tables ([ashift] moves the expression's indices there).  The
    definition's equation is [aedenB_map], with the tables checked by
    the kernel. *)

Fixpoint ashift (ot oa : N) (e : aexpN) : aexpN :=
  match e with
  | NId => NId
  | NAtom n => NAtom (N.add n oa)
  | NCompose a b => NCompose (ashift ot oa a) (ashift ot oa b)
  | NOuter h a => NOuter h (ashift ot oa a)
  | NInner h t a => NInner h (tshiftN ot oa t) (ashift ot oa a)
  | NLift h a => NLift h (ashift ot oa a)
  end
with tshiftN (ot oa : N) (t : texpN) : texpN :=
  match t with
  | NVarE h i => NVarE h i
  | NBindE u p => NBindE (N.add u ot) (ashift ot oa p)
  | NShiftE h t => NShiftE h (tshiftN ot oa t)
  | NLookE h i a => NLookE h i (ashift ot oa a)
  end.

Fixpoint abound (nt na : N) (e : aexpN) : bool :=
  match e with
  | NId => true
  | NAtom n => N.ltb n na
  | NCompose a b => abound nt na a && abound nt na b
  | NOuter _ a => abound nt na a
  | NInner _ t a => tbound nt na t && abound nt na a
  | NLift _ a => abound nt na a
  end
with tbound (nt na : N) (t : texpN) : bool :=
  match t with
  | NVarE _ _ => true
  | NBindE u p => N.ltb u nt && abound nt na p
  | NShiftE _ t => tbound nt na t
  | NLookE _ _ a => abound nt na a
  end.

Lemma nth_error_skipn' {X} o : forall (l : list X) i, nth_error (skipn o l) i = nth_error l (o + i).
Proof. induction o as [|o IH]; intros [|x l] i; cbn; auto; destruct i; reflexivity. Qed.

Lemma nth_error_firstn' {X} n : forall (l : list X) i, i < n -> nth_error (firstn n l) i = nth_error l i.
Proof. induction n as [|n IH]; intros [|x l] [|i] H; cbn; auto; try lia; apply IH; lia. Qed.

Lemma nth_shift {X Y} (G : X -> Y) (l : list X) (l' : list Y) o i :
  firstn (length l) (skipn o l') = map G l -> i < length l -> nth_error l' (o + i) = option_map G (nth_error l i).
Proof.
  intros H Hi; rewrite <- nth_error_skipn', <- (nth_error_firstn' (length l)) by exact Hi.
  rewrite H, nth_error_map; reflexivity.
Qed.

Lemma bnth_shift {X Y} (G : X -> Y) (l : list X) (l' : list Y) o n :
  firstn (length l) (skipn (N.to_nat o) l') = map G l -> N.ltb n (N.of_nat (length l)) = true ->
  bnth (bof l') (N.add n o) = option_map G (bnth (bof l) n).
Proof.
  intros H Hn; rewrite !bnth_bof, N2Nat.inj_add, Nat.add_comm.
  apply nth_shift; [exact H|]; apply N.ltb_lt in Hn; lia.
Qed.

Section DenMap.

Context {A B : Type} (F : A -> B).

Theorem aedenB_map Le (la : list A) (aa : list (radj A)) (lb : list B) (ab : list (radj B)) ot oa :
  firstn (length la) (skipn (N.to_nat ot) lb) = map F la ->
  firstn (length aa) (skipn (N.to_nat oa) ab) = map (rmap F) aa ->
  (forall e, abound (N.of_nat (length la)) (N.of_nat (length aa)) e = true ->
     aedenB Le (bof lb) (bof ab) (ashift ot oa e) = rmap F (aedenB Le (bof la) (bof aa) e)) /\
  (forall t, tbound (N.of_nat (length la)) (N.of_nat (length aa)) t = true ->
     tedenB Le (bof lb) (bof ab) (tshiftN ot oa t) = rtmap F (tedenB Le (bof la) (bof aa) t)).
Proof.
  intros Ht Ha; apply expN_mind; intros; cbn [abound tbound] in *; simpl;
    repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end;
    repeat match goal with IH : _ = true -> ?l = _ |- context [?l] => rewrite IH by assumption; clear IH end.
  - symmetry; apply rmap_identity.
  - rewrite (bnth_shift (rmap F) aa ab oa n Ha) by assumption.
    destruct (bnth (bof aa) n); cbn [option_map]; [reflexivity|symmetry; apply rmap_identity].
  - symmetry; apply rmap_compose.
  - symmetry; apply rmap_push_outer.
  - symmetry; apply rmap_push_inner.
  - symmetry; apply rmap_lift.
  - reflexivity.
  - rewrite (bnth_shift F la lb ot u Ht) by assumption.
    destruct (bnth (bof la) u); reflexivity.
  - symmetry; apply rtmap_shift.
  - rewrite rapply_rmap; destruct (rapply _ _) as [x|[u ρ]]; reflexivity.
Qed.

End DenMap.

(** ** On scoped adjustments: [pmap] *)

Section PMap.

Context {T U : nat -> Type} (h : forall K, T K -> U K).

(** A payload term [u : T K] mapped, in the same scope. *)
Definition pmapf (x : {K & T K}) : {K & U K} := existT U (projT1 x) (h (projT1 x) (projT2 x)).

Lemma scoped_rmap N M (a : radj {K & T K}) : scoped N M (rmap pmapf a) = scoped N M a.
Proof.
  unfold scoped; cbn [radj_n rmap].
  rewrite scoped_tail_nmap, (pscopedc_nmap pmapf (fun u => eq_refl)); reflexivity.
Qed.

Definition pmap {N M} (a : adj T N M) : adj U N M :=
  mk_adj (rmap pmapf (adj_raw a)) (Is_true_s_intro (eq_trans (scoped_rmap N M _) (Is_true_s_elim (adj_ok a)))).
Arguments pmap : simpl never.
(** [cbn] would read [apply (pmap h a)] through the projection. *)
#[global] Opaque pmap.

Theorem pmap_identity {N} : pmap (@identity T N) = identity.
Proof. apply adj_eq; apply rmap_identity. Qed.

Theorem pmap_compose {N M K} (a : adj T M K) (b : adj T N M) : pmap (compose a b) = compose (pmap a) (pmap b).
Proof. apply adj_eq; apply rmap_compose. Qed.

Lemma aok_nmap K M x : aok K M (nmap pmapf x) = aok K M x.
Proof.
  unfold aok; rewrite nwfc_nmap, scoped_tail_nmap, (pscopedc_nmap pmapf (fun u => eq_refl)); reflexivity.
Qed.

End PMap.

(** ** Maps between syntaxes

    A map [h] from the terms of [P] to those of [Q] that keeps variables
    and commutes with the Kleisli extension, the morphism mapped
    ([mmap]): substituting and then mapping is mapping and then
    substituting along the mapped adjustment ([subst_pmap]).  Type
    weakening, from the terms of System F with [N] type variables to
    those with [S N], is one. *)

Class SyntaxMap {P Q : nat -> Type} {kp : Kleisli P P} {sp : Syntax P} {kq : Kleisli Q Q} {sq : Syntax Q}
    (h : forall K, P K -> Q K) : Prop := {
  smap_var : forall K (v : var K), h K (Syntax.tvar v) = Syntax.tvar v;
  smap_kleisli : forall N M (f : morph P N M) K L (e : ext N M K L) (u : P K),
    h L (Syntax.kleisli f e u) = Syntax.kleisli (mmap h f) e (h K u) }.

Section Apply.

Context {P Q : nat -> Type} {kp : Kleisli P P} {sp : Syntax P} {kq : Kleisli Q Q} {sq : Syntax Q}.
Context (h : forall K, P K -> Q K) {hm : SyntaxMap h}.

Lemma gapply0_nmap n : forall x, nnest x < n ->
  forall Kx Mx s L0 HL Hx Hx' K L (e : ext Kx L0 K L) v,
  @gapply0 Q kq sq (nmap (pmapf h) x) Kx Mx s L0 HL Hx' K L e v = h L (@gapply0 P kp sp x Kx Mx s L0 HL Hx K L e v).
Proof.
  induction n as [|n IH]; intros x Hn Kx Mx s L0 HL Hx Hx' K L e v; [lia|].
  destruct (inner_or_outer (ext_depth e) (var_raw v)) as [[El Hi]|Hout].
  { rewrite (gapply0_inner _ _ _ _ _ _ _ e v (W_inner e _ El Hi) El Hi),
            (gapply0_inner _ _ _ _ _ _ _ e v (W_inner e _ El Hi) El Hi), smap_var; reflexivity. }
  pose proof (rvn_gapply0 x Kx Mx s L0 HL Hx e v (W_HL Mx s e HL) Hout) as R1.
  pose proof (@rvn_gapply0 Q kq sq (nmap (pmapf h) x) Kx Mx s L0 HL Hx' K L e v (W_HL Mx s e HL) Hout) as R2.
  rewrite napply_nmap in R2.
  destruct (napply x (down (ext_depth e) (var_raw v))) as [w|[u ρ]] eqn:E; cbn [resmap rvn] in R1, R2.
  - destruct R1 as [H1 ->], R2 as [H2 ->]; rewrite smap_var; reflexivity.
  - destruct R1 as [H1 ->], R2 as [H2 ->]; rewrite smap_kleisli.
    apply Syntax.kleisli_ext; intros K' L' e' v'; unfold mmap.
    apply IH; pose proof (napply_depth_aok _ _ _ _ _ _ (Is_true_s_elim Hx) E); lia.
Qed.

Theorem apply_pmap {N M} (a : adj P N M) K L (e : ext N M K L) v :
  apply (pmap h a) K L e v = h L (apply a K L e v).
Proof.
  rewrite (apply_gapply0 a top_HL (top_aok a)), (apply_gapply0 (pmap h a) top_HL (top_aok (pmap h a))).
  apply (gapply0_nmap (S (nnest (radj_n (adj_raw a))))); lia.
Qed.

(** Going under a binder of another sort: what [cbn] leaves of the
    Kleisli extension along a mapped [apply] ([names] rewrites with it). *)
Theorem kleisli_mmap_apply {N M} (a : adj P N M) K L (e : ext N M K L) (t : Q K) :
  Syntax.kleisli (mmap h (apply a)) e t = Syntax.kleisli (apply (pmap h a)) e t.
Proof. apply Syntax.kleisli_ext; intros; unfold mmap; symmetry; apply apply_pmap. Qed.

Theorem subst_pmap {N M} (a : adj P N M) (t : P N) : h M (t [a]) = (h N t) [pmap h a].
Proof. rewrite smap_kleisli; apply kleisli_mmap_apply. Qed.

End Apply.


(** ** [names] on [pmap]

    The equation of the definition [names] reads [pmap h a] as: [a]
    reified on its own ([Hd], by conversion, as for any adjustment), its
    terms and atoms mapped at the end of the node's tables ([Ht], [Ha],
    computed by the kernel). *)
Definition g_pmap_def {T U : nat -> Type} (h : forall K, T K -> U K) {N M} (a : adj T N M)
    Le (la : list {K & T K}) (aa : list (radj {K & T K})) (te : list {K & U K}) (ael : list (radj {K & U K}))
    ot oa e
    (Ht : firstn (length la) (skipn (N.to_nat ot) te) = map (pmapf h) la)
    (Ha : firstn (length aa) (skipn (N.to_nat oa) ael) = map (rmap (pmapf h)) aa)
    (Hb : abound (N.of_nat (length la)) (N.of_nat (length aa)) e = true)
    (Hd : adj_raw a = aedenB Le (bof la) (bof aa) e) :
  adj_raw (pmap h a) = aedenB Le (bof te) (bof ael) (ashift ot oa e) :=
  eq_trans (f_equal (rmap (pmapf h)) Hd) (eq_sym (proj1 (aedenB_map (pmapf h) Le la aa te ael ot oa Ht Ha) e Hb)).

From Ltac2 Require Import Ltac2.

Ltac2 reify_pmap (s : Names.st) (t : constr) (n : constr) (m : constr) (a : constr) : constr option :=
  let (f, args) := Names.split_app a in
  if (if Constr.equal f constr:(@pmap) then Int.equal (Array.length args) 6 else false) then
    let (tT, tU, h, a0) := (Array.get args 0, Array.get args 1, Array.get args 2, Array.get args 5) in
    Names.attempt (fun () =>
      (* [a0] on its own, with the node's labels *)
      let s' := { Names.labs := s.(Names.labs); Names.terms := Names.new_tbl (); Names.atoms := Names.new_tbl ();
                  Names.ns := s.(Names.ns); Names.lets := s.(Names.lets); Names.heads := s.(Names.heads);
                  Names.sdefs := FMap.empty FSet.Tags.int_tag; Names.sproofs := FMap.empty FSet.Tags.int_tag } in
      let e := Names.reify_adj s' tT n m a0 in
      (match FMap.bindings (s'.(Names.sdefs)) with [] => () | _ => Control.zero Not_found end);
      let la := List.rev ((s'.(Names.terms)).(Names.items)) in
      let aa := List.rev ((s'.(Names.atoms)).(Names.items)) in
      (* mapped, at the end of the node's tables *)
      let ot := (s.(Names.terms)).(Names.size) in
      List.iter (fun x => let (k, u) := Names.term_parts x in
                          let _ := Names.tbl_push (s.(Names.terms)) (Names.raw_term tU k (Names.app h [k; u])) in ()) la;
      let oa := (s.(Names.atoms)).(Names.size) in
      List.iter (fun y => let (_, ya) := Names.split_app y in
                          let (n', m', x) := (Array.get ya 1, Array.get ya 2, Array.get ya 3) in
                          let _ := Names.tbl_push (s.(Names.atoms))
                                     (Names.app constr:(@adj_raw) [tU; n'; m'; Names.app constr:(@pmap) [tT; tU; h; n'; m'; x]]) in
                          ()) aa;
      let k := Names.tbl_push (s.(Names.atoms)) (Names.app constr:(@adj_raw) [tU; n; m; a]) in
      let (otc, oac) := (Names.n_lit ot, Names.n_lit oa) in
      s.(Names.sdefs) := FMap.add k (Names.app constr:(@ashift) [otc; oac; e]) (s.(Names.sdefs));
      let pT := Names.raw_ty tT in
      let pU := Names.raw_ty tU in
      let lac := Names.list_of pT la in
      let aac := Names.list_of (Names.app constr:(@radj) [pT]) aa in
      s.(Names.sproofs) := FMap.add k (fun lt te ael =>
          Names.app constr:(@g_pmap_def)
            [tT; tU; h; n; m; a0; lt; lac; aac; te; ael; otc; oac; e;
             Names.refl (Names.app constr:(@list) [pU]) (Names.app constr:(@map) [pT; pU; Names.app constr:(@pmapf) [tT; tU; h]; lac]);
             Names.refl (Names.app constr:(@list) [Names.app constr:(@radj) [pU]])
               (Names.app constr:(@map) [Names.app constr:(@radj) [pT]; Names.app constr:(@radj) [pU];
                                        Names.app constr:(@rmap) [pT; pU; Names.app constr:(@pmapf) [tT; tU; h]]; aac]);
             Names.refl constr:(bool) constr:(true);
             Names.refl (Names.app constr:(@radj) [pT]) (Names.app constr:(@adj_raw) [tT; n; m; a0])]) (s.(Names.sproofs));
      Some (Names.app constr:(NAtom) [Names.n_lit k])) (fun _ => None)
  else None.

Ltac2 Set Names.reify_hook := reify_pmap.

(** Before [names_pre]: [kleisli (mmap h (apply a))], what [cbn] leaves
    under a binder of another sort, along [apply (pmap h a)]
    ([kleisli_mmap_apply]), the map's instance found by resolution. *)
Ltac2 Set Subst.mmap_hook := fun () =>
  ltac1:(repeat (rewrite kleisli_mmap_apply by typeclasses eauto)).
