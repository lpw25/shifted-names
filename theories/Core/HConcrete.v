(** * HNorm is sound for the concrete adjustments

    The adjustments of the library ([radj T], Adjustment.v) form a
    comprehension model ([kmodel]): an environment is an adjustment [x],
    [p_h] composes it with the weakening past [h], [q_h] reads where it
    sends [h₀], and pairing puts a target in front ([rpush_inner]).  An
    expression [e] acts on [x] as [x] composed with its denotation
    ([kden]).  The facts hold for the labels they mention, so two labels
    they order are distinct, and their projections commute ([kcons]).

    Hence [hn_eq_t_sound]: when [HNorm] finds two expressions equal (with
    their term atoms in range), their denotations are equal.  [HNorm] is
    not complete for these adjustments: labels the facts leave unordered
    may still be distinct here. *)

From Stdlib Require Import List Arith Lia Bool PArith.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise CNorm Comp HNorm KnownOrder HRefine CSound.
Import ListNotations.

(** Term atoms below [n]. *)
Fixpoint aok (n : nat) (a : aexp) : bool :=
  match a with
  | AId | AAtom _ => true
  | ACompose a b => aok n a && aok n b
  | AOuter _ a | ALift _ a => aok n a
  | AInner _ t a => tok n t && aok n a
  end
with tok (n : nat) (t : texp) : bool :=
  match t with
  | TVarE _ _ => true
  | TBindE u p => Nat.ltb u n && pok n p
  | TShiftE _ t => tok n t
  end
with pok (n : nat) (p : pexp) : bool :=
  match p with
  | PId | PAtom _ => true
  | PComp a p => aok n a && pok n p
  | PShift _ p => pok n p
  end.

(** The decision used by the [names] tactic. *)
Definition hn_eq_t (F : order) (n : nat) (e1 e2 : aexp) : bool := aok n e1 && aok n e2 && HNorm.hn_eq F e1 e2.

(** Where the normal form of [e] sends [hᵢ]. *)
Definition hlook (F : order) (n : nat) (e : aexp) (h : lexp) (i : nat) : option (HNorm.val * HNorm.st) :=
  if aok n e then let '(w, T0) := HNorm.norm F e [] HNorm.st0 in Some (HNorm.lookup F h i w T0) else None.

Definition hlook_var (F : order) (n : nat) (e : aexp) (h : lexp) (i : nat) : option (lexp * nat) :=
  match hlook F n e h i with Some (HNorm.VVar h' j, _) => Some (h', j) | _ => None end.

(** [hᵢ] goes to the term [u] whose payload [eb] shows: [eb] normalises,
    as a payload, to the payload's own word. *)
Definition hbind_check (F : order) (n : nat) (e : aexp) (h : lexp) (i : nat) (eb : aexp) (u : nat) : bool :=
  aok n eb &&
  match hlook F n e h i with
  | Some (HNorm.VTerm u' None p, T1) =>
      Nat.eqb u u' &&
      (let '(wb, T2) := HNorm.norm F eb [] T1 in let '(wb', _) := HNorm.clean None wb T2 in Pos.eqb (HNorm.wid wb') p)
  | _ => false
  end.


(** ** Materialising

    [e'] is [e] with some terms [u⟨eb⟩] replaced by term atoms [k] with
    the identity payload: their HNorm words, which have no atoms, are the
    same step by step except at such entries. *)

Fixpoint hmat_walk (ids : list (nat * nat * positive)) (w w' : HNorm.word) : bool :=
  match w, w' with
  | [], [] => true
  | (s, _) :: r, (s', _) :: r' =>
      (match s with HNorm.SA _ => false | _ => true end) &&
      (HNorm.step_eqb s s' ||
       match s, s' with
       | HNorm.SE h (HNorm.VTerm u None p), HNorm.SE h' (HNorm.VTerm k None q) =>
           lexp_eqb h h' && Pos.eqb q 1 && existsb (fun '(k', u', i) => Nat.eqb k k' && Nat.eqb u u' && Pos.eqb p i) ids
       | _, _ => false
       end) && hmat_walk ids r r'
  | _, _ => false
  end.

Definition hmat_ids (F : order) (facts : list (nat * nat * aexp)) (T : HNorm.st) : list (nat * nat * positive) * HNorm.st :=
  fold_left (fun '(acc, T) '(k, u, eb) =>
    let '(wb, T1) := HNorm.norm F eb [] T in let '(wb', T2) := HNorm.clean None wb T1 in ((k, u, HNorm.wid wb') :: acc, T2))
    facts ([], T).

Definition hmat_check (F : order) (n : nat) (facts : list (nat * nat * aexp)) (e e' : aexp) : bool :=
  aok n e && aok n e' && forallb (fun '(k, u, eb) => Nat.ltb k n && Nat.ltb u n && aok n eb) facts &&
  (let '(w, T1) := HNorm.norm F e [] HNorm.st0 in
   let '(w', T2) := HNorm.norm F e' [] T1 in
   let '(ids, _) := hmat_ids F facts T2 in
   hmat_walk ids w w').

Section Concrete.

Context {T : Type}.
Variables (lenv : list label) (tenv : list T) (aenv : list (radj T)) (penv : list (rpadj T)).

Local Notation lden := (lden lenv).
Local Notation aeden := (aeden lenv tenv aenv penv).
Local Notation teden := (teden lenv tenv aenv penv).
Local Notation peden := (peden lenv tenv aenv penv).

Definition kpop (h : lexp) (x : radj T) : radj T := rcompose x (Laws.rshift (lden h)).
Definition khd (h : lexp) (x : radj T) : rtarget T := rapply_target x (RRename (mk_rvar (lden h) 0)).
Definition kpush (h : lexp) (x : radj T) (t : rtarget T) : radj T := rpush_inner (lden h) t x.

Lemma kpop_push h x t : kpop h (kpush h x t) = x.
Proof. unfold kpop, kpush; exact (rcompose_push_inner_shift (lden h) t x). Qed.

Lemma khd_push h x t : khd h (kpush h x t) = t.
Proof.
  unfold khd, kpush, rapply_target; rewrite rapply_push_inner, rvar_eqb_refl.
  destruct t; reflexivity.
Qed.

Lemma kpush_pop h x : kpush h (kpop h x) (khd h x) = x.
Proof.
  apply rextensionality; intros v; unfold kpush, kpop, khd; rewrite rapply_push_inner.
  destruct (rvar_eqb_spec v (mk_rvar (lden h) 0)) as [->|Ne].
  - unfold rapply_target; destruct (rapply x _) as [u|[u ρ]]; reflexivity.
  - rewrite rapply_compose, Laws.rapply_shift, shift_unshift_rvar by exact Ne; reflexivity.
Qed.

Definition kterm (u : nat) (b : option nat) (x : radj T) : rtarget T :=
  match nth_error tenv u with Some w => RBind w (rpcompose x (bden penv b)) | None => RRename (mk_rvar None 0) end.

Definition kmodel : cmodel :=
  mk_cmodel (radj T) (rtarget T) kpop khd kpush kpop_push khd_push kpush_pop
    (fun n x => rcompose x (aden aenv n)) kterm.

(** Reading [hᵢ] after projections. *)
Lemma khd_iter h i x : forall j,
  rapply (iter i (kpop h) x) (mk_rvar (lden h) j) = rapply x (mk_rvar (lden h) (i + j)).
Proof.
  induction i as [|i IH]; intros j; [reflexivity|]; cbn [iter]; unfold kpop at 1.
  rewrite rapply_compose, Laws.rapply_shift; unfold shift_rvar; cbn [v_label v_index].
  rewrite label_eqb_refl; cbn [andb Nat.leb]; rewrite IH; f_equal; f_equal; lia.
Qed.

Lemma teden_kind n t : n <= List.length tenv -> tok n t = true ->
  (CNorm.is_bind t = true -> exists u ρ, teden t = RBind u ρ) /\ (CNorm.is_bind t = false -> exists w, teden t = RRename w).
Proof.
  intros Hn; induction t as [h i|u p|h t IH]; cbn [tok CNorm.is_bind Normalise.teden].
  - intros _; split; [discriminate|intros _; eexists; reflexivity].
  - intros H; apply andb_true_iff in H as [Hu _]; apply Nat.ltb_lt in Hu.
    destruct (nth_error tenv u) as [w|] eqn:E; [|apply nth_error_None in E; lia].
    split; [intros _; do 2 eexists; reflexivity|discriminate].
  - intros H; destruct (IH H) as [Hb Hv]; split.
    + intros B; destruct (Hb B) as [u [ρ E]]; rewrite E; do 2 eexists; reflexivity.
    + intros B; destruct (Hv B) as [w E]; rewrite E; eexists; reflexivity.
Qed.

(** An expression acts on [x] as [x] composed with its denotation. *)
Lemma kden n : n <= List.length tenv ->
  (forall a, aok n a = true -> forall x, @ca kmodel a x = rcompose x (aeden a))
  /\ (forall t, tok n t = true -> forall x, @ct kmodel t x = rapply_target x (teden t))
  /\ (forall p, pok n p = true -> forall x, rpcompose (@cp kmodel p x) (bden penv (fpb p)) = rpcompose x (peden p)).
Proof.
  intros Hn; apply exp_mind; cbn [aok tok pok ca ct cp fpb Normalise.aeden Normalise.teden Normalise.peden].
  - intros _ x; symmetry; apply rcompose_identity_r.
  - intros m _ x; reflexivity.
  - intros a IHa b IHb H x; apply andb_true_iff in H as [Ha Hb].
    rewrite (IHb Hb), (IHa Ha), rcompose_assoc; reflexivity.
  - intros h a IH H x; rewrite (IH H); cbn [kmodel cpop]; unfold kpop.
    rewrite <- rcompose_assoc, <- rpush_outer_as_compose; reflexivity.
  - intros h t IHt a IHa H x; apply andb_true_iff in H as [Ht Ha].
    rewrite (IHa Ha), (IHt Ht), rcompose_push_inner_r; reflexivity.
  - intros h a IH H x; rewrite (IH H); cbn [kmodel cpop chd cpush]; unfold kpop, khd, kpush.
    unfold rlift; rewrite rcompose_push_inner_r, rpush_outer_as_compose, rcompose_assoc; reflexivity.
  - intros h i _ x; unfold cname; cbn [kmodel chd cpop cU]; unfold khd, rapply_target.
    rewrite (khd_iter h i x 0), Nat.add_0_r; reflexivity.
  - intros u p IH H x; apply andb_true_iff in H as [Hu Hp]; apply Nat.ltb_lt in Hu.
    cbn [kmodel cterm]; unfold kterm; destruct (nth_error tenv u) as [w|] eqn:E; [|apply nth_error_None in E; lia].
    rewrite (IH Hp); reflexivity.
  - intros h t IH H x; pose proof (teden_kind n t Hn H) as [Hb Hv].
    destruct (CNorm.is_bind t) eqn:B.
    + destruct (Hb eq_refl) as [u [ρ E]]; rewrite (IH H), E; reflexivity.
    + destruct (Hv eq_refl) as [w E]; rewrite (IH H), E; cbn [kmodel cpop]; unfold kpop, rapply_target.
      rewrite rapply_compose, Laws.rapply_shift; reflexivity.
  - intros _ x; reflexivity.
  - intros m _ x; reflexivity.
  - intros a IHa p IHp H x; apply andb_true_iff in H as [Ha Hp].
    rewrite (IHp Hp), (IHa Ha), rpcompose_compose; reflexivity.
  - intros h p IH H x; rewrite (IH H); cbn [kmodel cpop]; unfold kpop.
    rewrite <- rpcompose_compose, <- rpshift_as_pcompose; reflexivity.
Qed.

Lemma shift_other l l' j : l' <> l -> shift_rvar (mk_rvar l 0) (mk_rvar l' j) = mk_rvar l' j.
Proof.
  intros Ne; unfold shift_rvar; cbn [v_label v_index].
  destruct (label_eqb_spec l l') as [->|_]; [contradiction|reflexivity].
Qed.

(** The model is consistent with facts that hold. *)
Lemma kcons F : facts_ok lenv F -> ccons F kmodel.
Proof.
  intros HF; split.
  - intros g h L x; pose proof (lt_known_sound lenv F HF g h L) as Lt.
    assert (Ne : lden g <> lden h) by (intros E; rewrite E in Lt; exact (olabel_lt_irrefl _ Lt)).
    cbn [kmodel cpop chd]; unfold kpop, khd, rapply_target; split; [|split].
    + rewrite <- !rcompose_assoc, rcompose_shift_comm; reflexivity.
    + rewrite rapply_compose, Laws.rapply_shift, shift_other by exact Ne; reflexivity.
    + rewrite rapply_compose, Laws.rapply_shift, shift_other by (intros E; apply Ne; symmetry; exact E); reflexivity.
  - intros u x; cbn [kmodel cterm cpop]; unfold kterm, kpop; destruct (nth_error tenv u); [|reflexivity].
    f_equal; cbn [bden]; apply rpcompose_named; intros v Hv.
    rewrite rapply_compose, Laws.rapply_shift; destruct v as [[s|] k]; [reflexivity|contradiction].
Qed.

(** ** Soundness of the decision *)

Theorem hn_eq_t_sound l e1 e2 : lfacts_ok lenv l ->
  hn_eq_t (order_of l) (List.length tenv) e1 e2 = true -> aeden e1 = aeden e2.
Proof.
  intros Hl H; unfold hn_eq_t in H; apply andb_true_iff in H as [H H3]; apply andb_true_iff in H as [H1 H2].
  pose proof (proj1 (hn_eq_order_correct l lenv Hl e1 e2) H3 kmodel (kcons _ (order_of_ok lenv l Hl)) ridentity) as E.
  destruct (kden (List.length tenv) (le_n _)) as [Ka _].
  rewrite (Ka e1 H1), (Ka e2 H2), !rcompose_identity_l in E; exact E.
Qed.

Lemma RVal_var S g k cv : RVal S (HNorm.VVar g k) cv -> cv = CNorm.VVar g k.
Proof. intros H; inversion H; reflexivity. Qed.

Lemma RVal_term S u b p cv : RVal S (HNorm.VTerm u b p) cv -> exists cp, cv = CNorm.VTerm u b cp /\ RId S p cp.
Proof. intros H; inversion H; subst; eexists; split; [reflexivity|eassumption]. Qed.

Lemma kname h i X : @cname kmodel h i X = rapply_target X (RRename (mk_rvar (lden h) i)).
Proof. unfold cname; cbn [kmodel chd cpop cU]; unfold khd, rapply_target; rewrite (khd_iter h i X 0), Nat.add_0_r; reflexivity. Qed.

(** The meaning of the [CNorm] lookup in [e]'s normal form. *)
Lemma klookup l e h i : lfacts_ok lenv l -> aok (List.length tenv) e = true ->
  @vden kmodel (CNorm.lookup (order_of l) h i (CNorm.norm (order_of l) e [])) ridentity
  = rapply_target (aeden e) (RRename (mk_rvar (lden h) i)).
Proof.
  intros Hl Ha; pose proof (kcons _ (order_of_ok lenv l Hl)) as HM.
  rewrite (lookup_sound kmodel _ HM), (norm_meaning kmodel _ HM), kname.
  destruct (kden (List.length tenv) (le_n _)) as [Ka _]; rewrite (Ka e Ha), rcompose_identity_l; reflexivity.
Qed.

Theorem hlook_var_sound l e h i h' j : lfacts_ok lenv l ->
  hlook_var (order_of l) (List.length tenv) e h i = Some (h', j) ->
  rapply (aeden e) (mk_rvar (lden h) i) = inl (mk_rvar (lden h') j).
Proof.
  intros Hl H; unfold hlook_var, hlook in H; destruct (aok _ e) eqn:Ha; [|discriminate].
  set (F := order_of l) in *.
  destruct (HNorm.norm F e [] HNorm.st0) as [w T0] eqn:En; destruct (HNorm.lookup F h i w T0) as [v T1] eqn:El.
  destruct v as [g k| |]; try discriminate; injection H as <- <-.
  pose proof (order_of_irrefl l lenv Hl) as Hirr; pose proof (order_of_trans l lenv Hl) as Htr.
  destruct (proj1 (norm_spec_all F Hirr Htr) e [] HNorm.st0 [] w T0 Inv_st0 (RWNil _) En) as [I1 [_ R1]].
  destruct (lookup_spec F Hirr Htr T0 h w _ I1 R1 i _ T1 El) as [_ [_ R2]].
  pose proof (klookup l e h i Hl Ha) as K; fold F in K.
  rewrite (RVal_var _ _ _ _ R2), vden_var, kname in K; unfold rapply_target in K; rewrite rapply_identity in K.
  destruct (rapply (aeden e) _) as [u|[u ρ]]; [injection K as <-; reflexivity|discriminate].
Qed.

Theorem hbind_sound l e h i eb u x : lfacts_ok lenv l ->
  hbind_check (order_of l) (List.length tenv) e h i eb u = true -> nth_error tenv u = Some x ->
  rapply (aeden e) (mk_rvar (lden h) i) = inr (x, rpcompose (aeden eb) rpidentity).
Proof.
  intros Hl H Hx; unfold hbind_check, hlook in H; apply andb_true_iff in H as [Hb H].
  destruct (aok _ e) eqn:Ha; [|discriminate].
  set (F := order_of l) in *.
  destruct (HNorm.norm F e [] HNorm.st0) as [w T0] eqn:En; destruct (HNorm.lookup F h i w T0) as [v T1] eqn:El.
  destruct v as [|u' [b|] p|]; try discriminate.
  apply andb_true_iff in H as [Hu H]; apply Nat.eqb_eq in Hu; subst u'.
  destruct (HNorm.norm F eb [] T1) as [wb T2] eqn:Eb; destruct (HNorm.clean None wb T2) as [wb' T3] eqn:Ec.
  apply Pos.eqb_eq in H.
  pose proof (order_of_irrefl l lenv Hl) as Hirr; pose proof (order_of_trans l lenv Hl) as Htr.
  destruct (proj1 (norm_spec_all F Hirr Htr) e [] HNorm.st0 [] w T0 Inv_st0 (RWNil _) En) as [I1 [_ R1]].
  destruct (lookup_spec F Hirr Htr T0 h w _ I1 R1 i _ T1 El) as [I2 [_ R2]].
  destruct (proj1 (norm_spec_all F Hirr Htr) eb [] T1 [] wb T2 I2 (RWNil _) Eb) as [I3 [X3 R3]].
  destruct (clean_spec T2 None wb _ wb' T3 I3 R3 Ec) as [I4 [X4 R4]].
  pose proof (klookup l e h i Hl Ha) as K; fold F in K.
  destruct (RVal_term _ _ _ _ _ R2) as [cp [Ecp Rp]]; rewrite Ecp in K.
  pose proof (proj1 (R_mono _ _ (Ext_trans _ _ _ X3 X4)) _ _ Rp) as Rp'.
  pose proof (RWord_RId _ _ _ R4) as Rb; rewrite H in Rb.
  pose proof (proj1 (R_func _ I4) _ _ Rp' _ Rb) as Ecp2; subst cp.
  pose proof (kcons _ (order_of_ok lenv l Hl)) as HM.
  rewrite vden_term, (clean_sound kmodel _ HM), (norm_meaning kmodel _ HM) in K.
  destruct (kden (List.length tenv) (le_n _)) as [Ka _]; rewrite (Ka eb Hb), rcompose_identity_l in K.
  cbn [kmodel cterm] in K; unfold kterm in K; rewrite Hx in K; unfold rapply_target in K.
  destruct (rapply (aeden e) _) as [w'|[u' ρ]]; [discriminate|injection K as -> ->; reflexivity].
Qed.

Section Mat.

Variable g : rpadj T -> T -> T.

Definition tmrel (t t' : rtarget T) : Prop := t = t' \/ exists u ρ, t = RBind u ρ /\ t' = RBind (g ρ u) rpidentity.

(** Two words without atoms, step by step the same except for related
    values. *)
Inductive matw : CNorm.cword -> CNorm.cword -> Prop :=
| MNil : matw [] []
| MSame s w w' : (match s with CNorm.SA _ => False | _ => True end) -> matw w w' -> matw (s :: w) (s :: w')
| MEnt h v v' w w' : tmrel (@vden kmodel v ridentity) (@vden kmodel v' ridentity) -> matw w w' ->
    matw (CNorm.SE h v :: w) (CNorm.SE h v' :: w').

Lemma matw_mrel w w' : matw w w' -> forall v, mrel g (rapply (@wden kmodel w ridentity) v) (rapply (@wden kmodel w' ridentity) v).
Proof.
  induction 1 as [|s w w' Hs Hw IH|h v v' w w' Ht Hw IH]; intros x; [left; reflexivity| |].
  - destruct s as [h v|h|a]; [| |contradiction]; cbn [wden sden kmodel cpush cpop]; unfold kpush, kpop.
    + rewrite !rapply_push_inner; destruct (rvar_eqb x _); [left; reflexivity|apply IH].
    + rewrite !rapply_compose, !Laws.rapply_shift; apply IH.
  - cbn [wden sden kmodel cpush]; unfold kpush; rewrite !rapply_push_inner; destruct (rvar_eqb x _); [|apply IH].
    destruct Ht as [E|[u [ρ [E1 E2]]]]; [rewrite E; left; reflexivity|].
    rewrite E1, E2; right; exists u, ρ; split; reflexivity.
Qed.

Lemma kword_meaning l e : lfacts_ok lenv l -> aok (List.length tenv) e = true ->
  @wden kmodel (CNorm.norm (order_of l) e []) ridentity = aeden e.
Proof.
  intros Hl Ha; rewrite (norm_meaning kmodel _ (kcons _ (order_of_ok lenv l Hl))).
  destruct (kden (List.length tenv) (le_n _)) as [Ka _]; rewrite (Ka e Ha); apply rcompose_identity_l.
Qed.

Lemma hmat_ids_aux F (Hirr : forall a, lt_known F a a = false)
  (Htr : forall a b c, lt_known F a b = true -> lt_known F b c = true -> lt_known F a c = true)
  (P : nat -> nat -> aexp -> Prop) :
  forall (facts : list (nat * nat * aexp)) (acc : list (nat * nat * positive)) (T0 : HNorm.st), Inv T0 ->
  (forall k u i, In (k, u, i) acc -> exists eb, P k u eb /\ RId T0 i (CNorm.clean None (CNorm.norm F eb []))) ->
  (forall k u eb, In (k, u, eb) facts -> P k u eb) ->
  Inv (snd (fold_left (fun '(acc, T) '(k, u, eb) =>
      let '(wb, T1) := HNorm.norm F eb [] T in let '(wb', T2) := HNorm.clean None wb T1 in ((k, u, HNorm.wid wb') :: acc, T2))
      facts (acc, T0)))
  /\ Ext T0 (snd (fold_left (fun '(acc, T) '(k, u, eb) =>
      let '(wb, T1) := HNorm.norm F eb [] T in let '(wb', T2) := HNorm.clean None wb T1 in ((k, u, HNorm.wid wb') :: acc, T2))
      facts (acc, T0)))
  /\ forall k u i, In (k, u, i) (fst (fold_left (fun '(acc, T) '(k, u, eb) =>
      let '(wb, T1) := HNorm.norm F eb [] T in let '(wb', T2) := HNorm.clean None wb T1 in ((k, u, HNorm.wid wb') :: acc, T2))
      facts (acc, T0))) ->
      exists eb, P k u eb /\ RId (snd (fold_left (fun '(acc, T) '(k, u, eb) =>
      let '(wb, T1) := HNorm.norm F eb [] T in let '(wb', T2) := HNorm.clean None wb T1 in ((k, u, HNorm.wid wb') :: acc, T2))
      facts (acc, T0))) i (CNorm.clean None (CNorm.norm F eb [])).
Proof.
  induction facts as [|[[k0 u0] eb0] facts IH]; intros acc T0 I0 Hacc Hf; cbn [fold_left].
  - split; [exact I0|split; [apply Ext_refl|exact Hacc]].
  - destruct (HNorm.norm F eb0 [] T0) as [wb T1] eqn:Eb; destruct (HNorm.clean None wb T1) as [wb' T2] eqn:Ec.
    destruct (proj1 (norm_spec_all F Hirr Htr) eb0 [] T0 [] wb T1 I0 (RWNil _) Eb) as [I1 [X1 R1]].
    destruct (clean_spec T1 None wb _ wb' T2 I1 R1 Ec) as [I2 [X2 R2]].
    destruct (IH ((k0, u0, HNorm.wid wb') :: acc) T2 I2) as [I3 [X3 H3]].
    + intros k u i [E|Hi].
      * injection E as <- <- <-; exists eb0; split; [apply Hf; left; reflexivity|apply RWord_RId, R2].
      * destruct (Hacc k u i Hi) as [eb [Hp Hr]]; exists eb; split; [exact Hp|].
        exact (proj1 (R_mono _ _ (Ext_trans _ _ _ X1 X2)) _ _ Hr).
    + intros k u eb Hi; apply Hf; right; exact Hi.
    + split; [exact I3|split; [exact (Ext_trans _ _ _ (Ext_trans _ _ _ X1 X2) X3)|exact H3]].
Qed.

Lemma RStep_SE_term S h u b p cs : RStep S (HNorm.SE h (HNorm.VTerm u b p)) cs ->
  exists cp, cs = CNorm.SE h (CNorm.VTerm u b cp) /\ RId S p cp.
Proof. intros H; inversion H as [? ? cv Hv| |]; subst; destruct (RVal_term _ _ _ _ _ Hv) as [cp [-> Hp]]; eexists; split; [reflexivity|exact Hp]. Qed.

Theorem hmat_sound l (facts : list (nat * nat * aexp)) e e' : lfacts_ok lenv l ->
  hmat_check (order_of l) (List.length tenv) facts e e' = true ->
  Forall (fun f => let '(k, u, eb) := f in forall y, nth_error tenv u = Some y ->
            nth_error tenv k = Some (g (rpcompose (aeden eb) rpidentity) y)) facts ->
  forall v, mrel g (rapply (aeden e) v) (rapply (aeden e') v).
Proof.
  intros Hl H Hfacts; unfold hmat_check in H.
  apply andb_true_iff in H as [H Hw]; apply andb_true_iff in H as [H Hfs]; apply andb_true_iff in H as [Ha Ha'].
  set (F := order_of l) in *.
  pose proof (order_of_irrefl l lenv Hl) as Hirr; pose proof (order_of_trans l lenv Hl) as Htr.
  destruct (HNorm.norm F e [] HNorm.st0) as [w T1] eqn:E1; destruct (HNorm.norm F e' [] T1) as [w' T2] eqn:E2.
  unfold hmat_ids in Hw.
  destruct (proj1 (norm_spec_all F Hirr Htr) e [] HNorm.st0 [] w T1 Inv_st0 (RWNil _) E1) as [I1 [X1 R1]].
  destruct (proj1 (norm_spec_all F Hirr Htr) e' [] T1 [] w' T2 I1 (RWNil _) E2) as [I2 [X2 R2]].
  destruct (hmat_ids_aux F Hirr Htr (fun k u eb => In (k, u, eb) facts) facts [] T2 I2
              (fun _ _ _ Hi => match Hi with end) (fun _ _ _ Hi => Hi)) as [I3 [X3 H3]].
  destruct (fold_left _ facts ([], T2)) as [ids T3] eqn:Ef; cbn [fst snd] in I3, X3, H3.
  pose proof (proj1 (R_mono _ _ (Ext_trans _ _ _ X2 X3)) _ _ (RWord_RId _ _ _ R1)) as _.
  assert (RW1 : RWord T3 w (CNorm.norm F e [])) by exact (RWord_mono _ _ (Ext_trans _ _ _ X2 X3) _ _ R1).
  assert (RW2 : RWord T3 w' (CNorm.norm F e' [])) by exact (RWord_mono _ _ X3 _ _ R2).
  rewrite <- (kword_meaning l e Hl Ha), <- (kword_meaning l e' Hl Ha'); fold F; apply matw_mrel.
  clear E1 E2 R1 R2 Ef; revert Hw RW2; generalize (CNorm.norm F e' []) as cw'; generalize w'.
  induction RW1 as [|s i w0 cs cw Hc Hs Hw0 IH]; intros w2 cw' Hw RW2; destruct w2 as [|[s' i'] w2]; cbn [hmat_walk] in Hw; try discriminate.
  - inversion RW2; constructor.
  - inversion RW2 as [|? ? ? cs' cw2 Hc' Hs' Hw2]; subst.
    apply andb_true_iff in Hw as [Hw Hrest]; apply andb_true_iff in Hw as [Hna Hst].
    apply orb_true_iff in Hst as [Hst|Hst].
    + apply hstep_eqb_eq in Hst; subst s'.
      pose proof (proj1 (proj2 (R_func _ I3)) _ _ Hs _ Hs') as <-.
      apply MSame; [destruct s; inversion Hs; subst; try exact I; discriminate|apply (IH _ _ Hrest Hw2)].
    + destruct s as [h [| u [b|] p |] | |]; try discriminate; destruct s' as [h' [| k [b'|] q |] | |]; try discriminate.
      apply andb_true_iff in Hst as [Hst Hex]; apply andb_true_iff in Hst as [Hh Hq].
      apply lexp_eqb_eq in Hh; subst h'; apply Pos.eqb_eq in Hq; subst q.
      apply existsb_exists in Hex as [[[k1 u1] i1] [Hin Hm]].
      apply andb_true_iff in Hm as [Hm Hp]; apply andb_true_iff in Hm as [Hk Hu].
      apply Nat.eqb_eq in Hk, Hu; apply Pos.eqb_eq in Hp; subst k1 u1 i1.
      destruct (H3 _ _ _ Hin) as [eb [Hinf Hr]].
      destruct (RStep_SE_term _ _ _ _ _ _ Hs) as [cp [-> Hcp]].
      destruct (RStep_SE_term _ _ _ _ _ _ Hs') as [cq [-> Hcq]].
      pose proof (proj1 (R_func _ I3) _ _ Hcp _ Hr) as ->.
      pose proof (proj1 (R_func _ I3) _ _ Hcq _ (RNil _)) as ->.
      apply MEnt; [|apply (IH _ _ Hrest Hw2)].
      rewrite forallb_forall in Hfs; pose proof (Hfs _ Hinf) as Hok; cbn in Hok.
      apply andb_true_iff in Hok as [Hok Hb]; apply andb_true_iff in Hok as [Hk Hu]; apply Nat.ltb_lt in Hk, Hu.
      rewrite Forall_forall in Hfacts; pose proof (Hfacts _ Hinf) as Hf; cbn in Hf.
      destruct (nth_error tenv u) as [y|] eqn:Ey; [|apply nth_error_None in Ey; lia].
      pose proof (Hf y eq_refl) as Ek.
      pose proof (clean_sound kmodel F (kcons _ (order_of_ok lenv l Hl)) u None (CNorm.norm F eb []) ridentity) as Cs.
      change (kterm u None (@wden kmodel (CNorm.clean None (CNorm.norm F eb [])) ridentity)
              = kterm u None (@wden kmodel (CNorm.norm F eb []) ridentity)) in Cs.
      unfold kterm in Cs; rewrite Ey in Cs.
      apply (f_equal (fun t => match t with RBind _ ρ => ρ | _ => rpidentity end)) in Cs.
      rewrite (kword_meaning l eb Hl Hb : @wden kmodel (CNorm.norm F eb []) ridentity = aeden eb) in Cs.
      change (bden penv None) with (@rpidentity T) in Cs.
      rewrite !vden_term.
      change (tmrel (kterm u None (@wden kmodel (CNorm.clean None (CNorm.norm F eb [])) ridentity))
                    (kterm k None (@wden kmodel [] ridentity))).
      unfold kterm; rewrite Ey, Ek; change (bden penv None) with (@rpidentity T).
      change (@wden kmodel [] ridentity) with (@ridentity T); rewrite rpcompose_identity.
      right; exists y, (rpcompose (aeden eb) rpidentity); split; [rewrite Cs; reflexivity|reflexivity].
Qed.

End Mat.

End Concrete.
