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
  | TBindE u p => Nat.ltb u n && aok n p
  | TShiftE _ t => tok n t
  | TLookE _ _ a => aok n a
  end.

(** The decision used by the [names] tactic. *)
Definition hn_eq_t (F : order) (n : nat) (e1 e2 : aexp) : bool := aok n e1 && aok n e2 && HNorm.hn_eq F e1 e2.

(** Where the normal form of [e] sends [hᵢ]. *)
Definition hlook (F : order) (n : nat) (e : aexp) (h : lexp) (i : nat) : option (HNorm.val * HNorm.st) :=
  if aok n e then let '(w, T0) := HNorm.norm F e [] HNorm.st0 in Some (HNorm.lookup F h i w T0) else None.

Definition hlook_var (F : order) (n : nat) (e : aexp) (h : lexp) (i : nat) : option (lexp * nat) :=
  match hlook F n e h i with Some (HNorm.VVar h' j, _) => Some (h', j) | _ => None end.

(** [hᵢ] goes to the term [u] whose payload [eb] shows: [eb] normalises
    to the payload's own word. *)
Definition hbind_check (F : order) (n : nat) (e : aexp) (h : lexp) (i : nat) (eb : aexp) (u : nat) : bool :=
  aok n eb &&
  match hlook F n e h i with
  | Some (HNorm.VTerm u' p, T1) =>
      Nat.eqb u u' && (let '(wb, _) := HNorm.norm F eb [] T1 in Pos.eqb (HNorm.wid wb) p)
  | _ => false
  end.


Section Concrete.

Context {T : Type}.
Variables (lenv : list label) (tenv : list T) (aenv : list (radj T)).

Local Notation lden := (lden lenv).
Local Notation aeden := (aeden lenv tenv aenv).
Local Notation teden := (teden lenv tenv aenv).

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

Definition kterm (u : nat) (x : radj T) : rtarget T :=
  match nth_error tenv u with Some w => RBind w x | None => RRename (mk_rvar None 0) end.

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

(** Reading a target through [x] after the weakening past [h]. *)
Lemma rapply_target_shift h (x : radj T) (t : rtarget T) :
  rapply_target (rcompose x (Laws.rshift (lden h))) t = rapply_target x (rshift_target (lden h) t).
Proof.
  destruct t as [w|u ρ]; cbn [rapply_target rshift_target].
  - rewrite rapply_compose, Laws.rapply_shift; reflexivity.
  - rewrite rpush_outer_as_compose, rcompose_assoc; reflexivity.
Qed.

Lemma rapply_target_compose (a b : radj T) w :
  rapply_target (rcompose a b) (RRename w) = rapply_target a (rapply_target b (RRename w)).
Proof.
  unfold rapply_target; rewrite rapply_compose.
  destruct (rapply b w) as [v|[u ρ]]; [|reflexivity].
  destruct (rapply a v) as [v'|[u' ρ']]; reflexivity.
Qed.

Lemma khd_target_iter h i x :
  rapply_target (iter i (kpop h) x) (RRename (mk_rvar (lden h) 0)) = rapply_target x (RRename (mk_rvar (lden h) (i + 0))).
Proof. unfold rapply_target; rewrite (khd_iter h i x 0); reflexivity. Qed.

(** An expression acts on [x] as [x] composed with its denotation. *)
Lemma kden n : n <= List.length tenv ->
  (forall a, aok n a = true -> forall x, @ca kmodel a x = rcompose x (aeden a))
  /\ (forall t, tok n t = true -> forall x, @ct kmodel t x = rapply_target x (teden t)).
Proof.
  intros Hn; apply exp_mind; cbn [aok tok ca ct Normalise.aeden Normalise.teden].
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
  - intros h t IH H x; rewrite (IH H); cbn [kmodel cpop]; unfold kpop; apply rapply_target_shift.
  - intros h i a IH H x; unfold cname; cbn [kmodel chd cpop cU]; unfold khd.
    rewrite (khd_target_iter h i), (IH H), Nat.add_0_r; apply rapply_target_compose.
Qed.

Lemma shift_other l l' j : l' <> l -> shift_rvar (mk_rvar l 0) (mk_rvar l' j) = mk_rvar l' j.
Proof.
  intros Ne; unfold shift_rvar; cbn [v_label v_index].
  destruct (label_eqb_spec l l') as [->|_]; [contradiction|reflexivity].
Qed.

(** The model is consistent with facts that hold. *)
Lemma kcons F : facts_ok lenv F -> ccons F kmodel.
Proof.
  intros HF g h L x; pose proof (lt_known_sound lenv F HF g h L) as Lt.
  assert (Ne : lden g <> lden h) by (intros E; rewrite E in Lt; exact (olabel_lt_irrefl _ Lt)).
  cbn [kmodel cpop chd]; unfold kpop, khd, rapply_target; split; [|split].
  - rewrite <- !rcompose_assoc, rcompose_shift_comm; reflexivity.
  - rewrite rapply_compose, Laws.rapply_shift, shift_other by exact Ne; reflexivity.
  - rewrite rapply_compose, Laws.rapply_shift, shift_other by (intros E; apply Ne; symmetry; exact E); reflexivity.
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

Lemma RVal_term S u p cv : RVal S (HNorm.VTerm u p) cv -> exists cp, cv = CNorm.VTerm u cp /\ RId S p cp.
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
  rapply (aeden e) (mk_rvar (lden h) i) = inr (x, aeden eb).
Proof.
  intros Hl H Hx; unfold hbind_check, hlook in H; apply andb_true_iff in H as [Hb H].
  destruct (aok _ e) eqn:Ha; [|discriminate].
  set (F := order_of l) in *.
  destruct (HNorm.norm F e [] HNorm.st0) as [w T0] eqn:En; destruct (HNorm.lookup F h i w T0) as [v T1] eqn:El.
  destruct v as [|u' p|]; try discriminate.
  apply andb_true_iff in H as [Hu H]; apply Nat.eqb_eq in Hu; subst u'.
  destruct (HNorm.norm F eb [] T1) as [wb T2] eqn:Eb.
  apply Pos.eqb_eq in H.
  pose proof (order_of_irrefl l lenv Hl) as Hirr; pose proof (order_of_trans l lenv Hl) as Htr.
  destruct (proj1 (norm_spec_all F Hirr Htr) e [] HNorm.st0 [] w T0 Inv_st0 (RWNil _) En) as [I1 [_ R1]].
  destruct (lookup_spec F Hirr Htr T0 h w _ I1 R1 i _ T1 El) as [I2 [_ R2]].
  destruct (proj1 (norm_spec_all F Hirr Htr) eb [] T1 [] wb T2 I2 (RWNil _) Eb) as [I3 [X3 R3]].
  pose proof (klookup l e h i Hl Ha) as K; fold F in K.
  destruct (RVal_term _ _ _ _ R2) as [cp [Ecp Rp]]; rewrite Ecp in K.
  pose proof (proj1 (R_mono _ _ X3) _ _ Rp) as Rp'.
  pose proof (RWord_RId _ _ _ R3) as Rb; rewrite H in Rb.
  pose proof (proj1 (R_func _ I3) _ _ Rp' _ Rb) as Ecp2; subst cp.
  pose proof (kcons _ (order_of_ok lenv l Hl)) as HM.
  rewrite vden_term, (norm_meaning kmodel _ HM) in K.
  destruct (kden (List.length tenv) (le_n _)) as [Ka _]; rewrite (Ka eb Hb), rcompose_identity_l in K.
  cbn [kmodel cterm] in K; unfold kterm in K; rewrite Hx in K; unfold rapply_target in K.
  destruct (rapply (aeden e) _) as [w'|[u' ρ]]; [discriminate|injection K as -> ->; reflexivity].
Qed.

Section WRel.

(** Two words step by step the same except for entries whose results are
    related by [B]. *)
Variable B : rresult T -> rresult T -> Prop.

Inductive wrel : CNorm.cword -> CNorm.cword -> Prop :=
| WNil : wrel [] []
| WSame s w w' : wrel w w' -> wrel (s :: w) (s :: w')
| WEnt h v v' w w' : B (rtarget_result (@vden kmodel v ridentity)) (rtarget_result (@vden kmodel v' ridentity)) ->
    wrel w w' -> wrel (CNorm.SE h v :: w) (CNorm.SE h v' :: w').

Lemma wrel_drel w w' : wrel w w' -> forall v, drel B (rapply (@wden kmodel w ridentity) v) (rapply (@wden kmodel w' ridentity) v).
Proof.
  induction 1 as [|s w w' Hw IH|h v v' w w' Ht Hw IH]; intros x; [apply DEq| |].
  - destruct s as [h v|h|a]; cbn [wden sden kmodel cpush cpop catom]; unfold kpush, kpop.
    + rewrite !rapply_push_inner; destruct (rvar_eqb x _); [apply DEq|apply IH].
    + rewrite !rapply_compose, !Laws.rapply_shift; apply IH.
    + rewrite !rapply_compose; destruct (rapply (aden aenv a) x) as [w0|[u ρ]]; [apply IH|apply DPay, IH].
  - cbn [wden sden kmodel cpush]; unfold kpush; rewrite !rapply_push_inner; destruct (rvar_eqb x _); [|apply IH].
    apply DBase, Ht.
Qed.

End WRel.

Lemma kword_meaning l e : lfacts_ok lenv l -> aok (List.length tenv) e = true ->
  @wden kmodel (CNorm.norm (order_of l) e []) ridentity = aeden e.
Proof.
  intros Hl Ha; rewrite (norm_meaning kmodel _ (kcons _ (order_of_ok lenv l Hl))).
  destruct (kden (List.length tenv) (le_n _)) as [Ka _]; rewrite (Ka e Ha); apply rcompose_identity_l.
Qed.

Lemma RStep_SE_term S h u p cs : RStep S (HNorm.SE h (HNorm.VTerm u p)) cs ->
  exists cp, cs = CNorm.SE h (CNorm.VTerm u cp) /\ RId S p cp.
Proof. intros H; inversion H as [? ? cv Hv| |]; subst; destruct (RVal_term _ _ _ _ Hv) as [cp [-> Hp]]; eexists; split; [reflexivity|exact Hp]. Qed.


End Concrete.
