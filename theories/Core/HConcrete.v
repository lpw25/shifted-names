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

From Stdlib Require Import List Arith Lia Bool.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise GEval CNorm Comp HNorm KnownOrder HRefine.
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

End Concrete.
