(** * A concrete λ-calculus over shifted names (unindexed)

    Variables are shifted names; [rtlam] binds the anonymous label (bound
    variables are [None₍ᵢ₎]).  Substitution acts through adjustments whose
    payloads are closed terms (no bound variables) with a lazily applied
    payload adjustment.  The laws of the substitution calculus hold with
    Leibniz equality, by induction on terms and on payload nesting depth,
    plus the adjustment laws.

    This file is an example client: the library knows nothing about these
    terms. *)

From Stdlib Require Import Arith List Lia Bool StrictProp.
From ShiftedNames.Core Require Import Label Var Nested Adjustment Laws Scoped.

Inductive rterm : Type :=
| rtvar (v : rvar)
| rtconst (n : nat)
| rtapp (t1 t2 : rterm)
| rtlam (b : rterm).

(** ** Scoping *)

Fixpoint wf_term (N : nat) (t : rterm) : bool :=
  match t with
  | rtvar v => wf_var N v
  | rtconst _ => true
  | rtapp t1 t2 => wf_term N t1 && wf_term N t2
  | rtlam b => wf_term (S N) b
  end.

(** Payload terms: terms with no bound variables. *)
Record cterm : Type := mk_ct { ct : rterm; ct_wf : Is_true_s (wf_term 0 ct) }.

Lemma cterm_eq (u1 u2 : cterm) : ct u1 = ct u2 -> u1 = u2.
Proof. destruct u1, u2; cbn; intros ->; reflexivity. Qed.

Definition rsub := radj cterm.

(** ** Substitution

    At a payload [(u, ρ)] substitution continues with [ρ] on [u]; [ρ] is
    nested strictly less deeply, so the fuel is the nesting depth. *)

Fixpoint rsubst_f (n : nat) : rsub -> rterm -> rterm :=
  fix go (s : rsub) (t : rterm) : rterm :=
    match t with
    | rtvar v =>
        match rapply s v with
        | inl w => rtvar w
        | inr p =>
            match n with
            | 0 => ct (fst p)
            | S n' => rsubst_f n' (rpadj_adj (snd p)) (ct (fst p))
            end
        end
    | rtconst k => rtconst k
    | rtapp t1 t2 => rtapp (go s t1) (go s t2)
    | rtlam b => rtlam (go (rlift None s) b)
    end.

Definition rsubst (s : rsub) (t : rterm) : rterm := rsubst_f (rdepth s) s t.

Lemma rsubst_f_fuel n :
  forall m s t, rdepth s <= n -> rdepth s <= m -> rsubst_f n s t = rsubst_f m s t.
Proof.
  induction n as [|n IHn]; intros m s t Hn Hm;
    [pose proof (ndepth_pos (radj_n s)); unfold rdepth in *; lia|].
  destruct m as [|m]; [pose proof (ndepth_pos (radj_n s)); unfold rdepth in *; lia|].
  revert s Hn Hm; induction t as [v|k|t1 IH1 t2 IH2|b IH]; intros s Hn Hm; cbn.
  - destruct (rapply s v) as [w|[u ρ]] eqn:E; [reflexivity|].
    pose proof (rdepth_payload s v u ρ E).
    apply IHn; cbn [snd]; rewrite rdepth_padj; lia.
  - reflexivity.
  - rewrite IH1, IH2 by assumption; reflexivity.
  - pose proof (rdepth_lift None s); rewrite IH by lia; reflexivity.
Qed.

(** The defining equations of [rsubst]. *)

Lemma rsubst_var s v :
  rsubst s (rtvar v)
  = match rapply s v with
    | inl w => rtvar w
    | inr p => rsubst (rpadj_adj (snd p)) (ct (fst p))
    end.
Proof.
  unfold rsubst; destruct (rdepth s) as [|d] eqn:Ed;
    [pose proof (ndepth_pos (radj_n s)); unfold rdepth in *; lia|].
  cbn; destruct (rapply s v) as [w|[u ρ]] eqn:E; [reflexivity|].
  pose proof (rdepth_payload s v u ρ E).
  cbn [fst snd]; unfold rsubst; apply rsubst_f_fuel; rewrite ?rdepth_padj; lia.
Qed.

Lemma depth_S (s : rsub) : exists d, rdepth s = S d.
Proof.
  pose proof (ndepth_pos (radj_n s)); unfold rdepth.
  destruct (ndepth (radj_n s)) as [|d]; [lia|exists d; reflexivity].
Qed.

Lemma rsubst_const s k : rsubst s (rtconst k) = rtconst k.
Proof. unfold rsubst; destruct (depth_S s) as [d ->]; reflexivity. Qed.

Lemma rsubst_app s t1 t2 : rsubst s (rtapp t1 t2) = rtapp (rsubst s t1) (rsubst s t2).
Proof. unfold rsubst; destruct (depth_S s) as [d ->]; reflexivity. Qed.

Lemma rsubst_lam s b : rsubst s (rtlam b) = rtlam (rsubst (rlift None s) b).
Proof.
  unfold rsubst at 1; destruct (depth_S s) as [d Ed]; rewrite Ed.
  change (rsubst_f (S d) s (rtlam b)) with (rtlam (rsubst_f (S d) (rlift None s) b)); f_equal.
  unfold rsubst; apply rsubst_f_fuel; [pose proof (rdepth_lift None s); lia|lia].
Qed.

Global Opaque rsubst.

(** ** Substitution only looks at the variables of the term *)

Definition agree (k : nat) (a b : rsub) : Prop :=
  forall v, (v_label v <> None \/ v_index v < k) -> rapply a v = rapply b v.

Lemma agree_lift k a b : agree k a b -> agree (S k) (rlift None a) (rlift None b).
Proof.
  intros H v Hv; rewrite !rapply_lift.
  destruct (rvar_eqb_spec v (mk_rvar None 0)) as [->|Hne]; [reflexivity|].
  rewrite H; [reflexivity|].
  destruct v as [[x|] i]; cbn [v_label v_index unshift_rvar] in *; [left; discriminate|].
  right; unfold unshift_rvar; cbn [v_label v_index label_eqb andb].
  destruct i as [|i]; [exfalso; apply Hne; reflexivity|].
  destruct Hv as [Hv|Hv]; [exfalso; apply Hv; reflexivity|]; cbn in *; lia.
Qed.

Lemma rsubst_agree t :
  forall k a b, wf_term k t = true -> agree k a b -> rsubst a t = rsubst b t.
Proof.
  induction t as [v|n|t1 IH1 t2 IH2|b' IH]; intros k a b Hwf Hab.
  - rewrite !rsubst_var, Hab; [reflexivity|].
    unfold wf_term, wf_var in Hwf; destruct v as [[x|] i]; cbn in *;
      [left; discriminate|right; apply Nat.ltb_lt, Hwf].
  - rewrite !rsubst_const; reflexivity.
  - cbn [wf_term] in Hwf; apply andb_true_iff in Hwf as [H1 H2].
    rewrite !rsubst_app, (IH1 k a b), (IH2 k a b) by assumption; reflexivity.
  - rewrite !rsubst_lam; f_equal; apply (IH (S k)); [exact Hwf|apply agree_lift, Hab].
Qed.

(** A payload term only sees the free variables of its adjustment, so
    restricting a composite at the bound label changes nothing. *)
Lemma rsubst_pcompose a ρ (u : cterm) :
  rsubst (rpadj_adj (rpcompose a ρ)) (ct u) = rsubst (rcompose a (rpadj_adj ρ)) (ct u).
Proof.
  apply (rsubst_agree _ 0); [apply Is_true_s_elim, ct_wf|].
  intros v [Hv|Hv]; [|lia].
  change (rapply (rpadj_adj (rpcompose a ρ)) v) with (rpapply (rpcompose a ρ) v).
  rewrite rpapply_pcompose, rapply_compose by exact Hv; reflexivity.
Qed.

(** ** The laws *)

Theorem rsubst_identity t : rsubst ridentity t = t.
Proof.
  induction t as [v|n|t1 IH1 t2 IH2|b IH].
  - rewrite rsubst_var, rapply_identity; reflexivity.
  - apply rsubst_const.
  - rewrite rsubst_app, IH1, IH2; reflexivity.
  - rewrite rsubst_lam, rlift_identity, IH; reflexivity.
Qed.

Lemma rsubst_subst_depth n :
  forall t b a, rdepth b <= n -> rsubst a (rsubst b t) = rsubst (rcompose a b) t.
Proof.
  induction n as [|n IHn]; intros t b a Hb;
    [pose proof (ndepth_pos (radj_n b)); unfold rdepth in *; lia|].
  revert b a Hb; induction t as [v|k|t1 IH1 t2 IH2|body IH]; intros b a Hb.
  - rewrite (rsubst_var b), (rsubst_var (rcompose a b)), rapply_compose.
    destruct (rapply b v) as [w|[u ρ]] eqn:E; [rewrite rsubst_var; reflexivity|]; cbn [fst snd].
    pose proof (rdepth_payload b v u ρ E).
    rewrite IHn by (rewrite rdepth_padj; lia).
    symmetry; apply rsubst_pcompose.
  - rewrite !rsubst_const; reflexivity.
  - rewrite !rsubst_app, IH1, IH2 by assumption; reflexivity.
  - rewrite !rsubst_lam, IH by (pose proof (rdepth_lift None b); lia).
    rewrite rlift_compose; reflexivity.
Qed.

Theorem rsubst_subst a b t : rsubst a (rsubst b t) = rsubst (rcompose a b) t.
Proof. apply (rsubst_subst_depth (rdepth b)); lia. Qed.

(** ** Substitution preserves scoping *)

Lemma pscoped_pshift_none M (ρ : rpadj cterm) :
  pscoped M ρ = true -> pscoped (S M) (rpshift None ρ) = true.
Proof.
  intros H; rewrite rpshift_as_pcompose.
  apply (pscoped_pcompose M); [apply scoped_shift_none|exact H].
Qed.

Lemma wf_rsubst_depth n :
  forall t a K M, rdepth a <= n -> wf_term K t = true ->
  (forall v, wf_var K v = true -> result_wf M (rapply a v) = true) ->
  wf_term M (rsubst a t) = true.
Proof.
  induction n as [|n IHn]; intros t a K M Hd;
    [pose proof (ndepth_pos (radj_n a)); unfold rdepth in *; lia|].
  revert a K M Hd; induction t as [v|k|t1 IH1 t2 IH2|b IH]; intros a K M Hd Ht Ha.
  - rewrite rsubst_var; specialize (Ha v Ht).
    destruct (rapply a v) as [w|[u ρ]] eqn:E; [exact Ha|]; cbn [fst snd].
    rewrite result_wf_inr in Ha.
    pose proof (rdepth_payload a v u ρ E).
    apply (IHn _ _ 0); [rewrite rdepth_padj; lia|apply Is_true_s_elim, ct_wf|].
    intros [[x|] i] Hv; [|discriminate].
    apply (proj1 (pscoped_spec M ρ) Ha); discriminate.
  - rewrite rsubst_const; reflexivity.
  - cbn [wf_term] in Ht |- *; apply andb_true_iff in Ht as [H1 H2].
    rewrite rsubst_app; cbn [wf_term]; rewrite (IH1 a K M), (IH2 a K M); auto.
  - rewrite rsubst_lam; cbn [wf_term] in *.
    apply (IH _ (S K)); [pose proof (rdepth_lift None a); lia|exact Ht|].
    intros v Hv; rewrite rapply_lift.
    destruct (rvar_eqb_spec v (mk_rvar None 0)) as [->|Hne]; [reflexivity|].
    assert (Hu : wf_var K (unshift_rvar (mk_rvar None 0) v) = true).
    { destruct v as [[x|] i]; unfold unshift_rvar; cbn in *; [reflexivity|].
      destruct i as [|i]; [exfalso; apply Hne; reflexivity|].
      apply Nat.ltb_lt in Hv; apply Nat.ltb_lt; cbn in *; lia. }
    specialize (Ha _ Hu).
    destruct (rapply a (unshift_rvar (mk_rvar None 0) v)) as [w|[u ρ]].
    + rewrite result_wf_inl in *; destruct w as [[x|] i]; unfold shift_rvar; cbn in *;
        [reflexivity|apply Nat.ltb_lt in Ha; apply Nat.ltb_lt; lia].
    + cbn [fst snd]; rewrite result_wf_inr in *; apply pscoped_pshift_none, Ha.
Qed.

Theorem wf_rsubst N M a t :
  scoped N M a = true -> wf_term N t = true -> wf_term M (rsubst a t) = true.
Proof.
  intros Ha Ht; apply (wf_rsubst_depth (rdepth a) t a N M); auto.
  apply (proj2 (proj1 (scoped_spec N M a) Ha)).
Qed.

Theorem wf_payload M (ρ : rpadj cterm) (u : cterm) :
  pscoped M ρ = true -> wf_term M (rsubst (rpadj_adj ρ) (ct u)) = true.
Proof.
  intros H; apply (wf_rsubst_depth (rdepth (rpadj_adj ρ)) _ _ 0 M);
    [lia|apply Is_true_s_elim, ct_wf|].
  intros [[x|] i] Hv; [|discriminate].
  apply (proj1 (pscoped_spec M ρ) H); discriminate.
Qed.

Lemma wf_var_mono N N' v : N <= N' -> wf_var N v = true -> wf_var N' v = true.
Proof.
  destruct v as [[x|] i]; cbn; [reflexivity|].
  intros H1 H2; apply Nat.ltb_lt in H2; apply Nat.ltb_lt; lia.
Qed.

Lemma wf_term_mono t : forall N N', N <= N' -> wf_term N t = true -> wf_term N' t = true.
Proof.
  induction t as [v|n|t1 IH1 t2 IH2|b IH]; intros N N' Hle H; cbn [wf_term] in *.
  - apply (wf_var_mono N); assumption.
  - reflexivity.
  - apply andb_true_iff in H as [H1 H2]; rewrite (IH1 N N'), (IH2 N N'); auto.
  - apply (IH (S N)); [lia|exact H].
Qed.

(** ** Locally nameless operations *)

(** Instantiating the innermost bound variable with a closed term. *)
Definition rinstantiate (b : rterm) (u : cterm) : rterm :=
  rsubst (rsubst1 None u (rto_padj nidentity)) b.

Definition ropen_term (x : label) (b : rterm) : rterm := rsubst (ropen x) b.
Definition rclose_term (x : label) (t : rterm) : rterm := rsubst (rclose x) t.

Theorem ropen_close x t : ropen_term x (rclose_term x t) = t.
Proof.
  unfold ropen_term, rclose_term; rewrite rsubst_subst, rcompose_open_close; apply rsubst_identity.
Qed.

Theorem rclose_open x t : rclose_term x (ropen_term x t) = t.
Proof.
  unfold ropen_term, rclose_term; rewrite rsubst_subst, rcompose_close_open; apply rsubst_identity.
Qed.
