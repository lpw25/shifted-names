(** * A concrete λ-calculus over shifted names (unindexed)

    Variables are shifted names; [tlam] binds the anonymous label (bound
    variables are [None₍ᵢ₎]).  Substitution acts through adjustments whose
    payloads are closed terms (no bound variables) with a lazily applied
    payload adjustment.  The laws of the substitution calculus hold with
    Leibniz equality, by induction on terms and on payload nesting depth,
    plus the adjustment laws.

    This file is an example client: the library knows nothing about these
    terms. *)

From Stdlib Require Import Arith List Lia Bool StrictProp.
From ShiftedNames.Core Require Import Label Var Nested Adjustment Laws.

Inductive term : Type :=
| tvar (v : var)
| tconst (n : nat)
| tapp (t1 t2 : term)
| tlam (b : term).

(** ** Scoping *)

Definition wf_var (N : nat) (v : var) : bool :=
  match v_label v with
  | None => Nat.ltb (v_index v) N
  | Some _ => true
  end.

Fixpoint wf_term (N : nat) (t : term) : bool :=
  match t with
  | tvar v => wf_var N v
  | tconst _ => true
  | tapp t1 t2 => wf_term N t1 && wf_term N t2
  | tlam b => wf_term (S N) b
  end.

(** Payload terms: terms with no bound variables. *)
Record cterm : Type := mk_ct { ct : term; ct_wf : Is_true_s (wf_term 0 ct) }.

Lemma cterm_eq (u1 u2 : cterm) : ct u1 = ct u2 -> u1 = u2.
Proof. destruct u1, u2; cbn; intros ->; reflexivity. Qed.

Definition sub := adjustment cterm.

(** ** Substitution

    At a payload [(u, ρ)] substitution continues with [ρ] on [u]; [ρ] is
    nested strictly less deeply, so the fuel is the nesting depth. *)

Fixpoint subst_f (n : nat) : sub -> term -> term :=
  fix go (s : sub) (t : term) : term :=
    match t with
    | tvar v =>
        match apply s v with
        | inl w => tvar w
        | inr p =>
            match n with
            | 0 => ct (fst p)
            | S n' => subst_f n' (padj_adj (snd p)) (ct (fst p))
            end
        end
    | tconst k => tconst k
    | tapp t1 t2 => tapp (go s t1) (go s t2)
    | tlam b => tlam (go (lift None s) b)
    end.

Definition subst (s : sub) (t : term) : term := subst_f (depth s) s t.

Lemma subst_f_fuel n :
  forall m s t, depth s <= n -> depth s <= m -> subst_f n s t = subst_f m s t.
Proof.
  induction n as [|n IHn]; intros m s t Hn Hm;
    [pose proof (ndepth_pos (adj_n s)); unfold depth in *; lia|].
  destruct m as [|m]; [pose proof (ndepth_pos (adj_n s)); unfold depth in *; lia|].
  revert s Hn Hm; induction t as [v|k|t1 IH1 t2 IH2|b IH]; intros s Hn Hm; cbn.
  - destruct (apply s v) as [w|[u ρ]] eqn:E; [reflexivity|].
    pose proof (depth_payload s v u ρ E).
    apply IHn; cbn [snd]; rewrite depth_padj; lia.
  - reflexivity.
  - rewrite IH1, IH2 by assumption; reflexivity.
  - pose proof (depth_lift None s); rewrite IH by lia; reflexivity.
Qed.

(** The defining equations of [subst]. *)

Lemma subst_var s v :
  subst s (tvar v)
  = match apply s v with
    | inl w => tvar w
    | inr p => subst (padj_adj (snd p)) (ct (fst p))
    end.
Proof.
  unfold subst; destruct (depth s) as [|d] eqn:Ed;
    [pose proof (ndepth_pos (adj_n s)); unfold depth in *; lia|].
  cbn; destruct (apply s v) as [w|[u ρ]] eqn:E; [reflexivity|].
  pose proof (depth_payload s v u ρ E).
  cbn [fst snd]; unfold subst; apply subst_f_fuel; rewrite ?depth_padj; lia.
Qed.

Lemma depth_S (s : sub) : exists d, depth s = S d.
Proof.
  pose proof (ndepth_pos (adj_n s)); unfold depth.
  destruct (ndepth (adj_n s)) as [|d]; [lia|exists d; reflexivity].
Qed.

Lemma subst_const s k : subst s (tconst k) = tconst k.
Proof. unfold subst; destruct (depth_S s) as [d ->]; reflexivity. Qed.

Lemma subst_app s t1 t2 : subst s (tapp t1 t2) = tapp (subst s t1) (subst s t2).
Proof. unfold subst; destruct (depth_S s) as [d ->]; reflexivity. Qed.

Lemma subst_lam s b : subst s (tlam b) = tlam (subst (lift None s) b).
Proof.
  unfold subst at 1; destruct (depth_S s) as [d Ed]; rewrite Ed.
  change (subst_f (S d) s (tlam b)) with (tlam (subst_f (S d) (lift None s) b)); f_equal.
  unfold subst; apply subst_f_fuel; [pose proof (depth_lift None s); lia|lia].
Qed.

Global Opaque subst.

(** ** Substitution only looks at the variables of the term *)

Definition agree (k : nat) (a b : sub) : Prop :=
  forall v, (v_label v <> None \/ v_index v < k) -> apply a v = apply b v.

Lemma agree_lift k a b : agree k a b -> agree (S k) (lift None a) (lift None b).
Proof.
  intros H v Hv; rewrite !apply_lift.
  destruct (var_eqb_spec v (mk_var None 0)) as [->|Hne]; [reflexivity|].
  rewrite H; [reflexivity|].
  destruct v as [[x|] i]; cbn [v_label v_index unshift_var] in *; [left; discriminate|].
  right; unfold unshift_var; cbn [v_label v_index label_eqb andb].
  destruct i as [|i]; [exfalso; apply Hne; reflexivity|].
  destruct Hv as [Hv|Hv]; [exfalso; apply Hv; reflexivity|]; cbn in *; lia.
Qed.

Lemma subst_agree t :
  forall k a b, wf_term k t = true -> agree k a b -> subst a t = subst b t.
Proof.
  induction t as [v|n|t1 IH1 t2 IH2|b' IH]; intros k a b Hwf Hab.
  - rewrite !subst_var, Hab; [reflexivity|].
    unfold wf_term, wf_var in Hwf; destruct v as [[x|] i]; cbn in *;
      [left; discriminate|right; apply Nat.ltb_lt, Hwf].
  - rewrite !subst_const; reflexivity.
  - cbn [wf_term] in Hwf; apply andb_true_iff in Hwf as [H1 H2].
    rewrite !subst_app, (IH1 k a b), (IH2 k a b) by assumption; reflexivity.
  - rewrite !subst_lam; f_equal; apply (IH (S k)); [exact Hwf|apply agree_lift, Hab].
Qed.

(** A payload term only sees the free variables of its adjustment, so
    restricting a composite at the bound label changes nothing. *)
Lemma subst_pcompose a ρ (u : cterm) :
  subst (padj_adj (pcompose a ρ)) (ct u) = subst (compose a (padj_adj ρ)) (ct u).
Proof.
  apply (subst_agree _ 0); [apply Is_true_s_elim, ct_wf|].
  intros v [Hv|Hv]; [|lia].
  change (apply (padj_adj (pcompose a ρ)) v) with (papply (pcompose a ρ) v).
  rewrite papply_pcompose, apply_compose by exact Hv; reflexivity.
Qed.

(** ** The laws *)

Theorem subst_identity t : subst identity t = t.
Proof.
  induction t as [v|n|t1 IH1 t2 IH2|b IH].
  - rewrite subst_var, apply_identity; reflexivity.
  - apply subst_const.
  - rewrite subst_app, IH1, IH2; reflexivity.
  - rewrite subst_lam, lift_identity, IH; reflexivity.
Qed.

Lemma subst_subst_depth n :
  forall t b a, depth b <= n -> subst a (subst b t) = subst (compose a b) t.
Proof.
  induction n as [|n IHn]; intros t b a Hb;
    [pose proof (ndepth_pos (adj_n b)); unfold depth in *; lia|].
  revert b a Hb; induction t as [v|k|t1 IH1 t2 IH2|body IH]; intros b a Hb.
  - rewrite (subst_var b), (subst_var (compose a b)), apply_compose.
    destruct (apply b v) as [w|[u ρ]] eqn:E; [rewrite subst_var; reflexivity|]; cbn [fst snd].
    pose proof (depth_payload b v u ρ E).
    rewrite IHn by (rewrite depth_padj; lia).
    symmetry; apply subst_pcompose.
  - rewrite !subst_const; reflexivity.
  - rewrite !subst_app, IH1, IH2 by assumption; reflexivity.
  - rewrite !subst_lam, IH by (pose proof (depth_lift None b); lia).
    rewrite lift_compose; reflexivity.
Qed.

Theorem subst_subst a b t : subst a (subst b t) = subst (compose a b) t.
Proof. apply (subst_subst_depth (depth b)); lia. Qed.

(** ** Locally nameless operations *)

(** Instantiating the innermost bound variable with a closed term. *)
Definition instantiate (b : term) (u : cterm) : term :=
  subst (subst1 None u (to_padj nidentity)) b.

Definition open_term (x : label) (b : term) : term := subst (open x) b.
Definition close_term (x : label) (t : term) : term := subst (close x) t.

Theorem open_close x t : open_term x (close_term x t) = t.
Proof.
  unfold open_term, close_term; rewrite subst_subst.
  replace (compose (open x) (close x)) with (@identity cterm); [apply subst_identity|].
  apply extensionality; intro v.
  rewrite apply_compose, apply_identity; unfold open, close; rewrite !apply_rename1.
  destruct v as [h i]; unfold var_eqb, shift_var, unshift_var; cbn [v_label v_index].
  case_vars; rewrite ?apply_rename1; unfold var_eqb, shift_var, unshift_var;
    cbn [v_label v_index]; case_vars.
Qed.
