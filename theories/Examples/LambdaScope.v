(** * Scoping for the λ-calculus (internal)

    [wf_term N t]: every bound variable [None₍ᵢ₎] of [t] has [i < N] (taking
    binders into account).  Free names are unrestricted.

    [scoped N M a] says that the adjustment [a] maps terms of scope [N] to
    terms of scope [M], and is canonical outside the scope:

    - every target is well scoped in [M], and payloads are never bare
      variables (a variable target is always a [Rename]);
    - the entry for the anonymous label covers at most [N] positions and has
      offset [M - N], so every out-of-scope [None₍ᵢ₎] ([i ≥ N]) maps to
      [None₍ᵢ₋ₙ₊ₘ₎].

    [scoped_spec] characterises [scoped] semantically, and [scoped_ext]
    shows that scoped adjustments are determined by their action on
    in-scope variables. *)

From Stdlib Require Import Arith List Lia Bool.
From ShiftedNames.Core Require Import Trie Label Var RawAdjustment Adjustment Laws.
From ShiftedNames.Examples Require Import LambdaCore.
Import ListNotations.

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

Definition is_tvar (t : term) : bool :=
  match t with tvar _ => true | _ => false end.

Definition result_ok (M : nat) (r : var + term) : bool :=
  match r with
  | inl w => wf_var M w
  | inr p => wf_term M p && negb (is_tvar p)
  end.

Definition target_ok (M : nat) (t : target term) : bool :=
  result_ok M (target_result t).

Definition none_ok (N M : nat) (e : list (target term) * nat) : bool :=
  Nat.leb (length (fst e)) N && Nat.eqb (length (fst e) + M) (snd e + N).

Definition scoped (N M : nat) (a : adjustment term) : bool :=
  forallb (fun _ e => List.forallb (target_ok M) (e_targets e)) (adj_raw a)
  && none_ok N M (find (adj_raw a) None).

Lemma find_targets_ok M (a : adjustment term) h t :
  forallb (fun _ e => List.forallb (target_ok M) (e_targets e)) (adj_raw a) = true ->
  In t (fst (find (adj_raw a) h)) -> target_ok M t = true.
Proof.
  intros Hall Hin; unfold find in Hin.
  destruct (get (label_key h) (adj_raw a)) as [e|] eqn:E; [|destruct Hin].
  rewrite forallb_spec in Hall; specialize (Hall _ _ E).
  rewrite List.forallb_forall in Hall; apply Hall, Hin.
Qed.

Theorem scoped_spec N M (a : adjustment term) :
  scoped N M a = true <->
  (forall v, wf_var N v = true -> result_ok M (apply a v) = true)
  /\ (forall i, N <= i -> apply a (mk_var None i) = inl (mk_var None (i - N + M))).
Proof.
  unfold scoped, none_ok; rewrite !andb_true_iff, Nat.leb_le, Nat.eqb_eq.
  pose proof (adj_normal_true a) as Hnorm.
  split.
  - intros [Hall [Hle Hoff]]; split.
    + intros [h i] Hwf; unfold apply, RawAdjustment.apply, apply_entry;
        cbn [v_label v_index].
      destruct (nth_error (fst (find (adj_raw a) h)) i) as [t|] eqn:E.
      * apply nth_error_In in E; apply (find_targets_ok M a h t Hall E).
      * apply nth_error_None in E.
        cbn [result_ok]; destruct h as [x|]; [reflexivity|].
        unfold wf_var in *; cbn [v_label v_index] in *.
        apply Nat.ltb_lt in Hwf; apply Nat.ltb_lt; lia.
    + intros i Hi; unfold apply, RawAdjustment.apply, apply_entry;
        cbn [v_label v_index].
      rewrite (proj2 (nth_error_None _ _)) by lia.
      f_equal; f_equal; lia.
  - intros [Hres Hout].
    destruct (find (adj_raw a) None) as [ts k] eqn:EN; cbn [fst snd].
    assert (Hoff : length ts + M = k + N).
    { specialize (Hout (N + length ts) ltac:(lia)).
      unfold apply, RawAdjustment.apply, apply_entry in Hout; cbn [v_label v_index] in Hout.
      rewrite EN in Hout; cbn [fst snd] in Hout.
      rewrite (proj2 (nth_error_None _ _)) in Hout by lia.
      injection Hout; lia. }
    assert (Hle : length ts <= N).
    { destruct (Nat.le_gt_cases (length ts) N) as [H|H]; [exact H|exfalso].
      pose proof (find_minimal (adj_raw a) None Hnorm) as Hmin.
      rewrite EN in Hmin; cbn [fst snd] in Hmin.
      specialize (Hout (length ts - 1) ltac:(lia)).
      unfold apply, RawAdjustment.apply, apply_entry in Hout; cbn [v_label v_index] in Hout.
      rewrite EN in Hout; cbn [fst snd] in Hout.
      unfold minimal, last_target in Hmin.
      rewrite Nat.sub_1_r in Hout.
      destruct (nth_error ts (pred (length ts))) as [[w|p]|] eqn:E.
      - injection Hout as ->; cbn in Hmin.
        destruct k as [|k']; [lia|].
        rewrite (proj2 (Nat.eqb_eq _ _)) in Hmin by lia; discriminate.
      - discriminate.
      - apply nth_error_None in E; lia. }
    split; [|split; [exact Hle|exact Hoff]].
    apply forallb_spec; intros key e He.
    pose proof (normal_get _ _ _ Hnorm He) as Hok.
    apply entry_ok_key in Hok; subst key.
    apply List.forallb_forall; intros t Hin.
    apply In_nth_error in Hin as [i Hi].
    specialize (Hres (mk_var (e_label e) i)).
    unfold apply, RawAdjustment.apply, apply_entry, find in Hres;
      cbn [v_label v_index] in Hres.
    rewrite He in Hres; cbn [fst snd] in Hres; rewrite Hi in Hres.
    apply Hres.
    unfold wf_var; cbn [v_label v_index].
    destruct (e_label e) as [x|] eqn:El; [reflexivity|].
    unfold find in EN; rewrite He in EN; injection EN as Ets _.
    apply Nat.ltb_lt.
    assert (i < length ts) by (rewrite <- Ets; apply nth_error_Some; congruence).
    lia.
Qed.

Theorem scoped_ext N M (a b : adjustment term) :
  scoped N M a = true -> scoped N M b = true ->
  (forall v, wf_var N v = true -> apply a v = apply b v) -> a = b.
Proof.
  intros Ha Hb H; apply extensionality; intros [h i].
  destruct h as [x|]; [apply H; reflexivity|].
  destruct (Nat.lt_ge_cases i N) as [Hi|Hi].
  - apply H; apply Nat.ltb_lt, Hi.
  - apply scoped_spec in Ha as [_ Ha]; apply scoped_spec in Hb as [_ Hb].
    rewrite Ha, Hb by exact Hi; reflexivity.
Qed.

(** ** Scoping is preserved by renaming and substitution *)

Definition maps_ok (N M : nat) (a : adjustment term) : Prop :=
  forall v, wf_var N v = true -> result_ok M (apply a v) = true.

Lemma wf_var_shift_none M w :
  wf_var M w = true -> wf_var (S M) (shift_var (mk_var None 0) w) = true.
Proof.
  destruct w as [[x|] i]; unfold wf_var, shift_var; cbn [v_label v_index];
    [reflexivity|]; cbn [label_eqb andb Nat.leb v_label v_index].
  intro H; apply Nat.ltb_lt in H; apply Nat.ltb_lt; lia.
Qed.

Lemma wf_var_unshift_none N v :
  v <> mk_var None 0 -> wf_var (S N) v = true ->
  wf_var N (unshift_var (mk_var None 0) v) = true.
Proof.
  destruct v as [[x|] [|i]]; unfold wf_var, unshift_var; cbn [v_label v_index];
    try reflexivity; cbn [label_eqb andb Nat.ltb Nat.leb v_label v_index].
  - intro H; exfalso; apply H; reflexivity.
  - intros _ H; apply Nat.ltb_lt in H; apply Nat.ltb_lt; lia.
Qed.

Lemma wf_var_shift_some N x w :
  wf_var N w = true -> wf_var N (shift_var (mk_var (Some x) 0) w) = true.
Proof.
  destruct w as [[y|] i]; unfold wf_var, shift_var; cbn [v_label v_index].
  - destruct (label_eqb _ _ && _); reflexivity.
  - cbn [label_eqb andb]; auto.
Qed.

Lemma wf_rename N M r t :
  (forall v, wf_var N v = true ->
     match apply r v with inl w => wf_var M w = true | inr e => False end) ->
  wf_term N t = true -> wf_term M (rename r t) = true.
Proof.
  revert N M r; induction t as [v|n|t1 IH1 t2 IH2|b IH]; intros N M r Hr Ht;
    cbn [rename wf_term] in *.
  - specialize (Hr v Ht); destruct (apply r v) as [w|[]]; exact Hr.
  - reflexivity.
  - apply andb_true_iff in Ht as [H1 H2].
    rewrite (IH1 N M r Hr H1), (IH2 N M r Hr H2); reflexivity.
  - apply (IH (S N) (S M)); [|exact Ht].
    intros v Hv; rewrite apply_lift.
    destruct (var_eqb_spec v (mk_var None 0)) as [->|Hne]; [reflexivity|].
    specialize (Hr _ (wf_var_unshift_none N v Hne Hv)).
    destruct (apply r _) as [w|[]]; apply wf_var_shift_none, Hr.
Qed.

Lemma not_tvar_rename r t : is_tvar t = false -> is_tvar (rename r t) = false.
Proof. destruct t; cbn; [discriminate|reflexivity..]. Qed.

Lemma not_tvar_subst s t : is_tvar t = false -> is_tvar (subst s t) = false.
Proof. destruct t; cbn; [discriminate|reflexivity..]. Qed.

Lemma wf_shift_term M p : wf_term M p = true -> wf_term (S M) (shift_term p) = true.
Proof.
  apply wf_rename; intros v Hv; rewrite apply_shift; apply wf_var_shift_none, Hv.
Qed.

Lemma wf_shift_some M x p :
  wf_term M p = true -> wf_term M (rename (shift (Some x)) p) = true.
Proof.
  apply wf_rename; intros v Hv; rewrite apply_shift; apply wf_var_shift_some, Hv.
Qed.

Lemma result_ok_shift_none M r :
  result_ok M r = true ->
  result_ok (S M) (match r with
                   | inl w => inl (shift_var (mk_var None 0) w)
                   | inr p => inr (shift_term p)
                   end) = true.
Proof.
  destruct r as [w|p]; cbn [result_ok]; [apply wf_var_shift_none|].
  rewrite !andb_true_iff, !negb_true_iff; intros [H1 H2]; split.
  - apply wf_shift_term, H1.
  - apply not_tvar_rename, H2.
Qed.

Lemma maps_ok_lift N M s :
  maps_ok N M s -> maps_ok (S N) (S M) (lift shift_term None s).
Proof.
  intros Hs v Hv; rewrite apply_lift.
  destruct (var_eqb_spec v (mk_var None 0)) as [->|Hne]; [reflexivity|].
  apply result_ok_shift_none, Hs, wf_var_unshift_none; assumption.
Qed.

Theorem wf_subst N M s t :
  maps_ok N M s -> wf_term N t = true -> wf_term M (subst s t) = true.
Proof.
  revert N M s; induction t as [v|n|t1 IH1 t2 IH2|b IH]; intros N M s Hs Ht;
    cbn [subst wf_term] in *.
  - specialize (Hs v Ht).
    destruct (apply s v) as [w|p]; cbn [result_ok] in Hs; [exact Hs|].
    apply andb_true_iff in Hs as [Hs _]; exact Hs.
  - reflexivity.
  - apply andb_true_iff in Ht as [H1 H2].
    rewrite (IH1 N M s Hs H1), (IH2 N M s Hs H2); reflexivity.
  - apply (IH (S N) (S M)); [apply maps_ok_lift, Hs|exact Ht].
Qed.

Lemma scoped_maps_ok N M a : scoped N M a = true -> maps_ok N M a.
Proof. intros H; apply scoped_spec in H as [H _]; exact H. Qed.

(** ** Scoping is preserved by the constructors and composition *)

Theorem scoped_identity N : scoped N N identity = true.
Proof.
  apply scoped_spec; split.
  - intros v Hv; rewrite apply_identity; exact Hv.
  - intros i Hi; rewrite apply_identity; f_equal; f_equal; lia.
Qed.

Theorem scoped_push_inner_bound N M t a :
  scoped N M a = true -> target_ok M t = true ->
  scoped (S N) M (push_inner None t a) = true.
Proof.
  intros Ha Ht; apply scoped_spec in Ha as [Hin Hout]; apply scoped_spec; split.
  - intros v Hv; rewrite apply_push_inner.
    destruct (var_eqb_spec v (mk_var None 0)) as [->|Hne]; [exact Ht|].
    apply Hin, wf_var_unshift_none; assumption.
  - intros i Hi; rewrite apply_push_inner.
    destruct i as [|i]; [lia|].
    unfold var_eqb, unshift_var; cbn [v_label v_index label_eqb andb Nat.eqb Nat.ltb Nat.leb].
    replace (S i - 1) with i by lia.
    rewrite Hout by lia; f_equal; f_equal; lia.
Qed.

Theorem scoped_push_inner_free N M x t a :
  scoped N M a = true -> target_ok M t = true ->
  scoped N M (push_inner (Some x) t a) = true.
Proof.
  intros Ha Ht; apply scoped_spec in Ha as [Hin Hout]; apply scoped_spec; split.
  - intros v Hv; rewrite apply_push_inner.
    destruct (var_eqb_spec v (mk_var (Some x) 0)) as [->|Hne]; [exact Ht|].
    apply Hin.
    destruct v as [[y|] i]; unfold wf_var, unshift_var in *; cbn [v_label v_index] in *;
      [destruct (label_eqb _ _ && _); reflexivity|exact Hv].
  - intros i Hi; rewrite apply_push_inner.
    unfold var_eqb, unshift_var; cbn [v_label v_index label_eqb andb].
    apply Hout, Hi.
Qed.

Theorem scoped_push_outer_bound N M a :
  scoped N M a = true -> scoped N (S M) (push_outer shift_term None a) = true.
Proof.
  intros Ha; apply scoped_spec in Ha as [Hin Hout]; apply scoped_spec; split.
  - intros v Hv; rewrite apply_push_outer; apply result_ok_shift_none, Hin, Hv.
  - intros i Hi; rewrite apply_push_outer, Hout by exact Hi.
    unfold shift_var; cbn [v_label v_index label_eqb andb Nat.leb].
    f_equal; f_equal; lia.
Qed.

Definition shift_term_some (x : label) (p : term) : term := rename (shift (Some x)) p.

Theorem scoped_push_outer_free N M x a :
  scoped N M a = true ->
  scoped N M (push_outer (shift_term_some x) (Some x) a) = true.
Proof.
  intros Ha; apply scoped_spec in Ha as [Hin Hout]; apply scoped_spec; split.
  - intros v Hv; rewrite apply_push_outer.
    specialize (Hin v Hv).
    destruct (apply a v) as [w|p]; cbn [result_ok] in *.
    + apply wf_var_shift_some, Hin.
    + rewrite andb_true_iff, negb_true_iff in *; destruct Hin as [H1 H2]; split.
      * apply wf_shift_some, H1.
      * apply not_tvar_rename, H2.
  - intros i Hi; rewrite apply_push_outer, Hout by exact Hi.
    unfold shift_var; cbn [v_label v_index label_eqb andb]; reflexivity.
Qed.

Theorem scoped_compose N M K a b :
  scoped M K a = true -> scoped N M b = true ->
  scoped N K (compose (subst a) a b) = true.
Proof.
  intros Ha Hb.
  pose proof (scoped_maps_ok _ _ _ Ha) as Ha'.
  apply scoped_spec in Ha as [Hain Haout]; apply scoped_spec in Hb as [Hbin Hbout].
  apply scoped_spec; split.
  - intros v Hv; rewrite apply_compose.
    specialize (Hbin v Hv).
    destruct (apply b v) as [w|p]; cbn [result_ok] in Hbin; [apply Hain, Hbin|].
    cbn [result_ok]; rewrite andb_true_iff, negb_true_iff in *.
    destruct Hbin as [H1 H2]; split.
    + apply (wf_subst M K a p Ha' H1).
    + apply not_tvar_subst, H2.
  - intros i Hi; rewrite apply_compose, Hbout by exact Hi.
    rewrite Haout by lia; f_equal; f_equal; lia.
Qed.

(** ** Closed substitutions go under binders for free *)

Lemma wf_var_mono N N' v : N <= N' -> wf_var N v = true -> wf_var N' v = true.
Proof.
  destruct v as [[x|] i]; unfold wf_var; cbn [v_label v_index]; [reflexivity|].
  rewrite !Nat.ltb_lt; lia.
Qed.

Lemma wf_term_mono N N' t : N <= N' -> wf_term N t = true -> wf_term N' t = true.
Proof.
  revert N N'; induction t as [v|n|t1 IH1 t2 IH2|b IH]; intros N N' Hle;
    cbn [wf_term]; [apply wf_var_mono, Hle|reflexivity| |].
  - rewrite !andb_true_iff; intros [H1 H2]; split; eauto.
  - apply IH; lia.
Qed.

Lemma rename_fixes N r p :
  (forall v, wf_var N v = true -> apply r v = inl v) ->
  wf_term N p = true -> rename r p = p.
Proof.
  revert N r; induction p as [v|n|t1 IH1 t2 IH2|b IH]; intros N r Hr Hp;
    cbn [rename wf_term] in *.
  - rewrite (Hr v Hp); reflexivity.
  - reflexivity.
  - apply andb_true_iff in Hp as [H1 H2]; rewrite (IH1 N r), (IH2 N r); auto.
  - f_equal; apply (IH (S N)); [|exact Hp].
    intros v Hv; rewrite apply_lift.
    destruct (var_eqb_spec v (mk_var None 0)) as [->|Hne]; [reflexivity|].
    rewrite (Hr _ (wf_var_unshift_none N v Hne Hv)).
    rewrite shift_unshift_var by exact Hne; reflexivity.
Qed.

Lemma shift_term_closed p : wf_term 0 p = true -> shift_term p = p.
Proof.
  apply rename_fixes; intros [[x|] i] Hv; [|discriminate].
  rewrite apply_shift; reflexivity.
Qed.

Theorem lift_scoped_closed a : scoped 0 0 a = true -> lift shift_term None a = a.
Proof.
  intro Ha; apply scoped_spec in Ha as [Hin Hout].
  apply lift_free.
  - intro i; rewrite Hout by lia; f_equal; f_equal; lia.
  - intros [[x|] i] w Hl Hw; [|contradiction].
    specialize (Hin (mk_var (Some x) i) eq_refl); rewrite Hw in Hin.
    destruct w as [[y|] j]; cbn in *; discriminate.
  - intros [[x|] i] p Hp.
    + specialize (Hin (mk_var (Some x) i) eq_refl); rewrite Hp in Hin.
      cbn [result_ok] in Hin; apply andb_true_iff in Hin as [Hin _].
      apply shift_term_closed, Hin.
    + rewrite Hout in Hp by lia; discriminate.
Qed.

Theorem scoped_closed_weaken N a : scoped 0 0 a = true -> scoped N N a = true.
Proof.
  intro Ha; apply scoped_spec in Ha as [Hin Hout]; apply scoped_spec; split.
  - intros [[x|] i] Hv.
    + specialize (Hin (mk_var (Some x) i) eq_refl).
      destruct (apply a _) as [w|p]; cbn [result_ok] in *.
      * apply (wf_var_mono 0); [lia|exact Hin].
      * rewrite andb_true_iff in *; destruct Hin as [H1 H2]; split; [|exact H2].
        apply (wf_term_mono 0); [lia|exact H1].
    + rewrite Hout by lia; cbn [result_ok]; rewrite Nat.sub_0_r, Nat.add_0_r; exact Hv.
  - intros i Hi; rewrite Hout by lia; f_equal; f_equal; lia.
Qed.

Theorem wf_subst_nolift N a t :
  scoped 0 0 a = true -> wf_term N t = true -> wf_term N (subst_nolift a t) = true.
Proof.
  intros Ha Ht; rewrite subst_nolift_spec by (apply lift_scoped_closed, Ha).
  apply (wf_subst N N); [apply scoped_maps_ok, scoped_closed_weaken, Ha|exact Ht].
Qed.
