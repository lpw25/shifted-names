(** * Scoped adjustments

    An adjustment from [N] to [M] bound variables.  Payload terms are closed,
    so scoping is a property of adjustments alone:

    - bound inputs [None₍ᵢ₎] with [i ≥ N] are outside the scope; they pass
      through to [None₍ᵢ₋N₊M₎] (a fixed tail, so the data stays canonical);
    - every other input is sent to a variable well scoped in [M], or to a
      payload whose adjustment uses fewer than [M] bound outputs
      (recursively).

    [scoped N M a] checks this on the data; [scoped_spec] says it means the
    above.  The public type [sadj N M] packages an adjustment with an SProp
    proof of [scoped N M], so equality is still Leibniz. *)

From Stdlib Require Import PArith Arith List Lia Bool StrictProp.
From ShiftedNames.Core Require Import Trie Label Var Slots Nested Adjustment Laws.
Import ListNotations.

Section Scoped.

Context {T : Type}.

Local Notation payload := (T * nadj T)%type.

(** A variable is in scope [M] if it is free, or bound below [M]. *)
Definition wf_var (M : nat) (v : var) : bool :=
  match v_label v with
  | None => Nat.ltb (v_index v) M
  | Some _ => true
  end.

(** Payload adjustments in scope [M]: fewer than [M] bound outputs, and the
    same for nested payloads. *)
Fixpoint nscoped (M : nat) (x : nadj T) : bool :=
  match x with
  | NAdj m =>
      Nat.leb (count m None) M
      && tall (fun e => List.forallb (fun t => match t with
                                               | Slots.Bind p => nscoped M (snd p)
                                               | Slots.Slot _ _ => true
                                               end) (e_targets e)) m
  end.

Definition rwf (M : nat) (r : var + payload) : bool :=
  match r with
  | inl w => wf_var M w
  | inr p => nscoped M (snd p)
  end.

Definition target_wf (M c : nat) (t : Slots.target payload) : bool :=
  match t with
  | Slots.Slot None l => Nat.ltb (c - S l) M
  | Slots.Slot (Some _) _ => true
  | Slots.Bind p => nscoped M (snd p)
  end.

Definition nscoped_top (N M : nat) (m : raw payload) : bool :=
  Nat.leb (jlen m None) N
  && Nat.eqb (count m None + N) (M + jlen m None)
  && tall (fun e => List.forallb (target_wf M (count m None)) (e_targets e)) m.

Definition scoped_sem (N M : nat) (m : raw payload) : Prop :=
  (forall i, N <= i -> Slots.apply m (mk_var None i) = inl (mk_var None (i - N + M)))
  /\ (forall v, wf_var N v = true -> rwf M (Slots.apply m v) = true).

Lemma apply_unfold (m : raw payload) v :
  Slots.apply m v
  = match nth_error (fst (find m (v_label v))) (v_index v) with
    | Some t => resolve m t
    | None => inl (mk_var (v_label v)
                     (v_index v - length (fst (find m (v_label v))) + count m (v_label v)))
    end.
Proof. reflexivity. Qed.

Theorem nscoped_top_spec N M (m : raw payload) :
  normal m = true -> (nscoped_top N M m = true <-> scoped_sem N M m).
Proof.
  intros Hm; pose proof (normal_keys_ok m Hm) as Hk.
  unfold nscoped_top, jlen; set (ts := fst (find m None)); set (c := count m None).
  split.
  - intros H; apply andb_true_iff in H as [H Ht]; apply andb_true_iff in H as [Hj Hc].
    apply Nat.leb_le in Hj; apply Nat.eqb_eq in Hc.
    pose proof (proj1 (tall_targets _ m Hk) Ht) as Ht'.
    split.
    + intros i Hi; rewrite apply_unfold; cbn [v_label v_index]; fold ts c.
      rewrite (proj2 (nth_error_None ts i)) by lia.
      do 2 f_equal; lia.
    + intros [h i] Hv; rewrite apply_unfold; cbn [v_label v_index] in *.
      destruct (nth_error (fst (find m h)) i) as [t|] eqn:E.
      * specialize (Ht' h i t E).
        destruct t as [[x|] l|p]; cbn in *; [reflexivity|exact Ht'|exact Ht'].
      * destruct h as [x|]; cbn [rwf wf_var v_label v_index]; [reflexivity|].
        fold ts c in E |- *; apply nth_error_None in E.
        apply Nat.ltb_lt in Hv; cbn [v_index] in Hv; apply Nat.ltb_lt; lia.
  - intros [Htail Hrel].
    assert (Hpass : forall i, length ts <= i ->
                    Slots.apply m (mk_var None i) = inl (mk_var None (i - length ts + c))).
    { intros i Hi; rewrite apply_unfold; cbn [v_label v_index]; fold ts c.
      rewrite (proj2 (nth_error_None ts i)) by exact Hi; reflexivity. }
    assert (Hjn : length ts <= N).
    { destruct (Nat.le_gt_cases (length ts) N) as [|Hlt]; [assumption|exfalso].
      set (j := length ts) in *.
      assert (Hcj : c = j - N + M).
      { pose proof (Hpass j (Nat.le_refl _)) as H1; rewrite Htail in H1 by lia.
        injection H1; lia. }
      destruct (nth_error ts (pred j)) as [t|] eqn:El;
        [|apply nth_error_None in El; unfold j in *; lia].
      pose proof (Htail (pred j) ltac:(lia)) as H2; rewrite apply_unfold in H2.
      cbn [v_label v_index] in H2; fold ts in H2; rewrite El in H2.
      destruct t as [h l|p]; cbn [resolve] in H2; [|discriminate].
      injection H2 as -> Hl.
      pose proof (slot_bound m (mk_var None (pred j)) None l Hm) as Hb.
      cbn [v_label v_index] in Hb; fold ts in Hb; specialize (Hb El); fold c in Hb, Hl.
      assert (l = 0) as -> by lia.
      pose proof (proj2 (proj1 (normal_iff m None) Hm)) as Hs; fold ts in Hs.
      rewrite (strip_ok_spec _ _ _ Hk) in Hs.
      destruct (Hs El) as [[hw k] [Hw Hne]]; cbn [v_label v_index] in Hw.
      assert (Ha : Slots.apply m (mk_var hw k) = inl (mk_var None (c - 1))).
      { rewrite apply_unfold; cbn [v_label v_index]; rewrite Hw; reflexivity. }
      destruct (match hw with None => Nat.ltb k N | Some _ => true end) eqn:Hrv.
      + pose proof (Hrel (mk_var hw k) Hrv) as H3; rewrite Ha in H3.
        cbn in H3; apply Nat.ltb_lt in H3; lia.
      + destruct hw as [x|]; [discriminate|]; apply Nat.ltb_ge in Hrv.
        rewrite Htail in Ha by exact Hrv; injection Ha as Hk'.
        apply Hne; f_equal; unfold j in *; lia. }
    assert (Hceq : c + N = M + length ts).
    { pose proof (Hpass N Hjn) as H1; rewrite Htail in H1 by lia.
      injection H1; lia. }
    apply andb_true_iff; split; [apply andb_true_iff; split|].
    + apply Nat.leb_le, Hjn.
    + apply Nat.eqb_eq, Hceq.
    + apply (tall_targets _ m Hk); intros h i t E.
      assert (Hv : wf_var N (mk_var h i) = true).
      { destruct h as [x|]; cbn; [reflexivity|].
        apply Nat.ltb_lt; fold ts in E.
        assert (i < length ts) by (apply nth_error_Some; congruence); lia. }
      pose proof (Hrel _ Hv) as H; rewrite apply_unfold in H; cbn [v_label v_index] in H.
      rewrite E in H.
      destruct t as [[x|] l|p]; cbn in *; [reflexivity|exact H|exact H].
Qed.

Theorem nscoped_spec M x :
  nnormal x = true -> pnormal_raw (nraw x) = true ->
  (nscoped M x = true <-> forall v, v_label v <> None -> rwf M (napply x v) = true).
Proof.
  destruct x as [m]; intros Hn Hp; cbn [nraw] in Hp; unfold napply; cbn [nraw nscoped].
  pose proof (nnormal_normal _ Hn) as Hm; cbn [nraw] in Hm.
  pose proof (normal_keys_ok m Hm) as Hk.
  unfold pnormal_raw in Hp; apply andb_true_iff in Hp as [Hnil Href].
  destruct (fst (find m None)) as [|t0 ts0] eqn:Ef; [|discriminate]; clear Hnil.
  split.
  - intros H; apply andb_true_iff in H as [Hc Ht]; apply Nat.leb_le in Hc.
    rewrite (tall_targets _ m Hk) in Ht.
    intros [h i] Hv; rewrite apply_unfold; cbn [v_label v_index] in *.
    destruct (nth_error (fst (find m h)) i) as [t|] eqn:E.
    + destruct t as [[x|] l|p]; cbn [resolve rwf wf_var v_label v_index].
      * reflexivity.
      * pose proof (slot_bound m (mk_var h i) None l Hm E).
        apply Nat.ltb_lt; lia.
      * apply (Ht h i _ E).
    + destruct h as [x|]; [reflexivity|contradiction].
  - intros H; apply andb_true_iff; split.
    + apply Nat.leb_le.
      destruct (Nat.le_gt_cases (count m None) M) as [|Hlt]; [assumption|exfalso].
      destruct (Nat.eqb_spec (count m None) 0) as [|Hc0]; [lia|].
      cbn [orb] in Href; apply existsb_exists in Href as [[[w h] [|n]] [Hin Hr]];
        [|discriminate].
      apply label_eqb_eq in Hr; subst h.
      apply In_refs in Hin; [|exact Hm].
      destruct w as [[x|] k]; cbn [v_label v_index] in Hin;
        [|rewrite Ef, nth_error_nil in Hin; discriminate].
      specialize (H (mk_var (Some x) k) ltac:(discriminate)).
      rewrite apply_unfold in H; cbn [v_label v_index] in H; rewrite Hin in H.
      cbn in H; apply Nat.ltb_lt in H; lia.
    + apply (tall_targets _ m Hk); intros h i t E.
      destruct t as [h' l|p]; [reflexivity|].
      destruct h as [x|]; [|rewrite Ef, nth_error_nil in E; discriminate].
      specialize (H (mk_var (Some x) i) ltac:(discriminate)).
      rewrite apply_unfold in H; cbn [v_label v_index] in H; rewrite E in H; exact H.
Qed.

(** ** In terms of the user-facing API *)

Definition result_wf (M : nat) (r : result T) : bool := rwf M (lower r).

Definition pscoped (M : nat) (ρ : padj T) : bool := nscoped M (padj_n ρ).

Definition scoped (N M : nat) (a : adjustment T) : bool := nscoped_top N M (nraw (adj_n a)).

Lemma result_wf_apply M (a : adjustment T) v : result_wf M (apply a v) = rwf M (napply (adj_n a) v).
Proof. unfold result_wf; rewrite lower_apply; reflexivity. Qed.

Lemma apply_inl (a : adjustment T) v w : apply a v = inl w <-> napply (adj_n a) v = inl w.
Proof.
  rewrite <- lower_apply; split; [intros ->; reflexivity|].
  intros H; apply lower_inj; exact H.
Qed.

Theorem pscoped_spec M ρ :
  pscoped M ρ = true <-> (forall v, v_label v <> None -> result_wf M (papply ρ v) = true).
Proof.
  unfold pscoped, papply; rewrite nscoped_spec by (apply padj_nnormal || apply padj_pnormal).
  split; intros H v Hv; specialize (H v Hv); rewrite ?result_wf_apply in *; exact H.
Qed.

Theorem scoped_spec N M a :
  scoped N M a = true
  <-> (forall i, N <= i -> apply a (mk_var None i) = inl (mk_var None (i - N + M)))
      /\ (forall v, wf_var N v = true -> result_wf M (apply a v) = true).
Proof.
  unfold scoped; rewrite nscoped_top_spec by apply (nnormal_normal _ (adj_ok_true a)).
  unfold scoped_sem; split; intros [H1 H2]; split.
  - intros i Hi; apply apply_inl, H1, Hi.
  - intros v Hv; rewrite result_wf_apply; apply H2, Hv.
  - intros i Hi; apply apply_inl, H1, Hi.
  - intros v Hv; change (rwf M (napply (adj_n a) v) = true); rewrite <- result_wf_apply; apply H2, Hv.
Qed.

Lemma result_wf_inl M w : result_wf M (inl w : result T) = wf_var M w.
Proof. reflexivity. Qed.

Lemma result_wf_inr M (u : T) ρ : result_wf M (inr (u, ρ)) = pscoped M ρ.
Proof. reflexivity. Qed.

(** ** Scoping is preserved by the constructors *)

Implicit Types (a b : adjustment T) (ρ : padj T).

Lemma wf_var_none M i : wf_var M (mk_var None i) = Nat.ltb i M.
Proof. reflexivity. Qed.

Lemma wf_var_some M x i : wf_var M (mk_var (Some x) i) = true.
Proof. reflexivity. Qed.

Theorem scoped_identity N : scoped N N (@identity T) = true.
Proof.
  apply scoped_spec; split.
  - intros i Hi; rewrite apply_identity; do 2 f_equal; lia.
  - intros v Hv; rewrite apply_identity; exact Hv.
Qed.

Lemma pscoped_pcompose_depth M K a n :
  scoped M K a = true ->
  forall ρ, ndepth (padj_n ρ) <= n -> pscoped M ρ = true -> pscoped K (pcompose a ρ) = true.
Proof.
  intros Ha; apply scoped_spec in Ha as [_ Ha].
  induction n as [|n IH]; intros ρ Hd Hρ; [pose proof (ndepth_pos (padj_n ρ)); lia|].
  apply pscoped_spec; intros v Hv; rewrite papply_pcompose by exact Hv.
  pose proof (proj1 (pscoped_spec M ρ) Hρ v Hv) as Hr.
  destruct (papply ρ v) as [w|[u ρ']] eqn:E.
  - apply Ha, Hr.
  - cbn [fst snd]; rewrite result_wf_inr; rewrite result_wf_inr in Hr.
    pose proof (papply_depth _ _ _ _ E); apply IH; [lia|exact Hr].
Qed.

Theorem pscoped_pcompose M K a ρ :
  scoped M K a = true -> pscoped M ρ = true -> pscoped K (pcompose a ρ) = true.
Proof. intros Ha; apply (pscoped_pcompose_depth M K a (ndepth (padj_n ρ)) Ha); lia. Qed.

Theorem scoped_compose N M K a b :
  scoped M K a = true -> scoped N M b = true -> scoped N K (compose a b) = true.
Proof.
  intros Ha Hb; pose proof Ha as Ha'.
  apply scoped_spec in Ha as [Hat Har]; apply scoped_spec in Hb as [Hbt Hbr].
  apply scoped_spec; split.
  - intros i Hi; rewrite apply_compose, Hbt by exact Hi.
    rewrite Hat by lia; do 2 f_equal; lia.
  - intros v Hv; rewrite apply_compose; specialize (Hbr v Hv).
    destruct (apply b v) as [w|[u ρ]].
    + apply Har, Hbr.
    + cbn [fst snd]; rewrite result_wf_inr in *; apply (pscoped_pcompose M); assumption.
Qed.

Theorem scoped_shift_none M : scoped M (S M) (@shift T None) = true.
Proof.
  apply scoped_spec; split.
  - intros i Hi; rewrite apply_shift; unfold shift_var; cbn.
    do 2 f_equal; lia.
  - intros [[x|] i] Hv; rewrite apply_shift; unfold shift_var; cbn in *; [reflexivity|].
    apply Nat.ltb_lt in Hv; apply Nat.ltb_lt; lia.
Qed.

Theorem scoped_shift_some x M : scoped M M (@shift T (Some x)) = true.
Proof.
  apply scoped_spec; split.
  - intros i Hi; rewrite apply_shift; unfold shift_var; cbn.
    do 2 f_equal; lia.
  - intros [[y|] i] Hv; rewrite apply_shift; unfold shift_var; cbn in *;
      [destruct (_ && _); reflexivity|exact Hv].
Qed.

Theorem scoped_push_outer_none N M a :
  scoped N M a = true -> scoped N (S M) (push_outer None a) = true.
Proof.
  intros Ha; rewrite push_outer_as_compose.
  apply (scoped_compose _ M); [apply scoped_shift_none|exact Ha].
Qed.

Theorem scoped_push_outer_some x N M a :
  scoped N M a = true -> scoped N M (push_outer (Some x) a) = true.
Proof.
  intros Ha; rewrite push_outer_as_compose.
  apply (scoped_compose _ M); [apply scoped_shift_some|exact Ha].
Qed.

Theorem scoped_push_inner_none N M t a :
  scoped N M a = true -> result_wf M (target_result t) = true ->
  scoped (S N) M (push_inner None t a) = true.
Proof.
  intros Ha Ht; apply scoped_spec in Ha as [Hat Har]; apply scoped_spec; split.
  - intros i Hi; rewrite apply_push_inner.
    destruct i as [|i]; [lia|]; cbn.
    unfold unshift_var; cbn; replace (i - 0) with i by lia.
    rewrite Hat by lia; do 2 f_equal; lia.
  - intros [[x|] i] Hv; rewrite apply_push_inner; cbn [var_eqb v_label v_index].
    + unfold var_eqb; cbn; apply Har; reflexivity.
    + destruct i as [|i]; unfold var_eqb; cbn; [exact Ht|].
      unfold unshift_var; cbn; replace (i - 0) with i by lia.
      apply Har; cbn in *; apply Nat.ltb_lt in Hv; apply Nat.ltb_lt; lia.
Qed.

Theorem scoped_push_inner_some x N M t a :
  scoped N M a = true -> result_wf M (target_result t) = true ->
  scoped N M (push_inner (Some x) t a) = true.
Proof.
  intros Ha Ht; apply scoped_spec in Ha as [Hat Har]; apply scoped_spec; split.
  - intros i Hi; rewrite apply_push_inner; unfold var_eqb, unshift_var; cbn.
    apply Hat, Hi.
  - intros [h i] Hv; rewrite apply_push_inner.
    destruct (var_eqb_spec (mk_var h i) (mk_var (Some x) 0)) as [E|E]; [exact Ht|].
    apply Har; destruct h as [y|]; unfold unshift_var; cbn in *.
    + destruct (_ && _); reflexivity.
    + exact Hv.
Qed.

Theorem scoped_lift_none N M a :
  scoped N M a = true -> scoped (S N) (S M) (lift None a) = true.
Proof.
  intros Ha; unfold lift; apply scoped_push_inner_none;
    [apply scoped_push_outer_none, Ha|reflexivity].
Qed.

Theorem scoped_lift_some x N M a :
  scoped N M a = true -> scoped N M (lift (Some x) a) = true.
Proof.
  intros Ha; unfold lift; apply scoped_push_inner_some;
    [apply scoped_push_outer_some, Ha|reflexivity].
Qed.

(** Scoped adjustments are determined by what they do in scope. *)
Theorem scoped_ext N M a b :
  scoped N M a = true -> scoped N M b = true ->
  (forall v, wf_var N v = true -> apply a v = apply b v) -> a = b.
Proof.
  intros Ha Hb H; apply scoped_spec in Ha as [Hat _]; apply scoped_spec in Hb as [Hbt _].
  apply extensionality; intros [[x|] i]; [apply H; reflexivity|].
  destruct (Nat.lt_ge_cases i N) as [Hi|Hi].
  - apply H; apply Nat.ltb_lt, Hi.
  - rewrite Hat, Hbt by exact Hi; reflexivity.
Qed.

(** ** Closed adjustments work at every scope, and lifting them is free *)

Lemma wf_var_mono M M' v : M <= M' -> wf_var M v = true -> wf_var M' v = true.
Proof.
  destruct v as [[x|] i]; cbn; [reflexivity|].
  intros H1 H2; apply Nat.ltb_lt in H2; apply Nat.ltb_lt; lia.
Qed.

Lemma pscoped_mono_depth M M' n :
  M <= M' -> forall ρ, ndepth (padj_n ρ) <= n -> pscoped M ρ = true -> pscoped M' ρ = true.
Proof.
  intros Hle; induction n as [|n IH]; intros ρ Hd H; [pose proof (ndepth_pos (padj_n ρ)); lia|].
  apply pscoped_spec; intros v Hv; pose proof (proj1 (pscoped_spec M ρ) H v Hv) as Hr.
  destruct (papply ρ v) as [w|[u ρ']] eqn:E.
  - rewrite result_wf_inl in *; apply (wf_var_mono M); assumption.
  - rewrite result_wf_inr in *; pose proof (papply_depth _ _ _ _ E); apply IH; [lia|exact Hr].
Qed.

Lemma pscoped_mono M M' ρ : M <= M' -> pscoped M ρ = true -> pscoped M' ρ = true.
Proof. intros Hle; apply (pscoped_mono_depth M M' (ndepth (padj_n ρ)) Hle); lia. Qed.

Lemma result_wf_mono M M' r : M <= M' -> result_wf M r = true -> result_wf M' r = true.
Proof.
  destruct r as [w|[u ρ]]; intros Hle; [apply wf_var_mono, Hle|apply pscoped_mono, Hle].
Qed.

Theorem scoped_closed N a : scoped 0 0 a = true -> scoped N N a = true.
Proof.
  intros H; apply scoped_spec in H as [Ht Hr]; apply scoped_spec; split.
  - intros i Hi; rewrite Ht by lia; do 2 f_equal; lia.
  - intros [[x|] i] Hv.
    + apply (result_wf_mono 0); [lia|apply Hr; reflexivity].
    + rewrite Ht by lia; cbn in *; replace (i - 0 + 0) with i by lia; exact Hv.
Qed.

Lemma pshift_closed_depth n :
  forall ρ, ndepth (padj_n ρ) <= n -> pscoped 0 ρ = true -> pshift_p None ρ = ρ.
Proof.
  induction n as [|n IH]; intros ρ Hd H; [pose proof (ndepth_pos (padj_n ρ)); lia|].
  apply pextensionality; intros v Hv; rewrite papply_pshift by exact Hv.
  pose proof (proj1 (pscoped_spec 0 ρ) H v Hv) as Hr.
  destruct (papply ρ v) as [[[x|] i]|[u ρ']] eqn:E.
  - reflexivity.
  - cbn in Hr; discriminate.
  - rewrite result_wf_inr in Hr; pose proof (papply_depth _ _ _ _ E).
    cbn [fst snd]; rewrite IH by (lia || exact Hr); reflexivity.
Qed.

Theorem pshift_closed ρ : pscoped 0 ρ = true -> pshift_p None ρ = ρ.
Proof. apply (pshift_closed_depth (ndepth (padj_n ρ))); lia. Qed.

Theorem lift_closed a : scoped 0 0 a = true -> lift None a = a.
Proof.
  intros H; apply scoped_spec in H as [Ht Hr]; apply lift_free.
  - intros i; rewrite Ht by lia; do 2 f_equal; lia.
  - intros [[x|] i] w Hv E; [|contradiction].
    pose proof (Hr (mk_var (Some x) i) eq_refl) as Hw; rewrite E in Hw.
    destruct w as [[y|] j]; cbn in Hw; [discriminate|discriminate].
  - intros [[x|] i] [u ρ] E.
    + pose proof (Hr (mk_var (Some x) i) eq_refl) as Hw; rewrite E in Hw.
      apply pshift_closed, Hw.
    + rewrite Ht in E by lia; discriminate.
Qed.

End Scoped.
