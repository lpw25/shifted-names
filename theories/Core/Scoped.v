(** * Scoped adjustments

    An adjustment from [N] to [M] bound variables.  Payload terms are closed,
    so scoping is a property of adjustments alone:

    - bound inputs [None₍ᵢ₎] with [i ≥ N] are outside the scope; they pass
      through to [None₍ᵢ₋N₊M₎] (a fixed tail, so the data stays canonical);
    - every other input is sent to a variable well scoped in [M], or to a
      payload whose adjustment sends its free variables into scope [M]
      (recursively).

    [scoped N M a] checks this on the data: the bound label's entry, and
    every target made absolute.  [scoped_spec] says it means the above.  The
    public type [sadj N M] packages an adjustment with an SProp proof of
    [scoped N M], so equality is still Leibniz. *)

From Stdlib Require Import PArith Arith List Lia Bool StrictProp.
From ShiftedNames.Core Require Import Trie Label Var Counts Based Skew ATrie Repr Point Deep Compose
  Adjustment Laws.
Import ListNotations.

Section Scoped.

Context {T : Type}.

Local Notation nadj := (@nadj T).
Local Notation entry := (@entry T).
Local Notation target := (@target T).

(** A variable is in scope [M] if it is free, or bound below [M]. *)
Definition wf_var (M : nat) (v : rvar) : bool :=
  match v_label v with
  | None => Nat.ltb (v_index v) M
  | Some _ => true
  end.

(** Every target, made absolute (by the base [B] it is stored under), is in
    scope [M]; payloads recursively. *)
Fixpoint pscopedc (M : nat) (rt : counts -> counts) (x : nadj) {struct x} : bool :=
  match x with
  | NAdj r es =>
      aallF (fun B e =>
               match e with
               | Entry _ ts _ _ =>
                   kallF (fun B' t => match t with
                                      | TVar None j => Nat.ltb (dval B' (label_key None) + j) M
                                      | TVar (Some _) _ => true
                                      | TBind _ rho => pscopedc M (cadd B') rho
                                      end) B ts
               end) (rt r) es
  end.

Definition tscope (M : nat) (B : counts) (t : target) : bool :=
  match t with
  | TVar None j => Nat.ltb (dval B (label_key None) + j) M
  | TVar (Some _) _ => true
  | TBind _ rho => pscopedc M (cadd B) rho
  end.

Lemma pscopedc_eq M rt r (es : atrie entry) :
  pscopedc M rt (NAdj r es) = aallF (fun B e => match e with Entry _ ts _ _ => kallF (tscope M) B ts end) (rt r) es.
Proof. reflexivity. Qed.

Lemma tscope_unshift M B t : tscope M B t = tscope M cnone (unshift B t).
Proof.
  destruct t as [[y|] j|u [r es]]; try reflexivity; cbn [tscope unshift target_based tunshift].
  rewrite !pscopedc_eq, (cadd_cnone (cadd B r)); reflexivity.
Qed.

Definition rwf (M : nat) (r : rresult T) : bool :=
  match r with inl w => wf_var M w | inr (_, ρ) => pscopedc M (fun r => r) (rpadj_n ρ) end.

Definition result_wf := rwf.

Definition pscoped (M : nat) (ρ : rpadj T) : bool := pscopedc M (fun r => r) (rpadj_n ρ).

(** The bound label of a top-level adjustment: its entry [(len, p)] keeps
    within [N] inputs, and its tail lands on [None₍ᵢ₋N₊M₎]. *)
Definition scoped_tail (N M : nat) (x : nadj) : bool :=
  match x with
  | NAdj r es =>
      let kN := label_key None in
      let '(len, p) := match aget kN es with Some (Entry _ _ len p) => (len, p) | None => (0, 0) end in
      Nat.leb len N && Nat.eqb (dval r kN + p + N) (M + len)
  end.

Definition scoped (N M : nat) (a : radj T) : bool :=
  scoped_tail N M (radj_n a) && pscopedc M (fun r => r) (radj_n a).

Lemma result_wf_inl M w : result_wf M (inl w : rresult T) = wf_var M w.
Proof. reflexivity. Qed.

Lemma result_wf_inr M (u : T) ρ : result_wf M (inr (u, ρ)) = pscoped M ρ.
Proof. reflexivity. Qed.

(** What a target check says about the result it gives. *)
Lemma tscope_result M t :
  (forall u rho, t = TBind u rho -> nwf true rho) -> tscope M cnone t = rwf M (rpack (tresult t)).
Proof.
  destruct t as [[y|] j|u [r es]]; intros Hw; try reflexivity.
  cbn [tscope tresult rpack rwf]; rewrite rpadj_n_to_padj by apply (Hw u _ eq_refl).
  rewrite !pscopedc_eq, cadd_cnone; reflexivity.
Qed.

(** The absolute targets of an entry, and their results. *)
Lemma entry_target_result Q r (es : atrie entry) k h ts len p t :
  nlocal Q (NAdj r es) -> aget k es = Some (Entry h ts len p) -> In t (klist (klift r ts)) ->
  exists i, i < len /\ napply (NAdj r es) (mk_rvar h i) = tresult t /\ Q h = true.
Proof.
  intros Hl E Ht; pose proof Hl as [_ [_ [Hent _]]].
  destruct (Hent _ _ E) as [[_ [G [Hlen _]]] _].
  rewrite klist_klift in Ht by apply kgood_inv, G; apply in_map_iff in Ht as [t0 [<- Ht0]].
  destruct (In_nth_error _ _ Ht0) as [i Ei].
  assert (Et : knth ts i = Some t0) by (rewrite knth_spec by apply kgood_shape, G; exact Ei).
  destruct (target_result _ r es k h ts len p i t0 Hl E Et) as [Hn HQ].
  exists i; split; [|split; [exact Hn|exact HQ]].
  rewrite <- Hlen, (klength_spec _ (kgood_shape _ G)); apply nth_error_Some; rewrite Ei; discriminate.
Qed.

(** Where an adjustment sends a variable, by cases on its entry. *)
Lemma napply_cases Q r (es : atrie entry) v :
  nlocal Q (NAdj r es) ->
  (aget (label_key (v_label v)) es = None /\ napply (NAdj r es) v = inl (mk_rvar (v_label v) (dval r (label_key (v_label v)) + v_index v)))
  \/ exists ts len p, aget (label_key (v_label v)) es = Some (Entry (v_label v) ts len p)
       /\ ((v_index v < len /\ exists t, In t (klist (klift r ts)) /\ napply (NAdj r es) v = tresult t)
           \/ (len <= v_index v
               /\ napply (NAdj r es) v = inl (mk_rvar (v_label v) (dval r (label_key (v_label v)) + (v_index v - len + p))))).
Proof.
  intros Hl; pose proof Hl as [_ [_ [Hent _]]]; cbn [napply].
  destruct (aget _ es) as [e|] eqn:E; [right|left; split; reflexivity].
  destruct (Hent _ _ E) as [Hok _]; destruct e as [h ts len p]; destruct Hok as [Hk [G [Hlen _]]].
  apply label_key_inj in Hk; subst h; exists ts, len, p; split; [reflexivity|]; cbn [eapply].
  destruct (Nat.ltb_spec (v_index v) len) as [Hi|Hi]; [left|right; split; [exact Hi|reflexivity]].
  split; [exact Hi|]; destruct (knth_some ts (v_index v) G ltac:(lia)) as [t0 Et]; rewrite Et.
  exists (tunshift r t0); split; [|reflexivity].
  rewrite klist_klift by apply kgood_inv, G; apply in_map, (knth_in _ _ _ G Et).
Qed.

Theorem pscoped_spec M ρ :
  pscoped M ρ = true <-> (forall v, v_label v <> None -> result_wf M (rpapply ρ v) = true).
Proof.
  unfold pscoped, rpapply; pose proof (rpadj_local ρ) as Hl; pose proof (rpadj_wf ρ) as Hw.
  destruct (rpadj_n ρ) as [r es]; rewrite pscopedc_eq; cbv beta.
  rewrite (targets_check (tscope M) (tscope_unshift M) Qnamed r es Hl).
  assert (Hpay : forall v t u rho, v_label v <> None -> napply (NAdj r es) v = tresult t -> t = TBind u rho -> nwf true rho).
  { intros v t u rho Hv E ->; apply (nwf_payload true _ v u rho Hw); [destruct (v_label v); [reflexivity|contradiction]|exact E]. }
  split.
  - intros H v Hv.
    destruct (napply_cases Qnamed r es v Hl) as [[_ En]|[ts [len [p [E [[_ [t [Ht En]]]|[_ En]]]]]]];
      rewrite En.
    + cbn; destruct (v_label v); [reflexivity|contradiction].
    + rewrite <- tscope_result; [apply (H _ _ E t Ht)|].
      intros u rho Et; apply (Hpay v t u rho Hv En Et).
    + cbn; destruct (v_label v); [reflexivity|contradiction].
  - intros H k [h ts len p] E t Ht.
    destruct (entry_target_result Qnamed r es k h ts len p t Hl E Ht) as [i [_ [En HQ]]].
    assert (Hh : v_label (mk_rvar h i) <> None) by (cbn; destruct h; [discriminate|discriminate]).
    pose proof (H _ Hh) as Hr; rewrite En in Hr.
    rewrite tscope_result; [exact Hr|intros u rho Et; apply (Hpay _ t u rho Hh En Et)].
Qed.

Theorem scoped_spec N M a :
  scoped N M a = true
  <-> (forall i, N <= i -> rapply a (mk_rvar None i) = inl (mk_rvar None (i - N + M)))
      /\ (forall v, wf_var N v = true -> result_wf M (rapply a v) = true).
Proof.
  unfold scoped, rapply; pose proof (radj_local a) as Hl; pose proof (radj_wf a) as Hw.
  destruct (radj_n a) as [r es]; rewrite pscopedc_eq; cbv beta.
  rewrite andb_true_iff, (targets_check (tscope M) (tscope_unshift M) Qall r es Hl).
  set (kN := label_key None).
  assert (Hpay : forall v t u rho, napply (NAdj r es) v = tresult t -> t = TBind u rho -> nwf true rho)
    by (intros v t u rho E ->; apply (nwf_payload false _ v u rho Hw eq_refl E)).
  (* the bound label's entry, as a pair *)
  assert (Hcase : forall i, napply (NAdj r es) (mk_rvar None i)
                  = match aget kN es with
                    | Some e => eapply r e i
                    | None => inl (mk_rvar None (dval r kN + i))
                    end) by (intros i; reflexivity).
  cbn [scoped_tail]; fold kN.
  split.
  - intros [Ht Hc].
    destruct (aget kN es) as [[h ts len p]|] eqn:EN.
    + apply andb_true_iff in Ht as [HlN Heq]; apply Nat.leb_le in HlN; apply Nat.eqb_eq in Heq.
      pose proof Hl as [_ [_ [Hent _]]]; destruct (Hent _ _ EN) as [[Hk _] _].
      apply label_key_inj in Hk; subst h.
      split.
      * intros i Hi; rewrite Hcase; cbn [eapply].
        destruct (Nat.ltb_spec i len); [lia|]; cbn [rpack]; f_equal; f_equal; fold kN; lia.
      * intros v Hv; destruct (napply_cases Qall r es v Hl) as [[E En]|[ts' [len' [p' [E [[_ [t [Htt En]]]|[Hi En]]]]]]];
          rewrite En.
        -- destruct v as [[x|] i]; [reflexivity|]; cbn [v_label] in E; fold kN in E.
           rewrite EN in E; discriminate.
        -- rewrite <- tscope_result; [apply (Hc _ _ E t Htt)|intros u rho Et; apply (Hpay v t u rho En Et)].
        -- destruct v as [[x|] i]; [reflexivity|]; cbn [v_label v_index] in *.
           fold kN in E; rewrite EN in E; injection E as <- <- <-.
           cbn [rpack rwf wf_var v_label v_index] in *; apply Nat.ltb_lt in Hv; apply Nat.ltb_lt; fold kN; cbn [v_index]; lia.
    + apply andb_true_iff in Ht as [_ Heq]; apply Nat.eqb_eq in Heq.
      split.
      * intros i Hi; rewrite Hcase; cbn [rpack]; f_equal; f_equal; lia.
      * intros v Hv; destruct (napply_cases Qall r es v Hl) as [[_ En]|[ts' [len' [p' [E [[_ [t [Htt En]]]|[Hi En]]]]]]];
          rewrite En.
        -- destruct v as [[x|] i]; [reflexivity|]; cbn [rpack rwf wf_var v_label v_index] in *; apply Nat.ltb_lt in Hv; apply Nat.ltb_lt; fold kN; cbn [v_index]; lia.
        -- rewrite <- tscope_result; [apply (Hc _ _ E t Htt)|intros u rho Et; apply (Hpay v t u rho En Et)].
        -- destruct v as [[x|] i]; [reflexivity|]; cbn [v_label] in E; fold kN in E; rewrite EN in E; discriminate.
  - intros [Ht Hc].
    assert (Hlen : match aget kN es with Some (Entry _ _ len _) => len | None => 0 end <= N).
    { destruct (aget kN es) as [[h ts len p]|] eqn:EN; [|lia].
      pose proof Hl as [_ [_ [Hent _]]]; destruct (Hent _ _ EN) as [[Hk [G [Hlen [_ Hs]]]] _].
      apply label_key_inj in Hk; subst h.
      destruct (Nat.le_gt_cases len N) as [|Hgt]; [assumption|exfalso].
      pose proof (Ht len ltac:(lia)) as Hp; rewrite Hcase in Hp; cbn [eapply] in Hp.
      destruct (Nat.ltb_spec len len); [lia|]; cbn [rpack] in Hp; injection Hp as Hp.
      pose proof (Ht (pred len) ltac:(lia)) as Hlast; rewrite Hcase in Hlast; cbn [eapply] in Hlast.
      destruct (Nat.ltb_spec (pred len) len); [|lia].
      destruct (knth ts (pred len)) as [t|] eqn:Et;
        [|exfalso; destruct (knth_some ts (pred len) G ltac:(lia)) as [t' Et']; congruence].
      destruct t as [y j|u [r0 es0]]; cbn [tunshift tresult rpack] in Hlast; [|discriminate].
      injection Hlast as -> Hj; change xH with kN in Hp; fold kN in Hj.
      apply Hs; split; [lia|split; [lia|rewrite Et; f_equal; f_equal; lia]]. }
    split.
    + destruct (aget kN es) as [[h ts len p]|] eqn:EN.
      * pose proof Hl as [_ [_ [Hent _]]]; destruct (Hent _ _ EN) as [[Hk _] _].
        apply label_key_inj in Hk; subst h.
        pose proof (Ht N ltac:(lia)) as HN; rewrite Hcase in HN; cbn [eapply] in HN.
        destruct (Nat.ltb_spec N len); [lia|]; cbn [rpack] in HN; injection HN as HN; change xH with kN in *.
        apply andb_true_iff; split; [apply Nat.leb_le; exact Hlen|apply Nat.eqb_eq; lia].
      * pose proof (Ht N ltac:(lia)) as HN; rewrite Hcase in HN; cbn [rpack] in HN; injection HN as HN; change xH with kN in *.
        apply andb_true_iff; split; [reflexivity|apply Nat.eqb_eq; lia].
    + intros k [h ts len p] E t Htt.
      destruct (entry_target_result Qall r es k h ts len p t Hl E Htt) as [i [Hi [En _]]].
      assert (Hv : wf_var N (mk_rvar h i) = true).
      { destruct h as [x|]; [reflexivity|]; cbn; apply Nat.ltb_lt.
        pose proof Hl as [_ [_ [Hent _]]]; destruct (Hent _ _ E) as [[Hk _] _]; subst k.
        fold kN in E; rewrite E in Hlen; lia. }
      pose proof (Hc _ Hv) as Hr; rewrite En in Hr.
      rewrite tscope_result; [exact Hr|intros u rho Et; apply (Hpay _ t u rho En Et)].
Qed.

(** ** Scoping is preserved by the constructors *)

Implicit Types (a b : radj T) (ρ : rpadj T).

Lemma wf_var_none M i : wf_var M (mk_rvar None i) = Nat.ltb i M.
Proof. reflexivity. Qed.

Lemma wf_var_some M x i : wf_var M (mk_rvar (Some x) i) = true.
Proof. reflexivity. Qed.

Theorem scoped_identity N : scoped N N (@ridentity T) = true.
Proof.
  apply scoped_spec; split.
  - intros i Hi; rewrite rapply_identity; do 2 f_equal; lia.
  - intros v Hv; rewrite rapply_identity; exact Hv.
Qed.

Lemma pscoped_pcompose_depth M K a n :
  scoped M K a = true ->
  forall ρ, rpdepth ρ < n -> pscoped M ρ = true -> pscoped K (rpcompose a ρ) = true.
Proof.
  intros Ha; apply scoped_spec in Ha as [_ Ha].
  induction n as [|n IH]; intros ρ Hd Hρ; [lia|].
  apply pscoped_spec; intros v Hv; rewrite rpapply_pcompose by exact Hv.
  pose proof (proj1 (pscoped_spec M ρ) Hρ v Hv) as Hr.
  destruct (rpapply ρ v) as [w|[u ρ']] eqn:E.
  - apply Ha, Hr.
  - cbn [fst snd]; rewrite result_wf_inr; rewrite result_wf_inr in Hr.
    pose proof (rpdepth_payload _ _ _ _ Hv E); apply IH; [lia|exact Hr].
Qed.

Theorem pscoped_pcompose M K a ρ :
  scoped M K a = true -> pscoped M ρ = true -> pscoped K (rpcompose a ρ) = true.
Proof. intros Ha; apply (pscoped_pcompose_depth M K a (S (rpdepth ρ)) Ha); lia. Qed.

Theorem scoped_compose N M K a b :
  scoped M K a = true -> scoped N M b = true -> scoped N K (rcompose a b) = true.
Proof.
  intros Ha Hb; pose proof Ha as Ha'.
  apply scoped_spec in Ha as [Hat Har]; apply scoped_spec in Hb as [Hbt Hbr].
  apply scoped_spec; split.
  - intros i Hi; rewrite rapply_compose, Hbt by exact Hi.
    rewrite Hat by lia; do 2 f_equal; lia.
  - intros v Hv; rewrite rapply_compose; specialize (Hbr v Hv).
    destruct (rapply b v) as [w|[u ρ]].
    + apply Har, Hbr.
    + cbn [fst snd]; rewrite result_wf_inr in *; apply (pscoped_pcompose M); assumption.
Qed.

Theorem scoped_shift_none M : scoped M (S M) (@rshift T None) = true.
Proof.
  apply scoped_spec; split.
  - intros i Hi; rewrite rapply_shift; unfold shift_rvar; cbn.
    do 2 f_equal; lia.
  - intros [[x|] i] Hv; rewrite rapply_shift; unfold shift_rvar; cbn in *; [reflexivity|].
    apply Nat.ltb_lt in Hv; apply Nat.ltb_lt; lia.
Qed.

Theorem scoped_shift_some x M : scoped M M (@rshift T (Some x)) = true.
Proof.
  apply scoped_spec; split.
  - intros i Hi; rewrite rapply_shift; unfold shift_rvar; cbn.
    do 2 f_equal; lia.
  - intros [[y|] i] Hv; rewrite rapply_shift; unfold shift_rvar; cbn in *;
      [destruct (_ && _); reflexivity|exact Hv].
Qed.

Theorem scoped_push_outer_none N M a :
  scoped N M a = true -> scoped N (S M) (rpush_outer None a) = true.
Proof.
  intros Ha; rewrite rpush_outer_as_compose.
  apply (scoped_compose _ M); [apply scoped_shift_none|exact Ha].
Qed.

Theorem scoped_push_outer_some x N M a :
  scoped N M a = true -> scoped N M (rpush_outer (Some x) a) = true.
Proof.
  intros Ha; rewrite rpush_outer_as_compose.
  apply (scoped_compose _ M); [apply scoped_shift_some|exact Ha].
Qed.

Theorem scoped_push_inner_none N M t a :
  scoped N M a = true -> result_wf M (rtarget_result t) = true ->
  scoped (S N) M (rpush_inner None t a) = true.
Proof.
  intros Ha Ht; apply scoped_spec in Ha as [Hat Har]; apply scoped_spec; split.
  - intros i Hi; rewrite rapply_push_inner.
    destruct i as [|i]; [lia|]; cbn.
    unfold unshift_rvar; cbn; replace (i - 0) with i by lia.
    rewrite Hat by lia; do 2 f_equal; lia.
  - intros [[x|] i] Hv; rewrite rapply_push_inner; cbn [rvar_eqb v_label v_index].
    + unfold rvar_eqb; cbn; apply Har; reflexivity.
    + destruct i as [|i]; unfold rvar_eqb; cbn; [exact Ht|].
      unfold unshift_rvar; cbn; replace (i - 0) with i by lia.
      apply Har; cbn in *; apply Nat.ltb_lt in Hv; apply Nat.ltb_lt; lia.
Qed.

Theorem scoped_push_inner_some x N M t a :
  scoped N M a = true -> result_wf M (rtarget_result t) = true ->
  scoped N M (rpush_inner (Some x) t a) = true.
Proof.
  intros Ha Ht; apply scoped_spec in Ha as [Hat Har]; apply scoped_spec; split.
  - intros i Hi; rewrite rapply_push_inner; unfold rvar_eqb, unshift_rvar; cbn.
    apply Hat, Hi.
  - intros [h i] Hv; rewrite rapply_push_inner.
    destruct (rvar_eqb_spec (mk_rvar h i) (mk_rvar (Some x) 0)) as [E|E]; [exact Ht|].
    apply Har; destruct h as [y|]; unfold unshift_rvar; cbn in *.
    + destruct (_ && _); reflexivity.
    + exact Hv.
Qed.

Theorem scoped_lift_none N M a :
  scoped N M a = true -> scoped (S N) (S M) (rlift None a) = true.
Proof.
  intros Ha; unfold rlift; apply scoped_push_inner_none;
    [apply scoped_push_outer_none, Ha|reflexivity].
Qed.

Theorem scoped_lift_some x N M a :
  scoped N M a = true -> scoped N M (rlift (Some x) a) = true.
Proof.
  intros Ha; unfold rlift; apply scoped_push_inner_some;
    [apply scoped_push_outer_some, Ha|reflexivity].
Qed.

(** Scoped adjustments are determined by what they do in scope. *)
Theorem scoped_ext N M a b :
  scoped N M a = true -> scoped N M b = true ->
  (forall v, wf_var N v = true -> rapply a v = rapply b v) -> a = b.
Proof.
  intros Ha Hb H; apply scoped_spec in Ha as [Hat _]; apply scoped_spec in Hb as [Hbt _].
  apply rextensionality; intros [[x|] i]; [apply H; reflexivity|].
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
  M <= M' -> forall ρ, rpdepth ρ < n -> pscoped M ρ = true -> pscoped M' ρ = true.
Proof.
  intros Hle; induction n as [|n IH]; intros ρ Hd H; [lia|].
  apply pscoped_spec; intros v Hv; pose proof (proj1 (pscoped_spec M ρ) H v Hv) as Hr.
  destruct (rpapply ρ v) as [w|[u ρ']] eqn:E.
  - rewrite result_wf_inl in *; apply (wf_var_mono M); assumption.
  - rewrite result_wf_inr in *; pose proof (rpdepth_payload _ _ _ _ Hv E); apply IH; [lia|exact Hr].
Qed.

Lemma pscoped_mono M M' ρ : M <= M' -> pscoped M ρ = true -> pscoped M' ρ = true.
Proof. intros Hle; apply (pscoped_mono_depth M M' (S (rpdepth ρ)) Hle); lia. Qed.

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
  forall ρ, rpdepth ρ < n -> pscoped 0 ρ = true -> rpshift None ρ = ρ.
Proof.
  induction n as [|n IH]; intros ρ Hd H; [lia|].
  apply rpextensionality; intros v Hv; rewrite rpapply_pshift by exact Hv.
  pose proof (proj1 (pscoped_spec 0 ρ) H v Hv) as Hr.
  destruct (rpapply ρ v) as [[[x|] i]|[u ρ']] eqn:E.
  - reflexivity.
  - cbn in Hr; discriminate.
  - rewrite result_wf_inr in Hr; pose proof (rpdepth_payload _ _ _ _ Hv E).
    cbn [fst snd]; rewrite IH by (lia || exact Hr); reflexivity.
Qed.

Theorem pshift_closed ρ : pscoped 0 ρ = true -> rpshift None ρ = ρ.
Proof. apply (pshift_closed_depth (S (rpdepth ρ))); lia. Qed.

Theorem lift_closed a : scoped 0 0 a = true -> rlift None a = a.
Proof.
  intros H; apply scoped_spec in H as [Ht Hr]; apply rlift_free.
  - intros i; rewrite Ht by lia; do 2 f_equal; lia.
  - intros [[x|] i] w Hv E; [|contradiction].
    pose proof (Hr (mk_rvar (Some x) i) eq_refl) as Hw; rewrite E in Hw.
    destruct w as [[y|] j]; cbn in Hw; [discriminate|discriminate].
  - intros [[x|] i] [u ρ] E.
    + pose proof (Hr (mk_rvar (Some x) i) eq_refl) as Hw; rewrite E in Hw.
      apply pshift_closed, Hw.
    + rewrite Ht in E by lia; discriminate.
Qed.

End Scoped.
