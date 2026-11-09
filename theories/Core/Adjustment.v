(** * Raw adjustments

    The unindexed layer; its names carry an [r] prefix, and the indexed
    public layer (Indexed.v) takes the plain names.

    A [radj T] is an adjustment (Repr.v) packaged with an SProp proof that
    it is deeply well formed (Deep.v).  [T] is the user's type of terms with
    no bound variables; the library never looks inside it.

    Because the proof is in SProp, two adjustments are equal exactly when
    their data is equal, and by canonicity that happens exactly when they
    act the same ([rextensionality]).  So all the usual laws hold up to
    Leibniz equality.

    A variable is sent either to a variable or to a payload [(u, ρ)]: a term
    [u] together with a payload adjustment [ρ : rpadj T] still to be applied
    to it.  Payload adjustments only ever see the free (named) variables of
    [u], and are canonical for that restricted meaning. *)

From Stdlib Require Import PArith Arith List Lia Bool StrictProp.
From ShiftedNames.Core Require Export Strict.
From ShiftedNames.Core Require Import Trie Label Var Counts Based Skew ATrie Repr Point Deep Compose.
Import ListNotations.

(** ** The types of adjustments and payload adjustments *)

Record radj (T : Type) : Type :=
  mk_radj { radj_n : @nadj T; radj_ok : Is_true_s (nwfc false (fun r => r) radj_n) }.

Record rpadj (T : Type) : Type :=
  mk_rpadj { rpadj_n : @nadj T; rpadj_ok : Is_true_s (nwfc true (fun r => r) rpadj_n) }.

Arguments mk_radj {T} _ _.
Arguments radj_n {T} _.
Arguments radj_ok {T} _.
Arguments mk_rpadj {T} _ _.
Arguments rpadj_n {T} _.
Arguments rpadj_ok {T} _.

Lemma radj_eq {T} (a b : radj T) : radj_n a = radj_n b -> a = b.
Proof. destruct a as [ra Ha], b as [rb Hb]; cbn; intros ->; reflexivity. Qed.

Lemma rpadj_eq {T} (a b : rpadj T) : rpadj_n a = rpadj_n b -> a = b.
Proof. destruct a as [ra Ha], b as [rb Hb]; cbn; intros ->; reflexivity. Qed.

Section Adjustment.

Context {T : Type}.

Implicit Types (a b c : radj T) (ρ : rpadj T) (v w : rvar) (h l : option label).

Lemma radj_wf a : nwf false (radj_n a).
Proof. apply Is_true_s_elim, radj_ok. Qed.

Lemma rpadj_wf ρ : nwf true (rpadj_n ρ).
Proof. apply Is_true_s_elim, rpadj_ok. Qed.

Lemma radj_local a : nlocal Qall (radj_n a).
Proof. apply (nwf_local false), radj_wf. Qed.

Lemma rpadj_local ρ : nlocal Qnamed (rpadj_n ρ).
Proof. apply (nwf_local true), rpadj_wf. Qed.

Lemma radj_fin a : nfin (radj_n a).
Proof. apply (nwf_fin false), radj_wf. Qed.

(** ** The identity payload adjustment: every named label used from 0, the
    bound label unused. *)

Definition pidentity_n : @nadj T :=
  NAdj (mk_counts (Some 0) (set (label_key None) None Empty) (Is_true_s_intro eq_refl)) AEmpty.

Lemma pidentity_wf : nwf true pidentity_n.
Proof. vm_compute; reflexivity. Qed.

Definition rpidentity : rpadj T := mk_rpadj pidentity_n (Is_true_s_intro pidentity_wf).

(** ** Packaging the payloads of results *)

(** Only used on payloads that are deeply well formed; the fallback is
    never reached. *)
Definition psel (x : @nadj T) : @nadj T := if nwfc true (fun r => r) x then x else pidentity_n.

Lemma psel_ok x : nwfc true (fun r => r) (psel x) = true.
Proof. unfold psel; destruct (nwfc true _ x) eqn:E; [exact E|apply pidentity_wf]. Qed.

Definition rto_padj (x : @nadj T) : rpadj T := mk_rpadj (psel x) (Is_true_s_intro (psel_ok x)).

Lemma rpadj_n_to_padj x : nwf true x -> rpadj_n (rto_padj x) = x.
Proof. intros H; cbn; unfold psel; unfold nwf in H; rewrite H; reflexivity. Qed.

Lemma rto_padj_padj_n ρ : rto_padj (rpadj_n ρ) = ρ.
Proof. apply rpadj_eq, rpadj_n_to_padj, rpadj_wf. Qed.

Definition rresult : Type := (rvar + (T * rpadj T))%type.

Definition rpack (r : result) : rresult :=
  match r with inl w => inl w | inr (u, x) => inr (u, rto_padj x) end.

Definition lower (r : rresult) : result :=
  match r with inl w => inl w | inr (u, ρ) => inr (u, rpadj_n ρ) end.

Lemma lower_inj r1 r2 : lower r1 = lower r2 -> r1 = r2.
Proof.
  destruct r1 as [w1|[u1 ρ1]], r2 as [w2|[u2 ρ2]]; cbn; intros H; try discriminate;
    injection H; intros; subst; [reflexivity|].
  f_equal; f_equal; apply rpadj_eq; assumption.
Qed.

Lemma lower_rpack r : (forall u x, r = inr (u, x) -> nwf true x) -> lower (rpack r) = r.
Proof.
  destruct r as [w|[u x]]; [reflexivity|]; intros H; cbn [rpack lower].
  f_equal; f_equal; apply rpadj_n_to_padj, (H u x eq_refl).
Qed.

(** ** Action *)

Definition rapply a v : rresult := rpack (napply (radj_n a) v).

Lemma lower_rapply a v : lower (rapply a v) = napply (radj_n a) v.
Proof. apply lower_rpack; intros u x E; apply (nwf_payload false _ v u x (radj_wf a) eq_refl E). Qed.

(** What a payload adjustment does to a free variable. *)
Definition rpapply ρ v : rresult := rpack (napply (rpadj_n ρ) v).

Lemma lower_rpapply ρ v : v_label v <> None -> lower (rpapply ρ v) = napply (rpadj_n ρ) v.
Proof.
  intros Hv; apply lower_rpack; intros u x E; apply (nwf_payload true _ v u x (rpadj_wf ρ)); [|exact E].
  destruct (v_label v); [reflexivity|contradiction].
Qed.

(** Adjustments are equal when they act the same. *)
Theorem rextensionality a b : (forall v, rapply a v = rapply b v) -> a = b.
Proof.
  intros H; apply radj_eq, (ncanonical Qall); try apply radj_local.
  intros v _; rewrite <- !lower_rapply, H; reflexivity.
Qed.

(** Payload adjustments are equal when they act the same on free variables. *)
Theorem rpextensionality ρ1 ρ2 :
  (forall v, v_label v <> None -> rpapply ρ1 v = rpapply ρ2 v) -> ρ1 = ρ2.
Proof.
  intros H; apply rpadj_eq, (ncanonical Qnamed); try apply rpadj_local.
  intros v Hv; assert (Hn : v_label v <> None) by (destruct (v_label v); [discriminate|discriminate]).
  rewrite <- !lower_rpapply, H by exact Hn; reflexivity.
Qed.

(** ** Identity and composition *)

Definition ridentity : radj T := mk_radj nidentity (Is_true_s_intro nwf_identity).

Lemma rapply_identity v : rapply ridentity v = inl v.
Proof. unfold rapply; cbn [radj_n ridentity]; rewrite napply_identity; reflexivity. Qed.

(** [rcompose a b] first applies [b] and then [a]. *)
Definition rcompose a b : radj T :=
  mk_radj (compose (radj_n a) (radj_n b))
    (Is_true_s_intro (proj1 (compose_spec _ _ (radj_wf a) (radj_wf b)))).

Lemma pcompose_ok a ρ : nwf true (ncomp (radj_n a) true (rpadj_n ρ) cnone).
Proof. apply (comp_correct (radj_n a) (radj_local a) (radj_wf a) true), rpadj_wf. Qed.

(** [rpcompose a ρ]: the payload adjustment [a ∘ ρ]. *)
Definition rpcompose a ρ : rpadj T :=
  mk_rpadj (ncomp (radj_n a) true (rpadj_n ρ) cnone) (Is_true_s_intro (pcompose_ok a ρ)).

Lemma rpack_rcomp a r :
  (forall u x, r = inr (u, x) -> nwf true x) ->
  rpack (rcomp (radj_n a) r)
  = match rpack r with inl w => rapply a w | inr (u, ρ) => inr (u, rpcompose a ρ) end.
Proof.
  intros H; destruct r as [w|[u x]]; [reflexivity|]; cbn [rcomp rpack].
  rewrite <- (rpadj_n_to_padj x (H u x eq_refl)) at 1; f_equal; f_equal.
  apply rpadj_eq; cbn [rpadj_n rpcompose]; apply rpadj_n_to_padj, (pcompose_ok a (rto_padj x)).
Qed.

Theorem rapply_compose a b v :
  rapply (rcompose a b) v
  = match rapply b v with inl w => rapply a w | inr (u, ρ) => inr (u, rpcompose a ρ) end.
Proof.
  unfold rapply at 1; cbn [radj_n rcompose].
  rewrite (proj2 (compose_spec _ _ (radj_wf a) (radj_wf b))).
  apply rpack_rcomp; intros u x E; apply (nwf_payload false _ v u x (radj_wf b) eq_refl E).
Qed.

Theorem rpapply_pcompose a ρ v :
  v_label v <> None ->
  rpapply (rpcompose a ρ) v
  = match rpapply ρ v with inl w => rapply a w | inr (u, ρ') => inr (u, rpcompose a ρ') end.
Proof.
  intros Hv; unfold rpapply at 1; cbn [rpadj_n rpcompose].
  assert (HQ : Qof true (v_label v) = true) by (destruct (v_label v); [reflexivity|contradiction]).
  destruct (comp_correct (radj_n a) (radj_local a) (radj_wf a) true (rpadj_n ρ) (rpadj_wf ρ)) as [_ [Hm _]].
  rewrite (Hm v HQ); apply rpack_rcomp; intros u x E; apply (nwf_payload true _ v u x (rpadj_wf ρ) HQ E).
Qed.

(** ** Nesting depth *)

Definition rdepth a : nat := nnest (radj_n a).
Definition rpdepth ρ : nat := nnest (rpadj_n ρ).

Lemma rpdepth_payload ρ v u ρ' : v_label v <> None -> rpapply ρ v = inr (u, ρ') -> rpdepth ρ' < rpdepth ρ.
Proof.
  intros Hv E; pose proof (f_equal lower E) as E'; rewrite lower_rpapply in E' by exact Hv; cbn [lower] in E'.
  apply (nest_napply _ v u); [|exact E'].
  intros k e Ek; pose proof (rpadj_local ρ) as Hl; destruct (rpadj_n ρ) as [r es]; cbn [nentries] in Ek.
  destruct Hl as [_ [_ [_ [Hent _]]]]; destruct (Hent k e Ek) as [Hok _]; destruct e; apply Hok.
Qed.

(** ** The category laws *)

Theorem rcompose_identity_r a : rcompose a ridentity = a.
Proof.
  apply rextensionality; intro v; rewrite rapply_compose, rapply_identity; reflexivity.
Qed.

Lemma rpcompose_identity_depth n : forall ρ, rpdepth ρ < n -> rpcompose ridentity ρ = ρ.
Proof.
  induction n as [|n IH]; intros ρ Hd; [lia|].
  apply rpextensionality; intros v Hv; rewrite rpapply_pcompose by exact Hv.
  destruct (rpapply ρ v) as [w|[u ρ']] eqn:E; [apply rapply_identity|].
  rewrite IH; [reflexivity|]; pose proof (rpdepth_payload ρ v u ρ' Hv E); lia.
Qed.

Theorem rpcompose_identity ρ : rpcompose ridentity ρ = ρ.
Proof. apply (rpcompose_identity_depth (S (rpdepth ρ))); lia. Qed.

Theorem rcompose_identity_l b : rcompose ridentity b = b.
Proof.
  apply rextensionality; intro v; rewrite rapply_compose.
  destruct (rapply b v) as [w|[u ρ]]; [apply rapply_identity|rewrite rpcompose_identity; reflexivity].
Qed.

Lemma rpcompose_compose_depth a b n :
  forall ρ, rpdepth ρ < n -> rpcompose a (rpcompose b ρ) = rpcompose (rcompose a b) ρ.
Proof.
  induction n as [|n IH]; intros ρ Hd; [lia|].
  apply rpextensionality; intros v Hv; rewrite !rpapply_pcompose by exact Hv.
  destruct (rpapply ρ v) as [w|[u ρ']] eqn:E; [rewrite rapply_compose; reflexivity|].
  rewrite IH; [reflexivity|]; pose proof (rpdepth_payload ρ v u ρ' Hv E); lia.
Qed.

Theorem rpcompose_compose a b ρ : rpcompose a (rpcompose b ρ) = rpcompose (rcompose a b) ρ.
Proof. apply (rpcompose_compose_depth a b (S (rpdepth ρ))); lia. Qed.

Theorem rcompose_assoc a b c : rcompose a (rcompose b c) = rcompose (rcompose a b) c.
Proof.
  apply rextensionality; intro v; rewrite !rapply_compose.
  destruct (rapply c v) as [w|[u ρ]]; [rewrite rapply_compose; reflexivity|].
  rewrite rpcompose_compose; reflexivity.
Qed.

(** ** Output entries: [rpush_outer h a] is [a] followed by weakening past
    one new outer [h]. *)

Definition rpush_outer h a : radj T :=
  mk_radj (weaken h (radj_n a)) (Is_true_s_intro (nwf_weaken h _ (radj_wf a))).

Lemma pshift_ok h ρ : nwf true (weaken h (rpadj_n ρ)).
Proof.
  pose proof (rpadj_wf ρ) as H; destruct (rpadj_n ρ) as [r es]; cbn [weaken].
  apply (nwf_cadd (S (nnest (NAdj r es)))); [lia|exact H|apply keyed_cone|reflexivity].
Qed.

(** Weakening a payload adjustment past a new outer [h]. *)
Definition rpshift h ρ : rpadj T := mk_rpadj (weaken h (rpadj_n ρ)) (Is_true_s_intro (pshift_ok h ρ)).

Lemma rweaken_var h w :
  (if label_eqb (v_label w) h then mk_rvar h (S (v_index w)) else w) = shift_rvar (mk_rvar h 0) w.
Proof.
  destruct w as [l i]; unfold shift_rvar; cbn [v_label v_index].
  destruct (label_eqb_spec l h) as [->|Hne]; [rewrite label_eqb_refl; reflexivity|].
  rewrite (proj2 (label_eqb_neq h l)) by congruence; reflexivity.
Qed.

Lemma rpack_rweaken h r :
  (forall u x, r = inr (u, x) -> nwf true x) ->
  rpack (rweaken h r)
  = match rpack r with inl w => inl (shift_rvar (mk_rvar h 0) w) | inr (u, ρ) => inr (u, rpshift h ρ) end.
Proof.
  intros H; destruct r as [w|[u [r es]]]; cbn [rweaken rpack]; [rewrite rweaken_var; reflexivity|].
  f_equal; f_equal; apply rpadj_eq; cbn [rpadj_n rpshift].
  assert (Hw : nwf true (weaken h (NAdj r es))).
  { pose proof (pshift_ok h (rto_padj (NAdj r es))) as P.
    rewrite rpadj_n_to_padj in P by apply (H u _ eq_refl); exact P. }
  rewrite (rpadj_n_to_padj (NAdj r es)) by apply (H u _ eq_refl); apply rpadj_n_to_padj, Hw.
Qed.

Theorem rapply_push_outer h a v :
  rapply (rpush_outer h a) v
  = match rapply a v with inl w => inl (shift_rvar (mk_rvar h 0) w) | inr (u, ρ) => inr (u, rpshift h ρ) end.
Proof.
  unfold rapply at 1; cbn [radj_n rpush_outer]; rewrite napply_weaken by apply radj_local.
  apply rpack_rweaken; intros u x E; apply (nwf_payload false _ v u x (radj_wf a) eq_refl E).
Qed.

(** In a payload, the bound label may be unused; weakening it then changes
    nothing. *)
Lemma rweaken_unused h (r : @result T) :
  (forall w, r = inl w -> label_key (v_label w) <> label_key h) ->
  (forall u rho, r = inr (u, rho) -> cwf (nroot rho) /\ cget (nroot rho) (label_key h) = None) ->
  rweaken h r = r.
Proof.
  destruct r as [w|[u [r0 es0]]]; intros Hw Hp; cbn [rweaken].
  - rewrite (proj2 (label_eqb_neq _ _)); [reflexivity|intros E; apply (Hw w eq_refl); rewrite E; reflexivity].
  - destruct (Hp u _ eq_refl) as [Cr Hr]; cbn [nroot nentries] in *; f_equal; f_equal; f_equal.
    apply counts_ext; [apply cwf_cmap2|exact Cr|]; intro k; rewrite cget_cadd, cget_cone.
    destruct (Pos.eqb_spec k (label_key h)) as [->|]; [rewrite Hr; reflexivity|destruct (cget r0 k); reflexivity].
Qed.

Lemma weaken_unused h (x : @nadj T) : cwf (nroot x) -> cget (nroot x) (label_key h) = None -> weaken h x = x.
Proof.
  destruct x as [r es]; cbn [nroot weaken]; intros Cr Hr; f_equal.
  apply counts_ext; [apply cwf_cmap2|exact Cr|]; intro k; rewrite cget_cadd, cget_cone.
  destruct (Pos.eqb_spec k (label_key h)) as [->|]; [rewrite Hr; reflexivity|destruct (cget r k); reflexivity].
Qed.

Lemma napply_unused Q (x : @nadj T) k v :
  nlocal Q x -> nfin x -> cget (nroot x) k = None -> Q (v_label v) = true ->
  match napply x v with
  | inl w => label_key (v_label w) <> k
  | inr (u, rho) => cwf (nroot rho) /\ cget (nroot rho) k = None
  end.
Proof.
  destruct x as [r es]; intros Hl Hf Hk HQ; cbn [nroot] in Hk; pose proof Hl as [_ [_ [_ [Hent [HQr _]]]]].
  assert (Hv : label_key (v_label v) <> k) by (intros <-; exact (HQr _ HQ Hk)).
  cbn [napply]; destruct (aget (label_key (v_label v)) es) as [e|] eqn:E; [|exact Hv].
  destruct (Hent _ _ E) as [Hok _]; destruct e as [h ts len p]; destruct Hok as [Hkh [G _]].
  pose proof (root_covers Q r es k Hl Hf Hk _ _ E) as Hcv; rewrite uses_entry_klist in Hcv by exact G.
  cbn [eapply]; destruct (Nat.ltb _ _); [|cbn [v_label]; rewrite Hkh; exact Hv].
  destruct (knth ts _) as [t|] eqn:Et; [|cbn [v_label]; rewrite Hkh; exact Hv].
  pose proof (knth_in _ _ _ G Et) as Hin.
  assert (Ht : cget (uses t) k = None).
  { destruct (cget (uses t) k) as [m|] eqn:Em; [|reflexivity].
    destruct (lmin_le _ t k m Hin Em) as [n [En _]]; rewrite En in Hcv; destruct (cget (cone _ p) k); discriminate. }
  destruct t as [y j|u [r0 es0]]; cbn [tunshift tresult v_label].
  - intros Ey; cbn in Ht; rewrite cget_cone, Ey, Pos.eqb_refl in Ht; discriminate.
  - split; [apply cwf_cmap2|]; cbn [nroot]; rewrite cget_cadd, Hk; cbn in Ht; rewrite Ht; reflexivity.
Qed.

Theorem rpapply_pshift h ρ v :
  v_label v <> None ->
  rpapply (rpshift h ρ) v
  = match rpapply ρ v with inl w => inl (shift_rvar (mk_rvar h 0) w) | inr (u, ρ') => inr (u, rpshift h ρ') end.
Proof.
  intros Hv; assert (HQ : Qnamed (v_label v) = true) by (destruct (v_label v); [reflexivity|contradiction]).
  assert (Hp : forall u x, napply (rpadj_n ρ) v = inr (u, x) -> nwf true x)
    by (intros u x E; apply (nwf_payload true _ v u x (rpadj_wf ρ) HQ E)).
  unfold rpapply at 1; cbn [rpadj_n rpshift].
  pose proof (rpadj_local ρ) as Hl; pose proof (nwf_fin true _ (rpadj_wf ρ)) as Hf.
  destruct (cget (nroot (rpadj_n ρ)) (label_key h)) eqn:Eh.
  - rewrite napply_weaken_used by (rewrite Eh; discriminate); apply rpack_rweaken, Hp.
  - assert (Cr : cwf (nroot (rpadj_n ρ))) by (destruct (rpadj_n ρ); apply Hl).
    rewrite (weaken_unused h _ Cr Eh).
    pose proof (napply_unused Qnamed _ _ v Hl Hf Eh HQ) as Hu.
    rewrite <- (rweaken_unused h (napply (rpadj_n ρ) v)) at 1.
    + apply rpack_rweaken, Hp.
    + intros w E; rewrite E in Hu; exact Hu.
    + intros u rho E; rewrite E in Hu; exact Hu.
Qed.

(** ** Input entries: [rpush_inner h t a] sends the innermost [h] to [t] and
    passes everything else to [a].  A variable target may be any variable. *)

Inductive rtarget : Type :=
| RRename (w : rvar)
| RBind (u : T) (ρ : rpadj T).

Definition rtarget_result (t : rtarget) : rresult :=
  match t with RRename w => inl w | RBind u ρ => inr (u, ρ) end.

Definition rtarget_n (t : rtarget) : target :=
  match t with RRename w => TVar (v_label w) (v_index w) | RBind u ρ => TBind u (rpadj_n ρ) end.

Lemma rtarget_wf t : twf (rtarget_n t).
Proof. destruct t as [w|u ρ]; [exact I|apply rpadj_wf]. Qed.

Definition rpush_inner h t a : radj T :=
  mk_radj (extend h (rtarget_n t) (radj_n a)) (Is_true_s_intro (nwf_extend h _ _ (radj_wf a) (rtarget_wf t))).

Theorem rapply_push_inner h t a v :
  rapply (rpush_inner h t a) v
  = if rvar_eqb v (mk_rvar h 0) then rtarget_result t else rapply a (unshift_rvar (mk_rvar h 0) v).
Proof.
  unfold rapply at 1; cbn [radj_n rpush_inner].
  assert (Hok : tok (rtarget_n t))
    by (destruct t as [w|u ρ]; [exact I|cbn; pose proof (rpadj_local ρ) as Hl;
        destruct (rpadj_n ρ) as [r es]; destruct Hl as [_ [Hc _]]; exact Hc]).
  rewrite napply_extend by (apply radj_local || apply radj_fin || exact Hok).
  destruct (rvar_eqb v _); [|reflexivity].
  destruct t as [w|u ρ]; cbn; [destruct w; reflexivity|rewrite rto_padj_padj_n; reflexivity].
Qed.

(** ** Going under a binder *)

(** [rlift h a] is [a] moved under a binder labelled [h]. *)
Definition rlift h a : radj T := rpush_inner h (RRename (mk_rvar h 0)) (rpush_outer h a).

Theorem rapply_lift h a v :
  rapply (rlift h a) v
  = if rvar_eqb v (mk_rvar h 0) then inl v
    else match rapply a (unshift_rvar (mk_rvar h 0) v) with
         | inl w => inl (shift_rvar (mk_rvar h 0) w)
         | inr (u, ρ) => inr (u, rpshift h ρ)
         end.
Proof.
  unfold rlift; rewrite rapply_push_inner, rapply_push_outer.
  destruct (rvar_eqb_spec v (mk_rvar h 0)) as [->|]; reflexivity.
Qed.

End Adjustment.

Arguments rtarget T : clear implicits.
Arguments rresult T : clear implicits.
