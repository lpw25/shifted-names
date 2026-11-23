(** * Raw adjustments

    The unindexed layer; its names carry an [r] prefix, and the indexed
    public layer (Indexed.v) takes the plain names.

    A [radj T] is an adjustment (Repr.v) packaged with an SProp proof that
    it is deeply well formed (Deep.v).  [T] is the user's type of terms;
    the library never looks inside it.

    Because the proof is in SProp, two adjustments are equal exactly when
    their data is equal, and by canonicity that happens exactly when they
    act the same ([rextensionality]).  So all the usual laws hold up to
    Leibniz equality.

    A variable is sent either to a variable or to a payload [(u, ρ)]: a term
    [u] together with an adjustment [ρ] still to be applied to it, which
    acts on all of [u]'s variables, bound ones too. *)

From Stdlib Require Import PArith Arith List Lia Bool StrictProp.
From ShiftedNames.Core Require Export Strict.
From ShiftedNames.Core Require Import Trie Label Var Counts Based Skew ATrie Repr Point Deep Compose.
Import ListNotations.

(** ** The type of adjustments *)

Record radj (T : Type) : Type :=
  mk_radj { radj_n : @nadj T; radj_ok : Is_true_s (nwfc false (fun r => r) radj_n) }.

Arguments mk_radj {T} _ _.
Arguments radj_n {T} _.
Arguments radj_ok {T} _.

Lemma radj_eq {T} (a b : radj T) : radj_n a = radj_n b -> a = b.
Proof. destruct a as [ra Ha], b as [rb Hb]; cbn; intros ->; reflexivity. Qed.

Section Adjustment.

Context {T : Type}.

Implicit Types (a b c ρ : radj T) (v w : rvar) (h l : option label).

Lemma radj_wf a : nwf false (radj_n a).
Proof. apply Is_true_s_elim, radj_ok. Qed.

Lemma radj_local a : nlocal Qall (radj_n a).
Proof. apply (nwf_local false), radj_wf. Qed.

Lemma radj_fin a : nfin (radj_n a).
Proof. apply (nwf_fin false), radj_wf. Qed.

(** ** Packaging the payloads of results *)

(** Only used on payloads that are deeply well formed; the fallback is
    never reached. *)
Definition asel (x : @nadj T) : @nadj T := if nwfc false (fun r => r) x then x else nidentity.

Lemma asel_ok x : nwfc false (fun r => r) (asel x) = true.
Proof. unfold asel; destruct (nwfc false _ x) eqn:E; [exact E|apply (@nwf_identity T)]. Qed.

Definition rto_adj (x : @nadj T) : radj T := mk_radj (asel x) (Is_true_s_intro (asel_ok x)).

Lemma radj_n_to_adj x : nwf false x -> radj_n (rto_adj x) = x.
Proof. intros H; cbn; unfold asel; unfold nwf in H; rewrite H; reflexivity. Qed.

Lemma rto_adj_n a : rto_adj (radj_n a) = a.
Proof. apply radj_eq, radj_n_to_adj, radj_wf. Qed.

Definition rresult : Type := (rvar + (T * radj T))%type.

Definition rpack (r : result) : rresult :=
  match r with inl w => inl w | inr (u, x) => inr (u, rto_adj x) end.

Definition lower (r : rresult) : result :=
  match r with inl w => inl w | inr (u, ρ) => inr (u, radj_n ρ) end.

Lemma lower_inj r1 r2 : lower r1 = lower r2 -> r1 = r2.
Proof.
  destruct r1 as [w1|[u1 ρ1]], r2 as [w2|[u2 ρ2]]; cbn; intros H; try discriminate;
    injection H; intros; subst; [reflexivity|].
  f_equal; f_equal; apply radj_eq; assumption.
Qed.

Lemma lower_rpack r : (forall u x, r = inr (u, x) -> nwf false x) -> lower (rpack r) = r.
Proof.
  destruct r as [w|[u x]]; [reflexivity|]; intros H; cbn [rpack lower].
  f_equal; f_equal; apply radj_n_to_adj, (H u x eq_refl).
Qed.

(** ** Action *)

Definition rapply a v : rresult := rpack (napply (radj_n a) v).

Lemma lower_rapply a v : lower (rapply a v) = napply (radj_n a) v.
Proof. apply lower_rpack; intros u x E; apply (nwf_payload false _ v u x (radj_wf a) eq_refl E). Qed.

(** Adjustments are equal when they act the same. *)
Theorem rextensionality a b : (forall v, rapply a v = rapply b v) -> a = b.
Proof.
  intros H; apply radj_eq, (ncanonical Qall); try apply radj_local.
  intros v _; rewrite <- !lower_rapply, H; reflexivity.
Qed.

(** ** Nesting depth *)

Definition rdepth a : nat := nnest (radj_n a).

Lemma rdepth_payload a v u ρ : rapply a v = inr (u, ρ) -> rdepth ρ < rdepth a.
Proof.
  intros E; pose proof (f_equal lower E) as E'; rewrite lower_rapply in E'; cbn [lower] in E'.
  apply (nest_napply _ v u); [|exact E'].
  intros k e Ek; pose proof (radj_local a) as Hl; destruct (radj_n a) as [r es]; cbn [nentries] in Ek.
  destruct Hl as [_ [_ [Hent _]]]; destruct (Hent k e Ek) as [Hok _]; destruct e; apply Hok.
Qed.

(** ** Identity and composition *)

Definition ridentity : radj T := mk_radj nidentity (Is_true_s_intro nwf_identity).

Lemma rapply_identity v : rapply ridentity v = inl v.
Proof. unfold rapply; cbn [radj_n ridentity]; rewrite napply_identity; reflexivity. Qed.

(** [rcompose a b] first applies [b] and then [a]. *)
Definition rcompose a b : radj T :=
  mk_radj (compose (radj_n a) (radj_n b))
    (Is_true_s_intro (proj1 (compose_spec _ _ (radj_wf a) (radj_wf b)))).

Lemma rpack_rcomp a r :
  (forall u x, r = inr (u, x) -> nwf false x) ->
  rpack (rcomp (radj_n a) r)
  = match rpack r with inl w => rapply a w | inr (u, ρ) => inr (u, rcompose a ρ) end.
Proof.
  intros H; destruct r as [w|[u x]]; [reflexivity|]; cbn [rcomp rpack].
  pose proof (H u x eq_refl) as Hx; f_equal; f_equal; apply radj_eq; cbn [radj_n rcompose].
  rewrite (radj_n_to_adj x Hx); apply radj_n_to_adj, (proj1 (compose_spec _ _ (radj_wf a) Hx)).
Qed.

Theorem rapply_compose a b v :
  rapply (rcompose a b) v
  = match rapply b v with inl w => rapply a w | inr (u, ρ) => inr (u, rcompose a ρ) end.
Proof.
  unfold rapply at 1; cbn [radj_n rcompose].
  rewrite (proj2 (compose_spec _ _ (radj_wf a) (radj_wf b))).
  apply rpack_rcomp; intros u x E; apply (nwf_payload false _ v u x (radj_wf b) eq_refl E).
Qed.

(** ** The category laws *)

Theorem rcompose_identity_r a : rcompose a ridentity = a.
Proof.
  apply rextensionality; intro v; rewrite rapply_compose, rapply_identity; reflexivity.
Qed.

Lemma rcompose_identity_depth n : forall b, rdepth b < n -> rcompose ridentity b = b.
Proof.
  induction n as [|n IH]; intros b Hd; [lia|].
  apply rextensionality; intros v; rewrite rapply_compose.
  destruct (rapply b v) as [w|[u ρ]] eqn:E; [apply rapply_identity|].
  rewrite IH; [reflexivity|]; pose proof (rdepth_payload b v u ρ E); lia.
Qed.

Theorem rcompose_identity_l b : rcompose ridentity b = b.
Proof. apply (rcompose_identity_depth (S (rdepth b))); lia. Qed.

Lemma rcompose_assoc_depth a b n :
  forall c, rdepth c < n -> rcompose a (rcompose b c) = rcompose (rcompose a b) c.
Proof.
  induction n as [|n IH]; intros c Hd; [lia|].
  apply rextensionality; intros v; rewrite !rapply_compose.
  destruct (rapply c v) as [w|[u ρ]] eqn:E; [rewrite rapply_compose; reflexivity|].
  rewrite IH; [reflexivity|]; pose proof (rdepth_payload c v u ρ E); lia.
Qed.

Theorem rcompose_assoc a b c : rcompose a (rcompose b c) = rcompose (rcompose a b) c.
Proof. apply (rcompose_assoc_depth a b (S (rdepth c))); lia. Qed.

(** ** Output entries: [rpush_outer h a] is [a] followed by weakening past
    one new outer [h]. *)

Definition rpush_outer h a : radj T :=
  mk_radj (weaken h (radj_n a)) (Is_true_s_intro (nwf_weaken h _ (radj_wf a))).

Lemma rweaken_var h w :
  (if label_eqb (v_label w) h then mk_rvar h (S (v_index w)) else w) = shift_rvar (mk_rvar h 0) w.
Proof.
  destruct w as [l i]; unfold shift_rvar; cbn [v_label v_index].
  destruct (label_eqb_spec l h) as [->|Hne]; [rewrite label_eqb_refl; reflexivity|].
  rewrite (proj2 (label_eqb_neq h l)) by congruence; reflexivity.
Qed.

Lemma rpack_rweaken h r :
  (forall u x, r = inr (u, x) -> nwf false x) ->
  rpack (rweaken h r)
  = match rpack r with inl w => inl (shift_rvar (mk_rvar h 0) w) | inr (u, ρ) => inr (u, rpush_outer h ρ) end.
Proof.
  intros H; destruct r as [w|[u [r es]]]; cbn [rweaken rpack]; [rewrite rweaken_var; reflexivity|].
  f_equal; f_equal; apply radj_eq; cbn [radj_n rpush_outer].
  assert (Hw : nwf false (weaken h (NAdj r es))) by (apply nwf_weaken, (H u _ eq_refl)).
  rewrite (radj_n_to_adj (NAdj r es)) by apply (H u _ eq_refl); apply radj_n_to_adj, Hw.
Qed.

Theorem rapply_push_outer h a v :
  rapply (rpush_outer h a) v
  = match rapply a v with inl w => inl (shift_rvar (mk_rvar h 0) w) | inr (u, ρ) => inr (u, rpush_outer h ρ) end.
Proof.
  unfold rapply at 1; cbn [radj_n rpush_outer]; rewrite napply_weaken by apply radj_local.
  apply rpack_rweaken; intros u x E; apply (nwf_payload false _ v u x (radj_wf a) eq_refl E).
Qed.

(** ** Input entries: [rpush_inner h t a] sends the innermost [h] to [t] and
    passes everything else to [a].  A variable target may be any variable. *)

Inductive rtarget : Type :=
| RRename (w : rvar)
| RBind (u : T) (ρ : radj T).

Definition rtarget_result (t : rtarget) : rresult :=
  match t with RRename w => inl w | RBind u ρ => inr (u, ρ) end.

Definition rtarget_n (t : rtarget) : target :=
  match t with RRename w => TVar (v_label w) (v_index w) | RBind u ρ => TBind u (radj_n ρ) end.

Lemma rtarget_wf t : twf (rtarget_n t).
Proof. destruct t as [w|u ρ]; [exact I|apply radj_wf]. Qed.

Definition rpush_inner h t a : radj T :=
  mk_radj (extend h (rtarget_n t) (radj_n a)) (Is_true_s_intro (nwf_extend h _ _ (radj_wf a) (rtarget_wf t))).

Theorem rapply_push_inner h t a v :
  rapply (rpush_inner h t a) v
  = if rvar_eqb v (mk_rvar h 0) then rtarget_result t else rapply a (unshift_rvar (mk_rvar h 0) v).
Proof.
  unfold rapply at 1; cbn [radj_n rpush_inner].
  rewrite napply_extend by (apply radj_local || apply radj_fin).
  destruct (rvar_eqb v _); [|reflexivity].
  destruct t as [w|u ρ]; cbn; [destruct w; reflexivity|rewrite rto_adj_n; reflexivity].
Qed.

(** ** Going under a binder *)

(** [rlift h a] is [a] moved under a binder labelled [h]. *)
Definition rlift h a : radj T := rpush_inner h (RRename (mk_rvar h 0)) (rpush_outer h a).

Theorem rapply_lift h a v :
  rapply (rlift h a) v
  = if rvar_eqb v (mk_rvar h 0) then inl v
    else match rapply a (unshift_rvar (mk_rvar h 0) v) with
         | inl w => inl (shift_rvar (mk_rvar h 0) w)
         | inr (u, ρ) => inr (u, rpush_outer h ρ)
         end.
Proof.
  unfold rlift; rewrite rapply_push_inner, rapply_push_outer.
  destruct (rvar_eqb_spec v (mk_rvar h 0)) as [->|]; reflexivity.
Qed.

End Adjustment.

Arguments rtarget T : clear implicits.
Arguments rresult T : clear implicits.
