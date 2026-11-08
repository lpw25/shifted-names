(** * Raw adjustments

    The unindexed layer; its names carry an [r] prefix, and the indexed
    public layer (Indexed.v) takes the plain names.

    A [radj T] is a normal nested adjustment (Nested.v) packaged with
    an SProp proof of normality.  [T] is the user's type of terms with no
    bound variables; the library never looks inside it.

    Because the proof is in SProp, two adjustments are equal exactly when
    their data is equal, and by canonicity that happens exactly when they
    act the same ([rextensionality]).  So all the usual laws hold up to
    Leibniz equality.

    A variable is sent either to a variable or to a payload [(u, ρ)]: a term
    [u] together with a payload adjustment [ρ : rpadj T] that is still to be
    applied to it.  Payload adjustments only ever see the free variables of
    [u], and are canonical for that restricted meaning. *)

From Stdlib Require Import PArith Arith List Lia Bool StrictProp.
From ShiftedNames.Core Require Export Strict.
From ShiftedNames.Core Require Import Trie Label Var Nested.
From ShiftedNames.Core Require Slots.
Import ListNotations.

(** ** The types of adjustments and payload adjustments *)

Record radj (T : Type) : Type :=
  mk_radj {
    radj_n : nadj T;
    radj_ok : Is_true_s (nnormal radj_n)
  }.

Record rpadj (T : Type) : Type :=
  mk_rpadj {
    rpadj_n : nadj T;
    rpadj_ok : Is_true_s (nnormal rpadj_n && pnormal_raw (nraw rpadj_n))
  }.

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

Lemma radj_ok_true a : nnormal (radj_n a) = true.
Proof. apply Is_true_s_elim, radj_ok. Qed.

Lemma rpadj_nnormal ρ : nnormal (rpadj_n ρ) = true.
Proof. pose proof (Is_true_s_elim (rpadj_ok ρ)) as H; apply andb_true_iff in H; apply H. Qed.

Lemma rpadj_pnormal ρ : pnormal_raw (nraw (rpadj_n ρ)) = true.
Proof. pose proof (Is_true_s_elim (rpadj_ok ρ)) as H; apply andb_true_iff in H; apply H. Qed.

(** A payload adjustment is in particular an adjustment. *)
Definition rpadj_adj ρ : radj T :=
  mk_radj (rpadj_n ρ) (Is_true_s_intro (rpadj_nnormal ρ)).

(** The identity payload adjustment: a payload that is just its term. *)
Definition rpidentity : rpadj T := mk_rpadj nidentity (Is_true_s_intro eq_refl).

(** ** Action *)

(** Packaging a nested payload adjustment; only used on ones that are
    already normal, the fallback is never reached. *)
Definition psel (x : nadj T) : nadj T :=
  if nnormal x && pnormal_raw (nraw x) then x else nidentity.

Lemma psel_ok x : nnormal (psel x) && pnormal_raw (nraw (psel x)) = true.
Proof. unfold psel; destruct (nnormal x && pnormal_raw (nraw x)) eqn:E; [exact E|reflexivity]. Qed.

Definition rto_padj (x : nadj T) : rpadj T := mk_rpadj (psel x) (Is_true_s_intro (psel_ok x)).

Lemma rpadj_n_to_padj x :
  nnormal x = true -> pnormal_raw (nraw x) = true -> rpadj_n (rto_padj x) = x.
Proof. intros H1 H2; cbn; unfold psel; rewrite H1, H2; reflexivity. Qed.

Lemma rto_padj_padj_n ρ : rto_padj (rpadj_n ρ) = ρ.
Proof. apply rpadj_eq, rpadj_n_to_padj; [apply rpadj_nnormal|apply rpadj_pnormal]. Qed.

Definition rresult : Type := (rvar + (T * rpadj T))%type.

Definition rapply a v : rresult :=
  match napply (radj_n a) v with
  | inl w => inl w
  | inr p => inr (fst p, rto_padj (snd p))
  end.

Definition lower (r : rresult) : rvar + (T * nadj T) :=
  match r with
  | inl w => inl w
  | inr p => inr (fst p, rpadj_n (snd p))
  end.

Lemma lower_inj r1 r2 : lower r1 = lower r2 -> r1 = r2.
Proof.
  destruct r1 as [w1|[u1 ρ1]], r2 as [w2|[u2 ρ2]]; cbn; intros H; try discriminate;
    injection H; intros; subst; [reflexivity|].
  f_equal; f_equal; apply rpadj_eq; assumption.
Qed.

Lemma lower_rapply a v : lower (rapply a v) = napply (radj_n a) v.
Proof.
  unfold rapply; destruct (napply (radj_n a) v) as [w|[u x]] eqn:E; [reflexivity|].
  cbn [lower fst snd]; pose proof (napply_payload _ _ _ (radj_ok_true a) E) as [H1 H2].
  rewrite rpadj_n_to_padj by assumption; reflexivity.
Qed.

(** Adjustments are equal when they act the same. *)
Theorem rextensionality a b : (forall v, rapply a v = rapply b v) -> a = b.
Proof.
  intros H; apply radj_eq, nextensionality; try apply radj_ok_true.
  intros v; rewrite <- !lower_rapply, H; reflexivity.
Qed.

(** ** Identity and composition *)

Definition ridentity : radj T := mk_radj nidentity (Is_true_s_intro nnormal_identity).

Lemma rapply_identity v : rapply ridentity v = inl v.
Proof. apply lower_inj; rewrite lower_rapply; apply napply_identity. Qed.

(** [rpcompose a ρ]: the payload adjustment [a ∘ ρ]. *)
Lemma rpcompose_ok a ρ :
  nnormal (prestrict (ncompose (radj_n a) (rpadj_n ρ)))
  && pnormal_raw (nraw (prestrict (ncompose (radj_n a) (rpadj_n ρ)))) = true.
Proof.
  apply andb_true_iff, nnormal_prestrict, nnormal_ncompose;
    [apply radj_ok_true|apply rpadj_nnormal].
Qed.

Definition rpcompose a ρ : rpadj T :=
  mk_rpadj (prestrict (ncompose (radj_n a) (rpadj_n ρ))) (Is_true_s_intro (rpcompose_ok a ρ)).

(** [rcompose a b] first applies [b] and then [a]. *)
Definition rcompose a b : radj T :=
  mk_radj (ncompose (radj_n a) (radj_n b))
    (Is_true_s_intro (nnormal_ncompose _ _ (radj_ok_true a) (radj_ok_true b))).

Theorem rapply_compose a b v :
  rapply (rcompose a b) v
  = match rapply b v with
    | inl w => rapply a w
    | inr p => inr (fst p, rpcompose a (snd p))
    end.
Proof.
  apply lower_inj; rewrite lower_rapply; cbn [radj_n rcompose].
  rewrite napply_ncompose by apply radj_ok_true.
  rewrite <- (lower_rapply b v); destruct (rapply b v) as [w|[u ρ]]; cbn.
  - symmetry; apply lower_rapply.
  - reflexivity.
Qed.

Theorem rcompose_identity_l b : rcompose ridentity b = b.
Proof. apply radj_eq, ncompose_identity_l, radj_ok_true. Qed.

Theorem rcompose_identity_r a : rcompose a ridentity = a.
Proof. apply radj_eq, ncompose_identity_r, radj_ok_true. Qed.

Theorem rcompose_assoc a b c : rcompose a (rcompose b c) = rcompose (rcompose a b) c.
Proof. apply radj_eq, ncompose_assoc; apply radj_ok_true. Qed.

Theorem rpcompose_identity ρ : rpcompose ridentity ρ = ρ.
Proof.
  apply rpadj_eq; cbn [rpcompose rpadj_n radj_n ridentity].
  rewrite ncompose_identity_l by apply rpadj_nnormal.
  apply prestrict_pnormal; [apply rpadj_nnormal|apply rpadj_pnormal].
Qed.

Theorem rpcompose_compose a b ρ : rpcompose a (rpcompose b ρ) = rpcompose (rcompose a b) ρ.
Proof.
  apply rpadj_eq; cbn [rpcompose rpadj_n radj_n rcompose].
  rewrite prestrict_ncompose_prestrict;
    [|apply radj_ok_true|apply nnormal_ncompose; [apply radj_ok_true|apply rpadj_nnormal]].
  rewrite ncompose_assoc; [reflexivity|apply radj_ok_true|apply radj_ok_true|apply rpadj_nnormal].
Qed.

(** ** Output entries: [rpush_outer h a] is [a] followed by weakening past
    one new outer [h]. *)

Definition rpush_outer h a : radj T :=
  mk_radj (npush_outer h (radj_n a)) (Is_true_s_intro (nnormal_npush_outer h _ (radj_ok_true a))).

Lemma rpshift_ok h ρ :
  nnormal (pshift h (rpadj_n ρ)) && pnormal_raw (nraw (pshift h (rpadj_n ρ))) = true.
Proof.
  apply andb_true_iff; split;
    [apply nnormal_pshift, rpadj_nnormal|apply pnormal_pshift'; [apply rpadj_nnormal|apply rpadj_pnormal]].
Qed.

(** Weakening a payload adjustment past a new outer [h]. *)
Definition rpshift h ρ : rpadj T := mk_rpadj (pshift h (rpadj_n ρ)) (Is_true_s_intro (rpshift_ok h ρ)).

Theorem rapply_push_outer h a v :
  rapply (rpush_outer h a) v
  = match rapply a v with
    | inl w => inl (shift_rvar (mk_rvar h 0) w)
    | inr p => inr (fst p, rpshift h (snd p))
    end.
Proof.
  apply lower_inj; rewrite lower_rapply; cbn [radj_n rpush_outer].
  rewrite napply_npush_outer by apply (nnormal_normal _ (radj_ok_true a)).
  rewrite <- (lower_rapply a v); destruct (rapply a v) as [w|[u ρ]]; reflexivity.
Qed.

(** ** Input entries: [rpush_inner h t a] sends the innermost [h] to [t] and
    passes everything else to [a].  A variable target may be any variable. *)

Inductive rtarget : Type :=
| RRename (w : rvar)
| RBind (u : T) (ρ : rpadj T).

Definition rtarget_result (t : rtarget) : rresult :=
  match t with
  | RRename w => inl w
  | RBind u ρ => inr (u, ρ)
  end.

Definition rpush_inner_n h t a : nadj T :=
  match t with
  | RRename w => npush_inner_var h w (radj_n a)
  | RBind u ρ => npush_inner h (Slots.Bind (u, rpadj_n ρ)) (radj_n a)
  end.

Lemma rpush_inner_n_ok h t a : nnormal (rpush_inner_n h t a) = true.
Proof.
  destruct t as [w|u ρ]; cbn [rpush_inner_n].
  - apply nnormal_npush_inner_var, radj_ok_true.
  - apply nnormal_npush_inner; [apply radj_ok_true|discriminate|].
    cbn; rewrite rpadj_nnormal, rpadj_pnormal; reflexivity.
Qed.

Definition rpush_inner h t a : radj T :=
  mk_radj (rpush_inner_n h t a) (Is_true_s_intro (rpush_inner_n_ok h t a)).

Theorem rapply_push_inner h t a v :
  rapply (rpush_inner h t a) v
  = if rvar_eqb v (mk_rvar h 0) then rtarget_result t
    else rapply a (unshift_rvar (mk_rvar h 0) v).
Proof.
  apply lower_inj; rewrite lower_rapply; cbn [radj_n rpush_inner].
  pose proof (radj_ok_true a) as Ha.
  destruct t as [w|u ρ]; cbn [rpush_inner_n].
  - rewrite napply_npush_inner_var by exact Ha.
    destruct (rvar_eqb v (mk_rvar h 0)); [reflexivity|symmetry; apply lower_rapply].
  - rewrite napply_npush_inner by (try discriminate; exact Ha).
    destruct (rvar_eqb v (mk_rvar h 0)); [reflexivity|symmetry; apply lower_rapply].
Qed.

(** The number of [h] output slots of [a]'s canonical form. *)
Definition rout_count a h : nat := Slots.count (nraw (radj_n a)) h.

(** ** Going under a binder *)

(** [rlift h a] is [a] moved under a binder labelled [h]. *)
Definition rlift h a : radj T := rpush_inner h (RRename (mk_rvar h 0)) (rpush_outer h a).

Theorem rapply_lift h a v :
  rapply (rlift h a) v
  = if rvar_eqb v (mk_rvar h 0) then inl v
    else match rapply a (unshift_rvar (mk_rvar h 0) v) with
         | inl w => inl (shift_rvar (mk_rvar h 0) w)
         | inr p => inr (fst p, rpshift h (snd p))
         end.
Proof.
  unfold rlift; rewrite rapply_push_inner, rapply_push_outer.
  destruct (rvar_eqb_spec v (mk_rvar h 0)) as [->|]; reflexivity.
Qed.

(** ** Nesting depth

    Term-level operations recurse into payloads; these bounds justify that
    recursion. *)

Definition rdepth a : nat := ndepth (radj_n a).

Lemma rdepth_payload a v u ρ : rapply a v = inr (u, ρ) -> ndepth (rpadj_n ρ) < rdepth a.
Proof.
  intros H; pose proof (f_equal lower H) as H'; rewrite lower_rapply in H'; cbn [lower fst snd] in H'.
  unfold rdepth; destruct (radj_n a) as [m] eqn:E.
  apply (ndepth_binds m (u, rpadj_n ρ)), (Slots.binds_in_apply m v), H'.
Qed.

Lemma rdepth_push_outer h a : rdepth (rpush_outer h a) <= rdepth a.
Proof. apply ndepth_npush_outer. Qed.

Lemma rdepth_lift h a : rdepth (rlift h a) <= rdepth a.
Proof.
  unfold rdepth, rlift; cbn [radj_n rpush_inner rpush_inner_n].
  pose proof (ndepth_npush_inner_var h (mk_rvar h 0) (radj_n (rpush_outer h a))).
  pose proof (rdepth_push_outer h a); unfold rdepth in *; lia.
Qed.

Lemma rdepth_padj ρ : rdepth (rpadj_adj ρ) = ndepth (rpadj_n ρ).
Proof. reflexivity. Qed.

End Adjustment.

Arguments rtarget T : clear implicits.
Arguments rresult T : clear implicits.
