(** * Adjustments

    An [adjustment T] is a normal nested adjustment (Nested.v) packaged with
    an SProp proof of normality.  [T] is the user's type of terms with no
    bound variables; the library never looks inside it.

    Because the proof is in SProp, two adjustments are equal exactly when
    their data is equal, and by canonicity that happens exactly when they
    act the same ([extensionality]).  So all the usual laws hold up to
    Leibniz equality.

    A variable is sent either to a variable or to a payload [(u, ρ)]: a term
    [u] together with a payload adjustment [ρ : padj T] that is still to be
    applied to it.  Payload adjustments only ever see the free variables of
    [u], and are canonical for that restricted meaning. *)

From Stdlib Require Import PArith Arith List Lia Bool StrictProp.
From ShiftedNames.Core Require Import Trie Label Var Nested.
From ShiftedNames.Core Require Slots.
Import ListNotations.

(** ** Booleans as strict propositions *)

Definition Is_true_s (b : bool) : SProp := if b then sUnit else sEmpty.

Definition Is_true_s_intro {b : bool} : b = true -> Is_true_s b :=
  match b with
  | true => fun _ => stt
  | false => fun H => match diff_false_true H with end
  end.

Lemma Is_true_s_elim {b : bool} : Is_true_s b -> b = true.
Proof. destruct b; [reflexivity|intros []]. Qed.

(** ** The types of adjustments and payload adjustments *)

Record adjustment (T : Type) : Type :=
  mk_adj {
    adj_n : nadj T;
    adj_ok : Is_true_s (nnormal adj_n)
  }.

Record padj (T : Type) : Type :=
  mk_padj {
    padj_n : nadj T;
    padj_ok : Is_true_s (nnormal padj_n && pnormal_raw (nraw padj_n))
  }.

Arguments mk_adj {T} _ _.
Arguments adj_n {T} _.
Arguments adj_ok {T} _.
Arguments mk_padj {T} _ _.
Arguments padj_n {T} _.
Arguments padj_ok {T} _.

Lemma adj_eq {T} (a b : adjustment T) : adj_n a = adj_n b -> a = b.
Proof. destruct a as [ra Ha], b as [rb Hb]; cbn; intros ->; reflexivity. Qed.

Lemma padj_eq {T} (a b : padj T) : padj_n a = padj_n b -> a = b.
Proof. destruct a as [ra Ha], b as [rb Hb]; cbn; intros ->; reflexivity. Qed.

Section Adjustment.

Context {T : Type}.

Implicit Types (a b c : adjustment T) (ρ : padj T) (v w : var) (h l : option label).

Lemma adj_ok_true a : nnormal (adj_n a) = true.
Proof. apply Is_true_s_elim, adj_ok. Qed.

Lemma padj_nnormal ρ : nnormal (padj_n ρ) = true.
Proof. pose proof (Is_true_s_elim (padj_ok ρ)) as H; apply andb_true_iff in H; apply H. Qed.

Lemma padj_pnormal ρ : pnormal_raw (nraw (padj_n ρ)) = true.
Proof. pose proof (Is_true_s_elim (padj_ok ρ)) as H; apply andb_true_iff in H; apply H. Qed.

(** A payload adjustment is in particular an adjustment. *)
Definition padj_adj ρ : adjustment T :=
  mk_adj (padj_n ρ) (Is_true_s_intro (padj_nnormal ρ)).

(** ** Action *)

(** Packaging a nested payload adjustment; only used on ones that are
    already normal, the fallback is never reached. *)
Definition psel (x : nadj T) : nadj T :=
  if nnormal x && pnormal_raw (nraw x) then x else nidentity.

Lemma psel_ok x : nnormal (psel x) && pnormal_raw (nraw (psel x)) = true.
Proof. unfold psel; destruct (nnormal x && pnormal_raw (nraw x)) eqn:E; [exact E|reflexivity]. Qed.

Definition to_padj (x : nadj T) : padj T := mk_padj (psel x) (Is_true_s_intro (psel_ok x)).

Lemma padj_n_to_padj x :
  nnormal x = true -> pnormal_raw (nraw x) = true -> padj_n (to_padj x) = x.
Proof. intros H1 H2; cbn; unfold psel; rewrite H1, H2; reflexivity. Qed.

Lemma to_padj_padj_n ρ : to_padj (padj_n ρ) = ρ.
Proof. apply padj_eq, padj_n_to_padj; [apply padj_nnormal|apply padj_pnormal]. Qed.

Definition result : Type := (var + (T * padj T))%type.

Definition apply a v : result :=
  match napply (adj_n a) v with
  | inl w => inl w
  | inr p => inr (fst p, to_padj (snd p))
  end.

Definition lower (r : result) : var + (T * nadj T) :=
  match r with
  | inl w => inl w
  | inr p => inr (fst p, padj_n (snd p))
  end.

Lemma lower_inj r1 r2 : lower r1 = lower r2 -> r1 = r2.
Proof.
  destruct r1 as [w1|[u1 ρ1]], r2 as [w2|[u2 ρ2]]; cbn; intros H; try discriminate;
    injection H; intros; subst; [reflexivity|].
  f_equal; f_equal; apply padj_eq; assumption.
Qed.

Lemma lower_apply a v : lower (apply a v) = napply (adj_n a) v.
Proof.
  unfold apply; destruct (napply (adj_n a) v) as [w|[u x]] eqn:E; [reflexivity|].
  cbn [lower fst snd]; pose proof (napply_payload _ _ _ (adj_ok_true a) E) as [H1 H2].
  rewrite padj_n_to_padj by assumption; reflexivity.
Qed.

(** Adjustments are equal when they act the same. *)
Theorem extensionality a b : (forall v, apply a v = apply b v) -> a = b.
Proof.
  intros H; apply adj_eq, nextensionality; try apply adj_ok_true.
  intros v; rewrite <- !lower_apply, H; reflexivity.
Qed.

(** ** Identity and composition *)

Definition identity : adjustment T := mk_adj nidentity (Is_true_s_intro nnormal_identity).

Lemma apply_identity v : apply identity v = inl v.
Proof. apply lower_inj; rewrite lower_apply; apply napply_identity. Qed.

(** [pcompose a ρ]: the payload adjustment [a ∘ ρ]. *)
Lemma pcompose_ok a ρ :
  nnormal (prestrict (ncompose (adj_n a) (padj_n ρ)))
  && pnormal_raw (nraw (prestrict (ncompose (adj_n a) (padj_n ρ)))) = true.
Proof.
  apply andb_true_iff, nnormal_prestrict, nnormal_ncompose;
    [apply adj_ok_true|apply padj_nnormal].
Qed.

Definition pcompose a ρ : padj T :=
  mk_padj (prestrict (ncompose (adj_n a) (padj_n ρ))) (Is_true_s_intro (pcompose_ok a ρ)).

(** [compose a b] first applies [b] and then [a]. *)
Definition compose a b : adjustment T :=
  mk_adj (ncompose (adj_n a) (adj_n b))
    (Is_true_s_intro (nnormal_ncompose _ _ (adj_ok_true a) (adj_ok_true b))).

Theorem apply_compose a b v :
  apply (compose a b) v
  = match apply b v with
    | inl w => apply a w
    | inr p => inr (fst p, pcompose a (snd p))
    end.
Proof.
  apply lower_inj; rewrite lower_apply; cbn [adj_n compose].
  rewrite napply_ncompose by apply adj_ok_true.
  rewrite <- (lower_apply b v); destruct (apply b v) as [w|[u ρ]]; cbn.
  - symmetry; apply lower_apply.
  - reflexivity.
Qed.

Theorem compose_identity_l b : compose identity b = b.
Proof. apply adj_eq, ncompose_identity_l, adj_ok_true. Qed.

Theorem compose_identity_r a : compose a identity = a.
Proof. apply adj_eq, ncompose_identity_r, adj_ok_true. Qed.

Theorem compose_assoc a b c : compose a (compose b c) = compose (compose a b) c.
Proof. apply adj_eq, ncompose_assoc; apply adj_ok_true. Qed.

Theorem pcompose_identity ρ : pcompose identity ρ = ρ.
Proof.
  apply padj_eq; cbn [pcompose padj_n adj_n identity].
  rewrite ncompose_identity_l by apply padj_nnormal.
  apply prestrict_pnormal; [apply padj_nnormal|apply padj_pnormal].
Qed.

Theorem pcompose_compose a b ρ : pcompose a (pcompose b ρ) = pcompose (compose a b) ρ.
Proof.
  apply padj_eq; cbn [pcompose padj_n adj_n compose].
  rewrite prestrict_ncompose_prestrict;
    [|apply adj_ok_true|apply nnormal_ncompose; [apply adj_ok_true|apply padj_nnormal]].
  rewrite ncompose_assoc; [reflexivity|apply adj_ok_true|apply adj_ok_true|apply padj_nnormal].
Qed.

(** ** Output entries: [push_outer h a] is [a] followed by weakening past
    one new outer [h]. *)

Definition push_outer h a : adjustment T :=
  mk_adj (npush_outer h (adj_n a)) (Is_true_s_intro (nnormal_npush_outer h _ (adj_ok_true a))).

Lemma pshift_ok h ρ :
  nnormal (pshift h (padj_n ρ)) && pnormal_raw (nraw (pshift h (padj_n ρ))) = true.
Proof.
  apply andb_true_iff; split;
    [apply nnormal_pshift, padj_nnormal|apply pnormal_pshift'; [apply padj_nnormal|apply padj_pnormal]].
Qed.

(** Weakening a payload adjustment past a new outer [h]. *)
Definition pshift_p h ρ : padj T := mk_padj (pshift h (padj_n ρ)) (Is_true_s_intro (pshift_ok h ρ)).

Theorem apply_push_outer h a v :
  apply (push_outer h a) v
  = match apply a v with
    | inl w => inl (shift_var (mk_var h 0) w)
    | inr p => inr (fst p, pshift_p h (snd p))
    end.
Proof.
  apply lower_inj; rewrite lower_apply; cbn [adj_n push_outer].
  rewrite napply_npush_outer by apply (nnormal_normal _ (adj_ok_true a)).
  rewrite <- (lower_apply a v); destruct (apply a v) as [w|[u ρ]]; reflexivity.
Qed.

(** ** Input entries: [push_inner h t a] sends the innermost [h] to [t] and
    passes everything else to [a].  A variable target may be any variable. *)

Inductive target : Type :=
| Rename (w : var)
| Bind (u : T) (ρ : padj T).

Definition target_result (t : target) : result :=
  match t with
  | Rename w => inl w
  | Bind u ρ => inr (u, ρ)
  end.

Definition push_inner_n h t a : nadj T :=
  match t with
  | Rename w => npush_inner_var h w (adj_n a)
  | Bind u ρ => npush_inner h (Slots.Bind (u, padj_n ρ)) (adj_n a)
  end.

Lemma push_inner_n_ok h t a : nnormal (push_inner_n h t a) = true.
Proof.
  destruct t as [w|u ρ]; cbn [push_inner_n].
  - apply nnormal_npush_inner_var, adj_ok_true.
  - apply nnormal_npush_inner; [apply adj_ok_true|discriminate|].
    cbn; rewrite padj_nnormal, padj_pnormal; reflexivity.
Qed.

Definition push_inner h t a : adjustment T :=
  mk_adj (push_inner_n h t a) (Is_true_s_intro (push_inner_n_ok h t a)).

Theorem apply_push_inner h t a v :
  apply (push_inner h t a) v
  = if var_eqb v (mk_var h 0) then target_result t
    else apply a (unshift_var (mk_var h 0) v).
Proof.
  apply lower_inj; rewrite lower_apply; cbn [adj_n push_inner].
  pose proof (nnormal_normal _ (adj_ok_true a)) as Ha.
  destruct t as [w|u ρ]; cbn [push_inner_n].
  - rewrite napply_npush_inner_var by exact Ha.
    destruct (var_eqb v (mk_var h 0)); [reflexivity|symmetry; apply lower_apply].
  - rewrite napply_npush_inner by (try discriminate; exact Ha).
    destruct (var_eqb v (mk_var h 0)); [reflexivity|symmetry; apply lower_apply].
Qed.

(** The number of [h] output slots of [a]'s canonical form. *)
Definition out_count a h : nat := Slots.count (nraw (adj_n a)) h.

(** ** Going under a binder *)

(** [lift h a] is [a] moved under a binder labelled [h]. *)
Definition lift h a : adjustment T := push_inner h (Rename (mk_var h 0)) (push_outer h a).

Theorem apply_lift h a v :
  apply (lift h a) v
  = if var_eqb v (mk_var h 0) then inl v
    else match apply a (unshift_var (mk_var h 0) v) with
         | inl w => inl (shift_var (mk_var h 0) w)
         | inr p => inr (fst p, pshift_p h (snd p))
         end.
Proof.
  unfold lift; rewrite apply_push_inner, apply_push_outer.
  destruct (var_eqb_spec v (mk_var h 0)) as [->|]; reflexivity.
Qed.

End Adjustment.

Arguments target T : clear implicits.
Arguments result T : clear implicits.
