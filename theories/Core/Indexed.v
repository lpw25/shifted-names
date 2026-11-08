(** * Indexed adjustments: the public layer

    [sadj T N M] is an adjustment from [N] to [M] bound variables: an
    adjustment with an SProp proof that it is scoped.  Equality is Leibniz,
    and two scoped adjustments are equal exactly when they agree on the
    variables in scope ([sext]).

    The constructors are the context-form ones, with their effect on the
    indices:
    - [sid : sadj N N];
    - [scompose : sadj M K -> sadj N M -> sadj N K];
    - [sweaken] adds an output bound variable, [sweaken_free x] an output [x];
    - [scons t] adds an input bound variable sent to [t], [scons_free x t] an
      input [x];
    - [slift] goes under a bound binder, [slift_free x] under an [x] one. *)

From Stdlib Require Import Arith List Lia Bool StrictProp.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Scoped.

(** ** Scoped variables, payload adjustments and targets *)

Record svar (M : nat) : Type :=
  mk_svar { sv : var; sv_ok : Is_true_s (wf_var M sv) }.

Arguments mk_svar {M} _ _.
Arguments sv {M} _.
Arguments sv_ok {M} _.

Lemma svar_eq {M} (v w : svar M) : sv v = sv w -> v = w.
Proof. destruct v, w; cbn; intros ->; reflexivity. Qed.

(** The [i]-th bound variable, and the free name [x₍ᵢ₎]. *)
Definition sbvar {M} (i : nat) (H : Is_true_s (Nat.ltb i M)) : svar M := @mk_svar M (mk_var None i) H.
Definition sbvar0 {M} : svar (S M) := @mk_svar (S M) (mk_var None 0) stt.
Definition sfvar {M} (x : label) (i : nat) : svar M := @mk_svar M (mk_var (Some x) i) stt.

Record spadj (T : Type) (M : nat) : Type :=
  mk_spadj { sp : padj T; sp_ok : Is_true_s (pscoped M sp) }.

Arguments mk_spadj {T M} _ _.
Arguments sp {T M} _.
Arguments sp_ok {T M} _.

Lemma spadj_eq {T M} (ρ1 ρ2 : spadj T M) : sp ρ1 = sp ρ2 -> ρ1 = ρ2.
Proof. destruct ρ1, ρ2; cbn; intros ->; reflexivity. Qed.

Inductive starget (T : Type) (M : nat) : Type :=
| SRename (w : svar M)
| SBind (u : T) (ρ : spadj T M).

Arguments SRename {T M} _.
Arguments SBind {T M} _ _.

Definition to_target {T M} (t : starget T M) : target T :=
  match t with
  | SRename w => Rename (sv w)
  | SBind u ρ => Bind u (sp ρ)
  end.

Lemma to_target_wf {T M} (t : starget T M) : result_wf M (target_result (to_target t)) = true.
Proof.
  destruct t as [w|u ρ]; cbn [to_target target_result].
  - rewrite result_wf_inl; apply Is_true_s_elim, sv_ok.
  - rewrite result_wf_inr; apply Is_true_s_elim, sp_ok.
Qed.

(** ** Scoped adjustments *)

Record sadj (T : Type) (N M : nat) : Type :=
  mk_sadj { sa : adjustment T; sa_ok : Is_true_s (scoped N M sa) }.

Arguments mk_sadj {T N M} _ _.
Arguments sa {T N M} _.
Arguments sa_ok {T N M} _.

Lemma sadj_eq {T N M} (a b : sadj T N M) : sa a = sa b -> a = b.
Proof. destruct a, b; cbn; intros ->; reflexivity. Qed.

Section Indexed.

Context {T : Type}.

Lemma sa_scoped {N M} (a : sadj T N M) : scoped N M (sa a) = true.
Proof. apply Is_true_s_elim, sa_ok. Qed.

Definition sapply {N M} (a : sadj T N M) (v : svar N) : result T := apply (sa a) (sv v).

Theorem sapply_wf {N M} (a : sadj T N M) (v : svar N) : result_wf M (sapply a v) = true.
Proof.
  apply (proj2 (proj1 (scoped_spec N M (sa a)) (sa_scoped a))), Is_true_s_elim, sv_ok.
Qed.

(** Scoped adjustments are equal when they agree on the variables in
    scope. *)
Theorem sext {N M} (a b : sadj T N M) : (forall v : svar N, sapply a v = sapply b v) -> a = b.
Proof.
  intros H; apply sadj_eq, (scoped_ext N M); try apply sa_scoped.
  intros v Hv; apply (H (mk_svar v (Is_true_s_intro Hv))).
Qed.

Definition sid {N} : sadj T N N := mk_sadj identity (Is_true_s_intro (scoped_identity N)).

Definition scompose {N M K} (a : sadj T M K) (b : sadj T N M) : sadj T N K :=
  mk_sadj (compose (sa a) (sa b))
    (Is_true_s_intro (scoped_compose N M K _ _ (sa_scoped a) (sa_scoped b))).

Definition sweaken {N M} (a : sadj T N M) : sadj T N (S M) :=
  mk_sadj (push_outer None (sa a)) (Is_true_s_intro (scoped_push_outer_none N M _ (sa_scoped a))).

Definition sweaken_free {N M} (x : label) (a : sadj T N M) : sadj T N M :=
  mk_sadj (push_outer (Some x) (sa a))
    (Is_true_s_intro (scoped_push_outer_some x N M _ (sa_scoped a))).

Definition scons {N M} (t : starget T M) (a : sadj T N M) : sadj T (S N) M :=
  mk_sadj (push_inner None (to_target t) (sa a))
    (Is_true_s_intro (scoped_push_inner_none N M _ _ (sa_scoped a) (to_target_wf t))).

Definition scons_free {N M} (x : label) (t : starget T M) (a : sadj T N M) : sadj T N M :=
  mk_sadj (push_inner (Some x) (to_target t) (sa a))
    (Is_true_s_intro (scoped_push_inner_some x N M _ _ (sa_scoped a) (to_target_wf t))).

Definition slift {N M} (a : sadj T N M) : sadj T (S N) (S M) :=
  mk_sadj (lift None (sa a)) (Is_true_s_intro (scoped_lift_none N M _ (sa_scoped a))).

Definition slift_free {N M} (x : label) (a : sadj T N M) : sadj T N M :=
  mk_sadj (lift (Some x) (sa a)) (Is_true_s_intro (scoped_lift_some x N M _ (sa_scoped a))).

(** Payload adjustments are moved through scoped adjustments. *)
Definition spcompose {M K} (a : sadj T M K) (ρ : spadj T M) : spadj T K :=
  mk_spadj (pcompose (sa a) (sp ρ))
    (Is_true_s_intro (pscoped_pcompose M K _ _ (sa_scoped a) (Is_true_s_elim (sp_ok ρ)))).

(** ** Laws *)

Theorem scompose_sid_l {N M} (a : sadj T N M) : scompose sid a = a.
Proof. apply sadj_eq, compose_identity_l. Qed.

Theorem scompose_sid_r {N M} (a : sadj T N M) : scompose a sid = a.
Proof. apply sadj_eq, compose_identity_r. Qed.

Theorem scompose_assoc {N M K L} (a : sadj T K L) (b : sadj T M K) (c : sadj T N M) :
  scompose a (scompose b c) = scompose (scompose a b) c.
Proof. apply sadj_eq, compose_assoc. Qed.

Theorem spcompose_compose {M K L} (a : sadj T K L) (b : sadj T M K) (ρ : spadj T M) :
  spcompose a (spcompose b ρ) = spcompose (scompose a b) ρ.
Proof. apply spadj_eq, pcompose_compose. Qed.

Theorem slift_sid {N} : slift (@sid N) = sid.
Proof. apply sadj_eq, lift_identity. Qed.

Theorem slift_compose {N M K} (a : sadj T M K) (b : sadj T N M) :
  scompose (slift a) (slift b) = slift (scompose a b).
Proof. apply sadj_eq, lift_compose. Qed.

Theorem slift_free_compose {N M K} x (a : sadj T M K) (b : sadj T N M) :
  scompose (slift_free x a) (slift_free x b) = slift_free x (scompose a b).
Proof. apply sadj_eq, lift_compose. Qed.

Theorem scompose_weaken_l {N M K} (a : sadj T M K) (b : sadj T N M) :
  scompose (sweaken a) b = sweaken (scompose a b).
Proof. apply sadj_eq, compose_push_outer_l. Qed.

Theorem scompose_weaken_free_l {N M K} x (a : sadj T M K) (b : sadj T N M) :
  scompose (sweaken_free x a) b = sweaken_free x (scompose a b).
Proof. apply sadj_eq, compose_push_outer_l. Qed.

(** An output entry is cancelled by an input entry with the same label. *)
Theorem scompose_cancel {N M K} (t : starget T K) (a : sadj T M K) (b : sadj T N M) :
  scompose (scons t a) (sweaken b) = scompose a b.
Proof. apply sadj_eq, compose_cancel. Qed.

Theorem scompose_cancel_free {N M K} x (t : starget T K) (a : sadj T M K) (b : sadj T N M) :
  scompose (scons_free x t a) (sweaken_free x b) = scompose a b.
Proof. apply sadj_eq, compose_cancel. Qed.

Theorem slift_as_context {N M} (a : sadj T N M) : slift a = scons (SRename sbvar0) (sweaken a).
Proof. reflexivity. Qed.

(** ** Closed adjustments

    An adjustment from no bound variables to none can be used at any scope
    with unchanged data, and going under a binder leaves it unchanged. *)

Definition at_scope {N} (a : sadj T 0 0) : sadj T N N :=
  mk_sadj (sa a) (Is_true_s_intro (scoped_closed N _ (sa_scoped a))).

Theorem slift_at_scope {N} (a : sadj T 0 0) : slift (@at_scope N a) = @at_scope (S N) a.
Proof. apply sadj_eq; cbn; apply lift_closed, (sa_scoped a). Qed.

Theorem at_scope_compose {N} (a b : sadj T 0 0) :
  scompose (@at_scope N a) (at_scope b) = at_scope (scompose a b).
Proof. apply sadj_eq; reflexivity. Qed.

End Indexed.
