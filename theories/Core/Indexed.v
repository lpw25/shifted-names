(** * Indexed adjustments: the public layer

    [adj T N M] is an adjustment from [N] to [M] bound variables: an
    adjustment with an SProp proof that it is scoped.  Equality is Leibniz,
    and two scoped adjustments are equal exactly when they agree on the
    variables in scope ([extensionality]).

    The constructors are the context-form ones, with their effect on the
    indices:
    - [identity : adj N N];
    - [compose : adj M K -> adj N M -> adj N K];
    - [weaken] adds an output bound variable, [weaken_free x] an output [x];
    - [extend t] adds an input bound variable sent to [t], [extend_free x t] an
      input [x];
    - [lift] goes under a bound binder, [lift_free x] under an [x] one. *)

From Stdlib Require Import Arith List Lia Bool StrictProp.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Scoped.

(** ** Scoped variables, payload adjustments and targets *)

Record var (M : nat) : Type :=
  mk_var { var_raw : rvar; var_ok : Is_true_s (wf_var M var_raw) }.

Arguments mk_var {M} _ _.
Arguments var_raw {M} _.
Arguments var_ok {M} _.

Lemma var_eq {M} (v w : var M) : var_raw v = var_raw w -> v = w.
Proof. destruct v, w; cbn; intros ->; reflexivity. Qed.

(** The [i]-th bound variable, and the free name [x₍ᵢ₎]. *)
Definition bvar {M} (i : nat) (H : Is_true_s (Nat.ltb i M)) : var M := @mk_var M (mk_rvar None i) H.
Definition bvar0 {M} : var (S M) := @mk_var (S M) (mk_rvar None 0) stt.
Definition fvar {M} (x : label) (i : nat) : var M := @mk_var M (mk_rvar (Some x) i) stt.

Record padj (T : Type) (M : nat) : Type :=
  mk_padj { padj_raw : rpadj T; padj_ok : Is_true_s (pscoped M padj_raw) }.

Arguments mk_padj {T M} _ _.
Arguments padj_raw {T M} _.
Arguments padj_ok {T M} _.

Lemma padj_eq {T M} (ρ1 ρ2 : padj T M) : padj_raw ρ1 = padj_raw ρ2 -> ρ1 = ρ2.
Proof. destruct ρ1, ρ2; cbn; intros ->; reflexivity. Qed.

(** Where an input goes: a variable, or a closed term.  (Payloads with a
    pending adjustment arise inside the library, never from users.) *)
Inductive target (T : Type) (M : nat) : Type :=
| Rename (w : var M)
| Bind (u : T).

Arguments Rename {T M} _.
Arguments Bind {T M} _.

Definition to_target {T M} (t : target T M) : rtarget T :=
  match t with
  | Rename w => RRename (var_raw w)
  | Bind u => RBind u rpidentity
  end.

Lemma to_target_wf {T M} (t : target T M) : result_wf M (rtarget_result (to_target t)) = true.
Proof.
  destruct t as [w|u]; cbn [to_target rtarget_result].
  - rewrite result_wf_inl; apply Is_true_s_elim, var_ok.
  - rewrite result_wf_inr; reflexivity.
Qed.

(** ** Scoped adjustments *)

Record adj (T : Type) (N M : nat) : Type :=
  mk_adj { adj_raw : radj T; adj_ok : Is_true_s (scoped N M adj_raw) }.

Arguments mk_adj {T N M} _ _.
Arguments adj_raw {T N M} _.
Arguments adj_ok {T N M} _.

Lemma adj_eq {T N M} (a b : adj T N M) : adj_raw a = adj_raw b -> a = b.
Proof. destruct a, b; cbn; intros ->; reflexivity. Qed.

Section Indexed.

Context {T : Type}.

Lemma adj_scoped {N M} (a : adj T N M) : scoped N M (adj_raw a) = true.
Proof. apply Is_true_s_elim, adj_ok. Qed.

Definition apply {N M} (a : adj T N M) (v : var N) : rresult T := rapply (adj_raw a) (var_raw v).

Theorem apply_wf {N M} (a : adj T N M) (v : var N) : result_wf M (apply a v) = true.
Proof.
  apply (proj2 (proj1 (scoped_spec N M (adj_raw a)) (adj_scoped a))), Is_true_s_elim, var_ok.
Qed.

(** Scoped adjustments are equal when they agree on the variables in
    scope. *)
Theorem extensionality {N M} (a b : adj T N M) : (forall v : var N, apply a v = apply b v) -> a = b.
Proof.
  intros H; apply adj_eq, (scoped_ext N M); try apply adj_scoped.
  intros v Hv; apply (H (mk_var v (Is_true_s_intro Hv))).
Qed.

Definition identity {N} : adj T N N := mk_adj ridentity (Is_true_s_intro (scoped_identity N)).

Definition compose {N M K} (a : adj T M K) (b : adj T N M) : adj T N K :=
  mk_adj (rcompose (adj_raw a) (adj_raw b))
    (Is_true_s_intro (scoped_compose N M K _ _ (adj_scoped a) (adj_scoped b))).

Definition weaken {N M} (a : adj T N M) : adj T N (S M) :=
  mk_adj (rpush_outer None (adj_raw a)) (Is_true_s_intro (scoped_push_outer_none N M _ (adj_scoped a))).

Definition weaken_free {N M} (x : label) (a : adj T N M) : adj T N M :=
  mk_adj (rpush_outer (Some x) (adj_raw a))
    (Is_true_s_intro (scoped_push_outer_some x N M _ (adj_scoped a))).

Definition extend {N M} (t : target T M) (a : adj T N M) : adj T (S N) M :=
  mk_adj (rpush_inner None (to_target t) (adj_raw a))
    (Is_true_s_intro (scoped_push_inner_none N M _ _ (adj_scoped a) (to_target_wf t))).

Definition extend_free {N M} (x : label) (t : target T M) (a : adj T N M) : adj T N M :=
  mk_adj (rpush_inner (Some x) (to_target t) (adj_raw a))
    (Is_true_s_intro (scoped_push_inner_some x N M _ _ (adj_scoped a) (to_target_wf t))).

Definition lift {N M} (a : adj T N M) : adj T (S N) (S M) :=
  mk_adj (rlift None (adj_raw a)) (Is_true_s_intro (scoped_lift_none N M _ (adj_scoped a))).

Definition lift_free {N M} (x : label) (a : adj T N M) : adj T N M :=
  mk_adj (rlift (Some x) (adj_raw a)) (Is_true_s_intro (scoped_lift_some x N M _ (adj_scoped a))).

(** Payload adjustments are moved through scoped adjustments. *)
Definition pcompose {M K} (a : adj T M K) (ρ : padj T M) : padj T K :=
  mk_padj (rpcompose (adj_raw a) (padj_raw ρ))
    (Is_true_s_intro (pscoped_pcompose M K _ _ (adj_scoped a) (Is_true_s_elim (padj_ok ρ)))).

(** ** Laws *)

Theorem compose_identity_l {N M} (a : adj T N M) : compose identity a = a.
Proof. apply adj_eq, rcompose_identity_l. Qed.

Theorem compose_identity_r {N M} (a : adj T N M) : compose a identity = a.
Proof. apply adj_eq, rcompose_identity_r. Qed.

Theorem compose_assoc {N M K L} (a : adj T K L) (b : adj T M K) (c : adj T N M) :
  compose a (compose b c) = compose (compose a b) c.
Proof. apply adj_eq, rcompose_assoc. Qed.

Theorem pcompose_compose {M K L} (a : adj T K L) (b : adj T M K) (ρ : padj T M) :
  pcompose a (pcompose b ρ) = pcompose (compose a b) ρ.
Proof. apply padj_eq, rpcompose_compose. Qed.

Theorem lift_identity {N} : lift (@identity N) = identity.
Proof. apply adj_eq, rlift_identity. Qed.

Theorem lift_compose {N M K} (a : adj T M K) (b : adj T N M) :
  compose (lift a) (lift b) = lift (compose a b).
Proof. apply adj_eq, rlift_compose. Qed.

Theorem lift_free_compose {N M K} x (a : adj T M K) (b : adj T N M) :
  compose (lift_free x a) (lift_free x b) = lift_free x (compose a b).
Proof. apply adj_eq, rlift_compose. Qed.

Theorem compose_weaken_l {N M K} (a : adj T M K) (b : adj T N M) :
  compose (weaken a) b = weaken (compose a b).
Proof. apply adj_eq, rcompose_push_outer_l. Qed.

Theorem compose_weaken_free_l {N M K} x (a : adj T M K) (b : adj T N M) :
  compose (weaken_free x a) b = weaken_free x (compose a b).
Proof. apply adj_eq, rcompose_push_outer_l. Qed.

(** An output entry is cancelled by an input entry with the same label. *)
Theorem compose_cancel {N M K} (t : target T K) (a : adj T M K) (b : adj T N M) :
  compose (extend t a) (weaken b) = compose a b.
Proof. apply adj_eq, rcompose_cancel. Qed.

Theorem compose_cancel_free {N M K} x (t : target T K) (a : adj T M K) (b : adj T N M) :
  compose (extend_free x t a) (weaken_free x b) = compose a b.
Proof. apply adj_eq, rcompose_cancel. Qed.

Theorem lift_as_context {N M} (a : adj T N M) : lift a = extend (Rename bvar0) (weaken a).
Proof. reflexivity. Qed.

(** ** Closed adjustments

    An adjustment from no bound variables to none can be used at any scope
    with unchanged data, and going under a binder leaves it unchanged. *)

Definition at_scope {N} (a : adj T 0 0) : adj T N N :=
  mk_adj (adj_raw a) (Is_true_s_intro (scoped_closed N _ (adj_scoped a))).

Theorem lift_at_scope {N} (a : adj T 0 0) : lift (@at_scope N a) = @at_scope (S N) a.
Proof. apply adj_eq; cbn; apply lift_closed, (adj_scoped a). Qed.

Theorem at_scope_compose {N} (a b : adj T 0 0) :
  compose (@at_scope N a) (at_scope b) = at_scope (compose a b).
Proof. apply adj_eq; reflexivity. Qed.

End Indexed.
