(** * Indexed adjustments: the public layer

    [adj T N M] is an adjustment from [N] to [M] bound variables: an
    adjustment with an SProp proof that it is scoped.  Equality is Leibniz,
    and two scoped adjustments are equal exactly when they agree on the
    variables in scope ([extensionality]).

    Users write and see adjustments as context forms [⟦ I ⇒ O | σ ⟧] (see
    "Context forms" below), composed with [∘]; [⟦⟧] is the identity.
    [weaken], [extend], [lift] and their named variants ([weaken_free x],
    ...) are abbreviations for one-entry context forms.  Bound and named
    labels have separate syntax ([·] and a [label]), so users never see
    [option label]. *)

From Stdlib Require Import Arith List Lia Bool StrictProp String.
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

(** The primitive entries, from which the context forms below are built:
    an output entry for the bound label or a named one, and an input entry
    for the bound label or a named one. *)
Definition out_bound {N M} (a : adj T N M) : adj T N (S M) :=
  mk_adj (rpush_outer None (adj_raw a)) (Is_true_s_intro (scoped_push_outer_none N M _ (adj_scoped a))).

Definition out_free {N M} (x : label) (a : adj T N M) : adj T N M :=
  mk_adj (rpush_outer (Some x) (adj_raw a))
    (Is_true_s_intro (scoped_push_outer_some x N M _ (adj_scoped a))).

Definition in_bound {N M} (t : target T M) (a : adj T N M) : adj T (S N) M :=
  mk_adj (rpush_inner None (to_target t) (adj_raw a))
    (Is_true_s_intro (scoped_push_inner_none N M _ _ (adj_scoped a) (to_target_wf t))).

Definition in_free {N M} (x : label) (t : target T M) (a : adj T N M) : adj T N M :=
  mk_adj (rpush_inner (Some x) (to_target t) (adj_raw a))
    (Is_true_s_intro (scoped_push_inner_some x N M _ _ (adj_scoped a) (to_target_wf t))).

(** Payload adjustments are moved through scoped adjustments. *)
Definition pcompose {M K} (a : adj T M K) (ρ : padj T M) : padj T K :=
  mk_padj (rpcompose (adj_raw a) (padj_raw ρ))
    (Is_true_s_intro (pscoped_pcompose M K _ _ (adj_scoped a) (Is_true_s_elim (padj_ok ρ)))).

End Indexed.

(** ** Context forms

    The adjustments users write and see are context forms
    [⟦ I ⇒ O | σ ⟧]: an input context [I] over an output context [O] over a
    tail adjustment [σ] (omitted when it is the identity).  The output context declares slots, each with an
    identifier and a label ([a : y], or [a : ·] for the bound label); the
    input context sends each input ([x], or [·]) either to a variable ([x
    as v], where [v] is a slot or any other variable of the output scope)
    or to a term ([x := u]).  Both contexts are written outermost first,
    so their last entries are the innermost ones.

    Slots are bound variables: [ctx σ o] binds the innermost slot first,
    and passes each slot's variable in the final output scope. *)

Section Context.

Context {T : Type}.

(** Shifting a variable past a new innermost bound or named output. *)
Lemma vshift_bound_ok {M} (v : var M) : Is_true_s (wf_var (S M) (shift_rvar (mk_rvar None 0) (var_raw v))).
Proof.
  apply Is_true_s_intro; pose proof (Is_true_s_elim (var_ok v)) as H.
  destruct v as [[[y|] i] Hv]; unfold shift_rvar, wf_var in *; cbn in *; [reflexivity|].
  apply Nat.ltb_lt in H; apply Nat.ltb_lt; lia.
Qed.

Lemma vshift_free_ok {M} y (v : var M) : Is_true_s (wf_var M (shift_rvar (mk_rvar (Some y) 0) (var_raw v))).
Proof.
  apply Is_true_s_intro; pose proof (Is_true_s_elim (var_ok v)) as H.
  destruct v as [[[x|] i] Hv]; unfold shift_rvar, wf_var in *; cbn in *;
    [destruct (String.eqb y x && _); reflexivity|exact H].
Qed.

Definition vshift_bound {M} (v : var M) : var (S M) := mk_var _ (vshift_bound_ok v).
Definition vshift_free {M} (y : label) (v : var M) : var M := mk_var _ (vshift_free_ok y v).

(** Input contexts over a tail with [Nt] inputs, into the output scope
    [M]; the last entry is the innermost. *)
Inductive ictx (Nt M : nat) : nat -> Type :=
| IEnd : ictx Nt M Nt
| IInB {N} (r : ictx Nt M N) (t : target T M) : ictx Nt M (S N)
| IInF {N} (r : ictx Nt M N) (x : label) (t : target T M) : ictx Nt M N.

(** Output contexts, innermost slot first, ending in the input context;
    the index is the output scope still to be built down to the tail's
    [Mt]. *)
Inductive octx (Nt Mt N M : nat) : nat -> Type :=
| OEnd (i : ictx Nt M N) : octx Nt Mt N M Mt
| OOutB {J} (k : var M -> octx Nt Mt N M J) : octx Nt Mt N M (S J)
| OOutF {J} (y : label) (k : var M -> octx Nt Mt N M J) : octx Nt Mt N M J.

Arguments IEnd {Nt M}.
Arguments IInB {Nt M N} r t.
Arguments IInF {Nt M N} r x t.
Arguments OEnd {Nt Mt N M} i.
Arguments OOutB {Nt Mt N M J} k.
Arguments OOutF {Nt Mt N M J} y k.

Fixpoint iden {Nt M N} (i : ictx Nt M N) (X : adj T Nt M) : adj T N M :=
  match i with
  | IEnd => X
  | IInB r t => in_bound t (iden r X)
  | IInF r x t => in_free x t (iden r X)
  end.

(** [sh] takes the variables of the scope [J] reached so far to the final
    output scope. *)
Fixpoint oden {Nt Mt N M J} (o : octx Nt Mt N M J)
  : (var J -> var M) -> ictx Nt M N * (adj T Nt Mt -> adj T Nt J) :=
  match o in octx _ _ _ _ J return (var J -> var M) -> ictx Nt M N * (adj T Nt Mt -> adj T Nt J) with
  | OEnd i => fun _ => (i, fun σ => σ)
  | OOutB k => fun sh =>
      let p := oden (k (sh bvar0)) (fun v => sh (vshift_bound v)) in (fst p, fun σ => out_bound (snd p σ))
  | OOutF y k => fun sh =>
      let p := oden (k (sh (fvar y 0))) (fun v => sh (vshift_free y v)) in (fst p, fun σ => out_free y (snd p σ))
  end.

Definition ctx {Nt Mt N M} (σ : adj T Nt Mt) (o : octx Nt Mt N M M) : adj T N M :=
  let p := oden o (fun v => v) in iden (fst p) (snd p σ).

End Context.

Arguments IEnd {T Nt M}.
Arguments IInB {T Nt M N} r t.
Arguments IInF {T Nt M N} r x t.
Arguments OEnd {T Nt Mt N M} i.
Arguments OOutB {T Nt Mt N M J} k.
Arguments OOutF {T Nt Mt N M J} y k.

(** *** Notation *)

Declare Custom Entry adj_in.
Declare Custom Entry adj_out.

(** Input contexts: a list of entries, outermost first. *)
Notation "i , x '↦' t" := (IInF i x t)
  (in custom adj_in at level 2, left associativity, x constr at level 0, t constr at level 0).
Notation "i , '·' '↦' t" := (IInB i t) (in custom adj_in at level 2, left associativity, t constr at level 0).
Notation "i , x 'as' v" := (IInF i x (Rename v)) (in custom adj_in at level 2, left associativity, x constr at level 0, v constr at level 0).
Notation "i , '·' 'as' v" := (IInB i (Rename v)) (in custom adj_in at level 2, left associativity, v constr at level 0).
Notation "i , x ':=' u" := (IInF i x (Bind u)) (in custom adj_in at level 2, left associativity, x constr at level 0, u constr at level 0).
Notation "i , '·' ':=' u" := (IInB i (Bind u)) (in custom adj_in at level 2, left associativity, u constr at level 0).
Notation "x '↦' t" := (IInF IEnd x t) (in custom adj_in at level 1, x constr at level 0, t constr at level 0).
Notation "'·' '↦' t" := (IInB IEnd t) (in custom adj_in at level 1, t constr at level 0).
Notation "x 'as' v" := (IInF IEnd x (Rename v)) (in custom adj_in at level 1, x constr at level 0, v constr at level 0).
Notation "'·' 'as' v" := (IInB IEnd (Rename v)) (in custom adj_in at level 1, v constr at level 0).
Notation "x ':=' u" := (IInF IEnd x (Bind u)) (in custom adj_in at level 1, x constr at level 0, u constr at level 0).
Notation "'·' ':=' u" := (IInB IEnd (Bind u)) (in custom adj_in at level 1, u constr at level 0).

(** Output contexts: the input context, [⇒], then the slots, outermost
    first. *)
Notation "o , a : y" := (OOutF y (fun a => o))
  (in custom adj_out at level 4, left associativity, a name, y constr at level 0).
Notation "o , a : '·'" := (OOutB (fun a => o)) (in custom adj_out at level 4, left associativity, a name).
Notation "'⇒'" := (OEnd IEnd) (in custom adj_out at level 3).
Notation "i '⇒'" := (OEnd i) (in custom adj_out at level 3, i custom adj_in at level 2).
Notation "'⇒' a : y" := (OOutF y (fun a => OEnd IEnd)) (in custom adj_out at level 3, a name, y constr at level 0).
Notation "'⇒' a : '·'" := (OOutB (fun a => OEnd IEnd)) (in custom adj_out at level 3, a name).
Notation "i '⇒' a : y" := (OOutF y (fun a => OEnd i))
  (in custom adj_out at level 3, i custom adj_in at level 2, a name, y constr at level 0).
Notation "i '⇒' a : '·'" := (OOutB (fun a => OEnd i)) (in custom adj_out at level 3, i custom adj_in at level 2, a name).

Notation "⟦ o | σ ⟧" := (ctx σ o) (o custom adj_out at level 4, σ constr at level 99, format "⟦  o  |  σ  ⟧").
Notation "⟦ o ⟧" := (ctx identity o) (o custom adj_out at level 4, format "⟦  o  ⟧").
Notation "⟦ ⟧" := identity (format "⟦ ⟧").

Declare Scope adj_scope.
Delimit Scope adj_scope with adj.
Bind Scope adj_scope with adj.
Notation "a ∘ b" := (compose a b) (at level 40, left associativity) : adj_scope.
Global Open Scope adj_scope.

(** The constructors, as context forms. *)
Notation weaken a := (ctx a (OOutB (fun _ => OEnd IEnd))) (only parsing).
Notation weaken_free x a := (ctx a (OOutF x (fun _ => OEnd IEnd))) (only parsing).
Notation extend t a := (ctx a (OEnd (IInB IEnd t))) (only parsing).
Notation extend_free x t a := (ctx a (OEnd (IInF IEnd x t))) (only parsing).
Notation lift a := (ctx a (OOutB (fun b => OEnd (IInB IEnd (Rename b))))) (only parsing).
Notation lift_free x a := (ctx a (OOutF x (fun b => OEnd (IInF IEnd x (Rename b))))) (only parsing).

Section Laws.

Context {T : Type}.

Lemma adj_raw_lift {N M} (a : adj T N M) : adj_raw (lift a) = rlift None (adj_raw a).
Proof. reflexivity. Qed.

Lemma adj_raw_lift_free {N M} x (a : adj T N M) : adj_raw (lift_free x a) = rlift (Some x) (adj_raw a).
Proof. reflexivity. Qed.

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

Theorem lift_identity {N} : lift (@identity T N) = identity.
Proof. apply adj_eq; rewrite adj_raw_lift; apply rlift_identity. Qed.

Theorem lift_compose {N M K} (a : adj T M K) (b : adj T N M) :
  compose (lift a) (lift b) = lift (compose a b).
Proof. apply adj_eq; cbn [adj_raw compose]; rewrite !adj_raw_lift; apply rlift_compose. Qed.

Theorem lift_free_compose {N M K} x (a : adj T M K) (b : adj T N M) :
  compose (lift_free x a) (lift_free x b) = lift_free x (compose a b).
Proof. apply adj_eq; cbn [adj_raw compose]; rewrite !adj_raw_lift_free; apply rlift_compose. Qed.

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
Proof. apply adj_eq; rewrite adj_raw_lift; cbn; apply lift_closed, (adj_scoped a). Qed.

Theorem at_scope_compose {N} (a b : adj T 0 0) :
  compose (@at_scope N a) (at_scope b) = at_scope (compose a b).
Proof. apply adj_eq; reflexivity. Qed.

End Laws.

