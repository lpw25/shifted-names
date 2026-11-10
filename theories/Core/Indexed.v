(** * Indexed adjustments: the public layer

    [adj T N M] is an adjustment from [N] to [M] bound variables: an
    adjustment with an SProp proof that it is scoped.  Equality is Leibniz,
    and two scoped adjustments are equal exactly when they agree on the
    variables in scope ([extensionality]).

    Users write and see adjustments as context forms (see "Context forms"
    below), composed with [∘]; [⟦⟧] is the identity.  [lift σ] and
    [lift_free x σ] are abbreviations for [⟦ · | σ ⟧] and [⟦ x | σ ⟧].  Bound
    and named labels have separate syntax ([·] and a [label]), so users
    never see [option label]. *)

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

(** *** Notation for variables

    A named variable prints as its label with its index as a superscript:
    [x] for [x₀] (a label is coerced to its first variable), [x¹] to [x⁹],
    and [x ^ n] otherwise.  Bound variables are [·], [·¹], ..., [· ^ n]. *)

(** The scope of a bound variable is taken from where it is used, before
    its proof of being in scope is checked. *)
Arguments bvar {M} & i H.

Definition lvar {M} (x : label) : var M := fvar x 0.
Coercion lvar : label >-> var.

Declare Scope var_scope.
Delimit Scope var_scope with var.
Bind Scope var_scope with var.

Notation "x ¹" := (fvar x 1) (at level 1, format "x ¹") : var_scope.
Notation "'·' ¹" := (bvar 1 stt) (only parsing) : var_scope.
Notation "'·' ¹" := (bvar 1 _) (only printing, format "· ¹") : var_scope.
Notation "x ²" := (fvar x 2) (at level 1, format "x ²") : var_scope.
Notation "'·' ²" := (bvar 2 stt) (only parsing) : var_scope.
Notation "'·' ²" := (bvar 2 _) (only printing, format "· ²") : var_scope.
Notation "x ³" := (fvar x 3) (at level 1, format "x ³") : var_scope.
Notation "'·' ³" := (bvar 3 stt) (only parsing) : var_scope.
Notation "'·' ³" := (bvar 3 _) (only printing, format "· ³") : var_scope.
Notation "x ⁴" := (fvar x 4) (at level 1, format "x ⁴") : var_scope.
Notation "'·' ⁴" := (bvar 4 stt) (only parsing) : var_scope.
Notation "'·' ⁴" := (bvar 4 _) (only printing, format "· ⁴") : var_scope.
Notation "x ⁵" := (fvar x 5) (at level 1, format "x ⁵") : var_scope.
Notation "'·' ⁵" := (bvar 5 stt) (only parsing) : var_scope.
Notation "'·' ⁵" := (bvar 5 _) (only printing, format "· ⁵") : var_scope.
Notation "x ⁶" := (fvar x 6) (at level 1, format "x ⁶") : var_scope.
Notation "'·' ⁶" := (bvar 6 stt) (only parsing) : var_scope.
Notation "'·' ⁶" := (bvar 6 _) (only printing, format "· ⁶") : var_scope.
Notation "x ⁷" := (fvar x 7) (at level 1, format "x ⁷") : var_scope.
Notation "'·' ⁷" := (bvar 7 stt) (only parsing) : var_scope.
Notation "'·' ⁷" := (bvar 7 _) (only printing, format "· ⁷") : var_scope.
Notation "x ⁸" := (fvar x 8) (at level 1, format "x ⁸") : var_scope.
Notation "'·' ⁸" := (bvar 8 stt) (only parsing) : var_scope.
Notation "'·' ⁸" := (bvar 8 _) (only printing, format "· ⁸") : var_scope.
Notation "x ⁹" := (fvar x 9) (at level 1, format "x ⁹") : var_scope.
Notation "'·' ⁹" := (bvar 9 stt) (only parsing) : var_scope.
Notation "'·' ⁹" := (bvar 9 _) (only printing, format "· ⁹") : var_scope.
Notation "x ^ n" := (fvar x n) : var_scope.
Notation "x" := (fvar x 0) (only printing, at level 1, x at level 0) : var_scope.
Notation "'·' ^ n" := (bvar n _) (only printing, at level 30) : var_scope.
Notation "'·'" := bvar0 : var_scope.

Record padj (T : Type) (M : nat) : Type :=
  mk_padj { padj_raw : rpadj T; padj_ok : Is_true_s (pscoped M padj_raw) }.

Arguments mk_padj {T M} _ _.
Arguments padj_raw {T M} _.
Arguments padj_ok {T M} _.

Lemma padj_eq {T M} (ρ1 ρ2 : padj T M) : padj_raw ρ1 = padj_raw ρ2 -> ρ1 = ρ2.
Proof. destruct ρ1, ρ2; cbn; intros ->; reflexivity. Qed.

(** The identity payload adjustment: a term's named variables stay as
    they are. *)
Definition pid {T M} : padj T M := mk_padj rpidentity (Is_true_s_intro eq_refl).

(** Where an input goes: a variable, or a term [u] whose variables are
    moved by the payload adjustment [ρ]. *)
Inductive target (T : Type) (M : nat) : Type :=
| Rename (w : var M)
| Bind (u : T) (ρ : padj T M).

Arguments Rename {T M} _.
Arguments Bind {T M} _ _.

Definition to_target {T M} (t : target T M) : rtarget T :=
  match t with
  | Rename w => RRename (var_raw w)
  | Bind u ρ => RBind u (padj_raw ρ)
  end.

Lemma to_target_wf {T M} (t : target T M) : result_wf M (rtarget_result (to_target t)) = true.
Proof.
  destruct t as [w|u ρ]; cbn [to_target rtarget_result].
  - rewrite result_wf_inl; apply Is_true_s_elim, var_ok.
  - rewrite result_wf_inr; apply Is_true_s_elim, padj_ok.
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

(** Applying an adjustment to a variable: a variable or a term. *)
Definition apply_var {N M} (a : adj T N M) (v : var N) : target T M :=
  match apply a v as r return result_wf M r = true -> target T M with
  | inl w => fun H => Rename (mk_var w (Is_true_s_intro H))
  | inr (u, ρ) => fun H => Bind u (mk_padj ρ (Is_true_s_intro H))
  end (apply_wf a v).

(** What a variable becomes, given what to make of a variable and of a
    term with its payload adjustment: the node [names] evaluates. *)
Definition eval {N M R} (f : var M -> R) (g : padj T M -> T -> R) (a : adj T N M) (v : var N) : R :=
  match apply_var a v with Rename w => f w | Bind u ρ => g ρ u end.

Lemma eval_rename {N M R} f g (a : adj T N M) v w : apply_var a v = Rename w -> @eval N M R f g a v = f w.
Proof. unfold eval; intros ->; reflexivity. Qed.

Lemma eval_bind {N M R} f g (a : adj T N M) v u ρ : apply_var a v = Bind u ρ -> @eval N M R f g a v = g ρ u.
Proof. unfold eval; intros ->; reflexivity. Qed.

Lemma apply_var_rename {N M} (a : adj T N M) (v : var N) (w : var M) :
  rapply (adj_raw a) (var_raw v) = inl (var_raw w) -> apply_var a v = Rename w.
Proof.
  unfold apply_var; generalize (apply_wf a v); unfold apply; intros H E.
  revert H; rewrite E; intros H; f_equal; apply var_eq; reflexivity.
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

Lemma apply_var_bind {N M K} (a : adj T N M) (v : var N) (u : T) (b : adj T K M) (ρ : padj T K) :
  rapply (adj_raw a) (var_raw v) = inr (u, rpcompose (adj_raw b) (padj_raw ρ)) ->
  apply_var a v = Bind u (pcompose b ρ).
Proof.
  unfold apply_var; generalize (apply_wf a v); unfold apply; intros H E.
  revert H; rewrite E; intros H; f_equal; apply padj_eq; reflexivity.
Qed.

End Indexed.

(** ** Context forms

    Users write and see adjustments as context forms.

    - The full form [⟦ I \ O ⟧], or [⟦ I | Γ \ O | Γ[σ] ⟧] with a tail.
      [I] is the input context, innermost entry first: an input ([x], or
      [·] for the bound label) is sent to a variable ([x as v]), to a term
      ([x := u]), or, written alone, to the output in the same position
      among the outputs written alone.  [O] is the output context,
      innermost first: [y as a] declares a slot [a] that inputs refer to,
      and [y] alone a positional slot.  The tail [Γ] names the rest of the
      input context; [Γ[σ]] (or just [Γ]) is the rest of the output
      context, the adjustment [σ] applied to it.  Without them the tail is
      the identity.
    - The short form [⟦ I ⟧], or [⟦ I | σ ⟧] with a tail: an input
      written alone is a lift (the label in both contexts, linked), [x :=
      u] a substitution.  [⟦ · | σ ⟧] lifts [σ] under a binder, [⟦ x := u
      ⟧] substitutes [u] for [x], [⟦ · := u ⟧] instantiates.

    Variables [v] in [x as v] are in the output scope; terms [u] in [x :=
    u] are in the scope of the output tail, and are shifted past the
    output context's slots. *)

(** A slot of an output context of [K] entries: a position in it. *)
Record slot (K : nat) : Type := mk_slot { slot_ix : nat; slot_ok : Is_true_s (Nat.ltb slot_ix K) }.

Arguments slot_ix {K} _.

(** The name of a tail. *)
Inductive tname : Type := tname_tt.

Section Context.

Context {T : Type}.

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

(** Shifting a variable past a new innermost bound or named output. *)
Definition vshift_bound {M} (v : var M) : var (S M) := mk_var _ (vshift_bound_ok v).
Definition vshift_free {M} (y : label) (v : var M) : var M := mk_var _ (vshift_free_ok y v).

(** *** Payload contexts

    [u⟨ P ⟩]: where the free names of a substituted term go.  [P] is an
    input context with no outputs of its own: [x as c] sends [u]'s [x₀] to
    the slot [c], [x := u'⟨ … ⟩] substitutes; the other names of [u] go
    to the output tail, past the slots. *)
Inductive pctx (K : nat) : Type :=
| PEmpty
| PRen (p : pctx K) (x : label) (c : slot K)
| PSub (p : pctx K) (x : label) (u : T) (q : pctx K).

Arguments PEmpty {K}.
Arguments PRen {K} p x c.
Arguments PSub {K} p x u q.

(** The payload adjustment of [P], with slots read by [f], over [wk], the
    weakening from the output tail past the slots. *)
Fixpoint pctx_den {K L J} (p : pctx K) (f : slot K -> var J) (wk : adj T L J) : adj T L J :=
  match p with
  | PEmpty => wk
  | PRen p x c => pctx_den p f (in_free x (Rename (f c)) wk)
  | PSub p x u q => pctx_den p f (in_free x (Bind u (pcompose (pctx_den q f wk) pid)) wk)
  end.

Definition pctx_pay {K L J} (p : pctx K) (f : slot K -> var J) (wk : adj T L J) : padj T J := pcompose (pctx_den p f wk) pid.

Definition vdummy {M} : var M := fvar EmptyString 0.

(** *** The short form *)

(** [sctx Nb Mb N M] goes from a tail [adj Nb Mb] to [adj N M].  It
    declares no slots, so its payload contexts cannot name any: there are
    no slots of [slot 0]. *)
Inductive sctx : nat -> nat -> nat -> nat -> Type :=
| SEmpty {N M} : sctx N M N M
| SLiftF {Nb Mb N M} (s : sctx Nb Mb N M) (x : label) : sctx Nb Mb N M
| SLiftB {Nb Mb N M} (s : sctx (S Nb) (S Mb) N M) : sctx Nb Mb N M
| SSubF {Nb Mb N M} (s : sctx Nb Mb N M) (x : label) (u : T) (q : pctx 0) : sctx Nb Mb N M
| SSubB {Nb Mb N M} (s : sctx (S Nb) Mb N M) (u : T) (q : pctx 0) : sctx Nb Mb N M.

Inductive sclosed (N M : nat) : Type :=
| STail {Nb Mb} (s : sctx Nb Mb N M) (σ : adj T Nb Mb).

Arguments STail {N M Nb Mb} s σ.

Definition noslot {J} (c : slot 0) : var J := vdummy.

Fixpoint sctx_den {K Nb Mb N M} (s : sctx Nb Mb N M) : (unit -> adj T K Mb) -> adj T Nb Mb -> adj T N M :=
  match s in sctx Nb Mb N M return (unit -> adj T K Mb) -> adj T Nb Mb -> adj T N M with
  | SEmpty => fun _ X => X
  | SLiftF s x => fun wk X => sctx_den s (fun _ => out_free x (wk tt)) (in_free x (Rename (fvar x 0)) (out_free x X))
  | SLiftB s => fun wk X => sctx_den s (fun _ => out_bound (wk tt)) (in_bound (Rename bvar0) (out_bound X))
  | SSubF s x u q => fun wk X => sctx_den s wk (in_free x (Bind u (pctx_pay q noslot (wk tt))) X)
  | SSubB s u q => fun wk X => sctx_den s wk (in_bound (Bind u (pctx_pay q noslot (wk tt))) X)
  end.

(** *** The full form

    A slot is a position in the output context: [slot K] for an output
    context of [K] entries, innermost first.  The output context binds a
    name for each of its positions written [y as a], and input entries
    refer to slots by those names. *)

(** Input contexts, innermost entry first, built by adding entries on the
    outside: [ictx K M Nb N P] goes from a tail with [Nb] inputs to [N]
    inputs, into the output scope [M], with [K] slots and [P] positional
    entries. *)
Inductive ictx (K M : nat) : nat -> nat -> nat -> Type :=
| IEmpty {N} : ictx K M N N 0
| IPosF {Nb N P} (i : ictx K M Nb N P) (x : label) : ictx K M Nb N (S P)
| IPosB {Nb N P} (i : ictx K M (S Nb) N P) : ictx K M Nb N (S P)
| IRenF {Nb N P} (i : ictx K M Nb N P) (x : label) (c : slot K) : ictx K M Nb N P
| IRenB {Nb N P} (i : ictx K M (S Nb) N P) (c : slot K) : ictx K M Nb N P
| ISubF {Nb N P} (i : ictx K M Nb N P) (x : label) (u : T) (q : pctx K) : ictx K M Nb N P
| ISubB {Nb N P} (i : ictx K M (S Nb) N P) (u : T) (q : pctx K) : ictx K M Nb N P.

(** Output contexts, innermost entry first, over the input context: the
    indices are the positional outputs so far, the output scope at the
    outer edge of the entries so far, their number, and the tail name the
    input context uses, if any. *)
Inductive octx (K Nt N M P : nat) : nat -> nat -> nat -> option tname -> Type :=
| OEnd (i : ictx K M Nt N P) : octx K Nt N M P 0 M 0 None
| OEndT (g : tname) (i : ictx K M Nt N P) : octx K Nt N M P 0 M 0 (Some g)
| OPosF {Po J n b} (o : octx K Nt N M P Po J n b) (y : label) : octx K Nt N M P (S Po) J (S n) b
| OPosB {Po J n b} (o : octx K Nt N M P Po (S J) n b) : octx K Nt N M P (S Po) J (S n) b
| ONamF {Po J n b} (y : label) (k : slot K -> octx K Nt N M P Po J n b) : octx K Nt N M P Po J (S n) b
| ONamB {Po J n b} (k : slot K -> octx K Nt N M P Po (S J) n b) : octx K Nt N M P Po J (S n) b
| OShort (s : sctx Nt Nt N M) : octx K Nt N M P 0 Nt 0 None
| OShortT (c : sclosed N M) : octx K Nt N M P 0 Nt 0 None.

Arguments IEmpty {K M N}.
Arguments IPosF {K M Nb N P} i x.
Arguments IPosB {K M Nb N P} i.
Arguments IRenF {K M Nb N P} i x c.
Arguments IRenB {K M Nb N P} i c.
Arguments ISubF {K M Nb N P} i x u q.
Arguments ISubB {K M Nb N P} i u q.
Arguments OEnd {K Nt N M P} i.
Arguments OEndT {K Nt N M P} g i.
Arguments OPosF {K Nt N M P Po J n b} o y.
Arguments OPosB {K Nt N M P Po J n b} o.
Arguments ONamF {K Nt N M P Po J n b} y k.
Arguments ONamB {K Nt N M P Po J n b} k.
Arguments OShort {K Nt N M P} s.
Arguments OShortT {K Nt N M P} c.

(** The input context over [X], with [env] the variables of the slots and
    [pos] those of the positional ones, both innermost first, and [wk] the
    weakening of its terms past the slots. *)
Fixpoint ictx_den {K L M Nb N P} (i : ictx K M Nb N P) (env : list (var M))
  : list (var M) -> (unit -> adj T L M) -> adj T Nb M -> adj T N M :=
  let f (c : slot K) := nth (slot_ix c) env vdummy in
  match i in ictx _ _ Nb N P return list (var M) -> (unit -> adj T L M) -> adj T Nb M -> adj T N M with
  | IEmpty => fun _ _ X => X
  | @IPosF _ _ _ _ P i x => fun pos wk X => ictx_den i env pos wk (in_free x (Rename (nth P pos vdummy)) X)
  | @IPosB _ _ _ _ P i => fun pos wk X => ictx_den i env pos wk (in_bound (Rename (nth P pos vdummy)) X)
  | IRenF i x c => fun pos wk X => ictx_den i env pos wk (in_free x (Rename (f c)) X)
  | IRenB i c => fun pos wk X => ictx_den i env pos wk (in_bound (Rename (f c)) X)
  | ISubF i x u q => fun pos wk X => ictx_den i env pos wk (in_free x (Bind u (pctx_pay q f (wk tt))) X)
  | ISubB i u q => fun pos wk X => ictx_den i env pos wk (in_bound (Bind u (pctx_pay q f (wk tt))) X)
  end.

(** The slot at position [n] of an output context of [K] entries. *)
Definition slot_at {K n} (H : S n <= K) : slot K := mk_slot K n (Is_true_s_intro (proj2 (Nat.ltb_lt n K) H)).

(** Where the entries inside [o] take a variable at its outer edge. *)
Fixpoint octx_probe {K Nt N M P Po J n b} (o : octx K Nt N M P Po J n b) : n <= K -> var J -> var M :=
  match o in octx _ _ _ _ _ _ J n _ return n <= K -> var J -> var M with
  | OEnd _ | OEndT _ _ => fun _ v => v
  | OPosF o y => fun H v => octx_probe o (Nat.lt_le_incl _ _ H) (vshift_free y v)
  | OPosB o => fun H v => octx_probe o (Nat.lt_le_incl _ _ H) (vshift_bound v)
  | ONamF y k => fun H v => octx_probe (k (slot_at H)) (Nat.lt_le_incl _ _ H) (vshift_free y v)
  | ONamB k => fun H v => octx_probe (k (slot_at H)) (Nat.lt_le_incl _ _ H) (vshift_bound v)
  | OShort _ | OShortT _ => fun _ _ => vdummy
  end.

(** The entries from the outermost in, over [X]: [env] collects the
    variables of the slots, [pos] those of the positional ones, and [wk]
    weakens past the entries so far. *)
Fixpoint octx_den {K L Nt N M P Po J n b} (o : octx K Nt N M P Po J n b)
  : n <= K -> list (var M) -> list (var M) -> (unit -> adj T L J) -> adj T Nt J -> adj T N M :=
  match o in octx _ _ _ _ _ _ J n _
        return n <= K -> list (var M) -> list (var M) -> (unit -> adj T L J) -> adj T Nt J -> adj T N M with
  | OEnd i | OEndT _ i => fun _ env pos wk X => ictx_den i env pos wk X
  | OPosF o y => fun H env pos wk X =>
      let a := octx_probe o (Nat.lt_le_incl _ _ H) (fvar y 0) in
      octx_den o (Nat.lt_le_incl _ _ H) (a :: env) (a :: pos) (fun _ => out_free y (wk tt)) (out_free y X)
  | OPosB o => fun H env pos wk X =>
      let a := octx_probe o (Nat.lt_le_incl _ _ H) bvar0 in
      octx_den o (Nat.lt_le_incl _ _ H) (a :: env) (a :: pos) (fun _ => out_bound (wk tt)) (out_bound X)
  | ONamF y k => fun H env pos wk X =>
      let o := k (slot_at H) in
      let a := octx_probe o (Nat.lt_le_incl _ _ H) (fvar y 0) in
      octx_den o (Nat.lt_le_incl _ _ H) (a :: env) pos (fun _ => out_free y (wk tt)) (out_free y X)
  | ONamB k => fun H env pos wk X =>
      let o := k (slot_at H) in
      let a := octx_probe o (Nat.lt_le_incl _ _ H) bvar0 in
      octx_den o (Nat.lt_le_incl _ _ H) (a :: env) pos (fun _ => out_bound (wk tt)) (out_bound X)
  | OShort s => fun _ _ _ _ X => sctx_den s (fun _ => identity) X
  | OShortT (STail s σ) => fun _ _ _ _ _ => sctx_den s (fun _ => identity) σ
  end.

Definition cform_id {K Nt N M P} (o : octx K Nt N M P P Nt K None) : adj T N M :=
  octx_den o (le_n K) nil nil (fun _ => @identity T Nt) identity.

(** With a tail: the output context's type records the tail name the
    input context used, which must be the one bound here. *)
Definition cform {K Nt Mt N M P} (o : forall g : tname, octx K Nt N M P P Mt K (Some g)) (σ : adj T Nt Mt) : adj T N M :=
  octx_den (o tname_tt) (le_n K) nil nil (fun _ => @identity T Mt) σ.

End Context.

Arguments PEmpty {T K}.
Arguments PRen {T K} p x c.
Arguments PSub {T K} p x u q.
Arguments IEmpty {T K M N}.
Arguments IPosF {T K M Nb N P} i x.
Arguments IPosB {T K M Nb N P} i.
Arguments IRenF {T K M Nb N P} i x c.
Arguments IRenB {T K M Nb N P} i c.
Arguments ISubF {T K M Nb N P} i x u q.
Arguments ISubB {T K M Nb N P} i u q.
Arguments OEnd {T K Nt N M P} i.
Arguments OEndT {T K Nt N M P} g i.
Arguments OPosF {T K Nt N M P Po J n b} o y.
Arguments OPosB {T K Nt N M P Po J n b} o.
Arguments ONamF {T K Nt N M P Po J n b} y k.
Arguments ONamB {T K Nt N M P Po J n b} k.
Arguments OShort {T K Nt N M P} s.
Arguments OShortT {T K Nt N M P} c.
Arguments SEmpty {T N M}.
Arguments SLiftF {T Nb Mb N M} s x.
Arguments SLiftB {T Nb Mb N M} s.
Arguments SSubF {T Nb Mb N M} s x u q.
Arguments SSubB {T Nb Mb N M} s u q.
Arguments STail {T N M Nb Mb} s σ.

(** *** Entries shared by both forms

    The input entries are written the same way in both forms; which form
    they build is decided by the type expected of them: an output context
    after [\] expects a full-form input context, and a context form with
    no [\] a short-form one. *)

Class CNil (C : Type) := cnil : C.
Class CEnt (C R : Type) := cent : C -> label -> R.
Class CBnd (C R : Type) := cbnd : C -> R.
Class CSub (T : Type) (K : nat) (C R : Type) := csub : C -> label -> T -> @pctx T K -> R.
Class CSubB (T : Type) (K : nat) (C R : Type) := csubb : C -> T -> @pctx T K -> R.
#[export] Instance cnil_full {T K M N} : CNil (@ictx T K M N N 0) := IEmpty.
#[export] Instance cnil_short {T N M} : CNil (@sctx T N M N M) := SEmpty.
#[export] Instance cent_full {T K M Nb N P} : CEnt (@ictx T K M Nb N P) (ictx K M Nb N (S P)) := IPosF.
#[export] Instance cent_short {T Nb Mb N M} : CEnt (@sctx T Nb Mb N M) (sctx Nb Mb N M) := SLiftF.
#[export] Instance cbnd_full {T K M Nb N P} : CBnd (@ictx T K M (S Nb) N P) (ictx K M Nb N (S P)) := IPosB.
#[export] Instance cbnd_short {T Nb Mb N M} : CBnd (@sctx T (S Nb) (S Mb) N M) (sctx Nb Mb N M) := SLiftB.
#[export] Instance csub_full {T K M Nb N P} : CSub T K (@ictx T K M Nb N P) (ictx K M Nb N P) := ISubF.
#[export] Instance csub_short {T Nb Mb N M} : CSub T 0 (@sctx T Nb Mb N M) (sctx Nb Mb N M) := SSubF.
#[export] Instance csubb_full {T K M Nb N P} : CSubB T K (@ictx T K M (S Nb) N P) (ictx K M Nb N P) := ISubB.
#[export] Instance csubb_short {T Nb Mb N M} : CSubB T 0 (@sctx T (S Nb) Mb N M) (sctx Nb Mb N M) := SSubB.
(** *** Notation *)

Declare Custom Entry adj_pay.
Declare Custom Entry adj_in.
Declare Custom Entry adj_out.

(** Printing the constructors themselves, as [names] builds them. *)
Notation "i ; x" := (IPosF i x) (only printing, in custom adj_in at level 2, left associativity, x constr at level 0).
Notation "i ; '·'" := (IPosB i) (only printing, in custom adj_in at level 2, left associativity).
Notation "i ; x ':=' u" := (ISubF i x u PEmpty) (only printing, in custom adj_in at level 2, left associativity, x constr at level 0, u constr at level 0).
Notation "i ; x ':=' u '⟨' p '⟩'" := (ISubF i x u p) (only printing, in custom adj_in at level 2, left associativity, x constr at level 0, u constr at level 0, p custom adj_pay at level 2).
Notation "i ; '·' ':=' u" := (ISubB i u PEmpty) (only printing, in custom adj_in at level 2, left associativity, u constr at level 0).
Notation "i ; '·' ':=' u '⟨' p '⟩'" := (ISubB i u p) (only printing, in custom adj_in at level 2, left associativity, u constr at level 0, p custom adj_pay at level 2).
Notation "x" := (IPosF IEmpty x) (only printing, in custom adj_in at level 1, x constr at level 0).
Notation "'·'" := (IPosB IEmpty) (only printing, in custom adj_in at level 1).
Notation "x 'as' v" := (IRenF IEmpty x v) (only printing, in custom adj_in at level 1, x constr at level 0, v constr at level 0).
Notation "'·' 'as' v" := (IRenB IEmpty v) (only printing, in custom adj_in at level 1, v constr at level 0).
Notation "x ':=' u" := (ISubF IEmpty x u PEmpty) (only printing, in custom adj_in at level 1, x constr at level 0, u constr at level 0).
Notation "x ':=' u '⟨' p '⟩'" := (ISubF IEmpty x u p) (only printing, in custom adj_in at level 1, x constr at level 0, u constr at level 0, p custom adj_pay at level 2).
Notation "'·' ':=' u" := (ISubB IEmpty u PEmpty) (only printing, in custom adj_in at level 1, u constr at level 0).
Notation "'·' ':=' u '⟨' p '⟩'" := (ISubB IEmpty u p) (only printing, in custom adj_in at level 1, u constr at level 0, p custom adj_pay at level 2).
Notation "i ; x" := (SLiftF i x) (only printing, in custom adj_in at level 2, left associativity, x constr at level 0).
Notation "i ; '·'" := (SLiftB i) (only printing, in custom adj_in at level 2, left associativity).
Notation "x" := (SLiftF SEmpty x) (only printing, in custom adj_in at level 1, x constr at level 0).
Notation "'·'" := (SLiftB SEmpty) (only printing, in custom adj_in at level 1).
Notation "i ; x ':=' u" := (SSubF i x u PEmpty) (only printing, in custom adj_in at level 2, left associativity, x constr at level 0, u constr at level 0).
Notation "i ; '·' ':=' u" := (SSubB i u PEmpty) (only printing, in custom adj_in at level 2, left associativity, u constr at level 0).
Notation "x ':=' u" := (SSubF SEmpty x u PEmpty) (only printing, in custom adj_in at level 1, x constr at level 0, u constr at level 0).
Notation "'·' ':=' u" := (SSubB SEmpty u PEmpty) (only printing, in custom adj_in at level 1, u constr at level 0).
Notation "i" := (OShort i) (only printing, in custom adj_out at level 3, i custom adj_in at level 2).
Notation "'\'" := (OEnd IEmpty) (only printing, in custom adj_out at level 3).
Notation "'\' y" := (OPosF (OEnd IEmpty) y) (only printing, in custom adj_out at level 3, y constr at level 0).
Notation "'\' y 'as' a" := (ONamF y (fun a => OEnd IEmpty)) (only printing, in custom adj_out at level 3, y constr at level 0, a name).
Notation "'\' '·'" := (OPosB (OEnd IEmpty)) (only printing, in custom adj_out at level 3).
Notation "'\' '·' 'as' a" := (ONamB (fun a => OEnd IEmpty)) (only printing, in custom adj_out at level 3, a name).
Notation "'|' g '\' y" := (OPosF (OEndT g IEmpty) y) (only printing, in custom adj_out at level 3, g constr at level 200, y constr at level 0).
Notation "'|' g '\' y 'as' a" := (ONamF y (fun a => OEndT g IEmpty)) (only printing, in custom adj_out at level 3, g constr at level 200, y constr at level 0, a name).
Notation "'|' g '\' '·'" := (OPosB (OEndT g IEmpty)) (only printing, in custom adj_out at level 3, g constr at level 200).
Notation "'|' g '\' '·' 'as' a" := (ONamB (fun a => OEndT g IEmpty)) (only printing, in custom adj_out at level 3, g constr at level 200, a name).
Notation "'|' g '\'" := (OEndT g IEmpty) (only printing, in custom adj_out at level 3, g constr at level 200).

(** Payload contexts. *)
Notation "p ; x 'as' c" := (PRen p x c) (in custom adj_pay at level 2, left associativity, x constr at level 0, c constr at level 0).
Notation "p ; x ':=' u" := (PSub p x u PEmpty) (in custom adj_pay at level 2, left associativity, x constr at level 0, u constr at level 0).
Notation "p ; x ':=' u '⟨' q '⟩'" := (PSub p x u q) (in custom adj_pay at level 2, left associativity, x constr at level 0, u constr at level 0, q custom adj_pay at level 2).
Notation "x 'as' c" := (PRen PEmpty x c) (in custom adj_pay at level 1, x constr at level 0, c constr at level 0).
Notation "x ':=' u" := (PSub PEmpty x u PEmpty) (in custom adj_pay at level 1, x constr at level 0, u constr at level 0).
Notation "x ':=' u '⟨' q '⟩'" := (PSub PEmpty x u q) (in custom adj_pay at level 1, x constr at level 0, u constr at level 0, q custom adj_pay at level 2).

Notation "i ; x" := (cent i x) (in custom adj_in at level 2, left associativity, x constr at level 0).
Notation "i ; x 'as' v" := (IRenF i x v) (in custom adj_in at level 2, left associativity, x constr at level 0, v constr at level 0).
Notation "i ; x ':=' u" := (csub i x u PEmpty) (in custom adj_in at level 2, left associativity, x constr at level 0, u constr at level 0).
Notation "i ; x ':=' u '⟨' p '⟩'" := (csub i x u p) (in custom adj_in at level 2, left associativity, x constr at level 0, u constr at level 0, p custom adj_pay at level 2).
Notation "i ; '·'" := (cbnd i) (in custom adj_in at level 2, left associativity).
Notation "i ; '·' 'as' v" := (IRenB i v) (in custom adj_in at level 2, left associativity, v constr at level 0).
Notation "i ; '·' ':=' u" := (csubb i u PEmpty) (in custom adj_in at level 2, left associativity, u constr at level 0).
Notation "i ; '·' ':=' u '⟨' p '⟩'" := (csubb i u p) (in custom adj_in at level 2, left associativity, u constr at level 0, p custom adj_pay at level 2).
Notation "x" := (cent cnil x) (in custom adj_in at level 1, x constr at level 0).
Notation "x 'as' v" := (IRenF cnil x v) (in custom adj_in at level 1, x constr at level 0, v constr at level 0).
Notation "x ':=' u" := (csub cnil x u PEmpty) (in custom adj_in at level 1, x constr at level 0, u constr at level 0).
Notation "x ':=' u '⟨' p '⟩'" := (csub cnil x u p) (in custom adj_in at level 1, x constr at level 0, u constr at level 0, p custom adj_pay at level 2).
Notation "'·'" := (cbnd cnil) (in custom adj_in at level 1).
Notation "'·' 'as' v" := (IRenB cnil v) (in custom adj_in at level 1, v constr at level 0).
Notation "'·' ':=' u" := (csubb cnil u PEmpty) (in custom adj_in at level 1, u constr at level 0).
Notation "'·' ':=' u '⟨' p '⟩'" := (csubb cnil u p) (in custom adj_in at level 1, u constr at level 0, p custom adj_pay at level 2).

Notation "o ; y" := (OPosF o y) (in custom adj_out at level 4, left associativity, y constr at level 0).
Notation "o ; y 'as' a" := (ONamF y (fun a => o)) (in custom adj_out at level 4, left associativity, y constr at level 0, a name).
Notation "o ; '·'" := (OPosB o) (in custom adj_out at level 4, left associativity).
Notation "o ; '·' 'as' a" := (ONamB (fun a => o)) (in custom adj_out at level 4, left associativity, a name).
Notation "i" := (OShort i) (in custom adj_out at level 3, i custom adj_in at level 2).
Notation "i '|' σ" := (OShortT (Nt:=0) (STail i σ)) (in custom adj_out at level 3, i custom adj_in at level 2, σ constr at level 200).
Notation "'|' σ" := (OShortT (Nt:=0) (STail cnil σ)) (in custom adj_out at level 3, σ constr at level 200).
Notation "i '\'" := (OEnd i) (in custom adj_out at level 3, i custom adj_in at level 2).
Notation "i '\' y" := (OPosF (OEnd i) y) (in custom adj_out at level 3, i custom adj_in at level 2, y constr at level 0).
Notation "i '\' y 'as' a" := (ONamF y (fun a => OEnd i)) (in custom adj_out at level 3, i custom adj_in at level 2, y constr at level 0, a name).
Notation "i '\' '·'" := (OPosB (OEnd i)) (in custom adj_out at level 3, i custom adj_in at level 2).
Notation "i '\' '·' 'as' a" := (ONamB (fun a => OEnd i)) (in custom adj_out at level 3, i custom adj_in at level 2, a name).
Notation "'\'" := (OEnd cnil) (in custom adj_out at level 3).
Notation "'\' y" := (OPosF (OEnd cnil) y) (in custom adj_out at level 3, y constr at level 0).
Notation "'\' y 'as' a" := (ONamF y (fun a => OEnd cnil)) (in custom adj_out at level 3, y constr at level 0, a name).
Notation "'\' '·'" := (OPosB (OEnd cnil)) (in custom adj_out at level 3).
Notation "'\' '·' 'as' a" := (ONamB (fun a => OEnd cnil)) (in custom adj_out at level 3, a name).
Notation "i '|' g '\'" := (OEndT g i) (in custom adj_out at level 3, i custom adj_in at level 2, g constr at level 200).
Notation "i '|' g '\' y" := (OPosF (OEndT g i) y) (in custom adj_out at level 3, i custom adj_in at level 2, g constr at level 200, y constr at level 0).
Notation "i '|' g '\' y 'as' a" := (ONamF y (fun a => OEndT g i)) (in custom adj_out at level 3, i custom adj_in at level 2, g constr at level 200, y constr at level 0, a name).
Notation "i '|' g '\' '·'" := (OPosB (OEndT g i)) (in custom adj_out at level 3, i custom adj_in at level 2, g constr at level 200).
Notation "i '|' g '\' '·' 'as' a" := (ONamB (fun a => OEndT g i)) (in custom adj_out at level 3, i custom adj_in at level 2, g constr at level 200, a name).
Notation "'|' g '\'" := (OEndT g cnil) (in custom adj_out at level 3, g constr at level 200).
Notation "'|' g '\' y" := (OPosF (OEndT g cnil) y) (in custom adj_out at level 3, g constr at level 200, y constr at level 0).
Notation "'|' g '\' y 'as' a" := (ONamF y (fun a => OEndT g cnil)) (in custom adj_out at level 3, g constr at level 200, y constr at level 0, a name).
Notation "'|' g '\' '·'" := (OPosB (OEndT g cnil)) (in custom adj_out at level 3, g constr at level 200).
Notation "'|' g '\' '·' 'as' a" := (ONamB (fun a => OEndT g cnil)) (in custom adj_out at level 3, g constr at level 200, a name).

Notation "⟦ c ⟧" := (cform_id c) (c custom adj_out at level 4, format "⟦  c  ⟧").
Notation "⟦ c | g [ σ ] ⟧" := (cform (fun g => c) σ)
  (c custom adj_out at level 4, g name, σ constr at level 200, format "⟦  c  |  g [ σ ]  ⟧").
Notation "⟦ c | g ⟧" := (cform (fun g => c) identity) (c custom adj_out at level 4, g name, format "⟦  c  |  g  ⟧").
Notation "⟦ ⟧" := identity (format "⟦ ⟧").

(** The rewrite database [names] uses besides normalising adjustments:
    the substitution functor adds its laws, and each syntax its own. *)
Create Rewrite HintDb names_pre.
Create Rewrite HintDb names_var.
Create Rewrite HintDb names_post.

Declare Scope adj_scope.
Delimit Scope adj_scope with adj.
Bind Scope adj_scope with adj.
(** Composition in diagrammatic order: [a ⨾ b] is [a], then [b]. *)
Notation "a ⨾ b" := (compose b a) (at level 40, left associativity) : adj_scope.
Global Open Scope adj_scope.

(** Going under a binder, bound or named. *)
Notation lift a := ⟦ · | a ⟧ (only parsing).
Notation lift_free x a := ⟦ x | a ⟧ (only parsing).

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

