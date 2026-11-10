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

(** The name of a tail: its binder exists only to make the input and the
    output context name the same tail. *)
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

(** Weakening a payload past one output.  Payloads are passed as thunks,
    so that the weakening is only computed for the entries that use it. *)
Definition pw_bound {M} (ρ : unit -> padj T M) : unit -> padj T (S M) := fun _ => pcompose (out_bound identity) (ρ tt).
Definition pw_free {M} (y : label) (ρ : unit -> padj T M) : unit -> padj T M := fun _ => pcompose (out_free y identity) (ρ tt).

(** *** The full form *)

(** Input contexts, innermost entry first, built by adding entries on the
    outside: [ictx M Nb N P] goes from a tail with [Nb] inputs to [N]
    inputs, into the output scope [M], with [P] positional entries. *)
Inductive ictx (M : nat) : nat -> nat -> nat -> Type :=
| IEmpty {N} : ictx M N N 0
| IPosF {Nb N P} (i : ictx M Nb N P) (x : label) : ictx M Nb N (S P)
| IPosB {Nb N P} (i : ictx M (S Nb) N P) : ictx M Nb N (S P)
| IRenF {Nb N P} (i : ictx M Nb N P) (x : label) (v : var M) : ictx M Nb N P
| IRenB {Nb N P} (i : ictx M (S Nb) N P) (v : var M) : ictx M Nb N P
| ISubF {Nb N P} (i : ictx M Nb N P) (x : label) (u : T) : ictx M Nb N P
| ISubB {Nb N P} (i : ictx M (S Nb) N P) (u : T) : ictx M Nb N P.

(** Output contexts, innermost slot first, over the input context: the
    indices are the positional outputs so far, the output scope at the
    outer edge of the slots so far, and whether the input context names
    its tail. *)
Inductive octx (Nt N M P : nat) : nat -> nat -> option tname -> Type :=
| OEnd (i : ictx M Nt N P) : octx Nt N M P 0 M None
| OEndT (g : tname) (i : ictx M Nt N P) : octx Nt N M P 0 M (Some g)
| OPosF {Po J b} (o : octx Nt N M P Po J b) (y : label) : octx Nt N M P (S Po) J b
| OPosB {Po J b} (o : octx Nt N M P Po (S J) b) : octx Nt N M P (S Po) J b
| ONamF {Po J b} (y : label) (k : var M -> octx Nt N M P Po J b) : octx Nt N M P Po J b
| ONamB {Po J b} (k : var M -> octx Nt N M P Po (S J) b) : octx Nt N M P Po J b.

Arguments IEmpty {M N}.
Arguments IPosF {M Nb N P} i x.
Arguments IPosB {M Nb N P} i.
Arguments IRenF {M Nb N P} i x v.
Arguments IRenB {M Nb N P} i v.
Arguments ISubF {M Nb N P} i x u.
Arguments ISubB {M Nb N P} i u.
Arguments OEnd {Nt N M P} i.
Arguments OEndT {Nt N M P} g i.
Arguments OPosF {Nt N M P Po J b} o y.
Arguments OPosB {Nt N M P Po J b} o.
Arguments ONamF {Nt N M P Po J b} y k.
Arguments ONamB {Nt N M P Po J b} k.

Definition vdummy {M} : var M := fvar EmptyString 0.

(** The input context over [X], with [pos] the positional slots,
    innermost first, and [ρ] the payload adjustment of its terms. *)
Fixpoint ictx_den {M Nb N P} (i : ictx M Nb N P) : list (var M) -> (unit -> padj T M) -> adj T Nb M -> adj T N M :=
  match i in ictx _ Nb N P return list (var M) -> (unit -> padj T M) -> adj T Nb M -> adj T N M with
  | IEmpty => fun _ _ X => X
  | @IPosF _ _ _ P i x => fun pos ρ X => ictx_den i pos ρ (in_free x (Rename (nth P pos vdummy)) X)
  | @IPosB _ _ _ P i => fun pos ρ X => ictx_den i pos ρ (in_bound (Rename (nth P pos vdummy)) X)
  | IRenF i x v => fun pos ρ X => ictx_den i pos ρ (in_free x (Rename v) X)
  | IRenB i v => fun pos ρ X => ictx_den i pos ρ (in_bound (Rename v) X)
  | ISubF i x u => fun pos ρ X => ictx_den i pos ρ (in_free x (Bind u (ρ tt)) X)
  | ISubB i u => fun pos ρ X => ictx_den i pos ρ (in_bound (Bind u (ρ tt)) X)
  end.

(** Where the slots inside [o] take a variable at its outer edge. *)
Fixpoint octx_probe {Nt N M P Po J b} (o : octx Nt N M P Po J b) : var J -> var M :=
  match o in octx _ _ _ _ _ J _ return var J -> var M with
  | OEnd _ | OEndT _ _ => fun v => v
  | OPosF o y => fun v => octx_probe o (vshift_free y v)
  | OPosB o => fun v => octx_probe o (vshift_bound v)
  | ONamF y k => fun v => octx_probe (k vdummy) (vshift_free y v)
  | ONamB k => fun v => octx_probe (k vdummy) (vshift_bound v)
  end.

(** The slots from the outermost in, over [X]; [pos] collects the
    positional slots and [ρ] weakens the input context's terms. *)
Fixpoint octx_den {Nt N M P Po J b} (o : octx Nt N M P Po J b)
  : list (var M) -> (unit -> padj T J) -> adj T Nt J -> adj T N M :=
  match o in octx _ _ _ _ _ J _ return list (var M) -> (unit -> padj T J) -> adj T Nt J -> adj T N M with
  | OEnd i | OEndT _ i => fun pos ρ X => ictx_den i pos ρ X
  | OPosF o y => fun pos ρ X => octx_den o (octx_probe o (fvar y 0) :: pos) (pw_free y ρ) (out_free y X)
  | OPosB o => fun pos ρ X => octx_den o (octx_probe o bvar0 :: pos) (pw_bound ρ) (out_bound X)
  | ONamF y k => fun pos ρ X =>
      let a := octx_probe (k vdummy) (fvar y 0) in octx_den (k a) pos (pw_free y ρ) (out_free y X)
  | ONamB k => fun pos ρ X =>
      let a := octx_probe (k vdummy) bvar0 in octx_den (k a) pos (pw_bound ρ) (out_bound X)
  end.

Definition cform_id {Nt N M P} (o : octx Nt N M P P Nt None) : adj T N M := octx_den o nil (fun _ => pid) identity.

Definition cform {Nt Mt N M P} (o : forall g : tname, octx Nt N M P P Mt (Some g)) (σ : adj T Nt Mt) : adj T N M :=
  octx_den (o tname_tt) nil (fun _ => pid) σ.

(** *** The short form *)

(** [sctx Nb Mb N M] goes from a tail [adj Nb Mb] to [adj N M]. *)
Inductive sctx : nat -> nat -> nat -> nat -> Type :=
| SEmpty {N M} : sctx N M N M
| SLiftF {Nb Mb N M} (s : sctx Nb Mb N M) (x : label) : sctx Nb Mb N M
| SLiftB {Nb Mb N M} (s : sctx (S Nb) (S Mb) N M) : sctx Nb Mb N M
| SSubF {Nb Mb N M} (s : sctx Nb Mb N M) (x : label) (u : T) : sctx Nb Mb N M
| SSubB {Nb Mb N M} (s : sctx (S Nb) Mb N M) (u : T) : sctx Nb Mb N M.

Inductive sclosed (N M : nat) : Type :=
| STail {Nb Mb} (s : sctx Nb Mb N M) (σ : adj T Nb Mb).

Arguments STail {N M Nb Mb} s σ.

Fixpoint sctx_den {Nb Mb N M} (s : sctx Nb Mb N M) : (unit -> padj T Mb) -> adj T Nb Mb -> adj T N M :=
  match s with
  | SEmpty => fun _ X => X
  | SLiftF s x => fun ρ X => sctx_den s (pw_free x ρ) (in_free x (Rename (fvar x 0)) (out_free x X))
  | SLiftB s => fun ρ X => sctx_den s (pw_bound ρ) (in_bound (Rename bvar0) (out_bound X))
  | SSubF s x u => fun ρ X => sctx_den s ρ (in_free x (Bind u (ρ tt)) X)
  | SSubB s u => fun ρ X => sctx_den s ρ (in_bound (Bind u (ρ tt)) X)
  end.

End Context.

Arguments IEmpty {T M N}.
Arguments IPosF {T M Nb N P} i x.
Arguments IPosB {T M Nb N P} i.
Arguments IRenF {T M Nb N P} i x v.
Arguments IRenB {T M Nb N P} i v.
Arguments ISubF {T M Nb N P} i x u.
Arguments ISubB {T M Nb N P} i u.
Arguments OEnd {T Nt N M P} i.
Arguments OEndT {T Nt N M P} g i.
Arguments OPosF {T Nt N M P Po J b} o y.
Arguments OPosB {T Nt N M P Po J b} o.
Arguments ONamF {T Nt N M P Po J b} y k.
Arguments ONamB {T Nt N M P Po J b} k.
Arguments SEmpty {T N M}.
Arguments SLiftF {T Nb Mb N M} s x.
Arguments SLiftB {T Nb Mb N M} s.
Arguments SSubF {T Nb Mb N M} s x u.
Arguments SSubB {T Nb Mb N M} s u.
Arguments STail {T N M Nb Mb} s σ.

(** *** Entries shared by both forms

    The input entries are written the same way in both forms; which form
    they build is decided by the type expected of them: an output context
    after [\] expects a full-form input context, and a context form with
    no [\] is a short form. *)

Class CNil (C : Type) := cnil : C.
Class CEnt (C E R : Type) := cent : C -> E -> R.
Class CBnd (C R : Type) := cbnd : C -> R.
Class CSub (T C R : Type) := csub : C -> label -> T -> R.
Class CSubB (T C R : Type) := csubb : C -> T -> R.
Class CDen (C A : Type) := cden : C -> A.

#[export] Instance cnil_full {T M N} : CNil (@ictx T M N N 0) := IEmpty.
#[export] Instance cnil_short {T N M} : CNil (@sctx T N M N M) := SEmpty.
#[export] Instance cent_full {T M Nb N P} : CEnt (@ictx T M Nb N P) label (ictx M Nb N (S P)) := IPosF.
#[export] Instance cent_short {T Nb Mb N M} : CEnt (@sctx T Nb Mb N M) label (sctx Nb Mb N M) := SLiftF.
#[export] Instance cbnd_full {T M Nb N P} : CBnd (@ictx T M (S Nb) N P) (ictx M Nb N (S P)) := IPosB.
#[export] Instance cbnd_short {T Nb Mb N M} : CBnd (@sctx T (S Nb) (S Mb) N M) (sctx Nb Mb N M) := SLiftB.
#[export] Instance csub_full {T M Nb N P} : CSub T (@ictx T M Nb N P) (ictx M Nb N P) := ISubF.
#[export] Instance csub_short {T Nb Mb N M} : CSub T (@sctx T Nb Mb N M) (sctx Nb Mb N M) := SSubF.
#[export] Instance csubb_full {T M Nb N P} : CSubB T (@ictx T M (S Nb) N P) (ictx M Nb N P) := ISubB.
#[export] Instance csubb_short {T Nb Mb N M} : CSubB T (@sctx T (S Nb) Mb N M) (sctx Nb Mb N M) := SSubB.
#[export] Instance cden_full {T Nt N M P} : CDen (@octx T Nt N M P P Nt None) (adj T N M) := cform_id.
#[export] Instance cden_short {T N0 N M} : CDen (@sctx T N0 N0 N M) (adj T N M) := fun s => sctx_den s (fun _ => pid) identity.
#[export] Instance cden_tail {T N M} : CDen (@sclosed T N M) (adj T N M) :=
  fun c => match c with STail s σ => sctx_den s (fun _ => pid) σ end.

(** *** Notation *)

Declare Custom Entry adj_in.
Declare Custom Entry adj_out.

Notation "i ; x" := (cent i x) (in custom adj_in at level 2, left associativity, x constr at level 0).
Notation "i ; x 'as' v" := (IRenF i x v) (in custom adj_in at level 2, left associativity, x constr at level 0, v constr at level 0).
Notation "i ; x ':=' u" := (csub i x u) (in custom adj_in at level 2, left associativity, x constr at level 0, u constr at level 0).
Notation "i ; '·'" := (cbnd i) (in custom adj_in at level 2, left associativity).
Notation "i ; '·' 'as' v" := (IRenB i v) (in custom adj_in at level 2, left associativity, v constr at level 0).
Notation "i ; '·' ':=' u" := (csubb i u) (in custom adj_in at level 2, left associativity, u constr at level 0).
Notation "x" := (cent cnil x) (in custom adj_in at level 1, x constr at level 0).
Notation "x 'as' v" := (IRenF cnil x v) (in custom adj_in at level 1, x constr at level 0, v constr at level 0).
Notation "x ':=' u" := (csub cnil x u) (in custom adj_in at level 1, x constr at level 0, u constr at level 0).
Notation "'·'" := (cbnd cnil) (in custom adj_in at level 1).
Notation "'·' 'as' v" := (IRenB cnil v) (in custom adj_in at level 1, v constr at level 0).
Notation "'·' ':=' u" := (csubb cnil u) (in custom adj_in at level 1, u constr at level 0).

Notation "o ; y" := (OPosF o y) (in custom adj_out at level 4, left associativity, y constr at level 0).
Notation "o ; y 'as' a" := (ONamF y (fun a => o)) (in custom adj_out at level 4, left associativity, y constr at level 0, a name).
Notation "o ; '·'" := (OPosB o) (in custom adj_out at level 4, left associativity).
Notation "o ; '·' 'as' a" := (ONamB (fun a => o)) (in custom adj_out at level 4, left associativity, a name).
Notation "i" := i (in custom adj_out at level 3, i custom adj_in at level 2).
Notation "i '|' σ" := (STail i σ) (in custom adj_out at level 3, i custom adj_in at level 2, σ constr at level 200).
Notation "'|' σ" := (STail cnil σ) (in custom adj_out at level 3, σ constr at level 200).
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

Notation "⟦ c ⟧" := (cden c) (c custom adj_out at level 4, format "⟦  c  ⟧").
Notation "⟦ c | g [ σ ] ⟧" := (cform (fun g => c) σ)
  (c custom adj_out at level 4, g name, σ constr at level 200, format "⟦  c  |  g [ σ ]  ⟧").
Notation "⟦ c | g ⟧" := (cform (fun g => c) identity) (c custom adj_out at level 4, g name, format "⟦  c  |  g  ⟧").
Notation "⟦ ⟧" := identity (format "⟦ ⟧").

Declare Scope adj_scope.
Delimit Scope adj_scope with adj.
Bind Scope adj_scope with adj.
Notation "a ∘ b" := (compose a b) (at level 40, left associativity) : adj_scope.
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

