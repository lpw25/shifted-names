(** * Scoped λ-terms and substitutions (public layer)

    [tm N] is the type of λ-terms with at most [N] bound variables in scope
    and any free names.  [sub N M] is the type of substitutions from scope
    [N] to scope [M]: the library's scoped adjustments, with closed terms as
    payloads.  Users work only with these types, their constructors and the
    laws below.

    Terms:          [fvar x i], [bvar i], [app t1 t2], [lam b], [const n].
    Substitutions:  [sid], [scons t σ], [scons_free x t σ], [sweaken σ],
                    [sweaken_free x σ], [scompose σ τ], [slift σ], and the
                    derived [open_sub x], [close_sub x], [inst u].

    A substitution sends a variable to a variable in scope or to a closed
    term (with a lazily applied payload adjustment).

    Equality on both types is Leibniz equality. *)

From Stdlib Require Import Arith List Lia Bool StrictProp.
From ShiftedNames.Core Require Import Label Var Nested Adjustment Laws Scoped Indexed.
From ShiftedNames.Examples Require LambdaCore.

Module L := ShiftedNames.Examples.LambdaCore.

(** ** Terms *)

Record tm (N : nat) : Type :=
  mk_tm { tm_raw : L.term; tm_wf : Is_true_s (L.wf_term N tm_raw) }.

Arguments mk_tm {N} _ _.
Arguments tm_raw {N} _.
Arguments tm_wf {N} _.

Lemma tm_eq {N} (t1 t2 : tm N) : tm_raw t1 = tm_raw t2 -> t1 = t2.
Proof. destruct t1, t2; cbn; intros ->; reflexivity. Qed.

Lemma tm_wf_true {N} (t : tm N) : L.wf_term N (tm_raw t) = true.
Proof. apply Is_true_s_elim, tm_wf. Qed.

Definition var_tm {N} (v : svar N) : tm N := mk_tm (L.tvar (sv v)) (sv_ok v).
Definition fvar {N} (x : label) (i : nat) : tm N := var_tm (sfvar x i).
Definition bvar {N} (i : nat) (H : Is_true_s (Nat.ltb i N)) : tm N := var_tm (sbvar i H).
Definition bvar0 {N} : tm (S N) := var_tm sbvar0.

Definition app {N} (t1 t2 : tm N) : tm N :=
  mk_tm (L.tapp (tm_raw t1) (tm_raw t2))
    (Is_true_s_intro (proj2 (andb_true_iff _ _) (conj (tm_wf_true t1) (tm_wf_true t2)))).

Definition lam {N} (b : tm (S N)) : tm N := mk_tm (L.tlam (tm_raw b)) (tm_wf b).

Definition const {N} (n : nat) : tm N := mk_tm (L.tconst n) stt.

(** Closed terms, the payloads of substitutions. *)
Definition to_cterm (u : tm 0) : L.cterm := L.mk_ct (tm_raw u) (tm_wf u).

(** A closed term in any scope. *)
Definition weaken0 {N} (u : tm 0) : tm N :=
  mk_tm (tm_raw u) (Is_true_s_intro (L.wf_term_mono _ 0 N (Nat.le_0_l N) (tm_wf_true u))).

(** ** Substitutions *)

Notation sub N M := (sadj L.cterm N M).

Definition subst {N M} (s : sub N M) (t : tm N) : tm M :=
  mk_tm (L.subst (sa s) (tm_raw t))
    (Is_true_s_intro (L.wf_subst N M _ _ (sa_scoped s) (tm_wf_true t))).

Notation "⟦ s ⟧ t" := (subst s t) (at level 9, s at level 200, right associativity).

(** A payload [(u, ρ)] as a term. *)
Definition payload_tm {M} (u : L.cterm) (ρ : spadj L.cterm M) : tm M :=
  mk_tm (L.subst (padj_adj (sp ρ)) (L.ct u))
    (Is_true_s_intro (L.wf_payload M _ u (Is_true_s_elim (sp_ok ρ)))).

(** The trivial payload adjustment. *)
Definition spid {M} : spadj L.cterm M := mk_spadj (to_padj nidentity) stt.

(** Targets: a variable in scope, or a closed term. *)
Definition tvar_target {M} (w : svar M) : starget L.cterm M := SRename w.
Definition closed_target {M} (u : tm 0) : starget L.cterm M := SBind (to_cterm u) spid.

(** Opening the innermost bound variable as [x], closing [x] into a new
    innermost bound variable, and instantiating it with a closed term. *)
Definition open_sub {N} (x : label) : sub (S N) N :=
  scons (tvar_target (sfvar x 0)) (sweaken_free x sid).
Definition close_sub {N} (x : label) : sub N (S N) :=
  scons_free x (tvar_target sbvar0) (sweaken sid).
Definition inst {N} (u : tm 0) : sub (S N) N := scons (closed_target u) sid.

(** ** Substitution on terms *)

Theorem subst_app {N M} (s : sub N M) t1 t2 : ⟦s⟧ (app t1 t2) = app (⟦s⟧ t1) (⟦s⟧ t2).
Proof. apply tm_eq, L.subst_app. Qed.

Theorem subst_const {N M} (s : sub N M) n : ⟦s⟧ (const n) = const n.
Proof. apply tm_eq, L.subst_const. Qed.

Theorem subst_lam {N M} (s : sub N M) b : ⟦s⟧ (lam b) = lam (⟦slift s⟧ b).
Proof. apply tm_eq, L.subst_lam. Qed.

Theorem subst_var {N M} (s : sub N M) (v : svar N) :
  tm_raw (⟦s⟧ (var_tm v))
  = match sapply s v with
    | inl w => L.tvar w
    | inr p => L.subst (padj_adj (snd p)) (L.ct (fst p))
    end.
Proof. apply L.subst_var. Qed.

Theorem subst_sid {N} (t : tm N) : ⟦sid⟧ t = t.
Proof. apply tm_eq, L.subst_identity. Qed.

Theorem subst_comp {N M K} (s : sub M K) (r : sub N M) t : ⟦s⟧ (⟦r⟧ t) = ⟦scompose s r⟧ t.
Proof. apply tm_eq, L.subst_subst. Qed.

Theorem subst_cons_var0 {N M} (w : svar M) (s : sub N M) :
  ⟦scons (tvar_target w) s⟧ bvar0 = var_tm w.
Proof.
  apply tm_eq; cbn [tm_raw subst bvar0 var_tm sv sbvar0].
  rewrite L.subst_var; cbn [sa scons to_target tvar_target].
  rewrite apply_push_inner, var_eqb_refl; reflexivity.
Qed.

Theorem subst_cons_bind0 {N M} u (ρ : spadj L.cterm M) (s : sub N M) :
  ⟦scons (SBind u ρ) s⟧ bvar0 = payload_tm u ρ.
Proof.
  apply tm_eq; cbn [tm_raw subst bvar0 var_tm sv sbvar0].
  rewrite L.subst_var; cbn [sa scons to_target].
  rewrite apply_push_inner, var_eqb_refl; reflexivity.
Qed.

Theorem subst_cons_S {N M} (t : starget L.cterm M) (s : sub N M) i H :
  ⟦scons t s⟧ (bvar (S i) H) = ⟦s⟧ (bvar i H).
Proof.
  apply tm_eq; cbn [tm_raw subst bvar var_tm sv sbvar].
  rewrite !L.subst_var; cbn [sa scons].
  rewrite apply_push_inner; unfold var_eqb, unshift_var; cbn.
  replace (i - 0) with i by lia; reflexivity.
Qed.

Theorem subst_cons_fvar {N M} (t : starget L.cterm M) (s : sub N M) x i :
  ⟦scons t s⟧ (fvar x i) = ⟦s⟧ (fvar x i).
Proof.
  apply tm_eq; cbn [tm_raw subst fvar var_tm sv sfvar].
  rewrite !L.subst_var; cbn [sa scons].
  rewrite apply_push_inner; reflexivity.
Qed.

Theorem subst_inst_bvar0 {N} (u : tm 0) : ⟦@inst N u⟧ bvar0 = weaken0 u.
Proof.
  unfold inst, closed_target; rewrite subst_cons_bind0.
  apply tm_eq; cbn [tm_raw payload_tm weaken0 sp spid L.ct to_cterm].
  replace (padj_adj (to_padj (@nidentity L.cterm))) with (@identity L.cterm)
    by (apply adj_eq; reflexivity).
  apply L.subst_identity.
Qed.

(** ** Locally nameless laws *)

Theorem open_close {N} x : scompose (@open_sub N x) (close_sub x) = sid.
Proof. apply sadj_eq, compose_open_close. Qed.

Theorem close_open {N} x : scompose (@close_sub N x) (open_sub x) = sid.
Proof. apply sadj_eq, compose_close_open. Qed.
