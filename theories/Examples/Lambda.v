(** * Scoped λ-terms and substitutions (public layer)

    [term N] is the type of λ-terms with at most [N] bound variables in scope
    and any free names.  [sub N M] is the type of substitutions from scope
    [N] to scope [M]: the library's scoped adjustments, with closed terms as
    payloads.  Users work only with these types, their constructors and the
    laws below.

    Terms:          [tfvar x i], [tbvar i], [tapp t1 t2], [tlam b], [tconst n].
    Substitutions:  [identity], [cons t σ], [cons_free x t σ], [weaken σ],
                    [weaken_free x σ], [compose σ τ], [lift σ], and the
                    derived [open_sub x], [close_sub x], [inst u].

    A substitution sends a variable to a variable in scope or to a closed
    term (with a lazily applied payload adjustment).

    Equality on both types is Leibniz equality. *)

From Stdlib Require Import Arith List Lia Bool StrictProp.
From ShiftedNames.Core Require Import Label Var Nested Adjustment Laws Scoped Indexed.
From ShiftedNames.Examples Require LambdaCore.

Module L := ShiftedNames.Examples.LambdaCore.

(** ** Terms *)

Record term (N : nat) : Type :=
  mk_term { term_raw : L.rterm; term_wf : Is_true_s (L.wf_term N term_raw) }.

Arguments mk_term {N} _ _.
Arguments term_raw {N} _.
Arguments term_wf {N} _.

Lemma term_eq {N} (t1 t2 : term N) : term_raw t1 = term_raw t2 -> t1 = t2.
Proof. destruct t1, t2; cbn; intros ->; reflexivity. Qed.

Lemma term_wf_true {N} (t : term N) : L.wf_term N (term_raw t) = true.
Proof. apply Is_true_s_elim, term_wf. Qed.

Definition tvar {N} (v : var N) : term N := mk_term (L.rtvar (var_raw v)) (var_ok v).
Definition tfvar {N} (x : label) (i : nat) : term N := tvar (fvar x i).
Definition tbvar {N} (i : nat) (H : Is_true_s (Nat.ltb i N)) : term N := tvar (bvar i H).
Definition tbvar0 {N} : term (S N) := tvar bvar0.

Definition tapp {N} (t1 t2 : term N) : term N :=
  mk_term (L.rtapp (term_raw t1) (term_raw t2))
    (Is_true_s_intro (proj2 (andb_true_iff _ _) (conj (term_wf_true t1) (term_wf_true t2)))).

Definition tlam {N} (b : term (S N)) : term N := mk_term (L.rtlam (term_raw b)) (term_wf b).

Definition tconst {N} (n : nat) : term N := mk_term (L.rtconst n) stt.

(** Closed terms, the payloads of substitutions. *)
Definition to_cterm (u : term 0) : L.cterm := L.mk_ct (term_raw u) (term_wf u).

(** A closed term in any scope. *)
Definition weaken0 {N} (u : term 0) : term N :=
  mk_term (term_raw u) (Is_true_s_intro (L.wf_term_mono _ 0 N (Nat.le_0_l N) (term_wf_true u))).

(** ** Substitutions *)

Notation sub N M := (adj L.cterm N M).

Definition subst {N M} (s : sub N M) (t : term N) : term M :=
  mk_term (L.rsubst (adj_raw s) (term_raw t))
    (Is_true_s_intro (L.wf_rsubst N M _ _ (adj_scoped s) (term_wf_true t))).

Notation "⟦ s ⟧ t" := (subst s t) (at level 9, s at level 200, right associativity).

(** A payload [(u, ρ)] as a term. *)
Definition payload_term {M} (u : L.cterm) (ρ : padj L.cterm M) : term M :=
  mk_term (L.rsubst (rpadj_adj (padj_raw ρ)) (L.ct u))
    (Is_true_s_intro (L.wf_payload M _ u (Is_true_s_elim (padj_ok ρ)))).

(** The trivial payload adjustment. *)
Definition pidentity {M} : padj L.cterm M := mk_padj (rto_padj nidentity) stt.

(** Targets: a variable in scope, or a closed term. *)
Definition tvar_target {M} (w : var M) : target L.cterm M := Rename w.
Definition closed_target {M} (u : term 0) : target L.cterm M := Bind (to_cterm u) pidentity.

(** Opening the innermost bound variable as [x], closing [x] into a new
    innermost bound variable, and instantiating it with a closed term. *)
Definition open_sub {N} (x : label) : sub (S N) N :=
  cons (tvar_target (fvar x 0)) (weaken_free x identity).
Definition close_sub {N} (x : label) : sub N (S N) :=
  cons_free x (tvar_target bvar0) (weaken identity).
Definition inst {N} (u : term 0) : sub (S N) N := cons (closed_target u) identity.

(** ** Substitution on terms *)

Theorem subst_app {N M} (s : sub N M) t1 t2 : ⟦s⟧ (tapp t1 t2) = tapp (⟦s⟧ t1) (⟦s⟧ t2).
Proof. apply term_eq, L.rsubst_app. Qed.

Theorem subst_const {N M} (s : sub N M) n : ⟦s⟧ (tconst n) = tconst n.
Proof. apply term_eq, L.rsubst_const. Qed.

Theorem subst_lam {N M} (s : sub N M) b : ⟦s⟧ (tlam b) = tlam (⟦lift s⟧ b).
Proof. apply term_eq, L.rsubst_lam. Qed.

Theorem subst_var {N M} (s : sub N M) (v : var N) :
  term_raw (⟦s⟧ (tvar v))
  = match apply s v with
    | inl w => L.rtvar w
    | inr p => L.rsubst (rpadj_adj (snd p)) (L.ct (fst p))
    end.
Proof. apply L.rsubst_var. Qed.

Theorem subst_sid {N} (t : term N) : ⟦identity⟧ t = t.
Proof. apply term_eq, L.rsubst_identity. Qed.

Theorem subst_comp {N M K} (s : sub M K) (r : sub N M) t : ⟦s⟧ (⟦r⟧ t) = ⟦compose s r⟧ t.
Proof. apply term_eq, L.rsubst_subst. Qed.

Theorem subst_cons_var0 {N M} (w : var M) (s : sub N M) :
  ⟦cons (tvar_target w) s⟧ tbvar0 = tvar w.
Proof.
  apply term_eq; cbn [term_raw subst tbvar0 tvar var_raw bvar0].
  rewrite L.rsubst_var; cbn [adj_raw cons to_target tvar_target].
  rewrite rapply_push_inner, rvar_eqb_refl; reflexivity.
Qed.

Theorem subst_cons_bind0 {N M} u (ρ : padj L.cterm M) (s : sub N M) :
  ⟦cons (Bind u ρ) s⟧ tbvar0 = payload_term u ρ.
Proof.
  apply term_eq; cbn [term_raw subst tbvar0 tvar var_raw bvar0].
  rewrite L.rsubst_var; cbn [adj_raw cons to_target].
  rewrite rapply_push_inner, rvar_eqb_refl; reflexivity.
Qed.

Theorem subst_cons_S {N M} (t : target L.cterm M) (s : sub N M) i H :
  ⟦cons t s⟧ (tbvar (S i) H) = ⟦s⟧ (tbvar i H).
Proof.
  apply term_eq; cbn [term_raw subst tbvar tvar var_raw bvar].
  rewrite !L.rsubst_var; cbn [adj_raw cons].
  rewrite rapply_push_inner; unfold rvar_eqb, unshift_rvar; cbn.
  replace (i - 0) with i by lia; reflexivity.
Qed.

Theorem subst_cons_fvar {N M} (t : target L.cterm M) (s : sub N M) x i :
  ⟦cons t s⟧ (tfvar x i) = ⟦s⟧ (tfvar x i).
Proof.
  apply term_eq; cbn [term_raw subst tfvar tvar var_raw fvar].
  rewrite !L.rsubst_var; cbn [adj_raw cons].
  rewrite rapply_push_inner; reflexivity.
Qed.

Theorem subst_inst_bvar0 {N} (u : term 0) : ⟦@inst N u⟧ tbvar0 = weaken0 u.
Proof.
  unfold inst, closed_target; rewrite subst_cons_bind0.
  apply term_eq; cbn [term_raw payload_term weaken0 padj_raw pidentity L.ct to_cterm].
  replace (rpadj_adj (rto_padj (@nidentity L.cterm))) with (@ridentity L.cterm)
    by (apply radj_eq; reflexivity).
  apply L.rsubst_identity.
Qed.

(** ** Locally nameless laws *)

Theorem open_close {N} x : compose (@open_sub N x) (close_sub x) = identity.
Proof. apply adj_eq, rcompose_open_close. Qed.

Theorem close_open {N} x : compose (@close_sub N x) (open_sub x) = identity.
Proof. apply adj_eq, rcompose_close_open. Qed.

(** ** Closed substitutions go under binders for free *)

Theorem subst_closed_lam {N} (s : sub 0 0) (b : term (S N)) :
  ⟦at_scope s⟧ (tlam b) = tlam (⟦at_scope s⟧ b).
Proof. rewrite subst_lam, lift_at_scope; reflexivity. Qed.
