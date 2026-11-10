(** * The simply typed λ-calculus

    Typing for the λ-calculus of [Lambda.v], with contexts and context
    morphisms from the library, and the usual metatheory: weakening (along
    any context morphism), the substitution lemma, and their corollaries.
    Binders are typed in the locally nameless style, by opening with any
    name. *)

From Stdlib Require Import String StrictProp.
From ShiftedNames.Core Require Import Label Var Adjustment Indexed Syntax Subst Names Context.
From ShiftedNames.Examples Require Import Lambda.
Import LS.
Open Scope ctx_scope.

Inductive ty : Type := Base | Fn (A B : ty).

Reserved Notation "Γ ⊢ e ~ A" (at level 70, e at next level).

Inductive types (Γ : ctx ty) : tm 0 -> ty -> Prop :=
| VAR (v : var 0) A : Γ ∋ v ~ A -> Γ ⊢ tvar v ~ A
| BASE k : Γ ⊢ tconst k ~ Base
| LAM body A B : (forall x, Γ & x ~ A ⊢ topen x body ~ B) -> Γ ⊢ tlam body ~ Fn A B
| APP f e A B : Γ ⊢ f ~ Fn A B -> Γ ⊢ e ~ A -> Γ ⊢ tapp f e ~ B
where "Γ ⊢ e ~ A" := (types Γ e A).

(** ** Weakening, along any context morphism *)

Theorem weakening {Γ e A} :
  Γ ⊢ e ~ A -> forall (σ : sub 0 0) Δ, Γ =[σ]=> Δ -> Δ ⊢ subst σ e ~ A.
Proof.
  induction 1 as [Γ v A Hv|Γ k|Γ body A B _ IH|Γ f e A B _ IHf _ IHe]; intros σ Δ Hσ.
  - destruct (Hσ v A Hv) as [w [Ew Hw]]; rewrite (subst_tvar_ren σ v w Ew); constructor; exact Hw.
  - rewrite subst_tconst; constructor.
  - rewrite subst_tlam; constructor; intros x.
    specialize (IH x _ _ (ctx_map_under Γ Δ σ x x A Hσ)).
    replace (topen x (subst ⟦ · | σ ⟧ body)) with (subst ⟦ x | R \ x | R[σ] ⟧ (topen x body))
      by (names; reflexivity).
    exact IH.
  - rewrite subst_tapp; econstructor; [apply IHf|apply IHe]; exact Hσ.
Qed.

(** ** The substitution lemma *)

Theorem substitution {Γ e A} :
  Γ ⊢ e ~ A ->
  forall (σ : sub 0 0) Δ, forall_has Γ (fun v B => Δ ⊢ subst σ (tvar v) ~ B) -> Δ ⊢ subst σ e ~ A.
Proof.
  induction 1 as [Γ v A Hv|Γ k|Γ body A B _ IH|Γ f e A B _ IHf _ IHe]; intros σ Δ Hσ.
  - apply Hσ, Hv.
  - rewrite subst_tconst; constructor.
  - rewrite subst_tlam; constructor; intros x.
    replace (topen x (subst ⟦ · | σ ⟧ body)) with (subst ⟦ x | R \ x | R[σ] ⟧ (topen x body))
      by (names; reflexivity).
    apply IH, forall_has_cons.
    + rewrite (subst_tvar_ren _ _ _ (apply_var_under_here x x σ)); constructor; apply has_here.
    + intros y b Hy.
      rewrite <- (subst_tvar_ren _ _ _ (apply_var_weaken x y)).
      replace (subst ⟦ x | R \ x | R[σ] ⟧ (subst ⟦ \ x as _ ⟧ (tvar y)))
        with (subst ⟦ | R \ x as _ | R[⟦⟧] ⟧ (subst σ (tvar y))) by (names; reflexivity).
      apply (weakening (Hσ y b Hy)), ctx_map_weaken, ctx_map_id.
  - rewrite subst_tapp; econstructor; [apply IHf|apply IHe]; exact Hσ.
Qed.

(** ** Corollaries *)

Corollary weakening1 {Γ e A} x B : Γ ⊢ e ~ A -> Γ & x ~ B ⊢ subst ⟦ \ x as _ ⟧ e ~ A.
Proof.
  intros H; replace (subst ⟦ \ x as _ ⟧ e) with (subst ⟦ | R \ x as _ | R[⟦⟧] ⟧ e) by (names; reflexivity).
  apply (weakening H), ctx_map_weaken, ctx_map_id.
Qed.

Corollary renaming1 {Γ e A} x y B : Γ & x ~ B ⊢ e ~ A -> Γ & y ~ B ⊢ subst ⟦ x \ y ⟧ e ~ A.
Proof.
  intros H; replace (subst ⟦ x \ y ⟧ e) with (subst ⟦ x | R \ y | R[⟦⟧] ⟧ e) by (names; reflexivity).
  apply (weakening H), ctx_map_under, ctx_map_id.
Qed.

Corollary renaming1' {Γ e A} x y B : Γ & y ~ B ⊢ subst ⟦ x \ y ⟧ e ~ A -> Γ & x ~ B ⊢ e ~ A.
Proof.
  intros H; apply (renaming1 y x) in H.
  replace (subst ⟦ y \ x ⟧ (subst ⟦ x \ y ⟧ e)) with e in H; [exact H|].
  destruct (label_compare_spec x y) as [<-|Hxy|Hxy]; names; reflexivity.
Qed.

Corollary substitution1 {Γ e e' A} x B : Γ & x ~ B ⊢ e ~ A -> Γ ⊢ e' ~ B -> Γ ⊢ subst ⟦ x := e' ⟧ e ~ A.
Proof.
  intros He He'; apply (substitution He), forall_has_cons.
  - refine (eq_ind _ (fun t => Γ ⊢ t ~ B) He' _ _); symmetry; apply subst_tvar_bind, apply_var_subst_here.
  - intros y b Hy; rewrite <- (subst_tvar_ren _ _ _ (apply_var_weaken x y)).
    replace (subst ⟦ x := e' ⟧ (subst ⟦ \ x as _ ⟧ (tvar y))) with (tvar y) by (names; reflexivity).
    constructor; exact Hy.
Qed.

(** A binder can be typed by opening with one chosen name. *)
Lemma LAM' x {Γ body A B} : Γ & x ~ A ⊢ topen x body ~ B -> Γ ⊢ tlam body ~ Fn A B.
Proof.
  intros H; apply LAM; intros y; apply (renaming1' y x).
  replace (subst ⟦ y \ x ⟧ (topen y body)) with (topen x body); [exact H|].
  destruct (label_compare_spec x y) as [<-|Hxy|Hxy]; names; reflexivity.
Qed.
