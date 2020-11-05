Require Import String Morph Var Context Relative.

Inductive tm {V : nat} :=
| vv : @var V -> @tm V
| const : nat -> @tm V
| lam : @tm (S V) -> @tm V
| app : @tm V -> @tm V -> @tm V. 

Module LambdaTerm <: Term.

  Definition term := @tm.

  Definition unit {N} : morph (@var) N (@term) N :=
    morph_inject (@vv).

  Fixpoint kleisli {N M} (f : morph (@var) N (@term) M) V t :=
    match t with
    | vv v => f V v
    | const n => const n
    | lam t =>
      lam (nset_push (kleisli f (S V) (nset_pop t)))
    | app t1 t2 =>
      app (kleisli f V t1) (kleisli f V t2)
    end.

  Lemma left_identity :
    forall N M (f : morph (@var) N (@term) M) V t,
      kleisli f V (unit V t) = f V t.
  Proof. reflexivity. Qed.

  Lemma right_identity :
    forall N V (t : @term (N + V)),
      @kleisli N N unit V t = t.
  Proof.
    intros.
    inductT t; simplT; reflexivity.
  Qed.

  Lemma associativity :
    forall N M L
      (f : morph (@var) N (@term) M)
      (g : morph (@var) M (@term) L) V t,
      kleisli (fun V' t' => kleisli g V' (f V' t')) V t
      = kleisli g V (kleisli f V t).
  Proof.
    intros.
    inductT t; simplT; reflexivity.
  Qed.

  Lemma unit_extend :
    forall N V v,
      morph_extend (@unit N) V v = unit V v.
  Proof.
    intros.
    apply morph_extend_inject.
  Qed.

  Lemma kleisli_extend :
    forall N M (f : morph (@var) N (@term) M) V t,
      morph_extend (kleisli f) V t
      = kleisli (morph_extend f) V t.
  Proof.
    intros.
    inductT t; simplT; reflexivity.
  Qed.      

  Lemma extensional :
    forall N M (f g : morph (@var) N (@term) M) V t,
      (forall V t, f V t = g V t) ->
      kleisli f V t = kleisli g V t.
  Proof.
    intros.
    inductT t; simplT; auto.
  Qed.

End LambdaTerm.

Module LambdaRen := Renamings(LambdaTerm).

Import LambdaTerm.
Import LambdaRen.

(*
 * Simply-typed lambda calculus
 *)

Inductive type := Base | Fn (a b : type).

Reserved Notation "Γ '⊢' e '~' A" (at level 60).
Inductive types (Γ : @context type) : @term 0 -> type -> Prop :=
| VAR x {A} :
   Γ ∋ x ~ A
   ->
   Γ ⊢ vv x ~ A
| BASE k :
   Γ ⊢ const k ~ Base
| LAM body {A B} :
   (forall x, Γ & x ~ A ⊢ open x body ~ B)
   ->
   Γ ⊢ lam body ~ Fn A B
| APP f e {A B} :
   Γ ⊢ f ~ Fn A B ->
   Γ ⊢ e ~ A ->
   Γ ⊢ app f e ~ B
where "Γ '⊢' e '~' A" := (types Γ e A).

Hint Constructors types.

Theorem weakening {Γ e A}:
  Γ ⊢ e ~ A ->
  forall r Δ,
    Γ =[r]=> Δ ->
    Δ ⊢ [r] e ~ A.
Proof.
  induction 1; cbn; intros * rl; eauto.
  - rewrite applyt_related with (rl := rl).
    auto with contexts.
  - constructor; intro.
    names; auto with contexts.
Qed.

Lemma ctx_extend_substitution {Γ Δ x} {A : type} {r} :
  forall_has Γ (fun v B => Δ ⊢ [r] (vv v) ~ B) ->
  forall_has (Γ & x ~ A)
    (fun v B => Δ & x ~ A ⊢ [r,,x] (vv v) ~ B).
Proof.
  intros H.
  apply forall_has_cons; names.
  - 
    apply VAR; names; easy.
  - apply (forall_has_map H); intros; names.
    eauto using weakening with contexts.
Qed.

Theorem substitution {Γ e A} :
  Γ ⊢ e ~ A ->
  forall r Δ,
    forall_has Γ (fun v B => Δ ⊢ [r] (vv v) ~ B) ->
    Δ ⊢ [r] e ~ A.
Proof.
  induction 1; cbn; intros; eauto.
  - constructor; intro v; names.
    eauto using ctx_extend_substitution.
Qed.

Corollary weakening1 Γ e A B x :
  Γ ⊢ e ~ A ->
  Γ & x ~ B ⊢ [^x] e ~ A.
Proof.
  eauto using weakening with contexts.
Qed.

Corollary renaming1 Γ e A B x y :
  Γ & x ~ B ⊢ e ~ A ->
  Γ & y ~ B ⊢ [y <- x] e ~ A.
Proof.
  eauto using weakening with contexts.
Qed.

Corollary renaming1' Γ e A B :
  forall x y,
  Γ & y ~ B ⊢ [y <- x] e ~ A ->
  Γ & x ~ B ⊢ e ~ A.
Proof.
  intros x y.
  replace e with ([x <- y] [y <- x] e) at 2
    by (names; reflexivity).
  apply renaming1.
Qed.

Corollary substitution1 Γ e e' A B x :
  Γ & x ~ B ⊢ e ~ A ->
  Γ ⊢ e' ~ B ->
  Γ ⊢ [e' // x] e ~ A.
Proof.
  intros He He'.
  apply (substitution He).
  apply forall_has_cons.
  - names; auto.
  - intros y b; names; auto.
Qed.

Lemma LAM' x {Γ body} {A B} :
  Γ & x ~ A ⊢ open x body ~ B ->
  Γ ⊢ lam body ~ (Fn A B).
Proof.
  intro H.
  apply LAM.
  intro y.
  apply renaming1' with (y := x); names; easy.
Qed.

Lemma barendregt_substitution_debruijn x y (M : @term 0) (L N : @term 0) :
  distinct_names x y ->
  [L // y] [N // x] M =
  [([L // y] N) // x] [([^x] L) // y] M.
Proof.
  intros.
  names.
  rewrite <- swap_subst_subst_distinct; easy.
Qed.

Inductive Vclosed : @term 0 -> Set :=
| vc_vv v : Vclosed (vv v)
| vc_const n : Vclosed (const n)
| vc_lam t : (forall n, Vclosed (open n t)) -> Vclosed (lam t)
| vc_app f e : Vclosed f -> Vclosed e -> Vclosed (app f e).

Fixpoint Vclosedk (V : nat) : @term V -> Set :=
  match V with
  | 0 => fun t => Vclosed t
  | S V => fun t => forall n, Vclosedk V (open n t)
  end.

Fixpoint always_Vclosedk {V : nat} (t : term) {struct t} : Vclosedk V t :=
  match t with
  | vv v =>
    let fix go {V} : forall (v : @var V), Vclosedk V (vv v) :=
      match V with 0 => vc_vv | S V => fun v n => go _ end in
    go v
  | const n =>
    let fix go {V} : Vclosedk V _ :=
      match V with 0 => vc_const n | S V => fun _ => go end in
    go
  | lam t =>
    let fix go {V} : forall t, Vclosedk (S V) t -> Vclosedk V (lam t) :=
      match V with 0 => vc_lam | S V => fun _ vc a => go _ (vc a) end in
    go _ (always_Vclosedk t)
  | app f e  =>
    let fix go {V} : forall f e, Vclosedk V f -> Vclosedk V e -> Vclosedk V (app f e) :=
      match V with 0 => vc_app | S V => fun _ _ vf ve a => go _ _ (vf a) (ve a) end in
    go _ _ (always_Vclosedk f) (always_Vclosedk e)
  end.

Lemma always_Vclosedk_open x : forall {V} (t : @term (1 + V)),
  always_Vclosedk t x = always_Vclosedk (open x t).
Proof.
  intros.
  inductT t; induction V0; cbn; try easy.
  - rewrite IHt; easy.
  - rewrite IHt; easy.
  - rewrite IHt1, IHt2; try apply heq_intro; easy.
  - rewrite IHt1, IHt2; try apply heq_intro; easy.
Qed.
Hint Rewrite always_Vclosedk_open : rw_names.
Open Scope string.

Notation "'λ' v ~> t" := (lam (close v t)) (at level 60, format "'λ' v  ~>  t").
Notation "f $ e" := (app f e) (at level 59, left associativity).
Notation "! k" := (vv (free k)) (at level 10, format "! k").

Fixpoint cps' {tm : @term 0} (t : Vclosed tm) : @term 0 :=
  match t with
  | vc_vv v =>
    λ"k" ~>
      !"k" $ [^"k"] (vv v)

  | vc_const n =>
    λ"k" ~>
     !"k" $ const n

  | vc_lam _ t =>
    λ"k" ~>
     !"k" $ λ"x" ~>
        [^"k"] (cps' (t "x"))

  | vc_app _ _ f e =>
    λ"k" ~>
       ([^"k"] (cps' f)) $ λ"f" ~>
          ([^"f"] ([^"k"] (cps' e))) $ λ"v" ~>
             !"f" $ !"v" $ !"k"
  end.

Definition cps tm := cps' (@always_Vclosedk 0 tm).

(* 
   Meyer and Wand's theorem about typed CPS transforms
     ("Continuation semantics in typed lambda calculi", 1985)
   This follows Harper and Lillibridge's presentation.
     ("Polymorphic Type Assignment and CPS Conversion", 1992)
 *)

Definition cont R A :=
  Fn (Fn A R) R.

Fixpoint cpsty R A :=
  match A with
  | Base => Base
  | Fn A B => Fn (cpsty R A) (cont R (cpsty R B))
  end.

Fixpoint cpsctx R ctx {struct ctx} :=
  match ctx with
  | ctx_empty => ctx_empty
  | ctx_cons G x A => ctx_cons (cpsctx R G) x (cpsty R A)
  end.

Lemma cpsctx_has {R Γ} :
  forall_has Γ (fun x A => cpsctx R Γ ∋ x ~ cpsty R A).
Proof.
  induction Γ; cbn; auto.
  apply forall_has_cons.
  - names; easy.
  - intros y b; names; auto.
Qed.

Theorem cps_type_preserving {Γ e A R} :
  Γ ⊢ e ~ A ->
  cpsctx R Γ ⊢ cps e ~ cont R (cpsty R A).
Proof.
  induction 1; names; intros; apply (LAM' "k"); cbn.
  - eapply APP; auto with contexts.
    apply VAR; names.
    apply cpsctx_has; auto.
  - eauto with contexts.
  - eapply APP; auto with contexts.
    apply (LAM' "x"); names.
    eapply weakening; eauto. 
    apply relates_swap_right; try easy.
    auto with contexts.
  - eapply APP; names; eauto using weakening with contexts.
    apply (LAM' "f"); names.
    eapply APP; eauto using weakening with contexts.
    apply (LAM' "v"); names.
    eauto 6 with contexts.
Qed.
