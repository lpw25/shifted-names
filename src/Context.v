Require Import String Morph Var.

Inductive context {A : Set} : Set :=
| ctx_empty
| ctx_cons (Γ : @context A) (a : name) (val : A).

Notation "Γ & x ~ A" := (ctx_cons Γ x A) (at level 50).

Fixpoint has {A} (ctx : @context A) (x : @var 0) (a : A) :=
  match ctx with
  | ctx_empty => False
  | ctx_cons ctx y b =>
    match bindv (closev y x) with
    | None => b = a
    | Some x' => has ctx x' a
    end
  end.

Notation "Γ ∋ x ~ a" := (has Γ x a) (at level 60).

Hint Extern 2 (?Γ ∋ ?x ~ ?a) =>
  solve [cbn; easy] : contexts.

(* TODO this should be done with a renaming now *)
Lemma has_swap {A : Set} {Γ : @context A} {x a y b} :
  distinct_names x y ->
  forall z c,
    ((Γ & y ~ b) & x ~ a) ∋ z ~ c ->
    ((Γ & x ~ a) & y ~ b) ∋ z ~ c.
Proof.
  intros H z c; cbn.
  destruct (compare_vars x z) as [|z'];
    autorewrite with rw_vars; cbn.
  - rewrite (substv_distinct (distinct_names_symmetric H)).
    autorewrite with rw_vars; easy.
  - destruct (compare_vars y z').
    + autorewrite with rw_vars; cbn.
      rewrite rw_shift_name_distinct by easy.
      autorewrite with rw_vars; easy.
    + autorewrite with rw_vars.
      rewrite swap_shiftv_shiftv_distinct by easy.
      autorewrite with rw_vars; easy.
Qed.

Definition forall_has {A : Set} Γ (P : var -> A -> Prop) :=
  (forall x a, Γ ∋ x ~ a -> P x a).

Hint Unfold forall_has.

Lemma forall_has_cons {A : Set} {Γ : @context A}
      {P : var -> A -> Prop} {x a} :
  P (free x) a ->
  forall_has Γ (fun y b => P (shiftv x y) b) ->
  forall_has (Γ & x ~ a) P.
Proof.
  intros Hp Hf y b.
  destruct (compare_vars x y);
    cbn; autorewrite with rw_vars; cbn;
      intros; subst; auto.
Qed.

Lemma forall_has_map {A : Set} {Γ : @context A}
      {P Q : var -> A -> Prop} :
  forall_has Γ P ->
  (forall x a, P x a -> Q x a) ->
  forall_has Γ Q.
Proof.
  unfold forall_has.
  auto.
Qed.

Inductive relates {trm A : Set}
  : @context A -> @renaming trm -> @context A -> Prop :=
  | relates_intro :
      forall (Γ Δ : @context A) (s : @renaming trm)
             (total : total s),
        forall_has Γ (fun v a => has Δ (applyt s total v) a) ->
        relates Γ s Δ.

Definition relates_total {trm A : Set}
           {Γ Δ : @context A} {r : @renaming trm}
           (rl : relates Γ r Δ) :=
  match rl with
  | relates_intro _ _ _ rn _ => rn
  end.

Definition relates_contexts {trm A : Set}
           {Γ Δ : @context A} {r : @renaming trm}
           (rl : relates Γ r Δ) :=
  match rl in relates Γ r' Δ return
    (forall v a, has Γ v a ->
                 has Δ (applyt r' (relates_total rl) v) a) with
  | relates_intro _ _ _ _ cs => cs
  end.

Hint Resolve relates_total relates_contexts : contexts.

Notation "Γ =[ r ]=> Δ" :=
  (relates Γ (r)%ren Δ) (at level 60).

Lemma ctx_shift {trm A : Set} :
  forall Γ Δ x (a : A) (r : @renaming trm),
    Γ =[r]=> Δ ->
    Γ =[r, ^x]=> (Δ & x ~ a).
Proof.
  intros * H.
  destruct H as [? ? r rn H].
  apply relates_intro with (s := (r, ^x)%ren) (total := rn).
  apply (forall_has_map H); intros y b. 
  cbn; autorewrite with rw_vars rw_names.
  auto.
Qed.

Lemma ctx_rename {trm A : Set} :
  forall Γ Δ x y (a : A) (r : @renaming trm),
    Γ =[r]=> Δ ->
    (Γ & x ~ a) =[r, y <- x]=> (Δ & y ~ a).
Proof.
  intros * H.
  destruct H as [? ? r rn H].
  apply relates_intro
    with (s := (r, y <- x)%ren) (total := rn); cbn.
  apply forall_has_cons;
    autorewrite with rw_vars rw_names; cbn; auto.
  apply (forall_has_map H); intros z c. 
  autorewrite with rw_vars rw_names; auto.
Qed.

Lemma ctx_id {trm A : Set} :
  forall (Γ : @context A), Γ =[(r_id : @renaming trm)]=> Γ.
Proof.
  intros.
  apply relates_intro with (total := I).
  easy.
Qed.

Hint Resolve ctx_shift ctx_rename ctx_id : contexts.

Lemma relates_swap_right {trm A : Set} {Γ Δ : @context A}
      {x a y b} {r : @renaming trm}:
  distinct_names x y ->
  Γ =[r]=> Δ & y ~ b & x ~ a ->
  Γ =[r]=> Δ & x ~ a & y ~ b.
Proof.
  intros Heq H.
  inversion H as [? ? ? tl H']; subst.
  apply relates_intro with (total := tl).
  auto using has_swap.
Qed.

Lemma relates_swap_left {trm A : Set} {Γ Δ : @context A}
      {x a y b} {r : @renaming trm}:
  distinct_names y x ->
  Γ & y ~ b & x ~ a =[r]=> Δ ->
  Γ & x ~ a & y ~ b =[r]=> Δ.
Proof.
  intros Heq H.
  inversion H as [? ? ? tl H']; subst.
  apply relates_intro with (total := tl).
  auto using has_swap.
Qed.
