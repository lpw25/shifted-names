Require Import Coq.Logic.EqdepFacts.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.

Definition nset := forall (V : nat), Set.

Definition heq {T : nset} : 
  forall {N : nat}, @T N -> forall {M : nat}, @T M -> Prop :=
    eq_dep nat (@T).

Definition heq_intro := eq_dep_intro.

Hint Resolve heq_intro.

Notation " x ~= y " :=
  (heq x y) (at level 70, no associativity).

Definition cast {T : nset} {N M} (pf : N = M) (t : @T N) : @T M :=
  match pf in (_ = L) return (@T L) with
  | eq_refl => t
  end.

Lemma eq_heq : forall {T : nset} {N} {t s : @T N},
    t = s -> t ~= s.
Proof.
  intros T N t s H.
  rewrite H.
  apply eq_dep_intro.
Qed.

Definition heq_eq :
  forall {T : nset} {N} {t s : @T N}, t ~= s -> t = s :=
  eq_dep_eq_dec eq_nat_dec.

Lemma heq_trans :
  forall (T:nset) N M L (t : @T N) (s : @T M) (r : @T L),
    t ~= s -> s ~= r -> t ~= r.
Proof.
  unfold heq.
  eauto using eq_dep_trans.
Qed.

Lemma heq_under : forall T N M t1 t2,
  @heq T (S N) t1 (S M) t2
  <-> @heq (fun V : nat => T (S V)) N t1 M t2.
Proof.
  unfold heq.
  intros T N M t1 t2.
  split; intro H;
    inversion H; subst;
      apply heq_eq in H; subst;
        apply eq_dep_intro.
Qed.    

Definition push_eq N V :=
  nat_ind (fun N' : nat => N' + S V = S (N' + V))
    (@eq_refl nat (S V))
    (fun (N' : nat) (IHn : N' + S V = S (N' + V)) =>
       f_equal_nat nat S (N' + S V) (S (N' + V)) IHn) N.

Definition pop_eq N V := eq_sym (push_eq N V).

Definition nset_push {T : nset} {N V}
           (t : @T (N + S V)) : @T (S (N + V)) :=
  cast (push_eq N V) t.

Definition nset_pop {T : nset} {N V}
           (t : @T (S (N + V))) : @T (N + S V) :=
  cast (pop_eq N V) t.

Lemma nset_push_heq :
  forall (T : nset) N V (t : @T (N + S V)),
    nset_push t ~= t.
Proof.
  intros.
  unfold nset_push, cast.
  destruct (push_eq N V).
  apply eq_dep_intro.
Qed.

Lemma nset_pop_heq :
  forall (T : nset) N V (t : @T (S (N + V))),
    nset_pop t ~= t.
Proof.
  intros.
  unfold nset_pop, cast.
  destruct (pop_eq N V).
  apply eq_dep_intro.
Qed.

Lemma nset_push_pop_eq :
  forall (T : nset) N V (t : @T (S (N + V))),
    nset_push (nset_pop t) = t.
Proof.
  intros T N V t.
  unfold nset_push, nset_pop, cast, pop_eq.
  destruct (push_eq N V); cbn.
  reflexivity.
Qed.

Lemma nset_pop_push_eq :
  forall (T : nset) N V (t : @T (N + S V)),
    nset_pop (nset_push t) = t.
Proof.
  intros T N V t.
  unfold nset_push, nset_pop, cast, pop_eq.
  destruct (push_eq N V); cbn.
  reflexivity.
Qed.

Lemma nset_pop_under : forall T N V t,
  @nset_pop (fun N' : nat => T (S N')) N V t
  = @nset_pop T (S N) V t.
Proof.
  intros.
  apply heq_eq.
  apply heq_trans with (s := t).
  - rewrite heq_under.
    apply nset_pop_heq.
  - apply eq_dep_sym.
    apply nset_pop_heq with (N := S N).
Qed.

Lemma nset_push_under : forall T N V t,
  @nset_push (fun N' : nat => T (S N')) N V t
  = @nset_push T (S N) V t.
Proof.
  intros.
  apply heq_eq.
  apply heq_trans with (s := t).
  - rewrite heq_under.
    apply nset_push_heq.
  - apply eq_dep_sym.
    apply nset_push_heq with (N := S N).
Qed.

Definition morph (T : nset) (N : nat) (S : nset) (M : nat) :=
  forall V, @T (N + V) -> @S (M + V).

Definition morph_inject {T S: nset} {N}
           (f : forall V, @T V -> @S V)
  : morph (@T) N (@S) N := fun V t => f (N + V) t.

Arguments morph_inject {T S N} f /.

Definition morph_id {T N} : morph (@T) N (@T) N :=
  (fun _ t => t).

Arguments morph_id {T N} V t /.

Notation " 1 " := morph_id : morph_scope.

Definition morph_compose {T N S M R L} :
  morph (@S) M (@R) L ->
  morph (@T) N (@S) M ->
  morph (@T) N (@R) L :=
  fun m2 m1 =>
    fun V t => m2 V (m1 V t).

Arguments morph_compose {T N S M R L} m1 m2 V t /.

Notation "m1 @ m2" := (morph_compose m1 m2)
    (at level 60, right associativity)
  : morph_scope.

Bind Scope morph_scope with morph.
Open Scope morph_scope.

Lemma morph_left_identity :
  forall T N S M (f : morph (@T) N (@S) M),
    1 @ f = f.
Proof. reflexivity. Qed.  

Lemma morph_right_identity :
  forall T N S M (f : morph (@T) N (@S) M),
    f @ 1 = f.
Proof. reflexivity. Qed.  

Lemma morph_associative :
  forall T N S M R L U O
     (f : morph (@T) N (@S) M)
     (g : morph (@R) L (@T) N)
     (h : morph (@U) O (@R) L),
    f @ (g @ h) = (f @ g) @ h.
Proof. reflexivity. Qed.

(* Extension *)

Definition morph_extend {T N R L} (m : morph (@T) N (@R) L)
  : morph (@T) (S N) (@R) (S L) :=
  fun V t => nset_push (m (S V) (nset_pop t)).

(* Automation *)

Ltac inductT t :=
  match type of t with
  | context T [?N + ?V] => 
    let t' := fresh "t" in
    let NV := fresh "NV" in
    let Heq := fresh "Heq" in
    let HeqNV := fresh "HeqNV" in
    let V' := fresh "V" in
    remember t as t' eqn:Heq;
      apply eq_heq in Heq;
      remember (N + V) as NV eqn:HeqNV in t, Heq at 2;
      generalize dependent HeqNV;
      generalize dependent t';
      generalize dependent V;
      induction t; intros V' t' Heq HeqNV;
        subst; rewrite (heq_eq Heq); clear Heq; cbn
  | context T [?N + ?V] => 
    fail "unexpected failure"
  | _ =>
    fail "term's type is not of the form '@T (?N + ?V)'"
  end.

Ltac pop_term_arguments t :=
  match t with
  | ?f ?s =>
    match type of s with
    | context T [S (?N + ?V)] =>
      let R :=
        constr:(fun N =>
          ltac:(let y := context T[N] in exact y))
      in
      assert (@nset_pop R N V s ~= s)
        by apply nset_pop_heq;
      generalize dependent (@nset_pop R N V s);
      pop_term_arguments f;
      match goal with
      | Heq : _ ~= s |- _ =>
        rewrite (heq_eq Heq); clear Heq
      end
    | nat =>
      match s with
      | S (?N + ?V) =>
        replace (N + S V) with s
          by apply (pop_eq N V);
        intros
      | _ => pop_term_arguments f
      end
    | _ => pop_term_arguments f
    end
  end.

Ltac popped_term t :=
  match t with
  | ?f ?s =>
    let f' := popped_term f in
    match type of s with
    | context T [S (?N + ?V)] =>
      let R :=
        constr:(fun N =>
          ltac:(let y := context T[N] in exact y))
      in
      constr:(f' (@nset_pop R N V s))
    | nat =>
      match s with
      | S (?N + ?V) => constr:(f' (N + S V))
      | _ => constr:(f' s)
      end
    | _ =>
      constr:(f' s)
    end
  | ?f =>
    constr:(f)
  end.

Ltac popT :=
  cbn in *;
  match goal with
  | |- context T [@nset_pop ?T' ?N ?V ?t] =>
    let t' := popped_term t in
    replace (@nset_pop T' N V t) with t';
      [> | symmetry; apply heq_eq;
           apply eq_dep_trans with (y := t);
           [>apply nset_pop_heq|];
           pop_term_arguments t;
           reflexivity
      ]
  end;
  repeat rewrite nset_pop_under.

Ltac push_term_arguments t :=
  match t with
  | ?f ?s =>
    match type of s with
    | context T [?N + S ?V] =>
      let R :=
        constr:(fun N =>
          ltac:(let y := context T[N] in exact y))
      in
      assert (@nset_push R N V s ~= s)
        by apply nset_push_heq;
      generalize dependent (@nset_push R N V s);
      push_term_arguments f;
      match goal with
      | Heq : _ ~= s |- _ =>
        rewrite (heq_eq Heq); clear Heq
      end
    | nat =>
      match s with
      | (?N + S ?V) =>
        replace (S (N + V)) with s
          by apply (push_eq N V);
        intros
      | _ => push_term_arguments f
      end
    | _ => push_term_arguments f
    end
  end.

Ltac pushed_term t :=
  match t with
  | ?f ?s =>
    let f' := pushed_term f in
    match type of s with
    | context T [?N + S ?V] =>
      let R :=
        constr:(fun N =>
          ltac:(let y := context T[N] in exact y))
      in
      constr:(f' (@nset_push R N V s))
    | nat =>
      match s with
      | (?N + S ?V) => constr:(f' (S (N + V)))
      | _ => constr:(f' s)
      end
    | _ =>
      constr:(f' s)
    end
  | ?f =>
    constr:(f)
  end.

Ltac pushT :=
  cbn in *;
  match goal with
  | |- context T [@nset_push ?T' ?N ?V ?t] =>
    let t' := pushed_term t in
    replace (@nset_push T' N V t) with t';
      [> | symmetry; apply heq_eq;
           apply eq_dep_trans with (y := t);
           [>apply nset_push_heq|];
           push_term_arguments t;
           reflexivity
      ]
  end;
  repeat rewrite nset_push_under.

Ltac simplT :=
  unfold morph_extend in *;
  try popT;
  try pushT;
  repeat
    match goal with
    | IH : forall (_ : nat) (_ : _),
             _ ~= _ -> _ = _ -> _ = _ |- _ =>
      rewrite IH;
      [> |
       match goal with
       | |- @nset_pop ?T' ?N' ?V' ?t' ~= ?t' =>
         apply nset_pop_heq with (N := N')
       | |- ?t' ~= ?t' =>
         apply heq_intro
       end
       | auto ]
    end;
  try rewrite nset_push_pop_eq;
  try rewrite nset_pop_push_eq.

Lemma morph_extend_inject :
  forall (T R : nset) N
         (f : forall V : nat, T V -> R V) V t,
  @morph_extend T N R N (morph_inject f) V t
  = morph_inject f V t.
Proof.
  intros.
  unfold morph_extend, morph_inject.
  pushT.
  rewrite nset_push_pop_eq.
  reflexivity.
Qed.
