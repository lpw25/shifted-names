(** * System F: two scopes, two substitutions

    Types have type variables; terms have type variables and term
    variables, in two scopes: [tm N K] is a term with [N] type variables
    and [K] term variables.  Type substitution acts on types (a [Syntax])
    and on terms, in their first scope (a [Family] over types, one for
    each term scope); it is written [A [a]] on types and [t {{ a }}] on
    terms ([kl_at]).  Term substitution acts on terms, in their second
    scope (a [Syntax] for each type scope): under a type binder, the
    payloads are weakened past it ([pmap tshift], [PMap]). *)

From Stdlib Require Import Arith List StrictProp.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Scoped Indexed Syntax Subst Names PMap.

(** ** The syntax *)

Inductive ty (N : nat) : Type :=
| tyvar (v : var N)
| tyarr (A B : ty N)
| tyall (B : ty (S N)).

Arguments tyvar {N} v.
Arguments tyarr {N} A B.
Arguments tyall {N} B.

Inductive tm (N K : nat) : Type :=
| tmvar (v : var K)
| lam (A : ty N) (b : tm N (S K))
| app (t u : tm N K)
| tlam (b : tm (S N) K)
| tapp (t : tm N K) (A : ty N).

Arguments tmvar {N K} v.
Arguments lam {N K} A b.
Arguments app {N K} t u.
Arguments tlam {N K} b.
Arguments tapp {N K} t A.

(** ** Types: a syntax *)

Module TySyntax.

  Fixpoint kleisli {N M} (f : morph ty N M) {K L} (e : ext N M K L) (A : ty K) : ty L :=
    match A with
    | tyvar v => f K L e v
    | tyarr A B => tyarr (kleisli f e A) (kleisli f e B)
    | tyall B => tyall (kleisli f (ext_under e) B)
    end.

  Lemma kleisli_var N M (f : morph ty N M) K L (e : ext N M K L) (v : var K) :
    kleisli f e (tyvar v) = f K L e v.
  Proof. reflexivity. Qed.

  Lemma kleisli_ext N M (f g : morph ty N M) :
    (forall K L (e : ext N M K L) v, f K L e v = g K L e v) ->
    forall K L (e : ext N M K L) A, kleisli f e A = kleisli g e A.
  Proof.
    intros H K L e A; revert L e; induction A; intros L e; cbn;
      try rewrite IHA1, IHA2; try rewrite IHA; auto.
  Qed.

  Lemma kleisli_rebase N M (f : morph ty N M) K L K' L' (e1 : ext N M K L) (e2 : ext K L K' L') A :
    kleisli f (ext_app e1 e2) A = kleisli (rebase_m e1 f) e2 A.
  Proof.
    revert L' e2; induction A; intros L' e2; cbn;
      try rewrite IHA1, IHA2; try rewrite <- IHA; reflexivity.
  Qed.

  Lemma kleisli_unit N K (e : ext N N K K) A :
    kleisli (fun K L e v => tyvar (ext_var e v)) e A = A.
  Proof.
    induction A; cbn; try rewrite IHA1, IHA2; try rewrite IHA; try reflexivity.
    rewrite ext_var_same; reflexivity.
  Qed.

  Lemma kleisli_assoc N M P (g : morph ty M P) (f : morph ty N M) K L (e : ext N P K L) A :
    kleisli (fun K L e v => kleisli g (ext_right M e) (f K (ext_mid M e) (ext_left M e) v)) e A
    = kleisli g (ext_right M e) (kleisli f (ext_left M e) A).
  Proof.
    revert L e; induction A; intros L e; cbn;
      try rewrite IHA1, IHA2; try rewrite IHA; reflexivity.
  Qed.

End TySyntax.

#[export] Instance ty_kleisli : Kleisli ty ty := {| Syntax.kleisli := @TySyntax.kleisli |}.
#[export] Instance ty_syntax : Syntax ty := {|
  Syntax.tvar := @tyvar;
  Syntax.kleisli_var := TySyntax.kleisli_var;
  Syntax.kleisli_ext := TySyntax.kleisli_ext;
  Syntax.kleisli_rebase := TySyntax.kleisli_rebase;
  Syntax.kleisli_unit_ := TySyntax.kleisli_unit;
  Syntax.kleisli_assoc_ := TySyntax.kleisli_assoc |}.
Canonical Structure ty_kleisli.
Canonical Structure ty_syntax.

(** ** Terms: a family over types, in their first scope

    The term scope [J] comes first, so that the instance for [J] is
    [tkleisli J], keyed on [tkleisli] for unification. *)

Module TmTy.

  Fixpoint tkleisli {J N M} (f : morph ty N M) {K L} (e : ext N M K L) (t : tm K J) : tm L J :=
    match t with
    | tmvar v => tmvar v
    | lam A b => lam (TySyntax.kleisli f e A) (tkleisli f e b)
    | app t u => app (tkleisli f e t) (tkleisli f e u)
    | tlam b => tlam (tkleisli f (ext_under e) b)
    | tapp t A => tapp (tkleisli f e t) (TySyntax.kleisli f e A)
    end.

  Lemma tkleisli_ext J N M (f g : morph ty N M) :
    (forall K L (e : ext N M K L) v, f K L e v = g K L e v) ->
    forall K L (e : ext N M K L) (t : tm K J), tkleisli f e t = tkleisli g e t.
  Proof.
    intros H K L e t; revert L e; induction t; intros L e; cbn; f_equal; auto;
      apply TySyntax.kleisli_ext; exact H.
  Qed.

  Lemma tkleisli_rebase J N M (f : morph ty N M) K L K' L' (e1 : ext N M K L) (e2 : ext K L K' L') (t : tm K' J) :
    tkleisli f (ext_app e1 e2) t = tkleisli (rebase_m e1 f) e2 t.
  Proof.
    revert L' e2; induction t; intros L' e2; cbn; f_equal; auto;
      try apply TySyntax.kleisli_rebase; rewrite <- IHt; reflexivity.
  Qed.

  Lemma tkleisli_unit J N K (e : ext N N K K) (t : tm K J) : tkleisli unit_m e t = t.
  Proof. induction t; cbn; f_equal; auto; apply TySyntax.kleisli_unit. Qed.

  Lemma tkleisli_assoc J N M P (g : morph ty M P) (f : morph ty N M) K L (e : ext N P K L) (t : tm K J) :
    tkleisli (comp_m g f) e t = tkleisli g (ext_right M e) (tkleisli f (ext_left M e) t).
  Proof.
    revert L e; induction t; intros L e; cbn; f_equal; auto;
      try apply TySyntax.kleisli_assoc; rewrite IHt; reflexivity.
  Qed.

End TmTy.

#[export] Instance tm_ty_kleisli J : Kleisli ty (fun K => tm K J) := {| Syntax.kleisli := @TmTy.tkleisli J |}.
#[export] Instance tm_ty_family J : Family ty (fun K => tm K J) := {|
  fkleisli_ext := TmTy.tkleisli_ext J;
  fkleisli_rebase := TmTy.tkleisli_rebase J;
  fkleisli_unit := TmTy.tkleisli_unit J;
  fkleisli_assoc := TmTy.tkleisli_assoc J |}.
Canonical Structure tm_ty_kleisli.

(** Type substitutions. *)
Notation tsub N M := (adj ty N M).

(** ** Type substitution in terms *)

Example tsub_tlam {N M K} (a : tsub N M) (b : tm (S N) K) :
  (tlam b) {{ a }} = tlam (b {{ lift a }}).
Proof. cbn; names; reflexivity. Qed.

Example tsub_lam {N M K} (a : tsub N M) (A : ty N) (b : tm N (S K)) :
  (lam A b) {{ a }} = lam (A [a]) (b {{ a }}).
Proof. cbn; names; reflexivity. Qed.

Example tsub_id {N K} (t : tm N K) : t {{ ⟦⟧ }} = t.
Proof. names; reflexivity. Qed.

Example tsub_fuse {N M P K} (a : tsub M P) (b : tsub N M) (t : tm N K) :
  t {{ b }} {{ a }} = t {{ b ⨾ a }}.
Proof. names; reflexivity. Qed.

(** Opening a type binder with a name and closing it again. *)
Theorem topen_close {N K} x (t : tm N K) : t {{ ⟦ x \ · ⟧ }} {{ ⟦ · \ x ⟧ }} = t.
Proof. names; reflexivity. Qed.

Theorem tinst_subst_lift {N M K} (A : ty M) (a : tsub N M) (t : tm (S N) K) :
  t {{ lift a }} {{ ⟦ · := A ⟧ }} = t {{ ⟦ · := A | a ⟧ }}.
Proof. names; reflexivity. Qed.

(** Type application of a type abstraction, in the two scopes. *)
Example tbeta {N K} (b : tm (S N) K) (A : ty N) x :
  (tapp (tlam b) A) {{ ⟦ x \ · ⟧ }} {{ ⟦ · \ x ⟧ }} = tapp (tlam b) A.
Proof. names; reflexivity. Qed.

Example tsub_tapp {N M K} (a : tsub N M) (t : tm N K) (A : ty N) :
  (tapp t A) {{ a }} = tapp (t {{ a }}) (A [a]).
Proof. cbn; names; reflexivity. Qed.

(** Payloads are types, substituted like the λ-calculus's terms. *)
Example tsub_mat x y (A B : ty 0) (s : tsub 0 0) (t : tm 0 0) :
  t {{ ⟦ x := A ⟧ }} {{ ⟦ y := B ⟧ }} {{ s }} = t {{ ⟦ x := (A [⟦ y := B ⟧ ⨾ s]); y := (B [s]) | s ⟧ }}.
Proof. names; reflexivity. Qed.

(** ** Terms: a syntax for each type scope

    Going under a type binder, the terms a substitution sends variables to
    are weakened past it: the morphism is mapped by [tshift] ([mmap]).
    Type substitution commutes with term substitution
    ([TmSyntax.tsub_kleisli], by induction, [names] for the type binder),
    which is the law that makes [tshift] a map of syntaxes. *)

(** Weakening a term past a new type binder. *)
Definition tshift {N K} (t : tm N K) : tm (S N) K := t {{ ⟦ \ · as _ ⟧ }}.
Arguments tshift : simpl never.

Module TmSyntax.

  Fixpoint kleisli {N J J'} (f : morph (tm N) J J') {K L} (e : ext J J' K L) (t : tm N K) : tm N L :=
    match t with
    | tmvar v => f K L e v
    | lam A b => lam A (kleisli f (ext_under e) b)
    | app t u => app (kleisli f e t) (kleisli f e u)
    | tlam b => tlam (kleisli (mmap (@tshift N) f) e b)
    | tapp t A => tapp (kleisli f e t) A
    end.

  Lemma kleisli_var N J J' (f : morph (tm N) J J') K L (e : ext J J' K L) (v : var K) :
    kleisli f e (tmvar v) = f K L e v.
  Proof. reflexivity. Qed.

  Lemma kleisli_ext N J J' (f g : morph (tm N) J J') :
    (forall K L (e : ext J J' K L) v, f K L e v = g K L e v) ->
    forall K L (e : ext J J' K L) t, kleisli f e t = kleisli g e t.
  Proof.
    intros H K L e t; revert f g H L e; induction t; intros f g H L e; cbn; f_equal; auto.
    apply IHt; intros; unfold mmap; rewrite H; reflexivity.
  Qed.

  Lemma kleisli_rebase N J J' (f : morph (tm N) J J') K L K' L' (e1 : ext J J' K L) (e2 : ext K L K' L') t :
    kleisli f (ext_app e1 e2) t = kleisli (rebase_m e1 f) e2 t.
  Proof.
    revert f L' e2; induction t; intros f L' e2; cbn; f_equal; auto;
      first [rewrite <- IHt; reflexivity | rewrite IHt; reflexivity].
  Qed.

  Lemma kleisli_unit N J K (e : ext J J K K) (t : tm N K) :
    kleisli (fun K L e v => tmvar (ext_var e v)) e t = t.
  Proof.
    induction t; cbn; f_equal; auto.
    rewrite ext_var_same; reflexivity.
  Qed.

  (** Type substitution commutes with term substitution: the map's law. *)
  Lemma tsub_kleisli N J J' (f : morph (tm N) J J') K L (e : ext J J' K L) (t : tm N K) :
    forall N' (c : tsub N N'), (kleisli f e t) {{ c }} = kleisli (mmap (fun K u => u {{ c }}) f) e (t {{ c }}).
  Proof.
    revert f L e; induction t; intros f L e N' c; cbn.
    - reflexivity.
    - f_equal; apply IHt.
    - f_equal; [apply IHt1|apply IHt2].
    - f_equal.
      rewrite !fkleisli_apply_under, !ext_shift_here.
      etransitivity; [apply (IHt (mmap (@tshift N) f) L e (S N') (lift c))|].
      apply kleisli_ext; intros K' L' e' v; unfold mmap, tshift.
      names; reflexivity.
    - f_equal; apply IHt.
  Qed.

  Lemma kleisli_assoc N J J' P (g : morph (tm N) J' P) (f : morph (tm N) J J') K L (e : ext J P K L) t :
    kleisli (fun K L e v => kleisli g (ext_right J' e) (f K (ext_mid J' e) (ext_left J' e) v)) e t
    = kleisli g (ext_right J' e) (kleisli f (ext_left J' e) t).
  Proof.
    revert f g L e; induction t; intros f g L e; cbn; f_equal; auto.
    rewrite <- IHt; apply kleisli_ext; intros; unfold mmap, tshift; apply tsub_kleisli.
  Qed.

End TmSyntax.

#[export] Instance tm_kleisli N : Kleisli (tm N) (tm N) := {| Syntax.kleisli := @TmSyntax.kleisli N |}.
#[export] Instance tm_syntax N : Syntax (tm N) := {|
  Syntax.tvar := @tmvar N;
  Syntax.kleisli_var := TmSyntax.kleisli_var N;
  Syntax.kleisli_ext := TmSyntax.kleisli_ext N;
  Syntax.kleisli_rebase := TmSyntax.kleisli_rebase N;
  Syntax.kleisli_unit_ := TmSyntax.kleisli_unit N;
  Syntax.kleisli_assoc_ := TmSyntax.kleisli_assoc N |}.
Canonical Structure tm_kleisli.
Canonical Structure tm_syntax.

#[export] Instance tshift_map N : SyntaxMap (@tshift N) := {|
  smap_var := fun K v => eq_refl;
  smap_kleisli := fun J J' f K L e u => TmSyntax.tsub_kleisli N J J' f K L e u (S N) ⟦ \ · as _ ⟧ |}.

(** Term substitutions. *)
Notation sub N K K' := (adj (tm N) K K').

(** ** Term substitution under type binders *)

Example sub_tlam {N K K'} (a : sub N K K') (b : tm (S N) K) : (tlam b) [a] = tlam (b [pmap (@tshift N) a]).
Proof. cbn; names; reflexivity. Qed.

(** The payloads of a concrete substitution are weakened. *)
Example sub_tlam_inst x (u : tm 0 0) (b : tm 1 0) : (tlam b) [⟦ x := u ⟧] = tlam (b [⟦ x := (tshift u) ⟧]).
Proof. cbn; names; reflexivity. Qed.

Example sub_tlam_compose {N K K' K''} (a1 : sub N K K') (a2 : sub N K' K'') (b : tm (S N) K) :
  (tlam b) [a1] [a2] = tlam (b [pmap (@tshift N) (a1 ⨾ a2)]).
Proof. cbn; names; reflexivity. Qed.

Example sub_tlam_lam {N K K'} (a : sub N K K') (A : ty (S N)) (b : tm (S N) (S K)) :
  (tlam (lam A b)) [a] = tlam (lam A (b [lift (pmap (@tshift N) a)])).
Proof. cbn; names; reflexivity. Qed.

(** Instantiating a term binder under a type binder. *)
Example sub_tlam_inst_open x (u : tm 0 0) (b : tm 1 1) :
  (tlam (lam (tyvar bvar0) b)) [⟦ x := u ⟧] = tlam (lam (tyvar bvar0) (b [lift ⟦ x := (tshift u) ⟧])).
Proof. cbn; names; reflexivity. Qed.
