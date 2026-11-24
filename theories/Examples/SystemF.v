(** * System F: two scopes, two substitutions

    Types have type variables; terms have type variables and term
    variables, in two scopes: [tm N K] is a term with [N] type variables
    and [K] term variables.  Type substitution acts on types (a [Syntax])
    and on terms, in their first scope (a [Family] over types, one for
    each term scope); it is written [A [a]] on types and [t {{ a }}] on
    terms ([kl_at]). *)

From Stdlib Require Import Arith List StrictProp.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Scoped Indexed Syntax Subst Names.

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
