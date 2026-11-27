(** * The λ-calculus as a client of the library

    The user's side is this file's first two sections: an indexed
    inductive, one Kleisli-extension function, and its laws, each a routine
    induction.  Everything about substitution then comes from the library
    ([Subst]), given the syntax as instances of [Kleisli] and [Syntax]. *)

From Stdlib Require Import Arith List Lia Bool StrictProp.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Scoped Indexed Syntax Subst Names.

(** ** The syntax *)

(** The scope is a (non-uniform) parameter, not an index: constructors do
    not store it, so extracted terms carry no scope information. *)
Inductive tm (N : nat) : Type :=
| tvar (v : var N)
| tconst (n : nat)
| tapp (t1 t2 : tm N)
| tlam (b : tm (S N)).

Arguments tvar {N} v.
Arguments tconst {N} n.
Arguments tapp {N} t1 t2.
Arguments tlam {N} b.

Module LambdaSyntax.

  Definition term := tm.
  Definition tvar {N} : var N -> term N := @tvar N.

  Definition morph (N M : nat) : Type := forall K L, ext N M K L -> var K -> term L.

  (** The one function: Kleisli extension, structural on terms. *)
  Fixpoint kleisli {N M} (f : morph N M) {K L} (e : ext N M K L) (t : term K) : term L :=
    match t with
    | Lambda.tvar v => f K L e v
    | tconst n => tconst n
    | tapp t1 t2 => tapp (kleisli f e t1) (kleisli f e t2)
    | tlam b => tlam (kleisli f (ext_under e) b)
    end.

  Definition unit_m {N} : morph N N := fun K L e v => tvar (ext_var e v).

  Definition comp_m {N M P} (g : morph M P) (f : morph N M) : morph N P :=
    fun K L e v => kleisli g (ext_right M e) (f K (ext_mid M e) (ext_left M e) v).

  Definition rebase_m {N M K L} (e1 : ext N M K L) (f : morph N M) : morph K L :=
    fun K' L' e v => f K' L' (ext_app e1 e) v.

  (** ** The laws *)

  Lemma kleisli_var N M (f : morph N M) K L (e : ext N M K L) (v : var K) :
    kleisli f e (tvar v) = f K L e v.
  Proof. reflexivity. Qed.

  Lemma kleisli_ext N M (f g : morph N M) :
    (forall K L (e : ext N M K L) v, f K L e v = g K L e v) ->
    forall K L (e : ext N M K L) t, kleisli f e t = kleisli g e t.
  Proof.
    intros H K L e t; revert L e; induction t; intros L e; cbn;
      try rewrite IHt1, IHt2; try rewrite IHt; auto.
  Qed.

  Lemma kleisli_rebase N M (f : morph N M) K L K' L' (e1 : ext N M K L) (e2 : ext K L K' L') t :
    kleisli f (ext_app e1 e2) t = kleisli (rebase_m e1 f) e2 t.
  Proof.
    revert L' e2; induction t; intros L' e2; cbn;
      try rewrite IHt1, IHt2; try rewrite <- IHt; reflexivity.
  Qed.

  Lemma kleisli_unit N K (e : ext N N K K) t : kleisli unit_m e t = t.
  Proof.
    induction t; cbn; try rewrite IHt1, IHt2; try rewrite IHt; reflexivity.
  Qed.

  Lemma kleisli_assoc N M P (g : morph M P) (f : morph N M) K L (e : ext N P K L) t :
    kleisli (comp_m g f) e t = kleisli g (ext_right M e) (kleisli f (ext_left M e) t).
  Proof.
    revert L e; induction t; intros L e; cbn;
      try rewrite IHt1, IHt2; try rewrite IHt; reflexivity.
  Qed.

End LambdaSyntax.

(** ** Substitution, from the library *)

#[export] Instance lambda_kleisli : Kleisli tm tm := {| Syntax.kleisli := @LambdaSyntax.kleisli |}.
#[export] Instance lambda_syntax : Syntax tm := {|
  Syntax.tvar := @tvar;
  Syntax.kleisli_var := LambdaSyntax.kleisli_var;
  Syntax.kleisli_ext := LambdaSyntax.kleisli_ext;
  Syntax.kleisli_rebase := LambdaSyntax.kleisli_rebase;
  Syntax.kleisli_unit_ := LambdaSyntax.kleisli_unit;
  Syntax.kleisli_assoc_ := LambdaSyntax.kleisli_assoc |}.
(** Canonical too: unification finds them from [LambdaSyntax.kleisli] and
    [tvar], so that the library's lemmas rewrite goals as written and as
    [cbn] leaves them. *)
Canonical Structure lambda_kleisli.
Canonical Structure lambda_syntax.

(** Substitutions: scoped adjustments whose payloads are terms of any
    scope. *)
Notation sub N M := (adj tm N M).

(** Instantiating a binder with an open term. *)
Example inst_open :
  (tlam (tapp (tvar (@bvar 3 1 stt)) (tvar bvar0)) : tm 2) [⟦ · := (tapp (tvar bvar0) (tconst 1)) ⟧]
  = (tlam (tapp (tapp (tvar (@bvar 2 1 stt)) (tconst 1)) (tvar bvar0)) : tm 1).
Proof. reflexivity. Qed.

(** The laws, with terms of any scope in substitutions. *)
Example subst_fuse {N M K} (a : sub M K) (b : sub N M) (t : tm N) : t [b] [a] = t [b ⨾ a].
Proof. apply subst_compose. Qed.

Example subst_under {N M} (a : sub N M) (b : tm (S N)) : (tlam b) [a] = tlam (b [lift a]).
Proof. cbn; rewrite kleisli_apply_under; reflexivity. Qed.

Example subst_id {N} (t : tm N) : t [⟦⟧] = t.
Proof. apply subst_identity. Qed.

(** Instantiating with an open term, as a law: the variable gets the term
    with the identity payload. *)
Example inst_var {N} (u : tm N) : (tvar bvar0 : tm (S N)) [⟦ · := u ⟧] = u.
Proof. rewrite subst_tvar_eval; exact (subst_identity u). Qed.

(** ** [names]

    Substitution is the library's [subst], an abbreviation for the
    Kleisli extension of its [apply]: [cbn] pushes it through the
    constructors, and [names] does the rest. *)
Example subst_tlam {N M} (a : sub N M) (b : tm (S N)) :
  (tlam b) [a] = tlam b [lift a].
Proof. cbn; names; reflexivity. Qed.

Example subst_two_binders {N M} (a : sub N M) (b c : tm (S (S N))) :
  (tlam (tlam (tapp b c))) [a]
  = tlam (tlam (tapp b [lift (lift a)] c [lift (lift a)])).
Proof. cbn; names; reflexivity. Qed.

(** Opening the innermost bound variable as [x] is [t [⟦ · \ x ⟧]],
    closing [x] is [t [⟦ x \ · ⟧]], and instantiating with a term [u] is
    [t [⟦ · := u ⟧]]. *)
Theorem open_close {N} x (t : tm N) : t [⟦ x \ · ⟧] [⟦ · \ x ⟧] = t.
Proof. names; reflexivity. Qed.

Theorem close_open {N} x (t : tm (S N)) : t [⟦ · \ x ⟧] [⟦ x \ · ⟧] = t.
Proof. names; reflexivity. Qed.

Theorem open_subst_lift {N M} x (a : sub N M) (t : tm (S N)) :
  t [lift a] [⟦ · \ x ⟧] = t [⟦ · | Γ \ x | Γ[a] ⟧].
Proof. names; reflexivity. Qed.

Theorem inst_subst_lift {N M} (u : tm M) (a : sub N M) (t : tm (S N)) :
  t [lift a] [⟦ · := u ⟧] = t [⟦ · := u | a ⟧].
Proof. names; reflexivity. Qed.

Example names_terms {N} x (t : tm (S N)) (u : tm N) :
  (tapp (tlam t) u) [⟦ x \ · ⟧] [⟦ · \ x ⟧] = tapp (tlam t) u.
Proof. names; reflexivity. Qed.

Example subst_var {N} x : (tvar bvar0 : tm (S N)) [⟦ · \ x ⟧] = tvar x.
Proof. names; reflexivity. Qed.

(** A term that is a variable is substituted as a renaming. *)
Example subst_var_term x y (M : tm 0) : M [⟦ x := (tvar (fvar y 0)) ⟧] = M [⟦ x as (fvar y 0) ⟧].
Proof. names; reflexivity. Qed.

Example subst_var_term_atom x y (M : tm 0) (s : sub 0 0) :
  M [⟦ x := (tvar (fvar y 0)) ⟧ ⨾ s] = M [(⟦ x as (fvar y 0) ⟧ : sub 0 0)] [s].
Proof. names; reflexivity. Qed.

(** A variable that a substitution sends through an atom is left there. *)
Example var_through_atom x y (s : sub 0 0) :
  (tvar (fvar x 0) : tm 0) [⟦ x := (tvar (fvar y 0)) ⟧ ⨾ s] = (tvar (fvar y 0)) [s].
Proof. names; reflexivity. Qed.

(** Substitutions nested in substitutions are converted all the way down. *)
Example nested_var_var x y z (M : tm 0) :
  M [⟦ x := ((tvar (fvar y 0)) [⟦ y := (tvar (fvar z 0)) ⟧]) ⟧] = M [⟦ x as (fvar z 0) ⟧].
Proof. names; reflexivity. Qed.

Example nested_var_term x y (u M : tm 0) (s : sub 0 0) :
  M [⟦ x := ((tvar (fvar y 0)) [⟦ y := u ⟧ ⨾ s]) ⟧] = M [⟦ x := (u [s]) ⟧].
Proof. names; reflexivity. Qed.

(** A payload with an atom in it is materialised. *)
Example mat_atom x y (N L M : tm 0) (s : sub 0 0) :
  M [⟦ x := N ⟧] [⟦ y := L ⟧] [s] = M [⟦ x := (N [⟦ y := L ⟧ ⨾ s]); y := (L [s]) | s ⟧].
Proof. names; reflexivity. Qed.

(** A substitution in a term of a substitution is normalised as part of
    the payload of that term. *)
Example nested_var x y z (u M : tm 0) :
  M [⟦ x := (u [⟦ y := (tvar (fvar z 0)) ⟧]) ⟧] = M [⟦ x := (u [(⟦ y as (fvar z 0) ⟧ : sub 0 0)]) ⟧].
Proof. names; reflexivity. Qed.

Example nested_open_close x y (u N M : tm 0) :
  M [⟦ x := (u [⟦ y := N ⟧ ⨾ ⟦ y \ · ⟧ ⨾ ⟦ · \ y ⟧]) ⟧] = M [⟦ x := (u [⟦ y := N ⟧]) ⟧].
Proof. names; reflexivity. Qed.

Example nested_after x y (u N L M : tm 0) :
  M [⟦ x := (u [⟦ y := N ⟧]) ⟧ ⨾ ⟦ y := L ⟧] = M [⟦ x := (u [⟦ y := N ⟧ ⨾ ⟦ y := L ⟧]); y := L ⟧].
Proof. names; reflexivity. Qed.

(** With open terms: substituting after instantiating, the de Bruijn
    substitution lemma, and opening then substituting for the name. *)
Theorem inst_subst {N M} (u : tm N) (a : sub N M) (t : tm (S N)) :
  t [⟦ · := u ⟧] [a] = t [lift a] [⟦ · := (u [a]) ⟧].
Proof. names; reflexivity. Qed.

Theorem inst_inst {N} (u : tm (S N)) (v : tm N) (t : tm (S (S N))) :
  t [⟦ · := u ⟧] [⟦ · := v ⟧] = t [lift ⟦ · := v ⟧] [⟦ · := (u [⟦ · := v ⟧]) ⟧].
Proof. names; reflexivity. Qed.

Theorem open_inst {N} x (u : tm N) (t : tm (S N)) :
  t [⟦ · \ x ⟧] [⟦ x := u ⟧] = t [⟦ · := u ⟧].
Proof. names; reflexivity. Qed.

(** Barendregt's substitution lemma. *)
Theorem barendregt x y (L N M : tm 0) : label_lt x y ->
  M [⟦ x := N ⟧] [⟦ y := L ⟧] = M [⟦ y := (L [⟦ \ x as _ ⟧]) ⟧] [⟦ x := (N [⟦ y := L ⟧]) ⟧].
Proof. intros; names; reflexivity. Qed.

From Stdlib Require Import String.
Open Scope string_scope.

(** A payload is any adjustment from the term's scope, written [u⟨| σ ⟩],
    or [u⟨ c ⟩] for the context form [⟦ c ⟧]. *)
Example payload_bound :
  (tvar (fvar "x" 0) : tm 0) [⟦ ("x") := (tapp (tvar bvar0) (tvar (fvar "y" 0)) : tm 1)⟨ · := (tconst 7) ⟩ ⟧]
  = tapp (tconst 7) (tvar (fvar "y" 0)).
Proof. reflexivity. Qed.

Example payload_explicit (σ : sub 1 0) (u : tm 1) :
  (⟦ ("x") := u⟨| σ ⟩ ⟧ : sub 0 0) = ⟦ ("x") := u⟨| ⟦ | σ ⟧ ⟩ ⟧.
Proof. reflexivity. Qed.

(** ** Closed terms

    A name for the terms with no bound variables free, the ones a client
    mostly works with. *)
Notation trm := (tm 0).

Example trm_identity (t : trm) : t [⟦⟧] = t.
Proof. apply subst_identity. Qed.

Example trm_names (t u : trm) x :
  (tapp t (tvar (fvar x 0)) : trm) [⟦ x := u ⟧] = tapp (t [⟦ x := u ⟧]) u.
Proof. cbn; names; reflexivity. Qed.
