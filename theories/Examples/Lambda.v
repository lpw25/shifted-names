(** * The λ-calculus as a client of the library

    The user's side is this file's first two sections: an indexed
    inductive, one Kleisli-extension function, and its laws, each a routine
    induction.  Everything about substitution then comes from the library's
    [Subst] functor. *)

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

Module LambdaSyntax <: SYNTAX.

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
    induction t; cbn; try rewrite IHt1, IHt2; try rewrite IHt; try reflexivity.
    unfold unit_m; rewrite ext_var_same; reflexivity.
  Qed.

  Lemma kleisli_assoc N M P (g : morph M P) (f : morph N M) K L (e : ext N P K L) t :
    kleisli (comp_m g f) e t = kleisli g (ext_right M e) (kleisli f (ext_left M e) t).
  Proof.
    revert L e; induction t; intros L e; cbn;
      try rewrite IHt1, IHt2; try rewrite IHt; reflexivity.
  Qed.

End LambdaSyntax.

(** ** Substitution, from the library *)

Module LS := Subst LambdaSyntax.
Import LS.

(** Substitutions: scoped adjustments whose payloads are closed terms. *)
Notation sub N M := (adj (tm 0) N M).

(** Substitution is the library's [subst], an abbreviation for the
    Kleisli extension of its [apply]: [cbn] pushes it through the
    constructors, and [names] does the rest. *)
Example subst_tlam {N M} (a : adj (tm 0) N M) (b : tm (S N)) :
  (tlam b) [a] = tlam b [lift a].
Proof. cbn; names; reflexivity. Qed.

Example subst_two_binders {N M} (a : adj (tm 0) N M) (b c : tm (S (S N))) :
  (tlam (tlam (tapp b c))) [a]
  = tlam (tlam (tapp b [lift (lift a)] c [lift (lift a)])).
Proof. cbn; names; reflexivity. Qed.

(** ** Locally nameless operations

    Opening the innermost bound variable as [x] is [t [⟦ · \ x ⟧]],
    closing [x] is [t [⟦ x \ · ⟧]], and instantiating with a closed term
    [u] is [t [⟦ · := u ⟧]]. *)

Theorem open_close {N} x (t : tm N) : t [⟦ x \ · ⟧] [⟦ · \ x ⟧] = t.
Proof. names; reflexivity. Qed.

Theorem close_open {N} x (t : tm (S N)) : t [⟦ · \ x ⟧] [⟦ x \ · ⟧] = t.
Proof. names; reflexivity. Qed.

(** Opening after substituting under the binder is one substitution. *)
Theorem open_subst_lift {N M} x (a : sub N M) (t : tm (S N)) :
  t [lift a] [⟦ · \ x ⟧] = t [⟦ · | Γ \ x | Γ[a] ⟧].
Proof. names; reflexivity. Qed.

Theorem inst_subst_lift {N M} (u : tm 0) (a : sub N M) (t : tm (S N)) :
  t [lift a] [⟦ · := u ⟧] = t [⟦ · := u | a ⟧].
Proof. names; reflexivity. Qed.

(** Under binders, through applications. *)
Example names_terms {N} x (t : tm (S N)) (u : tm N) :
  (tapp (tlam t) u) [⟦ x \ · ⟧] [⟦ · \ x ⟧] = tapp (tlam t) u.
Proof. names; reflexivity. Qed.

(** Substituting into a variable. *)
Example subst_var {N} x : (tvar bvar0 : tm (S N)) [⟦ · \ x ⟧] = tvar x.
Proof. names; reflexivity. Qed.
