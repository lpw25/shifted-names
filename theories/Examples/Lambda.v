(** * The λ-calculus as a client of the library

    The user's side is this file's first two sections: an indexed
    inductive, one Kleisli-extension function, and its laws, each a routine
    induction.  Everything about substitution then comes from the library's
    [Subst] functor. *)

From Stdlib Require Import Arith List Lia Bool StrictProp.
From ShiftedNames.Core Require Import Label Var Nested Adjustment Laws Scoped Indexed Syntax Subst.

(** ** The syntax *)

Inductive tm : nat -> Type :=
| tvar {N} (v : var N) : tm N
| tconst {N} (n : nat) : tm N
| tapp {N} (t1 t2 : tm N) : tm N
| tlam {N} (b : tm (S N)) : tm N.

Module LambdaSyntax <: SYNTAX.

  Definition term := tm.
  Definition tvar {N} : var N -> term N := @tvar N.

  Definition morph (N M : nat) : Type := forall K L, ext N M K L -> var K -> term L.

  (** The one function: Kleisli extension, structural on terms. *)
  Fixpoint kleisli {N M} (f : morph N M) {K L} (e : ext N M K L) (t : term K) : term L :=
    match t in tm K' return ext N M K' L -> term L with
    | Lambda.tvar v => fun e => f _ _ e v
    | tconst n => fun _ => tconst n
    | tapp t1 t2 => fun e => tapp (kleisli f e t1) (kleisli f e t2)
    | tlam b => fun e => tlam (kleisli f (ext_under e) b)
    end e.

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

(** Going under a binder: by the library's rewrite rules. *)
Theorem subst_tlam {N M} (a : adj (tm 0) N M) (b : tm (S N)) :
  subst a (tlam b) = tlam (subst (lift a) b).
Proof.
  unfold subst; cbn [LambdaSyntax.kleisli].
  rewrite (kleisli_apply_under a ext_here b); reflexivity.
Qed.

Theorem subst_tapp {N M} (a : adj (tm 0) N M) t1 t2 :
  subst a (tapp t1 t2) = tapp (subst a t1) (subst a t2).
Proof. reflexivity. Qed.

Theorem subst_tconst {N M} (a : adj (tm 0) N M) n : subst a (tconst n) = tconst n.
Proof. reflexivity. Qed.

(** Two binders, with no per-binder rule. *)
Example subst_two_binders {N M} (a : adj (tm 0) N M) (b c : tm (S (S N))) :
  subst a (tlam (tlam (tapp b c)))
  = tlam (tlam (tapp (subst (lift (lift a)) b) (subst (lift (lift a)) c))).
Proof.
  unfold subst; cbn [LambdaSyntax.kleisli].
  rewrite !kleisli_apply_under; cbn [ext_shift]; rewrite !kleisli_apply_under.
  reflexivity.
Qed.

Theorem subst_id {N} (t : tm N) : subst identity t = t.
Proof. apply subst_identity. Qed.

Theorem subst_subst {N M P} (a : adj (tm 0) M P) (b : adj (tm 0) N M) (t : tm N) :
  subst a (subst b t) = subst (compose a b) t.
Proof. apply subst_compose. Qed.

(** ** Locally nameless operations *)

(** Open the innermost bound variable as the name [x]; close [x] into a new
    innermost bound variable. *)
Definition open_sub {N} (x : label) : sub (S N) N :=
  extend (Rename (fvar x 0)) (weaken_free x identity).
Definition close_sub {N} (x : label) : sub N (S N) :=
  extend_free x (Rename bvar0) (weaken identity).

Definition topen {N} (x : label) (t : tm (S N)) : tm N := subst (open_sub x) t.
Definition tclose {N} (x : label) (t : tm N) : tm (S N) := subst (close_sub x) t.

Theorem topen_tclose {N} x (t : tm N) : topen x (tclose x t) = t.
Proof.
  unfold topen, tclose; rewrite subst_compose.
  transitivity (subst identity t); [f_equal|apply subst_identity].
  apply adj_eq; apply rcompose_open_close.
Qed.

Theorem tclose_topen {N} x (t : tm (S N)) : tclose x (topen x t) = t.
Proof.
  unfold topen, tclose; rewrite subst_compose.
  transitivity (subst identity t); [f_equal|apply subst_identity].
  apply adj_eq; apply rcompose_close_open.
Qed.

(** Instantiating the innermost bound variable with a closed term. *)
Definition pidentity {M} : padj (tm 0) M := mk_padj (rto_padj nidentity) stt.
Definition inst {N} (u : tm 0) : sub (S N) N := extend (Bind u pidentity) identity.
