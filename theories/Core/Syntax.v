(** * What a syntax provides

    A user's syntax is an indexed family [term N] (terms with [N] bound
    variables in scope), with variables [tvar : var N -> term N], and one
    function: a Kleisli extension in the style of relative monads
    (Altenkirch, Chapman and Uustalu; [src/Relative.v] on [master]).

    Kleisli extension takes a [morph N M]: something that, under any number
    of extra binders, sends variables to terms.  The extra binders are
    counted by an extension witness [ext N M K L] ("[K] and [L] are [N] and
    [M] under the same number of binders"), so the user's function goes
    under a binder with [ext_under] and never does index arithmetic.

    The laws are the relative-monad laws, each a routine induction on
    terms. *)

From Stdlib Require Import Arith Lia StrictProp.
From ShiftedNames.Core Require Import Label Var Adjustment Scoped Indexed.

(** ** Extension witnesses *)

Inductive ext (N M : nat) : nat -> nat -> Type :=
| ext_here : ext N M N M
| ext_under {K L} : ext N M K L -> ext N M (S K) (S L).

Arguments ext_here {N M}.
Arguments ext_under {N M K L} e.

(** The number of binders a witness stands for.  (Extraction makes the
    witness itself that number.) *)
Fixpoint ext_depth {N M K L} (e : ext N M K L) : nat :=
  match e with
  | ext_here => 0
  | ext_under e' => S (ext_depth e')
  end.

Lemma ext_depth_K {N M K L} (e : ext N M K L) : K = ext_depth e + N.
Proof. induction e; cbn; lia. Qed.

Lemma ext_depth_L {N M K L} (e : ext N M K L) : L = ext_depth e + M.
Proof. induction e; cbn; lia. Qed.

(** Moving the base under one more binder, and back. *)
Fixpoint ext_shift {N M K L} (e : ext N M K L) : ext (S N) (S M) (S K) (S L) :=
  match e with
  | ext_here => ext_here
  | ext_under e' => ext_under (ext_shift e')
  end.

Fixpoint ext_unshift {N M K L} (e : ext (S N) (S M) K L) : ext N M K L :=
  match e with
  | ext_here => ext_under ext_here
  | ext_under e' => ext_under (ext_unshift e')
  end.

Lemma ext_unshift_shift {N M K L} (e : ext N M K L) : ext_unshift (ext_shift e) = ext_under e.
Proof. induction e; cbn; [reflexivity|rewrite IHe; reflexivity]. Qed.

(** Splitting a witness [N ⇝ P] through a middle base [M]. *)
Fixpoint ext_mid {N P K L} (M : nat) (e : ext N P K L) : nat :=
  match e with
  | ext_here => M
  | ext_under e' => S (ext_mid M e')
  end.

Fixpoint ext_left {N P K L} (M : nat) (e : ext N P K L) : ext N M K (ext_mid M e) :=
  match e as e0 in ext _ _ K0 L0 return ext N M K0 (ext_mid M e0) with
  | ext_here => ext_here
  | ext_under e' => ext_under (ext_left M e')
  end.

Fixpoint ext_right {N P K L} (M : nat) (e : ext N P K L) : ext M P (ext_mid M e) L :=
  match e as e0 in ext _ _ K0 L0 return ext M P (ext_mid M e0) L0 with
  | ext_here => ext_here
  | ext_under e' => ext_under (ext_right M e')
  end.

(** Variables move along a witness [N ⇝ N] unchanged. *)
Lemma ext_same_wf {N K L} (e : ext N N K L) v : wf_var K v = true -> wf_var L v = true.
Proof.
  pose proof (ext_depth_K e) as HK; pose proof (ext_depth_L e) as HL.
  assert (K = L) as -> by lia; auto.
Qed.

Definition ext_var {N K L} (e : ext N N K L) (v : var K) : var L :=
  mk_var (var_raw v) (Is_true_s_intro (ext_same_wf e _ (Is_true_s_elim (var_ok v)))).

Lemma ext_var_same {N K} (e : ext N N K K) (v : var K) : ext_var e v = v.
Proof. apply var_eq; reflexivity. Qed.

(** ** The interface *)

Module Type SYNTAX.

  Parameter term : nat -> Type.

  Parameter tvar : forall {N}, var N -> term N.

  Definition morph (N M : nat) : Type := forall K L, ext N M K L -> var K -> term L.

  Parameter kleisli : forall {N M} (f : morph N M) {K L}, ext N M K L -> term K -> term L.

  (** The identity morphism, and Kleisli composition. *)
  Definition unit_m {N} : morph N N := fun K L e v => tvar (ext_var e v).

  Definition comp_m {N M P} (g : morph M P) (f : morph N M) : morph N P :=
    fun K L e v => kleisli g (ext_right M e) (f K (ext_mid M e) (ext_left M e) v).

  (** Re-basing a morphism one binder down. *)
  Definition unshift_m {N M} (f : morph N M) : morph (S N) (S M) :=
    fun K L e v => f K L (ext_unshift e) v.

  Axiom kleisli_var : forall N M (f : morph N M) K L (e : ext N M K L) (v : var K),
    kleisli f e (tvar v) = f K L e v.

  Axiom kleisli_ext : forall N M (f g : morph N M),
    (forall K L (e : ext N M K L) v, f K L e v = g K L e v) ->
    forall K L (e : ext N M K L) t, kleisli f e t = kleisli g e t.

  Axiom kleisli_unshift : forall N M (f : morph N M) K L (e : ext (S N) (S M) K L) t,
    kleisli f (ext_unshift e) t = kleisli (unshift_m f) e t.

  Axiom kleisli_unit : forall N K (e : ext N N K K) t, kleisli unit_m e t = t.

  Axiom kleisli_assoc : forall N M P (g : morph M P) (f : morph N M) K L (e : ext N P K L) t,
    kleisli (comp_m g f) e t = kleisli g (ext_right M e) (kleisli f (ext_left M e) t).

End SYNTAX.
