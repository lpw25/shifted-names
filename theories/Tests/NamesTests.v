(** * Tests of the context-form notation and the [names] tactic *)

From Stdlib Require Import String.
From ShiftedNames.Core Require Import Label Var Adjustment Indexed Names.
Open Scope string_scope.

Section Tests.

Context {T : Type}.

(** ** The notation *)

Example print_lift {N M} (a : adj T N M) : lift a = ⟦ · as b ⇒ b : · | a ⟧.
Proof. reflexivity. Qed.

Example print_lift_free {N M} x (a : adj T N M) : lift_free x a = ⟦ x as b ⇒ b : x | a ⟧.
Proof. reflexivity. Qed.

(** A slot is referred to by its identifier, whatever its position. *)
Example slots {N M} x (a : adj T N M) :
  ⟦ x as c, · as b ⇒ c : x, b : ·, _ : x | a ⟧
  = ⟦ x as (fvar x 1), · as bvar0 ⇒ _ : x, _ : ·, _ : x | a ⟧.
Proof. names. Qed.

(** ** The binder fragment *)

Example lift_compose' {N M K} (a : adj T M K) (b : adj T N M) :
  lift a ∘ lift b = lift (a ∘ b).
Proof. names. Qed.

Example lift_lift_compose {N M K} (a : adj T M K) (b : adj T N M) :
  lift (lift a) ∘ lift (lift b) = lift (lift (a ∘ b)).
Proof. names. Qed.

Example lift_weaken {N M} (a : adj T N M) : lift a ∘ weaken ⟦⟧ = weaken a.
Proof. names. Qed.

Example lift_identity' {N} : lift (@identity T N) = ⟦⟧.
Proof. names. Qed.

Example extend_lift {N M} (a : adj T N M) (u : T) :
  ⟦ · := u ⇒ ⟧ ∘ lift a = ⟦ · := u ⇒ | a ⟧.
Proof. names. Qed.

Example assoc4 {N M K L P} (a : adj T (S L) P) (b : adj T K L) (c : adj T M K) (d : adj T N (S M)) :
  a ∘ (lift b ∘ (lift c ∘ d)) = a ∘ lift (b ∘ c) ∘ d.
Proof. names. Qed.

(** ** Named labels *)

Example open_close {N} (x : label) :
  ⟦ · as a ⇒ a : x ⟧ ∘ ⟦ x as b ⇒ b : · ⟧ = @identity T (S N) .
Proof. names. Qed.

Example open_lift {N M} (a : adj T N M) x :
  ⟦ · as c ⇒ c : x ⟧ ∘ lift a = ⟦ · as c ⇒ c : x | a ⟧.
Proof. names. Qed.

Example lift_free_comm {N M} x y (a : adj T N M) :
  label_lt x y -> lift_free x (lift_free y a) = lift_free y (lift_free x a).
Proof. intros; names. Qed.

Example lift_free_comm_concrete {N M} (a : adj T N M) :
  lift_free "x" (lift_free "y" a) = lift_free "y" (lift_free "x" a).
Proof. names. Qed.

(** Two slots with labels whose order is known. *)
Example two_labels {N M} x y (a : adj T N M) :
  label_lt x y -> ⟦ x as p, y as q ⇒ p : x, q : y | a ⟧ = ⟦ y as q, x as p ⇒ q : y, p : x | a ⟧.
Proof. intros; names. Qed.

Example swap_swap {N} (x : label) :
  ⟦ x as b, x as a ⇒ a : x, b : x ⟧ ∘ ⟦ x as b, x as a ⇒ a : x, b : x ⟧ = @identity T N.
Proof. names. Qed.

Example swap_swap_bound {N} :
  ⟦ · as b, · as a ⇒ a : ·, b : · ⟧ ∘ ⟦ · as b, · as a ⇒ a : ·, b : · ⟧ = @identity T (S (S N)).
Proof. names. Qed.

(** Without the order between [x] and [y], the tactic fails; a case
    analysis on [label_compare] supplies it. *)
Example lift_free_comm_cases {N M} x y (a : adj T N M) :
  lift_free x (lift_free y a) = lift_free y (lift_free x a).
Proof.
  Fail names.
  destruct (label_compare_spec x y) as [<-|H|H]; [reflexivity|names|names].
Qed.

End Tests.
