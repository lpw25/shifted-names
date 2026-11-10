(** * Tests of the context-form notation and the [names] tactic *)

From Stdlib Require Import String.
From ShiftedNames.Core Require Import Label Var Adjustment Indexed Names.
Open Scope string_scope.

Section Tests.

Context {T : Type}.

(** ** The notation *)

(** A lift in the short form is the full form with the label linked
    positionally, or through a named slot. *)
Example lift_full {N M} (a : adj T N M) : ⟦ ·; a ⟧ = ⟦ · | Γ \ · | Γ[a] ⟧.
Proof. reflexivity. Qed.

Example lift_named {N M} x (a : adj T N M) : ⟦ x; a ⟧ = ⟦ x as b | Γ \ x as b | Γ[a] ⟧.
Proof. reflexivity. Qed.

(** Positional entries pair up in order, innermost first. *)
Example positional {N M} x y (a : adj T N M) :
  ⟦ x; · | Γ \ y; · | Γ[a] ⟧ = ⟦ x as p; · as q | Γ \ y as p; · as q | Γ[a] ⟧.
Proof. reflexivity. Qed.

(** A term substituted in is in the scope of the output tail, so it is
    shifted past the slots: its [x₀] is not the slot [c]. *)
Example subst_shifted (u : T) :
  ⟦ "x" as c; "y" := u \ "x" as c ⟧ = (⟦ "x"; "y" := u ⟧ : adj T 0 0).
Proof. names. Qed.


(** ** The binder fragment *)

Example lift_compose' {N M K} (a : adj T M K) (b : adj T N M) :
  ⟦ ·; a ⟧ ∘ ⟦ ·; b ⟧ = ⟦ ·; (a ∘ b) ⟧.
Proof. names. Qed.

Example lift_lift_compose {N M K} (a : adj T M K) (b : adj T N M) :
  ⟦ ·; ·; a ⟧ ∘ ⟦ ·; ·; b ⟧ = ⟦ ·; ·; (a ∘ b) ⟧.
Proof. names. Qed.

Example lift_weaken {N M} (a : adj T N M) : ⟦ ·; a ⟧ ∘ ⟦ \ · as _ ⟧ = ⟦ | Γ \ · as _ | Γ[a] ⟧.
Proof. names. Qed.

Example lift_identity' {N} : ⟦ ·; @identity T N ⟧ = ⟦⟧.
Proof. names. Qed.

Example instantiate_lift {N M} (a : adj T N M) (u : T) :
  ⟦ · := u ⟧ ∘ ⟦ ·; a ⟧ = ⟦ · := u; a ⟧.
Proof. names. Qed.

Example assoc4 {N M K L P} (a : adj T (S L) P) (b : adj T K L) (c : adj T M K) (d : adj T N (S M)) :
  a ∘ (⟦ ·; b ⟧ ∘ (⟦ ·; c ⟧ ∘ d)) = a ∘ ⟦ ·; (b ∘ c) ⟧ ∘ d.
Proof. names. Qed.

(** ** Named labels *)

Example open_close {N} (x : label) : ⟦ · \ x ⟧ ∘ ⟦ x \ · ⟧ = @identity T N.
Proof. names. Qed.

Example close_open {N} (x : label) : ⟦ x \ · ⟧ ∘ ⟦ · \ x ⟧ = @identity T (S N).
Proof. names. Qed.

Example open_lift {N M} (a : adj T N M) x : ⟦ · \ x ⟧ ∘ ⟦ ·; a ⟧ = ⟦ · | Γ \ x | Γ[a] ⟧.
Proof. names. Qed.

Example lift_free_comm {N M} x y (a : adj T N M) :
  label_lt x y -> ⟦ x; y; a ⟧ = ⟦ y; x; a ⟧.
Proof. intros; names. Qed.

Example lift_free_comm_concrete {N M} (a : adj T N M) : ⟦ "x"; "y"; a ⟧ = ⟦ "y"; "x"; a ⟧.
Proof. names. Qed.

Example two_labels {N M} x y (a : adj T N M) :
  label_lt x y -> ⟦ x as p; y as q | Γ \ x as p; y as q | Γ[a] ⟧ = ⟦ y as q; x as p | Γ \ y as q; x as p | Γ[a] ⟧.
Proof. intros; names. Qed.

Example swap_swap {N} (x : label) :
  ⟦ x as b; x as a \ x as a; x as b ⟧ ∘ ⟦ x as b; x as a \ x as a; x as b ⟧ = @identity T N.
Proof. names. Qed.

Example swap_swap_bound {N} :
  ⟦ · as b; · as a \ · as a; · as b ⟧ ∘ ⟦ · as b; · as a \ · as a; · as b ⟧ = @identity T (S (S N)).
Proof. names. Qed.

(** Without the order between [x] and [y], the tactic fails; a case
    analysis on [label_compare] supplies it. *)
Example lift_free_comm_cases {N M} x y (a : adj T N M) : ⟦ x; y; a ⟧ = ⟦ y; x; a ⟧.
Proof.
  Fail names.
  destruct (label_compare_spec x y) as [<-|H|H]; [reflexivity|names|names].
Qed.

End Tests.
