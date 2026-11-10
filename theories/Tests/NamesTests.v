(** * Tests of the [names] tactic *)

From Stdlib Require Import String.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Indexed Names.
Open Scope string_scope.

Section Tests.

Context {T : Type}.

(** The binder fragment. *)

Example lift_compose' {N M K} (a : adj T M K) (b : adj T N M) :
  compose (lift a) (lift b) = lift (compose a b).
Proof. names. Qed.

Example lift_lift_compose {N M K} (a : adj T M K) (b : adj T N M) :
  compose (lift (lift a)) (lift (lift b)) = lift (lift (compose a b)).
Proof. names. Qed.

Example lift_weaken {N M} (a : adj T N M) : compose (lift a) (weaken identity) = weaken a.
Proof. names. Qed.

Example lift_identity' {N} : lift (@identity T N) = identity.
Proof. names. Qed.

Example extend_lift {N M} (a : adj T N M) (u : T) :
  compose (extend (Bind u) identity) (lift a) = extend (Bind u) a.
Proof. names. Qed.

Example assoc4 {N M K L P} (a : adj T (S L) P) (b : adj T K L) (c : adj T M K) (d : adj T N (S M)) :
  compose a (compose (lift b) (compose (lift c) d)) = compose (compose a (lift (compose b c))) d.
Proof. names. Qed.

(** Named labels. *)

Example open_close (x : label) : rcompose (ropen x) (rclose x) = @ridentity T.
Proof. names. Qed.

Example close_open (x : label) : rcompose (rclose x) (ropen x) = @ridentity T.
Proof. names. Qed.

Example open_lift {N M} (a : adj T N M) x :
  compose (extend (Rename (fvar x 0)) (weaken_free x identity)) (lift a)
  = extend (Rename (fvar x 0)) (weaken_free x a).
Proof. names. Qed.

Example lift_free_comm {N M} x y (a : adj T N M) :
  label_lt (Some x) (Some y) -> lift_free x (lift_free y a) = lift_free y (lift_free x a).
Proof. intros; names. Qed.

Example lift_free_comm_concrete {N M} (a : adj T N M) :
  lift_free "x" (lift_free "y" a) = lift_free "y" (lift_free "x" a).
Proof. names. Qed.

Example swap_swap (x : label) : rcompose (rswap (Some x)) (rswap (Some x)) = @ridentity T.
Proof. names. Qed.

Example swap_swap_bound : rcompose (rswap None) (rswap None) = @ridentity T.
Proof. names. Qed.

(** Without the order between [x] and [y], the tactic fails. *)
Example lift_free_comm_unknown {N M} x y (a : adj T N M) :
  lift_free x (lift_free y a) = lift_free y (lift_free x a).
Proof. Fail names. Abort.

End Tests.
