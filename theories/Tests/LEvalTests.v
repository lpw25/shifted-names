(** * Tests of the layered normaliser on reified expressions *)

From Stdlib Require Import List String.
From ShiftedNames.Core Require Import Label Var Adjustment Normalise Layered LEval.
Import ListNotations.
Open Scope string_scope.

Definition O := order_of [].
Definition x := LCon "x".
Definition y := LCon "y".

(** A payload with an atom is kept by its term as a tree; an atom after
    the term joins it. *)
Example payload_atom :
  nf_eq_t O 1 (ACompose (AAtom 1) (AInner x (TBindE 0 (PComp (AAtom 0) PId)) AId))
              (AInner x (TBindE 0 (PComp (ACompose (AAtom 1) (AAtom 0)) PId)) (AAtom 1)) = true.
Proof. vm_compute; reflexivity. Qed.

(** A lift by the bound label inside a payload. *)
Example payload_bound_lift :
  nf_eq_t O 1 (AInner x (TBindE 0 (PComp (ALift LNone (AOuter y AId)) (PAtom 0))) AId)
              (AInner x (TBindE 0 (PComp (AOuter y AId) (PAtom 0))) AId) = true.
Proof. vm_compute; reflexivity. Qed.
