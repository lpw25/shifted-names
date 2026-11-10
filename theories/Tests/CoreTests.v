(** * Executable tests for the core

    Concrete adjustments compute, so identities between closed adjustment
    expressions are proved by [vm_compute] on the representation. *)

From Stdlib Require Import String List PArith.
From ShiftedNames.Core Require Import Trie Label Var Adjustment Indexed.
Import ListNotations.
Open Scope string_scope.

Notation ren N M := (adj Empty_set N M).

(** Closed equalities are decided by computing the representation. *)
Ltac adj_compute := apply adj_eq, radj_eq; vm_compute; reflexivity.

Notation open_x := (⟦ · \ "x" ⟧ : ren 1 0).
Notation close_x := (⟦ "x" \ · ⟧ : ren 0 1).

Example open_close : open_x ∘ close_x = ⟦⟧.
Proof. adj_compute. Qed.

Example close_open : close_x ∘ open_x = ⟦⟧.
Proof. adj_compute. Qed.

Example swap_swap :
  ⟦ "x" as b; "x" as a \ "x" as a; "x" as b ⟧ ∘ ⟦ "x" as b; "x" as a \ "x" as a; "x" as b ⟧ = ⟦⟧ :> ren 0 0.
Proof. adj_compute. Qed.

Example swap_bound_swap :
  ⟦ · as b; · as a \ · as a; · as b ⟧ ∘ ⟦ · as b; · as a \ · as a; · as b ⟧ = ⟦⟧ :> ren 2 2.
Proof. adj_compute. Qed.

Example lift_identity : lift ⟦⟧ = ⟦⟧ :> ren 1 1.
Proof. adj_compute. Qed.

Example lift_compose :
  lift (open_x ∘ ⟦ "y" \ "z" ⟧) = lift open_x ∘ lift ⟦ "y" \ "z" ⟧.
Proof. adj_compute. Qed.

(** Renaming [x] to [y] and then [y] to [z] is renaming [x] to [z]: the
    shift of the old [y]s by the first renaming is undone by the second
    ([rw_ren_rename_rename] on [master]). *)
Example rename_rename :
  ⟦ "y" \ "z" ⟧ ∘ ⟦ "x" \ "y" ⟧ = ⟦ "x" \ "z" ⟧ :> ren 0 0.
Proof. adj_compute. Qed.

Example rename_self : ⟦ "x" \ "x" ⟧ = ⟦⟧ :> ren 0 0.
Proof. adj_compute. Qed.

(** Targets that were stripped are re-materialised: sending [y] to [x₀]
    after [x₀ ↦ x₀] has collapsed to the identity. *)
Example push_inner_after_strip :
  apply (⟦ "y" as c; "x" as c \ "x" as c ⟧ : ren 0 0) (fvar "y" 0) = inl (mk_rvar (Some "x") 0).
Proof. vm_compute; reflexivity. Qed.

Example push_inner_after_strip_rest :
  apply (⟦ "y" as c; "x" as c \ "x" as c ⟧ : ren 0 0) (fvar "x" 3) = inl (mk_rvar (Some "x") 3).
Proof. vm_compute; reflexivity. Qed.

(** Applying an adjustment to concrete variables. *)
Example apply_open_bound : apply open_x bvar0 = inl (mk_rvar (Some "x") 0).
Proof. vm_compute; reflexivity. Qed.

Example apply_open_free : apply open_x (fvar "x" 2) = inl (mk_rvar (Some "x") 3).
Proof. vm_compute; reflexivity. Qed.

(** ** Trie performance: a few thousand entries under [vm_compute]. *)

Fixpoint build (n : nat) (p : positive) (m : tree nat) : tree nat :=
  match n with
  | O => m
  | S n => build n (Pos.succ p) (set p n m)
  end.

Definition big := build 5000 1 Empty.

Example big_get : get 4000 big = Some 1000.
Proof. vm_compute; reflexivity. Qed.

Example big_size : List.length (elements big) = 5000.
Proof. vm_compute; reflexivity. Qed.

(** Two constructions of the same adjustment, one of which only reaches
    the normal form by stripping targets that pass-through already
    produces, give equal representations. *)
Example strip_renumber :
  ⟦ "x" as b; "g" as a \ "x" as a; "x" as b ⟧ = ⟦ "g" \ "x" ⟧ :> ren 0 0.
Proof. adj_compute. Qed.
