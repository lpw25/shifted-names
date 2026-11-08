(** * Executable tests for the core

    Concrete adjustments compute, so identities between closed adjustment
    expressions are proved by [vm_compute] on the raw data. *)

From Stdlib Require Import String List PArith.
From ShiftedNames.Core Require Import Trie Label Var Adjustment Laws.
Import ListNotations.
Open Scope string_scope.

Definition renaming := radj Empty_set.

(** Closed equalities are decided by computing the representation. *)
Ltac adj_compute := apply radj_eq; vm_compute; reflexivity.

Example open_close : rcompose (ropen "x") (rclose "x") = ridentity :> renaming.
Proof. adj_compute. Qed.

Example close_open : rcompose (rclose "x") (ropen "x") = ridentity :> renaming.
Proof. adj_compute. Qed.

Example swap_swap : rcompose (rswap (Some "x")) (rswap (Some "x")) = ridentity :> renaming.
Proof. adj_compute. Qed.

Example swap_bound_swap : rcompose (rswap None) (rswap None) = ridentity :> renaming.
Proof. adj_compute. Qed.

Example rlift_identity : rlift None ridentity = ridentity :> renaming.
Proof. adj_compute. Qed.

Example rlift_compose :
  rlift None (rcompose (ropen "x") (rrename1 (Some "y") (Some "z")))
  = rcompose (rlift None (ropen "x")) (rlift None (rrename1 (Some "y") (Some "z"))) :> renaming.
Proof. adj_compute. Qed.

(** Renaming [x] to [y] and then [y] to [z] is renaming [x] to [z]: the
    shift of the old [y]s by the first renaming is undone by the second
    ([rw_ren_rename_rename] on [master]). *)
Example rename_rename :
  rcompose (rrename1 (Some "y") (Some "z")) (rrename1 (Some "x") (Some "y"))
  = rrename1 (Some "x") (Some "z") :> renaming.
Proof. adj_compute. Qed.

Example rename_self : rrename1 (Some "x") (Some "x") = @ridentity Empty_set :> renaming.
Proof. adj_compute. Qed.

(** Targets that were stripped are re-materialised: sending [y] to [x₀]
    after [x₀ ↦ x₀] has collapsed to the identity. *)
Example push_inner_after_strip :
  rapply (rpush_inner (T:=Empty_set) (Some "y") (RRename (mk_rvar (Some "x") 0))
           (rpush_inner (Some "x") (RRename (mk_rvar (Some "x") 0)) (rshift (Some "x"))))
        (mk_rvar (Some "y") 0)
  = inl (mk_rvar (Some "x") 0).
Proof. vm_compute; reflexivity. Qed.

Example push_inner_after_strip_rest :
  rapply (rpush_inner (T:=Empty_set) (Some "y") (RRename (mk_rvar (Some "x") 0))
           (rpush_inner (Some "x") (RRename (mk_rvar (Some "x") 0)) (rshift (Some "x"))))
        (mk_rvar (Some "x") 3)
  = inl (mk_rvar (Some "x") 3).
Proof. vm_compute; reflexivity. Qed.

(** Applying an adjustment to concrete variables. *)
Example apply_open_bound :
  rapply (ropen (T:=Empty_set) "x") (mk_rvar None 0) = inl (mk_rvar (Some "x") 0).
Proof. vm_compute; reflexivity. Qed.

Example apply_open_free :
  rapply (ropen (T:=Empty_set) "x") (mk_rvar (Some "x") 2) = inl (mk_rvar (Some "x") 3).
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

(** Stripping through back-links: [x₀ ↦ x₁] is the only reference to the
    innermost [x] slot, so it is stripped, and [g₀]'s reference to the other
    slot is renumbered (found through that slot's back-links).  The right
    side reaches the same adjustment without stripping. *)
Example strip_renumber :
  rpush_inner (Some "x") (RRename (mk_rvar (Some "x") 1))
    (rpush_inner (Some "g") (RRename (mk_rvar (Some "x") 0))
       (rpush_outer (Some "x") (rpush_outer (Some "x") ridentity)))
  = rpush_inner (Some "g") (RRename (mk_rvar (Some "x") 0)) (rpush_outer (Some "x") ridentity)
  :> renaming.
Proof. adj_compute. Qed.
