(** * Executable tests for the core

    Concrete adjustments compute, so identities between closed adjustment
    expressions are proved by [vm_compute] on the raw data. *)

From Stdlib Require Import String List PArith.
From ShiftedNames.Core Require Import Trie Label Var RawAdjustment Adjustment.
Import ListNotations.
Open Scope string_scope.

Definition renaming := adjustment Empty_set.

Definition rcompose (a b : renaming) : renaming := compose no_payload a b.
Definition rlift (l : option label) (a : renaming) : renaming := lift no_payload l a.

(** Closed equalities are decided by computing the raw representation. *)
Ltac adj_compute := apply adjustment_eq; vm_compute; reflexivity.

Example open_close : rcompose (open "x") (close "x") = identity.
Proof. adj_compute. Qed.

Example close_open : rcompose (close "x") (open "x") = identity.
Proof. adj_compute. Qed.

Example swap_swap : rcompose (swap (Some "x")) (swap (Some "x")) = identity.
Proof. adj_compute. Qed.

Example swap_bound_swap : rcompose (swap None) (swap None) = identity.
Proof. adj_compute. Qed.

Example lift_identity : rlift None identity = identity.
Proof. adj_compute. Qed.

Example lift_compose :
  rlift None (rcompose (open "x") (rename1 (Some "y") (Some "z")))
  = rcompose (rlift None (open "x")) (rlift None (rename1 (Some "y") (Some "z"))).
Proof. adj_compute. Qed.

(** Renaming [x] to [y] and then [y] to [z] is renaming [x] to [z]: the
    shift of the old [y]s by the first renaming is undone by the second
    ([rw_ren_rename_rename] on [master]). *)
Example rename_rename :
  rcompose (rename1 (Some "y") (Some "z")) (rename1 (Some "x") (Some "y"))
  = rename1 (Some "x") (Some "z").
Proof. adj_compute. Qed.

Example rename_self : rename1 (Some "x") (Some "x") = @identity Empty_set.
Proof. adj_compute. Qed.

(** Applying an adjustment to concrete variables. *)
Example apply_open_bound :
  apply (open (P:=Empty_set) "x") (mk_var None 0) = inl (mk_var (Some "x") 0).
Proof. vm_compute; reflexivity. Qed.

Example apply_open_free :
  apply (open (P:=Empty_set) "x") (mk_var (Some "x") 2) = inl (mk_var (Some "x") 3).
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
