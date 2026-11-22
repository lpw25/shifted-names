(** * Lists as Braun trees

    A list as a tree in which looking up the [n]th element, [n] a binary
    number, takes time logarithmic in [n]: the root is the first element,
    the left subtree the elements at odd positions, the right one those
    at even positions after the first.  [names] states what the kernel
    checks with environments as these trees, so that looking an entry up
    when it checks them does not walk a list. *)

From Stdlib Require Import List NArith PArith Pnat.
Import ListNotations.

Inductive braun (A : Type) : Type :=
| BE
| BN (x : A) (l r : braun A).

Arguments BE {A}.
Arguments BN {A} x l r.

Section Braun.

Context {A : Type}.

(** The element at position [p], counting from 1. *)
Fixpoint bget (t : braun A) (p : positive) : option A :=
  match t with
  | BE => None
  | BN x l r => match p with xH => Some x | xO q => bget l q | xI q => bget r q end
  end.

Fixpoint bcons (x : A) (t : braun A) : braun A :=
  match t with BE => BN x BE BE | BN y l r => BN x (bcons y r) l end.

Definition bof (l : list A) : braun A := fold_right bcons BE l.

(** The element at position [n], counting from 0. *)
Definition bnth (t : braun A) (n : N) : option A := bget t (N.succ_pos n).

Lemma bget_bcons_1 x t : bget (bcons x t) 1 = Some x.
Proof. destruct t; reflexivity. Qed.

Lemma bget_bcons_succ x t p : bget (bcons x t) (Pos.succ p) = bget t p.
Proof.
  revert x p; induction t as [|y l IHl r IHr]; intros x p.
  - destruct p; reflexivity.
  - destruct p as [q|q|]; cbn [Pos.succ bcons bget]; [apply IHr|reflexivity|apply bget_bcons_1].
Qed.

Lemma bget_bof l k : bget (bof l) (Pos.of_succ_nat k) = nth_error l k.
Proof.
  revert k; induction l as [|x l IH]; intros k; cbn [bof fold_right].
  - destruct k; reflexivity.
  - destruct k as [|k]; [apply bget_bcons_1|].
    change (Pos.of_succ_nat (S k)) with (Pos.succ (Pos.of_succ_nat k)); rewrite bget_bcons_succ; apply IH.
Qed.

Lemma bnth_bof l n : bnth (bof l) n = nth_error l (N.to_nat n).
Proof.
  unfold bnth; rewrite <- bget_bof; f_equal.
  destruct n as [|p]; [reflexivity|]; cbn [N.succ_pos N.to_nat].
  symmetry; apply Pos2SuccNat.id_succ.
Qed.

End Braun.
