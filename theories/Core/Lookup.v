(** * Lookups with continuations

    [get_with i m k n] looks up [i] in [m] and calls [k x] on the element it
    finds, or [n] if there is none; [nth_with] does the same for Braun
    trees.  The
    continuation also receives, as a strict proposition, where the element
    was found.

    Two things follow.  A recursive function can recurse on what it finds
    (the guard checker unfolds these definitions and sees a subterm), which
    is how substitution recurses structurally into payloads.  And proofs
    about the result (for example, that a variable is in scope) can be built
    from the location without any runtime test: the location proofs are
    erased by extraction. *)

From Stdlib Require Import PArith List StrictProp.
From ShiftedNames.Core Require Import Trie.
From ShiftedNames.Core Require Braun.
Import Braun(braun, BE, BN).
Import ListNotations.

Lemma sq_sym {X} {a b : X} : Squash (a = b) -> Squash (b = a).
Proof. intros [H]; exact (squash (eq_sym H)). Qed.

Section GetWith.

Context {A R : Type} (i0 : positive) (m0 : tree A)
  (k : forall x, Squash (get i0 m0 = Some x) -> R) (n : Squash (get i0 m0 = None) -> R).

(** The continuation is a fixed parameter; only the (strict) location proof
    is carried down: the subtree being searched answers as [m0] would. *)
Fixpoint get_with' (i : positive) (m : tree' A) {struct m} : Squash (get' i m = get i0 m0) -> R :=
  match m as m1, i as i1 return Squash (get' i1 m1 = get i0 m0) -> R with
  | Node001 r, xI j => fun H => get_with' j r H
  | Node010 x, xH => fun H => k x (sq_sym H)
  | Node011 x _, xH => fun H => k x (sq_sym H)
  | Node011 _ r, xI j => fun H => get_with' j r H
  | Node100 l, xO j => fun H => get_with' j l H
  | Node101 l _, xO j => fun H => get_with' j l H
  | Node101 _ r, xI j => fun H => get_with' j r H
  | Node110 l _, xO j => fun H => get_with' j l H
  | Node110 _ x, xH => fun H => k x (sq_sym H)
  | Node111 l _ _, xO j => fun H => get_with' j l H
  | Node111 _ x _, xH => fun H => k x (sq_sym H)
  | Node111 _ _ r, xI j => fun H => get_with' j r H
  | _, _ => fun H => n (sq_sym H)
  end.

Definition get_with : R :=
  match m0 as m1 return Squash (get i0 m1 = get i0 m0) -> R with
  | Empty => fun H => n (sq_sym H)
  | Nodes m' => fun H => get_with' i0 m' H
  end (squash eq_refl).

End GetWith.

Section NthWith.

Context {A R : Type} (i0 : nat) (t0 : braun A)
  (k : forall x, Squash (Braun.nth i0 t0 = Some x) -> R) (n : Squash (Braun.nth i0 t0 = None) -> R).

Fixpoint nth_with' (i : nat) (t : braun A) {struct t} : Squash (Braun.nth i t = Braun.nth i0 t0) -> R :=
  match t as t1 return Squash (Braun.nth i t1 = Braun.nth i0 t0) -> R with
  | BE => fun H => n (sq_sym H)
  | BN x l r =>
      match i as i1 return Squash (Braun.nth i1 (BN x l r) = Braun.nth i0 t0) -> R with
      | 0 => fun H => k x (sq_sym H)
      | S j =>
          match Nat.even j as b
                return Squash ((if b then Braun.nth (Nat.div2 j) l else Braun.nth (Nat.div2 j) r)
                               = Braun.nth i0 t0) -> R with
          | true => fun H => nth_with' (Nat.div2 j) l H
          | false => fun H => nth_with' (Nat.div2 j) r H
          end
      end
  end.

Definition nth_with : R := nth_with' i0 t0 (squash eq_refl).

End NthWith.

(** ** Specifications

    The location proofs are strict propositions, so the continuation cannot
    tell which proof it was given. *)

Section Specs.

Context {A R : Type}.

Lemma get_with'_some i0 (m0 : tree A) (k : forall x, Squash (get i0 m0 = Some x) -> R) n i m H
  (E : get' i m = get i0 m0) x (X : get i0 m0 = Some x) :
  get_with' i0 m0 k n i m H = k x (squash X).
Proof.
  revert i H E; induction m; intros [j|j|] H E; cbn [get_with'];
    try (apply IHm || apply IHm1 || apply IHm2; exact E); cbn in E; rewrite X in E;
    try discriminate; injection E as ->; reflexivity.
Qed.

Lemma get_with'_none i0 (m0 : tree A) (k : forall x, Squash (get i0 m0 = Some x) -> R) n i m H
  (E : get' i m = get i0 m0) (X : get i0 m0 = None) :
  get_with' i0 m0 k n i m H = n (squash X).
Proof.
  revert i H E; induction m; intros [j|j|] H E; cbn [get_with'];
    try (apply IHm || apply IHm1 || apply IHm2; exact E); cbn in E; rewrite X in E;
    try discriminate; reflexivity.
Qed.

Lemma get_with_some i (m : tree A) (k : forall x, Squash (get i m = Some x) -> R) n x
  (H : get i m = Some x) : get_with i m k n = k x (squash H).
Proof.
  unfold get_with; destruct m as [|m]; [discriminate|].
  exact (get_with'_some i (Nodes m) k n i m _ eq_refl x H).
Qed.

Lemma get_with_none i (m : tree A) (k : forall x, Squash (get i m = Some x) -> R) n
  (H : get i m = None) : get_with i m k n = n (squash H).
Proof.
  unfold get_with; destruct m as [|m]; [reflexivity|].
  exact (get_with'_none i (Nodes m) k n i m _ eq_refl H).
Qed.

Lemma nth_with'_some i0 (t0 : braun A) (k : forall x, Squash (Braun.nth i0 t0 = Some x) -> R) n i t H
  (E : Braun.nth i t = Braun.nth i0 t0) x (X : Braun.nth i0 t0 = Some x) :
  nth_with' i0 t0 k n i t H = k x (squash X).
Proof.
  revert i H E; induction t as [|y l IHl r IHr]; intros [|j] H E; cbn [nth_with'];
    cbn in E; rewrite ?X in E; try discriminate; [injection E as ->; reflexivity|].
  cbn [Braun.nth] in H; revert H E; destruct (Nat.even j); intros H E;
    [apply IHl|apply IHr]; rewrite X; exact E.
Qed.

Lemma nth_with'_none i0 (t0 : braun A) (k : forall x, Squash (Braun.nth i0 t0 = Some x) -> R) n i t H
  (E : Braun.nth i t = Braun.nth i0 t0) (X : Braun.nth i0 t0 = None) :
  nth_with' i0 t0 k n i t H = n (squash X).
Proof.
  revert i H E; induction t as [|y l IHl r IHr]; intros [|j] H E; cbn [nth_with'];
    cbn in E; rewrite ?X in E; try discriminate; try reflexivity.
  cbn [Braun.nth] in H; revert H E; destruct (Nat.even j); intros H E;
    [apply IHl|apply IHr]; rewrite X; exact E.
Qed.

Lemma nth_with_some i (t : braun A) (k : forall x, Squash (Braun.nth i t = Some x) -> R) n x
  (H : Braun.nth i t = Some x) : nth_with i t k n = k x (squash H).
Proof. exact (nth_with'_some i t k n i t _ eq_refl x H). Qed.

Lemma nth_with_none i (t : braun A) (k : forall x, Squash (Braun.nth i t = Some x) -> R) n
  (H : Braun.nth i t = None) : nth_with i t k n = n (squash H).
Proof. exact (nth_with'_none i t k n i t _ eq_refl H). Qed.

End Specs.
