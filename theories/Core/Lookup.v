(** * Lookups with continuations

    [get_with i m k n] looks up [i] in [m] and calls [k x] on the element it
    finds, or [n] if there is none; [nth_with] does the same for lists.  The
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
Import ListNotations.

Section Lookup.

Context {A R : Type}.

Fixpoint get_with' (i : positive) (m : tree' A) {struct m} :
  (forall x, Squash (get' i m = Some x) -> R) -> (Squash (get' i m = None) -> R) -> R :=
  match m as m0
        return (forall x, Squash (get' i m0 = Some x) -> R) -> (Squash (get' i m0 = None) -> R) -> R
  with
  | Node001 r =>
      match i as i0
            return (forall x, Squash (get' i0 (Node001 r) = Some x) -> R) ->
                   (Squash (get' i0 (Node001 r) = None) -> R) -> R with
      | xI j => fun k n => get_with' j r k n
      | xO _ => fun _ n => n (squash eq_refl)
      | xH => fun _ n => n (squash eq_refl)
      end
  | Node010 x =>
      match i as i0
            return (forall y, Squash (get' i0 (Node010 x) = Some y) -> R) ->
                   (Squash (get' i0 (Node010 x) = None) -> R) -> R with
      | xH => fun k _ => k x (squash eq_refl)
      | xO _ => fun _ n => n (squash eq_refl)
      | xI _ => fun _ n => n (squash eq_refl)
      end
  | Node011 x r =>
      match i as i0
            return (forall y, Squash (get' i0 (Node011 x r) = Some y) -> R) ->
                   (Squash (get' i0 (Node011 x r) = None) -> R) -> R with
      | xH => fun k _ => k x (squash eq_refl)
      | xI j => fun k n => get_with' j r k n
      | xO _ => fun _ n => n (squash eq_refl)
      end
  | Node100 l =>
      match i as i0
            return (forall y, Squash (get' i0 (Node100 l) = Some y) -> R) ->
                   (Squash (get' i0 (Node100 l) = None) -> R) -> R with
      | xO j => fun k n => get_with' j l k n
      | xH => fun _ n => n (squash eq_refl)
      | xI _ => fun _ n => n (squash eq_refl)
      end
  | Node101 l r =>
      match i as i0
            return (forall y, Squash (get' i0 (Node101 l r) = Some y) -> R) ->
                   (Squash (get' i0 (Node101 l r) = None) -> R) -> R with
      | xO j => fun k n => get_with' j l k n
      | xI j => fun k n => get_with' j r k n
      | xH => fun _ n => n (squash eq_refl)
      end
  | Node110 l x =>
      match i as i0
            return (forall y, Squash (get' i0 (Node110 l x) = Some y) -> R) ->
                   (Squash (get' i0 (Node110 l x) = None) -> R) -> R with
      | xO j => fun k n => get_with' j l k n
      | xH => fun k _ => k x (squash eq_refl)
      | xI _ => fun _ n => n (squash eq_refl)
      end
  | Node111 l x r =>
      match i as i0
            return (forall y, Squash (get' i0 (Node111 l x r) = Some y) -> R) ->
                   (Squash (get' i0 (Node111 l x r) = None) -> R) -> R with
      | xO j => fun k n => get_with' j l k n
      | xH => fun k _ => k x (squash eq_refl)
      | xI j => fun k n => get_with' j r k n
      end
  end.

Definition get_with (i : positive) (m : tree A)
  (k : forall x, Squash (get i m = Some x) -> R) (n : Squash (get i m = None) -> R) : R :=
  match m as m0
        return (forall x, Squash (get i m0 = Some x) -> R) -> (Squash (get i m0 = None) -> R) -> R
  with
  | Empty => fun _ n => n (squash eq_refl)
  | Nodes m' => fun k n => get_with' i m' k n
  end k n.

Fixpoint nth_with (i : nat) (l : list A) {struct l} :
  (forall x, Squash (nth_error l i = Some x) -> R) -> (Squash (nth_error l i = None) -> R) -> R :=
  match l as l0
        return (forall x, Squash (nth_error l0 i = Some x) -> R) ->
               (Squash (nth_error l0 i = None) -> R) -> R
  with
  | [] => fun _ n => n (squash (nth_error_nil A i))
  | x :: l' =>
      match i as i0
            return (forall y, Squash (nth_error (x :: l') i0 = Some y) -> R) ->
                   (Squash (nth_error (x :: l') i0 = None) -> R) -> R with
      | 0 => fun k _ => k x (squash eq_refl)
      | S i' => fun k n => nth_with i' l' k n
      end
  end.

(** ** Specifications

    The location proofs are strict propositions, so the continuation cannot
    tell which proof it was given. *)

Lemma get_with'_some i m k n x (H : get' i m = Some x) : get_with' i m k n = k x (squash H).
Proof.
  revert i k n H; induction m; intros [j|j|] k n H; cbn in H |- *; try discriminate;
    try (injection H as <-; reflexivity); auto.
Qed.

Lemma get_with'_none i m k n (H : get' i m = None) : get_with' i m k n = n (squash H).
Proof.
  revert i k n H; induction m; intros [j|j|] k n H; cbn in H |- *; try discriminate;
    try reflexivity; auto.
Qed.

Lemma get_with_some i m k n x (H : get i m = Some x) : get_with i m k n = k x (squash H).
Proof. destruct m as [|m]; [discriminate|apply get_with'_some]. Qed.

Lemma get_with_none i m k n (H : get i m = None) : get_with i m k n = n (squash H).
Proof. destruct m as [|m]; [reflexivity|apply get_with'_none]. Qed.

Lemma nth_with_some i l k n x (H : nth_error l i = Some x) : nth_with i l k n = k x (squash H).
Proof.
  revert i k n H; induction l as [|y l IH]; intros [|i] k n H; cbn in H |- *;
    try discriminate; [injection H as <-; reflexivity|apply IH].
Qed.

Lemma nth_with_none i l k n (H : nth_error l i = None) : nth_with i l k n = n (squash H).
Proof.
  revert i k n H; induction l as [|y l IH]; intros [|i] k n H; cbn in H |- *;
    try discriminate; [reflexivity|reflexivity|apply IH].
Qed.

End Lookup.
