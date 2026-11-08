(** * Booleans as strict propositions

    [Is_true_s b] is a strict (definitionally proof-irrelevant) proposition
    holding when [b] is [true].  Records that pair data with such a proof
    are equal exactly when their data are equal, and the proof can always
    be turned back into [b = true]. *)

From Stdlib Require Import Bool StrictProp.

Definition Is_true_s (b : bool) : SProp := if b then sUnit else sEmpty.

Definition Is_true_s_intro {b : bool} : b = true -> Is_true_s b :=
  match b with
  | true => fun _ => stt
  | false => fun H => match diff_false_true H with end
  end.

Lemma Is_true_s_elim {b : bool} : Is_true_s b -> b = true.
Proof. destruct b; [reflexivity|intros []]. Qed.
