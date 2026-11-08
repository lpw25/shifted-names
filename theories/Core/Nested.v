(** * Nested adjustments with closed payloads and a thinning front

    This is the representation of design D8 (docs/implementation-plan.md).

    - A payload is a pair [(u, ρ)]: [u] is a term with no bound variables,
      opaque to the library, and [ρ] is an adjustment to be applied to it
      lazily.  The library never applies adjustments to terms.
    - An adjustment is [θ ⊕ core]: [core] is a per-label trie (as in
      RawAdjustment.v) whose payloads are themselves [(u, ρ)] pairs, and
      [θ] is a keep/drop word of wrappers around it, read from the outside
      in: a keep is [lift (·)] and a drop is [shift ∘ ·] (both for the
      anonymous label).

    [lift] and weakening by a bound variable just cons onto [θ], so they are
    O(1) and never touch payloads. *)

From Stdlib Require Import Arith List Lia Bool.
From ShiftedNames.Core Require Import Trie Label Var RawAdjustment Thinning.
Import ListNotations.

Inductive nadj (T : Type) : Type :=
| NAdj : thinning -> tree (entry (T * nadj T)) -> nadj T.

Arguments NAdj {T} _ _.

Section Nested.

Context {T : Type}.

Definition payload : Type := (T * nadj T)%type.

Definition front (a : nadj T) : thinning := match a with NAdj θ _ => θ end.
Definition core (a : nadj T) : raw payload := match a with NAdj _ c => c end.

(** Number of keeps in a thinning: the bound inputs it handles itself. *)
Fixpoint keeps (θ : thinning) : nat :=
  match θ with
  | [] => 0
  | true :: θ' => S (keeps θ')
  | false :: θ' => keeps θ'
  end.

(** Moving an output of the core past the [n] slots of the front. *)
Definition shift_out (n : nat) (w : var) : var :=
  match v_label w with
  | None => mk_var None (v_index w + n)
  | Some _ => w
  end.

(** [n] drops in front of a payload's adjustment: shifting it past [n]
    bound variables. *)
Definition shift_payload_adj (n : nat) (ρ : nadj T) : nadj T :=
  match ρ with NAdj θ c => NAdj (repeat false n ++ θ) c end.

Definition post (n : nat) (r : var + payload) : var + payload :=
  match r with
  | inl w => inl (shift_out n w)
  | inr (u, ρ) => inr (u, shift_payload_adj n ρ)
  end.

(** ** Semantics *)

Definition napply (a : nadj T) (v : var) : var + payload :=
  match a with
  | NAdj θ c =>
      match v_label v with
      | None =>
          if Nat.ltb (v_index v) (keeps θ)
          then inl (mk_var None (thin θ (v_index v)))
          else post (length θ) (apply c (mk_var None (v_index v - keeps θ)))
      | Some _ => post (length θ) (apply c v)
      end
  end.

(** ** Lifting and weakening by a bound variable: O(1) *)

Definition nlift (a : nadj T) : nadj T :=
  match a with NAdj θ c => NAdj (true :: θ) c end.

Definition nweaken (a : nadj T) : nadj T :=
  match a with NAdj θ c => NAdj (false :: θ) c end.

Lemma shift_payload_adj_S n ρ :
  shift_payload_adj (S n) ρ = shift_payload_adj 1 (shift_payload_adj n ρ).
Proof. destruct ρ; reflexivity. Qed.

Lemma post_S n r : post (S n) r = post 1 (post n r).
Proof.
  destruct r as [w|[u ρ]]; cbn [post]; [|rewrite shift_payload_adj_S; reflexivity].
  f_equal; destruct w as [[x|] i]; unfold shift_out; cbn; [reflexivity|].
  f_equal; lia.
Qed.

(** [nlift a] is [a] moved under a binder: [None₀] is fixed, everything else
    goes through [a] one level down and comes out shifted by one. *)
Theorem napply_nlift a v :
  napply (nlift a) v
  = match v_label v, v_index v with
    | None, 0 => inl v
    | None, S i => post 1 (napply a (mk_var None i))
    | Some _, _ => post 1 (napply a v)
    end.
Proof.
  destruct a as [θ c]; destruct v as [[x|] [|i]]; cbn [nlift napply v_label v_index];
    cbn [keeps length]; rewrite ?(post_S (length θ)); try reflexivity.
  cbn [Nat.ltb Nat.leb thin].
  destruct (keeps θ) as [|K].
  - replace (S i - 1) with i by lia; rewrite Nat.sub_0_r; reflexivity.
  - destruct (Nat.leb_spec i K) as [H|H].
    + cbn [post]; unfold shift_out; cbn [v_label v_index]; f_equal; f_equal; lia.
    + replace (S i - S (S K)) with (i - S K) by lia; reflexivity.
Qed.

(** [nweaken a] is [a] followed by weakening by one bound variable. *)
Theorem napply_nweaken a v : napply (nweaken a) v = post 1 (napply a v).
Proof.
  destruct a as [θ c]; destruct v as [[x|] i]; cbn [nweaken napply v_label v_index];
    cbn [keeps length]; rewrite ?(post_S (length θ)); try reflexivity.
  destruct (Nat.ltb_spec i (keeps θ)); [|reflexivity].
  cbn [post thin]; f_equal; unfold shift_out; cbn; f_equal; lia.
Qed.

End Nested.
