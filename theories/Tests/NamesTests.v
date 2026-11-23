(** * Tests of the context-form notation and the [names] tactic *)

From Stdlib Require Import String StrictProp.
From ShiftedNames.Core Require Import Label Var Adjustment Indexed Names.
Open Scope string_scope.

Section Tests.

Context {T : nat -> Type}.

(** ** The notation *)

(** A lift in the short form is the full form with the label linked
    positionally, or through a named slot. *)
Example lift_full {N M} (a : adj T N M) : ⟦ · | a ⟧ = ⟦ · | Γ \ · | Γ[a] ⟧.
Proof. reflexivity. Qed.

Example lift_named {N M} x (a : adj T N M) : ⟦ x | a ⟧ = ⟦ x as b | Γ \ x as b | Γ[a] ⟧.
Proof. reflexivity. Qed.

(** Positional entries pair up in order, innermost first. *)
Example positional {N M} x y (a : adj T N M) :
  ⟦ x; · | Γ \ y; · | Γ[a] ⟧ = ⟦ x as p; · as q | Γ \ y as p; · as q | Γ[a] ⟧.
Proof. reflexivity. Qed.

(** Slots are positions in the output context, of type [slot K]; tail
    names are local to their context form.  A variable is not a slot, and
    outside can stand for one. *)
Fail Definition var_not_slot := (fun (c : var 0) => (⟦ "x" as c \ "x" as d ⟧ : adj T 0 0)).
Fail Check (fun (W : Type) (Δ : W) (σ : adj T 0 0) => ⟦ "x" | Δ \ "y" | Γ[σ] ⟧).
Fail Check (fun (σ : adj T 0 0) => ⟦ "x" | tt \ "y" | Γ[σ] ⟧).
Fail Check (fun (u : T 0) => (⟦ "y" := u⟨ "x" as c ⟩ ⟧ : adj T 0 0)).

(** ** The binder fragment *)

Example lift_compose' {N M K} (a : adj T M K) (b : adj T N M) :
  ⟦ · | b ⟧ ⨾ ⟦ · | a ⟧ = ⟦ · | b ⨾ a ⟧.
Proof. names; reflexivity. Qed.

Example lift_lift_compose {N M K} (a : adj T M K) (b : adj T N M) :
  ⟦ ·; · | b ⟧ ⨾ ⟦ ·; · | a ⟧ = ⟦ ·; · | b ⨾ a ⟧.
Proof. names; reflexivity. Qed.

Example lift_weaken {N M} (a : adj T N M) : ⟦ \ · as _ ⟧ ⨾ ⟦ · | a ⟧ = ⟦ | Γ \ · as _ | Γ[a] ⟧.
Proof. names; reflexivity. Qed.

Example lift_identity' {N} : ⟦ · | @identity T N ⟧ = ⟦⟧.
Proof. names; reflexivity. Qed.

Example instantiate_lift {N M} (a : adj T N M) (u : T M) :
  ⟦ · | a ⟧ ⨾ ⟦ · := u ⟧ = ⟦ · := u | a ⟧.
Proof. names; reflexivity. Qed.

Example assoc4 {N M K L P} (a : adj T (S L) P) (b : adj T K L) (c : adj T M K) (d : adj T N (S M)) :
  d ⨾ (⟦ · | c ⟧ ⨾ (⟦ · | b ⟧ ⨾ a)) = d ⨾ ⟦ · | c ⨾ b ⟧ ⨾ a.
Proof. names; reflexivity. Qed.

(** ** Named labels *)

Example open_close {N} (x : label) : ⟦ x \ · ⟧ ⨾ ⟦ · \ x ⟧ = @identity T N.
Proof. names; reflexivity. Qed.

Example close_open {N} (x : label) : ⟦ · \ x ⟧ ⨾ ⟦ x \ · ⟧ = @identity T (S N).
Proof. names; reflexivity. Qed.

Example open_lift {N M} (a : adj T N M) x : ⟦ · | a ⟧ ⨾ ⟦ · \ x ⟧ = ⟦ · | Γ \ x | Γ[a] ⟧.
Proof. names; reflexivity. Qed.

Example lift_free_comm {N M} x y (a : adj T N M) :
  label_lt x y -> ⟦ x; y | a ⟧ = ⟦ y; x | a ⟧.
Proof. intros; names; reflexivity. Qed.

Example lift_free_comm_concrete {N M} (a : adj T N M) : ⟦ "x"; "y" | a ⟧ = ⟦ "y"; "x" | a ⟧.
Proof. names; reflexivity. Qed.

(** A term substituted before an atom is shown before it, though the
    normal form carries it past. *)
Example term_before_atom {N M} x (u : T N) (s : adj T N M) : ⟦ x := u ⟧ ⨾ ⟦⟧ ⨾ s = ⟦ x := u ⟧ ⨾ s.
Proof. names; reflexivity. Qed.

Example term_before_atoms {N M} x (u : T N) (s : adj T N M) (t : adj T M M) :
  ⟦ x := u ⟧ ⨾ ⟦⟧ ⨾ s ⨾ t = ⟦ x := u ⟧ ⨾ (s ⨾ t).
Proof. names; reflexivity. Qed.

Example term_before_lifted_atom {N M} x y (u : T N) (s : adj T N M) :
  ⟦ x | ⟦ y := u ⟧ ⨾ ⟦⟧ ⨾ s ⟧ = ⟦ x | ⟦ y := u ⟧ ⨾ s ⟧.
Proof. names; reflexivity. Qed.

Example bound_term_before_atom {N M} (u : T N) (s : adj T N M) : ⟦ · := u ⟧ ⨾ ⟦⟧ ⨾ s = ⟦ · := u ⟧ ⨾ s.
Proof. names; reflexivity. Qed.

(** Substitutions one after another: each term's payload is what follows
    it. *)
Example subst_chain {N} x1 x2 x3 (u1 u2 u3 : T N) :
  label_lt x1 x2 -> label_lt x2 x3 ->
  (⟦ x1 := u1 ⟧ ⨾ ⟦ x2 := u2 ⟧ ⨾ ⟦ x3 := u3 ⟧ : adj T N N)
  = ⟦ x3 := u3; x2 := u2⟨ x3 := u3 ⟩; x1 := u1⟨ x3 := u3; x2 := u2⟨ x3 := u3 ⟩ ⟩ \ ⟧.
Proof. intros; names; reflexivity. Qed.

(** The payload's labels are compared with the label substituted for. *)
Example payload_entries_commute {N} x y z (u v w : T N) :
  label_lt x y -> label_lt y z ->
  (⟦ z := w⟨ x := u; y := v ⟩ \ ⟧ : adj T N N) = ⟦ z := w⟨ y := v; x := u ⟩ \ ⟧.
Proof. intros; names; reflexivity. Qed.

(** A long chain is normalised with each term written once (the
    normal form shares it), and shown as a chain of compositions, however
    it was nested. *)
Example long_chain {N} x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 : T N) :
  label_lt x1 x2 -> label_lt x2 x3 -> label_lt x3 x4 -> label_lt x4 x5 ->
  label_lt x5 x6 -> label_lt x6 x7 -> label_lt x7 x8 -> label_lt x8 x9 ->
  label_lt x9 x10 -> label_lt x10 x11 -> label_lt x11 x12 ->
  ((((((((((((⟦ x1 := u1 ⟧ ⨾ ⟦ x2 := u2 ⟧) ⨾ ⟦ x3 := u3 ⟧) ⨾ ⟦ x4 := u4 ⟧) ⨾ ⟦ x5 := u5 ⟧) ⨾ ⟦ x6 := u6 ⟧) ⨾ ⟦ x7 := u7 ⟧) ⨾ ⟦ x8 := u8 ⟧) ⨾ ⟦ x9 := u9 ⟧) ⨾ ⟦ x10 := u10 ⟧) ⨾ ⟦ x11 := u11 ⟧) ⨾ ⟦ x12 := u12 ⟧) : adj T N N)
  = (⟦ x1 := u1 ⟧ ⨾ (⟦ x2 := u2 ⟧ ⨾ (⟦ x3 := u3 ⟧ ⨾ (⟦ x4 := u4 ⟧ ⨾ (⟦ x5 := u5 ⟧ ⨾ (⟦ x6 := u6 ⟧ ⨾ (⟦ x7 := u7 ⟧ ⨾ (⟦ x8 := u8 ⟧ ⨾ (⟦ x9 := u9 ⟧ ⨾ (⟦ x10 := u10 ⟧ ⨾ (⟦ x11 := u11 ⟧ ⨾ ⟦ x12 := u12 ⟧))))))))))).
Proof. intros; names; reflexivity. Qed.

(** Entries sharing a payload are shown as one form composed with it,
    so a chain of two-entry substitutions stays linear. *)
Example pair_chain {N} x y (u1 v1 u2 v2 u3 v3 u4 v4 u5 v5 u6 v6 : T N) :
  label_lt x y ->
  (((((⟦ x := u1; y := v1 ⟧ ⨾ ⟦ x := u2; y := v2 ⟧) ⨾ ⟦ x := u3; y := v3 ⟧) ⨾ ⟦ x := u4; y := v4 ⟧) ⨾ ⟦ x := u5; y := v5 ⟧) ⨾ ⟦ x := u6; y := v6 ⟧ : adj T N N)
  = ⟦ x := u1; y := v1 ⟧ ⨾ (⟦ x := u2; y := v2 ⟧ ⨾ (⟦ x := u3; y := v3 ⟧ ⨾ (⟦ x := u4; y := v4 ⟧ ⨾ (⟦ x := u5; y := v5 ⟧ ⨾ ⟦ x := u6; y := v6 ⟧)))).
Proof. intros; names; reflexivity. Qed.

Example long_chain_left_alone {N} x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 : T N) (P : adj T N N -> Prop) :
  label_lt x1 x2 -> label_lt x2 x3 -> label_lt x3 x4 -> label_lt x4 x5 ->
  label_lt x5 x6 -> label_lt x6 x7 -> label_lt x7 x8 -> label_lt x8 x9 ->
  label_lt x9 x10 -> label_lt x10 x11 -> label_lt x11 x12 ->
  P (((((((((((⟦ x1 := u1 ⟧ ⨾ ⟦ x2 := u2 ⟧) ⨾ ⟦ x3 := u3 ⟧) ⨾ ⟦ x4 := u4 ⟧) ⨾ ⟦ x5 := u5 ⟧) ⨾ ⟦ x6 := u6 ⟧) ⨾ ⟦ x7 := u7 ⟧) ⨾ ⟦ x8 := u8 ⟧) ⨾ ⟦ x9 := u9 ⟧) ⨾ ⟦ x10 := u10 ⟧) ⨾ ⟦ x11 := u11 ⟧) ⨾ ⟦ x12 := u12 ⟧) ->
  P (((((((((((⟦ x1 := u1 ⟧ ⨾ ⟦ x2 := u2 ⟧) ⨾ ⟦ x3 := u3 ⟧) ⨾ ⟦ x4 := u4 ⟧) ⨾ ⟦ x5 := u5 ⟧) ⨾ ⟦ x6 := u6 ⟧) ⨾ ⟦ x7 := u7 ⟧) ⨾ ⟦ x8 := u8 ⟧) ⨾ ⟦ x9 := u9 ⟧) ⨾ ⟦ x10 := u10 ⟧) ⨾ ⟦ x11 := u11 ⟧) ⨾ ⟦ x12 := u12 ⟧).
Proof. intros; names; assumption. Qed.

(** A chain of facts is followed without trying every fact at every step
    (this took 16 seconds when [&&] made the search eager). *)
Example many_labels {N M} x1 x2 x3 x4 x5 x6 x7 x8 (a : adj T N M) :
  label_lt x1 x2 -> label_lt x2 x3 -> label_lt x3 x4 -> label_lt x4 x5 ->
  label_lt x5 x6 -> label_lt x6 x7 -> label_lt x7 x8 ->
  ⟦ x8; x7; x6; x5; x4; x3; x2; x1 | a ⟧ = ⟦ x1; x2; x3; x4; x5; x6; x7; x8 | a ⟧.
Proof. intros; names; reflexivity. Qed.

(** The order of [x] and [y] goes through the concrete labels between
    them. *)
Example lift_free_comm_through {N M} x y (a : adj T N M) :
  label_lt x "m" -> label_lt "n" y -> ⟦ x; y | a ⟧ = ⟦ y; x | a ⟧.
Proof. intros; names; reflexivity. Qed.

Example two_labels {N M} x y (a : adj T N M) :
  label_lt x y -> ⟦ x as p; y as q | Γ \ x as p; y as q | Γ[a] ⟧ = ⟦ y as q; x as p | Γ \ y as q; x as p | Γ[a] ⟧.
Proof. intros; names; reflexivity. Qed.

Example swap_swap {N} (x : label) :
  ⟦ x as b; x as a \ x as a; x as b ⟧ ⨾ ⟦ x as b; x as a \ x as a; x as b ⟧ = @identity T N.
Proof. names; reflexivity. Qed.

Example swap_swap_bound {N} :
  ⟦ · as b; · as a \ · as a; · as b ⟧ ⨾ ⟦ · as b; · as a \ · as a; · as b ⟧ = @identity T (S (S N)).
Proof. names; reflexivity. Qed.

(** Without the order between [x] and [y], the two sides have different
    normal forms; a case analysis on [label_compare] supplies the order. *)
Example lift_free_comm_cases {N M} x y (a : adj T N M) : ⟦ x; y | a ⟧ = ⟦ y; x | a ⟧.
Proof.
  names.
  destruct (label_compare_spec x y) as [<-|H|H]; names; reflexivity.
Qed.

(** ** Applying adjustments to variables *)

Example apply_open {N} (x : label) : apply_var (⟦ · \ x ⟧ : adj T (S N) N) bvar0 = Rename x.
Proof. names; reflexivity. Qed.

Example apply_open_shift {N} (x : label) : apply_var (⟦ · \ x ⟧ : adj T (S N) N) (fvar x 1) = Rename (fvar x 2).
Proof. names; reflexivity. Qed.

Example apply_composite {N} (x y : label) :
  label_lt x y -> apply_var (⟦ y \ x ⟧ ⨾ ⟦ x \ y ⟧ : adj T N N) (fvar y 0) = Rename y.
Proof. intros; names; reflexivity. Qed.

End Tests.

(** Slots are positions: written by number they mean the same as named
    ones. *)
Notation N0 := (fun _ : nat => nat).

(** Constants, as a family of terms of every scope. *)
Definition C (K : nat) : Type := nat.
Example slot_by_number : (⟦ "x" as (mk_slot 1 0 stt) \ "y" as _ ⟧ : adj N0 0 0) = ⟦ "x" \ "y" ⟧.
Proof. names; reflexivity. Qed.

(** A term substituted in is in its entry's scope, the output scope of a
    full form, with the identity payload: in [y := u] below, [u]'s [x₀]
    is the output's [x₀]. *)
Example subst_identity_payload :
  match apply (⟦ "x" as c; "y" := (0 : C 0) \ "x" as c ⟧ : adj C 0 0) (fvar "y" 0) with
  | inr (_, ρ) => rapply ρ (mk_rvar (Some "x") 0)
  | inl _ => inl (mk_rvar None 0)
  end = inl (mk_rvar (Some "x") 0).
Proof. vm_compute; reflexivity. Qed.

(** A payload is any adjustment from the term's scope: [u⟨ c ⟩] is
    [u⟨| ⟦ c ⟧ ⟩]. *)
Example payload_form :
  match apply (⟦ "y" := (0 : C 1)⟨ · \ "x" ⟩ \ ⟧ : adj C 0 0) (fvar "y" 0) with
  | inr (u, ρ) => (projT1 u, rapply ρ (mk_rvar None 0))
  | inl _ => (0, inl (mk_rvar None 0))
  end = (1, inl (mk_rvar (Some "x") 0)).
Proof. vm_compute; reflexivity. Qed.

(** Renamings commute with lifts: the lift moves to the label the renaming
    takes the lifted variable from. *)
Section Commute.
Context {T : nat -> Type}.

Example open_commutes_lift {N M} x (σ : adj T N M) : ⟦ · \ x ⟧ ⨾ ⟦ x | σ ⟧ = ⟦ · | σ ⟧ ⨾ ⟦ · \ x ⟧.
Proof. names; reflexivity. Qed.

Example rename_commutes_lift {N M} x y (σ : adj T N M) :
  label_lt x y -> ⟦ x \ y ⟧ ⨾ ⟦ y | σ ⟧ = ⟦ x | σ ⟧ ⨾ ⟦ x \ y ⟧.
Proof. intros; names; reflexivity. Qed.

Example swap_commutes_lift {N M} x y (σ : adj T N M) :
  label_lt x y -> ⟦ x as a; y as b \ y as b; x as a ⟧ ⨾ ⟦ x; y | σ ⟧ = ⟦ x; y | σ ⟧ ⨾ ⟦ x as a; y as b \ y as b; x as a ⟧.
Proof. intros; names; reflexivity. Qed.

End Commute.

(** Lifts are shown grouped: [names] shows both sides below as
    [⟦ · \ x ⟧ ∘ ⟦ · | a ∘ b ⟧]. *)
Example grouped {N M K} x (a : adj N0 M K) (b : adj N0 N M) :
  ⟦ · | b ⟧ ⨾ ⟦ · \ x ⟧ ⨾ ⟦ x | a ⟧ = ⟦ · | b ⨾ a ⟧ ⨾ ⟦ · \ x ⟧.
Proof. names; reflexivity. Qed.
