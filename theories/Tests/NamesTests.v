(** * Tests of the context-form notation and the [names] tactic *)

From Stdlib Require Import String StrictProp.
From ShiftedNames.Core Require Import Label Var Adjustment Indexed Names.
Open Scope string_scope.

Section Tests.

Context {T : Type}.

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
Fail Check (fun (c : var 0) => (⟦ "x" as c \ "x" as d ⟧ : adj T 0 0)).
Fail Check (fun (W : Type) (Δ : W) (σ : adj T 0 0) => ⟦ "x" | Δ \ "y" | Γ[σ] ⟧).
Fail Check (fun (σ : adj T 0 0) => ⟦ "x" | tt \ "y" | Γ[σ] ⟧).
Fail Check (fun (u : T) => (⟦ "y" := u⟨ "x" as c ⟩ ⟧ : adj T 0 0)).

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

Example instantiate_lift {N M} (a : adj T N M) (u : T) :
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
Example term_before_atom {N M} x (u : T) (s : adj T N M) : ⟦ x := u ⟧ ⨾ ⟦⟧ ⨾ s = ⟦ x := u ⟧ ⨾ s.
Proof. names; reflexivity. Qed.

Example term_before_atoms {N M} x (u : T) (s : adj T N M) (t : adj T M M) :
  ⟦ x := u ⟧ ⨾ ⟦⟧ ⨾ s ⨾ t = ⟦ x := u ⟧ ⨾ (s ⨾ t).
Proof. names; reflexivity. Qed.

Example term_before_lifted_atom {N M} x y (u : T) (s : adj T N M) :
  ⟦ x | ⟦ y := u ⟧ ⨾ ⟦⟧ ⨾ s ⟧ = ⟦ x | ⟦ y := u ⟧ ⨾ s ⟧.
Proof. names; reflexivity. Qed.

Example bound_term_before_atom {N M} (u : T) (s : adj T N M) : ⟦ · := u ⟧ ⨾ ⟦⟧ ⨾ s = ⟦ · := u ⟧ ⨾ s.
Proof. names; reflexivity. Qed.

(** Substitutions one after another: each term's payload is what follows
    it.  The entries of a payload context are simultaneous: in [u1]'s,
    the names of [u3] are not affected by the entry for [x2]. *)
Example subst_chain {N} x1 x2 x3 (u1 u2 u3 : T) :
  label_lt x1 x2 -> label_lt x2 x3 ->
  (⟦ x1 := u1 ⟧ ⨾ ⟦ x2 := u2 ⟧ ⨾ ⟦ x3 := u3 ⟧ : adj T N N)
  = ⟦ x3 := u3; x2 := u2⟨ x3 := u3 ⟩; x1 := u1⟨ x3 := u3; x2 := u2⟨ x3 := u3 ⟩ ⟩ \ ⟧.
Proof. intros; names; reflexivity. Qed.

Example payload_entries_commute {N} x y z (u v w : T) :
  label_lt x y ->
  (⟦ z := w⟨ x := u; y := v ⟩ \ ⟧ : adj T N N) = ⟦ z := w⟨ y := v; x := u ⟩ \ ⟧.
Proof. intros; names_eq. Qed.

(** A long chain is decided on the stored form, where each payload is
    written once; as a tree the normal form doubles with each step, and
    [names] leaves such a chain as it is.  However it is nested, it is
    normalised from its last step. *)
Example long_chain {N} x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 : T) :
  label_lt x1 x2 -> label_lt x2 x3 -> label_lt x3 x4 -> label_lt x4 x5 ->
  label_lt x5 x6 -> label_lt x6 x7 -> label_lt x7 x8 -> label_lt x8 x9 ->
  label_lt x9 x10 -> label_lt x10 x11 -> label_lt x11 x12 ->
  ((((((((((((⟦ x1 := u1 ⟧ ⨾ ⟦ x2 := u2 ⟧) ⨾ ⟦ x3 := u3 ⟧) ⨾ ⟦ x4 := u4 ⟧) ⨾ ⟦ x5 := u5 ⟧) ⨾ ⟦ x6 := u6 ⟧) ⨾ ⟦ x7 := u7 ⟧) ⨾ ⟦ x8 := u8 ⟧) ⨾ ⟦ x9 := u9 ⟧) ⨾ ⟦ x10 := u10 ⟧) ⨾ ⟦ x11 := u11 ⟧) ⨾ ⟦ x12 := u12 ⟧) : adj T N N)
  = (⟦ x1 := u1 ⟧ ⨾ (⟦ x2 := u2 ⟧ ⨾ (⟦ x3 := u3 ⟧ ⨾ (⟦ x4 := u4 ⟧ ⨾ (⟦ x5 := u5 ⟧ ⨾ (⟦ x6 := u6 ⟧ ⨾ (⟦ x7 := u7 ⟧ ⨾ (⟦ x8 := u8 ⟧ ⨾ (⟦ x9 := u9 ⟧ ⨾ (⟦ x10 := u10 ⟧ ⨾ (⟦ x11 := u11 ⟧ ⨾ ⟦ x12 := u12 ⟧))))))))))).
Proof. intros; names_eq. Qed.

Example long_chain_left_alone {N} x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 : T) (P : adj T N N -> Prop) :
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

(** Without the order between [x] and [y], [names] cannot normalise and
    leaves the goal; a case analysis on [label_compare] supplies it. *)
Example lift_free_comm_cases {N M} x y (a : adj T N M) : ⟦ x; y | a ⟧ = ⟦ y; x | a ⟧.
Proof.
  names.
  destruct (label_compare_spec x y) as [<-|H|H]; [reflexivity|names; reflexivity|names; reflexivity].
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

(** Nested context forms.  A slot is a position, so a slot of the form
    around can be used in a form with as many outputs, where it means that
    position; slots written by number mean the same as named ones.  Tail
    names stay local: an inner form must use its own. *)
Definition T0 := adj nat 0 0.
Definition nested_ok : adj T0 0 0 := ⟦ "y" := (⟦ "z" := 0⟨ "x" as d ⟩ \ "x" as d ⟧ : T0) \ "x" as c ⟧.
Definition nested_position : adj T0 0 0 := ⟦ "y" := (⟦ "x" as c \ "x" as d ⟧ : T0) \ "x" as c ⟧.
Example slot_by_number : (⟦ "x" as (mk_slot 1 0 stt) \ "y" as _ ⟧ : adj nat 0 0) = ⟦ "x" \ "y" ⟧.
Proof. names; reflexivity. Qed.
Fail Definition nested_tail (s : T0) : adj T0 0 0 := ⟦ "y" := (⟦ "x" | Γ \ "x" | Δ[s] ⟧ : T0) | Γ \ "x" | Γ[⟦⟧] ⟧.
Fail Definition slot_in_term : adj (var 0 * nat) 0 0 := ⟦ "y" := (c, 0) \ "x" as c ⟧.

(** A term substituted in is in the scope of the output tail, so it is
    shifted past the slots: in [y := u] below, [u]'s [x₀] is the output's
    [x₁], not the slot [c]. *)
Example subst_shifted :
  match apply (⟦ "x" as c; "y" := 0 \ "x" as c ⟧ : adj nat 0 0) (fvar "y" 0) with
  | inr (_, ρ) => rpapply ρ (mk_rvar (Some "x") 0)
  | inl _ => inl (mk_rvar None 0)
  end = inl (mk_rvar (Some "x") 1).
Proof. vm_compute; reflexivity. Qed.

(** A payload context sends the term's names to slots. *)
Example payload_to_slot :
  match apply (⟦ "y" := 0⟨ "x" as c ⟩ \ "x" as c ⟧ : adj nat 0 0) (fvar "y" 0) with
  | inr (_, ρ) => (rpapply ρ (mk_rvar (Some "x") 0), rpapply ρ (mk_rvar (Some "x") 1))
  | inl _ => (inl (mk_rvar None 0), inl (mk_rvar None 0))
  end = (inl (mk_rvar (Some "x") 0), inl (mk_rvar (Some "x") 1)).
Proof. vm_compute; reflexivity. Qed.

(** Renamings commute with lifts: the lift moves to the label the renaming
    takes the lifted variable from. *)
Section Commute.
Context {T : Type}.

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
Example grouped {N M K} x (a : adj nat M K) (b : adj nat N M) :
  ⟦ · | b ⟧ ⨾ ⟦ · \ x ⟧ ⨾ ⟦ x | a ⟧ = ⟦ · | b ⨾ a ⟧ ⨾ ⟦ · \ x ⟧.
Proof. names; reflexivity. Qed.

(** Two variables passed around an atom and merged after it: a term's
    names sent to either are the same. *)
Example merged_after_atom (σ : adj nat 0 0) (u : nat) :
  (⟦ "z" := u⟨ "y" as c ⟩; "x" as c; "x" as d \ "x" as c; "x" as d ⟧ : adj nat 0 0) ⨾ ⟦ "x"; "x" | σ ⟧ ⨾ ⟦ "x" as c; "x" as c \ "x" as c ⟧
  = (⟦ "z" := u⟨ "y" as d ⟩; "x" as c; "x" as d \ "x" as c; "x" as d ⟧ : adj nat 0 0) ⨾ ⟦ "x"; "x" | σ ⟧ ⨾ ⟦ "x" as c; "x" as c \ "x" as c ⟧.
Proof. names_eq. Qed.
