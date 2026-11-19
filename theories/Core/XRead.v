(** * Where a read sits among commuting weakenings matters

    Labels [g], [h], [k], [l] with the facts [g < k], [g < l], [k < l];
    [h] is ordered against none of them.  [C] copies [h₀] into [g]
    (an input entry on [g] whose target is [h₀]).  The four words put
    the weakenings of [k] and [l] on either side of [C]:

    - [X1 = ⟦ \ l as _ ⟧ ⨾ C ⨾ ⟦ \ k as _ ⟧]
    - [X2 = C ⨾ ⟦ \ k as _ ⟧ ⨾ ⟦ \ l as _ ⟧]
    - [X3 = ⟦ \ k as _ ⟧ ⨾ ⟦ \ l as _ ⟧ ⨾ C]
    - [X4 = ⟦ \ k as _ ⟧ ⨾ C ⨾ ⟦ \ l as _ ⟧]

    All four have the same inputs (one on [g], reading [h₀]) and the same
    outputs (one weakening each of [k] and [l], which commute), and they
    are pairwise different in comprehension models: the read of [h] is
    below [k] only, below both, above both, or below [l] only.  So a
    segment that records, per label, its targets and its number of
    outputs cannot be a normal form here: it must also say where each
    read sits among the outputs it does not commute with. *)

From Stdlib Require Import List String.
Import ListNotations.
From ShiftedNames.Core Require Import Label Normalise GEval CNorm Comp CSound CComplete.

(* g = 0, h = 1, k = 2, l = 3; facts g < k, g < l, k < l; h unordered. *)
Definition g := LAtom 0. Definition h := LAtom 1. Definition k := LAtom 2. Definition l := LAtom 3.
Definition tab : list (list bool) :=
  [[false; false; true; true]; [false; false; false; false]; [false; false; false; true]; [false; false; false; false]].
Definition F := mk_order [] tab.

Definition tabf (i j : nat) : bool :=
  match i, j with 0, 2 | 0, 3 | 2, 3 => true | _, _ => false end.

Definition lt_spec (a b : lexp) : bool :=
  match a, b with
  | LAtom i, LAtom j => tabf i j
  | LCon s, LCon s' => is_less_than_label s s'
  | LNone, _ => false
  | _, LNone => true
  | _, _ => false
  end.

Lemma lt_spec_eq a b : lt_known F a b = lt_spec a b.
Proof.
  destruct a as [|s|i], b as [|s'|j]; try reflexivity.
  { cbn; destruct (is_less_than_label s s'); reflexivity. }
  unfold lt_known, tab_get.
  destruct i as [|[|[|[|i]]]]; [| | | |cbn; destruct i; reflexivity];
  (destruct j as [|[|[|[|j]]]]; [reflexivity|reflexivity|reflexivity|reflexivity|cbn; destruct j; reflexivity]).
Qed.

Lemma Hirr : forall a, lt_known F a a = false.
Proof.
  intros a; rewrite lt_spec_eq; destruct a as [|s|[|[|[|[|n]]]]]; try reflexivity.
  cbn; destruct (is_less_than_label s s) eqn:E; [|reflexivity].
  pose proof (is_less_than_label_asymmetric _ _ E); congruence.
Qed.

Lemma Htrans : forall a b c, lt_known F a b = true -> lt_known F b c = true -> lt_known F a c = true.
Proof.
  intros a b c; rewrite !lt_spec_eq.
  destruct a as [|s|i], b as [|s'|j], c as [|s''|m]; cbn; try discriminate; try reflexivity.
  - apply is_less_than_label_transitive.
  - destruct i as [|[|[|[|i]]]], j as [|[|[|[|j]]]], m as [|[|[|[|m]]]]; cbn; congruence.
Qed.

Definition W (x : lexp) : aexp := AOuter x AId.
Definition C : aexp := AInner g (TVarE h 0) AId.
Definition seq3 (a b c : aexp) : aexp := ACompose (ACompose c b) a.

(* The weakenings of k and l on either side of the copy of h into g. *)
Definition X1 := seq3 (W l) C (W k).
Definition X2 := seq3 C (W k) (W l).
Definition X3 := seq3 (W k) (W l) C.
Definition X4 := seq3 (W k) C (W l).

Lemma distinct (a b : aexp) : cn_eq F a b = false -> ~ cequal F a b.
Proof. intros E H; apply (cn_eq_correct F Hirr Htrans) in H; congruence. Qed.

Lemma X12 : ~ cequal F X1 X2. Proof. apply distinct; vm_compute; reflexivity. Qed.
Lemma X13 : ~ cequal F X1 X3. Proof. apply distinct; vm_compute; reflexivity. Qed.
Lemma X14 : ~ cequal F X1 X4. Proof. apply distinct; vm_compute; reflexivity. Qed.
Lemma X23 : ~ cequal F X2 X3. Proof. apply distinct; vm_compute; reflexivity. Qed.
Lemma X24 : ~ cequal F X2 X4. Proof. apply distinct; vm_compute; reflexivity. Qed.
Lemma X34 : ~ cequal F X3 X4. Proof. apply distinct; vm_compute; reflexivity. Qed.



