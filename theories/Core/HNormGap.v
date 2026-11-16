(** * The hash-consed normal form is not canonical

    A counterexample to canonicity of [HNorm] over interleaved models.
    With label atoms [a] and [b] that the facts leave unordered,

      f1 = ⟦ \ a ⟧ ⨾ Eb ⨾ ⟦ \ b ⟧
      f2 = f1 ⨾ Ea ⨾ ⟦ \ a ⟧

    where [Eb] sends [b₀] to the bound variable [·₀]
    ([AInner b (TVarE · 0) AId]) and [Ea] sends [a₀] to [·₁],
    agree in every consistent model ([f1_f2]): after [⟦ \ a ⟧] no
    variable is at [a₀], [Eb ⨾ ⟦ \ b ⟧] sends every variable it
    does not consume back where it was, and the target [·₀] passes every
    step unchanged.  So the entry [Ea] is never reached, and
    with the weakening after it it does nothing.  [HNorm] keeps it
    ([hn_f1_f2]). *)

From Stdlib Require Import String List.
From ShiftedNames.Core Require Import Normalise IModel HNorm.
Import ListNotations.

Definition ga : lexp := LAtom 0.
Definition gb : lexp := LAtom 1.

(** [p ⨾ q], [p] first. *)
Definition gseq (p q : aexp) : aexp := ACompose q p.

Definition f1 : aexp := gseq (AOuter ga AId) (gseq (AInner gb (TVarE LNone 0) AId) (AOuter gb AId)).
Definition f2 : aexp := gseq f1 (gseq (AInner ga (TVarE LNone 1) AId) (AOuter ga AId)).

(** The bound label is ordered after every named label. *)
Lemma lt_known_bound F h : h <> LNone -> lt_known F h LNone = true.
Proof.
  intros Hh; unfold lt_known, lt_list.
  assert (E : forall n, lt_reach (ofacts F) n h LNone = true)
    by (intros [|n]; cbn; destruct h; [contradiction|reflexivity|reflexivity|contradiction|reflexivity|reflexivity]).
  destruct h; [contradiction|apply E|apply E].
Qed.

Lemma f1_f2 F : mequal F f1 f2.
Proof.
  intros M HM v; unfold mden, f2; unfold f1, gseq; cbn [ma mt].
  assert (Hb : forall h, h <> LNone -> @mat0 M h (mseq LNone 0) = false
                                     /\ @msh M h (mseq LNone 0) = mseq LNone 0).
  { intros h Hh; pose proof (consistent_sym M F h LNone 0 HM (lt_known_bound F h Hh)) as E.
    unfold mat0, msh; rewrite E; split; reflexivity. }
  destruct (Hb gb ltac:(discriminate)) as [_ Eb].
  destruct (Hb ga ltac:(discriminate)) as [Ea0 Ea].
  destruct (mat0 gb (msh ga v)) eqn:E0.
  - rewrite Eb, Ea0, (msh_mush M ga _ Ea0); apply meq_refl.
  - rewrite (msh_mush M gb _ E0), mat0_msh, (msh_mush M ga _ (mat0_msh M ga v)); apply meq_refl.
Qed.

(** [HNorm] gives them different normal forms. *)
Lemma hn_f1_f2 : hn_eq (order_of []) f1 f2 = false.
Proof. vm_compute; reflexivity. Qed.
