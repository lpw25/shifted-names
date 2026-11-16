(** * The eta pass is not canonical either

    Two counterexamples to canonicity of [HNorm] followed by the eta pass
    of [HEta], over interleaved models, with label atoms [a] and [b] that
    the facts leave unordered.  Below, [En h n] is the entry sending
    [h₀] to the bound variable [·ₙ] ([AInner h (TVarE · n) AId]), which
    no step on a named label moves, and [W h] is [⟦ \ h ⟧].

    - **Equal targets** ([t1_t2]).  [En a 0 ⨾ W a] and [En b 0 ⨾ W b]
      each send [a₀] (resp. [b₀]) to [·₀] and every other variable to
      itself, so they commute.
    - **Distinct targets** ([r1_r2]).  [r1] and [r2] differ only in the
      order of the entries [En a 0] and [En a 7]: in [r1] the input [v]
      reaches them as [v] and [⟦ \ b ⟧ v], in [r2] as [⟦ \ b ⟧ v] and
      [v].  The order matters only when both are [a₀], i.e. when [v] is
      [a₀] and [⟦ \ b ⟧] fixes it.  But then [⟦ \ b ⟧ ⟦ \ b ⟧ v] is
      [a₀] too, and the first entry, [En a 5], already took it.  The
      entries [En b 2] and [En b 3] only move the input back along [b];
      no input is ever at [b₀] there.

    Both pairs get different normal forms ([he_t1_t2], [he_r1_r2]).
    [docs/probes.md] explains why: whether two entries may swap depends
    on which earlier entries already catch their common inputs. *)

From Stdlib Require Import String List.
From ShiftedNames.Core Require Import Normalise IModel HNorm HEta HNormGap.
Import ListNotations.

Definition W (h : lexp) : aexp := AOuter h AId.
Definition En (h : lexp) (n : nat) : aexp := AInner h (TVarE LNone n) AId.

Fixpoint gseqs (l : list aexp) : aexp :=
  match l with [] => AId | [p] => p | p :: r => gseq p (gseqs r) end.

Definition t1 : aexp := gseqs [En ga 0; W ga; En gb 0; W gb].
Definition t2 : aexp := gseqs [En gb 0; W gb; En ga 0; W ga].

Definition r1 : aexp :=
  gseqs [W gb; W gb; En ga 5; W ga; En gb 2; En gb 3; En ga 0; W ga; W gb; En ga 7; W ga].
Definition r2 : aexp :=
  gseqs [W gb; W gb; En ga 5; W ga; En gb 2; En ga 7; W ga; En gb 3; En ga 0; W ga; W gb].

Section Bound.
Variables (F : order) (M : imodel).
Hypothesis HM : consistent F M.

Lemma bound_fixed h i : h <> LNone ->
  @mat0 M h (mseq LNone i) = false /\ @msh M h (mseq LNone i) = mseq LNone i
  /\ @mush M h (mseq LNone i) = mseq LNone i.
Proof.
  intros Hh; pose proof (consistent_sym M F h LNone i HM (lt_known_bound F h Hh)) as E.
  unfold mat0, msh, mush; rewrite E; repeat split; reflexivity.
Qed.
End Bound.

Lemma t1_t2 F : mequal F t1 t2.
Proof.
  intros M HM v; unfold mden, t1, t2, gseqs, gseq, W, En; cbn [ma mt].
  destruct (bound_fixed F M HM ga 0 ltac:(discriminate)) as (Ha0 & Has & Hau).
  destruct (bound_fixed F M HM gb 0 ltac:(discriminate)) as (Hb0 & Hbs & Hbu).
  rewrite ?Ha0, ?Has, ?Hau, ?Hb0, ?Hbs, ?Hbu.
  destruct (mat0 ga v) eqn:Ea; destruct (mat0 gb v) eqn:Eb;
    repeat (rewrite ?(msh_mush M ga v), ?(msh_mush M gb v), ?Ea, ?Eb, ?Ha0, ?Has, ?Hau, ?Hbs, ?Hbu by assumption;
            cbv iota);
    apply meq_refl.
Qed.

Lemma r1_r2 F : mequal F r1 r2.
Proof.
  intros M HM v; unfold mden, r1, r2, gseqs, gseq, W, En; cbn [ma mt].
  assert (Ha : forall i, mat0 ga (mseq LNone i) = false /\ msh ga (mseq LNone i) = mseq LNone i
                        /\ mush ga (mseq LNone i) = mseq LNone i)
    by (intros i; exact (bound_fixed F M HM ga i ltac:(discriminate))).
  assert (Hb : forall i, mat0 gb (mseq LNone i) = false /\ msh gb (mseq LNone i) = mseq LNone i
                        /\ mush gb (mseq LNone i) = mseq LNone i)
    by (intros i; exact (bound_fixed F M HM gb i ltac:(discriminate))).
  assert (Ha0 : forall i, mat0 ga (mseq LNone i) = false) by apply Ha.
  assert (Has : forall i, msh ga (mseq LNone i) = mseq LNone i) by apply Ha.
  assert (Hau : forall i, mush ga (mseq LNone i) = mseq LNone i) by apply Ha.
  assert (Hb0 : forall i, mat0 gb (mseq LNone i) = false) by apply Hb.
  assert (Hbs : forall i, msh gb (mseq LNone i) = mseq LNone i) by apply Hb.
  assert (Hbu : forall i, mush gb (mseq LNone i) = mseq LNone i) by apply Hb.
  clear Ha Hb.
  repeat (rewrite ?Ha0, ?Has, ?Hau, ?Hb0, ?Hbs, ?Hbu, ?mat0_msh, ?mush_msh; cbv iota).
  destruct (mat0 ga (msh gb (msh gb v))) eqn:E1; [apply meq_refl|].
  rewrite (msh_mush M ga _ E1); repeat (rewrite ?mat0_msh, ?mush_msh; cbv iota).
  destruct (mat0 ga v) eqn:E2; destruct (mat0 ga (msh gb v)) eqn:E3;
    repeat (rewrite ?mat0_msh, ?mush_msh, ?E2, ?E3, ?(msh_mush M ga v), ?(msh_mush M ga (msh gb v))
              by assumption; cbv iota);
    try apply meq_refl.
  (* [v] and [⟦ \ b ⟧ v] both [a₀]: then [⟦ \ b ⟧] fixes [v], and the
     first entry on [a] took it. *)
  apply mat0_eq in E2; apply mat0_eq in E3.
  assert (Ev : msh gb v = v) by congruence.
  rewrite !Ev, E2 in E1; unfold mat0 in E1; rewrite mpos_seq in E1; discriminate.
Qed.

(** Both pairs get different normal forms from [HNorm] and the eta pass. *)
Lemma he_t1_t2 : he_eq (order_of []) t1 t2 = false.
Proof. vm_compute; reflexivity. Qed.

Lemma he_r1_r2 : he_eq (order_of []) r1 r2 = false.
Proof. vm_compute; reflexivity. Qed.
