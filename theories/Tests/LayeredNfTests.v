(** Tests of the layered normal form ([Core/LayeredUnique.v]): the
    conditions hold of a chain of two substitutions, with the order of
    [Core/LayeredOrder.v]. *)

From Stdlib Require Import String List Arith Lia.
From ShiftedNames.Core Require Import Label Var Adjustment Normalise Unique Layered LayeredUnique LayeredOrder.
Import ListNotations.
Open Scope string_scope.

Definition labs : list lexp := [LCon "x"; LCon "y"].

Lemma labs_inj : forall h h', In h labs -> In h' labs -> lden [] h = lden [] h' -> h = h'.
Proof. intros h h' [<-|[<-|[]]] [<-|[<-|[]]]; cbn; intros E; try reflexivity; discriminate E. Qed.

(** [⟦ x := u₀ ⟧ ⨾ ⟦ y := u₁ ⟧]. *)
Definition S1 : seg := entry_seg (LCon "x") 0.
Definition S2 : seg := entry_seg (LCon "y") 1.

Local Notation gt := (gt_sz [] labs 0).
Local Notation R := (R []).

Lemma S2_pure : spure [] labs S2.
Proof. constructor; [exists SNil; split; reflexivity|constructor]. Qed.

(** What the second step does. *)
Lemma R2 v :
  R [LS S2] v
  = if label_eqb (@Some label "y") (v_label v)
    then match v_index v with 0 => FTerm 1 None FVar | S i => FVar (mk_rvar (v_label v) i) end
    else FVar v.
Proof.
  rewrite (R_cons [] labs S2 [] S2_pure); unfold res, S2; rewrite (sres_entry [] (LCon "y") 1 "y" v eq_refl).
  destruct (label_eqb (@Some label "y") (v_label v)); [destruct (v_index v)|]; reflexivity.
Qed.

Lemma R2_inj y y' : named y' -> feq (R [LS S2] y') (R [LS S2] y) -> y' = y.
Proof.
  intros _; rewrite !R2; destruct y as [l i], y' as [l' i']; cbn [v_label v_index].
  destruct (label_eqb_spec (@Some label "y") l') as [<-|N'], (label_eqb_spec (@Some label "y") l) as [<-|N].
  - destruct i' as [|j'], i as [|j]; cbn [feq]; try (intros []; fail); [reflexivity|].
    intros E; injection E as ->; reflexivity.
  - destruct i' as [|j']; cbn [feq]; [intros []|]; intros E; injection E as E _; destruct (N E).
  - destruct i as [|j]; cbn [feq]; [intros []|]; intros E; injection E as E _; destruct (N' (eq_sym E)).
  - cbn [feq]; intros E; exact E.
Qed.

Lemma R2_binj : binj (R [LS S2]).
Proof.
  intros [l i] [l' i'] Hs Hs'; unfold bound in Hs, Hs'; cbn in Hs, Hs'; subst l l'.
  rewrite !R2; cbn; intros E; exact E.
Qed.

Example chain_normal : lnf [] labs gt [LS S1; LS S2].
Proof.
  split; [discriminate|split; [|split; [discriminate|split; [|exact I]]]].
  - apply (segok_entry [] labs gt (LCon "x") "x" 0 [LS S2] eq_refl); [left; reflexivity| | |exact R2_inj|exact R2_binj].
    + intros y u b k E; rewrite R2 in E.
      destruct (label_eqb (@Some label "y") (v_label y)); [destruct (v_index y)|]; try discriminate E.
      injection E as _ _ <-.
      exists (WEnd S2), (WEnd SNil); split; [|split].
      * split; [|intros v _; apply feq_refl].
        unfold S2, entry_seg; split; [split|cbn; repeat split; constructor].
        -- constructor; [constructor|constructor].
        -- constructor; [|constructor].
           split; [right; left; reflexivity|split; [exact I|split; [left; discriminate|intros _; discriminate]]].
      * split; [|intros v _; apply feq_refl].
        split; [split; constructor|exact I].
      * left; cbn; lia.
    + intros G E _; injection E as <-; exists (mk_rvar (Some "y") 0), (1, None, SNil); reflexivity.
  - apply (segok_entry [] labs gt (LCon "y") "y" 1 [] eq_refl); [right; left; reflexivity| | | |apply binj_var].
    + intros y u b k E; discriminate E.
    + intros G E; discriminate E.
    + intros y y' _ E; exact E.
Qed.
