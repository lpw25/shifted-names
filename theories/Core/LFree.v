(** * Following a variable through a layered word, in the free model

    [dfollow l h i] follows the variable [h₍ᵢ₎] through the word [l] to
    what it reaches: a variable at the end ([DV]), a term of a segment
    ([DT t d], [d] the length of the rest after that segment), or an
    atom it is not lifted around ([DS a g j d], stuck as [g₍ⱼ₎], [d] the
    length of the rest after the atom).  [dfollow_sound] says what that
    is in the free model ([LayeredUnique.R]).

    The canonical word ([CanonF]) compares results and payloads by what
    [dfollow] finds. *)

From Stdlib Require Import Arith List Lia Bool.
From ShiftedNames.Core Require Import Label Var Adjustment Normalise Unique Layered LayeredUnique Order.
Import ListNotations.

Inductive desc : Type :=
| DV (h : lexp) (i : nat)
| DT (t : ntgt) (d : nat)
| DS (a : nat) (h : lexp) (j d : nat).

(** The last [d] steps of a word. *)
Definition suf (l : lword) (d : nat) : lword := skipn (List.length l - d) l.

Lemma suf_all l : suf l (List.length l) = l.
Proof. unfold suf; rewrite Nat.sub_diag; reflexivity. Qed.

Lemma suf_cons x r d : d <= List.length r -> suf (x :: r) d = suf r d.
Proof.
  intros Hd; unfold suf; cbn [List.length]; replace (S (List.length r) - d) with (S (List.length r - d)) by lia.
  reflexivity.
Qed.

Lemma suf_len l d : d <= List.length l -> List.length (suf l d) = d.
Proof. intros Hd; unfold suf; rewrite length_skipn; lia. Qed.

Lemma suf_suf l d e : e <= d -> d <= List.length l -> suf (suf l d) e = suf l e.
Proof.
  intros He Hd; unfold suf at 1; rewrite (suf_len l d Hd); unfold suf; rewrite skipn_skipn; f_equal; lia.
Qed.

Section Follow.

Variable F : order.

Fixpoint dfollow (l : lword) (h : lexp) (i : nat) : option desc :=
  match l with
  | [] => Some (DV h i)
  | LS s :: r =>
      match seg_tgt F s h i with
      | Some (NVar g j) => dfollow r g j
      | Some t => Some (DT t (List.length r))
      | None => None
      end
  | LA L a :: r =>
      match lcnt F h L with
      | Some c => if i <? c then dfollow r h i else Some (DS a h (i - c) (List.length r))
      | None => None
      end
  end.

End Follow.

Section Sound.

Variable lenv : list label.
Variable F : order.
Hypothesis HF : facts_ok lenv F.

Local Notation lden := (lden lenv).
Local Notation R := (R lenv).
Local Notation fs := (fs lenv).
Local Notation ft := (ft lenv).

Lemma R_seg s r v : R (LS s :: r) v = fs s (R r) v.
Proof. reflexivity. Qed.

Lemma R_atom L a r v : R (LA L a :: r) v = latom lenv L a (R r) v.
Proof. reflexivity. Qed.

Lemma seg_tgt_free s h i t K : seg_tgt F s h i = Some t -> fs s K (mk_rvar (lden h) i) = ft t K.
Proof.
  unfold seg_tgt; destruct (sfind F h s) as [e|] eqn:Ef; [|discriminate].
  apply (sfind_sound lenv F HF) in Ef; rewrite (fs_get lenv); unfold fget; cbn [v_label v_index]; rewrite <- Ef.
  destruct e as [[ts m]|]; intros H; injection H as <-; [|reflexivity].
  destruct (Nat.ltb_spec i (tlen ts)) as [Hi|Hi].
  - apply (ftl_lt lenv), Hi.
  - rewrite (ftl_ge lenv) by exact Hi; reflexivity.
Qed.

Lemma seg_tgt_in s h i t : seg_tgt F s h i = Some t -> (exists j, t = NVar h j) \/ In t (stgts s).
Proof.
  unfold seg_tgt; destruct (sfind F h s) as [e|] eqn:Ef; [|discriminate].
  apply (sfind_sound lenv F HF) in Ef.
  destruct e as [[ts m]|]; intros H; injection H as <-; [|left; eexists; reflexivity].
  destruct (Nat.ltb_spec i (tlen ts)) as [Hi|Hi]; [|left; eexists; reflexivity].
  right; apply (sget_tgts lenv _ s ts m (eq_sym Ef)), tnth_in, Hi.
Qed.

Theorem dfollow_sound l : forall h i x, dfollow F l h i = Some x ->
  match x with
  | DV g j => R l (mk_rvar (lden h) i) = FVar (mk_rvar (lden g) j)
  | DT t d =>
      d < List.length l /\ is_term t = true
      /\ exists s, suf l (S d) = LS s :: suf l d /\ In t (stgts s) /\ R l (mk_rvar (lden h) i) = ft t (R (suf l d))
  | DS a g j d =>
      d < List.length l
      /\ exists L, suf l (S d) = LA L a :: suf l d
                   /\ R l (mk_rvar (lden h) i) = FStuck a (mk_rvar (lden g) j) (fun y => R (suf l d) (shiftL lenv L y))
  end.
Proof.
  induction l as [|[s|L a] r IH]; intros h i x; cbn [dfollow].
  - intros H; injection H as <-; reflexivity.
  - destruct (seg_tgt F s h i) as [t|] eqn:Et; [|discriminate].
    pose proof (seg_tgt_free s h i t (R r) Et) as Ef.
    assert (Hlen : List.length r < List.length (LS s :: r)) by (cbn; lia).
    assert (Hsuf : suf (LS s :: r) (S (List.length r)) = LS s :: suf (LS s :: r) (List.length r)).
    { change (S (List.length r)) with (List.length (LS s :: r)); rewrite suf_all, (suf_cons _ _ _ (le_n _)), suf_all.
      reflexivity. }
    destruct t as [g j|u w b].
    + intros H; specialize (IH g j x H); destruct x as [g' j'|t d|a g' j' d].
      * rewrite R_seg, Ef; exact IH.
      * destruct IH as [Hd [Ht [s' [E1 [E2 E3]]]]]; split; [cbn; lia|split; [exact Ht|]].
        exists s'; rewrite !suf_cons by lia; split; [exact E1|split; [exact E2|]].
        rewrite R_seg, Ef; exact E3.
      * destruct IH as [Hd [L [E1 E2]]]; split; [cbn; lia|].
        exists L; rewrite !suf_cons by lia; split; [exact E1|].
        rewrite R_seg, Ef; exact E2.
    + intros H; injection H as <-; split; [exact Hlen|split; [reflexivity|]].
      exists s; rewrite Hsuf; split; [reflexivity|].
      destruct (seg_tgt_in s h i _ Et) as [[j E]|Hin]; [discriminate E|split; [exact Hin|]].
      rewrite (suf_cons _ _ _ (le_n _)), suf_all, R_seg; exact Ef.
  - destruct (lcnt F h L) as [c|] eqn:Ec; [|discriminate].
    pose proof (lcnt_sound lenv F HF _ _ _ Ec) as Hc.
    destruct (Nat.ltb_spec i c) as [Hi|Hi].
    + intros H; specialize (IH h i x H).
      assert (Ea : R (LA L a :: r) (mk_rvar (lden h) i) = R r (mk_rvar (lden h) i)).
      { rewrite R_atom; unfold latom; cbn [v_label v_index]; rewrite Hc, (proj2 (Nat.ltb_lt _ _) Hi); reflexivity. }
      destruct x as [g' j'|t d|a' g' j' d].
      * rewrite Ea; exact IH.
      * destruct IH as [Hd [Ht [s' [E1 [E2 E3]]]]]; split; [cbn; lia|split; [exact Ht|]].
        exists s'; rewrite !suf_cons by lia; split; [exact E1|split; [exact E2|]]; rewrite Ea; exact E3.
      * destruct IH as [Hd [L' [E1 E2]]]; split; [cbn; lia|].
        exists L'; rewrite !suf_cons by lia; split; [exact E1|]; rewrite Ea; exact E2.
    + intros H; injection H as <-; split; [cbn; lia|].
      exists L; split.
      * change (S (List.length r)) with (List.length (LA L a :: r)); rewrite suf_all, (suf_cons _ _ _ (le_n _)), suf_all.
        reflexivity.
      * rewrite (suf_cons _ _ _ (le_n _)), suf_all, R_atom; unfold latom; cbn [v_label v_index].
        rewrite Hc, (proj2 (Nat.ltb_ge _ _) Hi); reflexivity.
Qed.

End Sound.
