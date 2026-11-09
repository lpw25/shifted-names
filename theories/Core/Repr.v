(** * The representation of adjustments

    Targets name output variables directly; weakenings are applied lazily
    through the counts on the nodes (Counts.v, Skew.v, ATrie.v).

    - A [target] is a variable [TVar y j] ([j] relative to the counts above
      it) or a payload [TBind u ρ]: a closed term [u] with a pending
      adjustment [ρ] whose root counts are relative to the node above it.
    - An [entry] for label [h] holds the targets of [h₀ … h₍len−1₎] and the
      start [p] of the pass-through: [hᵢ ↦ h₍ᵢ₋len₊p₎] for [i ≥ len].
    - An adjustment [NAdj ω es] has root counts [ω] (per label, the
      weakening of the whole adjustment) and a trie of entries relative to
      [ω].  A label without an entry is the identity relative to [ω]. *)

From Stdlib Require Import PArith Arith Lia List Bool.
From ShiftedNames.Core Require Import Trie Label Var Counts Based Skew ATrie.
Import ListNotations.

Section Repr.

Context {T : Type}.

Inductive target : Type :=
| TVar (y : option label) (j : nat)
| TBind (u : T) (rho : nadj)
with nadj : Type :=
| NAdj (root : counts) (entries : atrie entry)
with entry : Type :=
| Entry (h : option label) (targets : kseq target) (len : nat) (p : nat).

Definition nroot (a : nadj) : counts := match a with NAdj r _ => r end.
Definition nentries (a : nadj) : atrie entry := match a with NAdj _ es => es end.

(** ** Targets relative to a base *)

Definition tuses (t : target) : counts :=
  match t with TVar y j => cone (label_key y) j | TBind _ rho => nroot rho end.

Definition tshift (d : counts) (t : target) : target :=
  match t with
  | TVar y j => TVar y (j - dval d (label_key y))
  | TBind u (NAdj r es) => TBind u (NAdj (csub r d) es)
  end.

Definition tunshift (d : counts) (t : target) : target :=
  match t with
  | TVar y j => TVar y (dval d (label_key y) + j)
  | TBind u (NAdj r es) => TBind u (NAdj (cadd d r) es)
  end.

Definition tok (t : target) : Prop :=
  match t with TVar _ _ => True | TBind _ rho => cwf (nroot rho) end.

#[export] Instance target_based : Based target :=
  {| uses := tuses; shift := tshift; unshift := tunshift; eok := tok |}.

Lemma cget_cone_same k n : cget (cone k n) k = Some n.
Proof. rewrite cget_cone, Pos.eqb_refl; reflexivity. Qed.

#[export] Instance target_laws : BasedLaws target.
Proof.
  split.
  - intros d [y j|u [r es]]; cbn; [intros _; exact I|intros _; apply cwf_cmap2].
  - intros d [y j|u [r es]]; cbn; [intros _; exact I|intros _; apply cwf_cmap2].
  - intros d [y j|u [r es]]; cbn; intros H; [f_equal; lia|rewrite csub_cadd by exact H; reflexivity].
  - intros d [y j|u [r es]]; cbn; intros H Hle.
    + pose proof (dval_le_cle d _ j Hle); f_equal; lia.
    + rewrite cadd_csub by assumption; reflexivity.
  - intros d1 d2 [y j|u [r es]]; cbn; [rewrite dval_cplus; f_equal; lia|rewrite cadd_cadd; reflexivity].
  - intros d d' [y j|u [r es]]; cbn; intros H.
    + rewrite (H (label_key y)) by (rewrite cget_cone_same; discriminate); reflexivity.
    + rewrite (cadd_ext d d' r H); reflexivity.
  - intros d [y j|u [r es]] k; cbn; [|apply cget_cadd].
    rewrite !cget_cone; destruct (Pos.eqb_spec k (label_key y)) as [->|]; [|reflexivity].
    reflexivity.
  - intros d [y j|u [r es]] k; cbn; [|apply cget_csub].
    rewrite !cget_cone; destruct (Pos.eqb_spec k (label_key y)) as [->|]; [|reflexivity].
    reflexivity.
Qed.

(** ** Entries relative to a base *)

Definition elabel (e : entry) : option label := match e with Entry h _ _ _ => h end.
Definition etargets (e : entry) : kseq target := match e with Entry _ ts _ _ => ts end.
Definition elen (e : entry) : nat := match e with Entry _ _ len _ => len end.
Definition epass (e : entry) : nat := match e with Entry _ _ _ p => p end.

(** An entry uses its pass-through outputs and its targets. *)
Definition euses (e : entry) : counts :=
  match e with Entry h ts _ p => cmin (cone (label_key h) p) (ksann ts) end.

Definition eshift (d : counts) (e : entry) : entry :=
  match e with Entry h ts len p => Entry h (krebase d ts) len (p - dval d (label_key h)) end.

Definition eunshift (d : counts) (e : entry) : entry :=
  match e with Entry h ts len p => Entry h (klift d ts) len (dval d (label_key h) + p) end.

Definition eok_entry (e : entry) : Prop := cwf (ksann (etargets e)).

#[export] Instance entry_based : Based entry :=
  {| uses := euses; shift := eshift; unshift := eunshift; eok := eok_entry |}.

Lemma ksann_krebase d (s : kseq target) k :
  cget (ksann (krebase d s)) k = osub (cget (ksann s) k) (cget d k).
Proof. destruct s; cbn [krebase ksann]; [reflexivity|apply cget_csub]. Qed.

Lemma ksann_klift d (s : kseq target) k :
  cget (ksann (klift d s)) k = oadd (cget d k) (cget (ksann s) k).
Proof. destruct s; cbn [klift ksann]; [destruct (cget d k); reflexivity|apply cget_cadd]. Qed.

#[export] Instance entry_laws : BasedLaws entry.
Proof.
  split.
  - intros d [h [|a w t s] len p]; unfold eok_entry; cbn; [intros H; exact H|intros _; apply cwf_cmap2].
  - intros d [h [|a w t s] len p]; unfold eok_entry; cbn; [intros H; exact H|intros _; apply cwf_cmap2].
  - intros d [h [|a w t s] len p]; unfold eok_entry; cbn; intros H; f_equal; try lia.
    rewrite csub_cadd by exact H; reflexivity.
  - intros d [h [|a w t s] len p]; unfold eok_entry; cbn [unshift shift uses entry_based eunshift eshift euses ksann klift krebase etargets];
      intros H Hle; pose proof (dval_le_cle d _ p (cle_cmin_inv_l _ _ _ Hle)); f_equal; try lia.
    rewrite cadd_csub by (exact H || apply (cle_cmin_inv_r _ _ _ Hle)); reflexivity.
  - intros d1 d2 [h [|a w t s] len p]; cbn; rewrite dval_cplus; f_equal; try lia.
    rewrite cadd_cadd; reflexivity.
  - intros d d' [h [|a w t s] len p]; cbn [uses entry_based euses ksann]; intros H; cbn [uses entry_based euses ksann] in H;
      assert (Hp : dval d (label_key h) = dval d' (label_key h))
        by (apply H; rewrite cget_cmin, cget_cone_same; destruct (cget _ _); discriminate);
      cbn [unshift entry_based eunshift klift]; rewrite Hp; [reflexivity|].
    rewrite (cadd_ext d d' a); [reflexivity|]; intros k Hk; apply H.
    rewrite cget_cmin; destruct (cget (cone _ _) k), (cget a k); cbn; congruence.
  - intros d [h s len p] k; cbn [uses unshift entry_based euses eunshift].
    rewrite !cget_cmin, ksann_klift, oadd_omin; f_equal.
    rewrite !cget_cone; destruct (Pos.eqb_spec k (label_key h)) as [->|]; reflexivity.
  - intros d [h s len p] k; cbn [uses shift entry_based euses eshift].
    rewrite !cget_cmin, ksann_krebase, osub_omin; f_equal.
    rewrite !cget_cone; destruct (Pos.eqb_spec k (label_key h)) as [->|]; reflexivity.
Qed.

End Repr.
