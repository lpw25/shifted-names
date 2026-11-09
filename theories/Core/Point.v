(** * Point operations on adjustments

    Identity, weakening, extension and lifting on the representation of
    Repr.v, each specified by its effect on the meaning ([napply]) and shown
    to keep the normal form. *)

From Stdlib Require Import PArith Arith Lia List Bool.
From ShiftedNames.Core Require Import Trie Label Var Counts Based Skew ATrie Repr.
Import ListNotations.

Section Point.

Context {T : Type}.

Local Notation nadj := (@nadj T).
Local Notation result := (@result T).

(** Every label matters at the top level. *)
Definition Qall : option label -> bool := fun _ => true.

(** ** Identity *)

Definition uniform0 : counts := mk_counts (Some 0) Empty.

Definition nidentity : nadj := NAdj uniform0 AEmpty.

Lemma cget_uniform0 k : cget uniform0 k = Some 0.
Proof. reflexivity. Qed.

Theorem nlocal_identity : nlocal Qall nidentity.
Proof.
  cbn [nlocal nidentity]; split; [exact I|split; [|split; [|split; [|split]]]].
  - intros k v H; cbn in H; discriminate.
  - intros k v H; cbn in H; discriminate.
  - intros k e H; cbn in H; discriminate.
  - intros l _; discriminate.
  - intros l H; discriminate.
Qed.

Theorem napply_identity v : napply nidentity v = inl v.
Proof. destruct v as [h i]; reflexivity. Qed.

(** ** Weakening: the outputs of [h] move up by one *)

Definition weaken (h : option label) (a : nadj) : nadj :=
  match a with NAdj w es => NAdj (cadd (cone (label_key h) 1) w) es end.

(** The effect on a result. *)
Definition rweaken (h : option label) (r : result) : result :=
  match r with
  | inl w => inl (if label_eqb (v_label w) h then mk_rvar h (S (v_index w)) else w)
  | inr (u, rho) => inr (u, NAdj (cadd (cone (label_key h) 1) (nroot rho)) (nentries rho))
  end.

Lemma dval_weaken h w k :
  cget w (label_key h) <> None ->
  dval (cadd (cone (label_key h) 1) w) k = (if Pos.eqb k (label_key h) then 1 else 0) + dval w k.
Proof.
  intros Hw; unfold dval; rewrite cget_cadd, cget_cone.
  destruct (cget w k) eqn:E; destruct (Pos.eqb_spec k (label_key h)) as [->|]; cbn; try reflexivity.
  contradiction.
Qed.

Lemma cadd_weaken h w r :
  cget w (label_key h) <> None ->
  cadd (cadd (cone (label_key h) 1) w) r = cadd (cone (label_key h) 1) (cadd w r).
Proof.
  intros Hw; apply counts_ext; try apply cwf_cmap2; intro k.
  rewrite !cget_cadd, cget_cone.
  destruct (cget r k) as [m|]; [|reflexivity].
  destruct (cget w k) eqn:E; destruct (Pos.eqb_spec k (label_key h)) as [->|]; cbn;
    try contradiction; f_equal; lia.
Qed.

Theorem napply_weaken h a v :
  nlocal Qall a -> napply (weaken h a) v = rweaken h (napply a v).
Proof.
  destruct a as [w es]; intros Ha; pose proof Ha as [_ [_ [_ [_ [HQ _]]]]].
  assert (Hw : cget w (label_key h) <> None) by (apply HQ; reflexivity).
  assert (Hvar : forall y n, inl (mk_rvar y (dval (cadd (cone (label_key h) 1) w) (label_key y) + n))
                             = rweaken h (inl (mk_rvar y (dval w (label_key y) + n))) :> result).
  { intros y n; cbn [rweaken v_label v_index]; rewrite dval_weaken by exact Hw.
    rewrite label_key_eqb; destruct (label_eqb_spec y h) as [->|]; reflexivity. }
  unfold napply, weaken; destruct (aget (label_key (v_label v)) es) as [[h' ts len p]|]; [|apply Hvar].
  cbn [eapply]; destruct (Nat.ltb (v_index v) len); [|apply Hvar].
  destruct (knth ts (v_index v)) as [[y j|u [r es']]|]; [|cbn [tunshift tresult]..|apply Hvar].
  - cbn [tunshift tresult]; apply (Hvar y j).
  - cbn [rweaken nroot nentries]; rewrite cadd_weaken by exact Hw; reflexivity.
Qed.

Theorem nlocal_weaken h a : nlocal Qall a -> nlocal Qall (weaken h a).
Proof.
  destruct a as [w es]; intros [Hes [Cw [Kw [Hent [HQ HnQ]]]]].
  split; [exact Hes|split; [apply cwf_cmap2|split; [apply keyed_cmap2; [apply keyed_cone|exact Kw]|]]].
  split; [exact Hent|split; [|intros l Hl; discriminate]].
  intros l _; rewrite cget_cadd; specialize (HQ l eq_refl).
  destruct (cget w (label_key l)); [discriminate|contradiction].
Qed.

End Point.
