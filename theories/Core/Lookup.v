(** * Lookups with continuations

    [aget_with k t B found none] looks up [k] in the annotated trie [t]
    stored over base [B], and calls [found B' x] on the element it finds,
    stored over base [B'] (so [unshift (lcounts B') x] is the element made
    absolute; bases are lazy, see below),
    or [none] if there is none; [knth_with] does the same for skew
    sequences.  The continuation also receives, as a strict proposition,
    where the element was found.

    Two things follow.  A recursive function can recurse on what it finds
    (the guard checker unfolds these definitions and sees a subterm), which
    is how substitution recurses structurally into payloads.  And proofs
    about the result (for example, that a variable is in scope) can be built
    from the location without any runtime test: the location proofs are
    erased by extraction. *)

From Stdlib Require Import PArith Arith List StrictProp.
From ShiftedNames.Core Require Import Trie Counts Based Skew ATrie.
Import ListNotations.

Definition sq_map {P Q : Prop} (f : P -> Q) (H : Squash P) : Squash Q :=
  match H with squash p => squash (f p) end.

Section Lookups.

Context {X : Type} {BX : Based X} {LX : BasedLaws X} {R : Type}.

Lemma omap_none {Y Z} (f g : Y -> Z) (o : option Y) o' : option_map f o = option_map g o' -> o = None -> o' = None.
Proof. intros E ->; destruct o'; [discriminate|reflexivity]. Qed.

(** ** Tries *)

Section AgetWith.

Variables (k0 : positive) (t0 : atrie X) (B0 : lbase)
  (found : forall B x, Squash (option_map (unshift (lcounts B0)) (aget k0 t0) = Some (unshift (lcounts B) x)) -> R)
  (none : Squash (aget k0 t0 = None) -> R).

Local Notation goal k t B := (option_map (unshift (lcounts B)) (aget k t) = option_map (unshift (lcounts B0)) (aget k0 t0)).

Fixpoint aget_with' (k : positive) (t : atrie X) (B : lbase) {struct t} :
  Squash (goal k t B) -> R :=
  match t as t1 return Squash (goal k t1 B) -> R with
  | AEmpty => fun H => none (sq_map (fun E => omap_none _ _ _ _ E eq_refl) H)
  | ANode a l o r =>
      match k as k1 return Squash (goal k1 (ANode a l o r) B) -> R with
      | xH =>
          match o as o1 return Squash (goal xH (ANode a l o1 r) B) -> R with
          | Some x => fun H => found (LPlus B a) x
                                (sq_map (fun E => eq_trans (eq_sym E) (f_equal Some (unshift_unshift (lcounts B) a x))) H)
          | None => fun H => none (sq_map (fun E => omap_none _ _ _ _ E eq_refl) H)
          end
      | xO k' => fun H => aget_with' k' l (LPlus B a)
                            (sq_map (fun E => eq_trans (eq_sym (omap_unshift2 (lcounts B) a _)) E) H)
      | xI k' => fun H => aget_with' k' r (LPlus B a)
                            (sq_map (fun E => eq_trans (eq_sym (omap_unshift2 (lcounts B) a _)) E) H)
      end
  end.

Definition aget_with : R := aget_with' k0 t0 B0 (squash eq_refl).

End AgetWith.

(** ** Skew sequences *)

Section KnthWith.

Variables (i0 : nat) (s0 : kseq X) (B0 : lbase)
  (found : forall B x, Squash (option_map (unshift (lcounts B0)) (knth s0 i0) = Some (unshift (lcounts B) x)) -> R)
  (none : Squash (knth s0 i0 = None) -> R).

Local Notation target := (option_map (unshift (lcounts B0)) (knth s0 i0)).

Fixpoint ktnth_with' (w : nat) (t : ktree X) (i : nat) (B : lbase) {struct t} :
  Squash (option_map (unshift (lcounts B)) (ktnth w t i) = target) -> R :=
  match t as t1 return Squash (option_map (unshift (lcounts B)) (ktnth w t1 i) = target) -> R with
  | KLeaf x =>
      match i as i1 return Squash (option_map (unshift (lcounts B)) (ktnth w (KLeaf x) i1) = target) -> R with
      | 0 => fun H => found B x (sq_map (@eq_sym _ _ _) H)
      | S _ => fun H => none (sq_map (fun E => omap_none _ _ _ _ E eq_refl) H)
      end
  | KNode a x l r =>
      match i as i1 return Squash (option_map (unshift (lcounts B)) (ktnth w (KNode a x l r) i1) = target) -> R with
      | 0 => fun H => found (LPlus B a) x (sq_map (fun E => eq_trans (eq_sym E) (f_equal Some (unshift_unshift (lcounts B) a x))) H)
      | S j =>
          match Nat.ltb j (Nat.div2 w) as b
                return Squash (option_map (unshift (lcounts B))
                                 (option_map (unshift a) (if b then ktnth (Nat.div2 w) l j
                                                          else ktnth (Nat.div2 w) r (j - Nat.div2 w)))
                               = target) -> R with
          | true => fun H => ktnth_with' (Nat.div2 w) l j (LPlus B a)
                                (sq_map (fun E => eq_trans (eq_sym (omap_unshift2 (lcounts B) a _)) E) H)
          | false => fun H => ktnth_with' (Nat.div2 w) r (j - Nat.div2 w) (LPlus B a)
                                 (sq_map (fun E => eq_trans (eq_sym (omap_unshift2 (lcounts B) a _)) E) H)
          end
      end
  end.

Fixpoint spnth_with' (s : kspine X) (i : nat) (B : lbase) {struct s} :
  Squash (option_map (unshift (lcounts B)) (spnth s i) = target) -> R :=
  match s as s1 return Squash (option_map (unshift (lcounts B)) (spnth s1 i) = target) -> R with
  | SNil => fun H => none (sq_map (fun E => omap_none _ _ _ _ E eq_refl) H)
  | SCons w t s' =>
      match Nat.ltb i w as b
            return Squash (option_map (unshift (lcounts B)) (if b then ktnth w t i else spnth s' (i - w)) = target) -> R with
      | true => fun H => ktnth_with' w t i B H
      | false => fun H => spnth_with' s' (i - w) B H
      end
  end.

Definition knth_with' (s : kseq X) (i : nat) (B : lbase) :
  Squash (option_map (unshift (lcounts B)) (knth s i) = target) -> R :=
  match s as s1 return Squash (option_map (unshift (lcounts B)) (knth s1 i) = target) -> R with
  | KNil => fun H => none (sq_map (fun E => omap_none _ _ _ _ E eq_refl) H)
  | KSeq a w t s' => fun H =>
      spnth_with' (SCons w t s') i (LPlus B a) (sq_map (fun E => eq_trans (eq_sym (omap_unshift2 (lcounts B) a _)) E) H)
  end.

Definition knth_with : R := knth_with' s0 i0 B0 (squash eq_refl).

End KnthWith.

(** ** Specifications

    The location proofs are strict propositions, so a continuation cannot
    tell which proof it was given; it is asked to depend only on the
    element made absolute. *)

Lemma aget_with'_prop k0 t0 B0 found none y (P : R -> Prop)
  (Hf : forall B x p, unshift (lcounts B) x = y -> P (found B x p)) (Y : option_map (unshift (lcounts B0)) (aget k0 t0) = Some y) :
  forall t k B H, option_map (unshift (lcounts B)) (aget k t) = option_map (unshift (lcounts B0)) (aget k0 t0) ->
  P (aget_with' k0 t0 B0 found none k t B H).
Proof.
  induction t as [|a l IHl o r IHr]; intros k B H E; cbn [aget_with'].
  - rewrite Y in E; discriminate.
  - destruct k as [k|k|].
    + apply IHr; rewrite <- E; cbn [aget]; rewrite omap_unshift2; reflexivity.
    + apply IHl; rewrite <- E; cbn [aget]; rewrite omap_unshift2; reflexivity.
    + destruct o as [x|]; cbn in E; rewrite Y in E; [|discriminate].
      apply Hf; injection E as <-; rewrite unshift_unshift; reflexivity.
Qed.

Lemma aget_with_prop k0 t0 B0 found none y (P : R -> Prop)
  (Hf : forall B x p, unshift (lcounts B) x = y -> P (found B x p)) :
  option_map (unshift (lcounts B0)) (aget k0 t0) = Some y -> P (aget_with k0 t0 B0 found none).
Proof. intros Y; apply (aget_with'_prop k0 t0 B0 found none y P Hf Y); reflexivity. Qed.

Lemma aget_with_some k0 t0 B0 found none y (Rv : R)
  (Hf : forall B x p, unshift (lcounts B) x = y -> found B x p = Rv) :
  option_map (unshift (lcounts B0)) (aget k0 t0) = Some y -> aget_with k0 t0 B0 found none = Rv.
Proof. apply (aget_with_prop k0 t0 B0 found none y (fun z => z = Rv) Hf). Qed.

Lemma aget_with_none k0 t0 B0 found none (H : aget k0 t0 = None) :
  aget_with k0 t0 B0 found none = none (squash H).
Proof.
  unfold aget_with.
  assert (G : forall t k B H', option_map (unshift (lcounts B)) (aget k t) = option_map (unshift (lcounts B0)) (aget k0 t0) ->
                aget_with' k0 t0 B0 found none k t B H' = none (squash H)).
  { induction t as [|a l IHl o r IHr]; intros k B H' E; cbn [aget_with']; [reflexivity|].
    destruct k as [k|k|].
    + apply IHr; rewrite <- E; cbn [aget]; rewrite omap_unshift2; reflexivity.
    + apply IHl; rewrite <- E; cbn [aget]; rewrite omap_unshift2; reflexivity.
    + destruct o as [x|]; [|reflexivity]; cbn in E; rewrite H in E; discriminate. }
  apply G; reflexivity.
Qed.

Lemma knth_with_prop i0 s0 B0 found none y (P : R -> Prop)
  (Hf : forall B x p, unshift (lcounts B) x = y -> P (found B x p)) :
  option_map (unshift (lcounts B0)) (knth s0 i0) = Some y -> P (knth_with i0 s0 B0 found none).
Proof.
  intros Y; unfold knth_with.
  assert (Gt : forall t w i B H, option_map (unshift (lcounts B)) (ktnth w t i) = option_map (unshift (lcounts B0)) (knth s0 i0) ->
                 P (ktnth_with' i0 s0 B0 found none w t i B H)).
  { induction t as [x|a x l IHl r IHr]; intros w i B H E; cbn [ktnth_with'].
    - destruct i; cbn in E; rewrite Y in E; [|discriminate]; apply Hf; injection E as <-; reflexivity.
    - destruct i as [|j]; cbn [ktnth] in E.
      + cbn in E; rewrite Y in E; apply Hf; injection E as <-; rewrite unshift_unshift; reflexivity.
      + change (Squash (option_map (unshift (lcounts B)) (option_map (unshift a)
                  (if Nat.ltb j (Nat.div2 w) then ktnth (Nat.div2 w) l j else ktnth (Nat.div2 w) r (j - Nat.div2 w)))
                  = option_map (unshift (lcounts B0)) (knth s0 i0))) in H.
        revert H E; destruct (Nat.ltb j (Nat.div2 w)); intros H E; [apply IHl|apply IHr];
          rewrite <- E, omap_unshift2; reflexivity. }
  assert (Gp : forall s i B H, option_map (unshift (lcounts B)) (spnth s i) = option_map (unshift (lcounts B0)) (knth s0 i0) ->
                 P (spnth_with' i0 s0 B0 found none s i B H)).
  { induction s as [|w t s IH]; intros i B H E; cbn [spnth_with'].
    - cbn in E; rewrite Y in E; discriminate.
    - cbn [spnth] in E.
      change (Squash (option_map (unshift (lcounts B)) (if Nat.ltb i w then ktnth w t i else spnth s (i - w))
                      = option_map (unshift (lcounts B0)) (knth s0 i0))) in H.
      revert H E; destruct (Nat.ltb i w); intros H E; [apply Gt|apply IH]; exact E. }
  destruct s0 as [|a w t s]; cbn [knth_with']; [cbn in Y; discriminate|].
  apply Gp; cbn [knth]; rewrite omap_unshift2; reflexivity.
Qed.

Lemma knth_with_some i0 s0 B0 found none y (Rv : R)
  (Hf : forall B x p, unshift (lcounts B) x = y -> found B x p = Rv) :
  option_map (unshift (lcounts B0)) (knth s0 i0) = Some y -> knth_with i0 s0 B0 found none = Rv.
Proof. apply (knth_with_prop i0 s0 B0 found none y (fun z => z = Rv) Hf). Qed.

Lemma knth_with_none i0 s0 B0 found none (H : knth s0 i0 = None) :
  knth_with i0 s0 B0 found none = none (squash H).
Proof.
  unfold knth_with.
  assert (Gt : forall t w i B H', option_map (unshift (lcounts B)) (ktnth w t i) = option_map (unshift (lcounts B0)) (knth s0 i0) ->
                 ktnth_with' i0 s0 B0 found none w t i B H' = none (squash H)).
  { induction t as [x|a x l IHl r IHr]; intros w i B H' E; cbn [ktnth_with'].
    - destruct i; [cbn in E; rewrite H in E; discriminate|reflexivity].
    - destruct i as [|j]; cbn [ktnth] in E; [cbn in E; rewrite H in E; discriminate|].
      change (Squash (option_map (unshift (lcounts B)) (option_map (unshift a)
                (if Nat.ltb j (Nat.div2 w) then ktnth (Nat.div2 w) l j else ktnth (Nat.div2 w) r (j - Nat.div2 w)))
                = option_map (unshift (lcounts B0)) (knth s0 i0))) in H'.
      revert H' E; destruct (Nat.ltb j (Nat.div2 w)); intros H' E; [apply IHl|apply IHr];
        rewrite <- E, omap_unshift2; reflexivity. }
  assert (Gp : forall s i B H', option_map (unshift (lcounts B)) (spnth s i) = option_map (unshift (lcounts B0)) (knth s0 i0) ->
                 spnth_with' i0 s0 B0 found none s i B H' = none (squash H)).
  { induction s as [|w t s IH]; intros i B H' E; cbn [spnth_with']; [reflexivity|].
    cbn [spnth] in E.
    change (Squash (option_map (unshift (lcounts B)) (if Nat.ltb i w then ktnth w t i else spnth s (i - w))
                    = option_map (unshift (lcounts B0)) (knth s0 i0))) in H'.
    revert H' E; destruct (Nat.ltb i w); intros H' E; [apply Gt|apply IH]; exact E. }
  destruct s0 as [|a w t s]; cbn [knth_with']; [reflexivity|].
  apply Gp; cbn [knth]; rewrite omap_unshift2; reflexivity.
Qed.

End Lookups.
