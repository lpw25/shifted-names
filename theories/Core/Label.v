(** * Labels

    A label is a string naming a family of free names.  Variables carry an
    [option label]: [Some s] for the free names [s₍ᵢ₎] and [None] for the
    anonymous label of bound (de Bruijn) variables.

    This file provides:
    - decidable equality on [option label];
    - a strict total order [olabel_lt] that computes on concrete labels, used
      for side conditions about symbolic labels;
    - an injective encoding [label_key] of [option label] into [positive],
      used as the key of canonical tries. *)

From Stdlib Require Import Ascii String PArith Arith Bool Lia List.

Definition label := string.

(** ** The order on ascii characters and strings

    Characters are compared bit by bit, most significant bit first; strings
    lexicographically. *)

Definition is_less_than_ascii (a1 : ascii) (a2 : ascii) :=
  match a1, a2 with
  | Ascii b11 b12 b13 b14 b15 b16 b17 b18,
    Ascii b21 b22 b23 b24 b25 b26 b27 b28 =>
    match b18, b28 with
    | true, false => false
    | false, true => true
    | _, _ =>
      match b17, b27 with
      | true, false => false
      | false, true => true
      | _, _ =>
        match b16, b26 with
        | true, false => false
        | false, true => true
        | _, _ =>
          match b15, b25 with
          | true, false => false
          | false, true => true
          | _, _ =>
            match b14, b24 with
            | true, false => false
            | false, true => true
            | _, _ =>
              match b13, b23 with
              | true, false => false
              | false, true => true
              | _, _ =>
                match b12, b22 with
                | true, false => false
                | false, true => true
                | _, _ =>
                  match b11, b21 with
                  | true, false => false
                  | false, true => true
                  | _, _ => false
                  end
                end
              end
            end
          end
        end
      end
    end
  end.

Fixpoint is_less_than_label s1 s2 :=
  match s1, s2 with
  | EmptyString, EmptyString => false
  | String a1 s1, EmptyString => false
  | EmptyString, String a2 s2 => true
  | String a1 s1, String a2 s2 =>
    if is_less_than_ascii a1 a2 then true
    else if is_less_than_ascii a2 a1 then false
    else is_less_than_label s1 s2
  end.

Lemma is_less_than_ascii_asymmetric a1 a2 :
  is_less_than_ascii a1 a2 = true ->
  is_less_than_ascii a2 a1 = false.
Proof.
  destruct a1 as [b1 b2 b3 b4 b5 b6 b7 b8],
    a2 as [b9 b10 b11 b12 b13 b14 b15 b16].
  destruct b8, b16; try easy;
    destruct b7, b15; try easy;
      destruct b6, b14; try easy;
        destruct b5, b13; try easy;
          destruct b4, b12; try easy;
            destruct b3, b11; try easy;
              destruct b2, b10; try easy;
                destruct b1, b9; easy.
Qed.

Lemma is_less_than_ascii_total a1 a2 :
  is_less_than_ascii a1 a2 = false ->
  is_less_than_ascii a2 a1 = false ->
  a1 = a2.
Proof.
  destruct a1 as [b1 b2 b3 b4 b5 b6 b7 b8],
    a2 as [b9 b10 b11 b12 b13 b14 b15 b16].
  destruct b8, b16; try easy;
    destruct b7, b15; try easy;
      destruct b6, b14; try easy;
        destruct b5, b13; try easy;
          destruct b4, b12; try easy;
            destruct b3, b11; try easy;
              destruct b2, b10; try easy;
                destruct b1, b9; easy.
Qed.

Lemma is_less_than_ascii_transitive a1 a2 a3 :
  is_less_than_ascii a1 a2 = true ->
  is_less_than_ascii a2 a3 = true ->
  is_less_than_ascii a1 a3 = true.
Proof.
  destruct a1 as [b1 b2 b3 b4 b5 b6 b7 b8],
    a2 as [b9 b10 b11 b12 b13 b14 b15 b16],
      a3 as [b17 b18 b19 b20 b21 b22 b23 b24].
  destruct b8, b16, b24; try easy;
    destruct b7, b15, b23; try easy;
      destruct b6, b14, b22; try easy;
        destruct b5, b13, b21; try easy;
          destruct b4, b12, b20; try easy;
            destruct b3, b11, b19; try easy;
              destruct b2, b10, b18; try easy;
                destruct b1, b9, b17; easy.
Qed.

Lemma is_less_than_label_asymmetric s1 s2 :
  is_less_than_label s1 s2 = true ->
  is_less_than_label s2 s1 = false.
Proof.
  generalize dependent s2.
  induction s1 as [|a1 s1];
    destruct s2 as [|a2 s2]; cbn; try easy.
  destruct (is_less_than_ascii a1 a2) eqn:Heq1;
    [|destruct (is_less_than_ascii a2 a1) eqn:Heq2];
    try easy.
  - replace (is_less_than_ascii a2 a1) with false
      by (symmetry;
          apply is_less_than_ascii_asymmetric; easy).
    easy.
  - apply IHs1.
Qed.

Lemma is_less_than_label_total s1 s2 :
  is_less_than_label s1 s2 = false ->
  is_less_than_label s2 s1 = false ->
  s1 = s2.
Proof.
  generalize dependent s2.
  induction s1 as [|a1 s1];
    destruct s2 as [|a2 s2]; cbn; try easy.
  destruct (is_less_than_ascii a1 a2) eqn:Heq1;
    [|destruct (is_less_than_ascii a2 a1) eqn:Heq2];
    try easy.
  replace a2 with a1
    by (apply is_less_than_ascii_total; easy).
  intros; replace s2 with s1 by (apply IHs1; easy).
  easy.
Qed.

Lemma is_less_than_label_transitive s1 s2 s3 :
  is_less_than_label s1 s2 = true ->
  is_less_than_label s2 s3 = true ->
  is_less_than_label s1 s3 = true.
Proof.
  generalize dependent s2.
  generalize dependent s3.
  induction s1 as [|a1 s1];
    destruct s2 as [|a2 s2], s3 as [|a3 s3]; cbn; try easy.
  destruct (is_less_than_ascii a1 a2) eqn:Heq1;
    [|destruct (is_less_than_ascii a2 a1) eqn:Heq2];
    try easy.
  - destruct (is_less_than_ascii a2 a3) eqn:Heq3;
      [|destruct (is_less_than_ascii a3 a2) eqn:Heq4];
      try easy.
    + replace (is_less_than_ascii a1 a3) with true
        by (symmetry; apply is_less_than_ascii_transitive
              with (a2 := a2); easy).
      easy.
    + replace a3 with a2
        by (apply is_less_than_ascii_total; easy).
      rewrite Heq1; easy.
  - replace a1 with a2
      by (apply is_less_than_ascii_total; easy).
    destruct (is_less_than_ascii a2 a3) eqn:Heq3;
      [|destruct (is_less_than_ascii a3 a2) eqn:Heq4];
      try easy.
    apply IHs1.
Qed.


(** ** The strict total order on labels

    The order the library's side conditions are stated with: [label_lt x y],
    decided by [label_compare]. *)

Definition label_ltb (x y : label) : bool := is_less_than_label x y.

Definition label_lt (x y : label) : Prop := label_ltb x y = true.

Lemma label_lt_irrefl x : ~ label_lt x x.
Proof. unfold label_lt, label_ltb; intro H; pose proof (is_less_than_label_asymmetric x x H); congruence. Qed.

Lemma label_lt_asym x y : label_lt x y -> ~ label_lt y x.
Proof. unfold label_lt, label_ltb; intros H1 H2; rewrite (is_less_than_label_asymmetric x y H1) in H2; discriminate. Qed.

Lemma label_lt_trans x y z : label_lt x y -> label_lt y z -> label_lt x z.
Proof. apply is_less_than_label_transitive. Qed.

Definition label_compare (x y : label) : comparison :=
  if label_ltb x y then Lt else if label_ltb y x then Gt else Eq.

Lemma label_compare_spec x y : CompareSpec (x = y) (label_lt x y) (label_lt y x) (label_compare x y).
Proof.
  unfold label_compare, label_lt.
  destruct (label_ltb x y) eqn:H1; [constructor; reflexivity|].
  destruct (label_ltb y x) eqn:H2; [constructor; reflexivity|].
  constructor; apply is_less_than_label_total; assumption.
Qed.

Lemma label_trichotomy x y : label_lt x y \/ x = y \/ label_lt y x.
Proof. destruct (label_compare_spec x y); auto. Qed.

(** ** Equality on [option label] *)

Definition label_eqb (l1 l2 : option label) : bool :=
  match l1, l2 with
  | None, None => true
  | Some s1, Some s2 => String.eqb s1 s2
  | _, _ => false
  end.

Lemma label_eqb_spec l1 l2 : reflect (l1 = l2) (label_eqb l1 l2).
Proof.
  destruct l1 as [s1|], l2 as [s2|]; cbn; try (constructor; congruence).
  destruct (String.eqb_spec s1 s2); constructor; congruence.
Qed.

Lemma label_eqb_eq l1 l2 : label_eqb l1 l2 = true <-> l1 = l2.
Proof. destruct (label_eqb_spec l1 l2); split; congruence. Qed.

Lemma label_eqb_refl l : label_eqb l l = true.
Proof. apply label_eqb_eq; reflexivity. Qed.

Lemma label_eqb_neq l1 l2 : label_eqb l1 l2 = false <-> l1 <> l2.
Proof. destruct (label_eqb_spec l1 l2); split; congruence. Qed.

Definition label_eq_dec (l1 l2 : option label) : {l1 = l2} + {l1 <> l2}.
Proof. destruct (label_eqb_spec l1 l2); [left|right]; assumption. Defined.

(** ** The strict total order on [option label] (internal)

    Named labels come before the anonymous label. *)

Definition olabel_ltb (l1 l2 : option label) : bool :=
  match l1, l2 with
  | None, _ => false
  | Some _, None => true
  | Some s1, Some s2 => is_less_than_label s1 s2
  end.

Definition olabel_lt (l1 l2 : option label) : Prop := olabel_ltb l1 l2 = true.

Lemma olabel_lt_irrefl l : ~ olabel_lt l l.
Proof.
  unfold olabel_lt; destruct l as [s|]; cbn; [|discriminate].
  intro H; pose proof (is_less_than_label_asymmetric s s H) as H'.
  congruence.
Qed.

Lemma olabel_lt_asym l1 l2 : olabel_lt l1 l2 -> ~ olabel_lt l2 l1.
Proof.
  unfold olabel_lt; destruct l1 as [s1|], l2 as [s2|]; cbn; try discriminate.
  intros H1 H2; rewrite (is_less_than_label_asymmetric s1 s2 H1) in H2.
  discriminate.
Qed.

Lemma olabel_lt_trans l1 l2 l3 :
  olabel_lt l1 l2 -> olabel_lt l2 l3 -> olabel_lt l1 l3.
Proof.
  unfold olabel_lt; destruct l1 as [s1|], l2 as [s2|], l3 as [s3|];
    cbn; try discriminate; try reflexivity.
  apply is_less_than_label_transitive.
Qed.

Definition olabel_compare (l1 l2 : option label) : comparison :=
  if olabel_ltb l1 l2 then Lt
  else if olabel_ltb l2 l1 then Gt
  else Eq.

Lemma olabel_compare_spec l1 l2 :
  CompareSpec (l1 = l2) (olabel_lt l1 l2) (olabel_lt l2 l1)
    (olabel_compare l1 l2).
Proof.
  unfold olabel_compare, olabel_lt.
  destruct (olabel_ltb l1 l2) eqn:H12; [constructor; reflexivity|].
  destruct (olabel_ltb l2 l1) eqn:H21; [constructor; reflexivity|].
  constructor.
  destruct l1 as [s1|], l2 as [s2|]; cbn in *; try discriminate; auto.
  f_equal; apply is_less_than_label_total; assumption.
Qed.

Lemma olabel_trichotomy l1 l2 : olabel_lt l1 l2 \/ l1 = l2 \/ olabel_lt l2 l1.
Proof. destruct (olabel_compare_spec l1 l2); auto. Qed.

(** ** Encoding labels as trie keys *)

Definition push_bit (b : bool) (p : positive) : positive :=
  if b then xI p else xO p.

Definition push_ascii (a : ascii) (p : positive) : positive :=
  match a with
  | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
      push_bit b0 (push_bit b1 (push_bit b2 (push_bit b3
        (push_bit b4 (push_bit b5 (push_bit b6 (push_bit b7 p)))))))
  end.

Fixpoint string_key (s : string) : positive :=
  match s with
  | EmptyString => xH
  | String a s => push_ascii a (string_key s)
  end.

Definition label_key (l : option label) : positive :=
  match l with
  | None => xH
  | Some s => xO (string_key s)
  end.

Lemma push_bit_inj b1 b2 p1 p2 :
  push_bit b1 p1 = push_bit b2 p2 -> b1 = b2 /\ p1 = p2.
Proof. destruct b1, b2; cbn; intro H; try discriminate; injection H; auto. Qed.

Lemma push_ascii_inj a1 a2 p1 p2 :
  push_ascii a1 p1 = push_ascii a2 p2 -> a1 = a2 /\ p1 = p2.
Proof.
  destruct a1, a2; cbn; intro H.
  repeat match goal with
         | H : push_bit _ _ = push_bit _ _ |- _ =>
             apply push_bit_inj in H; destruct H as [<- H]
         end.
  auto.
Qed.

Lemma push_ascii_not_xH a p : push_ascii a p <> xH.
Proof. destruct a as [[|] ? ? ? ? ? ? ?]; discriminate. Qed.

Lemma string_key_inj s1 s2 : string_key s1 = string_key s2 -> s1 = s2.
Proof.
  revert s2; induction s1 as [|a1 s1 IH]; intros [|a2 s2]; cbn; intro H.
  - reflexivity.
  - symmetry in H; apply push_ascii_not_xH in H; destruct H.
  - apply push_ascii_not_xH in H; destruct H.
  - apply push_ascii_inj in H; destruct H as [-> H].
    f_equal; apply IH, H.
Qed.

Lemma label_key_inj l1 l2 : label_key l1 = label_key l2 -> l1 = l2.
Proof.
  destruct l1 as [s1|], l2 as [s2|]; cbn; intro H; try discriminate.
  - injection H as H; f_equal; apply string_key_inj, H.
  - reflexivity.
Qed.

Lemma label_key_eqb l1 l2 :
  Pos.eqb (label_key l1) (label_key l2) = label_eqb l1 l2.
Proof.
  destruct (label_eqb_spec l1 l2) as [<-|Hne].
  - apply Pos.eqb_refl.
  - apply Pos.eqb_neq; intro H; apply Hne, label_key_inj, H.
Qed.

Lemma label_eqb_sym l1 l2 : label_eqb l1 l2 = label_eqb l2 l1.
Proof.
  destruct (label_eqb_spec l1 l2) as [<-|H]; [rewrite label_eqb_refl; reflexivity|].
  symmetry; apply label_eqb_neq; intro; apply H; symmetry; assumption.
Qed.



(** ** Decoding keys *)

Definition ascii_of_bits (bs : list bool) : ascii :=
  match bs with
  | (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: nil)%list => Ascii b0 b1 b2 b3 b4 b5 b6 b7
  | _ => Ascii false false false false false false false false
  end.

(** [decode p acc]: [acc] holds the bits of the current character read so
    far. *)
Fixpoint decode (p : positive) (acc : list bool) : option string :=
  match p with
  | xH => match acc with nil => Some EmptyString | _ => None end
  | xO q | xI q =>
      let acc' := (acc ++ (match p with xI _ => true | _ => false end :: nil))%list in
      if Nat.eqb (List.length acc') 8
      then match decode q nil with Some s => Some (String (ascii_of_bits acc') s) | None => None end
      else decode q acc'
  end.

Definition key_label (k : positive) : option (option label) :=
  match k with
  | xH => Some None
  | xO q => match decode q nil with Some s => Some (Some s) | None => None end
  | xI _ => None
  end.

Lemma decode_push_bit b p acc :
  List.length acc < 7 -> decode (push_bit b p) acc = decode p (acc ++ (b :: nil))%list.
Proof.
  intros H; destruct b; cbn [push_bit decode];
    rewrite List.length_app; cbn [List.length];
    rewrite (proj2 (Nat.eqb_neq _ 8)) by lia; reflexivity.
Qed.

Lemma decode_string_key s : decode (string_key s) nil = Some s.
Proof.
  induction s as [|[b0 b1 b2 b3 b4 b5 b6 b7] s IH]; [reflexivity|].
  cbn [string_key push_ascii].
  rewrite !decode_push_bit by (cbn; lia).
  destruct b7; cbn [push_bit decode List.app List.length Nat.eqb]; rewrite IH; reflexivity.
Qed.

Lemma key_label_spec l : key_label (label_key l) = Some l.
Proof. destruct l as [s|]; cbn; [rewrite decode_string_key|]; reflexivity. Qed.

