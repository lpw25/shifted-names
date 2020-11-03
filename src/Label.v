Require Import Ascii String StrictProp.

Definition label := string.

Definition label_dec s1 s2 := string_dec s1 s2.
Arguments label_dec !s1 !s2.

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

Definition less_than_label s1 s2 :=
  if is_less_than_label s1 s2 then sUnit else sEmpty.

Definition label_opt_dec (so1 so2 : option label)
  : {so1 = so2} + {so1 <> so2}.
  decide equality.
  apply label_dec.
Defined.

Definition label_opt_eqb s1 s2 : bool :=
  match label_opt_dec s1 s2 with
  | left _ => true
  | right _ => false
  end.

Lemma label_opt_eqb_reflexive so :
  label_opt_eqb so so = true.
Proof.
  unfold label_opt_eqb; destruct label_opt_dec; easy.
Qed.

Lemma label_opt_eqb_symmetric so1 so2 :
  label_opt_eqb so1 so2 = label_opt_eqb so2 so1.
Proof.
  unfold label_opt_eqb.
  destruct (label_opt_dec so1 so2), (label_opt_dec so2 so1);
    try congruence; easy.
Qed.

Lemma label_opt_eqb_transitive so1 so2 so3 :
  label_opt_eqb so1 so2 = true ->
  label_opt_eqb so2 so3 = label_opt_eqb so1 so3.
Proof.
  intros H; unfold label_opt_eqb in H.
  destruct (label_opt_dec so1 so2) as [Heq|]; try easy.
  rewrite Heq; easy.
Qed.

Definition is_less_than_label_opt so1 so2 :=
  match so1, so2 with
  | None, None => false
  | Some s1, None => true
  | None, Some s2 => false
  | Some s1, Some s2 => is_less_than_label s1 s2
  end.

Definition less_than_label_opt so1 so2 :=
  if is_less_than_label_opt so1 so2 then sUnit else sEmpty.

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

Lemma is_less_than_label_opt_asymmetric so1 so2 :
  is_less_than_label_opt so1 so2 = true ->
  is_less_than_label_opt so2 so1 = false.
Proof.
  destruct so1, so2; cbn; try easy.
  apply is_less_than_label_asymmetric.
Qed.

Lemma is_less_than_label_opt_total so1 so2 :
  is_less_than_label_opt so1 so2 = false ->
  is_less_than_label_opt so2 so1 = false ->
  so1 = so2.
Proof.
  intros.
  destruct so1 as [s1|], so2 as [s2|]; cbn; try easy.
  replace s1 with s2
    by (apply is_less_than_label_total; easy).
  easy.
Qed.

Lemma is_less_than_label_opt_transitive so1 so2 so3 :
  is_less_than_label_opt so1 so2 = true ->
  is_less_than_label_opt so2 so3 = true ->
  is_less_than_label_opt so1 so3 = true.
Proof.
  destruct so1, so2, so3; cbn; try easy.
  apply is_less_than_label_transitive.
Qed.

Lemma is_less_than_label_opt_irreflexive so :
  is_less_than_label_opt so so = false.
Proof.
  destruct (is_less_than_label_opt so so) eqn:Heq1; try easy.
  apply is_less_than_label_opt_asymmetric in Heq1 as Heq2.
  rewrite Heq2 in Heq1; easy.
Qed.
