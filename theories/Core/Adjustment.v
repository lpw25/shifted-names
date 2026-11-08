(** * Adjustments

    An [adjustment P] is a normal raw adjustment packaged with an SProp proof
    of normality.  Because the proof is in SProp, two adjustments are equal
    exactly when their raw data is equal, and by canonicity that happens
    exactly when they have the same action ([extensionality]).  So all the
    usual laws hold up to Leibniz equality. *)

From Stdlib Require Import PArith Arith List Lia Bool StrictProp.
From ShiftedNames.Core Require Import Trie Label Var RawAdjustment.
Import ListNotations.

(** ** Booleans as strict propositions *)

Definition Is_true_s (b : bool) : SProp := if b then sUnit else sEmpty.

Definition Is_true_s_intro {b : bool} : b = true -> Is_true_s b :=
  match b with
  | true => fun _ => stt
  | false => fun H => match diff_false_true H with end
  end.

Lemma Is_true_s_elim {b : bool} : Is_true_s b -> b = true.
Proof. destruct b; [reflexivity|intros []]. Qed.

(** ** The type of adjustments *)

Record adjustment (P : Type) : Type :=
  mk_adjustment {
    adj_raw : raw P;
    adj_normal : Is_true_s (normal adj_raw)
  }.

Arguments mk_adjustment {P} _ _.
Arguments adj_raw {P} _.
Arguments adj_normal {P} _.

Lemma adjustment_eq {P} (a b : adjustment P) : adj_raw a = adj_raw b -> a = b.
Proof. destruct a as [ra Ha], b as [rb Hb]; cbn; intros ->; reflexivity. Qed.

Section Adjustment.

Context {P : Type}.

Implicit Types (a b c : adjustment P) (v w : var) (l : option label).

Definition apply a v : var + P := RawAdjustment.apply (adj_raw a) v.

Lemma adj_normal_true a : normal (adj_raw a) = true.
Proof. apply Is_true_s_elim, adj_normal. Qed.

Theorem extensionality a b : (forall v, apply a v = apply b v) -> a = b.
Proof.
  intro H; apply adjustment_eq, canonical; auto using adj_normal_true.
Qed.

Definition identity : adjustment P := mk_adjustment RawAdjustment.identity stt.

Lemma apply_identity v : apply identity v = inl v.
Proof. apply RawAdjustment.apply_identity. Qed.

Definition compose (fp : P -> P) a b : adjustment P :=
  mk_adjustment
    (RawAdjustment.compose fp (adj_raw a) (adj_raw b))
    (Is_true_s_intro
       (normal_compose fp _ _ (adj_normal_true a) (adj_normal_true b))).

Theorem apply_compose fp a b v :
  apply (compose fp a b) v
  = match apply b v with
    | inl w => apply a w
    | inr p => inr (fp p)
    end.
Proof. apply RawAdjustment.apply_compose; apply adj_normal_true. Qed.

Theorem compose_identity_l fp b :
  (forall p, fp p = p) -> compose fp identity b = b.
Proof.
  intro Hfp; apply extensionality; intro v.
  rewrite apply_compose.
  destruct (apply b v); [apply apply_identity|rewrite Hfp; reflexivity].
Qed.

Theorem compose_identity_r fp a : compose fp a identity = a.
Proof.
  apply extensionality; intro v.
  rewrite apply_compose, apply_identity; reflexivity.
Qed.

Theorem compose_assoc fp1 fp2 fp3 fp4 a b c :
  (forall p, fp4 p = fp1 p) ->
  (forall p, fp1 (fp2 p) = fp3 p) ->
  compose fp1 a (compose fp2 b c) = compose fp3 (compose fp4 a b) c.
Proof.
  intros H4 H12; apply extensionality; intro v.
  rewrite !apply_compose.
  destruct (apply c v) as [w|p]; [|rewrite H12; reflexivity].
  rewrite apply_compose.
  destruct (apply b w); [reflexivity|rewrite H4; reflexivity].
Qed.

(** ** Building adjustments from raw data *)

Definition of_raw (r : raw P) (H : keys_ok r = true) : adjustment P :=
  mk_adjustment (normalize r) (Is_true_s_intro (normal_normalize r H)).

Lemma apply_of_raw r H v : apply (of_raw r H) v = RawAdjustment.apply r v.
Proof. apply apply_normalize, H. Qed.

Lemma keys_ok_single l (e : entry P) :
  e_label e = l -> keys_ok (set (label_key l) e Empty) = true.
Proof.
  intros He; unfold keys_ok; apply forallb_spec; intros key e' Hget.
  rewrite get_set, get_Empty in Hget.
  destruct (Pos.eqb_spec key (label_key l)) as [->|]; [|discriminate].
  injection Hget as <-; rewrite He; apply Pos.eqb_refl.
Qed.

(** A single entry for one label. *)
Definition single l (ts : list (target P)) (k : nat) : adjustment P :=
  of_raw (set (label_key l) (mk_entry l ts k) Empty)
    (keys_ok_single l (mk_entry l ts k) eq_refl).

Lemma apply_single l ts k v :
  apply (single l ts k) v
  = if label_eqb (v_label v) l then apply_entry l ts k (v_index v) else inl v.
Proof.
  unfold single; rewrite apply_of_raw.
  unfold RawAdjustment.apply, find.
  rewrite get_set, get_Empty, label_key_eqb.
  destruct (label_eqb_spec (v_label v) l) as [->|Hne]; [reflexivity|].
  unfold apply_entry; cbn [fst snd length].
  rewrite nth_error_nil, Nat.sub_0_r, Nat.add_0_r; reflexivity.
Qed.

(** ** Lifting under a binder

    [lift sp l a] is [a] moved under a binder labelled [l]: the new
    innermost [l₍₀₎] maps to itself, and everything else goes through [a]
    with [l] shifted past the new binder.  [sp] shifts payloads past the
    binder. *)

Definition lift_target (sp : P -> P) l (t : target P) : target P :=
  match t with
  | Rename w => Rename (shift_var (mk_var l 0) w)
  | Bind p => Bind (sp p)
  end.

Definition lift_raw (sp : P -> P) l (r : raw P) : raw P :=
  set (label_key l)
    (mk_entry l (Rename (mk_var l 0) :: map (lift_target sp l) (fst (find r l)))
       (S (snd (find r l))))
    (map_filter
       (fun _ e => Some (mk_entry (e_label e) (map (lift_target sp l) (e_targets e))
                                  (e_out e)))
       r).

Lemma keys_ok_lift_raw sp l r : keys_ok r = true -> keys_ok (lift_raw sp l r) = true.
Proof.
  unfold keys_ok; rewrite !forallb_spec; intros Hr key e He.
  unfold lift_raw in He; rewrite get_set in He.
  destruct (Pos.eqb_spec key (label_key l)) as [->|Hne].
  - injection He as <-; apply Pos.eqb_refl.
  - rewrite get_map_filter in He.
    destruct (get key r) as [e0|] eqn:E0; [|discriminate].
    injection He as <-; apply (Hr _ _ E0).
Qed.

Definition lift (sp : P -> P) l a : adjustment P :=
  of_raw (lift_raw sp l (adj_raw a))
    (keys_ok_lift_raw sp l _ (normal_keys_ok _ (adj_normal_true a))).

Lemma find_lift_raw sp l r h :
  keys_ok r = true ->
  find (lift_raw sp l r) h
  = if label_eqb h l
    then (Rename (mk_var l 0) :: map (lift_target sp l) (fst (find r l)),
          S (snd (find r l)))
    else (map (lift_target sp l) (fst (find r h)), snd (find r h)).
Proof.
  intros Hr; unfold find at 1; unfold lift_raw.
  rewrite get_set, label_key_eqb.
  destruct (label_eqb h l); [reflexivity|].
  rewrite get_map_filter; unfold find.
  destruct (get (label_key h) r); reflexivity.
Qed.

Lemma apply_entry_map_lift_target sp l h ts k i :
  h <> l ->
  apply_entry h (map (lift_target sp l) ts) k i
  = match apply_entry h ts k i with
    | inl w => inl (shift_var (mk_var l 0) w)
    | inr p => inr (sp p)
    end.
Proof.
  intros Hne; unfold apply_entry.
  rewrite nth_error_map, length_map.
  destruct (nth_error ts i) as [[w|p]|]; cbn; try reflexivity.
  f_equal; unfold shift_var; cbn.
  destruct (label_eqb_spec l h); [congruence|reflexivity].
Qed.

Theorem apply_lift sp l a v :
  apply (lift sp l a) v
  = if var_eqb v (mk_var l 0) then inl v
    else match apply a (unshift_var (mk_var l 0) v) with
         | inl w => inl (shift_var (mk_var l 0) w)
         | inr p => inr (sp p)
         end.
Proof.
  pose proof (normal_keys_ok _ (adj_normal_true a)) as Hk.
  unfold lift; rewrite apply_of_raw.
  unfold RawAdjustment.apply at 1; rewrite find_lift_raw by exact Hk.
  unfold apply, RawAdjustment.apply.
  destruct v as [h i]; cbn [v_label v_index].
  unfold var_eqb, unshift_var; cbn [v_label v_index].
  destruct (label_eqb_spec h l) as [->|Hne]; cbn [andb fst snd].
  - destruct i as [|i]; cbn [Nat.eqb Nat.ltb Nat.leb].
    + reflexivity.
    + rewrite label_eqb_refl; cbn [andb pred v_label v_index].
      replace (S i - 1) with i by lia.
      unfold apply_entry; cbn [nth_error length].
      rewrite nth_error_map, length_map.
      destruct (nth_error (fst (find (adj_raw a) l)) i) as [[w|p]|] eqn:E;
        cbn [option_map lift_target target_result]; try reflexivity.
      unfold shift_var; cbn [v_label v_index].
      rewrite label_eqb_refl; cbn [andb Nat.leb].
      f_equal; f_equal; lia.
  - assert (Hlh : label_eqb l h = false) by (apply label_eqb_neq; congruence).
    rewrite Hlh; cbn [andb v_label v_index].
    apply apply_entry_map_lift_target; exact Hne.
Qed.

End Adjustment.

(** ** Primitive adjustments *)

Section Primitives.

Context {P : Type}.

Definition no_payload (p : P) : P := p.

(** [shift l]: weaken by one [l]; every [l₍ᵢ₎] becomes [l₍ᵢ₊₁₎]. *)
Definition shift l : adjustment P := single l [] 1.

(** [rename1 l1 l2]: the innermost [l1] becomes a new innermost [l2]. *)
Definition rename1 l1 l2 : adjustment P :=
  compose no_payload (single l1 [Rename (mk_var l2 0)] 0) (single l2 [] 1).

(** Opening a bound variable as [x], and closing [x] into a bound variable. *)
Definition open (x : label) : adjustment P := rename1 None (Some x).
Definition close (x : label) : adjustment P := rename1 (Some x) None.

(** [swap l] exchanges the two innermost [l]s. *)
Definition swap l : adjustment P :=
  single l [Rename (mk_var l 1); Rename (mk_var l 0)] 2.

(** [subst1 l p]: the innermost [l] is replaced by the payload [p]. *)
Definition subst1 l (p : P) : adjustment P := single l [Bind p] 0.

Lemma apply_shift l v : apply (shift l) v = inl (shift_var (mk_var l 0) v).
Proof.
  unfold shift; rewrite apply_single.
  destruct v as [h i]; unfold shift_var, apply_entry; cbn [v_label v_index length].
  rewrite nth_error_nil; case_vars.
Qed.

Lemma apply_capture l (t : target P) v :
  apply (single l [t] 0) v
  = if var_eqb v (mk_var l 0) then target_result t
    else inl (unshift_var (mk_var l 0) v).
Proof.
  rewrite apply_single.
  destruct v as [h [|i]]; unfold var_eqb, unshift_var, apply_entry;
    cbn [v_label v_index nth_error length].
  - case_vars.
  - rewrite nth_error_nil; case_vars.
Qed.

Lemma apply_rename1 l1 l2 v :
  apply (rename1 l1 l2) v
  = inl (if var_eqb v (mk_var l1 0) then mk_var l2 0
         else shift_var (mk_var l2 0) (unshift_var (mk_var l1 0) v)).
Proof.
  unfold rename1; rewrite apply_compose.
  change (single l2 [] 1) with (shift l2); rewrite apply_shift.
  rewrite apply_capture; cbn [target_result].
  destruct v as [h i]; unfold var_eqb, shift_var, unshift_var; case_vars.
Qed.

End Primitives.
