(** * Adjustments with slot references counted from the inside

    In the specification form (RawAdjustment.v) a renaming target is a
    variable [h₍ᵢ₎] of the outer scope.  Adding an output slot for [h]
    ([push_outer h]) changes the index of every [h] in the outer scope, so
    every target mentioning [h] would have to be rewritten.

    Here a reference to [h] is encoded relative to the output slots for [h],
    counting from the innermost constructor (the oldest slot):

    - [ESlot h l] is the slot [l] places in from the innermost constructor,
      which is [h₍ₖ₋₁₋ₗ₎] when there are [k] slots;
    - [ETail h m] is the [m]-th [h] beyond the slots, [h₍ₖ₊ₘ₎].

    Adding a slot only increments [k]; no reference changes.  Removing the
    innermost slot (when normalisation strips a transparent pair) is the one
    operation that re-encodes references to [h].

    [decode] maps this form back to the specification form.  Operations are
    proved correct through it, and canonicity follows from canonicity of the
    specification form plus injectivity of [decode]. *)

From Stdlib Require Import PArith Arith List Lia Bool.
From ShiftedNames.Core Require Import Trie Label Var RawAdjustment.
Import ListNotations.

Inductive etarget (P : Type) : Type :=
| ESlot : option label -> nat -> etarget P
| ETail : option label -> nat -> etarget P
| EBind : P -> etarget P.

Arguments ESlot {P} _ _.
Arguments ETail {P} _ _.
Arguments EBind {P} _.

Record eentry (P : Type) : Type :=
  mk_eentry { ee_label : option label; ee_targets : list (etarget P); ee_out : nat }.

Arguments mk_eentry {P} _ _ _.
Arguments ee_label {P} _.
Arguments ee_targets {P} _.
Arguments ee_out {P} _.

Definition eraw (P : Type) : Type := tree (eentry P).

Section Encoded.

Context {P : Type}.

Implicit Types (a b : eraw P) (r : raw P) (h l : option label) (v w : var)
  (et : etarget P) (cnt : option label -> nat).

(** ** Encoding and decoding single targets, given the slot counts *)

Definition dec cnt et : target P :=
  match et with
  | ESlot h l => Rename (mk_var h (cnt h - S l))
  | ETail h m => Rename (mk_var h (cnt h + m))
  | EBind p => Bind p
  end.

Definition enc cnt (t : target P) : etarget P :=
  match t with
  | Rename w =>
      if Nat.ltb (v_index w) (cnt (v_label w))
      then ESlot (v_label w) (cnt (v_label w) - S (v_index w))
      else ETail (v_label w) (v_index w - cnt (v_label w))
  | Bind p => EBind p
  end.

Definition wf_target cnt et : bool :=
  match et with
  | ESlot h l => Nat.ltb l (cnt h)
  | _ => true
  end.

Lemma dec_enc cnt t : dec cnt (enc cnt t) = t.
Proof.
  destruct t as [[h i]|p]; cbn [enc dec v_label v_index]; [|reflexivity].
  destruct (Nat.ltb_spec i (cnt h)); cbn [dec]; f_equal; f_equal; lia.
Qed.

Lemma wf_enc cnt t : wf_target cnt (enc cnt t) = true.
Proof.
  destruct t as [[h i]|p]; cbn [enc v_label v_index]; [|reflexivity].
  destruct (Nat.ltb_spec i (cnt h)); cbn [wf_target]; [apply Nat.ltb_lt; lia|reflexivity].
Qed.

Lemma dec_inj cnt et1 et2 :
  wf_target cnt et1 = true -> wf_target cnt et2 = true ->
  dec cnt et1 = dec cnt et2 -> et1 = et2.
Proof.
  destruct et1 as [h1 l1|h1 m1|p1], et2 as [h2 l2|h2 m2|p2];
    cbn [wf_target dec]; rewrite ?Nat.ltb_lt; intros H1 H2 H; try discriminate.
  all: injection H; intros; subst; first [reflexivity | f_equal; lia | exfalso; lia].
Qed.

Lemma map_dec_inj cnt ts1 ts2 :
  List.forallb (wf_target cnt) ts1 = true -> List.forallb (wf_target cnt) ts2 = true ->
  map (dec cnt) ts1 = map (dec cnt) ts2 -> ts1 = ts2.
Proof.
  revert ts2; induction ts1 as [|t1 ts1 IH]; intros [|t2 ts2]; cbn;
    try discriminate; [reflexivity|].
  rewrite !andb_true_iff; intros [H1 H1s] [H2 H2s] H; injection H as Ht Hs.
  f_equal; [apply (dec_inj cnt); assumption|apply IH; assumption].
Qed.

(** ** Whole adjustments *)

Definition out_count a h : nat :=
  match get (label_key h) a with Some e => ee_out e | None => 0 end.

Definition efind a h : list (etarget P) * nat :=
  match get (label_key h) a with
  | Some e => (ee_targets e, ee_out e)
  | None => ([], 0)
  end.

Lemma out_count_efind a h : out_count a h = snd (efind a h).
Proof. unfold out_count, efind; destruct (get _ a); reflexivity. Qed.

Definition decode_entry cnt (e : eentry P) : entry P :=
  mk_entry (ee_label e) (map (dec cnt) (ee_targets e)) (ee_out e).

Definition decode a : raw P := map_filter (fun _ e => Some (decode_entry (out_count a) e)) a.

Definition rcount r h : nat := snd (find r h).

Definition encode_entry cnt (e : entry P) : eentry P :=
  mk_eentry (e_label e) (map (enc cnt) (e_targets e)) (e_out e).

Definition encode r : eraw P := map_filter (fun _ e => Some (encode_entry (rcount r) e)) r.

Definition enc_wf a : bool :=
  forallb (fun _ e => List.forallb (wf_target (out_count a)) (ee_targets e)) a.

Definition enc_normal a : bool := enc_wf a && normal (decode a).

Lemma find_decode a h :
  find (decode a) h = (map (dec (out_count a)) (fst (efind a h)), snd (efind a h)).
Proof.
  unfold find, decode, efind; rewrite get_map_filter.
  destruct (get (label_key h) a); reflexivity.
Qed.

Lemma rcount_decode a h : rcount (decode a) h = out_count a h.
Proof. unfold rcount; rewrite find_decode, out_count_efind; reflexivity. Qed.

Lemma out_count_encode r h : out_count (encode r) h = rcount r h.
Proof.
  unfold out_count, encode, rcount, find; rewrite get_map_filter.
  destruct (get (label_key h) r); reflexivity.
Qed.

Lemma dec_ext cnt1 cnt2 et :
  (forall h, cnt1 h = cnt2 h) -> dec cnt1 et = dec cnt2 et.
Proof. intro H; destruct et; cbn [dec]; rewrite ?H; reflexivity. Qed.

Lemma wf_target_ext cnt1 cnt2 et :
  (forall h, cnt1 h = cnt2 h) -> wf_target cnt1 et = wf_target cnt2 et.
Proof. intro H; destruct et; cbn [wf_target]; rewrite ?H; reflexivity. Qed.

Theorem decode_encode r : decode (encode r) = r.
Proof.
  apply extensionality; intro key.
  unfold decode at 1; rewrite get_map_filter.
  assert (E : get key (encode r) = option_map (encode_entry (rcount r)) (get key r))
    by (unfold encode; rewrite get_map_filter; destruct (get key r); reflexivity).
  rewrite E.
  destruct (get key r) as [[h ts k]|]; [|reflexivity].
  unfold decode_entry, encode_entry;
    cbn [option_map ee_label ee_targets ee_out e_label e_targets e_out].
  do 2 f_equal; rewrite map_map.
  rewrite <- (map_id ts) at 2; apply map_ext; intro t.
  rewrite (dec_ext _ (rcount r)) by apply out_count_encode.
  apply dec_enc.
Qed.

Theorem enc_wf_encode r : enc_wf (encode r) = true.
Proof.
  unfold enc_wf; apply forallb_spec; intros key e He.
  unfold encode in He; rewrite get_map_filter in He.
  destruct (get key r) as [e0|]; [|discriminate]; injection He as <-.
  apply List.forallb_forall; intros et Hin.
  unfold encode_entry in Hin; cbn [ee_targets] in Hin.
  apply in_map_iff in Hin as [t [<- _]].
  rewrite (wf_target_ext _ (rcount r)) by apply out_count_encode.
  apply wf_enc.
Qed.

Theorem enc_normal_encode r : normal r = true -> enc_normal (encode r) = true.
Proof. intro Hr; unfold enc_normal; rewrite enc_wf_encode, decode_encode, Hr; reflexivity. Qed.

(** ** Decoding is injective on well-formed data *)

Lemma get_decode a key :
  get key (decode a) = option_map (decode_entry (out_count a)) (get key a).
Proof. unfold decode; rewrite get_map_filter; destruct (get key a); reflexivity. Qed.

Theorem decode_inj a b :
  enc_wf a = true -> enc_wf b = true -> decode a = decode b -> a = b.
Proof.
  intros Ha Hb Heq.
  assert (Hcnt : forall h, out_count a h = out_count b h).
  { intro h; rewrite <- !rcount_decode, Heq; reflexivity. }
  apply extensionality; intro key.
  pose proof (f_equal (get key) Heq) as Hk; rewrite !get_decode in Hk.
  destruct (get key a) as [ea|] eqn:Ea, (get key b) as [eb|] eqn:Eb;
    cbn [option_map] in Hk; try discriminate; [|reflexivity].
  injection Hk as Hl Ht Ho.
  destruct ea as [la tsa ka], eb as [lb tsb kb]; cbn in *; subst.
  f_equal; f_equal.
  unfold enc_wf in Ha, Hb; rewrite forallb_spec in Ha, Hb.
  specialize (Ha _ _ Ea); specialize (Hb _ _ Eb); cbn [ee_targets] in Ha, Hb.
  apply (map_dec_inj (out_count a)); [exact Ha| |].
  - rewrite List.forallb_forall in *; intros et Hin.
    rewrite (wf_target_ext _ (out_count b)) by exact Hcnt; apply Hb, Hin.
  - rewrite Ht; apply map_ext; intro et; apply dec_ext; intro h; symmetry; apply Hcnt.
Qed.

(** ** Lookup *)

Definition apply_enc a v : var + P :=
  match nth_error (fst (efind a (v_label v))) (v_index v) with
  | Some et => target_result (dec (out_count a) et)
  | None => inl (mk_var (v_label v)
                   (v_index v - length (fst (efind a (v_label v)))
                    + snd (efind a (v_label v))))
  end.

Theorem apply_enc_spec a v : apply_enc a v = apply (decode a) v.
Proof.
  unfold apply_enc, apply, apply_entry; rewrite find_decode; cbn [fst snd].
  rewrite nth_error_map, length_map.
  destruct (nth_error _ _); reflexivity.
Qed.

Theorem enc_canonical a b :
  enc_normal a = true -> enc_normal b = true ->
  (forall v, apply_enc a v = apply_enc b v) -> a = b.
Proof.
  unfold enc_normal; rewrite !andb_true_iff; intros [Wa Na] [Wb Nb] H.
  apply decode_inj; try assumption.
  apply canonical; try assumption.
  intro v; rewrite <- !apply_enc_spec; apply H.
Qed.

(** ** Identity and composition *)

Definition enc_identity : eraw P := Empty.

Lemma apply_enc_identity v : apply_enc enc_identity v = inl v.
Proof.
  rewrite apply_enc_spec; unfold decode, enc_identity, map_filter.
  apply apply_identity.
Qed.

Definition enc_compose (fp : P -> P) a b : eraw P :=
  encode (compose fp (decode a) (decode b)).

Theorem apply_enc_compose fp a b v :
  enc_normal a = true -> enc_normal b = true ->
  apply_enc (enc_compose fp a b) v
  = match apply_enc b v with
    | inl w => apply_enc a w
    | inr p => inr (fp p)
    end.
Proof.
  unfold enc_normal; rewrite !andb_true_iff; intros [_ Na] [_ Nb].
  unfold enc_compose; rewrite apply_enc_spec, decode_encode, apply_compose by assumption.
  rewrite apply_enc_spec; destruct (apply (decode b) v); [|reflexivity].
  rewrite apply_enc_spec; reflexivity.
Qed.

Theorem enc_normal_compose fp a b :
  enc_normal a = true -> enc_normal b = true -> enc_normal (enc_compose fp a b) = true.
Proof.
  unfold enc_normal at 1 2; rewrite !andb_true_iff; intros [_ Na] [_ Nb].
  apply enc_normal_encode, normal_compose; assumption.
Qed.

(** ** Adding an output slot: O(log n), no reference changes *)

Definition push_outer_enc h a : eraw P :=
  update (label_key h)
    (fun o => Some (match o with
                    | Some e => mk_eentry h (ee_targets e) (S (ee_out e))
                    | None => mk_eentry h [] 1
                    end)) a.

Lemma out_count_push_outer h a h' :
  out_count (push_outer_enc h a) h'
  = if label_eqb h' h then S (out_count a h) else out_count a h'.
Proof.
  unfold out_count, push_outer_enc; rewrite get_update, label_key_eqb.
  destruct (label_eqb_spec h' h) as [->|]; [|reflexivity].
  destruct (get (label_key h) a); reflexivity.
Qed.

Lemma efind_push_outer h a h' :
  efind (push_outer_enc h a) h'
  = if label_eqb h' h then (fst (efind a h), S (snd (efind a h))) else efind a h'.
Proof.
  unfold efind, push_outer_enc; rewrite get_update, label_key_eqb.
  destruct (label_eqb_spec h' h) as [->|]; [|reflexivity].
  destruct (get (label_key h) a); reflexivity.
Qed.

Definition shift_t h (t : target P) : target P :=
  match t with
  | Rename w => Rename (shift_var (mk_var h 0) w)
  | Bind p => Bind p
  end.

Lemma dec_push_outer h a et :
  wf_target (out_count a) et = true ->
  dec (out_count (push_outer_enc h a)) et = shift_t h (dec (out_count a) et).
Proof.
  destruct et as [h' l|h' m|p]; cbn [wf_target dec shift_t]; intro Hwf; [| |reflexivity];
    rewrite out_count_push_outer; unfold shift_var; cbn [v_label v_index];
    rewrite (label_eqb_sym h h').
  - apply Nat.ltb_lt in Hwf.
    destruct (label_eqb_spec h' h) as [->|]; cbn [andb Nat.leb]; [|reflexivity].
    do 2 f_equal; lia.
  - destruct (label_eqb_spec h' h) as [->|]; cbn [andb Nat.leb]; [|reflexivity].
    do 2 f_equal; lia.
Qed.

Lemma wf_targets_efind a h et :
  enc_wf a = true -> In et (fst (efind a h)) -> wf_target (out_count a) et = true.
Proof.
  unfold enc_wf, efind; rewrite forallb_spec; intros Ha Hin.
  destruct (get (label_key h) a) as [e|] eqn:E; [|destruct Hin].
  specialize (Ha _ _ E); rewrite List.forallb_forall in Ha; apply Ha, Hin.
Qed.

Theorem apply_enc_push_outer h a v :
  enc_wf a = true ->
  apply_enc (push_outer_enc h a) v
  = match apply_enc a v with
    | inl w => inl (shift_var (mk_var h 0) w)
    | inr p => inr p
    end.
Proof.
  intros Ha; unfold apply_enc.
  rewrite efind_push_outer.
  destruct v as [h' i]; cbn [v_label v_index].
  destruct (label_eqb_spec h' h) as [->|Hne]; cbn [fst snd].
  - destruct (nth_error (fst (efind a h)) i) as [et|] eqn:E.
    + rewrite dec_push_outer by (apply (wf_targets_efind a h), (nth_error_In _ _ E); exact Ha).
      destruct (dec _ et); reflexivity.
    + unfold shift_var; cbn [v_label v_index]; rewrite label_eqb_refl; cbn [andb Nat.leb].
      do 2 f_equal; apply nth_error_None in E; lia.
  - destruct (nth_error (fst (efind a h')) i) as [et|] eqn:E.
    + rewrite dec_push_outer by (apply (wf_targets_efind a h'), (nth_error_In _ _ E); exact Ha).
      destruct (dec _ et); reflexivity.
    + unfold shift_var; cbn [v_label v_index].
      rewrite (proj2 (label_eqb_neq h h')) by congruence; reflexivity.
Qed.

Lemma minimal_map_shift h h1 ts k k' :
  (h1 = h -> k' = S k) -> (h1 <> h -> k' = k) ->
  minimal h1 (map (shift_t h) ts) k' = minimal h1 ts k.
Proof.
  intros Heq Hne; unfold minimal, last_target; rewrite length_map, nth_error_map.
  destruct (nth_error ts _) as [[[l i]|p]|]; cbn [option_map shift_t]; [|reflexivity..].
  f_equal; unfold transparent, shift_var; cbn [v_label v_index].
  destruct (label_eqb_spec h1 h) as [->|Hh];
    [rewrite (Heq eq_refl)|rewrite (Hne Hh)]; case_vars.
Qed.

Lemma wf_target_mono cnt1 cnt2 et :
  (forall h, cnt1 h <= cnt2 h) -> wf_target cnt1 et = true -> wf_target cnt2 et = true.
Proof.
  intro H; destruct et as [h l| |]; cbn [wf_target]; rewrite ?Nat.ltb_lt; [|auto..].
  specialize (H h); lia.
Qed.

Lemma out_count_push_outer_ge h a h' : out_count a h' <= out_count (push_outer_enc h a) h'.
Proof. rewrite out_count_push_outer; destruct (label_eqb_spec h' h) as [->|]; lia. Qed.

Lemma trivial_map (f : target P -> target P) (ts : list (target P)) k :
  trivial (map f ts) k = trivial ts k.
Proof. destruct ts, k; reflexivity. Qed.

Theorem enc_normal_push_outer h a :
  enc_normal a = true -> enc_normal (push_outer_enc h a) = true.
Proof.
  unfold enc_normal; rewrite !andb_true_iff; intros [Wa Na]; split.
  - unfold enc_wf in *; rewrite forallb_spec in *; intros key e He.
    unfold push_outer_enc in He; rewrite get_update in He.
    apply List.forallb_forall; intros et Hin.
    apply (wf_target_mono (out_count a)); [apply out_count_push_outer_ge|].
    destruct (Pos.eqb_spec key (label_key h)) as [->|].
    + injection He as <-.
      destruct (get (label_key h) a) as [e0|] eqn:E0; cbn [ee_targets] in Hin; [|destruct Hin].
      specialize (Wa _ _ E0); rewrite List.forallb_forall in Wa; apply Wa, Hin.
    + specialize (Wa _ _ He); rewrite List.forallb_forall in Wa; apply Wa, Hin.
  - unfold normal; apply forallb_spec; intros key e' He'.
    rewrite get_decode in He'.
    destruct (get key (push_outer_enc h a)) as [e|] eqn:He; [|discriminate].
    injection He' as <-.
    assert (Hdec : forall et, wf_target (out_count a) et = true ->
              dec (out_count (push_outer_enc h a)) et = shift_t h (dec (out_count a) et))
      by (intros; apply dec_push_outer; assumption).
    unfold push_outer_enc in He; rewrite get_update in He.
    destruct (Pos.eqb_spec key (label_key h)) as [->|Hkey].
    + injection He as <-.
      pose proof (find_minimal (decode a) h Na) as Hmin; rewrite find_decode in Hmin.
      unfold efind in Hmin.
      destruct (get (label_key h) a) as [e0|] eqn:E0; cbn [fst snd] in Hmin |- *;
        unfold decode_entry; cbn [ee_label ee_targets ee_out];
        rewrite entry_ok_mk_entry; cbn [trivial negb]; [|reflexivity].
      rewrite (map_ext_in _ (fun et => shift_t h (dec (out_count a) et))).
      * rewrite <- map_map, (minimal_map_shift h h _ (ee_out e0)), Hmin;
          [destruct (ee_targets e0), (ee_out e0); reflexivity|reflexivity|congruence].
      * intros et Hin; apply Hdec.
        unfold enc_wf in Wa; rewrite forallb_spec in Wa; specialize (Wa _ _ E0).
        rewrite List.forallb_forall in Wa; apply Wa, Hin.
    + pose proof (normal_get _ _ _ Na (eq_trans (get_decode a key) (f_equal _ He))) as Hok.
      cbn [option_map] in Hok.
      unfold entry_ok, decode_entry in *; cbn [e_label e_targets e_out ee_label ee_targets ee_out] in *.
      rewrite !andb_true_iff in *; destruct Hok as [[Hk Hm] Ht].
      assert (Hl : ee_label e <> h)
        by (intro Hl; apply Hkey; apply Pos.eqb_eq in Hk; rewrite Hk, Hl; reflexivity).
      rewrite (map_ext_in _ (fun et => shift_t h (dec (out_count a) et))).
      * rewrite <- map_map, (minimal_map_shift h (ee_label e) _ (ee_out e)) by (congruence || auto).
        rewrite trivial_map; auto.
      * intros et Hin; apply Hdec.
        unfold enc_wf in Wa; rewrite forallb_spec in Wa; specialize (Wa _ _ He).
        rewrite List.forallb_forall in Wa; apply Wa, Hin.
Qed.

End Encoded.
