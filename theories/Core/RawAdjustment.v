(** * Raw adjustments

    An adjustment maps the variables of an inner scope to variables of an
    outer scope, or to payloads (substitution).  The representation is
    grouped per label: for each label [h] there is an entry with

    - a list [ts] of targets for the first [length ts] indices [h₍₀₎, h₍₁₎, …];
    - a count [k] of fresh outer slots for [h].

    Every other variable [h₍ᵢ₎] with [i ≥ length ts] maps "passively" to
    [h₍ᵢ₋ₗₑₙ₉ₜₕ ₜₛ₊ₖ₎].  Labels with no entry map to themselves.

    Entries are stored in a canonical trie keyed by [label_key].  An
    adjustment is [normal] when every entry is stored at its own label's key,
    is non-trivial, and does not end in a "transparent" target (one that
    does exactly what the passive shift would do).  The main results are:

    - [apply_compose]: composition is correct;
    - [normal_compose]: composition preserves normality;
    - [canonical]: normal adjustments with the same action are equal. *)

From Stdlib Require Import PArith Arith List Lia Bool.
From ShiftedNames.Core Require Import Trie Label Var.
Import ListNotations.

Inductive target (P : Type) : Type :=
| Rename : var -> target P
| Bind : P -> target P.

Arguments Rename {P} _.
Arguments Bind {P} _.

Record entry (P : Type) : Type :=
  mk_entry { e_label : option label; e_targets : list (target P); e_out : nat }.

Arguments mk_entry {P} _ _ _.
Arguments e_label {P} _.
Arguments e_targets {P} _.
Arguments e_out {P} _.

Definition raw (P : Type) : Type := tree (entry P).

Section Raw.

Context {P : Type}.

Implicit Types (a b : raw P) (h : option label) (ts : list (target P))
  (t : target P) (v w : var).

(** ** Semantics *)

Definition target_result t : var + P :=
  match t with
  | Rename v => inl v
  | Bind p => inr p
  end.

Definition apply_entry h ts (k i : nat) : var + P :=
  match nth_error ts i with
  | Some t => target_result t
  | None => inl (mk_var h (i - length ts + k))
  end.

Definition find a h : list (target P) * nat :=
  match get (label_key h) a with
  | Some e => (e_targets e, e_out e)
  | None => ([], 0)
  end.

Definition apply a v : var + P :=
  apply_entry (v_label v) (fst (find a (v_label v))) (snd (find a (v_label v)))
    (v_index v).

Definition identity : raw P := Empty.

(** ** Normal forms *)

Definition transparent h (k : nat) t : bool :=
  match t with
  | Rename v => label_eqb (v_label v) h && Nat.eqb (S (v_index v)) k
  | Bind _ => false
  end.

Definition last_target ts : option (target P) :=
  nth_error ts (pred (length ts)).

Definition minimal h ts (k : nat) : bool :=
  match last_target ts with
  | Some t => negb (transparent h k t)
  | None => true
  end.

Definition trivial ts (k : nat) : bool :=
  match ts, k with
  | [], 0 => true
  | _, _ => false
  end.

Definition entry_ok (key : positive) (e : entry P) : bool :=
  Pos.eqb key (label_key (e_label e))
  && minimal (e_label e) (e_targets e) (e_out e)
  && negb (trivial (e_targets e) (e_out e)).

Definition normal a : bool := forallb entry_ok a.

(** Stripping trailing transparent targets.  [strip_rev] works on the
    reversed list of targets, so the last target is at the head. *)

Fixpoint strip_rev h (rts : list (target P)) (k : nat)
  : list (target P) * nat :=
  match rts with
  | t :: rts' => if transparent h k t then strip_rev h rts' (pred k) else (rts, k)
  | [] => ([], k)
  end.

Definition strip h ts (k : nat) : list (target P) * nat :=
  let r := strip_rev h (rev ts) k in (rev (fst r), snd r).
Arguments strip : simpl never.

Definition make_entry h ts (k : nat) : option (entry P) :=
  let r := strip h ts k in
  if trivial (fst r) (snd r) then None else Some (mk_entry h (fst r) (snd r)).

Definition normalize a : raw P :=
  map_filter (fun _ e => make_entry (e_label e) (e_targets e) (e_out e)) a.

(** ** Composition

    [compose fp a b] first applies [b] and then [a].  Payloads produced by
    [b] live in [a]'s inner scope, and [fp] says how to move them to the
    outer scope (for substitutions this is substitution by [a]; for
    renamings there are no payloads). *)

Definition map_target (fp : P -> P) a t : target P :=
  match t with
  | Rename v =>
      match apply a v with
      | inl w => Rename w
      | inr p => Bind p
      end
  | Bind p => Bind (fp p)
  end.

Definition compose_targets (fp : P -> P) a tsa (ka : nat) tsb (kb : nat)
  : list (target P) * nat :=
  (map (map_target fp a) tsb ++ skipn kb tsa, ka + (kb - length tsa)).

Definition entry_parts (e : option (entry P)) : list (target P) * nat :=
  match e with
  | Some e => (e_targets e, e_out e)
  | None => ([], 0)
  end.

Definition opt_label (ea eb : option (entry P)) : option label :=
  match ea, eb with
  | Some e, _ => e_label e
  | None, Some e => e_label e
  | None, None => None
  end.

Definition compose_entry (fp : P -> P) a (ea eb : option (entry P))
  : option (entry P) :=
  match ea, eb with
  | None, None => None
  | _, _ =>
      let r := compose_targets fp a
                 (fst (entry_parts ea)) (snd (entry_parts ea))
                 (fst (entry_parts eb)) (snd (entry_parts eb)) in
      make_entry (opt_label ea eb) (fst r) (snd r)
  end.

Definition compose (fp : P -> P) a b : raw P :=
  merge (fun _ ea eb => compose_entry fp a ea eb) a b.

(** ** Basic facts *)

Lemma find_identity h : find identity h = ([], 0).
Proof. reflexivity. Qed.

Lemma apply_identity v : apply identity v = inl v.
Proof.
  unfold apply, apply_entry; cbn [find get fst snd length].
  rewrite nth_error_nil, Nat.sub_0_r, Nat.add_0_r; reflexivity.
Qed.

Lemma entry_ok_key key e : entry_ok key e = true -> key = label_key (e_label e).
Proof.
  unfold entry_ok; rewrite !andb_true_iff; intros [[H _] _].
  apply Pos.eqb_eq, H.
Qed.

Lemma normal_get a key e :
  normal a = true -> get key a = Some e -> entry_ok key e = true.
Proof. unfold normal; rewrite forallb_spec; auto. Qed.

Lemma normal_label a h e :
  normal a = true -> get (label_key h) a = Some e -> e_label e = h.
Proof.
  intros Ha He.
  apply label_key_inj; symmetry.
  apply (entry_ok_key _ _ (normal_get a _ e Ha He)).
Qed.

(** ** Stripping preserves the action of an entry *)

Lemma transparent_spec h k t :
  transparent h k t = true ->
  exists i, t = Rename (mk_var h i) /\ k = S i.
Proof.
  destruct t as [v|p]; cbn [transparent]; [|discriminate].
  rewrite andb_true_iff, label_eqb_eq.
  intros [Hl Hk]; apply Nat.eqb_eq in Hk; exists (v_index v); split; [|symmetry; exact Hk].
  rewrite (var_eta v), Hl; reflexivity.
Qed.

Lemma apply_entry_snoc_transparent h ts k t i :
  transparent h k t = true ->
  apply_entry h (ts ++ [t]) k i = apply_entry h ts (pred k) i.
Proof.
  intros Ht; apply transparent_spec in Ht as [j [-> ->]].
  unfold apply_entry; cbn [pred].
  rewrite length_app; cbn [length].
  destruct (Nat.lt_ge_cases i (length ts)) as [Hi|Hi].
  - rewrite (nth_error_app1 _ _ Hi).
    destruct (nth_error ts i) eqn:E; [reflexivity|].
    apply nth_error_None in E; lia.
  - rewrite (nth_error_app2 _ _ Hi).
    rewrite (proj2 (nth_error_None ts i)) by exact Hi.
    destruct (i - length ts) as [|n] eqn:E; cbn.
    + f_equal; f_equal; lia.
    + rewrite nth_error_nil; f_equal; f_equal; lia.
Qed.

Lemma apply_entry_strip_rev h rts k i :
  apply_entry h (rev (fst (strip_rev h rts k))) (snd (strip_rev h rts k)) i
  = apply_entry h (rev rts) k i.
Proof.
  revert k; induction rts as [|t rts IH]; intro k; cbn [strip_rev]; [reflexivity|].
  destruct (transparent h k t) eqn:Ht; [|reflexivity].
  rewrite IH; cbn [rev].
  symmetry; apply apply_entry_snoc_transparent, Ht.
Qed.

Lemma apply_entry_strip h ts k i :
  apply_entry h (fst (strip h ts k)) (snd (strip h ts k)) i
  = apply_entry h ts k i.
Proof.
  unfold strip; cbn [fst snd].
  rewrite apply_entry_strip_rev, rev_involutive; reflexivity.
Qed.

Lemma last_target_rev_cons t rts : last_target (rev (t :: rts)) = Some t.
Proof.
  unfold last_target; cbn [rev].
  rewrite length_app, length_rev; cbn [length].
  rewrite Nat.add_1_r; cbn [pred].
  rewrite nth_error_app2 by (rewrite length_rev; lia).
  rewrite length_rev, Nat.sub_diag; reflexivity.
Qed.

Lemma minimal_strip h ts k :
  minimal h (fst (strip h ts k)) (snd (strip h ts k)) = true.
Proof.
  unfold strip; cbn [fst snd].
  generalize (rev ts) as rts; intro rts; revert k.
  induction rts as [|t rts IH]; intro k; cbn [strip_rev]; [reflexivity|].
  destruct (transparent h k t) eqn:Ht; [apply IH|].
  unfold minimal; cbn [fst snd].
  rewrite last_target_rev_cons, Ht; reflexivity.
Qed.

Lemma make_entry_parts h ts k :
  entry_parts (make_entry h ts k) = strip h ts k.
Proof.
  unfold make_entry.
  destruct (strip h ts k) as [ts' k'] eqn:E; cbn [fst snd].
  destruct ts' as [|t ts'], k' as [|k']; reflexivity.
Qed.

Lemma make_entry_label h ts k e :
  make_entry h ts k = Some e -> e_label e = h.
Proof.
  unfold make_entry; destruct (trivial _ _); [discriminate|].
  intros [= <-]; reflexivity.
Qed.

Lemma entry_ok_mk_entry h ts k :
  entry_ok (label_key h) (mk_entry h ts k) = minimal h ts k && negb (trivial ts k).
Proof. unfold entry_ok; cbn [e_label e_targets e_out]; rewrite Pos.eqb_refl; reflexivity. Qed.

Lemma make_entry_ok h ts k e :
  make_entry h ts k = Some e -> entry_ok (label_key h) e = true.
Proof.
  pose proof (minimal_strip h ts k) as Hm.
  unfold make_entry; cbv zeta.
  destruct (strip h ts k) as [ts' k']; cbn [fst snd] in *.
  destruct (trivial ts' k') eqn:Htriv; [discriminate|].
  intros [= <-]; rewrite entry_ok_mk_entry, Htriv, Hm; reflexivity.
Qed.

(** ** Composition is correct *)

Lemma find_label a h e :
  normal a = true -> get (label_key h) a = Some e ->
  find a h = (e_targets e, e_out e).
Proof. intros _ He; unfold find; rewrite He; reflexivity. Qed.

Lemma apply_entry_compose_targets fp a h tsa ka tsb kb i :
  find a h = (tsa, ka) ->
  apply_entry h (fst (compose_targets fp a tsa ka tsb kb))
    (snd (compose_targets fp a tsa ka tsb kb)) i
  = match apply_entry h tsb kb i with
    | inl w => apply a w
    | inr p => inr (fp p)
    end.
Proof.
  intros Hfind; unfold compose_targets, apply_entry; cbn [fst snd].
  rewrite length_app, length_map, length_skipn.
  destruct (Nat.lt_ge_cases i (length tsb)) as [Hi|Hi].
  - rewrite nth_error_app1 by (rewrite length_map; exact Hi).
    rewrite nth_error_map.
    destruct (nth_error tsb i) as [t|] eqn:E.
    + cbn; destruct t as [v|p]; cbn; [|reflexivity].
      destruct (apply a v); reflexivity.
    + apply nth_error_None in E; lia.
  - rewrite nth_error_app2 by (rewrite length_map; exact Hi).
    rewrite length_map, nth_error_skipn.
    rewrite (proj2 (nth_error_None tsb i) Hi).
    unfold apply; cbn [v_label v_index]; rewrite Hfind; cbn [fst snd].
    unfold apply_entry.
    replace (kb + (i - length tsb)) with (i - length tsb + kb) by lia.
    destruct (nth_error tsa (i - length tsb + kb)) eqn:E; [reflexivity|].
    apply nth_error_None in E.
    f_equal; f_equal; lia.
Qed.

Lemma find_compose fp a b h :
  normal a = true -> normal b = true ->
  find (compose fp a b) h
  = strip h (fst (compose_targets fp a (fst (find a h)) (snd (find a h))
                    (fst (find b h)) (snd (find b h))))
            (snd (compose_targets fp a (fst (find a h)) (snd (find a h))
                    (fst (find b h)) (snd (find b h)))).
Proof.
  intros Ha Hb.
  unfold find at 1; unfold compose.
  rewrite get_merge by reflexivity.
  unfold find.
  destruct (get (label_key h) a) as [ea|] eqn:Ea,
           (get (label_key h) b) as [eb|] eqn:Eb.
  all: try reflexivity.
  all: unfold compose_entry; rewrite <- make_entry_parts.
  all: cbn [opt_label entry_parts fst snd].
  all: rewrite ?(normal_label a h ea Ha Ea), ?(normal_label b h eb Hb Eb).
  all: reflexivity.
Qed.

Theorem apply_compose fp a b v :
  normal a = true -> normal b = true ->
  apply (compose fp a b) v
  = match apply b v with
    | inl w => apply a w
    | inr p => inr (fp p)
    end.
Proof.
  intros Ha Hb.
  unfold apply at 1 2.
  rewrite (find_compose fp a b (v_label v) Ha Hb).
  rewrite apply_entry_strip.
  apply apply_entry_compose_targets.
  destruct (find a (v_label v)); reflexivity.
Qed.

Theorem normal_compose fp a b :
  normal a = true -> normal b = true -> normal (compose fp a b) = true.
Proof.
  intros Ha Hb.
  unfold normal; apply forallb_spec; intros key e He.
  unfold compose in He; rewrite get_merge in He by reflexivity.
  unfold compose_entry in He.
  destruct (get key a) as [ea|] eqn:Ea, (get key b) as [eb|] eqn:Eb;
    try discriminate.
  all: cbn [opt_label] in He.
  all: pose proof (make_entry_ok _ _ _ _ He) as Hok.
  all: first [ rewrite <- (entry_ok_key _ _ (normal_get a key ea Ha Ea)) in Hok
             | rewrite <- (entry_ok_key _ _ (normal_get b key eb Hb Eb)) in Hok ].
  all: exact Hok.
Qed.

(** ** Normalisation *)

Definition keys_ok a : bool :=
  forallb (fun key e => Pos.eqb key (label_key (e_label e))) a.

Lemma normal_keys_ok a : normal a = true -> keys_ok a = true.
Proof.
  unfold normal, keys_ok; rewrite !forallb_spec.
  intros H key e He; specialize (H key e He).
  unfold entry_ok in H; rewrite !andb_true_iff in H; tauto.
Qed.

Lemma keys_ok_label a h e :
  keys_ok a = true -> get (label_key h) a = Some e -> e_label e = h.
Proof.
  unfold keys_ok; rewrite forallb_spec; intros H He.
  apply label_key_inj; symmetry; apply Pos.eqb_eq, (H _ _ He).
Qed.

Lemma find_normalize a h :
  keys_ok a = true -> find (normalize a) h = strip h (fst (find a h)) (snd (find a h)).
Proof.
  intros Ha; unfold find, normalize.
  rewrite get_map_filter.
  destruct (get (label_key h) a) as [e|] eqn:E; [|reflexivity].
  rewrite <- make_entry_parts, (keys_ok_label a h e Ha E).
  reflexivity.
Qed.

Theorem apply_normalize a v :
  keys_ok a = true -> apply (normalize a) v = apply a v.
Proof.
  intros Ha; unfold apply.
  rewrite find_normalize by exact Ha.
  apply apply_entry_strip.
Qed.

Theorem normal_normalize a : keys_ok a = true -> normal (normalize a) = true.
Proof.
  intros Ha; unfold normal; apply forallb_spec; intros key e He.
  unfold normalize in He; rewrite get_map_filter in He.
  destruct (get key a) as [e0|] eqn:E0; [|discriminate].
  pose proof (make_entry_ok _ _ _ _ He) as Hok.
  unfold keys_ok in Ha; rewrite forallb_spec in Ha.
  pose proof (Ha _ _ E0) as Hk; apply Pos.eqb_eq in Hk; rewrite <- Hk in Hok.
  exact Hok.
Qed.

(** ** Canonicity *)

Lemma target_result_inj t1 t2 : target_result t1 = target_result t2 -> t1 = t2.
Proof. destruct t1, t2; cbn; congruence. Qed.

Lemma last_target_nth ts :
  ts <> [] -> last_target ts = nth_error ts (length ts - 1).
Proof. intros _; unfold last_target; rewrite Nat.sub_1_r; reflexivity. Qed.

(** If an entry is longer than another with the same action, its last
    target is transparent. *)
Lemma longer_not_minimal h ts1 k1 ts2 k2 :
  (forall i, apply_entry h ts1 k1 i = apply_entry h ts2 k2 i) ->
  length ts2 + k1 = length ts1 + k2 ->
  length ts1 < length ts2 ->
  minimal h ts2 k2 = false.
Proof.
  intros Heq Hoff Hlt.
  specialize (Heq (length ts2 - 1)).
  unfold apply_entry in Heq.
  rewrite (proj2 (nth_error_None ts1 _)) in Heq by lia.
  unfold minimal; rewrite last_target_nth by (intros ->; cbn in Hlt; lia).
  destruct (nth_error ts2 (length ts2 - 1)) as [t|] eqn:E.
  - destruct t as [v|p]; cbn in Heq; [|discriminate].
    injection Heq as Hv; subst v.
    cbn [transparent v_label v_index].
    rewrite label_eqb_refl.
    replace (S (length ts2 - 1 - length ts1 + k1)) with k2 by lia.
    rewrite Nat.eqb_refl; reflexivity.
  - apply nth_error_None in E; lia.
Qed.

Theorem entry_canonical h ts1 k1 ts2 k2 :
  minimal h ts1 k1 = true -> minimal h ts2 k2 = true ->
  (forall i, apply_entry h ts1 k1 i = apply_entry h ts2 k2 i) ->
  ts1 = ts2 /\ k1 = k2.
Proof.
  intros Hm1 Hm2 Heq.
  assert (Hoff : length ts2 + k1 = length ts1 + k2).
  { specialize (Heq (length ts1 + length ts2)).
    unfold apply_entry in Heq.
    rewrite !(proj2 (nth_error_None _ _)) in Heq by lia.
    injection Heq; lia. }
  assert (Hlen : length ts1 = length ts2).
  { destruct (Nat.lt_trichotomy (length ts1) (length ts2)) as [H|[H|H]].
    - rewrite (longer_not_minimal h ts1 k1 ts2 k2 Heq Hoff H) in Hm2.
      discriminate.
    - exact H.
    - assert (Heq' : forall i, apply_entry h ts2 k2 i = apply_entry h ts1 k1 i)
        by (intro; symmetry; apply Heq).
      rewrite (longer_not_minimal h ts2 k2 ts1 k1 Heq' ltac:(lia) H) in Hm1.
      discriminate. }
  split; [|lia].
  apply nth_error_ext; intro i.
  destruct (Nat.lt_ge_cases i (length ts1)) as [Hi|Hi].
  - specialize (Heq i); unfold apply_entry in Heq.
    destruct (nth_error ts1 i) eqn:E1, (nth_error ts2 i) eqn:E2.
    + f_equal; apply target_result_inj, Heq.
    + apply nth_error_None in E2; lia.
    + apply nth_error_None in E1; lia.
    + reflexivity.
  - rewrite !(proj2 (nth_error_None _ _)) by lia; reflexivity.
Qed.

Lemma find_minimal a h :
  normal a = true -> minimal h (fst (find a h)) (snd (find a h)) = true.
Proof.
  intros Ha; unfold find.
  destruct (get (label_key h) a) as [e|] eqn:E; [|reflexivity].
  pose proof (normal_get a _ e Ha E) as Hok.
  rewrite <- (normal_label a h e Ha E).
  unfold entry_ok in Hok; rewrite !andb_true_iff in Hok; tauto.
Qed.

Lemma find_nontrivial a h e :
  normal a = true -> get (label_key h) a = Some e ->
  trivial (e_targets e) (e_out e) = false.
Proof.
  intros Ha He; pose proof (normal_get a _ e Ha He) as Hok.
  unfold entry_ok in Hok; rewrite !andb_true_iff, negb_true_iff in Hok.
  tauto.
Qed.

Theorem canonical a b :
  normal a = true -> normal b = true ->
  (forall v, apply a v = apply b v) -> a = b.
Proof.
  intros Ha Hb Heq.
  apply extensionality; intro key.
  (* Each side either has no entry, or one stored at its own label's key. *)
  assert (Hfind : forall h, find a h = find b h).
  { intro h.
    destruct (entry_canonical h (fst (find a h)) (snd (find a h))
                (fst (find b h)) (snd (find b h)))
      as [Ht Hk].
    - apply find_minimal, Ha.
    - apply find_minimal, Hb.
    - intro i; exact (Heq (mk_var h i)).
    - destruct (find a h), (find b h); cbn in *; congruence. }
  destruct (get key a) as [ea|] eqn:Ea, (get key b) as [eb|] eqn:Eb.
  - pose proof (entry_ok_key _ _ (normal_get a _ _ Ha Ea)) as Ka.
    pose proof (entry_ok_key _ _ (normal_get b _ _ Hb Eb)) as Kb.
    specialize (Hfind (e_label ea)); unfold find in Hfind.
    rewrite <- Ka, Ea, Eb in Hfind.
    destruct ea as [la tsa ka], eb as [lb tsb kb]; cbn in *.
    injection Hfind as -> ->.
    rewrite Ka in Kb; apply label_key_inj in Kb; subst; reflexivity.
  - pose proof (entry_ok_key _ _ (normal_get a _ _ Ha Ea)) as Ka.
    specialize (Hfind (e_label ea)); unfold find in Hfind.
    rewrite <- Ka, Ea, Eb in Hfind.
    pose proof (find_nontrivial a (e_label ea) ea Ha ltac:(rewrite <- Ka; exact Ea)).
    injection Hfind as Ht Hk; rewrite Ht, Hk in H; discriminate.
  - pose proof (entry_ok_key _ _ (normal_get b _ _ Hb Eb)) as Kb.
    specialize (Hfind (e_label eb)); unfold find in Hfind.
    rewrite <- Kb, Ea, Eb in Hfind.
    pose proof (find_nontrivial b (e_label eb) eb Hb ltac:(rewrite <- Kb; exact Eb)).
    injection Hfind as Ht Hk; rewrite <- Ht, <- Hk in H; discriminate.
  - reflexivity.
Qed.

(** ** Adding an input entry in front

    [push_inner h t r] makes the innermost [h₍₀₎] go to [t], and every other
    variable go through [r] (with the remaining [h]s moved down by one).  It
    only touches the entry for [h]. *)

Definition push_inner_raw h t a : raw P :=
  update (label_key h)
    (fun _ => make_entry h (t :: fst (find a h)) (snd (find a h))) a.

Lemma find_push_inner_raw h t a h' :
  find (push_inner_raw h t a) h'
  = if label_eqb h' h then strip h (t :: fst (find a h)) (snd (find a h))
    else find a h'.
Proof.
  unfold find at 1, push_inner_raw.
  rewrite get_update, label_key_eqb.
  destruct (label_eqb_spec h' h) as [->|]; [|reflexivity].
  rewrite <- make_entry_parts; unfold entry_parts.
  destruct (make_entry _ _ _); reflexivity.
Qed.

Theorem normal_push_inner_raw h t a :
  normal a = true -> normal (push_inner_raw h t a) = true.
Proof.
  intros Ha; unfold normal; apply forallb_spec; intros key e He.
  unfold push_inner_raw in He; rewrite get_update in He.
  destruct (Pos.eqb_spec key (label_key h)) as [->|].
  - apply (make_entry_ok _ _ _ _ He).
  - apply (normal_get a key e Ha He).
Qed.

Theorem apply_push_inner_raw h t a v :
  apply (push_inner_raw h t a) v
  = if var_eqb v (mk_var h 0) then target_result t
    else apply a (unshift_var (mk_var h 0) v).
Proof.
  destruct v as [h' i]; unfold apply at 1; cbn [v_label v_index].
  rewrite find_push_inner_raw.
  unfold var_eqb, unshift_var; cbn [v_label v_index].
  destruct (label_eqb_spec h' h) as [->|Hne].
  - rewrite apply_entry_strip, label_eqb_refl; cbn [andb].
    destruct i as [|i]; cbn [Nat.eqb Nat.ltb Nat.leb]; [reflexivity|].
    unfold apply; cbn [v_label v_index].
    replace (S i - 1) with i by lia.
    unfold apply_entry; cbn [nth_error length].
    destruct (nth_error (fst (find a h)) i); [reflexivity|].
    f_equal; f_equal; lia.
  - rewrite (proj2 (label_eqb_neq h h')) by congruence; cbn [andb].
    reflexivity.
Qed.

End Raw.
