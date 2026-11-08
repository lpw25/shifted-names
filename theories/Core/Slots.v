(** * Adjustments with slot references (the final core, design D9)

    For each label [h] an entry holds:
    - [e_targets]: where the inner [h₍₀₎, h₍₁₎, …] go (head = innermost, so
      adding an input entry is a cons);
    - [e_out]: the number of output slots for [h].

    A target is [Slot h' l], the [l]-th output slot for [h'] counted from
    the innermost constructor (it denotes [h'₍ₖ₋₁₋ₗ₎] when [h'] has [k]
    slots), or a payload [Bind p].  Explicit targets only ever land in
    slots: a contraction with a passed-through variable is written by giving
    that variable an explicit entry too.  Inner [h₍ᵢ₎] with
    [i ≥ |e_targets|] pass through to [h₍ᵢ₋|e_targets|+e_out₎].

    Because references count from the innermost constructor, adding an
    output slot ([push_outer]) changes no reference.

    This file treats payloads as opaque; nested payload adjustments are
    added on top later. *)

From Stdlib Require Import PArith Arith List Lia Bool.
From ShiftedNames.Core Require Import Trie Label Var.
From ShiftedNames.Core Require Braun.
From ShiftedNames.Core Require Import Braun(braun, BE, BN).
Import ListNotations.

Inductive target (P : Type) : Type :=
| Slot : option label -> nat -> target P
| Bind : P -> target P.

Arguments Slot {P} _ _.
Arguments Bind {P} _.

(** Back-links of one output slot: for each label (by key) whose inputs
    refer to the slot, the positions of those inputs, counted from the back
    of the label's targets (see "Back-links" below). *)
Definition links : Type := tree (tree unit).

Record entry (P : Type) : Type :=
  mk_entry { e_label : option label; e_tree : braun (target P); e_out : nat;
             e_back : braun links }.

Arguments mk_entry {P} _ _ _ _.
Arguments e_label {P} _.
Arguments e_tree {P} _.
Arguments e_out {P} _.
Arguments e_back {P} _.

(** The targets of an entry, as the list they denote. *)
Definition e_targets {P} (e : entry P) : list (target P) := Braun.to_list (e_tree e).

Definition raw (P : Type) : Type := tree (entry P).

Section Slots.

Context {P : Type}.

Implicit Types (a b : raw P) (h l : option label) (v w : rvar) (t : target P)
  (ts : list (target P)).

(** ** Semantics *)

Definition find a h : list (target P) * nat :=
  match get (label_key h) a with
  | Some e => (e_targets e, e_out e)
  | None => ([], 0)
  end.

(** Reading an entry's parts directly (what computation uses). *)
Definition seq_of a h : braun (target P) :=
  match get (label_key h) a with Some e => e_tree e | None => BE end.

Definition count a h : nat :=
  match get (label_key h) a with Some e => e_out e | None => 0 end.

Definition backs_of a h : braun links :=
  match get (label_key h) a with Some e => e_back e | None => BE end.

Lemma count_find a h : count a h = snd (find a h).
Proof. unfold count, find; destruct (get (label_key h) a); reflexivity. Qed.

Lemma elems_seq_of a h : Braun.to_list (seq_of a h) = fst (find a h).
Proof. unfold seq_of, find; destruct (get (label_key h) a); reflexivity. Qed.

Definition resolve a t : rvar + P :=
  match t with
  | Slot h l => inl (mk_rvar h (count a h - S l))
  | Bind p => inr p
  end.

(** The meaning of an adjustment. *)
Definition apply a v : rvar + P :=
  match nth_error (fst (find a (v_label v))) (v_index v) with
  | Some t => resolve a t
  | None => inl (mk_rvar (v_label v)
                   (v_index v - length (fst (find a (v_label v))) + count a (v_label v)))
  end.

(** Computing it: one trie lookup and one sequence lookup. *)
Definition lookup a v : rvar + P :=
  let s := seq_of a (v_label v) in
  match Braun.nth (v_index v) s with
  | Some t => resolve a t
  | None => inl (mk_rvar (v_label v) (v_index v - Braun.size s + count a (v_label v)))
  end.

Lemma lookup_spec a v : Braun.balanced (seq_of a (v_label v)) -> lookup a v = apply a v.
Proof.
  intros Hb; unfold lookup, apply.
  rewrite Braun.nth_to_list, <- Braun.to_list_length, elems_seq_of by exact Hb; reflexivity.
Qed.

(** ** Normal forms *)

Definition is_slot h (n : nat) t : bool :=
  match t with
  | Slot h' n' => label_eqb h' h && Nat.eqb n' n
  | Bind _ => false
  end.

(** All slot references, with the input variable they belong to. *)
Definition refs_of_entry (e : entry P) : list (rvar * option label * nat) :=
  let fix go (ts : list (target P)) (i : nat) :=
    match ts with
    | [] => []
    | Slot h' n :: ts' => (mk_rvar (e_label e) i, h', n) :: go ts' (S i)
    | Bind _ :: ts' => go ts' (S i)
    end in
  go (e_targets e) 0.

Definition refs a : list (rvar * option label * nat) :=
  flat_map (fun ke => refs_of_entry (snd ke)) (elements a).

Definition slot_wf a (r : rvar * option label * nat) : bool :=
  match r with (_, h, n) => Nat.ltb n (count a h) end.

Definition last_target ts : option (target P) := nth_error ts (pred (length ts)).

(** The strip condition: if the last target of [h] is [h]'s innermost slot,
    some other input refers to that slot too. *)
Definition strip_ok a h ts : bool :=
  match last_target ts with
  | Some (Slot h' 0) =>
      if label_eqb h' h then
        existsb (fun r => match r with
                          | (v, h'', 0) =>
                              label_eqb h'' h
                              && negb (rvar_eqb v (mk_rvar h (pred (length ts))))
                          | _ => false
                          end) (refs a)
      else true
  | _ => true
  end.

Definition nontrivial ts (k : nat) : bool :=
  match ts, k with [], 0 => false | _, _ => true end.

Definition nontrivial_seq (s : braun (target P)) (k : nat) : bool :=
  negb (Nat.eqb (Braun.size s) 0) || negb (Nat.eqb k 0).

Lemma nontrivial_seq_elems s k : nontrivial_seq s k = nontrivial (Braun.to_list s) k.
Proof.
  unfold nontrivial_seq; rewrite <- Braun.to_list_length.
  destruct (Braun.to_list s), k; reflexivity.
Qed.

Definition entry_ok a (key : positive) (e : entry P) : bool :=
  (Pos.eqb key (label_key (e_label e)) && Braun.balancedb (e_tree e))
  && nontrivial (e_targets e) (e_out e)
  && strip_ok a (e_label e) (e_targets e).

Definition normal a : bool := forallb (entry_ok a) a && List.forallb (slot_wf a) (refs a).

(** Entries are stored at their label's key, and their sequences are
    balanced Braun trees. *)
Definition keys_ok a : bool :=
  forallb (fun key e => Pos.eqb key (label_key (e_label e)) && Braun.balancedb (e_tree e)) a.

Lemma keys_ok_spec a :
  keys_ok a = true
  <-> forall key e, get key a = Some e -> key = label_key (e_label e) /\ Braun.balanced (e_tree e).
Proof.
  unfold keys_ok; rewrite forallb_spec; split; intros H key e He; specialize (H key e He).
  - apply andb_true_iff in H as [H1 H2]; split; [apply Pos.eqb_eq, H1|apply Braun.balancedb_spec, H2].
  - destruct H as [H1 H2]; apply andb_true_iff; split;
      [apply Pos.eqb_eq, H1|apply Braun.balancedb_spec, H2].
Qed.

Lemma keys_ok_balanced a h : keys_ok a = true -> Braun.balanced (seq_of a h).
Proof.
  intros H; unfold seq_of; destruct (get (label_key h) a) as [e|] eqn:E; [|exact I].
  apply (proj2 (proj1 (keys_ok_spec a) H _ _ E)).
Qed.

(** ** Basic facts *)

(** Everything about an entry except its back-links. *)
Definition shape (e : entry P) : option label * braun (target P) * nat :=
  (e_label e, e_tree e, e_out e).

(** Two adjustments with the same entries up to back-links. *)
Definition same_shape a b : Prop :=
  forall key, option_map shape (get key a) = option_map shape (get key b).

Lemma normal_entries a : normal a = true -> forallb (entry_ok a) a = true.
Proof. unfold normal; rewrite andb_true_iff; tauto. Qed.

Lemma normal_refs a : normal a = true -> List.forallb (slot_wf a) (refs a) = true.
Proof. unfold normal; rewrite andb_true_iff; tauto. Qed.

Lemma normal_label a key e :
  normal a = true -> get key a = Some e -> key = label_key (e_label e).
Proof.
  intros Ha He; apply normal_entries in Ha; rewrite forallb_spec in Ha.
  specialize (Ha _ _ He); unfold entry_ok in Ha; rewrite !andb_true_iff in Ha.
  apply Pos.eqb_eq; tauto.
Qed.

Lemma normal_balanced a key e :
  normal a = true -> get key a = Some e -> Braun.balanced (e_tree e).
Proof.
  intros Ha He; apply normal_entries in Ha; rewrite forallb_spec in Ha.
  specialize (Ha _ _ He); unfold entry_ok in Ha; rewrite !andb_true_iff in Ha.
  apply Braun.balancedb_spec; tauto.
Qed.

Lemma find_label a h e :
  normal a = true -> get (label_key h) a = Some e -> e_label e = h.
Proof. intros Ha He; apply label_key_inj; symmetry; apply (normal_label a _ e Ha He). Qed.

Lemma go_refs (e : entry P) ts i v h' n :
  In (v, h', n)
    ((fix go (ts : list (target P)) (i : nat) :=
        match ts with
        | [] => []
        | Slot h' n :: ts' => (mk_rvar (e_label e) i, h', n) :: go ts' (S i)
        | Bind _ :: ts' => go ts' (S i)
        end) ts i)
  <-> v_label v = e_label e /\ i <= v_index v /\ nth_error ts (v_index v - i) = Some (Slot h' n).
Proof.
  revert i; induction ts as [|t ts IH]; intro i.
  - cbn; split; [intros []|intros [_ [_ H]]; rewrite nth_error_nil in H; discriminate].
  - destruct t as [h'' n'|p]; cbn [In]; rewrite IH.
    + split.
      * intros [[= <- <- <-]|[Hl [Hi Hn]]].
        -- cbn; rewrite Nat.sub_diag; repeat split; auto.
        -- repeat split; [exact Hl|lia|].
           replace (v_index v - i) with (S (v_index v - S i)) by lia; exact Hn.
      * intros [Hl [Hi Hn]].
        destruct (Nat.eq_dec (v_index v) i) as [Heq|Hne].
        -- left; rewrite Heq, Nat.sub_diag in Hn; cbn in Hn; injection Hn as -> ->.
           destruct v; cbn in *; subst; reflexivity.
        -- right; repeat split; [exact Hl|lia|].
           replace (v_index v - i) with (S (v_index v - S i)) in Hn by lia; exact Hn.
    + split.
      * intros [Hl [Hi Hn]]; repeat split; [exact Hl|lia|].
        replace (v_index v - i) with (S (v_index v - S i)) by lia; exact Hn.
      * intros [Hl [Hi Hn]].
        destruct (Nat.eq_dec (v_index v) i) as [Heq|Hne].
        -- rewrite Heq, Nat.sub_diag in Hn; discriminate.
        -- repeat split; [exact Hl|lia|].
           replace (v_index v - i) with (S (v_index v - S i)) in Hn by lia; exact Hn.
Qed.

Lemma In_refs a v h' n :
  normal a = true ->
  In (v, h', n) (refs a) <-> nth_error (fst (find a (v_label v))) (v_index v) = Some (Slot h' n).
Proof.
  intro Ha; unfold refs; rewrite in_flat_map; split.
  - intros [[key e] [Hin Hr]]; apply In_elements in Hin; cbn [snd] in Hr.
    unfold refs_of_entry in Hr; apply go_refs in Hr as [Hl [_ Hn]].
    rewrite Nat.sub_0_r in Hn.
    unfold find; rewrite Hl, <- (normal_label a key e Ha Hin), Hin; exact Hn.
  - intro Hn; unfold find in Hn.
    destruct (get (label_key (v_label v)) a) as [e|] eqn:E; [|rewrite nth_error_nil in Hn; discriminate].
    exists (label_key (v_label v), e); split; [apply In_elements, E|].
    cbn [snd]; unfold refs_of_entry; apply go_refs.
    rewrite Nat.sub_0_r; repeat split; [|lia|exact Hn].
    symmetry; apply (find_label a _ e Ha E).
Qed.

Lemma slot_bound a v h' n :
  normal a = true ->
  nth_error (fst (find a (v_label v))) (v_index v) = Some (Slot h' n) -> n < count a h'.
Proof.
  intros Ha Hn; apply (In_refs a v h' n Ha) in Hn.
  apply normal_refs in Ha; rewrite List.forallb_forall in Ha.
  specialize (Ha _ Hn); cbn in Ha; apply Nat.ltb_lt, Ha.
Qed.

(** ** The pass-through part is characterised by the meaning *)

Definition jlen a h : nat := Braun.size (seq_of a h).

Lemma jlen_find a h : jlen a h = length (fst (find a h)).
Proof. unfold jlen; rewrite <- Braun.to_list_length, elems_seq_of; reflexivity. Qed.

(** In a normal adjustment, every outer [h₍ₘ₎] beyond the slots has exactly
    one preimage, the pass-through input. *)
Theorem tail_passthrough a h m :
  normal a = true -> count a h <= m ->
  forall v, apply a v = inl (mk_rvar h m) <-> v = mk_rvar h (m + jlen a h - count a h).
Proof.
  intros Ha Hm v; rewrite jlen_find; unfold apply; split.
  - destruct (nth_error (fst (find a (v_label v))) (v_index v)) as [t|] eqn:E.
    + destruct t as [h' n|p]; cbn [resolve]; [|discriminate].
      intros [= Hh Hi].
      pose proof (slot_bound a v h' n Ha E); subst h'; lia.
    + intros [= Hh Hi]; apply nth_error_None in E.
      destruct v as [hv iv]; cbn in *; subst hv; f_equal; lia.
  - intros ->; cbn [v_label v_index].
    rewrite (proj2 (nth_error_None _ _)) by lia.
    f_equal; f_equal; lia.
Qed.

Lemma resolve_slot_inv a t h k :
  resolve a t = inl (mk_rvar h k) ->
  exists n, t = Slot h n /\ k = count a h - S n.
Proof.
  destruct t as [h' n|p]; cbn [resolve]; [|discriminate].
  intros [= <- <-]; exists n; split; reflexivity.
Qed.

(** In a normal adjustment the innermost slot for [h] is never
    pass-through-like: it is either unreferenced, or referenced by
    something other than a lone last target. *)
Theorem innermost_slot_not_passthrough a h :
  normal a = true -> 0 < count a h ->
  ~ (forall v, apply a v = inl (mk_rvar h (count a h - 1))
               <-> v = mk_rvar h (count a h - 1 + jlen a h - count a h)).
Proof.
  intros Ha Hk H.
  rewrite jlen_find in H.
  destruct (find a h) as [ts k] eqn:Ef.
  rewrite !count_find in *; rewrite Ef in *; cbn [fst snd] in *.
  destruct ts as [|t0 ts0] eqn:Ets.
  - (* no input entries: the candidate preimage passes through elsewhere *)
    cbn [length] in H; replace (k - 1 + 0 - k) with 0 in H by lia.
    specialize (proj2 (H (mk_rvar h 0)) eq_refl) as Happ.
    unfold apply in Happ; cbn [v_label v_index] in Happ.
    rewrite Ef in Happ; cbn [fst nth_error length] in Happ.
    rewrite count_find in Happ; rewrite Ef in Happ; cbn in Happ.
    injection Happ; lia.
  - rewrite <- Ets in *.
    set (jj := length ts) in *.
    assert (Hj : 0 < jj) by (subst jj ts; cbn; lia).
    replace (k - 1 + jj - k) with (pred jj) in H by lia.
    specialize (proj2 (H (mk_rvar h (pred jj))) eq_refl) as Happ.
    unfold apply in Happ; cbn [v_label v_index] in Happ; rewrite Ef in Happ; cbn [fst] in Happ.
    destruct (nth_error ts (pred jj)) as [t|] eqn:Et;
      [|apply nth_error_None in Et; subst jj; lia].
    apply resolve_slot_inv in Happ as [n [-> Hn]].
    rewrite count_find in Hn; rewrite Ef in Hn; cbn [snd] in Hn.
    assert (Hb : n < k).
    { pose proof (slot_bound a (mk_rvar h (pred jj)) h n Ha) as Hsb.
      cbn [v_label v_index] in Hsb; rewrite Ef in Hsb; rewrite count_find in Hsb.
      rewrite Ef in Hsb; apply Hsb, Et. }
    assert (n = 0) as -> by lia.
    (* the strip condition provides another reference to the innermost slot *)
    unfold find in Ef.
    destruct (get (label_key h) a) as [e|] eqn:Ee; [|injection Ef as Hts _; rewrite <- Hts in Ets; discriminate].
    injection Ef as Ets' Hk'.
    pose proof (normal_entries a Ha) as He; rewrite forallb_spec in He.
    specialize (He _ _ Ee); unfold entry_ok in He; rewrite !andb_true_iff in He.
    destruct He as [_ Hstrip].
    rewrite (find_label a h e Ha Ee), Ets' in Hstrip.
    unfold strip_ok, last_target in Hstrip; fold jj in Hstrip; rewrite Et in Hstrip.
    rewrite label_eqb_refl, existsb_exists in Hstrip.
    destruct Hstrip as [[[v' h''] n''] [Hin Hr]].
    destruct n'' as [|n'']; [|discriminate].
    rewrite andb_true_iff, negb_true_iff in Hr; destruct Hr as [Hh'' Hv'].
    apply label_eqb_eq in Hh''; subst h''.
    apply (In_refs a v' h 0 Ha) in Hin.
    assert (Happ' : apply a v' = inl (mk_rvar h (k - 1))).
    { unfold apply; rewrite Hin; cbn [resolve].
      rewrite count_find; unfold find; rewrite Ee; cbn [snd]; rewrite Hk'; do 2 f_equal; lia. }
    apply H in Happ'; rewrite Happ', rvar_eqb_refl in Hv'; discriminate.
Qed.

Lemma resolve_inj a b t1 t2 :
  normal a = true -> normal b = true ->
  (forall h, count a h = count b h) ->
  (forall h n, t1 = Slot h n -> n < count a h) ->
  (forall h n, t2 = Slot h n -> n < count b h) ->
  resolve a t1 = resolve b t2 -> t1 = t2.
Proof.
  intros Ha Hb Hc H1 H2 Heq.
  destruct t1 as [h1 n1|p1], t2 as [h2 n2|p2]; cbn [resolve] in Heq; try discriminate.
  - injection Heq as <- Hn.
    specialize (H1 _ _ eq_refl); specialize (H2 _ _ eq_refl).
    rewrite Hc in H1, Hn; f_equal; lia.
  - injection Heq as ->; reflexivity.
Qed.

(** Normal adjustments with the same meaning have the same targets and slot
    counts; their back-links are compared in [canonical] below. *)
Theorem canonical_shape a b :
  normal a = true -> normal b = true ->
  (forall v, apply a v = apply b v) -> same_shape a b.
Proof.
  intros Ha Hb Heq.
  (* the pass-through offsets agree *)
  assert (Hoff : forall h, jlen a h + count b h = jlen b h + count a h).
  { intro h; set (M := count a h + count b h).
    pose proof (proj2 (tail_passthrough a h M Ha ltac:(lia) _) eq_refl) as Hm.
    rewrite Heq in Hm; apply (tail_passthrough b h M Hb ltac:(lia)) in Hm.
    injection Hm; lia. }
  (* the slot counts agree *)
  assert (Hcnt : forall h, count a h = count b h).
  { intro h; destruct (Nat.lt_trichotomy (count a h) (count b h)) as [Hlt|[Heq'|Hlt]];
      [exfalso| exact Heq' | exfalso].
    - apply (innermost_slot_not_passthrough b h Hb ltac:(lia)); intro v.
      rewrite <- Heq, (tail_passthrough a h (count b h - 1) Ha ltac:(lia)).
      specialize (Hoff h); split; intros ->; f_equal; lia.
    - apply (innermost_slot_not_passthrough a h Ha ltac:(lia)); intro v.
      rewrite Heq, (tail_passthrough b h (count a h - 1) Hb ltac:(lia)).
      specialize (Hoff h); split; intros ->; f_equal; lia. }
  assert (Hlen : forall h, jlen a h = jlen b h) by (intro h; specialize (Hoff h); rewrite Hcnt in Hoff; lia).
  (* the targets agree *)
  assert (Hfind : forall h, find a h = find b h).
  { intro h; destruct (find a h) as [tsa ka] eqn:Ea, (find b h) as [tsb kb] eqn:Eb.
    pose proof (Hcnt h) as Hk; pose proof (Hlen h) as Hj.
    rewrite !count_find in Hk; rewrite !jlen_find in Hj; rewrite Ea, Eb in Hk, Hj; cbn in Hk, Hj; subst kb.
    f_equal; apply nth_error_ext; intro i.
    destruct (nth_error tsa i) as [ta|] eqn:Ta, (nth_error tsb i) as [tb|] eqn:Tb.
    - f_equal; specialize (Heq (mk_rvar h i)); unfold apply in Heq; cbn [v_label v_index] in Heq.
      rewrite Ea, Eb in Heq; cbn [fst] in Heq; rewrite Ta, Tb in Heq.
      apply (resolve_inj a b ta tb Ha Hb Hcnt); [| |exact Heq].
      + intros h' n ->; apply (slot_bound a (mk_rvar h i) h' n Ha); cbn; rewrite Ea; exact Ta.
      + intros h' n ->; apply (slot_bound b (mk_rvar h i) h' n Hb); cbn; rewrite Eb; exact Tb.
    - apply nth_error_None in Tb; assert (i < length tsa) by (apply nth_error_Some; congruence); lia.
    - apply nth_error_None in Ta; assert (i < length tsb) by (apply nth_error_Some; congruence); lia.
    - reflexivity. }
  intro key.
  destruct (get key a) as [ea|] eqn:Ea, (get key b) as [eb|] eqn:Eb.
  - pose proof (normal_label a _ _ Ha Ea) as Ka; pose proof (normal_label b _ _ Hb Eb) as Kb.
    rewrite Ka in Kb; apply label_key_inj in Kb.
    specialize (Hfind (e_label ea)); unfold find in Hfind.
    pose proof (normal_balanced a _ _ Ha Ea) as Ba; pose proof (normal_balanced b _ _ Hb Eb) as Bb.
    rewrite <- Ka, Ea, Eb in Hfind; injection Hfind as Ht Ho.
    destruct ea as [la sa oa ba], eb as [lb sb ob bb]; unfold e_targets in Ht;
      cbn [e_label e_tree e_out] in *; subst.
    unfold shape; cbn; rewrite (Braun.canonical _ _ Ba Bb Ht); reflexivity.
  - exfalso; pose proof (normal_label a _ _ Ha Ea) as Ka.
    specialize (Hfind (e_label ea)); unfold find in Hfind; rewrite <- Ka, Ea, Eb in Hfind.
    injection Hfind as Ht Ho.
    pose proof (normal_entries a Ha) as He; rewrite forallb_spec in He; specialize (He _ _ Ea).
    unfold entry_ok in He; rewrite Ht, Ho in He; cbn in He; rewrite andb_false_r in He; discriminate.
  - exfalso; pose proof (normal_label b _ _ Hb Eb) as Kb.
    specialize (Hfind (e_label eb)); unfold find in Hfind; rewrite <- Kb, Ea, Eb in Hfind.
    injection Hfind as Ht Ho.
    pose proof (normal_entries b Hb) as He; rewrite forallb_spec in He; specialize (He _ _ Eb).
    unfold entry_ok in He; rewrite <- Ht, <- Ho in He; cbn in He; rewrite andb_false_r in He; discriminate.
  - reflexivity.
Qed.

(** ** Slot references, characterised without normality *)

Lemma In_refs_gen a v h' n :
  In (v, h', n) (refs a)
  <-> exists key e, get key a = Some e /\ v_label v = e_label e
                    /\ nth_error (e_targets e) (v_index v) = Some (Slot h' n).
Proof.
  unfold refs; rewrite in_flat_map; split.
  - intros [[key e] [Hin Hr]]; apply In_elements in Hin; cbn [snd] in Hr.
    unfold refs_of_entry in Hr; apply go_refs in Hr as [Hl [_ Hn]].
    rewrite Nat.sub_0_r in Hn; exists key, e; auto.
  - intros [key [e [He [Hl Hn]]]].
    exists (key, e); split; [apply In_elements, He|].
    cbn [snd]; unfold refs_of_entry; apply go_refs.
    rewrite Nat.sub_0_r; repeat split; [exact Hl|lia|exact Hn].
Qed.

(** ** Identity *)

Definition identity : raw P := Empty.

Lemma normal_identity : normal identity = true.
Proof. reflexivity. Qed.

Lemma apply_identity v : apply identity v = inl v.
Proof.
  unfold apply, identity, find, count; cbn [get fst snd length].
  rewrite nth_error_nil; destruct v; cbn; do 2 f_equal; lia.
Qed.

(** ** Adding an output slot: O(log n), no reference changes *)

Definition push_outer h a : raw P :=
  update (label_key h)
    (fun o => Some (match o with
                    | Some e => mk_entry h (e_tree e) (S (e_out e)) (Braun.snoc (e_back e) Empty)
                    | None => mk_entry h BE 1 (BN Empty BE BE)
                    end)) a.

Lemma find_push_outer h a h' :
  normal a = true ->
  find (push_outer h a) h'
  = if label_eqb h' h then (fst (find a h), S (count a h)) else find a h'.
Proof.
  intros Ha; unfold find at 1, push_outer; rewrite get_update, label_key_eqb.
  rewrite count_find; unfold find; destruct (label_eqb_spec h' h) as [->|]; [|reflexivity].
  destruct (get (label_key h) a); reflexivity.
Qed.

Lemma count_push_outer h a h' :
  normal a = true ->
  count (push_outer h a) h' = if label_eqb h' h then S (count a h) else count a h'.
Proof.
  intros Ha; rewrite (count_find (push_outer h a) h'), find_push_outer by exact Ha.
  destruct (label_eqb h' h); cbn [snd]; rewrite ?count_find; reflexivity.
Qed.

Theorem apply_push_outer h a v :
  normal a = true ->
  apply (push_outer h a) v
  = match apply a v with
    | inl w => inl (shift_rvar (mk_rvar h 0) w)
    | inr p => inr p
    end.
Proof.
  intros Ha; unfold apply.
  rewrite !find_push_outer, !count_push_outer by exact Ha.
  destruct v as [hv i]; cbn [v_label v_index].
  assert (Hslot : forall hv i h' n,
             nth_error (fst (find a hv)) i = Some (Slot h' n) ->
             resolve (push_outer h a) (Slot h' n)
             = match resolve a (Slot h' n) with
               | inl w => inl (shift_rvar (mk_rvar h 0) w)
               | inr p => inr p
               end).
  { intros hv' i' h' n Et; cbn [resolve]; rewrite count_push_outer by exact Ha.
    pose proof (slot_bound a (mk_rvar hv' i') h' n Ha Et) as Hb.
    unfold shift_rvar; cbn [v_label v_index]; rewrite (label_eqb_sym h h').
    destruct (label_eqb_spec h' h) as [->|]; cbn [andb Nat.leb]; [do 2 f_equal; lia|reflexivity]. }
  destruct (label_eqb_spec hv h) as [->|Hne]; cbn [fst snd].
  - destruct (nth_error (fst (find a h)) i) as [[h' n|p]|] eqn:Et.
    + apply (Hslot h i h' n Et).
    + reflexivity.
    + unfold shift_rvar; cbn [v_label v_index]; rewrite label_eqb_refl; cbn [andb Nat.leb].
      apply nth_error_None in Et; do 2 f_equal; lia.
  - destruct (nth_error (fst (find a hv)) i) as [[h' n|p]|] eqn:Et.
    + apply (Hslot hv i h' n Et).
    + reflexivity.
    + unfold shift_rvar; cbn [v_label v_index].
      rewrite (proj2 (label_eqb_neq h hv)) by congruence; reflexivity.
Qed.

Lemma existsb_same_members {A} (f : A -> bool) (l1 l2 : list A) :
  (forall x, In x l1 <-> In x l2) -> existsb f l1 = existsb f l2.
Proof.
  intros H; apply Bool.eq_iff_eq_true; rewrite !existsb_exists.
  split; intros [x [Hx Hf]]; exists x; split; auto; apply H; auto.
Qed.

Lemma refs_push_outer h a r :
  normal a = true -> In r (refs (push_outer h a)) <-> In r (refs a).
Proof.
  intros Ha; destruct r as [[v h'] n]; rewrite !In_refs_gen.
  unfold push_outer; split.
  - intros [key [e [He [Hl Hn]]]]; rewrite get_update in He.
    destruct (Pos.eqb_spec key (label_key h)) as [->|].
    + destruct (get (label_key h) a) as [e0|] eqn:E0; injection He as <-;
        cbn [e_label e_targets] in *; [|rewrite nth_error_nil in Hn; discriminate].
      exists (label_key h), e0; repeat split; [exact E0| |exact Hn].
      rewrite Hl; symmetry; apply (find_label a h e0 Ha E0).
    + exists key, e; auto.
  - intros [key [e [He [Hl Hn]]]].
    exists key; rewrite get_update.
    destruct (Pos.eqb_spec key (label_key h)) as [->|].
    + rewrite He; eexists; repeat split; [cbn [e_label]| exact Hn].
      rewrite Hl; apply (find_label a h e Ha He).
    + exists e; auto.
Qed.

Theorem normal_push_outer h a : normal a = true -> normal (push_outer h a) = true.
Proof.
  intros Ha; unfold normal; apply andb_true_iff; split.
  - apply forallb_spec; intros key e He.
    unfold push_outer in He; rewrite get_update in He.
    unfold entry_ok, strip_ok.
    rewrite (existsb_same_members _ (refs (push_outer h a)) (refs a))
      by (intro; apply refs_push_outer, Ha).
    destruct (Pos.eqb_spec key (label_key h)) as [->|].
    + destruct (get (label_key h) a) as [e0|] eqn:E0; injection He as <-.
      * pose proof (normal_entries a Ha) as Hn; rewrite forallb_spec in Hn.
        specialize (Hn _ _ E0); unfold entry_ok, strip_ok in Hn.
        rewrite !andb_true_iff in Hn; destruct Hn as [[[_ Hbal] _] Hs].
        rewrite (find_label a h e0 Ha E0) in Hs.
        change (e_targets (mk_entry h (e_tree e0) (S (e_out e0)) (Braun.snoc (e_back e0) Empty)))
          with (e_targets e0).
        cbn [e_label e_out e_tree]; rewrite Pos.eqb_refl, Hbal; cbn [andb].
        destruct (e_targets e0); exact Hs.
      * cbn; rewrite Pos.eqb_refl; reflexivity.
    + pose proof (normal_entries a Ha) as Hn; rewrite forallb_spec in Hn.
      apply (Hn _ _ He).
  - apply List.forallb_forall; intros [[v h'] n] Hin.
    apply refs_push_outer in Hin; [|exact Ha].
    pose proof (normal_refs a Ha) as Hr; rewrite List.forallb_forall in Hr.
    specialize (Hr _ Hin); cbn [slot_wf] in *; rewrite Nat.ltb_lt in *.
    rewrite count_push_outer by exact Ha; destruct (label_eqb_spec h' h) as [->|]; lia.
Qed.

(** ** Stripping the innermost slot of [h]

    When the last target of [h] is [h]'s innermost slot and nothing else
    refers to that slot, the pair is transparent: remove it, decrement the
    slot count, and renumber the remaining references to [h]'s slots. *)

Definition renumber_target h t : target P :=
  match t with
  | Slot h' n => if label_eqb h' h then Slot h' (pred n) else t
  | Bind _ => t
  end.

Definition renumber h a : raw P :=
  map_filter (fun _ e => Some (mk_entry (e_label e) (Braun.map (renumber_target h) (e_tree e))
                                        (e_out e) (e_back e))) a.

Definition set_entry h (s : braun (target P)) (k : nat) (bk : braun links) a : raw P :=
  update (label_key h)
    (fun _ => if nontrivial_seq s k then Some (mk_entry h s k bk) else None) a.

(** Stripping keeps the back-links of the remaining slots but does not
    renumber the positions in them; callers that strip recompute back-links
    with [relink] afterwards. *)
Definition strip_once h a : raw P :=
  renumber h (set_entry h (Braun.unsnoc (seq_of a h)) (pred (count a h)) (Braun.tail (backs_of a h)) a).

Lemma find_set_entry h s k bk a h' :
  find (set_entry h s k bk a) h' = if label_eqb h' h then (Braun.to_list s, k) else find a h'.
Proof.
  unfold find at 1, set_entry; rewrite get_update, label_key_eqb.
  destruct (label_eqb h' h); [|reflexivity].
  rewrite nontrivial_seq_elems; unfold e_targets; cbn [e_tree e_out].
  destruct (Braun.to_list s) eqn:E, k; cbn; rewrite ?E; reflexivity.
Qed.

Lemma find_renumber h a h' :
  find (renumber h a) h' = (map (renumber_target h) (fst (find a h')), snd (find a h')).
Proof.
  unfold find, renumber; rewrite get_map_filter.
  destruct (get (label_key h') a); [|reflexivity].
  unfold e_targets; cbn [e_tree e_out fst snd]; rewrite Braun.to_list_map; reflexivity.
Qed.

(** Entries of a [set_entry] or a renumbering, and their non-triviality. *)
Lemma get_set_entry h s k bk a key e :
  get key (set_entry h s k bk a) = Some e ->
  (key = label_key h /\ e_label e = h /\ nontrivial (e_targets e) (e_out e) = true)
  \/ (key <> label_key h /\ get key a = Some e).
Proof.
  unfold set_entry; rewrite get_update.
  destruct (Pos.eqb_spec key (label_key h)) as [->|Hne]; [|right; auto].
  destruct (nontrivial_seq s k) eqn:N; [|discriminate].
  intros [= <-]; left; unfold e_targets; cbn [e_tree e_label e_out]; rewrite <- nontrivial_seq_elems; auto.
Qed.

Lemma get_map_seq (f : target P -> target P) a key e :
  get key (map_filter (fun _ e => Some (mk_entry (e_label e) (Braun.map f (e_tree e)) (e_out e) (e_back e))) a)
    = Some e ->
  exists e0, get key a = Some e0 /\ e_label e = e_label e0
             /\ nontrivial (e_targets e) (e_out e) = nontrivial (e_targets e0) (e_out e0).
Proof.
  rewrite get_map_filter; destruct (get key a) as [e0|]; [|discriminate].
  intros [= <-]; exists e0; unfold e_targets; cbn [e_tree e_label e_out]; rewrite Braun.to_list_map.
  destruct (Braun.to_list (e_tree e0)); auto.
Qed.

Lemma count_strip_once h a h' :
  count (strip_once h a) h' = if label_eqb h' h then pred (count a h) else count a h'.
Proof.
  rewrite count_find at 1; unfold strip_once; rewrite find_renumber, find_set_entry; cbn [snd].
  destruct (label_eqb h' h); rewrite ?count_find; reflexivity.
Qed.

Lemma find_strip_once h a h' :
  keys_ok a = true ->
  find (strip_once h a) h'
  = (map (renumber_target h)
         (if label_eqb h' h then removelast (fst (find a h)) else fst (find a h')),
     if label_eqb h' h then pred (count a h) else count a h').
Proof.
  intros Hk; unfold strip_once; rewrite find_renumber, find_set_entry.
  destruct (label_eqb h' h); cbn [fst snd];
    rewrite ?(proj2 (Braun.unsnoc_spec _ (keys_ok_balanced a h Hk))), ?elems_seq_of, ?count_find;
    reflexivity.
Qed.

(** The condition under which [strip_once] is applied. *)
Definition strippable a h : Prop :=
  last_target (fst (find a h)) = Some (Slot h 0)
  /\ (forall v, nth_error (fst (find a (v_label v))) (v_index v) = Some (Slot h 0) ->
                v = mk_rvar h (pred (length (fst (find a h)))))
  /\ (forall v h' n, nth_error (fst (find a (v_label v))) (v_index v) = Some (Slot h' n) ->
                     n < count a h').

Lemma removelast_nth {A} (l : list A) i :
  i < pred (length l) -> nth_error (removelast l) i = nth_error l i.
Proof.
  revert i; induction l as [|x l IH]; intros i Hi; [reflexivity|].
  destruct l as [|y l]; [cbn in Hi; lia|].
  change (removelast (x :: y :: l)) with (x :: removelast (y :: l)).
  destruct i; [reflexivity|cbn [nth_error]; apply IH; cbn in *; lia].
Qed.

Lemma length_removelast {A} (l : list A) : length (removelast l) = pred (length l).
Proof.
  induction l as [|x l IH]; [reflexivity|].
  destruct l as [|y l]; [reflexivity|].
  change (removelast (x :: y :: l)) with (x :: removelast (y :: l)).
  cbn [length] in *; rewrite IH; reflexivity.
Qed.

Theorem apply_strip_once h a v :
  keys_ok a = true -> strippable a h -> apply (strip_once h a) v = apply a v.
Proof.
  intros Hko [Hlast [Huniq Hwf]].
  unfold last_target in Hlast.
  set (ts := fst (find a h)) in *; set (k := count a h).
  assert (Hk : 0 < k).
  { pose proof (Hwf (mk_rvar h (pred (length ts))) h 0) as Hw; cbn in Hw.
    apply Hw, Hlast. }
  assert (Hlen : 0 < length ts) by (destruct ts; [discriminate|cbn; lia]).
  unfold apply; destruct v as [hv i]; cbn [v_label v_index].
  rewrite find_strip_once by exact Hko; rewrite count_strip_once; cbn [fst snd].
  assert (Hres : forall h' n, (forall v, nth_error (fst (find a (v_label v))) (v_index v)
                                           = Some (Slot h' n) -> True) ->
                 True) by auto.
  clear Hres.
  (* resolution of a renumbered slot reference that is not the stripped one *)
  assert (Hr : forall w h' n,
             nth_error (fst (find a (v_label w))) (v_index w) = Some (Slot h' n) ->
             w <> mk_rvar h (pred (length ts)) ->
             resolve (strip_once h a) (renumber_target h (Slot h' n))
             = resolve a (Slot h' n)).
  { intros w h' n Hw Hne; cbn [renumber_target].
    destruct (label_eqb_spec h' h) as [->|Hh]; cbn [resolve]; rewrite count_strip_once.
    - rewrite label_eqb_refl.
      destruct n as [|n]; [exfalso; apply Hne, Huniq, Hw|].
      pose proof (Hwf _ _ _ Hw) as Hn'; fold k in Hn' |- *; cbn [pred]; do 2 f_equal; lia.
    - rewrite (proj2 (label_eqb_neq h' h) Hh); reflexivity. }
  destruct (label_eqb_spec hv h) as [->|Hne].
  - rewrite nth_error_map, length_map, length_removelast; fold ts k.
    destruct (Nat.lt_ge_cases i (pred (length ts))) as [Hi|Hi].
    + rewrite removelast_nth by exact Hi.
      destruct (nth_error ts i) as [[h' n|p]|] eqn:E; cbn [option_map];
        [| reflexivity | apply nth_error_None in E; lia].
      apply (Hr (mk_rvar h i) h' n E); intro H; injection H; lia.
    + rewrite (proj2 (nth_error_None (removelast ts) i)) by (rewrite length_removelast; lia).
      destruct (Nat.eq_dec i (pred (length ts))) as [->|Hi'].
      * rewrite Hlast; cbn [resolve option_map]; fold k; do 2 f_equal; lia.
      * rewrite (proj2 (nth_error_None ts i)) by lia; cbn [option_map]; do 2 f_equal; lia.
  - rewrite nth_error_map, length_map.
    destruct (nth_error (fst (find a hv)) i) as [[h' n|p]|] eqn:E; cbn [option_map];
      [| reflexivity | reflexivity].
    apply (Hr (mk_rvar hv i) h' n E); intro H; injection H; congruence.
Qed.

(** ** Normal forms in terms of [find] *)



Lemma normal_keys_ok a : normal a = true -> keys_ok a = true.
Proof.
  intros Ha; apply keys_ok_spec; intros key e He; split;
    [apply (normal_label a key e Ha He)|apply (normal_balanced a key e Ha He)].
Qed.

Lemma keys_ok_label a h e : keys_ok a = true -> get (label_key h) a = Some e -> e_label e = h.
Proof.
  intros Ha He; apply label_key_inj; symmetry; apply (proj1 (proj1 (keys_ok_spec a) Ha _ _ He)).
Qed.

Lemma In_refs_keys a v h' n :
  keys_ok a = true ->
  In (v, h', n) (refs a) <-> nth_error (fst (find a (v_label v))) (v_index v) = Some (Slot h' n).
Proof.
  intros Ha; rewrite In_refs_gen; split.
  - intros [key [e [He [Hl Hn]]]].
    pose proof (proj1 (proj1 (keys_ok_spec a) Ha _ _ He)) as Hk.
    unfold find; rewrite Hl, <- Hk, He; exact Hn.
  - intros Hn; unfold find in Hn.
    destruct (get (label_key (v_label v)) a) as [e|] eqn:E; [|rewrite nth_error_nil in Hn; discriminate].
    exists (label_key (v_label v)), e; repeat split; [exact E| |exact Hn].
    symmetry; apply (keys_ok_label a _ e Ha E).
Qed.

Definition other_ref a h (ts : list (target P)) : Prop :=
  exists v, nth_error (fst (find a (v_label v))) (v_index v) = Some (Slot h 0)
            /\ v <> mk_rvar h (pred (length ts)).

Lemma strip_ok_spec a h ts :
  keys_ok a = true ->
  strip_ok a h ts = true <-> (last_target ts = Some (Slot h 0) -> other_ref a h ts).
Proof.
  intros Ha; unfold strip_ok.
  destruct (last_target ts) as [[h' n|p]|].
  2,3: split; [intros _ H; discriminate|reflexivity].
  destruct n as [|n]; [|split; [intros _ H; discriminate|reflexivity]].
  destruct (label_eqb_spec h' h) as [->|Hne].
  - rewrite existsb_exists; split.
    + intros [[[v h''] n''] [Hin Hr]] _.
      destruct n''; [|discriminate].
      rewrite andb_true_iff, negb_true_iff in Hr; destruct Hr as [Hh Hv].
      apply label_eqb_eq in Hh; subst h''.
      exists v; split; [apply (In_refs_keys a v h 0 Ha), Hin|].
      intro Heq; rewrite Heq, rvar_eqb_refl in Hv; discriminate.
    + intros H; destruct (H eq_refl) as [v [Hn Hv]].
      exists (v, h, 0); split; [apply (In_refs_keys a v h 0 Ha), Hn|].
      rewrite label_eqb_refl; cbn [andb].
      destruct (rvar_eqb_spec v (mk_rvar h (pred (length ts)))); [contradiction|reflexivity].
  - split; [intros _ H; injection H; congruence|reflexivity].
Qed.

(** Everything in [normal] except the strip conditions for the labels in
    [Q]. *)
Definition pre_normal a (Q : option label -> Prop) : Prop :=
  keys_ok a = true
  /\ (forall key e, get key a = Some e -> nontrivial (e_targets e) (e_out e) = true)
  /\ (forall v h' n, nth_error (fst (find a (v_label v))) (v_index v) = Some (Slot h' n) ->
                     n < count a h')
  /\ (forall h', ~ Q h' -> strip_ok a h' (fst (find a h')) = true).

(** Everything in [normal] except the strip condition for [h]. *)
Definition almost_normal a h : Prop := pre_normal a (fun l => l = h).

Lemma find_entry_targets a h e :
  keys_ok a = true -> get (label_key h) a = Some e -> find a h = (e_targets e, e_out e).
Proof. intros _ He; unfold find; rewrite He; reflexivity. Qed.

Theorem normal_iff a h :
  normal a = true <-> almost_normal a h /\ strip_ok a h (fst (find a h)) = true.
Proof.
  split.
  - intros Ha; pose proof (normal_keys_ok a Ha) as Hk.
    pose proof (normal_entries a Ha) as He; rewrite forallb_spec in He.
    assert (Hs : forall h', strip_ok a h' (fst (find a h')) = true).
    { intro h'; unfold find; destruct (get (label_key h') a) as [e|] eqn:E; [|reflexivity].
      specialize (He _ _ E); unfold entry_ok in He; rewrite !andb_true_iff in He.
      rewrite <- (keys_ok_label a h' e Hk E); apply He. }
    repeat split; auto.
    + intros key e E; specialize (He _ _ E); unfold entry_ok in He.
      rewrite !andb_true_iff in He; apply He.
    + intros v h' n Hn; apply (slot_bound a v h' n Ha Hn).
  - intros [[Hk [Hnt [Hwf Hs]]] Hsh].
    unfold normal; apply andb_true_iff; split.
    + apply forallb_spec; intros key e E.
      destruct (proj1 (keys_ok_spec a) Hk _ _ E) as [Hkey Hbal].
      unfold entry_ok; rewrite Hkey, Pos.eqb_refl, (proj2 (Braun.balancedb_spec _) Hbal), (Hnt _ _ E).
      cbn [andb].
      assert (Ef : fst (find a (e_label e)) = e_targets e)
        by (unfold find; rewrite <- Hkey, E; reflexivity).
      destruct (label_eq_dec (e_label e) h) as [Heq|Hne].
      * rewrite <- Ef, Heq; exact Hsh.
      * rewrite <- Ef; apply Hs, Hne.
    + apply List.forallb_forall; intros [[v h'] n] Hin; cbn [slot_wf].
      apply Nat.ltb_lt, (Hwf v), (In_refs_keys a v h' n Hk), Hin.
Qed.

(** ** Back-links

    Each entry records, for each of its output slots (innermost first, as
    in slot references), the inputs that refer to that slot: the key of the
    referring label and the positions of the referring inputs, counted from
    the back of that label's targets.  Counting from the back keeps the
    positions stable when an input is added in front ([cons_entry]).

    Back-links are determined by the targets ([refers]), so they do not
    affect canonicity; [linked a] says that they are correct.  They let
    [push_inner] decide in O(log n) whether to strip, and renumber exactly
    the inputs that refer to the stripped label's slots. *)

Definition pos_key (p : nat) : positive := Pos.of_succ_nat p.
Definition key_pos (k : positive) : nat := pred (Pos.to_nat k).

Lemma key_pos_key p : key_pos (pos_key p) = p.
Proof. apply SuccNat2Pos.pred_id. Qed.

Lemma pos_key_pos k : pos_key (key_pos k) = k.
Proof. apply SuccNat2Pos.inv; unfold key_pos; pose proof (Pos2Nat.is_pos k); lia. Qed.

Definition link_add (k : positive) (p : nat) (s : links) : links :=
  update k (fun o => Some (set (pos_key p) tt (match o with Some ps => ps | None => Empty end))) s.

Definition link_mem (k : positive) (p : nat) (s : links) : Prop :=
  exists ps, get k s = Some ps /\ get (pos_key p) ps = Some tt.

(** Canonical link sets: no label with an empty set of positions. *)
Definition links_wf (s : links) : Prop := forall k ps, get k s = Some ps -> ps <> Empty.

Lemma links_wf_empty : links_wf Empty.
Proof. intros k ps H; rewrite get_Empty in H; discriminate. Qed.

Lemma link_mem_empty k p : ~ link_mem k p Empty.
Proof. intros [ps [H _]]; rewrite get_Empty in H; discriminate. Qed.

Lemma link_mem_add k p s k' p' :
  link_mem k' p' (link_add k p s) <-> (k' = k /\ p' = p) \/ link_mem k' p' s.
Proof.
  unfold link_mem, link_add; rewrite get_update.
  destruct (Pos.eqb_spec k' k) as [->|Hne].
  - split.
    + intros [ps [[= <-] Hp]]; rewrite get_set in Hp.
      destruct (Pos.eqb_spec (pos_key p') (pos_key p)) as [E|].
      * left; split; [reflexivity|]; rewrite <- (key_pos_key p'), E, key_pos_key; reflexivity.
      * right; destruct (get k s) as [ps0|]; [exists ps0; auto|rewrite get_Empty in Hp; discriminate].
    + intros [[_ ->]|[ps [E Hp]]]; eexists; split; try reflexivity; rewrite get_set.
      * rewrite Pos.eqb_refl; reflexivity.
      * rewrite E; destruct (Pos.eqb _ _); [destruct (get _ ps) as [[]|]|]; auto.
  - split; [intros H; right; exact H|intros [[E _]|H]; [contradiction|exact H]].
Qed.

Lemma links_wf_add k p s : links_wf s -> links_wf (link_add k p s).
Proof.
  intros Hs k' ps; unfold link_add; rewrite get_update.
  destruct (Pos.eqb k' k); [|apply Hs].
  intros [= <-] E; assert (H := get_set (pos_key p) (pos_key p) tt
                                 (match get k s with Some ps => ps | None => Empty end)).
  rewrite E, get_Empty, Pos.eqb_refl in H; discriminate.
Qed.

Lemma links_ext s1 s2 :
  links_wf s1 -> links_wf s2 -> (forall k p, link_mem k p s1 <-> link_mem k p s2) -> s1 = s2.
Proof.
  intros W1 W2 H.
  assert (Hside : forall s s', links_wf s -> (forall k p, link_mem k p s -> link_mem k p s') ->
                  forall k ps, get k s = Some ps -> exists ps', get k s' = Some ps').
  { intros s s' W H' k ps E.
    destruct (get_nonempty ps (W _ _ E)) as [i [[] Ei]].
    destruct (H' k (key_pos i)) as [ps' [E' _]]; [exists ps; rewrite pos_key_pos; auto|].
    exists ps'; exact E'. }
  apply extensionality; intro k.
  destruct (get k s1) as [ps1|] eqn:E1, (get k s2) as [ps2|] eqn:E2.
  - f_equal; apply extensionality; intro i.
    specialize (H k (key_pos i)); unfold link_mem in H; rewrite pos_key_pos, E1, E2 in H.
    destruct (get i ps1) as [[]|] eqn:G1, (get i ps2) as [[]|] eqn:G2; try reflexivity.
    + destruct (proj1 H (ex_intro _ ps1 (conj eq_refl G1))) as [q [[= <-] Q]]; congruence.
    + destruct (proj2 H (ex_intro _ ps2 (conj eq_refl G2))) as [q [[= <-] Q]]; congruence.
  - destruct (Hside s1 s2 W1 (fun k p => proj1 (H k p)) k ps1 E1); congruence.
  - destruct (Hside s2 s1 W2 (fun k p => proj2 (H k p)) k ps2 E2); congruence.
  - reflexivity.
Qed.

Definition links_eqb (s1 s2 : links) : bool := teqb (teqb (fun _ _ => true)) s1 s2.

Lemma links_eqb_spec s1 s2 : links_eqb s1 s2 = true <-> s1 = s2.
Proof.
  apply teqb_spec; intros x y; apply teqb_spec; intros [] []; split; reflexivity.
Qed.

(** The inputs referring to slot [j] of [h]. *)
Definition refers a h (j : nat) (k : positive) (p : nat) : Prop :=
  exists e, get k a = Some e /\ p < Braun.size (e_tree e)
            /\ nth_error (e_targets e) (Braun.size (e_tree e) - S p) = Some (Slot h j).

(** Back-links that record the relation [R] (label, slot, key, position). *)
Definition backs_for (R : option label -> nat -> positive -> nat -> Prop) (e : entry P) : Prop :=
  Braun.balanced (e_back e) /\ Braun.size (e_back e) = e_out e
  /\ forall j s, Braun.nth j (e_back e) = Some s ->
       links_wf s /\ forall k p, link_mem k p s <-> R (e_label e) j k p.

(** Correct back-links for an entry of [a]. *)
Definition backs_ok a (e : entry P) : Prop := backs_for (refers a) e.

Lemma backs_for_iff (R R' : option label -> nat -> positive -> nat -> Prop) e :
  (forall g j k p, R g j k p <-> R' g j k p) -> backs_for R e -> backs_for R' e.
Proof.
  intros HR [B [Sz M]]; split; [exact B|split; [exact Sz|]]; intros j s E.
  destruct (M j s E) as [W M']; split; [exact W|]; intros k p; rewrite M'; apply HR.
Qed.

Definition linked_prop a : Prop := forall key e, get key a = Some e -> backs_ok a e.

Lemma nth_none_size {A} (t : braun A) i : Braun.balanced t -> Braun.nth i t = None <-> Braun.size t <= i.
Proof. intros Hb; rewrite Braun.nth_to_list, nth_error_None, Braun.to_list_length by exact Hb; reflexivity. Qed.

Lemma backs_unique a e1 e2 :
  backs_ok a e1 -> backs_ok a e2 -> e_label e1 = e_label e2 -> e_out e1 = e_out e2 ->
  e_back e1 = e_back e2.
Proof.
  intros [B1 [Sz1 H1]] [B2 [Sz2 H2]] HL HO.
  apply Braun.canonical; [exact B1|exact B2|].
  apply nth_error_ext; intro j; rewrite <- !Braun.nth_to_list by assumption.
  destruct (Braun.nth j (e_back e1)) as [s1|] eqn:E1, (Braun.nth j (e_back e2)) as [s2|] eqn:E2.
  - f_equal; destruct (H1 _ _ E1) as [W1 M1], (H2 _ _ E2) as [W2 M2].
    apply links_ext; auto; intros k p; rewrite M1, M2, HL; reflexivity.
  - apply nth_none_size in E2; [|exact B2].
    assert (Braun.nth j (e_back e1) <> None) by congruence.
    rewrite nth_none_size in H by exact B1; lia.
  - apply nth_none_size in E1; [|exact B1].
    assert (Braun.nth j (e_back e2) <> None) by congruence.
    rewrite nth_none_size in H by exact B2; lia.
  - reflexivity.
Qed.

(** *** Everything except back-links is determined by the shape *)

Lemma shape_get a b key e :
  same_shape a b -> get key a = Some e ->
  exists e', get key b = Some e' /\ shape e' = shape e.
Proof.
  intros H E; specialize (H key); rewrite E in H.
  destruct (get key b) as [e'|]; [|discriminate]; exists e'; split; [reflexivity|].
  cbn [option_map] in H; congruence.
Qed.

Lemma same_shape_sym a b : same_shape a b -> same_shape b a.
Proof. intros H key; symmetry; apply H. Qed.

Lemma same_shape_trans a b c : same_shape a b -> same_shape b c -> same_shape a c.
Proof. intros H1 H2 key; rewrite H1; apply H2. Qed.

Lemma shape_find a b h : same_shape a b -> find a h = find b h.
Proof.
  intros H; specialize (H (label_key h)); unfold find.
  destruct (get (label_key h) a) as [e|], (get (label_key h) b) as [e'|];
    cbn in H; try discriminate; [|reflexivity].
  injection H as El Et Eo; unfold e_targets; rewrite Et, Eo; reflexivity.
Qed.

Lemma shape_count a b h : same_shape a b -> count a h = count b h.
Proof. intros H; rewrite !count_find, (shape_find a b h H); reflexivity. Qed.

Lemma shape_seq_of a b h : same_shape a b -> seq_of a h = seq_of b h.
Proof.
  intros H; specialize (H (label_key h)); unfold seq_of.
  destruct (get (label_key h) a) as [e|], (get (label_key h) b) as [e'|];
    cbn in H; try discriminate; [|reflexivity].
  injection H as _ Et _; exact Et.
Qed.

Lemma shape_jlen a b h : same_shape a b -> jlen a h = jlen b h.
Proof. intros H; unfold jlen; rewrite (shape_seq_of a b h H); reflexivity. Qed.

Lemma shape_resolve a b t : same_shape a b -> resolve a t = resolve b t.
Proof. intros H; destruct t; cbn; rewrite ?(shape_count a b _ H); reflexivity. Qed.

Lemma shape_apply a b v : same_shape a b -> apply a v = apply b v.
Proof.
  intros H; unfold apply; rewrite (shape_find a b _ H), (shape_count a b _ H).
  destruct (nth_error _ _); [apply shape_resolve, H|reflexivity].
Qed.

Lemma shape_lookup a b v : same_shape a b -> lookup a v = lookup b v.
Proof.
  intros H; unfold lookup; rewrite (shape_seq_of a b _ H), (shape_count a b _ H).
  destruct (Braun.nth _ _); [apply shape_resolve, H|reflexivity].
Qed.

Lemma shape_refs a b r : same_shape a b -> In r (refs a) <-> In r (refs b).
Proof.
  intros H; destruct r as [[v h'] n]; rewrite !In_refs_gen.
  split; intros [key [e [E [Hl Hn]]]]; [destruct (shape_get a b key e H E) as [e' [E' Sh]]
                                       |destruct (shape_get b a key e (same_shape_sym a b H) E) as [e' [E' Sh]]];
    exists key, e'; unfold shape, e_targets in *; injection Sh as -> -> _; auto.
Qed.

Lemma shape_refers a b h j k p : same_shape a b -> refers a h j k p <-> refers b h j k p.
Proof.
  intros H; split; intros [e [E R]];
    [destruct (shape_get a b k e H E) as [e' [E' Sh]]
    |destruct (shape_get b a k e (same_shape_sym a b H) E) as [e' [E' Sh]]];
    exists e'; unfold shape, e_targets in *; injection Sh as _ -> _; auto.
Qed.

Lemma shape_keys_ok a b : same_shape a b -> keys_ok a = keys_ok b.
Proof.
  intros H; apply Bool.eq_iff_eq_true; rewrite !keys_ok_spec; split; intros K key e E;
    [destruct (shape_get b a key e (same_shape_sym a b H) E) as [e' [E' Sh]]
    |destruct (shape_get a b key e H E) as [e' [E' Sh]]];
    unfold shape in Sh; injection Sh as Hl Ht _; rewrite <- Hl, <- Ht; apply (K _ _ E').
Qed.

Lemma shape_strip_ok a b h ts : same_shape a b -> strip_ok a h ts = strip_ok b h ts.
Proof.
  intros H; unfold strip_ok; destruct (last_target ts) as [[h' [|n]|p]|]; try reflexivity.
  destruct (label_eqb h' h); [|reflexivity].
  apply existsb_same_members; intro; apply shape_refs, H.
Qed.

Lemma shape_pre_normal a b Q : same_shape a b -> pre_normal a Q -> pre_normal b Q.
Proof.
  intros H [Hk [Hnt [Hwf Hs]]]; repeat split.
  - rewrite <- (shape_keys_ok a b H); exact Hk.
  - intros key e E; destruct (shape_get b a key e (same_shape_sym a b H) E) as [e' [E' Sh]].
    unfold shape, e_targets in *; injection Sh as _ <- <-; apply (Hnt _ _ E').
  - intros v h' n; rewrite <- !(shape_find a b _ H), <- (shape_count a b _ H); apply Hwf.
  - intros h' Hq; rewrite <- (shape_find a b _ H), <- (shape_strip_ok a b _ _ H); apply Hs, Hq.
Qed.

Lemma shape_normal a b : same_shape a b -> normal a = true -> normal b = true.
Proof.
  intros H Ha; apply (normal_iff b None); pose proof (proj1 (normal_iff a None) Ha) as [Hp Hs].
  split; [apply (shape_pre_normal a b _ H Hp)|].
  rewrite <- (shape_find a b _ H), <- (shape_strip_ok a b _ _ H); exact Hs.
Qed.

Lemma shape_backs_ok a b e : same_shape a b -> backs_ok a e -> backs_ok b e.
Proof.
  intros H [B [Sz M]]; split; [exact B|split; [exact Sz|]].
  intros j s E; destruct (M j s E) as [W M'];
    split; [exact W|]; intros k p; rewrite M'; apply shape_refers, H.
Qed.

Lemma shape_linked_prop a b : same_shape a b -> linked_prop a ->
  (forall key e e', get key a = Some e -> get key b = Some e' -> e_back e' = e_back e) ->
  linked_prop b.
Proof.
  intros H L Hb key e' E'.
  destruct (shape_get b a key e' (same_shape_sym a b H) E') as [e [E Sh]].
  destruct (shape_backs_ok a b e H (L _ _ E)) as [B [Sz M]].
  unfold shape in Sh; injection Sh as Hl _ Ho.
  rewrite <- (Hb _ _ _ E E') in B, Sz, M; split; [exact B|split; [lia|]].
  intros j s El; rewrite <- Hl; apply M, El.
Qed.

(** *** Computing back-links from scratch *)

Definition with_backs (e : entry P) (bk : braun links) : entry P :=
  mk_entry (e_label e) (e_tree e) (e_out e) bk.

(** Record that the input at position [p] (from the back) of the label with
    key [k] refers to slot [j] of [h]. *)
Definition add_link h (j : nat) (k : positive) (p : nat) a : raw P :=
  update (label_key h)
    (option_map (fun e => with_backs e (Braun.update j (link_add k p) (e_back e)))) a.

Definition empty_backs (n : nat) : braun links := Braun.of_list (repeat Empty n).

Definition unlinked a : raw P :=
  map_filter (fun _ e => Some (with_backs e (empty_backs (e_out e)))) a.

Definition link_ref a (r : raw P) (x : rvar * option label * nat) : raw P :=
  match x with
  | (v, h, j) => add_link h j (label_key (v_label v)) (jlen a (v_label v) - S (v_index v)) r
  end.

Definition relink a : raw P := fold_left (link_ref a) (refs a) (unlinked a).

Lemma shape_add_link h j k p a : same_shape (add_link h j k p a) a.
Proof.
  intro key; unfold add_link; rewrite get_update.
  destruct (Pos.eqb_spec key (label_key h)) as [->|]; [|reflexivity].
  destruct (get (label_key h) a); reflexivity.
Qed.

Lemma shape_unlinked a : same_shape (unlinked a) a.
Proof. intro key; unfold unlinked; rewrite get_map_filter; destruct (get key a); reflexivity. Qed.

Lemma shape_relink a : same_shape (relink a) a.
Proof.
  unfold relink; generalize (unlinked a) (shape_unlinked a); generalize (refs a).
  intros L; induction L as [|x L IH]; intros r Hr; [exact Hr|].
  apply IH; destruct x as [[v h] j].
  apply (same_shape_trans _ r a (shape_add_link _ _ _ _ _) Hr).
Qed.

(** The condition on slot references that [relink] needs. *)
Definition slots_ok a : Prop :=
  keys_ok a = true
  /\ forall v h' n, nth_error (fst (find a (v_label v))) (v_index v) = Some (Slot h' n) ->
                    n < count a h'.

Lemma pre_normal_slots_ok a Q : pre_normal a Q -> slots_ok a.
Proof. intros [Hk [_ [Hwf _]]]; split; assumption. Qed.

Lemma normal_slots_ok a : normal a = true -> slots_ok a.
Proof. intros Ha; apply (pre_normal_slots_ok a (fun l => l = None)), (proj1 (normal_iff a None) Ha). Qed.

(** References in terms of back positions. *)
Lemma refs_refers a h j k p :
  keys_ok a = true ->
  (exists v, In (v, h, j) (refs a) /\ k = label_key (v_label v)
             /\ p = jlen a (v_label v) - S (v_index v))
  <-> refers a h j k p.
Proof.
  intros Hk; split.
  - intros [v [Hin [-> ->]]]; apply In_refs_gen in Hin as [key [e [E [Hl Hn]]]].
    pose proof (proj1 (proj1 (keys_ok_spec a) Hk _ _ E)) as Key.
    assert (Hj : jlen a (v_label v) = Braun.size (e_tree e))
      by (unfold jlen, seq_of; rewrite Hl, <- Key, E; reflexivity).
    assert (Hi : v_index v < Braun.size (e_tree e))
      by (rewrite <- Braun.to_list_length; apply nth_error_Some; fold (e_targets e); congruence).
    exists e; rewrite Hj, Hl, <- Key; split; [exact E|split; [lia|]].
    replace (Braun.size (e_tree e) - S (Braun.size (e_tree e) - S (v_index v))) with (v_index v) by lia.
    exact Hn.
  - intros [e [E [Hp Hn]]].
    pose proof (proj1 (proj1 (keys_ok_spec a) Hk _ _ E)) as Key.
    exists (mk_rvar (e_label e) (Braun.size (e_tree e) - S p)); cbn [v_label v_index].
    assert (Hj : jlen a (e_label e) = Braun.size (e_tree e))
      by (unfold jlen, seq_of; rewrite <- Key, E; reflexivity).
    rewrite Hj; repeat split; [|exact Key|lia].
    apply In_refs_gen; exists k, e; auto.
Qed.

Lemma relink_spec a : slots_ok a -> same_shape (relink a) a /\ linked_prop (relink a).
Proof.
  intros [Hk Hwf].
  set (Inv := fun (L : list (rvar * option label * nat)) (r : raw P) =>
    same_shape r a
    /\ forall key e, get key r = Some e ->
       Braun.balanced (e_back e) /\ Braun.size (e_back e) = e_out e
       /\ forall j s, Braun.nth j (e_back e) = Some s ->
          links_wf s /\ forall k p, link_mem k p s
                                    <-> exists v, In (v, e_label e, j) L /\ k = label_key (v_label v)
                                                  /\ p = jlen a (v_label v) - S (v_index v)).
  assert (Hstep : forall L1 L2 r, L1 ++ L2 = refs a -> Inv L1 r ->
                  Inv (refs a) (fold_left (link_ref a) L2 r)).
  { intros L1 L2; revert L1; induction L2 as [|x L2 IH]; intros L1 r HL HI.
    { rewrite app_nil_r in HL; subst; exact HI. }
    cbn [fold_left]; apply (IH (L1 ++ [x])); [rewrite <- app_assoc; exact HL|].
    destruct HI as [Hs HI]; destruct x as [[v h] j].
    assert (Hin : In (v, h, j) (refs a)) by (rewrite <- HL; apply in_or_app; right; left; reflexivity).
    apply (In_refs_keys a v h j Hk) in Hin as Hn.
    pose proof (Hwf _ _ _ Hn) as Hl.
    split; [apply (same_shape_trans _ r a (shape_add_link _ _ _ _ _) Hs)|].
    intros key e E; unfold link_ref, add_link in E; rewrite get_update in E.
    destruct (Pos.eqb_spec key (label_key h)) as [->|Hne].
    - destruct (get (label_key h) r) as [e0|] eqn:E0; [|discriminate].
      injection E as <-; cbn [with_backs e_back e_out e_label].
      destruct (HI _ _ E0) as [B [Sz M]].
      destruct (shape_get r a _ e0 Hs E0) as [e1 [E1 Sh]].
      assert (Lh : e_label e0 = h)
        by (unfold shape in Sh; injection Sh as <- _ _; apply (keys_ok_label a h e1 Hk E1)).
      split; [apply Braun.balanced_update, B|split; [rewrite Braun.size_update; exact Sz|]].
      intros j' s Es; rewrite Braun.nth_update in Es;
        destruct (Nat.eqb_spec j j') as [<-|Hll]; split.
      + destruct (Braun.nth j (e_back e0)) as [s0|] eqn:Es0; [|discriminate].
        injection Es as <-; apply links_wf_add, (M _ _ Es0).
      + destruct (Braun.nth j (e_back e0)) as [s0|] eqn:Es0;
          [|apply nth_none_size in Es0; [|exact B]; unfold count in Hl;
            destruct (shape_get r a _ e0 Hs E0) as [e2 [E2 Sh2]];
            unfold shape in Sh2; injection Sh2 as _ _ Ho; rewrite E2, Ho in Hl; lia].
        injection Es as <-; intros k p; rewrite link_mem_add, (proj2 (M _ _ Es0)), Lh.
        split.
        * intros [[-> ->]|[v' [Hv' R]]]; [exists v; repeat split; auto; apply in_or_app; right; left; reflexivity|].
          exists v'; split; [apply in_or_app; left; exact Hv'|exact R].
        * intros [v' [Hv' R]]; apply in_app_or in Hv' as [Hv'|[E'|[]]]; [right; exists v'; auto|].
          left; injection E'; intros; subst; destruct R as [-> ->]; auto.
      + apply (M _ _ Es).
      + intros k p; rewrite (proj2 (M _ _ Es)), Lh; split.
        * intros [v' [Hv' R]]; exists v'; split; [apply in_or_app; left; exact Hv'|exact R].
        * intros [v' [Hv' R]]; apply in_app_or in Hv' as [Hv'|[E'|[]]]; [exists v'; auto|].
          injection E'; intros; subst; contradiction.
    - destruct (HI _ _ E) as [B [Sz M]]; split; [exact B|split; [exact Sz|]]; intros j' s Es.
      destruct (M _ _ Es) as [W M']; split; [exact W|]; intros k p; rewrite M'; split.
      + intros [v' [Hv' R]]; exists v'; split; [apply in_or_app; left; exact Hv'|exact R].
      + intros [v' [Hv' R]]; apply in_app_or in Hv' as [Hv'|[E'|[]]]; [exists v'; auto|].
        injection E' as _ Hh _; exfalso; apply Hne.
        destruct (shape_get r a key e Hs E) as [e2 [E2 Sh2]].
        unfold shape in Sh2; injection Sh2 as Hl2 _ _.
        rewrite (proj1 (proj1 (keys_ok_spec a) Hk _ _ E2)), Hl2, Hh; reflexivity. }
  assert (H0 : Inv [] (unlinked a)).
  { split; [apply shape_unlinked|]; intros key e E; unfold unlinked in E; rewrite get_map_filter in E.
    destruct (get key a) as [e0|]; [|discriminate]; injection E as <-; cbn [with_backs e_back e_out].
    unfold empty_backs; split; [apply Braun.balanced_of_list|split].
    - rewrite <- Braun.to_list_length, Braun.to_list_of_list, repeat_length; reflexivity.
    - intros j s Es; rewrite Braun.nth_to_list, Braun.to_list_of_list in Es by apply Braun.balanced_of_list.
      apply nth_error_In, repeat_spec in Es as ->; split; [apply links_wf_empty|].
      intros k p; split; [intros H; contradiction (link_mem_empty k p)|intros [v [[] _]]]. }
  destruct (Hstep [] (refs a) (unlinked a) eq_refl H0) as [Hs HI]; fold (relink a) in Hs, HI.
  split; [exact Hs|]; intros key e E.
  destruct (HI _ _ E) as [B [Sz M]]; split; [exact B|split; [exact Sz|]]; intros j s Es.
  destruct (M _ _ Es) as [W M']; split; [exact W|]; intros k p.
  rewrite M', (shape_refers _ a _ _ _ _ Hs); apply refs_refers, Hk.
Qed.

(** [linked a]: the back-links are correct (decided by recomputing them). *)
Definition backs_at (r : raw P) (key : positive) : braun links :=
  match get key r with Some e => e_back e | None => BE end.

Definition linked a : bool :=
  forallb (fun key e => Braun.eqb links_eqb (e_back e) (backs_at (relink a) key)) a.

Theorem linked_spec a : slots_ok a -> linked a = true <-> linked_prop a.
Proof.
  intros Ha; destruct (relink_spec a Ha) as [Hs Hl].
  assert (Hr : forall key e, get key a = Some e ->
               exists e', get key (relink a) = Some e' /\ shape e' = shape e /\ backs_ok a e').
  { intros key e E; destruct (shape_get a (relink a) key e (same_shape_sym _ _ Hs) E) as [e' [E' Sh]].
    exists e'; split; [exact E'|split; [exact Sh|]]; apply (shape_backs_ok (relink a) a e' Hs), (Hl _ _ E'). }
  assert (Heqb := Braun.eqb_spec links_eqb links_eqb_spec).
  unfold linked; rewrite forallb_spec; split.
  - intros H key e E; destruct (Hr _ _ E) as [e' [E' [Sh Ok]]].
    specialize (H _ _ E); rewrite Heqb in H; unfold backs_at in H; rewrite E' in H.
    unfold shape in Sh; injection Sh as Hl' _ Ho.
    destruct Ok as [B [Sz M]]; unfold backs_ok, backs_for; rewrite H; split; [exact B|split; [lia|]].
    intros j s Es; rewrite <- Hl'; apply M, Es.
  - intros H key e E; destruct (Hr _ _ E) as [e' [E' [Sh Ok]]].
    apply Heqb; unfold backs_at; rewrite E'.
    unfold shape in Sh; injection Sh as Hl' _ Ho.
    apply (backs_unique a e e' (H _ _ E) Ok); congruence.
Qed.

Theorem linked_relink a : slots_ok a -> linked (relink a) = true.
Proof.
  intros Ha; destruct (relink_spec a Ha) as [Hs Hl].
  apply linked_spec; [|exact Hl].
  destruct Ha as [Hk Hwf]; split; [rewrite (shape_keys_ok _ a Hs); exact Hk|].
  intros v h' n; rewrite !(shape_find _ a _ Hs), (shape_count _ a _ Hs); apply Hwf.
Qed.

Theorem canonical a b :
  normal a = true -> normal b = true -> linked a = true -> linked b = true ->
  (forall v, apply a v = apply b v) -> a = b.
Proof.
  intros Ha Hb La Lb Heq.
  pose proof (canonical_shape a b Ha Hb Heq) as Hs.
  apply linked_spec in La; [|apply normal_slots_ok, Ha].
  apply linked_spec in Lb; [|apply normal_slots_ok, Hb].
  apply extensionality; intro key; specialize (Hs key).
  destruct (get key a) as [ea|] eqn:Ea, (get key b) as [eb|] eqn:Eb; cbn in Hs;
    try discriminate; [|reflexivity].
  injection Hs as Hl Ht Ho.
  pose proof (backs_unique b ea eb (shape_backs_ok a b ea (canonical_shape a b Ha Hb Heq) (La _ _ Ea))
                (Lb _ _ Eb) Hl Ho) as Hbk.
  destruct ea, eb; cbn in *; subst; reflexivity.
Qed.

(** ** The strip step preserves the invariant *)

Lemma keys_ok_set_entry h s k bk a :
  Braun.balanced s -> keys_ok a = true -> keys_ok (set_entry h s k bk a) = true.
Proof.
  intros Hs Ha; apply keys_ok_spec; intros key e He.
  unfold set_entry in He; rewrite get_update in He.
  destruct (Pos.eqb_spec key (label_key h)) as [->|]; [|apply (proj1 (keys_ok_spec a) Ha _ _ He)].
  destruct (nontrivial_seq s k); [injection He as <-; split; [reflexivity|exact Hs]|discriminate].
Qed.

Lemma keys_ok_renumber h a : keys_ok a = true -> keys_ok (renumber h a) = true.
Proof.
  intros Ha; apply keys_ok_spec; intros key e He.
  unfold renumber in He; rewrite get_map_filter in He.
  destruct (get key a) as [e0|] eqn:E0; [|discriminate]; injection He as <-.
  destruct (proj1 (keys_ok_spec a) Ha _ _ E0) as [K B]; split; [exact K|apply Braun.balanced_map, B].
Qed.

Lemma keys_ok_strip_once h a : keys_ok a = true -> keys_ok (strip_once h a) = true.
Proof.
  intros Hk; apply keys_ok_renumber, keys_ok_set_entry; [|exact Hk].
  apply (proj1 (Braun.unsnoc_spec _ (keys_ok_balanced a h Hk))).
Qed.

Lemma strip_ok_false_strippable a Q h :
  pre_normal a Q -> strip_ok a h (fst (find a h)) = false -> strippable a h.
Proof.
  intros [Hk [Hnt [Hwf Hs]]] Hf.
  assert (Hn : ~ (last_target (fst (find a h)) = Some (Slot h 0) -> other_ref a h (fst (find a h)))).
  { rewrite <- (strip_ok_spec a h _ Hk), Hf; discriminate. }
  destruct (last_target (fst (find a h))) as [[h' [|n]|p]|] eqn:El;
    try (exfalso; apply Hn; intro H; discriminate).
  destruct (label_eq_dec h' h) as [->|Hne]; [|exfalso; apply Hn; intro H; injection H; congruence].
  repeat split; [exact El| |exact Hwf].
  intros v Hv; destruct (rvar_eq_dec v (mk_rvar h (pred (length (fst (find a h)))))) as [E|E];
    [exact E|].
  exfalso; apply Hn; intros _; exists v; auto.
Qed.

Lemma find_strip_once_nth h a v i t :
  keys_ok a = true ->
  nth_error (fst (find (strip_once h a) (v_label v))) i = Some t ->
  exists t0, nth_error (fst (find a (v_label v))) i = Some t0 /\ t = renumber_target h t0
             /\ (v_label v = h -> i < pred (length (fst (find a h)))).
Proof.
  intros Hk Ht; rewrite find_strip_once in Ht by exact Hk; cbn [fst] in Ht.
  rewrite nth_error_map in Ht.
  destruct (label_eqb_spec (v_label v) h) as [Hl|Hl].
  - destruct (Nat.lt_ge_cases i (pred (length (fst (find a h))))) as [Hi|Hi].
    + rewrite removelast_nth in Ht by exact Hi.
      rewrite Hl; destruct (nth_error (fst (find a h)) i) as [t0|]; [|discriminate].
      injection Ht as <-; exists t0; auto.
    + rewrite (proj2 (nth_error_None _ i)) in Ht by (rewrite length_removelast; exact Hi).
      discriminate.
  - destruct (nth_error (fst (find a (v_label v))) i) as [t0|]; [|discriminate].
    injection Ht as <-; exists t0; repeat split; auto; intro; contradiction.
Qed.

Theorem pre_normal_strip_once a Q h :
  pre_normal a Q -> Q h -> strippable a h -> pre_normal (strip_once h a) Q.
Proof.
  intros [Hk [Hnt [Hwf Hs]]] HQh Hst.
  pose proof Hst as [Hlast [Huniq _]].
  repeat split.
  - apply keys_ok_strip_once, Hk.
  - intros key e He; unfold strip_once, renumber in He.
    destruct (get_map_seq _ _ _ _ He) as [e0 [E0 [_ ->]]].
    destruct (get_set_entry _ _ _ _ _ _ _ E0) as [[_ [_ N]]|[_ E1]]; [exact N|apply (Hnt _ _ E1)].
  - intros v h' n Hn.
    destruct (find_strip_once_nth h a v (v_index v) _ Hk Hn) as [t0 [Ht0 [Heq Hlt]]].
    destruct t0 as [h0 n0|p]; cbn [renumber_target] in Heq; [|discriminate].
    pose proof (Hwf _ _ _ Ht0) as Hb.
    rewrite count_strip_once.
    destruct (label_eqb_spec h0 h) as [->|Hh]; injection Heq as -> ->.
    + rewrite label_eqb_refl.
      destruct n0 as [|n0]; [|cbn [pred]; lia].
      exfalso; specialize (Huniq _ Ht0).
      destruct v as [hv iv]; injection Huniq as -> ->; cbn in Hlt; specialize (Hlt eq_refl); lia.
    + rewrite (proj2 (label_eqb_neq h0 h) Hh); exact Hb.
  - intros h' HQ.
    assert (Hne : h' <> h) by (intro E; subst; contradiction).
    pose proof (keys_ok_strip_once h a Hk) as Hk'.
    apply (strip_ok_spec _ _ _ Hk'); intros Hl'.
    pose proof (Hs h' HQ) as Hs'; rewrite (strip_ok_spec _ _ _ Hk) in Hs'.
    assert (Ef : fst (find (strip_once h a) h') = map (renumber_target h) (fst (find a h'))).
    { rewrite find_strip_once by exact Hk; cbn [fst]; rewrite (proj2 (label_eqb_neq h' h) Hne); reflexivity. }
    rewrite Ef in Hl' |- *.
    unfold last_target in Hl'; rewrite length_map, nth_error_map in Hl'.
    destruct (nth_error (fst (find a h')) (pred (length (fst (find a h'))))) as [[h0 n0|p]|] eqn:El;
      cbn [option_map renumber_target] in Hl'; [|discriminate|discriminate].
    destruct (label_eqb_spec h0 h) as [->|Hh]; injection Hl' as E1 E2; [congruence|].
    subst h0 n0.
    destruct (Hs' El) as [w [Hw Hwne]].
    exists w; split; [|rewrite length_map; exact Hwne].
    fold (strip_once h a).
    destruct (label_eq_dec (v_label w) h) as [Hwl|Hwl].
    + assert (Hwi : v_index w < pred (length (fst (find a h)))).
      { assert (v_index w < length (fst (find a h)))
          by (rewrite <- Hwl; apply nth_error_Some; congruence).
        destruct (Nat.eq_dec (v_index w) (pred (length (fst (find a h))))) as [E|E]; [|lia].
        exfalso; rewrite Hwl, E in Hw.
        unfold last_target in Hlast; rewrite Hlast in Hw; injection Hw; congruence. }
      rewrite find_strip_once by exact Hk; cbn [fst]; rewrite Hwl, label_eqb_refl.
      rewrite nth_error_map, removelast_nth by exact Hwi.
      rewrite Hwl in Hw; rewrite Hw; cbn [option_map renumber_target].
      rewrite (proj2 (label_eqb_neq h' h) Hne); reflexivity.
    + rewrite find_strip_once by exact Hk; cbn [fst]; rewrite (proj2 (label_eqb_neq _ h) Hwl).
      rewrite nth_error_map, Hw; cbn [option_map renumber_target].
      rewrite (proj2 (label_eqb_neq h' h) Hne); reflexivity.
Qed.


(** ** Adding an input entry *)

Definition cons_entry h t a : raw P :=
  set_entry h (Braun.cons t (seq_of a h)) (count a h) (backs_of a h) a.

Lemma find_cons_entry h t a h' :
  find (cons_entry h t a) h'
  = if label_eqb h' h then (t :: fst (find a h), count a h) else find a h'.
Proof.
  unfold cons_entry; rewrite find_set_entry.
  destruct (label_eqb h' h); [rewrite Braun.to_list_cons, elems_seq_of|]; reflexivity.
 Qed.

Lemma count_cons_entry h t a h' : count (cons_entry h t a) h' = count a h'.
Proof.
  rewrite count_find at 1; rewrite find_cons_entry.
  destruct (label_eqb_spec h' h) as [->|]; rewrite ?count_find; reflexivity.
Qed.

Lemma resolve_cons_entry h t a t' : resolve (cons_entry h t a) t' = resolve a t'.
Proof. destruct t'; cbn [resolve]; rewrite ?count_cons_entry; reflexivity. Qed.

Theorem apply_cons_entry h t a v :
  apply (cons_entry h t a) v
  = if rvar_eqb v (mk_rvar h 0) then resolve a t else apply a (unshift_rvar (mk_rvar h 0) v).
Proof.
  unfold apply; rewrite !find_cons_entry, count_cons_entry.
  destruct v as [hv i]; unfold rvar_eqb, unshift_rvar; cbn [v_label v_index].
  rewrite (label_eqb_sym h hv).
  destruct (label_eqb_spec hv h) as [->|Hne]; cbn [andb fst snd].
  - destruct i as [|i]; cbn [Nat.eqb Nat.ltb Nat.leb nth_error]; [apply resolve_cons_entry|].
    replace (S i - 1) with i by lia; cbn [v_label v_index].
    destruct (nth_error (fst (find a h)) i); [apply resolve_cons_entry|].
    cbn [length]; do 2 f_equal; lia.
  - cbn [v_label v_index].
    destruct (nth_error (fst (find a hv)) i); [apply resolve_cons_entry|reflexivity].
Qed.

Theorem almost_normal_cons_entry h t a :
  normal a = true ->
  (forall h' n, t = Slot h' n -> n < count a h') ->
  almost_normal (cons_entry h t a) h.
Proof.
  intros Ha Ht.
  pose proof (normal_keys_ok a Ha) as Hk.
  pose proof (proj1 (normal_iff a h) Ha) as [[_ [Hnt [Hwf Hs]]] _].
  assert (Hk' : keys_ok (cons_entry h t a) = true) by (unfold cons_entry; apply keys_ok_set_entry; [apply Braun.balanced_cons, keys_ok_balanced, Hk|exact Hk]).
  repeat split.
  - exact Hk'.
  - intros key e He; unfold cons_entry in He.
    destruct (get_set_entry _ _ _ _ _ _ _ He) as [[_ [_ N]]|[_ E1]]; [exact N|apply (Hnt _ _ E1)].
  - intros v h' n Hn; rewrite count_cons_entry.
    rewrite find_cons_entry in Hn.
    destruct v as [hv i]; cbn [v_label v_index] in Hn.
    destruct (label_eqb_spec hv h) as [->|]; cbn [fst] in Hn.
    + destruct i as [|i]; cbn [nth_error] in Hn; [injection Hn as ->; apply Ht; reflexivity|].
      apply (Hwf (mk_rvar h i)), Hn.
    + apply (Hwf (mk_rvar hv i)), Hn.
  - intros h' Hne.
    apply (strip_ok_spec _ _ _ Hk'); intros Hl.
    pose proof (Hs h' Hne) as Hs'; rewrite (strip_ok_spec _ _ _ Hk) in Hs'.
    assert (Ef : fst (find (cons_entry h t a) h') = fst (find a h')).
    { rewrite find_cons_entry, (proj2 (label_eqb_neq h' h) Hne); reflexivity. }
    rewrite Ef in Hl |- *.
    destruct (Hs' Hl) as [w [Hw Hwne]].
    destruct (label_eq_dec (v_label w) h) as [Hwl|Hwl].
    + exists (mk_rvar h (S (v_index w))); split.
      * rewrite find_cons_entry; cbn [v_label v_index]; rewrite label_eqb_refl; cbn [fst nth_error].
        rewrite <- Hwl; exact Hw.
      * intro E; injection E as E1 _; congruence.
    + exists w; split; [|exact Hwne].
      rewrite find_cons_entry, (proj2 (label_eqb_neq _ h) Hwl); exact Hw.
Qed.

Fixpoint strip_loop (fuel : nat) h a : raw P :=
  match fuel with
  | 0 => a
  | S f => if strip_ok a h (fst (find a h)) then a else strip_loop f h (strip_once h a)
  end.

Theorem strip_loop_spec_gen fuel Q h a :
  pre_normal a Q -> Q h -> jlen a h < fuel ->
  pre_normal (strip_loop fuel h a) (fun l => Q l /\ l <> h)
  /\ (forall v, apply (strip_loop fuel h a) v = apply a v).
Proof.
  revert a; induction fuel as [|f IH]; intros a Ha HQh Hlen; [lia|].
  cbn [strip_loop].
  destruct (strip_ok a h (fst (find a h))) eqn:Hs.
  - split; [|reflexivity].
    destruct Ha as [Hk [Hnt [Hwf HS]]]; repeat split; auto.
    intros h' Hn; destruct (label_eq_dec h' h) as [->|Hne]; [exact Hs|].
    apply HS; intro HQ; apply Hn; split; assumption.
  - pose proof (strip_ok_false_strippable a Q h Ha Hs) as Hst.
    destruct (IH (strip_once h a)) as [Hn Happ].
    + apply pre_normal_strip_once; assumption.
    + exact HQh.
    + rewrite ?jlen_find in *; rewrite find_strip_once, label_eqb_refl by (destruct Ha as [Hk _]; exact Hk); cbn [fst].
      rewrite length_map, length_removelast.
      destruct Hst as [Hl _]; unfold last_target in Hl.
      assert (0 < length (fst (find a h))) by (destruct (fst (find a h)); [discriminate|cbn; lia]).
      lia.
    + split; [exact Hn|]; intro v; rewrite Happ; apply apply_strip_once; [destruct Ha as [Hk _]; exact Hk|exact Hst].
Qed.

Lemma normal_of_pre_normal a Q : pre_normal a Q -> (forall l, ~ Q l) -> normal a = true.
Proof.
  intros [Hk [Hnt [Hwf Hs]]] HQ.
  apply (normal_iff a None); split; [repeat split; auto|].
  apply Hs, HQ.
Qed.

Theorem strip_loop_spec fuel h a :
  almost_normal a h -> jlen a h < fuel ->
  normal (strip_loop fuel h a) = true /\ (forall v, apply (strip_loop fuel h a) v = apply a v).
Proof.
  intros Ha Hlen.
  destruct (strip_loop_spec_gen fuel _ h a Ha eq_refl Hlen) as [Hn Happ].
  split; [|exact Happ].
  apply (normal_of_pre_normal _ _ Hn); intros l [-> Hne]; apply Hne; reflexivity.
Qed.

(** ** Adding an input entry, keeping the back-links

    [push_inner h t a] adds [h ↦ t] in front of [a] and records the new
    reference in the back-links ([cons_linked]).  When [a] is normal, at
    most one strip is needed afterwards, and only when [h] had no inputs:
    the new input then refers to [h]'s innermost slot and nothing else
    does, which that slot's back-links show in O(log n) ([strip_check]).
    The strip ([strip_sole]) renumbers the inputs that refer to [h]'s other
    slots, which it finds through their back-links. *)

Definition link_target h t (k : positive) (p : nat) a : raw P :=
  match t with Slot g j => add_link g j k p a | Bind _ => a end.

Definition cons_linked h t a : raw P :=
  link_target h t (label_key h) (jlen a h) (cons_entry h t a).

Definition link_single (k : positive) : links := link_add k 0 Empty.

Definition strip_check h a : bool :=
  match Braun.nth 0 (backs_of a h) with
  | Some s => links_eqb s (link_single (label_key h))
  | None => false
  end.

(** Overwrite the target at position [p] from the back of the label with
    key [k]. *)
Definition retarget (k : positive) (p : nat) (t : target P) a : raw P :=
  update k (option_map (fun e =>
    mk_entry (e_label e) (Braun.update (Braun.size (e_tree e) - S p) (fun _ => t) (e_tree e))
             (e_out e) (e_back e))) a.

Definition retarget_all h (L : list (positive * nat * nat)) a : raw P :=
  fold_left (fun r x => match x with (k, p, j) => retarget k p (Slot h j) r end) L a.

(** The references recorded in back-links: (key, position, slot). *)
Definition link_list (bk : braun links) : list (positive * nat * nat) :=
  flat_map (fun js => match js with
                      | (j, s) => flat_map (fun kps => match kps with
                                                       | (k, ps) => List.map (fun qx => (k, key_pos (fst qx), j))
                                                                             (elements ps)
                                                       end) (elements s)
                      end)
           (combine (List.seq 0 (Braun.size bk)) (Braun.to_list bk)).

(** Strip [h]'s only input, which refers to [h]'s innermost slot and is the
    only reference to it. *)
Definition strip_sole h a : raw P :=
  let bk := Braun.tail (backs_of a h) in
  retarget_all h (link_list bk) (set_entry h BE (pred (count a h)) bk a).

Definition push_inner h t a : raw P :=
  let a1 := cons_linked h t a in
  if strip_check h a1 then strip_sole h a1 else a1.

(** *** The new reference *)

Lemma refers_cons_entry h t a g j k p :
  keys_ok a = true ->
  refers (cons_entry h t a) g j k p
  <-> refers a g j k p \/ (k = label_key h /\ p = jlen a h /\ t = Slot g j).
Proof.
  intros Hk; unfold refers, cons_entry, set_entry; rewrite get_update.
  destruct (Pos.eqb_spec k (label_key h)) as [->|Hne].
  - rewrite (nontrivial_seq_elems _ (count a h)), Braun.to_list_cons; cbn [nontrivial].
    set (sq := seq_of a h).
    transitivity (p < S (Braun.size sq)
                  /\ nth_error (t :: Braun.to_list sq) (S (Braun.size sq) - S p) = Some (Slot g j)).
    { unfold e_targets; split.
      - intros [e [[= <-] H]]; cbn [e_tree] in H; rewrite Braun.size_cons, Braun.to_list_cons in H; exact H.
      - intros H; eexists; split; [reflexivity|]; cbn [e_tree].
        rewrite Braun.size_cons, Braun.to_list_cons; exact H. }
    assert (Ha : (exists e, get (label_key h) a = Some e /\ p < Braun.size (e_tree e)
                            /\ nth_error (e_targets e) (Braun.size (e_tree e) - S p) = Some (Slot g j))
                 <-> p < Braun.size sq /\ nth_error (Braun.to_list sq) (Braun.size sq - S p) = Some (Slot g j)).
    { unfold sq, seq_of, e_targets; destruct (get (label_key h) a) as [e0|]; split.
      - intros [e [[= <-] H]]; exact H.
      - intros H; eexists; split; [reflexivity|exact H].
      - intros [e [[=] _]].
      - intros [H _]; cbn in H; lia. }
    rewrite Ha; unfold jlen; fold sq; split.
    + intros [Hp Hn]; destruct (Nat.eq_dec p (Braun.size sq)) as [->|Hp'].
      * right; rewrite Nat.sub_diag in Hn; cbn in Hn; injection Hn as ->; auto.
      * left; split; [lia|].
        replace (S (Braun.size sq) - S p) with (S (Braun.size sq - S p)) in Hn by lia; exact Hn.
    + intros [[Hp Hn]|[_ [-> ->]]]; (split; [lia|]).
      * replace (S (Braun.size sq) - S p) with (S (Braun.size sq - S p)) by lia; exact Hn.
      * rewrite Nat.sub_diag; reflexivity.
  - split; [intros H; left; exact H|intros [H|[E _]]; [exact H|contradiction]].
Qed.

Lemma backs_for_add_link (R : option label -> nat -> positive -> nat -> Prop) r h j k p key e' :
  keys_ok r = true ->
  (forall key e, get key r = Some e -> backs_for R e) ->
  (forall e, get (label_key h) r = Some e -> j < e_out e) ->
  get key (add_link h j k p r) = Some e' ->
  backs_for (fun g j' k' p' => R g j' k' p' \/ (g = h /\ j' = j /\ k' = k /\ p' = p)) e'.
Proof.
  intros Hk HR Hj E; unfold add_link in E; rewrite get_update in E.
  destruct (Pos.eqb_spec key (label_key h)) as [->|Hne].
  - destruct (get (label_key h) r) as [e0|] eqn:E0; [|discriminate].
    injection E as <-; destruct (HR _ _ E0) as [B [Sz M]].
    pose proof (keys_ok_label r h e0 Hk E0) as Lh; specialize (Hj _ eq_refl).
    unfold backs_for, with_backs; cbn [e_back e_out e_label].
    split; [apply Braun.balanced_update, B|split; [rewrite Braun.size_update; exact Sz|]].
    intros j' s Es; rewrite Braun.nth_update in Es.
    destruct (Nat.eqb_spec j j') as [<-|Hjj].
    + destruct (Braun.nth j (e_back e0)) as [s0|] eqn:Es0;
        [|apply nth_none_size in Es0; [lia|exact B]].
      injection Es as <-; destruct (M _ _ Es0) as [W M']; split; [apply links_wf_add, W|].
      intros k' p'; rewrite link_mem_add, M', Lh; intuition congruence.
    + destruct (M _ _ Es) as [W M']; split; [exact W|].
      intros k' p'; rewrite M'; intuition congruence.
  - destruct (HR _ _ E) as [B [Sz M]]; split; [exact B|split; [exact Sz|]]; intros j' s Es.
    destruct (M _ _ Es) as [W M']; split; [exact W|]; intros k' p'; rewrite M'.
    split; [intros H; left; exact H|intros [H|[Hl _]]; [exact H|]].
    exfalso; apply Hne; rewrite <- Hl; apply (proj1 (proj1 (keys_ok_spec r) Hk _ _ E)).
Qed.

Lemma shape_link_target h t k p a : same_shape (link_target h t k p a) a.
Proof. destruct t; [apply shape_add_link|intro; reflexivity]. Qed.

Theorem linked_cons h t a :
  keys_ok a = true -> linked_prop a -> (forall g n, t = Slot g n -> n < count a g) ->
  same_shape (cons_linked h t a) (cons_entry h t a) /\ linked_prop (cons_linked h t a).
Proof.
  intros Hk La Ht; split; [apply shape_link_target|].
  set (c := cons_entry h t a).
  assert (Hkc : keys_ok c = true)
    by (apply keys_ok_set_entry; [apply Braun.balanced_cons, keys_ok_balanced, Hk|exact Hk]).
  assert (Hc : forall key e, get key c = Some e -> backs_for (refers a) e).
  { intros key e E; unfold c, cons_entry, set_entry in E; rewrite get_update in E.
    destruct (Pos.eqb_spec key (label_key h)) as [->|]; [|apply (La _ _ E)].
    rewrite nontrivial_seq_elems, Braun.to_list_cons in E; cbn [nontrivial] in E.
    injection E as <-; unfold backs_of, count.
    destruct (get (label_key h) a) as [e0|] eqn:E0.
    - pose proof (keys_ok_label a h e0 Hk E0) as Lh.
      destruct (La _ _ E0) as [B [Sz M]]; split; [exact B|split; [exact Sz|]].
      intros j s Es; cbn [e_label]; rewrite <- Lh; apply M, Es.
    - split; [exact I|split; [reflexivity|]]; intros j s Es; discriminate. }
  intros key e E; unfold cons_linked, link_target in E; fold c in E.
  destruct t as [g n|q].
  - apply (backs_for_add_link (refers a) c g n (label_key h) (jlen a h) key e Hkc Hc) in E.
    + refine (backs_for_iff _ _ e _ E).
      intros g' j' k' p'; unfold cons_linked, link_target; fold c.
      rewrite (shape_refers _ c _ _ _ _ (shape_add_link _ _ _ _ _)).
      unfold c; rewrite (refers_cons_entry h _ a _ _ _ _ Hk); intuition congruence.
    + intros e0 E0; specialize (Ht g n eq_refl).
      assert (count c g = e_out e0) by (unfold count; rewrite E0; reflexivity).
      unfold c in H; rewrite count_cons_entry in H; lia.
  - refine (backs_for_iff (refers a) _ e _ (Hc _ _ E)).
    intros; unfold cons_linked, link_target; rewrite (refers_cons_entry h _ a _ _ _ _ Hk).
    intuition discriminate.
Qed.

(** *** Deciding whether to strip *)

Lemma refers_rvar a g j k p :
  keys_ok a = true ->
  refers a g j k p
  <-> exists v, nth_error (fst (find a (v_label v))) (v_index v) = Some (Slot g j)
                /\ k = label_key (v_label v) /\ p = jlen a (v_label v) - S (v_index v).
Proof.
  intros Hk; rewrite <- (refs_refers a g j k p Hk); split; intros [v [H R]]; exists v;
    split; auto; apply (In_refs_keys a v g j Hk); exact H.
Qed.

Lemma strip_check_true h a :
  keys_ok a = true -> linked_prop a -> strip_check h a = true ->
  forall k p, refers a h 0 k p <-> k = label_key h /\ p = 0.
Proof.
  intros Hk La H k p; unfold strip_check, backs_of in H.
  destruct (get (label_key h) a) as [e|] eqn:E; [|discriminate].
  destruct (Braun.nth 0 (e_back e)) as [s|] eqn:Es; [|discriminate].
  apply links_eqb_spec in H; subst s.
  destruct (La _ _ E) as [_ [_ M]]; destruct (M _ _ Es) as [_ M'].
  unfold link_single in M'; rewrite (keys_ok_label a h e Hk E) in M'; rewrite <- M', link_mem_add.
  split; [intros [H|H]; [exact H|contradiction (link_mem_empty k p)]|intros H; left; exact H].
Qed.

Lemma strip_check_false h a :
  slots_ok a -> linked_prop a -> strip_check h a = false -> strip_ok a h (fst (find a h)) = true.
Proof.
  intros [Hk Hwf] La H.
  destruct (strip_ok a h (fst (find a h))) eqn:Es; [reflexivity|exfalso].
  set (ts := fst (find a h)) in *.
  assert (Hl : last_target ts = Some (Slot h 0)).
  { unfold strip_ok in Es; destruct (last_target ts) as [[h' [|n]|q]|]; try discriminate.
    destruct (label_eqb_spec h' h) as [E|]; [rewrite E; reflexivity|discriminate]. }
  assert (Hno : ~ other_ref a h ts)
    by (intro Ho; rewrite (proj2 (strip_ok_spec a h ts Hk) (fun _ => Ho)) in Es; discriminate).
  (* the last input of [h] refers to slot 0, and is the only one *)
  unfold last_target in Hl.
  assert (Hin : refers a h 0 (label_key h) 0).
  { apply refers_rvar; [exact Hk|]; exists (mk_rvar h (pred (length ts))); cbn [v_label v_index].
    split; [exact Hl|split; [reflexivity|]].
    rewrite jlen_find; fold ts.
    assert (0 < length ts) by (destruct ts; [discriminate|cbn; lia]); lia. }
  assert (Hone : forall k p, refers a h 0 k p <-> k = label_key h /\ p = 0).
  { intros k p; split; [|intros [-> ->]; exact Hin].
    intros R; apply (refers_rvar a h 0 k p Hk) in R as [v [Hv [-> ->]]].
    destruct (rvar_eqb_spec v (mk_rvar h (pred (length ts)))) as [->|Hne];
      [|exfalso; apply Hno; exists v; auto].
    cbn [v_label v_index]; rewrite jlen_find; fold ts.
    assert (0 < length ts) by (destruct ts; [discriminate|cbn; lia]); split; [reflexivity|lia]. }
  (* so the slot's back-links are exactly that input *)
  apply refers_rvar in Hin as [v0 [Hv0 _]]; [|exact Hk].
  pose proof (Hwf _ _ _ Hv0) as Hc0.
  unfold strip_check, backs_of in H; unfold count in Hc0.
  destruct (get (label_key h) a) as [e|] eqn:E; [|lia].
  destruct (La _ _ E) as [B [Sz M]].
  destruct (Braun.nth 0 (e_back e)) as [s|] eqn:Ens; [|apply nth_none_size in Ens; [lia|exact B]].
  destruct (M _ _ Ens) as [W M'].
  assert (s = link_single (label_key h)).
  { apply links_ext; [exact W|apply links_wf_add, links_wf_empty|].
    intros k p; rewrite M', (keys_ok_label a h e Hk E), Hone; unfold link_single.
    rewrite link_mem_add; split; [intros H'; left; exact H'|intros [H'|H']; [exact H'|]].
    contradiction (link_mem_empty k p). }
  subst s; rewrite (proj2 (links_eqb_spec _ _) eq_refl) in H; discriminate.
Qed.

(** *** Retargeting *)

Definition rlookup (L : list (positive * nat * nat)) (k : positive) (p : nat) : option nat :=
  match List.find (fun x => match x with (k', p', _) => Pos.eqb k' k && Nat.eqb p' p end) L with
  | Some (_, _, j) => Some j
  | None => None
  end.

Lemma rlookup_some L k p j : rlookup L k p = Some j -> In (k, p, j) L.
Proof.
  unfold rlookup; destruct (List.find _ L) as [[[k' p'] j']|] eqn:E; [|discriminate].
  intros [= <-]; apply find_some in E as [Hin Hm].
  apply andb_true_iff in Hm as [H1 H2]; apply Pos.eqb_eq in H1; apply Nat.eqb_eq in H2; subst; exact Hin.
Qed.

Lemma rlookup_none L k p j : rlookup L k p = None -> ~ In (k, p, j) L.
Proof.
  unfold rlookup; destruct (List.find _ L) as [[[k' p'] j']|] eqn:E; [discriminate|].
  intros _ Hin; apply (find_none _ _ E) in Hin; rewrite !Pos.eqb_refl, Nat.eqb_refl in Hin; discriminate.
Qed.

Lemma rlookup_cons x L k p :
  rlookup (x :: L) k p
  = match x with (k', p', j) => if Pos.eqb k' k && Nat.eqb p' p then Some j else rlookup L k p end.
Proof. destruct x as [[k' p'] j]; unfold rlookup; cbn; destruct (_ && _); reflexivity. Qed.

Definition rfunctional (L : list (positive * nat * nat)) : Prop :=
  forall k p j j', In (k, p, j) L -> In (k, p, j') L -> j = j'.

Lemma keys_ok_retarget k p t r : keys_ok r = true -> keys_ok (retarget k p t r) = true.
Proof.
  intros Hk; apply keys_ok_spec; intros key e E; unfold retarget in E; rewrite get_update in E.
  destruct (Pos.eqb_spec key k) as [->|]; [|apply (proj1 (keys_ok_spec r) Hk _ _ E)].
  destruct (get k r) as [e0|] eqn:E0; [|discriminate]; injection E as <-; cbn [e_label e_tree].
  destruct (proj1 (keys_ok_spec r) Hk _ _ E0) as [K B]; split; [exact K|apply Braun.balanced_update, B].
Qed.

Lemma keys_ok_retarget_all h L r : keys_ok r = true -> keys_ok (retarget_all h L r) = true.
Proof.
  revert r; induction L as [|[[k p] j] L IH]; intros r Hk; [exact Hk|].
  apply IH, keys_ok_retarget, Hk.
Qed.

Lemma retarget_all_spec h L r key :
  keys_ok r = true -> rfunctional L ->
  (forall k p j, In (k, p, j) L -> exists e, get k r = Some e /\ p < Braun.size (e_tree e)) ->
  match get key (retarget_all h L r), get key r with
  | Some e', Some e =>
      e_label e' = e_label e /\ e_out e' = e_out e /\ e_back e' = e_back e
      /\ Braun.size (e_tree e') = Braun.size (e_tree e)
      /\ (forall z, In z (Braun.to_list (e_tree e')) ->
                    In z (Braun.to_list (e_tree e)) \/ exists j, z = Slot h j)
      /\ forall i, i < Braun.size (e_tree e) ->
           Braun.nth i (e_tree e')
           = match rlookup L key (Braun.size (e_tree e) - S i) with
             | Some j => Some (Slot h j)
             | None => Braun.nth i (e_tree e)
             end
  | None, None => True
  | _, _ => False
  end.
Proof.
  revert r; induction L as [|x L IH]; intros r Hk Hf Hv; cbn [retarget_all fold_left].
  - destruct (get key r) as [e|]; [|exact I].
    repeat split; auto; intros i _; reflexivity.
  - destruct x as [[kx px] jx]; fold (retarget_all h L (retarget kx px (Slot h jx) r)).
    assert (Hf' : rfunctional L) by (intros k p j j' H1 H2; apply (Hf k p); right; assumption).
    assert (Hv' : forall k p j, In (k, p, j) L ->
                  exists e, get k (retarget kx px (Slot h jx) r) = Some e /\ p < Braun.size (e_tree e)).
    { intros k p j Hin; destruct (Hv k p j (or_intror Hin)) as [e [E Hp]].
      unfold retarget; rewrite get_update; destruct (Pos.eqb_spec k kx) as [->|].
      - rewrite E; eexists; split; [reflexivity|]; cbn [e_tree]; rewrite Braun.size_update; exact Hp.
      - exists e; auto. }
    specialize (IH _ (keys_ok_retarget _ _ _ _ Hk) Hf' Hv').
    assert (G : get key (retarget kx px (Slot h jx) r)
                = if Pos.eqb key kx
                  then option_map (fun e => mk_entry (e_label e)
                                              (Braun.update (Braun.size (e_tree e) - S px)
                                                 (fun _ => Slot h jx) (e_tree e))
                                              (e_out e) (e_back e)) (get kx r)
                  else get key r)
      by (unfold retarget; rewrite get_update; reflexivity).
    rewrite G in IH; clear G.
    destruct (Pos.eqb_spec key kx) as [->|Hne].
    + destruct (get kx r) as [e|] eqn:E; cbn [option_map] in IH;
        [|destruct (get kx (retarget_all _ _ _)); [contradiction|exact I]].
      destruct (get kx (retarget_all h L _)) as [e'|]; [|contradiction].
      cbn [e_label e_out e_back e_tree] in IH; rewrite Braun.size_update in IH.
      destruct IH as [Hl [Ho [Hb [Hs [Hin Hn]]]]].
      split; [exact Hl|split; [exact Ho|split; [exact Hb|split; [exact Hs|split]]]].
      { intros z Hz; destruct (Hin z Hz) as [Hz'|Hz']; [|right; exact Hz'].
        apply Braun.in_update in Hz' as [Hz'|[y [_ ->]]]; [left; exact Hz'|right; eexists; reflexivity]. }
      intros i Hi; rewrite Hn by exact Hi; rewrite rlookup_cons, Pos.eqb_refl; cbn [andb].
      rewrite Braun.nth_update.
      destruct (Nat.eqb_spec px (Braun.size (e_tree e) - S i)) as [->|Hp].
      * replace (Braun.size (e_tree e) - S (Braun.size (e_tree e) - S i)) with i by lia.
        rewrite Nat.eqb_refl.
        destruct (rlookup L kx _) as [j|] eqn:R.
        -- f_equal; f_equal; apply (Hf kx (Braun.size (e_tree e) - S i) j jx);
             [right; apply rlookup_some, R|left; reflexivity].
        -- destruct (Braun.nth i (e_tree e)) eqn:N; [reflexivity|].
           apply nth_none_size in N; [lia|apply (proj2 (proj1 (keys_ok_spec r) Hk _ _ E))].
      * destruct (rlookup L kx _); [reflexivity|].
        destruct (Hv kx px jx (or_introl eq_refl)) as [e0 [E0 Hp0]]; rewrite E in E0; injection E0 as <-.
        destruct (Nat.eqb_spec (Braun.size (e_tree e) - S px) i); [lia|reflexivity].
    + destruct (get key r) as [e|]; [|exact IH].
      destruct (get key (retarget_all h L _)) as [e'|]; [|contradiction].
      destruct IH as [Hl [Ho [Hb [Hs [Hin Hn]]]]].
      repeat (split; [assumption|]); intros i Hi; rewrite Hn by exact Hi.
      rewrite rlookup_cons; destruct (Pos.eqb_spec kx key); [congruence|reflexivity].
Qed.

Lemma strip_check_true_strip_ok h a :
  keys_ok a = true -> linked_prop a -> strip_check h a = true ->
  strip_ok a h (fst (find a h)) = false.
Proof.
  intros Hk La C; pose proof (strip_check_true h a Hk La C) as H0.
  destruct (proj2 (H0 (label_key h) 0) (conj eq_refl eq_refl)) as [e [E [Hp Hn]]].
  pose proof (keys_ok_label a h e Hk E) as Lh.
  set (ts := fst (find a h)).
  assert (Ets : ts = e_targets e) by (unfold ts, find; rewrite E; reflexivity).
  assert (Hl : last_target ts = Some (Slot h 0)).
  { unfold last_target; rewrite Ets; unfold e_targets; rewrite Braun.to_list_length.
    replace (pred (Braun.size (e_tree e))) with (Braun.size (e_tree e) - 1) by lia; exact Hn. }
  destruct (strip_ok a h ts) eqn:Es; [exfalso|reflexivity].
  rewrite (strip_ok_spec a h ts Hk) in Es; destruct (Es Hl) as [v [Hv Hne]].
  assert (R : refers a h 0 (label_key (v_label v)) (jlen a (v_label v) - S (v_index v)))
    by (apply refers_rvar; [exact Hk|exists v; auto]).
  apply H0 in R as [Rk Rp]; apply label_key_inj in Rk.
  apply Hne; destruct v as [hv i]; cbn [v_label v_index] in *; subst hv.
  rewrite jlen_find in Rp; fold ts in Rp.
  assert (i < length ts) by (apply nth_error_Some; fold ts in Hv; congruence).
  f_equal; lia.
Qed.

Lemma in_combine_seq {A} (xs : list A) s j x :
  In (j, x) (combine (List.seq s (length xs)) xs) <-> s <= j /\ nth_error xs (j - s) = Some x.
Proof.
  revert s; induction xs as [|y ys IH]; intros s; cbn [length List.seq combine In].
  - split; [intros []|intros [_ H]; rewrite nth_error_nil in H; discriminate].
  - rewrite IH; split.
    + intros [[= -> ->]|[Hs Hn]]; [rewrite Nat.sub_diag; split; [lia|reflexivity]|].
      split; [lia|]; replace (j - s) with (S (j - S s)) by lia; exact Hn.
    + intros [Hs Hn]; destruct (Nat.eq_dec j s) as [->|Hne].
      * rewrite Nat.sub_diag in Hn; cbn in Hn; injection Hn as ->; left; reflexivity.
      * right; split; [lia|]; replace (j - s) with (S (j - S s)) in Hn by lia; exact Hn.
Qed.

Lemma in_link_list bk k p j :
  Braun.balanced bk ->
  In (k, p, j) (link_list bk) <-> exists s, Braun.nth j bk = Some s /\ link_mem k p s.
Proof.
  intros Hb; unfold link_list; rewrite in_flat_map.
  rewrite <- (Braun.to_list_length bk).
  split.
  - intros [[j' s] [Hin H]]; apply in_flat_map in H as [[k' ps] [Hin2 H]].
    apply in_map_iff in H as [[q []] [Heq Hin3]]; cbn [fst] in Heq; injection Heq as Hk' Hp Hj.
    subst k' j' p.
    apply in_combine_seq in Hin as [_ Hin]; rewrite Nat.sub_0_r in Hin.
    exists s; split; [rewrite Braun.nth_to_list by exact Hb; exact Hin|].
    exists ps; split; [apply In_elements, Hin2|]; rewrite pos_key_pos; apply In_elements, Hin3.
  - intros [s [Hs [ps [Hps Hq]]]].
    exists (j, s); split.
    + apply in_combine_seq; rewrite Nat.sub_0_r, <- Braun.nth_to_list by exact Hb; split; [lia|exact Hs].
    + apply in_flat_map; exists (k, ps); split; [apply In_elements, Hps|].
      apply in_map_iff; exists (pos_key p, tt); split; [cbn [fst]; rewrite key_pos_key; reflexivity|].
      apply In_elements, Hq.
Qed.

(** What stripping the sole input does to references. *)
Lemma refers_strip_once h a g j k p :
  keys_ok a = true -> fst (find a h) = [Slot h 0] ->
  (forall k p, refers a h 0 k p <-> k = label_key h /\ p = 0) ->
  refers (strip_once h a) g j k p
  <-> (g = h /\ refers a h (S j) k p) \/ (g <> h /\ refers a g j k p).
Proof.
  intros Hk Hf H0.
  assert (Hkh : forall j' p', ~ refers a h (S j') (label_key h) p').
  { intros j' p' [e [E [Hp Hn]]].
    unfold find in Hf; rewrite E in Hf; cbn [fst] in Hf.
    unfold e_targets in Hn, Hf; rewrite Hf in Hn.
    assert (Hs : Braun.size (e_tree e) = 1) by (rewrite <- Braun.to_list_length, Hf; reflexivity).
    rewrite Hs in Hn; replace (1 - S p') with 0 in Hn by lia; discriminate. }
  assert (Hkg : forall g' j' p', g' <> h -> ~ refers a g' j' (label_key h) p').
  { intros g' j' p' Hne [e [E [Hp Hn]]].
    unfold find in Hf; rewrite E in Hf; cbn [fst] in Hf.
    unfold e_targets in Hn, Hf; rewrite Hf in Hn.
    assert (Hs : Braun.size (e_tree e) = 1) by (rewrite <- Braun.to_list_length, Hf; reflexivity).
    rewrite Hs in Hn; replace (1 - S p') with 0 in Hn by lia; injection Hn; congruence. }
  unfold refers at 1; unfold strip_once, renumber; rewrite get_map_filter.
  unfold set_entry; rewrite get_update.
  destruct (Pos.eqb_spec k (label_key h)) as [->|Hne].
  - assert (Hu : Braun.to_list (Braun.unsnoc (seq_of a h)) = []).
    { rewrite (proj2 (Braun.unsnoc_spec _ (keys_ok_balanced a h Hk))), elems_seq_of, Hf; reflexivity. }
    rewrite (nontrivial_seq_elems _ (pred (count a h))), Hu.
    destruct (nontrivial [] (pred (count a h))); cbn [option_map].
    + split.
      * intros [e [[= <-] [Hp _]]]; cbn [e_tree] in Hp; rewrite Braun.size_map, <- Braun.to_list_length, Hu in Hp.
        cbn in Hp; lia.
      * intros [[-> R]|[Hne R]]; [contradiction (Hkh j p R)|contradiction (Hkg g j p Hne R)].
    + split; [intros [e [[=] _]]|].
      intros [[-> R]|[Hne R]]; [contradiction (Hkh j p R)|contradiction (Hkg g j p Hne R)].
  - unfold refers; destruct (get k a) as [e|] eqn:E; cbn [option_map].
    2: { split; [intros [e' [[=] _]]|intros [[_ [e' [[=] _]]]|[_ [e' [[=] _]]]]]. }
    assert (Hnot0 : forall i, i < Braun.size (e_tree e) ->
                    nth_error (e_targets e) i <> Some (Slot h 0)).
    { intros i Hi Hn; destruct (proj1 (H0 k (Braun.size (e_tree e) - S i))) as [Hk' _]; [|contradiction].
      exists e; split; [exact E|split; [lia|]].
      replace (Braun.size (e_tree e) - S (Braun.size (e_tree e) - S i)) with i by lia; exact Hn. }
    split.
    + intros [e' [[= <-] [Hp Hn]]]; unfold e_targets in Hn; cbn [e_tree] in Hp, Hn.
      rewrite Braun.size_map, Braun.to_list_map, nth_error_map in Hn; rewrite Braun.size_map in Hp.
      fold (e_targets e) in Hn.
      destruct (nth_error (e_targets e) (Braun.size (e_tree e) - S p)) as [[g' n|q]|] eqn:T;
        cbn [option_map renumber_target] in Hn; [|discriminate|discriminate].
      destruct (label_eqb_spec g' h) as [->|Hgh]; [injection Hn as <- <-|injection Hn as -> <-].
      * destruct n as [|n]; [exfalso; apply (Hnot0 (Braun.size (e_tree e) - S p) ltac:(lia) T)|].
        left; split; [reflexivity|]; exists e; auto.
      * right; split; [exact Hgh|]; exists e; auto.
    + intros [[-> [e' [E' [Hp Hn]]]]|[Hgh [e' [E' [Hp Hn]]]]]; injection E' as <-;
        (eexists; split; [reflexivity|]); unfold e_targets; cbn [e_tree];
        rewrite Braun.size_map, Braun.to_list_map, nth_error_map;
        fold (e_targets e); rewrite Hn; (split; [exact Hp|]); cbn [option_map renumber_target].
      * rewrite label_eqb_refl; reflexivity.
      * rewrite (proj2 (label_eqb_neq g h) Hgh); reflexivity.
Qed.

Theorem strip_sole_spec h a :
  slots_ok a -> linked_prop a -> fst (find a h) = [Slot h 0] ->
  (forall k p, refers a h 0 k p <-> k = label_key h /\ p = 0) ->
  same_shape (strip_sole h a) (strip_once h a) /\ linked_prop (strip_sole h a).
Proof.
  intros [Hk Hwf] La Hf H0.
  destruct (get (label_key h) a) as [eh|] eqn:Eh;
    [|unfold find in Hf; rewrite Eh in Hf; discriminate].
  pose proof (keys_ok_label a h eh Hk Eh) as Lh.
  destruct (La _ _ Eh) as [Bh [Szh Mh]].
  assert (Hth : e_targets eh = [Slot h 0]) by (unfold find in Hf; rewrite Eh in Hf; exact Hf).
  set (bk := Braun.tail (e_back eh)).
  destruct (Braun.tail_spec _ Bh) as [Bbk Lbk]; fold bk in Bbk, Lbk.
  assert (Hnb : forall j, Braun.nth j bk = Braun.nth (S j) (e_back eh)).
  { intro j; rewrite !Braun.nth_to_list by assumption; rewrite Lbk.
    destruct (Braun.to_list (e_back eh)); [rewrite !nth_error_nil|]; reflexivity. }
  set (L := link_list bk).
  assert (HL : forall k p j, In (k, p, j) L <-> refers a h (S j) k p).
  { intros k p j; unfold L; rewrite (in_link_list bk k p j Bbk), Hnb; split.
    - intros [s [Es Hm]]; rewrite <- Lh; apply (proj2 (Mh _ _ Es)), Hm.
    - intros R; destruct (Braun.nth (S j) (e_back eh)) as [s|] eqn:Es.
      + exists s; split; [reflexivity|]; rewrite <- Lh in R; apply (proj2 (Mh _ _ Es)), R.
      + exfalso; apply nth_none_size in Es; [|exact Bh].
        destruct R as [e [E [Hp Hn]]].
        pose proof (Hwf (mk_rvar (e_label e) (Braun.size (e_tree e) - S p)) h (S j)) as W.
        unfold count in W; rewrite Eh in W; cbn [v_label v_index] in W.
        unfold find in W; rewrite <- (proj1 (proj1 (keys_ok_spec a) Hk _ _ E)), E in W.
        specialize (W Hn); lia. }
  assert (Hfun : rfunctional L).
  { intros k p j j' H1 H2; apply HL in H1 as [e1 [E1 [_ N1]]]; apply HL in H2 as [e2 [E2 [_ N2]]].
    rewrite E1 in E2; injection E2 as <-; rewrite N1 in N2; injection N2; lia. }
  assert (Hnkh : forall k p j, In (k, p, j) L -> k <> label_key h).
  { intros k p j Hin ->; apply HL in Hin as [e [E [Hp Hn]]]; rewrite Eh in E; injection E as <-.
    rewrite Hth in Hn; unfold e_targets in Hth.
    assert (Braun.size (e_tree eh) = 1) by (rewrite <- Braun.to_list_length, Hth; reflexivity).
    rewrite H in Hn; replace (1 - S p) with 0 in Hn by lia; discriminate. }
  set (r := set_entry h BE (pred (count a h)) bk a).
  assert (Hr : forall k, k <> label_key h -> get k r = get k a)
    by (intros k Hne; unfold r, set_entry; rewrite get_update, (proj2 (Pos.eqb_neq _ _) Hne); reflexivity).
  assert (Hkr : keys_ok r = true) by (apply keys_ok_set_entry; [exact I|exact Hk]).
  assert (Hval : forall k p j, In (k, p, j) L -> exists e, get k r = Some e /\ p < Braun.size (e_tree e)).
  { intros k p j Hin; rewrite (Hr k (Hnkh _ _ _ Hin)); apply HL in Hin as [e [E [Hp _]]]; eauto. }
  assert (Hss : strip_sole h a = retarget_all h L r)
    by (unfold strip_sole, backs_of; rewrite Eh; reflexivity).
  assert (Hks : keys_ok (strip_sole h a) = true) by (rewrite Hss; apply keys_ok_retarget_all, Hkr).
  (* the shape *)
  assert (Hshape : same_shape (strip_sole h a) (strip_once h a)).
  { intro key; pose proof (retarget_all_spec h L r key Hkr Hfun Hval) as RS; rewrite <- Hss in RS.
    unfold strip_once, renumber; rewrite get_map_filter.
    destruct (Pos.eqb_spec key (label_key h)) as [->|Hne].
    - unfold r, set_entry in RS; rewrite get_update, Pos.eqb_refl in RS.
      unfold set_entry; rewrite get_update, Pos.eqb_refl.
      assert (Hu : Braun.unsnoc (seq_of a h) = BE).
      { apply Braun.empty_canonical; [apply (proj1 (Braun.unsnoc_spec _ (keys_ok_balanced a h Hk)))|].
        rewrite (proj2 (Braun.unsnoc_spec _ (keys_ok_balanced a h Hk))), elems_seq_of, Hf; reflexivity. }
      rewrite Hu; destruct (nontrivial_seq BE (pred (count a h))); cbn [option_map].
      + destruct (get (label_key h) (strip_sole h a)) as [e'|] eqn:E'; [|contradiction].
        destruct RS as [Hl [Ho [_ [Hs _]]]]; cbn [e_label e_out e_tree Braun.size] in Hl, Ho, Hs.
        assert (e_tree e' = BE).
        { apply Braun.empty_canonical; [apply (proj2 (proj1 (keys_ok_spec _) Hks _ _ E'))|].
          apply length_zero_iff_nil; rewrite Braun.to_list_length; exact Hs. }
        unfold shape; cbn; rewrite Hl, Ho, H; reflexivity.
      + destruct (get (label_key h) (strip_sole h a)); [contradiction|reflexivity].
    - rewrite (Hr key Hne) in RS; unfold set_entry; rewrite get_update, (proj2 (Pos.eqb_neq _ _) Hne).
      destruct (get key a) as [e|] eqn:E; cbn [option_map];
        [|destruct (get key (strip_sole h a)); [contradiction|reflexivity]].
      destruct (get key (strip_sole h a)) as [e'|] eqn:E'; [|contradiction].
      destruct RS as [Hl [Ho [_ [Hs [_ Hn]]]]].
      pose proof (proj2 (proj1 (keys_ok_spec a) Hk _ _ E)) as B.
      pose proof (proj2 (proj1 (keys_ok_spec _) Hks _ _ E')) as B'.
      cbn [option_map]; unfold shape; cbn [e_label e_tree e_out]; rewrite Hl, Ho; do 3 f_equal.
      apply Braun.canonical; [exact B'|apply Braun.balanced_map, B|].
      apply nth_error_ext; intro i.
      rewrite <- !Braun.nth_to_list by (assumption || apply Braun.balanced_map, B).
      rewrite Braun.nth_map.
      destruct (Nat.lt_ge_cases i (Braun.size (e_tree e))) as [Hi|Hi].
      2: { rewrite (proj2 (nth_none_size _ i B') ltac:(lia)), (proj2 (nth_none_size _ i B) Hi); reflexivity. }
      rewrite Hn by exact Hi.
      destruct (Braun.nth i (e_tree e)) as [ti|] eqn:Ti; [|apply nth_none_size in Ti; [lia|exact B]].
      assert (Ti' : nth_error (e_targets e) i = Some ti)
        by (unfold e_targets; rewrite <- Braun.nth_to_list by exact B; exact Ti).
      assert (Hrf : forall n, refers a h n key (Braun.size (e_tree e) - S i) <-> ti = Slot h n).
      { intros n; split.
        - intros [e0 [E0 [_ N0]]]; rewrite E in E0; injection E0 as <-.
          replace (Braun.size (e_tree e) - S (Braun.size (e_tree e) - S i)) with i in N0 by lia.
          congruence.
        - intros ->; exists e; split; [exact E|split; [lia|]].
          replace (Braun.size (e_tree e) - S (Braun.size (e_tree e) - S i)) with i by lia; exact Ti'. }
      destruct (rlookup L key _) as [j|] eqn:R.
      + apply rlookup_some, HL, Hrf in R; subst ti; cbn; rewrite label_eqb_refl; reflexivity.
      + destruct ti as [g n|q]; [|reflexivity]; cbn [option_map renumber_target].
        destruct (label_eqb_spec g h) as [->|]; [|reflexivity].
        exfalso; destruct n as [|n].
        * pose proof (proj2 (Hrf 0) eq_refl) as R0; apply H0 in R0 as [R0 _]; contradiction.
        * apply (rlookup_none L key _ n R), HL, Hrf; reflexivity. }
  split; [exact Hshape|].
  (* the back-links *)
  intros key e' E'.
  apply (shape_backs_ok (strip_once h a) (strip_sole h a) e' (same_shape_sym _ _ Hshape)).
  pose proof (retarget_all_spec h L r key Hkr Hfun Hval) as RS; rewrite <- Hss, E' in RS.
  unfold backs_ok; apply (backs_for_iff (fun g j k p => (g = h /\ refers a h (S j) k p)
                                                       \/ (g <> h /\ refers a g j k p))).
  { intros g j k p; rewrite (refers_strip_once h a g j k p Hk Hf H0); reflexivity. }
  destruct (Pos.eqb_spec key (label_key h)) as [->|Hne].
  - unfold r, set_entry in RS; rewrite get_update, Pos.eqb_refl in RS.
    destruct (nontrivial_seq BE (pred (count a h))); [|contradiction].
    destruct RS as [Hl [Ho [Hb _]]]; cbn [e_label e_out e_back] in Hl, Ho, Hb.
    split; [rewrite Hb; exact Bbk|split].
    + rewrite Hb, Ho; unfold count; rewrite Eh, <- Szh, <- !Braun.to_list_length, Lbk.
      destruct (Braun.to_list (e_back eh)); reflexivity.
    + intros j s Es; rewrite Hb, Hnb in Es; destruct (Mh _ _ Es) as [W M]; split; [exact W|].
      intros k p; rewrite M, Lh, Hl; split; [intros R; left; auto|intros [[_ R]|[Hh _]]; [exact R|contradiction]].
  - rewrite (Hr key Hne) in RS; destruct (get key a) as [e|] eqn:E; [|contradiction].
    destruct RS as [Hl [Ho [Hb _]]].
    pose proof (proj1 (proj1 (keys_ok_spec a) Hk _ _ E)) as Ke.
    assert (Hgh : e_label e <> h) by (intro Hx; apply Hne; rewrite Ke, Hx; reflexivity).
    destruct (La _ _ E) as [B [Sz M]].
    split; [rewrite Hb; exact B|split; [rewrite Hb, Ho; exact Sz|]].
    intros j s Es; rewrite Hb in Es; destruct (M _ _ Es) as [W M']; split; [exact W|].
    intros k p; rewrite M', Hl; split; [intros R; right; auto|intros [[Hh _]|[_ R]]; [contradiction|exact R]].
Qed.

(** *** The specification of [push_inner] *)

Theorem push_inner_spec h t a :
  slots_ok a -> linked_prop a -> (forall g n, t = Slot g n -> n < count a g) ->
  almost_normal (cons_entry h t a) h ->
  strip_ok a h (fst (find a h)) = true \/ t = Slot h 0 ->
  normal (push_inner h t a) = true /\ linked_prop (push_inner h t a)
  /\ forall v, apply (push_inner h t a) v = apply (cons_entry h t a) v.
Proof.
  intros [Hk Hwf] La Ht Han H4.
  destruct (linked_cons h t a Hk La Ht) as [Sh L1].
  set (a1 := cons_linked h t a) in *.
  assert (Han1 : almost_normal a1 h) by (apply (shape_pre_normal _ _ _ (same_shape_sym _ _ Sh)), Han).
  assert (Hk1 : keys_ok a1 = true) by (destruct Han1; assumption).
  assert (So1 : slots_ok a1) by (apply (pre_normal_slots_ok _ _ Han1)).
  unfold push_inner; fold a1; destruct (strip_check h a1) eqn:C.
  - pose proof (strip_check_true h a1 Hk1 L1 C) as H0.
    assert (R0 : refers a1 h 0 (label_key h) 0) by (apply H0; auto).
    rewrite (shape_refers _ _ _ _ _ _ Sh), (refers_cons_entry h t a _ _ _ _ Hk) in R0.
    (* [h] had no inputs *)
    assert (Hnil : fst (find a h) = []).
    { destruct (fst (find a h)) as [|t0 ts0] eqn:Ef; [reflexivity|exfalso].
      assert (Hj : jlen a h = length (t0 :: ts0)) by (rewrite jlen_find, Ef; reflexivity).
      destruct R0 as [R0|[_ [Hj0 _]]]; [|rewrite Hj in Hj0; discriminate].
      destruct H4 as [Hs| ->].
      - apply (refers_rvar a h 0 _ _ Hk) in R0 as [v0 [Hv0 [Hk0 Hp0]]].
        apply label_key_inj in Hk0; destruct v0 as [hv0 i0]; cbn [v_label v_index] in *; subst hv0.
        rewrite Hj in Hp0; rewrite Ef in Hv0.
        assert (Hlast : last_target (t0 :: ts0) = Some (Slot h 0)).
        { unfold last_target; assert (i0 < length (t0 :: ts0)) by (apply nth_error_Some; congruence).
          replace (pred (length (t0 :: ts0))) with i0 by lia; exact Hv0. }
        rewrite (strip_ok_spec a h _ Hk) in Hs; destruct (Hs Hlast) as [v [Hv Hne]].
        assert (R : refers a1 h 0 (label_key (v_label v)) (jlen a (v_label v) - S (v_index v))).
        { rewrite (shape_refers _ _ _ _ _ _ Sh), (refers_cons_entry h t a _ _ _ _ Hk); left.
          apply refers_rvar; [exact Hk|exists v; auto]. }
        apply H0 in R as [Rk Rp]; apply label_key_inj in Rk.
        apply Hne; destruct v as [hv i]; cbn [v_label v_index] in *; subst hv.
        rewrite Hj in Rp; assert (i < length (t0 :: ts0)) by (apply nth_error_Some; rewrite <- Ef; congruence).
        f_equal; lia.
      - assert (R : refers a1 h 0 (label_key h) (jlen a h)).
        { rewrite (shape_refers _ _ _ _ _ _ Sh), (refers_cons_entry h _ a _ _ _ _ Hk); right; auto. }
        apply H0 in R as [_ Rp]; rewrite Hj in Rp; discriminate. }
    assert (Ht0 : t = Slot h 0).
    { destruct R0 as [[e [E [Hp _]]]|[_ [_ Ht0]]]; [|exact Ht0].
      unfold find in Hnil; rewrite E in Hnil; cbn [fst] in Hnil; unfold e_targets in Hnil.
      rewrite <- Braun.to_list_length, Hnil in Hp; cbn in Hp; lia. }
    assert (Hf1 : fst (find a1 h) = [Slot h 0])
      by (rewrite (shape_find _ _ _ Sh), find_cons_entry, label_eqb_refl, Hnil, Ht0; reflexivity).
    destruct (strip_sole_spec h a1 So1 L1 Hf1 H0) as [Sh2 L2].
    pose proof (strip_check_true_strip_ok h a1 Hk1 L1 C) as Hs1.
    pose proof (strip_ok_false_strippable a1 _ h Han1 Hs1) as Hst.
    pose proof (pre_normal_strip_once a1 _ h Han1 eq_refl Hst) as Hp2.
    split; [|split; [exact L2|]].
    + apply (shape_normal _ _ (same_shape_sym _ _ Sh2)), (normal_iff _ h); split; [exact Hp2|].
      rewrite find_strip_once, label_eqb_refl, Hf1 by exact Hk1; reflexivity.
    + intros v; rewrite (shape_apply _ _ v Sh2), apply_strip_once by assumption.
      apply shape_apply, Sh.
  - split; [|split; [exact L1|intros v; apply shape_apply, Sh]].
    apply (normal_iff a1 h); split; [exact Han1|apply strip_check_false; assumption].
Qed.

Theorem push_inner_normal h t a :
  normal a = true -> linked a = true -> (forall g n, t = Slot g n -> n < count a g) ->
  normal (push_inner h t a) = true /\ linked (push_inner h t a) = true
  /\ forall v, apply (push_inner h t a) v
               = if rvar_eqb v (mk_rvar h 0) then resolve a t
                 else apply a (unshift_rvar (mk_rvar h 0) v).
Proof.
  intros Ha La Ht.
  apply linked_spec in La; [|apply normal_slots_ok, Ha].
  destruct (push_inner_spec h t a (normal_slots_ok a Ha) La Ht (almost_normal_cons_entry h t a Ha Ht)
              (or_introl (proj2 (proj1 (normal_iff a h) Ha)))) as [Hn [Hl Happ]].
  split; [exact Hn|split; [apply linked_spec; [apply normal_slots_ok, Hn|exact Hl]|]].
  intros v; rewrite Happ; apply apply_cons_entry.
Qed.


(** *** Adding an output slot keeps the back-links correct *)

Lemma refers_push_outer h a g j k p : refers (push_outer h a) g j k p <-> refers a g j k p.
Proof.
  unfold refers, push_outer; rewrite get_update.
  destruct (Pos.eqb_spec k (label_key h)) as [->|]; [|reflexivity].
  destruct (get (label_key h) a) as [e0|]; split.
  - intros [e [[= <-] R]]; exists e0; auto.
  - intros [e [[= <-] R]]; eexists; split; [reflexivity|exact R].
  - intros [e [[= <-] [Hp _]]]; cbn in Hp; lia.
  - intros [e [[=] _]].
Qed.

Theorem linked_push_outer h a :
  normal a = true -> linked a = true -> linked (push_outer h a) = true.
Proof.
  intros Ha La; pose proof (normal_slots_ok a Ha) as [Hk Hwf].
  apply linked_spec in La; [|apply normal_slots_ok, Ha].
  apply linked_spec; [apply normal_slots_ok, normal_push_outer, Ha|].
  assert (Hnone : forall j k p, count a h <= j -> ~ refers a h j k p).
  { intros j k p Hj R; apply (refers_rvar a h j k p Hk) in R as [v [Hv _]].
    pose proof (Hwf _ _ _ Hv); lia. }
  intros key e E; unfold push_outer in E; rewrite get_update in E.
  unfold backs_ok; apply (backs_for_iff (refers a)); [intros; symmetry; apply refers_push_outer|].
  destruct (Pos.eqb_spec key (label_key h)) as [->|]; [|apply (La _ _ E)].
  unfold count in Hnone; destruct (get (label_key h) a) as [e0|] eqn:E0; injection E as <-.
  - pose proof (keys_ok_label a h e0 Hk E0) as Lh.
    destruct (La _ _ E0) as [B [Sz M]].
    destruct (Braun.snoc_spec (e_back e0) Empty B) as [B' L'].
    unfold backs_for; cbn [e_back e_out e_label]; split; [exact B'|split].
    + rewrite <- Braun.to_list_length, L', length_app, Braun.to_list_length, Sz; cbn; lia.
    + intros j s Es; rewrite Braun.nth_to_list, L' in Es by exact B'.
      destruct (Nat.lt_ge_cases j (Braun.size (e_back e0))) as [Hj|Hj].
      * rewrite nth_error_app1 in Es by (rewrite Braun.to_list_length; exact Hj).
        rewrite <- Braun.nth_to_list in Es by exact B; rewrite <- Lh; apply M, Es.
      * rewrite nth_error_app2 in Es by (rewrite Braun.to_list_length; exact Hj).
        rewrite Braun.to_list_length in Es.
        destruct (j - Braun.size (e_back e0)) as [|]; cbn in Es; [|rewrite nth_error_nil in Es; discriminate].
        injection Es as <-; split; [apply links_wf_empty|]; intros k p.
        split; [intros Hm; contradiction (link_mem_empty k p)|intros R; exfalso].
        apply (Hnone j k p); [lia|exact R].
  - unfold backs_for; cbn [e_back e_out e_label].
    split; [cbn; auto|split; [reflexivity|]].
    intros [|j] s Es; cbn in Es; [|destruct (Nat.even j); discriminate].
    injection Es as <-; split; [apply links_wf_empty|]; intros k p.
    split; [intros Hm; contradiction (link_mem_empty k p)|intros R; exfalso].
    apply (Hnone 0 k p); [lia|exact R].
Qed.


(** ** Composition

    [compose fp a b] first applies [b] and then [a]; [fp] moves [b]'s
    payloads through [a].  For each label [h] the result has [jlen b h]
    input entries from [b], followed by [a]'s input entries that [b] passes
    through to; its output slots are [a]'s slots followed (on the innermost
    side) by those of [b]'s slots that [a] passes through. *)

Section Compose.

Variable fp : P -> P.

Definition ext_count a b h : nat := count a h + (count b h - jlen a h).
Definition res_len a b h : nat := jlen b h + (jlen a h - count b h).

Definition encode_res a b (r : rvar + P) : target P :=
  match r with
  | inl u => Slot (v_label u) (ext_count a b (v_label u) - S (v_index u))
  | inr p => Bind p
  end.

(** Where [b] sends the inner [h₍ᵢ₎]. *)
Definition b_image b h (i : nat) : rvar + P := lookup b (mk_rvar h i).

Definition comp_target a b h (i : nat) : target P :=
  match b_image b h i with
  | inl w => encode_res a b (lookup a w)
  | inr p => Bind (fp p)
  end.

Definition comp_entry a b h : option (entry P) :=
  let ts := Braun.of_list (map (comp_target a b h) (List.seq 0 (res_len a b h))) in
  let k := ext_count a b h in
  if nontrivial_seq ts k then Some (mk_entry h ts k BE) else None.

Definition compose_pre a b : raw P :=
  merge (fun _ ea eb =>
           match ea, eb with
           | None, None => None
           | Some e, _ => comp_entry a b (e_label e)
           | None, Some e => comp_entry a b (e_label e)
           end) a b.

Lemma find_none_trivial a h : get (label_key h) a = None -> find a h = ([], 0).
Proof. intro E; unfold find; rewrite E; reflexivity. Qed.

Lemma find_compose_pre a b h :
  normal a = true -> normal b = true ->
  find (compose_pre a b) h = (map (comp_target a b h) (List.seq 0 (res_len a b h)), ext_count a b h).
Proof.
  intros Ha Hb; unfold find at 1, compose_pre; rewrite get_merge by reflexivity.
  assert (Hc : forall e, comp_entry a b h = Some e -> (e_targets e, e_out e)
                 = (map (comp_target a b h) (List.seq 0 (res_len a b h)), ext_count a b h)).
  { unfold comp_entry; intros e; destruct (nontrivial_seq _ _); [|discriminate].
    intros [= <-]; unfold e_targets; cbn [e_tree e_out]; rewrite Braun.to_list_of_list; reflexivity. }
  assert (Hn : comp_entry a b h = None ->
               ([] : list (target P), 0) = (map (comp_target a b h) (List.seq 0 (res_len a b h)), ext_count a b h)).
  { unfold comp_entry; rewrite nontrivial_seq_elems, Braun.to_list_of_list.
    destruct (map _ _) as [|t ts] eqn:E, (ext_count a b h) as [|k];
      cbn [nontrivial]; try discriminate; intros _; reflexivity. }
  destruct (get (label_key h) a) as [ea|] eqn:Ea, (get (label_key h) b) as [eb|] eqn:Eb.
  - rewrite (find_label a h ea Ha Ea).
    destruct (comp_entry a b h) as [e|] eqn:E; [apply Hc; reflexivity|apply Hn; reflexivity].
  - rewrite (find_label a h ea Ha Ea).
    destruct (comp_entry a b h) as [e|] eqn:E; [apply Hc; reflexivity|apply Hn; reflexivity].
  - rewrite (find_label b h eb Hb Eb).
    destruct (comp_entry a b h) as [e|] eqn:E; [apply Hc; reflexivity|apply Hn; reflexivity].
  - unfold res_len, ext_count; rewrite ?jlen_find, ?count_find.
    rewrite (find_none_trivial a h Ea), (find_none_trivial b h Eb); reflexivity.
Qed.

(** Results of [a] on the inputs that [b] reaches stay within the result's
    slots. *)
Lemma apply_a_bound a b w u :
  normal a = true ->
  v_index w < Nat.max (jlen a (v_label w)) (count b (v_label w)) ->
  apply a w = inl u -> v_index u < ext_count a b (v_label u).
Proof.
  intros Ha Hw Hu; unfold apply in Hu.
  destruct (nth_error (fst (find a (v_label w))) (v_index w)) as [t|] eqn:E.
  - destruct t as [h' n|p]; cbn [resolve] in Hu; [|discriminate].
    injection Hu as <-; cbn [v_label v_index].
    pose proof (slot_bound a w h' n Ha E); unfold ext_count; lia.
  - injection Hu as <-; cbn [v_label v_index].
    apply nth_error_None in E; unfold ext_count in *; rewrite ?jlen_find in *; lia.
Qed.

Lemma resolve_encode_res c a b u :
  count c (v_label u) = ext_count a b (v_label u) ->
  v_index u < ext_count a b (v_label u) ->
  resolve c (encode_res a b (inl u)) = inl u.
Proof.
  intros Hc Hb; cbn [encode_res resolve]; rewrite Hc.
  destruct u as [h i]; cbn in *; do 2 f_equal; lia.
Qed.

Theorem apply_compose_pre a b v :
  normal a = true -> normal b = true ->
  apply (compose_pre a b) v
  = match apply b v with
    | inl w => apply a w
    | inr p => inr (fp p)
    end.
Proof.
  intros Ha Hb.
  assert (Hcount : forall h, count (compose_pre a b) h = ext_count a b h)
    by (intro h; rewrite !count_find; rewrite find_compose_pre by assumption; reflexivity).
  destruct v as [h i].
  assert (Hc : apply (compose_pre a b) (mk_rvar h i)
               = if Nat.ltb i (res_len a b h)
                 then resolve (compose_pre a b) (comp_target a b h i)
                 else inl (mk_rvar h (i - res_len a b h + ext_count a b h))).
  { unfold apply at 1; cbn [v_label v_index].
    rewrite find_compose_pre, Hcount by assumption; cbn [fst snd].
    rewrite nth_error_map, length_map, length_seq, List.nth_error_seq.
    destruct (Nat.ltb_spec i (res_len a b h)); reflexivity. }
  rewrite Hc.
  destruct (Nat.ltb_spec i (res_len a b h)) as [Hi|Hi].
  - unfold comp_target, b_image; rewrite !lookup_spec by (apply keys_ok_balanced, normal_keys_ok; assumption).
    destruct (apply b (mk_rvar h i)) as [w|p] eqn:Ebw; [|reflexivity].
    (* where b sends the inner h_i is within a's reach *)
    assert (Hw : v_index w < Nat.max (jlen a (v_label w)) (count b (v_label w))).
    { unfold apply in Ebw; cbn [v_label v_index] in Ebw.
      destruct (nth_error (fst (find b h)) i) as [t|] eqn:Et.
      - destruct t as [h' n|p]; cbn [resolve] in Ebw; [|discriminate].
        injection Ebw as <-; cbn [v_label v_index].
        pose proof (slot_bound b (mk_rvar h i) h' n Hb Et); lia.
      - injection Ebw as <-; cbn [v_label v_index].
        apply nth_error_None in Et; unfold res_len in *; rewrite ?jlen_find, ?count_find in *; lia. }
    rewrite ?lookup_spec by (apply keys_ok_balanced, normal_keys_ok; assumption); destruct (apply a w) as [u|p] eqn:Eaw; [|reflexivity].
    apply resolve_encode_res; [apply Hcount|apply (apply_a_bound a b w u Ha Hw Eaw)].
  - unfold apply; cbn [v_label v_index].
    unfold res_len, ext_count in *; rewrite ?jlen_find in *.
    rewrite (proj2 (nth_error_None (fst (find b h)) i)) by lia.
    cbn [v_label v_index].
    rewrite (proj2 (nth_error_None (fst (find a h)) _)) by lia.
    do 2 f_equal; lia.
Qed.

Lemma comp_target_slot_bound a b h i h' n :
  normal a = true -> normal b = true -> i < res_len a b h ->
  comp_target a b h i = Slot h' n -> n < ext_count a b h'.
Proof.
  intros Ha Hb Hi; unfold comp_target, b_image; rewrite !lookup_spec by (apply keys_ok_balanced, normal_keys_ok; assumption).
  destruct (apply b (mk_rvar h i)) as [w|p] eqn:Ebw; [|discriminate].
  assert (Hw : v_index w < Nat.max (jlen a (v_label w)) (count b (v_label w))).
  { unfold apply in Ebw; cbn [v_label v_index] in Ebw.
    destruct (nth_error (fst (find b h)) i) as [t|] eqn:Et.
    - destruct t as [h'' n'|p]; cbn [resolve] in Ebw; [|discriminate].
      injection Ebw as <-; cbn [v_label v_index].
      pose proof (slot_bound b (mk_rvar h i) h'' n' Hb Et); lia.
    - injection Ebw as <-; cbn [v_label v_index].
      apply nth_error_None in Et; unfold res_len in *; rewrite ?jlen_find, ?count_find in *; lia. }
  rewrite ?lookup_spec by (apply keys_ok_balanced, normal_keys_ok; assumption); destruct (apply a w) as [u|p] eqn:Eaw; cbn [encode_res]; [|discriminate].
  intros [= <- <-].
  pose proof (apply_a_bound a b w u Ha Hw Eaw); lia.
Qed.

Definition labels a : list (option label) := map (fun ke => e_label (snd ke)) (elements a).

Lemma not_in_labels a l : keys_ok a = true -> ~ In l (labels a) -> get (label_key l) a = None.
Proof.
  intros Ha Hl; destruct (get (label_key l) a) as [e|] eqn:E; [|reflexivity].
  exfalso; apply Hl, in_map_iff; exists (label_key l, e); split.
  - cbn [snd]; apply (keys_ok_label a l e Ha E).
  - apply In_elements, E.
Qed.

Lemma keys_ok_compose_pre a b :
  normal a = true -> normal b = true -> keys_ok (compose_pre a b) = true.
Proof.
  intros Ha Hb; apply keys_ok_spec; intros key e He.
  unfold compose_pre in He; rewrite get_merge in He by reflexivity.
  assert (Hc : forall l, comp_entry a b l = Some e -> e_label e = l /\ Braun.balanced (e_tree e))
    by (intros l; unfold comp_entry; destruct (nontrivial_seq _ _);
        [intros [= <-]; split; [reflexivity|apply Braun.balanced_of_list]|discriminate]).
  destruct (get key a) as [ea|] eqn:Ea, (get key b) as [eb|] eqn:Eb; try discriminate.
  all: destruct (Hc _ He) as [Hl Hbal]; split; [rewrite Hl|exact Hbal].
  all: first [ apply (normal_label a key ea Ha Ea) | apply (normal_label b key eb Hb Eb) ].
Qed.

Theorem pre_normal_compose_pre a b :
  normal a = true -> normal b = true ->
  pre_normal (compose_pre a b) (fun l => In l (labels (compose_pre a b))).
Proof.
  intros Ha Hb.
  pose proof (keys_ok_compose_pre a b Ha Hb) as Hk.
  repeat split.
  - exact Hk.
  - intros key e He; unfold compose_pre in He; rewrite get_merge in He by reflexivity.
    assert (Hc : forall l, comp_entry a b l = Some e -> nontrivial (e_targets e) (e_out e) = true)
      by (intros l; unfold comp_entry; destruct (nontrivial_seq _ _) eqn:N;
          [intros [= <-]; unfold e_targets; cbn [e_tree e_out]; rewrite <- nontrivial_seq_elems; exact N
          |discriminate]).
    destruct (get key a), (get key b); try discriminate; apply (Hc _ He).
  - intros v h' n Hn.
    rewrite !count_find; rewrite find_compose_pre by assumption; cbn [snd].
    rewrite find_compose_pre in Hn by assumption; cbn [fst] in Hn.
    rewrite nth_error_map, List.nth_error_seq in Hn.
    destruct (Nat.ltb_spec (v_index v) (res_len a b (v_label v))) as [Hi|]; [|discriminate].
    injection Hn as Hn.
    apply (comp_target_slot_bound a b (v_label v) (v_index v) h' n Ha Hb Hi Hn).
  - intros h' Hn.
    unfold find; rewrite (not_in_labels _ h' Hk Hn); reflexivity.
Qed.

End Compose.

Lemma pre_normal_mono a (Q Q' : option label -> Prop) :
  pre_normal a Q -> (forall x, ~ Q' x -> ~ Q x) -> pre_normal a Q'.
Proof. intros [Hk [Hnt [Hwf Hs]]] H; repeat split; auto. Qed.

Fixpoint normalize_list (L : list (option label)) a : raw P :=
  match L with
  | [] => a
  | l :: L' => normalize_list L' (strip_loop (S (jlen a l)) l a)
  end.

Theorem normalize_list_spec L a :
  pre_normal a (fun l => In l L) ->
  normal (normalize_list L a) = true /\ (forall v, apply (normalize_list L a) v = apply a v).
Proof.
  revert a; induction L as [|l L IH]; intros a Ha; cbn [normalize_list].
  - split; [|reflexivity].
    apply (normal_of_pre_normal a _ Ha); intros x [].
  - destruct (strip_loop_spec_gen (S (jlen a l)) _ l a Ha (or_introl eq_refl) ltac:(lia))
      as [Hn Happ].
    assert (Hmono : forall x, ~ In x L -> ~ (In x (l :: L) /\ x <> l)).
    { intros x Hx [[E|Hin] Hne]; [apply Hne; symmetry; exact E|apply Hx, Hin]. }
    destruct (IH _ (pre_normal_mono _ _ _ Hn Hmono)) as [Hn' Happ'].
    split; [exact Hn'|]; intro v; rewrite Happ', Happ; reflexivity.
Qed.

(** Composition rebuilds the back-links once the targets are normal. *)
Definition compose (fp : P -> P) a b : raw P :=
  relink (normalize_list (labels (compose_pre fp a b)) (compose_pre fp a b)).

Lemma compose_shape fp a b :
  normal a = true -> normal b = true ->
  normal (normalize_list (labels (compose_pre fp a b)) (compose_pre fp a b)) = true
  /\ same_shape (compose fp a b) (normalize_list (labels (compose_pre fp a b)) (compose_pre fp a b)).
Proof.
  intros Ha Hb; pose proof (proj1 (normalize_list_spec _ _ (pre_normal_compose_pre fp a b Ha Hb))) as Hn.
  split; [exact Hn|apply relink_spec, normal_slots_ok, Hn].
Qed.

Theorem normal_compose fp a b :
  normal a = true -> normal b = true -> normal (compose fp a b) = true.
Proof.
  intros Ha Hb; destruct (compose_shape fp a b Ha Hb) as [Hn Hs].
  apply (shape_normal _ _ (same_shape_sym _ _ Hs)), Hn.
Qed.

Theorem linked_compose fp a b :
  normal a = true -> normal b = true -> linked (compose fp a b) = true.
Proof.
  intros Ha Hb; apply linked_relink, normal_slots_ok, (proj1 (compose_shape fp a b Ha Hb)).
Qed.

Theorem apply_compose fp a b v :
  normal a = true -> normal b = true ->
  apply (compose fp a b) v
  = match apply b v with
    | inl w => apply a w
    | inr p => inr (fp p)
    end.
Proof.
  intros Ha Hb; rewrite (shape_apply _ _ v (proj2 (compose_shape fp a b Ha Hb))).
  rewrite (proj2 (normalize_list_spec _ _ (pre_normal_compose_pre fp a b Ha Hb))).
  apply apply_compose_pre; assumption.
Qed.


(** ** Restriction: forgetting the inputs of one label

    [restrict h a] agrees with [a] on every variable not labelled [h], has
    no input entries for [h], and drops the innermost [h] output slots that
    nothing refers to.  Payload adjustments are restricted at [None]: their
    inputs are the free variables of a closed term, so bound inputs never
    occur. *)

Definition has_ref0 a h : bool :=
  existsb (fun r => match r with (_, h', 0) => label_eqb h' h | _ => false end) (refs a).

Lemma has_ref0_spec a h :
  normal a = true ->
  has_ref0 a h = true
  <-> exists v, nth_error (fst (find a (v_label v))) (v_index v) = Some (Slot h 0).
Proof.
  intros Ha; unfold has_ref0; rewrite existsb_exists; split.
  - intros [[[v h'] [|n]] [Hin Hr]]; [|discriminate].
    apply label_eqb_eq in Hr; subst h'; exists v; apply In_refs; assumption.
  - intros [v Hv]; exists (v, h, 0); split; [apply In_refs; assumption|apply label_eqb_refl].
Qed.

Definition clear h a : raw P := set_entry h BE (count a h) (backs_of a h) a.

Lemma find_clear h a h' :
  find (clear h a) h' = if label_eqb h' h then ([], count a h) else find a h'.
Proof. apply find_set_entry. Qed.

Lemma count_clear h a h' : count (clear h a) h' = count a h'.
Proof.
  rewrite count_find at 1; rewrite find_clear.
  destruct (label_eqb_spec h' h) as [->|]; rewrite ?count_find; reflexivity.
Qed.

Lemma resolve_same_count a b t :
  (forall h, count a h = count b h) -> resolve a t = resolve b t.
Proof. intros H; destruct t; cbn [resolve]; [rewrite H|]; reflexivity. Qed.

Lemma apply_clear h a v : v_label v <> h -> apply (clear h a) v = apply a v.
Proof.
  intros Hv; unfold apply; rewrite find_clear, (proj2 (label_eqb_neq _ _) Hv), count_clear.
  destruct (nth_error _ _); [apply resolve_same_count, count_clear|reflexivity].
Qed.

Lemma pre_normal_clear h a :
  normal a = true -> pre_normal (clear h a) (fun l => In l (labels (clear h a))).
Proof.
  intros Ha; pose proof (proj1 (normal_iff a h) Ha) as [[Hk [Hnt [Hwf _]]] _].
  assert (Hk' : keys_ok (clear h a) = true) by (unfold clear; apply keys_ok_set_entry; [exact I|exact Hk]).
  repeat split.
  - exact Hk'.
  - intros key e He; unfold clear in He.
    destruct (get_set_entry _ _ _ _ _ _ _ He) as [[_ [_ N]]|[_ E1]]; [exact N|apply (Hnt _ _ E1)].
  - intros v h' n Hn; rewrite count_clear; rewrite find_clear in Hn.
    destruct (label_eqb (v_label v) h); [destruct (v_index v); discriminate|].
    apply (Hwf _ _ _ Hn).
  - intros l Hl; apply not_in_labels in Hl; [|exact Hk'].
    rewrite (find_none_trivial _ _ Hl); reflexivity.
Qed.

Lemma find_nil_strip_once l h a :
  fst (find a h) = [] -> fst (find (strip_once l a) h) = [].
Proof.
  intros H; unfold strip_once; rewrite find_renumber, find_set_entry; cbn [fst].
  destruct (label_eqb_spec h l) as [->|]; [|rewrite H; reflexivity].
  rewrite <- elems_seq_of in H; destruct (seq_of a l); [reflexivity|discriminate].
Qed.

Lemma find_nil_strip_loop fuel l h a :
  fst (find a h) = [] -> fst (find (strip_loop fuel l a) h) = [].
Proof.
  revert a; induction fuel as [|f IH]; intros a H; cbn [strip_loop]; [exact H|].
  destruct (strip_ok _ _ _); [exact H|apply IH, find_nil_strip_once, H].
Qed.

Lemma find_nil_normalize_list L h a :
  fst (find a h) = [] -> fst (find (normalize_list L a) h) = [].
Proof.
  revert a; induction L as [|l L IH]; intros a H; cbn [normalize_list]; [exact H|].
  apply IH, find_nil_strip_loop, H.
Qed.

Lemma normal_trim h a :
  normal a = true -> fst (find a h) = [] -> has_ref0 a h = false ->
  normal (strip_once h a) = true.
Proof.
  intros Ha Hnil Hr.
  pose proof (proj1 (normal_iff a h) Ha) as [[Hk [Hnt [Hwf Hs]]] _].
  assert (Hno : forall v, nth_error (fst (find a (v_label v))) (v_index v) <> Some (Slot h 0)).
  { intros v Hv; rewrite (proj2 (has_ref0_spec a h Ha) (ex_intro _ v Hv)) in Hr; discriminate. }
  assert (Hk' : keys_ok (strip_once h a) = true)
    by apply keys_ok_strip_once, Hk.
  apply (normal_of_pre_normal _ (fun _ => False)); [|auto].
  repeat split.
  - exact Hk'.
  - intros key e He; unfold strip_once, renumber in He.
    destruct (get_map_seq _ _ _ _ He) as [e0 [E0 [_ ->]]].
    destruct (get_set_entry _ _ _ _ _ _ _ E0) as [[_ [_ N]]|[_ E1]]; [exact N|apply (Hnt _ _ E1)].
  - intros v h' n Hn.
    destruct (find_strip_once_nth h a v (v_index v) _ Hk Hn) as [t0 [Ht0 [Heq _]]].
    destruct t0 as [h0 n0|p]; cbn [renumber_target] in Heq; [|discriminate].
    pose proof (Hwf _ _ _ Ht0) as Hb.
    rewrite count_strip_once.
    destruct (label_eqb_spec h0 h) as [->|Hh]; injection Heq as -> ->.
    + rewrite label_eqb_refl.
      destruct n0 as [|n0]; [exfalso; apply (Hno v Ht0)|cbn [pred]; lia].
    + rewrite (proj2 (label_eqb_neq h0 h) Hh); exact Hb.
  - intros h' _.
    destruct (label_eq_dec h' h) as [->|Hne].
    { rewrite (find_nil_strip_once h h a Hnil); reflexivity. }
    apply (strip_ok_spec _ _ _ Hk'); intros Hl'.
    pose proof (Hs h') as Hs'.
    assert (Ef : fst (find (strip_once h a) h') = map (renumber_target h) (fst (find a h'))).
    { rewrite find_strip_once by exact Hk; cbn [fst]; rewrite (proj2 (label_eqb_neq h' h) Hne); reflexivity. }
    assert (Hs'' : strip_ok a h' (fst (find a h')) = true).
    { pose proof (proj1 (normal_iff a h') Ha) as [_ X]; exact X. }
    rewrite (strip_ok_spec _ _ _ Hk) in Hs''.
    rewrite Ef in Hl' |- *.
    unfold last_target in Hl'; rewrite length_map, nth_error_map in Hl'.
    destruct (nth_error (fst (find a h')) (pred (length (fst (find a h'))))) as [[h0 n0|p]|] eqn:El;
      cbn [option_map renumber_target] in Hl'; [|discriminate|discriminate].
    destruct (label_eqb_spec h0 h) as [->|Hh]; injection Hl' as E1 E2; [congruence|].
    subst h0 n0.
    destruct (Hs'' El) as [w [Hw Hwne]].
    exists w; split; [|rewrite length_map; exact Hwne].
    destruct (label_eq_dec (v_label w) h) as [Hwl|Hwl].
    + exfalso; rewrite Hwl, Hnil in Hw; destruct (v_index w); discriminate.
    + rewrite find_strip_once by exact Hk; cbn [fst]; rewrite (proj2 (label_eqb_neq _ h) Hwl).
      rewrite nth_error_map, Hw; cbn [option_map renumber_target].
      rewrite (proj2 (label_eqb_neq h' h) Hne); reflexivity.
Qed.

Lemma apply_trim h a v :
  normal a = true -> fst (find a h) = [] -> has_ref0 a h = false -> v_label v <> h ->
  apply (strip_once h a) v = apply a v.
Proof.
  intros Ha Hnil Hr Hv.
  assert (Hno : forall v, nth_error (fst (find a (v_label v))) (v_index v) <> Some (Slot h 0)).
  { intros w Hw; rewrite (proj2 (has_ref0_spec a h Ha) (ex_intro _ w Hw)) in Hr; discriminate. }
  unfold apply; rewrite find_strip_once, count_strip_once by (apply normal_keys_ok, Ha); cbn [fst].
  rewrite (proj2 (label_eqb_neq _ h) Hv), nth_error_map, length_map.
  destruct (nth_error (fst (find a (v_label v))) (v_index v)) as [[h0 n0|p]|] eqn:E;
    cbn [option_map renumber_target]; [|reflexivity|reflexivity].
  destruct (label_eqb_spec h0 h) as [->|Hh]; cbn [resolve]; rewrite count_strip_once.
  - rewrite label_eqb_refl.
    destruct n0 as [|n0]; [exfalso; apply (Hno v E)|].
    pose proof (slot_bound a v h (S n0) Ha E); cbn [pred]; do 2 f_equal; lia.
  - rewrite (proj2 (label_eqb_neq h0 h) Hh); reflexivity.
Qed.

Fixpoint trim_loop (fuel : nat) h a : raw P :=
  match fuel with
  | 0 => a
  | S f => if Nat.eqb (count a h) 0 || has_ref0 a h then a else trim_loop f h (strip_once h a)
  end.

Lemma trim_loop_spec fuel h a :
  normal a = true -> fst (find a h) = [] -> count a h < fuel ->
  normal (trim_loop fuel h a) = true
  /\ fst (find (trim_loop fuel h a) h) = []
  /\ (count (trim_loop fuel h a) h = 0 \/ has_ref0 (trim_loop fuel h a) h = true)
  /\ (forall v, v_label v <> h -> apply (trim_loop fuel h a) v = apply a v).
Proof.
  revert a; induction fuel as [|f IH]; intros a Ha Hnil Hc; [lia|cbn [trim_loop]].
  destruct (Nat.eqb_spec (count a h) 0) as [H0|H0]; cbn [orb].
  { repeat split; auto. }
  destruct (has_ref0 a h) eqn:Hr.
  { repeat split; auto. }
  destruct (IH (strip_once h a)) as [H1 [H2 [H3 H4]]].
  - apply normal_trim; assumption.
  - apply find_nil_strip_once, Hnil.
  - rewrite count_strip_once, label_eqb_refl; lia.
  - repeat split; auto.
    intros v Hv; rewrite H4 by exact Hv; apply apply_trim; assumption.
Qed.

Definition restrict_targets h a : raw P :=
  let c := clear h a in
  let n := normalize_list (labels c) c in
  trim_loop (S (count n h)) h n.

(** Restriction rebuilds the back-links at the end. *)
Definition restrict h a : raw P := relink (restrict_targets h a).

Lemma restrict_targets_spec h a :
  normal a = true ->
  normal (restrict_targets h a) = true
  /\ fst (find (restrict_targets h a) h) = []
  /\ (count (restrict_targets h a) h = 0 \/ has_ref0 (restrict_targets h a) h = true)
  /\ (forall v, v_label v <> h -> apply (restrict_targets h a) v = apply a v).
Proof.
  intros Ha; unfold restrict_targets.
  destruct (normalize_list_spec _ _ (pre_normal_clear h a Ha)) as [Hn Happ].
  assert (Hnil : fst (find (normalize_list (labels (clear h a)) (clear h a)) h) = []).
  { apply find_nil_normalize_list; rewrite find_clear, label_eqb_refl; reflexivity. }
  destruct (trim_loop_spec (S (count (normalize_list (labels (clear h a)) (clear h a)) h)) h _
              Hn Hnil (Nat.lt_succ_diag_r _)) as [H1 [H2 [H3 H4]]].
  repeat split; auto.
  intros v Hv; rewrite H4, Happ by exact Hv; apply apply_clear, Hv.
Qed.

Theorem restrict_spec h a :
  normal a = true ->
  normal (restrict h a) = true /\ linked (restrict h a) = true
  /\ fst (find (restrict h a) h) = []
  /\ (count (restrict h a) h = 0 \/ has_ref0 (restrict h a) h = true)
  /\ (forall v, v_label v <> h -> apply (restrict h a) v = apply a v).
Proof.
  intros Ha; destruct (restrict_targets_spec h a Ha) as [Hn [Hf [Hc Happ]]].
  pose proof (proj1 (relink_spec _ (normal_slots_ok _ Hn))) as Hs; fold (restrict h a) in Hs.
  split; [apply (shape_normal _ _ (same_shape_sym _ _ Hs)), Hn|].
  split; [apply linked_relink, normal_slots_ok, Hn|].
  split; [rewrite (shape_find _ _ _ Hs); exact Hf|].
  split.
  - rewrite (shape_count _ _ _ Hs); unfold has_ref0.
    rewrite (existsb_same_members _ (refs (restrict h a)) (refs (restrict_targets h a)))
      by (intro; apply shape_refs, Hs).
    exact Hc.
  - intros v Hv; rewrite (shape_apply _ _ v Hs); apply Happ, Hv.
Qed.

(** ** Payloads occurring in an adjustment *)

Definition binds_in (m : raw P) (p : P) : Prop :=
  exists k e, get k m = Some e /\ In (Bind p) (e_targets e).



Lemma binds_in_find (m : raw P) h p :
  In (Bind p) (fst (find m h)) -> binds_in m p.
Proof.
  unfold find; destruct (get (label_key h) m) as [e|] eqn:E; cbn [fst]; [|intros []].
  intros Hin; exists (label_key h), e; auto.
Qed.

Lemma binds_in_renumber h (m : raw P) p : binds_in (renumber h m) p -> binds_in m p.
Proof.
  intros [k [e [He Hin]]]; unfold renumber in He; rewrite get_map_filter in He.
  destruct (get k m) as [e0|] eqn:E0; [|discriminate]; injection He as <-.
  unfold e_targets in Hin; cbn [e_tree] in Hin; rewrite Braun.to_list_map in Hin; apply in_map_iff in Hin as [t [Ht Hin]].
  exists k, e0; split; [exact E0|].
  destruct t as [h' n|p']; cbn in Ht; [destruct (label_eqb h' h); discriminate|].
  injection Ht as ->; exact Hin.
Qed.

Lemma binds_in_set_entry h s n bk (m : raw P) p :
  binds_in (set_entry h s n bk m) p -> binds_in m p \/ In (Bind p) (Braun.to_list s).
Proof.
  intros [k [e [He Hin]]]; unfold set_entry in He; rewrite get_update in He.
  destruct (Pos.eqb k (label_key h)); [|left; exists k, e; auto].
  destruct (nontrivial_seq s n); [|discriminate]; injection He as <-; right; exact Hin.
Qed.

Lemma In_removelast {A} (x : A) (xs : list A) : In x (removelast xs) -> In x xs.
Proof.
  induction xs as [|y xs IH]; [intros []|]; cbn.
  destruct xs as [|z xs]; [intros []|]; intros [->|H]; [left; reflexivity|right; apply IH, H].
Qed.

Lemma binds_in_strip_once h (m : raw P) p : binds_in (strip_once h m) p -> binds_in m p.
Proof.
  unfold strip_once; intros H; apply binds_in_renumber, binds_in_set_entry in H as [H|H];
    [exact H|apply Braun.in_unsnoc in H; rewrite elems_seq_of in H; apply binds_in_find in H; exact H].
Qed.

Lemma binds_in_strip_loop fuel h (m : raw P) p :
  binds_in (strip_loop fuel h m) p -> binds_in m p.
Proof.
  revert m; induction fuel as [|f IH]; intros m H; cbn [strip_loop] in H; [exact H|].
  destruct (strip_ok _ _ _); [exact H|].
  apply (binds_in_strip_once h), IH, H.
Qed.

Lemma binds_in_shape (m m' : raw P) p : same_shape m m' -> binds_in m p -> binds_in m' p.
Proof.
  intros H [k [e [E Hin]]]; destruct (shape_get m m' k e H E) as [e' [E' Sh]].
  exists k, e'; split; [exact E'|]; unfold shape, e_targets in *; injection Sh as _ -> _; exact Hin.
Qed.

Lemma binds_in_retarget_all h L (m : raw P) p : binds_in (retarget_all h L m) p -> binds_in m p.
Proof.
  revert m; induction L as [|[[k q] j] L IH]; intros m H; [exact H|].
  apply IH in H as [k' [e [E Hin]]]; unfold retarget in E; rewrite get_update in E.
  destruct (Pos.eqb_spec k' k) as [->|]; [|exists k', e; auto].
  destruct (get k m) as [e0|] eqn:E0; [|discriminate]; injection E as <-.
  unfold e_targets in Hin; cbn [e_tree] in Hin.
  apply Braun.in_update in Hin as [Hin|[x [_ Hx]]]; [exists k, e0; auto|discriminate].
Qed.

Lemma binds_in_push_inner h t (m : raw P) p :
  binds_in (push_inner h t m) p -> binds_in m p \/ t = Bind p.
Proof.
  assert (Hc : binds_in (cons_linked h t m) p -> binds_in m p \/ t = Bind p).
  { intros H; apply (binds_in_shape _ (cons_entry h t m)) in H; [|apply shape_link_target].
    unfold cons_entry in H; apply binds_in_set_entry in H as [H|H]; [left; exact H|].
    rewrite Braun.to_list_cons, elems_seq_of in H; destruct H as [H|H];
      [right; exact H|left; apply binds_in_find in H; exact H]. }
  unfold push_inner; destruct (strip_check h (cons_linked h t m)); [|exact Hc].
  unfold strip_sole; intros H; apply binds_in_retarget_all, binds_in_set_entry in H as [H|[]].
  apply Hc, H.
Qed.

Lemma binds_in_keys (m : raw P) p :
  keys_ok m = true -> binds_in m p -> exists h, In (Bind p) (fst (find m h)).
Proof.
  intros Hk [k [e [He Hin]]]; exists (e_label e).
  pose proof (proj1 (proj1 (keys_ok_spec m) Hk _ _ He)) as Hkey.
  unfold find; rewrite <- Hkey, He; exact Hin.
Qed.

Lemma binds_in_apply (m : raw P) v p : apply m v = inr p -> binds_in m p.
Proof.
  unfold apply; destruct (nth_error (fst (find m (v_label v))) (v_index v)) as [t|] eqn:E;
    [|discriminate].
  destruct t as [h n|p']; cbn [resolve]; [discriminate|intros [= ->]].
  apply (binds_in_find m (v_label v)), (nth_error_In _ _ E).
Qed.

Lemma binds_in_normalize_list L (m : raw P) p :
  binds_in (normalize_list L m) p -> binds_in m p.
Proof.
  revert m; induction L as [|l L IH]; intros m H; cbn [normalize_list] in H; [exact H|].
  apply IH, binds_in_strip_loop in H; exact H.
Qed.

Lemma binds_in_compose fp a b p :
  normal a = true -> normal b = true ->
  binds_in (compose fp a b) p -> binds_in a p \/ exists p', binds_in b p' /\ p = fp p'.
Proof.
  intros Ha Hb H; apply (binds_in_shape _ _ _ (proj2 (compose_shape fp a b Ha Hb))) in H.
  apply binds_in_normalize_list in H.
  apply binds_in_keys in H as [h Hin]; [|apply keys_ok_compose_pre; assumption].
  rewrite find_compose_pre in Hin by assumption; cbn [fst] in Hin.
  apply in_map_iff in Hin as [i [Ht _]]; unfold comp_target, b_image in Ht; rewrite !lookup_spec in Ht by (apply keys_ok_balanced, normal_keys_ok; assumption).
  destruct (apply b (mk_rvar h i)) as [w|p'] eqn:Eb.
  - rewrite ?lookup_spec in Ht by (apply keys_ok_balanced, normal_keys_ok; assumption); destruct (apply a w) as [u|p''] eqn:Ea; cbn [encode_res] in Ht; [discriminate|].
    injection Ht as ->; left; apply (binds_in_apply a w), Ea.
  - injection Ht as <-; right; exists p'; split; [apply (binds_in_apply b _ _ Eb)|reflexivity].
Qed.

Lemma binds_in_clear h (m : raw P) p : binds_in (clear h m) p -> binds_in m p.
Proof. intros H; apply binds_in_set_entry in H as [H|[]]; exact H. Qed.

Lemma binds_in_trim_loop fuel h (m : raw P) p : binds_in (trim_loop fuel h m) p -> binds_in m p.
Proof.
  revert m; induction fuel as [|f IH]; intros m H; cbn [trim_loop] in H; [exact H|].
  destruct (_ || _); [exact H|apply (binds_in_strip_once h), IH, H].
Qed.

Lemma binds_in_restrict h (m : raw P) p : binds_in (restrict h m) p -> binds_in m p.
Proof.
  intros H; apply (binds_in_shape _ (restrict_targets h m)) in H; [|apply shape_relink].
  unfold restrict_targets in H.
  apply binds_in_trim_loop, binds_in_normalize_list, binds_in_clear in H; exact H.
Qed.

(** ** Composition ignores [fp] outside [b]'s payloads *)

Lemma compose_ext fp fp' a b :
  normal a = true -> normal b = true ->
  (forall p, binds_in b p -> fp p = fp' p) -> compose fp a b = compose fp' a b.
Proof.
  intros Ha Hb H; apply canonical; try (apply normal_compose || apply linked_compose; assumption).
  intros v; rewrite !apply_compose by assumption.
  destruct (apply b v) eqn:E; [reflexivity|].
  rewrite (H _ (binds_in_apply b v _ E)); reflexivity.
Qed.

(** ** Expansion: the inverse of stripping

    [expand1 h a] represents the same adjustment with one more [h] output
    slot: every [h] slot reference moves one step outwards and the first
    pass-through [h] input becomes an explicit reference to the new
    innermost slot.  It lets an input entry refer to any output variable,
    including one that [a] only reaches by passing through. *)

Definition up_target h t : target P :=
  match t with
  | Slot h' n => if label_eqb h' h then Slot h' (S n) else t
  | Bind _ => t
  end.

Definition renumber_up h a : raw P :=
  map_filter (fun _ e => Some (mk_entry (e_label e) (Braun.map (up_target h) (e_tree e))
                                        (e_out e) (e_back e))) a.

Lemma find_renumber_up h a h' :
  find (renumber_up h a) h' = (map (up_target h) (fst (find a h')), snd (find a h')).
Proof.
  unfold find, renumber_up; rewrite get_map_filter.
  destruct (get (label_key h') a); [|reflexivity].
  unfold e_targets; cbn [e_tree e_out fst snd]; rewrite Braun.to_list_map; reflexivity.
Qed.

Lemma keys_ok_renumber_up h a : keys_ok a = true -> keys_ok (renumber_up h a) = true.
Proof.
  intros Ha; apply keys_ok_spec; intros key e He.
  unfold renumber_up in He; rewrite get_map_filter in He.
  destruct (get key a) as [e0|] eqn:E0; [|discriminate]; injection He as <-.
  destruct (proj1 (keys_ok_spec a) Ha _ _ E0) as [K B]; split; [exact K|apply Braun.balanced_map, B].
Qed.

Definition expand1 h a : raw P :=
  set_entry h (Braun.snoc (Braun.map (up_target h) (seq_of a h)) (Slot h 0)) (S (count a h))
    (Braun.cons Empty (backs_of a h)) (renumber_up h a).

Lemma find_expand1 h a h' :
  keys_ok a = true ->
  find (expand1 h a) h'
  = if label_eqb h' h then (map (up_target h) (fst (find a h)) ++ [Slot h 0], S (count a h))
    else (map (up_target h) (fst (find a h')), count a h').
Proof.
  intros Hk; unfold expand1; rewrite find_set_entry, find_renumber_up.
  destruct (label_eqb h' h); cbn [fst snd];
    rewrite ?(proj2 (Braun.snoc_spec _ _ (Braun.balanced_map _ _ (keys_ok_balanced a h Hk)))),
      ?Braun.to_list_map, ?elems_seq_of, ?count_find; reflexivity.
Qed.

Lemma count_expand1 h a h' :
  count (expand1 h a) h' = if label_eqb h' h then S (count a h) else count a h'.
Proof.
  rewrite count_find at 1; unfold expand1; rewrite find_set_entry, find_renumber_up.
  destruct (label_eqb h' h); cbn [snd]; rewrite ?count_find; reflexivity.
Qed.

Lemma resolve_up h a t : resolve (expand1 h a) (up_target h t) = resolve a t.
Proof.
  destruct t as [h' n|p]; cbn [up_target]; [|reflexivity].
  destruct (label_eqb_spec h' h) as [->|Hne]; cbn [resolve]; rewrite count_expand1.
  - rewrite label_eqb_refl; do 2 f_equal; lia.
  - rewrite (proj2 (label_eqb_neq h' h) Hne); reflexivity.
Qed.

Lemma keys_ok_expand1 h a : keys_ok a = true -> keys_ok (expand1 h a) = true.
Proof.
  intros Hk; apply keys_ok_set_entry; [|apply keys_ok_renumber_up, Hk].
  apply (proj1 (Braun.snoc_spec _ _ (Braun.balanced_map _ _ (keys_ok_balanced a h Hk)))).
Qed.

Theorem apply_expand1 h a v : keys_ok a = true -> apply (expand1 h a) v = apply a v.
Proof.
  intros Hk; unfold apply at 1; rewrite find_expand1, count_expand1 by exact Hk.
  destruct v as [hv i]; cbn [v_label v_index].
  destruct (label_eqb_spec hv h) as [->|Hl]; cbn [fst].
  - unfold apply; cbn [v_label v_index].
    destruct (Nat.lt_ge_cases i (length (fst (find a h)))) as [Hi|Hi].
    + rewrite nth_error_app1 by (rewrite length_map; exact Hi).
      rewrite nth_error_map.
      destruct (nth_error (fst (find a h)) i) eqn:E; [|apply nth_error_None in E; lia].
      apply resolve_up.
    + rewrite nth_error_app2 by (rewrite length_map; exact Hi).
      rewrite (proj2 (nth_error_None (fst (find a h)) i)) by exact Hi.
      rewrite length_map, length_app, length_map; cbn [length].
      destruct (i - length (fst (find a h))) as [|j] eqn:Ej; cbn [nth_error].
      * cbn [resolve]; rewrite count_expand1, label_eqb_refl; do 2 f_equal; lia.
      * rewrite nth_error_nil; do 2 f_equal; lia.
  - unfold apply; cbn [v_label v_index].
    rewrite nth_error_map, length_map.
    destruct (nth_error (fst (find a hv)) i); cbn [option_map]; [apply resolve_up|reflexivity].
Qed.

Theorem pre_normal_expand1 a Q h : pre_normal a Q -> Q h -> pre_normal (expand1 h a) Q.
Proof.
  intros [Hk [Hnt [Hwf Hs]]] HQh.
  assert (Hk' : keys_ok (expand1 h a) = true)
    by (apply keys_ok_set_entry; [apply (proj1 (Braun.snoc_spec _ _ (Braun.balanced_map _ _ (keys_ok_balanced a h Hk))))|apply keys_ok_renumber_up, Hk]).
  repeat split.
  - exact Hk'.
  - intros key e He; unfold expand1 in He.
    destruct (get_set_entry _ _ _ _ _ _ _ He) as [[_ [_ N]]|[_ E1]]; [exact N|].
    unfold renumber_up in E1; destruct (get_map_seq _ _ _ _ E1) as [e0 [E0 [_ ->]]].
    apply (Hnt _ _ E0).
  - intros v h' n Hn; rewrite count_expand1; rewrite find_expand1 in Hn by exact Hk.
    destruct v as [hv i]; cbn [v_label v_index] in *.
    destruct (label_eqb_spec hv h) as [->|Hl]; cbn [fst] in Hn.
    + destruct (Nat.lt_ge_cases i (length (fst (find a h)))) as [Hi|Hi].
      * rewrite nth_error_app1 in Hn by (rewrite length_map; exact Hi).
        rewrite nth_error_map in Hn.
        destruct (nth_error (fst (find a h)) i) as [t0|] eqn:E; [|discriminate].
        injection Hn as Hn.
        destruct t0 as [h0 n0|p]; cbn [up_target] in Hn; [|discriminate].
        pose proof (Hwf (mk_rvar h i) h0 n0 E) as Hw.
        destruct (label_eqb_spec h0 h) as [->|Hh]; injection Hn as <- <-.
        -- rewrite label_eqb_refl; lia.
        -- rewrite (proj2 (label_eqb_neq h0 h) Hh); exact Hw.
      * rewrite nth_error_app2 in Hn by (rewrite length_map; exact Hi).
        rewrite length_map in Hn.
        destruct (i - length (fst (find a h))) as [|j]; cbn [nth_error] in Hn;
          [|rewrite nth_error_nil in Hn; discriminate].
        injection Hn as <- <-; rewrite label_eqb_refl; lia.
    + rewrite nth_error_map in Hn.
      destruct (nth_error (fst (find a hv)) i) as [t0|] eqn:E; [|discriminate].
      injection Hn as Hn.
      destruct t0 as [h0 n0|p]; cbn [up_target] in Hn; [|discriminate].
      pose proof (Hwf (mk_rvar hv i) h0 n0 E) as Hw.
      destruct (label_eqb_spec h0 h) as [->|Hh]; injection Hn as <- <-.
      * rewrite label_eqb_refl; lia.
      * rewrite (proj2 (label_eqb_neq h0 h) Hh); exact Hw.
  - intros h' HQ.
    assert (Hne : h' <> h) by (intro E; subst; contradiction).
    apply (strip_ok_spec _ _ _ Hk'); intros Hl'.
    pose proof (Hs h' HQ) as Hs'; rewrite (strip_ok_spec _ _ _ Hk) in Hs'.
    assert (Ef : fst (find (expand1 h a) h') = map (up_target h) (fst (find a h'))).
    { rewrite find_expand1, (proj2 (label_eqb_neq h' h) Hne) by exact Hk; reflexivity. }
    rewrite Ef in Hl' |- *.
    unfold last_target in Hl'; rewrite length_map, nth_error_map in Hl'.
    destruct (nth_error (fst (find a h')) (pred (length (fst (find a h'))))) as [[h0 n0|p]|] eqn:El;
      cbn [option_map up_target] in Hl'; [|discriminate|discriminate].
    destruct (label_eqb_spec h0 h) as [->|Hh]; injection Hl' as E1 E2; [congruence|].
    subst h0 n0.
    destruct (Hs' El) as [w [Hw Hwne]].
    exists w; split; [|rewrite length_map; exact Hwne].
    rewrite find_expand1 by exact Hk.
    destruct w as [hw iw]; cbn [v_label v_index] in *.
    destruct (label_eqb_spec hw h) as [->|Hwl]; cbn [fst].
    + assert (Hwi : iw < length (fst (find a h))) by (apply nth_error_Some; congruence).
      rewrite nth_error_app1 by (rewrite length_map; exact Hwi).
      rewrite nth_error_map, Hw; cbn [option_map up_target].
      rewrite (proj2 (label_eqb_neq h' h) Hne); reflexivity.
    + rewrite nth_error_map, Hw; cbn [option_map up_target].
      rewrite (proj2 (label_eqb_neq h' h) Hne); reflexivity.
Qed.

Fixpoint expand_n (d : nat) h a : raw P :=
  match d with
  | 0 => a
  | S d' => expand1 h (expand_n d' h a)
  end.

Lemma keys_ok_expand_n d h a : keys_ok a = true -> keys_ok (expand_n d h a) = true.
Proof. intros Hk; induction d as [|d IH]; cbn [expand_n]; [exact Hk|apply keys_ok_expand1, IH]. Qed.

Lemma apply_expand_n d h a v : keys_ok a = true -> apply (expand_n d h a) v = apply a v.
Proof.
  intros Hk; induction d as [|d IH]; cbn [expand_n]; [reflexivity|].
  rewrite apply_expand1 by (apply keys_ok_expand_n, Hk); exact IH.
Qed.

Lemma count_expand_n d h a : count (expand_n d h a) h = d + count a h.
Proof.
  induction d as [|d IH]; cbn [expand_n]; [reflexivity|].
  rewrite count_expand1, label_eqb_refl, IH; reflexivity.
Qed.

Lemma pre_normal_expand_n d a Q h : pre_normal a Q -> Q h -> pre_normal (expand_n d h a) Q.
Proof.
  intros Ha HQ; induction d as [|d IH]; cbn [expand_n]; [exact Ha|].
  apply pre_normal_expand1; assumption.
Qed.

(** ** Input entries with arbitrary variable targets *)

Theorem pre_normal_cons_entry h t a Q :
  pre_normal a Q ->
  (forall h' n, t = Slot h' n -> n < count a h') ->
  pre_normal (cons_entry h t a) (fun l => Q l \/ l = h).
Proof.
  intros [Hk [Hnt [Hwf Hs]]] Ht.
  assert (Hk' : keys_ok (cons_entry h t a) = true) by (unfold cons_entry; apply keys_ok_set_entry; [apply Braun.balanced_cons, keys_ok_balanced, Hk|exact Hk]).
  repeat split.
  - exact Hk'.
  - intros key e He; unfold cons_entry in He.
    destruct (get_set_entry _ _ _ _ _ _ _ He) as [[_ [_ N]]|[_ E1]]; [exact N|apply (Hnt _ _ E1)].
  - intros v h' n Hn; rewrite count_cons_entry.
    rewrite find_cons_entry in Hn.
    destruct v as [hv i]; cbn [v_label v_index] in Hn.
    destruct (label_eqb_spec hv h) as [->|]; cbn [fst] in Hn.
    + destruct i as [|i]; cbn [nth_error] in Hn; [injection Hn as ->; apply Ht; reflexivity|].
      apply (Hwf (mk_rvar h i)), Hn.
    + apply (Hwf (mk_rvar hv i)), Hn.
  - intros h' Hn'.
    assert (HQ : ~ Q h') by (intro; apply Hn'; left; assumption).
    assert (Hne : h' <> h) by (intro; apply Hn'; right; assumption).
    apply (strip_ok_spec _ _ _ Hk'); intros Hl.
    pose proof (Hs h' HQ) as Hs'; rewrite (strip_ok_spec _ _ _ Hk) in Hs'.
    assert (Ef : fst (find (cons_entry h t a) h') = fst (find a h')).
    { rewrite find_cons_entry, (proj2 (label_eqb_neq h' h) Hne); reflexivity. }
    rewrite Ef in Hl |- *.
    destruct (Hs' Hl) as [w [Hw Hwne]].
    destruct (label_eq_dec (v_label w) h) as [Hwl|Hwl].
    + exists (mk_rvar h (S (v_index w))); split.
      * rewrite find_cons_entry; cbn [v_label v_index]; rewrite label_eqb_refl; cbn [fst nth_error].
        rewrite <- Hwl; exact Hw.
      * intro E; injection E as E1 _; congruence.
    + exists w; split; [|exact Hwne].
      rewrite find_cons_entry, (proj2 (label_eqb_neq _ h) Hwl); exact Hw.
Qed.

Lemma pre_normal_fix a Q x :
  pre_normal a Q -> strip_ok a x (fst (find a x)) = true ->
  pre_normal a (fun l => Q l /\ l <> x).
Proof.
  intros [Hk [Hnt [Hwf Hs]]] Hx; repeat split; auto.
  intros h' H; destruct (label_eq_dec h' x) as [->|Hne]; [exact Hx|].
  apply Hs; intro; apply H; split; assumption.
Qed.

Lemma strip_ok_cons_ref h h' a :
  keys_ok a = true -> h' <> h ->
  strip_ok (cons_entry h (Slot h' 0) a) h' (fst (find (cons_entry h (Slot h' 0) a) h')) = true.
Proof.
  intros Hk Hne; apply strip_ok_spec; [unfold cons_entry; apply keys_ok_set_entry; [apply Braun.balanced_cons, keys_ok_balanced, Hk|exact Hk]|].
  intros _; exists (mk_rvar h 0); split.
  - rewrite find_cons_entry; cbn [v_label v_index]; rewrite label_eqb_refl; reflexivity.
  - intro E; injection E as E _; congruence.
Qed.

(** [push_inner_var h w a] sends the innermost [h] to the variable [w] and
    passes everything else to [a]; [w] may be any variable. *)
Definition push_inner_var h (w : rvar) a : raw P :=
  let d := S (v_index w) - count a (v_label w) in
  let a' := if Nat.eqb d 0 then a else relink (expand_n d (v_label w) a) in
  push_inner h (Slot (v_label w) (count a' (v_label w) - S (v_index w))) a'.

Lemma shape_cons_entry h t a b : same_shape a b -> same_shape (cons_entry h t a) (cons_entry h t b).
Proof.
  intros H key; unfold cons_entry, set_entry; rewrite !get_update.
  rewrite (shape_seq_of a b h H), (shape_count a b h H).
  destruct (Pos.eqb key (label_key h)); [|apply H].
  destruct (nontrivial_seq _ _); reflexivity.
Qed.

Theorem push_inner_var_spec h w a :
  normal a = true -> linked a = true ->
  normal (push_inner_var h w a) = true /\ linked (push_inner_var h w a) = true
  /\ (forall v, apply (push_inner_var h w a) v
                = if rvar_eqb v (mk_rvar h 0) then inl w
                  else apply a (unshift_rvar (mk_rvar h 0) v)).
Proof.
  intros Ha La; apply linked_spec in La; [|apply normal_slots_ok, Ha].
  destruct w as [h' i]; unfold push_inner_var; cbn [v_label v_index].
  set (d := S i - count a h'); set (a'' := expand_n d h' a).
  assert (Hc : count a'' h' = d + count a h') by apply count_expand_n.
  pose proof (proj1 (normal_iff a h') Ha) as [Han _].
  pose proof (pre_normal_expand_n d a _ h' Han eq_refl) as Ha''; fold a'' in Ha''.
  set (a' := if Nat.eqb d 0 then a else relink a'').
  assert (Hs : same_shape a' a'').
  { unfold a'; destruct (Nat.eqb_spec d 0) as [E|]; [|apply shape_relink].
    unfold a''; rewrite E; intro; reflexivity. }
  assert (So : slots_ok a') by (apply (pre_normal_slots_ok _ _ (shape_pre_normal _ _ _ (same_shape_sym _ _ Hs) Ha''))).
  assert (La' : linked_prop a').
  { unfold a'; destruct (Nat.eqb d 0); [exact La|apply relink_spec, (pre_normal_slots_ok _ _ Ha'')]. }
  rewrite (shape_count _ _ _ Hs), Hc.
  set (t := Slot h' (d + count a h' - S i)).
  assert (Ht : forall g n, t = Slot g n -> n < count a' g)
    by (intros g n [= <- <-]; rewrite (shape_count _ _ _ Hs), Hc; unfold d; lia).
  assert (Hpre : pre_normal (cons_entry h t a'') (fun l => l = h)).
  { destruct d as [|d'] eqn:Ed.
    - assert (Hi : i < count a h') by lia.
      subst a''; cbn [expand_n] in *.
      apply almost_normal_cons_entry; [exact Ha|].
      intros h0 n0 [= <- <-]; lia.
    - assert (Ht0 : t = Slot h' 0) by (unfold t; f_equal; lia).
      pose proof (pre_normal_cons_entry h t a'' _ Ha'') as Hc'.
      assert (Hb : forall h0 n0, t = Slot h0 n0 -> n0 < count a'' h0)
        by (rewrite Ht0; intros h0 n0 [= <- <-]; lia).
      specialize (Hc' Hb).
      destruct (label_eq_dec h' h) as [->|Hne].
      + apply (pre_normal_mono _ _ _ Hc'); intros x Hx [H|H]; apply Hx; exact H.
      + rewrite Ht0 in Hc' |- *.
        pose proof (pre_normal_fix _ _ h' Hc') as Hf.
        assert (Hk' : keys_ok a'' = true) by (destruct Ha'' as [X _]; exact X).
        specialize (Hf (strip_ok_cons_ref h h' a'' Hk' Hne)).
        apply (pre_normal_mono _ _ _ Hf); intros x Hx [[H|H] Hx']; [contradiction|apply Hx, H]. }
  assert (H4 : strip_ok a' h (fst (find a' h)) = true \/ t = Slot h 0).
  { unfold a'; destruct (Nat.eqb_spec d 0) as [E|E].
    - left; apply (proj1 (normal_iff a h) Ha).
    - destruct (label_eq_dec h' h) as [->|Hne]; [right; unfold t; f_equal; unfold d in *; lia|left].
      rewrite (shape_find _ a'' _ (shape_relink _)), (shape_strip_ok _ a'' _ _ (shape_relink _)).
      destruct Ha'' as [_ [_ [_ Hs'']]]; apply Hs''; intro E'; apply Hne; symmetry; exact E'. }
  destruct (push_inner_spec h t a' So La' Ht
              (shape_pre_normal _ _ _ (shape_cons_entry h t _ _ (same_shape_sym _ _ Hs)) Hpre) H4)
    as [Hn [Hl Happ]].
  split; [exact Hn|split; [apply linked_spec; [apply normal_slots_ok, Hn|exact Hl]|]].
  intros v; rewrite Happ, apply_cons_entry.
  destruct (rvar_eqb v (mk_rvar h 0)).
  - unfold t; cbn [resolve]; rewrite (shape_count _ _ _ Hs), Hc; do 2 f_equal; unfold d; lia.
  - rewrite (shape_apply _ _ _ Hs); apply apply_expand_n, normal_keys_ok, Ha.
Qed.

Lemma binds_in_expand1 h (m : raw P) p : binds_in (expand1 h m) p -> binds_in m p.
Proof.
  intros H; unfold expand1 in H; apply binds_in_set_entry in H as [H|H].
  - destruct H as [k [e [He Hin]]]; unfold renumber_up in He; rewrite get_map_filter in He.
    destruct (get k m) as [e0|] eqn:E0; [|discriminate]; injection He as <-.
    unfold e_targets in Hin; cbn [e_tree] in Hin; rewrite Braun.to_list_map in Hin; apply in_map_iff in Hin as [t [Ht Hin]].
    exists k, e0; split; [exact E0|].
    destruct t as [h' n|p']; cbn in Ht; [destruct (label_eqb h' h); discriminate|].
    injection Ht as ->; exact Hin.
  - apply Braun.in_snoc in H as [H|H]; [discriminate|].
    rewrite Braun.to_list_map, elems_seq_of in H.
    apply in_map_iff in H as [t [Ht Hin]].
    destruct t as [h' n|p']; cbn in Ht; [destruct (label_eqb h' h); discriminate|].
    injection Ht as ->; apply (binds_in_find m h), Hin.
Qed.

Lemma binds_in_expand_n d h (m : raw P) p : binds_in (expand_n d h m) p -> binds_in m p.
Proof.
  induction d as [|d IH]; cbn [expand_n]; [auto|].
  intros H; apply IH, (binds_in_expand1 h), H.
Qed.

Lemma binds_in_push_inner_var h w (m : raw P) p :
  binds_in (push_inner_var h w m) p -> binds_in m p.
Proof.
  unfold push_inner_var; intros H.
  apply binds_in_push_inner in H as [H|H]; [|discriminate].
  destruct (Nat.eqb _ 0); [exact H|].
  apply (binds_in_shape _ _ _ (shape_relink _)), binds_in_expand_n in H; exact H.
Qed.

(** ** Conditions on every target *)

Lemma tall_targets (Pt : target P -> bool) a :
  keys_ok a = true ->
  tall (fun e => Braun.ball Pt (e_tree e)) a = true
  <-> (forall h i t, nth_error (fst (find a h)) i = Some t -> Pt t = true).
Proof.
  intros Hk; rewrite tall_spec; split.
  - intros H h i t E; unfold find in E.
    destruct (get (label_key h) a) as [e|] eqn:He; cbn [fst] in E;
      [|rewrite nth_error_nil in E; discriminate].
    specialize (H _ _ He); rewrite Braun.ball_spec in H.
    apply H, (nth_error_In _ _ E).
  - intros H k e He; apply Braun.ball_spec; intros t Hin.
    apply In_nth_error in Hin as [i Hi].
    pose proof (proj1 (proj1 (keys_ok_spec a) Hk _ _ He)) as Hkey.
    apply (H (e_label e) i); unfold find; rewrite <- Hkey, He; exact Hi.
Qed.

End Slots.
