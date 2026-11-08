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
Import ListNotations.

Inductive target (P : Type) : Type :=
| Slot : option label -> nat -> target P
| Bind : P -> target P.

Arguments Slot {P} _ _.
Arguments Bind {P} _.

Record entry (P : Type) : Type :=
  mk_entry { e_label : option label; e_targets : list (target P); e_out : nat }.

Arguments mk_entry {P} _ _ _.
Arguments e_label {P} _.
Arguments e_targets {P} _.
Arguments e_out {P} _.

Definition raw (P : Type) : Type := tree (entry P).

Section Slots.

Context {P : Type}.

Implicit Types (a b : raw P) (h l : option label) (v w : var) (t : target P)
  (ts : list (target P)).

(** ** Semantics *)

Definition find a h : list (target P) * nat :=
  match get (label_key h) a with
  | Some e => (e_targets e, e_out e)
  | None => ([], 0)
  end.

Definition count a h : nat := snd (find a h).

Definition resolve a t : var + P :=
  match t with
  | Slot h l => inl (mk_var h (count a h - S l))
  | Bind p => inr p
  end.

Definition apply a v : var + P :=
  match nth_error (fst (find a (v_label v))) (v_index v) with
  | Some t => resolve a t
  | None => inl (mk_var (v_label v)
                   (v_index v - length (fst (find a (v_label v))) + count a (v_label v)))
  end.

(** ** Normal forms *)

Definition is_slot h (n : nat) t : bool :=
  match t with
  | Slot h' n' => label_eqb h' h && Nat.eqb n' n
  | Bind _ => false
  end.

(** All slot references, with the input variable they belong to. *)
Definition refs_of_entry (e : entry P) : list (var * option label * nat) :=
  let fix go (ts : list (target P)) (i : nat) :=
    match ts with
    | [] => []
    | Slot h' n :: ts' => (mk_var (e_label e) i, h', n) :: go ts' (S i)
    | Bind _ :: ts' => go ts' (S i)
    end in
  go (e_targets e) 0.

Definition refs a : list (var * option label * nat) :=
  flat_map (fun ke => refs_of_entry (snd ke)) (elements a).

Definition slot_wf a (r : var * option label * nat) : bool :=
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
                              && negb (var_eqb v (mk_var h (pred (length ts))))
                          | _ => false
                          end) (refs a)
      else true
  | _ => true
  end.

Definition nontrivial ts (k : nat) : bool :=
  match ts, k with [], 0 => false | _, _ => true end.

Definition entry_ok a (key : positive) (e : entry P) : bool :=
  Pos.eqb key (label_key (e_label e))
  && nontrivial (e_targets e) (e_out e)
  && strip_ok a (e_label e) (e_targets e).

Definition normal a : bool := forallb (entry_ok a) a && List.forallb (slot_wf a) (refs a).

(** ** Basic facts *)

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

Lemma find_label a h e :
  normal a = true -> get (label_key h) a = Some e -> e_label e = h.
Proof. intros Ha He; apply label_key_inj; symmetry; apply (normal_label a _ e Ha He). Qed.

Lemma go_refs (e : entry P) ts i v h' n :
  In (v, h', n)
    ((fix go (ts : list (target P)) (i : nat) :=
        match ts with
        | [] => []
        | Slot h' n :: ts' => (mk_var (e_label e) i, h', n) :: go ts' (S i)
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

Definition jlen a h : nat := length (fst (find a h)).

(** In a normal adjustment, every outer [h₍ₘ₎] beyond the slots has exactly
    one preimage, the pass-through input. *)
Theorem tail_passthrough a h m :
  normal a = true -> count a h <= m ->
  forall v, apply a v = inl (mk_var h m) <-> v = mk_var h (m + jlen a h - count a h).
Proof.
  intros Ha Hm v; unfold apply, jlen; split.
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
  resolve a t = inl (mk_var h k) ->
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
  ~ (forall v, apply a v = inl (mk_var h (count a h - 1))
               <-> v = mk_var h (count a h - 1 + jlen a h - count a h)).
Proof.
  intros Ha Hk H.
  unfold jlen in H.
  destruct (find a h) as [ts k] eqn:Ef.
  unfold count in *; rewrite Ef in *; cbn [fst snd] in *.
  destruct ts as [|t0 ts0] eqn:Ets.
  - (* no input entries: the candidate preimage passes through elsewhere *)
    cbn [length] in H; replace (k - 1 + 0 - k) with 0 in H by lia.
    specialize (proj2 (H (mk_var h 0)) eq_refl) as Happ.
    unfold apply in Happ; cbn [v_label v_index] in Happ.
    rewrite Ef in Happ; cbn [fst nth_error length] in Happ.
    unfold count in Happ; rewrite Ef in Happ; cbn in Happ.
    injection Happ; lia.
  - rewrite <- Ets in *.
    set (jj := length ts) in *.
    assert (Hj : 0 < jj) by (subst jj ts; cbn; lia).
    replace (k - 1 + jj - k) with (pred jj) in H by lia.
    specialize (proj2 (H (mk_var h (pred jj))) eq_refl) as Happ.
    unfold apply in Happ; cbn [v_label v_index] in Happ; rewrite Ef in Happ; cbn [fst] in Happ.
    destruct (nth_error ts (pred jj)) as [t|] eqn:Et;
      [|apply nth_error_None in Et; subst jj; lia].
    apply resolve_slot_inv in Happ as [n [-> Hn]].
    unfold count in Hn; rewrite Ef in Hn; cbn [snd] in Hn.
    assert (Hb : n < k).
    { pose proof (slot_bound a (mk_var h (pred jj)) h n Ha) as Hsb.
      cbn [v_label v_index] in Hsb; rewrite Ef in Hsb; unfold count in Hsb.
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
    assert (Happ' : apply a v' = inl (mk_var h (k - 1))).
    { unfold apply; rewrite Hin; cbn [resolve].
      unfold count, find; rewrite Ee; cbn [snd]; rewrite Hk'; do 2 f_equal; lia. }
    apply H in Happ'; rewrite Happ', var_eqb_refl in Hv'; discriminate.
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

Theorem canonical a b :
  normal a = true -> normal b = true ->
  (forall v, apply a v = apply b v) -> a = b.
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
    unfold count, jlen in Hk, Hj; rewrite Ea, Eb in Hk, Hj; cbn in Hk, Hj; subst kb.
    f_equal; apply nth_error_ext; intro i.
    destruct (nth_error tsa i) as [ta|] eqn:Ta, (nth_error tsb i) as [tb|] eqn:Tb.
    - f_equal; specialize (Heq (mk_var h i)); unfold apply in Heq; cbn [v_label v_index] in Heq.
      rewrite Ea, Eb in Heq; cbn [fst] in Heq; rewrite Ta, Tb in Heq.
      apply (resolve_inj a b ta tb Ha Hb Hcnt); [| |exact Heq].
      + intros h' n ->; apply (slot_bound a (mk_var h i) h' n Ha); cbn; rewrite Ea; exact Ta.
      + intros h' n ->; apply (slot_bound b (mk_var h i) h' n Hb); cbn; rewrite Eb; exact Tb.
    - apply nth_error_None in Tb; assert (i < length tsa) by (apply nth_error_Some; congruence); lia.
    - apply nth_error_None in Ta; assert (i < length tsb) by (apply nth_error_Some; congruence); lia.
    - reflexivity. }
  apply extensionality; intro key.
  destruct (get key a) as [ea|] eqn:Ea, (get key b) as [eb|] eqn:Eb.
  - pose proof (normal_label a _ _ Ha Ea) as Ka; pose proof (normal_label b _ _ Hb Eb) as Kb.
    rewrite Ka in Kb; apply label_key_inj in Kb.
    specialize (Hfind (e_label ea)); unfold find in Hfind.
    rewrite <- Ka, Ea, Eb in Hfind; injection Hfind as Ht Ho.
    destruct ea, eb; cbn in *; subst; reflexivity.
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
                    | Some e => mk_entry h (e_targets e) (S (e_out e))
                    | None => mk_entry h [] 1
                    end)) a.

Lemma find_push_outer h a h' :
  normal a = true ->
  find (push_outer h a) h'
  = if label_eqb h' h then (fst (find a h), S (count a h)) else find a h'.
Proof.
  intros Ha; unfold find at 1, push_outer; rewrite get_update, label_key_eqb.
  unfold count, find; destruct (label_eqb_spec h' h) as [->|]; [|reflexivity].
  destruct (get (label_key h) a); reflexivity.
Qed.

Lemma count_push_outer h a h' :
  normal a = true ->
  count (push_outer h a) h' = if label_eqb h' h then S (count a h) else count a h'.
Proof.
  intros Ha; unfold count at 1; rewrite find_push_outer by exact Ha.
  destruct (label_eqb h' h); reflexivity.
Qed.

Theorem apply_push_outer h a v :
  normal a = true ->
  apply (push_outer h a) v
  = match apply a v with
    | inl w => inl (shift_var (mk_var h 0) w)
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
               | inl w => inl (shift_var (mk_var h 0) w)
               | inr p => inr p
               end).
  { intros hv' i' h' n Et; cbn [resolve]; rewrite count_push_outer by exact Ha.
    pose proof (slot_bound a (mk_var hv' i') h' n Ha Et) as Hb.
    unfold shift_var; cbn [v_label v_index]; rewrite (label_eqb_sym h h').
    destruct (label_eqb_spec h' h) as [->|]; cbn [andb Nat.leb]; [do 2 f_equal; lia|reflexivity]. }
  destruct (label_eqb_spec hv h) as [->|Hne]; cbn [fst snd].
  - destruct (nth_error (fst (find a h)) i) as [[h' n|p]|] eqn:Et.
    + apply (Hslot h i h' n Et).
    + reflexivity.
    + unfold shift_var; cbn [v_label v_index]; rewrite label_eqb_refl; cbn [andb Nat.leb].
      apply nth_error_None in Et; do 2 f_equal; lia.
  - destruct (nth_error (fst (find a hv)) i) as [[h' n|p]|] eqn:Et.
    + apply (Hslot hv i h' n Et).
    + reflexivity.
    + unfold shift_var; cbn [v_label v_index].
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
    + destruct (get (label_key h) a) as [e0|] eqn:E0; injection He as <-;
        cbn [e_label e_targets e_out nontrivial]; rewrite Pos.eqb_refl; cbn [andb];
        [|reflexivity].
      pose proof (normal_entries a Ha) as Hn; rewrite forallb_spec in Hn.
      specialize (Hn _ _ E0); unfold entry_ok, strip_ok in Hn.
      rewrite !andb_true_iff in Hn; destruct Hn as [_ Hs].
      rewrite (find_label a h e0 Ha E0) in Hs.
      destruct (e_targets e0); exact Hs.
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
  map_filter (fun _ e => Some (mk_entry (e_label e) (map (renumber_target h) (e_targets e))
                                        (e_out e))) a.

Definition set_entry h ts (k : nat) a : raw P :=
  update (label_key h)
    (fun _ => if nontrivial ts k then Some (mk_entry h ts k) else None) a.

Definition strip_once h a : raw P :=
  renumber h (set_entry h (removelast (fst (find a h))) (pred (count a h)) a).

Lemma find_set_entry h ts k a h' :
  find (set_entry h ts k a) h' = if label_eqb h' h then (ts, k) else find a h'.
Proof.
  unfold find at 1, set_entry; rewrite get_update, label_key_eqb.
  destruct (label_eqb h' h); [|reflexivity].
  destruct ts, k; reflexivity.
Qed.

Lemma find_renumber h a h' :
  find (renumber h a) h' = (map (renumber_target h) (fst (find a h')), snd (find a h')).
Proof.
  unfold find, renumber; rewrite get_map_filter.
  destruct (get (label_key h') a); reflexivity.
Qed.

Lemma count_strip_once h a h' :
  count (strip_once h a) h' = if label_eqb h' h then pred (count a h) else count a h'.
Proof.
  unfold count at 1, strip_once; rewrite find_renumber, find_set_entry; cbn [snd].
  destruct (label_eqb h' h); reflexivity.
Qed.

Lemma find_strip_once h a h' :
  find (strip_once h a) h'
  = (map (renumber_target h)
         (if label_eqb h' h then removelast (fst (find a h)) else fst (find a h')),
     if label_eqb h' h then pred (count a h) else count a h').
Proof.
  unfold strip_once; rewrite find_renumber, find_set_entry.
  destruct (label_eqb h' h); reflexivity.
Qed.

(** The condition under which [strip_once] is applied. *)
Definition strippable a h : Prop :=
  last_target (fst (find a h)) = Some (Slot h 0)
  /\ (forall v, nth_error (fst (find a (v_label v))) (v_index v) = Some (Slot h 0) ->
                v = mk_var h (pred (length (fst (find a h)))))
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
  strippable a h -> apply (strip_once h a) v = apply a v.
Proof.
  intros [Hlast [Huniq Hwf]].
  unfold last_target in Hlast.
  set (ts := fst (find a h)) in *; set (k := count a h).
  assert (Hk : 0 < k).
  { pose proof (Hwf (mk_var h (pred (length ts))) h 0) as Hw; cbn in Hw.
    apply Hw, Hlast. }
  assert (Hlen : 0 < length ts) by (destruct ts; [discriminate|cbn; lia]).
  unfold apply; destruct v as [hv i]; cbn [v_label v_index].
  rewrite find_strip_once, count_strip_once; cbn [fst snd].
  assert (Hres : forall h' n, (forall v, nth_error (fst (find a (v_label v))) (v_index v)
                                           = Some (Slot h' n) -> True) ->
                 True) by auto.
  clear Hres.
  (* resolution of a renumbered slot reference that is not the stripped one *)
  assert (Hr : forall w h' n,
             nth_error (fst (find a (v_label w))) (v_index w) = Some (Slot h' n) ->
             w <> mk_var h (pred (length ts)) ->
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
      apply (Hr (mk_var h i) h' n E); intro H; injection H; lia.
    + rewrite (proj2 (nth_error_None (removelast ts) i)) by (rewrite length_removelast; lia).
      destruct (Nat.eq_dec i (pred (length ts))) as [->|Hi'].
      * rewrite Hlast; cbn [resolve option_map]; fold k; do 2 f_equal; lia.
      * rewrite (proj2 (nth_error_None ts i)) by lia; cbn [option_map]; do 2 f_equal; lia.
  - rewrite nth_error_map, length_map.
    destruct (nth_error (fst (find a hv)) i) as [[h' n|p]|] eqn:E; cbn [option_map];
      [| reflexivity | reflexivity].
    apply (Hr (mk_var hv i) h' n E); intro H; injection H; congruence.
Qed.

End Slots.
