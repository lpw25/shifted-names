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

(** ** Normal forms in terms of [find] *)

Definition keys_ok a : bool :=
  forallb (fun key e => Pos.eqb key (label_key (e_label e))) a.

Lemma normal_keys_ok a : normal a = true -> keys_ok a = true.
Proof.
  intros Ha; unfold keys_ok; apply forallb_spec; intros key e He.
  apply Pos.eqb_eq, (normal_label a key e Ha He).
Qed.

Lemma keys_ok_label a h e : keys_ok a = true -> get (label_key h) a = Some e -> e_label e = h.
Proof.
  unfold keys_ok; rewrite forallb_spec; intros Ha He.
  apply label_key_inj; symmetry; apply Pos.eqb_eq, (Ha _ _ He).
Qed.

Lemma In_refs_keys a v h' n :
  keys_ok a = true ->
  In (v, h', n) (refs a) <-> nth_error (fst (find a (v_label v))) (v_index v) = Some (Slot h' n).
Proof.
  intros Ha; rewrite In_refs_gen; split.
  - intros [key [e [He [Hl Hn]]]].
    unfold keys_ok in Ha; rewrite forallb_spec in Ha.
    pose proof (Ha _ _ He) as Hk; apply Pos.eqb_eq in Hk.
    unfold find; rewrite Hl, <- Hk, He; exact Hn.
  - intros Hn; unfold find in Hn.
    destruct (get (label_key (v_label v)) a) as [e|] eqn:E; [|rewrite nth_error_nil in Hn; discriminate].
    exists (label_key (v_label v)), e; repeat split; [exact E| |exact Hn].
    symmetry; apply (keys_ok_label a _ e Ha E).
Qed.

Definition other_ref a h (ts : list (target P)) : Prop :=
  exists v, nth_error (fst (find a (v_label v))) (v_index v) = Some (Slot h 0)
            /\ v <> mk_var h (pred (length ts)).

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
      intro Heq; rewrite Heq, var_eqb_refl in Hv; discriminate.
    + intros H; destruct (H eq_refl) as [v [Hn Hv]].
      exists (v, h, 0); split; [apply (In_refs_keys a v h 0 Ha), Hn|].
      rewrite label_eqb_refl; cbn [andb].
      destruct (var_eqb_spec v (mk_var h (pred (length ts)))); [contradiction|reflexivity].
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
      unfold keys_ok in Hk; rewrite forallb_spec in Hk.
      pose proof (Hk _ _ E) as Hkey; apply Pos.eqb_eq in Hkey.
      unfold entry_ok; rewrite Hkey, Pos.eqb_refl, (Hnt _ _ E); cbn [andb].
      assert (Ef : fst (find a (e_label e)) = e_targets e)
        by (unfold find; rewrite <- Hkey, E; reflexivity).
      destruct (label_eq_dec (e_label e) h) as [Heq|Hne].
      * rewrite <- Ef, Heq; exact Hsh.
      * rewrite <- Ef; apply Hs, Hne.
    + apply List.forallb_forall; intros [[v h'] n] Hin; cbn [slot_wf].
      apply Nat.ltb_lt, (Hwf v), (In_refs_keys a v h' n Hk), Hin.
Qed.

(** ** The strip step preserves the invariant *)

Lemma keys_ok_set_entry h ts k a :
  keys_ok a = true -> keys_ok (set_entry h ts k a) = true.
Proof.
  unfold keys_ok; rewrite !forallb_spec; intros Ha key e He.
  unfold set_entry in He; rewrite get_update in He.
  destruct (Pos.eqb_spec key (label_key h)) as [->|]; [|apply (Ha _ _ He)].
  destruct (nontrivial ts k); [injection He as <-; apply Pos.eqb_refl|discriminate].
Qed.

Lemma keys_ok_renumber h a : keys_ok a = true -> keys_ok (renumber h a) = true.
Proof.
  unfold keys_ok; rewrite !forallb_spec; intros Ha key e He.
  unfold renumber in He; rewrite get_map_filter in He.
  destruct (get key a) as [e0|] eqn:E0; [|discriminate]; injection He as <-; apply (Ha _ _ E0).
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
  intros v Hv; destruct (var_eq_dec v (mk_var h (pred (length (fst (find a h)))))) as [E|E];
    [exact E|].
  exfalso; apply Hn; intros _; exists v; auto.
Qed.

Lemma find_strip_once_nth h a v i t :
  nth_error (fst (find (strip_once h a) (v_label v))) i = Some t ->
  exists t0, nth_error (fst (find a (v_label v))) i = Some t0 /\ t = renumber_target h t0
             /\ (v_label v = h -> i < pred (length (fst (find a h)))).
Proof.
  intros Ht; rewrite find_strip_once in Ht; cbn [fst] in Ht.
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
  - apply keys_ok_renumber, keys_ok_set_entry, Hk.
  - intros key e He; unfold strip_once, renumber in He; rewrite get_map_filter in He.
    destruct (get key (set_entry h _ _ a)) as [e0|] eqn:E0; [|discriminate].
    injection He as <-; cbn [e_targets e_out].
    unfold set_entry in E0; rewrite get_update in E0.
    destruct (Pos.eqb_spec key (label_key h)) as [->|].
    + destruct (nontrivial _ _) eqn:Hn; [|discriminate]; injection E0 as <-; cbn in *.
      destruct (removelast _), (pred _); cbn in *; auto.
    + specialize (Hnt _ _ E0); destruct (e_targets e0), (e_out e0); auto.
  - intros v h' n Hn.
    destruct (find_strip_once_nth h a v (v_index v) _ Hn) as [t0 [Ht0 [Heq Hlt]]].
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
    pose proof (keys_ok_renumber h _ (keys_ok_set_entry h (removelast (fst (find a h)))
                                         (pred (count a h)) a Hk)) as Hk'.
    apply (strip_ok_spec _ _ _ Hk'); intros Hl'.
    pose proof (Hs h' HQ) as Hs'; rewrite (strip_ok_spec _ _ _ Hk) in Hs'.
    assert (Ef : fst (find (strip_once h a) h') = map (renumber_target h) (fst (find a h'))).
    { rewrite find_strip_once; cbn [fst]; rewrite (proj2 (label_eqb_neq h' h) Hne); reflexivity. }
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
      rewrite find_strip_once; cbn [fst]; rewrite Hwl, label_eqb_refl.
      rewrite nth_error_map, removelast_nth by exact Hwi.
      rewrite Hwl in Hw; rewrite Hw; cbn [option_map renumber_target].
      rewrite (proj2 (label_eqb_neq h' h) Hne); reflexivity.
    + rewrite find_strip_once; cbn [fst]; rewrite (proj2 (label_eqb_neq _ h) Hwl).
      rewrite nth_error_map, Hw; cbn [option_map renumber_target].
      rewrite (proj2 (label_eqb_neq h' h) Hne); reflexivity.
Qed.


(** ** Adding an input entry *)

Definition cons_entry h t a : raw P :=
  set_entry h (t :: fst (find a h)) (count a h) a.

Lemma find_cons_entry h t a h' :
  find (cons_entry h t a) h'
  = if label_eqb h' h then (t :: fst (find a h), count a h) else find a h'.
Proof. apply find_set_entry. Qed.

Lemma count_cons_entry h t a h' : count (cons_entry h t a) h' = count a h'.
Proof.
  unfold count at 1; rewrite find_cons_entry.
  destruct (label_eqb_spec h' h) as [->|]; reflexivity.
Qed.

Lemma resolve_cons_entry h t a t' : resolve (cons_entry h t a) t' = resolve a t'.
Proof. destruct t'; cbn [resolve]; rewrite ?count_cons_entry; reflexivity. Qed.

Theorem apply_cons_entry h t a v :
  apply (cons_entry h t a) v
  = if var_eqb v (mk_var h 0) then resolve a t else apply a (unshift_var (mk_var h 0) v).
Proof.
  unfold apply; rewrite !find_cons_entry, count_cons_entry.
  destruct v as [hv i]; unfold var_eqb, unshift_var; cbn [v_label v_index].
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
  assert (Hk' : keys_ok (cons_entry h t a) = true) by apply keys_ok_set_entry, Hk.
  repeat split.
  - exact Hk'.
  - intros key e He; unfold cons_entry, set_entry in He; rewrite get_update in He.
    destruct (Pos.eqb_spec key (label_key h)) as [->|]; [|apply (Hnt _ _ He)].
    injection He as <-; reflexivity.
  - intros v h' n Hn; rewrite count_cons_entry.
    rewrite find_cons_entry in Hn.
    destruct v as [hv i]; cbn [v_label v_index] in Hn.
    destruct (label_eqb_spec hv h) as [->|]; cbn [fst] in Hn.
    + destruct i as [|i]; cbn [nth_error] in Hn; [injection Hn as ->; apply Ht; reflexivity|].
      apply (Hwf (mk_var h i)), Hn.
    + apply (Hwf (mk_var hv i)), Hn.
  - intros h' Hne.
    apply (strip_ok_spec _ _ _ Hk'); intros Hl.
    pose proof (Hs h' Hne) as Hs'; rewrite (strip_ok_spec _ _ _ Hk) in Hs'.
    assert (Ef : fst (find (cons_entry h t a) h') = fst (find a h')).
    { rewrite find_cons_entry, (proj2 (label_eqb_neq h' h) Hne); reflexivity. }
    rewrite Ef in Hl |- *.
    destruct (Hs' Hl) as [w [Hw Hwne]].
    destruct (label_eq_dec (v_label w) h) as [Hwl|Hwl].
    + exists (mk_var h (S (v_index w))); split.
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
    + unfold jlen in *; rewrite find_strip_once, label_eqb_refl; cbn [fst].
      rewrite length_map, length_removelast.
      destruct Hst as [Hl _]; unfold last_target in Hl.
      assert (0 < length (fst (find a h))) by (destruct (fst (find a h)); [discriminate|cbn; lia]).
      lia.
    + split; [exact Hn|]; intro v; rewrite Happ; apply apply_strip_once, Hst.
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

(** [push_inner h t a] adds the input entry [h ↦ t] in front of [a]; [t]
    refers to a slot of [a] or is a payload. *)
Definition push_inner h t a : raw P :=
  strip_loop (S (S (jlen a h))) h (cons_entry h t a).

Theorem normal_push_inner h t a :
  normal a = true -> (forall h' n, t = Slot h' n -> n < count a h') ->
  normal (push_inner h t a) = true.
Proof.
  intros Ha Ht; unfold push_inner.
  apply strip_loop_spec; [apply almost_normal_cons_entry; assumption|].
  unfold jlen; rewrite find_cons_entry, label_eqb_refl; cbn; lia.
Qed.

Theorem apply_push_inner h t a v :
  normal a = true -> (forall h' n, t = Slot h' n -> n < count a h') ->
  apply (push_inner h t a) v
  = if var_eqb v (mk_var h 0) then resolve a t else apply a (unshift_var (mk_var h 0) v).
Proof.
  intros Ha Ht; unfold push_inner.
  assert (Hlen : jlen (cons_entry h t a) h < S (S (jlen a h)))
    by (unfold jlen; rewrite find_cons_entry, label_eqb_refl; cbn; lia).
  rewrite (proj2 (strip_loop_spec _ h _ (almost_normal_cons_entry h t a Ha Ht) Hlen)).
  apply apply_cons_entry.
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

Definition encode_res a b (r : var + P) : target P :=
  match r with
  | inl u => Slot (v_label u) (ext_count a b (v_label u) - S (v_index u))
  | inr p => Bind p
  end.

(** Where [b] sends the inner [h₍ᵢ₎]. *)
Definition b_image b h (i : nat) : var + P := apply b (mk_var h i).

Definition comp_target a b h (i : nat) : target P :=
  match b_image b h i with
  | inl w => encode_res a b (apply a w)
  | inr p => Bind (fp p)
  end.

Definition comp_entry a b h : option (entry P) :=
  let ts := map (comp_target a b h) (seq 0 (res_len a b h)) in
  let k := ext_count a b h in
  if nontrivial ts k then Some (mk_entry h ts k) else None.

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
  find (compose_pre a b) h = (map (comp_target a b h) (seq 0 (res_len a b h)), ext_count a b h).
Proof.
  intros Ha Hb; unfold find at 1, compose_pre; rewrite get_merge by reflexivity.
  assert (Hc : forall e, comp_entry a b h = Some e -> (e_targets e, e_out e)
                 = (map (comp_target a b h) (seq 0 (res_len a b h)), ext_count a b h)).
  { unfold comp_entry; intros e; destruct (nontrivial _ _); [intros [= <-]; reflexivity|discriminate]. }
  assert (Hn : comp_entry a b h = None ->
               ([] : list (target P), 0) = (map (comp_target a b h) (seq 0 (res_len a b h)), ext_count a b h)).
  { unfold comp_entry; destruct (map _ _) as [|t ts] eqn:E, (ext_count a b h) as [|k];
      cbn [nontrivial]; try discriminate; intros _; reflexivity. }
  destruct (get (label_key h) a) as [ea|] eqn:Ea, (get (label_key h) b) as [eb|] eqn:Eb.
  - rewrite (find_label a h ea Ha Ea).
    destruct (comp_entry a b h) as [e|] eqn:E; [apply Hc; reflexivity|apply Hn; reflexivity].
  - rewrite (find_label a h ea Ha Ea).
    destruct (comp_entry a b h) as [e|] eqn:E; [apply Hc; reflexivity|apply Hn; reflexivity].
  - rewrite (find_label b h eb Hb Eb).
    destruct (comp_entry a b h) as [e|] eqn:E; [apply Hc; reflexivity|apply Hn; reflexivity].
  - unfold res_len, ext_count, jlen, count.
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
    apply nth_error_None in E; unfold ext_count, jlen in *; lia.
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
    by (intro h; unfold count; rewrite find_compose_pre by assumption; reflexivity).
  destruct v as [h i].
  assert (Hc : apply (compose_pre a b) (mk_var h i)
               = if Nat.ltb i (res_len a b h)
                 then resolve (compose_pre a b) (comp_target a b h i)
                 else inl (mk_var h (i - res_len a b h + ext_count a b h))).
  { unfold apply at 1; cbn [v_label v_index].
    rewrite find_compose_pre, Hcount by assumption; cbn [fst snd].
    rewrite nth_error_map, length_map, length_seq, nth_error_seq.
    destruct (Nat.ltb_spec i (res_len a b h)); reflexivity. }
  rewrite Hc.
  destruct (Nat.ltb_spec i (res_len a b h)) as [Hi|Hi].
  - unfold comp_target, b_image.
    destruct (apply b (mk_var h i)) as [w|p] eqn:Ebw; [|reflexivity].
    (* where b sends the inner h_i is within a's reach *)
    assert (Hw : v_index w < Nat.max (jlen a (v_label w)) (count b (v_label w))).
    { unfold apply in Ebw; cbn [v_label v_index] in Ebw.
      destruct (nth_error (fst (find b h)) i) as [t|] eqn:Et.
      - destruct t as [h' n|p]; cbn [resolve] in Ebw; [|discriminate].
        injection Ebw as <-; cbn [v_label v_index].
        pose proof (slot_bound b (mk_var h i) h' n Hb Et); lia.
      - injection Ebw as <-; cbn [v_label v_index].
        apply nth_error_None in Et; unfold res_len, jlen, count in *; lia. }
    destruct (apply a w) as [u|p] eqn:Eaw; [|reflexivity].
    apply resolve_encode_res; [apply Hcount|apply (apply_a_bound a b w u Ha Hw Eaw)].
  - unfold apply; cbn [v_label v_index].
    unfold res_len, ext_count, jlen in *.
    rewrite (proj2 (nth_error_None (fst (find b h)) i)) by lia.
    cbn [v_label v_index].
    rewrite (proj2 (nth_error_None (fst (find a h)) _)) by lia.
    do 2 f_equal; lia.
Qed.

Lemma comp_target_slot_bound a b h i h' n :
  normal a = true -> normal b = true -> i < res_len a b h ->
  comp_target a b h i = Slot h' n -> n < ext_count a b h'.
Proof.
  intros Ha Hb Hi; unfold comp_target, b_image.
  destruct (apply b (mk_var h i)) as [w|p] eqn:Ebw; [|discriminate].
  assert (Hw : v_index w < Nat.max (jlen a (v_label w)) (count b (v_label w))).
  { unfold apply in Ebw; cbn [v_label v_index] in Ebw.
    destruct (nth_error (fst (find b h)) i) as [t|] eqn:Et.
    - destruct t as [h'' n'|p]; cbn [resolve] in Ebw; [|discriminate].
      injection Ebw as <-; cbn [v_label v_index].
      pose proof (slot_bound b (mk_var h i) h'' n' Hb Et); lia.
    - injection Ebw as <-; cbn [v_label v_index].
      apply nth_error_None in Et; unfold res_len, jlen, count in *; lia. }
  destruct (apply a w) as [u|p] eqn:Eaw; cbn [encode_res]; [|discriminate].
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
  intros Ha Hb; unfold keys_ok; apply forallb_spec; intros key e He.
  unfold compose_pre in He; rewrite get_merge in He by reflexivity.
  assert (Hc : forall l, comp_entry a b l = Some e -> e_label e = l)
    by (intros l; unfold comp_entry; destruct (nontrivial _ _); [intros [= <-]; reflexivity|discriminate]).
  destruct (get key a) as [ea|] eqn:Ea, (get key b) as [eb|] eqn:Eb; try discriminate.
  all: first [ rewrite (Hc _ He); apply Pos.eqb_eq, (normal_label a key ea Ha Ea)
             | rewrite (Hc _ He); apply Pos.eqb_eq, (normal_label b key eb Hb Eb) ].
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
      by (intros l; unfold comp_entry; destruct (nontrivial _ _) eqn:N;
          [intros [= <-]; exact N|discriminate]).
    destruct (get key a), (get key b); try discriminate; apply (Hc _ He).
  - intros v h' n Hn.
    unfold count; rewrite find_compose_pre by assumption; cbn [snd].
    rewrite find_compose_pre in Hn by assumption; cbn [fst] in Hn.
    rewrite nth_error_map, nth_error_seq in Hn.
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

Definition compose (fp : P -> P) a b : raw P :=
  normalize_list (labels (compose_pre fp a b)) (compose_pre fp a b).

Theorem normal_compose fp a b :
  normal a = true -> normal b = true -> normal (compose fp a b) = true.
Proof.
  intros Ha Hb; apply normalize_list_spec, pre_normal_compose_pre; assumption.
Qed.

Theorem apply_compose fp a b v :
  normal a = true -> normal b = true ->
  apply (compose fp a b) v
  = match apply b v with
    | inl w => apply a w
    | inr p => inr (fp p)
    end.
Proof.
  intros Ha Hb; unfold compose.
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

Definition clear h a : raw P := set_entry h [] (count a h) a.

Lemma find_clear h a h' :
  find (clear h a) h' = if label_eqb h' h then ([], count a h) else find a h'.
Proof. apply find_set_entry. Qed.

Lemma count_clear h a h' : count (clear h a) h' = count a h'.
Proof.
  unfold count at 1; rewrite find_clear.
  destruct (label_eqb_spec h' h) as [->|]; reflexivity.
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
  assert (Hk' : keys_ok (clear h a) = true) by apply keys_ok_set_entry, Hk.
  repeat split.
  - exact Hk'.
  - intros key e He; unfold clear, set_entry in He; rewrite get_update in He.
    destruct (Pos.eqb key (label_key h)); [|apply (Hnt _ _ He)].
    destruct (nontrivial _ _) eqn:E; [injection He as <-; exact E|discriminate].
  - intros v h' n Hn; rewrite count_clear; rewrite find_clear in Hn.
    destruct (label_eqb (v_label v) h); [destruct (v_index v); discriminate|].
    apply (Hwf _ _ _ Hn).
  - intros l Hl; apply not_in_labels in Hl; [|exact Hk'].
    rewrite (find_none_trivial _ _ Hl); reflexivity.
Qed.

Lemma find_nil_strip_once l h a :
  fst (find a h) = [] -> fst (find (strip_once l a) h) = [].
Proof.
  intros H; rewrite find_strip_once; cbn [fst].
  destruct (label_eqb_spec h l) as [->|]; rewrite ?H; reflexivity.
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
    by apply keys_ok_renumber, keys_ok_set_entry, Hk.
  apply (normal_of_pre_normal _ (fun _ => False)); [|auto].
  repeat split.
  - exact Hk'.
  - intros key e He; unfold strip_once, renumber in He; rewrite get_map_filter in He.
    destruct (get key (set_entry h _ _ a)) as [e0|] eqn:E0; [|discriminate].
    injection He as <-; cbn [e_targets e_out].
    unfold set_entry in E0; rewrite get_update in E0.
    destruct (Pos.eqb_spec key (label_key h)) as [->|].
    + destruct (nontrivial _ _) eqn:Hn; [|discriminate]; injection E0 as <-; cbn in *.
      destruct (removelast _), (pred _); cbn in *; auto.
    + specialize (Hnt _ _ E0); destruct (e_targets e0), (e_out e0); auto.
  - intros v h' n Hn.
    destruct (find_strip_once_nth h a v (v_index v) _ Hn) as [t0 [Ht0 [Heq _]]].
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
    { rewrite find_strip_once; cbn [fst]; rewrite (proj2 (label_eqb_neq h' h) Hne); reflexivity. }
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
    + rewrite find_strip_once; cbn [fst]; rewrite (proj2 (label_eqb_neq _ h) Hwl).
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
  unfold apply; rewrite find_strip_once, count_strip_once; cbn [fst].
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

Definition restrict h a : raw P :=
  let c := clear h a in
  let n := normalize_list (labels c) c in
  trim_loop (S (count n h)) h n.

Theorem restrict_spec h a :
  normal a = true ->
  normal (restrict h a) = true
  /\ fst (find (restrict h a) h) = []
  /\ (count (restrict h a) h = 0 \/ has_ref0 (restrict h a) h = true)
  /\ (forall v, v_label v <> h -> apply (restrict h a) v = apply a v).
Proof.
  intros Ha; unfold restrict.
  destruct (normalize_list_spec _ _ (pre_normal_clear h a Ha)) as [Hn Happ].
  assert (Hnil : fst (find (normalize_list (labels (clear h a)) (clear h a)) h) = []).
  { apply find_nil_normalize_list; rewrite find_clear, label_eqb_refl; reflexivity. }
  destruct (trim_loop_spec (S (count (normalize_list (labels (clear h a)) (clear h a)) h)) h _
              Hn Hnil (Nat.lt_succ_diag_r _)) as [H1 [H2 [H3 H4]]].
  repeat split; auto.
  intros v Hv; rewrite H4, Happ by exact Hv; apply apply_clear, Hv.
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
  cbn [e_targets] in Hin; apply in_map_iff in Hin as [t [Ht Hin]].
  exists k, e0; split; [exact E0|].
  destruct t as [h' n|p']; cbn in Ht; [destruct (label_eqb h' h); discriminate|].
  injection Ht as ->; exact Hin.
Qed.

Lemma binds_in_set_entry h ts n (m : raw P) p :
  binds_in (set_entry h ts n m) p -> binds_in m p \/ In (Bind p) ts.
Proof.
  intros [k [e [He Hin]]]; unfold set_entry in He; rewrite get_update in He.
  destruct (Pos.eqb k (label_key h)); [|left; exists k, e; auto].
  destruct (nontrivial ts n); [|discriminate]; injection He as <-; right; exact Hin.
Qed.

Lemma In_removelast {A} (x : A) (xs : list A) : In x (removelast xs) -> In x xs.
Proof.
  induction xs as [|y xs IH]; [intros []|]; cbn.
  destruct xs as [|z xs]; [intros []|]; intros [->|H]; [left; reflexivity|right; apply IH, H].
Qed.

Lemma binds_in_strip_once h (m : raw P) p : binds_in (strip_once h m) p -> binds_in m p.
Proof.
  unfold strip_once; intros H; apply binds_in_renumber, binds_in_set_entry in H as [H|H];
    [exact H|apply In_removelast, binds_in_find in H; exact H].
Qed.

Lemma binds_in_strip_loop fuel h (m : raw P) p :
  binds_in (strip_loop fuel h m) p -> binds_in m p.
Proof.
  revert m; induction fuel as [|f IH]; intros m H; cbn [strip_loop] in H; [exact H|].
  destruct (strip_ok _ _ _); [exact H|].
  apply (binds_in_strip_once h), IH, H.
Qed.

Lemma binds_in_push_inner h t (m : raw P) p :
  binds_in (push_inner h t m) p -> binds_in m p \/ t = Bind p.
Proof.
  unfold push_inner, cons_entry; intros H.
  apply binds_in_strip_loop, binds_in_set_entry in H as [H|[H|H]];
    [left; exact H|right; exact H|left; apply binds_in_find in H; exact H].
Qed.

Lemma binds_in_keys (m : raw P) p :
  keys_ok m = true -> binds_in m p -> exists h, In (Bind p) (fst (find m h)).
Proof.
  intros Hk [k [e [He Hin]]]; exists (e_label e).
  unfold keys_ok in Hk; rewrite forallb_spec in Hk.
  pose proof (proj1 (Pos.eqb_eq _ _) (Hk _ _ He)) as Hkey.
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
  intros Ha Hb H; unfold compose in H; apply binds_in_normalize_list in H.
  apply binds_in_keys in H as [h Hin]; [|apply keys_ok_compose_pre; assumption].
  rewrite find_compose_pre in Hin by assumption; cbn [fst] in Hin.
  apply in_map_iff in Hin as [i [Ht _]]; unfold comp_target, b_image in Ht.
  destruct (apply b (mk_var h i)) as [w|p'] eqn:Eb.
  - destruct (apply a w) as [u|p''] eqn:Ea; cbn [encode_res] in Ht; [discriminate|].
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
  unfold restrict; intros H.
  apply binds_in_trim_loop, binds_in_normalize_list, binds_in_clear in H; exact H.
Qed.

(** ** Composition ignores [fp] outside [b]'s payloads *)

Lemma compose_ext fp fp' a b :
  normal a = true -> normal b = true ->
  (forall p, binds_in b p -> fp p = fp' p) -> compose fp a b = compose fp' a b.
Proof.
  intros Ha Hb H; apply canonical; try (apply normal_compose; assumption).
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
  map_filter (fun _ e => Some (mk_entry (e_label e) (map (up_target h) (e_targets e))
                                        (e_out e))) a.

Lemma find_renumber_up h a h' :
  find (renumber_up h a) h' = (map (up_target h) (fst (find a h')), snd (find a h')).
Proof.
  unfold find, renumber_up; rewrite get_map_filter.
  destruct (get (label_key h') a); reflexivity.
Qed.

Lemma keys_ok_renumber_up h a : keys_ok a = true -> keys_ok (renumber_up h a) = true.
Proof.
  unfold keys_ok; rewrite !forallb_spec; intros Ha key e He.
  unfold renumber_up in He; rewrite get_map_filter in He.
  destruct (get key a) as [e0|] eqn:E0; [|discriminate]; injection He as <-; apply (Ha _ _ E0).
Qed.

Definition expand1 h a : raw P :=
  set_entry h (map (up_target h) (fst (find a h)) ++ [Slot h 0]) (S (count a h))
    (renumber_up h a).

Lemma find_expand1 h a h' :
  find (expand1 h a) h'
  = if label_eqb h' h then (map (up_target h) (fst (find a h)) ++ [Slot h 0], S (count a h))
    else (map (up_target h) (fst (find a h')), count a h').
Proof.
  unfold expand1; rewrite find_set_entry, find_renumber_up.
  destruct (label_eqb h' h); reflexivity.
Qed.

Lemma count_expand1 h a h' :
  count (expand1 h a) h' = if label_eqb h' h then S (count a h) else count a h'.
Proof. unfold count at 1; rewrite find_expand1; destruct (label_eqb h' h); reflexivity. Qed.

Lemma resolve_up h a t : resolve (expand1 h a) (up_target h t) = resolve a t.
Proof.
  destruct t as [h' n|p]; cbn [up_target]; [|reflexivity].
  destruct (label_eqb_spec h' h) as [->|Hne]; cbn [resolve]; rewrite count_expand1.
  - rewrite label_eqb_refl; do 2 f_equal; lia.
  - rewrite (proj2 (label_eqb_neq h' h) Hne); reflexivity.
Qed.

Theorem apply_expand1 h a v : apply (expand1 h a) v = apply a v.
Proof.
  unfold apply at 1; rewrite find_expand1, count_expand1.
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
    by apply keys_ok_set_entry, keys_ok_renumber_up, Hk.
  repeat split.
  - exact Hk'.
  - intros key e He; unfold expand1, set_entry in He; rewrite get_update in He.
    destruct (Pos.eqb key (label_key h)).
    + destruct (nontrivial _ _) eqn:E; [injection He as <-; exact E|discriminate].
    + unfold renumber_up in He; rewrite get_map_filter in He.
      destruct (get key a) as [e0|] eqn:E0; [|discriminate]; injection He as <-; cbn.
      specialize (Hnt _ _ E0); destruct (e_targets e0), (e_out e0); auto.
  - intros v h' n Hn; rewrite count_expand1; rewrite find_expand1 in Hn.
    destruct v as [hv i]; cbn [v_label v_index] in *.
    destruct (label_eqb_spec hv h) as [->|Hl]; cbn [fst] in Hn.
    + destruct (Nat.lt_ge_cases i (length (fst (find a h)))) as [Hi|Hi].
      * rewrite nth_error_app1 in Hn by (rewrite length_map; exact Hi).
        rewrite nth_error_map in Hn.
        destruct (nth_error (fst (find a h)) i) as [t0|] eqn:E; [|discriminate].
        injection Hn as Hn.
        destruct t0 as [h0 n0|p]; cbn [up_target] in Hn; [|discriminate].
        pose proof (Hwf (mk_var h i) h0 n0 E) as Hw.
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
      pose proof (Hwf (mk_var hv i) h0 n0 E) as Hw.
      destruct (label_eqb_spec h0 h) as [->|Hh]; injection Hn as <- <-.
      * rewrite label_eqb_refl; lia.
      * rewrite (proj2 (label_eqb_neq h0 h) Hh); exact Hw.
  - intros h' HQ.
    assert (Hne : h' <> h) by (intro E; subst; contradiction).
    apply (strip_ok_spec _ _ _ Hk'); intros Hl'.
    pose proof (Hs h' HQ) as Hs'; rewrite (strip_ok_spec _ _ _ Hk) in Hs'.
    assert (Ef : fst (find (expand1 h a) h') = map (up_target h) (fst (find a h'))).
    { rewrite find_expand1, (proj2 (label_eqb_neq h' h) Hne); reflexivity. }
    rewrite Ef in Hl' |- *.
    unfold last_target in Hl'; rewrite length_map, nth_error_map in Hl'.
    destruct (nth_error (fst (find a h')) (pred (length (fst (find a h'))))) as [[h0 n0|p]|] eqn:El;
      cbn [option_map up_target] in Hl'; [|discriminate|discriminate].
    destruct (label_eqb_spec h0 h) as [->|Hh]; injection Hl' as E1 E2; [congruence|].
    subst h0 n0.
    destruct (Hs' El) as [w [Hw Hwne]].
    exists w; split; [|rewrite length_map; exact Hwne].
    rewrite find_expand1.
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

Lemma apply_expand_n d h a v : apply (expand_n d h a) v = apply a v.
Proof. induction d as [|d IH]; cbn [expand_n]; [reflexivity|rewrite apply_expand1; exact IH]. Qed.

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
  assert (Hk' : keys_ok (cons_entry h t a) = true) by apply keys_ok_set_entry, Hk.
  repeat split.
  - exact Hk'.
  - intros key e He; unfold cons_entry, set_entry in He; rewrite get_update in He.
    destruct (Pos.eqb_spec key (label_key h)) as [->|]; [|apply (Hnt _ _ He)].
    injection He as <-; reflexivity.
  - intros v h' n Hn; rewrite count_cons_entry.
    rewrite find_cons_entry in Hn.
    destruct v as [hv i]; cbn [v_label v_index] in Hn.
    destruct (label_eqb_spec hv h) as [->|]; cbn [fst] in Hn.
    + destruct i as [|i]; cbn [nth_error] in Hn; [injection Hn as ->; apply Ht; reflexivity|].
      apply (Hwf (mk_var h i)), Hn.
    + apply (Hwf (mk_var hv i)), Hn.
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
    + exists (mk_var h (S (v_index w))); split.
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
  intros Hk Hne; apply strip_ok_spec; [apply keys_ok_set_entry, Hk|].
  intros _; exists (mk_var h 0); split.
  - rewrite find_cons_entry; cbn [v_label v_index]; rewrite label_eqb_refl; reflexivity.
  - intro E; injection E as E _; congruence.
Qed.

(** [push_inner_var h w a] sends the innermost [h] to the variable [w] and
    passes everything else to [a]; [w] may be any variable. *)
Definition push_inner_var h (w : var) a : raw P :=
  let a' := expand_n (S (v_index w) - count a (v_label w)) (v_label w) a in
  push_inner h (Slot (v_label w) (count a' (v_label w) - S (v_index w))) a'.

Theorem push_inner_var_spec h w a :
  normal a = true ->
  normal (push_inner_var h w a) = true
  /\ (forall v, apply (push_inner_var h w a) v
                = if var_eqb v (mk_var h 0) then inl w
                  else apply a (unshift_var (mk_var h 0) v)).
Proof.
  intros Ha; destruct w as [h' i]; unfold push_inner_var; cbn [v_label v_index].
  set (d := S i - count a h'); set (a' := expand_n d h' a).
  assert (Hc : count a' h' = d + count a h') by apply count_expand_n.
  set (t := Slot h' (count a' h' - S i)).
  assert (Hpre : pre_normal (cons_entry h t a') (fun l => l = h)).
  { pose proof (proj1 (normal_iff a h') Ha) as [Han _].
    destruct d as [|d'] eqn:Ed.
    - assert (Hi : i < count a h') by lia.
      subst a'; cbn [expand_n] in *.
      apply almost_normal_cons_entry; [exact Ha|].
      intros h0 n0 [= <- <-]; lia.
    - assert (Ht : t = Slot h' 0) by (unfold t; f_equal; lia).
      pose proof (pre_normal_expand_n (S d') a _ h' Han eq_refl) as Ha'.
      fold a' in Ha'.
      pose proof (pre_normal_cons_entry h t a' _ Ha') as Hc'.
      assert (Hb : forall h0 n0, t = Slot h0 n0 -> n0 < count a' h0)
        by (rewrite Ht; intros h0 n0 [= <- <-]; lia).
      specialize (Hc' Hb).
      destruct (label_eq_dec h' h) as [->|Hne].
      + apply (pre_normal_mono _ _ _ Hc'); intros x Hx [H|H]; apply Hx; exact H.
      + rewrite Ht in Hc' |- *.
        pose proof (pre_normal_fix _ _ h' Hc') as Hf.
        assert (Hk' : keys_ok a' = true) by (destruct Ha' as [X _]; exact X).
        specialize (Hf (strip_ok_cons_ref h h' a' Hk' Hne)).
        apply (pre_normal_mono _ _ _ Hf); intros x Hx [[H|H] Hx']; [contradiction|apply Hx, H]. }
  assert (Hlen : jlen (cons_entry h t a') h < S (S (jlen a' h)))
    by (unfold jlen; rewrite find_cons_entry, label_eqb_refl; cbn; lia).
  destruct (strip_loop_spec_gen _ _ h _ Hpre eq_refl Hlen) as [Hn Happ].
  split.
  - apply (normal_of_pre_normal _ _ Hn); intros l [H1 H2]; contradiction.
  - intros v; unfold push_inner; rewrite Happ, apply_cons_entry.
    destruct (var_eqb v (mk_var h 0)); [|apply apply_expand_n].
    unfold t; cbn [resolve]; do 2 f_equal; lia.
Qed.

Lemma binds_in_expand1 h (m : raw P) p : binds_in (expand1 h m) p -> binds_in m p.
Proof.
  intros H; unfold expand1 in H; apply binds_in_set_entry in H as [H|H].
  - destruct H as [k [e [He Hin]]]; unfold renumber_up in He; rewrite get_map_filter in He.
    destruct (get k m) as [e0|] eqn:E0; [|discriminate]; injection He as <-.
    cbn [e_targets] in Hin; apply in_map_iff in Hin as [t [Ht Hin]].
    exists k, e0; split; [exact E0|].
    destruct t as [h' n|p']; cbn in Ht; [destruct (label_eqb h' h); discriminate|].
    injection Ht as ->; exact Hin.
  - apply in_app_or in H as [H|[H|[]]]; [|discriminate].
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
  apply binds_in_push_inner in H as [H|H]; [apply binds_in_expand_n in H; exact H|discriminate].
Qed.

(** ** Conditions on every target *)

Lemma tall_targets (Pt : target P -> bool) a :
  keys_ok a = true ->
  tall (fun e => List.forallb Pt (e_targets e)) a = true
  <-> (forall h i t, nth_error (fst (find a h)) i = Some t -> Pt t = true).
Proof.
  intros Hk; rewrite tall_spec; split.
  - intros H h i t E; unfold find in E.
    destruct (get (label_key h) a) as [e|] eqn:He; cbn [fst] in E;
      [|rewrite nth_error_nil in E; discriminate].
    specialize (H _ _ He); rewrite List.forallb_forall in H.
    apply H, (nth_error_In _ _ E).
  - intros H k e He; apply List.forallb_forall; intros t Hin.
    apply In_nth_error in Hin as [i Hi].
    unfold keys_ok in Hk; rewrite forallb_spec in Hk.
    pose proof (proj1 (Pos.eqb_eq _ _) (Hk _ _ He)) as Hkey.
    apply (H (e_label e) i); unfold find; rewrite <- Hkey, He; exact Hi.
Qed.

End Slots.
