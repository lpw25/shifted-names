(** * Nested adjustments: closed payloads with lazily applied adjustments

    A payload is a pair [(u, ρ)]: [u] is a term with no bound variables,
    opaque to the library, and [ρ] is an adjustment to be applied to it
    lazily.  [ρ] is an ordinary canonical adjustment into the outer scope
    (with its own slots), so a payload's data determines its meaning, and
    canonicity of nested adjustments is just canonicity of the flat form
    (Slots.v) with payloads compared as data.

    Because [u] has no bound variables, a payload adjustment ignores bound
    inputs: it has no input entries for the anonymous label, and keeps an
    output slot for it only if one is referenced. *)

From Stdlib Require Import PArith Arith List Lia Bool.
From ShiftedNames.Core Require Import Trie Label Var Slots.
Import ListNotations.

Inductive nadj (T : Type) : Type :=
| NAdj : tree (entry (T * nadj T)) -> nadj T.

Arguments NAdj {T} _.

Section Nested.

Context {T : Type}.

Local Notation payload := (T * nadj T)%type.

Definition nraw (a : nadj T) : raw payload := match a with NAdj m => m end.

(** ** Normal forms *)

(** Extra conditions on a payload adjustment: no bound input entries, and
    its innermost bound output slot (if any) is referenced. *)
Definition pnormal_raw (m : raw payload) : bool :=
  match fst (find m None) with [] => true | _ => false end
  && (Nat.eqb (count m None) 0
      || existsb (fun r => match r with
                           | (_, h, 0) => label_eqb h None
                           | _ => false
                           end) (refs m)).

Fixpoint nnormal (a : nadj T) : bool :=
  match a with
  | NAdj m =>
      normal m
      && tall (fun e => List.forallb (fun t => match t with
                                               | Bind (u, ρ) => nnormal ρ && pnormal_raw (nraw ρ)
                                               | Slot _ _ => true
                                               end) (e_targets e)) m
  end.

(** ** Semantics *)

Definition napply (a : nadj T) (v : var) : var + payload := apply (nraw a) v.

(** ** Mapping over the payloads of the top level *)

Definition map_target (f : payload -> payload) (t : target payload) : target payload :=
  match t with Bind p => Bind (f p) | Slot h n => Slot h n end.

Definition map_payloads (f : payload -> payload) (m : raw payload) : raw payload :=
  map_filter (fun _ e => Some (mk_entry (e_label e) (map (map_target f) (e_targets e))
                                        (e_out e))) m.

Lemma find_map_payloads f m h :
  find (map_payloads f m) h = (map (map_target f) (fst (find m h)), snd (find m h)).
Proof.
  unfold find, map_payloads; rewrite get_map_filter.
  destruct (get (label_key h) m); reflexivity.
Qed.

Lemma count_map_payloads f m h : count (map_payloads f m) h = count m h.
Proof. unfold count; rewrite find_map_payloads; reflexivity. Qed.

Lemma apply_map_payloads f m v :
  apply (map_payloads f m) v
  = match apply m v with inl w => inl w | inr p => inr (f p) end.
Proof.
  unfold apply; rewrite find_map_payloads, count_map_payloads; cbn [fst].
  rewrite nth_error_map, length_map.
  destruct (nth_error _ _) as [[h n|p]|]; cbn [option_map map_target resolve];
    rewrite ?count_map_payloads; reflexivity.
Qed.

Lemma refs_map_payloads f m r : In r (refs (map_payloads f m)) <-> In r (refs m).
Proof.
  destruct r as [[v h] n]; rewrite !In_refs_gen; split.
  - intros [key [e [He [Hl Hn]]]]; unfold map_payloads in He; rewrite get_map_filter in He.
    destruct (get key m) as [e0|] eqn:E0; [|discriminate]; injection He as <-.
    cbn [e_label e_targets] in *; rewrite nth_error_map in Hn.
    exists key, e0; repeat split; auto.
    destruct (nth_error (e_targets e0) (v_index v)) as [[h' n'|p]|]; cbn in Hn;
      [exact Hn|discriminate|discriminate].
  - intros [key [e [He [Hl Hn]]]]; exists key; unfold map_payloads; rewrite get_map_filter, He.
    eexists; repeat split; [cbn; exact Hl|]; cbn [e_targets].
    rewrite nth_error_map, Hn; reflexivity.
Qed.

Lemma existsb_same_members' {A} (f : A -> bool) (l1 l2 : list A) :
  (forall x, In x l1 <-> In x l2) -> existsb f l1 = existsb f l2.
Proof.
  intros H; apply Bool.eq_iff_eq_true; rewrite !existsb_exists.
  split; intros [x [Hx Hf]]; exists x; split; auto; apply H; auto.
Qed.

Lemma last_target_map_payloads f ts :
  last_target (map (map_target f) ts)
  = option_map (map_target f) (last_target ts).
Proof. unfold last_target; rewrite length_map, nth_error_map; reflexivity. Qed.

Theorem normal_map_payloads f m : normal m = true -> normal (map_payloads f m) = true.
Proof.
  intros Hm; unfold normal in *; rewrite andb_true_iff in *; destruct Hm as [He Hr]; split.
  - apply forallb_spec; intros key e Hget.
    unfold map_payloads in Hget; rewrite get_map_filter in Hget.
    destruct (get key m) as [e0|] eqn:E0; [|discriminate]; injection Hget as <-.
    rewrite forallb_spec in He; specialize (He _ _ E0).
    unfold entry_ok, strip_ok in *; cbn [e_label e_targets e_out].
    rewrite last_target_map_payloads.
    rewrite (existsb_same_members' _ (refs (map_payloads f m)) (refs m))
      by (intro; apply refs_map_payloads).
    destruct (e_targets e0) as [|t ts] eqn:Et; [exact He|].
    rewrite <- Et in *.
    destruct (last_target (e_targets e0)) as [[h n|p]|]; cbn [option_map map_target];
      rewrite ?length_map; destruct (e_targets e0); cbn in *; exact He.
  - apply List.forallb_forall; intros [[v h] n] Hin.
    apply refs_map_payloads in Hin.
    rewrite List.forallb_forall in Hr; specialize (Hr _ Hin); cbn in *.
    rewrite count_map_payloads; exact Hr.
Qed.

(** ** Nesting depth, for induction over payloads *)

Fixpoint ndepth (a : nadj T) : nat :=
  match a with
  | NAdj m => S (tmax (fun e => list_max (map (fun t => match t with
                                                        | Bind p => ndepth (snd p)
                                                        | Slot _ _ => 0
                                                        end) (e_targets e))) m)
  end.

Lemma ndepth_payload m k e p :
  get k m = Some e -> In (Bind p) (e_targets e) -> ndepth (snd p) < ndepth (NAdj m).
Proof.
  intros He Hin; cbn [ndepth].
  pose proof (tmax_ge (fun e => list_max (map (fun t => match t with
                                                       | Bind p => ndepth (snd p)
                                                       | Slot _ _ => 0
                                                       end) (e_targets e))) m k e He) as H.
  cbn beta in H.
  assert (ndepth (snd p) <= list_max (map (fun t => match t with
                                                     | Bind p => ndepth (snd p)
                                                     | Slot _ _ => 0
                                                     end) (e_targets e))).
  { assert (Hm : forall l x, In x l -> x <= list_max l).
    { intros l x Hx; pose proof (proj1 (list_max_le l (list_max l)) (Nat.le_refl _)) as Hl.
      rewrite Forall_forall in Hl; exact (Hl x Hx). }
    apply Hm, in_map_iff; exists (Bind p); split; [reflexivity|exact Hin]. }
  lia.
Qed.

(** ** Payload conditions on a whole trie *)

Definition payload_ok (t : target payload) : bool :=
  match t with
  | Bind (u, ρ) => nnormal ρ && pnormal_raw (nraw ρ)
  | Slot _ _ => true
  end.

Definition payloads_ok (m : raw payload) : bool :=
  tall (fun e => List.forallb payload_ok (e_targets e)) m.

Lemma nnormal_NAdj m : nnormal (NAdj m) = normal m && payloads_ok m.
Proof. reflexivity. Qed.

Lemma payloads_ok_spec m :
  payloads_ok m = true <->
  (forall k e p, get k m = Some e -> In (Bind p) (e_targets e) ->
                 nnormal (snd p) = true /\ pnormal_raw (nraw (snd p)) = true).
Proof.
  unfold payloads_ok; rewrite tall_spec; split.
  - intros H k e [u ρ] He Hin; specialize (H _ _ He).
    rewrite List.forallb_forall in H; specialize (H _ Hin); cbn in H.
    apply andb_true_iff in H; exact H.
  - intros H k e He; apply List.forallb_forall; intros [h n|[u ρ]] Hin; [reflexivity|].
    cbn; apply andb_true_iff, (H _ _ (u, ρ) He Hin).
Qed.

Lemma payloads_ok_push_outer h m : payloads_ok (push_outer h m) = payloads_ok m.
Proof.
  apply Bool.eq_iff_eq_true; rewrite !payloads_ok_spec; split.
  - intros H k e p He Hin; apply (H k (if Pos.eqb k (label_key h)
                                         then mk_entry h (e_targets e) (S (e_out e)) else e) p).
    + unfold push_outer; rewrite get_update.
      destruct (Pos.eqb_spec k (label_key h)) as [->|]; [rewrite He; reflexivity|exact He].
    + destruct (Pos.eqb k _); exact Hin.
  - intros H k e p He Hin; unfold push_outer in He; rewrite get_update in He.
    destruct (Pos.eqb_spec k (label_key h)) as [->|]; [|apply (H _ _ _ He Hin)].
    destruct (get (label_key h) m) as [e0|] eqn:E0; injection He as <-; cbn in Hin;
      [apply (H _ _ _ E0 Hin)|destruct Hin].
Qed.

Lemma payloads_ok_map f m :
  (forall k e p, get k m = Some e -> In (Bind p) (e_targets e) ->
                 nnormal (snd (f p)) = true /\ pnormal_raw (nraw (snd (f p))) = true) ->
  payloads_ok (map_payloads f m) = true.
Proof.
  intros H; apply payloads_ok_spec; intros k e p He Hin.
  unfold map_payloads in He; rewrite get_map_filter in He.
  destruct (get k m) as [e0|] eqn:E0; [|discriminate]; injection He as <-.
  cbn [e_targets] in Hin; apply in_map_iff in Hin as [[h n|p0] [Ht Hin]]; [discriminate|].
  injection Ht as <-; apply (H _ _ _ E0 Hin).
Qed.

(** ** Weakening payloads: [pshift h ρ] shifts [ρ]'s results past a new
    outer [h₍₀₎]. *)

Fixpoint pshift (h : option label) (ρ : nadj T) : nadj T :=
  match ρ with
  | NAdj m =>
      NAdj ((if label_eqb h None && Nat.eqb (count m None) 0 then (fun x => x) else push_outer h)
              (map_payloads (fun p => (fst p, pshift h (snd p))) m))
  end.

Definition npush_outer (h : option label) (a : nadj T) : nadj T :=
  match a with
  | NAdj m => NAdj (push_outer h (map_payloads (fun p => (fst p, pshift h (snd p))) m))
  end.

Theorem napply_npush_outer h a v :
  normal (nraw a) = true ->
  napply (npush_outer h a) v
  = match napply a v with
    | inl w => inl (shift_var (mk_var h 0) w)
    | inr p => inr (fst p, pshift h (snd p))
    end.
Proof.
  destruct a as [m]; cbn [nraw]; intros Hm; unfold napply, npush_outer; cbn [nraw]; change (nraw (NAdj m)) with m.
  rewrite apply_push_outer by (apply normal_map_payloads, Hm).
  rewrite apply_map_payloads; destruct (@apply payload m v); reflexivity.
Qed.

Lemma count_none_zero_no_bound (m : raw payload) v w :
  normal m = true -> count m None = 0 -> v_label v <> None ->
  apply m v = inl w -> v_label w <> None.
Proof.
  intros Hm Hc Hv Hw; unfold apply in Hw.
  destruct (nth_error (fst (find m (v_label v))) (v_index v)) as [t|] eqn:E.
  - destruct t as [h' n|p]; cbn [resolve] in Hw; [|discriminate].
    injection Hw as <-; cbn [v_label]; intro; subst h'.
    pose proof (slot_bound m v None n Hm E); lia.
  - injection Hw as <-; exact Hv.
Qed.

Theorem napply_pshift h ρ v :
  normal (nraw ρ) = true -> v_label v <> None ->
  napply (pshift h ρ) v
  = match napply ρ v with
    | inl w => inl (shift_var (mk_var h 0) w)
    | inr p => inr (fst p, pshift h (snd p))
    end.
Proof.
  destruct ρ as [m]; cbn [nraw]; intros Hm Hv; unfold napply; cbn [pshift nraw]; change (nraw (NAdj m)) with m.
  destruct (label_eqb_spec h None) as [->|Hh]; cbn [andb].
  - destruct (Nat.eqb_spec (count m None) 0) as [Hc|Hc].
    + rewrite apply_map_payloads.
      destruct (@apply payload m v) as [w|p] eqn:E; [|reflexivity].
      pose proof (count_none_zero_no_bound m v w Hm Hc Hv E) as Hw.
      unfold shift_var; cbn [v_label v_index].
      destruct (v_label w) as [x|] eqn:Ew; [|contradiction]; cbn [label_eqb andb].
      reflexivity.
    + rewrite apply_push_outer by (apply normal_map_payloads, Hm).
      rewrite apply_map_payloads; destruct (@apply payload m v); reflexivity.
  - rewrite apply_push_outer by (apply normal_map_payloads, Hm).
    rewrite apply_map_payloads; destruct (@apply payload m v); reflexivity.
Qed.

Lemma pnormal_raw_map_payloads f m : pnormal_raw (map_payloads f m) = pnormal_raw m.
Proof.
  unfold pnormal_raw; rewrite count_map_payloads, find_map_payloads; cbn [fst].
  rewrite (existsb_same_members' _ (refs (map_payloads f m)) (refs m))
    by (intro; apply refs_map_payloads).
  destruct (fst (find m None)); reflexivity.
Qed.

Lemma pnormal_raw_push_outer h m :
  normal m = true -> (label_eqb h None = false \/ count m None <> 0) ->
  pnormal_raw (push_outer h m) = pnormal_raw m.
Proof.
  intros Hm Hh; unfold pnormal_raw.
  rewrite count_push_outer, find_push_outer by exact Hm.
  rewrite (existsb_same_members' _ (refs (push_outer h m)) (refs m))
    by (intro; apply refs_push_outer, Hm).
  rewrite (label_eqb_sym None h).
  destruct (label_eqb h None) eqn:E; cbn [fst]; [|reflexivity].
  destruct Hh as [Hh|Hh]; [discriminate|].
  destruct (Nat.eqb_spec (count m None) 0); [contradiction|].
  cbn [Nat.eqb orb]; apply label_eqb_eq in E; subst h; reflexivity.
Qed.

Lemma pnormal_pshift h ρ :
  normal (nraw ρ) = true -> pnormal_raw (nraw (pshift h ρ)) = pnormal_raw (nraw ρ).
Proof.
  destruct ρ as [m]; cbn [nraw pshift]; intros Hm.
  destruct (label_eqb h None && Nat.eqb (count m None) 0) eqn:E.
  - apply pnormal_raw_map_payloads.
  - rewrite pnormal_raw_push_outer.
    + apply pnormal_raw_map_payloads.
    + apply normal_map_payloads, Hm.
    + rewrite count_map_payloads; apply andb_false_iff in E as [E|E];
        [left; exact E|right; apply Nat.eqb_neq, E].
Qed.

Lemma nnormal_pshift_depth h n :
  forall ρ, ndepth ρ <= n -> nnormal ρ = true -> nnormal (pshift h ρ) = true.
Proof.
  induction n as [|n IH]; intros [m] Hd Hn; [cbn in Hd; lia|].
  rewrite nnormal_NAdj in Hn; apply andb_true_iff in Hn as [Hm Hp].
  cbn [pshift]; rewrite nnormal_NAdj.
  assert (Hq : payloads_ok (map_payloads (fun p => (fst p, pshift h (snd p))) m) = true).
  { apply payloads_ok_map; intros k e p He Hin; cbn [snd].
    pose proof (proj1 (payloads_ok_spec m) Hp k e p He Hin) as [Hn1 Hn2].
    pose proof (ndepth_payload m k e p He Hin).
    split; [apply IH; [lia|exact Hn1]|].
    rewrite pnormal_pshift; [exact Hn2|].
    destruct (snd p) as [m']; rewrite nnormal_NAdj in Hn1; apply andb_true_iff in Hn1; apply Hn1. }
  destruct (label_eqb h None && Nat.eqb (count m None) 0).
  - rewrite normal_map_payloads, Hq by exact Hm; reflexivity.
  - rewrite normal_push_outer, payloads_ok_push_outer, Hq by (apply normal_map_payloads, Hm).
    reflexivity.
Qed.

Theorem nnormal_pshift h ρ : nnormal ρ = true -> nnormal (pshift h ρ) = true.
Proof. apply (nnormal_pshift_depth h (ndepth ρ)); lia. Qed.

Theorem pnormal_pshift' h ρ :
  nnormal ρ = true -> pnormal_raw (nraw ρ) = true -> pnormal_raw (nraw (pshift h ρ)) = true.
Proof.
  intros Hn Hp; rewrite pnormal_pshift; [exact Hp|].
  destruct ρ as [m]; rewrite nnormal_NAdj in Hn; apply andb_true_iff in Hn; apply Hn.
Qed.

Theorem nnormal_npush_outer h a : nnormal a = true -> nnormal (npush_outer h a) = true.
Proof.
  destruct a as [m]; intros Hn; pose proof (nnormal_pshift h (NAdj m) Hn) as H.
  cbn [pshift] in H; unfold npush_outer; rewrite nnormal_NAdj in *.
  apply andb_true_iff in Hn as [Hm _].
  destruct (label_eqb h None && Nat.eqb (count m None) 0).
  - rewrite normal_push_outer, payloads_ok_push_outer by (apply normal_map_payloads, Hm).
    apply andb_true_iff in H; apply H.
  - exact H.
Qed.

(** ** Payloads occurring in a trie *)

Lemma payloads_ok_binds m :
  payloads_ok m = true <->
  (forall p, binds_in m p -> nnormal (snd p) = true /\ pnormal_raw (nraw (snd p)) = true).
Proof.
  rewrite payloads_ok_spec; split.
  - intros H p [k [e [He Hin]]]; exact (H k e p He Hin).
  - intros H k e p He Hin; apply H; exists k, e; auto.
Qed.

(** ** Nested [push_inner]: payloads live in the output scope, so they are
    untouched. *)

Definition npush_inner (h : option label) (t : target payload) (a : nadj T) : nadj T :=
  match a with NAdj m => NAdj (push_inner h t m) end.

Theorem napply_npush_inner h t a v :
  normal (nraw a) = true -> (forall h' n, t = Slot h' n -> n < count (nraw a) h') ->
  napply (npush_inner h t a) v
  = if var_eqb v (mk_var h 0) then resolve (nraw a) t
    else napply a (unshift_var (mk_var h 0) v).
Proof. destruct a as [m]; apply apply_push_inner. Qed.

Theorem nnormal_npush_inner h t a :
  nnormal a = true -> (forall h' n, t = Slot h' n -> n < count (nraw a) h') ->
  payload_ok t = true ->
  nnormal (npush_inner h t a) = true.
Proof.
  destruct a as [m]; cbn [nraw npush_inner]; rewrite !nnormal_NAdj.
  intros Hn Ht Hp; apply andb_true_iff in Hn as [Hm Hq]; apply andb_true_iff; split.
  - apply normal_push_inner; assumption.
  - apply payloads_ok_binds; intros p Hb.
    apply binds_in_push_inner in Hb as [Hb|Hb].
    + apply (proj1 (payloads_ok_binds m) Hq p Hb).
    + subst t; destruct p as [u ρ]; cbn in Hp; apply andb_true_iff in Hp; exact Hp.
Qed.

(** ** Composition

    [ncompose a b] first applies [b] and then [a].  A payload [(u, ρ)] of [b]
    becomes [(u, a ∘ ρ)], restricted to the free (non-[None]) inputs of the
    closed term [u].  Recursion is on payload nesting depth, via fuel. *)

Definition prestrict (ρ : nadj T) : nadj T :=
  match ρ with NAdj m => NAdj (restrict None m) end.

Fixpoint ncompose_f (fuel : nat) (a b : nadj T) : nadj T :=
  match fuel with
  | 0 => b
  | S f =>
      match a, b with
      | NAdj ma, NAdj mb =>
          NAdj (compose (fun p => (fst p, prestrict (ncompose_f f a (snd p)))) ma mb)
      end
  end.

Definition ncompose (a b : nadj T) : nadj T := ncompose_f (ndepth b) a b.

Lemma nnormal_normal a : nnormal a = true -> normal (nraw a) = true.
Proof. destruct a as [m]; rewrite nnormal_NAdj; intros H; apply andb_true_iff in H; apply H. Qed.

Lemma nnormal_payloads m :
  nnormal (NAdj m) = true -> payloads_ok m = true.
Proof. rewrite nnormal_NAdj; intros H; apply andb_true_iff in H; apply H. Qed.

Theorem nnormal_prestrict ρ :
  nnormal ρ = true -> nnormal (prestrict ρ) = true /\ pnormal_raw (nraw (prestrict ρ)) = true.
Proof.
  destruct ρ as [m]; intros Hn; cbn [prestrict nraw].
  pose proof (nnormal_payloads m Hn) as Hp; apply nnormal_normal in Hn; cbn [nraw] in Hn.
  destruct (restrict_spec None m Hn) as [H1 [H2 [H3 _]]].
  split.
  - rewrite nnormal_NAdj, H1; cbn [andb].
    apply payloads_ok_binds; intros p Hb.
    apply (proj1 (payloads_ok_binds m) Hp), (binds_in_restrict None m p Hb).
  - unfold pnormal_raw; rewrite H2; cbn [andb].
    destruct H3 as [H3|H3]; [rewrite H3; reflexivity|].
    unfold has_ref0 in H3; rewrite H3; apply orb_true_r.
Qed.

Theorem nnormal_ncompose_f f a b :
  nnormal a = true -> nnormal b = true -> nnormal (ncompose_f f a b) = true.
Proof.
  revert a b; induction f as [|f IH]; intros a b Ha Hb; [exact Hb|].
  destruct a as [ma], b as [mb]; cbn [ncompose_f].
  pose proof (nnormal_normal _ Ha) as Hma; pose proof (nnormal_normal _ Hb) as Hmb.
  cbn [nraw] in Hma, Hmb.
  rewrite nnormal_NAdj, normal_compose by assumption; cbn [andb].
  apply payloads_ok_binds; intros p Hbd.
  apply binds_in_compose in Hbd as [Hbd|[p' [Hbd ->]]]; [| |exact Hma|exact Hmb].
  - apply (proj1 (payloads_ok_binds ma) (nnormal_payloads ma Ha) p Hbd).
  - cbn [snd]; apply nnormal_prestrict, IH; [exact Ha|].
    apply (proj1 (payloads_ok_binds mb) (nnormal_payloads mb Hb) p' Hbd).
Qed.

Theorem nnormal_ncompose a b :
  nnormal a = true -> nnormal b = true -> nnormal (ncompose a b) = true.
Proof. apply nnormal_ncompose_f. Qed.

Lemma ndepth_binds m p : binds_in m p -> ndepth (snd p) < ndepth (NAdj m).
Proof. intros [k [e [He Hin]]]; apply (ndepth_payload m k e p He Hin). Qed.

Lemma ndepth_pos a : 0 < ndepth a.
Proof. destruct a; cbn [ndepth]; lia. Qed.

Lemma ncompose_fuel f :
  forall g a b, nnormal a = true -> nnormal b = true -> ndepth b <= f -> ndepth b <= g ->
  ncompose_f f a b = ncompose_f g a b.
Proof.
  induction f as [|f IH]; intros g a b Ha Hb Hf Hg; [pose proof (ndepth_pos b); lia|].
  destruct g as [|g]; [pose proof (ndepth_pos b); lia|].
  destruct a as [ma], b as [mb]; cbn [ncompose_f]; f_equal.
  apply compose_ext; [apply (nnormal_normal _ Ha)|apply (nnormal_normal _ Hb)|].
  intros p Hbd; pose proof (ndepth_binds mb p Hbd).
  rewrite (IH g); [reflexivity|exact Ha| |lia|lia].
  apply (proj1 (payloads_ok_binds mb) (nnormal_payloads mb Hb) p Hbd).
Qed.

Theorem napply_ncompose a b v :
  nnormal a = true -> nnormal b = true ->
  napply (ncompose a b) v
  = match napply b v with
    | inl w => napply a w
    | inr p => inr (fst p, prestrict (ncompose a (snd p)))
    end.
Proof.
  intros Ha Hb; unfold ncompose.
  destruct (ndepth b) as [|d] eqn:Ed; [pose proof (ndepth_pos b); lia|].
  destruct a as [ma], b as [mb]; cbn [ncompose_f]; unfold napply; cbn [nraw].
  rewrite apply_compose by (apply (nnormal_normal (NAdj _)); assumption).
  destruct (@apply payload mb v) as [w|p] eqn:E; [reflexivity|].
  pose proof (binds_in_apply mb v p E) as Hbd; pose proof (ndepth_binds mb p Hbd).
  rewrite (ncompose_fuel d (ndepth (snd p))); [reflexivity|exact Ha| |lia|lia].
  apply (proj1 (payloads_ok_binds mb) (nnormal_payloads mb Hb) p Hbd).
Qed.

(** ** Canonicity of payload adjustments

    Payload adjustments are only ever applied to the free (non-[None])
    variables of a closed term, so they are canonical with respect to that
    restricted meaning. *)

Lemma slot_image (m : raw payload) v w :
  normal m = true -> apply m v = inl w -> v_label w <> v_label v ->
  v_index w < count m (v_label w).
Proof.
  intros Hm Hw Hne; unfold apply in Hw.
  destruct (nth_error (fst (find m (v_label v))) (v_index v)) as [t|] eqn:E.
  - destruct t as [h n|p]; cbn [resolve] in Hw; [|discriminate].
    injection Hw as <-; cbn [v_label v_index].
    pose proof (slot_bound m v h n Hm E); lia.
  - injection Hw as <-; contradiction.
Qed.

Lemma pnormal_none (m : raw payload) i :
  pnormal_raw m = true -> apply m (mk_var None i) = inl (mk_var None (i + count m None)).
Proof.
  unfold pnormal_raw, apply; cbn [v_label v_index].
  destruct (fst (find m None)) eqn:E; [|discriminate]; intros _.
  rewrite nth_error_nil; cbn [length]; do 2 f_equal; lia.
Qed.

Lemma pnormal_count_le ρ1 ρ2 :
  nnormal ρ1 = true -> pnormal_raw (nraw ρ1) = true ->
  nnormal ρ2 = true -> pnormal_raw (nraw ρ2) = true ->
  (forall v, v_label v <> None -> napply ρ1 v = napply ρ2 v) ->
  count (nraw ρ1) None <= count (nraw ρ2) None.
Proof.
  intros Hn1 Hp1 Hn2 Hp2 Heq.
  apply nnormal_normal in Hn1, Hn2.
  destruct (count (nraw ρ1) None) as [|c] eqn:Ec; [lia|].
  pose proof Hp1 as Hp1'.
  unfold pnormal_raw in Hp1'; rewrite Ec in Hp1'; cbn [Nat.eqb orb] in Hp1'.
  apply andb_true_iff in Hp1' as [Hnil Hr].
  destruct (fst (find (nraw ρ1) None)) eqn:Ef; [|discriminate].
  apply existsb_exists in Hr as [[[v h] [|n]] [Hin Hh]]; [|discriminate].
  apply label_eqb_eq in Hh; subst h.
  apply In_refs in Hin; [|exact Hn1].
  assert (Hv : v_label v <> None).
  { intros Hl; rewrite Hl, Ef, nth_error_nil in Hin; discriminate. }
  assert (Ha1 : napply ρ1 v = inl (mk_var None c)).
  { unfold napply, apply; rewrite Hin; cbn [resolve]; rewrite Ec; do 2 f_equal; lia. }
  rewrite Heq in Ha1 by exact Hv.
  pose proof (slot_image _ _ _ Hn2 Ha1) as H; cbn [v_label v_index] in H.
  assert (c < count (nraw ρ2) None) by (apply H; congruence); lia.
Qed.

Theorem pcanonical ρ1 ρ2 :
  nnormal ρ1 = true -> pnormal_raw (nraw ρ1) = true ->
  nnormal ρ2 = true -> pnormal_raw (nraw ρ2) = true ->
  (forall v, v_label v <> None -> napply ρ1 v = napply ρ2 v) ->
  ρ1 = ρ2.
Proof.
  intros Hn1 Hp1 Hn2 Hp2 Heq.
  assert (Hc : count (nraw ρ1) None = count (nraw ρ2) None).
  { apply Nat.le_antisymm; apply pnormal_count_le; auto.
    intros v Hv; symmetry; apply Heq, Hv. }
  destruct ρ1 as [m1], ρ2 as [m2]; f_equal.
  apply canonical; [apply (nnormal_normal (NAdj m1)), Hn1|apply (nnormal_normal (NAdj m2)), Hn2|].
  intros [h i]; destruct h as [x|].
  - apply (Heq (mk_var (Some x) i)); discriminate.
  - cbn [nraw] in *; rewrite !pnormal_none, Hc by assumption; reflexivity.
Qed.

(** ** Laws of composition *)

Definition nidentity : nadj T := NAdj identity.

Lemma nnormal_identity : nnormal nidentity = true.
Proof. reflexivity. Qed.

Lemma napply_identity v : napply nidentity v = inl v.
Proof. apply apply_identity. Qed.

Lemma pnormal_identity : pnormal_raw (nraw nidentity) = true.
Proof. reflexivity. Qed.

Lemma napply_prestrict ρ v :
  nnormal ρ = true -> v_label v <> None -> napply (prestrict ρ) v = napply ρ v.
Proof.
  destruct ρ as [m]; intros Hn Hv; unfold napply; cbn [prestrict nraw].
  apply (restrict_spec None m (nnormal_normal (NAdj m) Hn)), Hv.
Qed.

Lemma payload_normal m p :
  nnormal (NAdj m) = true -> binds_in m p ->
  nnormal (snd p) = true /\ pnormal_raw (nraw (snd p)) = true.
Proof. intros Hn Hb; apply (proj1 (payloads_ok_binds m) (nnormal_payloads m Hn) p Hb). Qed.

Lemma napply_payload a v p :
  nnormal a = true -> napply a v = inr p ->
  nnormal (snd p) = true /\ pnormal_raw (nraw (snd p)) = true.
Proof.
  destruct a as [m]; intros Hn Hv; apply (payload_normal m p Hn).
  apply (binds_in_apply m v p Hv).
Qed.

(** Adjustments are equal when they act the same. *)
Theorem nextensionality a b :
  nnormal a = true -> nnormal b = true -> (forall v, napply a v = napply b v) -> a = b.
Proof.
  destruct a as [ma], b as [mb]; intros Ha Hb H; f_equal.
  apply canonical; [apply (nnormal_normal (NAdj ma) Ha)|apply (nnormal_normal (NAdj mb) Hb)|].
  exact H.
Qed.

Lemma prestrict_pnormal ρ :
  nnormal ρ = true -> pnormal_raw (nraw ρ) = true -> prestrict ρ = ρ.
Proof.
  intros Hn Hp; apply pcanonical; try apply nnormal_prestrict; auto.
  intros v Hv; apply napply_prestrict; assumption.
Qed.

Lemma prestrict_ncompose_prestrict a x :
  nnormal a = true -> nnormal x = true ->
  prestrict (ncompose a (prestrict x)) = prestrict (ncompose a x).
Proof.
  intros Ha Hx.
  pose proof (proj1 (nnormal_prestrict x Hx)) as Hrx.
  apply pcanonical; try apply nnormal_prestrict; try apply nnormal_ncompose; auto.
  intros v Hv.
  rewrite !napply_prestrict by (try apply nnormal_ncompose; auto).
  rewrite !napply_ncompose by auto.
  rewrite napply_prestrict by auto; reflexivity.
Qed.

Theorem ncompose_identity_r a :
  nnormal a = true -> ncompose a nidentity = a.
Proof.
  intros Ha; apply nextensionality; [apply nnormal_ncompose; auto|exact Ha|].
  intros v; rewrite napply_ncompose, napply_identity by auto; reflexivity.
Qed.

Lemma ncompose_identity_l_depth n :
  forall b, ndepth b <= n -> nnormal b = true -> ncompose nidentity b = b.
Proof.
  induction n as [|n IH]; intros b Hd Hb; [pose proof (ndepth_pos b); lia|].
  apply nextensionality; [apply nnormal_ncompose; auto|exact Hb|].
  intros v; rewrite napply_ncompose by auto.
  destruct (napply b v) as [w|[u ρ]] eqn:E; [apply napply_identity|].
  pose proof (napply_payload b v _ Hb E) as [Hn Hp]; cbn [fst snd] in *.
  assert (ndepth ρ < ndepth b).
  { destruct b as [m]; apply (ndepth_binds m (u, ρ)), (binds_in_apply m v), E. }
  rewrite (IH ρ) by (auto; lia).
  rewrite prestrict_pnormal by assumption; reflexivity.
Qed.

Theorem ncompose_identity_l b : nnormal b = true -> ncompose nidentity b = b.
Proof. apply (ncompose_identity_l_depth (ndepth b)); lia. Qed.

Lemma ncompose_assoc_depth a b n :
  nnormal a = true -> nnormal b = true ->
  forall c, ndepth c <= n -> nnormal c = true ->
  ncompose a (ncompose b c) = ncompose (ncompose a b) c.
Proof.
  intros Ha Hb; induction n as [|n IH]; intros c Hd Hc; [pose proof (ndepth_pos c); lia|].
  apply nextensionality; try (repeat apply nnormal_ncompose; auto).
  intros v; rewrite !napply_ncompose by (try apply nnormal_ncompose; auto).
  destruct (napply c v) as [w|[u ρ]] eqn:E.
  - rewrite napply_ncompose by auto; reflexivity.
  - cbn [fst snd].
    pose proof (napply_payload c v _ Hc E) as [Hn _]; cbn [snd] in Hn.
    assert (ndepth ρ < ndepth c).
    { destruct c as [m]; apply (ndepth_binds m (u, ρ)), (binds_in_apply m v), E. }
    rewrite prestrict_ncompose_prestrict by (try apply nnormal_ncompose; auto).
    rewrite (IH ρ) by (auto; lia); reflexivity.
Qed.

Theorem ncompose_assoc a b c :
  nnormal a = true -> nnormal b = true -> nnormal c = true ->
  ncompose a (ncompose b c) = ncompose (ncompose a b) c.
Proof. intros Ha Hb Hc; apply (ncompose_assoc_depth a b (ndepth c)); auto. Qed.

End Nested.
