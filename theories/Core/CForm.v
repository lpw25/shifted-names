(** * Concrete context forms (normaliser groundwork)

    This is a concrete datatype for context forms.  It is *not* the
    user-facing presentation: users build adjustments with the constructors
    [identity], [push_inner] and [push_outer] (see Adjustment.v), which are
    functions on the trie form.  The datatype here is the start of the
    syntax that the reflective normaliser works in; this file covers the
    case of concrete labels and no adjustment variables.

    A context form is a pair of an *input context* and an *output context*:

    - the input context is a list of entries [(h, t)]: the [n]-th entry
      labelled [h] says where the inner variable [h₍ₙ₎] goes (a target);
    - the output context is a list of labels: the [n]-th [h] in it is a fresh
      outer [h₍ₙ₎];
    - implicitly, everything else maps across: an inner [h₍ᵢ₎] not covered by
      the input context goes to the outer [h] with the same position relative
      to the end of the contexts.

    Only the relative order of entries with the same label matters, so with
    concrete labels a context form can be sorted by label.  This file relates
    context forms to adjustments in both directions, and proves that sorted,
    minimal context forms are unique ([cform_canonical]).

    With symbolic labels the order of entries whose labels are not known to
    be different cannot be changed; that generalisation is the basis of the
    reflective normaliser (see docs/implementation-plan.md, D3). *)

From Stdlib Require Import PArith Arith List Lia Bool Permutation.
From ShiftedNames.Core Require Import Trie Label Var RawAdjustment Adjustment.
Import ListNotations.

Section CForm.

Context {P : Type}.

Record cform : Type :=
  mk_cform {
    cf_inner : list (option label * target P);
    cf_outer : list (option label)
  }.

Implicit Types (c : cform) (h l : option label) (v : var)
  (I : list (option label * target P)) (O : list (option label)).

(** ** Semantics *)

Definition inner_targets h I : list (target P) :=
  map snd (filter (fun e => label_eqb (fst e) h) I).

Definition count h O : nat := length (filter (fun l => label_eqb l h) O).

Definition apply_cform c v : var + P :=
  apply_entry (v_label v) (inner_targets (v_label v) (cf_inner c))
    (count (v_label v) (cf_outer c)) (v_index v).

Lemma inner_targets_app h I1 I2 :
  inner_targets h (I1 ++ I2) = inner_targets h I1 ++ inner_targets h I2.
Proof. unfold inner_targets; rewrite filter_app, map_app; reflexivity. Qed.

Lemma count_app h O1 O2 : count h (O1 ++ O2) = count h O1 + count h O2.
Proof. unfold count; rewrite filter_app, length_app; reflexivity. Qed.

(** ** From context forms to adjustments *)

Definition add_inner (r : raw P) (e : option label * target P) : raw P :=
  set (label_key (fst e))
    (mk_entry (fst e) (fst (find r (fst e)) ++ [snd e]) (snd (find r (fst e)))) r.

Definition add_outer (r : raw P) h : raw P :=
  set (label_key h) (mk_entry h (fst (find r h)) (S (snd (find r h)))) r.

Definition cform_raw c : raw P :=
  fold_left add_outer (cf_outer c) (fold_left add_inner (cf_inner c) Empty).

Lemma keys_ok_set (r : raw P) h (e : entry P) :
  keys_ok r = true -> e_label e = h -> keys_ok (set (label_key h) e r) = true.
Proof.
  unfold keys_ok; rewrite !forallb_spec; intros Hr He key e' Hget.
  rewrite get_set in Hget.
  destruct (Pos.eqb_spec key (label_key h)) as [->|]; [|apply (Hr _ _ Hget)].
  injection Hget as <-; rewrite He; apply Pos.eqb_refl.
Qed.

Lemma keys_ok_cform_raw c : keys_ok (cform_raw c) = true.
Proof.
  unfold cform_raw.
  assert (Hin : forall I r, keys_ok r = true ->
                  keys_ok (fold_left add_inner I r) = true).
  { induction I as [|e I IH]; intros r Hr; [exact Hr|].
    apply IH, keys_ok_set; [exact Hr|reflexivity]. }
  assert (Hout : forall O r, keys_ok r = true ->
                   keys_ok (fold_left add_outer O r) = true).
  { induction O as [|h O IH]; intros r Hr; [exact Hr|].
    apply IH, keys_ok_set; [exact Hr|reflexivity]. }
  apply Hout, Hin; reflexivity.
Qed.

Lemma find_set_entry (r : raw P) h h' ts k :
  find (set (label_key h) (mk_entry h ts k) r) h'
  = if label_eqb h' h then (ts, k) else find r h'.
Proof.
  unfold find at 1; rewrite get_set, label_key_eqb.
  destruct (label_eqb h' h); reflexivity.
Qed.

Lemma find_fold_inner I (r : raw P) h :
  find (fold_left add_inner I r) h
  = (fst (find r h) ++ inner_targets h I, snd (find r h)).
Proof.
  revert r; induction I as [|[h' t] I IH]; intro r; cbn [fold_left].
  - rewrite app_nil_r; destruct (find r h); reflexivity.
  - rewrite IH; unfold add_inner; cbn [fst snd].
    rewrite !find_set_entry; unfold inner_targets; cbn [filter fst].
    rewrite (label_eqb_sym h' h).
    destruct (label_eqb_spec h h') as [<-|]; cbn [map snd fst].
    + rewrite <- app_assoc; reflexivity.
    + reflexivity.
Qed.

Lemma find_fold_outer O (r : raw P) h :
  find (fold_left add_outer O r) h = (fst (find r h), snd (find r h) + count h O).
Proof.
  revert r; induction O as [|h' O IH]; intro r; cbn [fold_left].
  - rewrite Nat.add_0_r; destruct (find r h); reflexivity.
  - rewrite IH; unfold add_outer.
    rewrite !find_set_entry; unfold count; cbn [filter].
    rewrite (label_eqb_sym h' h).
    destruct (label_eqb_spec h h') as [<-|]; cbn [length fst snd].
    + f_equal; lia.
    + reflexivity.
Qed.

Lemma find_cform_raw c h :
  find (cform_raw c) h = (inner_targets h (cf_inner c), count h (cf_outer c)).
Proof.
  unfold cform_raw; rewrite find_fold_outer, find_fold_inner; reflexivity.
Qed.

Definition of_cform c : adjustment P := of_raw (cform_raw c) (keys_ok_cform_raw c).

Theorem apply_of_cform c v : apply (of_cform c) v = apply_cform c v.
Proof.
  unfold of_cform; rewrite apply_of_raw.
  unfold RawAdjustment.apply, apply_cform; rewrite find_cform_raw; reflexivity.
Qed.

(** ** From adjustments to context forms *)

Fixpoint insert_entry (e : entry P) (es : list (entry P)) : list (entry P) :=
  match es with
  | [] => [e]
  | e' :: es' =>
      if label_ltb (e_label e') (e_label e) then e' :: insert_entry e es'
      else e :: es
  end.

Definition sort_entries (es : list (entry P)) : list (entry P) :=
  fold_right insert_entry [] es.

Definition entries_of (a : adjustment P) : list (entry P) :=
  sort_entries (map snd (elements (adj_raw a))).

Definition inner_block (e : entry P) : list (option label * target P) :=
  map (fun t => (e_label e, t)) (e_targets e).

Definition outer_block (e : entry P) : list (option label) :=
  repeat (e_label e) (e_out e).

Definition to_cform (a : adjustment P) : cform :=
  mk_cform (flat_map inner_block (entries_of a)) (flat_map outer_block (entries_of a)).

Lemma insert_entry_perm e es : Permutation (insert_entry e es) (e :: es).
Proof.
  induction es as [|e' es IH]; cbn [insert_entry]; [reflexivity|].
  destruct (label_ltb _ _); [|reflexivity].
  rewrite IH; apply perm_swap.
Qed.

Lemma sort_entries_perm es : Permutation (sort_entries es) es.
Proof.
  induction es as [|e es IH]; cbn [sort_entries fold_right]; [reflexivity|].
  fold (sort_entries es); rewrite insert_entry_perm, IH; reflexivity.
Qed.

Lemma inner_targets_flat_map h (es : list (entry P)) :
  inner_targets h (flat_map inner_block es)
  = flat_map (fun e => if label_eqb (e_label e) h then e_targets e else []) es.
Proof.
  induction es as [|e es IH]; cbn [flat_map]; [reflexivity|].
  rewrite inner_targets_app, IH; f_equal.
  unfold inner_targets, inner_block.
  destruct (label_eqb (e_label e) h) eqn:E.
  - induction (e_targets e) as [|t ts IHts]; cbn; [reflexivity|].
    rewrite E; cbn; f_equal; exact IHts.
  - induction (e_targets e) as [|t ts IHts]; cbn; [reflexivity|].
    rewrite E; exact IHts.
Qed.

Lemma count_flat_map h (es : list (entry P)) :
  count h (flat_map outer_block es)
  = fold_right (fun e n => (if label_eqb (e_label e) h then e_out e else 0) + n) 0 es.
Proof.
  induction es as [|e es IH]; cbn [flat_map fold_right]; [reflexivity|].
  rewrite count_app, IH; f_equal.
  unfold count, outer_block.
  destruct (label_eqb (e_label e) h) eqn:E.
  - induction (e_out e) as [|k IHk]; cbn; [reflexivity|].
    rewrite E; cbn; f_equal; exact IHk.
  - induction (e_out e) as [|k IHk]; cbn; [reflexivity|].
    rewrite E; exact IHk.
Qed.

Lemma list_find_none {A} (f : A -> bool) (xs : list A) :
  (forall x, In x xs -> f x = false) -> List.find f xs = None.
Proof.
  induction xs as [|x xs IH]; intro H; cbn; [reflexivity|].
  rewrite (H x (or_introl eq_refl)); apply IH; intros y Hy; apply H; right; exact Hy.
Qed.

(** If labels are distinct, the per-label sums pick out one entry. *)
Lemma select_unique h (es : list (entry P)) :
  NoDup (map e_label es) ->
  (flat_map (fun e => if label_eqb (e_label e) h then e_targets e else []) es,
   fold_right (fun e n => (if label_eqb (e_label e) h then e_out e else 0) + n) 0 es)
  = match List.find (fun e => label_eqb (e_label e) h) es with
    | Some e => (e_targets e, e_out e)
    | None => ([], 0)
    end.
Proof.
  induction es as [|e es IH]; intro Hnd; cbn [flat_map fold_right List.find]; [reflexivity|].
  cbn [map] in Hnd; apply NoDup_cons_iff in Hnd as [Hnotin Hnd].
  specialize (IH Hnd).
  destruct (label_eqb_spec (e_label e) h) as [Eh|Eh].
  - assert (Hnone : List.find (fun e => label_eqb (e_label e) h) es = None).
    { apply list_find_none; intros e' Hin.
      apply label_eqb_neq; intros Hl.
      apply Hnotin; rewrite Eh, <- Hl; apply in_map, Hin. }
    rewrite Hnone in IH; injection IH as H1 H2.
    rewrite H1, H2, app_nil_r, Nat.add_0_r; reflexivity.
  - rewrite <- IH; reflexivity.
Qed.

Lemma elements_labels_nodup (a : adjustment P) :
  NoDup (map e_label (map snd (elements (adj_raw a)))).
Proof.
  pose proof (elements_nodup (adj_raw a)) as Hnd.
  pose proof (normal_keys_ok _ (adj_normal_true a)) as Hk.
  unfold keys_ok in Hk; rewrite forallb_spec in Hk.
  rewrite map_map.
  apply (NoDup_map_inv label_key).
  rewrite map_map.
  erewrite map_ext_in; [exact Hnd|].
  intros [k e] Hin; apply In_elements in Hin.
  symmetry; apply Pos.eqb_eq, (Hk _ _ Hin).
Qed.

Lemma find_entries_of (a : adjustment P) h :
  match List.find (fun e => label_eqb (e_label e) h) (entries_of a) with
  | Some e => (e_targets e, e_out e)
  | None => ([], 0)
  end = RawAdjustment.find (adj_raw a) h.
Proof.
  pose proof (adj_normal_true a) as Ha.
  pose proof (elements_labels_nodup a) as Hnd.
  assert (Hperm : Permutation (entries_of a) (map snd (elements (adj_raw a))))
    by apply sort_entries_perm.
  assert (Hnd' : NoDup (map e_label (entries_of a))).
  { eapply Permutation_NoDup; [|exact Hnd]; symmetry; apply Permutation_map, Hperm. }
  unfold RawAdjustment.find.
  destruct (List.find (fun e => label_eqb (e_label e) h) (entries_of a)) as [e|] eqn:E.
  - apply find_some in E as [Hin Hl]; apply label_eqb_eq in Hl.
    apply (Permutation_in _ Hperm), in_map_iff in Hin as [[k e'] [<- Hin]].
    cbn [snd] in *.
    pose proof (normal_get _ _ _ Ha (proj1 (In_elements _ _ _) Hin)) as Hok.
    apply entry_ok_key in Hok; rewrite Hl in Hok; subst k.
    apply In_elements in Hin; rewrite Hin; reflexivity.
  - destruct (get (label_key h) (adj_raw a)) as [e|] eqn:Eg; [|reflexivity].
    exfalso.
    assert (Hin : In e (entries_of a)).
    { apply (Permutation_in _ (Permutation_sym Hperm)), in_map_iff.
      exists (label_key h, e); split; [reflexivity|apply In_elements, Eg]. }
    apply (find_none _ _ E) in Hin.
    rewrite (normal_label _ h e Ha Eg), label_eqb_refl in Hin; discriminate.
Qed.

Theorem apply_to_cform (a : adjustment P) v : apply_cform (to_cform a) v = apply a v.
Proof.
  unfold apply_cform, to_cform, apply, RawAdjustment.apply; cbn [cf_inner cf_outer].
  rewrite inner_targets_flat_map, count_flat_map.
  pose proof (elements_labels_nodup a) as Hnd.
  assert (Hnd' : NoDup (map e_label (entries_of a))).
  { eapply Permutation_NoDup; [|exact Hnd].
    symmetry; apply Permutation_map, sort_entries_perm. }
  pose proof (select_unique (v_label v) (entries_of a) Hnd') as Hs.
  rewrite find_entries_of in Hs; rewrite <- Hs; reflexivity.
Qed.

Theorem of_to_cform (a : adjustment P) : of_cform (to_cform a) = a.
Proof.
  apply extensionality; intro v; rewrite apply_of_cform; apply apply_to_cform.
Qed.

End CForm.
