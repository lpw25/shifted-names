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

Definition payload : Type := (T * nadj T)%type.

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

End Nested.
