(** * Where a variable ends up

    The key of a variable in front of a layered word: the atom it gets
    stuck at, or its target in the first segment with terms (or in the
    last segment).  Variables with the same key have the same result, so
    one can stand for the other in what comes before the word. *)

From Stdlib Require Import Arith List Lia Bool.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Layered Canon.
Import ListNotations.

Inductive vkey : Type :=
| KT (d : nat) (t : ntgt)
| KS (d : nat) (a : nat) (g : lexp) (i : nat).

Definition vkey_eqb (x y : vkey) : bool :=
  match x, y with
  | KT d t, KT d' t' => Nat.eqb d d' && ntgt_eqb t t'
  | KS d a g i, KS d' a' g' i' => Nat.eqb d d' && Nat.eqb a a' && lexp_eqb g g' && Nat.eqb i i'
  | _, _ => false
  end.

Definition okey_eqb (x y : option vkey) : bool :=
  match x, y with Some p, Some q => vkey_eqb p q | _, _ => false end.

Section Keys.

Variable F : order.

Fixpoint vfollow (K : lword) (g : lexp) (i : nat) : option vkey :=
  match K with
  | [] => Some (KT 0 (NVar g i))
  | LA L a :: r =>
      let c := lcn F L g in
      if i <? c then vfollow r g i else Some (KS (List.length r) a g (i - c))
  | LS s :: r =>
      if has_terms s then option_map (KT (List.length r)) (seg_tgt F s g i)
      else match seg_tgt F s g i with
           | Some (NVar g' i') => match r with [] => Some (KT 0 (NVar g' i')) | _ => vfollow r g' i' end
           | _ => None
           end
  end.

(** The inputs of a word that may share their key with another input. *)
Fixpoint kcands (K : lword) : list (lexp * nat) :=
  match K with
  | [] => []
  | LA L a :: _ =>
      flat_map (fun '(g, n) => match g with LNone => [] | _ => map (fun j => (g, j)) (seq 0 n) end) L
      ++ map (fun j => (LNone, j)) (seq 0 (lcn F L LNone))
  | LS s1 :: r =>
      cands F s1
      ++ (if has_terms s1 then []
          else flat_map (fun w => named_srcs F s1 (NVar (fst w) (snd w))
                                  ++ map (fun k => (LNone, k)) (findix (NVar (fst w) (snd w)) (fst (bent F s1)) 0)
                                  ++ match fst w with
                                     | LNone => let '(ts, m) := bent F s1 in
                                                if m <=? snd w then [(LNone, snd w - m + tlen ts)] else []
                                     | _ => []
                                     end) (kcands r))
  end.

Fixpoint nodup_v (l : list (lexp * nat)) (seen : list (lexp * nat)) : list (lexp * nat) :=
  match l with [] => [] | x :: r => if existsb (veqb x) seen then nodup_v r seen else x :: nodup_v r (x :: seen) end.

(** Each candidate with the variable that stands for its key: the least
    named one, else the least bound one. *)
Definition kmap_g (K : lword) : list ((lexp * nat) * (lexp * nat)) :=
  let keyed := map (fun v => (v, vfollow K (fst v) (snd v))) (nodup_v (kcands K) []) in
  let rep := fun vk =>
    match vmin F (map fst (filter (fun p => negb (lexp_eqb (fst (fst p)) LNone) && okey_eqb (snd p) (snd vk)) keyed)) with
    | Some w => w
    | None => match filter (fun p => lexp_eqb (fst (fst p)) LNone && okey_eqb (snd p) (snd vk)) keyed with
              | p :: _ => fst p
              | [] => fst vk
              end
    end in
  filter (fun p => negb (veqb (fst p) (snd p))) (map (fun vk => (fst vk, rep vk)) keyed).

End Keys.

Lemma vkey_eqb_eq x y : vkey_eqb x y = true -> x = y.
Proof.
  destruct x as [d t|d a g i], y as [d' t'|d' a' g' i']; cbn [vkey_eqb]; try discriminate; intros H.
  - apply andb_true_iff in H as [H1 H2]; apply Nat.eqb_eq in H1; apply (proj1 nf_eqb_eq) in H2; subst; reflexivity.
  - apply andb_true_iff in H as [H H4]; apply andb_true_iff in H as [H H3]; apply andb_true_iff in H as [H1 H2].
    apply Nat.eqb_eq in H1, H2, H4; apply lexp_eqb_eq in H3; subst; reflexivity.
Qed.

Lemma okey_eqb_eq x y : okey_eqb x y = true -> exists k, x = Some k /\ y = Some k.
Proof.
  destruct x as [p|], y as [q|]; cbn [okey_eqb]; try discriminate; intros H.
  apply vkey_eqb_eq in H; subst; exists q; split; reflexivity.
Qed.

Section Sound.

Context {T : Type}.
Variable lenv : list label.
Variable tenv : list T.
Variable aenv : list (radj T).
Variable penv : list (rpadj T).
Variable F : order.
Hypothesis HF : facts_ok lenv F.
Variable ntm : nat.
Hypothesis Hntm : ntm <= List.length tenv.

Local Notation lden := (lden lenv).
Local Notation tden := (tden lenv tenv aenv penv).
Local Notation sden := (sden lenv tenv aenv penv).
Local Notation sdistd := (sdistd lenv).
Local Notation lwden := (lwden lenv tenv aenv penv).
Local Notation lwdist := (lwdist lenv).

Lemma vfollow_depth K : forall g i d a g' i', vfollow F K g i = Some (KS d a g' i') -> d < List.length K.
Proof.
  induction K as [|[s|L a0] r IH]; intros g i d a g' i'; cbn [vfollow]; try discriminate.
  - destruct (has_terms s).
    + destruct (seg_tgt F s g i); cbn [option_map]; discriminate.
    + destruct (seg_tgt F s g i) as [[g1 i1|? ? ?]|]; try discriminate.
      destruct r as [|x r']; [discriminate|]; intros H; apply IH in H; cbn [List.length] in *; lia.
  - destruct (i <? lcn F L g).
    + intros H; apply IH in H; cbn [List.length]; lia.
    + intros H; injection H as <- _ _ _; cbn [List.length]; lia.
Qed.

(** The result of a variable in front of a lifted atom that the lifts
    pass around. *)
Lemma lifted_apply L a r g i : i < lcn F L g ->
  rapply (lwden (LA L a :: r)) (mk_rvar (lden g) i) = rapply (lwden r) (mk_rvar (lden g) i).
Proof.
  intros Hi; cbn [Layered.lwden]; rewrite rapply_compose_cres, (lifts_apply lenv tenv ntm Hntm).
  unfold lcn in Hi; destruct (lcnt F g L) as [c|] eqn:E; [|lia].
  rewrite (lcnt_sound lenv F HF _ _ _ E), (proj2 (Nat.ltb_lt _ _) Hi); reflexivity.
Qed.

Theorem vfollow_sound K : lwdist K -> forall g i g' i' k,
  vfollow F K g i = Some k -> vfollow F K g' i' = Some k ->
  rapply (lwden K) (mk_rvar (lden g) i) = rapply (lwden K) (mk_rvar (lden g') i').
Proof.
  induction K as [|[s|L a] r IH]; intros HK g i g' i' k.
  - cbn [vfollow]; intros H1 H2; rewrite <- H1 in H2; injection H2 as -> ->; reflexivity.
  - inversion HK as [|? ? Hs Hr]; subst; cbn [vfollow Layered.lwden]; rewrite !rapply_compose_cres.
    destruct (has_terms s).
    + destruct (seg_tgt F s g i) as [t|] eqn:E1; [|discriminate].
      destruct (seg_tgt F s g' i') as [t'|] eqn:E2; [|discriminate]; cbn [option_map].
      intros H1 H2; rewrite <- H1 in H2; injection H2 as ->.
      rewrite (proj2 (seg_tgt_sound lenv tenv aenv penv F HF _ _ _ _ Hs E1)),
              (proj2 (seg_tgt_sound lenv tenv aenv penv F HF _ _ _ _ Hs E2)); reflexivity.
    + destruct (seg_tgt F s g i) as [[g1 i1|? ? ?]|] eqn:E1; try discriminate.
      destruct (seg_tgt F s g' i') as [[g2 i2|? ? ?]|] eqn:E2; try (intros _ H; discriminate H).
      rewrite (proj2 (seg_tgt_sound lenv tenv aenv penv F HF _ _ _ _ Hs E1)),
              (proj2 (seg_tgt_sound lenv tenv aenv penv F HF _ _ _ _ Hs E2)).
      destruct r as [|x r'].
      * intros H1 H2; rewrite <- H1 in H2; injection H2 as -> ->; reflexivity.
      * intros H1 H2; cbn [Normalise.tden rtarget_result cres]; exact (IH Hr _ _ _ _ _ H1 H2).
  - inversion HK as [|? ? _ Hr]; subst; cbn [vfollow].
    destruct (Nat.ltb_spec i (lcn F L g)) as [Hi|Hi], (Nat.ltb_spec i' (lcn F L g')) as [Hi'|Hi'].
    + intros H1 H2; rewrite (lifted_apply L a r g i Hi), (lifted_apply L a r g' i' Hi'); exact (IH Hr _ _ _ _ _ H1 H2).
    + intros H1 H2; injection H2 as <-; apply vfollow_depth in H1; lia.
    + intros H1 H2; injection H1 as <-; apply vfollow_depth in H2; lia.
    + intros H1 H2; rewrite <- H1 in H2; injection H2 as -> E; replace i' with i by lia; reflexivity.
Qed.

End Sound.
