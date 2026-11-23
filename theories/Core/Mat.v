(** * Materialising payloads

    A term with a payload, [x := u⟨| p ⟩], is turned into the term [u [p]]
    with the identity payload, [x := u [p]], where it stands: nothing is
    done to [p].  On reified expressions: an entry [NBindE u p] becomes
    [NBindE k NId] for a new term [k] that is [u [p]].  A shared
    definition whose entries change is a new atom, related to the old one
    variable by variable.

    [mrel] checks that one expression is such a materialisation of
    another: the same, except for materialised entries and for atoms
    that are a changed definition and its new version ([am]), with the
    changes only where nothing is applied after them (an entry, the rest
    of an entry, the outer side of a composition, a payload, a look-up).
    [mrel_sound]: the results of the two are related by the bases the
    substitution law is about ([Conv.lawbase]): [matbase] for a
    materialised entry, inside payloads and through changed definitions. *)

From Stdlib Require Import List Arith Lia NArith Bool.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Scoped Indexed Normalise HShow Braun HShowB Conv.
Import ListNotations.

(** ** Syntactic equality *)

Fixpoint aeqb (a b : aexpN) : bool :=
  match a, b with
  | NId, NId => true
  | NAtom n, NAtom n' => N.eqb n n'
  | NCompose a1 a2, NCompose b1 b2 => aeqb a1 b1 && aeqb a2 b2
  | NOuter h a, NOuter h' b => lexp_eqb h h' && aeqb a b
  | NInner h t a, NInner h' t' b => lexp_eqb h h' && teqb t t' && aeqb a b
  | NLift h a, NLift h' b => lexp_eqb h h' && aeqb a b
  | _, _ => false
  end
with teqb (t t' : texpN) : bool :=
  match t, t' with
  | NVarE h i, NVarE h' i' => lexp_eqb h h' && N.eqb i i'
  | NBindE u p, NBindE u' p' => N.eqb u u' && aeqb p p'
  | NShiftE h s, NShiftE h' s' => lexp_eqb h h' && teqb s s'
  | NLookE h i a, NLookE h' i' a' => lexp_eqb h h' && N.eqb i i' && aeqb a a'
  | _, _ => false
  end.

Lemma eqb_sound : (forall a b, aeqb a b = true -> a = b) /\ (forall t t', teqb t t' = true -> t = t').
Proof.
  apply expN_mind.
  - intros [] H; try discriminate; reflexivity.
  - intros n [] H; try discriminate; apply N.eqb_eq in H; subst; reflexivity.
  - intros a IHa b IHb [] H; try discriminate; cbn [aeqb] in H; apply andb_true_iff in H as [H1 H2].
    rewrite (IHa _ H1), (IHb _ H2); reflexivity.
  - intros h a IH [] H; try discriminate; cbn [aeqb] in H; apply andb_true_iff in H as [H1 H2].
    apply lexp_eqb_eq in H1; subst; rewrite (IH _ H2); reflexivity.
  - intros h t IHt a IHa [] H; try discriminate; cbn [aeqb] in H; apply andb_true_iff in H as [H H3];
      apply andb_true_iff in H as [H1 H2].
    apply lexp_eqb_eq in H1; subst; rewrite (IHt _ H2), (IHa _ H3); reflexivity.
  - intros h a IH [] H; try discriminate; cbn [aeqb] in H; apply andb_true_iff in H as [H1 H2].
    apply lexp_eqb_eq in H1; subst; rewrite (IH _ H2); reflexivity.
  - intros h i [] H; try discriminate; cbn [teqb] in H; apply andb_true_iff in H as [H1 H2].
    apply lexp_eqb_eq in H1; apply N.eqb_eq in H2; subst; reflexivity.
  - intros u p IH [] H; try discriminate; cbn [teqb] in H; apply andb_true_iff in H as [H1 H2].
    apply N.eqb_eq in H1; subst; rewrite (IH _ H2); reflexivity.
  - intros h s IH [] H; try discriminate; cbn [teqb] in H; apply andb_true_iff in H as [H1 H2].
    apply lexp_eqb_eq in H1; subst; rewrite (IH _ H2); reflexivity.
  - intros h i a IH [] H; try discriminate; cbn [teqb] in H; apply andb_true_iff in H as [H H3];
      apply andb_true_iff in H as [H1 H2].
    apply lexp_eqb_eq in H1; apply N.eqb_eq in H2; subst; rewrite (IH _ H3); reflexivity.
Qed.

(** ** The check *)

Section Check.

(** [am]: a changed definition's atom and its new version's; [mf]: a
    new term [k] that is [u [q]], [q] in the new atoms. *)
Variable am : list (N * N).
Variable mf : list (N * (N * aexpN)).
(** Changed atoms below [bound] only. *)
Variable bound : N.

Definition amap (n n' : N) : bool := existsb (fun '(o, o') => N.eqb o n && N.eqb o' n') am.

Fixpoint mrel (e e' : aexpN) : bool :=
  match e, e' with
  | NId, NId => true
  | NAtom n, NAtom n' => N.eqb n n' || (amap n n' && N.ltb n bound)
  | NCompose a b, NCompose a' b' => mrel a a' && aeqb b b'
  | NOuter h a, NOuter h' a' => lexp_eqb h h' && aeqb a a'
  | NInner h t a, NInner h' t' a' => lexp_eqb h h' && trel t t' && mrel a a'
  | NLift h a, NLift h' a' => lexp_eqb h h' && aeqb a a'
  | _, _ => false
  end
with trel (t t' : texpN) : bool :=
  match t, t' with
  | NVarE h i, NVarE h' i' => lexp_eqb h h' && N.eqb i i'
  | NBindE u p, NBindE u' p' =>
      (N.eqb u u' && mrel p p')
      || match p' with
         | NId => match nlook u' mf with Some (u0, q) => N.eqb u u0 && mrel p q | None => false end
         | _ => false
         end
  | NShiftE h s, NShiftE h' s' => lexp_eqb h h' && teqb s s'
  | NLookE h i a, NLookE h' i' a' => lexp_eqb h h' && N.eqb i i' && mrel a a'
  | _, _ => false
  end.

End Check.

(** The changed definitions, each a materialisation of the old one in
    which only definitions changed before it change ([defs]: each atom's
    definition, if it is one). *)
Definition dget (defs : list (option aexpN)) (n : N) : option aexpN :=
  match nth_error defs (N.to_nat n) with Some (Some d) => Some d | _ => None end.

Definition mchain (am : list (N * N)) (mf : list (N * (N * aexpN))) (defs : list (option aexpN)) : bool :=
  forallb (fun '(n, n') =>
             match dget defs n, dget defs n' with
             | Some d, Some d' => mrel am mf n d d'
             | _, _ => false
             end) am.

(** ** Soundness *)

Section Sound.

Context {term : nat -> Type}.
Variable tv : forall K, var K -> term K.
Variable sub : forall K M, adj term K M -> term K -> term M.
Local Notation P := {K & term K}.
Variables (Le : braun label) (Te : braun P) (Ae : braun (radj P)).

Local Notation den := (aedenB Le Te Ae).
Local Notation tden := (tedenB Le Te Ae).
Local Notation B := (lawbase tv sub).

Definition at_ (n : N) : radj P := match bnth Ae n with Some x => x | None => ridentity end.

Definition arel (A A' : radj P) : Prop := forall v, drel B (rapply A v) (rapply A' v).

Variable am : list (N * N).
Variable mf : list (N * (N * aexpN)).

Hypothesis Hmf : Forall (fun '(k, (u, q)) => exists K M (c : adj term K M) (x : term K),
                           adj_raw c = den q /\ bnth Te u = Some (existT term K x)
                           /\ bnth Te k = Some (existT term M (sub K M c x))) mf.

Lemma arel_refl A : arel A A.
Proof. intros v; apply DEq. Qed.

Lemma pay_rel x W W' : arel W W' -> drel B (inr (x, W)) (inr (x, W')).
Proof.
  intros H; rewrite <- (rcompose_identity_r W), <- (rcompose_identity_r W'); apply DPay, H.
Qed.

Lemma tres_bind' u p : rtarget_result (tden (NBindE u p))
  = match bnth Te u with Some x => inr (x, den p) | None => inl (mk_rvar None 0) end.
Proof. cbn [tedenB]; destruct (bnth Te u); reflexivity. Qed.

Lemma tres_look' h i a : rtarget_result (tden (NLookE h i a)) = rapply (den a) (mk_rvar (ldenB Le h) (N.to_nat i)).
Proof.
  change (tden (NLookE h i a)) with (rapply_target (den a) (RRename (mk_rvar (ldenB Le h) (N.to_nat i)))).
  unfold rapply_target; destruct (rapply _ _) as [w|[u ρ]]; reflexivity.
Qed.

Theorem mrel_sound bound :
  (forall n n', amap am n n' = true -> N.lt n bound -> arel (at_ n) (at_ n')) ->
  (forall e e', mrel am mf bound e e' = true -> arel (den e) (den e'))
  /\ (forall t t', trel am mf bound t t' = true -> drel B (rtarget_result (tden t)) (rtarget_result (tden t'))).
Proof.
  intros Ha.
  assert (Same : forall e e', aeqb e e' = true -> den e = den e') by (intros e e' H; rewrite (proj1 eqb_sound _ _ H); reflexivity).
  assert (TSame : forall t t', teqb t t' = true -> tden t = tden t') by (intros t t' H; rewrite (proj2 eqb_sound _ _ H); reflexivity).
  apply expN_mind.
  - intros [] H; try discriminate; apply arel_refl.
  - intros n [] H; try discriminate; cbn [mrel] in H; apply orb_true_iff in H as [H|H].
    + apply N.eqb_eq in H; subst; apply arel_refl.
    + apply andb_true_iff in H as [H1 H2]; apply N.ltb_lt in H2; exact (Ha _ _ H1 H2).
  - intros a IHa b _ [] H; try discriminate; cbn [mrel] in H; apply andb_true_iff in H as [H1 H2].
    intros v; cbn [aedenB]; rewrite (Same _ _ H2), !rapply_compose.
    destruct (rapply (den _) v) as [w|[u ρ]]; [apply (IHa _ H1)|apply DPay, (IHa _ H1)].
  - intros h a _ [] H; try discriminate; cbn [mrel] in H; apply andb_true_iff in H as [H1 H2].
    apply lexp_eqb_eq in H1; subst; cbn [aedenB]; rewrite (Same _ _ H2); apply arel_refl.
  - intros h t IHt a IHa [] H; try discriminate; cbn [mrel] in H; apply andb_true_iff in H as [H H3];
      apply andb_true_iff in H as [H1 H2]; apply lexp_eqb_eq in H1; subst.
    intros v; cbn [aedenB]; rewrite !rapply_push_inner.
    destruct (rvar_eqb v _); [apply (IHt _ H2)|apply (IHa _ H3)].
  - intros h a _ [] H; try discriminate; cbn [mrel] in H; apply andb_true_iff in H as [H1 H2].
    apply lexp_eqb_eq in H1; subst; cbn [aedenB]; rewrite (Same _ _ H2); apply arel_refl.
  - intros h i [] H; try discriminate; cbn [trel] in H; apply andb_true_iff in H as [H1 H2].
    apply lexp_eqb_eq in H1; apply N.eqb_eq in H2; subst; apply DEq.
  - intros u p IH [h0 i0|k p'|h0 s0|h0 i0 a0] H; try discriminate; cbn [trel] in H; apply orb_true_iff in H as [H|H].
    + apply andb_true_iff in H as [H1 H2]; apply N.eqb_eq in H1; subst.
      rewrite !tres_bind'; destruct (bnth Te _); [apply pay_rel, (IH _ H2)|apply DEq].
    + destruct p'; try discriminate.
      destruct (nlook k mf) as [[u0 q]|] eqn:En; [|discriminate].
      apply andb_true_iff in H as [H1 H2]; apply N.eqb_eq in H1; subst u0.
      pose proof (nlook_in _ _ _ En) as Hin; rewrite Forall_forall in Hmf.
      destruct (Hmf _ Hin) as [K [M [c [x [Ec [Eu Ek]]]]]].
      rewrite !tres_bind', Eu, Ek.
      eapply DTrans; [apply pay_rel, (IH _ H2)|].
      rewrite <- Ec; apply DBase; left; exists K, M, x, c; split; reflexivity.
  - intros h s _ [] H; try discriminate; cbn [trel] in H; apply andb_true_iff in H as [H1 H2].
    apply lexp_eqb_eq in H1; subst; cbn [tedenB]; rewrite (TSame _ _ H2); apply DEq.
  - intros h i a IH [] H; try discriminate; cbn [trel] in H; apply andb_true_iff in H as [H H3];
      apply andb_true_iff in H as [H1 H2]; apply lexp_eqb_eq in H1; apply N.eqb_eq in H2; subst.
    rewrite !tres_look'; apply (IH _ H3).
Qed.

(** The changed definitions are related, each from those before it. *)
Theorem mchain_sound defs :
  (forall n d, dget defs n = Some d -> at_ n = den d) ->
  mchain am mf defs = true ->
  forall n n', amap am n n' = true -> arel (at_ n) (at_ n').
Proof.
  intros Hd Hc.
  assert (All : forall k n n', N.to_nat n < k -> amap am n n' = true -> arel (at_ n) (at_ n')).
  { intros k; induction k as [|k IH]; intros n n' Lt Hn; [lia|].
    unfold amap in Hn; apply existsb_exists in Hn as [[o o'] [Hin Ho]].
    apply andb_true_iff in Ho as [E1 E2]; apply N.eqb_eq in E1; apply N.eqb_eq in E2; subst o o'.
    unfold mchain in Hc; rewrite forallb_forall in Hc; specialize (Hc _ Hin); cbn beta iota in Hc.
    destruct (dget defs n) as [d|] eqn:Ed, (dget defs n') as [d'|] eqn:Ed'; try discriminate.
    rewrite (Hd _ _ Ed), (Hd _ _ Ed').
    refine (proj1 (mrel_sound n _) _ _ Hc).
    intros m m' Hm Lm; apply (IH m m'); [lia|exact Hm]. }
  intros n n' Hn; exact (All (S (N.to_nat n)) n n' (Nat.lt_succ_diag_r _) Hn).
Qed.

(** The whole: a materialised expression's results are related to the
    original's. *)
Theorem mat_sound defs e e' :
  (forall n d, dget defs n = Some d -> at_ n = den d) ->
  mchain am mf defs = true ->
  mrel am mf (N.of_nat (S (List.length defs))) e e' = true ->
  arel (den e) (den e').
Proof.
  intros Hd Hc Hm; refine (proj1 (mrel_sound _ _) _ _ Hm).
  intros n n' Hn _; exact (mchain_sound defs Hd Hc n n' Hn).
Qed.

End Sound.

(** The definitions' facts, from the form the tactic proves them in. *)
Lemma dget_facts {X : Type} (den : aexpN -> X) (Ae : braun X) (dflt : X) (atoms : list X) defs :
  Ae = bof atoms ->
  Forall2 (fun x od => match od with Some d => x = den d | None => True end) atoms defs ->
  forall n d, dget defs n = Some d -> match bnth Ae n with Some x => x | None => dflt end = den d.
Proof.
  intros -> H n d E; unfold dget in E; rewrite bnth_bof.
  destruct (nth_error defs (N.to_nat n)) as [[d0|]|] eqn:Ed; try discriminate; injection E as ->.
  destruct (F2_nth _ _ _ _ _ H Ed) as [x [Ex Hx]]; rewrite Ex; exact Hx.
Qed.

(** ** Materialising a shown normal form

    [amat_disp base off nt sh root]: the shown definitions [sh] (atoms
    [base], [base + 1], …) and expression [root], with each entry with a
    payload materialised, the payload's own entries first.  A definition's
    new version is the atom [off] after it; the new terms are numbered
    from [nt].  The result, with the new terms, is checked by [mrel]: a
    payload in a place [mrel] does not allow is left as it is, and the
    check fails. *)
Section Disp.

Variables (base off : N).

Definition renum (n : N) : N := if N.leb base n then n + off else n.

Fixpoint amat_e (e : aexpN) (k : N) (acc : list (N * (N * aexpN))) {struct e} : aexpN * N * list (N * (N * aexpN)) :=
  match e with
  | NId => (NId, k, acc)
  | NAtom n => (NAtom (renum n), k, acc)
  | NCompose a b => let '(a', k1, acc1) := amat_e a k acc in (NCompose a' b, k1, acc1)
  | NOuter h a => (NOuter h a, k, acc)
  | NInner h t a =>
      let '(t', k1, acc1) := amat_t t k acc in
      let '(a', k2, acc2) := amat_e a k1 acc1 in (NInner h t' a', k2, acc2)
  | NLift h a => (NLift h a, k, acc)
  end
with amat_t (t : texpN) (k : N) (acc : list (N * (N * aexpN))) {struct t} : texpN * N * list (N * (N * aexpN)) :=
  match t with
  | NVarE h i => (NVarE h i, k, acc)
  | NBindE u NId => (NBindE u NId, k, acc)
  | NBindE u p => let '(p', k1, acc1) := amat_e p k acc in (NBindE k1 NId, N.succ k1, (k1, (u, p')) :: acc1)
  | NShiftE h s => (NShiftE h s, k, acc)
  | NLookE h i a => let '(a', k1, acc1) := amat_e a k acc in (NLookE h i a', k1, acc1)
  end.

Fixpoint amat_l (l : list aexpN) (k : N) (acc : list (N * (N * aexpN))) : list aexpN * N * list (N * (N * aexpN)) :=
  match l with
  | [] => ([], k, acc)
  | d :: l' => let '(d', k1, acc1) := amat_e d k acc in let '(l'', k2, acc2) := amat_l l' k1 acc1 in (d' :: l'', k2, acc2)
  end.

End Disp.

(** The new definitions, expression and terms (in the order they are
    numbered), and the pairs of old and new definitions. *)
Definition amat_disp (base nt : N) (sh : list aexpN) (root : aexpN)
  : list aexpN * aexpN * list (N * (N * aexpN)) * list (N * N) :=
  let off := N.of_nat (List.length sh) in
  let '(sh', k1, acc1) := amat_l base off sh nt [] in
  let '(root', _, acc2) := amat_e base off root k1 acc1 in
  (sh', root', rev acc2, List.map (fun i => (base + N.of_nat i, base + off + N.of_nat i)%N) (seq 0 (List.length sh))).

(** Two relations joined at an expression read in two environments, the
    same by conversion. *)
Lemma arel_trans {T} (B : rresult T -> rresult T -> Prop) (A X Y Z : radj T) :
  (forall v, drel B (rapply A v) (rapply X v)) -> X = Y -> (forall v, drel B (rapply Y v) (rapply Z v)) ->
  forall v, drel B (rapply A v) (rapply Z v).
Proof. intros H1 -> H2 v; eapply DTrans; [apply H1|apply H2]. Qed.
