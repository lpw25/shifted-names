(** * Materialising what the display shows

    The display shows a term with its payload, [x := u⟨| p ⟩], only where
    nothing is applied after it: on an entry over the rest of the word, in
    a payload, in a look-up's payload, and on the side of [⨾] applied
    last.  There, the term with its payload can become the term
    substituted by its payload, [x := u [p]], with the identity payload:
    per variable, this is the law's base [matbase].

    [matN] does this on the shown expression, in those positions only.
    Each materialised term becomes a new term index, after the old ones,
    with the identity payload; [matN] lists for each its old term and its
    materialised payload.  The rendering prints the new term as the
    syntax's substitution, and gives one fact per new term
    ([mat_fact]).  Shared definitions are materialised too, so the new
    shared variables mean the materialised definitions: [mat_core] builds
    the old ones' values and relates them to the new, definition by
    definition.

    [matN] also checks what this needs: indices in range, each shared
    definition using only the ones before it, and no shared variable
    where something is applied after it (it would stand for a changed
    value there). *)

From Stdlib Require Import Bool List Arith Lia NArith.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Scoped Indexed Normalise HConcrete CRange HShow Braun HShowB Conv.
Import ListNotations.
Local Open Scope bool_scope.

(** ** The check and the materialisation *)

(** Atoms below [na], terms below [nt]. *)
Fixpoint nrng (nt na : N) (e : aexpN) {struct e} : bool :=
  match e with
  | NId => true
  | NAtom a => N.ltb a na
  | NCompose x y => nrng nt na x && nrng nt na y
  | NOuter _ x => nrng nt na x
  | NLift _ x => nrng nt na x
  | NInner _ t x => trng nt na t && nrng nt na x
  end
with trng (nt na : N) (t : texpN) {struct t} : bool :=
  match t with
  | NVarE _ _ => true
  | NBindE u p => N.ltb u nt && nrng nt na p
  | NShiftE _ t => trng nt na t
  | NLookE _ _ a => nrng nt na a
  end.

(** Atoms below [b]. *)
Fixpoint nbelow (b : N) (e : aexpN) {struct e} : bool :=
  match e with
  | NId => true
  | NAtom a => N.ltb a b
  | NCompose x y => nbelow b x && nbelow b y
  | NOuter _ x => nbelow b x
  | NLift _ x => nbelow b x
  | NInner _ t x => tbelow b t && nbelow b x
  end
with tbelow (b : N) (t : texpN) {struct t} : bool :=
  match t with
  | NVarE _ _ => true
  | NBindE _ p => nbelow b p
  | NShiftE _ t => tbelow b t
  | NLookE _ _ a => nbelow b a
  end.

(** Shared variables (atoms from [b] on) only where nothing is applied
    after them. *)
Fixpoint nsafe (b : N) (e : aexpN) {struct e} : bool :=
  match e with
  | NId => true
  | NAtom _ => true
  | NCompose x y => nsafe b x && nbelow b y
  | NOuter _ x => nbelow b x
  | NLift _ x => nbelow b x
  | NInner _ t x => tsafe b t && nsafe b x
  end
with tsafe (b : N) (t : texpN) {struct t} : bool :=
  match t with
  | NVarE _ _ => true
  | NBindE _ p => nsafe b p
  | NShiftE _ t => tbelow b t
  | NLookE _ _ a => nsafe b a
  end.

Definition is_nid (e : aexpN) : bool := match e with NId => true | _ => false end.

(** The next new term index, and the new terms so far: each its index,
    its old term and its materialised payload. *)
Definition mst : Type := (N * list (N * (N * aexpN)))%type.

Fixpoint amat (s : mst) (e : aexpN) {struct e} : mst * aexpN :=
  match e with
  | NCompose x y => let '(s, x') := amat s x in (s, NCompose x' y)
  | NInner h t x => let '(s, t') := tmat s t in let '(s, x') := amat s x in (s, NInner h t' x')
  | _ => (s, e)
  end
with tmat (s : mst) (t : texpN) {struct t} : mst * texpN :=
  match t with
  | NBindE u p =>
      if is_nid p then (s, t)
      else let '((k, l), p') := amat s p in ((N.succ k, (k, (u, p')) :: l), NBindE k NId)
  | NLookE h i a => let '(s, a') := amat s a in (s, NLookE h i a')
  | _ => (s, t)
  end.

Fixpoint amats (s : mst) (l : list aexpN) : mst * list aexpN :=
  match l with
  | [] => (s, [])
  | d :: ds => let '(s, d') := amat s d in let '(s, ds') := amats s ds in (s, d' :: ds')
  end.

(** Each shared definition uses only the atoms before it. *)
Fixpoint shd_ok (nt na b : N) (l : list aexpN) : bool :=
  match l with
  | [] => true
  | d :: ds => nrng nt na d && nsafe b d && shd_ok nt (N.succ na) b ds
  end.

(** The shown shared definitions [shd] (atoms from [b]) and expression,
    with [nt] terms: materialised, and the new terms. *)
Definition matN (nt b : N) (shd : list aexpN) (root : aexpN) : option (list aexpN * aexpN * list (N * (N * aexpN))) :=
  if shd_ok nt b b shd && nrng nt (b + N.of_nat (List.length shd)) root && nsafe b root then
    let '(s, shd') := amats (nt, []) shd in
    let '(s, root') := amat s root in
    Some (shd', root', snd s)
  else None.

(** ** Environments that agree *)

Definition aval {T} (A : braun (radj T)) (k : N) : radj T := match bnth A k with Some x => x | None => ridentity end.

Lemma den_agree {T} Le (T1 T2 : braun T) (A1 A2 : braun (radj T)) nt na :
  (forall k, (k < nt)%N -> bnth T1 k = bnth T2 k) -> (forall k, (k < na)%N -> bnth A1 k = bnth A2 k) ->
  (forall e, nrng nt na e = true -> aedenB Le T1 A1 e = aedenB Le T2 A2 e)
  /\ (forall t, trng nt na t = true -> tedenB Le T1 A1 t = tedenB Le T2 A2 t).
Proof.
  intros HT HA; apply expN_mind.
  - intros _; reflexivity.
  - intros n H; cbn [nrng trng] in *; try simpl aedenB; try simpl tedenB; apply N.ltb_lt in H; rewrite (HA n H); reflexivity.
  - intros a IHa b IHb H; cbn [nrng trng] in *; try simpl aedenB; try simpl tedenB; apply andb_true_iff in H as [H1 H2]; rewrite (IHa H1), (IHb H2); reflexivity.
  - intros h a IH H; cbn [nrng trng] in *; try simpl aedenB; try simpl tedenB; rewrite (IH H); reflexivity.
  - intros h t IHt a IHa H; cbn [nrng trng] in *; try simpl aedenB; try simpl tedenB; apply andb_true_iff in H as [H1 H2]; rewrite (IHt H1), (IHa H2); reflexivity.
  - intros h a IH H; cbn [nrng trng] in *; try simpl aedenB; try simpl tedenB; rewrite (IH H); reflexivity.
  - intros h i _; reflexivity.
  - intros u p IH H; cbn [nrng trng] in *; try simpl aedenB; try simpl tedenB; apply andb_true_iff in H as [H1 H2]; apply N.ltb_lt in H1.
    rewrite (HT u H1), (IH H2); reflexivity.
  - intros h t IH H; cbn [nrng trng] in *; try simpl aedenB; try simpl tedenB; rewrite (IH H); reflexivity.
  - intros h i a IH H; cbn [nrng trng] in *; try simpl aedenB; try simpl tedenB; rewrite (IH H); reflexivity.
Qed.

Lemma below_rng nt na b :
  (forall e, nbelow b e = true -> nrng nt na e = true -> nrng nt b e = true)
  /\ (forall t, tbelow b t = true -> trng nt na t = true -> trng nt b t = true).
Proof.
  apply expN_mind; intros; cbn [nbelow tbelow nrng trng] in *;
    repeat match goal with H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?] end;
    rewrite ?andb_true_iff; auto.
Qed.

Lemma rng_mono nt na na' : (na <= na')%N ->
  (forall e, nrng nt na e = true -> nrng nt na' e = true)
  /\ (forall t, trng nt na t = true -> trng nt na' t = true).
Proof.
  intros L; apply expN_mind; intros; cbn [nrng trng] in *;
    repeat match goal with H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?] end;
    rewrite ?andb_true_iff; auto.
  apply N.ltb_lt; apply N.ltb_lt in H; lia.
Qed.

(** ** The state only grows *)

Lemma mat_incl :
  (forall e s, incl (snd s) (snd (fst (amat s e))))
  /\ (forall t s, incl (snd s) (snd (fst (tmat s t)))).
Proof.
  apply expN_mind; intros; cbn [amat tmat]; try apply incl_refl.
  - destruct (amat s a) as [s1 x'] eqn:E1; cbn; specialize (H s); rewrite E1 in H; exact H.
  - destruct (tmat s t) as [s1 t'] eqn:E1; destruct (amat s1 a) as [s2 x'] eqn:E2; cbn.
    specialize (H s); specialize (H0 s1); rewrite E1 in H; rewrite E2 in H0; cbn in *; eapply incl_tran; eauto.
  - destruct (is_nid p); [apply incl_refl|].
    destruct (amat s p) as [[k l] p'] eqn:E1; cbn; specialize (H s); rewrite E1 in H; cbn in H.
    apply incl_tl, H.
  - destruct (amat s a) as [s1 a'] eqn:E1; cbn; specialize (H s); rewrite E1 in H; exact H.
Qed.

Lemma mats_incl l : forall s, incl (snd s) (snd (fst (amats s l))).
Proof.
  induction l as [|d ds IH]; intros s; cbn [amats]; [apply incl_refl|].
  destruct (amat s d) as [s1 d'] eqn:E1; destruct (amats s1 ds) as [s2 ds'] eqn:E2; cbn.
  pose proof (proj1 mat_incl d s) as H1; rewrite E1 in H1; specialize (IH s1); rewrite E2 in IH.
  eapply incl_tran; eauto.
Qed.

Lemma bnth_app_lt {A} (l l' : list A) k : (k < N.of_nat (List.length l))%N -> bnth (bof (l ++ l')) k = bnth (bof l) k.
Proof. intros L; rewrite !bnth_bof, nth_error_app1 by lia; reflexivity. Qed.

(** ** The materialisation relates the results *)

Section Rel.

Context {term : nat -> Type}.
Variable tv : forall K, var K -> term K.
Variable sub : forall K M, adj term K M -> term K -> term M.
Local Notation P := {K & term K}.
Local Notation B := (lawbase tv sub).

Variables (Le : braun label) (Te Te' : braun P) (Ae Ae' : braun (radj P)) (nt b na : N).
Local Notation den := (aedenB Le Te Ae).
Local Notation tden := (tedenB Le Te Ae).
Local Notation den' := (aedenB Le Te' Ae').
Local Notation tden' := (tedenB Le Te' Ae').

Hypothesis HT : forall k, (k < nt)%N -> bnth Te' k = bnth Te k.
Hypothesis HA : forall k, (k < b)%N -> bnth Ae' k = bnth Ae k.
Hypothesis HR : forall k, (b <= k)%N -> (k < na)%N -> forall v, drel B (rapply (aval Ae k) v) (rapply (aval Ae' k) v).

(** One new term: its payload materialised is the payload of [c], and it
    is the old term substituted by [c]. *)
Definition mat_fact (x : N * (N * aexpN)) : Prop :=
  let '(k, (u, p)) := x in
  exists K M (c : adj term K M) (u0 : term K), adj_raw c = den' p
    /\ bnth Te u = Some (existT term K u0) /\ bnth Te' k = Some (existT term M (sub K M c u0)).

Variable mf : list (N * (N * aexpN)).
Hypothesis Hmf : forall x, In x mf -> mat_fact x.

Lemma plain_eq e : nbelow b e = true -> nrng nt na e = true -> den e = den' e.
Proof.
  intros H1 H2; symmetry.
  apply (proj1 (den_agree Le Te' Te Ae' Ae nt b HT HA)), (proj1 (below_rng nt na b) e H1 H2).
Qed.

Lemma tplain_eq t : tbelow b t = true -> trng nt na t = true -> tden t = tden' t.
Proof.
  intros H1 H2; symmetry.
  apply (proj2 (den_agree Le Te' Te Ae' Ae nt b HT HA)), (proj2 (below_rng nt na b) t H1 H2).
Qed.

Lemma tres_look_g {X} Le0 (Te0 : braun X) (Ae0 : braun (radj X)) h i a :
  rtarget_result (tedenB Le0 Te0 Ae0 (NLookE h i a)) = rapply (aedenB Le0 Te0 Ae0 a) (mk_rvar (ldenB Le0 h) (N.to_nat i)).
Proof.
  change (tedenB Le0 Te0 Ae0 (NLookE h i a)) with (rapply_target (aedenB Le0 Te0 Ae0 a) (RRename (mk_rvar (ldenB Le0 h) (N.to_nat i)))).
  unfold rapply_target; destruct (rapply _ _) as [w|[u ρ]]; reflexivity.
Qed.

Lemma pay_rel x (W W' : radj P) : (forall v, drel B (rapply W v) (rapply W' v)) -> drel B (inr (x, W)) (inr (x, W')).
Proof.
  intros H; rewrite <- (rcompose_identity_r W), <- (rcompose_identity_r W'); apply DPay, H.
Qed.

Theorem amat_rel :
  (forall e s, nrng nt na e = true -> nsafe b e = true -> incl (snd (fst (amat s e))) mf ->
     forall v, drel B (rapply (den e) v) (rapply (den' (snd (amat s e))) v))
  /\ (forall t s, trng nt na t = true -> tsafe b t = true -> incl (snd (fst (tmat s t))) mf ->
     drel B (rtarget_result (tden t)) (rtarget_result (tden' (snd (tmat s t))))).
Proof.
  apply expN_mind.
  - intros s _ _ _ v; apply DEq.
  - (* an atom: a real one is the same, a shared one related *)
    intros n s Hr _ _ v; cbn [nrng amat snd] in *; simpl aedenB; apply N.ltb_lt in Hr.
    destruct (N.lt_ge_cases n b) as [L|L].
    + unfold aval in HR; rewrite (HA n L); apply DEq.
    + exact (HR n L Hr v).
  - (* [x ⨾ y]: [y] is applied first, the same; [x] after *)
    intros x IHx y _ s Hr Hs Hi v; cbn [nrng nsafe amat] in *.
    apply andb_true_iff in Hr as [Hrx Hry]; apply andb_true_iff in Hs as [Hsx Hsy].
    destruct (amat s x) as [s1 x'] eqn:E1; cbn [snd fst] in *; simpl aedenB.
    rewrite <- (plain_eq y Hsy Hry), <- !rcomp_rapply; apply drel_rcomp_l.
    intros w; specialize (IHx s Hrx Hsx); rewrite E1 in IHx; apply IHx, Hi.
  - intros h x _ s Hr Hs _ v; cbn [nrng nsafe amat snd] in *.
    rewrite (plain_eq (NOuter h x)) by (cbn [nbelow nrng]; assumption); apply DEq.
  - intros h t IHt x IHx s Hr Hs Hi v; cbn [nrng nsafe amat] in *.
    apply andb_true_iff in Hr as [Hrt Hrx]; apply andb_true_iff in Hs as [Hst Hsx].
    destruct (tmat s t) as [s1 t'] eqn:E1; destruct (amat s1 x) as [s2 x'] eqn:E2; cbn [snd fst] in *.
    pose proof (proj1 mat_incl x s1) as I2; rewrite E2 in I2; cbn in I2.
    specialize (IHt s Hrt Hst); rewrite E1 in IHt; specialize (IHx s1 Hrx Hsx); rewrite E2 in IHx.
    simpl aedenB; rewrite !rapply_push_inner; destruct (rvar_eqb v _).
    + apply IHt; eapply incl_tran; eauto.
    + apply IHx, Hi.
  - intros h x _ s Hr Hs _ v; cbn [nrng nsafe amat snd] in *.
    rewrite (plain_eq (NLift h x)) by (cbn [nbelow nrng]; assumption); apply DEq.
  - intros h i s _ _ _; apply DEq.
  - (* a term with its payload *)
    intros u p IH s Hr Hs Hi; cbn [trng tsafe tmat] in *.
    apply andb_true_iff in Hr as [Hu Hrp]; apply N.ltb_lt in Hu.
    destruct (is_nid p) eqn:En.
    + cbn [snd]; destruct p; try discriminate; simpl tedenB; rewrite (HT u Hu); apply DEq.
    + destruct (amat s p) as [[k l] p'] eqn:E1; cbn [snd fst] in *.
      assert (Hin : In (k, (u, p')) mf) by (apply Hi; left; reflexivity).
      destruct (Hmf _ Hin) as [K [M [c [u0 [Ec [Eu Ek]]]]]].
      specialize (IH s Hrp Hs); rewrite E1 in IH; cbn [snd fst] in IH.
      simpl tedenB; rewrite Eu, Ek; cbn [rtarget_result]; simpl aedenB.
      eapply DTrans; [apply pay_rel; intros v; apply IH; intros y Hy; apply Hi; right; exact Hy|].
      apply DBase; left; exists K, M, u0, c; rewrite Ec; split; reflexivity.
  - intros h t _ s Hr Hs _; cbn [trng tsafe tmat snd] in *.
    rewrite (tplain_eq (NShiftE h t)) by (cbn [tbelow trng]; assumption); apply DEq.
  - intros h i a IH s Hr Hs Hi; cbn [trng tsafe tmat] in *.
    destruct (amat s a) as [s1 a'] eqn:E1; cbn [snd fst] in *.
    rewrite !tres_look_g; specialize (IH s Hr Hs); rewrite E1 in IH; apply IH, Hi.
Qed.

End Rel.

Lemma mat_fact_intro {term} (sub : forall K M, adj term K M -> term K -> term M) Le Te Te' Ae'
    K M (c : adj term K M) (u0 : term K) k u p :
  adj_raw c = aedenB Le Te' Ae' p -> bnth Te u = Some (existT term K u0) ->
  bnth Te' k = Some (existT term M (sub K M c u0)) -> mat_fact sub Le Te Te' Ae' (k, (u, p)).
Proof. intros E1 E2 E3; exists K, M, c, u0; split; [exact E1|split; assumption]. Qed.

(** ** The old shared definitions' values *)

Section Olds.

Context {T : Type}.
Variables (Le : braun label) (Te : braun T) (ae : list (radj T)) (nt b : N).

Fixpoint olds (acc : list (radj T)) (l : list aexpN) : list (radj T) :=
  match l with
  | [] => acc
  | d :: ds => olds (acc ++ [aedenB Le Te (bof (ae ++ acc)) d]) ds
  end.

Lemma olds_spec : forall l acc, shd_ok nt (N.of_nat (List.length ae + List.length acc)) b l = true ->
  exists ext, olds acc l = acc ++ ext
    /\ forall junk, Forall2 (fun x d => x = aedenB Le Te (bof (ae ++ acc ++ ext ++ junk)) d) ext l.
Proof.
  induction l as [|d ds IH]; intros acc H; cbn [olds shd_ok] in *.
  - exists []; rewrite app_nil_r; split; [reflexivity|intros; constructor].
  - apply andb_true_iff in H as [H H3]; apply andb_true_iff in H as [H1 _].
    set (x := aedenB Le Te (bof (ae ++ acc)) d).
    destruct (IH (acc ++ [x])) as [ext [E F]].
    { rewrite length_app; cbn [List.length].
      replace (N.of_nat (List.length ae + (List.length acc + 1))) with (N.succ (N.of_nat (List.length ae + List.length acc))) by lia.
      exact H3. }
    exists (x :: ext); split; [rewrite E, <- app_assoc; reflexivity|].
    intros junk; constructor.
    + unfold x; refine (proj1 (den_agree Le Te Te (bof (ae ++ acc)) _ nt (N.of_nat (List.length ae + List.length acc))
                                 (fun _ _ => eq_refl) _) d H1).
      intros k L; rewrite app_assoc, (bnth_app_lt (ae ++ acc)); [reflexivity|rewrite length_app; exact L].
    + specialize (F junk); rewrite <- !app_assoc in F; exact F.
Qed.

End Olds.

(** ** The theorem [names] uses

    Old values for the shown shared definitions exist, and the shown
    expression with them is related to the materialised one with the new
    shared variables, the materialised definitions. *)

Section Core.

Context {term : nat -> Type}.
Variable tv : forall K, var K -> term K.
Variable sub : forall K M, adj term K M -> term K -> term M.
Local Notation P := {K & term K}.
Local Notation B := (lawbase tv sub).

Variables (Le : braun label) (te ms : list P) (ae rs : list (radj P)).
Local Notation Te := (bof te).
Local Notation Te' := (bof (te ++ ms)).
Local Notation Ae' := (bof (ae ++ rs)).

Lemma shares_rel shd mf (Ae : braun (radj P)) :
  (forall x, In x mf -> mat_fact sub Le Te Te' Ae' x) ->
  (forall k, (k < N.of_nat (List.length ae))%N -> bnth Ae' k = bnth Ae k) ->
  forall s i0 olds_l rs_l,
  shd_ok (N.of_nat (List.length te)) (N.of_nat (List.length ae + i0)) (N.of_nat (List.length ae)) shd = true ->
  (forall k, (N.of_nat (List.length ae) <= k)%N -> (k < N.of_nat (List.length ae + i0))%N ->
     forall v, drel B (rapply (aval Ae k) v) (rapply (aval Ae' k) v)) ->
  Forall2 (fun x d => x = aedenB Le Te Ae d) olds_l shd ->
  (forall j x, nth_error olds_l j = Some x -> bnth Ae (N.of_nat (List.length ae + i0 + j)) = Some x) ->
  Forall2 (fun x d => x = aedenB Le Te' Ae' d) rs_l (snd (amats s shd)) ->
  (forall j x, nth_error rs_l j = Some x -> bnth Ae' (N.of_nat (List.length ae + i0 + j)) = Some x) ->
  incl (snd (fst (amats s shd))) mf ->
  forall k, (N.of_nat (List.length ae) <= k)%N -> (k < N.of_nat (List.length ae + i0 + List.length shd))%N ->
  forall v, drel B (rapply (aval Ae k) v) (rapply (aval Ae' k) v).
Proof.
  intros Hmf HA; induction shd as [|d ds IH]; intros s i0 olds_l rs_l Hok HR Ho Hoi Hn Hni Hi k L1 L2.
  { apply HR; [exact L1|cbn [List.length] in L2; lia]. }
  cbn [shd_ok amats] in *.
  apply andb_true_iff in Hok as [Hok H3]; apply andb_true_iff in Hok as [H1 H2].
  destruct (amat s d) as [s1 d'] eqn:E1; destruct (amats s1 ds) as [s2 ds'] eqn:E2; cbn [snd fst] in *.
  inversion Ho as [|xo d0 ol ds0 Exo Ho' Eo]; subst olds_l.
  inversion Hn as [|xn d1 nl ds1 Exn Hn' En]; subst rs_l.
  pose proof (mats_incl ds s1) as I2; rewrite E2 in I2; cbn in I2.
  (* the first definition: related as the materialisation of [d] *)
  assert (Hd : forall v, drel B (rapply (aval Ae (N.of_nat (List.length ae + i0))) v)
                                (rapply (aval Ae' (N.of_nat (List.length ae + i0))) v)).
  { intros w; unfold aval.
    pose proof (Hoi 0 xo eq_refl) as E3; pose proof (Hni 0 xn eq_refl) as E4; rewrite Nat.add_0_r in E3, E4.
    rewrite E3, E4, Exo, Exn.
    pose proof (proj1 (amat_rel tv sub Le Te Te' Ae Ae' (N.of_nat (List.length te)) (N.of_nat (List.length ae))
                         (N.of_nat (List.length ae + i0))
                         (fun k L => bnth_app_lt te ms k L) HA HR mf Hmf) d s H1 H2) as R.
    rewrite E1 in R; apply R; intros y Hy; apply Hi, I2, Hy. }
  destruct (N.eq_dec k (N.of_nat (List.length ae + i0))) as [->|Nk]; [apply Hd|].
  apply (IH s1 (S i0) ol nl).
  - replace (N.of_nat (List.length ae + S i0)) with (N.succ (N.of_nat (List.length ae + i0))) by lia; exact H3.
  - intros k' L1' L2' v; destruct (N.eq_dec k' (N.of_nat (List.length ae + i0))) as [->|Nk']; [apply Hd|].
    apply HR; lia.
  - exact Ho'.
  - intros j x E; replace (List.length ae + S i0 + j) with (List.length ae + i0 + S j) by lia; apply Hoi, E.
  - rewrite E2; exact Hn'.
  - intros j x E; replace (List.length ae + S i0 + j) with (List.length ae + i0 + S j) by lia; apply Hni, E.
  - rewrite E2; exact Hi.
  - exact L1.
  - cbn [List.length] in L2; lia.
Qed.

(** The theorem: [rN] with the old values against the materialised
    [rN'] with the new shared variables [rs]. *)
Theorem mat_core nt shd root shd' root' mf :
  nt = N.of_nat (List.length te) ->
  matN nt (N.of_nat (List.length ae)) shd root = Some (shd', root', mf) ->
  Forall2 (fun x d => x = aedenB Le Te' Ae' d) rs shd' ->
  Forall (mat_fact sub Le Te Te' Ae') mf ->
  exists olds_l, Forall2 (fun x d => x = aedenB Le Te (bof (ae ++ olds_l)) d) olds_l shd
    /\ forall v, drel B (rapply (aedenB Le Te (bof (ae ++ olds_l)) root) v) (rapply (aedenB Le Te' Ae' root') v).
Proof.
  intros -> E Hs Hmf; rewrite Forall_forall in Hmf; unfold matN in E.
  destruct (shd_ok _ _ _ shd) eqn:Hok; [|discriminate].
  destruct (nrng _ _ root) eqn:Hr; [|discriminate]; destruct (nsafe _ root) eqn:Hsf; [|discriminate]; cbn [andb] in E.
  destruct (amats (N.of_nat (List.length te), []) shd) as [s1 shd1] eqn:E1.
  destruct (amat s1 root) as [s2 root2] eqn:E2; injection E as <- <- <-.
  destruct (olds_spec Le Te ae (N.of_nat (List.length te)) (N.of_nat (List.length ae)) shd []) as [ext [Eo Fo]].
  { rewrite Nat.add_0_r; exact Hok. }
  specialize (Fo []); rewrite app_nil_r in Fo; cbn [app] in Fo.
  exists ext; split; [exact Fo|].
  pose proof (Forall2_length Fo) as Lo; pose proof (Forall2_length Hs) as Ln.
  assert (Ls : List.length shd1 = List.length shd).
  { clear -E1; revert E1; generalize (N.of_nat (List.length te), @nil (N * (N * aexpN))) as s0.
    revert shd1 s1; induction shd as [|d ds IH]; intros shd1 s1 s0 E; cbn [amats] in E.
    - injection E as _ <-; reflexivity.
    - destruct (amat s0 d) as [t1 d'] eqn:F1; destruct (amats t1 ds) as [t2 ds'] eqn:F2; injection E as _ <-.
      cbn [List.length]; f_equal; apply (IH _ _ _ F2). }
  pose proof (proj1 mat_incl root s1) as I2; rewrite E2 in I2; cbn in I2.
  pose proof (mats_incl shd (N.of_nat (List.length te), [])) as I1; rewrite E1 in I1; cbn in I1.
  assert (HA : forall k, (k < N.of_nat (List.length ae))%N -> bnth Ae' k = bnth (bof (ae ++ ext)) k).
  { intros k L; rewrite !bnth_app_lt by exact L; reflexivity. }
  assert (HR : forall k, (N.of_nat (List.length ae) <= k)%N -> (k < N.of_nat (List.length ae + List.length shd))%N ->
                 forall v, drel B (rapply (aval (bof (ae ++ ext)) k) v) (rapply (aval Ae' k) v)).
  { intros k0 M1 M2 v.
    refine (shares_rel shd (snd s2) (bof (ae ++ ext)) Hmf HA (N.of_nat (List.length te), []) 0 ext rs _ _ _ _ _ _ _ k0 M1 _ v);
      [| | | | | | |rewrite Nat.add_0_r; exact M2].
    - rewrite Nat.add_0_r; exact Hok.
    - intros k L1 L2; lia.
    - exact Fo.
    - intros j x E; rewrite bnth_bof, Nat2N.id, Nat.add_0_r, nth_error_app2 by lia.
      replace (List.length ae + j - List.length ae) with j by lia; exact E.
    - rewrite E1; exact Hs.
    - intros j x E; rewrite bnth_bof, Nat2N.id, Nat.add_0_r, nth_error_app2 by lia.
      replace (List.length ae + j - List.length ae) with j by lia; exact E.
    - rewrite E1; exact I2. }
  pose proof (proj1 (amat_rel tv sub Le Te Te' (bof (ae ++ ext)) Ae' (N.of_nat (List.length te)) (N.of_nat (List.length ae))
                       (N.of_nat (List.length ae + List.length shd))
                       (fun k L => bnth_app_lt te ms k L) HA HR (snd s2) Hmf) root s1) as R.
  rewrite E2 in R; apply R.
  - replace (N.of_nat (List.length ae + List.length shd)) with (N.of_nat (List.length ae) + N.of_nat (List.length shd))%N by lia.
    exact Hr.
  - exact Hsf.
  - apply incl_refl.
Qed.

End Core.

(** ** The checks [names] makes

    The display's checks with the shown expression materialised: the
    converted adjustment [ce] (with the input's atoms, [bof ae]) against
    the materialised rendering (with the new terms [ms] and the new
    shared variables [rs]). *)

Lemma nrng_adec n b :
  (forall e, CRange.inrange n b (adec e) = true -> nrng (N.of_nat n) (N.of_nat b) e = true)
  /\ (forall t, CRange.tinrange n b (tdec t) = true -> trng (N.of_nat n) (N.of_nat b) t = true).
Proof.
  apply expN_mind; intros; cbn [adec tdec CRange.inrange CRange.tinrange nrng trng] in *;
    repeat match goal with H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?] end;
    rewrite ?andb_true_iff; auto.
  - apply N.ltb_lt; apply Nat.ltb_lt in H; lia.
  - split; [apply N.ltb_lt; apply Nat.ltb_lt in H0; lia|auto].
Qed.

Lemma Forall2_impl_nth {A C} (R R' : A -> C -> Prop) xs ys :
  (forall k x y, nth_error xs k = Some x -> nth_error ys k = Some y -> R x y -> R' x y) ->
  Forall2 R xs ys -> Forall2 R' xs ys.
Proof.
  intros H F; revert H; induction F as [|x y xs ys Hxy F IH]; intros H; constructor.
  - apply (H 0); [reflexivity|reflexivity|exact Hxy].
  - apply IH; intros k; apply (H (S k)).
Qed.

Section Checks.

Context {term : nat -> Type}.
Variable tv : forall K, var K -> term K.
Variable sub : forall K M, adj term K M -> term K -> term M.
Local Notation P := {K & term K}.
Local Notation B := (lawbase tv sub).

Variables (le : list label) (te ms : list P) (ae rs : list (radj P)).
Variables (Le : braun label) (Te Te' : braun P) (Ae0 Ae' : braun (radj P)).
Hypotheses (HLe : Le = bof le) (HTe : Te = bof te) (HTe' : Te' = bof (te ++ ms)) (HAe0 : Ae0 = bof ae)
  (HAe' : Ae' = bof (ae ++ rs)).

(** The converted adjustment, in range, means the same with any shared
    variables after the input's atoms. *)
Lemma ce_old Te0 (olds : list (radj P)) ce :
  CRange.inrange (List.length te) (List.length ae) (adec ce) = true ->
  aedenB Le Te0 (bof ae) ce = aedenB Le Te0 (bof (ae ++ olds)) ce.
Proof.
  intros H; apply (proj1 (den_agree Le Te0 Te0 (bof ae) (bof (ae ++ olds)) (N.of_nat (List.length te)) (N.of_nat (List.length ae))
                           (fun _ _ => eq_refl) (fun k L => eq_sym (bnth_app_lt ae olds k L)))).
  apply (proj1 (nrng_adec _ _)), H.
Qed.

Theorem mat_show l defs ce shN rN shN' rN' mf :
  lfacts_okB Le l ->
  hshowDN (order_of l) (List.length te) (List.length ae) defs ce = Some (shN, rN) ->
  matN (N.of_nat (List.length te)) (N.of_nat (List.length ae)) shN rN = Some (shN', rN', mf) ->
  Forall2 (fun x od => match od with Some d => x = aedenB Le Te Ae0 d | None => True end) ae defs ->
  Forall2 (fun x d => x = aedenB Le Te' Ae' d) rs shN' ->
  Forall (mat_fact sub Le Te Te' Ae') mf ->
  forall v, drel B (rapply (aedenB Le Te Ae0 ce) v) (rapply (aedenB Le Te' Ae' rN') v).
Proof.
  intros Hl Ht Hm Hd Hs Hf; subst Te Te' Ae0 Ae'.
  destruct (mat_core tv sub Le te ms ae rs _ shN rN shN' rN' mf eq_refl Hm Hs Hf) as [olds [Ho Hrel]].
  (* the ranges the display checks *)
  pose proof Ht as Ht0; unfold hshowDN in Ht0.
  destruct (HShow.hshowD _ _ _ _ _) as [[sh0 r0]|] eqn:E0; [|discriminate]; clear Ht0.
  unfold HShow.hshowD in E0.
  destruct (inp _ _ (adec ce)) eqn:Ie; [|discriminate].
  destruct (Nat.eqb _ _) eqn:Ln; [|discriminate].
  destruct (defs_ok _ 0 _) eqn:Dk; [|discriminate].
  unfold inp in Ie; apply andb_true_iff in Ie as [_ Ir].
  apply Nat.eqb_eq in Ln; rewrite length_map in Ln.
  (* the input's definitions, with the old shared variables after *)
  assert (Hd' : Forall2 (fun x od => match od with Some d => x = aedenB Le (bof te) (bof (ae ++ olds)) d | None => True end) ae defs).
  { revert Hd; apply Forall2_impl_nth; intros k x od Ex Eod; destruct od as [d|]; [|trivial].
    intros ->.
    assert (Lk : k < List.length ae) by (apply nth_error_Some; rewrite Ex; discriminate).
    pose proof (defs_ok_nth _ _ 0 k (adec d) Dk) as K.
    rewrite (nth_error_nth _ _ _ (map_nth_error (option_map adec) _ _ Eod)) in K; cbn [option_map] in K.
    specialize (K eq_refl); unfold inp in K; apply andb_true_iff in K as [_ K].
    apply (proj1 (den_agree Le (bof te) (bof te) (bof ae) (bof (ae ++ olds)) (N.of_nat (List.length te))
                   (N.of_nat (List.length ae)) (fun _ _ => eq_refl) (fun k L => eq_sym (bnth_app_lt ae olds k L)))).
    apply (proj1 (rng_mono (N.of_nat (List.length te)) (N.of_nat (0 + k)) (N.of_nat (List.length ae)) ltac:(lia))), (proj1 (nrng_adec _ _)), K. }
  pose proof (hshowDB_sound le te ae olds Le (bof te) (bof (ae ++ olds)) HLe eq_refl eq_refl l defs ce shN rN Hl Ht Hd' Ho) as E.
  intros v; rewrite (ce_old (bof te) olds ce Ir), E; apply Hrel.
Qed.

(** A variable [h_i] followed to a term [x] with a shown payload. *)
Theorem mat_term l ce h i u shN rN x shN' rN' mf :
  lfacts_okB Le l ->
  hlook_showN (order_of l) (List.length te) (List.length ae) ce h i = Some (VSTermN u (shN, rN)) ->
  bnth Te u = Some x ->
  matN (N.of_nat (List.length te)) (N.of_nat (List.length ae)) shN rN = Some (shN', rN', mf) ->
  Forall2 (fun y d => y = aedenB Le Te' Ae' d) rs shN' ->
  Forall (mat_fact sub Le Te Te' Ae') mf ->
  drel B (rapply (aedenB Le Te Ae0 ce) (mk_rvar (ldenB Le h) i)) (inr (x, aedenB Le Te' Ae' rN')).
Proof.
  intros Hl Ht Hx Hm Hs Hf; subst Te Te' Ae0 Ae'.
  destruct (mat_core tv sub Le te ms ae rs _ shN rN shN' rN' mf eq_refl Hm Hs Hf) as [olds [Ho Hrel]].
  pose proof Ht as Ht0; unfold hlook_showN, hlook_show in Ht0.
  destruct (inp _ _ (adec ce)) eqn:Ie; [|discriminate]; clear Ht0.
  unfold inp in Ie; apply andb_true_iff in Ie as [_ Ir].
  rewrite (ce_old (bof te) olds ce Ir).
  rewrite (hlookB_term le te ae olds Le (bof te) (bof (ae ++ olds)) HLe eq_refl eq_refl l ce h i u shN rN x Hl Ht Ho Hx).
  apply pay_rel, Hrel.
Qed.

(** A variable [h_i] stuck at [g_j] looked up through a shown rest. *)
Theorem mat_look l ce h i g j shN rN shN' rN' mf :
  lfacts_okB Le l ->
  hlook_showN (order_of l) (List.length te) (List.length ae) ce h i = Some (VSLookN g j (shN, rN)) ->
  matN (N.of_nat (List.length te)) (N.of_nat (List.length ae)) shN rN = Some (shN', rN', mf) ->
  Forall2 (fun y d => y = aedenB Le Te' Ae' d) rs shN' ->
  Forall (mat_fact sub Le Te Te' Ae') mf ->
  drel B (rapply (aedenB Le Te Ae0 ce) (mk_rvar (ldenB Le h) i))
         (rapply (aedenB Le Te' Ae' rN') (mk_rvar (ldenB Le g) (N.to_nat j))).
Proof.
  intros Hl Ht Hm Hs Hf; subst Te Te' Ae0 Ae'.
  destruct (mat_core tv sub Le te ms ae rs _ shN rN shN' rN' mf eq_refl Hm Hs Hf) as [olds [Ho Hrel]].
  pose proof Ht as Ht0; unfold hlook_showN, hlook_show in Ht0.
  destruct (inp _ _ (adec ce)) eqn:Ie; [|discriminate]; clear Ht0.
  unfold inp in Ie; apply andb_true_iff in Ie as [_ Ir].
  rewrite (ce_old (bof te) olds ce Ir).
  rewrite (hlookB_look le te ae olds Le (bof te) (bof (ae ++ olds)) HLe eq_refl eq_refl l ce h i g j shN rN Hl Ht Ho).
  apply Hrel.
Qed.

End Checks.
