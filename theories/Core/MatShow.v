(** * Materialising what the display shows

    The display shows a term with its payload, [x := u⟨| p ⟩], only where
    nothing is applied after it: on an entry over the rest of the word, in
    a payload, in a look-up's payload, and on the side of [⨾] applied
    last.  There, the term with its payload can become the term
    substituted by its payload, [x := u [p]], with the identity payload:
    per variable, this is the law's base [matbase].

    Two parts:
    - The rendered expression as data ([madj], a mirror of the context
      forms), with two meanings: as shown ([mden]) and materialised
      ([mmat]).  One theorem relates them ([mat_rel]); [names] applies it
      once to each shared definition and to the root, and the kernel
      checks it by computing the two meanings.
    - The display's check, with the shared variables standing for the
      materialised definitions, related to the shown ones rather than
      equal to them ([show_rel]): its proof builds the shown definitions'
      values ([olds]), so they never appear in a proof [names] makes.
      [safeN] checks what this needs: indices in range, each definition
      using only the ones before it, and no shared variable where
      something is applied after it. *)

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

(** Each shared definition uses only the atoms before it. *)
Fixpoint shd_ok (nt na b : N) (l : list aexpN) : bool :=
  match l with
  | [] => true
  | d :: ds => nrng nt na d && nsafe b d && shd_ok nt (N.succ na) b ds
  end.

(** The check for the shown shared definitions [shd] (atoms from [b]) and root. *)
Definition safeN (nt b : N) (shd : list aexpN) (root : aexpN) : bool :=
  shd_ok nt b b shd && nrng nt (b + N.of_nat (List.length shd)) root && nsafe b root.

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

Lemma bnth_app_lt {A} (l l' : list A) k : (k < N.of_nat (List.length l))%N -> bnth (bof (l ++ l')) k = bnth (bof l) k.
Proof. intros L; rewrite !bnth_bof, nth_error_app1 by lia; reflexivity. Qed.

Lemma tres_look_g {X} Le0 (Te0 : braun X) (Ae0 : braun (radj X)) h i a :
  rtarget_result (tedenB Le0 Te0 Ae0 (NLookE h i a)) = rapply (aedenB Le0 Te0 Ae0 a) (mk_rvar (ldenB Le0 h) (N.to_nat i)).
Proof.
  change (tedenB Le0 Te0 Ae0 (NLookE h i a)) with (rapply_target (aedenB Le0 Te0 Ae0 a) (RRename (mk_rvar (ldenB Le0 h) (N.to_nat i)))).
  unfold rapply_target; destruct (rapply _ _) as [w|[u ρ]]; reflexivity.
Qed.

Lemma pay_rel {X} (B : rresult X -> rresult X -> Prop) x (W W' : radj X) :
  (forall v, drel B (rapply W v) (rapply W' v)) -> drel B (inr (x, W)) (inr (x, W')).
Proof.
  intros H; rewrite <- (rcompose_identity_r W), <- (rcompose_identity_r W'); apply DPay, H.
Qed.

(** ** Related shared variables give related meanings

    With the atoms from [b] on related (and the ones before the same),
    an expression with them only where nothing is applied after them
    means related things. *)

Section Cong.

Context {term : nat -> Type}.
Variable tv : forall K, var K -> term K.
Variable sub : forall K M, adj term K M -> term K -> term M.
Local Notation P := {K & term K}.
Local Notation B := (lawbase tv sub).

Variables (Le : braun label) (Te : braun P) (Ae Ae' : braun (radj P)) (nt b na : N).
Local Notation den := (aedenB Le Te Ae).
Local Notation tden := (tedenB Le Te Ae).
Local Notation den' := (aedenB Le Te Ae').
Local Notation tden' := (tedenB Le Te Ae').

Hypothesis HA : forall k, (k < b)%N -> bnth Ae' k = bnth Ae k.
Hypothesis HR : forall k, (b <= k)%N -> (k < na)%N -> forall v, drel B (rapply (aval Ae k) v) (rapply (aval Ae' k) v).

Lemma plain_eq e : nbelow b e = true -> nrng nt na e = true -> den e = den' e.
Proof.
  intros H1 H2; symmetry.
  apply (proj1 (den_agree Le Te Te Ae' Ae nt b (fun _ _ => eq_refl) HA)), (proj1 (below_rng nt na b) e H1 H2).
Qed.

Lemma tplain_eq t : tbelow b t = true -> trng nt na t = true -> tden t = tden' t.
Proof.
  intros H1 H2; symmetry.
  apply (proj2 (den_agree Le Te Te Ae' Ae nt b (fun _ _ => eq_refl) HA)), (proj2 (below_rng nt na b) t H1 H2).
Qed.

Theorem cong_rel :
  (forall e, nrng nt na e = true -> nsafe b e = true -> forall v, drel B (rapply (den e) v) (rapply (den' e) v))
  /\ (forall t, trng nt na t = true -> tsafe b t = true -> drel B (rtarget_result (tden t)) (rtarget_result (tden' t))).
Proof.
  apply expN_mind.
  - intros _ _ v; apply DEq.
  - intros n Hr _ v; cbn [nrng] in Hr; simpl aedenB; apply N.ltb_lt in Hr.
    destruct (N.lt_ge_cases n b) as [L|L].
    + rewrite (HA n L); apply DEq.
    + exact (HR n L Hr v).
  - (* [x ⨾ y]: [y] is applied first, the same; [x] after *)
    intros x IHx y _ Hr Hs v; cbn [nrng nsafe] in *.
    apply andb_true_iff in Hr as [Hrx Hry]; apply andb_true_iff in Hs as [Hsx Hsy].
    simpl aedenB; rewrite <- (plain_eq y Hsy Hry), <- !rcomp_rapply; apply drel_rcomp_l.
    intros w; apply IHx; assumption.
  - intros h x _ Hr Hs v; cbn [nrng nsafe] in *.
    rewrite (plain_eq (NOuter h x)) by (cbn [nbelow nrng]; assumption); apply DEq.
  - intros h t IHt x IHx Hr Hs v; cbn [nrng nsafe] in *.
    apply andb_true_iff in Hr as [Hrt Hrx]; apply andb_true_iff in Hs as [Hst Hsx].
    simpl aedenB; rewrite !rapply_push_inner; destruct (rvar_eqb v _); [apply IHt|apply IHx]; assumption.
  - intros h x _ Hr Hs v; cbn [nrng nsafe] in *.
    rewrite (plain_eq (NLift h x)) by (cbn [nbelow nrng]; assumption); apply DEq.
  - intros h i _ _; apply DEq.
  - intros u p IH Hr Hs; cbn [trng tsafe] in *.
    apply andb_true_iff in Hr as [_ Hrp].
    simpl tedenB; destruct (bnth Te u) as [x|]; cbn [rtarget_result]; [|apply DEq].
    apply pay_rel; intros v; apply IH; assumption.
  - intros h t _ Hr Hs; cbn [trng tsafe] in *.
    rewrite (tplain_eq (NShiftE h t)) by (cbn [tbelow trng]; assumption); apply DEq.
  - intros h i a IH Hr Hs; cbn [trng tsafe] in *.
    rewrite !tres_look_g; apply IH; assumption.
Qed.

End Cong.

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

(** ** The shown expression with related shared variables *)

Section Core.

Context {term : nat -> Type}.
Variable tv : forall K, var K -> term K.
Variable sub : forall K M, adj term K M -> term K -> term M.
Local Notation P := {K & term K}.
Local Notation B := (lawbase tv sub).

Variables (Le : braun label) (te : list P) (ae rs : list (radj P)).
Local Notation Te := (bof te).
Local Notation Ae' := (bof (ae ++ rs)).

Lemma shares_rel shd (Ae : braun (radj P)) :
  (forall k, (k < N.of_nat (List.length ae))%N -> bnth Ae' k = bnth Ae k) ->
  forall i0 olds_l rs_l,
  shd_ok (N.of_nat (List.length te)) (N.of_nat (List.length ae + i0)) (N.of_nat (List.length ae)) shd = true ->
  (forall k, (N.of_nat (List.length ae) <= k)%N -> (k < N.of_nat (List.length ae + i0))%N ->
     forall v, drel B (rapply (aval Ae k) v) (rapply (aval Ae' k) v)) ->
  Forall2 (fun x d => x = aedenB Le Te Ae d) olds_l shd ->
  (forall j x, nth_error olds_l j = Some x -> bnth Ae (N.of_nat (List.length ae + i0 + j)) = Some x) ->
  Forall2 (fun z d => forall v, drel B (rapply (aedenB Le Te Ae' d) v) (rapply z v)) rs_l shd ->
  (forall j x, nth_error rs_l j = Some x -> bnth Ae' (N.of_nat (List.length ae + i0 + j)) = Some x) ->
  forall k, (N.of_nat (List.length ae) <= k)%N -> (k < N.of_nat (List.length ae + i0 + List.length shd))%N ->
  forall v, drel B (rapply (aval Ae k) v) (rapply (aval Ae' k) v).
Proof.
  intros HA; induction shd as [|d ds IH]; intros i0 olds_l rs_l Hok HR Ho Hoi Hn Hni k L1 L2.
  { apply HR; [exact L1|cbn [List.length] in L2; lia]. }
  cbn [shd_ok] in Hok.
  apply andb_true_iff in Hok as [Hok H3]; apply andb_true_iff in Hok as [H1 H2].
  inversion Ho as [|xo d0 ol ds0 Exo Ho' Eo]; subst olds_l.
  inversion Hn as [|xn d1 nl ds1 Exn Hn' En]; subst rs_l.
  (* the first definition: the old value against the new, through the
     definition with the new variables *)
  assert (Hd : forall v, drel B (rapply (aval Ae (N.of_nat (List.length ae + i0))) v)
                                (rapply (aval Ae' (N.of_nat (List.length ae + i0))) v)).
  { intros w; unfold aval.
    pose proof (Hoi 0 xo eq_refl) as E3; pose proof (Hni 0 xn eq_refl) as E4; rewrite Nat.add_0_r in E3, E4.
    rewrite E3, E4, Exo.
    eapply DTrans; [|apply Exn].
    exact (proj1 (cong_rel tv sub Le Te Ae Ae' (N.of_nat (List.length te)) (N.of_nat (List.length ae))
                    (N.of_nat (List.length ae + i0)) HA HR) d H1 H2 w). }
  destruct (N.eq_dec k (N.of_nat (List.length ae + i0))) as [->|Nk]; [apply Hd|].
  apply (IH (S i0) ol nl).
  - replace (N.of_nat (List.length ae + S i0)) with (N.succ (N.of_nat (List.length ae + i0))) by lia; exact H3.
  - intros k' L1' L2' v; destruct (N.eq_dec k' (N.of_nat (List.length ae + i0))) as [->|Nk']; [apply Hd|].
    apply HR; lia.
  - exact Ho'.
  - intros j x E; replace (List.length ae + S i0 + j) with (List.length ae + i0 + S j) by lia; apply Hoi, E.
  - exact Hn'.
  - intros j x E; replace (List.length ae + S i0 + j) with (List.length ae + i0 + S j) by lia; apply Hni, E.
  - exact L1.
  - cbn [List.length] in L2; lia.
Qed.

(** Old values for the shown definitions exist, and the shown root with
    them is related to the shown root with the new variables. *)
Theorem rel_core nt shd root :
  nt = N.of_nat (List.length te) ->
  safeN nt (N.of_nat (List.length ae)) shd root = true ->
  Forall2 (fun z d => forall v, drel B (rapply (aedenB Le Te Ae' d) v) (rapply z v)) rs shd ->
  exists olds_l, Forall2 (fun x d => x = aedenB Le Te (bof (ae ++ olds_l)) d) olds_l shd
    /\ forall v, drel B (rapply (aedenB Le Te (bof (ae ++ olds_l)) root) v) (rapply (aedenB Le Te Ae' root) v).
Proof.
  intros -> E Hs; unfold safeN in E.
  apply andb_true_iff in E as [E Hsf]; apply andb_true_iff in E as [Hok Hr].
  destruct (olds_spec Le Te ae (N.of_nat (List.length te)) (N.of_nat (List.length ae)) shd []) as [ext [_ Fo]].
  { rewrite Nat.add_0_r; exact Hok. }
  specialize (Fo []); rewrite app_nil_r in Fo; cbn [app] in Fo.
  exists ext; split; [exact Fo|].
  pose proof (Forall2_length Fo) as Lo; pose proof (Forall2_length Hs) as Ln.
  assert (HA : forall k, (k < N.of_nat (List.length ae))%N -> bnth Ae' k = bnth (bof (ae ++ ext)) k).
  { intros k L; rewrite !bnth_app_lt by exact L; reflexivity. }
  assert (HR : forall k, (N.of_nat (List.length ae) <= k)%N -> (k < N.of_nat (List.length ae + List.length shd))%N ->
                 forall v, drel B (rapply (aval (bof (ae ++ ext)) k) v) (rapply (aval Ae' k) v)).
  { intros k0 M1 M2 v.
    refine (shares_rel shd (bof (ae ++ ext)) HA 0 ext rs _ _ _ _ _ _ k0 M1 _ v);
      [| | | | | |rewrite Nat.add_0_r; exact M2].
    - rewrite Nat.add_0_r; exact Hok.
    - intros k L1 L2; lia.
    - exact Fo.
    - intros j x E; rewrite bnth_bof, Nat2N.id, Nat.add_0_r, nth_error_app2 by lia.
      replace (List.length ae + j - List.length ae) with j by lia; exact E.
    - exact Hs.
    - intros j x E; rewrite bnth_bof, Nat2N.id, Nat.add_0_r, nth_error_app2 by lia.
      replace (List.length ae + j - List.length ae) with j by lia; exact E. }
  apply (proj1 (cong_rel tv sub Le Te (bof (ae ++ ext)) Ae' (N.of_nat (List.length te)) (N.of_nat (List.length ae))
                  (N.of_nat (List.length ae + List.length shd)) HA HR) root).
  - replace (N.of_nat (List.length ae + List.length shd)) with (N.of_nat (List.length ae) + N.of_nat (List.length shd))%N by lia.
    exact Hr.
  - exact Hsf.
Qed.

End Core.

(** ** The checks [names] makes

    The display's checks, the shared variables [rs] related to the shown
    definitions: the converted adjustment [ce] (with the input's atoms)
    against the shown root (with [rs]). *)

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

Variables (le : list label) (te : list P) (ae rs : list (radj P)).
Variables (Le : braun label) (Te : braun P) (Ae0 Ae' : braun (radj P)).
Hypotheses (HLe : Le = bof le) (HTe : Te = bof te) (HAe0 : Ae0 = bof ae) (HAe' : Ae' = bof (ae ++ rs)).

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

Theorem show_rel l defs ce shN rN :
  lfacts_okB Le l ->
  hshowDN (order_of l) (List.length te) (List.length ae) defs ce = Some (shN, rN) ->
  safeN (N.of_nat (List.length te)) (N.of_nat (List.length ae)) shN rN = true ->
  Forall2 (fun x od => match od with Some d => x = aedenB Le Te Ae0 d | None => True end) ae defs ->
  Forall2 (fun z d => forall v, drel B (rapply (aedenB Le Te Ae' d) v) (rapply z v)) rs shN ->
  forall v, drel B (rapply (aedenB Le Te Ae0 ce) v) (rapply (aedenB Le Te Ae' rN) v).
Proof.
  intros Hl Ht Hm Hd Hs; subst Te Ae0 Ae'.
  destruct (rel_core tv sub Le te ae rs _ shN rN eq_refl Hm Hs) as [olds [Ho Hrel]].
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
Theorem term_rel l ce h i u shN rN x :
  lfacts_okB Le l ->
  hlook_showN (order_of l) (List.length te) (List.length ae) ce h i = Some (VSTermN u (shN, rN)) ->
  bnth Te u = Some x ->
  safeN (N.of_nat (List.length te)) (N.of_nat (List.length ae)) shN rN = true ->
  Forall2 (fun z d => forall v, drel B (rapply (aedenB Le Te Ae' d) v) (rapply z v)) rs shN ->
  drel B (rapply (aedenB Le Te Ae0 ce) (mk_rvar (ldenB Le h) i)) (inr (x, aedenB Le Te Ae' rN)).
Proof.
  intros Hl Ht Hx Hm Hs; subst Te Ae0 Ae'.
  destruct (rel_core tv sub Le te ae rs _ shN rN eq_refl Hm Hs) as [olds [Ho Hrel]].
  pose proof Ht as Ht0; unfold hlook_showN, hlook_show in Ht0.
  destruct (inp _ _ (adec ce)) eqn:Ie; [|discriminate]; clear Ht0.
  unfold inp in Ie; apply andb_true_iff in Ie as [_ Ir].
  rewrite (ce_old (bof te) olds ce Ir).
  rewrite (hlookB_term le te ae olds Le (bof te) (bof (ae ++ olds)) HLe eq_refl eq_refl l ce h i u shN rN x Hl Ht Ho Hx).
  apply pay_rel, Hrel.
Qed.

(** A variable [h_i] stuck at [g_j] looked up through a shown rest. *)
Theorem look_rel l ce h i g j shN rN :
  lfacts_okB Le l ->
  hlook_showN (order_of l) (List.length te) (List.length ae) ce h i = Some (VSLookN g j (shN, rN)) ->
  safeN (N.of_nat (List.length te)) (N.of_nat (List.length ae)) shN rN = true ->
  Forall2 (fun z d => forall v, drel B (rapply (aedenB Le Te Ae' d) v) (rapply z v)) rs shN ->
  drel B (rapply (aedenB Le Te Ae0 ce) (mk_rvar (ldenB Le h) i))
         (rapply (aedenB Le Te Ae' rN) (mk_rvar (ldenB Le g) (N.to_nat j))).
Proof.
  intros Hl Ht Hm Hs; subst Te Ae0 Ae'.
  destruct (rel_core tv sub Le te ae rs _ shN rN eq_refl Hm Hs) as [olds [Ho Hrel]].
  pose proof Ht as Ht0; unfold hlook_showN, hlook_show in Ht0.
  destruct (inp _ _ (adec ce)) eqn:Ie; [|discriminate]; clear Ht0.
  unfold inp in Ie; apply andb_true_iff in Ie as [_ Ir].
  rewrite (ce_old (bof te) olds ce Ir).
  rewrite (hlookB_look le te ae olds Le (bof te) (bof (ae ++ olds)) HLe eq_refl eq_refl l ce h i g j shN rN Hl Ht Ho).
  apply Hrel.
Qed.

End Checks.

(** ** The rendering as data

    [madj]/[msctx] mirror the context forms the display renders to,
    argument for argument; [MAtom] is anything left as it is (an atom, a
    shared variable).  [mden] gives the adjustment as shown, [mmat] the
    same with each payload entry materialised, except where something is
    applied after it: the side of [⨾] applied first, the tail of a context
    form with outputs, and a short form with a lift. *)

Section Mirror.

Context {term : nat -> Type}.

Inductive madj : nat -> nat -> Type :=
| MAtom {N M} (a : adj term N M) : madj N M
| MCompose {N M K} (a : madj M K) (b : madj N M) : madj N K
| MShort {Nt N M} (s : msctx Nt Nt N M) : madj N M
| MShortT {N M Nb Mb} (s : msctx Nb Mb N M) (σ : madj Nb Mb) : madj N M
| MCform {K Nt Mt N M P} (o : forall g : tname, @octx term K Nt N M P P Mt K (Some g)) (σ : madj Nt Mt) : madj N M
with msctx : nat -> nat -> nat -> nat -> Type :=
| MSEmpty {N M} : msctx N M N M
| MSLiftF {Nb Mb N M} (s : msctx Nb Mb N M) (x : label) : msctx Nb Mb N M
| MSLiftB {Nb Mb N M} (s : msctx (S Nb) (S Mb) N M) : msctx Nb Mb N M
| MSSubF {Nb Mb N M} (s : msctx Nb Mb N M) (x : label) (u : term Mb) : msctx Nb Mb N M
| MSSubB {Nb Mb N M} (s : msctx (S Nb) Mb N M) (u : term Mb) : msctx Nb Mb N M
| MSRenF {Nb Mb N M} (s : msctx Nb Mb N M) (x : label) (w : var Mb) : msctx Nb Mb N M
| MSRenB {Nb Mb N M} (s : msctx (S Nb) Mb N M) (w : var Mb) : msctx Nb Mb N M
| MSSubFA {Nb Mb N M} (s : msctx Nb Mb N M) (x : label) {K} (u : term K) (r : madj K Mb) : msctx Nb Mb N M
| MSSubBA {Nb Mb N M} (s : msctx (S Nb) Mb N M) {K} (u : term K) (r : madj K Mb) : msctx Nb Mb N M
| MSLookF {Nb Mb N M K} (s : msctx Nb Mb N M) (x : label) (w : var K) (r : madj K Mb) : msctx Nb Mb N M
| MSLookB {Nb Mb N M K} (s : msctx (S Nb) Mb N M) (w : var K) (r : madj K Mb) : msctx Nb Mb N M.

Scheme madj_mind := Induction for madj Sort Prop
with msctx_mind := Induction for msctx Sort Prop.
Combined Scheme mdata_mind from madj_mind, msctx_mind.

Fixpoint mden {N M} (c : madj N M) : adj term N M :=
  match c in madj N M return adj term N M with
  | MAtom a => a
  | MCompose a b => compose (mden a) (mden b)
  | MShort s => @cform_id term 0 _ _ _ 0 (OShort (msden s))
  | MShortT s σ => @cform_id term 0 0 _ _ 0 (OShortT (STail (msden s) (mden σ)))
  | MCform o σ => cform o (mden σ)
  end
with msden {Nb Mb N M} (s : msctx Nb Mb N M) : @sctx term Nb Mb N M :=
  match s in msctx Nb Mb N M return @sctx term Nb Mb N M with
  | MSEmpty => SEmpty
  | MSLiftF s x => SLiftF (msden s) x
  | MSLiftB s => SLiftB (msden s)
  | MSSubF s x u => SSubF (msden s) x u
  | MSSubB s u => SSubB (msden s) u
  | MSRenF s x w => SRenF (msden s) x w
  | MSRenB s w => SRenB (msden s) w
  | MSSubFA s x u r => SSubFA (msden s) x u (mden r)
  | MSSubBA s u r => SSubBA (msden s) u (mden r)
  | MSLookF s x w r => SLookF (msden s) x w (mden r)
  | MSLookB s w r => SLookB (msden s) w (mden r)
  end.

(** Whether a short form has a lift. *)
Fixpoint mlift {Nb Mb N M} (s : msctx Nb Mb N M) : bool :=
  match s with
  | MSEmpty => false
  | MSLiftF _ _ | MSLiftB _ => true
  | MSSubF s _ _ | MSSubB s _ | MSRenF s _ _ | MSRenB s _ | MSSubFA s _ _ _ | MSSubBA s _ _
  | MSLookF s _ _ _ | MSLookB s _ _ => mlift s
  end.

Variable sub : forall K M, adj term K M -> term K -> term M.

Fixpoint mmat {N M} (c : madj N M) : adj term N M :=
  match c in madj N M return adj term N M with
  | MAtom a => a
  | MCompose a b => compose (mmat a) (mden b)
  | MShort s => if mlift s then @cform_id term 0 _ _ _ 0 (OShort (msden s)) else @cform_id term 0 _ _ _ 0 (OShort (msmat s))
  | MShortT s σ =>
      if mlift s then @cform_id term 0 0 _ _ 0 (OShortT (STail (msden s) (mden σ)))
      else @cform_id term 0 0 _ _ 0 (OShortT (STail (msmat s) (mmat σ)))
  | MCform o σ => cform o (mden σ)
  end
with msmat {Nb Mb N M} (s : msctx Nb Mb N M) : @sctx term Nb Mb N M :=
  match s in msctx Nb Mb N M return @sctx term Nb Mb N M with
  | MSEmpty => SEmpty
  | MSLiftF s x => SLiftF (msmat s) x
  | MSLiftB s => SLiftB (msmat s)
  | MSSubF s x u => SSubF (msmat s) x u
  | MSSubB s u => SSubB (msmat s) u
  | MSRenF s x w => SRenF (msmat s) x w
  | MSRenB s w => SRenB (msmat s) w
  | MSSubFA s x u r => SSubF (msmat s) x (sub _ _ (mmat r) u)
  | MSSubBA s u r => SSubB (msmat s) (sub _ _ (mmat r) u)
  | MSLookF s x w r => SLookF (msmat s) x w (mmat r)
  | MSLookB s w r => SLookB (msmat s) w (mmat r)
  end.

End Mirror.

Arguments madj term : clear implicits.
Arguments msctx term : clear implicits.

(** ** The theorem: shown and materialised meanings are related *)

Section MatRel.

Context {term : nat -> Type}.
Variable tv : forall K, var K -> term K.
Variable sub : forall K M, adj term K M -> term K -> term M.
Local Notation P := {K & term K}.
Local Notation B := (lawbase tv sub).

(** [Rt a a']: the results of [a] and [a'] are related, variable by
    variable; [SR s s']: related tails give related results. *)
Definition Rt {N M} (a a' : adj term N M) : Prop := forall v, drel B (rapply (adj_raw a) v) (rapply (adj_raw a') v).
Definition SR {Nb Mb N M} (s s' : @sctx term Nb Mb N M) : Prop :=
  forall X X' : adj term Nb Mb, Rt X X' -> Rt (sctx_den s X) (sctx_den s' X').

#[local] Transparent in_free in_bound in_look_free in_look_bound compose cform_id identity.

Lemma Rt_refl {N M} (a : adj term N M) : Rt a a.
Proof. intros v; apply DEq. Qed.

Lemma tgt_pay {Mb K} (u : term K) (r r' : adj term K Mb) : Rt r r' ->
  drel B (rtarget_result (to_target (Bind u r))) (rtarget_result (to_target (Bind u r'))).
Proof. intros H; cbn [to_target rtarget_result]; apply pay_rel, H. Qed.

Lemma tgt_mat {Mb K} (u : term K) (r r' : adj term K Mb) : Rt r r' ->
  drel B (rtarget_result (to_target (Bind u r))) (rtarget_result (to_target (Bind (sub K Mb r' u) identity))).
Proof.
  intros H; eapply DTrans; [apply (tgt_pay u r r' H)|].
  apply DBase; left; exists K, Mb, u, r'; split; reflexivity.
Qed.

Lemma push_rel h t t' (A A' : radj P) :
  drel B (rtarget_result t) (rtarget_result t') -> (forall v, drel B (rapply A v) (rapply A' v)) ->
  forall v, drel B (rapply (rpush_inner h t A) v) (rapply (rpush_inner h t' A') v).
Proof. intros Ht HA v; rewrite !rapply_push_inner; destruct (rvar_eqb _ _); auto. Qed.

Local Ltac push := let v := fresh "v" in intros v; unfold in_free, in_bound, in_look_free, in_look_bound; cbn [adj_raw]; revert v; apply push_rel.

Lemma look_tgt {K M} (r r' : adj term K M) w : Rt r r' ->
  drel B (rtarget_result (rapply_target (adj_raw r) (RRename w))) (rtarget_result (rapply_target (adj_raw r') (RRename w))).
Proof.
  intros H; specialize (H w); unfold rapply_target.
  destruct (rapply (adj_raw r) w) as [a|[u ρ]], (rapply (adj_raw r') w) as [a'|[u' ρ']]; exact H.
Qed.

Lemma Rt_compose {N M K} (a a' : adj term M K) (b : adj term N M) : Rt a a' -> Rt (compose a b) (compose a' b).
Proof.
  intros H v; unfold compose; cbn [adj_raw]; rewrite !rapply_compose.
  destruct (rapply (adj_raw b) v) as [w|[u ρ]]; [apply H|apply DPay, H].
Qed.

Theorem mat_rel :
  (forall N M (c : madj term N M), Rt (mden c) (mmat sub c))
  /\ (forall Nb Mb N M (s : msctx term Nb Mb N M), mlift s = false -> SR (msden s) (msmat sub s)).
Proof.
  apply mdata_mind; intros; cbn [mden msden mmat msmat mlift] in *.
  - apply Rt_refl.
  - apply Rt_compose; assumption.
  - destruct (mlift s) eqn:Ls; [apply Rt_refl|].
    unfold cform_id; cbn [octx_den]; apply H; [reflexivity|apply Rt_refl].
  - destruct (mlift s) eqn:Ls; [apply Rt_refl|].
    unfold cform_id; cbn [octx_den]; apply H; [reflexivity|exact H0].
  - apply Rt_refl.
  - intros X X' HX; exact HX.
  - discriminate.
  - discriminate.
  - intros X X' HX; cbn [sctx_den]; apply H; [assumption|push; [apply DEq|exact HX]].
  - intros X X' HX; cbn [sctx_den]; apply H; [assumption|push; [apply DEq|exact HX]].
  - intros X X' HX; cbn [sctx_den]; apply H; [assumption|push; [apply DEq|exact HX]].
  - intros X X' HX; cbn [sctx_den]; apply H; [assumption|push; [apply DEq|exact HX]].
  - intros X X' HX; cbn [sctx_den]; apply H; [assumption|push; [apply tgt_mat, H0|exact HX]].
  - intros X X' HX; cbn [sctx_den]; apply H; [assumption|push; [apply tgt_mat, H0|exact HX]].
  - intros X X' HX; cbn [sctx_den]; apply H; [assumption|push; [apply look_tgt, H0|exact HX]].
  - intros X X' HX; cbn [sctx_den]; apply H; [assumption|push; [apply look_tgt, H0|exact HX]].
Qed.

Lemma mat_rel_a {N M} (c : madj term N M) : Rt (mden c) (mmat sub c).
Proof. apply mat_rel. Qed.

(** For a shared variable [z] standing for a materialised definition. *)
Lemma def_rel {N M} (c : madj term N M) (z : radj P) :
  z = adj_raw (mmat sub c) -> forall v, drel B (rapply (adj_raw (mden c)) v) (rapply z v).
Proof. intros ->; apply mat_rel. Qed.

End MatRel.
