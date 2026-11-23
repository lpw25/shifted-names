(** * The checks [names] makes, with binary indices and environments

    What the kernel checks for [names]: the expressions with binary
    indices ([aexpN]) and the environments as Braun trees ([bof] of the
    lists), so that following an index is logarithmic in it.  Each theorem
    here is one of [HShow] and [HConcrete], with the expressions decoded
    ([adec]) and the environments given as trees equal to [bof] of the
    lists. *)

From Stdlib Require Import String List Arith Lia NArith.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise HConcrete HShow Braun.
Import ListNotations.

(** ** Decoding *)

Fixpoint adec (e : aexpN) : aexp :=
  match e with
  | NId => AId
  | NAtom n => AAtom (N.to_nat n)
  | NCompose a b => ACompose (adec a) (adec b)
  | NOuter h a => AOuter h (adec a)
  | NInner h t a => AInner h (tdec t) (adec a)
  | NLift h a => ALift h (adec a)
  end
with tdec (t : texpN) : texp :=
  match t with
  | NVarE h i => TVarE h (N.to_nat i)
  | NBindE u p => TBindE (N.to_nat u) (adec p)
  | NShiftE h t => TShiftE h (tdec t)
  | NLookE h i a => TLookE h (N.to_nat i) (adec a)
  end.

Scheme aexpN_mind := Induction for aexpN Sort Prop
with texpN_mind := Induction for texpN Sort Prop.
Combined Scheme expN_mind from aexpN_mind, texpN_mind.

Lemma dec_enc : (forall e, adec (aenc e) = e) /\ (forall t, tdec (tenc t) = t).
Proof. apply exp_mind; intros; cbn [adec tdec aenc tenc]; rewrite ?Nat2N.id; congruence. Qed.

Lemma adec_aenc e : adec (aenc e) = e.
Proof. apply dec_enc. Qed.

Lemma nth_error_nth' {A} (l : list A) k d : match nth_error l k with Some x => x | None => d end = nth k l d.
Proof. revert k; induction l as [|x l IH]; intros [|k]; cbn; auto. Qed.

Lemma Forall2_map_r {A B C} (P : A -> C -> Prop) (f : B -> C) xs ys :
  Forall2 (fun x y => P x (f y)) xs ys -> Forall2 P xs (map f ys).
Proof. induction 1; constructor; auto. Qed.

Lemma Forall2_map_l' {A B C} (P : A -> C -> Prop) (f : B -> C) xs ys :
  Forall2 P xs (map f ys) -> Forall2 (fun x y => P x (f y)) xs ys.
Proof. revert xs; induction ys as [|y ys IH]; intros xs H; inversion H; subst; constructor; auto. Qed.

(** ** Denotation *)

Definition ldenB (Le : braun label) (a : lexp) : option label :=
  match a with
  | LNone => None
  | LCon s => Some s
  | LAtom n => Some (match bnth Le n with Some x => x | None => EmptyString end)
  end.

Definition lfacts_okB (Le : braun label) (l : list (lexp * lexp)) : Prop :=
  Forall (fun '(x, y) => olabel_lt (ldenB Le x) (ldenB Le y)) l.

Lemma lfacts_nilB Le : lfacts_okB Le [].
Proof. constructor. Qed.

Lemma lfacts_consB Le x y l : olabel_lt (ldenB Le x) (ldenB Le y) -> lfacts_okB Le l -> lfacts_okB Le ((x, y) :: l).
Proof. intros H Hl; constructor; assumption. Qed.

Lemma ldenB_bof le h : ldenB (bof le) h = lden le h.
Proof. destruct h; cbn [ldenB lden]; [reflexivity|reflexivity|]; rewrite bnth_bof, nth_error_nth'; reflexivity. Qed.

Lemma lfacts_okB_bof le l : lfacts_okB (bof le) l -> lfacts_ok le l.
Proof.
  apply Forall_impl; intros [x y]; rewrite !ldenB_bof; exact (fun H => H).
Qed.

Section Denote.

Context {T : Type}.
Variables (Le : braun label) (Te : braun T) (Ae : braun (radj T)).

Local Notation ldenB := (ldenB Le).

Fixpoint aedenB (e : aexpN) : radj T :=
  match e with
  | NId => ridentity
  | NAtom n => match bnth Ae n with Some x => x | None => ridentity end
  | NCompose a b => rcompose (aedenB a) (aedenB b)
  | NOuter h a => rpush_outer (ldenB h) (aedenB a)
  | NInner h t a => rpush_inner (ldenB h) (tedenB t) (aedenB a)
  | NLift h a => rlift (ldenB h) (aedenB a)
  end
with tedenB (t : texpN) : rtarget T :=
  match t with
  | NVarE h i => RRename (mk_rvar (ldenB h) (N.to_nat i))
  | NBindE u p => match bnth Te u with Some x => RBind x (aedenB p) | None => RRename (mk_rvar None 0) end
  | NShiftE h t => rshift_target (ldenB h) (tedenB t)
  | NLookE h i a => rapply_target (aedenB a) (RRename (mk_rvar (ldenB h) (N.to_nat i)))
  end.

End Denote.

Section Bridge.

Context {T : Type}.
Variables (le : list label) (te : list T) (ae : list (radj T)).

Lemma edenB_bof :
  (forall e, aedenB (bof le) (bof te) (bof ae) e = aeden le te ae (adec e))
  /\ (forall t, tedenB (bof le) (bof te) (bof ae) t = teden le te ae (tdec t)).
Proof.
  apply expN_mind; intros; simpl;
    rewrite ?H, ?H0, ?ldenB_bof; try reflexivity.
  all: unfold aden; rewrite ?bnth_bof, ?nth_error_nth'; reflexivity.
Qed.

Lemma aedenB_bof e : aedenB (bof le) (bof te) (bof ae) e = aeden le te ae (adec e).
Proof. apply edenB_bof. Qed.

End Bridge.

(** ** The checks *)

Definition hshowDN (F : order) (n base : nat) (defs : list (option aexpN)) (e : aexpN) : option (list aexpN * aexpN) :=
  option_map enc_show (HShow.hshowD F n base (map (option_map adec) defs) (adec e)).

Definition hlook_varN (F : order) (n : nat) (e : aexpN) (h : lexp) (i : nat) : option (lexp * nat) :=
  hlook_var F n (adec e) h i.

Definition hlook_payN (F : order) (n base : nat) (e : aexpN) (h : lexp) (i : nat) : option (N * (list aexpN * aexpN)) :=
  option_map (fun p => (N.of_nat (fst p), enc_show (snd p))) (hlook_pay F n base (adec e) h i).

Definition hlook_lookN (F : order) (n base : nat) (e : aexpN) (h : lexp) (i : nat) : option (lexp * N * (list aexpN * aexpN)) :=
  option_map (fun p => let '(g, j, x) := p in (g, N.of_nat j, enc_show x)) (hlook_look F n base (adec e) h i).

Definition hmat_targetN (F : order) (n base : nat) (e : aexpN) : option (N * (list aexpN * aexpN)) :=
  option_map (fun p => (N.of_nat (fst p), enc_show (snd p))) (hmat_target F n base (adec e)).

Definition hmat_displayN (F : order) (n base : nat) (e : aexpN) (k : nat) : option (list aexpN * aexpN) :=
  option_map enc_show (hmat_display F n base (adec e) k).

Section Sound.

Context {T : Type}.
Variables (le : list label) (te : list T) (ae rs : list (radj T)).
Variables (Le : braun label) (Te : braun T) (Ae : braun (radj T)).
Hypotheses (HLe : Le = bof le) (HTe : Te = bof te) (HAe : Ae = bof (ae ++ rs)).

Local Notation den := (aedenB Le Te Ae).

Lemma den_dec e : den e = aeden le te (ae ++ rs) (adec e).
Proof. subst; apply aedenB_bof. Qed.

Lemma den_enc e : den (aenc e) = aeden le te (ae ++ rs) e.
Proof. rewrite den_dec, adec_aenc; reflexivity. Qed.

Lemma lfacts_den l : lfacts_okB Le l -> lfacts_ok le l.
Proof. subst; apply lfacts_okB_bof. Qed.

Lemma shares_den sh : Forall2 (fun x d => x = den d) rs (map aenc sh) ->
  Forall2 (fun x d => x = aeden le te (ae ++ rs) d) rs sh.
Proof.
  intros H; apply Forall2_map_l' in H; revert H; apply Forall2_impl; intros x d ->; apply den_enc.
Qed.

Theorem hshowDB_sound l defs e shN rN : lfacts_okB Le l ->
  hshowDN (order_of l) (List.length te) (List.length ae) defs e = Some (shN, rN) ->
  Forall2 (fun x od => match od with Some d => x = den d | None => True end) ae defs ->
  Forall2 (fun x d => x = den d) rs shN ->
  den e = den rN.
Proof.
  intros Hl E Hd Hs; unfold hshowDN in E.
  destruct (HShow.hshowD _ _ _ _ _) as [[sh r]|] eqn:E0; [|discriminate]; injection E as <- <-.
  rewrite den_dec, den_enc.
  apply (hshowD_sound le te ae rs l _ _ _ _ (lfacts_den l Hl) E0); [|apply shares_den, Hs].
  apply Forall2_map_r; revert Hd; apply Forall2_impl; intros x [d|]; cbn [option_map]; [|trivial].
  rewrite den_dec; exact (fun H => H).
Qed.

Theorem hbindB_show_sound l e h i u shN rN x : lfacts_okB Le l ->
  hlook_payN (order_of l) (List.length te) (List.length ae) e h i = Some (u, (shN, rN)) ->
  Forall2 (fun y d => y = den d) rs shN -> bnth Te u = Some x ->
  rapply (den e) (mk_rvar (ldenB Le h) i) = inr (x, den rN).
Proof.
  intros Hl E Hs Hx; unfold hlook_payN in E.
  destruct (hlook_pay _ _ _ _ _ _) as [[u0 [sh r]]|] eqn:E0; [|discriminate]; injection E as <- <- <-.
  rewrite den_dec, den_enc, HLe, ldenB_bof.
  apply (hbind_show_sound le te ae rs l _ _ _ u0 sh r x (lfacts_den l Hl) E0 (shares_den _ Hs)).
  rewrite HTe, bnth_bof, Nat2N.id in Hx; exact Hx.
Qed.


Theorem hlookB_look_sound l e h i g j shN rN : lfacts_okB Le l ->
  hlook_lookN (order_of l) (List.length te) (List.length ae) e h i = Some (g, j, (shN, rN)) ->
  Forall2 (fun y d => y = den d) rs shN ->
  rapply (den e) (mk_rvar (ldenB Le h) i) = rapply (den rN) (mk_rvar (ldenB Le g) (N.to_nat j)).
Proof.
  intros Hl E Hs; unfold hlook_lookN in E.
  destruct (hlook_look _ _ _ _ _ _) as [[[g0 j0] [sh r]]|] eqn:E0; [|discriminate]; injection E as <- <- <- <-.
  rewrite den_dec, den_enc, HLe, !ldenB_bof, Nat2N.id.
  apply (hlook_look_sound le te ae rs l _ _ _ g0 j0 sh r (lfacts_den l Hl) E0 (shares_den _ Hs)).
Qed.

Section MatB.

Variables (y y' : T).

Theorem hmatB_show_sound l e k u shbN rbN shN rN nb n1 n2 : lfacts_okB Le l ->
  n1 <= List.length te -> n2 <= List.length te ->
  hmat_targetN (order_of l) n1 nb e = Some (u, (shbN, rbN)) ->
  hmat_displayN (order_of l) n2 (List.length ae) e k = Some (shN, rN) ->
  nb = List.length ae + List.length shN ->
  Forall2 (fun x d => x = den d) rs (shN ++ shbN) ->
  bnth Te u = Some y -> bnth Te (N.of_nat k) = Some y' ->
  forall v, drel (mbase y y' (den rbN)) (rapply (den e) v) (rapply (den rN) v).
Proof.
  intros Hl L1 L2 Ht Hd Hnb Hs Hu Hk.
  unfold hmat_targetN in Ht; unfold hmat_displayN in Hd.
  destruct (hmat_target _ _ _ _) as [[u0 [shb rb]]|] eqn:Et; [|discriminate]; injection Ht as <- <- <-.
  destruct (hmat_display _ _ _ _ _) as [[sh r]|] eqn:Ed; [|discriminate]; injection Hd as <- <-.
  intros v; rewrite !den_enc, den_dec.
  assert (B : forall m, bnth Te (N.of_nat m) = nth_error te m) by (intros m; rewrite HTe, bnth_bof, Nat2N.id; reflexivity).
  apply (hmat_show_sound le te ae rs y y' l _ k u0 shb rb sh r nb n1 n2 (lfacts_den l Hl) L1 L2 Et Ed).
  - rewrite Hnb, length_map; reflexivity.
  - apply shares_den; rewrite map_app; exact Hs.
  - rewrite <- B; exact Hu.
  - rewrite <- B; exact Hk.
Qed.

End MatB.

End Sound.

Theorem hlook_varB_sound {T} (le : list label) (te : list T) (ae : list (radj T))
    Le Te Ae l e h i h' j :
  Le = bof le -> Te = bof te -> Ae = bof ae -> lfacts_okB Le l ->
  hlook_varN (order_of l) (List.length te) e h i = Some (h', j) ->
  rapply (aedenB Le Te Ae e) (mk_rvar (ldenB Le h) i) = inl (mk_rvar (ldenB Le h') j).
Proof.
  intros -> -> -> Hl E; rewrite aedenB_bof, !ldenB_bof.
  apply (hlook_var_sound le te ae l _ h i h' j (lfacts_okB_bof _ _ Hl) E).
Qed.
