(** * Showing normal forms, proved for the library's adjustments

    [hshow] normalises an expression with [HNorm] and shows the normal
    form ([HDisplay]).  [hshow_sound]: the expression means what it is
    shown as, given that each shared definition's atom is the
    definition. *)

From Stdlib Require Import List Arith Lia Bool PArith.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Comp KnownOrder HRefine CSound HConcrete.
From ShiftedNames.Core Require HNorm CNorm HDisplay HDisplaySound.
Import ListNotations.

(** Normalise [e] and show it, shared definitions numbered from
    [base].  Term atoms are checked to be below [n]. *)
Definition hshow (F : order) (n base : nat) (e : aexp) : option (list aexp * aexp) :=
  if aok n e then
    let '(w, T) := HNorm.norm F e [] HNorm.st0 in
    match HDisplay.display F base T (HNorm.wid w) with
    | Some (sh, r) => if forallb (aok n) sh && aok n r then Some (sh, r) else None
    | None => None
    end
  else None.

(** ** Materialising

    The first term entry with a payload, in a word without atoms; and
    the word with that term replaced by the term atom [k] with the
    identity payload. *)
Fixpoint first_paid (w : HNorm.word) : option (nat * positive) :=
  match w with
  | [] => None
  | (HNorm.SE _ (HNorm.VTerm u None p), _) :: r => if Pos.eqb p 1 then first_paid r else Some (u, p)
  | _ :: r => first_paid r
  end.

Fixpoint has_atom (w : HNorm.word) : bool :=
  match w with [] => false | (HNorm.SA _, _) :: _ => true | _ :: r => has_atom r end.

Fixpoint replace_paid (k : nat) (w : HNorm.word) : list HNorm.step :=
  match w with
  | [] => []
  | (HNorm.SE h (HNorm.VTerm u None p) as s, _) :: r =>
      if Pos.eqb p 1 then s :: replace_paid k r else HNorm.SE h (HNorm.VTerm k None 1) :: map fst r
  | (s, _) :: r => s :: replace_paid k r
  end.

Definition hmat_target (F : order) (n base : nat) (e : aexp) : option (nat * (list aexp * aexp)) :=
  if aok n e then
    let '(w, T) := HNorm.norm F e [] HNorm.st0 in
    if has_atom w then None
    else match first_paid w with
         | Some (u, p) =>
             match HDisplay.display_s F base false T p with
             | Some (sh, r) => if forallb (aok n) sh && aok n r && Nat.ltb u n then Some (u, (sh, r)) else None
             | None => None
             end
         | None => None
         end
  else None.

Definition hmat_display (F : order) (n base : nat) (e : aexp) (k : nat) : option (list aexp * aexp) :=
  if aok n e then
    let '(w, T) := HNorm.norm F e [] HNorm.st0 in
    if has_atom w then None
    else
      let '(w', T') := HNorm.rebuild (replace_paid k w) [] T in
      match HDisplay.display F base T' (HNorm.wid w') with
      | Some (sh, r) => if forallb (aok n) sh && aok n r then Some (sh, r) else None
      | None => None
      end
  else None.

Lemma F2_nth {A B} (P : A -> B -> Prop) xs ys s d : Forall2 P xs ys -> nth_error ys s = Some d ->
  exists x, nth_error xs s = Some x /\ P x d.
Proof.
  intros H; revert s; induction H as [|x y xs ys Hxy H IH]; intros [|s] E; cbn in E; try discriminate.
  - injection E as <-; exists x; split; [reflexivity|exact Hxy].
  - apply IH, E.
Qed.

Section Show.

Context {T : Type}.
Variables (lenv : list label) (tenv : list T) (aenv rs : list (radj T)) (penv : list (rpadj T)).

Local Notation aeden := (aeden lenv tenv (aenv ++ rs) penv).

Theorem hshow_sound l e sh r : lfacts_ok lenv l ->
  hshow (order_of l) (List.length tenv) (List.length aenv) e = Some (sh, r) ->
  Forall2 (fun x d => x = aeden d) rs sh ->
  aeden e = aeden r.
Proof.
  intros Hl E Hs; unfold hshow in E.
  destruct (aok (List.length tenv) e) eqn:Ae; [|discriminate].
  destruct (HNorm.norm (order_of l) e [] HNorm.st0) as [w T0] eqn:En.
  destruct (HDisplay.display (order_of l) (List.length aenv) T0 (HNorm.wid w)) as [[sh0 r0]|] eqn:Ed; [|discriminate].
  destruct (forallb (aok (List.length tenv)) sh0 && aok (List.length tenv) r0) eqn:Ok; [|discriminate].
  injection E as -> ->; apply andb_true_iff in Ok as [Osh Or].
  pose proof (order_of_irrefl l lenv Hl) as Hirr; pose proof (order_of_trans l lenv Hl) as Htr.
  set (K := kmodel lenv tenv (aenv ++ rs) penv).
  pose proof (kcons lenv tenv (aenv ++ rs) penv _ (order_of_ok lenv l Hl)) as HM.
  destruct (kden lenv tenv (aenv ++ rs) penv (List.length tenv) (le_n _)) as [Ka _].
  destruct (proj1 (norm_spec_all (order_of l) Hirr Htr) e [] HNorm.st0 [] w T0 Inv_st0 (RWNil _) En) as [I1 [_ R1]].
  assert (HS : forall s d, nth_error sh s = Some d -> forall x, @catom K (List.length aenv + s) x = @ca K d x).
  { intros s d Hd x; rewrite (Ka d) by (rewrite forallb_forall in Osh; apply Osh, (nth_error_In _ _ Hd)).
    cbn [K kmodel catom]; f_equal; unfold aden; rewrite app_nth2 by lia.
    replace (List.length aenv + s - List.length aenv) with s by lia.
    destruct (F2_nth _ _ _ s d Hs Hd) as [x0 [Hx0 ->]]; apply nth_error_nth, Hx0. }
  pose proof (HDisplaySound.display_sound (order_of l) Hirr Htr K HM (List.length aenv) T0 (HNorm.wid w) sh r
                (CNorm.norm (order_of l) e []) I1 (RWord_RId _ _ _ R1) Ed HS ridentity) as D.
  rewrite (Ka r Or), rcompose_identity_l in D; rewrite D.
  rewrite (norm_meaning K _ HM), (Ka e Ae), rcompose_identity_l; reflexivity.
Qed.


Lemma shares_model l n sh : lfacts_ok lenv l -> n <= List.length tenv ->
  Forall2 (fun x d => x = aeden d) rs sh -> forallb (aok n) sh = true ->
  forall s d, nth_error sh s = Some d -> forall x,
    @catom (kmodel lenv tenv (aenv ++ rs) penv) (List.length aenv + s) x = @ca (kmodel lenv tenv (aenv ++ rs) penv) d x.
Proof.
  intros Hl Hn Hs Osh s d Hd x.
  destruct (kden lenv tenv (aenv ++ rs) penv n Hn) as [Ka _].
  rewrite (Ka d) by (rewrite forallb_forall in Osh; apply Osh, (nth_error_In _ _ Hd)).
  cbn [kmodel catom]; f_equal; unfold aden; rewrite app_nth2 by lia.
  replace (List.length aenv + s - List.length aenv) with s by lia.
  destruct (F2_nth _ _ _ s d Hs Hd) as [x0 [Hx0 ->]]; apply nth_error_nth, Hx0.
Qed.

(** ** A variable sent to a term: the term and its payload, shown *)

Definition hlook_pay (F : order) (n base : nat) (e : aexp) (h : lexp) (i : nat) : option (nat * (list aexp * aexp)) :=
  match hlook F n e h i with
  | Some (HNorm.VTerm u None p, T1) =>
      match HDisplay.display F base T1 p with
      | Some (sh, r) => if forallb (aok n) sh && aok n r then Some (u, (sh, r)) else None
      | None => None
      end
  | _ => None
  end.

Theorem hbind_show_sound l e h i u sh r x : lfacts_ok lenv l ->
  hlook_pay (order_of l) (List.length tenv) (List.length aenv) e h i = Some (u, (sh, r)) ->
  Forall2 (fun y d => y = aeden d) rs sh -> nth_error tenv u = Some x ->
  rapply (aeden e) (mk_rvar (lden lenv h) i) = inr (x, rpcompose (aeden r) rpidentity).
Proof.
  intros Hl H Hs Hx; unfold hlook_pay, hlook in H; destruct (aok _ e) eqn:Ha; [|discriminate].
  set (F := order_of l) in *.
  destruct (HNorm.norm F e [] HNorm.st0) as [w T0] eqn:En; destruct (HNorm.lookup F h i w T0) as [v T1] eqn:El.
  destruct v as [|u' [b|] p|]; try discriminate.
  destruct (HDisplay.display F (List.length aenv) T1 p) as [[sh0 r0]|] eqn:Ed; [|discriminate].
  destruct (forallb (aok (List.length tenv)) sh0 && aok (List.length tenv) r0) eqn:Ok; [|discriminate].
  injection H as -> -> ->; apply andb_true_iff in Ok as [Osh Or].
  pose proof (order_of_irrefl l lenv Hl) as Hirr; pose proof (order_of_trans l lenv Hl) as Htr.
  set (K := kmodel lenv tenv (aenv ++ rs) penv).
  pose proof (kcons lenv tenv (aenv ++ rs) penv _ (order_of_ok lenv l Hl)) as HM.
  destruct (kden lenv tenv (aenv ++ rs) penv (List.length tenv) (le_n _)) as [Ka _].
  destruct (proj1 (norm_spec_all F Hirr Htr) e [] HNorm.st0 [] w T0 Inv_st0 (RWNil _) En) as [I1 [_ R1]].
  destruct (lookup_spec F Hirr Htr T0 h w _ I1 R1 i _ T1 El) as [I2 [_ R2]].
  pose proof (klookup lenv tenv (aenv ++ rs) penv l e h i Hl Ha) as Kl; fold F in Kl.
  destruct (RVal_term _ _ _ _ _ R2) as [cp [Ecp Rp]]; rewrite Ecp in Kl.
  pose proof (HDisplaySound.display_sound F Hirr Htr K HM (List.length aenv) T1 p sh r cp I2 Rp Ed
                (shares_model l _ sh Hl (le_n _) Hs Osh) ridentity) as D.
  rewrite (Ka r Or), rcompose_identity_l in D; unfold K in D.
  rewrite vden_term, <- D in Kl.
  cbn [K kmodel cterm] in Kl; unfold kterm in Kl; rewrite Hx in Kl; unfold rapply_target in Kl.
  destruct (rapply (aeden e) _) as [w'|[u' ρ]]; [discriminate|injection Kl as -> ->; reflexivity].
Qed.


Lemma RWord_fst S w cw : RWord S w cw -> Forall2 (RStep S) (map fst w) cw.
Proof. induction 1; constructor; assumption. Qed.

Lemma aok_mono :
  forall n n', n <= n' -> (forall a, aok n a = true -> aok n' a = true) /\ (forall t, tok n t = true -> tok n' t = true)
    /\ (forall p, pok n p = true -> pok n' p = true).
Proof.
  intros n n' L; apply exp_mind; cbn [aok tok pok]; intros; rewrite ?andb_true_iff in *; try tauto.
  destruct H0 as [H1 H2]; split; [apply Nat.ltb_lt in H1; apply Nat.ltb_lt; lia|auto].
Qed.

Section MatShow.

Variable g : rpadj T -> T -> T.

Lemma matw_same S w cw : RWord S w cw -> has_atom w = false -> matw lenv tenv (aenv ++ rs) penv g cw cw.
Proof.
  induction 1 as [|s i w cs cw Hc Hs Hw IH]; intros A; [constructor|].
  destruct s as [h v|h|a]; cbn [has_atom] in A; [| |discriminate]; inversion Hs; subst;
    (apply MSame; [exact I|apply IH, A]).
Qed.

Lemma paid_matw S w cw k u p : Inv S -> RWord S w cw -> has_atom w = false -> first_paid w = Some (u, p) ->
  (forall cp, RId S p cp -> tmrel g
       (@vden (kmodel lenv tenv (aenv ++ rs) penv) (CNorm.VTerm u None cp) ridentity)
       (@vden (kmodel lenv tenv (aenv ++ rs) penv) (CNorm.VTerm k None []) ridentity)) ->
  exists cw', Forall2 (RStep S) (replace_paid k w) cw' /\ matw lenv tenv (aenv ++ rs) penv g cw cw'.
Proof.
  intros I H; induction H as [|s i w cs cw Hc Hs Hw IH]; intros A Fp Prem; [discriminate|].
  destruct s as [h v|h|a]; cbn [has_atom] in A; [| |discriminate].
  - destruct v as [g0 j|u0 [b|] p0|g0 j x].
    + cbn [first_paid replace_paid] in Fp |- *; destruct (IH A Fp Prem) as [cw' [Hf Hm]].
      exists (cs :: cw'); split; [constructor; assumption|apply MSame; [inversion Hs; exact Logic.I|exact Hm]].
    + cbn [first_paid replace_paid] in Fp |- *; destruct (IH A Fp Prem) as [cw' [Hf Hm]].
      exists (cs :: cw'); split; [constructor; assumption|apply MSame; [inversion Hs; exact Logic.I|exact Hm]].
    + cbn [first_paid replace_paid] in Fp |- *; destruct (Pos.eqb p0 1) eqn:E1.
      * destruct (IH A Fp Prem) as [cw' [Hf Hm]].
        exists (cs :: cw'); split; [constructor; assumption|apply MSame; [inversion Hs; exact Logic.I|exact Hm]].
      * injection Fp as -> ->.
        destruct (RStep_SE_term _ _ _ _ _ _ Hs) as [cp [-> Hp]].
        exists (CNorm.SE h (CNorm.VTerm k None []) :: cw); split.
        -- constructor; [constructor; constructor; constructor|apply RWord_fst, Hw].
        -- apply MEnt; [apply Prem, Hp|apply (matw_same S w cw Hw A)].
    + cbn [first_paid replace_paid] in Fp |- *; destruct (IH A Fp Prem) as [cw' [Hf Hm]].
      exists (cs :: cw'); split; [constructor; assumption|apply MSame; [inversion Hs; exact Logic.I|exact Hm]].
  - cbn [first_paid replace_paid] in Fp |- *; destruct (IH A Fp Prem) as [cw' [Hf Hm]].
    exists (cs :: cw'); split; [constructor; assumption|apply MSame; [inversion Hs; exact Logic.I|exact Hm]].
Qed.

Theorem hmat_show_sound l e k u shb rb sh r nb n1 n2 : lfacts_ok lenv l ->
  n1 <= List.length tenv -> n2 <= List.length tenv ->
  hmat_target (order_of l) n1 nb e = Some (u, (shb, rb)) ->
  hmat_display (order_of l) n2 (List.length aenv) e k = Some (sh, r) ->
  nb = List.length aenv + List.length sh ->
  Forall2 (fun x d => x = aeden d) rs (sh ++ shb) ->
  (forall y, nth_error tenv u = Some y -> nth_error tenv k = Some (g (rpcompose (aeden rb) rpidentity) y)) ->
  forall v, mrel g (rapply (aeden e) v) (rapply (aeden r) v).
Proof.
  intros Hl L1 L2 Ht Hd Hnb Hs Hk.
  unfold hmat_target in Ht; unfold hmat_display in Hd.
  destruct (aok n1 e) eqn:Ae; [|discriminate]; destruct (aok n2 e) eqn:Ae2; [|discriminate].
  set (F := order_of l) in *.
  destruct (HNorm.norm F e [] HNorm.st0) as [w T0] eqn:En.
  destruct (has_atom w) eqn:Hat; [discriminate|].
  destruct (first_paid w) as [[u0 p]|] eqn:Fp; [|discriminate].
  destruct (HDisplay.display_s F nb false T0 p) as [[shb0 rb0]|] eqn:Eb; [|discriminate].
  destruct (forallb (aok n1) shb0 && aok n1 rb0 && Nat.ltb u0 n1) eqn:Okb; [|discriminate]; injection Ht as -> -> ->.
  destruct (HNorm.rebuild (replace_paid k w) [] T0) as [w' T1] eqn:Er.
  destruct (HDisplay.display F (List.length aenv) T1 (HNorm.wid w')) as [[sh0 r0]|] eqn:Ed; [|discriminate].
  destruct (forallb (aok n2) sh0 && aok n2 r0) eqn:Ok; [|discriminate]; injection Hd as -> ->.
  apply andb_true_iff in Okb as [Okb Lu]; apply Nat.ltb_lt in Lu.
  apply andb_true_iff in Okb as [Oshb Orb]; apply andb_true_iff in Ok as [Osh Or].
  pose proof (order_of_irrefl l lenv Hl) as Hirr; pose proof (order_of_trans l lenv Hl) as Htr.
  set (K := kmodel lenv tenv (aenv ++ rs) penv).
  pose proof (kcons lenv tenv (aenv ++ rs) penv _ (order_of_ok lenv l Hl)) as HM.
  destruct (kden lenv tenv (aenv ++ rs) penv (List.length tenv) (le_n _)) as [Ka _].
  destruct (proj1 (norm_spec_all F Hirr Htr) e [] HNorm.st0 [] w T0 Inv_st0 (RWNil _) En) as [I1 [_ R1]].
  (* the shares of both displays *)
  assert (Osh_all : forallb (aok (List.length tenv)) (sh ++ shb) = true).
  { rewrite forallb_app, andb_true_iff; split; rewrite forallb_forall in *; intros d Hd;
      [apply (proj1 (aok_mono n2 _ L2)), Osh, Hd|apply (proj1 (aok_mono n1 _ L1)), Oshb, Hd]. }
  pose proof (shares_model l _ _ Hl (le_n _) Hs Osh_all) as SM.
  assert (SA : forall s d, nth_error sh s = Some d -> forall x, @catom K (List.length aenv + s) x = @ca K d x).
  { intros s0 d Hd x; apply SM; rewrite nth_error_app1; [exact Hd|apply nth_error_Some; rewrite Hd; discriminate]. }
  assert (SB : forall s d, nth_error shb s = Some d -> forall x, @catom K (nb + s) x = @ca K d x).
  { intros s0 d Hd x; rewrite Hnb, <- Nat.add_assoc; apply SM.
    rewrite nth_error_app2 by lia; rewrite Nat.add_comm, Nat.add_sub; exact Hd. }
  (* the payload term and the term atom [k] are related *)
  assert (Prem : forall cp, RId T0 p cp ->
            tmrel g (@vden K (CNorm.VTerm u None cp) ridentity) (@vden K (CNorm.VTerm k None []) ridentity)).
  { intros cp Hp.
    pose proof (HDisplaySound.display_s_sound F Hirr Htr K HM nb false T0 p shb rb cp I1 Hp Eb SB ridentity) as D.
    rewrite (Ka rb (proj1 (aok_mono n1 _ L1) rb Orb)), rcompose_identity_l in D; unfold K in D.
    rewrite !vden_term; cbn [K kmodel cterm]; unfold kterm.
    destruct (nth_error tenv u) as [y|] eqn:Ey; [|apply nth_error_None in Ey; lia].
    rewrite (Hk y eq_refl); change (bden penv None) with (@rpidentity T).
    change (@wden K [] ridentity) with (@ridentity T); rewrite rpcompose_identity.
    right; exists y, (rpcompose (aeden rb) rpidentity); split; [rewrite D; reflexivity|reflexivity]. }
  destruct (paid_matw T0 w _ k u p I1 R1 Hat Fp Prem) as [cw' [Hf Hm]].
  destruct (rebuild_spec (replace_paid k w) cw' T0 [] [] w' T1 I1 Hf (RWNil _) Er) as [I2 [X2 R2]].
  rewrite app_nil_r in R2.
  pose proof (HDisplaySound.display_sound F Hirr Htr K HM (List.length aenv) T1 (HNorm.wid w') sh r cw' I2
                (RWord_RId _ _ _ R2) Ed SA ridentity) as D.
  rewrite (Ka r (proj1 (aok_mono n2 _ L2) r Or)), rcompose_identity_l in D; unfold K in D.
  intros v; rewrite D, <- (kword_meaning lenv tenv (aenv ++ rs) penv l e Hl (proj1 (aok_mono n1 _ L1) e Ae)).
  apply matw_mrel, Hm.
Qed.

End MatShow.

End Show.
