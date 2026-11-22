(** * Showing normal forms, proved for the library's adjustments

    [hshow] normalises an expression with [HNorm] and shows the normal
    form ([HDisplay]).  [hshow_sound]: the expression means what it is
    shown as, given that each shared definition's atom is the
    definition. *)

From Stdlib Require Import List Arith Lia Bool PArith NArith.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Comp KnownOrder HRefine CSound HConcrete.
From ShiftedNames.Core Require HNorm CNorm HDisplay HDisplaySound CRange.
Import ListNotations.

(** The input: term atoms below [n], adjustment atoms below [base]
    (what [names] reifies always is); what is shown is then in range too
    ([HDisplaySound.display_s_aok]). *)
Definition inp (n base : nat) (e : aexp) : bool := aok n e && CRange.inrange n base e.

(** Normalise [e] and show it, shared definitions numbered from
    [base]. *)
Definition hshow (F : order) (n base : nat) (e : aexp) : option (list aexp * aexp) :=
  if inp n base e then
    let '(w, T) := HNorm.norm F e [] HNorm.st0 in HDisplay.display F base T (HNorm.wid w)
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
  if inp n base e then
    let '(w, T) := HNorm.norm F e [] HNorm.st0 in
    if has_atom w then None
    else match first_paid w with
         | Some (u, p) =>
             match HDisplay.display_s F base false T p with
             | Some (sh, r) => Some (u, (sh, r))
             | None => None
             end
         | None => None
         end
  else None.

Definition hmat_display (F : order) (n base : nat) (e : aexp) (k : nat) : option (list aexp * aexp) :=
  if inp n base e && Nat.ltb k n then
    let '(w, T) := HNorm.norm F e [] HNorm.st0 in
    if has_atom w then None
    else
      let '(w', T') := HNorm.rebuild (replace_paid k w) [] T in
      HDisplay.display F base T' (HNorm.wid w')
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
  intros Hl E Hs; unfold hshow, inp in E.
  destruct (aok (List.length tenv) e) eqn:Ae; [|discriminate].
  destruct (CRange.inrange (List.length tenv) (List.length aenv) e) eqn:Ar; [|discriminate].
  destruct (HNorm.norm (order_of l) e [] HNorm.st0) as [w T0] eqn:Ed; cbn [andb] in E.
  pose proof (proj1 (CRange.norm_ok _ _ (order_of l)) e [] Ar (Forall_nil _)) as Oc.
  pose proof (order_of_irrefl l lenv Hl) as Hirr; pose proof (order_of_trans l lenv Hl) as Htr.
  rename Ed into En.
  set (K := kmodel lenv tenv (aenv ++ rs) penv).
  pose proof (kcons lenv tenv (aenv ++ rs) penv _ (order_of_ok lenv l Hl)) as HM.
  destruct (kden lenv tenv (aenv ++ rs) penv (List.length tenv) (le_n _)) as [Ka _].
  destruct (proj1 (norm_spec_all (order_of l) Hirr Htr) e [] HNorm.st0 [] w T0 Inv_st0 (RWNil _) En) as [I1 [_ R1]].
  destruct (HDisplaySound.display_s_aok (order_of l) K (List.length aenv) (List.length tenv) true T0
              (HNorm.wid w) sh r _ I1 (RWord_RId _ _ _ R1) Oc E) as [Osh Or].
  assert (HS : forall s d, nth_error sh s = Some d -> forall x, @catom K (List.length aenv + s) x = @ca K d x).
  { intros s d Hd x; rewrite (Ka d) by (rewrite Forall_forall in Osh; apply Osh, (nth_error_In _ _ Hd)).
    cbn [K kmodel catom]; f_equal; unfold aden; rewrite app_nth2 by lia.
    replace (List.length aenv + s - List.length aenv) with s by lia.
    destruct (F2_nth _ _ _ s d Hs Hd) as [x0 [Hx0 ->]]; apply nth_error_nth, Hx0. }
  pose proof (HDisplaySound.display_sound (order_of l) K (List.length aenv) (List.length tenv) T0 (HNorm.wid w) sh r
                (CNorm.norm (order_of l) e []) I1 (RWord_RId _ _ _ R1) Oc E HS ridentity) as D.
  rewrite (Ka r Or), rcompose_identity_l in D; rewrite D.
  rewrite (norm_meaning K _ HM), (Ka e Ae), rcompose_identity_l; reflexivity.
Qed.


Lemma shares_model l n sh : lfacts_ok lenv l -> n <= List.length tenv ->
  Forall2 (fun x d => x = aeden d) rs sh -> Forall (fun d => aok n d = true) sh ->
  forall s d, nth_error sh s = Some d -> forall x,
    @catom (kmodel lenv tenv (aenv ++ rs) penv) (List.length aenv + s) x = @ca (kmodel lenv tenv (aenv ++ rs) penv) d x.
Proof.
  intros Hl Hn Hs Osh s d Hd x.
  destruct (kden lenv tenv (aenv ++ rs) penv n Hn) as [Ka _].
  rewrite (Ka d) by (rewrite Forall_forall in Osh; apply Osh, (nth_error_In _ _ Hd)).
  cbn [kmodel catom]; f_equal; unfold aden; rewrite app_nth2 by lia.
  replace (List.length aenv + s - List.length aenv) with s by lia.
  destruct (F2_nth _ _ _ s d Hs Hd) as [x0 [Hx0 ->]]; apply nth_error_nth, Hx0.
Qed.

(** ** A variable sent to a term: the term and its payload, shown *)

Definition hlook_pay (F : order) (n base : nat) (e : aexp) (h : lexp) (i : nat) : option (nat * (list aexp * aexp)) :=
  if inp n base e then
    let '(w, T0) := HNorm.norm F e [] HNorm.st0 in
    match HNorm.lookup F h i w T0 with
    | (HNorm.VTerm u None p, T1) =>
        match HDisplay.display F base T1 p with
        | Some (sh, r) => Some (u, (sh, r))
        | None => None
        end
    | _ => None
    end
  else None.

Theorem hbind_show_sound l e h i u sh r x : lfacts_ok lenv l ->
  hlook_pay (order_of l) (List.length tenv) (List.length aenv) e h i = Some (u, (sh, r)) ->
  Forall2 (fun y d => y = aeden d) rs sh -> nth_error tenv u = Some x ->
  rapply (aeden e) (mk_rvar (lden lenv h) i) = inr (x, rpcompose (aeden r) rpidentity).
Proof.
  intros Hl H Hs Hx; unfold hlook_pay, inp in H.
  destruct (aok _ e) eqn:Ha; [|discriminate]; destruct (CRange.inrange _ _ e) eqn:Ar; [|discriminate]; cbn [andb] in H.
  set (F := order_of l) in *.
  destruct (HNorm.norm F e [] HNorm.st0) as [w T0] eqn:En; destruct (HNorm.lookup F h i w T0) as [v T1] eqn:El.
  destruct v as [|u' [b|] p|]; try discriminate.
  destruct (HDisplay.display F (List.length aenv) T1 p) as [[sh0 r0]|] eqn:Ed; [|discriminate].
  injection H as -> -> ->.
  pose proof (order_of_irrefl l lenv Hl) as Hirr; pose proof (order_of_trans l lenv Hl) as Htr.
  set (K := kmodel lenv tenv (aenv ++ rs) penv).
  pose proof (kcons lenv tenv (aenv ++ rs) penv _ (order_of_ok lenv l Hl)) as HM.
  destruct (kden lenv tenv (aenv ++ rs) penv (List.length tenv) (le_n _)) as [Ka _].
  destruct (proj1 (norm_spec_all F Hirr Htr) e [] HNorm.st0 [] w T0 Inv_st0 (RWNil _) En) as [I1 [_ R1]].
  destruct (lookup_spec F Hirr Htr T0 h w _ I1 R1 i _ T1 El) as [I2 [_ R2]].
  pose proof (klookup lenv tenv (aenv ++ rs) penv l e h i Hl Ha) as Kl; fold F in Kl.
  destruct (RVal_term _ _ _ _ _ R2) as [cp [Ecp Rp]]; rewrite Ecp in Kl.
  pose proof (CRange.lookup_ok _ _ F h i _ (proj1 (CRange.norm_ok _ _ F) e [] Ar (Forall_nil _))) as Ov.
  rewrite Ecp in Ov; inversion Ov as [|? ? ? _ Op|]; subst.
  destruct (HDisplaySound.display_s_aok F K (List.length aenv) (List.length tenv) true T1 p sh r cp I2 Rp Op Ed)
    as [Osh Or].
  pose proof (HDisplaySound.display_sound F K (List.length aenv) (List.length tenv) T1 p sh r cp I2 Rp Op Ed
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

Lemma paid_ok n b S w cw u p : RWord S w cw -> CRange.WOk n b cw -> first_paid w = Some (u, p) ->
  exists cp, RId S p cp /\ CRange.WOk n b cp /\ u < n.
Proof.
  intros H; induction H as [|s i w cs cw Hc Hs Hw IH]; intros O Fp; [discriminate|].
  inversion O as [|? ? Os Ow]; subst.
  destruct s as [h [g0 j|u0 [b0|] p0|g0 j x]|h|a]; cbn [first_paid] in Fp; try (apply IH; assumption).
  destruct (Pos.eqb p0 1); [apply IH; assumption|injection Fp as -> ->].
  destruct (RStep_SE_term _ _ _ _ _ _ Hs) as [cp [-> Hp]].
  inversion Os as [? ? Ov| |]; subst; inversion Ov; subst; exists cp; split; [exact Hp|split; assumption].
Qed.

Lemma paid_matw S w cw k u p : Inv S -> RWord S w cw -> has_atom w = false -> first_paid w = Some (u, p) ->
  (forall cp, RId S p cp -> tmrel g
       (@vden (kmodel lenv tenv (aenv ++ rs) penv) (CNorm.VTerm u None cp) ridentity)
       (@vden (kmodel lenv tenv (aenv ++ rs) penv) (CNorm.VTerm k None []) ridentity)) ->
  exists cw', Forall2 (RStep S) (replace_paid k w) cw' /\ matw lenv tenv (aenv ++ rs) penv g cw cw' /\
    (forall n b, k < n -> CRange.WOk n b cw -> CRange.WOk n b cw').
Proof.
  intros I H; induction H as [|s i w cs cw Hc Hs Hw IH]; intros A Fp Prem; [discriminate|].
  destruct s as [h v|h|a]; cbn [has_atom] in A; [| |discriminate].
  - destruct v as [g0 j|u0 [b|] p0|g0 j x].
    + cbn [first_paid replace_paid] in Fp |- *; destruct (IH A Fp Prem) as [cw' [Hf [Hm Ho]]].
      exists (cs :: cw'); split; [constructor; assumption|split; [apply MSame; [inversion Hs; exact Logic.I|exact Hm]|]].
      intros nn bb Lk O; inversion O; constructor; [assumption|apply Ho; assumption].
    + cbn [first_paid replace_paid] in Fp |- *; destruct (IH A Fp Prem) as [cw' [Hf [Hm Ho]]].
      exists (cs :: cw'); split; [constructor; assumption|split; [apply MSame; [inversion Hs; exact Logic.I|exact Hm]|]].
      intros nn bb Lk O; inversion O; constructor; [assumption|apply Ho; assumption].
    + cbn [first_paid replace_paid] in Fp |- *; destruct (Pos.eqb p0 1) eqn:E1.
      * destruct (IH A Fp Prem) as [cw' [Hf [Hm Ho]]].
        exists (cs :: cw'); split; [constructor; assumption|split; [apply MSame; [inversion Hs; exact Logic.I|exact Hm]|]].
        intros nn bb Lk O; inversion O; constructor; [assumption|apply Ho; assumption].
      * injection Fp as -> ->.
        destruct (RStep_SE_term _ _ _ _ _ _ Hs) as [cp [-> Hp]].
        exists (CNorm.SE h (CNorm.VTerm k None []) :: cw); split.
        -- constructor; [constructor; constructor; constructor|apply RWord_fst, Hw].
        -- split; [apply MEnt; [apply Prem, Hp|apply (matw_same S w cw Hw A)]|].
           intros nn bb Lk O; inversion O; subst; constructor; [constructor; constructor; [exact Lk|constructor]|assumption].
    + cbn [first_paid replace_paid] in Fp |- *; destruct (IH A Fp Prem) as [cw' [Hf [Hm Ho]]].
      exists (cs :: cw'); split; [constructor; assumption|split; [apply MSame; [inversion Hs; exact Logic.I|exact Hm]|]].
      intros nn bb Lk O; inversion O; constructor; [assumption|apply Ho; assumption].
  - cbn [first_paid replace_paid] in Fp |- *; destruct (IH A Fp Prem) as [cw' [Hf [Hm Ho]]].
    exists (cs :: cw'); split; [constructor; assumption|split; [apply MSame; [inversion Hs; exact Logic.I|exact Hm]|]].
    intros nn bb Lk O; inversion O; constructor; [assumption|apply Ho; assumption].
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
  unfold hmat_target, inp in Ht; unfold hmat_display, inp in Hd.
  destruct (aok n1 e) eqn:Ae; [|discriminate]; destruct (CRange.inrange n1 nb e) eqn:Ar1; [|discriminate].
  destruct (aok n2 e) eqn:Ae2; [|discriminate]; destruct (CRange.inrange n2 (List.length aenv) e) eqn:Ar2; [|discriminate].
  destruct (Nat.ltb k n2) eqn:Lk; [|discriminate]; apply Nat.ltb_lt in Lk; cbn [andb] in Ht, Hd.
  set (F := order_of l) in *.
  destruct (HNorm.norm F e [] HNorm.st0) as [w T0] eqn:En.
  destruct (has_atom w) eqn:Hat; [discriminate|].
  destruct (first_paid w) as [[u0 p]|] eqn:Fp; [|discriminate].
  destruct (HDisplay.display_s F nb false T0 p) as [[shb0 rb0]|] eqn:Eb; [|discriminate]; injection Ht as -> -> ->.
  destruct (HNorm.rebuild (replace_paid k w) [] T0) as [w' T1] eqn:Er.
  pose proof (order_of_irrefl l lenv Hl) as Hirr; pose proof (order_of_trans l lenv Hl) as Htr.
  set (K := kmodel lenv tenv (aenv ++ rs) penv).
  pose proof (kcons lenv tenv (aenv ++ rs) penv _ (order_of_ok lenv l Hl)) as HM.
  destruct (kden lenv tenv (aenv ++ rs) penv (List.length tenv) (le_n _)) as [Ka _].
  destruct (proj1 (norm_spec_all F Hirr Htr) e [] HNorm.st0 [] w T0 Inv_st0 (RWNil _) En) as [I1 [_ R1]].
  pose proof (proj1 (CRange.norm_ok _ _ F) e [] Ar1 (Forall_nil _)) as Oc1.
  pose proof (proj1 (CRange.norm_ok _ _ F) e [] Ar2 (Forall_nil _)) as Oc2.
  destruct (paid_ok _ _ T0 w _ u p R1 Oc1 Fp) as [cp0 [Hp0 [Op0 Lu]]].
  destruct (HDisplaySound.display_s_aok F K nb n1 false T0 p shb rb cp0 I1 Hp0 Op0 Eb) as [Oshb Orb].
  (* the payload term and the term atom [k] are related *)
  assert (SB : forall s d, nth_error shb s = Some d -> forall x, @catom K (nb + s) x = @ca K d x).
  { intros s0 d Hd0 x; rewrite Hnb, <- Nat.add_assoc.
    assert (Osh_b : Forall (fun d => aok (List.length tenv) d = true) shb)
      by (eapply Forall_impl; [|exact Oshb]; intros d0 H0; apply (proj1 (aok_mono n1 _ L1)), H0).
    rewrite (Ka d) by (rewrite Forall_forall in Osh_b; apply Osh_b, (nth_error_In _ _ Hd0)).
    cbn [K kmodel catom]; f_equal; unfold aden; rewrite app_nth2 by lia.
    replace (List.length aenv + (List.length sh + s0) - List.length aenv) with (List.length sh + s0) by lia.
    destruct (F2_nth _ _ _ (List.length sh + s0) d Hs ltac:(rewrite nth_error_app2 by lia; rewrite Nat.add_comm, Nat.add_sub; exact Hd0))
      as [x0 [Hx0 ->]]; apply nth_error_nth, Hx0. }
  assert (Prem : forall cp, RId T0 p cp ->
            tmrel g (@vden K (CNorm.VTerm u None cp) ridentity) (@vden K (CNorm.VTerm k None []) ridentity)).
  { intros cp Hp; pose proof (proj1 (R_func T0 I1) p _ Hp _ Hp0) as <-.
    pose proof (HDisplaySound.display_s_sound F K nb n1 false T0 p shb rb cp I1 Hp Op0 Eb SB ridentity) as D.
    rewrite (Ka rb (proj1 (aok_mono n1 _ L1) rb Orb)), rcompose_identity_l in D; unfold K in D.
    rewrite !vden_term; cbn [K kmodel cterm]; unfold kterm.
    destruct (nth_error tenv u) as [y|] eqn:Ey; [|apply nth_error_None in Ey; lia].
    rewrite (Hk y eq_refl); change (bden penv None) with (@rpidentity T).
    change (@wden K [] ridentity) with (@ridentity T); rewrite rpcompose_identity.
    right; exists y, (rpcompose (aeden rb) rpidentity); split; [rewrite D; reflexivity|reflexivity]. }
  destruct (paid_matw T0 w _ k u p I1 R1 Hat Fp Prem) as [cw' [Hf [Hm Ho]]].
  destruct (rebuild_spec (replace_paid k w) cw' T0 [] [] w' T1 I1 Hf (RWNil _) Er) as [I2 [X2 R2]].
  rewrite app_nil_r in R2.
  pose proof (Ho n2 (List.length aenv) Lk Oc2) as Ocw'.
  destruct (HDisplaySound.display_s_aok F K (List.length aenv) n2 true T1 (HNorm.wid w') sh r cw' I2
              (RWord_RId _ _ _ R2) Ocw' Hd) as [Osh Or].
  assert (SA : forall s d, nth_error sh s = Some d -> forall x, @catom K (List.length aenv + s) x = @ca K d x).
  { intros s0 d Hd0 x.
    rewrite (Ka d) by (rewrite Forall_forall in Osh; apply (proj1 (aok_mono n2 _ L2)), Osh, (nth_error_In _ _ Hd0)).
    cbn [K kmodel catom]; f_equal; unfold aden; rewrite app_nth2 by lia.
    replace (List.length aenv + s0 - List.length aenv) with s0 by lia.
    destruct (F2_nth _ _ _ s0 d Hs ltac:(rewrite nth_error_app1; [exact Hd0|apply nth_error_Some; rewrite Hd0; discriminate]))
      as [x0 [Hx0 ->]]; apply nth_error_nth, Hx0. }
  pose proof (HDisplaySound.display_sound F K (List.length aenv) n2 T1 (HNorm.wid w') sh r cw' I2
                (RWord_RId _ _ _ R2) Ocw' Hd SA ridentity) as D.
  rewrite (Ka r (proj1 (aok_mono n2 _ L2) r Or)), rcompose_identity_l in D; unfold K in D.
  intros v; rewrite D, <- (kword_meaning lenv tenv (aenv ++ rs) penv l e Hl (proj1 (aok_mono n1 _ L1) e Ae)).
  apply matw_mrel, Hm.
Qed.

End MatShow.

End Show.

(** ** Results with binary indices

    What the tactic reads back from [vm_compute]: a normal form with its
    indices as binary numerals, so that reading it back is linear. *)
Inductive aexpN : Type :=
| NId
| NAtom (n : N)
| NCompose (a b : aexpN)
| NOuter (h : lexp) (a : aexpN)
| NInner (h : lexp) (t : texpN) (a : aexpN)
| NLift (h : lexp) (a : aexpN)
with texpN : Type :=
| NVarE (h : lexp) (i : N)
| NBindE (u : N) (p : pexpN)
| NShiftE (h : lexp) (t : texpN)
| NLookE (h : lexp) (i : N) (a : aexpN)
with pexpN : Type :=
| NPId
| NPAtom (n : N)
| NPComp (a : aexpN) (p : pexpN)
| NPShift (h : lexp) (p : pexpN).

Fixpoint aenc (e : aexp) : aexpN :=
  match e with
  | AId => NId
  | AAtom n => NAtom (N.of_nat n)
  | ACompose a b => NCompose (aenc a) (aenc b)
  | AOuter h a => NOuter h (aenc a)
  | AInner h t a => NInner h (tenc t) (aenc a)
  | ALift h a => NLift h (aenc a)
  end
with tenc (t : texp) : texpN :=
  match t with
  | TVarE h i => NVarE h (N.of_nat i)
  | TBindE u p => NBindE (N.of_nat u) (penc p)
  | TShiftE h t => NShiftE h (tenc t)
  | TLookE h i a => NLookE h (N.of_nat i) (aenc a)
  end
with penc (p : pexp) : pexpN :=
  match p with
  | PId => NPId
  | PAtom n => NPAtom (N.of_nat n)
  | PComp a p => NPComp (aenc a) (penc p)
  | PShift h p => NPShift h (penc p)
  end.

Definition enc_show (x : list aexp * aexp) : list aexpN * aexpN := (map aenc (fst x), aenc (snd x)).
