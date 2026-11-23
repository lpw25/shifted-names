(** * Showing normal forms, proved for the library's adjustments

    [hshow] normalises an expression with [HNorm] and shows the normal
    form ([HDisplay]).  [hshow_sound]: the expression means what it is
    shown as, given that each shared definition's atom is the
    definition. *)

From Stdlib Require Import List Arith Lia Bool PArith NArith FMapPositive.
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

(** ** With shared definitions

    Atoms that [defs] defines stand for their definitions ([Exp]); a
    definition may use only the atoms before it.  [hshowD] normalises
    with [HNorm.normD], each definition once for each word it is
    followed by. *)
Fixpoint defs_ok (n k : nat) (defs : list (option aexp)) : bool :=
  match defs with
  | [] => true
  | od :: ds => (match od with Some d => inp n k d | None => true end) && defs_ok n (S k) ds
  end.

Fixpoint asize (a : aexp) : nat :=
  match a with
  | AId | AAtom _ => 1
  | ACompose a b => S (asize a + asize b)
  | AOuter _ a | ALift _ a => S (asize a)
  | AInner _ t a => S (tsize t + asize a)
  end
with tsize (t : texp) : nat :=
  match t with
  | TVarE _ _ => 1
  | TBindE _ p => S (asize p)
  | TShiftE _ t => S (tsize t)
  | TLookE _ _ a => S (asize a)
  end.

Definition dfuel (defs : list (option aexp)) (e : aexp) : nat :=
  fold_left (fun acc od => match od with Some d => acc + asize d | None => acc end) defs (S (asize e)).

Definition hshowD (F : order) (n base : nat) (defs : list (option aexp)) (e : aexp) : option (list aexp * aexp) :=
  if inp n base e && Nat.eqb (List.length defs) base && defs_ok n 0 defs then
    match HNorm.normD F defs (dfuel defs e) e [] HNorm.st0 (PositiveMap.empty _) with
    | Some (w, T, _) => HDisplay.display F base T (HNorm.wid w)
    | None => None
    end
  else None.

(** The definitions are expanded in range, and expansions exist. *)
Lemma defs_ok_nth n defs : forall j k d, defs_ok n j defs = true -> nth k defs None = Some d -> inp n (j + k) d = true.
Proof.
  induction defs as [|od ds IH]; intros j k d H E; [destruct k; discriminate|].
  cbn [defs_ok] in H; apply andb_true_iff in H as [H1 H2].
  destruct k as [|k]; cbn [nth] in E.
  - subst od; rewrite Nat.add_0_r; exact H1.
  - replace (j + S k) with (S j + k) by lia; apply (IH (S j) k d H2 E).
Qed.

Lemma Exp_range n b defs : (forall k d, nth k defs None = Some d -> CRange.inrange n b d = true /\ aok n d = true) ->
  (forall e e', Exp defs e e' -> CRange.inrange n b e = true -> aok n e = true -> CRange.inrange n b e' = true /\ aok n e' = true)
  /\ (forall t t', TExp defs t t' -> CRange.tinrange n b t = true -> tok n t = true ->
        CRange.tinrange n b t' = true /\ tok n t' = true).
Proof.
  intros Hd; apply ex_mind; intros; cbn [CRange.inrange CRange.tinrange aok tok] in *;
    rewrite ?andb_true_iff in *;
    repeat match goal with E : nth _ defs None = Some _ |- _ => destruct (Hd _ _ E); clear E end;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with
           | H : ?P -> ?Q -> _, H1 : ?P, H2 : ?Q |- _ => specialize (H H1 H2)
           end;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    tauto.
Qed.

Lemma Exp_exists n defs : defs_ok n 0 defs = true -> forall B,
  (forall e, CRange.inrange n B e = true -> exists e', Exp defs e e')
  /\ (forall t, CRange.tinrange n B t = true -> exists t', TExp defs t t').
Proof.
  intros Hd B; induction B as [B IHB] using (well_founded_induction lt_wf).
  apply exp_mind; intros; cbn [CRange.inrange CRange.tinrange] in *; rewrite ?andb_true_iff in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with H : ?P -> exists _, _, H' : ?P |- _ => destruct (H H') as [? ?]; clear H end.
  - eexists; constructor.
  - destruct (nth n0 defs None) as [d|] eqn:E; [|exists (AAtom n0); constructor; exact E].
    apply Nat.ltb_lt in H.
    pose proof (defs_ok_nth n defs 0 n0 d Hd E) as K; unfold inp in K; apply andb_true_iff in K as [_ K].
    destruct (proj1 (IHB n0 H) d K) as [d' Hd']; exists d'; apply (ExRef defs n0 d d' E Hd').
  - eexists; constructor; eassumption.
  - eexists; constructor; eassumption.
  - eexists; constructor; eassumption.
  - eexists; constructor; eassumption.
  - eexists; constructor.
  - eexists; constructor; eassumption.
  - eexists; constructor; eassumption.
  - eexists; constructor; eassumption.
Qed.

Lemma F2_nth {A B} (P : A -> B -> Prop) xs ys s d : Forall2 P xs ys -> nth_error ys s = Some d ->
  exists x, nth_error xs s = Some x /\ P x d.
Proof.
  intros H; revert s; induction H as [|x y xs ys Hxy H IH]; intros [|s] E; cbn in E; try discriminate.
  - injection E as <-; exists x; split; [reflexivity|exact Hxy].
  - apply IH, E.
Qed.

Lemma F2_nth_opt {A B} {P : A -> option B -> Prop} {xs ys} : Forall2 P xs ys -> forall k d, nth k ys None = Some d ->
  exists x, nth_error xs k = Some x /\ P x (Some d).
Proof.
  intros H; induction H as [|x y xs ys Hxy H IH]; intros [|k] d E; cbn in E; try discriminate.
  - subst y; exists x; split; [reflexivity|exact Hxy].
  - apply IH, E.
Qed.

Section Show.

Context {T : Type}.
Variables (lenv : list label) (tenv : list T) (aenv rs : list (radj T)).

Local Notation aeden := (aeden lenv tenv (aenv ++ rs)).

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
  set (K := kmodel lenv tenv (aenv ++ rs)).
  pose proof (kcons lenv tenv (aenv ++ rs) _ (order_of_ok lenv l Hl)) as HM.
  destruct (kden lenv tenv (aenv ++ rs) (List.length tenv) (le_n _)) as [Ka _].
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


(** With shared definitions: each defined atom is its definition. *)
Theorem hshowD_sound l defs e sh r : lfacts_ok lenv l ->
  hshowD (order_of l) (List.length tenv) (List.length aenv) defs e = Some (sh, r) ->
  Forall2 (fun x od => match od with Some d => x = aeden d | None => True end) aenv defs ->
  Forall2 (fun x d => x = aeden d) rs sh ->
  aeden e = aeden r.
Proof.
  intros Hl E Hdefs Hs; unfold hshowD in E.
  destruct (inp (List.length tenv) (List.length aenv) e) eqn:Ie; [|discriminate].
  destruct (Nat.eqb (List.length defs) (List.length aenv)) eqn:Ln; [|discriminate].
  destruct (defs_ok (List.length tenv) 0 defs) eqn:Dk; [|discriminate]; cbn [andb] in E.
  unfold inp in Ie; apply andb_true_iff in Ie as [Ae Ar].
  set (n := List.length tenv) in *; set (B := List.length aenv) in *.
  assert (Hd : forall k d, nth k defs None = Some d -> CRange.inrange n B d = true /\ aok n d = true).
  { intros k d Ek; pose proof (defs_ok_nth n defs 0 k d Dk Ek) as K; unfold inp in K; apply andb_true_iff in K as [K1 K2].
    assert (Lk : k < B).
    { apply Nat.eqb_eq in Ln; rewrite <- Ln; destruct (Nat.lt_ge_cases k (List.length defs)) as [L|L]; [exact L|].
      rewrite nth_overflow in Ek by exact L; discriminate. }
    split; [|exact K1]; refine (proj1 (CRange.inrange_mono n k B _) d K2); lia. }
  destruct (proj1 (Exp_exists n defs Dk B) e Ar) as [e' He].
  destruct (proj1 (Exp_range n B defs Hd) e e' He Ar Ae) as [Ar' Ae'].
  assert (Hm : forall k d, nth k defs None = Some d -> Normalise.aden (aenv ++ rs) k = aeden d).
  { intros k d Ek; unfold Normalise.aden.
    destruct (F2_nth_opt Hdefs k d Ek) as [x [Hx Ex]].
    rewrite app_nth1 by (apply nth_error_Some; rewrite Hx; discriminate).
    rewrite (nth_error_nth _ _ _ Hx); exact Ex. }
  rewrite (proj1 (Exp_meaning lenv tenv (aenv ++ rs) defs Hm) e e' He).
  destruct (HNorm.normD (order_of l) defs (dfuel defs e) e [] HNorm.st0 (PositiveMap.empty _)) as [[[w T0] m0]|] eqn:En;
    [|discriminate].
  pose proof (proj1 (CRange.norm_ok _ _ (order_of l)) e' [] Ar' (Forall_nil _)) as Oc.
  pose proof (order_of_irrefl l lenv Hl) as Hirr; pose proof (order_of_trans l lenv Hl) as Htr.
  set (K := kmodel lenv tenv (aenv ++ rs)).
  pose proof (kcons lenv tenv (aenv ++ rs) _ (order_of_ok lenv l Hl)) as HM.
  destruct (kden lenv tenv (aenv ++ rs) (List.length tenv) (le_n _)) as [Ka _].
  destruct (proj1 (normD_spec (order_of l) Hirr Htr defs (dfuel defs e)) e e' He [] HNorm.st0 (PositiveMap.empty _) []
              w T0 m0 Inv_st0 (RWNil _) (MInv_empty _ defs _) En) as [I1 [_ [_ R1]]].
  destruct (HDisplaySound.display_s_aok (order_of l) K B n true T0
              (HNorm.wid w) sh r _ I1 (RWord_RId _ _ _ R1) Oc E) as [Osh Or].
  assert (HS : forall s d, nth_error sh s = Some d -> forall x, @catom K (B + s) x = @ca K d x).
  { intros s d Hd0 x; rewrite (Ka d) by (rewrite Forall_forall in Osh; apply Osh, (nth_error_In _ _ Hd0)).
    cbn [K kmodel catom]; f_equal; unfold aden; rewrite app_nth2 by lia.
    replace (B + s - List.length aenv) with s by (unfold B; lia).
    destruct (F2_nth _ _ _ s d Hs Hd0) as [x0 [Hx0 ->]]; apply nth_error_nth, Hx0. }
  pose proof (HDisplaySound.display_sound (order_of l) K B n T0 (HNorm.wid w) sh r
                (CNorm.norm (order_of l) e' []) I1 (RWord_RId _ _ _ R1) Oc E HS ridentity) as D.
  rewrite (Ka r Or), rcompose_identity_l in D; rewrite D.
  rewrite (norm_meaning K _ HM), (Ka e' Ae'), rcompose_identity_l; reflexivity.
Qed.

Lemma shares_model l n sh : lfacts_ok lenv l -> n <= List.length tenv ->
  Forall2 (fun x d => x = aeden d) rs sh -> Forall (fun d => aok n d = true) sh ->
  forall s d, nth_error sh s = Some d -> forall x,
    @catom (kmodel lenv tenv (aenv ++ rs)) (List.length aenv + s) x = @ca (kmodel lenv tenv (aenv ++ rs)) d x.
Proof.
  intros Hl Hn Hs Osh s d Hd x.
  destruct (kden lenv tenv (aenv ++ rs) n Hn) as [Ka _].
  rewrite (Ka d) by (rewrite Forall_forall in Osh; apply Osh, (nth_error_In _ _ Hd)).
  cbn [kmodel catom]; f_equal; unfold aden; rewrite app_nth2 by lia.
  replace (List.length aenv + s - List.length aenv) with s by lia.
  destruct (F2_nth _ _ _ s d Hs Hd) as [x0 [Hx0 ->]]; apply nth_error_nth, Hx0.
Qed.

(** ** Where a variable goes

    The normal form of [e] followed from [hᵢ], once: to a variable, to a
    term with its payload (shown), or stuck at [g_j] looked up through
    the rest of the word (shown). *)

Inductive vshow : Type :=
| VSVar (h : lexp) (j : nat)
| VSTerm (u : nat) (s : list aexp * aexp)
| VSLook (g : lexp) (j : nat) (s : list aexp * aexp).

Definition hlook_show (F : order) (n base : nat) (e : aexp) (h : lexp) (i : nat) : option vshow :=
  if inp n base e then
    let '(w, T0) := HNorm.norm F e [] HNorm.st0 in
    match HNorm.lookup F h i w T0 with
    | (HNorm.VVar h' j, _) => Some (VSVar h' j)
    | (HNorm.VTerm u p, T1) => option_map (VSTerm u) (HDisplay.display F base T1 p)
    | (HNorm.VLook g j x, T1) => option_map (VSLook g j) (HDisplay.display F base T1 x)
    end
  else None.

Lemma rapply_target_rename_inj (X Y : radj T) w w' :
  rapply_target X (RRename w) = rapply_target Y (RRename w') -> rapply X w = rapply Y w'.
Proof.
  unfold rapply_target; destruct (rapply X w) as [a|[u ρ]], (rapply Y w') as [a'|[u' ρ']]; intros E;
    try discriminate; injection E; intros; subst; reflexivity.
Qed.

(** The common start of the three proofs: what [follow] gives, related
    to the [CNorm] lookup, whose meaning [klookup] gives. *)
Lemma hlook_show_spec l e h i r : lfacts_ok lenv l ->
  hlook_show (order_of l) (List.length tenv) (List.length aenv) e h i = Some r ->
  exists v T1 cv, RVal T1 v cv /\ Inv T1
    /\ CNorm.lookup (order_of l) h i (CNorm.norm (order_of l) e []) = cv
    /\ CRange.VOk (List.length tenv) (List.length aenv) cv
    /\ rapply_target (aeden e) (RRename (mk_rvar (lden lenv h) i)) = @vden (kmodel lenv tenv (aenv ++ rs)) cv ridentity
    /\ match v with
       | HNorm.VVar h' j => r = VSVar h' j
       | HNorm.VTerm u p => option_map (VSTerm u) (HDisplay.display (order_of l) (List.length aenv) T1 p) = Some r
       | HNorm.VLook g j x => option_map (VSLook g j) (HDisplay.display (order_of l) (List.length aenv) T1 x) = Some r
       end.
Proof.
  intros Hl H; unfold hlook_show, inp in H.
  destruct (aok _ e) eqn:Ha; [|discriminate]; destruct (CRange.inrange _ _ e) eqn:Ar; [|discriminate]; cbn [andb] in H.
  set (F := order_of l) in *.
  destruct (HNorm.norm F e [] HNorm.st0) as [w T0] eqn:En; destruct (HNorm.lookup F h i w T0) as [v T1] eqn:El.
  pose proof (order_of_irrefl l lenv Hl) as Hirr; pose proof (order_of_trans l lenv Hl) as Htr.
  destruct (proj1 (norm_spec_all F Hirr Htr) e [] HNorm.st0 [] w T0 Inv_st0 (RWNil _) En) as [I1 [_ R1]].
  destruct (lookup_spec F Hirr Htr T0 h w _ I1 R1 i _ T1 El) as [I2 [_ R2]].
  pose proof (klookup lenv tenv (aenv ++ rs) l e h i Hl Ha) as Kl; fold F in Kl.
  pose proof (CRange.lookup_ok _ _ F h i _ (proj1 (CRange.norm_ok _ _ F) e [] Ar (Forall_nil _))) as Ov.
  exists v, T1, (CNorm.lookup F h i (CNorm.norm F e [])).
  split; [exact R2|split; [exact I2|split; [reflexivity|split; [exact Ov|split; [symmetry; exact Kl|]]]]].
  destruct v; [injection H as <-|exact H|exact H]; reflexivity.
Qed.

Theorem hlook_show_var l e h i h' j : lfacts_ok lenv l ->
  hlook_show (order_of l) (List.length tenv) (List.length aenv) e h i = Some (VSVar h' j) ->
  rapply (aeden e) (mk_rvar (lden lenv h) i) = inl (mk_rvar (lden lenv h') j).
Proof.
  intros Hl H; destruct (hlook_show_spec l e h i _ Hl H) as [v [T1 [cv [R2 [_ [_ [_ [Kl Hv]]]]]]]].
  destruct v as [g k| |]; [|destruct (HDisplay.display _ _ _ _) as [[? ?]|]; discriminate..].
  injection Hv as <- <-.
  rewrite (RVal_var _ _ _ _ R2), vden_var, kname in Kl; unfold rapply_target in Kl; rewrite rapply_identity in Kl.
  destruct (rapply (aeden e) _) as [u|[u ρ]]; [injection Kl as <-; reflexivity|discriminate].
Qed.

Theorem hlook_show_term l e h i u sh r x : lfacts_ok lenv l ->
  hlook_show (order_of l) (List.length tenv) (List.length aenv) e h i = Some (VSTerm u (sh, r)) ->
  Forall2 (fun y d => y = aeden d) rs sh -> nth_error tenv u = Some x ->
  rapply (aeden e) (mk_rvar (lden lenv h) i) = inr (x, aeden r).
Proof.
  intros Hl H Hs Hx; destruct (hlook_show_spec l e h i _ Hl H) as [v [T1 [cv [R2 [I2 [Ecv [Ov [Kl Hv]]]]]]]].
  destruct v as [|u' p|]; [discriminate| |destruct (HDisplay.display _ _ _ _) as [[? ?]|]; discriminate].
  destruct (HDisplay.display _ _ _ p) as [[sh0 r0]|] eqn:Ed; [|discriminate]; cbn [option_map] in Hv; injection Hv as -> -> ->.
  set (F := order_of l) in *; set (K := kmodel lenv tenv (aenv ++ rs)).
  pose proof (kcons lenv tenv (aenv ++ rs) _ (order_of_ok lenv l Hl)) as HM.
  destruct (kden lenv tenv (aenv ++ rs) (List.length tenv) (le_n _)) as [Ka _].
  destruct (RVal_term _ _ _ _ R2) as [cp [Ecp Rp]]; subst cv; rewrite Ecp in Kl, Ov.
  inversion Ov as [|? ? _ Op|]; subst.
  destruct (HDisplaySound.display_s_aok F K (List.length aenv) (List.length tenv) true T1 p sh r cp I2 Rp Op Ed)
    as [Osh Or].
  pose proof (HDisplaySound.display_sound F K (List.length aenv) (List.length tenv) T1 p sh r cp I2 Rp Op Ed
                (shares_model l _ sh Hl (le_n _) Hs Osh) ridentity) as D.
  rewrite (Ka r Or), rcompose_identity_l in D; unfold K in D.
  rewrite vden_term, <- D in Kl.
  cbn [K kmodel cterm] in Kl; unfold kterm in Kl; rewrite Hx in Kl; unfold rapply_target in Kl.
  destruct (rapply (aeden e) _) as [w'|[u' ρ]]; [discriminate|injection Kl as -> ->; reflexivity].
Qed.

Theorem hlook_show_look l e h i g j sh r : lfacts_ok lenv l ->
  hlook_show (order_of l) (List.length tenv) (List.length aenv) e h i = Some (VSLook g j (sh, r)) ->
  Forall2 (fun y d => y = aeden d) rs sh ->
  rapply (aeden e) (mk_rvar (lden lenv h) i) = rapply (aeden r) (mk_rvar (lden lenv g) j).
Proof.
  intros Hl H Hs; destruct (hlook_show_spec l e h i _ Hl H) as [v [T1 [cv [R2 [I2 [Ecv [Ov [Kl Hv]]]]]]]].
  destruct v as [| |g' j' x]; [discriminate|destruct (HDisplay.display _ _ _ _) as [[? ?]|]; discriminate|].
  destruct (HDisplay.display _ _ _ x) as [[sh0 r0]|] eqn:Ed; [|discriminate]; cbn [option_map] in Hv; injection Hv as -> -> -> ->.
  set (F := order_of l) in *; set (K := kmodel lenv tenv (aenv ++ rs)).
  pose proof (kcons lenv tenv (aenv ++ rs) _ (order_of_ok lenv l Hl)) as HM.
  destruct (kden lenv tenv (aenv ++ rs) (List.length tenv) (le_n _)) as [Ka _].
  assert (Ecx : exists cx, cv = CNorm.VLook g j cx /\ RId T1 x cx)
    by (inversion R2; subst; eexists; split; [reflexivity|eassumption]).
  destruct Ecx as [cx [-> Hx]].
  inversion Ov as [| |? ? ? Ox]; subst.
  destruct (HDisplaySound.display_s_aok F K (List.length aenv) (List.length tenv) true T1 x sh r cx I2 Hx Ox Ed)
    as [Osh Or].
  pose proof (HDisplaySound.display_sound F K (List.length aenv) (List.length tenv) T1 x sh r cx I2 Hx Ox Ed
                (shares_model l _ sh Hl (le_n _) Hs Osh) ridentity) as D.
  rewrite (Ka r Or), rcompose_identity_l in D; unfold K in D.
  rewrite vden_look, kname, <- D in Kl.
  apply rapply_target_rename_inj, Kl.
Qed.

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
| NBindE (u : N) (p : aexpN)
| NShiftE (h : lexp) (t : texpN)
| NLookE (h : lexp) (i : N) (a : aexpN).

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
  | TBindE u p => NBindE (N.of_nat u) (aenc p)
  | TShiftE h t => NShiftE h (tenc t)
  | TLookE h i a => NLookE h (N.of_nat i) (aenc a)
  end.

Definition enc_show (x : list aexp * aexp) : list aexpN * aexpN := (map aenc (fst x), aenc (snd x)).
