(** * The display means the word

    [HDisplay.display] turns a normal form into an expression with
    shared definitions.  Here: in every comprehension model consistent
    with the facts, the expression means the word, given that each
    shared definition's atom means the definition ([display_sound]).

    Each cell is shown from its step and the rest of its word; the proof
    reads words off the table as [HRefine] does ([RId]), with references
    to shared definitions read through an environment [ρ] that agrees
    with the cells shown before them. *)

From Stdlib Require Import List PArith NArith Bool FMapPositive Arith Lia.
From ShiftedNames.Core Require Import Label Normalise KnownOrder Comp CSound HRefine HConcrete.
From ShiftedNames.Core Require HNorm CNorm HDisplay CRange.
Import ListNotations.

Section Sound.

Variable F : order.
Variable M : cmodel.

Local Notation U := (cU M).
Local Notation wden := (@wden M).
Local Notation vden := (@vden M).
Local Notation sden := (@sden M).
Local Notation wpre := (CSound.wpre M).

(** Term atoms below [nt], adjustment atoms below [base]: what is read
    off the normal form is in range ([CRange]). *)
Variables (base nt : nat).
Local Notation WOk := (CRange.WOk nt base).
Local Notation SOk := (CRange.SOk nt base).
Local Notation VOk := (CRange.VOk nt base).

Lemma WOk_cons s w : WOk (s :: w) <-> SOk s /\ WOk w.
Proof. split; [intros H; inversion H; split; assumption|intros [H1 H2]; constructor; assumption]. Qed.

(** ** Reading cells *)

Lemma RId_func T i cw cw' : Inv T -> RId T i cw -> RId T i cw' -> cw = cw'.
Proof. intros I H1 H2; apply (proj1 (R_func T I) i cw H1 cw' H2). Qed.

Lemma RId_cell T i s t cw : Inv T -> HDisplay.cell T i = Some (s, t) -> RId T i cw ->
  exists cs ct, cw = cs :: ct /\ RStep T s cs /\ RId T t ct.
Proof.
  intros I E H; unfold HDisplay.cell in E; fold (cellof T i) in E.
  inversion H as [|i0 s0 t0 cs ct Hc Hs Ht]; subst; [destruct (inv_next T I 1 _ E) as [_ N]; contradiction|].
  rewrite E in Hc; injection Hc as <- <-; exists cs, ct; auto.
Qed.

Lemma RId_nocell T i cw : HDisplay.cell T i = None -> RId T i cw -> cw = [].
Proof.
  intros E H; unfold HDisplay.cell in E; fold (cellof T i) in E.
  inversion H as [|i0 s0 t0 cs ct Hc]; subst; [reflexivity|rewrite E in Hc; discriminate].
Qed.

(** ** Showing cells *)

(** References to shared definitions, [base + k], read through [ρ]. *)
Definition upd (ρ : nat -> U -> U) : cmodel :=
  mk_cmodel U (cA M) (@cpop M) (@chd M) (@cpush M) (cpop_push M) (chd_push M) (cpush_pop M)
    (fun n x => if Nat.leb base n then ρ (n - base) x else catom n x) (@cterm M).

Definition dden (ρ : nat -> U -> U) (d : aexp) (c : U) : U := @ca (upd ρ) d c.

Lemma dden_acomp ρ r x c : dden ρ (HDisplay.acomp r x) c = dden ρ x (dden ρ r c).
Proof. destruct r; reflexivity. Qed.

Lemma dden_atom_real ρ a (Y : U) : a < base -> dden ρ (AAtom a) Y = catom a Y.
Proof.
  intros L; unfold dden; cbn [ca upd catom].
  replace (Nat.leb base a) with false by (symmetry; apply Nat.leb_gt, L); reflexivity.
Qed.

Lemma dden_ref ρ k (Y : U) : dden ρ (AAtom (base + k)) Y = ρ k Y.
Proof.
  unfold dden; cbn [ca upd catom].
  replace (Nat.leb base (base + k)) with true by (symmetry; apply Nat.leb_le; lia).
  replace (base + k - base) with k by lia; reflexivity.
Qed.

(** All atoms below [n]: real atoms below [base], references below [n]. *)
Fixpoint alt (n : nat) (d : aexp) : Prop :=
  match d with
  | AId => True
  | AAtom a => a < n
  | ACompose a b => alt n a /\ alt n b
  | AOuter _ a | ALift _ a => alt n a
  | AInner _ t a => tlt n t /\ alt n a
  end
with tlt (n : nat) (t : texp) : Prop :=
  match t with
  | TVarE _ _ => True
  | TBindE _ p => alt n p
  | TShiftE _ t => tlt n t
  | TLookE _ _ a => alt n a
  end.

Lemma alt_mono n n' : n <= n' ->
  (forall d, alt n d -> alt n' d) /\ (forall t, tlt n t -> tlt n' t).
Proof. intros L; apply exp_mind; cbn; intros; try tauto; lia. Qed.

Lemma alt_acomp n r x : alt n r -> alt n x -> alt n (HDisplay.acomp r x).
Proof. destruct r; cbn; tauto. Qed.

Lemma aok_acomp r x : aok nt r = true -> aok nt x = true -> aok nt (HDisplay.acomp r x) = true.
Proof. intros H1 H2; destruct r; cbn [HDisplay.acomp aok] in *; rewrite ?H1, ?H2; try reflexivity; exact H2. Qed.

(** ** Runs of entries *)

Definition sform_c (ts : list (lexp * nat)) : CNorm.cword :=
  map (fun '(h, u) => CNorm.SE h (CNorm.VTerm u [])) ts.

Lemma wden_wpre w (x : U) : wden w x = wpre w x x.
Proof. induction w as [|t w IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma sform_wpre ts cp (c Z : U) :
  wpre (map (fun '(h, u) => CNorm.SE h (CNorm.VTerm u cp)) ts) Z c = wpre (sform_c ts) Z (wden cp c).
Proof.
  induction ts as [|[h u] ts IH]; cbn [map CSound.wpre sform_c]; [reflexivity|].
  rewrite IH; cbn [sden]; rewrite !CSound.vden_term; reflexivity.
Qed.

Lemma lead_pay_spec T p cp : Inv T -> RId T p cp -> forall fuel j cj ts, RId T j cj ->
  HDisplay.lead_pay T fuel j p = Some ts ->
  cj = map (fun '(h, u) => CNorm.SE h (CNorm.VTerm u cp)) ts ++ cp.
Proof.
  intros I Hp; induction fuel as [|f IH]; intros j cj ts Hj E; cbn [HDisplay.lead_pay] in E; [discriminate|].
  destruct (Pos.eqb j p) eqn:Ej.
  - injection E as <-; apply Pos.eqb_eq in Ej; subst j; cbn; apply (RId_func T p _ _ I Hj Hp).
  - unfold HDisplay.cell in E; fold (cellof T j) in E.
    destruct (cellof T j) as [[[h [g k|u q|g k x]|h|a] t]|] eqn:Ec; try discriminate.
    destruct (Pos.eqb q p) eqn:Eq; [|discriminate]; apply Pos.eqb_eq in Eq; subst q.
    destruct (HDisplay.lead_pay T f t p) as [ts'|] eqn:E1; [|discriminate]; injection E as <-.
    inversion Hj as [|j0 s t0 cs cw Hc Hs Ht]; subst; [destruct (inv_next T I 1 _ Ec) as [_ N]; contradiction|].
    rewrite Ec in Hc; injection Hc as <- <-.
    inversion Hs as [h0 v0 cv Hv| |]; subst; inversion Hv as [|u1 p1 cq Hq|]; subst.
    rewrite (RId_func T p _ _ I Hq Hp), (IH t cw ts' Ht E1); reflexivity.
Qed.

Lemma dden_sform ρ ts (Y : U) : dden ρ (HDisplay.sform ts) Y = wden (sform_c ts) Y.
Proof.
  induction ts as [|[h u] ts IH]; [reflexivity|].
  change (cpush h (dden ρ (HDisplay.sform ts) Y) (cterm u Y)
          = cpush h (wden (sform_c ts) Y) (vden (CNorm.VTerm u []) Y)).
  rewrite IH, CSound.vden_term; reflexivity.
Qed.

Lemma alt_sform n ts : alt n (HDisplay.sform ts).
Proof. induction ts as [|[h u] ts IH]; cbn; tauto. Qed.

Lemma aok_sform ts : Forall (fun hu => snd hu < nt) ts -> aok nt (HDisplay.sform ts) = true.
Proof.
  induction ts as [|[h u] ts IH]; intros H; [reflexivity|]; inversion H; subst; cbn in *.
  apply andb_true_iff; split; [apply andb_true_iff; split; [apply Nat.ltb_lt; assumption|reflexivity]|apply IH; assumption].
Qed.

Lemma WOk_app w1 w2 : WOk (w1 ++ w2) <-> WOk w1 /\ WOk w2.
Proof. unfold CRange.WOk; rewrite Forall_app; tauto. Qed.

(** A run read off the cells: its entries, and what the word means. *)
Lemma run_spec T fuel i ci ts p : Inv T -> RId T i ci -> WOk ci ->
  HDisplay.lead_pay T fuel i p = Some ts ->
  exists cp, RId T p cp /\ WOk cp /\ Forall (fun hu => snd hu < nt) ts /\
    forall c, wden ci c = wden (sform_c ts) (wden cp c).
Proof.
  intros I Hi Oi E.
  assert (Hp : exists cp, RId T p cp).
  { clear Oi; revert i ci ts Hi E; induction fuel as [|f IH]; intros i ci ts Hi E; cbn [HDisplay.lead_pay] in E; [discriminate|].
    destruct (Pos.eqb i p) eqn:Ei; [apply Pos.eqb_eq in Ei; subst; exists ci; exact Hi|].
    unfold HDisplay.cell in E; fold (cellof T i) in E.
    destruct (cellof T i) as [[[h [g k|u q|g k x]|h|a] t]|] eqn:Ec; try discriminate.
    destruct (Pos.eqb q p); [|discriminate].
    destruct (HDisplay.lead_pay T f t p) as [ts'|] eqn:E1; [|discriminate].
    inversion Hi as [|j0 s t0 cs cw Hc Hs Ht]; subst; [destruct (inv_next T I 1 _ Ec) as [_ N]; contradiction|].
    rewrite Ec in Hc; injection Hc as <- <-; apply (IH t cw ts' Ht E1). }
  destruct Hp as [cp Hp].
  pose proof (lead_pay_spec T p cp I Hp fuel i ci ts Hi E) as Eci.
  rewrite Eci in Oi; apply WOk_app in Oi as [Oe Oq].
  exists cp; split; [exact Hp|split; [exact Oq|split]].
  - clear Eci E; revert Oe; induction ts as [|[h1 u1] l IHl]; intros Oe; [constructor|].
    cbn in Oe; apply WOk_cons in Oe as [O1 Oe]; constructor; [|apply IHl, Oe].
    inversion O1 as [? ? Ov| |]; subst; inversion Ov; subst; assumption.
  - intros c; rewrite Eci, CSound.wden_app, sform_wpre; symmetry; apply wden_wpre.
Qed.

Section Cells.

Variable T : HNorm.st.
Hypothesis I : Inv T.
Variables (shr : bool) (cnt : PositiveMap.t nat) (grp : PositiveMap.t positive).

Local Notation dref := (HDisplay.dref T base shr cnt grp).
Local Notation dbody := (HDisplay.dbody T base shr cnt grp).
Local Notation dval := (HDisplay.dval T base shr cnt grp).

(** An environment agrees with the shared definitions before [n]. *)
Definition Agree (D : HDisplay.dstate) (ρ : nat -> U -> U) (n : nat) : Prop :=
  forall k i d, nth_error (rev (HDisplay.ddefs D)) k = Some (i, d) -> k < n ->
    forall ci, RId T i ci -> forall c, ρ k c = wden ci c.

(** What a cell is shown as means its word. *)
Definition Shows (D : HDisplay.dstate) (n : nat) (i : positive) (r : aexp) : Prop :=
  alt (base + n) r /\ aok nt r = true /\
  forall ρ, Agree D ρ n -> forall ci, RId T i ci -> forall c, dden ρ r c = wden ci c.

Record DInv (D : HDisplay.dstate) : Prop := {
  di_len : length (HDisplay.ddefs D) = HDisplay.dn D;
  di_defs : forall k i d, nth_error (rev (HDisplay.ddefs D)) k = Some (i, d) -> Shows D k i d;
  di_memo : forall i r, PositiveMap.find i (HDisplay.dmemo D) = Some r -> Shows D (HDisplay.dn D) i r
}.

Definition DExt (D D' : HDisplay.dstate) : Prop :=
  (forall i r, PositiveMap.find i (HDisplay.dmemo D) = Some r -> PositiveMap.find i (HDisplay.dmemo D') = Some r) /\
  HDisplay.dn D <= HDisplay.dn D' /\
  (forall k x, nth_error (rev (HDisplay.ddefs D)) k = Some x -> nth_error (rev (HDisplay.ddefs D')) k = Some x).

Lemma DExt_refl D : DExt D D.
Proof. split; [auto|split; auto]. Qed.

Lemma DExt_trans D1 D2 D3 : DExt D1 D2 -> DExt D2 D3 -> DExt D1 D3.
Proof. intros [M1 [N1 L1]] [M2 [N2 L2]]; split; [auto|split; [lia|auto]]. Qed.

Lemma Agree_mono D D' ρ n n' : DExt D D' -> n <= n' -> Agree D' ρ n' -> Agree D ρ n.
Proof. intros [_ [_ L]] Ln A k i d E Lk; apply (A k i d (L _ _ E)); lia. Qed.

Lemma Shows_mono D D' n n' i r : DExt D D' -> n <= n' -> Shows D n i r -> Shows D' n' i r.
Proof.
  intros X Ln [Ar [Kr Sr]]; split; [apply (proj1 (alt_mono (base + n) (base + n') ltac:(lia))), Ar|split; [exact Kr|]].
  intros ρ A; apply Sr, (Agree_mono D D' ρ n n' X Ln A).
Qed.

(** A memo entry that is not a shared definition. *)
Lemma memo_spec D i d : DInv D -> PositiveMap.find i (HDisplay.dmemo D) = None -> Shows D (HDisplay.dn D) i d ->
  let D' := HDisplay.mk_dstate (PositiveMap.add i d (HDisplay.dmemo D)) (HDisplay.ddefs D) (HDisplay.dn D) in
  DInv D' /\ DExt D D'.
Proof.
  intros [L Ds Ms] N Sd D'.
  assert (X : DExt D D') by (split; [intros i' r E; cbn; rewrite PositiveMap.gso by congruence; exact E|split; cbn; auto]).
  split; [|exact X]; constructor; cbn [D' HDisplay.ddefs HDisplay.dn HDisplay.dmemo]; [exact L| |].
  - intros k i' d' E; apply (Shows_mono D D' k k i' d' X (le_n _)), Ds, E.
  - intros i' r E; destruct (Pos.eq_dec i' i) as [->|Ni].
    + rewrite PositiveMap.gss in E; injection E as <-; apply (Shows_mono D D' _ _ i d X (le_n _) Sd).
    + rewrite PositiveMap.gso in E by exact Ni; apply (Shows_mono D D' _ _ i' r X (le_n _)), Ms, E.
Qed.

(** A new shared definition. *)
Lemma share_spec D i d : DInv D -> PositiveMap.find i (HDisplay.dmemo D) = None -> Shows D (HDisplay.dn D) i d ->
  let r := AAtom (base + HDisplay.dn D) in
  let D' := HDisplay.mk_dstate (PositiveMap.add i r (HDisplay.dmemo D)) ((i, d) :: HDisplay.ddefs D) (S (HDisplay.dn D)) in
  DInv D' /\ DExt D D' /\ Shows D' (HDisplay.dn D') i r.
Proof.
  intros [L Ds Ms] N Sd r D'.
  assert (Lr : length (rev (HDisplay.ddefs D)) = HDisplay.dn D) by (rewrite length_rev; exact L).
  assert (Old : forall k x, nth_error (rev (HDisplay.ddefs D)) k = Some x -> nth_error (rev (HDisplay.ddefs D')) k = Some x).
  { intros k x E; cbn [D' HDisplay.ddefs rev]; rewrite nth_error_app1; [exact E|].
    apply nth_error_Some; rewrite E; discriminate. }
  assert (New : nth_error (rev (HDisplay.ddefs D')) (HDisplay.dn D) = Some (i, d)).
  { cbn [D' HDisplay.ddefs rev]; rewrite nth_error_app2 by lia; rewrite Lr, Nat.sub_diag; reflexivity. }
  assert (X : DExt D D') by (split; [intros i' r' E; cbn; rewrite PositiveMap.gso by congruence; exact E|split; [cbn; lia|exact Old]]).
  assert (Sr : Shows D' (HDisplay.dn D') i r).
  { split; [cbn; lia|split; [reflexivity|]].
    intros ρ A ci H c; unfold r; rewrite dden_ref; apply (A _ i d New); [cbn; lia|exact H]. }
  split; [|split; [exact X|exact Sr]].
  constructor; cbn [D' HDisplay.ddefs HDisplay.dn HDisplay.dmemo]; [cbn; rewrite L; reflexivity| |].
  - intros k i' d' E; destruct (Nat.lt_ge_cases k (HDisplay.dn D)) as [Lk|Lk].
    + assert (E0 : nth_error (rev (HDisplay.ddefs D)) k = Some (i', d')).
      { cbn [rev] in E; rewrite nth_error_app1 in E by lia; exact E. }
      apply (Shows_mono D D' k k i' d' X (le_n _)), Ds, E0.
    + assert (Ek : k = HDisplay.dn D).
      { apply Nat.le_antisymm; [|exact Lk]; apply Nat.lt_succ_r.
        replace (S (HDisplay.dn D)) with (length (rev (HDisplay.ddefs D'))) by (rewrite length_rev; cbn; lia).
        apply nth_error_Some; change (rev ((i, d) :: HDisplay.ddefs D)) with (rev (HDisplay.ddefs D')) in E; rewrite E; discriminate. }
      subst k; change (rev ((i, d) :: HDisplay.ddefs D)) with (rev (HDisplay.ddefs D')) in E; rewrite New in E.
      injection E as <- <-; apply (Shows_mono D D' _ _ i d X (le_n _) Sd).
  - intros i' r' E; destruct (Pos.eq_dec i' i) as [->|Ni].
    + rewrite PositiveMap.gss in E; injection E as <-; exact Sr.
    + rewrite PositiveMap.gso in E by exact Ni; apply (Shows_mono D D' _ _ i' r' X (le_S _ _ (le_n _))), Ms, E.
Qed.

Lemma dref_S f i D : dref (S f) i D =
  match PositiveMap.find i (HDisplay.dmemo D) with
  | Some r => Some (r, D)
  | None =>
      match dbody f i D with
      | Some (d, D1) =>
          match PositiveMap.find i (HDisplay.dmemo D1) with
          | Some r => Some (r, D1)
          | None =>
              if HDisplay.many cnt i then
                if shr && negb (HDisplay.trivial d) then
                  Some (AAtom (base + HDisplay.dn D1),
                        HDisplay.mk_dstate (PositiveMap.add i (AAtom (base + HDisplay.dn D1)) (HDisplay.dmemo D1))
                          ((i, d) :: HDisplay.ddefs D1) (S (HDisplay.dn D1)))
                else Some (d, HDisplay.mk_dstate (PositiveMap.add i d (HDisplay.dmemo D1)) (HDisplay.ddefs D1) (HDisplay.dn D1))
              else Some (d, D1)
          end
      | None => None
      end
  end.
Proof. reflexivity. Qed.

Lemma dbody_S f i D : dbody (S f) i D =
  match HDisplay.cell T i with
  | None => Some (AId, D)
  | Some (HNorm.SA a, t) => match dref f t D with Some (r, D1) => Some (HDisplay.acomp r (AAtom a), D1) | None => None end
  | Some (HNorm.SW h, t) => match dref f t D with Some (r, D1) => Some (HDisplay.acomp r (AOuter h AId), D1) | None => None end
  | Some (HNorm.SE h v, t) =>
      match match PositiveMap.find i grp with
            | Some p => match HDisplay.lead_pay T f i p with Some ((_ :: _) as ts) => Some (ts, p) | _ => None end
            | None => None end with
      | Some (ts, p) => match dref f p D with Some (r, D1) => Some (HDisplay.acomp r (HDisplay.sform ts), D1) | None => None end
      | None =>
          match dval f v D with
          | Some (tv, D1) => match dref f t D1 with Some (r, D2) => Some (AInner h tv r, D2) | None => None end
          | None => None
          end
      end
  end.
Proof. reflexivity. Qed.

Lemma dval_S f v D : dval (S f) v D =
  match v with
  | HNorm.VVar g j => Some (TVarE g j, D)
  | HNorm.VTerm u p => match dref f p D with Some (r, D1) => Some (TBindE u r, D1) | None => None end
  | HNorm.VLook g j x => match dref f x D with Some (r, D1) => Some (TLookE g j r, D1) | None => None end
  end.
Proof. reflexivity. Qed.

Lemma disp_spec : forall fuel,
  (forall i D r D', DInv D -> (exists ci, RId T i ci /\ WOk ci) -> dref fuel i D = Some (r, D') ->
     DInv D' /\ DExt D D' /\ Shows D' (HDisplay.dn D') i r)
  /\ (forall i D r D', DInv D -> (exists ci, RId T i ci /\ WOk ci) -> dbody fuel i D = Some (r, D') ->
     DInv D' /\ DExt D D' /\ Shows D' (HDisplay.dn D') i r)
  /\ (forall v cv D t D', DInv D -> RVal T v cv -> VOk cv -> dval fuel v D = Some (t, D') ->
     DInv D' /\ DExt D D' /\ tlt (base + HDisplay.dn D') t /\ tok nt t = true /\
     forall ρ, Agree D' ρ (HDisplay.dn D') -> forall c, @ct (upd ρ) t c = vden cv c).
Proof.
  induction fuel as [|f IH]; [repeat split; intros; discriminate|].
  destruct IH as [IHr [IHb IHv]]; split; [|split].
  - (* dref *)
    intros i D r D' DI Hi E; rewrite dref_S in E.
    destruct (PositiveMap.find i (HDisplay.dmemo D)) as [r0|] eqn:Fm.
    + injection E as <- <-; split; [exact DI|split; [apply DExt_refl|apply (di_memo D DI i r0 Fm)]].
    + destruct (dbody f i D) as [[d D1]|] eqn:Eb; [|discriminate].
      destruct (IHb i D d D1 DI Hi Eb) as [DI1 [X1 Sd]].
      destruct (PositiveMap.find i (HDisplay.dmemo D1)) as [r1|] eqn:Fm1.
      * injection E as <- <-; split; [exact DI1|split; [exact X1|apply (di_memo D1 DI1 i r1 Fm1)]].
      * destruct (HDisplay.many cnt i); [destruct (shr && negb (HDisplay.trivial d))|].
        -- injection E as <- <-; destruct (share_spec D1 i d DI1 Fm1 Sd) as [DI2 [X2 S2]].
           split; [exact DI2|split; [apply (DExt_trans _ _ _ X1 X2)|exact S2]].
        -- injection E as <- <-; destruct (memo_spec D1 i d DI1 Fm1 Sd) as [DI2 X2].
           split; [exact DI2|split; [apply (DExt_trans _ _ _ X1 X2)|apply (Shows_mono D1 _ _ _ i d X2 (le_n _) Sd)]].
        -- injection E as <- <-; split; [exact DI1|split; [exact X1|exact Sd]].
  - (* dbody *)
    intros i D r D' DI [ci [Hi Oi]] E; rewrite dbody_S in E.
    destruct (HDisplay.cell T i) as [[s t]|] eqn:Ec.
    2:{ injection E as <- <-; split; [exact DI|split; [apply DExt_refl|split; [exact Logic.I|split; [reflexivity|]]]].
        intros ρ A ci' H c; rewrite (RId_nocell T i ci' Ec H); reflexivity. }
    destruct (RId_cell T i s t ci I Ec Hi) as [cs [cw0 [-> [Hs Ht]]]].
    apply WOk_cons in Oi as [Os Ot].
    assert (Same : forall ci', RId T i ci' -> ci' = cs :: cw0) by (intros ci' H; apply (RId_func T i _ _ I H Hi)).
    destruct s as [h v|h|a].
    + destruct (match PositiveMap.find i grp with
                | Some p => match HDisplay.lead_pay T f i p with Some ((_ :: _) as ts) => Some (ts, p) | _ => None end
                | None => None end) as [[ts p]|] eqn:Eg.
      { destruct (PositiveMap.find i grp) as [p0|]; [|discriminate].
        destruct (HDisplay.lead_pay T f i p0) as [[|t0 ts0]|] eqn:El; try discriminate; injection Eg as <- <-.
        assert (Oi : WOk (cs :: cw0)) by (apply WOk_cons; split; assumption).
        destruct (run_spec T f i _ _ _ I Hi Oi El) as [cp [Hp [Op [Ots Sem]]]].
        destruct (dref f p0 D) as [[r1 D1]|] eqn:Er; [|discriminate]; injection E as <- <-.
        destruct (IHr p0 D r1 D1 DI (ex_intro _ cp (conj Hp Op)) Er) as [DI1 [X1 [A1 [K1 S1]]]].
        split; [exact DI1|split; [exact X1|split; [exact (alt_acomp _ _ _ A1 (alt_sform _ (t0 :: ts0)))|split; [exact (aok_acomp _ _ K1 (aok_sform (t0 :: ts0) Ots))|]]]].
        intros ρ A ci' H c; rewrite (Same ci' H), Sem, dden_acomp, (S1 ρ A cp Hp c); apply (dden_sform ρ (t0 :: ts0)). }
      inversion Hs as [h0 v0 cv Hv| |]; subst; inversion Os as [? ? Ov| |]; subst.
      destruct (dval f v D) as [[tv D1]|] eqn:Ev; [|discriminate].
      destruct (IHv v cv D tv D1 DI Hv Ov Ev) as [DI1 [X1 [At [Kt St]]]].
      destruct (dref f t D1) as [[r1 D2]|] eqn:Er; [|discriminate]; injection E as <- <-.
      destruct (IHr t D1 r1 D2 DI1 (ex_intro _ cw0 (conj Ht Ot)) Er) as [DI2 [X2 [A1 [K1 S1]]]].
      split; [exact DI2|split; [apply (DExt_trans _ _ _ X1 X2)|split]].
      * cbn; split; [|exact A1].
        apply (proj2 (alt_mono (base + HDisplay.dn D1) (base + HDisplay.dn D2) ltac:(pose proof (proj1 (proj2 X2)); lia))), At.
      * split; [cbn [aok]; rewrite Kt, K1; reflexivity|].
        intros ρ A ci' H c; rewrite (Same ci' H).
        change (cpush h (dden ρ r1 c) (@ct (upd ρ) tv c) = cpush h (wden cw0 c) (vden cv c)).
        rewrite (S1 ρ A cw0 Ht c), (St ρ (Agree_mono D1 D2 ρ _ _ X2 (proj1 (proj2 X2)) A) c); reflexivity.
    + inversion Hs; subst.
      destruct (dref f t D) as [[r1 D1]|] eqn:Er; [|discriminate]; injection E as <- <-.
      destruct (IHr t D r1 D1 DI (ex_intro _ cw0 (conj Ht Ot)) Er) as [DI1 [X1 [A1 [K1 S1]]]].
      split; [exact DI1|split; [exact X1|split; [apply alt_acomp; [exact A1|exact Logic.I]|split; [apply aok_acomp; [exact K1|reflexivity]|]]]].
      intros ρ A ci' H c; rewrite (Same ci' H), dden_acomp, (S1 ρ A cw0 Ht c); reflexivity.
    + inversion Hs; subst; inversion Os as [| |? La]; subst.
      destruct (dref f t D) as [[r1 D1]|] eqn:Er; [|discriminate]; injection E as <- <-.
      destruct (IHr t D r1 D1 DI (ex_intro _ cw0 (conj Ht Ot)) Er) as [DI1 [X1 [A1 [K1 S1]]]].
      split; [exact DI1|split; [exact X1|split; [apply alt_acomp; [exact A1|cbn; lia]|split; [apply aok_acomp; [exact K1|reflexivity]|]]]].
      intros ρ A ci' H c; rewrite (Same ci' H), dden_acomp, dden_atom_real by exact La.
      rewrite (S1 ρ A cw0 Ht c); reflexivity.
  - (* dval *)
    intros v cv D t D' DI Hv Ov E; rewrite dval_S in E.
    destruct v as [g j|u p|g j x].
    + injection E as <- <-; inversion Hv; subst.
      split; [exact DI|split; [apply DExt_refl|split; [exact Logic.I|split; [reflexivity|intros; reflexivity]]]].
    + inversion Hv as [|u0 p0 cp Hp|]; subst; inversion Ov as [|? ? Lu Op|]; subst.
      destruct (dref f p D) as [[r1 D1]|] eqn:Er; [|discriminate]; injection E as <- <-.
      destruct (IHr p D r1 D1 DI (ex_intro _ cp (conj Hp Op)) Er) as [DI1 [X1 [A1 [K1 S1]]]].
      split; [exact DI1|split; [exact X1|split; [exact A1|split]]].
      * cbn [tok]; rewrite K1; apply andb_true_iff; split; [apply Nat.ltb_lt, Lu|reflexivity].
      * intros ρ A c; rewrite CSound.vden_term; change (cterm u (dden ρ r1 c) = cterm u (wden cp c)).
        rewrite (S1 ρ A cp Hp); reflexivity.
    + inversion Hv as [| |g0 j0 x0 cx Hx]; subst; inversion Ov as [| |? ? ? Ox]; subst.
      destruct (dref f x D) as [[r1 D1]|] eqn:Er; [|discriminate]; injection E as <- <-.
      destruct (IHr x D r1 D1 DI (ex_intro _ cx (conj Hx Ox)) Er) as [DI1 [X1 [A1 [K1 S1]]]].
      split; [exact DI1|split; [exact X1|split; [exact A1|split; [exact K1|]]]].
      intros ρ A c; rewrite CSound.vden_look; change (cname g j (dden ρ r1 c) = cname g j (wden cx c)).
      rewrite (S1 ρ A cx Hx); reflexivity.
Qed.

Lemma DInv_start : DInv HDisplay.dstart.
Proof.
  constructor; cbn; [reflexivity|intros k i d E; destruct k; discriminate|].
  intros i r E; rewrite PositiveMap.gempty in E; discriminate.
Qed.

End Cells.

(** ** Renesting *)

Lemma lassoc_ca (N : cmodel) :
  (forall d (c : cU N), @ca N (HDisplay.lassoc d) c = @ca N d c
                        /\ forall y, @ca N (HDisplay.lassoc_to d y) c = @ca N y (@ca N d c))
  /\ (forall t (c : cU N), @ct N (HDisplay.tlassoc t) c = @ct N t c).
Proof.
  apply exp_mind; intros; cbn [HDisplay.lassoc HDisplay.lassoc_to HDisplay.tlassoc];
    repeat match goal with H : forall c : cU N, _ /\ _ |- _ =>
             let H1 := fresh "H" in let H2 := fresh "H" in
             assert (H1 := fun c => proj1 (H c)); assert (H2 := fun c => proj2 (H c)); clear H; cbn beta in H1, H2 end;
    repeat split; intros; cbn [ca ct]; try reflexivity;
    repeat match goal with
           | H : forall (_ : cU N) (_ : aexp), _ = _ |- _ => progress rewrite H
           | H : forall _ : cU N, _ = _ |- _ => progress rewrite H
           end; reflexivity.
Qed.

Lemma lassoc_aok :
  (forall d, aok nt d = true -> aok nt (HDisplay.lassoc d) = true
             /\ forall y, aok nt y = true -> aok nt (HDisplay.lassoc_to d y) = true)
  /\ (forall t, tok nt t = true -> tok nt (HDisplay.tlassoc t) = true).
Proof.
  apply exp_mind; intros; cbn [HDisplay.lassoc HDisplay.lassoc_to HDisplay.tlassoc aok tok] in *;
    rewrite ?andb_true_iff in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with H : ?P -> _, H' : ?P |- _ => specialize (H H') end;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; intros; cbn [aok tok]; rewrite ?andb_true_iff; repeat split; eauto.
Qed.

(** ** The display means the word *)

(** Reading references through the model's own atoms. *)
Lemma dden_real ρ : (forall k x, ρ k x = catom (base + k) x) ->
  (forall d (c : U), dden ρ d c = @ca M d c)
  /\ (forall t (c : U), @ct (upd ρ) t c = @ct M t c).
Proof.
  intros Hρ; unfold dden; apply exp_mind; intros; simpl; try reflexivity;
    [destruct (Nat.leb base n) eqn:L; [apply Nat.leb_le in L; rewrite Hρ; f_equal; lia|reflexivity]|..];
    rewrite ?H, ?H0; reflexivity.
Qed.

Lemma display_spec shr T i shared root : Inv T -> (exists ci, RId T i ci /\ WOk ci) ->
  HDisplay.display_s F base shr T i = Some (shared, root) ->
  Forall (fun d => aok nt d = true) shared /\ aok nt root = true /\
  ((forall s d, nth_error shared s = Some d -> forall x, catom (base + s) x = @ca M d x) ->
   forall ci, RId T i ci -> forall c, @ca M root c = wden ci c).
Proof.
  intros I Hi E; unfold HDisplay.display_s in E; cbv zeta in E.
  match type of E with context [HDisplay.dref T base shr ?cnt ?grp ?fu i HDisplay.dstart] =>
    destruct (HDisplay.dref T base shr cnt grp fu i HDisplay.dstart) as [[r D]|] eqn:Er; [|discriminate];
    injection E as <- <-;
    destruct (proj1 (disp_spec T I shr cnt grp fu) i _ r D (DInv_start T) Hi Er) as [DI [_ [_ [Kr Sr]]]]
  end.
  split; [|split; [apply (proj1 (proj1 lassoc_aok r Kr))|]].
  { rewrite Forall_forall; intros d Hd; apply in_map_iff in Hd as [[j d0] [<- Hd]]; apply In_nth_error in Hd as [k Hk].
    destruct (di_defs T D DI k j d0 Hk) as [_ [K _]]; apply (proj1 (proj1 lassoc_aok d0 K)). }
  intros HS ci Hci c.
  set (ρ := fun k (x : U) => @catom M (base + k) x).
  assert (Ag : forall n, Agree T D ρ n).
  { intros n k; induction k as [k IHk] using (well_founded_induction lt_wf); intros j d Hk Lk cj Hj x.
    destruct (di_defs T D DI k j d Hk) as [_ [_ Sd]].
    unfold ρ at 1; rewrite (HS k (HDisplay.lassoc d)) by (rewrite nth_error_map, Hk; reflexivity).
    rewrite (proj1 (proj1 (lassoc_ca M) d x)), <- (proj1 (dden_real ρ (fun _ _ => eq_refl)) d x).
    apply (Sd ρ); [|exact Hj]; intros k' j' d' Hk' Lk' cj' Hj' x'; apply (IHk k' Lk' j' d' Hk' ltac:(lia) cj' Hj' x'). }
  rewrite (proj1 (proj1 (lassoc_ca M) r c)), <- (proj1 (dden_real ρ (fun _ _ => eq_refl)) r c).
  apply (Sr ρ (Ag _) ci Hci c).
Qed.

Theorem display_s_sound shr T i shared root ci : Inv T -> RId T i ci -> WOk ci ->
  HDisplay.display_s F base shr T i = Some (shared, root) ->
  (forall s d, nth_error shared s = Some d -> forall x, catom (base + s) x = @ca M d x) ->
  forall c, @ca M root c = wden ci c.
Proof.
  intros I Hi Oi E HS; apply (proj2 (proj2 (display_spec shr T i shared root I (ex_intro _ ci (conj Hi Oi)) E)) HS ci Hi).
Qed.

Theorem display_sound T i shared root ci : Inv T -> RId T i ci -> WOk ci ->
  HDisplay.display F base T i = Some (shared, root) ->
  (forall s d, nth_error shared s = Some d -> forall x, catom (base + s) x = @ca M d x) ->
  forall c, @ca M root c = wden ci c.
Proof. apply display_s_sound. Qed.

(** ** What is shown is in range *)

Theorem display_s_aok shr T i shared root ci : Inv T -> RId T i ci -> WOk ci ->
  HDisplay.display_s F base shr T i = Some (shared, root) ->
  Forall (fun d => aok nt d = true) shared /\ aok nt root = true.
Proof.
  intros I Hi Oi E; destruct (display_spec shr T i shared root I (ex_intro _ ci (conj Hi Oi)) E) as [K1 [K2 _]]; auto.
Qed.

End Sound.
