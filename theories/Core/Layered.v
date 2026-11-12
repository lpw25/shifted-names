(** * Layered words, computed directly (in progress)

    A layered word is a list of segments, applied in order.  A term in a
    segment has the rest of the word as its payload: [NBind u (WEnd SNil)
    b] in a segment is [u] with [b] and then every later segment.  So
    the terms of one segment (a layer) all have the same payload, and
    nothing is written twice.

    The normaliser folds over the expression from its last step, putting
    one step at a time in front of the word built so far ([fold]); a lift
    is a close before and an open after, with the steps between folded
    one level deeper under the bound label.

    So far: a fragment (terms whose payload is the identity or a payload
    atom), with the meaning of a layered word and soundness of
    the fold. *)

From Stdlib Require Import Arith List Lia Bool.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Unique Normal Shared.
Import ListNotations.

Inductive lstep : Type :=
| LS (s : seg)
| LA (L : list (lexp * nat)) (a : nat).

Definition lword : Type := list lstep.

Section Layered.

Variable F : order.
Variable ntm : nat.

Definition is_term (t : ntgt) : bool := match t with NBind _ _ _ => true | NVar _ _ => false end.

Definition has_terms (s : seg) : bool := existsb is_term (stargets s).

(** Every term of the segment has the identity under its payload. *)
Definition no_atoms (s : seg) : bool :=
  forallb (fun t => match t with NBind _ _ (Some _) => false | _ => true end) (stargets s).

(** A segment that does nothing to named variables: only the bound
    label has an entry. *)
Fixpoint bound_only (s : seg) : bool :=
  match s with
  | SNil => true
  | SEnt LNone _ _ r => bound_only r
  | SEnt _ _ _ _ => false
  end.

Fixpoint slifts (d : nat) (s : seg) : option seg :=
  match d with
  | 0 => Some s
  | S d' => match slifts d' s with Some s' => slift F ntm LNone s' | None => None end
  end.

(** ** Putting a segment in front of a word

    A segment without terms joins the first segment.  One with terms is
    a new layer, unless the first segment does nothing to named
    variables and the terms have no payload atom: then they have the
    same payload as the terms of the first segment, and are in its
    layer.  Joining is composition of segments. *)
Definition cons_seg (s : seg) (K : lword) : option lword :=
  match K with
  | LS s1 :: K' =>
      if negb (has_terms s) || (bound_only s1 && no_atoms s)
      then match scomp F ntm s1 s with
           | Some SNil => Some K'
           | Some s' => Some (LS s' :: K')
           | None => None
           end
      else Some (LS s :: K)
  | _ => Some (match s with SNil => K | _ => LS s :: K end)
  end.

(** ** The steps *)

Definition entry (h : lexp) (t : ntgt) : option seg := sfront F h t SNil.

(** [⟦ h \ · ⟧] and [⟦ · \ h ⟧]. *)
Definition close_seg (h : lexp) : option seg := sfront F h (NVar LNone 0) (shseg LNone 1).
Definition open_seg (h : lexp) : option seg := sfront F LNone (NVar h 0) (shseg h 1).

Definition is_bound (h : lexp) : bool := match h with LNone => true | _ => false end.

(** A target of the fragment. *)
Definition tgt_of (t : texp) : option ntgt :=
  match t with
  | TVarE h i => Some (NVar h i)
  | TBindE u PId => if u <? ntm then Some (NBind u (WEnd SNil) None) else None
  | TBindE u (PAtom n) => if u <? ntm then Some (NBind u (WEnd SNil) (Some n)) else None
  | _ => None
  end.

Definition cons_lifted (d : nat) (s : option seg) (K : option lword) : option lword :=
  match s, K with
  | Some s0, Some K0 => match slifts d s0 with Some s' => cons_seg s' K0 | None => None end
  | _, _ => None
  end.

(** [fold d e K]: [e] under [d] lifts by the bound label, then [K]. *)
Fixpoint fold (d : nat) (e : aexp) (K : option lword) : option lword :=
  match e with
  | AId => K
  | AAtom n => match K with Some K0 => Some (LA (match d with 0 => [] | _ => [(LNone, d)] end) n :: K0) | None => None end
  | ACompose a b => fold d b (fold d a K)
  | AOuter h a => fold d a (cons_lifted d (Some (shseg h 1)) K)
  | AInner h t a =>
      match tgt_of t with
      | Some t' =>
          if is_bound h then fold (S d) a (cons_lifted d (entry h t') K)
          else cons_lifted d (close_seg h)
                 (fold (S d) a (cons_lifted d (open_seg h) (cons_lifted d (entry h t') K)))
      | None => None
      end
  | ALift h a =>
      if is_bound h then fold (S d) a K
      else cons_lifted d (close_seg h) (fold (S d) a (cons_lifted d (open_seg h) K))
  end.

Definition lnorm (e : aexp) : option lword := fold 0 e (Some []).

End Layered.

(** ** Soundness *)

(** A lift is a close before and an open after, around the lift by the
    bound label.  Decided by the normaliser, for a label variable and an
    atom. *)
Definition rclose {T} (x : label) : radj T :=
  rpush_inner (Some x) (RRename (mk_rvar None 0)) (rpush_outer None ridentity).
Definition ropen {T} (x : label) : radj T :=
  rpush_inner None (RRename (mk_rvar (Some x) 0)) (rpush_outer (Some x) ridentity).

Lemma lift_close_open {T} (x : label) (a : radj T) :
  rlift (Some x) a = rcompose (rcompose (ropen x) (rlift None a)) (rclose x).
Proof.
  set (e1 := ALift (LAtom 0) (AAtom 0)).
  set (e2 := ACompose (ACompose (AInner LNone (TVarE (LAtom 0) 0) (AOuter (LAtom 0) AId)) (ALift LNone (AAtom 0)))
                      (AInner (LAtom 0) (TVarE LNone 0) (AOuter LNone AId))).
  change (aeden [x] (@nil T) [a] [] e1 = aeden [x] (@nil T) [a] [] e2).
  refine (nf_eq_sh_sound [x] (@nil T) [a] [] (order_of []) _ 0 (le_n _) e1 e2 _); [|vm_compute; reflexivity].
  apply order_of_ok; unfold lfacts_ok; repeat constructor.
Qed.

(** ** The algebra of going around a payload

    [lifted d a] is [a] under [d] lifts by the bound label. *)

Section Algebra.

Context {T : Type}.

Definition lifted (d : nat) (a : radj T) : radj T := iter d (rlift None) a.

Lemma lifted_compose d a b : lifted d (rcompose a b) = rcompose (lifted d a) (lifted d b).
Proof. unfold lifted; induction d as [|d IH]; [reflexivity|]; cbn [iter]; rewrite IH, rlift_compose; reflexivity. Qed.

Lemma lifted_S d a : lifted (S d) a = lifted d (rlift None a).
Proof. unfold lifted; induction d as [|d IH]; [reflexivity|]; cbn [iter] in *; rewrite IH; reflexivity. Qed.

Lemma lifted_identity d : lifted d ridentity = ridentity.
Proof. unfold lifted; induction d as [|d IH]; [reflexivity|]; cbn [iter]; rewrite IH; apply rlift_identity. Qed.

Lemma lifted_add w t a : lifted (w + t) a = lifted w (lifted t a).
Proof. unfold lifted; apply iter_add. Qed.

Lemma shiftk_one : @shiftk T None 1 = rshift None.
Proof. reflexivity. Qed.

Lemma shiftk_add w t : @shiftk T None (w + t) = rcompose (shiftk None w) (shiftk None t).
Proof.
  induction w as [|w IH]; [symmetry; apply rcompose_identity_l|].
  cbn [Nat.add]; rewrite <- (shiftk_S (T:=T) None (w + t)), <- (shiftk_S (T:=T) None w), IH, rcompose_assoc; reflexivity.
Qed.

(** Weakening the bound label, then [a] under the lifts, is [a], then
    the weakening. *)
Lemma lifted_shift w a : rcompose (lifted w a) (shiftk None w) = rcompose (shiftk None w) a.
Proof.
  induction w as [|w IH]; [cbn; rewrite rcompose_identity_l, rcompose_identity_r; reflexivity|].
  rewrite <- (shiftk_S (T:=T) None w), shiftk_one; unfold lifted in *; cbn [iter].
  rewrite rcompose_assoc, rcompose_lift_shift, <- rcompose_assoc, IH, rcompose_assoc; reflexivity.
Qed.

(** A term whose payload ends with [B] is the term without it, then [B],
    when everything else is first sent through [A], which [B] undoes. *)
Lemma bypass h u (ρ : rpadj T) (A B : radj T) :
  rcompose B A = ridentity ->
  rpush_inner h (RBind u (rpcompose B ρ)) ridentity
  = rcompose B (rcompose (rpush_inner h (RBind u ρ) ridentity) (rlift h A)).
Proof.
  intros H; rewrite <- (rpush_inner_compose (@nil T) 0 (le_n 0)), rcompose_identity_l, rcompose_push_inner_r, H.
  reflexivity.
Qed.

(** [A] and [J] go around [a] with [t] bound variables: [A], then [a]
    under [t] lifts, then [J] is the identity, and [J] consumes exactly
    the [t] variables. *)
Definition bpair (a A J : radj T) (t : nat) : Prop :=
  rcompose (rcompose J (lifted t a)) A = ridentity /\ rcompose J (shiftk None t) = ridentity.

Lemma bypass_step h u (ρ : rpadj T) a A J t w :
  bpair a A J t ->
  rpush_inner h (RBind u (rpcompose (shiftk None w) (rpcompose a ρ))) ridentity
  = rcompose (lifted w J)
      (rcompose (lifted (w + t) a)
         (rcompose (rpush_inner h (RBind u (rpcompose (shiftk None (w + t)) ρ)) ridentity) (rlift h (lifted w A)))).
Proof.
  intros [H1 H2].
  assert (HBA : rcompose (rcompose (lifted w J) (lifted (w + t) a)) (lifted w A) = ridentity).
  { rewrite lifted_add, <- !lifted_compose, H1; apply lifted_identity. }
  assert (E : rcompose (shiftk None w) a
              = rcompose (rcompose (lifted w J) (lifted (w + t) a)) (shiftk None (w + t))).
  { rewrite shiftk_add, lifted_add.
    rewrite <- (rcompose_assoc (lifted w J) (lifted w (lifted t a)) _).
    rewrite (rcompose_assoc (lifted w (lifted t a)) (shiftk None w) (shiftk None t)).
    rewrite (lifted_shift w (lifted t a)).
    rewrite <- (rcompose_assoc (shiftk None w) (lifted t a) (shiftk None t)).
    rewrite (lifted_shift t a).
    rewrite (rcompose_assoc (lifted w J) (shiftk None w) _), (lifted_shift w J).
    rewrite <- (rcompose_assoc (shiftk None w) J _), (rcompose_assoc J (shiftk None t) a), H2, rcompose_identity_l.
    reflexivity. }
  rewrite (rcompose_assoc (lifted w J)), <- (bypass h u _ _ _ HBA), !rpcompose_compose, E; reflexivity.
Qed.

(** The units. *)
Lemma bpair_entry g tg : bpair (rpush_inner g tg ridentity) (rshift g) ridentity 0.
Proof.
  split; [|apply rcompose_identity_l].
  cbn [lifted iter]; rewrite rcompose_identity_l; apply rcompose_push_inner_shift.
Qed.

Lemma bpair_outer x :
  bpair (rshift (Some x)) (rclose x) (rpush_inner None (RRename (mk_rvar (Some x) 0)) ridentity) 1.
Proof.
  split; [|rewrite shiftk_one; apply rcompose_push_inner_shift].
  unfold lifted, rshift, rclose; cbn [iter].
  set (e1 := ACompose (ACompose (AInner LNone (TVarE (LAtom 0) 0) AId) (ALift LNone (AOuter (LAtom 0) AId)))
                      (AInner (LAtom 0) (TVarE LNone 0) (AOuter LNone AId))).
  change (aeden [x] (@nil T) [] [] e1 = aeden [x] (@nil T) [] [] AId).
  refine (nf_eq_sh_sound [x] (@nil T) [] [] (order_of []) _ 0 (le_n _) e1 AId _); [|vm_compute; reflexivity].
  apply order_of_ok; unfold lfacts_ok; repeat constructor.
Qed.

Lemma bpair_outer_bound :
  bpair (rshift None) ridentity (rpush_inner None (RRename (mk_rvar None 0)) (@ridentity T)) 1.
Proof.
  split; [|rewrite shiftk_one; apply rcompose_push_inner_shift].
  rewrite rcompose_identity_r; unfold lifted, rshift; cbn [iter].
  set (e1 := ACompose (AInner LNone (TVarE LNone 0) AId) (ALift LNone (AOuter LNone AId))).
  change (aeden [] (@nil T) [] [] e1 = aeden [] (@nil T) [] [] AId).
  refine (nf_eq_sh_sound [] (@nil T) [] [] (order_of []) _ 0 (le_n _) e1 AId _); [|vm_compute; reflexivity].
  apply order_of_ok; unfold lfacts_ok; repeat constructor.
Qed.

Lemma rlift_shift_bound y : rlift (Some y) (@rshift T None) = rshift None.
Proof.
  unfold rshift.
  set (e1 := ALift (LAtom 0) (AOuter LNone AId)).
  change (aeden [y] (@nil T) [] [] e1 = aeden [y] (@nil T) [] [] (AOuter LNone AId)).
  refine (nf_eq_sh_sound [y] (@nil T) [] [] (order_of []) _ 0 (le_n _) e1 _ _); [|vm_compute; reflexivity].
  apply order_of_ok; unfold lfacts_ok; repeat constructor.
Qed.

Lemma rlift_shiftk_bound y t : rlift (Some y) (@shiftk T None t) = shiftk None t.
Proof.
  induction t as [|t IH]; [apply rlift_identity|].
  rewrite <- (shiftk_S (T:=T) None t), <- rlift_compose, IH, shiftk_one, rlift_shift_bound; reflexivity.
Qed.

Lemma lifted_rlift y t (a : radj T) : lifted t (rlift (Some y) a) = rlift (Some y) (lifted t a).
Proof.
  unfold lifted; induction t as [|t IH]; [reflexivity|]; cbn [iter]; rewrite IH.
  apply rlift_comm; discriminate.
Qed.

Lemma bpair_lift y a A J t : bpair a A J t -> bpair (rlift (Some y) a) (rlift (Some y) A) (rlift (Some y) J) t.
Proof.
  intros [H1 H2]; split.
  - rewrite lifted_rlift, !rlift_compose, H1; apply rlift_identity.
  - rewrite <- (rlift_shiftk_bound y t), rlift_compose, H2; apply rlift_identity.
Qed.

End Algebra.

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
Local Notation aeden := (aeden lenv tenv aenv penv).
Local Notation teden := (teden lenv tenv aenv penv).

(** A layered word is its segments one after the other. *)
Fixpoint lwden (l : lword) : radj T :=
  match l with
  | [] => ridentity
  | LS s :: r => rcompose (lwden r) (sden s)
  | LA L a :: r => rcompose (lwden r) (lifts lenv L (aden aenv a))
  end.

Definition lwdist (l : lword) : Prop := Forall (fun x => match x with LS s => sdistd s | LA _ _ => True end) l.

Lemma slifts_sound d : forall s s', sdistd s -> slifts F ntm d s = Some s' -> sdistd s' /\ sden s' = lifted d (sden s).
Proof.
  induction d as [|d IH]; intros s s' Hd; cbn [slifts].
  - intros H; injection H as <-; split; [exact Hd|reflexivity].
  - destruct (slifts F ntm d s) as [s1|] eqn:E; [|discriminate]; intros H.
    destruct (IH s s1 Hd E) as [Hd1 Hs1].
    destruct (slift_sound lenv tenv aenv penv F HF ntm Hntm LNone s1 s' Hd1 H) as [Hd' Hs'].
    split; [exact Hd'|]; rewrite Hs', Hs1; reflexivity.
Qed.

Lemma cons_seg_sound s K K' :
  sdistd s -> lwdist K -> cons_seg F ntm s K = Some K' ->
  lwdist K' /\ lwden K' = rcompose (lwden K) (sden s).
Proof.
  intros Hs HK; unfold cons_seg.
  assert (Hplain : Some (match s with SNil => K | _ => LS s :: K end) = Some K' ->
                   lwdist K' /\ lwden K' = rcompose (lwden K) (sden s)).
  { intros H; injection H as <-; destruct s as [|h ts m r].
    - split; [exact HK|]; change (lwden K = rcompose (lwden K) ridentity); rewrite rcompose_identity_r; reflexivity.
    - split; [constructor; [exact Hs|exact HK]|reflexivity]. }
  destruct K as [|[s1|L a] K0]; [exact Hplain| |exact Hplain].
  - inversion HK as [|? ? H1 H0]; subst.
    destruct (negb (has_terms s) || (bound_only s1 && no_atoms s)).
    + destruct (scomp F ntm s1 s) as [s'|] eqn:E; [|discriminate].
      destruct (scomp_sound lenv tenv aenv penv F HF ntm Hntm s1 s s' H1 Hs E) as [Hd' Hs'].
      assert (Hgoal : lwden (LS s' :: K0) = rcompose (lwden (LS s1 :: K0)) (sden s)).
      { cbn [lwden]; rewrite Hs', rcompose_assoc; reflexivity. }
      destruct s' as [|h ts m r]; intros H; injection H as <-.
      * split; [exact H0|]; rewrite <- Hgoal; change (lwden K0 = rcompose (lwden K0) ridentity);
        rewrite rcompose_identity_r; reflexivity.
      * split; [constructor; assumption|exact Hgoal].
    + intros H; injection H as <-; split; [constructor; assumption|reflexivity].
Qed.

Lemma cons_lifted_sound d s K K' :
  sdistd s -> lwdist K -> cons_lifted F ntm d (Some s) (Some K) = Some K' ->
  lwdist K' /\ lwden K' = rcompose (lwden K) (lifted d (sden s)).
Proof.
  intros Hs HK; unfold cons_lifted; destruct (slifts F ntm d s) as [s'|] eqn:E; [|discriminate]; intros H.
  destruct (slifts_sound d s s' Hs E) as [Hd' Hs'].
  destruct (cons_seg_sound s' K K' Hd' HK H) as [A B]; split; [exact A|]; rewrite B, Hs'; reflexivity.
Qed.

Lemma entry_sound h t s : Normalise.tdist lenv t -> entry F h t = Some s ->
  sdistd s /\ sden s = rpush_inner (lden h) (tden t) ridentity.
Proof. intros Ht H; exact (sfront_sound lenv tenv aenv penv F HF ntm Hntm h t SNil s I Ht H). Qed.

Lemma close_seg_sound h x s : lden h = Some x -> close_seg F h = Some s -> sdistd s /\ sden s = rclose x.
Proof.
  intros Hx H.
  destruct (sfront_sound lenv tenv aenv penv F HF ntm Hntm h (NVar LNone 0) (shseg LNone 1) s (shseg_dd lenv _ _) I H) as [A B].
  split; [exact A|]; rewrite B, Hx; reflexivity.
Qed.

Lemma open_seg_sound h x s : lden h = Some x -> open_seg F h = Some s -> sdistd s /\ sden s = ropen x.
Proof.
  intros Hx H.
  destruct (sfront_sound lenv tenv aenv penv F HF ntm Hntm LNone (NVar h 0) (shseg h 1) s (shseg_dd lenv _ _) I H) as [A B].
  split; [exact A|]; rewrite B, sden_shseg; unfold shiftk, ropen; cbn [iter Normalise.tden]; rewrite Hx; reflexivity.
Qed.

Lemma tgt_of_sound t t' : tgt_of ntm t = Some t' -> Normalise.tdist lenv t' /\ tden t' = teden t.
Proof.
  destruct t as [h i|u p|h t]; cbn [tgt_of]; try discriminate.
  - intros H; injection H as <-; split; [exact I|reflexivity].
  - assert (Hu : (u <? ntm) = true -> exists y, nth_error tenv u = Some y).
    { intros Hu; apply Nat.ltb_lt in Hu; destruct (nth_error tenv u) as [y|] eqn:E; [exists y; reflexivity|].
      apply nth_error_None in E; lia. }
    destruct p as [|n|a p|h p]; try discriminate;
      (destruct (u <? ntm) eqn:Eu; [|discriminate]; intros H; injection H as <-; split; [exact I|];
       destruct (Hu eq_refl) as [y Ey]; cbn [Normalise.tden Normalise.teden]; rewrite Ey;
       cbn [Normalise.wden Normalise.sins Normalise.souts Normalise.peden Normalise.bden];
       rewrite rpcompose_identity; reflexivity).
Qed.

Lemma named_label h : is_bound h = false -> exists x, lden h = Some x.
Proof. destruct h; cbn; [discriminate| |]; intros _; eexists; reflexivity. Qed.

Lemma bound_label h : is_bound h = true -> lden h = None.
Proof. destruct h; cbn; [reflexivity|discriminate|discriminate]. Qed.

Lemma fold_none e : forall d, fold F ntm d e None = None.
Proof.
  induction e as [| n | a IHa b IHb | h a IHa | h t a IHa | h a IHa]; intros d; cbn [fold]; try reflexivity.
  - rewrite IHa; apply IHb.
  - apply IHa.
  - destruct (tgt_of ntm t); [|reflexivity]; destruct (is_bound h).
    + unfold cons_lifted; destruct (entry F h n); apply IHa.
    + assert (E : cons_lifted F ntm d (open_seg F h) (cons_lifted F ntm d (entry F h n) None) = None).
      { unfold cons_lifted; destruct (entry F h n); destruct (open_seg F h); reflexivity. }
      rewrite E, IHa; unfold cons_lifted; destruct (close_seg F h); reflexivity.
  - destruct (is_bound h); [apply IHa|].
    assert (E : cons_lifted F ntm d (open_seg F h) None = None) by (unfold cons_lifted; destruct (open_seg F h); reflexivity).
    rewrite E, IHa; unfold cons_lifted; destruct (close_seg F h); reflexivity.
Qed.

Lemma cons_lifted_some d s K K' : cons_lifted F ntm d s K = Some K' -> exists s0 K0, s = Some s0 /\ K = Some K0.
Proof. destruct s as [s0|], K as [K0|]; cbn; try discriminate; intros _; exists s0, K0; split; reflexivity. Qed.

Lemma fold_some e d K K' : fold F ntm d e K = Some K' -> exists K0, K = Some K0.
Proof. destruct K as [K0|]; [intros _; exists K0; reflexivity|rewrite fold_none; discriminate]. Qed.

Theorem fold_sound e : forall d K K',
  lwdist K -> fold F ntm d e (Some K) = Some K' ->
  lwdist K' /\ lwden K' = rcompose (lwden K) (lifted d (aeden e)).
Proof.
  induction e as [| n | a IHa b IHb | h a IHa | h t a IHa | h a IHa]; intros d K K' HK; cbn [fold].
  - intros H; injection H as <-; split; [exact HK|].
    cbn [Normalise.aeden]; rewrite lifted_identity, rcompose_identity_r; reflexivity.
  - intros H; injection H as <-; split; [constructor; [exact I|exact HK]|].
    cbn [lwden Normalise.aeden]; destruct d; reflexivity.
  - intros H; destruct (fold_some _ _ _ _ H) as [K1 E1]; rewrite E1 in H.
    destruct (IHa d K K1 HK E1) as [H1 D1]; destruct (IHb d K1 K' H1 H) as [H2 D2]; split; [exact H2|].
    rewrite D2, D1; cbn [Normalise.aeden]; rewrite lifted_compose, rcompose_assoc; reflexivity.
  - intros H; destruct (fold_some _ _ _ _ H) as [K1 E1]; rewrite E1 in H.
    destruct (cons_lifted_sound d _ K K1 (shseg_dd lenv _ _) HK E1) as [H1 D1].
    destruct (IHa d K1 K' H1 H) as [H2 D2]; split; [exact H2|].
    rewrite D2, D1; cbn [Normalise.aeden]; rewrite <- rcompose_assoc, <- lifted_compose.
    rewrite sden_shseg; unfold shiftk; cbn [iter]; rewrite rcompose_identity_push_outer; reflexivity.
  - destruct (tgt_of ntm t) as [t'|] eqn:Et; [|discriminate].
    destruct (tgt_of_sound t t' Et) as [Htd Htv].
    assert (Ein : aeden (AInner h t a) = rcompose (rpush_inner (lden h) (tden t') ridentity) (rlift (lden h) (aeden a))).
    { cbn [Normalise.aeden]; rewrite <- (rpush_inner_compose tenv ntm Hntm), rcompose_identity_l, Htv; reflexivity. }
    destruct (is_bound h) eqn:Eb.
    + intros H; destruct (fold_some _ _ _ _ H) as [K1 E1]; rewrite E1 in H.
      destruct (cons_lifted_some _ _ _ _ E1) as [s0 [K0 [Es EK]]]; injection EK as <-; rewrite Es in E1.
      destruct (entry_sound h t' s0 Htd Es) as [Hs0 Ds0].
      destruct (cons_lifted_sound d _ K K1 Hs0 HK E1) as [H1 D1].
      destruct (IHa (S d) K1 K' H1 H) as [H2 D2]; split; [exact H2|].
      rewrite D2, D1, Ds0, Ein, (bound_label h Eb), lifted_S, <- rcompose_assoc, <- lifted_compose; reflexivity.
    + destruct (named_label h Eb) as [x Hx]; intros H.
      destruct (cons_lifted_some _ _ _ _ H) as [sc [K3 [Ec E3]]]; rewrite Ec, E3 in H.
      destruct (fold_some _ _ _ _ E3) as [K2 E2]; rewrite E2 in E3.
      destruct (cons_lifted_some _ _ _ _ E2) as [so [K1 [Eo E1]]]; rewrite Eo, E1 in E2.
      destruct (cons_lifted_some _ _ _ _ E1) as [s0 [K0 [Es EK]]]; injection EK as <-; rewrite Es in E1.
      destruct (entry_sound h t' s0 Htd Es) as [Hs0 Ds0].
      destruct (open_seg_sound h x so Hx Eo) as [Hso Dso].
      destruct (close_seg_sound h x sc Hx Ec) as [Hsc Dsc].
      destruct (cons_lifted_sound d _ K K1 Hs0 HK E1) as [H1 D1].
      destruct (cons_lifted_sound d _ K1 K2 Hso H1 E2) as [H2 D2].
      destruct (IHa (S d) K2 K3 H2 E3) as [H3 D3].
      destruct (cons_lifted_sound d _ K3 K' Hsc H3 H) as [H4 D4]; split; [exact H4|].
      rewrite D4, D3, D2, D1, Ds0, Dso, Dsc, Ein, Hx, (lift_close_open x), lifted_S, !lifted_compose, !rcompose_assoc.
      reflexivity.
  - destruct (is_bound h) eqn:Eb.
    + intros H; destruct (IHa (S d) K K' HK H) as [H2 D2]; split; [exact H2|].
      rewrite D2; cbn [Normalise.aeden]; rewrite (bound_label h Eb), lifted_S; reflexivity.
    + destruct (named_label h Eb) as [x Hx]; intros H.
      destruct (cons_lifted_some _ _ _ _ H) as [sc [K3 [Ec E3]]]; rewrite Ec, E3 in H.
      destruct (fold_some _ _ _ _ E3) as [K2 E2]; rewrite E2 in E3.
      destruct (cons_lifted_some _ _ _ _ E2) as [so [K1 [Eo EK]]]; injection EK as <-; rewrite Eo in E2.
      destruct (open_seg_sound h x so Hx Eo) as [Hso Dso].
      destruct (close_seg_sound h x sc Hx Ec) as [Hsc Dsc].
      destruct (cons_lifted_sound d _ K K2 Hso HK E2) as [H2 D2].
      destruct (IHa (S d) K2 K3 H2 E3) as [H3 D3].
      destruct (cons_lifted_sound d _ K3 K' Hsc H3 H) as [H4 D4]; split; [exact H4|].
      rewrite D4, D3, D2, Dso, Dsc; cbn [Normalise.aeden]; rewrite Hx, (lift_close_open x), lifted_S, !lifted_compose, !rcompose_assoc.
      reflexivity.
Qed.

(** The layered word of an expression means what the expression means. *)
Theorem lnorm_sound e l : lnorm F ntm e = Some l -> lwden l = aeden e.
Proof.
  intros H; destruct (fold_sound e 0 [] l (Forall_nil _) H) as [_ D].
  rewrite D; cbn [lwden lifted iter]; apply rcompose_identity_l.
Qed.

End Sound.
