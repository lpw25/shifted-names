(** * The canonical graph: evaluation

    The free-model meaning of adjustment expressions, and a raw evaluator
    from expressions to encodings ([GForm]) with no canonicity
    conditions.  Canonicalisation is separate ([GCanon]). *)

From Stdlib Require Import String Arith List Lia Bool.
From ShiftedNames.Core Require Import Label Var Normalise Unique GForm.
Import ListNotations.

(** ** The free meaning of expressions *)

Section Free.

Variable lenv : list label.
Local Notation lden := (lden lenv).

Definition sh0 (h : lexp) (y : rvar) : rvar := shift_rvar (mk_rvar (lden h) 0) y.
Definition ush0 (h : lexp) (y : rvar) : rvar := unshift_rvar (mk_rvar (lden h) 0) y.

Fixpoint tvof (t : texp) : option rvar :=
  match t with
  | TVarE h i => Some (mk_rvar (lden h) i)
  | TBindE _ _ => None
  | TShiftE h t => option_map (sh0 h) (tvof t)
  end.

Fixpoint fpb (p : pexp) : option nat :=
  match p with PId => None | PAtom n => Some n | PComp _ p | PShift _ p => fpb p end.

(** [fa a K]: [a], then [K]. *)
Fixpoint fa (a : aexp) (K : rvar -> fres) (v : rvar) {struct a} : fres :=
  match a with
  | AId => K v
  | AAtom n => FStuck n v K
  | ACompose a b => fa b (fa a K) v
  | AOuter h a => fa a (fun y => K (sh0 h y)) v
  | AInner h t a => if rvar_eqb v (mk_rvar (lden h) 0) then ft t K else fa a K (ush0 h v)
  | ALift h a => if rvar_eqb v (mk_rvar (lden h) 0) then K v else fa a (fun y => K (sh0 h y)) (ush0 h v)
  end
with ft (t : texp) (K : rvar -> fres) : fres :=
  match t with
  | TVarE h i => K (mk_rvar (lden h) i)
  | TBindE u p => FTerm u (fpb p) (fp p K)
  | TShiftE h t => match tvof t with Some w => K (sh0 h w) | None => ft t K end
  end
with fp (p : pexp) (K : rvar -> fres) : rvar -> fres :=
  match p with
  | PId | PAtom _ => K
  | PComp a p => fp p (fa a K)
  | PShift h p => fp p (fun y => K (sh0 h y))
  end.

End Free.

(** ** Shift algebra *)

Section Raw.

Variable labs : list (option label).
Hypothesis Hnd : NoDup labs.

Local Notation lab := (GForm.lab labs).
Local Notation shv := (GForm.shv labs).
Local Notation fpost := (GForm.fpost labs).
Local Notation em := (GForm.em labs).
Local Notation lm := (GForm.lm labs).
Local Notation rm := (GForm.rm labs).
Local Notation nm := (GForm.nm labs).
Local Notation lsm := (GForm.lsm labs).
Local Notation dm := (GForm.dm labs).
Local Notation ush := (GForm.ush labs).
Local Notation zeros := (GForm.zeros labs).

Definition sadd (s t : list nat) : list nat := map (fun k => sget s k + sget t k) (seq 0 (length labs)).

Lemma sget_map_seq (f : nat -> nat) n k : k < n -> sget (map f (seq 0 n)) k = f k.
Proof.
  intros Hk; unfold sget.
  assert (H : forall n st j, j < n -> nth j (map f (seq st n)) 0 = f (st + j)).
  { induction n0 as [|n0 IH]; intros st j Hj; [lia|]; destruct j as [|j]; cbn [seq map nth].
    - rewrite Nat.add_0_r; reflexivity.
    - rewrite IH by lia; f_equal; lia. }
  apply (H n 0 k Hk).
Qed.

Lemma sget_sadd s t k : k < length labs -> sget (sadd s t) k = sget s k + sget t k.
Proof. intros Hk; unfold sadd; rewrite sget_map_seq by exact Hk; reflexivity. Qed.

Lemma shv_sadd s t v : shv (sadd s t) v = shv t (shv s v).
Proof.
  destruct v as [l i]; unfold GForm.shv; cbn [v_label v_index].
  destruct (GForm.pos labs l) as [k|] eqn:E; cbn [v_label v_index]; rewrite E; [|reflexivity].
  destruct (pos_some labs _ _ E) as [Hk _]; rewrite sget_sadd by exact Hk; f_equal; lia.
Qed.

Lemma fpost_sadd s t f : feq (fpost (sadd s t) f) (fpost t (fpost s f)).
Proof.
  induction f as [v|u b k IH|a z k IH]; cbn [GForm.fpost feq].
  - apply shv_sadd.
  - repeat split; intros y _; apply IH.
  - repeat split; intros y; apply IH.
Qed.

Lemma shv_out s v : ~ In (v_label v) labs -> shv s v = v.
Proof.
  intros Hn; destruct v as [l i]; unfold GForm.shv; cbn [v_label v_index].
  destruct (GForm.pos labs l) as [k|] eqn:E; [|reflexivity].
  destruct (pos_some labs _ _ E) as [Hk Hl]; exfalso; apply Hn; cbn; rewrite <- Hl; apply nth_In, Hk.
Qed.

(** Pushing a shift into an entry and a reference. *)

Definition rshift (r : gref) (t : list nat) : gref := match r with GR s n => GR (sadd s t) n end.

Definition eshift (e : ent) (t : list nat) : ent :=
  match e with
  | EV v => EV (shv t v)
  | ET u b r => ET u b (rshift r t)
  | ES a z r => ES a z (rshift r t)
  end.

Lemma rshift_rm r t v : feq (rm (rshift r t) v) (fpost t (rm r v)).
Proof. destruct r as [s n]; cbn [rshift GForm.rm]; apply fpost_sadd. Qed.

Lemma eshift_em e t : feq (em (eshift e t)) (fpost t (em e)).
Proof.
  destruct e as [v|u b r|a z r]; cbn [eshift GForm.em GForm.fpost feq].
  - reflexivity.
  - repeat split; intros y _; apply rshift_rm.
  - repeat split; intros y; apply rshift_rm.
Qed.

(** ** Raw operations on encodings *)

(** The entry at index [j] of list [L] of label [k], its outputs shifted by [acc]. *)
Fixpoint lookupL (k : nat) (acc : list nat) (L : lst) (j : nat) : ent :=
  match L with
  | LCons e s t => match j with 0 => eshift e acc | S j' => lookupL k (sadd s acc) t j' end
  | LNilV | LNilP => EV (shv acc (mk_rvar (lab k) j))
  | LNilS a r m => ES a (mk_rvar (lab k) (j + m)) (rshift r acc)
  end.

Fixpoint lsts_get (k : nat) (ls : lsts) : list nat * lst :=
  match ls, k with
  | LsNil, _ => ([], LNilV)
  | LsCons s L _, 0 => (s, L)
  | LsCons _ _ r, S k => lsts_get k r
  end.

Fixpoint lsts_set (k : nat) (x : list nat * lst) (ls : lsts) : lsts :=
  match ls, k with
  | LsNil, _ => LsNil
  | LsCons _ _ r, 0 => LsCons (fst x) (snd x) r
  | LsCons s L r, S k => LsCons s L (lsts_set k x r)
  end.

Fixpoint lsts_map (f : nat -> list nat * lst -> list nat * lst) (k : nat) (ls : lsts) : lsts :=
  match ls with
  | LsNil => LsNil
  | LsCons s L r => let x := f k (s, L) in LsCons (fst x) (snd x) (lsts_map f (S k) r)
  end.

Definition posv (v : rvar) : nat := match pos labs (v_label v) with Some k => k | None => 0 end.

(** The entry a reference gives a variable of a label of [labs]. *)
Definition apply_ref (r : gref) (v : rvar) : ent :=
  match r with
  | GR s (GN d ls) => let k := posv v in let '(s', L) := lsts_get k ls in lookupL k (sadd s' s) L (v_index v)
  end.

(** Dropping the first input of the list of label [k]. *)
Definition dropL (k : nat) (x : list nat * lst) : list nat * lst :=
  match x with
  | (s, LCons e s' t) => (sadd s' s, t)
  | (s, LNilV) => (sadd (ush k) s, LNilV)
  | (s, LNilP) => (sadd (ush k) s, LNilP)
  | (s, LNilS a r m) => (s, LNilS a r (S m))
  end.

Definition preshift (k : nat) (r : gref) : gref :=
  match r with GR s (GN d ls) => GR s (GN d (lsts_set k (dropL k (lsts_get k ls)) ls)) end.

Definition dshift (d : gdef) (t : list nat) : gdef := match d with DV => DV | DS a r => DS a (rshift r t) end.

(** Pushing the entry [e] in front of the list of label [h] of [B]. *)
Definition push (h : nat) (e : ent) (B : gref) : gref :=
  match B with
  | GR sB (GN d ls) =>
      GR zeros (GN (dshift d sB)
        (lsts_map (fun k x => if Nat.eqb k h then (zeros, LCons e (sadd (fst x) sB) (snd x))
                              else (sadd (fst x) sB, snd x)) 0 ls))
  end.

Fixpoint all_lsts (n : nat) (f : nat -> list nat * lst) (k : nat) : lsts :=
  match n with 0 => LsNil | S n => LsCons (fst (f k)) (snd (f k)) (all_lsts n f (S k)) end.

Definition atomR (a : nat) (K : gref) : gref :=
  GR zeros (GN (DS a K) (all_lsts (length labs) (fun _ => (zeros, LNilS a K 0)) 0)).

Definition endR : gref := GR zeros (GN DV (all_lsts (length labs) (fun _ => (zeros, LNilV)) 0)).

(** ** Meaning of the raw operations *)

Definition shapeR (r : gref) : Prop := match r with GR _ (GN _ ls) => lsts_len ls = length labs end.

Lemma lookupL_em L : forall k acc j, feq (em (lookupL k acc L j)) (fpost acc (lm k L j)).
Proof.
  induction L as [| |a r m|e s t IH]; intros k acc j; cbn [lookupL GForm.lm].
  - reflexivity.
  - reflexivity.
  - cbn [GForm.em GForm.fpost feq]; repeat split; intros y; apply rshift_rm.
  - destruct j as [|j]; [apply eshift_em|].
    eapply feq_trans; [apply IH|apply fpost_sadd].
Qed.

Lemma lsts_get_nth ls : forall k, k < lsts_len ls -> lsts_get k ls = (snth k ls, lnth k ls).
Proof. induction ls as [|s L r IH]; intros [|k] Hk; cbn in *; try lia; [reflexivity|apply IH; lia]. Qed.

Lemma nm_lab d ls k i : lsts_len ls = length labs -> k < length labs ->
  nm (GN d ls) (mk_rvar (lab k) i) = fpost (fst (lsts_get k ls)) (lm k (snd (lsts_get k ls)) i).
Proof.
  intros Hl Hk; rewrite lsts_get_nth by lia; cbn [GForm.nm fst snd].
  apply (lsm_lab labs Hnd (dm d) ls 0 k i); lia.
Qed.

Lemma nm_out d ls v : lsts_len ls = length labs -> ~ In (v_label v) labs -> nm (GN d ls) v = dm d v.
Proof. intros Hl Hn; cbn [GForm.nm]; apply (lsm_out labs); [lia|exact Hn]. Qed.

Lemma lab_pos v : In (v_label v) labs -> exists k, k < length labs /\ lab k = v_label v /\ posv v = k.
Proof.
  intros Hin; unfold posv; destruct (pos labs (v_label v)) as [k|] eqn:E.
  - destruct (pos_some labs _ _ E) as [Hk Hl]; exists k; auto.
  - exfalso; unfold GForm.pos in E; apply (pos_from_none _ _ _ E), Hin.
Qed.

Lemma apply_ref_rm r v : shapeR r -> In (v_label v) labs -> feq (em (apply_ref r v)) (rm r v).
Proof.
  destruct r as [s [d ls]]; intros Hs Hin; cbn [shapeR] in Hs.
  destruct (lab_pos v Hin) as (k & Hk & Hl & Hp); destruct v as [l i]; cbn in Hl; subst l.
  unfold apply_ref; rewrite Hp; cbn [GForm.rm]; rewrite nm_lab by assumption.
  destruct (lsts_get k ls) as [s' L]; cbn [fst snd v_index].
  eapply feq_trans; [apply lookupL_em|apply fpost_sadd].
Qed.

Lemma lsts_set_get ls : forall k k' x, k' < lsts_len ls ->
  lsts_get k' (lsts_set k x ls) = if Nat.eqb k' k then x else lsts_get k' ls.
Proof.
  induction ls as [|s L r IH]; intros [|k] [|k'] x Hk; cbn in *; try lia; try reflexivity.
  - destruct x; reflexivity.
  - apply IH; lia.
Qed.

Lemma lsts_set_len ls : forall k x, lsts_len (lsts_set k x ls) = lsts_len ls.
Proof. induction ls as [|s L r IH]; intros [|k] x; cbn; auto. Qed.

Lemma lsts_map_get f ls : forall k0 k, k < lsts_len ls -> lsts_get k (lsts_map f k0 ls) = f (k0 + k) (lsts_get k ls).
Proof.
  induction ls as [|s L r IH]; intros k0 [|k] Hk; cbn in *; try lia.
  - rewrite Nat.add_0_r; destruct (f k0 (s, L)); reflexivity.
  - rewrite IH by lia; f_equal; lia.
Qed.

Lemma lsts_map_len f ls : forall k0, lsts_len (lsts_map f k0 ls) = lsts_len ls.
Proof. induction ls as [|s L r IH]; intros k0; cbn; auto. Qed.

Lemma all_lsts_get n f : forall k0 k, k < n -> lsts_get k (all_lsts n f k0) = f (k0 + k).
Proof.
  induction n as [|n IH]; intros k0 [|k] Hk; cbn in *; try lia.
  - rewrite Nat.add_0_r; destruct (f k0); reflexivity.
  - rewrite IH by lia; f_equal; lia.
Qed.

Lemma all_lsts_len n f : forall k0, lsts_len (all_lsts n f k0) = n.
Proof. induction n as [|n IH]; intros k0; cbn; auto. Qed.

Lemma fpost_zeros f : feq (fpost zeros f) f.
Proof. apply fpost_id, sget_zeros. Qed.

Lemma shift_lab_same k i : shift_rvar (mk_rvar (lab k) 0) (mk_rvar (lab k) i) = mk_rvar (lab k) (S i).
Proof. unfold shift_rvar; cbn; rewrite label_eqb_refl; reflexivity. Qed.

Lemma shift_lab_other l k v : v_label v <> l -> shift_rvar (mk_rvar l k) v = v.
Proof. intros Hne; unfold shift_rvar; cbn; destruct (label_eqb_spec l (v_label v)); [congruence|reflexivity]. Qed.

Lemma unshift_lab_same k i : unshift_rvar (mk_rvar (lab k) 0) (mk_rvar (lab k) (S i)) = mk_rvar (lab k) i.
Proof. unfold unshift_rvar; cbn; rewrite label_eqb_refl; cbn; f_equal; lia. Qed.

Lemma unshift_lab_other l k v : v_label v <> l -> unshift_rvar (mk_rvar l k) v = v.
Proof. intros Hne; unfold unshift_rvar; cbn; destruct (label_eqb_spec l (v_label v)); [congruence|reflexivity]. Qed.

Lemma dropL_lm k x i : k < length labs ->
  feq (fpost (fst (dropL k x)) (lm k (snd (dropL k x)) i)) (fpost (fst x) (lm k (snd x) (S i))).
Proof.
  intros Hk; destruct x as [s [| |a r m|e s' t]]; cbn [dropL fst snd GForm.lm].
  - eapply feq_trans; [apply fpost_sadd|]; cbn [GForm.fpost feq].
    rewrite (shv_lab labs Hnd) by exact Hk; rewrite sget_ush, Nat.eqb_refl by exact Hk; f_equal; f_equal; lia.
  - eapply feq_trans; [apply fpost_sadd|]; cbn [GForm.fpost feq].
    rewrite (shv_lab labs Hnd) by exact Hk; rewrite sget_ush, Nat.eqb_refl by exact Hk; f_equal; f_equal; lia.
  - cbn [GForm.fpost feq]; repeat split; [f_equal; lia|intros y; apply feq_refl].
  - apply fpost_sadd.
Qed.

Lemma preshift_rm k r v : shapeR r -> k < length labs ->
  feq (rm (preshift k r) v) (rm r (shift_rvar (mk_rvar (lab k) 0) v)).
Proof.
  destruct r as [s [d ls]]; intros Hs Hk; cbn [shapeR] in Hs; cbn [preshift GForm.rm].
  apply feq_fpost.
  assert (Hs' : lsts_len (lsts_set k (dropL k (lsts_get k ls)) ls) = length labs) by (rewrite lsts_set_len; exact Hs).
  destruct (in_dec label_eq_dec (v_label v) labs) as [Hin|Hout].
  - destruct (lab_pos v Hin) as (k' & Hk' & Hl & _); destruct v as [l i]; cbn in Hl; subst l.
    rewrite nm_lab by assumption; rewrite lsts_set_get by lia.
    destruct (Nat.eqb_spec k' k) as [->|Hne].
    + rewrite shift_lab_same, nm_lab by assumption; apply dropL_lm, Hk.
    + rewrite shift_lab_other; [rewrite nm_lab by assumption; apply feq_refl|].
      cbn; intros He; apply Hne, (lab_inj labs Hnd); assumption.
  - rewrite shift_lab_other; [rewrite !nm_out by assumption; apply feq_refl|].
    intros He; apply Hout; rewrite He; apply nth_In, Hk.
Qed.

Lemma push_rm h e B v : shapeR B -> h < length labs ->
  feq (rm (push h e B) v)
      (if rvar_eqb v (mk_rvar (lab h) 0) then em e else rm B (unshift_rvar (mk_rvar (lab h) 0) v)).
Proof.
  destruct B as [sB [d ls]]; intros Hs Hh; cbn [shapeR] in Hs; cbn [push GForm.rm].
  eapply feq_trans; [apply fpost_zeros|].
  set (f := fun k x => if Nat.eqb k h then (zeros, LCons e (sadd (fst x) sB) (snd x)) else (sadd (fst x) sB, snd x)).
  assert (Hl : lsts_len (lsts_map f 0 ls) = length labs) by (rewrite lsts_map_len; exact Hs).
  destruct (in_dec label_eq_dec (v_label v) labs) as [Hin|Hout].
  - destruct (lab_pos v Hin) as (k & Hk & Hlk & _); destruct v as [l i]; cbn in Hlk; subst l.
    rewrite nm_lab by assumption; rewrite lsts_map_get by lia; cbn [Nat.add]; unfold f.
    destruct (Nat.eqb_spec k h) as [->|Hne].
    + destruct i as [|i].
      * replace (rvar_eqb _ _) with true by (unfold rvar_eqb; cbn; rewrite label_eqb_refl; reflexivity).
        apply fpost_zeros.
      * replace (rvar_eqb _ _) with false by (unfold rvar_eqb; cbn; rewrite label_eqb_refl; reflexivity).
        rewrite unshift_lab_same; cbn [GForm.rm]; rewrite nm_lab by assumption.
        eapply feq_trans; [apply fpost_zeros|]; destruct (lsts_get h ls) as [s L]; cbn [fst snd]; apply fpost_sadd.
    + assert (Hlab : lab k <> lab h) by (intros He'; apply Hne, (lab_inj labs Hnd); assumption).
      replace (rvar_eqb _ _) with false
        by (unfold rvar_eqb; cbn; destruct (label_eqb_spec (lab k) (lab h)); [contradiction|reflexivity]).
      rewrite unshift_lab_other by (cbn; exact Hlab); cbn [GForm.rm]; rewrite nm_lab by assumption.
      destruct (lsts_get k ls) as [s L]; cbn [fst snd]; apply fpost_sadd.
  - replace (rvar_eqb _ _) with false.
    2:{ unfold rvar_eqb; cbn [v_label v_index]; destruct (label_eqb_spec (v_label v) (lab h)) as [He|]; [|reflexivity].
        exfalso; apply Hout; rewrite He; apply nth_In, Hh. }
    rewrite unshift_lab_other by (intros He; apply Hout; rewrite He; apply nth_In, Hh).
    cbn [GForm.rm]; rewrite !nm_out by assumption; destruct d as [|a r]; cbn [dshift GForm.dm GForm.fpost feq].
    + symmetry; apply shv_out, Hout.
    + repeat split; intros y; apply rshift_rm.
Qed.

Lemma atomR_rm a K v : feq (rm (atomR a K) v) (FStuck a v (rm K)).
Proof.
  cbn [atomR GForm.rm]; eapply feq_trans; [apply fpost_zeros|].
  assert (Hl : lsts_len (all_lsts (length labs) (fun _ => (zeros, LNilS a K 0)) 0) = length labs) by apply all_lsts_len.
  destruct (in_dec label_eq_dec (v_label v) labs) as [Hin|Hout].
  - destruct (lab_pos v Hin) as (k & Hk & Hlk & _); destruct v as [l i]; cbn in Hlk; subst l.
    rewrite nm_lab by assumption; rewrite all_lsts_get by exact Hk; cbn [fst snd GForm.lm].
    eapply feq_trans; [apply fpost_zeros|]; cbn [feq]; repeat split; [f_equal; lia|intros y; apply feq_refl].
  - rewrite nm_out by assumption; apply feq_refl.
Qed.

Lemma endR_rm v : feq (rm endR v) (FVar v).
Proof.
  cbn [endR GForm.rm]; eapply feq_trans; [apply fpost_zeros|].
  assert (Hl : lsts_len (all_lsts (length labs) (fun _ => (zeros, LNilV)) 0) = length labs) by apply all_lsts_len.
  destruct (in_dec label_eq_dec (v_label v) labs) as [Hin|Hout].
  - destruct (lab_pos v Hin) as (k & Hk & Hlk & _); destruct v as [l i]; cbn in Hlk; subst l.
    rewrite nm_lab by assumption; rewrite all_lsts_get by exact Hk; cbn [fst snd GForm.lm]; apply fpost_zeros.
  - rewrite nm_out by assumption; apply feq_refl.
Qed.

Lemma shape_preshift k r : shapeR r -> shapeR (preshift k r).
Proof. destruct r as [s [d ls]]; cbn; rewrite lsts_set_len; auto. Qed.

Lemma shape_push h e B : shapeR B -> shapeR (push h e B).
Proof. destruct B as [s [d ls]]; cbn; rewrite lsts_map_len; auto. Qed.

Lemma shape_atomR a K : shapeR (atomR a K).
Proof. apply all_lsts_len. Qed.

Lemma shape_endR : shapeR endR.
Proof. apply all_lsts_len. Qed.

End Raw.
