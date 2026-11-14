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

(** ** The raw evaluator *)

Section Eval.

Variable lenv : list label.
Variable labs : list (option label).
Hypothesis Hnd : NoDup labs.

Local Notation lden := (lden lenv).
Local Notation lab := (GForm.lab labs).
Local Notation rm := (GForm.rm labs).
Local Notation em := (GForm.em labs).

Definition posh (h : lexp) : nat := posv labs (mk_rvar (lden h) 0).

Fixpoint ev (a : aexp) (K : gref) : gref :=
  match a with
  | AId => K
  | AAtom n => atomR labs n K
  | ACompose a b => ev b (ev a K)
  | AOuter h a => ev a (preshift labs (posh h) K)
  | AInner h t a => push labs (posh h) (evt t K) (ev a K)
  | ALift h a => push labs (posh h) (apply_ref labs K (mk_rvar (lden h) 0)) (ev a (preshift labs (posh h) K))
  end
with evt (t : texp) (K : gref) : ent :=
  match t with
  | TVarE h i => apply_ref labs K (mk_rvar (lden h) i)
  | TBindE u p => ET u (fpb p) (evp p K)
  | TShiftE h t => match tvof lenv t with Some w => apply_ref labs K (sh0 lenv h w) | None => evt t K end
  end
with evp (p : pexp) (K : gref) : gref :=
  match p with
  | PId | PAtom _ => K
  | PComp a p => evp p (ev a K)
  | PShift h p => evp p (preshift labs (posh h) K)
  end.

(** Expressions whose labels are all in [labs]. *)
Definition hl (h : lexp) : Prop := In (lden h) labs.

Fixpoint wfa (a : aexp) : Prop :=
  match a with
  | AId | AAtom _ => True
  | ACompose a b => wfa a /\ wfa b
  | AOuter h a | ALift h a => hl h /\ wfa a
  | AInner h t a => hl h /\ wft t /\ wfa a
  end
with wft (t : texp) : Prop :=
  match t with
  | TVarE h _ => hl h
  | TBindE _ p => wfp p
  | TShiftE h t => hl h /\ wft t
  end
with wfp (p : pexp) : Prop :=
  match p with
  | PId | PAtom _ => True
  | PComp a p => wfa a /\ wfp p
  | PShift h p => hl h /\ wfp p
  end.

Lemma posh_lab h : hl h -> posh h < length labs /\ lab (posh h) = lden h.
Proof.
  intros Hh; destruct (lab_pos labs (mk_rvar (lden h) 0) Hh) as (k & Hk & Hl & Hp).
  unfold posh; rewrite Hp; auto.
Qed.

Lemma tvof_label t w : wft t -> tvof lenv t = Some w -> In (v_label w) labs.
Proof.
  revert w; induction t as [h i|u p|h t IH]; intros w Hw E; cbn in E.
  - injection E as <-; exact Hw.
  - discriminate.
  - destruct (tvof lenv t) as [w'|] eqn:E'; [|discriminate]; injection E as <-.
    destruct Hw as [_ Hw]; unfold sh0, shift_rvar; destruct (_ && _); cbn; apply (IH w' Hw eq_refl).
Qed.

(** The free meaning respects agreement of continuations. *)
Lemma fa_feq_all :
  (forall a K1 K2, (forall v, feq (K1 v) (K2 v)) -> forall v, feq (fa lenv a K1 v) (fa lenv a K2 v))
  /\ (forall t K1 K2, (forall v, feq (K1 v) (K2 v)) -> feq (ft lenv t K1) (ft lenv t K2))
  /\ (forall p K1 K2, (forall v, feq (K1 v) (K2 v)) -> forall v, feq (fp lenv p K1 v) (fp lenv p K2 v)).
Proof.
  apply exp_mind; intros; cbn [fa ft fp];
    repeat match goal with |- context [rvar_eqb ?x ?y] => destruct (rvar_eqb x y) end;
    repeat match goal with |- context [tvof lenv ?t] => destruct (tvof lenv t) end;
    try solve [auto | cbn [feq]; repeat split; intros; auto].
  all: try (apply H; intros; apply H0; auto).
  all: try (apply H0; intros; apply H; auto).
  all: idtac.
Qed.

Lemma ev_shape_all :
  (forall a K, shapeR labs K -> shapeR labs (ev a K))
  /\ (forall (t : texp) (K : gref), True)
  /\ (forall p K, shapeR labs K -> shapeR labs (evp p K)).
Proof.
  apply exp_mind; intros; cbn [ev evp]; auto using shape_atomR, shape_push, shape_preshift.
Qed.

Lemma ev_shape a K : shapeR labs K -> shapeR labs (ev a K).
Proof. apply (proj1 ev_shape_all). Qed.

Lemma evp_shape p K : shapeR labs K -> shapeR labs (evp p K).
Proof. apply (proj2 (proj2 ev_shape_all)). Qed.

Lemma sh0_label h w : v_label (sh0 lenv h w) = v_label w.
Proof. unfold sh0, shift_rvar; destruct (_ && _); reflexivity. Qed.

Theorem ev_sound_all :
  (forall a K, wfa a -> shapeR labs K -> forall v, feq (rm (ev a K) v) (fa lenv a (rm K) v))
  /\ (forall t K, wft t -> shapeR labs K -> feq (em (evt t K)) (ft lenv t (rm K)))
  /\ (forall p K, wfp p -> shapeR labs K -> forall v, feq (rm (evp p K) v) (fp lenv p (rm K) v)).
Proof.
  destruct fa_feq_all as (Ha & Ht & Hp).
  apply exp_mind; intros; cbn [ev evt evp fa ft fp wfa wft wfp] in *.
  - apply feq_refl.
  - apply (atomR_rm labs Hnd).
  - (* composition *)
    destruct H1 as [Hwa Hwb]; eapply feq_trans; [apply H0; [exact Hwb|apply ev_shape, H2]|].
    apply Ha; intros y; apply H; assumption.
  - (* outer *)
    destruct H0 as [Hh Hw]; destruct (posh_lab h Hh) as [Hk Hl].
    eapply feq_trans; [apply H; [exact Hw|apply shape_preshift, H1]|].
    apply Ha; intros y; unfold sh0; rewrite <- Hl; apply (preshift_rm labs Hnd), Hk; exact H1.
  - (* inner *)
    destruct H1 as (Hh & Hwt & Hw); destruct (posh_lab h Hh) as [Hk Hl].
    eapply feq_trans; [apply (push_rm labs Hnd); [apply ev_shape, H2|exact Hk]|].
    rewrite Hl; destruct (rvar_eqb v _); [apply H; assumption|apply H0; assumption].
  - (* lift *)
    destruct H0 as [Hh Hw]; destruct (posh_lab h Hh) as [Hk Hl].
    eapply feq_trans; [apply (push_rm labs Hnd); [apply ev_shape, shape_preshift, H1|exact Hk]|].
    rewrite Hl; destruct (rvar_eqb_spec v (mk_rvar (lden h) 0)) as [->|_].
    + apply (apply_ref_rm labs Hnd); [exact H1|exact Hh].
    + eapply feq_trans; [apply H; [exact Hw|apply shape_preshift, H1]|].
      apply Ha; intros y; unfold sh0; rewrite <- Hl; apply (preshift_rm labs Hnd), Hk; exact H1.
  - (* variable *)
    apply (apply_ref_rm labs Hnd); [exact H0|exact H].
  - (* term *)
    cbn [GForm.em feq]; repeat split; intros y _; apply H; assumption.
  - (* shifted *)
    destruct H0 as [Hh Hwt]; destruct (tvof lenv t) as [w|] eqn:E.
    + apply (apply_ref_rm labs Hnd); [exact H1|rewrite sh0_label; apply (tvof_label t w Hwt E)].
    + apply H; assumption.
  - apply feq_refl.
  - apply feq_refl.
  - (* payload composition *)
    destruct H1 as [Hwa Hwp]; eapply feq_trans; [apply H0; [exact Hwp|apply ev_shape, H2]|].
    apply Hp; intros y; apply H; assumption.
  - (* payload shift *)
    destruct H0 as [Hh Hw]; destruct (posh_lab h Hh) as [Hk Hl].
    eapply feq_trans; [apply H; [exact Hw|apply shape_preshift, H1]|].
    apply Hp; intros y; unfold sh0; rewrite <- Hl; apply (preshift_rm labs Hnd), Hk; exact H1.
Qed.

Theorem ev_sound a v : wfa a -> feq (rm (ev a (endR labs)) v) (fa lenv a FVar v).
Proof.
  intros Hw; eapply feq_trans; [apply (proj1 ev_sound_all); [exact Hw|apply shape_endR]|].
  apply (proj1 fa_feq_all); intros y; apply (endR_rm labs Hnd).
Qed.

End Eval.

