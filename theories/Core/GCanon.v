(** * The canonical graph: canonicalisation

    Turning a raw encoding into a canonical one with the same meaning:
    shifts are factored out bottom-up, cells that repeat their nil are
    absorbed, and the bound inputs of payloads without payload atom are
    filled by [LNilP]. *)

From Stdlib Require Import String Arith List Lia Bool.
From ShiftedNames.Core Require Import Label Var Normalise Unique GForm GEval.
Import ListNotations.

Section Has.

Variable labs : list (option label).
Hypothesis Hnd : NoDup labs.

Local Notation lab := (GForm.lab labs).
Local Notation fpost := (GForm.fpost labs).
Local Notation em := (GForm.em labs).
Local Notation lm := (GForm.lm labs).
Local Notation rm := (GForm.rm labs).
Local Notation nm := (GForm.nm labs).
Local Notation dm := (GForm.dm labs).
Local Notation Out := GForm.Out.

(** ** Which labels an encoding outputs *)

Fixpoint hasE (e : ent) (k : nat) : bool :=
  match e with
  | EV v => label_eqb (v_label v) (lab k)
  | ET _ _ r | ES _ _ r => hasR r k
  end
with hasL (q : nat) (L : lst) (k : nat) : bool :=
  match L with
  | LNilV => Nat.eqb q k
  | LNilP => false
  | LNilS _ r _ => hasR r k
  | LCons e _ t => hasE e k || hasL q t k
  end
with hasR (r : gref) (k : nat) : bool := match r with GR _ n => hasN n k end
with hasN (n : gnode) (k : nat) : bool := match n with GN d ls => hasD d k || hasLs 0 ls k end
with hasLs (q : nat) (ls : lsts) (k : nat) : bool :=
  match ls with LsNil => false | LsCons _ L r => hasL q L k || hasLs (S q) r k end
with hasD (d : gdef) (k : nat) : bool := match d with DV => false | DS _ r => hasR r k end.

Definition Has {X} (D : X -> Prop) (F : X -> fres) (k : nat) : Prop := exists i, Out D F (mk_rvar (lab k) i).

Lemma Has_post {X} (D : X -> Prop) F s k : k < length labs -> Has D (fun x => fpost s (F x)) k <-> Has D F k.
Proof.
  intros Hk; split.
  - intros (i & Ho); apply (Out_post_lab labs Hnd) in Ho as [_ Ho]; [|exact Hk]; eexists; exact Ho.
  - intros (i & Ho); exists (i + sget s k); apply (Out_post_lab labs Hnd); [exact Hk|].
    replace (i + sget s k - sget s k) with i by lia; split; [lia|exact Ho].
Qed.

Lemma Has_feq {X} (D : X -> Prop) F G k : (forall x, D x -> feq (F x) (G x)) -> Has D F k -> Has D G k.
Proof. intros He (i & Ho); exists i; apply (Out_feq _ _ _ _ He Ho). Qed.

Lemma outs_term u b r w : outs (FTerm u b (rm r)) w <-> Out (Dom (match b with None => true | Some _ => false end)) (rm r) w.
Proof.
  split.
  - intros Ho; inversion Ho; subst; exists y; split; [|assumption].
    destruct b; [left; reflexivity|right; auto].
  - intros (y & Hy & Ho); apply outs_T with y; [|exact Ho].
    intros ->; destruct Hy as [Hy|Hy]; [discriminate|exact Hy].
Qed.

Lemma outs_stuck a z r w : outs (FStuck a z (rm r)) w <-> Out (Dom false) (rm r) w.
Proof.
  split.
  - intros Ho; inversion Ho; subst; exists y; split; [left; reflexivity|assumption].
  - intros (y & _ & Ho); apply outs_S with y; exact Ho.
Qed.

Lemma Dom_lab p q i : Dom p (mk_rvar (lab q) i) <-> (p = false \/ lab q <> None).
Proof. reflexivity. Qed.

(** The outputs of a node: those of its lists on observed labels, and
    those of its default. *)
Lemma Has_node p d ls k : lsts_len ls = length labs -> k < length labs ->
  Has (Dom p) (nm (GN d ls)) k <->
  (exists q, q < length labs /\ (p = false \/ lab q <> None) /\ Has all_nat (lm q (lnth q ls)) k)
  \/ (match d with DV => False | DS _ r => Has (Dom false) (rm r) k end).
Proof.
  intros Hl Hk; split.
  - intros (i & v & Hv & Ho).
    destruct (in_dec label_eq_dec (v_label v) labs) as [Hin|Hout].
    + destruct (lab_pos labs v Hin) as (q & Hq & Hlq & _); destruct v as [l j]; cbn in Hlq; subst l.
      rewrite (nm_lab labs Hnd) in Ho by assumption; rewrite (lsts_get_nth _ q) in Ho by lia; cbn [fst snd] in Ho.
      apply outs_fpost in Ho as (w0 & Ho & Hw).
      left; exists q; split; [exact Hq|split; [exact Hv|]].
      destruct w0 as [l0 i0]; unfold GForm.shv in Hw; cbn in Hw.
      destruct (pos labs l0) eqn:E; injection Hw as <- _; exists i0, j; exact (conj I Ho).
    + rewrite (nm_out labs) in Ho by assumption; right.
      destruct d as [|a r]; cbn [GForm.dm] in Ho.
      * inversion Ho; subst; apply Hout; cbn; apply nth_In, Hk.
      * exists i; apply outs_stuck in Ho; exact Ho.
  - intros [(q & Hq & Hv & (i & j & _ & Ho))|Hd].
    + exists (i + sget (snth q ls) k), (mk_rvar (lab q) j); split; [exact Hv|].
      rewrite (nm_lab labs Hnd) by assumption; rewrite (lsts_get_nth _ q) by lia; cbn [fst snd].
      apply outs_fpost; exists (mk_rvar (lab k) i); split; [exact Ho|]; rewrite (shv_lab labs Hnd) by exact Hk; reflexivity.
    + destruct d as [|a r]; [contradiction|]; destruct Hd as (i & Ho).
      destruct (fresh_label labs) as [fs Hfs].
      exists i, (mk_rvar (Some fs) 0); split; [right; discriminate|].
      rewrite (nm_out labs) by (exact Hl || exact Hfs); cbn [GForm.dm]; apply outs_stuck; exact Ho.
Qed.

Lemma has_spec_all :
  (forall e, cent labs e -> forall k, k < length labs -> hasE e k = true <-> exists i, outs (em e) (mk_rvar (lab k) i))
  /\ (forall L, forall q, q < length labs -> clst labs q L -> forall k, k < length labs ->
        hasL q L k = true <-> Has all_nat (lm q L) k)
  /\ (forall r, forall p, cref labs p r -> forall k, k < length labs -> hasR r k = true <-> Has (Dom p) (rm r) k)
  /\ (forall n, forall p, cnode labs p n -> forall k, k < length labs -> hasN n k = true <-> Has (Dom p) (nm n) k)
  /\ (forall ls, forall p q, clsts labs p q ls -> q + lsts_len ls = length labs -> forall k, k < length labs ->
        hasLs q ls k = true <->
        exists j, j < lsts_len ls /\ (p = false \/ lab (q + j) <> None) /\ Has all_nat (lm (q + j) (lnth j ls)) k)
  /\ (forall d, cdef labs d -> forall k, k < length labs ->
        hasD d k = true <-> match d with DV => False | DS _ r => Has (Dom false) (rm r) k end).
Proof.
  apply g_ind; intros; cbn [hasE hasL hasR hasN hasLs hasD cent clst cref cnode clsts cdef GForm.em GForm.lm] in *.
  - (* EV *)
    split.
    + intros E; destruct (label_eqb_spec (v_label v) (lab k)) as [He|]; [|discriminate].
      exists (v_index v); destruct v as [l i]; cbn in He; subst l; constructor.
    + intros (i & Ho); inversion Ho; subst; cbn; apply label_eqb_refl.
  - (* ET *)
    rewrite (H _ H0 k H1); split.
    + intros (i & Ho); exists i; apply outs_term; exact Ho.
    + intros (i & Ho); exists i; apply outs_term in Ho; exact Ho.
  - (* ES *)
    rewrite (H _ H0 k H1); split.
    + intros (i & Ho); exists i; apply outs_stuck; exact Ho.
    + intros (i & Ho); exists i; apply outs_stuck in Ho; exact Ho.
  - (* LNilV *)
    split.
    + intros E; apply Nat.eqb_eq in E; subst q; exists 0, 0; split; [exact I|constructor].
    + intros (i & j & _ & Ho); inversion Ho as [v Hv| |]; subst; apply Nat.eqb_eq.
      apply (lab_inj labs Hnd); assumption.
  - (* LNilP *)
    contradiction.
  - (* LNilS *)
    rewrite (H false H1 k H2); split.
    + intros (i & Ho); exists i, 0; split; [exact I|apply outs_stuck; exact Ho].
    + intros (i & j & _ & Ho); exists i; apply outs_stuck in Ho; exact Ho.
  - (* LCons *)
    destruct H2 as (He & Ht & _); rewrite orb_true_iff, (H He k H3), (H0 q H1 Ht k H3); split.
    + intros [(i & Ho)|Hh].
      * exists i, 0; split; [exact I|exact Ho].
      * apply (Has_post _ (fun j => lm q t j) s k H3) in Hh as (i & j & _ & Ho).
        exists i, (S j); split; [exact I|exact Ho].
    + intros (i & [|j] & _ & Ho); [left; exists i; exact Ho|right].
      apply (Has_post _ (fun j => lm q t j) s k H3); exists i, j; split; [exact I|exact Ho].
  - (* GR *)
    destruct H0 as (Hc & _); rewrite (H p Hc k H1).
    split; intros Hh; [apply (Has_post _ (nm n) s k H1)|apply (Has_post _ (nm n) s k H1) in Hh]; exact Hh.
  - (* GN *)
    destruct H1 as (Hd & Hls & Hlen); rewrite orb_true_iff, (H Hd k H2), (H0 p 0 Hls Hlen k H2), Has_node by assumption.
    cbn [Nat.add]; rewrite Hlen; split; (intros [X|X]; [right|left]; exact X).
  - (* LsNil *)
    split; [discriminate|intros (j & Hj & _); cbn in Hj; lia].
  - (* LsCons *)
    destruct H1 as [HL Hr]; cbn [lsts_len] in H2.
    rewrite orb_true_iff, (H0 p (S q) Hr ltac:(lia) k H3).
    assert (HL0 : hasL q L k = true <-> (p = false \/ lab q <> None) /\ Has all_nat (lm q L) k).
    { destruct (p && match lab q with None => true | Some _ => false end) eqn:Ep.
      - destruct HL as [-> _]; cbn [hasL]; split; [discriminate|].
        intros [[->|Hn] _]; [discriminate|]; destruct p; [|discriminate]; destruct (lab q); [|contradiction].
        discriminate.
      - destruct HL as (Hc & _); rewrite (H q ltac:(lia) Hc k H3); split; [|intros [_ X]; exact X].
        intros X; split; [|exact X].
        destruct p; [right; cbn in Ep; destruct (lab q); discriminate|left; reflexivity]. }
    rewrite HL0; split.
    + intros [[Hv Hh]|(j & Hj & Hv & Hh)].
      * exists 0; rewrite Nat.add_0_r; cbn [lnth]; repeat split; [cbn; lia|exact Hv|exact Hh].
      * exists (S j); replace (q + S j) with (S q + j) by lia; cbn [lnth]; repeat split; [cbn; lia|exact Hv|exact Hh].
    + intros ([|j] & Hj & Hv & Hh); cbn [lnth] in Hh.
      * rewrite Nat.add_0_r in Hv, Hh; left; split; assumption.
      * right; exists j; replace (q + S j) with (S q + j) in Hv, Hh by lia; repeat split; [cbn in Hj; lia|exact Hv|exact Hh].
  - (* DV *)
    split; [discriminate|contradiction].
  - (* DS *)
    apply H; assumption.
Qed.

End Has.

(** ** Canonicalisation *)

Section Canonise.

Variable labs : list (option label).
Hypothesis Hnd : NoDup labs.

Local Notation lab := (GForm.lab labs).
Local Notation fpost := (GForm.fpost labs).
Local Notation em := (GForm.em labs).
Local Notation lm := (GForm.lm labs).
Local Notation rm := (GForm.rm labs).
Local Notation nm := (GForm.nm labs).
Local Notation dm := (GForm.dm labs).
Local Notation zeros := (GForm.zeros labs).
Local Notation ush := (GForm.ush labs).
Local Notation sadd := (GEval.sadd labs).
Local Notation hasE := (hasE labs).
Local Notation hasL := (hasL labs).
Local Notation hasN := (hasN labs).

Definition vec (f : nat -> nat) : list nat := map f (seq 0 (length labs)).
Definition ssub (s t : list nat) : list nat := vec (fun k => sget s k - sget t k).
Definition srestr (h : nat -> bool) (s : list nat) : list nat := vec (fun k => if h k then sget s k else 0).

Definition omin (a b : option nat) : option nat :=
  match a, b with Some x, Some y => Some (Nat.min x y) | Some x, None => Some x | None, b => b end.
Definition oget (a : option nat) : nat := match a with Some x => x | None => 0 end.

(** The least output index of an entry on label [k] (when it has one). *)
Definition emin (e : ent) (k : nat) : nat :=
  match e with EV v => v_index v | ET _ _ (GR s _) | ES _ _ (GR s _) => sget s k end.

Definition rdown (r : gref) (m : list nat) : gref :=
  match r with GR s n => GR (srestr (hasN n) (ssub s m)) n end.

Definition edown (e : ent) (m : list nat) : ent :=
  match e with
  | EV v => EV (match pos labs (v_label v) with
                | Some k => mk_rvar (v_label v) (v_index v - sget m k)
                | None => v end)
  | ET u b r => ET u b (rdown r m)
  | ES a z r => ES a z (rdown r m)
  end.

Definition bflag (b : option nat) : bool := match b with None => true | Some _ => false end.

Definition phslot (p : bool) (q : nat) : bool := p && match lab q with None => true | Some _ => false end.

Fixpoint lsmin (q : nat) (ls : lsts) (k : nat) : option nat :=
  match ls with
  | LsNil => None
  | LsCons s L r => omin (if hasL q L k then Some (sget s k) else None) (lsmin (S q) r k)
  end.

Definition dmin (d : gdef) (k : nat) : option nat :=
  match d with DV => None | DS _ (GR s n) => if hasN n k then Some (sget s k) else None end.

Fixpoint lsdown (q : nat) (ls : lsts) (m : list nat) : lsts :=
  match ls with
  | LsNil => LsNil
  | LsCons s L r => LsCons (srestr (hasL q L) (ssub s m)) L (lsdown (S q) r m)
  end.

Definition ddown (d : gdef) (m : list nat) : gdef := match d with DV => DV | DS a r => DS a (rdown r m) end.

(** A cell [e'], then [t'] shifted by [st], with [e'] and [t'] canonical:
    its least outputs factored out, then absorbed into the nil when it
    only repeats it. *)
Definition cell (q : nat) (e' : ent) (st : list nat) (t' : lst) : list nat * lst :=
  let mn := vec (fun k => oget (omin (if hasE e' k then Some (emin e' k) else None)
                                     (if hasL q t' k then Some (sget st k) else None))) in
  let e'' := edown e' mn in
  let st' := srestr (hasL q t') (ssub st mn) in
  match t' with
  | LNilV =>
      if (0 <? sget st' q) && ent_eqb e'' (EV (mk_rvar (lab q) (sget st' q - 1)))
      then (sadd (srestr (Nat.eqb q) (ssub st' (ush q))) mn, LNilV)
      else (mn, LCons e'' st' t')
  | LNilS a (GR _ n) m0 =>
      if (0 <? m0) && ent_eqb e'' (ES a (mk_rvar (lab q) (m0 - 1)) (GR st' n))
      then (sadd st' mn, LNilS a (GR zeros n) (m0 - 1))
      else (mn, LCons e'' st' t')
  | _ => (mn, LCons e'' st' t')
  end.

Fixpoint canE (e : ent) : ent :=
  match e with
  | EV v => EV v
  | ET u b r => ET u b (canR (bflag b) r)
  | ES a z r => ES a z (canR false r)
  end
with canL (q : nat) (L : lst) : list nat * lst :=
  match L with
  | LNilV | LNilP => (zeros, LNilV)
  | LNilS a r m0 => match canR false r with GR sr nr => (sr, LNilS a (GR zeros nr) m0) end
  | LCons e s t => let e' := canE e in let '(mt, t') := canL q t in cell q e' (sadd mt s) t'
  end
with canR (p : bool) (r : gref) : gref :=
  match r with GR s n => let '(m, n') := canN p n in GR (srestr (hasN n') (sadd m s)) n' end
with canN (p : bool) (n : gnode) : list nat * gnode :=
  match n with
  | GN d ls =>
      let d' := canD d in
      let ls' := canLs p 0 ls in
      let m := vec (fun k => oget (omin (dmin d' k) (lsmin 0 ls' k))) in
      (m, GN (ddown d' m) (lsdown 0 ls' m))
  end
with canLs (p : bool) (q : nat) (ls : lsts) : lsts :=
  match ls with
  | LsNil => LsNil
  | LsCons s L r =>
      if phslot p q then LsCons zeros LNilP (canLs p (S q) r)
      else let '(m, L') := canL q L in LsCons (sadd m s) L' (canLs p (S q) r)
  end
with canD (d : gdef) : gdef :=
  match d with DV => DV | DS a r => DS a (canR false r) end.

(** ** Helpers *)

Lemma vec_len f : length (vec f) = length labs.
Proof. unfold vec; rewrite length_map, length_seq; reflexivity. Qed.

Lemma sget_vec f k : k < length labs -> sget (vec f) k = f k.
Proof. apply sget_map_seq. Qed.

Lemma vec_zeros : vec (fun _ => 0) = zeros.
Proof.
  unfold vec, GForm.zeros.
  assert (H : forall n st, map (fun _ : nat => 0) (seq st n) = repeat 0 n)
    by (induction n as [|n IH]; intros st; [reflexivity|cbn [seq map repeat]; f_equal; apply IH]).
  apply H.
Qed.

Lemma shv_agree s s' w :
  (forall k, k < length labs -> lab k = v_label w -> sget s k = sget s' k) -> GForm.shv labs s w = GForm.shv labs s' w.
Proof.
  intros H; destruct w as [l i]; unfold GForm.shv; cbn [v_label v_index].
  destruct (pos labs l) as [k|] eqn:E; [|reflexivity].
  destruct (pos_some labs _ _ E) as [Hk Hl]; rewrite (H k Hk Hl); reflexivity.
Qed.

Lemma fpost_agree s s' f : (forall w, outs f w -> GForm.shv labs s w = GForm.shv labs s' w) -> feq (fpost s f) (fpost s' f).
Proof.
  induction f as [v|u b k IH|a z k IH]; intros H; cbn [GForm.fpost feq].
  - apply H; constructor.
  - repeat split; intros y Hy; apply IH; intros w Hw; apply H; apply outs_T with y; assumption.
  - repeat split; intros y; apply IH; intros w Hw; apply H; apply outs_S with y; assumption.
Qed.

(** Two shifts that agree on the labels a family outputs act the same on it. *)
Lemma fpost_agree_has {X} (D : X -> Prop) F s s' x : D x ->
  (forall k, k < length labs -> Has labs D F k -> sget s k = sget s' k) -> feq (fpost s (F x)) (fpost s' (F x)).
Proof.
  intros Hx H; apply fpost_agree; intros w Hw; apply shv_agree; intros k Hk Hl.
  apply H; [exact Hk|]; exists (v_index w); exists x; split; [exact Hx|]; destruct w as [l i]; cbn in Hl; subst l; exact Hw.
Qed.

Lemma sget_srestr h s k : k < length labs -> sget (srestr h s) k = if h k then sget s k else 0.
Proof. intros Hk; unfold srestr; rewrite sget_vec by exact Hk; reflexivity. Qed.

Lemma sget_ssub s t k : k < length labs -> sget (ssub s t) k = sget s k - sget t k.
Proof. intros Hk; unfold ssub; rewrite sget_vec by exact Hk; reflexivity. Qed.

Lemma sget_sadd' s t k : k < length labs -> sget (sadd s t) k = sget s k + sget t k.
Proof. apply sget_sadd. Qed.

Lemma omin_le a b x : omin a b = Some x -> (forall y, a = Some y -> x <= y) /\ (forall y, b = Some y -> x <= y).
Proof.
  destruct a as [a|], b as [b|]; cbn; intros E; try discriminate; injection E as <-;
    split; intros y E'; try discriminate; injection E' as <-; lia.
Qed.

Lemma omin_some_l a b y : a = Some y -> exists x, omin a b = Some x.
Proof. intros ->; destruct b; cbn; eauto. Qed.

Lemma omin_some_r a b y : b = Some y -> exists x, omin a b = Some x.
Proof. intros ->; destruct a; cbn; eauto. Qed.

Lemma omin_cases a b x : omin a b = Some x -> a = Some x \/ b = Some x.
Proof.
  destruct a as [y|], b as [z|]; cbn; intros E; try discriminate; injection E as <-; auto.
  destruct (Nat.min_spec y z) as [[_ ->]|[_ ->]]; auto.
Qed.

Lemma hasE_spec e k : cent labs e -> k < length labs -> hasE e k = true <-> exists i, outs (em e) (mk_rvar (lab k) i).
Proof. intros; apply (proj1 (has_spec_all labs Hnd)); assumption. Qed.

Lemma hasL_spec q L k : q < length labs -> clst labs q L -> k < length labs -> hasL q L k = true <-> Has labs all_nat (lm q L) k.
Proof. intros; apply (proj1 (proj2 (has_spec_all labs Hnd))); assumption. Qed.

Lemma hasR_spec p r k : cref labs p r -> k < length labs -> GCanon.hasR labs r k = true <-> Has labs (Dom p) (rm r) k.
Proof. intros; apply (proj1 (proj2 (proj2 (has_spec_all labs Hnd)))); assumption. Qed.

Lemma hasN_spec p n k : cnode labs p n -> k < length labs -> hasN n k = true <-> Has labs (Dom p) (nm n) k.
Proof. intros; apply (proj1 (proj2 (proj2 (proj2 (has_spec_all labs Hnd))))); assumption. Qed.

(** Taking a shift [m] out of a canonical reference. *)
Lemma rdown_spec p s n m : cref labs p (GR s n) -> (forall k, k < length labs -> hasN n k = true -> sget m k <= sget s k) ->
  cref labs p (rdown (GR s n) m) /\ forall v, Dom p v -> feq (rm (GR s n) v) (fpost m (rm (rdown (GR s n) m) v)).
Proof.
  intros (Hc & Hf & Hr) Hle; cbn [rdown]; split.
  - cbn [cref]; split; [exact Hc|split; [exact Hf|]]; split; [apply vec_len|].
    intros k Hk Hp; rewrite sget_srestr in Hp by exact Hk; destruct (hasN n k) eqn:E; [|lia].
    apply (hasN_spec p n k Hc Hk) in E as (i & Ho); exists i; exact Ho.
  - intros v Hv; cbn [GForm.rm]; eapply feq_trans; [|apply (fpost_sadd labs)].
    apply (fpost_agree_has (Dom p) (nm n)); [exact Hv|]; intros k Hk Hh.
    apply (hasN_spec p n k Hc Hk) in Hh; rewrite sget_sadd', sget_srestr, sget_ssub, Hh by exact Hk.
    specialize (Hle k Hk Hh); lia.
Qed.

Lemma rmin_out p s n k : cref labs p (GR s n) -> k < length labs ->
  (hasN n k = true -> Out (Dom p) (rm (GR s n)) (mk_rvar (lab k) (sget s k)))
  /\ (forall i, Out (Dom p) (rm (GR s n)) (mk_rvar (lab k) i) -> sget s k <= i).
Proof.
  intros (Hc & Hf & Hr) Hk; split.
  - intros Hh; apply (hasN_spec p n k Hc Hk) in Hh as (i & Ho); apply Hf in Ho; [|exact Hk].
    apply (Out_post_lab labs Hnd); [exact Hk|]; rewrite Nat.sub_diag; split; [lia|exact Ho].
  - intros i Ho; apply (Out_post_lab labs Hnd) in Ho as [Hle _]; [exact Hle|exact Hk].
Qed.

(** An entry's least output index on a label it outputs is [emin]. *)
Lemma emin_spec e k : cent labs e -> k < length labs ->
  (hasE e k = true -> outs (em e) (mk_rvar (lab k) (emin e k)))
  /\ (forall i, outs (em e) (mk_rvar (lab k) i) -> emin e k <= i).
Proof.
  intros Hc Hk; destruct e as [v|u b [s n]|a z [s n]]; cbn [hasE emin GForm.em] in *.
  - split.
    + intros E; destruct (label_eqb_spec (v_label v) (lab k)) as [He|]; [|discriminate].
      destruct v as [l i]; cbn in He |- *; subst l; constructor.
    + intros i Ho; inversion Ho; subst; cbn; lia.
  - destruct (rmin_out _ s n k Hc Hk) as [H1 H2]; split.
    + intros Hh; apply outs_term, H1, Hh.
    + intros i Ho; apply outs_term in Ho; apply H2, Ho.
  - destruct (rmin_out false s n k Hc Hk) as [H1 H2]; split.
    + intros Hh; apply outs_stuck, H1, Hh.
    + intros i Ho; apply outs_stuck in Ho; apply H2, Ho.
Qed.

Lemma edown_spec e m : cent labs e -> (forall k, k < length labs -> hasE e k = true -> sget m k <= emin e k) ->
  cent labs (edown e m) /\ feq (em e) (fpost m (em (edown e m)))
  /\ (forall k, hasE (edown e m) k = hasE e k)
  /\ (forall k, k < length labs -> hasE e k = true -> emin (edown e m) k = emin e k - sget m k).
Proof.
  intros Hc Hle; destruct e as [v|u b [s n]|a z [s n]]; cbn [edown cent hasE emin] in *.
  - destruct v as [l i]; cbn [v_label v_index] in *.
    destruct (pos labs l) as [k|] eqn:E.
    + destruct (pos_some labs _ _ E) as [Hk Hl].
      assert (Hm : sget m k <= i) by (apply Hle; [exact Hk|rewrite Hl, label_eqb_refl; reflexivity]).
      split; [exact I|split; [|split]].
      * cbn [GForm.em GForm.fpost feq]; unfold GForm.shv; cbn [v_label v_index]; rewrite E; f_equal; lia.
      * intros k'; reflexivity.
      * intros k' Hk' Hh; cbn [v_index].
        destruct (label_eqb_spec l (lab k')) as [He|]; [|discriminate].
        rewrite He in Hl; apply (lab_inj labs Hnd) in Hl; [subst k'; reflexivity|exact Hk|exact Hk'].
    + split; [exact I|split; [|split]].
      * cbn [GForm.em GForm.fpost feq]; unfold GForm.shv; cbn [v_label v_index]; rewrite E; reflexivity.
      * intros k'; reflexivity.
      * intros k' Hk' Hh; exfalso; destruct (label_eqb_spec l (lab k')) as [He|]; [|discriminate].
        unfold GForm.pos in E; apply (pos_from_none _ _ _ E); rewrite He; apply nth_In, Hk'.
  - destruct (rdown_spec _ s n m Hc Hle) as [Hc' Hm]; split; [exact Hc'|split; [|split]].
    + cbn [GForm.em GForm.fpost feq]; repeat split; intros y Hy; apply Hm.
      destruct b; [left; reflexivity|right; exact (Hy eq_refl)].
    + intros k; reflexivity.
    + intros k Hk Hh; cbn [rdown emin]; cbn [GCanon.hasR] in Hh; rewrite sget_srestr, sget_ssub, Hh by exact Hk; reflexivity.
  - destruct (rdown_spec false s n m Hc Hle) as [Hc' Hm]; split; [exact Hc'|split; [|split]].
    + cbn [GForm.em GForm.fpost feq]; repeat split; intros y; apply Hm; left; reflexivity.
    + intros k; reflexivity.
    + intros k Hk Hh; cbn [rdown emin]; cbn [GCanon.hasR] in Hh; rewrite sget_srestr, sget_ssub, Hh by exact Hk; reflexivity.
Qed.

(** Lists from canonicalisation keep a nil's reference unshifted. *)
Definition nilsz (L : lst) : Prop := match L with LNilS _ (GR s _) _ => s = zeros | _ => True end.

Lemma ent_unique e1 e2 : cent labs e1 -> cent labs e2 -> feq (em e1) (em e2) -> e1 = e2.
Proof. intros; apply (proj1 (uniq_all labs Hnd (S (esz e1 + esz e2)))); [lia|assumption..]. Qed.

Lemma ent_eqb_refl e : ent_eqb e e = true.
Proof. apply (proj1 eqb_spec_all); reflexivity. Qed.

Lemma cell_spec q e' st t' : q < length labs -> cent labs e' -> clst labs q t' -> factored labs all_nat (lm q t') -> nilsz t' ->
  let '(m, L) := cell q e' st t' in
  clst labs q L /\ factored labs all_nat (lm q L) /\ nilsz L
  /\ forall j, feq (lm q (LCons e' st t') j) (fpost m (lm q L j)).
Proof.
  intros Hq He Ht Hft Hz; unfold cell.
  set (mn := vec _).
  assert (Hmn : forall k, k < length labs ->
            (hasE e' k = true -> sget mn k <= emin e' k) /\ (hasL q t' k = true -> sget mn k <= sget st k)
            /\ ((hasE e' k = true \/ hasL q t' k = true) ->
                (hasE e' k = true /\ sget mn k = emin e' k) \/ (hasL q t' k = true /\ sget mn k = sget st k))).
  { intros k Hk; unfold mn; rewrite sget_vec by exact Hk.
    destruct (hasE e' k), (hasL q t' k); cbn [omin oget].
    - split; [lia|split; [lia|]]; intros _.
      destruct (Nat.min_spec (emin e' k) (sget st k)) as [[_ ->]|[_ ->]]; [left|right]; auto.
    - split; [lia|split; [discriminate|]]; intros _; left; auto.
    - split; [discriminate|split; [lia|]]; intros _; right; auto.
    - split; [discriminate|split; [discriminate|]]; intros [H|H]; discriminate. }
  destruct (edown_spec e' mn He (fun k Hk Hh => proj1 (Hmn k Hk) Hh)) as (He'' & Hm'' & Hh'' & Hmin'').
  set (e'' := edown e' mn) in *; set (st' := srestr (hasL q t') (ssub st mn)).
  (* the factored cell means the cell *)
  assert (HM : forall j, feq (lm q (LCons e' st t') j) (fpost mn (lm q (LCons e'' st' t') j))).
  { intros [|j]; cbn [GForm.lm]; [exact Hm''|].
    eapply feq_trans; [|apply (fpost_sadd labs)].
    apply (fpost_agree_has all_nat (lm q t')); [exact I|]; intros k Hk Hh.
    apply (hasL_spec q t' k Hq Ht Hk) in Hh; unfold st'; rewrite sget_sadd', sget_srestr, sget_ssub, Hh by exact Hk.
    specialize (proj1 (proj2 (Hmn k Hk)) Hh); lia. }
  assert (Hrt : restricted labs all_nat (lm q t') st').
  { split; [apply vec_len|]; intros k Hk Hp; unfold st' in Hp; rewrite sget_srestr in Hp by exact Hk.
    destruct (hasL q t' k) eqn:E; [|lia]; apply (hasL_spec q t' k Hq Ht Hk) in E; exact E. }
  (* the factored cell is factored *)
  assert (HF : factored labs all_nat (lm q (LCons e'' st' t'))).
  { intros k i Hk (j & _ & Ho).
    assert (Hhas : hasE e' k = true \/ hasL q t' k = true).
    { destruct j as [|j]; cbn [GForm.lm] in Ho.
      - left; rewrite <- Hh''; apply (hasE_spec e'' k He'' Hk); exists i; exact Ho.
      - right; apply (hasL_spec q t' k Hq Ht Hk).
        apply (Has_post labs Hnd all_nat (lm q t') st' k Hk); exists i, j; split; [exact I|exact Ho]. }
    destruct (proj2 (proj2 (Hmn k Hk)) Hhas) as [[Hh Hv]|[Hh Hv]].
    - exists 0; split; [exact I|]; cbn [GForm.lm].
      assert (E0 : emin e'' k = 0) by (rewrite (Hmin'' k Hk Hh); lia).
      replace (mk_rvar (lab k) 0) with (mk_rvar (lab k) (emin e'' k)) by (rewrite E0; reflexivity).
      apply (emin_spec e'' k He'' Hk); rewrite Hh''; exact Hh.
    - apply (hasL_spec q t' k Hq Ht Hk) in Hh as (i0 & Ho0); apply Hft in Ho0 as (j0 & _ & Ho0); [|exact Hk].
      exists (S j0); split; [exact I|]; cbn [GForm.lm]; apply (outs_fpost labs).
      exists (mk_rvar (lab k) 0); split; [exact Ho0|]; rewrite (shv_lab labs Hnd) by exact Hk.
      unfold st'; rewrite sget_srestr, sget_ssub by exact Hk.
      destruct (hasL q t' k) eqn:E; [rewrite Hv; f_equal; lia|reflexivity]. }
  assert (Hplain : clst labs q (LCons e'' st' t') -> clst labs q (LCons e'' st' t') /\ factored labs all_nat (lm q (LCons e'' st' t'))
                   /\ nilsz (LCons e'' st' t') /\ forall j, feq (lm q (LCons e' st t') j) (fpost mn (lm q (LCons e'' st' t') j)))
    by (intros Hc; exact (conj Hc (conj HF (conj I HM)))).
  assert (Est : st' = srestr (hasL q t') (ssub st mn)) by reflexivity.
  clearbody e'' st'.
  destruct t' as [| |a [sz n] m0|e0 s0 t0].
  - (* LNilV *)
    destruct ((0 <? sget st' q) && ent_eqb e'' (EV (mk_rvar (lab q) (sget st' q - 1)))) eqn:Ec.
    + apply andb_true_iff in Ec as [Hp Heq]; apply Nat.ltb_lt in Hp.
      apply (proj1 (eqb_spec_all)) in Heq; rewrite Heq in HM.
      refine (conj I (conj (nilv_factored labs Hnd q Hq) (conj I _))).
      intros j; eapply feq_trans; [apply HM|]; destruct j as [|j]; cbn [GForm.lm GForm.em GForm.fpost feq].
      * rewrite !(shv_lab labs Hnd) by exact Hq; rewrite sget_sadd', sget_srestr, Nat.eqb_refl, sget_ssub, sget_ush, Nat.eqb_refl by exact Hq.
        f_equal; lia.
      * rewrite !(shv_lab labs Hnd) by exact Hq; rewrite sget_sadd', sget_srestr, Nat.eqb_refl, sget_ssub, sget_ush, Nat.eqb_refl by exact Hq.
        f_equal; lia.
    + apply Hplain; cbn [clst]; refine (conj He'' (conj Ht (conj Hft (conj Hrt _)))).
      intros [Hp Ha].
      assert (E : e'' = EV (mk_rvar (lab q) (sget st' q - 1))) by (apply ent_unique; [exact He''|exact I|exact Ha]).
      subst e''; rewrite ent_eqb_refl, andb_true_r in Ec; apply Nat.ltb_ge in Ec; lia.
  - (* LNilP *)
    cbn [clst] in Ht; contradiction.
  - (* LNilS *)
    cbn [nilsz] in Hz; subst sz; cbn [clst] in Ht.
    assert (Hcn : cnode labs false n /\ factored labs (Dom false) (nm n)) by (destruct Ht as (Hc & Hf & _); auto).
    destruct Hcn as [Hcn Hfn].
    assert (HES : cent labs (ES a (mk_rvar (lab q) (m0 - 1)) (GR st' n))).
    { cbn [cent cref]; split; [exact Hcn|split; [exact Hfn|]]; split; [rewrite Est; apply vec_len|].
      intros k Hk Hp; rewrite Est in Hp; rewrite sget_srestr in Hp by exact Hk.
      destruct (hasL q (LNilS a (GR zeros n) m0) k) eqn:E; [|lia]; cbn [GCanon.hasL GCanon.hasR] in E.
      apply (hasN_spec false n k Hcn Hk) in E; exact E. }
    assert (Hst : forall y, feq (fpost st' (rm (GR zeros n) y)) (rm (GR st' n) y))
      by (intros y; cbn [GForm.rm]; apply (feq_fpost labs), (fpost_zeros labs)).
    destruct ((0 <? m0) && ent_eqb e'' (ES a (mk_rvar (lab q) (m0 - 1)) (GR st' n))) eqn:Ec.
    + apply andb_true_iff in Ec as [Hp Heq]; apply Nat.ltb_lt in Hp.
      apply (proj1 (eqb_spec_all)) in Heq; rewrite Heq in HM.
      refine (conj Ht (conj (nils_factored labs q a n (m0 - 1) Hfn) (conj eq_refl _))).
      intros j; eapply feq_trans; [apply HM|]; destruct j as [|j]; cbn [GForm.lm GForm.em GForm.fpost GForm.rm feq].
      * split; [reflexivity|split; [f_equal; lia|intros y]].
        eapply feq_trans; [|apply feq_sym, (fpost_sadd labs)].
        apply (feq_fpost labs), (feq_fpost labs), feq_sym, (fpost_zeros labs).
      * split; [reflexivity|split; [f_equal; lia|intros y]].
        apply feq_sym, (fpost_sadd labs).
    + apply Hplain; cbn [clst]; refine (conj He'' (conj _ (conj Hft (conj Hrt _)))); [exact Ht|].
      intros [Hp Ha].
      assert (E : e'' = ES a (mk_rvar (lab q) (m0 - 1)) (GR st' n)).
      { apply ent_unique; [exact He''|exact HES|].
        eapply feq_trans; [exact Ha|]; cbn [GForm.em feq]; repeat split; intros y; apply Hst. }
      subst e''; rewrite ent_eqb_refl, andb_true_r in Ec; apply Nat.ltb_ge in Ec; lia.
  - (* LCons *)
    apply Hplain; cbn [clst]; refine (conj He'' (conj Ht (conj Hft (conj Hrt _)))); cbn [absorb]; intros [].
Qed.

(** ** The node case *)

Lemma lsmin_spec ls : forall q k,
  (forall x, lsmin q ls k = Some x ->
     (forall j, j < lsts_len ls -> hasL (q + j) (lnth j ls) k = true -> x <= sget (snth j ls) k)
     /\ exists j, j < lsts_len ls /\ hasL (q + j) (lnth j ls) k = true /\ sget (snth j ls) k = x)
  /\ (lsmin q ls k = None -> forall j, j < lsts_len ls -> hasL (q + j) (lnth j ls) k = false).
Proof.
  induction ls as [|s L r IH]; intros q k; cbn [lsmin lsts_len].
  - split; [discriminate|intros _ j Hj; lia].
  - destruct (IH (S q) k) as [IHs IHn].
    assert (Hshift : forall j, q + S j = S q + j) by (intros; lia).
    destruct (hasL q L k) eqn:EL, (lsmin (S q) r k) as [b|] eqn:Eb; cbn [omin].
    + split; [|discriminate]; intros x E; injection E as <-; destruct (IHs b eq_refl) as [Hb (j0 & Hj0 & Hh0 & Hv0)].
      split.
      * intros [|j] Hj Hh; cbn [lnth snth] in *; [lia|]; rewrite Hshift in Hh; specialize (Hb j ltac:(lia) Hh); lia.
      * destruct (Nat.min_spec (sget s k) b) as [[_ ->]|[_ ->]].
        -- exists 0; cbn; rewrite Nat.add_0_r; repeat split; [lia|exact EL].
        -- exists (S j0); cbn [lnth snth]; rewrite Hshift; repeat split; [lia|exact Hh0|exact Hv0].
    + split; [|discriminate]; intros x E; injection E as <-; split.
      * intros [|j] Hj Hh; cbn [lnth snth] in *; [lia|]; rewrite Hshift in Hh; rewrite (IHn eq_refl j ltac:(lia)) in Hh; discriminate.
      * exists 0; cbn; rewrite Nat.add_0_r; repeat split; [lia|exact EL].
    + split; [|discriminate]; intros x E; injection E as <-; destruct (IHs b eq_refl) as [Hb (j0 & Hj0 & Hh0 & Hv0)]; split.
      * intros [|j] Hj Hh; cbn [lnth snth] in *; [rewrite Nat.add_0_r in Hh; congruence|]; rewrite Hshift in Hh; apply Hb; [lia|exact Hh].
      * exists (S j0); cbn [lnth snth]; rewrite Hshift; repeat split; [lia|exact Hh0|exact Hv0].
    + split; [discriminate|]; intros _ [|j] Hj; cbn [lnth]; [rewrite Nat.add_0_r; exact EL|]; rewrite Hshift; apply IHn; [reflexivity|lia].
Qed.


Lemma lsdown_len ls : forall q m, lsts_len (lsdown q ls m) = lsts_len ls.
Proof. induction ls as [|s L r IH]; intros q m; cbn; auto. Qed.

Lemma lsdown_lnth ls : forall q m j, lnth j (lsdown q ls m) = lnth j ls.
Proof. induction ls as [|s L r IH]; intros q m [|j]; cbn; auto. Qed.

Lemma lsdown_snth ls : forall q m j, j < lsts_len ls ->
  snth j (lsdown q ls m) = srestr (hasL (q + j) (lnth j ls)) (ssub (snth j ls) m).
Proof.
  induction ls as [|s L r IH]; intros q m [|j] Hj; cbn in Hj |- *; try lia.
  - rewrite Nat.add_0_r; reflexivity.
  - rewrite IH by lia; replace (q + S j) with (S q + j) by lia; reflexivity.
Qed.

Lemma clsts_intro p ls : forall q, q + lsts_len ls = length labs ->
  (forall j, j < lsts_len ls ->
     if phslot p (q + j) then lnth j ls = LNilP /\ snth j ls = zeros
     else clst labs (q + j) (lnth j ls) /\ factored labs all_nat (lm (q + j) (lnth j ls))
          /\ restricted labs all_nat (lm (q + j) (lnth j ls)) (snth j ls)) ->
  clsts labs p q ls.
Proof.
  induction ls as [|s L r IH]; intros q Hl H; cbn [clsts]; [exact I|]; cbn [lsts_len] in Hl.
  split.
  - specialize (H 0 ltac:(cbn; lia)); rewrite Nat.add_0_r in H; cbn [lnth snth] in H.
    unfold phslot in H; destruct (p && _); exact H.
  - apply IH; [lia|]; intros j Hj; specialize (H (S j) ltac:(cbn; lia)); cbn [lnth snth] in H.
    replace (S q + j) with (q + S j) by lia; exact H.
Qed.

Lemma dmin_spec d k x : dmin d k = Some x -> exists a s n, d = DS a (GR s n) /\ hasN n k = true /\ x = sget s k.
Proof.
  destruct d as [|a [s n]]; cbn; [discriminate|].
  destruct (hasN n k) eqn:E; [intros H; injection H as <-; eauto 6|discriminate].
Qed.

Definition precan (p : bool) (ls : lsts) : Prop :=
  forall j, j < lsts_len ls ->
    if phslot p j then lnth j ls = LNilP /\ snth j ls = zeros
    else clst labs j (lnth j ls) /\ factored labs all_nat (lm j (lnth j ls)).

Lemma srestr_false s : srestr (fun _ => false) s = zeros.
Proof. unfold srestr; apply vec_zeros. Qed.

Lemma node_spec p d' ls' : cdef labs d' -> lsts_len ls' = length labs -> precan p ls' ->
  let m := vec (fun k => oget (omin (dmin d' k) (lsmin 0 ls' k))) in
  cnode labs p (GN (ddown d' m) (lsdown 0 ls' m)) /\ factored labs (Dom p) (nm (GN (ddown d' m) (lsdown 0 ls' m)))
  /\ forall v, Dom p v -> feq (nm (GN d' ls') v) (fpost m (nm (GN (ddown d' m) (lsdown 0 ls' m)) v)).
Proof.
  intros Hd Hl Hpc m.
  (* the least shift is below every component, and attained by one *)
  assert (Hmd : forall k y, k < length labs -> dmin d' k = Some y -> sget m k <= y).
  { intros k y Hk E; unfold m; rewrite sget_vec by exact Hk; rewrite E.
    destruct (lsmin 0 ls' k); cbn; lia. }
  assert (Hml : forall k j, k < length labs -> j < length labs -> hasL j (lnth j ls') k = true -> sget m k <= sget (snth j ls') k).
  { intros k j Hk Hj Hh; unfold m; rewrite sget_vec by exact Hk.
    destruct (lsmin 0 ls' k) as [x|] eqn:E.
    - destruct (proj1 (lsmin_spec ls' 0 k) x E) as [Hb _]; specialize (Hb j ltac:(lia) Hh).
      destruct (dmin d' k); cbn [omin oget]; lia.
    - pose proof (proj2 (lsmin_spec ls' 0 k) E j ltac:(lia)) as Hf; cbn [Nat.add] in Hf; congruence. }
  assert (Hatt : forall k, k < length labs ->
            (exists j, j < length labs /\ hasL j (lnth j ls') k = true /\ sget (snth j ls') k = sget m k)
            \/ (exists a s n, d' = DS a (GR s n) /\ hasN n k = true /\ sget s k = sget m k)
            \/ (dmin d' k = None /\ lsmin 0 ls' k = None)).
  { intros k Hk; unfold m; rewrite sget_vec by exact Hk.
    destruct (omin (dmin d' k) (lsmin 0 ls' k)) as [x|] eqn:E.
    - apply omin_cases in E as [E|E]; cbn [oget].
      + right; left; destruct (dmin_spec d' k x E) as (a & s & n & -> & Hh & ->); eauto 6.
      + left; destruct (proj1 (lsmin_spec ls' 0 k) x E) as [_ (j & Hj & Hh & Hv)]; exists j; repeat split; auto; lia.
    - right; right; destruct (dmin d' k), (lsmin 0 ls' k); cbn in E; try discriminate; auto. }
  set (d'' := ddown d' m); set (ls'' := lsdown 0 ls' m).
  assert (Hl'' : lsts_len ls'' = length labs) by (unfold ls''; rewrite lsdown_len; exact Hl).
  assert (Hlnth : forall j, lnth j ls'' = lnth j ls') by (intros; apply lsdown_lnth).
  assert (Hsnth : forall j, j < length labs -> snth j ls'' = srestr (hasL j (lnth j ls')) (ssub (snth j ls') m))
    by (intros; unfold ls''; rewrite lsdown_snth by lia; reflexivity).
  (* the default *)
  assert (Hd'' : cdef labs d'' /\ forall v, ~ In (v_label v) labs -> feq (dm d' v) (fpost m (dm d'' v))).
  { unfold d''; destruct d' as [|a [s n]]; cbn [ddown cdef GForm.dm] in *.
    - split; [exact I|]; intros v Hv; cbn [GForm.fpost feq]; symmetry; apply (shv_out labs), Hv.
    - assert (Hle : forall k, k < length labs -> hasN n k = true -> sget m k <= sget s k).
      { intros k Hk Hh; apply Hmd; [exact Hk|]; cbn [dmin]; rewrite Hh; reflexivity. }
      destruct (rdown_spec false s n m Hd Hle) as [Hc' Hm']; split; [exact Hc'|].
      intros v _; cbn [GForm.fpost feq]; repeat split; intros y; apply Hm'; left; reflexivity. }
  destruct Hd'' as [Hcd Hmd''].
  (* the lists *)
  assert (Hcl : clsts labs p 0 ls'').
  { apply clsts_intro; [exact Hl''|]; intros j Hj; rewrite Hl'' in Hj; cbn [Nat.add]; specialize (Hpc j ltac:(lia)).
    rewrite Hlnth, Hsnth by exact Hj; destruct (phslot p j).
    - destruct Hpc as [-> _]; split; [reflexivity|]; cbn [GCanon.hasL]; apply srestr_false.
    - destruct Hpc as [Hc Hf]; split; [exact Hc|split; [exact Hf|]]; split; [apply vec_len|].
      intros k Hk Hp; rewrite sget_srestr in Hp by exact Hk; destruct (hasL j (lnth j ls') k) eqn:E; [|lia].
      apply (hasL_spec j _ k Hj Hc Hk) in E; exact E. }
  (* a component reaching label k gives the node an output at index 0 *)
  assert (Hzero : forall k, k < length labs -> (dmin d' k <> None \/ lsmin 0 ls' k <> None) ->
            Out (Dom p) (nm (GN d'' ls'')) (mk_rvar (lab k) 0)).
  { intros k Hk Hsome; destruct (Hatt k Hk) as [(j & Hj & Hh & Hv)|[(a & s & n & Ed & Hh & Hv)|[E1 E2]]].
    - pose proof (Hpc j ltac:(lia)) as Hpj; destruct (phslot p j) eqn:Eph.
      + destruct Hpj as [EL _]; rewrite EL in Hh; discriminate.
      + destruct Hpj as [Hc Hf]; pose proof Hh as Hh'.
        apply (hasL_spec j _ k Hj Hc Hk) in Hh' as (i0 & Ho0); apply Hf in Ho0 as (i1 & _ & Ho1); [|exact Hk].
        exists (mk_rvar (lab j) i1); split.
        * unfold phslot in Eph; destruct p; [right; cbn in Eph; destruct (lab j); [discriminate|discriminate]|left; reflexivity].
        * rewrite (nm_lab labs Hnd) by assumption; rewrite lsts_get_nth by lia; cbn [fst snd].
          rewrite Hlnth, Hsnth by exact Hj; apply (outs_fpost labs); exists (mk_rvar (lab k) 0); split; [exact Ho1|].
          rewrite (shv_lab labs Hnd) by exact Hk; rewrite sget_srestr, Hh, sget_ssub by exact Hk; f_equal; lia.
    - subst d'; unfold d''; cbn [ddown rdown].
      destruct Hd as (Hcn & Hfn & _); apply (hasN_spec false n k Hcn Hk) in Hh as Hh'.
      destruct Hh' as (i0 & Ho0); apply Hfn in Ho0; [|exact Hk].
      destruct (fresh_label labs) as [fs Hfs]; exists (mk_rvar (Some fs) 0); split; [right; discriminate|].
      rewrite (nm_out labs) by (exact Hl'' || exact Hfs); cbn [GForm.dm]; apply outs_stuck.
      cbn [GForm.rm]; apply (Out_post_lab labs Hnd); [exact Hk|]; rewrite sget_srestr, Hh, sget_ssub by exact Hk.
      replace (0 - (sget s k - sget m k)) with 0 by lia; split; [lia|exact Ho0].
    - destruct Hsome; contradiction. }
  split; [cbn [cnode]; split; [exact Hcd|split; [exact Hcl|exact Hl'']]|split].
  - (* factored *)
    intros k i Hk Ho.
    assert (Hh : Has labs (Dom p) (nm (GN d'' ls'')) k) by (exists i; exact Ho).
    apply (Has_node labs Hnd p d'' ls'' k Hl'' Hk) in Hh as [(q & Hq & Hv & Hh)|Hh]; apply Hzero; [exact Hk| |exact Hk|].
    + right; rewrite Hlnth in Hh; pose proof (Hpc q ltac:(lia)) as Hpq; destruct (phslot p q) eqn:Eph.
      * exfalso; unfold phslot in Eph; destruct p; [|discriminate]; destruct (lab q) eqn:El; [discriminate|].
        destruct Hv as [Hv|Hv]; [discriminate|contradiction].
      * destruct Hpq as [Hc Hf]; apply (hasL_spec q _ k Hq Hc Hk) in Hh.
        intros E; pose proof (proj2 (lsmin_spec ls' 0 k) E q ltac:(lia)) as Hf'; cbn [Nat.add] in Hf'; congruence.
    + left; unfold d'' in Hh; destruct d' as [|a [s n]]; cbn [ddown rdown] in Hh; [contradiction|].
      destruct Hd as (Hcn & _ & _); cbn [GForm.rm] in Hh.
      apply (Has_post labs Hnd (Dom false) (nm n) _ k Hk) in Hh.
      apply (hasN_spec false n k Hcn Hk) in Hh; cbn [dmin]; rewrite Hh; discriminate.
  - (* meaning *)
    intros v Hv.
    destruct (in_dec label_eq_dec (v_label v) labs) as [Hin|Hout].
    + destruct (lab_pos labs v Hin) as (q & Hq & Hlq & _); destruct v as [l i]; cbn in Hlq; subst l.
      rewrite !(nm_lab labs Hnd) by assumption; rewrite !lsts_get_nth by lia; cbn [fst snd].
      rewrite Hlnth, Hsnth by exact Hq.
      pose proof (Hpc q ltac:(lia)) as Hpq; destruct (phslot p q) eqn:Eph.
      * exfalso; unfold phslot in Eph; destruct p; [|discriminate]; destruct Hv as [Hv|Hv]; [discriminate|].
        cbn [v_label] in Hv; destruct (lab q); [discriminate|contradiction].
      * destruct Hpq as [Hc Hf].
        eapply feq_trans; [|apply (fpost_sadd labs)].
        apply (fpost_agree_has all_nat (lm q (lnth q ls'))); [exact I|]; intros k Hk Hh.
        apply (hasL_spec q _ k Hq Hc Hk) in Hh; rewrite sget_sadd', sget_srestr, Hh, sget_ssub by exact Hk.
        specialize (Hml k q Hk Hq Hh); lia.
    + rewrite !(nm_out labs) by assumption; apply Hmd'', Hout.
Qed.



End Canonise.
