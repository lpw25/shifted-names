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
