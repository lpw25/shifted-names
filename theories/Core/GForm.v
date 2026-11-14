(** * The canonical graph: encoding and uniqueness

    An adjustment is represented by what it does to each variable in the
    free model ([Unique.fres]), stored per label as a list with a uniform
    tail, with sharing kept by references that carry a shift on their
    outputs (see [docs/canonical-graph.md]).

    This file defines the encoding, its meaning in the free model, the
    canonicity conditions (all local), and proves that canonical
    encodings with the same meaning are equal. *)

From Stdlib Require Import String Arith List Lia Bool.
From ShiftedNames.Core Require Import Label Var Normalise Unique.
Import ListNotations.

(** ** The encoding

    Labels are positions in a fixed list [labs] of distinct labels; labels
    outside it are treated by a node's default.  A shift is a list of
    counts, one per position of [labs]. *)

Inductive ent : Type :=
| EV (k i : nat)                              (* the output variable [labs_k, i] *)
| ET (u : nat) (b : option nat) (r : gref)    (* the term [u], payload atom [b], payload [r] *)
| ES (a : nat) (k i : nat) (r : gref)         (* stuck at atom [a] on input [labs_k, i], then [r] *)
with lst : Type :=
| LNilV                                       (* [j ↦] the output [labs_k, j] *)
| LNilP                                       (* not observed: bound inputs of a payload without payload atom *)
| LNilS (a : nat) (r : gref) (m : nat)        (* [j ↦] stuck at [a] on [labs_k, j + m], then [r] *)
| LCons (e : ent) (s : list nat) (t : lst)    (* [e], then [t] with its outputs shifted by [s] *)
with gref : Type :=
| GR (s : list nat) (n : gnode)               (* [n] with its outputs shifted by [s] *)
with gnode : Type :=
| GN (d : gdef) (ls : lsts)                   (* one list per position, a default for other labels *)
with lsts : Type :=
| LsNil
| LsCons (L : lst) (rest : lsts)
with gdef : Type :=
| DV                                          (* other labels: the identity *)
| DS (a : nat) (r : gref).                    (* other labels: stuck at [a], then [r] *)

Scheme ent_ind' := Induction for ent Sort Prop
with lst_ind' := Induction for lst Sort Prop
with gref_ind' := Induction for gref Sort Prop
with gnode_ind' := Induction for gnode Sort Prop
with lsts_ind' := Induction for lsts Sort Prop
with gdef_ind' := Induction for gdef Sort Prop.
Combined Scheme g_ind from ent_ind', lst_ind', gref_ind', gnode_ind', lsts_ind', gdef_ind'.

Section Meaning.

Variable labs : list (option label).

Definition lab (k : nat) : option label := nth k labs None.

Fixpoint pos_from (k : nat) (l : option label) (ls : list (option label)) : option nat :=
  match ls with
  | [] => None
  | l' :: ls' => if label_eqb l' l then Some k else pos_from (S k) l ls'
  end.

Definition pos (l : option label) : option nat := pos_from 0 l labs.

Definition sget (s : list nat) (k : nat) : nat := nth k s 0.

(** Shifting an output. *)
Definition shv (s : list nat) (v : rvar) : rvar :=
  match pos (v_label v) with
  | Some k => mk_rvar (v_label v) (v_index v + sget s k)
  | None => v
  end.

Fixpoint fpost (s : list nat) (f : fres) : fres :=
  match f with
  | FVar v => FVar (shv s v)
  | FTerm u b k => FTerm u b (fun y => fpost s (k y))
  | FStuck a z k => FStuck a z (fun y => fpost s (k y))
  end.

Fixpoint em (e : ent) : fres :=
  match e with
  | EV k i => FVar (mk_rvar (lab k) i)
  | ET u b r => FTerm u b (rm r)
  | ES a k i r => FStuck a (mk_rvar (lab k) i) (rm r)
  end
with lm (k : nat) (L : lst) (j : nat) : fres :=
  match L with
  | LNilV | LNilP => FVar (mk_rvar (lab k) j)
  | LNilS a r m => FStuck a (mk_rvar (lab k) (j + m)) (rm r)
  | LCons e s t => match j with 0 => em e | S j' => fpost s (lm k t j') end
  end
with rm (r : gref) (v : rvar) : fres :=
  match r with GR s n => fpost s (nm n v) end
with nm (n : gnode) (v : rvar) : fres :=
  match n with GN d ls => lsm (dm d) 0 ls v end
with lsm (dflt : rvar -> fres) (k : nat) (ls : lsts) (v : rvar) : fres :=
  match ls with
  | LsNil => dflt v
  | LsCons L rest => if label_eqb (lab k) (v_label v) then lm k L (v_index v) else lsm dflt (S k) rest v
  end
with dm (d : gdef) (v : rvar) : fres :=
  match d with
  | DV => FVar v
  | DS a r => FStuck a v (rm r)
  end.

End Meaning.

(** ** Outputs

    The output variables a result reaches: directly, through a payload
    (on named inputs only when there is no payload atom, as [feq]
    compares), or through the continuation of a stuck atom. *)

Inductive outs : fres -> rvar -> Prop :=
| outs_V v : outs (FVar v) v
| outs_T u b k y w : (b = None -> v_label y <> None) -> outs (k y) w -> outs (FTerm u b k) w
| outs_S a z k y w : outs (k y) w -> outs (FStuck a z k) w.

Lemma feq_outs f g w : feq f g -> outs f w -> outs g w.
Proof.
  intros He Ho; revert g He; induction Ho as [v|u b k y w Hy Ho IH|a z k y w Ho IH];
    intros [v'|u' b' k'|a' z' k'] He; cbn [feq] in He; try contradiction.
  - subst; constructor.
  - destruct He as [<- [<- He]]; apply outs_T with y; [exact Hy|apply IH, He, Hy].
  - destruct He as [<- [<- He]]; apply outs_S with y; apply IH, He.
Qed.

Section Shifts.

Variable labs : list (option label).
Hypothesis Hnd : NoDup labs.

Local Notation lab := (lab labs).
Local Notation pos := (pos labs).
Local Notation shv := (shv labs).
Local Notation fpost := (fpost labs).

Lemma pos_from_some k l ls j : pos_from k l ls = Some j -> k <= j /\ j < k + length ls /\ nth (j - k) ls None = l.
Proof.
  revert k; induction ls as [|l' ls IH]; intros k H; cbn in H; [discriminate|].
  destruct (label_eqb_spec l' l) as [<-|Hne].
  - injection H as <-; rewrite Nat.sub_diag; cbn; repeat split; lia.
  - destruct (IH (S k) H) as (H1 & H2 & H3); cbn [length]; split; [lia|split; [lia|]].
    replace (j - k) with (S (j - S k)) by lia; exact H3.
Qed.

Lemma pos_from_none k l ls : pos_from k l ls = None -> ~ In l ls.
Proof.
  revert k; induction ls as [|l' ls IH]; intros k H; cbn in H; [intros []|].
  destruct (label_eqb_spec l' l) as [<-|Hne]; [discriminate|].
  intros [->|Hin]; [contradiction|exact (IH _ H Hin)].
Qed.

Lemma pos_from_nodup k ls j : NoDup ls -> j < length ls -> pos_from k (nth j ls None) ls = Some (k + j).
Proof.
  revert k j; induction ls as [|l' ls IH]; intros k j Hn Hj; cbn in Hj; [lia|].
  inversion Hn as [|? ? Hni Hn']; subst; destruct j as [|j]; cbn.
  - rewrite label_eqb_refl, Nat.add_0_r; reflexivity.
  - destruct (label_eqb_spec l' (nth j ls None)) as [Heq|_].
    + exfalso; apply Hni; rewrite Heq; apply nth_In; lia.
    + rewrite IH by (assumption || lia); f_equal; lia.
Qed.

Lemma pos_lab k : k < length labs -> pos (lab k) = Some k.
Proof. intros Hk; unfold pos, GForm.lab; rewrite pos_from_nodup by assumption; reflexivity. Qed.

Lemma pos_some l k : pos l = Some k -> k < length labs /\ lab k = l.
Proof.
  intros H; destruct (pos_from_some _ _ _ _ H) as (_ & H2 & H3); rewrite Nat.sub_0_r in H3; split; [lia|exact H3].
Qed.

Lemma shv_label s v : v_label (shv s v) = v_label v.
Proof. unfold shv; destruct (pos (v_label v)); reflexivity. Qed.

Lemma shv_inj s v v' : shv s v = shv s v' -> v = v'.
Proof.
  destruct v as [l i], v' as [l' i']; unfold shv; cbn.
  destruct (pos l) eqn:E, (pos l') eqn:E'; intros H; injection H as -> Hi;
    try (rewrite E in E'; first [discriminate|injection E' as ->]); f_equal; lia.
Qed.

Lemma shv_lab s k i : k < length labs -> shv s (mk_rvar (lab k) i) = mk_rvar (lab k) (i + sget s k).
Proof. intros Hk; unfold shv; cbn; rewrite pos_lab by exact Hk; reflexivity. Qed.

Lemma outs_fpost s f w : outs (fpost s f) w <-> exists w0, outs f w0 /\ w = shv s w0.
Proof.
  split.
  - remember (fpost s f) as g eqn:Eg; intros Ho; revert f Eg; induction Ho as [v|u b k y w Hy Ho IH|a z k y w Ho IH];
      intros [v'|u' b' k'|a' z' k'] Eg; cbn in Eg; try discriminate.
    + injection Eg as ->; exists v'; split; [constructor|reflexivity].
    + injection Eg as -> -> Ek; subst k.
      destruct (IH (k' y) eq_refl) as (w0 & H1 & H2); exists w0; split; [apply outs_T with y; assumption|exact H2].
    + injection Eg as -> -> Ek; subst k.
      destruct (IH (k' y) eq_refl) as (w0 & H1 & H2); exists w0; split; [apply outs_S with y; assumption|exact H2].
  - intros (w0 & Ho & ->); induction Ho as [v|u b k y w Hy Ho IH|a z k y w Ho IH]; cbn [fpost].
    + constructor.
    + apply outs_T with y; assumption.
    + apply outs_S with y; assumption.
Qed.

Lemma feq_fpost s f g : feq f g -> feq (fpost s f) (fpost s g).
Proof.
  revert g; induction f as [v|u b k IH|a z k IH]; intros [v'|u' b' k'|a' z' k'] He; cbn [feq fpost] in *; try contradiction.
  - congruence.
  - destruct He as [<- [<- He]]; repeat split; intros y Hy; apply IH, He, Hy.
  - destruct He as [<- [<- He]]; repeat split; intros y; apply IH, He.
Qed.

Lemma feq_fpost_inv s f g : feq (fpost s f) (fpost s g) -> feq f g.
Proof.
  revert g; induction f as [v|u b k IH|a z k IH]; intros [v'|u' b' k'|a' z' k'] He; cbn [feq fpost] in *; try contradiction.
  - apply (shv_inj s); congruence.
  - destruct He as [<- [<- He]]; repeat split; intros y Hy; apply IH, He, Hy.
  - destruct He as [<- [<- He]]; repeat split; intros y; apply IH, He.
Qed.

(** *** Factoring

    A family of results [F] over a domain [D] is *factored* when, on every
    label of [labs] it outputs, its least output index is 0; a shift is
    *restricted* to [F] when it is 0 on labels [F] does not output.  The
    shift of a factored family is determined by the meaning. *)

Section Factor.

Context {X : Type}.

Definition Out (D : X -> Prop) (F : X -> fres) (w : rvar) : Prop := exists x, D x /\ outs (F x) w.

Definition factored (D : X -> Prop) (F : X -> fres) : Prop :=
  forall k i, k < length labs -> Out D F (mk_rvar (lab k) i) -> Out D F (mk_rvar (lab k) 0).

Definition restricted (D : X -> Prop) (F : X -> fres) (s : list nat) : Prop :=
  length s = length labs /\ forall k, k < length labs -> 0 < sget s k -> exists i, Out D F (mk_rvar (lab k) i).

Lemma Out_post D F s w : Out D (fun x => fpost s (F x)) w <-> exists w0, Out D F w0 /\ w = shv s w0.
Proof.
  split.
  - intros (x & Hx & Ho); apply outs_fpost in Ho as (w0 & Ho & ->); exists w0; split; [exists x; split|]; auto.
  - intros (w0 & (x & Hx & Ho) & ->); exists x; split; [exact Hx|apply outs_fpost; eauto].
Qed.

Lemma Out_feq D F G w : (forall x, D x -> feq (F x) (G x)) -> Out D F w -> Out D G w.
Proof. intros He (x & Hx & Ho); exists x; split; [exact Hx|apply (feq_outs _ _ _ (He x Hx) Ho)]. Qed.

Lemma Out_post_lab D F s k i : k < length labs ->
  Out D (fun x => fpost s (F x)) (mk_rvar (lab k) i) <-> sget s k <= i /\ Out D F (mk_rvar (lab k) (i - sget s k)).
Proof.
  intros Hk; rewrite Out_post; split.
  - intros ([l j] & Ho & Hw); unfold shv in Hw; cbn in Hw.
    destruct (pos l) as [k'|] eqn:Ep.
    + destruct (pos_some _ _ Ep) as [Hk' Hl]; injection Hw as Hkl ->.
      assert (k' = k) as -> by (rewrite <- Hkl, pos_lab in Ep by exact Hk; congruence).
      split; [lia|]; replace (j + sget s k - sget s k) with j by lia; rewrite Hkl; exact Ho.
    + exfalso; injection Hw as Hkl _; rewrite <- Hkl, pos_lab in Ep by exact Hk; discriminate.
  - intros [Hle Ho]; exists (mk_rvar (lab k) (i - sget s k)); split; [exact Ho|].
    rewrite shv_lab by exact Hk; f_equal; lia.
Qed.

Lemma sget_ext s s' : length s = length s' -> (forall k, k < length s -> sget s k = sget s' k) -> s = s'.
Proof.
  revert s'; induction s as [|x s IH]; intros [|x' s'] Hl Hk; cbn in Hl; try discriminate; [reflexivity|].
  f_equal; [apply (Hk 0); cbn; lia|].
  apply IH; [lia|]; intros k Hk'; apply (Hk (S k)); cbn; lia.
Qed.

Lemma factor_half D Fa Fb sa sb :
  factored D Fa -> factored D Fb -> restricted D Fa sa ->
  (forall x, D x -> feq (fpost sa (Fa x)) (fpost sb (Fb x))) ->
  (forall x, D x -> feq (fpost sb (Fb x)) (fpost sa (Fa x))) ->
  forall k, k < length labs -> 0 < sget sa k -> sget sa k = sget sb k.
Proof.
  intros Hfa Hfb [_ Hra] He He' k Hk Hp.
  destruct (Hra k Hk Hp) as [i Ho]; apply Hfa in Ho; [|exact Hk].
  assert (H1 : Out D (fun x => fpost sa (Fa x)) (mk_rvar (lab k) (sget sa k)))
    by (apply Out_post_lab; [exact Hk|]; rewrite Nat.sub_diag; split; [lia|exact Ho]).
  apply (Out_feq _ _ _ _ He) in H1; apply Out_post_lab in H1 as [Hle H1]; [|exact Hk].
  apply Hfb in H1; [|exact Hk].
  assert (H2 : Out D (fun x => fpost sb (Fb x)) (mk_rvar (lab k) (sget sb k)))
    by (apply Out_post_lab; [exact Hk|]; rewrite Nat.sub_diag; split; [lia|exact H1]).
  apply (Out_feq _ _ _ _ He') in H2; apply Out_post_lab in H2 as [Hle' _]; [|exact Hk]; lia.
Qed.

Lemma factor_unique D F1 F2 s1 s2 :
  factored D F1 -> factored D F2 -> restricted D F1 s1 -> restricted D F2 s2 ->
  (forall x, D x -> feq (fpost s1 (F1 x)) (fpost s2 (F2 x))) ->
  s1 = s2 /\ forall x, D x -> feq (F1 x) (F2 x).
Proof.
  intros Hf1 Hf2 Hr1 Hr2 He.
  assert (He' : forall x, D x -> feq (fpost s2 (F2 x)) (fpost s1 (F1 x))) by (intros x Hx; apply feq_sym, He, Hx).
  assert (Hs : s1 = s2).
  { apply sget_ext; [destruct Hr1, Hr2; congruence|]; intros k Hk; rewrite (proj1 Hr1) in Hk.
    destruct (Nat.eq_dec (sget s1 k) 0) as [E1|E1]; [destruct (Nat.eq_dec (sget s2 k) 0) as [E2|E2]|].
    - congruence.
    - symmetry; apply (factor_half D F2 F1 s2 s1); auto; lia.
    - apply (factor_half D F1 F2 s1 s2); auto; lia. }
  subst s2; split; [reflexivity|]; intros x Hx; apply (feq_fpost_inv s1), He, Hx.
Qed.

End Factor.

End Shifts.
