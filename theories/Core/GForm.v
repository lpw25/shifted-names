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
| EV (v : rvar)                               (* the output variable [v] *)
| ET (u : nat) (b : option nat) (r : gref)    (* the term [u], payload atom [b], payload [r] *)
| ES (a : nat) (z : rvar) (r : gref)          (* stuck at atom [a] on input [z], then [r] *)
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
| LsCons (s : list nat) (L : lst) (rest : lsts)   (* a list with its outputs shifted by [s] *)
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
  | EV v => FVar v
  | ET u b r => FTerm u b (rm r)
  | ES a z r => FStuck a z (rm r)
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
  | LsCons s L rest => if label_eqb (lab k) (v_label v) then fpost s (lm k L (v_index v)) else lsm dflt (S k) rest v
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

(** ** Canonical encodings *)

Section Canon.

Variable labs : list (option label).
Hypothesis Hnd : NoDup labs.

Local Notation lab := (lab labs).
Local Notation shv := (shv labs).
Local Notation fpost := (fpost labs).
Local Notation em := (em labs).
Local Notation lm := (lm labs).
Local Notation rm := (rm labs).
Local Notation nm := (nm labs).
Local Notation lsm := (lsm labs).
Local Notation dm := (dm labs).
Local Notation factored := (factored labs).
Local Notation restricted := (restricted labs).

Definition zeros : list nat := repeat 0 (length labs).

Lemma sget_zeros k : sget zeros k = 0.
Proof. unfold sget, zeros; revert k; induction (length labs) as [|n IH]; intros [|k]; cbn; auto. Qed.

(** The inputs observed by a reference: all, or (a payload without
    payload atom) the named ones. *)
Definition Dom (p : bool) (v : rvar) : Prop := p = false \/ v_label v <> None.

Definition all_nat (j : nat) : Prop := True.

Fixpoint lsts_len (ls : lsts) : nat := match ls with LsNil => 0 | LsCons _ _ r => S (lsts_len r) end.

Fixpoint lnth (j : nat) (ls : lsts) : lst :=
  match ls, j with
  | LsNil, _ => LNilV
  | LsCons _ L _, 0 => L
  | LsCons _ _ r, S j => lnth j r
  end.

Fixpoint snth (j : nat) (ls : lsts) : list nat :=
  match ls, j with
  | LsNil, _ => []
  | LsCons s _ _, 0 => s
  | LsCons _ _ r, S j => snth j r
  end.

(** A cell that only repeats what its nil gives is not allowed: it would
    be absorbed into the nil. *)
Definition absorb (k : nat) (e : ent) (s : list nat) (t : lst) : Prop :=
  match t with
  | LNilV => 0 < sget s k /\ feq (em e) (FVar (mk_rvar (lab k) (sget s k - 1)))
  | LNilS a r m => 0 < m /\ feq (em e) (FStuck a (mk_rvar (lab k) (m - 1)) (fun y => fpost s (rm r y)))
  | _ => False
  end.

Fixpoint cent (e : ent) : Prop :=
  match e with
  | EV _ => True
  | ET u b r => cref (match b with None => true | Some _ => false end) r
  | ES a z r => cref false r
  end
with clst (k : nat) (L : lst) : Prop :=
  match L with
  | LNilV => True
  | LNilP => False
  | LNilS a r m => cref false r
  | LCons e s t =>
      cent e /\ clst k t /\ factored all_nat (lm k t) /\ restricted all_nat (lm k t) s /\ ~ absorb k e s t
  end
with cref (p : bool) (r : gref) : Prop :=
  match r with GR s n => cnode p n /\ factored (Dom p) (nm n) /\ restricted (Dom p) (nm n) s end
with cnode (p : bool) (n : gnode) : Prop :=
  match n with GN d ls => cdef d /\ clsts p 0 ls /\ lsts_len ls = length labs end
with clsts (p : bool) (k : nat) (ls : lsts) : Prop :=
  match ls with
  | LsNil => True
  | LsCons s L rest =>
      (if p && match lab k with None => true | Some _ => false end then L = LNilP /\ s = zeros
       else clst k L /\ factored all_nat (lm k L) /\ restricted all_nat (lm k L) s)
      /\ clsts p (S k) rest
  end
with cdef (d : gdef) : Prop :=
  match d with DV => True | DS a r => cref false r end.

(** ** Sizes, for the induction *)

Fixpoint esz (e : ent) : nat :=
  match e with EV _ => 1 | ET _ _ r => S (rsz r) | ES _ _ r => S (rsz r) end
with lsz (L : lst) : nat :=
  match L with LNilV | LNilP => 1 | LNilS _ r _ => S (rsz r) | LCons e _ t => S (esz e + lsz t) end
with rsz (r : gref) : nat := match r with GR _ n => S (nsz n) end
with nsz (n : gnode) : nat := match n with GN d ls => S (dsz d + lssz ls) end
with lssz (ls : lsts) : nat := match ls with LsNil => 1 | LsCons _ L r => S (lsz L + lssz r) end
with dsz (d : gdef) : nat := match d with DV => 1 | DS _ r => S (rsz r) end.

(** ** Lemmas *)

Lemma lab_inj k k' : k < length labs -> k' < length labs -> lab k = lab k' -> k = k'.
Proof.
  intros Hk Hk' He; pose proof (pos_lab labs Hnd k Hk) as E; pose proof (pos_lab labs Hnd k' Hk') as E'.
  rewrite He in E; congruence.
Qed.

Lemma slen_app s1 s2 : String.length (s1 ++ s2) = String.length s1 + String.length s2.
Proof. induction s1; cbn; congruence. Qed.

Lemma fresh_label : exists s, ~ In (Some s) labs.
Proof.
  set (big := fold_right (fun l acc => match l with Some s => (s ++ acc)%string | None => acc end) ""%string labs).
  assert (Hb : forall s, In (Some s) labs -> String.length s <= String.length big).
  { unfold big; clear big; clear Hnd; induction labs as [|l ls IH]; intros s Hin; [destruct Hin|].
    destruct Hin as [Hl|Hin].
    - subst l; cbn; rewrite slen_app; lia.
    - specialize (IH s Hin); cbn; destruct l as [s'|]; [rewrite slen_app|]; lia. }
  exists (big ++ "a")%string; intros Hin; apply Hb in Hin; rewrite slen_app in Hin; cbn in Hin; lia.
Qed.

Lemma lsm_lab dflt ls : forall k j i, k + lsts_len ls = length labs -> j < lsts_len ls ->
  lsm dflt k ls (mk_rvar (lab (k + j)) i) = fpost (snth j ls) (lm (k + j) (lnth j ls) i).
Proof.
  induction ls as [|s L rest IH]; intros k j i Hl Hj; cbn in Hj; [lia|]; cbn [lsm lnth snth v_label v_index].
  destruct j as [|j].
  - rewrite Nat.add_0_r, label_eqb_refl; reflexivity.
  - destruct (label_eqb_spec (lab k) (lab (k + S j))) as [He|_].
    + exfalso; apply lab_inj in He; [lia| |]; cbn in Hl; lia.
    + replace (k + S j) with (S k + j) by lia; apply IH; cbn in Hl; lia.
Qed.

Lemma lsm_out dflt ls : forall k v, k + lsts_len ls = length labs -> ~ In (v_label v) labs -> lsm dflt k ls v = dflt v.
Proof.
  induction ls as [|s L rest IH]; intros k v Hl Hn; [reflexivity|]; cbn [lsm].
  destruct (label_eqb_spec (lab k) (v_label v)) as [He|_].
  - exfalso; apply Hn; rewrite <- He; apply nth_In; cbn in Hl; lia.
  - apply IH; [cbn in Hl; lia|exact Hn].
Qed.

Lemma fpost_id s f : (forall k, sget s k = 0) -> feq (fpost s f) f.
Proof.
  intros Hz; assert (Hv : forall v, shv s v = v).
  { intros [l i]; unfold GForm.shv; cbn; destruct (pos labs l); [rewrite Hz, Nat.add_0_r|]; reflexivity. }
  induction f as [v|u b k IH|a z k IH]; cbn [fpost feq].
  - rewrite Hv; reflexivity.
  - repeat split; intros y _; apply IH.
  - repeat split; intros y; apply IH.
Qed.

Definition ush (k : nat) : list nat := map (fun k' => if Nat.eqb k' k then 1 else 0) (seq 0 (length labs)).

Lemma ush_len k : length (ush k) = length labs.
Proof. unfold ush; rewrite length_map, length_seq; reflexivity. Qed.

Lemma sget_ush k k' : k' < length labs -> sget (ush k) k' = if Nat.eqb k' k then 1 else 0.
Proof.
  intros Hk; unfold sget, ush.
  assert (H : forall n st j, j < n -> nth j (map (fun k'' => if Nat.eqb k'' k then 1 else 0) (seq st n)) 0
                                     = if Nat.eqb (st + j) k then 1 else 0).
  { induction n as [|n IH]; intros st j Hj; [lia|]; destruct j as [|j]; cbn [seq map nth].
    - rewrite Nat.add_0_r; reflexivity.
    - rewrite IH by lia; replace (S st + j) with (st + S j) by lia; reflexivity. }
  apply (H _ 0 _ Hk).
Qed.

Lemma Out_nilv k w : Out all_nat (lm k LNilV) w <-> exists j, w = mk_rvar (lab k) j.
Proof.
  split.
  - intros (j & _ & Ho); inversion Ho; subst; eauto.
  - intros (j & ->); exists j; split; [exact I|constructor].
Qed.

Lemma nilv_factored k : k < length labs -> factored all_nat (lm k LNilV).
Proof.
  intros Hk k' i Hk' Ho; apply Out_nilv in Ho as (j & Hj); injection Hj as Hl _.
  apply lab_inj in Hl; [|exact Hk'|exact Hk]; subst k'; apply Out_nilv; eauto.
Qed.

Lemma nilv_restricted k : k < length labs -> restricted all_nat (lm k LNilV) (ush k).
Proof.
  intros Hk; split; [apply ush_len|]; intros k' Hk' Hp; rewrite sget_ush in Hp by exact Hk'.
  destruct (Nat.eqb_spec k' k) as [->|]; [|lia]; exists 0; apply Out_nilv; eauto.
Qed.

Lemma Out_nils k a r m w : Out all_nat (lm k (LNilS a r m)) w <-> exists y, outs (rm r y) w.
Proof.
  split.
  - intros (j & _ & Ho); inversion Ho; subst; eauto.
  - intros (y & Ho); exists 0; split; [exact I|]; apply outs_S with y; exact Ho.
Qed.

Lemma Out_rm_zeros n w : (exists y, outs (rm (GR zeros n) y) w) <-> Out (Dom false) (nm n) w.
Proof.
  split.
  - intros (y & Ho); exists y; split; [left; reflexivity|].
    apply (feq_outs _ _ _ (fpost_id zeros (nm n y) sget_zeros)), Ho.
  - intros (y & _ & Ho); exists y; apply (feq_outs _ _ _ (feq_sym _ _ (fpost_id zeros (nm n y) sget_zeros))), Ho.
Qed.

Lemma nils_factored k a n m : factored (Dom false) (nm n) -> factored all_nat (lm k (LNilS a (GR zeros n) m)).
Proof.
  intros Hf k' i Hk' Ho; apply Out_nils, Out_rm_zeros in Ho; apply Out_nils, Out_rm_zeros, (Hf k' i Hk' Ho).
Qed.

Lemma nils_restricted k a n m s : restricted (Dom false) (nm n) s -> restricted all_nat (lm k (LNilS a (GR zeros n) m)) s.
Proof.
  intros [Hl Hr]; split; [exact Hl|]; intros k' Hk' Hp; destruct (Hr k' Hk' Hp) as [i Ho].
  exists i; apply Out_nils, Out_rm_zeros, Ho.
Qed.

Lemma Dom_false v : Dom false v.
Proof. left; reflexivity. Qed.

(** ** Uniqueness

    Canonical encodings with the same meaning are equal.  By induction
    on the sum of the sizes of the two encodings, so that a cell can be
    compared with a nil on either side. *)

Definition U (n : nat) : Prop :=
  (forall e1 e2, esz e1 + esz e2 < n -> cent e1 -> cent e2 -> feq (em e1) (em e2) -> e1 = e2)
  /\ (forall k L1 L2, lsz L1 + lsz L2 < n -> k < length labs -> clst k L1 -> clst k L2 ->
        (forall j, feq (lm k L1 j) (lm k L2 j)) -> L1 = L2)
  /\ (forall p r1 r2, rsz r1 + rsz r2 < n -> cref p r1 -> cref p r2 ->
        (forall v, Dom p v -> feq (rm r1 v) (rm r2 v)) -> r1 = r2)
  /\ (forall p n1 n2, nsz n1 + nsz n2 < n -> cnode p n1 -> cnode p n2 ->
        (forall v, Dom p v -> feq (nm n1 v) (nm n2 v)) -> n1 = n2)
  /\ (forall p k ls1 ls2, lssz ls1 + lssz ls2 < n -> clsts p k ls1 -> clsts p k ls2 ->
        k + lsts_len ls1 = length labs -> k + lsts_len ls2 = length labs ->
        (forall j i, j < lsts_len ls1 -> Dom p (mk_rvar (lab (k + j)) i) ->
           feq (fpost (snth j ls1) (lm (k + j) (lnth j ls1) i)) (fpost (snth j ls2) (lm (k + j) (lnth j ls2) i))) ->
        ls1 = ls2)
  /\ (forall d1 d2, dsz d1 + dsz d2 < n -> cdef d1 -> cdef d2 ->
        (forall v, ~ In (v_label v) labs -> v_label v <> None -> feq (dm d1 v) (dm d2 v)) -> d1 = d2).

Lemma uniq_all n : U n.
Proof.
  induction n as [|n IH].
  { repeat split; intros; lia. }
  destruct IH as (IHe & IHl & IHr & IHn & IHs & IHd).
  (* a cell is never a nil *)
  assert (Hcv : forall k e s t, k < length labs -> lsz (LCons e s t) + lsz LNilV < S n -> clst k (LCons e s t) ->
            (forall j, feq (lm k (LCons e s t) j) (lm k LNilV j)) -> False).
  { intros k e s t Hk Hsz (He & Ht & Hf & Hr & Ha) Hm.
    assert (Htail : forall j, all_nat j -> feq (fpost s (lm k t j)) (fpost (ush k) (lm k LNilV j))).
    { intros j _; specialize (Hm (S j)); cbn [GForm.lm] in Hm |- *; eapply feq_trans; [exact Hm|].
      cbn [GForm.fpost feq]; rewrite (shv_lab labs Hnd) by exact Hk; rewrite sget_ush, Nat.eqb_refl by exact Hk.
      f_equal; lia. }
    destruct (factor_unique labs Hnd all_nat (lm k t) (lm k LNilV) s (ush k) Hf (nilv_factored k Hk) Hr
                (nilv_restricted k Hk) Htail) as [-> Htt].
    assert (t = LNilV) as ->.
    { apply (IHl k t LNilV); [cbn in Hsz |- *; lia|exact Hk|exact Ht|exact I|intros j; apply Htt; exact I]. }
    apply Ha; cbn [absorb]; rewrite sget_ush, Nat.eqb_refl by exact Hk; split; [lia|].
    specialize (Hm 0); cbn [GForm.lm] in Hm; exact Hm. }
  assert (Hcs : forall k e s t a r m, k < length labs -> lsz (LCons e s t) + lsz (LNilS a r m) < S n ->
            clst k (LCons e s t) -> clst k (LNilS a r m) ->
            (forall j, feq (lm k (LCons e s t) j) (lm k (LNilS a r m) j)) -> False).
  { intros k e s t a [sr nr] m Hk Hsz (He & Ht & Hf & Hr & Ha) (Hcn & Hfn & Hrn) Hm.
    assert (Hz : forall y, feq (fpost sr (nm nr y)) (fpost sr (fpost zeros (nm nr y))))
      by (intros y; apply (feq_fpost labs), feq_sym, fpost_id, sget_zeros).
    assert (Htail : forall j, all_nat j -> feq (fpost s (lm k t j)) (fpost sr (lm k (LNilS a (GR zeros nr) (S m)) j))).
    { intros j _; specialize (Hm (S j)); cbn [GForm.lm GForm.rm] in Hm |- *; eapply feq_trans; [exact Hm|].
      cbn [GForm.fpost feq]; split; [reflexivity|split; [f_equal; lia|]]; intros y; apply Hz. }
    destruct (factor_unique labs Hnd all_nat (lm k t) (lm k (LNilS a (GR zeros nr) (S m))) s sr Hf
                (nils_factored k a nr (S m) Hfn) Hr (nils_restricted k a nr (S m) sr Hrn) Htail) as [-> Htt].
    assert (t = LNilS a (GR zeros nr) (S m)) as ->.
    { apply (IHl k); [cbn in Hsz |- *; lia|exact Hk|exact Ht| |intros j; apply Htt; exact I].
      cbn [clst cref]; split; [exact Hcn|split; [exact Hfn|]]; split; [unfold zeros; apply repeat_length|].
      intros k' _ Hp; rewrite sget_zeros in Hp; lia. }
    apply Ha; cbn [absorb]; split; [lia|].
    specialize (Hm 0); cbn [GForm.lm GForm.rm] in Hm; eapply feq_trans; [exact Hm|].
    cbn [feq GForm.rm]; split; [reflexivity|split; [f_equal; lia|]]; intros y; apply Hz. }
  repeat split.
  - (* entries *)
    intros e1 e2 Hsz H1 H2 He.
    destruct e1 as [v|u b r|a z r], e2 as [v'|u' b' r'|a' z' r']; cbn [GForm.em feq] in He;
      try contradiction.
    + f_equal; exact He.
    + destruct He as [<- [<- He]]; f_equal.
      apply (IHr (match b with None => true | Some _ => false end) r r'); [cbn in Hsz; lia|exact H1|exact H2|].
      intros y Hy; apply He; intros Hb; subst b; destruct Hy as [Hy|Hy]; [discriminate|exact Hy].
    + destruct He as [<- [<- He]]; f_equal.
      apply (IHr false r r'); [cbn in Hsz; lia|exact H1|exact H2|intros y _; apply He].
  - (* lists *)
    intros k L1 L2 Hsz Hk H1 H2 Hm.
    destruct L1 as [| |a r m|e s t], L2 as [| |a' r' m'|e' s' t']; cbn [clst] in H1, H2; try contradiction.
    + reflexivity.
    + specialize (Hm 0); cbn in Hm; contradiction.
    + exfalso; apply (Hcv k e' s' t'); [exact Hk|lia|exact H2|intros j; apply feq_sym, Hm].
    + specialize (Hm 0); cbn in Hm; contradiction.
    + specialize (Hm 0); cbn [GForm.lm feq] in Hm; destruct Hm as [<- [Hz Hm]]; injection Hz as Hmm.
      replace m' with m by lia; f_equal; apply (IHr false r r'); [cbn in Hsz; lia|exact H1|exact H2|intros y _; apply Hm].
    + exfalso; apply (Hcs k e' s' t' a r m); [exact Hk|lia|exact H2|exact H1|intros j; apply feq_sym, Hm].
    + exfalso; apply (Hcv k e s t); [exact Hk|lia|exact H1|exact Hm].
    + exfalso; apply (Hcs k e s t a' r' m'); [exact Hk|lia|exact H1|exact H2|exact Hm].
    + destruct H1 as (He1 & Ht1 & Hf1 & Hr1 & _), H2 as (He2 & Ht2 & Hf2 & Hr2 & _).
      assert (e = e') as <-.
      { apply IHe; [cbn in Hsz; lia|exact He1|exact He2|specialize (Hm 0); exact Hm]. }
      destruct (factor_unique labs Hnd all_nat (lm k t) (lm k t') s s' Hf1 Hf2 Hr1 Hr2
                  (fun j _ => Hm (S j))) as [<- Htt].
      f_equal; apply (IHl k t t'); [cbn in Hsz; lia|exact Hk|exact Ht1|exact Ht2|intros j; apply Htt; exact I].
  - (* references *)
    intros p [s n1] [s' n2] Hsz (Hc1 & Hf1 & Hr1) (Hc2 & Hf2 & Hr2) He; cbn [GForm.rm] in He.
    destruct (factor_unique labs Hnd (Dom p) (nm n1) (nm n2) s s' Hf1 Hf2 Hr1 Hr2 He) as [<- Hnn].
    f_equal; apply (IHn p n1 n2); [cbn in Hsz; lia|exact Hc1|exact Hc2|exact Hnn].
  - (* nodes *)
    intros p [d ls] [d' ls'] Hsz (Hd & Hl & Hlen) (Hd' & Hl' & Hlen') He; cbn [GForm.nm] in He.
    assert (d = d') as <-.
    { apply IHd; [cbn in Hsz; lia|exact Hd|exact Hd'|]; intros v Hv Hnm.
      specialize (He v (or_intror Hnm)); rewrite !lsm_out in He by (cbn; lia || exact Hv); exact He. }
    f_equal; apply (IHs p 0 ls ls'); [cbn in Hsz; lia|exact Hl|exact Hl'|exact Hlen|exact Hlen'|].
    intros j i Hj Hdom; specialize (He _ Hdom); rewrite !lsm_lab in He by (cbn; lia); exact He.
  - (* the lists of a node *)
    intros p k ls1 ls2 Hsz H1 H2 Hl1 Hl2 He.
    destruct ls1 as [|s1 L1 r1], ls2 as [|s2 L2 r2]; cbn [lsts_len] in Hl1, Hl2; [reflexivity|lia|lia|].
    destruct H1 as [HL1 Hr1], H2 as [HL2 Hr2].
    assert (Hk : k < length labs) by lia.
    assert (Hhd : s1 = s2 /\ L1 = L2).
    { destruct (p && match lab k with None => true | Some _ => false end) eqn:Ep.
      - destruct HL1 as [-> ->], HL2 as [-> ->]; split; reflexivity.
      - destruct HL1 as (Hc1 & Hf1 & Hs1), HL2 as (Hc2 & Hf2 & Hs2).
        assert (Hm : forall i, all_nat i -> feq (fpost s1 (lm k L1 i)) (fpost s2 (lm k L2 i))).
        { intros i _; specialize (He 0 i); rewrite Nat.add_0_r in He; apply He; [cbn; lia|].
          destruct p; [right; cbn in Ep; destruct (lab k); discriminate|left; reflexivity]. }
        destruct (factor_unique labs Hnd all_nat (lm k L1) (lm k L2) s1 s2 Hf1 Hf2 Hs1 Hs2 Hm) as [<- HL].
        split; [reflexivity|]; apply (IHl k L1 L2); [cbn in Hsz; lia|exact Hk|exact Hc1|exact Hc2|].
        intros i; apply HL; exact I. }
    destruct Hhd as [<- <-]; f_equal.
    + apply (IHs p (S k) r1 r2); [cbn in Hsz; lia|exact Hr1|exact Hr2|lia|lia|].
      intros j i Hj Hdom; replace (S k + j) with (k + S j) in Hdom |- * by lia.
      apply (He (S j) i); [cbn; lia|exact Hdom].
  - (* defaults *)
    intros d1 d2 Hsz H1 H2 He; destruct fresh_label as [fs Hfs].
    specialize (He (mk_rvar (Some fs) 0) Hfs ltac:(discriminate)).
    destruct d1 as [|a r], d2 as [|a' r']; cbn [GForm.dm feq] in He; try contradiction; [reflexivity|].
    destruct He as [<- [_ He]]; f_equal; apply (IHr false r r'); [cbn in Hsz; lia|exact H1|exact H2|intros y _; apply He].
Qed.

Theorem gref_unique p r1 r2 : cref p r1 -> cref p r2 -> (forall v, Dom p v -> feq (rm r1 v) (rm r2 v)) -> r1 = r2.
Proof. apply (proj1 (proj2 (proj2 (uniq_all (S (rsz r1 + rsz r2)))))); lia. Qed.

End Canon.

(** ** Decidable equality of encodings *)

Definition lnat_eqb (s t : list nat) : bool := if list_eq_dec Nat.eq_dec s t then true else false.
Definition onat_eqb (b c : option nat) : bool :=
  match b, c with None, None => true | Some x, Some y => Nat.eqb x y | _, _ => false end.

Fixpoint ent_eqb (e e' : ent) : bool :=
  match e, e' with
  | EV v, EV v' => rvar_eqb v v'
  | ET u b r, ET u' b' r' => Nat.eqb u u' && onat_eqb b b' && gref_eqb r r'
  | ES a z r, ES a' z' r' => Nat.eqb a a' && rvar_eqb z z' && gref_eqb r r'
  | _, _ => false
  end
with lst_eqb (L L' : lst) : bool :=
  match L, L' with
  | LNilV, LNilV | LNilP, LNilP => true
  | LNilS a r m, LNilS a' r' m' => Nat.eqb a a' && gref_eqb r r' && Nat.eqb m m'
  | LCons e s t, LCons e' s' t' => ent_eqb e e' && lnat_eqb s s' && lst_eqb t t'
  | _, _ => false
  end
with gref_eqb (r r' : gref) : bool :=
  match r, r' with GR s n, GR s' n' => lnat_eqb s s' && gnode_eqb n n' end
with gnode_eqb (n n' : gnode) : bool :=
  match n, n' with GN d ls, GN d' ls' => gdef_eqb d d' && lsts_eqb ls ls' end
with lsts_eqb (ls ls' : lsts) : bool :=
  match ls, ls' with
  | LsNil, LsNil => true
  | LsCons s L r, LsCons s' L' r' => lnat_eqb s s' && lst_eqb L L' && lsts_eqb r r'
  | _, _ => false
  end
with gdef_eqb (d d' : gdef) : bool :=
  match d, d' with
  | DV, DV => true
  | DS a r, DS a' r' => Nat.eqb a a' && gref_eqb r r'
  | _, _ => false
  end.

Lemma lnat_eqb_spec s t : lnat_eqb s t = true <-> s = t.
Proof. unfold lnat_eqb; destruct (list_eq_dec Nat.eq_dec s t); split; congruence. Qed.

Lemma onat_eqb_spec b c : onat_eqb b c = true <-> b = c.
Proof. destruct b, c; cbn; rewrite ?Nat.eqb_eq; split; congruence. Qed.

Lemma rvar_eqb_iff v v' : rvar_eqb v v' = true <-> v = v'.
Proof. destruct (rvar_eqb_spec v v'); split; congruence. Qed.

Lemma eqb_spec_all :
  (forall e e', ent_eqb e e' = true <-> e = e')
  /\ (forall L L', lst_eqb L L' = true <-> L = L')
  /\ (forall r r', gref_eqb r r' = true <-> r = r')
  /\ (forall n n', gnode_eqb n n' = true <-> n = n')
  /\ (forall ls ls', lsts_eqb ls ls' = true <-> ls = ls')
  /\ (forall d d', gdef_eqb d d' = true <-> d = d').
Proof.
  apply g_ind; intros;
    match goal with
    | |- ent_eqb ?x ?y = true <-> _ => destruct y
    | |- lst_eqb ?x ?y = true <-> _ => destruct y
    | |- gref_eqb ?x ?y = true <-> _ => destruct y
    | |- gnode_eqb ?x ?y = true <-> _ => destruct y
    | |- lsts_eqb ?x ?y = true <-> _ => destruct y
    | |- gdef_eqb ?x ?y = true <-> _ => destruct y
    end; cbn [ent_eqb lst_eqb gref_eqb gnode_eqb lsts_eqb gdef_eqb];
    rewrite ?andb_true_iff, ?Nat.eqb_eq, ?rvar_eqb_iff, ?onat_eqb_spec, ?lnat_eqb_spec;
    repeat match goal with H : forall _, ?f _ _ = true <-> _ |- context [?f _ _ = true] => rewrite H end;
    split; intros; try discriminate; repeat match goal with H : _ /\ _ |- _ => destruct H end;
    subst; try congruence; try (injection H0 as; subst); try (injection H1 as; subst); try (injection H2 as; subst);
    try (injection H3 as; subst); repeat split; auto.
Qed.

