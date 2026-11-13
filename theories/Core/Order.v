(** * An order on payloads

    [LayeredUnique.lw_unique] takes a strict order on what payloads do to
    named variables.  This is the one the canonical word uses.  It is
    stated on the free model, so it only depends on what a payload
    does.  Of two payloads:

    - the one with more atoms left (far along a label, [deep]) is above;
    - then the one with deeper terms ([hle]: the terms it gives, and the
      terms their payloads give, nested at most [n] deep);
    - then what they do far along the label [lbig], which is what they
      do to every label they do not mention;
    - then the first variable, in the order [vlt], at which they differ.

    Results are compared by [rgt]: a variable is below a term, which is
    below a stuck atom; variables by [vlt]; terms by their term atom,
    payload atom and payload; stuck atoms by the atom, what follows it,
    and the variable.

    Here: the order is irreflexive up to [feq], only depends on results
    up to [feq], and is transitive, which is what uniqueness needs
    ([gtP_irrefl], [gtP_keq], [gtP_trans]).  That the canonical word can
    always compare its payloads is shown where it does. *)

From Stdlib Require Import Arith List Lia Bool.
From ShiftedNames.Core Require Import Label Var Adjustment Normalise Unique LayeredUnique.
Import ListNotations.

Lemma vlt_trans a b c : vlt a b -> vlt b c -> vlt a c.
Proof.
  intros [H|[E H]] [H'|[E' H']]; unfold vlt.
  - left; exact (olabel_lt_trans _ _ _ H H').
  - left; rewrite <- E'; exact H.
  - left; rewrite E; exact H'.
  - right; split; [congruence|lia].
Qed.

Section Order.

(** The variables that count: named ones, or all. *)
Definition dom (all : bool) (y : rvar) : Prop := all = true \/ v_label y <> None.

Definition probe (all : bool) (y : rvar) : Prop := dom all y.

Definition isb (b : option nat) : bool := match b with Some _ => true | None => false end.

Lemma dom_isb b y : dom (isb b) y <-> (b = None -> v_label y <> None).
Proof.
  unfold dom; destruct b; cbn; split.
  - intros _ H; discriminate H.
  - intros _; left; reflexivity.
  - intros [H|H]; [discriminate H|intros _; exact H].
  - intros H; right; apply H; reflexivity.
Qed.

(** The terms of a result are at most [n] deep. *)
Fixpoint dle (n : nat) (f : fres) {struct f} : Prop :=
  match f with
  | FVar _ => True
  | FTerm _ b k => match n with 0 => False | S m => forall y, dom (isb b) y -> dle m (k y) end
  | FStuck _ _ k => forall y, dle n (k y)
  end.

Definition hle (all : bool) (n : nat) (k : rvar -> fres) : Prop := forall y, dom all y -> dle n (k y).

Definition feqd (all : bool) (k k' : rvar -> fres) : Prop := forall y, dom all y -> feq (k y) (k' y).

(** The comparison of two payloads, given one of their results. *)
Definition KG (R : rvar -> fres -> Prop) (all : bool) (k k' : rvar -> fres) : Prop :=
  (exists d d', deep d k /\ deep d' k' /\ d' < d)
  \/ (exists d, deep d k /\ deep d k' /\
       ((exists n, hle all n k' /\ ~ hle all n k)
        \/ ((forall n, hle all n k <-> hle all n k') /\
            ((exists B, forall i, B <= i -> R (mk_rvar lbig i) (k' (mk_rvar lbig i)))
             \/ ((exists B, forall i, B <= i -> feq (k (mk_rvar lbig i)) (k' (mk_rvar lbig i))) /\
                 exists y, probe all y /\ (forall y', probe all y' -> vlt y' y -> feq (k y') (k' y')) /\ R y (k' y)))))).

Definition bgt (b b' : option nat) : Prop :=
  match b, b' with Some n, Some n' => n' < n | Some _, None => True | _, _ => False end.

(** [rgt f g]: the result [f] is above [g]. *)
Fixpoint rgt (f g : fres) {struct f} : Prop :=
  match f, g with
  | FVar v, FVar v' => vlt v' v
  | FVar _, _ => False
  | FTerm _ _ _, FVar _ => True
  | FTerm u b k, FTerm u' b' k' =>
      u' < u \/ (u = u' /\ (bgt b b' \/ (b = b' /\ KG (fun y g => rgt (k y) g) (isb b) k k')))
  | FTerm _ _ _, FStuck _ _ _ => False
  | FStuck a z k, FStuck a' z' k' =>
      a' < a \/ (a = a' /\ (KG (fun y g => rgt (k y) g) true k k' \/ (feqd true k k' /\ vlt z' z)))
  | FStuck _ _ _, _ => True
  end.

Definition kgt (all : bool) (k k' : rvar -> fres) : Prop := KG (fun y g => rgt (k y) g) all k k'.

(** The order on payloads. *)
Definition gtP : (rvar -> fres) -> (rvar -> fres) -> Prop := kgt false.

(** ** Depths *)

Lemma dle_feq f : forall g n, feq f g -> dle n f -> dle n g.
Proof.
  induction f as [v|u b k IH|a z k IH]; intros [v'|u' b' k'|a' z' k'] n; cbn [feq dle]; try contradiction.
  - intros _ _; exact I.
  - intros [<- [<- E]]; destruct n as [|n]; [tauto|]; intros H y Hy.
    apply (IH y), H, Hy; apply E, dom_isb, Hy.
  - intros [<- [<- E]] H y; exact (IH y _ n (E y) (H y)).
Qed.

Lemma dle_mono f : forall n m, n <= m -> dle n f -> dle m f.
Proof.
  induction f as [v|u b k IH|a z k IH]; intros n m Hnm; cbn [dle].
  - tauto.
  - destruct n as [|n]; [tauto|]; destruct m as [|m]; [lia|].
    intros H y Hy; exact (IH y n m ltac:(lia) (H y Hy)).
  - intros H y; exact (IH y n m Hnm (H y)).
Qed.

Lemma hle_feq all n k k' : feqd all k k' -> hle all n k -> hle all n k'.
Proof. intros E H y Hy; exact (dle_feq _ _ _ (E y Hy) (H y Hy)). Qed.

Lemma hle_mono all n m k : n <= m -> hle all n k -> hle all m k.
Proof. intros Hnm H y Hy; exact (dle_mono _ _ _ Hnm (H y Hy)). Qed.

Lemma dom_big all i : dom all (mk_rvar lbig i).
Proof. right; discriminate. Qed.

Lemma deep_feq d : forall k k', (forall i, feq (k (mk_rvar lbig i)) (k' (mk_rvar lbig i))) -> deep d k -> deep d k'.
Proof.
  induction d as [|d IH]; intros k k' E; cbn [deep].
  - intros [B H]; exists B; intros i Hi; destruct (H i Hi) as [y Ey].
    pose proof (E i) as F; rewrite Ey in F; destruct (k' (mk_rvar lbig i)); cbn [feq] in F; try contradiction.
    exists v; reflexivity.
  - intros [B [a H]]; exists B, a; intros i Hi; destruct (H i Hi) as [z [k1 [Ez Hk1]]].
    pose proof (E i) as F; rewrite Ez in F; destruct (k' (mk_rvar lbig i)) as [|? ? ?|a' z' k2]; cbn [feq] in F;
      try contradiction.
    destruct F as [<- [<- F]]; exists z, k2; split; [reflexivity|].
    exact (IH k1 k2 (fun j => F _) Hk1).
Qed.

Lemma feqd_big all k k' : feqd all k k' -> forall i, feq (k (mk_rvar lbig i)) (k' (mk_rvar lbig i)).
Proof. intros E i; apply E, dom_big. Qed.

Lemma feqd_sym all k k' : feqd all k k' -> feqd all k' k.
Proof. intros E y Hy; apply feq_sym, E, Hy. Qed.

Lemma feqd_trans all k1 k2 k3 : feqd all k1 k2 -> feqd all k2 k3 -> feqd all k1 k3.
Proof. intros E E' y Hy; exact (feq_trans _ _ _ (E y Hy) (E' y Hy)). Qed.

Lemma feqd_refl all k : feqd all k k.
Proof. intros y _; apply feq_refl. Qed.

Lemma probe_dom all y : probe all y -> dom all y.
Proof. intros H; exact H. Qed.


(** ** The comparison of payloads, for any comparison of results *)

Lemma deep_eq d d' k k' : deep d k -> deep d' k' -> (forall i, feq (k (mk_rvar lbig i)) (k' (mk_rvar lbig i))) -> d = d'.
Proof. intros H H' E; exact (deep_unique d d' k k' H H' E). Qed.

Lemma KG_compat (R R' : rvar -> fres -> Prop) all k1 k1' k2 k2' :
  feqd all k1 k1' -> feqd all k2 k2' ->
  (forall y, probe all y -> R y (k2 y) -> R' y (k2' y)) ->
  KG R all k1 k2 -> KG R' all k1' k2'.
Proof.
  intros E1 E2 HR [[d [d' [H1 [H2 Hlt]]]]|[d [H1 [H2 C]]]].
  - left; exists d, d'; split; [exact (deep_feq _ _ _ (feqd_big _ _ _ E1) H1)|].
    split; [exact (deep_feq _ _ _ (feqd_big _ _ _ E2) H2)|exact Hlt].
  - right; exists d; split; [exact (deep_feq _ _ _ (feqd_big _ _ _ E1) H1)|].
    split; [exact (deep_feq _ _ _ (feqd_big _ _ _ E2) H2)|].
    destruct C as [[n [Hn Hn']]|[Hh G]]; [left; exists n; split|right; split].
    + exact (hle_feq _ _ _ _ E2 Hn).
    + intros H; apply Hn', (hle_feq _ _ _ _ (feqd_sym _ _ _ E1) H).
    + intros n; split; intros H.
      * apply (hle_feq _ _ _ _ E2), Hh, (hle_feq _ _ _ _ (feqd_sym _ _ _ E1)), H.
      * apply (hle_feq _ _ _ _ E1), Hh, (hle_feq _ _ _ _ (feqd_sym _ _ _ E2)), H.
    + destruct G as [[B HB]|[[B HB] [y [Hy [Hpre HRy]]]]].
      * left; exists B; intros i Hi; exact (HR _ (dom_big _ _) (HB i Hi)).
      * right; split.
        -- exists B; intros i Hi.
           exact (feq_trans _ _ _ (feq_sym _ _ (E1 _ (dom_big _ _))) (feq_trans _ _ _ (HB i Hi) (E2 _ (dom_big _ _)))).
        -- exists y; split; [exact Hy|split; [|exact (HR y Hy HRy)]].
           intros y' Hy' Hv; pose proof (probe_dom _ _ Hy') as Hd.
           exact (feq_trans _ _ _ (feq_sym _ _ (E1 y' Hd)) (feq_trans _ _ _ (Hpre y' Hy' Hv) (E2 y' Hd))).
Qed.

Lemma KG_irrefl (R : rvar -> fres -> Prop) all k k' :
  feqd all k k' -> (forall y, probe all y -> ~ R y (k' y)) -> ~ KG R all k k'.
Proof.
  intros E HR [[d [d' [H1 [H2 Hlt]]]]|[d [H1 [H2 [[n [Hn Hn']]|[_ [[B HB]|[_ [y [Hy [_ HRy]]]]]]]]]]].
  - pose proof (deep_eq _ _ _ _ H1 H2 (feqd_big _ _ _ E)); lia.
  - exact (Hn' (hle_feq _ _ _ _ (feqd_sym _ _ _ E) Hn)).
  - exact (HR _ (dom_big _ _) (HB B (le_n _))).
  - exact (HR y Hy HRy).
Qed.

Lemma KG_trans (R1 R2 R3 : rvar -> fres -> Prop) all k1 k2 k3 :
  (forall y, probe all y -> feq (k1 y) (k2 y) -> R2 y (k3 y) -> R3 y (k3 y)) ->
  (forall y, probe all y -> R1 y (k2 y) -> feq (k2 y) (k3 y) -> R3 y (k3 y)) ->
  (forall y, probe all y -> R1 y (k2 y) -> R2 y (k3 y) -> R3 y (k3 y)) ->
  KG R1 all k1 k2 -> KG R2 all k2 k3 -> KG R3 all k1 k3.
Proof.
  intros HL HRt HT G1 G2.
  assert (Dk : forall d d' k, deep d k -> deep d' k -> d = d') by
    (intros d d' k H H'; exact (deep_eq _ _ _ _ H H' (fun i => feq_refl _))).
  destruct G1 as [[d1 [d2 [A1 [A2 L1]]]]|[d [A1 [A2 C1]]]];
    destruct G2 as [[e2 [e3 [B2 [B3 L2]]]]|[e [B2 [B3 C2]]]].
  - left; exists d1, e3; pose proof (Dk _ _ _ A2 B2); repeat split; auto; lia.
  - left; exists d1, e; pose proof (Dk _ _ _ A2 B2); repeat split; auto; lia.
  - left; exists d, e3; pose proof (Dk _ _ _ A2 B2); repeat split; auto; lia.
  - pose proof (Dk _ _ _ A2 B2) as <-; right; exists d; split; [exact A1|split; [exact B3|]].
    destruct C1 as [[n [Hn Hn']]|[Hh1 G1]]; destruct C2 as [[m [Hm Hm']]|[Hh2 G2]].
    + left; exists m; split; [exact Hm|intros H].
      destruct (Nat.le_gt_cases n m) as [Hle|Hgt]; [exact (Hm' (hle_mono _ _ _ _ Hle Hn))|].
      exact (Hn' (hle_mono _ m n _ (Nat.lt_le_incl _ _ Hgt) H)).
    + left; exists n; split; [apply Hh2, Hn|exact Hn'].
    + left; exists m; split; [exact Hm|intros H; apply Hm', Hh1, H].
    + right; split; [intros n; rewrite Hh1; apply Hh2|].
      destruct G1 as [[B1 HB1]|[[B1 HB1] [y1 [Hy1 [Hp1 HR1]]]]];
        destruct G2 as [[B2' HB2]|[[B2' HB2] [y2 [Hy2 [Hp2 HR2]]]]].
      * left; exists (B1 + B2'); intros i Hi; exact (HT _ (dom_big _ _) (HB1 i ltac:(lia)) (HB2 i ltac:(lia))).
      * left; exists (B1 + B2'); intros i Hi; exact (HRt _ (dom_big _ _) (HB1 i ltac:(lia)) (HB2 i ltac:(lia))).
      * left; exists (B1 + B2'); intros i Hi; exact (HL _ (dom_big _ _) (HB1 i ltac:(lia)) (HB2 i ltac:(lia))).
      * right; split; [exists (B1 + B2'); intros i Hi; exact (feq_trans _ _ _ (HB1 i ltac:(lia)) (HB2 i ltac:(lia)))|].
        destruct (vlt_total y1 y2) as [Hv|[<-|Hv]].
        -- exists y1; split; [exact Hy1|split].
           ++ intros y' Hy' Hv'; exact (feq_trans _ _ _ (Hp1 y' Hy' Hv') (Hp2 y' Hy' (vlt_trans _ _ _ Hv' Hv))).
           ++ exact (HRt y1 Hy1 HR1 (Hp2 y1 Hy1 Hv)).
        -- exists y1; split; [exact Hy1|split; [|exact (HT y1 Hy1 HR1 HR2)]].
           intros y' Hy' Hv'; exact (feq_trans _ _ _ (Hp1 y' Hy' Hv') (Hp2 y' Hy' Hv')).
        -- exists y2; split; [exact Hy2|split].
           ++ intros y' Hy' Hv'; exact (feq_trans _ _ _ (Hp1 y' Hy' (vlt_trans _ _ _ Hv' Hv)) (Hp2 y' Hy' Hv')).
           ++ exact (HL y2 Hy2 (Hp1 y2 Hy2 Hv) HR2).
Qed.

(** ** The order on results *)

Lemma bgt_irrefl b : ~ bgt b b.
Proof. destruct b; cbn; lia. Qed.

Lemma bgt_trans b1 b2 b3 : bgt b1 b2 -> bgt b2 b3 -> bgt b1 b3.
Proof. destruct b1, b2, b3; cbn; try tauto; lia. Qed.

Lemma feq_term u b k u' b' k' : feq (FTerm u b k) (FTerm u' b' k') <-> u = u' /\ b = b' /\ feqd (isb b) k k'.
Proof.
  cbn [feq]; split; intros [<- [<- E]]; repeat split; intros y Hy.
  - apply E, dom_isb, Hy.
  - apply E, dom_isb, Hy.
Qed.

Lemma feq_stuck a z k a' z' k' : feq (FStuck a z k) (FStuck a' z' k') <-> a = a' /\ z = z' /\ feqd true k k'.
Proof.
  cbn [feq]; split; intros [<- [<- E]]; repeat split; intros y; [intros _|]; apply E; [left; reflexivity].
Qed.

Theorem rgt_props f :
  (forall g, feq f g -> ~ rgt f g)
  /\ (forall f' g g', feq f f' -> feq g g' -> rgt f g -> rgt f' g')
  /\ (forall f' g g', feq f f' -> feq g g' -> rgt f' g' -> rgt f g)
  /\ (forall g h, rgt f g -> rgt g h -> rgt f h).
Proof.
  induction f as [v|u b k IH|a z k IH].
  - split; [intros [v'| |] E; cbn [feq] in E; try contradiction; subst v'; exact (vlt_irrefl v)|].
    split; [intros [v'| |] [w| |] [w'| |]; cbn [feq rgt]; try tauto; intros; subst; tauto|].
    split; [intros [v'| |] [w| |] [w'| |]; cbn [feq rgt]; try tauto; intros; subst; tauto|].
    intros [w| |] [w'| |]; cbn [rgt]; try tauto; intros H1 H2; exact (vlt_trans _ _ _ H2 H1).
  - assert (Hp : forall y, probe (isb b) y -> dom (isb b) y) by (intros y Hy; exact (probe_dom _ _ Hy)).
    split; [|split; [|split]].
    + intros [|u' b' k'|] E; cbn [feq] in E; try contradiction.
      apply feq_term in E; destruct E as [<- [<- E]]; cbn [rgt].
      intros [H|[_ [H|[_ H]]]]; [lia|exact (bgt_irrefl _ H)|].
      refine (KG_irrefl _ _ _ _ E _ H); intros y Hy; apply (proj1 (IH y)), E, Hp, Hy.
    + intros [|u1 b1 k1|] g g' E; cbn [feq] in E; try contradiction.
      apply feq_term in E; destruct E as [<- [<- E]].
      destruct g as [w|u' b' k'|a' z' k'], g' as [w'|u'' b'' k''|a'' z'' k'']; cbn [feq rgt]; try tauto.
      intros E'; apply feq_term in E'; destruct E' as [<- [<- E']].
      intros [H|[Hu [H|[Hb H]]]]; [left; exact H|right; split; [exact Hu|left; exact H]|].
      right; split; [exact Hu|right; split; [exact Hb|]]; subst b'.
      refine (KG_compat _ _ _ _ _ _ _ E E' _ H); intros y Hy Hr.
      exact (proj1 (proj2 (IH y)) (k1 y) (k' y) (k'' y) (E y (Hp y Hy)) (E' y (Hp y Hy)) Hr).
    + intros [|u1 b1 k1|] g g' E; cbn [feq] in E; try contradiction.
      apply feq_term in E; destruct E as [<- [<- E]].
      destruct g as [w|u' b' k'|a' z' k'], g' as [w'|u'' b'' k''|a'' z'' k'']; cbn [feq rgt]; try tauto.
      intros E'; apply feq_term in E'; destruct E' as [<- [<- E']].
      intros [H|[Hu [H|[Hb H]]]]; [left; exact H|right; split; [exact Hu|left; exact H]|].
      right; split; [exact Hu|right; split; [exact Hb|]]; subst b'.
      refine (KG_compat _ _ _ _ _ _ _ (feqd_sym _ _ _ E) (feqd_sym _ _ _ E') _ H); intros y Hy Hr.
      exact (proj1 (proj2 (proj2 (IH y))) (k1 y) (k' y) (k'' y) (E y (Hp y Hy)) (E' y (Hp y Hy)) Hr).
    + intros [w|u' b' k'|a' z' k'] [w'|u'' b'' k''|a'' z'' k'']; cbn [rgt]; try tauto.
      intros [H1|[<- [H1|[<- H1]]]] [H2|[<- [H2|[<- H2]]]]; try (left; lia);
        try (right; split; [reflexivity|left; exact (bgt_trans _ _ _ H1 H2)]);
        try (right; split; [reflexivity|left; exact H1]); try (right; split; [reflexivity|left; exact H2]).
      right; split; [reflexivity|right; split; [reflexivity|]].
      refine (KG_trans _ _ _ _ _ _ _ _ _ _ H1 H2).
      * intros y Hy E Hr; exact (proj1 (proj2 (proj2 (IH y))) (k' y) (k'' y) (k'' y) E (feq_refl _) Hr).
      * intros y Hy Hr E; exact (proj1 (proj2 (IH y)) (k y) (k' y) (k'' y) (feq_refl _) E Hr).
      * intros y Hy Hr Hr'; exact (proj2 (proj2 (proj2 (IH y))) _ _ Hr Hr').
  - assert (Hp : forall y, probe true y -> dom true y) by (intros y Hy; exact (probe_dom _ _ Hy)).
    split; [|split; [|split]].
    + intros [| |a' z' k'] E; cbn [feq] in E; try contradiction.
      apply feq_stuck in E; destruct E as [<- [<- E]]; cbn [rgt].
      intros [H|[_ [H|[_ H]]]]; [lia| |exact (vlt_irrefl _ H)].
      refine (KG_irrefl _ _ _ _ E _ H); intros y Hy; apply (proj1 (IH y)), E, Hp, Hy.
    + intros [| |a1 z1 k1] g g' E; cbn [feq] in E; try contradiction.
      apply feq_stuck in E; destruct E as [<- [<- E]].
      destruct g as [w|u' b' k'|a' z' k'], g' as [w'|u'' b'' k''|a'' z'' k'']; cbn [feq rgt]; try tauto.
      intros E'; apply feq_stuck in E'; destruct E' as [<- [<- E']].
      intros [H|[Ha [H|[Hk H]]]]; [left; exact H| |right; split; [exact Ha|right; split; [|exact H]]].
      * right; split; [exact Ha|left].
        refine (KG_compat _ _ _ _ _ _ _ E E' _ H); intros y Hy Hr.
        exact (proj1 (proj2 (IH y)) (k1 y) (k' y) (k'' y) (E y (Hp y Hy)) (E' y (Hp y Hy)) Hr).
      * exact (feqd_trans _ _ _ _ (feqd_sym _ _ _ E) (feqd_trans _ _ _ _ Hk E')).
    + intros [| |a1 z1 k1] g g' E; cbn [feq] in E; try contradiction.
      apply feq_stuck in E; destruct E as [<- [<- E]].
      destruct g as [w|u' b' k'|a' z' k'], g' as [w'|u'' b'' k''|a'' z'' k'']; cbn [feq rgt]; try tauto.
      intros E'; apply feq_stuck in E'; destruct E' as [<- [<- E']].
      intros [H|[Ha [H|[Hk H]]]]; [left; exact H| |right; split; [exact Ha|right; split; [|exact H]]].
      * right; split; [exact Ha|left].
        refine (KG_compat _ _ _ _ _ _ _ (feqd_sym _ _ _ E) (feqd_sym _ _ _ E') _ H); intros y Hy Hr.
        exact (proj1 (proj2 (proj2 (IH y))) (k1 y) (k' y) (k'' y) (E y (Hp y Hy)) (E' y (Hp y Hy)) Hr).
      * exact (feqd_trans _ _ _ _ E (feqd_trans _ _ _ _ Hk (feqd_sym _ _ _ E'))).
    + intros [w|u' b' k'|a' z' k'] [w'|u'' b'' k''|a'' z'' k'']; cbn [rgt]; try tauto.
      assert (HT : forall k1 k2, KG (fun y g => rgt (k y) g) true k k1 -> KG (fun y g => rgt (k1 y) g) true k1 k2 ->
                     KG (fun y g => rgt (k y) g) true k k2).
      { intros k1 k2 G1 G2; refine (KG_trans _ _ _ _ _ _ _ _ _ _ G1 G2).
        - intros y Hy E Hr; exact (proj1 (proj2 (proj2 (IH y))) (k1 y) (k2 y) (k2 y) E (feq_refl _) Hr).
        - intros y Hy Hr E; exact (proj1 (proj2 (IH y)) (k y) (k1 y) (k2 y) (feq_refl _) E Hr).
        - intros y Hy Hr Hr'; exact (proj2 (proj2 (proj2 (IH y))) _ _ Hr Hr'). }
      intros [H1|[<- [H1|[E1 H1]]]] [H2|[<- [H2|[E2 H2]]]]; try (left; lia).
      * right; split; [reflexivity|left; exact (HT k' k'' H1 H2)].
      * right; split; [reflexivity|left].
        refine (KG_compat _ _ _ _ _ _ _ (feqd_refl _ _) E2 _ H1); intros y _ Hr.
        exact (proj1 (proj2 (IH y)) (k y) (k' y) (k'' y) (feq_refl _) (E2 y (or_introl eq_refl)) Hr).
      * right; split; [reflexivity|left].
        refine (KG_compat _ _ _ _ _ _ _ (feqd_sym _ _ _ E1) (feqd_refl _ _) _ H2); intros y _ Hr.
        exact (proj1 (proj2 (proj2 (IH y))) (k' y) (k'' y) (k'' y) (E1 y (or_introl eq_refl)) (feq_refl _) Hr).
      * right; split; [reflexivity|right; split; [exact (feqd_trans _ _ _ _ E1 E2)|exact (vlt_trans _ _ _ H2 H1)]].
Qed.

Lemma rgt_irrefl f g : feq f g -> ~ rgt f g.
Proof. exact (proj1 (rgt_props f) g). Qed.

Lemma rgt_feq f f' g g' : feq f f' -> feq g g' -> rgt f g -> rgt f' g'.
Proof. exact (proj1 (proj2 (rgt_props f)) f' g g'). Qed.

Lemma rgt_trans f g h : rgt f g -> rgt g h -> rgt f h.
Proof. exact (proj2 (proj2 (proj2 (rgt_props f))) g h). Qed.

(** ** The order on payloads *)

Lemma kgt_irrefl all k k' : feqd all k k' -> ~ kgt all k k'.
Proof.
  intros E; apply KG_irrefl; [exact E|]; intros y Hy; apply rgt_irrefl, E, probe_dom, Hy.
Qed.

Lemma kgt_feq all k1 k1' k2 k2' : feqd all k1 k1' -> feqd all k2 k2' -> kgt all k1 k2 -> kgt all k1' k2'.
Proof.
  intros E1 E2; apply KG_compat; [exact E1|exact E2|]; intros y Hy Hr.
  exact (rgt_feq _ _ _ _ (E1 y (probe_dom _ _ Hy)) (E2 y (probe_dom _ _ Hy)) Hr).
Qed.

Lemma kgt_trans all k1 k2 k3 : kgt all k1 k2 -> kgt all k2 k3 -> kgt all k1 k3.
Proof.
  apply KG_trans.
  - intros y _ E Hr; exact (rgt_feq _ _ _ _ (feq_sym _ _ E) (feq_refl _) Hr).
  - intros y _ Hr E; exact (rgt_feq _ _ _ _ (feq_refl _) E Hr).
  - intros y _ Hr Hr'; exact (rgt_trans _ _ _ Hr Hr').
Qed.

(** What [LayeredUnique.lw_unique] needs of the order. *)
Lemma gtP_irrefl k k' : keq k k' -> ~ gtP k k'.
Proof. intros E; apply kgt_irrefl; intros y [H|H]; [discriminate H|exact (E y H)]. Qed.

Lemma gtP_trans k1 k2 k3 : gtP k1 k2 -> gtP k2 k3 -> gtP k1 k3.
Proof. apply kgt_trans. Qed.

Lemma gtP_keq k1 k1' k2 k2' : keq k1 k1' -> keq k2 k2' -> gtP k1 k2 -> gtP k1' k2'.
Proof.
  intros E1 E2; apply kgt_feq; intros y [H|H]; try discriminate H; [exact (E1 y H)|exact (E2 y H)].
Qed.

End Order.
