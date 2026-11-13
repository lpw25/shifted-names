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

(** Results that agree far along a label: the same kind, the same atom
    and what follows it; the variables may differ. *)
Definition ceq (f g : fres) : Prop :=
  match f, g with
  | FVar _, FVar _ => True
  | FTerm _ _ _, FTerm _ _ _ => feq f g
  | FStuck a _ k, FStuck a' _ k' => a = a' /\ forall y, feq (k y) (k' y)
  | _, _ => False
  end.

(** The comparison of two payloads, given comparisons of their results:
    [R] in full, [Rc] up to the variable reached. *)
Definition KG (R Rc : rvar -> fres -> Prop) (all : bool) (k k' : rvar -> fres) : Prop :=
  (exists d d', deep d k /\ deep d' k' /\ d' < d)
  \/ (exists d, deep d k /\ deep d k' /\
       ((exists n, hle all n k' /\ ~ hle all n k)
        \/ ((forall n, hle all n k <-> hle all n k') /\
            ((exists B, forall y, dom all y -> B <= v_index y -> Rc y (k' y))
             \/ ((exists B, forall y, dom all y -> B <= v_index y -> ceq (k y) (k' y)) /\
                 exists y, probe all y /\ (forall y', probe all y' -> vlt y' y -> feq (k y') (k' y')) /\ R y (k' y)))))).

Definition bgt (b b' : option nat) : Prop :=
  match b, b' with Some n, Some n' => n' < n | Some _, None => True | _, _ => False end.

(** [rgt c f g]: the result [f] is above [g]; with [c], up to the
    variable reached. *)
Fixpoint rgt (c : bool) (f g : fres) {struct f} : Prop :=
  match f, g with
  | FVar v, FVar v' => if c then False else vlt v' v
  | FVar _, _ => False
  | FTerm _ _ _, FVar _ => True
  | FTerm u b k, FTerm u' b' k' =>
      u' < u \/ (u = u' /\ (bgt b b' \/ (b = b' /\ KG (fun y g => rgt false (k y) g) (fun y g => rgt true (k y) g) (isb b) k k')))
  | FTerm _ _ _, FStuck _ _ _ => False
  | FStuck a z k, FStuck a' z' k' =>
      a' < a \/ (a = a' /\ (KG (fun y g => rgt false (k y) g) (fun y g => rgt true (k y) g) true k k'
                           \/ (if c then False else (feqd true k k' /\ vlt z' z))))
  | FStuck _ _ _, _ => True
  end.

Definition kgt (all : bool) (k k' : rvar -> fres) : Prop :=
  KG (fun y g => rgt false (k y) g) (fun y g => rgt true (k y) g) all k k'.

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

Lemma ceq_refl f : ceq f f.
Proof. destruct f; cbn [ceq]; auto using feq_refl. Qed.

Lemma ceq_sym f g : ceq f g -> ceq g f.
Proof.
  destruct f, g; cbn [ceq]; try tauto; [apply feq_sym|].
  intros [<- E]; split; [reflexivity|intros y; apply feq_sym, E].
Qed.

Lemma ceq_trans f g h : ceq f g -> ceq g h -> ceq f h.
Proof.
  destruct f, g, h; cbn [ceq]; try tauto; [apply feq_trans|].
  intros [<- E] [<- E']; split; [reflexivity|intros y; exact (feq_trans _ _ _ (E y) (E' y))].
Qed.

Lemma feq_ceq f g : feq f g -> ceq f g.
Proof.
  destruct f, g; cbn [ceq]; try (cbn [feq]; tauto).
Qed.

Lemma ceq_feq f f' g g' : feq f f' -> feq g g' -> ceq f g -> ceq f' g'.
Proof.
  intros E1 E2 C; apply (ceq_trans _ f); [apply ceq_sym, feq_ceq, E1|].
  apply (ceq_trans _ g); [exact C|apply feq_ceq, E2].
Qed.

Lemma KG_compat (R R' Rc Rc' : rvar -> fres -> Prop) all k1 k1' k2 k2' :
  feqd all k1 k1' -> feqd all k2 k2' ->
  (forall y, probe all y -> R y (k2 y) -> R' y (k2' y)) ->
  (forall y, dom all y -> Rc y (k2 y) -> Rc' y (k2' y)) ->
  KG R Rc all k1 k2 -> KG R' Rc' all k1' k2'.
Proof.
  intros E1 E2 HR HRc [[d [d' [H1 [H2 Hlt]]]]|[d [H1 [H2 C]]]].
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
      * left; exists B; intros y Hy Hi; exact (HRc y Hy (HB y Hy Hi)).
      * right; split.
        -- exists B; intros y' Hy' Hi; exact (ceq_feq _ _ _ _ (E1 y' Hy') (E2 y' Hy') (HB y' Hy' Hi)).
        -- exists y; split; [exact Hy|split; [|exact (HR y Hy HRy)]].
           intros y' Hy' Hv; pose proof (probe_dom _ _ Hy') as Hd.
           exact (feq_trans _ _ _ (feq_sym _ _ (E1 y' Hd)) (feq_trans _ _ _ (Hpre y' Hy' Hv) (E2 y' Hd))).
Qed.

Lemma KG_irrefl (R Rc : rvar -> fres -> Prop) all k k' :
  feqd all k k' -> (forall y, probe all y -> ~ R y (k' y)) -> (forall y, dom all y -> ~ Rc y (k' y)) -> ~ KG R Rc all k k'.
Proof.
  intros E HR HRc [[d [d' [H1 [H2 Hlt]]]]|[d [H1 [H2 [[n [Hn Hn']]|[_ [[B HB]|[_ [y [Hy [_ HRy]]]]]]]]]]].
  - pose proof (deep_eq _ _ _ _ H1 H2 (feqd_big _ _ _ E)); lia.
  - exact (Hn' (hle_feq _ _ _ _ (feqd_sym _ _ _ E) Hn)).
  - exact (HRc _ (dom_big _ B) (HB _ (dom_big _ B) (le_n _))).
  - exact (HR y Hy HRy).
Qed.

Lemma KG_trans (R1 R2 R3 Rc1 Rc2 Rc3 : rvar -> fres -> Prop) all k1 k2 k3 :
  (forall y, probe all y -> feq (k1 y) (k2 y) -> R2 y (k3 y) -> R3 y (k3 y)) ->
  (forall y, probe all y -> R1 y (k2 y) -> feq (k2 y) (k3 y) -> R3 y (k3 y)) ->
  (forall y, probe all y -> R1 y (k2 y) -> R2 y (k3 y) -> R3 y (k3 y)) ->
  (forall y, dom all y -> ceq (k1 y) (k2 y) -> Rc2 y (k3 y) -> Rc3 y (k3 y)) ->
  (forall y, dom all y -> Rc1 y (k2 y) -> ceq (k2 y) (k3 y) -> Rc3 y (k3 y)) ->
  (forall y, dom all y -> Rc1 y (k2 y) -> Rc2 y (k3 y) -> Rc3 y (k3 y)) ->
  KG R1 Rc1 all k1 k2 -> KG R2 Rc2 all k2 k3 -> KG R3 Rc3 all k1 k3.
Proof.
  intros HL HRt HT HLc HRtc HTc G1 G2.
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
      * left; exists (B1 + B2'); intros y Hy Hi; exact (HTc y Hy (HB1 y Hy ltac:(lia)) (HB2 y Hy ltac:(lia))).
      * left; exists (B1 + B2'); intros y Hy Hi; exact (HRtc y Hy (HB1 y Hy ltac:(lia)) (HB2 y Hy ltac:(lia))).
      * left; exists (B1 + B2'); intros y Hy Hi; exact (HLc y Hy (HB1 y Hy ltac:(lia)) (HB2 y Hy ltac:(lia))).
      * right; split; [exists (B1 + B2'); intros y Hy Hi; exact (ceq_trans _ _ _ (HB1 y Hy ltac:(lia)) (HB2 y Hy ltac:(lia)))|].
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

Definition rprops (f : fres) : Prop :=
  (forall g, feq f g -> ~ rgt false f g)
  /\ (forall g, ceq f g -> ~ rgt true f g)
  /\ (forall c f' g g', feq f f' -> feq g g' -> rgt c f g -> rgt c f' g')
  /\ (forall c f' g g', feq f f' -> feq g g' -> rgt c f' g' -> rgt c f g)
  /\ (forall c g h, rgt c f g -> rgt c g h -> rgt c f h)
  /\ (forall g h, ceq f g -> rgt true g h -> rgt true f h)
  /\ (forall g h, rgt true f g -> ceq g h -> rgt true f h).

(** The comparison of payloads, for results that have the properties. *)
Lemma KG_props all k :
  (forall y, rprops (k y)) ->
  (forall k', feqd all k k' -> ~ KG (fun y g => rgt false (k y) g) (fun y g => rgt true (k y) g) all k k')
  /\ (forall k1 k2 k2', feqd all k k1 -> feqd all k2 k2' ->
        KG (fun y g => rgt false (k y) g) (fun y g => rgt true (k y) g) all k k2 ->
        KG (fun y g => rgt false (k1 y) g) (fun y g => rgt true (k1 y) g) all k1 k2')
  /\ (forall k1 k2 k2', feqd all k k1 -> feqd all k2 k2' ->
        KG (fun y g => rgt false (k1 y) g) (fun y g => rgt true (k1 y) g) all k1 k2' ->
        KG (fun y g => rgt false (k y) g) (fun y g => rgt true (k y) g) all k k2)
  /\ (forall k2 k3,
        KG (fun y g => rgt false (k y) g) (fun y g => rgt true (k y) g) all k k2 ->
        KG (fun y g => rgt false (k2 y) g) (fun y g => rgt true (k2 y) g) all k2 k3 ->
        KG (fun y g => rgt false (k y) g) (fun y g => rgt true (k y) g) all k k3).
Proof.
  intros IH; split; [|split; [|split]].
  - intros k' E; apply KG_irrefl; [exact E| |].
    + intros y Hy; apply (proj1 (IH y)), E, probe_dom, Hy.
    + intros y Hy; apply (proj1 (proj2 (IH y))), feq_ceq, E, Hy.
  - intros k1 k2 k2' E1 E2; apply KG_compat; [exact E1|exact E2| |].
    + intros y Hy Hr; exact (proj1 (proj2 (proj2 (IH y))) false _ _ _ (E1 y (probe_dom _ _ Hy)) (E2 y (probe_dom _ _ Hy)) Hr).
    + intros y Hy Hr; exact (proj1 (proj2 (proj2 (IH y))) true _ _ _ (E1 y Hy) (E2 y Hy) Hr).
  - intros k1 k2 k2' E1 E2; apply KG_compat; [exact (feqd_sym _ _ _ E1)|exact (feqd_sym _ _ _ E2)| |].
    + intros y Hy Hr; exact (proj1 (proj2 (proj2 (proj2 (IH y)))) false _ _ _ (E1 y (probe_dom _ _ Hy)) (E2 y (probe_dom _ _ Hy)) Hr).
    + intros y Hy Hr; exact (proj1 (proj2 (proj2 (proj2 (IH y)))) true _ _ _ (E1 y Hy) (E2 y Hy) Hr).
  - intros k2 k3; apply KG_trans.
    + intros y _ E Hr; exact (proj1 (proj2 (proj2 (proj2 (IH y)))) false _ _ _ E (feq_refl _) Hr).
    + intros y _ Hr E; exact (proj1 (proj2 (proj2 (IH y))) false _ _ _ (feq_refl _) E Hr).
    + intros y _ Hr Hr'; exact (proj1 (proj2 (proj2 (proj2 (proj2 (IH y))))) false _ _ Hr Hr').
    + intros y _ C Hr; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (IH y)))))) _ _ C Hr).
    + intros y _ Hr C; exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (IH y)))))) _ _ Hr C).
    + intros y _ Hr Hr'; exact (proj1 (proj2 (proj2 (proj2 (proj2 (IH y))))) true _ _ Hr Hr').
Qed.

Theorem rgt_props f : rprops f.
Proof.
  induction f as [v|u b k IH|a z k IH].
  - split; [intros [v'| |] E; cbn [feq] in E; try contradiction; subst v'; exact (vlt_irrefl v)|].
    split; [intros [v'| |] E; cbn [ceq] in E; try contradiction; cbn [rgt]; tauto|].
    split; [intros c [v'| |] [w| |] [w'| |]; cbn [feq rgt]; try tauto; intros; subst; tauto|].
    split; [intros c [v'| |] [w| |] [w'| |]; cbn [feq rgt]; try tauto; intros; subst; tauto|].
    split; [intros c [w| |] [w'| |]; cbn [rgt]; try tauto; destruct c; [tauto|intros H1 H2; exact (vlt_trans _ _ _ H2 H1)]|].
    split; [intros [w| |] [w'| |]; cbn [rgt ceq]; tauto|].
    intros [w| |] [w'| |]; cbn [rgt ceq]; tauto.
  - destruct (KG_props (isb b) k IH) as [Ki [Kc [Kr Kt]]].
    assert (P1 : forall g, feq (FTerm u b k) g -> ~ rgt true (FTerm u b k) g /\ ~ rgt false (FTerm u b k) g).
    { intros [|u' b' k'|] E; cbn [feq] in E; try contradiction.
      apply feq_term in E; destruct E as [<- [<- E]]; cbn [rgt].
      split; intros [H|[_ [H|[_ H]]]]; try lia; try exact (bgt_irrefl _ H); exact (Ki _ E H). }
    assert (P2 : forall c f' g g', feq (FTerm u b k) f' -> feq g g' -> rgt c (FTerm u b k) g -> rgt c f' g').
    { intros c [|u1 b1 k1|] g g' E; cbn [feq] in E; try contradiction.
      apply feq_term in E; destruct E as [<- [<- E]].
      destruct g as [w|u' b' k'|a' z' k'], g' as [w'|u'' b'' k''|a'' z'' k'']; cbn [feq rgt]; try tauto.
      intros E'; apply feq_term in E'; destruct E' as [<- [<- E']].
      intros [H|[Hu [H|[Hb H]]]]; [left; exact H|right; split; [exact Hu|left; exact H]|].
      right; split; [exact Hu|right; split; [exact Hb|]]; subst b'.
      exact (Kc _ _ _ E E' H). }
    assert (P3 : forall c f' g g', feq (FTerm u b k) f' -> feq g g' -> rgt c f' g' -> rgt c (FTerm u b k) g).
    { intros c [|u1 b1 k1|] g g' E; cbn [feq] in E; try contradiction.
      apply feq_term in E; destruct E as [<- [<- E]].
      destruct g as [w|u' b' k'|a' z' k'], g' as [w'|u'' b'' k''|a'' z'' k'']; cbn [feq rgt]; try tauto.
      intros E'; apply feq_term in E'; destruct E' as [<- [<- E']].
      intros [H|[Hu [H|[Hb H]]]]; [left; exact H|right; split; [exact Hu|left; exact H]|].
      right; split; [exact Hu|right; split; [exact Hb|]]; subst b'.
      exact (Kr _ _ _ E E' H). }
    split; [intros g E; exact (proj2 (P1 g E))|].
    split; [intros g E; destruct g; cbn [ceq] in E; try contradiction; exact (proj1 (P1 _ E))|].
    split; [exact P2|split; [exact P3|split]].
    + intros c [w|u' b' k'|a' z' k'] [w'|u'' b'' k''|a'' z'' k'']; cbn [rgt]; try tauto.
      intros [H1|[<- [H1|[<- H1]]]] [H2|[<- [H2|[<- H2]]]]; try (left; lia);
        try (right; split; [reflexivity|left; exact (bgt_trans _ _ _ H1 H2)]);
        try (right; split; [reflexivity|left; exact H1]); try (right; split; [reflexivity|left; exact H2]).
      right; split; [reflexivity|right; split; [reflexivity|exact (Kt _ _ H1 H2)]].
    + split.
      * intros g h C Hr; destruct g as [|u' b' k'|]; cbn [ceq] in C; try contradiction.
        exact (P3 true _ _ _ C (feq_refl _) Hr).
      * intros [w|u' b' k'|a' z' k'] h Hr C; cbn [rgt] in Hr; try tauto.
        -- destruct h; cbn [ceq] in C; try contradiction; cbn [rgt]; exact I.
        -- destruct h as [|u'' b'' k''|]; cbn [ceq] in C; try contradiction.
           exact (P2 true _ _ _ (feq_refl _) C Hr).
  - assert (Kp := KG_props true k IH); destruct Kp as [Ki [Kc [Kr Kt]]].
    assert (P2 : forall c f' g g', feq (FStuck a z k) f' -> feq g g' -> rgt c (FStuck a z k) g -> rgt c f' g').
    { intros c [| |a1 z1 k1] g g' E; cbn [feq] in E; try contradiction.
      apply feq_stuck in E; destruct E as [<- [<- E]].
      destruct g as [w|u' b' k'|a' z' k'], g' as [w'|u'' b'' k''|a'' z'' k'']; cbn [feq rgt]; try tauto.
      intros E'; apply feq_stuck in E'; destruct E' as [<- [<- E']].
      intros [H|[Ha [H|H]]]; [left; exact H|right; split; [exact Ha|left; exact (Kc _ _ _ E E' H)]|].
      right; split; [exact Ha|right]; destruct c; [exact H|].
      destruct H as [Hk H]; split; [exact (feqd_trans _ _ _ _ (feqd_sym _ _ _ E) (feqd_trans _ _ _ _ Hk E'))|exact H]. }
    assert (P3 : forall c f' g g', feq (FStuck a z k) f' -> feq g g' -> rgt c f' g' -> rgt c (FStuck a z k) g).
    { intros c [| |a1 z1 k1] g g' E; cbn [feq] in E; try contradiction.
      apply feq_stuck in E; destruct E as [<- [<- E]].
      destruct g as [w|u' b' k'|a' z' k'], g' as [w'|u'' b'' k''|a'' z'' k'']; cbn [feq rgt]; try tauto.
      intros E'; apply feq_stuck in E'; destruct E' as [<- [<- E']].
      intros [H|[Ha [H|H]]]; [left; exact H|right; split; [exact Ha|left; exact (Kr _ _ _ E E' H)]|].
      right; split; [exact Ha|right]; destruct c; [exact H|].
      destruct H as [Hk H]; split; [exact (feqd_trans _ _ _ _ E (feqd_trans _ _ _ _ Hk (feqd_sym _ _ _ E')))|exact H]. }
    split; [|split; [|split; [exact P2|split; [exact P3|split; [|split]]]]].
    + intros [| |a' z' k'] E; cbn [feq] in E; try contradiction.
      apply feq_stuck in E; destruct E as [<- [<- E]]; cbn [rgt].
      intros [H|[_ [H|[_ H]]]]; [lia|exact (Ki _ E H)|exact (vlt_irrefl _ H)].
    + intros [| |a' z' k'] C; cbn [ceq] in C; try contradiction; destruct C as [<- C].
      cbn [rgt]; intros [H|[_ [H|H]]]; [lia|exact (Ki _ (fun y _ => C y) H)|exact H].
    + intros c [w|u' b' k'|a' z' k'] [w'|u'' b'' k''|a'' z'' k'']; cbn [rgt]; try tauto.
      intros [H1|[<- [H1|H1]]] [H2|[<- [H2|H2]]]; try (left; lia).
      * right; split; [reflexivity|left; exact (Kt _ _ H1 H2)].
      * right; split; [reflexivity|left]; destruct c; [destruct H2|].
        destruct H2 as [E2 _]; exact (Kc k k' k'' (feqd_refl _ _) E2 H1).
      * right; split; [reflexivity|left]; destruct c; [destruct H1|].
        destruct H1 as [E1 _]; exact (Kr k' k'' k'' E1 (feqd_refl _ _) H2).
      * right; split; [reflexivity|right]; destruct c; [destruct H1|].
        destruct H1 as [E1 H1]; destruct H2 as [E2 H2].
        split; [exact (feqd_trans _ _ _ _ E1 E2)|exact (vlt_trans _ _ _ H2 H1)].
    + intros g h C Hr; destruct g as [| |a' z' k']; cbn [ceq] in C; try contradiction; destruct C as [<- C].
      destruct h as [w|u'' b'' k''|a'' z'' k'']; cbn [rgt] in Hr |- *; try tauto.
      destruct Hr as [H|[<- [H|H]]]; [left; exact H| |destruct H].
      right; split; [reflexivity|left; exact (Kr k' k'' k'' (fun y _ => C y) (feqd_refl _ _) H)].
    + intros g h Hr C; destruct g as [w|u' b' k'|a' z' k']; cbn [rgt] in Hr; try tauto.
      * destruct h; cbn [ceq] in C; try contradiction; exact I.
      * destruct h; cbn [ceq] in C; try contradiction; exact I.
      * destruct h as [| |a'' z'' k'']; cbn [ceq] in C; try contradiction; destruct C as [<- C]; cbn [rgt].
        destruct Hr as [H|[<- [H|H]]]; [left; exact H| |destruct H].
        right; split; [reflexivity|left; exact (Kc k k' k'' (feqd_refl _ _) (fun y _ => C y) H)].
Qed.

Lemma rgt_irrefl f g : feq f g -> ~ rgt false f g.
Proof. exact (proj1 (rgt_props f) g). Qed.

Lemma rgt_feq c f f' g g' : feq f f' -> feq g g' -> rgt c f g -> rgt c f' g'.
Proof. exact (proj1 (proj2 (proj2 (rgt_props f))) c f' g g'). Qed.

Lemma rgt_trans c f g h : rgt c f g -> rgt c g h -> rgt c f h.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (rgt_props f))))) c g h). Qed.

(** ** The order on payloads *)

Lemma kgt_irrefl all k k' : feqd all k k' -> ~ kgt all k k'.
Proof. exact (proj1 (KG_props all k (fun y => rgt_props (k y))) k'). Qed.

Lemma kgt_feq all k1 k1' k2 k2' : feqd all k1 k1' -> feqd all k2 k2' -> kgt all k1 k2 -> kgt all k1' k2'.
Proof. exact (proj1 (proj2 (KG_props all k1 (fun y => rgt_props (k1 y)))) k1' k2 k2'). Qed.

Lemma kgt_trans all k1 k2 k3 : kgt all k1 k2 -> kgt all k2 k3 -> kgt all k1 k3.
Proof. exact (proj2 (proj2 (proj2 (KG_props all k1 (fun y => rgt_props (k1 y))))) k2 k3). Qed.

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
