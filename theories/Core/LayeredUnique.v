(** * Layered words in normal form are unique

    In the free model of [Unique], a layered word is its steps one after
    the other, each with the rest as its continuation; so a term of a
    segment has the rest of the word as what happens to its names.

    The normal-form conditions ([lnf]) are stated on that meaning.  For a
    segment [Sg] followed by [r]:

    - [Sg] is a canonical segment whose terms have the identity payload,
      and has a term unless it is the last;
    - the payloads of successive layers decrease in a strict order [gt]
      on what a payload does to named variables, and a last segment
      that does nothing to named variables has a term;
    - a variable goes on as the least named variable of the rest with
      the same result, and as a bound variable only when there is none;
    - every bound variable of the rest is used, and (except for the
      first segment of the word) the bound variables come in the order
      of what they go on as; distinct bound variables of a rest have
      distinct results.

    [lw_unique]: two words satisfying them with the same meaning are the
    same word.  The order [gt] is a parameter: any relation that is
    irreflexive, transitive and only looks at named variables.

    Not covered yet: atoms in the word, and terms with a payload atom. *)

From Stdlib Require Import Arith List Lia Bool.
From ShiftedNames.Core Require Import Label Var Adjustment Normalise Unique Layered.
Import ListNotations.

Section LUnique.

Variable lenv : list label.
Variable labs : list lexp.
Hypothesis Hinj : forall h h', In h labs -> In h' labs -> lden lenv h = lden lenv h' -> h = h'.

Local Notation lden := (lden lenv).
Local Notation fs := (fs lenv).
Local Notation ft := (ft lenv).
Local Notation fw := (fw lenv).
Local Notation ftl := (ftl lenv).
Local Notation fget := (fget lenv).
Local Notation sget := (sget lenv).
Local Notation sshape := (sshape lenv labs).

(** ** The free meaning of a layered word *)

Fixpoint flw (l : lword) (K : rvar -> fres) (v : rvar) : fres :=
  match l with
  | [] => K v
  | LS s :: r => fs s (flw r K) v
  | LA L a :: r => latom lenv L a (flw r K) v
  end.

Definition R (l : lword) : rvar -> fres := flw l FVar.

Definition named (v : rvar) : Prop := v_label v <> None.
Definition bound (v : rvar) : Prop := v_label v = None.

Lemma named_or_bound v : named v \/ bound v.
Proof. unfold named, bound; destruct (v_label v); [left; discriminate|right; reflexivity]. Qed.

Lemma bound_eq s s' : bound s -> bound s' -> v_index s = v_index s' -> s = s'.
Proof. destruct s as [l i], s' as [l' i']; unfold bound; cbn; intros -> -> ->; reflexivity. Qed.

(** Agreement on named variables. *)
Definition keq (k k' : rvar -> fres) : Prop := forall y, named y -> feq (k y) (k' y).

Lemma keq_refl k : keq k k.
Proof. intros y _; apply feq_refl. Qed.

Lemma keq_sym k k' : keq k k' -> keq k' k.
Proof. intros H y Hy; apply feq_sym, H, Hy. Qed.

Lemma keq_trans k1 k2 k3 : keq k1 k2 -> keq k2 k3 -> keq k1 k3.
Proof. intros H1 H2 y Hy; exact (feq_trans _ _ _ (H1 y Hy) (H2 y Hy)). Qed.

(** Distinct bound variables have distinct results. *)
Definition binj (k : rvar -> fres) : Prop := forall s s', bound s -> bound s' -> feq (k s) (k s') -> s = s'.

Lemma binj_var : binj FVar.
Proof. intros s s' _ _ H; exact H. Qed.

(** ** What a segment does to a variable *)

Definition tres (t : ntgt) : rvar + nat :=
  match t with NVar h j => inl (mk_rvar (lden h) j) | NBind u _ _ => inr u end.

Definition sres (Sg : seg) (v : rvar) : rvar + nat :=
  match sget (v_label v) Sg with
  | Some (ts, m) =>
      if v_index v <? tlen ts then tres (tnth ts (v_index v))
      else inl (mk_rvar (v_label v) (v_index v - tlen ts + m))
  | None => inl v
  end.

(** The targets of a layered segment: variables, and terms whose payload
    is the rest of the word. *)
Definition tpure (t : ntgt) : Prop :=
  match t with NVar h _ => In h labs | NBind _ w b => w = WEnd SNil /\ b = None end.

Definition spure (Sg : seg) : Prop := Forall tpure (stgts Sg).

Definition res (Sg : seg) (K : rvar -> fres) (x : rvar) : fres :=
  match sres Sg x with inl y => K y | inr u => FTerm u None K end.

Lemma fs_pure Sg K v : spure Sg -> fs Sg K v = res Sg K v.
Proof.
  intros HS; unfold res, sres; rewrite (fs_get lenv); unfold Unique.fget.
  destruct (sget (v_label v) Sg) as [[ts m]|] eqn:E; [|destruct v; reflexivity].
  destruct (Nat.ltb_spec (v_index v) (tlen ts)) as [Hlt|Hge].
  - rewrite (ftl_lt lenv) by exact Hlt.
    assert (Hp : tpure (tnth ts (v_index v))).
    { unfold spure in HS; rewrite Forall_forall in HS; apply HS, (sget_tgts lenv _ _ _ _ E), tnth_in, Hlt. }
    destruct (tnth ts (v_index v)) as [h j|u w b]; [reflexivity|].
    destruct Hp as [-> ->]; reflexivity.
  - rewrite (ftl_ge lenv) by exact Hge; reflexivity.
Qed.

Lemma sres_nil v : sres SNil v = inl v.
Proof. reflexivity. Qed.

(** A segment has a term. *)
Definition sterm (Sg : seg) : Prop := exists v u, sres Sg v = inr u.

(** ** The order on variables: named ones first *)

Definition vlt (a b : rvar) : Prop :=
  olabel_lt (v_label a) (v_label b) \/ (v_label a = v_label b /\ v_index a < v_index b).

Lemma vlt_irrefl a : ~ vlt a a.
Proof. intros [H|[_ H]]; [exact (olabel_lt_irrefl _ H)|lia]. Qed.

Lemma vlt_asym a b : vlt a b -> vlt b a -> False.
Proof.
  intros [H|[E H]] [H'|[E' H']].
  - exact (olabel_lt_irrefl _ (olabel_lt_trans _ _ _ H H')).
  - rewrite E' in H; exact (olabel_lt_irrefl _ H).
  - rewrite E in H'; exact (olabel_lt_irrefl _ H').
  - lia.
Qed.

Lemma vlt_total a b : vlt a b \/ a = b \/ vlt b a.
Proof.
  destruct a as [l i], b as [l' i']; unfold vlt; cbn [v_label v_index].
  destruct (olabel_trichotomy l l') as [H|[<-|H]]; [left; left; exact H| |right; right; left; exact H].
  destruct (Nat.lt_trichotomy i i') as [H|[<-|H]]; [left; right; split; [reflexivity|exact H]|right; left; reflexivity|].
  right; right; right; split; [reflexivity|exact H].
Qed.

Lemma vlt_bound i j : vlt (mk_rvar None i) (mk_rvar None j) <-> i < j.
Proof.
  unfold vlt; cbn [v_label v_index]; split; [intros [H|[_ H]]; [destruct (olabel_lt_irrefl _ H)|exact H]|].
  intros H; right; split; [reflexivity|exact H].
Qed.

(** ... and on what a segment makes of a variable: terms first. *)
Definition rlt (a b : rvar + nat) : Prop :=
  match a, b with
  | inr u, inr u' => u < u'
  | inr _, inl _ => True
  | inl _, inr _ => False
  | inl y, inl y' => vlt y y'
  end.

Lemma rlt_asym a b : rlt a b -> rlt b a -> False.
Proof. destruct a as [y|u], b as [y'|u']; cbn [rlt]; try tauto; [apply vlt_asym|lia]. Qed.

Lemma rlt_total a b : rlt a b \/ a = b \/ rlt b a.
Proof.
  destruct a as [y|u], b as [y'|u']; cbn [rlt]; [|tauto|tauto|].
  - destruct (vlt_total y y') as [H|[<-|H]]; tauto.
  - destruct (Nat.lt_trichotomy u u') as [H|[<-|H]]; tauto.
Qed.

(** ** The normal-form conditions *)

(** The order on payloads. *)
Variable gt : (rvar -> fres) -> (rvar -> fres) -> Prop.
Hypothesis gt_irrefl : forall k k', keq k k' -> ~ gt k k'.
Hypothesis gt_trans : forall k1 k2 k3, gt k1 k2 -> gt k2 k3 -> gt k1 k3.
Hypothesis gt_keq : forall k1 k1' k2 k2', keq k1 k1' -> keq k2 k2' -> gt k1 k2 -> gt k1' k2'.

Record segok (first : bool) (Sg : seg) (r : lword) : Prop := {
  so_shape : sshape false Sg;
  so_pure : spure Sg;
  so_term : r <> [] -> sterm Sg;
  so_order : forall Sg2 r2, r = LS Sg2 :: r2 -> sterm Sg2 -> gt (R r) (R r2);
  so_last : forall G, r = [LS G] -> keq (R r) FVar -> sterm G;
  so_named : forall x y, sres Sg x = inl y -> named y ->
               forall y', named y' -> feq (R r y') (R r y) -> ~ vlt y' y;
  so_bound : forall x y, sres Sg x = inl y -> bound y -> forall y', named y' -> ~ feq (R r y') (R r y);
  so_hit : r <> [] -> forall y, bound y -> exists x, sres Sg x = inl y;
  so_sorted : first = false ->
                forall i j, i < j -> ~ rlt (sres Sg (mk_rvar None j)) (sres Sg (mk_rvar None i))
}.

Fixpoint lnf (first : bool) (l : lword) : Prop :=
  match l with
  | [] => True
  | LS Sg :: r => Sg <> SNil /\ segok first Sg r /\ lnf false r /\ (first = false -> binj (R l))
  | LA _ _ :: _ => False
  end.

Lemma segok_nil first : segok first SNil [].
Proof.
  constructor.
  - split; constructor.
  - constructor.
  - intros H; destruct (H eq_refl).
  - intros Sg2 r2 H; discriminate H.
  - intros G H; discriminate H.
  - intros x y H Hy y' Hy' E; rewrite sres_nil in H; injection H as <-; cbn in E; subst y'; apply vlt_irrefl.
  - intros x y H Hy y' Hy' E; cbn in E; subst y'; exact (Hy' Hy).
  - intros H; destruct (H eq_refl).
  - intros _ i j Hij; rewrite !sres_nil; cbn [rlt]; rewrite vlt_bound; lia.
Qed.

(** A word as its first segment and the rest; the empty word as the
    empty segment and nothing. *)
Definition view (l : lword) : seg * lword :=
  match l with LS Sg :: r => (Sg, r) | _ => (SNil, []) end.

Lemma lnf_view first l : lnf first l ->
  segok first (fst (view l)) (snd (view l)) /\ lnf false (snd (view l))
  /\ (forall x, R l x = res (fst (view l)) (R (snd (view l))) x)
  /\ (first = false -> binj (R l)).
Proof.
  destruct l as [|[Sg|L a] r]; cbn [lnf view fst snd].
  - intros _; split; [apply segok_nil|split; [exact I|split; [reflexivity|intros _; apply binj_var]]].
  - intros [_ [HS [Hr Hb]]]; split; [exact HS|split; [exact Hr|split; [|exact Hb]]].
    intros x; unfold R; cbn [flw]; apply fs_pure, (so_pure _ _ _ HS).
  - intros [].
Qed.

Lemma view_eq first l m : lnf first l -> lnf first m -> view l = view m -> l = m.
Proof.
  destruct l as [|[Sg|L a] r], m as [|[Sg'|L' a'] r']; cbn [lnf view]; try (intros _ []; fail); try (intros [] ; fail).
  - reflexivity.
  - intros _ [Hn _] E; injection E as E _; destruct (Hn (eq_sym E)).
  - intros [Hn _] _ E; injection E as E _; destruct (Hn E).
  - intros _ _ E; injection E as -> ->; reflexivity.
Qed.

(** ** Uniqueness *)

Lemma lnf_binj r : lnf false r -> binj (R r).
Proof.
  destruct r as [|[Sg|L a] r]; cbn [lnf]; [intros _; apply binj_var| |intros []].
  intros [_ [_ [_ H]]]; exact (H eq_refl).
Qed.

Lemma R_cons first Sg r : segok first Sg r -> forall x, R (LS Sg :: r) x = res Sg (R r) x.
Proof. intros HS x; unfold R; cbn [flw]; apply fs_pure, (so_pure _ _ _ HS). Qed.

(** A term reached through the rest has a payload below the rest. *)
Lemma later r : forall first Sg, segok first Sg r -> lnf false r ->
  forall y u b k, R r y = FTerm u b k -> b = None /\ gt (R r) k.
Proof.
  induction r as [|[Sg2|L a] r2 IH]; intros first Sg HS Hr y u b k E; [discriminate E| |destruct Hr].
  destruct Hr as [_ [HS2 [Hr2 _]]]; rewrite (R_cons _ _ _ HS2) in E; unfold res in E.
  destruct (sres Sg2 y) as [y2|u2] eqn:E2.
  - destruct (IH false Sg2 HS2 Hr2 y2 u b k E) as [Eb G2]; split; [exact Eb|].
    assert (Hne : r2 <> []) by (intros ->; discriminate E).
    exact (gt_trans _ _ _ (so_order _ _ _ HS Sg2 r2 eq_refl (so_term _ _ _ HS2 Hne)) G2).
  - injection E as <- <- <-; split; [reflexivity|].
    apply (so_order _ _ _ HS Sg2 r2 eq_refl); exists y, u2; exact E2.
Qed.

(** A term with the continuation [K], against what a word does to a
    variable: its own term, or a term further on. *)
Lemma term_match first Sg r u K x :
  segok first Sg r -> lnf false r ->
  feq (FTerm u None K) (res Sg (R r) x) ->
  (sres Sg x = inr u /\ keq K (R r))
  \/ (exists y k, sres Sg x = inl y /\ r <> [] /\ keq K k /\ gt (R r) k).
Proof.
  intros HS Hr; unfold res; destruct (sres Sg x) as [y|u'] eqn:E.
  - destruct (R r y) as [v|u2 b2 k2|a z k2] eqn:Ey; cbn [feq]; try (intros []; fail).
    intros [<- [<- Hk]]; right; exists y, k2; split; [reflexivity|].
    split; [intros ->; discriminate Ey|].
    split; [intros z Hz; apply Hk; intros _; exact Hz|exact (proj2 (later r first Sg HS Hr y u None k2 Ey))].
  - cbn [feq]; intros [<- [_ Hk]]; left; split; [reflexivity|intros z Hz; apply Hk; intros _; exact Hz].
Qed.

(** If one word has a term in its first segment, so has the other, and
    the two rests agree on named variables. *)
Lemma first_layer first Sg r Sg' r' :
  segok first Sg r -> lnf false r -> segok first Sg' r' -> lnf false r' ->
  (forall x, exists x', feq (res Sg (R r) x) (res Sg' (R r') x')) ->
  (forall x', exists x, feq (res Sg (R r) x) (res Sg' (R r') x')) ->
  sterm Sg -> sterm Sg' /\ keq (R r) (R r').
Proof.
  intros HS Hr HS' Hr' H1 H2 [x0 [u E0]].
  destruct (H1 x0) as [x0' F]; unfold res at 1 in F; rewrite E0 in F.
  destruct (term_match _ _ _ _ _ _ HS' Hr' F) as [[E' K1]|[y' [k' [E' [Hne [K1 G1]]]]]].
  { split; [exists x0', u; exact E'|exact K1]. }
  destruct (so_term _ _ _ HS' Hne) as [x1' [u1 E1']].
  destruct (H2 x1') as [x1 F1]; unfold res at 2 in F1; rewrite E1' in F1; apply feq_sym in F1.
  destruct (term_match _ _ _ _ _ _ HS Hr F1) as [[E1 K2]|[y [k [E1 [_ [K2 G2]]]]]].
  { split; [exists x1', u1; exact E1'|exact (keq_sym _ _ K2)]. }
  exfalso.
  pose proof (gt_keq _ _ _ _ (keq_refl _) (keq_sym _ _ K1) G1) as G1'.
  pose proof (gt_keq _ _ _ _ (keq_refl _) (keq_sym _ _ K2) G2) as G2'.
  exact (gt_irrefl _ _ (keq_refl _) (gt_trans _ _ _ G2' G1')).
Qed.

(** A word that ends after its first segment against one that goes on. *)
Lemma no_trivial_tail first Sg Sg' r' :
  segok first Sg' r' -> lnf false r' -> r' <> [] -> keq (R r') FVar ->
  (forall x', exists x, feq (res Sg FVar x) (res Sg' (R r') x')) -> False.
Proof.
  intros HS' Hr' Hne Hk H2.
  destruct r' as [|[Sg2|L a] r2]; [destruct (Hne eq_refl)| |destruct Hr'].
  pose proof Hr' as Hr'0; destruct Hr' as [_ [HS2 [Hr2 _]]].
  assert (Ht : sterm Sg2).
  { destruct r2 as [|st r3]; [exact (so_last _ _ _ HS' Sg2 eq_refl Hk)|apply (so_term _ _ _ HS2); discriminate]. }
  destruct Ht as [y2 [c E2]].
  assert (Ey : R (LS Sg2 :: r2) y2 = FTerm c None (R r2)) by (rewrite (R_cons _ _ _ HS2); unfold res; rewrite E2; reflexivity).
  destruct (named_or_bound y2) as [Hn|Hb].
  - pose proof (Hk y2 Hn) as F; rewrite Ey in F; exact F.
  - destruct (so_hit _ _ _ HS' Hne y2 Hb) as [x' Ex'].
    destruct (H2 x') as [x F]; unfold res at 2 in F; rewrite Ex', Ey in F.
    unfold res in F; destruct (sres Sg x) as [y|u]; cbn [feq] in F; [destruct F|].
    destruct F as [_ [_ F]].
    assert (K2 : keq FVar (R r2)) by (intros z Hz; apply F; intros _; exact Hz).
    pose proof (so_order _ _ _ HS' Sg2 r2 eq_refl (ex_intro _ y2 (ex_intro _ c E2))) as G.
    exact (gt_irrefl _ _ (keq_refl _) (gt_keq _ _ _ _ Hk (keq_sym _ _ K2) G)).
Qed.

(** The bound variables of the two rests correspond. *)
Lemma tail_match first Sg r Sg' r' :
  segok first Sg r -> lnf false r -> segok first Sg' r' -> lnf false r' ->
  r <> [] -> keq (R r) (R r') ->
  (forall x, exists x', feq (res Sg (R r) x) (res Sg' (R r') x')) ->
  forall s, bound s -> exists s', bound s' /\ feq (R r s) (R r' s').
Proof.
  intros HS Hr HS' Hr' Hne Hk H1 s Hs.
  destruct (so_hit _ _ _ HS Hne s Hs) as [x Ex].
  destruct (H1 x) as [x' F]; unfold res at 1 in F; rewrite Ex in F.
  unfold res in F; destruct (sres Sg' x') as [y'|u'] eqn:E'.
  - destruct (named_or_bound y') as [Hn|Hb]; [|exists y'; split; [exact Hb|exact F]].
    exfalso; apply (so_bound _ _ _ HS x s Ex Hs y' Hn).
    exact (feq_trans _ _ _ (Hk y' Hn) (feq_sym _ _ F)).
  - exfalso; destruct (R r s) as [v|u b k|a z k] eqn:Es; cbn [feq] in F; try (destruct F; fail).
    destruct F as [_ [Eb F]]; subst b.
    assert (K1 : keq k (R r')) by (intros z Hz; apply F; intros _; exact Hz).
    pose proof (proj2 (later r first Sg HS Hr s u None k Es)) as G.
    exact (gt_irrefl _ _ (keq_trans _ _ _ Hk (keq_sym _ _ K1)) G).
Qed.

(** With the same rest, variables with the same result are treated the
    same way. *)
Lemma same_target first first' Sg Sg' r :
  segok first Sg r -> segok first' Sg' r -> lnf false r ->
  forall x x', feq (res Sg (R r) x) (res Sg' (R r) x') -> sres Sg x = sres Sg' x'.
Proof.
  intros HS HS' Hr x x'; unfold res.
  destruct (sres Sg x) as [y|u] eqn:E, (sres Sg' x') as [y'|u'] eqn:E'.
  - intros F; f_equal.
    destruct (named_or_bound y) as [Hy|Hy], (named_or_bound y') as [Hy'|Hy'].
    + destruct (vlt_total y y') as [H|[H|H]]; [|exact H|].
      * destruct (so_named _ _ _ HS' x' y' E' Hy' y Hy F H).
      * destruct (so_named _ _ _ HS x y E Hy y' Hy' (feq_sym _ _ F) H).
    + destruct (so_bound _ _ _ HS' x' y' E' Hy' y Hy F).
    + destruct (so_bound _ _ _ HS x y E Hy y' Hy' (feq_sym _ _ F)).
    + exact (lnf_binj r Hr y y' Hy Hy' F).
  - intros F; exfalso; destruct (R r y) as [v|u2 b k|a z k] eqn:Ey; cbn [feq] in F; try (destruct F; fail).
    destruct F as [_ [Eb F]]; subst b.
    assert (K1 : keq k (R r)) by (intros z Hz; apply F; intros _; exact Hz).
    exact (gt_irrefl _ _ (keq_sym _ _ K1) (proj2 (later r first Sg HS Hr y u2 None k Ey))).
  - intros F; exfalso; apply feq_sym in F.
    destruct (R r y') as [v|u2 b k|a z k] eqn:Ey; cbn [feq] in F; try (destruct F; fail).
    destruct F as [_ [Eb F]]; subst b.
    assert (K1 : keq k (R r)) by (intros z Hz; apply F; intros _; exact Hz).
    exact (gt_irrefl _ _ (keq_sym _ _ K1) (proj2 (later r first' Sg' HS' Hr y' u2 None k Ey))).
  - cbn [feq]; intros [<- _]; reflexivity.
Qed.

(** Two increasing sequences related by a correspondence that keeps
    their values are related by the identity. *)
Lemma mono_id (T T' : nat -> rvar + nat) (rel : nat -> nat -> Prop) :
  (forall i j, i < j -> rlt (T i) (T j)) -> (forall i j, i < j -> rlt (T' i) (T' j)) ->
  (forall i i', rel i i' -> T i = T' i') ->
  (forall i, exists i', rel i i') -> (forall i', exists i, rel i i') ->
  forall i i', rel i i' -> i = i'.
Proof.
  intros HT HT' Hrel H1 H2.
  assert (Hirr : forall a, ~ rlt a a) by (intros a H; exact (rlt_asym a a H H)).
  assert (Hn : forall n i i', rel i i' -> i < n \/ i' < n -> i = i').
  { induction n as [|n IH]; intros i i' Hr Hlt; [lia|].
    destruct (Nat.lt_trichotomy i i') as [Hii|[Hii|Hii]]; [|exact Hii|]; exfalso.
    - destruct (H2 i) as [j Hj].
      destruct (Nat.lt_trichotomy j i) as [Hji|[Hji|Hji]].
      + pose proof (IH j i Hj ltac:(lia)); lia.
      + subst j; pose proof (HT' i i' Hii) as G; rewrite <- (Hrel _ _ Hr), <- (Hrel _ _ Hj) in G; exact (Hirr _ G).
      + pose proof (HT i j Hji) as G; rewrite (Hrel _ _ Hr), (Hrel _ _ Hj) in G.
        exact (rlt_asym _ _ G (HT' i i' Hii)).
    - destruct (H1 i') as [j' Hj'].
      destruct (Nat.lt_trichotomy j' i') as [Hji|[Hji|Hji]].
      + pose proof (IH i' j' Hj' ltac:(lia)); lia.
      + subst j'; pose proof (HT i' i Hii) as G; rewrite (Hrel _ _ Hr), (Hrel _ _ Hj') in G; exact (Hirr _ G).
      + pose proof (HT' i' j' Hji) as G; rewrite <- (Hrel _ _ Hr), <- (Hrel _ _ Hj') in G.
        exact (rlt_asym _ _ G (HT i' i Hii)). }
  intros i i' Hr; exact (Hn (S i) i i' Hr (or_introl (Nat.lt_succ_diag_r i))).
Qed.

(** Canonical segments that treat every variable the same way are the
    same. *)
Lemma seg_same Sg Sg' :
  sshape false Sg -> sshape false Sg' -> spure Sg -> spure Sg' ->
  (forall x, sres Sg x = sres Sg' x) -> Sg = Sg'.
Proof.
  intros Hs Hs' Hp Hp' H.
  refine (seg_unique lenv labs Hinj tpure tpure _ _ _ Sg Sg' Hs Hs' Hp Hp' _).
  - intros [h j|u w b] [h' j'|u' w' b']; cbn [tpure Unique.ft feq]; try (intros _ _ []; fail).
    + intros Hh Hh' E; injection E as E ->; rewrite (Hinj h h' Hh Hh' E); reflexivity.
    + intros [-> ->] [-> ->] [-> _]; reflexivity.
  - intros h j Hh; exact Hh.
  - intros h j Hh; exact Hh.
  - intros l j; rewrite <- !(fs_get lenv _ FVar (mk_rvar l j)), !fs_pure by assumption.
    unfold res; rewrite H; apply feq_refl.
Qed.

Lemma step first l m :
  (forall r r', List.length r < List.length l -> lnf false r -> lnf false r' -> keq (R r) (R r') ->
     (forall s, bound s -> exists s', bound s' /\ feq (R r s) (R r' s')) ->
     (forall s', bound s' -> exists s, bound s /\ feq (R r s) (R r' s')) -> r = r') ->
  lnf first l -> lnf first m -> keq (R l) (R m) ->
  (forall s, bound s -> exists s', bound s' /\ feq (R l s) (R m s')) ->
  (forall s', bound s' -> exists s, bound s /\ feq (R l s) (R m s')) ->
  (first = true -> forall s, bound s -> feq (R l s) (R m s)) ->
  l = m.
Proof.
  intros IH Hl Hm Hk HM1 HM2 Hid.
  destruct (lnf_view first l Hl) as [HS [Hr [EA Hb]]]; destruct (lnf_view first m Hm) as [HS' [Hr' [EA' Hb']]].
  apply (view_eq first l m Hl Hm).
  assert (Hlen : snd (view l) <> [] -> List.length (snd (view l)) < List.length l).
  { destruct l as [|[Sg0|L a] r0]; cbn [view snd List.length]; [intros H; destruct (H eq_refl)|lia|intros H; destruct (H eq_refl)]. }
  destruct (view l) as [Sg r]; destruct (view m) as [Sg' r']; cbn [fst snd] in *.
  (* every variable of one word has a counterpart in the other *)
  assert (H1 : forall x, exists x', feq (res Sg (R r) x) (res Sg' (R r') x')).
  { intros x; rewrite <- EA; destruct (named_or_bound x) as [Hx|Hx].
    - exists x; rewrite <- EA'; exact (Hk x Hx).
    - destruct (HM1 x Hx) as [x' [_ F]]; exists x'; rewrite <- EA'; exact F. }
  assert (H2 : forall x', exists x, feq (res Sg (R r) x) (res Sg' (R r') x')).
  { intros x'; rewrite <- EA'; destruct (named_or_bound x') as [Hx|Hx].
    - exists x'; rewrite <- EA; exact (Hk x' Hx).
    - destruct (HM2 x' Hx) as [x [_ F]]; exists x; rewrite <- EA; exact F. }
  assert (H1s : forall x', exists x, feq (res Sg' (R r') x') (res Sg (R r) x))
    by (intros x'; destruct (H2 x') as [x F]; exists x; exact (feq_sym _ _ F)).
  assert (H2s : forall x, exists x', feq (res Sg' (R r') x') (res Sg (R r) x))
    by (intros x; destruct (H1 x) as [x' F]; exists x'; exact (feq_sym _ _ F)).
  (* the rests are the same *)
  assert (Er : r = r').
  { destruct r as [|st r0] eqn:Dr, r' as [|st' r0'] eqn:Dr'; [reflexivity| | |].
    - exfalso; rewrite <- Dr' in *.
      assert (Hne : r' <> []) by (rewrite Dr'; discriminate).
      destruct (first_layer first Sg' r' Sg [] HS' Hr' HS Hr H1s H2s (so_term _ _ _ HS' Hne)) as [_ K].
      exact (no_trivial_tail first Sg Sg' r' HS' Hr' Hne K H2).
    - exfalso; rewrite <- Dr in *.
      assert (Hne : r <> []) by (rewrite Dr; discriminate).
      destruct (first_layer first Sg r Sg' [] HS Hr HS' Hr' H1 H2 (so_term _ _ _ HS Hne)) as [_ K].
      exact (no_trivial_tail first Sg' Sg r HS Hr Hne K H2s).
    - rewrite <- Dr, <- Dr' in *.
      assert (Hne : r <> []) by (rewrite Dr; discriminate).
      assert (Hne' : r' <> []) by (rewrite Dr'; discriminate).
      destruct (first_layer first Sg r Sg' r' HS Hr HS' Hr' H1 H2 (so_term _ _ _ HS Hne)) as [_ K].
      apply (IH r r' (Hlen Hne) Hr Hr' K).
      + exact (tail_match first Sg r Sg' r' HS Hr HS' Hr' Hne K H1).
      + intros s' Hs'.
        destruct (tail_match first Sg' r' Sg r HS' Hr' HS Hr Hne' (keq_sym _ _ K) H1s s' Hs') as [s [Hs F]].
        exists s; split; [exact Hs|exact (feq_sym _ _ F)]. }
  subst r'; f_equal.
  (* the bound variables of the two words correspond by the identity *)
  assert (Hidb : forall s, bound s -> feq (R l s) (R m s)).
  { destruct first; [exact (Hid eq_refl)|].
    set (T := fun i => sres Sg (mk_rvar None i)); set (T' := fun i => sres Sg' (mk_rvar None i)).
    set (rel := fun i i' => feq (R l (mk_rvar None i)) (R m (mk_rvar None i'))).
    assert (Hmono : forall Sg0 w, segok false Sg0 r -> (forall x, R w x = res Sg0 (R r) x) -> binj (R w) ->
              forall i j, i < j -> rlt (sres Sg0 (mk_rvar None i)) (sres Sg0 (mk_rvar None j))).
    { intros Sg0 w HS0 E0 Hb0 i j Hij.
      destruct (rlt_total (sres Sg0 (mk_rvar None i)) (sres Sg0 (mk_rvar None j))) as [G|[G|G]]; [exact G| |].
      - exfalso; assert (E : mk_rvar None i = mk_rvar None j).
        { apply Hb0; [reflexivity|reflexivity|]; rewrite !E0; unfold res; rewrite G; apply feq_refl. }
        injection E as E; lia.
      - destruct (so_sorted _ _ _ HS0 eq_refl i j Hij G). }
    assert (Hrel : forall i i', rel i i' -> i = i').
    { apply (mono_id T T' rel).
      - exact (Hmono Sg l HS EA (Hb eq_refl)).
      - exact (Hmono Sg' m HS' EA' (Hb' eq_refl)).
      - intros i i' F; unfold rel in F; rewrite EA, EA' in F; exact (same_target false false Sg Sg' r HS HS' Hr _ _ F).
      - intros i; destruct (HM1 (mk_rvar None i) eq_refl) as [[l' i'] [Hs' F]]; unfold bound in Hs'; cbn in Hs'; subst l'.
        exists i'; exact F.
      - intros i'; destruct (HM2 (mk_rvar None i') eq_refl) as [[l' i] [Hs F]]; unfold bound in Hs; cbn in Hs; subst l'.
        exists i; exact F. }
    intros [l0 i] Hs; unfold bound in Hs; cbn in Hs; subst l0.
    destruct (HM1 (mk_rvar None i) eq_refl) as [[l' i'] [Hs' F]]; unfold bound in Hs'; cbn in Hs'; subst l'.
    pose proof (Hrel i i' F) as Eii; subst i'; exact F. }
  apply seg_same; [exact (so_shape _ _ _ HS)|exact (so_shape _ _ _ HS')|exact (so_pure _ _ _ HS)|exact (so_pure _ _ _ HS')|].
  intros x; apply (same_target first first Sg Sg' r HS HS' Hr); rewrite <- EA, <- EA'.
  destruct (named_or_bound x) as [Hx|Hx]; [exact (Hk x Hx)|exact (Hidb x Hx)].
Qed.

Lemma lw_unique_gen : forall n l m first, List.length l < n ->
  lnf first l -> lnf first m -> keq (R l) (R m) ->
  (forall s, bound s -> exists s', bound s' /\ feq (R l s) (R m s')) ->
  (forall s', bound s' -> exists s, bound s /\ feq (R l s) (R m s')) ->
  (first = true -> forall s, bound s -> feq (R l s) (R m s)) ->
  l = m.
Proof.
  induction n as [|n IH]; intros l m first Hlen; [lia|].
  apply step; intros r r' Hlt Hr Hr' K M1 M2.
  apply (IH r r' false); try assumption; [lia|discriminate].
Qed.

(** Layered words in normal form with the same meaning in the free
    model are the same. *)
Theorem lw_unique l m : lnf true l -> lnf true m -> (forall v, feq (R l v) (R m v)) -> l = m.
Proof.
  intros Hl Hm H; apply (lw_unique_gen (S (List.length l)) l m true (Nat.lt_succ_diag_r _) Hl Hm).
  - intros y _; apply H.
  - intros s Hs; exists s; split; [exact Hs|apply H].
  - intros s Hs; exists s; split; [exact Hs|apply H].
  - intros _ s _; apply H.
Qed.

End LUnique.

(** ** From every interpretation to the free model

    As for words ([Unique.adequacy]): layered words that mean the same
    under every interpretation of the atoms have the same free meaning,
    so in normal form they are the same word. *)

Section Adequacy.

Variable lenv : list label.

(** Segments with distinct labels, terms in range. *)
Definition lwok {T : Type} (tenv : list T) (l : lword) : Prop :=
  Forall (fun st => match st with LS s => oks lenv tenv s | LA _ _ => True end) l.

Lemma flw_real {T : Type} (tenv : list T) (aenv : list (radj T)) (penv : list (rpadj T)) l :
  lwok tenv l -> forall K Kr v, (forall y, realises tenv aenv penv (K y) (rapply Kr y)) ->
  realises tenv aenv penv (flw lenv l K v) (rapply (rcompose Kr (lwden lenv tenv aenv penv l)) v).
Proof.
  induction l as [|[s|L a] r IH]; intros Hok K Kr v HK.
  - cbn [flw lwden]; rewrite rcompose_identity_r; apply HK.
  - inversion Hok as [|? ? Hs Hr]; subst; cbn [flw lwden].
    rewrite rcompose_assoc, rapply_compose_cres, rapply_sden by (apply oks_sdist in Hs; exact Hs).
    apply (proj1 (proj2 (proj2 (fw_real lenv tenv aenv penv))) s Hs); intros y; apply IH; assumption.
  - inversion Hok as [|? ? _ Hr]; subst; cbn [flw lwden].
    change (latom lenv L a (flw lenv r K) v) with (fw lenv (WAtom SNil L a (WEnd SNil)) (flw lenv r K) v).
    pose proof (proj2 (proj2 (proj2 (fw_real lenv tenv aenv penv))) (WAtom SNil L a (WEnd SNil)) (conj I I)
                  (flw lenv r K) (rcompose Kr (lwden lenv tenv aenv penv r)) v (fun y => IH Hr K Kr y HK)) as H.
    rewrite wden_atom in H.
    change (sden lenv tenv aenv penv SNil) with (@ridentity T) in H.
    change (wden lenv tenv aenv penv (WEnd SNil)) with (@ridentity T) in H.
    rewrite rcompose_identity_l, rcompose_identity_r, <- rcompose_assoc in H; exact H.
Qed.

Theorem lw_adequacy nt l m : lwok (tenvT nt) l -> lwok (tenvT nt) m ->
  (forall aenv penv, lwden lenv (tenvT nt) aenv penv l = lwden lenv (tenvT nt) aenv penv m) ->
  forall v, feq (flw lenv l FVar v) (flw lenv m FVar v).
Proof.
  intros H1 H2 Heq v; apply fequ_feq; intros B.
  set (f1 := flw lenv l FVar v); set (f2 := flw lenv m FVar v).
  set (Z := stucks B f1 ++ stucks B f2); set (P := pays B f1 ++ pays B f2).
  set (Λ := map (fun p => v_label (snd p)) Z).
  set (N := S (list_max (map (fun p => v_index (snd p)) Z))).
  set (na := S (list_max (map fst Z))); set (np := S (list_max P)).
  set (aenv := aenvT B Λ N na); set (penv := penvT B np).
  assert (HK : forall y, realises (tenvT nt) aenv penv (FVar y) (rapply ridentity y))
    by (intros y; cbn [realises]; apply rapply_identity).
  pose proof (flw_real (tenvT nt) aenv penv l H1 FVar ridentity v HK) as R1.
  pose proof (flw_real (tenvT nt) aenv penv m H2 FVar ridentity v HK) as R2.
  rewrite rcompose_identity_l in R1, R2; rewrite (Heq aenv penv) in R1.
  assert (HZ : boxok Λ N na Z).
  { intros p Hp; split; [|split].
    - apply Nat.lt_succ_r, in_list_max, in_map, Hp.
    - apply (in_map (fun p => v_label (snd p))), Hp.
    - apply Nat.lt_succ_r, in_list_max, (in_map (fun p => v_index (snd p))), Hp. }
  assert (HP : payok np P) by (intros n Hn; apply Nat.lt_succ_r, in_list_max, Hn).
  apply (readback B Λ N na np nt f1 f2 _ R1 R2).
  - intros p Hp; apply HZ, in_or_app; left; exact Hp.
  - intros p Hp; apply HZ, in_or_app; right; exact Hp.
  - intros n Hn; apply HP, in_or_app; left; exact Hn.
  - intros n Hn; apply HP, in_or_app; right; exact Hn.
Qed.

(** Layered words in normal form that mean the same under every
    interpretation of the atoms are the same word. *)
Theorem lw_unique_real (labs : list lexp)
    (Hinj : forall h h', In h labs -> In h' labs -> lden lenv h = lden lenv h' -> h = h')
    (gt : (rvar -> fres) -> (rvar -> fres) -> Prop)
    (gt_irrefl : forall k k', keq k k' -> ~ gt k k')
    (gt_trans : forall k1 k2 k3, gt k1 k2 -> gt k2 k3 -> gt k1 k3)
    (gt_keq : forall k1 k1' k2 k2', keq k1 k1' -> keq k2 k2' -> gt k1 k2 -> gt k1' k2')
    nt l m :
  lnf lenv labs gt true l -> lnf lenv labs gt true m -> lwok (tenvT nt) l -> lwok (tenvT nt) m ->
  (forall aenv penv, lwden lenv (tenvT nt) aenv penv l = lwden lenv (tenvT nt) aenv penv m) ->
  l = m.
Proof.
  intros Hl Hm Ol Om Heq.
  exact (lw_unique lenv labs Hinj gt gt_irrefl gt_trans gt_keq l m Hl Hm (lw_adequacy nt l m Ol Om Heq)).
Qed.

End Adequacy.
