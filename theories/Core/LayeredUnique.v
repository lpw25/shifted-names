(** * Layered words in normal form are unique

    In the free model of [Unique], a layered word is its steps one after
    the other, each with the rest as its continuation; so a term of a
    segment has the rest of the word as what happens to its names.

    The normal-form conditions ([lnf]) are stated on that meaning.  For a
    segment [S] followed by [r]:

    - [S] is a canonical segment.  A term of [S] has the identity
      payload, or a payload atom followed by a renaming of the bound
      variables only.  [S] has a term, or is a renaming that ends the
      word or stands before an atom in lift position ([Unique.lpos]).
    - The rest's payload is above the payload of every term the rest
      sends a variable to, in a strict order [gt] on what a payload does
      to named variables; and a last segment that does nothing to named
      variables has a term.
    - A variable goes on as the least named variable of the rest with
      the same result, and as a bound variable only when there is none;
      the same for the bound variables of a term with a payload atom.
    - Every bound variable of the rest is used, distinct ones have
      distinct results, and they are numbered in the order of the first
      variables sent to them.

    An atom has a canonical list of lifts.

    [lw_unique]: two words satisfying [lnf] with the same meaning are
    the same word.  The order [gt] is a parameter: any relation that is
    irreflexive, transitive and only looks at named variables. *)

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
Local Notation sv := (sv lenv).
Local Notation sren := (sren labs).
Local Notation latom := (latom lenv).
Local Notation lpos := (lpos lenv).
Local Notation lok := (lok lenv labs).
Local Notation lc := (lc lenv).

(** ** The free meaning of a layered word *)

Fixpoint flw (l : lword) (K : rvar -> fres) (v : rvar) : fres :=
  match l with
  | [] => K v
  | LS s :: r => fs s (flw r K) v
  | LA L a :: r => latom L a (flw r K) v
  end.

Definition R (l : lword) : rvar -> fres := flw l FVar.

Definition named (v : rvar) : Prop := v_label v <> None.
Definition bound (v : rvar) : Prop := v_label v = None.

Lemma named_or_bound v : named v \/ bound v.
Proof. unfold named, bound; destruct (v_label v); [left; discriminate|right; reflexivity]. Qed.

Lemma named_big i : named (mk_rvar lbig i).
Proof. discriminate. Qed.

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

(** ** What a segment does to a variable *)

(** A term of a segment: the term, its payload atom, and what is done
    to its bound variables before the rest of the word. *)
Definition tm : Type := (nat * option nat * seg)%type.

Definition tres (t : ntgt) : rvar + tm :=
  match t with
  | NVar h j => inl (mk_rvar (lden h) j)
  | NBind u w b => inr (u, b, match w with WEnd s => s | WAtom _ _ _ _ => SNil end)
  end.

Definition sres (Sg : seg) (v : rvar) : rvar + tm :=
  match sget (v_label v) Sg with
  | Some (ts, m) =>
      if v_index v <? tlen ts then tres (tnth ts (v_index v))
      else inl (mk_rvar (v_label v) (v_index v - tlen ts + m))
  | None => inl v
  end.

(** A renaming that leaves named variables alone. *)
Definition psok (s : seg) : Prop :=
  sshape false s /\ sren s /\ forall v, named v -> sv s v = v.

(** The targets of a layered segment. *)
Definition tpure (t : ntgt) : Prop :=
  match t with
  | NVar h _ => In h labs
  | NBind _ w b => exists s, w = WEnd s /\ match b with None => s = SNil | Some _ => psok s end
  end.

Definition spure (Sg : seg) : Prop := Forall tpure (stgts Sg).

Definition res (Sg : seg) (K : rvar -> fres) (x : rvar) : fres :=
  match sres Sg x with
  | inl y => K y
  | inr (u, b, s) => FTerm u b (fun z => fs s K z)
  end.

Lemma sres_pure Sg v : spure Sg ->
  match sres Sg v with
  | inl _ => True
  | inr (_, b, s) => match b with None => s = SNil | Some _ => psok s end
  end.
Proof.
  intros HS; unfold sres; destruct (sget (v_label v) Sg) as [[ts m]|] eqn:E; [|exact I].
  destruct (Nat.ltb_spec (v_index v) (tlen ts)) as [Hlt|Hge]; [|exact I].
  assert (Hp : tpure (tnth ts (v_index v))).
  { unfold spure in HS; rewrite Forall_forall in HS; apply HS, (sget_tgts lenv _ _ _ _ E), tnth_in, Hlt. }
  destruct (tnth ts (v_index v)) as [h j|u w b]; [exact I|].
  destruct Hp as [s [-> Hs]]; exact Hs.
Qed.

Lemma fs_pure Sg K v : spure Sg -> fs Sg K v = res Sg K v.
Proof.
  intros HS; unfold res, sres; rewrite (fs_get lenv); unfold Unique.fget.
  destruct (sget (v_label v) Sg) as [[ts m]|] eqn:E; [|destruct v; reflexivity].
  destruct (Nat.ltb_spec (v_index v) (tlen ts)) as [Hlt|Hge].
  - rewrite (ftl_lt lenv) by exact Hlt.
    assert (Hp : tpure (tnth ts (v_index v))).
    { unfold spure in HS; rewrite Forall_forall in HS; apply HS, (sget_tgts lenv _ _ _ _ E), tnth_in, Hlt. }
    destruct (tnth ts (v_index v)) as [h j|u w b]; [reflexivity|].
    destruct Hp as [s [-> _]]; reflexivity.
  - rewrite (ftl_ge lenv) by exact Hge; reflexivity.
Qed.

Lemma sres_ren Sg v : sren Sg -> sres Sg v = inl (sv Sg v).
Proof.
  intros Hr; unfold sres, Unique.sv.
  destruct (sget (v_label v) Sg) as [[ts m]|] eqn:E; [|reflexivity].
  destruct (Nat.ltb_spec (v_index v) (tlen ts)) as [Hlt|Hge]; [|reflexivity].
  pose proof (proj1 (Forall_forall _ _) Hr _ (sget_tgts lenv _ _ _ _ E _ (tnth_in _ _ Hlt))) as Ht.
  destruct (tnth ts (v_index v)) as [h j|]; [reflexivity|destruct Ht].
Qed.

(** A segment has a term. *)
Definition sterm (Sg : seg) : Prop := exists v t, sres Sg v = inr t.

Lemma sren_noterm Sg : sren Sg -> ~ sterm Sg.
Proof. intros Hr [v [t E]]; rewrite (sres_ren _ _ Hr) in E; discriminate E. Qed.

(** What a term with [s] before the rest [K] does to named variables is
    what [K] does. *)
Lemma pay_keq (b : option nat) s K : match b with None => s = SNil | Some _ => psok s end -> keq (fun z => fs s K z) K.
Proof.
  intros Hs y Hy; destruct b as [n|]; [|subst s; apply feq_refl].
  destruct Hs as [_ [Hr Hn]]; rewrite (fs_ren lenv labs) by exact Hr; rewrite (Hn y Hy); apply feq_refl.
Qed.

(** ** The normal-form conditions *)

(** The order on payloads. *)
Variable gt : (rvar -> fres) -> (rvar -> fres) -> Prop.
Hypothesis gt_irrefl : forall k k', keq k k' -> ~ gt k k'.
Hypothesis gt_trans : forall k1 k2 k3, gt k1 k2 -> gt k2 k3 -> gt k1 k3.
Hypothesis gt_keq : forall k1 k1' k2 k2', keq k1 k1' -> keq k2 k2' -> gt k1 k2 -> gt k1' k2'.

(** Where a variable goes on to, among the variables of [k]: the least
    named variable with its result, a bound one only when there is none. *)
Definition routed (k : rvar -> fres) (y : rvar) : Prop :=
  (named y -> forall y', named y' -> feq (k y') (k y) -> ~ vlt y' y)
  /\ (bound y -> forall y', named y' -> ~ feq (k y') (k y)).

(** The rule for routes is a parameter: [route k x y] says the input [x]
    may go on as [y] of [k].  Uniqueness needs only that two routes of the
    same input with the same result, one of them named, agree. *)
Variable route : (rvar -> fres) -> rvar -> rvar -> Prop.
Hypothesis route_uniq : forall k k' x y y', keq k k' -> route k x y -> route k' x y' ->
  feq (k y) (k' y') -> named y -> y = y'.

Record segok (Sg : seg) (r : lword) : Prop := {
  so_shape : sshape false Sg;
  so_pure : spure Sg;
  so_order : forall y u b k, R r y = FTerm u b k -> gt (R r) k;
  so_last : forall G, r = [LS G] -> keq (R r) FVar -> sterm G;
  so_route : forall x y, sres Sg x = inl y -> route (R r) x y;
  so_pay : forall x u n s i, sres Sg x = inr (u, Some n, s) -> routed (R r) (sv s (mk_rvar None i));
  so_hit : r <> [] -> forall y, bound y -> exists x, sres Sg x = inl y;
  so_binj : binj (R r);
  so_src : r <> [] -> forall x x' i j,
             sres Sg x = inl (mk_rvar None i) -> sres Sg x' = inl (mk_rvar None j) -> i < j ->
             exists x0, sres Sg x0 = inl (mk_rvar None i)
                        /\ forall x'', sres Sg x'' = inl (mk_rvar None j) -> vlt x0 x''
}.

Fixpoint lnf (l : lword) : Prop :=
  match l with
  | [] => True
  | LS Sg :: r =>
      Sg <> SNil /\ lnf r
      /\ ((sterm Sg /\ segok Sg r)
          \/ (sshape false Sg /\ sren Sg /\ (r = [] \/ exists L a r2, r = LA L a :: r2 /\ lpos Sg L)))
  | LA L _ :: r => lok L /\ lnf r
  end.

Lemma lnf_cons_pure s r : lnf (LS s :: r) -> spure s /\ lnf r.
Proof.
  intros [_ [Hr [[_ HS]|[_ [Hren _]]]]]; split; try exact Hr; [exact (so_pure _ _ HS)|].
  unfold spure; eapply Forall_impl; [|exact Hren]; intros [h j|u w b]; cbn; tauto.
Qed.

Fixpoint natl (l : lword) : nat :=
  match l with [] => 0 | LS _ :: r => natl r | LA _ _ :: r => S (natl r) end.

Lemma R_cons Sg r : spure Sg -> forall x, R (LS Sg :: r) x = res Sg (R r) x.
Proof. intros HS x; unfold R; cbn [flw]; apply fs_pure, HS. Qed.

(** ** A substitution step

    The segment [⟦ h := u ⟧] in front of a word whose rest sends distinct
    variables to distinct results satisfies the conditions, given the
    two on the order. *)

Definition entry_seg (h : lexp) (u : nat) : seg := SEnt h (TCons (NBind u (WEnd SNil) None) TNil) 0 SNil.

Lemma sres_entry h u x v : lden h = Some x ->
  sres (entry_seg h u) v
  = if label_eqb (Some x) (v_label v)
    then match v_index v with 0 => inr (u, None, SNil) | S i => inl (mk_rvar (v_label v) i) end
    else inl v.
Proof.
  intros Hx; unfold sres, entry_seg; cbn [Normalise.sget]; rewrite Hx.
  destruct (label_eqb (Some x) (v_label v)); [|reflexivity].
  cbn [tlen tnth]; destruct (v_index v) as [|i]; cbn; [reflexivity|].
  do 2 f_equal; lia.
Qed.

Lemma sterm_entry h x u : lden h = Some x -> sterm (entry_seg h u).
Proof.
  intros Hx; exists (mk_rvar (Some x) 0), (u, None, SNil); rewrite (sres_entry h u x _ Hx).
  cbn [v_label v_index]; rewrite label_eqb_refl; reflexivity.
Qed.

Lemma segok_entry h x u r :
  lden h = Some x -> In h labs ->
  (forall y u' b k, R r y = FTerm u' b k -> gt (R r) k) ->
  (forall G, r = [LS G] -> keq (R r) FVar -> sterm G) ->
  (forall v y, route (R r) v y) ->
  binj (R r) ->
  segok (entry_seg h u) r.
Proof.
  intros Hx Hin Ho Hl Hi Hb; constructor.
  - split; [repeat constructor|]; constructor; [|constructor].
    split; [exact Hin|split; [exact I|split; [left; discriminate|discriminate]]].
  - constructor; [exists SNil; split; reflexivity|constructor].
  - exact Ho.
  - exact Hl.
  - intros v y _; exact (Hi v y).
  - intros v u' n s i E; rewrite (sres_entry h u x _ Hx) in E.
    destruct (label_eqb (Some x) (v_label v)); [destruct (v_index v); discriminate E|discriminate E].
  - intros _ y Hy; exists y; rewrite (sres_entry h u x _ Hx); unfold bound in Hy; rewrite Hy; reflexivity.
  - exact Hb.
  - intros _ v v' i j _ _ Hij; exists (mk_rvar None i); split; [rewrite (sres_entry h u x _ Hx); reflexivity|].
    intros v'' E; rewrite (sres_entry h u x _ Hx) in E.
    destruct (label_eqb_spec (Some x) (v_label v'')) as [El|_].
    + destruct (v_index v''); [discriminate E|]; injection E as E _; rewrite E in El; discriminate El.
    + injection E as ->; right; split; [reflexivity|exact Hij].
Qed.

(** ** Two words that begin with a segment with a term *)

(** A term with the continuation [K], against what a word does to a
    variable: its own term, or a term further on. *)
Lemma term_match Sg r u b K x :
  segok Sg r -> feq (FTerm u b K) (res Sg (R r) x) ->
  (exists s, sres Sg x = inr (u, b, s) /\ keq K (R r))
  \/ (exists y k, sres Sg x = inl y /\ keq K k /\ gt (R r) k).
Proof.
  intros HS; unfold res; pose proof (sres_pure Sg x (so_pure _ _ HS)) as Hp.
  destruct (sres Sg x) as [y|[[u' b'] s]] eqn:E.
  - destruct (R r y) as [v|u2 b2 k2|a z k2] eqn:Ey; cbn [feq]; try (intros []; fail).
    intros [<- [<- Hk]]; right; exists y, k2; split; [reflexivity|split].
    + intros z Hz; apply Hk; intros _; exact Hz.
    + exact (so_order _ _ HS y u b k2 Ey).
  - cbn [feq]; intros [<- [<- Hk]]; left; exists s; split; [reflexivity|].
    apply (keq_trans _ (fun z => fs s (R r) z)); [intros z Hz; apply Hk; intros _; exact Hz|].
    exact (pay_keq b s (R r) Hp).
Qed.

(** The rests of two such words agree on named variables. *)
Lemma first_layer Sg r Sg' r' :
  segok Sg r -> segok Sg' r' ->
  (forall x, feq (res Sg (R r) x) (res Sg' (R r') x)) ->
  sterm Sg -> sterm Sg' -> keq (R r) (R r').
Proof.
  intros HS HS' E [x0 [[[u b] s] E0]] [x1 [[[u1 b1] s1] E1]].
  pose proof (sres_pure Sg x0 (so_pure _ _ HS)) as Hp0; rewrite E0 in Hp0.
  pose proof (sres_pure Sg' x1 (so_pure _ _ HS')) as Hp1; rewrite E1 in Hp1.
  pose proof (E x0) as F; unfold res at 1 in F; rewrite E0 in F.
  destruct (term_match _ _ _ _ _ _ HS' F) as [[s' [_ K1]]|[y' [k' [_ [K1 G1]]]]].
  { exact (keq_trans _ _ _ (keq_sym _ _ (pay_keq b s (R r) Hp0)) K1). }
  pose proof (E x1) as F1; unfold res at 2 in F1; rewrite E1 in F1; apply feq_sym in F1.
  destruct (term_match _ _ _ _ _ _ HS F1) as [[s'' [_ K2]]|[y [k [_ [K2 G2]]]]].
  { exact (keq_sym _ _ (keq_trans _ _ _ (keq_sym _ _ (pay_keq b1 s1 (R r') Hp1)) K2)). }
  exfalso.
  assert (Ka : keq k' (R r)) by exact (keq_trans _ _ _ (keq_sym _ _ K1) (pay_keq b s (R r) Hp0)).
  assert (Kb : keq k (R r')) by exact (keq_trans _ _ _ (keq_sym _ _ K2) (pay_keq b1 s1 (R r') Hp1)).
  exact (gt_irrefl _ _ (keq_refl _)
           (gt_trans _ _ _ (gt_keq _ _ _ _ (keq_refl _) Kb G2) (gt_keq _ _ _ _ (keq_refl _) Ka G1))).
Qed.

(** A word that ends after its first segment against one that goes on
    without doing anything to named variables. *)
Lemma no_trivial_tail Sg Sg' r' :
  spure Sg -> segok Sg' r' -> lnf r' -> r' <> [] -> keq (R r') FVar ->
  (forall x, feq (res Sg FVar x) (res Sg' (R r') x)) -> False.
Proof.
  intros HpS HS' Hr' Hne Hk E.
  destruct r' as [|[Sg2|L a] r3]; [destruct (Hne eq_refl)| |].
  - destruct Hr' as [_ [_ [[[y2 [[[c b2] s2] E2]] HS2]|[_ [Hr2 [->|[L [a [r4 [-> _]]]]]]]]]].
    + assert (Ey : R (LS Sg2 :: r3) y2 = FTerm c b2 (fun z => fs s2 (R r3) z)).
      { rewrite (R_cons _ _ (so_pure _ _ HS2)); unfold res; rewrite E2; reflexivity. }
      destruct (named_or_bound y2) as [Hn|Hb].
      * pose proof (Hk y2 Hn) as F; rewrite Ey in F; exact F.
      * destruct (so_hit _ _ HS' Hne y2 Hb) as [x Ex].
        pose proof (E x) as F; unfold res at 2 in F; rewrite Ex, Ey in F.
        unfold res in F; pose proof (sres_pure Sg x HpS) as Hp.
        destruct (sres Sg x) as [y|[[u b] s]]; cbn [feq] in F; [destruct F|].
        destruct F as [_ [_ F]].
        assert (K2 : keq FVar (fun z => fs s2 (R r3) z)).
        { apply (keq_trans _ (fun z => fs s FVar z)); [exact (keq_sym _ _ (pay_keq b s FVar Hp))|].
          intros z Hz; apply F; intros _; exact Hz. }
        pose proof (so_order _ _ HS' y2 c b2 _ Ey) as G.
        exact (gt_irrefl _ _ (keq_refl _) (gt_keq _ _ _ _ Hk (keq_sym _ _ K2) G)).
    + exact (sren_noterm _ Hr2 (so_last _ _ HS' Sg2 eq_refl Hk)).
    + destruct (sv_big lenv labs Sg2 lbig (lc lbig L) Hr2) as [B HB].
      destruct (HB B (le_n _)) as [j [Hj Ej]].
      pose proof (Hk (mk_rvar lbig B) (named_big B)) as F.
      unfold R in F; cbn [flw] in F; rewrite (fs_ren lenv labs) in F by exact Hr2; rewrite Ej in F.
      unfold Unique.latom in F; cbn [v_label v_index] in F.
      rewrite (proj2 (Nat.ltb_ge _ _) Hj) in F; exact F.
  - pose proof (Hk (mk_rvar lbig (lc lbig L)) (named_big _)) as F.
    unfold R in F; cbn [flw] in F; unfold Unique.latom in F; cbn [v_label v_index] in F.
    rewrite Nat.ltb_irrefl in F; exact F.
Qed.

(** A variable that goes on as a variable in one word does so in the
    other, with the same result. *)
Lemma var_var Sg r Sg' r' :
  segok Sg r -> segok Sg' r' -> keq (R r) (R r') ->
  (forall x, feq (res Sg (R r) x) (res Sg' (R r') x)) ->
  forall x y, sres Sg x = inl y -> exists y', sres Sg' x = inl y' /\ feq (R r y) (R r' y').
Proof.
  intros HS HS' K E x y Ex; pose proof (E x) as F; unfold res in F; rewrite Ex in F.
  pose proof (sres_pure Sg' x (so_pure _ _ HS')) as Hp.
  destruct (sres Sg' x) as [y'|[[u b] s]]; [exists y'; split; [reflexivity|exact F]|exfalso].
  destruct (R r y) as [v|u2 b2 k|a z k] eqn:Ey; cbn [feq] in F; try (destruct F; fail).
  destruct F as [_ [_ F]].
  assert (K1 : keq k (R r)).
  { apply (keq_trans _ (fun z => fs s (R r') z)); [intros z Hz; apply F; intros _; exact Hz|].
    exact (keq_trans _ _ _ (pay_keq b s (R r') Hp) (keq_sym _ _ K)). }
  exact (gt_irrefl _ _ (keq_sym _ _ K1) (so_order _ _ HS y u2 b2 k Ey)).
Qed.

Lemma var_named Sg r Sg' r' :
  segok Sg r -> segok Sg' r' -> keq (R r) (R r') ->
  (forall x, feq (res Sg (R r) x) (res Sg' (R r') x)) ->
  forall x y, sres Sg x = inl y -> named y -> sres Sg' x = inl y.
Proof.
  intros HS HS' K E x y Ex Hy; destruct (var_var _ _ _ _ HS HS' K E x y Ex) as [y' [Ex' F]].
  rewrite Ex'; f_equal.
  symmetry; exact (route_uniq _ _ x y y' K (so_route _ _ HS x y Ex) (so_route _ _ HS' x y' Ex') F Hy).
Qed.

Lemma var_bound Sg r Sg' r' :
  segok Sg r -> segok Sg' r' -> keq (R r) (R r') ->
  (forall x, feq (res Sg (R r) x) (res Sg' (R r') x)) ->
  forall x y, sres Sg x = inl y -> bound y ->
  exists y', sres Sg' x = inl y' /\ bound y' /\ feq (R r y) (R r' y').
Proof.
  intros HS HS' K E x y Ex Hy; destruct (var_var _ _ _ _ HS HS' K E x y Ex) as [y' [Ex' F]].
  exists y'; split; [exact Ex'|split; [|exact F]].
  destruct (named_or_bound y') as [Hn|Hb]; [exfalso|exact Hb].
  assert (E' : forall x, feq (res Sg' (R r') x) (res Sg (R r) x)) by (intros x0; apply feq_sym, E).
  pose proof (var_named _ _ _ _ HS' HS (keq_sym _ _ K) E' x y' Ex' Hn) as Ex2.
  rewrite Ex in Ex2; injection Ex2 as ->; exact (Hn Hy).
Qed.

(** Two numberings of the same classes of variables, both in the order
    of the classes' first variables and both using every number, are the
    same. *)
Lemma class_index (f f' : rvar -> nat -> Prop) :
  (forall x i j, f' x i -> f' x j -> i = j) ->
  (forall x i, f x i -> exists i', f' x i') -> (forall x i', f' x i' -> exists i, f x i) ->
  (forall x x0 i i' j', f x i -> f x0 i -> f' x i' -> f' x0 j' -> i' = j') ->
  (forall x x0 i' i j, f' x i' -> f' x0 i' -> f x i -> f x0 j -> i = j) ->
  (forall i, exists x, f x i) -> (forall i, exists x, f' x i) ->
  (forall x x' i j, f x i -> f x' j -> i < j -> exists x0, f x0 i /\ forall x'', f x'' j -> vlt x0 x'') ->
  (forall x x' i j, f' x i -> f' x' j -> i < j -> exists x0, f' x0 i /\ forall x'', f' x'' j -> vlt x0 x'') ->
  forall n x, f x n -> f' x n.
Proof.
  intros Hfun Ha Ha' Hb Hb' Hs Hs' Hsrc Hsrc' n.
  induction n as [n IH] using lt_wf_ind; intros x Hx.
  destruct (Ha x n Hx) as [n' Hx'].
  destruct (Nat.lt_trichotomy n' n) as [Hlt|[->|Hgt]]; [exfalso|exact Hx'|exfalso].
  - destruct (Hs n') as [x1 H1]; pose proof (IH n' Hlt x1 H1) as H1'.
    pose proof (Hb' x x1 n' n n' Hx' H1' Hx H1); lia.
  - destruct (Hs' n) as [x2 H2']; destruct (Ha' x2 n H2') as [k H2].
    destruct (Nat.lt_trichotomy k n) as [Hk|[->|Hk]].
    + pose proof (Hfun x2 _ _ H2' (IH k Hk x2 H2)); lia.
    + pose proof (Hb x x2 n n' n Hx H2 Hx' H2'); lia.
    + destruct (Hsrc x x2 n k Hx H2 Hk) as [x0 [H0 Hall]].
      destruct (Hsrc' x2 x n n' H2' Hx' Hgt) as [x0' [H0' Hall']].
      destruct (Ha x0 n H0) as [q Hq]; pose proof (Hb x x0 n n' q Hx H0 Hx' Hq) as <-.
      destruct (Ha' x0' n H0') as [p Hp]; pose proof (Hb' x2 x0' n k p H2' H0' H2 Hp) as <-.
      exact (vlt_asym _ _ (Hall x0' Hp) (Hall' x0 Hq)).
Qed.

(** The renaming of a term's bound variables is determined. *)
Lemma pay_unique s s' k : psok s -> psok s' -> binj k ->
  (forall i, routed k (sv s (mk_rvar None i))) -> (forall i, routed k (sv s' (mk_rvar None i))) ->
  (forall z, feq (fs s k z) (fs s' k z)) -> s = s'.
Proof.
  intros [Hs [Hr Hn]] [Hs' [Hr' Hn']] Hb Ho Ho' E.
  apply (ren_unique lenv labs Hinj false s s' Hs Hs' Hr Hr'); intros v _.
  destruct (named_or_bound v) as [Hv|Hv]; [rewrite Hn, Hn' by exact Hv; reflexivity|].
  destruct v as [l i]; unfold bound in Hv; cbn in Hv; subst l.
  pose proof (E (mk_rvar None i)) as F; rewrite !(fs_ren lenv labs) in F by assumption.
  destruct (Ho i) as [A1 A2]; destruct (Ho' i) as [B1 B2].
  destruct (named_or_bound (sv s (mk_rvar None i))) as [Hy|Hy],
           (named_or_bound (sv s' (mk_rvar None i))) as [Hy'|Hy'].
  - destruct (vlt_total (sv s (mk_rvar None i)) (sv s' (mk_rvar None i))) as [H|[H|H]]; [|exact H|].
    + destruct (B1 Hy' _ Hy F H).
    + destruct (A1 Hy _ Hy' (feq_sym _ _ F) H).
  - destruct (B2 Hy' _ Hy F).
  - destruct (A2 Hy _ Hy' (feq_sym _ _ F)).
  - exact (Hb _ _ Hy Hy' F).
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
    + intros [s [-> Hsp]] [s' [-> Hsp']] [<- [<- Hk]]; f_equal; f_equal.
      destruct b as [n|]; [|rewrite Hsp, Hsp'; reflexivity].
      destruct Hsp as [A [B _]]; destruct Hsp' as [A' [B' _]].
      apply (ren_unique lenv labs Hinj false s s' A A' B B'); intros v _.
      pose proof (Hk v ltac:(discriminate)) as F; cbn [Unique.fw] in F.
      rewrite !(fs_ren lenv labs) in F by assumption; exact F.
  - intros h j Hh; exact Hh.
  - intros h j Hh; exact Hh.
  - intros l j; rewrite <- !(fs_get lenv _ FVar (mk_rvar l j)), !fs_pure by assumption.
    unfold res; rewrite H; apply feq_refl.
Qed.

(** Variables go on as the same variables. *)
Lemma var_same Sg r Sg' r' :
  segok Sg r -> segok Sg' r' -> keq (R r) (R r') ->
  (forall x, feq (res Sg (R r) x) (res Sg' (R r') x)) ->
  (r = [] -> r' = []) -> (r' = [] -> r = []) ->
  forall x y, sres Sg x = inl y -> sres Sg' x = inl y.
Proof.
  intros HS HS' K E Hnn Hnn' x y Ex.
  assert (E' : forall x, feq (res Sg' (R r') x) (res Sg (R r) x)) by (intros x0; apply feq_sym, E).
  destruct (named_or_bound y) as [Hy|Hy]; [exact (var_named _ _ _ _ HS HS' K E x y Ex Hy)|].
  destruct (var_bound _ _ _ _ HS HS' K E x y Ex Hy) as [y' [Ex' [Hy' F]]].
  destruct r as [|st r0] eqn:Dr.
  - rewrite (Hnn eq_refl) in F; cbn in F; rewrite Ex', F; reflexivity.
  - rewrite <- Dr in *.
    assert (Hne : r <> []) by (rewrite Dr; discriminate).
    assert (Hne' : r' <> []) by (intros H; exact (Hne (Hnn' H))).
    destruct y as [ly i], y' as [ly' i']; unfold bound in Hy, Hy'; cbn in Hy, Hy'; subst ly ly'.
    enough (H : sres Sg' x = inl (mk_rvar None i)) by exact H.
    apply (class_index (fun x i => sres Sg x = inl (mk_rvar None i)) (fun x i => sres Sg' x = inl (mk_rvar None i))).
    + intros x0 a b Ha Hb; rewrite Ha in Hb; injection Hb as Hb; exact Hb.
    + intros x0 a Ha; destruct (var_bound _ _ _ _ HS HS' K E x0 _ Ha eq_refl) as [[l a'] [Ha' [Hl _]]].
      unfold bound in Hl; cbn in Hl; subst l; exists a'; exact Ha'.
    + intros x0 a Ha; destruct (var_bound _ _ _ _ HS' HS (keq_sym _ _ K) E' x0 _ Ha eq_refl) as [[l a'] [Ha' [Hl _]]].
      unfold bound in Hl; cbn in Hl; subst l; exists a'; exact Ha'.
    + intros x1 x0 a a' b' H1 H0 H1' H0'.
      pose proof (E x1) as F1; unfold res in F1; rewrite H1, H1' in F1.
      pose proof (E x0) as F0; unfold res in F0; rewrite H0, H0' in F0.
      pose proof (so_binj _ _ HS' (mk_rvar None a') (mk_rvar None b') eq_refl eq_refl
                    (feq_trans _ _ _ (feq_sym _ _ F1) F0)) as Eq.
      injection Eq as Eq; exact Eq.
    + intros x1 x0 a' a b H1' H0' H1 H0.
      pose proof (E x1) as F1; unfold res in F1; rewrite H1, H1' in F1.
      pose proof (E x0) as F0; unfold res in F0; rewrite H0, H0' in F0.
      pose proof (so_binj _ _ HS (mk_rvar None a) (mk_rvar None b) eq_refl eq_refl
                    (feq_trans _ _ _ F1 (feq_sym _ _ F0))) as Eq.
      injection Eq as Eq; exact Eq.
    + intros a; exact (so_hit _ _ HS Hne (mk_rvar None a) eq_refl).
    + intros a; exact (so_hit _ _ HS' Hne' (mk_rvar None a) eq_refl).
    + exact (so_src _ _ HS Hne).
    + exact (so_src _ _ HS' Hne').
    + exact Ex.
Qed.

Lemma step_terms Sg r Sg' r' :
  (lnf r -> lnf r' -> (forall v, feq (R r v) (R r' v)) -> r = r') ->
  segok Sg r -> lnf r -> segok Sg' r' -> lnf r' -> sterm Sg -> sterm Sg' ->
  (forall x, feq (res Sg (R r) x) (res Sg' (R r') x)) -> Sg = Sg' /\ r = r'.
Proof.
  intros IH HS Hr HS' Hr' Ht Ht' E.
  assert (E' : forall x, feq (res Sg' (R r') x) (res Sg (R r) x)) by (intros x0; apply feq_sym, E).
  pose proof (first_layer _ _ _ _ HS HS' E Ht Ht') as K.
  assert (Hnn : r = [] -> r' = []).
  { intros ->; destruct r' as [|st r0'] eqn:Dr'; [reflexivity|exfalso; rewrite <- Dr' in *].
    refine (no_trivial_tail Sg Sg' r' (so_pure _ _ HS) HS' Hr' _ (keq_sym _ _ K) E); rewrite Dr'; discriminate. }
  assert (Hnn' : r' = [] -> r = []).
  { intros ->; destruct r as [|st r0] eqn:Dr; [reflexivity|exfalso; rewrite <- Dr in *].
    refine (no_trivial_tail Sg' Sg r (so_pure _ _ HS') HS Hr _ K E'); rewrite Dr; discriminate. }
  pose proof (var_same _ _ _ _ HS HS' K E Hnn Hnn') as Hv.
  pose proof (var_same _ _ _ _ HS' HS (keq_sym _ _ K) E' Hnn' Hnn) as Hv'.
  assert (Er : r = r').
  { apply (IH Hr Hr'); intros y; destruct (named_or_bound y) as [Hy|Hy]; [exact (K y Hy)|].
    destruct r as [|st r0] eqn:Dr; [rewrite (Hnn eq_refl); apply feq_refl|rewrite <- Dr in *].
    assert (Hne : r <> []) by (rewrite Dr; discriminate).
    destruct (so_hit _ _ HS Hne y Hy) as [x Ex].
    pose proof (E x) as F; unfold res in F; rewrite Ex, (Hv x y Ex) in F; exact F. }
  subst r'; split; [|reflexivity].
  apply seg_same; [exact (so_shape _ _ HS)|exact (so_shape _ _ HS')|exact (so_pure _ _ HS)|exact (so_pure _ _ HS')|].
  intros x; destruct (sres Sg x) as [y|[[u b] s]] eqn:Ex; [symmetry; exact (Hv x y Ex)|].
  destruct (sres Sg' x) as [y'|[[u' b'] s']] eqn:Ex'; [rewrite (Hv' x y' Ex') in Ex; discriminate Ex|].
  pose proof (sres_pure Sg x (so_pure _ _ HS)) as Hp; rewrite Ex in Hp.
  pose proof (sres_pure Sg' x (so_pure _ _ HS')) as Hp'; rewrite Ex' in Hp'.
  pose proof (E x) as F; unfold res in F; rewrite Ex, Ex' in F; cbn [feq] in F.
  destruct F as [<- [<- Hk]]; do 2 f_equal.
  destruct b as [n|]; [|rewrite Hp, Hp'; reflexivity].
  apply (pay_unique s s' (R r) Hp Hp' (so_binj _ _ HS)).
  - intros i; exact (so_pay _ _ HS x u n s i Ex).
  - intros i; exact (so_pay _ _ HS' x u n s' i Ex').
  - intros z; apply Hk; discriminate.
Qed.

(** ** Atoms

    As for words ([Unique.peel]): far along a named label every variable
    goes through each atom in turn, which counts the atoms that are
    left; a result stuck at the first atom of a word is told from one
    stuck further on by that count. *)

Lemma deep_flw l : forall d K, deep d K -> deep (natl l + d) (fun v => flw l K v).
Proof.
  induction l as [|[s|L a] r IH]; intros d K Hd; cbn [natl flw].
  - exact Hd.
  - exact (deep_fs lenv _ s _ (IH d K Hd)).
  - exact (deep_latom lenv _ L a _ (IH d K Hd)).
Qed.

Lemma nstuck_flw l : forall e K, nstuck e K -> deep e K -> nstuck (natl l + e) (fun v => flw l K v).
Proof.
  induction l as [|[s|L a] r IH]; intros e K Hn Hd; cbn [natl flw].
  - exact Hn.
  - exact (nstuck_fs lenv _ s _ (IH e K Hn Hd)).
  - exact (nstuck_latom lenv _ L a _ (IH e K Hn Hd) (deep_flw r e K Hd)).
Qed.

Lemma deep_R l : deep (natl l) (R l).
Proof. rewrite <- (Nat.add_0_r (natl l)); exact (deep_flw l 0 FVar deep_FVar). Qed.

Lemma nstuck_R l : nstuck (natl l) (R l).
Proof. rewrite <- (Nat.add_0_r (natl l)); exact (nstuck_flw l 0 FVar nstuck_FVar deep_FVar). Qed.

(** A term a word sends a variable to has at most the word's atoms
    after it. *)
Lemma tdeep l : lnf l -> forall y u b k, R l y = FTerm u b k -> exists e, e <= natl l /\ deep e k.
Proof.
  induction l as [|[s|L a] r IH]; intros Hl y u b k E; [discriminate E| |].
  - destruct (lnf_cons_pure _ _ Hl) as [Hp Hr]; rewrite (R_cons _ _ Hp) in E; unfold res in E.
    destruct (sres s y) as [y2|[[u' b'] s']]; [exact (IH Hr y2 u b k E)|].
    injection E as <- <- <-; exists (natl r); split; [apply le_n|exact (deep_fs lenv _ s' _ (deep_R r))].
  - destruct Hl as [_ Hr]; unfold R in E; cbn [flw] in E; unfold Unique.latom in E.
    destruct (v_index y <? lc (v_label y) L); [|discriminate E].
    destruct (IH Hr _ _ _ _ E) as [e [He Hd]]; exists e; split; [cbn [natl]; lia|exact Hd].
Qed.

(** The first atom, its lifts and the renaming before it are
    determined, and so is what the rest of the word does. *)
Lemma peel U1 L1 a1 R1 n1 U2 L2 a2 R2 n2 :
  sshape false U1 -> sren U1 -> lok L1 -> lpos U1 L1 ->
  sshape false U2 -> sren U2 -> lok L2 -> lpos U2 L2 ->
  deep n1 R1 -> nstuck n1 R1 -> deep n2 R2 -> nstuck n2 R2 ->
  (forall v, feq (latom L1 a1 R1 (sv U1 v)) (latom L2 a2 R2 (sv U2 v))) ->
  U1 = U2 /\ L1 = L2 /\ a1 = a2 /\ forall y, feq (R1 y) (R2 y).
Proof.
  intros Hs1 Hr1 Hl1 Hp1 Hs2 Hr2 Hl2 Hp2 Hd1' Hst1 Hd2' Hst2 H.
  destruct (sv_big lenv labs U1 lbig (lc lbig L1) Hr1) as [B1 HB1].
  destruct (sv_big lenv labs U2 lbig (lc lbig L2) Hr2) as [B2 HB2].
  destruct (HB1 (B1 + B2) ltac:(lia)) as [j1 [Hj1 E1]]; destruct (HB2 (B1 + B2) ltac:(lia)) as [j2 [Hj2 E2]].
  pose proof (H (mk_rvar lbig (B1 + B2))) as Hb; rewrite E1, E2 in Hb; unfold Unique.latom in Hb; cbn [v_label v_index] in Hb.
  rewrite (proj2 (Nat.ltb_ge _ _) Hj1), (proj2 (Nat.ltb_ge _ _) Hj2) in Hb; cbn [feq] in Hb.
  destruct Hb as [<- [_ Hk]].
  assert (Hd1 : deep n1 (fun y => R1 (shiftL lenv L1 y))) by exact (deep_shift lenv _ L1 _ Hd1').
  assert (Hd2 : deep n2 (fun y => R2 (shiftL lenv L2 y))) by exact (deep_shift lenv _ L2 _ Hd2').
  assert (En : n1 = n2) by (apply (deep_unique _ _ _ _ Hd1 Hd2); intros i; apply Hk).
  assert (HB : forall v,
    (inVb lenv L1 (sv U1 v) = true /\ inVb lenv L2 (sv U2 v) = true /\ feq (R1 (sv U1 v)) (R2 (sv U2 v)))
    \/ (inVb lenv L1 (sv U1 v) = false /\ inVb lenv L2 (sv U2 v) = false
        /\ unsh lenv L1 (sv U1 v) = unsh lenv L2 (sv U2 v))).
  { intros v; pose proof (H v) as E; unfold Unique.latom in E; unfold inVb.
    destruct (v_index (sv U1 v) <? _) eqn:Ei1, (v_index (sv U2 v) <? _) eqn:Ei2.
    - left; auto.
    - exfalso; destruct (R1 (sv U1 v)) as [| |a z k] eqn:ER; cbn [feq] in E; try contradiction.
      destruct E as [_ [_ Ek]]; destruct (Hst1 _ _ _ _ ER) as [d [Hd Hdk]].
      assert (d = n2) by (apply (deep_unique _ _ _ _ Hdk Hd2); intros i; apply Ek); lia.
    - exfalso; destruct (R2 (sv U2 v)) as [| |a z k] eqn:ER; cbn [feq] in E; try contradiction.
      destruct E as [_ [_ Ek]]; destruct (Hst2 _ _ _ _ ER) as [d [Hd Hdk]].
      assert (n1 = d) by (apply (deep_unique _ _ _ _ Hd1 Hdk); intros i; apply Ek); lia.
    - right; cbn [feq] in E; destruct E as [_ [Ez _]]; auto. }
  assert (Hcnt : forall g i, cntV lenv U1 L1 g i = cntV lenv U2 L2 g i).
  { intros g i; induction i as [|i IHi]; [reflexivity|]; cbn [cntV]; rewrite IHi.
    destruct (HB (mk_rvar g i)) as [[-> [-> _]]|[-> [-> _]]]; reflexivity. }
  assert (Hle : forall l j, j < lc l L1 -> j < lc l L2).
  { intros l j Hj; destruct (proj2 Hp1 l j Hj) as [i Ei].
    destruct (HB (mk_rvar l i)) as [[E1' [E2' _]]|[E1' _]].
    - rewrite (proj1 Hp1 l i E1') in Ei; injection Ei as <-.
      pose proof (proj1 Hp2 l i E2') as E; rewrite E in E2'; unfold inVb in E2'; cbn [v_label v_index] in E2'.
      rewrite Hcnt; apply Nat.ltb_lt, E2'.
    - rewrite Ei in E1'; unfold inVb in E1'; cbn [v_label v_index] in E1'; apply Nat.ltb_ge in E1'; lia. }
  assert (Hle' : forall l j, j < lc l L2 -> j < lc l L1).
  { intros l j Hj; destruct (proj2 Hp2 l j Hj) as [i Ei].
    destruct (HB (mk_rvar l i)) as [[E1' [E2' _]]|[_ [E2' _]]].
    - rewrite (proj1 Hp2 l i E2') in Ei; injection Ei as <-.
      pose proof (proj1 Hp1 l i E1') as E; rewrite E in E1'; unfold inVb in E1'; cbn [v_label v_index] in E1'.
      rewrite Hcnt in E1'; apply Nat.ltb_lt, E1'.
    - rewrite Ei in E2'; unfold inVb in E2'; cbn [v_label v_index] in E2'; apply Nat.ltb_ge in E2'; lia. }
  assert (Hlc : forall l, lc l L1 = lc l L2).
  { intros l; destruct (Nat.lt_trichotomy (lc l L1) (lc l L2)) as [Hlt|[E|Hlt]];
      [specialize (Hle' _ _ Hlt); lia|exact E|specialize (Hle _ _ Hlt); lia]. }
  assert (EL : L1 = L2) by (apply (lifts_unique lenv labs Hinj); assumption); subst L2.
  assert (Hsv : forall v, sv U1 v = sv U2 v).
  { intros [g i]; destruct (HB (mk_rvar g i)) as [[E1' [E2' _]]|[E1' [E2' Eu]]].
    - rewrite (proj1 Hp1 g i E1'), (proj1 Hp2 g i E2'), Hcnt; reflexivity.
    - unfold inVb, unsh in *; destruct (sv U1 (mk_rvar g i)) as [l1 i1], (sv U2 (mk_rvar g i)) as [l2 i2].
      cbn [v_label v_index] in *; injection Eu as -> Ei; apply Nat.ltb_ge in E1', E2'; f_equal; lia. }
  assert (EU : U1 = U2) by (apply (ren_unique lenv labs Hinj false); try assumption; intros v _; apply Hsv); subst U2.
  split; [reflexivity|split; [reflexivity|split; [reflexivity|]]].
  intros [l j]; destruct (Nat.ltb_spec j (lc l L1)) as [Hj|Hj].
  - destruct (proj2 Hp1 l j Hj) as [i Ei].
    destruct (HB (mk_rvar l i)) as [[_ [_ E]]|[E _]]; rewrite Ei in E; [exact E|].
    unfold inVb in E; cbn [v_label v_index] in E; apply Nat.ltb_ge in E; lia.
  - pose proof (Hk (mk_rvar l (j - lc l L1))) as E; unfold shiftL in E; cbn [v_label v_index] in E.
    replace (j - lc l L1 + lc l L1) with j in E by lia; exact E.
Qed.

(** ** How a word begins *)

Definition pre (U : seg) : lword := match U with SNil => [] | _ => [LS U] end.

Lemma natl_pre U r : natl (pre U ++ r) = natl r.
Proof. destruct U; reflexivity. Qed.

Lemma length_pre U r : List.length r <= List.length (pre U ++ r).
Proof. destruct U; cbn; lia. Qed.

Lemma cnt_nil L g i : i <= lc g L -> cntV lenv SNil L g i = i.
Proof.
  induction i as [|i IH]; intros Hi; [reflexivity|]; cbn [cntV]; rewrite IH by lia.
  unfold inVb; cbn [Unique.sv Normalise.sget v_label v_index]; rewrite (proj2 (Nat.ltb_lt _ _)) by lia; lia.
Qed.

Lemma lpos_nil L : lpos SNil L.
Proof.
  split.
  - intros g i H; unfold inVb in H; cbn [Unique.sv Normalise.sget v_label v_index] in H; apply Nat.ltb_lt in H.
    cbn [Unique.sv Normalise.sget v_label]; rewrite cnt_nil by lia; reflexivity.
  - intros g j Hj; exists j; reflexivity.
Qed.

(** A word in normal form begins with a segment with a term, or is a
    renaming, or is a renaming and an atom. *)
Lemma head_form l : lnf l ->
  (exists Sg r, l = LS Sg :: r /\ sterm Sg /\ segok Sg r /\ lnf r)
  \/ (exists U, l = pre U /\ sshape false U /\ sren U /\ forall x, R l x = FVar (sv U x))
  \/ (exists U L a r2, l = pre U ++ LA L a :: r2 /\ sshape false U /\ sren U /\ lok L /\ lpos U L /\ lnf r2
        /\ forall x, R l x = latom L a (R r2) (sv U x)).
Proof.
  destruct l as [|[Sg|L a] r]; cbn [lnf].
  - intros _; right; left; exists SNil; split; [reflexivity|].
    split; [split; constructor|split; [constructor|reflexivity]].
  - intros [Hn [Hr [[Ht HS]|[Hsh [Hren [->|[L [a [r2 [-> Hp]]]]]]]]]].
    + left; exists Sg, r; auto.
    + right; left; exists Sg; split; [destruct Sg; [destruct (Hn eq_refl)|reflexivity]|].
      split; [exact Hsh|split; [exact Hren|]].
      intros x; unfold R; cbn [flw]; apply (fs_ren lenv labs), Hren.
    + right; right; exists Sg, L, a, r2; split; [destruct Sg; [destruct (Hn eq_refl)|reflexivity]|].
      destruct Hr as [HL Hr2].
      split; [exact Hsh|split; [exact Hren|split; [exact HL|split; [exact Hp|split; [exact Hr2|]]]]].
      intros x; unfold R; cbn [flw]; rewrite (fs_ren lenv labs) by exact Hren; reflexivity.
  - intros [HL Hr]; right; right; exists SNil, L, a, r; split; [reflexivity|].
    split; [split; constructor|split; [constructor|split; [exact HL|split; [apply lpos_nil|split; [exact Hr|reflexivity]]]]].
Qed.

(** A word that begins with a term against one that does not. *)
Lemma term_first Sg r m :
  segok Sg r -> lnf r -> sterm Sg -> lnf m -> (forall v, feq (R (LS Sg :: r) v) (R m v)) ->
  exists Sg' r', m = LS Sg' :: r' /\ sterm Sg' /\ segok Sg' r' /\ lnf r'.
Proof.
  intros HS Hr [x0 [[[u b] s] E0]] Hm E.
  destruct (head_form m Hm) as [H|[[U [_ [_ [_ EU]]]]|[U [L [a [r2 [Em [_ [_ [_ [_ [Hr2 EU]]]]]]]]]]]]; [exact H| |]; exfalso.
  - pose proof (E x0) as F; rewrite (R_cons _ _ (so_pure _ _ HS)), EU in F; unfold res in F; rewrite E0 in F; exact F.
  - pose proof (E x0) as F; rewrite (R_cons _ _ (so_pure _ _ HS)), EU in F; unfold res in F; rewrite E0 in F.
    unfold Unique.latom in F; destruct (_ <? _); [|exact F].
    destruct (R r2 (sv U x0)) as [v|u' b' k'|a' z k'] eqn:Ey; cbn [feq] in F; try (destruct F; fail).
    destruct F as [_ [_ Hk]]; destruct (tdeep r2 Hr2 _ _ _ _ Ey) as [e [He Hde]].
    assert (E1 : natl r = e).
    { apply (deep_unique _ _ _ _ (deep_fs lenv _ s _ (deep_R r)) Hde); intros i; apply Hk; intros _; apply named_big. }
    assert (E2 : natl (LS Sg :: r) = natl m).
    { apply (deep_unique _ _ _ _ (deep_R _) (deep_R _)); intros i; apply E. }
    rewrite Em, natl_pre in E2; cbn [natl] in E2; lia.
Qed.

(** A renaming against a renaming and an atom. *)
Lemma end_vs_atom U U' L a K :
  sren U' -> (forall v, feq (FVar (sv U v)) (latom L a K (sv U' v))) -> False.
Proof.
  intros Hr E; destruct (sv_big lenv labs U' lbig (lc lbig L) Hr) as [B HB]; destruct (HB B (le_n _)) as [j [Hj Ej]].
  pose proof (E (mk_rvar lbig B)) as F; rewrite Ej in F; unfold Unique.latom in F; cbn [v_label v_index] in F.
  rewrite (proj2 (Nat.ltb_ge _ _) Hj) in F; exact F.
Qed.

(** ** Uniqueness *)

Lemma lw_unique_n : forall n l m, List.length l < n -> lnf l -> lnf m -> (forall v, feq (R l v) (R m v)) -> l = m.
Proof.
  induction n as [|n IH]; intros l m Hlen Hl Hm E; [lia|].
  assert (E' : forall v, feq (R m v) (R l v)) by (intros v; apply feq_sym, E).
  destruct (head_form l Hl) as [[Sg [r [El [Ht [HS Hr]]]]]|Hl'].
  { subst l; destruct (term_first Sg r m HS Hr Ht Hm E) as [Sg' [r' [-> [Ht' [HS' Hr']]]]].
    assert (H : Sg = Sg' /\ r = r').
    { apply step_terms; try assumption.
      - intros _ _ H; apply (IH r r'); [cbn [List.length] in Hlen; lia|assumption..].
      - intros x; rewrite <- (R_cons _ _ (so_pure _ _ HS)), <- (R_cons _ _ (so_pure _ _ HS')); apply E. }
    destruct H as [<- <-]; reflexivity. }
  destruct (head_form m Hm) as [[Sg' [r' [Em [Ht' [HS' Hr']]]]]|Hm'].
  { subst m; destruct (term_first Sg' r' l HS' Hr' Ht' Hl E') as [Sg [r [-> [Ht [HS Hr]]]]].
    exfalso; destruct Hl' as [[U [EU [_ [HrU _]]]]|[U [L [a [r2 [EU [_ [HrU _]]]]]]]];
      (destruct U; [discriminate EU|]; injection EU as -> _; exact (sren_noterm _ HrU Ht)). }
  destruct Hl' as [[U [-> [HsU [HrU EU]]]]|[U [L [a [r2 [-> [HsU [HrU [HL [Hp [Hr2 EU]]]]]]]]]]];
    destruct Hm' as [[U' [-> [HsU' [HrU' EU']]]]|[U' [L' [a' [r2' [-> [HsU' [HrU' [HL' [Hp' [Hr2' EU']]]]]]]]]]].
  - f_equal; apply (ren_unique lenv labs Hinj false); try assumption; intros v _.
    pose proof (E v) as F; rewrite EU, EU' in F; exact F.
  - exfalso; apply (end_vs_atom U U' L' a' (R r2') HrU'); intros v; rewrite <- EU, <- EU'; apply E.
  - exfalso; apply (end_vs_atom U' U L a (R r2) HrU); intros v; rewrite <- EU, <- EU'; apply E'.
  - destruct (peel U L a (R r2) (natl r2) U' L' a' (R r2') (natl r2')) as [<- [<- [<- HR]]]; try assumption;
      try apply deep_R; try apply nstuck_R.
    + intros v; rewrite <- EU, <- EU'; apply E.
    + do 2 f_equal; apply (IH r2 r2'); try assumption.
      pose proof (length_pre U (LA L a :: r2)) as Hle; cbn [List.length] in Hle; lia.
Qed.

(** Layered words in normal form with the same meaning in the free
    model are the same. *)
Theorem lw_unique l m : lnf l -> lnf m -> (forall v, feq (R l v) (R m v)) -> l = m.
Proof. exact (lw_unique_n (S (List.length l)) l m (Nat.lt_succ_diag_r _)). Qed.

End LUnique.

(** ** Two rules for routes *)

Section Routes.

(** Always the least variable with the result. *)
Definition route_min (k : rvar -> fres) (x y : rvar) : Prop := routed k y.

Lemma route_min_uniq k k' x y y' : keq k k' -> route_min k x y -> route_min k' x y' ->
  feq (k y) (k' y') -> named y -> y = y'.
Proof.
  intros K [Hn _] [Hn' Hb'] F Hy.
  destruct (named_or_bound y') as [Hy'|Hy'].
  - destruct (vlt_total y y') as [H|[H|H]]; [|exact H|]; exfalso.
    + exact (Hn' Hy' y Hy (feq_trans _ _ _ (feq_sym _ _ (K y Hy)) F) H).
    + exact (Hn Hy y' Hy' (feq_trans _ _ _ (K y' Hy') (feq_sym _ _ F)) H).
  - exfalso; exact (Hb' Hy' y Hy (feq_trans _ _ _ (feq_sym _ _ (K y Hy)) F)).
Qed.

(** A named input goes on as itself when the variable of the same name has
    its result; otherwise as the least named variable with it, and as a
    bound variable only when there is none.  This keeps the entries of a
    segment to what it changes. *)
Definition route_id (k : rvar -> fres) (x y : rvar) : Prop :=
  (named x -> feq (k x) (k y) -> y = x)
  /\ (named y -> y = x \/ forall y', named y' -> feq (k y') (k y) -> ~ vlt y' y)
  /\ (bound y -> forall y', named y' -> ~ feq (k y') (k y)).

Lemma route_id_uniq k k' x y y' : keq k k' -> route_id k x y -> route_id k' x y' ->
  feq (k y) (k' y') -> named y -> y = y'.
Proof.
  intros K [Ix [Nx Bx]] [Ix' [Nx' Bx']] F Hy.
  destruct (named_or_bound y') as [Hy'|Hy']; [|exfalso; exact (Bx' Hy' y Hy (feq_trans _ _ _ (feq_sym _ _ (K y Hy)) F))].
  destruct (Nx Hy) as [E1|Mn], (Nx' Hy') as [E2|Mn'].
  - congruence.
  - subst y; symmetry; apply Ix'; [exact Hy|]; exact (feq_trans _ _ _ (feq_sym _ _ (K x Hy)) F).
  - subst y'; apply Ix; [exact Hy'|]; exact (feq_trans _ _ _ (K x Hy') (feq_sym _ _ F)).
  - destruct (vlt_total y y') as [H|[H|H]]; [|exact H|]; exfalso.
    + exact (Mn' y Hy (feq_trans _ _ _ (feq_sym _ _ (K y Hy)) F) H).
    + exact (Mn y' Hy' (feq_trans _ _ _ (K y' Hy') (feq_sym _ _ F)) H).
Qed.

(** When the results of named variables are distinct, every route is
    allowed by either rule. *)
Lemma route_min_inj k x y : (forall y y', named y' -> feq (k y') (k y) -> y' = y) -> route_min k x y.
Proof.
  intros Hi; split.
  - intros Hy y' Hy' F H; rewrite (Hi y y' Hy' F) in H; exact (vlt_irrefl _ H).
  - intros Hy y' Hy' F; rewrite (Hi y y' Hy' F) in Hy'; exact (Hy' Hy).
Qed.

Lemma route_id_inj k x y : (forall y y', named y' -> feq (k y') (k y) -> y' = y) -> route_id k x y.
Proof.
  intros Hi; split; [|split].
  - intros Hx F; symmetry; exact (Hi y x Hx F).
  - intros Hy; right; intros y' Hy' F H; rewrite (Hi y y' Hy' F) in H; exact (vlt_irrefl _ H).
  - intros Hy y' Hy' F; rewrite (Hi y y' Hy' F) in Hy'; exact (Hy' Hy).
Qed.

End Routes.

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
    (route : (rvar -> fres) -> rvar -> rvar -> Prop)
    (route_uniq : forall k k' x y y', keq k k' -> route k x y -> route k' x y' -> feq (k y) (k' y') -> named y -> y = y')
    nt l m :
  lnf lenv labs gt route l -> lnf lenv labs gt route m -> lwok (tenvT nt) l -> lwok (tenvT nt) m ->
  (forall aenv penv, lwden lenv (tenvT nt) aenv penv l = lwden lenv (tenvT nt) aenv penv m) ->
  l = m.
Proof.
  intros Hl Hm Ol Om Heq.
  exact (lw_unique lenv labs Hinj gt gt_irrefl gt_trans gt_keq route route_uniq l m Hl Hm (lw_adequacy nt l m Ol Om Heq)).
Qed.

End Adequacy.
