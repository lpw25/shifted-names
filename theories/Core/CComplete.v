(** * The normaliser is complete for comprehension models

    The normaliser's own operations on normal words form a comprehension
    model, the term model ([tmodel]): environments are normal words,
    values are values, [cpop h] is [pushW h], [chd h] is [lookup h 0] and
    [cpush h] is [pushE h].  An expression means its normal form there
    ([tm_norm]), so expressions equal in every model have the same normal
    form ([cn_complete]).  With [CSound.cn_sound]: [cn_eq] decides
    equality in comprehension models ([cn_eq_correct]).

    The facts must form a strict order: [lt_known] irreflexive and
    transitive. *)

From Stdlib Require Import List Bool Arith Eqdep_dec Lia.
From ShiftedNames.Core Require Import Label Normalise GEval CNorm Comp CSound.
Import ListNotations.

Section Complete.

Variable F : order.
Hypothesis Hirr : forall a, lt_known F a a = false.
Hypothesis Htrans : forall a b c, lt_known F a b = true -> lt_known F b c = true -> lt_known F a c = true.

(** ** The order *)

Lemma lexp_eqb_false a b : lexp_eqb a b = false <-> a <> b.
Proof.
  split; intros H. - intros E; apply lexp_eqb_eq in E; congruence.
  - destruct (lexp_eqb a b) eqn:E; [apply lexp_eqb_eq in E; contradiction|reflexivity].
Qed.

Lemma lexp_eqb_refl a : lexp_eqb a a = true.
Proof. apply lexp_eqb_eq; reflexivity. Qed.

Lemma lexp_eqb_sym a b : lexp_eqb a b = lexp_eqb b a.
Proof. apply eq_iff_eq_true; rewrite !lexp_eqb_eq; split; auto. Qed.

Lemma before_spec a b : before F a b = true <-> a <> b /\ lt_known F a b = true.
Proof.
  unfold before, lcmp; destruct (lexp_eqb a b) eqn:E.
  - apply lexp_eqb_eq in E; split; [discriminate|intros [N _]; contradiction].
  - apply lexp_eqb_false in E; destruct (lt_known F a b) eqn:L.
    + split; auto.
    + destruct (lt_known F b a); split; try discriminate; intros [_ H]; discriminate.
Qed.

Lemma kd_spec a b : kd F a b = true <-> a <> b /\ (lt_known F a b = true \/ lt_known F b a = true).
Proof.
  unfold kd, lcmp; destruct (lexp_eqb a b) eqn:E.
  - apply lexp_eqb_eq in E; split; [discriminate|intros [N _]; contradiction].
  - apply lexp_eqb_false in E; destruct (lt_known F a b) eqn:L1; [split; auto|].
    destruct (lt_known F b a) eqn:L2; [split; auto|split; [discriminate|intros [_ [H|H]]; discriminate]].
Qed.

Lemma kd_sym a b : kd F a b = kd F b a.
Proof.
  apply eq_iff_eq_true; split; intros H; apply kd_spec in H as [N D]; apply kd_spec; split; auto; tauto.
Qed.

Lemma before_kd a b : before F a b = true -> kd F a b = true.
Proof. intros H; apply before_spec in H as [N L]; apply kd_spec; auto. Qed.

Lemma before_neq a b : before F a b = true -> a <> b.
Proof. intros H; apply before_spec in H as [N _]; exact N. Qed.

Lemma before_trans a b c : before F a b = true -> before F b c = true -> before F a c = true.
Proof.
  intros H1 H2; apply before_spec in H1 as [_ L1]; apply before_spec in H2 as [_ L2].
  apply before_spec; split; [|apply (Htrans a b c L1 L2)].
  intros ->; pose proof (Htrans c b c L1 L2) as L; rewrite Hirr in L; discriminate.
Qed.

Lemma before_asym a b : before F a b = true -> before F b a = false.
Proof.
  intros H; destruct (before F b a) eqn:E; [|reflexivity].
  pose proof (before_trans a b a H E) as L; apply before_neq in L; contradiction.
Qed.

Lemma before_irrefl a : before F a a = false.
Proof. destruct (before F a a) eqn:E; [apply before_neq in E; contradiction|reflexivity]. Qed.

(** ** Steps sorting before a label *)

Definition sbefore (h : lexp) (s : cstep) : Prop := exists l, slabel s = Some l /\ before F l h = true.

(** Where a step on [h] stops, in [p ++ q]. *)
Definition stops (h : lexp) (q : cword) : Prop :=
  match q with
  | [] => True
  | s :: _ => match slabel s with Some l => before F l h = false | None => True end
  end.

Lemma stop_app h p q : Forall (sbefore h) p -> stops h q -> stop F h (p ++ q) = (p, q).
Proof.
  intros Hp Hq; induction p as [|s p IH]; cbn [app].
  - destruct q as [|s q]; [reflexivity|]; cbn [stops] in Hq.
    destruct s as [g v|g|a]; cbn [slabel] in Hq; cbn [stop]; [rewrite Hq|rewrite Hq|]; reflexivity.
  - inversion Hp as [|? ? [l [El Bl]] Hp']; subst.
    destruct s as [g v|g|a]; cbn in El; try discriminate; injection El as ->; cbn [stop];
      rewrite Bl, IH by exact Hp'; reflexivity.
Qed.

Lemma stop_stops h w p r : stop F h w = (p, r) -> stops h r.
Proof.
  revert p r; induction w as [|s w IH]; intros p r E; cbn [stop] in E.
  - injection E as <- <-; exact I.
  - destruct s as [g v|g|a].
    + destruct (before F g h) eqn:B; [destruct (stop F h w) eqn:E'; injection E as <- <-; apply (IH _ _ eq_refl)|].
      injection E as <- <-; cbn [stops slabel]; exact B.
    + destruct (before F g h) eqn:B; [destruct (stop F h w) eqn:E'; injection E as <- <-; apply (IH _ _ eq_refl)|].
      injection E as <- <-; cbn [stops slabel]; exact B.
    + injection E as <- <-; exact I.
Qed.

Lemma stop_parts h w p r : stop F h w = (p, r) -> w = p ++ r /\ Forall (sbefore h) p /\ stops h r.
Proof.
  intros E; destruct (stop_spec F h w p r E) as [H1 H2]; split; [exact H1|split; [exact H2|apply (stop_stops h w p r), E]].
Qed.

(** ** Lookups pass a step on a label known distinct *)

Lemma lookup_pass g i p q :
  Forall (fun s => exists l, slabel s = Some l /\ kd F l g = true) p -> lookup F g i (p ++ q) = lookup F g i q.
Proof.
  induction p as [|s p IH]; intros Hp; [reflexivity|].
  inversion Hp as [|? ? [l [El Kl]] Hp']; subst.
  assert (N : lexp_eqb l g = false) by (apply lexp_eqb_false; apply kd_spec in Kl as [N _]; exact N).
  destruct s as [h v|h|a]; cbn in El; try discriminate; injection El as ->; cbn [app lookup];
    rewrite N, Kl; apply IH, Hp'.
Qed.

Lemma sbefore_kd h p : Forall (sbefore h) p -> Forall (fun s => exists l, slabel s = Some l /\ kd F l h = true) p.
Proof. intros H; eapply Forall_impl; [|exact H]; intros s [l [E B]]; exists l; split; [exact E|apply before_kd, B]. Qed.

(** A dropped step: [relnf_go] drops a step on [h] behind steps sorting
    before [h], when [h] is known distinct from [g]. *)
Lemma relnf_go_drop g h x r q : forall kept,
  kd F g h = true -> slabel x = Some h -> forallb (kd F h) kept = true -> Forall (sbefore h) q ->
  relnf_go F g kept (q ++ x :: r) = relnf_go F g kept (q ++ r).
Proof.
  induction q as [|s q IH]; intros kept K Ex Hk Hq.
  - cbn [app]; destruct x as [l v|l|a]; cbn in Ex; try discriminate; injection Ex as ->; cbn [relnf_go];
      rewrite K, Hk; reflexivity.
  - inversion Hq as [|? ? [l [El Bl]] Hq']; subst.
    destruct s as [l' v|l'|a]; cbn in El; try discriminate; injection El as ->; cbn [app relnf_go];
      (destruct (kd F g l && forallb (kd F l) kept); [apply IH; assumption|f_equal; apply IH; try assumption];
       cbn [forallb]; rewrite Hk, andb_true_r, kd_sym; apply before_kd, Bl).
Qed.

(** A lookup of [g] does not see a step on [h], known distinct from [g],
    behind steps sorting before [h]. *)
Lemma lookup_drop g h x i q r :
  kd F g h = true -> slabel x = Some h -> Forall (sbefore h) q ->
  lookup F g i (q ++ x :: r) = lookup F g i (q ++ r).
Proof.
  revert i; induction q as [|s q IH]; intros i K Ex Hq.
  - cbn [app]; assert (N : lexp_eqb h g = false) by (apply lexp_eqb_false; apply kd_spec in K as [N _]; auto).
    destruct x as [l v|l|a]; cbn in Ex; try discriminate; injection Ex as ->; cbn [lookup];
      rewrite N, kd_sym, K; reflexivity.
  - inversion Hq as [|? ? [l [El Bl]] Hq']; subst.
    assert (R : relnf F g (s :: q ++ x :: r) = relnf F g (s :: q ++ r)).
    { destruct s as [l' v|l'|a]; cbn in El; try discriminate; injection El as ->; cbn [relnf]; f_equal;
        apply (relnf_go_drop g h); try assumption; cbn [forallb]; rewrite andb_true_r, kd_sym; apply before_kd, Bl. }
    destruct s as [l' v|l'|a]; cbn in El; try discriminate; injection El as ->; cbn [app lookup].
    + destruct (lexp_eqb l g); [destruct i as [|i]; [reflexivity|apply IH; assumption]|].
      destruct (kd F l g); [apply IH; assumption|]; cbn [app] in R; rewrite R; reflexivity.
    + destruct (lexp_eqb l g); [apply IH; assumption|].
      destruct (kd F l g); [apply IH; assumption|]; cbn [app] in R; rewrite R; reflexivity.
Qed.

(** ** Normal words

    Adjacent steps are sorted, a weakening on [h] is not followed by an
    entry on [h] (they would cancel), and an entry on [h] is not followed
    by a weakening on [h] when its value is what the rest gives [h₀]
    (they would be absorbed). *)

Definition sorted_pair (s s' : cstep) : bool :=
  match slabel s, slabel s' with Some l, Some l' => negb (before F l' l) | _, _ => true end.

Definition okpair (s : cstep) (w : cword) : bool :=
  match w with
  | [] => true
  | s' :: r =>
      sorted_pair s s' &&
      match s, s' with
      | SW h, SE h' _ => negb (lexp_eqb h h')
      | SE h v, SW h' => negb (lexp_eqb h h' && val_eqb v (lookup F h 0 r))
      | _, _ => true
      end
  end.

Fixpoint nfb (w : cword) : bool :=
  match w with [] => true | s :: w' => okpair s w' && nfb w' end.

Lemma nfb_app_r p q : nfb (p ++ q) = true -> nfb q = true.
Proof. induction p as [|s p IH]; cbn [app nfb]; [auto|]; intros H; apply andb_true_iff in H as [_ H]; auto. Qed.

Lemma nfb_okpair p s q : nfb (p ++ s :: q) = true -> okpair s q = true.
Proof. intros H; apply nfb_app_r in H; cbn [nfb] in H; apply andb_true_iff in H as [H _]; exact H. Qed.

(** The step after an entry or weakening on [h] does not sort before
    [h]. *)
Lemma okpair_stops h s q : slabel s = Some h -> okpair s q = true -> stops h q.
Proof.
  intros Es; destruct q as [|s' q]; [intros _; exact I|]; cbn [okpair stops].
  intros H; apply andb_true_iff in H as [H _]; unfold sorted_pair in H; rewrite Es in H.
  destruct (slabel s') as [l'|]; [|exact I]; apply negb_true_iff, H.
Qed.

(** ** The laws of pairing in the term model *)

Lemma pushW_pushE h t w : nfb w = true -> pushW F h (pushE F h t w) = w.
Proof.
  intros Hw; unfold pushE; destruct (stop F h w) as [p r] eqn:E.
  destruct (stop_parts h w p r E) as [-> [Hp Hr]].
  assert (Ins : pushW F h (p ++ SE h t :: r) = p ++ r).
  { unfold pushW; rewrite stop_app by (exact Hp || (cbn; apply before_irrefl)); rewrite lexp_eqb_refl; reflexivity. }
  destruct r as [|[g v|g|a] r']; try exact Ins.
  destruct (lexp_eqb g h && val_eqb t (lookup F h 0 r')) eqn:G; [|exact Ins].
  apply andb_true_iff in G as [G _]; apply lexp_eqb_eq in G; subst g.
  pose proof (nfb_okpair p (SW h) r' Hw) as Hok.
  unfold pushW; rewrite stop_app by (exact Hp || exact (okpair_stops h (SW h) r' eq_refl Hok)).
  destruct r' as [|[g v|g|a] r'']; try reflexivity.
  cbn [okpair] in Hok; apply andb_true_iff in Hok as [_ Hok]; apply negb_true_iff in Hok; rewrite lexp_eqb_sym, Hok.
  reflexivity.
Qed.

Lemma lookup_pushE h t w : lookup F h 0 (pushE F h t w) = t.
Proof.
  unfold pushE; destruct (stop F h w) as [p r] eqn:E.
  destruct (stop_parts h w p r E) as [-> [Hp _]].
  assert (Ins : lookup F h 0 (p ++ SE h t :: r) = t)
    by (rewrite lookup_pass by (apply sbefore_kd, Hp); cbn; rewrite lexp_eqb_refl; reflexivity).
  destruct r as [|[g v|g|a] r']; try exact Ins.
  destruct (lexp_eqb g h && val_eqb t (lookup F h 0 r')) eqn:G; [|exact Ins].
  apply andb_true_iff in G as [_ G]; apply val_eqb_eq in G; subst t.
  rewrite lookup_pass by (apply sbefore_kd, Hp); reflexivity.
Qed.

Lemma pushE_pushW h w : nfb w = true -> pushE F h (lookup F h 0 w) (pushW F h w) = w.
Proof.
  intros Hw; unfold pushW; destruct (stop F h w) as [p r] eqn:E.
  destruct (stop_parts h w p r E) as [-> [Hp Hr]].
  rewrite lookup_pass by (apply sbefore_kd, Hp).
  assert (Ins : pushE F h (lookup F h 0 r) (p ++ SW h :: r) = p ++ r).
  { unfold pushE; rewrite stop_app by (exact Hp || (cbn; apply before_irrefl)).
    rewrite lexp_eqb_refl, val_eqb_refl; reflexivity. }
  destruct r as [|[g v|g|a] r']; try exact Ins.
  destruct (lexp_eqb g h) eqn:G; [|exact Ins].
  apply lexp_eqb_eq in G; subst g; cbn [lookup]; rewrite lexp_eqb_refl.
  pose proof (nfb_okpair p (SE h v) r' Hw) as Hok.
  unfold pushE; rewrite stop_app by (exact Hp || exact (okpair_stops h (SE h v) r' eq_refl Hok)).
  destruct r' as [|[g v'|g|a] r'']; try reflexivity.
  cbn [okpair] in Hok; apply andb_true_iff in Hok as [_ Hok]; apply negb_true_iff in Hok.
  rewrite lexp_eqb_sym, Hok; reflexivity.
Qed.

(** Names: [hᵢ] is [h₀] after [i] weakenings on [h]. *)
Lemma lookup_pushW_same h j w : lookup F h j (pushW F h w) = lookup F h (S j) w.
Proof.
  unfold pushW; destruct (stop F h w) as [p r] eqn:E.
  destruct (stop_parts h w p r E) as [-> [Hp _]].
  assert (Ins : lookup F h j (p ++ SW h :: r) = lookup F h (S j) (p ++ r)).
  { rewrite !lookup_pass by (apply sbefore_kd, Hp); cbn [lookup]; rewrite lexp_eqb_refl; reflexivity. }
  destruct r as [|[g v|g|a] r']; try exact Ins.
  destruct (lexp_eqb g h) eqn:G; [|exact Ins].
  apply lexp_eqb_eq in G; subst g; rewrite !lookup_pass by (apply sbefore_kd, Hp).
  cbn [lookup]; rewrite lexp_eqb_refl; reflexivity.
Qed.

(** A lookup of [g] does not see a weakening or an entry on [h] known
    distinct from [g]. *)
Lemma lookup_pushW_other g h i w : kd F g h = true -> lookup F g i (pushW F h w) = lookup F g i w.
Proof.
  intros K; unfold pushW; destruct (stop F h w) as [p r] eqn:E.
  destruct (stop_parts h w p r E) as [-> [Hp _]].
  assert (Ins : lookup F g i (p ++ SW h :: r) = lookup F g i (p ++ r)) by (apply (lookup_drop g h); auto).
  destruct r as [|[g' v|g'|a] r']; try exact Ins.
  destruct (lexp_eqb g' h) eqn:G; [|exact Ins].
  apply lexp_eqb_eq in G; subst g'; symmetry; apply (lookup_drop g h); auto.
Qed.

Lemma lookup_pushE_other g h t i w : kd F g h = true -> lookup F g i (pushE F h t w) = lookup F g i w.
Proof.
  intros K; unfold pushE; destruct (stop F h w) as [p r] eqn:E.
  destruct (stop_parts h w p r E) as [-> [Hp _]].
  assert (Ins : lookup F g i (p ++ SE h t :: r) = lookup F g i (p ++ r)) by (apply (lookup_drop g h); auto).
  destruct r as [|[g' v|g'|a] r']; try exact Ins.
  destruct (lexp_eqb g' h && val_eqb t (lookup F h 0 r')) eqn:G; [|exact Ins].
  apply andb_true_iff in G as [G _]; apply lexp_eqb_eq in G; subst g'; symmetry; apply (lookup_drop g h); auto.
Qed.

(** ** Normal words stay normal *)

(** Changing the word behind steps sorting before [h]. *)
Lemma nf_change h z z' :
  nfb z' = true ->
  (forall s, sbefore h s -> okpair s z = true -> okpair s z' = true) ->
  (forall l i q, before F l h = true -> Forall (sbefore h) q -> lookup F l i (q ++ z) = lookup F l i (q ++ z')) ->
  forall p, Forall (sbefore h) p -> nfb (p ++ z) = true -> nfb (p ++ z') = true.
Proof.
  intros Hz' J L; induction p as [|s p IH]; intros Hp Hw; [exact Hz'|].
  inversion Hp as [|? ? Hs Hp']; subst; cbn [app nfb] in Hw |- *.
  apply andb_true_iff in Hw as [Ho Hw]; rewrite (IH Hp' Hw), andb_true_r.
  destruct p as [|s1 p1]; [apply J; assumption|].
  cbn [app okpair] in Ho |- *; destruct s as [l v|l|a]; [|exact Ho|exact Ho].
  destruct s1 as [l1 v1|l1|a1]; try exact Ho.
  destruct Hs as [l' [El Bl]]; cbn in El; injection El as <-.
  inversion Hp' as [|? ? _ Hp1]; subst; rewrite <- (L l 0 p1 Bl Hp1); exact Ho.
Qed.

(** The step after a step on [h] does not sort before a label sorting
    before [h]. *)
Lemma okpair_junction h s x q :
  sbefore h s -> slabel x = Some h -> okpair x q = true -> okpair s q = true.
Proof.
  intros [l [El Bl]] Ex Hx; destruct q as [|s' q]; [reflexivity|].
  pose proof (okpair_stops h x (s' :: q) Ex Hx) as St; cbn [stops] in St.
  assert (Sp : sorted_pair s s' = true).
  { unfold sorted_pair; rewrite El; destruct (slabel s') as [l'|] eqn:El'; [|reflexivity].
    apply negb_true_iff; destruct (before F l' l) eqn:B; [|reflexivity].
    rewrite (before_trans l' l h B Bl) in St; discriminate. }
  cbn [okpair]; rewrite Sp; cbn [andb].
  destruct s as [g v|g|a]; cbn in El; try discriminate; injection El as ->;
    destruct s' as [g' v'|g'|a']; try reflexivity; cbn in St;
    (assert (N : lexp_eqb l g' = false) by (apply lexp_eqb_false; intros <-; rewrite Bl in St; discriminate));
    rewrite N; reflexivity.
Qed.

Lemma okpair_before_new h s x q :
  sbefore h s -> slabel x = Some h -> okpair s (x :: q) = true.
Proof.
  intros [l [El Bl]] Ex; cbn [okpair]; unfold sorted_pair; rewrite El, Ex, before_asym by exact Bl; cbn [negb andb].
  assert (N : lexp_eqb l h = false) by (apply lexp_eqb_false, before_neq, Bl).
  destruct s as [g v|g|a]; cbn in El; try discriminate; injection El as ->;
    destruct x as [g' v'|g'|a']; cbn in Ex; try discriminate; injection Ex as ->; try reflexivity; rewrite N; reflexivity.
Qed.

Lemma pushW_nf h w : nfb w = true -> nfb (pushW F h w) = true.
Proof.
  intros Hw; unfold pushW; destruct (stop F h w) as [p r] eqn:E.
  destruct (stop_parts h w p r E) as [-> [Hp Hr]].
  assert (Ins : r = [] \/ (exists s r', r = s :: r' /\ forall v, s <> SE h v) -> nfb (p ++ SW h :: r) = true).
  { intros Hn; apply (nf_change h r (SW h :: r)); auto.
    - cbn [nfb]; rewrite (nfb_app_r p r Hw), andb_true_r.
      destruct r as [|s r']; [reflexivity|]; cbn [okpair]; unfold sorted_pair; cbn [slabel].
      cbn [stops] in Hr; destruct (slabel s) as [l'|]; [rewrite Hr|]; cbn [negb andb];
        destruct s as [g v|g|a]; try reflexivity;
        (destruct Hn as [Hn|[s' [r'' [Es Hs]]]]; [discriminate|injection Es as <- _];
         destruct (lexp_eqb h g) eqn:G; [apply lexp_eqb_eq in G; subst g; exfalso; apply (Hs v); reflexivity|reflexivity]).
    - intros s Hs _; apply (okpair_before_new h s (SW h) r Hs eq_refl).
    - intros l i q Bl Hq; symmetry; apply (lookup_drop l h); auto; apply before_kd, Bl. }
  destruct r as [|[g v|g|a] r']; try (apply Ins; first [left; reflexivity|right; eexists; eexists; split; [reflexivity|intros v' Ev; discriminate]]).
  destruct (lexp_eqb g h) eqn:G.
  - apply lexp_eqb_eq in G; subst g.
    pose proof (nfb_okpair p (SE h v) r' Hw) as Hok.
    apply (nf_change h (SE h v :: r') r'); auto.
    + exact (nfb_app_r (p ++ [SE h v]) r' ltac:(rewrite <- app_assoc; exact Hw)).
    + intros s Hs _; apply (okpair_junction h s (SE h v) r' Hs eq_refl Hok).
    + intros l i q Bl Hq; apply (lookup_drop l h); auto; apply before_kd, Bl.
  - apply Ins; right; eexists; eexists; split; [reflexivity|intros v' Ev; injection Ev as -> _].
    rewrite lexp_eqb_refl in G; discriminate.
Qed.

Lemma pushE_nf h t w : nfb w = true -> nfb (pushE F h t w) = true.
Proof.
  intros Hw; unfold pushE; destruct (stop F h w) as [p r] eqn:E.
  destruct (stop_parts h w p r E) as [-> [Hp Hr]].
  assert (Ins : (forall r', r = SW h :: r' -> val_eqb t (lookup F h 0 r') = false) -> nfb (p ++ SE h t :: r) = true).
  { intros Hn; apply (nf_change h r (SE h t :: r)); auto.
    - cbn [nfb]; rewrite (nfb_app_r p r Hw), andb_true_r.
      destruct r as [|s r']; [reflexivity|]; cbn [stops] in Hr.
      assert (Sp : sorted_pair (SE h t) s = true)
        by (unfold sorted_pair; cbn [slabel]; destruct (slabel s) as [l'|]; [rewrite Hr|]; reflexivity).
      cbn [okpair]; rewrite Sp; cbn [andb].
      destruct s as [g v|g|a]; try reflexivity.
      destruct (lexp_eqb h g) eqn:G; [|reflexivity].
      apply lexp_eqb_eq in G; subst g; rewrite (Hn r' eq_refl); reflexivity.
    - intros s Hs _; apply (okpair_before_new h s (SE h t) r Hs eq_refl).
    - intros l i q Bl Hq; symmetry; apply (lookup_drop l h); auto; apply before_kd, Bl. }
  destruct r as [|[g v|g|a] r']; try (apply Ins; intros r'' Er; discriminate).
  destruct (lexp_eqb g h && val_eqb t (lookup F h 0 r')) eqn:G.
  - apply andb_true_iff in G as [G _]; apply lexp_eqb_eq in G; subst g.
    pose proof (nfb_okpair p (SW h) r' Hw) as Hok.
    apply (nf_change h (SW h :: r') r'); auto.
    + exact (nfb_app_r (p ++ [SW h]) r' ltac:(rewrite <- app_assoc; exact Hw)).
    + intros s Hs _; apply (okpair_junction h s (SW h) r' Hs eq_refl Hok).
    + intros l i q Bl Hq; apply (lookup_drop l h); auto; apply before_kd, Bl.
  - apply Ins; intros r'' Er; injection Er as -> <-; rewrite lexp_eqb_refl in G; exact G.
Qed.

(** ** Weakenings on ordered labels commute *)

(** What [pushW h] does at the point where it stops. *)
Definition yW (h : lexp) (r : cword) : cword :=
  match r with
  | SE g _ :: r' => if lexp_eqb g h then r' else SW h :: r
  | _ => SW h :: r
  end.

Lemma pushW_at h p r : Forall (sbefore h) p -> stops h r -> pushW F h (p ++ r) = p ++ yW h r.
Proof.
  intros Hp Hr; unfold pushW; rewrite stop_app by assumption.
  destruct r as [|[g v|g|a] r']; cbn [yW]; try reflexivity; destruct (lexp_eqb g h); reflexivity.
Qed.

Lemma sbefore_trans g h p : before F g h = true -> Forall (sbefore g) p -> Forall (sbefore h) p.
Proof.
  intros B H; eapply Forall_impl; [|exact H]; intros s [l [E Bl]]; exists l; split; [exact E|eapply before_trans; eauto].
Qed.

Lemma pushW_comm g h w : before F g h = true -> nfb w = true ->
  pushW F g (pushW F h w) = pushW F h (pushW F g w).
Proof.
  intros B Hw.
  destruct (stop F g w) as [pg rg] eqn:Eg; destruct (stop_parts g w pg rg Eg) as [-> [Hpg Hrg]].
  pose proof (sbefore_trans g h pg B Hpg) as Hpg'.
  destruct (stop F h rg) as [m rh] eqn:Eh; destruct (stop_parts h rg m rh Eh) as [-> [Hm Hrh]].
  rewrite (pushW_at g pg (m ++ rh) Hpg Hrg).
  rewrite app_assoc, (pushW_at h (pg ++ m) rh) by (try apply Forall_app; auto); rewrite <- app_assoc.
  destruct m as [|s0 m'].
  - cbn [app] in *.
    (* the step where both stop is not on [g], which sorts before [h] *)
    assert (Yg : yW g rh = SW g :: rh).
    { destruct rh as [|[g' v|g'|a] r']; try reflexivity; cbn [yW].
      destruct (lexp_eqb g' g) eqn:G; [|reflexivity].
      apply lexp_eqb_eq in G; subst g'; cbn [stops slabel] in Hrh; rewrite B in Hrh; discriminate. }
    rewrite Yg.
    replace (pg ++ SW g :: rh) with ((pg ++ [SW g]) ++ rh) by (rewrite <- app_assoc; reflexivity).
    rewrite (pushW_at h (pg ++ [SW g]) rh);
      [|apply Forall_app; split; [exact Hpg'|constructor; [exists g; split; [reflexivity|exact B]|constructor]]|exact Hrh].
    rewrite <- app_assoc; cbn [app].
    destruct rh as [|[g' v|g'|a] r'] eqn:Erh;
      try (rewrite (pushW_at g pg) by (auto; cbn [stops slabel]; apply before_asym, B); reflexivity).
    cbn [yW]; destruct (lexp_eqb g' h) eqn:G;
      [|rewrite (pushW_at g pg) by (auto; cbn [stops slabel]; apply before_asym, B); reflexivity].
    apply lexp_eqb_eq in G; subst g'.
    pose proof (nfb_okpair pg (SE h v) r' Hw) as Hok.
    pose proof (okpair_stops h (SE h v) r' eq_refl Hok) as St.
    assert (Stg : stops g r').
    { destruct r' as [|s' r'']; [exact I|]; cbn [stops] in St |- *.
      destruct (slabel s') as [l'|]; [|exact I].
      destruct (before F l' g) eqn:Bl; [|reflexivity].
      rewrite (before_trans l' g h Bl B) in St; discriminate. }
    rewrite (pushW_at g pg r' Hpg Stg).
    destruct r' as [|[g'' v'|g''|a] r'']; try reflexivity; cbn [yW].
    destruct (lexp_eqb g'' g) eqn:G; [|reflexivity].
    apply lexp_eqb_eq in G; subst g''.
    cbn [okpair sorted_pair slabel] in Hok; rewrite B in Hok; discriminate.
  - (* both stop at [s0], which is on a label sorting before [h] *)
    inversion Hm as [|? ? [l0 [El0 Bl0]] Hm']; subst.
    cbn [app] in *.
    rewrite (pushW_at g pg (s0 :: m' ++ yW h rh) Hpg Hrg).
    assert (Hbm : forall z, Forall (sbefore h) z -> pushW F h (pg ++ z ++ rh) = pg ++ z ++ yW h rh)
      by (intros z Hz; rewrite app_assoc, pushW_at by (try apply Forall_app; auto); rewrite <- app_assoc; reflexivity).
    assert (HgS : sbefore h (SW g)) by (exists g; split; [reflexivity|exact B]).
    assert (Hl0 : forall s0', slabel s0' = Some l0 -> sbefore h s0') by (intros s0' E; exists l0; split; [exact E|exact Bl0]).
    destruct s0 as [g' v|g'|a]; cbn in El0; try discriminate; injection El0 as ->; cbn [yW].
    + destruct (lexp_eqb l0 g).
      * rewrite (Hbm m' Hm'); reflexivity.
      * change (pg ++ SW g :: SE l0 v :: m' ++ rh) with (pg ++ (SW g :: SE l0 v :: m') ++ rh).
        rewrite (Hbm (SW g :: SE l0 v :: m')); [reflexivity|].
        constructor; [exact HgS|constructor; [apply Hl0; reflexivity|exact Hm']].
    + change (pg ++ SW g :: SW l0 :: m' ++ rh) with (pg ++ (SW g :: SW l0 :: m') ++ rh).
      rewrite (Hbm (SW g :: SW l0 :: m')); [reflexivity|].
      constructor; [exact HgS|constructor; [apply Hl0; reflexivity|exact Hm']].
Qed.

(** ** Payloads do not see the bound label *)

Lemma unbound_drop p x q :
  Forall (fun s => exists l, slabel s = Some l /\ l <> LNone) p -> slabel x = Some LNone ->
  unbound (p ++ x :: q) = unbound (p ++ q).
Proof.
  intros Hp Ex; induction p as [|s p IH].
  - destruct x as [g v|g|a]; cbn in Ex; try discriminate; injection Ex as ->; reflexivity.
  - inversion Hp as [|? ? [l [El Nl]] Hp']; subst; cbn [app].
    destruct s as [[|c|n] v|[|c|n]|a]; cbn in El; try discriminate; injection El as <-;
      try contradiction; cbn [unbound]; rewrite IH by exact Hp'; reflexivity.
Qed.

Lemma unbound_pushW w : unbound (pushW F LNone w) = unbound w.
Proof.
  unfold pushW; destruct (stop F LNone w) as [p r] eqn:E; destruct (stop_parts LNone w p r E) as [-> [Hp _]].
  assert (Hn : Forall (fun s => exists l, slabel s = Some l /\ l <> LNone) p)
    by (eapply Forall_impl; [|exact Hp]; intros s [l [El Bl]]; exists l; split; [exact El|apply before_neq, Bl]).
  assert (Ins : unbound (p ++ SW LNone :: r) = unbound (p ++ r)) by (apply unbound_drop; auto).
  destruct r as [|[g v|g|a] r']; try exact Ins.
  destruct (lexp_eqb g LNone) eqn:G; [|exact Ins].
  apply lexp_eqb_eq in G; subst g; symmetry; apply unbound_drop; auto.
Qed.

(** ** The term model *)

Definition TU : Type := {w : cword | nfb w = true}.

Lemma TU_eq (x y : TU) : proj1_sig x = proj1_sig y -> x = y.
Proof. destruct x as [x Hx], y as [y Hy]; cbn; intros ->; f_equal; apply UIP_dec, bool_dec. Qed.

Lemma atom_nf n w : nfb w = true -> nfb (SA n :: w) = true.
Proof. intros H; cbn [nfb]; rewrite H, andb_true_r; destruct w; reflexivity. Qed.

Definition tpop (h : lexp) (x : TU) : TU := exist _ (pushW F h (proj1_sig x)) (pushW_nf h _ (proj2_sig x)).
Definition thd (h : lexp) (x : TU) : cval := lookup F h 0 (proj1_sig x).
Definition tpush (h : lexp) (x : TU) (t : cval) : TU := exist _ (pushE F h t (proj1_sig x)) (pushE_nf h t _ (proj2_sig x)).
Definition tatom (n : nat) (x : TU) : TU := exist _ (SA n :: proj1_sig x) (atom_nf n _ (proj2_sig x)).
Definition tterm (u : nat) (b : option nat) (x : TU) : cval := VTerm u b (clean b (proj1_sig x)).

Lemma tpop_push h x t : tpop h (tpush h x t) = x.
Proof. apply TU_eq; apply pushW_pushE, proj2_sig. Qed.

Lemma thd_push h x t : thd h (tpush h x t) = t.
Proof. apply lookup_pushE. Qed.

Lemma tpush_pop h x : tpush h (tpop h x) (thd h x) = x.
Proof. apply TU_eq; apply pushE_pushW, proj2_sig. Qed.

Definition tmodel : cmodel := mk_cmodel TU cval tpop thd tpush tpop_push thd_push tpush_pop tatom tterm.

Lemma tm_ccons : ccons F tmodel.
Proof.
  split.
  - intros g h L x.
    assert (N : g <> h) by (intros ->; rewrite Hirr in L; discriminate).
    assert (B : before F g h = true) by (apply before_spec; auto).
    assert (K : kd F g h = true) by (apply before_kd, B).
    cbn [cpop chd tmodel]; repeat split.
    + apply TU_eq; cbn; apply pushW_comm; [exact B|apply proj2_sig].
    + unfold thd; cbn; apply lookup_pushW_other, K.
    + unfold thd; cbn; apply lookup_pushW_other; rewrite kd_sym; exact K.
  - intros u x; cbn [cterm cpop tmodel]; unfold tterm, clean; cbn; rewrite unbound_pushW; reflexivity.
Qed.

Lemma iter_tpop h i (x : TU) : proj1_sig (iter i (tpop h) x) = iter i (pushW F h) (proj1_sig x).
Proof. induction i as [|i IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma lookup_iter h i : forall j w, lookup F h j (iter i (pushW F h) w) = lookup F h (j + i) w.
Proof.
  induction i as [|i IH]; intros j w; cbn [iter]; [rewrite Nat.add_0_r; reflexivity|].
  rewrite lookup_pushW_same, IH; f_equal; lia.
Qed.

(** In the term model an expression means its normal form. *)
Theorem tm_norm_all :
  (forall a (x : TU), proj1_sig (@ca tmodel a x) = norm F a (proj1_sig x))
  /\ (forall t (x : TU), @ct tmodel t x = tval F t (proj1_sig x))
  /\ (forall p (x : TU), proj1_sig (@cp tmodel p x) = pnorm F p (proj1_sig x)).
Proof.
  apply exp_mind; intros; cbn [ca ct cp norm tval pnorm].
  - reflexivity.
  - reflexivity.
  - rewrite H0, H; reflexivity.
  - rewrite H; reflexivity.
  - cbn [cpush tmodel tpush proj1_sig]; rewrite H, H0; reflexivity.
  - cbn [cpush tmodel tpush proj1_sig]; rewrite H; reflexivity.
  - unfold cname; cbn [chd tmodel]; unfold thd; rewrite iter_tpop, lookup_iter; reflexivity.
  - cbn [cterm tmodel]; unfold tterm; rewrite H; reflexivity.
  - destruct (is_bind t); [apply H|rewrite H; reflexivity].
  - reflexivity.
  - reflexivity.
  - rewrite H0, H; reflexivity.
  - rewrite H; reflexivity.
Qed.

(** Equal in every comprehension model, same normal form. *)
Theorem cn_complete a b : cequal F a b -> norm F a [] = norm F b [].
Proof.
  intros H; pose (x0 := exist (fun w => nfb w = true) [] eq_refl : TU).
  pose proof (f_equal (@proj1_sig _ _) (H tmodel tm_ccons x0)) as E.
  rewrite !(proj1 tm_norm_all) in E; exact E.
Qed.

Theorem cn_eq_correct a b : cn_eq F a b = true <-> cequal F a b.
Proof.
  rewrite cn_eq_iff; split; [apply cn_sound|apply cn_complete].
Qed.

End Complete.
