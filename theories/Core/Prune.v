(** * Pruned maps over skew sequences

    Mapping a function [G] over the elements of a skew sequence, where [G]
    is known to act as a pure shift on every element whose uses are at or
    above some thresholds [th]: there it is [unshift tau ∘ shift th].  A
    subtree whose uses all clear the thresholds is then moved by changing
    its counts alone, and nothing below it is visited.

    The traversal carries a blocking map: the thresholds of the labels that
    some element below might still use under their threshold.  It is
    filtered by each node's counts on the way down, so a label leaves it at
    most once per path, and a node is moved as soon as it is empty.

    Mapped subtrees come back relative to base 0 (absolute), and their
    parent rebases them with the smart constructors of Skew.v. *)

From Stdlib Require Import PArith Arith Lia List Bool.
From ShiftedNames.Core Require Import Trie Counts Based Skew ATrie.
Import ListNotations.

Section Prune.

Context {X : Type} {BX : Based X} {LX : BasedLaws X}.

Variables (th tau : counts).

(** ** The blocking map *)

(** The thresholds still blocking below a node with absolute counts [M]. *)
Definition below (bl : tree nat) (M : counts) : tree nat :=
  map_filter (fun k t => match cget M k with
                         | Some m => if Nat.ltb m t then Some t else None
                         | None => None
                         end) bl.

Definition bempty (bl : tree nat) : bool := match bl with Empty => true | _ => false end.

(** Where a moved node's counts go. *)
Definition move (M : counts) : counts := cadd tau (csub M th).

(** ** The maps

    [F B x] maps the element [x] stored relative to base [B], giving the
    result relative to base 0. *)

Variable F : counts -> X -> X.

Fixpoint ktmap (bl : tree nat) (B : counts) (t : ktree X) : ktree X :=
  match t with
  | KLeaf x => KLeaf (F B x)
  | KNode a x l r =>
      let bl' := below bl (cadd B a) in
      if bempty bl' then KNode (move (cadd B a)) x l r
      else let P := cadd B a in ktnode (F P x) (ktmap bl' P l) (ktmap bl' P r)
  end.

Fixpoint atmap (bl : tree nat) (B : counts) (t : atrie X) : atrie X :=
  match t with
  | AEmpty => AEmpty
  | ANode a l o r =>
      let bl' := below bl (cadd B a) in
      if bempty bl' then ANode (move (cadd B a)) l o r
      else let P := cadd B a in amknode (atmap bl' P l) (option_map (F P) o) (atmap bl' P r)
  end.

(** The keys of the entries a pruned trie map visits ([kf] rebuilds the
    full key from the path). *)
Fixpoint atvisit (bl : tree nat) (B : counts) (kf : positive -> positive) (t : atrie X)
  : list positive :=
  match t with
  | AEmpty => []
  | ANode a l o r =>
      let bl' := below bl (cadd B a) in
      if bempty bl' then []
      else let P := cadd B a in
           match o with Some _ => [kf xH] | None => [] end
           ++ atvisit bl' P (fun k => kf (xO k)) l ++ atvisit bl' P (fun k => kf (xI k)) r
  end.

Fixpoint kmap (bl : tree nat) (B : counts) (s : kseq X) : kseq X :=
  match s with
  | KNil => KNil
  | KCons a w t s' =>
      let bl' := below bl (cadd B a) in
      if bempty bl' then KCons (move (cadd B a)) w t s'
      else let P := cadd B a in kcell w (ktmap bl' P t) (kmap bl' P s')
  end.

(** ** Specification *)

Variable G : X -> X.

(** [z] (absolute) uses nothing under the thresholds. *)
Definition clears (z : X) : Prop :=
  forall k t m, cget th k = Some t -> cget (uses z) k = Some m -> t <= m.

(** [Pd] says which (absolute) elements [G] is known on; every element
    of the structure mapped must satisfy it. *)
Variable Pd : X -> Prop.
Hypothesis HF : forall B x, eok x -> Pd (unshift B x) -> F B x = G (unshift B x).
Hypothesis HG : forall z, eok z -> Pd z -> clears z -> G z = unshift tau (shift th z).
Hypothesis HGok : forall z, eok z -> Pd z -> eok (G z).

(** The blocking map covers every use under a threshold among [L]. *)
Definition sound (bl : tree nat) (L : list X) : Prop :=
  forall z, In z L -> forall k t m,
    cget th k = Some t -> cget (uses z) k = Some m -> m < t -> get k bl = Some t.

Lemma bempty_spec bl : bempty bl = true -> forall k, get k bl = None.
Proof. destruct bl; [intros _ k; apply get_Empty|discriminate]. Qed.

Lemma oadd_le d c z : (forall n m, c = Some n -> z = Some m -> n <= m) ->
  forall n m, oadd d c = Some n -> oadd d z = Some m -> n <= m.
Proof.
  intros H n m; destruct c as [c|], z as [z|]; cbn; try discriminate.
  intros [= <-] [= <-]; specialize (H c z eq_refl eq_refl); lia.
Qed.

(** Elements below a node are above its counts. *)
Lemma lmin_le_in (L : list X) z k n m :
  In z L -> lmin L k = Some n -> cget (uses z) k = Some m -> n <= m.
Proof.
  intros Hin Hn Hm; destruct (lmin_le L z k m Hin Hm) as [n' [E Hle]]; congruence.
Qed.



Lemma Pd_child B a (L : list X) y :
  (forall k, cget a k = lmin (map (unshift a) L) k) ->
  (forall z, In z (map (unshift a) L) -> Pd (unshift B z)) -> In y L -> Pd (unshift (cadd B a) y).
Proof. intros Ha HP Hy; rewrite <- (unshift_cadd B a L y Ha Hy); apply HP, in_map, Hy. Qed.

Lemma sound_below bl B a (L : list X) :
  (forall k, cget a k = lmin (map (unshift a) L) k) ->
  sound bl (map (unshift B) (map (unshift a) L)) ->
  sound (below bl (cadd B a)) (map (unshift (cadd B a)) L).
Proof.
  intros Ha Hs z Hz k t m Ht Hm Hlt.
  apply in_map_iff in Hz as [y [<- Hy]].
  assert (Hz' : In (unshift B (unshift a y)) (map (unshift B) (map (unshift a) L)))
    by (apply in_map, in_map, Hy).
  rewrite <- (unshift_cadd B a L y Ha Hy) in Hm.
  specialize (Hs _ Hz' k t m Ht Hm Hlt).
  unfold below; rewrite get_map_filter, Hs, cget_cadd.
  rewrite uses_unshift in Hm.
  destruct (cget (uses (unshift a y)) k) as [u|] eqn:Eu; [|destruct (cget B k); discriminate].
  assert (Hin : In (unshift a y) (map (unshift a) L)) by (apply in_map, Hy).
  destruct (lmin_le _ _ k u Hin Eu) as [n [En Hn]]; rewrite Ha, En.
  destruct (cget B k) as [b|]; cbn [oadd oval] in Hm |- *; injection Hm as <-;
    rewrite (proj2 (Nat.ltb_lt _ _)) by lia; reflexivity.
Qed.

(** The shift arithmetic for a moved node. *)
Lemma move_shift M P y :
  eok y ->
  (forall k, cget (uses y) k <> None ->
             exists p, cget M k = Some p /\ cget P k = Some p
                       /\ forall t, cget th k = Some t -> t <= p) ->
  unshift tau (shift th (unshift P y)) = unshift (move M) y.
Proof.
  intros Hy HM; set (D := csub P th).
  assert (E1 : shift th (unshift P y) = unshift D y).
  { apply (unshift_inj th); [apply ok_shift, ok_unshift, Hy|apply ok_unshift, Hy|].
    rewrite unshift_shift.
    - rewrite unshift_unshift; apply unshift_ext; intros k Hk.
      destruct (HM k Hk) as [p [_ [Ep Ht]]]; rewrite dval_cplus; unfold dval, D.
      rewrite cget_csub, Ep; destruct (cget th k) as [t|] eqn:Et; cbn; [specialize (Ht t eq_refl)|]; lia.
    - apply ok_unshift, Hy.
    - intros k t m Et Em; rewrite uses_unshift in Em.
      destruct (cget (uses y) k) as [u|] eqn:Eu; [|destruct (cget P k); discriminate].
      destruct (HM k ltac:(congruence)) as [p [_ [Ep Ht]]]; rewrite Ep in Em; cbn in Em.
      specialize (Ht t Et); injection Em as <-; lia. }
  rewrite E1, unshift_unshift; apply unshift_ext; intros k Hk.
  destruct (HM k Hk) as [p [Em [Ep _]]]; rewrite dval_cplus; unfold dval, move, D.
  rewrite cget_cadd, !cget_csub, Em, Ep; destruct (cget th k), (cget tau k); cbn; lia.
Qed.

(** A node's counts are attained: relative to the node, its minimum is 0. *)
Lemma ann_cases a (L : list X) k :
  cget a k = lmin (map (unshift a) L) k ->
  (cget a k = None /\ lmin L k = None) \/ (exists x, cget a k = Some x /\ lmin L k = Some 0).
Proof.
  rewrite lmin_unshift; destruct (lmin L k) as [n|], (cget a k) as [x|]; cbn; intros H;
    try discriminate; [right; exists x; split; [reflexivity|]; injection H; intros; f_equal; lia|left; auto].
Qed.

Lemma sound_incl bl (L1 L2 : list X) : (forall z, In z L1 -> In z L2) -> sound bl L2 -> sound bl L1.
Proof. intros Hi Hs z Hz; apply Hs, Hi, Hz. Qed.

(** Below a moved node, every used label is at or above its threshold. *)
Lemma pruned_counts bl B a (L : list X) :
  (forall k, cget a k = lmin (map (unshift a) L) k) ->
  sound bl (map (unshift B) (map (unshift a) L)) ->
  bempty (below bl (cadd B a)) = true ->
  forall k, lmin L k <> None ->
    exists p, cget (cadd B a) k = Some p /\ cget (cadd B a) k = Some p
              /\ forall t, cget th k = Some t -> t <= p.
Proof.
  intros Ha Hs Hb; set (M := cadd B a); set (P := cadd B a).
  pose proof (bempty_spec _ Hb) as Hb'.
  intros k Hk; destruct (ann_cases a L k (Ha k)) as [[_ E]|[x [Ex E]]]; [contradiction|].
  exists (oval (cget B k) + x); unfold M, P; rewrite !cget_cadd, Ex.
  split; [destruct (cget B k); reflexivity|split; [destruct (cget B k); reflexivity|]].
  intros t Et; destruct (Nat.le_gt_cases t (oval (cget B k) + x)) as [|Hlt]; [assumption|exfalso].
  destruct (lmin_attained _ _ _ E) as [z0 [Hz0 Ez0]].
  assert (Hin : In (unshift B (unshift a z0)) (map (unshift B) (map (unshift a) L)))
    by (apply in_map, in_map, Hz0).
  assert (Eu : cget (uses (unshift B (unshift a z0))) k = Some (oval (cget B k) + x))
    by (rewrite !uses_unshift, Ez0, Ex; destruct (cget B k); cbn; f_equal; lia).
  specialize (Hs _ Hin k t _ Et Eu Hlt).
  specialize (Hb' k); unfold below in Hb'; rewrite get_map_filter, Hs in Hb'; fold M in Hb'.
  unfold M in Hb'; rewrite cget_cadd, Ex in Hb'.
  destruct (cget B k); cbn [oadd oval] in Hb', Hlt;
    rewrite (proj2 (Nat.ltb_lt _ _)) in Hb' by lia; discriminate.
Qed.

Lemma pruned_clears bl B a (L : list X) :
  (forall k, cget a k = lmin (map (unshift a) L) k) ->
  sound bl (map (unshift B) (map (unshift a) L)) ->
  bempty (below bl (cadd B a)) = true ->
  forall y, In y L -> clears (unshift (cadd B a) y).
Proof.
  intros Ha Hs Hb y Hy k t m Et Em; rewrite uses_unshift in Em.
  destruct (cget (uses y) k) as [u|] eqn:Eu; [|destruct (cget (cadd B a) k); discriminate].
  destruct (pruned_counts bl B a L Ha Hs Hb k (lmin_some L y k Hy ltac:(rewrite Eu; discriminate))) as [p [_ [Ep Ht]]].
  rewrite Ep in Em; cbn in Em; injection Em as <-; specialize (Ht t Et); lia.
Qed.

(** A moved node: its elements were all above the thresholds. *)
Lemma moved bl B a (L : list X) :
  (forall k, cget a k = lmin (map (unshift a) L) k) -> (forall y, In y L -> eok y) ->
  (forall z, In z (map (unshift a) L) -> Pd (unshift B z)) ->
  sound bl (map (unshift B) (map (unshift a) L)) ->
  bempty (below bl (cadd B a)) = true ->
  map (unshift (move (cadd B a))) L = map (fun y => G (unshift B y)) (map (unshift a) L)
  /\ forall k, cget (move (cadd B a)) k = lmin (map (unshift (move (cadd B a))) L) k.
Proof.
  intros Ha Hok HP Hs Hb; set (M := cadd B a); set (P := cadd B a).
  pose proof (pruned_counts bl B a L Ha Hs Hb) as HM; fold M P in HM.
  assert (Hused : forall y k, In y L -> cget (uses y) k <> None -> lmin L k <> None).
  { intros y k Hy Hk; apply (lmin_some L y k Hy Hk). }
  split.
  - rewrite map_map; apply map_ext_in; intros y Hy.
    rewrite (unshift_cadd B a L y Ha Hy).
    assert (Hy' : forall k, cget (uses y) k <> None ->
                  exists p, cget M k = Some p /\ cget P k = Some p
                            /\ forall t, cget th k = Some t -> t <= p)
      by (intros k Hk; apply HM, (Hused y k Hy Hk)).
    rewrite HG by (apply ok_unshift, Hok, Hy || apply (Pd_child B a L y Ha HP Hy)
                   || apply (pruned_clears bl B a L Ha Hs Hb y Hy)).
    symmetry; apply move_shift; [apply Hok, Hy|exact Hy'].
  - intros k; rewrite lmin_unshift.
    destruct (ann_cases a L k (Ha k)) as [[Ea E]|[x [Ex E]]]; rewrite E.
    + unfold move, M; rewrite cget_cadd, cget_csub, cget_cadd, Ea; reflexivity.
    + destruct (HM k ltac:(congruence)) as [p [Ep _]]; fold M.
      unfold move; rewrite cget_cadd, cget_csub, Ep; cbn; f_equal; lia.
Qed.

Theorem ktmap_spec t : forall bl B,
  ktinv t -> sound bl (map (unshift B) (ktlist t)) -> (forall y, In y (ktlist t) -> Pd (unshift B y)) ->
  ktinv (ktmap bl B t) /\ ktlist (ktmap bl B t) = map (fun y => G (unshift B y)) (ktlist t).
Proof.
  induction t as [x|a x l IHl r IHr]; intros bl B Ht Hs HP.
  - assert (HPx : Pd (unshift B x)) by (apply HP; left; reflexivity).
    assert (Hx : eok (F B x)) by (rewrite HF by (apply Ht || exact HPx); apply HGok; [apply ok_unshift, Ht|exact HPx]).
    split; [split; [intro k; cbn [ktlist ktann]; rewrite lmin_single; reflexivity|exact Hx]|].
    cbn; rewrite HF by (apply Ht || exact HPx); reflexivity.
  - pose proof (ktinv_ok _ Ht) as Hok; destruct Ht as [Ha [Hcwf [Hx [Hl Hr]]]].
    cbn [ktann ktlist] in Ha, Hok |- *; cbn [ktmap].
    set (L := x :: ktlist l ++ ktlist r) in *.
    assert (HokL : forall y, In y L -> eok y).
    { intros y Hy; destruct Hy as [<-|Hy]; [exact Hx|].
      apply in_app_or in Hy as [Hy|Hy]; [apply (ktinv_ok l Hl _ Hy)|apply (ktinv_ok r Hr _ Hy)]. }
    destruct (bempty (below bl (cadd B a))) eqn:Eb.
    + destruct (moved bl B a L Ha HokL HP Hs Eb) as [E Hann].
      split; [|cbn [ktlist]; exact E].
      split; [exact Hann|split; [apply cwf_cmap2|split; [exact Hx|split; assumption]]].
    + pose proof (sound_below bl B a L Ha Hs) as Hs'.
      pose proof (Pd_child B a L) as HPc.
      set (bl' := below bl (cadd B a)) in *; set (P := cadd B a) in *.
      assert (Hsl : sound bl' (map (unshift P) (ktlist l))).
      { eapply sound_incl; [|exact Hs']; intros z Hz; apply in_map_iff in Hz as [y [<- Hy]].
        apply in_map; right; apply in_or_app; left; exact Hy. }
      assert (Hsr : sound bl' (map (unshift P) (ktlist r))).
      { eapply sound_incl; [|exact Hs']; intros z Hz; apply in_map_iff in Hz as [y [<- Hy]].
        apply in_map; right; apply in_or_app; right; exact Hy. }
      destruct (IHl bl' P Hl Hsl) as [Hl' El].
      { intros y Hy; apply (HPc y Ha HP); right; apply in_or_app; left; exact Hy. }
      destruct (IHr bl' P Hr Hsr) as [Hr' Er].
      { intros y Hy; apply (HPc y Ha HP); right; apply in_or_app; right; exact Hy. }
      assert (HPx : Pd (unshift P x)) by (apply (HPc x Ha HP); left; reflexivity).
      assert (HFx : eok (F P x))
        by (rewrite HF by (exact Hx || exact HPx); apply HGok; [apply ok_unshift, Hx|exact HPx]).
      split; [apply ktinv_ktnode; assumption|].
      rewrite ktlist_ktnode, El, Er by assumption.
      rewrite HF by (exact Hx || exact HPx).
      transitivity (map (fun y => G (unshift P y)) L); [unfold L; cbn [map]; rewrite map_app; reflexivity|].
      rewrite map_map; apply map_ext_in; intros y Hy; unfold P; rewrite (unshift_cadd B a L y Ha Hy); reflexivity.
Qed.

Theorem kmap_spec s : forall bl B,
  kinv s -> sound bl (map (unshift B) (klist s)) -> (forall y, In y (klist s) -> Pd (unshift B y)) ->
  kinv (kmap bl B s) /\ klist (kmap bl B s) = map (fun y => G (unshift B y)) (klist s).
Proof.
  induction s as [|a w t s' IH]; intros bl B Hs Hsd HP; [split; [exact Hs|reflexivity]|].
  pose proof (kinv_ok _ Hs) as Hok; destruct Hs as [Ha [Hcwf [Ht Hs']]].
  cbn [ksann klist] in Ha, Hok |- *; cbn [kmap].
  set (L := ktlist t ++ klist s') in *.
  assert (HokL : forall y, In y L -> eok y).
  { intros y Hy; apply in_app_or in Hy as [Hy|Hy]; [apply (ktinv_ok t Ht _ Hy)|apply (kinv_ok s' Hs' _ Hy)]. }
  destruct (bempty (below bl (cadd B a))) eqn:Eb.
  - destruct (moved bl B a L Ha HokL HP Hsd Eb) as [E Hann].
    split; [|cbn [klist]; exact E].
    split; [exact Hann|split; [apply cwf_cmap2|split; assumption]].
  - pose proof (sound_below bl B a L Ha Hsd) as Hs2.
    pose proof (Pd_child B a L) as HPc.
    set (bl' := below bl (cadd B a)) in *; set (P := cadd B a) in *.
    destruct (ktmap_spec t bl' P Ht) as [Ht' Et].
    { eapply sound_incl; [|exact Hs2]; intros z Hz; apply in_map_iff in Hz as [y [<- Hy]].
      apply in_map, in_or_app; left; exact Hy. }
    { intros y Hy; apply (HPc y Ha HP); apply in_or_app; left; exact Hy. }
    destruct (IH bl' P Hs') as [Hs3 Es].
    { eapply sound_incl; [|exact Hs2]; intros z Hz; apply in_map_iff in Hz as [y [<- Hy]].
      apply in_map, in_or_app; right; exact Hy. }
    { intros y Hy; apply (HPc y Ha HP); apply in_or_app; right; exact Hy. }
    split; [apply kinv_kcell; assumption|].
    rewrite klist_kcell, Et, Es by assumption.
    rewrite <- map_app; fold L; rewrite map_map; apply map_ext_in; intros y Hy.
    unfold P; rewrite (unshift_cadd B a L y Ha Hy); reflexivity.
Qed.

Lemma ktshape_ktmap w t : forall bl B, ktshape w t -> ktshape w (ktmap bl B t).
Proof.
  revert w; induction t as [x|a x l IHl r IHr]; intros w bl B Hw; [exact Hw|].
  cbn [ktmap]; destruct (bempty _); [exact Hw|].
  destruct Hw as [w' [-> [Hl Hr]]]; exists w'; split; [reflexivity|].
  split; apply ktshape_ktrebase; [apply IHl, Hl|apply IHr, Hr].
Qed.

Lemma kshape_kweights_kmap s : forall bl B,
  (kshape s -> kshape (kmap bl B s)) /\ kweights (kmap bl B s) = kweights s.
Proof.
  induction s as [|a w t s' IH]; intros bl B; [split; [exact (fun H => H)|reflexivity]|].
  cbn [kmap]; destruct (bempty _); [split; [exact (fun H => H)|reflexivity]|].
  destruct (IH (below bl (cadd B a)) (cadd B a)) as [Hsh Hw].
  split; [|rewrite kweights_kcell, Hw; reflexivity].
  intros [Ht Hs]; unfold kcell; split; [apply ktshape_ktrebase, ktshape_ktmap, Ht|apply kshape_krebase, Hsh, Hs].
Qed.

Theorem kgood_kmap bl B s :
  kgood s -> sound bl (map (unshift B) (klist s)) -> (forall y, In y (klist s) -> Pd (unshift B y)) ->
  kgood (kmap bl B s) /\ klist (kmap bl B s) = map (fun y => G (unshift B y)) (klist s).
Proof.
  intros [Hs [Hsh Hc]] Hsd HP; destruct (kmap_spec s bl B Hs Hsd HP) as [Hs' E].
  destruct (kshape_kweights_kmap s bl B) as [Hsh' Hw].
  split; [|exact E]; split; [exact Hs'|split; [apply Hsh', Hsh|]].
  unfold kcanon in *; rewrite klength_weights, Hw, <- klength_weights; exact Hc.
Qed.

Lemma map_eq_in {A B} (f g : A -> B) (L : list A) : map f L = map g L -> forall y, In y L -> f y = g y.
Proof.
  induction L as [|x L IH]; [intros _ _ []|cbn; intros E y [<-|Hy]]; injection E as E1 E2; [exact E1|].
  apply IH; assumption.
Qed.

Lemma atmap_empty bl B t : atmap bl B t = AEmpty -> t = AEmpty.
Proof.
  destruct t as [|a l o r]; [reflexivity|cbn [atmap]].
  destruct (bempty _); [discriminate|unfold amknode; discriminate].
Qed.

Lemma anonempty_atmap bl B l o r bl' B' :
  anonempty l o r -> anonempty (atmap bl B l) (option_map (F B') o) (atmap bl' B r).
Proof.
  destruct (atmap bl B l) eqn:El, o, (atmap bl' B r) eqn:Er; cbn; try tauto.
  apply atmap_empty in El, Er; subst; cbn; tauto.
Qed.

Theorem atmap_spec t : forall bl B,
  ainv t -> sound bl (map (unshift B) (aelems t)) -> (forall y, In y (aelems t) -> Pd (unshift B y)) ->
  ainv (atmap bl B t)
  /\ forall k, aget k (atmap bl B t) = option_map (fun y => G (unshift B y)) (aget k t).
Proof.
  induction t as [|a l IHl o r IHr]; intros bl B Ht Hs HP; [split; [exact I|reflexivity]|].
  pose proof (ainv_ok _ Ht) as Hok; destruct Ht as [Ha [Hcwf [Hne [Ho [Hl Hr]]]]].
  cbn [aelems] in Ha, Hok |- *; cbn [atmap].
  set (L := aelems l ++ oelems o ++ aelems r) in *.
  assert (HokL : forall y, In y L -> eok y).
  { intros y Hy; apply in_app_or in Hy as [Hy|Hy]; [apply (ainv_ok l Hl _ Hy)|].
    apply in_app_or in Hy as [Hy|Hy]; [destruct o; [destruct Hy as [<-|[]]; exact Ho|destruct Hy]|apply (ainv_ok r Hr _ Hy)]. }
  destruct (bempty (below bl (cadd B a))) eqn:Eb.
  - destruct (moved bl B a L Ha HokL HP Hs Eb) as [E Hann].
    split; [split; [exact Hann|split; [apply cwf_cmap2|split; [exact Hne|split; [exact Ho|split; assumption]]]]|].
    intros k; cbn [aget]; fold (asub k l o r).
    destruct (asub k l o r) as [y|] eqn:Ey; [|reflexivity]; cbn [option_map].
    f_equal; rewrite map_map in E; apply (map_eq_in _ _ _ E), (asub_in _ _ _ _ _ Ey).
  - pose proof (sound_below bl B a L Ha Hs) as Hs2.
    pose proof (Pd_child B a L) as HPc.
    set (bl' := below bl (cadd B a)) in *; set (P := cadd B a) in *.
    destruct (IHl bl' P Hl) as [Hl' El].
    { eapply sound_incl; [|exact Hs2]; intros z Hz; apply in_map_iff in Hz as [y [<- Hy]].
      apply in_map, in_or_app; left; exact Hy. }
    { intros y Hy; apply (HPc y Ha HP); apply in_or_app; left; exact Hy. }
    destruct (IHr bl' P Hr) as [Hr' Er].
    { eapply sound_incl; [|exact Hs2]; intros z Hz; apply in_map_iff in Hz as [y [<- Hy]].
      apply in_map, in_or_app; right; apply in_or_app; right; exact Hy. }
    { intros y Hy; apply (HPc y Ha HP); apply in_or_app; right; apply in_or_app; right; exact Hy. }
    assert (HPo : forall x, o = Some x -> Pd (unshift P x))
      by (intros x ->; apply (HPc x Ha HP); apply in_or_app; right; apply in_or_app; left; left; reflexivity).
    assert (Ho' : ook (option_map (F P) o))
      by (destruct o as [x|]; [cbn; rewrite HF by (exact Ho || exact (HPo x eq_refl));
                               apply HGok; [apply ok_unshift, Ho|exact (HPo x eq_refl)]|exact I]).
    split; [apply ainv_amknode; [assumption|assumption|assumption|apply anonempty_atmap, Hne]|].
    intros k; rewrite aget_amknode by assumption; cbn [aget].
    destruct k as [k|k|]; cbn [asub].
    + rewrite Er; destruct (aget k r) as [y|] eqn:Ey; [|reflexivity]; cbn [option_map]; unfold P.
      rewrite (unshift_cadd B a L y Ha); [reflexivity|].
      apply in_or_app; right; apply in_or_app; right; apply (aget_in _ _ _ Ey).
    + rewrite El; destruct (aget k l) as [y|] eqn:Ey; [|reflexivity]; cbn [option_map]; unfold P.
      rewrite (unshift_cadd B a L y Ha); [reflexivity|].
      apply in_or_app; left; apply (aget_in _ _ _ Ey).
    + destruct o as [x|]; [|reflexivity]; cbn [option_map]; rewrite HF by (exact Ho || exact (HPo x eq_refl)); unfold P.
      rewrite (unshift_cadd B a L x Ha); [reflexivity|].
      apply in_or_app; right; apply in_or_app; left; left; reflexivity.
Qed.

(** Entries the map did not visit were moved: they clear the thresholds. *)
Theorem atvisit_spec t : forall bl B kf k e,
  ainv t -> sound bl (map (unshift B) (aelems t)) ->
  aget k t = Some e -> ~ In (kf k) (atvisit bl B kf t) -> clears (unshift B e).
Proof.
  induction t as [|a l IHl o r IHr]; intros bl B kf k e Ht Hs E Hv; [discriminate|].
  destruct Ht as [Ha [_ [_ [_ [Hl Hr]]]]]; cbn [aelems] in Ha, Hs.
  cbn [aget] in E; fold (asub k l o r) in E.
  destruct (asub k l o r) as [y|] eqn:Ey; [|discriminate]; injection E as <-.
  set (L := aelems l ++ oelems o ++ aelems r) in *.
  rewrite (unshift_cadd B a L y Ha (asub_in _ _ _ _ _ Ey)).
  cbn [atvisit] in Hv; destruct (bempty (below bl (cadd B a))) eqn:Eb.
  - apply (pruned_clears bl B a L Ha Hs Eb), (asub_in _ _ _ _ _ Ey).
  - pose proof (sound_below bl B a L Ha Hs) as Hs2.
    destruct k as [k|k|]; cbn [asub] in Ey.
    + apply (IHr (below bl (cadd B a)) (cadd B a) (fun k => kf (xI k)) k); [exact Hr| |exact Ey|].
      * eapply sound_incl; [|exact Hs2]; intros z Hz; apply in_map_iff in Hz as [w [<- Hw]].
        apply in_map, in_or_app; right; apply in_or_app; right; exact Hw.
      * intro H; apply Hv, in_or_app; right; apply in_or_app; right; exact H.
    + apply (IHl (below bl (cadd B a)) (cadd B a) (fun k => kf (xO k)) k); [exact Hl| |exact Ey|].
      * eapply sound_incl; [|exact Hs2]; intros z Hz; apply in_map_iff in Hz as [w [<- Hw]].
        apply in_map, in_or_app; left; exact Hw.
      * intro H; apply Hv, in_or_app; right; apply in_or_app; left; exact H.
    + subst o; exfalso; apply Hv; left; reflexivity.
Qed.

End Prune.
