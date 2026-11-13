(** * The canonical layered word, by its conditions

    [canonf] puts a layered word in the normal form [LayeredUnique.lnf]
    for the order [Order.gtP], and [canonf_lnf] proves that it does; with
    [LayeredUnique.lw_unique_real], two expressions that mean the same
    have the same canonical word. *)

From Stdlib Require Import Arith List Lia Bool Sorted.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Unique Normal Layered LayeredUnique Order
  Canon Retarget LFree.
Import ListNotations.

Section Bridge.

Variable lenv : list label.
Variable labs : list lexp.
Variable ntm : nat.

Local Notation lden := (lden lenv).

(** Segments of the canonical word: canonical, with variables of the
    labels and terms with the identity payload adjustment. *)
Definition tp1 (t : ntgt) : Prop :=
  match t with NVar h _ => In h labs | NBind u w b => w = WEnd SNil /\ b = None /\ u < ntm end.

Definition sp1 (s : seg) : Prop := sshape lenv labs false s /\ Forall tp1 (stgts s).

Lemma sp1_spure s : sp1 s -> spure lenv labs s.
Proof.
  intros [_ H]; unfold spure; eapply Forall_impl; [|exact H].
  intros [h j|u w b]; cbn; [tauto|intros [-> [-> _]]; exists SNil; split; reflexivity].
Qed.

Lemma sp1_oks s : sp1 s -> oks lenv (tenvT ntm) s.
Proof.
  intros [Hs Ht]; pose proof (sshape_dist lenv labs _ _ Hs) as Hd; clear Hs.
  induction s as [|h ts m r IH] using seg_spine; [exact I|]; destruct Hd as [Hn Hd].
  rewrite stgts_cons, Forall_app in Ht; destruct Ht as [H1 H2].
  split; [exact Hn|split; [|exact (IH H2 Hd)]].
  clear -H1; induction ts as [|t r IH] using tlist_spine; [exact I|]; cbn in H1; inversion H1 as [|? ? Ht Hr]; subst.
  split; [|exact (IH Hr)]; destruct t as [g j|u w b]; [exact I|destruct Ht as [-> [-> Hu]]].
  split; [unfold tenvT; rewrite length_map, length_seq; exact Hu|exact I].
Qed.

Lemma fs_FVar s x : sp1 s ->
  fs lenv s FVar x = match sres lenv s x with inl y => FVar y | inr (u, b, s') => FTerm u b (fun z => fs lenv s' FVar z) end.
Proof. intros H; rewrite (fs_pure lenv labs s FVar x (sp1_spure s H)); reflexivity. Qed.

Lemma sres_pure1 s x : sp1 s -> match sres lenv s x with inl _ => True | inr (u, b, s') => b = None /\ s' = SNil end.
Proof.
  intros [_ Ht]; unfold sres; destruct (sget lenv (v_label x) s) as [[ts m]|] eqn:E; [|exact I].
  destruct (v_index x <? tlen ts) eqn:Ei; [|exact I]; apply Nat.ltb_lt in Ei.
  pose proof (proj1 (Forall_forall _ _) Ht _ (sget_tgts lenv _ _ _ _ E _ (tnth_in _ _ Ei))) as Hp.
  destruct (tnth ts (v_index x)) as [h j|u w b]; [exact I|destruct Hp as [-> [-> _]]; split; reflexivity].
Qed.

(** Two canonical segments with the same results on every variable, once
    renamed, have the same targets. *)
Lemma sres_feq s s' x x' : sp1 s -> sp1 s' ->
  feq (fs lenv s FVar x) (fs lenv s' FVar x') -> sres lenv s x = sres lenv s' x'.
Proof.
  intros H H'; rewrite (fs_FVar s x H), (fs_FVar s' x' H').
  pose proof (sres_pure1 s x H) as P; pose proof (sres_pure1 s' x' H') as P'.
  destruct (sres lenv s x) as [y|[[u b] t]], (sres lenv s' x') as [y'|[[u' b'] t']]; cbn [feq]; try tauto.
  - intros ->; reflexivity.
  - destruct P as [-> ->], P' as [-> ->]; intros [-> _]; reflexivity.
Qed.

Theorem sres_bridge A B C : sp1 A -> sp1 C -> sshape lenv labs false B -> sren labs B ->
  (forall aenv penv, sden lenv (tenvT ntm) aenv penv A
                     = rcompose (sden lenv (tenvT ntm) aenv penv C) (sden lenv (tenvT ntm) aenv penv B)) ->
  forall x, sres lenv A x = sres lenv C (sv lenv B x).
Proof.
  intros HA HC HBs HBr E x.
  assert (OB : oks lenv (tenvT ntm) B).
  { apply sp1_oks; split; [exact HBs|]; unfold sren in HBr; eapply Forall_impl; [|exact HBr].
    intros [h j|]; cbn; tauto. }
  pose proof (lw_adequacy lenv ntm [LS A] [LS B; LS C]
                ltac:(constructor; [exact (sp1_oks A HA)|constructor])
                ltac:(constructor; [exact OB|constructor; [exact (sp1_oks C HC)|constructor]])) as Ad.
  assert (Hw : forall aenv penv, lwden lenv (tenvT ntm) aenv penv [LS A] = lwden lenv (tenvT ntm) aenv penv [LS B; LS C]).
  { intros aenv penv; cbn [lwden]; rewrite !rcompose_identity_l, E; reflexivity. }
  specialize (Ad Hw x); cbn [flw] in Ad; rewrite (fs_ren lenv labs B _ x HBr) in Ad.
  exact (sres_feq A C x (sv lenv B x) HA HC Ad).
Qed.

End Bridge.

Section Build.

Variable lenv : list label.
Variable F : order.
Hypothesis HF : facts_ok lenv F.

Local Notation lden := (lden lenv).

(** ** Segments built from entries *)

(** What an entry [h], [xs], [m] does to [h₍ᵢ₎]. *)
Definition etgt (h : lexp) (xs : list ntgt) (m i : nat) : rvar + tm :=
  if i <? List.length xs then tres lenv (nth i xs (NVar LNone 0)) else inl (mk_rvar (lden h) (i - List.length xs + m)).

Lemma trim_etgt h rx m : forall ry m', trim h rx m = (ry, m') -> forall i, etgt h (rev ry) m' i = etgt h (rev rx) m i.
Proof.
  revert m; induction rx as [|x rx IH]; intros m ry m'; cbn [trim].
  - intros H; injection H as <- <-; reflexivity.
  - destruct x as [h' j0|u w b]; [|intros H; injection H as <- <-; reflexivity].
    destruct m as [|m]; [intros H; injection H as <- <-; reflexivity|].
    destruct (lexp_eqb h' h && Nat.eqb j0 m) eqn:E; [|intros H; injection H as <- <-; reflexivity].
    apply andb_true_iff in E as [E1 E2]; apply lexp_eqb_eq in E1; apply Nat.eqb_eq in E2; subst h' j0.
    intros H i; rewrite (IH _ _ _ H i); unfold etgt; cbn [rev]; rewrite length_app; cbn [List.length].
    destruct (Nat.ltb_spec i (List.length (rev rx))) as [Hi|Hi];
      destruct (Nat.ltb_spec i (List.length (rev rx) + 1)) as [Hi'|Hi'].
    + rewrite app_nth1 by exact Hi; reflexivity.
    + lia.
    + assert (i = List.length (rev rx)) as -> by lia; rewrite nth_middle; cbn [tres]; do 2 f_equal; lia.
    + do 2 f_equal; lia.
Qed.

Lemma sres_sset h ts m s s' : sdist lenv s -> sset F h ts m s = Some s' ->
  forall l i, sres lenv s' (mk_rvar l i) = if label_eqb (lden h) l then etgt h (tl_list ts) m i else sres lenv s (mk_rvar l i).
Proof.
  intros Hd; rewrite sset_unfold; destruct (sdel F h s) as [s0|] eqn:Ed; [|discriminate].
  pose proof (sdel_sound lenv F HF h s s0 Ed) as Hs0.
  assert (Hn : sget lenv (lden h) s0 = None) by (rewrite Hs0, label_eqb_refl; reflexivity).
  destruct (trim h (rev (tl_list ts)) m) as [rts m'] eqn:Et.
  pose proof (trim_etgt h _ _ _ _ Et) as Te; rewrite rev_involutive in Te.
  assert (Hput : forall l i, sres lenv (sput F h (tl_of (rev rts)) m' s0) (mk_rvar l i)
                   = if label_eqb (lden h) l then etgt h (tl_list ts) m i else sres lenv s (mk_rvar l i)).
  { intros l i; destruct (sput_sound lenv F h (tl_of (rev rts)) m' s0 Hn) as [H1 _].
    unfold sres; cbn [v_label v_index]; rewrite H1, Hs0.
    destruct (label_eqb_spec (lden h) l) as [<-|Hne]; [|reflexivity].
    rewrite <- Te; unfold etgt; rewrite tlen_list, tl_list_of, tnth_list, tl_list_of; reflexivity. }
  destruct rts as [|x rts]; [destruct m' as [|m']|]; intros H; injection H as <-; try apply Hput.
  intros l i; unfold sres at 1; cbn [v_label v_index]; rewrite Hs0.
  destruct (label_eqb_spec (lden h) l) as [<-|Hne]; [|reflexivity].
  rewrite <- Te; unfold etgt; cbn; do 2 f_equal; lia.
Qed.

Lemma sbuild_sdist es s : sbuild F es = Some s -> sdist lenv s.
Proof.
  revert s; induction es as [|[h [xs m]] es IH]; intros s; cbn [sbuild].
  - intros H; injection H as <-; exact I.
  - destruct (sbuild F es) as [s0|] eqn:E; [|discriminate]; intros H.
    exact (proj1 (@sset_sound unit lenv [] [] [] F HF 0 (le_0_n _) h (tl_of xs) m s0 s (IH s0 eq_refl) H)).
Qed.

Lemma sres_sbuild es s : sbuild F es = Some s ->
  forall l i, sres lenv s (mk_rvar l i)
              = match find (fun e => label_eqb (lden (fst e)) l) es with
                | Some (h, (xs, m)) => etgt h xs m i
                | None => inl (mk_rvar l i)
                end.
Proof.
  revert s; induction es as [|[h [xs m]] es IH]; intros s; cbn [sbuild find fst].
  - intros H; injection H as <-; reflexivity.
  - destruct (sbuild F es) as [s0|] eqn:E; [|discriminate]; intros H l i.
    rewrite (sres_sset h (tl_of xs) m s0 s (sbuild_sdist es s0 E) H l i), tl_list_of.
    destruct (label_eqb (lden h) l); [reflexivity|apply IH; reflexivity].
Qed.

(** ** Numbering the bound variables a segment uses *)

(** The positions of the bound targets of a list, from [i]. *)
Fixpoint bpos (xs : list ntgt) (i : nat) : list (nat * nat) :=
  match xs with
  | [] => []
  | NVar LNone j :: r => (i, j) :: bpos r (S i)
  | _ :: r => bpos r (S i)
  end.

Definition rn_bl (es : list (lexp * tlist * nat)) : list nat := flat_map (fun e => map snd (bpos (tl_list (snd (fst e))) 0)) es.
Definition rn_M (mb : nat) (bl : list nat) : nat := fold_right (fun j acc => Nat.max (Datatypes.S j) acc) mb bl.
Definition rn_ord (bl : list nat) (mb M : nat) : list nat := nodup_nat (bl ++ seq mb (M - mb)) [].
Definition rn_g (M : nat) (ord : list nat) (j : nat) : nat := if j <? M then index_of j ord 0 else j - M + List.length ord.
Definition rn_gt (M : nat) (ord : list nat) (t : ntgt) : ntgt :=
  match t with NVar LNone j => NVar LNone (rn_g M ord j) | _ => t end.
Definition rn_ent (mb M : nat) (ord : list nat) (e : lexp * tlist * nat) : lexp * (list ntgt * nat) :=
  match fst (fst e) with
  | LNone => (LNone, (map (rn_gt M ord) (tl_list (snd (fst e)) ++ map (NVar LNone) (seq mb (M - mb))), List.length ord))
  | h => (h, (map (rn_gt M ord) (tl_list (snd (fst e))), snd e))
  end.

Lemma rn_ent_lab mb M ord e : fst (rn_ent mb M ord e) = fst (fst e).
Proof. unfold rn_ent; destruct (fst (fst e)); reflexivity. Qed.

Definition rn_es (es : list (lexp * tlist * nat)) (mb M : nat) (ord : list nat) : list (lexp * (list ntgt * nat)) :=
  map (rn_ent mb M ord) es
  ++ (if existsb (fun e => lexp_eqb (fst (fst e)) LNone) es then []
      else [(LNone, (map (rn_gt M ord) (map (NVar LNone) (seq mb (M - mb))), List.length ord))]).

(** [renum1 S]: [S] as [S''] followed by [io], a renaming of bound
    variables; [S''] uses every bound variable, numbered in the order of
    the first input sent to it. *)
Definition renum1 (S : seg) : option (seg * seg) :=
  let es := ents S in
  let '(tsb, mb) := bent F S in
  let bl := rn_bl es in
  let M := rn_M mb bl in
  let ord := rn_ord bl mb M in
  match sbuild F (rn_es es mb M ord), sbuild F [(LNone, (map (NVar LNone) ord, M))] with
  | Some S'', Some io => Some (S'', io)
  | _, _ => None
  end.

End Build.

Section RenumSound.

Variable lenv : list label.
Variable labs : list lexp.
Variable ntm : nat.
Variable F : order.
Hypothesis HF : facts_ok lenv F.

Local Notation lden := (lden lenv).
Local Notation sres := (sres lenv).
Local Notation etgt := (etgt lenv).

Lemma sres_ents s l i :
  sres s (mk_rvar l i) = match find (fun e => label_eqb (lden (fst (fst e))) l) (ents s) with
                         | Some (h, ts, m) => etgt h (tl_list ts) m i
                         | None => inl (mk_rvar l i)
                         end.
Proof.
  induction s as [|h ts m r IH] using seg_spine; [reflexivity|].
  unfold sres in *; cbn [v_label v_index Normalise.sget ents find fst] in *.
  destruct (label_eqb (lden h) l) eqn:E; [|exact IH].
  unfold etgt; apply label_eqb_eq in E; subst l; rewrite tlen_list, tnth_list; reflexivity.
Qed.

Lemma find_map_lab {A B} (f : A -> B) (la : A -> lexp) (lb : B -> lexp) (es : list A) l :
  (forall e, lb (f e) = la e) ->
  find (fun e => label_eqb (lden (lb e)) l) (map f es) = option_map f (find (fun e => label_eqb (lden (la e)) l) es).
Proof.
  intros H; induction es as [|e es IH]; [reflexivity|]; cbn [map find]; rewrite H.
  destruct (label_eqb (lden (la e)) l); [reflexivity|exact IH].
Qed.

Lemma find_app_none {A} (p : A -> bool) a b : find p a = None -> find p (a ++ b) = find p b.
Proof. induction a as [|x a IH]; [reflexivity|]; cbn; destruct (p x); [discriminate|exact IH]. Qed.

Lemma find_app_some {A} (p : A -> bool) a b x : find p a = Some x -> find p (a ++ b) = Some x.
Proof. induction a as [|y a IH]; [discriminate|]; cbn; destruct (p y); [exact (fun H => H)|exact IH]. Qed.

Lemma bpos_in xs : forall i0 i j, nth i xs (NVar LNone 0) = NVar LNone j -> i < List.length xs -> In (i0 + i, j) (bpos xs i0).
Proof.
  induction xs as [|x xs IH]; intros i0 i j E Hi; [cbn in Hi; lia|].
  destruct i as [|i]; cbn [nth] in E.
  - subst x; cbn; left; f_equal; lia.
  - replace (i0 + S i) with (S i0 + i) by lia; destruct x as [[|?|?] ?|]; cbn [bpos]; try right;
      apply IH; [exact E|cbn in Hi; lia|exact E|cbn in Hi; lia|exact E|cbn in Hi; lia|exact E|cbn in Hi; lia].
Qed.

Lemma bpos_lt xs : forall i0 i j, In (i, j) (bpos xs i0) -> i0 <= i < i0 + List.length xs /\ nth (i - i0) xs (NVar LNone 0) = NVar LNone j.
Proof.
  induction xs as [|x xs IH]; intros i0 i j; cbn [bpos]; [intros []|].
  assert (Rec : forall H : In (i, j) (bpos xs (S i0)), i0 <= i < i0 + List.length (x :: xs) /\ nth (i - i0) (x :: xs) (NVar LNone 0) = NVar LNone j).
  { intros H; destruct (IH _ _ _ H) as [Hi E]; cbn [List.length]; split; [lia|].
    replace (i - i0) with (S (i - S i0)) by lia; exact E. }
  destruct x as [[|?|?] k|]; [intros [E|H]|exact Rec|exact Rec|exact Rec]; [|exact (Rec H)].
  injection E as <- <-; cbn; split; [lia|rewrite Nat.sub_diag; reflexivity].
Qed.

Lemma bent_find s :
  bent F s = match find (fun e => label_eqb (lden (fst (fst e))) None) (ents s) with
             | Some (_, ts, m) => (ts, m)
             | None => (TNil, 0)
             end.
Proof.
  unfold bent; rewrite (sfind_none lenv F HF s).
  induction s as [|h ts m r IH] using seg_spine; [reflexivity|]; cbn [Normalise.sget ents find fst].
  destruct (label_eqb (lden h) None); [reflexivity|exact IH].
Qed.

Lemma find_some {A} (p : A -> bool) l e : find p l = Some e -> p e = true /\ In e l.
Proof.
  induction l as [|x l IH]; cbn; [discriminate|]; destruct (p x) eqn:E.
  - intros H; injection H as <-; split; [exact E|left; reflexivity].
  - intros H; destruct (IH H) as [H1 H2]; split; [exact H1|right; exact H2].
Qed.

Lemma find_none {A} (p : A -> bool) l e : find p l = None -> In e l -> p e = false.
Proof.
  induction l as [|x l IH]; cbn; [intros _ []|]; destruct (p x) eqn:E; [discriminate|].
  intros H [<-|Hin]; [exact E|exact (IH H Hin)].
Qed.

Lemma mem_in x l : mem x l = true <-> In x l.
Proof.
  unfold mem; rewrite existsb_exists; split.
  - intros [y [Hy E]]; apply Nat.eqb_eq in E; subst; exact Hy.
  - intros H; exists x; split; [exact H|apply Nat.eqb_refl].
Qed.

Lemma nodup_nat_spec l : forall seen x, In x (nodup_nat l seen) <-> In x l /\ ~ In x seen.
Proof.
  induction l as [|y l IH]; intros seen x; cbn [nodup_nat]; [cbn; tauto|].
  destruct (mem y seen) eqn:E.
  - rewrite IH; apply mem_in in E; cbn [In]; split; [tauto|intros [[<-|H] Hs]; [contradiction|tauto]].
  - cbn [In]; rewrite IH; cbn [In]; assert (~ In y seen) by (intros H; apply mem_in in H; congruence).
    split; [intros [<-|[H1 H2]]; [tauto|split; tauto]|].
    intros [[<-|H1] H2]; [left; reflexivity|].
    destruct (Nat.eq_dec y x) as [->|Hne]; [left; reflexivity|right; split; [exact H1|intros [E'|E']; [exact (Hne E')|exact (H2 E')]]].
Qed.

Lemma nodup_nat_nodup l : forall seen, NoDup (nodup_nat l seen).
Proof.
  induction l as [|y l IH]; intros seen; cbn [nodup_nat]; [constructor|].
  destruct (mem y seen); [apply IH|constructor; [|apply IH]].
  rewrite nodup_nat_spec; cbn; tauto.
Qed.

Lemma index_of_nth x l : In x l -> nth (index_of x l 0) l 0 = x /\ index_of x l 0 < List.length l.
Proof.
  intros H; apply mem_in in H; destruct (index_of_spec x l H 0) as [_ [H2 H3]]; rewrite Nat.sub_0_r in H3.
  split; [exact H3|lia].
Qed.

Lemma index_of_go x l : forall k, index_of x l k = k + index_of x l 0.
Proof.
  induction l as [|y l IH]; intros k; cbn [index_of]; [lia|].
  destruct (Nat.eqb x y); [lia|rewrite (IH (S k)), (IH 1); lia].
Qed.

Lemma nth_index_of l i : NoDup l -> i < List.length l -> index_of (nth i l 0) l 0 = i.
Proof.
  revert i; induction l as [|y l IH]; intros i Hd Hi; [cbn in Hi; lia|]; inversion Hd as [|? ? Hn Hd']; subst.
  destruct i as [|i]; cbn [nth index_of]; [rewrite Nat.eqb_refl; reflexivity|].
  destruct (Nat.eqb_spec (nth i l 0) y) as [E|_].
  - exfalso; apply Hn; rewrite <- E; apply nth_In; cbn in Hi; lia.
  - rewrite index_of_go, IH; [lia|exact Hd'|cbn in Hi; lia].
Qed.

Lemma rn_M_ge mb bl : mb <= rn_M mb bl /\ forall j, In j bl -> j < rn_M mb bl.
Proof.
  induction bl as [|j bl IH]; cbn [rn_M fold_right]; [split; [lia|intros j []]|].
  fold (rn_M mb bl); destruct IH as [H1 H2]; split; [lia|intros k [<-|Hk]; [lia|pose proof (H2 k Hk); lia]].
Qed.

Lemma io_sres ord M io : sbuild F [(LNone, (map (NVar LNone) ord, M))] = Some io ->
  forall l k, sres io (mk_rvar l k)
              = inl (match l with
                     | None => mk_rvar None (if k <? List.length ord then nth k ord 0 else k - List.length ord + M)
                     | Some _ => mk_rvar l k
                     end).
Proof.
  intros E l k; rewrite (sres_sbuild lenv F HF _ _ E l k); cbn [find fst Normalise.lden].
  destruct l as [x|]; cbn [label_eqb]; [reflexivity|].
  unfold etgt; rewrite length_map; destruct (k <? List.length ord) eqn:Ek; [|reflexivity].
  change (NVar LNone 0) with ((NVar LNone) 0); rewrite (map_nth (NVar LNone)); reflexivity.
Qed.

Lemma nth_map_gt M ord xs i : i < List.length xs ->
  nth i (map (rn_gt M ord) xs) (NVar LNone 0) = rn_gt M ord (nth i xs (NVar LNone 0)).
Proof.
  intros Hi; rewrite (nth_indep (map (rn_gt M ord) xs) (NVar LNone 0) (rn_gt M ord (NVar LNone 0))) by (rewrite length_map; exact Hi).
  apply map_nth.
Qed.

Theorem renum1_comp S S'' io : renum1 F S = Some (S'', io) ->
  forall x, sres S x = match sres S'' x with inl y => sres io y | r => r end.
Proof.
  unfold renum1; destruct (bent F S) as [tsb mb] eqn:Eb; cbv zeta.
  set (es := ents S); set (bl := rn_bl es); set (M := rn_M mb bl); set (ord := rn_ord bl mb M).
  destruct (sbuild F (rn_es es mb M ord)) as [S0|] eqn:E1; [|discriminate].
  destruct (sbuild F [(LNone, (map (NVar LNone) ord, M))]) as [io0|] eqn:E2; [|discriminate].
  intros H; injection H as <- <-.
  pose proof (io_sres ord M io0 E2) as Hio.
  destruct (rn_M_ge mb bl) as [HM HbM]; fold M in HM, HbM.
  assert (Hord : forall j, In j bl \/ (mb <= j < M) -> In j ord /\ j < M).
  { intros j Hj; unfold ord, rn_ord; rewrite nodup_nat_spec, in_app_iff, in_seq.
    destruct Hj as [Hj|Hj]; [pose proof (HbM j Hj); split; [split; [left; exact Hj|intros []]|lia]|].
    split; [split; [right; lia|intros []]|lia]. }
  set (n := List.length ord).
  assert (Gb : forall j, In j bl \/ (mb <= j < M) -> sres io0 (mk_rvar None (rn_g M ord j)) = inl (mk_rvar None j)).
  { intros j Hj; destruct (Hord j Hj) as [Hin Hlt]; rewrite Hio; unfold rn_g.
    rewrite (proj2 (Nat.ltb_lt _ _) Hlt); destruct (index_of_nth j ord Hin) as [En Hi].
    rewrite (proj2 (Nat.ltb_lt _ _) Hi), En; reflexivity. }
  (* a target of an entry, renamed *)
  assert (Tg : forall h ts m i, In (h, ts, m) es -> i < tlen ts ->
                 match tres lenv (rn_gt M ord (nth i (tl_list ts) (NVar LNone 0))) with inl y => sres io0 y | r => r end
                 = tres lenv (nth i (tl_list ts) (NVar LNone 0))).
  { intros h ts m i Hin Hi; destruct (nth i (tl_list ts) (NVar LNone 0)) as [[|x|x] j|u w b] eqn:Et; cbn [rn_gt tres];
      [|rewrite Hio; reflexivity|rewrite Hio; reflexivity|reflexivity].
    cbn [Normalise.lden]; rewrite Gb; [reflexivity|left].
    unfold bl, rn_bl; apply in_flat_map; exists (h, ts, m); split; [exact Hin|cbn [fst snd]].
    apply (in_map snd (bpos (tl_list ts) 0) (i, j)); rewrite tlen_list in Hi; exact (bpos_in _ 0 i j Et Hi). }
  intros [l i]; rewrite (sres_sbuild lenv F HF _ _ E1 l i), sres_ents; fold es.
  unfold rn_es; destruct (find (fun e => label_eqb (lden (fst (fst e))) l) es) as [[[h ts] m]|] eqn:Ef.
  - destruct (find_some _ _ _ Ef) as [El Hin]; cbn [fst] in El; apply label_eqb_eq in El; subst l.
    rewrite (find_app_some _ _ _ (rn_ent mb M ord (h, ts, m))
              (eq_trans (find_map_lab (rn_ent mb M ord) (fun e => fst (fst e)) fst es (lden h) (rn_ent_lab mb M ord))
                        (f_equal (option_map (rn_ent mb M ord)) Ef))).
    unfold rn_ent; cbn [fst snd].
    destruct h as [|x|x].
    + (* the bound entry *)
      assert (Ebent : (tsb, mb) = (ts, m)).
      { rewrite <- Eb, bent_find; fold es; cbn [Normalise.lden] in Ef; rewrite Ef; reflexivity. }
      injection Ebent as <- <-; symmetry.
      unfold etgt; rewrite length_map, length_app, length_map, length_seq; cbn [Normalise.lden].
      destruct (Nat.ltb_spec i (List.length (tl_list tsb))) as [Hi|Hi].
      * rewrite (proj2 (Nat.ltb_lt _ _)) by lia.
        rewrite nth_map_gt by (rewrite length_app, length_map, length_seq; lia).
        rewrite app_nth1 by exact Hi.
        apply (Tg LNone tsb mb i Hin); rewrite tlen_list; exact Hi.
      * destruct (Nat.ltb_spec i (List.length (tl_list tsb) + (M - mb))) as [Hi'|Hi'].
        -- rewrite nth_map_gt by (rewrite length_app, length_map, length_seq; lia).
           rewrite app_nth2 by exact Hi.
           change (NVar LNone 0) with ((NVar LNone) 0); rewrite (map_nth (NVar LNone)), seq_nth by (rewrite ?length_seq; lia).
           cbn [rn_gt tres Normalise.lden].
           rewrite Gb by (right; lia); do 2 f_equal; lia.
        -- rewrite Hio; fold n; rewrite (proj2 (Nat.ltb_ge _ _)) by lia; do 2 f_equal; lia.
    + symmetry; unfold etgt; rewrite length_map.
      destruct (Nat.ltb_spec i (List.length (tl_list ts))) as [Hi|Hi].
      * rewrite nth_map_gt by exact Hi.
        apply (Tg _ ts m i Hin); rewrite tlen_list; exact Hi.
      * rewrite Hio; reflexivity.
    + symmetry; unfold etgt; rewrite length_map.
      destruct (Nat.ltb_spec i (List.length (tl_list ts))) as [Hi|Hi].
      * rewrite nth_map_gt by exact Hi.
        apply (Tg _ ts m i Hin); rewrite tlen_list; exact Hi.
      * rewrite Hio; reflexivity.
  - rewrite find_app_none by (rewrite (find_map_lab (rn_ent mb M ord) (fun e => fst (fst e)) fst es l (rn_ent_lab mb M ord)), Ef; reflexivity).
    destruct l as [x|].
    + destruct (existsb _ es); cbn [find fst Normalise.lden label_eqb]; rewrite Hio; reflexivity.
    + assert (Ex : existsb (fun e => lexp_eqb (fst (fst e)) LNone) es = false).
      { apply Bool.not_true_iff_false; intros Hx; apply existsb_exists in Hx as [[[h ts] m] [Hin Hh]].
        cbn [fst] in Hh; apply lexp_eqb_eq in Hh; subst h.
        pose proof (find_none _ _ _ Ef Hin) as Hf; cbn in Hf; discriminate Hf. }
      assert (Ebent : (tsb, mb) = (TNil, 0)) by (rewrite <- Eb, bent_find; fold es; cbn [Normalise.lden] in Ef; rewrite Ef; reflexivity).
      injection Ebent as -> ->.
      rewrite Ex; cbn [app find fst Normalise.lden label_eqb]; symmetry.
      unfold etgt; rewrite !length_map, length_seq.
      destruct (Nat.ltb_spec i (M - 0)) as [Hi|Hi].
      * rewrite nth_map_gt by (rewrite length_map, length_seq; lia).
        change (NVar LNone 0) with ((NVar LNone) 0); rewrite (map_nth (NVar LNone)), seq_nth by lia; cbn [rn_gt tres Normalise.lden].
        rewrite Gb by (right; lia); do 2 f_equal; lia.
      * rewrite Hio; cbn [Normalise.lden]; fold n; rewrite (proj2 (Nat.ltb_ge _ _)) by lia; do 2 f_equal; lia.
Qed.

(** In [nodup_nat L seen], the elements come in the order of their first
    occurrences in [L]. *)
Lemma first_occ L : forall seen i j, i < j < List.length (nodup_nat L seen) ->
  exists p, p < List.length L /\ nth p L 0 = nth i (nodup_nat L seen) 0
            /\ forall q, q < List.length L -> nth q L 0 = nth j (nodup_nat L seen) 0 -> p < q.
Proof.
  induction L as [|x L IH]; intros seen i j Hij; cbn [nodup_nat List.length] in *; [lia|].
  destruct (mem x seen) eqn:Em.
  - destruct (IH seen i j Hij) as [p [Hp [E Hq]]]; exists (S p); split; [lia|split; [exact E|]].
    intros [|q] Hq' Eq; cbn [nth] in Eq.
    + exfalso; apply mem_in in Em.
      assert (Hin : In (nth j (nodup_nat L seen) 0) (nodup_nat L seen)) by (apply nth_In; lia).
      rewrite <- Eq in Hin; apply nodup_nat_spec in Hin as [_ Hs]; exact (Hs Em).
    + specialize (Hq q ltac:(lia) Eq); lia.
  - cbn [List.length] in Hij; destruct i as [|i].
    + exists 0; split; [lia|split; [reflexivity|]].
      intros [|q] Hq Eq; [|lia]; exfalso; cbn [nth] in Eq; destruct j as [|j]; [lia|].
      assert (Hin : In (nth j (nodup_nat L (x :: seen)) 0) (nodup_nat L (x :: seen))) by (apply nth_In; lia).
      rewrite <- Eq in Hin; apply nodup_nat_spec in Hin as [_ Hs]; apply Hs; left; reflexivity.
    + destruct j as [|j]; [lia|].
      destruct (IH (x :: seen) i j ltac:(lia)) as [p [Hp [E Hq]]]; exists (S p); split; [lia|split; [exact E|]].
      intros [|q] Hq' Eq; cbn [nth] in Eq.
      * exfalso; assert (Hin : In (nth j (nodup_nat L (x :: seen)) 0) (nodup_nat L (x :: seen))) by (apply nth_In; lia).
        rewrite <- Eq in Hin; apply nodup_nat_spec in Hin as [_ Hs]; apply Hs; left; reflexivity.
      * specialize (Hq q ltac:(lia) Eq); lia.
Qed.

Lemma SS_app {A} (R : A -> A -> Prop) a b :
  StronglySorted R a -> StronglySorted R b -> (forall x y, In x a -> In y b -> R x y) -> StronglySorted R (a ++ b).
Proof.
  induction a as [|x a IH]; intros Ha Hb H; [exact Hb|]; inversion Ha as [|? ? Ha' Hall]; subst; cbn [app].
  constructor; [apply IH; [exact Ha'|exact Hb|intros u v Hu Hv; apply H; [right; exact Hu|exact Hv]]|].
  apply Forall_app; split; [exact Hall|apply Forall_forall; intros y Hy; apply H; [left; reflexivity|exact Hy]].
Qed.

Lemma bpos_sorted xs : forall i0, StronglySorted (fun p q => fst p < fst q) (bpos xs i0) /\ forall p, In p (bpos xs i0) -> i0 <= fst p.
Proof.
  induction xs as [|x xs IH]; intros i0; cbn [bpos]; [split; [constructor|intros p []]|].
  destruct (IH (S i0)) as [H1 H2].
  assert (Hg : StronglySorted (fun p q => fst p < fst q) (bpos xs (S i0)) /\ forall p, In p (bpos xs (S i0)) -> i0 <= fst p)
    by (split; [exact H1|intros p Hp; pose proof (H2 p Hp); lia]).
  destruct x as [[|?|?] j|]; try exact Hg.
  split; [constructor; [exact H1|apply Forall_forall; intros p Hp; cbn [fst]; pose proof (H2 p Hp); lia]|].
  intros p [<-|Hp]; [cbn; lia|pose proof (H2 p Hp); lia].
Qed.

Lemma ents_sents s : map (fun e => (fst (fst e), tl_list (snd (fst e)), snd e)) (ents s) = sents s.
Proof. induction s as [|h ts m r IH] using seg_spine; [reflexivity|]; cbn; rewrite IH; reflexivity. Qed.

Lemma find_ents_in s e : sdist lenv s -> In e (ents s) -> find (fun e' => label_eqb (lden (fst (fst e'))) (lden (fst (fst e)))) (ents s) = Some e.
Proof.
  induction s as [|h ts m r IH] using seg_spine; cbn [ents]; [intros _ []|]; intros [Hn Hd] [<-|Hin]; cbn [find fst].
  - rewrite label_eqb_refl; reflexivity.
  - destruct (label_eqb_spec (lden h) (lden (fst (fst e)))) as [E|_]; [|exact (IH Hd Hin)].
    exfalso; destruct e as [[h' ts'] m']; cbn [fst] in E.
    pose proof (ents_sget lenv r h' ts' m' Hd Hin) as Eg; rewrite <- E, Hn in Eg; discriminate Eg.
Qed.


Lemma map_add_seq k : forall a, map (fun t => a + t) (seq 0 k) = seq a k.
Proof.
  induction k as [|k IH]; intros a; [reflexivity|]; cbn [seq map]; rewrite Nat.add_0_r; f_equal.
  rewrite <- seq_shift, map_map; rewrite <- (IH (S a)); apply map_ext; intros; lia.
Qed.

Lemma SS_flat_map {A B} (R : B -> B -> Prop) (Rk : A -> A -> Prop) (f : A -> list B) es :
  StronglySorted Rk es -> (forall e, In e es -> StronglySorted R (f e)) ->
  (forall e1 e2, Rk e1 e2 -> forall a b, In a (f e1) -> In b (f e2) -> R a b) ->
  StronglySorted R (flat_map f es).
Proof.
  induction es as [|e es IH]; intros Hs Hf Hx; cbn [flat_map]; [constructor|]; inversion Hs as [|? ? Hs' Hall]; subst.
  apply SS_app; [apply Hf; left; reflexivity|apply IH; [exact Hs'|intros e' He'; apply Hf; right; exact He'|exact Hx]|].
  intros a b Ha Hb; apply in_flat_map in Hb as [e2 [He2 Hb]].
  exact (Hx e e2 (proj1 (Forall_forall _ _) Hall e2 He2) a b Ha Hb).
Qed.

Lemma SS_nth {A} (R : A -> A -> Prop) l : StronglySorted R l -> forall p q d, p < q < List.length l -> R (nth p l d) (nth q l d).
Proof.
  induction l as [|a l IH]; intros Hs p q d Hpq; [cbn in Hpq; lia|].
  inversion Hs as [|? ? Hs' Hall]; subst; destruct p as [|p], q as [|q]; cbn [nth List.length] in *; try lia.
  - apply (proj1 (Forall_forall _ _) Hall), nth_In; lia.
  - apply IH; [exact Hs'|lia].
Qed.

(** The bound variables of [S] are numbered in the order of the first
    input sent to each. *)
Definition srcp (S : seg) : Prop :=
  forall x x' i j, sres S x = inl (mk_rvar None i) -> sres S x' = inl (mk_rvar None j) -> i < j ->
    exists x0, sres S x0 = inl (mk_rvar None i) /\ forall x'', sres S x'' = inl (mk_rvar None j) -> vlt x0 x''.

Theorem renum1_hs S S'' io : sshape lenv labs false S -> renum1 F S = Some (S'', io) ->
  (forall j, exists x, sres S'' x = inl (mk_rvar None j)) /\ srcp S''.
Proof.
  intros Hsh; pose proof (sshape_dist lenv labs _ _ Hsh) as Hd.
  unfold renum1; destruct (bent F S) as [tsb mb] eqn:Eb; cbv zeta.
  set (es := ents S); set (bl := rn_bl es); set (M := rn_M mb bl); set (ord := rn_ord bl mb M).
  destruct (sbuild F (rn_es es mb M ord)) as [S0|] eqn:E1; [|discriminate].
  destruct (sbuild F [(LNone, (map (NVar LNone) ord, M))]) as [io0|] eqn:E2; [|discriminate].
  intros H; injection H as <- <-.
  set (n := List.length ord); set (kk := M - mb); set (lb := List.length (tl_list tsb)).
  set (g := rn_g M ord).
  destruct (rn_M_ge mb bl) as [HM HbM]; fold M in HM, HbM.
  assert (Hnd : NoDup ord) by apply nodup_nat_nodup.
  assert (Hoin : forall o, In o ord <-> In o (bl ++ seq mb kk)).
  { intros o; unfold ord, rn_ord; rewrite nodup_nat_spec; cbn; tauto. }
  assert (HoM : forall o, In o ord -> o < M).
  { intros o Ho; apply Hoin, in_app_iff in Ho as [Ho|Ho]; [exact (HbM o Ho)|apply in_seq in Ho; unfold kk in Ho; lia]. }
  assert (Gin : forall o, In o ord -> g o < n /\ nth (g o) ord 0 = o).
  { intros o Ho; unfold g, rn_g; rewrite (proj2 (Nat.ltb_lt _ _) (HoM o Ho)).
    destruct (index_of_nth o ord Ho) as [E Hi]; split; [exact Hi|exact E]. }
  (* the bound entry *)
  assert (Bent : (exists h0, lden h0 = None /\ find (fun e => label_eqb (lden (fst (fst e))) None) es = Some (h0, tsb, mb))
                 \/ (find (fun e => label_eqb (lden (fst (fst e))) None) es = None /\ tsb = TNil /\ mb = 0)).
  { pose proof (bent_find S) as B; rewrite Eb in B; fold es in B.
    destruct (find _ es) as [[[h0 ts0] m0]|] eqn:Ef; injection B as -> ->; [left|right; auto].
    exists h0; split; [|reflexivity]; destruct (find_some _ _ _ Ef) as [El _]; apply label_eqb_eq in El; exact El. }
  assert (SRb : forall i, sres S0 (mk_rvar None i) = etgt LNone (map (rn_gt M ord) (tl_list tsb ++ map (NVar LNone) (seq mb kk))) n i).
  { intros i; rewrite (sres_sbuild lenv F HF _ _ E1 None i); unfold rn_es.
    destruct Bent as [[h0 [Eh0 Ef]]|[Ef [Et Em]]].
    - rewrite (find_app_some _ _ _ (rn_ent mb M ord (h0, tsb, mb))
                (eq_trans (find_map_lab (rn_ent mb M ord) (fun e => fst (fst e)) fst es None (rn_ent_lab mb M ord))
                          (f_equal (option_map (rn_ent mb M ord)) Ef))).
      apply (lden_none lenv) in Eh0; subst h0; reflexivity.
    - rewrite find_app_none by (rewrite (find_map_lab (rn_ent mb M ord) (fun e => fst (fst e)) fst es None (rn_ent_lab mb M ord)), Ef; reflexivity).
      assert (Ex : existsb (fun e => lexp_eqb (fst (fst e)) LNone) es = false).
      { apply Bool.not_true_iff_false; intros Hx; apply existsb_exists in Hx as [[[h ts] m] [Hin Hh]].
        cbn [fst] in Hh; apply lexp_eqb_eq in Hh; subst h.
        pose proof (find_none _ _ _ Ef Hin) as Hf; cbn in Hf; discriminate Hf. }
      rewrite Ex; cbn [app find fst Normalise.lden label_eqb]; unfold kk; rewrite Et, Em; reflexivity. }
  assert (SRn : forall x i, sres S0 (mk_rvar (Some x) i)
                  = match find (fun e => label_eqb (lden (fst (fst e))) (Some x)) es with
                    | Some (h, ts, m) => etgt h (map (rn_gt M ord) (tl_list ts)) m i
                    | None => inl (mk_rvar (Some x) i)
                    end).
  { intros x i; rewrite (sres_sbuild lenv F HF _ _ E1 (Some x) i); unfold rn_es.
    destruct (find (fun e => label_eqb (lden (fst (fst e))) (Some x)) es) as [[[h ts] m]|] eqn:Ef.
    - rewrite (find_app_some _ _ _ (rn_ent mb M ord (h, ts, m))
                (eq_trans (find_map_lab (rn_ent mb M ord) (fun e => fst (fst e)) fst es (Some x) (rn_ent_lab mb M ord))
                          (f_equal (option_map (rn_ent mb M ord)) Ef))).
      destruct (find_some _ _ _ Ef) as [El _]; cbn [fst] in El; apply label_eqb_eq in El.
      unfold rn_ent; cbn [fst snd]; destruct h; [discriminate El|reflexivity|reflexivity].
    - rewrite find_app_none by (rewrite (find_map_lab (rn_ent mb M ord) (fun e => fst (fst e)) fst es (Some x) (rn_ent_lab mb M ord)), Ef; reflexivity).
      destruct (existsb _ es); reflexivity. }
  set (PX := flat_map (fun e => map (fun ij => (mk_rvar (lden (fst (fst e))) (fst ij), snd ij)) (bpos (tl_list (snd (fst e))) 0)) es
             ++ map (fun t => (mk_rvar None (lb + t), mb + t)) (seq 0 kk)).
  assert (HPL : map snd PX = bl ++ seq mb kk).
  { unfold PX; rewrite map_app, map_map; cbn [snd]; rewrite map_add_seq; f_equal.
    unfold bl, rn_bl; clear; induction es as [|e es IH]; [reflexivity|]; cbn [flat_map]; rewrite map_app, IH, map_map; reflexivity. }
  assert (Gt0 : forall o, rn_gt M ord (NVar LNone o) = NVar LNone (g o)) by reflexivity.
  (* the bound entry, from an entry with the bound label *)
  assert (BE : forall h ts m, In (h, ts, m) es -> lden h = None -> ts = tsb /\ m = mb).
  { intros h ts m Hin Hl; pose proof (find_ents_in S (h, ts, m) Hd Hin) as Ef; cbn [fst] in Ef; rewrite Hl in Ef; fold es in Ef.
    destruct Bent as [[h0 [_ Ef']]|[Ef' _]]; rewrite Ef in Ef'; [injection Ef' as _ <- <-; split; reflexivity|discriminate]. }
  assert (Hmap : forall x o, In (x, o) PX -> sres S0 x = inl (mk_rvar None (g o)) /\ In o ord).
  { intros x o Hin; unfold PX in Hin; apply in_app_or in Hin as [Hin|Hin].
    - apply in_flat_map in Hin as [[[h ts] m] [He Hin]]; apply in_map_iff in Hin as [[i o'] [E Hb]]; cbn [fst snd] in *.
      injection E as <- ->; destruct (bpos_lt _ 0 i o Hb) as [Hi Et]; rewrite Nat.sub_0_r in Et.
      split.
      + destruct (lden h) as [y|] eqn:Eh.
        * rewrite SRn; pose proof (find_ents_in S (h, ts, m) Hd He) as Ef; cbn [fst] in Ef; rewrite Eh in Ef; fold es in Ef; rewrite Ef.
          unfold etgt; rewrite length_map, (proj2 (Nat.ltb_lt _ _)) by lia; rewrite nth_map_gt by lia; rewrite Et; reflexivity.
        * destruct (BE h ts m He Eh) as [-> ->]; rewrite SRb; unfold etgt.
          rewrite length_map, length_app, (proj2 (Nat.ltb_lt _ _)) by lia.
          rewrite nth_map_gt by (rewrite length_app; lia); rewrite app_nth1 by lia; rewrite Et; reflexivity.
      + apply Hoin, in_or_app; left; unfold bl, rn_bl; apply in_flat_map; exists (h, ts, m); split; [exact He|].
        apply (in_map snd _ (i, o)), Hb.
    - apply in_map_iff in Hin as [tt [E Ht]]; injection E as <- <-; apply in_seq in Ht; split.
      + rewrite SRb; unfold etgt; rewrite length_map, length_app, length_map, length_seq.
        rewrite (proj2 (Nat.ltb_lt _ _)) by lia; rewrite nth_map_gt by (rewrite length_app, length_map, length_seq; lia).
        rewrite app_nth2 by (unfold lb; lia); fold lb; replace (lb + tt - lb) with tt by lia.
        change (NVar LNone 0) with ((NVar LNone) 0); rewrite (map_nth (NVar LNone)), seq_nth by lia; reflexivity.
      + apply Hoin, in_or_app; right; apply in_seq; lia. }
  (* where a bound target comes from *)
  assert (Hback : forall x k, sres S0 x = inl (mk_rvar None k) ->
                    (exists o, In (x, o) PX /\ k = g o) \/ (n <= k /\ x = mk_rvar None (lb + kk + (k - n)))).
  { intros [[y|] i] k; [rewrite SRn|rewrite SRb].
    - destruct (find (fun e => label_eqb (lden (fst (fst e))) (Some y)) es) as [[[h ts] m]|] eqn:Ef; [|discriminate].
      destruct (find_some _ _ _ Ef) as [El He]; cbn [fst] in El; apply label_eqb_eq in El.
      unfold etgt; rewrite length_map; destruct (Nat.ltb_spec i (List.length (tl_list ts))) as [Hi|Hi]; [|rewrite El; discriminate].
      rewrite nth_map_gt by exact Hi.
      destruct (nth i (tl_list ts) (NVar LNone 0)) as [[|?|?] o|] eqn:Et; cbn [rn_gt tres]; try (rewrite ?El; discriminate).
      cbn [Normalise.lden]; intros E; injection E as <-; left; exists o; split; [|reflexivity].
      unfold PX; apply in_or_app; left; apply in_flat_map; exists (h, ts, m); split; [exact He|].
      apply in_map_iff; exists (i, o); cbn [fst snd]; rewrite El; split; [reflexivity|].
      exact (bpos_in _ 0 i o Et Hi).
    - unfold etgt; rewrite length_map, length_app, length_map, length_seq; fold lb.
      destruct (Nat.ltb_spec i (lb + kk)) as [Hi|Hi].
      + rewrite nth_map_gt by (rewrite length_app, length_map, length_seq; lia).
        destruct (Nat.ltb_spec i lb) as [Hl|Hl].
        * rewrite app_nth1 by exact Hl.
          destruct (nth i (tl_list tsb) (NVar LNone 0)) as [[|?|?] o|] eqn:Et; cbn [rn_gt tres]; try discriminate.
          cbn [Normalise.lden]; intros E; injection E as <-; left; exists o; split; [|reflexivity].
          destruct Bent as [[h0 [Eh0 Ef]]|[_ [Et0 _]]]; [|exfalso; unfold lb in Hl; rewrite Et0 in Hl; cbn in Hl; lia].
          destruct (find_some _ _ _ Ef) as [_ He].
          unfold PX; apply in_or_app; left; apply in_flat_map; exists (h0, tsb, mb); split; [exact He|].
          apply in_map_iff; exists (i, o); cbn [fst snd]; rewrite Eh0; split; [reflexivity|exact (bpos_in _ 0 i o Et Hl)].
        * rewrite app_nth2 by exact Hl; change (NVar LNone 0) with ((NVar LNone) 0).
          rewrite (map_nth (NVar LNone)), seq_nth by lia; cbn [rn_gt tres Normalise.lden].
          intros E; injection E as <-; left; exists (mb + (i - lb)); split; [|reflexivity].
          unfold PX; apply in_or_app; right; apply in_map_iff; exists (i - lb); split; [f_equal; f_equal; lia|apply in_seq; lia].
      + cbn [Normalise.lden]; intros E; injection E as <-; right; split; [lia|f_equal; lia]. }
  (* the inputs that give bound targets, in order *)
  assert (Hso : StronglySorted (fun p q => vlt (fst p) (fst q)) PX).
  { assert (Hes : StronglySorted (fun e e' => olabel_lt (lden (fst (fst e))) (lden (fst (fst e')))) es).
    { destruct Hsh as [Hss _]; rewrite <- ents_sents in Hss; fold es in Hss; clear -Hss.
      induction es as [|e es IH]; [constructor|]; inversion Hss as [|? ? Hs' Hall]; subst.
      constructor; [exact (IH Hs')|]; rewrite Forall_map in Hall; eapply Forall_impl; [|exact Hall].
      intros [[h ts] m]; destruct e as [[h' ts'] m']; cbn; tauto. }
    unfold PX; apply SS_app.
    - apply (SS_flat_map _ _ _ es Hes).
      + intros [[h ts] m] _; cbn [fst snd]; destruct (bpos_sorted (tl_list ts) 0) as [Hb _]; clear -Hb.
        induction (bpos (tl_list ts) 0) as [|p l IH]; [constructor|]; inversion Hb as [|? ? Hb' Hall]; subst.
        cbn [map]; constructor; [exact (IH Hb')|]; rewrite Forall_map; eapply Forall_impl; [|exact Hall].
        intros q Hq; right; cbn; split; [reflexivity|exact Hq].
      + intros e1 e2 Hlt a b Ha Hb; apply in_map_iff in Ha as [p [<- _]]; apply in_map_iff in Hb as [q [<- _]].
        left; exact Hlt.
    - assert (Gen : forall a k0, StronglySorted (fun p q => vlt (fst p) (fst q))
                                  (map (fun t0 => (mk_rvar None (lb + t0), mb + t0)) (seq a k0))).
      { intros a k0; revert a; induction k0 as [|k0 IH]; intros a; [constructor|]; cbn [seq map].
        constructor; [apply IH|]; rewrite Forall_map, Forall_forall; intros j Hj; apply in_seq in Hj.
        right; cbn; split; [reflexivity|lia]. }
      apply Gen.
    - intros p q Hp Hq; apply in_flat_map in Hp as [[[h ts] m] [He Hp]]; apply in_map_iff in Hp as [[i o] [<- Hb]].
      apply in_map_iff in Hq as [tt [<- Ht]]; cbn [fst snd].
      destruct (lden h) as [y|] eqn:Eh; [left; reflexivity|].
      destruct (BE h ts m He Eh) as [-> _]; destruct (bpos_lt _ 0 i o Hb) as [Hi _].
      right; cbn [v_label v_index]; cbn [fst snd] in Hi; split; [reflexivity|unfold lb; lia]. }
  assert (SSnth : forall p q d, p < q < List.length PX -> vlt (fst (nth p PX d)) (fst (nth q PX d)))
    by exact (SS_nth (fun p q => vlt (fst p) (fst q)) PX Hso).
  assert (Dflt : forall k, n <= k -> sres S0 (mk_rvar None (lb + kk + (k - n))) = inl (mk_rvar None k)).
  { intros k Hk; rewrite SRb; unfold etgt; rewrite length_map, length_app, length_map, length_seq; fold lb.
    rewrite (proj2 (Nat.ltb_ge _ _)) by lia; do 2 f_equal; lia. }
  assert (PXlt : forall x o e, In (x, o) PX -> vlt x (mk_rvar None (lb + kk + e))).
  { intros x o e Hin; unfold PX in Hin; apply in_app_or in Hin as [Hin|Hin].
    - apply in_flat_map in Hin as [[[h ts] m] [He Hp]]; apply in_map_iff in Hp as [[i o'] [E Hb]]; injection E as <- _.
      cbn [fst snd]; destruct (lden h) as [y|] eqn:Eh; [left; reflexivity|].
      destruct (BE h ts m He Eh) as [-> _]; destruct (bpos_lt _ 0 i o' Hb) as [Hi _]; cbn [fst snd] in Hi.
      right; cbn [v_label v_index]; split; [reflexivity|unfold lb; lia].
    - apply in_map_iff in Hin as [tt [E Ht]]; injection E as <- _; apply in_seq in Ht.
      right; cbn [v_label v_index]; split; [reflexivity|lia]. }
  assert (Gn : forall o, In o ord -> forall k, k < n -> g o = k -> o = nth k ord 0).
  { intros o Ho k Hk Eg; rewrite <- Eg; symmetry; exact (proj2 (Gin o Ho)). }
  assert (InPX : forall k, k < n -> exists x, In (x, nth k ord 0) PX).
  { intros k Hk; assert (Hin : In (nth k ord 0) (map snd PX)) by (rewrite HPL; apply Hoin, nth_In; exact Hk).
    apply in_map_iff in Hin as [[x o] [Eo Hin]]; cbn [snd] in Eo; subst o; exists x; exact Hin. }
  assert (Gk : forall k, k < n -> g (nth k ord 0) = k).
  { intros k Hk; unfold g, rn_g; rewrite (proj2 (Nat.ltb_lt _ _)) by (apply HoM, nth_In; exact Hk).
    apply nth_index_of; [exact Hnd|exact Hk]. }
  split.
  - intros k; destruct (Nat.lt_ge_cases k n) as [Hk|Hk].
    + destruct (InPX k Hk) as [x Hx]; exists x; rewrite (proj1 (Hmap x _ Hx)), Gk by exact Hk; reflexivity.
    + exists (mk_rvar None (lb + kk + (k - n))); exact (Dflt k Hk).
  - intros x x' i j Hx Hx' Hij.
    assert (Hj : forall x'', sres S0 x'' = inl (mk_rvar None j) ->
                   (j < n /\ exists o, In (x'', o) PX /\ o = nth j ord 0) \/ (n <= j /\ x'' = mk_rvar None (lb + kk + (j - n)))).
    { intros x'' E; destruct (Hback x'' j E) as [[o [Hin Eo]]|[Hn Ex]]; [left|right; auto].
      destruct (Hmap x'' o Hin) as [_ Ho]; destruct (Gin o Ho) as [Hlt _]; rewrite <- Eo in Hlt.
      split; [exact Hlt|exists o; split; [exact Hin|exact (Gn o Ho j Hlt (eq_sym Eo))]]. }
    destruct (Nat.lt_ge_cases i n) as [Hi|Hi].
    + destruct (Nat.lt_ge_cases j n) as [Hjn|Hjn].
      * assert (Hord : ord = nodup_nat (bl ++ seq mb kk) []) by reflexivity.
        destruct (first_occ (bl ++ seq mb kk) [] i j ltac:(rewrite <- Hord; fold n; lia)) as [p [Hp [Ep Hq]]].
        rewrite <- Hord in Ep, Hq; rewrite <- HPL in Hp, Ep, Hq; rewrite length_map in Hp.
        set (d := (mk_rvar None 0, 0)).
        assert (Ed : forall q, q < List.length PX -> nth q (map snd PX) 0 = snd (nth q PX d)).
        { intros q Hq'; rewrite (nth_indep _ _ (snd d)) by (rewrite length_map; exact Hq'); apply map_nth. }
        exists (fst (nth p PX d)); split.
        -- assert (Hin : In (fst (nth p PX d), nth i ord 0) PX).
           { rewrite Ed in Ep by exact Hp; rewrite <- Ep, <- surjective_pairing; apply nth_In, Hp. }
           rewrite (proj1 (Hmap _ _ Hin)), Gk by exact Hi; reflexivity.
        -- intros x'' E''; destruct (Hj x'' E'') as [[_ [o [Hin Eo]]]|[Hn _]]; [|lia].
           apply In_nth with (d := d) in Hin as [q [Hq' Eq]].
           assert (Hpq : p < q) by (apply Hq; [rewrite length_map; exact Hq'|rewrite Ed, Eq by exact Hq'; exact Eo]).
           pose proof (SSnth p q d (conj Hpq Hq')) as V; rewrite Eq in V; exact V.
      * destruct (InPX i Hi) as [x0 Hx0]; exists x0; split; [rewrite (proj1 (Hmap _ _ Hx0)), Gk by exact Hi; reflexivity|].
        intros x'' E''; destruct (Hj x'' E'') as [[Hlt _]|[_ ->]]; [lia|exact (PXlt x0 _ _ Hx0)].
    + exists (mk_rvar None (lb + kk + (i - n))); split; [exact (Dflt i Hi)|].
      intros x'' E''; destruct (Hj x'' E'') as [[Hlt _]|[_ ->]]; [lia|].
      right; cbn [v_label v_index]; split; [reflexivity|lia].
Qed.

Lemma ents_stgts s h ts m t : In (h, ts, m) (ents s) -> In t (tl_list ts) -> In t (stgts s).
Proof.
  induction s as [|h' ts' m' r IH] using seg_spine; cbn [ents]; [intros []|]; intros [E|Hin] Ht; rewrite stgts_cons;
    apply in_or_app; [injection E as -> -> ->; left; exact Ht|right; exact (IH Hin Ht)].
Qed.

Theorem renum1_shape S S'' io : In LNone labs -> sp1 lenv labs ntm S -> renum1 F S = Some (S'', io) ->
  sp1 lenv labs ntm S'' /\ sshape lenv labs false io /\ sren labs io.
Proof.
  intros HN [Hsh Ht]; unfold renum1; destruct (bent F S) as [tsb mb] eqn:Eb; cbv zeta.
  set (es := ents S); set (bl := rn_bl es); set (M := rn_M mb bl); set (ord := rn_ord bl mb M).
  destruct (sbuild F (rn_es es mb M ord)) as [S0|] eqn:E1; [|discriminate].
  destruct (sbuild F [(LNone, (map (NVar LNone) ord, M))]) as [io0|] eqn:E2; [|discriminate].
  intros H; injection H as <- <-.
  assert (Hlab : forall h ts m, In (h, ts, m) es -> In h labs).
  { intros h ts m Hin; apply (sshape_labs lenv labs false S Hsh h (tl_list ts) m).
    rewrite <- ents_sents; apply (in_map (fun e => (fst (fst e), tl_list (snd (fst e)), snd e)) _ _ Hin). }
  assert (Htp : forall h ts m t, In (h, ts, m) es -> In t (tl_list ts) -> tp1 labs ntm t).
  { intros h ts m t0 He H0; exact (proj1 (Forall_forall _ _) Ht t0 (ents_stgts S h ts m t0 He H0)). }
  assert (Gt : forall t, tp1 labs ntm t -> tp1 labs ntm (rn_gt M ord t)).
  { intros [[|?|?] j|u w b] Hp; cbn [rn_gt]; first [exact HN|exact Hp]. }
  assert (Gw : forall t, In t (map (NVar LNone) (seq mb (M - mb))) -> tp1 labs ntm t).
  { intros t0 H0; apply in_map_iff in H0 as [j [<- _]]; exact HN. }
  destruct (sbuild_shape lenv labs F HF _ _ E1) as [Hs1 [Ht1 _]].
  { intros h xs m Hin; unfold rn_es in Hin; apply in_app_or in Hin as [Hin|Hin].
    - apply in_map_iff in Hin as [[[h' ts'] m'] [E Hin]]; pose proof (f_equal fst E) as Eh; rewrite rn_ent_lab in Eh.
      cbn [fst] in Eh; subst h; exact (Hlab _ _ _ Hin).
    - destruct (existsb _ es); [destruct Hin|destruct Hin as [E|[]]; injection E as <- _ _; exact HN]. }
  destruct (sbuild_shape lenv labs F HF _ _ E2) as [Hs2 [Ht2 _]].
  { intros h xs m [E|[]]; injection E as <- _ _; exact HN. }
  split; [split; [exact Hs1|]|split; [exact Hs2|]].
  - apply Forall_forall; intros t' Hin; destruct (Ht1 t' Hin) as [h [xs [m [Hes Hx]]]].
    unfold rn_es in Hes; apply in_app_or in Hes as [Hes|Hes].
    + apply in_map_iff in Hes as [[[h' ts'] m'] [E He]]; unfold rn_ent in E; cbn [fst snd] in E.
      destruct h' as [|y|y]; injection E as <- <- <-; apply in_map_iff in Hx as [t0 [<- Hx]]; apply Gt;
        try (apply in_app_or in Hx as [Hx|Hx]; [|exact (Gw t0 Hx)]); exact (Htp _ _ _ t0 He Hx).
    + destruct (existsb _ es); [destruct Hes|destruct Hes as [E|[]]; injection E as <- <- <-].
      apply in_map_iff in Hx as [t0 [<- Hx]]; apply Gt, Gw, Hx.
  - unfold sren; apply Forall_forall; intros t' Hin; destruct (Ht2 t' Hin) as [h [xs [m [[E|[]] Hx]]]].
    injection E as <- <- <-; apply in_map_iff in Hx as [j [<- _]]; exact HN.
Qed.

End RenumSound.

(** ** Meanings *)

Section Sem.

Variable lenv : list label.
Variable labs : list lexp.
Variable ntm : nat.
Variable F : order.
Hypothesis HF : facts_ok lenv F.

Local Notation lden := (lden lenv).
Local Notation R := (R lenv).
Local Notation fs := (fs lenv).
Local Notation sp1 := (sp1 lenv labs ntm).

(** Words of the canonical form's steps. *)
Definition lw1 (l : lword) : Prop :=
  Forall (fun st => match st with LS s => sp1 s | LA L _ => lok lenv labs L end) l.

Lemma lw1_lwok l : lw1 l -> lwok lenv (tenvT ntm) l.
Proof.
  intros H; unfold lwok; eapply Forall_impl; [|exact H].
  intros [s|L a]; [apply sp1_oks|intros _; exact I].
Qed.

(** Free meanings that agree are real meanings that agree. *)
Lemma lw_real {T : Type} (tenv : list T) aenv penv l m : lwok lenv tenv l -> lwok lenv tenv m ->
  (forall v, feq (R l v) (R m v)) -> lwden lenv tenv aenv penv l = lwden lenv tenv aenv penv m.
Proof.
  intros Hl Hm E; apply rextensionality; intros v.
  assert (HK : forall y, realises tenv aenv penv (FVar y) (rapply ridentity y)) by (intros y; cbn; apply rapply_identity).
  pose proof (flw_real lenv tenv aenv penv l Hl FVar ridentity v HK) as A.
  pose proof (flw_real lenv tenv aenv penv m Hm FVar ridentity v HK) as B.
  rewrite rcompose_identity_l in A, B.
  exact (realises_unique tenv aenv penv _ _ _ (realises_feq tenv aenv penv _ _ _ (E v) A) B).
Qed.

Lemma fs_cong s K K' x : sp1 s -> (forall y, feq (K y) (K' y)) -> feq (fs s K x) (fs s K' x).
Proof.
  intros Hs E; rewrite !(fs_pure lenv labs s _ x (sp1_spure _ _ _ s Hs)); unfold res.
  pose proof (sres_pure1 lenv labs ntm s x Hs) as P.
  destruct (sres lenv s x) as [y|[[u b] s']]; [apply E|destruct P as [-> ->]].
  cbn [feq]; repeat split; intros y _; apply E.
Qed.

Lemma latom_cong L a K K' x : (forall y, feq (K y) (K' y)) -> feq (latom lenv L a K x) (latom lenv L a K' x).
Proof.
  intros E; unfold latom; destruct (_ <? _); [apply E|cbn [feq]; repeat split; intros y; apply E].
Qed.

Lemma R_cong x l m : (match x with LS s => sp1 s | LA _ _ => True end) ->
  (forall v, feq (R l v) (R m v)) -> forall v, feq (R (x :: l) v) (R (x :: m) v).
Proof.
  intros Hx E v; destruct x as [s|L a]; [rewrite !(R_seg lenv); exact (fs_cong s _ _ v Hx E)|].
  rewrite !(R_atom lenv); exact (latom_cong L a _ _ v E).
Qed.



Lemma sren_sp1 s : sshape lenv labs false s -> sren labs s -> sp1 s.
Proof. intros Hs Hr; split; [exact Hs|]; unfold sren in Hr; eapply Forall_impl; [|exact Hr]; intros [h j|]; cbn; tauto. Qed.

Lemma sp1_tgts_ren s : sp1 s -> sren labs s \/ exists t, In t (stgts s) /\ is_term t = true.
Proof.
  intros [_ Ht]; destruct (existsb is_term (stgts s)) eqn:E.
  - right; apply existsb_exists in E; exact E.
  - left; unfold sren; apply Forall_forall; intros t' Hin; pose proof (proj1 (Forall_forall _ _) Ht t' Hin) as Hp.
    destruct t' as [h j|u w b]; [exact Hp|].
    assert (existsb is_term (stgts s) = true) by (apply existsb_exists; exists (NBind u w b); split; [exact Hin|reflexivity]).
    congruence.
Qed.

(** A renaming then a segment. *)
Lemma scomp_sp1 S rho S' : sp1 S -> sshape lenv labs false rho -> sren labs rho ->
  scomp F ntm S rho = Some S' -> sp1 S'.
Proof.
  intros [HS Ht] Hr Hrr E; unfold scomp in E.
  destruct (sgo_spec lenv labs F HF ntm S rho S' E HS (sshape_labs lenv labs _ _ Hr)) as [Hs Htg]; split; [exact Hs|].
  apply Forall_forall; intros t' Hin; destruct (Htg t' Hin) as [H|[t0 [Hi Et]]]; [exact (proj1 (Forall_forall _ _) Ht _ H)|].
  pose proof (proj1 (Forall_forall _ _) Hrr t0 Hi) as Hp; destruct t0 as [h i|]; [|destruct Hp].
  destruct (tapp_var_in lenv F HF ntm S h i t' Et) as [[j ->]|H]; [exact Hp|exact (proj1 (Forall_forall _ _) Ht _ H)].
Qed.

Lemma res_free s K x : sp1 s ->
  fs s K x = match sres lenv s x with inl y => K y | inr (u, b, _) => FTerm u b K end.
Proof.
  intros Hs; rewrite (fs_pure lenv labs s K x (sp1_spure _ _ _ s Hs)); unfold res.
  pose proof (sres_pure1 lenv labs ntm s x Hs) as P; destruct (sres lenv s x) as [y|[[u b] s']]; [reflexivity|].
  destruct P as [-> ->]; reflexivity.
Qed.

Lemma scomp_free S rho S' : sp1 S -> sshape lenv labs false rho -> sren labs rho ->
  scomp F ntm S rho = Some S' -> forall K x, feq (fs S' K x) (fs rho (fs S K) x).
Proof.
  intros HS Hr Hrr E K x; pose proof (scomp_sp1 S rho S' HS Hr Hrr E) as HS'.
  assert (Hd : forall s, sp1 s -> sdistd lenv s).
  { intros s Hs; apply (sdistd_iff lenv); split; [exact (sshape_dist lenv labs _ _ (proj1 Hs))|].
    intros t' Hin; pose proof (proj1 (Forall_forall _ _) (proj2 Hs) t' ltac:(rewrite stgts_stargets; exact Hin)) as Hp; destruct t' as [|u w b]; [exact I|].
    destruct Hp as [-> _]; exact I. }
  assert (Er : forall s x, sren labs s -> sres lenv s x = inl (sv lenv s x)).
  { intros s x0 H; exact (sres_ren lenv labs s x0 H). }
  pose proof (sres_bridge lenv labs ntm S' rho S HS' HS Hr Hrr) as B.
  assert (Hden : forall aenv penv, sden lenv (tenvT ntm) aenv penv S'
                   = rcompose (sden lenv (tenvT ntm) aenv penv S) (sden lenv (tenvT ntm) aenv penv rho)).
  { intros aenv penv.
    exact (proj2 (scomp_sound lenv (tenvT ntm) aenv penv F HF ntm ltac:(unfold tenvT; rewrite length_map, length_seq; lia)
                    S rho S' (Hd S HS) (Hd rho (sren_sp1 rho Hr Hrr)) E)). }
  specialize (B Hden x).
  rewrite (res_free S' K x HS'), (fs_ren lenv labs rho _ x Hrr), (res_free S K _ HS), B; apply feq_refl.
Qed.

Lemma io_named io : sren labs io -> (forall l k, l <> None -> sv lenv io (mk_rvar l k) = mk_rvar l k) ->
  forall K, keq (fun z => fs io K z) K.
Proof. intros Hr H K y Hy; rewrite (fs_ren lenv labs io K y Hr); destruct y as [l k]; rewrite (H l k Hy); apply feq_refl. Qed.

Lemma renum1_io S S'' io : renum1 F S = Some (S'', io) ->
  (forall l k, l <> None -> sres lenv io (mk_rvar l k) = inl (mk_rvar l k))
  /\ exists ord M, NoDup ord /\ (forall o, In o ord -> o < M)
     /\ forall k, sres lenv io (mk_rvar None k)
                  = inl (mk_rvar None (if k <? List.length ord then nth k ord 0 else k - List.length ord + M)).
Proof.
  unfold renum1; destruct (bent F S) as [tsb mb]; cbv zeta.
  set (es := ents S); set (bl := rn_bl es); set (M := rn_M mb bl); set (ord := rn_ord bl mb M).
  destruct (sbuild F (rn_es es mb M ord)) as [S0|]; [|discriminate].
  destruct (sbuild F [(LNone, (map (NVar LNone) ord, M))]) as [io0|] eqn:E2; [|discriminate].
  intros H; injection H as <- <-; pose proof (io_sres lenv F HF ord M io0 E2) as Hio.
  split; [intros [x|] k Hl; [rewrite Hio; reflexivity|destruct (Hl eq_refl)]|].
  exists ord, M; split; [apply nodup_nat_nodup|split; [|intros k; exact (Hio None k)]].
  intros o Ho; unfold ord, rn_ord in Ho; apply nodup_nat_spec in Ho as [Ho _].
  destruct (rn_M_ge mb bl) as [HM HbM]; fold M in HM, HbM.
  apply in_app_or in Ho as [Ho|Ho]; [exact (HbM o Ho)|apply in_seq in Ho; lia].
Qed.

Lemma renum1_free S S'' io : In LNone labs -> sp1 S -> renum1 F S = Some (S'', io) ->
  forall K x, feq (fs S K x) (fs S'' (fs io K) x).
Proof.
  intros HN HS E K x; destruct (renum1_shape lenv labs ntm F HF S S'' io HN HS E) as [HS'' [Hio Hior]].
  destruct (renum1_io S S'' io E) as [Hn _].
  rewrite (res_free S K x HS), (res_free S'' _ x HS''), (renum1_comp lenv F HF S S'' io E x).
  pose proof (sres_pure1 lenv labs ntm S'' x HS'') as P.
  destruct (sres lenv S'' x) as [y|[[u b] s']].
  - rewrite (fs_ren lenv labs io K y Hior), (sres_ren lenv labs io y Hior); apply feq_refl.
  - destruct P as [-> _]; cbn [feq]; repeat split; intros y Hy; specialize (Hy eq_refl).
    rewrite (fs_ren lenv labs io K y Hior); destruct y as [l k]; cbn [v_label] in Hy.
    pose proof (Hn l k Hy) as E1; rewrite (sres_ren lenv labs io _ Hior) in E1; injection E1 as ->; apply feq_refl.
Qed.

End Sem.

(** ** A renaming in front of a canonical word *)

Section Rcons.

Variable F : order.
Variable ntm : nat.

Definition named_id (G : seg) : bool := match sdrop_none G with SNil => true | _ => false end.

(** A segment with terms in front of the canonical word [K], the word
    after it having been put in canonical form: a last segment that only
    renames bound variables joins it. *)
Definition fixlast (S : seg) (K : lword) : option lword :=
  match K with
  | [LS G] => if has_terms G then Some (LS S :: K)
              else if named_id G then option_map (fun X => [LS X]) (scomp F ntm G S)
              else Some (LS S :: K)
  | _ => Some (LS S :: K)
  end.

Fixpoint rcons (rho : seg) (K : lword) {struct K} : option lword :=
  match K with
  | [] => Some (lpre rho)
  | LS Sg :: K1 =>
      match scomp F ntm Sg rho with
      | Some S' =>
          if has_terms S' then
            match renum1 F S' with
            | Some (S'', io) =>
                obind (match io with SNil => Some K1 | _ => rcons io K1 end) (fixlast S'')
            | None => None
            end
          else rcons S' K1
      | None => None
      end
  | LA L a :: K2 =>
      match wcomp F ntm (WAtom SNil L a (WEnd SNil)) (WEnd rho) with
      | Some (WAtom Q L' a' (WEnd U)) =>
          if has_terms Q then None
          else obind (match Q with SNil => Some K2 | _ => rcons Q K2 end) (fun K2' => Some (lpre U ++ LA L' a' :: K2'))
      | _ => None
      end
  end.

End Rcons.
