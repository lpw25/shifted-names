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

End RenumSound.
