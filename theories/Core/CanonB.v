(** * Terms onto a canonical word

    [layer Z W]: a segment with terms in front of the canonical word [W],
    as a new layer: its targets go to their representatives in [W], its
    bound targets are renumbered, and the renumbering goes into [W].
    [bcore T W]: bound variables instantiated with terms, in front of
    [W]: the terms join the first layer, go on top of it, or go under
    it. *)

From Stdlib Require Import Arith List Lia Bool Sorted.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Unique Normal Layered LayeredUnique Order
  Canon Retarget LFree CanonF CanonR.
Import ListNotations.

Section Layer.

Variable F : order.
Variable ntm : nat.

(** A segment with terms [Z] as a new layer in front of [W]: its targets
    go to their representatives in [W], its bound targets are numbered by
    first use, and [rc] puts the renumbering in front of [W]. *)
Definition layer_with (rc : seg -> lword -> option lword) (Z : seg) (W : lword) : option lword :=
  match reroute F W Z with
  | Some Z' =>
      match W with
      | [] => Some [LS Z']
      | _ =>
          match renum1 F Z' with
          | Some (S'', io) => obind (match io with SNil => Some W | _ => rc io W end) (fixlast F ntm S'')
          | None => None
          end
      end
  | None => None
  end.

(** The canonical word of a renaming [rho] then the canonical word [K]. *)
Fixpoint rcons (rho : seg) (K : lword) {struct K} : option lword :=
  match K with
  | [] => Some (lpre rho)
  | LS Sg :: K1 =>
      match scomp F ntm Sg rho with
      | Some S' => if has_terms S' then layer_with (fun io _ => rcons io K1) S' K1 else rcons S' K1
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

Definition layer (Z : seg) (W : lword) : option lword := layer_with rcons Z W.

End Layer.

Section LayerOk.

Variable lenv : list label.
Variable labs : list lexp.
Hypothesis Hinj : forall h h', In h labs -> In h' labs -> lden lenv h = lden lenv h' -> h = h'.
Hypothesis HN : In LNone labs.
Variable ntm : nat.
Variable F : order.
Hypothesis HF : facts_ok lenv F.
Hypothesis Htot : forall a b, In a labs -> In b labs -> lcmp F a b <> None.

Local Notation lden := (lden lenv).
Local Notation R := (R lenv).
Local Notation fs := (fs lenv).
Local Notation sres := (sres lenv).
Local Notation sp1 := (sp1 lenv labs ntm).
Local Notation lw1 := (lw1 lenv labs ntm).
Local Notation lnf := (lnf lenv labs gtP route_id (num_first lenv)).
Local Notation segok := (segok lenv labs gtP route_id (num_first lenv)).

Lemma sres_lab Z x y : sp1 Z -> sres Z x = inl y ->
  llab lenv labs (v_label y) \/ (y = x /\ ~ llab lenv labs (v_label x)).
Proof.
  intros HZ; unfold LayeredUnique.sres.
  destruct (Normalise.sget lenv (v_label x) Z) as [[ts m]|] eqn:E.
  - intros Ey; left; destruct (sget_ents' lenv (v_label x) Z ts m E) as [g [Hin Hg]].
    assert (Hgl : In g labs).
    { apply (sshape_labs lenv labs false Z (proj1 HZ) g (tl_list ts) m).
      rewrite <- ents_sents; apply (in_map (fun e => (fst (fst e), tl_list (snd (fst e)), snd e)) _ _ Hin). }
    destruct (Nat.ltb_spec (v_index x) (tlen ts)) as [Hi|Hi].
    + pose proof (proj1 (Forall_forall _ _) (proj2 HZ) _ (sget_tgts lenv _ _ _ _ E _ (tnth_in _ _ Hi))) as Ht.
      destruct (tnth ts (v_index x)) as [h j|u w b]; cbn [tres] in Ey; [|discriminate].
      injection Ey as <-; exists h; split; [exact Ht|reflexivity].
    + injection Ey as <-; exists g; split; [exact Hgl|exact Hg].
  - intros Ey; injection Ey as <-.
    destruct (existsb (fun g => label_eqb (lden g) (v_label x)) labs) eqn:Ex.
    + left; apply existsb_exists in Ex as [g [Hg Eg]]; apply label_eqb_eq in Eg; exists g; split; [exact Hg|exact Eg].
    + right; split; [reflexivity|]; intros [g [Hg Eg]].
      assert (existsb (fun g => label_eqb (lden g) (v_label x)) labs = true)
        by (apply existsb_exists; exists g; split; [exact Hg|rewrite Eg; apply label_eqb_refl]); congruence.
Qed.

Lemma layer_with_ok rc Z W K' : lnf W -> lw1 W -> sp1 Z -> sterm lenv Z ->
  (forall y u b k, R W y = FTerm u b k -> gtP (R W) k) ->
  (forall io K1', sshape lenv labs false io -> sren labs io -> rc io W = Some K1' ->
     lnf K1' /\ lw1 K1' /\ forall v, feq (R K1' v) (R (LS io :: W) v)) ->
  layer_with F ntm rc Z W = Some K' -> lnf K' /\ lw1 K' /\ forall v, feq (R K' v) (R (LS Z :: W) v).
Proof.
  intros Hl Hw HZ HZt Hor Hrc; unfold layer_with.
  destruct (reroute F W Z) as [Z'|] eqn:ER; [|discriminate].
  destruct (reroute_ok lenv labs Hinj ntm F HF Htot HN W Z Z' Hw HZ ER) as [HZ' Hres].
  assert (Sem0 : forall v, feq (fs Z' (R W) v) (fs Z (R W) v)).
  { intros v; rewrite (res_free lenv labs ntm Z' _ v HZ'), (res_free lenv labs ntm Z _ v HZ), Hres.
    destruct (sres Z v) as [y|[[u b] s']]; cbn [rvsres];
      [exact (rvs_feq lenv labs Hinj ntm F HF Htot HN route_id (num_first lenv) W Hl Hw v y)|apply feq_refl]. }
  assert (HZ't : sterm lenv Z') by (destruct HZt as [x [t Ex]]; exists x, t; rewrite Hres, Ex; reflexivity).
  assert (Hne : forall X, sterm lenv X -> X <> SNil) by (intros X [x [t E]] ->; discriminate E).
  destruct W as [|st Wr].
  - intros E; injection E as <-.
    split; [split; [exact (Hne Z' HZ't)|split; [exact I|left; split; [exact HZ't|exact (segok_nil lenv labs ntm Z' HZ')]]]|].
    split; [exact (lw1_one lenv labs ntm Z' HZ')|intros v; exact (Sem0 v)].
  - destruct (renum1 F Z') as [[S'' io]|] eqn:EN; [|discriminate].
    destruct (renum1_shape lenv labs ntm F HF Z' S'' io HN HZ' EN) as [HS'' [Hios Hior]].
    assert (HS''t : sterm lenv S'').
    { destruct HZ't as [x [t Ex]]; exists x, t; rewrite (renum1_comp lenv F HF Z' S'' io EN x) in Ex.
      destruct (sres S'' x) as [y|t']; [|exact Ex].
      rewrite (sres_ren lenv labs io _ Hior) in Ex; discriminate Ex. }
    assert (HK1' : forall K1', (match io with SNil => Some (st :: Wr) | _ => rc io (st :: Wr) end) = Some K1' ->
                     lnf K1' /\ lw1 K1' /\ forall v, feq (R K1' v) (fs io (R (st :: Wr)) v)).
    { intros K1' E1; destruct io as [|h ts m r].
      - injection E1 as <-; split; [exact Hl|split; [exact Hw|intros v; rewrite (fs_nil lenv labs); apply feq_refl]].
      - exact (Hrc _ K1' Hios Hior E1). }
    match goal with |- obind ?X _ = _ -> _ => destruct X as [K1'|] eqn:E1 end;
      [|cbn [obind]; intros H; discriminate H]; cbn [obind]; intros EF.
    destruct (HK1' K1' E1) as [HlK1' [HwK1' Sem1]].
    assert (Hro : forall x y, sres Z' x = inl y -> route_id (R (st :: Wr)) x y).
    { intros x y e; rewrite Hres in e; destruct (sres Z x) as [y0|t] eqn:Ez; cbn [rvsres] in e; [|discriminate].
      injection e as <-; destruct (sres_lab Z x y0 HZ Ez) as [Hy|[-> Hn]].
      - exact (rvs_route lenv labs Hinj ntm F HF Htot HN _ _ _ Hl Hw x y0 Hy).
      - assert (Hx : isnamed x = true)
          by (unfold isnamed; destruct (v_label x) eqn:El; [reflexivity|exfalso; apply Hn; exists LNone; split; [exact HN|cbn; congruence]]).
        unfold rvs, same_r; destruct (find (fun g => label_eqb (lden g) (v_label x)) labs) as [g|] eqn:Eg.
        + exfalso; apply find_some in Eg as [Eg Hg]; apply label_eqb_eq in Eg; apply Hn; exists g; split; assumption.
        + rewrite andb_false_r; destruct (rv_cases lenv labs F (st :: Wr) x) as [[g [Hg [Eg' _]]]|[_ ->]].
          * exfalso; apply Hn; exists g; split; assumption.
          * split; [intros _ _; reflexivity|split; [intros _; left; reflexivity|intros Hb; unfold isnamed, bound in *; rewrite Hb in Hx; discriminate]]. }
    assert (Hbi : forall y y', bound y -> bound y' -> (exists x, sres Z' x = inl y) -> (exists x', sres Z' x' = inl y') ->
                    feq (R (st :: Wr) y) (R (st :: Wr) y') -> y = y').
    { intros y y' Hy Hy' [x e] [x' e']; rewrite Hres in e, e'.
      destruct (sres Z x) as [y0|t]; cbn [rvsres] in e; [|discriminate]; injection e as <-.
      destruct (sres Z x') as [y0'|t]; cbn [rvsres] in e'; [|discriminate]; injection e' as <-.
      pose proof (rvs_bound lenv labs F _ x y0 Hy) as Eb1; pose proof (rvs_bound lenv labs F _ x' y0' Hy') as Eb2.
      rewrite Eb1 in Hy |- *; rewrite Eb2 in Hy' |- *.
      exact (rv_inj lenv labs Hinj ntm F HF Htot HN _ _ _ Hl Hw y0 y0' Hy Hy'). }
    destruct (fixlast_ok lenv labs Hinj ntm F HF S'' K1' K' HS'' HS''t HlK1' HwK1'
                (fun Hlast => segok_renum lenv labs HN ntm F HF Z' S'' io (st :: Wr) K1' HZ' Hro Hor Hbi EN Sem1 Hlast) EF)
      as [A [B C]].
    split; [exact A|split; [exact B|intros v]].
    apply (feq_trans _ _ _ (C v)); rewrite (R_seg lenv S'' K1' v), (R_seg lenv Z (st :: Wr) v).
    apply (feq_trans _ _ _ (fs_cong lenv labs ntm S'' _ _ v HS'' Sem1)).
    apply (feq_trans _ _ _ (feq_sym _ _ (renum1_free lenv labs ntm F HF Z' S'' io HN HZ' EN _ v))).
    exact (Sem0 v).
Qed.

(** The canonical word of a renaming then a canonical word is canonical
    and means the same. *)
Theorem rcons_ok K : forall rho K', lnf K -> lw1 K -> sshape lenv labs false rho -> sren labs rho ->
  rcons F ntm rho K = Some K' -> lnf K' /\ lw1 K' /\ forall v, feq (R K' v) (R (LS rho :: K) v).
Proof.
  induction K as [|[Sg|L a] K1 IH]; intros rho K' Hl Hw Hr Hrr; cbn [rcons].
  - intros E; injection E as <-; destruct rho as [|h ts m r]; cbn [lpre].
    + split; [exact I|split; [constructor|intros v; rewrite (R_seg lenv SNil [] v), (fs_nil lenv labs); apply feq_refl]].
    + split; [split; [discriminate|split; [exact I|right; split; [exact Hr|split; [exact Hrr|left; reflexivity]]]]|].
      split; [exact (lw1_one lenv labs ntm _ (sren_sp1 lenv labs ntm _ Hr Hrr))|intros v; apply feq_refl].
  - inversion Hw as [|? ? HSg HK1]; subst; destruct Hl as [HnS [HlK1 Hor]].
    destruct (scomp F ntm Sg rho) as [S'|] eqn:ES; [|discriminate].
    pose proof (scomp_sp1 lenv labs ntm F HF Sg rho S' HSg Hr Hrr ES) as HS'.
    pose proof (scomp_free lenv labs ntm F HF Sg rho S' HSg Hr Hrr ES) as Sem0.
    destruct (has_terms S') eqn:Ht.
    + assert (HSt : sterm lenv S') by exact (has_terms_sterm lenv labs ntm S' HS' Ht).
      destruct Hor as [[_ HSo]|[_ [HSr _]]].
      2:{ exfalso; destruct HSt as [x [t Ex]].
          rewrite (scomp_sres lenv labs ntm F HF Sg rho S' HSg Hr Hrr ES x), (sres_ren lenv labs Sg _ HSr) in Ex.
          discriminate Ex. }
      intros E.
      destruct (layer_with_ok (fun io _ => rcons F ntm io K1) S' K1 K' HlK1 HK1 HS' HSt (so_order _ _ _ _ _ _ _ HSo)
                  (fun io K1' Hios Hior E1 => IH io K1' HlK1 HK1 Hios Hior E1) E) as [A [B C]].
      split; [exact A|split; [exact B|intros v]].
      apply (feq_trans _ _ _ (C v)); rewrite (R_seg lenv S' K1 v); exact (Sem0 _ v).
    + intros E; destruct (IH S' K' HlK1 HK1 (proj1 HS') (noterms_sren lenv labs ntm S' HS' Ht) E) as [A [B C]].
      split; [exact A|split; [exact B|intros v; exact (feq_trans _ _ _ (C v) (Sem0 _ v))]].
  - inversion Hw as [|? ? HL HK1]; subst; destruct Hl as [HLok HlK1].
    destruct (wcomp F ntm (WAtom SNil L a (WEnd SNil)) (WEnd rho)) as [[s0|Q L' a' [U|s2 L2 a2 w2|s5 w5]|s4 w4]|] eqn:EW;
      try (intros E; discriminate E).
    destruct (has_terms Q) eqn:HtQ; [intros E; discriminate E|].
    destruct (atom_ok lenv labs ntm F HF rho L a K1 Q L' a' U Hr Hrr HLok HK1 EW HtQ) as [HQs [HQr [HUs [HUr [HL' [Hpos Sem]]]]]].
    assert (HK2' : forall K2', (match Q with SNil => Some K1 | _ => rcons F ntm Q K1 end) = Some K2' ->
                     lnf K2' /\ lw1 K2' /\ forall v, feq (R K2' v) (R (LS Q :: K1) v)).
    { intros K2' E2; destruct Q as [|h ts m r].
      - injection E2 as <-; split; [exact HlK1|split; [exact HK1|intros v; rewrite (R_seg lenv SNil K1 v), (fs_nil lenv labs); apply feq_refl]].
      - exact (IH _ K2' HlK1 HK1 HQs HQr E2). }
    destruct (match Q with SNil => Some K1 | _ => rcons F ntm Q K1 end) as [K2'|] eqn:E2; [|intros E; discriminate E].
    cbn [obind]; intros E; injection E as <-.
    destruct (HK2' K2' eq_refl) as [A [B C]].
    assert (FU : Forall (fun st => match st with LS s => sp1 s | LA _ _ => True end) (lpre U)).
    { destruct U; [constructor|constructor; [exact (sren_sp1 lenv labs ntm _ HUs HUr)|constructor]]. }
    split; [|split].
    + destruct U as [|h ts m r]; cbn [lpre app]; [split; assumption|].
      split; [discriminate|split; [split; assumption|right; split; [exact HUs|split; [exact HUr|]]]].
      right; exists L', a', K2'; split; [reflexivity|exact Hpos].
    + apply (lw1_lpre lenv labs ntm); [exact (sren_sp1 lenv labs ntm _ HUs HUr)|constructor; assumption].
    + intros v; refine (feq_trans _ _ _ _ (Sem v)).
      apply (R_app_cong lenv labs ntm (lpre U) _ _ FU); exact (R_cong lenv labs ntm (LA L' a') _ _ I C).
Qed.

Lemma layer_ok Z W K' : lnf W -> lw1 W -> sp1 Z -> sterm lenv Z ->
  (forall y u b k, R W y = FTerm u b k -> gtP (R W) k) ->
  layer F ntm Z W = Some K' -> lnf K' /\ lw1 K' /\ forall v, feq (R K' v) (R (LS Z :: W) v).
Proof.
  intros Hl Hw HZ HZt Hor; apply (layer_with_ok (rcons F ntm) Z W K' Hl Hw HZ HZt Hor).
  intros io K1' Hios Hior E; exact (rcons_ok W io K1' Hl Hw Hios Hior E).
Qed.

End LayerOk.

(** ** Bound variables instantiated with terms *)

Section Bcore.

Variable F : order.
Variable labs : list lexp.
Variable ntm : nat.

(** [h₍ᵢ₎ ↦ Tᵢ] on bound variables below [|T|], the others shifted down. *)
Definition ET (T : list ntgt) : option seg := sbuild F [(LNone, (T, 0))].

(** The terms joined to the bound entry of the first layer [S1]. *)
Definition join (T : list ntgt) (S1 : seg) : option seg :=
  let '(xs, m) := bent F S1 in
  sbuild F ((LNone, (T ++ tl_list xs, m)) :: map (fun e => (fst (fst e), (tl_list (snd (fst e)), snd e))) (ents S1)).

(** *** Under the first layer

    When the terms' payload is below that of the first layer [S1], they
    go under it: [S1] does only renamings to named variables ([rho_sw]
    does the same, with bound variables for the named variables it does
    not reach); the terms go onto [rho_sw ⨾ K1]; [mu_sw] undoes the
    renaming of named variables; [S1] lifted over the terms ([lift_sw])
    goes on top. *)

Definition named_ents (S1 : seg) : list (lexp * tlist * nat) :=
  filter (fun e => negb (lexp_eqb (fst (fst e)) LNone)) (ents S1).

Definition ntgts (S1 : seg) : list ntgt := flat_map (fun e => tl_list (snd (fst e))) (named_ents S1).

Definition is_tgt (h : lexp) (j : nat) (ts : list ntgt) : bool :=
  existsb (fun t => match t with NVar g k => lexp_eqb g h && (k =? j) | _ => false end) ts.

Definition missing (S1 : seg) : list (lexp * nat) :=
  flat_map (fun e => let '(h, _, m) := e in
                     filter (fun p => negb (is_tgt (fst p) (snd p) (ntgts S1))) (map (fun j => (h, j)) (seq 0 m)))
           (named_ents S1).

Fixpoint posof (h : lexp) (j : nat) (ts : list ntgt) (p : nat) : option nat :=
  match ts with
  | [] => None
  | NVar g k :: r => if lexp_eqb g h && (k =? j) then Some p else posof h j r (S p)
  | _ :: r => posof h j r (S p)
  end.

Fixpoint findpos (h : lexp) (j : nat) (es : list (lexp * tlist * nat)) : option (lexp * nat) :=
  match es with
  | [] => None
  | (g, ts, _) :: r => match posof h j (tl_list ts) 0 with Some p => Some (g, p) | None => findpos h j r end
  end.

Fixpoint pidx (x : lexp * nat) (l : list (lexp * nat)) : nat :=
  match l with [] => 0 | y :: r => if lexp_eqb (fst y) (fst x) && (snd y =? snd x) then 0 else S (pidx x r) end.

Definition rho_sw (S1 : seg) : option seg :=
  sbuild F ((LNone, (map (fun p => NVar (fst p) (snd p)) (missing S1), 0))
            :: map (fun e => (fst (fst e), (tl_list (snd (fst e)), snd e))) (named_ents S1)).

Definition pre_sw (n : nat) (S1 : seg) (h : lexp) (j : nat) : ntgt :=
  match findpos h j (named_ents S1) with
  | Some (g, p) => NVar g p
  | None => NVar LNone (n + pidx (h, j) (missing S1))
  end.

Definition mu_sw (n : nat) (S1 : seg) : option seg :=
  sbuild F ((LNone, (map (NVar LNone) (seq 0 n), n + List.length (missing S1)))
            :: map (fun e => let '(h, ts, m) := e in (h, (map (pre_sw n S1 h) (seq 0 m), tlen ts))) (named_ents S1)).

Definition shb (n : nat) (t : ntgt) : ntgt := match t with NVar LNone j => NVar LNone (n + j) | _ => t end.

Definition lift_sw (n : nat) (S1 : seg) : option seg :=
  let '(xs, m) := bent F S1 in
  sbuild F ((LNone, (map (NVar LNone) (seq 0 n) ++ map (shb n) (tl_list xs), n + m))
            :: map (fun e => (fst (fst e), (map (shb n) (tl_list (snd (fst e))), snd e))) (named_ents S1)).

Fixpoint bcore (fuel : nat) (T : list ntgt) (K : lword) {struct fuel} : option lword :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match ET T with
      | None => None
      | Some E =>
          match K with
          | LS S1 :: K1 =>
              if has_terms S1 then
                if existsb is_term (ntgts S1) then layer F ntm E K else
                match pcmp F K (List.length K) (List.length K1) with
                | Some Eq => option_map (fun J => LS J :: K1) (join T S1)
                | Some Gt => layer F ntm E K
                | Some Lt =>
                    match rho_sw S1, mu_sw (List.length T) S1, lift_sw (List.length T) S1 with
                    | Some rho, Some mu, Some Z =>
                        match rcons F ntm rho K1 with
                        | Some K1' =>
                            match bcore fuel' T K1' with
                            | Some Y => match rcons F ntm mu Y with Some W => layer F ntm Z W | None => None end
                            | None => None
                            end
                        | None => None
                        end
                    | _, _, _ => None
                    end
                | None => None
                end
              else layer F ntm E K
          | _ => layer F ntm E K
          end
      end
  end.

End Bcore.

Section BcoreOk.

Variable lenv : list label.
Variable labs : list lexp.
Hypothesis Hinj : forall h h', In h labs -> In h' labs -> lden lenv h = lden lenv h' -> h = h'.
Hypothesis HN : In LNone labs.
Variable ntm : nat.
Variable F : order.
Hypothesis HF : facts_ok lenv F.
Hypothesis Htot : forall a b, In a labs -> In b labs -> lcmp F a b <> None.

Local Notation lden := (lden lenv).
Local Notation R := (R lenv).
Local Notation fs := (fs lenv).
Local Notation sres := (sres lenv).
Local Notation sp1 := (sp1 lenv labs ntm).
Local Notation tp1 := (tp1 labs ntm).
Local Notation lw1 := (lw1 lenv labs ntm).
Local Notation lnf := (lnf lenv labs gtP route_id (num_first lenv)).
Local Notation segok := (segok lenv labs gtP route_id (num_first lenv)).

Definition tterm (t : ntgt) : Prop := match t with NBind u w b => w = WEnd SNil /\ b = None /\ u < ntm | _ => False end.

Lemma ET_ok T E : Forall tterm T -> ET F T = Some E ->
  sp1 E /\ forall l i, sres E (mk_rvar l i) =
    match l with None => if i <? List.length T then tres lenv (nth i T (NVar LNone 0)) else inl (mk_rvar None (i - List.length T))
               | Some _ => inl (mk_rvar l i) end.
Proof.
  intros HT EE; split.
  - destruct (sbuild_shape lenv labs F HF _ _ EE) as [Hs [Ht _]]; [intros h xs m [Eh|[]]; injection Eh as <- _ _; exact HN|].
    split; [exact Hs|apply Forall_forall; intros t Hin; destruct (Ht t Hin) as [h [xs [m [[Eh|[]] Hx]]]]].
    injection Eh as <- <- <-; pose proof (proj1 (Forall_forall _ _) HT t Hx) as H; destruct t; [destruct H|exact H].
  - intros l i; rewrite (sres_sbuild lenv F HF _ _ EE l i); cbn [find fst].
    destruct l as [x|]; cbn [label_eqb Normalise.lden]; [reflexivity|].
    unfold etgt; destruct (i <? List.length T); [reflexivity|do 2 f_equal; lia].
Qed.

Lemma sp1_tterm T : Forall tterm T -> Forall tp1 T.
Proof. intros H; eapply Forall_impl; [|exact H]; intros [h j|u w b]; cbn; tauto. Qed.

Lemma lw1_lgood W : lw1 W -> lgood lenv labs W.
Proof.
  intros Hw; eapply Forall_impl; [|exact Hw]; intros [s|L a]; cbn.
  - intros Hs; split; [exact (sshape_dist lenv labs _ _ (proj1 Hs))|].
    intros h ts m Hin; apply (sshape_labs lenv labs false s (proj1 Hs) h (tl_list ts) m).
    rewrite <- ents_sents; apply (in_map (fun e => (fst (fst e), tl_list (snd (fst e)), snd e)) _ _ Hin).
  - intros [Hso Hf]; split; [intros p Hp; exact (proj1 (proj1 (Forall_forall _ _) Hf p Hp))|].
    clear Hf; induction L as [|p L IH]; [constructor|]; inversion Hso as [|? ? Hs Hall]; subst; constructor; [|exact (IH Hs)].
    intros Hin; apply in_map_iff in Hin as [q [Eq Hq]]; pose proof (proj1 (Forall_forall _ _) Hall q Hq) as H; cbn in H.
    rewrite Eq in H; exact (olabel_lt_irrefl _ H).
Qed.

(** What a word whose first step has no terms sends to a term has a
    smaller payload. *)
Lemma hor_noterm K : lnf K -> lw1 K -> (match K with LS S1 :: _ => has_terms S1 = false | _ => True end) ->
  forall y u b k, R K y = FTerm u b k -> gtP (R K) k.
Proof.
  intros Hl Hw Hk y u b k E.
  assert (Atom : forall L a K2 z, lnf K2 -> R (LA L a :: K2) z = FTerm u b k -> exists e, e < natl (LA L a :: K2) /\ deep e k).
  { intros L a K2 z H2 Ez; rewrite (R_atom lenv) in Ez; unfold latom in Ez; destruct (_ <? _); [|discriminate Ez].
    destruct (tdeep lenv labs gtP route_id (num_first lenv) K2 H2 z u b k Ez) as [e [He Hd]]; exists e; split; [cbn [natl]; lia|exact Hd]. }
  assert (Fin : forall e, e < natl K -> deep e k -> gtP (R K) k) by (intros e He Hd; exact (gtP_deep _ _ _ _ (deep_R lenv K) Hd He)).
  destruct K as [|[S1|L a] K1]; [discriminate E| |destruct (Atom L a K1 y (proj2 Hl) E) as [e [He Hd]]; exact (Fin e He Hd)].
  inversion Hw as [|? ? HS Hw1]; subst; destruct Hl as [_ [Hl1 [[[x [t Ex]] _]|[_ [Hren Hr]]]]].
  - exfalso; rewrite (sres_ren lenv labs S1 x (noterms_sren lenv labs ntm S1 HS Hk)) in Ex; discriminate Ex.
  - rewrite (R_seg lenv), (fs_ren lenv labs S1 _ y Hren) in E.
    destruct Hr as [->|[L [a [K2 [-> _]]]]]; [discriminate E|].
    destruct (Atom L a K2 _ (proj2 Hl1) E) as [e [He Hd]]; exact (Fin e He Hd).
Qed.

Lemma hor_gt S1 K1 : lnf (LS S1 :: K1) -> lw1 (LS S1 :: K1) -> has_terms S1 = true -> gtP (R (LS S1 :: K1)) (R K1) ->
  forall y u b k, R (LS S1 :: K1) y = FTerm u b k -> gtP (R (LS S1 :: K1)) k.
Proof.
  intros Hl Hw Ht Hgt y u b k E; inversion Hw as [|? ? HS _]; subst.
  destruct Hl as [_ [_ [[_ HSo]|[_ [Hren _]]]]]; [|rewrite (sren_noterms labs S1 Hren) in Ht; discriminate].
  rewrite (R_seg lenv), (res_free lenv labs ntm S1 _ y HS) in E.
  destruct (sres S1 y) as [y'|[[u' b'] s']] eqn:Ey.
  - exact (gtP_trans _ _ _ Hgt (so_order _ _ _ _ _ _ _ HSo y' u b k E)).
  - injection E as <- <- <-; apply (gtP_keq _ _ (R K1) _ (keq_refl _)); [apply keq_refl|exact Hgt].
Qed.

Lemma join_sres T S1 J : sp1 S1 -> join F T S1 = Some J -> forall l i,
  sres J (mk_rvar l i) = match l with
                         | None => if i <? List.length T then tres lenv (nth i T (NVar LNone 0)) else sres S1 (mk_rvar None (i - List.length T))
                         | Some _ => sres S1 (mk_rvar l i)
                         end.
Proof.
  intros HS; unfold join; pose proof (bent_find lenv F HF S1) as Eb.
  destruct (bent F S1) as [xs m]; intros E l i; rewrite (sres_sbuild lenv F HF _ _ E l i); cbn [find fst].
  destruct l as [x|]; cbn [label_eqb Normalise.lden].
  - rewrite (find_map_lab lenv (fun e => (fst (fst e), (tl_list (snd (fst e)), snd e))) (fun e => fst (fst e)) fst (ents S1))
      by (intros e; reflexivity).
    rewrite (sres_ents lenv S1 (Some x) i).
    destruct (find (fun e : lexp * tlist * nat => label_eqb (lden (fst (fst e))) (Some x)) (ents S1)) as [[[h ts] m']|]; reflexivity.
  - rewrite (sres_ents lenv S1 None (i - List.length T)).
    destruct (find (fun e => label_eqb (lden (fst (fst e))) None) (ents S1)) as [[[h ts] m']|] eqn:Ef;
      injection Eb as -> ->; unfold etgt; rewrite length_app; cbn [tl_list List.length].
    + apply find_some in Ef as [Eh _]; cbn [fst] in Eh; apply label_eqb_eq in Eh; rewrite Eh.
      destruct (Nat.ltb_spec i (List.length T)) as [H1|H1]; [rewrite (proj2 (Nat.ltb_lt _ _)) by lia; rewrite app_nth1 by exact H1; reflexivity|].
      rewrite app_nth2 by exact H1; destruct (Nat.ltb_spec (i - List.length T) (List.length (tl_list ts))) as [H2|H2].
      * rewrite (proj2 (Nat.ltb_lt _ _)) by lia; reflexivity.
      * rewrite (proj2 (Nat.ltb_ge _ _)) by lia; do 2 f_equal; lia.
    + destruct (Nat.ltb_spec i (List.length T)) as [H1|H1]; [rewrite (proj2 (Nat.ltb_lt _ _)) by lia; rewrite app_nth1 by exact H1; reflexivity|].
      rewrite (proj2 (Nat.ltb_ge _ _)) by lia; do 2 f_equal; lia.
Qed.

Lemma join_ok T S1 K1 J : Forall tterm T -> T <> [] -> sp1 S1 -> segok S1 K1 -> join F T S1 = Some J ->
  sp1 J /\ sterm lenv J /\ segok J K1.
Proof.
  intros HT Hne HS HSo E; pose proof (join_sres T S1 J HS E) as Hj.
  set (n := List.length T) in *.
  assert (HJ : sp1 J).
  { unfold join in E; destruct (bent F S1) as [xs m] eqn:Eb.
    pose proof (bent_find lenv F HF S1) as Eb'; rewrite Eb in Eb'.
    assert (Hlab : forall h ts m0, In (h, ts, m0) (ents S1) -> In h labs).
    { intros h ts m0 Hin; apply (sshape_labs lenv labs false S1 (proj1 HS) h (tl_list ts) m0).
      rewrite <- ents_sents; apply (in_map (fun e => (fst (fst e), tl_list (snd (fst e)), snd e)) _ _ Hin). }
    destruct (sbuild_shape lenv labs F HF _ _ E) as [Hs [Ht _]].
    { intros h xs0 m0 [Eh|Hin]; [injection Eh as <- _ _; exact HN|].
      apply in_map_iff in Hin as [[[h' ts'] m'] [Eh Hin]]; injection Eh as <- _ _; exact (Hlab _ _ _ Hin). }
    split; [exact Hs|apply Forall_forall; intros t Hin; destruct (Ht t Hin) as [h [xs0 [m0 [He Hx]]]]].
    destruct He as [Eh|He].
    - injection Eh as <- <- <-; apply in_app_or in Hx as [Hx|Hx]; [exact (proj1 (Forall_forall _ _) (sp1_tterm T HT) t Hx)|].
      destruct (find (fun e => label_eqb (lden (fst (fst e))) None) (ents S1)) as [[[h' ts'] m']|] eqn:Ef;
        injection Eb' as -> ->; [|destruct Hx].
      apply find_some in Ef as [_ Hin']; exact (proj1 (Forall_forall _ _) (proj2 HS) t (ents_stgts S1 _ _ _ t Hin' Hx)).
    - apply in_map_iff in He as [[[h' ts'] m'] [Eh He]]; injection Eh as <- <- <-.
      exact (proj1 (Forall_forall _ _) (proj2 HS) t (ents_stgts S1 _ _ _ t He Hx)). }
  set (sg := fun x : rvar => match v_label x with None => mk_rvar None (v_index x - n) | Some _ => x end).
  set (tau := fun x : rvar => match v_label x with None => mk_rvar None (n + v_index x) | Some _ => x end).
  assert (Hjs : forall x y, sres J x = inl y -> sres S1 (sg x) = inl y /\ x = tau (sg x)).
  { intros [[l|] i] y e; rewrite Hj in e; unfold sg, tau; cbn [v_label v_index]; [split; [exact e|reflexivity]|].
    destruct (Nat.ltb_spec i n) as [Hi|Hi].
    - exfalso; pose proof (proj1 (Forall_forall _ _) HT _ (nth_In T (NVar LNone 0) Hi)) as Ht.
      destruct (nth i T (NVar LNone 0)); [destruct Ht|discriminate e].
    - split; [exact e|f_equal; lia]. }
  assert (Hsj : forall z y, sres S1 z = inl y -> sres J (tau z) = inl y).
  { intros [[l|] i] y e; unfold tau; cbn [v_label v_index]; rewrite Hj; [exact e|].
    rewrite (proj2 (Nat.ltb_ge _ _)) by lia; replace (n + i - n) with i by lia; exact e. }
  assert (Vt : forall a b, vlt a b -> vlt (tau a) (tau b)).
  { intros [la ia] [lb ib] [H|[El H]]; unfold tau, vlt; cbn [v_label v_index] in *.
    - left; destruct la, lb; exact H.
    - right; subst lb; destruct la; cbn; split; [reflexivity|lia|reflexivity|lia]. }
  split; [exact HJ|split].
  - destruct T as [|t T']; [destruct (Hne eq_refl)|].
    exists (mk_rvar None 0); rewrite Hj; cbn [List.length nth]; inversion HT as [|? ? Ht _]; subst.
    destruct t as [|u w b]; [destruct Ht|eexists; reflexivity].
  - destruct HSo as [Hsh Hp Hord Hlast Hroute Hpay Hhit Hbinj Hsrc]; split.
    + exact (proj1 HJ).
    + exact (sp1_spure _ _ _ _ HJ).
    + exact Hord.
    + exact Hlast.
    + intros x y e; refine (route_id_src _ (sg x) x y _ (Hroute _ _ (proj1 (Hjs x y e)))).
      unfold sg, bound; destruct (v_label x) eqn:El; [left; reflexivity|right; split; reflexivity].
    + intros x u n0 s0 i e; pose proof (sres_pure1 lenv labs ntm J x HJ) as P; rewrite e in P; destruct P as [P _]; discriminate P.
    + intros Hr y Hy; destruct (Hhit Hr y Hy) as [z Ez]; exists (tau z); exact (Hsj z y Ez).
    + exact Hbinj.
    + intros Hr x x' i j e e' Hij.
      destruct (Hsrc Hr (sg x) (sg x') i j (proj1 (Hjs _ _ e)) (proj1 (Hjs _ _ e')) Hij) as [x0 [E0 Hm]].
      exists (tau x0); split; [exact (Hsj _ _ E0)|].
      intros x'' e''; destruct (Hjs _ _ e'') as [E2 Ex]; rewrite Ex; exact (Vt _ _ (Hm _ E2)).
Qed.

Lemma join_sem T S1 K1 J E : Forall tterm T -> sp1 S1 -> join F T S1 = Some J -> ET F T = Some E ->
  keq (R (LS S1 :: K1)) (R K1) -> sp1 J -> forall v, feq (R (LS J :: K1) v) (R (LS E :: LS S1 :: K1) v).
Proof.
  intros HT HS EJ EE Hk HJ [l i]; destruct (ET_ok T E HT EE) as [HE HEs].
  rewrite (R_seg lenv J), (R_seg lenv E), (res_free lenv labs ntm J _ _ HJ), (res_free lenv labs ntm E _ _ HE).
  rewrite (join_sres T S1 J HS EJ), HEs; destruct l as [x|].
  - rewrite (R_seg lenv S1), (res_free lenv labs ntm S1 _ _ HS); destruct (sres S1 (mk_rvar (Some x) i)) as [y|[[u b] s']]; apply feq_refl.
  - destruct (i <? List.length T) eqn:Ei.
    + apply Nat.ltb_lt in Ei; pose proof (proj1 (Forall_forall _ _) HT _ (nth_In T (NVar LNone 0) Ei)) as Ht.
      destruct (nth i T (NVar LNone 0)) as [|u w b]; [destruct Ht|destruct Ht as [-> [-> _]]]; cbn [tres feq].
      split; [reflexivity|split; [reflexivity|intros y Hy; exact (feq_sym _ _ (Hk y (Hy eq_refl)))]].
    + rewrite (R_seg lenv S1), (res_free lenv labs ntm S1 _ _ HS).
      destruct (sres S1 (mk_rvar None (i - List.length T))) as [y|[[u b] s']]; apply feq_refl.
Qed.

(** *** The segments of the swap *)

Lemma find_named S1 x : find (fun e => label_eqb (lden (fst (fst e))) (Some x)) (named_ents S1)
                        = find (fun e => label_eqb (lden (fst (fst e))) (Some x)) (ents S1).
Proof.
  unfold named_ents; induction (ents S1) as [|e es IH]; [reflexivity|]; cbn [filter find].
  destruct (lexp_eqb (fst (fst e)) LNone) eqn:E; cbn [negb find].
  - apply lexp_eqb_eq in E; rewrite E; cbn; exact IH.
  - destruct (label_eqb _ _); [reflexivity|exact IH].
Qed.

Lemma named_ents_in S1 e : In e (named_ents S1) -> In e (ents S1) /\ fst (fst e) <> LNone.
Proof.
  unfold named_ents; intros H; apply filter_In in H as [H E]; split; [exact H|].
  intros E'; rewrite E' in E; discriminate.
Qed.

Lemma sres_nb X (f : lexp * tlist * nat -> lexp * (list ntgt * nat)) S1 s :
  sbuild F ((LNone, X) :: map f (named_ents S1)) = Some s -> (forall e, fst (f e) = fst (fst e)) ->
  forall l i, sres s (mk_rvar l i) =
    match l with
    | None => etgt lenv LNone (fst X) (snd X) i
    | Some x => match find (fun e => label_eqb (lden (fst (fst e))) (Some x)) (ents S1) with
                | Some e => etgt lenv (fst (f e)) (fst (snd (f e))) (snd (snd (f e))) i
                | None => inl (mk_rvar l i)
                end
    end.
Proof.
  intros E Hf l i; rewrite (sres_sbuild lenv F HF _ _ E l i); cbn [find fst].
  destruct l as [x|]; cbn [label_eqb Normalise.lden]; [|destruct X; reflexivity].
  rewrite (find_map_lab lenv f (fun e => fst (fst e)) fst _ (Some x) Hf), find_named.
  destruct (find _ (ents S1)) as [e|]; [|reflexivity]; cbn [option_map].
  destruct (f e) as [h [xs m]]; reflexivity.
Qed.

Definition shr (n : nat) (r : rvar + tm) : rvar + tm :=
  match r with inl y => match v_label y with None => inl (mk_rvar None (n + v_index y)) | Some _ => r end | _ => r end.

Lemma tres_shb n t : tres lenv (shb n t) = shr n (tres lenv t).
Proof.
  destruct t as [[|x|x] j|u w b]; cbn [shb tres shr]; try reflexivity.
Qed.

Lemma etgt_shb n h xs m i : h <> LNone -> etgt lenv h (map (shb n) xs) m i = shr n (etgt lenv h xs m i).
Proof.
  intros Hh; unfold etgt; rewrite length_map; destruct (i <? List.length xs) eqn:Ei.
  - apply Nat.ltb_lt in Ei; rewrite (nth_map_lt (shb n) xs i (NVar LNone 0)) by exact Ei; apply tres_shb.
  - cbn [shr v_label]; destruct (Normalise.lden lenv h) eqn:E; [reflexivity|destruct (Hh (lden_none lenv h E))].
Qed.

Lemma posof_some h j ts : forall p0 p, posof h j ts p0 = Some p ->
  p0 <= p /\ p - p0 < List.length ts /\ nth (p - p0) ts (NVar LNone 0) = NVar h j.
Proof.
  induction ts as [|t ts IH]; intros p0 p; cbn [posof]; [discriminate|].
  destruct t as [g k|u w b].
  - destruct (lexp_eqb g h && (k =? j)) eqn:E.
    + intros H; injection H as <-; apply andb_true_iff in E as [E1 E2]; apply lexp_eqb_eq in E1; apply Nat.eqb_eq in E2.
      subst; rewrite Nat.sub_diag; cbn; split; [lia|split; [lia|reflexivity]].
    + intros H; destruct (IH _ _ H) as [A [B C]]; split; [lia|].
      replace (p - p0) with (S (p - S p0)) by lia; cbn [List.length nth]; split; [lia|exact C].
  - intros H; destruct (IH _ _ H) as [A [B C]]; split; [lia|].
    replace (p - p0) with (S (p - S p0)) by lia; cbn [List.length nth]; split; [lia|exact C].
Qed.

Lemma posof_none h j ts : forall p0, posof h j ts p0 = None -> ~ In (NVar h j) ts.
Proof.
  induction ts as [|t ts IH]; intros p0; cbn [posof]; [intros _ []|].
  destruct t as [g k|u w b].
  - destruct (lexp_eqb g h && (k =? j)) eqn:E; [discriminate|].
    intros H [E'|Hin]; [|exact (IH _ H Hin)].
    injection E' as -> ->; rewrite (proj2 (lexp_eqb_eq h h) eq_refl), Nat.eqb_refl in E; discriminate.
  - intros H [E'|Hin]; [discriminate E'|exact (IH _ H Hin)].
Qed.

Lemma findpos_some h j es g p : findpos h j es = Some (g, p) ->
  exists ts m, In (g, ts, m) es /\ p < List.length (tl_list ts) /\ nth p (tl_list ts) (NVar LNone 0) = NVar h j.
Proof.
  induction es as [|[[g' ts] m] es IH]; cbn [findpos]; [discriminate|].
  destruct (posof h j (tl_list ts) 0) as [p'|] eqn:E.
  - intros H; injection H as <- <-; destruct (posof_some h j _ 0 p' E) as [_ [A B]]; rewrite Nat.sub_0_r in *.
    exists ts, m; split; [left; reflexivity|split; assumption].
  - intros H; destruct (IH H) as [ts' [m' [A B]]]; exists ts', m'; split; [right; exact A|exact B].
Qed.

Lemma findpos_none h j es : findpos h j es = None -> forall e, In e es -> ~ In (NVar h j) (tl_list (snd (fst e))).
Proof.
  induction es as [|[[g' ts] m] es IH]; cbn [findpos]; [intros _ e []|].
  destruct (posof h j (tl_list ts) 0) as [p'|] eqn:E; [discriminate|].
  intros H e [<-|Hin]; [exact (posof_none h j _ 0 E)|exact (IH H e Hin)].
Qed.

Lemma is_tgt_false h j ts : (forall t, In t ts -> t <> NVar h j) -> is_tgt h j ts = false.
Proof.
  intros H; unfold is_tgt; destruct (existsb _ ts) eqn:E; [|reflexivity].
  apply existsb_exists in E as [[g k|u w b] [Hin E]]; [|discriminate].
  apply andb_true_iff in E as [E1 E2]; apply lexp_eqb_eq in E1; apply Nat.eqb_eq in E2; subst.
  destruct (H _ Hin eq_refl).
Qed.

Lemma missing_in S1 h j : In (h, j) (missing S1) <->
  exists ts m, In (h, ts, m) (named_ents S1) /\ j < m /\ is_tgt h j (ntgts S1) = false.
Proof.
  unfold missing; rewrite in_flat_map; split.
  - intros [[[h' ts] m] [He Hin]]; apply filter_In in Hin as [Hin E]; apply in_map_iff in Hin as [j' [Ej Hj]].
    injection Ej as <- <-; apply in_seq in Hj; cbn [fst snd] in E; apply negb_true_iff in E.
    exists ts, m; split; [exact He|split; [lia|exact E]].
  - intros [ts [m [He [Hj E]]]]; exists (h, ts, m); split; [exact He|].
    apply filter_In; split; [apply in_map_iff; exists j; split; [reflexivity|apply in_seq; lia]|cbn [fst snd]; rewrite E; reflexivity].
Qed.

Lemma pidx_spec x l : In x l -> pidx x l < List.length l /\ nth (pidx x l) l (LNone, 0) = x.
Proof.
  induction l as [|y l IH]; [intros []|]; cbn [pidx].
  destruct (lexp_eqb (fst y) (fst x) && (snd y =? snd x)) eqn:E.
  - apply andb_true_iff in E as [E1 E2]; apply lexp_eqb_eq in E1; apply Nat.eqb_eq in E2.
    intros _; split; [cbn; lia|destruct x, y; cbn in *; subst; reflexivity].
  - intros [<-|Hin]; [rewrite (proj2 (lexp_eqb_eq _ _) eq_refl), Nat.eqb_refl in E; discriminate|].
    destruct (IH Hin) as [A B]; split; [cbn; lia|exact B].
Qed.

Lemma named_ents_labs S1 e : sp1 S1 -> In e (named_ents S1) -> In (fst (fst e)) labs.
Proof.
  intros HS He; apply named_ents_in in He as [He _]; destruct e as [[h ts] m].
  apply (sshape_labs lenv labs false S1 (proj1 HS) h (tl_list ts) m).
  rewrite <- ents_sents; apply (in_map (fun e => (fst (fst e), tl_list (snd (fst e)), snd e)) _ _ He).
Qed.

Lemma named_ne S1 e : In e (named_ents S1) -> lden (fst (fst e)) <> None.
Proof. intros He E; apply named_ents_in in He as [_ Hn]; exact (Hn (lden_none lenv _ E)). Qed.

Lemma sres_S1_ent S1 h ts m j : sp1 S1 -> In (h, ts, m) (ents S1) ->
  sres S1 (mk_rvar (lden h) j) = etgt lenv h (tl_list ts) m j.
Proof.
  intros HS Hin; rewrite (sres_ents lenv S1 (lden h) j).
  pose proof (find_ents_in lenv S1 (h, ts, m) (sshape_dist lenv labs _ _ (proj1 HS)) Hin) as Hf; cbn [fst] in Hf; rewrite Hf; reflexivity.
Qed.

Lemma mu_bound n S1 mu : mu_sw F n S1 = Some mu -> forall i,
  sres mu (mk_rvar None i) = inl (mk_rvar None (if i <? n then i else i - n + (n + List.length (missing S1)))).
Proof.
  intros E i; unfold mu_sw in E.
  rewrite (sres_nb _ _ S1 mu E ltac:(intros [[h ts] m]; reflexivity) None i); cbn [fst snd]; unfold etgt.
  rewrite length_map, length_seq; destruct (Nat.ltb_spec i n) as [H|H]; [|reflexivity].
  rewrite (nth_map_lt _ _ _ 0) by (rewrite length_seq; exact H); rewrite seq_nth by exact H; reflexivity.
Qed.

Lemma mu_named n S1 mu : sp1 S1 -> mu_sw F n S1 = Some mu -> forall x i,
  exists z, sres mu (mk_rvar (Some x) i) = inl z /\
   ((v_label z <> None /\ sres S1 z = inl (mk_rvar (Some x) i))
    \/ (exists idx, idx < List.length (missing S1) /\ z = mk_rvar None (n + idx)
                    /\ mk_rvar (lden (fst (nth idx (missing S1) (LNone, 0)))) (snd (nth idx (missing S1) (LNone, 0)))
                       = mk_rvar (Some x) i)).
Proof.
  intros HS E x i; unfold mu_sw in E.
  rewrite (sres_nb _ _ S1 mu E ltac:(intros [[h ts] m]; reflexivity) (Some x) i).
  destruct (find (fun e => label_eqb (lden (fst (fst e))) (Some x)) (ents S1)) as [[[h ts] m]|] eqn:Ef.
  - apply find_some in Ef as [Eh Hin]; cbn [fst] in Eh; apply label_eqb_eq in Eh.
    assert (He : In (h, ts, m) (named_ents S1)).
    { apply filter_In; split; [exact Hin|cbn; destruct (lexp_eqb h LNone) eqn:E'; [|reflexivity]].
      apply lexp_eqb_eq in E'; subst h; discriminate Eh. }
    cbn [fst snd]; unfold etgt; rewrite length_map, length_seq.
    destruct (Nat.ltb_spec i m) as [Hi|Hi].
    + rewrite (nth_map_lt _ _ _ 0) by (rewrite length_seq; exact Hi); rewrite seq_nth by exact Hi; cbn [Nat.add].
      unfold pre_sw; destruct (findpos h i (named_ents S1)) as [[g p]|] eqn:Efp.
      * eexists; split; [reflexivity|left].
        destruct (findpos_some h i _ g p Efp) as [ts' [m' [Hg [Hp Hn]]]].
        split; [exact (named_ne S1 _ Hg)|].
        rewrite (sres_S1_ent S1 g ts' m' p HS (proj1 (named_ents_in S1 _ Hg))); unfold etgt.
        rewrite (proj2 (Nat.ltb_lt _ _) Hp), Hn; cbn [tres]; rewrite Eh; reflexivity.
      * eexists; split; [reflexivity|right].
        assert (Hm : In (h, i) (missing S1)).
        { apply missing_in; exists ts, m; split; [exact He|split; [exact Hi|]].
          apply is_tgt_false; intros t Ht ->; unfold ntgts in Ht; apply in_flat_map in Ht as [e [Hes Ht]].
          exact (findpos_none h i _ Efp e Hes Ht). }
        destruct (pidx_spec (h, i) _ Hm) as [A B]; exists (pidx (h, i) (missing S1)); split; [exact A|split; [reflexivity|]].
        rewrite B; cbn [fst snd]; rewrite Eh; reflexivity.
    + eexists; split; [reflexivity|left]; cbn [v_label]; rewrite Eh; split; [discriminate|].
      rewrite <- Eh, (sres_S1_ent S1 h ts m _ HS Hin); unfold etgt; rewrite tlen_list.
      rewrite (proj2 (Nat.ltb_ge _ _)) by lia; do 2 f_equal; lia.
  - eexists; split; [reflexivity|left]; split; [discriminate|].
    rewrite (sres_ents lenv S1 (Some x) i), Ef; reflexivity.
Qed.

Lemma rho_ok S1 rho : sp1 S1 -> existsb is_term (ntgts S1) = false -> rho_sw F S1 = Some rho ->
  sshape lenv labs false rho /\ sren labs rho
  /\ (forall x i, sres rho (mk_rvar (Some x) i) = sres S1 (mk_rvar (Some x) i))
  /\ (forall i, sres rho (mk_rvar None i) =
                inl (if i <? List.length (missing S1)
                     then mk_rvar (lden (fst (nth i (missing S1) (LNone, 0)))) (snd (nth i (missing S1) (LNone, 0)))
                     else mk_rvar None (i - List.length (missing S1)))).
Proof.
  intros HS Ht E; unfold rho_sw in E.
  pose proof (sres_nb _ _ S1 rho E ltac:(intros e; reflexivity)) as Hr.
  split; [|split; [|split]].
  - destruct (sbuild_shape lenv labs F HF _ _ E) as [Hs _]; [|exact Hs].
    intros h xs m [Eh|Hin]; [injection Eh as <- _ _; exact HN|].
    apply in_map_iff in Hin as [e [Eh He]]; injection Eh as <- _ _; exact (named_ents_labs S1 e HS He).
  - destruct (sbuild_shape lenv labs F HF _ _ E) as [_ [Hts _]].
    { intros h xs m [Eh|Hin]; [injection Eh as <- _ _; exact HN|].
      apply in_map_iff in Hin as [e [Eh He]]; injection Eh as <- _ _; exact (named_ents_labs S1 e HS He). }
    apply Forall_forall; intros t Hin; destruct (Hts t Hin) as [h [xs [m [[Eh|Hes] Hx]]]].
    + injection Eh as <- <- <-; apply in_map_iff in Hx as [[g j] [<- Hx]]; cbn [fst snd ren_target].
      apply missing_in in Hx as [ts [m [He _]]]; exact (named_ents_labs S1 _ HS He).
    + apply in_map_iff in Hes as [e [Eh He]]; injection Eh as <- <- <-.
      assert (Hnt : In t (ntgts S1)) by (apply in_flat_map; exists e; split; assumption).
      assert (Hst : In t (stgts S1)) by (destruct e as [[h ts] m]; exact (ents_stgts S1 h ts m t (proj1 (named_ents_in S1 _ He)) Hx)).
      pose proof (proj1 (Forall_forall _ _) (proj2 HS) t Hst) as Hp.
      destruct t as [g j|u w b]; [exact Hp|exfalso].
      assert (existsb is_term (ntgts S1) = true) by (apply existsb_exists; exists (NBind u w b); split; [exact Hnt|reflexivity]).
      congruence.
  - intros x i; rewrite Hr, (sres_ents lenv S1 (Some x) i).
    destruct (find _ (ents S1)) as [[[h ts] m]|]; reflexivity.
  - intros i; rewrite Hr; cbn [fst snd]; unfold etgt; rewrite length_map.
    destruct (Nat.ltb_spec i (List.length (missing S1))) as [H|H]; [|do 2 f_equal; lia].
    rewrite (nth_map_lt _ _ _ (LNone, 0)) by exact H; reflexivity.
Qed.

Lemma bent_sres S1 : sp1 S1 -> forall j, sres S1 (mk_rvar None j) = etgt lenv LNone (tl_list (fst (bent F S1))) (snd (bent F S1)) j.
Proof.
  intros HS j; rewrite (bent_find lenv F HF S1), (sres_ents lenv S1 None j).
  destruct (find (fun e => label_eqb (lden (fst (fst e))) None) (ents S1)) as [[[h ts] m]|] eqn:Ef.
  - apply find_some in Ef as [Eh _]; cbn [fst] in Eh; apply label_eqb_eq in Eh.
    rewrite (lden_none lenv h Eh); reflexivity.
  - unfold etgt; cbn; do 2 f_equal; lia.
Qed.

Lemma lift_ok n S1 Z : sp1 S1 -> lift_sw F n S1 = Some Z ->
  sp1 Z /\ (forall x i, sres Z (mk_rvar (Some x) i) = shr n (sres S1 (mk_rvar (Some x) i)))
  /\ (forall i, sres Z (mk_rvar None i) = if i <? n then inl (mk_rvar None i) else shr n (sres S1 (mk_rvar None (i - n)))).
Proof.
  intros HS E; unfold lift_sw in E; pose proof (bent_sres S1 HS) as Hb.
  destruct (bent F S1) as [xs m] eqn:Eb; cbn [fst snd] in Hb.
  pose proof (sres_nb _ _ S1 Z E ltac:(intros e; reflexivity)) as Hr.
  assert (Tp : forall t, tp1 t -> tp1 (shb n t)) by (intros [[|y|y] j|u w b] Ht; exact Ht).
  split; [|split].
  - destruct (sbuild_shape lenv labs F HF _ _ E) as [Hs [Hts _]].
    { intros h xs0 m0 [Eh|Hin]; [injection Eh as <- _ _; exact HN|].
      apply in_map_iff in Hin as [e [Eh He]]; injection Eh as <- _ _; exact (named_ents_labs S1 e HS He). }
    split; [exact Hs|apply Forall_forall; intros t Hin; destruct (Hts t Hin) as [h [xs0 [m0 [[Eh|Hes] Hx]]]]].
    + injection Eh as <- <- <-; apply in_app_or in Hx as [Hx|Hx]; [apply in_map_iff in Hx as [j [<- _]]; exact HN|].
      apply in_map_iff in Hx as [t0 [<- Hx]]; apply Tp.
      pose proof (bent_find lenv F HF S1) as Eb'; rewrite Eb in Eb'.
      destruct (find (fun e => label_eqb (lden (fst (fst e))) None) (ents S1)) as [[[h ts] m']|] eqn:Ef;
        injection Eb' as -> ->; [|destruct Hx].
      apply find_some in Ef as [_ Hin']; exact (proj1 (Forall_forall _ _) (proj2 HS) t0 (ents_stgts S1 _ _ _ t0 Hin' Hx)).
    + apply in_map_iff in Hes as [[[h' ts] m'] [Eh He]]; injection Eh as <- <- <-.
      apply in_map_iff in Hx as [t0 [<- Hx]]; apply Tp.
      exact (proj1 (Forall_forall _ _) (proj2 HS) t0 (ents_stgts S1 _ _ _ t0 (proj1 (named_ents_in S1 _ He)) Hx)).
  - intros x i; rewrite Hr, (sres_ents lenv S1 (Some x) i).
    destruct (find (fun e => label_eqb (lden (fst (fst e))) (Some x)) (ents S1)) as [[[h ts] m']|] eqn:Ef; [|reflexivity].
    cbn [fst snd]; apply etgt_shb; intros ->; apply find_some in Ef as [Eh _]; discriminate Eh.
  - intros i; rewrite Hr, Hb; cbn [fst snd]; unfold etgt; rewrite length_app, !length_map, length_seq.
    destruct (Nat.ltb_spec i n) as [H|H].
    + rewrite (proj2 (Nat.ltb_lt _ _)) by lia; rewrite app_nth1 by (rewrite length_map, length_seq; exact H).
      rewrite (nth_map_lt _ _ _ 0) by (rewrite length_seq; exact H); rewrite seq_nth by exact H; reflexivity.
    + rewrite app_nth2 by (rewrite length_map, length_seq; exact H); rewrite length_map, length_seq.
      destruct (Nat.ltb_spec (i - n) (List.length (tl_list xs))) as [H2|H2].
      * rewrite (proj2 (Nat.ltb_lt i (n + List.length (tl_list xs)))) by lia; rewrite (nth_map_lt _ _ _ (NVar LNone 0)) by exact H2; apply tres_shb.
      * rewrite (proj2 (Nat.ltb_ge i (n + List.length (tl_list xs)))) by lia; cbn [shr v_label v_index Normalise.lden]; do 2 f_equal; lia.
Qed.

Lemma mu_shape n S1 mu : sp1 S1 -> mu_sw F n S1 = Some mu -> sshape lenv labs false mu /\ sren labs mu.
Proof.
  intros HS E; unfold mu_sw in E.
  destruct (sbuild_shape lenv labs F HF _ _ E) as [Hs [Hts _]].
  { intros h xs m [Eh|Hin]; [injection Eh as <- _ _; exact HN|].
    apply in_map_iff in Hin as [[[h' ts] m'] [Eh He]]; injection Eh as <- _ _; exact (named_ents_labs S1 _ HS He). }
  split; [exact Hs|apply Forall_forall; intros t Hin; destruct (Hts t Hin) as [h [xs [m [[Eh|Hes] Hx]]]]].
  - injection Eh as <- <- <-; apply in_map_iff in Hx as [j [<- _]]; exact HN.
  - apply in_map_iff in Hes as [[[h' ts] m'] [Eh He]]; injection Eh as <- <- <-.
    apply in_map_iff in Hx as [j [<- _]]; unfold pre_sw.
    destruct (findpos h' j (named_ents S1)) as [[g p]|] eqn:Ef; [|exact HN].
    destruct (findpos_some h' j _ g p Ef) as [ts' [m'' [Hg _]]]; exact (named_ents_labs S1 _ HS Hg).
Qed.

Lemma S1_named_var S1 x i : sp1 S1 -> existsb is_term (ntgts S1) = false ->
  exists y, sres S1 (mk_rvar (Some x) i) = inl y.
Proof.
  intros HS Ht; rewrite (sres_ents lenv S1 (Some x) i).
  destruct (find (fun e => label_eqb (lden (fst (fst e))) (Some x)) (ents S1)) as [[[h ts] m]|] eqn:Ef; [|eauto].
  apply find_some in Ef as [Eh Hin]; cbn [fst] in Eh; apply label_eqb_eq in Eh.
  assert (He : In (h, ts, m) (named_ents S1)).
  { apply filter_In; split; [exact Hin|cbn; destruct (lexp_eqb h LNone) eqn:E'; [|reflexivity]].
    apply lexp_eqb_eq in E'; subst h; discriminate Eh. }
  unfold etgt; destruct (Nat.ltb_spec i (List.length (tl_list ts))) as [Hi|Hi]; [|eauto].
  assert (Hn : In (nth i (tl_list ts) (NVar LNone 0)) (ntgts S1)).
  { apply in_flat_map; exists (h, ts, m); split; [exact He|apply nth_In, Hi]. }
  destruct (nth i (tl_list ts) (NVar LNone 0)) as [g j|u w b]; [eexists; reflexivity|exfalso].
  assert (existsb is_term (ntgts S1) = true) by (apply existsb_exists; exists (NBind u w b); split; [exact Hn|reflexivity]).
  congruence.
Qed.

Lemma swap_core T S1 K1 rho mu Z E W :
  Forall tterm T -> sp1 S1 -> sterm lenv S1 -> lw1 K1 -> segok S1 K1 -> existsb is_term (ntgts S1) = false ->
  rho_sw F S1 = Some rho -> mu_sw F (List.length T) S1 = Some mu -> lift_sw F (List.length T) S1 = Some Z ->
  ET F T = Some E -> gtP (R K1) (R (LS S1 :: K1)) ->
  (forall v, feq (R W v) (fs mu (fun z => fs E (fun z' => fs rho (R K1) z') z) v)) ->
  (forall y u b k, R W y = FTerm u b k -> gtP (R W) k) /\ sterm lenv Z /\ sp1 Z
  /\ forall v, feq (fs Z (R W) v) (fs E (R (LS S1 :: K1)) v).
Proof.
  intros HT HS HSt HK1 HSo Hnt Er Em Ez EE Hc HW; set (n := List.length T) in *.
  destruct (rho_ok S1 rho HS Hnt Er) as [Hrs [Hrr [Hrn Hrb]]].
  destruct (mu_shape n S1 mu HS Em) as [Hms Hmr].
  destruct (lift_ok n S1 Z HS Ez) as [HZ [Hzn Hzb]].
  destruct (ET_ok T E HT EE) as [HE HEs].
  set (k := List.length (missing S1)) in *.
  assert (Rw : forall y, feq (R W y) (fs E (fun z' => fs rho (R K1) z') (sv lenv mu y))).
  { intros y; rewrite <- (fs_ren lenv labs mu _ y Hmr); exact (HW y). }
  assert (Svm : forall y z, sres mu y = inl z -> sv lenv mu y = z).
  { intros y z e; rewrite (sres_ren lenv labs mu y Hmr) in e; injection e as e; exact e. }
  assert (Svr : forall y z, sres rho y = inl z -> sv lenv rho y = z).
  { intros y z e; rewrite (sres_ren lenv labs rho y Hrr) in e; injection e as e; exact e. }
  assert (Er_ : forall z, fs rho (R K1) z = R K1 (sv lenv rho z)) by (intros z; exact (fs_ren lenv labs rho _ z Hrr)).
  assert (Ee : forall K z, fs E K z = match sres E z with inl y => K y | inr (u, b, _) => FTerm u b K end)
    by (intros K z; exact (res_free lenv labs ntm E K z HE)).
  (* named variables *)
  assert (WS1 : forall x i, feq (R W (mk_rvar (Some x) i)) (R K1 (mk_rvar (Some x) i))).
  { intros x i; refine (feq_trans _ _ _ (Rw _) _).
    destruct (mu_named n S1 mu HS Em x i) as [z [Ez0 [[Hz Ez1]|[idx [Hidx [-> Ex]]]]]]; rewrite (Svm _ _ Ez0).
    - destruct z as [[zl|] zi]; [|destruct (Hz eq_refl)]; rewrite Ee, HEs; cbv beta iota; rewrite Er_.
      rewrite (Svr _ _ (eq_trans (Hrn zl zi) Ez1)); apply feq_refl.
    - rewrite Ee, HEs; fold n; rewrite (proj2 (Nat.ltb_ge (n + idx) n)) by lia; cbv beta iota.
      replace (n + idx - n) with idx by lia.
      rewrite Er_, (Svr _ _ (Hrb _)); fold k; rewrite (proj2 (Nat.ltb_lt idx k) Hidx), Ex; apply feq_refl. }
  assert (WS3 : forall j, feq (R W (mk_rvar None (n + j))) (R K1 (mk_rvar None j))).
  { intros j; refine (feq_trans _ _ _ (Rw _) _); rewrite (Svm _ _ (mu_bound n S1 mu Em (n + j))).
    rewrite (proj2 (Nat.ltb_ge (n + j) n)) by lia; rewrite Ee, HEs; fold n; fold k.
    rewrite (proj2 (Nat.ltb_ge (n + j - n + (n + k)) n)) by lia; cbv beta iota.
    rewrite Er_, (Svr _ _ (Hrb _)); fold k; rewrite (proj2 (Nat.ltb_ge (n + j - n + (n + k) - n) k)) by lia.
    replace (n + j - n + (n + k) - n - k) with j by lia; apply feq_refl. }
  assert (WS2 : forall i, i < n -> exists u, nth i T (NVar LNone 0) = NBind u (WEnd SNil) None
                                     /\ feq (R W (mk_rvar None i)) (FTerm u None (fun z => fs rho (R K1) z))).
  { intros i Hi; pose proof (proj1 (Forall_forall _ _) HT _ (nth_In T (NVar LNone 0) Hi)) as Ht.
    destruct (nth i T (NVar LNone 0)) as [|u w b] eqn:Et; [destruct Ht|destruct Ht as [-> [-> _]]].
    exists u; split; [reflexivity|]; refine (feq_trans _ _ _ (Rw _) _).
    rewrite (Svm _ _ (mu_bound n S1 mu Em i)), (proj2 (Nat.ltb_lt _ _) Hi), Ee, HEs; fold n.
    rewrite (proj2 (Nat.ltb_lt _ _) Hi), Et; apply feq_refl. }
  assert (Kw : keq (R W) (R K1)) by (intros [[x|] i] Hy; [exact (WS1 x i)|destruct (Hy eq_refl)]).
  assert (Kr : keq (fun z => fs rho (R K1) z) (R (LS S1 :: K1))).
  { intros [[x|] i] Hy; [|destruct (Hy eq_refl)]; rewrite (R_seg lenv), (res_free lenv labs ntm S1 _ _ HS), Er_.
    destruct (S1_named_var S1 x i HS Hnt) as [y Ey]; rewrite Ey, (Svr _ _ (eq_trans (Hrn x i) Ey)); apply feq_refl. }
  assert (Gp : gtP (R W) (fun z => fs rho (R K1) z))
    by exact (gtP_keq _ _ _ _ (keq_sym _ _ Kw) (keq_sym _ _ Kr) Hc).
  (* results of S1 after the rest, against the lifted segment after W *)
  assert (Res : forall r : rvar + tm, (match r with inl y => True | inr (_, b, s) => b = None /\ s = SNil end) ->
                  feq (match shr n r with inl y => R W y | inr (u, b, _) => FTerm u b (R W) end)
                      (match r with inl y => R K1 y | inr (u, b, _) => FTerm u b (R K1) end)).
  { intros [[[x|] j]|[[u b] s']] Hr; cbn [shr v_label v_index].
    - exact (WS1 x j).
    - exact (WS3 j).
    - destruct Hr as [-> ->]; cbn [feq]; split; [reflexivity|split; [reflexivity|]].
      intros y Hy; exact (Kw y (Hy eq_refl)). }
  split; [|split; [|split; [exact HZ|]]].
  - intros y u b k0 Ey; pose proof (Rw y) as F0; rewrite Ey in F0.
    rewrite Ee in F0; destruct (sres E (sv lenv mu y)) as [z|[[u' b'] s']] eqn:Ez0.
    + rewrite Er_ in F0; destruct (R K1 (sv lenv rho z)) as [|u1 b1 k1|] eqn:E1; cbn [feq] in F0; try contradiction.
      destruct F0 as [_ [<- Fk]].
      apply (gtP_keq _ _ _ _ (keq_sym _ _ Kw) (fun z0 Hz => feq_sym _ _ (Fk z0 (fun _ => Hz)))).
      exact (so_order _ _ _ _ _ _ _ HSo _ _ _ _ E1).
    + cbn [feq] in F0; destruct F0 as [_ [<- Fk]].
      exact (gtP_keq _ _ _ _ (keq_refl _) (fun z0 Hz => feq_sym _ _ (Fk z0 (fun _ => Hz))) Gp).
  - destruct HSt as [[[x|] i] [t Ex]].
    + exists (mk_rvar (Some x) i), t; rewrite Hzn, Ex; reflexivity.
    + exists (mk_rvar None (n + i)), t; rewrite Hzb, (proj2 (Nat.ltb_ge _ _)) by lia.
      replace (n + i - n) with i by lia; rewrite Ex; reflexivity.
  - intros [[x|] i]; rewrite (res_free lenv labs ntm Z _ _ HZ), Ee, HEs.
    + rewrite Hzn, (R_seg lenv), (res_free lenv labs ntm S1 _ _ HS).
      apply Res; exact (sres_pure1 lenv labs ntm S1 _ HS).
    + rewrite Hzb; fold n; destruct (Nat.ltb_spec i n) as [Hi|Hi].
      * destruct (WS2 i Hi) as [u [Et Fw]]; rewrite Et; cbn [tres].
        refine (feq_trans _ _ _ Fw _); cbn [feq]; split; [reflexivity|split; [reflexivity|]].
        intros y Hy; exact (Kr y (Hy eq_refl)).
      * rewrite (R_seg lenv), (res_free lenv labs ntm S1 _ _ HS).
        apply Res; exact (sres_pure1 lenv labs ntm S1 _ HS).
Qed.

(** *** A first layer that sends a named variable to a term is above its rest *)

Lemma omax_some xs : (forall x, In x xs -> exists k, x = Some k) -> exists n, omax xs = Some n.
Proof.
  induction xs as [|x xs IH]; intros H; [exists 0; reflexivity|cbn [omax]].
  destruct (H x (or_introl eq_refl)) as [k ->]; destruct (IH (fun y Hy => H y (or_intror Hy))) as [n ->]; eauto.
Qed.

Lemma sp1_tail h ts m s0 : sp1 (SEnt h ts m s0) -> sp1 s0.
Proof.
  intros [[Hso Hf] Ht]; cbn [sents] in Hso, Hf; inversion Hso; inversion Hf; subst.
  split; [split; assumption|rewrite stgts_cons, Forall_app in Ht; exact (proj2 Ht)].
Qed.

Lemma depth_total W : lw1 W ->
  (forall h i, In h labs -> exists n, vdepth F W h i = Some n)
  /\ (forall all c, (forall p, In p c -> In (fst p) labs) -> exists n, hreg F W all c = Some n).
Proof.
  induction W as [|[s0|L a] r IH]; intros Hw.
  - split; intros; eexists; reflexivity.
  - inversion Hw as [|? ? Hs Hr]; subst; destruct (IH Hr) as [V H]; split.
    + intros h i Hh; cbn [vdepth]; destruct (seg_tgt_total lenv labs ntm F HF Htot s0 h i Hs Hh) as [t [Et Ht]]; rewrite Et.
      destruct t as [g j|u w b]; [exact (V g j Ht)|destruct Ht as [-> [-> _]]].
      destruct (H false [] (fun p Hp => match Hp with end)) as [n ->]; eexists; reflexivity.
    + intros all c Hc; cbn [hreg]; apply omax_some; intros x [<-|Hx].
      * apply H; intros p Hp; clear -Hp Hc Hs.
        induction s0 as [|h ts m s' IHs] using seg_spine; cbn [cbound] in Hp; [exact (Hc p Hp)|].
        destruct Hp as [<-|Hp]; [|exact (IHs (sp1_tail _ _ _ _ Hs) Hp)].
        cbn [fst]; apply (sshape_labs lenv labs false _ (proj1 Hs) h (tl_list ts) m); left; reflexivity.
      * destruct (H false [] (fun p Hp => match Hp with end)) as [nt Ent]; rewrite Ent in Hx.
        clear H; revert Hx; generalize c; induction s0 as [|h ts m s' IHs] using seg_spine; intros c0 Hx; [destruct Hx|].
        cbn [ehd] in Hx; apply in_app_or in Hx as [Hx|Hx].
        -- destruct (isall all h); [|destruct Hx]; apply in_map_iff in Hx as [i [<- Hi]]; apply in_seq in Hi.
           assert (Hin : In (tnth ts i) (stgts (SEnt h ts m s'))) by (rewrite stgts_cons; apply in_or_app; left; apply tnth_in; lia).
           pose proof (proj1 (Forall_forall _ _) (proj2 Hs) _ Hin) as Ht.
           destruct (tnth ts i) as [g j|u w b]; cbn [tdep]; [exact (V g j Ht)|destruct Ht as [-> [-> _]]; cbn [option_map]; eauto].
        -- apply (IHs ltac:(constructor; [exact (sp1_tail _ _ _ _ Hs)|exact Hr]) (sp1_tail _ _ _ _ Hs) c0 Hx).
  - inversion Hw as [|? ? HL Hr]; subst; destruct (IH Hr) as [V H]; split.
    + intros h i Hh; cbn [vdepth].
      destruct (lcnt F h L) as [c|] eqn:Ec; [|destruct (lcnt_total labs F Htot L h (proj2 HL) Hh Ec)].
      destruct (i <? c); [exact (V h i Hh)|apply H; intros p Hp; exact (proj1 (proj1 (Forall_forall _ _) (proj2 HL) p Hp))].
    + intros all c Hc; cbn [hreg]; apply omax_some; intros x [<-|Hx].
      * apply H; intros p Hp; exact (proj1 (proj1 (Forall_forall _ _) (proj2 HL) p Hp)).
      * apply in_flat_map in Hx as [p [Hp Hx]]; destruct (isall all (fst p)); [|destruct Hx].
        apply in_map_iff in Hx as [i [<- _]]; exact (V _ i (proj1 (proj1 (Forall_forall _ _) (proj2 HL) p Hp))).
Qed.

Lemma named_term_gt S1 K1 : lnf (LS S1 :: K1) -> lw1 (LS S1 :: K1) -> existsb is_term (ntgts S1) = true ->
  gtP (R (LS S1 :: K1)) (R K1).
Proof.
  intros Hl Hw Ht; inversion Hw as [|? ? HS HK1]; subst.
  apply existsb_exists in Ht as [t [Hin Et]]; unfold ntgts in Hin; apply in_flat_map in Hin as [[[h ts] m] [He Hin]].
  cbn [fst snd] in Hin; apply In_nth with (d := NVar LNone 0) in Hin as [i [Hi Ei]].
  pose proof (named_ents_in S1 _ He) as [He' Hh].
  assert (Ex : sres S1 (mk_rvar (lden h) i) = tres lenv t).
  { rewrite (sres_S1_ent S1 h ts m i HS He'); unfold etgt; rewrite (proj2 (Nat.ltb_lt _ _) Hi), Ei; reflexivity. }
  pose proof (proj1 (Forall_forall _ _) (proj2 HS) t (ents_stgts S1 h ts m t He' ltac:(rewrite <- Ei; apply nth_In, Hi))) as Hp.
  destruct t as [|u w b]; [discriminate Et|destruct Hp as [-> [-> _]]].
  destruct (proj2 (depth_total K1 HK1) false [] (fun p Hp => match Hp with end)) as [h1 Eh].
  pose proof (hle_iff lenv labs Hinj F HF K1 h1 (lw1_lgood _ HK1) Eh) as Hle.
  right; exists (natl K1); split; [exact (deep_R lenv (LS S1 :: K1))|split; [exact (deep_R lenv K1)|left]].
  exists h1; split; [apply Hle; lia|intros H].
  assert (Hn : dom false (mk_rvar (lden h) i)) by (right; cbn; intros E; exact (Hh (lden_none lenv h E))).
  specialize (H _ Hn); rewrite (R_seg lenv), (res_free lenv labs ntm S1 _ _ HS), Ex in H; cbn [tres dle] in H.
  destruct h1 as [|h1]; [exact H|].
  assert (H' : hle false h1 (R K1)) by (intros y Hy; apply H; exact Hy).
  apply Hle in H'; lia.
Qed.

Theorem bcore_ok fuel : forall T K K' E, Forall tterm T -> T <> [] -> lnf K -> lw1 K -> ET F T = Some E ->
  bcore F ntm fuel T K = Some K' -> lnf K' /\ lw1 K' /\ forall v, feq (R K' v) (R (LS E :: K) v).
Proof.
  induction fuel as [|fuel' IH]; intros T K K' E HT Hne Hl Hw EE; [discriminate|cbn [bcore]; rewrite EE].
  destruct (ET_ok T E HT EE) as [HE HEs].
  assert (HEt : sterm lenv E).
  { destruct T as [|t T']; [destruct (Hne eq_refl)|]; exists (mk_rvar None 0); rewrite HEs; cbn [List.length nth Nat.ltb].
    inversion HT as [|? ? Ht _]; subst; destruct t as [|u w b]; [destruct Ht|eexists; reflexivity]. }
  assert (New : forall K0 K0', lnf K0 -> lw1 K0 -> (forall y u b k, R K0 y = FTerm u b k -> gtP (R K0) k) ->
                  forall Z, sp1 Z -> sterm lenv Z ->
                  layer F ntm Z K0 = Some K0' -> lnf K0' /\ lw1 K0' /\ forall v, feq (R K0' v) (R (LS Z :: K0) v)).
  { intros K0 K0' H1 H2 H3 Z HZ HZt H4; exact (layer_ok lenv labs Hinj HN ntm F HF Htot Z K0 K0' H1 H2 HZ HZt H3 H4). }
  destruct K as [|[S1|L a] K1]; [exact (New _ _ Hl Hw (hor_noterm _ Hl Hw I) E HE HEt)| |exact (New _ _ Hl Hw (hor_noterm _ Hl Hw I) E HE HEt)].
  destruct (has_terms S1) eqn:Ht; [|exact (New _ _ Hl Hw (hor_noterm _ Hl Hw Ht) E HE HEt)].
  destruct (existsb is_term (ntgts S1)) eqn:Hnt;
    [exact (New _ _ Hl Hw (hor_gt S1 K1 Hl Hw Ht (named_term_gt S1 K1 Hl Hw Hnt)) E HE HEt)|].
  assert (Suf1 : suf (LS S1 :: K1) (List.length (LS S1 :: K1)) = LS S1 :: K1) by apply suf_all.
  assert (Suf2 : suf (LS S1 :: K1) (List.length K1) = K1) by (rewrite (suf_cons _ _ _ (le_n _)); apply suf_all).
  destruct (pcmp F (LS S1 :: K1) (List.length (LS S1 :: K1)) (List.length K1)) as [c|] eqn:Ec; [|discriminate].
  pose proof (pcmp_sound lenv labs Hinj F HF route_id (num_first lenv) (LS S1 :: K1) (List.length (LS S1 :: K1)) (List.length K1) c Hl
                (lw1_lgood _ Hw) (le_n _) ltac:(cbn; lia) Ec) as Hc.
  rewrite Suf1, Suf2 in Hc.
  inversion Hw as [|? ? HS HK1]; subst.
  pose proof Hl as Hl0; destruct Hl0 as [_ [Hl1 [[HSt HSo]|[_ [Hren _]]]]]; [|rewrite (sren_noterms labs S1 Hren) in Ht; discriminate].
  destruct c; [| |exact (New _ _ Hl Hw (hor_gt S1 K1 Hl Hw Ht Hc) E HE HEt)].
  - destruct (join F T S1) as [J|] eqn:EJ; [|discriminate]; cbn [option_map]; intros EK; injection EK as <-.
    destruct (join_ok T S1 K1 J HT Hne HS HSo EJ) as [HJ [HJt HJo]].
    split; [split; [intros ->; destruct HJt as [x [t Ex]]; discriminate Ex|split; [exact Hl1|left; split; assumption]]|].
    split; [constructor; assumption|exact (join_sem T S1 K1 J E HT HS EJ EE Hc HJ)].
  - destruct (rho_sw F S1) as [rho|] eqn:Er; [|discriminate].
    destruct (mu_sw F (List.length T) S1) as [mu|] eqn:Em; [|discriminate].
    destruct (lift_sw F (List.length T) S1) as [Z|] eqn:Ez; [|discriminate].
    destruct (rcons F ntm rho K1) as [K1'|] eqn:EK1; [|discriminate].
    destruct (bcore F ntm fuel' T K1') as [Y|] eqn:EY; [|discriminate].
    destruct (rcons F ntm mu Y) as [W|] eqn:EW; [|discriminate]; intros EL.
    destruct (rho_ok S1 rho HS Hnt Er) as [Hrs [Hrr _]].
    destruct (rcons_ok lenv labs Hinj HN ntm F HF Htot K1 rho K1' Hl1 HK1 Hrs Hrr EK1) as [Hl1' [Hw1' Sem1]].
    destruct (IH T K1' Y E HT Hne Hl1' Hw1' EE EY) as [HlY [HwY SemY]].
    destruct (mu_shape _ S1 mu HS Em) as [Hms Hmr].
    destruct (rcons_ok lenv labs Hinj HN ntm F HF Htot Y mu W HlY HwY Hms Hmr EW) as [HlW [HwW SemW]].
    assert (HW : forall v, feq (R W v) (fs mu (fun z => fs E (fun z' => fs rho (R K1) z') z) v)).
    { intros v; refine (feq_trans _ _ _ (SemW v) _); rewrite (R_seg lenv).
      apply (fs_cong lenv labs ntm mu _ _ v (sren_sp1 lenv labs ntm mu Hms Hmr)); intros y.
      refine (feq_trans _ _ _ (SemY y) _); rewrite (R_seg lenv).
      apply (fs_cong lenv labs ntm E _ _ y HE); intros z; exact (Sem1 z). }
    destruct (swap_core T S1 K1 rho mu Z E W HT HS HSt HK1 HSo Hnt Er Em Ez EE Hc HW) as [Hor [HZt [HZ SemZ]]].
    destruct (New W K' HlW HwW Hor Z HZ HZt EL) as [A [B C]].
    split; [exact A|split; [exact B|intros v]].
    refine (feq_trans _ _ _ (C v) _); rewrite (R_seg lenv Z), (R_seg lenv E); exact (SemZ v).
Qed.

End BcoreOk.
