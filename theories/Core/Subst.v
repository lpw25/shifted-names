(** * Substitution for any syntax

    Given a syntax (Syntax.v), [apply a : morph N M] turns a scoped
    adjustment into the morphism [kleisli] needs, and
    [subst a t := kleisli (apply a) ext_here t].

    [apply] is structural recursion on the adjustment: lookups pass what
    they find to a continuation (Lookup.v), so a payload's adjustment is a
    visible subterm, together with the base it is stored over.  Under [d]
    binders it does offset arithmetic on [d]; it never computes a [lift].
    Scoping proofs are built from the location proofs the lookups provide,
    so nothing is tested at runtime. *)

From Stdlib Require Import PArith Arith List Lia Bool StrictProp.
From ShiftedNames.Core Require Import Trie Label Var Counts Based Skew ATrie Repr Point Deep Compose Normalise Conv Names
  Lookup Adjustment Laws Scoped Indexed Syntax.
Import ListNotations.

(** ** Arithmetic on variables *)

(** Moving a variable out from under [k] bound binders, and back in. *)
Definition down (k : nat) (w : rvar) : rvar :=
  match v_label w with None => mk_rvar None (v_index w - k) | Some _ => w end.

Definition up (k : nat) (w : rvar) : rvar :=
  match v_label w with None => mk_rvar None (k + v_index w) | Some _ => w end.

(** ** Facts about locations and scoping *)

Section Facts.

Context {T : Type}.

Local Notation nadj := (@nadj T).
Local Notation entry := (@entry T).
Local Notation target := (@target T).

(** Payload adjustments in scope [M]. *)
Definition pok (M : nat) (x : nadj) : bool := nwfc true (fun r => r) x && pscopedc M (fun r => r) x.

(** A payload adjustment with its root read through [rt] (a lazy base,
    Lookup.v). *)
Definition absn (rt : counts -> lbase) (x : nadj) : nadj :=
  match x with NAdj r es => NAdj (lcounts (rt r)) es end.

Lemma pok_wf M x : pok M x = true -> nwf true x.
Proof. unfold pok; rewrite andb_true_iff; intros [H _]; exact H. Qed.

(** Where a lookup ends up: an entry found over base [Be]. *)
Lemma found_entry Q R (es : atrie entry) k Be h ts len p :
  nlocal Q (NAdj R es) ->
  option_map (unshift R) (aget k es) = Some (unshift Be (Entry h ts len p)) ->
  label_key h = k /\ Q h = true /\ kgood ts /\ klength ts = len
  /\ (forall i Bt t, i < len -> option_map (unshift Be) (knth ts i) = Some (unshift Bt t) ->
                     napply (NAdj R es) (mk_rvar h i) = tresult (unshift Bt t))
  /\ (forall i, len <= i -> napply (NAdj R es) (mk_rvar h i)
                           = inl (mk_rvar h (dval Be (label_key h) + (i - len + p))))
  /\ (forall i, i < len -> knth ts i <> None).
Proof.
  intros Hl E; pose proof Hl as [_ [_ [Hent _]]].
  destruct (aget k es) as [e0|] eqn:E0; [|discriminate]; cbn in E; injection E as E.
  destruct e0 as [h0 ts0 len0 p0]; destruct (Hent _ _ E0) as [[Hk [G0 [Hl0 _]]] [HQ _]].
  cbn [unshift entry_based eunshift] in E; injection E as -> Ets -> Ep.
  assert (G : kgood ts) by (apply (kgood_unlift Be); rewrite <- Ets; apply kgood_klift, G0).
  assert (Hlen : klength ts = len) by (rewrite <- Hl0, <- (klength_klift R ts0), Ets, klength_klift; reflexivity).
  subst k; split; [reflexivity|split; [exact HQ|split; [exact G|split; [exact Hlen|split; [|split]]]]].
  - intros i Bt t Hi Et; cbn [napply v_label v_index]; rewrite E0; cbn [eapply].
    destruct (Nat.ltb_spec i len); [|lia].
    rewrite <- (knth_klift Be ts i G), <- Ets, knth_klift in Et by exact G0.
    destruct (knth ts0 i) as [t0|]; [|discriminate]; cbn in Et; injection Et as Et.
    rewrite Et; reflexivity.
  - intros i Hi; cbn [napply v_label v_index]; rewrite E0; cbn [eapply].
    destruct (Nat.ltb_spec i len); [lia|]; f_equal; f_equal; lia.
  - intros i Hi En; rewrite knth_spec in En by apply kgood_shape, G.
    apply nth_error_None in En; rewrite <- (klength_spec _ (kgood_shape _ G)) in En; lia.
Qed.

Lemma found_none R (es : atrie entry) l i :
  aget (label_key l) es = None -> napply (NAdj R es) (mk_rvar l i) = inl (mk_rvar l (dval R (label_key l) + i)).
Proof. intros E; cbn [napply v_label v_index]; rewrite E; reflexivity. Qed.

(** What the scoping of a payload says about its results. *)
Lemma pay_result M x v :
  pok M x = true -> v_label v <> None ->
  match napply x v with
  | inl w => wf_var M w = true
  | inr (u, ρ) => pok M ρ = true
  end.
Proof.
  intros Hx Hv; unfold pok in Hx; apply andb_true_iff in Hx as [Hw Hs].
  set (ρ := mk_rpadj x (Is_true_s_intro Hw)).
  pose proof (proj1 (pscoped_spec M ρ) Hs v Hv) as H; unfold rpapply in H; cbn [rpadj_n ρ] in H.
  destruct (napply x v) as [w|[u y]] eqn:E; [exact H|].
  cbn [rpack result_wf rwf] in H.
  assert (Hy : nwf true y) by (apply (nwf_payload true x v u y Hw); [destruct (v_label v); [reflexivity|contradiction]|exact E]).
  rewrite rpadj_n_to_padj in H by exact Hy; unfold pok; rewrite Hy, H; reflexivity.
Qed.

(** What the scoping of an adjustment says about its results. *)
Lemma top_result {N M} (a : adj T N M) v :
  wf_var N v = true ->
  match napply (radj_n (adj_raw a)) v with
  | inl w => wf_var M w = true
  | inr (u, ρ) => pok M ρ = true
  end.
Proof.
  intros Hv; pose proof (proj2 (proj1 (scoped_spec N M (adj_raw a)) (adj_scoped a)) v Hv) as H.
  unfold rapply in H; destruct (napply _ v) as [w|[u y]] eqn:E; [exact H|].
  assert (Hy : nwf true y) by apply (nwf_payload false _ v u y (radj_wf (adj_raw a)) eq_refl E).
  cbn [rpack result_wf rwf] in H; rewrite rpadj_n_to_padj in H by exact Hy.
  unfold pok; rewrite Hy, H; reflexivity.
Qed.

Lemma wf_eq L L' w : L = L' -> wf_var L' w = true -> wf_var L w = true.
Proof. intros ->; auto. Qed.

Lemma up_wf M d w : wf_var M w = true -> wf_var (d + M) (up d w) = true.
Proof.
  destruct w as [[x|] i]; cbn; [reflexivity|].
  intros H; apply Nat.ltb_lt in H; apply Nat.ltb_lt; lia.
Qed.

Lemma inner_wf {N M K L} (e : ext N M K L) rv :
  v_label rv = None -> v_index rv < ext_depth e -> wf_var L rv = true.
Proof.
  intros Hl Hi; destruct rv as [h i]; cbn [v_label v_index] in Hl, Hi; subst h.
  unfold wf_var; cbn [v_label v_index]; apply Nat.ltb_lt.
  pose proof (ext_depth_L e); lia.
Qed.

Lemma down_wf {N M K L} (e : ext N M K L) rv :
  wf_var K rv = true -> (v_label rv = None -> ext_depth e <= v_index rv) ->
  wf_var N (down (ext_depth e) rv) = true.
Proof.
  pose proof (ext_depth_K e); destruct rv as [[x|] i]; cbn; [reflexivity|].
  intros H1 H2; specialize (H2 eq_refl); apply Nat.ltb_lt in H1; apply Nat.ltb_lt; lia.
Qed.

End Facts.

(** ** Strict wrappers used inside [apply]

    From where a lookup found something, and the invariants, the scoping of
    the result. *)

Section Wrappers.

Context {T : Type}.

Local Notation nadj := (@nadj T).
Local Notation entry := (@entry T).
Local Notation target := (@target T).

Lemma pok_local M (X : nadj) : pok M X = true -> nlocal Qnamed X.
Proof. intros H; apply (nwf_local true), (pok_wf M), H. Qed.

Lemma W_pinner {L0 K L} (e : ext 0 L0 K L) (rv : rvar) (Hv : Is_true_s (wf_var K rv))
  (Hl : v_label rv = None) : Is_true_s (wf_var L rv).
Proof.
  apply Is_true_s_intro; apply Is_true_s_elim in Hv.
  apply (inner_wf e); [exact Hl|].
  pose proof (ext_depth_K e); destruct rv as [h i]; cbn in *; subst h.
  apply Nat.ltb_lt in Hv; cbn in Hv; lia.
Qed.

Lemma W_pHL {L0 K L} Mρ s (e : ext 0 L0 K L) (HL : Is_true_s (Nat.eqb L0 (s + Mρ))) :
  Is_true_s (Nat.eqb L ((s + ext_depth e) + Mρ)).
Proof.
  apply Is_true_s_intro; apply Is_true_s_elim, Nat.eqb_eq in HL; apply Nat.eqb_eq.
  pose proof (ext_depth_L e); lia.
Qed.

(** A variable found as a target. *)
Lemma W_pvar Mρ s L0 {K L} (e : ext 0 L0 K L) R (es : atrie entry) y i Be h ts len p Bt y' j
  (HL : Is_true_s (Nat.eqb L0 (s + Mρ))) (Hx : Is_true_s (pok Mρ (NAdj R es)))
  (H1 : Squash (option_map (unshift R) (aget (label_key (Some y)) es) = Some (unshift (lcounts Be) (Entry h ts len p))))
  (Hi : i < len)
  (H2 : Squash (option_map (unshift (lcounts Be)) (knth ts i) = Some (unshift (lcounts Bt) (TVar y' j)))) :
  Is_true_s (wf_var L (up (s + ext_depth e) (mk_rvar y' (ldval Bt (label_key y') + j)))).
Proof.
  rewrite ldval_spec;
  destruct H1 as [H1], H2 as [H2]; apply Is_true_s_elim in Hx, HL; apply Nat.eqb_eq in HL.
  apply Is_true_s_intro; pose proof (pok_local _ _ Hx) as Hl.
  destruct (found_entry _ _ _ _ _ _ _ _ _ Hl H1) as [Hk [_ [_ [_ [Ht _]]]]].
  apply label_key_inj in Hk; subst h.
  pose proof (pay_result Mρ _ (mk_rvar (Some y) i) Hx ltac:(discriminate)) as Hr.
  rewrite (Ht i (lcounts Bt) _ Hi H2) in Hr; cbn in Hr.
  pose proof (ext_depth_L e); apply (wf_eq L ((s + ext_depth e) + Mρ)); [lia|apply up_wf, Hr].
Qed.

(** A payload found as a target. *)
Lemma W_ppay Mρ R (es : atrie entry) y i Be h ts len p Bt u (rho : nadj)
  (Hx : Is_true_s (pok Mρ (NAdj R es)))
  (H1 : Squash (option_map (unshift R) (aget (label_key (Some y)) es) = Some (unshift (lcounts Be) (Entry h ts len p))))
  (Hi : i < len)
  (H2 : Squash (option_map (unshift (lcounts Be)) (knth ts i) = Some (unshift (lcounts Bt) (TBind u rho)))) :
  Is_true_s (pok Mρ (absn (LAdd Bt) rho)).
Proof.
  destruct H1 as [H1], H2 as [H2]; apply Is_true_s_elim in Hx.
  apply Is_true_s_intro; pose proof (pok_local _ _ Hx) as Hl.
  destruct (found_entry _ _ _ _ _ _ _ _ _ Hl H1) as [Hk [_ [_ [_ [Ht _]]]]].
  apply label_key_inj in Hk; subst h.
  pose proof (pay_result Mρ _ (mk_rvar (Some y) i) Hx ltac:(discriminate)) as Hr.
  rewrite (Ht i (lcounts Bt) _ Hi H2) in Hr; destruct rho as [r0 es0]; exact Hr.
Qed.

(** Pass-through. *)
Lemma W_ppass Mρ s L0 {K L} (e : ext 0 L0 K L) R (es : atrie entry) y i Be h ts len p
  (HL : Is_true_s (Nat.eqb L0 (s + Mρ))) (Hx : Is_true_s (pok Mρ (NAdj R es)))
  (H1 : Squash (option_map (unshift R) (aget (label_key (Some y)) es) = Some (unshift (lcounts Be) (Entry h ts len p))))
  (Hi : ~ i < len) :
  Is_true_s (wf_var L (up (s + ext_depth e) (mk_rvar h (ldval Be (label_key h) + (i - len + p))))).
Proof.
  rewrite ldval_spec;
  destruct H1 as [H1]; apply Is_true_s_elim in Hx, HL; apply Nat.eqb_eq in HL.
  apply Is_true_s_intro; pose proof (pok_local _ _ Hx) as Hl.
  destruct (found_entry _ _ _ _ _ _ _ _ _ Hl H1) as [Hk [_ [_ [_ [_ [Hp _]]]]]].
  apply label_key_inj in Hk; subst h.
  pose proof (pay_result Mρ _ (mk_rvar (Some y) i) Hx ltac:(discriminate)) as Hr.
  rewrite (Hp i ltac:(lia)) in Hr; cbn in Hr.
  pose proof (ext_depth_L e); apply (wf_eq L ((s + ext_depth e) + Mρ)); [lia|apply up_wf, Hr].
Qed.

(** No entry. *)
Lemma W_pnone Mρ s L0 {K L} (e : ext 0 L0 K L) R (es : atrie entry) y i
  (HL : Is_true_s (Nat.eqb L0 (s + Mρ))) (Hx : Is_true_s (pok Mρ (NAdj (lcounts R) es)))
  (H1 : Squash (aget (label_key (Some y)) es = None)) :
  Is_true_s (wf_var L (up (s + ext_depth e) (mk_rvar (Some y) (ldval R (label_key (Some y)) + i)))).
Proof.
  rewrite ldval_spec; destruct H1 as [H1]; apply Is_true_s_elim in Hx, HL; apply Nat.eqb_eq in HL; apply Is_true_s_intro.
  pose proof (pay_result Mρ _ (mk_rvar (Some y) i) Hx ltac:(discriminate)) as Hr.
  rewrite found_none in Hr by exact H1; cbn in Hr.
  pose proof (ext_depth_L e); apply (wf_eq L ((s + ext_depth e) + Mρ)); [lia|apply up_wf, Hr].
Qed.

(** A target is always there below the length. *)
Lemma W_absurd Q R (es : atrie entry) k i Be h ts len p
  (Hl : Squash (nlocal Q (NAdj R es)))
  (H1 : Squash (option_map (unshift R) (aget k es) = Some (unshift (lcounts Be) (Entry h ts len p))))
  (Hi : i < len) (H2 : Squash (knth ts i = None)) : sEmpty.
Proof.
  destruct Hl as [Hl], H1 as [H1], H2 as [H2].
  destruct (found_entry _ _ _ _ _ _ _ _ _ Hl H1) as [_ [_ [_ [_ [_ [_ Hn]]]]]].
  exfalso; exact (Hn i Hi H2).
Qed.

Lemma pok_squash Mρ (X : nadj) (Hx : Is_true_s (pok Mρ X)) : Squash (nlocal Qnamed X).
Proof. apply Is_true_s_elim in Hx; exact (squash (pok_local _ _ Hx)). Qed.

End Wrappers.

(** At the top level. *)

Section TopWrappers.

Context {T : Type}.

Local Notation nadj := (@nadj T).
Local Notation entry := (@entry T).

Lemma rel_some (rv : rvar) y : v_label rv = Some y -> v_label rv = None -> forall d, d <= v_index rv.
Proof. congruence. Qed.

Lemma rel_ge (rv : rvar) d : ~ v_index rv < d -> v_label rv = None -> d <= v_index rv.
Proof. intros H _; lia. Qed.

Lemma W_tinner {N M K L} (e : ext N M K L) (rv : rvar) (Hl : v_label rv = None)
  (Hb : v_index rv < ext_depth e) : Is_true_s (wf_var L rv).
Proof. apply Is_true_s_intro, (inner_wf e); [exact Hl|exact Hb]. Qed.

Lemma W_tdown {N M K L} (e : ext N M K L) (rv : rvar) (Hv : Is_true_s (wf_var K rv))
  (Hrel : v_label rv = None -> ext_depth e <= v_index rv) :
  wf_var N (down (ext_depth e) rv) = true.
Proof. apply down_wf; [apply Is_true_s_elim, Hv|exact Hrel]. Qed.

Lemma W_tHL {N M K L} (e : ext N M K L) : Is_true_s (Nat.eqb L (ext_depth e + M)).
Proof. apply Is_true_s_intro, Nat.eqb_eq, ext_depth_L. Qed.

Local Notation rootA a := (nroot (radj_n (adj_raw a))).
Local Notation trieA a := (nentries (radj_n (adj_raw a))).

Lemma radj_eta (b : radj T) : radj_n b = NAdj (nroot (radj_n b)) (nentries (radj_n b)).
Proof. destruct (radj_n b); reflexivity. Qed.

Lemma W_tlocal {N M} (a : adj T N M) : Squash (nlocal Qall (NAdj (rootA a) (trieA a))).
Proof. rewrite <- radj_eta; exact (squash (radj_local (adj_raw a))). Qed.

Lemma W_tvar {N M K L} (a : adj T N M) (e : ext N M K L) v' (Hv' : wf_var N v' = true)
  Be h ts len p Bt y' j
  (H1 : Squash (option_map (unshift (rootA a)) (aget (label_key (v_label v')) (trieA a)) = Some (unshift (lcounts Be) (Entry h ts len p))))
  (Hi : v_index v' < len)
  (H2 : Squash (option_map (unshift (lcounts Be)) (knth ts (v_index v')) = Some (unshift (lcounts Bt) (TVar y' j)))) :
  Is_true_s (wf_var L (up (ext_depth e) (mk_rvar y' (ldval Bt (label_key y') + j)))).
Proof.
  rewrite ldval_spec;
  destruct H1 as [H1], H2 as [H2]; apply Is_true_s_intro.
  pose proof (radj_local (adj_raw a)) as Hl; rewrite radj_eta in Hl.
  destruct (found_entry _ _ _ _ _ _ _ _ _ Hl H1) as [Hk [_ [_ [_ [Ht _]]]]].
  apply label_key_inj in Hk; subst h.
  pose proof (top_result a v' Hv') as Hr; rewrite radj_eta, (rvar_eta v'), (Ht _ (lcounts Bt) _ Hi H2) in Hr; cbn in Hr.
  apply (wf_eq _ _ _ (ext_depth_L e)), up_wf, Hr.
Qed.

Lemma W_tpay {N M} (a : adj T N M) v' (Hv' : wf_var N v' = true)
  Be h ts len p Bt u (rho : nadj)
  (H1 : Squash (option_map (unshift (rootA a)) (aget (label_key (v_label v')) (trieA a)) = Some (unshift (lcounts Be) (Entry h ts len p))))
  (Hi : v_index v' < len)
  (H2 : Squash (option_map (unshift (lcounts Be)) (knth ts (v_index v')) = Some (unshift (lcounts Bt) (TBind u rho)))) :
  Is_true_s (pok M (absn (LAdd Bt) rho)).
Proof.
  destruct H1 as [H1], H2 as [H2]; apply Is_true_s_intro.
  pose proof (radj_local (adj_raw a)) as Hl; rewrite radj_eta in Hl.
  destruct (found_entry _ _ _ _ _ _ _ _ _ Hl H1) as [Hk [_ [_ [_ [Ht _]]]]].
  apply label_key_inj in Hk; subst h.
  pose proof (top_result a v' Hv') as Hr; rewrite radj_eta, (rvar_eta v'), (Ht _ (lcounts Bt) _ Hi H2) in Hr.
  destruct rho as [r0 es0]; exact Hr.
Qed.

Lemma W_tpass {N M K L} (a : adj T N M) (e : ext N M K L) v' (Hv' : wf_var N v' = true)
  Be h ts len p
  (H1 : Squash (option_map (unshift (rootA a)) (aget (label_key (v_label v')) (trieA a)) = Some (unshift (lcounts Be) (Entry h ts len p))))
  (Hi : ~ v_index v' < len) :
  Is_true_s (wf_var L (up (ext_depth e) (mk_rvar h (ldval Be (label_key h) + (v_index v' - len + p))))).
Proof.
  rewrite ldval_spec;
  destruct H1 as [H1]; apply Is_true_s_intro.
  pose proof (radj_local (adj_raw a)) as Hl; rewrite radj_eta in Hl.
  destruct (found_entry _ _ _ _ _ _ _ _ _ Hl H1) as [Hk [_ [_ [_ [_ [Hp _]]]]]].
  apply label_key_inj in Hk; subst h.
  pose proof (top_result a v' Hv') as Hr; rewrite radj_eta, (rvar_eta v'), (Hp (v_index v') ltac:(lia)) in Hr; cbn in Hr.
  apply (wf_eq _ _ _ (ext_depth_L e)), up_wf, Hr.
Qed.

Lemma W_tnone {N M K L} (a : adj T N M) (e : ext N M K L) v' (Hv' : wf_var N v' = true)
  (H1 : Squash (aget (label_key (v_label v')) (trieA a) = None)) :
  Is_true_s (wf_var L (up (ext_depth e) (mk_rvar (v_label v') (dval (rootA a) (label_key (v_label v')) + v_index v')))).
Proof.
  destruct H1 as [H1]; apply Is_true_s_intro.
  pose proof (top_result a v' Hv') as Hr; rewrite radj_eta, (rvar_eta v'), found_none in Hr by exact H1; cbn in Hr.
  apply (wf_eq _ _ _ (ext_depth_L e)), up_wf, Hr.
Qed.

End TopWrappers.

(** ** The raw lookup of lifts, compositions and payloads *)

Section Raw.

Context {T : Type}.

Local Notation nadj := (@nadj T).

Lemma napply_rlift (a : radj T) h v :
  napply (radj_n (rlift h a)) v
  = if rvar_eqb v (mk_rvar h 0) then inl v
    else match napply (radj_n a) (unshift_rvar (mk_rvar h 0) v) with
         | inl w => inl (shift_rvar (mk_rvar h 0) w)
         | inr (u, x) => inr (u, Point.weaken h x)
         end.
Proof.
  rewrite <- lower_rapply, rapply_lift.
  destruct (rvar_eqb v (mk_rvar h 0)); [reflexivity|].
  rewrite <- lower_rapply; destruct (rapply a _) as [w|[u ρ]]; reflexivity.
Qed.

Lemma napply_rcompose (a b : radj T) v :
  napply (radj_n (rcompose a b)) v
  = match napply (radj_n b) v with
    | inl w => napply (radj_n a) w
    | inr (u, x) => inr (u, ncomp (radj_n a) true x cnone)
    end.
Proof. cbn [radj_n rcompose]; rewrite (proj2 (compose_spec _ _ (radj_wf a) (radj_wf b))); reflexivity. Qed.

Lemma napply_pcompose (a : radj T) x v :
  nwf true x -> v_label v <> None ->
  napply (ncomp (radj_n a) true x cnone) v
  = match napply x v with
    | inl w => napply (radj_n a) w
    | inr (u, y) => inr (u, ncomp (radj_n a) true y cnone)
    end.
Proof.
  intros Hx Hv; destruct (comp_correct (radj_n a) (radj_local a) (radj_wf a) true x Hx) as [_ [Hm _]].
  apply Hm; destruct (v_label v); [reflexivity|contradiction].
Qed.

Lemma napply_pweaken h (x : nadj) v :
  nwf true x -> v_label v <> None -> napply (Point.weaken h x) v = rweaken h (napply x v).
Proof.
  intros Hx Hv; set (ρ := mk_rpadj x (Is_true_s_intro Hx)).
  pose proof (rpapply_pshift h ρ v Hv) as E.
  apply (f_equal lower) in E; rewrite lower_rpapply in E by exact Hv; cbn [rpadj_n rpshift ρ] in E.
  rewrite E; unfold rpapply; cbn [rpadj_n ρ].
  assert (Hp : forall u y, napply x v = inr (u, y) -> nwf true y)
    by (intros u y Ey; apply (nwf_payload true x v u y Hx); [destruct (v_label v); [reflexivity|contradiction]|exact Ey]).
  destruct (napply x v) as [[l i]|[u [r es]]] eqn:Ev; cbn [rpack lower rweaken].
  - rewrite rweaken_var; reflexivity.
  - cbn [rpadj_n rpshift]; rewrite rpadj_n_to_padj by apply (Hp u _ eq_refl); reflexivity.
Qed.

Lemma napply_depth x v u (y : nadj) :
  (exists Q, nlocal Q x) -> napply x v = inr (u, y) -> nnest y < nnest x.
Proof.
  intros [Q Hl] E; apply (nest_napply x v u y); [|exact E].
  intros k e Ek; destruct x as [r es]; destruct Hl as [_ [_ [Hent _]]]; cbn [nentries] in Ek.
  destruct (Hent k e Ek) as [Hok _]; destruct e; apply Hok.
Qed.

Lemma up_shift d w : up d (shift_rvar (mk_rvar None 0) w) = up (S d) w.
Proof.
  destruct w as [[y|] i]; unfold up, shift_rvar; cbn; [reflexivity|].
  f_equal; lia.
Qed.

Lemma up_up d1 d2 w : up d1 (up d2 w) = up (d1 + d2) w.
Proof. destruct w as [[y|] i]; unfold up; cbn; [reflexivity|f_equal; lia]. Qed.

Lemma down_up d w : down d (up d w) = w.
Proof. destruct w as [[y|] i]; unfold up, down; cbn; [reflexivity|f_equal; lia]. Qed.

End Raw.

(** ** In the shapes the proofs below use *)

Section Compat.

Context {T : Type}.

Local Notation nadj := (@nadj T).

Definition pshift (h : option label) (x : nadj) : nadj := Point.weaken h x.
Definition pcomp (a : radj T) (x : nadj) : nadj := ncomp (radj_n a) true x cnone.


Lemma pay_var_wf (x : nadj) Mρ s L0 {K L} (e : ext 0 L0 K L) v' w :
  pok Mρ x = true -> L0 = s + Mρ -> v_label v' <> None -> napply x v' = inl w ->
  wf_var L (up (s + ext_depth e) w) = true.
Proof.
  intros Hx HL Hv Hw; pose proof (pay_result Mρ x v' Hx Hv) as H; rewrite Hw in H.
  pose proof (ext_depth_L e) as HL'.
  apply (wf_eq L ((s + ext_depth e) + Mρ)); [lia|apply up_wf, H].
Qed.

Lemma pay_payload_ok (x : nadj) Mρ v' u ρ :
  pok Mρ x = true -> v_label v' <> None -> napply x v' = inr (u, ρ) -> pok Mρ ρ = true.
Proof. intros Hx Hv Hw; pose proof (pay_result Mρ x v' Hx Hv) as H; rewrite Hw in H; exact H. Qed.

Lemma top_var_wf {N M K L} (a : adj T N M) (e : ext N M K L) v' w :
  wf_var N v' = true -> napply (radj_n (adj_raw a)) v' = inl w ->
  wf_var L (up (ext_depth e) w) = true.
Proof.
  intros Hv Hw; pose proof (top_result a v' Hv) as H; rewrite Hw in H.
  apply (wf_eq _ _ _ (ext_depth_L e)), up_wf, H.
Qed.

Lemma top_payload_ok {N M} (a : adj T N M) v' u ρ :
  wf_var N v' = true -> napply (radj_n (adj_raw a)) v' = inr (u, ρ) -> pok M ρ = true.
Proof. intros Hv Hw; pose proof (top_result a v' Hv) as H; rewrite Hw in H; exact H. Qed.

Lemma napply_pshift h (x : nadj) v :
  nwf true x -> v_label v <> None ->
  napply (pshift h x) v
  = match napply x v with
    | inl w => inl (shift_rvar (mk_rvar h 0) w)
    | inr p => inr (fst p, pshift h (snd p))
    end.
Proof.
  intros Hx Hv; unfold pshift; rewrite napply_pweaken by assumption.
  destruct (napply x v) as [w|[u [r es]]]; cbn [rweaken fst snd]; [rewrite rweaken_var|]; reflexivity.
Qed.

Lemma napply_rlift' (a : radj T) h v :
  napply (radj_n (rlift h a)) v
  = if rvar_eqb v (mk_rvar h 0) then inl v
    else match napply (radj_n a) (unshift_rvar (mk_rvar h 0) v) with
         | inl w => inl (shift_rvar (mk_rvar h 0) w)
         | inr p => inr (fst p, pshift h (snd p))
         end.
Proof. rewrite napply_rlift; destruct (rvar_eqb _ _); [|destruct (napply _ _) as [|[]]]; reflexivity. Qed.

Lemma napply_rcompose' (a b : radj T) v :
  napply (radj_n (rcompose a b)) v
  = match napply (radj_n b) v with
    | inl w => napply (radj_n a) w
    | inr p => inr (fst p, pcomp a (snd p))
    end.
Proof. rewrite napply_rcompose; destruct (napply _ _) as [|[]]; reflexivity. Qed.

Lemma napply_pcompose' {M P'} (a : adj T M P') ρ v :
  pok M ρ = true -> v_label v <> None ->
  napply (pcomp (adj_raw a) ρ) v
  = match napply ρ v with
    | inl w => napply (radj_n (adj_raw a)) w
    | inr p => inr (fst p, pcomp (adj_raw a) (snd p))
    end.
Proof.
  intros H Hv; unfold pcomp; rewrite napply_pcompose by (apply (pok_wf M), H || exact Hv).
  destruct (napply ρ v) as [|[]]; reflexivity.
Qed.

Lemma napply_depth_pok M x v u (ρ : nadj) : pok M x = true -> napply x v = inr (u, ρ) -> nnest ρ < nnest x.
Proof. intros Hx E; apply (napply_depth x v u ρ); [exists Qnamed; apply (pok_local M), Hx|exact E]. Qed.

End Compat.

(** ** Substitution for a syntax *)

Module Subst (Import S : SYNTAX).

Local Notation P := (term 0).
Local Notation nadj := (@nadj P).
Local Notation entry := (@entry P).
Local Notation target := (@target P).

(** Payloads: [papply' rt x Mρ s L0] is the morphism for the payload
    adjustment [x], its root read through [rt] (adding the base it is stored
    over), in scope [Mρ], used under [s] outer binders, into scope [L0]. *)
Fixpoint papply' (rt : counts -> lbase) (x : nadj) (Mρ s L0 : nat) (HL : Is_true_s (Nat.eqb L0 (s + Mρ)))
  (Hx : Is_true_s (pok Mρ (absn rt x))) {struct x} : morph 0 L0 :=
  fun K L e v =>
  match v_label (var_raw v) as o return v_label (var_raw v) = o -> term L with
  | None => fun Hl => tvar (mk_var (var_raw v) (W_pinner e (var_raw v) (var_ok v) Hl))
  | Some y => fun _ =>
      let i := v_index (var_raw v) in
      match x as x0 return Is_true_s (pok Mρ (absn rt x0)) -> term L with
      | NAdj r es => fun Hx =>
          aget_with (label_key (Some y)) es (rt r)
            (fun Be ent =>
               match ent as ent0
                     return Squash (option_map (unshift (lcounts (rt r))) (aget (label_key (Some y)) es) = Some (unshift (lcounts Be) ent0)) -> term L with
               | Entry h ts len p => fun H1 =>
                   match lt_dec i len with
                   | Specif.left Hi =>
                       knth_with i ts Be
                         (fun Bt t =>
                            match t as t0
                                  return Squash (option_map (unshift (lcounts Be)) (knth ts i) = Some (unshift (lcounts Bt) t0)) -> term L with
                            | TVar y' j => fun H2 =>
                                tvar (mk_var (up (s + ext_depth e) (mk_rvar y' (ldval Bt (label_key y') + j)))
                                        (W_pvar Mρ s L0 e (lcounts (rt r)) es y i Be h ts len p Bt y' j HL Hx H1 Hi H2))
                            | TBind u rho => fun H2 =>
                                kleisli (papply' (LAdd Bt) rho Mρ (s + ext_depth e) L (W_pHL Mρ s e HL)
                                           (W_ppay Mρ (lcounts (rt r)) es y i Be h ts len p Bt u rho Hx H1 Hi H2))
                                        ext_here u
                            end)
                         (fun H2 => match W_absurd Qnamed (lcounts (rt r)) es _ i Be h ts len p (pok_squash Mρ _ Hx) H1 Hi H2
                                    with end)
                   | Specif.right Hi =>
                       tvar (mk_var (up (s + ext_depth e) (mk_rvar h (ldval Be (label_key h) + (i - len + p))))
                               (W_ppass Mρ s L0 e (lcounts (rt r)) es y i Be h ts len p HL Hx H1 Hi))
                   end
               end)
            (fun H1 =>
               tvar (mk_var (up (s + ext_depth e) (mk_rvar (Some y) (ldval (rt r) (label_key (Some y)) + i)))
                       (W_pnone Mρ s L0 e (rt r) es y i HL Hx H1)))
      end Hx
  end eq_refl.

Definition papply (x : nadj) (Mρ s L0 : nat) (HL : Is_true_s (Nat.eqb L0 (s + Mρ)))
  (Hx : Is_true_s (pok Mρ x)) : morph 0 L0 :=
  papply' LAbs x Mρ s L0 HL (match x as x0 return Is_true_s (pok Mρ x0) -> Is_true_s (pok Mρ (absn LAbs x0)) with
                                     | NAdj r es => fun H => H end Hx).

(** Looking up a variable outside the binders crossed so far. *)
Definition look {N M K L} (a : adj P N M) (e : ext N M K L) (v' : rvar)
  (Hv' : wf_var N v' = true) : term L :=
  let R := nroot (radj_n (adj_raw a)) in
  let es := nentries (radj_n (adj_raw a)) in
  aget_with (label_key (v_label v')) es (LAbs R)
    (fun Be ent =>
       match ent as ent0
             return Squash (option_map (unshift R) (aget (label_key (v_label v')) es) = Some (unshift (lcounts Be) ent0)) -> term L with
       | Entry h ts len p => fun H1 =>
           match lt_dec (v_index v') len with
           | Specif.left Hi =>
               knth_with (v_index v') ts Be
                 (fun Bt t =>
                    match t as t0
                          return Squash (option_map (unshift (lcounts Be)) (knth ts (v_index v')) = Some (unshift (lcounts Bt) t0)) -> term L with
                    | TVar y' j => fun H2 =>
                        tvar (mk_var (up (ext_depth e) (mk_rvar y' (ldval Bt (label_key y') + j)))
                                (W_tvar a e v' Hv' Be h ts len p Bt y' j H1 Hi H2))
                    | TBind u rho => fun H2 =>
                        kleisli (papply' (LAdd Bt) rho M (ext_depth e) L (W_tHL e)
                                   (W_tpay a v' Hv' Be h ts len p Bt u rho H1 Hi H2))
                                ext_here u
                    end)
                 (fun H2 => match W_absurd Qall R es _ (v_index v') Be h ts len p (W_tlocal a) H1 Hi H2 with end)
           | Specif.right Hi =>
               tvar (mk_var (up (ext_depth e) (mk_rvar h (ldval Be (label_key h) + (v_index v' - len + p))))
                       (W_tpass a e v' Hv' Be h ts len p H1 Hi))
           end
       end)
    (fun H1 =>
       tvar (mk_var (up (ext_depth e) (mk_rvar (v_label v') (dval R (label_key (v_label v')) + v_index v')))
               (W_tnone a e v' Hv' H1))).

(** The morphism of a scoped adjustment. *)
Definition apply {N M} (a : adj P N M) : morph N M :=
  fun K L e v =>
  let rv := var_raw v in
  match v_label rv as o return v_label rv = o -> term L with
  | None => fun Hl =>
      match lt_dec (v_index rv) (ext_depth e) with
      | Specif.left Hb => tvar (mk_var rv (W_tinner e rv Hl Hb))
      | Specif.right Hb => look a e (down (ext_depth e) rv) (W_tdown e rv (var_ok v) (rel_ge rv _ Hb))
      end
  | Some y => fun Hl =>
      look a e (down (ext_depth e) rv) (W_tdown e rv (var_ok v) (fun H => rel_some rv y Hl H _))
  end eq_refl.

(** Substitution [t [a]] is the Kleisli extension of [apply] at the top;
    it is notation, so rewriting sees the Kleisli extension. *)
Notation "t [ a ]" := (kleisli (apply a) ext_here t) (at level 1, left associativity, format "t [ a ]").
Notation subst a := (kleisli (apply a) ext_here) (only parsing).

Lemma padj_pok {M} (ρ : padj P M) : Is_true_s (pok M (rpadj_n (padj_raw ρ))).
Proof.
  apply Is_true_s_intro; unfold pok; apply andb_true_iff; split;
    [exact (Is_true_s_elim (rpadj_ok _))|exact (Is_true_s_elim (padj_ok ρ))].
Qed.

(** A payload term with its payload adjustment applied. *)
Definition psubst {M} (ρ : padj P M) (u : P) : term M :=
  kleisli (papply (rpadj_n (padj_raw ρ)) M 0 M (Is_true_s_intro (Nat.eqb_refl M)) (padj_pok ρ)) ext_here u.

(** ** What [look] and [papply] compute *)

Section Char.

Lemma option_cases {X} (o : option X) : (exists x, o = Some x) \/ o = None.
Proof. destruct o; eauto. Qed.

(** What [papply'] computes, for any lazy base: a payload result is
    looked up over the base the lookup reached. *)
Lemma papply'_result rt x Mρ s L0 HL Hx {K L} (e : ext 0 L0 K L) v :
  v_label (var_raw v) <> None ->
  match napply (absn rt x) (var_raw v) with
  | inl w => forall H, papply' rt x Mρ s L0 HL Hx K L e v = tvar (mk_var (up (s + ext_depth e) w) H)
  | inr (u, ρ) => exists Bt ρ0, ρ = absn (LAdd Bt) ρ0
                  /\ forall HL' Hρ0, papply' rt x Mρ s L0 HL Hx K L e v
                                     = kleisli (papply' (LAdd Bt) ρ0 Mρ (s + ext_depth e) L HL' Hρ0) ext_here u
  end.
Proof.
  pose proof (pok_local _ _ (Is_true_s_elim Hx)) as Hl.
  destruct v as [[[y|] i] Hv]; cbn [var_raw v_label v_index]; intros Hy; [|contradiction].
  destruct x as [r es]; cbn [papply' var_raw v_label v_index absn] in *.
  set (R := lcounts (rt r)) in *.
  destruct (option_cases (aget (label_key (Some y)) es)) as [[e0 E1]|E1].
  - destruct (napply (NAdj R es) (mk_rvar (Some y) i)) as [w|[u ρ]] eqn:En.
    + intros H; apply (aget_with_some _ _ _ _ _ (unshift R e0)); [|rewrite E1; reflexivity].
      intros Be [h ts len p] H1 Hy'.
      assert (Loc : option_map (unshift R) (aget (label_key (Some y)) es) = Some (unshift (lcounts Be) (Entry h ts len p)))
        by (rewrite E1, Hy'; reflexivity).
      destruct (found_entry _ _ _ _ _ _ _ _ _ Hl Loc) as [Hk [_ [G [Hlen [Ht [Hp Hnn]]]]]].
      apply label_key_inj in Hk; subst h.
      destruct (lt_dec i len) as [Hi|Hi].
      * destruct (option_cases (knth ts i)) as [[t Et]|Et]; [|exfalso; exact (Hnn i Hi Et)].
        apply (knth_with_some _ _ _ _ _ (unshift (lcounts Be) t)); [|rewrite Et; reflexivity].
        intros Bt t' H2 Ht'.
        pose proof (Ht i (lcounts Bt) t' Hi ltac:(rewrite Et, Ht'; reflexivity)) as Er; rewrite En in Er.
        destruct t' as [y' j|u' [r0 es0]]; cbn in Er; [|discriminate Er].
        injection Er as Ew; subst w; cbn beta iota; f_equal; apply var_eq; cbn [var_raw]; rewrite ldval_spec; reflexivity.
      * rewrite (Hp i ltac:(lia)) in En; injection En as <-; f_equal; apply var_eq; cbn [var_raw]; rewrite ldval_spec; reflexivity.
    + set (Pz := fun z => exists Bt ρ0, ρ = absn (LAdd Bt) ρ0
                   /\ forall HL' Hρ0, z = kleisli (papply' (LAdd Bt) ρ0 Mρ (s + ext_depth e) L HL' Hρ0) ext_here u).
      apply (aget_with_prop _ _ _ _ _ (unshift R e0) Pz); [|rewrite E1; reflexivity].
      intros Be [h ts len p] H1 Hy'.
      assert (Loc : option_map (unshift R) (aget (label_key (Some y)) es) = Some (unshift (lcounts Be) (Entry h ts len p)))
        by (rewrite E1, Hy'; reflexivity).
      destruct (found_entry _ _ _ _ _ _ _ _ _ Hl Loc) as [Hk [_ [G [Hlen [Ht [Hp Hnn]]]]]].
      apply label_key_inj in Hk; subst h.
      destruct (lt_dec i len) as [Hi|Hi].
      * destruct (option_cases (knth ts i)) as [[t Et]|Et]; [|exfalso; exact (Hnn i Hi Et)].
        apply (knth_with_prop _ _ _ _ _ (unshift (lcounts Be) t) Pz); [|rewrite Et; reflexivity].
        intros Bt t' H2 Ht'.
        pose proof (Ht i (lcounts Bt) t' Hi ltac:(rewrite Et, Ht'; reflexivity)) as Er; rewrite En in Er.
        destruct t' as [y' j|u' [r0 es0]]; cbn in Er; [discriminate|].
        injection Er as Eu Eρ; subst u ρ.
        exists Bt, (NAdj r0 es0); split; [reflexivity|intros HL' Hρ0; reflexivity].
      * rewrite (Hp i ltac:(lia)) in En; discriminate.
  - rewrite (aget_with_none _ _ _ _ _ E1), (found_none R es (Some y) i E1).
    intros H; f_equal; apply var_eq; cbn [var_raw]; rewrite ldval_spec; reflexivity.
Qed.

Lemma nnest_absn rt (x : nadj) : nnest (absn rt x) = nnest x.
Proof. destruct x; cbn [absn]; rewrite !nnest_es; reflexivity. Qed.

(** The lazy base only matters through what it denotes. *)
Lemma papply'_abs n : forall rt x Mρ s L0 HL Hx, nnest x < n ->
  forall K L (e : ext 0 L0 K L) v,
  papply' rt x Mρ s L0 HL Hx K L e v = papply (absn rt x) Mρ s L0 HL Hx K L e v.
Proof.
  induction n as [|n IH]; intros rt x Mρ s L0 HL Hx Hn K L e v; [lia|].
  destruct x as [r es]; unfold papply; cbn [absn lcounts] in *.
  destruct (option_cases (v_label (var_raw v))) as [[y Hy]|Hv].
  - assert (Hy' : v_label (var_raw v) <> None) by congruence.
    pose proof (papply'_result rt (NAdj r es) Mρ s L0 HL Hx e v Hy') as A.
    pose proof (papply'_result LAbs (absn rt (NAdj r es)) Mρ s L0 HL Hx e v Hy') as B.
    cbn [absn lcounts] in A, B.
    pose proof (Is_true_s_elim Hx) as Hx0; cbn [absn] in Hx0.
    destruct (napply (NAdj (lcounts (rt r)) es) (var_raw v)) as [w|[u ρ]] eqn:En.
    + assert (H : Is_true_s (wf_var L (up (s + ext_depth e) w))).
      { apply Is_true_s_intro, (pay_var_wf _ Mρ s L0 e (var_raw v) w Hx0); [|exact Hy'|exact En].
        apply Nat.eqb_eq, Is_true_s_elim, HL. }
      rewrite (A H), (B H); reflexivity.
    + destruct A as [Bt [ρ0 [E0 A]]], B as [Bt' [ρ1 [E1 B]]].
      assert (Hρ : pok Mρ ρ = true) by apply (pay_payload_ok _ Mρ (var_raw v) u ρ Hx0 Hy' En).
      assert (Hd : nnest ρ < nnest (NAdj (lcounts (rt r)) es)) by apply (napply_depth_pok Mρ _ _ _ _ Hx0 En).
      assert (HL' : Is_true_s (Nat.eqb L ((s + ext_depth e) + Mρ))) by apply (W_pHL Mρ s e HL).
      assert (H0 : Is_true_s (pok Mρ (absn (LAdd Bt) ρ0))) by (rewrite <- E0; apply Is_true_s_intro, Hρ).
      assert (H1 : Is_true_s (pok Mρ (absn (LAdd Bt') ρ1))) by (rewrite <- E1; apply Is_true_s_intro, Hρ).
      rewrite (A HL' H0), (B HL' H1); apply kleisli_ext; intros K' L' e' v'.
      rewrite (IH (LAdd Bt) ρ0), (IH (LAdd Bt') ρ1).
      * revert H0 H1; rewrite <- E0, <- E1; reflexivity.
      * rewrite E1, nnest_absn, nnest_es in Hd; rewrite nnest_es in Hn; lia.
      * rewrite E0, nnest_absn, nnest_es in Hd; rewrite nnest_es in Hn; lia.
  - destruct v as [[l i] Hv']; cbn [var_raw v_label] in Hv; subst l; reflexivity.
Qed.

Lemma papply_result x Mρ s L0 HL Hx {K L} (e : ext 0 L0 K L) v :
  v_label (var_raw v) <> None ->
  match napply x (var_raw v) with
  | inl w => forall H, papply x Mρ s L0 HL Hx K L e v = tvar (mk_var (up (s + ext_depth e) w) H)
  | inr (u, ρ) => forall HL' Hρ, papply x Mρ s L0 HL Hx K L e v
                                 = kleisli (papply ρ Mρ (s + ext_depth e) L HL' Hρ) ext_here u
  end.
Proof.
  intros Hv; destruct x as [r es]; pose proof (papply'_result LAbs (NAdj r es) Mρ s L0 HL Hx e v Hv) as A.
  unfold papply; cbn [absn lcounts] in A |- *.
  destruct (napply (NAdj r es) (var_raw v)) as [w|[u ρ]]; [exact A|].
  destruct A as [Bt [ρ0 [-> A]]]; intros HL' Hρ; rewrite (A HL' Hρ).
  apply kleisli_ext; intros K' L' e' v'.
  rewrite (papply'_abs (S (nnest ρ0)) (LAdd Bt) ρ0) by lia; reflexivity.
Qed.

Lemma look_result {N M K L} (a : adj P N M) (e : ext N M K L) v' Hv' :
  match napply (radj_n (adj_raw a)) v' with
  | inl w => forall H, look a e v' Hv' = tvar (mk_var (up (ext_depth e) w) H)
  | inr (u, ρ) => forall HL Hρ, look a e v' Hv' = kleisli (papply ρ M (ext_depth e) L HL Hρ) ext_here u
  end.
Proof.
  pose proof (radj_local (adj_raw a)) as Hl; rewrite radj_eta in Hl.
  rewrite radj_eta; unfold look; cbv zeta.
  set (R := nroot (radj_n (adj_raw a))) in *; set (es := nentries (radj_n (adj_raw a))) in *.
  destruct v' as [l i]; cbn [v_label v_index] in *.
  destruct (option_cases (aget (label_key l) es)) as [[e0 E1]|E1].
  - destruct (napply (NAdj R es) (mk_rvar l i)) as [w|[u ρ]] eqn:En.
    + intros H; apply (aget_with_some _ _ _ _ _ (unshift R e0)); [|rewrite E1; reflexivity].
      intros Be [h ts len p] H1 Hy.
      assert (Loc : option_map (unshift R) (aget (label_key l) es) = Some (unshift (lcounts Be) (Entry h ts len p)))
        by (rewrite E1, Hy; reflexivity).
      destruct (found_entry _ _ _ _ _ _ _ _ _ Hl Loc) as [Hk [_ [G [Hlen [Ht [Hp Hnn]]]]]].
      apply label_key_inj in Hk; subst h.
      destruct (lt_dec i len) as [Hi|Hi].
      * destruct (option_cases (knth ts i)) as [[t Et]|Et]; [|exfalso; exact (Hnn i Hi Et)].
        apply (knth_with_some _ _ _ _ _ (unshift (lcounts Be) t)); [|rewrite Et; reflexivity].
        intros Bt t' H2 Ht'.
        pose proof (Ht i (lcounts Bt) t' Hi ltac:(rewrite Et, Ht'; reflexivity)) as Er; rewrite En in Er.
        destruct t' as [y' j|u' [r0 es0]]; cbn in Er; [|discriminate Er].
        injection Er as Ew; subst w; cbn beta iota; f_equal; apply var_eq; cbn [var_raw]; rewrite ldval_spec; reflexivity.
      * rewrite (Hp i ltac:(lia)) in En; injection En as <-; f_equal; apply var_eq; cbn [var_raw]; rewrite ldval_spec; reflexivity.
    + intros HL Hρ; apply (aget_with_some _ _ _ _ _ (unshift R e0)); [|rewrite E1; reflexivity].
      intros Be [h ts len p] H1 Hy.
      assert (Loc : option_map (unshift R) (aget (label_key l) es) = Some (unshift (lcounts Be) (Entry h ts len p)))
        by (rewrite E1, Hy; reflexivity).
      destruct (found_entry _ _ _ _ _ _ _ _ _ Hl Loc) as [Hk [_ [G [Hlen [Ht [Hp Hnn]]]]]].
      apply label_key_inj in Hk; subst h.
      destruct (lt_dec i len) as [Hi|Hi].
      * destruct (option_cases (knth ts i)) as [[t Et]|Et]; [|exfalso; exact (Hnn i Hi Et)].
        apply (knth_with_some _ _ _ _ _ (unshift (lcounts Be) t)); [|rewrite Et; reflexivity].
        intros Bt t' H2 Ht'.
        pose proof (Ht i (lcounts Bt) t' Hi ltac:(rewrite Et, Ht'; reflexivity)) as Er; rewrite En in Er.
        destruct t' as [y' j|u' [r0 es0]]; cbn in Er; [discriminate|].
        injection Er as Eu Eρ; subst u ρ; cbn beta iota.
        apply kleisli_ext; intros K' L' e' v'.
        rewrite (papply'_abs (S (nnest (NAdj r0 es0))) (LAdd Bt) (NAdj r0 es0)) by lia; reflexivity.
      * rewrite (Hp i ltac:(lia)) in En; discriminate.
  - rewrite (aget_with_none _ _ _ _ _ E1), (found_none R es l i E1).
    intros H; f_equal; apply var_eq; reflexivity.
Qed.

Lemma look_var {N M K L} (a : adj P N M) (e : ext N M K L) v' Hv' w H :
  napply (radj_n (adj_raw a)) v' = inl w -> look a e v' Hv' = tvar (mk_var (up (ext_depth e) w) H).
Proof. intros E; pose proof (look_result a e v' Hv') as R; rewrite E in R; apply R. Qed.

Lemma look_pay {N M K L} (a : adj P N M) (e : ext N M K L) v' Hv' u ρ HL Hρ :
  napply (radj_n (adj_raw a)) v' = inr (u, ρ) ->
  look a e v' Hv' = kleisli (papply ρ M (ext_depth e) L HL Hρ) ext_here u.
Proof. intros E; pose proof (look_result a e v' Hv') as R; rewrite E in R; apply R. Qed.

Lemma papply_inner x Mρ s L0 HL Hx {K L} (e : ext 0 L0 K L) v H :
  v_label (var_raw v) = None -> papply x Mρ s L0 HL Hx K L e v = tvar (mk_var (var_raw v) H).
Proof.
  destruct v as [[[y|] i] Hv]; cbn [var_raw v_label v_index]; intros Hl; [discriminate|].
  destruct x as [r es]; reflexivity.
Qed.

Lemma papply_var x Mρ s L0 HL Hx {K L} (e : ext 0 L0 K L) v w H :
  v_label (var_raw v) <> None -> napply x (var_raw v) = inl w ->
  papply x Mρ s L0 HL Hx K L e v = tvar (mk_var (up (s + ext_depth e) w) H).
Proof. intros Hv E; pose proof (papply_result x Mρ s L0 HL Hx e v Hv) as R; rewrite E in R; apply R. Qed.

Lemma papply_pay x Mρ s L0 HL Hx {K L} (e : ext 0 L0 K L) v u ρ HL' Hρ :
  v_label (var_raw v) <> None -> napply x (var_raw v) = inr (u, ρ) ->
  papply x Mρ s L0 HL Hx K L e v = kleisli (papply ρ Mρ (s + ext_depth e) L HL' Hρ) ext_here u.
Proof. intros Hv E; pose proof (papply_result x Mρ s L0 HL Hx e v Hv) as R; rewrite E in R; apply R. Qed.

Lemma apply_inner {N M K L} (a : adj P N M) (e : ext N M K L) v H :
  v_label (var_raw v) = None -> v_index (var_raw v) < ext_depth e ->
  apply a K L e v = tvar (mk_var (var_raw v) H).
Proof.
  destruct v as [[[y|] i] Hv]; cbn [var_raw v_label v_index]; intros Hl Hi; [discriminate|].
  unfold apply; cbn [var_raw v_label v_index].
  destruct (lt_dec i (ext_depth e)) as [Hb|Hb]; [reflexivity|contradiction].
Qed.

Lemma apply_var {N M K L} (a : adj P N M) (e : ext N M K L) v w H :
  (v_label (var_raw v) = None -> ext_depth e <= v_index (var_raw v)) ->
  napply (radj_n (adj_raw a)) (down (ext_depth e) (var_raw v)) = inl w ->
  apply a K L e v = tvar (mk_var (up (ext_depth e) w) H).
Proof.
  destruct v as [[[y|] i] Hv]; cbn [var_raw v_label v_index]; intros Hr Hw;
    unfold apply; cbn [var_raw v_label v_index].
  - apply look_var, Hw.
  - specialize (Hr eq_refl).
    destruct (lt_dec i (ext_depth e)) as [Hb|Hb]; [lia|apply look_var, Hw].
Qed.

Lemma apply_pay {N M K L} (a : adj P N M) (e : ext N M K L) v u ρ HL Hρ :
  (v_label (var_raw v) = None -> ext_depth e <= v_index (var_raw v)) ->
  napply (radj_n (adj_raw a)) (down (ext_depth e) (var_raw v)) = inr (u, ρ) ->
  apply a K L e v = kleisli (papply ρ M (ext_depth e) L HL Hρ) ext_here u.
Proof.
  destruct v as [[[y|] i] Hv]; cbn [var_raw v_label v_index]; intros Hr Hw;
    unfold apply; cbn [var_raw v_label v_index].
  - apply look_pay, Hw.
  - specialize (Hr eq_refl).
    destruct (lt_dec i (ext_depth e)) as [Hb|Hb]; [lia|apply look_pay, Hw].
Qed.

(** Substituting into a variable the adjustment renames. *)
Lemma subst_tvar_rename {N M} (a : adj P N M) (v : var N) (w : var M) :
  Indexed.apply_var a v = Rename w -> subst a (tvar v) = tvar w.
Proof.
  intros E; rewrite kleisli_var.
  assert (Hr : rapply (adj_raw a) (var_raw v) = inl (var_raw w)).
  { revert E; unfold Indexed.apply_var; generalize (apply_wf a v); unfold Indexed.apply.
    destruct (rapply (adj_raw a) (var_raw v)) as [w0|[u ρ]]; intros H E; [|discriminate].
    injection E as <-; reflexivity. }
  unfold rapply in Hr.
  destruct (napply (radj_n (adj_raw a)) (var_raw v)) as [w0|[u x]] eqn:En; cbn in Hr; [|discriminate].
  injection Hr as Hr.
  assert (Hd : down 0 (var_raw v) = var_raw v)
    by (destruct v as [[[y|] i] Hv]; unfold down; cbn; [reflexivity|rewrite Nat.sub_0_r; reflexivity]).
  rewrite <- Hd in En.
  assert (Hu : up 0 w0 = var_raw w) by (subst w0; destruct w as [[[y|] i] Hw]; unfold up; reflexivity).
  assert (Hw : Is_true_s (wf_var M (up (ext_depth (@ext_here N M)) w0))) by (cbn [ext_depth]; rewrite Hu; exact (var_ok w)).
  rewrite (apply_var a ext_here v w0 Hw (fun _ => le_0_n _) En).
  f_equal; apply var_eq; exact Hu.
Qed.

(** The identity payload adjustment of a closed term leaves it as it is. *)
Lemma papply_pidentity HL Hx {K L} (e : ext 0 0 K L) (v : var K) :
  papply pidentity_n 0 0 0 HL Hx K L e v = unit_m K L e v.
Proof.
  unfold unit_m, ext_var; destruct v as [[[y|] i] Hv].
  - assert (E : napply (@pidentity_n P) (var_raw (mk_var (mk_rvar (Some y) i) Hv)) = inl (mk_rvar (Some y) i))
      by reflexivity.
    rewrite (papply_var _ 0 0 0 HL Hx e (mk_var (mk_rvar (Some y) i) Hv) (mk_rvar (Some y) i) (Is_true_s_intro (ext_same_wf e _ (Is_true_s_elim Hv))) ltac:(discriminate) E).
    reflexivity.
  - apply papply_inner; reflexivity.
Qed.

(** Substituting into a variable the adjustment sends to a closed term with
    the identity payload adjustment. *)
Lemma subst_tvar_bind0 {N} (a : adj P N 0) (v : var N) (u : P) :
  Indexed.apply_var a v = Bind u pid -> subst a (tvar v) = u.
Proof.
  intros E; rewrite kleisli_var.
  assert (Hr : rapply (adj_raw a) (var_raw v) = inr (u, rpidentity)).
  { revert E; unfold Indexed.apply_var; generalize (apply_wf a v); unfold Indexed.apply.
    destruct (rapply (adj_raw a) (var_raw v)) as [w0|[u0 ρ]]; intros H E; [discriminate|].
    injection E as <- Eρ; rewrite Eρ; reflexivity. }
  unfold rapply in Hr.
  destruct (napply (radj_n (adj_raw a)) (var_raw v)) as [w0|[u0 x]] eqn:En; cbn in Hr; [discriminate|].
  injection Hr as -> Ex.
  assert (Hwf : nwf true x) by (apply (nwf_payload false _ (var_raw v) u x (radj_wf (adj_raw a)) eq_refl En)).
  assert (Hxp : x = pidentity_n).
  { rewrite <- Ex; symmetry; exact (rpadj_n_to_padj x Hwf). }
  assert (Hd : down 0 (var_raw v) = var_raw v)
    by (destruct v as [[[y|] i] Hv]; unfold down; cbn; [reflexivity|rewrite Nat.sub_0_r; reflexivity]).
  assert (Hρ : Is_true_s (pok 0 x))
    by (apply Is_true_s_intro, (top_payload_ok a (var_raw v) u); [apply Is_true_s_elim, var_ok|exact En]).
  rewrite <- Hd in En.
  rewrite (apply_pay a ext_here v u x stt Hρ (fun _ => le_0_n _) En).
  subst x; transitivity (kleisli unit_m (@ext_here 0 0) u); [|apply kleisli_unit].
  apply kleisli_ext; intros K L e w; apply papply_pidentity.
Qed.

End Char.

(** ** Going under a binder is lifting *)

Section Lift.

Ltac sq := apply Is_true_s_intro.

Lemma papply_s_eq ρ M L s s' (E : s = s') HL HL' Hx :
  papply ρ M s L HL Hx = papply ρ M s' L HL' Hx.
Proof. subst; reflexivity. Qed.

Lemma papply_pshift_depth n :
  forall ρ, nnest ρ < n -> forall M d L HL HL' Hx Hx' K L' (e : ext 0 L K L') v,
  papply ρ M (S d) L HL Hx K L' e v = papply (pshift None ρ) (S M) d L HL' Hx' K L' e v.
Proof.
  induction n as [|n IH]; intros ρ Hd M d L HL HL' Hx Hx' K L' e v;
    [lia|].
  pose proof (Is_true_s_elim Hx) as Hx0; pose proof (Is_true_s_elim Hx') as Hx0'.
  assert (Hn : nwf true ρ) by apply (pok_wf M ρ Hx0).
  destruct (v_label (var_raw v)) as [y|] eqn:El.
  2: { pose proof (W_pinner e (var_raw v) (var_ok v) El) as H.
       rewrite (papply_inner _ _ _ _ _ _ e v H El), (papply_inner _ _ _ _ _ _ e v H El).
       reflexivity. }
  assert (Hl : v_label (var_raw v) <> None) by congruence.
  pose proof (napply_pshift None ρ (var_raw v) Hn Hl) as Hs.
  destruct (napply ρ (var_raw v)) as [w|[u ρ2]] eqn:E.
  - assert (H1 : Is_true_s (wf_var L' (up (S d + ext_depth e) w))).
    { sq; apply (pay_var_wf ρ M (S d) L e (var_raw v)); auto.
      apply Nat.eqb_eq, Is_true_s_elim, HL. }
    assert (H2 : Is_true_s (wf_var L' (up (d + ext_depth e) (shift_rvar (mk_rvar None 0) w)))).
    { rewrite up_shift; exact H1. }
    rewrite (papply_var _ _ _ _ _ _ e v w H1 Hl E), (papply_var _ _ _ _ _ _ e v _ H2 Hl Hs).
    f_equal; apply var_eq; cbn; rewrite up_shift; reflexivity.
  - pose proof (napply_depth_pok _ _ _ _ _ Hx0 E) as Hdep.
    assert (Hρ2 : Is_true_s (pok M ρ2)) by (sq; apply (pay_payload_ok ρ M (var_raw v) u); auto).
    assert (Hρ2' : Is_true_s (pok (S M) (pshift None ρ2))).
    { sq; apply (pay_payload_ok (pshift None ρ) (S M) (var_raw v) u); auto. }
    assert (HL1 : Is_true_s (Nat.eqb L' ((S d + ext_depth e) + M))) by (apply (W_pHL M (S d) e HL)).
    assert (HL2 : Is_true_s (Nat.eqb L' ((d + ext_depth e) + S M))) by (apply (W_pHL (S M) d e HL')).
    rewrite (papply_pay _ _ _ _ _ _ e v u ρ2 HL1 Hρ2 Hl E).
    rewrite (papply_pay _ _ _ _ _ _ e v u (pshift None ρ2) HL2 Hρ2' Hl Hs).
    apply kleisli_ext; intros K2 L2 e2 v2; apply IH; lia.
Qed.

Lemma apply_lift_rebase {N M K L} (a : adj P N M) (e : ext (S N) (S M) K L) v :
  apply a K L (ext_app (ext_under ext_here) e) v = apply (lift a) K L e v.
Proof.
  set (d := ext_depth e).
  assert (Hd : ext_depth (ext_app (ext_under ext_here) e) = S d)
    by (rewrite ext_depth_app; cbn; unfold d; lia).
  set (e1 := ext_app (ext_under ext_here) e) in *.
  (* the bound variables inside, and the new one *)
  destruct (v_label (var_raw v)) as [y|] eqn:El;
    [|destruct (lt_dec (v_index (var_raw v)) (S d)) as [Hi|Hi]].
  2: { pose proof (W_tinner e1 (var_raw v) El ltac:(lia)) as H.
       rewrite (apply_inner a e1 v H El) by lia.
       destruct (lt_dec (v_index (var_raw v)) d) as [Hi'|Hi'].
       - rewrite (apply_inner (lift a) e v H El Hi'); reflexivity.
       - assert (Hii : v_index (var_raw v) = d) by lia.
         assert (Hn : napply (radj_n (adj_raw (lift a))) (down d (var_raw v)) = inl (mk_rvar None 0)).
         { rewrite adj_raw_lift, napply_rlift'.
           destruct (var_raw v) as [h j]; cbn in El, Hii |- *; subst h j.
           unfold down; cbn [v_label v_index]; rewrite Nat.sub_diag; reflexivity. }
         assert (H' : Is_true_s (wf_var L (up d (mk_rvar None 0)))).
         { replace (up d (mk_rvar None 0)) with (var_raw v); [exact H|].
           destruct (var_raw v) as [h j]; cbn in El, Hii; subst h j; unfold up; cbn; f_equal; lia. }
         rewrite (apply_var (lift a) e v (mk_rvar None 0) H' (fun _ => ltac:(lia)) Hn).
         f_equal; apply var_eq; cbn.
         destruct (var_raw v) as [h j]; cbn in El, Hii; subst h j; unfold up; cbn; f_equal; lia. }
  (* everything else is looked up in [a] *)
  - assert (Hr1 : v_label (var_raw v) = None -> ext_depth e1 <= v_index (var_raw v))
      by (intros; rewrite Hd; try lia; congruence).
    assert (Hr2 : v_label (var_raw v) = None -> ext_depth e <= v_index (var_raw v))
      by (intros; unfold d in *; try lia; congruence).
    assert (Hdn : napply (radj_n (adj_raw (lift a))) (down (ext_depth e) (var_raw v))
                  = match napply (radj_n (adj_raw a)) (down (ext_depth e1) (var_raw v)) with
                    | inl w => inl (shift_rvar (mk_rvar None 0) w)
                    | inr p => inr (fst p, pshift None (snd p))
                    end).
    { rewrite adj_raw_lift, napply_rlift', Hd; fold d.
      destruct (var_raw v) as [h j]; cbn in El |- *; subst h.
      first [reflexivity|
        (unfold down; cbn [v_label v_index];
         replace (rvar_eqb (mk_rvar None (j - d)) (mk_rvar None 0)) with false
           by (symmetry; apply Bool.not_true_iff_false; intros Heq;
               apply (proj2 (reflect_iff _ _ (rvar_eqb_spec _ _))) in Heq; injection Heq; cbn in Hi; lia);
         unfold unshift_rvar; cbn;
         replace (j - d) with (S (j - S d)) by (cbn in Hi; lia);
         cbn; rewrite Nat.sub_0_r; reflexivity)]. }
    destruct (napply (radj_n (adj_raw a)) (down (ext_depth e1) (var_raw v))) as [w|[u ρ]] eqn:E.
    + assert (H1 : Is_true_s (wf_var L (up (ext_depth e1) w)))
        by (apply Is_true_s_intro, (top_var_wf a e1 (down (ext_depth e1) (var_raw v)) w);
            [apply (W_tdown e1 _ (var_ok v) Hr1)|exact E]).
      assert (H2 : Is_true_s (wf_var L (up (ext_depth e) (shift_rvar (mk_rvar None 0) w))))
        by (rewrite up_shift; fold d; rewrite <- Hd; exact H1).
      rewrite (apply_var a e1 v w H1 Hr1 E), (apply_var (lift a) e v _ H2 Hr2 Hdn).
      f_equal; apply var_eq; cbn; rewrite up_shift, Hd; reflexivity.
    + pose proof (top_payload_ok a _ u ρ (W_tdown e1 _ (var_ok v) Hr1) E) as Hρ.
      assert (Hρ' : pok (S M) (pshift None ρ) = true)
        by (apply (top_payload_ok (lift a) (down (ext_depth e) (var_raw v)) u);
            [apply (W_tdown e _ (var_ok v) Hr2)|exact Hdn]).
      rewrite (apply_pay a e1 v u ρ (W_tHL e1) (Is_true_s_intro Hρ) Hr1 E).
      rewrite (apply_pay (lift a) e v u (pshift None ρ) (W_tHL e) (Is_true_s_intro Hρ') Hr2 Hdn).
      apply kleisli_ext; intros K2 L2 e2 v2.
      assert (HL'' : Is_true_s (Nat.eqb L (S d + M)))
        by (apply Is_true_s_intro, Nat.eqb_eq; pose proof (ext_depth_L e); unfold d; lia).
      rewrite (papply_s_eq ρ M L _ (S d) Hd (W_tHL e1) HL'').
      apply (papply_pshift_depth (S (nnest ρ))); lia.
  - assert (Hr1 : v_label (var_raw v) = None -> ext_depth e1 <= v_index (var_raw v))
      by (intros; rewrite Hd; try lia; congruence).
    assert (Hr2 : v_label (var_raw v) = None -> ext_depth e <= v_index (var_raw v))
      by (intros; unfold d in *; try lia; congruence).
    assert (Hdn : napply (radj_n (adj_raw (lift a))) (down (ext_depth e) (var_raw v))
                  = match napply (radj_n (adj_raw a)) (down (ext_depth e1) (var_raw v)) with
                    | inl w => inl (shift_rvar (mk_rvar None 0) w)
                    | inr p => inr (fst p, pshift None (snd p))
                    end).
    { rewrite adj_raw_lift, napply_rlift', Hd; fold d.
      destruct (var_raw v) as [h j]; cbn in El |- *; subst h.
      first [reflexivity|
        (unfold down; cbn [v_label v_index];
         replace (rvar_eqb (mk_rvar None (j - d)) (mk_rvar None 0)) with false
           by (symmetry; apply Bool.not_true_iff_false; intros Heq;
               apply (proj2 (reflect_iff _ _ (rvar_eqb_spec _ _))) in Heq; injection Heq; cbn in Hi; lia);
         unfold unshift_rvar; cbn;
         replace (j - d) with (S (j - S d)) by (cbn in Hi; lia);
         cbn; rewrite Nat.sub_0_r; reflexivity)]. }
    destruct (napply (radj_n (adj_raw a)) (down (ext_depth e1) (var_raw v))) as [w|[u ρ]] eqn:E.
    + assert (H1 : Is_true_s (wf_var L (up (ext_depth e1) w)))
        by (apply Is_true_s_intro, (top_var_wf a e1 (down (ext_depth e1) (var_raw v)) w);
            [apply (W_tdown e1 _ (var_ok v) Hr1)|exact E]).
      assert (H2 : Is_true_s (wf_var L (up (ext_depth e) (shift_rvar (mk_rvar None 0) w))))
        by (rewrite up_shift; fold d; rewrite <- Hd; exact H1).
      rewrite (apply_var a e1 v w H1 Hr1 E), (apply_var (lift a) e v _ H2 Hr2 Hdn).
      f_equal; apply var_eq; cbn; rewrite up_shift, Hd; reflexivity.
    + pose proof (top_payload_ok a _ u ρ (W_tdown e1 _ (var_ok v) Hr1) E) as Hρ.
      assert (Hρ' : pok (S M) (pshift None ρ) = true)
        by (apply (top_payload_ok (lift a) (down (ext_depth e) (var_raw v)) u);
            [apply (W_tdown e _ (var_ok v) Hr2)|exact Hdn]).
      rewrite (apply_pay a e1 v u ρ (W_tHL e1) (Is_true_s_intro Hρ) Hr1 E).
      rewrite (apply_pay (lift a) e v u (pshift None ρ) (W_tHL e) (Is_true_s_intro Hρ') Hr2 Hdn).
      apply kleisli_ext; intros K2 L2 e2 v2.
      assert (HL'' : Is_true_s (Nat.eqb L (S d + M)))
        by (apply Is_true_s_intro, Nat.eqb_eq; pose proof (ext_depth_L e); unfold d; lia).
      rewrite (papply_s_eq ρ M L _ (S d) Hd (W_tHL e1) HL'').
      apply (papply_pshift_depth (S (nnest ρ))); lia.
Qed.

End Lift.

(** ** The rewrite view: offsets reduce to lifts *)

Theorem kleisli_apply_under {N M K L} (a : adj P N M) (e : ext N M K L) (t : term (S K)) :
  kleisli (apply a) (ext_under e) t = kleisli (apply (lift a)) (ext_shift e) t.
Proof.
  rewrite <- (ext_app_shift e), kleisli_rebase.
  apply kleisli_ext; intros K' L' e' v; apply apply_lift_rebase.
Qed.

Theorem kleisli_apply_here {N M} (a : adj P N M) (t : term N) :
  kleisli (apply a) ext_here t = subst a t.
Proof. reflexivity. Qed.

(** ** Identity *)

Lemma up_down d rv : (v_label rv = None -> d <= v_index rv) -> up d (down d rv) = rv.
Proof.
  destruct rv as [[y|] i]; unfold up, down; cbn; [reflexivity|].
  intros H; specialize (H eq_refl); f_equal; lia.
Qed.

Lemma apply_identity {N K L} (e : ext N N K L) v : apply identity K L e v = unit_m K L e v.
Proof.
  unfold unit_m.
  destruct (v_label (var_raw v)) as [y|] eqn:El;
    [|destruct (lt_dec (v_index (var_raw v)) (ext_depth e)) as [Hi|Hi]].
  2: { rewrite (apply_inner identity e v (W_tinner e _ El Hi) El Hi).
       f_equal; apply var_eq; reflexivity. }
  all: assert (Hr : v_label (var_raw v) = None -> ext_depth e <= v_index (var_raw v))
         by (intros; try lia; congruence).
  all: assert (Hn : napply (radj_n (adj_raw (@identity P N))) (down (ext_depth e) (var_raw v))
                    = inl (down (ext_depth e) (var_raw v))) by apply napply_identity.
  all: assert (H : Is_true_s (wf_var L (up (ext_depth e) (down (ext_depth e) (var_raw v)))))
         by (rewrite (up_down _ _ Hr); apply (var_ok (ext_var e v))).
  all: rewrite (apply_var identity e v _ H Hr Hn); f_equal; apply var_eq; cbn.
  all: apply up_down, Hr.
Qed.

Theorem subst_identity {N} (t : term N) : subst identity t = t.
Proof.
  rewrite (kleisli_ext _ _ _ unit_m (fun K L e v => apply_identity e v)).
  apply kleisli_unit.
Qed.

(** ** Composition *)

Lemma kleisli_rebase_here {N M K L} (f : morph N M) (e : ext N M K L) (t : term K) :
  kleisli f e t = kleisli (rebase_m e f) ext_here t.
Proof. exact (kleisli_rebase _ _ f _ _ _ _ e ext_here t). Qed.

Lemma kleisli_comp_here {N M P'} (g : morph M P') (f : morph N M) (t : term N) :
  kleisli g ext_here (kleisli f ext_here t) = kleisli (comp_m g f) ext_here t.
Proof. symmetry; exact (kleisli_assoc _ _ _ g f _ _ ext_here t). Qed.

Ltac sqa := apply Is_true_s_intro.

Lemma papply_compose_depth n :
  forall ρ, nnest ρ < n ->
  forall M P' Mid L (a : adj P M P') (e' : ext M P' Mid L) HL1 Hx1 HL2 Hx2 (u : P),
  kleisli (apply a) e' (kleisli (papply ρ M (ext_depth e') Mid HL1 Hx1) ext_here u)
  = kleisli (papply (pcomp (adj_raw a) (ρ)) P' (ext_depth e') L HL2 Hx2)
            ext_here u.
Proof.
  induction n as [|n IH]; intros ρ Hdep M P' Mid L a e' HL1 Hx1 HL2 Hx2 u;
    [lia|].
  set (d := ext_depth e') in *.
  set (ρ'' := pcomp (adj_raw a) (ρ)) in *.
  rewrite kleisli_rebase_here, kleisli_comp_here.
  apply kleisli_ext; intros K2 L2 e2 w.
  unfold comp_m; rewrite <- kleisli_rebase.
  pose proof (Is_true_s_elim Hx1) as Hx1b; pose proof (Is_true_s_elim Hx2) as Hx2b.
  pose proof (ext_depth_left Mid e2) as DL; pose proof (ext_depth_right Mid e2) as DR.
  pose proof (ext_depth_app e' (ext_right Mid e2)) as DA; fold d in DA.
  set (e3 := ext_app e' (ext_right Mid e2)) in *.
  destruct (v_label (var_raw w)) as [y|] eqn:El.
  2: { pose proof (W_pinner (ext_left Mid e2) _ (var_ok w) El) as H1.
       rewrite (papply_inner _ _ _ _ _ _ _ w H1 El), kleisli_var.
       assert (Hi : v_index (var_raw w) < ext_depth e3).
       { pose proof (Is_true_s_elim (var_ok w)) as Hw; pose proof (ext_depth_K e2).
         destruct (var_raw w) as [h i]; cbn in El, Hw |- *; subst h.
         apply Nat.ltb_lt in Hw; cbn in Hw; lia. }
       rewrite (apply_inner a e3 (mk_var (var_raw w) H1) (W_tinner e3 _ El Hi) El Hi).
       rewrite (papply_inner _ _ _ _ _ _ e2 w (W_pinner e2 _ (var_ok w) El) El).
       f_equal; apply var_eq; reflexivity. }
  assert (Hl : v_label (var_raw w) <> None) by congruence.
  pose proof (napply_pcompose' a ρ (var_raw w) Hx1b Hl) as Hc; fold ρ'' in Hc.
  destruct (napply ρ (var_raw w)) as [w'|[u3 ρ3]] eqn:E.
  - (* a variable of the payload *)
    assert (H1 : Is_true_s (wf_var (ext_mid Mid e2) (up (d + ext_depth (ext_left Mid e2)) w'))).
    { sqa; apply (pay_var_wf ρ M d Mid (ext_left Mid e2) (var_raw w)); auto.
      apply Nat.eqb_eq, Is_true_s_elim, HL1. }
    rewrite (papply_var _ _ _ _ _ _ _ w w' H1 Hl E), kleisli_var.
    set (wv := {| var_raw := up (d + ext_depth (ext_left Mid e2)) w'; var_ok := H1 |}).
    assert (Hr : v_label (var_raw wv) = None -> ext_depth e3 <= v_index (var_raw wv)).
    { cbn; destruct w' as [[y'|] j]; cbn; [discriminate|intros _; lia]. }
    assert (Hdn : down (ext_depth e3) (var_raw wv) = w').
    { cbn; rewrite DA, DR, DL, (Nat.add_comm (ext_depth e2) d); apply down_up. }
    destruct (napply (radj_n (adj_raw a)) w') as [z|[u2 ρ2]] eqn:E2.
    + assert (H2 : Is_true_s (wf_var L2 (up (ext_depth e3) z))).
      { sqa; apply (top_var_wf a e3 w' z); [|first [exact E2|reflexivity]].
        apply (pay_var_wf ρ M 0 M ext_here (var_raw w) w') in Hx1b; auto; cbn in Hx1b.
        destruct w' as [[y'|] j]; cbn in *; [reflexivity|exact Hx1b]. }
      rewrite (apply_var a e3 wv z H2 Hr) by (rewrite Hdn; first [exact E2|reflexivity]).
      assert (H3 : Is_true_s (wf_var L2 (up (d + ext_depth e2) z))).
      { rewrite DA, DR, Nat.add_comm in H2; exact H2. }
      rewrite (papply_var _ _ _ _ _ _ e2 w z H3 Hl) by (rewrite Hc; first [exact E2|reflexivity]).
      f_equal; apply var_eq; cbn; rewrite DA, DR, Nat.add_comm; reflexivity.
    + assert (Hρ2 : pok P' ρ2 = true).
      { apply (top_payload_ok a w' u2 ρ2); [|exact E2].
        apply (pay_var_wf ρ M 0 M ext_here (var_raw w) w') in Hx1b; auto; cbn in Hx1b.
        destruct w' as [[y'|] j]; cbn in *; [reflexivity|exact Hx1b]. }
      rewrite (apply_pay a e3 wv u2 ρ2 (W_tHL e3) (Is_true_s_intro Hρ2) Hr)
        by (rewrite Hdn; first [exact E2|reflexivity]).
      assert (HL3 : Is_true_s (Nat.eqb L2 ((d + ext_depth e2) + P'))).
      { sqa; apply Nat.eqb_eq; pose proof (ext_depth_L e2); apply Is_true_s_elim, Nat.eqb_eq in HL2; lia. }
      rewrite (papply_pay _ _ _ _ _ _ e2 w u2 ρ2 HL3 (Is_true_s_intro Hρ2) Hl)
        by (rewrite Hc; first [exact E2|reflexivity]).
      rewrite (papply_s_eq ρ2 P' L2 (ext_depth e3) (d + ext_depth e2) ltac:(lia) (W_tHL e3) HL3).
      reflexivity.
  - (* a nested payload *)
    pose proof (napply_depth_pok _ _ _ _ _ Hx1b E) as Hd3.
    assert (Hρ3 : pok M ρ3 = true) by (apply (pay_payload_ok ρ M (var_raw w) u3); auto).
    assert (Hρ3' : pok P' (pcomp (adj_raw a) (ρ3)) = true).
    { apply (pay_payload_ok ρ'' P' (var_raw w) u3); auto. }
    assert (HLa : Is_true_s (Nat.eqb (ext_mid Mid e2) ((d + ext_depth (ext_left Mid e2)) + M))).
    { apply (W_pHL M d (ext_left Mid e2) HL1). }
    rewrite (papply_pay _ _ _ _ _ _ _ w u3 ρ3 HLa (Is_true_s_intro Hρ3) Hl E).
    assert (HLb : Is_true_s (Nat.eqb (ext_mid Mid e2) (ext_depth e3 + M))).
    { sqa; apply Is_true_s_elim, Nat.eqb_eq in HLa; apply Nat.eqb_eq; lia. }
    rewrite (papply_s_eq ρ3 M (ext_mid Mid e2) (d + ext_depth (ext_left Mid e2)) (ext_depth e3) ltac:(lia) HLa HLb).
    assert (HL3 : Is_true_s (Nat.eqb L2 ((d + ext_depth e2) + P'))).
    { sqa; apply Nat.eqb_eq; pose proof (ext_depth_L e2); apply Is_true_s_elim, Nat.eqb_eq in HL2; lia. }
    rewrite (papply_pay _ _ _ _ _ _ e2 w u3 _ HL3 (Is_true_s_intro Hρ3') Hl Hc).
    assert (HL4 : Is_true_s (Nat.eqb L2 (ext_depth e3 + P'))).
    { sqa; apply Is_true_s_elim, Nat.eqb_eq in HL3; apply Nat.eqb_eq; lia. }
    rewrite (papply_s_eq (pcomp (adj_raw a) (ρ3)) P' L2 (d + ext_depth e2) (ext_depth e3) ltac:(lia) HL3 HL4).
    apply IH; lia.
Qed.

Lemma apply_compose {N M P'} (a : adj P M P') (b : adj P N M) {K L} (e : ext N P' K L) v :
  comp_m (apply a) (apply b) K L e v = apply (compose a b) K L e v.
Proof.
  unfold comp_m.
  pose proof (ext_depth_left M e) as DL; pose proof (ext_depth_right M e) as DR.
  set (d := ext_depth e) in *.
  set (el := ext_left M e) in *; set (er := ext_right M e) in *.
  destruct (v_label (var_raw v)) as [y|] eqn:El;
    [|destruct (lt_dec (v_index (var_raw v)) d) as [Hi|Hi]].
  2: { assert (Hi1 : v_index (var_raw v) < ext_depth el) by lia.
       pose proof (W_tinner el _ El Hi1) as H0.
       rewrite (apply_inner b el v H0 El Hi1), kleisli_var.
       assert (Hi2 : v_index (var_raw v) < ext_depth er) by lia.
       rewrite (apply_inner a er (mk_var (var_raw v) H0) (W_tinner er _ El Hi2) El Hi2).
       rewrite (apply_inner (compose a b) e v (W_tinner e _ El Hi) El Hi).
       f_equal; apply var_eq; reflexivity. }
  all: assert (Hr : v_label (var_raw v) = None -> d <= v_index (var_raw v))
         by (intros; try lia; congruence).
  all: assert (Hrl : v_label (var_raw v) = None -> ext_depth el <= v_index (var_raw v))
         by (rewrite DL; exact Hr).
  all: pose proof (napply_rcompose' (adj_raw a) (adj_raw b) (down d (var_raw v))) as Hc.
  all: pose proof (W_tdown e _ (var_ok v) Hr) as Hv'; fold d in Hv'.
  all: destruct (napply (radj_n (adj_raw b)) (down d (var_raw v))) as [w|[u ρ]] eqn:E.
  1,3: (* [b] gives a variable *)
       assert (H1 : Is_true_s (wf_var (ext_mid M e) (up (ext_depth el) w)))
         by (apply Is_true_s_intro, (top_var_wf b el (down d (var_raw v)) w);
             [exact Hv'|exact E]);
       rewrite (apply_var b el v w H1 Hrl) by (rewrite DL; exact E);
       rewrite kleisli_var;
       set (wv := {| var_raw := up (ext_depth el) w; var_ok := H1 |});
       assert (Hr2 : v_label (var_raw wv) = None -> ext_depth er <= v_index (var_raw wv))
         by (cbn; rewrite DL, DR; destruct w as [[y'|] j]; cbn; [discriminate|intros _; lia]);
       assert (Hdn : down (ext_depth er) (var_raw wv) = w)
         by (cbn; rewrite DL, DR; apply down_up);
       assert (Hw : wf_var M w = true)
         by (pose proof (top_result b _ Hv') as X; rewrite E in X; exact X);
       destruct (napply (radj_n (adj_raw a)) w) as [z|[u2 ρ2]] eqn:E2;
       [ assert (H2 : Is_true_s (wf_var L (up (ext_depth er) z)))
           by (apply Is_true_s_intro, (top_var_wf a er w z Hw E2));
         rewrite (apply_var a er wv z H2 Hr2) by (rewrite Hdn; exact E2);
         assert (H3 : Is_true_s (wf_var L (up d z))) by (rewrite DR in H2; exact H2);
         rewrite (apply_var (compose a b) e v z H3 Hr)
           by (cbn [adj_raw compose]; fold d; rewrite Hc; first [exact E2|reflexivity]);
         f_equal; apply var_eq; cbn; rewrite DR; reflexivity
       | pose proof (top_payload_ok a w u2 ρ2 Hw E2) as Hρ2;
         rewrite (apply_pay a er wv u2 ρ2 (W_tHL er) (Is_true_s_intro Hρ2) Hr2)
           by (rewrite Hdn; exact E2);
         rewrite (apply_pay (compose a b) e v u2 ρ2 (W_tHL e) (Is_true_s_intro Hρ2) Hr)
           by (cbn [adj_raw compose]; fold d; rewrite Hc; first [exact E2|reflexivity]);
         rewrite (papply_s_eq ρ2 P' L (ext_depth er) d DR (W_tHL er) (W_tHL e));
         reflexivity ].
  all: (* [b] gives a payload *)
       pose proof (top_payload_ok b _ u ρ Hv' E) as Hρ;
       rewrite (apply_pay b el v u ρ (W_tHL el) (Is_true_s_intro Hρ) Hrl) by (rewrite DL; exact E);
       assert (Hρ' : pok P' (pcomp (adj_raw a) (ρ)) = true)
         by (apply (top_payload_ok (compose a b) (down d (var_raw v)) u);
             [exact Hv'|cbn [adj_raw compose]; fold d; rewrite Hc; reflexivity]);
       rewrite (apply_pay (compose a b) e v u _ (W_tHL e) (Is_true_s_intro Hρ') Hr)
         by (cbn [adj_raw compose]; fold d; rewrite Hc; reflexivity).
  all: assert (HL1 : Is_true_s (Nat.eqb (ext_mid M e) (ext_depth er + M)))
         by (apply Is_true_s_intro, Nat.eqb_eq; pose proof (ext_depth_L el); lia).
  all: rewrite (papply_s_eq ρ M (ext_mid M e) (ext_depth el) (ext_depth er) ltac:(lia) (W_tHL el) HL1).
  all: assert (HL2 : Is_true_s (Nat.eqb L (ext_depth er + P')))
         by (apply Is_true_s_intro, Nat.eqb_eq; pose proof (ext_depth_L e); lia).
  all: rewrite (papply_s_eq _ P' L d (ext_depth er) ltac:(lia) (W_tHL e) HL2).
  all: apply (papply_compose_depth (S (nnest ρ))); lia.
Qed.

Theorem subst_compose {N M P'} (a : adj P M P') (b : adj P N M) (t : term N) :
  subst a (subst b t) = subst (compose a b) t.
Proof.
  rewrite kleisli_comp_here.
  apply kleisli_ext; intros; apply apply_compose.
Qed.

(** ** Variables *)

Lemma apply_here_rename {N M} (a : adj P N M) (v : var N) (w : var M) :
  Indexed.apply_var a v = Rename w -> apply a N M ext_here v = tvar w.
Proof. intros E; rewrite <- (kleisli_var _ _ (apply a) _ _ ext_here v); exact (subst_tvar_rename a v w E). Qed.

Lemma apply_here_bind {N M} (a : adj P N M) (v : var N) u ρ :
  Indexed.apply_var a v = Bind u ρ -> apply a N M ext_here v = psubst ρ u.
Proof.
  intros E.
  assert (Hr : rapply (adj_raw a) (var_raw v) = inr (u, padj_raw ρ)).
  { revert E; unfold Indexed.apply_var; generalize (apply_wf a v); unfold Indexed.apply.
    destruct (rapply (adj_raw a) (var_raw v)) as [w0|[u0 ρ0]]; intros H E; [discriminate|].
    injection E as <- <-; reflexivity. }
  unfold rapply in Hr.
  destruct (napply (radj_n (adj_raw a)) (var_raw v)) as [w0|[u0 x]] eqn:En; cbn in Hr; [discriminate|].
  injection Hr as -> Ex.
  assert (Hwf : nwf true x) by (apply (nwf_payload false _ (var_raw v) u x (radj_wf (adj_raw a)) eq_refl En)).
  assert (Hx : x = rpadj_n (padj_raw ρ)) by (rewrite <- Ex; symmetry; exact (rpadj_n_to_padj x Hwf)).
  assert (Hd : down 0 (var_raw v) = var_raw v)
    by (destruct v as [[[y|] i] Hv]; unfold down; cbn; [reflexivity|rewrite Nat.sub_0_r; reflexivity]).
  assert (Hρ : Is_true_s (pok M x))
    by (apply Is_true_s_intro, (top_payload_ok a (var_raw v) u); [apply Is_true_s_elim, var_ok|exact En]).
  rewrite <- Hd in En.
  rewrite (apply_pay a ext_here v u x (W_tHL ext_here) Hρ (fun _ => le_0_n _) En).
  unfold psubst; subst x; reflexivity.
Qed.

(** Applying a substitution to a variable is the [eval] node, which
    [names] evaluates. *)
Theorem apply_here_eval {N M} (a : adj P N M) (v : var N) :
  apply a N M ext_here v = Indexed.eval tvar psubst a v.
Proof.
  unfold Indexed.eval; destruct (Indexed.apply_var a v) eqn:E;
    [apply apply_here_rename|apply apply_here_bind]; exact E.
Qed.

Theorem apply_under {N M K L} (a : adj P N M) (e : ext N M K L) (v : var (S K)) :
  apply a (S K) (S L) (ext_under e) v = apply (lift a) (S K) (S L) (ext_shift e) v.
Proof. rewrite <- (ext_app_shift e); apply apply_lift_rebase. Qed.

Theorem subst_tvar_eval {N M} (a : adj P N M) (v : var N) :
  subst a (tvar v) = Indexed.eval tvar psubst a v.
Proof. rewrite kleisli_var; apply apply_here_eval. Qed.

Theorem eval_fold {N M} (a : adj P N M) (v : var N) :
  Indexed.eval tvar psubst a v = subst a (tvar v).
Proof. rewrite kleisli_var; symmetry; apply apply_here_eval. Qed.

(** [names] first applies the monad laws that remove a Kleisli extension
    or move work into the adjustment: going under a binder lifts the
    adjustment and nested substitutions fuse ([names_pre]); then
    substituting into a variable is the [eval] node ([names_var]).  After normalising adjustments and
    evaluating [eval] nodes, identity substitutions go, and an [eval]
    node it cannot evaluate is shown as a substitution again. *)
Lemma ext_shift_here {N M} : ext_shift (@ext_here N M) = ext_here.
Proof. reflexivity. Qed.

Lemma ext_shift_under {N M K L} (e : ext N M K L) : ext_shift (ext_under e) = ext_under (ext_shift e).
Proof. reflexivity. Qed.

Global Hint Rewrite @kleisli_apply_under @apply_under @subst_compose @ext_shift_here @ext_shift_under : names_pre.
Global Hint Rewrite @subst_tvar_eval @apply_here_eval : names_var.
(** Applying a payload adjustment [b ∘ ρ] is substituting with [b] after
    applying [ρ]; the identity payload adjustment of a closed term does
    nothing. *)
Theorem psubst_pcompose {K M} (b : adj P K M) (ρ : padj P K) (u : P) :
  psubst (pcompose b ρ) u = subst b (psubst ρ u).
Proof.
  unfold psubst; symmetry.
  exact (papply_compose_depth (S (nnest (rpadj_n (padj_raw ρ)))) _ (Nat.lt_succ_diag_r _) K M K M b ext_here _ _ _ _ u).
Qed.

Theorem psubst_pid (u : P) : psubst (@pid P 0) u = u.
Proof.
  unfold psubst; transitivity (kleisli unit_m (@ext_here 0 0) u); [|apply kleisli_unit].
  apply kleisli_ext; intros K L e w; apply papply_pidentity.
Qed.

(** ** Substitutions that agree on variables agree on terms *)

Lemma var_cases {N} (v : var (S N)) : v = bvar0 \/ exists v0 : var N, v = vshift_bound v0.
Proof.
  destruct v as [[[y|] i] Hv].
  - right; exists (mk_var (mk_rvar (Some y) i) stt); apply var_eq; reflexivity.
  - destruct i as [|i]; [left; apply var_eq; reflexivity|right].
    assert (H : Is_true_s (wf_var N (mk_rvar None i))).
    { apply Is_true_s_intro; pose proof (Is_true_s_elim Hv) as H; cbn in H |- *.
      apply Nat.ltb_lt in H; apply Nat.ltb_lt; lia. }
    exists (mk_var _ H); apply var_eq; cbn; unfold shift_rvar; cbn; f_equal; lia.
Qed.

Lemma tvar_shift_bound {N} (v : var N) : tvar (vshift_bound v) = (tvar v) [⟦ \ · as _ ⟧].
Proof.
  symmetry; apply subst_tvar_rename, apply_var_rename.
  change (adj_raw (⟦ \ · as _ ⟧ : adj P N (S N))) with (rpush_outer None (@ridentity P)).
  rewrite rapply_push_outer, rapply_identity; reflexivity.
Qed.

Lemma tvar_lift_here {N M} (a : adj P N M) : (tvar bvar0) [lift a] = tvar bvar0.
Proof.
  apply subst_tvar_rename, apply_var_rename; rewrite adj_raw_lift, rapply_lift.
  cbn [var_raw bvar0]; rewrite rvar_eqb_refl; reflexivity.
Qed.

Lemma weaken_lift {N M} (a : adj P N M) : ⟦ \ · as _ ⟧ ⨾ lift a = a ⨾ ⟦ \ · as _ ⟧.
Proof.
  apply adj_eq; cbn [adj_raw compose]; rewrite adj_raw_lift.
  change (adj_raw (⟦ \ · as _ ⟧ : adj P N (S N))) with (rpush_outer None (@ridentity P)).
  change (adj_raw (⟦ \ · as _ ⟧ : adj P M (S M))) with (rpush_outer None (@ridentity P)).
  rewrite !(rpush_outer_as_compose None ridentity), !rcompose_identity_r; apply rcompose_lift_shift.
Qed.

Lemma lift_agree {N M} (a a' : adj P N M) :
  (forall v, (tvar v) [a] = (tvar v) [a']) -> forall v, (tvar v) [lift a] = (tvar v) [lift a'].
Proof.
  intros H v; destruct (var_cases v) as [->|[v0 ->]]; [rewrite !tvar_lift_here; reflexivity|].
  rewrite !tvar_shift_bound, !subst_compose, !weaken_lift, <- !subst_compose, H; reflexivity.
Qed.

Lemma apply_agree d : forall N M (a a' : adj P N M), (forall v, (tvar v) [a] = (tvar v) [a']) ->
  forall K L (e : ext N M K L), ext_depth e = d -> forall v, apply a K L e v = apply a' K L e v.
Proof.
  induction d as [|d IH]; intros N M a a' H K L e; destruct e as [|K0 L0 e0]; cbn [ext_depth]; intros Hd v;
    try discriminate.
  - rewrite <- !(kleisli_var _ _ _ _ _ ext_here v); apply H.
  - rewrite <- (ext_app_shift e0), !apply_lift_rebase.
    apply (IH _ _ _ _ (lift_agree a a' H)); rewrite ext_depth_shift; lia.
Qed.

Theorem subst_ext_var {N M} (a a' : adj P N M) :
  (forall v, (tvar v) [a] = (tvar v) [a']) -> forall t, t [a] = t [a'].
Proof.
  intros H t; apply kleisli_ext; intros K L e v; apply (apply_agree (ext_depth e)); [exact H|reflexivity].
Qed.

(** ** Materialising payloads *)

(** A payload adjustment of the closed scope applied to a closed term. *)
Definition pg (ρ : rpadj P) (u : P) : P :=
  match pscoped 0 ρ as b return pscoped 0 ρ = b -> P with
  | true => fun H => psubst (mk_padj (M := 0) ρ (Is_true_s_intro H)) u
  | false => fun _ => u
  end eq_refl.

Lemma pg_ok ρ u (H : Is_true_s (pscoped 0 ρ)) : pg ρ u = psubst (mk_padj (M := 0) ρ H) u.
Proof.
  unfold pg; generalize (@eq_refl _ (pscoped 0 ρ)).
  pose proof (Is_true_s_elim H) as H'.
  generalize (pscoped 0 ρ) at 2 3; intros b Eb; destruct b; [reflexivity|congruence].
Qed.

Lemma pg_spec (b : adj P 0 0) u : pg (rpcompose (adj_raw b) rpidentity) u = u [b].
Proof.
  rewrite (pg_ok _ _ (padj_ok (pcompose b (@pid P 0)))).
  transitivity (psubst (pcompose b (@pid P 0)) u); [reflexivity|].
  rewrite psubst_pcompose, psubst_pid; reflexivity.
Qed.

(** A variable with a payload [W ∘ id] substituted is the variable [W]
    sends it to. *)
Lemma tvar_var_label (w : var 0) : v_label (var_raw w) <> None.
Proof. destruct w as [[[y|] i] Hw]; cbn; [discriminate|exact (match Hw with end)]. Qed.

(** ** Substitutions whose results are related are equal

    [rv M r d L HL t]: [t] is what a look-up with result [r] gives, used
    under [d] binders into [L], payloads in scope [M].  [rv_le r r']: if
    [r] is well-scoped so is [r'], and it gives the same terms.  The
    substitutions by [a] and [a'] are equal when the results of [a] are
    related so to those of [a']; [drel B] relates them so when [B] does. *)
Lemma pay_named (x : nadj) v w : pok 0 x = true -> v_label v <> None -> napply x v = inl w -> v_label w <> None.
Proof.
  intros Hx Hv E; pose proof (pay_var_wf x 0 0 0 (@ext_here 0 0) v w Hx eq_refl Hv E) as H.
  destruct w as [[y|] i]; [discriminate|cbn in H; discriminate].
Qed.

Section Rel.

Variable M : nat.

Definition rv (r : rresult P) (d L : nat) (HL : Is_true_s (Nat.eqb L (d + M))) (t : term L) : Prop :=
  match lower r with
  | inl w => exists H : wf_var L (up d w) = true, t = tvar (mk_var (up d w) (Is_true_s_intro H))
  | inr (u, ρ) => exists Hρ : pok M ρ = true, t = kleisli (papply ρ M d L HL (Is_true_s_intro Hρ)) ext_here u
  end.

Definition rv_le (r r' : rresult P) : Prop :=
  rwf M r = true -> rwf M r' = true /\ forall d L HL t, rv r d L HL t -> rv r' d L HL t.

Lemma rv_det r d d' L HL HL' t t' : d = d' -> rv r d L HL t -> rv r d' L HL' t' -> t = t'.
Proof. intros <-; unfold rv; destruct (lower r) as [w|[u ρ]]; intros [H1 ->] [H2 ->]; reflexivity. Qed.

Lemma rv_cast r d d' L HL HL' t : d = d' -> rv r d L HL t -> rv r d' L HL' t.
Proof. intros <-; exact (fun H => H). Qed.

Lemma HL_cast {L d d'} (E : d = d') (H : Is_true_s (Nat.eqb L (d + M))) : Is_true_s (Nat.eqb L (d' + M)).
Proof. subst; exact H. Qed.

Lemma rv_le_refl r : rv_le r r.
Proof. intros H; split; [exact H|auto]. Qed.

Lemma rv_le_trans r r' r'' : rv_le r r' -> rv_le r' r'' -> rv_le r r''.
Proof.
  intros H1 H2 W; destruct (H1 W) as [W' V1]; destruct (H2 W') as [W'' V2].
  split; [exact W''|auto].
Qed.

Lemma pok_rpadj (ρ : rpadj P) : pscoped M ρ = true -> pok M (rpadj_n ρ) = true.
Proof. intros H; unfold pok; apply andb_true_iff; split; [exact (rpadj_wf ρ)|exact H]. Qed.

Lemma rwf_pack (x : nadj) v : pok M x = true -> v_label v <> None -> rwf M (rpack (napply x v)) = true.
Proof.
  intros Hx Hv; pose proof (pay_result M x v Hx Hv) as R.
  destruct (napply x v) as [w|[u y]] eqn:E; [exact R|].
  cbn [rpack rwf]; rewrite rpadj_n_to_padj by exact (pok_wf M y R).
  apply andb_true_iff in R; exact (proj2 R).
Qed.

Lemma rv_papply x s L0 HL Hx {K L} (e : ext 0 L0 K L) v : v_label (var_raw v) <> None ->
  rv (rpack (napply x (var_raw v))) (s + ext_depth e) L (W_pHL M s e HL) (papply x M s L0 HL Hx K L e v).
Proof.
  intros Hv; pose proof (papply_result x M s L0 HL Hx e v Hv) as R.
  assert (Hxo := Is_true_s_elim Hx).
  assert (HL0 : L0 = s + M) by (apply Nat.eqb_eq, Is_true_s_elim, HL).
  unfold rv; rewrite lower_rpack
    by (intros u y E; exact (nwf_payload true x (var_raw v) u y (pok_wf M x Hxo) ltac:(destruct (v_label (var_raw v)); [reflexivity|contradiction]) E)).
  destruct (napply x (var_raw v)) as [w|[u y]] eqn:E.
  - exists (pay_var_wf x M s L0 e (var_raw v) w Hxo HL0 Hv E); apply R.
  - exists (pay_payload_ok x M (var_raw v) u y Hxo Hv E); apply R.
Qed.

Lemma rv_look {N K L} (a : adj P N M) (e : ext N M K L) v' Hv' :
  rv (rapply (adj_raw a) v') (ext_depth e) L (W_tHL e) (look a e v' Hv').
Proof.
  pose proof (look_result a e v' Hv') as R; unfold rv; rewrite lower_rapply.
  destruct (napply (radj_n (adj_raw a)) v') as [w|[u y]] eqn:E.
  - exists (top_var_wf a e v' w Hv' E); apply R.
  - exists (top_payload_ok a v' u y Hv' E); apply R.
Qed.

Theorem subst_rv {N} (a a' : adj P N M) :
  (forall v : var N, rv_le (rapply (adj_raw a) (var_raw v)) (rapply (adj_raw a') (var_raw v))) ->
  forall t, t [a] = t [a'].
Proof.
  intros H t; apply kleisli_ext; intros K L e v; unfold apply.
  assert (G : forall v' H1 H2, look a e v' H1 = look a' e v' H2).
  { intros v' H1 H2.
    assert (Wf : rwf M (rapply (adj_raw a) v') = true)
      by exact (proj2 (proj1 (scoped_spec N M (adj_raw a)) (Is_true_s_elim (adj_ok a))) v' H1).
    destruct (H (mk_var v' (Is_true_s_intro H1)) Wf) as [_ Hv].
    exact (rv_det _ _ _ _ _ _ _ _ eq_refl (Hv _ _ _ _ (rv_look a e v' H1)) (rv_look a' e v' H2)). }
  destruct v as [[[y|] i] Hv]; cbn [var_raw v_label v_index]; [apply G|].
  destruct (lt_dec i (ext_depth e)); [reflexivity|apply G].
Qed.

Lemma rpcompose_to (W : radj P) y : nwf true y -> rto_padj (ncomp (radj_n W) true y cnone) = rpcompose W (rto_padj y).
Proof.
  intros Hy; pose proof (pcompose_ok W (rto_padj y)) as Hc; rewrite rpadj_n_to_padj in Hc by exact Hy.
  apply rpadj_eq; rewrite rpadj_n_to_padj by exact Hc; cbn [rpcompose rpadj_n]; rewrite rpadj_n_to_padj by exact Hy.
  reflexivity.
Qed.

Lemma rv_le_pay (W W' : radj P) : (forall v, rv_le (rapply W v) (rapply W' v)) ->
  forall n (ρ : rpadj P) u, rpdepth ρ < n -> rv_le (inr (u, rpcompose W ρ)) (inr (u, rpcompose W' ρ)).
Proof.
  intros IHW n; induction n as [|n IH]; intros ρ u Hn; [lia|].
  intros Wf.
  assert (Wf' : rwf M (inr (u, rpcompose W' ρ)) = true).
  { change (pscoped M (rpcompose W' ρ) = true); apply pscoped_spec; intros v Hv.
    pose proof (proj1 (pscoped_spec M (rpcompose W ρ)) Wf v Hv) as R.
    rewrite rpapply_pcompose in R |- * by exact Hv.
    destruct (rpapply ρ v) as [w|[u' ρ']] eqn:E.
    - exact (proj1 (IHW w R)).
    - pose proof (rpdepth_payload ρ v u' ρ' Hv E); exact (proj1 (IH ρ' u' ltac:(lia) R)). }
  split; [exact Wf'|].
  intros d L HL t [Hρ ->]; exists (pok_rpadj _ Wf').
  change (rpadj_n (rpcompose W ρ)) with (ncomp (radj_n W) true (rpadj_n ρ) cnone) in Hρ |- *.
  change (rpadj_n (rpcompose W' ρ)) with (ncomp (radj_n W') true (rpadj_n ρ) cnone).
  apply kleisli_ext; intros K L' e v.
  destruct (v_label (var_raw v)) eqn:Hl.
  2: { transitivity (tvar (mk_var (var_raw v) (W_pinner e _ (var_ok v) Hl)));
         [|symmetry]; apply papply_inner, Hl. }
  assert (Hv : v_label (var_raw v) <> None) by (rewrite Hl; discriminate).
  pose proof (rv_papply _ d L HL (Is_true_s_intro Hρ) e v Hv) as R1.
  pose proof (rv_papply _ d L HL (Is_true_s_intro (pok_rpadj _ Wf')) e v Hv) as R2.
  enough (Q : rv_le (rpack (napply (ncomp (radj_n W) true (rpadj_n ρ) cnone) (var_raw v)))
                    (rpack (napply (ncomp (radj_n W') true (rpadj_n ρ) cnone) (var_raw v))))
    by exact (rv_det _ _ _ _ _ _ _ _ eq_refl (proj2 (Q (rwf_pack _ _ Hρ Hv)) _ _ _ _ R1) R2).
  assert (Ed := napply_pcompose W (rpadj_n ρ) (var_raw v) (rpadj_wf ρ) Hv).
  rewrite Ed, (napply_pcompose W' (rpadj_n ρ) (var_raw v) (rpadj_wf ρ) Hv).
  destruct (napply (rpadj_n ρ) (var_raw v)) as [w|[u' y]] eqn:E; [exact (IHW w)|].
  assert (Hy : nwf true y) by exact (nwf_payload true _ (var_raw v) u' y (rpadj_wf ρ) ltac:(rewrite Hl; reflexivity) E).
  cbn [rpack]; rewrite !rpcompose_to by exact Hy.
  apply IH; apply (Nat.lt_le_trans _ (rpdepth ρ)); [|lia].
  apply (rpdepth_payload ρ (var_raw v) u' (rto_padj y) Hv); unfold rpapply; rewrite E; reflexivity.
Qed.

(** Results related by the base relations. *)
Lemma vbase_rv r r' : vbase (@tvar 0) r r' -> rv_le r r'.
Proof.
  intros [w [W [-> ->]]] Wf.
  assert (Hlw := tvar_var_label w).
  assert (Hid : forall x : var 0, napply (rpadj_n (@rpidentity P)) (var_raw x) = inl (var_raw x) :> result)
    by (intros [[[y|] i] Hx]; [reflexivity|exact (match Hx with end)]).
  split.
  - pose proof (proj1 (pscoped_spec M _) Wf (var_raw w) Hlw) as R.
    rewrite rpapply_pcompose in R by exact Hlw; unfold rpapply in R; rewrite Hid in R; exact R.
  - intros d L HL t [Hρ ->]; rewrite kleisli_var.
    pose proof (rv_papply _ d L HL (Is_true_s_intro Hρ) ext_here w Hlw) as R1.
    change (rpadj_n (rpcompose W rpidentity)) with (ncomp (radj_n W) true (rpadj_n (@rpidentity P)) cnone) in R1.
    rewrite napply_pcompose in R1 by (apply rpadj_wf || exact Hlw).
    rewrite Hid in R1; exact (rv_cast _ _ _ _ _ _ _ (Nat.add_0_r d) R1).
Qed.

Lemma pscoped_after_depth (W : radj P) n : pscoped M (rpcompose W rpidentity) = true ->
  forall ρ, rpdepth ρ < n -> pscoped 0 ρ = true -> pscoped M (rpcompose W ρ) = true.
Proof.
  intros HW; induction n as [|n IH]; intros ρ Hd Hρ; [lia|].
  apply pscoped_spec; intros v Hv; rewrite rpapply_pcompose by exact Hv.
  pose proof (proj1 (pscoped_spec 0 ρ) Hρ v Hv) as Hr.
  destruct (rpapply ρ v) as [w|[u ρ']] eqn:E.
  - assert (Hw : v_label w <> None) by (destruct w as [[y|] i]; [discriminate|cbn in Hr; discriminate]).
    pose proof (proj1 (pscoped_spec M _) HW w Hw) as R.
    rewrite rpapply_pcompose in R by exact Hw; rewrite rpapply_identity in R by exact Hw; exact R.
  - cbn [fst snd]; rewrite result_wf_inr in Hr |- *; pose proof (rpdepth_payload ρ v u ρ' Hv E); apply IH; [lia|exact Hr].
Qed.

(** A morphism that sends a variable [v] where [W] does, used under
    [d0] binders. *)
Definition hrel (W : radj P) (d0 : nat) {m L1} (h : morph m L1) : Prop :=
  forall K L (e : ext m L1 K L) v,
    (v_label (var_raw v) = None -> exists H : wf_var L (var_raw v) = true, h K L e v = tvar (mk_var (var_raw v) (Is_true_s_intro H)))
    /\ (v_label (var_raw v) <> None -> forall HL, rv (rapply W (var_raw v)) (d0 + ext_depth e) L HL (h K L e v)).

Lemma hrel_rebase W d0 {m L1 K0 L0} (e0 : ext m L1 K0 L0) h : hrel W d0 h -> hrel W (d0 + ext_depth e0) (rebase_m e0 h).
Proof.
  intros Hh K L e v; destruct (Hh K L (ext_app e0 e) v) as [H1 H2]; split; [exact H1|].
  intros Hv HL.
  assert (E : d0 + ext_depth e0 + ext_depth e = d0 + ext_depth (ext_app e0 e)) by (rewrite ext_depth_app; lia).
  exact (rv_cast _ _ _ _ _ _ _ (eq_sym E) (H2 Hv (HL_cast E HL))).
Qed.

Lemma comp_papply (W : radj P) n : forall y, nnest y < n ->
  forall s m HLm (Hy : Is_true_s (pok 0 y)) d0 L1 HL1 (Hz : Is_true_s (pok M (ncomp (radj_n W) true y cnone)))
    (h : morph m L1), hrel W d0 h ->
  forall u, kleisli h ext_here (kleisli (papply y 0 s m HLm Hy) ext_here u)
            = kleisli (papply (ncomp (radj_n W) true y cnone) M d0 L1 HL1 Hz) ext_here u.
Proof.
  induction n as [|n IH]; intros y Hn s m HLm Hy d0 L1 HL1 Hz h Hh u; [lia|].
  rewrite kleisli_comp_here; apply kleisli_ext; intros K L e v; unfold comp_m.
  destruct (v_label (var_raw v)) eqn:Hl.
  2: { rewrite (papply_inner _ _ _ _ _ _ (ext_left m e) v (W_pinner (ext_left m e) _ (var_ok v) Hl) Hl), kleisli_var.
       rewrite (papply_inner _ _ _ _ _ _ e v (W_pinner e _ (var_ok v) Hl) Hl).
       destruct (proj1 (Hh _ _ (ext_right m e) (mk_var (var_raw v) (W_pinner (ext_left m e) _ (var_ok v) Hl))) Hl) as [H ->].
       reflexivity. }
  assert (Hv : v_label (var_raw v) <> None) by (rewrite Hl; discriminate).
  assert (Hyo := Is_true_s_elim Hy); assert (Hzo := Is_true_s_elim Hz).
  pose proof (papply_result y 0 s m HLm Hy (ext_left m e) v Hv) as R1.
  pose proof (rv_papply _ d0 L1 HL1 Hz e v Hv) as R2.
  rewrite napply_pcompose in R2 by (apply (pok_wf 0 y Hyo) || exact Hv).
  assert (Er : ext_depth (ext_right m e) = ext_depth e) by apply ext_depth_right.
  destruct (napply y (var_raw v)) as [w|[u' y']] eqn:E.
  - destruct w as [[yw|] iw]; [|exfalso; exact (pay_named y _ _ Hyo Hv E eq_refl)].
    rewrite (R1 (Is_true_s_intro eq_refl)), kleisli_var.
    pose proof (proj2 (Hh _ _ (ext_right m e) (mk_var (up (s + ext_depth (ext_left m e)) (mk_rvar (Some yw) iw)) (Is_true_s_intro eq_refl)))
                  ltac:(discriminate) (HL_cast (f_equal (Nat.add d0) (eq_sym Er)) (W_pHL M d0 e HL1))) as R3.
    exact (rv_det _ _ _ _ _ _ _ _ (f_equal (Nat.add d0) Er) R3 R2).
  - assert (Hy' := Is_true_s_intro (pay_payload_ok y 0 _ u' y' Hyo Hv E)).
    rewrite (R1 (W_pHL 0 s (ext_left m e) HLm) Hy').
    assert (Hwy : nwf true (ncomp (radj_n W) true y' cnone))
      by exact (proj1 (comp_correct (radj_n W) (radj_local W) (radj_wf W) true y' (pok_wf 0 y' (Is_true_s_elim Hy')))).
    unfold rv in R2; rewrite lower_rpack in R2 by (intros u0 x0 E0; injection E0 as <- <-; exact Hwy).
    destruct R2 as [Hz' ->].
    rewrite (kleisli_rebase_here h (ext_right m e)); apply IH.
    + pose proof (napply_depth_pok 0 y _ u' y' Hyo E); lia.
    + pose proof (hrel_rebase W d0 (ext_right m e) h Hh) as H'; rewrite Er in H'; exact H'.
Qed.

End Rel.

(** Weakening: a morphism that sends each variable to itself. *)
Definition weak {m L1} (h : morph m L1) : Prop :=
  forall K L (e : ext m L1 K L) v, exists H : wf_var L (var_raw v) = true, h K L e v = tvar (mk_var (var_raw v) (Is_true_s_intro H)).

Lemma weak_rebase {m L1 K0 L0} (e0 : ext m L1 K0 L0) h : weak h -> weak (rebase_m e0 h).
Proof. intros Hh K L e v; apply Hh. Qed.

Lemma weak_pid Mρ s L0 HL Hx : weak (papply pidentity_n Mρ s L0 HL Hx).
Proof.
  intros K L e v; destruct v as [[[y|] i] Hw].
  - exists eq_refl.
    exact (papply_var _ Mρ s L0 HL Hx e (mk_var (mk_rvar (Some y) i) Hw) (mk_rvar (Some y) i) (Is_true_s_intro eq_refl)
             ltac:(discriminate) eq_refl).
  - assert (Hl : v_label (var_raw (mk_var (mk_rvar None i) Hw)) = None) by reflexivity.
    exists (Is_true_s_elim (W_pinner e _ Hw Hl)); apply papply_inner, Hl.
Qed.


Lemma weak_papply n : forall y, nnest y < n ->
  forall s m (HLm : Is_true_s (Nat.eqb m (s + 0))) Mr s' L1 (HL1 : Is_true_s (Nat.eqb L1 (s' + Mr)))
    (Hy : Is_true_s (pok 0 y)) (Hy' : Is_true_s (pok Mr y)) (h : morph m L1), weak h ->
  forall u, kleisli h ext_here (kleisli (papply y 0 s m HLm Hy) ext_here u) = kleisli (papply y Mr s' L1 HL1 Hy') ext_here u.
Proof.
  induction n as [|n IH]; intros y Hn s m HLm Mr s' L1 HL1 Hy Hyr h Hh u; [lia|].
  rewrite kleisli_comp_here; apply kleisli_ext; intros K L e v; unfold comp_m.
  destruct (v_label (var_raw v)) eqn:Hl.
  2: { rewrite (papply_inner _ _ _ _ _ _ (ext_left m e) v (W_pinner (ext_left m e) _ (var_ok v) Hl) Hl), kleisli_var.
       rewrite (papply_inner _ _ _ _ _ _ e v (W_pinner e _ (var_ok v) Hl) Hl).
       destruct (Hh _ _ (ext_right m e) (mk_var (var_raw v) (W_pinner (ext_left m e) _ (var_ok v) Hl))) as [H ->].
       reflexivity. }
  assert (Hv : v_label (var_raw v) <> None) by (rewrite Hl; discriminate).
  assert (Hyo := Is_true_s_elim Hy); assert (Hyro := Is_true_s_elim Hyr).
  pose proof (papply_result y 0 s m HLm Hy (ext_left m e) v Hv) as R1.
  pose proof (papply_result y Mr s' L1 HL1 Hyr e v Hv) as R2.
  destruct (napply y (var_raw v)) as [w|[u' y']] eqn:E.
  - destruct w as [[yw|] iw]; [|exfalso; exact (pay_named y _ _ Hyo Hv E eq_refl)].
    rewrite (R1 (Is_true_s_intro eq_refl)), kleisli_var, (R2 (Is_true_s_intro eq_refl)).
    destruct (Hh _ _ (ext_right m e) (mk_var (up (s + ext_depth (ext_left m e)) (mk_rvar (Some yw) iw)) (Is_true_s_intro eq_refl)))
      as [H ->].
    reflexivity.
  - assert (Hy0 := Is_true_s_intro (pay_payload_ok y 0 _ u' y' Hyo Hv E)).
    assert (Hyr' := Is_true_s_intro (pay_payload_ok y Mr _ u' y' Hyro Hv E)).
    rewrite (R1 (W_pHL 0 s (ext_left m e) HLm) Hy0), (R2 (W_pHL Mr s' e HL1) Hyr').
    rewrite (kleisli_rebase_here h (ext_right m e)); apply IH; [|apply weak_rebase, Hh].
    pose proof (napply_depth_pok 0 y _ u' y' Hyo E); lia.
Qed.

Lemma pscoped_identity M : pscoped M (@rpidentity P) = true.
Proof. apply pscoped_spec; intros v Hv; rewrite rpapply_identity by exact Hv; destruct v as [[y|] i]; [reflexivity|contradiction]. Qed.

Lemma pg_scoped (c : adj P 0 0) : Is_true_s (pscoped 0 (rpcompose (adj_raw c) rpidentity)).
Proof. exact (padj_ok (pcompose c (@pid P 0))). Qed.

Lemma pg_subst (c : adj P 0 0) u :
  pg (rpcompose (adj_raw c) rpidentity) u
  = kleisli (papply (ncomp (radj_n (adj_raw c)) true pidentity_n cnone) 0 0 0 (Is_true_s_intro (Nat.eqb_refl 0))
                    (padj_pok (pcompose c (@pid P 0)))) ext_here u.
Proof. rewrite (pg_ok _ _ (pg_scoped c)); reflexivity. Qed.

Lemma matbase_rv M r r' : matbase pg r r' -> rv_le M r r'.
Proof.
  intros [u [c [-> ->]]] _; split; [exact (pscoped_identity M)|].
  intros d L HL t [Hρ ->]; exists (pok_rpadj M _ (pscoped_identity M)).
  rewrite pg_subst; symmetry.
  apply (weak_papply (S (nnest (ncomp (radj_n (adj_raw c)) true pidentity_n cnone)))); [apply Nat.lt_succ_diag_r|apply weak_pid].
Qed.

Lemma nbase_rv M r r' : nbase pg r r' -> rv_le M r r'.
Proof.
  intros [u [c [W [-> ->]]]] Wf.
  assert (Wf' : rwf M (inr (u, rpcompose W (rpcompose (adj_raw c) rpidentity))) = true)
    by exact (pscoped_after_depth M W _ Wf _ (Nat.lt_succ_diag_r _) (Is_true_s_elim (pg_scoped c))).
  split; [exact Wf'|].
  intros d L HL t [Hρ ->]; exists (pok_rpadj M _ Wf').
  rewrite pg_subst.
  change (rpadj_n (rpcompose W rpidentity)) with (ncomp (radj_n W) true (rpadj_n (@rpidentity P)) cnone) in Hρ |- *.
  change (rpadj_n (rpcompose W (rpcompose (adj_raw c) rpidentity)))
    with (ncomp (radj_n W) true (ncomp (radj_n (adj_raw c)) true pidentity_n cnone) cnone).
  apply (comp_papply M W (S (nnest (ncomp (radj_n (adj_raw c)) true pidentity_n cnone)))); [apply Nat.lt_succ_diag_r|].
  intros K L' e v; split.
  - intros Hl; exists (Is_true_s_elim (W_pinner e _ (var_ok v) Hl)); apply papply_inner, Hl.
  - intros Hv HL'.
    pose proof (rv_papply M _ d L HL (Is_true_s_intro Hρ) e v Hv) as R.
    rewrite napply_pcompose in R by (apply rpadj_wf || exact Hv).
    assert (Hid : napply (rpadj_n (@rpidentity P)) (var_raw v) = inl (var_raw v))
      by (destruct v as [[[y|] i] Hw]; [reflexivity|contradiction]).
    rewrite Hid in R; exact (rv_cast M _ _ _ _ _ _ _ eq_refl R).
Qed.

Lemma lawbase_rv M r r' : lawbase (@tvar 0) pg r r' -> rv_le M r r'.
Proof. intros [H|[H|H]]; [apply matbase_rv|apply nbase_rv|apply vbase_rv]; exact H. Qed.

Lemma drel_rv M (B : rresult P -> rresult P -> Prop) : (forall r r', B r r' -> rv_le M r r') ->
  forall r r', drel B r r' -> rv_le M r r'.
Proof.
  intros HB r r' H; induction H as [r|r r' Hb|u W W' ρ _ IH|r r' r'' _ IH1 _ IH2].
  - apply rv_le_refl.
  - apply HB, Hb.
  - apply (rv_le_pay M W W' IH (S (rpdepth ρ))); apply Nat.lt_succ_diag_r.
  - exact (rv_le_trans M _ _ _ IH1 IH2).
Qed.

Theorem subst_rel {N M} (a a' : adj P N M) :
  (forall v : var N, drel (lawbase (@tvar 0) pg) (rapply (adj_raw a) (var_raw v)) (rapply (adj_raw a') (var_raw v))) ->
  forall t, t [a] = t [a'].
Proof. intros H; apply subst_rv; intros v; apply (drel_rv M _ (lawbase_rv M)), H. Qed.

(** Substitution as the node [names] works on. *)
Definition subst_law : SubstLaw term (@tvar 0) (fun N M a t => t [a]) pg :=
  {| sl_g := pg_spec; sl_rel := @subst_rel |}.

Lemma subst_csubst {N M} (a : adj P N M) (t : term N) : t [a] = csubst subst_law a t.
Proof. reflexivity. Qed.

Lemma csubst_subst {N M} (a : adj P N M) (t : term N) : csubst subst_law a t = t [a].
Proof. reflexivity. Qed.

Lemma tvar_cvar (w : var 0) : tvar w = cvar subst_law w.
Proof. reflexivity. Qed.

Lemma cvar_tvar (w : var 0) : cvar subst_law w = tvar w.
Proof. reflexivity. Qed.

Global Hint Rewrite @subst_csubst @tvar_cvar : names_node.
Global Hint Rewrite @csubst_subst @cvar_tvar : names_post.
Global Hint Rewrite @subst_identity @eval_fold @psubst_pcompose @psubst_pid : names_post.

End Subst.
