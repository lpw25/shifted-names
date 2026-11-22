(** * Substitution for a syntax

    Given a syntax with a Kleisli extension (Syntax.v), [apply a] is the
    morphism of an adjustment [a] and [t [a]] is substitution.  Payload
    terms have scopes of their own: a result [(u, ρ)] is a term [u] of
    scope [K] with an adjustment [ρ] from [K], and becomes [u [ρ]], used
    under the binders crossed so far.  One function, [gapply], does both:
    it applies a raw adjustment from [Kx] to [Mx] under [s] outer binders,
    and its payloads recursively. *)

From Stdlib Require Import PArith Arith List Lia Bool StrictProp.
From ShiftedNames.Core Require Import Trie Label Var Counts Based Skew ATrie Repr Point Deep Compose
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

Context {T : Type} {TS : TermScope T}.

Local Notation nadj := (@nadj T).
Local Notation entry := (@entry T).
Local Notation target := (@target T).

(** A raw adjustment scoped from [K] to [M]. *)
Definition aok (K M : nat) (x : nadj) : bool :=
  nwfc false (fun r => r) x && (scoped_tail K M x && pscopedc M (fun r => r) x).

(** An adjustment with its root read through [rt] (a lazy base,
    Lookup.v). *)
Definition absn (rt : counts -> lbase) (x : nadj) : nadj :=
  match x with NAdj r es => NAdj (lcounts (rt r)) es end.

Lemma aok_wf K M x : aok K M x = true -> nwf false x.
Proof. unfold aok; rewrite andb_true_iff; intros [H _]; exact H. Qed.

Lemma aok_local K M x : aok K M x = true -> nlocal Qall x.
Proof. intros H; apply (nwf_local false), (aok_wf K M), H. Qed.

Lemma aok_scoped K M (a : radj T) : aok K M (radj_n a) = scoped K M a.
Proof. unfold aok, scoped; rewrite (radj_wf a); reflexivity. Qed.

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

(** What the scoping of an adjustment says about its results. *)
Lemma res_wf K M x v :
  aok K M x = true -> wf_var K v = true ->
  match napply x v with
  | inl w => wf_var M w = true
  | inr (u, ρ) => aok (tscope u) M ρ = true
  end.
Proof.
  intros Hx Hv; pose proof (aok_wf _ _ _ Hx) as Hw.
  set (a := mk_radj x (Is_true_s_intro Hw)).
  assert (Hs : scoped K M a = true) by (rewrite <- aok_scoped; exact Hx).
  pose proof (proj2 (proj1 (scoped_spec K M a) Hs) v Hv) as H; unfold rapply in H; cbn [radj_n a] in H.
  destruct (napply x v) as [w|[u y]] eqn:E; [exact H|].
  assert (Hy : nwf false y) by exact (nwf_payload false x v u y Hw eq_refl E).
  cbn [rpack result_wf rwf] in H; rewrite <- aok_scoped, radj_n_to_adj in H by exact Hy; exact H.
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

(** ** Strict wrappers used inside [gapply]

    From where a lookup found something, and the invariants, the scoping of
    the result. *)

Section Wrappers.

Context {T : Type} {TS : TermScope T}.

Local Notation nadj := (@nadj T).
Local Notation entry := (@entry T).
Local Notation target := (@target T).

Lemma rel_some (rv : rvar) y : v_label rv = Some y -> v_label rv = None -> forall d, d <= v_index rv.
Proof. congruence. Qed.

Lemma rel_ge (rv : rvar) d : ~ v_index rv < d -> v_label rv = None -> d <= v_index rv.
Proof. intros H _; lia. Qed.

Lemma W_inner {N M K L} (e : ext N M K L) (rv : rvar) (Hl : v_label rv = None)
  (Hb : v_index rv < ext_depth e) : Is_true_s (wf_var L rv).
Proof. apply Is_true_s_intro, (inner_wf e); [exact Hl|exact Hb]. Qed.

Lemma W_down {N M K L} (e : ext N M K L) (rv : rvar) (Hv : Is_true_s (wf_var K rv))
  (Hrel : v_label rv = None -> ext_depth e <= v_index rv) :
  wf_var N (down (ext_depth e) rv) = true.
Proof. apply down_wf; [apply Is_true_s_elim, Hv|exact Hrel]. Qed.

Lemma W_HL {Kx L0 K L} Mx s (e : ext Kx L0 K L) (HL : Is_true_s (Nat.eqb L0 (s + Mx))) :
  Is_true_s (Nat.eqb L ((s + ext_depth e) + Mx)).
Proof.
  apply Is_true_s_intro; apply Is_true_s_elim, Nat.eqb_eq in HL; apply Nat.eqb_eq.
  pose proof (ext_depth_L e); lia.
Qed.

Lemma aok_squash K M (X : nadj) (Hx : Is_true_s (aok K M X)) : Squash (nlocal Qall X).
Proof. apply Is_true_s_elim in Hx; exact (squash (aok_local _ _ _ Hx)). Qed.

Lemma found_at R (es : atrie entry) v' Be h ts len p :
  nlocal Qall (NAdj R es) ->
  option_map (unshift R) (aget (label_key (v_label v')) es) = Some (unshift (lcounts Be) (Entry h ts len p)) ->
  h = v_label v'.
Proof.
  intros Hl H1; destruct (found_entry _ _ _ _ _ _ _ _ _ Hl H1) as [Hk _]; apply label_key_inj, Hk.
Qed.

(** A variable found as a target. *)
Lemma W_var Kx Mx s L0 {K L} (e : ext Kx L0 K L) R (es : atrie entry) v' (Hv' : wf_var Kx v' = true)
  Be h ts len p Bt y' j
  (HL : Is_true_s (Nat.eqb L0 (s + Mx))) (Hx : Is_true_s (aok Kx Mx (NAdj R es)))
  (H1 : Squash (option_map (unshift R) (aget (label_key (v_label v')) es) = Some (unshift (lcounts Be) (Entry h ts len p))))
  (Hi : v_index v' < len)
  (H2 : Squash (option_map (unshift (lcounts Be)) (knth ts (v_index v')) = Some (unshift (lcounts Bt) (TVar y' j)))) :
  Is_true_s (wf_var L (up (s + ext_depth e) (mk_rvar y' (ldval Bt (label_key y') + j)))).
Proof.
  rewrite ldval_spec;
  destruct H1 as [H1], H2 as [H2]; apply Is_true_s_elim in Hx, HL; apply Nat.eqb_eq in HL.
  apply Is_true_s_intro; pose proof (aok_local _ _ _ Hx) as Hl.
  pose proof (found_at _ _ _ _ _ _ _ _ Hl H1) as Eh.
  destruct (found_entry _ _ _ _ _ _ _ _ _ Hl H1) as [_ [_ [_ [_ [Ht _]]]]].
  pose proof (res_wf Kx Mx _ v' Hx Hv') as Hr; rewrite (rvar_eta v'), <- Eh, (Ht _ (lcounts Bt) _ Hi H2) in Hr; cbn in Hr.
  pose proof (ext_depth_L e); apply (wf_eq L ((s + ext_depth e) + Mx)); [lia|apply up_wf, Hr].
Qed.

(** A payload found as a target. *)
Lemma W_pay Kx Mx R (es : atrie entry) v' (Hv' : wf_var Kx v' = true) Be h ts len p Bt u (rho : nadj)
  (Hx : Is_true_s (aok Kx Mx (NAdj R es)))
  (H1 : Squash (option_map (unshift R) (aget (label_key (v_label v')) es) = Some (unshift (lcounts Be) (Entry h ts len p))))
  (Hi : v_index v' < len)
  (H2 : Squash (option_map (unshift (lcounts Be)) (knth ts (v_index v')) = Some (unshift (lcounts Bt) (TBind u rho)))) :
  Is_true_s (aok (tscope u) Mx (absn (LAdd Bt) rho)).
Proof.
  destruct H1 as [H1], H2 as [H2]; apply Is_true_s_elim in Hx.
  apply Is_true_s_intro; pose proof (aok_local _ _ _ Hx) as Hl.
  pose proof (found_at _ _ _ _ _ _ _ _ Hl H1) as Eh.
  destruct (found_entry _ _ _ _ _ _ _ _ _ Hl H1) as [_ [_ [_ [_ [Ht _]]]]].
  pose proof (res_wf Kx Mx _ v' Hx Hv') as Hr; rewrite (rvar_eta v'), <- Eh, (Ht _ (lcounts Bt) _ Hi H2) in Hr.
  destruct rho as [r0 es0]; exact Hr.
Qed.

(** Pass-through. *)
Lemma W_pass Kx Mx s L0 {K L} (e : ext Kx L0 K L) R (es : atrie entry) v' (Hv' : wf_var Kx v' = true) Be h ts len p
  (HL : Is_true_s (Nat.eqb L0 (s + Mx))) (Hx : Is_true_s (aok Kx Mx (NAdj R es)))
  (H1 : Squash (option_map (unshift R) (aget (label_key (v_label v')) es) = Some (unshift (lcounts Be) (Entry h ts len p))))
  (Hi : ~ v_index v' < len) :
  Is_true_s (wf_var L (up (s + ext_depth e) (mk_rvar h (ldval Be (label_key h) + (v_index v' - len + p))))).
Proof.
  rewrite ldval_spec;
  destruct H1 as [H1]; apply Is_true_s_elim in Hx, HL; apply Nat.eqb_eq in HL.
  apply Is_true_s_intro; pose proof (aok_local _ _ _ Hx) as Hl.
  pose proof (found_at _ _ _ _ _ _ _ _ Hl H1) as Eh.
  destruct (found_entry _ _ _ _ _ _ _ _ _ Hl H1) as [_ [_ [_ [_ [_ [Hp _]]]]]].
  pose proof (res_wf Kx Mx _ v' Hx Hv') as Hr; rewrite (rvar_eta v'), <- Eh, (Hp (v_index v') ltac:(lia)) in Hr; cbn in Hr.
  pose proof (ext_depth_L e); apply (wf_eq L ((s + ext_depth e) + Mx)); [lia|apply up_wf, Hr].
Qed.

(** No entry. *)
Lemma W_none Kx Mx s L0 {K L} (e : ext Kx L0 K L) R (es : atrie entry) v' (Hv' : wf_var Kx v' = true)
  (HL : Is_true_s (Nat.eqb L0 (s + Mx))) (Hx : Is_true_s (aok Kx Mx (NAdj (lcounts R) es)))
  (H1 : Squash (aget (label_key (v_label v')) es = None)) :
  Is_true_s (wf_var L (up (s + ext_depth e) (mk_rvar (v_label v') (ldval R (label_key (v_label v')) + v_index v')))).
Proof.
  rewrite ldval_spec; destruct H1 as [H1]; apply Is_true_s_elim in Hx, HL; apply Nat.eqb_eq in HL; apply Is_true_s_intro.
  pose proof (res_wf Kx Mx _ v' Hx Hv') as Hr.
  rewrite (rvar_eta v'), found_none in Hr by exact H1; cbn in Hr.
  pose proof (ext_depth_L e); apply (wf_eq L ((s + ext_depth e) + Mx)); [lia|apply up_wf, Hr].
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

End Wrappers.

(** ** Substitution for a syntax *)

Module Subst (Import S : SYNTAX).

Local Notation P := {K & term K}.
Local Notation nadj := (@nadj P).
Local Notation entry := (@entry P).
Local Notation target := (@target P).

(** [gapply rt x Kx Mx s L0]: the morphism of the adjustment [x] from [Kx]
    to [Mx], its root read through [rt] (adding the base it is stored
    over), used under [s] outer binders, into [L0]. *)
Fixpoint gapply (rt : counts -> lbase) (x : nadj) (Kx Mx s L0 : nat) (HL : Is_true_s (Nat.eqb L0 (s + Mx)))
  (Hx : Is_true_s (aok Kx Mx (absn rt x))) {struct x} : morph Kx L0 :=
  fun K L e v =>
  let rv := var_raw v in
  let look (v' : rvar) (Hv' : wf_var Kx v' = true) : term L :=
    match x as x0 return Is_true_s (aok Kx Mx (absn rt x0)) -> term L with
    | NAdj r es => fun Hx =>
        aget_with (label_key (v_label v')) es (rt r)
          (fun Be ent =>
             match ent as ent0
                   return Squash (option_map (unshift (lcounts (rt r))) (aget (label_key (v_label v')) es) = Some (unshift (lcounts Be) ent0)) -> term L with
             | Entry h ts len p => fun H1 =>
                 match lt_dec (v_index v') len with
                 | Specif.left Hi =>
                     knth_with (v_index v') ts Be
                       (fun Bt t =>
                          match t as t0
                                return Squash (option_map (unshift (lcounts Be)) (knth ts (v_index v')) = Some (unshift (lcounts Bt) t0)) -> term L with
                          | TVar y' j => fun H2 =>
                              tvar (mk_var (up (s + ext_depth e) (mk_rvar y' (ldval Bt (label_key y') + j)))
                                      (W_var Kx Mx s L0 e (lcounts (rt r)) es v' Hv' Be h ts len p Bt y' j HL Hx H1 Hi H2))
                          | TBind u rho => fun H2 =>
                              kleisli (gapply (LAdd Bt) rho (projT1 u) Mx (s + ext_depth e) L (W_HL Mx s e HL)
                                         (W_pay Kx Mx (lcounts (rt r)) es v' Hv' Be h ts len p Bt u rho Hx H1 Hi H2))
                                      ext_here (projT2 u)
                          end)
                       (fun H2 => match W_absurd Qall (lcounts (rt r)) es _ (v_index v') Be h ts len p (aok_squash Kx Mx _ Hx) H1 Hi H2
                                  with end)
                 | Specif.right Hi =>
                     tvar (mk_var (up (s + ext_depth e) (mk_rvar h (ldval Be (label_key h) + (v_index v' - len + p))))
                             (W_pass Kx Mx s L0 e (lcounts (rt r)) es v' Hv' Be h ts len p HL Hx H1 Hi))
                 end
             end)
          (fun H1 =>
             tvar (mk_var (up (s + ext_depth e) (mk_rvar (v_label v') (ldval (rt r) (label_key (v_label v')) + v_index v')))
                     (W_none Kx Mx s L0 e (rt r) es v' Hv' HL Hx H1)))
    end Hx in
  match v_label rv as o return v_label rv = o -> term L with
  | None => fun Hl =>
      match lt_dec (v_index rv) (ext_depth e) with
      | Specif.left Hb => tvar (mk_var rv (W_inner e rv Hl Hb))
      | Specif.right Hb => look (down (ext_depth e) rv) (W_down e rv (var_ok v) (rel_ge rv _ Hb))
      end
  | Some y => fun Hl => look (down (ext_depth e) rv) (W_down e rv (var_ok v) (fun H => rel_some rv y Hl H _))
  end eq_refl.

Lemma adj_aok {N M} (a : adj term N M) : Is_true_s (aok N M (absn LAbs (radj_n (adj_raw a)))).
Proof.
  apply Is_true_s_intro; pose proof (adj_scoped a) as H; rewrite <- aok_scoped in H.
  destruct (radj_n (adj_raw a)); exact H.
Qed.

(** The morphism of a scoped adjustment. *)
Definition apply {N M} (a : adj term N M) : morph N M :=
  gapply LAbs (radj_n (adj_raw a)) N M 0 M (Is_true_s_intro (Nat.eqb_refl M)) (adj_aok a).

(** Substitution [t [a]] is the Kleisli extension of [apply] at the top;
    it is notation, so rewriting sees the Kleisli extension. *)
Notation "t [ a ]" := (kleisli (apply a) ext_here t) (at level 1, left associativity, format "t [ a ]").
Notation subst a := (kleisli (apply a) ext_here) (only parsing).

End Subst.
