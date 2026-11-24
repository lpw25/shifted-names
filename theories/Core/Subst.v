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
  Lookup Adjustment Laws Scoped Indexed Syntax Normalise Conv Names.
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
  nwfc (fun r => r) x && (scoped_tail K M x && pscopedc M (fun r => r) x).

(** An adjustment with its root read through [rt] (a lazy base,
    Lookup.v). *)
Definition absn (rt : counts -> lbase) (x : nadj) : nadj :=
  match x with NAdj r es => NAdj (lcounts (rt r)) es end.

Lemma aok_wf K M x : aok K M x = true -> nwf x.
Proof. unfold aok; rewrite andb_true_iff; intros [H _]; exact H. Qed.

Lemma aok_local K M x : aok K M x = true -> nlocal x.
Proof. intros H; apply nwf_local, (aok_wf K M), H. Qed.

Lemma aok_scoped K M (a : radj T) : aok K M (radj_n a) = scoped K M a.
Proof. unfold aok, scoped; rewrite (radj_wf a); reflexivity. Qed.

(** Where a lookup ends up: an entry found over base [Be]. *)
Lemma found_entry R (es : atrie entry) k Be h ts len p :
  nlocal (NAdj R es) ->
  option_map (unshift R) (aget k es) = Some (unshift Be (Entry h ts len p)) ->
  label_key h = k /\ kgood ts /\ klength ts = len
  /\ (forall i Bt t, i < len -> option_map (unshift Be) (knth ts i) = Some (unshift Bt t) ->
                     napply (NAdj R es) (mk_rvar h i) = tresult (unshift Bt t))
  /\ (forall i, len <= i -> napply (NAdj R es) (mk_rvar h i)
                           = inl (mk_rvar h (dval Be (label_key h) + (i - len + p))))
  /\ (forall i, i < len -> knth ts i <> None).
Proof.
  intros Hl E; pose proof Hl as [_ [_ [Hent _]]].
  destruct (aget k es) as [e0|] eqn:E0; [|discriminate]; cbn in E; injection E as E.
  destruct e0 as [h0 ts0 len0 p0]; destruct (Hent _ _ E0) as [[Hk [G0 [Hl0 _]]] _].
  cbn [unshift entry_based eunshift] in E; injection E as -> Ets -> Ep.
  assert (G : kgood ts) by (apply (kgood_unlift Be); rewrite <- Ets; apply kgood_klift, G0).
  assert (Hlen : klength ts = len) by (rewrite <- Hl0, <- (klength_klift R ts0), Ets, klength_klift; reflexivity).
  subst k; split; [reflexivity|split; [exact G|split; [exact Hlen|split; [|split]]]].
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
  assert (Hy : nwf y) by exact (nwf_payload x v u y Hw E).
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

Lemma W_tHL {N M K L} (e : ext N M K L) : Is_true_s (Nat.eqb L (ext_depth e + M)).
Proof. apply Is_true_s_intro, Nat.eqb_eq, ext_depth_L. Qed.

Lemma W_HL {Kx L0 K L} Mx s (e : ext Kx L0 K L) (HL : Is_true_s (Nat.eqb L0 (s + Mx))) :
  Is_true_s (Nat.eqb L ((s + ext_depth e) + Mx)).
Proof.
  apply Is_true_s_intro; apply Is_true_s_elim, Nat.eqb_eq in HL; apply Nat.eqb_eq.
  pose proof (ext_depth_L e); lia.
Qed.

Lemma aok_squash K M (X : nadj) (Hx : Is_true_s (aok K M X)) : Squash (nlocal X).
Proof. apply Is_true_s_elim in Hx; exact (squash (aok_local _ _ _ Hx)). Qed.

Lemma found_at R (es : atrie entry) v' Be h ts len p :
  nlocal (NAdj R es) ->
  option_map (unshift R) (aget (label_key (v_label v')) es) = Some (unshift (lcounts Be) (Entry h ts len p)) ->
  h = v_label v'.
Proof.
  intros Hl H1; destruct (found_entry _ _ _ _ _ _ _ _ Hl H1) as [Hk _]; apply label_key_inj, Hk.
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
  destruct (found_entry _ _ _ _ _ _ _ _ Hl H1) as [_ [_ [_ [Ht _]]]].
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
  destruct (found_entry _ _ _ _ _ _ _ _ Hl H1) as [_ [_ [_ [Ht _]]]].
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
  destruct (found_entry _ _ _ _ _ _ _ _ Hl H1) as [_ [_ [_ [_ [Hp _]]]]].
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
Lemma W_absurd R (es : atrie entry) k i Be h ts len p
  (Hl : Squash (nlocal (NAdj R es)))
  (H1 : Squash (option_map (unshift R) (aget k es) = Some (unshift (lcounts Be) (Entry h ts len p))))
  (Hi : i < len) (H2 : Squash (knth ts i = None)) : sEmpty.
Proof.
  destruct Hl as [Hl], H1 as [H1], H2 as [H2].
  destruct (found_entry _ _ _ _ _ _ _ _ Hl H1) as [_ [_ [_ [_ [_ Hn]]]]].
  exfalso; exact (Hn i Hi H2).
Qed.

End Wrappers.

(** ** Substitution for a syntax *)

(** The substitution of any syntax ([Syntax]): its definitions and laws
    take the syntax's instance as an implicit argument. *)
Section Subst0.
Context {term : nat -> Type} `{Sx : Syntax term}.
Local Notation morph := (morph term).
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
                       (fun H2 => match W_absurd (lcounts (rt r)) es _ (v_index v') Be h ts len p (aok_squash Kx Mx _ Hx) H1 Hi H2
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

End Subst0.

(** Substitution [t [a]] is the Kleisli extension of [apply] at the top;
    it is notation, so rewriting sees the Kleisli extension. *)
Notation "t [ a ]" := (kleisli (apply a) ext_here t) (at level 1, left associativity, format "t [ a ]").
Notation subst a := (kleisli (apply a) ext_here) (only parsing).

Section Subst1.
Context {term : nat -> Type} `{Sx : Syntax term}.
Local Notation morph := (morph term).
Local Notation P := {K & term K}.
Local Notation nadj := (@nadj P).
Local Notation entry := (@entry P).
Local Notation target := (@target P).

(** ** What [gapply] computes *)

Section Char.

Lemma option_cases {X} (o : option X) : (exists x, o = Some x) \/ o = None.
Proof. destruct o; eauto. Qed.

(** An input outside the binders crossed so far. *)
Definition outer (d : nat) (rv : rvar) : Prop := v_label rv = None -> d <= v_index rv.

(** What [gapply] computes on such an input, for any lazy base: a payload
    result is looked up over the base the lookup reached. *)
Lemma gapply_result rt x Kx Mx s L0 HL Hx {K L} (e : ext Kx L0 K L) v :
  outer (ext_depth e) (var_raw v) ->
  match napply (absn rt x) (down (ext_depth e) (var_raw v)) with
  | inl w => forall H, gapply rt x Kx Mx s L0 HL Hx K L e v = tvar (mk_var (up (s + ext_depth e) w) H)
  | inr (u, ρ) => exists Bt ρ0, ρ = absn (LAdd Bt) ρ0
                  /\ forall HL' Hρ0, gapply rt x Kx Mx s L0 HL Hx K L e v
                                     = kleisli (gapply (LAdd Bt) ρ0 (projT1 u) Mx (s + ext_depth e) L HL' Hρ0)
                                               ext_here (projT2 u)
  end.
Proof.
  pose proof (aok_local _ _ _ (Is_true_s_elim Hx)) as Hl.
  intros Hout.
  assert (Hlook : forall (Hv' : wf_var Kx (down (ext_depth e) (var_raw v)) = true),
    gapply rt x Kx Mx s L0 HL Hx K L e v =
    (match x as x0 return Is_true_s (aok Kx Mx (absn rt x0)) -> term L with
     | NAdj r es => fun Hx =>
        aget_with (label_key (v_label (down (ext_depth e) (var_raw v)))) es (rt r)
          (fun Be ent =>
             match ent as ent0
                   return Squash (option_map (unshift (lcounts (rt r))) (aget (label_key (v_label (down (ext_depth e) (var_raw v)))) es) = Some (unshift (lcounts Be) ent0)) -> term L with
             | Entry h ts len p => fun H1 =>
                 match lt_dec (v_index (down (ext_depth e) (var_raw v))) len with
                 | Specif.left Hi =>
                     knth_with (v_index (down (ext_depth e) (var_raw v))) ts Be
                       (fun Bt t =>
                          match t as t0
                                return Squash (option_map (unshift (lcounts Be)) (knth ts (v_index (down (ext_depth e) (var_raw v)))) = Some (unshift (lcounts Bt) t0)) -> term L with
                          | TVar y' j => fun H2 =>
                              tvar (mk_var (up (s + ext_depth e) (mk_rvar y' (ldval Bt (label_key y') + j)))
                                      (W_var Kx Mx s L0 e (lcounts (rt r)) es _ Hv' Be h ts len p Bt y' j HL Hx H1 Hi H2))
                          | TBind u rho => fun H2 =>
                              kleisli (gapply (LAdd Bt) rho (projT1 u) Mx (s + ext_depth e) L (W_HL Mx s e HL)
                                         (W_pay Kx Mx (lcounts (rt r)) es _ Hv' Be h ts len p Bt u rho Hx H1 Hi H2))
                                      ext_here (projT2 u)
                          end)
                       (fun H2 => match W_absurd (lcounts (rt r)) es _ _ Be h ts len p (aok_squash Kx Mx _ Hx) H1 Hi H2
                                  with end)
                 | Specif.right Hi =>
                     tvar (mk_var (up (s + ext_depth e) (mk_rvar h (ldval Be (label_key h) + (v_index (down (ext_depth e) (var_raw v)) - len + p))))
                             (W_pass Kx Mx s L0 e (lcounts (rt r)) es _ Hv' Be h ts len p HL Hx H1 Hi))
                 end
             end)
          (fun H1 =>
             tvar (mk_var (up (s + ext_depth e) (mk_rvar (v_label (down (ext_depth e) (var_raw v)))
                                                    (ldval (rt r) (label_key (v_label (down (ext_depth e) (var_raw v)))) + v_index (down (ext_depth e) (var_raw v)))))
                     (W_none Kx Mx s L0 e (rt r) es _ Hv' HL Hx H1)))
     end Hx)).
  { intros Hv'; destruct v as [[[y|] i] Hv]; cbn [var_raw v_label v_index] in *.
    - destruct x as [r es]; reflexivity.
    - unfold outer in Hout; cbn [v_label v_index] in Hout; specialize (Hout eq_refl).
      destruct x as [r es]; cbv beta iota zeta delta [gapply var_raw v_label v_index].
      destruct (lt_dec i (ext_depth e)) as [Hb|Hb]; [lia|]; reflexivity. }
  assert (Hv' : wf_var Kx (down (ext_depth e) (var_raw v)) = true)
    by (apply (W_down e (var_raw v) (var_ok v)), Hout).
  rewrite (Hlook Hv'); clear Hlook.
  set (v' := down (ext_depth e) (var_raw v)) in *; clearbody v'.
  destruct x as [r es]; cbn [absn] in *.
  set (R := lcounts (rt r)) in *.
  destruct (option_cases (aget (label_key (v_label v')) es)) as [[e0 E1]|E1].
  - destruct (napply (NAdj R es) v') as [w|[u ρ]] eqn:En.
    + intros H; apply (aget_with_some _ _ _ _ _ (unshift R e0)); [|rewrite E1; reflexivity].
      intros Be [h ts len p] H1 Hy'.
      assert (Loc : option_map (unshift R) (aget (label_key (v_label v')) es) = Some (unshift (lcounts Be) (Entry h ts len p)))
        by (rewrite E1, Hy'; reflexivity).
      destruct (found_entry _ _ _ _ _ _ _ _ Hl Loc) as [Hk [G [Hlen [Ht [Hp Hnn]]]]].
      apply label_key_inj in Hk; subst h; rewrite (rvar_eta v') in En.
      destruct (lt_dec (v_index v') len) as [Hi|Hi].
      * destruct (option_cases (knth ts (v_index v'))) as [[t Et]|Et]; [|exfalso; exact (Hnn _ Hi Et)].
        apply (knth_with_some _ _ _ _ _ (unshift (lcounts Be) t)); [|rewrite Et; reflexivity].
        intros Bt t' H2 Ht'.
        pose proof (Ht _ (lcounts Bt) t' Hi ltac:(rewrite Et, Ht'; reflexivity)) as Er; rewrite En in Er.
        destruct t' as [y' j|u' [r0 es0]]; cbn in Er; [|discriminate Er].
        injection Er as Ew; subst w; cbn beta iota; f_equal; apply var_eq; cbn [var_raw]; rewrite ldval_spec; reflexivity.
      * rewrite (Hp (v_index v') ltac:(lia)) in En; injection En as <-; f_equal; apply var_eq; cbn [var_raw]; rewrite ldval_spec; reflexivity.
    + set (Pz := fun z => exists Bt ρ0, ρ = absn (LAdd Bt) ρ0
                   /\ forall HL' Hρ0, z = kleisli (gapply (LAdd Bt) ρ0 (projT1 u) Mx (s + ext_depth e) L HL' Hρ0) ext_here (projT2 u)).
      apply (aget_with_prop _ _ _ _ _ (unshift R e0) Pz); [|rewrite E1; reflexivity].
      intros Be [h ts len p] H1 Hy'.
      assert (Loc : option_map (unshift R) (aget (label_key (v_label v')) es) = Some (unshift (lcounts Be) (Entry h ts len p)))
        by (rewrite E1, Hy'; reflexivity).
      destruct (found_entry _ _ _ _ _ _ _ _ Hl Loc) as [Hk [G [Hlen [Ht [Hp Hnn]]]]].
      apply label_key_inj in Hk; subst h; rewrite (rvar_eta v') in En.
      destruct (lt_dec (v_index v') len) as [Hi|Hi].
      * destruct (option_cases (knth ts (v_index v'))) as [[t Et]|Et]; [|exfalso; exact (Hnn _ Hi Et)].
        apply (knth_with_prop _ _ _ _ _ (unshift (lcounts Be) t) Pz); [|rewrite Et; reflexivity].
        intros Bt t' H2 Ht'.
        pose proof (Ht _ (lcounts Bt) t' Hi ltac:(rewrite Et, Ht'; reflexivity)) as Er; rewrite En in Er.
        destruct t' as [y' j|u' [r0 es0]]; cbn in Er; [discriminate|].
        injection Er as Eu Eρ; subst u ρ.
        exists Bt, (NAdj r0 es0); split; [reflexivity|intros HL' Hρ0; reflexivity].
      * rewrite (Hp (v_index v') ltac:(lia)) in En; discriminate.
  - assert (En : napply (NAdj R es) v' = inl (mk_rvar (v_label v') (dval R (label_key (v_label v')) + v_index v')))
      by (destruct v'; apply found_none, E1).
    rewrite (aget_with_none _ _ _ _ _ E1), En.
    intros H; f_equal; apply var_eq; cbn [var_raw]; rewrite ldval_spec; reflexivity.
Qed.

(** Inside the binders crossed so far, a variable stays. *)
Lemma gapply_inner rt x Kx Mx s L0 HL Hx {K L} (e : ext Kx L0 K L) v H :
  v_label (var_raw v) = None -> v_index (var_raw v) < ext_depth e ->
  gapply rt x Kx Mx s L0 HL Hx K L e v = tvar (mk_var (var_raw v) H).
Proof.
  destruct v as [[[y|] i] Hv]; cbn [var_raw v_label v_index]; intros Hl Hi; [discriminate|].
  destruct x as [r es]; cbv beta iota zeta delta [gapply var_raw v_label v_index].
  destruct (lt_dec i (ext_depth e)) as [Hb|Hb]; [reflexivity|contradiction].
Qed.

(** With the root read directly. *)
Definition gapply0 (x : nadj) (Kx Mx s L0 : nat) (HL : Is_true_s (Nat.eqb L0 (s + Mx)))
  (Hx : Is_true_s (aok Kx Mx x)) : morph Kx L0 :=
  gapply LAbs x Kx Mx s L0 HL (match x as x0 return Is_true_s (aok Kx Mx x0) -> Is_true_s (aok Kx Mx (absn LAbs x0)) with
                                 | NAdj r es => fun H => H end Hx).

Lemma apply_gapply0 {N M} (a : adj term N M) HL Hx : apply a = gapply0 (radj_n (adj_raw a)) N M 0 M HL Hx.
Proof. unfold apply, gapply0; reflexivity. Qed.

Lemma nnest_absn rt (x : nadj) : nnest (absn rt x) = nnest x.
Proof. destruct x; cbn [absn]; rewrite !nnest_es; reflexivity. Qed.

Lemma napply_depth_aok K M (x : nadj) v u (y : nadj) : aok K M x = true -> napply x v = inr (u, y) -> nnest y < nnest x.
Proof.
  intros Hx E; apply (nest_napply x v u y); [|exact E].
  intros k e Ek; pose proof (aok_local _ _ _ Hx) as Hl; destruct x as [r es]; destruct Hl as [_ [_ [Hent _]]]; cbn [nentries] in Ek.
  destruct (Hent k e Ek) as [Hok _]; destruct e; apply Hok.
Qed.

Lemma pay_var_wf (x : nadj) Kx Mx s L0 {K L} (e : ext Kx L0 K L) v' w :
  aok Kx Mx x = true -> L0 = s + Mx -> wf_var Kx v' = true -> napply x v' = inl w ->
  wf_var L (up (s + ext_depth e) w) = true.
Proof.
  intros Hx HL Hv Hw; pose proof (res_wf Kx Mx x v' Hx Hv) as H; rewrite Hw in H.
  pose proof (ext_depth_L e) as HL'.
  apply (wf_eq L ((s + ext_depth e) + Mx)); [lia|apply up_wf, H].
Qed.

Lemma pay_payload_ok (x : nadj) Kx Mx v' u ρ :
  aok Kx Mx x = true -> wf_var Kx v' = true -> napply x v' = inr (u, ρ) -> aok (projT1 u) Mx ρ = true.
Proof. intros Hx Hv Hw; pose proof (res_wf Kx Mx x v' Hx Hv) as H; rewrite Hw in H; exact H. Qed.

Lemma outer_down_wf {Kx L0 K L} (e : ext Kx L0 K L) (v : var K) :
  outer (ext_depth e) (var_raw v) -> wf_var Kx (down (ext_depth e) (var_raw v)) = true.
Proof. intros H; apply (W_down e (var_raw v) (var_ok v)), H. Qed.

(** The lazy base only matters through what it denotes. *)
Lemma gapply_abs n : forall rt x Kx Mx s L0 HL Hx, nnest x < n ->
  forall K L (e : ext Kx L0 K L) v,
  gapply rt x Kx Mx s L0 HL Hx K L e v = gapply0 (absn rt x) Kx Mx s L0 HL Hx K L e v.
Proof.
  induction n as [|n IH]; intros rt x Kx Mx s L0 HL Hx Hn K L e v; [lia|].
  destruct (option_cases (v_label (var_raw v))) as [[y Hy]|Hv]
    ; [|destruct (lt_dec (v_index (var_raw v)) (ext_depth e)) as [Hb|Hb]].
  2: { rewrite (gapply_inner _ _ _ _ _ _ _ _ e v (W_inner e _ Hv Hb) Hv Hb); unfold gapply0;
         rewrite (gapply_inner _ _ _ _ _ _ _ _ e v (W_inner e _ Hv Hb) Hv Hb); reflexivity. }
  all: assert (Hout : outer (ext_depth e) (var_raw v)) by (unfold outer; intros H; first [congruence|lia]).
  all: destruct x as [r es]; unfold gapply0; cbn [absn lcounts] in *.
  all: pose proof (gapply_result rt (NAdj r es) Kx Mx s L0 HL Hx e v Hout) as A.
  all: pose proof (gapply_result LAbs (absn rt (NAdj r es)) Kx Mx s L0 HL Hx e v Hout) as B.
  all: cbn [absn lcounts] in A, B.
  all: pose proof (Is_true_s_elim Hx) as Hx0; cbn [absn] in Hx0.
  all: pose proof (outer_down_wf e v Hout) as Hv'.
  all: destruct (napply (NAdj (lcounts (rt r)) es) (down (ext_depth e) (var_raw v))) as [w|[u ρ]] eqn:En;
       [ assert (H : Is_true_s (wf_var L (up (s + ext_depth e) w)))
           by (apply Is_true_s_intro, (pay_var_wf _ Kx Mx s L0 e (down (ext_depth e) (var_raw v)) w Hx0); [apply Nat.eqb_eq, Is_true_s_elim, HL|exact Hv'|exact En]);
         rewrite (A H), (B H); reflexivity
       | ].
  all: destruct A as [Bt [ρ0 [E0 A]]], B as [Bt' [ρ1 [E1 B]]].
  all: assert (Hρ : aok (projT1 u) Mx ρ = true) by apply (pay_payload_ok _ Kx Mx (down (ext_depth e) (var_raw v)) u ρ Hx0 Hv' En).
  all: assert (Hd : nnest ρ < nnest (NAdj (lcounts (rt r)) es)) by apply (napply_depth_aok _ _ _ (down (ext_depth e) (var_raw v)) _ _ Hx0 En).
  all: assert (HL' : Is_true_s (Nat.eqb L ((s + ext_depth e) + Mx))) by apply (W_HL Mx s e HL).
  all: assert (H0 : Is_true_s (aok (projT1 u) Mx (absn (LAdd Bt) ρ0))) by (rewrite <- E0; apply Is_true_s_intro, Hρ).
  all: assert (H1 : Is_true_s (aok (projT1 u) Mx (absn (LAdd Bt') ρ1))) by (rewrite <- E1; apply Is_true_s_intro, Hρ).
  all: rewrite (A HL' H0), (B HL' H1); apply kleisli_ext; intros K' L' e' v'.
  all: rewrite (IH (LAdd Bt) ρ0), (IH (LAdd Bt') ρ1);
         [revert H0 H1; rewrite <- E0, <- E1; reflexivity
         |rewrite E1, nnest_absn, nnest_es in Hd; rewrite nnest_es in Hn; lia
         |rewrite E0, nnest_absn, nnest_es in Hd; rewrite nnest_es in Hn; lia].
Qed.

(** What [gapply0] computes on an input outside the binders crossed. *)
Lemma gapply0_result x Kx Mx s L0 HL Hx {K L} (e : ext Kx L0 K L) v :
  outer (ext_depth e) (var_raw v) ->
  match napply x (down (ext_depth e) (var_raw v)) with
  | inl w => forall H, gapply0 x Kx Mx s L0 HL Hx K L e v = tvar (mk_var (up (s + ext_depth e) w) H)
  | inr (u, ρ) => forall HL' Hρ, gapply0 x Kx Mx s L0 HL Hx K L e v
                                 = kleisli (gapply0 ρ (projT1 u) Mx (s + ext_depth e) L HL' Hρ) ext_here (projT2 u)
  end.
Proof.
  intros Hv; destruct x as [r es]; pose proof (gapply_result LAbs (NAdj r es) Kx Mx s L0 HL Hx e v Hv) as A.
  unfold gapply0; cbn [absn lcounts] in A |- *.
  destruct (napply (NAdj r es) _) as [w|[u ρ]]; [exact A|].
  destruct A as [Bt [ρ0 [-> A]]]; intros HL' Hρ; rewrite (A HL' Hρ).
  apply kleisli_ext; intros K' L' e' v'.
  rewrite (gapply_abs (S (nnest ρ0)) (LAdd Bt) ρ0) by lia; reflexivity.
Qed.

Lemma gapply0_inner x Kx Mx s L0 HL Hx {K L} (e : ext Kx L0 K L) v H :
  v_label (var_raw v) = None -> v_index (var_raw v) < ext_depth e ->
  gapply0 x Kx Mx s L0 HL Hx K L e v = tvar (mk_var (var_raw v) H).
Proof. unfold gapply0; apply gapply_inner. Qed.

Lemma gapply0_var x Kx Mx s L0 HL Hx {K L} (e : ext Kx L0 K L) v w H :
  outer (ext_depth e) (var_raw v) -> napply x (down (ext_depth e) (var_raw v)) = inl w ->
  gapply0 x Kx Mx s L0 HL Hx K L e v = tvar (mk_var (up (s + ext_depth e) w) H).
Proof. intros Hv E; pose proof (gapply0_result x Kx Mx s L0 HL Hx e v Hv) as R; rewrite E in R; apply R. Qed.

Lemma gapply0_pay x Kx Mx s L0 HL Hx {K L} (e : ext Kx L0 K L) v u ρ HL' Hρ :
  outer (ext_depth e) (var_raw v) -> napply x (down (ext_depth e) (var_raw v)) = inr (u, ρ) ->
  gapply0 x Kx Mx s L0 HL Hx K L e v = kleisli (gapply0 ρ (projT1 u) Mx (s + ext_depth e) L HL' Hρ) ext_here (projT2 u).
Proof. intros Hv E; pose proof (gapply0_result x Kx Mx s L0 HL Hx e v Hv) as R; rewrite E in R; apply R. Qed.

(** The SProp arguments are irrelevant; the scope arguments only through
    their value. *)
Lemma gapply0_s_eq x Kx Mx L0 s s' (E : s = s') HL HL' Hx :
  gapply0 x Kx Mx s L0 HL Hx = gapply0 x Kx Mx s' L0 HL' Hx.
Proof. subst; reflexivity. Qed.

End Char.

(** ** Raw facts *)

Section Raw.

Lemma napply_rlift (a : radj P) h v :
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

Lemma napply_rcompose (a b : radj P) v :
  napply (radj_n (rcompose a b)) v
  = match napply (radj_n b) v with
    | inl w => napply (radj_n a) w
    | inr (u, x) => inr (u, Compose.compose (radj_n a) x)
    end.
Proof. cbn [radj_n rcompose]; rewrite (proj2 (compose_spec _ _ (radj_wf a) (radj_wf b))); reflexivity. Qed.

Lemma napply_nweaken h (x : nadj) v :
  nwf x -> napply (Point.weaken h x) v
  = match napply x v with
    | inl w => inl (shift_rvar (mk_rvar h 0) w)
    | inr (u, y) => inr (u, Point.weaken h y)
    end.
Proof.
  intros Hx; rewrite napply_weaken by apply (nwf_local _ Hx).
  destruct (napply x v) as [w|[u [r es]]]; cbn [rweaken]; [rewrite rweaken_var|]; reflexivity.
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

Lemma up_down d rv : outer d rv -> up d (down d rv) = rv.
Proof.
  destruct rv as [[y|] i]; unfold up, down, outer; cbn; [reflexivity|].
  intros H; specialize (H eq_refl); f_equal; lia.
Qed.

End Raw.

(** ** At the top *)

Section Top.

Lemma top_HL {M} : Is_true_s (Nat.eqb M (0 + M)).
Proof. exact (Is_true_s_intro (Nat.eqb_refl M)). Qed.

Lemma top_aok {N M} (a : adj term N M) : Is_true_s (aok N M (radj_n (adj_raw a))).
Proof. apply Is_true_s_intro; rewrite aok_scoped; apply adj_scoped. Qed.

Lemma apply_inner {N M K L} (a : adj term N M) (e : ext N M K L) v H :
  v_label (var_raw v) = None -> v_index (var_raw v) < ext_depth e -> apply a K L e v = tvar (mk_var (var_raw v) H).
Proof. rewrite (apply_gapply0 a top_HL (top_aok a)); apply gapply0_inner. Qed.

Lemma apply_var {N M K L} (a : adj term N M) (e : ext N M K L) v w H :
  outer (ext_depth e) (var_raw v) -> napply (radj_n (adj_raw a)) (down (ext_depth e) (var_raw v)) = inl w ->
  apply a K L e v = tvar (mk_var (up (ext_depth e) w) H).
Proof. rewrite (apply_gapply0 a top_HL (top_aok a)); apply gapply0_var. Qed.

Lemma apply_pay {N M K L} (a : adj term N M) (e : ext N M K L) v u ρ HL' Hρ :
  outer (ext_depth e) (var_raw v) -> napply (radj_n (adj_raw a)) (down (ext_depth e) (var_raw v)) = inr (u, ρ) ->
  apply a K L e v = kleisli (gapply0 ρ (projT1 u) M (ext_depth e) L HL' Hρ) ext_here (projT2 u).
Proof. rewrite (apply_gapply0 a top_HL (top_aok a)); apply gapply0_pay. Qed.

Lemma top_var_wf {N M K L} (a : adj term N M) (e : ext N M K L) v' w :
  wf_var N v' = true -> napply (radj_n (adj_raw a)) v' = inl w -> wf_var L (up (ext_depth e) w) = true.
Proof.
  intros Hv Hw; apply (pay_var_wf (radj_n (adj_raw a)) N M 0 M e v' w); [apply Is_true_s_elim, top_aok|reflexivity|exact Hv|exact Hw].
Qed.

Lemma top_payload_ok {N M} (a : adj term N M) v' u ρ :
  wf_var N v' = true -> napply (radj_n (adj_raw a)) v' = inr (u, ρ) -> aok (projT1 u) M ρ = true.
Proof. intros Hv Hw; apply (pay_payload_ok (radj_n (adj_raw a)) N M v'); [apply Is_true_s_elim, top_aok|exact Hv|exact Hw]. Qed.

End Top.

(** ** Going under a binder is lifting *)

Section Lift.

Ltac sq := apply Is_true_s_intro.

(** Weakening an adjustment's output past one more bound variable is using
    it under one more outer binder. *)
Lemma gapply0_weaken n :
  forall ρ, nnest ρ < n -> forall Kx Mx d L HL HL' Hx Hx' K L' (e : ext Kx L K L') v,
  gapply0 ρ Kx Mx (S d) L HL Hx K L' e v = gapply0 (Point.weaken None ρ) Kx (S Mx) d L HL' Hx' K L' e v.
Proof.
  induction n as [|n IH]; intros ρ Hd Kx Mx d L HL HL' Hx Hx' K L' e v; [lia|].
  pose proof (Is_true_s_elim Hx) as Hx0; pose proof (Is_true_s_elim Hx') as Hx0'.
  assert (Hn : nwf ρ) by apply (aok_wf _ _ ρ Hx0).
  destruct (option_cases (v_label (var_raw v))) as [[y Hy]|Hl]
    ; [|destruct (lt_dec (v_index (var_raw v)) (ext_depth e)) as [Hb|Hb]].
  2: { pose proof (W_inner e (var_raw v) Hl Hb) as H.
       rewrite (gapply0_inner _ _ _ _ _ _ _ e v H Hl Hb), (gapply0_inner _ _ _ _ _ _ _ e v H Hl Hb); reflexivity. }
  all: assert (Hout : outer (ext_depth e) (var_raw v)) by (unfold outer; intros H; first [congruence|lia]).
  all: pose proof (outer_down_wf e v Hout) as Hv'.
  all: pose proof (napply_nweaken None ρ (down (ext_depth e) (var_raw v)) Hn) as Hs.
  all: destruct (napply ρ (down (ext_depth e) (var_raw v))) as [w|[u ρ2]] eqn:E;
    [ assert (H1 : Is_true_s (wf_var L' (up (S d + ext_depth e) w)))
        by (sq; apply (pay_var_wf ρ Kx Mx (S d) L e (down (ext_depth e) (var_raw v)) w Hx0); [apply Nat.eqb_eq, Is_true_s_elim, HL|exact Hv'|exact E]);
      assert (H2 : Is_true_s (wf_var L' (up (d + ext_depth e) (shift_rvar (mk_rvar None 0) w))))
        by (rewrite up_shift; exact H1);
      rewrite (gapply0_var _ _ _ _ _ _ _ e v w H1 Hout E), (gapply0_var _ _ _ _ _ _ _ e v (shift_rvar (mk_rvar None 0) w) H2 Hout Hs);
      f_equal; apply var_eq; cbn; rewrite up_shift; reflexivity
    | ].
  all: pose proof (napply_depth_aok _ _ _ (down (ext_depth e) (var_raw v)) _ _ Hx0 E) as Hdep.
  all: assert (Hρ2 : Is_true_s (aok (projT1 u) Mx ρ2)) by (sq; apply (pay_payload_ok ρ Kx Mx (down (ext_depth e) (var_raw v)) u ρ2 Hx0 Hv' E)).
  all: assert (Hρ2' : Is_true_s (aok (projT1 u) (S Mx) (Point.weaken None ρ2)))
         by (sq; apply (pay_payload_ok (Point.weaken None ρ) Kx (S Mx) (down (ext_depth e) (var_raw v)) u _ Hx0' Hv' Hs)).
  all: assert (HL1 : Is_true_s (Nat.eqb L' ((S d + ext_depth e) + Mx))) by (apply (W_HL Mx (S d) e HL)).
  all: assert (HL2 : Is_true_s (Nat.eqb L' ((d + ext_depth e) + S Mx))) by (apply (W_HL (S Mx) d e HL')).
  all: rewrite (gapply0_pay _ _ _ _ _ _ _ e v u ρ2 HL1 Hρ2 Hout E).
  all: rewrite (gapply0_pay _ _ _ _ _ _ _ e v u (Point.weaken None ρ2) HL2 Hρ2' Hout Hs).
  all: apply kleisli_ext; intros K2 L2 e2 v2.
  all: assert (HL3 : Is_true_s (Nat.eqb L' (S (d + ext_depth e) + Mx))) by (sq; apply Nat.eqb_eq; apply Is_true_s_elim, Nat.eqb_eq in HL1; lia).
  all: rewrite (gapply0_s_eq ρ2 _ Mx L' (S d + ext_depth e) (S (d + ext_depth e)) eq_refl HL1 HL3).
  all: apply IH; lia.
Qed.

Lemma apply_lift_rebase {N M K L} (a : adj term N M) (e : ext (S N) (S M) K L) v :
  apply a K L (ext_app (ext_under ext_here) e) v = apply (lift a) K L e v.
Proof.
  set (d := ext_depth e).
  assert (Hd : ext_depth (ext_app (ext_under ext_here) e) = S d)
    by (rewrite ext_depth_app; cbn; unfold d; lia).
  set (e1 := ext_app (ext_under ext_here) e) in *.
  destruct (option_cases (v_label (var_raw v))) as [[y El]|El];
    [|destruct (lt_dec (v_index (var_raw v)) (S d)) as [Hi|Hi]].
  2: { pose proof (W_inner e1 (var_raw v) El ltac:(lia)) as H.
       rewrite (apply_inner a e1 v H El) by lia.
       destruct (lt_dec (v_index (var_raw v)) d) as [Hi'|Hi'].
       - rewrite (apply_inner (lift a) e v H El Hi'); reflexivity.
       - assert (Hii : v_index (var_raw v) = d) by lia.
         assert (Hn : napply (radj_n (adj_raw (lift a))) (down d (var_raw v)) = inl (mk_rvar None 0)).
         { rewrite adj_raw_lift, napply_rlift.
           destruct (var_raw v) as [h j]; cbn in El, Hii |- *; subst h j.
           unfold down; cbn [v_label v_index]; rewrite Nat.sub_diag; reflexivity. }
         assert (H' : Is_true_s (wf_var L (up d (mk_rvar None 0)))).
         { replace (up d (mk_rvar None 0)) with (var_raw v); [exact H|].
           destruct (var_raw v) as [h j]; cbn in El, Hii; subst h j; unfold up; cbn; f_equal; lia. }
         rewrite (apply_var (lift a) e v (mk_rvar None 0) H' (fun _ => ltac:(lia)) Hn).
         f_equal; apply var_eq; cbn.
         destruct (var_raw v) as [h j]; cbn in El, Hii; subst h j; unfold up; cbn; f_equal; lia. }
  all: assert (Hr1 : outer (ext_depth e1) (var_raw v)) by (unfold outer; intros; rewrite Hd; first [lia|congruence]).
  all: assert (Hr2 : outer (ext_depth e) (var_raw v)) by (unfold outer, d in *; intros; first [lia|congruence]).
  all: assert (Hdn : napply (radj_n (adj_raw (lift a))) (down (ext_depth e) (var_raw v))
                  = match napply (radj_n (adj_raw a)) (down (ext_depth e1) (var_raw v)) with
                    | inl w => inl (shift_rvar (mk_rvar None 0) w)
                    | inr (u, x) => inr (u, Point.weaken None x)
                    end).
  all: try (rewrite adj_raw_lift, napply_rlift, Hd; fold d;
            destruct (var_raw v) as [h j]; cbn in El |- *; subst h;
            first [reflexivity|
              (unfold down; cbn [v_label v_index];
               replace (rvar_eqb (mk_rvar None (j - d)) (mk_rvar None 0)) with false
                 by (symmetry; apply Bool.not_true_iff_false; intros Heq;
                     apply (proj2 (reflect_iff _ _ (rvar_eqb_spec _ _))) in Heq; injection Heq; cbn in Hi; lia);
               unfold unshift_rvar; cbn;
               replace (j - d) with (S (j - S d)) by (cbn in Hi; lia);
               cbn; rewrite Nat.sub_0_r; reflexivity)]).
  all: destruct (napply (radj_n (adj_raw a)) (down (ext_depth e1) (var_raw v))) as [w|[u ρ]] eqn:E.
  all: try (assert (H1 : Is_true_s (wf_var L (up (ext_depth e1) w)))
              by (apply Is_true_s_intro, (top_var_wf a e1 (down (ext_depth e1) (var_raw v)) w);
                  [apply (outer_down_wf e1 v Hr1)|exact E]);
            assert (H2 : Is_true_s (wf_var L (up (ext_depth e) (shift_rvar (mk_rvar None 0) w))))
              by (rewrite up_shift; fold d; rewrite <- Hd; exact H1);
            rewrite (apply_var a e1 v w H1 Hr1 E), (apply_var (lift a) e v _ H2 Hr2 Hdn);
            f_equal; apply var_eq; cbn; rewrite up_shift, Hd; reflexivity).
  all: pose proof (top_payload_ok a _ u ρ (outer_down_wf e1 v Hr1) E) as Hρ.
  all: assert (Hρ' : aok (projT1 u) (S M) (Point.weaken None ρ) = true)
         by (apply (top_payload_ok (lift a) (down (ext_depth e) (var_raw v)) u);
             [apply (outer_down_wf e v Hr2)|exact Hdn]).
  all: rewrite (apply_pay a e1 v u ρ (W_tHL e1) (Is_true_s_intro Hρ) Hr1 E).
  all: rewrite (apply_pay (lift a) e v u (Point.weaken None ρ) (W_tHL e) (Is_true_s_intro Hρ') Hr2 Hdn).
  all: apply kleisli_ext; intros K2 L2 e2 v2.
  all: assert (HL'' : Is_true_s (Nat.eqb L (S d + M)))
         by (apply Is_true_s_intro, Nat.eqb_eq; pose proof (ext_depth_L e); unfold d; lia).
  all: rewrite (gapply0_s_eq ρ _ M L _ (S d) Hd (W_tHL e1) HL'').
  all: apply (gapply0_weaken (S (nnest ρ))); lia.
Qed.

End Lift.

(** ** The rewrite view: offsets reduce to lifts *)

Theorem kleisli_apply_under {N M K L} (a : adj term N M) (e : ext N M K L) (t : term (S K)) :
  kleisli (apply a) (ext_under e) t = kleisli (apply (lift a)) (ext_shift e) t.
Proof.
  rewrite <- (ext_app_shift e), kleisli_rebase.
  apply kleisli_ext; intros K' L' e' v; apply apply_lift_rebase.
Qed.

(** ** Identity *)

Lemma apply_identity {N K L} (e : ext N N K L) v : apply identity K L e v = unit_m K L e v.
Proof.
  unfold unit_m.
  destruct (option_cases (v_label (var_raw v))) as [[y El]|El];
    [|destruct (lt_dec (v_index (var_raw v)) (ext_depth e)) as [Hi|Hi]].
  2: { rewrite (apply_inner identity e v (W_inner e _ El Hi) El Hi).
       f_equal; apply var_eq; reflexivity. }
  all: assert (Hr : outer (ext_depth e) (var_raw v)) by (unfold outer; intros; first [lia|congruence]).
  all: assert (Hn : napply (radj_n (adj_raw (@identity term N))) (down (ext_depth e) (var_raw v))
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

Lemma napply_ncompose (a : radj P) (x : nadj) v :
  nwf x ->
  napply (Compose.compose (radj_n a) x) v
  = match napply x v with
    | inl w => napply (radj_n a) w
    | inr (u, y) => inr (u, Compose.compose (radj_n a) y)
    end.
Proof. intros Hx; rewrite (proj2 (compose_spec _ _ (radj_wf a) Hx)); reflexivity. Qed.

(** Substituting with [a] after applying an adjustment [ρ] to a payload
    term is applying [a ∘ ρ]. *)
Lemma gapply0_compose n :
  forall ρ, nnest ρ < n ->
  forall Kx M P' Mid L (a : adj term M P') (e' : ext M P' Mid L) HL1 Hx1 HL2 Hx2 (u : term Kx),
  kleisli (apply a) e' (kleisli (gapply0 ρ Kx M (ext_depth e') Mid HL1 Hx1) ext_here u)
  = kleisli (gapply0 (Compose.compose (radj_n (adj_raw a)) ρ) Kx P' (ext_depth e') L HL2 Hx2) ext_here u.
Proof.
  induction n as [|n IH]; intros ρ Hdep Kx M P' Mid L a e' HL1 Hx1 HL2 Hx2 u; [lia|].
  set (d := ext_depth e') in *.
  set (ρ'' := Compose.compose (radj_n (adj_raw a)) ρ) in *.
  rewrite kleisli_rebase_here, kleisli_comp_here.
  apply kleisli_ext; intros K2 L2 e2 w.
  unfold comp_m; rewrite <- kleisli_rebase.
  pose proof (Is_true_s_elim Hx1) as Hx1b; pose proof (Is_true_s_elim Hx2) as Hx2b.
  pose proof (ext_depth_left Mid e2) as DL; pose proof (ext_depth_right Mid e2) as DR.
  pose proof (ext_depth_app e' (ext_right Mid e2)) as DA; fold d in DA.
  set (e3 := ext_app e' (ext_right Mid e2)) in *.
  set (el := ext_left Mid e2) in *.
  destruct (option_cases (v_label (var_raw w))) as [[y El]|El]
    ; [|destruct (lt_dec (v_index (var_raw w)) (ext_depth e2)) as [Hb|Hb]].
  2: { assert (Hbl : v_index (var_raw w) < ext_depth el) by lia.
       pose proof (W_inner el _ El Hbl) as H1.
       rewrite (gapply0_inner _ _ _ _ _ _ _ el w H1 El Hbl), kleisli_var.
       assert (Hi : v_index (var_raw w) < ext_depth e3) by lia.
       rewrite (apply_inner a e3 (mk_var (var_raw w) H1) (W_inner e3 _ El Hi) El Hi).
       rewrite (gapply0_inner _ _ _ _ _ _ _ e2 w (W_inner e2 _ El Hb) El Hb).
       f_equal; apply var_eq; reflexivity. }
  all: assert (Hout : outer (ext_depth e2) (var_raw w)) by (unfold outer; intros; first [lia|congruence]).
  all: assert (Houtl : outer (ext_depth el) (var_raw w)) by (rewrite DL; exact Hout).
  all: pose proof (outer_down_wf e2 w Hout) as Hv'.
  all: set (w0 := down (ext_depth e2) (var_raw w)) in *.
  all: assert (Ew0 : down (ext_depth el) (var_raw w) = w0) by (unfold w0; rewrite DL; reflexivity).
  all: pose proof (napply_ncompose (adj_raw a) ρ w0 (aok_wf _ _ _ Hx1b)) as Hc; fold ρ'' in Hc.
  all: destruct (napply ρ w0) as [w'|[u3 ρ3]] eqn:E;
    [ (* a variable of the payload *)
      assert (H1 : Is_true_s (wf_var (ext_mid Mid e2) (up (d + ext_depth el) w')))
        by (sqa; apply (pay_var_wf ρ Kx M d Mid el w0 w' Hx1b);
            [apply Nat.eqb_eq, Is_true_s_elim, HL1|exact Hv'|exact E]);
      rewrite (gapply0_var _ _ _ _ _ _ _ el w w' H1 Houtl) by (rewrite Ew0; exact E);
      rewrite kleisli_var;
      set (wv := {| var_raw := up (d + ext_depth el) w'; var_ok := H1 |});
      assert (Hr : outer (ext_depth e3) (var_raw wv))
        by (unfold outer; cbn; destruct w' as [[y'|] j]; cbn; [discriminate|intros _; lia]);
      assert (Hdn : down (ext_depth e3) (var_raw wv) = w')
        by (cbn; rewrite DA, DR, DL, (Nat.add_comm (ext_depth e2) d); apply down_up);
      assert (Hw' : wf_var M w' = true)
        by (pose proof (res_wf Kx M ρ w0 Hx1b Hv') as X; rewrite E in X; exact X);
      destruct (napply (radj_n (adj_raw a)) w') as [z|[u2 ρ2]] eqn:E2;
      [ assert (H2 : Is_true_s (wf_var L2 (up (ext_depth e3) z)))
          by (sqa; apply (top_var_wf a e3 w' z Hw' E2));
        rewrite (apply_var a e3 wv z H2 Hr) by (rewrite Hdn; exact E2);
        assert (H3 : Is_true_s (wf_var L2 (up (d + ext_depth e2) z))) by (rewrite DA, DR, Nat.add_comm in H2; exact H2);
        rewrite (gapply0_var _ _ _ _ _ _ _ e2 w z H3 Hout Hc);
        f_equal; apply var_eq; cbn; rewrite DA, DR, Nat.add_comm; reflexivity
      | assert (Hρ2 : aok (projT1 u2) P' ρ2 = true) by (apply (top_payload_ok a w' u2 ρ2 Hw' E2));
        rewrite (apply_pay a e3 wv u2 ρ2 (W_tHL e3) (Is_true_s_intro Hρ2) Hr) by (rewrite Hdn; exact E2);
        assert (HL3 : Is_true_s (Nat.eqb L2 ((d + ext_depth e2) + P')))
          by (sqa; apply Nat.eqb_eq; pose proof (ext_depth_L e2); apply Is_true_s_elim, Nat.eqb_eq in HL2; lia);
        rewrite (gapply0_pay _ _ _ _ _ _ _ e2 w u2 ρ2 HL3 (Is_true_s_intro Hρ2) Hout Hc);
        rewrite (gapply0_s_eq ρ2 _ P' L2 (ext_depth e3) (d + ext_depth e2) ltac:(lia) (W_tHL e3) HL3);
        reflexivity ]
    | ].
  (* a nested payload *)
  all: pose proof (napply_depth_aok _ _ _ w0 _ _ Hx1b E) as Hd3.
  all: assert (Hρ3 : aok (projT1 u3) M ρ3 = true) by (apply (pay_payload_ok ρ Kx M w0 u3 ρ3 Hx1b Hv' E)).
  all: assert (Hρ3' : aok (projT1 u3) P' (Compose.compose (radj_n (adj_raw a)) ρ3) = true)
         by (apply (pay_payload_ok ρ'' Kx P' w0 u3 _ Hx2b Hv' Hc)).
  all: assert (HLa : Is_true_s (Nat.eqb (ext_mid Mid e2) ((d + ext_depth el) + M))) by (apply (W_HL M d el HL1)).
  all: rewrite (gapply0_pay _ _ _ _ _ _ _ el w u3 ρ3 HLa (Is_true_s_intro Hρ3) Houtl) by (rewrite Ew0; exact E).
  all: assert (HLb : Is_true_s (Nat.eqb (ext_mid Mid e2) (ext_depth e3 + M)))
         by (sqa; apply Is_true_s_elim, Nat.eqb_eq in HLa; apply Nat.eqb_eq; lia).
  all: rewrite (gapply0_s_eq ρ3 _ M (ext_mid Mid e2) (d + ext_depth el) (ext_depth e3) ltac:(lia) HLa HLb).
  all: assert (HL3 : Is_true_s (Nat.eqb L2 ((d + ext_depth e2) + P')))
         by (sqa; apply Nat.eqb_eq; pose proof (ext_depth_L e2); apply Is_true_s_elim, Nat.eqb_eq in HL2; lia).
  all: rewrite (gapply0_pay _ _ _ _ _ _ _ e2 w u3 _ HL3 (Is_true_s_intro Hρ3') Hout Hc).
  all: assert (HL4 : Is_true_s (Nat.eqb L2 (ext_depth e3 + P')))
         by (sqa; apply Is_true_s_elim, Nat.eqb_eq in HL3; apply Nat.eqb_eq; lia).
  all: rewrite (gapply0_s_eq (Compose.compose (radj_n (adj_raw a)) ρ3) _ P' L2 (d + ext_depth e2) (ext_depth e3) ltac:(lia) HL3 HL4).
  all: apply IH; lia.
Qed.

Lemma apply_compose {N M P'} (a : adj term M P') (b : adj term N M) {K L} (e : ext N P' K L) v :
  comp_m (apply a) (apply b) K L e v = apply (compose a b) K L e v.
Proof.
  unfold comp_m.
  pose proof (ext_depth_left M e) as DL; pose proof (ext_depth_right M e) as DR.
  set (d := ext_depth e) in *.
  set (el := ext_left M e) in *; set (er := ext_right M e) in *.
  destruct (option_cases (v_label (var_raw v))) as [[y El]|El];
    [|destruct (lt_dec (v_index (var_raw v)) d) as [Hi|Hi]].
  2: { assert (Hi1 : v_index (var_raw v) < ext_depth el) by lia.
       pose proof (W_inner el _ El Hi1) as H0.
       rewrite (apply_inner b el v H0 El Hi1), kleisli_var.
       assert (Hi2 : v_index (var_raw v) < ext_depth er) by lia.
       rewrite (apply_inner a er (mk_var (var_raw v) H0) (W_inner er _ El Hi2) El Hi2).
       rewrite (apply_inner (compose a b) e v (W_inner e _ El Hi) El Hi).
       f_equal; apply var_eq; reflexivity. }
  all: assert (Hr : outer d (var_raw v)) by (unfold outer; intros; first [lia|congruence]).
  all: assert (Hrl : outer (ext_depth el) (var_raw v)) by (rewrite DL; exact Hr).
  all: pose proof (napply_rcompose (adj_raw a) (adj_raw b) (down d (var_raw v))) as Hc.
  all: pose proof (outer_down_wf e v Hr) as Hv'; fold d in Hv'.
  all: destruct (napply (radj_n (adj_raw b)) (down d (var_raw v))) as [w|[u ρ]] eqn:E;
    [ (* [b] gives a variable *)
      assert (H1 : Is_true_s (wf_var (ext_mid M e) (up (ext_depth el) w)))
        by (apply Is_true_s_intro, (top_var_wf b el (down d (var_raw v)) w); [exact Hv'|exact E]);
      rewrite (apply_var b el v w H1 Hrl) by (rewrite DL; exact E);
      rewrite kleisli_var;
      set (wv := {| var_raw := up (ext_depth el) w; var_ok := H1 |});
      assert (Hr2 : outer (ext_depth er) (var_raw wv))
        by (unfold outer; cbn; rewrite DL, DR; destruct w as [[y'|] j]; cbn; [discriminate|intros _; lia]);
      assert (Hdn : down (ext_depth er) (var_raw wv) = w) by (cbn; rewrite DL, DR; apply down_up);
      assert (Hw : wf_var M w = true)
        by (pose proof (res_wf N M _ _ (Is_true_s_elim (top_aok b)) Hv') as X; rewrite E in X; exact X);
      destruct (napply (radj_n (adj_raw a)) w) as [z|[u2 ρ2]] eqn:E2;
      [ assert (H2 : Is_true_s (wf_var L (up (ext_depth er) z)))
          by (apply Is_true_s_intro, (top_var_wf a er w z Hw E2));
        rewrite (apply_var a er wv z H2 Hr2) by (rewrite Hdn; exact E2);
        assert (H3 : Is_true_s (wf_var L (up d z))) by (rewrite DR in H2; exact H2);
        rewrite (apply_var (compose a b) e v z H3 Hr) by (cbn [adj_raw compose]; fold d; exact Hc);
        f_equal; apply var_eq; cbn; rewrite DR; reflexivity
      | pose proof (top_payload_ok a w u2 ρ2 Hw E2) as Hρ2;
        rewrite (apply_pay a er wv u2 ρ2 (W_tHL er) (Is_true_s_intro Hρ2) Hr2) by (rewrite Hdn; exact E2);
        rewrite (apply_pay (compose a b) e v u2 ρ2 (W_tHL e) (Is_true_s_intro Hρ2) Hr)
          by (cbn [adj_raw compose]; fold d; exact Hc);
        rewrite (gapply0_s_eq ρ2 _ P' L (ext_depth er) d DR (W_tHL er) (W_tHL e));
        reflexivity ]
    | ].
  (* [b] gives a payload *)
  all: pose proof (top_payload_ok b _ u ρ Hv' E) as Hρ.
  all: rewrite (apply_pay b el v u ρ (W_tHL el) (Is_true_s_intro Hρ) Hrl) by (rewrite DL; exact E).
  all: assert (Hρ' : aok (projT1 u) P' (Compose.compose (radj_n (adj_raw a)) ρ) = true)
         by (apply (top_payload_ok (compose a b) (down d (var_raw v)) u);
             [exact Hv'|cbn [adj_raw compose]; fold d; rewrite Hc; reflexivity]).
  all: rewrite (apply_pay (compose a b) e v u _ (W_tHL e) (Is_true_s_intro Hρ') Hr)
         by (cbn [adj_raw compose]; fold d; rewrite Hc; reflexivity).
  all: assert (HL1 : Is_true_s (Nat.eqb (ext_mid M e) (ext_depth er + M)))
         by (apply Is_true_s_intro, Nat.eqb_eq; pose proof (ext_depth_L el); lia).
  all: rewrite (gapply0_s_eq ρ _ M (ext_mid M e) (ext_depth el) (ext_depth er) ltac:(lia) (W_tHL el) HL1).
  all: assert (HL2 : Is_true_s (Nat.eqb L (ext_depth er + P')))
         by (apply Is_true_s_intro, Nat.eqb_eq; pose proof (ext_depth_L e); lia).
  all: rewrite (gapply0_s_eq _ _ P' L d (ext_depth er) ltac:(lia) (W_tHL e) HL2).
  all: apply (gapply0_compose (S (nnest ρ))); lia.
Qed.

Theorem subst_compose {N M P'} (a : adj term M P') (b : adj term N M) (t : term N) :
  subst a (subst b t) = subst (compose a b) t.
Proof.
  rewrite kleisli_comp_here.
  apply kleisli_ext; intros; apply apply_compose.
Qed.

(** ** Variables *)

Theorem apply_under {N M K L} (a : adj term N M) (e : ext N M K L) (v : var (S K)) :
  apply a (S K) (S L) (ext_under e) v = apply (lift a) (S K) (S L) (ext_shift e) v.
Proof. rewrite <- (ext_app_shift e); apply apply_lift_rebase. Qed.

Lemma down0 rv : down 0 rv = rv.
Proof. destruct rv as [[y|] i]; unfold down; cbn; [reflexivity|rewrite Nat.sub_0_r; reflexivity]. Qed.

Lemma up0 rv : up 0 rv = rv.
Proof. destruct rv as [[y|] i]; reflexivity. Qed.

(** Applying a substitution to a variable: a variable, or the term with
    its adjustment substituted. *)
Theorem apply_here_eval {N M} (a : adj term N M) (v : var N) :
  apply a N M ext_here v = Indexed.eval tvar (fun K ρ u => u [ρ]) a v.
Proof.
  unfold Indexed.eval, Indexed.apply_var.
  generalize (apply_wf a v); unfold Indexed.apply, rapply.
  assert (Hout : outer (ext_depth (@ext_here N M)) (var_raw v)) by (unfold outer; cbn; lia).
  assert (Hd : down (ext_depth (@ext_here N M)) (var_raw v) = var_raw v) by apply down0.
  destruct (napply (radj_n (adj_raw a)) (var_raw v)) as [w|[u x]] eqn:E; intros H; cbn [rpack].
  - assert (H' : Is_true_s (wf_var M (up (ext_depth (@ext_here N M)) w))) by (cbn; rewrite up0; exact (Is_true_s_intro H)).
    rewrite (apply_var a ext_here v w H' Hout) by (rewrite Hd; exact E).
    f_equal; apply var_eq; apply up0.
  - assert (Hx : nwf x) by exact (nwf_payload _ _ u x (radj_wf (adj_raw a)) E).
    assert (Hρ : aok (projT1 u) M x = true) by (apply (top_payload_ok a (var_raw v) u x); [apply Is_true_s_elim, var_ok|exact E]).
    rewrite (apply_pay a ext_here v u x (W_tHL ext_here) (Is_true_s_intro Hρ) Hout) by (rewrite Hd; exact E).
    cbn [projT1 projT2].
    apply kleisli_ext; intros K L e w.
    rewrite (apply_gapply0 _ top_HL (top_aok _)); cbn [adj_raw].
    assert (PE : forall y (Ey : x = y) Hy, gapply0 x (projT1 u) M 0 M top_HL (Is_true_s_intro Hρ) K L e w
                                          = gapply0 y (projT1 u) M 0 M top_HL Hy K L e w)
      by (intros y <- Hy; reflexivity).
    apply PE; symmetry; apply radj_n_to_adj, Hx.
Qed.

Theorem subst_tvar_eval {N M} (a : adj term N M) (v : var N) :
  subst a (tvar v) = Indexed.eval tvar (fun K ρ u => u [ρ]) a v.
Proof. rewrite kleisli_var; apply apply_here_eval. Qed.

Theorem subst_tvar_rename {N M} (a : adj term N M) (v : var N) (w : var M) :
  Indexed.apply_var a v = Rename w -> subst a (tvar v) = tvar w.
Proof. intros H; rewrite subst_tvar_eval; unfold Indexed.eval; rewrite H; reflexivity. Qed.

Lemma ext_shift_here {N M} : ext_shift (@ext_here N M) = ext_here.
Proof. reflexivity. Qed.

Lemma ext_shift_under {N M K L} (e : ext N M K L) : ext_shift (ext_under e) = ext_under (ext_shift e).
Proof. reflexivity. Qed.


Theorem eval_fold {N M} (a : adj term N M) (v : var N) :
  Indexed.eval tvar (fun K ρ u => u [ρ]) a v = subst a (tvar v).
Proof. rewrite kleisli_var; symmetry; apply apply_here_eval. Qed.

(** [names] first applies the monad laws that remove a Kleisli extension
    or move work into the adjustment: going under a binder lifts the
    adjustment ([names_pre]); nested substitutions fuse in [names] itself,
    by the law's [sl_comp].  The
    substitutions are then the nodes [names] works on ([names_node],
    below), and after it they are written back as substitutions. *)

(** ** The law [names] uses

    Results related by the bases [names] converts and materialises with
    ([Conv.lawbase]), also inside payloads and in steps ([drel]), give
    the same substitution ([subst_rel]).  A result is read at the output
    scope [M], used under [d] binders ([rv]): a variable, or the term
    substituted by its payload; related results read the same. *)


Section Rel.

Definition sub0 : forall N M, adj term N M -> term N -> term M := fun N M a t => t [a].

Definition rvn (M : nat) (r : result) (d L : nat) (HL : Is_true_s (Nat.eqb L (d + M))) (t : term L) : Prop :=
  match r with
  | inl w => exists H : wf_var L (up d w) = true, t = tvar (mk_var (up d w) (Is_true_s_intro H))
  | inr (u, ρ) => exists Hρ : aok (projT1 u) M ρ = true,
      t = kleisli (gapply0 ρ (projT1 u) M d L HL (Is_true_s_intro Hρ)) ext_here (projT2 u)
  end.

Definition rv (M : nat) (r : rresult P) := rvn M (lower r).

Lemma rvn_det M r d L HL HL' t t' : rvn M r d L HL t -> rvn M r d L HL' t' -> t = t'.
Proof. unfold rvn; destruct r as [w|[u ρ]]; intros [H1 ->] [H2 ->]; reflexivity. Qed.

Lemma rvn_cast M r d d' L HL HL' t : d = d' -> rvn M r d L HL t -> rvn M r d' L HL' t.
Proof. intros <-; exact (fun H => H). Qed.

Lemma inner_or_outer d rv : (v_label rv = None /\ v_index rv < d) \/ outer d rv.
Proof.
  destruct rv as [[y|] i]; unfold outer; cbn; [right; discriminate|].
  destruct (lt_dec i d); [left; auto|right; intros _; lia].
Qed.

Lemma outer_up d w : outer d (up d w).
Proof. destruct w as [[y|] i]; unfold outer, up; cbn; [discriminate|intros _; lia]. Qed.

Lemma gapply0_pe x y (E : x = y) Kx Mx s L0 HL Hx Hy : gapply0 x Kx Mx s L0 HL Hx = gapply0 y Kx Mx s L0 HL Hy.
Proof. subst; reflexivity. Qed.

(** What [gapply0] gives on an input outside the binders crossed. *)
Lemma rvn_gapply0 x Kx Mx s L0 HL Hx {K L} (e : ext Kx L0 K L) v HL' :
  outer (ext_depth e) (var_raw v) ->
  rvn Mx (napply x (down (ext_depth e) (var_raw v))) (s + ext_depth e) L HL' (gapply0 x Kx Mx s L0 HL Hx K L e v).
Proof.
  intros Hout; pose proof (gapply0_result x Kx Mx s L0 HL Hx e v Hout) as R.
  pose proof (Is_true_s_elim Hx) as Hx0.
  pose proof (outer_down_wf e v Hout) as Hv'.
  unfold rvn; destruct (napply x _) as [w|[u ρ]] eqn:E.
  - exists (pay_var_wf x Kx Mx s L0 e _ w Hx0 (proj1 (Nat.eqb_eq _ _) (Is_true_s_elim HL)) Hv' E); apply R.
  - exists (pay_payload_ok x Kx Mx _ u ρ Hx0 Hv' E); apply R.
Qed.

(** A morphism that sends the variables outside [s] binders where [W]
    does, used under [d0] binders. *)
Definition hrel (W : nadj) (M s d0 : nat) {m L1} (h : morph m L1) : Prop :=
  forall K L (e : ext m L1 K L) v,
    (v_label (var_raw v) = None -> v_index (var_raw v) < s + ext_depth e ->
       exists H : wf_var L (var_raw v) = true, h K L e v = tvar (mk_var (var_raw v) (Is_true_s_intro H)))
    /\ (outer (s + ext_depth e) (var_raw v) -> forall HL,
          rvn M (napply W (down (s + ext_depth e) (var_raw v))) (d0 + ext_depth e) L HL (h K L e v)).

Lemma hrel_gapply0 W Mid Mout d0 L1 HL1 Hw : hrel W Mout 0 d0 (gapply0 W Mid Mout d0 L1 HL1 Hw).
Proof.
  intros K L e v; split.
  - intros Hl Hi; pose proof (W_inner e _ Hl Hi) as H.
    exists (Is_true_s_elim H); apply gapply0_inner; assumption.
  - intros Hout HL; apply (rvn_gapply0 W Mid Mout d0 L1 HL1 Hw e v HL Hout).
Qed.

Lemma hrel_rebase W M s d0 {m L1 K0 L0} (e0 : ext m L1 K0 L0) h :
  hrel W M s d0 h -> hrel W M (s + ext_depth e0) (d0 + ext_depth e0) (rebase_m e0 h).
Proof.
  intros Hh K L e v; destruct (Hh K L (ext_app e0 e) v) as [H1 H2].
  rewrite ext_depth_app in H1, H2; unfold rebase_m; split.
  - intros Hl Hi; apply H1; [exact Hl|lia].
  - intros Hout HL.
    assert (E1 : s + (ext_depth e + ext_depth e0) = s + ext_depth e0 + ext_depth e) by lia.
    assert (E2 : d0 + (ext_depth e + ext_depth e0) = d0 + ext_depth e0 + ext_depth e) by lia.
    assert (HL2 : Is_true_s (Nat.eqb L ((d0 + (ext_depth e + ext_depth e0)) + M)))
      by (apply Is_true_s_intro, Nat.eqb_eq; apply Is_true_s_elim, Nat.eqb_eq in HL; lia).
    rewrite <- E1 in Hout |- *.
    exact (rvn_cast _ _ _ _ L HL2 HL _ E2 (H2 Hout HL2)).
Qed.

(** Substituting with a morphism that sends the variables where [W] does
    after applying [y] to a payload term is applying [W ∘ y]. *)
Lemma comp_gapply (W : radj P) M n : forall y, nnest y < n ->
  forall Kx Mid s m HLm Hy d0 L1 HL1 Hz (h : morph m L1), hrel (radj_n W) M s d0 h ->
  forall u : term Kx,
  kleisli h ext_here (kleisli (gapply0 y Kx Mid s m HLm Hy) ext_here u)
  = kleisli (gapply0 (Compose.compose (radj_n W) y) Kx M d0 L1 HL1 Hz) ext_here u.
Proof.
  induction n as [|n IH]; intros y Hn Kx Mid s m HLm Hy d0 L1 HL1 Hz h Hh u; [lia|].
  rewrite kleisli_comp_here; apply kleisli_ext; intros K L e v; unfold comp_m.
  pose proof (ext_depth_left m e) as DL; pose proof (ext_depth_right m e) as DR.
  set (k := ext_depth e) in *.
  set (el := ext_left m e) in *; set (er := ext_right m e) in *.
  pose proof (Is_true_s_elim Hy) as Hy0; pose proof (Is_true_s_elim Hz) as Hz0.
  assert (Hwy : nwf y) by apply (aok_wf _ _ _ Hy0).
  destruct (inner_or_outer k (var_raw v)) as [[El Hi]|Hr].
  { assert (Hi1 : v_index (var_raw v) < ext_depth el) by lia.
    pose proof (W_inner el _ El Hi1) as H0.
    rewrite (gapply0_inner _ _ _ _ _ _ _ el v H0 El Hi1), kleisli_var.
    destruct (proj1 (Hh _ _ er (mk_var (var_raw v) H0)) El ltac:(cbn; lia)) as [H3 ->].
    rewrite (gapply0_inner _ _ _ _ _ _ _ e v (W_inner e _ El Hi) El Hi).
    f_equal; apply var_eq; reflexivity. }
  assert (Hrl : outer (ext_depth el) (var_raw v)) by (rewrite DL; exact Hr).
  pose proof (W_HL M d0 e HL1) as HLR.
  pose proof (rvn_gapply0 _ _ _ _ _ HL1 Hz e v HLR Hr) as RR.
  rewrite napply_ncompose in RR by exact Hwy; fold k in RR, HLR.
  pose proof (W_HL Mid s el HLm) as HLl.
  pose proof (rvn_gapply0 _ _ _ _ _ HLm Hy el v HLl Hrl) as RL.
  replace (down (ext_depth el) (var_raw v)) with (down k (var_raw v)) in RL by (rewrite DL; reflexivity).
  destruct (napply y (down k (var_raw v))) as [w|[u' y']] eqn:E.
  - (* a variable *)
    destruct RL as [H1 ->]; rewrite kleisli_var.
    assert (Hup : outer (s + ext_depth er) (up (s + ext_depth el) w)) by (rewrite DL, DR; apply outer_up).
    pose proof (W_HL M d0 er HL1) as HLR'.
    pose proof (proj2 (Hh _ _ er (mk_var _ (Is_true_s_intro H1))) Hup HLR') as H3; cbn [var_raw] in H3.
    replace (down (s + ext_depth er) (up (s + ext_depth el) w)) with w in H3 by (rewrite DL, DR; symmetry; apply down_up).
    exact (rvn_det _ _ _ _ _ _ _ _ (rvn_cast _ _ _ (d0 + k) L HLR' HLR _ ltac:(rewrite DR; reflexivity) H3) RR).
  - (* a payload *)
    destruct RL as [Hρ' ->]; destruct RR as [Hz' ->].
    rewrite (kleisli_rebase_here h er).
    pose proof (hrel_rebase _ M s d0 er h Hh) as Hh'; rewrite DR in Hh'.
    assert (HLl2 : Is_true_s (Nat.eqb (ext_mid m e) ((s + k) + Mid)))
      by (apply Is_true_s_intro, Nat.eqb_eq; apply Is_true_s_elim, Nat.eqb_eq in HLl; lia).
    rewrite (gapply0_s_eq y' _ Mid _ (s + ext_depth el) (s + k) ltac:(lia) HLl HLl2).
    apply (IH y' ltac:(pose proof (napply_depth_aok _ _ _ _ _ _ Hy0 E); lia) (projT1 u') Mid (s + k) (ext_mid m e) HLl2
             (Is_true_s_intro Hρ') (d0 + k) L HLR (Is_true_s_intro Hz') (rebase_m er h) Hh' (projT2 u')).
Qed.

(** ** Related results *)

Definition rv_le (M : nat) (r r' : rresult P) : Prop :=
  (rwf M r = true -> rwf M r' = true) /\ (forall d L HL t, rv M r d L HL t -> rv M r' d L HL t).

Lemma rv_le_refl M r : rv_le M r r.
Proof. split; auto. Qed.

Lemma rv_le_trans M r r' r'' : rv_le M r r' -> rv_le M r' r'' -> rv_le M r r''.
Proof. intros [W1 V1] [W2 V2]; split; auto. Qed.

Theorem subst_rv {N M} (a a' : adj term N M) :
  (forall v : var N, rv_le M (rapply (adj_raw a) (var_raw v)) (rapply (adj_raw a') (var_raw v))) ->
  forall t, t [a] = t [a'].
Proof.
  intros H t; apply kleisli_ext; intros K L e v.
  destruct (inner_or_outer (ext_depth e) (var_raw v)) as [[El Hi]|Hr].
  { rewrite (apply_inner a e v (W_inner e _ El Hi) El Hi), (apply_inner a' e v (W_inner e _ El Hi) El Hi); reflexivity. }
  all: pose proof (outer_down_wf e v Hr) as Hv'.
  all: pose proof (rvn_gapply0 _ _ _ _ _ top_HL (top_aok a) e v (W_tHL e) Hr) as R1.
  all: pose proof (rvn_gapply0 _ _ _ _ _ top_HL (top_aok a') e v (W_tHL e) Hr) as R2.
  all: rewrite <- (apply_gapply0 a top_HL (top_aok a)) in R1.
  all: rewrite <- (apply_gapply0 a' top_HL (top_aok a')) in R2.
  all: rewrite <- lower_rapply in R1, R2.
  all: destruct (H (mk_var (down (ext_depth e) (var_raw v)) (Is_true_s_intro Hv'))) as [_ Hrv].
  all: exact (rvn_det _ _ _ _ _ _ _ _ (Hrv _ _ _ _ R1) R2).
Qed.

Lemma lawbase_not_inl w r' : ~ lawbase (@tvar term Sx) sub0 (inl w) r'.
Proof.
  intros [[K [M [u [c [E _]]]]]|[[K [M [u [c [W [E _]]]]]]|[K [w' [W [E _]]]]]]; discriminate.
Qed.

(** A variable is related only to itself. *)
Lemma drel_inl r r' : drel (lawbase (@tvar term Sx) sub0) r r' -> forall w, r = inl w -> r' = inl w.
Proof.
  induction 1 as [r|r r' Hb|u W W' ρ _ _|r r' r'' _ IH1 _ IH2]; intros w E.
  - exact E.
  - subst; destruct (lawbase_not_inl _ _ Hb).
  - discriminate.
  - apply IH2, IH1, E.
Qed.

Lemma rv_le_pay M (W W' : radj P) :
  (forall v, drel (lawbase (@tvar term Sx) sub0) (rapply W v) (rapply W' v)) -> (forall v, rv_le M (rapply W v) (rapply W' v)) ->
  forall n ρ u, rdepth ρ < n -> rv_le M (inr (u, rcompose W ρ)) (inr (u, rcompose W' ρ)).
Proof.
  intros HW IHW n; induction n as [|n IH]; intros ρ u Hn; [lia|].
  assert (Wf : rwf M (inr (u, rcompose W ρ)) = true -> rwf M (inr (u, rcompose W' ρ)) = true).
  { change (scoped (projT1 u) M (rcompose W ρ) = true -> scoped (projT1 u) M (rcompose W' ρ) = true).
    intros Hs; apply scoped_spec in Hs as [Ht Hv]; apply scoped_spec; split.
    - intros i Hi; specialize (Ht i Hi); rewrite rapply_compose in Ht |- *.
      destruct (rapply ρ (mk_rvar None i)) as [w|[u' ρ']] eqn:E; [|discriminate].
      exact (drel_inl _ _ (HW w) _ Ht).
    - intros v Hv0; specialize (Hv v Hv0); rewrite rapply_compose in Hv |- *.
      destruct (rapply ρ v) as [w|[u' ρ']] eqn:E; [apply (proj1 (IHW w)), Hv|].
      apply (proj1 (IH ρ' u' ltac:(pose proof (rdepth_payload ρ v u' ρ' E); lia))), Hv. }
  split; [exact Wf|].
  unfold rv, rvn; cbn [lower]; intros d L HL t [Hρ ->].
  assert (Hρ' : aok (projT1 u) M (radj_n (rcompose W' ρ)) = true)
    by (rewrite aok_scoped; apply Wf; change (aok (projT1 u) M (radj_n (rcompose W ρ)) = true) in Hρ;
        rewrite aok_scoped in Hρ; exact Hρ).
  exists Hρ'.
  apply kleisli_ext; intros K' L' e v.
  destruct (inner_or_outer (ext_depth e) (var_raw v)) as [[El Hi]|Hr].
  { rewrite !(gapply0_inner _ _ _ _ _ _ _ e v (W_inner e _ El Hi) El Hi); reflexivity. }
  all: pose proof (W_HL M d e HL) as HL2.
  all: pose proof (rvn_gapply0 _ _ _ _ _ HL (Is_true_s_intro Hρ) e v HL2 Hr) as R1.
  all: pose proof (rvn_gapply0 _ _ _ _ _ HL (Is_true_s_intro Hρ') e v HL2 Hr) as R2.
  all: rewrite <- lower_rapply, rapply_compose in R1, R2.
  all: destruct (rapply ρ (down (ext_depth e) (var_raw v))) as [w|[u' ρ']] eqn:E.
  1: exact (rvn_det _ _ _ _ _ _ _ _ (proj2 (IHW w) _ _ _ _ R1) R2).
  all: exact (rvn_det _ _ _ _ _ _ _ _
                (proj2 (IH ρ' u' ltac:(pose proof (rdepth_payload ρ _ u' ρ' E); lia)) _ _ _ _ R1) R2).
Qed.

Lemma scoped_unique K M M' (a : radj P) : scoped K M a = true -> scoped K M' a = true -> M = M'.
Proof.
  intros H1 H2; apply scoped_spec in H1 as [T1 _]; apply scoped_spec in H2 as [T2 _].
  specialize (T1 K (le_n K)); specialize (T2 K (le_n K)); rewrite T1 in T2.
  injection T2; lia.
Qed.

Lemma aok_identity M : aok M M (radj_n (@ridentity P)) = true.
Proof. rewrite aok_scoped; apply scoped_identity. Qed.

Lemma matbase_rv M r r' : matbase sub0 r r' -> rv_le M r r'.
Proof.
  intros [K [M' [u [c [-> ->]]]]].
  assert (Hc := adj_scoped c).
  split.
  - change (scoped K M (adj_raw c) = true -> scoped M' M (@ridentity P) = true).
    intros Hs; rewrite (scoped_unique K M' M _ Hc Hs); apply scoped_identity.
  - unfold rv, rvn; cbn [lower projT1 projT2]; intros d L HL t [Hρ ->].
    assert (Hs : scoped K M (adj_raw c) = true) by (rewrite <- aok_scoped; exact Hρ).
    assert (EM := scoped_unique K M' M _ Hc Hs); subst M'.
    exists (aok_identity M); unfold sub0.
    rewrite (apply_gapply0 c top_HL (top_aok c)).
    assert (Ec : Compose.compose (radj_n (@ridentity P)) (radj_n (adj_raw c)) = radj_n (adj_raw c))
      by exact (f_equal radj_n (rcompose_identity_l (adj_raw c))).
    assert (Hz : Is_true_s (aok K M (Compose.compose (radj_n (@ridentity P)) (radj_n (adj_raw c)))))
      by (apply Is_true_s_intro; rewrite Ec; exact Hρ).
    rewrite (comp_gapply ridentity M (S (nnest (radj_n (adj_raw c)))) (radj_n (adj_raw c)) ltac:(lia) K M 0 M top_HL (top_aok c) d L HL
               Hz _ (hrel_gapply0 _ M M d L HL (Is_true_s_intro (aok_identity M))) u).
    symmetry; apply (f_equal (fun f => kleisli f ext_here u)); apply gapply0_pe, Ec.
Qed.

Lemma nbase_rv M r r' : nbase sub0 r r' -> rv_le M r r'.
Proof.
  intros [K [M' [u [c [W [-> ->]]]]]].
  assert (Hc := adj_scoped c).
  split.
  - change (scoped M' M W = true -> scoped K M (rcompose W (adj_raw c)) = true).
    intros Hs; exact (scoped_compose K M' M W _ Hs Hc).
  - unfold rv, rvn; cbn [lower projT1 projT2]; intros d L HL t [Hρ ->].
    assert (Hs : scoped M' M W = true) by (rewrite <- aok_scoped; exact Hρ).
    assert (Hz : aok K M (radj_n (rcompose W (adj_raw c))) = true)
      by (rewrite aok_scoped; exact (scoped_compose K M' M W _ Hs Hc)).
    exists Hz; unfold sub0.
    rewrite (apply_gapply0 c top_HL (top_aok c)).
    exact (comp_gapply W M (S (nnest (radj_n (adj_raw c)))) (radj_n (adj_raw c)) ltac:(lia) K M' 0 M' top_HL (top_aok c) d L HL
             (Is_true_s_intro Hz) _ (hrel_gapply0 _ M' M d L HL (Is_true_s_intro Hρ)) u).
Qed.

Lemma vbase_rv M r r' : vbase (@tvar term Sx) r r' -> rv_le M r r'.
Proof.
  intros [K [w [W [-> ->]]]].
  split.
  - change (scoped K M W = true -> result_wf M (rapply W (var_raw w)) = true).
    intros Hs; apply scoped_spec in Hs as [_ Hv]; apply Hv, Is_true_s_elim, var_ok.
  - unfold rv, rvn; cbn [lower projT1 projT2]; intros d L HL t [Hρ ->].
    rewrite kleisli_var, lower_rapply.
    assert (Hout : outer (ext_depth (@ext_here K L)) (var_raw w)) by (unfold outer; cbn; lia).
    pose proof (rvn_gapply0 _ _ _ _ _ HL (Is_true_s_intro Hρ) ext_here w (W_HL M d ext_here HL) Hout) as R.
    cbn [ext_depth] in R; rewrite down0 in R.
    exact (rvn_cast _ _ _ _ L _ HL _ (Nat.add_0_r d) R).
Qed.

Lemma lawbase_rv M r r' : lawbase (@tvar term Sx) sub0 r r' -> rv_le M r r'.
Proof. intros [H|[H|H]]; [apply matbase_rv|apply nbase_rv|apply vbase_rv]; exact H. Qed.

Lemma drel_rv M r r' : drel (lawbase (@tvar term Sx) sub0) r r' -> rv_le M r r'.
Proof.
  induction 1 as [r|r r' Hb|u W W' ρ HW IH|r r' r'' _ IH1 _ IH2].
  - apply rv_le_refl.
  - apply lawbase_rv, Hb.
  - apply (rv_le_pay M W W' HW IH (S (rdepth ρ))); lia.
  - exact (rv_le_trans M _ _ _ IH1 IH2).
Qed.

Theorem subst_rel {N M} (a a' : adj term N M) :
  (forall v : var N, drel (lawbase (@tvar term Sx) sub0) (rapply (adj_raw a) (var_raw v)) (rapply (adj_raw a') (var_raw v))) ->
  forall t, t [a] = t [a'].
Proof. intros H; apply subst_rv; intros v; apply drel_rv, H. Qed.

(** The same for one variable: related results, read at the output
    scope, give the same term. *)
Theorem subst_res {N N' M} (a : adj term N M) (v : var N) (a' : adj term N' M) (v' : var N') :
  drel (lawbase (@tvar term Sx) sub0) (rapply (adj_raw a) (var_raw v)) (rapply (adj_raw a') (var_raw v')) ->
  (tvar v) [a] = (tvar v') [a'].
Proof.
  intros H; destruct (drel_rv M _ _ H) as [_ Hrv].
  rewrite !kleisli_var.
  assert (Hout : forall K (w : var K), outer (ext_depth (@ext_here K M)) (var_raw w)) by (intros; unfold outer; cbn; lia).
  pose proof (rvn_gapply0 _ _ _ _ _ top_HL (top_aok a) ext_here v (W_tHL ext_here) (Hout _ v)) as R1.
  pose proof (rvn_gapply0 _ _ _ _ _ top_HL (top_aok a') ext_here v' (W_tHL ext_here) (Hout _ v')) as R2.
  rewrite <- (apply_gapply0 a top_HL (top_aok a)) in R1.
  rewrite <- (apply_gapply0 a' top_HL (top_aok a')) in R2.
  cbn [ext_depth] in R1, R2; rewrite down0 in R1, R2.
  rewrite <- lower_rapply in R1, R2.
  exact (rvn_det _ _ _ _ _ _ _ _ (Hrv _ _ _ _ R1) R2).
Qed.

End Rel.

(** Substitution as the node [names] works on. *)
Definition subst_law : SubstLaw term (@tvar term Sx) sub0 :=
  {| sl_var := @subst_tvar_eval; sl_rel := @subst_rel; sl_res := @subst_res; sl_id := @subst_identity; sl_comp := @subst_compose |}.

Lemma subst_csubst {N M} (a : adj term N M) (t : term N) : t [a] = csubst subst_law a t.
Proof. reflexivity. Qed.

Lemma csubst_subst {N M} (a : adj term N M) (t : term N) : csubst subst_law a t = t [a].
Proof. reflexivity. Qed.


(** What [cbn] leaves of a substitution into a variable, as a node. *)
Lemma apply_here_node {N M} (a : adj term N M) (v : var N) : apply a N M ext_here v = csubst subst_law a (tvar v).
Proof. symmetry; apply kleisli_var. Qed.

End Subst1.

Global Hint Rewrite @kleisli_apply_under @apply_under @ext_shift_here @ext_shift_under : names_pre.
Global Hint Rewrite @subst_csubst @apply_here_node : names_node.

(** ** [names] on substitutions

    What [cbn] leaves of a substitution is the syntax's own [kleisli]
    (and its variable constructor), not the class's projections: [cbn]
    unfolds the instance and does not fold back.  [names] first writes the
    syntax's [kleisli] as the class's, for each syntax in the goal (one
    [change], so by conversion); then the substitutions are its nodes, by
    conversion too ([csubst subst_law] is [t [a]] unfolded), and what
    [cbn] leaves of a substitution into a variable is a node when the
    syntax's [kleisli] computes on a variable (otherwise [apply_here_node]
    rewrites it). *)
From Ltac2 Require Import Ltac2.

(** The syntaxes in the goal, [(term, instance)], from the uses of
    [apply] (which [cbn] leaves alone) and of [kleisli]. *)
Ltac2 goal_syntaxes () : (constr * constr) list :=
  let acc := { contents := [] } in
  let add t i :=
    if List.exist (fun (t', i') => Bool.and (Constr.equal t t') (Constr.equal i i')) (acc.(contents)) then ()
    else acc.(contents) := (t, i) :: acc.(contents) in
  let _ := Control.case (fun () =>
    multi_match! goal with
    | [ |- context [ @apply ?t ?i _ _ _ ] ] => add t i; Control.zero Not_found
    | [ |- context [ @Syntax.kleisli ?t ?i _ _ _ _ _ _ _ ] ] => add t i; Control.zero Not_found
    end) in
  acc.(contents).

(** The syntax's own function [proj t i] reads as, written as the class's
    projection. *)
Ltac2 fold_proj (g : constr) : unit :=
  let sk := Names.unfold_head g in
  if Constr.equal sk g then () else
  Names.attempt (fun () => ltac1:(sk gk |- change sk with gk) (Ltac1.of_constr sk) (Ltac1.of_constr g)) (fun _ => ()).

(** The syntax's own [kleisli] written as the class's ([names]); with
    [vars], its variable constructor too (for rewriting with the
    library's lemmas, stated with the class's). *)
Ltac2 syntax_fold_with (vars : bool) : unit :=
  List.iter (fun (t, i) =>
    fold_proj '(@Syntax.kleisli $t $i);
    if vars then fold_proj '(@Syntax.tvar $t $i) else ())
    (goal_syntaxes ()).

Ltac2 syntax_fold () : unit := syntax_fold_with false.

Ltac2 subst_nodes () : unit :=
  let laws := { contents := [] } in
  let law t i :=
    match List.find_opt (fun (t', i', _) => Bool.and (Constr.equal t t') (Constr.equal i i')) (laws.(contents)) with
    | Some (_, _, l) => l
    | None =>
        let lw := '(@subst_law $t $i) in
        let (_, ta) := Names.split_app (Constr.type lw) in
        let l := (Array.get ta 1, Array.get ta 2, lw) in
        laws.(contents) := (t, i, l) :: laws.(contents); l
    end in
  let node t i n m a u := let (tv, sb, lw) := law t i in Names.app constr:(@csubst) [t; tv; sb; lw; n; m; a; u] in
  let rec rounds p f :=
    match Control.case (fun () => Pattern.matches_subterm p (Control.goal ())) with
    | Err _ => ()
    | Val _ => Std.change (Some p) f (Names.concl ()); rounds p f
    end in
  (* [t [a]]; in a chain [t [a] [b] …], the inner ones at once *)
  let sp := pat:(@Syntax.kleisli ?a1 ?a2 ?a3 ?a4 (@apply _ _ _ _ ?a5) _ _ (@ext_here _ _) ?a6) in
  let rec conv s := node (Array.get s 0) (Array.get s 1) (Array.get s 2) (Array.get s 3) (Array.get s 4) (inner (Array.get s 5))
  with inner u := match Control.case (fun () => Pattern.matches_vect sp u) with Val (s, _) => conv s | Err _ => u end in
  rounds sp conv;
  (* [apply a _ _ ext_here v], by conversion where [kleisli] computes *)
  Names.attempt (fun () =>
    rounds pat:(@apply ?a1 ?a2 ?a3 ?a4 ?a5 _ _ (@ext_here _ _) ?a6)
      (fun s => let (t, i, n, v) := (Array.get s 0, Array.get s 1, Array.get s 2, Array.get s 5) in
                node t i n (Array.get s 3) (Array.get s 4) '(@Syntax.tvar $t $i $n $v)))
    (fun _ => Names.autorw @names_node).

Ltac2 Set Names.names_fold_hook := syntax_fold.
Ltac2 Set Names.names_node_hook := subst_nodes.

(** For Ltac1 proofs: after [cbn], the syntax's own functions written as
    the library's, so that the library's lemmas rewrite. *)
Ltac syntax_fold := ltac2:(syntax_fold_with true).
