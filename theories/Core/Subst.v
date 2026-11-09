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

Context {T : Type}.

Local Notation nadj := (@nadj T).
Local Notation entry := (@entry T).
Local Notation target := (@target T).

(** Payload adjustments in scope [M]. *)
Definition pok (M : nat) (x : nadj) : bool := nwfc true (fun r => r) x && pscopedc M (fun r => r) x.

(** A payload adjustment with its root read through [rt]. *)
Definition absn (rt : counts -> counts) (x : nadj) : nadj := match x with NAdj r es => NAdj (rt r) es end.

Lemma pok_wf M x : pok M x = true -> nwf true x.
Proof. unfold pok; rewrite andb_true_iff; intros [H _]; exact H. Qed.

(** Where a lookup ends up: an entry found over base [Be]. *)
Lemma found_entry Q R (es : atrie entry) k Be h ts len p :
  nlocal Q (NAdj R es) ->
  option_map (unshift R) (aget k es) = Some (unshift Be (Entry h ts len p)) -> eok (Entry h ts len p) ->
  label_key h = k /\ Q h = true /\ kgood ts /\ klength ts = len
  /\ (forall i Bt t, i < len -> option_map (unshift Be) (knth ts i) = Some (unshift Bt t) ->
                     napply (NAdj R es) (mk_rvar h i) = tresult (unshift Bt t))
  /\ (forall i, len <= i -> napply (NAdj R es) (mk_rvar h i)
                           = inl (mk_rvar h (dval Be (label_key h) + (i - len + p))))
  /\ (forall i, i < len -> knth ts i <> None).
Proof.
  intros Hl E Hok; pose proof Hl as [_ [_ [_ [Hent _]]]].
  destruct (aget k es) as [e0|] eqn:E0; [|discriminate]; cbn in E; injection E as E.
  destruct e0 as [h0 ts0 len0 p0]; destruct (Hent _ _ E0) as [[Hk [G0 [Hl0 _]]] [HQ _]].
  cbn [unshift entry_based eunshift] in E; injection E as -> Ets -> Ep.
  assert (G : kgood ts) by (apply (kgood_unlift Be); [rewrite <- Ets; apply kgood_klift, G0|exact Hok]).
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
