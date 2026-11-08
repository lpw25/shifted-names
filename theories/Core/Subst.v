(** * Substitution for any syntax

    Given a syntax (Syntax.v), [apply a : morph N M] turns a scoped
    adjustment into the morphism [kleisli] needs, and
    [subst a t := kleisli (apply a) ext_here t].

    [apply] is structural recursion on the nested adjustment: lookups pass
    what they find to a continuation (Lookup.v), so a payload's adjustment
    is a visible subterm.  Under [d] binders it does offset arithmetic on
    [d]; it never computes a [lift].  Scoping proofs are built from the
    location proofs the lookups provide, so nothing is tested at runtime. *)

From Stdlib Require Import PArith Arith List Lia Bool StrictProp.
From ShiftedNames.Core Require Import Trie Label Var Lookup Slots Nested Adjustment Laws
  Scoped Indexed Syntax.
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

Local Notation payload := (T * nadj T)%type.

(** Payload adjustments in scope [M]. *)
Definition pok (M : nat) (x : nadj T) : bool := nnormal x && pnormal_raw (nraw x) && nscoped M x.

Lemma loc_some (m : raw payload) h ent i t :
  get (label_key h) m = Some ent -> nth_error (e_targets ent) i = Some t ->
  Slots.apply m (mk_rvar h i) = resolve m t.
Proof. intros H1 H2; unfold Slots.apply, find; cbn; rewrite H1; cbn; rewrite H2; reflexivity. Qed.

Lemma loc_pass (m : raw payload) h ent i :
  get (label_key h) m = Some ent -> nth_error (e_targets ent) i = None ->
  Slots.apply m (mk_rvar h i) = inl (mk_rvar h (i - length (e_targets ent) + e_out ent)).
Proof. intros H1 H2; unfold Slots.apply, count, find; cbn; rewrite H1; cbn; rewrite H2; reflexivity. Qed.

Lemma loc_none (m : raw payload) h i :
  get (label_key h) m = None -> Slots.apply m (mk_rvar h i) = inl (mk_rvar h i).
Proof.
  intros H1; unfold Slots.apply, count, find; cbn; rewrite H1; cbn.
  rewrite nth_error_nil; do 2 f_equal; lia.
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

Lemma top_var_wf {N M K L} (a : adj T N M) (e : ext N M K L) v' w :
  wf_var N v' = true -> napply (radj_n (adj_raw a)) v' = inl w ->
  wf_var L (up (ext_depth e) w) = true.
Proof.
  intros Hv Hw.
  pose proof (proj2 (proj1 (scoped_spec N M (adj_raw a)) (adj_scoped a)) v' Hv) as H.
  rewrite result_wf_apply, Hw in H; cbn in H.
  apply (wf_eq _ _ _ (ext_depth_L e)), up_wf, H.
Qed.

Lemma top_payload_ok {N M} (a : adj T N M) v' u ρ :
  wf_var N v' = true -> napply (radj_n (adj_raw a)) v' = inr (u, ρ) -> pok M ρ = true.
Proof.
  intros Hv Hw.
  pose proof (proj2 (proj1 (scoped_spec N M (adj_raw a)) (adj_scoped a)) v' Hv) as H.
  rewrite result_wf_apply, Hw in H; cbn in H.
  pose proof (napply_payload _ _ _ (radj_ok_true (adj_raw a)) Hw) as [H1 H2]; cbn in H1, H2.
  unfold pok; rewrite H1, H2, H; reflexivity.
Qed.

Lemma pay_var_wf x Mρ s L0 {K L} (e : ext 0 L0 K L) v' w :
  pok Mρ x = true -> L0 = s + Mρ -> v_label v' <> None -> napply x v' = inl w ->
  wf_var L (up (s + ext_depth e) w) = true.
Proof.
  intros Hx HL Hv Hw; unfold pok in Hx; apply andb_true_iff in Hx as [Hx H3];
    apply andb_true_iff in Hx as [H1 H2].
  pose proof (proj1 (nscoped_spec Mρ x H1 H2) H3 v' Hv) as H; rewrite Hw in H; cbn in H.
  pose proof (ext_depth_L e) as HL'.
  apply (wf_eq L ((s + ext_depth e) + Mρ)); [lia|apply up_wf, H].
Qed.

Lemma pay_payload_ok x Mρ v' u ρ :
  pok Mρ x = true -> v_label v' <> None -> napply x v' = inr (u, ρ) -> pok Mρ ρ = true.
Proof.
  intros Hx Hv Hw; unfold pok in Hx; apply andb_true_iff in Hx as [Hx H3];
    apply andb_true_iff in Hx as [H1 H2].
  pose proof (proj1 (nscoped_spec Mρ x H1 H2) H3 v' Hv) as H; rewrite Hw in H; cbn in H.
  pose proof (napply_payload _ _ _ H1 Hw) as [H4 H5]; cbn in H4, H5.
  unfold pok; rewrite H4, H5, H; reflexivity.
Qed.

(** Strict-proposition wrappers used inside [apply]: from where a lookup
    found something, and the invariants, the scoping of the result. *)

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

Lemma W_pslot (m : raw payload) Mρ s L0 {K L} (e : ext 0 L0 K L) y i ent h l
  (HL : Is_true_s (Nat.eqb L0 (s + Mρ))) (Hx : Is_true_s (pok Mρ (NAdj m)))
  (H1 : Squash (get (label_key (Some y)) m = Some ent))
  (H2 : Squash (nth_error (e_targets ent) i = Some (Slots.Slot h l))) :
  Is_true_s (wf_var L (up (s + ext_depth e) (mk_rvar h (count m h - S l)))).
Proof.
  destruct H1 as [H1], H2 as [H2]; apply Is_true_s_intro.
  apply (pay_var_wf (NAdj m) Mρ s L0 e (mk_rvar (Some y) i));
    [apply Is_true_s_elim, Hx|apply Nat.eqb_eq, Is_true_s_elim, HL|discriminate|].
  unfold napply; cbn [nraw]; rewrite (loc_some _ _ _ _ _ H1 H2); reflexivity.
Qed.

Lemma W_ppass (m : raw payload) Mρ s L0 {K L} (e : ext 0 L0 K L) y i ent
  (HL : Is_true_s (Nat.eqb L0 (s + Mρ))) (Hx : Is_true_s (pok Mρ (NAdj m)))
  (H1 : Squash (get (label_key (Some y)) m = Some ent))
  (H2 : Squash (nth_error (e_targets ent) i = None)) :
  Is_true_s (wf_var L (up (s + ext_depth e)
                          (mk_rvar (Some y) (i - length (e_targets ent) + e_out ent)))).
Proof.
  destruct H1 as [H1], H2 as [H2]; apply Is_true_s_intro.
  apply (pay_var_wf (NAdj m) Mρ s L0 e (mk_rvar (Some y) i));
    [apply Is_true_s_elim, Hx|apply Nat.eqb_eq, Is_true_s_elim, HL|discriminate|].
  unfold napply; cbn [nraw]; apply (loc_pass _ _ _ _ H1 H2).
Qed.

Lemma W_pnone (m : raw payload) Mρ s L0 {K L} (e : ext 0 L0 K L) y i
  (HL : Is_true_s (Nat.eqb L0 (s + Mρ))) (Hx : Is_true_s (pok Mρ (NAdj m)))
  (H1 : Squash (get (label_key (Some y)) m = None)) :
  Is_true_s (wf_var L (up (s + ext_depth e) (mk_rvar (Some y) i))).
Proof.
  destruct H1 as [H1]; apply Is_true_s_intro.
  apply (pay_var_wf (NAdj m) Mρ s L0 e (mk_rvar (Some y) i));
    [apply Is_true_s_elim, Hx|apply Nat.eqb_eq, Is_true_s_elim, HL|discriminate|].
  unfold napply; cbn [nraw]; apply (loc_none _ _ _ H1).
Qed.

Lemma W_ppay (m : raw payload) Mρ y i ent u ρ (Hx : Is_true_s (pok Mρ (NAdj m)))
  (H1 : Squash (get (label_key (Some y)) m = Some ent))
  (H2 : Squash (nth_error (e_targets ent) i = Some (Slots.Bind (u, ρ)))) :
  Is_true_s (pok Mρ ρ).
Proof.
  destruct H1 as [H1], H2 as [H2]; apply Is_true_s_intro.
  apply (pay_payload_ok (NAdj m) Mρ (mk_rvar (Some y) i) u ρ);
    [apply Is_true_s_elim, Hx|discriminate|].
  unfold napply; cbn [nraw]; rewrite (loc_some _ _ _ _ _ H1 H2); reflexivity.
Qed.

(** At the top level. *)

Lemma rel_some (rv : rvar) y : v_label rv = Some y -> v_label rv = None -> forall d, d <= v_index rv.
Proof. congruence. Qed.

Lemma rel_ltb (rv : rvar) d : Nat.ltb (v_index rv) d = false -> v_label rv = None -> d <= v_index rv.
Proof. intros H _; apply Nat.ltb_ge, H. Qed.

Lemma W_tinner {N M K L} (e : ext N M K L) (rv : rvar) (Hl : v_label rv = None)
  (Hb : Nat.ltb (v_index rv) (ext_depth e) = true) : Is_true_s (wf_var L rv).
Proof. apply Is_true_s_intro, (inner_wf e); [exact Hl|apply Nat.ltb_lt, Hb]. Qed.

Lemma W_tdown {N M K L} (e : ext N M K L) (rv : rvar) (Hv : Is_true_s (wf_var K rv))
  (Hrel : v_label rv = None -> ext_depth e <= v_index rv) :
  wf_var N (down (ext_depth e) rv) = true.
Proof. apply down_wf; [apply Is_true_s_elim, Hv|exact Hrel]. Qed.

Lemma W_tHL {N M K L} (e : ext N M K L) : Is_true_s (Nat.eqb L (ext_depth e + M)).
Proof. apply Is_true_s_intro, Nat.eqb_eq, ext_depth_L. Qed.

Lemma W_tslot {N M K L} (a : adj T N M) (e : ext N M K L) v' (Hv' : wf_var N v' = true)
  ent h l
  (H1 : Squash (get (label_key (v_label v')) (nraw (radj_n (adj_raw a))) = Some ent))
  (H2 : Squash (nth_error (e_targets ent) (v_index v') = Some (Slots.Slot h l))) :
  Is_true_s (wf_var L (up (ext_depth e)
                          (mk_rvar h (count (nraw (radj_n (adj_raw a))) h - S l)))).
Proof.
  destruct H1 as [H1], H2 as [H2]; apply Is_true_s_intro.
  apply (top_var_wf a e v' _ Hv'); unfold napply.
  destruct v' as [h' i']; cbn [v_label v_index] in *; rewrite (loc_some _ _ _ _ _ H1 H2); reflexivity.
Qed.

Lemma W_tpass {N M K L} (a : adj T N M) (e : ext N M K L) v' (Hv' : wf_var N v' = true) ent
  (H1 : Squash (get (label_key (v_label v')) (nraw (radj_n (adj_raw a))) = Some ent))
  (H2 : Squash (nth_error (e_targets ent) (v_index v') = None)) :
  Is_true_s (wf_var L (up (ext_depth e)
                          (mk_rvar (v_label v') (v_index v' - length (e_targets ent) + e_out ent)))).
Proof.
  destruct H1 as [H1], H2 as [H2]; apply Is_true_s_intro.
  apply (top_var_wf a e v' _ Hv'); unfold napply.
  destruct v' as [h' i']; cbn [v_label v_index] in *; apply (loc_pass _ _ _ _ H1 H2).
Qed.

Lemma W_tnone {N M K L} (a : adj T N M) (e : ext N M K L) v' (Hv' : wf_var N v' = true)
  (H1 : Squash (get (label_key (v_label v')) (nraw (radj_n (adj_raw a))) = None)) :
  Is_true_s (wf_var L (up (ext_depth e) v')).
Proof.
  destruct H1 as [H1]; apply Is_true_s_intro.
  apply (top_var_wf a e v' _ Hv'); unfold napply.
  destruct v' as [h' i']; cbn [v_label v_index] in *; apply (loc_none _ _ _ H1).
Qed.

Lemma W_tpay {N M} (a : adj T N M) v' (Hv' : wf_var N v' = true) ent u ρ
  (H1 : Squash (get (label_key (v_label v')) (nraw (radj_n (adj_raw a))) = Some ent))
  (H2 : Squash (nth_error (e_targets ent) (v_index v') = Some (Slots.Bind (u, ρ)))) :
  Is_true_s (pok M ρ).
Proof.
  destruct H1 as [H1], H2 as [H2]; apply Is_true_s_intro.
  apply (top_payload_ok a v' u ρ Hv'); unfold napply.
  destruct v' as [h' i']; cbn [v_label v_index] in *; rewrite (loc_some _ _ _ _ _ H1 H2); reflexivity.
Qed.

End Facts.

(** ** Substitution for a syntax *)

Module Subst (Import S : SYNTAX).

Local Notation P := (term 0).
Local Notation payload := (P * nadj P)%type.

(** Payloads: [papply x Mρ s L0] is the morphism for a payload adjustment
    [x] in scope [Mρ], used under [s] outer binders, into scope [L0]. *)
Fixpoint papply (x : nadj P) (Mρ s L0 : nat) (HL : Is_true_s (Nat.eqb L0 (s + Mρ)))
  (Hx : Is_true_s (pok Mρ x)) {struct x} : morph 0 L0 :=
  fun K L e v =>
  match v_label (var_raw v) as o return v_label (var_raw v) = o -> term L with
  | None => fun Hl => tvar (mk_var (var_raw v) (W_pinner e (var_raw v) (var_ok v) Hl))
  | Some y => fun _ =>
      match x as x0 return Is_true_s (pok Mρ x0) -> term L with
      | NAdj m => fun Hx =>
          get_with (label_key (Some y)) m
            (fun ent H1 =>
               nth_with (v_index (var_raw v)) (e_targets ent)
                 (fun t =>
                    match t as t0
                          return Squash (nth_error (e_targets ent) (v_index (var_raw v)) = Some t0) ->
                                 term L with
                    | Slots.Slot h l => fun H2 =>
                        tvar (mk_var (up (s + ext_depth e) (mk_rvar h (count m h - S l)))
                                (W_pslot m Mρ s L0 e y _ ent h l HL Hx H1 H2))
                    | Slots.Bind p =>
                        match p as p0
                              return Squash (nth_error (e_targets ent) (v_index (var_raw v)) = Some (Slots.Bind p0)) ->
                                     term L with
                        | (u, ρ) => fun H2 =>
                            kleisli (papply ρ Mρ (s + ext_depth e) L (W_pHL Mρ s e HL)
                                       (W_ppay m Mρ y _ ent u ρ Hx H1 H2))
                                    ext_here u
                        end
                    end)
                 (fun H2 =>
                    tvar (mk_var (up (s + ext_depth e)
                                    (mk_rvar (Some y) (v_index (var_raw v) - length (e_targets ent) + e_out ent)))
                            (W_ppass m Mρ s L0 e y _ ent HL Hx H1 H2))))
            (fun H1 =>
               tvar (mk_var (up (s + ext_depth e) (mk_rvar (Some y) (v_index (var_raw v))))
                       (W_pnone m Mρ s L0 e y _ HL Hx H1)))
      end Hx
  end eq_refl.

(** Looking up a variable outside the binders crossed so far. *)
Definition look {N M K L} (a : adj P N M) (e : ext N M K L) (v' : rvar)
  (Hv' : wf_var N v' = true) : term L :=
  let m := nraw (radj_n (adj_raw a)) in
  get_with (label_key (v_label v')) m
    (fun ent H1 =>
       nth_with (v_index v') (e_targets ent)
         (fun t =>
            match t as t0
                  return Squash (nth_error (e_targets ent) (v_index v') = Some t0) -> term L with
            | Slots.Slot h l => fun H2 =>
                tvar (mk_var (up (ext_depth e) (mk_rvar h (count m h - S l)))
                        (W_tslot a e v' Hv' ent h l H1 H2))
            | Slots.Bind p =>
                match p as p0
                      return Squash (nth_error (e_targets ent) (v_index v') = Some (Slots.Bind p0)) -> term L with
                | (u, ρ) => fun H2 =>
                    kleisli (papply ρ M (ext_depth e) L (W_tHL e) (W_tpay a v' Hv' ent u ρ H1 H2))
                            ext_here u
                end
            end)
         (fun H2 =>
            tvar (mk_var (up (ext_depth e)
                            (mk_rvar (v_label v') (v_index v' - length (e_targets ent) + e_out ent)))
                    (W_tpass a e v' Hv' ent H1 H2))))
    (fun H1 => tvar (mk_var (up (ext_depth e) v') (W_tnone a e v' Hv' H1))).

(** The morphism of a scoped adjustment. *)
Definition apply {N M} (a : adj P N M) : morph N M :=
  fun K L e v =>
  let rv := var_raw v in
  match v_label rv as o return v_label rv = o -> term L with
  | None => fun Hl =>
      match Nat.ltb (v_index rv) (ext_depth e) as b
            return Nat.ltb (v_index rv) (ext_depth e) = b -> term L with
      | true => fun Hb => tvar (mk_var rv (W_tinner e rv Hl Hb))
      | false => fun Hb => look a e (down (ext_depth e) rv) (W_tdown e rv (var_ok v) (rel_ltb rv _ Hb))
      end eq_refl
  | Some y => fun Hl =>
      look a e (down (ext_depth e) rv) (W_tdown e rv (var_ok v) (fun H => rel_some rv y Hl H _))
  end eq_refl.

Definition subst {N M} (a : adj P N M) (t : term N) : term M := kleisli (apply a) ext_here t.


End Subst.
