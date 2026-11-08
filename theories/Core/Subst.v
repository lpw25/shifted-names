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

(** Payload adjustments in scope [M]. *)

(** Where a lookup in a normal adjustment ends up. *)

Lemma loc_some (m : raw payload) h ent i t :
  normal m = true -> get (label_key h) m = Some ent -> Braun.nth i (e_tree ent) = Some t ->
  Slots.apply m (mk_rvar h i) = resolve m t.
Proof.
  intros Hm H1 H2; rewrite (Braun.nth_to_list _ _ (normal_balanced _ _ _ Hm H1)) in H2.
  fold (e_targets ent) in H2; unfold Slots.apply, find; cbn; rewrite H1; cbn; rewrite H2; reflexivity.
Qed.

Lemma loc_pass (m : raw payload) h ent i :
  normal m = true -> get (label_key h) m = Some ent -> Braun.nth i (e_tree ent) = None ->
  Slots.apply m (mk_rvar h i) = inl (mk_rvar h (i - Braun.size (e_tree ent) + e_out ent)).
Proof.
  intros Hm H1 H2; rewrite (Braun.nth_to_list _ _ (normal_balanced _ _ _ Hm H1)) in H2.
  fold (e_targets ent) in H2; unfold Slots.apply, count, find; cbn; rewrite H1; cbn; rewrite H2.
  unfold e_targets; rewrite Braun.to_list_length; reflexivity.
Qed.

Lemma pok_normal M x : pok M x = true -> normal (nraw x) = true.
Proof. unfold pok; rewrite !andb_true_iff; intros [[H _] _]; apply nnormal_normal, H. Qed.

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
  (H2 : Squash (Braun.nth i (e_tree ent) = Some (Slots.Slot h l))) :
  Is_true_s (wf_var L (up (s + ext_depth e) (mk_rvar h (count m h - S l)))).
Proof.
  pose proof (pok_normal _ _ (Is_true_s_elim Hx)) as HM; cbn [nraw] in HM.
  destruct H1 as [H1], H2 as [H2]; apply Is_true_s_intro.
  apply (pay_var_wf (NAdj m) Mρ s L0 e (mk_rvar (Some y) i));
    [apply Is_true_s_elim, Hx|apply Nat.eqb_eq, Is_true_s_elim, HL|discriminate|].
  unfold napply; cbn [nraw]; rewrite (loc_some _ _ _ _ _ HM H1 H2); reflexivity.
Qed.

Lemma W_ppass (m : raw payload) Mρ s L0 {K L} (e : ext 0 L0 K L) y i ent
  (HL : Is_true_s (Nat.eqb L0 (s + Mρ))) (Hx : Is_true_s (pok Mρ (NAdj m)))
  (H1 : Squash (get (label_key (Some y)) m = Some ent))
  (H2 : Squash (Braun.nth i (e_tree ent) = None)) :
  Is_true_s (wf_var L (up (s + ext_depth e)
                          (mk_rvar (Some y) (i - Braun.size (e_tree ent) + e_out ent)))).
Proof.
  pose proof (pok_normal _ _ (Is_true_s_elim Hx)) as HM; cbn [nraw] in HM.
  destruct H1 as [H1], H2 as [H2]; apply Is_true_s_intro.
  apply (pay_var_wf (NAdj m) Mρ s L0 e (mk_rvar (Some y) i));
    [apply Is_true_s_elim, Hx|apply Nat.eqb_eq, Is_true_s_elim, HL|discriminate|].
  unfold napply; cbn [nraw]; apply (loc_pass _ _ _ _ HM H1 H2).
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
  (H2 : Squash (Braun.nth i (e_tree ent) = Some (Slots.Bind (u, ρ)))) :
  Is_true_s (pok Mρ ρ).
Proof.
  pose proof (pok_normal _ _ (Is_true_s_elim Hx)) as HM; cbn [nraw] in HM.
  destruct H1 as [H1], H2 as [H2]; apply Is_true_s_intro.
  apply (pay_payload_ok (NAdj m) Mρ (mk_rvar (Some y) i) u ρ);
    [apply Is_true_s_elim, Hx|discriminate|].
  unfold napply; cbn [nraw]; rewrite (loc_some _ _ _ _ _ HM H1 H2); reflexivity.
Qed.

(** At the top level. *)

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

Lemma W_tslot {N M K L} (a : adj T N M) (e : ext N M K L) v' (Hv' : wf_var N v' = true)
  ent h l
  (H1 : Squash (get (label_key (v_label v')) (nraw (radj_n (adj_raw a))) = Some ent))
  (H2 : Squash (Braun.nth (v_index v') (e_tree ent) = Some (Slots.Slot h l))) :
  Is_true_s (wf_var L (up (ext_depth e)
                          (mk_rvar h (count (nraw (radj_n (adj_raw a))) h - S l)))).
Proof.
  pose proof (nnormal_normal _ (radj_ok_true (adj_raw a))) as HM.
  destruct H1 as [H1], H2 as [H2]; apply Is_true_s_intro.
  apply (top_var_wf a e v' _ Hv'); unfold napply.
  destruct v' as [h' i']; cbn [v_label v_index] in *; rewrite (loc_some _ _ _ _ _ HM H1 H2); reflexivity.
Qed.

Lemma W_tpass {N M K L} (a : adj T N M) (e : ext N M K L) v' (Hv' : wf_var N v' = true) ent
  (H1 : Squash (get (label_key (v_label v')) (nraw (radj_n (adj_raw a))) = Some ent))
  (H2 : Squash (Braun.nth (v_index v') (e_tree ent) = None)) :
  Is_true_s (wf_var L (up (ext_depth e)
                          (mk_rvar (v_label v') (v_index v' - Braun.size (e_tree ent) + e_out ent)))).
Proof.
  pose proof (nnormal_normal _ (radj_ok_true (adj_raw a))) as HM.
  destruct H1 as [H1], H2 as [H2]; apply Is_true_s_intro.
  apply (top_var_wf a e v' _ Hv'); unfold napply.
  destruct v' as [h' i']; cbn [v_label v_index] in *; apply (loc_pass _ _ _ _ HM H1 H2).
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
  (H2 : Squash (Braun.nth (v_index v') (e_tree ent) = Some (Slots.Bind (u, ρ)))) :
  Is_true_s (pok M ρ).
Proof.
  pose proof (nnormal_normal _ (radj_ok_true (adj_raw a))) as HM.
  destruct H1 as [H1], H2 as [H2]; apply Is_true_s_intro.
  apply (top_payload_ok a v' u ρ Hv'); unfold napply.
  destruct v' as [h' i']; cbn [v_label v_index] in *; rewrite (loc_some _ _ _ _ _ HM H1 H2); reflexivity.
Qed.

(** ** The raw lookup of lifts, compositions and payloads *)

Lemma napply_rlift (a : radj T) h v :
  napply (radj_n (rlift h a)) v
  = if rvar_eqb v (mk_rvar h 0) then inl v
    else match napply (radj_n a) (unshift_rvar (mk_rvar h 0) v) with
         | inl w => inl (shift_rvar (mk_rvar h 0) w)
         | inr p => inr (fst p, pshift h (snd p))
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
    | inr p => inr (fst p, prestrict (ncompose (radj_n a) (snd p)))
    end.
Proof. apply napply_ncompose; apply radj_ok_true. Qed.

Lemma napply_depth (x : nadj T) v u ρ : napply x v = inr (u, ρ) -> ndepth ρ < ndepth x.
Proof.
  destruct x as [m]; unfold napply; cbn [nraw]; intros H.
  apply (ndepth_binds m (u, ρ)), (binds_in_apply m v), H.
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
               nth_with (v_index (var_raw v)) (e_tree ent)
                 (fun t =>
                    match t as t0
                          return Squash (Braun.nth (v_index (var_raw v)) (e_tree ent) = Some t0) ->
                                 term L with
                    | Slots.Slot h l => fun H2 =>
                        tvar (mk_var (up (s + ext_depth e) (mk_rvar h (count m h - S l)))
                                (W_pslot m Mρ s L0 e y _ ent h l HL Hx H1 H2))
                    | Slots.Bind p =>
                        match p as p0
                              return Squash (Braun.nth (v_index (var_raw v)) (e_tree ent) = Some (Slots.Bind p0)) ->
                                     term L with
                        | (u, ρ) => fun H2 =>
                            kleisli (papply ρ Mρ (s + ext_depth e) L (W_pHL Mρ s e HL)
                                       (W_ppay m Mρ y _ ent u ρ Hx H1 H2))
                                    ext_here u
                        end
                    end)
                 (fun H2 =>
                    tvar (mk_var (up (s + ext_depth e)
                                    (mk_rvar (Some y) (v_index (var_raw v) - Braun.size (e_tree ent) + e_out ent)))
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
       nth_with (v_index v') (e_tree ent)
         (fun t =>
            match t as t0
                  return Squash (Braun.nth (v_index v') (e_tree ent) = Some t0) -> term L with
            | Slots.Slot h l => fun H2 =>
                tvar (mk_var (up (ext_depth e) (mk_rvar h (count m h - S l)))
                        (W_tslot a e v' Hv' ent h l H1 H2))
            | Slots.Bind p =>
                match p as p0
                      return Squash (Braun.nth (v_index v') (e_tree ent) = Some (Slots.Bind p0)) -> term L with
                | (u, ρ) => fun H2 =>
                    kleisli (papply ρ M (ext_depth e) L (W_tHL e) (W_tpay a v' Hv' ent u ρ H1 H2))
                            ext_here u
                end
            end)
         (fun H2 =>
            tvar (mk_var (up (ext_depth e)
                            (mk_rvar (v_label v') (v_index v' - Braun.size (e_tree ent) + e_out ent)))
                    (W_tpass a e v' Hv' ent H1 H2))))
    (fun H1 => tvar (mk_var (up (ext_depth e) v') (W_tnone a e v' Hv' H1))).

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

Definition subst {N M} (a : adj P N M) (t : term N) : term M := kleisli (apply a) ext_here t.


(** ** What [apply] computes *)

Section Char.

Lemma option_cases {X} (o : option X) : (exists x, o = Some x) \/ o = None.
Proof. destruct o; eauto. Qed.

Lemma look_var {N M K L} (a : adj P N M) (e : ext N M K L) v' Hv' w H :
  napply (radj_n (adj_raw a)) v' = inl w -> look a e v' Hv' = tvar (mk_var (up (ext_depth e) w) H).
Proof.
  pose proof (nnormal_normal _ (radj_ok_true (adj_raw a))) as HM.
  unfold look, napply; cbv zeta; set (m := nraw (radj_n (adj_raw a))) in *.
  destruct v' as [h i]; cbn [v_label v_index] in *.
  destruct (option_cases (get (label_key h) m)) as [[ent E1]|E1].
  - rewrite (get_with_some _ _ _ _ ent E1); cbv beta.
    destruct (option_cases (Braun.nth i (e_tree ent))) as [[t E2]|E2].
    + rewrite (nth_with_some _ _ _ _ t E2).
      rewrite (loc_some _ _ _ _ _ HM E1 E2); destruct t as [h' l|[u ρ]]; cbn; [|discriminate].
      intros [= <-]; f_equal; apply var_eq; reflexivity.
    + rewrite (nth_with_none _ _ _ _ E2), (loc_pass _ _ _ _ HM E1 E2).
      intros [= <-]; f_equal; apply var_eq; reflexivity.
  - rewrite (get_with_none _ _ _ _ E1), (loc_none _ _ _ E1).
    intros [= <-]; f_equal; apply var_eq; reflexivity.
Qed.

Lemma look_pay {N M K L} (a : adj P N M) (e : ext N M K L) v' Hv' u ρ HL Hρ :
  napply (radj_n (adj_raw a)) v' = inr (u, ρ) ->
  look a e v' Hv' = kleisli (papply ρ M (ext_depth e) L HL Hρ) ext_here u.
Proof.
  pose proof (nnormal_normal _ (radj_ok_true (adj_raw a))) as HM.
  unfold look, napply; cbv zeta; set (m := nraw (radj_n (adj_raw a))) in *.
  destruct v' as [h i]; cbn [v_label v_index] in *.
  destruct (option_cases (get (label_key h) m)) as [[ent E1]|E1].
  - rewrite (get_with_some _ _ _ _ ent E1); cbv beta.
    destruct (option_cases (Braun.nth i (e_tree ent))) as [[t E2]|E2].
    + rewrite (nth_with_some _ _ _ _ t E2).
      rewrite (loc_some _ _ _ _ _ HM E1 E2); destruct t as [h' l|[u' ρ']]; cbn; [discriminate|].
      intros [= <- <-]; reflexivity.
    + rewrite (loc_pass _ _ _ _ HM E1 E2); discriminate.
  - rewrite (loc_none _ _ _ E1); discriminate.
Qed.

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

Lemma papply_inner x Mρ s L0 HL Hx {K L} (e : ext 0 L0 K L) v H :
  v_label (var_raw v) = None -> papply x Mρ s L0 HL Hx K L e v = tvar (mk_var (var_raw v) H).
Proof.
  destruct v as [[[y|] i] Hv]; cbn [var_raw v_label v_index]; intros Hl; [discriminate|].
  destruct x as [m]; reflexivity.
Qed.

Lemma papply_var x Mρ s L0 HL Hx {K L} (e : ext 0 L0 K L) v w H :
  v_label (var_raw v) <> None -> napply x (var_raw v) = inl w ->
  papply x Mρ s L0 HL Hx K L e v = tvar (mk_var (up (s + ext_depth e) w) H).
Proof.
  pose proof (pok_normal _ _ (Is_true_s_elim Hx)) as HM.
  destruct v as [[[y|] i] Hv]; cbn [var_raw v_label v_index]; intros Hl; [|contradiction].
  destruct x as [m]; cbn [nraw] in HM; unfold napply; cbn [papply nraw var_raw v_label v_index].
  destruct (option_cases (get (label_key (Some y)) m)) as [[ent E1]|E1].
  - rewrite (get_with_some _ _ _ _ ent E1); cbv beta.
    destruct (option_cases (Braun.nth i (e_tree ent))) as [[t E2]|E2].
    + rewrite (nth_with_some _ _ _ _ t E2).
      rewrite (loc_some _ _ _ _ _ HM E1 E2); destruct t as [h' l|[u ρ]]; cbn; [|discriminate].
      intros [= <-]; f_equal; apply var_eq; reflexivity.
    + rewrite (nth_with_none _ _ _ _ E2), (loc_pass _ _ _ _ HM E1 E2).
      intros [= <-]; f_equal; apply var_eq; reflexivity.
  - rewrite (get_with_none _ _ _ _ E1), (loc_none _ _ _ E1).
    intros [= <-]; f_equal; apply var_eq; reflexivity.
Qed.

Lemma papply_pay x Mρ s L0 HL Hx {K L} (e : ext 0 L0 K L) v u ρ HL' Hρ :
  v_label (var_raw v) <> None -> napply x (var_raw v) = inr (u, ρ) ->
  papply x Mρ s L0 HL Hx K L e v = kleisli (papply ρ Mρ (s + ext_depth e) L HL' Hρ) ext_here u.
Proof.
  pose proof (pok_normal _ _ (Is_true_s_elim Hx)) as HM.
  destruct v as [[[y|] i] Hv]; cbn [var_raw v_label v_index]; intros Hl; [|contradiction].
  destruct x as [m]; cbn [nraw] in HM; unfold napply; cbn [papply nraw var_raw v_label v_index].
  destruct (option_cases (get (label_key (Some y)) m)) as [[ent E1]|E1].
  - rewrite (get_with_some _ _ _ _ ent E1); cbv beta.
    destruct (option_cases (Braun.nth i (e_tree ent))) as [[t E2]|E2].
    + rewrite (nth_with_some _ _ _ _ t E2).
      rewrite (loc_some _ _ _ _ _ HM E1 E2); destruct t as [h' l|[u' ρ']]; cbn; [discriminate|].
      intros [= <- <-]; reflexivity.
    + rewrite (loc_pass _ _ _ _ HM E1 E2); discriminate.
  - rewrite (loc_none _ _ _ E1); discriminate.
Qed.

End Char.

(** ** Going under a binder is lifting *)

Section Lift.

Ltac sq := apply Is_true_s_intro.

Lemma papply_s_eq ρ M L s s' (E : s = s') HL HL' Hx :
  papply ρ M s L HL Hx = papply ρ M s' L HL' Hx.
Proof. subst; reflexivity. Qed.

Lemma papply_pshift_depth n :
  forall ρ, ndepth ρ <= n -> forall M d L HL HL' Hx Hx' K L' (e : ext 0 L K L') v,
  papply ρ M (S d) L HL Hx K L' e v = papply (pshift None ρ) (S M) d L HL' Hx' K L' e v.
Proof.
  induction n as [|n IH]; intros ρ Hd M d L HL HL' Hx Hx' K L' e v;
    [pose proof (ndepth_pos ρ); lia|].
  pose proof (Is_true_s_elim Hx) as Hx0; pose proof (Is_true_s_elim Hx') as Hx0'.
  assert (Hn : normal (nraw ρ) = true).
  { unfold pok in Hx0; apply andb_true_iff in Hx0 as [Hx0 _]; apply andb_true_iff in Hx0 as [Hx0 _].
    apply (nnormal_normal _ Hx0). }
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
  - pose proof (napply_depth _ _ _ _ E) as Hdep.
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
         { cbn [adj_raw lift]; rewrite napply_rlift.
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
    { cbn [adj_raw lift]; rewrite napply_rlift, Hd; fold d.
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
      apply (papply_pshift_depth (ndepth ρ)); lia.
  - assert (Hr1 : v_label (var_raw v) = None -> ext_depth e1 <= v_index (var_raw v))
      by (intros; rewrite Hd; try lia; congruence).
    assert (Hr2 : v_label (var_raw v) = None -> ext_depth e <= v_index (var_raw v))
      by (intros; unfold d in *; try lia; congruence).
    assert (Hdn : napply (radj_n (adj_raw (lift a))) (down (ext_depth e) (var_raw v))
                  = match napply (radj_n (adj_raw a)) (down (ext_depth e1) (var_raw v)) with
                    | inl w => inl (shift_rvar (mk_rvar None 0) w)
                    | inr p => inr (fst p, pshift None (snd p))
                    end).
    { cbn [adj_raw lift]; rewrite napply_rlift, Hd; fold d.
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
      apply (papply_pshift_depth (ndepth ρ)); lia.
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
  unfold subst; rewrite (kleisli_ext _ _ _ unit_m (fun K L e v => apply_identity e v)).
  apply kleisli_unit.
Qed.

(** ** Composition *)

Lemma kleisli_rebase_here {N M K L} (f : morph N M) (e : ext N M K L) (t : term K) :
  kleisli f e t = kleisli (rebase_m e f) ext_here t.
Proof. exact (kleisli_rebase _ _ f _ _ _ _ e ext_here t). Qed.

Lemma kleisli_comp_here {N M P'} (g : morph M P') (f : morph N M) (t : term N) :
  kleisli g ext_here (kleisli f ext_here t) = kleisli (comp_m g f) ext_here t.
Proof. symmetry; exact (kleisli_assoc _ _ _ g f _ _ ext_here t). Qed.

Lemma pok_prestrict_compose {M P'} (a : adj P M P') ρ :
  pok M ρ = true -> nnormal (prestrict (ncompose (radj_n (adj_raw a)) ρ)) = true.
Proof.
  intros H; unfold pok in H; apply andb_true_iff in H as [H _]; apply andb_true_iff in H as [H _].
  apply nnormal_prestrict, nnormal_ncompose; [apply radj_ok_true|exact H].
Qed.

Lemma napply_pcompose {M P'} (a : adj P M P') ρ v :
  pok M ρ = true -> v_label v <> None ->
  napply (prestrict (ncompose (radj_n (adj_raw a)) ρ)) v
  = match napply ρ v with
    | inl w => napply (radj_n (adj_raw a)) w
    | inr p => inr (fst p, prestrict (ncompose (radj_n (adj_raw a)) (snd p)))
    end.
Proof.
  intros H Hv; unfold pok in H; apply andb_true_iff in H as [H _]; apply andb_true_iff in H as [H _].
  rewrite napply_prestrict by (try apply nnormal_ncompose; auto using radj_ok_true).
  apply napply_ncompose; [apply radj_ok_true|exact H].
Qed.

Ltac sqa := apply Is_true_s_intro.

Lemma papply_compose_depth n :
  forall ρ, ndepth ρ <= n ->
  forall M P' Mid L (a : adj P M P') (e' : ext M P' Mid L) HL1 Hx1 HL2 Hx2 (u : P),
  kleisli (apply a) e' (kleisli (papply ρ M (ext_depth e') Mid HL1 Hx1) ext_here u)
  = kleisli (papply (prestrict (ncompose (radj_n (adj_raw a)) ρ)) P' (ext_depth e') L HL2 Hx2)
            ext_here u.
Proof.
  induction n as [|n IH]; intros ρ Hdep M P' Mid L a e' HL1 Hx1 HL2 Hx2 u;
    [pose proof (ndepth_pos ρ); lia|].
  set (d := ext_depth e') in *.
  set (ρ'' := prestrict (ncompose (radj_n (adj_raw a)) ρ)) in *.
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
  pose proof (napply_pcompose a ρ (var_raw w) Hx1b Hl) as Hc; fold ρ'' in Hc.
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
    pose proof (napply_depth _ _ _ _ E) as Hd3.
    assert (Hρ3 : pok M ρ3 = true) by (apply (pay_payload_ok ρ M (var_raw w) u3); auto).
    assert (Hρ3' : pok P' (prestrict (ncompose (radj_n (adj_raw a)) ρ3)) = true).
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
    rewrite (papply_s_eq (prestrict (ncompose (radj_n (adj_raw a)) ρ3)) P' L2 (d + ext_depth e2) (ext_depth e3) ltac:(lia) HL3 HL4).
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
  all: pose proof (napply_rcompose (adj_raw a) (adj_raw b) (down d (var_raw v))) as Hc.
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
         by (pose proof (proj2 (proj1 (scoped_spec N M (adj_raw b)) (adj_scoped b)) _ Hv') as X;
             rewrite result_wf_apply, E in X; exact X);
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
       assert (Hρ' : pok P' (prestrict (ncompose (radj_n (adj_raw a)) ρ)) = true)
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
  all: apply (papply_compose_depth (ndepth ρ)); lia.
Qed.

Theorem subst_compose {N M P'} (a : adj P M P') (b : adj P N M) (t : term N) :
  subst a (subst b t) = subst (compose a b) t.
Proof.
  unfold subst; rewrite kleisli_comp_here.
  apply kleisli_ext; intros; apply apply_compose.
Qed.

End Subst.
