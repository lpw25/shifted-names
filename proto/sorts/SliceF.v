(** * Prototype: System F terms, the type scope fixed, as a one-sorted
    syntax of the library (from [Slice])

    Build with
      rocq compile -R theories ShiftedNames -Q proto/sorts Proto proto/sorts/Desc.v
      rocq compile -R theories ShiftedNames -Q proto/sorts Proto proto/sorts/Slice.v
      rocq compile -R theories ShiftedNames -Q proto/sorts Proto proto/sorts/SliceF.v *)

From Stdlib Require Import Arith Lia StrictProp.
From ShiftedNames.Core Require Import Strict Label Var Scoped Indexed.
From ShiftedNames.Core Require Syntax.
From Proto Require Import Desc Slice.
Import Syntax (ext, ext_here, ext_under, ext_app, ext_mid, ext_left, ext_right, ext_depth, ext_var).

(** ** Renaming type variables *)

(** Shifting the bound variables at or past the cut [d] by [k]. *)
Definition shc (k d : nat) (w : rvar) : rvar :=
  match v_label w with
  | None => if Nat.ltb (v_index w) d then w else mk_rvar None (k + v_index w)
  | Some _ => w
  end.

Lemma shc_wf k G H d w : H = k + G -> wf_var (d + G) w = true -> wf_var (d + H) (shc k d w) = true.
Proof.
  intros ->; destruct w as [[x|] j]; unfold shc, wf_var; cbn [v_label v_index]; [reflexivity|].
  intros Hj; apply Nat.ltb_lt in Hj.
  destruct (Nat.ltb_spec j d); cbn [v_label v_index]; apply Nat.ltb_lt; lia.
Qed.

Lemma shc_comp a b x d w : x <= b -> shc a (d + x) (shc b d w) = shc (b + a) d w.
Proof.
  intros Hx; destruct w as [[y|] j]; unfold shc; cbn [v_label v_index]; [reflexivity|].
  destruct (Nat.ltb_spec j d); cbn [v_label v_index].
  - destruct (Nat.ltb_spec j (d + x)); [reflexivity|lia].
  - destruct (Nat.ltb_spec (b + j) (d + x)); [lia|]; f_equal; lia.
Qed.

Lemma shc_comp0 a b d w : shc a d (shc b d w) = shc (b + a) d w.
Proof. rewrite <- (shc_comp a b 0 d w) by lia; rewrite <- plus_n_O; reflexivity. Qed.

Lemma shc_0 d w : shc 0 d w = w.
Proof. destruct w as [[y|] j]; unfold shc; cbn [v_label v_index]; [reflexivity|]; destruct (j <? d); reflexivity. Qed.

(** The other sorts' scopes of a type witness: none used. *)
Definition Bh : vec 1 := pair 0 tt.

Lemma rnm_ok {G H} (ρ : nat -> rvar -> rvar) (Hρ : forall d w, wf_var (d + G) w = true -> wf_var (d + H) (ρ d w) = true)
    {O Ki Li} (e : vext 1 0 Bh G H O Ki Li) (v : var Ki) : Is_true_s (wf_var Li (ρ (vdepth e) (var_raw v))).
Proof.
  apply Is_true_s_intro; generalize (Is_true_s_elim (var_ok v)); generalize (var_raw v); intros w Hw.
  generalize (vdepth_K e) (vdepth_L e); generalize (vdepth e); intros d HK HL.
  rewrite HL; apply Hρ; rewrite <- HK; exact Hw.
Qed.

(** A renaming of type variables, as a morphism of the type sort. *)
Definition rnm {G H} (ρ : nat -> rvar -> rvar) (Hρ : forall d w, wf_var (d + G) w = true -> wf_var (d + H) (ρ d w) = true)
    : morph 1 0 (uncurry 1 ty) Bh G H :=
  fun O Ki Li e v => tyvar (mk_var (ρ (vdepth e) (var_raw v)) (rnm_ok ρ Hρ e v)).

Lemma vdepth_under {n i Bo Bi Mi O Ki Li} (e : vext n i Bo Bi Mi O Ki Li) : vdepth (vunder e) = S (vdepth e).
Proof. reflexivity. Qed.

Section Rename.

Context {G1 H1 G2 H2 G3 H3 : nat} (ρ1 ρ2 ρ3 : nat -> rvar -> rvar)
  (Hρ1 : forall d w, wf_var (d + G1) w = true -> wf_var (d + H1) (ρ1 d w) = true)
  (Hρ2 : forall d w, wf_var (d + G2) w = true -> wf_var (d + H2) (ρ2 d w) = true)
  (Hρ3 : forall d w, wf_var (d + G3) w = true -> wf_var (d + H3) (ρ3 d w) = true).

Lemma rnm_comp_ty Ka (A : ty Ka) : forall O1 O2 O3 Kb Kc
    (e1 : vext 1 0 Bh G1 H1 O1 Ka Kb) (e2 : vext 1 0 Bh G2 H2 O2 Kb Kc) (e3 : vext 1 0 Bh G3 H3 O3 Ka Kc),
  (forall d w, ρ2 (d + vdepth e2) (ρ1 (d + vdepth e1) w) = ρ3 (d + vdepth e3) w) ->
  kl_ty (rnm ρ2 Hρ2) e2 (kl_ty (rnm ρ1 Hρ1) e1 A) = kl_ty (rnm ρ3 Hρ3) e3 A.
Proof.
  induction A; intros O1 O2 O3 Kb Kc e1 e2 e3 H; cbn.
  - unfold rnm; f_equal; apply var_eq; cbn; exact (H 0 _).
  - f_equal; auto.
  - f_equal; apply (IHA _ _ _ _ _ (vunder e1) (vunder e2) (vunder e3)).
    intros d w; rewrite !vdepth_under, <- !plus_n_Sm; apply (H (S d)).
Qed.

Lemma rnm_comp_tmty Ka J (t : tm Ka J) : forall O1 O2 O3 Kb Kc
    (e1 : vext 1 0 Bh G1 H1 O1 Ka Kb) (e2 : vext 1 0 Bh G2 H2 O2 Kb Kc) (e3 : vext 1 0 Bh G3 H3 O3 Ka Kc),
  (forall d w, ρ2 (d + vdepth e2) (ρ1 (d + vdepth e1) w) = ρ3 (d + vdepth e3) w) ->
  kl_tmty (rnm ρ2 Hρ2) e2 (kl_tmty (rnm ρ1 Hρ1) e1 t) = kl_tmty (rnm ρ3 Hρ3) e3 t.
Proof.
  induction t; intros O1 O2 O3 Kb Kc e1 e2 e3 H; cbn; f_equal; auto; try (apply rnm_comp_ty; exact H).
  apply (IHt _ _ _ _ _ (vunder e1) (vunder e2) (vunder e3)).
  intros d w; rewrite !vdepth_under, <- !plus_n_Sm; apply (H (S d)).
Qed.

Lemma rnm_id_ty Ka (A : ty Ka) : forall O (e1 : vext 1 0 Bh G1 H1 O Ka Ka),
  (forall d w, ρ1 (d + vdepth e1) w = w) -> kl_ty (rnm ρ1 Hρ1) e1 A = A.
Proof.
  induction A; intros O e1 H; cbn.
  - unfold rnm; f_equal; apply var_eq; cbn; exact (H 0 _).
  - f_equal; auto.
  - f_equal; apply (IHA _ (vunder e1)).
    intros d w; rewrite !vdepth_under, <- !plus_n_Sm; apply (H (S d)).
Qed.

Lemma rnm_id_tmty Ka J (t : tm Ka J) : forall O (e1 : vext 1 0 Bh G1 H1 O Ka Ka),
  (forall d w, ρ1 (d + vdepth e1) w = w) -> kl_tmty (rnm ρ1 Hρ1) e1 t = t.
Proof.
  induction t; intros O e1 H; cbn; f_equal; auto; try (apply rnm_id_ty; exact H).
  apply (IHt _ (vunder e1)).
  intros d w; rewrite !vdepth_under, <- !plus_n_Sm; apply (H (S d)).
Qed.

End Rename.

(** Weakening terms by [c] type variables. *)
Definition shN (c : nat) {G K} (u : tm G K) : tm (c + G) K :=
  kl_tmty (rnm (shc c) (fun d w => shc_wf c G (c + G) d w eq_refl)) (vhere (Bo := Bh)) u.

(** ** Terms as a slice *)

Notation tmP := (uncurry 2 tm).

(** A step past a type binder shifts the types; past a term binder
    (which a slice of the term sort does not cross) nothing. *)
Definition stepF (t L : nat) (O : vec 2) : tmP (upd 2 1 L O) -> tmP (upd 2 1 L (upd 2 t (S (get 2 t O)) O)) :=
  match t return tmP (upd 2 1 L O) -> tmP (upd 2 1 L (upd 2 t (S (get 2 t O)) O)) with
  | 0 => fun u => shN 1 u
  | S _ => fun u => u
  end.

Lemma stepF_var t L O (w : var L) : stepF t L O (tmvar w) = tmvar w.
Proof. destruct t; reflexivity. Qed.

Notation wkF e L u := (@wk 2 1 tmP stepF _ _ _ _ _ _ e L u).
Notation liftF Bo := (@lift 2 1 tmP stepF Bo).

(** The type binders crossed. *)
Fixpoint tcnt {Bo Bi Mi O Ki Li} (e : vext 2 1 Bo Bi Mi O Ki Li) : nat :=
  match e with
  | vhere => 0
  | vunder e => tcnt e
  | vother t e => match t with 0 => S (tcnt e) | S _ => tcnt e end
  end.

Lemma tcnt_first {Bo Bi Mi O Ki Li} (e : vext 2 1 Bo Bi Mi O Ki Li) : first O = tcnt e + first Bo.
Proof. induction e; cbn; [reflexivity|assumption|destruct t; cbn; lia]. Qed.

Lemma tcnt_etv {Bo N M K L} (e : ext N M K L) : tcnt (etv (n := 2) (i := 1) (Bo := Bo) e) = 0.
Proof. induction e; cbn; auto. Qed.

Lemma tcnt_wf {Bo Bi Mi O Ki Li} (e : vext 2 1 Bo Bi Mi O Ki Li) d w :
  wf_var (d + first Bo) w = true -> wf_var (d + first O) (shc (tcnt e) d w) = true.
Proof. apply shc_wf, tcnt_first. Qed.

(** Weakening along a witness is shifting by its type binders. *)
Lemma wkF_shift {Bo Bi Mi O Ki Li} (e : vext 2 1 Bo Bi Mi O Ki Li) {L} (y : tm (first Bo) L) :
  wkF e L y = kl_tmty (rnm (shc (tcnt e)) (tcnt_wf e)) (vhere (Bo := Bh)) y.
Proof.
  induction e; cbn [wk tcnt].
  - symmetry; apply rnm_id_tmty; intros; apply shc_0.
  - rewrite IHe; reflexivity.
  - destruct t; cbn [stepF]; rewrite IHe; [|reflexivity].
    unfold shN; apply rnm_comp_tmty; intros d w; cbn [vdepth vext_i ext_depth].
    rewrite <- !plus_n_O, shc_comp0, Nat.add_1_r; reflexivity.
Qed.

(** The one commutation lemma: renaming types by a shift commutes with
    substituting terms (along lifted morphisms), between slices whose
    type scopes differ by [c]. *)
Section Commute.

Context {G1 : nat} (r1 r2 : vec 1) (c k Gs Gt : nat) (Hk : forall d w, wf_var (d + Gs) w = true -> wf_var (d + Gt) (shc k d w) = true).
Context {Mi Pi : nat} (g : Syntax.morph (fun K => tm G1 K) Mi Pi).

Lemma kl_commute N1 K (u : tm N1 K) : forall s1 O2 L
    (e1 : vext 2 1 (pair G1 r1) Mi Pi (pair N1 s1) K L) (e2 : vext 2 1 (pair (c + G1) r2) Mi Pi O2 K L)
    (eh : vext 1 0 Bh Gs Gt Bh N1 (first O2)),
  vext_i e1 = vext_i e2 -> vdepth eh = tcnt e1 -> tcnt e1 + k = tcnt e2 + c ->
  kl_tmty (rnm (shc k) Hk) eh (kl_tm (liftF (pair G1 r1) g) e1 u)
  = kl_tm (liftF (pair (c + G1) r2) (Syntax.mmap (fun K u => shN c u) g)) e2 (kl_tmty (rnm (shc k) Hk) eh u).
Proof.
  induction u; intros s1 O2 L e1 e2 eh Hi Hd Hc; cbn [kl_tm kl_tmty].
  - unfold lift, Syntax.mmap; rewrite Hi, (wkF_shift e1), (wkF_shift e2); unfold shN.
    set (x := g K L (vext_i e2) v).
    assert (H3 : forall d w, wf_var (d + G1) w = true -> wf_var (d + first O2) (shc (c + tcnt e2) d w) = true)
      by (intros d w; apply shc_wf; rewrite (tcnt_first e2); cbn; lia).
    transitivity (kl_tmty (rnm (shc (c + tcnt e2)) H3) (vhere (Bo := Bh)) x).
    + apply rnm_comp_tmty; intros d w; change (first (pair N s1)) with N; rewrite Hd; cbn [vdepth vext_i ext_depth].
      rewrite <- plus_n_O, shc_comp by lia; f_equal; lia.
    + symmetry; apply rnm_comp_tmty; intros d w; cbn [vdepth vext_i ext_depth].
      rewrite <- !plus_n_O, shc_comp0; reflexivity.
  - f_equal; apply (IHu _ _ _ (vunder e1) (vunder e2) eh); [cbn [vext_i]; rewrite Hi; reflexivity|exact Hd|exact Hc].
  - f_equal; [apply IHu1|apply IHu2]; assumption.
  - f_equal; apply (IHu _ _ _ (vother 0 e1) (vother 0 e2) (vunder eh)); [exact Hi|exact (f_equal S Hd)|cbn [tcnt]; lia].
  - f_equal; apply IHu; assumption.
Qed.

End Commute.

(** ** The slice's hypotheses *)

Lemma wkF_kl {Bo} Mi Pi (g : Syntax.morph (fun K => tmP (upd 2 1 K Bo)) Mi Pi) O K L (ev : vext 2 1 Bo Mi Pi O K L)
    (u : tmP (upd 2 1 K Bo)) :
  wkF ev L (tm_k _ _ _ (liftF Bo g) _ _ _ (etv (vext_i ev)) u) = tm_k _ _ _ (liftF Bo g) _ _ _ ev (wkF ev K u).
Proof.
  destruct Bo as [G1 r1]; cbn [tm_k]; cbn in u, g.
  rewrite (wkF_shift ev), (wkF_shift ev).
  etransitivity.
  { apply (kl_commute r1 r1 0 (tcnt ev) G1 (first O) (tcnt_wf ev) g _ _ u _ _ _ (etv (vext_i ev)) ev vhere).
    - apply vext_i_etv.
    - symmetry; apply tcnt_etv.
    - rewrite tcnt_etv, <- plus_n_O; reflexivity. }
  refine (kl_tm_ext _ _ _ O K L ev _); intros O' Ki Li e v; unfold lift, Syntax.mmap; f_equal.
  unfold shN; apply rnm_id_tmty; intros; apply shc_0.
Qed.

Section Instance.

Context (G : nat).

Definition BoF : vec 2 := pair G (pair 0 tt).

Definition kl_tmF {N M} (f : Syntax.morph (tm G) N M) {K L} (e : ext N M K L) (t : tm G K) : tm G L :=
  kl1 tmP tm_k stepF BoF f e t.

Definition tmF_laws := @slice_laws 2 1 tmP (fun O K v => @tmvar (first O) K v) tm_k stepF BoF tm_laws stepF_var (@wkF_kl BoF).

End Instance.

(** ** Going under a type binder

    A term substitution under a type binder is the next slice's, along
    the morphism whose results are weakened ([shN 1], a map of syntaxes:
    it commutes with substitution). *)

Lemma kl_tmF_tlam G {N M} (f : Syntax.morph (tm G) N M) {K L} (e : ext N M K L) (b : tm (S G) K) :
  kl_tmF G f e (tlam b) = tlam (kl_tmF (S G) (Syntax.mmap (fun K u => shN 1 u) f) e b).
Proof.
  unfold kl_tmF, kl1; cbn [tm_k kl_tm]; f_equal.
  assert (Hk : forall d w, wf_var (d + G) w = true -> wf_var (d + G) (shc 0 d w) = true)
    by (intros d w; apply shc_wf; reflexivity).
  pose proof (kl_commute (pair 0 tt) (pair 0 tt) 1 0 G G Hk f (S G) K b (pair 0 tt) (BoF (S G)) L
                (vother 0 (etv (Bo := BoF G) e)) (etv (Bo := BoF (S G)) e) (vunder vhere)) as E.
  rewrite !rnm_id_tmty in E by (intros; apply shc_0).
  apply E.
  - cbn [vext_i]; rewrite !vext_i_etv; reflexivity.
  - cbn [tcnt]; rewrite tcnt_etv; reflexivity.
  - cbn [tcnt]; rewrite !tcnt_etv; reflexivity.
Qed.

Lemma kl_tmF_shN G {N M} (f : Syntax.morph (tm G) N M) {K L} (e : ext N M K L) (u : tm G K) :
  shN 1 (kl_tmF G f e u) = kl_tmF (S G) (Syntax.mmap (fun K u => shN 1 u) f) e (shN 1 u).
Proof.
  unfold kl_tmF, kl1; cbn [tm_k].
  apply (kl_commute (pair 0 tt) (pair 0 tt) 1 1 G (S G) (fun d w => shc_wf 1 G (S G) d w eq_refl) f G K u
           (pair 0 tt) (BoF (S G)) L (etv (Bo := BoF G) e) (etv (Bo := BoF (S G)) e) vhere).
  - rewrite !vext_i_etv; reflexivity.
  - rewrite tcnt_etv; reflexivity.
  - rewrite !tcnt_etv; reflexivity.
Qed.
