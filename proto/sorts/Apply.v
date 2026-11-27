(** * Prototype: the morphism of an adjustment, for one sort of several

    [apply a] for a sort of a family: an adjustment [a] of that sort, whose
    payloads are terms of the family at the other sorts' base scopes, gives
    a morphism along any descent.  It is the library's [gapply] with three
    changes:
    - the depth is that of the sort's own [ext] in the descent ([main]);
    - a variable result is built at the output scopes directly ([out]);
    - a payload result is weakened along the other sorts' binders crossed
      ([wk]).

    Weakening along another sort is a substitution of that sort, which
    can only be written where the sorts are concrete (as with commuting),
    so it is a parameter, which a syntax supplies from its own Kleisli
    functions.  For System F: terms' term substitution weakens payloads by
    shifting their types; type substitution (of types, or of the types in
    terms) has nothing to weaken.  Build with
      rocq compile -R theories ShiftedNames -Q proto/sorts Proto proto/sorts/Focus.v
      rocq compile -R theories ShiftedNames -Q proto/sorts Proto proto/sorts/Apply.v *)

From Stdlib Require Import PArith Arith List Lia Bool StrictProp.
From ShiftedNames.Core Require Import Trie Label Var Counts Based Skew ATrie Repr Point Deep Compose
  Lookup Adjustment Laws Scoped Indexed Normalise Conv Names.
From ShiftedNames.Core Require Syntax Subst.
Import Syntax (ext, ext_here, ext_under, ext_depth, ext_var, ext_app, ext_shift).
Import Subst (up, down, aok, absn, adj_aok, rel_some, rel_ge, W_inner, W_down, W_HL, W_var, W_pay, W_pass, W_none, W_absurd, aok_squash).
From Proto Require Import Focus.

Section Apply.

Context {a b : nat} (P : vec (radd a (S b)) -> Type) (tv : forall K, var (focus K) -> P (plug K)) (kp : sort_kl a b P).

(** Weakening a term along the other sorts' binders of a descent. *)
Context (wk : forall B M K L (x : descent a b B M K L) k, P (plug (refocus B k)) -> P (plug (refocus K k))).

(** The other sorts at [Bo]: the payloads' family. *)
Context (Bo Mo : scopes a b).
Local Notation term K := (P (plug (refocus Bo K))).
Local Notation Pay := {K & term K}.
Local Notation nadj := (@nadj Pay).
Local Notation entry := (@entry Pay).
Local Notation target := (@target Pay).

(** As [gapply]: descents of the sort's own [ext] ([main]); a variable
    result built at the output scopes; a payload result weakened along
    the other sorts. *)
Local Notation multi f := (f (fun K : scopes a b => focus K) (fun L : scopes a b => focus L)
  (fun Kx L0 K L => descent a b (refocus Bo Kx) (refocus Mo L0) K L) (fun Kx L0 K L x => main x)
  (fun K L => P (plug (out K L))) (fun K L rv H => tv (out K L) (mk_var rv H))
  (fun Kx L0 K L x u m => wk _ _ _ _ x (focus L) (kp _ _ m _ _ here (projT2 u)))) (only parsing).

Definition gapply2 (rt : counts -> lbase) (x : nadj) (Kx Mx s L0 : nat) (HL : Is_true_s (Nat.eqb L0 (s + Mx)))
  (Hx : Is_true_s (aok Kx Mx (absn rt x))) : morph a b P (refocus Bo Kx) (refocus Mo L0) :=
  multi (@Subst.ggapply (fun K => term K) (scopes a b)) rt x Kx Mx s L0 HL Hx.

(** The morphism of an adjustment of the sort, its payloads at [Bo]. *)
Definition apply2 {N M} (ad : adj (fun K => term K) N M) : morph a b P (refocus Bo N) (refocus Mo M) :=
  gapply2 LAbs (radj_n (adj_raw ad)) N M 0 M (Is_true_s_intro (Nat.eqb_refl M)) (adj_aok ad).

(** ** Its laws *)

Context (laws : sort_laws a b P tv kp).

Lemma multi_pres_ext Kx L0 K L (x : descent a b (refocus Bo Kx) (refocus Mo L0) K L) (u : Pay)
    (m1 m2 : morph a b P (refocus Bo (projT1 u)) (refocus Mo (focus L))) :
  (forall K' L' x' v', m1 K' L' x' v' = m2 K' L' x' v') ->
  wk _ _ _ _ x (focus L) (kp _ _ m1 _ _ here (projT2 u)) = wk _ _ _ _ x (focus L) (kp _ _ m2 _ _ here (projT2 u)).
Proof. intros H; f_equal; apply (s_ext _ _ _ _ _ laws), H. Qed.

(** The identity adjustment is the identity morphism. *)
Lemma apply2_identity {N K L} (x : descent a b (refocus Bo N) (refocus Mo N) K L) v :
  apply2 identity K L x v = tv (out K L) (ext_var (main x) v).
Proof.
  set (e := main x).
  assert (A : apply2 identity K L x v
              = multi (@Subst.ggapply0 (fun K => term K) (scopes a b)) (radj_n (adj_raw (@identity _ N))) N N 0 N
                  (Is_true_s_intro (Nat.eqb_refl N)) (Subst.top_aok identity) K L x v) by reflexivity.
  rewrite A; clear A.
  destruct (Subst.option_cases (v_label (var_raw v))) as [[y El]|El];
    [|destruct (lt_dec (v_index (var_raw v)) (ext_depth e)) as [Hi|Hi]].
  2: { rewrite (multi (@Subst.ggapply0_inner (fun K => term K) (scopes a b)) _ _ _ _ _ _ _ x v (W_inner e _ El Hi) El Hi).
       f_equal; apply var_eq; reflexivity. }
  all: assert (Hr : Subst.outer (ext_depth e) (var_raw v)) by (unfold Subst.outer; intros; first [lia|congruence]).
  all: assert (Hn : napply (radj_n (adj_raw (@identity (fun K => term K) N))) (down (ext_depth e) (var_raw v))
                    = inl (down (ext_depth e) (var_raw v))) by apply napply_identity.
  all: assert (H : Is_true_s (wf_var (focus L) (up (0 + ext_depth e) (down (ext_depth e) (var_raw v)))))
         by (cbn [Nat.add]; rewrite (Subst.up_down _ _ Hr); apply (var_ok (ext_var e v))).
  all: rewrite (multi (@Subst.ggapply0_var (fun K => term K) (scopes a b)) multi_pres_ext _ _ _ _ _ _ _ x v _ H Hr Hn).
  all: f_equal; apply var_eq; cbn; apply Subst.up_down, Hr.
Qed.

(** Substituting by the identity adjustment, at the root. *)
Theorem subst2_identity {N} (t : P (plug (refocus Bo N))) :
  kp _ _ (apply2 (N := N) identity) _ _ (here (B := refocus Bo N) (M := refocus Mo N)) t = t.
Proof.
  rewrite (s_ext _ _ _ _ _ laws _ _ (apply2 identity) (unit_m a b P tv) (fun K L x v => apply2_identity x v)).
  apply (s_unit _ _ _ _ _ laws (refocus Bo N) Mo (refocus Bo N) Mo).
Qed.

(** ** Under a binder of the sort *)

(** The descent at the root under one binder of the sort. *)
Definition root1 {N M} : descent a b (refocus Bo N) (refocus Mo M) (refocus Bo (S N)) (refocus Mo (S M)) :=
  pair (whome a _ _) (pair (ext_under ext_here) (whome b _ _)).

(** A descent rebased under it. *)
Definition dlift {N M K L} (x : descent a b (refocus Bo (S N)) (refocus Mo (S M)) K L) : descent a b (refocus Bo N) (refocus Mo M) K L :=
  fapp root1 x.

(** Weakening does not see the sort's own binders. *)
Context (wk_lift : forall N M K L (x : descent a b (refocus Bo (S N)) (refocus Mo (S M)) K L) k u,
  wk _ _ _ _ (dlift x) k u = wk _ _ _ _ x k u).

Lemma apply2_lift_rebase {N M K L} (ad : adj (fun K => term K) N M) (x : descent a b (refocus Bo (S N)) (refocus Mo (S M)) K L) v :
  apply2 ad K L (dlift x) v = apply2 (lift ad) K L x v.
Proof.
  exact (multi (@Subst.gtop_lift_rebase (fun K => term K) (scopes a b)) multi_pres_ext (fun N M K L x => dlift x)
           (fun N M K L x => eq_refl) (fun N M K L x u m => wk_lift N M K L x (focus L) _) ad x v).
Qed.

(** Under a binder of the sort, the descent ([dunder]); the same with the
    bases one up ([dshift]). *)
Definition dunder {B M K L} (x : descent a b B M K L) : descent a b B M (refocus K (S (focus K))) (refocus L (S (focus L))) :=
  pair (first x) (pair (ext_under (main x)) (second (second x))).
Definition dshift {B M K L} (x : descent a b B M K L)
    : descent a b (refocus B (S (focus B))) (refocus M (S (focus M))) (refocus K (S (focus K))) (refocus L (S (focus L))) :=
  pair (first x) (pair (ext_shift (main x)) (second (second x))).

Lemma ext_app_here_l {N M K L} (e : ext N M K L) : ext_app ext_here e = e.
Proof. induction e; cbn; [reflexivity|rewrite IHe; reflexivity]. Qed.

Lemma wapp_home_l n : forall B M K L (w : wit n B M K L), wapp n _ _ _ _ _ _ (whome n B M) w = w.
Proof.
  induction n as [|n IH]; intros B M K L w; cbn; [destruct w; reflexivity|].
  rewrite IH, ext_app_here_l; reflexivity.
Qed.

Lemma dlift_dshift {N M K L} (x : descent a b (refocus Bo N) (refocus Mo M) K L) : dlift (dshift x) = dunder x.
Proof.
  unfold dlift, fapp, root1, dshift, dunder, main; cbn [first second].
  f_equal; [apply wapp_home_l|f_equal; [apply Syntax.ext_app_shift|apply wapp_home_l]].
Qed.

(** Going under a binder of the sort is substituting by the lifted
    adjustment, with the bases one up. *)
Theorem kp_apply2_under {N M K L} (ad : adj (fun K => term K) N M) (x : descent a b (refocus Bo N) (refocus Mo M) K L) t :
  kp _ _ (apply2 ad) _ _ (dunder x) t = kp _ _ (apply2 (lift ad)) _ _ (dshift x) t.
Proof.
  rewrite <- dlift_dshift; unfold dlift.
  rewrite (s_rebase _ _ _ _ _ laws).
  apply (s_ext _ _ _ _ _ laws); intros K' L' x' v; unfold rebase_m.
  exact (apply2_lift_rebase ad x' v).
Qed.

End Apply.

(** ** System F *)

(** Shifting bound variables at or past the cut [dd] by [k]. *)
Definition shc (k dd : nat) (w : rvar) : rvar :=
  match v_label w with
  | None => if Nat.ltb (v_index w) dd then w else mk_rvar None (k + v_index w)
  | Some _ => w
  end.

Lemma shc_wf k G H dd w : H = k + G -> wf_var (dd + G) w = true -> wf_var (dd + H) (shc k dd w) = true.
Proof.
  intros ->; destruct w as [[x|] j]; unfold shc, wf_var; cbn [v_label v_index]; [reflexivity|].
  intros Hj; apply Nat.ltb_lt in Hj.
  destruct (Nat.ltb_spec j dd); cbn [v_label v_index]; apply Nat.ltb_lt; lia.
Qed.

(** Weakening types by the depth [k] of a witness from [G] to [H]: a
    morphism of the type sort. *)
Definition shift_ty {G H : nat} (k : nat) (E : H = k + G) : morph 0 0 (uncurry 1 ty) (pair tt (pair G tt)) (pair tt (pair H tt)) :=
  fun K L x v =>
    tyvar (mk_var (shc k (ext_depth (main x)) (var_raw v))
             (Is_true_s_intro
                (match eq_sym (Syntax.ext_depth_L (main x)) in _ = l return wf_var l _ = true with
                 | eq_refl => shc_wf k G H _ _ E
                                (match Syntax.ext_depth_K (main x) in _ = l return wf_var l _ = true with
                                 | eq_refl => Is_true_s_elim (var_ok v) end) end))).

(** Terms' term substitution: payloads' types shifted along the type
    binders crossed. *)
Definition wk_tm (B M K L : scopes 1 0) (x : descent 1 0 B M K L) (k : nat) (u : tm @ refocus B k) : tm @ refocus K k :=
  kl_tmty (B := pair tt (pair (first (zleft B)) (pair k tt))) (M := pair tt (pair (first (zleft K)) (pair k tt)))
    (shift_ty (ext_depth (first (first x))) (Syntax.ext_depth_K (first (first x)))) here u.

Definition apply_tm {Bo Mo : scopes 1 0} {N M} (ad : adj (fun K => tm @ refocus Bo K) N M) :=
  apply2 (a := 1) (b := 0) (uncurry 2 tm) (fun K v => tmvar v) (fun B M f K L x t => kl_tm f x t) wk_tm Bo Mo ad.

(** Weakening shifts by the type binders crossed, so it does not see the
    term binders at the root. *)
Lemma kl_shift_irr {G H} k1 k2 (E1 : H = k1 + G) (E2 : H = k2 + G) {J} (u : tm G J) :
  k1 = k2 ->
  kl_tmty (B := pair tt (pair G (pair J tt))) (M := pair tt (pair H (pair J tt))) (shift_ty k1 E1) here u
  = kl_tmty (B := pair tt (pair G (pair J tt))) (M := pair tt (pair H (pair J tt))) (shift_ty k2 E2) here u.
Proof. intros ->; reflexivity. Qed.

Lemma wk_tm_lift (Bo Mo : scopes 1 0) N M K L (x : descent 1 0 (refocus Bo (S N)) (refocus Mo (S M)) K L) k u :
  wk_tm _ _ _ _ (dlift Bo Mo x) k u = wk_tm _ _ _ _ x k u.
Proof.
  unfold wk_tm; apply kl_shift_irr; cbn [dlift fapp root1 first second wapp whome].
  rewrite Syntax.ext_depth_app; cbn [Syntax.ext_depth]; lia.
Qed.

(** Going under a term binder: substituting by the lifted adjustment. *)
Theorem tm_apply_under {Bo Mo : scopes 1 0} {N M K L} (ad : adj (fun K => tm @ refocus Bo K) N M)
    (x : descent 1 0 (refocus Bo N) (refocus Mo M) K L) (t : tm @ refocus K (S (focus K))) :
  kl_tm (apply_tm (Bo := Bo) (Mo := Mo) ad) (dunder x) t = kl_tm (apply_tm (Bo := Bo) (Mo := Mo) (lift ad)) (dshift x) t.
Proof.
  exact (kp_apply2_under (a := 1) (b := 0) (uncurry 2 tm) (fun K v => tmvar v) tm_k wk_tm Bo Mo tm_laws (wk_tm_lift Bo Mo) ad x t).
Qed.

(** Type substitution: nothing to weaken. *)
Definition apply_ty {Bo Mo : scopes 0 0} {N M} (ad : adj (fun K => ty @ refocus Bo K) N M) :=
  apply2 (a := 0) (b := 0) (uncurry 1 ty) (fun K v => tyvar v) (fun B M f K L x t => kl_ty f x t)
    (fun B M K L x k u => u) Bo Mo ad.

(** Substitution at the root. *)
Definition subst_tm {G N M} (ad : adj (fun K => tm G K) N M) (t : tm G N) : tm G M :=
  kl_tm (apply_tm (Bo := pair (pair G tt) (pair 0 tt)) (Mo := pair (pair G tt) (pair 0 tt)) ad) here t.

(** ** Checks, by computation *)

(** Instantiating a term variable under a type binder shifts the payload's
    types. *)
Example inst_under_tlam (A : ty 0) :
  subst_tm ⟦ · := (lam A (tmvar bvar0) : tm 0 0) ⟧ (tlam (tmvar bvar0) : tm 0 1)
  = tlam (lam (kl_ty (shift_ty (G := 0) (H := 1) 1 eq_refl) (here (a := 0) (b := 0) (B := pair tt (pair 0 tt)) (M := pair tt (pair 1 tt))) A)
              (tmvar bvar0)).
Proof. reflexivity. Qed.

From Stdlib Require Import String.
Open Scope string_scope.

(** A named variable: the payload's free type variable is shifted past the
    type binder. *)
Example named_under_tlam :
  subst_tm ⟦ "x" := (lam (tyvar bvar0) (tmvar bvar0) : tm 1 0) ⟧ (tlam (tmvar (fvar "x" 0)) : tm 1 0)
  = tlam (lam (tyvar (@mk_var 2 (mk_rvar None 1) stt)) (tmvar bvar0)).
Proof. reflexivity. Qed.

(** Type substitution in terms: the annotations under a term binder and a
    type binder. *)
Definition sc0 (k : nat) : scopes 0 0 := pair tt (pair k tt).
Definition sc01 (N K : nat) : scopes 0 1 := pair tt (pair N (pair K tt)).

Definition tsubst_tm {N M K} (ad : adj (fun G => ty @ refocus (sc0 0) G) N M) (t : tm N K) : tm M K :=
  kl_tmty (B := sc01 N K) (M := sc01 M K) (apply_ty (Bo := sc0 0) (Mo := sc0 0) ad) here t.

Example tsubst_under_binders :
  tsubst_tm ⟦ · := (tyvar bvar0 : ty 1) ⟧
    (lam (tyvar bvar0) (tlam (tapp (tmvar bvar0) (tyvar (@mk_var 3 (mk_rvar None 1) stt)))) : tm 2 0)
  = lam (tyvar bvar0) (tlam (tapp (tmvar bvar0) (tyvar (@mk_var 2 (mk_rvar None 1) stt)))).
Proof. reflexivity. Qed.
