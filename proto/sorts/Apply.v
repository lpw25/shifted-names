(** * Prototype: the morphism of an adjustment, for one sort of several

    [apply a] for a sort of a family: an adjustment [a] of that sort, whose
    payloads are terms of the family at the other sorts' base scopes, gives
    a morphism along any descent.  It is the library's [gapply] with three
    changes:
    - the depth is that of the sort's own [ext] in the descent ([main]);
    - a variable result is built at the output scopes directly ([out]);
    - a payload result is weakened along the other sorts' binders crossed,
      step by step in the descent's order ([wk]).

    Weakening along one step ([wks]) is a substitution of the other sort,
    by a shift ([shift_m], from that sort's [tvar]), with the user's own
    Kleisli function for it ([weaken_x], from the registration of the two
    sorts).  So a syntax supplies only its Kleisli functions and [tvar]s.
    For System F: terms' term substitution weakens payloads by shifting
    their types; type substitution (of types, or of the types in terms)
    has nothing to weaken.  Build with
      rocq compile -R theories ShiftedNames -Q proto/sorts Proto proto/sorts/Focus.v
      rocq compile -R theories ShiftedNames -Q proto/sorts Proto proto/sorts/Commute.v
      rocq compile -R theories ShiftedNames -Q proto/sorts Proto proto/sorts/Apply.v *)

From Stdlib Require Import PArith Arith List Lia Bool StrictProp.
From ShiftedNames.Core Require Import Trie Label Var Counts Based Skew ATrie Repr Point Deep Compose
  Lookup Adjustment Laws Scoped Indexed Normalise Conv Names.
From ShiftedNames.Core Require Syntax Subst.
Import Syntax (ext, ext_here, ext_under, ext_depth, ext_var, ext_app).
Import Subst (up, down, aok, absn, adj_aok, rel_some, rel_ge, W_inner, W_down, W_HL, W_var, W_pay, W_pass, W_none, W_absurd, aok_squash).
From Proto Require Import Focus Commute.

(** ** Shifting: a morphism from [tvar] *)

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

Lemma shc_0 dd w : shc 0 dd w = w.
Proof. destruct w as [[x|] j]; unfold shc; cbn [v_label v_index]; [reflexivity|]. destruct (Nat.ltb j dd); reflexivity. Qed.

(** Weakening by [k] binders of the focused sort, at the root. *)
Definition shift_m {a b} (P : vec (radd a (S b)) -> Type) (tv : forall K, var (focus K) -> P (plug K))
    {B M : scopes a b} (k : nat) (E : focus M = k + focus B) : morph a b P B M :=
  fun K L x v =>
    tv (out K L) (mk_var (shc k (ext_depth (main x)) (var_raw v))
             (Is_true_s_intro
                (match eq_sym (Syntax.ext_depth_L (main x)) in _ = l return wf_var l _ = true with
                 | eq_refl => shc_wf k _ _ _ _ E
                                (match Syntax.ext_depth_K (main x) in _ = l return wf_var l _ = true with
                                 | eq_refl => Is_true_s_elim (var_ok v) end) end))).

Arguments shift_m {a b} P tv {B M} & k E.

(** By none, it is the unit. *)
Lemma shift_m_0 {a b} P tv {B : scopes a b} (E : focus B = 0 + focus B) K L x v :
  shift_m (B := B) (M := B) P tv 0 E K L x v = unit_m a b P tv (B := B) (M := B) K L x v.
Proof. unfold shift_m, unit_m; f_equal; apply var_eq; cbn; apply shc_0. Qed.

(** ** Weakening along a step, from a registration

    A registration of sorts [x] (left) and [y] (right) of a family [T]:
    a term of [T], focused on [y], weakened along one step of a descent
    on [y] (seen from [y]), by [x]'s Kleisli function with a shift by the
    step's [x] binders. *)
Fixpoint zeros (n : nat) : vec n := match n with 0 => tt | S n => pair 0 (zeros n) end.
Definition zeros2 {a c d} : scopes2 a c d := pair (zeros a) (pair 0 (pair (zeros c) (pair 0 (zeros d)))).

(** [p]'s two-hole zipper from [y]'s view, and a step. *)
Definition hole2 {a c d T} (p : @two_sorts a c d T) (z : scopes (radd c (S a)) d) : scopes2 a c d := unzj zeros2 z.
Definition step_of {a c d T} (p : @two_sorts a c d T) {K L K' L'} (s : step (radd c (S a)) d (zj (hole2 p K)) (zj (hole2 p L)) K' L')
    : step2 (hole2 p K) (hole2 p L) (unzj (hole2 p K) K') (unzj (hole2 p L) L') :=
  swunj _ _ s.

Notation weaken_x p tvx :=
  (fun K L K' L' s k u =>
     kx _ p (hole2 p (refocus K k)) (setx (hole2 p (refocus K k)) (zx (hole2 p K')))
       (shift_m _ tvx (ext_depth (ex (step_of p s))) (Syntax.ext_depth_K (ex (step_of p s))))
       k k _ _ pnil u) (only parsing).

Section Apply.

Context {a b : nat} (P : vec (radd a (S b)) -> Type) (tv : forall K, var (focus K) -> P (plug K)) (kp : sort_kl a b P).

(** Weakening a term along the other sorts' binders of one step; along
    a descent, step by step in order. *)
Context (wks : forall K L K' L' (s : step a b K L K' L') k, P (plug (refocus K k)) -> P (plug (refocus K' k))).

Fixpoint wk {B M K L} (x : descent a b B M K L) k : P (plug (refocus B k)) -> P (plug (refocus K k)) :=
  match x in path _ _ _ K0 L0 return P (plug (refocus B k)) -> P (plug (refocus K0 k)) with
  | pnil => fun u => u
  | psnoc x s => fun u => wks _ _ _ _ s k (wk x k u)
  end.

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
  (fun Kx L0 K L x u m => wk x (focus L) (kp _ _ m _ _ here (projT2 u)))) (only parsing).

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
  wk x (focus L) (kp _ _ m1 _ _ here (projT2 u)) = wk x (focus L) (kp _ _ m2 _ _ here (projT2 u)).
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

(** One step under a binder of the sort; the descent at the root under
    it. *)
Definition sfocus {K L : scopes a b} : step a b K L (refocus K (S (focus K))) (refocus L (S (focus L))) :=
  pair (whome a _ _) (pair (ext_under ext_here) (whome b _ _)).

Definition root1 {N M} : descent a b (refocus Bo N) (refocus Mo M) (refocus Bo (S N)) (refocus Mo (S M)) :=
  psnoc pnil sfocus.

(** A descent rebased under it. *)
Definition dlift {N M K L} (x : descent a b (refocus Bo (S N)) (refocus Mo (S M)) K L) : descent a b (refocus Bo N) (refocus Mo M) K L :=
  fapp root1 x.

Lemma ext_app_here_l {N M K L} (e : ext N M K L) : ext_app ext_here e = e.
Proof. induction e; cbn; [reflexivity|rewrite IHe; reflexivity]. Qed.

Lemma ext_app_assoc {N M K L K' L' K'' L''} (e1 : ext N M K L) (e2 : ext K L K' L') (e3 : ext K' L' K'' L'') :
  ext_app e1 (ext_app e2 e3) = ext_app (ext_app e1 e2) e3.
Proof. induction e3; cbn; [reflexivity|rewrite IHe3; reflexivity]. Qed.

Lemma main_fapp {B M K L K' L'} (x1 : descent a b B M K L) (x2 : descent a b K L K' L') :
  main (fapp x1 x2) = ext_app (main x1) (main x2).
Proof. induction x2; cbn; [reflexivity|]. unfold fapp in IHx2; rewrite IHx2, ext_app_assoc; reflexivity. Qed.

Lemma wk_fapp {B M K L K' L'} (x1 : descent a b B M K L) (x2 : descent a b K L K' L') k u :
  wk (fapp x1 x2) k u = wk x2 k (wk x1 k u).
Proof. induction x2; cbn; [reflexivity|]. unfold fapp in IHx2; rewrite IHx2; reflexivity. Qed.

(** Weakening does not see a binder of the sort itself. *)
Context (wks_focus : forall K L k u, wks K L _ _ sfocus k u = u).

Lemma wk_dlift {N M K L} (x : descent a b (refocus Bo (S N)) (refocus Mo (S M)) K L) k u :
  wk (dlift x) k u = wk x k u.
Proof. unfold dlift; rewrite wk_fapp; cbn [wk root1]; f_equal; apply wks_focus. Qed.

Lemma main_dlift {N M K L} (x : descent a b (refocus Bo (S N)) (refocus Mo (S M)) K L) :
  main (dlift x) = ext_app (ext_under ext_here) (main x).
Proof. unfold dlift; rewrite main_fapp; cbn [main root1]; rewrite ext_app_here_l; reflexivity. Qed.

Lemma apply2_lift_rebase {N M K L} (ad : adj (fun K => term K) N M) (x : descent a b (refocus Bo (S N)) (refocus Mo (S M)) K L) v :
  apply2 ad K L (dlift x) v = apply2 (lift ad) K L x v.
Proof.
  exact (multi (@Subst.gtop_lift_rebase (fun K => term K) (scopes a b)) multi_pres_ext (fun N M K L x => dlift x)
           (fun N M K L x => main_dlift x) (fun N M K L x u m => wk_dlift x _ _) ad x v).
Qed.

(** Going under a binder of the sort at the root is substituting by the
    lifted adjustment. *)
Theorem kp_apply2_lift {N M K L} (ad : adj (fun K => term K) N M) (x : descent a b (refocus Bo (S N)) (refocus Mo (S M)) K L) t :
  kp _ _ (apply2 ad) _ _ (dlift x) t = kp _ _ (apply2 (lift ad)) _ _ x t.
Proof.
  unfold dlift; rewrite (s_rebase _ _ _ _ _ laws).
  apply (s_ext _ _ _ _ _ laws); intros K' L' x' v; unfold rebase_m.
  exact (apply2_lift_rebase ad x' v).
Qed.

End Apply.

(** ** System F *)

(** Terms' term substitution: payloads' types shifted along the type
    binders crossed, by the user's [kl_tmty] and [tyvar]. *)
Definition wks_tm : forall K L K' L' (s : step 1 0 K L K' L') k, tm @ refocus K k -> tm @ refocus K' k :=
  weaken_x tm_types_terms (fun K v => tyvar v).

Definition apply_tm {Bo Mo : scopes 1 0} {N M} (ad : adj (fun K => tm @ refocus Bo K) N M) :=
  apply2 (a := 1) (b := 0) (uncurry 2 tm) (fun K v => tmvar v) tm_k wks_tm Bo Mo ad.

(** A term binder shifts no types. *)
Lemma wks_tm_focus K L k u : wks_tm K L _ _ (sfocus (a := 1) (b := 0)) k u = u.
Proof.
  unfold wks_tm; cbn [kx tm_types_terms].
  match goal with |- @kl_tmty ?B ?M ?f ?K ?L ?x ?t = _ =>
    transitivity (tmty_k B M (unit_m 0 0 (uncurry 1 ty) (fun K0 v => tyvar v) (B := zsub (true :: false :: nil) B) (M := zsub (true :: false :: nil) M)) K L x t);
    [ exact (f_ext _ _ _ _ _ _ _ _ _ tmty_laws B M f _ (fun K' L' x' v => shift_m_0 _ _ _ K' L' x' v) K L x t)
    | exact (f_unit _ _ _ _ _ _ _ _ _ tmty_laws B M K L x t) ] end.
Qed.

(** Going under a term binder: substituting by the lifted adjustment. *)
Theorem tm_apply_lift {Bo Mo : scopes 1 0} {N M K L} (ad : adj (fun K => tm @ refocus Bo K) N M)
    (x : descent 1 0 (refocus Bo (S N)) (refocus Mo (S M)) K L) (t : tm @ K) :
  kl_tm (apply_tm (Bo := Bo) (Mo := Mo) ad) (dlift Bo Mo x) t = kl_tm (apply_tm (Bo := Bo) (Mo := Mo) (lift ad)) x t.
Proof.
  exact (kp_apply2_lift (a := 1) (b := 0) (uncurry 2 tm) (fun K v => tmvar v) tm_k wks_tm Bo Mo tm_laws wks_tm_focus ad x t).
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
  = tlam (lam (kl_ty (shift_m (a := 0) (b := 0) (B := pair tt (pair 0 tt)) (M := pair tt (pair 1 tt)) (uncurry 1 ty) (fun K v => tyvar v) 1 eq_refl) here A)
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
