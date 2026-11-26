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
Import Syntax (ext, ext_here, ext_under, ext_depth).
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

(** [gapply2 rt x Kx Mx s L0]: as [gapply]. *)
Fixpoint gapply2 (rt : counts -> lbase) (x : nadj) (Kx Mx s L0 : nat) (HL : Is_true_s (Nat.eqb L0 (s + Mx)))
  (Hx : Is_true_s (aok Kx Mx (absn rt x))) {struct x} : morph a b P (refocus Bo Kx) (refocus Mo L0) :=
  fun K L dx v =>
  let e := main dx in
  let rv := var_raw v in
  let look (v' : rvar) (Hv' : wf_var Kx v' = true) : P (plug (out K L)) :=
    match x as x0 return Is_true_s (aok Kx Mx (absn rt x0)) -> P (plug (out K L)) with
    | NAdj r es => fun Hx =>
        aget_with (label_key (v_label v')) es (rt r)
          (fun Be ent =>
             match ent as ent0
                   return Squash (option_map (unshift (lcounts (rt r))) (aget (label_key (v_label v')) es) = Some (unshift (lcounts Be) ent0)) -> P (plug (out K L)) with
             | Entry h ts len p => fun H1 =>
                 match lt_dec (v_index v') len with
                 | Specif.left Hi =>
                     knth_with (v_index v') ts Be
                       (fun Bt t =>
                          match t as t0
                                return Squash (option_map (unshift (lcounts Be)) (knth ts (v_index v')) = Some (unshift (lcounts Bt) t0)) -> P (plug (out K L)) with
                          | TVar y' j => fun H2 =>
                              tv (out K L) (mk_var (up (s + ext_depth e) (mk_rvar y' (ldval Bt (label_key y') + j)))
                                      (W_var Kx Mx s L0 e (lcounts (rt r)) es v' Hv' Be h ts len p Bt y' j HL Hx H1 Hi H2))
                          | TBind u rho => fun H2 =>
                              wk _ _ _ _ dx (focus L)
                                (kp _ _ (gapply2 (LAdd Bt) rho (projT1 u) Mx (s + ext_depth e) (focus L) (W_HL Mx s e HL)
                                           (W_pay Kx Mx (lcounts (rt r)) es v' Hv' Be h ts len p Bt u rho Hx H1 Hi H2))
                                    _ _ here (projT2 u))
                          end)
                       (fun H2 => match W_absurd (lcounts (rt r)) es _ (v_index v') Be h ts len p (aok_squash Kx Mx _ Hx) H1 Hi H2
                                  with end)
                 | Specif.right Hi =>
                     tv (out K L) (mk_var (up (s + ext_depth e) (mk_rvar h (ldval Be (label_key h) + (v_index v' - len + p))))
                             (W_pass Kx Mx s L0 e (lcounts (rt r)) es v' Hv' Be h ts len p HL Hx H1 Hi))
                 end
             end)
          (fun H1 =>
             tv (out K L) (mk_var (up (s + ext_depth e) (mk_rvar (v_label v') (ldval (rt r) (label_key (v_label v')) + v_index v')))
                     (W_none Kx Mx s L0 e (rt r) es v' Hv' HL Hx H1)))
    end Hx in
  match v_label rv as o return v_label rv = o -> P (plug (out K L)) with
  | None => fun Hl =>
      match lt_dec (v_index rv) (ext_depth e) with
      | Specif.left Hb => tv (out K L) (mk_var rv (W_inner e rv Hl Hb))
      | Specif.right Hb => look (down (ext_depth e) rv) (W_down e rv (var_ok v) (rel_ge rv _ Hb))
      end
  | Some y => fun Hl => look (down (ext_depth e) rv) (W_down e rv (var_ok v) (fun H => rel_some rv y Hl H _))
  end eq_refl.

(** The morphism of an adjustment of the sort, its payloads at [Bo]. *)
Definition apply2 {N M} (ad : adj (fun K => term K) N M) : morph a b P (refocus Bo N) (refocus Mo M) :=
  gapply2 LAbs (radj_n (adj_raw ad)) N M 0 M (Is_true_s_intro (Nat.eqb_refl M)) (adj_aok ad).

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
