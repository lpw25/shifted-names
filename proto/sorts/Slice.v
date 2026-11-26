(** * Prototype: a sort of a multi-sorted syntax, the others' scopes fixed,
    is a one-sorted syntax of the library

    Substituting sort [i] with the other sorts' scopes fixed at [Bo] is a
    one-sorted substitution on [fun K => P (upd n i K Bo)]: its Kleisli
    function is the user's along the morphism lifted to the new witnesses
    ([lift]): a result found under binders of other sorts is weakened
    along them ([wk], from one weakening step per sort, [step]).  So the
    library's [apply], [Subst] and [names] apply as they are.

    Hypotheses, which a syntax proves (System F below / next): a step
    keeps sort [i]'s variables ([step_var]), and weakening commutes with
    the Kleisli function of a lifted morphism ([wk_kl]).  Build with
      rocq compile -R theories ShiftedNames -Q proto/sorts Proto proto/sorts/Desc.v
      rocq compile -R theories ShiftedNames -Q proto/sorts Proto proto/sorts/Slice.v *)

From Stdlib Require Import Arith Lia StrictProp.
From ShiftedNames.Core Require Import Strict Label Var Scoped Indexed.
From ShiftedNames.Core Require Syntax.
From Proto Require Import Desc.
Import Syntax (ext, ext_here, ext_under, ext_app, ext_mid, ext_left, ext_right, ext_depth, ext_var).

Section Slice.

Context {n i : nat}.

(** ** One-sorted witnesses as witnesses with no other binders *)

Fixpoint etv {Bo N M K L} (e : ext N M K L) : vext n i Bo N M Bo K L :=
  match e in ext _ _ K0 L0 return vext n i Bo N M Bo K0 L0 with
  | ext_here => vhere
  | ext_under e => vunder (etv e)
  end.

Lemma vext_i_etv {Bo N M K L} (e : ext N M K L) : vext_i (etv (Bo := Bo) e) = e.
Proof. induction e; cbn; [reflexivity|rewrite IHe; reflexivity]. Qed.

Lemma vext_i_vapp {Bo Bi Mi O1 K1 L1 O2 K2 L2} (e1 : vext n i Bo Bi Mi O1 K1 L1) (e2 : vext n i O1 K1 L1 O2 K2 L2) :
  vext_i (vapp e1 e2) = ext_app (vext_i e1) (vext_i e2).
Proof. induction e2; cbn; try rewrite IHe2; reflexivity. Qed.

Lemma vext_i_vleft {Bo Bi Pi O Ki Li} M (e : vext n i Bo Bi Pi O Ki Li) : vext_i (vleft M e) = ext_left M (vext_i e).
Proof. induction e; cbn; try rewrite IHe; reflexivity. Qed.

Lemma vext_i_vright {Bo Bi Pi O Ki Li} M (e : vext n i Bo Bi Pi O Ki Li) : vext_i (vright M e) = ext_right M (vext_i e).
Proof. induction e; cbn; try rewrite IHe; reflexivity. Qed.

Lemma etv_app {Bo N M K L K' L'} (e1 : ext N M K L) (e2 : ext K L K' L') :
  etv (Bo := Bo) (ext_app e1 e2) = vapp (etv e1) (etv e2).
Proof. induction e2; cbn; try rewrite IHe2; reflexivity. Qed.

(** Splitting the witness of a one-sorted witness is the witnesses of its
    split (with the middle scope, as a pair). *)
Lemma etv_split {Bo N P K L} M (e : ext N P K L) :
  existT (fun m => (vext n i Bo M P Bo m L * vext n i Bo N M Bo K m)%type) _ (vright M (etv e), vleft M (etv e))
  = existT _ _ (etv (ext_right M e), etv (ext_left M e)).
Proof.
  induction e; cbn; [reflexivity|].
  exact (f_equal (fun x : {m & (vext n i Bo M P Bo m _ * vext n i Bo N M Bo _ m)%type} =>
                    let (m, p) := x in existT _ (S m) (vunder (fst p), vunder (snd p))) IHe).
Qed.

(** ** Weakening along the other sorts *)

Context (P : vec n -> Type) (tv : forall O K, var K -> P (upd n i K O)) (kp : sort_kl n i P).
Context (step : forall t L O, P (upd n i L O) -> P (upd n i L (upd n t (S (get n t O)) O))).

Fixpoint wk {Bo Bi Mi O Ki Li} (e : vext n i Bo Bi Mi O Ki Li) {L} (u : P (upd n i L Bo)) : P (upd n i L O) :=
  match e in vext _ _ _ _ _ O0 _ _ return P (upd n i L O0) with
  | vhere => u
  | vunder e => wk e u
  | vother t e => step t L _ (wk e u)
  end.

Lemma wk_etv {Bo N M K L} (e : ext N M K L) {L'} (u : P (upd n i L' Bo)) : wk (etv e) u = u.
Proof. induction e; cbn; auto. Qed.

Lemma wk_vapp {Bo Bi Mi O1 K1 L1 O2 K2 L2} (e1 : vext n i Bo Bi Mi O1 K1 L1) (e2 : vext n i O1 K1 L1 O2 K2 L2) {L}
    (u : P (upd n i L Bo)) : wk (vapp e1 e2) u = wk e2 (wk e1 u).
Proof. induction e2; cbn; try rewrite IHe2; reflexivity. Qed.

Lemma wk_vleft {Bo Bi Pi O Ki Li} M (e : vext n i Bo Bi Pi O Ki Li) {L} (u : P (upd n i L Bo)) :
  wk (vleft M e) u = wk e u.
Proof. induction e; cbn; try rewrite IHe; reflexivity. Qed.

Lemma wk_vright {Bo Bi Pi O Ki Li} M (e : vext n i Bo Bi Pi O Ki Li) {L} (u : P (upd n i L Bo)) :
  wk (vright M e) u = wk e u.
Proof. induction e; cbn; try rewrite IHe; reflexivity. Qed.

(** ** The slice *)

Context (Bo : vec n).

Definition P1 (K : nat) : Type := P (upd n i K Bo).

(** A one-sorted morphism, as a morphism of the new witnesses: its
    results weakened along the other sorts' binders crossed. *)
Definition lift {Bi Mi} (f : Syntax.morph P1 Bi Mi) : morph n i P Bo Bi Mi :=
  fun O Ki Li e v => wk e (f Ki Li (vext_i e) v).

Definition kl1 {N M} (f : Syntax.morph P1 N M) {K L} (e : ext N M K L) (t : P1 K) : P1 L :=
  kp _ _ _ (lift f) _ _ _ (etv e) t.

Context (laws : sort_laws n i P tv kp).

Hypothesis step_var : forall t L O (w : var L), step t L O (tv O L w) = tv _ L w.

Hypothesis wk_kl : forall Mi Pi (g : Syntax.morph P1 Mi Pi) O K L (ev : vext n i Bo Mi Pi O K L) (u : P1 K),
  wk ev (kp _ _ _ (lift g) _ _ _ (etv (vext_i ev)) u) = kp _ _ _ (lift g) _ _ _ ev (wk ev u).

Lemma wk_tv {Bi Mi O Ki Li} (e : vext n i Bo Bi Mi O Ki Li) {L} (w : var L) : wk e (tv Bo L w) = tv O L w.
Proof. induction e; cbn; [reflexivity|exact IHe|rewrite IHe; apply step_var]. Qed.

Theorem slice_laws :
  (forall N M (f : Syntax.morph P1 N M) K L (e : ext N M K L) v, kl1 f e (tv Bo K v) = f K L e v)
  /\ (forall N M (f g : Syntax.morph P1 N M), (forall K L e v, f K L e v = g K L e v) ->
        forall K L (e : ext N M K L) t, kl1 f e t = kl1 g e t)
  /\ (forall N M (f : Syntax.morph P1 N M) K L K' L' (e1 : ext N M K L) (e2 : ext K L K' L') t,
        kl1 f (ext_app e1 e2) t = kl1 (Syntax.rebase_m e1 f) e2 t)
  /\ (forall N K (e : ext N N K K) t, kl1 (fun K L e v => tv Bo L (ext_var e v)) e t = t)
  /\ (forall N M P' (g : Syntax.morph P1 M P') (f : Syntax.morph P1 N M) K L (e : ext N P' K L) t,
        kl1 (fun K L e v => kl1 g (ext_right M e) (f K (ext_mid M e) (ext_left M e) v)) e t
        = kl1 g (ext_right M e) (kl1 f (ext_left M e) t)).
Proof.
  destruct laws as [Hvar Hext Hreb Hunit Hassoc].
  split; [|split; [|split; [|split]]]; unfold kl1.
  - intros N M f K L e v; rewrite Hvar; unfold lift; rewrite wk_etv, vext_i_etv; reflexivity.
  - intros N M f g H K L e t; apply Hext; intros; unfold lift; rewrite H; reflexivity.
  - intros N M f K L K' L' e1 e2 t; rewrite etv_app, Hreb; apply Hext; intros O Ki Li ev v.
    unfold rebase_m, lift, Syntax.rebase_m; rewrite wk_vapp, wk_etv, vext_i_vapp, vext_i_etv; reflexivity.
  - intros N K e t.
    rewrite (Hext _ _ _ _ (unit_m n i P tv)); [apply Hunit|].
    intros O Ki Li ev v; unfold lift, unit_m; rewrite wk_tv; f_equal; apply var_eq; reflexivity.
  - intros N M P' g f K L e t.
    rewrite (Hext _ _ _ _ (comp_m n i P kp (lift g) (lift f))).
    + rewrite Hassoc.
      exact (f_equal (fun x : {m & (vext n i Bo M P' Bo m L * vext n i Bo N M Bo K m)%type} =>
                        let (m, p) := x in kp _ _ _ (lift g) _ _ _ (fst p) (kp _ _ _ (lift f) _ _ _ (snd p) t))
                     (etv_split M e)).
    + intros O Ki Li ev v; unfold lift, comp_m.
      rewrite wk_vleft, vext_i_vleft, <- (vext_i_vright M ev).
      rewrite <- (wk_vright M ev (L := Li)), <- (wk_vright M ev (L := vmid M ev)).
      apply wk_kl.
Qed.

End Slice.
