(** * Prototype: one witness for every sort, the same for every Kleisli
    function of a family

    The witness is one [ext] per sort ([wit n B M K L]: bases [B], [M],
    scopes [K], [L]); going under a binder of sort [t] is [wunder t].  A
    Kleisli function of sort [i] takes the family from [K] to [K] with
    [i]'s scope replaced by [L]'s, so the other sorts are untouched.  All
    the Kleisli functions of a family (here terms' term and type
    substitutions) take witnesses over the family's sorts; a morphism over
    fewer sorts sees its part ([wty]).

    Checked on System F, with no casts: composing witnesses ([wapp]) and
    the rebase law; moving a type substitution past a term substitution
    ([interaction]), with one witness read from either side for the type
    sort ([wflip]).  Both are routine inductions.  Build with
      rocq compile -R theories ShiftedNames -Q proto/sorts Proto proto/sorts/Desc.v
      rocq compile -R theories ShiftedNames -Q proto/sorts Proto proto/sorts/Wall.v *)

From Stdlib Require Import Arith Lia StrictProp.
From ShiftedNames.Core Require Import Strict Label Var Scoped Indexed.
From ShiftedNames.Core Require Syntax.
Import Syntax (ext, ext_here, ext_under, ext_app).
From Proto Require Import Desc.
Import Desc (vec, get, upd, uncurry, both, pair, first, second, ty, tm, tyvar, tyarr, tyall, tmvar, lam, app, tlam, tapp).

(* The witness: one ext per sort. *)
Fixpoint wit (n : nat) : vec n -> vec n -> vec n -> vec n -> Type :=
  match n with
  | 0 => fun _ _ _ _ => unit
  | S n => fun B M K L => both (ext (first B) (first M) (first K) (first L)) (wit n (second B) (second M) (second K) (second L))
  end.

Fixpoint whome (n : nat) : forall B M, wit n B M B M :=
  match n with 0 => fun _ _ => tt | S n => fun B M => pair ext_here (whome n (second B) (second M)) end.

Definition up (n t : nat) (K : vec n) : vec n := upd n t (S (get n t K)) K.

(* Under a binder of sort t. *)
Fixpoint wunder (n t : nat) : forall B M K L, wit n B M K L -> wit n B M (up n t K) (up n t L) :=
  match n with
  | 0 => fun _ _ _ _ w => w
  | S n => fun B M K L w =>
      match t with
      | 0 => pair (ext_under (first w)) (second w)
      | S t => pair (first w) (wunder n t _ _ _ _ (second w))
      end
  end.
Arguments wunder {n} t {B M K L} w.

(* Composing witnesses (rebase), componentwise. *)
Fixpoint wapp (n : nat) : forall B M K L K' L', wit n B M K L -> wit n K L K' L' -> wit n B M K' L' :=
  match n with
  | 0 => fun _ _ _ _ _ _ _ _ => tt
  | S n => fun B M K L K' L' w1 w2 => pair (ext_app (first w1) (first w2)) (wapp n _ _ _ _ _ _ (second w1) (second w2))
  end.

(* Reading sort j's descent the other way (the other side of a substitution of j). *)
Fixpoint ext_flip {N M K L} (e : ext N M K L) : ext M N L K :=
  match e with Syntax.ext_here => ext_here | Syntax.ext_under e => ext_under (ext_flip e) end.

Fixpoint wflip (n j : nat) : forall B M K L, wit n B M K L ->
    wit n (upd n j (get n j M) B) (upd n j (get n j B) M) (upd n j (get n j L) K) (upd n j (get n j K) L) :=
  match n with
  | 0 => fun _ _ _ _ w => w
  | S n => fun B M K L w =>
      match j with
      | 0 => pair (ext_flip (first w)) (second w)
      | S j => pair (first w) (wflip n j _ _ _ _ (second w))
      end
  end.
Arguments wflip {n} j {B M K L} w.

Lemma ext_flip_flip {N M K L} (e : ext N M K L) : ext_flip (ext_flip e) = e.
Proof. induction e; cbn; congruence. Qed.

(* System F *)
Definition tymorph (B M : vec 1) := forall K L, wit 1 B M K L -> var (first K) -> ty (first L).

Fixpoint kl_ty {B M} (h : tymorph B M) {K L} (w : wit 1 B M K L) (A : ty (first K)) : ty (first L) :=
  match A with
  | tyvar v => h K L w v
  | tyarr A A' => tyarr (kl_ty h w A) (kl_ty h w A')
  | tyall A => tyall (kl_ty h (wunder 0 w) A)
  end.

Definition tmmorph (B M : vec 2) := forall K L, wit 2 B M K L -> var (first (second K)) -> tm (first K) (first (second L)).

Fixpoint kl_tm {B M} (f : tmmorph B M) {K L} (w : wit 2 B M K L) (t : tm (first K) (first (second K)))
    : tm (first K) (first (second L)) :=
  match t with
  | tmvar v => f K L w v
  | lam A u => lam A (kl_tm f (wunder 1 w) u)
  | app t u => app (kl_tm f w t) (kl_tm f w u)
  | tlam u => tlam (kl_tm f (wunder 0 w) u)
  | tapp t A => tapp (kl_tm f w t) A
  end.

(* Types in terms: the same witness; the type morphism sees its types' part. *)
Definition wty {B M K L} (w : wit 2 B M K L) : wit 1 (pair (first B) tt) (pair (first M) tt) (pair (first K) tt) (pair (first L) tt) :=
  pair (first w) tt.

Fixpoint kl_tmty {B M} (h : tymorph (pair (first B) tt) (pair (first M) tt)) {K L} (w : wit 2 B M K L)
    (t : tm (first K) (first (second K))) : tm (first L) (first (second K)) :=
  match t with
  | tmvar v => tmvar v
  | lam A u => lam (kl_ty h (wty w) A) (kl_tmty h (wunder 1 w) u)
  | app t u => app (kl_tmty h w t) (kl_tmty h w u)
  | tlam u => tlam (kl_tmty h (wunder 0 w) u)
  | tapp t A => tapp (kl_tmty h w t) (kl_ty h (wty w) A)
  end.

(* Interaction: a term substitution f and a type substitution h, one witness w. *)
Definition tmap {B M} (h : tymorph (pair (first B) tt) (pair (first M) tt)) (f : tmmorph B M)
    : tmmorph (pair (first M) (second B)) (pair (first B) (second M)) :=
  fun K L w v => @kl_tmty (pair (first B) (second M)) (pair (first M) (second B)) h _ _ (wflip 1 (wflip 0 w)) (f _ _ (wflip 0 w) v).

Lemma interaction {B M} (h : tymorph (pair (first B) tt) (pair (first M) tt)) (f : tmmorph B M) :
  forall K L (w : wit 2 B M K L) t,
  @kl_tmty (pair (first B) (second M)) (pair (first M) (second B)) h _ _ (wflip 1 w) (kl_tm f w t) = kl_tm (tmap h f) (wflip 0 w) (kl_tmty h w t).
Proof.
  fix IH 4; intros K L w t; destruct t; cbn [kl_tm kl_tmty].
  - unfold tmap; cbn [wflip first second]; rewrite ext_flip_flip; reflexivity.
  - f_equal; exact (IH _ _ (wunder 1 w) t).
  - f_equal; apply IH.
  - f_equal; exact (IH _ _ (wunder 0 w) t).
  - f_equal; apply IH.
Qed.

(* Rebase, stated without casts. *)
Definition rebase {B M K L} (w1 : wit 2 B M K L) (f : tmmorph B M) : tmmorph K L :=
  fun K' L' w v => f K' L' (wapp 2 _ _ _ _ _ _ w1 w) v.

Lemma rebase_law {B M} (f : tmmorph B M) K L (w1 : wit 2 B M K L) : forall K' L' (w2 : wit 2 K L K' L') t,
  kl_tm f (wapp 2 _ _ _ _ _ _ w1 w2) t = kl_tm (rebase w1 f) w2 t.
Proof.
  fix IH 4; intros K' L' w2 t; destruct t; cbn [kl_tm]; f_equal;
    first [reflexivity | apply IH | exact (IH _ _ (wunder 1 w2) t) | exact (IH _ _ (wunder 0 w2) t)].
Qed.
