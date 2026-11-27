(** * Prototype: a substitution is focused on its sort

    Substituting sort [i] of a family over [a + 1 + b] sorts, the scopes
    are a zipper ([scopes a b]): the sorts to the left of [i] (nearest
    first), [i]'s scope (the focus), and the sorts to the right.  The
    family is at the zipper plugged back ([plug]).  The witness
    ([descent]) is a path of steps, in the order the binders were gone
    under; a step is a zipper of [ext]s: the focus's input and output
    scopes, and for each other sort its scope and the one on the other
    side of a substitution of it.  A Kleisli function goes from the input zipper to
    the same zipper with the focus's output scope ([out]): the other sorts
    are the same on both sides, so nothing containing only them is
    visited.  Nothing is cut out of a vector or put back, so there are no
    casts.

    For the user ([What the user writes] below): [fam F K], the family at a
    zipper; [under t x], going under a binder of sort [t] (counted from the
    left); [x‹+ -›], the witness for a family inside another, saying which
    of the sorts (in order) it has, whichever sort is focused.  The sorts are concrete there, so all of them compute away.
    The laws of a Kleisli function are one tactic call ([laws_proof]).
    Build with
      rocq compile -R theories ShiftedNames -Q proto/sorts Proto proto/sorts/Focus.v *)

From Stdlib Require Import Arith Lia StrictProp.
From ShiftedNames.Core Require Import Strict Label Var Scoped Indexed.
From ShiftedNames.Core Require Syntax.
Import Syntax (ext, ext_here, ext_under, ext_app, ext_mid, ext_left, ext_right, ext_var, ext_var_same).

Set Primitive Projections.
Record both (A B : Type) : Type := pair { first : A; second : B }.
Unset Primitive Projections.
Arguments pair {A B} first second.
Arguments first {A B} _.
Arguments second {A B} _.

(** ** Vectors and zippers of scopes *)

Fixpoint vec (n : nat) : Type := match n with 0 => unit | S n => both nat (vec n) end.

Fixpoint get (n p : nat) : vec n -> nat :=
  match n as n0 return vec n0 -> nat with
  | 0 => fun _ => 0
  | S n => fun x => match p with 0 => first x | S p => get n p (second x) end
  end.

Fixpoint upd (n p k : nat) : vec n -> vec n :=
  match n as n0 return vec n0 -> vec n0 with
  | 0 => fun x => x
  | S n => fun x => match p with 0 => pair k (second x) | S p => pair (first x) (upd n p k (second x)) end
  end.

(** [a + b], counted so that moving one sort across is no change. *)
Fixpoint radd (a b : nat) : nat := match a with 0 => b | S a => radd a (S b) end.

(** The left part (nearest first) put back onto the right. *)
Fixpoint rev_app (a b : nat) : vec a -> vec b -> vec (radd a b) :=
  match a as a0 return vec a0 -> vec b -> vec (radd a0 b) with
  | 0 => fun _ r => r
  | S a => fun l r => rev_app a (S b) (second l) (pair (first l) r)
  end.

(** A zipper: the left part (nearest first), the focus, the right part. *)
Definition scopes (a b : nat) : Type := both (vec a) (both nat (vec b)).

Definition focus {a b} (z : scopes a b) : nat := first (second z).
Definition zleft {a b} (z : scopes a b) : vec a := first z.
Definition zright {a b} (z : scopes a b) : vec b := second (second z).

Definition plug {a b} (z : scopes a b) : vec (radd a (S b)) := rev_app a (S b) (zleft z) (second z).

(** The zipper [K] with [L]'s focus. *)
Definition out {a b} (K L : scopes a b) : scopes a b := pair (zleft K) (pair (focus L) (zright K)).

(** The zipper [z] with focus [k]. *)
Definition refocus {a b} (z : scopes a b) (k : nat) : scopes a b := pair (zleft z) (pair k (zright z)).

(** Moving the focus one sort to the right: the same vector, by
    computation, whatever the number of sorts. *)
Definition zright1 {a b} (z : scopes a (S b)) : scopes (S a) b :=
  pair (pair (focus z) (zleft z)) (zright z).

Lemma plug_right1 {a b} (z : scopes a (S b)) : plug (zright1 z) = plug z.
Proof. reflexivity. Qed.

(** ** Families *)

Fixpoint arity (n : nat) : Type := match n with 0 => Type | S n => nat -> arity n end.

Fixpoint uncurry (n : nat) : arity n -> vec n -> Type :=
  match n as n0 return arity n0 -> vec n0 -> Type with
  | 0 => fun F _ => F
  | S n => fun F x => uncurry n (F (first x)) (second x)
  end.

(** The user's family at a zipper. *)
Definition fam {a b} (K : scopes a b) (F : arity (radd a (S b))) : Type := uncurry _ F (plug K).
Notation "F @ K" := (fam K F) (at level 11, K at level 10, no associativity).

(** Some of [n] sorts, in order. *)
Inductive thin : nat -> nat -> Type :=
| tdone : thin 0 0
| tkeep {m n} : thin m n -> thin (S m) (S n)
| tskip {m n} : thin m n -> thin m (S n).

Fixpoint restr {m n} (th : thin m n) : vec n -> vec m :=
  match th in thin m0 n0 return vec n0 -> vec m0 with
  | tdone => fun x => x
  | tkeep th => fun x => pair (first x) (restr th (second x))
  | tskip th => fun x => restr th (second x)
  end.

(** A zipper over some of the sorts around the focus. *)
Definition zrestr {a b aT bT} (tl : thin a aT) (tr : thin b bT) (z : scopes aT bT) : scopes a b :=
  pair (restr tl (zleft z)) (pair (focus z) (restr tr (zright z))).

(** ** Thinnings for the user: which sorts, all at once

    A mask: of the sorts in order, which to keep ([x‹+ -›] below: keep the
    first, skip the second; types inside terms).  Whatever sort is focused, the left part (nearest
    first) and the right part are read off it ([tl_of], [tr_of]); the
    focus is always kept. *)

From Stdlib Require Import List.

Declare Custom Entry sorts.
Notation "›" := nil (in custom sorts at level 0).
Notation "+ m" := (cons true m) (in custom sorts at level 2, m custom sorts at level 2, format "+ m").
Notation "- m" := (cons false m) (in custom sorts at level 2, m custom sorts at level 2, format "- m").

Definition mask : Type := list bool.

Fixpoint nthb (p : nat) (s : mask) : bool :=
  match s with nil => false | cons c s => match p with 0 => c | S p => nthb p s end end.

(** How many of the [a] sorts left of the focus are kept, and which. *)
Fixpoint lkept (s : mask) (a : nat) : nat :=
  match a with 0 => 0 | S a => if nthb a s then S (lkept s a) else lkept s a end.

Fixpoint tl_of (s : mask) (a : nat) : thin (lkept s a) a :=
  match a as a0 return thin (lkept s a0) a0 with
  | 0 => tdone
  | S a =>
      match nthb a s as c return thin (if c then S (lkept s a) else lkept s a) (S a) with
      | true => tkeep (tl_of s a)
      | false => tskip (tl_of s a)
      end
  end.

(** The same for the [b] sorts right of the focus at [a]. *)
Fixpoint rkept (s : mask) (a b : nat) : nat :=
  match b with 0 => 0 | S b => if nthb (S a) s then S (rkept s (S a) b) else rkept s (S a) b end.

Fixpoint tr_of (s : mask) (a b : nat) : thin (rkept s a b) b :=
  match b as b0 return thin (rkept s a b0) b0 with
  | 0 => tdone
  | S b =>
      match nthb (S a) s as c return thin (if c then S (rkept s (S a) b) else rkept s (S a) b) (S b) with
      | true => tkeep (tr_of s (S a) b)
      | false => tskip (tr_of s (S a) b)
      end
  end.

(** A zipper over the sorts [s] keeps. *)
Definition zsub {a b} (s : mask) (z : scopes a b) : scopes (lkept s a) (rkept s a b) := zrestr (tl_of s a) (tr_of s a b) z.

(** ** Witnesses *)

Fixpoint ext_flip {N M K L} (e : ext N M K L) : ext M N L K :=
  match e with Syntax.ext_here => ext_here | Syntax.ext_under e => ext_under (ext_flip e) end.

Lemma ext_flip_flip {N M K L} (e : ext N M K L) : ext_flip (ext_flip e) = e.
Proof. induction e; cbn; congruence. Qed.

(** An [ext] for each of [n] sorts. *)
Fixpoint wit (n : nat) : vec n -> vec n -> vec n -> vec n -> Type :=
  match n with
  | 0 => fun _ _ _ _ => unit
  | S n => fun B M K L => both (ext (first B) (first M) (first K) (first L)) (wit n (second B) (second M) (second K) (second L))
  end.

Fixpoint whome (n : nat) : forall B M, wit n B M B M :=
  match n with 0 => fun _ _ => tt | S n => fun B M => pair ext_here (whome n (second B) (second M)) end.

Fixpoint wunder (n p : nat) : forall B M K L, wit n B M K L ->
    wit n B M (upd n p (S (get n p K)) K) (upd n p (S (get n p L)) L) :=
  match n with
  | 0 => fun _ _ _ _ w => w
  | S n => fun B M K L w =>
      match p with
      | 0 => pair (ext_under (first w)) (second w)
      | S p => pair (first w) (wunder n p _ _ _ _ (second w))
      end
  end.

Fixpoint wapp (n : nat) : forall B M K L K' L', wit n B M K L -> wit n K L K' L' -> wit n B M K' L' :=
  match n with
  | 0 => fun _ _ _ _ _ _ _ _ => tt
  | S n => fun B M K L K' L' w1 w2 => pair (ext_app (first w1) (first w2)) (wapp n _ _ _ _ _ _ (second w1) (second w2))
  end.

Fixpoint wrestr {m n} (th : thin m n) : forall B M K L, wit n B M K L ->
    wit m (restr th B) (restr th M) (restr th K) (restr th L) :=
  match th as th0 in thin m0 n0 return forall B M K L, wit n0 B M K L -> wit m0 (restr th0 B) (restr th0 M) (restr th0 K) (restr th0 L) with
  | tdone => fun _ _ _ _ w => w
  | tkeep th => fun B M K L w => pair (first w) (wrestr th _ _ _ _ (second w))
  | tskip th => fun B M K L w => wrestr th _ _ _ _ (second w)
  end.

(** One step of a descent: a zipper of [ext]s, one per sort. *)
Definition step (a b : nat) (B M K L : scopes a b) : Type :=
  both (wit a (zleft B) (zleft M) (zleft K) (zleft L))
       (both (ext (focus B) (focus M) (focus K) (focus L)) (wit b (zright B) (zright M) (zright K) (zright L))).

Definition smain {a b B M K L} (x : step a b B M K L) : ext (focus B) (focus M) (focus K) (focus L) := first (second x).

Definition swith_main {a b B M K L} Bi Mi Ki Li (x : step a b B M K L) (e : ext Bi Mi Ki Li)
    : step a b (refocus B Bi) (refocus M Mi) (refocus K Ki) (refocus L Li) :=
  pair (first x) (pair e (second (second x))).

Definition shere {a b} {B M : scopes a b} : step a b B M B M := pair (whome a _ _) (pair ext_here (whome b _ _)).

(** Sort [t]'s scope one up (counted from the left). *)
Definition zup {a b} (t : nat) (z : scopes a b) : scopes a b :=
  match Nat.compare t a with
  | Lt => pair (upd a (a - S t) (S (get a (a - S t) (zleft z))) (zleft z)) (second z)
  | Eq => refocus z (S (focus z))
  | Gt => pair (zleft z) (pair (focus z) (upd b (t - S a) (S (get b (t - S a) (zright z))) (zright z)))
  end.

(** A step under a binder of sort [t]. *)
Definition sunder {a b} (t : nat) {B M K L} (x : step a b B M K L) : step a b B M (zup t K) (zup t L) :=
  match Nat.compare t a as c return
    step a b B M
      (match c with
       | Lt => pair (upd a (a - S t) (S (get a (a - S t) (zleft K))) (zleft K)) (second K)
       | Eq => refocus K (S (focus K))
       | Gt => pair (zleft K) (pair (focus K) (upd b (t - S a) (S (get b (t - S a) (zright K))) (zright K)))
       end)
      (match c with
       | Lt => pair (upd a (a - S t) (S (get a (a - S t) (zleft L))) (zleft L)) (second L)
       | Eq => refocus L (S (focus L))
       | Gt => pair (zleft L) (pair (focus L) (upd b (t - S a) (S (get b (t - S a) (zright L))) (zright L)))
       end)
  with
  | Lt => pair (wunder a (a - S t) _ _ _ _ (first x)) (second x)
  | Eq => pair (first x) (pair (ext_under (smain x)) (second (second x)))
  | Gt => pair (first x) (pair (smain x) (wunder b (t - S a) _ _ _ _ (second (second x))))
  end.

Definition srestrict_lr {a b aT bT} (tl : thin a aT) (tr : thin b bT) {B M K L} (x : step aT bT B M K L)
    : step a b (zrestr tl tr B) (zrestr tl tr M) (zrestr tl tr K) (zrestr tl tr L) :=
  pair (wrestr tl _ _ _ _ (first x)) (pair (smain x) (wrestr tr _ _ _ _ (second (second x)))).

(** Through a middle base [Mi] of the focus (assoc). *)
Definition smid {a b B M K L} Mi (x : step a b B M K L) : nat := ext_mid Mi (smain x).

Definition sleft {a b B M K L} Mi (x : step a b B M K L) : step a b B (refocus M Mi) K (refocus L (smid Mi x)) :=
  swith_main _ _ _ _ x (ext_left Mi (smain x)).

Definition sright {a b B M K L} Mi (x : step a b B M K L) : step a b (refocus B Mi) M (refocus K (smid Mi x)) L :=
  swith_main _ _ _ _ x (ext_right Mi (smain x)).

(** A path of steps, in order. *)
Inductive path {Z : Type} (St : Z -> Z -> Z -> Z -> Type) (B M : Z) : Z -> Z -> Type :=
| pnil : path St B M B M
| psnoc {K L K' L'} : path St B M K L -> St K L K' L' -> path St B M K' L'.

Arguments pnil {Z St B M}.
Arguments psnoc {Z St B M K L K' L'} x s.

(** One path after another. *)
Fixpoint papp {Z St} {B M K L K' L' : Z} (x1 : path St B M K L) (x2 : path St K L K' L') : path St B M K' L' :=
  match x2 in path _ _ _ K0 L0 return path St B M K0 L0 with
  | pnil => x1
  | psnoc x2 s => psnoc (papp x1 x2) s
  end.

(** Step by step, the scopes mapped. *)
Fixpoint pmap {Z Z' St St'} (gK gL : Z -> Z -> Z')
    (h : forall K L K' L', St K L K' L' -> St' (gK K L) (gL K L) (gK K' L') (gL K' L')) {B M K L}
    (x : path St B M K L) : path St' (gK B M) (gL B M) (gK K L) (gL K L) :=
  match x in path _ _ _ K0 L0 return path St' (gK B M) (gL B M) (gK K0 L0) (gL K0 L0) with
  | pnil => pnil
  | psnoc x s => psnoc (pmap gK gL h x) (h _ _ _ _ s)
  end.

Lemma pmap_papp {Z Z' : Type} {St : Z -> Z -> Z -> Z -> Type} {St' : Z' -> Z' -> Z' -> Z' -> Type} gK gL h
    {B M K L K' L' : Z} (x1 : path St B M K L) (x2 : path St K L K' L') :
  pmap (St' := St') gK gL h (papp x1 x2) = papp (pmap gK gL h x1) (pmap gK gL h x2).
Proof. induction x2; cbn; [reflexivity|rewrite IHx2; reflexivity]. Qed.

(** A descent: the steps gone under, in order. *)
Notation descent a b := (path (step a b)).

(** The focused sort's [ext] over the whole descent. *)
Fixpoint main {a b B M K L} (x : descent a b B M K L) : ext (focus B) (focus M) (focus K) (focus L) :=
  match x in path _ _ _ K0 L0 return ext (focus B) (focus M) (focus K0) (focus L0) with
  | pnil => ext_here
  | psnoc x s => ext_app (main x) (smain s)
  end.

(** ** What the user writes *)

(** At the root: nothing gone under. *)
Definition here {a b} {B M : scopes a b} : descent a b B M B M := pnil.

(** Under a binder of sort [t]. *)
Definition under {a b} (t : nat) {B M K L} (x : descent a b B M K L) : descent a b B M (zup t K) (zup t L) :=
  psnoc x (sunder t shere).

(** The part for a family inside another, over some of the sorts on each
    side ([tl] on the left, nearest first; [tr] on the right): step by
    step. *)
Definition restrict_lr {a b aT bT} (tl : thin a aT) (tr : thin b bT) {B M K L} (x : descent aT bT B M K L)
    : descent a b (zrestr tl tr B) (zrestr tl tr M) (zrestr tl tr K) (zrestr tl tr L) :=
  pmap (fun K _ => zrestr tl tr K) (fun _ L => zrestr tl tr L) (fun _ _ _ _ s => srestrict_lr tl tr s) x.

(** The witness for a family inside another, over the sorts [s] keeps. *)
Definition restrict {a b} (s : mask) {B M K L} (x : descent a b B M K L)
    : descent (lkept s a) (rkept s a b) (zsub s B) (zsub s M) (zsub s K) (zsub s L) :=
  restrict_lr (tl_of s a) (tr_of s a b) x.

(** Written after the witness: [x‹+ -›]. *)
Notation "z ‹ m" := (zsub m z) (only printing, at level 1, left associativity, m custom sorts at level 2, format "z ‹ m").
Notation "x ‹ m" := (restrict m x) (at level 1, left associativity, m custom sorts at level 2, format "x ‹ m").

(** ** Operations of the library *)

(** Composing (rebase): one descent after another. *)
Definition fapp {a b} {B M K L K' L' : scopes a b} (x1 : descent a b B M K L) (x2 : descent a b K L K' L') : descent a b B M K' L' :=
  papp x1 x2.

(** Through a middle base [Mi] of the focus (assoc): step by step. *)
Fixpoint fmid {a b B M K L} Mi (x : descent a b B M K L) : nat :=
  match x with
  | pnil => Mi
  | psnoc x s => smid (fmid Mi x) s
  end.

Fixpoint fleft {a b B M K L} Mi (x : descent a b B M K L) : descent a b B (refocus M Mi) K (refocus L (fmid Mi x)) :=
  match x in path _ _ _ K0 L0 return descent a b B (refocus M Mi) K0 (refocus L0 (fmid Mi x)) with
  | pnil => pnil
  | psnoc x s => psnoc (fleft Mi x) (sleft (fmid Mi x) s)
  end.

Fixpoint fright {a b B M K L} Mi (x : descent a b B M K L) : descent a b (refocus B Mi) M (refocus K (fmid Mi x)) L :=
  match x in path _ _ _ K0 L0 return descent a b (refocus B Mi) M (refocus K0 (fmid Mi x)) L0 with
  | pnil => pnil
  | psnoc x s => psnoc (fright Mi x) (sright (fmid Mi x) s)
  end.

(** Restricting commutes with composing. *)
Lemma restrict_lr_fapp {a b aT bT} (tl : thin a aT) (tr : thin b bT) {B M K L K' L'}
    (x1 : descent aT bT B M K L) (x2 : descent aT bT K L K' L') :
  restrict_lr tl tr (fapp x1 x2) = fapp (restrict_lr tl tr x1) (restrict_lr tl tr x2).
Proof. exact (pmap_papp _ _ _ x1 x2). Qed.

(** Restricting commutes with splitting: the two halves and their middle
    scope, as a dependent pair. *)
Lemma restrict_lr_split {a b aT bT} (tl : thin a aT) (tr : thin b bT) {B M K L} Mi (x : descent aT bT B M K L) :
  existT (fun m => (descent a b (zrestr tl tr B) (refocus (zrestr tl tr M) Mi) (zrestr tl tr K) (refocus (zrestr tl tr L) m)
                    * descent a b (refocus (zrestr tl tr B) Mi) (zrestr tl tr M) (refocus (zrestr tl tr K) m) (zrestr tl tr L))%type)
    (fmid Mi x) (restrict_lr tl tr (fleft Mi x), restrict_lr tl tr (fright Mi x))
  = existT _ (fmid Mi (restrict_lr tl tr x)) (fleft Mi (restrict_lr tl tr x), fright Mi (restrict_lr tl tr x)).
Proof.
  induction x as [|K L K' L' x IH s]; cbn; [reflexivity|].
  exact (f_equal (fun p : {m & (descent a b (zrestr tl tr B) (refocus (zrestr tl tr M) Mi) (zrestr tl tr K) (refocus (zrestr tl tr L) m)
                               * descent a b (refocus (zrestr tl tr B) Mi) (zrestr tl tr M) (refocus (zrestr tl tr K) m) (zrestr tl tr L))%type} =>
                    let (m, pr) := p in
                    existT (fun m => (descent a b (zrestr tl tr B) (refocus (zrestr tl tr M) Mi) (zrestr tl tr K') (refocus (zrestr tl tr L') m)
                                      * descent a b (refocus (zrestr tl tr B) Mi) (zrestr tl tr M) (refocus (zrestr tl tr K') m) (zrestr tl tr L'))%type)
                      (smid m s) (psnoc (fst pr) (srestrict_lr tl tr (sleft m s)), psnoc (snd pr) (srestrict_lr tl tr (sright m s)))) IH).
Qed.

(** ** Morphisms, Kleisli functions and their laws *)

Section Generic.

Context (a b : nat).
Notation n := (radd a (S b)).

(** A morphism of the focused sort into its carrier [P], from the bases
    [B] (the other side [M]; the focus goes from [B]'s to [M]'s). *)
Definition morph (P : vec n -> Type) (B M : scopes a b) : Type :=
  forall K L, descent a b B M K L -> var (focus K) -> P (plug (out K L)).

Definition rebase_m {P B M K1 L1} (x1 : descent a b B M K1 L1) (f : morph P B M) : morph P K1 L1 :=
  fun K L x v => f K L (fapp x1 x) v.

Definition sort_kl (P : vec n -> Type) : Type :=
  forall B M (f : morph P B M) K L, descent a b B M K L -> P (plug K) -> P (plug (out K L)).

(** A family over more sorts, focused on the same sort. *)
Definition fam_kl (P : vec n -> Type) {aT bT} (tl : thin a aT) (tr : thin b bT) (T : vec (radd aT (S bT)) -> Type) : Type :=
  forall B M (f : morph P (zrestr tl tr B) (zrestr tl tr M)) K L, descent aT bT B M K L -> T (plug K) -> T (plug (out K L)).

Section Laws.

Context (P : vec n -> Type) (tv : forall K, var (focus K) -> P (plug K)) (kp : sort_kl P).

Definition unit_m {B M} : morph P B (refocus M (focus B)) := fun K L x v => tv (out K L) (ext_var (main x) v).

Definition comp_m {B M} Mi (g : morph P (refocus B Mi) M) (f : morph P B (refocus M Mi)) : morph P B M :=
  fun K L x v => kp _ _ g _ _ (fright Mi x) (f K _ (fleft Mi x) v).

Record sort_laws : Prop := {
  s_var : forall B M (f : morph P B M) K L (x : descent a b B M K L) v, kp _ _ f _ _ x (tv K v) = f K L x v;
  s_ext : forall B M (f g : morph P B M), (forall K L x v, f K L x v = g K L x v) ->
    forall K L (x : descent a b B M K L) t, kp _ _ f _ _ x t = kp _ _ g _ _ x t;
  s_rebase : forall B M (f : morph P B M) K1 L1 K2 L2 (x1 : descent a b B M K1 L1) (x2 : descent a b K1 L1 K2 L2) t,
    kp _ _ f _ _ (fapp x1 x2) t = kp _ _ (rebase_m x1 f) _ _ x2 t;
  s_unit : forall B M K L (x : descent a b B (refocus M (focus B)) K (refocus L (focus K))) t, kp _ _ unit_m _ _ x t = t;
  s_assoc : forall B M Mi (g : morph P (refocus B Mi) M) (f : morph P B (refocus M Mi)) K L (x : descent a b B M K L) t,
    kp _ _ (comp_m Mi g f) _ _ x t = kp _ _ g _ _ (fright Mi x) (kp _ _ f _ _ (fleft Mi x) t) }.

Record fam_laws {aT bT} (tl : thin a aT) (tr : thin b bT) (T : vec (radd aT (S bT)) -> Type) (k : fam_kl P tl tr T) : Prop := {
  f_ext : forall B M (f g : morph P (zrestr tl tr B) (zrestr tl tr M)), (forall K L x v, f K L x v = g K L x v) ->
    forall K L (x : descent aT bT B M K L) t, k _ _ f _ _ x t = k _ _ g _ _ x t;
  f_rebase : forall B M (f : morph P (zrestr tl tr B) (zrestr tl tr M)) K1 L1 K2 L2
      (x1 : descent aT bT B M K1 L1) (x2 : descent aT bT K1 L1 K2 L2) t,
    k _ _ f _ _ (fapp x1 x2) t = k _ _ (rebase_m (restrict_lr tl tr x1) f) _ _ x2 t;
  f_unit : forall B M K L (x : descent aT bT B (refocus M (focus B)) K (refocus L (focus K))) t,
    k B (refocus M (focus B)) (@unit_m (zrestr tl tr B) (zrestr tl tr M)) _ _ x t = t;
  f_assoc : forall B M Mi (g : morph P (zrestr tl tr (refocus B Mi)) (zrestr tl tr M)) (f : morph P (zrestr tl tr B) (zrestr tl tr (refocus M Mi)))
      K L (x : descent aT bT B M K L) t,
    k B M (@comp_m (zrestr tl tr B) (zrestr tl tr M) Mi g f) _ _ x t = k _ _ g _ _ (fright Mi x) (k _ _ f _ _ (fleft Mi x) t) }.

(** Associativity through a restriction (a family's Kleisli function
    passes its restricted witness to its carrier's). *)
Lemma assoc_restrict (H : sort_laws) {aT bT} (tl : thin a aT) (tr : thin b bT) {B M : scopes aT bT} Mi
    (g : morph P (refocus (zrestr tl tr B) Mi) (zrestr tl tr M)) (f : morph P (zrestr tl tr B) (refocus (zrestr tl tr M) Mi))
    {K L} (x : descent aT bT B M K L) t :
  kp _ _ (comp_m (B := zrestr tl tr B) (M := zrestr tl tr M) Mi g f) _ _ (restrict_lr tl tr x) t
  = kp _ _ g _ _ (restrict_lr tl tr (fright Mi x)) (kp _ _ f _ _ (restrict_lr tl tr (fleft Mi x)) t).
Proof.
  rewrite (s_assoc H).
  exact (f_equal (fun p : {m & (descent a b (zrestr tl tr B) (refocus (zrestr tl tr M) Mi) (zrestr tl tr K) (refocus (zrestr tl tr L) m)
                               * descent a b (refocus (zrestr tl tr B) Mi) (zrestr tl tr M) (refocus (zrestr tl tr K) m) (zrestr tl tr L))%type} =>
                    let (m, pr) := p in (kp _ _ g _ _ (snd pr) (kp _ _ f _ _ (fst pr) t) : P (plug (out (zrestr tl tr K) (zrestr tl tr L)))))
                 (eq_sym (restrict_lr_split tl tr Mi x))).
Qed.

(** Rebase and unit through a restriction. *)
Lemma rebase_restrict (H : sort_laws) {aT bT} (tl : thin a aT) (tr : thin b bT) {B M : scopes aT bT}
    (f : morph P (zrestr tl tr B) (zrestr tl tr M)) {K1 L1 K2 L2}
    (x1 : descent aT bT B M K1 L1) (x2 : descent aT bT K1 L1 K2 L2) t :
  kp _ _ f _ _ (restrict_lr tl tr (fapp x1 x2)) t = kp _ _ (rebase_m (restrict_lr tl tr x1) f) _ _ (restrict_lr tl tr x2) t.
Proof. rewrite restrict_lr_fapp; apply (s_rebase H). Qed.

Lemma unit_restrict (H : sort_laws) {aT bT} (tl : thin a aT) (tr : thin b bT) {B M : scopes aT bT}
    {K L} (x : descent aT bT B (refocus M (focus B)) K (refocus L (focus K))) t :
  kp _ _ (unit_m (B := zrestr tl tr B) (M := zrestr tl tr M)) _ _ (restrict_lr tl tr x) t = t.
Proof. exact (s_unit H _ _ (zrestr tl tr K) (zrestr tl tr L) _ t). Qed.

End Laws.

End Generic.

(** ** Proving the laws of a Kleisli function

    [laws_proof] proves [sort_laws] of a Kleisli function, and
    [laws_proof using Lc] the [fam_laws] of one whose family contains
    another, with [Lc] the laws of the other's.  Each law is an induction
    on the term; every case is the induction hypothesis (at the same
    witness, or one more binder down), the carrier's law (through the
    restriction), or holds by computation. *)

Ltac head_of t := lazymatch t with ?g _ => head_of g | _ => t end.

(** The fixpoint behind a Kleisli function [k]. *)
Ltac kl_fix k :=
  let t := open_constr:(k _ _ _ _ _ _ _) in
  let t := eval cbv beta delta [k] in t in head_of t.

Ltac laws_case IH Lc :=
  first
    [ reflexivity
    | exact (IH _ _ _ _)
    | match goal with
      | |- context [under ?t ?x] =>
          first [ exact (IH _ _ (under t x) _)
                | lazymatch type of x with descent _ _ _ _ _ (refocus ?L _) => exact (IH _ (zup t L) (under t x) _) end ]
      end
    | apply (s_ext _ _ _ _ _ Lc); assumption
    | apply (rebase_restrict _ _ _ _ _ Lc)
    | unfold restrict;
      match goal with
      | |- context [@restrict_lr _ _ _ _ ?tl ?tr ?B ?M0 ?K ?L0 ?x] =>
          first
            [ exact (assoc_restrict _ _ _ _ _ Lc tl tr (B := B) (M := M0) _ _ _ x _)
            | lazymatch type of x with
              | descent _ _ _ (refocus ?M _) _ (refocus ?L _) =>
                  exact (unit_restrict _ _ _ _ _ Lc tl tr (B := B) (M := M) (K := K) (L := L) x _)
              end ]
      end ].

(** One law, after its parameters: by induction on the term. *)
Ltac laws_ind k Lc :=
  let h := kl_fix k in
  let IH := fresh "IH" in
  fix IH 4; intros ? ? ? t; destruct t; cbn [k h];
  first
    [ reflexivity
    | solve [unfold unit_m; cbv beta; f_equal; apply ext_var_same]
    | solve [f_equal; laws_case IH Lc] ].

Ltac laws_proof_with Lc :=
  lazymatch goal with
  | |- sort_laws _ _ _ _ ?k =>
      split;
      [ intros; reflexivity
      | intros ? ? ? ? Hfg; laws_ind k Lc
      | intros ? ? ? ? ? K2 L2 ?; revert K2 L2; laws_ind k Lc
      | intros ? ?; laws_ind k Lc
      | intros ? ? ? ? ?; laws_ind k Lc ]
  | |- @fam_laws _ _ _ _ _ _ _ _ _ _ ?k =>
      split;
      [ intros ? ? ? ? Hfg; laws_ind k Lc
      | intros ? ? ? ? ? K2 L2 ?; revert K2 L2; laws_ind k Lc
      | intros ? ?; laws_ind k Lc
      | intros ? ? ? ? ?; laws_ind k Lc ]
  end.

Tactic Notation "laws_proof" := laws_proof_with I.
Tactic Notation "laws_proof" "using" constr(Lc) := laws_proof_with Lc.

(** For a family over sorts [aT], [bT] around the focus, containing a family
    over the sorts [s] keeps: that family's morphisms and the family's
    Kleisli function along them. *)
Definition morph_in {aT bT} (s : mask) (B M : scopes aT bT) (F : arity (radd (lkept s aT) (S (rkept s aT bT)))) : Type :=
  morph (lkept s aT) (rkept s aT bT) (uncurry _ F) (zsub s B) (zsub s M).

Definition fam_kl_in (aT bT : nat) (s : mask) (P : vec (radd (lkept s aT) (S (rkept s aT bT))) -> Type) (T : vec (radd aT (S bT)) -> Type) : Type :=
  fam_kl (lkept s aT) (rkept s aT bT) P (tl_of s aT) (tr_of s aT bT) T.

(** ** System F *)

Inductive ty (N : nat) : Type :=
| tyvar (v : var N)
| tyarr (A B : ty N)
| tyall (B : ty (S N)).

Arguments tyvar {N} v.
Arguments tyarr {N} A B.
Arguments tyall {N} B.

Inductive tm (N K : nat) : Type :=
| tmvar (v : var K)
| lam (A : ty N) (b : tm N (S K))
| app (t u : tm N K)
| tlam (b : tm (S N) K)
| tapp (t : tm N K) (A : ty N).

Arguments tmvar {N K} v.
Arguments lam {N K} A b.
Arguments app {N K} t u.
Arguments tlam {N K} b.
Arguments tapp {N K} t A.

(** The user's three Kleisli functions.  Sorts: types 0, terms 1. *)

(** Types, focused on their one sort. *)
Fixpoint kl_ty {B M} (f : morph 0 0 (uncurry 1 ty) B M) {K L} (x : descent 0 0 B M K L) (A : ty @ K) : ty @ out K L :=
  match A with
  | tyvar v => f K L x v
  | tyarr A A' => tyarr (kl_ty f x A) (kl_ty f x A')
  | tyall A => tyall (kl_ty f (under 0 x) A)
  end.

(** Terms, focused on term variables. *)
Fixpoint kl_tm {B M} (f : morph 1 0 (uncurry 2 tm) B M) {K L} (x : descent 1 0 B M K L) (t : tm @ K) : tm @ out K L :=
  match t with
  | tmvar v => f K L x v
  | lam A u => lam A (kl_tm f (under 1 x) u)
  | app t u => app (kl_tm f x t) (kl_tm f x u)
  | tlam u => tlam (kl_tm f (under 0 x) u)
  | tapp t A => tapp (kl_tm f x t) A
  end.

(** Terms, focused on type variables.  Types are inside terms, over the
    first of their sorts ([x‹+ -›]). *)
Fixpoint kl_tmty {B M : scopes 0 1} (f : morph 0 0 (uncurry 1 ty) _ _)
    {K L} (x : descent 0 1 B M K L) (t : tm @ K) : tm @ out K L :=
  match t with
  | tmvar v => tmvar v
  | lam A u => lam (kl_ty f x‹+ -› A) (kl_tmty f (under 1 x) u)
  | app t u => app (kl_tmty f x t) (kl_tmty f x u)
  | tlam u => tlam (kl_tmty f (under 0 x) u)
  | tapp t A => tapp (kl_tmty f x t) (kl_ty f x‹+ -› A)
  end.

Definition ty_k : sort_kl 0 0 (uncurry 1 ty) := fun B M f K L x A => kl_ty f x A.
Definition tm_k : sort_kl 1 0 (uncurry 2 tm) := fun B M f K L x t => kl_tm f x t.
Definition tmty_k := fun (B M : scopes 0 1) f K L (x : descent 0 1 B M K L) t => kl_tmty f x t.

(** ** Their laws: routine inductions *)

Section Proofs.

Theorem ty_laws : sort_laws 0 0 (uncurry 1 ty) (fun K v => tyvar v) ty_k.
Proof. laws_proof. Qed.

Theorem tm_laws : sort_laws 1 0 (uncurry 2 tm) (fun K v => tmvar v) tm_k.
Proof. laws_proof. Qed.

(** Types inside terms, over the first of their sorts. *)
Theorem tmty_laws : fam_laws 0 0 (uncurry 1 ty) (fun K v => tyvar v) ty_k
    (tl_of (true :: false :: nil) 0) (tr_of (true :: false :: nil) 0 1) (uncurry 2 tm) tmty_k.
Proof. laws_proof using ty_laws. Qed.

End Proofs.

(** ** Using it: substituting at the root *)

Definition subst_tm {B M} (f : morph 1 0 (uncurry 2 tm) B M) (t : tm @ B) : tm @ out B M := kl_tm f here t.

(** ** One mask, any focus

    Three sorts, the inner family having the first and third: focused on
    any of them, the left part (nearest first) and the right part are read
    off by computation. *)
Let keep13 : mask := true :: false :: true :: nil.

Example mask_at_0 : tl_of keep13 0 = tdone /\ tr_of keep13 0 2 = tskip (tkeep tdone).
Proof. split; reflexivity. Qed.

Example mask_at_2 : tl_of keep13 2 = tskip (tkeep tdone) /\ tr_of keep13 2 0 = tdone.
Proof. split; reflexivity. Qed.

Example zsub_at_2 (r k : nat) x : zsub keep13 (pair (pair r (pair k tt)) (pair x tt) : scopes 2 0) = pair (pair k tt) (pair x tt).
Proof. reflexivity. Qed.
