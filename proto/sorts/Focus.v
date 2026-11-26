(** * Prototype: a substitution is focused on its sort

    Substituting sort [i] of a family over [a + 1 + b] sorts, the scopes
    are a zipper: the sorts to the left ([a], nearest first), [i]'s
    scope, and the sorts to the right ([b]); the family is at the zipper
    plugged back ([plug]).  The witness is the same shape: an [ext] for
    sort [i], and a context with an [ext] for every other sort ([cwit]).
    The other sorts are the same context on both sides, so nothing
    containing only them is visited; nothing is cut out of a vector or
    put back, so there are no casts.  Build with
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

(** ** Vectors, zippers, families *)

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

(** The other sorts around a focus. *)
Definition cvec (a b : nat) : Type := both (vec a) (vec b).

Definition plug (a b : nat) (C : cvec a b) (x : nat) : vec (radd a (S b)) := rev_app a (S b) (first C) (pair x (second C)).

(** A curried family over [n] scopes, seen through a vector. *)
Fixpoint arity (n : nat) : Type := match n with 0 => Type | S n => nat -> arity n end.

Fixpoint uncurry (n : nat) : arity n -> vec n -> Type :=
  match n as n0 return arity n0 -> vec n0 -> Type with
  | 0 => fun F _ => F
  | S n => fun F x => uncurry n (F (first x)) (second x)
  end.

(** Some of [n] sorts, in order. *)
Inductive thin : nat -> nat -> Type :=
| tdone : thin 0 0
| tkeep {m n} : thin m n -> thin (S m) (S n)
| tskip {m n} : thin m n -> thin m (S n).

Fixpoint restr {m n} (th : thin m n) : vec n -> vec m :=
  match th in thin m0 n0 return vec n0 -> vec m0 with
  | tdone => fun _ => tt
  | tkeep th => fun x => pair (first x) (restr th (second x))
  | tskip th => fun x => restr th (second x)
  end.

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
  | tdone => fun _ _ _ _ _ => tt
  | tkeep th => fun B M K L w => pair (first w) (wrestr th _ _ _ _ (second w))
  | tskip th => fun B M K L w => wrestr th _ _ _ _ (second w)
  end.

(** The other sorts' witnesses around a focus. *)
Definition cwit (a b : nat) (B M K L : cvec a b) : Type :=
  both (wit a (first B) (first M) (first K) (first L)) (wit b (second B) (second M) (second K) (second L)).

Definition chome {a b B M} : cwit a b B M B M := pair (whome a _ _) (whome b _ _).

(** Under a binder of sort [t] (counting from the left, as the user does),
    not the one focused on. *)
Definition cup (a b t : nat) (C : cvec a b) : cvec a b :=
  if Nat.ltb t a then pair (upd a (a - S t) (S (get a (a - S t) (first C))) (first C)) (second C)
  else pair (first C) (upd b (t - S a) (S (get b (t - S a) (second C))) (second C)).

Definition cunder {a b} (t : nat) {B M K L} (w : cwit a b B M K L) : cwit a b B M (cup a b t K) (cup a b t L) :=
  match Nat.ltb t a as c return
    cwit a b B M
      (if c then pair (upd a (a - S t) (S (get a (a - S t) (first K))) (first K)) (second K)
       else pair (first K) (upd b (t - S a) (S (get b (t - S a) (second K))) (second K)))
      (if c then pair (upd a (a - S t) (S (get a (a - S t) (first L))) (first L)) (second L)
       else pair (first L) (upd b (t - S a) (S (get b (t - S a) (second L))) (second L)))
  with
  | true => pair (wunder a (a - S t) _ _ _ _ (first w)) (second w)
  | false => pair (first w) (wunder b (t - S a) _ _ _ _ (second w))
  end.

Definition capp {a b B M K L K' L'} (w1 : cwit a b B M K L) (w2 : cwit a b K L K' L') : cwit a b B M K' L' :=
  pair (wapp a _ _ _ _ _ _ (first w1) (first w2)) (wapp b _ _ _ _ _ _ (second w1) (second w2)).

Definition crestr {a b aT bT} (tl : thin a aT) (tr : thin b bT) (C : cvec aT bT) : cvec a b :=
  pair (restr tl (first C)) (restr tr (second C)).

Definition cwrestr {a b aT bT} (tl : thin a aT) (tr : thin b bT) {B M K L} (w : cwit aT bT B M K L)
    : cwit a b (crestr tl tr B) (crestr tl tr M) (crestr tl tr K) (crestr tl tr L) :=
  pair (wrestr tl _ _ _ _ (first w)) (wrestr tr _ _ _ _ (second w)).

(** ** Morphisms, Kleisli functions and their laws *)

Section Generic.

Context (a b : nat).
Notation n := (radd a (S b)).

(** A morphism of the focused sort into its carrier [P], from the other
    sorts' bases [B] (their other side [M]) and the sort's [Bi] to [Mi]. *)
Definition morph (P : vec n -> Type) (B M : cvec a b) (Bi Mi : nat) : Type :=
  forall C C' Ki Li, cwit a b B M C C' -> ext Bi Mi Ki Li -> var Ki -> P (plug a b C Li).

Definition rebase_m {P B M Bi Mi C1 C1' K1 L1} (w1 : cwit a b B M C1 C1') (e1 : ext Bi Mi K1 L1)
    (f : morph P B M Bi Mi) : morph P C1 C1' K1 L1 :=
  fun C C' Ki Li w e v => f C C' Ki Li (capp w1 w) (ext_app e1 e) v.

Definition sort_kl (P : vec n -> Type) : Type :=
  forall B M Bi Mi (f : morph P B M Bi Mi) C C' Ki Li, cwit a b B M C C' -> ext Bi Mi Ki Li ->
    P (plug a b C Ki) -> P (plug a b C Li).

(** A family over more sorts, focused on the same sort ([tl], [tr] place
    the carrier's other sorts among the family's). *)
Definition fam_kl (P : vec n -> Type) {aT bT} (tl : thin a aT) (tr : thin b bT) (T : vec (radd aT (S bT)) -> Type) : Type :=
  forall B M Bi Mi (f : morph P (crestr tl tr B) (crestr tl tr M) Bi Mi) C C' Ki Li, cwit aT bT B M C C' -> ext Bi Mi Ki Li ->
    T (plug aT bT C Ki) -> T (plug aT bT C Li).

Section Laws.

Context (P : vec n -> Type) (tv : forall C K, var K -> P (plug a b C K)) (kp : sort_kl P).

Definition unit_m {B M Bi} : morph P B M Bi Bi := fun C C' Ki Li w e v => tv C Li (ext_var e v).

Definition comp_m {B M Bi Mi Pi} (g : morph P B M Mi Pi) (f : morph P B M Bi Mi) : morph P B M Bi Pi :=
  fun C C' Ki Li w e v => kp _ _ _ _ g _ _ _ _ w (ext_right Mi e) (f C C' Ki (ext_mid Mi e) w (ext_left Mi e) v).

Record sort_laws : Prop := {
  s_var : forall B M Bi Mi (f : morph P B M Bi Mi) C C' Ki Li (w : cwit a b B M C C') (e : ext Bi Mi Ki Li) v,
    kp _ _ _ _ f _ _ _ _ w e (tv C Ki v) = f C C' Ki Li w e v;
  s_ext : forall B M Bi Mi (f g : morph P B M Bi Mi), (forall C C' Ki Li w e v, f C C' Ki Li w e v = g C C' Ki Li w e v) ->
    forall C C' Ki Li (w : cwit a b B M C C') (e : ext Bi Mi Ki Li) t, kp _ _ _ _ f _ _ _ _ w e t = kp _ _ _ _ g _ _ _ _ w e t;
  s_rebase : forall B M Bi Mi (f : morph P B M Bi Mi) C1 C1' K1 L1 C2 C2' K2 L2
      (w1 : cwit a b B M C1 C1') (e1 : ext Bi Mi K1 L1) (w2 : cwit a b C1 C1' C2 C2') (e2 : ext K1 L1 K2 L2) t,
    kp _ _ _ _ f _ _ _ _ (capp w1 w2) (ext_app e1 e2) t = kp _ _ _ _ (rebase_m w1 e1 f) _ _ _ _ w2 e2 t;
  s_unit : forall B M Bi C C' Ki (w : cwit a b B M C C') (e : ext Bi Bi Ki Ki) t, kp _ _ _ _ unit_m _ _ _ _ w e t = t;
  s_assoc : forall B M Bi Mi Pi (g : morph P B M Mi Pi) (f : morph P B M Bi Mi) C C' Ki Li
      (w : cwit a b B M C C') (e : ext Bi Pi Ki Li) t,
    kp _ _ _ _ (comp_m g f) _ _ _ _ w e t = kp _ _ _ _ g _ _ _ _ w (ext_right Mi e) (kp _ _ _ _ f _ _ _ _ w (ext_left Mi e) t) }.

Record fam_laws {aT bT} (tl : thin a aT) (tr : thin b bT) (T : vec (radd aT (S bT)) -> Type) (k : fam_kl P tl tr T) : Prop := {
  f_ext : forall B M Bi Mi (f g : morph P (crestr tl tr B) (crestr tl tr M) Bi Mi),
    (forall C C' Ki Li w e v, f C C' Ki Li w e v = g C C' Ki Li w e v) ->
    forall C C' Ki Li (w : cwit aT bT B M C C') (e : ext Bi Mi Ki Li) t, k _ _ _ _ f _ _ _ _ w e t = k _ _ _ _ g _ _ _ _ w e t;
  f_rebase : forall B M Bi Mi (f : morph P (crestr tl tr B) (crestr tl tr M) Bi Mi) C1 C1' K1 L1 C2 C2' K2 L2
      (w1 : cwit aT bT B M C1 C1') (e1 : ext Bi Mi K1 L1) (w2 : cwit aT bT C1 C1' C2 C2') (e2 : ext K1 L1 K2 L2) t,
    k _ _ _ _ f _ _ _ _ (capp w1 w2) (ext_app e1 e2) t = k _ _ _ _ (rebase_m (cwrestr tl tr w1) e1 f) _ _ _ _ w2 e2 t;
  f_unit : forall B M Bi C C' Ki (w : cwit aT bT B M C C') (e : ext Bi Bi Ki Ki) t, k _ _ _ _ unit_m _ _ _ _ w e t = t;
  f_assoc : forall B M Bi Mi Pi (g : morph P (crestr tl tr B) (crestr tl tr M) Mi Pi) (f : morph P (crestr tl tr B) (crestr tl tr M) Bi Mi)
      C C' Ki Li (w : cwit aT bT B M C C') (e : ext Bi Pi Ki Li) t,
    k _ _ _ _ (comp_m g f) _ _ _ _ w e t = k _ _ _ _ g _ _ _ _ w (ext_right Mi e) (k _ _ _ _ f _ _ _ _ w (ext_left Mi e) t) }.

End Laws.

End Generic.

(** ** System F: the user's own families *)

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

Notation tyP := (uncurry 1 ty).
Notation tmP := (uncurry 2 tm).

(** Types: one sort, focused with nothing around it. *)
Fixpoint kl_ty {B M Bi Mi} (f : morph 0 0 tyP B M Bi Mi) {C C' Ki Li} (w : cwit 0 0 B M C C') (e : ext Bi Mi Ki Li)
    (A : ty Ki) : ty Li :=
  match A with
  | tyvar v => f C C' Ki Li w e v
  | tyarr A A' => tyarr (kl_ty f w e A) (kl_ty f w e A')
  | tyall A => tyall (kl_ty f w (ext_under e) A)
  end.

(** Terms, focused on term variables: the type scope is on the left. *)
Fixpoint kl_tm {B M Bi Mi} (f : morph 1 0 tmP B M Bi Mi) {C C' Ki Li} (w : cwit 1 0 B M C C') (e : ext Bi Mi Ki Li)
    (t : tm (first (first C)) Ki) : tm (first (first C)) Li :=
  match t with
  | tmvar v => f C C' Ki Li w e v
  | lam A u => lam A (kl_tm f w (ext_under e) u)
  | app t u => app (kl_tm f w e t) (kl_tm f w e u)
  | tlam u => tlam (kl_tm f (cunder 0 w) e u)
  | tapp t A => tapp (kl_tm f w e t) A
  end.

(** Terms, focused on type variables: the term scope is on the right, and
    the type morphism does not see it. *)
Fixpoint kl_tmty {B M Bi Mi} (f : morph 0 0 tyP (crestr tdone (tskip tdone) B) (crestr tdone (tskip tdone) M) Bi Mi)
    {C C' Ki Li} (w : cwit 0 1 B M C C') (e : ext Bi Mi Ki Li) (t : tm Ki (first (second C))) : tm Li (first (second C)) :=
  match t with
  | tmvar v => tmvar v
  | lam A u => lam (kl_ty f (cwrestr tdone (tskip tdone) w) e A) (kl_tmty f (cunder 1 w) e u)
  | app t u => app (kl_tmty f w e t) (kl_tmty f w e u)
  | tlam u => tlam (kl_tmty f w (ext_under e) u)
  | tapp t A => tapp (kl_tmty f w e t) (kl_ty f (cwrestr tdone (tskip tdone) w) e A)
  end.

Definition ty_k : sort_kl 0 0 tyP := fun B M Bi Mi f C C' Ki Li w e A => kl_ty f w e A.
Definition tm_k : sort_kl 1 0 tmP := fun B M Bi Mi f C C' Ki Li w e t => kl_tm f w e t.
Definition tmty_k : fam_kl 0 0 tyP tdone (tskip tdone) tmP := fun B M Bi Mi f C C' Ki Li w e t => kl_tmty f w e t.

(** ** Their laws: routine inductions *)

Section Proofs.

Lemma kl_ty_ext {B M Bi Mi} (f g : morph 0 0 tyP B M Bi Mi) :
  (forall C C' Ki Li w e v, f C C' Ki Li w e v = g C C' Ki Li w e v) ->
  forall C C' Ki Li (w : cwit 0 0 B M C C') (e : ext Bi Mi Ki Li) A, kl_ty f w e A = kl_ty g w e A.
Proof. intros H C C' Ki Li w e A; revert Li e; induction A; intros Li e; cbn [kl_ty]; f_equal; auto. Qed.

Lemma kl_ty_rebase {B M Bi Mi} (f : morph 0 0 tyP B M Bi Mi) C1 C1' K1 L1 C2 C2' K2 L2
    (w1 : cwit 0 0 B M C1 C1') (e1 : ext Bi Mi K1 L1) (w2 : cwit 0 0 C1 C1' C2 C2') (e2 : ext K1 L1 K2 L2) A :
  kl_ty f (capp w1 w2) (ext_app e1 e2) A = kl_ty (rebase_m 0 0 w1 e1 f) w2 e2 A.
Proof. revert L2 e2; induction A; intros L2 e2; cbn [kl_ty]; f_equal; auto; exact (IHA _ (ext_under e2)). Qed.

Lemma kl_ty_unit {B M Bi} C C' Ki (w : cwit 0 0 B M C C') (e : ext Bi Bi Ki Ki) A :
  kl_ty (unit_m 0 0 tyP (fun C K v => tyvar v)) w e A = A.
Proof. induction A; cbn [kl_ty]; [unfold unit_m; f_equal; apply ext_var_same|f_equal; auto..]. Qed.

Lemma kl_ty_assoc {B M Bi Mi Pi} (g : morph 0 0 tyP B M Mi Pi) (f : morph 0 0 tyP B M Bi Mi)
    C C' Ki Li (w : cwit 0 0 B M C C') (e : ext Bi Pi Ki Li) A :
  kl_ty (comp_m 0 0 tyP ty_k g f) w e A = kl_ty g w (ext_right Mi e) (kl_ty f w (ext_left Mi e) A).
Proof. revert Li e; induction A; intros Li e; cbn [kl_ty]; f_equal; auto; exact (IHA _ (ext_under e)). Qed.

Theorem ty_laws : sort_laws 0 0 tyP (fun C K v => tyvar v) ty_k.
Proof.
  split; cbn [ty_k].
  - reflexivity.
  - intros; apply kl_ty_ext; assumption.
  - intros; apply kl_ty_rebase.
  - intros; apply kl_ty_unit.
  - intros; apply kl_ty_assoc.
Qed.

Lemma kl_tm_ext {B M Bi Mi} (f g : morph 1 0 tmP B M Bi Mi) (H : forall C C' Ki Li w e v, f C C' Ki Li w e v = g C C' Ki Li w e v) :
  forall C C' Ki Li (w : cwit 1 0 B M C C') (e : ext Bi Mi Ki Li) t, kl_tm f w e t = kl_tm g w e t.
Proof. fix IH 7; intros C C' Ki Li w e t; destruct t; cbn [kl_tm]; f_equal; auto. Qed.

Lemma kl_tm_rebase {B M Bi Mi} (f : morph 1 0 tmP B M Bi Mi) C1 C1' K1 L1 (w1 : cwit 1 0 B M C1 C1') (e1 : ext Bi Mi K1 L1) :
  forall C2 C2' K2 L2 (w2 : cwit 1 0 C1 C1' C2 C2') (e2 : ext K1 L1 K2 L2) t,
  kl_tm f (capp w1 w2) (ext_app e1 e2) t = kl_tm (rebase_m 1 0 w1 e1 f) w2 e2 t.
Proof.
  fix IH 7; intros C2 C2' K2 L2 w2 e2 t; destruct t; cbn [kl_tm]; f_equal;
    first [reflexivity | apply IH | exact (IH _ _ _ _ w2 (ext_under e2) t) | exact (IH _ _ _ _ (cunder 0 w2) e2 t)].
Qed.

Lemma kl_tm_unit {B M Bi} : forall C C' Ki (w : cwit 1 0 B M C C') (e : ext Bi Bi Ki Ki) t,
  kl_tm (unit_m 1 0 tmP (fun C K v => tmvar v)) w e t = t.
Proof. fix IH 6; intros C C' Ki w e t; destruct t; cbn [kl_tm]; [unfold unit_m; f_equal; apply ext_var_same|f_equal; auto..]. Qed.

Lemma kl_tm_assoc {B M Bi Mi Pi} (g : morph 1 0 tmP B M Mi Pi) (f : morph 1 0 tmP B M Bi Mi) :
  forall C C' Ki Li (w : cwit 1 0 B M C C') (e : ext Bi Pi Ki Li) t,
  kl_tm (comp_m 1 0 tmP tm_k g f) w e t = kl_tm g w (ext_right Mi e) (kl_tm f w (ext_left Mi e) t).
Proof.
  fix IH 7; intros C C' Ki Li w e t; destruct t; cbn [kl_tm]; f_equal;
    first [reflexivity | apply IH | exact (IH _ _ _ _ w (ext_under e) t) | exact (IH _ _ _ _ (cunder 0 w) e t)].
Qed.

Theorem tm_laws : sort_laws 1 0 tmP (fun C K v => tmvar v) tm_k.
Proof.
  split; cbn [tm_k].
  - reflexivity.
  - intros B M Bi Mi f g H; exact (kl_tm_ext f g H).
  - intros B M Bi Mi f C1 C1' K1 L1 C2 C2' K2 L2 w1 e1; exact (kl_tm_rebase f C1 C1' K1 L1 w1 e1 C2 C2' K2 L2).
  - intros B M Bi; exact kl_tm_unit.
  - intros B M Bi Mi Pi g f; exact (kl_tm_assoc g f).
Qed.

Lemma kl_tmty_ext {B M Bi Mi} (f g : morph 0 0 tyP (crestr tdone (tskip tdone) B) (crestr tdone (tskip tdone) M) Bi Mi)
    (H : forall C C' Ki Li w e v, f C C' Ki Li w e v = g C C' Ki Li w e v) :
  forall C C' Ki Li (w : cwit 0 1 B M C C') (e : ext Bi Mi Ki Li) t, kl_tmty f w e t = kl_tmty g w e t.
Proof. fix IH 7; intros C C' Ki Li w e t; destruct t; cbn [kl_tmty]; f_equal; auto; apply kl_ty_ext; exact H. Qed.

Lemma kl_tmty_rebase {B M Bi Mi} (f : morph 0 0 tyP (crestr tdone (tskip tdone) B) (crestr tdone (tskip tdone) M) Bi Mi)
    C1 C1' K1 L1 (w1 : cwit 0 1 B M C1 C1') (e1 : ext Bi Mi K1 L1) :
  forall C2 C2' K2 L2 (w2 : cwit 0 1 C1 C1' C2 C2') (e2 : ext K1 L1 K2 L2) t,
  kl_tmty f (capp w1 w2) (ext_app e1 e2) t = kl_tmty (rebase_m 0 0 (cwrestr tdone (tskip tdone) w1) e1 f) w2 e2 t.
Proof.
  fix IH 7; intros C2 C2' K2 L2 w2 e2 t; destruct t; cbn [kl_tmty]; f_equal;
    first [exact (kl_ty_rebase f _ _ _ _ _ _ _ _ (cwrestr tdone (tskip tdone) w1) e1 (cwrestr tdone (tskip tdone) w2) e2 _)
          | apply IH | exact (IH _ _ _ _ w2 (ext_under e2) t) | exact (IH _ _ _ _ (cunder 1 w2) e2 t)].
Qed.

Lemma kl_tmty_unit {B M Bi} : forall C C' Ki (w : cwit 0 1 B M C C') (e : ext Bi Bi Ki Ki) t,
  kl_tmty (unit_m 0 0 tyP (fun C K v => tyvar v)) w e t = t.
Proof. fix IH 6; intros C C' Ki w e t; destruct t; cbn [kl_tmty]; f_equal; auto; apply kl_ty_unit. Qed.

Lemma kl_tmty_assoc {B M Bi Mi Pi} (g : morph 0 0 tyP (crestr tdone (tskip tdone) B) (crestr tdone (tskip tdone) M) Mi Pi)
    (f : morph 0 0 tyP (crestr tdone (tskip tdone) B) (crestr tdone (tskip tdone) M) Bi Mi) :
  forall C C' Ki Li (w : cwit 0 1 B M C C') (e : ext Bi Pi Ki Li) t,
  kl_tmty (comp_m 0 0 tyP ty_k g f) w e t = kl_tmty g w (ext_right Mi e) (kl_tmty f w (ext_left Mi e) t).
Proof.
  fix IH 7; intros C C' Ki Li w e t; destruct t; cbn [kl_tmty]; f_equal;
    first [apply kl_ty_assoc | apply IH | exact (IH _ _ _ _ w (ext_under e) t) | exact (IH _ _ _ _ (cunder 1 w) e t)].
Qed.

Theorem tmty_laws : fam_laws 0 0 tyP (fun C K v => tyvar v) ty_k tdone (tskip tdone) tmP tmty_k.
Proof.
  split; cbn [tmty_k].
  - intros B M Bi Mi f g H; exact (kl_tmty_ext f g H).
  - intros B M Bi Mi f C1 C1' K1 L1 C2 C2' K2 L2 w1 e1; exact (kl_tmty_rebase f C1 C1' K1 L1 w1 e1 C2 C2' K2 L2).
  - intros B M Bi; exact kl_tmty_unit.
  - intros B M Bi Mi Pi g f; exact (kl_tmty_assoc g f).
Qed.

(** ** Moving a type substitution past a term substitution

    The type witness [e0] and the term witness [e1]: each substitution
    has the other's in its context, read from the side it is on.  The term
    morphism mapped by the type substitution ([tmap]) substitutes its
    results' types, at its context's type witness read back. *)

(** Contexts with one other sort: on the left of term variables, on the
    right of type variables. *)
Definition lctx (N : nat) : cvec 1 0 := pair (pair N tt) tt.
Definition rctx (J : nat) : cvec 0 1 := pair tt (pair J tt).
Definition lwit {N M K L} (e : ext N M K L) : cwit 1 0 (lctx N) (lctx M) (lctx K) (lctx L) := pair (pair e tt) tt.
Definition rwit {N M K L} (e : ext N M K L) : cwit 0 1 (rctx N) (rctx M) (rctx K) (rctx L) := pair tt (pair e tt).

Definition tmap {Gs Gt Bi Mi} (h : morph 0 0 tyP (pair tt tt) (pair tt tt) Gs Gt)
    (f : morph 1 0 tmP (lctx Gs) (lctx Gt) Bi Mi) : morph 1 0 tmP (lctx Gt) (lctx Gs) Bi Mi :=
  fun C C' Ki Li w e v =>
    kl_tmty h (rwit (ext_flip e)) (ext_flip (first (first w))) (f _ _ _ _ (lwit (ext_flip (first (first w)))) e v).

Lemma commute {Gs Gt Bi Mi} (h : morph 0 0 tyP (pair tt tt) (pair tt tt) Gs Gt) (f : morph 1 0 tmP (lctx Gs) (lctx Gt) Bi Mi) :
  forall Ks Kt Ki Li (e0 : ext Gs Gt Ks Kt) (e1 : ext Bi Mi Ki Li) (t : tm Ks Ki),
  kl_tmty h (rwit (ext_flip e1)) e0 (kl_tm f (lwit e0) e1 t) = kl_tm (tmap h f) (lwit (ext_flip e0)) e1 (kl_tmty h (rwit e1) e0 t).
Proof.
  fix IH 7; intros Ks Kt Ki Li e0 e1 t; destruct t; cbn [kl_tm kl_tmty].
  - unfold tmap, lwit; cbn [first second]; rewrite ext_flip_flip; reflexivity.
  - f_equal; exact (IH _ _ _ _ e0 (ext_under e1) t).
  - f_equal; apply IH.
  - f_equal; exact (IH _ _ _ _ (ext_under e0) e1 t).
  - f_equal; apply IH.
Qed.

End Proofs.

(** ** Moving the focus

    Moving the focus one sort to the right leaves the plugged vector the
    same, by computation, whatever the number of sorts: what relates a
    substitution of one sort to one of the next is no cast. *)
Lemma plug_move a b (l : vec a) x y (r : vec b) :
  plug a (S b) (pair l (pair y r)) x = plug (S a) b (pair (pair x l) r) y.
Proof. reflexivity. Qed.
