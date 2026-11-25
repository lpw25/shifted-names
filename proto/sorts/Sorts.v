(** * Prototype: syntaxes with any number of sorts of variable

    Checks the scheme of [docs/sorts.md].  A family is indexed by a vector
    of nats, one scope per sort, a sort being a position; a family inside
    another is indexed by a prefix of its vector.  A sort's morphisms,
    Kleisli functions and laws are generic over the vector's length and
    the position.  Instances: System F (types over the first sort, terms
    over two) and a calculus with three (types, regions, terms).  Standalone:
    only [Var] and the witnesses of [Syntax] are used.  Build with
      rocq compile -R theories ShiftedNames proto/sorts/Sorts.v *)

From Stdlib Require Import Arith Lia.
From ShiftedNames.Core Require Import Strict Label Var Scoped Indexed.
From ShiftedNames.Core Require Syntax.
Import Syntax (ext, ext_here, ext_under, ext_app, ext_mid, ext_left, ext_right, ext_var, ext_var_same).

(** Pairs with eta, so that a vector taken apart and put back is the same
    vector. *)
Set Primitive Projections.
Record both (A B : Type) : Type := pair { first : A; second : B }.
Unset Primitive Projections.
Arguments pair {A B} first second.
Arguments first {A B} _.
Arguments second {A B} _.

(** ** The generic part

    A family is indexed by a vector of nats, one scope per sort; a sort is
    a position in the vector.  A family inside another (types inside
    terms) is indexed by a prefix of the other's vector. *)

Fixpoint vec (n : nat) : Type := match n with 0 => unit | S n => both nat (vec n) end.

(** Sort [i]'s scope replaced. *)
Fixpoint upd (n : nat) (i : nat) (k : nat) : vec n -> vec n :=
  match n as n0 return vec n0 -> vec n0 with
  | 0 => fun x => x
  | S n => fun x => match i with 0 => pair k (second x) | S i => pair (first x) (upd n i k (second x)) end
  end.

(** The first [m] scopes (of a vector at least as long). *)
Fixpoint prefix (m n : nat) : vec n -> vec m :=
  match m as m0 return vec n -> vec m0 with
  | 0 => fun _ => tt
  | S m => match n as n0 return vec n0 -> vec (S m) with
           | 0 => fun _ => pair 0 (prefix m 0 tt)
           | S n => fun x => pair (first x) (prefix m n (second x))
           end
  end.

(** Substituting sort [i]: the other sorts' binders crossed, each over
    its base with the base unchanged ([b] the bases, [j] the scopes
    reached; [i]'s own component is unused).  Internally the position is
    an option, [None] once it has been passed. *)
Definition here_ty (o : option nat) (B J : nat) : Type :=
  match o with Some 0 => unit | _ => ext B B J J end.

Definition tl (o : option nat) : option nat := match o with Some (S i) => Some i | _ => None end.

Fixpoint lifts' (n : nat) (o : option nat) : vec n -> vec n -> Type :=
  match n as n0 return vec n0 -> vec n0 -> Type with
  | 0 => fun _ _ => unit
  | S n => fun b j => both (here_ty o (first b) (first j)) (lifts' n (tl o) (second b) (second j))
  end.

Definition lifts (n i : nat) : vec n -> vec n -> Type := lifts' n (Some i).

Fixpoint lhere' (n : nat) (o : option nat) : forall b, lifts' n o b b :=
  match n as n0 return forall b : vec n0, lifts' n0 o b b with
  | 0 => fun _ => tt
  | S n => fun b =>
      pair (match o as o0 return here_ty o0 (first b) (first b) with
            | Some 0 => tt
            | Some (S _) => ext_here
            | None => ext_here
            end) (lhere' n (tl o) (second b))
  end.

Definition lhere (n i : nat) : forall b, lifts n i b b := lhere' n (Some i).

Fixpoint lcomp' (n : nat) (o : option nat) : forall b j1 j2, lifts' n o b j1 -> lifts' n o j1 j2 -> lifts' n o b j2 :=
  match n as n0 return forall b j1 j2 : vec n0, lifts' n0 o b j1 -> lifts' n0 o j1 j2 -> lifts' n0 o b j2 with
  | 0 => fun _ _ _ _ _ => tt
  | S n => fun b j1 j2 w1 w2 =>
      pair (match o as o0
                  return here_ty o0 (first b) (first j1) -> here_ty o0 (first j1) (first j2) ->
                         here_ty o0 (first b) (first j2) with
            | Some 0 => fun _ _ => tt
            | Some (S _) => fun x y => ext_app x y
            | None => fun x y => ext_app x y
            end (first w1) (first w2))
           (lcomp' n (tl o) (second b) (second j1) (second j2) (second w1) (second w2))
  end.

Definition lcomp {n i b j1 j2} : lifts n i b j1 -> lifts n i j1 j2 -> lifts n i b j2 := lcomp' n (Some i) b j1 j2.

Section Generic.

Context (n : nat) (i : nat).

(** A morphism of sort [i] into its carrier [P] (over [n] sorts):
    liftable along [i]'s binders ([ext]) and along the others' ([lifts]). *)
Definition morph (P : vec n -> Type) (N M : nat) (b : vec n) : Type :=
  forall K L, ext N M K L -> forall j, lifts n i b j -> var K -> P (upd n i L j).

Definition rebase_m {P N M K L b} (e1 : ext N M K L) (f : morph P N M b) : morph P K L b :=
  fun K' L' e j w v => f K' L' (ext_app e1 e) j w v.

Definition orebase_m {P N M b j1} (w1 : lifts n i b j1) (f : morph P N M b) : morph P N M j1 :=
  fun K L e j2 w2 v => f K L e j2 (lcomp w1 w2) v.

(** The carrier's own Kleisli function, and that of a family over a
    longer vector ([nT] sorts, the carrier's first). *)
Record sort_kl (P : vec n -> Type) := mk_skl {
  skl : forall {N M b} (f : morph P N M b) {K L} (e : ext N M K L) {j} (w : lifts n i b j),
          P (upd n i K j) -> P (upd n i L j) }.

Record fam_kl (P : vec n -> Type) (nT : nat) (T : vec nT -> Type) := mk_fkl {
  fkl : forall {N M b} (f : morph P N M b) {K L} (e : ext N M K L) {jT} (w : lifts n i b (prefix n nT jT)),
          T (upd nT i K jT) -> T (upd nT i L jT) }.

Arguments skl {P} _ {N M b} f {K L} e {j} w _.
Arguments fkl {P nT T} _ {N M b} f {K L} e {jT} w _.

Section Laws.

Context (P : vec n -> Type) (tv : forall K j, var K -> P (upd n i K j)) (kp : sort_kl P).

Definition unit_m {N b} : morph P N N b := fun K L e j w v => tv L j (ext_var e v).

Definition comp_m {N M P' b} (g : morph P M P' b) (f : morph P N M b) : morph P N P' b :=
  fun K L e j w v => skl kp g (ext_right M e) w (f K (ext_mid M e) (ext_left M e) j w v).

(** The laws of a sort's syntax: the current ones, the other sorts'
    witness threaded through, and [orebase]: those witnesses compose. *)
Record sort_laws : Prop := {
  s_var : forall N M b (f : morph P N M b) K L (e : ext N M K L) j (w : lifts n i b j) v,
    skl kp f e w (tv K j v) = f K L e j w v;
  s_ext : forall N M b (f g : morph P N M b), (forall K L e j w v, f K L e j w v = g K L e j w v) ->
    forall K L (e : ext N M K L) j (w : lifts n i b j) t, skl kp f e w t = skl kp g e w t;
  s_rebase : forall N M b (f : morph P N M b) K L K' L' (e1 : ext N M K L) (e2 : ext K L K' L') j
      (w : lifts n i b j) t,
    skl kp f (ext_app e1 e2) w t = skl kp (rebase_m e1 f) e2 w t;
  s_orebase : forall N M b (f : morph P N M b) K L (e : ext N M K L) j1 j2 (w1 : lifts n i b j1)
      (w2 : lifts n i j1 j2) t,
    skl kp f e (lcomp w1 w2) t = skl kp (orebase_m w1 f) e w2 t;
  s_unit : forall N K (e : ext N N K K) b j (w : lifts n i b j) t, skl kp (unit_m (b := b)) e w t = t;
  s_assoc : forall N M P' b (g : morph P M P' b) (f : morph P N M b) K L (e : ext N P' K L) j
      (w : lifts n i b j) t,
    skl kp (comp_m g f) e w t = skl kp g (ext_right M e) w (skl kp f (ext_left M e) w t) }.

(** A family over a longer vector: the same laws, along the carrier's
    morphisms. *)
Record fam_laws (nT : nat) (T : vec nT -> Type) (k : fam_kl P nT T) : Prop := {
  f_ext : forall N M b (f g : morph P N M b), (forall K L e j w v, f K L e j w v = g K L e j w v) ->
    forall K L (e : ext N M K L) jT (w : lifts n i b (prefix n nT jT)) t, fkl k f e w t = fkl k g e w t;
  f_rebase : forall N M b (f : morph P N M b) K L K' L' (e1 : ext N M K L) (e2 : ext K L K' L') jT
      (w : lifts n i b (prefix n nT jT)) t,
    fkl k f (ext_app e1 e2) w t = fkl k (rebase_m e1 f) e2 w t;
  f_orebase : forall N M b (f : morph P N M b) K L (e : ext N M K L) j1 jT (w1 : lifts n i b j1)
      (w2 : lifts n i j1 (prefix n nT jT)) t,
    fkl k f e (lcomp w1 w2) t = fkl k (orebase_m w1 f) e w2 t;
  f_unit : forall N K (e : ext N N K K) b jT (w : lifts n i b (prefix n nT jT)) t,
    fkl k (unit_m (b := b)) e w t = t;
  f_assoc : forall N M P' b (g : morph P M P' b) (f : morph P N M b) K L (e : ext N P' K L) jT
      (w : lifts n i b (prefix n nT jT)) t,
    fkl k (comp_m g f) e w t = fkl k g (ext_right M e) w (fkl k f (ext_left M e) w t) }.

End Laws.

End Generic.

Arguments skl {n i P} _ {N M b} f {K L} e {j} w _.
Arguments fkl {n i P nT T} _ {N M b} f {K L} e {jT} w _.

(** ** System F: types are sort 0, terms sort 1; types over the first *)

Inductive ty (N : nat) : Type :=
| tyvar (v : var N)
| tyarr (A B : ty N)
| tyall (B : ty (S N)).

Arguments tyvar {N} v.
Arguments tyarr {N} A B.
Arguments tyall {N} B.

(** [tm N K]: [N] type variables, [K] term variables. *)
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

(** The families over their vectors. *)
Definition Ty (x : vec 1) : Type := ty (first x).
Definition Tm (x : vec 2) : Type := tm (first x) (first (second x)).

(** Types, the type sort: the other sorts' witness is threaded through
    (there are none). *)
Fixpoint kl_ty {N M b} (f : morph 1 0 Ty N M b) {K L} (e : ext N M K L) (j : vec 1)
    (w : lifts 1 0 b j) (A : ty K) : ty L :=
  match A with
  | tyvar v => f K L e j w v
  | tyarr A B => tyarr (kl_ty f e j w A) (kl_ty f e j w B)
  | tyall B => tyall (kl_ty f (ext_under e) j w B)
  end.

Definition ty_k : sort_kl 1 0 Ty := mk_skl _ _ _ (fun N M b f K L e j w A => kl_ty f e j w A).

(** Terms, the type sort: a family over two sorts with the carrier over
    the first; types inside are the carrier itself. *)
Fixpoint kl_tmty {J N M b} (f : morph 1 0 Ty N M b) {K L} (e : ext N M K L) (j : vec 1)
    (w : lifts 1 0 b j) (t : tm K J) : tm L J :=
  match t with
  | tmvar v => tmvar v
  | lam A u => lam (kl_ty f e j w A) (kl_tmty f e j w u)
  | app t u => app (kl_tmty f e j w t) (kl_tmty f e j w u)
  | tlam u => tlam (kl_tmty f (ext_under e) j w u)
  | tapp t A => tapp (kl_tmty f e j w t) (kl_ty f e j w A)
  end.

Definition tmty_k : fam_kl 1 0 Ty 2 Tm :=
  mk_fkl _ _ _ _ _ (fun N M b f K L e jT w t => kl_tmty f e _ w t).

(** Terms, the term sort: under a type binder only the witness moves. *)
Fixpoint kl_tm {N M b} (f : morph 2 1 Tm N M b) {K L} (e : ext N M K L) (J : nat) (r : vec 1)
    (w : lifts 2 1 b (pair J r)) (t : tm J K) : tm J L :=
  match t with
  | tmvar v => f K L e (pair J r) w v
  | lam A u => lam A (kl_tm f (ext_under e) J r w u)
  | app t u => app (kl_tm f e J r w t) (kl_tm f e J r w u)
  | tlam u => tlam (kl_tm f e (S J) r (pair (ext_under (first w)) (second w)) u)
  | tapp t A => tapp (kl_tm f e J r w t) A
  end.

Definition tm_k : sort_kl 2 1 Tm := mk_skl _ _ _ (fun N M b f K L e j w t => kl_tm f e (first j) (second j) w t).

(** *** Their laws: routine inductions *)

(** A term's type as the user wrote it, from the one computed. *)
Ltac sc t := cbv beta iota delta [Ty Tm upd prefix] in t |- *; cbn in t |- *.

(** The induction hypotheses, which [auto] does not see through the
    computed witness types. *)
Ltac ih := try solve [match goal with IH : _ |- _ => apply IH end].

Theorem ty_laws : sort_laws 1 0 Ty (fun K j v => tyvar v) ty_k.
Proof.
  split; cbn.
  - reflexivity.
  - intros N M b f g H K L e j w t; sc t; revert L e; induction t; intros L e; cbn; f_equal; auto; ih.
  - intros N M b f K L K' L' e1 e2 j w t; sc t; revert L' e2; induction t; intros L' e2; cbn; f_equal; auto; ih;
      rewrite <- IHt; reflexivity.
  - intros N M b f K L e j1 j2 w1 w2 t; sc t; revert L e; induction t; intros L e; cbn; f_equal; auto; ih.
  - intros N K e b j w t; sc t; induction t; cbn; f_equal; auto; ih; unfold unit_m; rewrite ext_var_same; reflexivity.
  - intros N M P' b g f K L e j w t; sc t; revert L e; induction t; intros L e; cbn; f_equal; auto; ih;
      rewrite <- IHt; reflexivity.
Qed.

Theorem tmty_laws : fam_laws 1 0 Ty (fun K j v => tyvar v) ty_k 2 Tm tmty_k.
Proof.
  pose proof ty_laws as [_ Hext Hreb Horeb Hunit Hassoc]; cbn in *.
  split; cbn.
  - intros N M b f g H K L e [D [J u]] w t; sc t; revert L e; induction t; intros L e; cbn; f_equal; auto; ih; apply Hext; exact H.
  - intros N M b f K L K' L' e1 e2 [D [J u]] w t; sc t; revert L' e2; induction t; intros L' e2; cbn; f_equal; auto; ih;
      try apply Hreb; rewrite <- IHt; reflexivity.
  - intros N M b f K L e j1 jT w1 w2 t; sc t; revert L e; induction t; intros L e; cbn; f_equal; auto; ih; apply Horeb.
  - intros N K e b [D [J u]] w t; sc t; induction t; cbn; f_equal; auto; ih; apply Hunit.
  - intros N M P' b g f K L e [D [J u]] w t; sc t; revert L e; induction t; intros L e; cbn; f_equal; auto; ih;
      try apply Hassoc; rewrite <- IHt; reflexivity.
Qed.

Theorem tm_laws : sort_laws 2 1 Tm (fun K j v => tmvar v) tm_k.
Proof.
  split; cbn.
  - reflexivity.
  - intros N M b f g H K L e [J r] w t; sc t; revert L e r w; induction t; intros L e r w; cbn;
      f_equal; auto; ih.
  - intros N M b f K L K' L' e1 e2 [J r] w t; sc t; revert L' e2 r w; induction t; intros L' e2 r w;
      cbn; f_equal; auto; ih; rewrite <- IHt; reflexivity.
  - intros N M b f K L e j1 [J r] w1 w2 t; sc t; revert L e r w2; induction t; intros L e r w2; cbn;
      f_equal; auto; ih.
    apply (IHt L e r (pair (ext_under (first w2)) (second w2))).
  - intros N K e b [J r] w t; sc t; revert r w; induction t; intros r w; cbn; f_equal; auto; ih;
      unfold unit_m; rewrite ext_var_same; reflexivity.
  - intros N M P' b g f K L e [J r] w t; sc t; revert L e r w; induction t; intros L e r w; cbn;
      f_equal; auto; ih; rewrite <- IHt; reflexivity.
Qed.

(** ** Three sorts: types 0, regions 1, terms 2

    Types may mention regions and bind types, over the first two sorts;
    terms bind all three.  Only the definitions, to check that the
    witnesses come out right for more sorts and for a family over a
    middle-sized prefix. *)

(** [ty3 N R]: [N] type variables, [R] region variables. *)
Inductive ty3 (N R : nat) : Type :=
| ty3var (v : var N)
| ty3arr (A B : ty3 N R)
| ty3ref (r : var R) (A : ty3 N R)
| ty3all (B : ty3 (S N) R)
| ty3rall (B : ty3 N (S R)).

Arguments ty3var {N R} v.
Arguments ty3arr {N R} A B.
Arguments ty3ref {N R} r A.
Arguments ty3all {N R} B.
Arguments ty3rall {N R} B.

(** [tm3 N R K]: and [K] term variables. *)
Inductive tm3 (N R K : nat) : Type :=
| tm3var (v : var K)
| lam3 (A : ty3 N R) (b : tm3 N R (S K))
| app3 (t u : tm3 N R K)
| tlam3 (b : tm3 (S N) R K)
| rlam3 (b : tm3 N (S R) K)
| new3 (r : var R) (t : tm3 N R K).

Arguments tm3var {N R K} v.
Arguments lam3 {N R K} A b.
Arguments app3 {N R K} t u.
Arguments tlam3 {N R K} b.
Arguments rlam3 {N R K} b.
Arguments new3 {N R K} r t.

Definition Ty3 (x : vec 2) : Type := ty3 (first x) (first (second x)).
Definition Tm3 (x : vec 3) : Type := tm3 (first x) (first (second x)) (first (second (second x))).

(** The type sort of types: going under a region binder moves the
    region component of the witness. *)
Fixpoint kl_ty3 {N M b} (f : morph 2 0 Ty3 N M b) {K L} (e : ext N M K L) (D R : nat)
    (w : lifts 2 0 b (pair D (pair R tt))) (A : ty3 K R) : ty3 L R :=
  match A with
  | ty3var v => f K L e (pair D (pair R tt)) w v
  | ty3arr A B => ty3arr (kl_ty3 f e D R w A) (kl_ty3 f e D R w B)
  | ty3ref x A => ty3ref x (kl_ty3 f e D R w A)
  | ty3all B => ty3all (kl_ty3 f (ext_under e) D R w B)
  | ty3rall B => ty3rall (kl_ty3 f e D (S R) (pair (first w) (pair (ext_under (first (second w))) (second (second w)))) B)
  end.

(** The term sort of terms: a witness for types and one for regions. *)
Fixpoint kl_tm3 {N M b} (f : morph 3 2 Tm3 N M b) {K L} (e : ext N M K L) (J R : nat) (r : vec 1)
    (w : lifts 3 2 b (pair J (pair R r))) (t : tm3 J R K) : tm3 J R L :=
  match t with
  | tm3var v => f K L e (pair J (pair R r)) w v
  | lam3 A u => lam3 A (kl_tm3 f (ext_under e) J R r w u)
  | app3 t u => app3 (kl_tm3 f e J R r w t) (kl_tm3 f e J R r w u)
  | tlam3 u => tlam3 (kl_tm3 f e (S J) R r (pair (ext_under (first w)) (second w)) u)
  | rlam3 u => rlam3 (kl_tm3 f e J (S R) r (pair (first w) (pair (ext_under (first (second w))) (second (second w)))) u)
  | new3 x t => new3 x (kl_tm3 f e J R r w t)
  end.

(** What the witnesses are, computed from the vectors: *)
Example lifts_tm3 b J R r :
  lifts 3 2 b (pair J (pair R r))
  = both (ext (first b) (first b) J J) (both (ext (first (second b)) (first (second b)) R R) (both unit unit)).
Proof. reflexivity. Qed.

Example lifts_ty3 b D R :
  lifts 2 0 b (pair D (pair R tt)) = both unit (both (ext (first (second b)) (first (second b)) R R) unit).
Proof. reflexivity. Qed.
