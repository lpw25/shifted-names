(** * Prototype: syntaxes with any number of sorts of variable

    Checks the scheme of [docs/sorts.md].  Sorts are any type with a
    boolean equality; a family is indexed by the scopes of a list of
    sorts; a sort's morphisms, Kleisli functions and laws are computed
    from those lists.  Instances: System F (two sorts, types over one of
    them) and a calculus with three (types, regions, terms).  Standalone:
    only [Var] and the witnesses of [Syntax] are used.  Build with
      rocq compile -R theories ShiftedNames proto/sorts/Sorts.v *)

From Stdlib Require Import Arith Lia List Bool.
From ShiftedNames.Core Require Import Strict Label Var Scoped Indexed.
From ShiftedNames.Core Require Syntax.
Import Syntax (ext, ext_here, ext_under, ext_app, ext_mid, ext_left, ext_right, ext_var, ext_var_same).
Import ListNotations.

(** Pairs with eta, so that a tuple of scopes taken apart and put back is
    the same tuple. *)
Set Primitive Projections.
Record both (A B : Type) : Type := pair { first : A; second : B }.
Unset Primitive Projections.
Arguments pair {A B} first second.
Arguments first {A B} _.
Arguments second {A B} _.

(** ** The generic part *)

Class Sorts (S : Type) := { seqb : S -> S -> bool }.

Section Generic.

Context {S : Type} {SS : Sorts S}.

(** The scopes of a list of sorts. *)
Fixpoint scopes (ss : list S) : Type :=
  match ss with [] => unit | _ :: ss => both nat (scopes ss) end.

(** The scope of sort [s], and the scopes with it replaced. *)
Fixpoint get (ss : list S) (s : S) : scopes ss -> nat :=
  match ss as ss0 return scopes ss0 -> nat with
  | [] => fun _ => 0
  | t :: ss => fun x => if seqb t s then first x else get ss s (second x)
  end.

Fixpoint upd (ss : list S) (s : S) (n : nat) : scopes ss -> scopes ss :=
  match ss as ss0 return scopes ss0 -> scopes ss0 with
  | [] => fun x => x
  | t :: ss => fun x => if seqb t s then pair n (second x) else pair (first x) (upd ss s n (second x))
  end.

(** The scopes of a sub-list (the sorts of a family inside another). *)
Fixpoint restrict (ss : list S) (ss' : list S) : scopes ss -> scopes ss' :=
  match ss' as ss0 return scopes ss -> scopes ss0 with
  | [] => fun _ => tt
  | t :: ss' => fun x => pair (get ss t x) (restrict ss ss' x)
  end.

(** Substituting sort [s]: the other sorts' binders crossed, each over
    its base with the base unchanged ([b] the bases, [j] the scopes
    reached; [s]'s own component is unused). *)
Fixpoint lifts (ss : list S) (s : S) : scopes ss -> scopes ss -> Type :=
  match ss as ss0 return scopes ss0 -> scopes ss0 -> Type with
  | [] => fun _ _ => unit
  | t :: ss => fun b j =>
      both (if seqb t s then unit else ext (first b) (first b) (first j) (first j)) (lifts ss s (second b) (second j))
  end.

Fixpoint lhere (ss : list S) (s : S) : forall b, lifts ss s b b :=
  match ss as ss0 return forall b : scopes ss0, lifts ss0 s b b with
  | [] => fun _ => tt
  | t :: ss => fun b =>
      pair (match seqb t s as c return (if c then unit else ext (first b) (first b) (first b) (first b)) with
            | true => tt
            | false => ext_here
            end) (lhere ss s (second b))
  end.

Fixpoint lcomp (ss : list S) (s : S) : forall b j1 j2, lifts ss s b j1 -> lifts ss s j1 j2 -> lifts ss s b j2 :=
  match ss as ss0 return forall b j1 j2 : scopes ss0, lifts ss0 s b j1 -> lifts ss0 s j1 j2 -> lifts ss0 s b j2 with
  | [] => fun _ _ _ _ _ => tt
  | t :: ss => fun b j1 j2 w1 w2 =>
      pair (match seqb t s as c
                  return (if c then unit else ext (first b) (first b) (first j1) (first j1)) ->
                         (if c then unit else ext (first j1) (first j1) (first j2) (first j2)) ->
                         (if c then unit else ext (first b) (first b) (first j2) (first j2)) with
            | true => fun _ _ => tt
            | false => fun x y => ext_app x y
            end (first w1) (first w2))
           (lcomp ss s (second b) (second j1) (second j2) (second w1) (second w2))
  end.

Arguments lcomp {ss s b j1 j2} w1 w2.

Context (ss : list S) (s : S).

(** A morphism of sort [s] into its carrier [P] (over the sorts [ss]):
    liftable along [s]'s binders ([ext]) and along the others' ([lifts]). *)
Definition morph (P : scopes ss -> Type) (N M : nat) (b : scopes ss) : Type :=
  forall K L, ext N M K L -> forall j, lifts ss s b j -> var K -> P (upd ss s L j).

Definition rebase_m {P N M K L b} (e1 : ext N M K L) (f : morph P N M b) : morph P K L b :=
  fun K' L' e j w v => f K' L' (ext_app e1 e) j w v.

Definition orebase_m {P N M b j1} (w1 : lifts ss s b j1) (f : morph P N M b) : morph P N M j1 :=
  fun K L e j2 w2 v => f K L e j2 (lcomp w1 w2) v.

(** The carrier's own Kleisli function, and another family's (over more
    sorts [ssT], the carrier's sorts among them). *)
Record sort_kl (P : scopes ss -> Type) := mk_skl {
  skl : forall {N M b} (f : morph P N M b) {K L} (e : ext N M K L) {j} (w : lifts ss s b j),
          P (upd ss s K j) -> P (upd ss s L j) }.

Record fam_kl (P : scopes ss -> Type) (ssT : list S) (T : scopes ssT -> Type) := mk_fkl {
  fkl : forall {N M b} (f : morph P N M b) {K L} (e : ext N M K L) {jT} (w : lifts ss s b (restrict ssT ss jT)),
          T (upd ssT s K jT) -> T (upd ssT s L jT) }.

Arguments skl {P} _ {N M b} f {K L} e {j} w _.
Arguments fkl {P ssT T} _ {N M b} f {K L} e {jT} w _.

Section Laws.

Context (P : scopes ss -> Type) (tv : forall K j, var K -> P (upd ss s K j)) (kp : sort_kl P).

Definition unit_m {N b} : morph P N N b := fun K L e j w v => tv L j (ext_var e v).

Definition comp_m {N M P' b} (g : morph P M P' b) (f : morph P N M b) : morph P N P' b :=
  fun K L e j w v => skl kp g (ext_right M e) w (f K (ext_mid M e) (ext_left M e) j w v).

(** The laws of a sort's syntax: the current ones, the other sorts'
    witness threaded through, and [orebase]: those witnesses compose. *)
Record sort_laws : Prop := {
  s_var : forall N M b (f : morph P N M b) K L (e : ext N M K L) j (w : lifts ss s b j) v,
    skl kp f e w (tv K j v) = f K L e j w v;
  s_ext : forall N M b (f g : morph P N M b), (forall K L e j w v, f K L e j w v = g K L e j w v) ->
    forall K L (e : ext N M K L) j (w : lifts ss s b j) t, skl kp f e w t = skl kp g e w t;
  s_rebase : forall N M b (f : morph P N M b) K L K' L' (e1 : ext N M K L) (e2 : ext K L K' L') j
      (w : lifts ss s b j) t,
    skl kp f (ext_app e1 e2) w t = skl kp (rebase_m e1 f) e2 w t;
  s_orebase : forall N M b (f : morph P N M b) K L (e : ext N M K L) j1 j2 (w1 : lifts ss s b j1)
      (w2 : lifts ss s j1 j2) t,
    skl kp f e (lcomp w1 w2) t = skl kp (orebase_m w1 f) e w2 t;
  s_unit : forall N K (e : ext N N K K) b j (w : lifts ss s b j) t, skl kp (unit_m (b := b)) e w t = t;
  s_assoc : forall N M P' b (g : morph P M P' b) (f : morph P N M b) K L (e : ext N P' K L) j
      (w : lifts ss s b j) t,
    skl kp (comp_m g f) e w t = skl kp g (ext_right M e) w (skl kp f (ext_left M e) w t) }.

(** Another family: the same laws, along the carrier's morphisms. *)
Record fam_laws (ssT : list S) (T : scopes ssT -> Type) (k : fam_kl P ssT T) : Prop := {
  f_ext : forall N M b (f g : morph P N M b), (forall K L e j w v, f K L e j w v = g K L e j w v) ->
    forall K L (e : ext N M K L) jT (w : lifts ss s b (restrict ssT ss jT)) t, fkl k f e w t = fkl k g e w t;
  f_rebase : forall N M b (f : morph P N M b) K L K' L' (e1 : ext N M K L) (e2 : ext K L K' L') jT
      (w : lifts ss s b (restrict ssT ss jT)) t,
    fkl k f (ext_app e1 e2) w t = fkl k (rebase_m e1 f) e2 w t;
  f_orebase : forall N M b (f : morph P N M b) K L (e : ext N M K L) j1 jT (w1 : lifts ss s b j1)
      (w2 : lifts ss s j1 (restrict ssT ss jT)) t,
    fkl k f e (lcomp w1 w2) t = fkl k (orebase_m w1 f) e w2 t;
  f_unit : forall N K (e : ext N N K K) b jT (w : lifts ss s b (restrict ssT ss jT)) t,
    fkl k (unit_m (b := b)) e w t = t;
  f_assoc : forall N M P' b (g : morph P M P' b) (f : morph P N M b) K L (e : ext N P' K L) jT
      (w : lifts ss s b (restrict ssT ss jT)) t,
    fkl k (comp_m g f) e w t = fkl k g (ext_right M e) w (fkl k f (ext_left M e) w t) }.

End Laws.

End Generic.

Arguments skl {S SS ss s P} _ {N M b} f {K L} e {j} w _.
Arguments fkl {S SS ss s P ssT T} _ {N M b} f {K L} e {jT} w _.

(** ** System F: two sorts, types over one of them *)

Inductive sortF := TY | TM.

#[export] Instance sortF_sorts : Sorts sortF :=
  {| seqb a b := match a, b with TY, TY | TM, TM => true | _, _ => false end |}.

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

(** The families over their lists of sorts. *)
Definition Ty (x : scopes [TY]) : Type := ty (first x).
Definition Tm (x : scopes [TY; TM]) : Type := tm (first x) (first (second x)).

(** Types, the type sort: the other sorts' witness is threaded through
    (there are none). *)
Fixpoint kl_ty {N M b} (f : morph [TY] TY Ty N M b) {K L} (e : ext N M K L) (j : scopes [TY])
    (w : lifts [TY] TY b j) (A : ty K) : ty L :=
  match A with
  | tyvar v => f K L e j w v
  | tyarr A B => tyarr (kl_ty f e j w A) (kl_ty f e j w B)
  | tyall B => tyall (kl_ty f (ext_under e) j w B)
  end.

Definition ty_k : sort_kl [TY] TY Ty := mk_skl _ _ _ (fun N M b f K L e j w A => kl_ty f e j w A).

(** Terms, the type sort: a family over [TY; TM] with the carrier over
    [TY]; types inside are the carrier itself. *)
Fixpoint kl_tmty {J N M b} (f : morph [TY] TY Ty N M b) {K L} (e : ext N M K L) (j : scopes [TY])
    (w : lifts [TY] TY b j) (t : tm K J) : tm L J :=
  match t with
  | tmvar v => tmvar v
  | lam A u => lam (kl_ty f e j w A) (kl_tmty f e j w u)
  | app t u => app (kl_tmty f e j w t) (kl_tmty f e j w u)
  | tlam u => tlam (kl_tmty f (ext_under e) j w u)
  | tapp t A => tapp (kl_tmty f e j w t) (kl_ty f e j w A)
  end.

Definition tmty_k : fam_kl [TY] TY Ty [TY; TM] Tm :=
  mk_fkl _ _ _ _ _ (fun N M b f K L e jT w t => kl_tmty f e _ w t).

(** Terms, the term sort: under a type binder only the witness moves. *)
Fixpoint kl_tm {N M b} (f : morph [TY; TM] TM Tm N M b) {K L} (e : ext N M K L) (J : nat) (r : scopes [TM])
    (w : lifts [TY; TM] TM b (pair J r)) (t : tm J K) : tm J L :=
  match t with
  | tmvar v => f K L e (pair J r) w v
  | lam A u => lam A (kl_tm f (ext_under e) J r w u)
  | app t u => app (kl_tm f e J r w t) (kl_tm f e J r w u)
  | tlam u => tlam (kl_tm f e (S J) r (pair (ext_under (first w)) (second w)) u)
  | tapp t A => tapp (kl_tm f e J r w t) A
  end.

Definition tm_k : sort_kl [TY; TM] TM Tm := mk_skl _ _ _ (fun N M b f K L e j w t => kl_tm f e (first j) (second j) w t).

(** *** Their laws: routine inductions *)

(** A term's type as the user wrote it, from the one computed. *)
Ltac sc t := cbv beta iota delta [Ty Tm upd get restrict seqb sortF_sorts] in t |- *; cbn in t |- *.

(** The induction hypotheses, which [auto] does not see through the
    computed witness types. *)
Ltac ih := try solve [match goal with IH : _ |- _ => apply IH end].

Theorem ty_laws : sort_laws [TY] TY Ty (fun K j v => tyvar v) ty_k.
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

Theorem tmty_laws : fam_laws [TY] TY Ty (fun K j v => tyvar v) ty_k [TY; TM] Tm tmty_k.
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

Theorem tm_laws : sort_laws [TY; TM] TM Tm (fun K j v => tmvar v) tm_k.
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

(** ** Three sorts: types, regions and terms

    Types may mention regions and bind types; terms bind all three.  Only
    the definitions, to check that the witnesses come out right for more
    sorts and for a family over a middle-sized list. *)

Inductive sort3 := TY3 | RG3 | TM3.

#[export] Instance sort3_sorts : Sorts sort3 :=
  {| seqb a b := match a, b with TY3, TY3 | RG3, RG3 | TM3, TM3 => true | _, _ => false end |}.

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

Definition Ty3 (x : scopes [TY3; RG3]) : Type := ty3 (first x) (first (second x)).
Definition Tm3 (x : scopes [TY3; RG3; TM3]) : Type := tm3 (first x) (first (second x)) (first (second (second x))).

(** The type sort of types: going under a region binder moves the
    region component of the witness. *)
Fixpoint kl_ty3 {N M b} (f : morph [TY3; RG3] TY3 Ty3 N M b) {K L} (e : ext N M K L) (D R : nat) (r : scopes [])
    (w : lifts [TY3; RG3] TY3 b (pair D (pair R r))) (A : ty3 K R) : ty3 L R :=
  match A with
  | ty3var v => f K L e (pair D (pair R r)) w v
  | ty3arr A B => ty3arr (kl_ty3 f e D R r w A) (kl_ty3 f e D R r w B)
  | ty3ref x A => ty3ref x (kl_ty3 f e D R r w A)
  | ty3all B => ty3all (kl_ty3 f (ext_under e) D R r w B)
  | ty3rall B => ty3rall (kl_ty3 f e D (S R) r (pair (first w) (pair (ext_under (first (second w))) (second (second w)))) B)
  end.

(** The term sort of terms: a witness for types and one for regions. *)
Fixpoint kl_tm3 {N M b} (f : morph [TY3; RG3; TM3] TM3 Tm3 N M b) {K L} (e : ext N M K L) (J R : nat) (r : scopes [TM3])
    (w : lifts [TY3; RG3; TM3] TM3 b (pair J (pair R r))) (t : tm3 J R K) : tm3 J R L :=
  match t with
  | tm3var v => f K L e (pair J (pair R r)) w v
  | lam3 A u => lam3 A (kl_tm3 f (ext_under e) J R r w u)
  | app3 t u => app3 (kl_tm3 f e J R r w t) (kl_tm3 f e J R r w u)
  | tlam3 u => tlam3 (kl_tm3 f e (S J) R r (pair (ext_under (first w)) (second w)) u)
  | rlam3 u => rlam3 (kl_tm3 f e J (S R) r (pair (first w) (pair (ext_under (first (second w))) (second (second w)))) u)
  | new3 x t => new3 x (kl_tm3 f e J R r w t)
  end.

(** What the witnesses are, computed from the lists: *)
Example lifts_tm3 b J R r :
  lifts [TY3; RG3; TM3] TM3 b (pair J (pair R r))
  = both (ext (first b) (first b) J J) (both (ext (first (second b)) (first (second b)) R R) (both unit unit)).
Proof. reflexivity. Qed.

Example lifts_ty3 b D R r :
  lifts [TY3; RG3] TY3 b (pair D (pair R r)) = both unit (both (ext (first (second b)) (first (second b)) R R) unit).
Proof. reflexivity. Qed.
