(** * Prototype: syntaxes with any number of sorts

    A family is the user's own curried inductive ([tm : nat -> nat ->
    Type]); the library sees it through a vector of scopes ([uncurry]), a
    sort being a position.  Substituting sort [i], the binders gone under
    are one value [vext n i Bo Bi Mi O Ki Li]: the other sorts' scopes [O]
    and [i]'s input and output scopes [Ki], [Li]; the family goes from
    [upd n i Ki O] to [upd n i Li O], so the other sorts are visibly the
    same on both sides and nothing containing only them is visited.  A
    family inside another is over a thinning of its sorts.

    Checked here: the generic interface (witnesses, morphisms, Kleisli
    functions and their laws) and System F (types over one sort, terms
    over two) with all its laws.  Build with
      rocq compile -R theories ShiftedNames proto/sorts/Desc.v *)

From Stdlib Require Import Arith Lia StrictProp.
From ShiftedNames.Core Require Import Strict Label Var Scoped Indexed.

Set Primitive Projections.
Record both (A B : Type) : Type := pair { first : A; second : B }.
Unset Primitive Projections.
Arguments pair {A B} first second.
Arguments first {A B} _.
Arguments second {A B} _.

(** ** Vectors of scopes, and families seen through them *)

Fixpoint vec (n : nat) : Type := match n with 0 => unit | S n => both nat (vec n) end.

Fixpoint get (n i : nat) : vec n -> nat :=
  match n as n0 return vec n0 -> nat with
  | 0 => fun _ => 0
  | S n => fun x => match i with 0 => first x | S i => get n i (second x) end
  end.

Fixpoint upd (n i k : nat) : vec n -> vec n :=
  match n as n0 return vec n0 -> vec n0 with
  | 0 => fun x => x
  | S n => fun x => match i with 0 => pair k (second x) | S i => pair (first x) (upd n i k (second x)) end
  end.

(** A curried family over [n] scopes, seen through a vector. *)
Fixpoint arity (n : nat) : Type := match n with 0 => Type | S n => nat -> arity n end.

Fixpoint uncurry (n : nat) : arity n -> vec n -> Type :=
  match n as n0 return arity n0 -> vec n0 -> Type with
  | 0 => fun F _ => F
  | S n => fun F x => uncurry n (F (first x)) (second x)
  end.

(** A family inside another: which of the [n] sorts it has, in order;
    [merge] puts the larger vector together from the smaller one and the
    scopes of the sorts it skips. *)
Inductive thin : nat -> nat -> Type :=
| tdone : thin 0 0
| tkeep {m n} : thin m n -> thin (S m) (S n)
| tskip {m n} : thin m n -> thin m (S n).

Fixpoint skips {m n} (th : thin m n) : nat :=
  match th with tdone => 0 | tkeep th => skips th | tskip th => S (skips th) end.

Fixpoint merge {m n} (th : thin m n) : vec m -> vec (skips th) -> vec n :=
  match th in thin m0 n0 return vec m0 -> vec (skips th) -> vec n0 with
  | tdone => fun _ _ => tt
  | tkeep th => fun x r => pair (first x) (merge th (second x) r)
  | tskip th => fun x r => pair (first r) (merge th x (second r))
  end.

(** ** The descent witness

    Substituting sort [i] of [n], from the base scopes [Bo] (the other
    sorts) and [Bi] (sort [i]) to [i]'s base output scope [Mi]: under a
    binder of sort [i] its input and output scopes go up ([vunder]); under
    one of another sort [t], [t]'s scope ([vother t]).  [vother i] only
    changes [O]'s component [i], which is not used.  With one sort this is
    [ext]. *)
Inductive vext (n i : nat) (Bo : vec n) (Bi Mi : nat) : vec n -> nat -> nat -> Type :=
| vhere : vext n i Bo Bi Mi Bo Bi Mi
| vunder {O Ki Li} : vext n i Bo Bi Mi O Ki Li -> vext n i Bo Bi Mi O (S Ki) (S Li)
| vother (t : nat) {O Ki Li} : vext n i Bo Bi Mi O Ki Li -> vext n i Bo Bi Mi (upd n t (S (get n t O)) O) Ki Li.

Arguments vhere {n i Bo Bi Mi}.
Arguments vunder {n i Bo Bi Mi O Ki Li} e.
Arguments vother {n i Bo Bi Mi} t {O Ki Li} e.

Section Witness.

Context {n i : nat}.

(** Composing witnesses ([rebase]). *)
Fixpoint vapp {Bo Bi Mi O1 K1 L1 O2 K2 L2} (e1 : vext n i Bo Bi Mi O1 K1 L1) (e2 : vext n i O1 K1 L1 O2 K2 L2)
    : vext n i Bo Bi Mi O2 K2 L2 :=
  match e2 in vext _ _ _ _ _ O0 K0 L0 return vext n i Bo Bi Mi O0 K0 L0 with
  | vhere => e1
  | vunder e2 => vunder (vapp e1 e2)
  | vother t e2 => vother t (vapp e1 e2)
  end.

(** Splitting a witness [Bi ⇝ Pi] through a middle base [Mi] ([assoc]). *)
Fixpoint vmid {Bo Bi Pi O Ki Li} (Mi : nat) (e : vext n i Bo Bi Pi O Ki Li) : nat :=
  match e with
  | vhere => Mi
  | vunder e => S (vmid Mi e)
  | vother _ e => vmid Mi e
  end.

Fixpoint vleft {Bo Bi Pi O Ki Li} (Mi : nat) (e : vext n i Bo Bi Pi O Ki Li) : vext n i Bo Bi Mi O Ki (vmid Mi e) :=
  match e as e0 in vext _ _ _ _ _ O0 K0 L0 return vext n i Bo Bi Mi O0 K0 (vmid Mi e0) with
  | vhere => vhere
  | vunder e => vunder (vleft Mi e)
  | vother t e => vother t (vleft Mi e)
  end.

Fixpoint vright {Bo Bi Pi O Ki Li} (Mi : nat) (e : vext n i Bo Bi Pi O Ki Li) : vext n i Bo Mi Pi O (vmid Mi e) Li :=
  match e as e0 in vext _ _ _ _ _ O0 K0 L0 return vext n i Bo Mi Pi O0 (vmid Mi e0) L0 with
  | vhere => vhere
  | vunder e => vunder (vright Mi e)
  | vother t e => vother t (vright Mi e)
  end.

(** How many binders of sort [i]: its scopes are that many above the
    bases. *)
Fixpoint vdepth {Bo Bi Mi O Ki Li} (e : vext n i Bo Bi Mi O Ki Li) : nat :=
  match e with
  | vhere => 0
  | vunder e => S (vdepth e)
  | vother _ e => vdepth e
  end.

Lemma vdepth_K {Bo Bi Mi O Ki Li} (e : vext n i Bo Bi Mi O Ki Li) : Ki = vdepth e + Bi.
Proof. induction e; cbn; lia. Qed.

Lemma vdepth_L {Bo Bi Mi O Ki Li} (e : vext n i Bo Bi Mi O Ki Li) : Li = vdepth e + Mi.
Proof. induction e; cbn; lia. Qed.

(** A variable along a witness that keeps the base ([unit]). *)
Lemma vvar_wf {Bo Bi O Ki Li} (e : vext n i Bo Bi Bi O Ki Li) v : wf_var Ki v = true -> wf_var Li v = true.
Proof. pose proof (vdepth_K e) as HK; pose proof (vdepth_L e) as HL; rewrite <- HL in HK; subst; exact (fun H => H). Qed.

Definition vvar {Bo Bi O Ki Li} (e : vext n i Bo Bi Bi O Ki Li) (v : var Ki) : var Li :=
  mk_var (var_raw v) (Is_true_s_intro (vvar_wf e _ (Is_true_s_elim (var_ok v)))).

Lemma vvar_same {Bo Bi O Ki} (e : vext n i Bo Bi Bi O Ki Ki) v : vvar e v = v.
Proof. apply var_eq; reflexivity. Qed.

End Witness.

(** ** Morphisms, Kleisli functions and their laws *)

Section Generic.

Context (n i : nat).

(** A morphism of sort [i] into its carrier [P] (a family over the [n]
    sorts), from base scopes [Bo], [Bi] to [Mi]. *)
Definition morph (P : vec n -> Type) (Bo : vec n) (Bi Mi : nat) : Type :=
  forall O Ki Li, vext n i Bo Bi Mi O Ki Li -> var Ki -> P (upd n i Li O).

Definition rebase_m {P Bo Bi Mi O1 K1 L1} (e1 : vext n i Bo Bi Mi O1 K1 L1) (f : morph P Bo Bi Mi) : morph P O1 K1 L1 :=
  fun O Ki Li e v => f O Ki Li (vapp e1 e) v.

(** The carrier's own Kleisli function. *)
Definition sort_kl (P : vec n -> Type) : Type :=
  forall Bo Bi Mi (f : morph P Bo Bi Mi) O Ki Li (e : vext n i Bo Bi Mi O Ki Li), P (upd n i Ki O) -> P (upd n i Li O).

(** A family over more sorts ([th] places the carrier's among them; [r]
    the scopes of the others, which this sort's binders do not change). *)
Definition fam_kl (P : vec n -> Type) {nT} (th : thin n nT) (T : vec nT -> Type) : Type :=
  forall Bo Bi Mi (f : morph P Bo Bi Mi) O Ki Li (e : vext n i Bo Bi Mi O Ki Li) (r : vec (skips th)),
    T (merge th (upd n i Ki O) r) -> T (merge th (upd n i Li O) r).

Section Laws.

Context (P : vec n -> Type) (tv : forall O K, var K -> P (upd n i K O)) (kp : sort_kl P).

Definition unit_m {Bo Bi} : morph P Bo Bi Bi := fun O Ki Li e v => tv O Li (vvar e v).

Definition comp_m {Bo Bi Mi Pi} (g : morph P Bo Mi Pi) (f : morph P Bo Bi Mi) : morph P Bo Bi Pi :=
  fun O Ki Li e v => kp _ _ _ g _ _ _ (vright Mi e) (f O Ki (vmid Mi e) (vleft Mi e) v).

Record sort_laws : Prop := {
  s_var : forall Bo Bi Mi (f : morph P Bo Bi Mi) O Ki Li (e : vext n i Bo Bi Mi O Ki Li) v,
    kp _ _ _ f _ _ _ e (tv O Ki v) = f O Ki Li e v;
  s_ext : forall Bo Bi Mi (f g : morph P Bo Bi Mi), (forall O Ki Li e v, f O Ki Li e v = g O Ki Li e v) ->
    forall O Ki Li (e : vext n i Bo Bi Mi O Ki Li) t, kp _ _ _ f _ _ _ e t = kp _ _ _ g _ _ _ e t;
  s_rebase : forall Bo Bi Mi (f : morph P Bo Bi Mi) O1 K1 L1 O2 K2 L2
      (e1 : vext n i Bo Bi Mi O1 K1 L1) (e2 : vext n i O1 K1 L1 O2 K2 L2) t,
    kp _ _ _ f _ _ _ (vapp e1 e2) t = kp _ _ _ (rebase_m e1 f) _ _ _ e2 t;
  s_unit : forall Bo Bi O Ki (e : vext n i Bo Bi Bi O Ki Ki) t, kp _ _ _ unit_m _ _ _ e t = t;
  s_assoc : forall Bo Bi Mi Pi (g : morph P Bo Mi Pi) (f : morph P Bo Bi Mi) O Ki Li (e : vext n i Bo Bi Pi O Ki Li) t,
    kp _ _ _ (comp_m g f) _ _ _ e t = kp _ _ _ g _ _ _ (vright Mi e) (kp _ _ _ f _ _ _ (vleft Mi e) t) }.

Record fam_laws {nT} (th : thin n nT) (T : vec nT -> Type) (k : fam_kl P th T) : Prop := {
  f_ext : forall Bo Bi Mi (f g : morph P Bo Bi Mi), (forall O Ki Li e v, f O Ki Li e v = g O Ki Li e v) ->
    forall O Ki Li (e : vext n i Bo Bi Mi O Ki Li) r t, k _ _ _ f _ _ _ e r t = k _ _ _ g _ _ _ e r t;
  f_rebase : forall Bo Bi Mi (f : morph P Bo Bi Mi) O1 K1 L1 O2 K2 L2
      (e1 : vext n i Bo Bi Mi O1 K1 L1) (e2 : vext n i O1 K1 L1 O2 K2 L2) r t,
    k _ _ _ f _ _ _ (vapp e1 e2) r t = k _ _ _ (rebase_m e1 f) _ _ _ e2 r t;
  f_unit : forall Bo Bi O Ki (e : vext n i Bo Bi Bi O Ki Ki) r t, k _ _ _ unit_m _ _ _ e r t = t;
  f_assoc : forall Bo Bi Mi Pi (g : morph P Bo Mi Pi) (f : morph P Bo Bi Mi) O Ki Li (e : vext n i Bo Bi Pi O Ki Li) r t,
    k _ _ _ (comp_m g f) _ _ _ e r t = k _ _ _ g _ _ _ (vright Mi e) r (k _ _ _ f _ _ _ (vleft Mi e) r t) }.

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

(** Types are sort 0 of terms. *)
Definition ty_in_tm : thin 1 2 := tkeep (tskip tdone).

(** The user's three Kleisli functions. *)

(** Types, the type sort ([O] has no other sort). *)
Fixpoint kl_ty {Bo Bi Mi} (f : morph 1 0 (uncurry 1 ty) Bo Bi Mi) {O Ki Li} (e : vext 1 0 Bo Bi Mi O Ki Li)
    (A : ty Ki) : ty Li :=
  match A with
  | tyvar v => f O Ki Li e v
  | tyarr A A' => tyarr (kl_ty f e A) (kl_ty f e A')
  | tyall A => tyall (kl_ty f (vunder e) A)
  end.

(** Terms, the term sort: the type scope is [O]'s; annotations untouched. *)
Fixpoint kl_tm {Bo Bi Mi} (f : morph 2 1 (uncurry 2 tm) Bo Bi Mi) {O Ki Li} (e : vext 2 1 Bo Bi Mi O Ki Li)
    (t : tm (first O) Ki) : tm (first O) Li :=
  match t with
  | tmvar v => f O Ki Li e v
  | lam A u => lam A (kl_tm f (vunder e) u)
  | app t u => app (kl_tm f e t) (kl_tm f e u)
  | tlam u => tlam (kl_tm f (vother 0 e) u)
  | tapp t A => tapp (kl_tm f e t) A
  end.

(** Terms, the type sort: the witness is over the types' sort; the term
    scope [J] is an ordinary argument. *)
Fixpoint kl_tmty {Bo Bi Mi} (f : morph 1 0 (uncurry 1 ty) Bo Bi Mi) {O Ki Li} (e : vext 1 0 Bo Bi Mi O Ki Li)
    {J} (t : tm Ki J) : tm Li J :=
  match t with
  | tmvar v => tmvar v
  | lam A u => lam (kl_ty f e A) (kl_tmty f e u)
  | app t u => app (kl_tmty f e t) (kl_tmty f e u)
  | tlam u => tlam (kl_tmty f (vunder e) u)
  | tapp t A => tapp (kl_tmty f e t) (kl_ty f e A)
  end.

(** What the library takes: the same functions at the interface's types
    (they are the same types, computed). *)
Definition ty_k : sort_kl 1 0 (uncurry 1 ty) := fun Bo Bi Mi f O Ki Li e A => kl_ty f e A.
Definition tm_k : sort_kl 2 1 (uncurry 2 tm) := fun Bo Bi Mi f O Ki Li e t => kl_tm f e t.
Definition tmty_k : fam_kl 1 0 (uncurry 1 ty) ty_in_tm (uncurry 2 tm) := fun Bo Bi Mi f O Ki Li e r t => kl_tmty f e t.

(** ** Their laws: routine inductions *)

Section Proofs.

Lemma kl_ty_ext {Bo Bi Mi} (f g : morph 1 0 (uncurry 1 ty) Bo Bi Mi) :
  (forall O Ki Li e v, f O Ki Li e v = g O Ki Li e v) ->
  forall O Ki Li (e : vext 1 0 Bo Bi Mi O Ki Li) A, kl_ty f e A = kl_ty g e A.
Proof. intros H O Ki Li e A; revert Li e; induction A; intros Li e; cbn; f_equal; auto. Qed.

Lemma kl_ty_rebase {Bo Bi Mi} (f : morph 1 0 (uncurry 1 ty) Bo Bi Mi) O1 K1 L1 O2 K2 L2
    (e1 : vext 1 0 Bo Bi Mi O1 K1 L1) (e2 : vext 1 0 O1 K1 L1 O2 K2 L2) A :
  kl_ty f (vapp e1 e2) A = kl_ty (rebase_m 1 0 e1 f) e2 A.
Proof. revert L2 e2; induction A; intros L2 e2; cbn; f_equal; auto; apply (IHA _ (vunder e2)). Qed.

Lemma kl_ty_unit {Bo Bi} O Ki (e : vext 1 0 Bo Bi Bi O Ki Ki) A :
  kl_ty (unit_m 1 0 (uncurry 1 ty) (fun O K v => tyvar v)) e A = A.
Proof.
  induction A; cbn; f_equal; auto; unfold unit_m; rewrite vvar_same; reflexivity.
Qed.

Lemma kl_ty_assoc {Bo Bi Mi Pi} (g : morph 1 0 (uncurry 1 ty) Bo Mi Pi) (f : morph 1 0 (uncurry 1 ty) Bo Bi Mi)
    O Ki Li (e : vext 1 0 Bo Bi Pi O Ki Li) A :
  kl_ty (comp_m 1 0 (uncurry 1 ty) ty_k g f) e A = kl_ty g (vright Mi e) (kl_ty f (vleft Mi e) A).
Proof. revert Li e; induction A; intros Li e; cbn; f_equal; auto; apply (IHA _ (vunder e)). Qed.

Theorem ty_laws : sort_laws 1 0 (uncurry 1 ty) (fun O K v => tyvar v) ty_k.
Proof.
  split; cbn [ty_k].
  - reflexivity.
  - intros; apply kl_ty_ext; assumption.
  - intros; apply kl_ty_rebase.
  - intros; apply kl_ty_unit.
  - intros; apply kl_ty_assoc.
Qed.

Lemma kl_tm_ext {Bo Bi Mi} (f g : morph 2 1 (uncurry 2 tm) Bo Bi Mi) :
  (forall O Ki Li e v, f O Ki Li e v = g O Ki Li e v) ->
  forall O Ki Li (e : vext 2 1 Bo Bi Mi O Ki Li) t, kl_tm f e t = kl_tm g e t.
Proof.
  intros H [N r] Ki Li e t; cbn in t; revert r Li e; induction t; intros r Li e; cbn; f_equal; auto;
    try (unfold unit_m; rewrite vvar_same; reflexivity); try apply IHt.
Qed.

Lemma kl_tm_rebase {Bo Bi Mi} (f : morph 2 1 (uncurry 2 tm) Bo Bi Mi) O1 K1 L1 O2 K2 L2
    (e1 : vext 2 1 Bo Bi Mi O1 K1 L1) (e2 : vext 2 1 O1 K1 L1 O2 K2 L2) t :
  kl_tm f (vapp e1 e2) t = kl_tm (rebase_m 2 1 e1 f) e2 t.
Proof.
  destruct O2 as [N r]; cbn in t; revert r L2 e2; induction t; intros r L2 e2; cbn; f_equal; auto;
    try (unfold unit_m; rewrite vvar_same; reflexivity); first [apply (IHt _ _ (vunder e2)) | apply (IHt _ _ (vother 0 e2))].
Qed.

Lemma kl_tm_unit {Bo Bi} O Ki (e : vext 2 1 Bo Bi Bi O Ki Ki) t :
  kl_tm (unit_m 2 1 (uncurry 2 tm) (fun O K v => tmvar v)) e t = t.
Proof.
  destruct O as [N r]; cbn in t; revert r e; induction t; intros r e; cbn; f_equal; auto;
    try (unfold unit_m; rewrite vvar_same; reflexivity); try apply IHt.
Qed.

Lemma kl_tm_assoc {Bo Bi Mi Pi} (g : morph 2 1 (uncurry 2 tm) Bo Mi Pi) (f : morph 2 1 (uncurry 2 tm) Bo Bi Mi)
    O Ki Li (e : vext 2 1 Bo Bi Pi O Ki Li) t :
  kl_tm (comp_m 2 1 (uncurry 2 tm) tm_k g f) e t = kl_tm g (vright Mi e) (kl_tm f (vleft Mi e) t).
Proof.
  destruct O as [N r]; cbn in t; revert r Li e; induction t; intros r Li e; cbn; f_equal; auto;
    try (unfold unit_m; rewrite vvar_same; reflexivity); try apply IHt.
Qed.

Theorem tm_laws : sort_laws 2 1 (uncurry 2 tm) (fun O K v => tmvar v) tm_k.
Proof.
  split; cbn [tm_k].
  - reflexivity.
  - intros Bo Bi Mi f g H O Ki Li e t; exact (kl_tm_ext f g H O Ki Li e t).
  - intros Bo Bi Mi f O1 K1 L1 O2 K2 L2 e1 e2 t; exact (kl_tm_rebase f O1 K1 L1 O2 K2 L2 e1 e2 t).
  - intros Bo Bi O Ki e t; exact (kl_tm_unit O Ki e t).
  - intros Bo Bi Mi Pi g f O Ki Li e t; exact (kl_tm_assoc g f O Ki Li e t).
Qed.

Lemma kl_tmty_ext {Bo Bi Mi} (f g : morph 1 0 (uncurry 1 ty) Bo Bi Mi) :
  (forall O Ki Li e v, f O Ki Li e v = g O Ki Li e v) ->
  forall O Ki Li (e : vext 1 0 Bo Bi Mi O Ki Li) J (t : tm Ki J), kl_tmty f e t = kl_tmty g e t.
Proof.
  intros H O Ki Li e J t; revert Li e; induction t; intros Li e; cbn; f_equal; auto;
    try (apply kl_ty_ext; assumption).
Qed.

Lemma kl_tmty_rebase {Bo Bi Mi} (f : morph 1 0 (uncurry 1 ty) Bo Bi Mi) O1 K1 L1 O2 K2 L2
    (e1 : vext 1 0 Bo Bi Mi O1 K1 L1) (e2 : vext 1 0 O1 K1 L1 O2 K2 L2) J (t : tm K2 J) :
  kl_tmty f (vapp e1 e2) t = kl_tmty (rebase_m 1 0 e1 f) e2 t.
Proof.
  revert L2 e2; induction t; intros L2 e2; cbn; f_equal; auto; try apply kl_ty_rebase.
  apply (IHt _ (vunder e2)).
Qed.

Lemma kl_tmty_unit {Bo Bi} O Ki (e : vext 1 0 Bo Bi Bi O Ki Ki) J (t : tm Ki J) :
  kl_tmty (unit_m 1 0 (uncurry 1 ty) (fun O K v => tyvar v)) e t = t.
Proof. induction t; cbn; f_equal; auto; apply kl_ty_unit. Qed.

Lemma kl_tmty_assoc {Bo Bi Mi Pi} (g : morph 1 0 (uncurry 1 ty) Bo Mi Pi) (f : morph 1 0 (uncurry 1 ty) Bo Bi Mi)
    O Ki Li (e : vext 1 0 Bo Bi Pi O Ki Li) J (t : tm Ki J) :
  kl_tmty (comp_m 1 0 (uncurry 1 ty) ty_k g f) e t = kl_tmty g (vright Mi e) (kl_tmty f (vleft Mi e) t).
Proof. revert Li e; induction t; intros Li e; cbn; f_equal; auto; apply kl_ty_assoc. Qed.

Theorem tmty_laws : fam_laws 1 0 (uncurry 1 ty) (fun O K v => tyvar v) ty_k ty_in_tm (uncurry 2 tm) tmty_k.
Proof.
  split; cbn [tmty_k].
  - intros Bo Bi Mi f g H O Ki Li e r t; exact (kl_tmty_ext f g H O Ki Li e _ t).
  - intros Bo Bi Mi f O1 K1 L1 O2 K2 L2 e1 e2 r t; exact (kl_tmty_rebase f O1 K1 L1 O2 K2 L2 e1 e2 _ t).
  - intros Bo Bi O Ki e r t; exact (kl_tmty_unit O Ki e _ t).
  - intros Bo Bi Mi Pi g f O Ki Li e r t; exact (kl_tmty_assoc g f O Ki Li e _ t).
Qed.

End Proofs.
