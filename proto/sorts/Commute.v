(** * Prototype: moving a substitution of one sort past one of another

    Two sorts of a family, [i] left of [j]: the scopes are a zipper with
    two holes ([scopes2 a c d]: the [a] sorts left of [i], nearest first;
    [i]'s scope; the [c] sorts between, in order; [j]'s scope; the [d]
    sorts right of [j]).  Seen from either hole it is a one-hole zipper
    ([zi], [zj]), and a two-hole zipper of [ext]s is a one-hole witness
    for either sort ([wi], [wj]); all of these are plain functions.

    The commuting law is a class over two-hole zippers ([commute]): both
    substitutions act on the family at the two-hole zipper ([T2]), so
    nothing relates the two views.  A user registers their own two
    Kleisli functions with [from_i] and [from_j]: at their concrete
    number of sorts both views plug to the same vector by computation.
    The morphism mapped by the other substitution ([tmap]) is defined
    once, from the class.  Checked on System F, the law by a routine
    induction.  Build with
      rocq compile -R theories ShiftedNames -Q proto/sorts Proto proto/sorts/Focus.v
      rocq compile -R theories ShiftedNames -Q proto/sorts Proto proto/sorts/Commute.v *)

From Stdlib Require Import Arith List StrictProp.
From ShiftedNames.Core Require Import Strict Label Var Scoped Indexed.
From ShiftedNames.Core Require Syntax.
Import Syntax (ext, ext_here, ext_under).
From Proto Require Import Focus.

(** ** Two-hole zippers *)

(** Appending (the sorts between, then [j] and the rest, seen from [i]). *)
Fixpoint vapp (c b : nat) : vec c -> vec b -> vec (c + b) :=
  match c as c0 return vec c0 -> vec b -> vec (c0 + b) with
  | 0 => fun _ r => r
  | S c => fun m r => pair (first m) (vapp c b (second m) r)
  end.

Fixpoint wvapp (c b : nat) : forall Bm Mm Km Lm B M K L, wit c Bm Mm Km Lm -> wit b B M K L ->
    wit (c + b) (vapp c b Bm B) (vapp c b Mm M) (vapp c b Km K) (vapp c b Lm L) :=
  match c with
  | 0 => fun _ _ _ _ _ _ _ _ _ w => w
  | S c => fun Bm Mm Km Lm B M K L wm w => pair (first wm) (wvapp c b _ _ _ _ _ _ _ _ (second wm) w)
  end.

Fixpoint wrev_app (c b : nat) {struct c} : forall Bm Mm Km Lm B M K L, wit c Bm Mm Km Lm -> wit b B M K L ->
    wit (radd c b) (rev_app c b Bm B) (rev_app c b Mm M) (rev_app c b Km K) (rev_app c b Lm L) :=
  match c as c0 return forall b Bm Mm Km Lm B M K L, wit c0 Bm Mm Km Lm -> wit b B M K L ->
      wit (radd c0 b) (rev_app c0 b Bm B) (rev_app c0 b Mm M) (rev_app c0 b Km K) (rev_app c0 b Lm L) with
  | 0 => fun _ _ _ _ _ _ _ _ _ _ w => w
  | S c => fun b Bm Mm Km Lm B M K L wm w =>
      wrev_app c (S b) _ _ _ _ (pair (first Bm) B) (pair (first Mm) M) (pair (first Km) K) (pair (first Lm) L) (second wm) (pair (first wm) w)
  end b.

Definition scopes2 (a c d : nat) : Type := both (vec a) (both nat (both (vec c) (both nat (vec d)))).

Section Holes.

Context {a c d : nat}.

Definition zl (Z : scopes2 a c d) : vec a := first Z.
Definition zx (Z : scopes2 a c d) : nat := first (second Z).
Definition zm (Z : scopes2 a c d) : vec c := first (second (second Z)).
Definition zy (Z : scopes2 a c d) : nat := first (second (second (second Z))).
Definition zr (Z : scopes2 a c d) : vec d := second (second (second (second Z))).

(** [Z] with [i]'s scope [k]; with [j]'s. *)
Definition setx (Z : scopes2 a c d) (k : nat) : scopes2 a c d := pair (zl Z) (pair k (second (second Z))).
Definition sety (Z : scopes2 a c d) (k : nat) : scopes2 a c d := pair (zl Z) (pair (zx Z) (pair (zm Z) (pair k (zr Z)))).

(** The output of a substitution of [i], of [j]. *)
Definition outx (K L : scopes2 a c d) : scopes2 a c d := setx K (zx L).
Definition outy (K L : scopes2 a c d) : scopes2 a c d := sety K (zy L).

(** Seen from [i], from [j]. *)
Definition zi (Z : scopes2 a c d) : scopes a (c + S d) := pair (zl Z) (pair (zx Z) (vapp c (S d) (zm Z) (pair (zy Z) (zr Z)))).
Definition zj (Z : scopes2 a c d) : scopes (radd c (S a)) d := pair (rev_app c (S a) (zm Z) (pair (zx Z) (zl Z))) (pair (zy Z) (zr Z)).

(** A two-hole zipper of [ext]s. *)
Definition descent2 (B M K L : scopes2 a c d) : Type :=
  both (wit a (zl B) (zl M) (zl K) (zl L))
    (both (ext (zx B) (zx M) (zx K) (zx L))
       (both (wit c (zm B) (zm M) (zm K) (zm L))
          (both (ext (zy B) (zy M) (zy K) (zy L)) (wit d (zr B) (zr M) (zr K) (zr L))))).

Context {B M K L : scopes2 a c d}.

Definition ex (X : descent2 B M K L) := first (second X).
Definition ey (X : descent2 B M K L) := first (second (second (second X))).

Definition wi (X : descent2 B M K L) : descent a (c + S d) (zi B) (zi M) (zi K) (zi L) :=
  pair (first X) (pair (ex X) (wvapp c (S d) _ _ _ _ (pair (zy B) (zr B)) (pair (zy M) (zr M)) (pair (zy K) (zr K)) (pair (zy L) (zr L))
                                 (first (second (second X))) (second (second (second X))))).

Definition wj (X : descent2 B M K L) : descent (radd c (S a)) d (zj B) (zj M) (zj K) (zj L) :=
  pair (wrev_app c (S a) _ _ _ _ (pair (zx B) (zl B)) (pair (zx M) (zl M)) (pair (zx K) (zl K)) (pair (zx L) (zl L))
          (first (second (second X))) (pair (ex X) (first X))) (second (second (second X))).

(** [i]'s witness read from the other side; [j]'s. *)
Definition flipx (X : descent2 B M K L) : descent2 (setx B (zx M)) (setx M (zx B)) (setx K (zx L)) (setx L (zx K)) :=
  pair (first X) (pair (ext_flip (ex X)) (second (second X))).
Definition flipy (X : descent2 B M K L) : descent2 (sety B (zy M)) (sety M (zy B)) (sety K (zy L)) (sety L (zy K)) :=
  pair (first X) (pair (ex X) (pair (first (second (second X))) (pair (ext_flip (ey X)) (second (second (second (second X))))))).

(** Under a binder of [i]'s sort, of [j]'s (for the user's proofs). *)
Definition xunder (X : descent2 B M K L) : descent2 B M (setx K (S (zx K))) (setx L (S (zx L))) :=
  pair (first X) (pair (ext_under (ex X)) (second (second X))).
Definition yunder (X : descent2 B M K L) : descent2 B M (sety K (S (zy K))) (sety L (S (zy L))) :=
  pair (first X) (pair (ex X) (pair (first (second (second X))) (pair (ext_under (ey X)) (second (second (second (second X))))))).

End Holes.

(** Back from [j]'s view (registering a user's Kleisli function for [j]). *)
Fixpoint unzj (c : nat) : forall a d, scopes (radd c (S a)) d -> scopes2 a c d :=
  match c with
  | 0 => fun a d z => pair (second (zleft z)) (pair (first (zleft z)) (pair tt (second z)))
  | S c => fun a d z =>
      let Z := unzj c (S a) d z in
      pair (second (zl Z)) (pair (first (zl Z)) (pair (pair (zx Z) (zm Z)) (second (second (second Z)))))
  end.

(** The first sort between moved to the left of [i]'s hole: the same
    view from [j]. *)
Definition shift {a c d} (Z : scopes2 a (S c) d) : scopes2 (S a) c d :=
  pair (pair (zx Z) (zl Z)) (pair (first (zm Z)) (pair (second (zm Z)) (second (second (second Z))))).

(** A witness from [j]'s view, at the two-hole bases it was seen from. *)
Fixpoint unwj (c : nat) : forall a d (B M : scopes2 a c d) K L, descent (radd c (S a)) d (zj B) (zj M) K L -> descent2 B M (unzj c a d K) (unzj c a d L) :=
  match c with
  | 0 => fun a d B M K L x => pair (second (first x)) (pair (first (first x)) (pair tt (second x)))
  | S c => fun a d B M K L x =>
      let X := unwj c (S a) d (shift B) (shift M) K L x in
      pair (second (first X)) (pair (first (first X)) (pair (pair (ex X) (first (second (second X)))) (second (second (second X)))))
  end.

Arguments unzj {c a d} & z.
Arguments unwj {c a d} B M {K L} x.

(** ** The commuting law *)

Section Commute.

Context {a c d : nat}.

(** Which of the family's sorts [i]'s carrier has, around the two holes
    ([j]'s sort dropped). *)
Definition zsub2 (s : mask) (Z : scopes2 a c d) : scopes (lkept s a) (rkept s a c + rkept s (S (a + c)) d) :=
  pair (restr (tl_of s a) (zl Z))
    (pair (zx Z) (vapp _ _ (restr (tr_of s a c) (zm Z)) (restr (tr_of s (S (a + c)) d) (zr Z)))).

Context (T : vec (radd a (S (c + S d))) -> Type).

(** The family at a two-hole zipper. *)
Definition T2 (Z : scopes2 a c d) : Type := T (plug (zi Z)).

(** Morphisms of [j]'s sort, into the family. *)
Definition ymorph (B M : scopes2 a c d) : Type :=
  forall K L, descent2 B M K L -> var (zy K) -> T2 (outy K L).

(** The two substitutions: [i]'s along its morphisms ([xmorph], whatever
    they are: the morphisms of the user's Kleisli function, found when
    registering it), [j]'s along [ymorph]. *)
Record two_sorts : Type := {
  xmorph : scopes2 a c d -> scopes2 a c d -> Type;
  kx : forall B M (h : xmorph B M) yb ym K L, descent2 (sety B yb) (sety M ym) K L -> T2 K -> T2 (outx K L);
  ky : forall B M (f : ymorph B M) K L, descent2 B M K L -> T2 K -> T2 (outy K L) }.

(** [j]'s morphism with its results' [i]-sort substituted, at [i]'s
    witness read back. *)
Definition tmap (p : two_sorts) {B M} (h : xmorph p B M) (f : ymorph B M) : ymorph (setx B (zx M)) (setx M (zx B)) :=
  fun K L X v => kx p B M h (zy M) (zy B) _ _ (flipy (flipx X)) (f _ _ (flipx X) v).

Record commute (p : two_sorts) : Prop := {
  move : forall B M (h : xmorph p B M) (f : ymorph B M) K L (X : descent2 B M K L) t,
    kx p B M h (zy M) (zy B) _ _ (flipy X) (ky p _ _ f _ _ X t)
    = ky p _ _ (tmap p h f) _ _ (flipx X) (kx p B M h (zy B) (zy M) _ _ X t) }.

End Commute.

Arguments commute {a c d T} p.

(** Registering the user's Kleisli functions (one hole each). *)
Notation from_i k := (fun B M h yb ym K L X t => k (zi (sety B yb)) (zi (sety M ym)) h _ _ (wi X) t) (only parsing).
Notation from_j k := (fun B M f K L X t =>
  k (zj B) (zj M) (fun K' L' x v => f (unzj K') (unzj L') (unwj B M x) v) _ _ (wj X) t) (only parsing).
(** Sorts [i] and [j] of [n], with the user's Kleisli functions for them. *)
(** [i]'s morphisms are read off the user's function (its first argument
    at [j]'s bases 0, which it does not see). *)
Notation register n i j T kx ky :=
  (@Build_two_sorts i (j - S i) (n - S j) T
     (fun B M => ltac:(let ty := type of (kx (zi (sety B 0)) (zi (sety M 0))) in
                       lazymatch ty with forall _ : ?A, _ => let A' := eval cbn in A in exact A' end))
     (from_i kx) (from_j ky)) (only parsing).

(** Under a binder of a sort left of the holes, between them, right of
    them (for the proofs). *)
Definition setl {a c d} (Z : scopes2 a c d) (l : vec a) : scopes2 a c d := pair l (second Z).
Definition setm {a c d} (Z : scopes2 a c d) (m : vec c) : scopes2 a c d := pair (zl Z) (pair (zx Z) (pair m (second (second (second Z))))).
Definition setr {a c d} (Z : scopes2 a c d) (r : vec d) : scopes2 a c d := pair (zl Z) (pair (zx Z) (pair (zm Z) (pair (zy Z) r))).

Definition lunder {a c d} p {B M K L : scopes2 a c d} (X : descent2 B M K L)
    : descent2 B M (setl K (upd a p (S (get a p (zl K))) (zl K))) (setl L (upd a p (S (get a p (zl L))) (zl L))) :=
  pair (wunder a p _ _ _ _ (first X)) (second X).
Definition munder {a c d} p {B M K L : scopes2 a c d} (X : descent2 B M K L)
    : descent2 B M (setm K (upd c p (S (get c p (zm K))) (zm K))) (setm L (upd c p (S (get c p (zm L))) (zm L))) :=
  pair (first X) (pair (ex X) (pair (wunder c p _ _ _ _ (first (second (second X)))) (second (second (second X))))).
Definition runder {a c d} p {B M K L : scopes2 a c d} (X : descent2 B M K L)
    : descent2 B M (setr K (upd d p (S (get d p (zr K))) (zr K))) (setr L (upd d p (S (get d p (zr L))) (zr L))) :=
  pair (first X) (pair (ex X) (pair (first (second (second X))) (pair (ey X) (wunder d p _ _ _ _ (second (second (second (second X)))))))).

(** The law's proof: by recursion on the term; at a variable the views
    are unfolded; under a binder, the witness goes under. *)
Ltac commute_var :=
  cbv [tmap flipx flipy wj wi ex ey shift setx sety outx outy];
  cbn [first second unwj wrev_app wvapp];
  rewrite ?ext_flip_flip; reflexivity.

Ltac commute_ih IH X :=
  first [ exact (IH _ _ X _) | exact (IH _ _ (xunder X) _) | exact (IH _ _ (yunder X) _)
        | exact (IH _ _ (munder 0 X) _) | exact (IH _ _ (munder 1 X) _) | exact (IH _ _ (munder 2 X) _)
        | exact (IH _ _ (lunder 0 X) _) | exact (IH _ _ (lunder 1 X) _) | exact (IH _ _ (lunder 2 X) _)
        | exact (IH _ _ (runder 0 X) _) | exact (IH _ _ (runder 1 X) _) | exact (IH _ _ (runder 2 X) _) ].

Ltac commute_proof :=
  let IH := fresh "IH" in let X := fresh "X" in let t := fresh "t" in
  constructor; intros ? ? ? ?; cbn;
  fix IH 4; intros ? ? X t; destruct t; cbn;
  first [ commute_var | f_equal; try reflexivity; commute_ih IH X ].

(** ** System F: types (sort 0) past terms (sort 1) *)

Definition tm_types_terms := register 2 0 1 (uncurry 2 tm) (@kl_tmty) (@kl_tm).

Theorem tm_commute : commute tm_types_terms.
Proof. commute_proof. Qed.

(** ** A sort in between: types (0) past terms (2), regions (1) between *)

Inductive tm3 (N R K : nat) : Type :=
| var3 (v : var K)
| lam3 (A : ty N) (b : tm3 N R (S K))
| app3 (t u : tm3 N R K)
| rlam3 (b : tm3 N (S R) K)
| tlam3 (b : tm3 (S N) R K).

Arguments var3 {N R K} v.
Arguments lam3 {N R K} A b.
Arguments app3 {N R K} t u.
Arguments rlam3 {N R K} b.
Arguments tlam3 {N R K} b.

(** The user's two Kleisli functions. *)
Fixpoint kl_tm3 {B M} (f : morph 2 0 (uncurry 3 tm3) B M) {K L} (x : descent 2 0 B M K L) (t : tm3 @ K) : tm3 @ out K L :=
  match t with
  | var3 v => f K L x v
  | lam3 A u => lam3 A (kl_tm3 f (under 2 x) u)
  | app3 t u => app3 (kl_tm3 f x t) (kl_tm3 f x u)
  | rlam3 u => rlam3 (kl_tm3 f (under 1 x) u)
  | tlam3 u => tlam3 (kl_tm3 f (under 0 x) u)
  end.

Fixpoint kl_tm3ty {B M : scopes 0 2} (f : morph 0 0 (uncurry 1 ty) _ _) {K L} (x : descent 0 2 B M K L) (t : tm3 @ K) : tm3 @ out K L :=
  match t with
  | var3 v => var3 v
  | lam3 A u => lam3 (kl_ty f x‹+ - -› A) (kl_tm3ty f (under 2 x) u)
  | app3 t u => app3 (kl_tm3ty f x t) (kl_tm3ty f x u)
  | rlam3 u => rlam3 (kl_tm3ty f (under 1 x) u)
  | tlam3 u => tlam3 (kl_tm3ty f (under 0 x) u)
  end.

Definition tm3_types_terms := register 3 0 2 (uncurry 3 tm3) (@kl_tm3ty) (@kl_tm3).

Theorem tm3_commute : commute tm3_types_terms.
Proof. commute_proof. Qed.
