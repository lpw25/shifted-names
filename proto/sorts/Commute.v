(** * Prototype: moving a substitution of one sort past one of another

    Two sorts of a family, [i] left of [j]: the scopes are a zipper with
    two holes ([zip2 a c d]: the [a] sorts left of [i], nearest first;
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

Definition zip2 (a c d : nat) : Type := both (vec a) (both nat (both (vec c) (both nat (vec d)))).

Section Holes.

Context {a c d : nat}.

Definition zl (Z : zip2 a c d) : vec a := first Z.
Definition zx (Z : zip2 a c d) : nat := first (second Z).
Definition zm (Z : zip2 a c d) : vec c := first (second (second Z)).
Definition zy (Z : zip2 a c d) : nat := first (second (second (second Z))).
Definition zr (Z : zip2 a c d) : vec d := second (second (second (second Z))).

(** [Z] with [i]'s scope [k]; with [j]'s. *)
Definition setx (Z : zip2 a c d) (k : nat) : zip2 a c d := pair (zl Z) (pair k (second (second Z))).
Definition sety (Z : zip2 a c d) (k : nat) : zip2 a c d := pair (zl Z) (pair (zx Z) (pair (zm Z) (pair k (zr Z)))).

(** The output of a substitution of [i], of [j]. *)
Definition outx (K L : zip2 a c d) : zip2 a c d := setx K (zx L).
Definition outy (K L : zip2 a c d) : zip2 a c d := sety K (zy L).

(** Seen from [i], from [j]. *)
Definition zi (Z : zip2 a c d) : zip a (c + S d) := pair (zl Z) (pair (zx Z) (vapp c (S d) (zm Z) (pair (zy Z) (zr Z)))).
Definition zj (Z : zip2 a c d) : zip (radd c (S a)) d := pair (rev_app c (S a) (zm Z) (pair (zx Z) (zl Z))) (pair (zy Z) (zr Z)).

(** A two-hole zipper of [ext]s. *)
Definition fwit2 (B M K L : zip2 a c d) : Type :=
  both (wit a (zl B) (zl M) (zl K) (zl L))
    (both (ext (zx B) (zx M) (zx K) (zx L))
       (both (wit c (zm B) (zm M) (zm K) (zm L))
          (both (ext (zy B) (zy M) (zy K) (zy L)) (wit d (zr B) (zr M) (zr K) (zr L))))).

Context {B M K L : zip2 a c d}.

Definition ex (X : fwit2 B M K L) := first (second X).
Definition ey (X : fwit2 B M K L) := first (second (second (second X))).

Definition wi (X : fwit2 B M K L) : fwit a (c + S d) (zi B) (zi M) (zi K) (zi L) :=
  pair (first X) (pair (ex X) (wvapp c (S d) _ _ _ _ (pair (zy B) (zr B)) (pair (zy M) (zr M)) (pair (zy K) (zr K)) (pair (zy L) (zr L))
                                 (first (second (second X))) (second (second (second X))))).

Definition wj (X : fwit2 B M K L) : fwit (radd c (S a)) d (zj B) (zj M) (zj K) (zj L) :=
  pair (wrev_app c (S a) _ _ _ _ (pair (zx B) (zl B)) (pair (zx M) (zl M)) (pair (zx K) (zl K)) (pair (zx L) (zl L))
          (first (second (second X))) (pair (ex X) (first X))) (second (second (second X))).

(** [i]'s witness read from the other side; [j]'s. *)
Definition flipx (X : fwit2 B M K L) : fwit2 (setx B (zx M)) (setx M (zx B)) (setx K (zx L)) (setx L (zx K)) :=
  pair (first X) (pair (ext_flip (ex X)) (second (second X))).
Definition flipy (X : fwit2 B M K L) : fwit2 (sety B (zy M)) (sety M (zy B)) (sety K (zy L)) (sety L (zy K)) :=
  pair (first X) (pair (ex X) (pair (first (second (second X))) (pair (ext_flip (ey X)) (second (second (second (second X))))))).

(** Under a binder of [i]'s sort, of [j]'s (for the user's proofs). *)
Definition xunder (X : fwit2 B M K L) : fwit2 B M (setx K (S (zx K))) (setx L (S (zx L))) :=
  pair (first X) (pair (ext_under (ex X)) (second (second X))).
Definition yunder (X : fwit2 B M K L) : fwit2 B M (sety K (S (zy K))) (sety L (S (zy L))) :=
  pair (first X) (pair (ex X) (pair (first (second (second X))) (pair (ext_under (ey X)) (second (second (second (second X))))))).

End Holes.

(** Back from [j]'s view (registering a user's Kleisli function for [j]). *)
Fixpoint unzj (c : nat) : forall a d, zip (radd c (S a)) d -> zip2 a c d :=
  match c with
  | 0 => fun a d z => pair (second (zleft z)) (pair (first (zleft z)) (pair tt (second z)))
  | S c => fun a d z =>
      let Z := unzj c (S a) d z in
      pair (second (zl Z)) (pair (first (zl Z)) (pair (pair (zx Z) (zm Z)) (second (second (second Z)))))
  end.

(** The first sort between moved to the left of [i]'s hole: the same
    view from [j]. *)
Definition shift {a c d} (Z : zip2 a (S c) d) : zip2 (S a) c d :=
  pair (pair (zx Z) (zl Z)) (pair (first (zm Z)) (pair (second (zm Z)) (second (second (second Z))))).

(** A witness from [j]'s view, at the two-hole bases it was seen from. *)
Fixpoint unwj (c : nat) : forall a d (B M : zip2 a c d) K L, fwit (radd c (S a)) d (zj B) (zj M) K L -> fwit2 B M (unzj c a d K) (unzj c a d L) :=
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
Definition zsub2 (s : mask) (Z : zip2 a c d) : zip (lkept s a) (rkept s a c + rkept s (S (a + c)) d) :=
  pair (restr (tl_of s a) (zl Z))
    (pair (zx Z) (vapp _ _ (restr (tr_of s a c) (zm Z)) (restr (tr_of s (S (a + c)) d) (zr Z)))).

Context (T : vec (radd a (S (c + S d))) -> Type) (s : mask)
  (Q : vec (radd (lkept s a) (S (rkept s a c + rkept s (S (a + c)) d))) -> Type).

(** The family at a two-hole zipper. *)
Definition T2 (Z : zip2 a c d) : Type := T (plug (zi Z)).

(** Morphisms of [i]'s sort (into [Q]) and of [j]'s (into the family). *)
Definition xmorph (B M : zip2 a c d) : Type :=
  morph (lkept s a) (rkept s a c + rkept s (S (a + c)) d) Q (zsub2 s B) (zsub2 s M).
Definition ymorph (B M : zip2 a c d) : Type :=
  forall K L, fwit2 B M K L -> var (zy K) -> T2 (outy K L).

Definition kx_t : Type := forall B M (h : xmorph B M) K L, fwit2 B M K L -> T2 K -> T2 (outx K L).
Definition ky_t : Type := forall B M (f : ymorph B M) K L, fwit2 B M K L -> T2 K -> T2 (outy K L).

(** [j]'s morphism with its results' [i]-sort substituted, at [i]'s
    witness read back. *)
Definition tmap (kx : kx_t) {B M} (h : xmorph B M) (f : ymorph B M) : ymorph (setx B (zx M)) (setx M (zx B)) :=
  fun K L X v => kx (sety B (zy M)) (sety M (zy B)) h _ _ (flipy (flipx X)) (f _ _ (flipx X) v).

Record commute (kx : kx_t) (ky : ky_t) : Prop := {
  move : forall B M (h : xmorph B M) (f : ymorph B M) K L (X : fwit2 B M K L) t,
    kx (sety B (zy M)) (sety M (zy B)) h _ _ (flipy X) (ky _ _ f _ _ X t) = ky _ _ (tmap kx h f) _ _ (flipx X) (kx _ _ h _ _ X t) }.

End Commute.

(** Registering the user's Kleisli functions (one hole each). *)
Notation from_i k := (fun B M h K L X t => k (zi B) (zi M) h _ _ (wi X) t) (only parsing).
Notation from_j k := (fun B M f K L X t =>
  k (zj B) (zj M) (fun K' L' x v => f (unzj K') (unzj L') (unwj B M x) v) _ _ (wj X) t) (only parsing).

(** ** System F: types (sort 0) past terms (sort 1) *)

Definition tm_kx : kx_t (a := 0) (c := 0) (d := 0) (uncurry 2 tm) (true :: false :: nil) (uncurry 1 ty) := from_i (@kl_tmty).
Definition tm_ky : ky_t (a := 0) (c := 0) (d := 0) (uncurry 2 tm) := from_j (@kl_tm).

Theorem tm_commute : commute (a := 0) (c := 0) (d := 0) (uncurry 2 tm) (true :: false :: nil) (uncurry 1 ty) tm_kx tm_ky.
Proof.
  constructor; intros B M h f; unfold tm_kx, tm_ky.
  fix IH 4; intros K L X t; destruct t; cbn [kl_tm kl_tmty].
  - unfold tmap, flipx, flipy, wj; cbn [first second unwj wrev_app]; unfold ex; cbn [first second]; rewrite ext_flip_flip; reflexivity.
  - f_equal; exact (IH _ _ (yunder X) t).
  - f_equal; [exact (IH _ _ X t1) | exact (IH _ _ X t2)].
  - f_equal; exact (IH _ _ (xunder X) t).
  - f_equal; exact (IH _ _ X t).
Qed.

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
Fixpoint kl_tm3 {B M} (f : morph 2 0 (uncurry 3 tm3) B M) {K L} (x : fwit 2 0 B M K L) (t : tm3 @ K) : tm3 @ out K L :=
  match t with
  | var3 v => f K L x v
  | lam3 A u => lam3 A (kl_tm3 f (under 2 x) u)
  | app3 t u => app3 (kl_tm3 f x t) (kl_tm3 f x u)
  | rlam3 u => rlam3 (kl_tm3 f (under 1 x) u)
  | tlam3 u => tlam3 (kl_tm3 f (under 0 x) u)
  end.

Fixpoint kl_tm3ty {B M : zip 0 2} (f : morph 0 0 (uncurry 1 ty) _ _) {K L} (x : fwit 0 2 B M K L) (t : tm3 @ K) : tm3 @ out K L :=
  match t with
  | var3 v => var3 v
  | lam3 A u => lam3 (kl_ty f x‹+ - -› A) (kl_tm3ty f (under 2 x) u)
  | app3 t u => app3 (kl_tm3ty f x t) (kl_tm3ty f x u)
  | rlam3 u => rlam3 (kl_tm3ty f (under 1 x) u)
  | tlam3 u => tlam3 (kl_tm3ty f (under 0 x) u)
  end.

(** Under a binder of a sort between the holes (for the proofs). *)
Definition setm {a c d} (Z : zip2 a c d) (m : vec c) : zip2 a c d := pair (zl Z) (pair (zx Z) (pair m (second (second (second Z))))).

Definition munder {a c d} p {B M K L : zip2 a c d} (X : fwit2 B M K L)
    : fwit2 B M (setm K (upd c p (S (get c p (zm K))) (zm K))) (setm L (upd c p (S (get c p (zm L))) (zm L))) :=
  pair (first X) (pair (ex X) (pair (wunder c p _ _ _ _ (first (second (second X)))) (second (second (second X))))).

Definition tm3_kx : kx_t (a := 0) (c := 1) (d := 0) (uncurry 3 tm3) (true :: false :: false :: nil) (uncurry 1 ty) := from_i (@kl_tm3ty).
Definition tm3_ky : ky_t (a := 0) (c := 1) (d := 0) (uncurry 3 tm3) := from_j (@kl_tm3).

Theorem tm3_commute : commute (a := 0) (c := 1) (d := 0) (uncurry 3 tm3) (true :: false :: false :: nil) (uncurry 1 ty) tm3_kx tm3_ky.
Proof.
  constructor; intros B M h f; unfold tm3_kx, tm3_ky.
  fix IH 4; intros K L X t; destruct t; cbn [kl_tm3 kl_tm3ty].
  - unfold tmap, flipx, flipy, wj; cbn [first second unwj wrev_app]; unfold ex, shift; cbn [first second]; rewrite ext_flip_flip; reflexivity.
  - f_equal; exact (IH _ _ (yunder X) t).
  - f_equal; [exact (IH _ _ X t1) | exact (IH _ _ X t2)].
  - f_equal; exact (IH _ _ (munder 0 X) t).
  - f_equal; exact (IH _ _ (xunder X) t).
Qed.
