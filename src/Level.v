Require Import String Omega Setoid Morphisms.
Require Import Morph.

(* Bound variables are represented by a level *)

Definition Zero := Empty_set.

Inductive Succ {S : Set} : Set := l0 | lS (s : S).

Fixpoint level (V : nat) : Set :=
  match V with
  | 0 => Zero
  | S V => @Succ (level V)
  end.
Arguments level !V.

(* Liftable morphisms from [level]s that we treat like streams *)
Definition ilevel N T M := morph level N T M.

Bind Scope morph_scope with ilevel.

Definition hd_ilevel {N T M} (f : ilevel (S N) T M) : pnset T M :=
  fun V => @f V l0.

Definition tl_ilevel {N T M} (f : ilevel (S N) T M)
  : ilevel N T M :=
  fun V l => f V (lS l).

Definition cons_ilevel {N T M} (a : pnset T M)
           (f : ilevel N T M) : ilevel (S N) T M :=
  fun V l =>
    match l with
    | l0 => a V
    | lS l => f V l
    end.

Arguments hd_ilevel {N T M} f V /.
Arguments tl_ilevel {N T M} f V l /.
Arguments cons_ilevel {N T M} a f V !l.

(* Derived operations *)

Definition swap_ilevel {N T M} (f : ilevel (S (S N)) T M) :=
  cons_ilevel (hd_ilevel (tl_ilevel f))
    (cons_ilevel (hd_ilevel f)
      (tl_ilevel (tl_ilevel f))).

(* Morphism definitions *)

Add Parametric Morphism {N T M} : (@hd_ilevel N T M)
    with signature eq_morph ==> eq_pnset
      as hd_ilevel_mor.
  intros * Heq; unfold hd_ilevel; intro.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {N T M} : (@tl_ilevel N T M)
    with signature eq_morph ==> eq_morph
      as tl_ilevel_mor.
  intros * Heq V l; unfold tl_ilevel.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {N T M} : (@cons_ilevel N T M)
    with signature eq_pnset ==> eq_morph ==> eq_morph
    as cons_ilevel_mor.
  intros * Heq1 * Heq2 V l; unfold cons_ilevel.
  destruct l; rewrite ?Heq1, ?Heq2; easy.
Qed.

Add Parametric Morphism {N T M} : (@swap_ilevel N T M)
    with signature eq_morph ==> eq_morph
    as swap_ilevel_mor.
  intros * Heq V l; unfold swap_ilevel.
  destruct l; rewrite ?Heq; easy.
Qed.

(* Beta and eta rules for [ilevel] operations *)

Lemma ilevel_beta_hd {N} {T : nset} {M} (a : forall V, T (M + V))
      (f : ilevel N T M) :
  hd_ilevel (cons_ilevel a f) = a.
Proof. easy. Qed.

Lemma ilevel_beta_tl {N} {T : nset} {M} (a : forall V, T (M + V))
      (f : ilevel N T M) :
  tl_ilevel (cons_ilevel a f) = f.
Proof. easy. Qed.

Lemma ilevel_eta {N T M} (f : ilevel (S N) T M) :
  cons_ilevel (hd_ilevel f) (tl_ilevel f) =m= f.
Proof.
  intros V l.
  destruct l; cbn; easy.
Qed.

Hint Rewrite @ilevel_beta_hd @ilevel_beta_tl @ilevel_eta
  : simpl_ilevels.

(* Unfolding derived operations *)

Lemma unfold_swap_ilevel {N T M} (f : ilevel (S (S N)) T M) :
  swap_ilevel f
  = cons_ilevel (hd_ilevel (tl_ilevel f))
      (cons_ilevel (hd_ilevel f)
        (tl_ilevel (tl_ilevel f))).
Proof. easy. Qed.

Hint Rewrite @unfold_swap_ilevel
  : unfold_ilevels.

(* Folding derived operations *)

Lemma fold_swap_ilevel {N T M} (f : ilevel (S (S N)) T M) :
  cons_ilevel (hd_ilevel (tl_ilevel f))
      (cons_ilevel (hd_ilevel f)
        (tl_ilevel (tl_ilevel f)))
      = swap_ilevel f.
Proof. easy. Qed.

Hint Rewrite @fold_swap_ilevel
  : fold_ilevels.

(* Simplify [ilevel] terms by unfolding, simplifying and folding *)
Ltac simpl_ilevels :=
  autorewrite with unfold_ilevels;
  autorewrite with simpl_ilevels;
  repeat progress
    (cbn;
     try (rewrite_strat topdown (hints simpl_ilevels)));
  autorewrite with fold_ilevels.

(* There is a full covariant functor from [T O] to [ilevel N T O]
   by composition.

   Such composition distributes over our operations. *)

Lemma hd_ilevel_compose_distribute {N T M R L}
      (f : ilevel (S N) T M) (g : morph T M R L) :
  morph_apply g (hd_ilevel f) =p= hd_ilevel (g @ f).
Proof. easy. Qed.

Lemma tl_ilevel_compose_distribute {N T M R L}
      (f : ilevel (S N) T M) (g : morph T M R L) :
  g @ (tl_ilevel f) =m= tl_ilevel (g @ f).
Proof. easy. Qed.

Lemma cons_ilevel_compose_distribute {N T M R L} a
      (f : ilevel N T M) (g : morph T M R L) :
  g @ (cons_ilevel a f) =m= cons_ilevel (morph_apply g a) (g @ f).
Proof.
  intros V l.
  destruct l; easy.
Qed.

Lemma swap_ilevel_compose_distribute {N T M R L}
      (f : ilevel (S (S N)) T M) (g : morph T M R L) :
  g @ (swap_ilevel f) =m= swap_ilevel (g @ f).
Proof.
  unfold swap_ilevel.
  rewrite cons_ilevel_compose_distribute.
  rewrite hd_ilevel_compose_distribute.
  rewrite tl_ilevel_compose_distribute.
  rewrite cons_ilevel_compose_distribute.
  rewrite hd_ilevel_compose_distribute.
  rewrite tl_ilevel_compose_distribute.
  easy.
Qed.

