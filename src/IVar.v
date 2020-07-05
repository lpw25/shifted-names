Require Import String Omega Setoid Morphisms.
Require Import Morph Var IIndex IName ILevel.

(* Liftable morphisms from [var]s that we treat like pairs *)
Definition ivar N T M := morph var N T M.

Bind Scope morph_scope with ivar.

Definition fst_ivar {N T M} (f : ivar N T M) : iname T M :=
    fun V (n : name) => f V (free n).
Arguments fst_ivar {N T M} f V n /.

Definition snd_ivar {N T M} (f : ivar N T M) : ilevel N T M :=
    fun V (l : level (N + V)) => f V (bound l).
Arguments snd_ivar {N T M} f V l /.

Definition pair_ivar {N T M} (f : iname T M)
           (g : ilevel N T M) : ivar N T M :=
  fun V v =>
    match v with
    | free n => f V n
    | bound l => g V l
    end.
Arguments pair_ivar {N T M} f g V !v.

(* Derived operations *)

Definition open_ivar {N T M} n (f : ivar N T M)
  : ivar (S N) T M :=
  pair_ivar
    (delete_iname n (fst_ivar f))
    (cons_ilevel (get_iname n (fst_ivar f)) (snd_ivar f)).

Definition close_ivar {N T M} n (f : ivar (S N) T M) : ivar N T M :=
  pair_ivar
    (insert_iname (hd_ilevel (snd_ivar f)) n (fst_ivar f))
    (tl_ilevel (snd_ivar f)).

Definition weak_ivar {N T M} (f : ivar (S N) T M) : ivar N T M :=
  pair_ivar (fst_ivar f) (tl_ilevel (snd_ivar f)).

Definition bind_ivar {N T M} (a : pnset T M) (f : ivar N T M)
  : ivar (S N) T M :=
  pair_ivar (fst_ivar f) (cons_ilevel a (snd_ivar f)).

Definition swap_ivar {N T M} l (f : ivar (S N) T M)
  : ivar (S N) T M :=
  pair_ivar (fst_ivar f) (swap_ilevel l (snd_ivar f)).

(* Morphism definitions *)

Add Parametric Morphism {N T M} : (@fst_ivar N T M)
    with signature eq_morph ==> eq_kmorph
    as fst_ivar_mor.
  intros * Heq V n; unfold fst_ivar.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {N T M} : (@snd_ivar N T M)
    with signature eq_morph ==> eq_morph
    as snd_ivar_mor.
  intros * Heq V n; unfold snd_ivar.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {N T M} : (@pair_ivar N T M)
    with signature eq_kmorph ==> eq_morph ==> eq_morph
    as pair_ivar_mor.
  intros * Heq1 f g Heq2 V v; unfold pair_ivar.
  destruct v; rewrite ?Heq1, ?Heq2; easy.
Qed.

Add Parametric Morphism {N T M} : (@open_ivar N T M)
    with signature eq ==> eq_morph ==> eq_morph
    as open_ivar_mor.
  intros * Heq V v; unfold open_ivar.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {N T M} : (@close_ivar N T M)
    with signature eq ==> eq_morph ==> eq_morph
    as close_ivar_mor.
  intros * Heq V v; unfold close_ivar.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {N T M} : (@weak_ivar N T M)
    with signature eq_morph ==> eq_morph
    as weak_ivar_mor.
  intros * Heq V v; unfold weak_ivar.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {N T M} : (@bind_ivar N T M)
    with signature eq_pnset ==> eq_morph ==> eq_morph
    as bind_ivar_mor.
  intros * Heq1 * Heq2 V v; unfold bind_ivar.
  rewrite Heq1, Heq2; easy.
Qed.

Add Parametric Morphism {N T M l} : (@swap_ivar N T M l)
    with signature eq_morph ==> eq_morph
    as swap_ivar_mor.
  intros * Heq V v; unfold swap_ivar.
  rewrite Heq; easy.
Qed.

(* Beta and eta rules for [ivar] operations *)

Lemma ivar_beta_fst {N T M} f (g : ilevel N T M) :
  fst_ivar (pair_ivar f g) = f.
Proof. easy. Qed.

Lemma ivar_beta_snd {N T M} f (g : ilevel N T M) :
  snd_ivar (pair_ivar f g) = g.
Proof. easy. Qed.

Lemma ivar_eta {N T M} (f : ivar N T M) :
  pair_ivar (fst_ivar f) (snd_ivar f) =m= f.
Proof.
  intros V v; destruct v; easy.
Qed.

Hint Rewrite @ivar_beta_fst @ivar_beta_snd @ivar_eta
  : simpl_ivars.

(* Unfolding derived operations *)

Lemma unfold_open_ivar {N T M} n (f : ivar N T M) :
  open_ivar n f
  = pair_ivar
      (delete_iname n (fst_ivar f))
      (cons_ilevel (get_iname n (fst_ivar f)) (snd_ivar f)).
Proof. easy. Qed.

Lemma unfold_close_ivar {N T M} n (f : ivar (S N) T M) :
  close_ivar n f
  = pair_ivar
      (insert_iname (hd_ilevel (snd_ivar f)) n (fst_ivar f))
      (tl_ilevel (snd_ivar f)).
Proof. easy. Qed.

Lemma unfold_weak_ivar {N T M} (f : ivar (S N) T M) :
  weak_ivar f
  = pair_ivar (fst_ivar f) (tl_ilevel (snd_ivar f)).
Proof. easy. Qed.

Lemma unfold_bind_ivar {N T M} a (f : ivar N T M) :
  bind_ivar a f
  = pair_ivar (fst_ivar f) (cons_ilevel a (snd_ivar f)).
Proof. easy. Qed.

Lemma unfold_swap_ivar {N T M} l (f : ivar (S N) T M) :
  swap_ivar l f
  = pair_ivar (fst_ivar f) (swap_ilevel l (snd_ivar f)).
Proof. easy. Qed.

Hint Rewrite @unfold_open_ivar @unfold_close_ivar
     @unfold_weak_ivar @unfold_bind_ivar @unfold_swap_ivar
  : unfold_ivars.

(* Folding derived operations *)

Lemma fold_open_ivar {N T M} n (f : ivar N T M) :
  pair_ivar
    (delete_iname n (fst_ivar f))
    (cons_ilevel (get_iname n (fst_ivar f)) (snd_ivar f))
  = open_ivar n f.
Proof. easy. Qed.

Lemma fold_close_ivar {N T M} n (f : ivar (S N) T M) :
  pair_ivar
    (insert_iname (hd_ilevel (snd_ivar f)) n (fst_ivar f))
    (tl_ilevel (snd_ivar f))
  = close_ivar n f.
Proof. easy. Qed.

Lemma fold_weak_ivar {N T M} (f : ivar (S N) T M) :
  pair_ivar (fst_ivar f) (tl_ilevel (snd_ivar f))
  = weak_ivar f.
Proof. easy. Qed.

Lemma fold_bind_ivar {N T M} a (f : ivar N T M) :
  pair_ivar (fst_ivar f) (cons_ilevel a (snd_ivar f))
  = bind_ivar a f.
Proof. easy. Qed.

Lemma fold_swap_ivar {N T M} l (f : ivar (S N) T M) :
  pair_ivar (fst_ivar f) (swap_ilevel l (snd_ivar f))
  = swap_ivar l f.
Proof. easy. Qed.

Hint Rewrite @fold_open_ivar @fold_close_ivar
     @fold_weak_ivar @fold_bind_ivar @fold_swap_ivar
  : fold_ivars.

(* Simplify [ivars] terms by unfolding, simplifying and folding *)
Ltac simpl_ivars :=
  autorewrite with unfold_ivars;
  autorewrite with simpl_ivars;
  autorewrite with unfold_ilevels;
  autorewrite with simpl_ilevels;
  autorewrite with unfold_inames;
  autorewrite with simpl_inames;
  autorewrite with simpl_iindexs;
  repeat progress
    (cbn;
     try (rewrite_strat topdown (hints simpl_ivars));
     try (rewrite_strat topdown (hints simpl_ilevels));
     try (rewrite_strat topdown (hints simpl_inames));
     try (rewrite_strat topdown (hints simpl_iindexs)));
  autorewrite with fold_inames fold_ilevels fold_ivars;
  try (rewrite_strat topdown (hints fold_inames)).

(* There is a full covariant functor from [T O] to [ivar N T O]
   by composition.

   Such composition distributes over our operations. *)

Lemma pair_ivar_compose_distribute {N T M R L}
      (f : iname T M) (g : ilevel N T M) (h : morph T M R L) :
  h @ (pair_ivar f g) =m= pair_ivar (h @ f) (h @ g).
Proof.
  intros V v.
  destruct v; easy.
Qed.

Lemma fst_ivar_compose_distribute {N T M R L}
      (f : ivar N T M) (g : morph T M R L) :
  g @ (fst_ivar f) =km= fst_ivar (g @ f).
Proof. easy. Qed.

Lemma snd_ivar_compose_distribute {N T M R L}
      (f : ivar N T M) (g : morph T M R L) :
  g @ (snd_ivar f) =m= snd_ivar (g @ f).
Proof. easy. Qed.

Lemma open_ivar_compose_distribute {N T M R L} n
      (f : ivar N T M) (g : morph T M R L) :
  g @ (open_ivar n f) =m= open_ivar n (g @ f).
Proof.
  unfold open_ivar.
  rewrite pair_ivar_compose_distribute.
  rewrite delete_iname_compose_distribute.
  rewrite fst_ivar_compose_distribute.
  rewrite cons_ilevel_compose_distribute.
  rewrite get_iname_compose_distribute.
  rewrite snd_ivar_compose_distribute.
  easy.
Qed.

Lemma close_ivar_compose_distribute {N T M R L} n
      (f : ivar (S N) T M) (g : morph T M R L) :
  g @ (close_ivar n f) =m= close_ivar n (g @ f).
Proof.
  unfold close_ivar.
  rewrite pair_ivar_compose_distribute.
  rewrite insert_iname_compose_distribute.
  rewrite hd_ilevel_compose_distribute.
  rewrite snd_ivar_compose_distribute.
  rewrite fst_ivar_compose_distribute.
  rewrite tl_ilevel_compose_distribute.
  rewrite snd_ivar_compose_distribute.
  easy.
Qed.

Lemma weak_ivar_compose_distribute {N T M R L}
      (f : ivar (S N) T M) (g : morph T M R L) :
  g @ (weak_ivar f) =m= weak_ivar (g @ f).
Proof.
  unfold weak_ivar.
  rewrite pair_ivar_compose_distribute.
  rewrite fst_ivar_compose_distribute.
  rewrite tl_ilevel_compose_distribute.
  rewrite snd_ivar_compose_distribute.
  easy.
Qed.

Lemma bind_ivar_compose_distribute {N T M R L} t
      (f : ivar N T M) (g : morph T M R L) :
  g @ (bind_ivar t f)
  =m= bind_ivar (morph_apply g t) (g @ f).
Proof.
  unfold bind_ivar.
  rewrite pair_ivar_compose_distribute.
  rewrite fst_ivar_compose_distribute.
  rewrite cons_ilevel_compose_distribute.
  rewrite snd_ivar_compose_distribute.
  easy.
Qed.

Lemma swap_ivar_compose_distribute {N T M R L} l
      (f : ivar (S N) T M) (g : morph T M R L) :
  g @ swap_ivar l f
  =m= swap_ivar l (g @ f).
Proof.
  unfold swap_ivar.
  rewrite pair_ivar_compose_distribute.
  rewrite fst_ivar_compose_distribute.
  rewrite swap_ilevel_compose_distribute.
  rewrite snd_ivar_compose_distribute.
  easy.
Qed.


(* Morphism extension distributes over the operations *)

Lemma fst_ivar_extend {N T M} (f : ivar N T M) :
  kmorph_extend (fst_ivar f)
  =km= fst_ivar (morph_extend f).
Proof.
  intros V v; simplT; easy.
Qed.

Lemma snd_ivar_extend {N T M} (f : ivar N T M) :
  morph_extend (snd_ivar f)
  =m= snd_ivar (morph_extend f).
Proof.
  intros V v; simplT; easy.
Qed.

Lemma pair_ivar_extend {N T M}
      (f : iname T M) (g : ilevel N T M) :
  morph_extend (pair_ivar f g)
  =m= pair_ivar (kmorph_extend f) (morph_extend g).
Proof.
  intros V v.
  destruct v; simplT; easy.
Qed.

Lemma open_ivar_extend {N T M} n (f : ivar N T M) :
  morph_extend (open_ivar n f)
  =m= open_ivar n (morph_extend f).
Proof.
  intros V v; unfold open_ivar.
  rewrite pair_ivar_extend, delete_iname_extend,
    cons_ilevel_extend, get_iname_extend,
    !fst_ivar_extend, !snd_ivar_extend.
  easy.
Qed.

Lemma close_ivar_extend {N T M} n (f : ivar (S N) T M) :
  morph_extend (close_ivar n f)
  =m= close_ivar n (morph_extend f).
Proof.
  intros V v; unfold close_ivar.
  rewrite pair_ivar_extend, insert_iname_extend,
    hd_ilevel_extend, tl_ilevel_extend,
    !fst_ivar_extend, !snd_ivar_extend.
  easy.
Qed.

Lemma weak_ivar_extend {N T M} (f : ivar (S N) T M) :
  morph_extend (weak_ivar f)
  =m= weak_ivar (morph_extend f).
Proof.
  intros V v; unfold weak_ivar.
  rewrite pair_ivar_extend, tl_ilevel_extend,
    !fst_ivar_extend, !snd_ivar_extend.
  easy.
Qed.

Lemma bind_ivar_extend {N T M} a (f : ivar N T M) :
  morph_extend (bind_ivar a f)
  =m= bind_ivar (pnset_extend a) (morph_extend f).
Proof.
  intros V v; unfold bind_ivar.
  rewrite pair_ivar_extend, cons_ilevel_extend,
    !fst_ivar_extend, !snd_ivar_extend.
  easy.
Qed.

Lemma swap_ivar_extend {N T M} l (f : ivar (S N) T M) :
  morph_extend (swap_ivar l f)
  =m= swap_ivar (level_extend l) (morph_extend f).
Proof.
  intros V v; unfold swap_ivar.
  rewrite pair_ivar_extend, swap_ilevel_extend,
    !fst_ivar_extend, !snd_ivar_extend.
  easy.
Qed.

(* There is a full contravariant functor from [var N] to [ivar N
   T O] by composition.

   Operations not involving bind are in the image of that
   functor. We call these operations "static". *)

Definition open_var {N} n : ivar (S N) var N :=
  open_ivar n 1.

Definition close_var {N} n : ivar N var (S N) :=
  close_ivar n 1.

Definition weak_var {N} : ivar N var (S N) := weak_ivar 1.

Definition swap_var {N} l : ivar (S N) var (S N) :=
  swap_ivar l 1.

Lemma open_ivar_as_composition {N T M} n (f : ivar N T M) :
  open_ivar n f =m= f @ open_var n.
Proof.
  rewrite <- morph_right_identity with (f := f) at 1.
  rewrite <- open_ivar_compose_distribute.
  easy.
Qed.

Lemma close_ivar_as_composition {N T M} n
      (f : ivar (S N) T M) :
  close_ivar n f =m= f @ close_var n.
Proof.
  rewrite <- morph_right_identity with (f := f) at 1.
  rewrite <- close_ivar_compose_distribute.
  easy.
Qed.

Lemma weak_ivar_as_composition {N T M} (f : ivar (S N) T M) :
  weak_ivar f =m= f @ weak_var.
Proof.
  rewrite <- morph_right_identity with (f := f) at 1.
  rewrite <- weak_ivar_compose_distribute.
  easy.
Qed.

Lemma swap_ivar_as_composition {N T M} l (f : ivar (S N) T M) :
  swap_ivar l f =m= f @ swap_var l.
Proof.
  rewrite <- morph_right_identity with (f := f) at 1.
  rewrite <- swap_ivar_compose_distribute.
  easy.
Qed.

(* Transposing operations

   As with [iiindex] and [iname] we wish to reason about transpositions
   and permutations of [ivar] operations. However, rather than the full
   group of permutations, we will restrict our attention to a subset of
   the permutations.

   We can split our operations into three groups:
   - The "pop" operations which decrease the number of bound variables:
     [open_ivar] and [bind_ivar].
   - The "push" operations which increase the number of bound variables:
     [close_ivar] and [weak_ivar].
   - The swap<l> operations: [swap_ivar].

   Any sequence of operations of type [ivar 0 T M -> ivar 0 T M] must
   have "well-balanced" push and pop operations. Treating pop operations
   as opening brackets, push operations as closing brackets and ignoring
   swap operations; the sequence must be a Dyck word.

   The standard partial order on Dyck words of a given length is
   defined as:

     u ≤ v iff v can be reached from u by a series of "proper"
     transpositions

   where "proper" transpositions are those that replace ")(" with "()".

   We can extend that idea to a preorder on our sequences of operations
   by allowing as "proper" transpositions the following cases:

     1. Transposing a push followed by a pop into a
        push, swap<0>, pop sequence.
     2. Transposing a pop, pop, swap<0> sequence into a pop and a pop.
     3. Transposing a swap<0>, push, push sequence into a push and a push.
     4. Transposing a pop and a swap<n+1> into a swap<n> and a pop,
        and vice-versa
     5. Transposing a push and swap<n> into a swap<n+1> and push,
        and vice-versa

   The maximal elements of this pre-order are sequences consisting of a
   sequence of pop operations followed by a sequence of push operations.

   We are primarily concerned with transforming sequences of operations
   into such maximal forms. So we will restrict our attention to the
   transformation semigroup of permutations generated by these proper
   transpositions.
  *)

Inductive pop_op T M : Type :=
| open : name -> pop_op T M
| bind : pnset T M -> pop_op T M.
Arguments open {T M} n.
Arguments bind {T M} a.

Definition apply_pop_op {N T M} (op : pop_op T M)
  : ivar N T M -> ivar (S N) T M :=
  match op with
  | open n => open_ivar n
  | bind a => bind_ivar a
  end.

Inductive push_op : Type :=
| close : name -> push_op
| weak : push_op.

Definition apply_push_op {N T M} (op : push_op)
  : ivar (S N) T M -> ivar N T M :=
  match op with
  | close n => close_ivar n
  | weak => weak_ivar
  end.

Definition irreducible_ivar_pop_push_ops {T M} (op1 : pop_op T M) op2 :=
  match op1, op2 with
  | open n1, close n2 => n1 <> n2
  | open n1, weak => True
  | bind a, close n2 => True
  | bind a, weak => True
  end.
Arguments irreducible_ivar_pop_push_ops {T M} !op1 !op2.

Definition transpose_ivar_pop_push_left {T M} (op1 : pop_op T M) op2 :=
  match op1, op2 with
  | open n1, close n2 => close (unshift_name n1 n2)
  | open n1, weak => weak
  | bind a, close n2 => close n2
  | bind a, weak => weak
  end.
Arguments transpose_ivar_pop_push_left {T M} !op1 !op2.

Definition transpose_ivar_pop_push_right {T M} op2 (op1 : pop_op T M) :=
  match op1, op2 with
  | open n1, close n2 => open (unshift_name n2 n1)
  | open n1, weak => open n1
  | bind a, close n2 => bind a
  | bind a, weak => bind a
  end.
Arguments transpose_ivar_pop_push_right {T M} !op2 !op1.

Lemma transpose_ivar_pop_push {N T M}
      (op1 : pop_op T M) op2 (f : ivar (S N) T M) :
  irreducible_ivar_pop_push_ops op1 op2 ->
  apply_pop_op op1
    (apply_push_op op2 f)
  =m=
    apply_push_op (transpose_ivar_pop_push_left op1 op2)
      (swap_ivar l0
        (apply_pop_op (transpose_ivar_pop_push_right op2 op1) f)).
Proof.
  destruct op1, op2; cbn; intro Hirr; try easy.
  - simpl_ivars.
    transpose_iname delete _ (insert _) _.
    transpose_get_iname _ (insert _) _.
    easy.
Qed.

Ltac transpose_ivar_pop_push op1 op2 :=
  let Hrw := fresh "Hrw" in
  epose (transpose_ivar_pop_push op1 op2) as Hrw;
  cbn in Hrw; rewrite Hrw; clear Hrw.

Definition transpose_ivar_pop_pop_left {T M} (op1 op2 : pop_op T M) :=
  match op1, op2 with
  | open n1, open n2 => open (unshift_name n1 n2)
  | open n1, bind a2 => bind a2
  | bind a1, open n2 => open n2
  | bind a1, bind a2 => bind a2
  end.
Arguments transpose_ivar_pop_pop_left {T M} !op1 !op2.

Definition transpose_ivar_pop_pop_right {T M} (op2 op1 : pop_op T M) :=
  match op1, op2 with
  | open n1, open n2 => open (shift_below_name n2 n1)
  | open n1, bind n2 => open n1
  | bind a1, open n2 => bind a1
  | bind a1, bind a2 => bind a1
  end.
Arguments transpose_ivar_pop_pop_right {T M} !op2 !op1.

Lemma transpose_ivar_pop_pop {N T M} op1 op2 (f : ivar N T M) :
  swap_ivar l0
    (apply_pop_op op1 (apply_pop_op op2 f))
  =m=
    apply_pop_op (transpose_ivar_pop_pop_left op1 op2)
      (apply_pop_op (transpose_ivar_pop_pop_right op2 op1) f).
Proof.
  destruct op1, op2; cbn; simpl_ivars; try easy.
  - transpose_iname delete _ delete _.
    transpose_get_iname _ delete _.
    transpose_get_iname _ delete _.
    transpose_iname_squared_right Del _ Del _.
    easy.
Qed.

Tactic Notation "transpose_ivar_pop_pop"
       open_constr(op1) open_constr(op2) :=
  let Hrw := fresh "Hrw" in
  epose (transpose_ivar_pop_pop op1 op2) as Hrw;
  cbn in Hrw; rewrite Hrw; clear Hrw.

Definition transpose_ivar_push_push_left op1 op2 :=
  match op1, op2 with
  | close n1, close n2 => close (shift_below_name n1 n2)
  | close n1, weak => weak
  | weak, close n2 => close n2
  | weak, weak => weak
  end.
Arguments transpose_ivar_push_push_left !op1 !op2.

Definition transpose_ivar_push_push_right op2 op1 :=
  match op1, op2 with
  | close n1, close n2 => close (unshift_name n2 n1)
  | close n1, weak => close n1
  | weak, close n2 => weak
  | weak, weak => weak
  end.
Arguments transpose_ivar_push_push_right !op2 !op1.

Lemma transpose_ivar_push_push {N T M} op1 op2 (f : ivar (S (S N)) T M) :
  apply_push_op op1
    (apply_push_op op2 (swap_ivar l0 f))
  =m=
    apply_push_op (transpose_ivar_push_push_left op1 op2)
      (apply_push_op (transpose_ivar_push_push_right op2 op1) f).
Proof.
  destruct op1, op2; cbn; try easy.
  - simpl_ivars.
    transpose_iname (insert _) _ (insert _) _.
    easy.
Qed.

Tactic Notation "transpose_ivar_push_push"
       open_constr(op1) open_constr(op2) :=
  let Hrw := fresh "Hrw" in
  epose (transpose_ivar_push_push op1 op2) as Hrw;
  cbn in Hrw; rewrite Hrw; clear Hrw.

Lemma transpose_ivar_swap_pop {N T M} op l (f : ivar (S N) T M) :
  swap_ivar (lS l) (apply_pop_op op f)
  =m= apply_pop_op op (swap_ivar l f).
Proof.
  destruct op; easy.
Qed.

Tactic Notation "transpose_ivar_swap_pop" open_constr(op) :=
  let Hrw := fresh "Hrw" in
  epose (transpose_ivar_swap_pop op) as Hrw;
  cbn in Hrw; rewrite Hrw; clear Hrw.

Lemma transpose_ivar_pop_swap {N T M} op l (f : ivar (S N) T M) :
  apply_pop_op op (swap_ivar l f)
  =m= swap_ivar (lS l) (apply_pop_op op f).
Proof.
  destruct op; easy.
Qed.

Tactic Notation "transpose_ivar_pop_swap" open_constr(op) :=
  let Hrw := fresh "Hrw" in
  epose (transpose_ivar_pop_swap op) as Hrw;
  cbn in Hrw; rewrite Hrw; clear Hrw.

Lemma transpose_ivar_swap_push {N T M} op l (f : ivar (S (S N)) T M) :
  swap_ivar l (apply_push_op op f)
  =m= apply_push_op op (swap_ivar (lS l) f).
Proof.
  destruct op; easy.
Qed.

Tactic Notation "transpose_ivar_swap_push" open_constr(op) :=
  let Hrw := fresh "Hrw" in
  epose (transpose_ivar_swap_push op) as Hrw;
  cbn in Hrw; rewrite Hrw; clear Hrw.

Lemma transpose_ivar_push_swap {N T M} op l (f : ivar (S (S N)) T M) :
  apply_push_op op (swap_ivar (lS l) f)
  =m= swap_ivar l (apply_push_op op f).
Proof.
  destruct op; easy.
Qed.

Tactic Notation "transpose_ivar_push_swap" open_constr(op) :=
  let Hrw := fresh "Hrw" in
  epose (transpose_ivar_push_swap op) as Hrw;
  cbn in Hrw; rewrite Hrw; clear Hrw.

(* Equivalences between core var operations and their definition
   in terms of the ivar primitives *)

Lemma shift_name_def n1 n2 :
  Var.shift_name n1 n2 = shift_below_name n1 n2.
Proof.
  unfold shift_name.
  case_string (n_string n1) (n_string n2); try easy.
  destruct (le_gt_dec (n_index n1) (n_index n2));
    red_iindexs; try easy.
  change n2 with (mkname (n_string n2) (n_index n2)); cbn.
  congruence.
Qed.

Lemma unshift_name_def n1 n2 :
  Var.unshift_name n1 n2 = unshift_name n1 n2.
Proof.
  unfold Var.unshift_name.
  case_string (n_string n1) (n_string n2); try easy.
  destruct (le_gt_dec (n_index n2) (n_index n1));
    red_iindexs; try easy.
  change n2 with (mkname (n_string n2) (n_index n2)); cbn.
  congruence.
Qed.

Lemma open_var_def n :
  @Var.open_var n =m= open_var n.
Proof.
  intros V v; destruct v as [n2|[|l]]; try easy; cbn.
  rewrite shift_name_def; simpl_ivars.
  case_string (n_string n) (n_string n2); try easy.
  case_order (n_index n) (n_index n2); easy.
Qed.

Lemma close_var_def n :
  @Var.close_var n =m= close_var n.
Proof.
  intros V v; destruct v as [n2|l]; try easy.
  unfold Var.close_var; rewrite unshift_name_def.
  destruct (name_dec n n2); subst;
    red_inames; red_iindexs; try easy.
  case_string (n_string n) (n_string n2); try easy.
  case_order (n_index n2) (n_index n); easy.
Qed.

Lemma weak_var_def :
  @Var.weak_var =m= weak_var.
Proof. easy. Qed.

Hint Rewrite shift_name_def unshift_name_def
     open_var_def close_var_def weak_var_def
  : var_ops_as_ivars.
