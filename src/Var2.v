Require Import String Omega Setoid Morphisms.
Require Import Morph Index Name Level.

(* Variables are either free names or bound levels *)

Inductive var (V : nat) :=
| free (n : name)
| bound (l : level V).

Arguments free {V} n.
Arguments bound {V} l.

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

Definition swap_ivar {N T M} (f : ivar (S (S N)) T M)
  : ivar (S (S N)) T M :=
  pair_ivar (fst_ivar f) (swap_ilevel (snd_ivar f)).

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

Add Parametric Morphism {N T M} : (@swap_ivar N T M)
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

Lemma unfold_swap_ivar {N T M} (f : ivar (S (S N)) T M) :
  swap_ivar f
  = pair_ivar (fst_ivar f) (swap_ilevel (snd_ivar f)).
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

Lemma fold_swap_ivar {N T M} (f : ivar (S (S N)) T M) :
  pair_ivar (fst_ivar f) (swap_ilevel (snd_ivar f))
  = swap_ivar f.
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

Lemma swap_ivar_compose_distribute {N T M R L}
      (f : ivar (S (S N)) T M) (g : morph T M R L) :
  g @ swap_ivar f
  =m= swap_ivar (g @ f).
Proof.
  unfold swap_ivar.
  rewrite pair_ivar_compose_distribute.
  rewrite fst_ivar_compose_distribute.
  rewrite swap_ilevel_compose_distribute.
  rewrite snd_ivar_compose_distribute.
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

Definition swap_var {N} : ivar (S (S N)) var (S (S N)) :=
  swap_ivar 1.

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

Lemma swap_ivar_as_composition {N T M} (f : ivar (S (S N)) T M) :
  swap_ivar f =m= f @ swap_var.
Proof.
  rewrite <- morph_right_identity with (f := f) at 1.
  rewrite <- swap_ivar_compose_distribute.
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

Lemma swap_ivar_extend {N T M} (f : ivar (S (S N)) T M) :
  morph_extend (swap_ivar f)
  =m= swap_ivar (morph_extend f).
Proof.
  intros V v; unfold swap_ivar.
  rewrite pair_ivar_extend, swap_ilevel_extend,
    !fst_ivar_extend, !snd_ivar_extend.
  easy.
Qed.

Section Term.

  Context {trm : nset}.

  Variable unit : forall {N}, ivar N (@trm) N.

  Variable kleisli :
    forall {N M},
      ivar N (@trm) M ->
      morph (@trm) N (@trm) M.

  Definition open_ktrm n := open_ivar n (@unit 0).
  Definition open_trm n := kleisli (open_ktrm n).

  Definition close_ktrm n := close_ivar n (@unit 1).
  Definition close_trm n := kleisli (close_ktrm n).

  Definition weak_ktrm := weak_ivar (@unit 1).
  Definition weak_trm := kleisli weak_ktrm.

  Fixpoint weaken_trm (t : @trm 0) V : @trm (0 + V) :=
    match V with
    | 0 => t
    | S V => weak_trm V (weaken_trm t V)
    end.

  Definition bind_ktrm t := bind_ivar (weaken_trm t) (@unit 0).
  Definition bind_trm t := kleisli (bind_ktrm t).

  Definition swap_ktrm := swap_ivar (@unit 2).
  Definition swap_trm := kleisli swap_ktrm.

  Hypothesis extensional :
    forall N M (f g : morph (@var) N (@trm) M),
      f =m= g ->
      kleisli f =m= kleisli g.

  Add Parametric Morphism {N M} : (@kleisli N M)
    with signature eq_morph ==> eq_morph
    as kleisli_mor.
    intros * Heq V n; unfold fst_ivar.
    apply extensional; easy.
  Qed.

  Hypothesis left_identity :
    forall N M (f : morph (@var) N (@trm) M),
      kleisli f @ unit =m= f.

  Hypothesis right_identity :
    forall N, kleisli (@unit N) =m= 1.

  Hypothesis associativity :
    forall N M L
      (f : morph (@var) N (@trm) M)
      (g : morph (@var) M (@trm) L),
      (kleisli g) @ (kleisli f)
      =m= kleisli (kleisli g @ f).

  Hypothesis unit_extend :
    forall N,
      morph_extend (@unit N) =m= unit.

  Hypothesis kleisli_extend :
    forall N M (f : morph (@var) N (@trm) M),
      morph_extend (kleisli f)
      =m= kleisli (morph_extend f).

  Hint Rewrite @left_identity @right_identity @associativity
       @unit_extend @kleisli_extend
       @morph_apply_compose @morph_apply_id
       @pair_ivar_compose_distribute @fst_ivar_compose_distribute
       @snd_ivar_compose_distribute @open_ivar_compose_distribute
       @close_ivar_compose_distribute @weak_ivar_compose_distribute
       @bind_ivar_compose_distribute @swap_ivar_compose_distribute
       @pair_ivar_extend @fst_ivar_extend
       @snd_ivar_extend @open_ivar_extend
       @close_ivar_extend @weak_ivar_extend
       @bind_ivar_extend @swap_ivar_extend
    : simpl_trms.

  (* Unfolding operations *)

  Lemma unfold_open_ktrm n :
    open_ktrm n = open_ivar n (@unit 0).
  Proof. easy. Qed.

  Lemma unfold_close_ktrm n :
    close_ktrm n = close_ivar n (@unit 1).
  Proof. easy. Qed.

  Lemma unfold_weak_ktrm :
    weak_ktrm = weak_ivar (@unit 1).
  Proof. easy. Qed.

  Lemma unfold_bind_ktrm t :
    bind_ktrm t = bind_ivar (weaken_trm t) (@unit 0).
  Proof. easy. Qed.

  Lemma unfold_swap_ktrm :
    swap_ktrm = swap_ivar (@unit 2).
  Proof. easy. Qed.

  Lemma unfold_open_trm n :
    open_trm n = kleisli (open_ktrm n).
  Proof. easy. Qed.

  Lemma unfold_close_trm n :
    close_trm n = kleisli (close_ktrm n).
  Proof. easy. Qed.

  Lemma unfold_weak_trm :
    weak_trm = kleisli weak_ktrm.
  Proof. easy. Qed.

  Lemma unfold_bind_trm t :
    bind_trm t = kleisli (bind_ktrm t).
  Proof. easy. Qed.

  Lemma unfold_swap_trm :
    swap_trm = kleisli swap_ktrm.
  Proof. easy. Qed.

  Hint Rewrite @unfold_open_ktrm @unfold_close_ktrm
       @unfold_weak_ktrm @unfold_bind_ktrm @unfold_swap_ktrm
       @unfold_open_trm @unfold_close_trm
       @unfold_weak_trm @unfold_bind_trm @unfold_swap_trm
    : unfold_trms.

  (* Folding operations *)

  Lemma fold_open_ktrm n :
    open_ivar n (@unit 0) = open_ktrm n.
  Proof. easy. Qed.

  Lemma fold_close_ktrm n :
    close_ivar n (@unit 1) = close_ktrm n.
  Proof. easy. Qed.

  Lemma fold_weak_ktrm :
    weak_ivar (@unit 1) = weak_ktrm.
  Proof. easy. Qed.

  Lemma fold_bind_ktrm t :
    bind_ivar (weaken_trm t) (@unit 0) = bind_ktrm t.
  Proof. easy. Qed.

  Lemma fold_swap_ktrm :
    swap_ivar (@unit 2) = swap_ktrm.
  Proof. easy. Qed.

  Lemma fold_open_trm n :
    kleisli (open_ktrm n) = open_trm n.
  Proof. easy. Qed.

  Lemma fold_close_trm n :
    kleisli (close_ktrm n) = close_trm n.
  Proof. easy. Qed.

  Lemma fold_weak_trm :
    kleisli weak_ktrm = weak_trm.
  Proof. easy. Qed.

  Lemma fold_bind_trm t :
    kleisli (bind_ktrm t) = bind_trm t.
  Proof. easy. Qed.

  Lemma fold_swap_trm :
    kleisli swap_ktrm = swap_trm.
  Proof. easy. Qed.

  Hint Rewrite @fold_open_ktrm @fold_close_ktrm
       @fold_weak_ktrm @fold_bind_ktrm @fold_swap_ktrm
       @fold_open_trm @fold_close_trm
       @fold_weak_trm @fold_bind_trm @fold_swap_trm
    : fold_trms.

  Ltac simpl_trms :=
    autorewrite with unfold_trms;
    autorewrite with simpl_trms;
    simpl_ivars;
    repeat progress
      (cbn;
       try (rewrite_strat topdown (hints simpl_trms));
       simpl_ivars);
    autorewrite with fold_trms.

  (* Transposing operations *)

  Lemma transpose_close_trm_open_trm n1 n2 :
    n1 <> n2 ->
    (close_trm n1) @ (open_trm n2)
    =m=
    morph_extend (open_trm (unshift_name n1 n2))
      @ swap_trm
      @ morph_extend (close_trm (unshift_name n2 n1)).
  Proof.
    intro Hirr; simpl_trms.
    transpose_iname delete _ (insert _) _; try congruence.
    transpose_get_iname _ (insert _) _; congruence.
  Qed.

  (* Pop operations *)

  Inductive pop_op N : Type :=
  | open : name -> pop_op N
  | bind : pnset trm N -> pop_op N.
  Arguments open {N} n.
  Arguments bind {N} a.

  Definition eq_pop_op {N} (op1 op2 : pop_op N) :=
    match op1, op2 with
    | open n1, open n2 => n1 = n2
    | open _, bind _ => False
    | bind p1, bind p2 => p1 =p= p2
    | bind _, open _ => False
    end.

  Notation "op1 =pop= op2" :=
    (eq_pop_op op1 op2) (at level 70).

  Definition apply_pop_op {N} (op : pop_op N)
    : morph trm (S N) trm N :=
    match op with
    | open n => open_trm n
    | bind a => bind_trm a
    end.

  Definition transpose_trm_pop_pop_left
             {N} (op1 : pop_op N) op2 :=
    match op1, op2 with
    | open n1, open n2 => open (shift_below_name n1 n2)
    | open n1, bind a2 => bind (morph_apply (open_trm n1) a2)
    | bind a1, open n2 => open n2
    | bind a1, bind a2 => bind (morph_apply (bind_trm a1) a2)
    end.
  Arguments transpose_trm_pop_pop_left {N} !op1 !op2.

  Definition transpose_trm_pop_pop_right
             {N} (op2 : pop_op (S N)) (op1 : pop_op N) :=
    match op1, op2 with
    | open n1, open n2 => open (unshift_name n2 n1)
    | open n1, bind n2 => open n1
    | bind a1, open n2 => bind (morph_apply (close_trm n2) a1)
    | bind a1, bind a2 => bind (morph_apply weak_trm a1)
    end.
  Arguments transpose_trm_pop_pop_right {N} !op2 !op1.

  Lemma transpose_trm_pop_pop {N} op1 op2 :
    (@apply_pop_op N op1)
      @ (apply_pop_op op2)
    =m=
    (apply_pop_op (transpose_trm_pop_pop_left op1 op2))
      @ (apply_pop_op (transpose_trm_pop_pop_right op2 op1))
      @ swap_trm.
  Proof.
    destruct op1, op2; cbn; simpl_trm; try easy.
    - transpose_iname delete _ delete _.
      transpose_get_iname _ delete _.
      transpose_get_iname _ delete _.
      transpose_iname_squared_right Del _ Del _.
      easy.
  Qed.

  Ltac transpose_trm_pop_pop op1 op2 :=
    let Hrw := fresh "Hrw" in
    epose (transpose_trm_pop_pop op1 op2) as Hrw;
    cbn in Hrw; rewrite Hrw; clear Hrw.

  Lemma transpose_trm_pop_pop_squared_left {N}
        (op1 : pop_op N) op2 :
    transpose_trm_pop_pop_left
      (transpose_trm_pop_pop_left op1 op2)
      (transpose_trm_pop_pop_right op2 op1)
    =pop= op1.
  Proof.
    intros.
    destruct op1, op2; cbn; simpl_trm; try easy.
    - transpose_iname_squared_left Ins _ Ins _.
      easy.
  Qed.

  Lemma transpose_trm_pop_pop_squared_right {N}
        (op1 : pop_op N) op2 :
    transpose_trm_pop_pop_right
      (transpose_trm_pop_pop_right op2 op1)
      (transpose_trm_pop_pop_left op1 op2)
    =pop= op2.
  Proof.
    intros.
    destruct op1, op2; cbn; simpl_trm; try easy.
    - transpose_iname_squared_right Ins _ Ins _.
      easy.
    - 
  Qed.

  (* Push operations *)
  Inductive push_op : Type :=
  | close : name -> push_op
  | weak : push_op.

  Definition apply_push_op {N} (op : push_op)
    : morph trm N trm (S N) :=
    match op with
    | close n => close_trm n
    | weak => weak_trm
    end.

  Definition transpose_trm_push_push_left op1 op2 :=
    match op1, op2 with
    | close n1, close n2 => close (unshift_name n1 n2)
    | close n1, weak => weak
    | weak, close n2 => close n2
    | weak, weak => weak
    end.
  Arguments transpose_trm_push_push_left !op1 !op2.

  Definition transpose_trm_push_push_right op2 op1 :=
    match op1, op2 with
    | close n1, close n2 => close (shift_below_name n2 n1)
    | close n1, weak => close n1
    | weak, close n2 => weak
    | weak, weak => weak
    end.
  Arguments transpose_trm_push_push_right !op2 !op1.

  Lemma transpose_trm_push_push {N} op1 op2 :
    (apply_push_op op1)
      @ (@apply_push_op N op2)
    =m=
    swap_trm
    @ (apply_push_op (transpose_trm_push_push_left op1 op2))
      @ (apply_push_op (transpose_trm_push_push_right op2 op1)).
  Proof.
    destruct op1, op2; cbn; simpl_trm; try easy.
    - transpose_iname (insert _) _ (insert _) _.
      easy.
  Qed.

  Ltac transpose_trm_push_push op1 op2 :=
    let Hrw := fresh "Hrw" in
    epose (transpose_trm_push_push op1 op2) as Hrw;
    cbn in Hrw; rewrite Hrw; clear Hrw.

End Term.
