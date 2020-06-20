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

Lemma ivar_eta_pointwise {N T M} (f : ivar N T M) :
  pair_ivar (fst_ivar f) (snd_ivar f) =m= f.
Proof.
  intros V v; destruct v; easy.
Qed.

Definition ivar_eta {N T M} f :=
  eq_morph_expand (@ivar_eta_pointwise N T M f).

Hint Rewrite @ivar_beta_fst @ivar_beta_snd @ivar_eta
  : simpl_ivars.

Hint Rewrite @ivar_beta_fst @ivar_beta_snd @ivar_eta_pointwise
  : simpl_ivars_pointwise.

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
  autorewrite with fold_inames fold_ilevels fold_ivars.

Ltac simpl_ivars_eqn :=
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
     try (rewrite_strat topdown (hints simpl_inames_eqn));
     try (rewrite_strat topdown (hints simpl_iindexs));
     try (rewrite_strat topdown (hints simpl_iindexs_eqn)));
  autorewrite with fold_inames fold_ilevels fold_ivars.

Ltac simpl_ivars_pointwise :=
  autorewrite with unfold_ivars;
  autorewrite with simpl_ivars_pointwise;
  autorewrite with unfold_ilevels;
  autorewrite with simpl_ilevels_pointwise;
  autorewrite with unfold_inames;
  autorewrite with simpl_inames_pointwise;
  autorewrite with simpl_iindexs_pointwise;
  repeat progress
    (cbn;
     try (rewrite_strat topdown (hints simpl_ivars_pointwise));
     try (rewrite_strat topdown (hints simpl_ilevels_pointwise));
     try (rewrite_strat topdown (hints simpl_inames_pointwise));
     try (rewrite_strat topdown (hints simpl_iindexs_pointwise)));
  autorewrite with fold_inames fold_ilevels fold_ivars.

Ltac simpl_ivars_pointwise_eqn :=
  autorewrite with unfold_ivars;
  autorewrite with simpl_ivars_pointwise;
  autorewrite with unfold_ilevels;
  autorewrite with simpl_ilevels_pointwise;
  autorewrite with unfold_inames;
  autorewrite with simpl_inames_pointwise;
  autorewrite with simpl_iindexs_pointwise;
  repeat progress
    (cbn;
     try (rewrite_strat topdown (hints simpl_ivars_pointwise));
     try (rewrite_strat topdown (hints simpl_ilevels_pointwise));
     try (rewrite_strat topdown (hints simpl_inames_pointwise));
     try (rewrite_strat topdown (hints simpl_inames_pointwise_eqn));
     try (rewrite_strat topdown (hints simpl_iindexs_pointwise));
     try (rewrite_strat topdown (hints simpl_iindexs_pointwise_eqn)));
  autorewrite with fold_inames fold_ilevels fold_ivars.

(* Transposing operations

   Unlike [iindex] and [iname] we don't provide general
   support for permutations, just a few simple
   transpositions.
*)

Lemma transpose_open_ivar_open_ivar_pointwise {N T M} n m
      (f : ivar N T M) :
  open_ivar n (open_ivar m f)
  =m= swap_ivar
        (open_ivar (unshift_name n m)
          (open_ivar (shift_below_name m n) f)).
Proof.
  intros; simpl_ivars_pointwise.
  transpose_iname Del _ Del _.
  transpose_get_iname _ Del _.
  transpose_get_iname _ Del _.
  transpose_iname_squared_right delete _ delete _.
  easy.
Qed.

Definition transpose_open_ivar_open_ivar {N T M} n m f :=
  eq_morph_expand
    (@transpose_open_ivar_open_ivar_pointwise N T M n m f).

Lemma transpose_open_ivar_close_ivar_pointwise {N T M} n m
      (f : ivar (S N) T M) :
  n <> m ->
  open_ivar n (close_ivar m f)
  =m= close_ivar (unshift_name n m)
        (swap_ivar
          (open_ivar (unshift_name m n) f)).
 Proof.
   intros; simpl_ivars_pointwise.
   transpose_iname Del _ (Ins _) _.
   transpose_get_iname _ (Ins _) _.
   easy.
 Qed.

Definition transpose_open_ivar_close_ivar {N T M} n m f :=
  fun V l Hneq =>
    eq_morph_expand
      (@transpose_open_ivar_close_ivar_pointwise
         N T M n m f Hneq)
      V l.

Lemma transpose_open_ivar_weak_ivar_pointwise {N T M} n
      (f : ivar (S N) T M) :
  open_ivar n (weak_ivar f)
  =m= weak_ivar (swap_ivar (open_ivar n f)).
Proof. easy. Qed.

Definition transpose_open_ivar_weak_ivar {N T M} n f :=
  eq_morph_expand
    (@transpose_open_ivar_weak_ivar_pointwise N T M n f).

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

Definition open_var {N} a : ivar (S N) var N :=
  open_ivar a 1.

Definition close_var {N} a : ivar N var (S N) :=
  close_ivar a 1.

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

Section Term.

  Context {trm : nset}.

  Variable unit : forall {N}, ivar N (@trm) N.

  Definition open_ktrm {N} a := open_ivar a (@unit N).
  Definition close_ktrm {N} a := close_ivar a (@unit (S N)).
  Definition weak_ktrm {N} := weak_ivar (@unit (S N)).
  Definition bind_ktrm {N} t := bind_ivar t (@unit N).
  Definition swap_ktrm {N} := swap_ivar (@unit (S (S N))).

  Variable kleisli :
    forall {N M},
      ivar N (@trm) M ->
      morph (@trm) N (@trm) M.

  Definition open_trm {N} a := kleisli (@open_ktrm N a).
  Definition close_trm {N} a := kleisli (@close_ktrm N a).
  Definition weak_trm {N} := kleisli (@weak_ktrm N).
  Definition bind_trm {N} t := kleisli (@bind_ktrm N t).
  Definition swap_trm {N} := kleisli (@swap_ktrm N).

  Axiom extensional :
    forall N M (f g : morph (@var) N (@trm) M),
      f =m= g ->
      kleisli f =m= kleisli g.

  Add Parametric Morphism {N M} : (@kleisli N M)
    with signature eq_morph ==> eq_morph
    as kleisli_mor.
    intros * Heq V n; unfold fst_ivar.
    apply extensional; easy.
  Qed.

  Axiom left_identity :
    forall N M (f : morph (@var) N (@trm) M),
      kleisli f @ unit =m= f.

  Axiom right_identity :
    forall N, kleisli (@unit N) =m= 1.

  Axiom associativity :
    forall N M L
      (f : morph (@var) N (@trm) M)
      (g : morph (@var) M (@trm) L),
      (kleisli g) @ (kleisli f)
      =m= kleisli (kleisli g @ f).

  Hint Rewrite left_identity right_identity associativity
       @pair_ivar_compose_distribute @fst_ivar_compose_distribute
       @snd_ivar_compose_distribute @open_ivar_compose_distribute
       @close_ivar_compose_distribute @weak_ivar_compose_distribute
       @bind_ivar_compose_distribute @swap_ivar_compose_distribute
    : simpl_trm.

  Lemma foo N a :
    @close_trm N a @ (open_trm a)
    =m= morph_id.
  Proof.
    unfold open_trm, close_trm, open_ktrm, close_ktrm.
    autorewrite with simpl_trm.
    intros V t.
    replace (kleisli (open_ivar a (close_ivar a unit)) V t)
      with (kleisli unit V t).
    - autorewrite with simpl_trm.
      easy.
    - apply extensional.
      intros V' t'.
      time simpl_ivars.
    easy.
  Qed.

End Term.
