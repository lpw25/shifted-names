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
    (insert_iname n (hd_ilevel (snd_ivar f)) (fst_ivar f))
    (tl_ilevel (snd_ivar f)).

Definition weak_ivar {N T M} (f : ivar (S N) T M) : ivar N T M :=
  pair_ivar (fst_ivar f) (tl_ilevel (snd_ivar f)).

Definition bind_ivar {N T M} (a : pnset T M) (f : ivar N T M)
  : ivar (S N) T M :=
  pair_ivar (fst_ivar f) (cons_ilevel a (snd_ivar f)).

Definition transpose_ivar {N T M} (f : ivar (S (S N)) T M)
  : ivar (S (S N)) T M :=
  pair_ivar (fst_ivar f) (transpose_ilevel (snd_ivar f)).

Definition rename_ivar {N T M} n m (f : ivar N T M) : ivar N T M :=
  close_ivar n (open_ivar m f).

Definition shift_ivar {N T M} n (f : ivar N T M) : ivar N T M :=
  weak_ivar (open_ivar n f).

Definition subst_ivar {N T M} n a (f : ivar N T M) : ivar N T M :=
  close_ivar n (bind_ivar a f).

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

Add Parametric Morphism {N T M} : (@transpose_ivar N T M)
    with signature eq_morph ==> eq_morph
    as transpose_ivar_mor.
  intros * Heq V v; unfold transpose_ivar.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {N T M} : (@rename_ivar N T M)
    with signature eq ==> eq ==> eq_morph ==> eq_morph
    as rename_ivar_mor.
  intros * Heq V v; unfold rename_ivar.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {N T M} : (@shift_ivar N T M)
    with signature eq ==> eq_morph ==> eq_morph
    as shift_ivar_mor.
  intros * Heq V v; unfold shift_ivar.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {N T M} : (@subst_ivar N T M)
    with signature eq ==> eq_pnset ==> eq_morph ==> eq_morph
    as subst_ivar_mor.
  intros * Heq1 * Heq2 V v; unfold subst_ivar.
  rewrite Heq1, Heq2; easy.
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
      (insert_iname n (hd_ilevel (snd_ivar f)) (fst_ivar f))
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

Lemma unfold_transpose_ivar {N T M} (f : ivar (S (S N)) T M) :
  transpose_ivar f
  = pair_ivar (fst_ivar f) (transpose_ilevel (snd_ivar f)).
Proof. easy. Qed.

Lemma unfold_rename_ivar {N T M} n m (f : ivar N T M) :
  rename_ivar n m f
  = close_ivar n (open_ivar m f).
Proof. easy. Qed.

Lemma unfold_shift_ivar {N T M} n (f : ivar N T M) :
  shift_ivar n f
  = weak_ivar (open_ivar n f).
Proof. easy. Qed.

Lemma unfold_subst_ivar {N T M} n a (f : ivar N T M) :
  subst_ivar n a f
  = close_ivar n (bind_ivar a f).
Proof. easy. Qed.

Hint Rewrite @unfold_open_ivar @unfold_close_ivar
     @unfold_weak_ivar @unfold_bind_ivar @unfold_transpose_ivar
     @unfold_rename_ivar @unfold_shift_ivar @unfold_subst_ivar
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
    (insert_iname n (hd_ilevel (snd_ivar f)) (fst_ivar f))
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

Lemma fold_transpose_ivar {N T M} (f : ivar (S (S N)) T M) :
  pair_ivar (fst_ivar f) (transpose_ilevel (snd_ivar f))
  = transpose_ivar f.
Proof. easy. Qed.

Lemma fold_rename_ivar {N T M} n m (f : ivar N T M) :
  close_ivar n (open_ivar m f)
  = rename_ivar n m f.
Proof. easy. Qed.

Lemma fold_shift_ivar {N T M} n (f : ivar N T M) :
  weak_ivar (open_ivar n f)
  = shift_ivar n f.
Proof. easy. Qed.

Lemma fold_subst_ivar {N T M} n a (f : ivar N T M) :
  close_ivar n (bind_ivar a f)
  = subst_ivar n a f.
Proof. easy. Qed.

Hint Rewrite @fold_open_ivar @fold_close_ivar
     @fold_weak_ivar @fold_bind_ivar @fold_transpose_ivar
     @fold_rename_ivar @fold_shift_ivar @fold_subst_ivar
  : fold_ivars.

(* Simplify [ivars] terms by unfolding, simplifying and folding *)
Ltac simpl_ivars :=
  autorewrite with unfold_ivars;
  autorewrite with simpl_ivars;
  autorewrite with unfold_ilevels;
  autorewrite with simpl_ilevels;
  autorewrite with unfold_inames;
  autorewrite with simpl_names simpl_inames;
  autorewrite with unfold_iindexs;
  autorewrite with simpl_indexs simpl_iindexs;
  repeat progress
    (cbn;
     try (rewrite_strat topdown (hints simpl_ivars));
     try (rewrite_strat topdown (hints simpl_ilevels));
     try (rewrite_strat topdown (hints simpl_names));
     try (rewrite_strat topdown (hints simpl_inames));
     try (rewrite_strat topdown (hints simpl_indexs));
     try (rewrite_strat topdown (hints simpl_iindexs)));
  autorewrite with fold_iindexs fold_inames fold_ivars.

Ltac simpl_ivars_eqn :=
  autorewrite with unfold_ivars;
  autorewrite with simpl_ivars;
  autorewrite with unfold_ilevels;
  autorewrite with simpl_ilevels;
  autorewrite with unfold_inames;
  autorewrite with simpl_names simpl_inames;
  autorewrite with unfold_iindexs;
  autorewrite with simpl_indexs simpl_iindexs;
  repeat progress
    (cbn;
     try (rewrite_strat topdown (hints simpl_ivars));
     try (rewrite_strat topdown (hints simpl_ilevels));
     try (rewrite_strat topdown (hints simpl_names));
     try (rewrite_strat topdown (hints simpl_inames));
     try (rewrite_strat topdown (hints simpl_inames_eqn));
     try (rewrite_strat topdown (hints simpl_indexs));
     try (rewrite_strat topdown (hints simpl_iindexs));
     try (rewrite_strat topdown (hints simpl_iindexs_eqn)));
  autorewrite with fold_iindexs fold_inames fold_ivars.

Ltac simpl_ivars_pointwise :=
  autorewrite with unfold_ivars;
  autorewrite with simpl_ivars_pointwise;
  autorewrite with unfold_ilevels;
  autorewrite with simpl_ilevels_pointwise;
  autorewrite with unfold_inames;
  autorewrite with simpl_names simpl_inames_pointwise;
  autorewrite with unfold_iindexs;
  autorewrite with simpl_indexs simpl_iindexs_pointwise;
  repeat progress
    (cbn;
     try (rewrite_strat topdown (hints simpl_ivars_pointwise));
     try (rewrite_strat topdown (hints simpl_ilevels_pointwise));
     try (rewrite_strat topdown (hints simpl_names));
     try (rewrite_strat topdown (hints simpl_inames_pointwise));
     try (rewrite_strat topdown (hints simpl_indexs));
     try (rewrite_strat topdown (hints simpl_iindexs_pointwise)));
  autorewrite with fold_iindexs fold_inames fold_ivars.

Ltac simpl_ivars_pointwise_eqn :=
  autorewrite with unfold_ivars;
  autorewrite with simpl_ivars_pointwise;
  autorewrite with unfold_ilevels;
  autorewrite with simpl_ilevels_pointwise;
  autorewrite with unfold_inames;
  autorewrite with simpl_names simpl_inames_pointwise;
  autorewrite with unfold_iindexs;
  autorewrite with simpl_indexs simpl_iindexs_pointwise;
  repeat progress
    (cbn;
     try (rewrite_strat topdown (hints simpl_ivars_pointwise));
     try (rewrite_strat topdown (hints simpl_ilevels_pointwise));
     try (rewrite_strat topdown (hints simpl_names));
     try (rewrite_strat topdown (hints simpl_inames_pointwise));
     try (rewrite_strat topdown (hints simpl_inames_pointwise_eqn));
     try (rewrite_strat topdown (hints simpl_indexs));
     try (rewrite_strat topdown (hints simpl_iindexs_pointwise));
     try (rewrite_strat topdown (hints simpl_iindexs_pointwise_eqn)));
  autorewrite with fold_iindexs fold_inames fold_ivars.

(* Commute operations *)

Lemma swap_open_ivar_open_ivar_pointwise {N T M} n m
      (f : ivar N T M) :
  open_ivar n (open_ivar m f)
  =m= transpose_ivar
        (open_ivar (unshift_name n m)
          (open_ivar (shift_name m n) f)).
Proof.
  intros; simpl_ivars_pointwise.
  rewrite swap_delete_iname_delete_iname_pointwise.
  rewrite swap_get_iname_delete_iname_pointwise.
  rewrite swap_get_iname_delete_iname_pointwise.
  simpl_names; easy.
Qed.

Definition swap_open_ivar_open_ivar {N T M} n m f :=
  eq_morph_expand
    (@swap_open_ivar_open_ivar_pointwise N T M n m f).

Lemma swap_open_ivar_close_ivar_pointwise {N T M} n m
      (f : ivar (S N) T M) :
  n <> m ->
  open_ivar n (close_ivar m f)
  =m= close_ivar (unshift_name n m)
        (transpose_ivar
          (open_ivar (unshift_name m n) f)).
Proof.
  intros; simpl_ivars_pointwise.
  rewrite swap_delete_iname_insert_iname_pointwise by easy.
  rewrite swap_get_iname_insert_iname_pointwise by easy.
  easy.
Qed.

Definition swap_open_ivar_close_ivar {N T M} n m f :=
  fun V l Hneq =>
    eq_morph_expand
      (@swap_open_ivar_close_ivar_pointwise N T M n m f Hneq)
      V l.

Lemma swap_open_ivar_weak_ivar_pointwise {N T M} n
      (f : ivar (S N) T M) :
  open_ivar n (weak_ivar f)
  =m= weak_ivar (transpose_ivar (open_ivar n f)).
Proof. easy. Qed.

Definition swap_open_ivar_weak_ivar {N T M} n f :=
  eq_morph_expand
    (@swap_open_ivar_weak_ivar_pointwise N T M n f).

Lemma swap_open_ivar_bind_ivar_pointwise {N T M} n t
      (f : ivar N T M) :
  open_ivar n (bind_ivar t f)
  =m= transpose_ivar (bind_ivar t (open_ivar n f)).
Proof. easy. Qed.

Definition swap_open_ivar_bind_ivar {N T M} n t f :=
  eq_morph_expand
    (@swap_open_ivar_bind_ivar_pointwise N T M n t f).

Lemma swap_open_ivar_rename_ivar_pointwise {N T M} n m o
      (f : ivar N T M) :
  n <> m ->
  open_ivar n (rename_ivar m o f)
  =m= rename_ivar
         (unshift_name n m) (unshift_name (unshift_name m n) o)
         (open_ivar (shift_name o (unshift_name m n)) f).
Proof.
  intros; simpl_ivars_pointwise.
  rewrite swap_delete_iname_move_iname_pointwise by easy.
  rewrite swap_get_iname_move_iname_pointwise by easy.
  easy.
Qed.

Definition swap_open_ivar_rename_ivar {N T M} n m o f :=
  fun V l Hneq =>
    eq_morph_expand
      (@swap_open_ivar_rename_ivar_pointwise N T M n m o f Hneq)
      V l.

Lemma swap_open_ivar_shift_ivar_pointwise {N T M} n m
      (f : ivar N T M) :
  open_ivar n (shift_ivar m f)
  =m= shift_ivar (unshift_name n m)
        (open_ivar (shift_name m n) f).
Proof.
  simpl_ivars_pointwise.
  rewrite swap_delete_iname_delete_iname_pointwise.
  rewrite swap_get_iname_delete_iname_pointwise.
  easy.
Qed.

Definition swap_open_ivar_shift_ivar {N T M} n m f :=
  eq_morph_expand
    (@swap_open_ivar_shift_ivar_pointwise N T M n m f).

Lemma swap_open_ivar_subst_ivar_pointwise {N T M} n m t
      (f : ivar N T M) :
  n <> m ->
  open_ivar n (subst_ivar m t f)
  =m= subst_ivar (unshift_name n m) t
        (open_ivar (unshift_name m n) f).
Proof.
  intros; simpl_ivars_pointwise.
  rewrite swap_delete_iname_insert_iname_pointwise by easy.
  rewrite swap_get_iname_insert_iname_pointwise by easy.
  easy.
Qed.

Definition swap_open_ivar_subst_ivar {N T M} n m t f :=
  fun V l Hneq =>
    eq_morph_expand
      (@swap_open_ivar_rename_ivar_pointwise N T M n m t f Hneq)
      V l.

Lemma swap_close_ivar_close_ivar_pointwise {N T M} n m
      (f : ivar (S (S N)) T M) :
  close_ivar n (close_ivar m f)
  =m= close_ivar (shift_name n m)
        (close_ivar (unshift_name m n)
          (transpose_ivar f)).
Proof.
  simpl_ivars_pointwise.
  rewrite swap_insert_iname_insert_iname_pointwise.
  easy.
Qed.

Definition swap_close_ivar_close_ivar {N T M} n m f :=
  eq_morph_expand
    (@swap_close_ivar_close_ivar_pointwise N T M n m f).

Lemma swap_close_ivar_weak_ivar_pointwise {N T M} n
      (f : ivar (S (S N)) T M) :
  close_ivar n (weak_ivar f)
  =m= weak_ivar (close_ivar n (transpose_ivar f)).
Proof. easy. Qed.

Definition swap_close_ivar_weak_ivar {N T M} n f :=
  eq_morph_expand
    (@swap_close_ivar_weak_ivar_pointwise N T M n f).

Lemma swap_close_ivar_rename_ivar_pointwise {N T M} n m o
      (f : ivar (S N) T M) :
  close_ivar n (rename_ivar m o f)
  =m= rename_ivar
         (shift_name n m) (shift_above_name (unshift_name m n) o)
         (close_ivar (shift_name o (unshift_name m n)) f).
Proof.
  simpl_ivars_pointwise.
  rewrite swap_insert_iname_move_iname_pointwise.
  easy.
Qed.

Definition swap_close_ivar_rename_ivar {N T M} n m o f :=
  eq_morph_expand
    (@swap_close_ivar_rename_ivar_pointwise N T M n m o f).

Lemma swap_close_ivar_shift_ivar_pointwise {N T M} n m
      (f : ivar (S N) T M) :
  close_ivar n (shift_ivar m f)
  =m= shift_ivar (shift_above_name n m)
        (close_ivar (shift_name m n) f).
Proof.
  simpl_ivars_pointwise.
  rewrite swap_insert_iname_delete_iname_pointwise.
  easy.
Qed.

Definition swap_close_ivar_shift_ivar {N T M} n m f :=
  eq_morph_expand
    (@swap_close_ivar_shift_ivar_pointwise N T M n m f).

Lemma swap_close_ivar_subst_ivar_pointwise {N T M} n m t
      (f : ivar (S N) T M) :
  close_ivar n (subst_ivar m t f)
  =m= subst_ivar (shift_name n m) t
        (close_ivar (unshift_name m n) f).
Proof.
  simpl_ivars_pointwise.
  rewrite swap_insert_iname_insert_iname_pointwise.
  easy.
Qed.

Definition swap_close_ivar_subst_ivar {N T M} n m t f :=
  eq_morph_expand
    (@swap_close_ivar_subst_ivar_pointwise N T M n m t f).

Lemma swap_weak_ivar_close_ivar_pointwise {N T M} n
      (f : ivar (S (S N)) T M) :
  weak_ivar (close_ivar n f)
  =m= close_ivar n (weak_ivar (transpose_ivar f)).
Proof. easy. Qed.

Definition swap_weak_ivar_close_ivar {N T M} n f :=
  eq_morph_expand
    (@swap_weak_ivar_close_ivar_pointwise N T M n f).

Lemma swap_weak_ivar_weak_ivar_pointwise {N T M}
      (f : ivar (S (S N)) T M) :
  weak_ivar (weak_ivar f)
  =m= weak_ivar (weak_ivar (transpose_ivar f)).
Proof. easy. Qed.

Definition swap_weak_ivar_weak_ivar {N T M} f :=
  eq_morph_expand
    (@swap_weak_ivar_weak_ivar_pointwise N T M f).

Lemma swap_weak_ivar_rename_ivar_pointwise {N T M} n m
      (f : ivar (S N) T M) :
  weak_ivar (rename_ivar n m f)
  =m= rename_ivar n m (weak_ivar f).
Proof. easy. Qed.

Definition swap_weak_ivar_rename_ivar {N T M} n m f :=
  eq_morph_expand
    (@swap_weak_ivar_rename_ivar_pointwise N T M n m f).

Lemma swap_weak_ivar_shift_ivar_pointwise {N T M} n
      (f : ivar (S N) T M) :
  weak_ivar (shift_ivar n f)
  =m= shift_ivar n (weak_ivar f).
Proof. easy. Qed.

Definition swap_weak_ivar_shift_ivar {N T M} n f :=
  eq_morph_expand
    (@swap_weak_ivar_shift_ivar_pointwise N T M n f).

Lemma swap_weak_ivar_subst_ivar_pointwise {N T M} n t
      (f : ivar (S N) T M) :
  weak_ivar (subst_ivar n t f)
  =m= subst_ivar n t (weak_ivar f).
Proof. easy. Qed.

Definition swap_weak_ivar_subst_ivar {N T M} n t f :=
  eq_morph_expand
    (@swap_weak_ivar_subst_ivar_pointwise N T M n t f).

Lemma swap_bind_ivar_open_ivar_pointwise {N T M} t n
      (f : ivar N T M) :
  bind_ivar t (open_ivar n f)
  =m= transpose_ivar (open_ivar n (bind_ivar t f)).
Proof. easy. Qed.

Definition swap_bind_ivar_open_ivar {N T M} t n f :=
  eq_morph_expand
    (@swap_bind_ivar_open_ivar_pointwise N T M t n f).

Lemma swap_bind_ivar_close_ivar_pointwise {N T M} t n
      (f : ivar (S N) T M) :
  bind_ivar t (close_ivar n f)
  =m= close_ivar n (transpose_ivar (bind_ivar t f)).
Proof. easy. Qed.

Definition swap_bind_ivar_close_ivar {N T M} t n f :=
  eq_morph_expand
    (@swap_bind_ivar_close_ivar_pointwise N T M t n f).

Lemma swap_bind_ivar_weak_ivar_pointwise {N T M} t
      (f : ivar (S N) T M) :
  bind_ivar t (weak_ivar f)
  =m= weak_ivar (transpose_ivar (bind_ivar t f)).
Proof. easy. Qed.

Definition swap_bind_ivar_weak_ivar {N T M} t f :=
  eq_morph_expand
    (@swap_bind_ivar_weak_ivar_pointwise N T M t f).

Lemma swap_bind_ivar_bind_ivar_pointwise {N T M} t s
      (f : ivar N T M) :
  bind_ivar t (bind_ivar s f)
  =m= transpose_ivar (bind_ivar s (bind_ivar t f)).
Proof. easy. Qed.

Definition swap_bind_ivar_bind_ivar {N T M} t s f :=
  eq_morph_expand
    (@swap_bind_ivar_bind_ivar_pointwise N T M t s f).

Lemma swap_bind_ivar_rename_ivar_pointwise {N T M} t n m
      (f : ivar N T M) :
  bind_ivar t (rename_ivar n m f)
  =m= rename_ivar n m (bind_ivar t f).
Proof. easy. Qed.

Definition swap_bind_ivar_rename_ivar {N T M} t n m f :=
  eq_morph_expand
    (@swap_bind_ivar_rename_ivar_pointwise N T M t n m f).

Lemma swap_bind_ivar_shift_ivar_pointwise {N T M} t n
      (f : ivar N T M) :
  bind_ivar t (shift_ivar n f)
  =m= shift_ivar n (bind_ivar t f).
Proof. easy. Qed.

Definition swap_bind_ivar_shift_ivar {N T M} t n f :=
  eq_morph_expand
    (@swap_bind_ivar_shift_ivar_pointwise N T M t n f).

Lemma swap_bind_ivar_subst_ivar_pointwise {N T M} t n s
      (f : ivar N T M) :
  bind_ivar t (subst_ivar n s f)
  =m= subst_ivar n s (bind_ivar t f).
Proof. easy. Qed.

Definition swap_bind_ivar_subst_ivar {N T M} t n s f :=
  eq_morph_expand
    (@swap_bind_ivar_subst_ivar_pointwise N T M t n s f).

Lemma swap_rename_ivar_open_ivar_pointwise {N T M} n m o
      (f : ivar N T M) :
  rename_ivar n m (open_ivar o f)
  =m= open_ivar (shift_above_name n (unshift_name m o))
        (rename_ivar (shift_name (unshift_name m o) n)
                     (shift_name o m) f).
Proof.
  simpl_ivars_pointwise.
  rewrite swap_move_iname_delete_iname_pointwise.
  rewrite swap_get_iname_move_iname_pointwise
    by auto using shift_above_name_neq_shift_name.
  simpl_names; easy.
Qed.

Definition swap_rename_ivar_open_ivar {N T M} n m o f :=
  eq_morph_expand
    (@swap_rename_ivar_open_ivar_pointwise N T M n m o f).

Lemma swap_rename_ivar_close_ivar_pointwise {N T M} n m o
      (f : ivar (S N) T M) :
  m <> o ->
  rename_ivar n m (close_ivar o f)
  =m= close_ivar (shift_name n (unshift_name m o))
         (rename_ivar (unshift_name (unshift_name m o) n)
            (unshift_name o m) f).
Proof.
  intros; simpl_ivars_pointwise.
  rewrite swap_move_iname_insert_iname_pointwise by easy.
  easy.
Qed.

Definition swap_rename_ivar_close_ivar {N T M} n m o f :=
  fun V l Hneq =>
    eq_morph_expand
      (@swap_rename_ivar_close_ivar_pointwise N T M n m o f Hneq)
      V l.

Lemma swap_rename_ivar_weak_ivar_pointwise {N T M} n m
      (f : ivar (S N) T M) :
  rename_ivar n m (weak_ivar f)
  =m= weak_ivar (rename_ivar n m f).
Proof. easy. Qed.

Definition swap_rename_ivar_weak_ivar {N T M} n m f :=
  eq_morph_expand
    (@swap_rename_ivar_weak_ivar_pointwise N T M n m f).

Lemma swap_rename_ivar_bind_ivar_pointwise {N T M} n m t
      (f : ivar N T M) :
  rename_ivar n m (bind_ivar t f)
  =m= bind_ivar t (rename_ivar n m f).
Proof. easy. Qed.

Definition swap_rename_ivar_bind_ivar {N T M} n m t f :=
  eq_morph_expand
    (@swap_rename_ivar_bind_ivar_pointwise N T M n m t f).

Lemma swap_shift_ivar_open_ivar_pointwise {N T M} n m
      (f : ivar N T M) :
  shift_ivar n (open_ivar m f)
  =m= open_ivar (unshift_name n m)
         (shift_ivar (shift_name m n) f).
Proof.
  simpl_ivars_pointwise.
  rewrite swap_delete_iname_delete_iname_pointwise.
  rewrite swap_get_iname_delete_iname_pointwise.
  simpl_names.
  easy.
Qed.

Definition swap_shift_ivar_open_ivar {N T M} n m f :=
  eq_morph_expand
    (@swap_shift_ivar_open_ivar_pointwise N T M n m f).

Lemma swap_shift_ivar_close_ivar_pointwise {N T M} n m
      (f : ivar (S N) T M) :
  n <> m ->
  shift_ivar n (close_ivar m f)
  =m= close_ivar (unshift_name n m)
         (shift_ivar (unshift_name m n) f).
Proof.
  intros; simpl_ivars_pointwise.
  rewrite swap_delete_iname_insert_iname_pointwise by easy.
  easy.
Qed.

Definition swap_shift_ivar_close_ivar {N T M} n m f :=
  fun V l Hneq =>
    eq_morph_expand
      (@swap_shift_ivar_close_ivar_pointwise N T M n m f Hneq)
      V l.

Lemma swap_shift_ivar_weak_ivar_pointwise {N T M} n
      (f : ivar (S N) T M) :
  shift_ivar n (weak_ivar f)
  =m= weak_ivar (shift_ivar n f).
Proof. easy. Qed.

Definition swap_shift_ivar_weak_ivar {N T M} n f :=
  eq_morph_expand
    (@swap_shift_ivar_weak_ivar_pointwise N T M n f).

Lemma swap_shift_ivar_bind_ivar_pointwise {N T M} n t
      (f : ivar N T M) :
  shift_ivar n (bind_ivar t f)
  =m= bind_ivar t (shift_ivar n f).
Proof. easy. Qed.

Definition swap_shift_ivar_bind_ivar {N T M} n t f :=
  eq_morph_expand
    (@swap_shift_ivar_bind_ivar_pointwise N T M n t f).

Lemma swap_subst_ivar_open_ivar_pointwise {N T M} n t m
      (f : ivar N T M) :
  subst_ivar n t (open_ivar m f)
  =m= open_ivar (shift_above_name n m)
         (subst_ivar (shift_name m n) t f).
Proof.
  simpl_ivars_pointwise.
  rewrite swap_insert_iname_delete_iname_pointwise.
  rewrite swap_get_iname_insert_iname_pointwise
    by apply shift_above_name_neq_shift_name.
  simpl_names; easy.
Qed.

Definition swap_subst_ivar_open_ivar {N T M} n t m f :=
  eq_morph_expand
    (@swap_subst_ivar_open_ivar_pointwise N T M n t m f).

Lemma swap_subst_ivar_close_ivar_pointwise {N T M} n t m
      (f : ivar (S N) T M) :
  subst_ivar n t (close_ivar m f)
  =m= close_ivar (shift_name n m)
         (subst_ivar (unshift_name m n) t f).
Proof.
  simpl_ivars_pointwise.
  rewrite swap_insert_iname_insert_iname_pointwise.
  easy.
Qed.

Definition swap_subst_ivar_close_ivar {N T M} n t m f :=
    eq_morph_expand
      (@swap_subst_ivar_close_ivar_pointwise N T M n t m f).

Lemma swap_subst_ivar_weak_ivar_pointwise {N T M} n t
      (f : ivar (S N) T M) :
  subst_ivar n t (weak_ivar f)
  =m= weak_ivar (subst_ivar n t f).
Proof. easy. Qed.

Definition swap_subst_ivar_weak_ivar {N T M} n t f :=
  eq_morph_expand
    (@swap_subst_ivar_weak_ivar_pointwise N T M n t f).

Lemma swap_subst_ivar_bind_ivar_pointwise {N T M} n t s
      (f : ivar N T M) :
  subst_ivar n t (bind_ivar s f)
  =m= bind_ivar s (subst_ivar n t f).
Proof. easy. Qed.

Definition swap_subst_ivar_bind_ivar {N T M} n t s f :=
  eq_morph_expand
    (@swap_subst_ivar_bind_ivar_pointwise N T M n t s f).

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

Lemma rename_ivar_compose_distribute {N T M R L} n m
      (f : ivar N T M) (g : morph T M R L) :
  g @ (rename_ivar n m f) =m= rename_ivar n m (g @ f).
Proof.
  unfold rename_ivar.
  rewrite close_ivar_compose_distribute.
  rewrite open_ivar_compose_distribute.
  easy.
Qed.

Lemma shift_ivar_compose_distribute {N T M R L} n
      (f : ivar N T M) (g : morph T M R L) :
  g @ (shift_ivar n f) =m= shift_ivar n (g @ f).
Proof.
  unfold shift_ivar.
  rewrite weak_ivar_compose_distribute.
  rewrite open_ivar_compose_distribute.
  easy.
Qed.

Lemma subst_ivar_compose_distribute {N T M R L} n t
      (f : ivar N T M) (g : morph T M R L) :
  g @ (subst_ivar n t f)
  =m= subst_ivar n (morph_apply g t) (g @ f).
Proof.
  unfold subst_ivar.
  rewrite close_ivar_compose_distribute.
  rewrite bind_ivar_compose_distribute.
  easy.
Qed.

(* There is a full contravariant functor from [var N] to [ivar N
   T O] by composition.

   Operations not involving bind are in the image of that
   functor. We call these operations "static". *)

Definition open_var a : ivar 1 var 0 := open_ivar a 1.
Definition close_var a : ivar 0 var 1 := close_ivar a 1.
Definition weak_var : ivar 0 var 1 := weak_ivar 1.
Definition rename_var a b : ivar 0 var 0 :=
  (open_var b) @ (close_var a).
Definition shift_var a : ivar 0 var 0 := (open_var a) @ weak_var.

Lemma open_ivar_as_composition {N T M} n (f : ivar N T M) :
  open_ivar n f =m= f @ (morph_extend_by N (open_var n)).
Proof.
  rewrite <- morph_right_identity with (f := f) at 1.
  rewrite <- open_ivar_compose_distribute.
  easy.
Qed.

Lemma close_ivar_as_composition {N T M} n (f : ivar (S N) T M) :
  close_ivar n f =m=
  f @ (morph_extend_by N (close_var n)).
Proof.
  rewrite <- morph_right_identity with (f := f) at 1.
  rewrite <- close_ivar_compose_distribute.
  easy.
Qed.

Lemma weak_ivar_as_composition {N T M} (f : ivar (S N) T M) :
  weak_ivar f =m= f @ (morph_extend_by N weak_var).
Proof.
  rewrite <- morph_right_identity with (f := f) at 1.
  rewrite <- weak_ivar_compose_distribute.
  easy.
Qed.

Lemma rename_ivar_as_composition {N T M} n m (f : ivar N T M) :
  rename_ivar n m f
  =m= f @ (morph_extend_by N (rename_var n m)).
Proof.
  unfold rename_var, rename_ivar.
  rewrite morph_extend_by_compose,
    open_ivar_as_composition, close_ivar_as_composition.
  easy.
Qed.

Lemma shift_ivar_as_composition {N T M} n (f : ivar N T M) :
  shift_ivar n f
  =m= f @ (morph_extend_by N (shift_var n)).
Proof.
  unfold shift_var, shift_ivar.
  rewrite morph_extend_by_compose,
    open_ivar_as_composition, weak_ivar_as_composition.
  easy.
Qed.
