Require Import String Omega Setoid Morphisms.
Require Import Morph Index.

(* Free names are a pair of a string and an index *)

Set Primitive Projections.
Record name := mkname { name_string : string; name_index : index }.
Add Printing Constructor name.
Unset Primitive Projections.

(* Alias the projections to avoid bug in rewrite_strat *)
Definition n_string := name_string.
Definition n_index := name_index.

Definition name_of_string s := mkname s 0.
Coercion name_of_string : string >-> name.
Bind Scope string_scope with name.

(* Boolean equality function *)
Definition name_eqb n m :=
  andb (String.eqb (n_string n) (n_string m))
       (index_eqb (n_index n) (n_index m)).

Lemma name_eqb_eq n m :
  name_eqb n m = true <-> n = m.
Proof.
  destruct n as [ns ni], m as [ms mi]; unfold name_eqb; cbn.
  rewrite Bool.andb_true_iff; intuition auto.
  - f_equal.
    + apply String.eqb_eq; easy.
    + apply index_eqb_eq; easy.
  - rewrite String.eqb_eq; congruence.
  - rewrite index_eqb_eq; congruence.
Qed.

Lemma name_eqb_neq n m :
  name_eqb n m = false <-> n <> m.
Proof.
  split.
  - intros Heq1 Heq2.
    rewrite <- name_eqb_eq in Heq2.
    rewrite Heq1 in Heq2; discriminate.
  - intro Hneq.
    remember (name_eqb n m) as nm eqn:Hnm.
    symmetry in Hnm.
    destruct nm; try easy.
    rewrite name_eqb_eq in Hnm.
    contradiction.
Qed.

Lemma name_eqb_refl n :
  name_eqb n n = true.
Proof.
  unfold name_eqb.
  rewrite index_eqb_refl.
  rewrite String.eqb_refl.
  easy.
Qed.

(* Useful lemma *)
Lemma name_neq_string_eq_index_neq n m :
  n <> m ->
  n_string n = n_string m ->
  n_index n <> n_index m.
Proof.
  intros Hneq Heq1 Heq2; apply Hneq.
  replace n with (mkname (n_string n) (n_index n)) by easy.
  rewrite Heq1, Heq2; easy.
Qed.

(* Liftable functions from [names]s to [nset]s that we treat
   like direct sums of streams *)
Definition iname (T : nset) M := kmorph name T M.

Bind Scope kmorph_scope with iname.

Definition project_iname {T M} s (f : iname T M) : iindex T M :=
  fun V (i : index) => f V (mkname s i).
Arguments project_iname {T M} s f V i /.

Definition with_iname {T M} s (f : iindex T M) (g : iname T M)
  : iname T M :=
  fun V (n : name) =>
    if string_dec (n_string n) s then get_iindex (n_index n) f V
    else g V n.

(* Derived operations *)

Definition get_iname {T M} (n : name) (f : iname T M) : pnset T M :=
  get_iindex (n_index n) (project_iname (n_string n) f).

Definition delete_iname {T M} (n : name) (f : iname T M) : iname T M :=
  with_iname (n_string n)
    (delete_iindex (n_index n) (project_iname (n_string n) f)) f.

Definition insert_iname {T M} (a : pnset T M) n (f : iname T M)
  : iname T M :=
  with_iname (n_string n)
    (insert_iindex a (n_index n) (project_iname (n_string n) f)) f.

(* Morphism definitions *)

Add Parametric Morphism {T M} s : (@project_iname T M s)
    with signature eq_kmorph ==> eq_kmorph
    as project_iname_mor.
  intros * Heq V n; unfold project_iname.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {T M} s : (@with_iname T M s)
    with signature eq_kmorph ==> eq_kmorph ==> eq_kmorph
      as with_iname_mor.
  intros * Heq1 * Heq2 V n; unfold with_iname; cbn.
  rewrite Heq1, Heq2; easy.
Qed.

Add Parametric Morphism {T M} : (@get_iname T M)
    with signature eq ==> eq_kmorph ==> eq_pnset
    as get_iname_mor.
  intros * Heq V; unfold get_iname; cbn.
  rewrite Heq; easy.
Qed.

(* Work around apparent bug in morphism resolution *)
Instance get_iname_mor_eta {T M} :
  Proper (eq ==> eq_kmorph ==> forall_relation (fun V : nat => eq))
    (@get_iname T M) | 2.
Proof.
  apply get_iname_mor_Proper.
Qed.

Add Parametric Morphism {T M} : (@delete_iname T M)
    with signature eq ==> eq_kmorph ==> eq_kmorph
      as delete_iname_mor.
  intros * Heq V m; unfold delete_iname.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {T M} : (@insert_iname T M)
    with signature eq_pnset ==> eq ==> eq_kmorph ==> eq_kmorph
    as insert_iname_mor.
  intros * Heq1 * Heq2 V m; unfold insert_iname.
  rewrite Heq1, Heq2; easy.
Qed.

(* The identity [iname] *)

Definition id_iname : iname (knset name) 0 :=
  fun _ (j : name) => j.
Arguments id_iname V j /.

(* Reductions *)

Lemma red_with_iname_eq {T M} s f (g : iname T M) V n :
  s = n_string n ->
  with_iname s f g V n = f V (n_index n).
Proof.
  intro Heq; subst; unfold with_iname.
  destruct (string_dec (n_string n) (n_string n));
    try contradiction; easy.
Qed.

Lemma red_with_iname_neq {T M} s f (g : iname T M) V n :
  s <> n_string n ->
  with_iname s f g V n = g V n.
Proof.
  intro Heq; unfold with_iname.
  destruct (string_dec (n_string n) s); subst;
    try contradiction; easy.
Qed.

Lemma red_get_iname {T M} n (f : iname T M) V :
  get_iname n f V = f V n.
Proof.
  unfold get_iname; easy.
Qed.

Lemma red_delete_iname_indistinct {T M} n (f : iname T M) V m :
  n_string n = n_string m ->
  delete_iname n f V m
  = delete_iindex (n_index n)
      (project_iname (n_string n) f) V (n_index m).
Proof.
  intro Heq; unfold delete_iname.
  rewrite red_with_iname_eq; easy.
Qed.

Lemma red_delete_iname_distinct {T M} n (f : iname T M) V m :
  n_string n <> n_string m ->
  delete_iname n f V m = f V m.
Proof.
  intro Heq; unfold delete_iname.
  rewrite red_with_iname_neq; easy.
Qed.

Lemma red_insert_iname_indistinct {T M} n a (f : iname T M) V m :
  n_string n = n_string m ->
  insert_iname a n f V m
  = insert_iindex a (n_index n)
      (project_iname (n_string n) f) V (n_index m).
Proof.
  intro Heq; unfold insert_iname.
  rewrite red_with_iname_eq; easy.
Qed.

Lemma red_insert_iname_distinct {T M} n a (f : iname T M) V m :
  n_string n <> n_string m ->
  insert_iname a n f V m = f V m.
Proof.
  intro Heq; unfold insert_iname.
  rewrite red_with_iname_neq; easy.
Qed.

Hint Rewrite @red_with_iname_eq @red_with_iname_neq
     @red_delete_iname_distinct @red_delete_iname_indistinct
     @red_insert_iname_distinct @red_insert_iname_indistinct
     using (cbn; congruence) : red_inames.

(* Rewrite operations using reductions *)
Ltac red_inames :=
  autorewrite with red_inames;
  repeat progress
    (try (rewrite_strat topdown (hints red_inames)); cbn).

(* Case split on the equality of the string parameters. *)
Ltac case_string s1 s2 :=
  destruct (string_dec s1 s2);
    red_inames; [> replace s2 with s1 by easy |]; try contradiction.

(* Beta and eta rules for [iname] operations *)

Lemma iname_beta_project_eq_pointwise {T M} s1 s2
      f (g : iname T M) :
  s1 = s2 ->
  project_iname s1 (with_iname s2 f g) =km= f.
Proof.
  intros Heq V i; red_inames; easy.
Qed.

Definition iname_beta_project_eq {T M} s1 s2 f g :=
  fun V Heq =>
    eq_kmorph_expand
      (@iname_beta_project_eq_pointwise T M s1 s2 f g Heq) V.

Lemma iname_beta_project_same_pointwise {T M} s f (g : iname T M) :
  project_iname s (with_iname s f g) =km= f.
Proof. apply iname_beta_project_eq_pointwise; easy. Qed.

Definition iname_beta_project_same {T M} s f g :=
  eq_kmorph_expand (@iname_beta_project_same_pointwise T M s f g).

Lemma iname_beta_with_eq_pointwise {T M} s1 f s2 g (h : iname T M) :
  s1 = s2 ->
  with_iname s1 f (with_iname s2 g h)
  =km= with_iname s1 f h.
Proof.
  intros Heq V n.
  case_string s1 (n_string n); easy.
Qed.

Definition iname_beta_with_eq {T M} s1 f s2 g h :=
  fun V Heq =>
    eq_kmorph_expand
      (@iname_beta_with_eq_pointwise T M s1 f s2 g h Heq) V.

Lemma iname_beta_with_same_pointwise {T M} s f g (h : iname T M) :
  with_iname s f (with_iname s g h)
  =km= with_iname s f h.
Proof. apply iname_beta_with_eq_pointwise; easy. Qed.

Definition iname_beta_with_same {T M} s f g h :=
  eq_kmorph_expand (@iname_beta_with_same_pointwise T M s f g h).

Lemma iname_eta_eq_pointwise {T M} s1 s2 (f : iname T M) :
  s1 = s2 ->
  with_iname s1 (project_iname s2 f) f =km= f.
Proof.
  intros Heq V n.
  case_string s1 (n_string n); subst; easy.
Qed.

Definition iname_eta_eq {T M} s1 s2 f :=
  fun V Heq =>
    eq_kmorph_expand (@iname_eta_eq_pointwise T M s1 s2 f Heq) V.

Lemma iname_eta_pointwise {T M} s (f : iname T M) :
  with_iname s (project_iname s f) f =km= f.
Proof. apply iname_eta_eq_pointwise; easy. Qed.

Definition iname_eta {T M} s f :=
  eq_kmorph_expand (@iname_eta_pointwise T M s f).

Hint Rewrite @iname_beta_project_same @iname_beta_with_same
     @iname_eta
  : simpl_inames.

Hint Rewrite @iname_beta_project_eq @iname_beta_with_eq @iname_eta_eq
  using (cbn; congruence) : simpl_inames_eqn.

Hint Rewrite @iname_beta_project_same_pointwise
     @iname_beta_with_same_pointwise @iname_eta_pointwise
  : simpl_inames_pointwise.

Hint Rewrite @iname_beta_project_eq_pointwise
     @iname_beta_with_eq_pointwise @iname_eta_eq_pointwise
  using (cbn; congruence) : simpl_inames_pointwise_eqn.

(* Unfolding derived operations *)

Lemma unfold_get_iname {T M} n (f : iname T M) :
  get_iname n f
  = get_iindex (n_index n) (project_iname (n_string n) f).
Proof. easy. Qed.

Lemma unfold_delete_iname {T M} n (f : iname T M) :
  delete_iname n f
  = with_iname (n_string n)
      (delete_iindex (n_index n) (project_iname (n_string n) f)) f.
Proof. easy. Qed.

Lemma unfold_insert_iname {T M} n a (f : iname T M) :
  insert_iname a n f
  = with_iname (n_string n)
      (insert_iindex a (n_index n) (project_iname (n_string n) f)) f.
Proof. easy. Qed.

Hint Rewrite @unfold_get_iname @unfold_delete_iname
  @unfold_insert_iname
  : unfold_inames.

(* Folding derived operations *)

Lemma fold_get_iname {T M} n (f : iname T M) :
  get_iindex (n_index n) (project_iname (n_string n) f)
  = get_iname n f.
Proof. easy. Qed.

Lemma fold_delete_iname {T M} n (f : iname T M) :
  with_iname (n_string n)
    (delete_iindex (n_index n) (project_iname (n_string n) f)) f
  = delete_iname n f.
Proof. easy. Qed.

Lemma fold_insert_iname {T M} n a (f : iname T M) :
  with_iname (n_string n)
    (insert_iindex a (n_index n) (project_iname (n_string n) f)) f
  = insert_iname a n f.
Proof. easy. Qed.

Hint Rewrite @fold_get_iname @fold_delete_iname
  @fold_insert_iname : fold_inames.

(* Simplify [iname] terms by unfolding, simplifying and folding *)
Ltac simpl_inames :=
  autorewrite with unfold_inames;
  autorewrite with simpl_inames;
  autorewrite with simpl_iindexs;
  repeat progress
    (cbn;
     try (rewrite_strat topdown (hints simpl_inames));
     try (rewrite_strat topdown (hints simpl_iindexs)));
  autorewrite with fold_inames.

Ltac simpl_inames_eqn :=
  autorewrite with unfold_inames;
  autorewrite with simpl_inames;
  autorewrite with simpl_iindexs;
  repeat progress
    (cbn;
     try (rewrite_strat topdown (hints simpl_inames));
     try (rewrite_strat topdown (hints simpl_inames_eqn));
     try (rewrite_strat topdown (hints simpl_iindexs));
     try (rewrite_strat topdown (hints simpl_iindexs_eqn)));
  autorewrite with fold_inames.

Ltac simpl_inames_pointwise :=
  autorewrite with unfold_inames;
  autorewrite with simpl_inames_pointwise;
  autorewrite with simpl_iindexs_pointwise;
  repeat progress
    (cbn;
     try (rewrite_strat topdown (hints simpl_inames_pointwise));
     try (rewrite_strat topdown (hints simpl_iindexs_pointwise)));
  autorewrite with fold_inames.

Ltac simpl_inames_pointwise_eqn :=
  autorewrite with unfold_inames;
  autorewrite with simpl_inames_pointwise;
  autorewrite with simpl_iindexs_pointwise;
  repeat progress
    (cbn;
     try (rewrite_strat topdown (hints simpl_inames_pointwise));
     try (rewrite_strat topdown (hints simpl_inames_pointwise_eqn));
     try (rewrite_strat topdown (hints simpl_iindexs_pointwise));
     try (rewrite_strat topdown (hints simpl_iindexs_pointwise_eqn)));
  autorewrite with fold_inames.

(* Transposing distinct operations *)

Definition transpose_with_iname_with_iname
           {T M} s1 f1 s2 f2 (g : iname T M) :
    s1 <> s2 ->
    with_iname s1 f1 (with_iname s2 f2 g)
    =km= with_iname s2 f2 (with_iname s1 f1 g).
Proof.
  intros Hneq V n.
  case_string s2 (n_string n);
    case_string s1 (n_string n); easy.
Qed.

Definition transpose_project_iname_with_iname
           {T M} s1 s2 f (g : iname T M) :
    s1 <> s2 ->
    project_iname s1 (with_iname s2 f g)
    =km= project_iname s1 g.
Proof.
  intros Hneq V n.
  red_inames; easy.
Qed.

(* Transposing derived operations

   We wish to reason about transposing [insert] and [delete]
   operations. These operations are not commutative, however
   they can be transposed by applying transformations to
   their indices.

   We follow the same approach as for [iindex]s. We define
   two transformations on names:

     transpose_iname_left(op1, op2, n1, n2)

     transpose_iname_right(op2, op1, n2, n1)

   such that:

     op1<n1> (op2<n2>(f))
     = op2<transpose_iname_left(op1, op2, n1, n2)>
         (op1<transpose_iname_right(op2, op1, n2, n1)>(f))

   These transformations do not work in the case where [op1]
   is [delete], [op2] is [insert] and [n1 = n2]. In this
   case the composed operations reduce to the identity by
   beta-reduction and cannot be transposed.
*)

Definition apply_iname_op {T M}
           (op : pnset_stream_op T M) :=
  match op with
  | Ins a => insert_iname a
  | Del => delete_iname
  end.

(* Precondition on transposing two operations *)
Definition irreducible_iname_ops (op1 op2 : stream_op)
  : name -> name -> Prop :=
  match op1, op2 with
  | insert, insert => fun n1 n2 => True
  | insert, delete => fun n1 n2 => True
  | delete, insert => fun n1 n2 => n1 <> n2
  | delete, delete => fun n1 n2 => True
  end.

(* Shift and unshift

   We define [transpose_iname_left] and
   [transpose_iname_right] in terms of three operations on
   names: [shift_below_name], [shift_above_name] and
   [unshift_name].
*)

Definition shift_below_name_index (n : name)
  : name -> index :=
  fun (m : name) =>
    if string_dec (n_string n) (n_string m) then
      shift_below_index (n_index n) (n_index m)
    else (n_index m).

Definition shift_below_name (n : name) : name -> name :=
  fun (m : name) =>
    mkname (n_string m) (shift_below_name_index n m).

Definition shift_above_name_index (n : name)
  : name -> index :=
  fun (m : name) =>
    if string_dec (n_string n) (n_string m) then
      shift_above_index (n_index n) (n_index m)
    else (n_index m).

Definition shift_above_name (n : name) : name -> name :=
  fun (m : name) =>
    mkname (n_string m) (shift_above_name_index n m).

Definition unshift_name_index (n : name) : name -> index :=
  fun (m : name) =>
    if string_dec (n_string n) (n_string m) then
      unshift_index (n_index n) (n_index m)
    else (n_index m).

Definition unshift_name (n : name) : name -> name :=
  fun (m : name) =>
    mkname (n_string m) (unshift_name_index n m).

(* Reductions *)

Lemma red_shift_below_name_index_distinct n m :
  n_string n <> n_string m ->
  shift_below_name_index n m = (n_index m).
Proof.
  intros; unfold shift_below_name_index.
  destruct (string_dec (n_string n) (n_string m)); subst;
    try contradiction; easy.
Qed.

Lemma red_shift_below_name_index_indistinct n m :
  n_string n = n_string m ->
  shift_below_name_index n m
  = shift_below_index (n_index n) (n_index m).
Proof.
  intros; unfold shift_below_name_index.
  destruct (string_dec (n_string n) (n_string m)); subst;
    try contradiction; easy.
Qed.

Lemma red_shift_below_name_distinct n m :
  n_string n <> n_string m ->
  shift_below_name n m = m.
Proof.
  intros; unfold shift_below_name.
  rewrite red_shift_below_name_index_distinct; easy.
Qed.

Lemma red_shift_below_name_indistinct n m :
  n_string n = n_string m ->
  shift_below_name n m
  = mkname (n_string m)
      (shift_below_index (n_index n) (n_index m)).
Proof.
  intros; unfold shift_below_name.
  rewrite red_shift_below_name_index_indistinct; easy.
Qed.

Lemma red_shift_above_name_index_distinct n m :
  n_string n <> n_string m ->
  shift_above_name_index n m = (n_index m).
Proof.
  intros; unfold shift_above_name_index.
  destruct (string_dec (n_string n) (n_string m)); subst;
    try contradiction; easy.
Qed.

Lemma red_shift_above_name_index_indistinct n m :
  n_string n = n_string m ->
  shift_above_name_index n m
  = shift_above_index (n_index n) (n_index m).
Proof.
  intros; unfold shift_above_name_index.
  destruct (string_dec (n_string n) (n_string m)); subst;
    try contradiction; easy.
Qed.

Lemma red_shift_above_name_distinct n m :
  n_string n <> n_string m ->
  shift_above_name n m = m.
Proof.
  intros; unfold shift_above_name.
  rewrite red_shift_above_name_index_distinct; easy.
Qed.

Lemma red_shift_above_name_indistinct n m :
  n_string n = n_string m ->
  shift_above_name n m
  = mkname (n_string m)
      (shift_above_index (n_index n) (n_index m)).
Proof.
  intros; unfold shift_above_name.
  rewrite red_shift_above_name_index_indistinct; easy.
Qed.

Lemma red_unshift_name_index_distinct n m :
  n_string n <> n_string m ->
  unshift_name_index n m = (n_index m).
Proof.
  intros; unfold unshift_name_index.
  destruct (string_dec (n_string n) (n_string m)); subst;
    try contradiction; easy.
Qed.

Lemma red_unshift_name_index_indistinct n m :
  n_string n = n_string m ->
  unshift_name_index n m
  = unshift_index (n_index n) (n_index m).
Proof.
  intros; unfold unshift_name_index.
  destruct (string_dec (n_string n) (n_string m)); subst;
    try contradiction; easy.
Qed.

Lemma red_unshift_name_distinct n m :
  n_string n <> n_string m ->
  unshift_name n m = m.
Proof.
  intros; unfold unshift_name.
  rewrite red_unshift_name_index_distinct; easy.
Qed.

Lemma red_unshift_name_indistinct n m :
  n_string n = n_string m ->
  unshift_name n m
  = mkname (n_string m)
      (unshift_index (n_index n) (n_index m)).
Proof.
  intros; unfold unshift_name.
  rewrite red_unshift_name_index_indistinct; easy.
Qed.

Hint Rewrite @red_shift_below_name_index_distinct
     @red_shift_below_name_index_indistinct
     @red_shift_below_name_distinct
     @red_shift_below_name_indistinct
     @red_shift_above_name_index_distinct
     @red_shift_above_name_index_indistinct
     @red_shift_above_name_distinct
     @red_shift_above_name_indistinct
     @red_unshift_name_index_distinct
     @red_unshift_name_index_indistinct
     @red_unshift_name_distinct
     @red_unshift_name_indistinct
     using (cbn; congruence) : red_inames.

(* Useful lemmas about shifting *)

Lemma shift_below_name_neq n m :
  shift_below_name n m <> n.
Proof.
  pose shift_below_index_neq.
  case_string (n_string n) (n_string m);
    try congruence.
  destruct n, m; cbn in *; congruence.
Qed.

Lemma shift_above_name_neq_shift_below_name n m :
  shift_above_name n m <> shift_below_name m n.
Proof.
  pose shift_above_index_neq_shift_below_index.
  case_string (n_string n) (n_string m); congruence.
Qed.

Definition transpose_iname_left (op1 op2 : stream_op) :=
  match op1, op2 with
  | insert, insert => shift_below_name
  | insert, delete => shift_above_name
  | delete, insert => unshift_name
  | delete, delete => unshift_name
  end.
Arguments transpose_iname_left !op1 !op2.

Definition transpose_iname_right (op2 op1 : stream_op) :=
  match op1, op2 with
  | insert, insert => unshift_name
  | insert, delete => shift_below_name
  | delete, insert => unshift_name
  | delete, delete => shift_below_name
  end.
Arguments transpose_iname_right !op2 !op1.

Lemma transpose_iname {T M}
      (op1 op2 : pnset_stream_op T M) :
  forall n1 n2 f,
    irreducible_iname_ops op1 op2 n1 n2 ->
    apply_iname_op op1 n1
      (apply_iname_op op2 n2 f)
    =km= apply_iname_op op2
           (transpose_iname_left op1 op2 n1 n2)
              (apply_iname_op op1
                 (transpose_iname_right op2 op1 n2 n1) f).
Proof.
  intros n1 n2 f Hirr.
  case_string (n_string n1) (n_string n2).
  - destruct op1, op2; cbn in *; red_inames;
      simpl_inames_pointwise_eqn.
    + transpose_iindex (Ins _) _ (Ins _) _.
      congruence.
    + transpose_iindex (Ins _) _ Del _.
      congruence.
    + transpose_iindex Del _ (Ins _) _;
        auto using name_neq_string_eq_index_neq.
      congruence.
    + transpose_iindex Del _ Del _.
      congruence.
  - destruct op1, op2; cbn;
      autorewrite with unfold_inames; red_inames;
      rewrite transpose_with_iname_with_iname
        by congruence;
      rewrite transpose_project_iname_with_iname
        by congruence;
      rewrite transpose_project_iname_with_iname
        by congruence;
      easy.
Qed.

Tactic Notation
  "transpose_iname"
    uconstr(op1) uconstr(n1) uconstr(op2) uconstr(n2) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_iname op1 op2 n1 n2) as Hrw;
      cbn in Hrw; rewrite Hrw;
        [> | try easy]; clear Hrw.

Tactic Notation
  "transpose_iname"
    uconstr(op1) uconstr(n1) uconstr(op2) uconstr(n2)
    "at" occurrences(occ) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_iname op1 op2 n1 n2) as Hrw;
      cbn in Hrw; rewrite Hrw at occ;
        [> | try easy]; clear Hrw.

(* Normalizing pairs of operations

   The choice of names on some pairs of operations is not
   unique. In particular,

     delete (s, S i) (insert (s, i) f)

   is equivalent to:

     delete (s, i) (insert (s, S i) f)

   We define a pair of transformations on names:

     normalize_iname_left(op2, op1, n2, n1)

     normalize_iname_right(op1, op2, n1, n2)

   such that:

     op1<n1>(op2<n2>(f))
     = op1<normalize_iname_left(op2, op1, n2, n1)>
         (op2<normalize_iname_right(op1, op2, n1, n2)>(f))

   and:

     normalize_iname_left(insert, delete, (s, i), (s, S i))
     = (s, i)
     normalize_iname_right(delete, insert, (s, S i), (s, i))
     = (s, S i)

*)

(* Contract

   We define [normalize_iname_left] and
   [normalize_iname_right] in terms of three operations on
   names: [contract_down_name] ,[contrace_up_name] and
   [unchanged_name]. *)

Definition contract_down_name_index (n : name)
  : name -> index :=
  fun (m : name) =>
    if string_dec (n_string n) (n_string m) then
      contract_down_index (n_index n) (n_index m)
    else (n_index m).

Definition contract_down_name (n : name) : name -> name :=
  fun (m : name) =>
    mkname (n_string m) (contract_down_name_index n m).

Definition contract_up_name_index (n : name)
  : name -> index :=
  fun (m : name) =>
    if string_dec (n_string n) (n_string m) then
      contract_up_index (n_index n) (n_index m)
    else (n_index m).

Definition contract_up_name (n : name) : name -> name :=
  fun (m : name) =>
    mkname (n_string m) (contract_up_name_index n m).

Definition unchanged_name (i : name) : name -> name :=
  fun (j : name) => j.
Arguments unchanged_name i j /.

(* Reductions *)

Lemma red_contract_down_name_index_distinct n m :
  n_string n <> n_string m ->
  contract_down_name_index n m = (n_index m).
Proof.
  intros; unfold contract_down_name_index.
  destruct (string_dec (n_string n) (n_string m)); subst;
    try contradiction; easy.
Qed.

Lemma red_contract_down_name_index_indistinct n m :
  n_string n = n_string m ->
  contract_down_name_index n m
  = contract_down_index (n_index n) (n_index m).
Proof.
  intros; unfold contract_down_name_index.
  destruct (string_dec (n_string n) (n_string m)); subst;
    try contradiction; easy.
Qed.

Lemma red_contract_down_name_distinct n m :
  n_string n <> n_string m ->
  contract_down_name n m = m.
Proof.
  intros; unfold contract_down_name.
  rewrite red_contract_down_name_index_distinct; easy.
Qed.

Lemma red_contract_down_name_indistinct n m :
  n_string n = n_string m ->
  contract_down_name n m
  = mkname (n_string m)
      (contract_down_index (n_index n) (n_index m)).
Proof.
  intros; unfold contract_down_name.
  rewrite red_contract_down_name_index_indistinct; easy.
Qed.

Lemma red_contract_up_name_index_distinct n m :
  n_string n <> n_string m ->
  contract_up_name_index n m = (n_index m).
Proof.
  intros; unfold contract_up_name_index.
  destruct (string_dec (n_string n) (n_string m)); subst;
    try contradiction; easy.
Qed.

Lemma red_contract_up_name_index_indistinct n m :
  n_string n = n_string m ->
  contract_up_name_index n m
  = contract_up_index (n_index n) (n_index m).
Proof.
  intros; unfold contract_up_name_index.
  destruct (string_dec (n_string n) (n_string m)); subst;
    try contradiction; easy.
Qed.

Lemma red_contract_up_name_distinct n m :
  n_string n <> n_string m ->
  contract_up_name n m = m.
Proof.
  intros; unfold contract_up_name.
  rewrite red_contract_up_name_index_distinct; easy.
Qed.

Lemma red_contract_up_name_indistinct n m :
  n_string n = n_string m ->
  contract_up_name n m
  = mkname (n_string m)
      (contract_up_index (n_index n) (n_index m)).
Proof.
  intros; unfold contract_up_name.
  rewrite red_contract_up_name_index_indistinct; easy.
Qed.

Lemma red_unchanged_name n m :
  unchanged_index n m = m.
Proof. easy. Qed.

Hint Rewrite @red_contract_down_name_index_distinct
     @red_contract_down_name_index_indistinct
     @red_contract_down_name_distinct
     @red_contract_down_name_indistinct
     @red_contract_up_name_index_distinct
     @red_contract_up_name_index_indistinct
     @red_contract_up_name_distinct
     @red_contract_up_name_indistinct
     @red_unchanged_name
     using (cbn; congruence) : red_inames.

Definition normalize_iname_left (op2 op1 : stream_op)
  : name -> name -> name :=
  match op1, op2 with
  | insert, insert => unchanged_name
  | insert, delete => unchanged_name
  | delete, insert => contract_down_name
  | delete, delete => unchanged_name
  end.

Definition normalize_iname_right (op1 op2 : stream_op) :=
  match op1, op2 with
  | insert, insert => unchanged_name
  | insert, delete => unchanged_name
  | delete, insert => contract_up_name
  | delete, delete => unchanged_name
  end.

Lemma normalize_iname {T M}
      (op1 op2 : pnset_stream_op T M) :
  forall i1 i2 f,
    apply_iname_op op1 i1
      (apply_iname_op op2 i2 f)
    =km= apply_iname_op op1
           (normalize_iname_left op2 op1 i2 i1)
           (apply_iname_op op2
              (normalize_iname_right op1 op2 i1 i2) f).
Proof.
  intros n1 n2 f.
  destruct op1, op2; cbn; try easy.
  case_string (n_string n1) (n_string n2); try easy.
  intros V n3.
  case_string (n_string n2) (n_string n3); try easy.
  simpl_inames_pointwise_eqn.
  normalize_iindex Del _ (Ins _) _.
  congruence.
Qed.

Tactic Notation
  "normalize_iname" uconstr(op1) uconstr(i1) uconstr(op2) uconstr(i2) :=
  let Hrw := fresh "Hrw" in
    epose (normalize_iname op1 op2 i1 i2) as Hrw;
      cbn in Hrw; rewrite Hrw; clear Hrw.

Tactic Notation
  "normalize_iname"
    uconstr(op1) uconstr(i1) uconstr(op2) uconstr(i2)
    "at" occurrences(occ) :=
  let Hrw := fresh "Hrw" in
    epose (normalize_iname op1 op2 i1 i2) as Hrw;
      cbn in Hrw; rewrite Hrw at occ; clear Hrw.

(* Transposing normalizes indices *)

Lemma normalize_transpose_iname_left (op1 op2 : stream_op) :
  forall n1 n2,
    transpose_iname_left op1 op2 n1 n2
    = normalize_iname_left op1 op2
        (transpose_iname_right op2 op1 n2 n1)
        (transpose_iname_left op1 op2 n1 n2).
Proof.
  intros n1 n2.
  case_string (n_string n1) (n_string n2).
  - destruct op1, op2; red_inames; try easy.
    normalize_transpose_iindex_left insert _ delete _ at 1.
    easy.
  - destruct op1, op2; red_inames; easy.
Qed.

Lemma normalize_transpose_iname_right (op1 op2 : stream_op) :
  forall n1 n2,
    transpose_iname_right op2 op1 n2 n1
    = normalize_iname_right op2 op1
        (transpose_iname_left op1 op2 n1 n2)
        (transpose_iname_right op2 op1 n2 n1).
Proof.
  intros n1 n2.
  case_string (n_string n1) (n_string n2).
  - destruct op1, op2; red_inames; try easy.
    normalize_transpose_iindex_right insert _ delete _ at 1.
    easy.
  - destruct op1, op2; red_inames; easy.
Qed.

(* Permutations of [iname] operations

   Beyond transposing pairs of operations, we wish to reason
   about arbitrary permutations of sequences of [iname]
   operations.

   Given a sequence of n operations, rewriting with
   [transpose_iname] essentially gives us transpositions σᵢ
   which swap the ith and (i+1)th operations. The group of
   permutations of n operations can be generated from these
   transpositions and the following equations:

   1) σᵢ ∘ σⱼ = σⱼ ∘ σᵢ where |i - j| > 1

   2) σᵢ ∘ σᵢ = 1

   3) σᵢ ∘ σᵢ₊₁ ∘ σᵢ = σᵢ₊₁ ∘ σᵢ ∘ σᵢ₊₁

   The first equation follows automatically since rewriting
   with [transpose_iname] only affects the operations that
   are transposed.

   Lemmas [transpose_iname_squared_left] and
   [transpose_iname_squared_right] below are equivalent to
   the second equation.

   Lemmas [transpose_iname_reverse_left],
   [transpose_iname_reverse_middle] and
   [transpose_iname_reverse_right] below are equivalent to
   the third equation.
 *)

Lemma transpose_iname_squared_left (op1 op2 : stream_op) :
  forall n1 n2,
    transpose_iname_left op2 op1
      (transpose_iname_left op1 op2 n1 n2)
      (transpose_iname_right op2 op1 n2 n1)
    = normalize_iname_left op2 op1 n2 n1.
Proof.
  intros.
  case_string (n_string n1) (n_string n2).
  - destruct op1, op2; cbn; red_inames.
    + transpose_iindex_squared_left insert _ insert _; easy.
    + transpose_iindex_squared_left insert _ delete _; easy.
    + transpose_iindex_squared_left delete _ insert _; easy.
    + transpose_iindex_squared_left delete _ delete _; easy.
  - destruct op1, op2; cbn; red_inames; easy.
Qed.

Lemma transpose_iname_squared_right (op1 op2 : stream_op) :
  forall n1 n2,
    irreducible_iname_ops op1 op2 n1 n2 ->
    transpose_iname_right op1 op2
      (transpose_iname_right op2 op1 n2 n1)
      (transpose_iname_left op1 op2 n1 n2)
    = normalize_iname_right op1 op2 n1 n2.
Proof.
  intros.
  case_string (n_string n1) (n_string n2).
  - destruct op1, op2; cbn in *; red_inames.
    + transpose_iindex_squared_right insert _ insert _; easy.
    + transpose_iindex_squared_right insert _ delete _; easy.
    + transpose_iindex_squared_right delete _ insert _;
        auto using name_neq_string_eq_index_neq.
    + transpose_iindex_squared_right delete _ delete _; easy.
  - destruct op1, op2; cbn; red_inames; easy.
Qed.

Tactic Notation "transpose_iname_squared_left"
       uconstr(op1) uconstr(n1) uconstr(op2) uconstr(n2) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_iname_squared_left op1 op2 n1 n2)
      as Hrw; cbn in Hrw; rewrite Hrw; clear Hrw.

Tactic Notation "transpose_iname_squared_left"
       uconstr(op1) uconstr(n1) uconstr(op2) uconstr(n2)
       "at" occurrences(occ) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_iname_squared_left op1 op2 n1 n2)
      as Hrw; cbn in Hrw; rewrite Hrw at occ; clear Hrw.

Tactic Notation "transpose_iname_squared_right"
       uconstr(op1) uconstr(n1) uconstr(op2) uconstr(n2) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_iname_squared_right op1 op2 n1 n2)
      as Hrw; cbn in Hrw;
        rewrite Hrw; [> | try easy]; clear Hrw.

Tactic Notation "transpose_iname_squared_right"
       uconstr(op1) uconstr(n1) uconstr(op2) uconstr(n2)
       "at" occurrences(occ) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_iname_squared_right op1 op2 n1 n2)
      as Hrw; cbn in Hrw;
        rewrite Hrw at occ; [> | try easy]; clear Hrw.

Lemma transpose_iname_reverse_left (op1 op2 op3 : stream_op) :
  forall n1 n2 n3,
    irreducible_iname_ops op1 op2 n1 n2 ->
    irreducible_iname_ops op2 op3 n2 n3 ->
    irreducible_iname_ops op1 op3 n1
      (transpose_iname_left op2 op3 n2 n3) ->
    transpose_iname_left op2 op3 (transpose_iname_left op1 op2 n1 n2)
      (transpose_iname_left op1 op3
         (transpose_iname_right op2 op1 n2 n1) n3)
    = normalize_iname_left op2 op3
        (transpose_iname_left op1 op2 n1
           (transpose_iname_right op3 op2 n3 n2))
        (transpose_iname_left op1 op3 n1
          (transpose_iname_left op2 op3 n2 n3)).
Proof.
  intros n1 n2 n3.
  case_string (n_string n1) (n_string n2);
    case_string (n_string n2) (n_string n3);
      case_string (n_string n1) (n_string n3);
        try congruence.
  - destruct op1, op2, op3; cbn; red_inames;
      intros Hirr1 Hirr2 Hirr3.
    + transpose_iindex_reverse_left
        insert _ insert _ insert _; easy.
    + transpose_iindex_reverse_left
        insert _ insert _ delete _; easy.
    + transpose_iindex_reverse_left
        insert _ delete _ insert _;
          auto using name_neq_string_eq_index_neq.
    + transpose_iindex_reverse_left
        insert _ delete _ delete _; easy.
    + transpose_iindex_reverse_left
        delete _ insert _ insert _;
          auto using name_neq_string_eq_index_neq.
      apply name_neq_string_eq_index_neq in Hirr3; auto.
    + transpose_iindex_reverse_left
        delete _ insert _ delete _;
          auto using name_neq_string_eq_index_neq.
    + transpose_iindex_reverse_left
        delete _ delete _ insert _;
          auto using name_neq_string_eq_index_neq.
      apply name_neq_string_eq_index_neq in Hirr3; auto.
    + transpose_iindex_reverse_left
        delete _ delete _ delete _; easy.
  - destruct op1, op2, op3; cbn; red_inames; easy.
  - destruct op1, op2, op3; cbn; red_inames; try easy;
      intros Hirr1 Hirr2 Hirr3.
    + normalize_transpose_iindex_left insert _ delete _ at 1; easy.
    + normalize_transpose_iindex_left insert _ delete _ at 1; easy.
  - destruct op1, op2, op3; cbn; red_inames; easy.
  - destruct op1, op2, op3; cbn; red_inames; easy.
Qed.

Lemma transpose_iname_reverse_middle (op1 op2 op3 : stream_op) :
  forall n1 n2 n3,
    irreducible_iname_ops op1 op2 n1 n2 ->
    irreducible_iname_ops op2 op3 n2 n3 ->
    irreducible_iname_ops op1 op3 n1
      (transpose_iname_left op2 op3 n2 n3) ->
    normalize_iname_right op3 op2
      (transpose_iname_left op1 op3 n1
          (transpose_iname_left op2 op3 n2 n3))
      (transpose_iname_left op1 op2
        (transpose_iname_right op3 op1
           (transpose_iname_left op2 op3 n2 n3) n1)
        (transpose_iname_right op3 op2 n3 n2))
    = normalize_iname_left op1 op2
        (transpose_iname_right op3 op1 n3
           (transpose_iname_right op2 op1 n2 n1))
        (transpose_iname_right op3 op2
          (transpose_iname_left op1 op3
            (transpose_iname_right op2 op1 n2 n1) n3)
          (transpose_iname_left op1 op2 n1 n2)).
Proof.
  intros n1 n2 n3.
  case_string (n_string n1) (n_string n2);
    case_string (n_string n2) (n_string n3);
      case_string (n_string n1) (n_string n3);
        try congruence.
  - destruct op1, op2, op3; cbn; red_inames;
      intros Hirr1 Hirr2 Hirr3.
    + transpose_iindex_reverse_middle
        insert _ insert _ insert _; easy.
    + transpose_iindex_reverse_middle
        insert _ insert _ delete _; easy.
    + transpose_iindex_reverse_middle
        insert _ delete _ insert _;
          auto using name_neq_string_eq_index_neq.
    + transpose_iindex_reverse_middle
        insert _ delete _ delete _; easy.
    + transpose_iindex_reverse_middle
        delete _ insert _ insert _;
          auto using name_neq_string_eq_index_neq.
      apply name_neq_string_eq_index_neq in Hirr3; auto.
    + transpose_iindex_reverse_middle
        delete _ insert _ delete _;
          auto using name_neq_string_eq_index_neq.
    + transpose_iindex_reverse_middle
        delete _ delete _ insert _;
          auto using name_neq_string_eq_index_neq.
      apply name_neq_string_eq_index_neq in Hirr3; auto.
    + transpose_iindex_reverse_middle
        delete _ delete _ delete _; easy.
  - destruct op1, op2, op3; cbn; red_inames; try easy;
      intros Hirr1 Hirr2 Hirr3.
    + normalize_transpose_iindex_left insert _ delete _ at 1; easy.
    + normalize_transpose_iindex_left insert _ delete _ at 1; easy.
  - destruct op1, op2, op3; cbn; red_inames; try easy;
      intros Hirr1 Hirr2 Hirr3.
    + normalize_transpose_iindex_right insert _ delete _ at 2; easy.
    + normalize_transpose_iindex_right insert _ delete _ at 2; easy.
  - destruct op1, op2, op3; cbn; red_inames; easy.
  - destruct op1, op2, op3; cbn; red_inames; easy.
Qed.

Lemma transpose_iname_reverse_right (op1 op2 op3 : stream_op) :
  forall n1 n2 n3,
    irreducible_iname_ops op1 op2 n1 n2 ->
    irreducible_iname_ops op2 op3 n2 n3 ->
    irreducible_iname_ops op1 op3 n1 (transpose_iname_left op2 op3 n2 n3) ->
    transpose_iname_right op2 op1
      (transpose_iname_right op3 op2 n3 n2)
      (transpose_iname_right op3 op1
        (transpose_iname_left op2 op3 n2 n3) n1)
    = normalize_iname_right op2 op1
        (transpose_iname_right op3 op2 n3
           (transpose_iname_left op1 op2 n1 n2))
        (transpose_iname_right op3 op1 n3
          (transpose_iname_right op2 op1 n2 n1)).
Proof.
  intros n1 n2 n3.
  case_string (n_string n1) (n_string n2);
    case_string (n_string n2) (n_string n3);
      case_string (n_string n1) (n_string n3);
        try congruence.
  - destruct op1, op2, op3; cbn; red_inames;
      intros Hirr1 Hirr2 Hirr3.
    + transpose_iindex_reverse_right
        insert _ insert _ insert _; easy.
    + transpose_iindex_reverse_right
        insert _ insert _ delete _; easy.
    + transpose_iindex_reverse_right
        insert _ delete _ insert _;
          auto using name_neq_string_eq_index_neq.
    + transpose_iindex_reverse_right
        insert _ delete _ delete _; easy.
    + transpose_iindex_reverse_right
        delete _ insert _ insert _;
          auto using name_neq_string_eq_index_neq.
      apply name_neq_string_eq_index_neq in Hirr3; auto.
    + transpose_iindex_reverse_right
        delete _ insert _ delete _;
          auto using name_neq_string_eq_index_neq.
    + transpose_iindex_reverse_right
        delete _ delete _ insert _;
          auto using name_neq_string_eq_index_neq.
      apply name_neq_string_eq_index_neq in Hirr3; auto.
    + transpose_iindex_reverse_right
        delete _ delete _ delete _; easy.
  - destruct op1, op2, op3; cbn; red_inames; try easy;
      intros Hirr1 Hirr2 Hirr3.
    + normalize_transpose_iindex_right insert _ delete _ at 1; easy.
    + normalize_transpose_iindex_right insert _ delete _ at 1; easy.
  - destruct op1, op2, op3; cbn; red_inames; easy.
  - destruct op1, op2, op3; cbn; red_inames; easy.
  - destruct op1, op2, op3; cbn; red_inames; easy.
Qed.

Tactic Notation "transpose_iname_reverse_left"
       uconstr(op1) uconstr(n1)
       uconstr(op2) uconstr(n2)
       uconstr(op3) uconstr(n3) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_iname_reverse_left
             op1 op2 op3 n1 n2 n3) as Hrw;
      cbn in Hrw; rewrite Hrw;
      [> | try easy | try easy | try easy]; clear Hrw.

Tactic Notation "transpose_iname_reverse_left"
       uconstr(op1) uconstr(n1)
       uconstr(op2) uconstr(n2)
       uconstr(op3) uconstr(n3)
       "at" occurrences(occ) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_iname_reverse_left
             op1 op2 op3 n1 n2 n3) as Hrw;
      cbn in Hrw; rewrite Hrw at occ;
      [> | try easy | try easy | try easy]; clear Hrw.

Tactic Notation "transpose_iname_reverse_middle"
       uconstr(op1) uconstr(n1)
       uconstr(op2) uconstr(n2)
       uconstr(op3) uconstr(n3) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_iname_reverse_middle
             op1 op2 op3 n1 n2 n3) as Hrw;
      cbn in Hrw; rewrite Hrw;
      [> | try easy | try easy | try easy]; clear Hrw.

Tactic Notation "transpose_iname_reverse_middle"
       uconstr(op1) uconstr(n1)
       uconstr(op2) uconstr(n2)
       uconstr(op3) uconstr(n3)
       "at" occurrences(occ) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_iname_reverse_middle
             op1 op2 op3 n1 n2 n3) as Hrw;
      cbn in Hrw; rewrite Hrw at occ;
      [> | try easy | try easy | try easy]; clear Hrw.

Tactic Notation "transpose_iname_reverse_right"
       uconstr(op1) uconstr(n1)
       uconstr(op2) uconstr(n2)
       uconstr(op3) uconstr(n3) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_iname_reverse_right
             op1 op2 op3 n1 n2 n3) as Hrw;
      cbn in Hrw; rewrite Hrw;
      [> | try easy | try easy | try easy]; clear Hrw.

Tactic Notation "transpose_iname_reverse_right"
       uconstr(op1) uconstr(n1)
       uconstr(op2) uconstr(n2)
       uconstr(op3) uconstr(n3)
       "at" occurrences(occ) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_iname_reverse_right
             op1 op2 op3 n1 n2 n3) as Hrw;
      cbn in Hrw; rewrite Hrw at occ;
      [> | try easy | try easy | try easy]; clear Hrw.

(* Pushing [get_iname] through other operations

   We reuse the machinery for trasposition, since this
   transformation is closely related to transposing
   operations with delete.
*)

Lemma transpose_get_iname {T M} (op : pnset_stream_op T M) :
  forall n1 n2 f,
    irreducible_iname_ops delete op n1 n2 ->
    get_iname n1 (apply_iname_op op n2 f)
    =p= get_iname (transpose_iname_right op delete n2 n1) f.
Proof.
  intros n1 n2 f.
  destruct op; cbn; intro Hirr.
  - case_string (n_string n1) (n_string n2).
    + simpl_inames_pointwise_eqn.
      transpose_get_iindex _ (Ins _) _;
        auto using name_neq_string_eq_index_neq;
        congruence.
    + autorewrite with unfold_inames; red_inames.
      rewrite transpose_project_iname_with_iname
        by congruence.
      easy.
  - case_string (n_string n1) (n_string n2).
    + simpl_inames_pointwise_eqn.
      transpose_get_iindex _ Del _;
        auto using name_neq_string_eq_index_neq;
        congruence.
    + autorewrite with unfold_inames; red_inames.
      rewrite transpose_project_iname_with_iname
        by congruence.
      easy.
Qed.

Tactic Notation "transpose_get_iname"
       uconstr(n1) uconstr(op) uconstr(n2) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_get_iname op n1 n2) as Hrw;
      cbn in Hrw; rewrite Hrw; [> | try easy]; clear Hrw.

Tactic Notation "transpose_get_iname"
       uconstr(n1) uconstr(op) uconstr(n2) "at" occurrences(occ) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_get_iname op n1 n2) as Hrw;
      cbn in Hrw; rewrite Hrw at occ; [> | try easy]; clear Hrw.

(* There is a full covariant functor from [T O] to [iname N
   T O] by composition.

   Such composition distributes over our operations. *)

Lemma project_iname_compose_distribute {T M R L} s
      (f : iname T M) (g : morph T M R L) :
  g @ (project_iname s f) =km= project_iname s (g @ f).
Proof. easy. Qed.

Lemma with_iname_compose_distribute {T M R L} s
      (f : iindex T M) (g : iname T M) (h : morph T M R L) :
  h @ (with_iname s f g) =km= with_iname s (h @ f) (h @ g).
Proof.
  intros V n.
  case_string s (n_string n); easy.
Qed.

Lemma get_iname_compose_distribute {T M R L} n
      (f : iname T M) (g : morph T M R L) :
  morph_apply g (get_iname n f) =p= get_iname n (g @ f).
Proof.
  unfold get_iname.
  rewrite get_iindex_compose_distribute.
  rewrite project_iname_compose_distribute.
  easy.
Qed.

Lemma delete_iname_compose_distribute {T M R L} n
      (f : iname T M) (g : morph T M R L) :
  g @ (delete_iname n f) =km= delete_iname n (g @ f).
Proof.
  unfold delete_iname.
  rewrite with_iname_compose_distribute.
  rewrite delete_iindex_compose_distribute.
  rewrite project_iname_compose_distribute.
  easy.
Qed.

Lemma insert_iname_compose_distribute {T M R L} n a
      (f : iname T M) (g : morph T M R L) :
  g @ (insert_iname a n f)
  =km= insert_iname (morph_apply g a) n (g @ f).
Proof.
  unfold insert_iname.
  rewrite with_iname_compose_distribute.
  rewrite insert_iindex_compose_distribute.
  rewrite project_iname_compose_distribute.
  easy.
Qed.
