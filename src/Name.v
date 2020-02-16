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
  n <> m -> n_string n = n_string m -> n_index n <> n_index m.
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

Definition insert_iname {T M} n (a : pnset T M) (f : iname T M)
  : iname T M :=
  with_iname (n_string n)
    (insert_iindex (n_index n) a (project_iname (n_string n) f)) f.

Definition move_iname {T M} n m (f : iname T M) :=
  insert_iname n (get_iname m f) (delete_iname m f).

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
    with signature eq ==> eq_pnset ==> eq_kmorph ==> eq_kmorph
    as insert_iname_mor.
  intros * Heq1 * Heq2 V m; unfold insert_iname.
  rewrite Heq1, Heq2; easy.
Qed.

Add Parametric Morphism {T M} : (@move_iname T M)
    with signature eq ==> eq ==> eq_kmorph ==> eq_kmorph
    as move_iname_mor.
  intros * Heq V o; unfold move_iname.
  rewrite Heq; easy.
Qed.

(* The identity [iname] *)

Definition id_iname : iname (knset name) 0 :=
  fun _ (j : name) => j.
Arguments id_iname V j /.

(* Successor *)
Definition succ_name (n : name) :=
  mkname (n_string n) (S (n_index n)).

(* Operational transforms *)

Definition shift_name (n : name) : name -> name :=
  delete_iname n id_iname 0.

Definition unshift_name (n : name) : name -> name :=
  insert_iname n (pnset_const n) id_iname 0.

Definition shift_above_name (n : name) : name -> name :=
  shift_name (succ_name n).

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

Lemma red_with_iname_same {T M} f (g : iname T M) V n :
  with_iname (n_string n) f g V n = f V (n_index n).
Proof.
  apply red_with_iname_eq; easy.
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

Lemma red_delete_iname_same {T M} n (f : iname T M) V :
  delete_iname n f V n
  = f V (mkname (n_string n) (S (n_index n))).
Proof.
  rewrite red_delete_iname_indistinct by easy.
  rewrite red_delete_iindex_same; easy.
Qed.

Lemma red_insert_iname_indistinct {T M} n a (f : iname T M) V m :
  n_string n = n_string m ->
  insert_iname n a f V m
  = insert_iindex (n_index n) a
      (project_iname (n_string n) f) V (n_index m).
Proof.
  intro Heq; unfold insert_iname.
  rewrite red_with_iname_eq; easy.
Qed.

Lemma red_insert_iname_distinct {T M} n a (f : iname T M) V m :
  n_string n <> n_string m ->
  insert_iname n a f V m = f V m.
Proof.
  intro Heq; unfold insert_iname.
  rewrite red_with_iname_neq; easy.
Qed.

Lemma red_insert_iname_same {T M} n a (f : iname T M) V :
  insert_iname n a f V n = a V.
Proof.
  rewrite red_insert_iname_indistinct by easy.
  rewrite red_insert_iindex_same; easy.
Qed.

Lemma red_shift_name_indistinct n m :
  n_string n = n_string m ->
  shift_name n m
  = mkname (n_string m) (shift_index (n_index n) (n_index m)).
Proof.
  intros Heq; unfold shift_name.
  rewrite red_delete_iname_indistinct by easy.
  rewrite Heq.
  case_order (n_index n) (n_index m); easy.
Qed.

Lemma red_shift_name_distinct n m :
  n_string n <> n_string m ->
  shift_name n m = m.
Proof.
  intros; unfold shift_name.
  rewrite red_delete_iname_distinct by easy; easy.
Qed.

Lemma red_shift_name_same n :
  shift_name n n
  = mkname (n_string n) (S (n_index n)).
Proof.
  rewrite red_shift_name_indistinct by easy.
  rewrite red_shift_index_same; easy.
Qed.

Lemma red_unshift_name_indistinct n m :
  n_string n = n_string m ->
  unshift_name n m
  = mkname (n_string m) (unshift_index (n_index n) (n_index m)).
Proof.
  intros Heq; unfold unshift_name.
  rewrite red_insert_iname_indistinct by easy.
  rewrite <- Heq.
  case_order (n_index n) (n_index m); easy.
Qed.

Lemma red_unshift_name_distinct n m :
  n_string n <> n_string m ->
  unshift_name n m = m.
Proof.
  intros; unfold unshift_name.
  rewrite red_insert_iname_distinct by easy; easy.
Qed.

Lemma red_unshift_name_same n :
  unshift_name n n = n.
Proof.
  rewrite red_unshift_name_indistinct by easy.
  rewrite red_unshift_index_same; easy.
Qed.

Lemma red_shift_above_name_indistinct n m :
  n_string n = n_string m ->
  shift_above_name n m
  = mkname (n_string m)
      (shift_above_index (n_index n) (n_index m)).
Proof.
  intros; unfold shift_above_name.
  rewrite red_shift_name_indistinct by easy; easy.
Qed.

Lemma red_shift_above_name_distinct n m :
  n_string n <> n_string m ->
  shift_above_name n m = m.
Proof.
  intros; unfold shift_above_name.
  rewrite red_shift_name_distinct by easy; easy.
Qed.

Lemma red_shift_above_name_same n :
  shift_above_name n n = n.
Proof.
  rewrite red_shift_above_name_indistinct by easy.
  rewrite red_shift_above_index_same; easy.
Qed.

Lemma red_move_iname_indistinct {T M} n m (f : iname T M) V o :
  n_string n = n_string o ->
  n_string m = n_string o ->
  move_iname n m f V o
  = move_iindex (n_index n) (n_index m)
      (project_iname (n_string n) f) V (n_index o).
Proof.
  intros Heq1 Heq2; unfold move_iname, move_iindex, get_iname.
  rewrite red_insert_iname_indistinct by easy.
  rewrite Heq1, Heq2.
  case_order (n_index n) (n_index o); try easy;
    rewrite red_delete_iname_indistinct by easy;
    rewrite Heq2; easy.
Qed.

Lemma red_move_iname_distinct1 {T M} n m (f : iname T M) V o :
  n_string n <> n_string o ->
  move_iname n m f V o
  = delete_iname m f V o.
Proof.
  intros; unfold move_iname.
  rewrite red_insert_iname_distinct by easy; easy.
Qed.

Lemma red_move_iname_distinct2 {T M} n m (f : iname T M) V o :
  n_string m <> n_string o ->
  move_iname n m f V o
  = insert_iname n (get_iname m f) f V o.
Proof.
  intros; unfold move_iname.
  destruct (string_dec (n_string n) (n_string o)).
  - rewrite red_insert_iname_indistinct by easy.
    rewrite red_insert_iname_indistinct by easy.
    case_order (n_index n) (n_index o); try easy;
      rewrite red_delete_iname_distinct by (cbn; congruence); easy.
  - rewrite red_insert_iname_distinct by easy.
    rewrite red_insert_iname_distinct by easy.
    rewrite red_delete_iname_distinct by easy; easy.
Qed.

Lemma red_move_iname_same {T M} n m (f : iname T M) V :
  move_iname n m f V n = get_iname m f V.
Proof.
  intros; unfold move_iname.
  rewrite red_insert_iname_same by easy; easy.
Qed.

Hint Rewrite @red_get_iname @red_with_iname_same
     @red_delete_iname_same @red_insert_iname_same
     @red_shift_name_same @red_unshift_name_same
     @red_shift_above_name_same @red_move_iname_same
  : red_inames.

Hint Rewrite @red_with_iname_eq @red_with_iname_neq
     @red_delete_iname_distinct @red_delete_iname_indistinct
     @red_insert_iname_distinct @red_insert_iname_indistinct
     @red_shift_name_distinct @red_shift_name_indistinct
     @red_unshift_name_distinct @red_unshift_name_indistinct
     @red_shift_above_name_distinct @red_shift_above_name_indistinct
     @red_move_iname_indistinct @red_move_iname_distinct1
     @red_move_iname_distinct2
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

Lemma iname_beta_project_neq_pointwise {T M} s t f (g : iname T M) :
  s <> t ->
  project_iname s (with_iname t f g) =km= project_iname s g.
Proof.
  intros Hneq V i; red_inames; easy.
Qed.

Definition iname_beta_project_neq {T M} s t f g :=
  fun V i Hneq =>
    eq_kmorph_expand
      (@iname_beta_project_neq_pointwise T M s t f g Hneq) V i.

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

Hint Rewrite @iname_beta_project_neq
  using (cbn; congruence) : simpl_inames_eqn.

Hint Rewrite @iname_beta_project_neq_pointwise
  using (cbn; congruence) : simpl_inames_pointwise_eqn.

(* Simple inversions of operational transforms *)

Lemma simpl_shift_shift_name_unshift_name n m :
  shift_name (shift_name n m) (unshift_name m n) = n.
Proof.
  case_string (n_string n) (n_string m); simpl_iindexs; easy.
Qed.

Lemma simpl_unshift_unshift_name_shift_name n m :
  unshift_name (unshift_name n m) (shift_name m n) = n.
Proof.
  case_string (n_string n) (n_string m); simpl_iindexs; easy.
Qed.

Lemma simpl_unshift_shift_above_name_shift_name n m :
  unshift_name (shift_above_name n m) (shift_name m n) = n.
Proof.
  case_string (n_string n) (n_string m); simpl_iindexs; easy.
Qed.

Lemma simpl_unshift_shift_name_shift_above_name n m :
  unshift_name (shift_name n m) (shift_above_name m n) = n.
Proof.
  case_string (n_string n) (n_string m); simpl_iindexs; easy.
Qed.

(* Unshift is right inverse of shift *)
Lemma simpl_shift_name_unshift_name n m :
  unshift_name n (shift_name n m) = m.
Proof.
  case_string (n_string m) (n_string n); simpl_iindexs; easy.
Qed.

(* Shift is left inverse of unshift if the indices aren't equal *)
Lemma simpl_unshift_name_shift_name n m :
  n <> m ->
  shift_name n (unshift_name n m) = m.
Proof.
  intros Hneq.
  case_string (n_string m) (n_string n); try easy.
  apply name_neq_string_eq_index_neq in Hneq; try easy.
  simpl_iindexs; easy.
Qed.

Hint Rewrite simpl_shift_shift_name_unshift_name
     simpl_unshift_unshift_name_shift_name
     simpl_unshift_shift_above_name_shift_name
     simpl_unshift_shift_name_shift_above_name
     simpl_shift_name_unshift_name name_eqb_refl
  : simpl_names.

Hint Rewrite simpl_unshift_name_shift_name
  using congruence : simpl_names.

Ltac simpl_names := autorewrite with simpl_names.

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
  insert_iname n a f
  = with_iname (n_string n)
      (insert_iindex (n_index n) a (project_iname (n_string n) f)) f.
Proof. easy. Qed.

Lemma unfold_move_iname {T M} n m (f : iname T M) :
  move_iname n m f
  = insert_iname n (get_iname m f) (delete_iname m f).
Proof. easy. Qed.

Hint Rewrite @unfold_get_iname @unfold_delete_iname
  @unfold_insert_iname @unfold_move_iname 
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
    (insert_iindex (n_index n) a (project_iname (n_string n) f)) f
  = insert_iname n a f.
Proof. easy. Qed.

Lemma fold_move_iname {T M} n m (f : iname T M) :
  insert_iname n (get_iname m f) (delete_iname m f)
  = move_iname n m f.
Proof. easy. Qed.

Hint Rewrite @fold_get_iname @fold_delete_iname
  @fold_insert_iname @fold_move_iname 
  : fold_inames.

(* Simplify [iname] terms by unfolding, simplifying and folding *)
Ltac simpl_inames :=
  autorewrite with unfold_inames;
  autorewrite with simpl_names simpl_inames;
  autorewrite with unfold_iindexs;
  autorewrite with simpl_indexs simpl_iindexs;
  repeat progress
    (cbn;
     try (rewrite_strat topdown (hints simpl_names));
     try (rewrite_strat topdown (hints simpl_inames));
     try (rewrite_strat topdown (hints simpl_indexs));
     try (rewrite_strat topdown (hints simpl_iindexs)));
  autorewrite with fold_iindexs fold_inames.

Ltac simpl_inames_eqn :=
  autorewrite with unfold_inames;
  autorewrite with simpl_names simpl_inames;
  autorewrite with unfold_iindexs;
  autorewrite with simpl_indexs simpl_iindexs;
  repeat progress
    (cbn;
     try (rewrite_strat topdown (hints simpl_names));
     try (rewrite_strat topdown (hints simpl_inames));
     try (rewrite_strat topdown (hints simpl_inames_eqn));
     try (rewrite_strat topdown (hints simpl_indexs));
     try (rewrite_strat topdown (hints simpl_iindexs));
     try (rewrite_strat topdown (hints simpl_iindexs_eqn)));
  autorewrite with fold_iindexs fold_inames.

Ltac simpl_inames_pointwise :=
  autorewrite with unfold_inames;
  autorewrite with simpl_names simpl_inames_pointwise;
  autorewrite with unfold_iindexs;
  autorewrite with simpl_indexs simpl_iindexs_pointwise;
  repeat progress
    (cbn;
     try (rewrite_strat topdown (hints simpl_names));
     try (rewrite_strat topdown (hints simpl_inames_pointwise));
     try (rewrite_strat topdown (hints simpl_indexs));
     try (rewrite_strat topdown (hints simpl_iindexs_pointwise)));
  autorewrite with fold_iindexs fold_inames.

Ltac simpl_inames_pointwise_eqn :=
  autorewrite with unfold_inames;
  autorewrite with simpl_names simpl_inames_pointwise;
  autorewrite with unfold_iindexs;
  autorewrite with simpl_indexs simpl_iindexs_pointwise;
  repeat progress
    (cbn;
     try (rewrite_strat topdown (hints simpl_names));
     try (rewrite_strat topdown (hints simpl_inames_pointwise));
     try (rewrite_strat topdown (hints simpl_inames_pointwise_eqn));
     try (rewrite_strat topdown (hints simpl_indexs));
     try (rewrite_strat topdown (hints simpl_iindexs_pointwise));
     try (rewrite_strat topdown (hints simpl_iindexs_pointwise_eqn)));
  autorewrite with fold_iindexs fold_inames.

Lemma project_id_iname {T N} (f : iindex T N) i :
  @morph_compose (knset index) 0 (knset index) 0 T N
     f (delete_iindex i id_iindex) =m= delete_iindex i f.
Proof.
  intros V j.
  case_order i j; easy.
Qed.

(* Useful lemmas about shifting *)

Lemma shift_name_neq n m :
  shift_name n m <> n.
Proof.
  pose shift_index_neq.
  case_string (n_string n) (n_string m); try congruence.
  destruct n, m; cbn in *; congruence.
Qed.

Lemma shift_above_name_neq_shift_name n m :
  shift_above_name n m <> shift_name m n.
Proof.
  pose shift_above_index_neq_shift_index.
  case_string (n_string n) (n_string m); congruence.
Qed.

(* Commuting [iname] operations *)

Lemma swap_with_iname_with_iname_pointwise {T M} s f t g
      (h : iname T M) :
  s <> t ->
  with_iname s f (with_iname t g h)
  =km= with_iname t g (with_iname s f h).
Proof.
  intros Hneq V n.
  case_string s (n_string n); try easy.
  case_string t (n_string n); easy.
Qed.

Definition swap_with_iname_with_iname {T M} s f t g h :=
  fun V n Heq =>
    eq_kmorph_expand
      (@swap_with_iname_with_iname_pointwise T M s f t g h Heq) V n.

Lemma swap_delete_iname_delete_iname_pointwise {T M} n m
      (f : iname T M) :
  delete_iname n (delete_iname m f)
  =km= delete_iname (unshift_name n m)
         (delete_iname (shift_name m n) f).
Proof.
  case_string (n_string n) (n_string m).
  - intros V o.
    case_string (n_string n) (n_string o); try easy.
    simpl_inames_pointwise_eqn.
    rewrite swap_delete_iindex_delete_iindex_pointwise; congruence.
  - unfold delete_iname.
    rewrite swap_with_iname_with_iname_pointwise by easy.
    simpl_inames_pointwise_eqn; easy.
Qed.

Definition swap_delete_iname_delete_iname {T M} n m f :=
  eq_kmorph_expand
    (@swap_delete_iname_delete_iname_pointwise T M n m f).

Lemma swap_insert_iname_insert_iname_pointwise {T M} n a m b
      (f : iname T M) :
  insert_iname n a (insert_iname m b f)
  =km= insert_iname (shift_name n m) b
      (insert_iname (unshift_name m n) a f).
Proof.
  case_string (n_string n) (n_string m).
  - intros V o.
    case_string (n_string n) (n_string o); try easy.
    simpl_inames_pointwise_eqn.
    rewrite swap_insert_iindex_insert_iindex; congruence.
  - unfold insert_iname.
    rewrite swap_with_iname_with_iname_pointwise by easy.
    simpl_inames_pointwise_eqn; easy.
Qed.

Definition swap_insert_iname_insert_iname {T M} n a m b f :=
  eq_kmorph_expand
    (@swap_insert_iname_insert_iname_pointwise T M n a m b f).

Lemma swap_delete_iname_insert_iname_pointwise {T M} n m a
      (f : iname T M) :
  n <> m ->
  delete_iname n (insert_iname m a f)
  =km= insert_iname (unshift_name n m) a
        (delete_iname (unshift_name m n) f).
Proof.
  intros Hneq.
  case_string (n_string n) (n_string m).
  - intros V o.
    case_string (n_string n) (n_string o); try easy.
    simpl_inames_pointwise_eqn.
    rewrite swap_delete_iindex_insert_iindex
      by auto using name_neq_string_eq_index_neq; congruence.
  - unfold delete_iname, insert_iname.
    rewrite swap_with_iname_with_iname_pointwise by easy.
    simpl_inames_pointwise_eqn; easy.
Qed.

Definition swap_delete_iname_insert_iname {T M} n m a f :=
  fun V o Heq =>
    eq_kmorph_expand
      (@swap_delete_iname_insert_iname_pointwise
         T M n m a f Heq) V o.

Lemma swap_insert_iname_delete_iname_pointwise {T M} n m a
      (f : iname T M) :
  insert_iname n a (delete_iname m f)
  =km= delete_iname (shift_above_name n m)
         (insert_iname (shift_name m n) a f).
Proof.
  case_string (n_string n) (n_string m).
  - intros V o.
    case_string (n_string n) (n_string o); try easy.
    simpl_inames_pointwise_eqn.
    rewrite swap_insert_iindex_delete_iindex; congruence.
  - unfold insert_iname, delete_iname.
    rewrite swap_with_iname_with_iname_pointwise by easy.
    simpl_inames_pointwise_eqn; easy.
Qed.

Definition swap_insert_iname_delete_iname {T M} n m a f :=
  eq_kmorph_expand
    (@swap_insert_iname_delete_iname_pointwise T M n m a f).

Lemma swap_get_iname_insert_iname_pointwise {T M} n m a
      (f : iname T M) :
  n <> m ->
  get_iname n (insert_iname m a f)
  =p= get_iname (unshift_name m n) f.
Proof.
  intros Hneq V; cbn.
  case_string (n_string n) (n_string m); try easy.
  apply name_neq_string_eq_index_neq in Hneq; try easy.
  case_order (n_index n) (n_index m); easy.
Qed.

Definition swap_get_iname_insert_iname {T M} n m a f :=
  fun V Hneq =>
    eq_pnset_expand
      (@swap_get_iname_insert_iname_pointwise T M n m a f Hneq) V.

Lemma swap_get_iname_delete_iname_pointwise {T M} n m
      (f : iname T M) :
  get_iname n (delete_iname m f)
  =p= get_iname (shift_name m n) f.
Proof.
  intros V; cbn.
  case_string (n_string n) (n_string m); try easy.
  case_order (n_index n) (n_index m); easy.
Qed.

Definition swap_get_iname_delete_iname {T M} n m f :=
  eq_pnset_expand
    (@swap_get_iname_delete_iname_pointwise T M n m f).

Lemma swap_insert_iname_move_iname_pointwise {T M} n a m o
      (f : iname T M) :
  insert_iname n a (move_iname m o f)
  =km= move_iname (shift_name n m)
                  (shift_above_name (unshift_name m n) o)
         (insert_iname (shift_name o (unshift_name m n)) a f).
Proof.
  unfold move_iname.
  rewrite swap_insert_iname_insert_iname_pointwise.
  rewrite swap_insert_iname_delete_iname_pointwise.
  rewrite swap_get_iname_insert_iname_pointwise
    by auto using shift_above_name_neq_shift_name.
  simpl_names; easy.
Qed.

Definition swap_insert_iname_move_iname {T M} n a m o f :=
  eq_kmorph_expand
    (@swap_insert_iname_move_iname_pointwise T M n a m o f).

Lemma swap_move_iname_insert_iname_pointwise {T M} n m o a
      (f : iname T M) :
  m <> o ->
  move_iname n m (insert_iname o a f)
  =km= insert_iname (shift_name n (unshift_name m o)) a
         (move_iname (unshift_name (unshift_name m o) n)
            (unshift_name o m) f).
Proof.
  intros; unfold move_iname.
  rewrite swap_delete_iname_insert_iname_pointwise by easy.
  rewrite swap_insert_iname_insert_iname_pointwise.
  rewrite swap_get_iname_insert_iname_pointwise by easy.
  easy.
Qed.

Definition swap_move_iname_insert_iname {T M} n m o a f :=
  fun V l Hneq =>
    eq_kmorph_expand
      (@swap_move_iname_insert_iname_pointwise T M n m o a f Hneq)
      V l.

Lemma swap_delete_iname_move_iname_pointwise {T M} n m o
      (f : iname T M) :
  n <> m ->
  delete_iname n (move_iname m o f)
  =km= move_iname
         (unshift_name n m) (unshift_name (unshift_name m n) o)
         (delete_iname (shift_name o (unshift_name m n)) f).
Proof.
  intros; unfold move_iname.
  rewrite swap_delete_iname_insert_iname_pointwise by easy.
  rewrite swap_delete_iname_delete_iname_pointwise.
  rewrite swap_get_iname_delete_iname_pointwise.
  simpl_names; easy.
Qed.

Definition swap_delete_iname_move_iname {T M} n m o f :=
  fun V l Hneq =>
    eq_kmorph_expand
      (@swap_delete_iname_move_iname_pointwise T M n m o f Hneq)
      V l.

Lemma swap_move_iname_delete_iname_pointwise {T M} n m o
      (f : iname T M) :
  move_iname n m (delete_iname o f)
  =km= delete_iname (shift_above_name n (unshift_name m o))
         (move_iname (shift_name (unshift_name m o) n)
            (shift_name o m) f).
Proof.
  intros; unfold move_iname.
  rewrite swap_delete_iname_delete_iname_pointwise.
  rewrite swap_get_iname_delete_iname_pointwise by easy.
  rewrite swap_insert_iname_delete_iname_pointwise by easy.
  easy.
Qed.

Definition swap_move_iname_delete_iname {T M} n m o f :=
  eq_kmorph_expand
    (@swap_move_iname_delete_iname_pointwise T M n m o f).

Lemma swap_get_iname_move_iname_pointwise {T M} n m o
      (f : iname T M) :
  n <> m ->
  get_iname n (move_iname m o f)
  =p= get_iname (shift_name o (unshift_name m n)) f.
Proof.
  intros; unfold move_iname.
  rewrite swap_get_iname_insert_iname_pointwise by easy.
  rewrite swap_get_iname_delete_iname_pointwise; easy.
Qed.

(* Commuting [name] operations *)

Lemma swap_shift_name_shift_name n m o :
  shift_name n (shift_name m o)
  = shift_name (shift_name n m)
      (shift_name (unshift_name m n) o).
Proof.
  case_string (n_string n) (n_string m).
  - case_string (n_string n) (n_string o); try easy.
    rewrite swap_shift_index_shift_index; easy.
  - case_string (n_string n) (n_string o); try easy.
    case_string (n_string m) (n_string o); easy.
Qed.

Lemma swap_shift_name_unshift_name n m o :
  shift_name n (unshift_name m o)
  = unshift_name (shift_name n m)
      (shift_name (shift_above_name m n) o).
Proof.
  case_string (n_string n) (n_string m).
  - case_string (n_string n) (n_string o); try easy.
    rewrite swap_shift_index_unshift_index; easy.
  - case_string (n_string n) (n_string o); try easy.
    case_string (n_string m) (n_string o); easy.
Qed.

Lemma swap_unshift_name_unshift_name n m o :
  unshift_name n (unshift_name m o)
  = unshift_name (unshift_name n m)
      (unshift_name (shift_name m n) o).
Proof.
  case_string (n_string n) (n_string m).
  - case_string (n_string n) (n_string o); try easy.
    rewrite swap_unshift_index_unshift_index; easy.
  - case_string (n_string n) (n_string o); try easy.
    case_string (n_string m) (n_string o); easy.
Qed.

Lemma swap_unshift_name_shift_name n m o :
  m <> n ->
  shift_name m o <> n ->
  unshift_name n (shift_name m o) =
  shift_name (unshift_name n m)
    (unshift_name (unshift_name m n) o).
Proof.
  intros Hn1 Hn2.
  case_string (n_string n) (n_string m).
  - apply name_neq_string_eq_index_neq in Hn1; try easy.
    case_string (n_string n) (n_string o); try easy.
    apply name_neq_string_eq_index_neq in Hn2;
      red_inames; try easy.
    rewrite swap_unshift_index_shift_index; try easy.
    replace (shift_index (n_index m) (n_index o))
      with (n_index (shift_name m o))
      by (red_inames; easy).
    easy.
  - case_string (n_string n) (n_string o); try easy.
    case_string (n_string m) (n_string o); easy.
Qed.

(* There is a full covariant functor from [T O] to [iname N T O]
   by composition.

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
  g @ (insert_iname n a f)
  =km= insert_iname n (morph_apply g a) (g @ f).
Proof.
  unfold insert_iname.
  rewrite with_iname_compose_distribute.
  rewrite insert_iindex_compose_distribute.
  rewrite project_iname_compose_distribute.
  easy.
Qed.

Lemma move_iname_compose_distribute {T M R L} n m
      (f : iname T M) (g : morph T M R L) :
  g @ (move_iname n m f) =km= move_iname n m (g @ f).
Proof.
  unfold move_iname.
  rewrite insert_iname_compose_distribute.
  rewrite get_iname_compose_distribute.
  rewrite delete_iname_compose_distribute.
  easy.
Qed.
