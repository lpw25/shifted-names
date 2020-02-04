Require Import String Omega Morph Setoid Morphisms.
Arguments string_dec !s1 !s2.

(* Name indices are [nat]s *)
Definition index := nat.

(* Boolean equality function *)
Definition index_eqb := Nat.eqb.

Lemma index_eqb_eq i j :
  index_eqb i j = true <-> i = j.
Proof. apply Nat.eqb_eq. Qed.

(* Liftable functions from [index]s to nsets that we treat
   like streams *)
Definition iindex (T : nset) M := kmorph index T M.

Definition get_iindex {T M} (i : index) (f : iindex T M)
  : pnset T M :=
  fun V => f V i.
Arguments get_iindex {T M} i f V /.

Definition delete_iindex {T M} (i : index) (f : iindex T M) :
  iindex T M :=
  fun V (j : index) =>
    if Compare_dec.le_lt_dec i j then get_iindex (S j) f V
    else get_iindex j f V.

Definition insert_iindex {T M} (i : index)
           (a : pnset T M) (f : iindex T M)
  : iindex T M :=
  fun V (j : index) =>
    match Compare_dec.lt_eq_lt_dec i j with
    | inleft (left _) => get_iindex (pred j) f V
    | inleft (right _) => a V
    | inright _ => get_iindex j f V
    end.

(* Derived operations *)

Definition move_iindex {T M} i j (f : iindex T M) :=
  insert_iindex i (get_iindex j f) (delete_iindex j f).

(* Morphism definitions *)

Add Parametric Morphism {T M} : (@get_iindex T M)
    with signature eq ==> eq_kmorph ==> eq_pnset
      as get_iindex_mor.
  intros * Heq * V; cbn.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {T M} : (@delete_iindex T M)
    with signature eq ==> eq_kmorph ==> eq_kmorph
    as delete_iindex_mor.
  intros * Heq V j; unfold delete_iindex; cbn.
  rewrite Heq, Heq; easy.
Qed.

Add Parametric Morphism {T M} : (@insert_iindex T M)
    with signature eq ==> eq_pnset ==> eq_kmorph ==> eq_kmorph
      as insert_iindex_mor.
  intros * Heq1 * Heq2 V j; unfold insert_iindex; cbn.
  rewrite Heq1, Heq2, Heq2; easy.
Qed.

Add Parametric Morphism {T M} i j : (@move_iindex T M i j)
    with signature eq_kmorph ==> eq_kmorph
      as move_iindex_mor.
  intros * Heq V k; unfold move_iindex.
  rewrite Heq; easy.
Qed.

(* The identity [iindex] *)

Definition id_iindex : iindex (knset index) 0 :=
  fun _ (j : index) => j.
Arguments id_iindex V j /.

(* Operational transforms

   Using the (somewhat dubious) notation of the operational
   transforms literature, we define IT and ET for our
   operations as:

     IT(insert n, insert m) = insert (shift m n)
     IT(insert n, delete m) = insert (unshift m n)
     IT(delete n, insert m) = delete (shift m n)
     IT(delete n, delete m) = delete (unshift m n)

     ET(insert n, insert m) = insert (unshift m n)
     ET(insert n, delete m) = insert (shift m n)
     ET(delete n, insert m) = delete (unshift m n)
     ET(delete n, delete m) = delete (shift m n)

   from which we can define an additional transfrom

     XT(o1, o2) := IT(o1, ET(o2, o1))

   that expands out to:

     XT(insert n, insert m) = insert (shift m n)
     XT(insert n, delete m) = insert (unshift m n)
     XT(delete n, insert m) = delete (shift_above m n)
     XT(delete n, delete m) = delete (unshift m n)

   With these definitions we have:

     o1 (o2 f)
     = XT(o2, o1) (ET(o1, o2) f)

   and

     o1 (o2 (o3 f))
     = XT(o2, o1) (XT(o3, ET(o1, o2)) (ET(ET(o1, o2), o3) f))
     = XT(XT(o3, o2), o1) (ET(o1, XT(o3, o2)) (ET(o2, o3) f))

   which allows us to commute our operations and derived operations.
*)

Definition shift_index (i : index) : index -> index :=
  delete_iindex i id_iindex 0.

Definition unshift_index (i : index) : index -> index :=
  insert_iindex i (fun V => i) id_iindex 0.

Definition shift_above_index (i : index) : index -> index :=
  shift_index (S i).

(* Reductions *)

Lemma red_delete_iindex_ge {T M} i (f : iindex T M) V j :
  i <= j ->
  delete_iindex i f V j = f V (S j).
Proof.
  intros; unfold delete_iindex.
  destruct (le_lt_dec i j); try easy; omega.
Qed.

Lemma red_delete_iindex_lt {T M} i (f : iindex T M) V j :
  S j <= i ->
  delete_iindex i f V j = f V j.
Proof.
  intros; unfold delete_iindex.
  destruct (le_lt_dec i j); try easy; omega.
Qed.

Lemma red_delete_iindex_same {T M} i (f : iindex T M) V :
  delete_iindex i f V i = f V (S i).
Proof.
  apply red_delete_iindex_ge; auto.
Qed.

Lemma red_insert_iindex_gt {T M} i a (f : iindex T M) V j :
  S i <= j ->
  insert_iindex i a f V j = f V (pred j).
Proof.
  intros; unfold insert_iindex.
  destruct (lt_eq_lt_dec i j) as [[|]|]; try easy; omega.
Qed.

Lemma red_insert_iindex_eq {T M} i a (f : iindex T M) V j :
  i = j ->
  insert_iindex i a f V j = a V.
Proof.
  intros; unfold insert_iindex.
  destruct (lt_eq_lt_dec i j) as [[|]|]; try easy; omega.
Qed.

Lemma red_insert_iindex_lt {T M} i a (f : iindex T M) V j :
  S j <= i ->
  insert_iindex i a f V j = f V j.
Proof.
  intros; unfold insert_iindex.
  destruct (lt_eq_lt_dec i j) as [[|]|]; try easy; omega.
Qed.

Lemma red_insert_iindex_same {T M} i a (f : iindex T M) V :
  insert_iindex i a f V i = a V.
Proof.
  apply red_insert_iindex_eq; auto.
Qed.

Lemma red_shift_index_ge i j :
  i <= j ->
  shift_index i j = S j.
Proof.
  intros; unfold shift_index.
  rewrite red_delete_iindex_ge by easy; easy.
Qed.

Lemma red_shift_index_lt i j :
  S j <= i ->
  shift_index i j = j.
Proof.
  intros; unfold shift_index.
  rewrite red_delete_iindex_lt by easy; easy.
Qed.

Lemma red_shift_index_same i :
  shift_index i i = S i.
Proof.
  apply red_shift_index_ge; omega.
Qed.

Lemma red_unshift_index_gt i j :
  S i <= j ->
  unshift_index i j = pred j.
Proof.
  intros; unfold unshift_index.
  rewrite red_insert_iindex_gt by easy; easy.
Qed.

Lemma red_unshift_index_le i j :
  j <= i ->
  unshift_index i j = j.
Proof.
  intros Hle; unfold unshift_index.
  destruct (le_lt_eq_dec j i Hle).
  - rewrite red_insert_iindex_lt by easy; easy.
  - rewrite red_insert_iindex_eq by easy; easy.
Qed.

Lemma red_unshift_index_same i :
  unshift_index i i = i.
Proof.
  apply red_unshift_index_le; omega.
Qed.

Lemma red_shift_above_index_gt i j :
  S i <= j ->
  shift_above_index i j = S j.
Proof.
  intros; unfold shift_above_index.
  rewrite red_shift_index_ge by easy; easy.
Qed.

Lemma red_shift_above_index_le i j :
  j <= i ->
  shift_above_index i j = j.
Proof.
  intros; unfold shift_above_index.
  rewrite red_shift_index_lt by omega; easy.
Qed.

Lemma red_shift_above_index_same i :
  shift_above_index i i = i.
Proof.
  apply red_shift_above_index_le; omega.
Qed.

Lemma red_move_iindex_eq {T M} i j (f : iindex T M) V k :
  i = k ->
  move_iindex i j f V k = get_iindex j f V.
Proof.
  intros; unfold move_iindex.
  rewrite red_insert_iindex_eq by easy; easy.
Qed.

Lemma red_move_iindex_neq {T M} i j (f : iindex T M) V k :
  i <> k ->
  move_iindex i j f V k = delete_iindex j f V (unshift_index i k).
Proof.
  intros; unfold move_iindex.
  destruct (lt_eq_lt_dec i k) as [[|]|]; try omega.
  - rewrite red_insert_iindex_gt by easy.
    rewrite red_unshift_index_gt by easy.
    easy.
  - rewrite red_insert_iindex_lt by easy.
    rewrite red_unshift_index_le by omega.
    easy.
Qed.

Lemma red_move_iindex_same {T M} i j (f : iindex T M) V :
  move_iindex i j f V i = get_iindex j f V.
Proof.
  intros; unfold move_iindex.
  rewrite red_insert_iindex_same by easy; easy.
Qed.

(* Useful lemma about predecessor and successor *)
Lemma red_succ_pred i :
  0 < i ->
  S (pred i) = i.
Proof.
  intros; omega.
Qed.

Hint Rewrite @red_delete_iindex_same @red_insert_iindex_same
     @red_move_iindex_same @red_shift_index_same
     @red_unshift_index_same @red_shift_above_index_same
  : red_iindexs.

Hint Rewrite @red_delete_iindex_ge @red_delete_iindex_lt
     @red_insert_iindex_gt @red_insert_iindex_eq
     @red_insert_iindex_lt @red_move_iindex_eq @red_move_iindex_neq
     @red_shift_index_ge @red_shift_index_lt @red_unshift_index_le
     @red_unshift_index_gt @red_shift_above_index_le
     @red_shift_above_index_gt @red_succ_pred
     using omega : red_iindexs.

(* Rewrite operations using reductions *)
Ltac red_iindexs :=
  repeat progress
    (try (rewrite_strat topdown (hints red_iindexs)); cbn).

(* Case split on the order of the parameters. *)
Ltac case_order i j :=
  destruct (Compare_dec.lt_eq_lt_dec i j) as [[|]|];
    red_iindexs; [> | replace j with i by easy |]; try omega.

(* Beta and eta rules for [iindex] operations *)

Lemma iindex_beta_get_eq_pointwise {T M} i j a (f : iindex T M) :
  i = j ->
  get_iindex i (insert_iindex j a f) =p= a.
Proof.
  intros Heq V; red_iindexs; easy.
Qed.

Definition iindex_beta_get_eq {T M} i j a f :=
  fun V Heq =>
    eq_pnset_expand (@iindex_beta_get_eq_pointwise T M i j a f Heq) V.

Lemma iindex_beta_get_pointwise {T M} i a (f : iindex T M) :
  get_iindex i (insert_iindex i a f) =p= a.
Proof. apply iindex_beta_get_eq_pointwise; easy. Qed.

Definition iindex_beta_get {T M} i a f :=
  eq_pnset_expand (@iindex_beta_get_pointwise T M i a f).

Lemma iindex_beta_delete_eq_pointwise {T M} i j a (f : iindex T M) :
  i = j ->
  delete_iindex i (insert_iindex j a f) =km= f.
Proof.
  intros Heq V k.
  case_order i k; easy.
Qed.

Definition iindex_beta_delete_eq {T M} i j a f :=
  fun V Heq =>
    eq_kmorph_expand
      (@iindex_beta_delete_eq_pointwise T M i j a f Heq) V.

Lemma iindex_beta_delete_pointwise {T M} i a (f : iindex T M) :
  delete_iindex i (insert_iindex i a f) =km= f.
Proof. apply iindex_beta_delete_eq_pointwise; easy. Qed.

Definition iindex_beta_delete {T M} i a f :=
  eq_kmorph_expand (@iindex_beta_delete_pointwise T M i a f).

Lemma iindex_eta_eq_pointwise {T M} i j k (f : iindex T M) :
  i = j ->
  i = k ->
  insert_iindex i (get_iindex j f) (delete_iindex k f) =km= f.
Proof.
  intros Heq1 Heq2 V l.
  case_order i l; f_equal; easy.
Qed.

Definition iindex_eta_eq {T M} i j k f :=
  fun V Heq1 Heq2 =>
    eq_kmorph_expand
      (@iindex_eta_eq_pointwise T M i j k f Heq1 Heq2) V.

Lemma iindex_eta_pointwise {T M} i (f : iindex T M) :
  insert_iindex i (get_iindex i f) (delete_iindex i f) =km= f.
Proof. apply iindex_eta_eq_pointwise; easy. Qed.

Definition iindex_eta {T M} i f :=
  eq_kmorph_expand (@iindex_eta_pointwise T M i f).

Hint Rewrite @iindex_beta_get @iindex_beta_delete @iindex_eta
  : simpl_iindexs.

Hint Rewrite @iindex_beta_get_eq @iindex_beta_delete_eq @iindex_eta_eq
  using omega : simpl_iindexs_eqn.

Hint Rewrite @iindex_beta_get_pointwise
     @iindex_beta_delete_pointwise @iindex_eta_pointwise
  : simpl_iindexs_pointwise.

Hint Rewrite @iindex_beta_get_eq_pointwise
     @iindex_beta_delete_eq_pointwise
     @iindex_eta_eq_pointwise
  using omega : simpl_iindexs_pointwise_eqn.

(* Simple inversions of operational transforms:

     XT(ET(o1, o2), XT(o2, o1)) = o1

     ET(XT(o2, o1), ET(o1, o2)) = o2

   We leave out the case where o1 is delete and o2 is insert because it
   is harder to express as just shifts and we don't seem to need it
   for anything.
*)

Lemma simpl_shift_shift_index_unshift_index i j :
  shift_index (shift_index i j) (unshift_index j i) = i.
Proof. case_order i j. Qed.

Lemma simpl_unshift_unshift_index_shift_index i j :
  unshift_index (unshift_index i j) (shift_index j i) = i.
Proof. case_order i j. Qed.

Lemma simpl_unshift_shift_above_index_shift_index i j :
  unshift_index (shift_above_index i j) (shift_index j i) = i.
Proof. case_order i j. Qed.

Lemma simpl_unshift_shift_index_shift_above_index i j :
  unshift_index (shift_index i j) (shift_above_index j i) = i.
Proof. case_order i j. Qed.

Hint Rewrite simpl_shift_shift_index_unshift_index
     simpl_unshift_unshift_index_shift_index
     simpl_unshift_shift_above_index_shift_index
     simpl_unshift_shift_index_shift_above_index
  : simpl_indexs.

(* Unfolding derived operations *)

Lemma unfold_move_iindex {T M} i j (f : iindex T M) :
  move_iindex i j f =
  insert_iindex i (get_iindex j f) (delete_iindex j f).
Proof. easy. Qed.

Hint Rewrite @unfold_move_iindex : unfold_iindexs.

(* Folding derived operations *)

Lemma fold_move_iindex {T M} i j (f : iindex T M) :
  insert_iindex i (get_iindex j f) (delete_iindex j f)
  = move_iindex i j f.
Proof. easy. Qed.

Hint Rewrite @fold_move_iindex : fold_iindexs. 

(* Simplify [iindex] terms by unfolding, simplifying and folding *)
Ltac simpl_iindexs :=
  autorewrite with unfold_iindexs;
  autorewrite with simpl_indexs simpl_iindexs;
  repeat progress
    (cbn;
     try (rewrite_strat topdown (hints simpl_indexs));
     try (rewrite_strat topdown (hints simpl_iindexs)));
  autorewrite with fold_iindexs.

Ltac simpl_iindexs_eqn :=
  autorewrite with unfold_iindexs;
  autorewrite with simpl_indexs simpl_iindexs;
  repeat progress
    (cbn;
     try (rewrite_strat topdown (hints simpl_indexs));
     try (rewrite_strat topdown (hints simpl_iindexs));
     try (rewrite_strat topdown (hints simpl_iindexs_eqn)));
  autorewrite with fold_iindexs.

Ltac simpl_iindexs_pointwise :=
  autorewrite with unfold_iindexs;
  autorewrite with simpl_indexs simpl_iindexs_pointwise;
  repeat progress
    (cbn;
     try (rewrite_strat topdown (hints simpl_indexs));
     try (rewrite_strat topdown (hints simpl_iindexs_pointwise)));
  autorewrite with fold_iindexs.

Ltac simpl_iindexs_pointwise_eqn :=
  autorewrite with unfold_iindexs;
  autorewrite with simpl_indexs simpl_iindexs_pointwise;
  repeat progress
    (cbn;
     try (rewrite_strat topdown (hints simpl_indexs));
     try (rewrite_strat topdown (hints simpl_iindexs_pointwise));
     try (rewrite_strat topdown (hints simpl_iindexs_pointwise_eqn)));
  autorewrite with fold_iindexs.

(* Useful lemmas about shifting *)

Lemma shift_index_neq i j :
  shift_index i j <> i.
Proof.
  case_order i j; omega.
Qed.

Lemma shift_above_index_neq_shift_index i j :
  shift_above_index i j <> shift_index j i.
Proof.
  case_order i j; omega.
Qed.

(* Commuting [iindex] operations *)

Lemma swap_delete_iindex_delete_iindex_pointwise {T M} i j
      (f : iindex T M) :
  delete_iindex i (delete_iindex j f)
  =km= delete_iindex (unshift_index i j)
        (delete_iindex (shift_index j i) f).
Proof.
  intros V k.
  case_order i j;
    case_order j k; try easy;
      case_order i k; try easy;
        case_order (S k) j; try easy.
Qed.

Definition swap_delete_iindex_delete_iindex {T M} i j f :=
  eq_kmorph_expand
    (@swap_delete_iindex_delete_iindex_pointwise T M i j f).

Lemma swap_insert_iindex_insert_iindex_pointwise {T M} i a j b
      (f : iindex T M) :
  insert_iindex i a (insert_iindex j b f)
  =km= insert_iindex (shift_index i j) b
         (insert_iindex (unshift_index j i) a f).
Proof.
  intros V k.
  case_order i j;
    case_order j k; try easy;
      case_order i k; try easy;
        case_order j (pred k); try easy.
Qed.

Definition swap_insert_iindex_insert_iindex {T M} i a j b f :=
  eq_kmorph_expand
    (@swap_insert_iindex_insert_iindex_pointwise T M i a j b f).

Lemma swap_delete_iindex_insert_iindex_pointwise {T M} i j a
      (f : iindex T M) :
  i <> j ->
  delete_iindex i (insert_iindex j a f)
  =km= insert_iindex (unshift_index i j) a
         (delete_iindex (unshift_index j i) f).
Proof.
  intros Hneq V k.
  case_order i j; try contradiction;
    case_order i k; try easy;
      case_order j k; try easy;
        case_order j (S k); easy.
Qed.

Definition swap_delete_iindex_insert_iindex {T M} i j a f :=
  fun V k Heq =>
    eq_kmorph_expand
      (@swap_delete_iindex_insert_iindex_pointwise T M i j a f Heq) V k.

Lemma swap_insert_iindex_delete_iindex_pointwise {T M} i j a
      (f : iindex T M) :
  insert_iindex i a (delete_iindex j f)
  =km= delete_iindex (shift_above_index i j)
         (insert_iindex (shift_index j i) a f).
Proof.
  intros V k.
  case_order i j;
    case_order i k; try easy;
      case_order j k; try easy.
Qed.

Definition swap_insert_iindex_delete_iindex {T M} i j a f :=
  eq_kmorph_expand
    (@swap_insert_iindex_delete_iindex_pointwise T M i j a f).

Lemma swap_get_iindex_insert_iindex_pointwise {T M} i j a
      (f : iindex T M) :
  i <> j ->
  get_iindex i (insert_iindex j a f)
  =p= get_iindex (unshift_index j i) f.
Proof.
  intros Hneq V; cbn.
  case_order j i; easy.
Qed.

Definition swap_get_iindex_insert_iindex {T M} i j a f :=
  fun V Hneq =>
    eq_pnset_expand
      (@swap_get_iindex_insert_iindex_pointwise T M i j a f Hneq) V.

Lemma swap_get_iindex_delete_iindex_pointwise {T M} i j
      (f : iindex T M) :
  get_iindex i (delete_iindex j f)
  =p= get_iindex (shift_index j i) f.
Proof.
  intros V; cbn.
  case_order j i; easy.
Qed.

Definition swap_get_iindex_delete_iindex {T M} i j f :=
  eq_pnset_expand
    (@swap_get_iindex_delete_iindex_pointwise T M i j f).

Lemma swap_insert_iindex_move_iindex_pointwise {T M} i a j k
      (f : iindex T M) :
  insert_iindex i a (move_iindex j k f)
  =km= move_iindex
         (shift_index i j) (shift_above_index (unshift_index j i) k)
         (insert_iindex (shift_index k (unshift_index j i)) a f).
Proof.
  unfold move_iindex.
  rewrite swap_insert_iindex_insert_iindex_pointwise.
  rewrite swap_insert_iindex_delete_iindex_pointwise.
  rewrite swap_get_iindex_insert_iindex_pointwise
    by auto using shift_above_index_neq_shift_index.
  simpl_iindexs; easy.
Qed.

Definition swap_insert_iindex_move_iindex {T M} i a j k f :=
  eq_kmorph_expand
    (@swap_insert_iindex_move_iindex_pointwise T M i a j k f).

Lemma swap_move_iindex_insert_iindex_pointwise {T M} i j k a
      (f : iindex T M) :
  j <> k ->
  move_iindex i j (insert_iindex k a f)
  =km= insert_iindex (shift_index i (unshift_index j k)) a
         (move_iindex (unshift_index (unshift_index j k) i)
            (unshift_index k j) f).
Proof.
  intros; unfold move_iindex.
  rewrite swap_delete_iindex_insert_iindex_pointwise by easy.
  rewrite swap_insert_iindex_insert_iindex_pointwise.
  rewrite swap_get_iindex_insert_iindex_pointwise by easy.
  easy.
Qed.

Definition swap_move_iindex_insert_iindex {T M} i j k a f :=
  fun V l Hneq =>
    eq_kmorph_expand
      (@swap_move_iindex_insert_iindex_pointwise
         T M i j k a f Hneq)
      V l.

Lemma swap_delete_iindex_move_iindex_pointwise {T M} i j k
      (f : iindex T M) :
  i <> j ->
  delete_iindex i (move_iindex j k f)
  =km= move_iindex
         (unshift_index i j) (unshift_index (unshift_index j i) k)
         (delete_iindex (shift_index k (unshift_index j i)) f).
Proof.
  intros; unfold move_iindex.
  rewrite swap_delete_iindex_insert_iindex_pointwise by easy.
  rewrite swap_delete_iindex_delete_iindex_pointwise.
  rewrite swap_get_iindex_delete_iindex_pointwise.
  simpl_iindexs; easy.
Qed.

Definition swap_delete_iindex_move_iindex {T M} i j k f :=
  fun V l Hneq =>
    eq_kmorph_expand
      (@swap_delete_iindex_move_iindex_pointwise T M i j k f Hneq)
      V l.

Lemma swap_move_iindex_delete_iindex_pointwise {T M} i j k
      (f : iindex T M) :
  move_iindex i j (delete_iindex k f)
  =km= delete_iindex (shift_above_index i (unshift_index j k))
         (move_iindex
            (shift_index (unshift_index j k) i)
            (shift_index k j) f).
Proof.
  intros; unfold move_iindex.
  rewrite swap_delete_iindex_delete_iindex_pointwise.
  rewrite swap_get_iindex_delete_iindex_pointwise by easy.
  rewrite swap_insert_iindex_delete_iindex_pointwise by easy.
  easy.
Qed.

Definition swap_move_iindex_delete_iindex {T M} i j k f :=
  eq_kmorph_expand
    (@swap_move_iindex_delete_iindex_pointwise T M i j k f).

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
  insert_iname n (fun V => n) id_iname 0.

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

Hint Rewrite simpl_shift_shift_name_unshift_name
     simpl_unshift_unshift_name_shift_name
     simpl_unshift_shift_above_name_shift_name
     simpl_unshift_shift_name_shift_above_name
  : simpl_names.

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

Definition transpose_ilevel {N T M} (f : ilevel (S (S N)) T M) :=
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

Add Parametric Morphism {N T M} : (@transpose_ilevel N T M)
    with signature eq_morph ==> eq_morph
    as transpose_ilevel_mor.
  intros * Heq V l; unfold transpose_ilevel.
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

Lemma ilevel_eta_pointwise {N T M} (f : ilevel (S N) T M) :
  cons_ilevel (hd_ilevel f) (tl_ilevel f) =m= f.
Proof.
  intros V l.
  destruct l; cbn; easy.
Qed.

Definition ilevel_eta {N T M} f :=
  eq_morph_expand (@ilevel_eta_pointwise N T M f).

Hint Rewrite @ilevel_beta_hd @ilevel_beta_tl @ilevel_eta
  : simpl_ilevels.

Hint Rewrite @ilevel_beta_hd @ilevel_beta_tl @ilevel_eta_pointwise
  : simpl_ilevels_pointwise.

(* Unfolding derived operations *)

Lemma unfold_transpose_ilevel {N T M} (f : ilevel (S (S N)) T M) :
  transpose_ilevel f
  = cons_ilevel (hd_ilevel (tl_ilevel f))
      (cons_ilevel (hd_ilevel f)
        (tl_ilevel (tl_ilevel f))).
Proof. easy. Qed.

Hint Rewrite @unfold_transpose_ilevel
  : unfold_ilevels.

(* Folding derived operations *)

Lemma fold_transpose_ilevel {N T M} (f : ilevel (S (S N)) T M) :
  cons_ilevel (hd_ilevel (tl_ilevel f))
      (cons_ilevel (hd_ilevel f)
        (tl_ilevel (tl_ilevel f)))
      = transpose_ilevel f.
Proof. easy. Qed.

Hint Rewrite @fold_get_iname
  : fold_inames.

(* Simplify [ilevel] terms by unfolding, simplifying and folding *)
Ltac simpl_ilevels :=
  autorewrite with unfold_ilevels;
  autorewrite with simpl_ilevels;
  repeat progress
    (cbn;
     try (rewrite_strat topdown (hints simpl_ilevels)));
  autorewrite with fold_ilevels.

Ltac simpl_ilevels_pointwise :=
  autorewrite with unfold_ilevels;
  autorewrite with simpl_ilevels_pointwise;
  repeat progress
    (cbn;
     try (rewrite_strat topdown (hints simpl_ilevels_pointwise)));
  autorewrite with fold_ilevels.

(* Variables are either free names or bound levels *)

Inductive var (V : nat) :=
| free (n : name)
| bound (l : level V).

Arguments free {V} n.
Arguments bound {V} l.

(* Liftable morphisms from [var]s that we treat like pairs *)
Definition ivar N T M := morph var N T M.

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

(* TODO: Find modular way to prove these *)

Lemma open_ivar_as_composition {N T M} n (f : ivar N T M) :
  open_ivar n f =m= f @ (morph_extend_by N (open_var n)).
Proof.
  intros V v.
  destruct v as [m|l]; cbn.
  - case_string (n_string n) (n_string m); try easy.
    case_order (n_index n) (n_index m); easy.
  - destruct l; easy.
Qed.

Lemma close_ivar_as_composition {N T M} n (f : ivar (S N) T M) :
  close_ivar n f =m=
  f @ (morph_extend_by N (close_var n)).
Proof.
  intros V v.
  destruct v as [m|l]; cbn; try easy.
  case_string (n_string n) (n_string m); try easy.
  case_order (n_index n) (n_index m); easy.
Qed.

Lemma weak_ivar_as_composition {N T M} (f : ivar (S N) T M) :
  weak_ivar f =m= f @ (morph_extend_by N weak_var).
Proof.
  intros V v.
  destruct v as [n|l]; easy.
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
  intros V v.
  unfold shift_var, shift_ivar.
  rewrite morph_extend_by_compose,
    open_ivar_as_composition, weak_ivar_as_composition.
  easy.
Qed.

(* There is a full covariant functor from [T O] to [ivar N T O]
   by composition.

   Such composition distributes over our operations. *)

Lemma open_ivar_compose_distribute {N T M R L} n
      (f : ivar N T M) (g : morph T M R L) :
  g @ (open_ivar n f) =m= open_ivar n (g @ f).
Proof.
  rewrite open_ivar_as_composition.
  rewrite morph_associative.
  rewrite <- open_ivar_as_composition.
  easy.
Qed.

Lemma close_ivar_compose_distribute {N T M R L} n
      (f : ivar (S N) T M) (g : morph T M R L) :
  g @ (close_ivar n f) =m= close_ivar n (g @ f).
Proof.
  rewrite close_ivar_as_composition.
  rewrite morph_associative.
  rewrite <- close_ivar_as_composition.
  easy.
Qed.

Lemma weak_ivar_compose_distribute {N T M R L}
      (f : ivar (S N) T M) (g : morph T M R L) :
  g @ (weak_ivar f) =m= weak_ivar (g @ f).
Proof.
  rewrite weak_ivar_as_composition.
  rewrite morph_associative.
  rewrite <- weak_ivar_as_composition.
  easy.
Qed.

Lemma bind_ivar_compose_distribute {N T M R L} t
      (f : ivar N T M) (g : morph T M R L) :
  g @ (bind_ivar t f)
  =m= bind_ivar (morph_apply g t) (g @ f).
Proof.
  intros V v.
  destruct v as [m|l]; cbn.
  - easy.
  - destruct l; easy.
Qed.

Lemma rename_ivar_compose_distribute {N T M R L} n m
      (f : ivar N T M) (g : morph T M R L) :
  g @ (rename_ivar n m f) =m= rename_ivar n m (g @ f).
Proof.
  rewrite rename_ivar_as_composition.
  rewrite morph_associative.
  rewrite <- rename_ivar_as_composition.
  easy.
Qed.

Lemma shift_ivar_compose_distribute {N T M R L} n
      (f : ivar N T M) (g : morph T M R L) :
  g @ (shift_ivar n f) =m= shift_ivar n (g @ f).
Proof.
  rewrite shift_ivar_as_composition.
  rewrite morph_associative.
  rewrite <- shift_ivar_as_composition.
  easy.
Qed.

Lemma subst_ivar_compose_distribute {N T M R L} n t
      (f : ivar N T M) (g : morph T M R L) :
  g @ (subst_ivar n t f)
  =m= subst_ivar n (morph_apply g t) (g @ f).
Proof.
  intros V v.
  unfold subst_ivar.
  rewrite close_ivar_compose_distribute,
    bind_ivar_compose_distribute.
  easy.
Qed.
