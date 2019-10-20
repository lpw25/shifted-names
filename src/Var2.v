Require Import String Omega Morph Setoid Morphisms.
Arguments string_dec !s1 !s2.

(* Pointwise equality for liftable functions to nsets *)
Definition eq_morph {S N T M} (f g : morph S N T M) :=
  forall_relation
     (fun V => pointwise_relation (S (N + V)) (@eq (T (M + V))))
     f g.

Notation "f =m= g" := (eq_morph f g) (at level 70).

Definition eq_morph_expand {S N T M} {f g : morph S N T M}
           (eq : eq_morph f g) :
  forall (V : nat) (s : S (N + V)), f V s = g V s := eq.

Definition kmorph (T : Set) (S : nset) (M : nat) :=
  forall V : nat, T -> S (M + V).

Definition eq_kmorph {S T M} (f g : kmorph S T M) :=
  forall_relation
     (fun V => pointwise_relation S (@eq (T (M + V))))
     f g.

Notation "f =km= g" := (eq_kmorph f g) (at level 70).

Definition eq_kmorph_expand {S T M} {f g : kmorph S T M}
           (eq : eq_kmorph f g) :
  forall (V : nat) (s : S), f V s = g V s := eq.

Definition pnset (T : nset) (M : nat) :=
  forall V : nat, T (M + V).

Definition eq_pnset {T M} (f g : pnset T M) :=
  forall_relation (fun V => (@eq (T (M + V)))) f g.

Notation "f =p= g" := (eq_pnset f g) (at level 70).

Definition eq_pnset_expand {T M} {f g : pnset T M}
           (eq : eq_pnset f g) :
  forall (V : nat), f V = g V := eq.

Instance eq_morph_equiv {S N T M} :
  Equivalence (@eq_morph S N T M).
Proof.
  apply Build_Equivalence; try easy.
  intros f g h Heq1 Heq2 V s.
  rewrite Heq1, Heq2; easy.
Qed.

Instance eq_kmorph_equiv {S T M} :
  Equivalence (@eq_kmorph S T M).
Proof.
  apply Build_Equivalence; try easy.
  intros f g h Heq1 Heq2 V s.
  rewrite Heq1, Heq2; easy.
Qed.

Instance eq_pnset_equiv {T M} :
  Equivalence (@eq_pnset T M).
Proof.
  apply Build_Equivalence; try easy.
  intros f g h Heq1 Heq2 V.
  rewrite Heq1, Heq2; easy.
Qed.

Instance eq_morph_eta {S N T M } :
  subrelation (@eq_morph S N T M)
    (forall_relation (fun V => respectful eq eq)) | 2.
Proof.
  intros f g Heq1 V s1 s2 Heq2.
  rewrite Heq1, Heq2; easy.
Qed.

Instance eq_kmorph_eta {S T M } :
  subrelation (@eq_kmorph S T M)
    (forall_relation (fun V => respectful eq eq)) | 2.
Proof.
  intros f g Heq1 V s1 s2 Heq2.
  rewrite Heq1, Heq2; easy.
Qed.

(* Name indices are [nat]s *)
Definition index := nat.

(* Liftable functions from [index]s to nsets that we treat
   like streams *)
Definition iindex (T : nset) M := kmorph index T M.

Definition get_iindex {T M} (i : index) (f : iindex T M)
  : pnset T M :=
  fun V => f V i.
Arguments get_iindex {T M} i f V /.

Definition drop_iindex {T M} (i : index) (f : iindex T M) :
  iindex T M :=
  fun V (j : index) =>
    if Compare_dec.le_lt_dec i j then get_iindex (S j) f V
    else get_iindex j f V.

Definition insert_iindex {T : nset} {M} (i : index)
           (a : pnset T M) (f : iindex T M)
  : iindex T M :=
  fun V (j : index) =>
    match Compare_dec.lt_eq_lt_dec i j with
    | inleft (left _) => get_iindex (pred j) f V
    | inleft (right _) => a V
    | inright _ => get_iindex j f V
    end.

(* Derived operations *)

Definition rename_iindex {T M} i j (f : iindex T M) :=
  insert_iindex i (get_iindex j f) (drop_iindex j f).

(* Morphism definitions *)

Add Parametric Morphism {T : nset} {M} : (@get_iindex T M)
    with signature eq ==> eq_kmorph ==> eq_pnset
      as get_iindex_mor.
  intros * Heq * V; cbn.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {T : nset} {M} : (@drop_iindex T M)
    with signature eq ==> eq_kmorph ==> eq_kmorph
    as drop_iindex_mor.
  intros * Heq V j; unfold drop_iindex; cbn.
  rewrite Heq, Heq; easy.
Qed.

Add Parametric Morphism {T : nset} {M} :
  (@insert_iindex T M)
    with signature eq ==> eq_pnset ==> eq_kmorph ==> eq_kmorph
      as insert_iindex_mor.
  intros * Heq1 * Heq2 V j; unfold insert_iindex; cbn.
  rewrite Heq1, Heq2, Heq2; easy.
Qed.

Add Parametric Morphism {T : nset} {M} i j :
  (@rename_iindex T M i j)
    with signature eq_kmorph ==> eq_kmorph
      as rename_iindex_mor.
  intros * Heq V k; unfold rename_iindex.
  rewrite Heq; easy.
Qed.

(* The identity [iindex] *)

Definition id_iindex : iindex (knset index) 0 :=
  fun _ (j : index) => j.
Arguments id_iindex V j /.

(* Useful functions on indices *)

Definition shift_index (i : index) : index -> index :=
  drop_iindex i id_iindex 0.

Definition unshift_index (i : index) : index -> index :=
  insert_iindex i (fun V => i) id_iindex 0.

Definition rename_index (i : index) (j : index) : index -> index :=
  rename_iindex i j id_iindex 0.

(* Reductions *)

Lemma rw_drop_iindex_ge {T M} i (f : iindex T M) V j :
  i <= j ->
  drop_iindex i f V j = f V (S j).
Proof.
  intros; unfold drop_iindex.
  destruct (le_lt_dec i j); try easy; omega.
Qed.

Lemma rw_drop_iindex_lt {T M} i (f : iindex T M) V j :
  S j <= i ->
  drop_iindex i f V j = f V j.
Proof.
  intros; unfold drop_iindex.
  destruct (le_lt_dec i j); try easy; omega.
Qed.

Lemma rw_drop_iindex_same {T M} i (f : iindex T M) V :
  drop_iindex i f V i = f V (S i).
Proof.
  apply rw_drop_iindex_ge; auto.
Qed.

Lemma rw_insert_iindex_gt {T M} i a (f : iindex T M) V j :
  S i <= j ->
  insert_iindex i a f V j = f V (pred j).
Proof.
  intros; unfold insert_iindex.
  destruct (lt_eq_lt_dec i j) as [[|]|]; try easy; omega.
Qed.

Lemma rw_insert_iindex_eq {T M} i a (f : iindex T M) V j :
  i = j ->
  insert_iindex i a f V j = a V.
Proof.
  intros; unfold insert_iindex.
  destruct (lt_eq_lt_dec i j) as [[|]|]; try easy; omega.
Qed.

Lemma rw_insert_iindex_lt {T M} i a (f : iindex T M) V j :
  S j <= i ->
  insert_iindex i a f V j = f V j.
Proof.
  intros; unfold insert_iindex.
  destruct (lt_eq_lt_dec i j) as [[|]|]; try easy; omega.
Qed.

Lemma rw_insert_iindex_same {T M} i a (f : iindex T M) V :
  insert_iindex i a f V i = a V.
Proof.
  apply rw_insert_iindex_eq; auto.
Qed.

Lemma rw_shift_index_ge i j :
  i <= j ->
  shift_index i j = S j.
Proof.
  intros; unfold shift_index.
  rewrite rw_drop_iindex_ge by easy; easy.
Qed.

Lemma rw_shift_index_lt i j :
  S j <= i ->
  shift_index i j = j.
Proof.
  intros; unfold shift_index.
  rewrite rw_drop_iindex_lt by easy; easy.
Qed.

Lemma rw_shift_index_same i :
  shift_index i i = S i.
Proof.
  unfold shift_index.
  rewrite rw_drop_iindex_same; easy.
Qed.

Lemma rw_unshift_index_gt i j :
  S i <= j ->
  unshift_index i j = pred j.
Proof.
  intros; unfold unshift_index.
  rewrite rw_insert_iindex_gt by easy; easy.
Qed.

Lemma rw_unshift_index_le i j :
  j <= i ->
  unshift_index i j = j.
Proof.
  intros Hle; unfold unshift_index.
  destruct (le_lt_eq_dec j i Hle).
  - rewrite rw_insert_iindex_lt by easy; easy.
  - rewrite rw_insert_iindex_eq by easy; easy.
Qed.

Lemma rw_unshift_index_same i :
  unshift_index i i = i.
Proof.
  unfold unshift_index.
  rewrite rw_insert_iindex_same; easy.
Qed.

Lemma rw_rename_iindex_eq {T M} i j (f : iindex T M) V k :
  i = k ->
  rename_iindex i j f V k = get_iindex j f V.
Proof.
  intros; unfold rename_iindex.
  rewrite rw_insert_iindex_eq by easy; easy.
Qed.

Lemma rw_rename_iindex_neq {T M} i j (f : iindex T M) V k :
  i <> k ->
  rename_iindex i j f V k = drop_iindex j f V (unshift_index i k).
Proof.
  intros; unfold rename_iindex.
  destruct (lt_eq_lt_dec i k) as [[|]|]; try omega.
  - rewrite rw_insert_iindex_gt by easy.
    rewrite rw_unshift_index_gt by easy.
    easy.
  - rewrite rw_insert_iindex_lt by easy.
    rewrite rw_unshift_index_le by omega.
    easy.
Qed.

Lemma rw_rename_iindex_same {T M} i j (f : iindex T M) V :
  rename_iindex i j f V i = get_iindex j f V.
Proof.
  intros; unfold rename_iindex.
  rewrite rw_insert_iindex_same by easy; easy.
Qed.  

Lemma rw_rename_index_eq i j k :
  i = k ->
  rename_index i j k = j.
Proof.
  intros; unfold rename_index.
  rewrite rw_rename_iindex_eq by easy; easy.
Qed.  

Lemma rw_rename_index_neq i j k :
  i <> k ->
  rename_index i j k = shift_index j (unshift_index i k).
Proof.
  intros; unfold rename_index.
  rewrite rw_rename_iindex_neq by easy; easy.
Qed.  

Lemma rw_rename_index_same i j :
  rename_index i j i = j.
Proof.
  rewrite rw_rename_index_eq by easy; easy.
Qed.

(* Useful lemma about predecessor and successor *)
Lemma rw_succ_pred i :
  0 < i ->
  S (pred i) = i.
Proof.
  intros; omega.
Qed.

Hint Rewrite @rw_drop_iindex_same @rw_insert_iindex_same
     @rw_rename_iindex_same @rw_shift_index_same
     @rw_unshift_index_same @rw_rename_index_same
  : rw_iindexs.

Hint Rewrite @rw_drop_iindex_ge @rw_drop_iindex_lt @rw_insert_iindex_gt
     @rw_insert_iindex_eq @rw_insert_iindex_lt
     @rw_rename_iindex_eq @rw_rename_iindex_neq @rw_shift_index_ge
     @rw_shift_index_lt @rw_unshift_index_le @rw_unshift_index_gt
     @rw_rename_index_eq @rw_rename_index_neq
     @rw_succ_pred
     using omega : rw_iindexs.

(* Case split on the order of the parameters, then simplify any
   index operations affected by the ordering. *)
Ltac case_order i j :=
  destruct (Compare_dec.lt_eq_lt_dec i j) as [[|]|];
  try omega;
  repeat progress
    ((rewrite_strat bottomup (hints rw_iindexs)); cbn).

(* Beta and eta rules for [iindex] operations *)

Lemma iindex_beta_get_pointwise {T M} i a (f : iindex T M) :
  get_iindex i (insert_iindex i a f) =p= a.
Proof.
  intros V; cbn; autorewrite with rw_iindexs; easy.
Qed.

Definition iindex_beta_get {T M} i a f :=
  eq_pnset_expand (@iindex_beta_get_pointwise T M i a f).

Lemma iindex_beta_drop_pointwise {T M} i a (f : iindex T M) :
  drop_iindex i (insert_iindex i a f) =km= f.
Proof.
  intros V j.
  case_order i j; easy.
Qed.

Definition iindex_beta_drop {T M} i a f :=
  eq_kmorph_expand (@iindex_beta_drop_pointwise T M i a f).

Lemma iindex_eta_pointwise {T M} i (f : iindex T M) :
  insert_iindex i (get_iindex i f) (drop_iindex i f) =km= f.
Proof.
  intros V j.
  case_order i j; f_equal; omega.
Qed.

Definition iindex_eta {T M} i f :=
  eq_kmorph_expand (@iindex_eta_pointwise T M i f).

Hint Rewrite @iindex_beta_get @iindex_beta_drop @iindex_eta
  : rw_iindexs.

Hint Rewrite @iindex_beta_get_pointwise
     @iindex_beta_drop_pointwise @iindex_eta_pointwise
  : rw_iindexs_pointwise.

(* Corollaries to beta and eta rules *)

Lemma iindex_beta_rename_insert_pointwise {T M} i j a
           (f : iindex T M) :
  rename_iindex i j (insert_iindex j a f) =km= insert_iindex i a f.
Proof.
  unfold rename_iindex.
  autorewrite with rw_iindexs_pointwise; easy.
Qed.

Definition iindex_beta_rename_insert {T M} i j a f :=
  eq_kmorph_expand (@iindex_beta_rename_insert_pointwise T M i j a f).

Lemma iindex_beta_drop_rename_pointwise {T M} i j
           (f : iindex T M) :
  drop_iindex i (rename_iindex i j f) =km= drop_iindex j f.
Proof.
  unfold rename_iindex.
  autorewrite with rw_iindexs_pointwise; easy.
Qed.

Definition iindex_beta_drop_rename {T M} i j f :=
  eq_kmorph_expand (@iindex_beta_drop_rename_pointwise T M i j f).

Lemma iindex_beta_rename_rename_pointwise {T M} i j k
           (f : iindex T M) :
  rename_iindex i j (rename_iindex j k f) =km= rename_iindex i k f.
Proof.
  unfold rename_iindex.
  autorewrite with rw_iindexs_pointwise; easy.
Qed.

Definition iindex_beta_rename_rename {T M} i j k f :=
  eq_kmorph_expand (@iindex_beta_rename_rename_pointwise T M i j k f).

Lemma iindex_beta_rename_pointwise {T M} i (f : iindex T M) :
  rename_iindex i i f =km= f.
Proof.
  unfold rename_iindex.
  autorewrite with rw_iindexs_pointwise; easy.
Qed.

Definition iindex_beta_rename {T M} i f :=
  eq_kmorph_expand (@iindex_beta_rename_pointwise T M i f).

Hint Rewrite @iindex_beta_rename_insert @iindex_beta_drop_rename
     @iindex_beta_rename_rename @iindex_beta_rename
  : rw_iindexs.

Hint Rewrite @iindex_beta_rename_insert_pointwise
     @iindex_beta_drop_rename_pointwise
     @iindex_beta_rename_rename_pointwise @iindex_beta_rename_pointwise
  : rw_iindexs_pointwise.

(* Useful lemmas about shifting and renaming*)

Lemma shift_index_neq i j :
  shift_index i j <> i.
Proof.
  case_order i j; omega.
Qed.

Lemma rename_index_neq i j k :
  i <> k ->
  j <> rename_index i j k.
Proof.
  intros.
  case_order i k; case_order j k; omega.
Qed.

(* Commuting [iindex] operations *)

Lemma swap_drop_iindex_drop_iindex_pointwise {T M} i j (f : iindex T M) :
  drop_iindex i (drop_iindex j f)
  =km= drop_iindex (unshift_index i j)
        (drop_iindex (shift_index j i) f).
Proof.
  intros V k.
  case_order i j;
    case_order j k; try easy;
      case_order i k; try easy;
        case_order j (S k); try easy.
Qed.

Definition swap_drop_iindex_drop_iindex {T M} i j f :=
  eq_kmorph_expand (@swap_drop_iindex_drop_iindex_pointwise T M i j f).

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

Lemma swap_drop_iindex_insert_iindex_pointwise {T M} i j a
      (f : iindex T M) :
  i <> j ->
  drop_iindex i (insert_iindex j a f)
  =km= insert_iindex (unshift_index i j) a
         (drop_iindex (unshift_index j i) f).
Proof.
  intros Hneq V k.
  case_order i j; try contradiction;
    case_order i k; try easy;
      case_order j k; try easy;
        case_order j (S k); easy.     
Qed.

Definition swap_drop_iindex_insert_iindex {T M} i j a f :=
  fun V k Heq =>
    eq_kmorph_expand
      (@swap_drop_iindex_insert_iindex_pointwise T M i j a f Heq) V k.

Lemma swap_insert_iindex_drop_iindex_pointwise {T M} i j a
      (f : iindex T M) :
  insert_iindex i a (drop_iindex j f)
  =km= drop_iindex (shift_index i j)
         (insert_iindex (shift_index (shift_index i j) i) a f).
Proof.
  intros V k.
  case_order i j;
    case_order i k; try easy;
      case_order j k; try easy.
Qed.

Definition swap_insert_iindex_drop_iindex {T M} i j a f :=
  eq_kmorph_expand
    (@swap_insert_iindex_drop_iindex_pointwise T M i j a f).

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

Lemma swap_insert_iindex_get_iindex_pointwise {T M} i j a
      (f : iindex T M) :
  i <> j ->
  get_iindex i f
  =p= get_iindex (shift_index j i) (insert_iindex j a f).
Proof.
  intros Hneq V; cbn.
  case_order j i; easy.
Qed.

Definition swap_insert_iindex_get_iindex {T M} i j a f :=
  fun V Hneq =>
    eq_pnset_expand
      (@swap_insert_iindex_get_iindex_pointwise T M i j a f Hneq) V.

Lemma swap_get_iindex_drop_iindex_pointwise {T M} i j
      (f : iindex T M) :
  get_iindex i (drop_iindex j f)
  =p= get_iindex (shift_index j i) f.
Proof.
  intros V; cbn.
  case_order j i; easy.
Qed.

Definition swap_get_iindex_drop_iindex {T M} i j f :=
  eq_pnset_expand
    (@swap_get_iindex_drop_iindex_pointwise T M i j f).

Lemma swap_drop_iindex_get_iindex_pointwise {T M} i j
      (f : iindex T M) :
  i <> j ->
  get_iindex i f
  =p= get_iindex (unshift_index j i) (drop_iindex j f).
Proof.
  intros Hneq V; cbn.
  case_order j i; easy.
Qed.

Definition swap_drop_iindex_get_iindex {T M} i j f :=
  fun V Hneq =>
    eq_pnset_expand
      (@swap_drop_iindex_get_iindex_pointwise T M i j f Hneq) V.

Lemma swap_insert_iindex_rename_iindex_pointwise {T M} i a j k
      (f : iindex T M) :
  insert_iindex i a (rename_iindex j k f)
  =km= rename_iindex (shift_index i j) (shift_index i k)
         (insert_iindex
            (rename_index (shift_index i j) (shift_index i k) i) a f).
Proof.
  unfold rename_iindex.
  rewrite swap_insert_iindex_insert_iindex_pointwise.
  rewrite swap_insert_iindex_drop_iindex_pointwise.
  rewrite swap_get_iindex_insert_iindex_pointwise
    by auto using rename_index_neq, shift_index_neq.
  case_order i j;
    case_order i k; try easy;
      case_order (pred i) k; try easy.
  rewrite swap_drop_iindex_insert_iindex_pointwise by omega.
  rewrite swap_drop_iindex_insert_iindex_pointwise by omega.
  autorewrite with rw_iindexs.
  easy.
Qed.

Definition swap_insert_iindex_rename_iindex {T M} i a j k f :=
  eq_kmorph_expand
    (@swap_insert_iindex_rename_iindex_pointwise T M i a j k f).

Lemma swap_rename_iindex_insert_iindex_pointwise {T M} i j k a
      (f : iindex T M) :
  j <> k ->
  rename_iindex i j (insert_iindex k a f)
  =km= insert_iindex (rename_index j i k) a
         (rename_iindex (unshift_index (unshift_index j k) i)
            (unshift_index k j) f).
Proof.
  intros; unfold rename_iindex.
  rewrite swap_drop_iindex_insert_iindex_pointwise by easy.
  rewrite swap_insert_iindex_insert_iindex_pointwise.
  rewrite swap_get_iindex_insert_iindex_pointwise by easy.
  case_order i k;
    case_order j k; easy.
Qed.

Definition swap_rename_iindex_insert_iindex {T M} i j k a f :=
  fun V l Hneq =>
    eq_kmorph_expand
      (@swap_rename_iindex_insert_iindex_pointwise T M i j k a f Hneq)
      V l.

Lemma swap_drop_iindex_rename_iindex_pointwise {T M} i j k
      (f : iindex T M) :
  i <> j ->
  drop_iindex i (rename_iindex j k f)
  =km= rename_iindex
         (unshift_index i j) (unshift_index (unshift_index j i) k)
         (drop_iindex (rename_index j k i) f).
Proof.
  intros; unfold rename_iindex.
  rewrite swap_drop_iindex_insert_iindex_pointwise by easy.
  rewrite swap_drop_iindex_drop_iindex_pointwise.
  rewrite swap_get_iindex_drop_iindex_pointwise.
  case_order i k;
    case_order i j; try easy.
Qed.

Definition swap_drop_iindex_rename_iindex {T M} i j k f :=
  fun V l Hneq =>
    eq_kmorph_expand
      (@swap_drop_iindex_rename_iindex_pointwise T M i j k f Hneq)
      V l.

Lemma swap_rename_iindex_drop_iindex_pointwise {T M} i j k
      (f : iindex T M) :
  rename_iindex i j (drop_iindex k f)
  =km= drop_iindex (shift_index i (unshift_index j k))
         (rename_iindex 
            (shift_index (shift_index i (unshift_index j k)) i)
            (shift_index k j) f).
Proof.
  intros; unfold rename_iindex.
  rewrite swap_drop_iindex_drop_iindex_pointwise.
  rewrite swap_get_iindex_drop_iindex_pointwise by easy.
  rewrite swap_insert_iindex_drop_iindex_pointwise by easy.
  easy.
Qed.

Definition swap_rename_iindex_drop_iindex {T M} i j k f :=
  eq_kmorph_expand
    (@swap_rename_iindex_drop_iindex_pointwise T M i j k f).

(* Free names are a pair of a string and an index *)

Set Primitive Projections.
Record name := mkname { n_string : string; n_index : index }.
Add Printing Constructor name.
Unset Primitive Projections.

Definition name_of_string s := mkname s 0.
Coercion name_of_string : string >-> name.
Bind Scope string_scope with name.

(* Useful lemma *)
Lemma name_neq_string_eq_index_neq n m :
  n <> m -> n_string n = n_string m -> n_index n <> n_index m.
Proof.
  intros Hneq Heq1 Heq2; apply Hneq.
  replace n with (mkname (n_string n) (n_index n)) by easy.
  replace (n_string n) with (n_string m) by easy.
  replace (n_index n) with (n_index m) by easy.
  easy.
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

Definition drop_iname {T M} (n : name) (f : iname T M) : iname T M :=
  with_iname (n_string n)
    (drop_iindex (n_index n) (project_iname (n_string n) f)) f.

Definition insert_iname {T M} n (a : pnset T M) (f : iname T M)
  : iname T M :=
  with_iname (n_string n)
    (insert_iindex (n_index n) a (project_iname (n_string n) f)) f.

Definition rename_iname {T M} n m (f : iname T M) :=
  insert_iname n (get_iname m f) (drop_iname m f).

(* Morphism definitions *)

Add Parametric Morphism {T : nset} {M} s : (@project_iname T M s)
    with signature eq_kmorph ==> eq_kmorph
    as project_iname_mor.
  intros * Heq V n; unfold project_iname.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {T : nset} {M} s : (@with_iname T M s)
    with signature eq_kmorph ==> eq_kmorph ==> eq_kmorph
      as with_iname_mor.
  intros * Heq1 * Heq2 V n; unfold with_iname; cbn.
  rewrite Heq1, Heq2; easy.
Qed.

Add Parametric Morphism {T : nset} {M} n : (@get_iname T M n)
    with signature eq_kmorph ==> eq_pnset
    as get_iname_mor.
  intros * Heq V; unfold get_iname; cbn.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {T : nset} {M} n : (@drop_iname T M n)
    with signature eq_kmorph ==> eq_kmorph
      as drop_iname_mor.
  intros * Heq V m; unfold drop_iname.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {T : nset} {M} n : (@insert_iname T M n)
    with signature eq_pnset ==> eq_kmorph ==> eq_kmorph
    as insert_iname_mor.
  intros * Heq1 * Heq2 V m; unfold insert_iname.
  rewrite Heq1, Heq2; easy.
Qed.

Add Parametric Morphism {T : nset} {M} n m : (@rename_iname T M n m)
    with signature eq_kmorph ==> eq_kmorph
    as rename_iname_mor.
  intros * Heq V o; unfold rename_iname.
  rewrite Heq; easy.
Qed.

(* The identity [iname] *)

Definition id_iname : iname (knset name) 0 :=
  fun _ (j : name) => j.
Arguments id_iname V j /.

(* Useful functions on names *)

Definition shift_name (n : name) : name -> name :=
  drop_iname n id_iname 0.

Definition unshift_name (n : name) : name -> name :=
  insert_iname n (fun V => n) id_iname 0.

Definition rename_name (n : name) (m : name) : name -> name :=
  rename_iname n m id_iname 0.

(* Reductions *)

Lemma rw_with_iname_eq {T M} s f (g : iname T M) V n :
  s = n_string n ->
  with_iname s f g V n = f V (n_index n).
Proof.
  intro Heq; subst; unfold with_iname.
  destruct (string_dec (n_string n) (n_string n));
    try contradiction; easy.
Qed.

Lemma rw_with_iname_neq {T M} s f (g : iname T M) V n :
  s <> n_string n ->
  with_iname s f g V n = g V n.
Proof.
  intro Heq; unfold with_iname.
  destruct (string_dec (n_string n) s); subst;
    try contradiction; easy.
Qed.

Lemma rw_with_iname_same {T M} f (g : iname T M) V n :
  with_iname (n_string n) f g V n = f V (n_index n).
Proof.
  apply rw_with_iname_eq; easy.
Qed.

Lemma rw_get_iname {T M} n (f : iname T M) V :
  get_iname n f V = f V n.
Proof.
  unfold get_iname; easy.
Qed.

Lemma rw_drop_iname_indistinct {T M} n (f : iname T M) V m :
  n_string n = n_string m ->
  drop_iname n f V m
  = drop_iindex (n_index n)
      (project_iname (n_string n) f) V (n_index m).
Proof.
  intro Heq; unfold drop_iname.
  rewrite rw_with_iname_eq; easy.
Qed.

Lemma rw_drop_iname_distinct {T M} n (f : iname T M) V m :
  n_string n <> n_string m ->
  drop_iname n f V m = f V m.
Proof.
  intro Heq; unfold drop_iname.
  rewrite rw_with_iname_neq; easy.
Qed.

Lemma rw_drop_iname_same {T M} n (f : iname T M) V :
  drop_iname n f V n
  = f V (mkname (n_string n) (S (n_index n))).
Proof.
  rewrite rw_drop_iname_indistinct by easy.
  rewrite rw_drop_iindex_same; easy.
Qed.

Lemma rw_insert_iname_indistinct {T M} n a (f : iname T M) V m :
  n_string n = n_string m ->
  insert_iname n a f V m
  = insert_iindex (n_index n) a
      (project_iname (n_string n) f) V (n_index m).
Proof.
  intro Heq; unfold insert_iname.
  rewrite rw_with_iname_eq; easy.
Qed.

Lemma rw_insert_iname_distinct {T M} n a (f : iname T M) V m :
  n_string n <> n_string m ->
  insert_iname n a f V m = f V m.
Proof.
  intro Heq; unfold insert_iname.
  rewrite rw_with_iname_neq; easy.
Qed.

Lemma rw_insert_iname_same {T M} n a (f : iname T M) V :
  insert_iname n a f V n = a V.
Proof.
  rewrite rw_insert_iname_indistinct by easy.
  rewrite rw_insert_iindex_same; easy.
Qed.

Lemma rw_shift_name_indistinct n m :
  n_string n = n_string m ->
  shift_name n m
  = mkname (n_string m) (shift_index (n_index n) (n_index m)).
Proof.
  intros; unfold shift_name.
  rewrite rw_drop_iname_indistinct by easy.
  replace (n_string m) with (n_string n) by easy.
  case_order (n_index n) (n_index m); easy.
Qed.

Lemma rw_shift_name_distinct n m :
  n_string n <> n_string m ->
  shift_name n m = m.
Proof.
  intros; unfold shift_name.
  rewrite rw_drop_iname_distinct by easy; easy.
Qed.

Lemma rw_shift_name_same n :
  shift_name n n
  = mkname (n_string n) (S (n_index n)).
Proof.
  rewrite rw_shift_name_indistinct by easy.
  rewrite rw_shift_index_same; easy.
Qed.

Lemma rw_unshift_name_indistinct n m :
  n_string n = n_string m ->
  unshift_name n m
  = mkname (n_string m) (unshift_index (n_index n) (n_index m)).
Proof.
  intros; unfold unshift_name.
  rewrite rw_insert_iname_indistinct by easy.
  replace (n_string m) with (n_string n) by easy.
  case_order (n_index n) (n_index m); try easy.
  replace (n_index m) with (n_index n) by easy; easy.
Qed.

Lemma rw_unshift_name_distinct n m :
  n_string n <> n_string m ->
  unshift_name n m = m.
Proof.
  intros; unfold unshift_name.
  rewrite rw_insert_iname_distinct by easy; easy.
Qed.

Lemma rw_unshift_name_same n :
  unshift_name n n = n.
Proof.
  rewrite rw_unshift_name_indistinct by easy.
  rewrite rw_unshift_index_same; easy.
Qed.

Lemma rw_rename_iname_indistinct {T M} n m (f : iname T M) V o :
  n_string n = n_string o ->
  rename_iname n m f V o
  = insert_iindex (n_index n) (get_iname m f)
      (project_iname (n_string n) (drop_iname m f)) V (n_index o).
Proof.
  intros; unfold rename_iname.
  rewrite rw_insert_iname_indistinct by easy; easy.
Qed.

Lemma rw_rename_iname_distinct {T M} n m (f : iname T M) V o :
  n_string n <> n_string o ->
  rename_iname n m f V o
  = drop_iname m f V o.
Proof.
  intros; unfold rename_iname.
  rewrite rw_insert_iname_distinct by easy; easy.
Qed.

Lemma rw_rename_iname_same {T M} n m (f : iname T M) V :
  rename_iname n m f V n = get_iname m f V.
Proof.
  intros; unfold rename_iname.
  rewrite rw_insert_iname_same by easy; easy.
Qed.

Lemma rw_rename_name_indistinct n m o :
  n_string n = n_string o ->
  rename_name n m o =
  insert_iindex (n_index n) (fun _ => m)
    (project_iname (n_string n) (drop_iname m id_iname)) 0 
    (n_index o).
Proof.
  intros; unfold rename_name.
  rewrite rw_rename_iname_indistinct by easy; easy.
Qed.  

Lemma rw_rename_name_distinct n m o :
  n_string n <> n_string o ->
  rename_name n m o = shift_name m o.
Proof.
  intros; unfold rename_name, shift_name.
  rewrite rw_rename_iname_distinct by easy; easy.
Qed.

Lemma rw_rename_name_same n m :
  rename_name n m n = m.
Proof.
  unfold rename_name.
  rewrite rw_rename_iname_same; easy.
Qed.

Hint Rewrite @rw_get_iname @rw_with_iname_same
     @rw_drop_iname_same @rw_insert_iname_same
     @rw_shift_name_same @rw_unshift_name_same
     @rw_rename_iname_same @rw_rename_name_same
  : rw_inames.

Hint Rewrite @rw_with_iname_eq @rw_with_iname_neq
     @rw_drop_iname_distinct @rw_drop_iname_indistinct
     @rw_insert_iname_distinct @rw_insert_iname_indistinct
     @rw_shift_name_distinct @rw_shift_name_indistinct
     @rw_unshift_name_distinct @rw_unshift_name_indistinct
     @rw_rename_iname_distinct @rw_rename_iname_indistinct
     @rw_rename_name_distinct @rw_rename_name_indistinct
     using (cbn; congruence) : rw_inames.

(* Case split on the equality of the string parameters, then simplify
   any name operations affected by the ordering. *)
Ltac case_string s1 s2 :=
  destruct (string_dec s1 s2); try contradiction;
  repeat progress (autorewrite with rw_inames; cbn).

(* Beta and eta rules for [iname] operations *)

Lemma iname_beta_project_same_pointwise {T M} s f (g : iname T M) :
  project_iname s (with_iname s f g) =km= f.
Proof.
  intros V i; cbn; autorewrite with rw_inames; easy.
Qed.

Definition iname_beta_project_same {T M} s f g :=
  eq_kmorph_expand (@iname_beta_project_same_pointwise T M s f g).

Lemma iname_beta_project_neq_pointwise {T M} s t f (g : iname T M) :
  s <> t ->
  project_iname s (with_iname t f g) =km= project_iname s g.
Proof.
  intros Hneq V i; cbn; autorewrite with rw_inames; easy.
Qed.

Definition iname_beta_project_neq {T M} s t f g :=
  fun V i Hneq =>
    eq_kmorph_expand
      (@iname_beta_project_neq_pointwise T M s t f g Hneq) V i.

Lemma iname_beta_with_same_pointwise {T M} s f g (h : iname T M) :
  with_iname s f (with_iname s g h)
  =km= with_iname s f h.
Proof.
  intros V n.
  case_string s (n_string n); easy.
Qed.

Definition iname_beta_with_same {T M} s f g h :=
  eq_kmorph_expand (@iname_beta_with_same_pointwise T M s f g h).

Lemma iname_eta_pointwise {T M} s (f : iname T M) :
  with_iname s (project_iname s f) f =km= f.
Proof.
  intros V n.
  case_string s (n_string n); subst; easy.
Qed.

Definition iname_eta {T M} s f :=
  eq_kmorph_expand (@iname_eta_pointwise T M s f).

Hint Rewrite @iname_beta_project_same @iname_beta_with_same
     @iname_eta
  : rw_inames.

Hint Rewrite @iname_beta_project_same_pointwise @iname_beta_with_same_pointwise @iname_eta_pointwise
  : rw_inames_pointwise.

Hint Rewrite @iname_beta_project_neq
  using (cbn; congruence) : rw_inames.

Hint Rewrite @iname_beta_project_neq_pointwise
  using (cbn; congruence) : rw_inames_pointwise.

(* Corollaries of the beta rules *)

Lemma iname_beta_project_drop_eq_pointwise {T M} s n (f : iname T M) :
  s = n_string n ->
  project_iname s (drop_iname n f)
  =km= drop_iindex (n_index n) (project_iname (n_string n) f).
Proof.
  intro Heq; unfold drop_iname; subst.
  intros V i; autorewrite with rw_inames; easy.
Qed.

Definition iname_beta_project_drop_eq {T M} s n f :=
  fun V i Heq =>
    eq_kmorph_expand
      (@iname_beta_project_drop_eq_pointwise T M s n f Heq) V i.

Lemma iname_beta_project_drop_neq_pointwise {T M} s n (f : iname T M) :
  s <> n_string n ->
  project_iname s (drop_iname n f)
  =km= project_iname s f.
Proof.
  intro Heq; unfold drop_iname.
  autorewrite with rw_inames rw_inames_pointwise; easy.
Qed.

Definition iname_beta_project_drop_neq {T M} s n f :=
  fun V i Hneq =>
    eq_kmorph_expand
      (@iname_beta_project_drop_neq_pointwise T M s n f Hneq) V i.

Lemma iname_beta_project_insert_eq_pointwise {T M} s n a
      (f : iname T M) :
  s = n_string n ->
  project_iname s (insert_iname n a f)
  =km= insert_iindex (n_index n) a (project_iname (n_string n) f).
Proof.
  intro; unfold insert_iname; subst.
  autorewrite with rw_inames rw_inames_pointwise; easy.
Qed.

Definition iname_beta_project_insert_eq {T M} s n a f :=
  fun V i Heq =>
    eq_kmorph_expand
      (@iname_beta_project_insert_eq_pointwise T M s n a f Heq) V i.

Lemma iname_beta_project_insert_neq_pointwise {T M} s n a
      (f : iname T M) :
  s <> n_string n ->
  project_iname s (insert_iname n a f)
  =km= project_iname s f.
Proof.
  intro; unfold insert_iname.
  autorewrite with rw_inames rw_inames_pointwise; easy.
Qed.

Definition iname_beta_project_insert_neq {T M} s n a f :=
  fun V i Hneq =>
    eq_kmorph_expand
      (@iname_beta_project_insert_neq_pointwise T M s n a f Hneq) V i.

Lemma iname_beta_with_drop_eq_pointwise {T M} s n (f : iindex T M) g :
  s = n_string n ->
  with_iname s f (drop_iname n g)
  =km= with_iname s f g.
Proof.
  intros; unfold drop_iname; subst.
  autorewrite with rw_inames_pointwise; easy.
Qed.

Definition iname_beta_with_drop_eq {T M} s n f g :=
  fun V i Heq =>
    eq_kmorph_expand
      (@iname_beta_with_drop_eq_pointwise T M s n f g Heq) V i.

Lemma iname_beta_with_insert_eq_pointwise {T M} s n
      (f : iindex T M) a g :
  s = n_string n ->
  with_iname s f (insert_iname n a g)
  =km= with_iname s f g.
Proof.
  intros; unfold insert_iname; subst.
  autorewrite with rw_inames_pointwise; easy.
Qed.

Definition iname_beta_with_insert_eq {T M} s n f a g :=
  fun V i Heq =>
    eq_kmorph_expand
      (@iname_beta_with_insert_eq_pointwise T M s n f a g Heq) V i.

Lemma iname_beta_get_with_eq_pointwise {T M} s n (f : iindex T M) g :
  s = n_string n ->
  get_iname n (with_iname s f g)
  =p= get_iindex (n_index n) f.
Proof.
  intros; unfold get_iname; subst.
  autorewrite with rw_inames_pointwise; easy.
Qed.

Definition iname_beta_get_with_eq {T M} s n f g :=
  fun V Heq =>
    eq_pnset_expand
      (@iname_beta_get_with_eq_pointwise T M s n f g Heq) V.

Lemma iname_beta_get_with_neq_pointwise {T M} s n (f : iindex T M) g :
  s <> n_string n ->
  get_iname n (with_iname s f g)
  =p= get_iname n g.
Proof.
  intros; unfold get_iname; subst.
  autorewrite with rw_inames_pointwise; easy.
Qed.

Definition iname_beta_get_with_neq {T M} s n f g :=
  fun V Hneq =>
    eq_pnset_expand
      (@iname_beta_get_with_neq_pointwise T M s n f g Hneq) V.

Lemma iname_beta_drop_with_eq_pointwise {T M} s n (f : iindex T M) g :
  s = n_string n ->
  drop_iname n (with_iname s f g)
  =km= with_iname s (drop_iindex (n_index n) f) g.
Proof.
  intros; unfold drop_iname; subst.
  autorewrite with rw_inames_pointwise; easy.
Qed.

Definition iname_beta_drop_with_eq {T M} s n f g :=
  fun V i Heq =>
    eq_kmorph_expand
      (@iname_beta_drop_with_eq_pointwise T M s n f g Heq) V i.

Lemma iname_beta_drop_with_neq_pointwise {T M} s n (f : iindex T M) g :
  s <> n_string n ->
  drop_iname n (with_iname s f g)
  =km= with_iname (n_string n)
         (drop_iindex (n_index n) (project_iname (n_string n) g))
           (with_iname s f g).
Proof.
  intros; unfold drop_iname; subst.
  autorewrite with rw_inames_pointwise; easy.
Qed.

Definition iname_beta_drop_with_neq {T M} s n f g :=
  fun V i Hneq =>
    eq_kmorph_expand
      (@iname_beta_drop_with_neq_pointwise T M s n f g Hneq) V i.

Lemma iname_beta_insert_with_eq_pointwise {T M} s n a
      (f : iindex T M) g :
  s = n_string n ->
  insert_iname n a (with_iname s f g)
  =km= with_iname s (insert_iindex (n_index n) a f) g.
Proof.
  intros; unfold insert_iname; subst.
  autorewrite with rw_inames_pointwise; easy.
Qed.

Definition iname_beta_insert_with_eq {T M} s n a f g :=
  fun V i Heq =>
    eq_kmorph_expand
      (@iname_beta_insert_with_eq_pointwise T M s n a f g Heq) V i.

Lemma iname_beta_insert_with_neq_pointwise {T M} s n a
      (f : iindex T M) g :
  s <> n_string n ->
  insert_iname n a (with_iname s f g)
  =km= with_iname (n_string n)
         (insert_iindex (n_index n) a (project_iname (n_string n) g))
           (with_iname s f g).
Proof.
  intros; unfold insert_iname; subst.
  autorewrite with rw_inames_pointwise; easy.
Qed.

Definition iname_beta_insert_with_neq {T M} s n a f g :=
  fun V i Hneq =>
    eq_kmorph_expand
      (@iname_beta_insert_with_neq_pointwise T M s n a f g Hneq) V i.

Hint Rewrite @iname_beta_project_drop_eq @iname_beta_project_drop_neq
     @iname_beta_project_insert_eq @iname_beta_project_insert_neq
     @iname_beta_with_drop_eq @iname_beta_with_insert_eq
     @iname_beta_get_with_eq @iname_beta_get_with_neq
     @iname_beta_drop_with_eq @iname_beta_drop_with_neq
     @iname_beta_insert_with_eq @iname_beta_insert_with_neq
  using (cbn; congruence) : rw_inames.

Hint Rewrite @iname_beta_project_drop_eq_pointwise
     @iname_beta_project_drop_neq_pointwise
     @iname_beta_project_insert_eq_pointwise
     @iname_beta_project_insert_neq_pointwise
     @iname_beta_with_drop_eq_pointwise
     @iname_beta_with_insert_eq_pointwise
     @iname_beta_get_with_eq_pointwise
     @iname_beta_get_with_neq_pointwise
     @iname_beta_drop_with_eq_pointwise
     @iname_beta_drop_with_neq_pointwise
     @iname_beta_insert_with_eq_pointwise
     @iname_beta_insert_with_neq_pointwise
  using (cbn; congruence) : rw_inames_pointwise.

Lemma iname_beta_project_rename_eq_pointwise {T M} s n m
      (f : iname T M) :
  s = n_string n ->
  project_iname s (rename_iname n m f)
  =km= insert_iindex (n_index n) (get_iname m f)
         (project_iname (n_string n) (drop_iname m f)).
Proof.
  intro; unfold rename_iname; subst.
  autorewrite with rw_inames_pointwise; easy.
Qed.

Definition iname_beta_project_rename_eq {T M} s n m f :=
  fun V i Heq =>
    eq_kmorph_expand
      (@iname_beta_project_rename_eq_pointwise T M s n m f Heq) V i.

Lemma iname_beta_project_rename_neq_pointwise {T M} s n m
      (f : iname T M) :
  s <> n_string n ->
  project_iname s (rename_iname n m f)
  =km= project_iname s (drop_iname m f).
Proof.
  intro; unfold rename_iname.
  autorewrite with rw_inames_pointwise; easy.
Qed.

Definition iname_beta_project_rename_neq {T M} s n m f :=
  fun V i Hneq =>
    eq_kmorph_expand
      (@iname_beta_project_rename_neq_pointwise T M s n m f Hneq) V i.

Lemma iname_beta_with_rename_eq_pointwise {T M} s n
      (f : iindex T M) m g :
  s = n_string n ->
  with_iname s f (rename_iname n m g)
  =km= with_iname s f (drop_iname m g).
Proof.
  intros; unfold rename_iname; subst.
  autorewrite with rw_inames_pointwise; easy.
Qed.

Definition iname_beta_with_rename_eq {T M} s n f m g :=
  fun V i Heq =>
    eq_kmorph_expand
      (@iname_beta_with_rename_eq_pointwise T M s n f m g Heq) V i.

Lemma iname_beta_rename_with_eq_pointwise {T M} s n m
      (f : iindex T M) g :
  s = n_string m ->
  rename_iname n m (with_iname s f g)
  =km= insert_iname n (get_iindex (n_index m) f)
        (with_iname s (drop_iindex (n_index m) f) g).
Proof.
  intros; unfold rename_iname; subst.
  autorewrite with rw_inames_pointwise; easy.
Qed.

Definition iname_beta_rename_with_eq {T M} s n m f g :=
  fun V Heq =>
    eq_kmorph_expand
      (@iname_beta_rename_with_eq_pointwise T M s n m f g Heq) V.

Lemma iname_beta_rename_with_neq_pointwise {T M} s n m
      (f : iindex T M) g :
  s <> n_string m ->
  rename_iname n m (with_iname s f g)
  =km= insert_iname n (get_iname m g)
         (with_iname (n_string m)
           (drop_iindex (n_index m) (project_iname (n_string m) g))
             (with_iname s f g)).
Proof.
  intros; unfold rename_iname; subst.
  autorewrite with rw_inames_pointwise; easy.
Qed.

Definition iname_beta_rename_with_neq {T M} s n m f g :=
  fun V Hneq =>
    eq_kmorph_expand
      (@iname_beta_rename_with_neq_pointwise T M s n m f g Hneq) V.

Hint Rewrite @iname_beta_project_rename_eq
     @iname_beta_project_rename_neq
     @iname_beta_with_rename_eq
     @iname_beta_rename_with_eq
     @iname_beta_rename_with_neq
  using (cbn; congruence) : rw_inames.

Hint Rewrite @iname_beta_project_rename_eq_pointwise
     @iname_beta_project_rename_neq_pointwise
     @iname_beta_with_rename_eq_pointwise
     @iname_beta_rename_with_eq_pointwise
     @iname_beta_rename_with_neq_pointwise 
  using (cbn; congruence) : rw_inames_pointwise.

Lemma iname_beta_get_pointwise {T M} n a (f : iname T M) :
  get_iname n (insert_iname n a f) =p= a.
Proof.
  intros V; autorewrite with rw_inames rw_iindexs; easy.
Qed.

Definition iname_beta_get {T M} n a f :=
  eq_pnset_expand (@iname_beta_get_pointwise T M n a f).

Lemma iname_beta_drop_pointwise {T M} n a (f : iname T M) :
  drop_iname n (insert_iname n a f) =km= f.
Proof.
  intros V m.
  case_string (n_string n) (n_string m); try easy.
  autorewrite with rw_inames_pointwise rw_iindexs; cbn.
  replace (n_string n) with (n_string m) by easy; easy.
Qed.

Definition iname_beta_drop {T M} n a f :=
  eq_kmorph_expand (@iname_beta_drop_pointwise T M n a f).

Lemma iname_eta_insert_pointwise {T M} n (f : iname T M) :
  insert_iname n (get_iname n f) (drop_iname n f) =km= f.
Proof.
  intros V m.
  case_string (n_string n) (n_string m); try easy.
  autorewrite with rw_inames_pointwise.
  replace (get_iname n f)
    with (get_iindex (n_index n) (project_iname (n_string n) f)) 
    by easy.  
  autorewrite with rw_iindexs; cbn.
  replace (n_string n) with (n_string m); easy.
Qed.

Definition iname_eta_insert {T M} n f :=
  eq_kmorph_expand (@iname_eta_insert_pointwise T M n f).

Hint Rewrite @iname_beta_get @iname_beta_drop @iname_eta_insert
  : rw_inames.

Hint Rewrite @iname_beta_get_pointwise
     @iname_beta_drop_pointwise @iname_eta_insert_pointwise
  : rw_inames_pointwise.

Lemma iname_beta_rename_insert_pointwise {T M} n m a
           (f : iname T M) :
  rename_iname n m (insert_iname m a f) =km= insert_iname n a f.
Proof.
  unfold rename_iname.
  autorewrite with rw_inames_pointwise; easy.
Qed.

Definition iname_beta_rename_insert {T M} n m a f :=
  eq_kmorph_expand (@iname_beta_rename_insert_pointwise T M n m a f).

Lemma iname_beta_drop_rename_pointwise {T M} n m
           (f : iname T M) :
  drop_iname n (rename_iname n m f) =km= drop_iname m f.
Proof.
  unfold rename_iname.
  autorewrite with rw_inames_pointwise; easy.
Qed.

Definition iname_beta_drop_rename {T M} n m f :=
  eq_kmorph_expand (@iname_beta_drop_rename_pointwise T M n m f).

Lemma iname_beta_rename_rename_pointwise {T M} n m o
           (f : iname T M) :
  rename_iname n m (rename_iname m o f) =km= rename_iname n o f.
Proof.
  unfold rename_iname.
  autorewrite with rw_inames_pointwise; easy.
Qed.

Definition iname_beta_rename_rename {T M} n m o f :=
  eq_kmorph_expand (@iname_beta_rename_rename_pointwise T M n m o f).

Lemma iname_beta_rename_pointwise {T M} n (f : iname T M) :
  rename_iname n n f =km= f.
Proof.
  unfold rename_iname.
  autorewrite with rw_inames_pointwise; easy.
Qed.

Definition iname_beta_rename {T M} n f :=
  eq_kmorph_expand (@iname_beta_rename_pointwise T M n f).

Hint Rewrite @iname_beta_rename_insert @iname_beta_drop_rename
     @iname_beta_rename_rename @iname_beta_rename
  : rw_inames.

Hint Rewrite @iname_beta_rename_insert_pointwise
     @iname_beta_drop_rename_pointwise
     @iname_beta_rename_rename_pointwise @iname_beta_rename_pointwise
  : rw_inames_pointwise.

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

Lemma swap_drop_iname_drop_iname_pointwise {T M} n m
      (f : iname T M) :
  drop_iname n (drop_iname m f)
  =km= drop_iname (unshift_name n m) (drop_iname (shift_name m n) f).
Proof.
  intros V o.
  case_string (n_string n) (n_string m).
  - case_string (n_string m) (n_string o); try easy.
    autorewrite with rw_inames_pointwise.
    rewrite swap_drop_iindex_drop_iindex_pointwise.
    replace (n_string n) with (n_string m) by easy; easy.
  - unfold drop_iname.
    rewrite swap_with_iname_with_iname by easy.
    autorewrite with rw_inames rw_inames_pointwise; easy.
Qed.

Definition swap_drop_iname_drop_iname {T M} n m f :=
  eq_kmorph_expand
    (@swap_drop_iname_drop_iname_pointwise T M n m f).

Lemma swap_insert_iname_insert_iname_pointwise {T M} n a m b
      (f : iname T M) :
  insert_iname n a (insert_iname m b f)
  =km= insert_iname (shift_name n m) b
      (insert_iname (unshift_name m n) a f).
Proof.
  intros V o.
  case_string (n_string n) (n_string m).
  - case_string (n_string m) (n_string o); try easy.
    autorewrite with rw_inames_pointwise.
    rewrite swap_insert_iindex_insert_iindex.
    replace (n_string n) with (n_string m) by easy; easy.
  - unfold insert_iname.
    rewrite swap_with_iname_with_iname by easy.
    autorewrite with rw_inames rw_inames_pointwise; easy.
Qed.

Definition swap_insert_iname_insert_iname {T M} n a m b f :=
  eq_kmorph_expand
    (@swap_insert_iname_insert_iname_pointwise T M n a m b f).

Lemma swap_drop_iname_insert_iname_pointwise {T M} n m a
      (f : iname T M) :
  n <> m ->
  drop_iname n (insert_iname m a f)
  =km= insert_iname (unshift_name n m) a
        (drop_iname (unshift_name m n) f).
Proof.
  intros Hneq V o.
  case_string (n_string n) (n_string m).
  - case_string (n_string n) (n_string o); try easy.
    autorewrite with rw_inames_pointwise.
    rewrite swap_drop_iindex_insert_iindex
      by auto using name_neq_string_eq_index_neq.
    replace (n_string n) with (n_string m) by easy; easy.
  - unfold drop_iname, insert_iname.
    rewrite swap_with_iname_with_iname by easy.
    autorewrite with rw_inames rw_inames_pointwise; easy.
Qed.

Definition swap_drop_iname_insert_iname {T M} n m a f :=
  fun V o Heq =>
    eq_kmorph_expand
      (@swap_drop_iname_insert_iname_pointwise T M n m a f Heq) V o.

Lemma swap_insert_iname_drop_iname_pointwise {T M} n m a
      (f : iname T M) :
  insert_iname n a (drop_iname m f)
  =km= drop_iname (shift_name n m)
      (insert_iname (shift_name (shift_name n m) n) a f).
Proof.
  intros V o.
  case_string (n_string n) (n_string m).
  - case_string (n_string n) (n_string o); try easy.
    autorewrite with rw_inames_pointwise.
    rewrite swap_insert_iindex_drop_iindex.
    replace (n_string n) with (n_string m) by easy; easy.
  - unfold drop_iname, insert_iname.
    rewrite swap_with_iname_with_iname by easy.
    autorewrite with rw_inames rw_inames_pointwise; easy.
Qed.

Definition swap_insert_iname_drop_iname {T M} n m a f :=
  eq_kmorph_expand
    (@swap_insert_iname_drop_iname_pointwise T M n m a f).

Lemma swap_insert_iname_rename_iname_pointwise {T M} n a m o
      (f : iname T M) :
  insert_iname n a (rename_iname m o f)
  =km= rename_iname (shift_name n m) (shift_name n o)
         (insert_iname
            (rename_name (shift_name n m) (shift_name n o) n) a f).
Proof.
  unfold rename_iname.
  rewrite swap_insert_iname_insert_iname_pointwise.
  rewrite swap_insert_iname_drop_iname_pointwise.
  rewrite swap_get_iname_insert_iname_pointwise
    by auto using rename_name_neq, shift_name_neq.
  case_order n m;
    case_order n o; try easy;
      case_order (pred n) o; try easy.
  rewrite swap_drop_iname_insert_iname_pointwise by omega.
  rewrite swap_drop_iname_insert_iname_pointwise by omega.
  autorewrite with rw_inames.
  easy.
Qed.

Definition swap_insert_iname_rename_iname {T M} n a m o f :=
  eq_kmorph_expand
    (@swap_insert_iname_rename_iname_pointwise T M n a m o f).

Lemma swap_rename_iname_insert_iname_pointwise {T M} n m o a
      (f : iname T M) :
  m <> o ->
  rename_iname n m (insert_iname o a f)
  =km= insert_iname (rename_name m n o) a
         (rename_iname (unshift_name (unshift_name m o) n)
            (unshift_name o m) f).
Proof.
  intros; unfold rename_iname.
  rewrite swap_drop_iname_insert_iname_pointwise by easy.
  rewrite swap_insert_iname_insert_iname_pointwise.
  rewrite swap_get_iname_insert_iname_pointwise by easy.
  case_order n o;
    case_order m o; easy.
Qed.

Definition swap_rename_iname_insert_iname {T M} n m o a f :=
  fun V l Hneq =>
    eq_kmorph_expand
      (@swap_rename_iname_insert_iname_pointwise T M n m o a f Hneq)
      V l.

Lemma swap_drop_iname_rename_iname_pointwise {T M} n m o
      (f : iname T M) :
  n <> m ->
  drop_iname n (rename_iname m o f)
  =km= rename_iname
         (unshift_name n m) (unshift_name (unshift_name m n) o)
         (drop_iname (rename_name m o n) f).
Proof.
  intros; unfold rename_iname.
  rewrite swap_drop_iname_insert_iname_pointwise by easy.
  rewrite swap_drop_iname_drop_iname_pointwise.
  rewrite swap_get_iname_drop_iname_pointwise.
  case_order n o;
    case_order n m; try easy.
Qed.

Definition swap_drop_iname_rename_iname {T M} n m o f :=
  fun V l Hneq =>
    eq_kmorph_expand
      (@swap_drop_iname_rename_iname_pointwise T M n m o f Hneq)
      V l.

Lemma swap_rename_iname_drop_iname_pointwise {T M} n m o
      (f : iname T M) :
  rename_iname n m (drop_iname o f)
  =km= drop_iname (shift_name n (unshift_name m o))
         (rename_iname 
            (shift_name (shift_name n (unshift_name m o)) n)
            (shift_name o m) f).
Proof.
  intros; unfold rename_iname.
  rewrite swap_drop_iname_drop_iname_pointwise.
  rewrite swap_get_iname_drop_iname_pointwise by easy.
  rewrite swap_insert_iname_drop_iname_pointwise by easy.
  easy.
Qed.

Definition swap_rename_iname_drop_iname {T M} n m o f :=
  eq_kmorph_expand
    (@swap_rename_iname_drop_iname_pointwise T M n m o f).

Add swap rules for rename_iname.

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

Definition tl_ilevel {N T M} (f : ilevel (S N) T M) : ilevel N T M :=
  fun V l => f V (lS l).

Definition cons_ilevel {N} {T : nset} {M} (a : pnset T M)
           (f : ilevel N T M)
  : ilevel (S N) T M :=
  fun V l =>
    match l with
    | l0 => a V
    | lS l => f V l
    end.

Arguments hd_ilevel {N T M} f V /.
Arguments tl_ilevel {N T M} f V l /.
Arguments cons_ilevel {N T M} a f V !l.

(* Morphism definitions *)

Add Parametric Morphism {N} {T : nset} {M} : (@hd_ilevel N T M)
    with signature eq_morph ==> eq_pnset
      as hd_ilevel_mor.
  intros * Heq; unfold hd_ilevel; intro.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {N} {T : nset} {M} : (@tl_ilevel N T M)
    with signature eq_morph ==> eq_morph
      as tl_ilevel_mor.
  intros * Heq V l; unfold tl_ilevel.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {N} {T : nset} {M} : (@cons_ilevel N T M)
    with signature eq_pnset ==> eq_morph ==> eq_morph
    as cons_ilevel_mor.
  intros * Heq1 * Heq2 V l; unfold cons_ilevel.
  destruct l; rewrite ?Heq1, ?Heq2; easy.
Qed.

(* The idenitity [ilevel] *)

Definition id_ilevel : ilevel 0 level 0 :=
  fun V l => l.
Arguments id_ilevel V l /.

(* Beta and eta rules for [ilevel] operations *)

Lemma ilevel_beta_hd {N} {T : nset} {M} (a : forall V, T (M + V))
      (f : ilevel N T M) :
  hd_ilevel (cons_ilevel a f) = a.
Proof. easy. Qed.

Lemma ilevel_beta_tl {N} {T : nset} {M} (a : forall V, T (M + V))
      (f : ilevel N T M) :
  tl_ilevel (cons_ilevel a f) = f.
Proof. easy. Qed.

Lemma ilevel_eta_pointwise {N} {T : nset} {M} (f : ilevel (S N) T M) :
  cons_ilevel (hd_ilevel f) (tl_ilevel f) =m= f.
Proof.
  intros V l.
  destruct l; cbn; easy.
Qed.

Definition ilevel_eta {N T M} f :=
  eq_morph_expand (@ilevel_eta_pointwise N T M f).

Hint Rewrite @ilevel_beta_hd @ilevel_beta_tl @ilevel_eta
  : rw_ilevels.

Hint Rewrite @ilevel_eta_pointwise
  : rw_ilevels_pointwise.

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

Definition pair_ivar {N} {T : nset} {M}
             (f : iname T M) (g : ilevel N T M) : ivar N T M :=
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
    (drop_iname n (fst_ivar f))
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

Add the derived derived operations.

(* Morphism definitions *)

Add Parametric Morphism {N} {T : nset} {M} : (@fst_ivar N T M)
    with signature eq_morph ==> eq_kmorph
    as fst_ivar_mor.
  intros * Heq V n; unfold fst_ivar.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {N} {T : nset} {M} : (@snd_ivar N T M)
    with signature eq_morph ==> eq_morph
    as snd_ivar_mor.
  intros * Heq V n; unfold snd_ivar.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {N} {T : nset} {M} : (@pair_ivar N T M)
    with signature eq_kmorph ==> eq_morph ==> eq_morph
    as pair_ivar_mor.
  intros * Heq1 f g Heq2 V v; unfold pair_ivar.
  destruct v; rewrite ?Heq1, ?Heq2; easy.
Qed.

Add Parametric Morphism {N} {T : nset} {M} n : (@open_ivar N T M n)
    with signature eq_morph ==> eq_morph
    as open_ivar_mor.
  intros * Heq V v; unfold open_ivar.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {N} {T : nset} {M} n : (@close_ivar N T M n)
    with signature eq_morph ==> eq_morph
    as close_ivar_mor.
  intros * Heq V v; unfold close_ivar.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {N} {T : nset} {M} : (@weak_ivar N T M)
    with signature eq_morph ==> eq_morph
    as weak_ivar_mor.
  intros * Heq V v; unfold weak_ivar.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {N} {T : nset} {M} : (@bind_ivar N T M)
    with signature eq_pnset ==> eq_morph ==> eq_morph
    as bind_ivar_mor.
  intros * Heq1 * Heq2 V v; unfold bind_ivar.
  rewrite Heq1, Heq2; easy.
Qed.

Add morphisms for the derived derived operations.

(* The identity [ivar] *)

Definition id_ivar : ivar 0 var 0 :=
  fun V v => v.
Arguments id_ivar V v /.

(* Useful functions on [var]s *)

Definition open_var n :=
  open_ivar n id_ivar.

Definition close_var n :=
  close_ivar n (morph_extend id_ivar).

Definition weak_var :=
  weak_ivar (morph_extend id_ivar).

Definition bind_var a :=
  bind_ivar a id_ivar.

Add name versions of the derived derived operations.

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
  : rw_ivars.

Hint Rewrite @ivar_eta_pointwise
  : rw_ivars_pointwise.

(* Corollaries of the beta and eta rules *)

Lemma ivar_beta_open_pair_pointwise {N T M} n f (g : ilevel N T M) :
  open_ivar n (pair_ivar f g)
  =m= pair_ivar (drop_iname n f) (cons_ilevel (get_iname n f) g).
Proof.
  unfold open_ivar.
  autorewrite with rw_ivars; easy.
Qed.

Definition ivar_beta_open_pair {N T M} n f g :=
  eq_morph_expand (@ivar_beta_open_pair_pointwise N T M n f g).

Lemma ivar_beta_close_pair_pointwise {N T M} n f
      (g : ilevel (S N) T M) :
  close_ivar n (pair_ivar f g)
  =m= pair_ivar (insert_iname n (hd_ilevel g) f) (tl_ilevel g).
Proof.
  unfold close_ivar.
  autorewrite with rw_ivars; easy.
Qed.

Definition ivar_beta_close_pair {N T M} n f g :=
  eq_morph_expand (@ivar_beta_close_pair_pointwise N T M n f g).

Lemma ivar_beta_weak_pair_pointwise {N T M} f (g : ilevel (S N) T M) :
  weak_ivar (pair_ivar f g)
  =m= pair_ivar f (tl_ilevel g).
Proof.
  unfold weak_ivar.
  autorewrite with rw_ivars; easy.
Qed.

Definition ivar_beta_weak_pair {N T M} f g :=
  eq_morph_expand (@ivar_beta_weak_pair_pointwise N T M f g).

Lemma ivar_beta_bind_pair_pointwise {N T M} a f (g : ilevel N T M) :
  bind_ivar a (pair_ivar f g)
  =m= pair_ivar f (cons_ilevel a g).
Proof.
  unfold bind_ivar.
  autorewrite with rw_ivars; easy.
Qed.

Definition ivar_beta_bind_pair {N T M} a f g :=
  eq_morph_expand (@ivar_beta_bind_pair_pointwise N T M a f g).

Lemma ivar_beta_open_close_pointwise {N T M} n (f : ivar (S N) T M) :
  open_ivar n (close_ivar n f) =m= f.
Proof.
  unfold open_ivar, close_ivar.
  autorewrite with rw_ivars rw_ivars_pointwise
    rw_inames_pointwise rw_ilevels_pointwise; easy.
Qed.

Definition ivar_beta_open_close {N T M} n f :=
  eq_morph_expand (@ivar_beta_open_close_pointwise N T M n f).

Lemma ivar_beta_close_open_pointwise {N T M} n (f : ivar N T M) :
  close_ivar n (open_ivar n f) =m= f.
Proof.
  unfold open_ivar, close_ivar.
  autorewrite with rw_ivars rw_ivars_pointwise
    rw_inames_pointwise rw_ilevels; easy.
Qed.

Definition ivar_beta_close_open {N T M} n f :=
  eq_morph_expand (@ivar_beta_close_open_pointwise N T M n f).

Lemma ivar_beta_weak_bind_pointwise {N T M} a (f : ivar N T M) :
  weak_ivar (bind_ivar a f) =m= f.
Proof.
  unfold weak_ivar, bind_ivar.
  autorewrite with rw_ivars rw_ivars_pointwise rw_ilevels; easy.
Qed.

Definition ivar_beta_weak_bind {N T M} a f :=
  eq_morph_expand (@ivar_beta_weak_bind_pointwise N T M a f).

Add beta rules for the derived derived operations.

