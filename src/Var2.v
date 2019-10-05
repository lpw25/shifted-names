Require Import String Omega Morph Setoid Morphisms.
Arguments string_dec !s1 !s2.

(* Pointwise equality *)

Notation "f =p= g" :=
  (pointwise_relation _ eq f g)
    (at level 70).

Add Parametric Morphism {A B} : (@pointwise_relation A B eq)
  with signature
    (pointwise_relation A eq ==>
       pointwise_relation A eq ==>
         Basics.impl)
    as pointwise_relation_index_mor.
  unfold pointwise_relation; intros.
  intro. intro.
  rewrite <- H.
  rewrite <- H0.
  easy.
Qed.

(* Pointwise equality for nsets *)

Notation "f =pn= g" :=
  (forall_relation
     (fun V => pointwise_relation (_ (_ + V)) eq) f g)
    (at level 70).

(* Name indices are [nat]s *)
Definition index := nat.

(* Liftable functions from [index]s to nsets that we treat
   like streams *)
Definition iindex (T : nset) M := forall V, index -> T (M + V).

Definition get_idx {T M} (i : index) (f : iindex T M) :=
  fun V => f V i.
Arguments get_idx {T M} i f V /.

Definition drop_idx {T M} (i : index) (f : iindex T M) :
  iindex T M :=
  fun V (j : index) =>
    if Compare_dec.le_lt_dec i j then get_idx (S j) f V
    else get_idx j f V.

Definition insert_idx {T : nset} {M} (i : index)
           (a : forall V, T (M + V)) (f : iindex T M)
  : iindex T M :=
  fun V (j : index) =>
    match Compare_dec.lt_eq_lt_dec i j with
    | inleft (left _) => get_idx (pred j) f V
    | inleft (right _) => a V
    | inright _ => get_idx j f V
    end.  

(* Morphism definitions *)

Add Parametric Morphism {T : nset} {M} i : (@get_idx T M i)
    with signature
      (forall_relation
         (fun V => pointwise_relation index (@eq (T (M + V))))
         ==> forall_relation (fun V => @eq (T (M + V))))
    as get_idx_mor.
  intros * Heq *; intro V. cbn.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {A} i : (@drop_idx A i)
    with signature
      (pointwise_relation index eq ==>
          pointwise_relation index eq)
    as drop_idx_mor.
  intros * Heq; intro; unfold drop_idx; cbn.
  rewrite Heq, Heq; easy.
Qed.

Add Parametric Morphism {A} i : (@drop_idx A i)
    with signature
      (pointwise_relation index eq ==> eq ==> eq)
    as drop_idx_mor_eta.
  apply drop_idx_mor.
Qed.

Add Parametric Morphism {A} i a : (@insert_idx A i a)
    with signature
      (pointwise_relation index eq ==>
          pointwise_relation index eq)
    as insert_idx_mor.
  intros * Heq; intro; unfold insert_idx; cbn.
  rewrite Heq, Heq; easy.
Qed.

Add Parametric Morphism {A} i a : (@insert_idx A i a)
    with signature
      (pointwise_relation index eq ==> eq ==> eq)
    as insert_idx_mor_eta.
  apply insert_idx_mor.
Qed.

(* Useful [iindex index]s *)

Definition id_idx : iindex index :=
  fun (j : index) => j.
Arguments id_idx j /.

Definition shift_idx (i : index) :=
  drop_idx i id_idx.

Definition unshift_idx (i : index) :=
  insert_idx i i id_idx.

(* Reductions *)

Lemma rw_drop_idx_ge {A} i (f : iindex A) j :
  i <= j ->
  drop_idx i f j = f (S j).
Proof.
  intros; unfold drop_idx.
  destruct (le_lt_dec i j); try easy; omega.
Qed.

Lemma rw_drop_idx_lt {A} i (f : iindex A) j :
  S j <= i ->
  drop_idx i f j = f j.
Proof.
  intros; unfold drop_idx.
  destruct (le_lt_dec i j); try easy; omega.
Qed.

Lemma rw_drop_idx_same {A} i (f : iindex A) :
  drop_idx i f i = f (S i).
Proof.
  apply rw_drop_idx_ge; auto.
Qed.

Lemma rw_insert_idx_gt {A} i a (f : iindex A) j :
  S i <= j ->
  insert_idx i a f j = f (pred j).
Proof.
  intros; unfold insert_idx.
  destruct (lt_eq_lt_dec i j) as [[|]|]; try easy; omega.
Qed.

Lemma rw_insert_idx_eq {A} i a (f : iindex A) j :
  i = j ->
  insert_idx i a f j = a.
Proof.
  intros; unfold insert_idx.
  destruct (lt_eq_lt_dec i j) as [[|]|]; try easy; omega.
Qed.

Lemma rw_insert_idx_lt {A} i a (f : iindex A) j :
  S j <= i ->
  insert_idx i a f j = f j.
Proof.
  intros; unfold insert_idx.
  destruct (lt_eq_lt_dec i j) as [[|]|]; try easy; omega.
Qed.

Lemma rw_insert_idx_same {A} i a (f : iindex A) :
  insert_idx i a f i = a.
Proof.
  apply rw_insert_idx_eq; auto.
Qed.

Lemma rw_shift_idx_ge i j :
  i <= j ->
  shift_idx i j = S j.
Proof.
  intros; unfold shift_idx.
  rewrite rw_drop_idx_ge; easy.
Qed.

Lemma rw_shift_idx_lt i j :
  S j <= i ->
  shift_idx i j = j.
Proof.
  intros; unfold shift_idx.
  rewrite rw_drop_idx_lt; easy.
Qed.

Lemma rw_shift_idx_same i :
  shift_idx i i = S i.
Proof.
  apply rw_shift_idx_ge; auto.
Qed.

Lemma rw_unshift_idx_gt i j :
  S i <= j ->
  unshift_idx i j = pred j.
Proof.
  intros; unfold unshift_idx.
  rewrite rw_insert_idx_gt; easy.
Qed.

Lemma rw_unshift_idx_le i j :
  j <= i ->
  unshift_idx i j = j.
Proof.
  intros; unfold unshift_idx.
  destruct (Compare_dec.le_lt_dec i j).
  - rewrite rw_insert_idx_eq; omega.
  - rewrite rw_insert_idx_lt; easy.
Qed.

Lemma rw_unshift_idx_same i :
  unshift_idx i i = i.
Proof.
  apply rw_unshift_idx_le; auto.
Qed.

(* Useful lemma about predecessor and successor *)
Lemma rw_succ_pred i :
  0 < i ->
  S (pred i) = i.
Proof.
  intros; omega.
Qed.

Hint Rewrite @rw_drop_idx_same @rw_insert_idx_same
     @rw_shift_idx_same @rw_unshift_idx_same
  : rw_idxs.

Hint Rewrite @rw_drop_idx_ge @rw_drop_idx_lt @rw_insert_idx_gt
     @rw_insert_idx_eq @rw_insert_idx_lt @rw_shift_idx_ge
     @rw_shift_idx_lt @rw_unshift_idx_le @rw_unshift_idx_gt
     @rw_succ_pred using omega : rw_idxs.

(* Case split on the order of the parameters, then simplify any
   index operations affected by the ordering. *)
Ltac case_order i j :=
  destruct (Compare_dec.lt_eq_lt_dec i j) as [[|]|]; try omega;
  repeat progress (autorewrite with rw_idxs; cbn).

(* Beta and eta rules for [iindex] operations *)

Lemma iindex_beta_get {A} i (a : A) f :
  get_idx i (insert_idx i a f) = a.
Proof.
  cbn; autorewrite with rw_idxs; easy.
Qed.

Lemma iindex_beta_drop {A} i (a : A) f :
  drop_idx i (insert_idx i a f) =p= f.
Proof.
  intro j.
  case_order i j; easy.
Qed.

Lemma iindex_eta {A} i (f : iindex A) :
  insert_idx i (get_idx i f) (drop_idx i f) =p= f.
Proof.
  intro j.
  case_order i j; f_equal; omega.
Qed.

Hint Rewrite @iindex_beta_get @iindex_beta_drop @iindex_eta
  : rw_idxs.

(* Commuting [iindex] operations *)

Lemma swap_drop_idx_drop_idx {A} i j (f : iindex A) :
  drop_idx i (drop_idx j f)
  =p= drop_idx (unshift_idx i j)
        (drop_idx (shift_idx j i) f).
Proof.
  intro k.
  case_order i j;
    case_order j k; try easy;
      case_order i k; try easy;
        case_order j (S k); easy.
Qed.

Lemma swap_insert_idx_insert_idx {A} i a j b (f : iindex A) :
  insert_idx i a (insert_idx j b f)
  =p= insert_idx (shift_idx i j) b
      (insert_idx (unshift_idx j i) a f).
Proof.
  intro k.
  case_order i j;
    case_order j k; try easy;
      case_order i k; try easy;
        case_order j (pred k); easy.
Qed.

Lemma swap_drop_idx_insert_idx {A} i j a (f : iindex A) :
  i <> j ->
  drop_idx i (insert_idx j a f)
  =p= insert_idx (unshift_idx i j) a
        (drop_idx (unshift_idx j i) f).
Proof.
  intros Hneq k.
  case_order i j; try contradiction;
    case_order i k; try easy;
      case_order j k; try easy;
        case_order j (S k); easy.     
Qed.

Lemma swap_insert_idx_drop_idx {A} i j a (f : iindex A) :
  insert_idx i a (drop_idx j f)
  =p= drop_idx (shift_idx i j)
      (insert_idx (shift_idx (shift_idx i j) i) a f).
Proof.
  intro k.
  case_order i j;
    case_order i k; try easy;
      case_order j k; try easy.
Qed.

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

(* Functions from [names]s that we treat like direct
   sums of streams *)
Definition iname A := name -> A.

Definition project_name {A} s (f : iname A) : iindex A :=
  fun (i : index) => f (mkname s i).
Arguments project_name {A} s f i /.

Definition with_name {A} s (f : iindex A) (g : iname A)
  : iname A :=
  fun (n : name) =>
    if string_dec (n_string n) s then get_idx (n_index n) f
    else g n.

Definition get_name {A} (n : name) (f : iname A) :=
  get_idx (n_index n) (project_name (n_string n) f).

Definition drop_name {A} (n : name) (f : iname A) : iname A :=
  with_name (n_string n)
    (drop_idx (n_index n) (project_name (n_string n) f)) f.

Definition insert_name {A} (n : name) (a : A) (f : iname A)
  : iname A :=
  with_name (n_string n)
    (insert_idx (n_index n) a (project_name (n_string n) f)) f.

(* Morphism definitions *)

Add Parametric Morphism {A} s : (@project_name A s)
    with signature
      (pointwise_relation name eq ==>
         pointwise_relation index eq)
    as project_name_mor.
  intros; unfold project_name; easy.
Qed.

Add Parametric Morphism {A} s : (@project_name A s)
    with signature
      (pointwise_relation name eq ==> eq ==> eq)
    as project_name_mor_eta.
  apply project_name_mor.
Qed.

Add Parametric Morphism {A} s : (@with_name A s)
    with signature
      (pointwise_relation index eq ==>
         pointwise_relation name eq ==>
           pointwise_relation name eq)
    as with_name_mor.
  intros * Heq1 * Heq2; unfold with_name; cbn.
  intro; rewrite Heq1, Heq2; easy.
Qed.

Add Parametric Morphism {A} s : (@with_name A s)
    with signature
      (pointwise_relation index eq ==>
         pointwise_relation name eq ==> eq ==> eq)
    as with_name_mor_eta.
  apply with_name_mor.
Qed.

Add Parametric Morphism {A} n : (@get_name A n)
    with signature
      (pointwise_relation name eq ==> eq)
    as get_name_mor.
  intros; unfold get_name; cbn; easy.
Qed.

Add Parametric Morphism {A} n : (@drop_name A n)
    with signature
      (pointwise_relation name eq ==>
          pointwise_relation name eq)
    as drop_name_mor.
  intros * Heq; intro; unfold drop_name; cbn.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {A} i : (@drop_name A i)
    with signature
      (pointwise_relation name eq ==> eq ==> eq)
    as drop_name_mor_eta.
  apply drop_name_mor.
Qed.

Add Parametric Morphism {A} n a : (@insert_name A n a)
    with signature
      (pointwise_relation name eq ==>
          pointwise_relation name eq)
    as insert_name_mor.
  intros * Heq; intro; unfold insert_name; cbn.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {A} i a : (@insert_name A i a)
    with signature
      (pointwise_relation name eq ==> eq ==> eq)
    as insert_name_mor_eta.
  apply insert_name_mor.
Qed.

(* Useful [iname name]s *)

Definition id_name : iname name :=
  fun (j : name) => j.
Arguments id_name j /.

Definition shift_name (n : name) :=
  drop_name n id_name.

Definition unshift_name (n : name) :=
  insert_name n n id_name.

(* Reductions *)

Lemma rw_with_name_eq {A} s f (g : iname A) n :
  s = n_string n ->
  with_name s f g n = f (n_index n).
Proof.
  intro Heq; subst; unfold with_name.
  destruct (string_dec (n_string n) (n_string n));
    try contradiction; easy.
Qed.

Lemma rw_with_name_neq {A} s f (g : iname A) n :
  s <> n_string n ->
  with_name s f g n = g n.
Proof.
  intro Heq; unfold with_name.
  destruct (string_dec (n_string n) s); subst;
    try contradiction; easy.
Qed.

Lemma rw_with_name_same {A} f (g : iname A) n :
  with_name (n_string n) f g n = f (n_index n).
Proof.
  apply rw_with_name_eq; easy.
Qed.

Lemma rw_get_name {A} n (f : iname A) :
  get_name n f = f n.
Proof.
  unfold get_name; easy.
Qed.

Lemma rw_drop_name_indistinct {A} n (f : iname A) m :
  n_string n = n_string m ->
  drop_name n f m
  = drop_idx (n_index n) (project_name (n_string n) f) (n_index m).
Proof.
  intro Heq; unfold drop_name.
  rewrite rw_with_name_eq; easy.
Qed.

Lemma rw_drop_name_distinct {A} n (f : iname A) m :
  n_string n <> n_string m ->
  drop_name n f m = f m.
Proof.
  intro Heq; unfold drop_name.
  rewrite rw_with_name_neq; easy.
Qed.

Lemma rw_drop_name_same {A} n (f : iname A) :
  drop_name n f n
  = f (mkname (n_string n) (S (n_index n))).
Proof.
  rewrite rw_drop_name_indistinct by easy.
  rewrite rw_drop_idx_same; easy.
Qed.

Lemma rw_insert_name_indistinct {A} n a (f : iname A) m :
  n_string n = n_string m ->
  insert_name n a f m
  = insert_idx (n_index n) a
      (project_name (n_string n) f) (n_index m).
Proof.
  intro Heq; unfold insert_name.
  rewrite rw_with_name_eq; easy.
Qed.

Lemma rw_insert_name_distinct {A} n a (f : iname A) m :
  n_string n <> n_string m ->
  insert_name n a f m = f m.
Proof.
  intro Heq; unfold insert_name.
  rewrite rw_with_name_neq; easy.
Qed.

Lemma rw_insert_name_same {A} n a (f : iname A) :
  insert_name n a f n = a.
Proof.
  rewrite rw_insert_name_indistinct by easy.
  rewrite rw_insert_idx_same; easy.
Qed.

Lemma rw_shift_name_indistinct n m :
  n_string n = n_string m ->
  shift_name n m
  = mkname (n_string m) (shift_idx (n_index n) (n_index m)).
Proof.
  intro Heq; unfold shift_name.
  rewrite rw_drop_name_indistinct by easy.
  case_order (n_index n) (n_index m); rewrite Heq; easy.
Qed.

Lemma rw_shift_name_distinct n m :
  n_string n <> n_string m ->
  shift_name n m = m.
Proof.
  intro Heq; unfold shift_name.
  rewrite rw_drop_name_distinct by easy; easy.
Qed.

Lemma rw_shift_name_same n :
  shift_name n n
  = mkname (n_string n) (S (n_index n)).
Proof.
  rewrite rw_shift_name_indistinct by easy.
  rewrite rw_shift_idx_same; easy.
Qed.

Lemma rw_unshift_name_indistinct n m :
  n_string n = n_string m ->
  unshift_name n m
  = mkname (n_string m) (unshift_idx (n_index n) (n_index m)).
Proof.
  intro Heq; unfold unshift_name.
  rewrite rw_insert_name_indistinct by easy.
  case_order (n_index n) (n_index m);
    rewrite <- Heq; try easy.
  replace (n_index m) with (n_index n) by easy; easy.
Qed.

Lemma rw_unshift_name_distinct n m :
  n_string n <> n_string m ->
  unshift_name n m = m.
Proof.  
  intro Heq; unfold unshift_name.
  rewrite rw_insert_name_distinct by easy; easy.
Qed.

Lemma rw_unshift_name_same n :
  unshift_name n n = n.
Proof.
  rewrite rw_unshift_name_indistinct by easy.
  rewrite rw_unshift_idx_same; easy.
Qed.

Hint Rewrite @rw_get_name @rw_with_name_same
     @rw_drop_name_same @rw_insert_name_same
     @rw_shift_name_same @rw_unshift_name_same
  : rw_names.

Hint Rewrite @rw_with_name_eq @rw_with_name_neq
     @rw_drop_name_distinct @rw_drop_name_indistinct
     @rw_insert_name_distinct @rw_insert_name_indistinct
     @rw_shift_name_distinct @rw_shift_name_indistinct
     @rw_unshift_name_distinct @rw_unshift_name_indistinct
     using (cbn; congruence) : rw_names.

(* Case split on the equality of the string parameters, then simplify
   any name operations affected by the ordering. *)
Ltac case_string s1 s2 :=
  destruct (string_dec s1 s2); try contradiction;
  repeat progress (autorewrite with rw_names; cbn).

(* Beta and eta rules for [iname] operations *)

Lemma iname_beta_project_same {A} s f (g : iname A) :
  project_name s (with_name s f g) =p= f.
Proof.
  intro n; cbn; autorewrite with rw_names; easy.
Qed.

Lemma iname_beta_project_neq {A} s t f (g : iname A) :
  s <> t ->
  project_name s (with_name t f g) =p= project_name s g.
Proof.
  intros; intro; cbn; autorewrite with rw_names; easy.
Qed.

Lemma iname_beta_with_same {A} s f g (h : iname A) :
  with_name s f (with_name s g h)
  =p= with_name s f h.
Proof.
  intro n.
  case_string s (n_string n); easy.
Qed.

Lemma iname_eta {A} s (f : iname A) :
  with_name s (project_name s f) f =p= f.
Proof.
  intro n.
  case_string s (n_string n); subst; easy.
Qed.

Hint Rewrite @iname_beta_project_same @iname_beta_with_same @iname_eta
  : rw_names.

Hint Rewrite @iname_beta_project_neq
  using (cbn; congruence) : rw_names.

(* Corollaries of the beta rules *)

Lemma iname_beta_project_drop_eq {A} s n (f : iname A) :
  s = n_string n ->
  project_name s (drop_name n f)
  =p= drop_idx (n_index n) (project_name (n_string n) f).
Proof.
  intro; unfold drop_name; subst.
  autorewrite with rw_names; easy.
Qed.

Lemma iname_beta_project_drop_neq {A} s n (f : iname A) :
  s <> n_string n ->
  project_name s (drop_name n f)
  =p= project_name s f.
Proof.
  intro; unfold drop_name.
  autorewrite with rw_names; easy.
Qed.

Lemma iname_beta_project_insert_eq {A} s n a (f : iname A) :
  s = n_string n ->
  project_name s (insert_name n a f)
  =p= insert_idx (n_index n) a (project_name (n_string n) f).
Proof.
  intro; unfold insert_name; subst.
  autorewrite with rw_names; easy.
Qed.

Lemma iname_beta_project_insert_neq {A} s n a (f : iname A) :
  s <> n_string n ->
  project_name s (insert_name n a f)
  =p= project_name s f.
Proof.
  intro; unfold insert_name.
  autorewrite with rw_names; easy.
Qed.

Hint Rewrite @iname_beta_project_drop_eq @iname_beta_project_drop_neq
     @iname_beta_project_insert_eq @iname_beta_project_insert_neq
  using (cbn; congruence) : rw_names.

Lemma iname_beta_get {A} n (a : A) f :
  get_name n (insert_name n a f) = a.
Proof.
  autorewrite with rw_names rw_idxs; easy.
Qed.

Lemma iname_beta_drop {A} n (a : A) f :
  drop_name n (insert_name n a f) =p= f.
Proof.
  intro m.
  case_string (n_string n) (n_string m); try easy.
  autorewrite with rw_idxs; cbn.
  replace (n_string n) with (n_string m) by easy; easy.
Qed.

Lemma iname_insert_eta {A} n (f : iname A) :
  insert_name n (get_name n f) (drop_name n f) =p= f.
Proof.
  intro m.
  case_string (n_string n) (n_string m); try easy.
  replace (f n)
    with (get_idx (n_index n) (project_name (n_string n) f)) by easy.
  autorewrite with rw_idxs; cbn.
  replace (n_string n) with (n_string m); easy.
Qed.

Hint Rewrite @iname_beta_get @iname_beta_drop @iname_insert_eta
  : rw_names.

(* Commuting [iname] operations *)

Lemma swap_with_name_with_name {A} s li t lj (ln : iname A) :
  s <> t ->
  with_name s li (with_name t lj ln)
  =p= with_name t lj (with_name s li ln).
Proof.
  intros Hneq n.
  case_string s (n_string n); try easy.
  case_string t (n_string n); easy.
Qed.

Lemma swap_drop_name_drop_name {A} n m (f : iname A) :
  drop_name n (drop_name m f)
  =p= drop_name (unshift_name n m) (drop_name (shift_name m n) f).
Proof.
  intro o.
  case_string (n_string n) (n_string m).
  - case_string (n_string m) (n_string o); try easy.
    rewrite swap_drop_idx_drop_idx.
    replace (n_string n) with (n_string m) by easy; easy.
  - unfold drop_name.
    rewrite swap_with_name_with_name by easy.
    autorewrite with rw_names; easy.
Qed.

Lemma swap_insert_name_insert_name {A} n a m b (f : iname A) :
  insert_name n a (insert_name m b f)
  =p= insert_name (shift_name n m) b
      (insert_name (unshift_name m n) a f).
Proof.
  intro o.
  case_string (n_string n) (n_string m).
  - case_string (n_string m) (n_string o); try easy.
    rewrite swap_insert_idx_insert_idx.
    replace (n_string n) with (n_string m) by easy; easy.
  - unfold insert_name.
    rewrite swap_with_name_with_name by easy.
    autorewrite with rw_names; easy.
Qed.

Lemma swap_drop_name_insert_name {A} n m a (f : iname A) :
  n <> m ->
  drop_name n (insert_name m a f)
  =p= insert_name (unshift_name n m) a
        (drop_name (unshift_name m n) f).
Proof.
  intros Hneq o.
  case_string (n_string n) (n_string m).
  - case_string (n_string n) (n_string o); try easy.
    rewrite swap_drop_idx_insert_idx
      by auto using name_neq_string_eq_index_neq.
    replace (n_string n) with (n_string m) by easy; easy.
  - unfold drop_name, insert_name.
    rewrite swap_with_name_with_name by easy.
    autorewrite with rw_names; easy.
Qed.

Lemma swap_insert_name_drop_name {A} n m a (f : iname A) :
  insert_name n a (drop_name m f)
  =p= drop_name (shift_name n m)
      (insert_name (shift_name (shift_name n m) n) a f).
Proof.
  intro o.
  case_string (n_string n) (n_string m).
  - case_string (n_string n) (n_string o); try easy.
    rewrite swap_insert_idx_drop_idx.
    replace (n_string n) with (n_string m) by easy; easy.
  - unfold drop_name, insert_name.
    rewrite swap_with_name_with_name by easy.
    autorewrite with rw_names; easy.
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

Definition hd_level {N T M} (f : ilevel (S N) T M)
  : forall V, T (M + V) :=
  fun V => @f V l0.

Definition tl_level {N T M} (f : ilevel (S N) T M)
  : ilevel N T M :=
  fun V l => f V (lS l).

Definition cons_level {N} {T : nset} {M}
  (a : forall V, T (M + V)) (f : ilevel N T M)
  : ilevel (S N) T M :=
  fun V l =>
    match l with
    | l0 => a V
    | lS l => f V l
    end.

Arguments hd_level {N T M} f V /.
Arguments tl_level {N T M} f V l /.
Arguments cons_level {N T M} a f V !l.

(* Morphism definitions *)

Add Parametric Morphism {N} {T : nset} {M} : (@hd_level N T M)
    with signature
      (forall_relation
         (fun V => pointwise_relation (level (S N + V)) eq)
         ==>
         (forall_relation
            (fun V => @eq (T (M + V)))))
    as hd_level_mor.
  intros * Heq; unfold hd_level; intro.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {N} {T : nset} {M} : (@tl_level N T M)
    with signature
      (forall_relation
         (fun V => pointwise_relation (level (S N + V)) eq)
         ==>
         (forall_relation
            (fun V => pointwise_relation (level (N + V)) eq)))
    as tl_level_mor.
  intros * Heq; intro; intro; unfold tl_level; cbn.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {N} {T : nset} {M} : (@cons_level N T M)
    with signature
      (forall_relation
         (fun V => @eq (T (M + V)))
        ==>
        (forall_relation
           (fun V => pointwise_relation (level (N + V)) eq)
           ==>
           (forall_relation
              (fun V => pointwise_relation (level (S N + V)) eq))))
    as cons_level_mor.
  intros * Heq1 * Heq2; intro a; intro b; unfold cons_level.
  destruct b; rewrite ?Heq1, ?Heq2; easy.
Qed.

(* Useful [ilevel level]s *)

Definition id_level {N} : ilevel N level N :=
  fun V l => l.
Arguments id_level {N} V l /.

Definition shift_level {N} :=
  tl_level (@id_level (S N)).

Definition unshift_level N : ilevel (S (S N)) level (S N) :=
  @cons_level (S N) level (S N) (fun V => l0) (@id_level (S N)).

(* Beta and eta rules for [ilevel] operations *)

Lemma ilevel_beta_hd {N} {T : nset} {M} (a : forall V, T (M + V))
      (f : ilevel N T M) :
  hd_level (cons_level a f) = a.
Proof. easy. Qed.

Lemma ilevel_beta_tl {N} {T : nset} {M} (a : forall V, T (M + V))
      (f : ilevel N T M) :
  tl_level (cons_level a f) = f.
Proof. easy. Qed.

Lemma ilevel_eta {N} {T : nset} {M} (f : ilevel (S N) T M) :
  cons_level (hd_level f) (tl_level f) =pn= f.
Proof.
  intros V l.
  destruct l; cbn; easy.
Qed.

Hint Rewrite @ilevel_beta_hd @ilevel_beta_tl @ilevel_eta
  : rw_levels.

(* Variables are either free names or bound levels *)

Inductive var (V : nat) :=
| free (n : name)
| bound (l : level V).

Arguments free {V} n.
Arguments bound {V} l.

(* Liftable morphisms from [var]s that we treat like pairs *)
Definition ivar N T M := morph var N T M.

Definition fst_var {N T M} (f : ivar N T M) :
  forall V, iname (T (M + V)) :=
    fun V (n : name) => f V (free n).

Definition snd_var {N T M} (f : ivar N T M) : ilevel N T M :=
    fun V (l : level (N + V)) => f V (bound l).

Definition pair_var {N} {T : nset} {M}
             (f : forall V, iname (T (M + V)))
             (g : ilevel N T M) : ivar N T M :=
  fun V v =>
    match v with
    | free n => f V n
    | bound l => g V l
    end.

Definition opn_var {N T M} n (f : ivar N T M)
  : ivar (S N) T M :=
  pair_var
    (fun V => drop_name n (fst_var f V))
    (cons_level (fun V => get_name n (fst_var f V)) (snd_var f)).

Definition cls_var {N T M} n (f : ivar (S N) T M)
  : ivar N T M :=
  pair_var
    (fun V => insert_name n (hd_level (snd_var f) V) (fst_var f V))
    (tl_level (snd_var f)).

Definition wk_var {N T M} (f : ivar (S N) T M)
  : ivar N T M :=
  pair_var (fst_var f) (tl_level (snd_var f)).

Definition bnd_var {N T M} a (f : ivar N T M)
  : ivar (S N) T M :=
  pair_var (fst_var f) (cons_level a (snd_var f)).

(* Morphism definitions *)

Add Parametric Morphism {N} {T : nset} {M} : (@hd_level N T M)
    with signature
      (forall_relation
         (fun V => pointwise_relation (level (S N + V)) eq)
         ==>
         (forall_relation
            (fun V => @eq (T (M + V)))))
    as hd_level_mor.
  intros * Heq; unfold hd_level; intro.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {N} {T : nset} {M} : (@tl_level N T M)
    with signature
      (forall_relation
         (fun V => pointwise_relation (level (S N + V)) eq)
         ==>
         (forall_relation
            (fun V => pointwise_relation (level (N + V)) eq)))
    as tl_level_mor.
  intros * Heq; intro; intro; unfold tl_level; cbn.
  rewrite Heq; easy.
Qed.

Add Parametric Morphism {N} {T : nset} {M} : (@cons_level N T M)
    with signature
      (forall_relation
         (fun V => @eq (T (M + V)))
        ==>
        (forall_relation
           (fun V => pointwise_relation (level (N + V)) eq)
           ==>
           (forall_relation
              (fun V => pointwise_relation (level (S N + V)) eq))))
    as cons_level_mor.
  intros * Heq1 * Heq2; intro a; intro b; unfold cons_level.
  destruct b; rewrite ?Heq1, ?Heq2; easy.
Qed.

(* Useful [ilevel level]s *)

Definition id_level {N} : ilevel N level N :=
  fun V l => l.
Arguments id_level {N} V l /.

Definition shift_level {N} :=
  tl_level (@id_level (S N)).

Definition unshift_level N : ilevel (S (S N)) level (S N) :=
  @cons_level (S N) level (S N) (fun V => l0) (@id_level (S N)).

(* Beta and eta rules for [ilevel] operations *)

Lemma ilevel_beta_hd {N} {T : nset} {M} (a : forall V, T (M + V))
      (f : ilevel N T M) :
  hd_level (cons_level a f) = a.
Proof. easy. Qed.

Lemma ilevel_beta_tl {N} {T : nset} {M} (a : forall V, T (M + V))
      (f : ilevel N T M) :
  tl_level (cons_level a f) = f.
Proof. easy. Qed.

Lemma ilevel_eta {N} {T : nset} {M} (f : ilevel (S N) T M) :
  cons_level (hd_level f) (tl_level f) =pn= f.
Proof.
  intros V l.
  destruct l; cbn; easy.
Qed.

Hint Rewrite @ilevel_beta_hd @ilevel_beta_tl @ilevel_eta
  : rw_levels.

