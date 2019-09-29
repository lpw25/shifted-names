Require Import String Omega Morph.
Arguments string_dec !s1 !s2.

(* Name indices are [nat]s *)
Definition index := nat.

(* Functions from [index]s that we treat like streams *)
Definition iindex A := index -> A.

Definition get_idx {A} (i : index) (l : iindex A) := l i.
Arguments get_idx {A} i l /.

Definition drop_idx {A} (i : index) (l : iindex A) : iindex A :=
  fun (j : index) =>
    if Compare_dec.le_lt_dec i j then get_idx (S j) l
    else get_idx j l.

Definition insert_idx {A} (i : index) (a : A) (l : iindex A)
  : iindex A :=
  fun (j : index) =>
    match Compare_dec.lt_eq_lt_dec i j with
    | inleft (left _) => get_idx (pred j) l
    | inleft (right _) => a
    | inright _ => get_idx j l
    end.  

(* Extensionality of these primitives *)

Lemma get_idx_ext {A} i (l1 : iindex A) l2 :
  (forall j, l1 j = l2 j) ->
  get_idx i l1 = get_idx i l2.
Proof. intro Heq; cbn; easy. Qed.

Lemma drop_idx_ext {A} i (l1 : iindex A) l2 j :
  (forall j, l1 j = l2 j) ->
  drop_idx i l1 j = drop_idx i l2 j.
Proof.
  intro Heq; unfold drop_idx; cbn.
  rewrite Heq, Heq; easy.
Qed.

Lemma insert_idx_ext {A} i a (l1 : iindex A) l2 j :
  (forall j, l1 j = l2 j) ->
  insert_idx i a l1 j = insert_idx i a l2 j.
Proof.
  intro Heq; unfold insert_idx; cbn.
  rewrite Heq, Heq; easy.
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

Lemma rw_drop_idx_ge {A} i (l : iindex A) j :
  i <= j ->
  drop_idx i l j = l (S j).
Proof.
  intros; unfold drop_idx.
  destruct (le_lt_dec i j); try easy; omega.
Qed.

Lemma rw_drop_idx_lt {A} i (l : iindex A) j :
  S j <= i ->
  drop_idx i l j = l j.
Proof.
  intros; unfold drop_idx.
  destruct (le_lt_dec i j); try easy; omega.
Qed.

Lemma rw_drop_idx_same {A} i (l : iindex A) :
  drop_idx i l i = l (S i).
Proof.
  apply rw_drop_idx_ge; auto.
Qed.

Lemma rw_insert_idx_gt {A} i a (l : iindex A) j :
  S i <= j ->
  insert_idx i a l j = l (pred j).
Proof.
  intros; unfold insert_idx.
  destruct (lt_eq_lt_dec i j) as [[|]|]; try easy; omega.
Qed.

Lemma rw_insert_idx_eq {A} i a (l : iindex A) j :
  i = j ->
  insert_idx i a l j = a.
Proof.
  intros; unfold insert_idx.
  destruct (lt_eq_lt_dec i j) as [[|]|]; try easy; omega.
Qed.

Lemma rw_insert_idx_lt {A} i a (l : iindex A) j :
  S j <= i ->
  insert_idx i a l j = l j.
Proof.
  intros; unfold insert_idx.
  destruct (lt_eq_lt_dec i j) as [[|]|]; try easy; omega.
Qed.

Lemma rw_insert_idx_same {A} i a (l : iindex A) :
  insert_idx i a l i = a.
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

Lemma iindex_beta_get {A} i (a : A) l :
  get_idx i (insert_idx i a l) = a.
Proof.
  cbn; autorewrite with rw_idxs; easy.
Qed.

Lemma iindex_beta_drop {A} i (a : A) l j :
  drop_idx i (insert_idx i a l) j = l j.
Proof.
  case_order i j; easy.
Qed.

Lemma iindex_eta {A} i (l : iindex A) j :
  insert_idx i (get_idx i l) (drop_idx i l) j = l j.
Proof.
  case_order i j; f_equal; omega.
Qed.

Hint Rewrite @iindex_beta_get @iindex_beta_drop @iindex_eta
  : rw_idxs.

(* Commuting [iindex] operations *)

Lemma swap_drop_idx_drop_idx {A} i j (l : iindex A) k :
  drop_idx i (drop_idx j l) k
  = drop_idx (unshift_idx i j)
      (drop_idx (shift_idx j i) l) k.
Proof.
  case_order i j;
    case_order j k; try easy;
      case_order i k; try easy;
        case_order j (S k); easy.
Qed.

Lemma swap_insert_idx_insert_idx {A} i a j b (l : iindex A) k :
  insert_idx i a (insert_idx j b l) k
  = insert_idx (shift_idx i j) b
      (insert_idx (unshift_idx j i) a l) k.
Proof.
  case_order i j;
    case_order j k; try easy;
      case_order i k; try easy;
        case_order j (pred k); easy.
Qed.

Lemma swap_drop_idx_insert_idx {A} i j a (l : iindex A) k :
  i <> j ->
  drop_idx i (insert_idx j a l) k
  = insert_idx (unshift_idx i j) a
      (drop_idx (unshift_idx j i) l) k.
Proof.
  intro Hneq.
  case_order i j; try contradiction;
    case_order i k; try easy;
      case_order j k; try easy;
        case_order j (S k); easy.     
Qed.

Lemma swap_insert_idx_drop_idx {A} i j a (l : iindex A) k :
  insert_idx i a (drop_idx j l) k
  = drop_idx (shift_idx i j)
      (insert_idx (shift_idx (shift_idx i j) i) a l) k.
Proof.
  case_order i j;
    case_order i k; try easy;
      case_order j k; try easy.
Qed.

(* Pre-composition of [iindex index] values *)

Definition compose_idx {A} (l1 : iindex index) (l2 : iindex A) :=
  fun (i : index) => get_idx (get_idx i l1) l2.

Lemma compose_idx_assoc {A} l1 l2 (l3 : iindex A) i :
  compose_idx (compose_idx l1 l2) l3 i
  = compose_idx l1 (compose_idx l2 l3) i.
Proof.
  unfold compose_idx; cbn; easy.
Qed.

Lemma compose_idx_id {A} (l : iindex A) i :
  compose_idx id_idx l i = l i.
Proof.
  unfold compose_idx; cbn; easy.
Qed.

Lemma compose_idx_drop {A} i l1 (l2 : iindex A) j :
  compose_idx (drop_idx i l1) l2 j
  = drop_idx i (compose_idx l1 l2) j.
Proof.
  unfold compose_idx; case_order i j; easy.
Qed.

Lemma compose_idx_shift {A} i (l : iindex A) j :
  compose_idx (shift_idx i) l j
  = drop_idx i l j.
Proof.
  unfold shift_idx; rewrite compose_idx_drop.
  apply drop_idx_ext; intro; rewrite compose_idx_id; easy.
Qed.

Lemma compose_idx_insert {A} i j l1 (l2 : iindex A) k :
  compose_idx (insert_idx i j l1) l2 k
  = insert_idx i (get_idx j l2) (compose_idx l1 l2) k.
Proof.
  unfold compose_idx; case_order i k; easy.
Qed.

Lemma compose_idx_unshift {A} i (l : iindex A) j :
  compose_idx (unshift_idx i) l j
  = insert_idx i (get_idx i l) l j.
Proof.
  unfold unshift_idx; rewrite compose_idx_insert.
  apply insert_idx_ext; intro; rewrite compose_idx_id; easy.
Qed.

Hint Rewrite @compose_idx_assoc @compose_idx_id @compose_idx_drop
     @compose_idx_shift @compose_idx_insert @compose_idx_unshift
  : rw_idxs.

(* Free names are a pair of a string and an index *)

Set Primitive Projections.
Record name := mkname { n_string : string; n_index : index }.
Add Printing Constructor name.
Unset Primitive Projections.

Definition name_of_string s := mkname s 0.
Coercion name_of_string : string >-> name.
Bind Scope string_scope with name.

(* Functions from [names]s that we treat like direct
   sums of streams *)
Definition iname A := name -> A.

Definition project_name {A} s (l : iname A) : iindex A :=
  fun (i : index) => l (mkname s i).
Arguments project_name {A} s l i /.

Definition with_name {A} s (li : iindex A) (ln : iname A)
  : iname A :=
  fun (n : name) =>
    if string_dec (n_string n) s then get_idx (n_index n) li
    else ln n.

Definition get_name {A} (n : name) (l : iname A) :=
  get_idx (n_index n) (project_name (n_string n) l).

Definition drop_name {A} (n : name) (l : iname A) : iname A :=
  with_name (n_string n)
    (drop_idx (n_index n) (project_name (n_string n) l)) l.

Definition insert_name {A} (n : name) (a : A) (l : iname A)
  : iname A :=
  with_name (n_string n)
    (insert_idx (n_index n) a (project_name (n_string n) l)) l.

(* Extensionality of these primitives *)

Lemma project_name_ext {A} s (l1 : iname A) l2 n :
  (forall m, l1 m = l2 m) ->
  project_name s l1 n = project_name s l2 n.
Proof. intro Heq; cbn; easy. Qed.

Lemma with_name_ext1 {A} s (li1 : iindex A) li2 ln n :
  (forall i, li1 i = li2 i) ->
  with_name s li1 ln n = with_name s li2 ln n.
Proof.
  intro Heq; unfold with_name; cbn.
  rewrite Heq; easy.
Qed.

Lemma with_name_ext2 {A} s (li : iindex A) ln1 ln2 n :
  (forall m, ln1 m = ln2 m) ->
  with_name s li ln1 n = with_name s li ln2 n.
Proof.
  intro Heq; unfold with_name; cbn.
  rewrite Heq; easy.
Qed.

Lemma with_name_ext {A} s (li1 : iindex A) li2 ln1 ln2 n :
  (forall i, li1 i = li2 i) ->
  (forall m, ln1 m = ln2 m) ->
  with_name s li1 ln1 n = with_name s li2 ln2 n.
Proof.
  intros Heq1 Heq2.
  erewrite with_name_ext1 by exact Heq1.
  apply with_name_ext2; easy.
Qed.

Lemma get_name_ext {A} n (l1 : iname A) l2 :
  (forall m, l1 m = l2 m) ->
  get_name n l1 = get_name n l2.
Proof.
  intro Heq; unfold get_name.
  apply get_idx_ext; intro.
  apply project_name_ext; easy.
Qed.

Lemma drop_name_ext {A} n (l1 : iname A) l2 m :
  (forall o, l1 o = l2 o) ->
  drop_name n l1 m = drop_name n l2 m.
Proof.
  intro Heq; unfold drop_name.
  apply with_name_ext; try easy; intro.
  apply drop_idx_ext; intro.
  apply project_name_ext; easy.
Qed.

Lemma insert_name_ext {A} n a (l1 : iname A) l2 m :
  (forall o, l1 o = l2 o) ->
  insert_name n a l1 m = insert_name n a l2 m.
Proof.
  intro Heq; unfold insert_name.
  apply with_name_ext; try easy; intro.
  apply insert_idx_ext; intro.
  apply project_name_ext; easy.
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

Lemma rw_with_name_eq {A} s li (ln : iname A) n :
  s = n_string n ->
  with_name s li ln n = li (n_index n).
Proof.
  intro Heq; subst; unfold with_name.
  destruct (string_dec (n_string n) (n_string n));
    try contradiction; easy.
Qed.

Lemma rw_with_name_neq {A} s li (ln : iname A) n :
  s <> n_string n ->
  with_name s li ln n = ln n.
Proof.
  intro Heq; unfold with_name.
  destruct (string_dec (n_string n) s); subst;
    try contradiction; easy.
Qed.

Lemma rw_with_name_same {A} li (ln : iname A) n :
  with_name (n_string n) li ln n = li (n_index n).
Proof.
  apply rw_with_name_eq; easy.
Qed.

Lemma rw_get_name {A} n (l : iname A) :
  get_name n l = l n.
Proof.
  unfold get_name; easy.
Qed.

Lemma rw_drop_name_indistinct {A} n (l : iname A) m :
  n_string n = n_string m ->
  drop_name n l m
  = drop_idx (n_index n) (project_name (n_string n) l) (n_index m).
Proof.
  intro Heq; unfold drop_name.
  rewrite rw_with_name_eq; easy.
Qed.

Lemma rw_drop_name_distinct {A} n (l : iname A) m :
  n_string n <> n_string m ->
  drop_name n l m = l m.
Proof.
  intro Heq; unfold drop_name.
  rewrite rw_with_name_neq; easy.
Qed.

Lemma rw_drop_name_same {A} n (l : iname A) :
  drop_name n l n
  = l (mkname (n_string n) (S (n_index n))).
Proof.
  rewrite rw_drop_name_indistinct by easy.
  rewrite rw_drop_idx_same; easy.
Qed.

Lemma rw_insert_name_indistinct {A} n a (l : iname A) m :
  n_string n = n_string m ->
  insert_name n a l m
  = insert_idx (n_index n) a
      (project_name (n_string n) l) (n_index m).
Proof.
  intro Heq; unfold insert_name.
  rewrite rw_with_name_eq; easy.
Qed.

Lemma rw_insert_name_distinct {A} n a (l : iname A) m :
  n_string n <> n_string m ->
  insert_name n a l m = l m.
Proof.
  intro Heq; unfold insert_name.
  rewrite rw_with_name_neq; easy.
Qed.

Lemma rw_insert_name_same {A} n a (l : iname A) :
  insert_name n a l n = a.
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

Lemma iname_beta_project_same {A} s li (ln : iname A) i :
  project_name s (with_name s li ln) i = li i.
Proof.
  cbn; autorewrite with rw_names; easy.
Qed.

Lemma iname_beta_project_neq {A} s t li (ln : iname A) i :
  s <> t ->
  project_name s (with_name t li ln) i = project_name s ln i.
Proof.
  intro; cbn.
  autorewrite with rw_names; easy.
Qed.

Lemma iname_beta_with_same {A} s li lj (ln : iname A) n :
  with_name s li (with_name s lj ln) n
  = with_name s li ln n.
Proof.
  case_string s (n_string n); easy.
Qed.

Lemma iname_eta {A} s (ln : iname A) n :
  with_name s (project_name s ln) ln n = ln n.
Proof.
  case_string s (n_string n); subst; easy.
Qed.

Hint Rewrite @iname_beta_project_same @iname_beta_with_same @iname_eta
  : rw_names.

Hint Rewrite @iname_beta_project_neq
  using (cbn; congruence) : rw_names.

(* Corollaries of the beta rules *)

Lemma iname_beta_project_drop_eq {A} s n (l : iname A) i :
  s = n_string n ->
  project_name s (drop_name n l) i
  = drop_idx (n_index n) (project_name (n_string n) l) i.
Proof.
  intro; unfold drop_name; subst.
  autorewrite with rw_names; easy.
Qed.

Lemma iname_beta_project_drop_neq {A} s n (l : iname A) i :
  s <> n_string n ->
  project_name s (drop_name n l) i
  = project_name s l i.
Proof.
  intro; unfold drop_name.
  autorewrite with rw_names; easy.
Qed.

Lemma iname_beta_project_insert_eq {A} s n a (l : iname A) i :
  s = n_string n ->
  project_name s (insert_name n a l) i
  = insert_idx (n_index n) a (project_name (n_string n) l) i.
Proof.
  intro; unfold insert_name; subst.
  autorewrite with rw_names; easy.
Qed.

Lemma iname_beta_project_insert_neq {A} s n a (l : iname A) i :
  s <> n_string n ->
  project_name s (insert_name n a l) i
  = project_name s l i.
Proof.
  intro; unfold insert_name.
  autorewrite with rw_names; easy.
Qed.

Hint Rewrite @iname_beta_project_drop_eq @iname_beta_project_drop_neq
     @iname_beta_project_insert_eq @iname_beta_project_insert_neq
  using (cbn; congruence) : rw_names.

Lemma iname_beta_get {A} n (a : A) l :
  get_name n (insert_name n a l) = a.
Proof.
  autorewrite with rw_names rw_idxs; easy.
Qed.

Lemma iname_beta_drop {A} n (a : A) l m :
  drop_name n (insert_name n a l) m = l m.
Proof.
  case_string (n_string n) (n_string m); try easy.
  rewrite drop_idx_ext
    with (l2 := insert_idx (n_index n) a (project_name (n_string n) l))
    by (intro; autorewrite with rw_names; easy).
  autorewrite with rw_idxs; cbn.
  replace (n_string n) with (n_string m) by easy; easy.
Qed.

Lemma iname_insert_eta {A} n (l : iname A) m :
  insert_name n (get_name n l) (drop_name n l) m = l m.
Proof.
  case_string (n_string n) (n_string m); try easy.
  rewrite insert_idx_ext
    with (l2 := drop_idx (n_index n) (project_name (n_string n) l))
    by (intro; autorewrite with rw_names; easy).
  replace (l n)
    with (get_idx (n_index n) (project_name (n_string n) l)) by easy.
  autorewrite with rw_idxs.
  replace (n_string n) with (n_string m); easy.
Qed.

Hint Rewrite @iname_beta_get @iname_beta_drop @iname_insert_eta
  : rw_names.

(* Commuting [iname] operations *)

Lemma swap_with_name_with_name {A} s li t lj (ln : iname A) n :
  s <> t ->
  with_name s li (with_name t lj ln) n
  = with_name t lj (with_name s li ln) n.
Proof.
  intro Hneq.
  case_string s (n_string n); try easy.
  case_string t (n_string n); easy.
Qed.

(* These proofs could really use rewriting under binders ... *)

Lemma swap_drop_name_drop_name {A} n m (l : iname A) o :
  drop_name n (drop_name m l) o
  = drop_name (unshift_name n m)
      (drop_name (shift_name m n) l) o.
Proof.
  case_string (n_string n) (n_string m).
  - case_string (n_string m) (n_string o); try easy.
    rewrite drop_idx_ext
      with (l2 := drop_idx (n_index m) (project_name (n_string m) l))
      by (intro; autorewrite with rw_names; easy).
    rewrite swap_drop_idx_drop_idx.
    apply drop_idx_ext; intro.
    autorewrite with rw_names; cbn.
    replace (n_string n) with (n_string m) by easy; easy.
  - unfold drop_name.
    rewrite swap_with_name_with_name by easy.
    apply with_name_ext; intro.
    + apply drop_idx_ext; intro.
      autorewrite with rw_names; easy.
    + apply with_name_ext1; intro.
      apply drop_idx_ext; intro.
      autorewrite with rw_names; easy.
Qed.

Lemma swap_insert_name_insert_name {A} n a m b (l : iname A) o :
  insert_name n a (insert_name m b l) o
  = insert_name (shift_name n m) b
      (insert_name (unshift_name m n) a l) o.
Proof.
  case_string (n_string n) (n_string m).
  - case_string (n_string m) (n_string o); try easy.
    rewrite insert_idx_ext
      with (l2 := insert_idx (n_index m) b (project_name (n_string m) l))
      by (intro; autorewrite with rw_names; easy).
    rewrite swap_insert_idx_insert_idx.
    apply insert_idx_ext; intro.
    autorewrite with rw_names; cbn.
    replace (n_string n) with (n_string m) by easy; easy.
  - unfold insert_name.
    rewrite swap_with_name_with_name by easy.
    apply with_name_ext; intro.
    + apply insert_idx_ext; intro.
      autorewrite with rw_names; easy.
    + apply with_name_ext1; intro.
      apply insert_idx_ext; intro.
      autorewrite with rw_names; easy.
Qed.

Lemma swap_drop_name_insert_name {A} n m a (l : iname A) o :
  n <> m ->
  drop_name n (insert_name m a l) o
  = insert_name (unshift_name n m) a
      (drop_name (unshift_name m n) l) o.
Proof.
  intro Hneq.
  case_string (n_string n) (n_string m).
  - case_string (n_string n) (n_string o); try easy.
    rewrite drop_idx_ext
      with (l2 := insert_idx (n_index m) a (project_name (n_string m) l))
      by (intro; autorewrite with rw_names; easy).
    rewrite swap_drop_idx_insert_idx.
    + apply insert_idx_ext; intro.
      autorewrite with rw_names; cbn.
      replace (n_string n) with (n_string m) by easy.
      easy.
    + intro; apply Hneq.
      replace n with (mkname (n_string n) (n_index n)) by easy.
      replace (n_string n) with (n_string m) by easy.
      replace (n_index n) with (n_index m) by easy.
      easy.
  - unfold drop_name, insert_name.
    rewrite swap_with_name_with_name by easy.
    apply with_name_ext; intro.
    + apply insert_idx_ext; intro.
      autorewrite with rw_names; easy.
    + apply with_name_ext1; intro.
      apply drop_idx_ext; intro.
      autorewrite with rw_names; easy.
Qed.

Lemma swap_insert_name_drop_name {A} n m a (l : iname A) o :
  insert_name n a (drop_name m l) o
  = drop_name (shift_name n m)
      (insert_name (shift_name (shift_name n m) n) a l) o.
Proof.
  case_string (n_string n) (n_string m).
  - case_string (n_string n) (n_string o); try easy.
    rewrite insert_idx_ext
      with (l2 := drop_idx (n_index m) (project_name (n_string m) l))
      by (intro; autorewrite with rw_names; easy).
    rewrite swap_insert_idx_drop_idx.
    apply drop_idx_ext; intro.
    autorewrite with rw_names; cbn.
    replace (n_string n) with (n_string m) by easy.
    easy.
  - unfold drop_name, insert_name.
    rewrite swap_with_name_with_name by easy.
    apply with_name_ext; intro.
    + apply drop_idx_ext; intro.
      autorewrite with rw_names; easy.
    + apply with_name_ext1; intro.
      apply insert_idx_ext; intro.
      autorewrite with rw_names; easy.
Qed.

(* Pre-composition of [iname name] values *)

Definition compose_name {A} (l1 : iname name) (l2 : iname A) :=
  fun (n : name) => get_name (get_name n l1) l2.

Lemma compose_name_assoc {A} l1 l2 (l3 : iname A) n :
  compose_name (compose_name l1 l2) l3 n
  = compose_name l1 (compose_name l2 l3) n.
Proof.
  unfold compose_name; cbn; easy.
Qed.

Lemma compose_name_id {A} (l : iname A) n :
  compose_name id_name l n = l n.
Proof.
  unfold compose_name; cbn; easy.
Qed.

Lemma compose_name_drop {A} n l1 (l2 : iname A) m :
  compose_name (drop_name n l1) l2 m
  = drop_name n (compose_name l1 l2) m.
Proof.
  unfold compose_name.
  case_string (n_string n) (n_string m); try easy.
  case_order (n_index n) (n_index m);
    autorewrite with rw_names; easy.
Qed.

Lemma compose_name_shift {A} n (l : iname A) m :
  compose_name (shift_name n) l m
  = drop_name n l m.
Proof.
  unfold shift_name; rewrite compose_name_drop.
  apply drop_name_ext; intro; rewrite compose_name_id; easy.
Qed.

Lemma compose_name_insert {A} n m l1 (l2 : iname A) o :
  compose_name (insert_name n m l1) l2 o
  = insert_name n (get_name m l2) (compose_name l1 l2) o.
Proof.
  unfold compose_name.
  case_string (n_string n) (n_string o); try easy.
  case_order (n_index n) (n_index o);
    autorewrite with rw_names; easy.
Qed.

Lemma compose_name_unshift {A} i (l : iname A) j :
  compose_name (unshift_name i) l j
  = insert_name i (get_name i l) l j.
Proof.
  unfold unshift_name; rewrite compose_name_insert.
  apply insert_name_ext; intro; rewrite compose_name_id; easy.
Qed.

Hint Rewrite @compose_name_assoc @compose_name_id @compose_name_drop
     @compose_name_shift @compose_name_insert @compose_name_unshift
  : rw_names.

(* Bound variables are represented by a level *)

Definition Zero := Empty_set.

Inductive Succ {S : Set} : Set := l0 | lS (s : S).

Fixpoint level (V : nat) : Set :=
  match V with
  | 0 => Zero
  | S V => @Succ (level V)
  end.
Arguments level !V.

(* Functions from [levels]s that we treat like lists *)
Definition ilevel V A := level V -> A.

Definition hd_level {V} {A} (l : ilevel (S V) A) := l l0.

Definition tl_level {V} {A} (l : ilevel (S V) A) : ilevel V A :=
  fun (v : level V) => l (lS v).

Definition cons_level {V} {A} a (l : ilevel V A) : ilevel (S V) A :=
  fun (v : level (S V)) =>
    match v with
    | l0 => a
    | lS v => l v
    end.