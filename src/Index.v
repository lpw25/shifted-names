Require Import String Omega Morph Setoid Morphisms.
Arguments string_dec !s1 !s2.

(* Name indices are [nat]s *)
Definition index := nat.

(* Boolean equality function *)
Definition index_eqb := Nat.eqb.

Lemma index_eqb_eq i j :
  index_eqb i j = true <-> i = j.
Proof. apply Nat.eqb_eq. Qed.

Lemma index_eqb_neq i j :
  index_eqb i j = false <-> i <> j.
Proof.
  split.
  - intros Heq1 Heq2.
    rewrite <- index_eqb_eq in Heq2.
    rewrite Heq1 in Heq2; discriminate.
  - intro Hneq.
    remember (index_eqb i j) as ij eqn:Hij.
    symmetry in Hij.
    destruct ij; try easy.
    rewrite index_eqb_eq in Hij.
    contradiction.
Qed.

Lemma index_eqb_refl i :
  index_eqb i i = true.
Proof.
  induction i; easy.
Qed.

(* Liftable functions from [index]s to nsets that we treat
   like streams *)
Definition iindex (T : nset) M := kmorph index T M.

Bind Scope kmorph_scope with iindex.

Definition get_iindex {T M} (i : index) (f : iindex T M)
  : pnset T M :=
  fun V => f V i.
Arguments get_iindex {T M} i f V /.

Definition delete_iindex {T M} (i : index) (f : iindex T M) :
  iindex T M :=
  fun V (j : index) =>
    if Compare_dec.le_lt_dec i j then get_iindex (S j) f V
    else get_iindex j f V.

Definition insert_iindex {T M} (a : pnset T M)
           (i : index) (f : iindex T M)
  : iindex T M :=
  fun V (j : index) =>
    match Compare_dec.lt_eq_lt_dec i j with
    | inleft (left _) => get_iindex (pred j) f V
    | inleft (right _) => a V
    | inright _ => get_iindex j f V
    end.

(* Derived operations *)

Definition move_iindex {T M} i j (f : iindex T M) :=
  insert_iindex (get_iindex j f) i (delete_iindex j f).

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
    with signature eq_pnset ==> eq ==> eq_kmorph ==> eq_kmorph
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
  insert_iindex a i f V j = f V (pred j).
Proof.
  intros; unfold insert_iindex.
  destruct (lt_eq_lt_dec i j) as [[|]|]; try easy; omega.
Qed.

Lemma red_insert_iindex_eq {T M} i a (f : iindex T M) V j :
  i = j ->
  insert_iindex a i f V j = a V.
Proof.
  intros; unfold insert_iindex.
  destruct (lt_eq_lt_dec i j) as [[|]|]; try easy; omega.
Qed.

Lemma red_insert_iindex_lt {T M} i a (f : iindex T M) V j :
  S j <= i ->
  insert_iindex a i f V j = f V j.
Proof.
  intros; unfold insert_iindex.
  destruct (lt_eq_lt_dec i j) as [[|]|]; try easy; omega.
Qed.

Lemma red_insert_iindex_same {T M} i a (f : iindex T M) V :
  insert_iindex a i f V i = a V.
Proof.
  apply red_insert_iindex_eq; auto.
Qed.

(* Useful lemma about predecessor and successor *)
Lemma red_succ_pred i :
  0 < i ->
  S (pred i) = i.
Proof.
  intros; omega.
Qed.

Hint Rewrite @red_delete_iindex_same @red_insert_iindex_same
  : red_iindexs.

Hint Rewrite @red_delete_iindex_ge @red_delete_iindex_lt
     @red_insert_iindex_gt @red_insert_iindex_eq
     @red_insert_iindex_lt @red_succ_pred
     using omega : red_iindexs.

(* Rewrite operations using reductions *)
Ltac red_iindexs :=
  autorewrite with red_iindexs in *;
  repeat progress
    (try (rewrite_strat topdown (hints red_iindexs)); cbn).

(* Case split on the order of the parameters. *)
Ltac case_order i j :=
  destruct (Compare_dec.lt_eq_lt_dec i j) as [[|]|];
    red_iindexs; [> | replace j with i by easy |]; try omega.

(* Beta and eta rules for [iindex] operations *)

Lemma iindex_beta_get_eq_pointwise {T M} i j a (f : iindex T M) :
  i = j ->
  get_iindex i (insert_iindex a j f) =p= a.
Proof.
  intros Heq V; red_iindexs; easy.
Qed.

Definition iindex_beta_get_eq {T M} i j a f :=
  fun V Heq =>
    eq_pnset_expand (@iindex_beta_get_eq_pointwise T M i j a f Heq) V.

Lemma iindex_beta_get_pointwise {T M} i a (f : iindex T M) :
  get_iindex i (insert_iindex a i f) =p= a.
Proof. apply iindex_beta_get_eq_pointwise; easy. Qed.

Definition iindex_beta_get {T M} i a f :=
  eq_pnset_expand (@iindex_beta_get_pointwise T M i a f).

Lemma iindex_beta_delete_eq_pointwise {T M} i j a (f : iindex T M) :
  i = j ->
  delete_iindex i (insert_iindex a j f) =km= f.
Proof.
  intros Heq V k.
  case_order i k; easy.
Qed.

Definition iindex_beta_delete_eq {T M} i j a f :=
  fun V Heq =>
    eq_kmorph_expand
      (@iindex_beta_delete_eq_pointwise T M i j a f Heq) V.

Lemma iindex_beta_delete_pointwise {T M} i a (f : iindex T M) :
  delete_iindex i (insert_iindex a i f) =km= f.
Proof. apply iindex_beta_delete_eq_pointwise; easy. Qed.

Definition iindex_beta_delete {T M} i a f :=
  eq_kmorph_expand (@iindex_beta_delete_pointwise T M i a f).

Lemma iindex_eta_eq_pointwise {T M} i j k (f : iindex T M) :
  i = j ->
  i = k ->
  insert_iindex (get_iindex j f) i (delete_iindex k f) =km= f.
Proof.
  intros Heq1 Heq2 V l.
  case_order i l; f_equal; easy.
Qed.

Definition iindex_eta_eq {T M} i j k f :=
  fun V Heq1 Heq2 =>
    eq_kmorph_expand
      (@iindex_eta_eq_pointwise T M i j k f Heq1 Heq2) V.

Lemma iindex_eta_pointwise {T M} i (f : iindex T M) :
  insert_iindex (get_iindex i f) i (delete_iindex i f) =km= f.
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

(* Unfolding derived operations *)

Lemma unfold_move_iindex {T M} i j (f : iindex T M) :
  move_iindex i j f =
  insert_iindex (get_iindex j f) i (delete_iindex j f).
Proof. easy. Qed.

Hint Rewrite @unfold_move_iindex : unfold_iindexs.

(* Folding derived operations *)

Lemma fold_move_iindex {T M} i j (f : iindex T M) :
  insert_iindex (get_iindex j f) i (delete_iindex j f)
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
  fun (j : index) =>
    if Compare_dec.le_lt_dec i j then S j
    else j.

Definition unshift_index (i : index) : index -> index :=
  fun (j : index) =>
    if Compare_dec.le_lt_dec j i then j
    else pred j.

Definition shift_above_index (i : index) : index -> index :=
  shift_index (S i).

Definition contract_down_index (i : index) : index -> index :=
  fun (j : index) =>
    if Nat.eq_dec (S i) j then i
    else j.

Definition contract_up_index (i : index) : index -> index :=
  fun (j : index) =>
    if Nat.eq_dec i (S j) then i
    else j.

(* Reductions *)

Lemma red_shift_index_ge i j :
  i <= j ->
  shift_index i j = S j.
Proof.
  intros; unfold shift_index.
  destruct (le_lt_dec i j); try easy; omega.
Qed.

Lemma red_shift_index_lt i j :
  S j <= i ->
  shift_index i j = j.
Proof.
  intros; unfold shift_index.
  destruct (le_lt_dec i j); try easy; omega.
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
  destruct (le_lt_dec j i); try easy; omega.
Qed.

Lemma red_unshift_index_le i j :
  j <= i ->
  unshift_index i j = j.
Proof.
  intros; unfold unshift_index.
  destruct (le_lt_dec j i); try easy; omega.
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

Lemma red_contract_down_index_neq i j :
  j <> S i ->
  contract_down_index i j = j.
Proof.
  intros; unfold contract_down_index.
  destruct (Nat.eq_dec (S i) j); omega.
Qed.

Lemma red_contract_down_index_eq i j :
  j = S i ->
  contract_down_index i j = i.
Proof.
  intros; unfold contract_down_index.
  destruct (Nat.eq_dec (S i) j); omega.
Qed.

Lemma red_contract_down_index_same i :
  contract_down_index i i = i.
Proof.
  apply red_contract_down_index_neq; omega.
Qed.

Lemma red_contract_up_index_neq i j :
  S j <> i ->
  contract_up_index i j = j.
Proof.
  intros; unfold contract_up_index.
  destruct (Nat.eq_dec i (S j)); omega.
Qed.

Lemma red_contract_up_index_eq i j :
  S j = i ->
  contract_up_index i j = i.
Proof.
  intros; unfold contract_up_index.
  destruct (Nat.eq_dec i (S j)); omega.
Qed.

Lemma red_contract_up_index_same i :
  contract_up_index i i = i.
Proof.
  apply red_contract_up_index_neq; omega.
Qed.

Hint Rewrite @red_shift_index_same @red_unshift_index_same
     @red_shift_above_index_same @red_contract_down_index_same
     @red_contract_up_index_same
  : red_iindexs.

Hint Rewrite @red_shift_index_ge @red_shift_index_lt
     @red_unshift_index_le @red_unshift_index_gt
     @red_shift_above_index_le @red_shift_above_index_gt
     @red_contract_down_index_neq @red_contract_down_index_eq
     @red_contract_up_index_neq @red_contract_up_index_eq
     using omega : red_iindexs.

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

Inductive iindex_op T M : Type :=
  | Ins : pnset T M -> iindex_op T M
  | Del : iindex_op T M.
Arguments Ins {T M} a.
Arguments Del {T M}.

Definition apply_iindex_op {T M}
           (op : iindex_op T M) :=
  match op with
  | Ins a => insert_iindex a
  | Del => delete_iindex
  end.

Definition normalize_iindex_left {T M} (op1 op2 : iindex_op T M)
  : index -> index -> index :=
  match op1, op2 with
  | Ins _, Ins _ => fun i1 i2 => i1
  | Ins _, Del => fun i1 i2 => i1
  | Del, Ins _ => fun i1 i2 => contract_down_index i2 i1
  | Del, Del => fun i1 i2 => i1
  end.

Definition normalize_iindex_right {T M} (op1 op2 : iindex_op T M) :=
  match op1, op2 with
  | Ins _, Ins _ => fun i1 i2 => i2
  | Ins _, Del => fun i1 i2 => i2
  | Del, Ins _ => fun i1 i2 => contract_up_index i1 i2
  | Del, Del => fun i1 i2 => i2
  end.

Lemma normalize_iindex {T M} (op1 op2 : iindex_op T M) :
  forall i1 i2 f,
    apply_iindex_op op1 i1
      (apply_iindex_op op2 i2 f)
    =km= apply_iindex_op op1 (normalize_iindex_left op1 op2 i1 i2)
           (apply_iindex_op op2 (normalize_iindex_right op1 op2 i1 i2) f).
Proof.
  intros i1 i2 f.
  destruct op1, op2; cbn; try easy.
  case_order i1 (S i2); try easy; subst.
  intros V i3.
  case_order i2 i3; easy.
Qed.

Definition transpose_iindex_left {T M} (op1 op2 : iindex_op T M) :=
  match op1, op2 with
  | Ins _, Ins _ => shift_index
  | Del, Ins _ => unshift_index
  | Ins _, Del => shift_above_index
  | Del, Del => unshift_index
  end.
Arguments transpose_iindex_left {T M} !op1 !op2.

Definition transpose_iindex_right {T M} (op1 op2 : iindex_op T M) :=
  match op1, op2 with
  | Ins _, Ins _ => fun i1 i2 => unshift_index i2 i1
  | Ins _, Del => fun i1 i2 => shift_index i2 i1
  | Del, Ins _ => fun i1 i2 => unshift_index i2 i1
  | Del, Del => fun i1 i2 => shift_index i2 i1
  end.
Arguments transpose_iindex_right {T M} !op1 !op2.

Definition irreducible_iindex_ops {T M} (op1 op2 : iindex_op T M)
  : index -> index -> Prop :=
  match op1, op2 with
  | Ins _, Ins _ => fun i1 i2 => True
  | Ins _, Del => fun i1 i2 => True
  | Del, Ins _ => fun i1 i2 => i1 <> i2
  | Del, Del => fun i1 i2 => True
  end.

Lemma transpose_iindex {T M} (op1 op2 : iindex_op T M) :
  forall i1 i2 f,
    irreducible_iindex_ops op1 op2 i1 i2 ->
    apply_iindex_op op1 i1
      (apply_iindex_op op2 i2 f)
    =km= apply_iindex_op op2 (transpose_iindex_left op1 op2 i1 i2)
          (apply_iindex_op op1 (transpose_iindex_right op1 op2 i1 i2) f).
Proof.
  intros i1 i2 f Hirr V i3.
  destruct op1, op2; cbn;
    case_order i1 i2;
      case_order i2 i3; try easy;
        case_order i1 i3; try easy.
  - case_order i2 (pred i3); easy.
  - case_order i2 (pred i3); easy.
  - case_order i2 (S i3); easy.
  - case_order i2 (S i1); easy.
  - case_order i2 (S i3); easy.
  - case_order i2 (S i1); easy.
Qed.

Lemma transpose_iindex_squared_left {T M} (op1 op2 : iindex_op T M) :
  forall i1 i2,
    transpose_iindex_left op2 op1
      (transpose_iindex_left op1 op2 i1 i2)
      (transpose_iindex_right op1 op2 i1 i2)
    = normalize_iindex_left op1 op2 i1 i2.
Proof.
  intros.
  destruct op1, op2; cbn;
    case_order i1 i2.
  case_order i2 (pred i1).
Qed.

Lemma transpose_iindex_squared_right {T M} (op1 op2 : iindex_op T M) :
  forall i1 i2,
    irreducible_iindex_ops op1 op2 i1 i2 ->
    transpose_iindex_right op2 op1
      (transpose_iindex_left op1 op2 i1 i2)
      (transpose_iindex_right op1 op2 i1 i2)
    = normalize_iindex_right op1 op2 i1 i2.
Proof.
  intros i1 i2 Hirr.
  destruct op1, op2; cbn in Hirr |- *;
    case_order i1 i2.
  case_order i2 (pred i1).
Qed.

Lemma transpose_iindex_reverse_left  {T M} (op1 op2 op3 : iindex_op T M) :
  forall i1 i2 i3,
    irreducible_iindex_ops op1 op2 i1 i2 ->
    irreducible_iindex_ops op2 op3 i2 i3 ->
    irreducible_iindex_ops op1 op3 i1 (transpose_iindex_left op2 op3 i2 i3) ->
    transpose_iindex_left op2 op3 (transpose_iindex_left op1 op2 i1 i2)
      (transpose_iindex_left op1 op3
         (transpose_iindex_right op1 op2 i1 i2) i3)
    = normalize_iindex_left op3 op2
        (transpose_iindex_left op1 op3 i1
          (transpose_iindex_left op2 op3 i2 i3))
        (transpose_iindex_left op1 op2 i1
           (transpose_iindex_right op2 op3 i2 i3)).
Proof.
  intros i1 i2 i3 Hirr1 Hirr2 Hirr3.
  destruct op1, op2, op3; cbn in *;
    case_order i1 i2;
      case_order i2 i3; try easy;
        case_order i1 i3; try easy.
  - case_order i3 (pred i1).
  - case_order i2 (pred i1).
  - case_order i2 (pred i1).
  - case_order i2 (pred i1).
  - case_order i1 (pred i3).
  - case_order i1 (pred i3).
  - case_order i2 (pred i3).
  - case_order i1 (pred i3).
  - case_order i1 (pred i3).
Qed.

Lemma transpose_iindex_reverse_right  {T M} (op1 op2 op3 : iindex_op T M) :
  forall i1 i2 i3,
    irreducible_iindex_ops op1 op2 i1 i2 ->
    irreducible_iindex_ops op2 op3 i2 i3 ->
    irreducible_iindex_ops op1 op3 i1 (transpose_iindex_left op2 op3 i2 i3) ->
    transpose_iindex_right op1 op2
      (transpose_iindex_right op1 op3 i1
         (transpose_iindex_left op2 op3 i2 i3))
      (transpose_iindex_right op2 op3 i2 i3)
    = normalize_iindex_right op2 op1
        (transpose_iindex_right op2 op3
           (transpose_iindex_left op1 op2 i1 i2) i3)
        (transpose_iindex_right op1 op3
          (transpose_iindex_right op1 op2 i1 i2) i3).
Proof.
  intros i1 i2 i3 Hirr1 Hirr2 Hirr3.
  destruct op1, op2, op3; cbn in *;
    case_order i1 i2;
      case_order i2 i3; try easy;
        case_order i1 i3; try easy.
  - case_order i3 (pred i1).
  - case_order i2 (pred i1).
  - case_order i1 (pred i2).
  - case_order (pred i3) i2.
  - case_order i2 (pred i3).
  - case_order i1 (pred i3).
  - case_order i1 (pred i3).
  - case_order i1 (pred i3).
Qed.

Lemma transpose_iindex_reverse_middle  {T M} (op1 op2 op3 : iindex_op T M) :
  forall i1 i2 i3,
    irreducible_iindex_ops op1 op2 i1 i2 ->
    irreducible_iindex_ops op2 op3 i2 i3 ->
    irreducible_iindex_ops op1 op3 i1 (transpose_iindex_left op2 op3 i2 i3) ->
    normalize_iindex_right op3 op2
      (transpose_iindex_left op1 op3 i1
          (transpose_iindex_left op2 op3 i2 i3))
      (transpose_iindex_left op1 op2
        (transpose_iindex_right op1 op3 i1
           (transpose_iindex_left op2 op3 i2 i3))
        (transpose_iindex_right op2 op3 i2 i3))
    = normalize_iindex_left op2 op1
        (transpose_iindex_right op2 op3
          (transpose_iindex_left op1 op2 i1 i2)
          (transpose_iindex_left op1 op3
            (transpose_iindex_right op1 op2 i1 i2) i3))
        (transpose_iindex_right op1 op3
          (transpose_iindex_right op1 op2 i1 i2) i3).
Proof.
  intros i1 i2 i3 Hirr1 Hirr2 Hirr3.
  remember op1 as oper1.
  remember op2 as oper2.
  remember op3 as oper3.
  destruct oper1, oper2, oper3; cbn in *;
    case_order i1 i2;
      case_order i2 i3; try easy;
        case_order i1 i3; try easy.
  - case_order i3 (pred i1).
  - case_order i2 (pred i1).
  - case_order i1 (pred i2).
  - case_order (pred i3) i2.
  - case_order i1 (pred i3).
  - case_order i2 (pred i1).
  - case_order i1 (pred i3).
  - case_order i1 (pred i3).
Qed.

(* Given a sequence of n operations, the operational transforms
   essentially give us transpositions σᵢ which swap the ith and (i+1)th
   operations. The group of permutations of n operations can be
   generated from the transpositions and the following relations:

   1) σᵢ ∘ σⱼ = σⱼ ∘ σᵢ where |i - j| > 1 2) σᵢ ∘ σᵢ = 1 3) σᵢ ∘ σᵢ₊₁ ∘
   σᵢ = σᵢ₊₁ ∘ σᵢ ∘ σᵢ₊₁

   1) follows automatically since the operational transforms only affect
   the operations that they are transposing.

   Showing 2) amounts to proving the following inversions:

     XT(ET(o1, o2), XT(o2, o1)) = o1

     ET(XT(o2, o1), ET(o1, o2)) = o2

   when expanded out and deduplicated, these are equivalent to showing:

     shift (shift n m) (unshift m n) = n
     unshift (shift_above n m) (shift m n) = n
     shift_above (unshift n m) (unshift m n) = n
     unshift (unshift n m) (shift m n) = n
     shift (unshift n m) (unshift m n) = n
     unshift (shift n m) (shift_above m n) = n

   Showing 3) amounts to proving the following equations:

     XT(XT(o3, o2), o1) = XT(XT(o3, ET(o1, o2)), XT(o2, o1))

     ET(ET(o1, o2), o3) = ET(ET(o1, XT(o3, o2)), ET(o2, o3))

     ET(XT(o2, o1), XT(o3, ET(o1, o2))) = XT(ET(o2, o3), ET(o1, XT(o3, o2)))

   when expanded out and deduplicated, these are equivalent to showing:

     shift o (shift m n) = shift (shift o m) (shift (unshift m o) n)
     shift (shift_above (unshift n m) o) (shift m n) = shift (shift (shift_above n o) m) (shift o n)
     shift (shift_above (shift n m) o) (shift_above m n) = shift_above (shift (unshift n o) m) (shift o n)
     shift o (unshift m n) = unshift (shift_above o m) (shift (shift m o) n)
     shift o (unshift m n) = unshift (shift o m) (shift (shift_above m o) n)
     shift (unshift (unshift n m) o) (unshift m n) = unshift (shift (shift_above n o) m) (shift o n)
     shift (unshift (shift n m) o) (unshift m n) = unshift (shift (unshift n o) m) (shift o n)
     shift_above o (shift_above m n) = shift_above (shift o m) (shift_above ((unshift m o) n))
     shift_above o (unshift m n) = unshift (shift_above o m) (shift_above (shift m o) n)
     unshift o (shift m n) = shift (unshift o m) (unshift (unshift m o) n)
     unshift (shift (unshift n m) o) (shift m n) = shift (unshift (shift n o) m) (unshift o n)
     unshift o (shift_above m n) = shift_above (unshift o m) (unshift (unshift m o) n)
     unshift (shift (shift n m) o) (shift_above m n) = shift_above (unshift (unshift n o) m) (unshift o n)
     unshift o (unshift m n) = unshift (unshift o m) (unshift (shift m o) n)
     unshift (unshift (unshift n m) o) (unshift m n) = unshift (unshift (shift n o) m) (unshift o n)
     unshift (unshift (shift n m) o) (unshift m n) = unshift (unshift (unshift n o) m) (unshift o n)

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

(* Unshift is right inverse of shift *)
Lemma simpl_shift_index_unshift_index i j :
  unshift_index i (shift_index i j) = j.
Proof. case_order i j. Qed.

(* Shift is left inverse of unshift if the indices aren't equal *)
Lemma simpl_unshift_index_shift_index i j :
  i <> j ->
  shift_index i (unshift_index i j) = j.
Proof. case_order i j. Qed.

Hint Rewrite simpl_shift_shift_index_unshift_index
     simpl_unshift_unshift_index_shift_index
     simpl_unshift_shift_above_index_shift_index
     simpl_unshift_shift_index_shift_above_index
     simpl_shift_index_unshift_index
  : simpl_indexs.

Hint Rewrite simpl_unshift_index_shift_index
  using congruence : simpl_indexs.

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

(* Commuting [index] operations *)

Lemma swap_shift_index_shift_index i j k :
  shift_index i (shift_index j k)
  = shift_index (shift_index i j)
      (shift_index (unshift_index j i) k).
Proof.
  case_order i j;
    case_order j k; try easy;
      case_order i k; try easy;
        case_order (S k) i; easy.
Qed.

Lemma swap_shift_index_unshift_index i j k :
  shift_index i (unshift_index j k)
  = unshift_index (shift_index i j)
      (shift_index (shift_above_index j i) k).
Proof.
  case_order i j;
    case_order j k; try easy;
      case_order i k; try easy.
Qed.

Lemma swap_unshift_index_unshift_index i j k :
  unshift_index i (unshift_index j k)
  = unshift_index (unshift_index i j)
      (unshift_index (shift_index j i) k).
Proof.
  case_order i j;
    case_order j k; try easy;
      case_order i k; try easy;
        case_order (S i) k; easy.
Qed.

Lemma swap_unshift_index_shift_index i j k :
  j <> i ->
  shift_index j k <> i ->
  unshift_index i (shift_index j k) =
  shift_index (unshift_index i j)
    (unshift_index (unshift_index j i) k).
Proof.
  intros Hn1 Hn2.
  case_order i j;
    case_order j k; try easy;
      case_order i k; try easy.
  contradiction Hn2.
  red_iindexs; easy.
Qed.

(* There is a full covariant functor from [T O] to [iindex N T O]
   by composition.

   Such composition distributes over our operations. *)

Lemma get_iindex_compose_distribute {T M R L} i
      (f : iindex T M) (g : morph T M R L) :
  morph_apply g (get_iindex i f) =p= get_iindex i (g @ f).
Proof. easy. Qed.

Lemma delete_iindex_compose_distribute {T M R L} i
      (f : iindex T M) (g : morph T M R L) :
  g @ (delete_iindex i f) =km= delete_iindex i (g @ f).
Proof.
  intros V j.
  case_order i j; easy.
Qed.

Lemma insert_iindex_compose_distribute {T M R L} i a
      (f : iindex T M) (g : morph T M R L) :
  g @ (insert_iindex i a f)
  =km= insert_iindex i (morph_apply g a) (g @ f).
Proof.
  intros V j.
  case_order i j; easy.
Qed.

Lemma move_iindex_compose_distribute {T M R L} i j
      (f : iindex T M) (g : morph T M R L) :
  g @ (move_iindex i j f) =km= move_iindex i j (g @ f).
Proof.
  unfold move_iindex.
  rewrite insert_iindex_compose_distribute.
  rewrite get_iindex_compose_distribute.
  rewrite delete_iindex_compose_distribute.
  easy.
Qed.
