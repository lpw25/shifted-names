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
    if Compare_dec.le_gt_dec i j then get_iindex (S j) f V
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
  destruct (le_gt_dec i j); try easy; omega.
Qed.

Lemma red_delete_iindex_lt {T M} i (f : iindex T M) V j :
  S j <= i ->
  delete_iindex i f V j = f V j.
Proof.
  intros; unfold delete_iindex.
  destruct (le_gt_dec i j); try easy; omega.
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

(* Useful lemma about predecessor and successor *)
Lemma red_succ_pred i :
  0 < i ->
  S (pred i) = i.
Proof.
  intros; omega.
Qed.

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

Lemma iindex_beta_get_eq {T M} i j a (f : iindex T M) :
  i = j ->
  get_iindex i (insert_iindex a j f) =p= a.
Proof.
  intros Heq V; red_iindexs; easy.
Qed.

Lemma iindex_beta_get {T M} i a (f : iindex T M) :
  get_iindex i (insert_iindex a i f) =p= a.
Proof. apply iindex_beta_get_eq; easy. Qed.

Lemma iindex_beta_delete_eq {T M} i j a (f : iindex T M) :
  i = j ->
  delete_iindex i (insert_iindex a j f) =km= f.
Proof.
  intros Heq V k.
  case_order i k; easy.
Qed.

Lemma iindex_beta_delete {T M} i a (f : iindex T M) :
  delete_iindex i (insert_iindex a i f) =km= f.
Proof. apply iindex_beta_delete_eq; easy. Qed.

Lemma iindex_eta_eq {T M} i j k (f : iindex T M) :
  i = j ->
  i = k ->
  insert_iindex (get_iindex j f) i (delete_iindex k f) =km= f.
Proof.
  intros Heq1 Heq2 V l.
  case_order i l; f_equal; easy.
Qed.

Lemma iindex_eta {T M} i (f : iindex T M) :
  insert_iindex (get_iindex i f) i (delete_iindex i f) =km= f.
Proof. apply iindex_eta_eq; easy. Qed.

Hint Rewrite @iindex_beta_get @iindex_beta_delete @iindex_eta
  : simpl_iindexs.

Hint Rewrite @iindex_beta_get_eq @iindex_beta_delete_eq
     @iindex_eta_eq
  using omega : simpl_iindexs.

(* Simplify [iindex] terms *)
Ltac simpl_iindexs :=
  autorewrite with simpl_iindexs;
  repeat progress
    (cbn;
     try (rewrite_strat topdown (hints simpl_iindexs))).

(* Transposing [iindex] operations

   We wish to reason about transposing [insert] and [delete]
   operations. These operations are not commutative, however they can be
   transposed by applying transformations to their indices.

   This situation is very close to that studied by the "operational
   transforms" literature in the context of collaborative text
   editors. However, rather than define the "ET" and "IT"
   transformations for our operations as they do, we will use a slightly
   different formulation.

   We define two transformations on indices:

     transpose_iindex_left(op1, op2, i1, i2)

     transpose_iindex_right(op2, op1, i2, i1)

   such that:

     op1<i1> (op2<i2>(f))
     = op2<transpose_iindex_left(op1, op2, i1, i2)>
         (op1<transpose_iindex_right(op2, op1, i2, i1)>(f))

   These transformations do not work in the case where [op1] is [delete],
   [op2] is [insert] and [i1 = i2]. In this case the composed operations
   reduce to the identity by beta-reduction and cannot be transposed.

*)

(* Stream operations *)
Inductive pnset_stream_op T M : Type :=
  | insert : pnset T M -> pnset_stream_op T M
  | delete : pnset_stream_op T M.
Arguments insert {T M} a.
Arguments delete {T M}.

Definition apply_iindex_op {T M}
           (op : pnset_stream_op T M) :=
  match op with
  | insert a => insert_iindex a
  | delete => delete_iindex
  end.

(* Abstract stream operations *)
Inductive stream_op : Type :=
  | Ins : stream_op
  | Del : stream_op.

Definition stream_op_of_pnset_stream_op {T M}
           (op : pnset_stream_op T M) :=
  match op with
  | insert a => Ins
  | delete => Del
  end.
Coercion stream_op_of_pnset_stream_op :
  pnset_stream_op >-> stream_op.

(* Precondition on transposing two operations *)
Definition irreducible_iindex_ops (op1 op2 : stream_op)
  : index -> index -> Prop :=
  match op1, op2 with
  | Ins, Ins => fun i1 i2 => True
  | Ins, Del => fun i1 i2 => True
  | Del, Ins => fun i1 i2 => i1 <> i2
  | Del, Del => fun i1 i2 => True
  end.

(* Shift and unshift

   We define [transpose_iindex_left] and
   [transpose_iindex_right] in terms of three operations on
   indices: [shift_below_index], [shift_above_index] and
   [unshift_index].
*)

Definition shift_below_index (i : index) : index -> index :=
  fun (j : index) =>
    if Compare_dec.le_gt_dec i j then S j
    else j.

Definition shift_above_index (i : index) : index -> index :=
  fun (j : index) =>
    if Compare_dec.le_gt_dec j i then j
    else S j.

Definition unshift_index (i : index) : index -> index :=
  fun (j : index) =>
    if Compare_dec.le_gt_dec j i then j
    else pred j.

(* Reductions *)

Lemma red_shift_below_index_ge i j :
  i <= j ->
  shift_below_index i j = S j.
Proof.
  intros; unfold shift_below_index.
  destruct (le_gt_dec i j); try easy; omega.
Qed.

Lemma red_shift_below_index_lt i j :
  S j <= i ->
  shift_below_index i j = j.
Proof.
  intros; unfold shift_below_index.
  destruct (le_gt_dec i j); try easy; omega.
Qed.

Lemma red_unshift_index_gt i j :
  S i <= j ->
  unshift_index i j = pred j.
Proof.
  intros; unfold unshift_index.
  destruct (le_gt_dec j i); try easy; omega.
Qed.

Lemma red_unshift_index_le i j :
  j <= i ->
  unshift_index i j = j.
Proof.
  intros; unfold unshift_index.
  destruct (le_gt_dec j i); try easy; omega.
Qed.

Lemma red_shift_above_index_gt i j :
  S i <= j ->
  shift_above_index i j = S j.
Proof.
  intros; unfold shift_above_index.
  destruct (le_gt_dec j i); try easy; omega.
Qed.

Lemma red_shift_above_index_le i j :
  j <= i ->
  shift_above_index i j = j.
Proof.
  intros; unfold shift_above_index.
  destruct (le_gt_dec j i); try easy; omega.
Qed.

Hint Rewrite red_shift_below_index_ge red_shift_below_index_lt
     red_unshift_index_le red_unshift_index_gt
     red_shift_above_index_le red_shift_above_index_gt
     using omega : red_iindexs.

(* Useful lemmas about shifting *)

Lemma shift_below_index_neq i j :
  shift_below_index i j <> i.
Proof.
  case_order i j; omega.
Qed.

Lemma shift_above_index_neq_shift_below_index i j :
  shift_above_index i j <> shift_below_index j i.
Proof.
  case_order i j; omega.
Qed.

Definition transpose_iindex_left (op1 op2 : stream_op) :=
  match op1, op2 with
  | Ins, Ins => shift_below_index
  | Ins, Del => shift_above_index
  | Del, Ins => unshift_index
  | Del, Del => unshift_index
  end.
Arguments transpose_iindex_left !op1 !op2.

Definition transpose_iindex_right (op2 op1 : stream_op) :=
  match op1, op2 with
  | Ins, Ins => unshift_index
  | Ins, Del => shift_below_index
  | Del, Ins => unshift_index
  | Del, Del => shift_below_index
  end.
Arguments transpose_iindex_right !op2 !op1.

Lemma transpose_iindex {T M}
      (op1 op2 : pnset_stream_op T M) :
  forall i1 i2 f,
    irreducible_iindex_ops op1 op2 i1 i2 ->
    apply_iindex_op op1 i1
      (apply_iindex_op op2 i2 f)
    =km= apply_iindex_op op2 (transpose_iindex_left op1 op2 i1 i2)
          (apply_iindex_op op1 (transpose_iindex_right op2 op1 i2 i1) f).
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

Tactic Notation
  "transpose_iindex" open_constr(op1) open_constr(i1)
  open_constr(op2) open_constr(i2) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_iindex op1 op2 i1 i2) as Hrw;
      cbn in Hrw; rewrite Hrw;
        [> | try easy]; clear Hrw.

Tactic Notation
  "transpose_iindex"
    open_constr(op1) open_constr(i1)
    open_constr(op2) open_constr(i2)
    "at" occurrences(occ) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_iindex op1 op2 i1 i2) as Hrw;
      cbn in Hrw; rewrite Hrw at occ;
        [> | try easy]; clear Hrw.

(* Normalizing pairs of operations

   The choice of indices on some pairs of operations is not
   unique. In particular,

     delete (S i) (insert i f)

   is equivalent to:

     delete i (insert (S i) f)

   We define a pair of transformations on indices:

     normalize_iindex_left(op2, op1, i2, i1)

     normalize_iindex_right(op1, op2, i1, i2)

   such that:

     op1<i1>(op2<i2>(f))
     = op1<normalize_iindex_left(op2, op1, i2, i1)>
         (op2<normalize_iindex_right(op1, op2, i1, i2)>(f))

   and:

     normalize_iindex_left(insert, delete, i, S i) = i
     normalize_iindex_right(delete, insert, S i, i) = S i

*)

(* Contract

   We define [normalize_iindex_left] and [normalize_iindex_right]
   in terms of three operations on indices: [contract_down_index]
   ,[contrace_up_index] and [unchanged_index]. *)

Definition contract_down_index (i : index) : index -> index :=
  fun (j : index) =>
    if Nat.eq_dec (S i) j then i
    else j.

Definition contract_up_index (i : index) : index -> index :=
  fun (j : index) =>
    if Nat.eq_dec i (S j) then i
    else j.

Definition unchanged_index (i : index) : index -> index :=
  fun (j : index) => j.
Arguments unchanged_index i j /.

(* Reductions *)

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

Lemma red_unchanged_index i j :
  unchanged_index i j = j.
Proof. easy. Qed.

Hint Rewrite red_contract_down_index_neq red_contract_down_index_eq
     red_contract_up_index_neq red_contract_up_index_eq
     using omega : red_iindexs.

Definition normalize_iindex_left (op2 op1 : stream_op)
  : index -> index -> index :=
  match op1, op2 with
  | Ins, Ins => unchanged_index
  | Ins, Del => unchanged_index
  | Del, Ins => contract_down_index
  | Del, Del => unchanged_index
  end.

Definition normalize_iindex_right (op1 op2 : stream_op) :=
  match op1, op2 with
  | Ins, Ins => unchanged_index
  | Ins, Del => unchanged_index
  | Del, Ins => contract_up_index
  | Del, Del => unchanged_index
  end.

Lemma normalize_iindex {T M}
      (op1 op2 : pnset_stream_op T M) :
  forall i1 i2 f,
    apply_iindex_op op1 i1
      (apply_iindex_op op2 i2 f)
    =km= apply_iindex_op op1
           (normalize_iindex_left op2 op1 i2 i1)
           (apply_iindex_op op2
              (normalize_iindex_right op1 op2 i1 i2) f).
Proof.
  intros i1 i2 f.
  destruct op1, op2; cbn; try easy.
  case_order i1 (S i2); try easy; subst.
  intros V i3.
  case_order i2 i3; easy.
Qed.

Tactic Notation
  "normalize_iindex" open_constr(op1) open_constr(i1)
  open_constr(op2) open_constr(i2) :=
  let Hrw := fresh "Hrw" in
    epose (normalize_iindex op1 op2 i1 i2) as Hrw;
      cbn in Hrw; rewrite Hrw; clear Hrw.

Tactic Notation
  "normalize_iindex"
    open_constr(op1) open_constr(i1)
    open_constr(op2) open_constr(i2)
    "at" occurrences(occ) :=
  let Hrw := fresh "Hrw" in
    epose (normalize_iindex op1 op2 i1 i2) as Hrw;
      cbn in Hrw; rewrite Hrw at occ; clear Hrw.

(* Transposing normalizes indices *)

Lemma normalize_transpose_iindex_left (op1 op2 : stream_op) :
  forall i1 i2,
    transpose_iindex_left op1 op2 i1 i2
    = normalize_iindex_left op1 op2
        (transpose_iindex_right op2 op1 i2 i1)
        (transpose_iindex_left op1 op2 i1 i2).
Proof.
  intros i1 i2.
  destruct op1, op2; cbn; try easy.
  case_order i1 i2.
Qed.

Lemma normalize_transpose_iindex_right (op1 op2 : stream_op) :
  forall i1 i2,
    transpose_iindex_right op2 op1 i2 i1
    = normalize_iindex_right op2 op1
        (transpose_iindex_left op1 op2 i1 i2)
        (transpose_iindex_right op2 op1 i2 i1).
Proof.
  intros i1 i2.
  destruct op1, op2; cbn; try easy.
  case_order i1 i2.
Qed.

Tactic Notation
  "normalize_transpose_iindex_left"
    open_constr(op1) open_constr(i1)
    open_constr(op2) open_constr(i2) :=
  let Hrw := fresh "Hrw" in
    epose (normalize_transpose_iindex_left op1 op2 i1 i2)
      as Hrw; cbn in Hrw; rewrite Hrw; clear Hrw.

Tactic Notation
  "normalize_transpose_iindex_left"
    open_constr(op1) open_constr(i1)
    open_constr(op2) open_constr(i2)
    "at" occurrences(occ) :=
  let Hrw := fresh "Hrw" in
    epose (normalize_transpose_iindex_left op1 op2 i1 i2)
      as Hrw; cbn in Hrw; rewrite Hrw at occ; clear Hrw.

Tactic Notation
  "normalize_transpose_iindex_right"
    open_constr(op1) open_constr(i1)
    open_constr(op2) open_constr(i2) :=
  let Hrw := fresh "Hrw" in
    epose (normalize_transpose_iindex_right op1 op2 i1 i2)
      as Hrw; cbn in Hrw; rewrite Hrw; clear Hrw.

Tactic Notation
  "normalize_transpose_iindex_right"
    open_constr(op1) open_constr(i1)
    open_constr(op2) open_constr(i2)
    "at" occurrences(occ) :=
  let Hrw := fresh "Hrw" in
    epose (normalize_transpose_iindex_right op1 op2 i1 i2)
      as Hrw; cbn in Hrw; rewrite Hrw at occ; clear Hrw.

(* Permutations of [iindex] operations

   Beyond transposing pairs of operations, we wish to reason
   about arbitrary permutations of sequences of [iindex]
   operations.

   Given a sequence of n operations, rewriting with
   [transpose_iindex] essentially gives us transpositions σᵢ
   which swap the ith and (i+1)th operations. The group of
   permutations of n operations can be generated from these
   transpositions and the following equations:

   1) σᵢ ∘ σⱼ = σⱼ ∘ σᵢ where |i - j| > 1

   2) σᵢ ∘ σᵢ = 1

   3) σᵢ ∘ σᵢ₊₁ ∘ σᵢ = σᵢ₊₁ ∘ σᵢ ∘ σᵢ₊₁

   The first equation follows automatically since rewriting
   with [transpose_iindex] only affects the operations that
   are transposed.

   Lemmas [transpose_iindex_squared_left] and
   [transpose_iindex_squared_right] below are equivalent to
   the second equation.

   Lemmas [transpose_iindex_reverse_left],
   [transpose_iindex_reverse_middle] and
   [transpose_iindex_reverse_right] below are equivalent to
   the third equation.
 *)

Lemma transpose_iindex_squared_left (op1 op2 : stream_op) :
  forall i1 i2,
    transpose_iindex_left op2 op1
      (transpose_iindex_left op1 op2 i1 i2)
      (transpose_iindex_right op2 op1 i2 i1)
    = normalize_iindex_left op2 op1 i2 i1.
Proof.
  intros.
  destruct op1, op2; cbn;
    case_order i1 i2.
  case_order i2 (pred i1).
Qed.

Lemma transpose_iindex_squared_right (op1 op2 : stream_op) :
  forall i1 i2,
    irreducible_iindex_ops op1 op2 i1 i2 ->
    transpose_iindex_right op1 op2
      (transpose_iindex_right op2 op1 i2 i1)
      (transpose_iindex_left op1 op2 i1 i2)
    = normalize_iindex_right op1 op2 i1 i2.
Proof.
  intros i1 i2 Hirr.
  destruct op1, op2; cbn in Hirr |- *;
    case_order i1 i2.
  case_order i2 (pred i1).
Qed.

Tactic Notation "transpose_iindex_squared_left"
       open_constr(op1) open_constr(i1)
       open_constr(op2) open_constr(i2) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_iindex_squared_left op1 op2 i1 i2)
      as Hrw; cbn in Hrw; rewrite Hrw; clear Hrw.

Tactic Notation "transpose_iindex_squared_left"
       open_constr(op1) open_constr(i1)
       open_constr(op2) open_constr(i2)
       "at" occurrences(occ) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_iindex_squared_left op1 op2 i1 i2)
      as Hrw; cbn in Hrw; rewrite Hrw at occ; clear Hrw.

Tactic Notation "transpose_iindex_squared_right"
       open_constr(op1) open_constr(i1)
       open_constr(op2) open_constr(i2) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_iindex_squared_right op1 op2 i1 i2)
      as Hrw; cbn in Hrw;
        rewrite Hrw; [> | try easy]; clear Hrw.

Tactic Notation "transpose_iindex_squared_right"
       open_constr(op1) open_constr(i1)
       open_constr(op2) open_constr(i2)
       "at" occurrences(occ) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_iindex_squared_right op1 op2 i1 i2)
      as Hrw; cbn in Hrw;
        rewrite Hrw at occ; [> | try easy]; clear Hrw.

Lemma transpose_iindex_reverse_left (op1 op2 op3 : stream_op) :
  forall i1 i2 i3,
    irreducible_iindex_ops op1 op2 i1 i2 ->
    irreducible_iindex_ops op2 op3 i2 i3 ->
    irreducible_iindex_ops op1 op3 i1
      (transpose_iindex_left op2 op3 i2 i3) ->
    transpose_iindex_left op2 op3 (transpose_iindex_left op1 op2 i1 i2)
      (transpose_iindex_left op1 op3
         (transpose_iindex_right op2 op1 i2 i1) i3)
    = normalize_iindex_left op2 op3
        (transpose_iindex_left op1 op2 i1
           (transpose_iindex_right op3 op2 i3 i2))
        (transpose_iindex_left op1 op3 i1
          (transpose_iindex_left op2 op3 i2 i3)).
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

Lemma transpose_iindex_reverse_middle (op1 op2 op3 : stream_op) :
  forall i1 i2 i3,
    irreducible_iindex_ops op1 op2 i1 i2 ->
    irreducible_iindex_ops op2 op3 i2 i3 ->
    irreducible_iindex_ops op1 op3 i1
      (transpose_iindex_left op2 op3 i2 i3) ->
    normalize_iindex_right op3 op2
      (transpose_iindex_left op1 op3 i1
          (transpose_iindex_left op2 op3 i2 i3))
      (transpose_iindex_left op1 op2
        (transpose_iindex_right op3 op1
           (transpose_iindex_left op2 op3 i2 i3) i1)
        (transpose_iindex_right op3 op2 i3 i2))
    = normalize_iindex_left op1 op2
        (transpose_iindex_right op3 op1 i3
           (transpose_iindex_right op2 op1 i2 i1))
        (transpose_iindex_right op3 op2
          (transpose_iindex_left op1 op3
            (transpose_iindex_right op2 op1 i2 i1) i3)
          (transpose_iindex_left op1 op2 i1 i2)).
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

Lemma transpose_iindex_reverse_right (op1 op2 op3 : stream_op) :
  forall i1 i2 i3,
    irreducible_iindex_ops op1 op2 i1 i2 ->
    irreducible_iindex_ops op2 op3 i2 i3 ->
    irreducible_iindex_ops op1 op3 i1 (transpose_iindex_left op2 op3 i2 i3) ->
    transpose_iindex_right op2 op1
      (transpose_iindex_right op3 op2 i3 i2)
      (transpose_iindex_right op3 op1
        (transpose_iindex_left op2 op3 i2 i3) i1)
    = normalize_iindex_right op2 op1
        (transpose_iindex_right op3 op2 i3
           (transpose_iindex_left op1 op2 i1 i2))
        (transpose_iindex_right op3 op1 i3
          (transpose_iindex_right op2 op1 i2 i1)).
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

Tactic Notation "transpose_iindex_reverse_left"
       open_constr(op1) open_constr(i1)
       open_constr(op2) open_constr(i2)
       open_constr(op3) open_constr(i3) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_iindex_reverse_left
             op1 op2 op3 i1 i2 i3) as Hrw;
      cbn in Hrw; rewrite Hrw;
      [> | try easy | try easy | try easy]; clear Hrw.

Tactic Notation "transpose_iindex_reverse_left"
       open_constr(op1) open_constr(i1)
       open_constr(op2) open_constr(i2)
       open_constr(op3) open_constr(i3)
       "at" occurrences(occ) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_iindex_reverse_left
             op1 op2 op3 i1 i2 i3) as Hrw;
      cbn in Hrw; rewrite Hrw at occ;
      [> | try easy | try easy | try easy]; clear Hrw.

Tactic Notation "transpose_iindex_reverse_middle"
       open_constr(op1) open_constr(i1)
       open_constr(op2) open_constr(i2)
       open_constr(op3) open_constr(i3) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_iindex_reverse_middle
             op1 op2 op3 i1 i2 i3) as Hrw;
      cbn in Hrw; rewrite Hrw;
      [> | try easy | try easy | try easy]; clear Hrw.

Tactic Notation "transpose_iindex_reverse_middle"
       open_constr(op1) open_constr(i1)
       open_constr(op2) open_constr(i2)
       open_constr(op3) open_constr(i3)
       "at" occurrences(occ) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_iindex_reverse_middle
             op1 op2 op3 i1 i2 i3) as Hrw;
      cbn in Hrw; rewrite Hrw at occ;
      [> | try easy | try easy | try easy]; clear Hrw.

Tactic Notation "transpose_iindex_reverse_right"
       open_constr(op1) open_constr(i1)
       open_constr(op2) open_constr(i2)
       open_constr(op3) open_constr(i3) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_iindex_reverse_right
             op1 op2 op3 i1 i2 i3) as Hrw;
      cbn in Hrw; rewrite Hrw;
      [> | try easy | try easy | try easy]; clear Hrw.

Tactic Notation "transpose_iindex_reverse_right"
       open_constr(op1) open_constr(i1)
       open_constr(op2) open_constr(i2)
       open_constr(op3) open_constr(i3)
       "at" occurrences(occ) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_iindex_reverse_right
             op1 op2 op3 i1 i2 i3) as Hrw;
      cbn in Hrw; rewrite Hrw at occ;
      [> | try easy | try easy | try easy]; clear Hrw.

(* Pushing [get_iindex] through other operations

   We reuse the machinery for trasposition, since this
   transformation is closely related to transposing
   operations with delete.
*)

Lemma transpose_get_iindex {T M} (op : pnset_stream_op T M) :
  forall i1 i2 f,
    irreducible_iindex_ops Del op i1 i2 ->
    get_iindex i1 (apply_iindex_op op i2 f)
    =p= get_iindex (transpose_iindex_right op Del i2 i1) f.
Proof.
  intros i1 i2 f Hirr V.
  destruct op; cbn in *;
    case_order i1 i2; easy.
Qed.

Tactic Notation "transpose_get_iindex"
       open_constr(i1) open_constr(op) open_constr(i2) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_get_iindex op i1 i2) as Hrw;
      cbn in Hrw; rewrite Hrw; [> | try easy]; clear Hrw.

Tactic Notation "transpose_get_iindex"
       open_constr(i1) open_constr(op)
       open_constr(i2) "at" occurrences(occ) :=
  let Hrw := fresh "Hrw" in
    epose (transpose_get_iindex op i1 i2) as Hrw;
      cbn in Hrw; rewrite Hrw at occ; [> | try easy]; clear Hrw.

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
  g @ (insert_iindex a i f)
  =km= insert_iindex (morph_apply g a) i (g @ f).
Proof.
  intros V j.
  case_order i j; easy.
Qed.

(* Morphism extension distributes over the operations *)

Lemma get_iindex_extend {T M} i (f : iindex T M) :
  pnset_extend (get_iindex i f)
  =p= get_iindex i (kmorph_extend f).
Proof.
  intros V; simplT; easy.
Qed.

Lemma insert_iindex_extend {T M} a i (f : iindex T M) :
  kmorph_extend (insert_iindex a i f)
  =km= insert_iindex (pnset_extend a) i (kmorph_extend f).
Proof.
  intros V v.
  case_order i v;
    simplT; red_iindexs; easy.
Qed.

Lemma delete_iindex_extend {T M} i (f : iindex T M) :
  kmorph_extend (delete_iindex i f)
  =km= delete_iindex i (kmorph_extend f).
Proof.
  intros V v.
  simplT.
  case_order i v;
    simplT; red_iindexs; easy.
Qed.

