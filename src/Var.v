Require Import String Omega Morph.

(* Name indices are [nat]s *)
Definition index := nat.

(* Shift up all indices greater than or equal to [i] *)
Fixpoint shift_idx (i : index) (j : index) : index :=
  match i with
  | 0 => S j
  | S i =>
    match j with
    | 0 => 0
    | S j => S (shift_idx i j)
    end
  end.

Lemma rw_shift_idx_ge i j :
  i <= j ->
  shift_idx i j = S j.
Proof.
  generalize dependent j.
  induction i; destruct j; intros; try easy.
  cbn; auto with arith.
Qed.

Lemma rw_shift_idx_lt i j :
  S j <= i ->
  shift_idx i j = j.
Proof.
  generalize dependent j.
  induction i; destruct j; intros; try easy.
  cbn; auto with arith.
Qed.

Lemma rw_shift_idx_same i :
  shift_idx i i = S i.
Proof.
  apply rw_shift_idx_ge; auto.
Qed.

(* Partial inverse of [shift_idx]. Returns [None] iff [i = j]. *)
Fixpoint inverse_shift_idx i j :=
  match i with
  | 0 =>
    match j with
    | 0 => None
    | S j => Some j
    end
  | S i =>
    match j with
    | 0 => Some 0
    | S j =>
      match inverse_shift_idx i j with
      | None => None
      | Some j' => Some (S j')
      end
    end
  end.

Lemma rw_inverse_shift_idx_eq i j :
  i = j ->
  inverse_shift_idx i j = None.
Proof.
  intros <-.
  induction i; try easy; cbn.
  rewrite IHi; easy.
Qed.

Lemma rw_inverse_shift_idx_lt i j :
  S j <= i ->
  inverse_shift_idx i j = Some j.
Proof.
  generalize dependent j.
  induction i; destruct j; intros Heq; try easy; cbn.
  rewrite IHi; auto with arith.
Qed.

Lemma rw_inverse_shift_idx_gt i j :
  S i <= j ->
  inverse_shift_idx i j = Some (pred j).
Proof.
  generalize dependent j.
  induction i; destruct j; intros Heq; try easy; cbn.
  rewrite IHi; f_equal; omega.
Qed.

Lemma rw_inverse_shift_idx_same i :
  inverse_shift_idx i i = None.
Proof.
  apply rw_inverse_shift_idx_eq; easy.
Qed.

(* Tactics for handling the above operations *)

Arguments shift_idx !i !j.
Arguments inverse_shift_idx !i !j.

(* Rewrite [shift_idx]s, [unshift_idx]s and [inverse_shift_idx]s where
   the order of the parameters can be determined by the omega tactic *)
Ltac simpl_idxs :=
  repeat progress
    (match goal with
     | |- context [shift_idx ?i ?j] =>
       first
         [ rewrite (rw_shift_idx_ge i j) by omega
         | rewrite (rw_shift_idx_lt i j) by omega ]
     | |- context [inverse_shift_idx ?i ?j] =>
       first
         [ rewrite (rw_inverse_shift_idx_eq i j) by omega
         | rewrite (rw_inverse_shift_idx_lt i j) by omega
         | rewrite (rw_inverse_shift_idx_gt i j) by omega ]
     end; cbn).

(* Case split on the order of the parameters, then simplify any
   [shift_idx]s and [inverse_shift_idx]s affected by the
   ordering. *)
Ltac case_order i j :=
  destruct (Compare_dec.lt_eq_lt_dec i j) as [[|]|];
  simpl_idxs.

(* Inverses *)

Lemma rw_inverse_shift_idx_shift_idx i j :
  inverse_shift_idx i (shift_idx i j) = Some j.
Proof.
  case_order i j; easy.
Qed.

Lemma rw_shift_idx_inverse_shift_idx {i j} :
  option_map (shift_idx i) (inverse_shift_idx i j)
  = if Nat.eq_dec i j then None else Some j.
Proof.
  case_order i j;
    destruct (Nat.eq_dec i j); f_equal; try omega.
Qed.

(* Comparison for free name indices *)

Inductive index_comparison (i : index) : index -> Set :=
| same_idx : index_comparison i i
| diff_idx j : index_comparison i (shift_idx i j).

Fixpoint compare_idx (i : index)
  : forall j, index_comparison i j :=
  match i with
  | 0 => fun j =>
    match j with
    | 0 => same_idx _
    | S j => diff_idx _ j
    end
  | S i => fun j =>
    match j with
    | 0 => diff_idx _ 0
    | S j =>
      match compare_idx i j with
      | same_idx _ => same_idx _
      | diff_idx _ j' => diff_idx _ (S j')
      end
    end
  end.

Lemma rw_compare_idx_same :
  forall i, compare_idx i i = same_idx i.
Proof. induction i; cbn; try rewrite IHi; easy. Qed.

Lemma rw_compare_idx_shift :
  forall i j, compare_idx i (shift_idx i j) = diff_idx i j.
Proof. induction i; destruct j; cbn; try rewrite IHi; easy. Qed.

Hint Rewrite @rw_shift_idx_same @rw_inverse_shift_idx_same
     @rw_inverse_shift_idx_shift_idx @rw_shift_idx_inverse_shift_idx
     @rw_compare_idx_same @rw_compare_idx_shift
  : rw_idxs.

Arguments shift_idx : simpl never.
Arguments inverse_shift_idx : simpl never.

(* Free names are a pair of a string and an index *)

Set Primitive Projections.
Record name := mkname { n_string : string; n_index : index }.
Add Printing Constructor name.
Unset Primitive Projections.

Definition name_of_string s := mkname s 0.
Coercion name_of_string : string >-> name.
Bind Scope string_scope with name.

Lemma name_dec (a : name) (b : name) :
  {a = b} + {a <> b}.
Proof.
  destruct (string_dec (n_string a) (n_string b)).
  - destruct (Nat.eq_dec (n_index a) (n_index b)).
    + left; destruct a, b; cbn in *; subst; easy.
    + right; intro; subst; contradiction.
  - right; intro; subst; contradiction.
Qed.

Definition indistinct_names a b :=
  n_string a = n_string b.

Definition distinct_names a b :=
  not (indistinct_names a b).

Lemma distinct_names_dec a b :
  { distinct_names a b } + { indistinct_names a b }.
Proof.
  destruct (string_dec (n_string a) (n_string b)).
  - right; easy.
  - left; easy.
Qed.

Lemma distinct_names_same a :
  ~ (distinct_names a a).
Proof.
  intro Hd.
  unfold distinct_names, indistinct_names in Hd.
  easy.
Qed.

Lemma distinct_names_symmetric {a b} :
  distinct_names a b ->
  distinct_names b a.
Proof.
  unfold distinct_names; intuition.
Qed.
  
(* Shift the index of a name up by one *)
Definition succ_name (a : name) :=
  mkname (n_string a) (S (n_index a)).

(* Shift up all names with the same string as [a] and an index
   greater than or equal to [a]'s *)
Definition shift_name (a : name) (b : name) :=
  mkname (n_string b)
   (if string_dec (n_string a) (n_string b) then
      shift_idx (n_index a) (n_index b)
    else
      n_index b).
Arguments shift_name !a !b.

Lemma rw_shift_name_distinct a b :
  distinct_names a b ->
  shift_name a b = b.
Proof.
  unfold shift_name.
  destruct (string_dec (n_string a) (n_string b)); easy.  
Qed.

Lemma rw_shift_name_indistinct a b :
  indistinct_names a b ->
  shift_name a b
  = mkname (n_string b) (shift_idx (n_index a) (n_index b)).
Proof.
  unfold shift_name.
  destruct (string_dec (n_string a) (n_string b)); easy.
Qed.

Lemma rw_shift_name_same a :
  shift_name a a = succ_name a.
Proof.
  rewrite rw_shift_name_indistinct by easy.
  rewrite rw_shift_idx_same; easy.
Qed.

(* Partial inverse of [shift_name]. Returns [None] iff [b = a]. *)
Definition inverse_shift_name (a : name) (b : name) :=
  if string_dec (n_string a) (n_string b) then
    option_map (mkname (n_string b))
      (inverse_shift_idx (n_index a) (n_index b))
  else
    Some b.

Lemma rw_inverse_shift_name_distinct a b :
  distinct_names a b ->
  inverse_shift_name a b = Some b.
Proof.
  unfold inverse_shift_name.
  destruct (string_dec (n_string a) (n_string b)); easy.
Qed.

Lemma rw_inverse_shift_name_indistinct a b :
  indistinct_names a b ->
  inverse_shift_name a b
  = option_map (mkname (n_string b))
      (inverse_shift_idx (n_index a) (n_index b)).
Proof.
  unfold inverse_shift_name.
  destruct (string_dec (n_string a) (n_string b)); easy.
Qed.

Lemma rw_inverse_shift_name_same a :
  inverse_shift_name a a = None.
Proof.
  rewrite rw_inverse_shift_name_indistinct by easy.
  rewrite rw_inverse_shift_idx_same; easy.
Qed.

(* Rewrite [shift_idx]s, [unshift_idx]s and [inverse_shift_idx]s where
   the order of the parameters can be determined by the omega tactic *)
Ltac simpl_names :=
  repeat progress
    (match goal with
     | |- context [shift_name ?a ?b] =>
       first
         [ rewrite (rw_shift_name_distinct a b) by easy
         | rewrite (rw_shift_name_indistinct a b) by easy ]
     | |- context [inverse_shift_name ?a ?b] =>
       first
         [ rewrite (rw_inverse_shift_name_distinct a b) by easy
         | rewrite (rw_inverse_shift_name_indistinct a b) by easy ]
     end; cbn).

(* Case split on the strings of the parameters, then simplify any
   [shift_names]s and [inverse_shift_names]s affected by the
   ordering. *)
Ltac case_strings a b :=
  destruct (distinct_names_dec a b);
  simpl_names.

(* Inverses *)

Lemma rw_inverse_shift_name_shift_name a b :
  inverse_shift_name a (shift_name a b) = Some b.
Proof.
  case_strings a b; autorewrite with rw_idxs; easy.
Qed.

Lemma rw_shift_name_inverse_shift_name a b :
  option_map (shift_name a) (inverse_shift_name a b)
  = if distinct_names_dec a b then Some b
    else if Nat.eq_dec (n_index a) (n_index b) then None
    else Some b.
Proof.
  case_strings a b; try easy;
    case_order (n_index a) (n_index b);
    simpl_names; simpl_idxs;
      try replace (S (pred (n_index b))) with (n_index b) by omega;
      destruct (Nat.eq_dec (n_index a) (n_index b)); try omega; easy.
Qed.    

Hint Rewrite @rw_shift_name_same @rw_inverse_shift_name_same
     @rw_inverse_shift_name_shift_name
  : rw_names.

(* Renaming operation on names *)

Definition rename_name a b c :=
  match inverse_shift_name b c with
  | Some c' => shift_name a c'
  | None => a
  end.

Arguments rename_name !a !b !c.

Lemma rw_rename_name_distinct a b c :
  distinct_names a c ->
  rename_name b a c = shift_name b c.
Proof.
  intros.
  unfold rename_name.
  rewrite (rw_inverse_shift_name_distinct a c) by easy.
  easy.
Qed.

Lemma rw_rename_name_both_distinct a b c :
  distinct_names a c ->
  distinct_names b c ->
  rename_name b a c = c.
Proof.
  intros.
  rewrite (rw_rename_name_distinct a b c) by easy.
  rewrite (rw_shift_name_distinct b c) by easy.
  easy.
Qed.

Lemma rw_rename_name_same a b : rename_name b a a = b.
Proof.
  unfold rename_name.
  autorewrite with rw_names; easy.
Qed.

Lemma rw_rename_name_shift_name a b c :
  rename_name b a (shift_name a c) = shift_name b c.
Proof.
  unfold rename_name.
  autorewrite with rw_names; easy.
Qed.

Lemma rw_rename_name_rename_name a b c d :
  rename_name b a (rename_name a c d)
  = rename_name b c d.
Proof.
  unfold rename_name.
  case_strings c d;
    case_order (n_index c) (n_index d);
    autorewrite with rw_names; easy.
Qed.

Hint Rewrite @rw_rename_name_same @rw_rename_name_shift_name
     @rw_rename_name_rename_name
  : rw_names.

(* Comparison for free names *)

Inductive name_comparison (a : name) : name -> Set :=
| same_name : name_comparison a a
| diff_name b : name_comparison a (shift_name a b).

Lemma compare_names a b : name_comparison a b.
Proof.
  destruct a as [an ai], b as [bn bi]; cbn.
  remember (string_dec an bn) as Hdec.
  destruct Hdec; subst.
  - destruct (compare_idx ai bi) as [|j].
    + apply same_name.
    + replace (mkname bn (shift_idx ai j))
        with (shift_name (mkname bn ai) (mkname bn j));
        try apply diff_name.
      unfold shift_name, n_string.
      rewrite <- HeqHdec; easy.      
  - replace (mkname bn bi)
        with (shift_name (mkname an ai) (mkname bn bi));
      try apply diff_name.
    unfold shift_name, n_string.
    rewrite <- HeqHdec; easy.
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

(* Variables are either free names or bound levels *)

Inductive var {V : nat} :=
| free (name : name)
| bound (l : level V).

(* The core operations acting on variables *)

Definition wkv {V} (v : @var V) : @var (S V) :=
  match v with
  | free n => free n
  | bound l => @bound (S V) (lS l)
  end.

Definition openv a {V} (v : @var (S V)) : @var V :=
  match v with
  | free n => free (shift_name a n)
  | bound l0 => free a
  | bound (lS l) => @bound V l
  end.

Definition closev a {V} (v : @var V) : @var (S V) :=
  match v with
  | free n =>
    match inverse_shift_name a n with
    | Some n' => free n'
    | None => @bound (S V) l0
    end
  | bound l => @bound (S V) (lS l)
  end.

Definition bindv {V} (v : @var (S V)) : option (@var V) :=
  match v with
  | free n => Some (free n)
  | bound l0 => None
  | bound (lS l) => Some (@bound V l)
  end.

(* We don't want to reduce the operations if it just exposes
   the inner match. ([wkv] has no inner matches) *)

Arguments openv : simpl nomatch.
Arguments closev : simpl nomatch.
Arguments bindv : simpl nomatch.

(* Add reductions for [closev]. The other operations reduce
   directly by cbn. *)

Lemma rw_closev_shift a b :
  forall {V}, @closev a V (free (shift_name a b)) = free b.
Proof.
  unfold closev; autorewrite with rw_names; easy.
Qed.

Lemma rw_closev_same a :
  forall {V}, @closev a V (free a) =
    @bound (S V) (@l0 (level V)).
Proof.
  unfold closev; autorewrite with rw_names; easy.
Qed.

Hint Rewrite @rw_closev_shift @rw_closev_same : rw_vars.

(* Open and close on the same variable are inverses. Weaken
   is a right inverse of bind. *)

Lemma rw_openv_closev a {V} (v : @var V) :
  openv a (closev a v) = v.
Proof.
  destruct v as [n|l]; cbn; try easy.
  destruct (compare_names a n); autorewrite with rw_vars; easy.
Qed.

Lemma rw_closev_openv a {V} (v : @var (S V)) :
  closev a (openv a v) = v.
Proof.
  destruct v as [n|[|l]]; cbn;
    autorewrite with rw_vars; easy.
Qed.

Lemma rw_bindv_wkv {V} (v : @var V) :
  bindv (wkv v) = Some v.
Proof. destruct v; easy. Qed.

Hint Rewrite @rw_closev_openv @rw_openv_closev @rw_bindv_wkv
  : rw_vars.

(* [openv] and [closev] on distinct names *)
Lemma closev_distinct {a b} (Hd : distinct_names a b) {V} :
  closev a (@free V b) = free b.
Proof.
  unfold closev.
  rewrite (rw_inverse_shift_name_distinct a b) by easy.
  easy.
Qed.

Lemma openv_distinct {a b} (Hd : distinct_names a b) {V} :
  openv a (@free (S V) b) = free b.
Proof.
  unfold openv.
  rewrite (rw_shift_name_distinct a b) by easy.
  easy.
Qed.

(* Combined operations *)

Definition shiftv a {V} v := @openv a V (wkv v).
Definition renv a b {V} v := @openv a V (closev b v).
Definition substv a {V} v := @bindv V (closev a v).

(* We want [shiftv] to reduce whenever [v] is a
   constructor, since [wkv] will always reduce in
   such cases. *)
Arguments shiftv a {V} !v.

(* Add reductions for [renv] and [substv] based on the
   similar reductions for [closev] *)

Lemma rw_renv_free a b c :
  forall {V}, @renv b a V (free c) =
    free (rename_name b a c).
Proof.
  intros; unfold renv.
  destruct (compare_names a c);
    autorewrite with rw_names rw_vars; easy.
Qed.

Lemma rw_substv_shift a c :
  forall {V}, @substv a V (free (shift_name a c)) =
              Some (free c).
Proof.
  intros; unfold substv; autorewrite with rw_vars; easy.
Qed.

Lemma rw_substv_same a :
  forall {V}, @substv a V (free a) = None.
Proof.
  intros; unfold substv; autorewrite with rw_vars; easy.
Qed.

Hint Rewrite @rw_renv_free @rw_substv_shift @rw_substv_same
  : rw_vars.

(* Combined operation reductions based on identities *)

Lemma rw_closev_shiftv a {V} (v : @var V) :
  closev a (shiftv a v) = wkv v.
Proof.
  unfold shiftv; autorewrite with rw_vars; easy.
Qed.

Lemma rw_closev_renv a b {V} (v : @var V) :
  closev a (renv a b v) = closev b v.
Proof.
  unfold renv; autorewrite with rw_vars; easy.
Qed.

Lemma rw_renv_same a {V} (v : @var V) :
  renv a a v = v.
Proof.
  unfold renv; autorewrite with rw_vars; easy.
Qed.

Lemma rw_renv_openv a b {V} (v : @var (S V)) :
  renv b a (openv a v) = openv b v.
Proof.
  unfold renv; autorewrite with rw_vars; easy.
Qed.

Lemma rw_renv_shiftv a b {V} (v : @var V) :
  renv b a (shiftv a v) = shiftv b v.
Proof.
  unfold renv, shiftv; autorewrite with rw_vars; easy.
Qed.

Lemma rw_renv_renv a b c {V} (v : @var V) :
  renv b a (renv a c v) = renv b c v.
Proof.
  unfold renv; autorewrite with rw_vars; easy.
Qed.

Lemma rw_substv_renv a b {V} (v : @var V) :
  substv a (renv a b v) = substv b v.
Proof.
  unfold renv, substv; autorewrite with rw_vars; easy.
Qed.

Lemma rw_substv_shiftv a {V} (v : @var V) :
  substv a (shiftv a v) = Some v.
Proof.
  unfold shiftv, substv; autorewrite with rw_vars; easy.
Qed.

Hint Rewrite @rw_closev_shiftv @rw_closev_renv @rw_renv_same
     @rw_renv_openv @rw_renv_shiftv @rw_renv_renv
     @rw_substv_renv @rw_substv_shiftv
  : rw_vars.

(* Fold combined operations *)

Lemma rw_shiftv_fold a {V} (v : @var V) :
  openv a (wkv v) = shiftv a v.
Proof. easy. Qed.
Lemma rw_renv_fold a b {V} (v : @var V) :
  openv b (closev a v) = renv b a v.
Proof. easy. Qed.
Lemma rw_substv_fold a {V} (v : @var V) :
  bindv (closev a v) = substv a v.
Proof. easy. Qed.

Hint Rewrite @rw_shiftv_fold @rw_renv_fold @rw_substv_fold
  : rw_vars.

(* Combined operations on distinct names *)

Lemma shiftv_distinct {a b} (Hd : distinct_names a b) {V} :
  shiftv a (@free V b) = free b.
Proof.
  cbn; rewrite (rw_shift_name_distinct a b) by easy; easy.
Qed.

Lemma renv_distinct {a b c} (Hd : distinct_names a c) {V} :
  renv b a (@free V c) = free (shift_name b c).
Proof.
  autorewrite with rw_vars.
  rewrite (rw_rename_name_distinct a b c) by easy; easy.
Qed.

Lemma renv_both_distinct {a b c}
      (Hd1 : distinct_names a c) (Hd2 : distinct_names b c) {V} :
  renv b a (@free V c) = free c.
Proof.
  autorewrite with rw_vars.
  rewrite (rw_rename_name_both_distinct a b c) by easy; easy.
Qed.

Lemma substv_distinct {a b} (Hd : distinct_names a b) {V} :
  substv a (@free V b) = Some (free b).
Proof.
  unfold substv; rewrite (closev_distinct Hd); easy.
Qed.

(* [wkv] commutes with [shiftv] and [renv]. We generally
   try to move [wkv] leftwards but carefully to avoid
   breaking confluence. *)

Lemma swap_shiftv_wkv a {V} (v : @var V) :
  shiftv a (wkv v) = wkv (shiftv a v).
Proof. destruct v; easy. Qed.

Lemma swap_renv_wkv a b {V} (v : @var V) :
  renv a b (wkv v) = wkv (renv a b v).
Proof. 
  destruct v; cbn; autorewrite with rw_vars; easy.
Qed.

Lemma rw_bindv_shiftv_wkv a {V} (v : @var V) :
  bindv (shiftv a (wkv v)) = Some (shiftv a v).
Proof.
  rewrite swap_shiftv_wkv; autorewrite with rw_vars; easy.
Qed.

Lemma rw_bindv_renv_wkv a b {V} (v : @var V) :
  bindv (renv a b (wkv v)) = Some (renv a b v).
Proof.
  rewrite swap_renv_wkv; autorewrite with rw_vars; easy.
Qed.

Lemma rw_openv_shiftv_wkv a b {V} (v : @var V) :
  openv a (shiftv b (wkv v)) = shiftv a (shiftv b v).
Proof.
  rewrite swap_shiftv_wkv; autorewrite with rw_vars; easy.
Qed.

Lemma rw_openv_renv_wkv a b c {V} (v : @var V) :
  openv a (renv b c (wkv v)) = shiftv a (renv b c v).
Proof.
  rewrite swap_renv_wkv; autorewrite with rw_vars; easy.
Qed.

Lemma rw_closev_wkv_shiftv a {V} (v : @var V) :
  closev a (wkv (shiftv a v)) = wkv (wkv v).
Proof.
  rewrite <- swap_shiftv_wkv; autorewrite with rw_vars; easy.
Qed.

Lemma rw_renv_wkv_shiftv a b {V} (v : @var V) :
  renv b a (wkv (shiftv a v)) = wkv (shiftv b v).
Proof.
  rewrite swap_renv_wkv; autorewrite with rw_vars; easy.
Qed.

Lemma rw_substv_wkv_shiftv a {V} (v : @var V) :
  substv a (wkv (shiftv a v)) = Some (wkv v).
Proof.
  rewrite <- swap_shiftv_wkv; autorewrite with rw_vars; easy.
Qed.

Lemma rw_closev_wkv_renv a b {V} (v : @var V) :
  closev a (wkv (renv a b v)) = closev b (wkv v).
Proof.
  rewrite <- swap_renv_wkv; autorewrite with rw_vars; easy.
Qed.

Lemma rw_renv_wkv_renv a b c {V} (v : @var V) :
  renv b a (wkv (renv a c v)) = wkv (renv b c v).
Proof.
  rewrite swap_renv_wkv; autorewrite with rw_vars; easy.
Qed.

Lemma rw_substv_wkv_renv a b {V} (v : @var V) :
  substv a (wkv (renv a b v)) = substv b (wkv v).
Proof.
  rewrite <- swap_renv_wkv; autorewrite with rw_vars; easy.
Qed.

Lemma rw_shiftv_shiftv_wkv a b {V} (v : @var V) :
  shiftv a (shiftv b (wkv v)) = shiftv a (wkv (shiftv b v)).
Proof.
  rewrite swap_shiftv_wkv; easy.
Qed.

Lemma rw_renv_shiftv_wkv a b c {V} (v : @var V) :
  renv b a (shiftv c (wkv v)) = renv b a (wkv (shiftv c v)).
Proof.
  rewrite swap_shiftv_wkv; easy.
Qed.

Lemma rw_renv_renv_wkv a b c d {V} (v : @var V) :
  renv b a (renv c d (wkv v)) = renv b a (wkv (renv c d v)).
Proof.
  rewrite swap_renv_wkv; easy.
Qed.

Hint Rewrite @rw_bindv_shiftv_wkv @rw_bindv_renv_wkv
     @rw_openv_shiftv_wkv @rw_openv_renv_wkv
     @rw_closev_wkv_shiftv @rw_renv_wkv_shiftv
     @rw_substv_wkv_shiftv @rw_closev_wkv_renv
     @rw_renv_wkv_renv @rw_substv_wkv_renv
     @rw_shiftv_shiftv_wkv @rw_renv_shiftv_wkv
     @rw_renv_renv_wkv
  : rw_vars.

(* Comparison of vars *)

Inductive var_comparison (a : name) {V} : @var V -> Set :=
| samev : var_comparison a (@free V a)
| diffv v : var_comparison a (shiftv a v).

Definition compare_vars a {V} (v : @var V)
  : var_comparison a v.
  destruct v as [b|l].
  destruct (compare_names a b).
  - constructor.
  - change (free (shift_name a b))
      with (shiftv a (@free V b)).
    constructor.
  - change (bound l) with (shiftv a (bound l)).
    constructor.
Qed.

(* Comparison with [bound l0] *)

Inductive l0_comparison {V} : @var (S V) -> Set :=
| samel0 : l0_comparison (@bound (S V) (@l0 (level V)))
| diffl0 v : l0_comparison (wkv v).

Definition compare_l0 {V} (v : @var (S V)) : l0_comparison v.
Proof.
  destruct v as [a|[|l]].
  - change (@free (S V) a)
      with (@wkv V (free a)); constructor.
  - constructor.
  - change (@bound (S V) (lS l))
      with (@wkv V (bound l)); constructor.
Qed.

(* A couple of useful commuting lemmas *)

Lemma swap_shiftv_shiftv_distinct {a b} (Hd : distinct_names a b)
      {V} (v : @var V) :
  shiftv a (shiftv b v) = shiftv b (shiftv a v).
Proof.
  destruct v as [c|l]; cbn; try easy.
  case_strings b c; try easy.
  rewrite (rw_shift_name_distinct a c).
  - rewrite (rw_shift_name_distinct a _);
      replace (n_string c) with (n_string b); easy.
  - unfold distinct_names, indistinct_names.
    replace (n_string c) with (n_string b); easy.
Qed.

Lemma swap_shift_close {a b} (Hd : distinct_names b a)
      {V} (v : @var V) :
  closev a (shiftv b v) = shiftv b (closev a v).
Proof.
  destruct (compare_vars a v).
  - rewrite shiftv_distinct by easy.
    autorewrite with rw_vars rw_names.
    easy.
  - rewrite swap_shiftv_shiftv_distinct by easy.
    autorewrite with rw_vars rw_names.
    rewrite swap_shiftv_wkv; easy.
Qed.

Definition swap_bound {V} (v : @var (S (S V))) : @var (S (S V)) :=
  match v with
  | free a => free a
  | bound l =>
    @bound (S (S V))
    (match l with
     | l0 => lS l0
     | lS l0 => l0
     | lS (lS v) => lS (lS v)
     end)
  end.

Lemma swap_close_close {x y}
      (Hd : distinct_names x y) {V} {v : @var V} :
  closev x (closev y v) = swap_bound (closev y (closev x v)).
Proof.
  destruct (compare_vars y v); autorewrite with rw_vars; cbn.
  - replace (free y) with (shiftv x (@free V y)).
    + autorewrite with rw_vars; easy.
    + rewrite (shiftv_distinct Hd); easy.
  - rewrite swap_shift_close
      by auto using distinct_names_symmetric.
    autorewrite with rw_vars.
    destruct v as [n|l]; cbn; try easy.
    destruct (compare_names x n);
      autorewrite with rw_vars; easy.
Qed.

(* Algebra of operations on [var 0] *)
Inductive renaming {trm : Set} :=
| r_id
| r_comp (r : renaming) (s : renaming)
| r_shift (b : name) (r : renaming)
| r_rename (b : name) (r : renaming) (a : name)
| r_subst (t : trm) (r : renaming) (a : name).

Notation "r1 ; r2" := (r_comp r1 r2)
  (at level 57, right associativity) : ren_scope.
Notation "r , ^ a" := (r_shift a r)
  (at level 47, left associativity) : ren_scope.
Notation "r , a <- b" := (r_rename a r b)
  (at level 47, left associativity, a at next level) : ren_scope.
Notation "r , u // a" := (r_subst u r a)
  (at level 47, left associativity, u at next level) : ren_scope.
Notation "^ a" := (r_shift a r_id)
  (at level 47, left associativity) : ren_scope.
Notation "a <- b" := (r_rename a r_id b)
  (at level 47, left associativity) : ren_scope.
Notation "u // a" := (r_subst u r_id a)
  (at level 47, left associativity) : ren_scope.
Notation "r , a" := (r_rename a r a)
  (at level 47, left associativity) : ren_scope.

Delimit Scope ren_scope with ren.

Fixpoint total {trm : Set} (r : @renaming trm) : Prop :=
  match r with
  | r_id => True
  | r_comp r s => total r /\ total s
  | r_shift b r => total r
  | r_rename b r a => total r
  | r_subst u r a => False
  end.

Definition proj1 {A B : Prop} (H : A /\ B) := let (a, _) := H in a.
Definition proj2 {A B : Prop} (H : A /\ B) := let (_, b) := H in b.

Fixpoint applyt {trm : Set} (r : @renaming trm) :
  forall (rn : total r), morph (@var) 0 (@var) 0 :=
  match r with
  | r_id =>
    fun _ _ v => v
  | r_comp r s =>
    fun rn V v => applyt r (proj1 rn) V (applyt s (proj2 rn) V v)
  | r_shift b r =>
    fun rn V v => openv b (applyt r rn (S V) (wkv v))
  | r_rename b r a =>
    fun rn V v => openv b (applyt r rn (S V) (closev a v))
  | r_subst _ _ _ => False_rec _
  end.

Arguments applyt {trm} !r rn {V} t /.

Lemma rw_applyt_bound trm (r : @renaming trm) rn :
  forall {V} (v : level V),
    applyt r rn (bound v) = bound v.
Proof.
  induction r; try destruct rn; cbn; intros; auto;
    repeat match goal with [ H : _ |- _ ] => rewrite H; clear H end;
    cbn; easy.
Qed.

Hint Rewrite @rw_applyt_bound : rw_names.

Lemma rw_applyt_wkv :
  forall trm (r : @renaming trm) (rn : total r) {V} (v : @var V),
    applyt r rn (wkv v) = wkv (applyt r rn v).
Proof.
  induction r; cbn; intuition.
  - rewrite IHr2, IHr1; reflexivity.
  - repeat rewrite IHr.
    autorewrite with rw_vars.
    rewrite <- swap_shiftv_wkv; reflexivity.
  - destruct (compare_vars a v).
    + autorewrite with rw_vars rw_names; reflexivity.
    + autorewrite with rw_vars.
      repeat rewrite IHr.
      autorewrite with rw_vars.
      rewrite <- swap_shiftv_wkv; reflexivity.
Qed.

Hint Rewrite @rw_applyt_wkv : rw_names.

Lemma rw_applyt_wkv_free trm (r : @renaming trm) rn {a V} :
  applyt r rn (@free (S V) a) = wkv (applyt r rn (@free V a)).
Proof.
  change (@free (S V) a) with (wkv (@free V a)).
  apply rw_applyt_wkv.
Qed.

Hint Rewrite @rw_applyt_wkv_free : rw_names.

