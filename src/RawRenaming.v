Require Import Label PeanoNat Psatz Ring Compare_dec StrictProp.
Require Import Var.

Definition incoming_item : Set := (option label) * nat.

Definition incoming := list incoming_item.

Definition apply_incoming_item
           (vn : var + nat) (inc : incoming_item)
  : var + nat :=
  match vn with
  | inl v =>
    match inc with
    | (l, m) =>
      if label_opt_eqb l (v_label_opt v) then
        match v_nat v with
        | 0 => inr m
        | S n => inl (mk_var (v_label_opt v) n)
        end
      else
        vn
    end
  | inr n => vn
  end.

Definition apply_incoming inc vn :=
  List.fold_left apply_incoming_item inc vn.

Lemma apply_incoming_cons_inv hd tl vn :
  apply_incoming (cons hd tl) vn
  = apply_incoming tl (apply_incoming_item vn hd).
Proof. reflexivity. Qed.

Definition incoming_item_less_than
           (n : nat) (inc : incoming_item) :=
  Nat.ltb (snd inc) n.

Definition incoming_less_than (n : nat) (inc : incoming) :=
  List.forallb (incoming_item_less_than n) inc.

Lemma incoming_less_than_cons_inv n hd tl :
  incoming_less_than n (cons hd tl)
  = andb (incoming_item_less_than n hd)
         (incoming_less_than n tl).
Proof. reflexivity. Qed.

Definition incoming_item_is_less_than n inc : SProp :=
  if incoming_item_less_than n inc then sUnit
  else sEmpty.

Definition incoming_is_less_than n inc : SProp :=
  if incoming_less_than n inc then sUnit
  else sEmpty.

Lemma incoming_is_less_than_head n inc rest :
  incoming_is_less_than n (inc :: rest)%list ->
  incoming_item_is_less_than n inc.
Proof.
  unfold incoming_is_less_than, incoming_item_is_less_than.
  rewrite incoming_less_than_cons_inv.
  destruct incoming_item_less_than; easy.
Qed.

Lemma incoming_is_less_than_tail n inc rest :
  incoming_is_less_than n (inc :: rest)%list ->
  incoming_is_less_than n rest.
Proof.
  unfold incoming_is_less_than, incoming_item_is_less_than.
  rewrite incoming_less_than_cons_inv.
  destruct incoming_item_less_than; easy.
Qed.

Definition outgoing_item := option label.

Definition outgoing := list outgoing_item.

Definition apply_outgoing_item
           (otg : outgoing_item) (vn : var + nat)
  : var + nat :=
  match vn with
  | inr n =>
    match n with
    | 0 => inl (mk_var otg 0)
    | S n => inr n
    end
  | inl v =>
    if label_opt_eqb otg (v_label_opt v) then
      inl (mk_var (v_label_opt v) (S (v_nat v)))
    else
      vn
  end.

Definition apply_outgoing otg vn :=
  List.fold_right apply_outgoing_item vn otg.

Lemma apply_outgoing_cons_inv hd tl vn :
  apply_outgoing (cons hd tl) vn
  = apply_outgoing_item hd (apply_outgoing tl vn).
Proof. reflexivity. Qed.

Definition vn_less_than n (vn : var + nat) :=
  match vn with
  | inl _ => true
  | inr m => Nat.ltb m n
  end.

Definition vn_is_less_than n vn : SProp :=
  if vn_less_than n vn then sUnit
  else sEmpty.
 
Lemma vn_is_less_than_inr_succ n m :
  vn_is_less_than (S n) (inr (S m)) ->
  vn_is_less_than n (inr m).
Proof. induction n; easy. Qed.

Lemma apply_incoming_less_than n inc vn :
  incoming_is_less_than n inc ->
  vn_is_less_than n vn ->
  vn_is_less_than n (apply_incoming inc vn).
Proof.
  intro Hinc.
  generalize dependent vn.
  induction inc as [|[l m] tl]; intros vn Hv; try easy.
  apply incoming_is_less_than_head in Hinc as Hinc1.
  apply incoming_is_less_than_tail in Hinc as Hinc2.
  rewrite apply_incoming_cons_inv.
  apply (IHtl Hinc2).
  destruct vn as [v|o]; cbn; try easy.
  destruct label_opt_eqb, (v_nat v); easy.
Qed.

Lemma apply_outgoing_item_less_than n otg vn :
  vn_is_less_than (S n) vn ->
  vn_is_less_than n (apply_outgoing_item otg vn).
Proof.
  destruct vn as [v|[|m]]; cbn; try easy.
  destruct (label_opt_eqb otg (v_label_opt v)); easy.
Qed.   

Lemma apply_outgoing_less_than otg :
  forall n vn,
    vn_is_less_than (n + List.length otg) vn ->
    vn_is_less_than n (apply_outgoing otg vn).
Proof.
  induction otg as [|l tl]; intros n vn Hv.
  - rewrite <- plus_n_O in Hv; easy.
  - rewrite apply_outgoing_cons_inv.
    apply apply_outgoing_item_less_than.
    apply IHtl.
    cbn in Hv.
    rewrite <- plus_n_Sm in Hv.
    easy.
Qed.

Lemma apply_renaming_var_less_than inc otg v :
  incoming_is_less_than (List.length otg) inc ->
  vn_is_less_than 0
    (apply_outgoing otg (apply_incoming inc (inl v))).
Proof.
  intros Hin.
  apply apply_outgoing_less_than.
  apply apply_incoming_less_than; easy.
Qed.

Definition apply_renaming inc otg {H : incoming_is_less_than (List.length otg) inc} v :=
  (match apply_outgoing otg (apply_incoming inc (inl v)) as vn return vn_is_less_than 0 vn -> var with
   | inl v' => fun _ => v'
   | inr _ => fun H => match H with end
   end)
    (apply_renaming_var_less_than inc otg v H).

Fixpoint add_incoming (i : incoming_item) (inc : incoming) :=
  match inc with
  | nil => cons i nil
  | cons i' tl =>
        if is_less_than_label_opt (fst i) (fst i') then cons i' (add_incoming i tl)
        else cons i (cons i' tl)
  end.

Lemma apply_incoming_item_separate vn i1 i2 :
  label_opt_eqb (fst i1) (fst i2) = false ->
  apply_incoming_item (apply_incoming_item vn i1) i2
  = apply_incoming_item (apply_incoming_item vn i2) i1.
Proof.
  intro H.
  destruct vn as [v|n]; cbn; try easy.
  destruct i1 as (l1, m1); destruct i2 as (l2, m2); cbn in H.
  destruct (label_opt_eqb l1 (v_label_opt v)) eqn:Heq1; cbn;
    destruct (label_opt_eqb l2 (v_label_opt v)) eqn:Heq2; cbn.
  - rewrite label_opt_eqb_symmetric in Heq2.
    rewrite label_opt_eqb_transitive with (so1 := l1) in Heq2; try easy.
    rewrite H in Heq2; easy.
  - destruct (v_nat v) eqn:Hn; cbn; rewrite Heq1, ?Heq2; easy.
  - destruct (v_nat v) eqn:Hn; cbn; rewrite ?Heq1; easy.
  - destruct (v_nat v) eqn:Hn; cbn; rewrite Heq1; easy.
Qed.

Lemma apply_add_incoming i inc vn :
  apply_incoming (add_incoming i inc) vn
  = apply_incoming (cons i inc) vn.
Proof.
  generalize dependent vn.
  induction inc as [|hd tl]; intro vn; cbn.
  - easy.
  - destruct (is_less_than_label_opt (fst i) (fst hd)) eqn:Hlt; cbn.
    + rewrite IHtl; cbn.
      rewrite apply_incoming_item_separate; try easy.
      rewrite label_opt_eqb_symmetric.
      apply is_less_than_label_opt_not_equal; easy.
    + easy.
Qed.

Definition rotate_nat (from : nat) (to : nat) (n : nat) :=
  if Nat.eqb n from then to
  else
    plus (if Nat.leb to n then 1 else 0)
         (minus n (if Nat.ltb from n then 1 else 0)).

Lemma rotate_nat_id m n :
  rotate_nat m m n = n.
Proof.
  unfold rotate_nat.
  destruct (Nat.eqb n m) eqn:Heq.
  - rewrite Nat.eqb_eq in Heq; easy.
  - rewrite Nat.eqb_neq in Heq.
    destruct (Nat.leb m n) eqn:Hle.
    + rewrite Nat.leb_le in Hle.
      destruct (Nat.ltb m n) eqn:Hlt.
      * rewrite Nat.ltb_lt in Hlt; lia.
      * rewrite Nat.ltb_nlt in Hlt; lia.
    + rewrite Nat.leb_nle in Hle.
      destruct (Nat.ltb m n) eqn:Hlt.
      * rewrite Nat.ltb_lt in Hlt; lia.
      * rewrite Nat.ltb_nlt in Hlt; lia.
Qed.

Definition rotate_vn (from : nat) (to : nat) (vn : var + nat) :=
  match vn with
  | inl v => vn
  | inr n => inr (rotate_nat from to n)
  end.

Lemma rotate_vn_id n vn :
  rotate_vn n n vn = vn.
Proof.
  destruct vn; cbn; rewrite ?rotate_nat_id; easy.
Qed.

Fixpoint add_outgoing_aux (otg : outgoing) (o : outgoing_item) (acc : nat) : outgoing * nat :=
  match otg with
  | nil => (cons o otg , acc)
  | cons o' tl =>
        if is_less_than_label_opt o o' then
          match add_outgoing_aux tl o (S acc) with
          | (otg, idx) => (cons o' otg, idx)
          end
        else (cons o otg, acc)
  end.

Lemma apply_add_outgoing_aux otg o :
  forall acc vn,
    apply_outgoing (fst (add_outgoing_aux o otg acc))
      (rotate_vn (List.length otg + acc) (snd (add_outgoing_aux o otg acc)) vn)
    = apply_outgoing (cons o otg) (rotate_vn (List.length otg + acc) vn.
Proof.
  induction otg as [|o' otg']; cbn.
  - rewrite rotate_vn_id; easy.
  - destruct (is_less_than_label_opt o o').
    + 


Definition add_outgoing o otg := add_outgoing_aux otg o 0.

Lemma apply_add_outgoing o otg vn :
  apply_outgoing (fst (add_outgoing o otg))
    (rotate_vn (List.length otg) (snd (add_outgoing o otg)) vn)
  = apply_outgoing (otg ++ (cons o nil)) vn.
Proof.
  induction otg as [|o' otg']; cbn.
  - rewrite rotate_vn_id; easy.
  - destruct (is_less_than_label_opt o o').
    + 

Definition apply_rotation_incoming_item r (inc : incoming_item) :=
  match inc with
  | (l, m) => (l, rotate_nat r m)
  end.

Definition apply_rotation_incoming r (inc : incoming) :=
  List.map (apply_rotation_incoming_item r) inc.

(* TODO:
   - Define composition
   - Prove composition with identity
   - Prove associativity of composition
   - Define normalized predicate and normalization
   - Prove extentiality of normalized case *)
   
