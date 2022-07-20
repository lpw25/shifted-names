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
           (vn : var + nat) (otg : option label)
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
  List.fold_left apply_outgoing_item otg vn.

Lemma apply_outgoing_cons_inv hd tl vn :
  apply_outgoing (cons hd tl) vn
  = apply_outgoing tl (apply_outgoing_item vn hd).
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

Lemma apply_outgoing_less_than n otg vn :
  vn_is_less_than (n + List.length otg) vn ->
  vn_is_less_than n (apply_outgoing otg vn).
Proof.
  generalize dependent vn.
  induction otg as [|l tl]; intros vn Hv.
  - rewrite <- plus_n_O in Hv; easy.
  - rewrite apply_outgoing_cons_inv.
    apply IHtl.
    destruct vn as [v|[|m]]; cbn; try easy.
    + destruct label_opt_eqb; easy.
    + cbn in Hv.
      rewrite <- plus_n_Sm in Hv.
      apply vn_is_less_than_inr_succ; easy.
Qed.

Lemma apply_renaming_var_less_than v inc otg :
  incoming_is_less_than (List.length otg) inc ->
  vn_is_less_than 0
    (apply_outgoing otg (apply_incoming inc (inl v))).
Proof.
  intros Hin.
  apply apply_outgoing_less_than.
  apply apply_incoming_less_than; easy.
Qed.

Definition apply_renaming inc otg
           {H : incoming_is_less_than (List.length otg) inc}
           v :=
  match apply_outgoing otg (apply_incoming inc (inl v)) with
  | inl v' => v'
  | inr _ => 

