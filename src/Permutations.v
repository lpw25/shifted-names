
Require Import List Psatz.

Definition swap := nat.

Definition permutation := list swap.

Fixpoint apply_swap {A : Type} (l : list A) s {struct s} : list A :=
  match s with
  | S s' =>
      match l with
      | nil => l
      | cons x l' => cons x (apply_swap l' s')
      end
  | 0 =>
      match l with
      | nil => l
      | cons x nil => l
      | cons x (cons y l) => cons y (cons x l)
      end
  end.

Definition apply_permutation {A : Type} (p : permutation) (l : list A) : list A :=
  List.fold_left apply_swap p l.

Definition swap_length s := S (S s).

Arguments swap_length / s.

Definition permutation_length (p : permutation) : nat :=
  List.fold_left (fun l1 s => max l1 (swap_length s)) p 0.

Fixpoint apply_swap_nat n s {struct s} :=
  match s with
  | S s' =>
      match n with
      | 0 => n
      | S n' => S (apply_swap_nat n' s')
      end
  | 0 =>
      match n with
      | 0 => S 0
      | S 0 => 0
      | S (S _) => n
      end
  end.

Definition apply_permutation_nat (p : permutation) (n : nat) : nat :=
  List.fold_left apply_swap_nat p n.

Lemma swap_nth s :
  forall {A} (l : list A) n d,
    swap_length s <= length l ->
    nth n l d = nth (apply_swap_nat n s) (apply_swap l s) d.
Proof.
  induction s; intros A l n d; cbn.
  - destruct n as [|[|n']]; destruct l as [|x [|y l']];
      cbn; try easy; lia.
  - destruct n as [|n']; destruct l as [| l']; cbn; try easy; intros Hl.
    apply IHs; cbn.
    lia.
Qed.

Lemma permutation_nth p :
  forall {A} (l : list A) n d,
    permutation_length p <= length l ->
    nth n l d = nth (apply_permutation_nat p n) (apply_permutation p l) d.
Proof.
  unfold apply_permutation, apply_permutation_nat, permutation_length.
  induction p; intros A l n d; cbn; try easy.
  apply IHp.

  - destruct l as [|a l]; try easy.
    destruct n as [|n]; try easy; cbn; intro Hl.
    apply IHp.
    lia.
  - 
  - 
  - 
