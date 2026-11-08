(** * Braun trees: canonical persistent sequences

    A Braun tree stores a sequence with its first element at the root, the
    elements at odd positions (1, 3, 5, ...) in the left subtree and those at
    even positions (2, 4, ...) in the right one.  The left subtree is never
    smaller than the right one and at most one larger, so the shape of a
    Braun tree is determined by its size: a sequence has exactly one Braun
    tree ([canonical]).  That is what lets adjustments built from them be
    compared with Leibniz equality.

    The sequence a tree denotes is [to_list]; every operation is specified
    by what it does to that sequence.  Adding or removing at either end,
    reading and changing an element are O(log n); mapping is O(n). *)

From Stdlib Require Import Arith List Lia.
Import ListNotations.

Inductive braun (A : Type) : Type :=
| BE : braun A
| BN : A -> braun A -> braun A -> braun A.

Arguments BE {A}.
Arguments BN {A} _ _ _.

Section Braun.

Context {A : Type}.

Implicit Types (t l r : braun A) (x y : A) (i j : nat).

Fixpoint size t : nat :=
  match t with
  | BE => 0
  | BN _ l r => S (size l + size r)
  end.

Fixpoint balanced t : Prop :=
  match t with
  | BE => True
  | BN _ l r => size r <= size l <= S (size r) /\ balanced l /\ balanced r
  end.

(** ** The sequence a tree denotes *)

Fixpoint interleave (xs ys : list A) : list A :=
  match xs with
  | [] => ys
  | x :: xs' =>
      match ys with
      | [] => x :: xs'
      | y :: ys' => x :: y :: interleave xs' ys'
      end
  end.

Fixpoint to_list t : list A :=
  match t with
  | BE => []
  | BN x l r => x :: interleave (to_list l) (to_list r)
  end.

(** ** Operations *)

(** The element at position [i]. *)
Fixpoint nth i t : option A :=
  match t with
  | BE => None
  | BN x l r =>
      match i with
      | 0 => Some x
      | S i' => if Nat.even i' then nth (Nat.div2 i') l else nth (Nat.div2 i') r
      end
  end.

(** Changing the element at position [i]. *)
Fixpoint update i (f : A -> A) t : braun A :=
  match t with
  | BE => BE
  | BN x l r =>
      match i with
      | 0 => BN (f x) l r
      | S i' => if Nat.even i' then BN x (update (Nat.div2 i') f l) r
                else BN x l (update (Nat.div2 i') f r)
      end
  end.

(** Adding at the front: every other position moves one along, so the old
    root and right subtree become the new left subtree. *)
Fixpoint cons x t : braun A :=
  match t with
  | BE => BN x BE BE
  | BN y l r => BN x (cons y r) l
  end.

(** Removing the first element. *)
Fixpoint tail t : braun A :=
  match t with
  | BE => BE
  | BN _ l r =>
      match l with
      | BE => BE
      | BN y _ _ => BN y r (tail l)
      end
  end.

(** Adding a new last element, at position [i = size t]. *)
Fixpoint add_at i x t : braun A :=
  match t with
  | BE => BN x BE BE
  | BN y l r =>
      match i with
      | 0 => BN y l r
      | S i' => if Nat.even i' then BN y (add_at (Nat.div2 i') x l) r
                else BN y l (add_at (Nat.div2 i') x r)
      end
  end.

Definition snoc t x : braun A := add_at (size t) x t.

(** Removing the last element, at position [i = size t - 1]. *)
Fixpoint drop_at i t : braun A :=
  match t with
  | BE => BE
  | BN y l r =>
      match i with
      | 0 => BE
      | S i' => if Nat.even i' then BN y (drop_at (Nat.div2 i') l) r
                else BN y l (drop_at (Nat.div2 i') r)
      end
  end.

Definition unsnoc t : braun A := drop_at (pred (size t)) t.

Definition last t : option A := nth (pred (size t)) t.

(** Building a tree from a list. *)
Definition of_list (xs : list A) : braun A := fold_right cons BE xs.

End Braun.

Fixpoint map {A B} (f : A -> B) (t : braun A) : braun B :=
  match t with
  | BE => BE
  | BN x l r => BN (f x) (map f l) (map f r)
  end.

(** ** Arithmetic of positions *)

Lemma even_double n : Nat.even (n + n) = true.
Proof. replace (n + n) with (2 * n) by lia; apply Nat.even_mul. Qed.

Lemma div2_double n : Nat.div2 (n + n) = n.
Proof. replace (n + n) with (2 * n) by lia; apply Nat.div2_double. Qed.

Lemma even_double_S n : Nat.even (S (n + n)) = false.
Proof. rewrite Nat.even_succ, <- Nat.negb_even, even_double; reflexivity. Qed.

Lemma div2_double_S n : Nat.div2 (S (n + n)) = n.
Proof. replace (n + n) with (2 * n) by lia; apply Nat.div2_succ_double. Qed.

(** Two positions are equal when their parities and halves are. *)
Lemma pos_eq_iff i j : i = j <-> Nat.even i = Nat.even j /\ Nat.div2 i = Nat.div2 j.
Proof.
  split; [intros ->; auto|intros [E D]].
  rewrite (Nat.div2_odd i), (Nat.div2_odd j), <- !Nat.negb_even, E, D; reflexivity.
Qed.

Section Facts.

Context {A : Type}.

Implicit Types (t u l r : braun A) (x y : A) (i j : nat).

(** ** Lists and interleaving *)

Lemma interleave_length (xs ys : list A) : length (interleave xs ys) = length xs + length ys.
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys]; cbn; try reflexivity; [lia|].
  rewrite IH; lia.
Qed.

Lemma interleave_cons a (xs ys : list A) : interleave (a :: xs) ys = a :: interleave ys xs.
Proof.
  revert a ys; induction xs as [|x xs IH]; intros a [|y ys]; try reflexivity.
  change (interleave (a :: x :: xs) (y :: ys)) with (a :: y :: interleave (x :: xs) ys).
  rewrite IH; reflexivity.
Qed.

Lemma to_list_length t : length (to_list t) = size t.
Proof. induction t; cbn; [reflexivity|rewrite interleave_length; lia]. Qed.

Lemma interleave_nth (xs ys : list A) i :
  length ys <= length xs <= S (length ys) ->
  nth_error (interleave xs ys) i
  = if Nat.even i then nth_error xs (Nat.div2 i) else nth_error ys (Nat.div2 i).
Proof.
  revert xs ys; induction i as [i IH] using lt_wf_ind; intros xs ys Hl.
  destruct xs as [|x xs].
  - destruct ys; cbn in Hl; [|lia].
    destruct (Nat.even i); rewrite !nth_error_nil; reflexivity.
  - destruct ys as [|y ys].
    + cbn in Hl; assert (xs = []) as -> by (destruct xs; [reflexivity|cbn in Hl; lia]).
      destruct i as [|[|i]]; cbn; [reflexivity|reflexivity|].
      rewrite nth_error_nil; destruct (Nat.even i), (Nat.div2 i); reflexivity.
    + destruct i as [|[|i]]; [reflexivity|reflexivity|]; cbn [interleave nth_error].
      rewrite IH by (cbn in Hl |- *; lia).
      change (Nat.even (S (S i))) with (Nat.even i).
      change (Nat.div2 (S (S i))) with (S (Nat.div2 i)).
      destruct (Nat.even i); reflexivity.
Qed.

Lemma balanced_lengths x l r :
  balanced (BN x l r) -> length (to_list r) <= length (to_list l) <= S (length (to_list r)).
Proof. intros [Hs _]; rewrite !to_list_length; exact Hs. Qed.

(** Reading a tree is reading its sequence. *)
Lemma nth_to_list t i : balanced t -> nth i t = nth_error (to_list t) i.
Proof.
  revert i; induction t as [|x l IHl r IHr]; intros i Hb.
  - cbn; rewrite nth_error_nil; reflexivity.
  - destruct i as [|i]; [reflexivity|].
    pose proof (balanced_lengths _ _ _ Hb) as Hs; destruct Hb as [_ [Hl Hr]].
    cbn [nth to_list nth_error]; rewrite interleave_nth by exact Hs.
    destruct (Nat.even i); auto.
Qed.

Lemma list_ext (xs ys : list A) :
  length xs = length ys -> (forall i, nth_error xs i = nth_error ys i) -> xs = ys.
Proof. intros _ H; apply nth_error_ext, H. Qed.

(** ** Canonicity *)

Theorem canonical t u : balanced t -> balanced u -> to_list t = to_list u -> t = u.
Proof.
  revert u; induction t as [|x l IHl r IHr]; intros [|y l' r'] Ht Hu H; cbn in H;
    try discriminate; [reflexivity|].
  injection H as -> H.
  pose proof (balanced_lengths _ _ _ Ht) as Hs; pose proof (balanced_lengths _ _ _ Hu) as Hs'.
  destruct Ht as [_ [Hl Hr]], Hu as [_ [Hl' Hr']].
  assert (Hn : length (to_list l) + length (to_list r) = length (to_list l') + length (to_list r'))
    by (rewrite <- !interleave_length, H; reflexivity).
  assert (E1 : length (to_list l) = length (to_list l')) by lia.
  assert (E2 : length (to_list r) = length (to_list r')) by lia.
  f_equal; [apply IHl|apply IHr]; auto; apply list_ext; auto; intros i.
  - pose proof (f_equal (fun xs => nth_error xs (i + i)) H) as Hi; cbn beta in Hi.
    rewrite !interleave_nth, even_double, div2_double in Hi by assumption; exact Hi.
  - pose proof (f_equal (fun xs => nth_error xs (S (i + i))) H) as Hi; cbn beta in Hi.
    rewrite !interleave_nth, even_double_S, div2_double_S in Hi by assumption; exact Hi.
Qed.

(** ** Each operation, on the sequence *)

Lemma size_cons x t : size (cons x t) = S (size t).
Proof. revert x; induction t as [|y l IHl r IHr]; intros x; cbn; [reflexivity|rewrite IHr; lia]. Qed.

Lemma balanced_cons x t : balanced t -> balanced (cons x t).
Proof.
  revert x; induction t as [|y l IHl r IHr]; intros x; cbn; [intros; repeat split; auto|].
  intros [Hs [Hl Hr]]; rewrite size_cons; repeat split; auto; lia.
Qed.

Lemma to_list_cons x t : to_list (cons x t) = x :: to_list t.
Proof.
  revert x; induction t as [|y l IHl r IHr]; intros x; cbn; [reflexivity|].
  rewrite IHr, interleave_cons; reflexivity.
Qed.

Lemma tail_spec t : balanced t -> balanced (tail t) /\ to_list (tail t) = List.tl (to_list t).
Proof.
  induction t as [|x l IHl r IHr]; intros Hb; [cbn; auto|].
  destruct Hb as [Hs [Hl Hr]]; destruct (IHl Hl) as [Hb' Ht'].
  destruct l as [|y l1 r1].
  - cbn in Hs; destruct r; [|cbn in Hs; lia]; cbn; auto.
  - cbn [to_list List.tl] in Ht'.
    assert (Hsz : size (tail (BN y l1 r1)) = size l1 + size r1).
    { rewrite <- to_list_length, Ht', interleave_length, !to_list_length; reflexivity. }
    change (tail (BN x (BN y l1 r1) r)) with (BN y r (tail (BN y l1 r1))).
    split.
    + cbn [balanced]; rewrite Hsz; cbn [size] in Hs; repeat split; auto; lia.
    + cbn [to_list List.tl]; rewrite Ht', interleave_cons; reflexivity.
Qed.

Lemma size_update i f t : size (update i f t) = size t.
Proof.
  revert i; induction t as [|x l IHl r IHr]; intros [|i]; cbn; auto.
  destruct (Nat.even i); cbn; rewrite ?IHl, ?IHr; reflexivity.
Qed.

Lemma balanced_update i f t : balanced t -> balanced (update i f t).
Proof.
  revert i; induction t as [|x l IHl r IHr]; intros [|i] Hb; cbn in *; auto.
  destruct Hb as [Hs [Hl Hr]]; destruct (Nat.even i); cbn; rewrite ?size_update; auto.
Qed.

Lemma nth_update i f t j : nth j (update i f t) = if Nat.eqb i j then option_map f (nth j t) else nth j t.
Proof.
  revert i j; induction t as [|x l IHl r IHr]; intros i j; cbn.
  - destruct (Nat.eqb i j); reflexivity.
  - destruct i as [|i], j as [|j]; cbn [Nat.eqb]; try reflexivity.
    all: try (destruct (Nat.even i); reflexivity).
    destruct (Nat.eqb_spec i j) as [->|Hne].
    + destruct (Nat.even j) eqn:Ej; cbn; rewrite Ej; [rewrite IHl|rewrite IHr];
        rewrite Nat.eqb_refl; reflexivity.
    + destruct (Nat.even i) eqn:Ei, (Nat.even j) eqn:Ej; cbn; rewrite ?Ei, ?Ej; try reflexivity;
        [rewrite IHl|rewrite IHr]; replace (Nat.div2 i =? Nat.div2 j) with false; auto;
        symmetry; apply Nat.eqb_neq; intro; apply Hne, pos_eq_iff; split; congruence.
Qed.

Lemma size_add_at t x : balanced t -> size (add_at (size t) x t) = S (size t).
Proof.
  induction t as [|y l IHl r IHr]; cbn; [reflexivity|].
  intros [Hs [Hl Hr]].
  destruct (Nat.eq_dec (size l) (size r)) as [E|E].
  - rewrite E, even_double, div2_double; cbn; rewrite <- E, IHl by exact Hl; lia.
  - assert (size l = S (size r)) as E' by lia; rewrite E'.
    replace (S (size r) + size r) with (S (size r + size r)) by lia.
    rewrite even_double_S, div2_double_S; cbn; rewrite IHr by exact Hr; lia.
Qed.

Lemma add_at_spec t x :
  balanced t ->
  balanced (add_at (size t) x t)
  /\ (forall j, nth j (add_at (size t) x t) = if Nat.eqb j (size t) then Some x else nth j t).
Proof.
  induction t as [|y l IHl r IHr]; intros Hb.
  - split; [cbn; repeat split; lia|].
    intros [|j]; cbn; [reflexivity|]; destruct (Nat.even j); reflexivity.
  - destruct Hb as [Hs [Hl Hr]].
    destruct (Nat.eq_dec (size l) (size r)) as [E|E].
    + (* the new element goes at the end of the left subtree *)
      assert (Hev : Nat.even (size l + size r) = true /\ Nat.div2 (size l + size r) = size l)
        by (rewrite <- E, even_double, div2_double; auto).
      destruct Hev as [Hev Hdv].
      change (add_at (size (BN y l r)) x (BN y l r))
        with (if Nat.even (size l + size r) then BN y (add_at (Nat.div2 (size l + size r)) x l) r
              else BN y l (add_at (Nat.div2 (size l + size r)) x r)).
      rewrite Hev, Hdv.
      destruct (IHl Hl) as [Hb' Hn']; split.
      * cbn; rewrite size_add_at by exact Hl; repeat split; auto; lia.
      * intros [|j]; [reflexivity|]; cbn [size nth Nat.eqb].
        destruct (Nat.even j) eqn:Ej.
        -- rewrite Hn'; replace (Nat.div2 j =? size l) with (j =? size l + size r); [reflexivity|].
           apply Bool.eq_iff_eq_true; rewrite !Nat.eqb_eq; split.
           ++ intros ->; exact Hdv.
           ++ intros Hd; apply pos_eq_iff; split; congruence.
        -- replace (j =? size l + size r) with false; [reflexivity|].
           symmetry; apply Nat.eqb_neq; intros ->; congruence.
    + (* the new element goes at the end of the right subtree *)
      assert (Hev : Nat.even (size l + size r) = false /\ Nat.div2 (size l + size r) = size r).
      { replace (size l + size r) with (S (size r + size r)) by lia.
        rewrite even_double_S, div2_double_S; auto. }
      destruct Hev as [Hev Hdv].
      change (add_at (size (BN y l r)) x (BN y l r))
        with (if Nat.even (size l + size r) then BN y (add_at (Nat.div2 (size l + size r)) x l) r
              else BN y l (add_at (Nat.div2 (size l + size r)) x r)).
      rewrite Hev, Hdv.
      destruct (IHr Hr) as [Hb' Hn']; split.
      * cbn; rewrite size_add_at by exact Hr; repeat split; auto; lia.
      * intros [|j]; [reflexivity|]; cbn [size nth Nat.eqb].
        destruct (Nat.even j) eqn:Ej.
        -- replace (j =? size l + size r) with false; [reflexivity|].
           symmetry; apply Nat.eqb_neq; intros ->; congruence.
        -- rewrite Hn'; replace (Nat.div2 j =? size r) with (j =? size l + size r); [reflexivity|].
           apply Bool.eq_iff_eq_true; rewrite !Nat.eqb_eq; split.
           ++ intros ->; exact Hdv.
           ++ intros Hd; apply pos_eq_iff; split; congruence.
Qed.

Lemma snoc_spec t x :
  balanced t -> balanced (snoc t x) /\ to_list (snoc t x) = to_list t ++ [x].
Proof.
  intros Hb; destruct (add_at_spec t x Hb) as [Hb' Hn]; split; [exact Hb'|].
  apply list_ext.
  - rewrite length_app, !to_list_length; cbn; unfold snoc; rewrite size_add_at by exact Hb; lia.
  - intros j; rewrite <- !nth_to_list by assumption; unfold snoc; rewrite Hn.
    destruct (Nat.eqb_spec j (size t)) as [->|Hne].
    + rewrite nth_error_app2 by (rewrite to_list_length; lia).
      rewrite to_list_length, Nat.sub_diag; reflexivity.
    + destruct (Nat.lt_ge_cases j (size t)).
      * rewrite nth_error_app1 by (rewrite to_list_length; lia); apply nth_to_list, Hb.
      * rewrite nth_error_app2 by (rewrite to_list_length; lia).
        rewrite nth_to_list, (proj2 (nth_error_None _ _)) by (try rewrite to_list_length; lia || exact Hb).
        rewrite to_list_length; destruct (j - size t) as [|k] eqn:Ek; [lia|].
        cbn; rewrite nth_error_nil; reflexivity.
Qed.

Lemma drop_at_spec t :
  balanced t -> size t <> 0 ->
  balanced (drop_at (pred (size t)) t)
  /\ size (drop_at (pred (size t)) t) = pred (size t)
  /\ (forall j, nth j (drop_at (pred (size t)) t) = if Nat.eqb j (pred (size t)) then None else nth j t).
Proof.
  induction t as [|y l IHl r IHr]; intros Hb Hz; [contradiction|].
  destruct Hb as [Hs [Hl Hr]]; cbn [size pred drop_at].
  destruct (Nat.eq_dec (size l + size r) 0) as [Z|Z].
  - assert (size l = 0) by lia; assert (size r = 0) by lia.
    destruct l; [|cbn in *; lia]; destruct r; [|cbn in *; lia].
    rewrite Z; cbn; split; [tauto|split; [reflexivity|]].
    intros [|j]; cbn; [reflexivity|]; destruct (Nat.even j); reflexivity.
  - destruct (size l + size r) as [|k] eqn:Ek; [contradiction|].
    destruct (Nat.eq_dec (size l) (size r)) as [E|E].
    + (* the last element is the last of the right subtree *)
      assert (Hk : k = pred (size r + size r)) by lia.
      assert (Er : size r <> 0) by lia.
      assert (Ev : Nat.even k = false /\ Nat.div2 k = pred (size r)).
      { destruct (size r) as [|s] eqn:Es; [contradiction|].
        replace k with (S (s + s)) by lia; rewrite even_double_S, div2_double_S; auto. }
      destruct Ev as [Ev Dv]; rewrite Ev, Dv.
      destruct (IHr Hr Er) as [Hb' [Hz' Hn']]; split; [|split].
      * cbn; rewrite Hz'; repeat split; auto; lia.
      * cbn; rewrite Hz'; lia.
      * intros [|j]; cbn [nth Nat.eqb]; [reflexivity|].
        destruct (Nat.even j) eqn:Ej; [|rewrite Hn'].
        -- replace (j =? k) with false; [reflexivity|].
           symmetry; apply Nat.eqb_neq; intros ->; congruence.
        -- replace (Nat.div2 j =? pred (size r)) with (j =? k); [reflexivity|].
           apply Bool.eq_iff_eq_true; rewrite !Nat.eqb_eq; split; [intros ->; exact Dv|].
           intros Hd; apply pos_eq_iff; split; congruence.
    + (* the last element is the last of the left subtree *)
      assert (El : size l = S (size r)) by lia.
      assert (Ev : Nat.even k = true /\ Nat.div2 k = pred (size l)).
      { replace k with (size r + size r) by lia; rewrite even_double, div2_double; split; [reflexivity|lia]. }
      destruct Ev as [Ev Dv]; rewrite Ev, Dv.
      destruct (IHl Hl ltac:(lia)) as [Hb' [Hz' Hn']]; split; [|split].
      * cbn; rewrite Hz'; repeat split; auto; lia.
      * cbn; rewrite Hz'; lia.
      * intros [|j]; cbn [nth Nat.eqb]; [reflexivity|].
        destruct (Nat.even j) eqn:Ej; [rewrite Hn'|].
        -- replace (Nat.div2 j =? pred (size l)) with (j =? k); [reflexivity|].
           apply Bool.eq_iff_eq_true; rewrite !Nat.eqb_eq; split; [intros ->; exact Dv|].
           intros Hd; apply pos_eq_iff; split; congruence.
        -- replace (j =? k) with false; [reflexivity|].
           symmetry; apply Nat.eqb_neq; intros ->; congruence.
Qed.

Lemma removelast_length (xs : list A) : length (removelast xs) = pred (length xs).
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  destruct xs as [|y xs]; [reflexivity|].
  change (removelast (x :: y :: xs)) with (x :: removelast (y :: xs)).
  cbn [length] in *; rewrite IH; reflexivity.
Qed.

Lemma removelast_nth (xs : list A) i :
  i < pred (length xs) -> nth_error (removelast xs) i = nth_error xs i.
Proof.
  revert i; induction xs as [|x xs IH]; intros i Hi; [reflexivity|].
  destruct xs as [|y xs]; [cbn in Hi; lia|].
  change (removelast (x :: y :: xs)) with (x :: removelast (y :: xs)).
  destruct i; [reflexivity|cbn [nth_error]; apply IH; cbn in *; lia].
Qed.

Lemma unsnoc_spec t :
  balanced t -> balanced (unsnoc t) /\ to_list (unsnoc t) = removelast (to_list t).
Proof.
  intros Hb; unfold unsnoc.
  destruct (Nat.eq_dec (size t) 0) as [Z|Z].
  { destruct t; [|cbn in Z; lia]; cbn; split; auto. }
  destruct (drop_at_spec t Hb Z) as [Hb' [Hz Hn]]; split; [exact Hb'|].
  apply list_ext.
  - rewrite to_list_length, Hz, removelast_length, to_list_length; reflexivity.
  - intros j; rewrite <- nth_to_list by exact Hb'; rewrite Hn.
    destruct (Nat.eqb_spec j (pred (size t))) as [->|Hne].
    + symmetry; apply nth_error_None; rewrite removelast_length, to_list_length; lia.
    + destruct (Nat.lt_ge_cases j (pred (size t))).
      * rewrite removelast_nth by (rewrite to_list_length; lia); apply nth_to_list, Hb.
      * rewrite nth_to_list by exact Hb.
        rewrite !(proj2 (nth_error_None _ _)); auto;
          rewrite ?removelast_length, to_list_length; lia.
Qed.

Lemma last_spec t : balanced t -> last t = nth_error (to_list t) (pred (length (to_list t))).
Proof. intros Hb; unfold last; rewrite nth_to_list, to_list_length by exact Hb; reflexivity. Qed.

Lemma balanced_of_list (xs : list A) : balanced (of_list xs).
Proof. induction xs; cbn; [exact I|apply balanced_cons; assumption]. Qed.

Lemma to_list_of_list (xs : list A) : to_list (of_list xs) = xs.
Proof. unfold of_list; induction xs; cbn; [reflexivity|rewrite to_list_cons, IHxs; reflexivity]. Qed.

(** ** Membership (for any tree) *)

Lemma in_interleave (xs ys : list A) z : In z (interleave xs ys) <-> In z xs \/ In z ys.
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys]; cbn; try tauto.
  rewrite IH; tauto.
Qed.

Lemma in_to_list_node z x l r : In z (to_list (BN x l r)) <-> z = x \/ In z (to_list l) \/ In z (to_list r).
Proof. cbn; rewrite in_interleave; intuition congruence. Qed.

Lemma in_drop_at i t z : In z (to_list (drop_at i t)) -> In z (to_list t).
Proof.
  revert i; induction t as [|x l IHl r IHr]; intros i H; [exact H|].
  destruct i as [|i]; cbn [drop_at] in H; [destruct H|].
  apply in_to_list_node; destruct (Nat.even i); apply in_to_list_node in H;
    destruct H as [H|[H|H]]; eauto.
Qed.

Lemma in_unsnoc t z : In z (to_list (unsnoc t)) -> In z (to_list t).
Proof. apply in_drop_at. Qed.

Lemma in_add_at i x t z : In z (to_list (add_at i x t)) -> z = x \/ In z (to_list t).
Proof.
  revert i; induction t as [|y l IHl r IHr]; intros i H.
  - destruct H as [H|[]]; auto.
  - destruct i as [|i]; cbn [add_at] in H; [auto|].
    rewrite in_to_list_node; destruct (Nat.even i); apply in_to_list_node in H;
      destruct H as [H|[H|H]]; auto;
      [apply IHl in H as [H|H]|apply IHr in H as [H|H]]; auto.
Qed.

Lemma in_snoc t x z : In z (to_list (snoc t x)) -> z = x \/ In z (to_list t).
Proof. apply in_add_at. Qed.

End Facts.

Lemma size_map {A B} (f : A -> B) t : size (map f t) = size t.
Proof. induction t; cbn; congruence. Qed.

Lemma balanced_map {A B} (f : A -> B) t : balanced t -> balanced (map f t).
Proof. induction t; cbn; [auto|]; rewrite !size_map; tauto. Qed.

Lemma to_list_map {A B} (f : A -> B) t : to_list (map f t) = List.map f (to_list t).
Proof.
  induction t as [|x l IHl r IHr]; cbn; [reflexivity|]; f_equal.
  rewrite IHl, IHr; generalize (to_list l) (to_list r); clear.
  intros xs; induction xs as [|x xs IH]; intros [|y ys]; cbn; try reflexivity.
  rewrite IH; reflexivity.
Qed.

Lemma nth_map {A B} (f : A -> B) t i : nth i (map f t) = option_map f (nth i t).
Proof.
  revert i; induction t as [|x l IHl r IHr]; intros [|i]; cbn; try reflexivity.
  destruct (Nat.even i); [apply IHl|apply IHr].
Qed.

Lemma in_update {A} i (f : A -> A) t z :
  In z (to_list (update i f t)) -> In z (to_list t) \/ exists x, In x (to_list t) /\ z = f x.
Proof.
  revert i; induction t as [|x l IHl r IHr]; intros [|i] H; cbn [update] in H; [exact (or_introl H)..| |].
  - apply in_to_list_node in H as [->|[H|H]].
    + right; exists x; split; [apply in_to_list_node; left|]; reflexivity.
    + left; apply in_to_list_node; auto.
    + left; apply in_to_list_node; auto.
  - destruct (Nat.even i); apply in_to_list_node in H as [->|[H|H]];
      try (left; apply in_to_list_node; auto; fail).
    + destruct (IHl _ H) as [H'|[y [Hy ->]]];
        [left|right; exists y; split]; auto; apply in_to_list_node; auto.
    + destruct (IHr _ H) as [H'|[y [Hy ->]]];
        [left|right; exists y; split]; auto; apply in_to_list_node; auto.
Qed.

Lemma empty_canonical {A} (t : braun A) : balanced t -> to_list t = [] -> t = BE.
Proof. intros Hb H; apply (canonical t BE Hb I H). Qed.

(** ** Structural folds

    Defined on the tree itself, so that a function recursing through the
    elements is structurally recursive. *)

Fixpoint ball {A} (f : A -> bool) (t : braun A) : bool :=
  match t with
  | BE => true
  | BN x l r => f x && ball f l && ball f r
  end.

Fixpoint bmax {A} (f : A -> nat) (t : braun A) : nat :=
  match t with
  | BE => 0
  | BN x l r => Nat.max (f x) (Nat.max (bmax f l) (bmax f r))
  end.

Lemma ball_spec {A} (f : A -> bool) t : ball f t = true <-> forall x, In x (to_list t) -> f x = true.
Proof.
  induction t as [|x l IHl r IHr]; cbn [ball]; [split; [intros _ y []|reflexivity]|].
  rewrite !Bool.andb_true_iff, IHl, IHr; split.
  - intros [[Hx Hl] Hr] y Hy; apply in_to_list_node in Hy as [->|[Hy|Hy]]; auto.
  - intros H; repeat split; [apply H, in_to_list_node; auto|intros y Hy|intros y Hy];
      apply H, in_to_list_node; auto.
Qed.

Lemma bmax_ge {A} (f : A -> nat) t x : In x (to_list t) -> f x <= bmax f t.
Proof.
  induction t as [|y l IHl r IHr]; [intros []|].
  intros H; apply in_to_list_node in H as [->|[H|H]]; cbn [bmax];
    [|specialize (IHl H)|specialize (IHr H)]; lia.
Qed.

Lemma bmax_le {A} (f : A -> nat) t D : (forall x, In x (to_list t) -> f x <= D) -> bmax f t <= D.
Proof.
  induction t as [|y l IHl r IHr]; intros H; cbn [bmax]; [lia|].
  assert (f y <= D) by (apply H, in_to_list_node; auto).
  assert (bmax f l <= D) by (apply IHl; intros x Hx; apply H, in_to_list_node; auto).
  assert (bmax f r <= D) by (apply IHr; intros x Hx; apply H, in_to_list_node; auto).
  lia.
Qed.

(** ** Deciding balance and equality *)

Fixpoint balancedb {A} (t : braun A) : bool :=
  match t with
  | BE => true
  | BN _ l r => Nat.leb (size r) (size l) && Nat.leb (size l) (S (size r))
                && balancedb l && balancedb r
  end.

Lemma balancedb_spec {A} (t : braun A) : balancedb t = true <-> balanced t.
Proof.
  induction t as [|x l IHl r IHr]; cbn; [split; auto|].
  rewrite !Bool.andb_true_iff, !Nat.leb_le, IHl, IHr; tauto.
Qed.

Fixpoint eqb {A} (eqA : A -> A -> bool) (t u : braun A) : bool :=
  match t, u with
  | BE, BE => true
  | BN x l r, BN y l' r' => eqA x y && eqb eqA l l' && eqb eqA r r'
  | _, _ => false
  end.

Lemma eqb_spec {A} (eqA : A -> A -> bool) :
  (forall x y, eqA x y = true <-> x = y) -> forall t u, eqb eqA t u = true <-> t = u.
Proof.
  intros HA t; induction t as [|x l IHl r IHr]; intros [|y l' r']; cbn;
    try (split; [discriminate|intros [=]]); [split; auto|].
  rewrite !Bool.andb_true_iff, HA, IHl, IHr; split; [intros [[-> ->] ->]; reflexivity|].
  intros [= -> -> ->]; auto.
Qed.
