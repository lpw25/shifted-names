(** * Canonical binary tries

    Finite maps over [positive] keys whose representation is canonical: two
    maps with the same bindings are equal ([extensionality]).

    This follows Andrew W. Appel and Xavier Leroy, "Efficient Extensional
    Binary Tries", Journal of Automated Reasoning 67 (2023).  A non-empty
    tree is built from seven constructors that record which of the left
    subtree, the value and the right subtree are present, so empty subtrees
    cannot be represented and no well-formedness invariant is needed.

    Keys are read least-significant bit first: [xO k] is looked up as [k] in
    the left subtree and [xI k] as [k] in the right subtree. *)

From Stdlib Require Import PArith List Lia.
Import ListNotations.

Inductive tree' (A : Type) : Type :=
| Node001 : tree' A -> tree' A
| Node010 : A -> tree' A
| Node011 : A -> tree' A -> tree' A
| Node100 : tree' A -> tree' A
| Node101 : tree' A -> tree' A -> tree' A
| Node110 : tree' A -> A -> tree' A
| Node111 : tree' A -> A -> tree' A -> tree' A.

Arguments Node001 {A} _.
Arguments Node010 {A} _.
Arguments Node011 {A} _ _.
Arguments Node100 {A} _.
Arguments Node101 {A} _ _.
Arguments Node110 {A} _ _.
Arguments Node111 {A} _ _ _.

Inductive tree (A : Type) : Type :=
| Empty : tree A
| Nodes : tree' A -> tree A.

Arguments Empty {A}.
Arguments Nodes {A} _.

Section Trie.

Context {A : Type}.

(** ** Smart constructor and destructors *)

Definition Node (l : tree A) (o : option A) (r : tree A) : tree A :=
  match l, o, r with
  | Empty, None, Empty => Empty
  | Empty, None, Nodes r' => Nodes (Node001 r')
  | Empty, Some x, Empty => Nodes (Node010 x)
  | Empty, Some x, Nodes r' => Nodes (Node011 x r')
  | Nodes l', None, Empty => Nodes (Node100 l')
  | Nodes l', None, Nodes r' => Nodes (Node101 l' r')
  | Nodes l', Some x, Empty => Nodes (Node110 l' x)
  | Nodes l', Some x, Nodes r' => Nodes (Node111 l' x r')
  end.

Definition left (m : tree A) : tree A :=
  match m with
  | Empty => Empty
  | Nodes m' =>
      match m' with
      | Node100 l | Node101 l _ | Node110 l _ | Node111 l _ _ => Nodes l
      | Node001 _ | Node010 _ | Node011 _ _ => Empty
      end
  end.

Definition root (m : tree A) : option A :=
  match m with
  | Empty => None
  | Nodes m' =>
      match m' with
      | Node010 x | Node011 x _ | Node110 _ x | Node111 _ x _ => Some x
      | Node001 _ | Node100 _ | Node101 _ _ => None
      end
  end.

Definition right (m : tree A) : tree A :=
  match m with
  | Empty => Empty
  | Nodes m' =>
      match m' with
      | Node001 r | Node011 _ r | Node101 _ r | Node111 _ _ r => Nodes r
      | Node010 _ | Node100 _ | Node110 _ _ => Empty
      end
  end.

Lemma Node_split (m : tree A) : m = Node (left m) (root m) (right m).
Proof. destruct m as [|m]; [|destruct m]; reflexivity. Qed.

Lemma left_Node l o r : left (Node l o r) = l.
Proof. destruct l, o, r; reflexivity. Qed.

Lemma root_Node l o r : root (Node l o r) = o.
Proof. destruct l, o, r; reflexivity. Qed.

Lemma right_Node l o r : right (Node l o r) = r.
Proof. destruct l, o, r; reflexivity. Qed.

Lemma Node_Empty : Node Empty None Empty = Empty.
Proof. reflexivity. Qed.

(** Induction over trees through the smart constructor. *)
Lemma tree_ind' (P : tree A -> Prop) :
  P Empty ->
  (forall l o r, P l -> P r -> P (Node l o r)) ->
  forall m, P m.
Proof.
  intros HE HN [|m]; [exact HE|].
  induction m.
  - change (P (Node Empty None (Nodes m))); auto.
  - change (P (Node Empty (Some a) Empty)); auto.
  - change (P (Node Empty (Some a) (Nodes m))); auto.
  - change (P (Node (Nodes m) None Empty)); auto.
  - change (P (Node (Nodes m1) None (Nodes m2))); auto.
  - change (P (Node (Nodes m) (Some a) Empty)); auto.
  - change (P (Node (Nodes m1) (Some a) (Nodes m2))); auto.
Qed.

(** ** Lookup *)

Fixpoint get' (i : positive) (m : tree' A) {struct i} : option A :=
  match i, m with
  | xH, (Node001 _ | Node100 _ | Node101 _ _) => None
  | xH, (Node010 x | Node011 x _ | Node110 _ x | Node111 _ x _) => Some x
  | xO _, (Node001 _ | Node010 _ | Node011 _ _) => None
  | xO j, (Node100 l | Node101 l _ | Node110 l _ | Node111 l _ _) => get' j l
  | xI _, (Node010 _ | Node100 _ | Node110 _ _) => None
  | xI j, (Node001 r | Node011 _ r | Node101 _ r | Node111 _ _ r) => get' j r
  end.

Definition get (i : positive) (m : tree A) : option A :=
  match m with
  | Empty => None
  | Nodes m' => get' i m'
  end.

Lemma get_Empty i : get i Empty = None.
Proof. reflexivity. Qed.

Lemma get_Node i l o r :
  get i (Node l o r) =
  match i with
  | xH => o
  | xO j => get j l
  | xI j => get j r
  end.
Proof. destruct l, o, r, i; reflexivity. Qed.

Lemma get_split i m :
  get i m =
  match i with
  | xH => root m
  | xO j => get j (left m)
  | xI j => get j (right m)
  end.
Proof. rewrite (Node_split m) at 1; apply get_Node. Qed.

Lemma get'_not_empty (m : tree' A) : exists i, get' i m <> None.
Proof.
  induction m as [r [i Hi]|x|x r _|l [i Hi]|l [i Hi] r _
                 |l _ x|l _ x r _].
  - exists (xI i); exact Hi.
  - exists xH; discriminate.
  - exists xH; discriminate.
  - exists (xO i); exact Hi.
  - exists (xO i); exact Hi.
  - exists xH; discriminate.
  - exists xH; discriminate.
Qed.

(** ** Extensionality *)

Theorem extensionality (m1 m2 : tree A) :
  (forall i, get i m1 = get i m2) -> m1 = m2.
Proof.
  revert m2.
  induction m1 as [|l1 o1 r1 IHl IHr] using tree_ind'; intros m2 H.
  - destruct m2 as [|m2]; [reflexivity|].
    destruct (get'_not_empty m2) as [i Hi].
    exfalso; apply Hi; symmetry; apply (H i).
  - rewrite (Node_split m2).
    f_equal.
    + apply IHl; intro i.
      specialize (H (xO i)); rewrite get_Node, (get_split (xO i) m2) in H; exact H.
    + specialize (H xH); rewrite get_Node, (get_split xH m2) in H; exact H.
    + apply IHr; intro i.
      specialize (H (xI i)); rewrite get_Node, (get_split (xI i) m2) in H; exact H.
Qed.

(** ** Updates *)

Fixpoint update (i : positive) (f : option A -> option A) (m : tree A)
  {struct i} : tree A :=
  match i with
  | xH => Node (left m) (f (root m)) (right m)
  | xO j => Node (update j f (left m)) (root m) (right m)
  | xI j => Node (left m) (root m) (update j f (right m))
  end.

Lemma get_update k i f m :
  get k (update i f m) =
  if Pos.eqb k i then f (get i m) else get k m.
Proof.
  revert k m; induction i as [i IH|i IH|]; intros k m;
    cbn [update]; rewrite get_Node;
    destruct k as [k|k|]; cbn [Pos.eqb];
    rewrite ?IH, ?(get_split (xI _) m), ?(get_split (xO _) m),
      ?(get_split xH m); try reflexivity.
Qed.

Definition set (i : positive) (x : A) (m : tree A) : tree A :=
  update i (fun _ => Some x) m.

Definition remove (i : positive) (m : tree A) : tree A :=
  update i (fun _ => None) m.

Lemma get_set k i x m :
  get k (set i x m) = if Pos.eqb k i then Some x else get k m.
Proof. apply get_update. Qed.

Lemma get_remove k i m :
  get k (remove i m) = if Pos.eqb k i then None else get k m.
Proof. apply get_update. Qed.

(** ** Elements *)

Fixpoint elements' (kf : positive -> positive) (m : tree' A)
  : list (positive * A) :=
  match m with
  | Node001 r => elements' (fun p => kf (xI p)) r
  | Node010 x => [(kf xH, x)]
  | Node011 x r => (kf xH, x) :: elements' (fun p => kf (xI p)) r
  | Node100 l => elements' (fun p => kf (xO p)) l
  | Node101 l r =>
      elements' (fun p => kf (xO p)) l ++ elements' (fun p => kf (xI p)) r
  | Node110 l x => elements' (fun p => kf (xO p)) l ++ [(kf xH, x)]
  | Node111 l x r =>
      elements' (fun p => kf (xO p)) l
        ++ (kf xH, x) :: elements' (fun p => kf (xI p)) r
  end.

Definition elements (m : tree A) : list (positive * A) :=
  match m with
  | Empty => []
  | Nodes m' => elements' (fun p => p) m'
  end.

Lemma elements'_complete kf m i x :
  get' i m = Some x -> In (kf i, x) (elements' kf m).
Proof.
  revert kf i; induction m as [r IHr|y|y r IHr|l IHl|l IHl r IHr
                              |l IHl y|l IHl y r IHr]; intros kf i H;
    destruct i as [i|i|]; cbn [get'] in H; try discriminate;
    cbn [elements']; rewrite ?in_app_iff; cbn [In];
    try (injection H as <-);
    try pose proof (IHl (fun p => kf (xO p)) _ H);
    try pose proof (IHr (fun p => kf (xI p)) _ H);
    cbn beta in *; intuition.
Qed.

Lemma elements'_sound kf m k x :
  In (k, x) (elements' kf m) -> exists i, k = kf i /\ get' i m = Some x.
Proof.
  revert kf; induction m as [r IHr|y|y r IHr|l IHl|l IHl r IHr
                            |l IHl y|l IHl y r IHr]; intros kf Hin;
    cbn [elements'] in Hin; rewrite ?in_app_iff in Hin; cbn [In] in Hin;
    repeat match goal with
           | H : _ \/ _ |- _ => destruct H
           | H : False |- _ => destruct H
           | H : (_, _) = (_, _) |- _ => injection H as <- <-
           | H : In _ (elements' _ l) |- _ =>
               apply IHl in H; destruct H as [? [-> ?]]
           | H : In _ (elements' _ r) |- _ =>
               apply IHr in H; destruct H as [? [-> ?]]
           end;
    eexists; (split; [reflexivity|cbn [get']; eassumption || reflexivity]).
Qed.

Lemma In_elements' kf m k x :
  In (k, x) (elements' kf m) <-> exists i, k = kf i /\ get' i m = Some x.
Proof.
  split; [apply elements'_sound|].
  intros [i [-> Hi]]; apply elements'_complete, Hi.
Qed.

Lemma In_elements m k x : In (k, x) (elements m) <-> get k m = Some x.
Proof.
  destruct m as [|m]; cbn.
  - split; [intros []|discriminate].
  - rewrite In_elements'; split.
    + intros [i [-> Hi]]; exact Hi.
    + intros Hk; exists k; split; [reflexivity|exact Hk].
Qed.

Lemma in_keys' kf m k :
  In k (map fst (elements' kf m)) -> exists i, k = kf i.
Proof.
  rewrite in_map_iff; intros [[k' x] [<- Hin]].
  apply elements'_sound in Hin as [i [-> _]]; exists i; reflexivity.
Qed.

Lemma elements'_nodup kf m :
  (forall p q, kf p = kf q -> p = q) -> NoDup (map fst (elements' kf m)).
Proof.
  revert kf; induction m as [r IHr|y|y r IHr|l IHl|l IHl r IHr
                            |l IHl y|l IHl y r IHr]; intros kf Hinj.
  all: assert (HO : forall p q, kf (xO p) = kf (xO q) -> p = q)
         by (intros p q H; apply Hinj in H; injection H; auto).
  all: assert (HI : forall p q, kf (xI p) = kf (xI q) -> p = q)
         by (intros p q H; apply Hinj in H; injection H; auto).
  all: cbn [elements']; rewrite ?map_app; cbn [map fst].
  - apply IHr, HI.
  - repeat constructor; intros [].
  - constructor; [|apply IHr, HI].
    intros Hin; apply in_keys' in Hin as [i Hi]; apply Hinj in Hi; discriminate.
  - apply IHl, HO.
  - apply NoDup_app; [apply IHl, HO|apply IHr, HI|].
    intros k Hl Hr; apply in_keys' in Hl as [i ->]; apply in_keys' in Hr as [j Hj].
    apply Hinj in Hj; discriminate.
  - apply NoDup_app; [apply IHl, HO|repeat constructor; intros []|].
    intros k Hl [<-|[]]; apply in_keys' in Hl as [i Hi]; apply Hinj in Hi; discriminate.
  - apply NoDup_app; [apply IHl, HO| |].
    + constructor; [|apply IHr, HI].
      intros Hin; apply in_keys' in Hin as [i Hi]; apply Hinj in Hi; discriminate.
    + intros k Hl [<-|Hr]; apply in_keys' in Hl as [i Hi].
      * apply Hinj in Hi; discriminate.
      * apply in_keys' in Hr as [j Hj]; rewrite Hi in Hj; apply Hinj in Hj; discriminate.
Qed.

Lemma elements_nodup m : NoDup (map fst (elements m)).
Proof.
  destruct m as [|m]; [constructor|apply elements'_nodup; auto].
Qed.

Definition forallb (f : positive -> A -> bool) (m : tree A) : bool :=
  List.forallb (fun kx => f (fst kx) (snd kx)) (elements m).

Lemma forallb_spec f m :
  forallb f m = true <-> (forall k x, get k m = Some x -> f k x = true).
Proof.
  unfold forallb; rewrite List.forallb_forall; split.
  - intros H k x Hk; apply (H (k, x)), In_elements, Hk.
  - intros H [k x] Hin; apply H, In_elements, Hin.
Qed.

Definition fold {B} (f : positive -> A -> B -> B) (m : tree A) (b : B) : B :=
  List.fold_right (fun kx acc => f (fst kx) (snd kx) acc) b (elements m).

End Trie.

(** ** Merging two tries

    [merge f m1 m2] has [f k (get k m1) (get k m2)] at each key [k], provided
    [f k None None = None].  It is linear in the sizes of [m1] and [m2]. *)

Section Merge.

Context {A B C : Type}.
Variable f : positive -> option A -> option B -> option C.

Fixpoint merge_r' (kf : positive -> positive) (m : tree' B) : tree C :=
  let kfO := fun p => kf (xO p) in
  let kfI := fun p => kf (xI p) in
  match m with
  | Node001 r => Node Empty (f (kf xH) None None) (merge_r' kfI r)
  | Node010 y => Node Empty (f (kf xH) None (Some y)) Empty
  | Node011 y r => Node Empty (f (kf xH) None (Some y)) (merge_r' kfI r)
  | Node100 l => Node (merge_r' kfO l) (f (kf xH) None None) Empty
  | Node101 l r => Node (merge_r' kfO l) (f (kf xH) None None) (merge_r' kfI r)
  | Node110 l y => Node (merge_r' kfO l) (f (kf xH) None (Some y)) Empty
  | Node111 l y r =>
      Node (merge_r' kfO l) (f (kf xH) None (Some y)) (merge_r' kfI r)
  end.

Definition merge_r (kf : positive -> positive) (m : tree B) : tree C :=
  match m with
  | Empty => Empty
  | Nodes m' => merge_r' kf m'
  end.

Fixpoint merge' (kf : positive -> positive) (m1 : tree' A) (m2 : tree B)
  : tree C :=
  let kfO := fun p => kf (xO p) in
  let kfI := fun p => kf (xI p) in
  let l2 := left m2 in
  let o2 := root m2 in
  let r2 := right m2 in
  match m1 with
  | Node001 r1 =>
      Node (merge_r kfO l2) (f (kf xH) None o2) (merge' kfI r1 r2)
  | Node010 x =>
      Node (merge_r kfO l2) (f (kf xH) (Some x) o2) (merge_r kfI r2)
  | Node011 x r1 =>
      Node (merge_r kfO l2) (f (kf xH) (Some x) o2) (merge' kfI r1 r2)
  | Node100 l1 =>
      Node (merge' kfO l1 l2) (f (kf xH) None o2) (merge_r kfI r2)
  | Node101 l1 r1 =>
      Node (merge' kfO l1 l2) (f (kf xH) None o2) (merge' kfI r1 r2)
  | Node110 l1 x =>
      Node (merge' kfO l1 l2) (f (kf xH) (Some x) o2) (merge_r kfI r2)
  | Node111 l1 x r1 =>
      Node (merge' kfO l1 l2) (f (kf xH) (Some x) o2) (merge' kfI r1 r2)
  end.

Definition merge (m1 : tree A) (m2 : tree B) : tree C :=
  match m1 with
  | Empty => merge_r (fun p => p) m2
  | Nodes m1' => merge' (fun p => p) m1' m2
  end.

Hypothesis f_None : forall k, f k None None = None.

Lemma get_merge_r kf m i :
  get i (merge_r kf m) = f (kf i) None (get i m).
Proof.
  destruct m as [|m]; cbn [merge_r].
  - rewrite f_None; reflexivity.
  - revert kf i; induction m as [r IHr|y|y r IHr|l IHl|l IHl r IHr
                                |l IHl y|l IHl y r IHr]; intros kf i;
      cbn [merge_r']; rewrite get_Node;
      destruct i as [i|i|]; cbn [get get'];
      rewrite ?IHl, ?IHr, ?get_Empty, ?f_None; reflexivity.
Qed.

Lemma get_merge' kf m1 m2 i :
  get i (merge' kf m1 m2) = f (kf i) (get' i m1) (get i m2).
Proof.
  revert kf m2 i; induction m1 as [r IHr|x|x r IHr|l IHl|l IHl r IHr
                                  |l IHl x|l IHl x r IHr]; intros kf m2 i;
    cbn [merge']; rewrite get_Node, (get_split i m2);
    destruct i as [i|i|]; cbn [get'];
    rewrite ?IHl, ?IHr, ?get_merge_r; reflexivity.
Qed.

Theorem get_merge m1 m2 i :
  get i (merge m1 m2) = f i (get i m1) (get i m2).
Proof.
  destruct m1 as [|m1]; cbn [merge get].
  - apply get_merge_r.
  - apply get_merge'.
Qed.

End Merge.

(** ** Derived operations *)

Definition map_filter {A B} (f : positive -> A -> option B) (m : tree A)
  : tree B :=
  merge (fun k (oa : option A) (_ : option unit) =>
           match oa with Some a => f k a | None => None end)
        m Empty.

Lemma get_map_filter {A B} (f : positive -> A -> option B) m i :
  get i (map_filter f m) =
  match get i m with Some a => f i a | None => None end.
Proof. unfold map_filter; rewrite get_merge; reflexivity. Qed.

(** ** Structural folds

    These are defined by structural recursion on the tree, so that nested
    fixpoints over types stored in tries pass the guard checker. *)

Section Structural.

Context {A : Type}.

Fixpoint tall' (f : A -> bool) (m : tree' A) : bool :=
  match m with
  | Node001 r => tall' f r
  | Node010 x => f x
  | Node011 x r => f x && tall' f r
  | Node100 l => tall' f l
  | Node101 l r => tall' f l && tall' f r
  | Node110 l x => tall' f l && f x
  | Node111 l x r => tall' f l && f x && tall' f r
  end.

Definition tall (f : A -> bool) (m : tree A) : bool :=
  match m with Empty => true | Nodes m' => tall' f m' end.

Lemma tall'_elements f m kf :
  tall' f m = List.forallb (fun kx => f (snd kx)) (elements' kf m).
Proof.
  revert kf; induction m; intro kf; cbn [tall' elements'];
    rewrite ?List.forallb_app; cbn [List.forallb snd];
    rewrite <- ?IHm, <- ?IHm1, <- ?IHm2, ?Bool.andb_true_r, ?Bool.andb_assoc; reflexivity.
Qed.

Lemma tall_spec f m : tall f m = true <-> (forall k x, get k m = Some x -> f x = true).
Proof.
  assert (E : tall f m = forallb (fun _ x => f x) m).
  { unfold forallb; destruct m as [|m]; [reflexivity|]; apply tall'_elements. }
  rewrite E, forallb_spec; reflexivity.
Qed.

Fixpoint tmax' (f : A -> nat) (m : tree' A) : nat :=
  match m with
  | Node001 r => tmax' f r
  | Node010 x => f x
  | Node011 x r => Nat.max (f x) (tmax' f r)
  | Node100 l => tmax' f l
  | Node101 l r => Nat.max (tmax' f l) (tmax' f r)
  | Node110 l x => Nat.max (tmax' f l) (f x)
  | Node111 l x r => Nat.max (Nat.max (tmax' f l) (f x)) (tmax' f r)
  end.

Definition tmax (f : A -> nat) (m : tree A) : nat :=
  match m with Empty => 0 | Nodes m' => tmax' f m' end.

Lemma tmax_ge f m k x : get k m = Some x -> f x <= tmax f m.
Proof.
  destruct m as [|m]; cbn [get tmax]; [discriminate|].
  revert k; induction m; intros [k|k|] Hx; cbn [get' tmax'] in *; try discriminate;
    try (injection Hx as <-); try (specialize (IHm _ Hx)); try (specialize (IHm1 _ Hx));
    try (specialize (IHm2 _ Hx)); lia.
Qed.

End Structural.
