(** * The reflective normaliser

    Goals between adjustments are decided by reflection: both sides are
    reified into [aexp], an expression over label atoms, adjustment atoms,
    payload atoms and term atoms, normalised to a [word], and compared.
    This file has the words, the operations on them that the normaliser
    is built from, and their soundness; the normaliser itself is the
    fold of [Layered].

    ** Normal forms

    A [seg] is a context form with the identity tail: per label, the input
    entries (targets for [h₍₀₎], [h₍₁₎], ...) and the number of output
    entries.  A [word] is a composite

      S₀ ∘ ⇑ᴸ¹σ₁ ∘ S₁ ∘ ⇑ᴸ²σ₂ ∘ ... ∘ Sₙ

    of segments and adjustment atoms [σᵢ], each under a multiset of lifts
    [Lᵢ].  Lifts are pushed onto the atoms, and an input entry in front of
    a composite becomes an input entry of its first segment over a lift of
    the rest:

      push_inner h t (S ∘ X) = push_inner h t S ∘ ⇑ₕX.

    Two adjacent segments are always composed into one.  The segment to
    the right of a lifted atom (applied before it) is settled against its
    lifts in one pass ([settle1]): the inputs it sends to a variable the
    lifts pass around, or to a term, become exactly the variables passed
    around, each label lifted once per such input, and what happens to
    them (renaming, merging, substituting, with the atom composed into a
    term's payload) moves to the segment on the left.  So terms are only
    in the leftmost segment, and [⟦ x | σ ⟧ ∘ ⟦ · \ x ⟧] and
    [⟦ · \ x ⟧ ∘ ⟦ · | σ ⟧] have the same normal form.  See
    [docs/normal-forms.md].

    ** Labels

    Labels in normal forms are expressions: the bound label, a concrete
    label, or a label atom.  The normaliser needs to know how the labels it
    meets are related: it compares two label expressions with [lcmp], which
    knows concrete labels, the bound label (the greatest), and the facts
    [x < y] the tactic found in the context, closed under transitivity.
    When two labels it needs to compare are unrelated, normalisation fails,
    and the tactic reports it.

    Soundness is proved: the normal form denotes the same adjustment as the
    expression.  Uniqueness of normal forms is not proved; normal forms are
    unique by design, and when two expressions normalise differently the
    tactic leaves the goal. *)

From Stdlib Require Import Arith List Lia Bool String.
From ShiftedNames.Core Require Import Label Var Adjustment Laws.
Import ListNotations.

(** ** Label expressions *)

Inductive lexp : Type :=
| LNone
| LCon (s : label)
| LAtom (n : nat).

Definition lexp_eqb (a b : lexp) : bool :=
  match a, b with
  | LNone, LNone => true
  | LCon s, LCon s' => String.eqb s s'
  | LAtom n, LAtom n' => Nat.eqb n n'
  | _, _ => false
  end.

Lemma lexp_eqb_eq a b : lexp_eqb a b = true <-> a = b.
Proof.
  destruct a, b; cbn; split; intro H; try discriminate; try reflexivity.
  - apply String.eqb_eq in H; subst; reflexivity.
  - injection H as ->; apply String.eqb_refl.
  - apply Nat.eqb_eq in H; subst; reflexivity.
  - injection H as ->; apply Nat.eqb_refl.
Qed.

(** Known strict order: the concrete order, the bound label last, and the
    facts [(x, y)] ("[x < y]"), followed transitively; a step of the
    concrete order may come before or after any fact. *)
Definition lt_base (a b : lexp) : bool :=
  match a, b with
  | LCon s, LCon s' => is_less_than_label s s'
  | LNone, _ => false
  | _, LNone => true
  | _, _ => false
  end.

Fixpoint lt_reach (F : list (lexp * lexp)) (fuel : nat) (a b : lexp) : bool :=
  if lt_base a b then true
  else match fuel with
       | 0 => false
       | S f =>
           existsb (fun '(x, y) =>
             if lexp_eqb x a || lt_base a x then (if lexp_eqb y b then true else lt_reach F f y b) else false) F
       end.

(** Written with [if] rather than [&&] and [||], which [vm_compute]
    evaluates eagerly: otherwise every fact would be followed at every
    step, exponentially in the number of facts. *)
Definition lt_list (F : list (lexp * lexp)) (a b : lexp) : bool := lt_reach F (List.length F) a b.

(** The known order as the normaliser uses it: the facts, and what they
    say about each pair of label atoms, worked out once.  Following the
    facts at every comparison is what a normalisation over many label
    variables would otherwise spend its time on. *)
Record order := mk_order { ofacts : list (lexp * lexp); otab : list (list bool) }.

Definition tab_get (tab : list (list bool)) (i j : nat) : option bool :=
  match nth_error tab i with Some row => nth_error row j | None => None end.

Definition lt_known (F : order) (a b : lexp) : bool :=
  match a, b with
  | LAtom i, LAtom j => match tab_get (otab F) i j with Some r => r | None => lt_list (ofacts F) a b end
  | _, _ => lt_list (ofacts F) a b
  end.

(** One more than the label atoms of the facts. *)
Definition asucc (a : lexp) : nat := match a with LAtom n => S n | _ => 0 end.

Fixpoint amax (l : list (lexp * lexp)) : nat :=
  match l with [] => 0 | (x, y) :: r => Nat.max (asucc x) (Nat.max (asucc y) (amax r)) end.

(** The table: what one or two facts say about each pair of label atoms
    (two, for a step between concrete labels), closed under transitivity
    one atom at a time. *)
Fixpoint zipor (a b : list bool) : list bool :=
  match a, b with
  | x :: a', y :: b' => (if x then true else y) :: zipor a' b'
  | _, _ => a
  end.

Definition wstep (tab : list (list bool)) (k : nat) : list (list bool) :=
  match nth_error tab k with
  | Some rk => map (fun ri => match nth_error ri k with Some true => zipor ri rk | _ => ri end) tab
  | None => tab
  end.

Definition order_of (l : list (lexp * lexp)) : order :=
  let n := amax l in
  let t0 := map (fun i => map (fun j => lt_reach l 2 (LAtom i) (LAtom j)) (seq 0 n)) (seq 0 n) in
  mk_order l (fold_left wstep (seq 0 n) t0).

Definition lcmp (F : order) (a b : lexp) : option comparison :=
  if lexp_eqb a b then Some Eq
  else if lt_known F a b then Some Lt
  else if lt_known F b a then Some Gt
  else None.

Section Labels.

Variable lenv : list label.

Definition lden (a : lexp) : option label :=
  match a with
  | LNone => None
  | LCon s => Some s
  | LAtom n => Some (nth n lenv EmptyString)
  end.

Definition lfacts_ok (l : list (lexp * lexp)) : Prop :=
  Forall (fun '(x, y) => olabel_lt (lden x) (lden y)) l.

Definition facts_ok (F : order) : Prop :=
  lfacts_ok (ofacts F)
  /\ forall i j, tab_get (otab F) i j = Some true -> olabel_lt (lden (LAtom i)) (lden (LAtom j)).

Lemma lt_base_sound a b : lt_base a b = true -> olabel_lt (lden a) (lden b).
Proof. destruct a, b; cbn; try discriminate; unfold olabel_lt; cbn; auto. Qed.

Lemma lt_reach_sound l (Hl : lfacts_ok l) fuel : forall a b, lt_reach l fuel a b = true -> olabel_lt (lden a) (lden b).
Proof.
  induction fuel as [|f IH]; intros a b H; cbn [lt_reach] in H;
    (destruct (lt_base a b) eqn:Eb; [apply lt_base_sound, Eb|]); [discriminate|].
  apply existsb_exists in H as [[x y] [Hin H]].
  destruct (lexp_eqb x a || lt_base a x) eqn:Hx; [|discriminate].
  pose proof (proj1 (Forall_forall _ l) Hl _ Hin) as Hxy; cbn in Hxy.
  assert (Hax : lden a = lden x \/ olabel_lt (lden a) (lden x)).
  { apply orb_true_iff in Hx as [Hx|Hx]; [left; apply lexp_eqb_eq in Hx; subst; reflexivity|right; apply lt_base_sound, Hx]. }
  assert (Hyb : olabel_lt (lden y) (lden b) \/ lden y = lden b).
  { destruct (lexp_eqb y b) eqn:Ey; [right; apply lexp_eqb_eq in Ey; subst; reflexivity|left; apply IH, H]. }
  destruct Hax as [Hax|Hax]; destruct Hyb as [Hyb|Hyb].
  - rewrite Hax; exact (olabel_lt_trans _ _ _ Hxy Hyb).
  - rewrite Hax, <- Hyb; exact Hxy.
  - exact (olabel_lt_trans _ _ _ Hax (olabel_lt_trans _ _ _ Hxy Hyb)).
  - rewrite <- Hyb; exact (olabel_lt_trans _ _ _ Hax Hxy).
Qed.

Lemma nth_error_seq0 n i x : nth_error (seq 0 n) i = Some x -> x = i.
Proof.
  intros H; assert (Hi : i < n).
  { rewrite <- (length_seq n 0); apply nth_error_Some; rewrite H; discriminate. }
  apply (nth_error_nth _ _ 0) in H; rewrite seq_nth in H by exact Hi; symmetry; exact H.
Qed.

(** The order worked out from facts that hold. *)
Definition tab_ok (tab : list (list bool)) : Prop :=
  forall i j, tab_get tab i j = Some true -> olabel_lt (lden (LAtom i)) (lden (LAtom j)).

Lemma zipor_nth a : forall b j, nth_error (zipor a b) j = Some true ->
  nth_error a j = Some true \/ nth_error b j = Some true.
Proof.
  induction a as [|x a IH]; intros b j; cbn [zipor]; [auto|].
  destruct b as [|y b]; [auto|]; destruct j as [|j]; cbn [nth_error].
  - destruct x; [auto|intros H; right; exact H].
  - apply IH.
Qed.

Lemma wstep_ok tab k : tab_ok tab -> tab_ok (wstep tab k).
Proof.
  intros H; unfold wstep; destruct (nth_error tab k) as [rk|] eqn:Ek; [|exact H].
  intros i j; unfold tab_get; rewrite nth_error_map.
  destruct (nth_error tab i) as [ri|] eqn:Ei; [|discriminate]; cbn [option_map].
  destruct (nth_error ri k) as [[|]|] eqn:Eik;
    try (intros E; apply (H i j); unfold tab_get; rewrite Ei; exact E).
  intros E; apply zipor_nth in E; destruct E as [E|E].
  - apply (H i j); unfold tab_get; rewrite Ei; exact E.
  - refine (olabel_lt_trans _ (lden (LAtom k)) _ _ _).
    + apply (H i k); unfold tab_get; rewrite Ei; exact Eik.
    + apply (H k j); unfold tab_get; rewrite Ek; exact E.
Qed.

Lemma order_of_ok l : lfacts_ok l -> facts_ok (order_of l).
Proof.
  intros Hl; split; [exact Hl|]; unfold order_of; cbn [otab].
  set (t0 := map _ _).
  assert (H0 : tab_ok t0).
  { intros i j; unfold t0, tab_get.
    rewrite nth_error_map; destruct (nth_error (seq 0 (amax l)) i) as [i'|] eqn:Ei; [|discriminate]; cbn [option_map].
    rewrite nth_error_map; destruct (nth_error (seq 0 (amax l)) j) as [j'|] eqn:Ej; [|discriminate]; cbn [option_map].
    apply nth_error_seq0 in Ei, Ej; subst; intros H.
    exact (lt_reach_sound l Hl 2 _ _ (f_equal (fun o => match o with Some b => b | None => false end) H)). }
  clearbody t0; revert t0 H0; generalize (seq 0 (amax l)) as ks.
  induction ks as [|k ks IH]; intros t0 H0; [exact H0|]; cbn [fold_left]; apply IH, wstep_ok, H0.
Qed.

Variable F : order.
Hypothesis HF : facts_ok F.

Lemma lt_known_sound a b : lt_known F a b = true -> olabel_lt (lden a) (lden b).
Proof.
  assert (Hl : forall a b, lt_list (ofacts F) a b = true -> olabel_lt (lden a) (lden b))
    by (intros x y; apply (lt_reach_sound _ (proj1 HF))).
  unfold lt_known; destruct a as [|s|i]; try apply Hl; destruct b as [|s|j]; try apply Hl.
  destruct (tab_get (otab F) i j) as [[|]|] eqn:E; [intros _; exact (proj2 HF i j E)|discriminate|apply Hl].
Qed.

(** What a comparison tells about the labels. *)
Definition cmp_holds (c : comparison) (a b : lexp) : Prop :=
  match c with
  | Eq => a = b
  | Lt => olabel_lt (lden a) (lden b)
  | Gt => olabel_lt (lden b) (lden a)
  end.

Lemma lcmp_sound a b c : lcmp F a b = Some c -> cmp_holds c a b.
Proof.
  unfold lcmp; destruct (lexp_eqb a b) eqn:E.
  - intros H; injection H as <-; apply lexp_eqb_eq, E.
  - destruct (lt_known F a b) eqn:L1; [intros H; injection H as <-; apply lt_known_sound, L1|].
    destruct (lt_known F b a) eqn:L2; [intros H; injection H as <-; apply lt_known_sound, L2|discriminate].
Qed.

Lemma lcmp_neq a b c : lcmp F a b = Some c -> c <> Eq -> lden a <> lden b.
Proof.
  intros H Hc; apply lcmp_sound in H; destruct c; cbn in H; [contradiction| |];
    intros E; rewrite E in H; exact (olabel_lt_irrefl _ H).
Qed.

End Labels.

(** [iter n f x] applies [f] [n] times. *)
Fixpoint iter {A} (n : nat) (f : A -> A) (x : A) : A :=
  match n with 0 => x | S n => f (iter n f x) end.

Lemma iter_add {A} n m (f : A -> A) x : iter (n + m) f x = iter n f (iter m f x).
Proof. induction n; cbn; congruence. Qed.

(** ** Normal forms *)

(** A target ([NBind u w b] is the payload [(u, w ∘ b)], with [b] the
    identity payload adjustment or a payload atom); the targets of one
    label; a segment, one entry per label with its targets and its number
    of outputs; a word. *)
Inductive ntgt : Type :=
| NVar (h : lexp) (i : nat)
| NBind (u : nat) (w : word) (b : option nat)
with tlist : Type :=
| TNil
| TCons (t : ntgt) (r : tlist)
with seg : Type :=
| SNil
| SEnt (h : lexp) (ts : tlist) (m : nat) (r : seg)
with word : Type :=
| WEnd (s : seg)
| WAtom (s : seg) (L : list (lexp * nat)) (a : nat) (w : word)
| WLay (s : seg) (w : word).

Scheme ntgt_mind := Induction for ntgt Sort Prop
with tlist_mind := Induction for tlist Sort Prop
with seg_mind := Induction for seg Sort Prop
with word_mind := Induction for word Sort Prop.
Combined Scheme nf_mind from ntgt_mind, tlist_mind, seg_mind, word_mind.

(** Induction along the spine of a segment or a target list. *)
Lemma seg_spine (P : seg -> Prop) :
  P SNil -> (forall h ts m r, P r -> P (SEnt h ts m r)) -> forall s, P s.
Proof. intros H0 HS; fix IH 1; intros [|h ts m r]; [exact H0|apply HS, IH]. Qed.

Lemma word_spine (P : word -> Prop) :
  (forall s, P (WEnd s)) -> (forall s L a w, P w -> P (WAtom s L a w)) -> (forall s w, P w -> P (WLay s w)) -> forall w, P w.
Proof. intros H0 HS HL; fix IH 1; intros [s|s L a w|s w]; [apply H0|apply HS, IH|apply HL, IH]. Qed.

Lemma tlist_spine (P : tlist -> Prop) :
  P TNil -> (forall t r, P r -> P (TCons t r)) -> forall ts, P ts.
Proof. intros H0 HS; fix IH 1; intros [|t r]; [exact H0|apply HS, IH]. Qed.

Fixpoint tl_list (ts : tlist) : list ntgt :=
  match ts with TNil => [] | TCons t r => t :: tl_list r end.

Fixpoint tl_of (l : list ntgt) : tlist :=
  match l with [] => TNil | t :: r => TCons t (tl_of r) end.

Lemma tl_list_of l : tl_list (tl_of l) = l.
Proof. induction l; cbn; congruence. Qed.

Fixpoint stargets (s : seg) : list ntgt :=
  match s with SNil => [] | SEnt _ ts _ r => tl_list ts ++ stargets r end.

Lemma tl_of_list ts : tl_of (tl_list ts) = ts.
Proof. induction ts; cbn; congruence. Qed.

(** *** Decidable equality

    With the lazy conjunction: a comparison stops at the first
    difference, also under [vm_compute], which evaluates the arguments
    of [&&] before calling it. *)

Local Open Scope lazy_bool_scope.

Lemma landb_true_iff (a b : bool) : a &&& b = true <-> a = true /\ b = true.
Proof. destruct a, b; cbn; tauto. Qed.

Fixpoint lifts_eqb (L L' : list (lexp * nat)) : bool :=
  match L, L' with
  | [], [] => true
  | (h, n) :: L, (h', n') :: L' => lexp_eqb h h' &&& Nat.eqb n n' &&& lifts_eqb L L'
  | _, _ => false
  end.

Lemma lifts_eqb_eq L L' : lifts_eqb L L' = true -> L = L'.
Proof.
  revert L'; induction L as [|[h n] L IH]; intros [|[h' n'] L']; cbn; try discriminate; [reflexivity|].
  intros H; apply landb_true_iff in H as [H H3]; apply landb_true_iff in H as [H1 H2].
  apply lexp_eqb_eq in H1; apply Nat.eqb_eq in H2; subst; f_equal; apply IH, H3.
Qed.

Fixpoint ntgt_eqb (t1 t2 : ntgt) : bool :=
  match t1, t2 with
  | NVar h i, NVar h' i' => lexp_eqb h h' &&& Nat.eqb i i'
  | NBind u w b, NBind u' w' b' =>
      Nat.eqb u u' &&& word_eqb w w'
      &&& match b, b' with None, None => true | Some n, Some n' => Nat.eqb n n' | _, _ => false end
  | _, _ => false
  end
with tlist_eqb (ts1 ts2 : tlist) : bool :=
  match ts1, ts2 with
  | TNil, TNil => true
  | TCons t r, TCons t' r' => ntgt_eqb t t' &&& tlist_eqb r r'
  | _, _ => false
  end
with seg_eqb (s1 s2 : seg) : bool :=
  match s1, s2 with
  | SNil, SNil => true
  | SEnt h ts m r, SEnt h' ts' m' r' => lexp_eqb h h' &&& tlist_eqb ts ts' &&& Nat.eqb m m' &&& seg_eqb r r'
  | _, _ => false
  end
with word_eqb (w1 w2 : word) : bool :=
  match w1, w2 with
  | WEnd s, WEnd s' => seg_eqb s s'
  | WAtom s L a w, WAtom s' L' a' w' =>
      seg_eqb s s'
      &&& lifts_eqb L L'
      &&& Nat.eqb a a' &&& word_eqb w w'
  | WLay s w, WLay s' w' => seg_eqb s s' &&& word_eqb w w'
  | _, _ => false
  end.

Lemma nf_eqb_eq :
  (forall t t', ntgt_eqb t t' = true -> t = t')
  /\ (forall ts ts', tlist_eqb ts ts' = true -> ts = ts')
  /\ (forall s s', seg_eqb s s' = true -> s = s')
  /\ (forall w w', word_eqb w w' = true -> w = w').
Proof.
  apply nf_mind.
  - intros h i [h' i'|] H; cbn in H; [|discriminate].
    apply landb_true_iff in H as [H1 H2]; apply lexp_eqb_eq in H1; apply Nat.eqb_eq in H2; subst; reflexivity.
  - intros u w IH b [|u' w' b'] H; cbn in H; [discriminate|].
    apply landb_true_iff in H as [H H3]; apply landb_true_iff in H as [H1 H2].
    apply Nat.eqb_eq in H1; apply IH in H2; subst.
    destruct b as [n|], b' as [n'|]; try discriminate; [apply Nat.eqb_eq in H3; subst|]; reflexivity.
  - intros [|]; cbn; congruence.
  - intros t IHt r IHr [|t' r'] H; cbn in H; [discriminate|].
    apply landb_true_iff in H as [H1 H2]; f_equal; [apply IHt, H1|apply IHr, H2].
  - intros [|]; cbn; congruence.
  - intros h ts IHts m r IHr [|h' ts' m' r'] H; cbn in H; [discriminate|].
    apply landb_true_iff in H as [H H4]; apply landb_true_iff in H as [H H3]; apply landb_true_iff in H as [H1 H2].
    apply lexp_eqb_eq in H1; apply Nat.eqb_eq in H3; subst; f_equal; [apply IHts, H2|apply IHr, H4].
  - intros s IH [s'| |] H; cbn in H; [f_equal; apply IH, H|discriminate|discriminate].
  - intros s IHs L a w IHw [|s' L' a' w'|] H; cbn in H; [discriminate| |discriminate].
    apply landb_true_iff in H as [H H4]; apply landb_true_iff in H as [H H3]; apply landb_true_iff in H as [H1 H2].
    apply Nat.eqb_eq in H3; subst; f_equal; [apply IHs, H1|apply lifts_eqb_eq, H2|apply IHw, H4].
  - intros s IHs w IHw [| |s' w'] H; cbn in H; try discriminate.
    apply landb_true_iff in H as [H1 H2]; f_equal; [apply IHs, H1|apply IHw, H2].
Qed.

Local Close Scope lazy_bool_scope.

(** ** Denotation *)

Section Denote.

Context {T : Type}.
Variable lenv : list label.
Variable tenv : list T.
Variable aenv : list (radj T).
Variable penv : list (rpadj T).

Local Notation lden := (lden lenv).

Definition aden (n : nat) : radj T := nth n aenv ridentity.
Definition bden (b : option nat) : rpadj T := match b with None => rpidentity | Some n => nth n penv rpidentity end.

Definition lifts (L : list (lexp * nat)) (x : radj T) : radj T :=
  fold_right (fun '(h, n) acc => iter n (rlift (lden h)) acc) x L.

Fixpoint souts (s : seg) (tail : radj T) : radj T :=
  match s with
  | SNil => tail
  | SEnt h _ m r => iter m (rpush_outer (lden h)) (souts r tail)
  end.

Fixpoint tden (t : ntgt) : rtarget T :=
  match t with
  | NVar h i => RRename (mk_rvar (lden h) i)
  | NBind u w b =>
      match nth_error tenv u with
      | Some x => RBind x (rpcompose (wden w) (bden b))
      | None => RRename (mk_rvar None 0)
      end
  end
with tins (h : option label) (ts : tlist) (tail : radj T) : radj T :=
  match ts with
  | TNil => tail
  | TCons t r => rpush_inner h (tden t) (tins h r tail)
  end
with sins (s : seg) (tail : radj T) : radj T :=
  match s with
  | SNil => tail
  | SEnt h ts _ r => tins (lden h) ts (sins r tail)
  end
with wden (w : word) : radj T :=
  match w with
  | WEnd s => sins s (souts s ridentity)
  | WAtom s L a w => rcompose (sins s (souts s ridentity)) (rcompose (lifts L (aden a)) (wden w))
  | WLay s w => rcompose (sins s (souts s ridentity)) (wden w)
  end.

Definition sden (s : seg) : radj T := sins s (souts s ridentity).

Lemma wden_end s : wden (WEnd s) = sden s.
Proof. reflexivity. Qed.

Lemma wden_atom s L a w : wden (WAtom s L a w) = rcompose (sden s) (rcompose (lifts L (aden a)) (wden w)).
Proof. reflexivity. Qed.

Lemma wden_lay s w : wden (WLay s w) = rcompose (sden s) (wden w).
Proof. reflexivity. Qed.

(** *** What a segment does *)

(** The entry of label [l]: the first one, and the only one when the
    labels are distinct. *)
Fixpoint sget (l : option label) (s : seg) : option (tlist * nat) :=
  match s with
  | SNil => None
  | SEnt h ts m r => if label_eqb (lden h) l then Some (ts, m) else sget l r
  end.

Fixpoint sdist (s : seg) : Prop :=
  match s with
  | SNil => True
  | SEnt h _ _ r => sget (lden h) r = None /\ sdist r
  end.

(** Every segment of a word, payload words included, has distinct labels.
    The normaliser's operations keep this, so they need not check it. *)
Fixpoint tdist (t : ntgt) : Prop :=
  match t with NVar _ _ => True | NBind _ w _ => wdist w end
with tldist (ts : tlist) : Prop :=
  match ts with TNil => True | TCons t r => tdist t /\ tldist r end
with sdistd (s : seg) : Prop :=
  match s with SNil => True | SEnt h ts _ r => sget (lden h) r = None /\ tldist ts /\ sdistd r end
with wdist (w : word) : Prop :=
  match w with WEnd s => sdistd s | WAtom s _ _ w => sdistd s /\ wdist w | WLay s w => sdistd s /\ wdist w end.

Fixpoint tlen (ts : tlist) : nat := match ts with TNil => 0 | TCons _ r => S (tlen r) end.

Fixpoint tnth (ts : tlist) (j : nat) : ntgt :=
  match ts, j with
  | TNil, _ => NVar LNone 0
  | TCons t _, 0 => t
  | TCons _ r, S j => tnth r j
  end.

(** What the [j]-th variable of label [l] goes to, given the entry. *)
Definition esem (l : option label) (e : option (tlist * nat)) (j : nat) : rresult T :=
  match e with
  | Some (ts, m) => if j <? tlen ts then rtarget_result (tden (tnth ts j)) else inl (mk_rvar l (j - tlen ts + m))
  | None => inl (mk_rvar l j)
  end.

Fixpoint scount (l : option label) (s : seg) : nat :=
  match s with
  | SNil => 0
  | SEnt h _ m r => (if label_eqb (lden h) l then m else 0) + scount l r
  end.

Lemma rapply_iter_outer h m (a : radj T) v :
  rapply (iter m (rpush_outer h) a) v
  = match rapply a v with
    | inl w => inl (iter m (shift_rvar (mk_rvar h 0)) w)
    | inr (u, ρ) => inr (u, iter m (rpshift h) ρ)
    end.
Proof.
  induction m as [|m IH]; cbn [iter]; [destruct (rapply a v) as [|[]]; reflexivity|].
  rewrite rapply_push_outer, IH; destruct (rapply a v) as [|[]]; reflexivity.
Qed.

Lemma iter_shift_rvar h m l j :
  iter m (shift_rvar (mk_rvar h 0)) (mk_rvar l j) = mk_rvar l (j + if label_eqb h l then m else 0).
Proof.
  induction m as [|m IH]; cbn [iter]; [destruct (label_eqb h l); f_equal; lia|].
  rewrite IH; unfold shift_rvar; cbn [v_label v_index].
  destruct (label_eqb h l); cbn; f_equal; lia.
Qed.

Lemma rapply_souts s l j : rapply (souts s ridentity) (mk_rvar l j) = inl (mk_rvar l (j + scount l s)).
Proof.
  induction s as [|h ts m r IH] using seg_spine; cbn [souts scount].
  - rewrite rapply_identity; f_equal; f_equal; lia.
  - rewrite rapply_iter_outer, IH, iter_shift_rvar; f_equal; f_equal.
    rewrite (label_eqb_sym (lden h) l); destruct (label_eqb l (lden h)); lia.
Qed.

Lemma rapply_tins h ts tail l j :
  rapply (tins h ts tail) (mk_rvar l j)
  = if label_eqb h l && (j <? tlen ts) then rtarget_result (tden (tnth ts j))
    else rapply tail (mk_rvar l (if label_eqb h l then j - tlen ts else j)).
Proof.
  revert j; induction ts as [|t r IH] using tlist_spine; intros j; cbn [tins tlen tnth].
  - destruct (label_eqb h l); cbn [andb]; [rewrite Nat.sub_0_r|]; reflexivity.
  - rewrite rapply_push_inner; unfold rvar_eqb, unshift_rvar; cbn [v_label v_index].
    rewrite (label_eqb_sym l h); destruct (label_eqb h l) eqn:E; cbn [andb].
    + destruct j as [|j]; [reflexivity|].
      replace (Nat.eqb (S j) 0) with false by reflexivity; replace (0 <? S j) with true by reflexivity.
      replace (S j <? S (tlen r)) with (j <? tlen r) by reflexivity.
      cbn [andb]; rewrite IH; cbn [andb]; replace (S j - 1) with j by lia.
      destruct (j <? tlen r); [reflexivity|]; repeat f_equal; lia.
    + rewrite IH; reflexivity.
Qed.

Lemma scount_get l s : sdist s -> scount l s = match sget l s with Some (_, m) => m | None => 0 end.
Proof.
  induction s as [|h ts m r IH] using seg_spine; cbn [scount sget sdist]; [reflexivity|]; intros [Hn Hd].
  destruct (label_eqb_spec (lden h) l) as [<-|Hne]; rewrite IH by exact Hd; [rewrite Hn; lia|lia].
Qed.

Lemma rapply_sins s tail l j :
  sdist s ->
  rapply (sins s tail) (mk_rvar l j)
  = match sget l s with
    | Some (ts, _) => if j <? tlen ts then rtarget_result (tden (tnth ts j)) else rapply tail (mk_rvar l (j - tlen ts))
    | None => rapply tail (mk_rvar l j)
    end.
Proof.
  revert j; induction s as [|h ts m r IH] using seg_spine; intros j; cbn [sins sget sdist]; [reflexivity|]; intros [Hn Hd].
  rewrite rapply_tins; destruct (label_eqb_spec (lden h) l) as [<-|Hne]; cbn [andb].
  - destruct (j <? tlen ts); [reflexivity|]; rewrite IH, Hn by exact Hd; reflexivity.
  - apply IH, Hd.
Qed.

Theorem rapply_sden s v : sdist s -> rapply (sden s) v = esem (v_label v) (sget (v_label v) s) (v_index v).
Proof.
  intros Hd; destruct v as [l j]; unfold sden; cbn [v_label v_index].
  rewrite rapply_sins by exact Hd.
  unfold esem; destruct (sget l s) as [[ts m]|] eqn:E.
  - destruct (j <? tlen ts) eqn:Ej; [reflexivity|].
    rewrite rapply_souts, scount_get, E by exact Hd; reflexivity.
  - rewrite rapply_souts, scount_get, E by exact Hd; f_equal; f_equal; lia.
Qed.

End Denote.

(** ** Operations on normal forms

    Every operation compares labels with [lcmp], and fails ([None]) when a
    comparison it needs is unknown.  [ntm] is the number of term atoms. *)

Section Ops.

Variable F : order.
Variable ntm : nat.

(** *** Segments *)

(** The entry of [h], when [h]'s relation to the labels before it is
    known. *)
Fixpoint sfind (h : lexp) (s : seg) : option (option (tlist * nat)) :=
  match s with
  | SNil => Some None
  | SEnt h' ts m r =>
      match lcmp F h h' with
      | None => None
      | Some Eq => Some (Some (ts, m))
      | Some _ => sfind h r
      end
  end.

Definition ofe (e : option (tlist * nat)) : tlist * nat :=
  match e with Some p => p | None => (TNil, 0) end.

(** Removing the entry of [h]. *)
Fixpoint sdel (h : lexp) (s : seg) : option seg :=
  match s with
  | SNil => Some SNil
  | SEnt h' ts m r =>
      match lcmp F h h' with
      | None => None
      | Some Eq => sdel h r
      | Some _ => match sdel h r with Some r' => Some (SEnt h' ts m r') | None => None end
      end
  end.

(** Adding an entry for a label that has none, in order. *)
Fixpoint sput (h : lexp) (ts : tlist) (m : nat) (s : seg) : seg :=
  match s with
  | SNil => SEnt h ts m SNil
  | SEnt h' ts' m' r =>
      match lcmp F h h' with
      | Some Lt => SEnt h ts m s
      | _ => SEnt h' ts' m' (sput h ts m r)
      end
  end.

(** Dropping transparent entries: a last target [h₍ₘ₋₁₎] with [m] outputs
    is the same as no target and [m - 1] outputs.  The targets are given
    last first. *)
Fixpoint trim (h : lexp) (rts : list ntgt) (m : nat) : list ntgt * nat :=
  match rts, m with
  | NVar h' j :: r, S m' => if lexp_eqb h' h && Nat.eqb j m' then trim h r m' else (rts, m)
  | _, _ => (rts, m)
  end.

(** Setting the entry of [h]. *)
Definition sset (h : lexp) (ts : tlist) (m : nat) (s : seg) : option seg :=
  match sdel h s with
  | None => None
  | Some s' =>
      match trim h (rev_append (tl_list ts) []) m with
      | ([], 0) => Some s'
      | (rts, m') => Some (sput h (tl_of (rev_append rts [])) m' s')
      end
  end.

Lemma sset_unfold h ts m s :
  sset h ts m s
  = match sdel h s with
    | None => None
    | Some s' =>
        match trim h (rev (tl_list ts)) m with
        | ([], 0) => Some s'
        | (rts, m') => Some (sput h (tl_of (rev rts)) m' s')
        end
    end.
Proof.
  unfold sset; rewrite <- rev_alt; destruct (sdel h s); [|reflexivity].
  destruct (trim h (rev (tl_list ts)) m) as [[|x r] [|m']]; rewrite <- ?rev_alt; reflexivity.
Qed.

Fixpoint tcat (a b : tlist) : tlist :=
  match a with TNil => b | TCons t r => TCons t (tcat r b) end.

Fixpoint tskip (n : nat) (ts : tlist) : tlist :=
  match n, ts with
  | 0, _ => ts
  | S n, TCons _ r => tskip n r
  | S _, TNil => TNil
  end.

(** Payload adjustments over the identity payload only matter on named
    variables: the bound entry of their last segment goes. *)
Fixpoint sdrop_none (s : seg) : seg :=
  match s with
  | SNil => SNil
  | SEnt LNone _ _ r => sdrop_none r
  | SEnt h ts m r => SEnt h ts m (sdrop_none r)
  end.

Fixpoint pnorm (w : word) : word :=
  match w with
  | WEnd s => WEnd (sdrop_none s)
  | WAtom s L a w => WAtom s L a (pnorm w)
  | WLay s w => WLay s (pnorm w)
  end.

Definition bnorm (b : option nat) (w : word) : word :=
  match b with None => pnorm w | Some _ => w end.

(** *** Composing with a segment on the left *)

(** The entry of the label of the last variable looked up, with the
    place reached in its list of targets: a run of variables of one
    label in increasing order is one pass over that list. *)
Definition cursor : Type := (lexp * option (nat * nat * list ntgt * nat * list ntgt))%type.

Definition cload (S : seg) (h : lexp) : option cursor :=
  match sfind h S with
  | None => None
  | Some None => Some (h, None)
  | Some (Some (tsS, mS)) => Some (h, Some (tlen tsS, mS, tl_list tsS, 0, tl_list tsS))
  end.

Section Comp.

Variable S : seg.

Fixpoint tapp (t : ntgt) : option ntgt :=
  match t with
  | NVar h i =>
      match sfind h S with
      | None => None
      | Some None => Some (NVar h i)
      | Some (Some (ts, m)) => Some (if i <? tlen ts then tnth ts i else NVar h (i - tlen ts + m))
      end
  | NBind u w b =>
      if u <? ntm then match wapp w with Some w' => Some (NBind u (bnorm b w') b) | None => None end
      else None
  end
with tlapp (ts : tlist) : option tlist :=
  match ts with
  | TNil => Some TNil
  | TCons t r => match tapp t, tlapp r with Some t', Some r' => Some (TCons t' r') | _, _ => None end
  end
with tlappc (c : option cursor) (ts : tlist) {struct ts} : option tlist :=
  match ts with
  | TNil => Some TNil
  | TCons (NVar h i) r =>
      match (match c with
             | Some (hc, e) => if lexp_eqb hc h then Some (h, e) else cload S h
             | None => cload S h
             end) with
      | None => None
      | Some (_, None) =>
          match tlappc (Some (h, None)) r with Some r' => Some (TCons (NVar h i) r') | None => None end
      | Some (_, Some (n, mS, full, pos, suf)) =>
          if i <? n then
            let suf' := if pos <=? i then skipn (i - pos) suf else skipn i full in
            match tlappc (Some (h, Some (n, mS, full, i, suf'))) r with
            | Some r' => Some (TCons (hd (NVar LNone 0) suf') r')
            | None => None
            end
          else match tlappc (Some (h, Some (n, mS, full, pos, suf))) r with
               | Some r' => Some (TCons (NVar h (i - n + mS)) r')
               | None => None
               end
      end
  | TCons t r =>
      match tapp t, tlappc c r with Some t', Some r' => Some (TCons t' r') | _, _ => None end
  end
with sgo (U : seg) : option seg :=
  match U with
  | SNil => Some S
  | SEnt h ts m r =>
      match sgo r, tlappc None ts, sfind h S with
      | Some R, Some ts', Some e =>
          let '(tsS, mS) := ofe e in
          sset h (tcat ts' (tskip m tsS)) (if tlen tsS <=? m then m - tlen tsS + mS else mS) R
      | _, _, _ => None
      end
  end
with wapp (w : word) : option word :=
  match w with
  | WEnd U => match sgo U with Some U' => Some (WEnd U') | None => None end
  | WAtom U L a w => match sgo U with Some U' => Some (WAtom U' L a w) | None => None end
  | WLay _ _ => None
  end.

End Comp.

(** [scomp S U] is [S ∘ U]; [wcons S w] is [S ∘ w]. *)
Definition scomp (S U : seg) : option seg :=
  sgo S U.

Definition wcons (S : seg) (w : word) : option word :=
  wapp S w.

(** *** Lifts *)

(** Adding [n] lifts by [h]. *)
Fixpoint ladd (h : lexp) (n : nat) (L : list (lexp * nat)) : option (list (lexp * nat)) :=
  match L with
  | [] => Some [(h, n)]
  | (h', n') :: L' =>
      match lcmp F h h' with
      | None => None
      | Some Eq => Some ((h', n' + n) :: L')
      | Some Lt => Some ((h, n) :: L)
      | Some Gt => match ladd h n L' with Some L'' => Some ((h', n') :: L'') | None => None end
      end
  end.

(** The number of lifts by [h]. *)
Fixpoint lcount (h : lexp) (L : list (lexp * nat)) : nat :=
  match L with
  | [] => 0
  | (h', n') :: L' => if lexp_eqb h h' then n' else lcount h L'
  end.

(** The number of lifts by labels equal to [h], when [h]'s relation to
    every label of [L] is known. *)
Fixpoint lcnt (h : lexp) (L : list (lexp * nat)) : option nat :=
  match L with
  | [] => Some 0
  | (h', n') :: L' =>
      match lcmp F h h', lcnt h L' with
      | Some Eq, Some c => Some (n' + c)
      | Some _, Some c => Some c
      | _, _ => None
      end
  end.

Definition shseg (h : lexp) (k : nat) : seg := SEnt h TNil k SNil.

Definition sfront (h : lexp) (t : ntgt) (s : seg) : option seg :=
  match sfind h s with
  | Some e => let '(ts, m) := ofe e in sset h (TCons t ts) m s
  | None => None
  end.

Definition slift (h : lexp) (s : seg) : option seg :=
  match scomp (shseg h 1) s with Some s' => sfront h (NVar h 0) s' | None => None end.

Definition whead (w : word) : seg := match w with WEnd s | WAtom s _ _ _ | WLay s _ => s end.

Definition wsethead (w : word) (s : seg) : word :=
  match w with WEnd _ => WEnd s | WAtom _ L a w => WAtom s L a w | WLay _ w => WLay s w end.

(** *** Settling in one pass

    [A ∘ ⇑ᴸσ ∘ U] (with [U] applied first) is rewritten to
    [(A ∘ Q) ∘ ⇑ᴸ'σ ∘ U'], computed directly from [U]'s entries.  For each
    label [g]: the inputs [g₍ᵢ₎] that [U] sends to a variable the lifts
    pass around, or to a term, are [P g]; [L'] lifts [g] once for each;
    [U'] sends the [j]-th of them to [g₍ⱼ₎] and re-indexes every other
    target from [L] to [L']; and [Q] sends [g₍ⱼ₎] to the original target
    of the [j]-th of them (a term with [⇑ᴸσ] composed into its payload),
    and has [L]'s number of lifts by [g] as its outputs. *)

Fixpoint lsum (h : lexp) (L : list (lexp * nat)) : nat :=
  match L with [] => 0 | (h', n) :: L => (if lexp_eqb h h' then n else 0) + lsum h L end.

(** A set of label expressions whose relations are all known. *)
Fixpoint lins (h : lexp) (hs : list lexp) : option (list lexp) :=
  match hs with
  | [] => Some [h]
  | h' :: r =>
      match lcmp F h h' with
      | None => None
      | Some Eq => Some hs
      | Some _ => match lins h r with Some r' => Some (h' :: r') | None => None end
      end
  end.

Fixpoint linss (hs acc : list lexp) : option (list lexp) :=
  match hs with
  | [] => Some acc
  | h :: hs => match lins h acc with Some acc' => linss hs acc' | None => None end
  end.

Fixpoint seg_labels (s : seg) : list lexp :=
  match s with
  | SNil => []
  | SEnt h ts _ r =>
      h :: flat_map (fun t => match t with NVar h' _ => [h'] | NBind _ _ _ => [] end) (tl_list ts) ++ seg_labels r
  end.

Section One.

Variable L : list (lexp * nat).
Variable U : seg.

Definition entd (g : lexp) : list ntgt * nat :=
  match sfind g U with Some (Some (ts, m)) => (tl_list ts, m) | _ => ([], 0) end.

Definition otg (g : lexp) (i : nat) : ntgt :=
  let '(xs, m) := entd g in
  if i <? List.length xs then nth i xs (NVar LNone 0) else NVar g (i - List.length xs + m).

Definition inP (t : ntgt) : bool :=
  match t with NVar h j => j <? lsum h L | NBind _ _ _ => true end.

Definition orng (g : lexp) : nat :=
  let '(xs, m) := entd g in Nat.max (List.length xs) (List.length xs + lsum g L - m).

Definition oP (g : lexp) : list nat := filter (fun i => inP (otg g i)) (seq 0 (orng g)).

Definition olp (g : lexp) : nat := List.length (oP g).

Definition opos (g : lexp) (i : nat) : nat := List.length (filter (fun p => p <? i) (oP g)).

Definition oreidx (t : ntgt) : ntgt :=
  match t with NVar h j => NVar h (j - lsum h L + olp h) | t => t end.

Definition u'ent (g : lexp) : lexp * (list ntgt * nat) :=
  let '(xs, m) := entd g in
  (g, (map (fun i => let t := otg g i in if inP t then NVar g (opos g i) else oreidx t) (seq 0 (orng g)),
       orng g - List.length xs + m - lsum g L + olp g)).

End One.

Fixpoint sbuild (es : list (lexp * (list ntgt * nat))) : option seg :=
  match es with
  | [] => Some SNil
  | (h, (xs, m)) :: es => match sbuild es with Some s => sset h (tl_of xs) m s | None => None end
  end.

Fixpoint omap {A B} (f : A -> option B) (xs : list A) : option (list B) :=
  match xs with
  | [] => Some []
  | x :: xs => match f x, omap f xs with Some y, Some ys => Some (y :: ys) | _, _ => None end
  end.

Fixpoint lbuild (es : list (lexp * nat)) : option (list (lexp * nat)) :=
  match es with
  | [] => Some []
  | (h, n) :: es => match lbuild es with Some L => if Nat.eqb n 0 then Some L else ladd h n L | None => None end
  end.

Section OneTq.

Variable wc : word -> word -> option word.
Variable pn : option nat -> word -> option word.
Variable a : nat.

(** A target moved past [⇑ᴸσ]: a term gets it composed into its payload. *)
Definition otq (L : list (lexp * nat)) (t : ntgt) : option ntgt :=
  match t with
  | NVar _ _ => Some t
  | NBind u w b =>
      if u <? ntm then
        match wc (WAtom SNil L a (WEnd SNil)) w with
        | Some w' => match pn b w' with Some w'' => Some (NBind u w'' b) | None => None end
        | None => None
        end
      else None
  end.

Definition qent (L : list (lexp * nat)) (U : seg) (g : lexp) : option (lexp * (list ntgt * nat)) :=
  match omap (fun i => otq L (otg U g i)) (oP L U g) with
  | Some ts => Some (g, (ts, lsum g L))
  | None => None
  end.

Definition settle1 (A : seg) (L : list (lexp * nat)) (U : seg) : option (seg * list (lexp * nat) * seg) :=
  match linss (map fst L ++ seg_labels U) [] with
  | None => None
  | Some hs =>
      match omap (qent L U) hs, sbuild (map (u'ent L U) hs), lbuild (map (fun g => (g, olp L U g)) hs) with
      | Some qs, Some U', Some L' =>
          match sbuild qs with
          | Some Q => match scomp A Q with Some A' => Some (A', L', U') | None => None end
          | None => None
          end
      | _, _, _ => None
      end
  end.

End OneTq.

(** [S ∘ ⇑ᴸσ ∘ w], settled; payloads composed by [wc]. *)

Definition settle (wc : word -> word -> option word) (pn : option nat -> word -> option word)
  (A : seg) (L : list (lexp * nat)) (a : nat) (w : word) : option word :=
  match settle1 wc pn a A L (whead w) with
  | Some (A', L', U') => Some (WAtom A' L' a (wsethead w U'))
  | None => None
  end.

(** Payload words are applied to named variables only.  Their last atom is
    settled with the last segment's bound inputs sent past it, so that no
    lift by [·] is kept that only named inputs could reach, and the
    earlier atoms are settled again. *)
Definition pfinal (L : list (lexp * nat)) (s : seg) : option seg :=
  sset LNone TNil (lcount LNone L) s.

Fixpoint pnormf (wc : word -> word -> option word) (pn : option nat -> word -> option word) (w : word) : option word :=
  match w with
  | WEnd s => Some (WEnd (sdrop_none s))
  | WAtom A L a w' =>
      match w' with
      | WEnd s => match pfinal L s with Some s' => settle wc pn A L a (WEnd s') | None => None end
      | _ => match pnormf wc pn w' with Some w'' => settle wc pn A L a w'' | None => None end
      end
  | WLay _ _ => None
  end.

Definition bnormf (wc : word -> word -> option word) (pn : option nat -> word -> option word)
  (b : option nat) (w : word) : option word :=
  match b with None => pnormf wc pn w | Some _ => Some w end.

(** *** The constructors on normal forms *)

Fixpoint wcomp_with (wc : word -> word -> option word) (pn : option nat -> word -> option word) (w1 w2 : word) : option word :=
  match w1 with
  | WEnd A => wcons A w2
  | WAtom A L a w => match wcomp_with wc pn w w2 with Some w' => settle wc pn A L a w' | None => None end
  | WLay _ _ => None
  end.

(** Composition, and normalising payload words; [n] bounds the depth of
    recursion into payloads. *)
Fixpoint wops (n : nat) : (word -> word -> option word) * (option nat -> word -> option word) :=
  match n with
  | 0 => (fun _ _ => None, fun _ _ => None)
  | S n' =>
      let '(wc, pn) := wops n' in (wcomp_with wc pn, bnormf wc pn)
  end.

Definition wcomp (w1 w2 : word) : option word := fst (wops 64) w1 w2.
Definition pnormw (b : option nat) (w : word) : option word := snd (wops 64) b w.

Fixpoint wlift (h : lexp) (w : word) : option word :=
  match w with
  | WEnd s => match slift h s with Some s' => Some (WEnd s') | None => None end
  | WAtom s L a w =>
      match slift h s, ladd h 1 L, wlift h w with
      | Some s', Some L', Some w' => Some (WAtom s' L' a w')
      | _, _, _ => None
      end
  | WLay _ _ => None
  end.

(** [push_inner h t (S ∘ X) = push_inner h t S ∘ ⇑ₕX]. *)
Definition wpush (h : lexp) (t : ntgt) (w : word) : option word :=
  match w with
  | WEnd s => match sfront h t s with Some s' => Some (WEnd s') | None => None end
  | WAtom s L a w =>
      match sfront h t s, ladd h 1 L, wlift h w with
      | Some s', Some L', Some w' => Some (WAtom s' L' a w')
      | _, _, _ => None
      end
  | WLay _ _ => None
  end.

Definition wouter (h : lexp) (w : word) : option word := wcons (shseg h 1) w.

End Ops.

(** ** Expressions *)

Inductive aexp : Type :=
| AId
| AAtom (n : nat)
| ACompose (a b : aexp)
| AOuter (h : lexp) (a : aexp)
| AInner (h : lexp) (t : texp) (a : aexp)
| ALift (h : lexp) (a : aexp)
with texp : Type :=
| TVarE (h : lexp) (i : nat)
| TBindE (u : nat) (p : pexp)
| TShiftE (h : lexp) (t : texp)
with pexp : Type :=
| PId
| PAtom (n : nat)
| PComp (a : aexp) (p : pexp)
| PShift (h : lexp) (p : pexp).

(** ** Soundness *)

Section Sound.

Context {T : Type}.
Variable lenv : list label.
Variable tenv : list T.
Variable aenv : list (radj T).
Variable penv : list (rpadj T).
Variable F : order.
Hypothesis HF : facts_ok lenv F.
Variable ntm : nat.
Hypothesis Hntm : ntm <= List.length tenv.

Local Notation lden := (lden lenv).
Local Notation tden := (tden lenv tenv aenv penv).
Local Notation sden := (sden lenv tenv aenv penv).
Local Notation wden := (wden lenv tenv aenv penv).
Local Notation sget := (sget lenv).
Local Notation sdist := (sdist lenv).
Local Notation tdist := (tdist lenv).
Local Notation tldist := (tldist lenv).
Local Notation sdistd := (sdistd lenv).
Local Notation wdist := (wdist lenv).
Local Notation esem := (esem lenv tenv aenv penv).
Local Notation lifts := (lifts lenv).
Local Notation aden := (aden aenv).
Local Notation bden := (bden penv).
Local Notation souts := (@souts T lenv).
Local Notation tins := (tins lenv tenv aenv penv).
Local Notation sins := (sins lenv tenv aenv penv).

(** *** Segments *)

Lemma tldist_iff ts : tldist ts <-> forall t, In t (tl_list ts) -> tdist t.
Proof.
  induction ts as [|t r IH] using tlist_spine; cbn [tldist tl_list]; [split; [intros _ t []|intros _; exact I]|].
  rewrite IH; split; [intros [Ht Hr] t' [<-|H]; [exact Ht|apply Hr, H]|].
  intros H; split; [apply H; left; reflexivity|intros t' Ht'; apply H; right; exact Ht'].
Qed.

Lemma sdistd_iff s : sdistd s <-> sdist s /\ forall t, In t (stargets s) -> tdist t.
Proof.
  induction s as [|h ts m r IH] using seg_spine; cbn [sdistd sdist stargets]; [split; [intros _; split; [exact I|intros t []]|intros _; exact I]|].
  rewrite IH, tldist_iff; split.
  - intros [Hn [Ht [Hd Hr]]]; split; [split; assumption|]; intros t Hin; apply in_app_or in Hin as [Hin|Hin]; [apply Ht|apply Hr]; exact Hin.
  - intros [[Hn Hd] H]; split; [exact Hn|split; [intros t Ht; apply H, in_or_app; left; exact Ht|split; [exact Hd|]]].
    intros t Ht; apply H, in_or_app; right; exact Ht.
Qed.

Lemma sdistd_sdist s : sdistd s -> sdist s.
Proof. intros H; exact (proj1 (proj1 (sdistd_iff s) H)). Qed.

Lemma sget_stargets l s ts m : sget l s = Some (ts, m) -> forall t, In t (tl_list ts) -> In t (stargets s).
Proof.
  induction s as [|h ts' m' r IH] using seg_spine; cbn [sget stargets]; [discriminate|].
  destruct (label_eqb (lden h) l); [intros E; injection E as <- <-; intros t Ht; apply in_or_app; left; exact Ht|].
  intros E t Ht; apply in_or_app; right; exact (IH E t Ht).
Qed.

Lemma sget_dd l s ts m : sdistd s -> sget l s = Some (ts, m) -> tldist ts.
Proof.
  intros Hd E; apply (proj2 (tldist_iff ts)); intros t Ht; exact (proj2 (proj1 (sdistd_iff s) Hd) t (sget_stargets _ _ _ _ E _ Ht)).
Qed.

Lemma sfind_sound h s e : sfind F h s = Some e -> e = sget (lden h) s.
Proof.
  induction s as [|h' ts m r IH] using seg_spine; cbn; [congruence|].
  destruct (lcmp F h h') as [c|] eqn:E; [|discriminate].
  destruct c.
  - apply (lcmp_sound lenv F HF) in E; cbn in E; subst h'; rewrite label_eqb_refl; congruence.
  - intros H; rewrite (proj2 (label_eqb_neq _ _)); [apply IH, H|].
    intros Heq; apply (lcmp_neq lenv F HF h h' Lt E); [discriminate|congruence].
  - intros H; rewrite (proj2 (label_eqb_neq _ _)); [apply IH, H|].
    intros Heq; apply (lcmp_neq lenv F HF h h' Gt E); [discriminate|congruence].
Qed.

Lemma sdel_sound h s s' :
  sdel F h s = Some s' -> forall l, sget l s' = if label_eqb (lden h) l then None else sget l s.
Proof.
  revert s'; induction s as [|h' ts m r IH] using seg_spine; cbn; intros s'.
  - intros H; injection H as <-; intros l; destruct (label_eqb _ _); reflexivity.
  - destruct (lcmp F h h') as [c|] eqn:E; [|discriminate].
    assert (Hc := E); apply (lcmp_sound lenv F HF) in Hc.
    destruct c; cbn in Hc.
    + subst h'; intros H l; rewrite (IH _ H); destruct (label_eqb (lden h) l); reflexivity.
    + destruct (sdel F h r) as [r'|] eqn:Er; [|discriminate]; intros H; injection H as <-; intros l; cbn.
      rewrite (IH _ eq_refl).
      destruct (label_eqb_spec (lden h') l) as [<-|]; destruct (label_eqb_spec (lden h) (lden h')) as [Heq|];
        try reflexivity; rewrite Heq in Hc; exfalso; exact (olabel_lt_irrefl _ Hc).
    + destruct (sdel F h r) as [r'|] eqn:Er; [|discriminate]; intros H; injection H as <-; intros l; cbn.
      rewrite (IH _ eq_refl).
      destruct (label_eqb_spec (lden h') l) as [<-|]; destruct (label_eqb_spec (lden h) (lden h')) as [Heq|];
        try reflexivity; rewrite Heq in Hc; exfalso; exact (olabel_lt_irrefl _ Hc).
Qed.

Lemma sdel_dist h s s' : sdist s -> sdel F h s = Some s' -> sdist s'.
Proof.
  revert s'; induction s as [|h' ts m r IH] using seg_spine; cbn; intros s' Hd.
  - intros H; injection H as <-; exact I.
  - destruct Hd as [Hn Hd]; destruct (lcmp F h h') as [[]|] eqn:E; try discriminate; [apply IH, Hd| |];
      destruct (sdel F h r) as [r'|] eqn:Er; try discriminate; intros H; injection H as <-; cbn;
      (split; [rewrite (sdel_sound h r r' Er), Hn; destruct (label_eqb _ _); reflexivity|apply (IH _ Hd eq_refl)]).
Qed.

Lemma sput_sound h ts m s :
  sget (lden h) s = None ->
  (forall l, sget l (sput F h ts m s) = if label_eqb (lden h) l then Some (ts, m) else sget l s)
  /\ (sdist s -> sdist (sput F h ts m s)).
Proof.
  induction s as [|h' ts' m' r IH] using seg_spine; cbn [sput sget sdist]; intros Hn.
  - split; [intros l; cbn; destruct (label_eqb _ _); reflexivity|intros _; cbn; split; [reflexivity|exact I]].
  - destruct (label_eqb (lden h') (lden h)) eqn:Ehh; [discriminate|].
    destruct (lcmp F h h') as [[]|]; cbn [sget sdist];
      try (split; [intros l; destruct (label_eqb _ _); reflexivity|intros Hd; split; [rewrite Ehh; exact Hn|exact Hd]]);
      (destruct (IH Hn) as [IH1 IH2]; split;
       [intros l; rewrite IH1; destruct (label_eqb_spec (lden h') l) as [<-|]; [|reflexivity];
        rewrite label_eqb_sym, Ehh; reflexivity
       |intros [Hn' Hd]; split; [rewrite IH1, label_eqb_sym, Ehh; exact Hn'|apply IH2, Hd]]).
Qed.

(** Target lists as lists. *)
Lemma tlen_list ts : tlen ts = List.length (tl_list ts).
Proof. induction ts using tlist_spine; cbn; congruence. Qed.

Lemma tnth_list ts j : tnth ts j = nth j (tl_list ts) (NVar LNone 0).
Proof. revert j; induction ts as [|t r IH] using tlist_spine; intros [|j]; cbn; auto. Qed.

Definition lsem (l : option label) (xs : list ntgt) (m j : nat) : rresult T :=
  if j <? List.length xs then rtarget_result (tden (nth j xs (NVar LNone 0))) else inl (mk_rvar l (j - List.length xs + m)).

Lemma esem_lsem l ts m j : esem l (Some (ts, m)) j = lsem l (tl_list ts) m j.
Proof. unfold esem, lsem; rewrite tlen_list, tnth_list; reflexivity. Qed.

Lemma trim_sound h rx m ry m' :
  trim h rx m = (ry, m') -> forall j, lsem (lden h) (rev rx) m j = lsem (lden h) (rev ry) m' j.
Proof.
  revert m; induction rx as [|x rx IH]; intros m; cbn [trim].
  - intros H; injection H as <- <-; reflexivity.
  - destruct x as [h' j0|u w b]; [|intros H; injection H as <- <-; reflexivity].
    destruct m as [|m]; [intros H; injection H as <- <-; reflexivity|].
    destruct (lexp_eqb h' h && Nat.eqb j0 m) eqn:E; [|intros H; injection H as <- <-; reflexivity].
    apply andb_true_iff in E as [E1 E2]; apply lexp_eqb_eq in E1; apply Nat.eqb_eq in E2; subst h' j0.
    intros H j; rewrite <- (IH _ H j); unfold lsem; cbn [rev]; rewrite length_app; cbn [Datatypes.length].
    destruct (Nat.ltb_spec j (List.length (rev rx))) as [Hj|Hj];
      destruct (Nat.ltb_spec j (List.length (rev rx) + 1)) as [Hj'|Hj'].
    + rewrite app_nth1 by exact Hj; reflexivity.
    + lia.
    + assert (j = List.length (rev rx)) as -> by lia.
      rewrite nth_middle; cbn; f_equal; f_equal; lia.
    + f_equal; f_equal; lia.
Qed.

Lemma esem_none l j : esem l None j = esem l (Some (TNil, 0)) j.
Proof. cbn; f_equal; f_equal; lia. Qed.

Lemma esem_ofe l e j : esem l (Some (ofe e)) j = esem l e j.
Proof. destruct e as [[ts m]|]; [reflexivity|symmetry; apply esem_none]. Qed.

Lemma sset_sound h ts m s s' :
  sdist s -> sset F h ts m s = Some s' ->
  sdist s'
  /\ forall l j, esem l (sget l s') j
                 = if label_eqb (lden h) l then esem l (Some (ts, m)) j else esem l (sget l s) j.
Proof.
  rewrite sset_unfold; intros Hd; destruct (sdel F h s) as [s0|] eqn:Ed; [|discriminate].
  pose proof (sdel_sound h s s0 Ed) as Hs0; pose proof (sdel_dist h s s0 Hd Ed) as Hd0.
  assert (Hn : sget (lden h) s0 = None) by (rewrite Hs0, label_eqb_refl; reflexivity).
  destruct (trim h (rev (tl_list ts)) m) as [rts m'] eqn:Et.
  assert (Hsem : forall j, esem (lden h) (Some (ts, m)) j = esem (lden h) (Some (tl_of (rev rts), m')) j).
  { intros j; rewrite !esem_lsem, tl_list_of; rewrite <- (rev_involutive (tl_list ts)) at 1.
    apply (trim_sound h _ _ _ _ Et). }
  assert (Hput : forall s'', s'' = sput F h (tl_of (rev rts)) m' s0 -> sdist s''
            /\ forall l j, esem l (sget l s'') j
                           = if label_eqb (lden h) l then esem l (Some (ts, m)) j else esem l (sget l s) j).
  { intros s'' ->; destruct (sput_sound h (tl_of (rev rts)) m' s0 Hn) as [H1 H2]; split; [apply H2, Hd0|].
    intros l j; rewrite H1, Hs0; destruct (label_eqb_spec (lden h) l) as [<-|]; [|reflexivity].
    symmetry; apply Hsem. }
  destruct rts as [|x rts]; [destruct m' as [|m']|];
    intros H; injection H as <-; try (apply Hput; reflexivity).
  split; [exact Hd0|]; intros l j; rewrite Hs0; destruct (label_eqb_spec (lden h) l) as [<-|]; [|reflexivity].
  rewrite Hsem, esem_none; reflexivity.
Qed.

Lemma sdel_tgts h s s' : sdel F h s = Some s' -> forall t, In t (stargets s') -> In t (stargets s).
Proof.
  revert s'; induction s as [|h' ts m r IH] using seg_spine; intros s'; cbn [sdel].
  - intros H; injection H as <-; intros t [].
  - destruct (lcmp F h h') as [[]|]; try discriminate; cbn [stargets].
    + intros H t Ht; apply in_or_app; right; exact (IH _ H t Ht).
    + destruct (sdel F h r) as [r'|] eqn:Er; [|discriminate]; intros H; injection H as <-; cbn [stargets].
      intros t Ht; apply in_app_or in Ht as [Ht|Ht]; apply in_or_app; [left; exact Ht|right; exact (IH _ eq_refl t Ht)].
    + destruct (sdel F h r) as [r'|] eqn:Er; [|discriminate]; intros H; injection H as <-; cbn [stargets].
      intros t Ht; apply in_app_or in Ht as [Ht|Ht]; apply in_or_app; [left; exact Ht|right; exact (IH _ eq_refl t Ht)].
Qed.

Lemma sput_tgts h ts m s t : In t (stargets (sput F h ts m s)) -> In t (tl_list ts) \/ In t (stargets s).
Proof.
  induction s as [|h' ts' m' r IH] using seg_spine; cbn [sput stargets].
  - rewrite app_nil_r; left; assumption.
  - destruct (lcmp F h h') as [[]|]; cbn [stargets]; try (intros Ht; apply in_app_or in Ht; exact Ht);
      intros Ht; apply in_app_or in Ht as [Ht|Ht];
      try (right; apply in_or_app; left; exact Ht);
      (destruct (IH Ht) as [H|H]; [left; exact H|right; apply in_or_app; right; exact H]).
Qed.

Lemma trim_tgts h rts m : forall rts' m', trim h rts m = (rts', m') -> forall t, In t rts' -> In t rts.
Proof.
  revert m; induction rts as [|x r IH]; intros m rts' m' E; cbn [trim] in E.
  - injection E as <- <-; intros t [].
  - destruct x as [h' j|u w b]; [destruct m as [|m0]|];
      try (injection E as <- <-; intros t Ht; exact Ht).
    destruct (lexp_eqb h' h && Nat.eqb j m0); [|injection E as <- <-; intros t Ht; exact Ht].
    intros t Ht; right; exact (IH _ _ _ E t Ht).
Qed.

Lemma sset_tgts h ts m s s' : sset F h ts m s = Some s' ->
  forall t, In t (stargets s') -> In t (stargets s) \/ In t (tl_list ts).
Proof.
  rewrite sset_unfold; destruct (sdel F h s) as [s0|] eqn:Ed; [|discriminate].
  destruct (trim h (rev (tl_list ts)) m) as [rts m'] eqn:Et.
  assert (Hput : forall t, In t (stargets (sput F h (tl_of (rev rts)) m' s0)) -> In t (stargets s) \/ In t (tl_list ts)).
  { intros t Ht; destruct (sput_tgts _ _ _ _ _ Ht) as [H|H].
    - right; rewrite tl_list_of, <- in_rev in H; apply (trim_tgts _ _ _ _ _ Et) in H; rewrite <- in_rev in H; exact H.
    - left; exact (sdel_tgts _ _ _ Ed _ H). }
  destruct rts as [|x rts]; [destruct m' as [|m']|]; intros H; injection H as <-; try exact Hput.
  intros t Ht; left; exact (sdel_tgts _ _ _ Ed _ Ht).
Qed.

Lemma sset_dd h ts m s s' : sdistd s -> tldist ts -> sset F h ts m s = Some s' -> sdistd s'.
Proof.
  intros Hd Ht E; apply (proj2 (sdistd_iff s')); split; [exact (proj1 (sset_sound _ _ _ _ _ (sdistd_sdist _ Hd) E))|].
  intros t Hin; destruct (sset_tgts _ _ _ _ _ E t Hin) as [H|H].
  - exact (proj2 (proj1 (sdistd_iff s) Hd) t H).
  - exact (proj1 (tldist_iff ts) Ht t H).
Qed.

(** *** Composition with a segment *)

Definition cres (a : radj T) (r : rresult T) : rresult T :=
  match r with inl w => rapply a w | inr (u, ρ) => inr (u, rpcompose a ρ) end.

Lemma rapply_compose_cres (a b : radj T) v : rapply (rcompose a b) v = cres a (rapply b v).
Proof. rewrite rapply_compose; reflexivity. Qed.

Lemma tcat_list a b : tl_list (tcat a b) = tl_list a ++ tl_list b.
Proof. induction a as [|t r IH] using tlist_spine; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma tskip_list_in n ts t : In t (tl_list (tskip n ts)) -> In t (tl_list ts).
Proof.
  revert ts; induction n as [|n IH]; intros [|t0 r] H; cbn [tskip] in H; try exact H.
  cbn [tl_list In]; right; apply (IH r), H.
Qed.

Lemma tlen_tcat a b : tlen (tcat a b) = tlen a + tlen b.
Proof. induction a using tlist_spine; cbn; congruence. Qed.

Lemma tnth_tcat a b j : tnth (tcat a b) j = if j <? tlen a then tnth a j else tnth b (j - tlen a).
Proof.
  revert j; induction a as [|t r IH] using tlist_spine; intros j; cbn [tcat tlen tnth].
  - rewrite Nat.sub_0_r; reflexivity.
  - destruct j as [|j]; [reflexivity|]; cbn [tnth]; rewrite IH; reflexivity.
Qed.

Lemma tlen_tskip n ts : tlen (tskip n ts) = tlen ts - n.
Proof. revert ts; induction n as [|n IH]; intros [|t r]; cbn; auto; lia. Qed.

Lemma tnth_tskip n ts j : tnth (tskip n ts) j = tnth ts (n + j).
Proof. revert ts; induction n as [|n IH]; intros [|t r]; cbn; auto; destruct j; reflexivity. Qed.

(** The identity payload adjustment acts on named variables only. *)
Lemma rpapply_identity v : v_label v <> None -> rpapply (@rpidentity T) v = inl v.
Proof. intros Hv; destruct v as [[x|] i]; [|contradiction]; unfold rpapply; cbn; reflexivity. Qed.

Lemma rpcompose_named (a b : radj T) :
  (forall v, v_label v <> None -> rapply a v = rapply b v) -> rpcompose a rpidentity = rpcompose b rpidentity.
Proof.
  intros H; apply rpextensionality; intros v Hv.
  rewrite !rpapply_pcompose, rpapply_identity by exact Hv; apply H, Hv.
Qed.

Definition named_eq (a b : radj T) : Prop := forall v, v_label v <> None -> rapply a v = rapply b v.

Lemma named_tins h ts X X' : named_eq X X' -> named_eq (tins h ts X) (tins h ts X').
Proof.
  intros H [l j] Hl; rewrite !rapply_tins; destruct (label_eqb h l && _); [reflexivity|].
  apply H; exact Hl.
Qed.

Lemma named_tins_none ts X : named_eq (tins None ts X) X.
Proof.
  intros [l j] Hl; rewrite rapply_tins; cbn [v_label] in Hl.
  destruct l; [|contradiction]; reflexivity.
Qed.

Lemma named_sdrop_none s : named_eq (sden s) (sden (sdrop_none s)).
Proof.
  unfold sden.
  assert (Ho : named_eq (souts s ridentity) (souts (sdrop_none s) ridentity)).
  { intros [l j] Hl; rewrite !rapply_souts; do 3 f_equal; cbn [v_label] in Hl.
    induction s as [|h ts m r IH] using seg_spine; [reflexivity|].
    destruct h; cbn [sdrop_none scount]; rewrite IH; [destruct l; [reflexivity|contradiction]|reflexivity|reflexivity]. }
  generalize (souts s ridentity) (souts (sdrop_none s) ridentity) Ho; clear Ho; intros X X' Ho.
  induction s as [|h ts m r IH] using seg_spine; [exact Ho|].
  destruct h; cbn [sdrop_none sins]; try (apply named_tins, IH).
  intros v Hv; rewrite (named_tins_none ts _ v Hv); apply IH, Hv.
Qed.

Lemma named_pnorm w : named_eq (wden w) (wden (pnorm w)).
Proof.
  induction w as [s|s L a w IH|s w IH] using word_spine; cbn [pnorm].
  - apply named_sdrop_none.
  - intros v Hv; rewrite !wden_atom, !rapply_compose_cres, IH by exact Hv; reflexivity.
  - intros v Hv; rewrite !wden_lay, !rapply_compose_cres, IH by exact Hv; reflexivity.
Qed.

Lemma bnorm_sound b w : rpcompose (wden (bnorm b w)) (bden b) = rpcompose (wden w) (bden b).
Proof.
  destruct b as [n|]; [reflexivity|]; cbn [bnorm bden].
  symmetry; apply rpcompose_named, named_pnorm.
Qed.

Lemma sget_drop l s : sget l (sdrop_none s) = match l with None => None | Some _ => sget l s end.
Proof.
  induction s as [|h ts m r IH] using seg_spine; [destruct l; reflexivity|].
  destruct h as [|x|n]; cbn [sdrop_none sget lden]; rewrite IH; [destruct l; reflexivity| |];
    destruct l; cbn [label_eqb]; reflexivity.
Qed.

Lemma sdrop_dd s : sdistd s -> sdistd (sdrop_none s).
Proof.
  induction s as [|h ts m r IH] using seg_spine; [intros _; exact I|]; intros [Hn [Ht Hd]].
  destruct h as [|x|n]; cbn [sdrop_none]; [apply IH, Hd| |];
    (split; [rewrite sget_drop; exact Hn|split; [exact Ht|apply IH, Hd]]).
Qed.

Lemma pnorm_dd w : wdist w -> wdist (pnorm w).
Proof.
  induction w as [s|s L a w IH|s w IH] using word_spine; cbn [pnorm wdist]; [apply sdrop_dd| |];
    intros [Hs Hw]; split; [exact Hs|apply IH, Hw|exact Hs|apply IH, Hw].
Qed.

Lemma bnorm_dd b w : wdist w -> wdist (bnorm b w).
Proof. destruct b; [exact (fun H => H)|apply pnorm_dd]. Qed.

(** Unfolding the composition functions. *)
Lemma tapp_var S h i :
  tapp F ntm S (NVar h i)
  = match sfind F h S with
    | None => None
    | Some None => Some (NVar h i)
    | Some (Some (ts, m)) => Some (if i <? tlen ts then tnth ts i else NVar h (i - tlen ts + m))
    end.
Proof. reflexivity. Qed.

Lemma tapp_bind S u w b :
  tapp F ntm S (NBind u w b)
  = if u <? ntm then match wapp F ntm S w with Some w' => Some (NBind u (bnorm b w') b) | None => None end
    else None.
Proof. reflexivity. Qed.

Lemma tlapp_cons S t r :
  tlapp F ntm S (TCons t r)
  = match tapp F ntm S t, tlapp F ntm S r with Some t', Some r' => Some (TCons t' r') | _, _ => None end.
Proof. reflexivity. Qed.

Lemma hd_skipn_nth (l : list ntgt) i d : hd d (skipn i l) = nth i l d.
Proof. revert l; induction i as [|i IH]; intros [|x r]; cbn; auto. Qed.

Lemma tnth_nth ts : forall j, tnth ts j = nth j (tl_list ts) (NVar LNone 0).
Proof. induction ts as [|t r IH] using tlist_spine; intros [|j]; cbn; auto. Qed.

Definition cinv (S : seg) (c : option cursor) : Prop :=
  match c with
  | None => True
  | Some (hc, None) => sfind F hc S = Some None
  | Some (hc, Some (n, mS, full, pos, suf)) =>
      exists tsS, sfind F hc S = Some (Some (tsS, mS)) /\ n = tlen tsS /\ full = tl_list tsS /\ suf = skipn pos full
  end.

Lemma tlappc_eq S ts : forall c, cinv S c -> tlappc F ntm S c ts = tlapp F ntm S ts.
Proof using.
  induction ts as [|t r IH] using tlist_spine; intros c Hc; [reflexivity|].
  rewrite tlapp_cons; destruct t as [h i|u w b].
  - cbn [tlappc]; rewrite tapp_var.
    assert (Hl : exists c', (match c with
                             | Some (hc, e) => if lexp_eqb hc h then Some (h, e) else cload F S h
                             | None => cload F S h
                             end) = c' /\ match c' with Some (h', _) => h' = h /\ cinv S c' | None => sfind F h S = None end).
    { assert (Hload : match cload F S h with Some (h', _) => h' = h /\ cinv S (cload F S h) | None => sfind F h S = None end).
      { unfold cload; destruct (sfind F h S) as [[[tsS mS]|]|] eqn:E; [|split; [reflexivity|exact E]|reflexivity].
        split; [reflexivity|]; exists tsS; repeat split; exact E. }
      destruct c as [[hc e]|]; [|eexists; split; [reflexivity|]; destruct (cload F S h) as [[h' e']|]; exact Hload].
      destruct (lexp_eqb hc h) eqn:Eh; [|eexists; split; [reflexivity|]; destruct (cload F S h) as [[h' e']|]; exact Hload].
      apply lexp_eqb_eq in Eh; subst hc; eexists; split; [reflexivity|]; split; [reflexivity|exact Hc]. }
    destruct Hl as [c' [-> Hc']]; destruct c' as [[h' e]|]; [|rewrite Hc'; reflexivity].
    destruct Hc' as [-> Hc']; destruct e as [[[[[n mS] full] pos] suf]|]; cbn [cinv] in Hc'.
    + destruct Hc' as [tsS [Ef [-> [-> ->]]]]; rewrite Ef.
      destruct (i <? tlen tsS) eqn:Ei.
      * rewrite IH by (exists tsS; repeat split; [exact Ef|destruct (pos <=? i) eqn:Ep; [apply Nat.leb_le in Ep; rewrite skipn_skipn, Nat.sub_add by exact Ep; reflexivity|reflexivity]]).
        assert (Eh : hd (NVar LNone 0) (if pos <=? i then skipn (i - pos) (skipn pos (tl_list tsS)) else skipn i (tl_list tsS)) = tnth tsS i).
        { rewrite tnth_nth, <- hd_skipn_nth; destruct (pos <=? i) eqn:Ep; [|reflexivity].
          apply Nat.leb_le in Ep; rewrite skipn_skipn, Nat.sub_add by exact Ep; reflexivity. }
        rewrite Eh; destruct (tlapp F ntm S r); reflexivity.
      * rewrite IH by (exists tsS; repeat split; exact Ef); destruct (tlapp F ntm S r); reflexivity.
    + rewrite Hc', IH by exact Hc'; destruct (tlapp F ntm S r); reflexivity.
  - cbn [tlappc]; rewrite IH by exact Hc; reflexivity.
Qed.

Lemma sgo_ent S h ts m r :
  sgo F ntm S (SEnt h ts m r)
  = match sgo F ntm S r, tlapp F ntm S ts, sfind F h S with
    | Some R, Some ts', Some e =>
        let '(tsS, mS) := ofe e in
        sset F h (tcat ts' (tskip m tsS)) (if tlen tsS <=? m then m - tlen tsS + mS else mS) R
    | _, _, _ => None
    end.
Proof using. rewrite <- (tlappc_eq S ts None I); reflexivity. Qed.

Lemma wapp_end S U :
  wapp F ntm S (WEnd U) = match sgo F ntm S U with Some U' => Some (WEnd U') | None => None end.
Proof. reflexivity. Qed.

Lemma wapp_atom S U L a w :
  wapp F ntm S (WAtom U L a w)
  = match sgo F ntm S U with Some U' => Some (WAtom U' L a w) | None => None end.
Proof. reflexivity. Qed.

Lemma wapp_lay S U w : wapp F ntm S (WLay U w) = None.
Proof. reflexivity. Qed.

Section CompSound.

Variable S : seg.
Hypothesis HS : sdistd S.

Lemma comp_sound :
  (forall t t', tdist t -> tapp F ntm S t = Some t' ->
     tdist t' /\ rtarget_result (tden t') = cres (sden S) (rtarget_result (tden t)))
  /\ (forall ts ts', tldist ts -> tlapp F ntm S ts = Some ts' ->
        tldist ts' /\ tlen ts' = tlen ts
        /\ forall j, j < tlen ts -> rtarget_result (tden (tnth ts' j)) = cres (sden S) (rtarget_result (tden (tnth ts j))))
  /\ (forall U, sdistd U -> forall R, sgo F ntm S U = Some R ->
        sdistd R /\ forall l j, esem l (sget l R) j = cres (sden S) (esem l (sget l U) j))
  /\ (forall w w', wdist w -> wapp F ntm S w = Some w' -> wdist w' /\ wden w' = rcompose (sden S) (wden w)).
Proof.
  pose proof (sdistd_sdist _ HS) as HS'.
  apply nf_mind.
  - (* NVar *)
    intros h i t' _; rewrite tapp_var; destruct (sfind F h S) as [e|] eqn:E; [|discriminate].
    apply sfind_sound in E; subst e; cbn [tden rtarget_result cres].
    rewrite rapply_sden by exact HS'; cbn [v_label v_index].
    destruct (sget (lden h) S) as [[ts m]|] eqn:Eg; intros H; injection H as <-; cbn [esem]; [|split; [exact I|reflexivity]].
    destruct (Nat.ltb_spec i (tlen ts)) as [Hi|Hi]; (split; [|reflexivity]); [|exact I].
    apply (proj1 (tldist_iff ts) (sget_dd _ _ _ _ HS Eg)); rewrite tnth_list; apply nth_In; rewrite <- tlen_list; exact Hi.
  - (* NBind *)
    intros u w IH b t' Hw; rewrite tapp_bind; destruct (Nat.ltb_spec u ntm) as [Hu|]; [|discriminate].
    destruct (wapp F ntm S w) as [w'|] eqn:E; [|discriminate]; intros H; injection H as <-.
    destruct (IH _ Hw eq_refl) as [Hw' Hs]; split; [apply bnorm_dd, Hw'|].
    destruct (nth_error tenv u) as [x|] eqn:Ex; [|apply nth_error_None in Ex; lia].
    cbn [tden]; rewrite Ex; cbn [rtarget_result cres]; f_equal; f_equal.
    rewrite bnorm_sound, Hs, rpcompose_compose; reflexivity.
  - (* TNil *)
    intros ts' _ H; injection H as <-; split; [exact I|split; [reflexivity|]]; intros j Hj; cbn in Hj; lia.
  - (* TCons *)
    intros t IHt r IHr ts' [Ht Hr]; rewrite tlapp_cons.
    destruct (tapp F ntm S t) as [t'|] eqn:Et; [|discriminate].
    destruct (tlapp F ntm S r) as [r'|] eqn:Er; [|discriminate]; intros H; injection H as <-.
    destruct (IHt _ Ht eq_refl) as [Ht' Hst]; destruct (IHr _ Hr eq_refl) as [Hr' [Hl Hn]].
    cbn [tlen tldist]; split; [split; assumption|split; [congruence|]].
    intros [|j] Hj; cbn [tnth]; [exact Hst|apply Hn; lia].
  - (* SNil *)
    intros _ R H; injection H as <-; split; [exact HS|].
    intros l j; cbn [sget esem cres]; rewrite rapply_sden by exact HS'; reflexivity.
  - (* SEnt *)
    intros h ts IHts m r IHr [Hn [Hts Hd]] R; rewrite sgo_ent.
    destruct (sgo F ntm S r) as [R0|] eqn:ER; [|discriminate].
    destruct (tlapp F ntm S ts) as [ts'|] eqn:Ets; [|discriminate].
    destruct (sfind F h S) as [e|] eqn:Ee; [|discriminate].
    apply sfind_sound in Ee; destruct (IHr Hd _ eq_refl) as [Hd0 Hs0].
    destruct (IHts _ Hts eq_refl) as [Hts' [Hlen Hts0]].
    destruct (ofe e) as [tsS mS] eqn:Eo; intros Hset.
    assert (HtsS : tldist tsS).
    { destruct e as [[ts1 m1]|]; cbn [ofe] in Eo; injection Eo as <- <-; [|exact I].
      exact (sget_dd _ _ _ _ HS (eq_sym Ee)). }
    assert (Hcat : tldist (tcat ts' (tskip m tsS))).
    { apply tldist_iff; intros t Ht; rewrite tcat_list in Ht; apply in_app_or in Ht as [Ht|Ht].
      - exact (proj1 (tldist_iff ts') Hts' t Ht).
      - apply (proj1 (tldist_iff tsS) HtsS); exact (tskip_list_in _ _ _ Ht). }
    split; [exact (sset_dd _ _ _ _ _ Hd0 Hcat Hset)|].
    destruct (sset_sound _ _ _ _ _ (sdistd_sdist _ Hd0) Hset) as [HdR HsR].
    intros l j; rewrite HsR; cbn [sget].
    destruct (label_eqb_spec (lden h) l) as [<-|Hne]; [|apply Hs0].
    rewrite !esem_lsem; unfold lsem; rewrite <- !tlen_list, <- !tnth_list, tlen_tcat, tlen_tskip, Hlen.
    destruct (Nat.ltb_spec j (tlen ts)) as [Hj|Hj].
    + rewrite (proj2 (Nat.ltb_lt _ _)) by lia; rewrite tnth_tcat, Hlen, (proj2 (Nat.ltb_lt _ _)) by exact Hj.
      apply Hts0, Hj.
    + cbn [cres]; rewrite rapply_sden by exact HS'; cbn [v_label v_index]; rewrite <- Ee, <- esem_ofe, Eo.
      cbn [esem]; rewrite tnth_tcat, Hlen, (proj2 (Nat.ltb_ge j (tlen ts)) Hj), tnth_tskip.
      destruct (Nat.ltb_spec (j - tlen ts + m) (tlen tsS)) as [Hk|Hk].
      * rewrite (proj2 (Nat.ltb_lt j (tlen ts + (tlen tsS - m)))) by lia; do 3 f_equal; lia.
      * rewrite (proj2 (Nat.ltb_ge j (tlen ts + (tlen tsS - m)))) by lia; do 2 f_equal.
        destruct (Nat.leb_spec (tlen tsS) m); lia.
  - (* WEnd *)
    intros U IH w' HU; rewrite wapp_end; destruct (sgo F ntm S U) as [U'|] eqn:E; [|discriminate].
    intros H; injection H as <-; destruct (IH HU _ eq_refl) as [Hd' Hs]; split; [exact Hd'|].
    rewrite !wden_end; apply rextensionality; intros v.
    rewrite rapply_compose_cres, !rapply_sden by (apply sdistd_sdist; assumption); apply Hs.
  - (* WAtom *)
    intros U IH L a w _ w' [HU Hw]; rewrite wapp_atom; destruct (sgo F ntm S U) as [U'|] eqn:E; [|discriminate].
    intros H; injection H as <-; destruct (IH HU _ eq_refl) as [Hd' Hs]; split; [split; assumption|].
    rewrite !wden_atom, (rcompose_assoc (sden S)); f_equal.
    apply rextensionality; intros v.
    rewrite rapply_compose_cres, !rapply_sden by (apply sdistd_sdist; assumption); apply Hs.
  - (* WLay *)
    intros U _ w _ w' _; rewrite wapp_lay; discriminate.
Qed.

End CompSound.

Lemma scomp_sound A U R : sdistd A -> sdistd U -> scomp F ntm A U = Some R ->
  sdistd R /\ sden R = rcompose (sden A) (sden U).
Proof.
  unfold scomp; intros HA HU H.
  destruct (proj1 (proj2 (proj2 (comp_sound A HA))) U HU R H) as [Hd Hs]; split; [exact Hd|].
  apply rextensionality; intros v; rewrite rapply_compose_cres, !rapply_sden by (apply sdistd_sdist; assumption); apply Hs.
Qed.

Lemma wcons_sound A w w' : sdistd A -> wdist w -> wcons F ntm A w = Some w' -> wdist w' /\ wden w' = rcompose (sden A) (wden w).
Proof. unfold wcons; intros HA; apply (proj2 (proj2 (proj2 (comp_sound A HA)))). Qed.

(** *** Lifts *)

Lemma rlift_comm h h' (a : radj T) : h <> h' -> rlift h (rlift h' a) = rlift h' (rlift h a).
Proof.
  intros Hne; unfold rlift.
  rewrite !rpush_outer_inner; cbn [rshift_target].
  assert (E1 : shift_rvar (mk_rvar h 0) (mk_rvar h' 0) = mk_rvar h' 0)
    by (unfold shift_rvar; cbn; rewrite (proj2 (label_eqb_neq _ _) Hne); reflexivity).
  assert (E2 : shift_rvar (mk_rvar h' 0) (mk_rvar h 0) = mk_rvar h 0)
    by (unfold shift_rvar; cbn; rewrite (proj2 (label_eqb_neq _ _) (not_eq_sym Hne)); reflexivity).
  rewrite E1, E2, rpush_inner_comm, rpush_outer_comm by exact Hne; reflexivity.
Qed.

Lemma iter_rlift_comm h h' n n' (a : radj T) :
  h <> h' -> iter n (rlift h) (iter n' (rlift h') a) = iter n' (rlift h') (iter n (rlift h) a).
Proof.
  intros Hne; induction n as [|n IH]; cbn [iter]; [reflexivity|].
  rewrite IH; clear IH; generalize (iter n (rlift h) a); intros b.
  induction n' as [|n' IH]; cbn [iter]; [reflexivity|].
  rewrite <- IH, rlift_comm by exact Hne; reflexivity.
Qed.

Lemma lifts_cons h n L (x : radj T) : lifts ((h, n) :: L) x = iter n (rlift (lden h)) (lifts L x).
Proof. reflexivity. Qed.

Lemma ladd_sound h n L L' (x : radj T) : ladd F h n L = Some L' -> lifts L' x = iter n (rlift (lden h)) (lifts L x).
Proof.
  revert L'; induction L as [|[h' n'] L IH]; intros L'; cbn [ladd].
  - intros H; injection H as <-; reflexivity.
  - destruct (lcmp F h h') as [c|] eqn:E; [|discriminate]; assert (Hc := E).
    apply (lcmp_sound lenv F HF) in Hc; destruct c; cbn in Hc.
    + subst h'; intros H; injection H as <-; rewrite !lifts_cons, <- !iter_add, Nat.add_comm; reflexivity.
    + intros H; injection H as <-; reflexivity.
    + destruct (ladd F h n L) as [L''|] eqn:EL; [|discriminate]; intros H; injection H as <-.
      rewrite !lifts_cons, (IH _ eq_refl), iter_rlift_comm; [reflexivity|].
      intros Heq; rewrite Heq in Hc; exact (olabel_lt_irrefl _ Hc).
Qed.



(** *** Settling *)

Definition shiftk (h : option label) (k : nat) : radj T := iter k (rpush_outer h) ridentity.

Lemma sden_shseg h k : sden (shseg h k) = shiftk (lden h) k.
Proof. reflexivity. Qed.

Lemma sfront_sound h t s s' : sdistd s -> tdist t ->
  sfront F h t s = Some s' -> sdistd s' /\ sden s' = rpush_inner (lden h) (tden t) (sden s).
Proof.
  unfold sfront; intros Hdd Ht; pose proof (sdistd_sdist _ Hdd) as Ed.
  destruct (sfind F h s) as [e|] eqn:Ef; [|discriminate]; apply sfind_sound in Ef.
  destruct (ofe e) as [ts m] eqn:Eo; intros H.
  assert (Hts : tldist (TCons t ts)).
  { split; [exact Ht|]; destruct e as [[ts1 m1]|]; cbn [ofe] in Eo; injection Eo as <- <-; [|exact I].
    exact (sget_dd _ _ _ _ Hdd (eq_sym Ef)). }
  destruct (sset_sound _ _ _ _ _ Ed H) as [Hd' Hs]; split; [exact (sset_dd _ _ _ _ _ Hdd Hts H)|].
  apply rextensionality; intros [l j].
  rewrite rapply_push_inner; unfold rvar_eqb, unshift_rvar; cbn [v_label v_index].
  rewrite (label_eqb_sym l (lden h)).
  destruct (label_eqb_spec (lden h) l) as [<-|Hne]; cbn [andb].
  - rewrite rapply_sden, Hs, label_eqb_refl by exact Hd'; cbn [v_label v_index].
    destruct j as [|j]; [reflexivity|]; cbn [Nat.eqb].
    replace (0 <? S j) with true by reflexivity; replace (S j - 1) with j by lia.
    rewrite rapply_sden by exact Ed; cbn [v_label v_index].
    rewrite <- Ef, <- (esem_ofe (lden h) e j), Eo; cbn [esem tlen tnth].
    change (S j <? S (tlen ts)) with (j <? tlen ts); destruct (j <? tlen ts); [reflexivity|].
    do 2 f_equal; lia.
  - rewrite !rapply_sden by assumption; cbn [v_label v_index]; rewrite Hs.
    rewrite (proj2 (label_eqb_neq _ _) Hne); reflexivity.
Qed.

Lemma shseg_dd h k : sdistd (shseg h k).
Proof. cbn; repeat split; exact I. Qed.

Lemma slift_sound h s s' : sdistd s -> slift F ntm h s = Some s' -> sdistd s' /\ sden s' = rlift (lden h) (sden s).
Proof.
  unfold slift; intros Hd; destruct (scomp F ntm (shseg h 1) s) as [s1|] eqn:E; [|discriminate]; intros H.
  destruct (scomp_sound _ _ _ (shseg_dd h 1) Hd E) as [Hd1 Hs1].
  destruct (sfront_sound h (NVar h 0) _ _ Hd1 I H) as [Hd' Hs']; split; [exact Hd'|].
  rewrite Hs', Hs1, sden_shseg.
  unfold shiftk; cbn [iter]; rewrite rcompose_identity_push_outer; reflexivity.
Qed.

Lemma rpush_inner_compose h t (a b : radj T) :
  rpush_inner h t (rcompose a b) = rcompose (rpush_inner h t a) (rlift h b).
Proof.
  apply rextensionality; intro v.
  rewrite rapply_compose, rapply_push_inner, rapply_lift.
  destruct (rvar_eqb_spec v (mk_rvar h 0)) as [->|Hne].
  - rewrite rapply_push_inner, rvar_eqb_refl; reflexivity.
  - rewrite rapply_compose; destruct (rapply b (unshift_rvar (mk_rvar h 0) v)) as [w|[u ρ]].
    + rewrite rapply_push_inner.
      destruct (rvar_eqb_spec (shift_rvar (mk_rvar h 0) w) (mk_rvar h 0)) as [E|E].
      * exfalso; destruct w as [h' i]; unfold shift_rvar in E; revert E; case_vars.
      * rewrite unshift_shift_rvar; reflexivity.
    + rewrite rpshift_as_pcompose, rpcompose_compose, rcompose_push_inner_shift; reflexivity.
Qed.

(** *** Pulls *)

Lemma tden_bind u w b y : nth_error tenv u = Some y -> tden (NBind u w b) = RBind y (rpcompose (wden w) (bden b)).
Proof. intros H; cbn [tden]; rewrite H; reflexivity. Qed.

(** *** Lifts, pointwise *)

Lemma cres_compose (a b : radj T) r : cres a (cres b r) = cres (rcompose a b) r.
Proof.
  destruct r as [w|[u ρ]]; cbn [cres]; [rewrite rapply_compose_cres; reflexivity|].
  rewrite rpcompose_compose; reflexivity.
Qed.

Lemma cres_id r : cres (@ridentity T) r = r.
Proof. destruct r as [w|[u ρ]]; cbn [cres]; [apply rapply_identity|rewrite rpcompose_identity; reflexivity]. Qed.

Lemma shiftk_apply h n l j :
  rapply (shiftk h n) (mk_rvar l j) = inl (mk_rvar l (j + if label_eqb h l then n else 0)).
Proof. unfold shiftk; rewrite rapply_iter_outer, rapply_identity, iter_shift_rvar; reflexivity. Qed.

Lemma rlift_apply_other h (Y : radj T) v :
  v <> mk_rvar h 0 -> rapply (rlift h Y) v = cres (shiftk h 1) (rapply Y (unshift_rvar (mk_rvar h 0) v)).
Proof.
  intros Hv; rewrite rapply_lift; destruct (rvar_eqb_spec v (mk_rvar h 0)) as [E|_]; [contradiction|].
  destruct (rapply Y (unshift_rvar (mk_rvar h 0) v)) as [w|[u ρ]]; cbn [cres].
  - destruct w as [l' j']; rewrite shiftk_apply; unfold shift_rvar; cbn [v_label v_index].
    destruct (label_eqb h l'); cbn; f_equal; f_equal; lia.
  - rewrite rpshift_as_pcompose; unfold shiftk; cbn [iter]; reflexivity.
Qed.

Lemma shiftk_S h n : rcompose (shiftk h 1) (shiftk h n) = shiftk h (S n).
Proof. unfold shiftk; cbn [iter]; apply rcompose_identity_push_outer. Qed.

Lemma iter_rlift_apply h n (X : radj T) l j :
  rapply (iter n (rlift h) X) (mk_rvar l j)
  = if label_eqb h l && (j <? n) then inl (mk_rvar l j)
    else cres (shiftk h n) (rapply X (mk_rvar l (if label_eqb h l then j - n else j))).
Proof.
  revert j; induction n as [|n IH]; intros j; cbn [iter].
  - rewrite andb_false_r; unfold shiftk; cbn [iter]; rewrite cres_id.
    destruct (label_eqb h l); [rewrite Nat.sub_0_r|]; reflexivity.
  - destruct (label_eqb_spec h l) as [E|Hne]; cbn [andb]; [subst l|].
    + destruct j as [|j].
      * rewrite rapply_lift, rvar_eqb_refl; reflexivity.
      * rewrite rlift_apply_other by (intros E; injection E; lia).
        replace (unshift_rvar (mk_rvar h 0) (mk_rvar h (S j))) with (mk_rvar h j)
          by (unfold unshift_rvar; cbn; rewrite label_eqb_refl; cbn; f_equal; lia).
        rewrite IH, ?label_eqb_refl; cbn [andb].
        destruct (Nat.ltb_spec j n) as [Hj|Hj]; destruct (Nat.ltb_spec (S j) (S n)) as [Hj'|Hj']; try lia.
        -- cbn [cres]; rewrite shiftk_apply, ?label_eqb_refl; do 2 f_equal; lia.
        -- rewrite cres_compose, shiftk_S; do 2 f_equal; f_equal; lia.
    + rewrite rlift_apply_other by (intros E; injection E as E; congruence).
      replace (unshift_rvar (mk_rvar h 0) (mk_rvar l j)) with (mk_rvar l j)
        by (unfold unshift_rvar; cbn; rewrite (proj2 (label_eqb_neq _ _) Hne); reflexivity).
      rewrite IH, ?(proj2 (label_eqb_neq _ _) Hne); cbn [andb].
      rewrite cres_compose, shiftk_S; reflexivity.
Qed.

Fixpoint lc (l : option label) (L : list (lexp * nat)) : nat :=
  match L with [] => 0 | (h, n) :: L => (if label_eqb (lden h) l then n else 0) + lc l L end.

Fixpoint SH (L : list (lexp * nat)) : radj T :=
  match L with [] => ridentity | (h, n) :: L => rcompose (shiftk (lden h) n) (SH L) end.

Lemma SH_apply L l j : rapply (SH L) (mk_rvar l j) = inl (mk_rvar l (j + lc l L)).
Proof.
  revert j; induction L as [|[h n] L IH]; intros j; cbn [SH lc].
  - rewrite rapply_identity; f_equal; f_equal; lia.
  - rewrite rapply_compose_cres, IH; cbn [cres]; rewrite shiftk_apply.
    destruct (label_eqb (lden h) l); do 2 f_equal; lia.
Qed.

Lemma lifts_apply L (x : radj T) l j :
  rapply (lifts L x) (mk_rvar l j)
  = if j <? lc l L then inl (mk_rvar l j) else cres (SH L) (rapply x (mk_rvar l (j - lc l L))).
Proof.
  revert j; induction L as [|[h n] L IH]; intros j; cbn [lc SH].
  - cbn [lifts fold_right]; rewrite cres_id, Nat.sub_0_r; reflexivity.
  - rewrite lifts_cons, iter_rlift_apply.
    destruct (label_eqb (lden h) l) eqn:El; cbn [andb].
    + destruct (Nat.ltb_spec j n) as [Hj|Hj].
      { destruct (Nat.ltb_spec j (n + lc l L)); [reflexivity|lia]. }
      rewrite IH; destruct (Nat.ltb_spec (j - n) (lc l L)) as [Hj'|Hj'];
        destruct (Nat.ltb_spec j (n + lc l L)) as [Hk|Hk]; try lia.
      * cbn [cres]; rewrite shiftk_apply, El; do 2 f_equal; lia.
      * rewrite cres_compose; do 3 f_equal; lia.
    + rewrite IH; cbn [Nat.add].
      destruct (Nat.ltb_spec j (lc l L)); [cbn [cres]; rewrite shiftk_apply, El; do 2 f_equal; lia|].
      rewrite cres_compose; reflexivity.
Qed.

Lemma lcnt_sound h L c : lcnt F h L = Some c -> lc (lden h) L = c.
Proof.
  revert c; induction L as [|[h' n'] L IH]; intros c; cbn [lcnt lc]; [intros H; injection H as <-; reflexivity|].
  destruct (lcmp F h h') as [cm|] eqn:E; [|discriminate].
  destruct (lcnt F h L) as [c'|] eqn:El; [|destruct cm; discriminate].
  pose proof (lcmp_sound lenv F HF _ _ _ E) as Hc; rewrite (IH c' eq_refl).
  destruct cm; cbn in Hc; intros H; injection H as <-.
  - subst h'; rewrite label_eqb_refl; reflexivity.
  - rewrite (proj2 (label_eqb_neq _ _)); [reflexivity|]; intros Heq; rewrite Heq in Hc; exact (olabel_lt_irrefl _ Hc).
  - rewrite (proj2 (label_eqb_neq _ _)); [reflexivity|]; intros Heq; rewrite <- Heq in Hc; exact (olabel_lt_irrefl _ Hc).
Qed.

(** *** Settling in one pass: soundness *)

Definition ldist (hs : list lexp) : Prop := forall x y, In x hs -> In y hs -> lden x = lden y -> x = y.

Lemma lins_spec h hs hs' :
  lins F h hs = Some hs' -> (forall x, In x hs' <-> x = h \/ In x hs) /\ (ldist hs -> ldist hs').
Proof.
  revert hs'; induction hs as [|h' r IH]; intros hs'; cbn [lins].
  - intros H; injection H as <-; split.
    + intros x; cbn; split; [intros [<-|[]]; left; reflexivity|intros [->|[]]; left; reflexivity].
    + intros _ x y [<-|[]] [<-|[]] _; reflexivity.
  - destruct (lcmp F h h') as [c|] eqn:Ec; [|discriminate].
    destruct c.
    + intros H; injection H as <-; apply (lcmp_sound lenv F HF) in Ec; cbn in Ec; subst h'.
      split; [intros x; split; [intros Hx; right; exact Hx|intros [->|Hx]; [left; reflexivity|exact Hx]]|tauto].
    + destruct (lins F h r) as [r'|] eqn:Er; [|discriminate]; intros H; injection H as <-.
      destruct (IH _ eq_refl) as [Hi Hd]; split.
      * intros x; cbn; rewrite Hi; tauto.
      * intros Hdh x y Hx Hy Exy; cbn in Hx, Hy.
        assert (Hdr : ldist r) by (intros a b Ha Hb; apply Hdh; right; assumption).
        assert (Hne : lden h <> lden h') by (apply (lcmp_neq lenv F HF _ _ _ Ec); discriminate).
        destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy]; [reflexivity| | |apply Hd; assumption].
        -- apply Hi in Hy as [<-|Hy]; [congruence|apply Hdh; [left|right|]; auto].
        -- apply Hi in Hx as [<-|Hx]; [congruence|apply Hdh; [right|left|]; auto].
    + destruct (lins F h r) as [r'|] eqn:Er; [|discriminate]; intros H; injection H as <-.
      destruct (IH _ eq_refl) as [Hi Hd]; split.
      * intros x; cbn; rewrite Hi; tauto.
      * intros Hdh x y Hx Hy Exy; cbn in Hx, Hy.
        assert (Hdr : ldist r) by (intros a b Ha Hb; apply Hdh; right; assumption).
        assert (Hne : lden h <> lden h') by (apply (lcmp_neq lenv F HF _ _ _ Ec); discriminate).
        destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy]; [reflexivity| | |apply Hd; assumption].
        -- apply Hi in Hy as [<-|Hy]; [congruence|apply Hdh; [left|right|]; auto].
        -- apply Hi in Hx as [<-|Hx]; [congruence|apply Hdh; [right|left|]; auto].
Qed.

Lemma linss_spec hs acc hs' :
  linss F hs acc = Some hs' -> (forall x, In x hs' <-> In x hs \/ In x acc) /\ (ldist acc -> ldist hs').
Proof.
  revert acc; induction hs as [|h hs IH]; intros acc; cbn [linss].
  - intros H; injection H as <-; split; [intros x; split; [intros Hx; right; exact Hx|intros [[]|Hx]; exact Hx]|tauto].
  - destruct (lins F h acc) as [acc'|] eqn:E; [|discriminate]; intros H.
    destruct (lins_spec _ _ _ E) as [Hi Hd]; destruct (IH _ H) as [Hi' Hd']; split.
    + intros x; rewrite Hi', Hi; cbn; split; [intros [Hx|[->|Hx]]; auto|intros [[->|Hx]|Hx]; auto].
    + intros Ha; apply Hd', Hd, Ha.
Qed.

Lemma lins_nodup h hs hs' : lins F h hs = Some hs' -> NoDup hs -> NoDup hs'.
Proof.
  revert hs'; induction hs as [|h' r IH]; intros hs'; cbn [lins].
  - intros H; injection H as <-; intros _; constructor; [intros []|constructor].
  - destruct (lcmp F h h') as [c|] eqn:Ec; [|discriminate].
    destruct c; [intros H; injection H as <-; tauto| |];
      (destruct (lins F h r) as [r'|] eqn:Er; [|discriminate]; intros H; injection H as <-; intros Hn;
       inversion Hn as [|x l Hx Hr]; subst; constructor; [|apply IH; [reflexivity|exact Hr]];
       intros Hi; apply (proj1 (proj1 (lins_spec _ _ _ Er) h')) in Hi as [Hi|Hi]; [subst h'|contradiction];
       unfold lcmp in Ec; rewrite (proj2 (lexp_eqb_eq h h) eq_refl) in Ec; discriminate).
Qed.

Lemma linss_nodup hs acc hs' : linss F hs acc = Some hs' -> NoDup acc -> NoDup hs'.
Proof.
  revert acc; induction hs as [|h hs IH]; intros acc; cbn [linss]; [intros H; injection H as <-; tauto|].
  destruct (lins F h acc) as [acc'|] eqn:E; [|discriminate]; intros H Hn.
  apply (IH _ H), (lins_nodup _ _ _ E Hn).
Qed.

(** All comparisons among the labels [linss] collects are known. *)
Definition lknown (hs : list lexp) : Prop := forall x y, In x hs -> In y hs -> exists c, lcmp F x y = Some c.

Lemma lcmp_known_sym x y c : lcmp F x y = Some c -> exists c', lcmp F y x = Some c'.
Proof.
  unfold lcmp; destruct (lexp_eqb x y) eqn:E1.
  - apply lexp_eqb_eq in E1; subst y; rewrite (proj2 (lexp_eqb_eq x x) eq_refl); eexists; reflexivity.
  - assert (E1' : lexp_eqb y x = false)
      by (destruct (lexp_eqb y x) eqn:E; [apply lexp_eqb_eq in E; subst y; rewrite (proj2 (lexp_eqb_eq x x) eq_refl) in E1; discriminate|reflexivity]).
    rewrite E1'; destruct (lt_known F x y), (lt_known F y x); try discriminate; eexists; reflexivity.
Qed.

Lemma lins_cmp h hs hs' : lins F h hs = Some hs' ->
  (forall z, In z hs -> exists c, lcmp F h z = Some c) \/ In h hs.
Proof.
  revert hs'; induction hs as [|h' r IH]; intros hs'; cbn [lins]; [intros _; left; intros z []|].
  destruct (lcmp F h h') as [[]|] eqn:Ec; try discriminate.
  - intros _; right; apply (lcmp_sound lenv F HF) in Ec; cbn in Ec; subst h'; left; reflexivity.
  - destruct (lins F h r) as [r'|] eqn:Er; [|discriminate]; intros _.
    destruct (IH _ eq_refl) as [H|H]; [left; intros z [<-|Hz]; [eexists; exact Ec|apply H, Hz]|right; right; exact H].
  - destruct (lins F h r) as [r'|] eqn:Er; [|discriminate]; intros _.
    destruct (IH _ eq_refl) as [H|H]; [left; intros z [<-|Hz]; [eexists; exact Ec|apply H, Hz]|right; right; exact H].
Qed.

Lemma lins_known h hs hs' : lins F h hs = Some hs' -> lknown hs -> lknown hs'.
Proof.
  intros E Hk; destruct (lins_spec _ _ _ E) as [Hi _].
  assert (Hrefl : forall x, exists c, lcmp F x x = Some c)
    by (intros x; unfold lcmp; rewrite (proj2 (lexp_eqb_eq x x) eq_refl); eexists; reflexivity).
  assert (Hh : forall z, In z hs -> exists c, lcmp F h z = Some c).
  { destruct (lins_cmp _ _ _ E) as [H|H]; [exact H|intros z Hz; exact (Hk h z H Hz)]. }
  intros x y Hx Hy; apply Hi in Hx as [->|Hx]; apply Hi in Hy as [->|Hy].
  - apply Hrefl.
  - apply Hh, Hy.
  - destruct (Hh x Hx) as [c Ec]; exact (lcmp_known_sym _ _ _ Ec).
  - apply Hk; assumption.
Qed.

Lemma linss_known hs acc hs' : linss F hs acc = Some hs' -> lknown acc -> lknown hs'.
Proof.
  revert acc; induction hs as [|h hs IH]; intros acc; cbn [linss]; [intros H; injection H as <-; tauto|].
  destruct (lins F h acc) as [acc'|] eqn:E; [|discriminate]; intros H Hk.
  apply (IH _ H), (lins_known _ _ _ E Hk).
Qed.

Lemma sfind_known g s : (forall k, In k (seg_labels s) -> exists c, lcmp F g k = Some c) -> exists e, sfind F g s = Some e.
Proof.
  induction s as [|h ts m r IH] using seg_spine; cbn [sfind seg_labels]; [eexists; reflexivity|]; intros H.
  destruct (H h (or_introl eq_refl)) as [c Ec]; rewrite Ec.
  destruct c; [eexists; reflexivity| |]; apply IH; intros k Hk; apply H; right; apply in_or_app; right; exact Hk.
Qed.

Lemma linss_sfind (L : list (lexp * nat)) U hs : linss F (map fst L ++ seg_labels U) [] = Some hs ->
  forall g, In g hs -> exists e, sfind F g U = Some e.
Proof.
  intros Eh g Hg; destruct (linss_spec _ _ _ Eh) as [Hin _].
  pose proof (linss_known _ _ _ Eh ltac:(intros x y [])) as Hk.
  apply sfind_known; intros k Hkk; apply Hk; [exact Hg|apply Hin; left; apply in_or_app; right; exact Hkk].
Qed.

Lemma lsum_lc hs L h :
  ldist hs -> (forall k, In k (map fst L) -> In k hs) -> In h hs -> lsum h L = lc (lden h) L.
Proof.
  intros Hd Hk Hh; induction L as [|[h' n] L IH]; cbn [lsum lc]; [reflexivity|].
  rewrite IH by (intros k Hi; apply Hk; right; exact Hi); f_equal.
  destruct (lexp_eqb h h') eqn:Ehh; [apply lexp_eqb_eq in Ehh; subst h'; rewrite label_eqb_refl; reflexivity|].
  assert (Hne : h <> h') by (intros E; subst h'; rewrite (proj2 (lexp_eqb_eq h h) eq_refl) in Ehh; discriminate).
  destruct (label_eqb_spec (lden h') (lden h)) as [E|_]; [|reflexivity].
  exfalso; apply Hne, Hd; [exact Hh|apply Hk; left; reflexivity|symmetry; exact E].
Qed.

Lemma lc_out hs L l :
  (forall k, In k (map fst L) -> In k hs) -> (forall g, In g hs -> lden g <> l) -> lc l L = 0.
Proof.
  intros Hk Hl; induction L as [|[h' n] L IH]; cbn [lc]; [reflexivity|].
  rewrite IH by (intros k Hi; apply Hk; right; exact Hi).
  destruct (label_eqb_spec (lden h') l) as [E|_]; [|reflexivity].
  exfalso; apply (Hl h'); [apply Hk; left; reflexivity|exact E].
Qed.

(** Segments built entry by entry. *)
Fixpoint esl (l : option label) (es : list (lexp * (list ntgt * nat))) (j : nat) : rresult T :=
  match es with
  | [] => inl (mk_rvar l j)
  | (h, (xs, m)) :: es => if label_eqb (lden h) l then lsem l xs m j else esl l es j
  end.

Lemma sbuild_sem es s : sbuild F es = Some s -> sdist s /\ forall l j, esem l (sget l s) j = esl l es j.
Proof.
  revert s; induction es as [|[h [xs m]] es IH]; intros s; cbn [sbuild].
  - intros H; injection H as <-; split; [exact I|reflexivity].
  - destruct (sbuild F es) as [s0|] eqn:E; [|discriminate]; intros H.
    destruct (IH _ eq_refl) as [Hd Hs]; destruct (sset_sound _ _ _ _ _ Hd H) as [Hd' Hs']; split; [exact Hd'|].
    intros l j; rewrite Hs', Hs; cbn [esl]; rewrite esem_lsem, tl_list_of; reflexivity.
Qed.

Lemma esl_in {E : lexp -> list ntgt * nat} hs g j :
  ldist hs -> In g hs -> esl (lden g) (map (fun g => (g, E g)) hs) j = let '(xs, m) := E g in lsem (lden g) xs m j.
Proof.
  intros Hd Hg; induction hs as [|h hs IH]; [destruct Hg|]; cbn [map esl].
  destruct (E h) as [xs m] eqn:Eh.
  destruct (label_eqb_spec (lden h) (lden g)) as [Ehg|Hne].
  - assert (h = g) as <- by (apply Hd; [left; reflexivity|exact Hg|exact Ehg]); rewrite Eh; reflexivity.
  - destruct Hg as [<-|Hg]; [contradiction|]; apply IH; [|exact Hg].
    intros x y Hx Hy; apply Hd; right; assumption.
Qed.

Lemma esl_out {E : lexp -> list ntgt * nat} hs l j :
  (forall g, In g hs -> lden g <> l) -> esl l (map (fun g => (g, E g)) hs) j = inl (mk_rvar l j).
Proof.
  intros Hl; induction hs as [|h hs IH]; cbn [map esl]; [reflexivity|].
  destruct (E h) as [xs m]; destruct (label_eqb_spec (lden h) l) as [E'|_].
  - exfalso; apply (Hl h); [left; reflexivity|exact E'].
  - apply IH; intros g Hg; apply Hl; right; exact Hg.
Qed.

Lemma Forall2_in_r {A B} (R : A -> B -> Prop) xs ys y : Forall2 R xs ys -> In y ys -> exists x, In x xs /\ R x y.
Proof.
  induction 1 as [|x y' xs ys Hxy H2 IH]; [intros []|]; intros [<-|Hy]; [exists x; split; [left; reflexivity|exact Hxy]|].
  destruct (IH Hy) as [x' [Hx Hr]]; exists x'; split; [right; exact Hx|exact Hr].
Qed.

Lemma omap_f2 {A B} (f : A -> option B) xs ys : omap f xs = Some ys -> Forall2 (fun x y => f x = Some y) xs ys.
Proof.
  revert ys; induction xs as [|x xs IH]; intros ys; cbn [omap].
  - intros H; injection H as <-; constructor.
  - destruct (f x) as [y|] eqn:Ef; [|discriminate]; destruct (omap f xs) as [ys'|] eqn:Eo; [|discriminate].
    intros H; injection H as <-; constructor; [exact Ef|apply IH; reflexivity].
Qed.

Lemma esl_f2_in (f : lexp -> option (lexp * (list ntgt * nat))) hs qs g j :
  Forall2 (fun x y => f x = Some y) hs qs -> (forall x q, f x = Some q -> fst q = x) -> ldist hs -> In g hs ->
  exists xs m, f g = Some (g, (xs, m)) /\ esl (lden g) qs j = lsem (lden g) xs m j.
Proof.
  intros H2 Hk Hd Hg; induction H2 as [|h q hs qs Hq H2 IH]; [destruct Hg|].
  destruct q as [h' [xs m]]; pose proof (Hk _ _ Hq) as E; cbn in E; subst h'; cbn [esl].
  destruct (label_eqb_spec (lden h) (lden g)) as [Ehg|Hne].
  - assert (h = g) as <- by (apply Hd; [left; reflexivity|exact Hg|exact Ehg]); exists xs, m; split; [exact Hq|reflexivity].
  - destruct Hg as [<-|Hg]; [contradiction|]; apply IH; [|exact Hg].
    intros x y Hx Hy; apply Hd; right; assumption.
Qed.

Lemma esl_f2_out (f : lexp -> option (lexp * (list ntgt * nat))) hs qs l j :
  Forall2 (fun x y => f x = Some y) hs qs -> (forall x q, f x = Some q -> fst q = x) ->
  (forall g, In g hs -> lden g <> l) -> esl l qs j = inl (mk_rvar l j).
Proof.
  intros H2 Hk Hl; induction H2 as [|h q hs qs Hq H2 IH]; cbn [esl]; [reflexivity|].
  destruct q as [h' [xs m]]; pose proof (Hk _ _ Hq) as E; cbn in E; subst h'.
  destruct (label_eqb_spec (lden h) l) as [E'|_].
  - exfalso; apply (Hl h); [left; reflexivity|exact E'].
  - apply IH; intros g Hg; apply Hl; right; exact Hg.
Qed.

Lemma filter_seq_pos (p : nat -> bool) R : forall s i, s <= i -> i < s + R -> p i = true ->
  let P := filter p (seq s R) in
  nth (List.length (filter (fun q => q <? i) P)) P 0 = i /\ List.length (filter (fun q => q <? i) P) < List.length P.
Proof.
  induction R as [|R IH]; intros s i Hs Hi Hp; [lia|]; cbn [seq filter].
  assert (Hgt : forall q, In q (filter p (seq (S s) R)) -> s < q)
    by (intros q Hq; apply filter_In in Hq as [Hq _]; apply in_seq in Hq; lia).
  destruct (Nat.eq_dec i s) as [->|Hne].
  - rewrite Hp; cbn [filter]; rewrite Nat.ltb_irrefl.
    replace (filter (fun q => q <? s) (filter p (seq (S s) R))) with (@nil nat); [cbn; split; [reflexivity|lia]|].
    symmetry; apply (proj2 (filter_nil _ _)) || idtac.
    induction (filter p (seq (S s) R)) as [|q qs IHq]; [reflexivity|]; cbn [filter].
    destruct (Nat.ltb_spec q s) as [Hq|_]; [exfalso; specialize (Hgt q (or_introl eq_refl)); lia|].
    apply IHq; intros q' Hq'; apply Hgt; right; exact Hq'.
  - destruct (IH (S s) i ltac:(lia) ltac:(lia) Hp) as [E1 E2].
    destruct (p s); cbn [filter List.length nth].
    + rewrite (proj2 (Nat.ltb_lt s i) ltac:(lia)); cbn [List.length nth]; split; [exact E1|lia].
    + split; [exact E1|exact E2].
Qed.

Lemma lbuild_sound es L' (x : radj T) : lbuild F es = Some L' -> lifts L' x = lifts es x.
Proof.
  revert L'; induction es as [|[h n] es IH]; intros L'; cbn [lbuild].
  - intros H; injection H as <-; reflexivity.
  - destruct (lbuild F es) as [L0|] eqn:E; [|discriminate].
    destruct (Nat.eqb_spec n 0) as [->|_].
    + intros H; injection H as <-; rewrite lifts_cons, (IH _ eq_refl); reflexivity.
    + intros H; rewrite (ladd_sound _ _ _ _ x H), (IH _ eq_refl), lifts_cons; reflexivity.
Qed.

Lemma lc_map (f : lexp -> nat) hs g :
  ldist hs -> NoDup hs -> In g hs -> lc (lden g) (map (fun g => (g, f g)) hs) = f g.
Proof.
  intros Hd Hn Hg; induction hs as [|h hs IH]; [destruct Hg|]; cbn [map lc].
  inversion Hn as [|x l Hx Hr]; subst.
  destruct (label_eqb_spec (lden h) (lden g)) as [E|Hne].
  - assert (h = g) as <- by (apply Hd; [left; reflexivity|exact Hg|exact E]).
    enough (lc (lden h) (map (fun g => (g, f g)) hs) = 0) by lia.
    apply (lc_out hs); [intros k Hk; rewrite map_map in Hk; cbn in Hk; rewrite map_id in Hk; exact Hk|].
    intros g' Hg' E'; apply Hx; rewrite <- (Hd g' h (or_intror Hg') (or_introl eq_refl) E'); exact Hg'.
  - destruct Hg as [<-|Hg]; [contradiction|]; apply IH; [intros a b Ha Hb; apply Hd; right; assumption|exact Hr|exact Hg].
Qed.

Lemma sget_label l s ts m : sget l s = Some (ts, m) -> exists h, In h (seg_labels s) /\ lden h = l
  /\ forall t, In t (tl_list ts) -> forall h' j, t = NVar h' j -> In h' (seg_labels s).
Proof.
  induction s as [|h ts' m' r IH] using seg_spine; cbn [sget seg_labels]; [discriminate|].
  destruct (label_eqb_spec (lden h) l) as [E|_].
  - intros H; injection H as <- <-; exists h; split; [left; reflexivity|split; [exact E|]].
    intros t Ht h' j ->; right; apply in_or_app; left; apply in_flat_map; exists (NVar h' j); split; [exact Ht|left; reflexivity].
  - intros H; destruct (IH H) as [h0 [H1 [H2 H3]]]; exists h0; split; [right; apply in_or_app; right; exact H1|split; [exact H2|]].
    intros t Ht h' j Et; right; apply in_or_app; right; exact (H3 t Ht h' j Et).
Qed.

(** What settling needs of payload composition and normalisation. *)
Definition wc_ok (wc : word -> word -> option word) : Prop :=
  forall w1 w2 w, wdist w1 -> wdist w2 -> wc w1 w2 = Some w -> wdist w /\ wden w = rcompose (wden w1) (wden w2).

Definition pn_ok (pn : option nat -> word -> option word) : Prop :=
  forall b w w', wdist w -> pn b w = Some w' -> wdist w' /\ rpcompose (wden w') (bden b) = rpcompose (wden w) (bden b).

Lemma atom_dd L a : wdist (WAtom SNil L a (WEnd SNil)).
Proof. split; exact I. Qed.

Section OneSound.

Variable L : list (lexp * nat).
Variable U : seg.
Variable hs : list lexp.
Hypothesis HdU : sdist U.
Hypothesis Hd : ldist hs.
Hypothesis Hn : NoDup hs.
Hypothesis HL : forall k, In k (map fst L) -> In k hs.
Hypothesis HU : forall k, In k (seg_labels U) -> In k hs.
Hypothesis Hf : forall g, In g hs -> exists e, sfind F g U = Some e.

Lemma U_in g i : In g hs -> rapply (sden U) (mk_rvar (lden g) i) = rtarget_result (tden (otg F U g i)).
Proof.
  intros Hg; destruct (Hf g Hg) as [e Ee]; pose proof (sfind_sound _ _ _ Ee) as Es.
  rewrite rapply_sden by exact HdU; cbn [v_label v_index]; rewrite <- Es.
  unfold otg, entd; rewrite Ee; destruct e as [[ts m]|]; cbn [esem].
  - rewrite esem_lsem || idtac; unfold lsem; rewrite tlen_list, tnth_list; destruct (_ <? _); reflexivity.
  - cbn [List.length]; replace (i <? 0) with false by (destruct i; reflexivity); cbn; do 2 f_equal; lia.
Qed.

Lemma otg_label g i h j : In g hs -> otg F U g i = NVar h j -> In h hs.
Proof.
  intros Hg; destruct (Hf g Hg) as [e Ee]; pose proof (sfind_sound _ _ _ Ee) as Es.
  unfold otg, entd; rewrite Ee; destruct e as [[ts m]|].
  - destruct (_ <? _) eqn:Ei; [|intros H; injection H as <- _; exact Hg].
    intros E; symmetry in Es; destruct (sget_label _ _ _ _ Es) as [h0 [_ [_ H3]]].
    apply HU, (H3 _ (nth_In _ _ (proj1 (Nat.ltb_lt _ _) Ei)) h j E).
  - cbn; intros H; injection H as <- _; exact Hg.
Qed.

Lemma U_out l i : (forall g, In g hs -> lden g <> l) -> rapply (sden U) (mk_rvar l i) = inl (mk_rvar l i).
Proof.
  intros Hl; rewrite rapply_sden by exact HdU; cbn [v_label v_index].
  destruct (sget l U) as [[ts m]|] eqn:E; [|reflexivity].
  exfalso; destruct (sget_label _ _ _ _ E) as [h [H1 [H2 _]]]; exact (Hl h (HU _ H1) H2).
Qed.

Lemma otg_tail g i : In g hs -> orng F L U g <= i -> otg F U g i = NVar g (i - List.length (fst (entd F U g)) + snd (entd F U g))
  /\ inP L (otg F U g i) = false.
Proof.
  intros Hg; unfold orng, otg; destruct (entd F U g) as [xs m]; cbn [fst snd]; intros Hi.
  destruct (Nat.ltb_spec i (List.length xs)); [lia|]; split; [reflexivity|].
  cbn [inP]; apply Nat.ltb_ge; lia.
Qed.

Lemma u'ent_eta g : u'ent F L U g = (g, snd (u'ent F L U g)).
Proof. unfold u'ent; destruct (entd F U g); reflexivity. Qed.

Definition u'tgt (g : lexp) (i : nat) : ntgt :=
  if inP L (otg F U g i) then NVar g (opos F L U g i) else oreidx F L U (otg F U g i).

Lemma U'_in g i : In g hs ->
  esl (lden g) (map (u'ent F L U) hs) i = rtarget_result (tden (u'tgt g i)).
Proof.
  intros Hg; rewrite (map_ext (u'ent F L U) (fun g => (g, snd (u'ent F L U g))) u'ent_eta hs), (esl_in hs g i Hd Hg).
  pose proof (otg_tail g i Hg) as Ht; unfold u'tgt; unfold u'ent in *; unfold orng in *.
  destruct (entd F U g) as [xs m] eqn:Ee; cbn [snd fst] in *.
  set (R := Nat.max (List.length xs) (List.length xs + lsum g L - m)) in *.
  unfold lsem; rewrite length_map, length_seq.
  destruct (Nat.ltb_spec i R) as [Hi|Hi].
  - assert (Hnth : forall (f : nat -> ntgt) d, nth i (map f (seq 0 R)) d = f i)
      by (intros f d; rewrite (nth_indep _ d (f 0)) by (rewrite length_map, length_seq; lia);
          rewrite map_nth, seq_nth by lia; reflexivity).
    rewrite Hnth; reflexivity.
  - destruct (Ht Hi) as [E1 E2]; rewrite E2, E1; cbn [oreidx tden rtarget_result].
    do 2 f_equal; lia.
Qed.

Lemma U'_out (l : option label) i : (forall g, In g hs -> lden g <> l) ->
  esl l (map (u'ent F L U) hs) i = inl (mk_rvar l i).
Proof.
  intros Hl; rewrite (map_ext (u'ent F L U) (fun g => (g, snd (u'ent F L U g))) u'ent_eta hs); apply esl_out, Hl.
Qed.

Lemma oP_pos g i : In g hs -> inP L (otg F U g i) = true ->
  nth (opos F L U g i) (oP F L U g) 0 = i /\ opos F L U g i < olp F L U g.
Proof.
  intros Hg Hp.
  assert (Hi : i < orng F L U g) by (destruct (Nat.lt_ge_cases i (orng F L U g)) as [H|H];
    [exact H|rewrite (proj2 (otg_tail g i Hg H)) in Hp; discriminate]).
  unfold opos, olp, oP; apply (filter_seq_pos (fun i => inP L (otg F U g i)) (orng F L U g) 0 i); [lia|lia|exact Hp].
Qed.

Lemma f2_nth {A B} (P : A -> B -> Prop) xs ys : Forall2 P xs ys -> forall p da db, p < List.length xs -> P (nth p xs da) (nth p ys db).
Proof.
  induction 1 as [|x y xs ys Hxy H2 IH]; intros p da db Hp; [cbn in Hp; lia|].
  destruct p as [|p]; [exact Hxy|apply IH; cbn in Hp; lia].
Qed.

Hypothesis HdUd : sdistd U.

Lemma otg_dd g i u w b : In g hs -> otg F U g i = NBind u w b -> wdist w.
Proof.
  intros Hg; destruct (Hf g Hg) as [e Ee]; pose proof (sfind_sound _ _ _ Ee) as Es.
  unfold otg, entd; rewrite Ee; destruct e as [[ts m]|]; [|cbn; destruct (i <? 0); discriminate].
  destruct (Nat.ltb_spec i (List.length (tl_list ts))) as [Hi|Hi]; [|discriminate].
  intros E; pose proof (proj1 (tldist_iff ts) (sget_dd _ _ _ _ HdUd (eq_sym Es)) _ (nth_In _ (NVar LNone 0) Hi)) as H.
  rewrite E in H; exact H.
Qed.

Variable wc : word -> word -> option word.
Hypothesis Hwc : wc_ok wc.
Variable pn : option nat -> word -> option word.
Hypothesis Hpn : pn_ok pn.
Variable a : nat.
Variable qs : list (lexp * (list ntgt * nat)).
Variables Q U' : seg.
Hypothesis Hq : Forall2 (fun g q => qent F ntm wc pn a L U g = Some q) hs qs.
Hypothesis HQ : sbuild F qs = Some Q.
Hypothesis HU' : sbuild F (map (u'ent F L U) hs) = Some U'.

Let Lraw := map (fun g => (g, olp F L U g)) hs.

Lemma qent_key x q : qent F ntm wc pn a L U x = Some q -> fst q = x.
Proof. unfold qent; destruct (omap _ _); [intros H; injection H as <-; reflexivity|discriminate]. Qed.

Lemma Q_in g j : In g hs -> exists xs,
  Forall2 (fun i t => otq ntm wc pn a L (otg F U g i) = Some t) (oP F L U g) xs
  /\ esem (lden g) (sget (lden g) Q) j = lsem (lden g) xs (lsum g L) j.
Proof.
  intros Hg; destruct (esl_f2_in _ hs qs g j Hq qent_key Hd Hg) as [xs [m [E1 E2]]].
  unfold qent in E1; destruct (omap _ _) as [ts|] eqn:Eo; [|discriminate]; injection E1 as <- <-.
  exists ts; split; [apply omap_f2, Eo|]; rewrite (proj2 (sbuild_sem _ _ HQ)); exact E2.
Qed.

Lemma Q_out (l : option label) j : (forall g, In g hs -> lden g <> l) -> esem l (sget l Q) j = inl (mk_rvar l j).
Proof. intros Hl; rewrite (proj2 (sbuild_sem _ _ HQ)); apply (esl_f2_out _ hs qs l j Hq qent_key Hl). Qed.

Lemma QSH : rcompose (sden Q) (SH Lraw) = SH L.
Proof.
  apply rextensionality; intros [l j]; rewrite rapply_compose_cres, !SH_apply; cbn [cres].
  rewrite rapply_sden by exact (proj1 (sbuild_sem _ _ HQ)); cbn [v_label v_index].
  destruct (existsb (fun g => label_eqb (lden g) l) hs) eqn:Ex.
  - apply existsb_exists in Ex as [g [Hg El]]; destruct (label_eqb_spec (lden g) l) as [<-|]; [|discriminate].
    destruct (Q_in g (j + lc (lden g) Lraw) Hg) as [xs [H2 E]]; rewrite E.
    unfold Lraw; rewrite (lc_map (olp F L U) hs g Hd Hn Hg), <- (lsum_lc hs L g Hd HL Hg).
    pose proof (Forall2_length H2) as Hlen; fold (olp F L U g) in Hlen.
    unfold lsem; destruct (Nat.ltb_spec (j + olp F L U g) (List.length xs)); [lia|].
    do 2 f_equal; unfold olp in *; lia.
  - assert (Hl : forall g, In g hs -> lden g <> l)
      by (intros g Hg E; subst l;
          rewrite (proj2 (existsb_exists _ _) (ex_intro _ g (conj Hg (label_eqb_refl _)))) in Ex; discriminate).
    rewrite (Q_out l _ Hl).
    rewrite (lc_out hs L l HL Hl), (lc_out hs Lraw l) by (try exact Hl; intros k Hk; unfold Lraw in Hk;
      rewrite map_map in Hk; cbn in Hk; rewrite map_id in Hk; exact Hk).
    reflexivity.
Qed.

Theorem one_core : rcompose (lifts L (aden a)) (sden U) = rcompose (sden Q) (rcompose (lifts Lraw (aden a)) (sden U')).
Proof.
  destruct (sbuild_sem _ _ HU') as [HdU' HsU'].
  assert (HlcR : forall g, In g hs -> lc (lden g) Lraw = olp F L U g)
    by (intros g Hg; unfold Lraw; apply lc_map; assumption).
  assert (HLR : forall k, In k (map fst Lraw) -> In k hs)
    by (intros k Hk; unfold Lraw in Hk; rewrite map_map in Hk; cbn in Hk; rewrite map_id in Hk; exact Hk).
  apply rextensionality; intros [l i]; rewrite !rapply_compose_cres.
  rewrite (rapply_sden lenv tenv aenv penv U') by exact HdU'; cbn [v_label v_index]; rewrite HsU'.
  destruct (existsb (fun g => label_eqb (lden g) l) hs) eqn:Ex.
  - apply existsb_exists in Ex as [g [Hg El]]; destruct (label_eqb_spec (lden g) l) as [<-|]; [|discriminate].
    rewrite (U_in g i Hg), (U'_in g i Hg); unfold u'tgt.
    destruct (inP L (otg F U g i)) eqn:Ep.
    + destruct (oP_pos g i Hg Ep) as [Enth Hlt].
      cbn [tden rtarget_result cres].
      rewrite lifts_apply, (HlcR g Hg), (proj2 (Nat.ltb_lt _ _) Hlt); cbn [cres].
      rewrite (rapply_sden lenv tenv aenv penv Q) by exact (proj1 (sbuild_sem _ _ HQ)); cbn [v_label v_index].
      destruct (Q_in g (opos F L U g i) Hg) as [xs [H2 E]]; rewrite E.
      pose proof (Forall2_length H2) as Hlen.
      assert (Hp : opos F L U g i < List.length (oP F L U g)) by (unfold olp in Hlt; exact Hlt).
      pose proof (f2_nth _ _ _ H2 (opos F L U g i) 0 (NVar LNone 0) Hp) as Ht.
      rewrite Enth in Ht.
      unfold lsem; rewrite (proj2 (Nat.ltb_lt (opos F L U g i) (List.length xs)) ltac:(lia)).
      destruct (otg F U g i) as [h j|u w b] eqn:Eo; cbn [otq] in Ht.
      * injection Ht as Ht; rewrite <- Ht; cbn [tden rtarget_result cres].
        cbn [inP] in Ep; apply Nat.ltb_lt in Ep.
        rewrite lifts_apply, <- (lsum_lc hs L h Hd HL (otg_label g i h j Hg Eo)), (proj2 (Nat.ltb_lt _ _) Ep); reflexivity.
      * destruct (Nat.ltb_spec u ntm) as [Hu|]; [|discriminate].
        destruct (wc (WAtom SNil L a (WEnd SNil)) w) as [w'|] eqn:Ew; [|discriminate].
        destruct (pn b w') as [w''|] eqn:Ep'; [|discriminate]; injection Ht as Ht; rewrite <- Ht.
        destruct (nth_error tenv u) as [y|] eqn:Ey; [|apply nth_error_None in Ey; lia].
        rewrite !(tden_bind _ _ _ _ Ey); cbn [rtarget_result cres].
        destruct (Hwc _ _ _ (atom_dd L a) (otg_dd g i u w b Hg Eo) Ew) as [Hw' Ewc].
        rewrite (proj2 (Hpn _ _ _ Hw' Ep')), Ewc, rpcompose_compose, wden_atom, wden_end.
        change (sden SNil) with (@ridentity T); rewrite rcompose_identity_l, rcompose_identity_r; reflexivity.
    + destruct (otg F U g i) as [h j|u w b] eqn:Eo; cbn [inP] in Ep; [|discriminate].
      apply Nat.ltb_ge in Ep; pose proof (otg_label g i h j Hg Eo) as Hh.
      cbn [oreidx tden rtarget_result cres].
      rewrite !lifts_apply, (HlcR h Hh), <- (lsum_lc hs L h Hd HL Hh).
      destruct (Nat.ltb_spec j (lsum h L)); [lia|].
      destruct (Nat.ltb_spec (j - lsum h L + olp F L U h) (olp F L U h)); [lia|].
      rewrite cres_compose, QSH; do 3 f_equal; lia.
  - assert (Hl : forall g, In g hs -> lden g <> l)
      by (intros g Hg E; subst l;
          rewrite (proj2 (existsb_exists _ _) (ex_intro _ g (conj Hg (label_eqb_refl _)))) in Ex; discriminate).
    rewrite (U_out l i Hl), (U'_out l i Hl); cbn [cres].
    rewrite !lifts_apply, (lc_out hs L l HL Hl), (lc_out hs Lraw l HLR Hl); cbn [Nat.ltb Nat.leb].
    destruct (i <? 0) eqn:Ei; [apply Nat.ltb_lt in Ei; lia|].
    rewrite cres_compose, QSH; reflexivity.
Qed.

End OneSound.

Lemma sbuild_dd es s : (forall h xs m, In (h, (xs, m)) es -> forall t, In t xs -> tdist t) ->
  sbuild F es = Some s -> sdistd s.
Proof.
  revert s; induction es as [|[h [xs m]] es IH]; intros s Ht; cbn [sbuild]; [intros H; injection H as <-; exact I|].
  destruct (sbuild F es) as [s0|] eqn:E0; [|discriminate]; intros E.
  apply (sset_dd h (tl_of xs) m s0 s); [apply IH; [intros h' xs' m' Hi; apply (Ht h' xs' m'); right; exact Hi|reflexivity]| |exact E].
  apply tldist_iff; rewrite tl_list_of; apply (Ht h xs m); left; reflexivity.
Qed.

Theorem settle1_sound wc (Hwc : wc_ok wc) pn (Hpn : pn_ok pn) a A L U A' L' U' rest :
  sdistd A -> sdistd U -> settle1 F ntm wc pn a A L U = Some (A', L', U') ->
  sdistd A' /\ sdistd U'
  /\ rcompose (sden A') (rcompose (lifts L' (aden a)) (rcompose (sden U') rest))
     = rcompose (sden A) (rcompose (lifts L (aden a)) (rcompose (sden U) rest)).
Proof.
  intros HA HUd; pose proof (sdistd_sdist _ HUd) as Ed.
  unfold settle1.
  destruct (linss F (map fst L ++ seg_labels U) []) as [hs|] eqn:Eh; [|discriminate].
  destruct (linss_spec _ _ _ Eh) as [Hin Hdist].
  assert (Hd : ldist hs) by (apply Hdist; intros x y []).
  assert (Hn : NoDup hs) by (apply (linss_nodup _ _ _ Eh); constructor).
  assert (HL : forall k, In k (map fst L) -> In k hs) by (intros k Hk; apply Hin; left; apply in_or_app; left; exact Hk).
  assert (HU : forall k, In k (seg_labels U) -> In k hs) by (intros k Hk; apply Hin; left; apply in_or_app; right; exact Hk).
  pose proof (linss_sfind L U hs Eh) as Hf.
  destruct (omap (qent F ntm wc pn a L U) hs) as [qs|] eqn:Eq; [|discriminate].
  destruct (sbuild F (map (u'ent F L U) hs)) as [U1|] eqn:EU; [|discriminate].
  destruct (lbuild F (map (fun g => (g, olp F L U g)) hs)) as [L1|] eqn:EL; [|discriminate].
  destruct (sbuild F qs) as [Q|] eqn:EQ; [|discriminate].
  destruct (scomp F ntm A Q) as [A1|] eqn:EA; [|discriminate].
  intros H; injection H as <- <- <-.
  assert (HQ : sdistd Q).
  { apply (sbuild_dd qs); [|exact EQ]; intros h xs m Hi t Ht.
    destruct (Forall2_in_r _ _ _ _ (omap_f2 _ _ _ Eq) Hi) as [g [Hg E]]; unfold qent in E; revert E.
    destruct (omap (fun i => otq ntm wc pn a L (otg F U g i)) (oP F L U g)) as [ts|] eqn:Eo; [|discriminate].
    intros E; injection E as _ <- _.
    destruct (Forall2_in_r _ _ _ _ (omap_f2 _ _ _ Eo) Ht) as [i [_ Et]].
    destruct (otg F U g i) as [h' j|u w b] eqn:Eg; cbn [otq] in Et; [injection Et as <-; exact I|].
    destruct (u <? ntm); [|discriminate].
    destruct (wc (WAtom SNil L a (WEnd SNil)) w) as [w'|] eqn:Ew; [|discriminate].
    destruct (pn b w') as [w''|] eqn:Ep; [|discriminate]; injection Et as <-.
    destruct (Hwc _ _ _ (atom_dd L a) ltac:(eapply otg_dd; eassumption) Ew) as [Hw' _].
    exact (proj1 (Hpn _ _ _ Hw' Ep)). }
  destruct (scomp_sound _ _ _ HA HQ EA) as [HA1 EA1].
  split; [exact HA1|split].
  { refine (sbuild_dd _ _ _ EU); intros h xs m Hi t Ht; apply in_map_iff in Hi as [g [E _]].
    unfold u'ent in E; destruct (entd F U g); injection E as _ <- _; apply in_map_iff in Ht as [i [<- _]].
    destruct (inP L (otg F U g i)) eqn:Ep; [exact I|]; destruct (otg F U g i); [exact I|discriminate Ep]. }
  rewrite EA1, (lbuild_sound _ _ _ EL).
  pose proof (one_core L U hs Ed Hd Hn HL HU Hf HUd wc Hwc pn Hpn a qs Q U1 (omap_f2 _ _ _ Eq) EQ EU) as Hc.
  rewrite (rcompose_assoc (lifts L (aden a))), Hc, <- !rcompose_assoc; reflexivity.
Qed.

Definition wrest (w : word) : radj T :=
  match w with WEnd _ => ridentity | WAtom _ L a w => rcompose (lifts L (aden a)) (wden w) | WLay _ w => wden w end.

Lemma wden_head w : wden w = rcompose (sden (whead w)) (wrest w).
Proof. destruct w; cbn [whead wrest]; [rewrite wden_end, rcompose_identity_r|rewrite wden_atom|rewrite wden_lay]; reflexivity. Qed.

Lemma wden_sethead w U : wden (wsethead w U) = rcompose (sden U) (wrest w).
Proof. destruct w; cbn [wsethead wrest]; [rewrite wden_end, rcompose_identity_r|rewrite wden_atom|rewrite wden_lay]; reflexivity. Qed.

Lemma whead_dd w : wdist w -> sdistd (whead w).
Proof. destruct w; cbn [wdist whead]; [exact (fun H => H)|intros [H _]; exact H|intros [H _]; exact H]. Qed.

Lemma wsethead_dd w U : wdist w -> sdistd U -> wdist (wsethead w U).
Proof. destruct w; cbn [wdist wsethead]; [intros _ H; exact H|intros [_ Hw] H; split; assumption|intros [_ Hw] H; split; assumption]. Qed.

Lemma settle_sound wc (Hwc : wc_ok wc) pn (Hpn : pn_ok pn) A L a w w' :
  sdistd A -> wdist w -> settle F ntm wc pn A L a w = Some w' ->
  wdist w' /\ wden w' = rcompose (sden A) (rcompose (lifts L (aden a)) (wden w)).
Proof.
  unfold settle; intros HA Hw; destruct (settle1 F ntm wc pn a A L (whead w)) as [[[A' L'] U']|] eqn:E; [|discriminate].
  intros H; injection H as <-.
  destruct (settle1_sound _ Hwc _ Hpn _ _ _ _ _ _ _ (wrest w) HA (whead_dd _ Hw) E) as [HA' [HU' Eq]].
  split; [split; [exact HA'|apply wsethead_dd; assumption]|].
  rewrite wden_atom, wden_sethead, Eq, <- (wden_head w); reflexivity.
Qed.

(** *** The constructors *)

Lemma named_compose_l (Y X X' : radj T) : named_eq X X' -> named_eq (rcompose Y X) (rcompose Y X').
Proof. intros H v Hv; rewrite !rapply_compose_cres, (H v Hv); reflexivity. Qed.

Lemma pnormf_sound wc (Hwc : wc_ok wc) pn (Hpn : pn_ok pn) :
  forall w w', wdist w -> pnormf F ntm wc pn w = Some w' -> wdist w' /\ named_eq (wden w) (wden w').
Proof.
  induction w as [s|A L a w IH|s w IH] using word_spine; cbn [pnormf]; [| |intros w' _ H; discriminate H].
  - intros w' Hd H; injection H as <-; split; [apply sdrop_dd, Hd|]; rewrite !wden_end; apply named_sdrop_none.
  - intros w0 [HA Hw]; destruct w as [s|A' L' a' w1|s1 w1]; [| |cbn [pnormf]; discriminate].
    + unfold pfinal; pose proof (sdistd_sdist _ Hw) as Ed.
      destruct (sset F LNone TNil (lcount LNone L) s) as [s'|] eqn:Es; [|discriminate]; intros H.
      destruct (settle_sound _ Hwc _ Hpn A L a (WEnd s') w0 HA (sset_dd LNone TNil _ _ _ Hw I Es) H) as [Hd' Eq].
      split; [exact Hd'|]; rewrite Eq, wden_atom.
      apply named_compose_l, named_compose_l; rewrite !wden_end.
      intros [l j] Hl; rewrite !rapply_sden by first [exact Ed|exact (proj1 (sset_sound _ _ _ _ _ Ed Es))].
      cbn [v_label v_index]; rewrite (proj2 (sset_sound _ _ _ _ _ Ed Es)); cbn [lden].
      destruct l; [reflexivity|contradiction].
    + destruct (pnormf F ntm wc pn (WAtom A' L' a' w1)) as [w''|] eqn:E; [|discriminate]; intros H.
      destruct (IH _ Hw eq_refl) as [Hd'' Hn''].
      destruct (settle_sound _ Hwc _ Hpn _ _ _ _ _ HA Hd'' H) as [Hd' Eq].
      split; [exact Hd'|]; rewrite Eq, wden_atom.
      apply named_compose_l, named_compose_l, Hn''.
Qed.

Lemma wops_sound n : wc_ok (fst (wops F ntm n)) /\ pn_ok (snd (wops F ntm n)).
Proof.
  induction n as [|n [IHc IHp]]; [split; intros; discriminate|]; cbn [wops].
  destruct (wops F ntm n) as [wc pn] eqn:Ew; cbn [fst snd] in *; split.
  - intros w1; induction w1 as [A|A L a w1 IH|A w1 IH] using word_spine; intros w2 w Hw1 Hw2; cbn [wcomp_with];
      [| |discriminate].
    + intros H; exact (wcons_sound _ _ _ Hw1 Hw2 H).
    + destruct Hw1 as [HA Hw1].
      destruct (wcomp_with F ntm wc pn w1 w2) as [w'|] eqn:E; [|discriminate]; intros H.
      destruct (IH _ _ Hw1 Hw2 E) as [Hd' Eq'].
      destruct (settle_sound _ IHc _ IHp _ _ _ _ _ HA Hd' H) as [Hd Eq].
      split; [exact Hd|]; rewrite Eq, Eq', wden_atom, !rcompose_assoc; reflexivity.
  - intros [m|] w w' Hw H; cbn [bnormf] in H; [injection H as <-; split; [exact Hw|reflexivity]|].
    destruct (pnormf_sound _ IHc _ IHp _ _ Hw H) as [Hd Hn]; split; [exact Hd|].
    symmetry; apply rpcompose_named, Hn.
Qed.

Lemma wcomp_sound w1 w2 w : wdist w1 -> wdist w2 -> wcomp F ntm w1 w2 = Some w ->
  wdist w /\ wden w = rcompose (wden w1) (wden w2).
Proof. apply (proj1 (wops_sound 64)). Qed.

Lemma pnormw_sound b w w' : wdist w -> pnormw F ntm b w = Some w' ->
  wdist w' /\ rpcompose (wden w') (bden b) = rpcompose (wden w) (bden b).
Proof. apply (proj2 (wops_sound 64)). Qed.

Lemma wlift_sound h w w' : wdist w -> wlift F ntm h w = Some w' -> wdist w' /\ wden w' = rlift (lden h) (wden w).
Proof.
  revert w'; induction w as [s|s L a w IH|s w IH] using word_spine; intros w' Hd; cbn [wlift]; [| |discriminate].
  - destruct (slift F ntm h s) as [s'|] eqn:E; [|discriminate]; intros H; injection H as <-.
    destruct (slift_sound _ _ _ Hd E) as [Hd' Eq]; split; [exact Hd'|]; rewrite !wden_end; exact Eq.
  - destruct Hd as [Hs Hw].
    destruct (slift F ntm h s) as [s'|] eqn:Es; [|discriminate].
    destruct (ladd F h 1 L) as [L'|] eqn:EL; [|discriminate].
    destruct (wlift F ntm h w) as [w1|] eqn:Ew; [|discriminate]; intros H; injection H as <-.
    destruct (slift_sound _ _ _ Hs Es) as [Hs' Eqs]; destruct (IH _ Hw eq_refl) as [Hw' Eqw].
    split; [split; assumption|].
    rewrite !wden_atom, Eqs, (ladd_sound _ _ _ _ _ EL), Eqw; cbn [iter].
    rewrite !rlift_compose; reflexivity.
Qed.

Lemma wpush_sound h t w w' : tdist t -> wdist w -> wpush F ntm h t w = Some w' ->
  wdist w' /\ wden w' = rpush_inner (lden h) (tden t) (wden w).
Proof.
  intros Ht; destruct w as [s|s L a w|s w]; cbn [wpush]; [| |discriminate].
  - intros Hs; destruct (sfront F h t s) as [s'|] eqn:E; [|discriminate]; intros H; injection H as <-.
    destruct (sfront_sound _ _ _ _ Hs Ht E) as [Hs' Eq]; split; [exact Hs'|]; rewrite !wden_end; exact Eq.
  - intros [Hs Hw].
    destruct (sfront F h t s) as [s'|] eqn:Es; [|discriminate].
    destruct (ladd F h 1 L) as [L'|] eqn:EL; [|discriminate].
    destruct (wlift F ntm h w) as [w1|] eqn:Ew; [|discriminate]; intros H; injection H as <-.
    destruct (sfront_sound _ _ _ _ Hs Ht Es) as [Hs' Eqs]; destruct (wlift_sound _ _ _ Hw Ew) as [Hw' Eqw].
    split; [split; assumption|].
    rewrite !wden_atom, Eqs, (ladd_sound _ _ _ _ _ EL), Eqw.
    cbn [iter]; rewrite rpush_inner_compose, rlift_compose; reflexivity.
Qed.

Lemma wouter_sound h w w' : wdist w -> wouter F ntm h w = Some w' -> wdist w' /\ wden w' = rpush_outer (lden h) (wden w).
Proof.
  unfold wouter; intros Hw H; destruct (wcons_sound _ _ _ (shseg_dd h 1) Hw H) as [Hd Eq]; split; [exact Hd|].
  rewrite Eq, sden_shseg; unfold shiftk; cbn [iter]; apply rcompose_identity_push_outer.
Qed.

(** *** Expressions *)

Fixpoint aeden (e : aexp) : radj T :=
  match e with
  | AId => ridentity
  | AAtom n => aden n
  | ACompose a b => rcompose (aeden a) (aeden b)
  | AOuter h a => rpush_outer (lden h) (aeden a)
  | AInner h t a => rpush_inner (lden h) (teden t) (aeden a)
  | ALift h a => rlift (lden h) (aeden a)
  end
with teden (t : texp) : rtarget T :=
  match t with
  | TVarE h i => RRename (mk_rvar (lden h) i)
  | TBindE u p => match nth_error tenv u with Some x => RBind x (peden p) | None => RRename (mk_rvar None 0) end
  | TShiftE h t => match teden t with RRename w => RRename (shift_rvar (mk_rvar (lden h) 0) w) | r => r end
  end
with peden (p : pexp) : rpadj T :=
  match p with
  | PId => rpidentity
  | PAtom n => nth n penv rpidentity
  | PComp a p => rpcompose (aeden a) (peden p)
  | PShift h p => rpshift (lden h) (peden p)
  end.

Scheme aexp_mind := Induction for aexp Sort Prop
with texp_mind := Induction for texp Sort Prop
with pexp_mind := Induction for pexp Sort Prop.
Combined Scheme exp_mind from aexp_mind, texp_mind, pexp_mind.

Lemma wden_id : wden (WEnd SNil) = ridentity.
Proof. reflexivity. Qed.

(** *** Applying a single segment to a variable *)

Definition seg_tgt (F : order) (Sg : seg) (h : lexp) (i : nat) : option ntgt :=
  match sfind F h Sg with
  | Some None => Some (NVar h i)
  | Some (Some (ts, m)) => Some (if i <? tlen ts then tnth ts i else NVar h (i - tlen ts + m))
  | None => None
  end.

(** Following a variable through a word, from the right: [Some (Some t)]
    when it reaches the target [t]; [Some None] when, with every label
    comparison known, it reaches a lifted atom that does not pass it
    around; [None] when a label comparison is unknown (or a term turns up
    before the last segment, which a normal form never has). *)
Fixpoint wtrace (F : order) (w : word) (h : lexp) (i : nat) : option (option ntgt) :=
  match w with
  | WEnd Sg => match seg_tgt F Sg h i with Some t => Some (Some t) | None => None end
  | WAtom Sg L a w =>
      match wtrace F w h i with
      | Some (Some (NVar h' j)) =>
          match lcnt F h' L with
          | Some c => if j <? c then match seg_tgt F Sg h' j with Some t => Some (Some t) | None => None end
                      else Some None
          | None => None
          end
      | Some None => Some None
      | _ => None
      end
  | WLay _ _ => None
  end.

Definition wtgt (F : order) (w : word) (h : lexp) (i : nat) : option ntgt :=
  match wtrace F w h i with Some (Some t) => Some t | _ => None end.

Lemma seg_tgt_sound Sg h i t : sdistd Sg ->
  seg_tgt F Sg h i = Some t -> tdist t /\ rapply (sden Sg) (mk_rvar (lden h) i) = rtarget_result (tden t).
Proof.
  unfold seg_tgt; intros Hdd; pose proof (sdistd_sdist _ Hdd) as Ed.
  destruct (sfind F h Sg) as [r|] eqn:Ef; [|discriminate]; apply sfind_sound in Ef.
  rewrite rapply_sden by exact Ed; cbn [v_label v_index].
  rewrite <- Ef; destruct r as [[ts m]|]; cbn [esem]; intros H; injection H as <-; [|split; [exact I|reflexivity]].
  destruct (Nat.ltb_spec i (tlen ts)) as [Hi|Hi]; (split; [|reflexivity]); [|exact I].
  apply (proj1 (tldist_iff ts) (sget_dd _ _ _ _ Hdd (eq_sym Ef))); rewrite tnth_list; apply nth_In.
  rewrite <- tlen_list; exact Hi.
Qed.

Lemma wtrace_sound w h i t : wdist w ->
  wtrace F w h i = Some (Some t) -> tdist t /\ rapply (wden w) (mk_rvar (lden h) i) = rtarget_result (tden t).
Proof.
  revert t; induction w as [Sg|Sg L a w IH|Sg w IH] using word_spine; intros t Hd; cbn [wtrace]; [| |discriminate].
  - rewrite wden_end; destruct (seg_tgt F Sg h i) as [t'|] eqn:E; [|discriminate].
    intros H; injection H as <-; apply seg_tgt_sound; assumption.
  - destruct Hd as [Hs Hw].
    destruct (wtrace F w h i) as [[[h1 j1|]|]|] eqn:E; try discriminate.
    destruct (lcnt F h1 L) as [c|] eqn:EL; [|discriminate].
    destruct (Nat.ltb_spec j1 c) as [Hj|]; [|discriminate].
    destruct (seg_tgt F Sg h1 j1) as [t'|] eqn:Es; [|discriminate]; intros H; injection H as <-.
    destruct (seg_tgt_sound _ _ _ _ Hs Es) as [Ht Eq]; split; [exact Ht|].
    rewrite wden_atom, !rapply_compose_cres, (proj2 (IH _ Hw eq_refl)); cbn [tden rtarget_result cres].
    rewrite lifts_apply, (lcnt_sound _ _ _ EL), (proj2 (Nat.ltb_lt _ _) Hj); cbn [cres].
    exact Eq.
Qed.

Lemma wtgt_sound w h i t : wdist w ->
  wtgt F w h i = Some t -> tdist t /\ rapply (wden w) (mk_rvar (lden h) i) = rtarget_result (tden t).
Proof.
  unfold wtgt; intros Hd; destruct (wtrace F w h i) as [[t'|]|] eqn:E; try discriminate.
  intros H; injection H as <-; exact (wtrace_sound _ _ _ _ Hd E).
Qed.

(** *** Materialised payloads

    Results that are the same except that, where the first is a term
    [u⟨ρ⟩], the second is the term [g ρ u] with the identity payload
    adjustment ([mrel]); and the facts that say which term atoms are
    such [g ρ u].  [Eval] checks two adjustments against them. *)
Fixpoint mfind (facts : list (nat * nat * aexp)) (k : nat) : option (nat * aexp) :=
  match facts with
  | [] => None
  | (k', u, eb) :: r => if Nat.eqb k k' then Some (u, eb) else mfind r k
  end.

Section Mat.

Variable g : rpadj T -> T -> T.
Variable facts : list (nat * nat * aexp).
Hypothesis Hfacts : Forall (fun f => let '(k, u, eb) := f in
  forall y, nth_error tenv u = Some y -> nth_error tenv k = Some (g (rpcompose (aeden eb) rpidentity) y)) facts.

Lemma mfind_fact k u eb y : mfind facts k = Some (u, eb) -> nth_error tenv u = Some y ->
  nth_error tenv k = Some (g (rpcompose (aeden eb) rpidentity) y).
Proof.
  revert Hfacts; generalize facts as fs; intros fs Hfs; induction fs as [|[[k' u'] eb'] r IH]; cbn [mfind]; [discriminate|].
  inversion Hfs as [|f l Hf Hr]; subst.
  destruct (Nat.eqb_spec k k') as [->|_]; [intros H; injection H as <- <-; exact (Hf y)|exact (IH Hr)].
Qed.

Definition mrel (r r' : rresult T) : Prop :=
  r = r' \/ exists u ρ, r = inr (u, ρ) /\ r' = inr (g ρ u, rpidentity).

End Mat.

End Sound.
