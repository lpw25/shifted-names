(** * The reflective normaliser

    Goals between adjustments are decided by reflection: both sides are
    reified into [aexp], an expression over label atoms, adjustment atoms,
    payload atoms and term atoms, normalised to a [word], and compared.

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
    facts [(x, y)] ("[x < y]"), followed transitively. *)
Definition lt_base (a b : lexp) : bool :=
  match a, b with
  | LCon s, LCon s' => is_less_than_label s s'
  | LNone, _ => false
  | _, LNone => true
  | _, _ => false
  end.

Fixpoint lt_reach (F : list (lexp * lexp)) (fuel : nat) (a b : lexp) : bool :=
  lt_base a b
  || match fuel with
     | 0 => false
     | S f => existsb (fun '(x, y) => lexp_eqb x a && (lexp_eqb y b || lt_reach F f y b)) F
     end.

Definition lt_known (F : list (lexp * lexp)) (a b : lexp) : bool := lt_reach F (List.length F) a b.

Definition lcmp (F : list (lexp * lexp)) (a b : lexp) : option comparison :=
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

Definition facts_ok (F : list (lexp * lexp)) : Prop :=
  Forall (fun '(x, y) => olabel_lt (lden x) (lden y)) F.

Variable F : list (lexp * lexp).
Hypothesis HF : facts_ok F.

Lemma lt_base_sound a b : lt_base a b = true -> olabel_lt (lden a) (lden b).
Proof. destruct a, b; cbn; try discriminate; unfold olabel_lt; cbn; auto. Qed.

Lemma lt_reach_sound fuel : forall a b, lt_reach F fuel a b = true -> olabel_lt (lden a) (lden b).
Proof.
  induction fuel as [|f IH]; intros a b H; cbn [lt_reach] in H; apply orb_true_iff in H as [H|H];
    try (apply lt_base_sound, H); [discriminate|].
  apply existsb_exists in H as [[x y] [Hin H]].
  apply andb_true_iff in H as [Hx H]; apply lexp_eqb_eq in Hx; subst x.
  pose proof (proj1 (Forall_forall _ F) HF _ Hin) as Hxy; cbn in Hxy.
  apply orb_true_iff in H as [H|H].
  - apply lexp_eqb_eq in H; subst y; exact Hxy.
  - apply (olabel_lt_trans _ (lden y)); [exact Hxy|apply IH, H].
Qed.

Lemma lt_known_sound a b : lt_known F a b = true -> olabel_lt (lden a) (lden b).
Proof. apply lt_reach_sound. Qed.

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

Lemma lcmp_eq a b : lcmp F a b = Some Eq -> lden a = lden b.
Proof. intros H; apply lcmp_sound in H; cbn in H; subst; reflexivity. Qed.

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
| WAtom (s : seg) (L : list (lexp * nat)) (a : nat) (w : word).

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
  (forall s, P (WEnd s)) -> (forall s L a w, P w -> P (WAtom s L a w)) -> forall w, P w.
Proof. intros H0 HS; fix IH 1; intros [s|s L a w]; [apply H0|apply HS, IH]. Qed.

Lemma tlist_spine (P : tlist -> Prop) :
  P TNil -> (forall t r, P r -> P (TCons t r)) -> forall ts, P ts.
Proof. intros H0 HS; fix IH 1; intros [|t r]; [exact H0|apply HS, IH]. Qed.

Fixpoint tl_list (ts : tlist) : list ntgt :=
  match ts with TNil => [] | TCons t r => t :: tl_list r end.

Fixpoint tl_of (l : list ntgt) : tlist :=
  match l with [] => TNil | t :: r => TCons t (tl_of r) end.

Lemma tl_list_of l : tl_list (tl_of l) = l.
Proof. induction l; cbn; congruence. Qed.

Lemma tl_of_list ts : tl_of (tl_list ts) = ts.
Proof. induction ts; cbn; congruence. Qed.

(** *** Decidable equality *)

Fixpoint lifts_eqb (L L' : list (lexp * nat)) : bool :=
  match L, L' with
  | [], [] => true
  | (h, n) :: L, (h', n') :: L' => lexp_eqb h h' && Nat.eqb n n' && lifts_eqb L L'
  | _, _ => false
  end.

Lemma lifts_eqb_eq L L' : lifts_eqb L L' = true -> L = L'.
Proof.
  revert L'; induction L as [|[h n] L IH]; intros [|[h' n'] L']; cbn; try discriminate; [reflexivity|].
  intros H; apply andb_true_iff in H as [H H3]; apply andb_true_iff in H as [H1 H2].
  apply lexp_eqb_eq in H1; apply Nat.eqb_eq in H2; subst; f_equal; apply IH, H3.
Qed.

Fixpoint ntgt_eqb (t1 t2 : ntgt) : bool :=
  match t1, t2 with
  | NVar h i, NVar h' i' => lexp_eqb h h' && Nat.eqb i i'
  | NBind u w b, NBind u' w' b' =>
      Nat.eqb u u' && word_eqb w w'
      && match b, b' with None, None => true | Some n, Some n' => Nat.eqb n n' | _, _ => false end
  | _, _ => false
  end
with tlist_eqb (ts1 ts2 : tlist) : bool :=
  match ts1, ts2 with
  | TNil, TNil => true
  | TCons t r, TCons t' r' => ntgt_eqb t t' && tlist_eqb r r'
  | _, _ => false
  end
with seg_eqb (s1 s2 : seg) : bool :=
  match s1, s2 with
  | SNil, SNil => true
  | SEnt h ts m r, SEnt h' ts' m' r' => lexp_eqb h h' && tlist_eqb ts ts' && Nat.eqb m m' && seg_eqb r r'
  | _, _ => false
  end
with word_eqb (w1 w2 : word) : bool :=
  match w1, w2 with
  | WEnd s, WEnd s' => seg_eqb s s'
  | WAtom s L a w, WAtom s' L' a' w' =>
      seg_eqb s s'
      && lifts_eqb L L'
      && Nat.eqb a a' && word_eqb w w'
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
    apply andb_true_iff in H as [H1 H2]; apply lexp_eqb_eq in H1; apply Nat.eqb_eq in H2; subst; reflexivity.
  - intros u w IH b [|u' w' b'] H; cbn in H; [discriminate|].
    apply andb_true_iff in H as [H H3]; apply andb_true_iff in H as [H1 H2].
    apply Nat.eqb_eq in H1; apply IH in H2; subst.
    destruct b as [n|], b' as [n'|]; try discriminate; [apply Nat.eqb_eq in H3; subst|]; reflexivity.
  - intros [|]; cbn; congruence.
  - intros t IHt r IHr [|t' r'] H; cbn in H; [discriminate|].
    apply andb_true_iff in H as [H1 H2]; f_equal; [apply IHt, H1|apply IHr, H2].
  - intros [|]; cbn; congruence.
  - intros h ts IHts m r IHr [|h' ts' m' r'] H; cbn in H; [discriminate|].
    apply andb_true_iff in H as [H H4]; apply andb_true_iff in H as [H H3]; apply andb_true_iff in H as [H1 H2].
    apply lexp_eqb_eq in H1; apply Nat.eqb_eq in H3; subst; f_equal; [apply IHts, H2|apply IHr, H4].
  - intros s IH [s'|] H; cbn in H; [f_equal; apply IH, H|discriminate].
  - intros s IHs L a w IHw [|s' L' a' w'] H; cbn in H; [discriminate|].
    apply andb_true_iff in H as [H H4]; apply andb_true_iff in H as [H H3]; apply andb_true_iff in H as [H1 H2].
    apply Nat.eqb_eq in H3; subst; f_equal; [apply IHs, H1|apply lifts_eqb_eq, H2|apply IHw, H4].
Qed.

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
  end.

Definition sden (s : seg) : radj T := sins s (souts s ridentity).

Lemma wden_end s : wden (WEnd s) = sden s.
Proof. reflexivity. Qed.

Lemma wden_atom s L a w : wden (WAtom s L a w) = rcompose (sden s) (rcompose (lifts L (aden a)) (wden w)).
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

Variable F : list (lexp * lexp).
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
      match trim h (rev (tl_list ts)) m with
      | ([], 0) => Some s'
      | (rts, m') => Some (sput h (tl_of (rev rts)) m' s')
      end
  end.

(** Labels known to be pairwise distinct. *)
Fixpoint sall_ne (h : lexp) (s : seg) : bool :=
  match s with
  | SNil => true
  | SEnt h' _ _ r => match lcmp F h h' with Some Lt | Some Gt => sall_ne h r | _ => false end
  end.

Fixpoint sdistb (s : seg) : bool :=
  match s with
  | SNil => true
  | SEnt h _ _ r => sall_ne h r && sdistb r
  end.

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
  end.

Definition bnorm (b : option nat) (w : word) : word :=
  match b with None => pnorm w | Some _ => w end.

(** *** Composing with a segment on the left *)

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
with sgo (U : seg) : option seg :=
  match U with
  | SNil => Some S
  | SEnt h ts m r =>
      match sgo r, tlapp ts, sfind h S with
      | Some R, Some ts', Some e =>
          let '(tsS, mS) := ofe e in
          sset h (tcat ts' (tskip m tsS)) (if tlen tsS <=? m then m - tlen tsS + mS else mS) R
      | _, _, _ => None
      end
  end
with wapp (w : word) : option word :=
  match w with
  | WEnd U => if sdistb U then match sgo U with Some U' => Some (WEnd U') | None => None end else None
  | WAtom U L a w =>
      if sdistb U then match sgo U with Some U' => Some (WAtom U' L a w) | None => None end else None
  end.

End Comp.

(** [scomp S U] is [S ∘ U]; [wcons S w] is [S ∘ w]. *)
Definition scomp (S U : seg) : option seg :=
  if sdistb S && sdistb U then sgo S U else None.

Definition wcons (S : seg) (w : word) : option word :=
  if sdistb S then wapp S w else None.

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

(** Taking [k] lifts by [h] out to the front. *)
Fixpoint lsub (h : lexp) (k : nat) (L : list (lexp * nat)) : option (list (lexp * nat)) :=
  match L with
  | [] => None
  | (h', n') :: L' =>
      match lcmp F h h' with
      | None => None
      | Some Eq => if k <=? n' then Some (if Nat.eqb n' k then L' else (h', n' - k) :: L') else None
      | Some _ => match lsub h k L' with Some L'' => Some ((h', n') :: L'') | None => None end
      end
  end.

Definition shseg (h : lexp) (k : nat) : seg := SEnt h TNil k SNil.

Definition sfront (h : lexp) (t : ntgt) (s : seg) : option seg :=
  if sdistb s then
    match sfind h s with
    | Some e => let '(ts, m) := ofe e in sset h (TCons t ts) m s
    | None => None
    end
  else None.

Definition slift (h : lexp) (s : seg) : option seg :=
  match scomp (shseg h 1) s with Some s' => sfront h (NVar h 0) s' | None => None end.

Definition whead (w : word) : seg := match w with WEnd s | WAtom s _ _ _ => s end.

Definition wsethead (w : word) (s : seg) : word :=
  match w with WEnd _ => WEnd s | WAtom _ L a w => WAtom s L a w end.

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
  if sdistb U then
    match linss (map fst L ++ seg_labels U) [] with
    | None => None
    | Some hs =>
        if forallb (fun g => match sfind g U with Some _ => true | None => false end) hs then
          match omap (qent L U) hs, sbuild (map (u'ent L U) hs), lbuild (map (fun g => (g, olp L U g)) hs) with
          | Some qs, Some U', Some L' =>
              match sbuild qs with
              | Some Q => match scomp A Q with Some A' => Some (A', L', U') | None => None end
              | None => None
              end
          | _, _, _ => None
          end
        else None
    end
  else None.

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
  if sdistb s then sset LNone TNil (lcount LNone L) s else None.

Fixpoint pnormf (wc : word -> word -> option word) (pn : option nat -> word -> option word) (w : word) : option word :=
  match w with
  | WEnd s => Some (WEnd (sdrop_none s))
  | WAtom A L a w' =>
      match w' with
      | WEnd s => match pfinal L s with Some s' => settle wc pn A L a (WEnd s') | None => None end
      | _ => match pnormf wc pn w' with Some w'' => settle wc pn A L a w'' | None => None end
      end
  end.

Definition bnormf (wc : word -> word -> option word) (pn : option nat -> word -> option word)
  (b : option nat) (w : word) : option word :=
  match b with None => pnormf wc pn w | Some _ => Some w end.

(** *** The constructors on normal forms *)

Fixpoint wcomp_with (wc : word -> word -> option word) (pn : option nat -> word -> option word) (w1 w2 : word) : option word :=
  match w1 with
  | WEnd A => wcons A w2
  | WAtom A L a w => match wcomp_with wc pn w w2 with Some w' => settle wc pn A L a w' | None => None end
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

Section Normalise.

Variable F : list (lexp * lexp).
Variable ntm : nat.

Fixpoint anorm (e : aexp) : option word :=
  match e with
  | AId => Some (WEnd SNil)
  | AAtom n => Some (WAtom SNil [] n (WEnd SNil))
  | ACompose a b =>
      match anorm a, anorm b with Some wa, Some wb => wcomp F ntm wa wb | _, _ => None end
  | AOuter h a => match anorm a with Some w => wouter F ntm h w | None => None end
  | AInner h t a =>
      match tnorm t, anorm a with Some t', Some w => wpush F ntm h t' w | _, _ => None end
  | ALift h a => match anorm a with Some w => wlift F ntm h w | None => None end
  end
with tnorm (t : texp) : option ntgt :=
  match t with
  | TVarE h i => Some (NVar h i)
  | TBindE u p =>
      if u <? ntm then
        match pnorm_e p with
        | Some (w, b) => match pnormw F ntm b w with Some w' => Some (NBind u w' b) | None => None end
        | None => None
        end
      else None
  | TShiftE h t =>
      match tnorm t with
      | Some (NVar h' i) =>
          match lcmp F h h' with
          | Some Eq => Some (NVar h' (S i))
          | Some _ => Some (NVar h' i)
          | None => None
          end
      | _ => None
      end
  end
with pnorm_e (p : pexp) : option (word * option nat) :=
  match p with
  | PId => Some (WEnd SNil, None)
  | PAtom n => Some (WEnd SNil, Some n)
  | PComp a p =>
      match anorm a, pnorm_e p with
      | Some wa, Some (w, b) => match wcomp F ntm wa w with Some w' => Some (w', b) | None => None end
      | _, _ => None
      end
  | PShift h p =>
      match pnorm_e p with
      | Some (w, b) => match wouter F ntm h w with Some w' => Some (w', b) | None => None end
      | None => None
      end
  end.

(** The decision: both sides normalise to the same normal form. *)
Definition nf_eq (e1 e2 : aexp) : bool :=
  match anorm e1, anorm e2 with Some w1, Some w2 => word_eqb w1 w2 | _, _ => false end.

End Normalise.

(** ** Soundness *)

Section Sound.

Context {T : Type}.
Variable lenv : list label.
Variable tenv : list T.
Variable aenv : list (radj T).
Variable penv : list (rpadj T).
Variable F : list (lexp * lexp).
Hypothesis HF : facts_ok lenv F.
Variable ntm : nat.
Hypothesis Hntm : ntm <= List.length tenv.

Local Notation lden := (lden lenv).
Local Notation tden := (tden lenv tenv aenv penv).
Local Notation sden := (sden lenv tenv aenv penv).
Local Notation wden := (wden lenv tenv aenv penv).
Local Notation sget := (sget lenv).
Local Notation sdist := (sdist lenv).
Local Notation esem := (esem lenv tenv aenv penv).
Local Notation lifts := (lifts lenv).
Local Notation aden := (aden aenv).
Local Notation bden := (bden penv).
Local Notation souts := (@souts T lenv).
Local Notation tins := (tins lenv tenv aenv penv).
Local Notation sins := (sins lenv tenv aenv penv).

(** *** Segments *)

Lemma sdistb_ne h s : sall_ne F h s = true -> sget (lden h) s = None.
Proof.
  induction s as [|h' ts m r IH] using seg_spine; cbn; [reflexivity|].
  destruct (lcmp F h h') as [[]|] eqn:E; try discriminate; intros H;
    (rewrite (proj2 (label_eqb_neq _ _)); [apply IH, H|]);
    intros Heq; apply (lcmp_neq lenv F HF h h' _ E); [discriminate| |discriminate|]; congruence.
Qed.

Lemma sdistb_sound s : sdistb F s = true -> sdist s.
Proof.
  induction s as [|h ts m r IH] using seg_spine; cbn; [constructor|].
  intros H; apply andb_true_iff in H as [H1 H2]; split; [apply sdistb_ne, H1|apply IH, H2].
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
  unfold sset; intros Hd; destruct (sdel F h s) as [s0|] eqn:Ed; [|discriminate].
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

(** Segments with the same entries are the same adjustment. *)
Lemma sden_ext s s' :
  sdist s -> sdist s' -> (forall l j, esem l (sget l s) j = esem l (sget l s') j) -> sden s = sden s'.
Proof.
  intros Hd Hd' H; apply rextensionality; intros v.
  rewrite !rapply_sden by assumption; apply H.
Qed.

(** *** Composition with a segment *)

Definition cres (a : radj T) (r : rresult T) : rresult T :=
  match r with inl w => rapply a w | inr (u, ρ) => inr (u, rpcompose a ρ) end.

Lemma rapply_compose_cres (a b : radj T) v : rapply (rcompose a b) v = cres a (rapply b v).
Proof. rewrite rapply_compose; reflexivity. Qed.

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
  induction w as [s|s L a w IH] using word_spine; cbn [pnorm].
  - apply named_sdrop_none.
  - intros v Hv; rewrite !wden_atom, !rapply_compose_cres, IH by exact Hv; reflexivity.
Qed.

Lemma bnorm_sound b w : rpcompose (wden (bnorm b w)) (bden b) = rpcompose (wden w) (bden b).
Proof.
  destruct b as [n|]; [reflexivity|]; cbn [bnorm bden].
  symmetry; apply rpcompose_named, named_pnorm.
Qed.

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

Lemma sgo_ent S h ts m r :
  sgo F ntm S (SEnt h ts m r)
  = match sgo F ntm S r, tlapp F ntm S ts, sfind F h S with
    | Some R, Some ts', Some e =>
        let '(tsS, mS) := ofe e in
        sset F h (tcat ts' (tskip m tsS)) (if tlen tsS <=? m then m - tlen tsS + mS else mS) R
    | _, _, _ => None
    end.
Proof. reflexivity. Qed.

Lemma wapp_end S U :
  wapp F ntm S (WEnd U) = if sdistb F U then match sgo F ntm S U with Some U' => Some (WEnd U') | None => None end else None.
Proof. reflexivity. Qed.

Lemma wapp_atom S U L a w :
  wapp F ntm S (WAtom U L a w)
  = if sdistb F U then match sgo F ntm S U with Some U' => Some (WAtom U' L a w) | None => None end else None.
Proof. reflexivity. Qed.

Section CompSound.

Variable S : seg.
Hypothesis HS : sdist S.

Lemma comp_sound :
  (forall t t', tapp F ntm S t = Some t' -> rtarget_result (tden t') = cres (sden S) (rtarget_result (tden t)))
  /\ (forall ts ts', tlapp F ntm S ts = Some ts' ->
        tlen ts' = tlen ts
        /\ forall j, j < tlen ts -> rtarget_result (tden (tnth ts' j)) = cres (sden S) (rtarget_result (tden (tnth ts j))))
  /\ (forall U, sdist U -> forall R, sgo F ntm S U = Some R ->
        sdist R /\ forall l j, esem l (sget l R) j = cres (sden S) (esem l (sget l U) j))
  /\ (forall w w', wapp F ntm S w = Some w' -> wden w' = rcompose (sden S) (wden w)).
Proof.
  apply nf_mind.
  - (* NVar *)
    intros h i t'; rewrite tapp_var; destruct (sfind F h S) as [e|] eqn:E; [|discriminate].
    apply sfind_sound in E; subst e; cbn [tden rtarget_result cres].
    rewrite rapply_sden by exact HS; cbn [v_label v_index].
    destruct (sget (lden h) S) as [[ts m]|]; intros H; injection H as <-; cbn [esem]; [|reflexivity].
    destruct (i <? tlen ts); reflexivity.
  - (* NBind *)
    intros u w IH b t'; rewrite tapp_bind; destruct (Nat.ltb_spec u ntm) as [Hu|]; [|discriminate].
    destruct (wapp F ntm S w) as [w'|] eqn:E; [|discriminate]; intros H; injection H as <-.
    destruct (nth_error tenv u) as [x|] eqn:Ex; [|apply nth_error_None in Ex; lia].
    cbn [tden]; rewrite Ex; cbn [rtarget_result cres]; f_equal; f_equal.
    rewrite bnorm_sound, (IH _ eq_refl), rpcompose_compose; reflexivity.
  - (* TNil *)
    intros ts' H; injection H as <-; split; [reflexivity|]; intros j Hj; cbn in Hj; lia.
  - (* TCons *)
    intros t IHt r IHr ts'; rewrite tlapp_cons.
    destruct (tapp F ntm S t) as [t'|] eqn:Et; [|discriminate].
    destruct (tlapp F ntm S r) as [r'|] eqn:Er; [|discriminate]; intros H; injection H as <-.
    destruct (IHr _ eq_refl) as [Hl Hn]; cbn [tlen]; split; [congruence|].
    intros [|j] Hj; cbn [tnth]; [apply IHt; reflexivity|apply Hn; lia].
  - (* SNil *)
    intros _ R H; injection H as <-; split; [exact HS|].
    intros l j; cbn [sget esem cres]; rewrite rapply_sden by exact HS; reflexivity.
  - (* SEnt *)
    intros h ts IHts m r IHr [Hn Hd] R; rewrite sgo_ent.
    destruct (sgo F ntm S r) as [R0|] eqn:ER; [|discriminate].
    destruct (tlapp F ntm S ts) as [ts'|] eqn:Ets; [|discriminate].
    destruct (sfind F h S) as [e|] eqn:Ee; [|discriminate].
    apply sfind_sound in Ee; destruct (IHr Hd _ eq_refl) as [Hd0 Hs0].
    destruct (IHts _ eq_refl) as [Hlen Hts].
    destruct (ofe e) as [tsS mS] eqn:Eo; intros Hset.
    destruct (sset_sound _ _ _ _ _ Hd0 Hset) as [HdR HsR]; split; [exact HdR|].
    intros l j; rewrite HsR; cbn [sget].
    destruct (label_eqb_spec (lden h) l) as [<-|Hne]; [|apply Hs0].
    rewrite !esem_lsem; unfold lsem; rewrite <- !tlen_list, <- !tnth_list, tlen_tcat, tlen_tskip, Hlen.
    destruct (Nat.ltb_spec j (tlen ts)) as [Hj|Hj].
    + rewrite (proj2 (Nat.ltb_lt _ _)) by lia; rewrite tnth_tcat, Hlen, (proj2 (Nat.ltb_lt _ _)) by exact Hj.
      apply Hts, Hj.
    + cbn [cres]; rewrite rapply_sden by exact HS; cbn [v_label v_index]; rewrite <- Ee, <- esem_ofe, Eo.
      cbn [esem]; rewrite tnth_tcat, Hlen, (proj2 (Nat.ltb_ge j (tlen ts)) Hj), tnth_tskip.
      destruct (Nat.ltb_spec (j - tlen ts + m) (tlen tsS)) as [Hk|Hk].
      * rewrite (proj2 (Nat.ltb_lt j (tlen ts + (tlen tsS - m)))) by lia; do 3 f_equal; lia.
      * rewrite (proj2 (Nat.ltb_ge j (tlen ts + (tlen tsS - m)))) by lia; do 2 f_equal.
        destruct (Nat.leb_spec (tlen tsS) m); lia.
  - (* WEnd *)
    intros U IH w'; rewrite wapp_end; destruct (sdistb F U) eqn:Eb; [|discriminate].
    apply sdistb_sound in Eb; destruct (sgo F ntm S U) as [U'|] eqn:E; [|discriminate].
    intros H; injection H as <-; destruct (IH Eb _ eq_refl) as [Hd' Hs].
    rewrite !wden_end; apply rextensionality; intros v.
    rewrite rapply_compose_cres, !rapply_sden by assumption; apply Hs.
  - (* WAtom *)
    intros U IH L a w _ w'; rewrite wapp_atom; destruct (sdistb F U) eqn:Eb; [|discriminate].
    apply sdistb_sound in Eb; destruct (sgo F ntm S U) as [U'|] eqn:E; [|discriminate].
    intros H; injection H as <-; destruct (IH Eb _ eq_refl) as [Hd' Hs].
    rewrite !wden_atom, (rcompose_assoc (sden S)); f_equal.
    apply rextensionality; intros v.
    rewrite rapply_compose_cres, !rapply_sden by assumption; apply Hs.
Qed.

End CompSound.

Lemma scomp_sound A U R : scomp F ntm A U = Some R -> sdist R /\ sden R = rcompose (sden A) (sden U).
Proof.
  unfold scomp; destruct (sdistb F A) eqn:EA, (sdistb F U) eqn:EU; try discriminate; cbn [andb]; intros H.
  apply sdistb_sound in EA, EU.
  destruct (proj1 (proj2 (proj2 (comp_sound A EA))) U EU R H) as [Hd Hs]; split; [exact Hd|].
  apply rextensionality; intros v; rewrite rapply_compose_cres, !rapply_sden by assumption; apply Hs.
Qed.

Lemma wcons_sound A w w' : wcons F ntm A w = Some w' -> wden w' = rcompose (sden A) (wden w).
Proof.
  unfold wcons; destruct (sdistb F A) eqn:EA; [|discriminate]; apply sdistb_sound in EA.
  apply (proj2 (proj2 (proj2 (comp_sound A EA)))).
Qed.

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

Lemma lsub_sound h k L L' (x : radj T) : lsub F h k L = Some L' -> lifts L x = iter k (rlift (lden h)) (lifts L' x).
Proof.
  revert L'; induction L as [|[h' n'] L IH]; intros L'; cbn [lsub]; [discriminate|].
  destruct (lcmp F h h') as [c|] eqn:E; [|discriminate]; assert (Hc := E).
  apply (lcmp_sound lenv F HF) in Hc; destruct c; cbn in Hc.
  - subst h'; destruct (Nat.leb_spec k n') as [Hk|]; [|discriminate]; intros H; injection H as <-.
    destruct (Nat.eqb_spec n' k) as [->|Hne]; [reflexivity|].
    rewrite !lifts_cons, <- iter_add; f_equal; lia.
  - destruct (lsub F h k L) as [L''|] eqn:EL; [|discriminate]; intros H; injection H as <-.
    rewrite !lifts_cons, (IH _ eq_refl), iter_rlift_comm; [reflexivity|].
    intros Heq; rewrite Heq in Hc; exact (olabel_lt_irrefl _ Hc).
  - destruct (lsub F h k L) as [L''|] eqn:EL; [|discriminate]; intros H; injection H as <-.
    rewrite !lifts_cons, (IH _ eq_refl), iter_rlift_comm; [reflexivity|].
    intros Heq; rewrite Heq in Hc; exact (olabel_lt_irrefl _ Hc).
Qed.

(** *** Settling *)

Definition shiftk (h : option label) (k : nat) : radj T := iter k (rpush_outer h) ridentity.

Lemma sden_shseg h k : sden (shseg h k) = shiftk (lden h) k.
Proof. reflexivity. Qed.

Lemma sfront_sound h t s s' :
  sfront F h t s = Some s' -> sdist s' /\ sden s' = rpush_inner (lden h) (tden t) (sden s).
Proof.
  unfold sfront; destruct (sdistb F s) eqn:Ed; [|discriminate]; apply sdistb_sound in Ed.
  destruct (sfind F h s) as [e|] eqn:Ef; [|discriminate]; apply sfind_sound in Ef.
  destruct (ofe e) as [ts m] eqn:Eo; intros H.
  destruct (sset_sound _ _ _ _ _ Ed H) as [Hd' Hs]; split; [exact Hd'|].
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

Lemma slift_sound h s s' : slift F ntm h s = Some s' -> sden s' = rlift (lden h) (sden s).
Proof.
  unfold slift; destruct (scomp F ntm (shseg h 1) s) as [s1|] eqn:E; [|discriminate]; intros H.
  rewrite (proj2 (sfront_sound _ _ _ _ H)), (proj2 (scomp_sound _ _ _ E)), sden_shseg.
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

Lemma iter_rlift_fix l k : forall j (x : radj T), j < k -> rapply (iter k (rlift l) x) (mk_rvar l j) = inl (mk_rvar l j).
Proof.
  induction k as [|k IH]; intros j x Hj; [lia|]; cbn [iter]; rewrite rapply_lift.
  destruct j as [|j]; [rewrite rvar_eqb_refl; reflexivity|].
  destruct (rvar_eqb_spec (mk_rvar l (S j)) (mk_rvar l 0)) as [E|_]; [injection E; discriminate|].
  replace (unshift_rvar (mk_rvar l 0) (mk_rvar l (S j))) with (mk_rvar l j)
    by (unfold unshift_rvar; cbn [v_label v_index]; rewrite label_eqb_refl; cbn; f_equal; lia).
  rewrite IH by lia; unfold shift_rvar; cbn [v_label v_index]; rewrite label_eqb_refl; cbn; f_equal; f_equal; lia.
Qed.

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

Variable wc : word -> word -> option word.
Hypothesis Hwc : forall w1 w2 w, wc w1 w2 = Some w -> wden w = rcompose (wden w1) (wden w2).
Variable pn : option nat -> word -> option word.
Hypothesis Hpn : forall b w w', pn b w = Some w' -> rpcompose (wden w') (bden b) = rpcompose (wden w) (bden b).
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
        rewrite (Hpn _ _ _ Ep'), (Hwc _ _ _ Ew), rpcompose_compose, wden_atom, wden_end.
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

Theorem settle1_sound wc (Hwc : forall w1 w2 w, wc w1 w2 = Some w -> wden w = rcompose (wden w1) (wden w2))
  pn (Hpn : forall b w w', pn b w = Some w' -> rpcompose (wden w') (bden b) = rpcompose (wden w) (bden b))
  a A L U A' L' U' rest :
  settle1 F ntm wc pn a A L U = Some (A', L', U') ->
  rcompose (sden A') (rcompose (lifts L' (aden a)) (rcompose (sden U') rest))
  = rcompose (sden A) (rcompose (lifts L (aden a)) (rcompose (sden U) rest)).
Proof.
  unfold settle1; destruct (sdistb F U) eqn:Ed; [|discriminate]; apply sdistb_sound in Ed.
  destruct (linss F (map fst L ++ seg_labels U) []) as [hs|] eqn:Eh; [|discriminate].
  destruct (linss_spec _ _ _ Eh) as [Hin Hdist].
  assert (Hd : ldist hs) by (apply Hdist; intros x y []).
  assert (Hn : NoDup hs) by (apply (linss_nodup _ _ _ Eh); constructor).
  assert (HL : forall k, In k (map fst L) -> In k hs) by (intros k Hk; apply Hin; left; apply in_or_app; left; exact Hk).
  assert (HU : forall k, In k (seg_labels U) -> In k hs) by (intros k Hk; apply Hin; left; apply in_or_app; right; exact Hk).
  destruct (forallb _ hs) eqn:Ef; [|discriminate].
  assert (Hf : forall g, In g hs -> exists e, sfind F g U = Some e).
  { intros g Hg; apply (proj1 (forallb_forall _ _) Ef) in Hg; destruct (sfind F g U) as [e|]; [exists e; reflexivity|discriminate]. }
  destruct (omap (qent F ntm wc pn a L U) hs) as [qs|] eqn:Eq; [|discriminate].
  destruct (sbuild F (map (u'ent F L U) hs)) as [U1|] eqn:EU; [|discriminate].
  destruct (lbuild F (map (fun g => (g, olp F L U g)) hs)) as [L1|] eqn:EL; [|discriminate].
  destruct (sbuild F qs) as [Q|] eqn:EQ; [|discriminate].
  destruct (scomp F ntm A Q) as [A1|] eqn:EA; [|discriminate].
  intros H; injection H as <- <- <-.
  rewrite (proj2 (scomp_sound _ _ _ EA)), (lbuild_sound _ _ _ EL).
  pose proof (one_core L U hs Ed Hd Hn HL HU Hf wc Hwc pn Hpn a qs Q U1 (omap_f2 _ _ _ Eq) EQ EU) as Hc.
  rewrite (rcompose_assoc (lifts L (aden a))), Hc, <- !rcompose_assoc; reflexivity.
Qed.

Definition wrest (w : word) : radj T :=
  match w with WEnd _ => ridentity | WAtom _ L a w => rcompose (lifts L (aden a)) (wden w) end.

Lemma wden_head w : wden w = rcompose (sden (whead w)) (wrest w).
Proof. destruct w; cbn [whead wrest]; [rewrite wden_end, rcompose_identity_r|rewrite wden_atom]; reflexivity. Qed.

Lemma wden_sethead w U : wden (wsethead w U) = rcompose (sden U) (wrest w).
Proof. destruct w; cbn [wsethead wrest]; [rewrite wden_end, rcompose_identity_r|rewrite wden_atom]; reflexivity. Qed.

Lemma settle_sound wc (Hwc : forall w1 w2 w, wc w1 w2 = Some w -> wden w = rcompose (wden w1) (wden w2))
  pn (Hpn : forall b w w', pn b w = Some w' -> rpcompose (wden w') (bden b) = rpcompose (wden w) (bden b)) A L a w w' :
  settle F ntm wc pn A L a w = Some w' -> wden w' = rcompose (sden A) (rcompose (lifts L (aden a)) (wden w)).
Proof.
  unfold settle; destruct (settle1 F ntm wc pn a A L (whead w)) as [[[A' L'] U']|] eqn:E; [|discriminate].
  intros H; injection H as <-.
  rewrite wden_atom, wden_sethead, (settle1_sound _ Hwc _ Hpn _ _ _ _ _ _ _ _ E), <- (wden_head w); reflexivity.
Qed.

(** *** The constructors *)

Lemma named_compose_l (Y X X' : radj T) : named_eq X X' -> named_eq (rcompose Y X) (rcompose Y X').
Proof. intros H v Hv; rewrite !rapply_compose_cres, (H v Hv); reflexivity. Qed.

Lemma pnormf_sound wc (Hwc : forall w1 w2 w, wc w1 w2 = Some w -> wden w = rcompose (wden w1) (wden w2))
  pn (Hpn : forall b w w', pn b w = Some w' -> rpcompose (wden w') (bden b) = rpcompose (wden w) (bden b)) :
  forall w w', pnormf F ntm wc pn w = Some w' -> named_eq (wden w) (wden w').
Proof.
  induction w as [s|A L a w IH] using word_spine; cbn [pnormf].
  - intros w' H; injection H as <-; rewrite !wden_end; apply named_sdrop_none.
  - intros w0; destruct w as [s|A' L' a' w1].
    + unfold pfinal; destruct (sdistb F s) eqn:Ed; [|discriminate]; apply sdistb_sound in Ed.
      destruct (sset F LNone TNil (lcount LNone L) s) as [s'|] eqn:Es; [|discriminate]; intros H.
      rewrite (settle_sound _ Hwc _ Hpn _ _ _ _ _ H), wden_atom.
      apply named_compose_l, named_compose_l; rewrite !wden_end.
      intros [l j] Hl; rewrite !rapply_sden by first [exact Ed|exact (proj1 (sset_sound _ _ _ _ _ Ed Es))].
      cbn [v_label v_index]; rewrite (proj2 (sset_sound _ _ _ _ _ Ed Es)); cbn [lden].
      destruct l; [reflexivity|contradiction].
    + destruct (pnormf F ntm wc pn (WAtom A' L' a' w1)) as [w''|] eqn:E; [|discriminate]; intros H.
      rewrite (settle_sound _ Hwc _ Hpn _ _ _ _ _ H), wden_atom.
      apply named_compose_l, named_compose_l, (IH _ eq_refl).
Qed.

Lemma wops_sound n :
  (forall w1 w2 w, fst (wops F ntm n) w1 w2 = Some w -> wden w = rcompose (wden w1) (wden w2))
  /\ (forall b w w', snd (wops F ntm n) b w = Some w' -> rpcompose (wden w') (bden b) = rpcompose (wden w) (bden b)).
Proof.
  induction n as [|n [IHc IHp]]; [split; discriminate|]; cbn [wops].
  destruct (wops F ntm n) as [wc pn] eqn:Ew; cbn [fst snd] in *; split.
  - intros w1; induction w1 as [A|A L a w1 IH] using word_spine; intros w2 w; cbn [wcomp_with].
    + intros H; rewrite (wcons_sound _ _ _ H); reflexivity.
    + destruct (wcomp_with F ntm wc pn w1 w2) as [w'|] eqn:E; [|discriminate]; intros H.
      rewrite (settle_sound _ IHc _ IHp _ _ _ _ _ H), (IH _ _ E), wden_atom, !rcompose_assoc; reflexivity.
  - intros [m|] w w' H; cbn [bnormf] in H; [injection H as <-; reflexivity|].
    symmetry; apply rpcompose_named, (pnormf_sound _ IHc _ IHp _ _ H).
Qed.

Lemma wcomp_sound w1 w2 w : wcomp F ntm w1 w2 = Some w -> wden w = rcompose (wden w1) (wden w2).
Proof. apply (proj1 (wops_sound 64)). Qed.

Lemma pnormw_sound b w w' : pnormw F ntm b w = Some w' -> rpcompose (wden w') (bden b) = rpcompose (wden w) (bden b).
Proof. apply (proj2 (wops_sound 64)). Qed.

Lemma wlift_sound h w w' : wlift F ntm h w = Some w' -> wden w' = rlift (lden h) (wden w).
Proof.
  revert w'; induction w as [s|s L a w IH] using word_spine; intros w'; cbn [wlift].
  - destruct (slift F ntm h s) as [s'|] eqn:E; [|discriminate]; intros H; injection H as <-.
    rewrite !wden_end; apply (slift_sound _ _ _ E).
  - destruct (slift F ntm h s) as [s'|] eqn:Es; [|discriminate].
    destruct (ladd F h 1 L) as [L'|] eqn:EL; [|discriminate].
    destruct (wlift F ntm h w) as [w1|] eqn:Ew; [|discriminate]; intros H; injection H as <-.
    rewrite !wden_atom, (slift_sound _ _ _ Es), (ladd_sound _ _ _ _ _ EL), (IH _ eq_refl); cbn [iter].
    rewrite !rlift_compose; reflexivity.
Qed.

Lemma wpush_sound h t w w' : wpush F ntm h t w = Some w' -> wden w' = rpush_inner (lden h) (tden t) (wden w).
Proof.
  destruct w as [s|s L a w]; cbn [wpush].
  - destruct (sfront F h t s) as [s'|] eqn:E; [|discriminate]; intros H; injection H as <-.
    rewrite !wden_end; apply (proj2 (sfront_sound _ _ _ _ E)).
  - destruct (sfront F h t s) as [s'|] eqn:Es; [|discriminate].
    destruct (ladd F h 1 L) as [L'|] eqn:EL; [|discriminate].
    destruct (wlift F ntm h w) as [w1|] eqn:Ew; [|discriminate]; intros H; injection H as <-.
    rewrite !wden_atom, (proj2 (sfront_sound _ _ _ _ Es)), (ladd_sound _ _ _ _ _ EL), (wlift_sound _ _ _ Ew).
    cbn [iter]; rewrite rpush_inner_compose, rlift_compose; reflexivity.
Qed.

Lemma wouter_sound h w w' : wouter F ntm h w = Some w' -> wden w' = rpush_outer (lden h) (wden w).
Proof.
  unfold wouter; intros H; rewrite (wcons_sound _ _ _ H), sden_shseg.
  unfold shiftk; cbn [iter]; apply rcompose_identity_push_outer.
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

Lemma anorm_compose a b :
  anorm F ntm (ACompose a b) = match anorm F ntm a, anorm F ntm b with Some wa, Some wb => wcomp F ntm wa wb | _, _ => None end.
Proof. reflexivity. Qed.

Lemma anorm_outer h a : anorm F ntm (AOuter h a) = match anorm F ntm a with Some w => wouter F ntm h w | None => None end.
Proof. reflexivity. Qed.

Lemma anorm_inner h t a :
  anorm F ntm (AInner h t a) = match tnorm F ntm t, anorm F ntm a with Some t', Some w => wpush F ntm h t' w | _, _ => None end.
Proof. reflexivity. Qed.

Lemma anorm_lift h a : anorm F ntm (ALift h a) = match anorm F ntm a with Some w => wlift F ntm h w | None => None end.
Proof. reflexivity. Qed.

Lemma tnorm_bind u p :
  tnorm F ntm (TBindE u p)
  = if u <? ntm then
      match pnorm_e F ntm p with
      | Some (w, b) => match pnormw F ntm b w with Some w' => Some (NBind u w' b) | None => None end
      | None => None
      end
    else None.
Proof. reflexivity. Qed.

Lemma tnorm_shift h t :
  tnorm F ntm (TShiftE h t)
  = match tnorm F ntm t with
    | Some (NVar h' i) =>
        match lcmp F h h' with Some Eq => Some (NVar h' (S i)) | Some _ => Some (NVar h' i) | None => None end
    | _ => None
    end.
Proof. reflexivity. Qed.

Lemma pnorm_comp a p :
  pnorm_e F ntm (PComp a p)
  = match anorm F ntm a, pnorm_e F ntm p with
    | Some wa, Some (w, b) => match wcomp F ntm wa w with Some w' => Some (w', b) | None => None end
    | _, _ => None
    end.
Proof. reflexivity. Qed.

Lemma pnorm_shift h p :
  pnorm_e F ntm (PShift h p)
  = match pnorm_e F ntm p with
    | Some (w, b) => match wouter F ntm h w with Some w' => Some (w', b) | None => None end
    | None => None
    end.
Proof. reflexivity. Qed.

Lemma wden_id : wden (WEnd SNil) = ridentity.
Proof. reflexivity. Qed.

Theorem anorm_sound :
  (forall e w, anorm F ntm e = Some w -> wden w = aeden e)
  /\ (forall t t', tnorm F ntm t = Some t' -> tden t' = teden t)
  /\ (forall p w b, pnorm_e F ntm p = Some (w, b) -> rpcompose (wden w) (bden b) = peden p).
Proof.
  apply exp_mind; cbn [aeden teden peden].
  - intros w H; injection H as <-; reflexivity.
  - intros n w H; injection H as <-; rewrite wden_atom, wden_id, rcompose_identity_r.
    change (sden SNil) with (@ridentity T); apply rcompose_identity_l.
  - intros a IHa b IHb w; rewrite anorm_compose.
    destruct (anorm F ntm a) as [wa|] eqn:Ea; [|discriminate].
    destruct (anorm F ntm b) as [wb|] eqn:Eb; [|discriminate]; intros H.
    rewrite (wcomp_sound _ _ _ H), (IHa _ eq_refl), (IHb _ eq_refl); reflexivity.
  - intros h a IH w; rewrite anorm_outer; destruct (anorm F ntm a) as [wa|] eqn:Ea; [|discriminate]; intros H.
    rewrite (wouter_sound _ _ _ H), (IH _ eq_refl); reflexivity.
  - intros h t IHt a IHa w; rewrite anorm_inner.
    destruct (tnorm F ntm t) as [t'|] eqn:Et; [|discriminate].
    destruct (anorm F ntm a) as [wa|] eqn:Ea; [|discriminate]; intros H.
    rewrite (wpush_sound _ _ _ _ H), (IHt _ eq_refl), (IHa _ eq_refl); reflexivity.
  - intros h a IH w; rewrite anorm_lift; destruct (anorm F ntm a) as [wa|] eqn:Ea; [|discriminate]; intros H.
    rewrite (wlift_sound _ _ _ H), (IH _ eq_refl); reflexivity.
  - intros h i t' H; injection H as <-; reflexivity.
  - intros u p IH t'; rewrite tnorm_bind; destruct (Nat.ltb_spec u ntm) as [Hu|]; [|discriminate].
    destruct (pnorm_e F ntm p) as [[w b]|] eqn:Ep; [|discriminate].
    destruct (pnormw F ntm b w) as [w'|] eqn:Ew; [|discriminate]; intros H; injection H as <-.
    destruct (nth_error tenv u) as [x|] eqn:Ex; [|apply nth_error_None in Ex; lia].
    rewrite (tden_bind _ _ _ _ Ex), (pnormw_sound _ _ _ Ew); rewrite (IH _ _ eq_refl); reflexivity.
  - intros h t IH t'; rewrite tnorm_shift.
    destruct (tnorm F ntm t) as [[h' i|]|] eqn:Et; try discriminate.
    rewrite <- (IH _ eq_refl); cbn [tden].
    destruct (lcmp F h h') as [c|] eqn:Ec; [|discriminate].
    apply (lcmp_sound lenv F HF) in Ec; destruct c; intros H; injection H as <-;
      unfold shift_rvar; cbn [v_label v_index tden]; cbn in Ec.
    + subst h'; rewrite label_eqb_refl; reflexivity.
    + rewrite (proj2 (label_eqb_neq _ _)); [reflexivity|].
      intros E; rewrite E in Ec; exact (olabel_lt_irrefl _ Ec).
    + rewrite (proj2 (label_eqb_neq _ _)); [reflexivity|].
      intros E; rewrite E in Ec; exact (olabel_lt_irrefl _ Ec).
  - intros w b H; injection H as <- <-; rewrite wden_id; apply rpcompose_identity.
  - intros n w b H; injection H as <- <-; rewrite wden_id; apply rpcompose_identity.
  - intros a IHa p IHp w b; rewrite pnorm_comp.
    destruct (anorm F ntm a) as [wa|] eqn:Ea; [|discriminate].
    destruct (pnorm_e F ntm p) as [[w0 b0]|] eqn:Ep; [|discriminate].
    destruct (wcomp F ntm wa w0) as [w'|] eqn:Ew; [|discriminate]; intros H; injection H as <- <-.
    rewrite (wcomp_sound _ _ _ Ew), <- rpcompose_compose, (IHp _ _ eq_refl), (IHa _ eq_refl); reflexivity.
  - intros h p IH w b; rewrite pnorm_shift.
    destruct (pnorm_e F ntm p) as [[w0 b0]|] eqn:Ep; [|discriminate].
    destruct (wouter F ntm h w0) as [w'|] eqn:Ew; [|discriminate]; intros H; injection H as <- <-.
    rewrite (wouter_sound _ _ _ Ew), rpush_outer_as_compose, <- rpcompose_compose, (IH _ _ eq_refl).
    symmetry; apply rpshift_as_pcompose.
Qed.

Theorem nf_eq_sound e1 e2 : nf_eq F ntm e1 e2 = true -> aeden e1 = aeden e2.
Proof.
  unfold nf_eq; destruct (anorm F ntm e1) as [w1|] eqn:E1; [|discriminate].
  destruct (anorm F ntm e2) as [w2|] eqn:E2; [|discriminate]; intros H.
  apply (proj2 (proj2 (proj2 nf_eqb_eq))) in H; subst w2.
  rewrite <- (proj1 anorm_sound _ _ E1), <- (proj1 anorm_sound _ _ E2); reflexivity.
Qed.

(** *** Applying a single segment to a variable *)

Definition seg_tgt (F : list (lexp * lexp)) (Sg : seg) (h : lexp) (i : nat) : option ntgt :=
  if sdistb F Sg then
    match sfind F h Sg with
    | Some None => Some (NVar h i)
    | Some (Some (ts, m)) => Some (if i <? tlen ts then tnth ts i else NVar h (i - tlen ts + m))
    | None => None
    end
  else None.

(** Where a word sends a variable, from the right: past each lifted atom
    only when the lifts pass it through; a term only from the outermost
    segment. *)
Fixpoint wtgt (F : list (lexp * lexp)) (w : word) (h : lexp) (i : nat) : option ntgt :=
  match w with
  | WEnd Sg => seg_tgt F Sg h i
  | WAtom Sg L a w =>
      match wtgt F w h i with
      | Some (NVar h' j) => match lsub F h' (S j) L with Some _ => seg_tgt F Sg h' j | None => None end
      | _ => None
      end
  end.

Definition apply_result (F : list (lexp * lexp)) (ntm : nat) (e : aexp) (h : lexp) (i : nat) : option (lexp * nat) :=
  match anorm F ntm e with
  | Some w => match wtgt F w h i with Some (NVar h' j) => Some (h', j) | _ => None end
  | None => None
  end.

(** A variable sent to a term with the identity payload adjustment after
    [w]: the term and [w], for [names] to show [w]. *)
Definition apply_payload (F : list (lexp * lexp)) (ntm : nat) (e : aexp) (h : lexp) (i : nat) : option (nat * word) :=
  match anorm F ntm e with
  | Some w => match wtgt F w h i with Some (NBind u wp None) => Some (u, wp) | _ => None end
  | None => None
  end.

(** ... checked against the reified adjustment [eb] it was shown as. *)
Definition apply_bind_check (F : list (lexp * lexp)) (ntm : nat) (e : aexp) (h : lexp) (i : nat) (eb : aexp) : option nat :=
  match apply_payload F ntm e h i, anorm F ntm eb with
  | Some (u, wp), Some wb =>
      match pnormw F ntm None wp, pnormw F ntm None wb with
      | Some w1, Some w2 => if word_eqb w1 w2 then Some u else None
      | _, _ => None
      end
  | _, _ => None
  end.

Lemma seg_tgt_sound Sg h i t :
  seg_tgt F Sg h i = Some t -> rapply (sden Sg) (mk_rvar (lden h) i) = rtarget_result (tden t).
Proof.
  unfold seg_tgt; destruct (sdistb F Sg) eqn:Ed; [|discriminate]; apply sdistb_sound in Ed.
  destruct (sfind F h Sg) as [r|] eqn:Ef; [|discriminate]; apply sfind_sound in Ef.
  rewrite rapply_sden by exact Ed; cbn [v_label v_index].
  rewrite <- Ef; destruct r as [[ts m]|]; cbn [esem]; intros H; injection H as <-.
  - destruct (i <? tlen ts); reflexivity.
  - reflexivity.
Qed.

Lemma wtgt_sound w h i t :
  wtgt F w h i = Some t -> rapply (wden w) (mk_rvar (lden h) i) = rtarget_result (tden t).
Proof.
  revert t; induction w as [Sg|Sg L a w IH] using word_spine; intros t; cbn [wtgt].
  - rewrite wden_end; apply seg_tgt_sound.
  - destruct (wtgt F w h i) as [[h1 j1|]|] eqn:E; try discriminate.
    destruct (lsub F h1 (S j1) L) as [L0|] eqn:EL; [|discriminate]; intros H.
    rewrite wden_atom, !rapply_compose_cres, (IH _ eq_refl); cbn [tden rtarget_result cres].
    rewrite (lsub_sound _ _ _ _ (aden a) EL), iter_rlift_fix by lia; cbn [cres].
    exact (seg_tgt_sound _ _ _ _ H).
Qed.

Theorem apply_result_sound e h i h' j :
  apply_result F ntm e h i = Some (h', j) ->
  rapply (aeden e) (mk_rvar (lden h) i) = inl (mk_rvar (lden h') j).
Proof.
  unfold apply_result; destruct (anorm F ntm e) as [w|] eqn:E; [|discriminate].
  destruct (wtgt F w h i) as [[h1 j1|]|] eqn:Et; try discriminate; intros H; injection H as <- <-.
  rewrite <- (proj1 anorm_sound _ _ E), (wtgt_sound _ _ _ _ Et); reflexivity.
Qed.

Theorem apply_bind_sound e h i eb u x :
  apply_bind_check F ntm e h i eb = Some u -> nth_error tenv u = Some x ->
  rapply (aeden e) (mk_rvar (lden h) i) = inr (x, rpcompose (aeden eb) rpidentity).
Proof.
  unfold apply_bind_check, apply_payload; destruct (anorm F ntm e) as [w|] eqn:E; [|discriminate].
  destruct (wtgt F w h i) as [[|u0 wp [b|]]|] eqn:Et; try discriminate.
  destruct (anorm F ntm eb) as [wb|] eqn:Eb; [|discriminate].
  destruct (pnormw F ntm None wp) as [w1|] eqn:E1; [|discriminate].
  destruct (pnormw F ntm None wb) as [w2|] eqn:E2; [|discriminate].
  destruct (word_eqb w1 w2) eqn:Ew; [|discriminate]; intros H; injection H as <-; intros Hx.
  apply (proj2 (proj2 (proj2 nf_eqb_eq))) in Ew; subst w2.
  rewrite <- (proj1 anorm_sound _ _ E), (wtgt_sound _ _ _ _ Et), (tden_bind _ _ _ _ Hx); cbn [rtarget_result].
  rewrite <- (proj1 anorm_sound _ _ Eb).
  rewrite <- (pnormw_sound None wp w1 E1).
  change (@rpidentity T) with (bden None); rewrite <- (pnormw_sound None wb w1 E2); reflexivity.
Qed.

(** *** Materialised payloads

    Two segments that are the same except that, where the first sends a
    variable to a term [u⟨w⟩], the second sends it to a term atom [k] with
    the identity payload adjustment, where [k] is [u] with the payload
    adjustment applied ([facts], checked against the reified adjustment
    the payload was shown as). *)
Fixpoint mfind (facts : list (nat * nat * aexp)) (k : nat) : option (nat * aexp) :=
  match facts with
  | [] => None
  | (k', u, eb) :: r => if Nat.eqb k k' then Some (u, eb) else mfind r k
  end.

Definition tmat (F : list (lexp * lexp)) (ntm : nat) (facts : list (nat * nat * aexp)) (t t' : ntgt) : bool :=
  ntgt_eqb t t'
  || match t, t' with
     | NBind u wp None, NBind k (WEnd SNil) None =>
         match mfind facts k with
         | Some (u', eb) =>
             Nat.eqb u u' && (u <? ntm) && (k <? ntm)
             && match anorm F ntm eb with
                | Some wb =>
                    match pnormw F ntm None wp, pnormw F ntm None wb with
                    | Some w1, Some w2 => word_eqb w1 w2
                    | _, _ => false
                    end
                | None => false
                end
         | None => false
         end
     | _, _ => false
     end.

Fixpoint tlmat F ntm facts (ts ts' : tlist) : bool :=
  match ts, ts' with
  | TNil, TNil => true
  | TCons t r, TCons t' r' => tmat F ntm facts t t' && tlmat F ntm facts r r'
  | _, _ => false
  end.

Fixpoint smat F ntm facts (s s' : seg) : bool :=
  match s, s' with
  | SNil, SNil => true
  | SEnt h ts m r, SEnt h' ts' m' r' =>
      lexp_eqb h h' && tlmat F ntm facts ts ts' && Nat.eqb m m' && smat F ntm facts r r'
  | _, _ => false
  end.

Definition mat_eqb (F : list (lexp * lexp)) (ntm : nat) (facts : list (nat * nat * aexp)) (e e' : aexp) : bool :=
  match anorm F ntm e, anorm F ntm e' with
  | Some (WEnd S1), Some (WEnd S2) => sdistb F S1 && sdistb F S2 && smat F ntm facts S1 S2
  | _, _ => false
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

Lemma tmat_sound t t' : tmat F ntm facts t t' = true -> mrel (rtarget_result (tden t)) (rtarget_result (tden t')).
Proof.
  unfold tmat; destruct (ntgt_eqb t t') eqn:E; cbn [orb].
  { intros _; left; apply (proj1 nf_eqb_eq) in E; subst; reflexivity. }
  destruct t as [|u wp [b|]]; try discriminate; destruct t' as [|k [[|]|] [b'|]]; try discriminate.
  destruct (mfind facts k) as [[u' eb]|] eqn:Ef; [|discriminate].
  destruct (Nat.eqb u u') eqn:Eu; [|discriminate]; apply Nat.eqb_eq in Eu; subst u'.
  destruct (u <? ntm) eqn:Hu; [|discriminate]; destruct (k <? ntm) eqn:Hk; [|discriminate].
  apply Nat.ltb_lt in Hu, Hk; cbn [andb].
  destruct (anorm F ntm eb) as [wb|] eqn:Eb; [|discriminate].
  destruct (pnormw F ntm None wp) as [w1|] eqn:E1; [|discriminate].
  destruct (pnormw F ntm None wb) as [w2|] eqn:E2; [|discriminate].
  intros Ew; apply (proj2 (proj2 (proj2 nf_eqb_eq))) in Ew; subst w2.
  destruct (nth_error tenv u) as [y|] eqn:Ey; [|apply nth_error_None in Ey; lia].
  right; exists y, (rpcompose (wden wp) rpidentity).
  rewrite (tden_bind _ _ _ _ Ey), (tden_bind _ _ _ _ (mfind_fact _ _ _ _ Ef Ey)); cbn [rtarget_result]; split; [reflexivity|].
  rewrite wden_end; change (sden SNil) with (@ridentity T); rewrite rpcompose_identity.
  do 3 f_equal; change (bden None) with (@rpidentity T).
  change (rpcompose (aeden eb) (bden None) = rpcompose (wden wp) (bden None)).
  rewrite <- (proj1 anorm_sound _ _ Eb), <- (pnormw_sound None wp w1 E1), <- (pnormw_sound None wb w1 E2); reflexivity.
Qed.

Lemma tlmat_len ts ts' : tlmat F ntm facts ts ts' = true -> tlen ts = tlen ts'.
Proof.
  revert ts'; induction ts as [|t r IH] using tlist_spine; intros [|t' r']; cbn; try discriminate; [reflexivity|].
  intros H; apply andb_true_iff in H as [_ H]; rewrite (IH _ H); reflexivity.
Qed.

Lemma tlmat_nth ts ts' j : tlmat F ntm facts ts ts' = true -> j < tlen ts -> tmat F ntm facts (tnth ts j) (tnth ts' j) = true.
Proof.
  revert ts' j; induction ts as [|t r IH] using tlist_spine; intros [|t' r'] j; cbn; try discriminate; [lia|].
  intros H Hj; apply andb_true_iff in H as [H1 H2]; destruct j; [exact H1|apply IH; [exact H2|lia]].
Qed.

Lemma smat_get s s' l : smat F ntm facts s s' = true ->
  match sget l s, sget l s' with
  | Some (ts, m), Some (ts', m') => tlmat F ntm facts ts ts' = true /\ m = m'
  | None, None => True
  | _, _ => False
  end.
Proof.
  revert s'; induction s as [|h ts m r IH] using seg_spine; intros [|h' ts' m' r']; cbn [smat]; try discriminate; [cbn; tauto|].
  intros H; apply andb_true_iff in H as [H H4]; apply andb_true_iff in H as [H H3]; apply andb_true_iff in H as [H1 H2].
  apply lexp_eqb_eq in H1; apply Nat.eqb_eq in H3; subst h' m'; cbn [sget].
  destruct (label_eqb (lden h) l); [split; [exact H2|reflexivity]|apply IH, H4].
Qed.

Theorem mat_sound e e' : mat_eqb F ntm facts e e' = true -> forall v, mrel (rapply (aeden e) v) (rapply (aeden e') v).
Proof.
  unfold mat_eqb; destruct (anorm F ntm e) as [[S1|]|] eqn:E; try discriminate.
  destruct (anorm F ntm e') as [[S2|]|] eqn:E'; try discriminate.
  intros H; apply andb_true_iff in H as [H Hm]; apply andb_true_iff in H as [Hd Hd'].
  apply sdistb_sound in Hd, Hd'; intros [l j].
  rewrite <- (proj1 anorm_sound _ _ E), <- (proj1 anorm_sound _ _ E'), !wden_end, !rapply_sden by assumption.
  cbn [v_label v_index]; pose proof (smat_get _ _ l Hm) as Hg.
  destruct (sget l S1) as [[ts m]|], (sget l S2) as [[ts' m']|]; try contradiction; [|left; reflexivity].
  destruct Hg as [Ht <-]; cbn [esem]; rewrite <- (tlmat_len _ _ Ht).
  destruct (j <? tlen ts) eqn:Ej; [|left; reflexivity].
  apply tmat_sound, tlmat_nth; [exact Ht|apply Nat.ltb_lt, Ej].
Qed.

End Mat.

End Sound.
