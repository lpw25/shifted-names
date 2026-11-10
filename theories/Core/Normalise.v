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

    Two adjacent segments are always composed into one.  Where an atom
    lifted by [h] is followed by a segment that skips [h₍₀₎], the shift
    moves out to the left ([⇑ₕσ ∘ shiftₕ = shiftₕ ∘ σ]), so the segment to
    the right of a lift by [h] always reaches [h₍₀₎].

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

(** *** Settling a lifted atom against the segment to its right

    [⇑ₕᵏσ ∘ shiftₕᵏ = shiftₕᵏ ∘ σ]: when the segment [U] to the right of an
    atom lifted [k] times by [h] is [shiftₕᵏ ∘ U'], the shift moves to the
    segment [S] on the left.  The largest such [k] is found by trying: [U']
    is [unshiftₕᵏ ∘ U], checked by composing back. *)

Definition shseg (h : lexp) (k : nat) : seg := SEnt h TNil k SNil.
Definition unseg (h : lexp) (k : nat) : seg := SEnt h (tl_of (repeat (NVar h 0) k)) 0 SNil.

Fixpoint try_unshift (h : lexp) (U : seg) (k : nat) : option (nat * seg) :=
  match k with
  | 0 => None
  | S k' =>
      match scomp (unseg h k) U with
      | Some U' =>
          match scomp (shseg h k) U' with
          | Some U2 => if seg_eqb U2 U then Some (k, U') else try_unshift h U k'
          | None => try_unshift h U k'
          end
      | None => try_unshift h U k'
      end
  end.

Definition settle1 (h : lexp) (st : seg * list (lexp * nat) * seg) : option (seg * list (lexp * nat) * seg) :=
  let '(A, L, U) := st in
  match try_unshift h U (lcount h L) with
  | None => Some st
  | Some (k, U') =>
      match scomp A (shseg h k), lsub h k L with
      | Some A', Some L' => Some (A', L', U')
      | _, _ => None
      end
  end.

Fixpoint settle_all (hs : list lexp) (st : seg * list (lexp * nat) * seg) : option (seg * list (lexp * nat) * seg) :=
  match hs with
  | [] => Some st
  | h :: hs => match settle1 h st with Some st' => settle_all hs st' | None => None end
  end.

Definition whead (w : word) : seg := match w with WEnd s | WAtom s _ _ _ => s end.

Definition wsethead (w : word) (s : seg) : word :=
  match w with WEnd _ => WEnd s | WAtom _ L a w => WAtom s L a w end.

(** [S ∘ ⇑ᴸσ ∘ w], settled. *)
Definition settle (A : seg) (L : list (lexp * nat)) (a : nat) (w : word) : option word :=
  match settle_all (map fst L) (A, L, whead w) with
  | Some (A', L', U') => Some (WAtom A' L' a (wsethead w U'))
  | None => None
  end.

(** *** The constructors on normal forms *)

Fixpoint wcomp (w1 w2 : word) : option word :=
  match w1 with
  | WEnd A => wcons A w2
  | WAtom A L a w => match wcomp w w2 with Some w' => settle A L a w' | None => None end
  end.

Definition sfront (h : lexp) (t : ntgt) (s : seg) : option seg :=
  if sdistb s then
    match sfind h s with
    | Some e => let '(ts, m) := ofe e in sset h (TCons t ts) m s
    | None => None
    end
  else None.

Definition slift (h : lexp) (s : seg) : option seg :=
  match scomp (shseg h 1) s with Some s' => sfront h (NVar h 0) s' | None => None end.

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
      if u <? ntm then match pnorm_e p with Some (w, b) => Some (NBind u (bnorm b w) b) | None => None end
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

Lemma lift_shiftk h k (a : radj T) : rcompose (iter k (rlift h) a) (shiftk h k) = rcompose (shiftk h k) a.
Proof.
  induction k as [|k IH]; cbn [iter shiftk]; [rewrite rcompose_identity_l, rcompose_identity_r; reflexivity|].
  fold (shiftk h k); rewrite !(rpush_outer_as_compose h (shiftk h k)).
  rewrite rcompose_assoc, rcompose_lift_shift, <- rcompose_assoc, IH, rcompose_assoc; reflexivity.
Qed.

Lemma assoc_move (A Sh Y Z U rest : radj T) :
  rcompose Z Sh = rcompose Sh Y ->
  rcompose A (rcompose Z (rcompose (rcompose Sh U) rest)) = rcompose (rcompose A Sh) (rcompose Y (rcompose U rest)).
Proof.
  intros H; rewrite <- (rcompose_assoc Sh U rest), (rcompose_assoc Z Sh), H.
  rewrite <- (rcompose_assoc Sh Y), (rcompose_assoc A Sh); reflexivity.
Qed.

Lemma try_unshift_sound h U k k' U' :
  try_unshift F ntm h U k = Some (k', U') -> sden U = rcompose (shiftk (lden h) k') (sden U').
Proof.
  induction k as [|k IH]; cbn [try_unshift]; [discriminate|].
  destruct (scomp F ntm (unseg h (S k)) U) as [U1|] eqn:E1; [|apply IH].
  destruct (scomp F ntm (shseg h (S k)) U1) as [U2|] eqn:E2; [|apply IH].
  destruct (seg_eqb U2 U) eqn:Eq; [|apply IH].
  intros H; injection H as <- <-; apply (proj1 (proj2 (proj2 nf_eqb_eq))) in Eq; subst U2.
  rewrite (proj2 (scomp_sound _ _ _ E2)); reflexivity.
Qed.

Definition stden (st : seg * list (lexp * nat) * seg) (x rest : radj T) : radj T :=
  let '(A, L, U) := st in rcompose (sden A) (rcompose (lifts L x) (rcompose (sden U) rest)).

Lemma settle1_sound h st st' (x rest : radj T) : settle1 F ntm h st = Some st' -> stden st' x rest = stden st x rest.
Proof.
  destruct st as [[A L] U]; unfold settle1.
  destruct (try_unshift F ntm h U (lcount h L)) as [[k U']|] eqn:Et; [|intros H; injection H as <-; reflexivity].
  destruct (scomp F ntm A (shseg h k)) as [A'|] eqn:EA; [|discriminate].
  destruct (lsub F h k L) as [L'|] eqn:EL; [|discriminate]; intros H; injection H as <-; cbn [stden].
  rewrite (try_unshift_sound _ _ _ _ _ Et), (lsub_sound _ _ _ _ x EL), (proj2 (scomp_sound _ _ _ EA)), sden_shseg.
  symmetry; apply assoc_move, lift_shiftk.
Qed.

Lemma settle_all_sound hs st st' (x rest : radj T) : settle_all F ntm hs st = Some st' -> stden st' x rest = stden st x rest.
Proof.
  revert st; induction hs as [|h hs IH]; intros st; cbn [settle_all]; [congruence|].
  destruct (settle1 F ntm h st) as [st1|] eqn:E; [|discriminate]; intros H.
  rewrite (IH _ H); apply (settle1_sound _ _ _ _ _ E).
Qed.

Definition wrest (w : word) : radj T :=
  match w with WEnd _ => ridentity | WAtom _ L a w => rcompose (lifts L (aden a)) (wden w) end.

Lemma wden_head w : wden w = rcompose (sden (whead w)) (wrest w).
Proof. destruct w; cbn [whead wrest]; [rewrite wden_end, rcompose_identity_r|rewrite wden_atom]; reflexivity. Qed.

Lemma wden_sethead w U : wden (wsethead w U) = rcompose (sden U) (wrest w).
Proof. destruct w; cbn [wsethead wrest]; [rewrite wden_end, rcompose_identity_r|rewrite wden_atom]; reflexivity. Qed.

Lemma settle_sound A L a w w' :
  settle F ntm A L a w = Some w' -> wden w' = rcompose (sden A) (rcompose (lifts L (aden a)) (wden w)).
Proof.
  unfold settle; destruct (settle_all F ntm (map fst L) (A, L, whead w)) as [[[A' L'] U']|] eqn:E; [|discriminate].
  intros H; injection H as <-; pose proof (settle_all_sound _ _ _ (aden a) (wrest w) E) as Hs; cbn [stden] in Hs.
  rewrite wden_atom, wden_sethead, Hs, <- (wden_head w); reflexivity.
Qed.

(** *** The constructors *)

Lemma wcomp_sound w1 w2 w : wcomp F ntm w1 w2 = Some w -> wden w = rcompose (wden w1) (wden w2).
Proof.
  revert w; induction w1 as [A|A L a w1 IH] using word_spine; intros w; cbn [wcomp].
  - intros H; rewrite (wcons_sound _ _ _ H); reflexivity.
  - destruct (wcomp F ntm w1 w2) as [w'|] eqn:E; [|discriminate]; intros H.
    rewrite (settle_sound _ _ _ _ _ H), (IH _ eq_refl), wden_atom, !rcompose_assoc; reflexivity.
Qed.

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
  = if u <? ntm then match pnorm_e F ntm p with Some (w, b) => Some (NBind u (bnorm b w) b) | None => None end else None.
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
    destruct (pnorm_e F ntm p) as [[w b]|] eqn:Ep; [|discriminate]; intros H; injection H as <-.
    destruct (nth_error tenv u) as [x|] eqn:Ex; [|apply nth_error_None in Ex; lia].
    cbn [tden]; rewrite Ex, bnorm_sound, (IH _ _ eq_refl); reflexivity.
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

Definition apply_result (F : list (lexp * lexp)) (ntm : nat) (e : aexp) (h : lexp) (i : nat) : option (lexp * nat) :=
  match anorm F ntm e with
  | Some (WEnd Sg) =>
      if sdistb F Sg then
        match sfind F h Sg with
        | Some None => Some (h, i)
        | Some (Some (ts, m)) =>
            if i <? tlen ts then match tnth ts i with NVar h' j => Some (h', j) | _ => None end
            else Some (h, i - tlen ts + m)
        | None => None
        end
      else None
  | _ => None
  end.

Theorem apply_result_sound e h i h' j :
  apply_result F ntm e h i = Some (h', j) ->
  rapply (aeden e) (mk_rvar (lden h) i) = inl (mk_rvar (lden h') j).
Proof.
  unfold apply_result; destruct (anorm F ntm e) as [[Sg|]|] eqn:E; try discriminate.
  destruct (sdistb F Sg) eqn:Ed; [|discriminate]; apply sdistb_sound in Ed.
  destruct (sfind F h Sg) as [r|] eqn:Ef; [|discriminate]; apply sfind_sound in Ef.
  rewrite <- (proj1 anorm_sound _ _ E), wden_end, rapply_sden by exact Ed; cbn [v_label v_index].
  rewrite <- Ef; destruct r as [[ts m]|]; cbn [esem].
  - destruct (i <? tlen ts); [|intros H; injection H as <- <-; reflexivity].
    destruct (tnth ts i) as [h0 j0|]; [|discriminate]; intros H; injection H as <- <-; reflexivity.
  - intros H; injection H as <- <-; reflexivity.
Qed.

End Sound.
