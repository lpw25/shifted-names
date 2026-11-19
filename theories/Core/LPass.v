(** * A left-to-right pass: weakenings and renamings move right

    A word of single steps, each read where it stands:
    - [RW h]: the weakening [⟦ \ h as _ ⟧];
    - [RE h t]: an input entry on [h] whose target [t] is read in the
      step's own output, so [RE g (TVarE h 0)] copies [h₀] into [g];
    - [RO e]: any other expression, which nothing moves past.

    The pass moves weakenings and entries whose target is a name to the
    right, past steps on labels that sort before theirs, and lets a
    weakening cancel the entry on its own label it meets.  On the way
    the targets are adjusted, and a copy [g ↦ x₀] followed by an entry
    on [x] takes that entry's target.  Each move is sound in every
    comprehension model consistent with the facts ([swap_sound],
    [subst_sound]), so the pass is ([pass_sound]). *)

From Stdlib Require Import List Bool Arith.
From ShiftedNames.Core Require Import Label Normalise GEval CNorm Comp CSound.
Import ListNotations.

Inductive rstep : Type :=
| RW (h : lexp)
| RE (h : lexp) (t : texp)
| RO (e : aexp).

Definition rword : Type := list rstep.

(** ** Words and expressions *)

(** The steps of an expression, the first applying first to a variable. *)
Fixpoint flatten (e : aexp) : rword :=
  match e with
  | AId => []
  | ACompose a b => flatten b ++ flatten a
  | AOuter h a => flatten a ++ [RW h]
  | AInner h t AId => [RE h t]
  | _ => [RO e]
  end.

Definition sexp (s : rstep) : aexp :=
  match s with RW h => AOuter h AId | RE h t => AInner h t AId | RO e => e end.

Fixpoint wexp (w : rword) : aexp :=
  match w with [] => AId | s :: w' => ACompose (wexp w') (sexp s) end.

Section Pass.

Variable F : order.

(** [t] read one weakening of [g] further on: [t ∘ p_g], as a target. *)
Definition up (g : lexp) (t : texp) : option texp :=
  match t with
  | TVarE y i => if lexp_eqb y g then Some (TVarE y (S i)) else if kd F y g then Some t else None
  | TBindE u p => Some (TBindE u (PShift g p))
  | TShiftE _ _ => None
  end.

(** A target [t'] with [t' ∘ p_h = t]: [t] does not read [h₀]. *)
Definition down (h : lexp) (t : texp) : option texp :=
  match t with
  | TVarE y i =>
      if lexp_eqb y h then match i with 0 => None | S i' => Some (TVarE y i') end
      else if kd F y h then Some t else None
  | _ => None
  end.

(** The name [a] read through an entry on [g] with target [t]. *)
Definition through (g : lexp) (t : texp) (a : texp) : option texp :=
  match a with
  | TVarE y i =>
      if lexp_eqb y g then match i with 0 => Some t | S i' => Some (TVarE y i') end
      else if kd F y g then Some a else None
  | _ => None
  end.

Definition slab (s : rstep) : option lexp :=
  match s with RW h | RE h _ => Some h | RO _ => None end.

Inductive move : Type :=
| Cancel
| Swap (a b : rstep)
| Stuck.

(** [s1 ⨾ s2], with [s1] moving right past [s2]. *)
Definition swap (s1 s2 : rstep) : move :=
  match s1, s2 with
  | RW h, RE g _ => if lexp_eqb g h then Cancel else
      if before F g h then match s2 with RE g t => match down h t with Some t' => Swap (RE g t') s1 | None => Stuck end | _ => Stuck end
      else Stuck
  | RW h, RW g => if before F g h then Swap s2 s1 else Stuck
  | RE h a, RW g =>
      if before F g h then match up g a with Some a' => Swap s2 (RE h a') | None => Stuck end else Stuck
  | RE h a, RE g t =>
      if before F g h then
        match through g t a, up h t with Some a', Some t' => Swap (RE g t') (RE h a') | _, _ => Stuck end
      else Stuck
  | _, _ => Stuck
  end.

(** A copy of [x₀] followed by an entry on [x] takes that entry's target. *)
Definition subst (s1 s2 : rstep) : rstep :=
  match s1, s2 with
  | RE g (TVarE x 0), RE x' t =>
      if lexp_eqb x x' then match up x t with Some t' => RE g t' | None => s1 end else s1
  | _, _ => s1
  end.

Definition movable (s : rstep) : bool :=
  match s with RW _ | RE _ (TVarE _ _) => true | _ => false end.

(** [s] in front of a word it has been moved into, moved right as far as
    it goes. *)
Fixpoint insert (s : rstep) (r : rword) : rword :=
  match r with
  | [] => [s]
  | s2 :: r' =>
      let s := subst s s2 in
      if movable s then
        match swap s s2 with
        | Cancel => r'
        | Swap a b => a :: insert b r'
        | Stuck => s :: r
        end
      else s :: r
  end.

(** Every step, from the last, moved right into the steps after it. *)
Definition pass (w : rword) : rword := fold_right insert [] w.

(** ** Soundness *)

Variable M : cmodel.
Hypothesis HM : ccons F M.
Local Notation U := (cU M) (only parsing).

Definition rden (s : rstep) (x : U) : U :=
  match s with RW h => cpop h x | RE h t => cpush h x (ct t x) | RO e => ca e x end.

Fixpoint wden' (w : rword) (x : U) : U :=
  match w with [] => x | s :: w' => rden s (wden' w' x) end.

Lemma wden'_app p q x : wden' (p ++ q) x = wden' p (wden' q x).
Proof. induction p as [|s p IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma wexp_sound w x : ca (wexp w) x = wden' w x.
Proof. induction w as [|s w IH]; cbn; [reflexivity|]; rewrite IH; destruct s; reflexivity. Qed.

Lemma flatten_sound e x : wden' (flatten e) x = ca e x.
Proof.
  revert x; induction e; intros x; try reflexivity; cbn.
  - rewrite wden'_app, IHe1, IHe2; reflexivity.
  - rewrite wden'_app, IHe; reflexivity.
  - destruct e; reflexivity.
Qed.

(** *** Names past steps on other labels *)

Lemma pops_comm y g i (z : U) : known_distinct F y g ->
  iter i (cpop y) (cpop g z) = cpop g (iter i (cpop y) z).
Proof.
  intros D; induction i as [|i IH]; cbn; [reflexivity|]; rewrite IH.
  destruct (kd_pops F M HM y g D (iter i (cpop y) z)) as [E _]; exact E.
Qed.

Lemma cname_pop_other y g i (z : U) : known_distinct F y g -> cname y i (cpop g z) = cname y i z.
Proof.
  intros D; unfold cname; rewrite (pops_comm y g i z D).
  destruct (kd_pops F M HM y g D (iter i (cpop y) z)) as [_ [E _]]; exact E.
Qed.

Lemma cname_push_other y g i (z : U) s : known_distinct F y g -> cname y i (cpush g z s) = cname y i z.
Proof.
  intros D; revert z; induction i as [|i IH]; intros z.
  - apply (kd_hd_push F M HM y g D).
  - rewrite <- (cname_pop M y i), (kd_pop_push F M HM y g D), IH, (cname_pop M y i); reflexivity.
Qed.

Lemma lexp_eqb_true a b : lexp_eqb a b = true -> a = b.
Proof. apply lexp_eqb_eq. Qed.

Lemma up_sound g t t' (x : U) : up g t = Some t' -> ct t' x = ct t (cpop g x).
Proof.
  destruct t as [y i|u p|k t0]; cbn; try discriminate.
  - destruct (lexp_eqb y g) eqn:E; [apply lexp_eqb_true in E; subst|].
    + intros H; injection H as <-; cbn; symmetry; apply (cname_pop M).
    + destruct (kd F y g) eqn:K; [|discriminate]; intros H; injection H as <-; cbn.
      symmetry; apply cname_pop_other, (kd_known F _ _ K).
  - intros H; injection H as <-; reflexivity.
Qed.

Lemma down_sound h t t' (x : U) : down h t = Some t' -> ct t' (cpop h x) = ct t x.
Proof.
  destruct t as [y i|u p|k t0]; cbn; try discriminate.
  destruct (lexp_eqb y h) eqn:E; [apply lexp_eqb_true in E; subst|].
  - destruct i as [|i]; [discriminate|]; intros H; injection H as <-; cbn; apply (cname_pop M).
  - destruct (kd F y h) eqn:K; [|discriminate]; intros H; injection H as <-; cbn.
    apply cname_pop_other, (kd_known F _ _ K).
Qed.

Lemma through_sound g t a a' (x : U) : through g t a = Some a' ->
  ct a' x = ct a (cpush g x (ct t x)).
Proof.
  destruct a as [y i|u p|k t0]; cbn; try discriminate.
  destruct (lexp_eqb y g) eqn:E; [apply lexp_eqb_true in E; subst|].
  - destruct i as [|i]; intros H; injection H as <-; cbn.
    + symmetry; apply (cname_push0 M).
    + symmetry; apply (cname_push M).
  - destruct (kd F y g) eqn:K; [|discriminate]; intros H; injection H as <-; cbn.
    symmetry; apply cname_push_other, (kd_known F _ _ K).
Qed.

(** *** The moves *)

Lemma swap_sound s1 s2 (x : U) :
  (swap s1 s2 = Cancel -> rden s1 (rden s2 x) = x)
  /\ (forall a b, swap s1 s2 = Swap a b -> rden s1 (rden s2 x) = rden a (rden b x)).
Proof.
  destruct s1 as [h|h a|e1], s2 as [g|g t|e2]; cbn [swap]; try (split; [discriminate|intros ? ? H; discriminate]).
  - (* W, W *)
    destruct (before F g h) eqn:B; [|split; [discriminate|intros ? ? H; discriminate]].
    split; [discriminate|]; intros a b H; injection H as <- <-; cbn.
    destruct (kd_pops F M HM h g (known_distinct_sym F g h (before_known F g h B)) x) as [E _]; exact E.
  - (* W, E *)
    destruct (lexp_eqb g h) eqn:Q.
    { apply lexp_eqb_true in Q; subst; split; [intros _; cbn; apply cpop_push|intros ? ? H; discriminate]. }
    destruct (before F g h) eqn:B; [|split; [discriminate|intros ? ? H; discriminate]].
    destruct (down h t) as [t'|] eqn:D; [|split; [discriminate|intros ? ? H; discriminate]].
    split; [discriminate|]; intros a b H; injection H as <- <-; cbn.
    rewrite (down_sound h t t' x D).
    apply (kd_pop_push F M HM h g (known_distinct_sym F g h (before_known F g h B))).
  - (* E, W *)
    destruct (before F g h) eqn:B; [|split; [discriminate|intros ? ? H; discriminate]].
    destruct (up g a) as [a'|] eqn:D; [|split; [discriminate|intros ? ? H; discriminate]].
    split; [discriminate|]; intros a0 b H; injection H as <- <-; cbn.
    rewrite (up_sound g a a' x D).
    symmetry; apply (kd_pop_push F M HM g h (before_known F g h B)).
  - (* E, E *)
    destruct (before F g h) eqn:B; [|split; [discriminate|intros ? ? H; discriminate]].
    destruct (through g t a) as [a'|] eqn:T; [|split; [discriminate|intros ? ? H; discriminate]].
    destruct (up h t) as [t'|] eqn:D; [|split; [discriminate|intros ? ? H; discriminate]].
    split; [discriminate|]; intros a0 b H; injection H as <- <-; cbn.
    rewrite (up_sound h t t' _ D), cpop_push, (through_sound g t a a' x T).
    apply (kd_push_push F M HM h g (known_distinct_sym F g h (before_known F g h B))).
Qed.

Lemma subst_sound s1 s2 (x : U) : rden (subst s1 s2) (rden s2 x) = rden s1 (rden s2 x).
Proof.
  destruct s1 as [h|g a|e1]; try reflexivity.
  destruct a as [y [|i]|u p|k0 t0]; try reflexivity.
  destruct s2 as [k|x' t|e2]; try reflexivity; cbn [subst].
  destruct (lexp_eqb y x') eqn:E; [|reflexivity]; apply lexp_eqb_true in E; subst y.
  destruct (up x' t) as [t'|] eqn:D; [|reflexivity]; cbn.
  rewrite (up_sound x' t t' _ D), cpop_push, (cname_push0 M); reflexivity.
Qed.

Lemma insert_sound s r (x : U) : wden' (insert s r) x = rden s (wden' r x).
Proof.
  revert s; induction r as [|s2 r IH]; intros s; [reflexivity|]; cbn [insert wden'].
  rewrite <- (subst_sound s s2 (wden' r x)).
  destruct (movable (subst s s2)); [|reflexivity].
  destruct (swap_sound (subst s s2) s2 (wden' r x)) as [C S].
  destruct (swap (subst s s2) s2) as [|a b|]; [rewrite C; reflexivity| |reflexivity].
  rewrite (S a b eq_refl); cbn [wden']; rewrite IH; reflexivity.
Qed.

Lemma pass_sound w (x : U) : wden' (pass w) x = wden' w x.
Proof.
  induction w as [|s w IH]; [reflexivity|]; cbn [pass fold_right wden'].
  fold (pass w); rewrite insert_sound, IH; reflexivity.
Qed.

(** The pass, read back as an expression, means what the expression
    does. *)
Lemma lpass_sound e (x : U) : ca (wexp (pass (flatten e))) x = ca e x.
Proof. rewrite wexp_sound, pass_sound, flatten_sound; reflexivity. Qed.

End Pass.

Definition lpass (F : order) (e : aexp) : aexp := wexp (pass F (flatten e)).

Theorem lpass_cequal F e : forall M, ccons F M -> forall x : cU M, ca (lpass F e) x = ca e x.
Proof. intros M HM x; apply (lpass_sound F M HM). Qed.

(** ** The examples that needed [CNorm.relnf]

    Facts [g < h], [k < h], [m < h]; [g], [k], [m] pairwise unordered.
    In [W1] and [W2] the copies [h ↦ ·₀] and [g ↦ m₀] come in either
    order before [⟦ \ k as _ ⟧]; [Y1] and [Y2] differ in whether [g]
    copies [g₀] or [h₀], where the entry on [h] after it copies [g₀].
    The pass gives each pair one word, so the right-to-left normaliser
    then sees the same input. *)
Module Examples.
Definition g := LAtom 0. Definition h := LAtom 1. Definition k := LAtom 2. Definition m := LAtom 3.
Definition F := order_of [(g, h); (k, h); (m, h)].
Definition E (a b : lexp) (i : nat) : aexp := AInner a (TVarE b i) AId.
Definition W (a : lexp) : aexp := AOuter a AId.
Definition seq3 (a b c : aexp) : aexp := ACompose (ACompose c b) a.
Definition W1 := seq3 (E h LNone 0) (E g m 0) (W k).
Definition W2 := seq3 (E g m 0) (E h LNone 0) (W k).
Definition Y1 := seq3 (E g g 0) (E h g 0) (W k).
Definition Y2 := seq3 (E g h 0) (E h g 0) (W k).
Lemma W12 : pass F (flatten W1) = pass F (flatten W2). Proof. vm_compute; reflexivity. Qed.
Lemma Y12 : pass F (flatten Y1) = pass F (flatten Y2). Proof. vm_compute; reflexivity. Qed.
Lemma W_pass : pass F (flatten W1) = [RE g (TVarE m 0); RW k; RE h (TVarE LNone 0)]. Proof. vm_compute; reflexivity. Qed.
End Examples.
