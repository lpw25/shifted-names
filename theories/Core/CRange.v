(** * Index ranges of normal forms

    An expression whose term atoms are below [n] and whose adjustment
    atoms are below [b] ([inrange]) has a normal form whose values and
    steps are in the same ranges ([WOk]).  So what is read off a normal
    form (its display, a lookup) needs no checking. *)

From Stdlib Require Import List Arith Lia Bool.
From ShiftedNames.Core Require Import Label Normalise CNorm.
Import ListNotations.

Section Range.

Variables (n b : nat).

Inductive VOk : cval -> Prop :=
| VOkVar h i : VOk (VVar h i)
| VOkTerm u p : u < n -> Forall SOk p -> VOk (VTerm u p)
| VOkLook h i w : Forall SOk w -> VOk (VLook h i w)
with SOk : cstep -> Prop :=
| SOkE h v : VOk v -> SOk (SE h v)
| SOkW h : SOk (SW h)
| SOkA a : a < b -> SOk (SA a).

Definition WOk (w : cword) : Prop := Forall SOk w.

Fixpoint inrange (e : aexp) : bool :=
  match e with
  | AId => true
  | AAtom a => Nat.ltb a b
  | ACompose x y => inrange x && inrange y
  | AOuter _ x | ALift _ x => inrange x
  | AInner _ t x => tinrange t && inrange x
  end
with tinrange (t : texp) : bool :=
  match t with
  | TVarE _ _ => true
  | TBindE u p => Nat.ltb u n && inrange p
  | TShiftE _ t => tinrange t
  | TLookE _ _ x => inrange x
  end.

End Range.

(** A larger bound on atoms. *)
Lemma inrange_mono n b b' : b <= b' ->
  (forall e, inrange n b e = true -> inrange n b' e = true)
  /\ (forall t, tinrange n b t = true -> tinrange n b' t = true).
Proof.
  intros L; apply exp_mind; intros; cbn [inrange tinrange] in *; rewrite ?andb_true_iff in *; try tauto.
  apply Nat.ltb_lt in H; apply Nat.ltb_lt; lia.
Qed.

Section Range2.

Variables (n b : nat).

Lemma Forall_rev_append {A} (P : A -> Prop) l r : Forall P l -> Forall P r -> Forall P (rev_append l r).
Proof.
  revert r; induction l as [|x l IH]; intros r Hl Hr; cbn; [exact Hr|].
  inversion Hl; subst; apply IH; [assumption|constructor; assumption].
Qed.

Local Notation VOk := (VOk n b).
Local Notation SOk := (SOk n b).
Local Notation WOk := (WOk n b).
Local Notation inrange := (inrange n b).
Local Notation tinrange := (tinrange n b).

Variable F : order.

Lemma follow_ok h : forall w i kept, Forall SOk kept -> WOk w -> VOk (follow F h i kept w).
Proof.
  induction w as [|s w IH]; intros i kept Hk Hw; cbn [follow].
  - destruct kept; [constructor|constructor; apply Forall_rev, Hk].
  - inversion Hw as [|? ? Hs Hw']; subst.
    destruct s as [g v|g|a].
    + destruct (passes F h g kept); [apply IH; assumption|].
      destruct kept as [|k kept].
      * destruct (lexp_eqb g h); [|apply IH; [constructor; [exact Hs|constructor]|exact Hw']].
        destruct i; [inversion Hs; assumption|apply IH; [constructor|exact Hw']].
      * apply IH; [constructor; assumption|exact Hw'].
    + destruct (passes F h g kept); [apply IH; assumption|].
      destruct kept as [|k kept].
      * destruct (lexp_eqb g h); apply IH; try exact Hw'; constructor; [exact Hs|constructor].
      * apply IH; [constructor; assumption|exact Hw'].
    + constructor; apply Forall_rev_append; [exact Hk|exact Hw].
Qed.

Lemma lookup_ok h i w : WOk w -> VOk (lookup F h i w).
Proof. intros H; apply follow_ok; [constructor|exact H]. Qed.

Lemma stop_ok h : forall w p r, WOk w -> stop F h w = (p, r) -> WOk p /\ WOk r.
Proof.
  induction w as [|s w IH]; intros p r Hw E; cbn [stop] in E.
  - injection E as <- <-; split; constructor.
  - inversion Hw as [|? ? Hs Hw']; subst.
    destruct s as [g v|g|a];
      [destruct (before F g h)|destruct (before F g h)|];
      try (injection E as <- <-; split; [constructor|exact Hw]).
    + destruct (stop F h w) as [p' r'] eqn:E'; injection E as <- <-.
      destruct (IH p' r' Hw' eq_refl) as [Hp Hr]; split; [constructor; assumption|exact Hr].
    + destruct (stop F h w) as [p' r'] eqn:E'; injection E as <- <-.
      destruct (IH p' r' Hw' eq_refl) as [Hp Hr]; split; [constructor; assumption|exact Hr].
Qed.

Lemma pushW_ok h w : WOk w -> WOk (pushW F h w).
Proof.
  intros Hw; unfold pushW; destruct (stop F h w) as [p r] eqn:E.
  destruct (stop_ok h w p r Hw E) as [Hp Hr]; unfold WOk in *.
  destruct r as [|[g v|g|a] r']; try (apply Forall_app; split; [exact Hp|constructor; [constructor|exact Hr]]).
  inversion Hr; subst; destruct (lexp_eqb g h); apply Forall_app; split; try exact Hp; try assumption.
  constructor; [constructor|exact Hr].
Qed.

Lemma pushE_ok h v w : VOk v -> WOk w -> WOk (pushE F h v w).
Proof.
  intros Hv Hw; unfold pushE; destruct (stop F h w) as [p r] eqn:E.
  destruct (stop_ok h w p r Hw E) as [Hp Hr]; unfold WOk in *.
  destruct r as [|[g v'|g|a] r']; try (apply Forall_app; split; [exact Hp|constructor; [constructor; exact Hv|exact Hr]]).
  inversion Hr; subst; destruct (lexp_eqb g h && val_eqb v (lookup F h 0 r')); apply Forall_app; split;
    try exact Hp; try assumption; constructor; [constructor; exact Hv|exact Hr].
Qed.

Lemma norm_ok :
  (forall e K, inrange e = true -> WOk K -> WOk (norm F e K))
  /\ (forall t K, tinrange t = true -> WOk K -> VOk (tval F t K)).
Proof.
  apply exp_mind; cbn [inrange tinrange norm tval]; intros; rewrite ?andb_true_iff in *.
  - exact H0.
  - constructor; [constructor; apply Nat.ltb_lt, H|exact H0].
  - destruct H1; apply H0; [assumption|apply H; assumption].
  - apply H; [exact H0|apply pushW_ok, H1].
  - destruct H1; apply pushE_ok; [apply H; assumption|apply H0; assumption].
  - apply pushE_ok; [apply lookup_ok, H1|apply H; [exact H0|apply pushW_ok, H1]].
  - apply lookup_ok; assumption.
  - destruct H0 as [Hu Hp]; constructor; [apply Nat.ltb_lt, Hu|apply H; assumption].
  - apply H; [assumption|apply pushW_ok, H1].
  - apply lookup_ok, H; assumption.
Qed.

End Range2.
