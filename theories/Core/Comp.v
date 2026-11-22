(** * Comprehension models

    The generic models of [docs/comprehension.md].  An adjustment is a
    map into a context, not a function on variables: each label [h] comes
    with a comprehension, an isomorphism between environments [U] and
    environments with one more value, [U × A]:
    - [cpop h] forgets the head value of [h] (the projection [p_h]);
    - [chd h] reads it ([q_h]);
    - [cpush h x t] puts [t] in front ([⟨x, t⟩_h]).

    Labels the facts order commute.  Term atoms without a payload atom
    ignore the bound label.  Nothing else is assumed: labels the facts
    leave unordered are unrelated.

    An adjustment acts on environments of its output and gives
    environments of its input, so [ACompose a b] ([b] acting first on a
    variable) is [a]'s action followed by [b]'s. *)

From Stdlib Require Import List.
From ShiftedNames.Core Require Import Label Normalise CNorm.
Import ListNotations.

Record cmodel : Type := mk_cmodel {
  cU : Type;
  cA : Type;
  cpop : lexp -> cU -> cU;
  chd : lexp -> cU -> cA;
  cpush : lexp -> cU -> cA -> cU;
  cpop_push : forall h x t, cpop h (cpush h x t) = x;
  chd_push : forall h x t, chd h (cpush h x t) = t;
  cpush_pop : forall h x, cpush h (cpop h x) (chd h x) = x;
  (** adjustment atoms, and term atoms with their payload atom *)
  catom : nat -> cU -> cU;
  cterm : nat -> option nat -> cU -> cA
}.

Arguments cpop {_} _ _.
Arguments chd {_} _ _.
Arguments cpush {_} _ _ _.
Arguments catom {_} _ _.
Arguments cterm {_} _ _ _.

(** Consistency with the facts. *)
Definition ccons (F : order) (M : cmodel) : Prop :=
  (forall g h, lt_known F g h = true -> forall x : cU M,
     cpop g (cpop h x) = cpop h (cpop g x) /\ chd g (cpop h x) = chd g x /\ chd h (cpop g x) = chd h x)
  /\ (forall u (x : cU M), cterm u None (cpop LNone x) = cterm u None x).

Section Interp.

Variable M : cmodel.
Local Notation U := (cU M).
Local Notation A := (cA M).

(** [hᵢ]: the head of [h] after [i] projections. *)
Definition cname (h : lexp) (i : nat) (x : U) : A := chd h (iter i (cpop h) x).

Fixpoint ca (a : aexp) (x : U) {struct a} : U :=
  match a with
  | AId => x
  | AAtom n => catom n x
  | ACompose a b => ca b (ca a x)
  | AOuter h a => ca a (cpop h x)
  | AInner h t a => cpush h (ca a x) (ct t x)
  | ALift h a => cpush h (ca a (cpop h x)) (chd h x)
  end
with ct (t : texp) (x : U) {struct t} : A :=
  match t with
  | TVarE h i => cname h i x
  | TBindE u p => cterm u (fpb p) (cp p x)
  | TShiftE h t' => if CNorm.is_bind t' then ct t' x else ct t' (cpop h x)
  end
with cp (p : pexp) (x : U) {struct p} : U :=
  match p with
  | PId | PAtom _ => x
  | PComp a p' => cp p' (ca a x)
  | PShift h p' => cp p' (cpop h x)
  end.

(** Pairing is injective. *)
Lemma cpush_inj h (x y : U) : cpop h x = cpop h y -> chd h x = chd h y -> x = y.
Proof. intros E1 E2; rewrite <- (cpush_pop M h x), <- (cpush_pop M h y), E1, E2; reflexivity. Qed.

End Interp.

Arguments cname {M} h i x.
Arguments ca {M} a x.
Arguments ct {M} t x.
Arguments cp {M} p x.

(** Two expressions are equal when they act the same in every model
    consistent with the facts. *)
Definition cequal (F : order) (a b : aexp) : Prop :=
  forall M, ccons F M -> forall x : cU M, ca a x = ca b x.

(** ** Labels the facts order *)

Section Ordered.

Variables (F : order) (M : cmodel).
Hypothesis HM : ccons F M.
Local Notation U := (cU M).

(** Labels the facts show distinct, in either direction. *)
Definition known_distinct (g h : lexp) : Prop := lt_known F g h = true \/ lt_known F h g = true.

Lemma kd_pops g h : known_distinct g h -> forall x : U,
  cpop g (cpop h x) = cpop h (cpop g x) /\ chd g (cpop h x) = chd g x /\ chd h (cpop g x) = chd h x.
Proof.
  intros [L|L] x; [apply (proj1 HM g h L)|].
  destruct (proj1 HM h g L x) as [E1 [E2 E3]]; repeat split; auto.
Qed.

Lemma kd_pop_push g h : known_distinct g h -> forall (x : U) t, cpop g (cpush h x t) = cpush h (cpop g x) t.
Proof.
  intros D x t; apply (cpush_inj M h).
  - destruct (kd_pops g h D (cpush h x t)) as [E _]; rewrite <- E, !cpop_push; reflexivity.
  - destruct (kd_pops g h D (cpush h x t)) as [_ [_ E]]; rewrite E, !chd_push; reflexivity.
Qed.

Lemma kd_hd_push g h : known_distinct g h -> forall (x : U) t, chd g (cpush h x t) = chd g x.
Proof.
  intros D x t; destruct (kd_pops g h D (cpush h x t)) as [_ [E _]]; rewrite <- E, cpop_push; reflexivity.
Qed.

Lemma kd_push_push g h : known_distinct g h -> forall (x : U) s t,
  cpush g (cpush h x t) s = cpush h (cpush g x s) t.
Proof.
  intros D x s t; apply (cpush_inj M g).
  - rewrite cpop_push, (kd_pop_push g h D), cpop_push; reflexivity.
  - rewrite chd_push, (kd_hd_push g h D), chd_push; reflexivity.
Qed.

Lemma known_distinct_sym g h : known_distinct g h -> known_distinct h g.
Proof. intros [L|L]; [right|left]; exact L. Qed.

End Ordered.
