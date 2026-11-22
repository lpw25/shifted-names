(** * The normaliser, without sharing

    [HNorm]'s algorithm on plain lists ([docs/comprehension.md]).  A
    lookup that cannot get past a step gives the variable with the steps
    that can affect it as its payload ([follow]).  [CSound] proves it sound
    and [CComplete] complete for comprehension models ([Comp]).

    A word is a list of steps, the first applying first to a variable:
    - [SE h v]: an input entry on [h] with the value [v];
    - [SW h]: a weakening on [h];
    - [SA a]: an adjustment atom.
    Values are absolute, read at the end of the word: a name [hᵢ], a term
    with its payload word, or a name with the payload word it is read
    through. *)

From Stdlib Require Import String List Bool Arith.
From ShiftedNames.Core Require Import Label Normalise.
Import ListNotations.

Inductive cval : Type :=
| VVar (h : lexp) (i : nat)
| VTerm (u : nat) (b : option nat) (p : list cstep)
| VLook (h : lexp) (i : nat) (w : list cstep)
with cstep : Type :=
| SE (h : lexp) (v : cval)
| SW (h : lexp)
| SA (a : nat).

Definition cword : Type := list cstep.

(** ** Decidable equality *)

Definition oeqb (a b : option nat) : bool :=
  match a, b with Some x, Some y => Nat.eqb x y | None, None => true | _, _ => false end.

Lemma oeqb_eq a b : oeqb a b = true <-> a = b.
Proof.
  destruct a, b; cbn; split; intros H; try discriminate; try reflexivity.
  - apply Nat.eqb_eq in H; subst; reflexivity.
  - injection H as ->; apply Nat.eqb_refl.
Qed.

Fixpoint val_eqb (a b : cval) : bool :=
  let fix weqb (x y : cword) : bool :=
    match x, y with
    | [], [] => true
    | s :: x', s' :: y' =>
        match s, s' with
        | SE h v, SE h' v' => lexp_eqb h h' && val_eqb v v' && weqb x' y'
        | SW h, SW h' => lexp_eqb h h' && weqb x' y'
        | SA a, SA a' => Nat.eqb a a' && weqb x' y'
        | _, _ => false
        end
    | _, _ => false
    end in
  match a, b with
  | VVar h i, VVar h' i' => lexp_eqb h h' && Nat.eqb i i'
  | VTerm u b p, VTerm u' b' p' => Nat.eqb u u' && oeqb b b' && weqb p p'
  | VLook h i w, VLook h' i' w' => lexp_eqb h h' && Nat.eqb i i' && weqb w w'
  | _, _ => false
  end.

Lemma val_eqb_eq : forall a b, val_eqb a b = true <-> a = b.
Proof.
  fix IH 1.
  assert (W : forall x y : cword,
    (fix weqb (x y : cword) : bool :=
       match x, y with
       | [], [] => true
       | s :: x', s' :: y' =>
           match s, s' with
           | SE h v, SE h' v' => lexp_eqb h h' && val_eqb v v' && weqb x' y'
           | SW h, SW h' => lexp_eqb h h' && weqb x' y'
           | SA a, SA a' => Nat.eqb a a' && weqb x' y'
           | _, _ => false
           end
       | _, _ => false
       end) x y = true <-> x = y).
  { fix IW 1; intros [|s x] [|s' y]; cbn; try (split; intros H; congruence).
    destruct s as [h v|h|a], s' as [h' v'|h'|a']; try (split; intros H; congruence);
      rewrite ?andb_true_iff, ?lexp_eqb_eq, ?Nat.eqb_eq, ?IH, ?IW.
    - split; [intros [[-> ->] ->]; reflexivity|intros E; injection E as -> -> ->; auto].
    - split; [intros [-> ->]; reflexivity|intros E; injection E as -> ->; auto].
    - split; [intros [-> ->]; reflexivity|intros E; injection E as -> ->; auto]. }
  intros [h i|u b p|h i w] [h' i'|u' b' p'|h' i' w']; cbn; try (split; intros H; congruence);
    rewrite ?andb_true_iff, ?lexp_eqb_eq, ?Nat.eqb_eq, ?oeqb_eq, ?W.
  - split; [intros [-> ->]; reflexivity|intros E; injection E as -> ->; auto].
  - split; [intros [[-> ->] ->]; reflexivity|intros E; injection E as -> -> ->; auto].
  - split; [intros [[-> ->] ->]; reflexivity|intros E; injection E as -> -> ->; auto].
Qed.

Lemma val_eqb_refl v : val_eqb v v = true.
Proof. apply val_eqb_eq; reflexivity. Qed.

Definition slabel (s : cstep) : option lexp :=
  match s with SE h _ | SW h => Some h | SA _ => None end.

Section Norm.

Variable F : order.

(** Labels the facts show distinct. *)
Definition kd (a b : lexp) : bool := match lcmp F a b with Some Lt | Some Gt => true | _ => false end.

(** [a] sorts before [b]. *)
Definition before (a b : lexp) : bool := match lcmp F a b with Some Lt => true | _ => false end.

(** ** Following a variable

    [follow h i kept w] follows [hᵢ] through [w], first step first, as
    [apply_var] follows a variable through an adjustment.  It passes a
    step that cannot affect [hᵢ]: one on a label known distinct from [h]
    and sorting after the label of every step kept so far, so that it can
    be moved in front of the kept steps.  (In a normal word this is the
    same as known distinct from every kept label: a step known distinct
    from them all always sorts after them.)  Until a step is kept, a step
    on [h] moves the index, or, as an entry for [h₀], gives the value.
    Any other step is kept, and the value is then the variable [hᵢ] with
    the kept steps as its payload; an atom is kept with everything after
    it.  [kept] is in reverse order. *)

(** The step [t] is kept on a label sorting before [l]. *)
Definition sbef (l : lexp) (t : cstep) : bool := match slabel t with Some m => before m l | None => false end.

Definition passes (h l : lexp) (kept : cword) : bool := kd h l && forallb (sbef l) kept.

Fixpoint follow (h : lexp) (i : nat) (kept : cword) (w : cword) : cval :=
  match w with
  | [] => match kept with [] => VVar h i | _ => VLook h i (rev kept) end
  | s :: w' =>
      match s with
      | SE g v =>
          if passes h g kept then follow h i kept w'
          else match kept with
               | [] => if lexp_eqb g h then match i with 0 => v | S i' => follow h i' [] w' end
                       else follow h i [s] w'
               | _ => follow h i (s :: kept) w'
               end
      | SW g =>
          if passes h g kept then follow h i kept w'
          else match kept with
               | [] => if lexp_eqb g h then follow h (S i) [] w' else follow h i [s] w'
               | _ => follow h i (s :: kept) w'
               end
      | SA _ => VLook h i (rev_append kept w)
      end
  end.

(** The name [hᵢ] at the start of [w], followed to its value. *)
Definition lookup (h : lexp) (i : nat) (w : cword) : cval := follow h i [] w.

(** The steps a new step on [h] passes: those on labels sorting before
    [h]; and the rest. *)
Fixpoint stop (h : lexp) (w : cword) : cword * cword :=
  match w with
  | [] => ([], [])
  | s :: w' =>
      match s with
      | SE g _ | SW g => if before g h then let '(p, r) := stop h w' in (s :: p, r) else ([], w)
      | SA _ => ([], w)
      end
  end.

(** A weakening on [h] in front of [w]. *)
Definition pushW (h : lexp) (w : cword) : cword :=
  let '(p, r) := stop h w in
  match r with
  | SE g _ :: r' => if lexp_eqb g h then p ++ r' else p ++ SW h :: r
  | _ => p ++ SW h :: r
  end.

(** An entry on [h] with value [v] in front of [w]. *)
Definition pushE (h : lexp) (v : cval) (w : cword) : cword :=
  let '(p, r) := stop h w in
  match r with
  | SW g :: r' => if lexp_eqb g h && val_eqb v (lookup h 0 r') then p ++ r' else p ++ SE h v :: r
  | _ => p ++ SE h v :: r
  end.

(** A payload with no payload atom only sees named variables:
    bound-label steps before its first atom are dropped. *)
Fixpoint unbound (w : cword) : cword :=
  match w with
  | [] => []
  | s :: w' =>
      match s with
      | SE LNone _ | SW LNone => unbound w'
      | SA _ => w
      | _ => s :: unbound w'
      end
  end.

Definition clean (b : option nat) (w : cword) : cword :=
  match b with Some _ => w | None => unbound w end.

Fixpoint is_bind (t : texp) : bool := match t with TBindE _ _ => true | TShiftE _ t => is_bind t | _ => false end.

(** [norm e K]: [e], then the word [K]. *)
Fixpoint norm (e : aexp) (K : cword) {struct e} : cword :=
  match e with
  | AId => K
  | AAtom n => SA n :: K
  | ACompose a b => norm b (norm a K)
  | AOuter h a => norm a (pushW h K)
  | AInner h t a => pushE h (tval t K) (norm a K)
  | ALift h a => pushE h (lookup h 0 K) (norm a (pushW h K))
  end
with tval (t : texp) (K : cword) {struct t} : cval :=
  match t with
  | TVarE h i => lookup h i K
  | TBindE u p => VTerm u (fpb p) (clean (fpb p) (pnorm p K))
  | TShiftE h t' => if is_bind t' then tval t' K else tval t' (pushW h K)
  end
with pnorm (p : pexp) (K : cword) {struct p} : cword :=
  match p with
  | PId | PAtom _ => K
  | PComp a p' => pnorm p' (norm a K)
  | PShift h p' => pnorm p' (pushW h K)
  end.

(** The decision. *)
Definition cn_eq (e1 e2 : aexp) : bool := val_eqb (VLook LNone 0 (norm e1 [])) (VLook LNone 0 (norm e2 [])).

Lemma cn_eq_iff e1 e2 : cn_eq e1 e2 = true <-> norm e1 [] = norm e2 [].
Proof.
  unfold cn_eq; rewrite val_eqb_eq; split; [intros E; injection E as E; exact E|intros ->; reflexivity].
Qed.

End Norm.
