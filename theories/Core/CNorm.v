(** * The normaliser, without sharing

    [HNorm]'s algorithm on plain lists ([docs/comprehension.md]), with
    one change: a lookup stuck at a step keeps only the steps of the rest
    of the word that can affect it ([relnf]).  [CSound] proves it sound
    and [CComplete] complete for comprehension models ([Comp]).

    A word is a list of steps, the first applying first to a variable:
    - [SE h v]: an input entry on [h] with the value [v];
    - [SW h]: a weakening on [h];
    - [SA a]: an adjustment atom.
    Values are absolute, read at the end of the word: a name [hᵢ], a term
    with its payload word, or a name looked up through a word whose
    first step stops it. *)

From Stdlib Require Import String List Bool Arith.
From ShiftedNames.Core Require Import Label Normalise GEval.
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

(** ** Stuck lookups keep only what can affect them

    In a lookup of [g] stopped at the first step of a word, a later step
    on a label known distinct from [g] that commutes with every step kept
    before it can be moved to the front, where it does not affect [g].
    [kept] are the labels of the steps kept so far. *)
Fixpoint relnf_go (g : lexp) (kept : list lexp) (w : cword) : cword :=
  match w with
  | [] => []
  | s :: w' =>
      match s with
      | SA _ => w
      | SE l _ | SW l =>
          if kd g l && forallb (kd l) kept then relnf_go g kept w'
          else s :: relnf_go g (l :: kept) w'
      end
  end.

Definition relnf (g : lexp) (w : cword) : cword :=
  match w with
  | [] => []
  | s :: w' =>
      match s with
      | SA _ => w
      | SE l _ | SW l => s :: relnf_go g [l] w'
      end
  end.

(** The name [hᵢ] at the start of [w], followed to its value. *)
Fixpoint lookup (h : lexp) (i : nat) (w : cword) : cval :=
  match w with
  | [] => VVar h i
  | s :: w' =>
      match s with
      | SE g v =>
          if lexp_eqb g h then match i with 0 => v | S i' => lookup h i' w' end
          else if kd g h then lookup h i w' else VLook h i (relnf h w)
      | SW g =>
          if lexp_eqb g h then lookup h (S i) w'
          else if kd g h then lookup h i w' else VLook h i (relnf h w)
      | SA _ => VLook h i (relnf h w)
      end
  end.

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
