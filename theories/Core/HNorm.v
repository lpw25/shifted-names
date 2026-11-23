(** * A simple hash-consed normaliser (experiment)

    The normal form is a sorted, reduced word of steps, stored as a
    hash-consed linked list ([docs/nf-design.md]):
    - [SE h v]: an input entry on [h] with the absolute value [v];
    - [SW h]: a weakening on [h];
    - [SA a]: an adjustment atom.
    Values are absolute: a variable of the scope at the end of the word,
    a term with its payload word, or a lookup stuck at the first step of
    a word.

    Expressions are normalised from right to left: each construct is
    pushed onto the word for what comes after it.  Entries and weakenings
    walk down the word to cancel, be absorbed, or be inserted in sorted
    order; the cells in front of the edit are rebuilt, the rest is
    shared.

    A lookup that cannot get past a step gives the variable with the
    steps that can affect it as its payload ([follow]), as [CNorm] does; [HRefine] proves that the two compute the same
    normal forms, so [hn_eq] decides equality in comprehension models
    ([Comp]). *)

From Stdlib Require Import String List PArith NArith Bool FMapPositive.
From ShiftedNames.Core Require Import Label Normalise.
Import ListNotations.

Inductive val : Type :=
| VVar (h : lexp) (i : nat)
| VTerm (u : nat) (p : positive)
| VLook (h : lexp) (i : nat) (x : positive).

Inductive step : Type :=
| SE (h : lexp) (v : val)
| SW (h : lexp)
| SA (a : nat).

Definition val_eqb (a b : val) : bool :=
  match a, b with
  | VVar h i, VVar h' i' => lexp_eqb h h' && Nat.eqb i i'
  | VTerm u p, VTerm u' p' => Nat.eqb u u' && Pos.eqb p p'
  | VLook h i x, VLook h' i' x' => lexp_eqb h h' && Nat.eqb i i' && Pos.eqb x x'
  | _, _ => false
  end.

Definition step_eqb (a b : step) : bool :=
  match a, b with
  | SE h v, SE h' v' => lexp_eqb h h' && val_eqb v v'
  | SW h, SW h' => lexp_eqb h h'
  | SA a, SA a' => Nat.eqb a a'
  | _, _ => false
  end.

(** A word: each cell carries its step and the id of the word that
    starts there.  The empty word has id 1. *)
Definition word : Type := list (step * positive).

Definition wid (w : word) : positive := match w with [] => 1 | (_, i) :: _ => i end.

(** The hash-consing table: for each tail id, the cells built on it. *)
Record st : Type := mk_st { tab : PositiveMap.t (list (step * positive)); cells : PositiveMap.t (step * positive); next : positive }.

Definition st0 : st := mk_st (PositiveMap.empty _) (PositiveMap.empty _) 2.

Definition hcons (s : step) (w : word) (S : st) : word * st :=
  let t := wid w in
  let bucket := match PositiveMap.find t (tab S) with Some l => l | None => [] end in
  match find (fun p => step_eqb (fst p) s) bucket with
  | Some (_, i) => ((s, i) :: w, S)
  | None =>
      let i := next S in
      ((s, i) :: w, mk_st (PositiveMap.add t ((s, i) :: bucket) (tab S)) (PositiveMap.add i (s, t) (cells S)) (Pos.succ i))
  end.

(** Put the steps of [pre] (in order) back in front of [w]. *)
Fixpoint rebuild (pre : list step) (w : word) (S : st) : word * st :=
  match pre with
  | [] => (w, S)
  | s :: pre' => let '(w', S') := rebuild pre' w S in hcons s w' S'
  end.

Section Norm.

Variable F : order.

(** Labels the facts show distinct. *)
Definition kd (a b : lexp) : bool := match lcmp F a b with Some Lt | Some Gt => true | _ => false end.

(** [a] sorts before [b]. *)
Definition before (a b : lexp) : bool := match lcmp F a b with Some Lt => true | _ => false end.

(** ** Following a variable

    As [CNorm.follow]: [hᵢ] is followed through [w], first step first.  A
    step that cannot affect it is passed: one on a label known distinct
    from [h] and sorting after the label of every step kept so far.  Until a step
    is kept, a step on [h] moves the index or gives the value.  Any other
    step is kept, and the value is then [hᵢ] with the kept steps as its
    payload, hash-consed; an atom is kept with the rest of the word.
    The kept steps since the last step not kept are shared, as they
    stand in the word ([mark]).  [kept] is in reverse order. *)

(** A step is passed when its label is known distinct from [h] and
    sorts after every kept label: after every label of the frontier
    [fr], the maximal kept labels.  They are mutually unordered, so there
    are never more of them than the width of the order.  Labels kept
    since a step was last tested wait in [pend], and are merged into the
    frontier only when a step on a label known distinct from [h] has to
    be tested, so a lookup that tests none pays nothing for them.
    Written with [if]: [vm_compute] evaluates both sides of [&&]. *)

(** [y] kept: the frontier labels below [y] go, and [y] joins unless it
    is below or equal to one of them; one comparison per frontier label
    ([None]: [y] is absorbed). *)
Fixpoint addf_go (y : lexp) (fr : list lexp) : option (list lexp) :=
  match fr with
  | [] => Some []
  | m :: r =>
      match lcmp F y m with
      | Some Eq | Some Lt => None
      | Some Gt => addf_go y r
      | None => match addf_go y r with Some r' => Some (m :: r') | None => None end
      end
  end.

Definition addf (y : lexp) (fr : list lexp) : list lexp :=
  match addf_go y fr with Some r => y :: r | None => fr end.

Fixpoint mergef (pend fr : list lexp) : list lexp :=
  match pend with [] => fr | y :: p => mergef p (addf y fr) end.

(** Whether a step on [l] is passed, with the new frontier and pending
    labels. *)
Definition decide (h l : lexp) (fr pend : list lexp) : bool * list lexp * list lexp :=
  if kd h l then let fr' := mergef pend fr in (forallb (fun m => before m l) fr', fr', []) else (false, fr, pend).

(** The payload: the kept steps up to [mark], rebuilt, on [mark], which
    is shared: [mark] starts with the last [n] kept steps. *)
Definition payload (h : lexp) (i : nat) (kept : list step) (n : nat) (mark : word) (Z : st) : val * st :=
  let '(r, S1) := rebuild (rev (skipn n kept)) mark Z in (VLook h i (wid r), S1).

(** [mark] is the word from the first of the last [n] kept steps, all
    contiguous; it moves on past every step that is not kept. *)
Fixpoint follow (h : lexp) (i : nat) (kept : list step) (fr pend : list lexp) (n : nat) (mark : word) (w : word)
  (Z : st) : val * st :=
  match w with
  | [] => match kept with [] => (VVar h i, Z) | _ => payload h i kept n mark Z end
  | (s, _) :: w' =>
      match s with
      | SE g v =>
          let '(p, fr1, pend1) := decide h g fr pend in
          if p then follow h i kept fr1 pend1 0 w' w' Z
          else match kept with
               | [] => if lexp_eqb g h then match i with 0 => (v, Z) | S i' => follow h i' [] [] [] 0 w' w' Z end
                       else follow h i [s] [] [g] 1 mark w' Z
               | _ => follow h i (s :: kept) fr1 (g :: pend1) (S n) mark w' Z
               end
      | SW g =>
          let '(p, fr1, pend1) := decide h g fr pend in
          if p then follow h i kept fr1 pend1 0 w' w' Z
          else match kept with
               | [] => if lexp_eqb g h then follow h (S i) [] [] [] 0 w' w' Z else follow h i [s] [] [g] 1 mark w' Z
               | _ => follow h i (s :: kept) fr1 (g :: pend1) (S n) mark w' Z
               end
      | SA _ => payload h i kept n mark Z
      end
  end.

(** The variable [hᵢ] at the start of [w], followed to its value. *)
Definition lookup (h : lexp) (i : nat) (w : word) (Z : st) : val * st := follow h i [] [] [] 0 w w Z.

(** Where a step on [h] stops: the steps it passes and the rest,
    starting at the stopping step.  It passes steps on labels that sort
    before [h].  It stops at a step on [h], on a label not known
    distinct from [h], at an atom, or at a step on a label that sorts
    after [h]: in a sorted word no step on [h] can follow that one
    while every step in between is known distinct from [h] (the
    argument that sorted words are unique).  So the steps passed are
    exactly the ones a new step on [h] is inserted after. *)
Fixpoint stop (h : lexp) (w : word) : list step * word :=
  match w with
  | [] => ([], [])
  | (s, _) :: w' =>
      match s with
      | SE g _ | SW g =>
          if before g h then let '(p, r) := stop h w' in (s :: p, r) else ([], w)
      | SA _ => ([], w)
      end
  end.

(** Sorted position for a new step on [h]: past steps on labels known
    distinct from [h] that sort before it. *)
Fixpoint sorted_at (h : lexp) (w : word) : list step * word :=
  match w with
  | [] => ([], [])
  | (s, _) :: w' =>
      match s with
      | SE g _ | SW g =>
          if before g h then let '(p, r) := sorted_at h w' in (s :: p, r) else ([], w)
      | SA _ => ([], w)
      end
  end.

Definition insert (s : step) (h : lexp) (w : word) (S : st) : word * st :=
  let '(p, r) := sorted_at h w in
  let '(r', S1) := hcons s r S in
  rebuild p r' S1.

(** A weakening on [h] in front of [w]: it cancels against the first
    entry on [h] it reaches, or stays, in sorted position. *)
Definition place (s : step) (p : list step) (r : word) (S : st) : word * st :=
  let '(r', S1) := hcons s r S in rebuild p r' S1.

Definition pushW (h : lexp) (w : word) (S : st) : word * st :=
  match stop h w with
  | (p, (SE g _, _) :: r) as pr => if lexp_eqb g h then rebuild p r S else place (SW h) p (snd pr) S
  | (p, r) => place (SW h) p r S
  end.

(** An entry on [h] in front of [w]: it is absorbed by a weakening on
    [h] it reaches when its value is what the rest gives [h₀];
    otherwise it is inserted in sorted position. *)
Definition pushE (h : lexp) (v : val) (w : word) (S : st) : word * st :=
  match stop h w with
  | (p, (SW g, _) :: r) as pr =>
      if lexp_eqb g h then
        let '(v', S1) := lookup h 0 r S in
        if val_eqb v v' then rebuild p r S1 else place (SE h v) p (snd pr) S1
      else place (SE h v) p (snd pr) S
  | (p, r) => place (SE h v) p r S
  end.

(** [norm e K]: [e], then the word [K]. *)
Fixpoint norm (e : aexp) (K : word) (S : st) {struct e} : word * st :=
  match e with
  | AId => (K, S)
  | AAtom n => hcons (SA n) K S
  | ACompose a b => let '(K1, S1) := norm a K S in norm b K1 S1
  | AOuter h a => let '(K1, S1) := pushW h K S in norm a K1 S1
  | AInner h t a =>
      let '(v, S1) := tval t K S in
      let '(K1, S2) := norm a K S1 in
      pushE h v K1 S2
  | ALift h a =>
      let '(v, S0) := lookup h 0 K S in
      let '(K1, S1) := pushW h K S0 in
      let '(K2, S2) := norm a K1 S1 in
      pushE h v K2 S2
  end
with tval (t : texp) (K : word) (S : st) {struct t} : val * st :=
  match t with
  | TVarE h i => lookup h i K S
  | TBindE u p => let '(P, S1) := norm p K S in (VTerm u (wid P), S1)
  | TShiftE h t' => let '(K1, S1) := pushW h K S in tval t' K1 S1
  | TLookE h i a => let '(K1, S1) := norm a K S in lookup h i K1 S1
  end.

(** ** With shared definitions

    [normD]: [norm], with the atoms that [defs] defines standing for
    their definitions (as [Normalise.Exp] expands them).  A definition
    followed by a word [K] is normalised once: the result is kept by
    the definition and [K]'s cell. *)
Section Defs.

Variable defs : list (option aexp).

Definition dmemo := PositiveMap.t (PositiveMap.t word).

Definition mget (m : dmemo) (k i : positive) : option word :=
  match PositiveMap.find k m with Some mk => PositiveMap.find i mk | None => None end.

Definition mput (m : dmemo) (k i : positive) (w : word) : dmemo :=
  PositiveMap.add k (PositiveMap.add i w (match PositiveMap.find k m with Some mk => mk | None => PositiveMap.empty _ end)) m.

Fixpoint normD (fuel : nat) (e : aexp) (K : word) (S : st) (m : dmemo) {struct fuel} : option (word * st * dmemo) :=
  match fuel with
  | 0 => None
  | S f =>
      match e with
      | AId => Some (K, S, m)
      | AAtom n =>
          match nth n defs None with
          | Some d =>
              let k := Pos.of_succ_nat n in
              match mget m k (wid K) with
              | Some w => Some (w, S, m)
              | None =>
                  match normD f d K S m with
                  | Some (w, S1, m1) => Some (w, S1, mput m1 k (wid K) w)
                  | None => None
                  end
              end
          | None => let '(w, S1) := hcons (SA n) K S in Some (w, S1, m)
          end
      | ACompose a b =>
          match normD f a K S m with Some (K1, S1, m1) => normD f b K1 S1 m1 | None => None end
      | AOuter h a => let '(K1, S1) := pushW h K S in normD f a K1 S1 m
      | AInner h t a =>
          match tvalD f t K S m with
          | Some (v, S1, m1) =>
              match normD f a K S1 m1 with
              | Some (K1, S2, m2) => let '(w, S3) := pushE h v K1 S2 in Some (w, S3, m2)
              | None => None
              end
          | None => None
          end
      | ALift h a =>
          let '(v, S0) := lookup h 0 K S in
          let '(K1, S1) := pushW h K S0 in
          match normD f a K1 S1 m with
          | Some (K2, S2, m2) => let '(w, S3) := pushE h v K2 S2 in Some (w, S3, m2)
          | None => None
          end
      end
  end
with tvalD (fuel : nat) (t : texp) (K : word) (S : st) (m : dmemo) {struct fuel} : option (val * st * dmemo) :=
  match fuel with
  | 0 => None
  | S f =>
      match t with
      | TVarE h i => let '(v, S1) := lookup h i K S in Some (v, S1, m)
      | TBindE u p =>
          match normD f p K S m with
          | Some (P, S1, m1) => Some (VTerm u (wid P), S1, m1)
          | None => None
          end
      | TShiftE h t' => let '(K1, S1) := pushW h K S in tvalD f t' K1 S1 m
      | TLookE h i a =>
          match normD f a K S m with
          | Some (K1, S1, m1) => let '(v, S2) := lookup h i K1 S1 in Some (v, S2, m1)
          | None => None
          end
      end
  end.

End Defs.

(** The decision: both sides normalised against one table. *)
Definition hn_eq (e1 e2 : aexp) : bool :=
  let '(w1, S1) := norm e1 [] st0 in
  let '(w2, _) := norm e2 [] S1 in
  Pos.eqb (wid w1) (wid w2).

End Norm.

(** ** Size of the output

    The number of distinct cells reachable from a word, through tails
    and through the words that values refer to. *)

Definition val_refs (v : val) : list positive :=
  match v with VVar _ _ => [] | VTerm _ p => [p] | VLook _ _ x => [x] end.

Definition step_refs (s : step) : list positive := match s with SE _ v => val_refs v | _ => [] end.

Fixpoint reach (fuel : nat) (T : st) (todo : list positive) (seen : PositiveMap.t unit) (n : N) : N :=
  match fuel with
  | 0 => n
  | S fuel' =>
      match todo with
      | [] => n
      | i :: todo' =>
          if Pos.eqb i 1 then reach fuel' T todo' seen n
          else match PositiveMap.find i seen with
               | Some _ => reach fuel' T todo' seen n
               | None =>
                   match PositiveMap.find i (cells T) with
                   | Some (s, t) => reach fuel' T (t :: step_refs s ++ todo') (PositiveMap.add i tt seen) (N.succ n)
                   | None => reach fuel' T todo' seen n
                   end
               end
      end
  end.

Definition hsize (F : order) (e : aexp) : N * N :=
  let '(w, T) := norm F e [] st0 in
  (reach (2 * Pos.to_nat (next T)) T [wid w] (PositiveMap.empty _) 0, N.pos (next T)).

(** ** Normalising a normal form again

    What the tactic does on its own output.  A word is printed with one
    [share] per cell: a step in front of a reference to the word after
    it, and term payloads and stuck lookups referring to their words.
    Normalising that expression meets each reference once (the
    continuation is always the empty word, since values are absolute),
    so it amounts to rebuilding each reachable cell once, pushing its
    step onto the rebuilt word after it. *)

Section Renorm.

Variable F : order.

Variable src : PositiveMap.t (step * positive).

Fixpoint renorm (fuel : nat) (i : positive) (M : PositiveMap.t word) (T : st) {struct fuel}
  : word * PositiveMap.t word * st :=
  if Pos.eqb i 1 then ([], M, T) else
  match PositiveMap.find (xO i) M with
  | Some w => (w, M, T)
  | None =>
      match fuel with
      | 0 => ([], M, T)
      | S f =>
          match PositiveMap.find i src with
          | None => ([], M, T)
          | Some (s, t) =>
              let '(wt, M1, S1) := renorm f t M T in
              let '(w, M2, S2) :=
                match s with
                | SE h v =>
                    let '(v', M2, S2) :=
                      match v with
                      | VVar _ _ => (v, M1, S1)
                      | VTerm u p =>
                          let '(wp, M2, S2) := renorm f p M1 S1 in
                          (VTerm u (wid wp), M2, S2)
                      | VLook g j x =>
                          let '(wx, M2, S2) := renorm f x M1 S1 in
                          let '(v', S3) := lookup F g j wx S2 in
                          (v', M2, S3)
                      end in
                    let '(w, S3) := pushE F h v' wt S2 in (w, M2, S3)
                | SW h => let '(w, S2) := pushW F h wt S1 in (w, M1, S2)
                | SA a => let '(w, S2) := hcons (SA a) wt S1 in (w, M1, S2)
                end in
              (w, PositiveMap.add (xO i) w M2, S2)
          end
      end
  end.

(** Normalise both sides, then normalise both results again.  The
    second component says whether normalising again gave back the same
    words (idempotence). *)
End Renorm.

(** The cells reachable from some roots: what a printed normal form
    holds, without the rest of the table. *)
Fixpoint prune (fuel : nat) (T : st) (todo : list positive) (acc : PositiveMap.t (step * positive)) : PositiveMap.t (step * positive) :=
  match fuel with
  | 0 => acc
  | S fuel' =>
      match todo with
      | [] => acc
      | i :: todo' =>
          if Pos.eqb i 1 then prune fuel' T todo' acc
          else match PositiveMap.find i acc with
               | Some _ => prune fuel' T todo' acc
               | None =>
                   match PositiveMap.find i (cells T) with
                   | Some (s, t) => prune fuel' T (t :: step_refs s ++ todo') (PositiveMap.add i (s, t) acc)
                   | None => prune fuel' T todo' acc
                   end
               end
      end
  end.

(** Normalise both sides, keeping only the reachable cells. *)
Definition norm_both (F : order) (e1 e2 : aexp) : word * word * PositiveMap.t (step * positive) * positive :=
  let '(w1, S1) := norm F e1 [] st0 in
  let '(w2, S2) := norm F e2 [] S1 in
  (w1, w2, prune (2 * Pos.to_nat (next S2)) S2 [wid w1; wid w2] (PositiveMap.empty _), next S2).

(** Normalise the two results again, on a fresh table.  The first
    component says whether they are still equal; the second whether
    each came back as the same word (compared on the fresh table, by
    renormalising once more and checking the ids are stable). *)
Definition renorm_both (F : order) (r : word * word * PositiveMap.t (step * positive) * positive) : bool * bool :=
  let '(w1, w2, C, nx) := r in
  let fuel := Pos.to_nat nx in
  let '(v1, M1, S1) := renorm F C fuel (wid w1) (PositiveMap.empty _) st0 in
  let '(v2, _, S2) := renorm F C fuel (wid w2) M1 S1 in
  let C2 := cells S2 in
  let '(u1, N1, S3) := renorm F C2 fuel (wid v1) (PositiveMap.empty _) S2 in
  let '(u2, _, _) := renorm F C2 fuel (wid v2) N1 S3 in
  (Pos.eqb (wid v1) (wid v2), Pos.eqb (wid u1) (wid v1) && Pos.eqb (wid u2) (wid v2)).

(** Only the first pass, for timing. *)
Definition renorm_eq (F : order) (r : word * word * PositiveMap.t (step * positive) * positive) : bool :=
  let '(w1, w2, C, nx) := r in
  let fuel := Pos.to_nat nx in
  let '(v1, M1, S1) := renorm F C fuel (wid w1) (PositiveMap.empty _) st0 in
  let '(v2, _, _) := renorm F C fuel (wid w2) M1 S1 in
  Pos.eqb (wid v1) (wid v2).
