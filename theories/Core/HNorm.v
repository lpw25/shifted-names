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

    A stuck lookup keeps only the steps that can affect it ([relnf]),
    as [CNorm] does; [HRefine] proves that the two compute the same
    normal forms, so [hn_eq] decides equality in comprehension models
    ([Comp]). *)

From Stdlib Require Import String List PArith NArith Bool FMapPositive.
From ShiftedNames.Core Require Import Label Normalise GEval.
Import ListNotations.

Inductive val : Type :=
| VVar (h : lexp) (i : nat)
| VTerm (u : nat) (b : option nat) (p : positive)
| VLook (h : lexp) (i : nat) (x : positive).

Inductive step : Type :=
| SE (h : lexp) (v : val)
| SW (h : lexp)
| SA (a : nat).

Definition oeqb (a b : option nat) : bool :=
  match a, b with Some x, Some y => Nat.eqb x y | None, None => true | _, _ => false end.

Definition val_eqb (a b : val) : bool :=
  match a, b with
  | VVar h i, VVar h' i' => lexp_eqb h h' && Nat.eqb i i'
  | VTerm u b p, VTerm u' b' p' => Nat.eqb u u' && oeqb b b' && Pos.eqb p p'
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

(** A lookup of [g] stuck at the first step of [w] keeps only the steps
    that can affect it ([CNorm.relnf]): a later step on a label known
    distinct from [g] that commutes with every step kept before it is
    dropped.  [relnf_go] gives the kept steps after the first change, to
    put back on the rest, which is shared. *)
Fixpoint relnf_go (g : lexp) (kept : list lexp) (w : word) : list step * word :=
  match w with
  | [] => ([], [])
  | (s, _) :: w' =>
      match s with
      | SA _ => ([], w)
      | SE l _ | SW l =>
          if kd g l && forallb (kd l) kept then relnf_go g kept w'
          else let '(p, b) := relnf_go g (l :: kept) w' in
               match p with
               | [] => if Pos.eqb (wid b) (wid w') then ([], w) else ([s], b)
               | _ => (s :: p, b)
               end
      end
  end.

Definition relnf (g : lexp) (w : word) (S : st) : word * st :=
  match w with
  | [] => ([], S)
  | (s, _) :: w' =>
      match s with
      | SA _ => (w, S)
      | SE l _ | SW l =>
          let '(p, b) := relnf_go g [l] w' in
          match p with
          | [] => if Pos.eqb (wid b) (wid w') then (w, S) else rebuild [s] b S
          | _ => rebuild (s :: p) b S
          end
      end
  end.

(** The variable [hᵢ] at the start of [w], followed to its value. *)
Fixpoint lookup (h : lexp) (i : nat) (w : word) (Z : st) : val * st :=
  match w with
  | [] => (VVar h i, Z)
  | (s, x) :: w' =>
      match s with
      | SE g v =>
          if lexp_eqb g h then match i with 0 => (v, Z) | S i' => lookup h i' w' Z end
          else if kd g h then lookup h i w' Z
          else let '(r, S1) := relnf h w Z in (VLook h i (wid r), S1)
      | SW g =>
          if lexp_eqb g h then lookup h (S i) w' Z
          else if kd g h then lookup h i w' Z
          else let '(r, S1) := relnf h w Z in (VLook h i (wid r), S1)
      | SA _ => let '(r, S1) := relnf h w Z in (VLook h i (wid r), S1)
      end
  end.

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

(** A payload with no payload atom only sees named variables: bound-label
    steps before its first atom are dropped. *)
Fixpoint unbound (w : word) : list step * word :=
  match w with
  | [] => ([], [])
  | (s, _) :: w' =>
      match s with
      | SE LNone _ | SW LNone => unbound w'
      | SA _ => ([], w)
      | _ => let '(p, r) := unbound w' in (s :: p, r)
      end
  end.

Fixpoint has_unbound (w : word) : bool :=
  match w with
  | [] => false
  | (s, _) :: w' => match s with SE LNone _ | SW LNone => true | SA _ => false | _ => has_unbound w' end
  end.

Definition clean (b : option nat) (w : word) (S : st) : word * st :=
  match b with
  | Some _ => (w, S)
  | None => if has_unbound w then let '(p, r) := unbound w in rebuild p r S else (w, S)
  end.

Fixpoint is_bind (t : texp) : bool := match t with TBindE _ _ => true | TShiftE _ t => is_bind t | _ => false end.

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
  | TBindE u p =>
      let '(P, S1) := pnorm p K S in
      let '(P', S2) := clean (fpb p) P S1 in
      (VTerm u (fpb p) (wid P'), S2)
  | TShiftE h t' =>
      if is_bind t' then tval t' K S
      else let '(K1, S1) := pushW h K S in tval t' K1 S1
  end
with pnorm (p : pexp) (K : word) (S : st) {struct p} : word * st :=
  match p with
  | PId | PAtom _ => (K, S)
  | PComp a p' => let '(K1, S1) := norm a K S in pnorm p' K1 S1
  | PShift h p' => let '(K1, S1) := pushW h K S in pnorm p' K1 S1
  end.

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
  match v with VVar _ _ => [] | VTerm _ _ p => [p] | VLook _ _ x => [x] end.

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
                      | VTerm u b p =>
                          (* the cleaned payload is memoised under the
                             cell's own key with the low bit set, so each
                             payload is scanned once *)
                          match b, PositiveMap.find (xI p) M1 with
                          | None, Some wc => (VTerm u b (wid wc), M1, S1)
                          | _, _ =>
                              let '(wp, M2, S2) := renorm f p M1 S1 in
                              let '(wp', S3) := clean b wp S2 in
                              (VTerm u b (wid wp'), PositiveMap.add (xI p) wp' M2, S3)
                          end
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
