(** * Showing [HNorm]'s normal forms

    A normal form is a word whose values are absolute: read at the end
    of the word.  It is shown as an expression ([aexp]) that [names]
    renders as context forms, cell by cell:
    - an entry [h ↦ v] is an input entry with its absolute value over
      the rest of the word: [AInner h t rest];
    - a run of entries whose payload is the rest of the word after the
      run is the form [⟦ hᵢ := uᵢ ⟧] composed with the rest;
    - a weakening or an atom is composed with the rest of the word;
    - the empty word is the identity.
    A cell the expression refers to at least twice (as the rest of a
    word, or as a payload or a lookup) is shown once, as a shared
    definition, unless it is small; the others are shown in place.
    References to shared definitions are atoms numbered from [base].
    The work is linear in the number of cells.

    [HDisplaySound] proves that the expression means the word. *)

From Stdlib Require Import List PArith NArith Bool FMapPositive Arith.
From ShiftedNames.Core Require Import Label Normalise.
From ShiftedNames.Core Require HNorm.
Import ListNotations.
Import HNorm.

Section Display.

Variable T : st.

Definition cell (i : positive) : option (step * positive) := PositiveMap.find i (cells T).

(** ** How often each cell is referred to *)

Definition vrefs (v : val) : list positive := match v with VVar _ _ => [] | VTerm _ _ p => [p] | VLook _ _ x => [x] end.

(** The references of the cell [i]: its rest, and its value's, except a
    payload that is absorbed into a run ([grp], below). *)
Definition srefs (grp : PositiveMap.t positive) (i : positive) (s : step) (t : positive) : list positive :=
  t :: match s with
       | SE _ v => match v, PositiveMap.find i grp with VTerm _ None q, Some q' => if Pos.eqb q q' then [] else vrefs v | _, _ => vrefs v end
       | _ => []
       end.

(** Each cell's references are followed once, when it is first met. *)
Fixpoint count (grp : PositiveMap.t positive) (fuel : nat) (todo : list positive) (c : PositiveMap.t nat) : PositiveMap.t nat :=
  match fuel with
  | 0 => c
  | S f =>
      match todo with
      | [] => c
      | i :: todo' =>
          match PositiveMap.find i c with
          | Some m => count grp f todo' (PositiveMap.add i (S m) c)
          | None =>
              let c' := PositiveMap.add i 1 c in
              match cell i with
              | Some (s, t) => count grp f (srefs grp i s t ++ todo') c'
              | None => count grp f todo' c'
              end
          end
      end
  end.

(** ** Runs of entries sharing the rest as payload

    A run of leading entries [hᵢ ↦ uᵢ⟨p⟩] whose payload is the cell [p]
    just after the run is the form [⟦ hᵢ := uᵢ ⟧] composed with [p].
    [groups] finds where such runs start, in one pass over the cells in
    order (a cell's rest has a smaller id); a run only goes through cells
    referred to once, so each cell is in at most one run.  References
    are counted again with the payloads of runs left out, as a run's form
    does not refer to its payload.  [lead_pay]
    reads the run off the cells, checking it. *)

Definition one (cnt : PositiveMap.t nat) (i : positive) : bool := match PositiveMap.find i cnt with Some 1 => true | _ => false end.

Fixpoint groups (cnt : PositiveMap.t nat) (fuel : nat) (c : positive) (g : PositiveMap.t positive) : PositiveMap.t positive :=
  match fuel with
  | 0 => g
  | S f =>
      let g' := match cell c with
                | Some (SE _ (VTerm _ None q), t) =>
                    if Pos.eqb t q then PositiveMap.add c q g
                    else if one cnt t then
                      match PositiveMap.find t g with
                      | Some q' => if Pos.eqb q q' then PositiveMap.add c q g else g
                      | None => g
                      end
                    else g
                | _ => g
                end in
      groups cnt f (Pos.succ c) g'
  end.

Fixpoint lead_pay (fuel : nat) (j p : positive) : option (list (lexp * nat)) :=
  match fuel with
  | 0 => None
  | S f =>
      if Pos.eqb j p then Some []
      else match cell j with
           | Some (SE h (VTerm u None q), t) => if Pos.eqb q p then option_map (cons (h, u)) (lead_pay f t p) else None
           | _ => None
           end
  end.

(** The form [⟦ hᵢ := uᵢ ⟧]. *)
Definition sform (ts : list (lexp * nat)) : aexp :=
  fold_right (fun '(h, u) a => AInner h (TBindE u (PComp AId PId)) a) AId ts.

(** ** Showing cells *)

Variable base : nat.
Variable shr : bool.
Variable cnt : PositiveMap.t nat.
Variable grp : PositiveMap.t positive.

(** What a cell shown before is shown as ([dmemo]), and the shared
    definitions, latest first, with their cells. *)
Record dstate := mk_dstate { dmemo : PositiveMap.t aexp; ddefs : list (positive * aexp); dn : nat }.

Definition dstart : dstate := mk_dstate (PositiveMap.empty _) [] 0.

(** Whether [d] has at most [n] nodes (looking at most that far). *)
Fixpoint small (n : nat) (d : aexp) : bool :=
  match n with
  | 0 => false
  | S n =>
      match d with
      | AId | AAtom _ => true
      | ACompose a b => small n a && small n b
      | AOuter _ a | ALift _ a => small n a
      | AInner _ (TVarE _ _) a => small n a
      | AInner _ _ _ => false
      end
  end.

(** A definition too small to be worth sharing: it is shown where it is
    used. *)
Definition trivial (d : aexp) : bool := small 3 d.

Definition acomp (r x : aexp) : aexp := match r with AId => x | _ => ACompose r x end.

Definition many (i : positive) : bool := match PositiveMap.find i cnt with Some (S (S _)) => true | _ => false end.

Fixpoint dref (fuel : nat) (i : positive) (D : dstate) {struct fuel} : option (aexp * dstate) :=
  match fuel with
  | 0 => None
  | S f =>
      match PositiveMap.find i (dmemo D) with
      | Some r => Some (r, D)
      | None =>
          match dbody f i D with
          | Some (d, D1) =>
              match PositiveMap.find i (dmemo D1) with
              | Some r => Some (r, D1)
              | None =>
                  if many i then
                    if shr && negb (trivial d) then
                      let r := AAtom (base + dn D1) in
                      Some (r, mk_dstate (PositiveMap.add i r (dmemo D1)) ((i, d) :: ddefs D1) (S (dn D1)))
                    else Some (d, mk_dstate (PositiveMap.add i d (dmemo D1)) (ddefs D1) (dn D1))
                  else Some (d, D1)
              end
          | None => None
          end
      end
  end
with dbody (fuel : nat) (i : positive) (D : dstate) {struct fuel} : option (aexp * dstate) :=
  match fuel with
  | 0 => None
  | S f =>
      match cell i with
      | None => Some (AId, D)
      | Some (SA a, t) => match dref f t D with Some (r, D1) => Some (acomp r (AAtom a), D1) | None => None end
      | Some (SW h, t) => match dref f t D with Some (r, D1) => Some (acomp r (AOuter h AId), D1) | None => None end
      | Some (SE h v, t) =>
          match match PositiveMap.find i grp with Some p => match lead_pay f i p with Some ((_ :: _) as ts) => Some (ts, p) | _ => None end | None => None end with
          | Some (ts, p) => match dref f p D with Some (r, D1) => Some (acomp r (sform ts), D1) | None => None end
          | None =>
              match dval f v D with
              | Some (tv, D1) => match dref f t D1 with Some (r, D2) => Some (AInner h tv r, D2) | None => None end
              | None => None
              end
          end
      end
  end
with dval (fuel : nat) (v : val) (D : dstate) {struct fuel} : option (texp * dstate) :=
  match fuel with
  | 0 => None
  | S f =>
      match v with
      | VVar g j => Some (TVarE g j, D)
      | VTerm u None p => match dref f p D with Some (r, D1) => Some (TBindE u (PComp r PId), D1) | None => None end
      | VLook g j x => match dref f x D with Some (r, D1) => Some (TLookE g j r, D1) | None => None end
      | VTerm _ (Some _) _ => None
      end
  end.

End Display.

(** ** Compositions nested to the left, as [⨾] is read: [(a ⨾ b) ⨾ c] *)

Fixpoint lassoc (d : aexp) : aexp :=
  match d with
  | AId => AId
  | AAtom n => AAtom n
  | ACompose a b => lassoc_to a (lassoc b)
  | AOuter h a => AOuter h (lassoc a)
  | AInner h t a => AInner h (tlassoc t) (lassoc a)
  | ALift h a => ALift h (lassoc a)
  end
(** [lassoc_to d y] is [ACompose (lassoc d) y], renested. *)
with lassoc_to (d : aexp) (y : aexp) : aexp :=
  match d with
  | ACompose a b => lassoc_to a (lassoc_to b y)
  | AId => ACompose AId y
  | AAtom n => ACompose (AAtom n) y
  | AOuter h a => ACompose (AOuter h (lassoc a)) y
  | AInner h t a => ACompose (AInner h (tlassoc t) (lassoc a)) y
  | ALift h a => ACompose (ALift h (lassoc a)) y
  end
with tlassoc (t : texp) : texp :=
  match t with
  | TVarE h i => TVarE h i
  | TBindE u p => TBindE u (plassoc p)
  | TShiftE h t => TShiftE h (tlassoc t)
  | TLookE h i a => TLookE h i (lassoc a)
  end
with plassoc (p : pexp) : pexp :=
  match p with
  | PId => PId
  | PAtom n => PAtom n
  | PComp a p => PComp (lassoc a) (plassoc p)
  | PShift h p => PShift h (plassoc p)
  end.

(** Showing the word from the cell [i]: shared definitions, numbered
    from [base], and the expression; with [shr] false, nothing is
    shared. *)
Definition display_s (F : order) (base : nat) (shr : bool) (T : st) (i : positive) : option (list aexp * aexp) :=
  let fuel := 4 * Pos.to_nat (next T) + 16 in
  let cnt0 := count T (PositiveMap.empty _) fuel [i] (PositiveMap.empty _) in
  let grp := groups T cnt0 (Pos.to_nat (next T)) 2 (PositiveMap.empty _) in
  let cnt := count T grp fuel [i] (PositiveMap.empty _) in
  match dref T base shr cnt grp fuel i dstart with
  | Some (r, D) => Some (map (fun d => lassoc (snd d)) (rev (ddefs D)), lassoc r)
  | None => None
  end.

Definition display (F : order) (base : nat) := display_s F base true.
