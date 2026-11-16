(** * The eta pass after [HNorm] (experiment)

    [docs/eta.md].  After the beta normaliser [HNorm], remove what no
    relevant variable can reach:

    - an entry on [h] is dead when, within its segment (since the start
      of the word or the last atom), some weakening on [h] is followed by
      a window that reduces, in the right-angled Artin group of the
      labels (weakening [g], entry [g⁻¹], labels commuting when the
      facts order them), to letters on labels ordered against [h];
    - a dead entry directly followed by a weakening on its label goes
      with it; a weakening directly followed by an entry on its label
      cancels (beta, when a removal made them adjacent); repeated to a
      fixpoint;
    - the dead entries left get the canonical target [·₀];
    - a term's payload without a payload atom matters on named inputs
      only: its bound-label steps before the first atom go ([clean]);
    - payload and lookup words are made normal first.

    Lookup words are treated as whole results here, which is not exact
    ([docs/eta.md]: only what the looked-up variable reaches matters).

    For measuring and testing only: nothing is proved. *)

From Stdlib Require Import String List PArith NArith Bool FMapPositive.
From ShiftedNames.Core Require Import Label Normalise GEval HNorm.
Import ListNotations.

Section Eta.

Variable F : order.

(** ** The group reduction *)

(** [true]: a weakening, [g]; [false]: an entry, [g⁻¹]. *)
Definition letter : Type := (lexp * bool)%type.

Definition letters (l : list step) : list letter :=
  flat_map (fun s => match s with SE h _ => [(h, false)] | SW h => [(h, true)] | SA _ => [] end) l.

(** The partner of [(g, sg)] in [r]: the inverse letter, past letters
    on labels the facts order against [g]. *)
Fixpoint partner (g : lexp) (sg : bool) (r acc : list letter) : option (list letter) :=
  match r with
  | [] => None
  | (g', s') :: r' =>
      if lexp_eqb g g' then (if Bool.eqb sg s' then None else Some (rev acc ++ r'))
      else if kd F g g' then partner g sg r' ((g', s') :: acc)
      else None
  end.

Fixpoint cancel_one (l : list letter) : option (list letter) :=
  match l with
  | [] => None
  | (g, s) :: r =>
      match partner g s r [] with
      | Some r' => Some r'
      | None => option_map (cons (g, s)) (cancel_one r)
      end
  end.

Fixpoint greduce (fuel : nat) (l : list letter) : list letter :=
  match fuel with
  | 0 => l
  | S f => match cancel_one l with Some l' => greduce f l' | None => l end
  end.

(** ** Dead entries *)

(** The steps of [pre] since its last atom. *)
Fixpoint segment (pre acc : list step) : list step :=
  match pre with
  | [] => rev acc
  | SA _ :: r => segment r []
  | s :: r => segment r (s :: acc)
  end.

Definition window_ok (h : lexp) (r : list step) : bool :=
  forallb (fun '(g, _) => negb (lexp_eqb g h) && kd F g h) (greduce (List.length r) (letters r)).

(** [h₀] is unreachable after the segment [seg]. *)
Fixpoint unreach (h : lexp) (seg : list step) : bool :=
  match seg with
  | [] => false
  | SW g :: r => (lexp_eqb g h && window_ok h r) || unreach h r
  | _ :: r => unreach h r
  end.

Definition dead (pre : list step) (h : lexp) : bool := unreach h (segment pre []).

(** ** One pass on a list of steps *)

Fixpoint redex (pre : list step) (w : list step) : option (list step) :=
  match w with
  | [] => None
  | s :: r =>
      let hit := match s, r with
                 | SW h, SE g _ :: r' => if lexp_eqb g h then Some (rev pre ++ r') else None
                 | SE h _, SW g :: r' => if lexp_eqb g h && dead (rev pre) h then Some (rev pre ++ r') else None
                 | _, _ => None
                 end in
      match hit with Some l => Some l | None => redex (s :: pre) r end
  end.

Fixpoint reduce_all (fuel : nat) (w : list step) : list step :=
  match fuel with
  | 0 => w
  | S f => match redex [] w with Some w' => reduce_all f w' | None => w end
  end.

Fixpoint canon_dead (pre w : list step) : list step :=
  match w with
  | [] => []
  | SE h v :: r => (if dead (rev pre) h then SE h (VVar LNone 0) else SE h v) :: canon_dead (SE h v :: pre) r
  | s :: r => s :: canon_dead (s :: pre) r
  end.

(** Named inputs only: the bound-label steps before the first atom go. *)
Fixpoint drop_bound (w : list step) : list step :=
  match w with
  | [] => []
  | SA a :: r => SA a :: r
  | SE LNone _ :: r | SW LNone :: r => drop_bound r
  | s :: r => s :: drop_bound r
  end.

(** ** Over the table *)

Fixpoint steps_of (fuel : nat) (i : positive) (Z : st) : list step :=
  match fuel with
  | 0 => []
  | S f => if Pos.eqb i 1 then [] else
           match PositiveMap.find i (cells Z) with Some (s, t) => s :: steps_of f t Z | None => [] end
  end.

Definition mkey (i : positive) (named : bool) : positive := if named then xI i else xO i.

Fixpoint eta (fuel : nat) (named : bool) (i : positive) (M : PositiveMap.t positive) (Z : st)
  : positive * PositiveMap.t positive * st :=
  match fuel with
  | 0 => (i, M, Z)
  | S f =>
      if Pos.eqb i 1 then (1%positive, M, Z) else
      match PositiveMap.find (mkey i named) M with
      | Some r => (r, M, Z)
      | None =>
          let l := steps_of (Pos.to_nat (next Z)) i Z in
          (* values first *)
          let '(l1, M1, S1) := fold_right (fun s '(acc, M, Z) =>
               match s with
               | SE h (VTerm u b p) =>
                   let '(p', M', Z') := eta f (match b with None => true | Some _ => false end) p M Z in
                   (SE h (VTerm u b p') :: acc, M', Z')
               | SE h (VLook g j x) =>
                   let '(x', M', Z') := eta f false x M Z in (SE h (VLook g j x') :: acc, M', Z')
               | s => (s :: acc, M, Z)
               end) ([], M, Z) l in
          let l2 := if named then drop_bound l1 else l1 in
          let l3 := canon_dead [] (reduce_all (List.length l2) l2) in
          let '(w, S2) := rebuild l3 [] S1 in
          let r := wid w in
          (r, PositiveMap.add (mkey i named) r M1, S2)
      end
  end.

(** Both sides through [HNorm], then the pass, in one table. *)
Definition he_eq (e1 e2 : aexp) : bool :=
  let '(w1, S1) := norm F e1 [] st0 in
  let '(w2, S2) := norm F e2 [] S1 in
  let fu := 2 * Pos.to_nat (next S2) in
  let '(r1, M, S3) := eta fu false (wid w1) (PositiveMap.empty _) S2 in
  let '(r2, _, _) := eta fu false (wid w2) M S3 in
  Pos.eqb r1 r2.

(** The normal-form ids of a list of expressions, in one table. *)
Definition he_ids (es : list aexp) : list positive :=
  let '(ws, Z) := fold_left (fun '(acc, Z) e => let '(w, Z') := norm F e [] Z in (wid w :: acc, Z')) es ([], st0) in
  let fu := 2 * Pos.to_nat (next Z) in
  let '(rs, _, _) := fold_left (fun '(acc, M, Z) w => let '(r, M', Z') := eta fu false w M Z in (r :: acc, M', Z'))
                        (rev ws) ([], PositiveMap.empty _, Z) in
  rev rs.

End Eta.
