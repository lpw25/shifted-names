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
    - the steps are pushed back through [HNorm], since a removal can
      leave steps on ordered labels out of order, and all of this is
      repeated until nothing changes;
    - a term's payload without a payload atom matters on named inputs
      only: its bound-label steps before the first atom go ([clean]);
    - payload and lookup words are made normal first.

    A stuck lookup's word is kept whole: in zero-set models
    ([docs/zero-sets.md]) steps on labels ordered against the looked-up
    label can move it.

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

Fixpoint canon_dead (pre w : list step) : list step :=
  match w with
  | [] => []
  | SE h v :: r => (if dead (rev pre) h then SE h (VVar LNone 0) else SE h v) :: canon_dead (SE h v :: pre) r
  | s :: r => s :: canon_dead (s :: pre) r
  end.

(** ** Which inputs matter

    [All]: every input; [Named]: named inputs (a term's payload without
    a payload atom); [One h]: one variable of [h] (a stuck lookup).
    Before the first atom, a step on a label that every label the
    inputs could be on is ordered against can never be reached: it
    goes.  A label becomes possible once a step on it comes while the
    walk may be on a label not ordered against it. *)

Inductive mode : Type := All | Named | One (h : lexp).

Definition mode_eqb (a b : mode) : bool :=
  match a, b with All, All | Named, Named => true | One h, One g => lexp_eqb h g | _, _ => false end.

Definition reachable_from (R : list lexp) (named : bool) (l : lexp) : bool :=
  (if named then negb (lexp_eqb l LNone) else false)
  || existsb (fun r => lexp_eqb r l || negb (kd F r l)) R.

Fixpoint restrict (R : list lexp) (named : bool) (w : list step) : list step :=
  match w with
  | [] => []
  | SA a :: r => SA a :: r
  | s :: r =>
      let l := match s with SE h _ | SW h => h | SA _ => LNone end in
      if reachable_from R named l then s :: restrict (l :: R) named r else restrict R named r
  end.

(** In zero-set models ([docs/zero-sets.md]) steps on labels ordered
    against [h] can move a variable of [h], so a stuck lookup's word
    keeps them: [One h] restricts nothing. *)
Definition restrict_mode (m : mode) (w : list step) : list step :=
  match m with All | One _ => w | Named => restrict [] true w end.

(** ** Over the table *)

Fixpoint steps_of (fuel : nat) (i : positive) (Z : st) : list step :=
  match fuel with
  | 0 => []
  | S f => if Pos.eqb i 1 then [] else
           match PositiveMap.find i (cells Z) with Some (s, t) => s :: steps_of f t Z | None => [] end
  end.

Definition mfind (i : positive) (m : mode) (M : PositiveMap.t (list (mode * positive))) : option positive :=
  match PositiveMap.find i M with
  | Some l => option_map snd (find (fun '(m', _) => mode_eqb m m') l)
  | None => None
  end.

Definition madd (i : positive) (m : mode) (r : positive) (M : PositiveMap.t (list (mode * positive))) :=
  PositiveMap.add i ((m, r) :: match PositiveMap.find i M with Some l => l | None => [] end) M.

Definition vmode (b : option nat) : mode := match b with None => Named | Some _ => All end.

(** Push steps back through [HNorm]: removing a pair can leave steps on
    ordered labels out of order ([docs/normal-form.md]). *)
Definition repush (l : list step) (Z : st) : word * st :=
  fold_right (fun s '(w, Z) =>
    match s with SE h v => pushE F h v w Z | SW h => pushW F h w Z | SA a => hcons (SA a) w Z end) ([], Z) l.

Fixpoint steps_eqb (a b : list step) : bool :=
  match a, b with
  | [], [] => true
  | s :: a', t :: b' => step_eqb s t && steps_eqb a' b'
  | _, _ => false
  end.

Fixpoint eta (fuel : nat) (m : mode) (i : positive) (M : PositiveMap.t (list (mode * positive))) (Z : st)
  : positive * PositiveMap.t (list (mode * positive)) * st :=
  match fuel with
  | 0 => (i, M, Z)
  | S f =>
      if Pos.eqb i 1 then (1%positive, M, Z) else
      match mfind i m M with
      | Some r => (r, M, Z)
      | None =>
          let l := steps_of (Pos.to_nat (next Z)) i Z in
          let '(l1, M1, Z1) := fold_right (fun s '(acc, M, Z) =>
               let '(s', M', Z') := estep f s M Z in (s' :: acc, M', Z')) ([], M, Z) l in
          let l2 := restrict_mode m l1 in
          let '(l5, M2, Z2) := settle f (List.length l2) l2 M1 Z1 in
          let '(w, Z3) := rebuild l5 [] Z2 in
          let r := wid w in
          (r, madd i m r M2, Z3)
      end
  end
(** Remove pairs, give dead entries the canonical target, push back
    through [HNorm], until nothing changes. *)
with settle (fuel : nat) (n : nat) (l : list step) (M : PositiveMap.t (list (mode * positive))) (Z : st)
  : list step * PositiveMap.t (list (mode * positive)) * st :=
  match fuel with
  | 0 => (l, M, Z)
  | S f =>
      let '(l3, M1, Z1) := reduce_all f (List.length l) l M Z in
      let l4 := canon_dead [] l3 in
      let '(w, Z2) := repush l4 Z1 in
      let l5 := steps_of (Pos.to_nat (next Z2)) (wid w) Z2 in
      match n with
      | 0 => (l5, M1, Z2)
      | S n' => if steps_eqb l5 l then (l5, M1, Z2) else settle f n' l5 M1 Z2
      end
  end
with estep (fuel : nat) (s : step) (M : PositiveMap.t (list (mode * positive))) (Z : st)
  : step * PositiveMap.t (list (mode * positive)) * st :=
  match fuel with
  | 0 => (s, M, Z)
  | S f =>
      match s with
      | SE h v => let '(v', M', Z') := eval f v M Z in (SE h v', M', Z')
      | _ => (s, M, Z)
      end
  end
with eval (fuel : nat) (v : val) (M : PositiveMap.t (list (mode * positive))) (Z : st)
  : val * PositiveMap.t (list (mode * positive)) * st :=
  match fuel with
  | 0 => (v, M, Z)
  | S f =>
      match v with
      | VTerm u b p => let '(p', M', Z') := eta f (vmode b) p M Z in (VTerm u b p', M', Z')
      | VLook g j x => let '(x', M', Z') := eta f (One g) x M Z in (VLook g j x', M', Z')
      | VVar _ _ => (v, M, Z)
      end
  end
(** Remove redexes to a fixpoint: a weakening and an entry on its label
    (cancellation); an entry and a weakening on its label, when the
    entry is dead or its target is what the rest gives [h₀]. *)
with reduce_all (fuel : nat) (n : nat) (w : list step) (M : PositiveMap.t (list (mode * positive))) (Z : st)
  : list step * PositiveMap.t (list (mode * positive)) * st :=
  match fuel with
  | 0 => (w, M, Z)
  | S f =>
      match n with
      | 0 => (w, M, Z)
      | S n' =>
          let '(o, M1, Z1) := redex f [] w M Z in
          match o with Some w' => reduce_all f n' w' M1 Z1 | None => (w, M1, Z1) end
      end
  end
with redex (fuel : nat) (pre w : list step) (M : PositiveMap.t (list (mode * positive))) (Z : st)
  : option (list step) * PositiveMap.t (list (mode * positive)) * st :=
  match fuel with
  | 0 => (None, M, Z)
  | S f =>
      match w with
      | [] => (None, M, Z)
      | s :: r =>
          let '(hit, M1, Z1) :=
            match s, r with
            | SW h, SE g _ :: r' => (if lexp_eqb g h then Some (rev pre ++ r') else None, M, Z)
            | SE h v, SW g :: r' =>
                if lexp_eqb g h then
                  if dead (rev pre) h then (Some (rev pre ++ r'), M, Z)
                  else
                    let '(rw, Z1) := rebuild r' [] Z in
                    let '(v0, M1, Z2) := eval f (lookup F h 0 rw) M Z1 in
                    (if val_eqb v v0 then Some (rev pre ++ r') else None, M1, Z2)
                else (None, M, Z)
            | _, _ => (None, M, Z)
            end in
          match hit with Some l => (Some l, M1, Z1) | None => redex f (s :: pre) r M1 Z1 end
      end
  end.

(** Both sides through [HNorm], then the pass, in one table. *)
Definition he_eq (e1 e2 : aexp) : bool :=
  let '(w1, Z1) := norm F e1 [] st0 in
  let '(w2, Z2) := norm F e2 [] Z1 in
  let fu := 2 * Pos.to_nat (next Z2) + 100 in
  let '(r1, M, Z3) := eta fu All (wid w1) (PositiveMap.empty _) Z2 in
  let '(r2, _, _) := eta fu All (wid w2) M Z3 in
  Pos.eqb r1 r2.

(** The normal-form ids of a list of expressions, in one table. *)
Definition he_ids (es : list aexp) : list positive :=
  let '(ws, Z) := fold_left (fun '(acc, Z) e => let '(w, Z') := norm F e [] Z in (wid w :: acc, Z')) es ([], st0) in
  let fu := 2 * Pos.to_nat (next Z) + 100 in
  let '(rs, _, _) := fold_left (fun '(acc, M, Z) w => let '(r, M', Z') := eta fu All w M Z in (r :: acc, M', Z'))
                        (rev ws) ([], PositiveMap.empty _, Z) in
  rev rs.

End Eta.
