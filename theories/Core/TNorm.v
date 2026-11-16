(** * A trie normaliser with a printer (experiment)

    The normal form of [HNorm], with each run of steps on ground labels
    (concrete labels and the bound label, all ordered against each
    other) stored as a canonical binary trie from labels to the stack
    of steps on that label ([docs/hnorm.md], "The trie as a term").

    - A word is the empty word, a run (a trie) in front of a word that
      does not start with a run, or a barrier step in front of a word.
      Barriers are adjustment atoms and steps on label atoms.
    - The trie is keyed by the bits of the label, most significant
      first, so its in-order is the label order: concrete labels by
      string order, then the bound label.  Its shape depends only on
      its keys: there are no empty branches.
    - Everything is hash-consed, so equal normal forms have equal ids.

    Steps on label atoms are kept where they are put: they never pass
    other steps, even when the facts would allow it.  So this
    normaliser is sound but not complete for label atoms with facts.

    The printer writes the normal form as shared definitions, with
    context fragments for the tries ([sx], [fx]); [nx] normalises that
    syntax again.

    This file is for measuring time and size only: nothing is proved. *)

From Stdlib Require Import String Ascii List PArith NArith Bool FMapPositive.
From ShiftedNames.Core Require Import Label Normalise GEval HNorm.
Import ListNotations.

(** ** Keys *)

Definition ground (h : lexp) : bool := match h with LAtom _ => false | _ => true end.

Definition abits (a : ascii) : list bool :=
  match a with Ascii b0 b1 b2 b3 b4 b5 b6 b7 => [b7; b6; b5; b4; b3; b2; b1; b0] end.

Fixpoint sbits (s : string) : list bool :=
  match s with EmptyString => [false] | String a s' => true :: abits a ++ sbits s' end.

(** The bound label is last. *)
Definition key (h : lexp) : list bool :=
  match h with LNone => [true] | LCon s => false :: sbits s | LAtom _ => [] end.

(** ** Hash-consed nodes

    Id 1 is empty (the empty word, trie and stack).  Id 2 is never
    allocated: lookups that run off a fragment end there, so they never
    equal a real value. *)

Inductive kstep : Type := KE (v : val) | KW.
Inductive bstep : Type := BA (a : nat) | BE (h : lexp) (v : val) | BW (h : lexp).

Inductive node : Type :=
| NStk (h : lexp) (s : kstep) (tl : positive)
| NTri (l r : positive)
| NLeaf (stk : positive)
| NRun (t rest : positive)
| NBar (s : bstep) (rest : positive).

Definition kstep_eqb (a b : kstep) : bool :=
  match a, b with KE v, KE v' => val_eqb v v' | KW, KW => true | _, _ => false end.

Definition bstep_eqb (a b : bstep) : bool :=
  match a, b with
  | BA a, BA a' => Nat.eqb a a'
  | BE h v, BE h' v' => lexp_eqb h h' && val_eqb v v'
  | BW h, BW h' => lexp_eqb h h'
  | _, _ => false
  end.

Definition node_eqb (a b : node) : bool :=
  match a, b with
  | NStk h s t, NStk h' s' t' => Pos.eqb t t' && lexp_eqb h h' && kstep_eqb s s'
  | NTri l r, NTri l' r' => Pos.eqb l l' && Pos.eqb r r'
  | NLeaf s, NLeaf s' => Pos.eqb s s'
  | NRun t r, NRun t' r' => Pos.eqb t t' && Pos.eqb r r'
  | NBar s r, NBar s' r' => Pos.eqb r r' && bstep_eqb s s'
  | _, _ => false
  end.

Definition hmask : N := 1073741823.
Definition mix (a b : N) : N := N.land (N.lxor (N.shiftl a 5 + a) b) hmask.

Definition hstr (s : string) : N :=
  (fix go s acc := match s with EmptyString => acc | String c s' => go s' (mix acc (N_of_ascii c)) end) s 7%N.

Definition hlexp (h : lexp) : N :=
  match h with LNone => 1 | LCon s => mix 2 (hstr s) | LAtom n => mix 3 (N.of_nat n) end.

Definition hval (v : val) : N :=
  match v with
  | VVar h i => mix (mix 11 (hlexp h)) (N.of_nat i)
  | VTerm u b p => mix (mix (mix 13 (N.of_nat u)) (match b with Some n => N.of_nat (S n) | None => 0 end)) (Npos p)
  | VLook h i x => mix (mix (mix 17 (hlexp h)) (N.of_nat i)) (Npos x)
  end.

Definition hnode (n : node) : positive :=
  N.succ_pos match n with
  | NStk h s t => mix (mix (mix 19 (hlexp h)) (match s with KE v => hval v | KW => 5 end)) (Npos t)
  | NTri l r => mix (mix 23 (Npos l)) (Npos r)
  | NLeaf s => mix 29 (Npos s)
  | NRun t r => mix (mix 31 (Npos t)) (Npos r)
  | NBar s r => mix (mix 37 (match s with BA a => mix 1 (N.of_nat a) | BE h v => mix (hlexp h) (hval v) | BW h => mix 2 (hlexp h) end)) (Npos r)
  end.

Record st : Type := mk_st { tab : PositiveMap.t (list (node * positive)); defs : PositiveMap.t node; next : positive }.

Definition st0 : st := mk_st (PositiveMap.empty _) (PositiveMap.empty _) 3.

Definition get (i : positive) (Z : st) : option node := PositiveMap.find i (defs Z).

Definition hcons (n : node) (Z : st) : positive * st :=
  let k := hnode n in
  let b := match PositiveMap.find k (tab Z) with Some b => b | None => [] end in
  match find (fun '(m, _) => node_eqb m n) b with
  | Some (_, i) => (i, Z)
  | None =>
      let i := next Z in
      (i, mk_st (PositiveMap.add k ((n, i) :: b) (tab Z)) (PositiveMap.add i n (defs Z)) (Pos.succ i))
  end.

(** ** Tries *)

Fixpoint tfind (k : list bool) (t : positive) (Z : st) : positive :=
  match k, get t Z with
  | [], Some (NLeaf s) => s
  | b :: k', Some (NTri l r) => tfind k' (if b then r else l) Z
  | _, _ => 1
  end.

(** Set the stack of key [k] ([1] removes it). *)
Fixpoint tset (k : list bool) (t stk : positive) (Z : st) : positive * st :=
  match k with
  | [] => if Pos.eqb stk 1 then (xH, Z) else hcons (NLeaf stk) Z
  | b :: k' =>
      let '(l, r) := match get t Z with Some (NTri l r) => (l, r) | _ => (xH, xH) end in
      let '(c, S1) := tset k' (if b then r else l) stk Z in
      let '(l', r') := if b then (l, c) else (c, r) in
      if Pos.eqb l' 1 && Pos.eqb r' 1 then (xH, S1) else hcons (NTri l' r') S1
  end.

Definition mkrun (t rest : positive) (Z : st) : positive * st :=
  if Pos.eqb t 1 then (rest, Z) else hcons (NRun t rest) Z.

Section Norm.

Variable F : order.

(** A bound on the depth of every walk, computed once. *)
Variable fu : nat.

(** ** Lookups *)

Fixpoint slookup (fuel : nat) (h : lexp) (i : nat) (stk rest : positive) (Z : st) : val :=
  match fuel with
  | 0 => VLook h i 2
  | S f =>
      match get stk Z with
      | Some (NStk _ (KE v) tl) => match i with 0 => v | S i' => slookup f h i' tl rest Z end
      | Some (NStk _ KW tl) => slookup f h (S i) tl rest Z
      | _ => wlookup f h i rest Z
      end
  end
with wlookup (fuel : nat) (h : lexp) (i : nat) (w : positive) (Z : st) : val :=
  match fuel with
  | 0 => VLook h i w
  | S f =>
      if Pos.eqb w 1 then VVar h i else
      match get w Z with
      | Some (NRun t rest) => if ground h then slookup f h i (tfind (key h) t Z) rest Z else VLook h i w
      | Some (NBar (BE g v) rest) =>
          if lexp_eqb g h then match i with 0 => v | S i' => wlookup f h i' rest Z end
          else if kd F g h then wlookup f h i rest Z else VLook h i w
      | Some (NBar (BW g) rest) =>
          if lexp_eqb g h then wlookup f h (S i) rest Z
          else if kd F g h then wlookup f h i rest Z else VLook h i w
      | _ => VLook h i w
      end
  end.

Definition lookup (h : lexp) (i : nat) (w : positive) (Z : st) : val := wlookup fu h i w Z.

(** ** Pushing a step *)

(** A step on top of the stack [stk] of [h], with [rest] below the run. *)
Definition spush (h : lexp) (s : kstep) (stk rest : positive) (Z : st) : positive * st :=
  match s, get stk Z with
  | KW, Some (NStk _ (KE _) tl) => (tl, Z)
  | KE v, Some (NStk _ KW tl) =>
      if val_eqb v (slookup fu h 0 tl rest Z) then (tl, Z) else hcons (NStk h s stk) Z
  | _, _ => hcons (NStk h s stk) Z
  end.

Definition pushG (h : lexp) (s : kstep) (w : positive) (Z : st) : positive * st :=
  let k := key h in
  let '(t, rest) := match get w Z with Some (NRun t r) => (t, r) | _ => (xH, w) end in
  let '(stk, S1) := spush h s (tfind k t Z) rest Z in
  let '(t', S2) := tset k t stk S1 in
  mkrun t' rest S2.

Definition pushB (s : bstep) (w : positive) (Z : st) : positive * st :=
  match s, get w Z with
  | BW h, Some (NBar (BE g _) rest) => if lexp_eqb g h then (rest, Z) else hcons (NBar s w) Z
  | BE h v, Some (NBar (BW g) rest) =>
      if lexp_eqb g h && val_eqb v (lookup h 0 rest Z) then (rest, Z) else hcons (NBar s w) Z
  | _, _ => hcons (NBar s w) Z
  end.

Definition pushW (h : lexp) (w : positive) (Z : st) : positive * st :=
  if ground h then pushG h KW w Z else pushB (BW h) w Z.

Definition pushE (h : lexp) (v : val) (w : positive) (Z : st) : positive * st :=
  if ground h then pushG h (KE v) w Z else pushB (BE h v) w Z.

(** ** Payloads without a payload atom drop bound-label steps before
    the first atom *)

Fixpoint has_unb (fuel : nat) (w : positive) (Z : st) : bool :=
  match fuel with
  | 0 => false
  | S f =>
      match get w Z with
      | Some (NRun t rest) => if Pos.eqb (tfind (key LNone) t Z) 1 then has_unb f rest Z else true
      | Some (NBar (BA _) _) => false
      | Some (NBar _ rest) => has_unb f rest Z
      | _ => false
      end
  end.

Fixpoint unb (fuel : nat) (w : positive) (Z : st) : positive * st :=
  match fuel with
  | 0 => (w, Z)
  | S f =>
      match get w Z with
      | Some (NRun t rest) =>
          let '(t', S1) := tset (key LNone) t 1 Z in
          let '(r', S2) := unb f rest S1 in
          mkrun t' r' S2
      | Some (NBar (BA _) _) => (w, Z)
      | Some (NBar s rest) => let '(r', S1) := unb f rest Z in hcons (NBar s r') S1
      | _ => (w, Z)
      end
  end.

Definition clean (b : option nat) (w : positive) (Z : st) : positive * st :=
  match b with
  | Some _ => (w, Z)
  | None => if has_unb fu w Z then unb fu w Z else (w, Z)
  end.

(** ** Normalising an expression, from right to left *)

Fixpoint norm (e : aexp) (K : positive) (Z : st) {struct e} : positive * st :=
  match e with
  | AId => (K, Z)
  | AAtom n => pushB (BA n) K Z
  | ACompose a b => let '(K1, S1) := norm a K Z in norm b K1 S1
  | AOuter h a => let '(K1, S1) := pushW h K Z in norm a K1 S1
  | AInner h t a =>
      let '(v, S1) := tval t K Z in
      let '(K1, S2) := norm a K S1 in
      pushE h v K1 S2
  | ALift h a =>
      let v := lookup h 0 K Z in
      let '(K1, S1) := pushW h K Z in
      let '(K2, S2) := norm a K1 S1 in
      pushE h v K2 S2
  end
with tval (t : texp) (K : positive) (Z : st) {struct t} : val * st :=
  match t with
  | TVarE h i => (lookup h i K Z, Z)
  | TBindE u p =>
      let '(P, S1) := pnorm p K Z in
      let '(P', S2) := clean (fpb p) P S1 in
      (VTerm u (fpb p) P', S2)
  | TShiftE h t' =>
      if is_bind t' then tval t' K Z
      else let '(K1, S1) := pushW h K Z in tval t' K1 S1
  end
with pnorm (p : pexp) (K : positive) (Z : st) {struct p} : positive * st :=
  match p with
  | PId | PAtom _ => (K, Z)
  | PComp a p' => let '(K1, S1) := norm a K Z in pnorm p' K1 S1
  | PShift h p' => let '(K1, S1) := pushW h K Z in pnorm p' K1 S1
  end.

End Norm.

(** ** Size: nodes reachable from a word *)

Definition val_refs (v : val) : list positive :=
  match v with VVar _ _ => [] | VTerm _ _ p => [p] | VLook _ _ x => [x] end.

Definition node_refs (n : node) : list positive :=
  match n with
  | NStk _ (KE v) t => t :: val_refs v
  | NStk _ KW t => [t]
  | NTri l r => [l; r]
  | NLeaf s => [s]
  | NRun t r => [t; r]
  | NBar (BE _ v) r => r :: val_refs v
  | NBar _ r => [r]
  end.

Fixpoint reach (fuel : nat) (Z : st) (todo : list positive) (seen : PositiveMap.t unit) : PositiveMap.t unit :=
  match fuel with
  | 0 => seen
  | S f =>
      match todo with
      | [] => seen
      | i :: todo' =>
          if Pos.leb i 2 then reach f Z todo' seen
          else match PositiveMap.find i seen with
               | Some _ => reach f Z todo' seen
               | None =>
                   match get i Z with
                   | Some n => reach f Z (node_refs n ++ todo') (PositiveMap.add i tt seen)
                   | None => reach f Z todo' seen
                   end
               end
      end
  end.

(** ** The printed syntax

    Adjustments and context fragments, with references to shared
    definitions.  A fragment's targets are in the output scope of the
    whole adjustment, as for [AInner]; [FApp d1 d2] is [d1]'s steps in
    front of [d2]'s. *)

Inductive sx : Type :=
| XId
| XAtom (n : nat) (a : sx)          (* the atom, then [a] *)
| XFrag (d : fx) (a : sx)           (* [d]'s steps in front of [a] *)
| XRef (i : positive)
with fx : Type :=
| FEnt (h : lexp) (t : tx)
| FWk (h : lexp)
| FApp (d1 d2 : fx)
| FRef (i : positive)
with tx : Type :=
| TVar (h : lexp) (i : nat)
| TTerm (u : nat) (b : option nat) (p : sx)
| TLook (h : lexp) (i : nat) (n : sx).

Inductive def : Type := DX (a : sx) | DF (d : fx).

Fixpoint sx_size (a : sx) : N :=
  match a with
  | XId | XRef _ => 1
  | XAtom _ a => N.succ (sx_size a)
  | XFrag d a => N.succ (fx_size d + sx_size a)
  end
with fx_size (d : fx) : N :=
  match d with
  | FEnt _ t => N.succ (tx_size t)
  | FWk _ | FRef _ => 1
  | FApp d1 d2 => N.succ (fx_size d1 + fx_size d2)
  end
with tx_size (t : tx) : N :=
  match t with TVar _ _ => 1 | TTerm _ _ p => N.succ (sx_size p) | TLook _ _ n => N.succ (sx_size n) end.

Definition def_size (d : def) : N := match d with DX a => sx_size a | DF f => fx_size f end.

(** ** Printing

    Every reachable word, stack cell and binary trie node becomes one
    definition.  Unary trie nodes are skipped: a trie prints as its
    binary nodes and leaves. *)

Definition pword (w : positive) : sx := if Pos.eqb w 1 then XId else XRef w.

Definition pval (v : val) : tx :=
  match v with
  | VVar h i => TVar h i
  | VTerm u b p => TTerm u b (pword p)
  | VLook h i x => TLook h i (pword x)
  end.

(** The fragment for a trie or stack id, skipping unary trie nodes. *)
Fixpoint ptrie (fuel : nat) (t : positive) (Z : st) : fx :=
  match fuel with
  | 0 => FRef t
  | S f =>
      match get t Z with
      | Some (NTri l r) =>
          if Pos.eqb l 1 then ptrie f r Z else if Pos.eqb r 1 then ptrie f l Z else FRef t
      | Some (NLeaf s) => FRef s
      | _ => FRef t
      end
  end.

Definition pdef (fu : nat) (i : positive) (Z : st) : option def :=
  match get i Z with
  | Some (NRun t rest) => Some (DX (XFrag (ptrie fu t Z) (pword rest)))
  | Some (NBar (BA a) rest) => Some (DX (XAtom a (pword rest)))
  | Some (NBar (BE h v) rest) => Some (DX (XFrag (FEnt h (pval v)) (pword rest)))
  | Some (NBar (BW h) rest) => Some (DX (XFrag (FWk h) (pword rest)))
  | Some (NTri l r) =>
      if Pos.eqb l 1 then None else if Pos.eqb r 1 then None
      else Some (DF (FApp (ptrie fu l Z) (ptrie fu r Z)))
  | Some (NStk h s tl) =>
      let one := match s with KE v => FEnt h (pval v) | KW => FWk h end in
      Some (DF (if Pos.eqb tl 1 then one else FApp one (FRef tl)))
  | _ => None
  end.

(** The printed form of the words [roots]: the definitions, keyed by
    id. *)
Definition print (fu : nat) (roots : list positive) (Z : st) : PositiveMap.t def :=
  let seen := reach fu Z roots (PositiveMap.empty _) in
  PositiveMap.fold (fun i _ acc => match pdef fu i Z with Some d => PositiveMap.add i d acc | None => acc end)
    seen (PositiveMap.empty _).

Definition psize (P : PositiveMap.t def) : N * N :=
  PositiveMap.fold (fun _ d '(n, s) => (N.succ n, s + def_size d)%N) P (0%N, 0%N).

(** ** Normalising printed syntax *)

Section Read.

Variable F : order.
Variable fu : nat.
Variable P : PositiveMap.t def.

(** Push the steps of stack [s1] (from the table [Z]) on top of stack
    [s2], bottom first.  Lookups that run off [s2] end at id 2. *)
Fixpoint sapp (fuel : nat) (s1 s2 : positive) (Z : st) : positive * st :=
  match fuel with
  | 0 => (s2, Z)
  | S f =>
      match get s1 Z with
      | Some (NStk h s tl) => let '(s2', S1) := sapp f tl s2 Z in spush F fu h s s2' 2 S1
      | _ => (s2, Z)
      end
  end.

(** Union of two tries, the first one's steps in front. *)
Fixpoint tunion (fuel : nat) (t1 t2 : positive) (Z : st) : positive * st :=
  match fuel with
  | 0 => (t2, Z)
  | S f =>
      if Pos.eqb t1 1 then (t2, Z) else if Pos.eqb t2 1 then (t1, Z) else
      match get t1 Z, get t2 Z with
      | Some (NTri l1 r1), Some (NTri l2 r2) =>
          let '(l, S1) := tunion f l1 l2 Z in
          let '(r, S2) := tunion f r1 r2 S1 in
          if Pos.eqb l 1 && Pos.eqb r 1 then (xH, S2) else hcons (NTri l r) S2
      | Some (NLeaf s1), Some (NLeaf s2) =>
          let '(s, S1) := sapp fu s1 s2 Z in
          if Pos.eqb s 1 then (xH, S1) else hcons (NLeaf s) S1
      | _, _ => (t2, Z)
      end
  end.

(** All the steps of a run, as a list of (label, step), front first. *)
Fixpoint tsteps (fuel : nat) (t : positive) (Z : st) : list (lexp * kstep) :=
  match fuel with
  | 0 => []
  | S f =>
      match get t Z with
      | Some (NTri l r) => tsteps f l Z ++ tsteps f r Z
      | Some (NLeaf s) => tsteps f s Z
      | Some (NStk h s tl) => (h, s) :: tsteps f tl Z
      | _ => []
      end
  end.

(** Memo: for (reference, continuation), the result.  Keys pair the
    two ids. *)
Definition mkey (i K : positive) : positive := (i * 1000003 + K)%positive.

Record rs : Type := mk_rs { mw : PositiveMap.t (list (positive * positive * positive)); rst : st }.

Definition mfind (i K : positive) (R : rs) : option positive :=
  match PositiveMap.find (mkey i K) (mw R) with
  | Some l => option_map (fun '(_, _, r) => r) (find (fun '(a, b, _) => Pos.eqb a i && Pos.eqb b K) l)
  | None => None
  end.

Definition madd (i K r : positive) (R : rs) : rs :=
  let k := mkey i K in
  let l := match PositiveMap.find k (mw R) with Some l => l | None => [] end in
  mk_rs (PositiveMap.add k ((i, K, r) :: l) (mw R)) (rst R).

Definition lift1 {A} (f : st -> A * st) (R : rs) : A * rs :=
  let '(a, Z) := f (rst R) in (a, mk_rs (mw R) Z).

(** [nx e K]: [e], then [K].  [fd d K] is the fragment [d] as a
    standalone trie, its targets against [K]; it fails ([None]) on a
    step on a label atom. *)
Fixpoint nx (fuel : nat) (e : sx) (K : positive) (R : rs) {struct fuel} : positive * rs :=
  match fuel with
  | 0 => (K, R)
  | S f =>
      match e with
      | XId => (K, R)
      | XAtom a e' => let '(K1, R1) := nx f e' K R in lift1 (pushB F fu (BA a) K1) R1
      | XFrag d e' =>
          let '(K1, R1) := nx f e' K R in
          match d with
          | FEnt h t => if ground h then frag f d K K1 R1
                        else let '(v, R2) := tx_val f t K R1 in lift1 (pushB F fu (BE h v) K1) R2
          | FWk h => if ground h then frag f d K K1 R1 else lift1 (pushB F fu (BW h) K1) R1
          | _ => frag f d K K1 R1
          end
      | XRef i =>
          match mfind i K R with
          | Some r => (r, R)
          | None =>
              match PositiveMap.find i P with
              | Some (DX e') => let '(r, R1) := nx f e' K R in (r, madd i K r R1)
              | _ => (K, R)
              end
          end
      end
  end
with frag (fuel : nat) (d : fx) (K K1 : positive) (R : rs) {struct fuel} : positive * rs :=
  match fuel with
  | 0 => (K1, R)
  | S f =>
      let '(t, R1) := fd f d K R in
      let S1 := rst R1 in
      match get K1 S1 with
      | Some (NRun _ _) =>
          (* the tail starts with a run: push the steps one by one *)
          lift1 (fun Z => fold_right (fun '(h, s) '(w, Z) => pushG F fu h s w Z) (K1, Z)
                            (tsteps fu t Z)) R1
      | _ => lift1 (mkrun t K1) R1
      end
  end
with fd (fuel : nat) (d : fx) (K : positive) (R : rs) {struct fuel} : positive * rs :=
  match fuel with
  | 0 => (xH, R)
  | S f =>
      match d with
      | FEnt h t =>
          let '(v, R1) := tx_val f t K R in
          lift1 (fun Z => let '(s, S1) := hcons (NStk h (KE v) 1) Z in tset (key h) 1 s S1) R1
      | FWk h => lift1 (fun Z => let '(s, S1) := hcons (NStk h KW 1) Z in tset (key h) 1 s S1) R
      | FApp d1 d2 =>
          let '(t1, R1) := fd f d1 K R in
          let '(t2, R2) := fd f d2 K R1 in
          lift1 (tunion fu t1 t2) R2
      | FRef i =>
          match mfind i K R with
          | Some r => (r, R)
          | None =>
              match PositiveMap.find i P with
              | Some (DF d') => let '(r, R1) := fd f d' K R in (r, madd i K r R1)
              | _ => (xH, R)
              end
          end
      end
  end
with tx_val (fuel : nat) (t : tx) (K : positive) (R : rs) {struct fuel} : val * rs :=
  match fuel with
  | 0 => (VVar LNone 0, R)
  | S f =>
      match t with
      | TVar h i => (lookup F fu h i K (rst R), R)
      | TTerm u b p =>
          let '(w, R1) := nx f p K R in
          let '(w', R2) := lift1 (clean fu b w) R1 in
          (VTerm u b w', R2)
      | TLook h i n =>
          let '(w, R1) := nx f n K R in (lookup F fu h i w (rst R1), R1)
      end
  end.

End Read.

(** ** Benchmark entry points

    [fu] bounds every walk.  It is built once, from the size of the
    input: walks are bounded by the number of nodes, which is at most a
    constant (the key length plus a few) times the input size. *)

Fixpoint asize (e : aexp) : positive :=
  match e with
  | AId | AAtom _ => 1
  | ACompose a b => Pos.succ (asize a + asize b)
  | AOuter _ a | ALift _ a => Pos.succ (asize a)
  | AInner _ t a => Pos.succ (tsize t + asize a)
  end
with tsize (t : texp) : positive :=
  match t with
  | TVarE _ _ => 1
  | TBindE _ p => Pos.succ (psz p)
  | TShiftE _ t => Pos.succ (tsize t)
  end
with psz (p : pexp) : positive :=
  match p with
  | PId | PAtom _ => 1
  | PComp a p => Pos.succ (asize a + psz p)
  | PShift _ p => Pos.succ (psz p)
  end.

Definition fuel_for (e1 e2 : aexp) : nat := Pos.to_nat (128 * (asize e1 + asize e2) + 1000).

(** Normalise both sides; the two roots and the table. *)
Definition tn_both (F : order) (fu : nat) (e1 e2 : aexp) : positive * positive * st :=
  let '(w1, S1) := norm F fu e1 1 st0 in
  let '(w2, S2) := norm F fu e2 1 S1 in
  (w1, w2, S2).

Definition tn_eq (F : order) (e1 e2 : aexp) : bool :=
  let fu := fuel_for e1 e2 in let '(w1, w2, _) := tn_both F fu e1 e2 in Pos.eqb w1 w2.

(** Reachable nodes of one side, and nodes built for it. *)
Definition tn_size (F : order) (e : aexp) : N * N :=
  let fu := fuel_for e AId in
  let '(w, Z) := norm F fu e 1 st0 in
  (N.of_nat (PositiveMap.cardinal (reach fu Z [w] (PositiveMap.empty _))), Npos (next Z) - 3)%N.

(** The printed form of both sides. *)
Definition tn_print (F : order) (e1 e2 : aexp) : positive * positive * PositiveMap.t def :=
  let fu := fuel_for e1 e2 in
  let '(w1, w2, Z) := tn_both F fu e1 e2 in (w1, w2, print fu [w1; w2] Z).

(** Definitions and total size of the printed form of one side. *)
Definition tn_psize (F : order) (e : aexp) : N * N :=
  let fu := fuel_for e AId in
  let '(w, Z) := norm F fu e 1 st0 in psize (print fu [w] Z).

(** Normalise the printed form again on a fresh table: are the two
    sides still equal? *)
Definition tn_reread (F : order) (r : positive * positive * PositiveMap.t def) : bool :=
  let '(w1, w2, P) := r in
  let fu := 8 * PositiveMap.cardinal P + 1000 in
  let R0 := mk_rs (PositiveMap.empty _) st0 in
  let '(v1, R1) := nx F fu P fu (pword w1) 1 R0 in
  let '(v2, _) := nx F fu P fu (pword w2) 1 R1 in
  Pos.eqb v1 v2.

(** Idempotence: normalise, print, and normalise the printed form in
    the same table; the ids must come back. *)
Definition tn_idem (F : order) (e1 e2 : aexp) : bool :=
  let fu := fuel_for e1 e2 in
  let '(w1, w2, Z) := tn_both F fu e1 e2 in
  let P := print fu [w1; w2] Z in
  let R0 := mk_rs (PositiveMap.empty _) Z in
  let '(v1, R1) := nx F fu P fu (pword w1) 1 R0 in
  let '(v2, _) := nx F fu P fu (pword w2) 1 R1 in
  Pos.eqb v1 w1 && Pos.eqb v2 w2.
