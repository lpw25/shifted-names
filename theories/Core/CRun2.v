(** * The reworked context-form pass, with a representation that keeps
      each step proportional to what moves

    [CRun] keeps a form's outputs top first, so every merge appends the
    new outputs at the end of a list, and it reaches inputs and outputs
    by position.  Here:

    - an [eform] keeps its outputs bottom first, with their number, so new
      outputs go on at the bottom in constant time, and reads near the
      bottom are reached from the front of the list;
    - outputs and inputs carry their ids in the same lists;
    - merging ([ecompose]), taking new reads as early as they go
      ([nread_e]) and placing new items ([place_front], [place_suffix_out],
      [place_out_bottom]) are written for this representation; an output
      swap looks up the reads between the two outputs in a map from
      depths to counts ([PositiveMap]), and only scans the inputs when
      there is one;
    - the operations that scan a form anyway (absorbing a restore, moving
      one output or input on, lifting) go through [CRun]'s representation
      and back ([to_i], [of_i]).

    Every operation is proved sound against [CForm]; [rrun2_sound] and
    [cr2_eq_correct] are closed under the global context. *)

From Stdlib Require Import List Bool Arith Lia PArith FMapPositive Permutation.
From ShiftedNames.Core Require Import Label Normalise GEval CNorm Comp CSound CComplete CForm CRun.
Import ListNotations.

Record eform : Type := mkE {
  ob : list (positive * lexp);              (* outputs, bottom first, with ids *)
  ol : nat;                                 (* their number *)
  ei : list (positive * (lexp * tgt))       (* inputs, outermost first, with ids *)
}.

Inductive eitem : Type :=
| KF (f : eform)
| KA (L : list lexp) (n : nat).

Definition eff (e : eform) : form := mkF (rev (map snd (ob e))) (map snd (ei e)).

Definition estrip (it : eitem) : item := match it with KF f => IF (eff f) | KA L n => IA L n end.

Fixpoint zipd {X} (ids : list positive) (l : list X) : list (positive * X) :=
  match l with
  | [] => []
  | x :: l' => match ids with i :: ids' => (i, x) :: zipd ids' l' | [] => (xH, x) :: zipd [] l' end
  end.

Definition to_i (e : eform) : iform := mkI (eff e) (rev (map fst (ob e))) (map fst (ei e)).

(** Back from [CRun]'s representation; targets clamped to the outputs
    (they already are, but this way it needs no proof). *)
Definition of_i (f : iform) : eform :=
  let n := length (fout (ff f)) in
  mkE (rev (zipd (oids f) (fout (ff f)))) n (zipd (iids f) (map (fun '(l, t) => (l, clamp n t)) (fin (ff f)))).

Definition emptyE : eform := mkE [] 0 [].

Section Run2.

Variable F : order.

Definition lab_i (x : positive * (lexp * tgt)) : lexp := fst (snd x).

(** ** Reads taken as early as they go, from the bottom *)

Fixpoint nread_up (up : list (positive * lexp)) (z : lexp) (i d : nat) : tgt :=
  match d with
  | 0 => TR z i 0
  | S d' =>
      match up with
      | (_, o) :: up' =>
          if lexp_eqb o z then nread_up up' z (S i) d' else if kd F z o then nread_up up' z i d' else TR z i d
      | [] => TR z i d
      end
  end.

Definition nread_e (e : eform) (t : tgt) : tgt :=
  match t with
  | TR z i d => if Nat.leb d (ol e) then nread_up (skipn (ol e - d) (ob e)) z i d else t
  | TT _ _ => t
  end.

Fixpoint map_front {X} (n : nat) (g : X -> X) (l : list X) : list X :=
  match n, l with S n', x :: l' => g x :: map_front n' g l' | _, _ => l end.

Definition reread_front (n : nat) (e : eform) : eform :=
  mkE (ob e) (ol e) (map_front n (fun '(id, (l, t)) => (id, (l, nread_e e t))) (ei e)).

Definition reread_at (j : nat) (e : eform) : eform :=
  mkE (ob e) (ol e) (map (fun '(id, (l, t)) => (id, (l, if is_dep j t then nread_e e t else t))) (ei e)).

(** ** Placing inputs *)

(** [x] moved inward past inputs that sort before it. *)
Fixpoint bub_in (x : positive * (lexp * tgt)) (I : list (positive * (lexp * tgt))) : list (positive * (lexp * tgt)) :=
  match I with
  | [] => [x]
  | y :: r => if before F (lab_i y) (lab_i x) then y :: bub_in x r else x :: I
  end.

(** The first [n] inputs placed, the innermost of them first. *)
Fixpoint place_front (n : nat) (I : list (positive * (lexp * tgt))) : list (positive * (lexp * tgt)) :=
  match n, I with S n', x :: I' => bub_in x (place_front n' I') | _, _ => I end.

(** [x] moved outward, [rp] the inputs outside it, nearest first. *)
Fixpoint ins_out (x : positive * (lexp * tgt)) (rp : list (positive * (lexp * tgt))) : list (positive * (lexp * tgt)) :=
  match rp with
  | [] => [x]
  | y :: r => if before F (lab_i x) (lab_i y) then y :: ins_out x r else x :: rp
  end.

Fixpoint out_pass (rp suf : list (positive * (lexp * tgt))) : list (positive * (lexp * tgt)) :=
  match suf with [] => rev rp | x :: s => out_pass (ins_out x rp) s end.

(** The inputs from position [p] on placed, each moved outward. *)
Definition place_suffix_out (p : nat) (I : list (positive * (lexp * tgt))) : list (positive * (lexp * tgt)) :=
  out_pass (rev (firstn p I)) (skipn p I).

(** ** Placing outputs *)

Definition dkey (d : nat) : positive := Pos.of_succ_nat d.

Definition cnt (m : PositiveMap.t nat) (d : nat) : nat :=
  match PositiveMap.find (dkey d) m with Some c => c | None => 0 end.

Definition idx_add (m : PositiveMap.t nat) (t : tgt) : PositiveMap.t nat :=
  match t with TR _ _ d => PositiveMap.add (dkey d) (S (cnt m d)) m | TT _ _ => m end.

Definition idx_of (I : list (positive * (lexp * tgt))) : PositiveMap.t nat :=
  fold_left (fun m x => idx_add m (snd (snd x))) I (PositiveMap.empty nat).

(** The reads at depth [d] moved to [d+1]. *)
Definition idx_move (m : PositiveMap.t nat) (d : nat) : PositiveMap.t nat :=
  PositiveMap.add (dkey d) 0 (PositiveMap.add (dkey (S d)) (cnt m (S d) + cnt m d) m).

Definition swap_in (k : nat) (b : lexp) (I : list (positive * (lexp * tgt))) : option (list (positive * (lexp * tgt))) :=
  omap (fun '(id, (l, t)) => option_map (fun t' => (id, (l, t'))) (swap_read F k b t)) I.

(** Output [x], at depth [pos] (top first), moved up past the outputs
    [acc] above it (nearest first), as [CForm.oswap] allows.  The map
    [mo], built when first needed, counts the reads at each depth. *)
Fixpoint bub_out (x : positive * lexp) (acc : list (positive * lexp)) (pos : nat)
    (I : list (positive * (lexp * tgt))) (mo : option (PositiveMap.t nat)) {struct acc} :
    list (positive * lexp) * list (positive * (lexp * tgt)) * option (PositiveMap.t nat) :=
  match acc with
  | [] => ([x], I, mo)
  | y :: acc' =>
      if before F (snd x) (snd y) then
        let m := match mo with Some m => m | None => idx_of I end in
        match cnt m pos with
        | 0 => let '(r, I', mo') := bub_out x acc' (pred pos) I (Some m) in (y :: r, I', mo')
        | S _ =>
            match swap_in (pred pos) (snd x) I with
            | Some I' => let '(r, I'', mo') := bub_out x acc' (pred pos) I' (Some (idx_move m pos)) in (y :: r, I'', mo')
            | None => (x :: acc, I, Some m)
            end
        end
      else (x :: acc, I, mo)
  end.

(** The bottom outputs [rng] placed, the topmost first; [k] of them are
    below, [n] is the number of outputs. *)
Fixpoint place_rng (k n : nat) (rng above : list (positive * lexp)) (I : list (positive * (lexp * tgt)))
    (mo : option (PositiveMap.t nat)) : list (positive * lexp) * list (positive * (lexp * tgt)) * option (PositiveMap.t nat) :=
  match rng with
  | [] => (above, I, mo)
  | x :: rng' =>
      let '(a', I', mo') := place_rng (S k) n rng' above I mo in
      bub_out x a' (n - 1 - k) I' mo'
  end.

(** The bottom [r] outputs placed (as [CRun.place_out_up] from depth
    [ol - r]). *)
Definition place_out_bottom (r : nat) (e : eform) : eform :=
  let '(o, Is, _) := place_rng 0 (ol e) (firstn r (ob e)) (skipn r (ob e)) (ei e) None in mkE o (ol e) Is.

(** ** Composing *)

Fixpoint popin_e (o : lexp) (rem : list (positive * (lexp * tgt))) : option (option (list (positive * (lexp * tgt)))) :=
  match rem with
  | [] => Some None
  | y :: r =>
      if lexp_eqb (lab_i y) o then Some (Some r)
      else if kd F (lab_i y) o then
        match popin_e o r with
        | Some (Some r') => Some (Some (y :: r'))
        | Some None => Some None
        | None => None
        end
      else None
  end.

Fixpoint popall_e (O1 : list (positive * lexp)) (rem : list (positive * (lexp * tgt))) (passed : list (positive * lexp)) (canc : bool) :
  option (list (list (positive * (lexp * tgt)) * list (positive * lexp)) * bool) :=
  match O1 with
  | [] => Some ([(rem, passed)], canc)
  | (y, o) :: O1' =>
      match popin_e o rem with
      | Some (Some rem') => option_map (fun '(st, c) => ((rem, passed) :: st, c)) (popall_e O1' rem' passed true)
      | Some None => option_map (fun '(st, c) => ((rem, passed) :: st, c)) (popall_e O1' rem (passed ++ [(y, o)]) canc)
      | None => None
      end
  end.

Fixpoint rthrough_e (rem : list (positive * (lexp * tgt))) (z : lexp) (i : nat) : option (tgt + nat) :=
  match rem with
  | [] => Some (inr i)
  | (_, (l, t)) :: r =>
      if lexp_eqb l z then match i with 0 => Some (inl t) | S i' => rthrough_e r z i' end
      else if kd F l z then rthrough_e r z i else None
  end.

Definition newt_e (f2 : eform) (st : list (list (positive * (lexp * tgt)) * list (positive * lexp))) (t : tgt) : option tgt :=
  match t with
  | TR z i d =>
      match nth_error st d with
      | Some (rem, passed) =>
          match rthrough_e rem z i with
          | Some (inl t') => Some t'
          | Some (inr i') => Some (TR z i' (ol f2 + length passed))
          | None => None
          end
      | None => None
      end
  | TT u p => Some (TT u (PComp (fexp (eff f2)) p))
  end.

(** [f1 ⨾ f2] as one form, the new outputs at the bottom of [f2]'s.  Also
    the ids of the outputs that passed, the ids of [f1]'s inputs, and
    whether an input of [f2] was cancelled. *)
Definition ecompose (f1 f2 : eform) : option (eform * list positive * list positive * bool) :=
  match popall_e (rev (ob f1)) (ei f2) [] false with
  | Some (st, canc) =>
      let '(rem, passed) := last st ([], []) in
      match omap (fun '(id, (l, t)) => option_map (fun t' => (id, (l, t'))) (newt_e f2 st t)) (ei f1) with
      | Some I1 => Some (mkE (rev passed ++ ob f2) (ol f2 + length passed) (I1 ++ rem), map fst passed, map fst (ei f1), canc)
      | None => None
      end
  | None => None
  end.

(** ** Through [CRun]'s representation *)

Definition remove_at_ids {X} (j : nat) (l : list X) : list X := remove_at j l.

Definition iabsorb_e (p : nat) (e : eform) : option eform :=
  match absorb2 F p (eff e) with
  | Some (j, g) =>
      let e1 := reread_at j (of_i (mkI g (remove_at j (rev (map fst (ob e)))) (remove_at p (map fst (ei e))))) in
      let e2 := place_out_bottom (ol e1 - j) e1 in
      Some (mkE (ob e2) (ol e2) (place_suffix_out p (ei e2)))
  | None => None
  end.

Definition restore_like (x : positive * (lexp * tgt)) : bool :=
  match snd (snd x) with TR z 0 _ => lexp_eqb z (lab_i x) | _ => false end.

Fixpoint absorb_scan_e (new : list positive) (e : eform) (p : nat) (I : list (positive * (lexp * tgt))) : option eform :=
  match I with
  | [] => None
  | x :: I' =>
      if mem (fst x) new && restore_like x then
        match iabsorb_e p e with Some g => Some g | None => absorb_scan_e new e (S p) I' end
      else absorb_scan_e new e (S p) I'
  end.

Fixpoint absorb_new_e (fuel : nat) (new : list positive) (e : eform) : eform :=
  match fuel with
  | 0 => e
  | S fuel' => match absorb_scan_e new e 0 (ei e) with Some g => absorb_new_e fuel' new g | None => e end
  end.

Definition icompose_e (f1 f2 : eform) : option (eform * list positive * list positive * bool) :=
  match ecompose f1 f2 with
  | Some (g, passed, newin, canc) =>
      let n1 := length (ei f1) in
      let g1 := reread_front n1 g in
      let g2 := mkE (ob g1) (ol g1) (place_front n1 (ei g1)) in
      let g3 := if canc then mkE (ob g2) (ol g2) (place_suffix_out n1 (ei g2)) else g2 in
      let g4 := place_out_bottom (length passed) g3 in
      Some (match newin with [] => g4 | _ => absorb_new_e (S (length newin)) newin g4 end, passed, newin, canc)
  | None => None
  end.

Definition oids_e (e : eform) : list positive := rev (map fst (ob e)).
Definition iids_e (e : eform) : list positive := map fst (ei e).

Definition imove_e (f1 f2 : eform) (x : positive) : option (eform * eform * list positive * bool * bool) :=
  match index_of x (oids_e f1) with
  | Some j =>
      match out_first F j (eff f1) with
      | Some (o, f1') =>
          match icompose_e (mkE [(x, o)] 1 []) f2 with
          | Some (g, no, _, canc) =>
              let f1n := reread_at j (of_i (mkI f1' (remove_at j (oids_e f1)) (iids_e f1))) in
              Some (place_out_bottom (ol f1n - j) f1n, g, no, canc, false)
          | None => None
          end
      | None => None
      end
  | None =>
      match index_of x (iids_e f1) with
      | Some p =>
          match in_first F p (eff f1) with
          | Some (h, t, f1') =>
              match icompose_e (mkE [] 0 [(x, (h, t))]) f2 with
              | Some (g, _, ni, canc) =>
                  let f1n := of_i (mkI f1' (oids_e f1) (remove_at p (iids_e f1))) in
                  Some (mkE (ob f1n) (ol f1n) (place_suffix_out p (ei f1n)), g, ni, canc, true)
              | None => None
              end
          | None => None
          end
      | None => None
      end
  end.

(** ** The word, as in [CRun] *)

Definition ids_of_e (f : eform) : list positive := oids_e f ++ iids_e f.

Definition isz_e (f : eform) : nat := ol f + length (ei f).

Definition iempty_e (f : eform) : bool := match ob f, ei f with [], [] => true | _, _ => false end.

Fixpoint try_ids_e (f1 f2 : eform) (xs cands : list positive) : option (eform * eform * list positive * bool * bool) :=
  match xs with
  | [] => None
  | x :: xs' =>
      if mem x cands then match imove_e f1 f2 x with Some r => Some r | None => try_ids_e f1 f2 xs' cands end
      else try_ids_e f1 f2 xs' cands
  end.

Fixpoint moves_e (fuel k : nat) (f1 f2 : eform) (cands : list positive) (acc : work) : eform * eform * work :=
  match fuel with
  | 0 => (f1, f2, acc)
  | S fuel' =>
      match try_ids_e f1 f2 (ids_of_e f1) cands with
      | Some (f1', g, new, canc, lost) =>
          let acc1 := (S k, Some new) :: acc in
          let acc2 := if lost then match k with 0 => acc1 | S k' => (k', None) :: acc1 end else acc1 in
          moves_e fuel' k f1' g (if canc then ids_of_e f1' else cands) acc2
      | None => (f1, f2, acc)
      end
  end.

Definition put2e (k : nat) (st : list eitem) (mid : list eitem) : list eitem :=
  firstn k st ++ mid ++ skipn (S (S k)) st.

Definition step_e (s : list eitem * work) : list eitem * work :=
  let '(st, w) := s in
  match w with
  | [] => (st, [])
  | (k, cands) :: w' =>
      match nth_error st k, nth_error st (S k) with
      | Some (KF f1), Some (KF f2) =>
          let merged := match cands with None => icompose_e f1 f2 | Some _ => None end in
          match merged with
          | Some (g, no, ni, _) =>
              if iempty_e g then (put2e k st [], w')
              else (put2e k st [KF g], (k, Some (no ++ ni)) :: w')
          | None =>
              let c := match cands with Some c => c | None => ids_of_e f1 end in
              let '(f1', g, acc) := moves_e (isz_e f1 + 1) k f1 f2 c [] in
              if iempty_e f1' then (put2e k st [KF g], acc ++ match k with 0 => w' | S k' => (k', None) :: w' end)
              else (put2e k st [KF f1'; KF g], acc ++ w')
          end
      | _, _ => (st, w')
      end
  end.

Fixpoint settle_e (p : positive) (s : list eitem * work) : list eitem * work :=
  match snd s with
  | [] => s
  | _ =>
      match p with
      | xH => step_e s
      | xO p' => settle_e p' (settle_e p' s)
      | xI p' => step_e (settle_e p' (settle_e p' s))
      end
  end.

Definition insert_e (it : eitem) (st : list eitem) : list eitem :=
  match it with
  | KF f => if iempty_e f then st else fst (settle_e big (it :: st, [(0, None)]))
  | KA _ _ => it :: st
  end.

(** ** Expressions *)

Definition fresh_e (f : form) (c : positive) : eform * positive :=
  let '(g, c') := fresh f c in (of_i g, c').

(** Output [x], at depth [pos], moved down past the outputs [below]
    (nearest first), as [CForm.oswap] allows. *)
Fixpoint bub_down (x : positive * lexp) (below : list (positive * lexp)) (pos : nat)
    (I : list (positive * (lexp * tgt))) (mo : option (PositiveMap.t nat)) {struct below} :
    list (positive * lexp) * list (positive * (lexp * tgt)) * option (PositiveMap.t nat) :=
  match below with
  | [] => ([x], I, mo)
  | y :: below' =>
      if before F (snd y) (snd x) then
        let m := match mo with Some m => m | None => idx_of I end in
        match cnt m (S pos) with
        | 0 => let '(r, I', mo') := bub_down x below' (S pos) I (Some m) in (y :: r, I', mo')
        | S _ =>
            match swap_in pos (snd y) I with
            | Some I' => let '(r, I'', mo') := bub_down x below' (S pos) I' (Some (idx_move m (S pos))) in (y :: r, I'', mo')
            | None => (x :: below, I, Some m)
            end
        end
      else (x :: below, I, mo)
  end.

(** The top outputs [pre] (top first, the first at depth [k]) placed,
    the lowest of them first. *)
Fixpoint place_down (k : nat) (pre rest : list (positive * lexp)) (I : list (positive * (lexp * tgt)))
    (mo : option (PositiveMap.t nat)) : list (positive * lexp) * list (positive * (lexp * tgt)) * option (PositiveMap.t nat) :=
  match pre with
  | [] => (rest, I, mo)
  | x :: pre' =>
      let '(r', I', mo') := place_down (S k) pre' rest I mo in
      bub_down x r' k I' mo'
  end.

(** The top [r] outputs placed (as [CRun.place_out_down] from depth
    [r - 1] up to [0]). *)
Definition place_out_top (r : nat) (e : eform) : eform :=
  let top := rev (ob e) in
  let '(o, Is, _) := place_down 0 (firstn r top) (skipn r top) (ei e) None in mkE (rev o) (ol e) Is.

(** [f] under the lifts [L], built at once. *)
Definition lift_e (L : list lexp) (f : eform) (c : positive) : eform :=
  let n := length L in
  mkE (ob f ++ rev (combine (pseq c n) L)) (ol f + n)
      (combine (pseq (padd c n) n) (mapi_from 0 (fun k h => (h, TR h 0 k)) L)
       ++ map (fun '(id, (g, t)) => (id, (g, shift_ts L t))) (ei f)).

(** Cheap conditions that [absorb2] also checks, tested first: the
    outputs below the read are on labels ordered against [l], but for one
    on [l]; the inputs inside are on labels ordered against [l]. *)
Fixpoint below_ok (l : lexp) (n : nat) (O : list (positive * lexp)) (seen : bool) : bool :=
  match n, O with
  | S n', (_, o) :: O' =>
      if lexp_eqb o l then (if seen then false else below_ok l n' O' true)
      else if kd F l o then below_ok l n' O' seen else false
  | _, _ => seen
  end.

Fixpoint allkd_in_e (l : lexp) (I : list (positive * (lexp * tgt))) : bool :=
  match I with [] => true | (_, (m, _)) :: I' => if kd F l m then allkd_in_e l I' else false end.

Definition pre_x (x : positive * (lexp * tgt)) (inside : list (positive * (lexp * tgt))) (e : eform) : bool :=
  match x with
  | (_, (l, TR z 0 d)) =>
      if lexp_eqb z l then
        if Nat.leb d (ol e) then if below_ok l (ol e - d) (ob e) false then allkd_in_e l inside else false
        else false
      else false
  | _ => false
  end.

(** The restores, innermost first, absorbed where they can be: [rf] is
    the inputs up to restore [p], nearest first, [inside] those after it.
    [k] counts the restores kept. *)
Fixpoint absorb_walk (fuel p : nat) (rf inside : list (positive * (lexp * tgt))) (e : eform) (k : nat) : eform * nat :=
  match fuel with
  | 0 => (e, k)
  | S fuel' =>
      match rf with
      | [] => (e, k)
      | x :: rf' =>
          match (if pre_x x inside e then iabsorb_e p e else None) with
          | Some e' => absorb_walk fuel' (pred p) (rev (firstn p (ei e'))) (skipn p (ei e')) e' k
          | None => absorb_walk fuel' (pred p) rf' (x :: inside) e (S k)
          end
      end
  end.

Definition lift_many_e (L : list lexp) (it : eitem) (c : positive) : eitem * positive :=
  match it with
  | KA L' n => (KA (L ++ L') n, c)
  | KF f =>
      let n := length L in
      let f0 := lift_e L f c in
      let '(f1, k) := absorb_walk n (pred n) (rev (firstn n (ei f0))) (skipn n (ei f0)) f0 0 in
      let f2 := mkE (ob f1) (ol f1) (place_front k (ei f1)) in
      (KF (place_out_top (Nat.min k (ol f2)) f2), padd c (n + n))
  end.

Fixpoint insert_lifted_e (L : list lexp) (w : list eitem) (st : list eitem) (c : positive) : list eitem * positive :=
  match w with
  | [] => (st, c)
  | it :: w' =>
      let '(st1, c1) := insert_lifted_e L w' st c in
      let '(it', c2) := lift_many_e L it c1 in
      (insert_e it' st1, c2)
  end.

Fixpoint rnorm2 (e : aexp) (st : list eitem) (c : positive) {struct e} : list eitem * positive :=
  match e with
  | AId => (st, c)
  | AAtom n => (insert_e (KA [] n) st, c)
  | ACompose a b => let '(st1, c1) := rnorm2 a st c in rnorm2 b st1 c1
  | AOuter h a => let '(f, c1) := fresh_e (weak h) c in rnorm2 a (insert_e (KF f) st) c1
  | AInner h t a =>
      let '(f, c1) := fresh_e (entry h t) c in
      let fix peel (R : list lexp) (a : aexp) (st : list eitem) (c : positive) {struct a} : list eitem * positive :=
        match a with
        | ALift h' a' => peel (h' :: R) a' st c
        | _ => let '(w, c1) := rnorm2 a [] c in insert_lifted_e (rev R) w st c1
        end in
      peel [h] a (insert_e (KF f) st) c1
  | ALift h a =>
      let fix peel (R : list lexp) (a : aexp) (st : list eitem) (c : positive) {struct a} : list eitem * positive :=
        match a with
        | ALift h' a' => peel (h' :: R) a' st c
        | _ => let '(w, c1) := rnorm2 a [] c in insert_lifted_e (rev R) w st c1
        end in
      peel [h] a st c
  end.

Definition rrun2 (e : aexp) : fword := map estrip (fst (rnorm2 e [] xH)).

End Run2.

(** The chain of lifts inside [rnorm2], as a function of its own. *)
Section Peel2.
Variable F : order.
Fixpoint peel2 (R : list lexp) (a : aexp) (st : list eitem) (c : positive) {struct a} : list eitem * positive :=
  match a with
  | ALift h' a' => peel2 (h' :: R) a' st c
  | _ => let '(w, c1) := rnorm2 F a [] c in insert_lifted_e F (rev R) w st c1
  end.
End Peel2.

Lemma fresh_e_eq f c : fresh_e f c = (of_i (fst (fresh f c)), snd (fresh f c)).
Proof. reflexivity. Qed.

Lemma fresh_ff f c : ff (fst (fresh f c)) = f.
Proof. reflexivity. Qed.

Lemma rnorm2_outer F h a st c : rnorm2 F (AOuter h a) st c = rnorm2 F a (insert_e F (KF (of_i (fst (fresh (weak h) c)))) st) (snd (fresh (weak h) c)).
Proof. reflexivity. Qed.

Lemma rnorm2_lift F h a st c : rnorm2 F (ALift h a) st c = peel2 F [h] a st c.
Proof. reflexivity. Qed.

Lemma rnorm2_inner F h t a st c :
  rnorm2 F (AInner h t a) st c = peel2 F [h] a (insert_e F (KF (of_i (fst (fresh (entry h t) c)))) st) (snd (fresh (entry h t) c)).
Proof. reflexivity. Qed.

(** ** Soundness *)

Section Sound2.

Variable F : order.
Variable M : cmodel.
Hypothesis HM : ccons F M.

Local Notation fd := (fden M).

(** Reads no deeper than the outputs; the number of outputs right. *)
Definition tok (n : nat) (t : tgt) : Prop := match t with TR _ _ d => d <= n | TT _ _ => True end.
Definition wfd (f : form) : Prop := Forall (fun lt => tok (length (fout f)) (snd lt)) (fin f).
Definition ok (e : eform) : Prop := ol e = length (ob e) /\ wfd (eff e).

Lemma length_zipd {X} ids (l : list X) : length (zipd ids l) = length l.
Proof. revert ids; induction l as [|x l IH]; intros [|i ids]; cbn; rewrite ?IH; reflexivity. Qed.

Lemma map_snd_zipd {X} ids (l : list X) : map snd (zipd ids l) = l.
Proof. revert ids; induction l as [|x l IH]; intros [|i ids]; cbn; rewrite ?IH; reflexivity. Qed.

Lemma eff_fout e : fout (eff e) = rev (map snd (ob e)).
Proof. reflexivity. Qed.

Lemma eff_len e : length (fout (eff e)) = length (ob e).
Proof. unfold eff; cbn; rewrite length_rev, length_map; reflexivity. Qed.

Lemma eff_of_i f : eff (of_i f) = mkF (fout (ff f)) (map (fun '(l, t) => (l, clamp (length (fout (ff f))) t)) (fin (ff f))).
Proof. unfold eff, of_i; cbn; rewrite map_rev, rev_involutive, !map_snd_zipd; reflexivity. Qed.

Lemma pushes_clamp0 O I b x : pushes M O (map (fun '(l, t) => (l, clamp (length O) t)) I) b x = pushes M O I b x.
Proof. pose proof (pushes_clamp M O [] I b x) as H; rewrite app_nil_r in H; exact H. Qed.

Lemma of_i_sound f x : fd (eff (of_i f)) x = fd (ff f) x.
Proof. rewrite eff_of_i; unfold fden; cbn [fout fin]; apply pushes_clamp0. Qed.

Lemma tok_clamp n t : tok n (clamp n t).
Proof. destruct t; cbn; lia. Qed.

Lemma of_i_ok f : ok (of_i f).
Proof.
  split; [cbn; rewrite length_rev, length_zipd; reflexivity|].
  unfold wfd; rewrite eff_of_i; cbn [fout fin].
  apply Forall_forall; intros [l t] H; apply in_map_iff in H as [[l' t'] [E _]]; injection E as <- <-; apply tok_clamp.
Qed.

(** *** Reads, from the bottom *)

Lemma skipn_cons_nth {X} (l : list X) n dflt : n < length l -> skipn n l = nth n l dflt :: skipn (S n) l.
Proof. revert l; induction n as [|n IH]; intros [|a l] H; cbn in *; try lia; [reflexivity|apply IH; lia]. Qed.

Lemma nread_up_eq (o : list (positive * lexp)) z i d : d <= length o ->
  nread_up F (skipn (length o - d) o) z i d = nread F (rev (map snd o)) z i d.
Proof.
  revert i; induction d as [|d IH]; intros i Hd; [destruct (skipn _ o); reflexivity|].
  rewrite (skipn_cons_nth o (length o - S d) (xH, LNone)) by lia.
  replace (S (length o - S d)) with (length o - d) by lia.
  cbn [nread_up nread]; rewrite length_rev, length_map.
  replace (Nat.ltb d (length o)) with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite rev_nth by (rewrite length_map; lia); rewrite length_map.
  replace (length o - S d) with (length o - S d) by reflexivity.
  rewrite (map_nth snd o (xH, LNone)); destruct (nth (length o - S d) o (xH, LNone)) as [y v]; cbn [snd].
  destruct (lexp_eqb v z); [apply IH; lia|]; destruct (kd F z v); [apply IH; lia|reflexivity].
Qed.

Lemma nread_big O z i d : length O < d -> nread F O z i d = TR z i d.
Proof.
  destruct d as [|d]; intros H; [lia|]; cbn [nread].
  replace (Nat.ltb d (length O)) with false by (symmetry; apply Nat.ltb_ge; lia); reflexivity.
Qed.

Lemma nread_e_eq e t : ol e = length (ob e) -> nread_e F e t = ntgt F (fout (eff e)) t.
Proof.
  intros H; destruct t as [z i d|u p]; [|reflexivity]; cbn [nread_e ntgt]; rewrite eff_fout, H.
  destruct (Nat.leb d (length (ob e))) eqn:L.
  - apply Nat.leb_le in L; apply nread_up_eq, L.
  - apply Nat.leb_gt in L; symmetry; apply nread_big; rewrite length_rev, length_map; exact L.
Qed.

Lemma nread_depth O z i d : tok d (nread F O z i d).
Proof.
  revert i; induction d as [|d IH]; intros i; [cbn; lia|]; cbn [nread].
  destruct (Nat.ltb d (length O)); [|cbn; lia].
  destruct (lexp_eqb _ z); [pose proof (IH (S i)) as H; destruct (nread F O z (S i) d); cbn in *; lia|].
  destruct (kd F z _); [pose proof (IH i) as H; destruct (nread F O z i d); cbn in *; lia|cbn; lia].
Qed.

Lemma tok_ntgt n O t : tok n t -> tok n (ntgt F O t).
Proof.
  destruct t as [z i d|u p]; cbn; [|auto]; intros H.
  pose proof (nread_depth O z i d) as N; destruct (nread F O z i d); cbn in *; lia.
Qed.

(** *** Inputs related one to one *)

Definition irel (O : list lexp) (x : cU M) (a b : positive * (lexp * tgt)) : Prop :=
  fst (snd a) = fst (snd b) /\ tden M O (snd (snd a)) x = tden M O (snd (snd b)) x
  /\ forall n, tok n (snd (snd b)) -> tok n (snd (snd a)).

Lemma pushes_irel O x I I' b : Forall2 (irel O x) I' I -> pushes M O (map snd I') b x = pushes M O (map snd I) b x.
Proof.
  induction 1 as [|[i [l t]] [i' [l' t']] I I' [E1 [E2 _]] _ IH]; [reflexivity|]; cbn in *; subst; rewrite IH, E2; reflexivity.
Qed.

Lemma wfd_irel O x n I I' : Forall2 (irel O x) I' I -> Forall (fun lt => tok n (snd lt)) (map snd I) ->
  Forall (fun lt => tok n (snd lt)) (map snd I').
Proof.
  induction 1 as [|a b I I' [_ [_ E3]] _ IH]; cbn; [auto|]; intros H; inversion H; subst; constructor; auto.
Qed.

Lemma irel_refl O x a : irel O x a a.
Proof. split; [reflexivity|split; [reflexivity|auto]]. Qed.

Lemma Forall2_refl_irel O x I : Forall2 (irel O x) I I.
Proof. induction I; constructor; auto using irel_refl. Qed.

Lemma reread_front_rel e n x : ol e = length (ob e) -> Forall2 (irel (fout (eff e)) x) (ei (reread_front F n e)) (ei e).
Proof.
  intros H; unfold reread_front; cbn [ei]; generalize (ei e); induction n as [|n IH]; intros [|[i [l t]] I];
    cbn [map_front]; try apply Forall2_refl_irel; constructor; [|apply IH].
  split; [reflexivity|split]; cbn [snd fst]; [rewrite nread_e_eq by exact H; apply (ntgt_sound F M HM)|].
  intros k Hk; rewrite nread_e_eq by exact H; apply tok_ntgt, Hk.
Qed.

Lemma reread_at_rel e j x : ol e = length (ob e) -> Forall2 (irel (fout (eff e)) x) (ei (reread_at F j e)) (ei e).
Proof.
  intros H; unfold reread_at; cbn [ei]; generalize (ei e); intros L; induction L as [|[i [l t]] I IH]; cbn [map]; constructor; auto.
  split; [reflexivity|split]; cbn [snd fst]; destruct (is_dep j t); try reflexivity; try auto.
  - rewrite nread_e_eq by exact H; apply (ntgt_sound F M HM).
  - intros k Hk; rewrite nread_e_eq by exact H; apply tok_ntgt, Hk.
Qed.

(** An input-only change preserving [irel] keeps meaning and [ok]. *)
Lemma inputs_rel e I' x : Forall2 (irel (fout (eff e)) x) I' (ei e) ->
  fd (eff (mkE (ob e) (ol e) I')) x = fd (eff e) x.
Proof. intros R; unfold fden; cbn [eff fout fin]; apply pushes_irel, R. Qed.

Lemma inputs_ok e I' x : ok e -> Forall2 (irel (fout (eff e)) x) I' (ei e) -> ok (mkE (ob e) (ol e) I').
Proof.
  intros [H1 H2] R; split; [exact H1|]; unfold wfd in *; cbn [eff fout fin] in *.
  eapply wfd_irel; eassumption.
Qed.


(** *** Placing inputs *)

Lemma pushes_swap2 O (a c : positive * (lexp * tgt)) s b z : before F (lab_i c) (lab_i a) = true ->
  pushes M O (map snd (c :: a :: s)) b z = pushes M O (map snd (a :: c :: s)) b z.
Proof.
  destruct a as [i [l t]], c as [j [m u]]; unfold lab_i; cbn; intros B.
  apply (kd_push_push F M HM); apply bk; exact B.
Qed.

Lemma pushes_app_mid O (A s1 s2 : list (positive * (lexp * tgt))) b z :
  pushes M O (map snd s1) b z = pushes M O (map snd s2) b z ->
  pushes M O (map snd (A ++ s1)) b z = pushes M O (map snd (A ++ s2)) b z.
Proof. intros H; rewrite !map_app, !pushes_app, H; reflexivity. Qed.

Lemma pushes_cons_eq O (a : positive * (lexp * tgt)) (s1 s2 : list (positive * (lexp * tgt))) b z : (forall b, pushes M O (map snd s1) b z = pushes M O (map snd s2) b z) ->
  pushes M O (map snd (a :: s1)) b z = pushes M O (map snd (a :: s2)) b z.
Proof. destruct a as [i [l t]]; cbn; intros H; rewrite H; reflexivity. Qed.

Lemma bub_in_sound O x I b z : pushes M O (map snd (bub_in F x I)) b z = pushes M O (map snd (x :: I)) b z
  /\ Permutation (bub_in F x I) (x :: I).
Proof.
  revert b; induction I as [|y I IH]; intros b; cbn [bub_in]; [split; reflexivity|].
  destruct (before F (lab_i y) (lab_i x)) eqn:B; [|split; reflexivity].
  split.
  - rewrite (pushes_cons_eq O y _ (x :: I) b z) by (intros b'; apply IH); apply pushes_swap2, B.
  - destruct (IH b) as [_ P]; rewrite P; apply perm_swap.
Qed.

Lemma place_front_sound O n I b z : pushes M O (map snd (place_front F n I)) b z = pushes M O (map snd I) b z
  /\ Permutation (place_front F n I) I.
Proof.
  revert I b; induction n as [|n IH]; intros [|x I] b; cbn [place_front]; try (split; reflexivity).
  destruct (bub_in_sound O x (place_front F n I) b z) as [E P]; rewrite E; split.
  - apply pushes_cons_eq; intros b'; apply IH.
  - rewrite P; apply perm_skip, IH; exact b.
Qed.

Lemma ins_out_sound O x rp s b z : pushes M O (map snd (rev (ins_out F x rp) ++ s)) b z = pushes M O (map snd (rev rp ++ x :: s)) b z
  /\ Permutation (ins_out F x rp) (x :: rp).
Proof.
  revert s; induction rp as [|y r IH]; intros s; cbn [ins_out]; [split; reflexivity|].
  destruct (before F (lab_i x) (lab_i y)) eqn:B; [|split; [cbn [rev]; rewrite <- !app_assoc; reflexivity|reflexivity]].
  split.
  - cbn [rev]; rewrite <- !app_assoc; cbn [app].
    rewrite (proj1 (IH (y :: s))); apply pushes_app_mid, pushes_swap2, B.
  - rewrite (proj2 (IH s)); apply perm_swap.
Qed.

Lemma out_pass_sound O rp suf b z : pushes M O (map snd (out_pass F rp suf)) b z = pushes M O (map snd (rev rp ++ suf)) b z
  /\ Permutation (out_pass F rp suf) (rev rp ++ suf).
Proof.
  revert rp; induction suf as [|x s IH]; intros rp; cbn [out_pass]; [rewrite app_nil_r; split; reflexivity|].
  destruct (IH (ins_out F x rp)) as [E P]; destruct (ins_out_sound O x rp s b z) as [E2 P2]; split.
  - rewrite E, E2; reflexivity.
  - rewrite P, P2; cbn [rev]; rewrite <- app_assoc; reflexivity.
Qed.

Lemma place_suffix_out_sound O p I b z : pushes M O (map snd (place_suffix_out F p I)) b z = pushes M O (map snd I) b z
  /\ Permutation (place_suffix_out F p I) I.
Proof.
  unfold place_suffix_out; destruct (out_pass_sound O (rev (firstn p I)) (skipn p I) b z) as [E P].
  rewrite rev_involutive, firstn_skipn in E, P; split; assumption.
Qed.

(** An input change that keeps the pushes and permutes keeps meaning and
    [ok]. *)
Lemma perm_inputs e I' x : (forall b, pushes M (fout (eff e)) (map snd I') b x = pushes M (fout (eff e)) (map snd (ei e)) b x) ->
  fd (eff (mkE (ob e) (ol e) I')) x = fd (eff e) x.
Proof. intros H; unfold fden; cbn [eff fout fin]; apply H. Qed.

Lemma perm_ok e I' : ok e -> Permutation I' (ei e) -> ok (mkE (ob e) (ol e) I').
Proof.
  intros [H1 H2] P; split; [exact H1|]; unfold wfd in *; cbn [eff fout fin] in *.
  rewrite Forall_forall in *; intros lt Hin; apply H2.
  apply (Permutation_in _ (Permutation_map snd P)), Hin.
Qed.


(** *** The map from depths to the number of reads there *)

Definition cntI (d : nat) (I : list (positive * (lexp * tgt))) : nat :=
  length (filter (fun y => is_dep d (snd (snd y))) I).

Definition idx_ok (m : PositiveMap.t nat) (I : list (positive * (lexp * tgt))) : Prop := forall d, cnt m d = cntI d I.

Lemma cnt_add m d v d' : cnt (PositiveMap.add (dkey d) v m) d' = if Nat.eqb d d' then v else cnt m d'.
Proof.
  unfold cnt; destruct (Nat.eqb d d') eqn:E.
  - apply Nat.eqb_eq in E; subst; rewrite PositiveMap.gss; reflexivity.
  - apply Nat.eqb_neq in E; rewrite PositiveMap.gso; [reflexivity|].
    intros K; apply E; symmetry; apply SuccNat2Pos.inj; exact K.
Qed.

Lemma cnt_empty d : cnt (PositiveMap.empty nat) d = 0.
Proof. unfold cnt; rewrite PositiveMap.gempty; reflexivity. Qed.

Lemma cnt_idx_add m t d : cnt (idx_add m t) d = cnt m d + (if is_dep d t then 1 else 0).
Proof.
  destruct t as [z i d'|u p]; cbn [idx_add is_dep tdep]; [|lia].
  rewrite cnt_add; destruct (Nat.eqb d' d) eqn:E; [apply Nat.eqb_eq in E; subst; lia|lia].
Qed.

Lemma idx_of_ok I : idx_ok (idx_of I) I.
Proof.
  unfold idx_of, idx_ok, cntI.
  assert (G : forall (J : list (positive * (lexp * tgt))) m d, cnt (fold_left (fun m x => idx_add m (snd (snd x))) J m) d
                             = cnt m d + length (filter (fun y : positive * (lexp * tgt) => is_dep d (snd (snd y))) J)).
  { induction J as [|y J IH]; intros m d; cbn [fold_left filter]; [cbn; lia|].
    rewrite IH, cnt_idx_add; destruct (is_dep d (snd (snd y))); cbn; lia. }
  intros d; rewrite G, cnt_empty; reflexivity.
Qed.

Definition tag_omap (g : tgt -> option tgt) (I : list (positive * (lexp * tgt))) :=
  omap (fun '(id, (l, t)) => option_map (fun t' => (id, (l, t'))) (g t)) I.

Lemma swap_in_zero m I k b : idx_ok m I -> cnt m (S k) = 0 -> swap_in F k b I = Some I.
Proof.
  intros H Z; rewrite H in Z; unfold cntI in Z; unfold swap_in; clear H.
  induction I as [|[i [l t]] I IH]; [reflexivity|]; cbn [omap].
  cbn [filter snd] in Z; destruct (is_dep (S k) t) eqn:D; [discriminate|].
  rewrite IH by exact Z.
  destruct t as [z j d|u p]; cbn [swap_read option_map]; [|reflexivity].
  cbn [is_dep tdep] in D; rewrite D; reflexivity.
Qed.

Lemma cntI_cons d y I : cntI d (y :: I) = (if is_dep d (snd (snd y)) then 1 else 0) + cntI d I.
Proof. unfold cntI; cbn [filter]; destruct (is_dep d (snd (snd y))); reflexivity. Qed.

Lemma is_dep_TR d z i d' : is_dep d (TR z i d') = Nat.eqb d' d.
Proof. reflexivity. Qed.

Ltac eqbs := repeat (match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b); try subst end); simpl; try lia.

Lemma swap_read_dep k b t t' : swap_read F k b t = Some t' -> forall d,
  (if is_dep d t' then 1 else 0) =
  (if Nat.eqb d (S k) then 0 else if Nat.eqb d (S (S k)) then (if is_dep (S (S k)) t then 1 else 0) + (if is_dep (S k) t then 1 else 0)
   else if is_dep d t then 1 else 0).
Proof.
  intros G d; destruct t as [z j dd|u p]; cbn [swap_read] in G.
  - destruct (Nat.eqb dd (S k)) eqn:Dk.
    + apply Nat.eqb_eq in Dk; subst dd.
      assert (exists j', t' = TR z j' (S (S k))) as [j' ->]
        by (destruct (lexp_eqb z b); [destruct j; [discriminate|injection G as <-; eexists; reflexivity]|
            destruct (kd F z b); [injection G as <-; eexists; reflexivity|discriminate]]).
      rewrite !is_dep_TR; eqbs.
    + injection G as <-; rewrite !is_dep_TR; apply Nat.eqb_neq in Dk; eqbs.
  - injection G as <-; cbn [is_dep tdep]; eqbs.
Qed.

Lemma swap_in_depths k b I I' : swap_in F k b I = Some I' -> forall d,
  cntI d I' = if Nat.eqb d (S k) then 0 else if Nat.eqb d (S (S k)) then cntI (S (S k)) I + cntI (S k) I else cntI d I.
Proof.
  unfold swap_in; revert I'; induction I as [|[i [l t]] I IH]; intros I' E d; cbn [omap] in E.
  - injection E as <-; unfold cntI; cbn; eqbs.
  - destruct (swap_read F k b t) as [t'|] eqn:G; cbn [option_map] in E; [|discriminate].
    destruct (omap _ I) as [I''|] eqn:E2; [|discriminate]; injection E as <-.
    specialize (IH I'' eq_refl d); rewrite !cntI_cons, IH; cbn [snd].
    rewrite (swap_read_dep k b t t' G d); eqbs.
Qed.

Lemma idx_move_ok m I k b I' : idx_ok m I -> swap_in F k b I = Some I' -> idx_ok (idx_move m (S k)) I'.
Proof.
  intros H E d; rewrite (swap_in_depths k b I I' E d); unfold idx_move; rewrite !cnt_add, !H; eqbs.
Qed.

Lemma swap_in_map k b I I' : swap_in F k b I = Some I' ->
  omap (fun '(l, t) => option_map (fun t' => (l, t')) (swap_read F k b t)) (map snd I) = Some (map snd I').
Proof.
  unfold swap_in; revert I'; induction I as [|[i [l t]] I IH]; intros I' E; cbn -[swap_read] in *.
  - injection E as <-; reflexivity.
  - destruct (swap_read F k b t) as [t'|]; cbn -[swap_read] in *; [|discriminate].
    destruct (omap _ I) as [I''|]; [|discriminate]; injection E as <-; rewrite (IH I'' eq_refl); reflexivity.
Qed.

Lemma swap_in_tok k b I I' n : swap_in F k b I = Some I' -> S (S k) <= n ->
  Forall (fun lt => tok n (snd lt)) (map snd I) -> Forall (fun lt => tok n (snd lt)) (map snd I').
Proof.
  unfold swap_in; revert I'; induction I as [|[i [l t]] I IH]; intros I' E Hn H; cbn [omap map] in *.
  - injection E as <-; constructor.
  - inversion H as [|a b0 H1 H2]; subst.
    destruct (swap_read F k b t) as [t'|] eqn:Sw; cbn in *; [|discriminate].
    destruct (omap _ I) as [I''|]; [|discriminate]; injection E as <-; cbn; constructor; [|apply IH; auto].
    cbn; destruct t as [z j d|u p]; cbn in Sw, H1 |- *.
    + destruct (Nat.eqb d (S k)); [destruct (lexp_eqb z b); [destruct j|destruct (kd F z b)]|]; try discriminate;
        injection Sw as <-; cbn; lia.
    + injection Sw as <-; exact Logic.I.
Qed.

(** One output swap, as [CForm.oswap]. *)
Lemma oswap_step (top bot : list lexp) a c I I' z :
  before F c a = true -> swap_in F (length top) c I = Some I' ->
  fd (mkF (top ++ c :: a :: bot) (map snd I')) z = fd (mkF (top ++ a :: c :: bot) (map snd I)) z.
Proof.
  intros B Sw; apply (oswap_sound F M HM (length top)).
  assert (N1 : nth_error (top ++ a :: c :: bot) (length top) = Some a) by (rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity).
  assert (N2 : nth_error (top ++ a :: c :: bot) (S (length top)) = Some c)
    by (rewrite nth_error_app2 by lia; replace (S (length top) - length top) with 1 by lia; reflexivity).
  unfold oswap; cbn -[nth_error omap swap_at before swap_read]; rewrite N1, N2, B, (swap_in_map _ _ _ _ Sw), swap_at_app; reflexivity.
Qed.


Definition itok (n : nat) (I : list (positive * (lexp * tgt))) : Prop := Forall (fun lt => tok n (snd lt)) (map snd I).
Definition iok (mo : option (PositiveMap.t nat)) (I : list (positive * (lexp * tgt))) : Prop :=
  forall m, mo = Some m -> idx_ok m I.

Lemma get_idx_ok mo I : iok mo I -> idx_ok (match mo with Some m => m | None => idx_of I end) I.
Proof. destruct mo as [m|]; [intros H; apply H; reflexivity|intros _; apply idx_of_ok]. Qed.

Lemma rev_mid (below acc : list (positive * lexp)) y x :
  rev (map snd (below ++ y :: x :: acc)) = rev (map snd acc) ++ snd x :: snd y :: rev (map snd below).
Proof. rewrite map_app, rev_app_distr; cbn; rewrite <- !app_assoc; reflexivity. Qed.

(** *** Outputs moved up from the bottom *)

Lemma bub_out_sound x acc : forall below pos I mo r I' mo' n,
  bub_out F x acc pos I mo = (r, I', mo') -> pos = length acc -> n = length below + S (length acc) ->
  iok mo I -> itok n I ->
  (forall z, fd (mkF (rev (map snd (below ++ r))) (map snd I')) z = fd (mkF (rev (map snd (below ++ x :: acc))) (map snd I)) z)
  /\ iok mo' I' /\ length r = S (length acc) /\ itok n I'.
Proof.
  induction acc as [|y acc IH]; intros below pos I mo r I' mo' n E Hp Hn Hi Ht; cbn [bub_out] in E.
  - injection E as <- <- <-; auto.
  - destruct (before F (snd x) (snd y)) eqn:B; [|injection E as <- <- <-; auto].
    pose proof (get_idx_ok mo I Hi) as Hm; set (m := match mo with Some m => m | None => idx_of I end) in *.
    cbn [length] in Hp; subst pos; cbn [pred] in E.
    destruct (cnt m (S (length acc))) as [|c] eqn:C.
    + destruct (bub_out F x acc (length acc) I (Some m)) as [[r0 I0] mo0] eqn:E0; injection E as <- <- <-.
      destruct (IH (below ++ [y]) (length acc) I (Some m) r0 I0 mo0 n E0 eq_refl) as [S1 [S2 [S3 S4]]];
        [rewrite length_app; cbn in *; lia|intros m' Hm'; injection Hm' as <-; exact Hm|exact Ht|].
      split; [|split; [exact S2|split; [cbn; lia|exact S4]]]; intros z.
      replace (below ++ y :: r0) with ((below ++ [y]) ++ r0) by (rewrite <- app_assoc; reflexivity); rewrite S1.
      replace ((below ++ [y]) ++ x :: acc) with (below ++ y :: x :: acc) by (rewrite <- app_assoc; reflexivity).
      rewrite !rev_mid; apply oswap_step; [exact B|]; rewrite length_rev, length_map; apply (swap_in_zero m); [exact Hm|exact C].
    + destruct (swap_in F (length acc) (snd x) I) as [I1|] eqn:Sw.
      * destruct (bub_out F x acc (length acc) I1 (Some (idx_move m (S (length acc))))) as [[r0 I0] mo0] eqn:E0; injection E as <- <- <-.
        destruct (IH (below ++ [y]) (length acc) I1 _ r0 I0 mo0 n E0 eq_refl) as [S1 [S2 [S3 S4]]];
          [rewrite length_app; cbn in *; lia|intros m' Hm'; injection Hm' as <-; apply (idx_move_ok m I _ _ _ Hm Sw)|
           apply (swap_in_tok _ _ _ _ _ Sw); [cbn in Hn; lia|exact Ht]|].
        split; [|split; [exact S2|split; [cbn; lia|exact S4]]]; intros z.
        replace (below ++ y :: r0) with ((below ++ [y]) ++ r0) by (rewrite <- app_assoc; reflexivity); rewrite S1.
        replace ((below ++ [y]) ++ x :: acc) with (below ++ y :: x :: acc) by (rewrite <- app_assoc; reflexivity).
        rewrite !rev_mid; apply oswap_step; [exact B|]; rewrite length_rev, length_map; exact Sw.
      * injection E as <- <- <-; split; [reflexivity|split; [intros m' Hm'; injection Hm' as <-; exact Hm|auto]].
Qed.

Lemma place_rng_sound rng : forall k n above below I mo o I' mo',
  place_rng F k n rng above I mo = (o, I', mo') -> length below = k -> n = k + length rng + length above ->
  iok mo I -> itok n I ->
  (forall z, fd (mkF (rev (map snd (below ++ o))) (map snd I')) z = fd (mkF (rev (map snd (below ++ rng ++ above))) (map snd I)) z)
  /\ iok mo' I' /\ length o = length rng + length above /\ itok n I'.
Proof.
  induction rng as [|x rng IH]; intros k n above below I mo o I' mo' E Hk Hn Hi Ht; cbn [place_rng] in E.
  - injection E as <- <- <-; auto.
  - destruct (place_rng F (S k) n rng above I mo) as [[a' I1] mo1] eqn:E1.
    destruct (IH (S k) n above (below ++ [x]) I mo a' I1 mo1 E1) as [S1 [S2 [S3 S4]]];
      [rewrite length_app; cbn; lia|cbn in Hn; lia|exact Hi|exact Ht|].
    destruct (bub_out_sound x a' below (n - 1 - k) I1 mo1 o I' mo' n E) as [T1 [T2 [T3 T4]]];
      [rewrite S3; cbn in Hn; lia|rewrite S3; cbn in Hn; lia|exact S2|exact S4|].
    split; [|split; [exact T2|split; [rewrite T3, S3; reflexivity|exact T4]]]; intros z.
    rewrite T1; replace (below ++ x :: a') with ((below ++ [x]) ++ a') by (rewrite <- app_assoc; reflexivity).
    rewrite S1, <- app_assoc; reflexivity.
Qed.

Lemma place_out_bottom_sound r e : ok e ->
  (forall z, fd (eff (place_out_bottom F r e)) z = fd (eff e) z) /\ ok (place_out_bottom F r e).
Proof.
  intros [H1 H2]; unfold place_out_bottom.
  destruct (place_rng F 0 (ol e) (firstn r (ob e)) (skipn r (ob e)) (ei e) None) as [[o I] mo] eqn:E.
  destruct (place_rng_sound _ 0 (ol e) _ [] _ _ _ _ _ E eq_refl) as [S1 [_ [S3 S4]]];
    [rewrite length_firstn, length_skipn, H1; lia|intros m Hm; discriminate|unfold itok; unfold wfd in H2; rewrite eff_len in H2; rewrite H1; exact H2|].
  split; [intros z; specialize (S1 z); cbn [app] in S1; rewrite firstn_skipn in S1; exact S1|split; cbn [ol ob]].
  - rewrite S3, <- length_app, firstn_skipn; exact H1.
  - unfold wfd; rewrite eff_len; cbn [ob ei]; rewrite S3, <- length_app, firstn_skipn, <- H1; exact S4.
Qed.

(** *** Outputs moved down from the top *)

Lemma bub_down_sound x below : forall above pos I mo r I' mo' n,
  bub_down F x below pos I mo = (r, I', mo') -> pos = length above -> n = length above + S (length below) ->
  iok mo I -> itok n I ->
  (forall z, fd (mkF (map snd (above ++ r)) (map snd I')) z = fd (mkF (map snd (above ++ x :: below)) (map snd I)) z)
  /\ iok mo' I' /\ length r = S (length below) /\ itok n I'.
Proof.
  induction below as [|y below IH]; intros above pos I mo r I' mo' n E Hp Hn Hi Ht; cbn [bub_down] in E.
  - injection E as <- <- <-; auto.
  - destruct (before F (snd y) (snd x)) eqn:B; [|injection E as <- <- <-; auto].
    pose proof (get_idx_ok mo I Hi) as Hm; set (m := match mo with Some m => m | None => idx_of I end) in *.
    subst pos.
    assert (L : forall r0, map snd (above ++ y :: r0) = map snd (above ++ [y]) ++ map snd r0)
      by (intros; rewrite <- map_app, <- app_assoc; reflexivity).
    assert (L2 : map snd (above ++ x :: y :: below) = map snd above ++ snd x :: snd y :: map snd below)
      by (rewrite map_app; reflexivity).
    assert (L3 : map snd ((above ++ [y]) ++ x :: below) = map snd above ++ snd y :: snd x :: map snd below)
      by (rewrite <- app_assoc, map_app; reflexivity).
    destruct (cnt m (S (length above))) as [|c] eqn:C.
    + destruct (bub_down F x below (S (length above)) I (Some m)) as [[r0 I0] mo0] eqn:E0; injection E as <- <- <-.
      destruct (IH (above ++ [y]) (S (length above)) I (Some m) r0 I0 mo0 n E0) as [S1 [S2 [S3 S4]]];
        [rewrite length_app; cbn; lia|rewrite length_app; cbn in *; lia|intros m' Hm'; injection Hm' as <-; exact Hm|exact Ht|].
      split; [|split; [exact S2|split; [cbn; lia|exact S4]]]; intros z.
      rewrite L, <- map_app, S1, L3, L2.
      replace (length above) with (length (map snd above)) in C by apply length_map.
      apply oswap_step; [exact B|]; apply (swap_in_zero m); [exact Hm|exact C].
    + destruct (swap_in F (length above) (snd y) I) as [I1|] eqn:Sw.
      * destruct (bub_down F x below (S (length above)) I1 (Some (idx_move m (S (length above))))) as [[r0 I0] mo0] eqn:E0; injection E as <- <- <-.
        destruct (IH (above ++ [y]) (S (length above)) I1 _ r0 I0 mo0 n E0) as [S1 [S2 [S3 S4]]];
          [rewrite length_app; cbn; lia|rewrite length_app; cbn in *; lia|intros m' Hm'; injection Hm' as <-; apply (idx_move_ok m I _ _ _ Hm Sw)|
           apply (swap_in_tok _ _ _ _ _ Sw); [cbn in Hn; lia|exact Ht]|].
        split; [|split; [exact S2|split; [cbn; lia|exact S4]]]; intros z.
        rewrite L, <- map_app, S1, L3, L2.
        replace (length above) with (length (map snd above)) in Sw by apply length_map.
        apply oswap_step; [exact B|exact Sw].
      * injection E as <- <- <-; split; [reflexivity|split; [intros m' Hm'; injection Hm' as <-; exact Hm|auto]].
Qed.

Lemma place_down_sound pre : forall k rest above I mo o I' mo' n,
  place_down F k pre rest I mo = (o, I', mo') -> length above = k -> n = k + length pre + length rest ->
  iok mo I -> itok n I ->
  (forall z, fd (mkF (map snd (above ++ o)) (map snd I')) z = fd (mkF (map snd (above ++ pre ++ rest)) (map snd I)) z)
  /\ iok mo' I' /\ length o = length pre + length rest /\ itok n I'.
Proof.
  induction pre as [|x pre IH]; intros k rest above I mo o I' mo' n E Hk Hn Hi Ht; cbn [place_down] in E.
  - injection E as <- <- <-; auto.
  - destruct (place_down F (S k) pre rest I mo) as [[r' I1] mo1] eqn:E1.
    destruct (IH (S k) rest (above ++ [x]) I mo r' I1 mo1 n E1) as [S1 [S2 [S3 S4]]];
      [rewrite length_app; cbn; lia|cbn in Hn; lia|exact Hi|exact Ht|].
    destruct (bub_down_sound x r' above k I1 mo1 o I' mo' n E) as [T1 [T2 [T3 T4]]];
      [lia|rewrite S3; cbn in Hn; lia|exact S2|exact S4|].
    split; [|split; [exact T2|split; [rewrite T3, S3; reflexivity|exact T4]]]; intros z.
    rewrite T1; replace (above ++ x :: r') with ((above ++ [x]) ++ r') by (rewrite <- app_assoc; reflexivity).
    rewrite S1, <- app_assoc; reflexivity.
Qed.

Lemma place_out_top_sound r e : ok e ->
  (forall z, fd (eff (place_out_top F r e)) z = fd (eff e) z) /\ ok (place_out_top F r e).
Proof.
  intros [H1 H2]; unfold place_out_top.
  destruct (place_down F 0 (firstn r (rev (ob e))) (skipn r (rev (ob e))) (ei e) None) as [[o I] mo] eqn:E.
  destruct (place_down_sound _ 0 _ [] _ _ _ _ _ (ol e) E eq_refl) as [S1 [_ [S3 S4]]];
    [rewrite length_firstn, length_skipn, length_rev, H1; lia|intros m Hm; discriminate|unfold itok; unfold wfd in H2; rewrite eff_len in H2; rewrite H1; exact H2|].
  assert (Lo : length o = length (ob e)) by (rewrite S3, <- length_app, firstn_skipn, length_rev; reflexivity).
  split.
  - intros z; specialize (S1 z); cbn [app] in S1; rewrite firstn_skipn in S1.
    unfold eff; cbn [ob ei ol fout fin]; rewrite map_rev, rev_involutive, S1, map_rev; reflexivity.
  - unfold ok; cbn [ol ob]; split; [rewrite length_rev, Lo; exact H1|].
    unfold wfd, eff; cbn [fout fin ob ei]; rewrite map_rev, rev_involutive, length_map, Lo, <- H1; exact S4.
Qed.


(** *** Composing *)

Definition erase (s : list (positive * (lexp * tgt)) * list (positive * lexp)) : list (lexp * tgt) * list lexp :=
  (map snd (fst s), map snd (snd s)).

Lemma popin_e_spec o rem :
  popin F o (map snd rem) = option_map (option_map (map snd)) (popin_e F o rem).
Proof.
  induction rem as [|[i [l t]] rem IH]; [reflexivity|]; cbn [popin popin_e map snd lab_i fst].
  destruct (lexp_eqb l o); [reflexivity|]; destruct (kd F l o); [|reflexivity].
  rewrite IH; destruct (popin_e F o rem) as [[r|]|]; reflexivity.
Qed.

Lemma popall_e_nonempty O1 rem passed c st c' : popall_e F O1 rem passed c = Some (st, c') -> st <> [].
Proof.
  destruct O1 as [|[y o] O1]; cbn [popall_e]; [intros H; injection H as <- _; discriminate|].
  destruct (popin_e F o rem) as [[r|]|]; [| |discriminate];
    match goal with |- option_map _ ?x = _ -> _ => destruct x as [[s0 c0]|] end; cbn; try discriminate;
    intros H; injection H as <- _; discriminate.
Qed.

Lemma popall_e_spec O1 : forall rem passed c st c', popall_e F O1 rem passed c = Some (st, c') ->
  popall F (map snd O1) (map snd rem) (map snd passed) = Some (map erase st)
  /\ (forall d r p, nth_error st d = Some (r, p) -> incl r rem /\ length passed <= length p /\ length p <= length (snd (last st ([], []))))
  /\ incl (fst (last st ([], []))) rem /\ length passed <= length (snd (last st ([], []))).
Proof.
  induction O1 as [|[y o] O1 IH]; intros rem passed c st c' E; cbn [popall_e] in E.
  - injection E as <- <-; cbn; split; [reflexivity|split; [|split; [apply incl_refl|lia]]].
    intros [|d] r p N; cbn in N; [injection N as <- <-; split; [apply incl_refl|lia]|destruct d; discriminate].
  - cbn [map popall]; cbn [snd]; rewrite popin_e_spec.
    destruct (popin_e F o rem) as [[rem'|]|] eqn:P; cbn [option_map]; [| |discriminate].
    + destruct (popall_e F O1 rem' passed true) as [[st0 c0]|] eqn:E0; cbn in E; [|discriminate]; injection E as <- <-.
      destruct (IH _ _ _ _ _ E0) as [A [B [C D]]].
      assert (Inc : incl rem' rem).
      { clear -P; revert rem' P; induction rem as [|x rem IH]; intros rem' P; cbn [popin_e] in P; [discriminate|].
        destruct (lexp_eqb (lab_i x) o); [injection P as <-; intros z Hz; right; exact Hz|].
        destruct (kd F (lab_i x) o); [|discriminate].
        destruct (popin_e F o rem) as [[r'|]|]; try discriminate; injection P as <-.
        intros z [Hz|Hz]; [left; exact Hz|right; apply (IH r' eq_refl), Hz]. }
      rewrite A; split; [reflexivity|].
      assert (Lst : last ((rem, passed) :: st0) ([], []) = last st0 ([], []))
        by (destruct st0; [exfalso; apply (popall_e_nonempty _ _ _ _ _ _ E0); reflexivity|reflexivity]).
      rewrite Lst; split; [|split; [intros z Hz; apply Inc, C, Hz|exact D]].
      intros [|d] r p N; cbn [nth_error] in N.
      * injection N as <- <-; split; [apply incl_refl|lia].
      * destruct (B d r p N) as [B1 [B2 B3]]; split; [intros z Hz; apply Inc, B1, Hz|lia].
    + destruct (popall_e F O1 rem (passed ++ [(y, o)]) c) as [[st0 c0]|] eqn:E0; cbn in E; [|discriminate]; injection E as <- <-.
      destruct (IH _ _ _ _ _ E0) as [A [B [C D]]].
      rewrite map_app in A; cbn in A; rewrite A; split; [reflexivity|].
      assert (Lst : last ((rem, passed) :: st0) ([], []) = last st0 ([], []))
        by (destruct st0; [exfalso; apply (popall_e_nonempty _ _ _ _ _ _ E0); reflexivity|reflexivity]).
      rewrite length_app in B, D; cbn in B, D.
      rewrite Lst; split; [|split; [exact C|lia]].
      intros [|d] r p N; cbn [nth_error] in N.
      * injection N as <- <-; split; [apply incl_refl|lia].
      * destruct (B d r p N) as [B1 [B2 B3]]; split; [exact B1|lia].
Qed.

Lemma rthrough_e_spec rem z i : rthrough_e F rem z i = rthrough F (map snd rem) z i.
Proof.
  revert i; induction rem as [|[j [l t]] rem IH]; intros i; [reflexivity|]; cbn [rthrough_e rthrough map snd].
  destruct (lexp_eqb l z); [destruct i; [reflexivity|apply IH]|]; destruct (kd F l z); [apply IH|reflexivity].
Qed.

Lemma rthrough_in rem z i t : rthrough F rem z i = Some (inl t) -> exists l, In (l, t) rem.
Proof.
  revert i; induction rem as [|[l s] rem IH]; intros i; cbn [rthrough]; [discriminate|].
  destruct (lexp_eqb l z); [destruct i; [intros H; injection H as <-; exists l; left; reflexivity|]|];
    [| destruct (kd F l z); [|discriminate]]; intros H; destruct (IH _ H) as [l' Hl]; exists l'; right; exact Hl.
Qed.

Lemma last_map {X Y} (g : X -> Y) l d : last (map g l) (g d) = g (last l d).
Proof. induction l as [|a l IH]; [reflexivity|]; destruct l; [reflexivity|]; exact IH. Qed.

Lemma clamp_id n (I : list (lexp * tgt)) : Forall (fun lt => tok n (snd lt)) I ->
  map (fun '(l, t) => (l, clamp n t)) I = I.
Proof.
  induction 1 as [|[l t] I H _ IH]; [reflexivity|]; cbn; rewrite IH; f_equal; f_equal.
  destruct t as [z i d|u p]; cbn in *; [rewrite Nat.min_l by exact H|]; reflexivity.
Qed.

Lemma omap_tag (g : tgt -> option tgt) (I I' : list (positive * (lexp * tgt))) :
  omap (fun '(id, (l, t)) => option_map (fun t' => (id, (l, t'))) (g t)) I = Some I' ->
  omap (fun '(l, t) => option_map (fun t' => (l, t')) (g t)) (map snd I) = Some (map snd I').
Proof.
  revert I'; induction I as [|[i [l t]] I IH]; intros I' E; cbn in *; [injection E as <-; reflexivity|].
  destruct (g t) as [t'|]; cbn in *; [|discriminate].
  destruct (omap _ I) as [I''|]; [|discriminate]; injection E as <-; rewrite (IH I'' eq_refl); reflexivity.
Qed.

Lemma omap_tag_in (g : tgt -> option tgt) (I I' : list (positive * (lexp * tgt))) (y : positive * (lexp * tgt)) :
  omap (fun '(id, (l, t)) => option_map (fun t' => (id, (l, t'))) (g t)) I = Some I' -> In y I' ->
  exists i l t t', In (i, (l, t)) I /\ g t = Some t' /\ y = (i, (l, t')).
Proof.
  revert I'; induction I as [|[i [l t]] I IH]; intros I' E Hy; cbn in *; [injection E as <-; destruct Hy|].
  destruct (g t) as [t'|] eqn:G; cbn in *; [|discriminate].
  destruct (omap _ I) as [I''|] eqn:E2; [|discriminate]; injection E as <-.
  destruct Hy as [<-|Hy]; [exists i, l, t, t'; auto|].
  destruct (IH I'' eq_refl Hy) as [i' [l' [t0 [t1 [H1 H2]]]]]; exists i', l', t0, t1; auto.
Qed.

Lemma last_erase (st : list (list (positive * (lexp * tgt)) * list (positive * lexp))) :
  last (map erase st) ([], []) = erase (last st ([], [])).
Proof. rewrite <- (last_map erase st ([], [])); reflexivity. Qed.

Lemma omap_ext {X Y} (g g' : X -> option Y) l : (forall x, g x = g' x) -> omap g l = omap g' l.
Proof. intros H; induction l as [|a l IH]; cbn; [reflexivity|rewrite H, IH; reflexivity]. Qed.

Lemma newt_e_spec f2 st t : newt_e F f2 st t = newt F (ol f2) (fexp (eff f2)) (map erase st) t.
Proof.
  destruct t as [z i d|u p]; [|reflexivity]; cbn [newt_e newt].
  rewrite nth_error_map; destruct (nth_error st d) as [[r q]|]; cbn [option_map erase fst snd]; [|reflexivity].
  rewrite rthrough_e_spec, length_map; reflexivity.
Qed.

Lemma tok_mono n n' t : n <= n' -> tok n t -> tok n' t.
Proof. destruct t; cbn; lia. Qed.

Theorem ecompose_sound f1 f2 g no ni canc : ok f1 -> ok f2 -> ecompose F f1 f2 = Some (g, no, ni, canc) ->
  (forall z, fd (eff g) z = fd (eff f1) (fd (eff f2) z)) /\ ok g.
Proof.
  intros [O1 W1] [O2 W2]; unfold ecompose.
  destruct (popall_e F (rev (ob f1)) (ei f2) [] false) as [[st c]|] eqn:P; [|discriminate].
  destruct (popall_e_spec _ _ _ _ _ _ P) as [A [B [C D]]]; cbn [map] in A.
  destruct (last st ([], [])) as [rem passed] eqn:L.
  destruct (omap _ (ei f1)) as [I1|] eqn:Om; [|discriminate]; intros H; injection H as <- _ _ _.
  pose proof (omap_tag (fun t => newt_e F f2 st t) _ _ Om) as Om'.
  unfold wfd in W1, W2; rewrite eff_len in W1, W2; cbn [eff fin] in W1, W2.
  assert (Cmp : compose F (eff f1) (eff f2) = Some (mkF (fout (eff f2) ++ map snd passed) (map snd I1 ++ map snd rem))).
  { unfold compose, eff; cbn [fout fin].
    rewrite length_rev, length_map, <- O2, clamp_id by (rewrite O2; exact W2).
    rewrite <- map_rev, A.
    rewrite last_erase, L; cbn [erase fst snd].
    rewrite (omap_ext _ (fun '(l, t) => option_map (fun t' => (l, t')) (newt_e F f2 st t))), Om'; [reflexivity|].
    intros [l t]; rewrite newt_e_spec; reflexivity. }
  split.
  - intros z; rewrite <- (compose_sound F M HM _ _ _ z Cmp); unfold eff; cbn [ob ei fout fin].
    rewrite map_app, map_app, rev_app_distr, map_rev, rev_involutive; reflexivity.
  - split; [cbn [ol ob]; rewrite length_app, length_rev, O2; lia|].
    unfold wfd; rewrite eff_len; cbn [eff fin ob ei].
    rewrite length_app, length_rev, map_app; apply Forall_app; split.
    + apply Forall_forall; intros [l t] Hin; apply in_map_iff in Hin as [y [Ey Hy]].
      destruct (omap_tag_in _ _ _ y Om Hy) as [i [l0 [t0 [t1 [Hi [Ht ->]]]]]]; cbn in Ey; injection Ey as <- <-; cbn [snd].
      destruct t0 as [z0 i0 d0|u p0]; cbn [newt_e] in Ht.
      * destruct (nth_error st d0) as [[r q]|] eqn:N; [|discriminate].
        destruct (B _ _ _ N) as [B1 [_ B3]]; cbn [snd] in B3.
        rewrite rthrough_e_spec in Ht.
        destruct (rthrough F (map snd r) z0 i0) as [[t'|i']|] eqn:R; [| |discriminate]; injection Ht as <-.
        -- destruct (rthrough_in _ _ _ _ R) as [l' Hl].
           apply in_map_iff in Hl as [y' [Ey' Hy']]; apply B1 in Hy'.
           rewrite Forall_forall in W2; specialize (W2 (l', t') (proj2 (in_map_iff _ _ _) (ex_intro _ y' (conj Ey' Hy')))).
           apply (tok_mono (length (ob f2))); [lia|exact W2].
        -- cbn; rewrite O2 in *; lia.
      * injection Ht as <-; exact Logic.I.
    + apply Forall_forall; intros [l t] Hin; apply in_map_iff in Hin as [y [Ey Hy]].
      assert (Hy' : In y (ei f2)) by (apply C; exact Hy).
      rewrite Forall_forall in W2; specialize (W2 (l, t) (proj2 (in_map_iff _ _ _) (ex_intro _ y (conj Ey Hy')))).
      apply (tok_mono (length (ob f2))); [lia|exact W2].
Qed.


(** *** Form-level steps: meaning and [ok] kept *)

Definition keeps (e e' : eform) : Prop := ok e' /\ forall z, fd (eff e') z = fd (eff e) z.

Lemma keeps_trans a b c : keeps a b -> keeps b c -> keeps a c.
Proof. intros [_ H1] [O2 H2]; split; [exact O2|intros z; rewrite H2, H1; reflexivity]. Qed.

Lemma keeps_refl e : ok e -> keeps e e.
Proof. intros O; split; [exact O|reflexivity]. Qed.

Lemma bub_in_perm x I : Permutation (bub_in F x I) (x :: I).
Proof.
  induction I as [|y I IH]; cbn [bub_in]; [reflexivity|].
  destruct (before F (lab_i y) (lab_i x)); [rewrite IH; apply perm_swap|reflexivity].
Qed.

Lemma place_front_perm n I : Permutation (place_front F n I) I.
Proof.
  revert I; induction n as [|n IH]; intros [|x I]; cbn [place_front]; try reflexivity.
  rewrite bub_in_perm; apply perm_skip, IH.
Qed.

Lemma ins_out_perm x rp : Permutation (ins_out F x rp) (x :: rp).
Proof.
  induction rp as [|y r IH]; cbn [ins_out]; [reflexivity|].
  destruct (before F (lab_i x) (lab_i y)); [rewrite IH; apply perm_swap|reflexivity].
Qed.

Lemma out_pass_perm rp suf : Permutation (out_pass F rp suf) (rev rp ++ suf).
Proof.
  revert rp; induction suf as [|x s IH]; intros rp; cbn [out_pass]; [rewrite app_nil_r; reflexivity|].
  rewrite IH, ins_out_perm; cbn [rev]; rewrite <- app_assoc; reflexivity.
Qed.

Lemma place_suffix_out_perm p I : Permutation (place_suffix_out F p I) I.
Proof. unfold place_suffix_out; rewrite out_pass_perm, rev_involutive, firstn_skipn; reflexivity. Qed.

Lemma reread_front_keeps n e : ok e -> keeps e (reread_front F n e).
Proof.
  intros Ok; assert (H : forall z, Forall2 (irel (fout (eff e)) z) (ei (reread_front F n e)) (ei e))
    by (intros z; apply reread_front_rel, (proj1 Ok)).
  split; [|intros z; apply (inputs_rel e _ z (H z))].
  destruct Ok as [O W]; split; [exact O|]; unfold wfd in *; cbn [eff fout fin] in *.
  clear H; revert W; unfold reread_front; cbn [ei]; generalize (ei e); induction n as [|n IH]; intros [|[i [l t]] I] W; cbn [map_front map];
    try exact W; inversion W as [|a b W1 W2]; subst; constructor; [|apply IH, W2].
  cbn [snd] in *; rewrite nread_e_eq by exact O; apply tok_ntgt, W1.
Qed.

Lemma reread_at_keeps j e : ok e -> keeps e (reread_at F j e).
Proof.
  intros Ok; split; [|intros z; apply (inputs_rel e _ z (reread_at_rel e j z (proj1 Ok)))].
  destruct Ok as [O W]; split; [exact O|]; unfold wfd in *; cbn [eff fout fin] in *.
  revert W; unfold reread_at; cbn [ei]; generalize (ei e); intros L; induction L as [|[i [l t]] I IH]; intros W; cbn [map]; [exact W|].
  inversion W as [|a b W1 W2]; subst; constructor; [|apply IH, W2].
  cbn [snd] in *; destruct (is_dep j t); [rewrite nread_e_eq by exact O; apply tok_ntgt|]; exact W1.
Qed.

Lemma place_front_keeps n e : ok e -> keeps e (mkE (ob e) (ol e) (place_front F n (ei e))).
Proof.
  intros Ok; split; [apply perm_ok; [exact Ok|apply place_front_perm]|].
  intros z; apply perm_inputs; intros b; apply place_front_sound.
Qed.

Lemma place_suffix_keeps p e : ok e -> keeps e (mkE (ob e) (ol e) (place_suffix_out F p (ei e))).
Proof.
  intros Ok; split; [apply perm_ok; [exact Ok|apply place_suffix_out_perm]|].
  intros z; apply perm_inputs; intros b; apply place_suffix_out_sound.
Qed.

Lemma place_out_bottom_keeps r e : ok e -> keeps e (place_out_bottom F r e).
Proof. intros Ok; destruct (place_out_bottom_sound r e Ok) as [H O]; split; assumption. Qed.

Lemma place_out_top_keeps r e : ok e -> keeps e (place_out_top F r e).
Proof. intros Ok; destruct (place_out_top_sound r e Ok) as [H O]; split; assumption. Qed.


(** *** Absorbing, composing, moving *)

Lemma iabsorb_e_keeps p e e' : ok e -> iabsorb_e F p e = Some e' -> keeps e e'.
Proof.
  intros Ok; unfold iabsorb_e; destruct (absorb2 F p (eff e)) as [[j g]|] eqn:A; [|discriminate].
  intros H; injection H as <-.
  set (e0 := of_i (mkI g (remove_at j (rev (map fst (ob e)))) (remove_at p (map fst (ei e))))).
  assert (K0 : keeps e e0).
  { split; [apply of_i_ok|intros z; unfold e0; rewrite of_i_sound; cbn [ff]; apply (absorb2_sound F M HM p _ j g z A)]. }
  assert (K1 := keeps_trans _ _ _ K0 (reread_at_keeps j e0 (proj1 K0))).
  assert (K2 := keeps_trans _ _ _ K1 (place_out_bottom_keeps (ol (reread_at F j e0) - j) _ (proj1 K1))).
  exact (keeps_trans _ _ _ K2 (place_suffix_keeps p _ (proj1 K2))).
Qed.

Lemma absorb_scan_e_keeps new e p I e' : ok e -> absorb_scan_e F new e p I = Some e' -> keeps e e'.
Proof.
  intros Ok; revert p; induction I as [|x I IH]; intros p; cbn [absorb_scan_e]; [discriminate|].
  destruct (mem (fst x) new && restore_like x); [|apply IH].
  destruct (iabsorb_e F p e) as [g|] eqn:A; [intros H; injection H as <-; apply (iabsorb_e_keeps p), A; exact Ok|apply IH].
Qed.

Lemma absorb_new_e_keeps fuel new e : ok e -> keeps e (absorb_new_e F fuel new e).
Proof.
  revert e; induction fuel as [|fuel IH]; intros e Ok; cbn [absorb_new_e]; [apply keeps_refl, Ok|].
  destruct (absorb_scan_e F new e 0 (ei e)) as [g|] eqn:A; [|apply keeps_refl, Ok].
  pose proof (absorb_scan_e_keeps _ _ _ _ _ Ok A) as K; exact (keeps_trans _ _ _ K (IH g (proj1 K))).
Qed.

Theorem icompose_e_sound f1 f2 g no ni canc : ok f1 -> ok f2 -> icompose_e F f1 f2 = Some (g, no, ni, canc) ->
  ok g /\ forall z, fd (eff g) z = fd (eff f1) (fd (eff f2) z).
Proof.
  intros O1 O2; unfold icompose_e.
  destruct (ecompose F f1 f2) as [[[[g0 passed] newin] c]|] eqn:E; [|discriminate]; intros H; injection H as <- _ _ _.
  destruct (ecompose_sound _ _ _ _ _ _ O1 O2 E) as [S0 Ok0].
  assert (K1 := reread_front_keeps (length (ei f1)) g0 Ok0).
  assert (K2 := keeps_trans _ _ _ K1 (place_front_keeps (length (ei f1)) _ (proj1 K1))).
  set (g2 := mkE (ob (reread_front F (length (ei f1)) g0)) (ol (reread_front F (length (ei f1)) g0))
                 (place_front F (length (ei f1)) (ei (reread_front F (length (ei f1)) g0)))) in K2.
  assert (K3 : keeps g0 (if c then mkE (ob g2) (ol g2) (place_suffix_out F (length (ei f1)) (ei g2)) else g2))
    by (destruct c; [exact (keeps_trans _ _ _ K2 (place_suffix_keeps _ _ (proj1 K2)))|exact K2]).
  assert (K4 := keeps_trans _ _ _ K3 (place_out_bottom_keeps (length passed) _ (proj1 K3))).
  assert (K5 : keeps g0 (match newin with [] => place_out_bottom F (length passed) (if c then mkE (ob g2) (ol g2) (place_suffix_out F (length (ei f1)) (ei g2)) else g2)
                                     | _ => absorb_new_e F (S (length newin)) newin (place_out_bottom F (length passed) (if c then mkE (ob g2) (ol g2) (place_suffix_out F (length (ei f1)) (ei g2)) else g2)) end))
    by (destruct newin; [exact K4|exact (keeps_trans _ _ _ K4 (absorb_new_e_keeps _ _ _ (proj1 K4)))]).
  destruct K5 as [O5 H5]; split; [exact O5|intros z; rewrite H5; apply S0].
Qed.

Lemma ok_single_out (x : positive) o : ok (mkE [(x, o)] 1 []).
Proof. split; [reflexivity|constructor]. Qed.

Lemma in_first_tok p f h t f' : in_first F p f = Some (h, t, f') -> tok 0 t.
Proof.
  unfold in_first; destruct (nth_error (fin f) p) as [[h0 t0]|]; [|discriminate].
  destruct (_ && _); [|discriminate].
  destruct t0 as [z i d|u q].
  - destruct (pull F (fout f) d z i); cbn; [|discriminate].
    destruct (omap _ _); [|discriminate]; intros H; injection H as _ <- _; cbn; lia.
  - destruct (omap _ _); [|discriminate]; intros H; injection H as _ <- _; exact Logic.I.
Qed.

Theorem imove_e_sound f1 f2 y f1' g new canc lost : ok f1 -> ok f2 -> imove_e F f1 f2 y = Some (f1', g, new, canc, lost) ->
  ok f1' /\ ok g /\ forall z, fd (eff f1') (fd (eff g) z) = fd (eff f1) (fd (eff f2) z).
Proof.
  intros O1 O2; unfold imove_e.
  destruct (index_of y (oids_e f1)) as [j|].
  - destruct (out_first F j (eff f1)) as [[o f1o]|] eqn:Of; [|discriminate].
    destruct (icompose_e F (mkE [(y, o)] 1 []) f2) as [[[[g' no] ni] c]|] eqn:C; [|discriminate].
    intros H; injection H as <- <- _ _ _.
    destruct (icompose_e_sound _ _ _ _ _ _ (ok_single_out y o) O2 C) as [Og Hg].
    set (e0 := of_i (mkI f1o (remove_at j (oids_e f1)) (iids_e f1))).
    assert (K0 : ok e0 /\ forall z, fd (eff e0) z = fd f1o z) by (split; [apply of_i_ok|intros z; apply of_i_sound]).
    assert (K1 := reread_at_keeps j e0 (proj1 K0)).
    assert (K2 := keeps_trans _ _ _ K1 (place_out_bottom_keeps (ol (reread_at F j e0) - j) _ (proj1 K1))).
    destruct K2 as [O3 H3]; split; [exact O3|split; [exact Og|]].
    intros z; rewrite H3, (proj2 K0), Hg, (out_first_sound F M HM j _ _ _ _ Of); reflexivity.
  - destruct (index_of y (iids_e f1)) as [p|]; [|discriminate].
    destruct (in_first F p (eff f1)) as [[[h t] f1o]|] eqn:If; [|discriminate].
    destruct (icompose_e F (mkE [] 0 [(y, (h, t))]) f2) as [[[[g' no] ni] c]|] eqn:C; [|discriminate].
    intros H; injection H as <- <- _ _ _.
    assert (Os : ok (mkE [] 0 [(y, (h, t))])) by (split; [reflexivity|constructor; [exact (in_first_tok _ _ _ _ _ If)|constructor]]).
    destruct (icompose_e_sound _ _ _ _ _ _ Os O2 C) as [Og Hg].
    set (e0 := of_i (mkI f1o (oids_e f1) (remove_at p (iids_e f1)))).
    assert (K0 : ok e0 /\ forall z, fd (eff e0) z = fd f1o z) by (split; [apply of_i_ok|intros z; apply of_i_sound]).
    assert (K1 := place_suffix_keeps p e0 (proj1 K0)).
    destruct K1 as [O3 H3]; split; [exact O3|split; [exact Og|]].
    intros z; rewrite H3, (proj2 K0), Hg, (in_first_sound F M HM p _ _ _ _ _ If); reflexivity.
Qed.


(** *** Lifts *)

Lemma map_snd_combine {X Y} (a : list X) (b : list Y) : length a = length b -> map snd (combine a b) = b.
Proof. revert b; induction a as [|x a IH]; intros [|y b] H; cbn in *; try discriminate; [reflexivity|rewrite IH; [reflexivity|lia]]. Qed.

Lemma length_pseq c n : length (pseq c n) = n.
Proof. revert c; induction n as [|n IH]; intros c; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma length_mapi {X Y} k (g : nat -> X -> Y) l : length (mapi_from k g l) = length l.
Proof. revert k; induction l as [|a l IH]; intros k; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma lift_e_eff L f c : eff (lift_e L f c) = lift_n L (eff f).
Proof.
  unfold lift_e, lift_n, eff; cbn [ob ei fout fin].
  rewrite map_app, rev_app_distr, map_rev, rev_involutive, map_snd_combine by (rewrite length_pseq; reflexivity).
  rewrite map_app, map_snd_combine by (rewrite length_pseq, length_mapi; reflexivity).
  f_equal; f_equal; rewrite !map_map; apply map_ext; intros [i [g t]]; reflexivity.
Qed.

Lemma restores_tok n k (L : list lexp) : k + length L <= n ->
  Forall (fun lt => tok n (snd lt)) (mapi_from k (fun k h => (h, TR h 0 k)) L).
Proof. revert k; induction L as [|h L IH]; intros k H; cbn in *; constructor; [cbn; lia|apply IH; lia]. Qed.

Lemma lift_e_ok L f c : ok f -> ok (lift_e L f c).
Proof.
  intros [O W]; split.
  - unfold lift_e; cbn [ol ob]; rewrite length_app, length_rev, length_combine, length_pseq, O; lia.
  - unfold wfd in *; rewrite lift_e_eff; unfold lift_n; cbn [fout fin] in *; rewrite length_app.
    apply Forall_app; split; [apply restores_tok; lia|].
    rewrite Forall_forall in *; intros [g t] Hin; apply in_map_iff in Hin as [[g0 t0] [E Hin]]; injection E as <- <-.
    specialize (W _ Hin); destruct t0; cbn in *; [lia|exact Logic.I].
Qed.

Lemma absorb_walk_keeps fuel p rf inside e k : ok e -> keeps e (fst (absorb_walk F fuel p rf inside e k)).
Proof.
  revert p rf inside e k; induction fuel as [|fuel IH]; intros p rf inside e k Ok; cbn [absorb_walk]; [apply keeps_refl, Ok|].
  destruct rf as [|x rf]; [apply keeps_refl, Ok|].
  destruct (if pre_x F x inside e then iabsorb_e F p e else None) as [e'|] eqn:A.
  - assert (K : keeps e e') by (destruct (pre_x F x inside e); [apply (iabsorb_e_keeps p e e' Ok A)|discriminate]).
    exact (keeps_trans _ _ _ K (IH _ _ _ _ _ (proj1 K))).
  - apply IH, Ok.
Qed.

Lemma lift_many_e_sound L f c : ok f ->
  match fst (lift_many_e F L (KF f) c) with
  | KF g => ok g /\ forall z, fd (eff g) z = liftsem M L (fd (eff f)) z
  | KA _ _ => False
  end.
Proof.
  intros Ok; unfold lift_many_e.
  destruct (absorb_walk F _ _ _ _ (lift_e L f c) 0) as [f1 k] eqn:W.
  assert (K0 : keeps (lift_e L f c) f1).
  { pose proof (absorb_walk_keeps (length L) (pred (length L)) (rev (firstn (length L) (ei (lift_e L f c))))
                  (skipn (length L) (ei (lift_e L f c))) (lift_e L f c) 0 (lift_e_ok L f c Ok)) as K; rewrite W in K; exact K. }
  assert (K1 := keeps_trans _ _ _ K0 (place_front_keeps k f1 (proj1 K0))).
  assert (K2 := keeps_trans _ _ _ K1 (place_out_top_keeps (Nat.min k (ol (mkE (ob f1) (ol f1) (place_front F k (ei f1))))) _ (proj1 K1))).
  cbn [fst]; destruct K2 as [O2 H2]; split; [exact O2|intros z; rewrite H2, lift_e_eff, lift_n_eq; apply lift_fold_sound].
Qed.


(** *** The word *)

Definition okit (it : eitem) : Prop := match it with KF f => ok f | KA _ _ => True end.

Local Notation wde := (fun st x => wden M (map estrip st) x).

Lemma try_ids_e_sound f1 f2 xs cands f1' g new canc lost : ok f1 -> ok f2 ->
  try_ids_e F f1 f2 xs cands = Some (f1', g, new, canc, lost) ->
  ok f1' /\ ok g /\ forall z, fd (eff f1') (fd (eff g) z) = fd (eff f1) (fd (eff f2) z).
Proof.
  intros O1 O2; induction xs as [|y xs IH]; cbn [try_ids_e]; [discriminate|].
  destruct (mem y cands); [|apply IH].
  destruct (imove_e F f1 f2 y) as [[[[[a b] c] d] e]|] eqn:E; [|apply IH].
  intros H; injection H as -> -> -> -> ->; apply (imove_e_sound _ _ _ _ _ _ _ _ O1 O2 E).
Qed.

Lemma moves_e_sound fuel k f1 f2 c acc f1' g acc' : ok f1 -> ok f2 -> moves_e F fuel k f1 f2 c acc = (f1', g, acc') ->
  ok f1' /\ ok g /\ forall z, fd (eff f1') (fd (eff g) z) = fd (eff f1) (fd (eff f2) z).
Proof.
  revert f1 f2 c acc; induction fuel as [|fuel IH]; intros f1 f2 c acc O1 O2; cbn [moves_e].
  - intros H; injection H as <- <- _; auto.
  - destruct (try_ids_e F f1 f2 (ids_of_e f1) c) as [[[[[a b] new] canc] lost]|] eqn:T.
    + destruct (try_ids_e_sound _ _ _ _ _ _ _ _ _ O1 O2 T) as [Oa [Ob H1]].
      intros H; destruct (IH _ _ _ _ Oa Ob H) as [O3 [O4 H2]]; split; [exact O3|split; [exact O4|intros z; rewrite H2, H1; reflexivity]].
    + intros H; injection H as <- <- _; auto.
Qed.

Lemma Forall_firstn' {X} (P : X -> Prop) n l : Forall P l -> Forall P (firstn n l).
Proof. revert l; induction n; intros [|a l] H; cbn; auto; inversion H; subst; constructor; auto. Qed.

Lemma Forall_skipn' {X} (P : X -> Prop) n l : Forall P l -> Forall P (skipn n l).
Proof. revert l; induction n; intros [|a l] H; cbn; auto; inversion H; subst; auto. Qed.

Lemma Forall_put2e k st mid : Forall okit st -> Forall okit mid -> Forall okit (put2e k st mid).
Proof.
  intros H1 H2; unfold put2e; apply Forall_app; split; [apply Forall_firstn', H1|].
  apply Forall_app; split; [exact H2|apply Forall_skipn', H1].
Qed.

Lemma wde_app st1 st2 x : wde (st1 ++ st2) x = wde st1 (wde st2 x).
Proof. cbn; rewrite map_app; apply wden_app. Qed.

Lemma step_e_put k st a b mid x : nth_error st k = Some a -> nth_error st (S k) = Some b ->
  (forall y, wde mid y = iden M (estrip a) (iden M (estrip b) y)) -> wde (put2e k st mid) x = wde st x.
Proof.
  intros Ha Hb H; unfold put2e; pose proof (split2 st k a b Ha Hb) as E.
  set (A := firstn k st) in *; set (R := skipn (S (S k)) st) in *.
  rewrite E; rewrite !wde_app, H; reflexivity.
Qed.

Lemma iempty_e_den g : iempty_e g = true -> forall y, fd (eff g) y = y.
Proof. destruct g as [[|o go] gl [|i gi]]; cbn; try discriminate; reflexivity. Qed.

Lemma step_e_sound s : Forall okit (fst s) -> Forall okit (fst (step_e F s)) /\ forall x, wde (fst (step_e F s)) x = wde (fst s) x.
Proof.
  destruct s as [st w]; unfold step_e; cbn [fst]; intros Hst.
  destruct w as [|[k cands] w']; [auto|].
  destruct (nth_error st k) as [[f1|L1 n1]|] eqn:Ea; try (split; [exact Hst|reflexivity]).
  destruct (nth_error st (S k)) as [[f2|L2 n2]|] eqn:Eb; try (split; [exact Hst|reflexivity]).
  assert (O1 : ok f1) by (rewrite Forall_forall in Hst; apply (Hst (KF f1)), (nth_error_In _ _ Ea)).
  assert (O2 : ok f2) by (rewrite Forall_forall in Hst; apply (Hst (KF f2)), (nth_error_In _ _ Eb)).
  destruct (match cands with None => icompose_e F f1 f2 | Some _ => None end) as [[[[g no] ni] cc]|] eqn:Mg.
  - assert (G : ok g /\ forall y, fd (eff g) y = fd (eff f1) (fd (eff f2) y))
      by (destruct cands; [discriminate|apply (icompose_e_sound _ _ _ _ _ _ O1 O2 Mg)]).
    destruct G as [Og G].
    destruct (iempty_e g) eqn:Em; cbn [fst].
    + split; [apply Forall_put2e; [exact Hst|constructor]|].
      intros x; apply (step_e_put k st (KF f1) (KF f2)); auto; intros y; cbn [map estrip wden iden]; rewrite <- G, (iempty_e_den g Em); reflexivity.
    + split; [apply Forall_put2e; [exact Hst|constructor; [exact Og|constructor]]|].
      intros x; apply (step_e_put k st (KF f1) (KF f2)); auto; intros y; cbn [map estrip wden iden]; apply G.
  - destruct (moves_e F _ k f1 f2 _ []) as [[f1' g] acc] eqn:Mv.
    destruct (moves_e_sound _ _ _ _ _ _ _ _ _ O1 O2 Mv) as [Oa [Ob G]].
    destruct (iempty_e f1') eqn:Em; cbn [fst].
    + split; [apply Forall_put2e; [exact Hst|repeat first [apply Forall_nil|apply Forall_cons; [assumption|]]]|].
      intros x; apply (step_e_put k st (KF f1) (KF f2)); auto; intros y; cbn [map estrip wden iden]; rewrite <- G, (iempty_e_den f1' Em); reflexivity.
    + split; [apply Forall_put2e; [exact Hst|repeat first [apply Forall_nil|apply Forall_cons; [assumption|]]]|].
      intros x; apply (step_e_put k st (KF f1) (KF f2)); auto; intros y; cbn [map estrip wden iden]; apply G.
Qed.

Lemma settle_e_sound p s : Forall okit (fst s) -> Forall okit (fst (settle_e F p s)) /\ forall x, wde (fst (settle_e F p s)) x = wde (fst s) x.
Proof.
  revert s; induction p as [p IH|p IH|]; intros s Hs; cbn [settle_e]; destruct (snd s); try (split; [exact Hs|reflexivity]).
  - destruct (IH s Hs) as [A1 B1]; destruct (IH _ A1) as [A2 B2]; destruct (step_e_sound _ A2) as [A3 B3].
    split; [exact A3|intros x; rewrite B3, B2, B1; reflexivity].
  - destruct (IH s Hs) as [A1 B1]; destruct (IH _ A1) as [A2 B2]; split; [exact A2|intros x; rewrite B2, B1; reflexivity].
  - apply step_e_sound, Hs.
Qed.

Lemma insert_e_sound it st : okit it -> Forall okit st ->
  Forall okit (insert_e F it st) /\ forall x, wde (insert_e F it st) x = iden M (estrip it) (wde st x).
Proof.
  intros Hi Hs; destruct it as [f|L n]; cbn [insert_e]; [|split; [constructor; [exact Hi|exact Hs]|reflexivity]].
  destruct (iempty_e f) eqn:E.
  - split; [exact Hs|intros x; cbn [map estrip iden]; symmetry; apply (iempty_e_den f E)].
  - destruct (settle_e_sound big (KF f :: st, [(0, None)])) as [A B]; [constructor; assumption|].
    split; [exact A|intros x; rewrite B; reflexivity].
Qed.

Lemma lift_many_e_sound' L it c : okit it -> okit (fst (lift_many_e F L it c)) /\
  forall x, iden M (estrip (fst (lift_many_e F L it c))) x = liftsem M L (iden M (estrip it)) x.
Proof.
  destruct it as [f|L' n]; intros Hi.
  - pose proof (lift_many_e_sound L f c Hi) as H; destruct (fst (lift_many_e F L (KF f) c)) as [g|]; [|contradiction].
    destruct H as [Og Hg]; split; [exact Og|exact Hg].
  - split; [exact Logic.I|intros x; cbn; apply lden_app].
Qed.

Lemma insert_lifted_e_sound L w st c : Forall okit w -> Forall okit st ->
  Forall okit (fst (insert_lifted_e F L w st c)) /\ forall x, wde (fst (insert_lifted_e F L w st c)) x = liftsem M L (wde w) (wde st x).
Proof.
  revert c; induction w as [|it w IH]; intros c Hw Hs; cbn [insert_lifted_e].
  - split; [exact Hs|intros x; cbn; symmetry; apply liftsem_id].
  - inversion Hw as [|a b Hit Hw']; subst.
    destruct (insert_lifted_e F L w st c) as [st1 c1] eqn:E1.
    destruct (lift_many_e F L it c1) as [it' c2] eqn:E2; cbn [fst].
    destruct (IH c Hw' Hs) as [A1 B1]; rewrite E1 in A1, B1; cbn [fst] in A1, B1.
    destruct (lift_many_e_sound' L it c1 Hit) as [A2 B2]; rewrite E2 in A2, B2; cbn [fst] in A2, B2.
    destruct (insert_e_sound it' st1 A2 A1) as [A3 B3]; split; [exact A3|].
    intros x; rewrite B3, B1, B2, liftsem_comp; reflexivity.
Qed.

(** *** Expressions *)

Theorem rnorm2_sound : forall e,
  (forall st c, Forall okit st -> Forall okit (fst (rnorm2 F e st c)) /\ forall x, wde (fst (rnorm2 F e st c)) x = ca e (wde st x))
  /\ (forall R st c, Forall okit st -> Forall okit (fst (peel2 F R e st c)) /\ forall x, wde (fst (peel2 F R e st c)) x = liftsem M (rev R) (ca e) (wde st x)).
Proof.
  assert (Peel : forall e, (forall st c, Forall okit st -> Forall okit (fst (rnorm2 F e st c)) /\ forall x, wde (fst (rnorm2 F e st c)) x = ca e (wde st x)) ->
            (forall a, e <> ALift (fst a) (snd a)) ->
            forall R st c, Forall okit st -> Forall okit (fst (peel2 F R e st c)) /\ forall x, wde (fst (peel2 F R e st c)) x = liftsem M (rev R) (ca e) (wde st x)).
  { intros e H1 Hn R st c Hs.
    assert (P : peel2 F R e st c = let '(w, c1) := rnorm2 F e [] c in insert_lifted_e F (rev R) w st c1)
      by (destruct e as [| | | | |h' a']; try reflexivity; exfalso; apply (Hn (h', a')); reflexivity).
    rewrite P; destruct (rnorm2 F e [] c) as [w c1] eqn:E.
    destruct (H1 [] c (Forall_nil _)) as [A B]; rewrite E in A, B; cbn [fst] in A, B.
    destruct (insert_lifted_e_sound (rev R) w st c1 A Hs) as [A2 B2]; split; [exact A2|].
    intros x; rewrite B2; apply liftsem_ext; intros y; apply B. }
  induction e as [|n|a [IHa1 IHa2] b [IHb1 IHb2]|h a [IH1 IH2]|h t a [IH1 IH2]|h a [IH1 IH2]].
  - assert (H1 : forall st c, Forall okit st -> Forall okit (fst (rnorm2 F AId st c)) /\ forall x, wde (fst (rnorm2 F AId st c)) x = ca AId (wde st x))
      by (intros st c Hs; split; [exact Hs|reflexivity]).
    split; [exact H1|apply Peel; [exact H1|intros [? ?]; discriminate]].
  - assert (H1 : forall st c, Forall okit st -> Forall okit (fst (rnorm2 F (AAtom n) st c)) /\ forall x, wde (fst (rnorm2 F (AAtom n) st c)) x = ca (AAtom n) (wde st x)).
    { intros st c Hs; cbn [rnorm2 fst]; destruct (insert_e_sound (KA [] n) st Logic.I Hs) as [A B]; split; [exact A|intros x; rewrite B; reflexivity]. }
    split; [exact H1|apply Peel; [exact H1|intros [? ?]; discriminate]].
  - assert (H1 : forall st c, Forall okit st -> Forall okit (fst (rnorm2 F (ACompose a b) st c)) /\ forall x, wde (fst (rnorm2 F (ACompose a b) st c)) x = ca (ACompose a b) (wde st x)).
    { intros st c Hs; cbn [rnorm2]; destruct (rnorm2 F a st c) as [st1 c1] eqn:E.
      destruct (IHa1 st c Hs) as [A1 B1]; rewrite E in A1, B1; cbn [fst] in A1, B1.
      destruct (IHb1 st1 c1 A1) as [A2 B2]; split; [exact A2|intros x; rewrite B2, B1; reflexivity]. }
    split; [exact H1|apply Peel; [exact H1|intros [? ?]; discriminate]].
  - assert (H1 : forall st c, Forall okit st -> Forall okit (fst (rnorm2 F (AOuter h a) st c)) /\ forall x, wde (fst (rnorm2 F (AOuter h a) st c)) x = ca (AOuter h a) (wde st x)).
    { intros st c Hs; rewrite rnorm2_outer; set (g := fst (fresh (weak h) c)); set (c1 := snd (fresh (weak h) c)).
      destruct (insert_e_sound (KF (of_i g)) st (of_i_ok g) Hs) as [A B].
      destruct (IH1 _ c1 A) as [A2 B2]; split; [exact A2|intros x; rewrite B2, B; cbn [estrip iden]; rewrite of_i_sound].
      reflexivity. }
    split; [exact H1|apply Peel; [exact H1|intros [? ?]; discriminate]].
  - assert (H1 : forall st c, Forall okit st -> Forall okit (fst (rnorm2 F (AInner h t a) st c)) /\ forall x, wde (fst (rnorm2 F (AInner h t a) st c)) x = ca (AInner h t a) (wde st x)).
    { intros st c Hs; rewrite rnorm2_inner; set (g := fst (fresh (entry h t) c)); set (c1 := snd (fresh (entry h t) c)).
      destruct (insert_e_sound (KF (of_i g)) st (of_i_ok g) Hs) as [A B].
      destruct (IH2 [h] _ c1 A) as [A2 B2]; split; [exact A2|intros x; rewrite B2, B; cbn [estrip iden rev app]; rewrite of_i_sound].
      subst g; rewrite fresh_ff; cbn [liftsem]; rewrite entry_sound, cpop_push, chd_push; reflexivity. }
    split; [exact H1|apply Peel; [exact H1|intros [? ?]; discriminate]].
  - split.
    + intros st c Hs; rewrite rnorm2_lift; destruct (IH2 [h] st c Hs) as [A B]; split; [exact A|intros x; rewrite B; reflexivity].
    + intros R st c Hs; cbn [peel2]; destruct (IH2 (h :: R) st c Hs) as [A B]; split; [exact A|].
      intros x; rewrite B; cbn [rev]; rewrite liftsem_app; apply liftsem_ext; reflexivity.
Qed.

Theorem rrun2_sound e x : wden M (rrun2 F e) x = ca e x.
Proof. unfold rrun2; destruct (proj1 (rnorm2_sound e) [] xH (Forall_nil _)) as [_ B]; rewrite B; reflexivity. Qed.

End Sound2.

(** ** The normaliser: the pass, then [CNorm] *)

Definition cr2_form (F : order) (e : aexp) : aexp := wexp (rrun2 F e).

Theorem cr2_form_sound F e : forall M, ccons F M -> forall x : cU M, ca (cr2_form F e) x = ca e x.
Proof. intros M HM x; unfold cr2_form; rewrite wexp_sound, (rrun2_sound F M HM); reflexivity. Qed.

Definition cr2_eq (F : order) (e1 e2 : aexp) : bool := cn_eq F (cr2_form F e1) (cr2_form F e2).

Theorem cr2_eq_correct F
  (Hirr : forall a, lt_known F a a = false)
  (Htrans : forall a b c, lt_known F a b = true -> lt_known F b c = true -> lt_known F a c = true)
  e1 e2 : cr2_eq F e1 e2 = true <-> cequal F e1 e2.
Proof.
  unfold cr2_eq; rewrite (CComplete.cn_eq_correct F Hirr Htrans); split; intros H M HM x.
  - rewrite <- (cr2_form_sound F e1 M HM x), <- (cr2_form_sound F e2 M HM x); apply H, HM.
  - rewrite (cr2_form_sound F e1 M HM x), (cr2_form_sound F e2 M HM x); apply H, HM.
Qed.
