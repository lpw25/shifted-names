(** * The context-form pass

    An expression is read right to left as a word of forms and lifted
    atoms.  Each new item is inserted at the front of the word and the
    word is settled: adjacent forms are composed, and where they cannot
    be, single outputs and inputs move on; only what is new is
    re-examined.  A chain of lifts is applied to a form at once, its
    restores absorbed innermost first.

    Representation:
    - a form ([bform]) keeps its outputs bottom first, with their number,
      so new outputs go on at the bottom in constant time and reads near
      the bottom are reached from the front of the list;
    - outputs and inputs carry their ids in the same lists;
    - depths and name indices of reads ([btgt]), and the number of
      outputs, are binary ([N]); list positions (which output, which
      input, which item) stay [nat], since each is used to walk a list
      that far;
    - an output swap looks up the reads between the two outputs in a map
      from depths to counts, and only scans the inputs when there is one;
    - lists are reversed with [rev'] (linear), and the outputs passed in a
      composition are kept newest first with their count.

    It depends only on the specification [CSpec]: every operation is
    proved sound against the meaning of forms there ([rrunN_sound]), and
    [crN_eq_correct] follows by [CNorm] completeness. *)

From Stdlib Require Import List Bool Arith Lia PArith NArith FMapPositive Permutation.
From ShiftedNames.Core Require Import Label Normalise GEval CNorm Comp CSound CComplete CSpec.
Import ListNotations.

Inductive btgt : Type :=
| BR (z : lexp) (i d : N)
| BT (u : nat) (p : pexp).

Definition ta (t : btgt) : tgt := match t with BR z i d => TR z (N.to_nat i) (N.to_nat d) | BT u p => TT u p end.
Definition tb (t : tgt) : btgt := match t with TR z i d => BR z (N.of_nat i) (N.of_nat d) | TT u p => BT u p end.

(** Forms without ids, outputs top first. *)
Record bfm : Type := mkC { cout : list lexp; cin : list (lexp * btgt) }.

Definition ina (x : lexp * btgt) : lexp * tgt := (fst x, ta (snd x)).
Definition fa (f : bfm) : form := mkF (cout f) (map ina (cin f)).
Definition fb (f : form) : bfm := mkC (fout f) (map (fun x => (fst x, tb (snd x))) (fin f)).

(** Forms with ids, outputs bottom first, and their number. *)
Record bform : Type := mkB {
  bo : list (positive * lexp);
  bl : N;
  bi : list (positive * (lexp * btgt))
}.

Inductive bitem : Type :=
| BF (f : bform)
| BA (L : list lexp) (n : nat).

Definition isnd (x : positive * (lexp * btgt)) : lexp * tgt := ina (snd x).

(** The form a [bform] stands for. *)
Definition beff (e : bform) : form := mkF (rev (map snd (bo e))) (map isnd (bi e)).
Definition bstrip (it : bitem) : item := match it with BF f => IF (beff f) | BA L n => IA L n end.

Definition b_to_c (e : bform) : bfm := mkC (rev' (map snd (bo e))) (map snd (bi e)).

Definition bclamp (n : N) (t : btgt) : btgt :=
  match t with BR z i d => BR z i (N.min d n) | BT _ _ => t end.

Definition bof_i (g : bfm) (oids iids : list positive) : bform :=
  let n := N.of_nat (length (cout g)) in
  mkB (rev' (zipd oids (cout g))) n (zipd iids (map (fun x => (fst x, bclamp n (snd x))) (cin g))).

Definition bis_dep (j : N) (t : btgt) : bool := match t with BR _ _ d => N.eqb d j | BT _ _ => false end.

Fixpoint mapi_fromN {X Y} (k : N) (g : N -> X -> Y) (l : list X) : list Y :=
  match l with [] => [] | a :: l' => g k a :: mapi_fromN (N.succ k) g l' end.

(** Steps on the work list: item [k] and [k+1] to examine, all ids
    ([None]) or the ids that are new. *)
Definition bwork : Type := list (nat * option (list positive)).

Definition bbig : positive := 1099511627776%positive.

(** A new form, with fresh ids from [c]. *)
Definition bfresh (f : form) (c : positive) : bform * positive :=
  let a := length (fout f) in let b := length (fin f) in
  (bof_i (fb f) (pseq c a) (pseq (padd c a) b), padd c (a + b)).

Section RunN.

Variable F : order.

(** The output a read of [l₀] at depth [j] reaches through outputs on
    labels ordered against [l]; [R] is the outputs from depth [j] on. *)
Fixpoint bslot_go (l : lexp) (R : list lexp) (j : nat) : option nat :=
  match R with
  | [] => None
  | o :: R' => if lexp_eqb o l then Some j else if kd F l o then bslot_go l R' (S j) else None
  end.

Fixpoint ballkd (l : lexp) (L : list lexp) : bool :=
  match L with [] => true | o :: L' => if kd F l o then ballkd l L' else false end.

(** ** Steps on forms without ids *)

Definition bswap_read (k : N) (b : lexp) (t : btgt) : option btgt :=
  match t with
  | BR z i d =>
      if N.eqb d (N.succ k) then
        if lexp_eqb z b then match i with N0 => None | _ => Some (BR z (N.pred i) (N.succ (N.succ k))) end
        else if kd F z b then Some (BR z i (N.succ (N.succ k))) else None
      else Some t
  | BT _ _ => Some t
  end.

Definition bdrop_read (j : N) (l : lexp) (t : btgt) : option btgt :=
  match t with
  | BR z i d =>
      if N.leb d j then Some t
      else if lexp_eqb z l then Some (BR z (N.succ i) (N.pred d))
      else if kd F z l then Some (BR z i (N.pred d)) else None
  | BT _ _ => Some t
  end.

Definition babsorb_at (j p : nat) (f : bfm) : option bfm :=
  let jN := N.of_nat j in
  match nth_error (cout f) j, nth_error (cin f) p with
  | Some l, Some (l', BR z i d) =>
      if lexp_eqb l l' && lexp_eqb z l && N.eqb i 0 && N.eqb d jN
         && forallb (kd F l) (skipn (S j) (cout f))
         && forallb (fun '(m, _) => kd F l m) (skipn (S p) (cin f)) then
        match omap (fun '(m, t) => option_map (fun t' => (m, t')) (bdrop_read jN l t)) (remove_at p (cin f)) with
        | Some Is => Some (mkC (remove_at j (cout f)) Is)
        | None => None
        end
      else None
  | _, _ => None
  end.

(** The input at position [p] given the target [t]: a walk to [p], with
    no comparison of positions. *)
Fixpoint set_tgt (p : nat) (t : btgt) (I : list (lexp * btgt)) : list (lexp * btgt) :=
  match p, I with
  | 0, (l, _) :: I' => (l, t) :: I'
  | S p', x :: I' => x :: set_tgt p' t I'
  | _, [] => []
  end.

Definition bset_in (p : nat) (t : btgt) (f : bfm) : bfm := mkC (cout f) (set_tgt p t (cin f)).

Fixpoint ballkd_in (l : lexp) (I : list (lexp * btgt)) : bool :=
  match I with [] => true | (m, _) :: I' => if kd F l m then ballkd_in l I' else false end.

Definition babsorb2 (p : nat) (f : bfm) : option (nat * bfm) :=
  match nth_error (cin f) p with
  | Some (l, BR z i d) =>
      if lexp_eqb z l then if N.eqb i 0 then
        match bslot_go l (skipn (N.to_nat d) (cout f)) (N.to_nat d) with
        | Some j =>
            if ballkd l (skipn (S j) (cout f)) then if ballkd_in l (skipn (S p) (cin f)) then
              option_map (fun g => (j, g)) (babsorb_at j p (bset_in p (BR l 0 (N.of_nat j)) f))
            else None else None
        | None => None
        end
      else None else None
  | _ => None
  end.

Definition btop_read (j : N) (o : lexp) (t : btgt) : option btgt :=
  match t with
  | BR z i d =>
      if N.ltb j d then Some (BR z i (N.pred d))
      else if lexp_eqb z o then match i with N0 => None | _ => Some (BR z (N.pred i) d) end
      else if kd F z o then Some t else None
  | BT _ _ => None
  end.

Definition bout_first (j : nat) (f : bfm) : option (lexp * bfm) :=
  match nth_error (cout f) j with
  | Some o =>
      if forallb (kd F o) (firstn j (cout f)) then
        let jN := N.of_nat j in
        match omap (fun '(m, t) => option_map (fun t' => (m, t')) (btop_read jN o t)) (cin f) with
        | Some Is => Some (o, mkC (remove_at j (cout f)) Is)
        | None => None
        end
      else None
  | None => None
  end.

Fixpoint bpull (O : list lexp) (d : nat) (z : lexp) (i : N) : option N :=
  match O, d with
  | o :: O', S d' =>
      match bpull O' d' z i with
      | Some j => if lexp_eqb o z then Some (N.succ j) else if kd F z o then Some j else None
      | None => None
      end
  | _, _ => Some i
  end.

Definition bunder_read (h : lexp) (t : btgt) : option btgt :=
  match t with
  | BR z i d => if lexp_eqb z h then Some (BR z (N.succ i) d) else if kd F z h then Some t else None
  | BT u p => Some (BT u (PShift h p))
  end.

Definition bin_first (p : nat) (f : bfm) : option (lexp * btgt * bfm) :=
  match nth_error (cin f) p with
  | Some (h, t) =>
      if forallb (fun '(m, _) => kd F h m) (skipn (S p) (cin f)) && forallb (kd F h) (cout f) then
        let t0 := match t with BR z i d => option_map (fun i' => BR z i' 0) (bpull (cout f) (N.to_nat d) z i) | BT _ _ => Some t end in
        match t0, omap (fun '(m, s) => option_map (fun s' => (m, s')) (bunder_read h s)) (remove_at p (cin f)) with
        | Some t', Some Is => Some (h, t', mkC (cout f) Is)
        | _, _ => None
        end
      else None
  | None => None
  end.

(** ** Steps on forms with ids *)

Definition blab (x : positive * (lexp * btgt)) : lexp := fst (snd x).

Fixpoint nread_up_b (up : list (positive * lexp)) (z : lexp) (i d : N) : btgt :=
  match d with
  | N0 => BR z i 0
  | _ =>
      match up with
      | (_, o) :: up' =>
          if lexp_eqb o z then nread_up_b up' z (N.succ i) (N.pred d) else if kd F z o then nread_up_b up' z i (N.pred d) else BR z i d
      | [] => BR z i d
      end
  end.

Definition nread_e_b (e : bform) (t : btgt) : btgt :=
  match t with
  | BR z i d => if N.leb d (bl e) then nread_up_b (skipn (N.to_nat (bl e - d)) (bo e)) z i d else t
  | BT _ _ => t
  end.

Definition reread_front_b (n : nat) (e : bform) : bform :=
  mkB (bo e) (bl e) (map_front n (fun '(id, (l, t)) => (id, (l, nread_e_b e t))) (bi e)).

Definition reread_at_b (j : nat) (e : bform) : bform :=
  let jN := N.of_nat j in
  mkB (bo e) (bl e) (map (fun '(id, (l, t)) => (id, (l, if bis_dep jN t then nread_e_b e t else t))) (bi e)).

Fixpoint bub_in_b (x : positive * (lexp * btgt)) (I : list (positive * (lexp * btgt))) : list (positive * (lexp * btgt)) :=
  match I with
  | [] => [x]
  | y :: r => if before F (blab y) (blab x) then y :: bub_in_b x r else x :: I
  end.

Fixpoint place_front_b (n : nat) (I : list (positive * (lexp * btgt))) : list (positive * (lexp * btgt)) :=
  match n, I with S n', x :: I' => bub_in_b x (place_front_b n' I') | _, _ => I end.

Fixpoint ins_out_b (x : positive * (lexp * btgt)) (rp : list (positive * (lexp * btgt))) : list (positive * (lexp * btgt)) :=
  match rp with
  | [] => [x]
  | y :: r => if before F (blab x) (blab y) then y :: ins_out_b x r else x :: rp
  end.

Fixpoint out_pass_b (rp suf : list (positive * (lexp * btgt))) : list (positive * (lexp * btgt)) :=
  match suf with [] => rev' rp | x :: s => out_pass_b (ins_out_b x rp) s end.

Definition place_suffix_out_b (p : nat) (I : list (positive * (lexp * btgt))) : list (positive * (lexp * btgt)) :=
  out_pass_b (rev' (firstn p I)) (skipn p I).

Definition dkey_b (d : N) : positive := N.succ_pos d.

(** Inputs as maps, for output swaps: the inputs by key [1 … n], in
    order, and for each depth the keys of the reads there.  A key may stay
    in the list of a depth its read has left; a swap leaves such a read
    alone. *)
Record imap : Type := mkIM {
  imm : PositiveMap.t (positive * (lexp * btgt));
  imx : PositiveMap.t (list positive);
  imn : nat
}.

(** The inputs during an output placement: still the list, or the maps
    once a swap needed them. *)
Inductive istate : Type :=
| IL (I : list (positive * (lexp * btgt)))
| IM (r : imap).

Definition dummy_in : positive * (lexp * btgt) := (xH, (LNone, BT 0 PId)).

Definition im_get (m : PositiveMap.t (positive * (lexp * btgt))) (q : positive) : positive * (lexp * btgt) :=
  match PositiveMap.find q m with Some x => x | None => dummy_in end.

Definition im_list (r : imap) : list (positive * (lexp * btgt)) := map (im_get (imm r)) (pseq 1 (imn r)).

Definition ins (s : istate) : list (positive * (lexp * btgt)) := match s with IL l => l | IM r => im_list r end.

Definition ix_get (ix : PositiveMap.t (list positive)) (d : N) : list positive :=
  match PositiveMap.find (dkey_b d) ix with Some l => l | None => [] end.

Fixpoint im_build (I : list (positive * (lexp * btgt))) (c : positive) (m : PositiveMap.t (positive * (lexp * btgt)))
    (ix : PositiveMap.t (list positive)) : PositiveMap.t (positive * (lexp * btgt)) * PositiveMap.t (list positive) :=
  match I with
  | [] => (m, ix)
  | x :: I' =>
      let ix' := match snd (snd x) with BR _ _ d => PositiveMap.add (dkey_b d) (c :: ix_get ix d) ix | BT _ _ => ix end in
      im_build I' (Pos.succ c) (PositiveMap.add c x m) ix'
  end.

Definition to_im (s : istate) : imap :=
  match s with
  | IM r => r
  | IL l => let '(m, ix) := im_build l 1 (PositiveMap.empty _) (PositiveMap.empty _) in mkIM m ix (length l)
  end.

(** What a swap of outputs [k] and [k+1] does to the reads, on the list
    (the specification of [sswap]). *)
Definition swap_in_b (k : N) (b : lexp) (I : list (positive * (lexp * btgt))) : option (list (positive * (lexp * btgt))) :=
  omap (fun '(id, (l, t)) => option_map (fun t' => (id, (l, t'))) (bswap_read k b t)) I.

Fixpoint upd_keys (k : N) (b : lexp) (ks : list positive) (m : PositiveMap.t (positive * (lexp * btgt))) :
    option (PositiveMap.t (positive * (lexp * btgt))) :=
  match ks with
  | [] => Some m
  | q :: ks' =>
      match PositiveMap.find q m with
      | Some (id, (l, t)) =>
          match bswap_read k b t with
          | Some t' => upd_keys k b ks' (PositiveMap.add q (id, (l, t')) m)
          | None => None
          end
      | None => upd_keys k b ks' m
      end
  end.

(** The swap of outputs [k] and [k+1]: only the reads at depth [k+1]. *)
Definition sswap (k : N) (b : lexp) (r : imap) : option imap :=
  let ks := ix_get (imx r) (N.succ k) in
  match upd_keys k b ks (imm r) with
  | Some m' =>
      Some (mkIM m' (PositiveMap.add (dkey_b (N.succ k)) []
                       (PositiveMap.add (dkey_b (N.succ (N.succ k))) (rev_append ks (ix_get (imx r) (N.succ (N.succ k)))) (imx r)))
                 (imn r))
  | None => None
  end.

Fixpoint bub_out_b (x : positive * lexp) (acc : list (positive * lexp)) (pos : N) (s : istate) {struct acc} :
    list (positive * lexp) * istate :=
  match acc with
  | [] => ([x], s)
  | y :: acc' =>
      if before F (snd x) (snd y) then
        let r := to_im s in
        match sswap (N.pred pos) (snd x) r with
        | Some r' => let '(rr, s') := bub_out_b x acc' (N.pred pos) (IM r') in (y :: rr, s')
        | None => (x :: acc, IM r)
        end
      else (x :: acc, s)
  end.

Fixpoint place_rng_b (k n : N) (rng above : list (positive * lexp)) (s : istate) : list (positive * lexp) * istate :=
  match rng with
  | [] => (above, s)
  | x :: rng' =>
      let '(a', s') := place_rng_b (N.succ k) n rng' above s in
      bub_out_b x a' (n - 1 - k) s'
  end.

Definition place_out_bottom_b (r : nat) (e : bform) : bform :=
  let '(o, s) := place_rng_b 0 (bl e) (firstn r (bo e)) (skipn r (bo e)) (IL (bi e)) in mkB o (bl e) (ins s).

Fixpoint popin_b (o : lexp) (rem : list (positive * (lexp * btgt))) : option (option (list (positive * (lexp * btgt)))) :=
  match rem with
  | [] => Some None
  | y :: r =>
      if lexp_eqb (blab y) o then Some (Some r)
      else if kd F (blab y) o then
        match popin_b o r with
        | Some (Some r') => Some (Some (y :: r'))
        | Some None => Some None
        | None => None
        end
      else None
  end.

Fixpoint popall_b (O1 : list (positive * lexp)) (rem : list (positive * (lexp * btgt))) (pr : list (positive * lexp)) (np : N) (canc : bool) :
  option (list (list (positive * (lexp * btgt)) * (list (positive * lexp) * N)) * bool) :=
  match O1 with
  | [] => Some ([(rem, (pr, np))], canc)
  | (y, o) :: O1' =>
      match popin_b o rem with
      | Some (Some rem') => option_map (fun '(st, c) => ((rem, (pr, np)) :: st, c)) (popall_b O1' rem' pr np true)
      | Some None => option_map (fun '(st, c) => ((rem, (pr, np)) :: st, c)) (popall_b O1' rem ((y, o) :: pr) (N.succ np) canc)
      | None => None
      end
  end.

Fixpoint rthrough_b (rem : list (positive * (lexp * btgt))) (z : lexp) (i : N) : option (btgt + N) :=
  match rem with
  | [] => Some (inr i)
  | (_, (l, t)) :: r =>
      if lexp_eqb l z then match i with N0 => Some (inl t) | _ => rthrough_b r z (N.pred i) end
      else if kd F l z then rthrough_b r z i else None
  end.

Definition newt_b (f2 : bform) (st : list (list (positive * (lexp * btgt)) * (list (positive * lexp) * N))) (t : btgt) : option btgt :=
  match t with
  | BR z i d =>
      match nth_error st (N.to_nat d) with
      | Some (rem, (_, np)) =>
          match rthrough_b rem z i with
          | Some (inl t') => Some t'
          | Some (inr i') => Some (BR z i' (bl f2 + np))
          | None => None
          end
      | None => None
      end
  | BT u p => Some (BT u (PComp (fexp (fa (b_to_c f2))) p))
  end.

Definition ecompose_b (f1 f2 : bform) : option (bform * list positive * list positive * bool) :=
  match popall_b (rev' (bo f1)) (bi f2) [] 0 false with
  | Some (st, canc) =>
      let '(rem, (pr, np)) := last st ([], ([], 0%N)) in
      match omap (fun '(id, (l, t)) => option_map (fun t' => (id, (l, t'))) (newt_b f2 st t)) (bi f1) with
      | Some I1 => Some (mkB (pr ++ bo f2) (bl f2 + np) (I1 ++ rem), rev' (map fst pr), map fst (bi f1), canc)
      | None => None
      end
  | None => None
  end.

Definition iabsorb_b (p : nat) (e : bform) : option bform :=
  match babsorb2 p (b_to_c e) with
  | Some (j, g) =>
      let e1 := reread_at_b j (bof_i g (remove_at j (rev' (map fst (bo e)))) (remove_at p (map fst (bi e)))) in
      let e2 := place_out_bottom_b (N.to_nat (bl e1) - j) e1 in
      Some (mkB (bo e2) (bl e2) (place_suffix_out_b p (bi e2)))
  | None => None
  end.

Definition restore_like_b (x : positive * (lexp * btgt)) : bool :=
  match snd (snd x) with BR z N0 _ => lexp_eqb z (blab x) | _ => false end.

Fixpoint absorb_scan_b (new : list positive) (e : bform) (p : nat) (I : list (positive * (lexp * btgt))) : option bform :=
  match I with
  | [] => None
  | x :: I' =>
      if mem (fst x) new && restore_like_b x then
        match iabsorb_b p e with Some g => Some g | None => absorb_scan_b new e (S p) I' end
      else absorb_scan_b new e (S p) I'
  end.

Fixpoint absorb_new_b (fuel : nat) (new : list positive) (e : bform) : bform :=
  match fuel with
  | 0 => e
  | S fuel' => match absorb_scan_b new e 0 (bi e) with Some g => absorb_new_b fuel' new g | None => e end
  end.

Definition icompose_b (f1 f2 : bform) : option (bform * list positive * list positive * bool) :=
  match ecompose_b f1 f2 with
  | Some (g, passed, newin, canc) =>
      let n1 := length (bi f1) in
      let g1 := reread_front_b n1 g in
      let g2 := mkB (bo g1) (bl g1) (place_front_b n1 (bi g1)) in
      let g3 := if canc then mkB (bo g2) (bl g2) (place_suffix_out_b n1 (bi g2)) else g2 in
      let g4 := place_out_bottom_b (length passed) g3 in
      Some (match newin with [] => g4 | _ => absorb_new_b (S (length newin)) newin g4 end, passed, newin, canc)
  | None => None
  end.

Definition oids_b (e : bform) : list positive := rev' (map fst (bo e)).
Definition iids_b (e : bform) : list positive := map fst (bi e).

Definition imove_b (f1 f2 : bform) (x : positive) : option (bform * bform * list positive * bool * bool) :=
  match index_of x (oids_b f1) with
  | Some j =>
      match bout_first j (b_to_c f1) with
      | Some (o, f1') =>
          match icompose_b (mkB [(x, o)] 1 []) f2 with
          | Some (g, no, _, canc) =>
              let f1n := reread_at_b j (bof_i f1' (remove_at j (oids_b f1)) (iids_b f1)) in
              Some (place_out_bottom_b (N.to_nat (bl f1n) - j) f1n, g, no, canc, false)
          | None => None
          end
      | None => None
      end
  | None =>
      match index_of x (iids_b f1) with
      | Some p =>
          match bin_first p (b_to_c f1) with
          | Some (h, t, f1') =>
              match icompose_b (mkB [] 0 [(x, (h, t))]) f2 with
              | Some (g, _, ni, canc) =>
                  let f1n := bof_i f1' (oids_b f1) (remove_at p (iids_b f1)) in
                  Some (mkB (bo f1n) (bl f1n) (place_suffix_out_b p (bi f1n)), g, ni, canc, true)
              | None => None
              end
          | None => None
          end
      | None => None
      end
  end.

(** ** The word *)

Definition ids_of_b (f : bform) : list positive := oids_b f ++ iids_b f.

Definition isz_b (f : bform) : nat := N.to_nat (bl f) + length (bi f).

Definition iempty_b (f : bform) : bool := match bo f, bi f with [], [] => true | _, _ => false end.

Fixpoint try_ids_b (f1 f2 : bform) (xs cands : list positive) : option (bform * bform * list positive * bool * bool) :=
  match xs with
  | [] => None
  | x :: xs' =>
      if mem x cands then match imove_b f1 f2 x with Some r => Some r | None => try_ids_b f1 f2 xs' cands end
      else try_ids_b f1 f2 xs' cands
  end.

Fixpoint moves_b (fuel k : nat) (f1 f2 : bform) (cands : list positive) (acc : bwork) : bform * bform * bwork :=
  match fuel with
  | 0 => (f1, f2, acc)
  | S fuel' =>
      match try_ids_b f1 f2 (ids_of_b f1) cands with
      | Some (f1', g, new, canc, lost) =>
          let acc1 := (S k, Some new) :: acc in
          let acc2 := if lost then match k with 0 => acc1 | S k' => (k', None) :: acc1 end else acc1 in
          moves_b fuel' k f1' g (if canc then ids_of_b f1' else cands) acc2
      | None => (f1, f2, acc)
      end
  end.

Definition put2b (k : nat) (st : list bitem) (mid : list bitem) : list bitem :=
  firstn k st ++ mid ++ skipn (S (S k)) st.

Definition step_b (s : list bitem * bwork) : list bitem * bwork :=
  let '(st, w) := s in
  match w with
  | [] => (st, [])
  | (k, cands) :: w' =>
      match nth_error st k, nth_error st (S k) with
      | Some (BF f1), Some (BF f2) =>
          let merged := match cands with None => icompose_b f1 f2 | Some _ => None end in
          match merged with
          | Some (g, no, ni, _) =>
              if iempty_b g then (put2b k st [], w')
              else (put2b k st [BF g], (k, Some (no ++ ni)) :: w')
          | None =>
              let c := match cands with Some c => c | None => ids_of_b f1 end in
              let '(f1', g, acc) := moves_b (isz_b f1 + 1) k f1 f2 c [] in
              if iempty_b f1' then (put2b k st [BF g], acc ++ match k with 0 => w' | S k' => (k', None) :: w' end)
              else (put2b k st [BF f1'; BF g], acc ++ w')
          end
      | _, _ => (st, w')
      end
  end.

Fixpoint settle_b (p : positive) (s : list bitem * bwork) : list bitem * bwork :=
  match snd s with
  | [] => s
  | _ =>
      match p with
      | xH => step_b s
      | xO p' => settle_b p' (settle_b p' s)
      | xI p' => step_b (settle_b p' (settle_b p' s))
      end
  end.

Definition insert_b (it : bitem) (st : list bitem) : list bitem :=
  match it with
  | BF f => if iempty_b f then st else fst (settle_b bbig (it :: st, [(0, None)]))
  | BA _ _ => it :: st
  end.

(** ** Expressions *)

Fixpoint bub_down_b (x : positive * lexp) (below : list (positive * lexp)) (pos : N) (s : istate) {struct below} :
    list (positive * lexp) * istate :=
  match below with
  | [] => ([x], s)
  | y :: below' =>
      if before F (snd y) (snd x) then
        let r := to_im s in
        match sswap pos (snd y) r with
        | Some r' => let '(rr, s') := bub_down_b x below' (N.succ pos) (IM r') in (y :: rr, s')
        | None => (x :: below, IM r)
        end
      else (x :: below, s)
  end.

Fixpoint place_down_b (k : N) (pre rest : list (positive * lexp)) (s : istate) : list (positive * lexp) * istate :=
  match pre with
  | [] => (rest, s)
  | x :: pre' =>
      let '(r', s') := place_down_b (N.succ k) pre' rest s in
      bub_down_b x r' k s'
  end.

Definition place_out_top_b (r : nat) (e : bform) : bform :=
  let top := rev' (bo e) in
  let '(o, s) := place_down_b 0 (firstn r top) (skipn r top) (IL (bi e)) in mkB (rev' o) (bl e) (ins s).

Definition bshift_ts (nN : N) (L : list lexp) (t : btgt) : btgt :=
  match t with BR z i d => BR z i (nN + d) | BT u p => BT u (fold_right PShift p L) end.

Definition lift_b (L : list lexp) (f : bform) (c : positive) : bform :=
  let n := length L in
  let nN := N.of_nat n in
  mkB (bo f ++ rev' (combine (pseq c n) L)) (bl f + nN)
      (combine (pseq (padd c n) n) (mapi_fromN 0 (fun k h => (h, BR h 0 k)) L)
       ++ map (fun '(id, (g, t)) => (id, (g, bshift_ts nN L t))) (bi f)).

Fixpoint below_ok_b (l : lexp) (n : N) (O : list (positive * lexp)) (seen : bool) : bool :=
  match O with
  | (_, o) :: O' =>
      match n with
      | N0 => seen
      | _ =>
          if lexp_eqb o l then (if seen then false else below_ok_b l (N.pred n) O' true)
          else if kd F l o then below_ok_b l (N.pred n) O' seen else false
      end
  | [] => seen
  end.

Fixpoint ballkd_in_e (l : lexp) (I : list (positive * (lexp * btgt))) : bool :=
  match I with [] => true | (_, (m, _)) :: I' => if kd F l m then ballkd_in_e l I' else false end.

Definition pre_x_b (x : positive * (lexp * btgt)) (inside : list (positive * (lexp * btgt))) (e : bform) : bool :=
  match x with
  | (_, (l, BR z N0 d)) =>
      if lexp_eqb z l then
        if N.leb d (bl e) then if below_ok_b l (bl e - d) (bo e) false then ballkd_in_e l inside else false
        else false
      else false
  | _ => false
  end.

Fixpoint absorb_walk_b (fuel p : nat) (rf inside : list (positive * (lexp * btgt))) (e : bform) (k : nat) : bform * nat :=
  match fuel with
  | 0 => (e, k)
  | S fuel' =>
      match rf with
      | [] => (e, k)
      | x :: rf' =>
          match (if pre_x_b x inside e then iabsorb_b p e else None) with
          | Some e' => absorb_walk_b fuel' (pred p) (rev' (firstn p (bi e'))) (skipn p (bi e')) e' k
          | None => absorb_walk_b fuel' (pred p) rf' (x :: inside) e (S k)
          end
      end
  end.

Definition lift_many_b (L : list lexp) (it : bitem) (c : positive) : bitem * positive :=
  match it with
  | BA L' n => (BA (L ++ L') n, c)
  | BF f =>
      let n := length L in
      let f0 := lift_b L f c in
      let '(f1, k) := absorb_walk_b n (pred n) (rev' (firstn n (bi f0))) (skipn n (bi f0)) f0 0 in
      let f2 := mkB (bo f1) (bl f1) (place_front_b k (bi f1)) in
      (BF (place_out_top_b (Nat.min k (N.to_nat (bl f2))) f2), padd c (n + n))
  end.

Fixpoint insert_lifted_b (L : list lexp) (w : list bitem) (st : list bitem) (c : positive) : list bitem * positive :=
  match w with
  | [] => (st, c)
  | it :: w' =>
      let '(st1, c1) := insert_lifted_b L w' st c in
      let '(it', c2) := lift_many_b L it c1 in
      (insert_b it' st1, c2)
  end.

Fixpoint rnormN (e : aexp) (st : list bitem) (c : positive) {struct e} : list bitem * positive :=
  match e with
  | AId => (st, c)
  | AAtom n => (insert_b (BA [] n) st, c)
  | ACompose a b => let '(st1, c1) := rnormN a st c in rnormN b st1 c1
  | AOuter h a => let '(f, c1) := bfresh (weak h) c in rnormN a (insert_b (BF f) st) c1
  | AInner h t a =>
      let '(f, c1) := bfresh (entry h t) c in
      let fix peel (R : list lexp) (a : aexp) (st : list bitem) (c : positive) {struct a} : list bitem * positive :=
        match a with
        | ALift h' a' => peel (h' :: R) a' st c
        | _ => let '(w, c1) := rnormN a [] c in insert_lifted_b (rev' R) w st c1
        end in
      peel [h] a (insert_b (BF f) st) c1
  | ALift h a =>
      let fix peel (R : list lexp) (a : aexp) (st : list bitem) (c : positive) {struct a} : list bitem * positive :=
        match a with
        | ALift h' a' => peel (h' :: R) a' st c
        | _ => let '(w, c1) := rnormN a [] c in insert_lifted_b (rev' R) w st c1
        end in
      peel [h] a st c
  end.

Definition rrunN (e : aexp) : fword := map bstrip (fst (rnormN e [] xH)).

End RunN.

(** ** Soundness *)

(** *** Numbers *)

Lemma Neqb_nat a b : N.eqb a b = Nat.eqb (N.to_nat a) (N.to_nat b).
Proof. apply Bool.eq_iff_eq_true; rewrite N.eqb_eq, Nat.eqb_eq; split; [intros ->; reflexivity|apply N2Nat.inj]. Qed.

Lemma Nleb_nat a b : N.leb a b = Nat.leb (N.to_nat a) (N.to_nat b).
Proof. apply Bool.eq_iff_eq_true; rewrite N.leb_le, Nat.leb_le; lia. Qed.

Lemma Nltb_nat a b : N.ltb a b = Nat.ltb (N.to_nat a) (N.to_nat b).
Proof. apply Bool.eq_iff_eq_true; rewrite N.ltb_lt, Nat.ltb_lt; lia. Qed.

Lemma N0nat : N.to_nat 0 = 0.
Proof. reflexivity. Qed.

Lemma Npos_succ q : exists m, N.to_nat (Npos q) = S m /\ N.to_nat (N.pred (Npos q)) = m.
Proof. destruct (Pos2Nat.is_succ q) as [m Hm]; exists m; split; [exact Hm|rewrite N2Nat.inj_pred; cbn [N.to_nat]; rewrite Hm; reflexivity]. Qed.

Ltac ncase i :=
  let q := fresh "q" in let m := fresh "m" in let H1 := fresh "Hq" in let H2 := fresh "Hq" in
  destruct i as [|q]; cbv iota beta; [rewrite ?N0nat; cbv iota beta|destruct (Npos_succ q) as [m [H1 H2]]; rewrite ?H2, ?H1; cbn [Nat.pred]; cbv iota beta].

Ltac npos := repeat match goal with H : N.to_nat (N.pos _) = _ |- _ => rewrite H; cbn [Nat.pred] end.

Ltac nnorm := rewrite ?Neqb_nat, ?Nleb_nat, ?Nltb_nat, ?N2Nat.inj_succ, ?N2Nat.inj_pred, ?N2Nat.inj_add, ?N2Nat.inj_sub, ?N2Nat.inj_min, ?Nat2N.id, ?N0nat.

Lemma omap_comm {A B A' B'} (g : A -> A') (h : B -> B') (f : A -> option B) (f' : A' -> option B') :
  (forall x, option_map h (f x) = f' (g x)) -> forall l, option_map (map h) (omap f l) = omap f' (map g l).
Proof.
  intros H; induction l as [|x l IH]; cbn; [reflexivity|]; rewrite <- H, <- IH.
  destruct (f x), (omap f l); reflexivity.
Qed.

Lemma remove_at_map {X Y} (g : X -> Y) k l : remove_at k (map g l) = map g (remove_at k l).
Proof. revert l; induction k as [|k IH]; intros [|a l]; cbn; auto; f_equal; apply IH. Qed.

Lemma mapi_from_map {X Y Z} (g : X -> Y) (h : nat -> Y -> Z) (h' : nat -> X -> Z) k l :
  (forall q x, h q (g x) = h' q x) -> mapi_from k h (map g l) = mapi_from k h' l.
Proof. intros H; revert k; induction l as [|a l IH]; intros k; cbn; [reflexivity|rewrite H, IH; reflexivity]. Qed.

Lemma map_mapi_from {X Y Z} (g : Y -> Z) (h : nat -> X -> Y) k l : map g (mapi_from k h l) = mapi_from k (fun q x => g (h q x)) l.
Proof. revert k; induction l as [|a l IH]; intros k; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma rev'_rev {X} (l : list X) : rev' l = rev l.
Proof. unfold rev'; symmetry; apply rev_alt. Qed.


Lemma ta_tb t : ta (tb t) = t.
Proof. destruct t; cbn; rewrite ?Nat2N.id; reflexivity. Qed.

Lemma fa_fb f : fa (fb f) = f.
Proof. destruct f as [O I]; unfold fa, fb; cbn; f_equal; rewrite map_map; erewrite map_ext; [apply map_id|]; intros [l t]; unfold ina; cbn; rewrite ta_tb; reflexivity. Qed.

Lemma fa_b_to_c e : fa (b_to_c e) = beff e.
Proof. unfold fa, b_to_c, beff; cbn; rewrite rev'_rev, map_map; reflexivity. Qed.

(** *** Steps on [bfm] *)

Section StepsN.

Variable F : order.
Variable M : cmodel.
Hypothesis HM : ccons F M.

Local Notation popn := (popn M).
Local Notation tden := (tden M).
Local Notation pushes := (pushes M).
Local Notation fden := (fden M).
Local Notation wden_app := (CSpec.wden_app M).
Local Notation pushes_app := (CSpec.pushes_app M).
Local Notation pushes_ext := (CSpec.pushes_ext M).
Local Notation tden_shift := (CSpec.tden_shift M).
Local Notation pushes_shift := (CSpec.pushes_shift M).
Local Notation lift_f_sound := (CSpec.lift_f_sound M).
Local Notation restore_sound := (CSpec.restore_sound M).
Local Notation ttgt_sound := (CSpec.ttgt_sound M).
Local Notation entry_sound := (CSpec.entry_sound M).
Local Notation lift_i_sound := (CSpec.lift_i_sound M).
Local Notation lift_w_sound := (CSpec.lift_w_sound M).
Local Notation of_exp_sound := (CSpec.of_exp_sound M).
Local Notation rexp_sound := (CSpec.rexp_sound M).
Local Notation texp_of_sound := (CSpec.texp_of_sound M).
Local Notation fexp_sound := (CSpec.fexp_sound M).
Local Notation iexp_sound := (CSpec.iexp_sound M).
Local Notation wexp_sound := (CSpec.wexp_sound M).
Local Notation pops_comm := (CSpec.pops_comm F M HM).
Local Notation cname_pop_other := (CSpec.cname_pop_other F M HM).
Local Notation cname_push_other := (CSpec.cname_push_other F M HM).
Local Notation pop_comm := (CSpec.pop_comm F M HM).
Local Notation kdk := (CSpec.kdk F).
Local Notation bk := (CSpec.bk F).
Local Notation popn_0 := (CSpec.popn_0 M).
Local Notation popn_app_le := (CSpec.popn_app_le M).
Local Notation popn_app_add := (CSpec.popn_app_add M).
Local Notation popn_over := (CSpec.popn_over M).
Local Notation popn_min := (CSpec.popn_min M).
Local Notation popn_S := (CSpec.popn_S M).
Local Notation omap_pushes := (CSpec.omap_pushes M).
Local Notation forallb_kd := (CSpec.forallb_kd F).
Local Notation forallb_kd_in := (CSpec.forallb_kd_in F).
Local Notation popn_pop_comm := (CSpec.popn_pop_comm F M HM).
Local Notation popn_hd := (CSpec.popn_hd F M HM).
Local Notation popn_push_comm := (CSpec.popn_push_comm F M HM).
Local Notation pushes_pop_comm := (CSpec.pushes_pop_comm F M HM).
Local Notation pushes_hd := (CSpec.pushes_hd F M HM).
Local Notation pushes_push_comm := (CSpec.pushes_push_comm F M HM).
Local Notation popn_mid := (CSpec.popn_mid M).
Local Notation popn_at := (CSpec.popn_at M).
Local Notation popn_len_le := (CSpec.popn_len_le M).
Local Notation wden_rev_cons := (CSpec.wden_rev_cons M).

Lemma ina_pair l t : ina (l, t) = (l, ta t).
Proof. reflexivity. Qed.

Lemma bomap_pushes (g : lexp * btgt -> option (lexp * btgt)) O O' I I' b x x' :
  omap g I = Some I' ->
  (forall h t h' t', g (h, t) = Some (h', t') -> h' = h /\ tden O' (ta t') x' = tden O (ta t) x) ->
  pushes O' (map ina I') b x' = pushes O (map ina I) b x.
Proof.
  revert I'; induction I as [|[h t] I IH]; intros I' E H; cbn in E.
  - injection E as <-; reflexivity.
  - destruct (g (h, t)) as [[h' t']|] eqn:G; [|discriminate].
    destruct (omap g I) as [I''|] eqn:E2; [|discriminate]; injection E as <-.
    destruct (H h t h' t' G) as [-> T]; cbn; rewrite T, (IH I'' eq_refl H); reflexivity.
Qed.

Lemma bforallb_kd_in l (Q : list (lexp * btgt)) : forallb (fun '(m, _) => kd F l m) Q = true ->
  Forall (fun mt => known_distinct F l (fst mt)) (map ina Q).
Proof.
  intros H; rewrite forallb_forall in H; apply Forall_forall; intros [m t] Hm; apply in_map_iff in Hm as [[m' t'] [E Hm]].
  injection E as <- <-; apply kdk; exact (H (m', t') Hm).
Qed.

Lemma babsorb_at_sound j p f f' x : babsorb_at F j p f = Some f' -> fden (fa f') x = fden (fa f) x.
Proof.
  unfold babsorb_at; destruct f as [O I]; cbn [cout cin].
  destruct (nth_error O j) as [l|] eqn:Ej; [|discriminate].
  destruct (nth_error I p) as [[l' [z i d|u q]]|] eqn:Ep; try discriminate.
  destruct (lexp_eqb l l' && lexp_eqb z l && N.eqb i 0 && N.eqb d (N.of_nat j)
            && forallb (kd F l) (skipn (S j) O) && forallb (fun '(m, _) => kd F l m) (skipn (S p) I)) eqn:C; [|discriminate].
  destruct (omap _ (remove_at p I)) as [Is|] eqn:Om; [|discriminate]; intros H; injection H as <-.
  rewrite !andb_true_iff in C; destruct C as [[[[[C1 C2] C3] C4] C5] C6].
  apply lexp_eqb_true in C1, C2; apply N.eqb_eq in C3, C4; subst l' z i d.
  destruct (split_at O j l Ej) as [A [B [-> LA]]]; subst j.
  destruct (split_at I p _ Ep) as [P [Q [-> LP]]]; subst p.
  rewrite skipn_app_at in C5; rewrite skipn_app_at in C6; apply forallb_kd in C5; apply bforallb_kd_in in C6.
  rewrite (remove_at_app P Q) in Om; rewrite (remove_at_app A B).
  unfold fa; cbn [cout cin]; rewrite map_app; cbn [map].
  set (Pa := popn A (length A) x).
  assert (Base : popn (A ++ l :: B) (length (A ++ l :: B)) x = cpop l (popn (A ++ B) (length (A ++ B)) x)).
  { rewrite !length_app; cbn [length]; rewrite popn_at, !popn_app_add, popn_pop_comm by exact C5; reflexivity. }
  unfold fden; cbn [fout fin]; rewrite Base, pushes_app; cbn [pushes]; rewrite pushes_pop_comm by exact C6.
  rewrite ina_pair; cbn [ta tden]; rewrite Nat2N.id, N0nat, (popn_len_le A (l :: B) (length A) x) by lia.
  fold Pa; rewrite (cname0 M), <- (popn_hd l B (length B) Pa C5).
  assert (Z : popn B (length B) Pa = popn (A ++ B) (length (A ++ B)) x) by (rewrite length_app, popn_app_add; reflexivity).
  rewrite Z, <- (pushes_hd l (A ++ l :: B) (map ina Q) _ x C6), cpush_pop, <- pushes_app, <- map_app.
  apply (bomap_pushes _ _ _ (P ++ Q) Is _ _ _ Om).
  intros h t h' t' G; destruct (bdrop_read F (N.of_nat (length A)) l t) as [t''|] eqn:Dr; cbn in G; [|discriminate].
  injection G as <- <-; split; [reflexivity|].
  destruct t as [z i d|u q']; cbn [bdrop_read] in Dr; [|injection Dr as <-; reflexivity].
  rewrite Nleb_nat, Nat2N.id in Dr.
  destruct (Nat.leb (N.to_nat d) (length A)) eqn:Le.
  - apply Nat.leb_le in Le; injection Dr as <-; cbn [tden ta]; rewrite !popn_len_le by lia; reflexivity.
  - apply Nat.leb_gt in Le.
    assert (Pd : popn (A ++ l :: B) (N.to_nat d) x = cpop l (popn (A ++ B) (pred (N.to_nat d)) x)).
    { replace (N.to_nat d) with (length A + S (N.to_nat d - length A - 1)) by lia; rewrite popn_at.
      replace (pred (length A + S (N.to_nat d - length A - 1))) with (length A + (N.to_nat d - length A - 1)) by lia.
      rewrite popn_app_add, popn_pop_comm by exact C5; reflexivity. }
    destruct (lexp_eqb z l) eqn:Ez.
    + apply lexp_eqb_true in Ez; subst z; injection Dr as <-; cbn [tden ta].
      rewrite N2Nat.inj_succ, N2Nat.inj_pred, Pd, (cname_pop M); reflexivity.
    + destruct (kd F z l) eqn:K; [|discriminate]; injection Dr as <-; cbn [tden ta].
      rewrite N2Nat.inj_pred, Pd, cname_pop_other by (apply kdk, K); reflexivity.
Qed.

Lemma skipn_cons_inv {X} (O : list X) j o R : skipn j O = o :: R -> nth_error O j = Some o /\ skipn (S j) O = R.
Proof. revert O; induction j as [|j IH]; intros [|x O] H; cbn in *; try discriminate; [injection H as -> ->; auto|apply IH, H]. Qed.

Lemma bslot_go_sound l O R j j' y : R = skipn j O -> bslot_go F l R j = Some j' -> cname l 0 (popn O j' y) = cname l 0 (popn O j y).
Proof.
  revert j; induction R as [|o R IH]; intros j HR; cbn; [discriminate|].
  destruct (skipn_cons_inv O j o R (eq_sym HR)) as [N HR'].
  destruct (lexp_eqb o l) eqn:E; [intros H; injection H as <-; reflexivity|].
  destruct (kd F l o) eqn:K; [|discriminate]; intros H; rewrite (IH _ (eq_sym HR') H).
  assert (L : j < length O) by (apply nth_error_Some; congruence).
  rewrite (popn_S O j y L), (nth_error_nth O j LNone N); apply cname_pop_other, kdk, K.
Qed.

Lemma pushes_set_tgt O p t I b x : (forall l s, nth_error I p = Some (l, s) -> tden O (ta t) x = tden O (ta s) x) ->
  pushes O (map ina (set_tgt p t I)) b x = pushes O (map ina I) b x.
Proof.
  revert p; induction I as [|[l s] I IH]; intros [|p] H; cbn [set_tgt map]; try reflexivity; rewrite !ina_pair; cbn [pushes].
  - rewrite (H l s eq_refl); reflexivity.
  - rewrite IH; [reflexivity|]; intros l' s' N; apply (H l' s' N).
Qed.

Lemma babsorb2_sound p f j g x : babsorb2 F p f = Some (j, g) -> fden (fa g) x = fden (fa f) x.
Proof.
  unfold babsorb2; destruct (nth_error (cin f) p) as [[l [z i d|u q]]|] eqn:Np; try discriminate.
  destruct (lexp_eqb z l) eqn:C1; [|discriminate]; destruct (N.eqb i 0) eqn:C2; [|discriminate].
  apply lexp_eqb_true in C1; apply N.eqb_eq in C2; subst z i.
  destruct (bslot_go F l (skipn (N.to_nat d) (cout f)) (N.to_nat d)) as [j'|] eqn:S; [|discriminate].
  destruct (ballkd F l _); [|discriminate]; destruct (ballkd_in F l _); [|discriminate].
  destruct (babsorb_at F j' p (bset_in p (BR l 0 (N.of_nat j')) f)) as [g'|] eqn:A; cbn [option_map]; [|discriminate].
  intros H; injection H as <- <-.
  rewrite (babsorb_at_sound _ _ _ _ x A).
  unfold bset_in, fa, fden; cbn [cout cin fout fin]; apply pushes_set_tgt; intros l' t N.
  rewrite Np in N; injection N as <- <-; cbn [tden ta].
  rewrite Nat2N.id, N0nat; apply (bslot_go_sound _ _ _ _ _ _ eq_refl S).
Qed.

Lemma bout_first_sound j f o f' y : bout_first F j f = Some (o, f') -> fden (fa f) y = fden (fa f') (cpop o y).
Proof.
  unfold bout_first; destruct f as [O I]; cbn [cout cin].
  destruct (nth_error O j) as [o'|] eqn:Ej; [|discriminate].
  destruct (forallb (kd F o') (firstn j O)) eqn:C; [|discriminate].
  destruct (omap _ I) as [Is|] eqn:Om; [|discriminate]; intros H; injection H as <- <-.
  destruct (split_at O j o' Ej) as [A [B [-> LA]]]; subst j.
  rewrite firstn_app_at in C; apply forallb_kd in C; rewrite (remove_at_app A B).
  unfold fa, fden; cbn [cout cin fout fin].
  assert (Base : popn (A ++ B) (length (A ++ B)) (cpop o' y) = popn (A ++ o' :: B) (length (A ++ o' :: B)) y).
  { rewrite !length_app; cbn [length]; rewrite popn_at, popn_app_add, popn_pop_comm by exact C; reflexivity. }
  rewrite Base; symmetry; apply (bomap_pushes _ _ _ I Is _ _ _ Om).
  intros h t h' t' G; destruct (btop_read F (N.of_nat (length A)) o' t) as [t''|] eqn:Tr; cbn in G; [|discriminate].
  injection G as <- <-; split; [reflexivity|].
  destruct t as [z i d|u q]; cbn [btop_read] in Tr; [|discriminate].
  rewrite Nltb_nat, Nat2N.id in Tr.
  destruct (Nat.ltb (length A) (N.to_nat d)) eqn:Lt.
  - apply Nat.ltb_lt in Lt; injection Tr as <-; cbn [tden ta]; rewrite N2Nat.inj_pred.
    replace (N.to_nat d) with (length A + S (N.to_nat d - length A - 1)) by lia; rewrite popn_at.
    replace (pred (length A + S (N.to_nat d - length A - 1))) with (length A + (N.to_nat d - length A - 1)) by lia.
    rewrite popn_app_add, popn_pop_comm by exact C; reflexivity.
  - apply Nat.ltb_ge in Lt.
    assert (Pd : popn (A ++ B) (N.to_nat d) (cpop o' y) = cpop o' (popn (A ++ o' :: B) (N.to_nat d) y)).
    { rewrite !popn_len_le by lia; apply popn_pop_comm, C. }
    destruct (lexp_eqb z o') eqn:Ez.
    + apply lexp_eqb_true in Ez; subst z; destruct i as [|q]; [discriminate|]; injection Tr as <-; cbn [tden ta].
      change (Pos.pred_N q) with (N.pred (N.pos q)); destruct (Npos_succ q) as [m [H1 H2]]; rewrite H1, H2, Pd, (cname_pop M); reflexivity.
    + destruct (kd F z o') eqn:K; [|discriminate]; injection Tr as <-; cbn [tden ta].
      rewrite Pd, cname_pop_other by (apply kdk, K); reflexivity.
Qed.

Lemma bpull_sound O d z i i' y : bpull F O d z i = Some i' -> cname z (N.to_nat i) (popn O d y) = cname z (N.to_nat i') y.
Proof.
  revert d y i'; induction O as [|o O IH]; intros [|d] y i' H; cbn [bpull] in H;
    try (injection H as <-; reflexivity).
  destruct (bpull F O d z i) as [j|] eqn:P; [|discriminate]; cbn [popn]; rewrite (IH d (cpop o y) j P).
  destruct (lexp_eqb o z) eqn:E.
  - apply lexp_eqb_true in E; subst o; injection H as <-; rewrite N2Nat.inj_succ; apply (cname_pop M).
  - destruct (kd F z o) eqn:K; [|discriminate]; injection H as <-; apply cname_pop_other, kdk, K.
Qed.

Lemma bin_first_sound p f h t' f' y : bin_first F p f = Some (h, t', f') ->
  fden (fa f) y = fden (fa f') (cpush h y (tden [] (ta t') y)).
Proof.
  unfold bin_first; destruct f as [O I]; cbn [cout cin].
  destruct (nth_error I p) as [[h0 t]|] eqn:Ep; [|discriminate].
  destruct (forallb (fun '(m, _) => kd F h0 m) (skipn (S p) I) && forallb (kd F h0) O) eqn:C; [|discriminate].
  apply andb_true_iff in C as [C1 C2]; apply forallb_kd in C2.
  set (t0 := match t with BR z i d => option_map (fun i' => BR z i' 0) (bpull F O (N.to_nat d) z i) | BT _ _ => Some t end).
  destruct t0 as [t''|] eqn:T0; [|discriminate].
  destruct (omap _ (remove_at p I)) as [Is|] eqn:Om; [|discriminate]; intros H; injection H as <- <- <-.
  destruct (split_at I p _ Ep) as [P [Q [-> LP]]]; subst p.
  rewrite skipn_app_at in C1; apply bforallb_kd_in in C1; rewrite (remove_at_app P Q) in Om.
  assert (V : tden O (ta t) y = tden [] (ta t'') y).
  { unfold t0 in T0; destruct t as [z i d|u q].
    - destruct (bpull F O (N.to_nat d) z i) as [i'|] eqn:Pl; [|discriminate]; injection T0 as <-; cbn [tden ta].
      rewrite N0nat, popn_0; apply bpull_sound, Pl.
    - injection T0 as <-; reflexivity. }
  set (y' := cpush h0 y (tden [] (ta t'') y)).
  unfold fa, fden; cbn [cout cin fout fin]; rewrite map_app, pushes_app; cbn [map]; rewrite ina_pair; cbn [pushes].
  rewrite V, pushes_push_comm by exact C1; rewrite <- popn_push_comm by exact C2; fold y'.
  rewrite <- pushes_app, <- map_app; symmetry; apply (bomap_pushes _ _ _ (P ++ Q) Is _ _ _ Om).
  intros m s m' s' G; destruct (bunder_read F h0 s) as [s''|] eqn:U; cbn in G; [|discriminate].
  injection G as <- <-; split; [reflexivity|].
  destruct s as [z i d|u q]; cbn [bunder_read] in U.
  - assert (Pd : popn O (N.to_nat d) y' = cpush h0 (popn O (N.to_nat d) y) (tden [] (ta t'') y)) by (apply popn_push_comm, C2).
    destruct (lexp_eqb z h0) eqn:Ez.
    + apply lexp_eqb_true in Ez; subst z; injection U as <-; cbn [tden ta]; rewrite N2Nat.inj_succ, Pd, (cname_push M); reflexivity.
    + destruct (kd F z h0) eqn:K; [|discriminate]; injection U as <-; cbn [tden ta].
      rewrite Pd, cname_push_other by (apply kdk, K); reflexivity.
  - injection U as <-; cbn [tden ta cp fpb]; unfold y'; rewrite cpop_push; reflexivity.
Qed.

End StepsN.

(** *** Forms with ids *)

Section SoundN.

Variable F : order.
Variable M : cmodel.
Hypothesis HM : ccons F M.

Local Notation popn := (popn M).
Local Notation tden := (tden M).
Local Notation pushes := (pushes M).
Local Notation fd := (fden M).
Local Notation wden_app := (CSpec.wden_app M).
Local Notation pushes_app := (CSpec.pushes_app M).
Local Notation pushes_ext := (CSpec.pushes_ext M).
Local Notation tden_shift := (CSpec.tden_shift M).
Local Notation pushes_shift := (CSpec.pushes_shift M).
Local Notation lift_f_sound := (CSpec.lift_f_sound M).
Local Notation restore_sound := (CSpec.restore_sound M).
Local Notation ttgt_sound := (CSpec.ttgt_sound M).
Local Notation entry_sound := (CSpec.entry_sound M).
Local Notation lift_i_sound := (CSpec.lift_i_sound M).
Local Notation lift_w_sound := (CSpec.lift_w_sound M).
Local Notation of_exp_sound := (CSpec.of_exp_sound M).
Local Notation rexp_sound := (CSpec.rexp_sound M).
Local Notation texp_of_sound := (CSpec.texp_of_sound M).
Local Notation fexp_sound := (CSpec.fexp_sound M).
Local Notation iexp_sound := (CSpec.iexp_sound M).
Local Notation wexp_sound := (CSpec.wexp_sound M).
Local Notation pops_comm := (CSpec.pops_comm F M HM).
Local Notation cname_pop_other := (CSpec.cname_pop_other F M HM).
Local Notation cname_push_other := (CSpec.cname_push_other F M HM).
Local Notation pop_comm := (CSpec.pop_comm F M HM).
Local Notation kdk := (CSpec.kdk F).
Local Notation bk := (CSpec.bk F).
Local Notation popn_0 := (CSpec.popn_0 M).
Local Notation popn_app_le := (CSpec.popn_app_le M).
Local Notation popn_app_add := (CSpec.popn_app_add M).
Local Notation popn_over := (CSpec.popn_over M).
Local Notation popn_min := (CSpec.popn_min M).
Local Notation popn_S := (CSpec.popn_S M).
Local Notation omap_pushes := (CSpec.omap_pushes M).
Local Notation forallb_kd := (CSpec.forallb_kd F).
Local Notation forallb_kd_in := (CSpec.forallb_kd_in F).
Local Notation popn_pop_comm := (CSpec.popn_pop_comm F M HM).
Local Notation popn_hd := (CSpec.popn_hd F M HM).
Local Notation popn_push_comm := (CSpec.popn_push_comm F M HM).
Local Notation pushes_pop_comm := (CSpec.pushes_pop_comm F M HM).
Local Notation pushes_hd := (CSpec.pushes_hd F M HM).
Local Notation pushes_push_comm := (CSpec.pushes_push_comm F M HM).
Local Notation popn_mid := (CSpec.popn_mid M).
Local Notation popn_at := (CSpec.popn_at M).
Local Notation popn_len_le := (CSpec.popn_len_le M).
Local Notation wden_rev_cons := (CSpec.wden_rev_cons M).

(** Reads no deeper than the outputs; the number of outputs right. *)
Definition tok (n : nat) (t : tgt) : Prop := match t with TR _ _ d => d <= n | TT _ _ => True end.
Definition wfd (f : form) : Prop := Forall (fun lt => tok (length (fout f)) (snd lt)) (fin f).
Definition bok (e : bform) : Prop := N.to_nat (bl e) = length (bo e) /\ wfd (beff e).

Lemma length_zipd {X} ids (l : list X) : length (zipd ids l) = length l.
Proof. revert ids; induction l as [|x l IH]; intros [|i ids]; cbn; rewrite ?IH; reflexivity. Qed.

Lemma map_snd_zipd {X} ids (l : list X) : map snd (zipd ids l) = l.
Proof. revert ids; induction l as [|x l IH]; intros [|i ids]; cbn; rewrite ?IH; reflexivity. Qed.

Lemma map_isnd I : map isnd I = map ina (map snd I).
Proof. rewrite map_map; reflexivity. Qed.

Lemma beff_len e : length (fout (beff e)) = length (bo e).
Proof. unfold beff; cbn; rewrite length_rev, length_map; reflexivity. Qed.

Lemma beff_bof_i g o i : beff (bof_i g o i) =
  mkF (cout g) (map ina (map (fun x => (fst x, bclamp (N.of_nat (length (cout g))) (snd x))) (cin g))).
Proof. unfold beff, bof_i; cbn; rewrite rev'_rev, map_rev, rev_involutive, !map_snd_zipd, map_isnd, map_snd_zipd; reflexivity. Qed.

Lemma bclamp_sound O P t x : tden (O ++ P) (ta (bclamp (N.of_nat (length O)) t)) x = tden O (ta t) x.
Proof.
  destruct t as [z i d|u p]; [|reflexivity]; cbn [bclamp ta tden]; rewrite N2Nat.inj_min, Nat2N.id.
  rewrite popn_app_le by lia; rewrite popn_min; reflexivity.
Qed.

Lemma pushes_bclamp O I b x :
  pushes O (map ina (map (fun x => (fst x, bclamp (N.of_nat (length O)) (snd x))) I)) b x = pushes O (map ina I) b x.
Proof.
  induction I as [|[l t] I IH]; cbn [map]; [reflexivity|]; rewrite !ina_pair; cbn [pushes fst snd]; rewrite IH.
  pose proof (bclamp_sound O [] t x) as H; rewrite app_nil_r in H; rewrite H; reflexivity.
Qed.

Lemma bof_i_sound g o i x : fd (beff (bof_i g o i)) x = fd (fa g) x.
Proof. rewrite beff_bof_i; unfold fden, fa; cbn [fout fin cout cin]; apply pushes_bclamp. Qed.

Lemma tok_bclamp n t : tok n (ta (bclamp (N.of_nat n) t)).
Proof. destruct t; cbn; rewrite ?N2Nat.inj_min, ?Nat2N.id; [lia|exact Logic.I]. Qed.

Lemma bof_i_ok g o i : bok (bof_i g o i).
Proof.
  split; [cbn; rewrite Nat2N.id, rev'_rev, length_rev, length_zipd; reflexivity|].
  unfold wfd; rewrite beff_bof_i; cbn [fout fin].
  apply Forall_forall; intros [l t] H; apply in_map_iff in H as [[l' t'] [E H]]; apply in_map_iff in H as [[l0 t0] [E' _]].
  rewrite ina_pair in E; injection E as <- <-; injection E' as <- <-; apply tok_bclamp.
Qed.

(** *** Reads, from the bottom *)

Lemma nread_up_b_sound up B z i d x : N.to_nat d = length up ->
  tden (rev (map snd up) ++ B) (ta (nread_up_b F up z i d)) x = cname z (N.to_nat i) (popn (rev (map snd up) ++ B) (N.to_nat d) x).
Proof.
  revert B i d; induction up as [|[id o] up IH]; intros B i d Hd; cbn [length] in Hd.
  - destruct d as [|q]; [reflexivity|]; destruct (Npos_succ q) as [m [H1 _]]; lia.
  - destruct d as [|q]; [cbn in Hd; lia|]; destruct (Npos_succ q) as [m [H1 H2]].
    assert (Hm : m = length up) by lia; rewrite Hm in H1, H2; clear Hm m.
    replace (rev (map snd ((id, o) :: up)) ++ B) with (rev (map snd up) ++ o :: B) by (cbn; rewrite <- app_assoc; reflexivity).
    assert (P : popn (rev (map snd up) ++ o :: B) (N.to_nat (N.pos q)) x = cpop o (popn (rev (map snd up) ++ o :: B) (length up) x)).
    { rewrite H1; replace (S (length up)) with (length (rev (map snd up)) + S 0) by (rewrite length_rev, length_map; lia).
      rewrite popn_at, popn_0, popn_len_le by (rewrite length_rev, length_map; lia); rewrite length_rev, length_map; reflexivity. }
    cbn [nread_up_b]; rewrite P.
    destruct (lexp_eqb o z) eqn:E.
    + apply lexp_eqb_true in E; subst o; rewrite IH by (rewrite H2; reflexivity).
      rewrite H2, N2Nat.inj_succ, (cname_pop M); reflexivity.
    + destruct (kd F z o) eqn:K.
      * rewrite IH by (rewrite H2; reflexivity); rewrite H2, cname_pop_other by (apply kdk, K); reflexivity.
      * cbn [ta tden]; rewrite P; reflexivity.
Qed.

Lemma nread_up_b_tok up z i d n : N.to_nat d <= n -> tok n (ta (nread_up_b F up z i d)).
Proof.
  revert i d; induction up as [|[id o] up IH]; intros i d Hd; destruct d as [|q]; cbn [nread_up_b]; try (cbn [ta tok]; lia).
  destruct (lexp_eqb o z); [apply IH; rewrite N2Nat.inj_pred; lia|].
  destruct (kd F z o); [apply IH; rewrite N2Nat.inj_pred; lia|cbn [ta tok]; lia].
Qed.

Lemma nread_e_b_sound e t x : N.to_nat (bl e) = length (bo e) ->
  tden (fout (beff e)) (ta (nread_e_b F e t)) x = tden (fout (beff e)) (ta t) x.
Proof.
  intros H; destruct t as [z i d|u p]; [|reflexivity]; cbn [nread_e_b]; rewrite Nleb_nat, H.
  destruct (Nat.leb (N.to_nat d) (length (bo e))) eqn:L; [|reflexivity]; apply Nat.leb_le in L.
  rewrite N2Nat.inj_sub, H.
  set (k := length (bo e) - N.to_nat d).
  assert (Fo : fout (beff e) = rev (map snd (skipn k (bo e))) ++ rev (map snd (firstn k (bo e))))
    by (cbn; rewrite <- rev_app_distr, <- map_app, firstn_skipn; reflexivity).
  rewrite Fo, nread_up_b_sound by (rewrite length_skipn; unfold k; lia); reflexivity.
Qed.

Lemma nread_e_b_tok e t n : tok n (ta t) -> tok n (ta (nread_e_b F e t)).
Proof.
  destruct t as [z i d|u p]; cbn [nread_e_b]; [|auto]; intros Hn.
  destruct (N.leb d (bl e)); [apply nread_up_b_tok; exact Hn|exact Hn].
Qed.

(** *** Inputs related one to one *)

Definition irel (O : list lexp) (x : cU M) (a b : positive * (lexp * btgt)) : Prop :=
  fst (isnd a) = fst (isnd b) /\ tden O (snd (isnd a)) x = tden O (snd (isnd b)) x
  /\ forall n, tok n (snd (isnd b)) -> tok n (snd (isnd a)).

Lemma pushes_irel O x I I' b : Forall2 (irel O x) I' I -> pushes O (map isnd I') b x = pushes O (map isnd I) b x.
Proof.
  induction 1 as [|[i [l t]] [i' [l' t']] I I' [E1 [E2 _]] _ IH]; [reflexivity|]; cbn in *; subst; rewrite IH, E2; reflexivity.
Qed.

Lemma wfd_irel O x n I I' : Forall2 (irel O x) I' I -> Forall (fun lt => tok n (snd lt)) (map isnd I) ->
  Forall (fun lt => tok n (snd lt)) (map isnd I').
Proof.
  induction 1 as [|a b I I' [_ [_ E3]] _ IH]; cbn; [auto|]; intros H; inversion H; subst; constructor; auto.
Qed.

Lemma irel_refl O x a : irel O x a a.
Proof. split; [reflexivity|split; [reflexivity|auto]]. Qed.

Lemma Forall2_refl_irel O x I : Forall2 (irel O x) I I.
Proof. induction I; constructor; auto using irel_refl. Qed.

Lemma reread_front_b_rel e n x : N.to_nat (bl e) = length (bo e) -> Forall2 (irel (fout (beff e)) x) (bi (reread_front_b F n e)) (bi e).
Proof.
  intros H; unfold reread_front_b; cbn [bi]; generalize (bi e); induction n as [|n IH]; intros [|[i [l t]] I];
    cbn [map_front]; try apply Forall2_refl_irel; constructor; [|apply IH].
  unfold irel, isnd; cbn [snd]; rewrite !ina_pair; cbn [snd fst]; split; [reflexivity|split]; [apply nread_e_b_sound, H|].
  intros k Hk; apply nread_e_b_tok, Hk.
Qed.

Lemma reread_at_b_rel e j x : N.to_nat (bl e) = length (bo e) -> Forall2 (irel (fout (beff e)) x) (bi (reread_at_b F j e)) (bi e).
Proof.
  intros H; unfold reread_at_b; cbn [bi]; generalize (bi e); intros L; induction L as [|[i [l t]] I IH]; cbn [map]; constructor; auto.
  unfold irel, isnd; cbn [snd]; rewrite !ina_pair; cbn [snd fst]; split; [reflexivity|split]; destruct (bis_dep _ t); try reflexivity; try auto.
  - apply nread_e_b_sound, H.
  - intros k Hk; apply nread_e_b_tok, Hk.
Qed.

Lemma inputs_rel e I' x : Forall2 (irel (fout (beff e)) x) I' (bi e) ->
  fd (beff (mkB (bo e) (bl e) I')) x = fd (beff e) x.
Proof. intros R; unfold fden; cbn [beff fout fin bo bi]; apply pushes_irel, R. Qed.

Lemma inputs_ok e I' x : bok e -> Forall2 (irel (fout (beff e)) x) I' (bi e) -> bok (mkB (bo e) (bl e) I').
Proof.
  intros [H1 H2] R; split; [exact H1|]; unfold wfd in *; cbn [beff fout fin bo bi] in *.
  eapply wfd_irel; eassumption.
Qed.

(** *** Placing inputs *)

Lemma pushes_swap2 O (a c : positive * (lexp * btgt)) s b z : before F (blab c) (blab a) = true ->
  pushes O (map isnd (c :: a :: s)) b z = pushes O (map isnd (a :: c :: s)) b z.
Proof.
  destruct a as [i [l t]], c as [j [m u]]; unfold blab, isnd; cbn; intros B.
  apply (kd_push_push F M HM); apply bk; exact B.
Qed.

Lemma pushes_app_mid O (A s1 s2 : list (positive * (lexp * btgt))) b z :
  pushes O (map isnd s1) b z = pushes O (map isnd s2) b z ->
  pushes O (map isnd (A ++ s1)) b z = pushes O (map isnd (A ++ s2)) b z.
Proof. intros H; rewrite !map_app, !pushes_app, H; reflexivity. Qed.

Lemma pushes_cons_eq O (a : positive * (lexp * btgt)) (s1 s2 : list (positive * (lexp * btgt))) b z :
  (forall b, pushes O (map isnd s1) b z = pushes O (map isnd s2) b z) ->
  pushes O (map isnd (a :: s1)) b z = pushes O (map isnd (a :: s2)) b z.
Proof. destruct a as [i [l t]]; unfold isnd; cbn; intros H; rewrite H; reflexivity. Qed.

Lemma bub_in_b_sound O x I b z : pushes O (map isnd (bub_in_b F x I)) b z = pushes O (map isnd (x :: I)) b z
  /\ Permutation (bub_in_b F x I) (x :: I).
Proof.
  revert b; induction I as [|y I IH]; intros b; cbn [bub_in_b]; [split; reflexivity|].
  destruct (before F (blab y) (blab x)) eqn:B; [|split; reflexivity].
  split.
  - rewrite (pushes_cons_eq O y _ (x :: I) b z) by (intros b'; apply IH); apply pushes_swap2, B.
  - destruct (IH b) as [_ P]; rewrite P; apply perm_swap.
Qed.

Lemma place_front_b_sound O n I b z : pushes O (map isnd (place_front_b F n I)) b z = pushes O (map isnd I) b z
  /\ Permutation (place_front_b F n I) I.
Proof.
  revert I b; induction n as [|n IH]; intros [|x I] b; cbn [place_front_b]; try (split; reflexivity).
  destruct (bub_in_b_sound O x (place_front_b F n I) b z) as [E P]; rewrite E; split.
  - apply pushes_cons_eq; intros b'; apply IH.
  - rewrite P; apply perm_skip, IH; exact b.
Qed.

Lemma ins_out_b_sound O x rp s b z : pushes O (map isnd (rev (ins_out_b F x rp) ++ s)) b z = pushes O (map isnd (rev rp ++ x :: s)) b z
  /\ Permutation (ins_out_b F x rp) (x :: rp).
Proof.
  revert s; induction rp as [|y r IH]; intros s; cbn [ins_out_b]; [split; reflexivity|].
  destruct (before F (blab x) (blab y)) eqn:B; [|split; [cbn [rev]; rewrite <- !app_assoc; reflexivity|reflexivity]].
  split.
  - cbn [rev]; rewrite <- !app_assoc; cbn [app].
    rewrite (proj1 (IH (y :: s))); apply pushes_app_mid, pushes_swap2, B.
  - rewrite (proj2 (IH s)); apply perm_swap.
Qed.

Lemma out_pass_b_sound O rp suf b z : pushes O (map isnd (out_pass_b F rp suf)) b z = pushes O (map isnd (rev rp ++ suf)) b z
  /\ Permutation (out_pass_b F rp suf) (rev rp ++ suf).
Proof.
  revert rp; induction suf as [|x s IH]; intros rp; cbn [out_pass_b]; [rewrite rev'_rev, app_nil_r; split; reflexivity|].
  destruct (IH (ins_out_b F x rp)) as [E P]; destruct (ins_out_b_sound O x rp s b z) as [E2 P2]; split.
  - rewrite E, E2; reflexivity.
  - rewrite P, P2; cbn [rev]; rewrite <- app_assoc; reflexivity.
Qed.

Lemma place_suffix_out_b_sound O p I b z : pushes O (map isnd (place_suffix_out_b F p I)) b z = pushes O (map isnd I) b z
  /\ Permutation (place_suffix_out_b F p I) I.
Proof.
  unfold place_suffix_out_b; rewrite rev'_rev; destruct (out_pass_b_sound O (rev (firstn p I)) (skipn p I) b z) as [E P].
  rewrite rev_involutive, firstn_skipn in E, P; split; assumption.
Qed.

Lemma perm_inputs e I' x : (forall b, pushes (fout (beff e)) (map isnd I') b x = pushes (fout (beff e)) (map isnd (bi e)) b x) ->
  fd (beff (mkB (bo e) (bl e) I')) x = fd (beff e) x.
Proof. intros H; unfold fden; cbn [beff fout fin bo bi]; apply H. Qed.

Lemma perm_ok e I' : bok e -> Permutation I' (bi e) -> bok (mkB (bo e) (bl e) I').
Proof.
  intros [H1 H2] P; split; [exact H1|]; unfold wfd in *; cbn [beff fout fin bo bi] in *.
  rewrite Forall_forall in *; intros lt Hin; apply H2.
  apply (Permutation_in _ (Permutation_map isnd P)), Hin.
Qed.

(** *** Inputs as maps, for output swaps *)

Lemma dkey_b_inj d d' : dkey_b d = dkey_b d' -> d = d'.
Proof. unfold dkey_b; intros H; apply N.succ_inj; rewrite <- !N.succ_pos_spec, H; reflexivity. Qed.

Lemma ix_get_add ix d v d' : ix_get (PositiveMap.add (dkey_b d) v ix) d' = if N.eqb d d' then v else ix_get ix d'.
Proof.
  unfold ix_get; destruct (N.eqb_spec d d') as [<-|Ne].
  - rewrite PositiveMap.gss; reflexivity.
  - rewrite PositiveMap.gso; [reflexivity|]; intros K; apply Ne; symmetry; apply dkey_b_inj, K.
Qed.

Definition tdepth (t : btgt) : option N := match t with BR _ _ d => Some d | BT _ _ => None end.

(** Every read in range is listed at its depth. *)
Definition imok (r : imap) : Prop :=
  forall q x d, In q (pseq 1 (imn r)) -> PositiveMap.find q (imm r) = Some x -> tdepth (snd (snd x)) = Some d -> In q (ix_get (imx r) d).

Definition sok (s : istate) : Prop := match s with IL _ => True | IM r => imok r end.

Lemma pseq_le c n q : In q (pseq c n) -> (c <= q)%positive.
Proof.
  revert c; induction n as [|n IH]; intros c H; cbn in H; [contradiction|].
  destruct H as [<-|H]; [lia|specialize (IH _ H); lia].
Qed.

Lemma im_build_spec I : forall c m ix m' ix', im_build I c m ix = (m', ix') ->
  map (im_get m') (pseq c (length I)) = I
  /\ (forall q x d, In q (pseq c (length I)) -> PositiveMap.find q m' = Some x -> tdepth (snd (snd x)) = Some d -> In q (ix_get ix' d))
  /\ (forall q, ~ In q (pseq c (length I)) -> PositiveMap.find q m' = PositiveMap.find q m)
  /\ (forall d, incl (ix_get ix d) (ix_get ix' d)).
Proof.
  induction I as [|y I IH]; intros c m ix m' ix' E; cbn [im_build] in E.
  - injection E as <- <-; cbn; split; [reflexivity|split; [intros; contradiction|split; [reflexivity|intros; apply incl_refl]]].
  - set (ix1 := match snd (snd y) with BR _ _ d => PositiveMap.add (dkey_b d) (c :: ix_get ix d) ix | BT _ _ => ix end) in E.
    destruct (IH _ _ _ _ _ E) as [A [B [C D]]].
    assert (Nc : ~ In c (pseq (Pos.succ c) (length I))) by (intros H; apply pseq_le in H; lia).
    assert (Fc : PositiveMap.find c m' = Some y) by (rewrite C by exact Nc; apply PositiveMap.gss).
    assert (D1 : forall d, incl (ix_get ix d) (ix_get ix1 d)).
    { intros d; unfold ix1; destruct y as [i [l [z j e|u p]]]; cbn [snd]; [|apply incl_refl].
      rewrite ix_get_add; destruct (N.eqb e d) eqn:Ed; [apply N.eqb_eq in Ed; subst; intros w Hw; right; exact Hw|apply incl_refl]. }
    split; [cbn [length pseq map]; unfold im_get at 1; rewrite Fc, A; reflexivity|].
    split; [|split].
    + intros q x d Hq Fq Dq; cbn [length pseq] in Hq; destruct Hq as [<-|Hq]; [|exact (B q x d Hq Fq Dq)].
      rewrite Fc in Fq; injection Fq as <-; apply D; unfold ix1.
      destruct y as [i [l [z j e|u p]]]; cbn [snd tdepth] in Dq |- *; [|discriminate].
      injection Dq as <-; rewrite ix_get_add, N.eqb_refl; left; reflexivity.
    + intros q Hq; cbn [length pseq] in Hq; rewrite C by (intros H; apply Hq; right; exact H).
      apply PositiveMap.gso; intros <-; apply Hq; left; reflexivity.
    + intros d; eapply incl_tran; [apply D1|apply D].
Qed.

Lemma to_im_spec s : sok s -> im_list (to_im s) = ins s /\ imok (to_im s).
Proof.
  destruct s as [I|r]; cbn [to_im ins sok]; [intros _|intros H; split; [reflexivity|exact H]].
  destruct (im_build I 1 (PositiveMap.empty _) (PositiveMap.empty _)) as [m ix] eqn:E.
  destruct (im_build_spec I _ _ _ _ _ E) as [A [B _]]; split; [exact A|].
  intros q x d Hq Fq Dq; exact (B q x d Hq Fq Dq).
Qed.

Definition swp (k : N) (b : lexp) (x : positive * (lexp * btgt)) : option (positive * (lexp * btgt)) :=
  let '(id, (l, t)) := x in option_map (fun t' => (id, (l, t'))) (bswap_read F k b t).

Lemma bswap_read_idem k b t t' : bswap_read F k b t = Some t' -> bswap_read F k b t' = Some t'.
Proof.
  destruct t as [z i d|u p]; cbn [bswap_read]; [|intros H; injection H as <-; reflexivity].
  destruct (N.eqb_spec d (N.succ k)) as [->|Ne].
  - assert (Ne2 : N.eqb (N.succ (N.succ k)) (N.succ k) = false) by (apply N.eqb_neq; lia).
    destruct (lexp_eqb z b); [destruct i; [discriminate|]|destruct (kd F z b); [|discriminate]];
      intros H; injection H as <-; cbn [bswap_read]; rewrite Ne2; reflexivity.
  - intros H; injection H as <-; cbn [bswap_read]; replace (N.eqb d (N.succ k)) with false by (symmetry; apply N.eqb_neq; exact Ne); reflexivity.
Qed.

Lemma swp_idem k b x x' : swp k b x = Some x' -> swp k b x' = Some x'.
Proof.
  destruct x as [id [l t]]; cbn [swp]; destruct (bswap_read F k b t) as [t'|] eqn:G; cbn [option_map]; [|discriminate].
  intros H; injection H as <-; cbn [swp]; rewrite (bswap_read_idem _ _ _ _ G); reflexivity.
Qed.

Lemma upd_keys_spec k b ks : forall m m', upd_keys F k b ks m = Some m' -> forall q,
  (PositiveMap.find q m = None -> PositiveMap.find q m' = None)
  /\ (forall x, PositiveMap.find q m = Some x -> exists x', PositiveMap.find q m' = Some x'
        /\ (if in_dec Pos.eq_dec q ks then swp k b x = Some x' else x' = x)).
Proof.
  induction ks as [|q0 ks IH]; intros m m' E q; cbn [upd_keys] in E.
  - injection E as <-; split; [auto|intros x Fx; exists x; split; [exact Fx|reflexivity]].
  - destruct (PositiveMap.find q0 m) as [[id [l t]]|] eqn:F0.
    + destruct (bswap_read F k b t) as [t1|] eqn:G; [|discriminate].
      destruct (IH _ _ E q) as [I1 I2]; split.
      * intros Fq; apply I1; rewrite PositiveMap.gso; [exact Fq|intros ->; congruence].
      * intros x Fx; destruct (Pos.eq_dec q q0) as [->|Nq].
        -- rewrite F0 in Fx; injection Fx as <-.
           destruct (I2 (id, (l, t1)) (PositiveMap.gss _ _ _)) as [x' [F' Hx']]; exists x'; split; [exact F'|].
           destruct (in_dec Pos.eq_dec q0 (q0 :: ks)) as [_|Nn]; [|exfalso; apply Nn; left; reflexivity].
           assert (S1 : swp k b (id, (l, t)) = Some (id, (l, t1))) by (cbn [swp]; rewrite G; reflexivity).
           destruct (in_dec Pos.eq_dec q0 ks); [|subst x'; exact S1].
           rewrite S1; rewrite (swp_idem _ _ _ _ S1) in Hx'; exact Hx'.
        -- destruct (I2 x) as [x' [F' Hx']]; [rewrite PositiveMap.gso by exact Nq; exact Fx|].
           exists x'; split; [exact F'|].
           destruct (in_dec Pos.eq_dec q ks) as [Hi|Hn]; destruct (in_dec Pos.eq_dec q (q0 :: ks)) as [Hi'|Hn'];
             [exact Hx'|exfalso; apply Hn'; right; exact Hi|destruct Hi' as [E'|Hi']; [congruence|contradiction]|exact Hx'].
    + destruct (IH _ _ E q) as [I1 I2]; split; [exact I1|].
      intros x Fx; destruct (I2 x Fx) as [x' [F' Hx']]; exists x'; split; [exact F'|].
      destruct (Pos.eq_dec q q0) as [->|Nq]; [congruence|].
      destruct (in_dec Pos.eq_dec q ks) as [Hi|Hn]; destruct (in_dec Pos.eq_dec q (q0 :: ks)) as [Hi'|Hn'];
        [exact Hx'|exfalso; apply Hn'; right; exact Hi|destruct Hi' as [E'|Hi']; [congruence|contradiction]|exact Hx'].
Qed.

Lemma swp_other k b x : tdepth (snd (snd x)) <> Some (N.succ k) -> swp k b x = Some x.
Proof.
  destruct x as [id [l [z i d|u p]]]; cbn [swp bswap_read snd tdepth]; intros H; [|reflexivity].
  replace (N.eqb d (N.succ k)) with false by (symmetry; apply N.eqb_neq; intros ->; apply H; reflexivity); reflexivity.
Qed.

Lemma swap_in_map k b (g g' : positive -> positive * (lexp * btgt)) keys :
  (forall q, In q keys -> swp k b (g q) = Some (g' q)) -> swap_in_b F k b (map g keys) = Some (map g' keys).
Proof.
  unfold swap_in_b; induction keys as [|q keys IH]; intros H; [reflexivity|]; cbn [map omap].
  specialize (H q (or_introl eq_refl)) as Hq; destruct (g q) as [id [l t]]; cbn [swp] in Hq.
  destruct (bswap_read F k b t) as [t'|]; cbn [option_map] in *; [|discriminate]; injection Hq as <-.
  rewrite IH by (intros q' Hq'; apply H; right; exact Hq'); reflexivity.
Qed.

Lemma in_rev_app_l {X} (a : X) l1 l2 : In a l1 -> In a (rev_append l1 l2).
Proof. rewrite rev_append_rev; intros H; apply in_or_app; left; apply in_rev in H; exact H. Qed.

Lemma in_rev_app_r {X} (a : X) l1 l2 : In a l2 -> In a (rev_append l1 l2).
Proof. rewrite rev_append_rev; intros H; apply in_or_app; right; exact H. Qed.

Lemma sswap_spec k b r r' : imok r -> sswap F k b r = Some r' ->
  swap_in_b F k b (im_list r) = Some (im_list r') /\ imok r' /\ imn r' = imn r.
Proof.
  intros Ok; unfold sswap; set (ks := ix_get (imx r) (N.succ k)).
  destruct (upd_keys F k b ks (imm r)) as [m'|] eqn:U; [|discriminate]; intros H; injection H as <-.
  pose proof (upd_keys_spec k b ks _ _ U) as US.
  split; [|split; [|reflexivity]].
  - unfold im_list; cbn [imm imn]; apply swap_in_map; intros q Hq.
    destruct (US q) as [U1 U2]; unfold im_get.
    destruct (PositiveMap.find q (imm r)) as [x|] eqn:Fx.
    + destruct (U2 x eq_refl) as [x' [F' Hx']]; rewrite F'.
      destruct (in_dec Pos.eq_dec q ks) as [_|Nk]; [exact Hx'|subst x'; apply swp_other].
      intros D; apply Nk, (Ok q x _ Hq Fx D).
    + rewrite (U1 eq_refl); reflexivity.
  - intros q x' d Hq F' D; cbn [imm imx imn] in *.
    destruct (US q) as [U1 U2]; destruct (PositiveMap.find q (imm r)) as [x|] eqn:Fx; [|rewrite (U1 eq_refl) in F'; discriminate].
    destruct (U2 x eq_refl) as [x'' [F'' Hx]]; rewrite F' in F''; injection F'' as <-.
    rewrite !ix_get_add.
    assert (Ix : forall d0, tdepth (snd (snd x)) = Some d0 -> In q (ix_get (imx r) d0)) by (intros d0 D0; exact (Ok q x d0 Hq Fx D0)).
    destruct (in_dec Pos.eq_dec q ks) as [Hk|Nk].
    + destruct x as [id [l [z i e|u p]]]; cbn [swp bswap_read] in Hx; [|injection Hx as <-; discriminate].
      destruct (N.eqb_spec e (N.succ k)) as [->|Ne].
      * assert (Hd : d = N.succ (N.succ k)).
        { destruct (lexp_eqb z b); [destruct i; [discriminate|]|destruct (kd F z b); [|discriminate]];
            injection Hx as <-; cbn [snd tdepth] in D; injection D as <-; reflexivity. }
        subst d; rewrite (proj2 (N.eqb_neq (N.succ k) (N.succ (N.succ k))) ltac:(lia)), N.eqb_refl.
        apply in_rev_app_l, Hk.
      * injection Hx as <-; cbn [snd tdepth] in D; injection D as <-.
        rewrite (proj2 (N.eqb_neq _ _) (fun H => Ne (eq_sym H))).
        destruct (N.eqb_spec (N.succ (N.succ k)) e) as [<-|_]; [apply in_rev_app_r, (Ix _ eq_refl)|exact (Ix _ eq_refl)].
    + subst x'; assert (Dn : d <> N.succ k) by (intros ->; apply Nk, (Ix _ D)).
      rewrite (proj2 (N.eqb_neq _ _) (fun H => Dn (eq_sym H))).
      destruct (N.eqb_spec (N.succ (N.succ k)) d) as [<-|_]; [apply in_rev_app_r, (Ix _ D)|exact (Ix _ D)].
Qed.

Lemma isnd_eq i l t : isnd (i, (l, t)) = (l, ta t).
Proof. reflexivity. Qed.

Lemma tag_pushes (g : btgt -> option btgt) O O' I I' b x x' :
  omap (fun '(id, (l, t)) => option_map (fun t' => (id, (l, t'))) (g t)) I = Some I' ->
  (forall t t', g t = Some t' -> tden O' (ta t') x' = tden O (ta t) x) ->
  pushes O' (map isnd I') b x' = pushes O (map isnd I) b x.
Proof.
  revert I'; induction I as [|[i [h t]] I IH]; intros I' E H; cbn in E.
  - injection E as <-; reflexivity.
  - destruct (g t) as [t'|] eqn:G; cbn in E; [|discriminate].
    destruct (omap _ I) as [I''|] eqn:E2; [|discriminate]; injection E as <-.
    cbn [map]; rewrite !isnd_eq; cbn [pushes]; rewrite (H t t' G), (IH I'' eq_refl H); reflexivity.
Qed.

Lemma swap_in_tok k b I I' n : swap_in_b F k b I = Some I' -> N.to_nat k + 2 <= n ->
  Forall (fun lt => tok n (snd lt)) (map isnd I) -> Forall (fun lt => tok n (snd lt)) (map isnd I').
Proof.
  unfold swap_in_b; revert I'; induction I as [|[i [l t]] I IH]; intros I' E Hn H; cbn [omap map] in *.
  - injection E as <-; constructor.
  - inversion H as [|a b0 H1 H2]; subst.
    destruct (bswap_read F k b t) as [t'|] eqn:Sw; cbn in *; [|discriminate].
    destruct (omap _ I) as [I''|]; [|discriminate]; injection E as <-; cbn; constructor; [|apply IH; auto].
    cbn [isnd ina snd fst] in H1 |- *; destruct t as [z j d|u p]; cbn in Sw, H1 |- *.
    + destruct (N.eqb d (N.succ k)); [destruct (lexp_eqb z b); [destruct j|destruct (kd F z b)]|]; try discriminate;
        injection Sw as <-; cbn; rewrite ?N2Nat.inj_succ; lia.
    + injection Sw as <-; exact Logic.I.
Qed.

(** One output swap. *)
Lemma boswap_step (top bot : list lexp) a c I I' z :
  before F c a = true -> swap_in_b F (N.of_nat (length top)) c I = Some I' ->
  fd (mkF (top ++ c :: a :: bot) (map isnd I')) z = fd (mkF (top ++ a :: c :: bot) (map isnd I)) z.
Proof.
  intros Bf Sw.
  assert (D : known_distinct F a c) by (apply known_distinct_sym, bk, Bf).
  unfold fden; cbn [fout fin]; rewrite !length_app; cbn [length].
  rewrite !popn_mid, (pop_comm c a) by (apply known_distinct_sym; exact D).
  apply (tag_pushes _ _ _ I I' _ _ _ Sw).
  intros t t' Sw1; destruct t as [z0 i d|u p]; cbn [bswap_read] in Sw1; [|injection Sw1 as <-; reflexivity].
  rewrite Neqb_nat, N2Nat.inj_succ, Nat2N.id in Sw1.
  destruct (Nat.eqb (N.to_nat d) (S (length top))) eqn:Ed.
  - apply Nat.eqb_eq in Ed.
    assert (P1 : popn (top ++ a :: c :: bot) (N.to_nat d) z = cpop a (popn top (length top) z)).
    { rewrite Ed; replace (S (length top)) with (length top + S 0) by lia; rewrite popn_at, popn_0; reflexivity. }
    assert (P2 : popn (top ++ c :: a :: bot) (S (S (length top))) z = cpop a (cpop c (popn top (length top) z))).
    { replace (S (S (length top))) with (length top + S (S 0)) by lia; rewrite popn_mid, popn_0; reflexivity. }
    destruct (lexp_eqb z0 c) eqn:Ez.
    + apply lexp_eqb_true in Ez; subst z0; destruct i as [|q]; [discriminate|]; injection Sw1 as <-; cbn [tden ta].
      change (Pos.pred_N q) with (N.pred (N.pos q)); destruct (Npos_succ q) as [m [H1 H2]].
      rewrite H1, H2, !N2Nat.inj_succ, Nat2N.id, P1, P2, (pop_comm a c _ D), (cname_pop M); reflexivity.
    + destruct (kd F z0 c) eqn:K; [|discriminate]; injection Sw1 as <-; cbn [tden ta].
      rewrite !N2Nat.inj_succ, Nat2N.id, P1, P2, (pop_comm a c _ D), cname_pop_other by (apply kdk, K); reflexivity.
  - injection Sw1 as <-; cbn [tden ta]; apply Nat.eqb_neq in Ed.
    destruct (Nat.le_gt_cases (N.to_nat d) (length top)) as [Le|Gt].
    + rewrite !popn_len_le by exact Le; reflexivity.
    + replace (N.to_nat d) with (length top + S (S (N.to_nat d - length top - 2))) by lia.
      rewrite !popn_mid, (pop_comm a c _ D); reflexivity.
Qed.

Definition itok (n : nat) (I : list (positive * (lexp * btgt))) : Prop := Forall (fun lt => tok n (snd lt)) (map isnd I).

Lemma rev_mid (below acc : list (positive * lexp)) y x :
  rev (map snd (below ++ y :: x :: acc)) = rev (map snd acc) ++ snd x :: snd y :: rev (map snd below).
Proof. rewrite map_app, rev_app_distr; cbn; rewrite <- !app_assoc; reflexivity. Qed.

(** *** Outputs moved up from the bottom *)

Lemma bub_out_b_sound x acc : forall below pos s r s' n,
  bub_out_b F x acc pos s = (r, s') -> N.to_nat pos = length acc -> n = length below + S (length acc) ->
  sok s -> itok n (ins s) ->
  (forall z, fd (mkF (rev (map snd (below ++ r))) (map isnd (ins s'))) z = fd (mkF (rev (map snd (below ++ x :: acc))) (map isnd (ins s))) z)
  /\ sok s' /\ length r = S (length acc) /\ itok n (ins s').
Proof.
  induction acc as [|y acc IH]; intros below pos s r s' n E Hp Hn Hi Ht; cbn [bub_out_b] in E.
  - injection E as <- <-; auto.
  - destruct (before F (snd x) (snd y)) eqn:B; [|injection E as <- <-; auto].
    destruct (to_im_spec s Hi) as [Ti Tok].
    cbn [length] in Hp.
    assert (Hp' : N.to_nat (N.pred pos) = length acc) by (rewrite N2Nat.inj_pred; lia).
    assert (Ek : N.pred pos = N.of_nat (length (rev (map snd acc)))) by (rewrite length_rev, length_map, <- Hp', N2Nat.id; reflexivity).
    destruct (sswap F (N.pred pos) (snd x) (to_im s)) as [r1|] eqn:Sw.
    + destruct (sswap_spec _ _ _ _ Tok Sw) as [Sw' [Ok1 _]]; rewrite Ti in Sw'.
      destruct (bub_out_b F x acc (N.pred pos) (IM r1)) as [r0 s0] eqn:E0; injection E as <- <-.
      destruct (IH (below ++ [y]) (N.pred pos) (IM r1) r0 s0 n E0 Hp') as [S1 [S2 [S3 S4]]];
        [rewrite length_app; cbn in *; lia|exact Ok1|apply (swap_in_tok _ _ _ _ _ Sw'); [cbn in Hn; lia|exact Ht]|].
      split; [|split; [exact S2|split; [cbn; lia|exact S4]]]; intros z.
      replace (below ++ y :: r0) with ((below ++ [y]) ++ r0) by (rewrite <- app_assoc; reflexivity); rewrite S1.
      replace ((below ++ [y]) ++ x :: acc) with (below ++ y :: x :: acc) by (rewrite <- app_assoc; reflexivity).
      rewrite !rev_mid; apply boswap_step; [exact B|]; rewrite <- Ek; exact Sw'.
    + injection E as <- <-; cbn [ins sok]; rewrite Ti; split; [reflexivity|split; [exact Tok|auto]].
Qed.

Lemma place_rng_b_sound rng : forall k n above below s o s',
  place_rng_b F k n rng above s = (o, s') -> N.to_nat k = length below -> N.to_nat n = N.to_nat k + length rng + length above ->
  sok s -> itok (N.to_nat n) (ins s) ->
  (forall z, fd (mkF (rev (map snd (below ++ o))) (map isnd (ins s'))) z = fd (mkF (rev (map snd (below ++ rng ++ above))) (map isnd (ins s))) z)
  /\ sok s' /\ length o = length rng + length above /\ itok (N.to_nat n) (ins s').
Proof.
  induction rng as [|x rng IH]; intros k n above below s o s' E Hk Hn Hi Ht; cbn [place_rng_b] in E.
  - injection E as <- <-; auto.
  - destruct (place_rng_b F (N.succ k) n rng above s) as [a' s1] eqn:E1.
    destruct (IH (N.succ k) n above (below ++ [x]) s a' s1 E1) as [S1 [S2 [S3 S4]]];
      [rewrite length_app; cbn; lia|cbn in Hn; lia|exact Hi|exact Ht|].
    destruct (bub_out_b_sound x a' below (n - 1 - k) s1 o s' (N.to_nat n) E) as [T1 [T2 [T3 T4]]];
      [rewrite S3; cbn in Hn; lia|rewrite S3; cbn in Hn; lia|exact S2|exact S4|].
    split; [|split; [exact T2|split; [rewrite T3, S3; reflexivity|exact T4]]]; intros z.
    rewrite T1; replace (below ++ x :: a') with ((below ++ [x]) ++ a') by (rewrite <- app_assoc; reflexivity).
    rewrite S1, <- app_assoc; reflexivity.
Qed.

Lemma place_out_bottom_b_sound r e : bok e ->
  (forall z, fd (beff (place_out_bottom_b F r e)) z = fd (beff e) z) /\ bok (place_out_bottom_b F r e).
Proof.
  intros [H1 H2]; unfold place_out_bottom_b.
  destruct (place_rng_b F 0 (bl e) (firstn r (bo e)) (skipn r (bo e)) (IL (bi e))) as [o s] eqn:E.
  destruct (place_rng_b_sound _ 0 (bl e) _ [] _ _ _ E eq_refl) as [S1 [_ [S3 S4]]];
    [rewrite length_firstn, length_skipn, H1; cbn; lia|exact Logic.I|unfold itok; unfold wfd in H2; rewrite beff_len in H2; rewrite H1; exact H2|].
  split; [intros z; specialize (S1 z); cbn [app ins] in S1; rewrite firstn_skipn in S1; exact S1|split; cbn [bl bo]].
  - rewrite S3, <- length_app, firstn_skipn; exact H1.
  - unfold wfd; rewrite beff_len; cbn [bo bi]; rewrite S3, <- length_app, firstn_skipn, <- H1; exact S4.
Qed.

(** *** Outputs moved down from the top *)

Lemma bub_down_b_sound x below : forall above pos s r s' n,
  bub_down_b F x below pos s = (r, s') -> N.to_nat pos = length above -> n = length above + S (length below) ->
  sok s -> itok n (ins s) ->
  (forall z, fd (mkF (map snd (above ++ r)) (map isnd (ins s'))) z = fd (mkF (map snd (above ++ x :: below)) (map isnd (ins s))) z)
  /\ sok s' /\ length r = S (length below) /\ itok n (ins s').
Proof.
  induction below as [|y below IH]; intros above pos s r s' n E Hp Hn Hi Ht; cbn [bub_down_b] in E.
  - injection E as <- <-; auto.
  - destruct (before F (snd y) (snd x)) eqn:B; [|injection E as <- <-; auto].
    destruct (to_im_spec s Hi) as [Ti Tok].
    assert (Ek : pos = N.of_nat (length (map snd above))) by (rewrite length_map, <- Hp, N2Nat.id; reflexivity).
    assert (L : forall r0, map snd (above ++ y :: r0) = map snd (above ++ [y]) ++ map snd r0)
      by (intros; rewrite <- map_app, <- app_assoc; reflexivity).
    assert (L2 : map snd (above ++ x :: y :: below) = map snd above ++ snd x :: snd y :: map snd below)
      by (rewrite map_app; reflexivity).
    assert (L3 : map snd ((above ++ [y]) ++ x :: below) = map snd above ++ snd y :: snd x :: map snd below)
      by (rewrite <- app_assoc, map_app; reflexivity).
    destruct (sswap F pos (snd y) (to_im s)) as [r1|] eqn:Sw.
    + destruct (sswap_spec _ _ _ _ Tok Sw) as [Sw' [Ok1 _]]; rewrite Ti in Sw'.
      destruct (bub_down_b F x below (N.succ pos) (IM r1)) as [r0 s0] eqn:E0; injection E as <- <-.
      destruct (IH (above ++ [y]) (N.succ pos) (IM r1) r0 s0 n E0) as [S1 [S2 [S3 S4]]];
        [rewrite N2Nat.inj_succ, length_app; cbn; lia|rewrite length_app; cbn in *; lia|exact Ok1|
         apply (swap_in_tok _ _ _ _ _ Sw'); [cbn in Hn; lia|exact Ht]|].
      split; [|split; [exact S2|split; [cbn; lia|exact S4]]]; intros z.
      rewrite L, <- map_app, S1, L3, L2.
      apply boswap_step; [exact B|]; rewrite <- Ek; exact Sw'.
    + injection E as <- <-; cbn [ins sok]; rewrite Ti; split; [reflexivity|split; [exact Tok|auto]].
Qed.

Lemma place_down_b_sound pre : forall k rest above s o s' n,
  place_down_b F k pre rest s = (o, s') -> N.to_nat k = length above -> n = N.to_nat k + length pre + length rest ->
  sok s -> itok n (ins s) ->
  (forall z, fd (mkF (map snd (above ++ o)) (map isnd (ins s'))) z = fd (mkF (map snd (above ++ pre ++ rest)) (map isnd (ins s))) z)
  /\ sok s' /\ length o = length pre + length rest /\ itok n (ins s').
Proof.
  induction pre as [|x pre IH]; intros k rest above s o s' n E Hk Hn Hi Ht; cbn [place_down_b] in E.
  - injection E as <- <-; auto.
  - destruct (place_down_b F (N.succ k) pre rest s) as [r' s1] eqn:E1.
    destruct (IH (N.succ k) rest (above ++ [x]) s r' s1 n E1) as [S1 [S2 [S3 S4]]];
      [rewrite N2Nat.inj_succ, length_app; cbn; lia|rewrite N2Nat.inj_succ; cbn in Hn; lia|exact Hi|exact Ht|].
    destruct (bub_down_b_sound x r' above k s1 o s' n E) as [T1 [T2 [T3 T4]]];
      [exact Hk|rewrite S3; cbn in Hn; lia|exact S2|exact S4|].
    split; [|split; [exact T2|split; [rewrite T3, S3; reflexivity|exact T4]]]; intros z.
    rewrite T1; replace (above ++ x :: r') with ((above ++ [x]) ++ r') by (rewrite <- app_assoc; reflexivity).
    rewrite S1, <- app_assoc; reflexivity.
Qed.

Lemma place_out_top_b_sound r e : bok e ->
  (forall z, fd (beff (place_out_top_b F r e)) z = fd (beff e) z) /\ bok (place_out_top_b F r e).
Proof.
  intros [H1 H2]; unfold place_out_top_b; rewrite !rev'_rev.
  destruct (place_down_b F 0 (firstn r (rev (bo e))) (skipn r (rev (bo e))) (IL (bi e))) as [o s] eqn:E.
  destruct (place_down_b_sound _ 0 _ [] _ _ _ (N.to_nat (bl e)) E eq_refl) as [S1 [_ [S3 S4]]];
    [rewrite length_firstn, length_skipn, length_rev, H1; cbn; lia|exact Logic.I|unfold itok; unfold wfd in H2; rewrite beff_len in H2; rewrite H1; exact H2|].
  assert (Lo : length o = length (bo e)) by (rewrite S3, <- length_app, firstn_skipn, length_rev; reflexivity).
  rewrite rev'_rev; split.
  - intros z; specialize (S1 z); cbn [app ins] in S1; rewrite firstn_skipn in S1.
    unfold beff; cbn [bo bi bl fout fin]; rewrite map_rev, rev_involutive, S1, map_rev; reflexivity.
  - unfold bok; cbn [bl bo]; split; [rewrite length_rev, Lo; exact H1|].
    unfold wfd, beff; cbn [fout fin bo bi]; rewrite map_rev, rev_involutive, length_map, Lo, <- H1; exact S4.
Qed.

(** *** Composing *)

Lemma popin_b_sound o rem O b x :
  (forall rem', popin_b F o rem = Some (Some rem') -> cpop o (pushes O (map isnd rem) b x) = pushes O (map isnd rem') b x)
  /\ (popin_b F o rem = Some None -> cpop o (pushes O (map isnd rem) b x) = pushes O (map isnd rem) (cpop o b) x).
Proof.
  induction rem as [|[i [l t]] rem IH]; cbn [popin_b]; [split; [discriminate|reflexivity]|].
  unfold blab; cbn [fst snd]; destruct (lexp_eqb l o) eqn:E.
  - apply lexp_eqb_true in E; subst l; split; [intros rem' H; injection H as <-; cbn [map]; rewrite isnd_eq; cbn [pushes]; apply cpop_push|discriminate].
  - destruct (kd F l o) eqn:K; [|split; discriminate].
    assert (D : known_distinct F o l) by (apply known_distinct_sym, kdk, K).
    destruct IH as [IH1 IH2]; destruct (popin_b F o rem) as [[rem'|]|]; [| |split; discriminate].
    + split; [|discriminate]; intros r H; injection H as <-; cbn [map]; rewrite !isnd_eq; cbn [pushes].
      rewrite (kd_pop_push F M HM o l D), (IH1 rem' eq_refl); reflexivity.
    + split; [discriminate|intros _]; cbn [map]; rewrite isnd_eq; cbn [pushes]; rewrite (kd_pop_push F M HM o l D), IH2 by reflexivity; reflexivity.
Qed.

Lemma popin_b_incl o rem rem' : popin_b F o rem = Some (Some rem') -> incl rem' rem.
Proof.
  revert rem'; induction rem as [|x rem IH]; intros rem' P; cbn [popin_b] in P; [discriminate|].
  destruct (lexp_eqb (blab x) o); [injection P as <-; intros z Hz; right; exact Hz|].
  destruct (kd F (blab x) o); [|discriminate].
  destruct (popin_b F o rem) as [[r'|]|]; try discriminate; injection P as <-.
  intros z [Hz|Hz]; [left; exact Hz|right; apply (IH r' eq_refl), Hz].
Qed.

Lemma rthrough_b_sound rem z i O b x :
  (forall t, rthrough_b F rem z i = Some (inl t) -> cname z (N.to_nat i) (pushes O (map isnd rem) b x) = tden O (ta t) x)
  /\ (forall i', rthrough_b F rem z i = Some (inr i') -> cname z (N.to_nat i) (pushes O (map isnd rem) b x) = cname z (N.to_nat i') b).
Proof.
  revert i; induction rem as [|[j [l t]] rem IH]; intros i; cbn [rthrough_b map]; [split; [discriminate|intros i' H; injection H as <-; reflexivity]|].
  rewrite isnd_eq; cbn [pushes]; destruct (lexp_eqb l z) eqn:E.
  - apply lexp_eqb_true in E; subst l; destruct i as [|q].
    + split; [intros t' H; injection H as <-; apply (cname_push0 M)|discriminate].
    + destruct (Npos_succ q) as [m [H1 H2]]; rewrite H1, (cname_push M), <- H2; apply IH.
  - destruct (kd F l z) eqn:K; [|split; discriminate].
    rewrite cname_push_other by (apply known_distinct_sym, kdk, K); apply IH.
Qed.

Lemma rthrough_b_in rem z i t : rthrough_b F rem z i = Some (inl t) -> exists j l, In (j, (l, t)) rem.
Proof.
  revert i; induction rem as [|[j [l s]] rem IH]; intros i; cbn [rthrough_b]; [discriminate|].
  destruct (lexp_eqb l z); [destruct i; [intros H; injection H as <-; exists j, l; left; reflexivity|]|];
    [| destruct (kd F l z); [|discriminate]]; intros H; destruct (IH _ H) as [j' [l' Hl]]; exists j', l'; right; exact Hl.
Qed.

Definition d0 : list (positive * (lexp * btgt)) * (list (positive * lexp) * N) := ([], ([], 0%N)).

Lemma popall_b_struct O1 : forall rem pr np c st c', popall_b F O1 rem pr np c = Some (st, c') -> np = N.of_nat (length pr) ->
  st <> []
  /\ (forall d r p n, nth_error st d = Some (r, (p, n)) ->
        incl r rem /\ length pr <= length p /\ length p <= length (fst (snd (last st d0))) /\ n = N.of_nat (length p))
  /\ incl (fst (last st d0)) rem /\ length pr <= length (fst (snd (last st d0)))
  /\ snd (snd (last st d0)) = N.of_nat (length (fst (snd (last st d0)))).
Proof.
  induction O1 as [|[y o] O1 IH]; intros rem pr np c st c' E Hn; cbn [popall_b] in E.
  - injection E as <- <-; cbn; split; [discriminate|split; [|split; [apply incl_refl|split; [lia|exact Hn]]]].
    intros [|d] r p n N; cbn in N; [injection N as <- <- <-; split; [apply incl_refl|split; [lia|split; [lia|exact Hn]]]|destruct d; discriminate].
  - destruct (popin_b F o rem) as [[rem'|]|] eqn:P; [| |discriminate].
    + destruct (popall_b F O1 rem' pr np true) as [[st0 c0]|] eqn:E0; cbn in E; [|discriminate]; injection E as <- <-.
      destruct (IH _ _ _ _ _ _ E0 Hn) as [Ne [B [C [D G]]]].
      pose proof (popin_b_incl _ _ _ P) as Inc.
      assert (Lst : last ((rem, (pr, np)) :: st0) d0 = last st0 d0) by (destruct st0; [contradiction|reflexivity]).
      split; [discriminate|]; rewrite Lst; split; [|split; [intros z Hz; apply Inc, C, Hz|split; [exact D|exact G]]].
      intros [|d] r p n N; cbn [nth_error] in N.
      * injection N as <- <- <-; split; [apply incl_refl|split; [lia|split; [exact D|exact Hn]]].
      * destruct (B d r p n N) as [B1 [B2 [B3 B4]]]; split; [intros z Hz; apply Inc, B1, Hz|split; [lia|split; [exact B3|exact B4]]].
    + destruct (popall_b F O1 rem ((y, o) :: pr) (N.succ np) c) as [[st0 c0]|] eqn:E0; cbn in E; [|discriminate]; injection E as <- <-.
      destruct (IH _ _ _ _ _ _ E0) as [Ne [B [C [D G]]]]; [cbn [length]; rewrite Nat2N.inj_succ, Hn; reflexivity|].
      assert (Lst : last ((rem, (pr, np)) :: st0) d0 = last st0 d0) by (destruct st0; [contradiction|reflexivity]).
      cbn [length] in B, D.
      split; [discriminate|]; rewrite Lst; split; [|split; [exact C|split; [lia|exact G]]].
      intros [|d] r p n N; cbn [nth_error] in N.
      * injection N as <- <- <-; split; [apply incl_refl|split; [lia|split; [lia|exact Hn]]].
      * destruct (B d r p n N) as [B1 [B2 [B3 B4]]]; split; [exact B1|split; [lia|split; [exact B3|exact B4]]].
Qed.

Lemma popall_b_spec O1 : forall rem pr np c st c', popall_b F O1 rem pr np c = Some (st, c') ->
  length st = S (length O1)
  /\ exists Pf, map snd (rev (fst (snd (last st d0)))) = map snd (rev pr) ++ Pf
  /\ forall O x n0, length pr + length Pf + n0 <= length O ->
       (forall k, k < length pr + length Pf -> nth (n0 + k) O LNone = nth k (map snd (rev pr) ++ Pf) LNone) ->
       forall d, d <= length O1 -> exists r p n, nth_error st d = Some (r, (p, n))
         /\ popn (map snd O1) d (pushes O (map isnd rem) (popn O (n0 + length pr) x) x)
            = pushes O (map isnd r) (popn O (n0 + length p) x) x.
Proof.
  induction O1 as [|[y o] O1 IH]; intros rem pr np c st c' H; cbn [popall_b] in H.
  - injection H as <- _; split; [reflexivity|]; exists []; rewrite app_nil_r; split; [reflexivity|].
    intros O x n0 _ _ d Hd; cbn in Hd; assert (d = 0) as -> by lia; exists rem, pr, np; split; [reflexivity|].
    rewrite popn_0; reflexivity.
  - destruct (popin_b F o rem) as [[rem'|]|] eqn:P; [| |discriminate].
    + destruct (popall_b F O1 rem' pr np true) as [[st'' c'']|] eqn:E; cbn in H; [|discriminate]; injection H as <- _.
      destruct (IH _ _ _ _ _ _ E) as [L [Pf [Last S]]]; split; [cbn; rewrite L; reflexivity|].
      exists Pf; split.
      { destruct st'' as [|q st'']; [discriminate|]; exact Last. }
      intros O x n0 HO HP [|d] Hd.
      * exists rem, pr, np; split; [reflexivity|]; rewrite popn_0; reflexivity.
      * cbn [length] in Hd; destruct (S O x n0 HO HP d ltac:(lia)) as [rd [pd [nd [N Q]]]].
        exists rd, pd, nd; split; [exact N|]; cbn [map popn].
        rewrite (proj1 (popin_b_sound o rem O _ x) rem' P); exact Q.
    + destruct (popall_b F O1 rem ((y, o) :: pr) (N.succ np) c) as [[st'' c'']|] eqn:E; cbn in H; [|discriminate]; injection H as <- _.
      destruct (IH _ _ _ _ _ _ E) as [L [Pf [Last S]]]; split; [cbn; rewrite L; reflexivity|].
      cbn [rev] in Last; rewrite map_app, <- app_assoc in Last; cbn [map app snd] in Last.
      exists (o :: Pf); split.
      { destruct st'' as [|q st'']; [discriminate|]; exact Last. }
      intros O x n0 HO HP [|d] Hd.
      * exists rem, pr, np; split; [reflexivity|]; rewrite popn_0; reflexivity.
      * cbn [length] in Hd, HO.
        assert (HO' : length ((y, o) :: pr) + length Pf + n0 <= length O) by (cbn; lia).
        assert (HP' : forall k, k < length ((y, o) :: pr) + length Pf -> nth (n0 + k) O LNone = nth k (map snd (rev ((y, o) :: pr)) ++ Pf) LNone).
        { intros k Hk; cbn [rev]; rewrite map_app, <- app_assoc; apply HP; cbn in *; lia. }
        destruct (S O x n0 HO' HP' d ltac:(lia)) as [rd [pd [nd [N Q]]]].
        exists rd, pd, nd; split; [exact N|]; cbn [map popn snd].
        rewrite (proj2 (popin_b_sound o rem O _ x) P), <- Q; cbn [length].
        f_equal; f_equal; rewrite Nat.add_succ_r, popn_S by lia.
        f_equal; specialize (HP (length pr) ltac:(cbn [length]; lia)); rewrite HP, app_nth2 by (rewrite length_map, length_rev; lia).
        rewrite length_map, length_rev, Nat.sub_diag; reflexivity.
Qed.

Lemma pushes_tok_app O P I b x : Forall (fun lt => tok (length O) (snd lt)) I -> pushes (O ++ P) I b x = pushes O I b x.
Proof.
  induction 1 as [|[l t] I H _ IH]; [reflexivity|]; cbn [pushes]; rewrite IH; f_equal.
  destruct t as [z i d|u p]; [|reflexivity]; cbn in H |- *; rewrite popn_app_le by exact H; reflexivity.
Qed.

Lemma tok_mono n n' t : n <= n' -> tok n t -> tok n' t.
Proof. destruct t; cbn; lia. Qed.

Lemma omap_tag_in (g : btgt -> option btgt) (I I' : list (positive * (lexp * btgt))) (y : positive * (lexp * btgt)) :
  omap (fun '(id, (l, t)) => option_map (fun t' => (id, (l, t'))) (g t)) I = Some I' -> In y I' ->
  exists i l t t', In (i, (l, t)) I /\ g t = Some t' /\ y = (i, (l, t')).
Proof.
  revert I'; induction I as [|[i [l t]] I IH]; intros I' E Hy; cbn in *; [injection E as <-; destruct Hy|].
  destruct (g t) as [t'|] eqn:G; cbn in *; [|discriminate].
  destruct (omap _ I) as [I''|] eqn:E2; [|discriminate]; injection E as <-.
  destruct Hy as [<-|Hy]; [exists i, l, t, t'; auto|].
  destruct (IH I'' eq_refl Hy) as [i' [l' [t0 [t1 [H1 H2]]]]]; exists i', l', t0, t1; auto.
Qed.

Lemma tok_in e y : bok e -> In y (bi e) -> tok (length (bo e)) (snd (isnd y)).
Proof.
  intros [_ W] Hy; unfold wfd in W; rewrite beff_len in W; rewrite Forall_forall in W.
  apply (W (isnd y)); cbn [beff fin]; apply in_map, Hy.
Qed.

Theorem ecompose_b_sound f1 f2 g no ni canc : bok f1 -> bok f2 -> ecompose_b F f1 f2 = Some (g, no, ni, canc) ->
  (forall z, fd (beff g) z = fd (beff f1) (fd (beff f2) z)) /\ bok g.
Proof.
  intros Ok1 Ok2; pose proof Ok2 as [O2 W2]; unfold ecompose_b; rewrite rev'_rev.
  destruct (popall_b F (rev (bo f1)) (bi f2) [] 0 false) as [[st c]|] eqn:P; [|discriminate].
  destruct (popall_b_struct _ _ _ _ _ _ _ P eq_refl) as [Ne [B [C [D G]]]].
  destruct (popall_b_spec _ _ _ _ _ _ _ P) as [L [Pf [Last S]]]; cbn [rev map app length] in Last, S.
  change ([], ([], 0%N)) with d0.
  destruct (last st d0) as [remf [prf npf]] eqn:Lst; cbn [fst snd] in C, D, G, Last.
  destruct (omap _ (bi f1)) as [I1|] eqn:Om; [|discriminate]; intros H; injection H as <- _ _ _.
  set (O2l := rev (map snd (bo f2))).
  set (O := O2l ++ Pf).
  assert (LPf : length Pf = length prf) by (rewrite <- Last, length_map, length_rev; reflexivity).
  assert (LO2 : length O2l = length (bo f2)) by (unfold O2l; rewrite length_rev, length_map; reflexivity).
  assert (HO : length (@nil (positive * lexp)) + length Pf + length O2l <= length O) by (unfold O; rewrite length_app; cbn; lia).
  assert (HP : forall k, k < length (@nil (positive * lexp)) + length Pf -> nth (length O2l + k) O LNone = nth k (map snd (rev (@nil (positive * lexp))) ++ Pf) LNone).
  { intros k _; unfold O; rewrite app_nth2 by lia; f_equal; lia. }
  assert (Y : forall x, fd (beff f2) x = pushes O (map isnd (bi f2)) (popn O (length O2l + length (@nil (positive * lexp))) x) x).
  { intros x; unfold fden, O; cbn [beff fout fin]; fold O2l; rewrite Nat.add_0_r, (popn_app_le O2l Pf (length O2l) x) by lia; rewrite pushes_tok_app; [reflexivity|].
    unfold wfd in W2; rewrite beff_len in W2; rewrite LO2; exact W2. }
  assert (Gfo : fout (beff (mkB (prf ++ bo f2) (bl f2 + npf) (I1 ++ remf))) = O).
  { unfold O, O2l; cbn [beff fout bo]; rewrite map_app, rev_app_distr, <- Last, map_rev; reflexivity. }
  assert (LOt : length O = length O2l + length prf) by (unfold O; rewrite length_app; lia).
  split.
  - intros x; specialize (S O x (length O2l) HO HP).
    unfold fden at 1; rewrite Gfo; cbn [beff fin bi]; rewrite map_app, pushes_app.
    rewrite Y; unfold fden at 1; cbn [beff fout fin].
    replace (rev (map snd (bo f1))) with (map snd (rev (bo f1))) by apply map_rev.
    rewrite length_map.
    destruct (S (length (rev (bo f1))) (le_n _)) as [rf [pf [nf [N Q]]]].
    rewrite (nth_error_last_len st (length (rev (bo f1))) d0 L), Lst in N; injection N as <- <- <-.
    replace (length (@nil (positive * lexp))) with 0 by reflexivity; rewrite Q, LOt; apply (tag_pushes _ _ _ (bi f1) I1 _ _ _ Om).
    intros t t' Nt; destruct t as [z i d|u p]; cbn [newt_b] in Nt.
    + destruct (nth_error st (N.to_nat d)) as [[rd [pd nd]]|] eqn:Nd; [|discriminate].
      assert (Hd : N.to_nat d <= length (rev (bo f1))).
      { assert (nth_error st (N.to_nat d) <> None) as Hn by congruence; apply nth_error_Some in Hn; lia. }
      destruct (S (N.to_nat d) Hd) as [rd' [pd' [nd' [Nd' Qd]]]]; rewrite Nd in Nd'; injection Nd' as <- <- <-.
      cbn [tden ta]; rewrite Qd.
      destruct (rthrough_b_sound rd z i O (popn O (length O2l + length pd) x) x) as [R1 R2].
      destruct (rthrough_b F rd z i) as [[t''|i']|]; [| |discriminate]; injection Nt as <-.
      * symmetry; apply R1; reflexivity.
      * cbn [tden ta]; symmetry; rewrite (R2 i' eq_refl).
        destruct (B _ _ _ _ Nd) as [_ [_ [_ Hnd]]]; rewrite N2Nat.inj_add, Hnd, Nat2N.id, O2, <- LO2; reflexivity.
    + injection Nt as <-; cbn [tden ta cp fpb]; rewrite fexp_sound, fa_b_to_c, Y; reflexivity.
  - split; [cbn [bl bo]; rewrite N2Nat.inj_add, G, Nat2N.id, length_app, O2; lia|].
    unfold wfd; rewrite beff_len; cbn [beff fin bo bi]; rewrite length_app, map_app; apply Forall_app; split.
    + apply Forall_forall; intros [l t] Hin; apply in_map_iff in Hin as [y [Ey Hy]].
      destruct (omap_tag_in _ _ _ y Om Hy) as [i [l0 [t0 [t1 [Hi [Ht ->]]]]]]; rewrite isnd_eq in Ey; injection Ey as <- <-; cbn [snd].
      destruct t0 as [z0 i0 d0'|u p0]; cbn [newt_b] in Ht.
      * destruct (nth_error st (N.to_nat d0')) as [[r [q n]]|] eqn:N; [|discriminate].
        destruct (B _ _ _ _ N) as [B1 [_ [B3 B4]]].
        destruct (rthrough_b F r z0 i0) as [[t'|i']|] eqn:R; [| |discriminate]; injection Ht as <-.
        -- destruct (rthrough_b_in _ _ _ _ R) as [j' [l' Hl]]; apply B1 in Hl.
           apply (tok_mono (length (bo f2))); [lia|exact (tok_in f2 _ Ok2 Hl)].
        -- cbn [fst snd] in B3; cbn; rewrite N2Nat.inj_add, B4, Nat2N.id, O2; lia.
      * injection Ht as <-; exact Logic.I.
    + apply Forall_forall; intros [l t] Hin; apply in_map_iff in Hin as [y [Ey Hy]].
      pose proof (tok_in f2 y Ok2 (C _ Hy)) as T; rewrite Ey in T; cbn [snd] in T.
      apply (tok_mono (length (bo f2))); [lia|exact T].
Qed.

(** *** Steps that keep meaning and [bok] *)

Definition keeps (e e' : bform) : Prop := bok e' /\ forall z, fd (beff e') z = fd (beff e) z.

Lemma keeps_trans a b c : keeps a b -> keeps b c -> keeps a c.
Proof. intros [_ H1] [O2 H2]; split; [exact O2|intros z; rewrite H2, H1; reflexivity]. Qed.

Lemma keeps_refl e : bok e -> keeps e e.
Proof. intros O; split; [exact O|reflexivity]. Qed.

Lemma reread_front_b_keeps n e : bok e -> keeps e (reread_front_b F n e).
Proof.
  intros Ok; split; [|intros z; apply (inputs_rel e _ z (reread_front_b_rel e n z (proj1 Ok)))].
  destruct Ok as [O W]; split; [exact O|]; unfold wfd in *; cbn [beff fout fin bo bi] in *.
  revert W; unfold reread_front_b; cbn [bi]; generalize (bi e); induction n as [|n IH]; intros [|[i [l t]] I] W; cbn [map_front map];
    try exact W; inversion W as [|a b W1 W2]; subst; constructor; [|apply IH, W2].
  cbn [isnd ina snd fst] in *; apply nread_e_b_tok, W1.
Qed.

Lemma reread_at_b_keeps j e : bok e -> keeps e (reread_at_b F j e).
Proof.
  intros Ok; split; [|intros z; apply (inputs_rel e _ z (reread_at_b_rel e j z (proj1 Ok)))].
  destruct Ok as [O W]; split; [exact O|]; unfold wfd in *; cbn [beff fout fin bo bi] in *.
  revert W; unfold reread_at_b; cbn [bi]; generalize (bi e); intros L; induction L as [|[i [l t]] I IH]; intros W; cbn [map]; [exact W|].
  inversion W as [|a b W1 W2]; subst; constructor; [|apply IH, W2].
  cbn [isnd ina snd fst] in *; destruct (bis_dep _ t); [apply nread_e_b_tok|]; exact W1.
Qed.

Lemma bub_in_b_perm x I : Permutation (bub_in_b F x I) (x :: I).
Proof.
  induction I as [|y I IH]; cbn [bub_in_b]; [reflexivity|].
  destruct (before F (blab y) (blab x)); [rewrite IH; apply perm_swap|reflexivity].
Qed.

Lemma place_front_b_perm n I : Permutation (place_front_b F n I) I.
Proof.
  revert I; induction n as [|n IH]; intros [|x I]; cbn [place_front_b]; try reflexivity.
  rewrite bub_in_b_perm; apply perm_skip, IH.
Qed.

Lemma ins_out_b_perm x rp : Permutation (ins_out_b F x rp) (x :: rp).
Proof.
  induction rp as [|y r IH]; cbn [ins_out_b]; [reflexivity|].
  destruct (before F (blab x) (blab y)); [rewrite IH; apply perm_swap|reflexivity].
Qed.

Lemma out_pass_b_perm rp suf : Permutation (out_pass_b F rp suf) (rev rp ++ suf).
Proof.
  revert rp; induction suf as [|x s IH]; intros rp; cbn [out_pass_b]; [rewrite rev'_rev, app_nil_r; reflexivity|].
  rewrite IH, ins_out_b_perm; cbn [rev]; rewrite <- app_assoc; reflexivity.
Qed.

Lemma place_suffix_out_b_perm p I : Permutation (place_suffix_out_b F p I) I.
Proof. unfold place_suffix_out_b; rewrite rev'_rev, out_pass_b_perm, rev_involutive, firstn_skipn; reflexivity. Qed.

Lemma place_front_b_keeps n e : bok e -> keeps e (mkB (bo e) (bl e) (place_front_b F n (bi e))).
Proof.
  intros Ok; split; [apply perm_ok; [exact Ok|apply place_front_b_perm]|].
  intros z; apply perm_inputs; intros b; apply place_front_b_sound.
Qed.

Lemma place_suffix_b_keeps p e : bok e -> keeps e (mkB (bo e) (bl e) (place_suffix_out_b F p (bi e))).
Proof.
  intros Ok; split; [apply perm_ok; [exact Ok|apply place_suffix_out_b_perm]|].
  intros z; apply perm_inputs; intros b; apply place_suffix_out_b_sound.
Qed.

Lemma place_out_bottom_b_keeps r e : bok e -> keeps e (place_out_bottom_b F r e).
Proof. intros Ok; destruct (place_out_bottom_b_sound r e Ok) as [H O]; split; assumption. Qed.

Lemma place_out_top_b_keeps r e : bok e -> keeps e (place_out_top_b F r e).
Proof. intros Ok; destruct (place_out_top_b_sound r e Ok) as [H O]; split; assumption. Qed.

Lemma bof_i_keeps e g o i : (forall z, fd (fa g) z = fd (beff e) z) -> keeps e (bof_i g o i).
Proof. intros H; split; [apply bof_i_ok|intros z; rewrite bof_i_sound; apply H]. Qed.

(** *** Absorbing, composing, moving *)

Lemma iabsorb_b_keeps p e e' : bok e -> iabsorb_b F p e = Some e' -> keeps e e'.
Proof.
  intros Ok; unfold iabsorb_b; destruct (babsorb2 F p (b_to_c e)) as [[j g]|] eqn:A; [|discriminate].
  intros H; injection H as <-.
  set (e0 := bof_i g (remove_at j (rev' (map fst (bo e)))) (remove_at p (map fst (bi e)))).
  assert (K0 : keeps e e0) by (apply bof_i_keeps; intros z; rewrite (babsorb2_sound F M HM p _ j g z A), fa_b_to_c; reflexivity).
  assert (K1 := keeps_trans _ _ _ K0 (reread_at_b_keeps j e0 (proj1 K0))).
  assert (K2 := keeps_trans _ _ _ K1 (place_out_bottom_b_keeps (N.to_nat (bl (reread_at_b F j e0)) - j) _ (proj1 K1))).
  exact (keeps_trans _ _ _ K2 (place_suffix_b_keeps p _ (proj1 K2))).
Qed.

Lemma absorb_scan_b_keeps new e p I e' : bok e -> absorb_scan_b F new e p I = Some e' -> keeps e e'.
Proof.
  intros Ok; revert p; induction I as [|x I IH]; intros p; cbn [absorb_scan_b]; [discriminate|].
  destruct (mem (fst x) new && restore_like_b x); [|apply IH].
  destruct (iabsorb_b F p e) as [g|] eqn:A; [intros H; injection H as <-; apply (iabsorb_b_keeps p), A; exact Ok|apply IH].
Qed.

Lemma absorb_new_b_keeps fuel new e : bok e -> keeps e (absorb_new_b F fuel new e).
Proof.
  revert e; induction fuel as [|fuel IH]; intros e Ok; cbn [absorb_new_b]; [apply keeps_refl, Ok|].
  destruct (absorb_scan_b F new e 0 (bi e)) as [g|] eqn:A; [|apply keeps_refl, Ok].
  pose proof (absorb_scan_b_keeps _ _ _ _ _ Ok A) as K; exact (keeps_trans _ _ _ K (IH g (proj1 K))).
Qed.

Theorem icompose_b_sound f1 f2 g no ni canc : bok f1 -> bok f2 -> icompose_b F f1 f2 = Some (g, no, ni, canc) ->
  bok g /\ forall z, fd (beff g) z = fd (beff f1) (fd (beff f2) z).
Proof.
  intros O1 O2; unfold icompose_b.
  destruct (ecompose_b F f1 f2) as [[[[g0 passed] newin] c]|] eqn:E; [|discriminate]; intros H; injection H as <- _ _ _.
  destruct (ecompose_b_sound _ _ _ _ _ _ O1 O2 E) as [S0 Ok0].
  assert (K1 := reread_front_b_keeps (length (bi f1)) g0 Ok0).
  assert (K2 := keeps_trans _ _ _ K1 (place_front_b_keeps (length (bi f1)) _ (proj1 K1))).
  set (g2 := mkB (bo (reread_front_b F (length (bi f1)) g0)) (bl (reread_front_b F (length (bi f1)) g0))
                 (place_front_b F (length (bi f1)) (bi (reread_front_b F (length (bi f1)) g0)))) in K2.
  assert (K3 : keeps g0 (if c then mkB (bo g2) (bl g2) (place_suffix_out_b F (length (bi f1)) (bi g2)) else g2))
    by (destruct c; [exact (keeps_trans _ _ _ K2 (place_suffix_b_keeps _ _ (proj1 K2)))|exact K2]).
  assert (K4 := keeps_trans _ _ _ K3 (place_out_bottom_b_keeps (length passed) _ (proj1 K3))).
  assert (K5 : keeps g0 (match newin with [] => place_out_bottom_b F (length passed) (if c then mkB (bo g2) (bl g2) (place_suffix_out_b F (length (bi f1)) (bi g2)) else g2)
                                     | _ => absorb_new_b F (S (length newin)) newin (place_out_bottom_b F (length passed) (if c then mkB (bo g2) (bl g2) (place_suffix_out_b F (length (bi f1)) (bi g2)) else g2)) end))
    by (destruct newin; [exact K4|exact (keeps_trans _ _ _ K4 (absorb_new_b_keeps _ _ _ (proj1 K4)))]).
  destruct K5 as [O5 H5]; split; [exact O5|intros z; rewrite H5; apply S0].
Qed.

Lemma ok_single_out (x : positive) o : bok (mkB [(x, o)] 1 []).
Proof. split; [reflexivity|constructor]. Qed.

Lemma bin_first_tok p f h t f' : bin_first F p f = Some (h, t, f') -> tok 0 (ta t).
Proof.
  unfold bin_first; destruct (nth_error (cin f) p) as [[h0 t0]|]; [|discriminate].
  destruct (_ && _); [|discriminate].
  destruct t0 as [z i d|u q].
  - destruct (bpull F (cout f) (N.to_nat d) z i); cbn; [|discriminate].
    destruct (omap _ _); [|discriminate]; intros H; injection H as _ <- _; cbn; lia.
  - destruct (omap _ _); [|discriminate]; intros H; injection H as _ <- _; exact Logic.I.
Qed.

Theorem imove_b_sound f1 f2 y f1' g new canc lost : bok f1 -> bok f2 -> imove_b F f1 f2 y = Some (f1', g, new, canc, lost) ->
  bok f1' /\ bok g /\ forall z, fd (beff f1') (fd (beff g) z) = fd (beff f1) (fd (beff f2) z).
Proof.
  intros O1 O2; unfold imove_b.
  destruct (index_of y (oids_b f1)) as [j|].
  - destruct (bout_first F j (b_to_c f1)) as [[o f1o]|] eqn:Of; [|discriminate].
    destruct (icompose_b F (mkB [(y, o)] 1 []) f2) as [[[[g' no] ni] c]|] eqn:C; [|discriminate].
    intros H; injection H as <- <- _ _ _.
    destruct (icompose_b_sound _ _ _ _ _ _ (ok_single_out y o) O2 C) as [Og Hg].
    set (e0 := bof_i f1o (remove_at j (oids_b f1)) (iids_b f1)).
    assert (K0 : bok e0 /\ forall z, fd (beff e0) z = fd (fa f1o) z) by (split; [apply bof_i_ok|intros z; apply bof_i_sound]).
    assert (K1 := reread_at_b_keeps j e0 (proj1 K0)).
    assert (K2 := keeps_trans _ _ _ K1 (place_out_bottom_b_keeps (N.to_nat (bl (reread_at_b F j e0)) - j) _ (proj1 K1))).
    destruct K2 as [O3 H3]; split; [exact O3|split; [exact Og|]].
    intros z; rewrite H3, (proj2 K0), Hg, <- (fa_b_to_c f1), (bout_first_sound F M HM j _ _ _ _ Of); reflexivity.
  - destruct (index_of y (iids_b f1)) as [p|]; [|discriminate].
    destruct (bin_first F p (b_to_c f1)) as [[[h t] f1o]|] eqn:If; [|discriminate].
    destruct (icompose_b F (mkB [] 0 [(y, (h, t))]) f2) as [[[[g' no] ni] c]|] eqn:C; [|discriminate].
    intros H; injection H as <- <- _ _ _.
    assert (Os : bok (mkB [] 0 [(y, (h, t))])) by (split; [reflexivity|constructor; [exact (bin_first_tok _ _ _ _ _ If)|constructor]]).
    destruct (icompose_b_sound _ _ _ _ _ _ Os O2 C) as [Og Hg].
    set (e0 := bof_i f1o (oids_b f1) (remove_at p (iids_b f1))).
    assert (K0 : bok e0 /\ forall z, fd (beff e0) z = fd (fa f1o) z) by (split; [apply bof_i_ok|intros z; apply bof_i_sound]).
    assert (K1 := place_suffix_b_keeps p e0 (proj1 K0)).
    destruct K1 as [O3 H3]; split; [exact O3|split; [exact Og|]].
    intros z; rewrite H3, (proj2 K0), Hg, <- (fa_b_to_c f1), (bin_first_sound F M HM p _ _ _ _ _ If); reflexivity.
Qed.

(** *** Lifts *)

Definition shift_tl (L : list lexp) (t : tgt) : tgt :=
  match t with TR z i d => TR z i (length L + d) | TT u p => TT u (fold_right PShift p L) end.

(** A form under the lifts [L], outermost first, as one form. *)
Definition lift_spec (L : list lexp) (f : form) : form :=
  mkF (L ++ fout f) (mapi_from 0 (fun k h => (h, TR h 0 k)) L ++ map (fun '(g, t) => (g, shift_tl L t)) (fin f)).

Lemma map_shift_mapi h k (L : list lexp) :
  map (fun '(g, t) => (g, shift_t h t)) (mapi_from k (fun k h' => (h', TR h' 0 k)) L)
  = mapi_from (S k) (fun k h' => (h', TR h' 0 k)) L.
Proof. revert k; induction L as [|h' L IH]; intros k; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma map_shift_tl h L (I : list (lexp * tgt)) :
  map (fun '(g, t) => (g, shift_t h t)) (map (fun '(g, t) => (g, shift_tl L t)) I)
  = map (fun '(g, t) => (g, shift_tl (h :: L) t)) I.
Proof. induction I as [|[g [z i d|u q]] I IH]; cbn; [reflexivity| |]; rewrite IH; reflexivity. Qed.

Lemma lift_spec_eq L f : lift_spec L f = fold_right lift_f f L.
Proof.
  induction L as [|h L IH].
  - destruct f as [O I]; unfold lift_spec; cbn; f_equal.
    induction I as [|[g [z i d|u q]] I IH]; cbn; [reflexivity| |]; rewrite IH; reflexivity.
  - change (fold_right lift_f f (h :: L)) with (lift_f h (fold_right lift_f f L)); rewrite <- IH.
    unfold lift_f, lift_spec; cbn [fout fin app mapi_from]; f_equal.
    rewrite map_app, map_shift_mapi, map_shift_tl; reflexivity.
Qed.

Lemma map_snd_combine {X Y} (a : list X) (b : list Y) : length a = length b -> map snd (combine a b) = b.
Proof. revert b; induction a as [|x a IH]; intros [|y b] H; cbn in *; try discriminate; [reflexivity|rewrite IH; [reflexivity|lia]]. Qed.

Lemma length_pseq c n : length (pseq c n) = n.
Proof. revert c; induction n as [|n IH]; intros c; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma length_mapiN {X Y} k (g : N -> X -> Y) l : length (mapi_fromN k g l) = length l.
Proof. revert k; induction l as [|a l IH]; intros k; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma mapi_fromN_eq k L :
  map ina (mapi_fromN (N.of_nat k) (fun k h => (h, BR h 0 k)) L) = mapi_from k (fun k h => (h, TR h 0 k)) L.
Proof.
  revert k; induction L as [|h L IH]; intros k; cbn [mapi_fromN mapi_from map]; [reflexivity|]; f_equal.
  - rewrite ina_pair; cbn [ta]; rewrite Nat2N.id; reflexivity.
  - rewrite <- Nat2N.inj_succ; apply IH.
Qed.

Lemma beff_lift_b L f c : beff (lift_b L f c) = lift_spec L (beff f).
Proof.
  unfold lift_b, beff, lift_spec; cbn [bo bi fout fin]; f_equal.
  - rewrite rev'_rev, map_app, rev_app_distr, map_rev, rev_involutive, map_snd_combine by (rewrite length_pseq; reflexivity); reflexivity.
  - rewrite map_app, map_isnd, map_snd_combine by (rewrite length_pseq, length_mapiN; reflexivity).
    rewrite (mapi_fromN_eq 0); f_equal; rewrite !map_map; apply map_ext; intros [i [g [z j d|u q]]]; rewrite !isnd_eq; cbn [ta bshift_ts shift_tl]; rewrite ?N2Nat.inj_add, ?Nat2N.id; reflexivity.
Qed.

Lemma lift_b_sound L f c z : fd (beff (lift_b L f c)) z = liftsem M L (fd (beff f)) z.
Proof. rewrite beff_lift_b, lift_spec_eq; apply CSpec.lift_fold_sound. Qed.

Lemma restores_tok n k (L : list lexp) : k + length L <= n ->
  Forall (fun lt => tok n (snd lt)) (mapi_from k (fun k h => (h, TR h 0 k)) L).
Proof. revert k; induction L as [|h L IH]; intros k H; cbn in *; constructor; [cbn; lia|apply IH; lia]. Qed.

Lemma lift_b_ok L f c : bok f -> bok (lift_b L f c).
Proof.
  intros [O W]; split.
  - unfold lift_b; cbn [bl bo]; rewrite N2Nat.inj_add, Nat2N.id, rev'_rev, length_app, length_rev, length_combine, length_pseq, O; lia.
  - unfold wfd in *; rewrite beff_lift_b; unfold lift_spec; cbn [fout fin] in *; rewrite length_app.
    apply Forall_app; split; [apply restores_tok; lia|].
    rewrite Forall_forall in *; intros [g t] Hin; apply in_map_iff in Hin as [[g0 t0] [E Hin]]; injection E as <- <-.
    specialize (W _ Hin); destruct t0; cbn in *; [lia|exact Logic.I].
Qed.

Lemma absorb_walk_b_keeps fuel p rf inside e k : bok e -> keeps e (fst (absorb_walk_b F fuel p rf inside e k)).
Proof.
  revert p rf inside e k; induction fuel as [|fuel IH]; intros p rf inside e k Ok; cbn [absorb_walk_b]; [apply keeps_refl, Ok|].
  destruct rf as [|x rf]; [apply keeps_refl, Ok|].
  destruct (if pre_x_b F x inside e then iabsorb_b F p e else None) as [e'|] eqn:A.
  - assert (K : keeps e e') by (destruct (pre_x_b F x inside e); [apply (iabsorb_b_keeps p e e' Ok A)|discriminate]).
    exact (keeps_trans _ _ _ K (IH _ _ _ _ _ (proj1 K))).
  - apply IH, Ok.
Qed.

Lemma lift_many_b_sound L f c : bok f ->
  match fst (lift_many_b F L (BF f) c) with
  | BF g => bok g /\ forall z, fd (beff g) z = liftsem M L (fd (beff f)) z
  | BA _ _ => False
  end.
Proof.
  intros Ok; unfold lift_many_b.
  destruct (absorb_walk_b F _ _ _ _ (lift_b L f c) 0) as [f1 k] eqn:W.
  assert (K0 : keeps (lift_b L f c) f1).
  { pose proof (absorb_walk_b_keeps (length L) (pred (length L)) (rev' (firstn (length L) (bi (lift_b L f c))))
                  (skipn (length L) (bi (lift_b L f c))) (lift_b L f c) 0 (lift_b_ok L f c Ok)) as K; rewrite W in K; exact K. }
  assert (K1 := keeps_trans _ _ _ K0 (place_front_b_keeps k f1 (proj1 K0))).
  assert (K2 := keeps_trans _ _ _ K1 (place_out_top_b_keeps (Nat.min k (N.to_nat (bl (mkB (bo f1) (bl f1) (place_front_b F k (bi f1)))))) _ (proj1 K1))).
  cbn [fst]; destruct K2 as [O2 H2]; split; [exact O2|intros z; rewrite H2; apply lift_b_sound].
Qed.

(** *** The word *)

Definition okit (it : bitem) : Prop := match it with BF f => bok f | BA _ _ => True end.

Local Notation wde := (fun st x => wden M (map bstrip st) x).

Lemma try_ids_b_sound f1 f2 xs cands f1' g new canc lost : bok f1 -> bok f2 ->
  try_ids_b F f1 f2 xs cands = Some (f1', g, new, canc, lost) ->
  bok f1' /\ bok g /\ forall z, fd (beff f1') (fd (beff g) z) = fd (beff f1) (fd (beff f2) z).
Proof.
  intros O1 O2; induction xs as [|y xs IH]; cbn [try_ids_b]; [discriminate|].
  destruct (mem y cands); [|apply IH].
  destruct (imove_b F f1 f2 y) as [[[[[a b] c] d] e]|] eqn:E; [|apply IH].
  intros H; injection H as -> -> -> -> ->; apply (imove_b_sound _ _ _ _ _ _ _ _ O1 O2 E).
Qed.

Lemma moves_b_sound fuel k f1 f2 c acc f1' g acc' : bok f1 -> bok f2 -> moves_b F fuel k f1 f2 c acc = (f1', g, acc') ->
  bok f1' /\ bok g /\ forall z, fd (beff f1') (fd (beff g) z) = fd (beff f1) (fd (beff f2) z).
Proof.
  revert f1 f2 c acc; induction fuel as [|fuel IH]; intros f1 f2 c acc O1 O2; cbn [moves_b].
  - intros H; injection H as <- <- _; auto.
  - destruct (try_ids_b F f1 f2 (ids_of_b f1) c) as [[[[[a b] new] canc] lost]|] eqn:T.
    + destruct (try_ids_b_sound _ _ _ _ _ _ _ _ _ O1 O2 T) as [Oa [Ob H1]].
      intros H; destruct (IH _ _ _ _ Oa Ob H) as [O3 [O4 H2]]; split; [exact O3|split; [exact O4|intros z; rewrite H2, H1; reflexivity]].
    + intros H; injection H as <- <- _; auto.
Qed.

Lemma Forall_firstn' {X} (P : X -> Prop) n l : Forall P l -> Forall P (firstn n l).
Proof. revert l; induction n; intros [|a l] H; cbn; auto; inversion H; subst; constructor; auto. Qed.

Lemma Forall_skipn' {X} (P : X -> Prop) n l : Forall P l -> Forall P (skipn n l).
Proof. revert l; induction n; intros [|a l] H; cbn; auto; inversion H; subst; auto. Qed.

Lemma Forall_put2b k st mid : Forall okit st -> Forall okit mid -> Forall okit (put2b k st mid).
Proof.
  intros H1 H2; unfold put2b; apply Forall_app; split; [apply Forall_firstn', H1|].
  apply Forall_app; split; [exact H2|apply Forall_skipn', H1].
Qed.

Lemma wde_app st1 st2 x : wde (st1 ++ st2) x = wde st1 (wde st2 x).
Proof. cbn; rewrite map_app; apply CSpec.wden_app. Qed.

Lemma step_b_put k st a b mid x : nth_error st k = Some a -> nth_error st (S k) = Some b ->
  (forall y, wde mid y = iden M (bstrip a) (iden M (bstrip b) y)) -> wde (put2b k st mid) x = wde st x.
Proof.
  intros Ha Hb H; unfold put2b; pose proof (split2 st k a b Ha Hb) as E.
  set (A := firstn k st) in *; set (R := skipn (S (S k)) st) in *.
  rewrite E; rewrite !wde_app, H; reflexivity.
Qed.

Lemma iempty_b_den g : iempty_b g = true -> forall y, fd (beff g) y = y.
Proof. destruct g as [[|o go] gl [|i gi]]; cbn; try discriminate; reflexivity. Qed.

Lemma step_b_sound s : Forall okit (fst s) -> Forall okit (fst (step_b F s)) /\ forall x, wde (fst (step_b F s)) x = wde (fst s) x.
Proof.
  destruct s as [st w]; unfold step_b; cbn [fst]; intros Hst.
  destruct w as [|[k cands] w']; [auto|].
  destruct (nth_error st k) as [[f1|L1 n1]|] eqn:Ea; try (split; [exact Hst|reflexivity]).
  destruct (nth_error st (S k)) as [[f2|L2 n2]|] eqn:Eb; try (split; [exact Hst|reflexivity]).
  assert (O1 : bok f1) by (rewrite Forall_forall in Hst; apply (Hst (BF f1)), (nth_error_In _ _ Ea)).
  assert (O2 : bok f2) by (rewrite Forall_forall in Hst; apply (Hst (BF f2)), (nth_error_In _ _ Eb)).
  destruct (match cands with None => icompose_b F f1 f2 | Some _ => None end) as [[[[g no] ni] cc]|] eqn:Mg.
  - assert (G : bok g /\ forall y, fd (beff g) y = fd (beff f1) (fd (beff f2) y))
      by (destruct cands; [discriminate|apply (icompose_b_sound _ _ _ _ _ _ O1 O2 Mg)]).
    destruct G as [Og G].
    destruct (iempty_b g) eqn:Em; cbn [fst].
    + split; [apply Forall_put2b; [exact Hst|constructor]|].
      intros x; apply (step_b_put k st (BF f1) (BF f2)); auto; intros y; cbn [map bstrip wden iden]; rewrite <- G, (iempty_b_den g Em); reflexivity.
    + split; [apply Forall_put2b; [exact Hst|constructor; [exact Og|constructor]]|].
      intros x; apply (step_b_put k st (BF f1) (BF f2)); auto; intros y; cbn [map bstrip wden iden]; apply G.
  - destruct (moves_b F _ k f1 f2 _ []) as [[f1' g] acc] eqn:Mv.
    destruct (moves_b_sound _ _ _ _ _ _ _ _ _ O1 O2 Mv) as [Oa [Ob G]].
    destruct (iempty_b f1') eqn:Em; cbn [fst].
    + split; [apply Forall_put2b; [exact Hst|repeat first [apply Forall_nil|apply Forall_cons; [assumption|]]]|].
      intros x; apply (step_b_put k st (BF f1) (BF f2)); auto; intros y; cbn [map bstrip wden iden]; rewrite <- G, (iempty_b_den f1' Em); reflexivity.
    + split; [apply Forall_put2b; [exact Hst|repeat first [apply Forall_nil|apply Forall_cons; [assumption|]]]|].
      intros x; apply (step_b_put k st (BF f1) (BF f2)); auto; intros y; cbn [map bstrip wden iden]; apply G.
Qed.

Lemma settle_b_sound p s : Forall okit (fst s) -> Forall okit (fst (settle_b F p s)) /\ forall x, wde (fst (settle_b F p s)) x = wde (fst s) x.
Proof.
  revert s; induction p as [p IH|p IH|]; intros s Hs; cbn [settle_b]; destruct (snd s); try (split; [exact Hs|reflexivity]).
  - destruct (IH s Hs) as [A1 B1]; destruct (IH _ A1) as [A2 B2]; destruct (step_b_sound _ A2) as [A3 B3].
    split; [exact A3|intros x; rewrite B3, B2, B1; reflexivity].
  - destruct (IH s Hs) as [A1 B1]; destruct (IH _ A1) as [A2 B2]; split; [exact A2|intros x; rewrite B2, B1; reflexivity].
  - apply step_b_sound, Hs.
Qed.

Lemma insert_b_sound it st : okit it -> Forall okit st ->
  Forall okit (insert_b F it st) /\ forall x, wde (insert_b F it st) x = iden M (bstrip it) (wde st x).
Proof.
  intros Hi Hs; destruct it as [f|L n]; cbn [insert_b]; [|split; [constructor; [exact Hi|exact Hs]|reflexivity]].
  destruct (iempty_b f) eqn:E.
  - split; [exact Hs|intros x; cbn [map bstrip iden]; symmetry; apply (iempty_b_den f E)].
  - destruct (settle_b_sound bbig (BF f :: st, [(0, None)])) as [A B]; [constructor; assumption|].
    split; [exact A|intros x; rewrite B; reflexivity].
Qed.

Lemma lift_many_b_sound' L it c : okit it -> okit (fst (lift_many_b F L it c)) /\
  forall x, iden M (bstrip (fst (lift_many_b F L it c))) x = liftsem M L (iden M (bstrip it)) x.
Proof.
  destruct it as [f|L' n]; intros Hi.
  - pose proof (lift_many_b_sound L f c Hi) as H; destruct (fst (lift_many_b F L (BF f) c)) as [g|]; [|contradiction].
    destruct H as [Og Hg]; split; [exact Og|exact Hg].
  - split; [exact Logic.I|intros x; cbn; apply CSpec.lden_app].
Qed.

Lemma insert_lifted_b_sound L w st c : Forall okit w -> Forall okit st ->
  Forall okit (fst (insert_lifted_b F L w st c)) /\ forall x, wde (fst (insert_lifted_b F L w st c)) x = liftsem M L (wde w) (wde st x).
Proof.
  revert c; induction w as [|it w IH]; intros c Hw Hs; cbn [insert_lifted_b].
  - split; [exact Hs|intros x; cbn; symmetry; apply CSpec.liftsem_id].
  - inversion Hw as [|a b Hit Hw']; subst.
    destruct (insert_lifted_b F L w st c) as [st1 c1] eqn:E1.
    destruct (lift_many_b F L it c1) as [it' c2] eqn:E2; cbn [fst].
    destruct (IH c Hw' Hs) as [A1 B1]; rewrite E1 in A1, B1; cbn [fst] in A1, B1.
    destruct (lift_many_b_sound' L it c1 Hit) as [A2 B2]; rewrite E2 in A2, B2; cbn [fst] in A2, B2.
    destruct (insert_b_sound it' st1 A2 A1) as [A3 B3]; split; [exact A3|].
    intros x; rewrite B3, B1, B2, CSpec.liftsem_comp; reflexivity.
Qed.

End SoundN.

(** *** Expressions *)

(** The chain of lifts inside [rnormN], as a function of its own. *)
Section PeelN.
Variable F : order.
Fixpoint peelN (R : list lexp) (a : aexp) (st : list bitem) (c : positive) {struct a} : list bitem * positive :=
  match a with
  | ALift h' a' => peelN (h' :: R) a' st c
  | _ => let '(w, c1) := rnormN F a [] c in insert_lifted_b F (rev' R) w st c1
  end.
End PeelN.

Lemma rnormN_lift F h a st c : rnormN F (ALift h a) st c = peelN F [h] a st c.
Proof. reflexivity. Qed.

Lemma rnormN_inner F h t a st c :
  rnormN F (AInner h t a) st c = peelN F [h] a (insert_b F (BF (fst (bfresh (entry h t) c))) st) (snd (bfresh (entry h t) c)).
Proof. reflexivity. Qed.

Lemma rnormN_outer F h a st c : rnormN F (AOuter h a) st c = rnormN F a (insert_b F (BF (fst (bfresh (weak h) c))) st) (snd (bfresh (weak h) c)).
Proof. reflexivity. Qed.

Section SoundExp.

Variable F : order.
Variable M : cmodel.
Hypothesis HM : ccons F M.

Local Notation wde := (fun st x => wden M (map bstrip st) x).

Lemma bfresh_ok f c : bok (fst (bfresh f c)).
Proof. apply bof_i_ok. Qed.

Lemma bfresh_sound f c x : fden M (beff (fst (bfresh f c))) x = fden M f x.
Proof. cbn [bfresh fst]; rewrite bof_i_sound, fa_fb; reflexivity. Qed.

Theorem rnormN_sound : forall e,
  (forall st c, Forall okit st -> Forall okit (fst (rnormN F e st c)) /\ forall x, wde (fst (rnormN F e st c)) x = ca e (wde st x))
  /\ (forall R st c, Forall okit st -> Forall okit (fst (peelN F R e st c)) /\ forall x, wde (fst (peelN F R e st c)) x = liftsem M (rev R) (ca e) (wde st x)).
Proof.
  assert (Peel : forall e, (forall st c, Forall okit st -> Forall okit (fst (rnormN F e st c)) /\ forall x, wde (fst (rnormN F e st c)) x = ca e (wde st x)) ->
            (forall a, e <> ALift (fst a) (snd a)) ->
            forall R st c, Forall okit st -> Forall okit (fst (peelN F R e st c)) /\ forall x, wde (fst (peelN F R e st c)) x = liftsem M (rev R) (ca e) (wde st x)).
  { intros e H1 Hn R st c Hs.
    assert (P : peelN F R e st c = let '(w, c1) := rnormN F e [] c in insert_lifted_b F (rev' R) w st c1)
      by (destruct e as [| | | | |h' a']; try reflexivity; exfalso; apply (Hn (h', a')); reflexivity).
    rewrite P, rev'_rev; destruct (rnormN F e [] c) as [w c1] eqn:E.
    destruct (H1 [] c (Forall_nil _)) as [A B]; rewrite E in A, B; cbn [fst] in A, B.
    destruct (insert_lifted_b_sound F M HM (rev R) w st c1 A Hs) as [A2 B2]; split; [exact A2|].
    intros x; rewrite B2; apply CSpec.liftsem_ext; intros y; apply B. }
  induction e as [|n|a [IHa1 IHa2] b [IHb1 IHb2]|h a [IH1 IH2]|h t a [IH1 IH2]|h a [IH1 IH2]].
  - assert (H1 : forall st c, Forall okit st -> Forall okit (fst (rnormN F AId st c)) /\ forall x, wde (fst (rnormN F AId st c)) x = ca AId (wde st x))
      by (intros st c Hs; split; [exact Hs|reflexivity]).
    split; [exact H1|apply Peel; [exact H1|intros [? ?]; discriminate]].
  - assert (H1 : forall st c, Forall okit st -> Forall okit (fst (rnormN F (AAtom n) st c)) /\ forall x, wde (fst (rnormN F (AAtom n) st c)) x = ca (AAtom n) (wde st x)).
    { intros st c Hs; cbn [rnormN fst]; destruct (insert_b_sound F M HM (BA [] n) st Logic.I Hs) as [A B]; split; [exact A|intros x; rewrite B; reflexivity]. }
    split; [exact H1|apply Peel; [exact H1|intros [? ?]; discriminate]].
  - assert (H1 : forall st c, Forall okit st -> Forall okit (fst (rnormN F (ACompose a b) st c)) /\ forall x, wde (fst (rnormN F (ACompose a b) st c)) x = ca (ACompose a b) (wde st x)).
    { intros st c Hs; cbn [rnormN]; destruct (rnormN F a st c) as [st1 c1] eqn:E.
      destruct (IHa1 st c Hs) as [A1 B1]; rewrite E in A1, B1; cbn [fst] in A1, B1.
      destruct (IHb1 st1 c1 A1) as [A2 B2]; split; [exact A2|intros x; rewrite B2, B1; reflexivity]. }
    split; [exact H1|apply Peel; [exact H1|intros [? ?]; discriminate]].
  - assert (H1 : forall st c, Forall okit st -> Forall okit (fst (rnormN F (AOuter h a) st c)) /\ forall x, wde (fst (rnormN F (AOuter h a) st c)) x = ca (AOuter h a) (wde st x)).
    { intros st c Hs; rewrite rnormN_outer.
      destruct (insert_b_sound F M HM (BF (fst (bfresh (weak h) c))) st (bfresh_ok _ _) Hs) as [A B].
      destruct (IH1 _ (snd (bfresh (weak h) c)) A) as [A2 B2]; split; [exact A2|intros x; rewrite B2, B; cbn [bstrip iden]; rewrite bfresh_sound; reflexivity]. }
    split; [exact H1|apply Peel; [exact H1|intros [? ?]; discriminate]].
  - assert (H1 : forall st c, Forall okit st -> Forall okit (fst (rnormN F (AInner h t a) st c)) /\ forall x, wde (fst (rnormN F (AInner h t a) st c)) x = ca (AInner h t a) (wde st x)).
    { intros st c Hs; rewrite rnormN_inner.
      destruct (insert_b_sound F M HM (BF (fst (bfresh (entry h t) c))) st (bfresh_ok _ _) Hs) as [A B].
      destruct (IH2 [h] _ (snd (bfresh (entry h t) c)) A) as [A2 B2]; split; [exact A2|intros x; rewrite B2, B; cbn [bstrip iden rev app]; rewrite bfresh_sound].
      cbn [liftsem]; rewrite CSpec.entry_sound, cpop_push, chd_push; reflexivity. }
    split; [exact H1|apply Peel; [exact H1|intros [? ?]; discriminate]].
  - split.
    + intros st c Hs; rewrite rnormN_lift; destruct (IH2 [h] st c Hs) as [A B]; split; [exact A|intros x; rewrite B; reflexivity].
    + intros R st c Hs; cbn [peelN]; destruct (IH2 (h :: R) st c Hs) as [A B]; split; [exact A|].
      intros x; rewrite B; cbn [rev]; rewrite CSpec.liftsem_app; apply CSpec.liftsem_ext; reflexivity.
Qed.

Theorem rrunN_sound e x : wden M (rrunN F e) x = ca e x.
Proof. unfold rrunN; destruct (proj1 (rnormN_sound e) [] xH (Forall_nil _)) as [_ B]; rewrite B; reflexivity. Qed.

End SoundExp.

(** ** The normaliser: the pass, then [CNorm] *)

Definition crN_form (F : order) (e : aexp) : aexp := wexp (rrunN F e).

Theorem crN_form_sound F e : forall M, ccons F M -> forall x : cU M, ca (crN_form F e) x = ca e x.
Proof. intros M HM x; unfold crN_form; rewrite CSpec.wexp_sound, (rrunN_sound F M HM); reflexivity. Qed.

Definition crN_eq (F : order) (e1 e2 : aexp) : bool := cn_eq F (crN_form F e1) (crN_form F e2).

Theorem crN_eq_correct F
  (Hirr : forall a, lt_known F a a = false)
  (Htrans : forall a b c, lt_known F a b = true -> lt_known F b c = true -> lt_known F a c = true)
  e1 e2 : crN_eq F e1 e2 = true <-> cequal F e1 e2.
Proof.
  unfold crN_eq; rewrite (CComplete.cn_eq_correct F Hirr Htrans); split; intros H M HM x.
  - rewrite <- (crN_form_sound F e1 M HM x), <- (crN_form_sound F e2 M HM x); apply H, HM.
  - rewrite (crN_form_sound F e1 M HM x), (crN_form_sound F e2 M HM x); apply H, HM.
Qed.
