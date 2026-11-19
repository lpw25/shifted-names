(** * The context-form pass with binary depths

    [CRun2]'s pass, with the depths and name indices of reads, and the
    number of outputs of a form, in [N] instead of [nat].  Under a chain
    of [n] lifts a form has [n] restores reading depths [0 .. n-1]; in
    unary these alone have size [n²].

    List positions (which output, which input, which item) stay [nat]:
    each is used to walk a list that far, so converting one costs no more
    than the walk.

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

(** [CForm]'s forms, with binary targets. *)
Record bfm : Type := mkC { cout : list lexp; cin : list (lexp * btgt) }.

Definition ina (x : lexp * btgt) : lexp * tgt := (fst x, ta (snd x)).
Definition fa (f : bfm) : form := mkF (cout f) (map ina (cin f)).
Definition fb (f : form) : bfm := mkC (fout f) (map (fun x => (fst x, tb (snd x))) (fin f)).

(** [CRun2]'s forms, with binary targets and count. *)
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
    labels ordered against [l]. *)
Fixpoint bslot_go (l : lexp) (O : list lexp) (k j : nat) : option nat :=
  match k with
  | 0 => None
  | S k' =>
      match nth_error O j with
      | Some o => if lexp_eqb o l then Some j else if kd F l o then bslot_go l O k' (S j) else None
      | None => None
      end
  end.

Fixpoint ballkd (l : lexp) (L : list lexp) : bool :=
  match L with [] => true | o :: L' => if kd F l o then ballkd l L' else false end.

(** ** [CForm]'s steps, binary *)

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

Definition bset_in (p : nat) (t : btgt) (f : bfm) : bfm :=
  mkC (cout f) (mapi_from 0 (fun q '(l, s) => (l, if Nat.eqb q p then t else s)) (cin f)).

Fixpoint ballkd_in (l : lexp) (I : list (lexp * btgt)) : bool :=
  match I with [] => true | (m, _) :: I' => if kd F l m then ballkd_in l I' else false end.

Definition babsorb2 (p : nat) (f : bfm) : option (nat * bfm) :=
  match nth_error (cin f) p with
  | Some (l, BR z i d) =>
      if lexp_eqb z l then if N.eqb i 0 then
        match bslot_go l (cout f) (length (cout f)) (N.to_nat d) with
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

(** ** [CRun2]'s steps, binary *)

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

Definition cnt_b (m : PositiveMap.t nat) (d : N) : nat :=
  match PositiveMap.find (dkey_b d) m with Some c => c | None => 0 end.

Definition idx_add_b (m : PositiveMap.t nat) (t : btgt) : PositiveMap.t nat :=
  match t with BR _ _ d => PositiveMap.add (dkey_b d) (S (cnt_b m d)) m | BT _ _ => m end.

Definition idx_of_b (I : list (positive * (lexp * btgt))) : PositiveMap.t nat :=
  fold_left (fun m x => idx_add_b m (snd (snd x))) I (PositiveMap.empty nat).

Definition idx_move_b (m : PositiveMap.t nat) (d : N) : PositiveMap.t nat :=
  PositiveMap.add (dkey_b d) 0 (PositiveMap.add (dkey_b (N.succ d)) (cnt_b m (N.succ d) + cnt_b m d) m).

Definition swap_in_b (k : N) (b : lexp) (I : list (positive * (lexp * btgt))) : option (list (positive * (lexp * btgt))) :=
  omap (fun '(id, (l, t)) => option_map (fun t' => (id, (l, t'))) (bswap_read k b t)) I.

Fixpoint bub_out_b (x : positive * lexp) (acc : list (positive * lexp)) (pos : N)
    (I : list (positive * (lexp * btgt))) (mo : option (PositiveMap.t nat)) {struct acc} :
    list (positive * lexp) * list (positive * (lexp * btgt)) * option (PositiveMap.t nat) :=
  match acc with
  | [] => ([x], I, mo)
  | y :: acc' =>
      if before F (snd x) (snd y) then
        let m := match mo with Some m => m | None => idx_of_b I end in
        match cnt_b m pos with
        | 0 => let '(r, I', mo') := bub_out_b x acc' (N.pred pos) I (Some m) in (y :: r, I', mo')
        | S _ =>
            match swap_in_b (N.pred pos) (snd x) I with
            | Some I' => let '(r, I'', mo') := bub_out_b x acc' (N.pred pos) I' (Some (idx_move_b m pos)) in (y :: r, I'', mo')
            | None => (x :: acc, I, Some m)
            end
        end
      else (x :: acc, I, mo)
  end.

Fixpoint place_rng_b (k n : N) (rng above : list (positive * lexp)) (I : list (positive * (lexp * btgt)))
    (mo : option (PositiveMap.t nat)) : list (positive * lexp) * list (positive * (lexp * btgt)) * option (PositiveMap.t nat) :=
  match rng with
  | [] => (above, I, mo)
  | x :: rng' =>
      let '(a', I', mo') := place_rng_b (N.succ k) n rng' above I mo in
      bub_out_b x a' (n - 1 - k) I' mo'
  end.

Definition place_out_bottom_b (r : nat) (e : bform) : bform :=
  let '(o, Is, _) := place_rng_b 0 (bl e) (firstn r (bo e)) (skipn r (bo e)) (bi e) None in mkB o (bl e) Is.

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

Fixpoint bub_down_b (x : positive * lexp) (below : list (positive * lexp)) (pos : N)
    (I : list (positive * (lexp * btgt))) (mo : option (PositiveMap.t nat)) {struct below} :
    list (positive * lexp) * list (positive * (lexp * btgt)) * option (PositiveMap.t nat) :=
  match below with
  | [] => ([x], I, mo)
  | y :: below' =>
      if before F (snd y) (snd x) then
        let m := match mo with Some m => m | None => idx_of_b I end in
        match cnt_b m (N.succ pos) with
        | 0 => let '(r, I', mo') := bub_down_b x below' (N.succ pos) I (Some m) in (y :: r, I', mo')
        | S _ =>
            match swap_in_b pos (snd y) I with
            | Some I' => let '(r, I'', mo') := bub_down_b x below' (N.succ pos) I' (Some (idx_move_b m (N.succ pos))) in (y :: r, I'', mo')
            | None => (x :: below, I, Some m)
            end
        end
      else (x :: below, I, mo)
  end.

Fixpoint place_down_b (k : N) (pre rest : list (positive * lexp)) (I : list (positive * (lexp * btgt)))
    (mo : option (PositiveMap.t nat)) : list (positive * lexp) * list (positive * (lexp * btgt)) * option (PositiveMap.t nat) :=
  match pre with
  | [] => (rest, I, mo)
  | x :: pre' =>
      let '(r', I', mo') := place_down_b (N.succ k) pre' rest I mo in
      bub_down_b x r' k I' mo'
  end.

Definition place_out_top_b (r : nat) (e : bform) : bform :=
  let top := rev' (bo e) in
  let '(o, Is, _) := place_down_b 0 (firstn r top) (skipn r top) (bi e) None in mkB (rev' o) (bl e) Is.

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

Lemma bslot_go_sound l O k j j' y : bslot_go F l O k j = Some j' -> cname l 0 (popn O j' y) = cname l 0 (popn O j y).
Proof.
  revert j; induction k as [|k IH]; intros j; cbn; [discriminate|].
  destruct (nth_error O j) as [o|] eqn:N; [|discriminate].
  destruct (lexp_eqb o l) eqn:E; [intros H; injection H as <-; reflexivity|].
  destruct (kd F l o) eqn:K; [|discriminate]; intros H; rewrite (IH _ H).
  assert (L : j < length O) by (apply nth_error_Some; congruence).
  rewrite (popn_S O j y L), (nth_error_nth O j LNone N); apply cname_pop_other, kdk, K.
Qed.

Lemma bpushes_mapi O (g : nat -> lexp * btgt -> lexp * btgt) I k b x :
  (forall q l t, nth_error I q = Some (l, t) -> fst (g (k + q) (l, t)) = l /\ tden O (ta (snd (g (k + q) (l, t)))) x = tden O (ta t) x) ->
  pushes O (map ina (mapi_from k g I)) b x = pushes O (map ina I) b x.
Proof.
  revert k; induction I as [|[l t] I IH]; intros k H; [reflexivity|]; cbn [mapi_from map pushes].
  destruct (g k (l, t)) as [l' t'] eqn:G; destruct (H 0 l t eq_refl) as [H1 H2]; rewrite Nat.add_0_r, G in H1, H2; cbn in H1, H2; subst l'.
  rewrite !ina_pair; cbn [pushes]; rewrite IH, H2; [reflexivity|]; intros q l2 t2 N; replace (S k + q) with (k + S q) by lia; apply (H (S q)), N.
Qed.

Lemma babsorb2_sound p f j g x : babsorb2 F p f = Some (j, g) -> fden (fa g) x = fden (fa f) x.
Proof.
  unfold babsorb2; destruct (nth_error (cin f) p) as [[l [z i d|u q]]|] eqn:Np; try discriminate.
  destruct (lexp_eqb z l) eqn:C1; [|discriminate]; destruct (N.eqb i 0) eqn:C2; [|discriminate].
  apply lexp_eqb_true in C1; apply N.eqb_eq in C2; subst z i.
  destruct (bslot_go F l (cout f) (length (cout f)) (N.to_nat d)) as [j'|] eqn:S; [|discriminate].
  destruct (ballkd F l _); [|discriminate]; destruct (ballkd_in F l _); [|discriminate].
  destruct (babsorb_at F j' p (bset_in p (BR l 0 (N.of_nat j')) f)) as [g'|] eqn:A; cbn [option_map]; [|discriminate].
  intros H; injection H as <- <-.
  rewrite (babsorb_at_sound _ _ _ _ x A).
  unfold bset_in, fa, fden; cbn [cout cin fout fin]; apply bpushes_mapi; intros q l' t N; cbn.
  split; [reflexivity|]; destruct (Nat.eqb q p) eqn:Q; [|reflexivity].
  apply Nat.eqb_eq in Q; subst q; rewrite Np in N; injection N as <- <-; cbn [tden ta].
  rewrite Nat2N.id, N0nat; apply (bslot_go_sound _ _ _ _ _ _ S).
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
