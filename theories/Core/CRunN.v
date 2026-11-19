(** * The context-form pass with binary depths

    [CRun2]'s pass, with the depths and name indices of reads, and the
    number of outputs of a form, in [N] instead of [nat].  Under a chain
    of [n] lifts a form has [n] restores reading depths [0 .. n-1]; in
    unary these alone have size [n²].

    List positions (which output, which input, which item) stay [nat]:
    each is used to walk a list that far, so converting one costs no more
    than the walk.

    [rrunN] is proved equal to [CRun2.rrun2] ([rrunN_eq]): every function
    here, mapped back to [nat], is the function of [CRun2] (or [CForm],
    [CRun]) it mirrors.  Soundness and [crN_eq_correct] follow. *)

From Stdlib Require Import List Bool Arith Lia PArith NArith FMapPositive.
From ShiftedNames.Core Require Import Label Normalise GEval CNorm Comp CSound CComplete CForm CRun CRun2.
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

Definition iina (x : positive * (lexp * btgt)) : positive * (lexp * tgt) := (fst x, ina (snd x)).
Definition ea (e : bform) : eform := mkE (bo e) (N.to_nat (bl e)) (map iina (bi e)).
Definition ia (it : bitem) : eitem := match it with BF f => KF (ea f) | BA L n => KA L n end.

Definition b_to_c (e : bform) : bfm := mkC (rev' (map snd (bo e))) (map snd (bi e)).

Definition bclamp (n : N) (t : btgt) : btgt :=
  match t with BR z i d => BR z i (N.min d n) | BT _ _ => t end.

Definition bof_i (g : bfm) (oids iids : list positive) : bform :=
  let n := N.of_nat (length (cout g)) in
  mkB (rev' (zipd oids (cout g))) n (zipd iids (map (fun x => (fst x, bclamp n (snd x))) (cin g))).

Definition bis_dep (j : N) (t : btgt) : bool := match t with BR _ _ d => N.eqb d j | BT _ _ => false end.

Fixpoint mapi_fromN {X Y} (k : N) (g : N -> X -> Y) (l : list X) : list Y :=
  match l with [] => [] | a :: l' => g k a :: mapi_fromN (N.succ k) g l' end.

Section RunN.

Variable F : order.

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
        match slot_go F l (cout f) (length (cout f)) (N.to_nat d) with
        | Some j =>
            if allkd F l (skipn (S j) (cout f)) then if ballkd_in l (skipn (S p) (cin f)) then
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

Fixpoint moves_b (fuel k : nat) (f1 f2 : bform) (cands : list positive) (acc : work) : bform * bform * work :=
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

Definition step_b (s : list bitem * work) : list bitem * work :=
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

Fixpoint settle_b (p : positive) (s : list bitem * work) : list bitem * work :=
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
  | BF f => if iempty_b f then st else fst (settle_b big (it :: st, [(0, None)]))
  | BA _ _ => it :: st
  end.

(** ** Expressions *)

Definition fresh_b (f : form) (c : positive) : bform * positive :=
  let '(g, c') := fresh f c in (bof_i (fb (ff g)) (oids g) (iids g), c').

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
  | AOuter h a => let '(f, c1) := fresh_b (weak h) c in rnormN a (insert_b (BF f) st) c1
  | AInner h t a =>
      let '(f, c1) := fresh_b (entry h t) c in
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

Definition rrunN (e : aexp) : fword := map (fun it => estrip (ia it)) (fst (rnormN e [] xH)).

End RunN.

(** ** Mapped back to [nat], the functions of [CRun2] *)

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

Lemma ta_bclamp n t : ta (bclamp n t) = clamp (N.to_nat n) (ta t).
Proof. destruct t; cbn; nnorm; reflexivity. Qed.

Lemma map_iina_zipd ids (l : list (lexp * btgt)) : map iina (zipd ids l) = zipd ids (map ina l).
Proof. revert ids; induction l as [|x l IH]; intros [|i ids]; cbn; rewrite ?IH; reflexivity. Qed.

Lemma ea_bof_i g o i : ea (bof_i g o i) = of_i (mkI (fa g) o i).
Proof.
  unfold ea, bof_i, of_i, fa; cbn; rewrite Nat2N.id; f_equal; [apply rev'_rev|].
  rewrite map_iina_zipd, !map_map; f_equal; apply map_ext; intros [l t]; unfold ina; cbn; rewrite ta_bclamp, Nat2N.id; reflexivity.
Qed.

Lemma fa_b_to_c e : fa (b_to_c e) = eff (ea e).
Proof. unfold fa, b_to_c, eff, ea; cbn; rewrite rev'_rev, !map_map; reflexivity. Qed.

Lemma ob_ea e : ob (ea e) = bo e. Proof. reflexivity. Qed.
Lemma ol_ea e : ol (ea e) = N.to_nat (bl e). Proof. reflexivity. Qed.
Lemma ei_ea e : ei (ea e) = map iina (bi e). Proof. reflexivity. Qed.

Section Refine.

Variable F : order.

(** *** [CForm]'s steps *)

Lemma bswap_read_eq k b t : option_map ta (bswap_read F k b t) = swap_read F (N.to_nat k) b (ta t).
Proof.
  destruct t as [z i d|u p]; cbn [bswap_read swap_read ta]; [|reflexivity].
  nnorm; destruct (Nat.eqb _ _); [|reflexivity].
  destruct (lexp_eqb z b); [ncase i; cbn [option_map ta]; nnorm; npos; reflexivity|].
  destruct (kd F z b); cbn; nnorm; reflexivity.
Qed.

Lemma bdrop_read_eq j l t : option_map ta (bdrop_read F j l t) = drop_read F (N.to_nat j) l (ta t).
Proof.
  destruct t as [z i d|u p]; cbn [bdrop_read drop_read ta]; [|reflexivity].
  nnorm; destruct (Nat.leb _ _); [reflexivity|].
  destruct (lexp_eqb z l); [cbn; nnorm; reflexivity|].
  destruct (kd F z l); cbn; nnorm; reflexivity.
Qed.

Lemma nth_error_ina I p : nth_error (map ina I) p = option_map ina (nth_error I p).
Proof. apply nth_error_map. Qed.

Lemma forallb_ina (P : lexp -> bool) I : forallb (fun '(m, _) => P m) (map ina I) = forallb (fun '(m, _) => P m) I.
Proof. induction I as [|[m t] I IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma babsorb_at_eq j p f : option_map fa (babsorb_at F j p f) = absorb_at F j p (fa f).
Proof.
  unfold babsorb_at, absorb_at; cbn [fa fout fin cout cin]; rewrite nth_error_ina.
  destruct (nth_error (cout f) j) as [l|]; [|reflexivity].
  destruct (nth_error (cin f) p) as [[l' [z i d|u q]]|]; cbn [option_map ina fst snd ta]; try reflexivity.
  rewrite !Neqb_nat, !Nat2N.id, N0nat, skipn_map, forallb_ina.
  destruct (_ && _); [|reflexivity].
  rewrite remove_at_map.
  pose proof (omap_comm ina ina (fun '(m, t) => option_map (fun t' => (m, t')) (bdrop_read F (N.of_nat j) l t))
    (fun '(m, t) => option_map (fun t' => (m, t')) (drop_read F j l t))) as H.
  rewrite <- H; [destruct (omap _ _); reflexivity|].
  intros [m t]; cbn; rewrite <- (Nat2N.id j) at 2; rewrite <- bdrop_read_eq; destruct (bdrop_read F _ l t); reflexivity.
Qed.

Lemma fa_bset_in p t f : fa (bset_in p t f) = set_in p (ta t) (fa f).
Proof.
  unfold fa, bset_in, set_in; cbn; f_equal; rewrite map_mapi_from; symmetry; apply mapi_from_map.
  intros q [l s]; cbn; destruct (Nat.eqb q p); reflexivity.
Qed.

Lemma ballkd_in_eq l I : ballkd_in F l I = allkd_in F l (map ina I).
Proof. induction I as [|[m t] I IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma babsorb2_eq p f : option_map (fun '(j, g) => (j, fa g)) (babsorb2 F p f) = absorb2 F p (fa f).
Proof.
  unfold babsorb2, absorb2; cbn [fa fout fin cout cin]; rewrite nth_error_ina.
  destruct (nth_error (cin f) p) as [[l [z i d|u q]]|]; cbn [option_map ina fst snd ta]; try reflexivity.
  destruct (lexp_eqb z l); [|reflexivity]; rewrite Neqb_nat, N0nat.
  destruct (Nat.eqb _ 0); [|reflexivity].
  destruct (slot_go F l (cout f) (length (cout f)) (N.to_nat d)) as [j|]; [|reflexivity].
  destruct (allkd F l _); [|reflexivity]; rewrite skipn_map, <- ballkd_in_eq.
  destruct (ballkd_in F l _); [|reflexivity].
  pose proof (babsorb_at_eq j p (bset_in p (BR l 0 (N.of_nat j)) f)) as H.
  rewrite fa_bset_in in H; cbn [ta] in H; rewrite Nat2N.id, N0nat in H; rewrite <- H.
  destruct (babsorb_at F _ _ _); reflexivity.
Qed.

Lemma btop_read_eq j o t : option_map ta (btop_read F j o t) = top_read F (N.to_nat j) o (ta t).
Proof.
  destruct t as [z i d|u p]; cbn [btop_read top_read ta]; [|reflexivity].
  nnorm; destruct (Nat.ltb _ _); [cbn; nnorm; reflexivity|].
  destruct (lexp_eqb z o); [ncase i; cbn [option_map ta]; nnorm; npos; reflexivity|].
  destruct (kd F z o); reflexivity.
Qed.

Lemma bout_first_eq j f : option_map (fun '(o, g) => (o, fa g)) (bout_first F j f) = out_first F j (fa f).
Proof.
  unfold bout_first, out_first; cbn [fa fout fin cout cin].
  destruct (nth_error (cout f) j) as [o|]; [|reflexivity].
  destruct (forallb _ _); [|reflexivity].
  pose proof (omap_comm ina ina (fun '(m, t) => option_map (fun t' => (m, t')) (btop_read F (N.of_nat j) o t))
    (fun '(m, t) => option_map (fun t' => (m, t')) (top_read F j o t))) as H.
  rewrite <- H; [destruct (omap _ _); reflexivity|].
  intros [m t]; cbn; rewrite <- (Nat2N.id j) at 2; rewrite <- btop_read_eq; destruct (btop_read F _ o t); reflexivity.
Qed.

Lemma bpull_eq O d z i : option_map N.to_nat (bpull F O d z i) = pull F O d z (N.to_nat i).
Proof.
  revert d; induction O as [|o O IH]; intros [|d]; cbn [bpull pull]; try reflexivity.
  rewrite <- IH; destruct (bpull F O d z i); [|reflexivity]; cbn.
  destruct (lexp_eqb o z); [cbn [option_map]; nnorm; reflexivity|]; destruct (kd F z o); reflexivity.
Qed.

Lemma bunder_read_eq h t : option_map ta (bunder_read F h t) = under_read F h (ta t).
Proof.
  destruct t as [z i d|u p]; cbn [bunder_read under_read ta]; [|reflexivity].
  destruct (lexp_eqb z h); [cbn; nnorm; reflexivity|]; destruct (kd F z h); reflexivity.
Qed.

Lemma bin_first_eq p f : option_map (fun '(h, t, g) => (h, ta t, fa g)) (bin_first F p f) = in_first F p (fa f).
Proof.
  unfold bin_first, in_first; cbn [fa fout fin cout cin]; rewrite nth_error_ina.
  destruct (nth_error (cin f) p) as [[h t]|]; cbn [option_map ina fst snd]; [|reflexivity].
  rewrite skipn_map, forallb_ina.
  destruct (_ && _); [|reflexivity].
  rewrite remove_at_map.
  pose proof (omap_comm ina ina (fun '(m, s) => option_map (fun s' => (m, s')) (bunder_read F h s))
    (fun '(m, s) => option_map (fun s' => (m, s')) (under_read F h s))) as H.
  rewrite <- H; [|intros [m s]; cbn; rewrite <- bunder_read_eq; destruct (bunder_read F h s); reflexivity].
  destruct t as [z i d|u q]; cbn [ta].
  - rewrite <- bpull_eq; destruct (bpull F _ _ z i); cbn; [|reflexivity].
    destruct (omap _ _); reflexivity.
  - destruct (omap _ _); reflexivity.
Qed.

End Refine.

Lemma ea_mk o n I : ea (mkB o n I) = mkE o (N.to_nat n) (map iina I).
Proof. reflexivity. Qed.

Lemma map_front_comm {X Y} (g : X -> Y) (h : X -> X) (h' : Y -> Y) n l :
  (forall x, g (h x) = h' (g x)) -> map g (map_front n h l) = map_front n h' (map g l).
Proof. intros H; revert l; induction n as [|n IH]; intros [|a l]; cbn; auto; rewrite H, IH; reflexivity. Qed.

Lemma fold_left_map' {X Y Z} (f : Z -> Y -> Z) (g : X -> Y) l a : fold_left f (map g l) a = fold_left (fun a x => f a (g x)) l a.
Proof. revert a; induction l as [|x l IH]; intros a; cbn; [reflexivity|apply IH]. Qed.

Lemma Forall_last {X} (P : X -> Prop) l d : Forall P l -> P d -> P (last l d).
Proof. induction 1 as [|x l Hx Hl IH]; intros Hd; [exact Hd|]; destruct l; [exact Hx|apply IH, Hd]. Qed.

Definition tr3 (r : list (positive * lexp) * list (positive * (lexp * btgt)) * option (PositiveMap.t nat)) :=
  (fst (fst r), map iina (snd (fst r)), snd r).

Definition st_a (s : list (positive * (lexp * btgt)) * (list (positive * lexp) * N)) :
  list (positive * (lexp * tgt)) * list (positive * lexp) := (map iina (fst s), rev (fst (snd s))).

Definition npok (s : list (positive * (lexp * btgt)) * (list (positive * lexp) * N)) : Prop :=
  snd (snd s) = N.of_nat (length (fst (snd s))).

Definition smap (x : btgt + N) : tgt + nat := match x with inl t => inl (ta t) | inr n => inr (N.to_nat n) end.

Lemma dkey_b_eq d : dkey_b d = dkey (N.to_nat d).
Proof. destruct d as [|p]; [reflexivity|]; unfold dkey_b, dkey; cbn; symmetry; apply Pos2SuccNat.id_succ. Qed.

Lemma cnt_b_eq m d : cnt_b m d = cnt m (N.to_nat d).
Proof. unfold cnt_b, cnt; rewrite dkey_b_eq; reflexivity. Qed.

Lemma idx_add_b_eq m t : idx_add_b m t = idx_add m (ta t).
Proof. destruct t; cbn; [rewrite dkey_b_eq, cnt_b_eq|]; reflexivity. Qed.

Lemma idx_of_b_eq I : idx_of_b I = idx_of (map iina I).
Proof.
  unfold idx_of_b, idx_of; rewrite fold_left_map'; generalize (PositiveMap.empty nat); induction I as [|x I IH]; intros m; cbn; [reflexivity|].
  rewrite idx_add_b_eq; apply IH.
Qed.

Lemma idx_move_b_eq m d : idx_move_b m d = idx_move m (N.to_nat d).
Proof. unfold idx_move_b, idx_move; rewrite !dkey_b_eq, !cnt_b_eq, N2Nat.inj_succ; reflexivity. Qed.

Section Refine2.

Variable F : order.

Lemma nread_up_b_eq up z i d : ta (nread_up_b F up z i d) = nread_up F up z (N.to_nat i) (N.to_nat d).
Proof.
  revert i d; induction up as [|[id o] up IH]; intros i d; destruct d as [|q]; cbn [nread_up_b]; try reflexivity;
    destruct (Npos_succ q) as [m [H1 H2]]; rewrite H1; cbn [nread_up].
  - cbn [ta]; rewrite H1; reflexivity.
  - destruct (lexp_eqb o z); [rewrite IH, N2Nat.inj_succ, H2; reflexivity|].
    destruct (kd F z o); [rewrite IH, H2; reflexivity|cbn [ta]; rewrite H1; reflexivity].
Qed.

Lemma nread_e_b_eq e t : ta (nread_e_b F e t) = nread_e F (ea e) (ta t).
Proof.
  destruct t as [z i d|u p]; cbn [nread_e_b nread_e ta]; [|reflexivity].
  rewrite ol_ea, Nleb_nat; destruct (Nat.leb _ _); [|reflexivity].
  rewrite ob_ea, N2Nat.inj_sub; apply nread_up_b_eq.
Qed.

Lemma reread_front_b_eq n e : ea (reread_front_b F n e) = reread_front F n (ea e).
Proof.
  unfold reread_front_b, reread_front; rewrite ea_mk, ob_ea, ol_ea, ei_ea; f_equal.
  apply map_front_comm; intros [id [l t]]; cbn; unfold iina, ina; cbn; rewrite nread_e_b_eq; reflexivity.
Qed.

Lemma bis_dep_eq j t : bis_dep (N.of_nat j) t = is_dep j (ta t).
Proof. destruct t; cbn; [rewrite Neqb_nat, Nat2N.id|]; reflexivity. Qed.

Lemma reread_at_b_eq j e : ea (reread_at_b F j e) = reread_at F j (ea e).
Proof.
  unfold reread_at_b, reread_at; rewrite ea_mk, ob_ea, ol_ea, ei_ea; f_equal.
  rewrite !map_map; apply map_ext; intros [id [l t]]; cbn; unfold iina, ina; cbn.
  rewrite <- bis_dep_eq; destruct (bis_dep _ t); [rewrite nread_e_b_eq|]; reflexivity.
Qed.

Lemma bub_in_b_eq x I : map iina (bub_in_b F x I) = bub_in F (iina x) (map iina I).
Proof. induction I as [|y I IH]; cbn; [reflexivity|]; destruct (before _ _ _); cbn; rewrite ?IH; reflexivity. Qed.

Lemma place_front_b_eq n I : map iina (place_front_b F n I) = place_front F n (map iina I).
Proof. revert I; induction n as [|n IH]; intros [|x I]; cbn; auto; rewrite bub_in_b_eq, IH; reflexivity. Qed.

Lemma ins_out_b_eq x I : map iina (ins_out_b F x I) = ins_out F (iina x) (map iina I).
Proof. induction I as [|y I IH]; cbn; [reflexivity|]; destruct (before _ _ _); cbn; rewrite ?IH; reflexivity. Qed.

Lemma out_pass_b_eq rp suf : map iina (out_pass_b F rp suf) = out_pass F (map iina rp) (map iina suf).
Proof.
  revert rp; induction suf as [|x suf IH]; intros rp; cbn; [rewrite rev'_rev, map_rev; reflexivity|].
  rewrite IH, ins_out_b_eq; reflexivity.
Qed.

Lemma place_suffix_out_b_eq p I : map iina (place_suffix_out_b F p I) = place_suffix_out F p (map iina I).
Proof. unfold place_suffix_out_b, place_suffix_out; rewrite out_pass_b_eq, rev'_rev, map_rev, firstn_map, skipn_map; reflexivity. Qed.

Lemma swap_in_b_eq k b I : option_map (map iina) (swap_in_b F k b I) = swap_in F (N.to_nat k) b (map iina I).
Proof.
  apply omap_comm; intros [id [l t]]; cbn; rewrite <- bswap_read_eq; destruct (bswap_read F k b t); reflexivity.
Qed.

Lemma bub_out_b_eq x acc pos I mo : tr3 (bub_out_b F x acc pos I mo) = bub_out F x acc (N.to_nat pos) (map iina I) mo.
Proof.
  revert pos I mo; induction acc as [|y acc IH]; intros pos I mo; cbn [bub_out_b bub_out]; [reflexivity|].
  destruct (before F (snd x) (snd y)); [|reflexivity].
  rewrite <- idx_of_b_eq; generalize (match mo with Some m => m | None => idx_of_b I end) as m; intros m.
  rewrite cnt_b_eq; destruct (cnt m (N.to_nat pos)) as [|c].
  - rewrite <- N2Nat.inj_pred, <- IH; destruct (bub_out_b F x acc (N.pred pos) I (Some m)) as [[r I'] mo']; reflexivity.
  - rewrite <- N2Nat.inj_pred, <- swap_in_b_eq; destruct (swap_in_b F (N.pred pos) (snd x) I) as [I'|]; cbn [option_map]; [|reflexivity].
    rewrite <- idx_move_b_eq, <- IH; destruct (bub_out_b F x acc _ I' _) as [[r I''] mo']; reflexivity.
Qed.

Lemma place_rng_b_eq k n rng above I mo :
  tr3 (place_rng_b F k n rng above I mo) = place_rng F (N.to_nat k) (N.to_nat n) rng above (map iina I) mo.
Proof.
  revert k; induction rng as [|x rng IH]; intros k; cbn [place_rng_b place_rng]; [reflexivity|].
  rewrite <- N2Nat.inj_succ, <- IH; destruct (place_rng_b F (N.succ k) n rng above I mo) as [[a' I'] mo']; cbn [tr3 fst snd].
  rewrite bub_out_b_eq, !N2Nat.inj_sub; reflexivity.
Qed.

Lemma place_out_bottom_b_eq r e : ea (place_out_bottom_b F r e) = place_out_bottom F r (ea e).
Proof.
  unfold place_out_bottom_b, place_out_bottom; rewrite ob_ea, ol_ea, ei_ea.
  pose proof (place_rng_b_eq 0 (bl e) (firstn r (bo e)) (skipn r (bo e)) (bi e) None) as H; change (N.to_nat 0) with 0 in H.
  rewrite <- H; destruct (place_rng_b F 0 (bl e) _ _ (bi e) None) as [[o Is] mo]; reflexivity.
Qed.

Lemma popin_b_eq o rem : option_map (option_map (map iina)) (popin_b F o rem) = popin_e F o (map iina rem).
Proof.
  induction rem as [|y r IH]; cbn [popin_b popin_e map]; [reflexivity|].
  change (lab_i (iina y)) with (blab y).
  destruct (lexp_eqb (blab y) o); [reflexivity|]; destruct (kd F (blab y) o); [|reflexivity].
  rewrite <- IH; destruct (popin_b F o r) as [[r'|]|]; reflexivity.
Qed.

Lemma popall_b_eq O1 rem pr np canc :
  option_map (fun r => (map st_a (fst r), snd r)) (popall_b F O1 rem pr np canc) = popall_e F O1 (map iina rem) (rev pr) canc.
Proof.
  revert rem pr np canc; induction O1 as [|[y o] O1 IH]; intros rem pr np canc; cbn [popall_b popall_e]; [reflexivity|].
  rewrite <- popin_b_eq; destruct (popin_b F o rem) as [[rem'|]|]; cbn [option_map].
  - rewrite <- (IH rem' pr np true); destruct (popall_b F O1 rem' pr np true) as [[st c]|]; reflexivity.
  - specialize (IH rem ((y, o) :: pr) (N.succ np) canc); cbn [rev] in IH; rewrite <- IH.
    destruct (popall_b F O1 rem _ _ canc) as [[st c]|]; reflexivity.
  - reflexivity.
Qed.

Lemma popall_b_np O1 rem pr np canc st c : popall_b F O1 rem pr np canc = Some (st, c) -> np = N.of_nat (length pr) -> Forall npok st.
Proof.
  revert rem pr np canc st c; induction O1 as [|[y o] O1 IH]; intros rem pr np canc st c; cbn [popall_b].
  - intros H Hn; injection H as <- _; constructor; [exact Hn|constructor].
  - destruct (popin_b F o rem) as [[rem'|]|]; [| |discriminate].
    + destruct (popall_b F O1 rem' pr np true) as [[st' c']|] eqn:E; cbn; [|discriminate].
      intros H Hn; injection H as <- _; constructor; [exact Hn|apply (IH _ _ _ _ _ _ E Hn)].
    + destruct (popall_b F O1 rem ((y, o) :: pr) (N.succ np) canc) as [[st' c']|] eqn:E; cbn; [|discriminate].
      intros H Hn; injection H as <- _; constructor; [exact Hn|apply (IH _ _ _ _ _ _ E)].
      cbn [length]; rewrite Nat2N.inj_succ, Hn; reflexivity.
Qed.

Lemma rthrough_b_eq rem z i : option_map smap (rthrough_b F rem z i) = rthrough_e F (map iina rem) z (N.to_nat i).
Proof.
  revert i; induction rem as [|[id [l t]] r IH]; intros i; cbn [rthrough_b rthrough_e map iina ina fst snd]; [reflexivity|].
  destruct (lexp_eqb l z).
  - destruct i as [|q]; [reflexivity|]; destruct (Npos_succ q) as [m [H1 H2]].
    cbv iota beta; rewrite H1, IH, H2; reflexivity.
  - destruct (kd F l z); [apply IH|reflexivity].
Qed.

Lemma newt_b_eq f2 st t : Forall npok st -> option_map ta (newt_b F f2 st t) = newt_e F (ea f2) (map st_a st) (ta t).
Proof.
  intros Hst; destruct t as [z i d|u p]; cbn [newt_b newt_e ta].
  - rewrite nth_error_map; destruct (nth_error st (N.to_nat d)) as [[rem [pr np]]|] eqn:E; cbn [option_map st_a fst snd]; [|reflexivity].
    assert (Hn : np = N.of_nat (length pr)).
    { rewrite Forall_forall in Hst; apply (Hst _ (nth_error_In _ _ E)). }
    rewrite <- rthrough_b_eq; destruct (rthrough_b F rem z i) as [[t'|i']|]; cbn; try reflexivity.
    rewrite N2Nat.inj_add, Hn, Nat2N.id, length_rev; reflexivity.
  - rewrite fa_b_to_c; reflexivity.
Qed.

Lemma ecompose_b_eq f1 f2 :
  option_map (fun '(g, a, b, c) => (ea g, a, b, c)) (ecompose_b F f1 f2) = ecompose F (ea f1) (ea f2).
Proof.
  unfold ecompose_b, ecompose; rewrite ob_ea, ei_ea, rev'_rev.
  pose proof (popall_b_eq (rev (bo f1)) (bi f2) [] 0 false) as H; cbn [rev] in H; rewrite <- H.
  destruct (popall_b F (rev (bo f1)) (bi f2) [] 0 false) as [[st canc]|] eqn:E; cbn [option_map fst snd]; [|reflexivity].
  pose proof (popall_b_np _ _ _ _ _ _ _ E eq_refl) as Hst.
  change ([] : list (positive * (lexp * tgt)), [] : list (positive * lexp)) with (st_a ([], ([], 0%N))).
  rewrite last_map.
  pose proof (Forall_last _ _ ([], ([], 0%N)) Hst eq_refl) as Hl.
  destruct (last st ([], ([], 0%N))) as [rem [pr np]]; cbn [st_a fst snd]; unfold npok in Hl; cbn [fst snd] in Hl.
  rewrite ei_ea.
  pose proof (omap_comm iina iina (fun '(id, (l, t)) => option_map (fun t' => (id, (l, t'))) (newt_b F f2 st t))
    (fun '(id, (l, t)) => option_map (fun t' => (id, (l, t'))) (newt_e F (ea f2) (map st_a st) t))) as H2.
  rewrite <- H2; [|intros [id [l t]]; cbn; rewrite <- newt_b_eq by exact Hst; destruct (newt_b F f2 st t); reflexivity].
  destruct (omap _ (bi f1)) as [I1|]; cbn [option_map]; [|reflexivity].
  rewrite ea_mk, ob_ea, ol_ea, rev_involutive, map_app, N2Nat.inj_add, Hl, Nat2N.id, length_rev, rev'_rev, map_rev, map_map.
  reflexivity.
Qed.

End Refine2.
