(** * The layered form of a stored normal form (prototype)

    See "Layered form" in [docs/normal-forms.md].  [layers] turns a
    stored word and its table into an expression that is a composition
    of small steps: the root's renaming, then for each height of terms a
    renaming followed by a layer of instantiations of bound variables,
    then what every party agrees on.  Nothing here is verified;
    [layers_check] normalises the result again and compares.

    Not done yet: sharing atoms.  A term carried past an atom keeps the
    atom in its payload, as in the stored form. *)

From Stdlib Require Import Arith List Lia Bool NArith.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Unique Normal Complete Shared Eval.
Import ListNotations.

Notation ent := (lexp * list ntgt * nat)%type.

Inductive ref : Type :=
| RName (h : lexp) (i : nat)
| RSlot (t : ntgt)
| RBound (r : nat).

Notation sent := (lexp * list ref * nat)%type.

Fixpoint opt_all {A} (l : list (option A)) : option (list A) :=
  match l with
  | [] => Some []
  | Some x :: r => match opt_all r with Some xs => Some (x :: xs) | None => None end
  | None :: _ => None
  end.

Definition is_lnone (h : lexp) : bool := match h with LNone => true | _ => false end.
Definition isterm (t : ntgt) : bool := match t with NBind _ _ _ => true | NVar _ _ => false end.
Definition tmem (t : ntgt) (l : list ntgt) : bool := existsb (ntgt_eqb t) l.

Fixpoint tindex (t : ntgt) (l : list ntgt) : option nat :=
  match l with
  | [] => None
  | x :: r => if ntgt_eqb t x then Some 0 else option_map S (tindex t r)
  end.

Fixpoint efind (x : lexp) (es : list ent) : option (list ntgt * nat) :=
  match es with
  | [] => None
  | (h, ts, m) :: r => if lexp_eqb x h then Some (ts, m) else efind x r
  end.

Definition etgts (es : list ent) : list ntgt := flat_map (fun '(_, ts, _) => ts) es.

(** Common suffix. *)
Fixpoint cpre (a b : list ntgt) : list ntgt :=
  match a, b with
  | x :: a', y :: b' => if ntgt_eqb x y then x :: cpre a' b' else []
  | _, _ => []
  end.

Definition csuf (a b : list ntgt) : list ntgt := rev (cpre (rev a) (rev b)).

Fixpoint takew (l : list ntgt) : list ntgt :=
  match l with x :: r => if isterm x then x :: takew r else [] | [] => [] end.

(** ** Expressions for segments *)

Definition mkseg (es : list (lexp * list texp * nat)) : aexp :=
  fold_right (fun '(h, ts, _) acc => fold_right (fun t a => AInner h t a) acc ts)
    (fold_right (fun '(h, _, m) acc => iter m (AOuter h) acc) AId es) es.

Definition alifts (L : list (lexp * nat)) (x : aexp) : aexp :=
  fold_right (fun '(h, n) acc => iter n (ALift h) acc) x L.

Definition stexp (t : ntgt) : texp :=
  match t with
  | NVar h i => TVarE h i
  | NBind u _ b => TBindE u (match b with Some n => PAtom n | None => PId end)
  end.

Definition sexp (s : seg) : aexp := mkseg (map (fun '(h, ts, m) => (h, map stexp ts, m)) (sents s)).

Fixpoint waexp (w : word) : aexp :=
  match w with
  | WEnd s => sexp s
  | WAtom s L a w' => ACompose (sexp s) (ACompose (alifts L (AAtom a)) (waexp w'))
  end.

Definition is_aid (e : aexp) : bool := match e with AId => true | _ => false end.

(** [steps], first applied first, composed so that the normaliser builds
    the result from its end. *)
Definition compose_steps (steps : list aexp) : aexp :=
  match rev (filter (fun e => negb (is_aid e)) steps) with
  | [] => AId
  | e :: r => fold_left (fun acc x => ACompose acc x) r e
  end.

Fixpoint asize (e : aexp) : nat :=
  match e with
  | AId | AAtom _ => 1
  | ACompose a b => S (asize a + asize b)
  | AOuter _ a | ALift _ a => S (asize a)
  | AInner _ t a => S (tsize t + asize a)
  end
with tsize (t : texp) : nat :=
  match t with
  | TVarE _ _ => 1
  | TBindE _ p => S (psize p)
  | TShiftE _ t => S (tsize t)
  end
with psize (p : pexp) : nat :=
  match p with
  | PId | PAtom _ => 1
  | PComp a p => S (asize a + psize p)
  | PShift _ p => S (psize p)
  end.

Section Layers.

Variable np : nat.
Variable F : order.
Variable ds : list pdef.

(** The payload of a stored term: its word and what the word is over. *)
Definition pay (b : option nat) : word * option nat :=
  match b with
  | Some β =>
      if β <? np then (WEnd SNil, b)
      else match dget ds (β - np) with Some d => d | None => (WEnd SNil, b) end
  | None => (WEnd SNil, None)
  end.

Definition tpay (t : ntgt) : word * option nat :=
  match t with NBind _ _ b => pay b | NVar _ _ => (WEnd SNil, None) end.

Definition tents (t : ntgt) : list ent := sents (whead (fst (tpay t))).

(** The terms, in order of first occurrence from the root. *)
Fixpoint visit (fuel : nat) (acc : list ntgt) (ts : list ntgt) : list ntgt :=
  match fuel with
  | 0 => acc
  | S f =>
      fold_left (fun acc t =>
        if isterm t then (if tmem t acc then acc else visit f (acc ++ [t]) (etgts (tents t))) else acc) ts acc
  end.

(** Heights of the definitions, newest first like the table. *)
Definition bheight (hs : list nat) (b : option nat) : nat :=
  match b with
  | Some β => if β <? np then 0 else nth (List.length hs - 1 - (β - np)) hs 0
  | None => 0
  end.

Fixpoint dheights (l : list pdef) : list nat :=
  match l with
  | [] => []
  | (w, _) :: r =>
      let hs := dheights r in
      let ts := filter isterm (stargets (whead w)) in
      match ts with
      | [] => 0
      | _ => S (fold_right (fun t m => Nat.max (match t with NBind _ _ b => bheight hs b | _ => 0 end) m) 0 ts)
      end :: hs
  end.

(** ** What the parties agree on *)

(** Sharing everything the parties agree on, or only their terms, or
    nothing. *)
Variable share : bool.
Variable full : bool.

Definition agree_init (root : list ent) : list ent :=
  flat_map (fun '(x, ts, m) =>
    if is_lnone x || negb share then []
    else if full then match ts, m with [], 0 => [] | _, _ => [(x, ts, m)] end
    else match m, rev (takew (rev ts)) with 0, (_ :: _) as c => [(x, c, 0)] | _, _ => [] end) root.

Definition agree1 (N S : list ent) : list ent :=
  flat_map (fun '(x, cs, m) =>
    match efind x S with
    | Some (ts, m') =>
        if Nat.eqb m m' then
          let c := csuf cs ts in match c, m with [], 0 => [] | _, _ => [(x, c, m)] end
        else []
    | None => []
    end) N.

(** ** A party's remainder: its segment divided by what is agreed *)

Fixpoint nfindt (t : ntgt) (N : list ent) : option (lexp * nat) :=
  match N with
  | [] => None
  | (x, cs, _) :: r => match tindex t cs with Some k => Some (x, k) | None => nfindt t r end
  end.

Definition known_distinct (y : lexp) (N : list ent) : bool :=
  forallb (fun '(x, _, _) => match lcmp F y x with Some Lt | Some Gt => true | _ => false end) N.

Definition mkref (N : list ent) (t : ntgt) : option ref :=
  match t with
  | NVar LNone r => Some (RBound r)
  | NVar y r =>
      match efind y N with
      | Some (cs, my) =>
          if my <=? r then Some (RName y (r - my + List.length cs))
          else match nfindt t N with Some (x, k) => Some (RName x k) | None => None end
      | None => if known_distinct y N then Some (RName y r) else None
      end
  | NBind _ _ _ => match nfindt t N with Some (x, k) => Some (RName x k) | None => Some (RSlot t) end
  end.

Definition quot (N S : list ent) : option (list sent) :=
  option_map (@concat _)
    (opt_all (map (fun '(x, ts, m) =>
       if is_lnone x then Some []
       else match efind x N with
            | Some (cs, _) =>
                match opt_all (map (mkref N) (firstn (List.length ts - List.length cs) ts)) with
                | Some [] => Some []
                | Some rs => Some [(x, rs, 0)]
                | None => None
                end
            | None => match opt_all (map (mkref N) ts) with Some rs => Some [(x, rs, m)] | None => None end
            end) S)).

Definition srefs (q : list sent) : list ntgt :=
  flat_map (fun '(_, rs, _) => flat_map (fun r => match r with RSlot t => [t] | _ => [] end) rs) q.

Definition resolve (scope : list ntgt) (r : ref) : texp :=
  match r with
  | RName y i => TVarE y i
  | RSlot t => TVarE LNone (match tindex t scope with Some k => k | None => 0 end)
  | RBound i => TVarE LNone (i + List.length scope)
  end.

Definition rseg (scope : list ntgt) (q : list sent) : list (lexp * list texp * nat) :=
  map (fun '(x, rs, m) => (x, map (resolve scope) rs, m)) q.

(** ** The layers *)

Definition layers_of (w : word) : option aexp :=
  let hs := dheights ds in
  let hgt := fun t => match t with NBind _ _ b => bheight hs b | NVar _ _ => 0 end in
  let root := sents (whead w) in
  let prefix := match w with WEnd _ => AId | WAtom _ L a w' => ACompose (alifts L (AAtom a)) (waexp w') end in
  let nodes := visit (S (List.length ds)) [] (etgts root) in
  match nodes with
  | [] => Some (waexp w)
  | _ =>
      let H := fold_right (fun t m => Nat.max (hgt t) m) 0 nodes in
      let at_h := fun k => filter (fun t => Nat.eqb (hgt t) k) nodes in
      (* Ns: N_0 :: N_1 :: ... :: N_(H+1) *)
      let Ns := (fix go (k : nat) (Nabove : list ent) (acc : list (list ent)) : list (list ent) :=
                   match k with
                   | 0 => acc
                   | S k' =>
                       let Nk := fold_left (fun N t => agree1 N (tents t)) (at_h k') Nabove in
                       go k' Nk (Nk :: acc)
                   end) (S H) (agree_init root) [agree_init root] in
      let Nat_ := fun k => nth k Ns [] in
      match quot (Nat_ (S H)) root,
            opt_all (map (mkref (Nat_ (S H))) (match efind LNone root with Some (ts, _) => ts | None => [] end)),
            opt_all (map (fun k => quot (Nat_ k) (Nat_ (S k))) (seq 0 (S H))),
            opt_all (map (fun t => quot (Nat_ (hgt t)) (tents t)) nodes),
            opt_all (map (fun t => opt_all (map (mkref (Nat_ (hgt t)))
                                              (match efind LNone (tents t) with Some (ts, _) => ts | None => [] end))) nodes) with
      | Some qroot, Some broot, Some Dq, Some Pq, Some Bq =>
          let payq := fun t => match tindex t nodes with Some k => nth k Pq [] | None => [] end in
          let payb := fun t => match tindex t nodes with Some k => nth k Bq [] | None => [] end in
          let rslots := fun rs => flat_map (fun r => match r with RSlot t => [t] | _ => [] end) rs in
          (* slot references with the level they are at *)
          let lrefs :=
            map (fun t => (t, S H)) (srefs qroot ++ flat_map (fun r => match r with RSlot t => [t] | _ => [] end) broot)
            ++ concat (map (fun k => map (fun t => (t, k)) (srefs (nth k Dq []))) (seq 0 (S H)))
            ++ flat_map (fun t => map (fun t' => (t', hgt t)) (srefs (payq t) ++ rslots (payb t))) nodes in
          let lvl := fun t => fold_right (fun '(t', k) m => if ntgt_eqb t t' then Nat.max k m else m) 0 lrefs in
          let lvls := map lvl nodes in
          let lvl' := fun t => match tindex t nodes with Some k => nth k lvls 0 | None => 0 end in
          let slots := fun k => flat_map (fun hh => filter (fun t => Nat.eqb (hgt t) hh && (k <=? lvl' t)) nodes)
                                         (rev (seq 0 k)) in
          let slotsp := fun k => at_h k ++ slots k in
          let bm := match efind LNone root with Some (_, m) => m | None => 0 end in
          let sH := slots (S H) in
          let Rroot := mkseg (rseg sH qroot ++ [(LNone, map (resolve sH) broot, bm + List.length sH)]) in
          let layer := fun k =>
            let sp := slotsp k in
            let sk := slots k in
            (* the bound variables: those in use above, to their places among those in use here *)
            let pl := map (fun t => match tindex t sp with Some i => i | None => 0 end) (slots (S k)) in
            let plumb := if list_eq_dec Nat.eq_dec pl (seq 0 (List.length sp)) then []
                         else [(LNone, map (fun i => TVarE LNone i) pl, List.length sp)] in
            let A := mkseg (rseg sp (nth k Dq []) ++ plumb) in
            let term := fun t =>
              match t with
              | NBind u _ _ =>
                  let '(wp, b0) := tpay t in
                  (* the payload's bound outputs are past the bound variables in use here *)
                  let bnd := match efind LNone (tents t), wp, b0 with
                             | Some (_, m), _, _ => [(LNone, map (resolve sk) (payb t), m + List.length sk)]
                             | None, WEnd _, None => []
                             | None, _, _ => match sk with [] => [] | _ => [(LNone, [], List.length sk)] end
                             end in
                  let hd := mkseg (rseg sk (payq t) ++ bnd) in
                  let pe := match wp with
                            | WEnd _ => hd
                            | WAtom _ L a w'' => ACompose hd (ACompose (alifts L (AAtom a)) (waexp w''))
                            end in
                  TBindE u (PComp pe (match b0 with Some n => PAtom n | None => PId end))
              | NVar h i => TVarE h i
              end in
            let I := mkseg [(LNone, map term (at_h k), 0)] in
            [A; I] in
          let Omega := mkseg (map (fun '(x, ts, m) => (x, map stexp ts, m)) (Nat_ 0)) in
          Some (compose_steps ([prefix; Rroot] ++ flat_map layer (rev (seq 0 (S H))) ++ [Omega]))
      | _, _, _, _, _ => None
      end
  end.

End Layers.

(** Sharing renamings too when that works, else only terms.  A label
    can only be shared when its order to every label a party mentions is
    known; when it is not, nothing is shared, which always works. *)
Definition layers (np : nat) (F : order) (ds : list pdef) (w : word) : option aexp :=
  match layers_of np F ds true true w with
  | Some e => Some e
  | None =>
      match layers_of np F ds true false w with
      | Some e => Some e
      | None => layers_of np F ds false false w
      end
  end.

(** The stored word and its table written as expressions, for a size in
    the same unit as the layered form's. *)
Definition stored_size (ds : list pdef) (w : word) : nat :=
  fold_right (fun d acc => asize (waexp (fst d)) + acc) (asize (waexp w)) ds.

(** The layered form of an expression, whether normalising it again
    gives the same stored word, and sizes: of the layered form, of the
    stored word with its table, and of the tree (in nodes). *)
Definition layers_check (F : order) (ntm : nat) (e : aexp) : option (aexp * bool * (nat * nat * N)) :=
  let n := apmax e in
  match anorm_s n F ntm e sst0 with
  | Some (st, w) =>
      match layers n F (sdefs st) w with
      | Some le =>
          let ok := match anorm_s n F ntm le st with Some (_, w') => word_eqb w w' | None => false end in
          let zs := usz n (sdefs st) in
          Some (le, ok, (asize le, stored_size (sdefs st) w, wsz_u n zs w))
      | None => None
      end
  | None => None
  end.
