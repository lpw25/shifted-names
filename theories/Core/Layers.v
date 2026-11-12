(** * The layered form of a stored normal form (prototype)

    See "Layered form" in [docs/normal-forms.md].  [layers] turns a
    stored word and its table into an expression that is a composition
    of small steps.  It is built from the end: whatever every party not
    yet placed has at the end of its remainder is shared (entries of a
    label, or a lifted atom), and when nothing is, the terms whose
    remainder mentions no term not yet placed are instantiated, with
    that remainder as payload.  Nothing here is verified;
    [layers_check] normalises the result again and compares. *)

From Stdlib Require Import Arith List Lia Bool NArith.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Unique Normal Complete Shared Eval.
Import ListNotations.

Notation ent := (lexp * list ntgt * nat)%type.

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

(** A size that counts what is written (entries, outputs, lifts, atoms,
    terms) and not how the expression is bracketed.  Several outputs or
    lifts of one label count once, as the number they are in a word. *)
Fixpoint csize (e : aexp) : nat :=
  match e with
  | AId => 0
  | AAtom _ => 1
  | ACompose a b => csize a + csize b
  | AOuter h a => (match a with AOuter h' _ => if lexp_eqb h h' then 0 else 1 | _ => 1 end) + csize a
  | ALift h a => (match a with ALift h' _ => if lexp_eqb h h' then 0 else 1 | _ => 1 end) + csize a
  | AInner _ t a => S (ctsize t + csize a)
  end
with ctsize (t : texp) : nat :=
  match t with
  | TVarE _ _ => 0
  | TBindE _ p => S (cpsize p)
  | TShiftE _ t => S (ctsize t)
  end
with cpsize (p : pexp) : nat :=
  match p with
  | PId => 0
  | PAtom _ => 1
  | PComp a p => csize a + cpsize p
  | PShift _ p => S (cpsize p)
  end.

Section Layers.

Variable np : nat.
Variable F : order.
Variable ntm : nat.
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

Definition hents (k : word) : list ent := sents (whead k).

(** The terms, in order of first occurrence from the root. *)
Fixpoint visit (fuel : nat) (acc : list ntgt) (ts : list ntgt) : list ntgt :=
  match fuel with
  | 0 => acc
  | S f =>
      fold_left (fun acc t =>
        if isterm t then (if tmem t acc then acc else visit f (acc ++ [t]) (etgts (hents (fst (tpay t))))) else acc) ts acc
  end.

(** ** Segments from entries *)

Fixpoint trim_rev (h : lexp) (rts : list ntgt) (m : nat) : list ntgt * nat :=
  match rts, m with
  | NVar h' j :: r, S m' => if lexp_eqb h h' && Nat.eqb j m' then trim_rev h r m' else (rts, m)
  | _, _ => (rts, m)
  end.

Definition etrim (e : ent) : list ent :=
  let '(h, ts, m) := e in
  let '(r, m') := trim_rev h (rev ts) m in
  match r, m' with [], 0 => [] | _, _ => [(h, rev r, m')] end.

Definition mkS (es : list ent) : seg := fold_right (fun '(h, ts, m) r => SEnt h (tl_of ts) m r) SNil es.

Definition set_head (k : word) (s : seg) : word :=
  match k with WEnd _ => WEnd s | WAtom _ L a w => WAtom s L a w end.

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

Definition agree1 (N P : list ent) : list ent :=
  flat_map (fun '(x, cs, m) =>
    match efind x P with
    | Some (ts, m') =>
        if Nat.eqb m m' then
          let c := csuf cs ts in match c, m with [], 0 => [] | _, _ => [(x, c, m)] end
        else []
    | None => []
    end) N.

(** ** A party's remainder divided by what is shared *)

Fixpoint nfindt (t : ntgt) (N : list ent) : option (lexp * nat) :=
  match N with
  | [] => None
  | (x, cs, _) :: r => match tindex t cs with Some k => Some (x, k) | None => nfindt t r end
  end.

Definition known_distinct (y : lexp) (N : list ent) : bool :=
  forallb (fun '(x, _, _) => match lcmp F y x with Some Lt | Some Gt => true | _ => false end) N.

(** Where a target is before the shared step: a name the step sends
    there if there is one. *)
Definition mkref (N : list ent) (t : ntgt) : option ntgt :=
  match t with
  | NVar LNone r => Some t
  | NVar y r =>
      match efind y N with
      | Some (cs, my) =>
          if my <=? r then Some (NVar y (r - my + List.length cs))
          else match nfindt t N with Some (x, k) => Some (NVar x k) | None => None end
      | None => if known_distinct y N then Some t else None
      end
  | NBind _ _ _ => match nfindt t N with Some (x, k) => Some (NVar x k) | None => Some t end
  end.

Definition quot (N P : list ent) : option (list ent) :=
  option_map (@concat _)
    (opt_all (map (fun '(x, ts, m) =>
       match efind x N with
       | Some (cs, _) =>
           option_map (fun rs => etrim (x, rs, 0))
             (opt_all (map (mkref N) (firstn (List.length ts - List.length cs) ts)))
       | None => option_map (fun rs => etrim (x, rs, m)) (opt_all (map (mkref N) ts))
       end) P)).

(** ** Sharing an atom

    Every remaining party ends with the atom [a]; after it, a party only
    sends variables passed around the atom to remaining terms, innermost
    first.  Those terms then sit before the atom, which is no longer
    lifted over their variables; the lifts that remain are the same for
    every party. *)

Fixpoint lcs (g : lexp) (L : list (lexp * nat)) : nat :=
  match L with [] => 0 | (h, n) :: r => if lexp_eqb g h then n + lcs g r else lcs g r end.

Definition uncarry (inst : list ntgt) (k : word) : option (nat * list (lexp * nat) * word) :=
  match k with
  | WEnd _ => None
  | WAtom sg L a w =>
      let es := sents sg in
      if forallb (fun '(g, ts, m) =>
            Nat.eqb m 0 && (List.length ts <=? lcs g L)
            && forallb (fun t => isterm t && negb (tmem t inst)) ts) es
      then
        let L0 := flat_map (fun '(g, n) =>
                    let p := match efind g es with Some (ts, _) => List.length ts | None => 0 end in
                    match n - p with 0 => [] | c => [(g, c)] end) L in
        match scomp F ntm sg (whead w) with
        | Some hd => Some (a, L0, set_head w hd)
        | None => None
        end
      else None
  end.

Definition try_atom (inst : list ntgt) (parts : list (option ntgt * word))
  : option (list (lexp * nat) * nat * list (option ntgt * word)) :=
  if negb share then None else
  match opt_all (map (fun p => option_map (fun r => (fst p, r)) (uncarry inst (snd p))) parts) with
  | Some (((_, (a, L0, _)) :: _) as rs) =>
      if forallb (fun r => let '(_, (a', L', _)) := r in Nat.eqb a a' && lifts_eqb L0 L') rs
      then Some (L0, a, map (fun r => let '(id, (_, _, k)) := r in (id, k)) rs)
      else None
  | _ => None
  end.

(** ** The steps, from the end *)

(** A segment, with the terms written in it (each with its remainder);
    an atom; a layer of instantiations. *)
Inductive step : Type :=
| SRen (es : list ent) (il : list (ntgt * word))
| SAtom (L : list (lexp * nat)) (a : nat)
| SInst (l : list (ntgt * word)).

Fixpoint rootsteps (k : word) : list step :=
  match k with
  | WEnd sg => [SRen (sents sg) []]
  | WAtom sg L a w => rootsteps w ++ [SAtom L a; SRen (sents sg) []]
  end.

Definition ready (inst : list ntgt) (p : option ntgt * word) : bool :=
  match fst p with
  | Some _ => forallb (fun t => negb (isterm t) || tmem t inst) (etgts (hents (snd p)))
  | None => false
  end.

Definition inst_step (R : list (option ntgt * word)) : list (ntgt * word) :=
  flat_map (fun p => match fst p with Some t => [(t, snd p)] | None => [] end) R.

Definition agreement (ps : list (option ntgt * word)) : list ent :=
  match ps with
  | p0 :: rest => fold_left (fun N p => agree1 N (hents (snd p))) rest (agree_init (hents (snd p0)))
  | [] => []
  end.

(** What every remaining party has at its end is shared: entries, then
    an atom.  When nothing is, the terms that can be placed are. *)
Fixpoint build (fuel : nat) (parts : list (option ntgt * word)) (inst : list ntgt) (acc : list step)
  : option (list step) :=
  match fuel with
  | 0 => None
  | S f =>
      match parts with
      | [] => Some acc
      | [(None, k)] => Some (rootsteps k ++ acc)
      | _ =>
          match agreement parts with
          | (_ :: _) as N =>
              match opt_all (map (fun p => option_map (fun es => (fst p, set_head (snd p) (mkS es)))
                                             (quot N (hents (snd p)))) parts) with
              | Some parts' => build f parts' inst (SRen N [] :: acc)
              | None => None
              end
          | [] =>
              match try_atom inst parts with
              | Some (L0, a, parts') => build f parts' inst (SAtom L0 a :: acc)
              | None =>
                  let R := filter (ready inst) parts in
                  match R with
                  | [] => None
                  | _ =>
                      build f (filter (fun p => negb (existsb (fun q => match fst p, fst q with
                                                                        | Some t, Some t' => ntgt_eqb t t'
                                                                        | _, _ => false
                                                                        end) R)) parts)
                            (inst ++ map fst (inst_step R)) (SInst (inst_step R) :: acc)
                  end
              end
          end
      end
  end.

(** ** From steps to an expression

    A term referred to before its layer is a bound variable from the
    first step that refers to it until its layer.  The bound variables
    in use are ordered by layer, the next layer innermost, then by
    first occurrence from the root. *)

Variable nodes : list ntgt.

Definition pay_refs (l : list (ntgt * word)) : list ntgt :=
  filter isterm (flat_map (fun '(_, k) => etgts (hents k)) l).

Definition step_refs (s : step) : list ntgt :=
  match s with
  | SRen es il => filter (fun t => isterm t && negb (tmem t (map fst il))) (etgts es) ++ pay_refs il
  | SAtom _ _ => []
  | SInst l => pay_refs l
  end.

Definition step_inst (s : step) : list ntgt :=
  match s with SInst l => map fst l | SRen _ il => map fst il | SAtom _ _ => [] end.

(** A term is written where it is referred to, instead of through a
    bound variable, when that is its only reference, it is in a segment,
    and only layers of instantiations lie between that segment and the
    term's own layer: an instantiation touches only the bound label,
    which the term does not see. *)
Definition inline_pass (steps : list step) : list step :=
  let n := List.length steps in
  let at_ := fun j => nth j steps (SAtom [] 0) in
  let is_inst := fun s => match s with SInst _ => true | _ => false end in
  let home := fun i t =>
    match filter (fun j => tmem t (step_refs (at_ j))) (seq 0 n) with
    | [j] =>
        match at_ j with
        | SRen es _ =>
            (j <? i) && Nat.eqb (List.length (filter (ntgt_eqb t) (etgts es))) 1
            && forallb (fun m => is_inst (at_ m)) (seq (S j) (i - S j))
        | _ => false
        end
    | _ => false
    end in
  let homej := fun i t =>
    match filter (fun j => tmem t (step_refs (at_ j))) (seq 0 n) with j :: _ => j | [] => 0 end in
  let moved := flat_map (fun i => match at_ i with
                                  | SInst l => flat_map (fun '(t, k) => if home i t then [(homej i t, (t, k))] else []) l
                                  | _ => []
                                  end) (seq 0 n) in
  flat_map (fun j =>
    match at_ j with
    | SRen es _ => [SRen es (flat_map (fun '(j', tk) => if Nat.eqb j j' then [tk] else []) moved)]
    | SAtom L a => [SAtom L a]
    | SInst l =>
        match filter (fun '(t, _) => negb (home j t)) l with
        | [] => []
        | l' => [SInst l']
        end
    end) (seq 0 n).

Fixpoint first_idx (f : step -> bool) (steps : list step) (i : nat) : nat :=
  match steps with [] => i | s :: r => if f s then i else first_idx f r (S i) end.

Definition base_pexp (b : option nat) : pexp := match b with Some n => PAtom n | None => PId end.

Definition rtgt (sc : list ntgt) (term : ntgt -> option texp) (t : ntgt) : texp :=
  match t with
  | NVar LNone r => TVarE LNone (r + List.length sc)
  | NVar y r => TVarE y r
  | NBind _ _ _ =>
      match term t with
      | Some e => e
      | None => TVarE LNone (match tindex t sc with Some k => k | None => 0 end)
      end
  end.

(** An entry of the bound label with the targets the tail gives anyway
    taken off its end. *)
Fixpoint btrim_rev (rts : list texp) (m : nat) : list texp * nat :=
  match rts, m with
  | TVarE LNone j :: r, S m' => if Nat.eqb j m' then btrim_rev r m' else (rts, m)
  | _, _ => (rts, m)
  end.

Definition bentry (ts : list texp) (m : nat) : list (lexp * list texp * nat) :=
  let '(r, m') := btrim_rev (rev ts) m in
  match r, m' with [], 0 => [] | _, _ => [(LNone, rev r, m')] end.

(** A segment between the bound variables [sin] in use before it and
    [sout] after it; [term] gives the terms written here. *)
Definition emit_seg (sin sout : list ntgt) (term : ntgt -> option texp) (es : list ent) : aexp :=
  let pl := map (fun t => match term t with
                          | Some e => e
                          | None => TVarE LNone (match tindex t sout with Some i => i | None => 0 end)
                          end) sin in
  let named := flat_map (fun '(x, ts, m) => if is_lnone x then [] else [(x, map (rtgt sout term) ts, m)]) es in
  let '(bts, bm) := match efind LNone es with Some (ts, m) => (map (rtgt sout term) ts, m) | None => ([], 0) end in
  mkseg (named ++ bentry (pl ++ bts) (bm + List.length sout)).

(** A term with its payload, among the bound variables [sc]. *)
Definition emit_term (sc : list ntgt) (t : ntgt) (k : word) : texp :=
  match t with
  | NBind u _ _ =>
      let b0 := snd (tpay t) in
      let es := hents k in
      let named := flat_map (fun '(x, ts, m) => if is_lnone x then [] else [(x, map (rtgt sc (fun _ => None)) ts, m)]) es in
      let bnd := match efind LNone es, k, b0 with
                 | Some (ts, m), _, _ => [(LNone, map (rtgt sc (fun _ => None)) ts, m + List.length sc)]
                 | None, WEnd _, None => []
                 | None, _, _ => match sc with [] => [] | _ => [(LNone, [], List.length sc)] end
                 end in
      let hd := mkseg (named ++ bnd) in
      let pe := match k with
                | WEnd _ => hd
                | WAtom _ L a w' => ACompose hd (ACompose (alifts L (AAtom a)) (waexp w'))
                end in
      TBindE u (if is_aid pe then base_pexp b0 else PComp pe (base_pexp b0))
  | NVar h i => TVarE h i
  end.

Definition emit (steps0 : list step) : list aexp :=
  let steps := inline_pass steps0 in
  let n := List.length steps in
  let firstref := fun t => first_idx (fun s => tmem t (step_refs s)) steps 0 in
  let instat := fun t => first_idx (fun s => tmem t (step_inst s)) steps 0 in
  let frs := map firstref nodes in
  let ins := map instat nodes in
  let fr := fun t => match tindex t nodes with Some k => nth k frs 0 | None => 0 end in
  let ia := fun t => match tindex t nodes with Some k => nth k ins 0 | None => 0 end in
  (* the bound variables in use after step [j]: by layer, the next innermost; in a layer the last
     referred to innermost *)
  let slots_after := fun j =>
    flat_map (fun i => flat_map (fun f => filter (fun t => Nat.eqb (ia t) i && Nat.eqb (fr t) f) nodes)
                                (rev (seq 0 (S j))))
             (seq (S j) (n - S j)) in
  let slots_before := fun j => match j with 0 => [] | S j' => slots_after j' end in
  let payload := fun sc l t => match find (fun '(t', _) => ntgt_eqb t t') l with
                               | Some (_, k) => Some (emit_term sc t k)
                               | None => None
                               end in
  (fix go (j : nat) (ss : list step) : list aexp :=
     match ss with
     | [] => []
     | SRen es il :: r => let sout := slots_after j in emit_seg (slots_before j) sout (payload sout il) es :: go (S j) r
     | SAtom L a :: r => iter (List.length (slots_after j)) (ALift LNone) (alifts L (AAtom a)) :: go (S j) r
     | SInst l :: r => let sout := slots_after j in emit_seg (slots_before j) sout (payload sout l) [] :: go (S j) r
     end) 0 steps.

End Layers.

Definition layers_of (np : nat) (F : order) (ntm : nat) (ds : list pdef) (share full : bool) (w : word) : option aexp :=
  let nodes := visit np ds (S (List.length ds)) [] (etgts (hents w)) in
  let parts := (None, w) :: map (fun t => (Some t, fst (tpay np ds t))) nodes in
  match build F ntm share full (1000 + 20 * List.length nodes) parts [] [] with
  | Some steps => Some (compose_steps (emit np ds nodes steps))
  | None => None
  end.

(** Sharing renamings too when that works, else only terms.  A label
    can only be shared when its order to every label a party mentions is
    known; when it is not, nothing is shared, which always works. *)
Definition layers (np : nat) (F : order) (ntm : nat) (ds : list pdef) (w : word) : option aexp :=
  match layers_of np F ntm ds true true w with
  | Some e => Some e
  | None =>
      match layers_of np F ntm ds true false w with
      | Some e => Some e
      | None => layers_of np F ntm ds false false w
      end
  end.

(** A tree word as an expression. *)
Fixpoint taexp (fuel : nat) (w : word) : aexp :=
  match fuel with
  | 0 => AId
  | S f =>
      let tx := fun t => match t with
                         | NVar h i => TVarE h i
                         | NBind u wp b =>
                             TBindE u (match wp with
                                       | WEnd SNil => base_pexp b
                                       | _ => PComp (taexp f wp) (base_pexp b)
                                       end)
                         end in
      let sx := fun sg => mkseg (map (fun '(h, ts, m) => (h, map tx ts, m)) (sents sg)) in
      (fix go (w : word) : aexp :=
         match w with
         | WEnd sg => sx sg
         | WAtom sg L a w' => ACompose (sx sg) (ACompose (alifts L (AAtom a)) (go w'))
         end) w
  end.

(** The size of the tree, when it is small enough to build. *)
Definition tree_size (np : nat) (ds : list pdef) (w : word) : option nat :=
  match unfold_small np 20000%N ds w with
  | Some t => Some (csize (taexp (S (List.length ds)) t))
  | None => None
  end.

(** The stored word and its table written as expressions, for a size in
    the same unit as the layered form's. *)
Definition stored_size (ds : list pdef) (w : word) : nat :=
  fold_right (fun d acc => csize (waexp (fst d)) + acc) (csize (waexp w)) ds.

(** The layered form of an expression, whether normalising it again
    gives the same stored word, and sizes: of the layered form, of the
    stored word with its table, and of the tree (in nodes). *)
Definition layers_check (F : order) (ntm : nat) (e : aexp) : option (aexp * bool * (nat * nat * N)) :=
  let n := apmax e in
  match anorm_s n F ntm e sst0 with
  | Some (st, w) =>
      match layers n F ntm (sdefs st) w with
      | Some le =>
          let ok := match anorm_s n F ntm le st with Some (_, w') => word_eqb w w' | None => false end in
          let zs := usz n (sdefs st) in
          Some (le, ok, (csize le, stored_size (sdefs st) w, wsz_u n zs w))
      | None => None
      end
  | None => None
  end.
