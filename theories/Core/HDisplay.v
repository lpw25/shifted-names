(** * Showing [HNorm]'s normal forms

    A normal form is a word whose values are absolute: read at the end
    of the word.  It is shown as an expression ([aexp]) that [names]
    renders as context forms: a word is shown once per cell, and a cell
    the expression refers to more than once is shared.  References to
    cells are atoms numbered from [base]: [display] first shows every
    cell it needs ([dref]), and [assemble] then inlines the cells
    referred to once and keeps the others as shared definitions.

    A word is shown by the first rule that applies ([dbody]):
    - [factor]: entries [hᵢ := uᵢ] whose payload is the rest of the
      word are the form [⟦ hᵢ := uᵢ ⟧] composed with the rest;
    - [split]: a word whose leading values only look through a suffix is
      the word before the suffix, read relative to it, composed with the
      suffix;
    - [lift]: an entry [x ↦ g₀] whose rest does not otherwise see [g₀]
      is a lift ([x = g]) or a renaming to an output, over the rest with
      [g] popped;
    - otherwise the entries are shown with their absolute values in a
      short form over the rest, an atom is composed with the rest, and
      weakenings are a form with outputs only.

    [HDisplaySound] proves that the expression means the word. *)

From Stdlib Require Import List PArith NArith Bool FMapPositive Arith.
From ShiftedNames.Core Require Import Label Normalise.
From ShiftedNames.Core Require HNorm.
Import ListNotations.
Import HNorm.

Section Display.

Variable F : order.

Definition cell (T : st) (i : positive) : option (step * positive) := PositiveMap.find i (cells T).

(** The word from the cell [i]. *)
Fixpoint hword (T : st) (fuel : nat) (i : positive) : word :=
  match fuel with
  | 0 => []
  | S f =>
      if Pos.eqb i 1 then []
      else match cell T i with Some (s, t) => (s, i) :: hword T f t | None => [] end
  end.

(** Ids decrease along a word, so [i] is fuel enough. *)
Definition hw (T : st) (i : positive) : word := hword T (Pos.to_nat i) i.

(** [hcons] on an id. *)
Definition hcons_w (s : step) (w : word) (T : st) : word * st := hcons s w T.

Definition memo := PositiveMap.t positive.

(** ** Relative to a suffix

    [relw s w]: [w] up to its suffix [s], with each value read at the
    start of [s] instead of at the end. *)
Section Rel.

Variable s : positive.

Fixpoint relw (fuel : nat) (w : word) (T : st) (m : memo) {struct fuel} : option (word * st * memo) :=
  match fuel with
  | 0 => None
  | S f =>
      match w with
      | [] => if Pos.eqb s 1 then Some ([], T, m) else None
      | (x, i) :: w' =>
          if Pos.eqb i s then Some ([], T, m)
          else match relst f x T m with
               | Some (x', T1, m1) =>
                   match relw f w' T1 m1 with
                   | Some (w1, T2, m2) => let '(w2, T3) := hcons x' w1 T2 in Some (w2, T3, m2)
                   | None => None
                   end
               | None => None
               end
      end
  end
with relst (fuel : nat) (x : step) (T : st) (m : memo) {struct fuel} : option (step * st * memo) :=
  match fuel with
  | 0 => None
  | S f =>
      match x with
      | SE h v => match relv f v T m with Some (v', T1, m1) => Some (SE h v', T1, m1) | None => None end
      | _ => Some (x, T, m)
      end
  end
with relv (fuel : nat) (v : val) (T : st) (m : memo) {struct fuel} : option (val * st * memo) :=
  match fuel with
  | 0 => None
  | S f =>
      match v with
      | VLook g j x => if Pos.eqb x s then Some (VVar g j, T, m) else None
      | VVar g j => let '(v', T1) := lookup F g j (hw T s) T in if val_eqb v' v then Some (v, T1, m) else None
      | VTerm u None p =>
          match PositiveMap.find p m with
          | Some p' => Some (VTerm u None p', T, m)
          | None =>
              match relw f (hw T p) T m with
              | Some (w', T1, m1) => Some (VTerm u None (wid w'), T1, PositiveMap.add p (wid w') m1)
              | None => None
              end
          end
      | VTerm _ (Some _) _ => None
      end
  end.

End Rel.

(** ** Without a final pop

    [unw g w]: a word that, on [x] with [g] popped, does what [w] does on
    [x]; [w] ends with a weakening on [g], followed only by weakenings
    on labels known distinct from [g].  A term's payload with no payload
    atom may instead see only named labels when [g] is the bound label
    ([unall]).  Memo keys: [xO x] for words, [xI p] for payloads. *)
Section Unlift.

Variable g : lexp.

Fixpoint all_sw_kd (w : word) : bool :=
  match w with [] => true | (SW h, _) :: w' => kd F h g && all_sw_kd w' | _ => false end.

Fixpoint named_only (w : word) : bool :=
  match w with
  | [] => true
  | (SE h _, _) :: w' | (SW h, _) :: w' => negb (lexp_eqb h LNone) && named_only w'
  | (SA _, _) :: _ => false
  end.

Fixpoint unw (fuel : nat) (w : word) (T : st) (m : memo) {struct fuel} : option (word * st * memo) :=
  match fuel with
  | 0 => None
  | S f =>
      match w with
      | [] => None
      | (x, _) :: w' =>
          if match x with SW h => lexp_eqb h g && all_sw_kd w' | _ => false end then Some (w', T, m)
          else match unst f x T m with
               | Some (x', T1, m1) =>
                   match unw f w' T1 m1 with
                   | Some (w1, T2, m2) => let '(w2, T3) := hcons x' w1 T2 in Some (w2, T3, m2)
                   | None => None
                   end
               | None => None
               end
      end
  end
with unall (fuel : nat) (w : word) (T : st) (m : memo) {struct fuel} : option (word * st * memo) :=
  match fuel with
  | 0 => None
  | S f =>
      match w with
      | [] => Some ([], T, m)
      | (x, _) :: w' =>
          match unst f x T m with
          | Some (x', T1, m1) =>
              match unall f w' T1 m1 with
              | Some (w1, T2, m2) => let '(w2, T3) := hcons x' w1 T2 in Some (w2, T3, m2)
              | None => None
              end
          | None => None
          end
      end
  end
with unst (fuel : nat) (x : step) (T : st) (m : memo) {struct fuel} : option (step * st * memo) :=
  match fuel with
  | 0 => None
  | S f =>
      match x with
      | SE h v => match unv f v T m with Some (v', T1, m1) => Some (SE h v', T1, m1) | None => None end
      | _ => Some (x, T, m)
      end
  end
with unv (fuel : nat) (v : val) (T : st) (m : memo) {struct fuel} : option (val * st * memo) :=
  match fuel with
  | 0 => None
  | S f =>
      match v with
      | VVar h j =>
          if lexp_eqb h g then match j with 0 => None | S j' => Some (VVar h j', T, m) end
          else if kd F h g then Some (v, T, m) else None
      | VLook h j x =>
          match PositiveMap.find (xO x) m with
          | Some x' => Some (VLook h j x', T, m)
          | None =>
              match unw f (hw T x) T m with
              | Some (w', T1, m1) => Some (VLook h j (wid w'), T1, PositiveMap.add (xO x) (wid w') m1)
              | None => None
              end
          end
      | VTerm u None p =>
          match PositiveMap.find (xI p) m with
          | Some p' => Some (VTerm u None p', T, m)
          | None =>
              let w := hw T p in
              let r := match unw f w T m with
                       | Some r => Some r
                       | None => if lexp_eqb g LNone && named_only w then unall f w T m else None
                       end in
              match r with
              | Some (w', T1, m1) => Some (VTerm u None (wid w'), T1, PositiveMap.add (xI p) (wid w') m1)
              | None => None
              end
          end
      | VTerm _ (Some _) _ => None
      end
  end.

End Unlift.

(** ** The rules *)

Fixpoint take_se (w : word) : list (lexp * val) * word :=
  match w with (SE h v, _) :: w' => let '(l, r) := take_se w' in ((h, v) :: l, r) | _ => ([], w) end.

Fixpoint take_sw (w : word) : list lexp * word :=
  match w with (SW h, _) :: w' => let '(l, r) := take_sw w' in (h :: l, r) | _ => ([], w) end.

Definition tpay (v : val) : option (nat * positive) :=
  match v with VTerm u None p => Some (u, p) | _ => None end.

(** The entries whose payload is the cell [p] and that commute with
    every entry before them that is not taken; and the others. *)
Fixpoint split_pay (p : positive) (seen : list lexp) (es : list (lexp * val)) : list (lexp * nat) * list (lexp * val) :=
  match es with
  | [] => ([], [])
  | (h, v) :: r =>
      let take := match tpay v with
                  | Some (u, q) => if Pos.eqb p q && forallb (fun k => kd F k h) seen then Some u else None
                  | None => None
                  end in
      match take with
      | Some u => let '(ts, rest) := split_pay p seen r in ((h, u) :: ts, rest)
      | None => let '(ts, rest) := split_pay p (h :: seen) r in (ts, (h, v) :: rest)
      end
  end.

(** The entries of [w] in front of the cell [a1]. *)
Fixpoint strip_to (a1 : positive) (w : word) : option (list (lexp * val)) :=
  match w with
  | [] => if Pos.eqb a1 1 then Some [] else None
  | (x, i) :: w' =>
      if Pos.eqb i a1 then Some []
      else match x with SE h v => option_map (cons (h, v)) (strip_to a1 w') | _ => None end
  end.

Fixpoint entries_eqb (a b : list (lexp * val)) : bool :=
  match a, b with
  | [], [] => true
  | (h, v) :: a', (k, u) :: b' => lexp_eqb h k && val_eqb v u && entries_eqb a' b'
  | _, _ => false
  end.

(** [factor]: the entries taken and their common payload. *)
Fixpoint find_factor (T : st) (a1 : positive) (es l : list (lexp * val)) : option (list (lexp * nat) * positive) :=
  match l with
  | [] => None
  | (_, v) :: r =>
      match tpay v with
      | Some (_, p) =>
          let '(ts, rest) := split_pay p [] es in
          match ts, strip_to a1 (hw T p) with
          | _ :: _, Some pre => if entries_eqb pre rest then Some (ts, p) else find_factor T a1 es r
          | _, _ => find_factor T a1 es r
          end
      | None => find_factor T a1 es r
      end
  end.

Fixpoint wids (w : word) : list positive := match w with [] => [] | (_, i) :: w' => i :: wids w' end.

(** [split]: a suffix that a leading value refers to. *)
Fixpoint split_cand (R : list positive) (es : list (lexp * val)) : option positive :=
  match es with
  | [] => None
  | (_, v) :: r =>
      match v with
      | VLook _ _ x | VTerm _ None x => if existsb (Pos.eqb x) R then Some x else split_cand R r
      | _ => split_cand R r
      end
  end.

Definition fuel_of (T : st) : nat := 2 * Pos.to_nat (next T) + 8.

Definition find_split (T : st) (W R : word) (es : list (lexp * val)) : option (positive * word * st) :=
  match split_cand (wids R) es with
  | Some x => match relw x (fuel_of T) W T (PositiveMap.empty _) with
              | Some (W1, T1, _) => Some (x, W1, T1)
              | None => None
              end
  | None => None
  end.

(** The entries [es] without a final pop of [g], in front of [R']. *)
Fixpoint unents (g : lexp) (fuel : nat) (es : list (lexp * val)) (R' : word) (T : st) (m : memo)
  : option (word * st * memo) :=
  match es with
  | [] => Some (R', T, m)
  | (h, v) :: es' =>
      match unv g fuel v T m with
      | Some (v', T1, m1) =>
          match unents g fuel es' R' T1 m1 with
          | Some (w1, T2, m2) => let '(w2, T3) := hcons (SE h v') w1 T2 in Some (w2, T3, m2)
          | None => None
          end
      | None => None
      end
  end.

(** [lift]: an entry [x ↦ g₀] that commutes with the entries before
    it, and the rest without the pop of [g]. *)
Fixpoint find_lift (T : st) (seen : list lexp) (pre : list (lexp * val)) (es : list (lexp * val)) (R : word)
  : option (lexp * lexp * word * st) :=
  match es with
  | [] => None
  | (x, v) :: r =>
      let next := find_lift T (x :: seen) ((x, v) :: pre) r R in
      match v with
      | VVar g 0 =>
          if forallb (fun k => kd F k x) seen then
            match unw g (fuel_of T) R T (PositiveMap.empty _) with
            | Some (R', T1, m1) =>
                match unents g (fuel_of T) (rev pre ++ r) R' T1 m1 with
                | Some (B, T2, _) => Some (x, g, B, T2)
                | None => next
                end
            | None => next
            end
          else next
      | _ => next
      end
  end.

(** ** Showing cells *)

Variable base : nat.

Record dstate := mk_dstate { dT : st; dmemo : PositiveMap.t nat; ddefs : list aexp; dn : nat }.

Definition setT (D : dstate) (T : st) : dstate := mk_dstate T (dmemo D) (ddefs D) (dn D).

Definition acomp (r x : aexp) : aexp := match r with AId => x | _ => ACompose r x end.

(** Weakenings on [h₁ … hₖ], [h₁] outermost. *)
Definition weak (hs : list lexp) : aexp := fold_left (fun a h => AOuter h a) hs AId.

(** The form [⟦ hᵢ := uᵢ ⟧]. *)
Definition sform (ts : list (lexp * nat)) : aexp :=
  fold_right (fun '(h, u) a => AInner h (TBindE u (PComp AId PId)) a) AId ts.

Fixpoint dref (fuel : nat) (i : positive) (D : dstate) {struct fuel} : option (aexp * dstate) :=
  match fuel with
  | 0 => None
  | S f =>
      if Pos.eqb i 1 then Some (AId, D)
      else match PositiveMap.find i (dmemo D) with
           | Some k => Some (AAtom (base + k), D)
           | None =>
               match dbody f i D with
               | Some (d, D1) =>
                   match PositiveMap.find i (dmemo D1) with
                   | Some k => Some (AAtom (base + k), D1)
                   | None =>
                       let k := dn D1 in
                       Some (AAtom (base + k), mk_dstate (dT D1) (PositiveMap.add i k (dmemo D1)) (d :: ddefs D1) (S k))
                   end
               | None => None
               end
           end
  end
with dbody (fuel : nat) (i : positive) (D : dstate) {struct fuel} : option (aexp * dstate) :=
  match fuel with
  | 0 => None
  | S f =>
      let T := dT D in
      let W := hw T i in
      match W with
      | [] => Some (AId, D)
      | (SA a, _) :: R =>
          if Nat.ltb a base then
            match dref f (wid R) D with Some (r, D1) => Some (acomp r (AAtom a), D1) | None => None end
          else None
      | (SW _, _) :: _ =>
          let '(hs, R) := take_sw W in
          match dref f (wid R) D with Some (r, D1) => Some (acomp r (weak hs), D1) | None => None end
      | (SE _ _, _) :: _ =>
          let '(es, R) := take_se W in
          match find_factor T (wid R) es es with
          | Some (ts, p) => match dref f p D with Some (r, D1) => Some (acomp r (sform ts), D1) | None => None end
          | None =>
              match find_split T W R es with
              | Some (x, W1, T1) =>
                  match dref f x (setT D T1) with
                  | Some (r2, D1) =>
                      match dref f (wid W1) D1 with Some (r1, D2) => Some (acomp r2 r1, D2) | None => None end
                  | None => None
                  end
              | None =>
                  match find_lift T [] [] es R with
                  | Some (x, g, B, T1) =>
                      match dref f (wid B) (setT D T1) with
                      | Some (rb, D1) => Some (AInner x (TVarE g 0) (AOuter g rb), D1)
                      | None => None
                      end
                  | None => dabs f es R D
                  end
              end
          end
      end
  end
(** The entries with their absolute values, over the rest. *)
with dabs (fuel : nat) (es : list (lexp * val)) (R : word) (D : dstate) {struct fuel} : option (aexp * dstate) :=
  match fuel with
  | 0 => None
  | S f =>
      match es with
      | [] => dref f (wid R) D
      | (h, v) :: es' =>
          let tg : option (texp * dstate) :=
            match v with
            | VVar g j => Some (TVarE g j, D)
            | VTerm u None p =>
                match dref f p D with Some (r, D1) => Some (TBindE u (PComp r PId), D1) | None => None end
            | VLook g j x =>
                match dref f x D with Some (r, D1) => Some (TLookE g j r, D1) | None => None end
            | VTerm _ (Some _) _ => None
            end in
          match tg with
          | Some (t, D1) => match dabs f es' R D1 with Some (a, D2) => Some (AInner h t a, D2) | None => None end
          | None => None
          end
      end
  end.

(** ** Sharing *)

(** How often each cell is referred to. *)
Fixpoint arefs (d : aexp) (c : PositiveMap.t nat) : PositiveMap.t nat :=
  match d with
  | AId => c
  | AAtom n =>
      if Nat.leb base n then
        let k := Pos.of_succ_nat (n - base) in
        PositiveMap.add k (S (match PositiveMap.find k c with Some m => m | None => 0 end)) c
      else c
  | ACompose a b => arefs b (arefs a c)
  | AOuter _ a | ALift _ a => arefs a c
  | AInner _ t a => arefs a (trefs t c)
  end
with trefs (t : texp) (c : PositiveMap.t nat) : PositiveMap.t nat :=
  match t with
  | TVarE _ _ => c
  | TBindE _ p => prefs p c
  | TShiftE _ t => trefs t c
  | TLookE _ _ a => arefs a c
  end
with prefs (p : pexp) (c : PositiveMap.t nat) : PositiveMap.t nat :=
  match p with
  | PId | PAtom _ => c
  | PComp a p => prefs p (arefs a c)
  | PShift _ p => prefs p c
  end.

(** Replacing references: [σ k] is what the [k]th cell becomes. *)
Section Subst.

Variable σ : nat -> aexp.

Fixpoint asub (d : aexp) : aexp :=
  match d with
  | AId => AId
  | AAtom n => if Nat.leb base n then σ (n - base) else AAtom n
  | ACompose a b => ACompose (asub a) (asub b)
  | AOuter h a => AOuter h (asub a)
  | AInner h t a => AInner h (tsub t) (asub a)
  | ALift h a => ALift h (asub a)
  end
with tsub (t : texp) : texp :=
  match t with
  | TVarE h i => TVarE h i
  | TBindE u p => TBindE u (psub p)
  | TShiftE h t => TShiftE h (tsub t)
  | TLookE h i a => TLookE h i (asub a)
  end
with psub (p : pexp) : pexp :=
  match p with
  | PId => PId
  | PAtom n => PAtom n
  | PComp a p => PComp (asub a) (psub p)
  | PShift h p => PShift h (psub p)
  end.

End Subst.

Definition trivial (d : aexp) : bool := match d with AId | AAtom _ => true | _ => false end.

(** The cells in order (each refers only to earlier ones): what each
    becomes, and the shared definitions so far. *)
Fixpoint assemble_go (shr : bool) (cnt : PositiveMap.t nat) (k : nat) (ds : list aexp) (out : list aexp) (shared : list aexp)
  : list aexp * list aexp :=
  match ds with
  | [] => (out, shared)
  | d :: ds' =>
      let σ (j : nat) := nth j out AId in
      let d' := asub σ d in
      let n := match PositiveMap.find (Pos.of_succ_nat k) cnt with Some m => m | None => 0 end in
      if shr && Nat.leb 2 n && negb (trivial d') then
        assemble_go shr cnt (S k) ds' (out ++ [AAtom (base + List.length shared)]) (shared ++ [d'])
      else assemble_go shr cnt (S k) ds' (out ++ [d']) shared
  end.

Definition assemble (shr : bool) (r : aexp) (D : dstate) : list aexp * aexp :=
  let ds := rev (ddefs D) in
  let cnt := fold_left (fun c d => arefs d c) ds (arefs r (PositiveMap.empty _)) in
  let '(out, shared) := assemble_go shr cnt 0 ds [] [] in
  (shared, asub (fun j => nth j out AId) r).

(** Compositions nested to the left, as [⨾] is read: [(a ⨾ b) ⨾ c]. *)
Fixpoint comp_l (x y : aexp) : aexp :=
  match x with ACompose x1 x2 => comp_l x1 (comp_l x2 y) | _ => ACompose x y end.

Fixpoint lassoc (d : aexp) : aexp :=
  match d with
  | AId => AId
  | AAtom n => AAtom n
  | ACompose a b => comp_l (lassoc a) (lassoc b)
  | AOuter h a => AOuter h (lassoc a)
  | AInner h t a => AInner h (tlassoc t) (lassoc a)
  | ALift h a => ALift h (lassoc a)
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

Definition dstart (T : st) : dstate := mk_dstate T (PositiveMap.empty _) [] 0.

(** Showing the word from the cell [i]: shared definitions, numbered
    from [base], and the expression; with [shr] false, nothing is
    shared. *)
Definition display_s (shr : bool) (T : st) (i : positive) : option (list aexp * aexp) :=
  match dref (4 * Pos.to_nat (next T) + 16) i (dstart T) with
  | Some (r, D) => let '(sh, root) := assemble shr r D in Some (map lassoc sh, lassoc root)
  | None => None
  end.

Definition display := display_s true.

End Display.
