(** * Composition

    [compose a b] is [b] followed by [a]: a variable [b] sends to [y] goes
    where [a] sends [y], and a payload [(u, rho)] becomes
    [(u, restrict (a ∘ rho))].

    The composition is eager but pruned (Prune.v).  Above the thresholds
    [th] (the lengths of [a]'s explicit targets), [a] is the pure shift
    [unshift tau ∘ shift th], so any part of [b] whose uses clear the
    thresholds is moved by its counts alone.  The rest is mapped leaf by
    leaf, and the result is put back into normal form:

    - entries of [a] for labels [b] has no entry for are added, dropped by
      [b]'s root counts;
    - the root counts are recomputed, from the trie's counts and the
      identity starts of the labels with no entry;
    - an entry that has become the identity relative to the new root is
      removed, and a label without an entry whose identity start is above
      the new root gets a gap entry.

    Only the entries the traversal visited, and the labels of [a], can need
    removing; only the labels [b]'s root weakens can need a gap. *)

From Stdlib Require Import PArith Arith Lia List Bool.
From ShiftedNames.Core Require Import Trie Label Var Counts Based Skew ATrie Prune Repr Point.
Import ListNotations.

Section Compose.

Context {T : Type}.

Local Notation nadj := (@nadj T).
Local Notation result := (@result T).
Local Notation entry := (@entry T).
Local Notation target := (@target T).

(** ** Count map helpers *)

(** Setting one key, keeping the exceptions canonical. *)
Definition cset (c : counts) (k : positive) (v : option nat) : counts :=
  mk_counts (c_def c) (if oeqb v (c_def c) then remove k (c_exc c) else set k v (c_exc c)).

(** The pointwise sum of two count maps, as totals. *)
Definition ctotal (c1 c2 : counts) : counts :=
  cmap2 (fun x y => Some (oval x + oval y)) c1 c2.

(** ** What [a] looks like above the thresholds *)

Variable a : nadj.

Definition wa : counts := nroot a.
Definition esa : atrie entry := nentries a.

(** [a]'s entries, relative to its root. *)
Definition aentries : list entry := aelems esa.

Definition th_tree : tree nat :=
  fold_right (fun e m => match e with
                         | Entry h _ len _ => if Nat.eqb len 0 then m else set (label_key h) len m
                         end) Empty aentries.

Definition th : counts := mk_counts None (map_filter (fun _ n => Some (Some n)) th_tree).

Definition tau : counts :=
  fold_right (fun e c => match e with
                         | Entry h _ _ p => cset c (label_key h) (Some (dval wa (label_key h) + p))
                         end) wa aentries.

Definition thv (h : option label) : nat := dval th (label_key h).
Definition tauv (h : option label) : nat := dval tau (label_key h).

(** [a]'s explicit targets for [h] from absolute input [s] on, absolute. *)
Definition aextra (h : option label) (s : nat) : list target :=
  match aget (label_key h) esa with
  | Some (Entry _ tsa _ _) => map (tunshift wa) (skipn s (klist tsa))
  | None => []
  end.

(** [a]'s entry for [h] with its first [n] inputs dropped, absolute. *)
Definition adrop (h : option label) (n : nat) : option entry :=
  match aget (label_key h) esa with
  | Some (Entry _ tsa lena pa) =>
      let p := dval wa (label_key h) + pa in
      if Nat.ltb n lena
      then Some (Entry h (kof_list (map (tunshift wa) (skipn n (klist tsa)))) (lena - n) p)
      else Some (Entry h KNil 0 (p + (n - lena)))
  | None => None
  end.

(** ** Entries *)

Definition rtarget (r : result) : target :=
  match r with inl v => TVar (v_label v) (v_index v) | inr (u, rho) => TBind u rho end.

(** Stripping a reversed target list against pass-through [p]. *)
Fixpoint rstrip (h : option label) (R : list target) (p : nat) : list target * nat :=
  match R, p with
  | t :: R', S p' => if tvar_at h p' t then rstrip h R' p' else (R, p)
  | _, _ => (R, p)
  end.

(** An absolute entry, stripped: the last target is checked in O(log n),
    and the sequence is rebuilt only if it strips. *)
Definition estrip (h : option label) (ts : kseq target) (len p : nat) : entry :=
  match len, p with
  | S len', S p' =>
      match knth ts len' with
      | Some t =>
          if tvar_at h p' t
          then let (R, p2) := rstrip h (rev (klist ts)) p in
               Entry h (kof_list (rev R)) (length R) p2
          else Entry h ts len p
      | None => Entry h ts len p
      end
  | _, _ => Entry h ts len p
  end.

(** The composite of an entry whose targets [ts1] are already mapped
    (absolute); [s] is its absolute pass-through start. *)
Definition ecomp (h : option label) (ts1 : kseq target) (len s : nat) : entry :=
  if Nat.leb (thv h) s
  then estrip h ts1 len (s - thv h + tauv h)
  else let ex := aextra h s in
       estrip h (kof_list (klist ts1 ++ ex)) (len + length ex) (tauv h).

(** ** Putting the result in normal form *)

Definition bl0 : tree nat := th_tree.

(** Add [a]'s entries for labels the composite has no entry for. *)
Definition add_aonly (W : counts) (es : atrie entry) : atrie entry :=
  fold_right (fun e es =>
                let h := elabel e in
                match aget (label_key h) es with
                | Some _ => es
                | None => aupdate (label_key h) (fun _ => adrop h (dval W (label_key h))) es
                end) es aentries.

(** Identity starts of the labels with no entry of [a]. *)
Definition jstarts (W : counts) : counts :=
  fold_right (fun e c => cset c (label_key (elabel e)) None) (ctotal wa W) aentries.

(** Remove an entry that is the identity relative to the root. *)
Definition drop_ident (R : counts) (es : atrie entry) (k : positive) : atrie entry :=
  match aget k es with
  | Some (Entry _ KNil 0 p) =>
      if oeqb (cget R k) (Some p) then aupdate k (fun _ => None) es else es
  | _ => es
  end.

(** An absolute gap entry. *)
Definition agap (k : positive) (p : nat) : option entry :=
  match key_label k with
  | Some l => if Pos.eqb (label_key l) k then Some (Entry l KNil 0 p) else None
  | None => None
  end.

Definition add_gap_at (I R : counts) (es : atrie entry) (k : positive) : atrie entry :=
  match aget k es with
  | Some _ => es
  | None => if Nat.ltb (dval R k) (dval I k)
            then aupdate k (fun _ => agap k (dval I k)) es else es
  end.

Definition finish (W : counts) (es : atrie entry) (visited : list positive) : nadj :=
  let es1 := add_aonly W es in
  let R := cmin (aann es1) (jstarts W) in
  let keys_a := map (fun e => label_key (elabel e)) aentries in
  let es2 := fold_left (drop_ident R) (visited ++ keys_a) es1 in
  let I := ctotal wa W in
  let es3 := fold_left (add_gap_at I R) (map fst (elements (c_exc W))) es2 in
  NAdj R (arebase R es3).

(** Payloads only care about named labels: drop the bound label. *)
Definition restrict (c : nadj) : nadj :=
  match c with
  | NAdj R es =>
      let kN := label_key None in
      let es' := aupdate kN (fun _ => None) es in
      match cget (aann es') kN with
      | None => NAdj (cset R kN None) es'
      | Some n => NAdj (cset R kN (Some (dval R kN + n))) (arebase (cone kN n) es')
      end
  end.

(** ** The traversal *)

Fixpoint ncomp (b : nadj) (B : counts) {struct b} : nadj :=
  match b with
  | NAdj r es =>
      let tc := fun (B' : counts) (t : target) =>
                  match t with
                  | TVar y j => rtarget (napply a (mk_rvar y (dval B' (label_key y) + j)))
                  | TBind u rho => TBind u (restrict (ncomp rho B'))
                  end in
      let ec := fun (B' : counts) (e : entry) =>
                  match e with
                  | Entry h ts len p =>
                      ecomp h (kmap th tau tc bl0 B' ts) len (dval B' (label_key h) + p)
                  end in
      let P := cplus B r in
      finish (cadd B r) (atmap th tau ec bl0 P es) (@atvisit entry bl0 P (fun k => k) es)
  end.

Definition compose (b : nadj) : nadj := ncomp b cnone.

End Compose.
