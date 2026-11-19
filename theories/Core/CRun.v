(** * The context-form pass, reworked so that a step only touches what moves

    The pass of [CForm] re-tidies a whole form after every merge.  This is
    the reworked pass of [proto/comprehension/rforms.py]:

    - The expression is processed from its end ([rnorm]), as [HNorm] does:
      each new form enters on the left of the settled word, and its
      outputs and inputs move right, form by form, as far as they go
      ([settle]).
    - A form that receives items places only those: new inputs and
      outputs by insertion ([place_in_inward], [place_out_up], ...), new
      reads taken as early as they go ([reread]), new restores absorbed
      ([absorb_new]).
    - Only items that just arrived in a form are tried against the next
      one; a boundary is looked at again in full when an input of the
      form to its right is cancelled or the form to its left loses an
      input.
    - A chain of lifts is applied in one go ([lift_many]), absorbing
      restores innermost first.
    - Absorption takes a restore whose read reaches its output through
      outputs it commutes with ([absorb2]).

    To know which items are new, an [iform] is a [CForm.form] with ids for
    its outputs and inputs.  Every operation computes its form with
    operations of [CForm] (or new ones proved sound here) and moves the
    ids along; the ids only decide what is tried, so soundness does not
    depend on them ([rrun_sound], [cr_eq_correct]). *)

From Stdlib Require Import List Bool Arith Lia PArith.
From ShiftedNames.Core Require Import Label Normalise GEval CNorm Comp CSound CComplete CForm.
Import ListNotations.

Record iform : Type := mkI { ff : form; oids : list positive; iids : list positive }.

Inductive iitem : Type :=
| JF (f : iform)
| JA (L : list lexp) (n : nat).

Definition strip (it : iitem) : item := match it with JF f => IF (ff f) | JA L n => IA L n end.

Definition mem (x : positive) (l : list positive) : bool := existsb (Pos.eqb x) l.

Fixpoint index_of (x : positive) (l : list positive) : option nat :=
  match l with [] => None | y :: l' => if Pos.eqb x y then Some 0 else option_map S (index_of x l') end.

(** [n] fresh ids from [c]. *)
Fixpoint pseq (c : positive) (n : nat) : list positive :=
  match n with 0 => [] | S n' => c :: pseq (Pos.succ c) n' end.

Definition padd (c : positive) (n : nat) : positive := Nat.iter n Pos.succ c.

Fixpoint mapi_from {X Y} (k : nat) (g : nat -> X -> Y) (l : list X) : list Y :=
  match l with [] => [] | a :: l' => g k a :: mapi_from (S k) g l' end.

Definition tdep (t : tgt) : option nat := match t with TR _ _ d => Some d | TT _ _ => None end.

Definition is_dep (j : nat) (t : tgt) : bool := match tdep t with Some d => Nat.eqb d j | None => false end.

Section Run.

Variable F : order.

Definition isz (f : iform) : nat := length (fout (ff f)) + length (fin (ff f)).

Definition iempty (f : iform) : bool := fempty (ff f).

Definition ids_of (f : iform) : list positive := oids f ++ iids f.

(** ** Placing items by insertion *)

(** Inputs [k] and [k+1] swapped when they sort the other way. *)
Definition iswap (k : nat) (f : iform) : option iform :=
  match nth_error (fin (ff f)) k, nth_error (fin (ff f)) (S k) with
  | Some (a, _), Some (b, _) =>
      if before F b a then Some (mkI (mkF (fout (ff f)) (swap_at k (fin (ff f)))) (oids f) (swap_at k (iids f)))
      else None
  | _, _ => None
  end.

(** Outputs [k] and [k+1] swapped, as [CForm.oswap] allows. *)
Definition ioswap (k : nat) (f : iform) : option iform :=
  match oswap F k (ff f) with Some g => Some (mkI g (swap_at k (oids f)) (iids f)) | None => None end.

Fixpoint in_inward (fuel k : nat) (f : iform) : iform :=
  match fuel with 0 => f | S fuel' => match iswap k f with Some g => in_inward fuel' (S k) g | None => f end end.

Fixpoint in_outward (fuel k : nat) (f : iform) : iform :=
  match fuel, k with
  | S fuel', S k' => match iswap k' f with Some g => in_outward fuel' k' g | None => f end
  | _, _ => f
  end.

Fixpoint out_up (fuel k : nat) (f : iform) : iform :=
  match fuel, k with
  | S fuel', S k' => match ioswap k' f with Some g => out_up fuel' k' g | None => f end
  | _, _ => f
  end.

Fixpoint out_down (fuel k : nat) (f : iform) : iform :=
  match fuel with 0 => f | S fuel' => match ioswap k f with Some g => out_down fuel' (S k) g | None => f end end.

(** Swaps do not change the size, so it is worked out once. *)
Definition place_in_inward (ks : list nat) (f : iform) : iform := let n := isz f in fold_left (fun f k => in_inward n k f) ks f.
Definition place_in_outward (ks : list nat) (f : iform) : iform := let n := isz f in fold_left (fun f k => in_outward n k f) ks f.
Definition place_out_up (ks : list nat) (f : iform) : iform := let n := isz f in fold_left (fun f k => out_up n k f) ks f.
Definition place_out_down (ks : list nat) (f : iform) : iform := let n := isz f in fold_left (fun f k => out_down n k f) ks f.

(** The positions from [a] to the end of a list of length [n]. *)
Definition from (a n : nat) : list nat := seq a (n - a).

(** Selected reads taken as early as they go; [ids] are the ids of the
    inputs, walked alongside. *)
Fixpoint rr (sel : positive -> tgt -> bool) (O : list lexp) (ids : list positive) (I : list (lexp * tgt)) : list (lexp * tgt) :=
  match I with
  | [] => []
  | (l, t) :: I' => (l, if sel (hd xH ids) t then ntgt F O t else t) :: rr sel O (tl ids) I'
  end.

Definition reread (sel : positive -> tgt -> bool) (f : iform) : iform :=
  mkI (mkF (fout (ff f)) (rr sel (fout (ff f)) (iids f) (fin (ff f)))) (oids f) (iids f).

(** ** Absorbing a restore *)

(** The output a read of [l₀] at depth [d] reaches, through outputs on
    labels ordered against [l]. *)
Fixpoint slot_go (l : lexp) (O : list lexp) (k j : nat) : option nat :=
  match k with
  | 0 => None
  | S k' =>
      match nth_error O j with
      | Some o => if lexp_eqb o l then Some j else if kd F l o then slot_go l O k' (S j) else None
      | None => None
      end
  end.

Definition set_in (p : nat) (t : tgt) (f : form) : form :=
  mkF (fout f) (mapi_from 0 (fun q '(l, s) => (l, if Nat.eqb q p then t else s)) (fin f)).

(** Checked with [if], not [&&], which [vm_compute] evaluates eagerly. *)
Fixpoint allkd (l : lexp) (L : list lexp) : bool :=
  match L with [] => true | o :: L' => if kd F l o then allkd l L' else false end.

Fixpoint allkd_in (l : lexp) (I : list (lexp * tgt)) : bool :=
  match I with [] => true | (m, _) :: I' => if kd F l m then allkd_in l I' else false end.

Definition absorb2 (p : nat) (f : form) : option (nat * form) :=
  match nth_error (fin f) p with
  | Some (l, TR z i d) =>
      if lexp_eqb z l then if Nat.eqb i 0 then
        match slot_go l (fout f) (length (fout f)) d with
        | Some j =>
            if allkd l (skipn (S j) (fout f)) then if allkd_in l (skipn (S p) (fin f)) then
              option_map (fun g => (j, g)) (absorb_at F j p (set_in p (TR l 0 j) f))
            else None else None
        | None => None
        end
      else None else None
  | _ => None
  end.

Definition iabsorb (p : nat) (f : iform) : option iform :=
  match absorb2 p (ff f) with
  | Some (j, g) =>
      let f1 := reread (fun _ t => is_dep j t) (mkI g (remove_at j (oids f)) (remove_at p (iids f))) in
      let f2 := place_out_up (from j (length (fout (ff f1)))) f1 in
      Some (place_in_outward (from p (length (fin (ff f2)))) f2)
  | None => None
  end.

Fixpoint absorb_scan (new : list positive) (f : iform) (p : nat) (ids : list positive) : option iform :=
  match ids with
  | [] => None
  | x :: ids' =>
      if mem x new then
        match iabsorb p f with Some g => Some g | None => absorb_scan new f (S p) ids' end
      else absorb_scan new f (S p) ids'
  end.

Fixpoint absorb_new (fuel : nat) (new : list positive) (f : iform) : iform :=
  match new with
  | [] => f
  | _ =>
      match fuel with
      | 0 => f
      | S fuel' => match absorb_scan new f 0 (iids f) with Some g => absorb_new fuel' new g | None => f end
      end
  end.

(** ** Composing, with ids *)

Fixpoint popin_i (o : lexp) (rem : list (positive * lexp)) : option (option (list (positive * lexp))) :=
  match rem with
  | [] => Some None
  | (x, l) :: r =>
      if lexp_eqb l o then Some (Some r)
      else if kd F l o then
        match popin_i o r with
        | Some (Some r') => Some (Some ((x, l) :: r'))
        | Some None => Some None
        | None => None
        end
      else None
  end.

Fixpoint popall_i (O1 : list (positive * lexp)) (rem : list (positive * lexp)) (passed : list positive) :
  option (list (positive * lexp) * list positive) :=
  match O1 with
  | [] => Some (rem, passed)
  | (y, o) :: O1' =>
      match popin_i o rem with
      | Some (Some rem') => popall_i O1' rem' passed
      | Some None => popall_i O1' rem (passed ++ [y])
      | None => None
      end
  end.

(** [f1 ⨾ f2] as one form; the new outputs and inputs placed.  Also the
    ids of the outputs and inputs that came from [f1], and whether an
    input of [f2] was cancelled. *)
Definition icompose (f1 f2 : iform) : option (iform * list positive * list positive * bool) :=
  match compose F (ff f1) (ff f2),
        popall_i (combine (oids f1) (fout (ff f1))) (combine (iids f2) (map fst (fin (ff f2)))) [] with
  | Some g, Some (rem, passed) =>
      let n1 := length (fin (ff f1)) in
      let n2 := length (fout (ff f2)) in
      let canc := negb (Nat.eqb (length rem) (length (fin (ff f2)))) in
      let g1 := reread (fun x _ => mem x (iids f1)) (mkI g (oids f2 ++ passed) (iids f1 ++ map fst rem)) in
      let g2 := place_in_inward (rev (seq 0 n1)) g1 in
      let g3 := if canc then place_in_outward (from n1 (length (fin (ff g2)))) g2 else g2 in
      let g4 := place_out_up (from n2 (length (fout (ff g3)))) g3 in
      Some (absorb_new (isz g4 + 1) (iids f1) g4, passed, iids f1, canc)
  | _, _ => None
  end.

(** Item [x] of [f1] moved into [f2] on its own: the two forms, the ids
    that arrived, whether an input of [f2] was cancelled, and whether
    [f1] lost an input. *)
Definition imove (f1 f2 : iform) (x : positive) : option (iform * iform * list positive * bool * bool) :=
  match index_of x (oids f1) with
  | Some j =>
      match out_first F j (ff f1) with
      | Some (o, f1') =>
          match icompose (mkI (weak o) [x] []) f2 with
          | Some (g, no, _, canc) =>
              let f1n := reread (fun _ t => is_dep j t) (mkI f1' (remove_at j (oids f1)) (iids f1)) in
              Some (place_out_up (from j (length (fout (ff f1n)))) f1n, g, no, canc, false)
          | None => None
          end
      | None => None
      end
  | None =>
      match index_of x (iids f1) with
      | Some p =>
          match in_first F p (ff f1) with
          | Some (h, t, f1') =>
              match icompose (mkI (mkF [] [(h, t)]) [] [x]) f2 with
              | Some (g, _, ni, canc) =>
                  let f1n := mkI f1' (oids f1) (remove_at p (iids f1)) in
                  Some (place_in_outward (from p (length (fin (ff f1n)))) f1n, g, ni, canc, true)
              | None => None
              end
          | None => None
          end
      | None => None
      end
  end.

(** ** The word *)

Fixpoint try_ids (f1 f2 : iform) (xs cands : list positive) : option (iform * iform * list positive * bool * bool) :=
  match xs with
  | [] => None
  | x :: xs' =>
      if mem x cands then match imove f1 f2 x with Some r => Some r | None => try_ids f1 f2 xs' cands end
      else try_ids f1 f2 xs' cands
  end.

Definition work : Type := list (nat * option (list positive)).

(** The candidates of [f1] moved into [f2] one at a time, while any can
    move.  Also the boundaries to look at afterwards, the latest first. *)
Fixpoint moves (fuel k : nat) (f1 f2 : iform) (cands : list positive) (acc : work) : iform * iform * work :=
  match fuel with
  | 0 => (f1, f2, acc)
  | S fuel' =>
      match try_ids f1 f2 (ids_of f1) cands with
      | Some (f1', g, new, canc, lost) =>
          let acc1 := (S k, Some new) :: acc in
          let acc2 := if lost then match k with 0 => acc1 | S k' => (k', None) :: acc1 end else acc1 in
          moves fuel' k f1' g (if canc then ids_of f1' else cands) acc2
      | None => (f1, f2, acc)
      end
  end.

Definition put2 (k : nat) (st : list iitem) (mid : list iitem) : list iitem :=
  firstn k st ++ mid ++ skipn (S (S k)) st.

(** One boundary from the work list looked at. *)
Definition step (s : list iitem * work) : list iitem * work :=
  let '(st, w) := s in
  match w with
  | [] => (st, [])
  | (k, cands) :: w' =>
      match nth_error st k, nth_error st (S k) with
      | Some (JF f1), Some (JF f2) =>
          let merged :=
            match cands with
            | None => icompose f1 f2
            | Some _ => None
            end in
          match merged with
          | Some (g, no, ni, _) =>
              if iempty g then (put2 k st [], w')
              else (put2 k st [JF g], (k, Some (no ++ ni)) :: w')
          | None =>
              let c := match cands with Some c => c | None => ids_of f1 end in
              let '(f1', g, acc) := moves (isz f1 + 1) k f1 f2 c [] in
              if iempty f1' then (put2 k st [JF g], acc ++ match k with 0 => w' | S k' => (k', None) :: w' end)
              else (put2 k st [JF f1'; JF g], acc ++ w')
          end
      | _, _ => (st, w')
      end
  end.

(** Steps until the work list is empty, at most [2^(size of p)]; the
    fuel is binary so that it costs nothing to build. *)
Fixpoint settle (p : positive) (s : list iitem * work) : list iitem * work :=
  match snd s with
  | [] => s
  | _ =>
      match p with
      | xH => step s
      | xO p' => settle p' (settle p' s)
      | xI p' => step (settle p' (settle p' s))
      end
  end.

Definition big : positive := 1099511627776%positive.

Definition wsize (st : list iitem) : nat :=
  fold_right (fun it n => match it with JF f => isz f + n | JA L _ => length L + n end) (length st) st.

Definition insert (it : iitem) (st : list iitem) : list iitem :=
  match it with
  | JF f => if iempty f then st else fst (settle big (it :: st, [(0, None)]))
  | JA _ _ => it :: st
  end.

(** ** Expressions *)

Definition fresh (f : form) (c : positive) : iform * positive :=
  let a := length (fout f) in let b := length (fin f) in (mkI f (pseq c a) (pseq (padd c a) b), padd c (a + b)).

(** A form under the lifts [L], outermost first, built at once: the
    outputs of [L] on top, an input restoring each, the reads of [f]
    deeper by [length L]. *)
Definition shift_ts (L : list lexp) (t : tgt) : tgt :=
  match t with TR z i d => TR z i (length L + d) | TT u p => TT u (fold_right PShift p L) end.

Definition lift_n (L : list lexp) (f : form) : form :=
  mkF (L ++ fout f) (mapi_from 0 (fun k h => (h, TR h 0 k)) L ++ map (fun '(g, t) => (g, shift_ts L t)) (fin f)).

(** An item under the lifts [L], outermost first. *)
Definition lift_many (L : list lexp) (it : iitem) (c : positive) : iitem * positive :=
  match it with
  | JA L' n => (JA (L ++ L') n, c)
  | JF f =>
      let n := length L in
      let f0 := mkI (lift_n L (ff f)) (pseq c n ++ oids f) (pseq (padd c n) n ++ iids f) in
      (* restores absorbed innermost first, counting those kept *)
      let '(f1, k) := fold_left (fun '(g, k) p => match iabsorb p g with Some g' => (g', k) | None => (g, S k) end)
                                (rev (seq 0 n)) (f0, 0) in
      let f2 := place_in_inward (rev (seq 0 k)) f1 in
      (JF (place_out_down (rev (seq 0 (Nat.min k (length (fout (ff f2)))))) f2), padd c (n + n))
  end.

Fixpoint insert_lifted (L : list lexp) (w : list iitem) (st : list iitem) (c : positive) : list iitem * positive :=
  match w with
  | [] => (st, c)
  | it :: w' =>
      let '(st1, c1) := insert_lifted L w' st c in
      let '(it', c2) := lift_many L it c1 in
      (insert it' st1, c2)
  end.

(** [e] in front of the settled word [st]; [c] the next fresh id. *)
Fixpoint rnorm (e : aexp) (st : list iitem) (c : positive) {struct e} : list iitem * positive :=
  match e with
  | AId => (st, c)
  | AAtom n => (insert (JA [] n) st, c)
  | ACompose a b => let '(st1, c1) := rnorm a st c in rnorm b st1 c1
  | AOuter h a => let '(f, c1) := fresh (weak h) c in rnorm a (insert (JF f) st) c1
  | AInner h t a =>
      let '(f, c1) := fresh (entry h t) c in
      let fix peel (L : list lexp) (a : aexp) (st : list iitem) (c : positive) {struct a} : list iitem * positive :=
        match a with
        | ALift h' a' => peel (L ++ [h']) a' st c
        | _ => let '(w, c1) := rnorm a [] c in insert_lifted L w st c1
        end in
      peel [h] a (insert (JF f) st) c1
  | ALift h a =>
      let fix peel (L : list lexp) (a : aexp) (st : list iitem) (c : positive) {struct a} : list iitem * positive :=
        match a with
        | ALift h' a' => peel (L ++ [h']) a' st c
        | _ => let '(w, c1) := rnorm a [] c in insert_lifted L w st c1
        end in
      peel [h] a st c
  end.

Definition rrun (e : aexp) : fword := map strip (fst (rnorm e [] xH)).

End Run.

(** The chain of lifts inside [rnorm], as a function of its own. *)
Section Peel.
Variable F : order.
Fixpoint peel (L : list lexp) (a : aexp) (st : list iitem) (c : positive) {struct a} : list iitem * positive :=
  match a with
  | ALift h' a' => peel (L ++ [h']) a' st c
  | _ => let '(w, c1) := rnorm F a [] c in insert_lifted F L w st c1
  end.
End Peel.

Lemma rnorm_lift F h a st c : rnorm F (ALift h a) st c = peel F [h] a st c.
Proof. reflexivity. Qed.

Lemma rnorm_inner F h t a st c :
  rnorm F (AInner h t a) st c = let '(f, c1) := fresh (entry h t) c in peel F [h] a (insert F (JF f) st) c1.
Proof. reflexivity. Qed.

(** ** Soundness *)

Section Sound.

Variable F : order.
Variable M : cmodel.
Hypothesis HM : ccons F M.

Local Notation fd := (fden M).
Local Notation wd := (fun st x => wden M (map strip st) x).

(** *** Inputs and outputs swapped *)

Lemma iswap_sound k f g x : iswap F k f = Some g -> fd (ff g) x = fd (ff f) x.
Proof.
  unfold iswap; destruct (nth_error (fin (ff f)) k) as [[a ta]|] eqn:Ea; [|discriminate].
  destruct (nth_error (fin (ff f)) (S k)) as [[b tb]|] eqn:Eb; [|discriminate].
  destruct (before F b a) eqn:B; [|discriminate]; intros H; injection H as <-; cbn [ff].
  destruct (split_at _ k _ Ea) as [A [R [E LA]]]; subst k.
  rewrite E, nth_error_app2 in Eb by lia; rewrite Nat.sub_succ_l, Nat.sub_diag in Eb by lia.
  destruct R as [|[b' tb'] B']; [discriminate|]; cbn in Eb; injection Eb as -> ->.
  unfold fden; cbn [fout fin]; rewrite E, swap_at_app, !pushes_app; cbn [pushes]; f_equal.
  apply (kd_push_push F M HM); apply bk; exact B.
Qed.

Lemma ioswap_sound k f g x : ioswap F k f = Some g -> fd (ff g) x = fd (ff f) x.
Proof.
  unfold ioswap; destruct (oswap F k (ff f)) as [g'|] eqn:E; [|discriminate]; intros H; injection H as <-.
  apply (oswap_sound F M HM k _ _ _ E).
Qed.

Lemma in_inward_sound fuel k f x : fd (ff (in_inward F fuel k f)) x = fd (ff f) x.
Proof.
  revert k f; induction fuel as [|fuel IH]; intros k f; [reflexivity|]; cbn.
  destruct (iswap F k f) as [g|] eqn:E; [rewrite IH; apply (iswap_sound k), E|reflexivity].
Qed.

Lemma in_outward_sound fuel k f x : fd (ff (in_outward F fuel k f)) x = fd (ff f) x.
Proof.
  revert k f; induction fuel as [|fuel IH]; intros [|k] f; try reflexivity; cbn.
  destruct (iswap F k f) as [g|] eqn:E; [rewrite IH; apply (iswap_sound k), E|reflexivity].
Qed.

Lemma out_up_sound fuel k f x : fd (ff (out_up F fuel k f)) x = fd (ff f) x.
Proof.
  revert k f; induction fuel as [|fuel IH]; intros [|k] f; try reflexivity; cbn.
  destruct (ioswap F k f) as [g|] eqn:E; [rewrite IH; apply (ioswap_sound k), E|reflexivity].
Qed.

Lemma out_down_sound fuel k f x : fd (ff (out_down F fuel k f)) x = fd (ff f) x.
Proof.
  revert k f; induction fuel as [|fuel IH]; intros k f; [reflexivity|]; cbn.
  destruct (ioswap F k f) as [g|] eqn:E; [rewrite IH; apply (ioswap_sound k), E|reflexivity].
Qed.

Lemma fold_place (step : nat -> iform -> iform) ks f x :
  (forall k g, fd (ff (step k g)) x = fd (ff g) x) ->
  fd (ff (fold_left (fun g k => step k g) ks f)) x = fd (ff f) x.
Proof. revert f; induction ks as [|k ks IH]; intros f H; [reflexivity|]; cbn; rewrite IH, H by assumption; reflexivity. Qed.

Lemma place_in_inward_sound ks f x : fd (ff (place_in_inward F ks f)) x = fd (ff f) x.
Proof. unfold place_in_inward; apply (fold_place (fun k g => in_inward F (isz f) k g)); intros; apply in_inward_sound. Qed.

Lemma place_in_outward_sound ks f x : fd (ff (place_in_outward F ks f)) x = fd (ff f) x.
Proof. unfold place_in_outward; apply (fold_place (fun k g => in_outward F (isz f) k g)); intros; apply in_outward_sound. Qed.

Lemma place_out_up_sound ks f x : fd (ff (place_out_up F ks f)) x = fd (ff f) x.
Proof. unfold place_out_up; apply (fold_place (fun k g => out_up F (isz f) k g)); intros; apply out_up_sound. Qed.

Lemma place_out_down_sound ks f x : fd (ff (place_out_down F ks f)) x = fd (ff f) x.
Proof. unfold place_out_down; apply (fold_place (fun k g => out_down F (isz f) k g)); intros; apply out_down_sound. Qed.

(** *** Targets replaced by equal ones *)

Lemma pushes_mapi O (g : nat -> lexp * tgt -> lexp * tgt) I k b x :
  (forall q l t, nth_error I q = Some (l, t) -> fst (g (k + q) (l, t)) = l /\ tden M O (snd (g (k + q) (l, t))) x = tden M O t x) ->
  pushes M O (mapi_from k g I) b x = pushes M O I b x.
Proof.
  revert k; induction I as [|[l t] I IH]; intros k H; [reflexivity|]; cbn [mapi_from pushes].
  destruct (g k (l, t)) as [l' t'] eqn:G; destruct (H 0 l t eq_refl) as [H1 H2]; rewrite Nat.add_0_r, G in H1, H2; cbn in H1, H2; subst l'.
  rewrite IH, H2; [reflexivity|]; intros q l2 t2 N; replace (S k + q) with (k + S q) by lia; apply (H (S q)), N.
Qed.

Lemma rr_sound sel O ids I b x : pushes M O (rr F sel O ids I) b x = pushes M O I b x.
Proof.
  revert ids; induction I as [|[l t] I IH]; intros ids; [reflexivity|]; cbn [rr pushes].
  rewrite IH; destruct (sel _ t); [rewrite (ntgt_sound F M HM)|]; reflexivity.
Qed.

Lemma reread_sound sel f x : fd (ff (reread F sel f)) x = fd (ff f) x.
Proof. unfold reread, fden; cbn [ff fout fin]; apply rr_sound. Qed.

Lemma slot_go_sound l O k j j' y : slot_go F l O k j = Some j' -> cname l 0 (popn M O j' y) = cname l 0 (popn M O j y).
Proof.
  revert j; induction k as [|k IH]; intros j; cbn; [discriminate|].
  destruct (nth_error O j) as [o|] eqn:N; [|discriminate].
  destruct (lexp_eqb o l) eqn:E; [intros H; injection H as <-; reflexivity|].
  destruct (kd F l o) eqn:K; [|discriminate]; intros H; rewrite (IH _ H).
  assert (L : j < length O) by (apply nth_error_Some; congruence).
  rewrite (popn_S M O j y L), (nth_error_nth O j LNone N); apply (cname_pop_other F M HM), kdk, K.
Qed.

Lemma absorb2_sound p f j g x : absorb2 F p f = Some (j, g) -> fd g x = fd f x.
Proof.
  unfold absorb2; destruct (nth_error (fin f) p) as [[l [z i d|u q]]|] eqn:Np; try discriminate.
  destruct (lexp_eqb z l) eqn:C1; [|discriminate]; destruct (Nat.eqb i 0) eqn:C2; [|discriminate].
  apply lexp_eqb_true in C1; apply Nat.eqb_eq in C2; subst z i.
  destruct (slot_go F l (fout f) (length (fout f)) d) as [j'|] eqn:S; [|discriminate].
  destruct (allkd F l _); [|discriminate]; destruct (allkd_in F l _); [|discriminate].
  destruct (absorb_at F j' p (set_in p (TR l 0 j') f)) as [g'|] eqn:A; cbn; [|discriminate].
  intros H; injection H as <- <-.
  rewrite (absorb_at_sound F M HM _ _ _ _ x A).
  unfold set_in, fden; cbn [fout fin]; apply pushes_mapi; intros q l' t N; cbn.
  split; [reflexivity|]; destruct (Nat.eqb q p) eqn:Q; [|reflexivity].
  apply Nat.eqb_eq in Q; subst q; rewrite Np in N; injection N as <- <-; cbn [tden].
  apply (slot_go_sound _ _ _ _ _ _ S).
Qed.

Lemma iabsorb_sound p f g x : iabsorb F p f = Some g -> fd (ff g) x = fd (ff f) x.
Proof.
  unfold iabsorb; destruct (absorb2 F p (ff f)) as [[j g']|] eqn:A; [|discriminate]; intros H; injection H as <-.
  rewrite place_in_outward_sound, place_out_up_sound, reread_sound; cbn [ff].
  apply (absorb2_sound _ _ _ _ _ A).
Qed.

Lemma absorb_scan_sound new f p ids g x : absorb_scan F new f p ids = Some g -> fd (ff g) x = fd (ff f) x.
Proof.
  revert p; induction ids as [|y ids IH]; intros p; cbn; [discriminate|].
  destruct (mem y new); [|apply IH].
  destruct (iabsorb F p f) as [g'|] eqn:A; [intros H; injection H as <-; apply (iabsorb_sound p), A|apply IH].
Qed.

Lemma absorb_new_sound fuel new f x : fd (ff (absorb_new F fuel new f)) x = fd (ff f) x.
Proof.
  revert f; induction fuel as [|fuel IH]; intros f; cbn; destruct new; try reflexivity.
  destruct (absorb_scan F _ f 0 _) as [g|] eqn:A; [rewrite IH; apply (absorb_scan_sound _ f 0 (iids f) g x A)|reflexivity].
Qed.

(** *** Composing and moving *)

Lemma icompose_sound f1 f2 g no ni canc x : icompose F f1 f2 = Some (g, no, ni, canc) ->
  fd (ff g) x = fd (ff f1) (fd (ff f2) x).
Proof.
  unfold icompose.
  destruct (compose F (ff f1) (ff f2)) as [g0|] eqn:C; [|discriminate].
  destruct (popall_i _ _ _) as [[rem passed]|]; [|discriminate]; intros H; injection H as <- _ _ _.
  rewrite absorb_new_sound, place_out_up_sound.
  match goal with |- context [if ?b then _ else _] => destruct b end;
    rewrite ?place_in_outward_sound, place_in_inward_sound, reread_sound; cbn [ff];
    apply (compose_sound F M HM _ _ _ x C).
Qed.

Lemma weak_sound h x : fd (weak h) x = cpop h x.
Proof. reflexivity. Qed.

Lemma imove_sound f1 f2 y f1' g new canc lost : imove F f1 f2 y = Some (f1', g, new, canc, lost) ->
  forall x, fd (ff f1') (fd (ff g) x) = fd (ff f1) (fd (ff f2) x).
Proof.
  unfold imove; intros H x.
  destruct (index_of y (oids f1)) as [j|].
  - destruct (out_first F j (ff f1)) as [[o f1o]|] eqn:O; [|discriminate].
    destruct (icompose F (mkI (weak o) [y] []) f2) as [[[[g' no] ni] c]|] eqn:C; [|discriminate].
    injection H as <- <- _ _ _.
    rewrite place_out_up_sound, reread_sound, (icompose_sound _ _ _ _ _ _ x C); cbn [ff].
    rewrite weak_sound; symmetry; apply (out_first_sound F M HM j _ _ _ _ O).
  - destruct (index_of y (iids f1)) as [p|]; [|discriminate].
    destruct (in_first F p (ff f1)) as [[[h t] f1o]|] eqn:I; [|discriminate].
    destruct (icompose F (mkI (mkF [] [(h, t)]) [] [y]) f2) as [[[[g' no] ni] c]|] eqn:C; [|discriminate].
    injection H as <- <- _ _ _.
    rewrite place_in_outward_sound, (icompose_sound _ _ _ _ _ _ x C); cbn [ff].
    symmetry; apply (in_first_sound F M HM p _ _ _ _ _ I).
Qed.


(** *** The word *)

Lemma try_ids_sound f1 f2 xs cands f1' g new canc lost : try_ids F f1 f2 xs cands = Some (f1', g, new, canc, lost) ->
  forall x, fd (ff f1') (fd (ff g) x) = fd (ff f1) (fd (ff f2) x).
Proof.
  induction xs as [|y xs IH]; cbn; [discriminate|].
  destruct (mem y cands); [|apply IH].
  destruct (imove F f1 f2 y) as [[[[[a b] c] d] e]|] eqn:E; [|apply IH].
  intros H; injection H as -> -> -> -> ->; apply (imove_sound _ _ _ _ _ _ _ _ E).
Qed.

Lemma moves_sound fuel k f1 f2 c acc f1' g acc' : moves F fuel k f1 f2 c acc = (f1', g, acc') ->
  forall x, fd (ff f1') (fd (ff g) x) = fd (ff f1) (fd (ff f2) x).
Proof.
  revert f1 f2 c acc; induction fuel as [|fuel IH]; intros f1 f2 c acc; cbn.
  - intros H; injection H as <- <- _; reflexivity.
  - destruct (try_ids F f1 f2 (ids_of f1) c) as [[[[[a b] new] canc] lost]|] eqn:T.
    + intros H x; rewrite (IH _ _ _ _ H x); apply (try_ids_sound _ _ _ _ _ _ _ _ _ T).
    + intros H; injection H as <- <- _; reflexivity.
Qed.

Lemma split2 {X} (st : list X) k a b : nth_error st k = Some a -> nth_error st (S k) = Some b ->
  st = firstn k st ++ a :: b :: skipn (S (S k)) st.
Proof.
  revert st; induction k as [|k IH]; intros [|c st] Ha Hb; cbn in *; try discriminate.
  - injection Ha as ->; destruct st as [|d st]; [discriminate|]; injection Hb as ->; reflexivity.
  - f_equal; apply IH; assumption.
Qed.

Lemma wd_app st1 st2 x : wd (st1 ++ st2) x = wd st1 (wd st2 x).
Proof. cbn; rewrite map_app; apply wden_app. Qed.

Lemma settle_step k st a b mid x : nth_error st k = Some a -> nth_error st (S k) = Some b ->
  (forall y, wd mid y = iden M (strip a) (iden M (strip b) y)) -> wd (put2 k st mid) x = wd st x.
Proof.
  intros Ha Hb H; unfold put2; pose proof (split2 st k a b Ha Hb) as E.
  set (A := firstn k st) in *; set (R := skipn (S (S k)) st) in *.
  rewrite E; rewrite !wd_app, H; reflexivity.
Qed.

Lemma step_sound s x : wd (fst (step F s)) x = wd (fst s) x.
Proof.
  destruct s as [st w]; unfold step.
  destruct w as [|[k cands] w']; [reflexivity|].
  destruct (nth_error st k) as [[f1|L1 n1]|] eqn:Ea; try reflexivity.
  destruct (nth_error st (S k)) as [[f2|L2 n2]|] eqn:Eb; try reflexivity.
  destruct (match cands with None => icompose F f1 f2 | Some _ => None end) as [[[[g no] ni] cc]|] eqn:Mg.
  - assert (G : forall y, fd (ff g) y = fd (ff f1) (fd (ff f2) y)).
    { intros y; destruct cands; [discriminate|]; apply (icompose_sound _ _ _ _ _ _ _ Mg). }
    destruct (iempty g) eqn:Em; cbn [fst]; apply (settle_step k st (JF f1) (JF f2)); auto; intros y; cbn;
      try (rewrite <- G; symmetry; apply fempty_sound, Em); try apply G.
  - destruct (moves F _ k f1 f2 _ []) as [[f1' g] acc] eqn:Mv.
    pose proof (moves_sound _ _ _ _ _ _ _ _ _ Mv) as G.
    destruct (iempty f1') eqn:Em; cbn [fst]; apply (settle_step k st (JF f1) (JF f2)); auto; intros y; cbn;
      try (rewrite <- G, (fempty_sound M (ff f1') _ Em); reflexivity); try apply G.
Qed.

Lemma settle_sound p s x : wd (fst (settle F p s)) x = wd (fst s) x.
Proof.
  revert s; induction p as [p IH|p IH|]; intros s; cbn [settle];
    destruct (snd s); try reflexivity; rewrite ?step_sound, ?IH; reflexivity.
Qed.

Lemma insert_sound it st x : wd (insert F it st) x = iden M (strip it) (wd st x).
Proof.
  destruct it as [f|L n]; cbn [insert]; [|reflexivity].
  destruct (iempty f) eqn:E; [symmetry; apply fempty_sound, E|].
  rewrite settle_sound; reflexivity.
Qed.

(** *** Lifts *)

Fixpoint liftsem (L : list lexp) (g : cU M -> cU M) (x : cU M) : cU M :=
  match L with [] => g x | h :: L' => cpush h (liftsem L' g (cpop h x)) (chd h x) end.

Lemma liftsem_ext L g g' x : (forall y, g y = g' y) -> liftsem L g x = liftsem L g' x.
Proof. intros H; revert x; induction L as [|h L IH]; intros x; cbn; [apply H|rewrite IH; reflexivity]. Qed.

Lemma liftsem_app L1 L2 g x : liftsem (L1 ++ L2) g x = liftsem L1 (liftsem L2 g) x.
Proof. revert x; induction L1 as [|h L IH]; intros x; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma liftsem_comp L g g' x : liftsem L g (liftsem L g' x) = liftsem L (fun y => g (g' y)) x.
Proof.
  revert x; induction L as [|h L IH]; intros x; cbn; [reflexivity|].
  rewrite cpop_push, chd_push, IH; reflexivity.
Qed.

Lemma liftsem_id L x : liftsem L (fun y => y) x = x.
Proof. revert x; induction L as [|h L IH]; intros x; cbn; [reflexivity|rewrite IH; apply cpush_pop]. Qed.

Lemma lift_fold_sound L f x : fd (fold_right lift_f f L) x = liftsem L (fd f) x.
Proof.
  revert x; induction L as [|h L IH]; intros x; [reflexivity|].
  change (fold_right lift_f f (h :: L)) with (lift_f h (fold_right lift_f f L)); rewrite lift_f_sound, IH; reflexivity.
Qed.

Lemma lden_app L L' n x : lden M (L ++ L') n x = liftsem L (lden M L' n) x.
Proof. revert x; induction L as [|h L IH]; intros x; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma map_shift_mapi h k (L : list lexp) :
  map (fun '(g, t) => (g, shift_t h t)) (mapi_from k (fun k h' => (h', TR h' 0 k)) L)
  = mapi_from (S k) (fun k h' => (h', TR h' 0 k)) L.
Proof. revert k; induction L as [|h' L IH]; intros k; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma map_shift_ts h L (I : list (lexp * tgt)) :
  map (fun '(g, t) => (g, shift_t h t)) (map (fun '(g, t) => (g, shift_ts L t)) I)
  = map (fun '(g, t) => (g, shift_ts (h :: L) t)) I.
Proof. induction I as [|[g [z i d|u q]] I IH]; cbn; [reflexivity| |]; rewrite IH; reflexivity. Qed.

Lemma lift_n_eq L f : lift_n L f = fold_right lift_f f L.
Proof.
  induction L as [|h L IH].
  - destruct f as [O I]; unfold lift_n; cbn; f_equal.
    induction I as [|[g [z i d|u q]] I IH]; cbn; [reflexivity| |]; rewrite IH; reflexivity.
  - change (fold_right lift_f f (h :: L)) with (lift_f h (fold_right lift_f f L)); rewrite <- IH.
    unfold lift_f, lift_n; cbn [fout fin app mapi_from]; f_equal.
    rewrite map_app, map_shift_mapi, map_shift_ts; reflexivity.
Qed.

Lemma lift_many_sound L it c x : iden M (strip (fst (lift_many F L it c))) x = liftsem L (iden M (strip it)) x.
Proof.
  destruct it as [f|L' n]; cbn [lift_many fst strip iden]; [|apply lden_app].
  match goal with |- context [fold_left ?st ?ks ?a] => remember (fold_left st ks a) as r eqn:R end.
  destruct r as [f1 k]; cbn [fst snd strip iden].
  assert (G : forall ks (gk : iform * nat), fd (ff (fst (fold_left (fun '(g, k) p => match iabsorb F p g with Some g' => (g', k) | None => (g, S k) end) ks gk))) x = fd (ff (fst gk)) x).
  { induction ks as [|p ks IH]; intros [g k0]; [reflexivity|]; cbn [fold_left]; rewrite IH.
    destruct (iabsorb F p g) as [g'|] eqn:E; cbn [fst]; [apply (iabsorb_sound p), E|reflexivity]. }
  rewrite place_out_down_sound, place_in_inward_sound.
  specialize (G (rev (seq 0 (length L))) (mkI (lift_n L (ff f)) (pseq c (length L) ++ oids f) (pseq (padd c (length L)) (length L) ++ iids f), 0)).
  rewrite <- R in G; cbn [fst] in G; rewrite G; cbn [ff]; rewrite lift_n_eq; apply lift_fold_sound.
Qed.

Lemma insert_lifted_sound L w st c x : wd (fst (insert_lifted F L w st c)) x = liftsem L (wd w) (wd st x).
Proof.
  revert c; induction w as [|it w IH]; intros c; cbn [insert_lifted].
  - cbn; symmetry; apply liftsem_id.
  - destruct (insert_lifted F L w st c) as [st1 c1] eqn:E1.
    destruct (lift_many F L it c1) as [it' c2] eqn:E2; cbn [fst].
    rewrite insert_sound.
    specialize (IH c); rewrite E1 in IH; cbn [fst] in IH; rewrite IH.
    pose proof (lift_many_sound L it c1) as Lm; rewrite E2 in Lm; cbn [fst] in Lm.
    rewrite Lm, liftsem_comp; reflexivity.
Qed.

(** *** Expressions *)

Lemma fresh_ff f c : ff (fst (fresh f c)) = f.
Proof. reflexivity. Qed.

Theorem rnorm_sound : forall e,
  (forall st c x, wd (fst (rnorm F e st c)) x = ca e (wd st x))
  /\ (forall L st c x, wd (fst (peel F L e st c)) x = liftsem L (ca e) (wd st x)).
Proof.
  assert (Peel : forall e, (forall st c x, wd (fst (rnorm F e st c)) x = ca e (wd st x)) ->
            (forall a, e <> ALift (fst a) (snd a)) ->
            forall L st c x, wd (fst (peel F L e st c)) x = liftsem L (ca e) (wd st x)).
  { intros e H1 Hn L st c x.
    assert (P : peel F L e st c = let '(w, c1) := rnorm F e [] c in insert_lifted F L w st c1)
      by (destruct e as [| | | | |h' a']; try reflexivity; exfalso; apply (Hn (h', a')); reflexivity).
    rewrite P; destruct (rnorm F e [] c) as [w c1] eqn:E.
    rewrite insert_lifted_sound; apply liftsem_ext; intros y.
    specialize (H1 [] c y); rewrite E in H1; exact H1. }
  induction e as [|n|a [IHa1 IHa2] b [IHb1 IHb2]|h a [IH1 IH2]|h t a [IH1 IH2]|h a [IH1 IH2]].
  - assert (H1 : forall st c x, wd (fst (rnorm F AId st c)) x = ca AId (wd st x)) by reflexivity.
    split; [exact H1|apply Peel; [exact H1|intros [? ?]; discriminate]].
  - assert (H1 : forall st c x, wd (fst (rnorm F (AAtom n) st c)) x = ca (AAtom n) (wd st x)).
    { intros st c x; cbn [rnorm fst]; rewrite insert_sound; reflexivity. }
    split; [exact H1|apply Peel; [exact H1|intros [? ?]; discriminate]].
  - assert (H1 : forall st c x, wd (fst (rnorm F (ACompose a b) st c)) x = ca (ACompose a b) (wd st x)).
    { intros st c x; cbn [rnorm]; destruct (rnorm F a st c) as [st1 c1] eqn:E.
      rewrite IHb1; specialize (IHa1 st c x); rewrite E in IHa1; cbn [fst] in IHa1; rewrite IHa1; reflexivity. }
    split; [exact H1|apply Peel; [exact H1|intros [? ?]; discriminate]].
  - assert (H1 : forall st c x, wd (fst (rnorm F (AOuter h a) st c)) x = ca (AOuter h a) (wd st x)).
    { intros st c x; cbn [rnorm fresh]; rewrite IH1, insert_sound; reflexivity. }
    split; [exact H1|apply Peel; [exact H1|intros [? ?]; discriminate]].
  - assert (H1 : forall st c x, wd (fst (rnorm F (AInner h t a) st c)) x = ca (AInner h t a) (wd st x)).
    { intros st c x; rewrite rnorm_inner; cbn [fresh]; rewrite IH2, insert_sound; cbn [liftsem strip iden ff].
      rewrite entry_sound, cpop_push, chd_push; reflexivity. }
    split; [exact H1|apply Peel; [exact H1|intros [? ?]; discriminate]].
  - split.
    + intros st c x; rewrite rnorm_lift, IH2; reflexivity.
    + intros L st c x; cbn [peel]; rewrite IH2, liftsem_app; apply liftsem_ext; reflexivity.
Qed.

Theorem rrun_sound e x : wden M (rrun F e) x = ca e x.
Proof. unfold rrun; rewrite (proj1 (rnorm_sound e) [] xH x); reflexivity. Qed.

End Sound.

(** ** The normaliser: the reworked pass, then [CNorm] *)

Definition cr_form (F : order) (e : aexp) : aexp := wexp (rrun F e).

Theorem cr_form_sound F e : forall M, ccons F M -> forall x : cU M, ca (cr_form F e) x = ca e x.
Proof. intros M HM x; unfold cr_form; rewrite wexp_sound, (rrun_sound F M HM); reflexivity. Qed.

Definition cr_eq (F : order) (e1 e2 : aexp) : bool := cn_eq F (cr_form F e1) (cr_form F e2).

Theorem cr_eq_correct F
  (Hirr : forall a, lt_known F a a = false)
  (Htrans : forall a b c, lt_known F a b = true -> lt_known F b c = true -> lt_known F a c = true)
  e1 e2 : cr_eq F e1 e2 = true <-> cequal F e1 e2.
Proof.
  unfold cr_eq; rewrite (CComplete.cn_eq_correct F Hirr Htrans); split; intros H M HM x.
  - rewrite <- (cr_form_sound F e1 M HM x), <- (cr_form_sound F e2 M HM x); apply H, HM.
  - rewrite (cr_form_sound F e1 M HM x), (cr_form_sound F e2 M HM x); apply H, HM.
Qed.

(** ** Examples (by computation)

    Facts [g < h], [k < h], [m < h].  The pairs of [CForm.Examples] get
    one word each, and the lift law holds after sorting has moved the
    lifted output down: [⟦ h | ⟦ \ g as _ ⟧ ⟧] is [⟦ \ g as _ ⟧]. *)
Module Examples.
Import CForm.Examples.
Definition L1 := ALift h (W g).
Lemma W12 : rrun F W1 = [IF (mkF [k] [(g, TR m 0 1); (h, TR LNone 0 0)])] /\ rrun F W2 = rrun F W1.
Proof. split; vm_compute; reflexivity. Qed.
Lemma Y12 : rrun F Y1 = rrun F Y2. Proof. vm_compute; reflexivity. Qed.
Lemma V12 : rrun F V1 = rrun F V2. Proof. vm_compute; reflexivity. Qed.
Lemma L1_law : rrun F L1 = rrun F (W g). Proof. vm_compute; reflexivity. Qed.
End Examples.
