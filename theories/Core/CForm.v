(** * Context forms, and a left-to-right pass over them

    A context form [⟦ I \ O ⟧] has outputs [O], popped in order (the first
    one first), and inputs [I], outermost first, each pushed with a
    target.  A target [TR z i d] is the name [zᵢ] read after the first
    [d] outputs have been popped: [d = 0] is a name of the form's own
    output, a read exactly at an output is that output's slot, and
    [d = length O] is a name of the identity tail.  A target [TT u p] is
    a term, with its payload read in the form's output.

    Every expression is a word of forms and lifted atoms ([of_exp]): a
    weakening is a form with one output; an input entry is a form with
    one input; a lift of a form is a form.  Adjacent forms are composed
    left to right ([compose]); where they cannot be (an output or a read
    meets an input on a label it is not ordered against), the outputs and
    inputs that can move on their own move right into the next form
    ([transfer]).  Inside a form, inputs and outputs on ordered labels
    are sorted and reads are taken as early as they can be ([tidy]), and
    an input that restores an output nothing else needs is dropped with
    it ([absorb]).  Every operation is sound in every comprehension model
    consistent with the facts ([run_sound]). *)

From Stdlib Require Import NArith List Bool Arith Lia.
From ShiftedNames.Core Require Import Label Normalise GEval CNorm Comp CSound CComplete.
From ShiftedNames.Core Require Export CSpec.
Import ListNotations.

Section Pass.

Variable F : order.

Definition clamp (n : nat) (t : tgt) : tgt :=
  match t with TR z i d => TR z i (Nat.min d n) | TT _ _ => t end.

(** A read taken as early as it can be: an output before it on its label
    moves its index, one on a label ordered against it does nothing. *)
Fixpoint nread (O : list lexp) (z : lexp) (i d : nat) {struct d} : tgt :=
  match d with
  | 0 => TR z i 0
  | S d' =>
      let o := nth d' O LNone in
      if Nat.ltb d' (length O) then
        if lexp_eqb o z then nread O z (S i) d'
        else if kd F z o then nread O z i d' else TR z i d
      else TR z i d
  end.

Definition ntgt (O : list lexp) (t : tgt) : tgt :=
  match t with TR z i d => nread O z i d | TT _ _ => t end.

(** An output [o] of the form before, popped from the inputs [rem] of the
    form after: it cancels the first input on [o] (Some (Some rem')),
    passes them all (Some None), or meets one on a label it is not
    ordered against (None). *)
Fixpoint popin (o : lexp) (rem : list (lexp * tgt)) : option (option (list (lexp * tgt))) :=
  match rem with
  | [] => Some None
  | (l, t) :: r =>
      if lexp_eqb l o then Some (Some r)
      else if kd F l o then
        match popin o r with
        | Some (Some r') => Some (Some ((l, t) :: r'))
        | Some None => Some None
        | None => None
        end
      else None
  end.

(** All the outputs [O1], in order: the inputs left and the outputs
    passed, after each. *)
Fixpoint popall (O1 : list lexp) (rem : list (lexp * tgt)) (passed : list lexp) :
  option (list (list (lexp * tgt) * list lexp)) :=
  match O1 with
  | [] => Some [(rem, passed)]
  | o :: O1' =>
      match popin o rem with
      | Some (Some rem') => option_map (cons (rem, passed)) (popall O1' rem' passed)
      | Some None => option_map (cons (rem, passed)) (popall O1' rem (passed ++ [o]))
      | None => None
      end
  end.

(** A name read through inputs: one of their targets, or a name of
    what they are pushed on. *)
Fixpoint rthrough (rem : list (lexp * tgt)) (z : lexp) (i : nat) : option (tgt + nat) :=
  match rem with
  | [] => Some (inr i)
  | (l, t) :: r =>
      if lexp_eqb l z then match i with 0 => Some (inl t) | S i' => rthrough r z i' end
      else if kd F l z then rthrough r z i else None
  end.

Definition newt (n2 : nat) (f2 : aexp) (st : list (list (lexp * tgt) * list lexp)) (t : tgt) : option tgt :=
  match t with
  | TR z i d =>
      match nth_error st d with
      | Some (rem, passed) =>
          match rthrough rem z i with
          | Some (inl t') => Some t'
          | Some (inr i') => Some (TR z i' (n2 + length passed))
          | None => None
          end
      | None => None
      end
  | TT u p => Some (TT u (PComp f2 p))
  end.

(** [f1 ⨾ f2] as one form, [f1] acting first on a variable. *)
Definition compose (f1 f2 : form) : option form :=
  let O2 := fout f2 in
  let I2 := map (fun '(l, t) => (l, clamp (length O2) t)) (fin f2) in
  match popall (fout f1) I2 [] with
  | Some st =>
      let '(rem, passed) := last st ([], []) in
      match omap (fun '(l, t) => option_map (fun t' => (l, t')) (newt (length O2) (fexp f2) st t)) (fin f1) with
      | Some I1 => Some (mkF (O2 ++ passed) (I1 ++ rem))
      | None => None
      end
  | None => None
  end.

(** *** Inside a form *)

(** One pass of a bubble sort of the inputs. *)
Fixpoint bubble (x : lexp * tgt) (I : list (lexp * tgt)) : list (lexp * tgt) :=
  match I with
  | [] => [x]
  | y :: r => if before F (fst y) (fst x) then y :: bubble x r else x :: bubble y r
  end.

Definition sort_in (I : list (lexp * tgt)) : list (lexp * tgt) :=
  match I with [] => [] | x :: r => bubble x r end.

(** Swapping outputs [k] and [k+1]: a read between them is read after
    both. *)
Definition swap_read (k : nat) (b : lexp) (t : tgt) : option tgt :=
  match t with
  | TR z i d =>
      if Nat.eqb d (S k) then
        if lexp_eqb z b then match i with 0 => None | S i' => Some (TR z i' (S (S k))) end
        else if kd F z b then Some (TR z i (S (S k))) else None
      else Some t
  | TT _ _ => Some t
  end.

Definition oswap (k : nat) (f : form) : option form :=
  match nth_error (fout f) k, nth_error (fout f) (S k) with
  | Some a, Some b =>
      if before F b a then
        match omap (fun '(l, t) => option_map (fun t' => (l, t')) (swap_read k b t)) (fin f) with
        | Some Is => Some (mkF (swap_at k (fout f)) Is)
        | None => None
        end
      else None
  | _, _ => None
  end.

Fixpoint sort_out_go (k fuel : nat) (f : form) : form :=
  match fuel with
  | 0 => f
  | S fuel' =>
      if Nat.ltb (S k) (length (fout f)) then
        match oswap k f with
        | Some f' => sort_out_go (S k) fuel' f'
        | None => sort_out_go (S k) fuel' f
        end
      else f
  end.

(** Dropping output [j] and the input [p] that restores it: reads after
    output [j] are read without it. *)
Definition drop_read (j : nat) (l : lexp) (t : tgt) : option tgt :=
  match t with
  | TR z i d =>
      if Nat.leb d j then Some t
      else if lexp_eqb z l then Some (TR z (S i) (pred d))
      else if kd F z l then Some (TR z i (pred d)) else None
  | TT _ _ => Some t
  end.

Definition absorb_at (j p : nat) (f : form) : option form :=
  match nth_error (fout f) j, nth_error (fin f) p with
  | Some l, Some (l', TR z i d) =>
      if lexp_eqb l l' && lexp_eqb z l && Nat.eqb i 0 && Nat.eqb d j
         && forallb (kd F l) (skipn (S j) (fout f))
         && forallb (fun '(m, _) => kd F l m) (skipn (S p) (fin f)) then
        match omap (fun '(m, t) => option_map (fun t' => (m, t')) (drop_read j l t)) (remove_at p (fin f)) with
        | Some Is => Some (mkF (remove_at j (fout f)) Is)
        | None => None
        end
      else None
  | _, _ => None
  end.

Fixpoint first_some {X Y} (l : list X) (f : X -> option Y) : option Y :=
  match l with [] => None | x :: l' => match f x with Some y => Some y | None => first_some l' f end end.

Definition absorb (f : form) : option form :=
  first_some (seq 0 (length (fin f))) (fun p => first_some (seq 0 (length (fout f))) (fun j => absorb_at j p f)).

Definition normreads (f : form) : form :=
  mkF (fout f) (map (fun '(l, t) => (l, ntgt (fout f) t)) (fin f)).

Fixpoint tidy_go (fuel : nat) (f : form) : form :=
  match fuel with
  | 0 => f
  | S fuel' =>
      let f1 := normreads (mkF (fout f) (sort_in (fin f))) in
      let f2 := normreads (sort_out_go 0 (length (fout f1)) f1) in
      match absorb f2 with
      | Some f3 => tidy_go fuel' f3
      | None => if Nat.eqb (length (fout f2)) (length (fout f)) then f2 else tidy_go fuel' f2
      end
  end.

Definition fsize (f : form) : nat := length (fout f) + length (fin f).

Definition tidy (f : form) : form := tidy_go (S (fsize f * fsize f)) f.

(** *** Moving single outputs and inputs on *)

(** Output [j] of [f], popped first instead: reads above it are read
    after it. *)
Definition top_read (j : nat) (o : lexp) (t : tgt) : option tgt :=
  match t with
  | TR z i d =>
      if Nat.ltb j d then Some (TR z i (pred d))
      else if lexp_eqb z o then match i with 0 => None | S i' => Some (TR z i' d) end
      else if kd F z o then Some t else None
  | TT _ _ => None
  end.

Definition out_first (j : nat) (f : form) : option (lexp * form) :=
  match nth_error (fout f) j with
  | Some o =>
      if forallb (kd F o) (firstn j (fout f)) then
        match omap (fun '(m, t) => option_map (fun t' => (m, t')) (top_read j o t)) (fin f) with
        | Some Is => Some (o, mkF (remove_at j (fout f)) Is)
        | None => None
        end
      else None
  | None => None
  end.

(** Input [p] of [f], pushed before [f] instead. *)
Fixpoint pull (O : list lexp) (d : nat) (z : lexp) (i : nat) : option nat :=
  match O, d with
  | o :: O', S d' =>
      match pull O' d' z i with
      | Some j => if lexp_eqb o z then Some (S j) else if kd F z o then Some j else None
      | None => None
      end
  | _, _ => Some i
  end.

Definition under_read (h : lexp) (t : tgt) : option tgt :=
  match t with
  | TR z i d => if lexp_eqb z h then Some (TR z (S i) d) else if kd F z h then Some t else None
  | TT u p => Some (TT u (PShift h p))
  end.

Definition in_first (p : nat) (f : form) : option (lexp * tgt * form) :=
  match nth_error (fin f) p with
  | Some (h, t) =>
      if forallb (fun '(m, _) => kd F h m) (skipn (S p) (fin f)) && forallb (kd F h) (fout f) then
        let t0 := match t with TR z i d => option_map (fun i' => TR z i' 0) (pull (fout f) d z i) | TT _ _ => Some t end in
        match t0, omap (fun '(m, s) => option_map (fun s' => (m, s')) (under_read h s)) (remove_at p (fin f)) with
        | Some t', Some Is => Some (h, t', mkF (fout f) Is)
        | _, _ => None
        end
      else None
  | None => None
  end.

Definition transfer (f1 f2 : form) : option (form * form) :=
  let try_out j :=
    match out_first j f1 with
    | Some (o, f1') => match compose (weak o) f2 with Some g => Some (f1', g) | None => None end
    | None => None
    end in
  let try_in p :=
    match in_first p f1 with
    | Some (h, t, f1') => match compose (mkF [] [(h, t)]) f2 with Some g => Some (f1', g) | None => None end
    | None => None
    end in
  match first_some (seq 0 (length (fout f1))) try_out with
  | Some r => Some r
  | None => first_some (seq 0 (length (fin f1))) try_in
  end.

Definition fempty (f : form) : bool :=
  match fout f, fin f with [], [] => true | _, _ => false end.

(** [f] after the items [out] (reversed: the head is just before [f]):
    composed with the forms before it while it can be, and otherwise
    taking what can move on its own. *)
Fixpoint addf (fuel : nat) (f : form) (out : list item) : list item :=
  match fuel with
  | 0 => IF f :: out
  | S fuel' =>
      match out with
      | IF f1 :: out' =>
          match compose f1 f with
          | Some g => addf fuel' (tidy g) out'
          | None =>
              match transfer f1 f with
              | Some (f1', g) =>
                  let f1'' := tidy f1' in
                  if fempty f1'' then addf fuel' (tidy g) out' else addf fuel' (tidy g) (IF f1'' :: out')
              | None => IF f :: out
              end
          end
      | _ => if fempty f then out else IF f :: out
      end
  end.

Definition isize (it : item) : nat := match it with IF f => fsize f | IA L _ => length L end.

Definition run (w : fword) : fword :=
  let fuel := S (let n := fold_right (fun it n => isize it + n) (length w) w in n * n) in
  rev (fold_left (fun out it => match it with IF f => addf fuel (tidy f) out | IA _ _ => it :: out end) w []).

End Pass.

(** ** Soundness *)

Section Sound.

Variable F : order.
Variable M : cmodel.
Hypothesis HM : ccons F M.

Local Notation popn := (popn M).
Local Notation tden := (tden M).
Local Notation pushes := (pushes M).
Local Notation fden := (fden M).
Local Notation lden := (lden M).
Local Notation iden := (iden M).
Local Notation wden := (wden M).
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

(** *** Reads *)

Lemma nread_sound O z i d x : tden O (nread F O z i d) x = cname z i (popn O d x).
Proof.
  revert i; induction d as [|d IH]; intros i; [reflexivity|]; cbn [nread].
  destruct (Nat.ltb d (length O)) eqn:L; [|reflexivity]; apply Nat.ltb_lt in L.
  rewrite (popn_S O d x L).
  destruct (lexp_eqb (nth d O LNone) z) eqn:E.
  - apply lexp_eqb_true in E; rewrite E, IH, (cname_pop M); reflexivity.
  - destruct (kd F z (nth d O LNone)) eqn:K; [|cbn [tden]; rewrite (popn_S O d x L); reflexivity].
    rewrite IH, cname_pop_other by (apply kdk, K); reflexivity.
Qed.

Lemma ntgt_sound O t x : tden O (ntgt F O t) x = tden O t x.
Proof. destruct t; [apply nread_sound|reflexivity]. Qed.

Lemma normreads_sound f x : fden (normreads F f) x = fden f x.
Proof.
  unfold fden, normreads; cbn [fout fin]; destruct f as [O I]; cbn [fout fin].
  induction I as [|[h t] I IH]; cbn; [reflexivity|]; rewrite IH, ntgt_sound; reflexivity.
Qed.

Lemma bubble_sound O y I b x : pushes O (bubble F y I) b x = pushes O (y :: I) b x.
Proof.
  revert y; induction I as [|z I IH]; intros y; [reflexivity|]; cbn [bubble].
  destruct (before F (fst z) (fst y)) eqn:B; cbn [pushes]; rewrite IH; destruct y as [a ta], z as [c tc]; cbn [pushes fst] in *; [|reflexivity].
  apply (kd_push_push F M HM); apply bk; exact B.
Qed.

Lemma sort_in_sound O I b x : pushes O (sort_in F I) b x = pushes O I b x.
Proof. destruct I as [|y I]; [reflexivity|apply bubble_sound]. Qed.

(** *** Composing two forms *)

Lemma popin_sound o rem O b x :
  (forall rem', popin F o rem = Some (Some rem') -> cpop o (pushes O rem b x) = pushes O rem' b x)
  /\ (popin F o rem = Some None -> cpop o (pushes O rem b x) = pushes O rem (cpop o b) x).
Proof.
  induction rem as [|[l t] rem IH]; cbn [popin]; [split; [discriminate|reflexivity]|].
  destruct (lexp_eqb l o) eqn:E.
  - apply lexp_eqb_true in E; subst l; split; [intros rem' H; injection H as <-; cbn; apply cpop_push|discriminate].
  - destruct (kd F l o) eqn:K; [|split; discriminate].
    assert (D : known_distinct F o l) by (apply known_distinct_sym, kdk, K).
    destruct IH as [IH1 IH2]; destruct (popin F o rem) as [[rem'|]|]; [| |split; discriminate].
    + split; [|discriminate]; intros r H; injection H as <-; cbn [pushes].
      rewrite (kd_pop_push F M HM o l D), (IH1 rem' eq_refl); reflexivity.
    + split; [discriminate|intros _]; cbn [pushes]; rewrite (kd_pop_push F M HM o l D), IH2 by reflexivity; reflexivity.
Qed.

Lemma rthrough_sound rem z i O b x :
  (forall t, rthrough F rem z i = Some (inl t) -> cname z i (pushes O rem b x) = tden O t x)
  /\ (forall i', rthrough F rem z i = Some (inr i') -> cname z i (pushes O rem b x) = cname z i' b).
Proof.
  revert i; induction rem as [|[l t] rem IH]; intros i; cbn [rthrough pushes].
  - split; [discriminate|intros i' H; injection H as <-; reflexivity].
  - destruct (lexp_eqb l z) eqn:E.
    + apply lexp_eqb_true in E; subst l; destruct i as [|i].
      * split; [intros t' H; injection H as <-; apply (cname_push0 M)|discriminate].
      * rewrite (cname_push M); apply IH.
    + destruct (kd F l z) eqn:K; [|split; discriminate].
      rewrite cname_push_other by (apply known_distinct_sym, kdk, K); apply IH.
Qed.

(** The states of [popall]: after [d] outputs, the inputs left and the
    outputs passed, read in any list of outputs that has the passed ones
    from position [n0] on. *)
Lemma popall_spec O1 : forall rem passed st, popall F O1 rem passed = Some st ->
  length st = S (length O1)
  /\ exists remf Pf, last st ([], []) = (remf, passed ++ Pf)
  /\ forall O x n0, length passed + length Pf + n0 <= length O ->
       (forall k, k < length passed + length Pf -> nth (n0 + k) O LNone = nth k (passed ++ Pf) LNone) ->
       forall d, d <= length O1 -> exists rem_d passed_d, nth_error st d = Some (rem_d, passed_d)
         /\ popn O1 d (pushes O rem (popn O (n0 + length passed) x) x)
            = pushes O rem_d (popn O (n0 + length passed_d) x) x.
Proof.
  induction O1 as [|o O1 IH]; intros rem passed st H; cbn [popall] in H.
  - injection H as <-; split; [reflexivity|]; exists rem, []; rewrite app_nil_r; split; [reflexivity|].
    intros O x n0 _ _ d Hd; cbn in Hd; assert (d = 0) as -> by lia; exists rem, passed; split; [reflexivity|].
    rewrite popn_0; reflexivity.
  - destruct (popin F o rem) as [[rem'|]|] eqn:P; [| |discriminate].
    + destruct (popall F O1 rem' passed) as [st'|] eqn:E; [|discriminate]; injection H as <-.
      destruct (IH _ _ _ E) as [L [remf [Pf [Last S]]]]; split; [cbn; rewrite L; reflexivity|].
      exists remf, Pf; split.
      { destruct st' as [|q st']; [discriminate|]; exact Last. }
      intros O x n0 HO HP [|d] Hd.
      * exists rem, passed; split; [reflexivity|]; rewrite popn_0; reflexivity.
      * cbn [length] in Hd; destruct (S O x n0 HO HP d ltac:(lia)) as [rd [pd [N Q]]].
        exists rd, pd; split; [exact N|]; cbn [popn].
        rewrite (proj1 (popin_sound o rem O _ x) rem' P); exact Q.
    + destruct (popall F O1 rem (passed ++ [o])) as [st'|] eqn:E; [|discriminate]; injection H as <-.
      destruct (IH _ _ _ E) as [L [remf [Pf [Last S]]]]; split; [cbn; rewrite L; reflexivity|].
      exists remf, (o :: Pf); split.
      { destruct st' as [|q st']; [discriminate|].
        transitivity (last (q :: st') ([], [])); [reflexivity|]; rewrite Last, <- app_assoc; reflexivity. }
      intros O x n0 HO HP [|d] Hd.
      * exists rem, passed; split; [reflexivity|]; rewrite popn_0; reflexivity.
      * cbn [length] in Hd, HO.
        assert (HO' : length (passed ++ [o]) + length Pf + n0 <= length O) by (rewrite length_app; cbn; lia).
        assert (HP' : forall k, k < length (passed ++ [o]) + length Pf -> nth (n0 + k) O LNone = nth k ((passed ++ [o]) ++ Pf) LNone).
        { intros k Hk; rewrite <- app_assoc; apply HP; rewrite length_app in Hk; cbn in *; lia. }
        destruct (S O x n0 HO' HP' d ltac:(lia)) as [rd [pd [N Q]]].
        exists rd, pd; split; [exact N|]; cbn [popn].
        rewrite (proj2 (popin_sound o rem O _ x) P), <- Q, length_app; cbn [length].
        f_equal; f_equal; rewrite Nat.add_1_r, <- plus_n_Sm, popn_S by lia.
        f_equal; specialize (HP (length passed) ltac:(cbn [length]; lia)); rewrite HP, app_nth2 by lia.
        rewrite Nat.sub_diag; reflexivity.
Qed.

Lemma clamp_sound O2 P t x : tden (O2 ++ P) (clamp (length O2) t) x = tden O2 t x.
Proof.
  destruct t as [z i d|u p]; [|reflexivity]; cbn.
  rewrite popn_app_le by lia; rewrite popn_min; reflexivity.
Qed.

Lemma pushes_clamp O2 P I b x :
  pushes (O2 ++ P) (map (fun '(l, t) => (l, clamp (length O2) t)) I) b x = pushes O2 I b x.
Proof. induction I as [|[l t] I IH]; cbn; [reflexivity|rewrite IH, clamp_sound; reflexivity]. Qed.

Theorem compose_sound f1 f2 g x : compose F f1 f2 = Some g -> fden g x = fden f1 (fden f2 x).
Proof.
  unfold compose; destruct f1 as [O1 I1], f2 as [O2 I2]; cbn [fout fin].
  set (I2c := map (fun '(l, t) => (l, clamp (length O2) t)) I2).
  destruct (popall F O1 I2c []) as [st|] eqn:P; [|discriminate].
  destruct (popall_spec O1 I2c [] st P) as [L [remf [Pf [Last S]]]].
  rewrite Last; cbn [app].
  destruct (omap _ I1) as [I1'|] eqn:Om; [|discriminate]; intros H; injection H as <-.
  set (O := O2 ++ Pf).
  assert (HO : length (@nil lexp) + length Pf + length O2 <= length O) by (unfold O; rewrite length_app; cbn; lia).
  assert (HP : forall k, k < length (@nil lexp) + length Pf -> nth (length O2 + k) O LNone = nth k ([] ++ Pf) LNone).
  { intros k _; unfold O; rewrite app_nth2 by lia; f_equal; lia. }
  specialize (S O x (length O2) HO HP).
  assert (Y : fden (mkF O2 I2) x = pushes O I2c (popn O (length O2 + length (@nil lexp)) x) x).
  { unfold fden, I2c, O; cbn [fout fin]; rewrite pushes_clamp, Nat.add_0_r, popn_app_le by lia; reflexivity. }
  rewrite Y; unfold fden at 1; cbn [fout fin].
  destruct (S (length O1) (le_n _)) as [rf [pf [N Q]]].
  rewrite (nth_error_last_len st (length O1) ([], []) L), Last in N; injection N as <- <-.
  unfold fden; cbn [fout fin]; rewrite Q, pushes_app.
  replace (length O2 + length Pf) with (length O) by (unfold O; rewrite length_app; reflexivity).
  apply (omap_pushes _ O1 O I1 I1' _ _ _ Om).
  intros h t h' t' G; destruct (newt F (length O2) (fexp (mkF O2 I2)) st t) as [t''|] eqn:Nt; cbn in G; [|discriminate].
  injection G as <- <-; split; [reflexivity|].
  destruct t as [z i d|u p]; cbn [newt] in Nt.
  - destruct (nth_error st d) as [[rd pd]|] eqn:Nd; [|discriminate].
    assert (Hd : d <= length O1) by (assert (nth_error st d <> None) as Hn by congruence; apply nth_error_Some in Hn; lia).
    destruct (S d Hd) as [rd' [pd' [Nd' Qd]]]; rewrite Nd in Nd'; injection Nd' as <- <-.
    cbn [tden]; rewrite Qd.
    destruct (rthrough_sound rd z i O (popn O (length O2 + length pd) x) x) as [R1 R2].
    destruct (rthrough F rd z i) as [[t'|i']|]; [| |discriminate]; injection Nt as <-.
    + symmetry; apply R1; reflexivity.
    + cbn [tden]; symmetry; apply R2; reflexivity.
  - injection Nt as <-; cbn [tden cp fpb]; rewrite fexp_sound, Y; reflexivity.
Qed.

(** *** Sorting the outputs *)

Lemma oswap_sound k f f' x : oswap F k f = Some f' -> fden f' x = fden f x.
Proof.
  unfold oswap; destruct f as [O I]; cbn [fout fin].
  destruct (nth_error O k) as [a|] eqn:Ea; [|discriminate].
  destruct (nth_error O (S k)) as [b|] eqn:Eb; [|discriminate].
  destruct (before F b a) eqn:Bf; [|discriminate].
  destruct (omap _ I) as [Is|] eqn:Om; [|discriminate]; intros H; injection H as <-.
  destruct (split_at O k a Ea) as [A [R [-> LA]]]; subst k.
  rewrite nth_error_app2 in Eb by lia; rewrite Nat.sub_succ_l, Nat.sub_diag in Eb by lia.
  destruct R as [|b' B]; [discriminate|]; cbn in Eb; injection Eb as ->.
  assert (D : known_distinct F a b) by (apply known_distinct_sym, bk, Bf).
  unfold fden; cbn [fout fin]; rewrite swap_at_app.
  assert (Lens : length (A ++ b :: a :: B) = length A + S (S (length B))) by (rewrite length_app; reflexivity).
  assert (Lens' : length (A ++ a :: b :: B) = length A + S (S (length B))) by (rewrite length_app; reflexivity).
  rewrite Lens, Lens', !popn_mid, (pop_comm b a) by (apply known_distinct_sym; exact D).
  apply (omap_pushes _ _ _ I Is _ _ _ Om).
  intros h t h' t' G; destruct (swap_read F (length A) b t) as [t''|] eqn:Sw; cbn in G; [|discriminate].
  injection G as <- <-; split; [reflexivity|].
  destruct t as [z i d|u p]; cbn [swap_read] in Sw; [|injection Sw as <-; reflexivity].
  destruct (Nat.eqb d (S (length A))) eqn:Ed.
  - apply Nat.eqb_eq in Ed; subst d.
    assert (P1 : popn (A ++ a :: b :: B) (S (length A)) x = cpop a (popn A (length A) x)).
    { replace (S (length A)) with (length A + S 0) by lia; rewrite popn_at, popn_0; reflexivity. }
    assert (P2 : popn (A ++ b :: a :: B) (S (S (length A))) x = cpop a (cpop b (popn A (length A) x))).
    { replace (S (S (length A))) with (length A + S (S 0)) by lia; rewrite popn_mid, popn_0; reflexivity. }
    destruct (lexp_eqb z b) eqn:Ez.
    + apply lexp_eqb_true in Ez; subst z; destruct i as [|i]; [discriminate|]; injection Sw as <-; cbn [tden].
      rewrite P1, P2, (pop_comm a b _ D), (cname_pop M); reflexivity.
    + destruct (kd F z b) eqn:K; [|discriminate]; injection Sw as <-; cbn [tden].
      rewrite P1, P2, (pop_comm a b _ D), cname_pop_other by (apply kdk, K); reflexivity.
  - injection Sw as <-; cbn [tden]; apply Nat.eqb_neq in Ed.
    destruct (Nat.le_gt_cases d (length A)) as [Le|Gt].
    + rewrite !popn_len_le by exact Le; reflexivity.
    + replace d with (length A + S (S (d - length A - 2))) by lia.
      rewrite !popn_mid, (pop_comm a b _ D); reflexivity.
Qed.

Lemma sort_out_go_sound k fuel f x : fden (sort_out_go F k fuel f) x = fden f x.
Proof.
  revert k f; induction fuel as [|fuel IH]; intros k f; [reflexivity|]; cbn [sort_out_go].
  destruct (Nat.ltb (S k) (length (fout f))); [|reflexivity].
  destruct (oswap F k f) as [f'|] eqn:E; rewrite IH; [apply (oswap_sound k)|]; easy.
Qed.

(** *** Absorbing an input that restores an output *)

Lemma absorb_at_sound j p f f' x : absorb_at F j p f = Some f' -> fden f' x = fden f x.
Proof.
  unfold absorb_at; destruct f as [O I]; cbn [fout fin].
  destruct (nth_error O j) as [l|] eqn:Ej; [|discriminate].
  destruct (nth_error I p) as [[l' [z i d|u q]]|] eqn:Ep; try discriminate.
  destruct (lexp_eqb l l' && lexp_eqb z l && Nat.eqb i 0 && Nat.eqb d j
            && forallb (kd F l) (skipn (S j) O) && forallb (fun '(m, _) => kd F l m) (skipn (S p) I)) eqn:C; [|discriminate].
  destruct (omap _ (remove_at p I)) as [Is|] eqn:Om; [|discriminate]; intros H; injection H as <-.
  rewrite !andb_true_iff in C; destruct C as [[[[[C1 C2] C3] C4] C5] C6].
  apply lexp_eqb_true in C1, C2; apply Nat.eqb_eq in C3, C4; subst l' z i d.
  destruct (split_at O j l Ej) as [A [B [-> LA]]]; subst j.
  destruct (split_at I p _ Ep) as [P [Q [-> LP]]]; subst p.
  rewrite skipn_app_at in C5; rewrite skipn_app_at in C6; apply forallb_kd in C5; apply forallb_kd_in in C6.
  rewrite (remove_at_app P Q) in Om; rewrite (remove_at_app A B).
  set (Pa := popn A (length A) x).
  assert (Base : popn (A ++ l :: B) (length (A ++ l :: B)) x = cpop l (popn (A ++ B) (length (A ++ B)) x)).
  { rewrite !length_app; cbn [length]; rewrite popn_at, !popn_app_add, popn_pop_comm by exact C5; reflexivity. }
  unfold fden; cbn [fout fin]; rewrite Base, pushes_app; cbn [pushes]; rewrite pushes_pop_comm by exact C6.
  cbn [tden]; rewrite (popn_len_le A (l :: B) (length A) x) by lia.
  fold Pa; rewrite (cname0 M), <- (popn_hd l B (length B) Pa C5).
  assert (Z : popn B (length B) Pa = popn (A ++ B) (length (A ++ B)) x) by (rewrite length_app, popn_app_add; reflexivity).
  rewrite Z, <- (pushes_hd l (A ++ l :: B) Q _ x C6), cpush_pop, <- pushes_app.
  apply (omap_pushes _ _ _ (P ++ Q) Is _ _ _ Om).
  intros h t h' t' G; destruct (drop_read F (length A) l t) as [t''|] eqn:Dr; cbn in G; [|discriminate].
  injection G as <- <-; split; [reflexivity|].
  destruct t as [z i d|u q']; cbn [drop_read] in Dr; [|injection Dr as <-; reflexivity].
  destruct (Nat.leb d (length A)) eqn:Le.
  - apply Nat.leb_le in Le; injection Dr as <-; cbn [tden]; rewrite !popn_len_le by lia; reflexivity.
  - apply Nat.leb_gt in Le.
    assert (Pd : popn (A ++ l :: B) d x = cpop l (popn (A ++ B) (pred d) x)).
    { replace d with (length A + S (d - length A - 1)) by lia; rewrite popn_at.
      replace (pred (length A + S (d - length A - 1))) with (length A + (d - length A - 1)) by lia.
      rewrite popn_app_add, popn_pop_comm by exact C5; reflexivity. }
    destruct (lexp_eqb z l) eqn:Ez.
    + apply lexp_eqb_true in Ez; subst z; injection Dr as <-; cbn [tden]; rewrite Pd, (cname_pop M); reflexivity.
    + destruct (kd F z l) eqn:K; [|discriminate]; injection Dr as <-; cbn [tden].
      rewrite Pd, cname_pop_other by (apply kdk, K); reflexivity.
Qed.

Lemma first_some_spec {X Y} (l : list X) (g : X -> option Y) y : first_some l g = Some y -> exists a, g a = Some y.
Proof.
  induction l as [|a l IH]; cbn; [discriminate|]; destruct (g a) eqn:E; [intros H; injection H as <-; exists a; exact E|exact IH].
Qed.

Lemma absorb_sound f f' x : absorb F f = Some f' -> fden f' x = fden f x.
Proof.
  unfold absorb; intros H; apply first_some_spec in H as [p H]; apply first_some_spec in H as [j H].
  apply (absorb_at_sound j p), H.
Qed.

Lemma tidy_go_sound fuel f x : fden (tidy_go F fuel f) x = fden f x.
Proof.
  revert f; induction fuel as [|fuel IH]; intros f; [reflexivity|]; cbn [tidy_go].
  set (f1 := normreads F (mkF (fout f) (sort_in F (fin f)))).
  assert (E1 : fden f1 x = fden f x).
  { unfold f1; rewrite normreads_sound; unfold fden; cbn [fout fin]; apply sort_in_sound. }
  set (f2 := normreads F (sort_out_go F 0 (length (fout f1)) f1)).
  assert (E2 : fden f2 x = fden f x) by (unfold f2; rewrite normreads_sound, sort_out_go_sound; exact E1).
  destruct (absorb F f2) as [f3|] eqn:A.
  - rewrite IH, (absorb_sound f2 f3 x A); exact E2.
  - destruct (Nat.eqb (length (fout f2)) (length (fout f))); [exact E2|rewrite IH; exact E2].
Qed.

Lemma tidy_sound f x : fden (tidy F f) x = fden f x.
Proof. apply tidy_go_sound. Qed.

(** *** Moving an output or an input into the next form *)

Lemma out_first_sound j f o f' y : out_first F j f = Some (o, f') -> fden f y = fden f' (cpop o y).
Proof.
  unfold out_first; destruct f as [O I]; cbn [fout fin].
  destruct (nth_error O j) as [o'|] eqn:Ej; [|discriminate].
  destruct (forallb (kd F o') (firstn j O)) eqn:C; [|discriminate].
  destruct (omap _ I) as [Is|] eqn:Om; [|discriminate]; intros H; injection H as <- <-.
  destruct (split_at O j o' Ej) as [A [B [-> LA]]]; subst j.
  rewrite firstn_app_at in C; apply forallb_kd in C; rewrite (remove_at_app A B).
  unfold fden; cbn [fout fin].
  assert (Base : popn (A ++ B) (length (A ++ B)) (cpop o' y) = popn (A ++ o' :: B) (length (A ++ o' :: B)) y).
  { rewrite !length_app; cbn [length]; rewrite popn_at, popn_app_add, popn_pop_comm by exact C; reflexivity. }
  rewrite Base; symmetry; apply (omap_pushes _ _ _ I Is _ _ _ Om).
  intros h t h' t' G; destruct (top_read F (length A) o' t) as [t''|] eqn:Tr; cbn in G; [|discriminate].
  injection G as <- <-; split; [reflexivity|].
  destruct t as [z i d|u q]; cbn [top_read] in Tr; [|discriminate].
  destruct (Nat.ltb (length A) d) eqn:Lt.
  - apply Nat.ltb_lt in Lt; injection Tr as <-; cbn [tden].
    replace d with (length A + S (d - length A - 1)) by lia; rewrite popn_at.
    replace (pred (length A + S (d - length A - 1))) with (length A + (d - length A - 1)) by lia.
    rewrite popn_app_add, popn_pop_comm by exact C; reflexivity.
  - apply Nat.ltb_ge in Lt.
    assert (Pd : popn (A ++ B) d (cpop o' y) = cpop o' (popn (A ++ o' :: B) d y)).
    { rewrite !popn_len_le by lia; apply popn_pop_comm, C. }
    destruct (lexp_eqb z o') eqn:Ez.
    + apply lexp_eqb_true in Ez; subst z; destruct i as [|i]; [discriminate|]; injection Tr as <-; cbn [tden].
      rewrite Pd, (cname_pop M); reflexivity.
    + destruct (kd F z o') eqn:K; [|discriminate]; injection Tr as <-; cbn [tden].
      rewrite Pd, cname_pop_other by (apply kdk, K); reflexivity.
Qed.

Lemma pull_sound O d z i i' y : pull F O d z i = Some i' -> cname z i (popn O d y) = cname z i' y.
Proof.
  revert d y i'; induction O as [|o O IH]; intros [|d] y i' H; cbn [pull] in H;
    try (injection H as <-; reflexivity).
  destruct (pull F O d z i) as [j|] eqn:P; [|discriminate]; cbn [popn]; rewrite (IH d (cpop o y) j P).
  destruct (lexp_eqb o z) eqn:E.
  - apply lexp_eqb_true in E; subst o; injection H as <-; apply (cname_pop M).
  - destruct (kd F z o) eqn:K; [|discriminate]; injection H as <-; apply cname_pop_other, kdk, K.
Qed.

Lemma in_first_sound p f h t' f' y : in_first F p f = Some (h, t', f') ->
  fden f y = fden f' (cpush h y (tden [] t' y)).
Proof.
  unfold in_first; destruct f as [O I]; cbn [fout fin].
  destruct (nth_error I p) as [[h0 t]|] eqn:Ep; [|discriminate].
  destruct (forallb (fun '(m, _) => kd F h0 m) (skipn (S p) I) && forallb (kd F h0) O) eqn:C; [|discriminate].
  apply andb_true_iff in C as [C1 C2]; apply forallb_kd in C2.
  set (t0 := match t with TR z i d => option_map (fun i' => TR z i' 0) (pull F O d z i) | TT _ _ => Some t end).
  destruct t0 as [t''|] eqn:T0; [|discriminate].
  destruct (omap _ (remove_at p I)) as [Is|] eqn:Om; [|discriminate]; intros H; injection H as <- <- <-.
  destruct (split_at I p _ Ep) as [P [Q [-> LP]]]; subst p.
  rewrite skipn_app_at in C1; apply forallb_kd_in in C1; rewrite (remove_at_app P Q) in Om.
  assert (V : tden O t y = tden [] t'' y).
  { unfold t0 in T0; destruct t as [z i d|u q].
    - destruct (pull F O d z i) as [i'|] eqn:Pl; [|discriminate]; injection T0 as <-; cbn [tden].
      rewrite popn_0; apply pull_sound, Pl.
    - injection T0 as <-; reflexivity. }
  set (y' := cpush h0 y (tden [] t'' y)).
  unfold fden; cbn [fout fin]; rewrite pushes_app; cbn [pushes].
  rewrite V, pushes_push_comm by exact C1; rewrite <- popn_push_comm by exact C2; fold y'.
  rewrite <- pushes_app; symmetry; apply (omap_pushes _ _ _ (P ++ Q) Is _ _ _ Om).
  intros m s m' s' G; destruct (under_read F h0 s) as [s''|] eqn:U; cbn in G; [|discriminate].
  injection G as <- <-; split; [reflexivity|].
  destruct s as [z i d|u q]; cbn [under_read] in U.
  - assert (Pd : popn O d y' = cpush h0 (popn O d y) (tden [] t'' y)) by (apply popn_push_comm, C2).
    destruct (lexp_eqb z h0) eqn:Ez.
    + apply lexp_eqb_true in Ez; subst z; injection U as <-; cbn [tden]; rewrite Pd, (cname_push M); reflexivity.
    + destruct (kd F z h0) eqn:K; [|discriminate]; injection U as <-; cbn [tden].
      rewrite Pd, cname_push_other by (apply kdk, K); reflexivity.
  - injection U as <-; cbn [tden cp fpb]; unfold y'; rewrite cpop_push; reflexivity.
Qed.

Lemma transfer_sound f1 f2 f1' g x : transfer F f1 f2 = Some (f1', g) -> fden f1' (fden g x) = fden f1 (fden f2 x).
Proof.
  unfold transfer.
  destruct (first_some (seq 0 (length (fout f1))) _) as [r|] eqn:E1.
  - intros H; injection H as ->; apply first_some_spec in E1 as [j E1].
    destruct (out_first F j f1) as [[o f1'']|] eqn:Of; [|discriminate].
    destruct (compose F (weak o) f2) as [g'|] eqn:Cp; [|discriminate]; injection E1 as <- <-.
    rewrite (compose_sound _ _ _ x Cp), (out_first_sound j f1 o f1'' _ Of); reflexivity.
  - intros H; apply first_some_spec in H as [p H].
    destruct (in_first F p f1) as [[[h t] f1'']|] eqn:If; [|discriminate].
    destruct (compose F (mkF [] [(h, t)]) f2) as [g'|] eqn:Cp; [|discriminate]; injection H as <- <-.
    rewrite (compose_sound _ _ _ x Cp), (in_first_sound p f1 h t f1'' _ If); reflexivity.
Qed.

(** *** The pass *)

Lemma fempty_sound f x : fempty f = true -> fden f x = x.
Proof. unfold fempty, fden; destruct f as [[|o O] [|[h t] I]]; cbn; easy. Qed.

Lemma addf_sound fuel f out x : wden (rev (addf F fuel f out)) x = wden (rev out) (fden f x).
Proof.
  revert f out x; induction fuel as [|fuel IH]; intros f out x; cbn [addf].
  - apply wden_rev_cons.
  - destruct out as [|[f1|L n] out'].
    + destruct (fempty f) eqn:E; [rewrite fempty_sound by exact E; reflexivity|apply wden_rev_cons].
    + destruct (compose F f1 f) as [g|] eqn:Cp.
      * rewrite IH, tidy_sound, (compose_sound _ _ _ x Cp), wden_rev_cons; reflexivity.
      * destruct (transfer F f1 f) as [[f1' g]|] eqn:Tr; [|apply wden_rev_cons].
        destruct (fempty (tidy F f1')) eqn:E.
        -- rewrite IH, tidy_sound, wden_rev_cons; cbn [iden].
           rewrite <- (transfer_sound f1 f f1' g x Tr), <- (tidy_sound f1'), (fempty_sound (tidy F f1') _ E); reflexivity.
        -- rewrite IH, tidy_sound, !wden_rev_cons; cbn [iden].
           rewrite tidy_sound, (transfer_sound f1 f f1' g x Tr); reflexivity.
    + destruct (fempty f) eqn:E; [rewrite fempty_sound by exact E; reflexivity|apply wden_rev_cons].
Qed.

Lemma run_go_sound fuel w out x :
  wden (rev (fold_left (fun out it => match it with IF f => addf F fuel (tidy F f) out | IA _ _ => it :: out end) w out)) x
  = wden (rev out) (wden w x).
Proof.
  revert out x; induction w as [|it w IH]; intros out x; [reflexivity|]; cbn [fold_left wden].
  rewrite IH; destruct it as [f|L n].
  - rewrite addf_sound, tidy_sound; reflexivity.
  - rewrite wden_rev_cons; reflexivity.
Qed.

Theorem run_sound w x : wden (run F w) x = wden w x.
Proof. unfold run; rewrite run_go_sound; reflexivity. Qed.

End Sound.

(** ** The normaliser: the pass, then [CNorm] *)

Definition cf_form (F : order) (e : aexp) : aexp := wexp (run F (of_exp e)).

Theorem cf_form_sound F e : forall M, ccons F M -> forall x : cU M, ca (cf_form F e) x = ca e x.
Proof. intros M HM x; unfold cf_form; rewrite wexp_sound, (run_sound F M HM), of_exp_sound; reflexivity. Qed.

Definition cf_eq (F : order) (e1 e2 : aexp) : bool := cn_eq F (cf_form F e1) (cf_form F e2).

Theorem cf_eq_correct F
  (Hirr : forall a, lt_known F a a = false)
  (Htrans : forall a b c, lt_known F a b = true -> lt_known F b c = true -> lt_known F a c = true)
  e1 e2 : cf_eq F e1 e2 = true <-> cequal F e1 e2.
Proof.
  unfold cf_eq; rewrite (CComplete.cn_eq_correct F Hirr Htrans); split; intros H M HM x.
  - rewrite <- (cf_form_sound F e1 M HM x), <- (cf_form_sound F e2 M HM x); apply H, HM.
  - rewrite (cf_form_sound F e1 M HM x), (cf_form_sound F e2 M HM x); apply H, HM.
Qed.

(** ** Examples

    Facts [g < h], [k < h], [m < h].  [W1]/[W2]: the copies [h ↦ ·₀] and
    [g ↦ m₀] in either order, then [⟦ \ k as _ ⟧]; both give the one form
    [⟦ g ↦ m₀ read below k; h ↦ ·₀ \ k as _ ⟧].  [Y1]/[Y2]: [g] copies
    [g₀] or [h₀], where the entry on [h] after it copies [g₀].  [V1]/[V2]:
    the lift law, [⟦ \ g as _ ⟧ ⨾ ⟦ k | ⟦ \ h as _ ⟧ ⟧] against
    [⟦ \ g as _ ⟧ ⨾ ⟦ \ h as _ ⟧]. *)
Module Examples.
Definition g := LAtom 0. Definition h := LAtom 1. Definition k := LAtom 2. Definition m := LAtom 3.
Definition F := order_of [(g, h); (k, h); (m, h)].
Definition E (a b : lexp) (i : nat) : aexp := AInner a (TVarE b i) AId.
Definition W (a : lexp) : aexp := AOuter a AId.
Definition seq2 (a b : aexp) : aexp := ACompose b a.
Definition seq3 (a b c : aexp) : aexp := ACompose (ACompose c b) a.
Definition W1 := seq3 (E h LNone 0) (E g m 0) (W k).
Definition W2 := seq3 (E g m 0) (E h LNone 0) (W k).
Definition Y1 := seq3 (E g g 0) (E h g 0) (W k).
Definition Y2 := seq3 (E g h 0) (E h g 0) (W k).
Definition V1 := seq2 (W g) (ALift k (W h)).
Definition V2 := seq2 (W g) (W h).
Lemma W12 : run F (of_exp W1) = [IF (mkF [k] [(g, TR m 0 1); (h, TR LNone 0 0)])] /\ run F (of_exp W2) = run F (of_exp W1).
Proof. split; vm_compute; reflexivity. Qed.
Lemma Y12 : run F (of_exp Y1) = run F (of_exp Y2). Proof. vm_compute; reflexivity. Qed.
Lemma V12 : run F (of_exp V1) = run F (of_exp V2). Proof. vm_compute; reflexivity. Qed.
End Examples.
