(** * Layered words, computed directly (in progress)

    A layered word is a list of segments, applied in order.  A term in a
    segment has the rest of the word as its payload: [NBind u (WEnd SNil)
    b] in a segment is [u] with [b] and then every later segment.  So
    the terms of one segment (a layer) all have the same payload, and
    nothing is written twice.

    The normaliser folds over the expression from its last step, putting
    one step at a time in front of the word built so far ([fold]); a lift
    is a close before and an open after, with the steps between folded
    one level deeper under the bound label.

    A term whose payload goes on with further steps is put in front of
    those steps, and everything else is sent around them: an entry is
    undone by a weakening before it, and the variable an output entry
    creates is carried past it as a bound variable ([bypass_step]).

    So far: the meaning of a layered word and soundness of the fold
    ([lnorm_sound]).  Not covered yet: an atom or a lift by the bound
    label inside a payload, and shifted targets. *)

From Stdlib Require Import Arith List Lia Bool.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Unique Normal.
Import ListNotations.

Inductive lstep : Type :=
| LS (s : seg)
| LA (L : list (lexp * nat)) (a : nat).

Definition lword : Type := list lstep.

Section Layered.

Variable F : order.
Variable ntm : nat.

Definition is_term (t : ntgt) : bool := match t with NBind _ _ _ => true | NVar _ _ => false end.

Definition has_terms (s : seg) : bool := existsb is_term (stargets s).

(** Every term of the segment has the identity under its payload. *)
Definition no_atoms (s : seg) : bool :=
  forallb (fun t => match t with NBind _ _ (Some _) => false | _ => true end) (stargets s).

(** A segment that does nothing to named variables: only the bound
    label has an entry. *)
Fixpoint bound_only (s : seg) : bool :=
  match s with
  | SNil => true
  | SEnt LNone _ _ r => bound_only r
  | SEnt _ _ _ _ => false
  end.

(** [d] lifts by the bound label, in one pass: the outputs of the bound
    label move up by [d], and its first [d] inputs go to themselves. *)
Fixpoint idts (i n : nat) : tlist :=
  match n with 0 => TNil | S n' => TCons (NVar LNone i) (idts (S i) n') end.

Definition slifts (d : nat) (s : seg) : option seg :=
  match d with
  | 0 => Some s
  | _ =>
      match scomp F ntm (shseg LNone d) s with
      | Some s1 =>
          match sfind F LNone s1 with
          | Some e => let '(ts, m) := ofe e in sset F LNone (tcat (idts 0 d) ts) m s1
          | None => None
          end
      | None => None
      end
  end.

(** ** Putting a segment in front of a word

    A segment without terms joins the first segment.  One with terms is
    a new layer, unless the first segment does nothing to named
    variables and the terms have no payload atom: then they have the
    same payload as the terms of the first segment, and are in its
    layer.  Joining is composition of segments. *)
Definition obind {A B} (x : option A) (f : A -> option B) : option B :=
  match x with Some a => f a | None => None end.

Definition lpre (U : seg) : lword := match U with SNil => [] | _ => [LS U] end.

(** In front of an atom, a segment with terms stays where it is.  A
    renaming is settled as in [Normalise]: what it does to the variables
    passed around the atom moves after the atom, and what is left before
    it is in lift position. *)
Fixpoint cons_seg (s : seg) (K : lword) {struct K} : option lword :=
  match K with
  | LS s1 :: K' =>
      if negb (has_terms s) || (bound_only s1 && no_atoms s)
      then match scomp F ntm s1 s with
           | Some SNil => Some K'
           | Some s' => Some (LS s' :: K')
           | None => None
           end
      else Some (LS s :: K)
  | LA L a :: K' =>
      if has_terms s then Some (LS s :: K)
      else match wcomp F ntm (WAtom SNil L a (WEnd SNil)) (WEnd s) with
           | Some (WAtom s' L' a' (WEnd U)) =>
               obind (cons_seg s' K') (fun K'' => Some (lpre U ++ LA L' a' :: K''))
           | _ => None
           end
  | [] => Some (lpre s)
  end.

(** ** The steps *)

Definition entry (h : lexp) (t : ntgt) : option seg := sfront F h t SNil.

(** [⟦ h \ · ⟧] and [⟦ · \ h ⟧]. *)
Definition close_seg (h : lexp) : option seg := sfront F h (NVar LNone 0) (shseg LNone 1).
Definition open_seg (h : lexp) : option seg := sfront F LNone (NVar h 0) (shseg h 1).

Definition is_bound (h : lexp) : bool := match h with LNone => true | _ => false end.

Definition cons_lifted (d : nat) (s : option seg) (K : lword) : option lword :=
  obind s (fun s0 => obind (slifts d s0) (fun s' => cons_seg s' K)).

(** Lifts by the labels of [G], the first innermost. *)
Fixpoint glifts (G : list lexp) (s : seg) : option seg :=
  match G with
  | [] => Some s
  | g :: G' => obind (slift F ntm g s) (glifts G')
  end.

(** [k] under the lifts of [G]: each is a close before and an open
    after, one level deeper. *)
Fixpoint under (G : list lexp) (d : nat) (k : nat -> lword -> option lword) (K : lword) : option lword :=
  match G with
  | [] => k d K
  | g :: G' =>
      under G' d (fun d' K' => obind (cons_lifted d' (open_seg g) K')
                                 (fun K1 => obind (k (S d') K1) (cons_lifted d' (close_seg g)))) K
  end.

(** A term whose payload goes on with an output entry of [g] under the
    lifts [G]: everything else goes around that entry.  For a named [g]
    its variable [g₍₀₎] is closed before and sent back to [g₍₀₎] after;
    for the bound label there is nothing to close.  [w] counts the bound
    variables of the steps already gone around; [next] puts the term
    with the rest of its payload. *)
Definition bouter (d w : nat) (h : lexp) (G : list lexp) (g : lexp)
    (next : nat -> lword -> option lword) (K : lword) : option lword :=
  obind (cons_lifted (d + w) (obind (entry LNone (NVar g 0)) (glifts G)) K) (fun K1 =>
  obind (cons_lifted (d + w + 1) (glifts G (shseg g 1)) K1) (fun K2 =>
  obind (next (w + 1) K2) (fun K3 =>
  if is_bound g then Some K3
  else cons_lifted d (obind (obind (obind (close_seg g) (glifts G)) (slifts w)) (slift F ntm h)) K3))).

(** ** Multiplying out

    The word of the normal form of [Normalise]: every step composed into
    the next, so that each term carries its whole payload. *)
Fixpoint expand (l : lword) : option word :=
  match l with
  | [] => Some (WEnd SNil)
  | LS s :: r => obind (expand r) (fun w => wcomp F ntm w (WEnd s))
  | LA L a :: r => obind (expand r) (fun w => wcomp F ntm w (WAtom SNil L a (WEnd SNil)))
  end.

(** Payloads the term keeps as a tree: those with an atom, or a lift by
    the bound label.  The atom acts on the names of the term alone, which
    no step of the word can do. *)
Fixpoint ahard (a : aexp) : bool :=
  match a with
  | AId => false
  | AAtom _ => true
  | ACompose a b => ahard a || ahard b
  | AOuter _ a => ahard a
  | AInner g _ a => is_bound g || ahard a
  | ALift g a => is_bound g || ahard a
  end.

Fixpoint phard (p : pexp) : bool :=
  match p with
  | PId | PAtom _ => false
  | PComp a p => ahard a || phard p
  | PShift _ p => phard p
  end.

(** The variable that a target without terms stands for. *)
Fixpoint tvar (t : texp) : option (lexp * nat) :=
  match t with
  | TVarE g i => Some (g, i)
  | TBindE _ _ => None
  | TShiftE h t' =>
      match tvar t' with
      | Some (g, i) =>
          match lcmp F h g with
          | Some Eq => Some (g, S i)
          | Some _ => Some (g, i)
          | None => None
          end
      | None => None
      end
  end.

(** [fold d e K]: [e] under [d] lifts by the bound label, then [K].
    [centry d G h t K]: the entry of [h] with target [t], under the
    lifts [G] and [d] lifts by the bound label, then [K].
    [cterm d w h u p K]: the entry of [h] with the term [u], whose
    payload is [p] and then [w] weakenings of the bound label.
    [byp d w h G a inner K]: [inner] puts a term; here its payload goes
    on with [a] under the lifts [G]. *)
Fixpoint fold (d : nat) (e : aexp) (K : lword) {struct e} : option lword :=
  match e with
  | AId => Some K
  | AAtom n => Some (LA (match d with 0 => [] | _ => [(LNone, d)] end) n :: K)
  | ACompose a b => obind (fold d a K) (fold d b)
  | AOuter h a => obind (cons_lifted d (Some (shseg h 1)) K) (fold d a)
  | AInner h t a =>
      obind (centry d [] h t K) (fun K1 =>
      if is_bound h then fold (S d) a K1
      else obind (cons_lifted d (open_seg h) K1) (fun K2 =>
           obind (fold (S d) a K2) (cons_lifted d (close_seg h))))
  | ALift h a =>
      if is_bound h then fold (S d) a K
      else obind (cons_lifted d (open_seg h) K) (fun K2 =>
           obind (fold (S d) a K2) (cons_lifted d (close_seg h)))
  end
with centry (d : nat) (G : list lexp) (h : lexp) (t : texp) (K : lword) {struct t} : option lword :=
  match t with
  | TVarE g i => cons_lifted d (obind (entry h (NVar g i)) (glifts G)) K
  | TBindE u p =>
      if u <? ntm then
        if phard p then
          match ptree p with
          | Some (w, b) => cons_lifted d (obind (entry h (NBind u w b)) (glifts G)) K
          | None => None
          end
        else under G d (fun d' K' => cterm d' 0 h u p K') K
      else None
  | TShiftE _ _ =>
      match tvar t with
      | Some (g, i) => cons_lifted d (obind (entry h (NVar g i)) (glifts G)) K
      | None => None
      end
  end
with cterm (d w : nat) (h : lexp) (u : nat) (p : pexp) (K : lword) {struct p} : option lword :=
  match p with
  | PId => cons_lifted d (entry h (NBind u (WEnd SNil) None)) K
  | PAtom n =>
      cons_lifted d (entry h (NBind u (WEnd (match w with 0 => SNil | _ => shseg LNone w end)) (Some n))) K
  | PComp a p' => byp d w h [] a (fun w' K' => cterm d w' h u p' K') K
  | PShift g p' => bouter d w h [] g (fun w' K' => cterm d w' h u p' K') K
  end
with byp (d w : nat) (h : lexp) (G : list lexp) (a : aexp)
         (inner : nat -> lword -> option lword) (K : lword) {struct a} : option lword :=
  match a with
  | AId => inner w K
  | AAtom _ => None
  | ACompose a2 a1 => byp d w h G a2 (fun w' K' => byp d w' h G a1 inner K') K
  | AOuter g a' => bouter d w h G g (fun w' K' => byp d w' h G a' inner K') K
  | AInner g tg a' =>
      if is_bound g then None
      else obind (centry (d + w) G g tg K) (fun K1 =>
           obind (byp d w h (g :: G) a' inner K1)
             (cons_lifted d (obind (obind (glifts G (shseg g 1)) (slifts w)) (slift F ntm h))))
  | ALift g a' => if is_bound g then None else byp d w h (g :: G) a' inner K
  end
with ptree (p : pexp) {struct p} : option (word * option nat) :=
  match p with
  | PId => Some (WEnd SNil, None)
  | PAtom n => Some (WEnd SNil, Some n)
  | PComp a p' =>
      match ptree p', fold 0 a [] with
      | Some (w', b), Some l =>
          match expand l with
          | Some wa => match wcomp F ntm wa w' with Some w => Some (bnorm b w, b) | None => None end
          | None => None
          end
      | _, _ => None
      end
  | PShift g p' =>
      match ptree p' with
      | Some (w', b) => match wcomp F ntm (WEnd (shseg g 1)) w' with Some w => Some (bnorm b w, b) | None => None end
      | None => None
      end
  end.

Definition lnorm (e : aexp) : option lword := fold 0 e [].

(** The equations of the four functions. *)
Lemma fold_compose d a b K : fold d (ACompose a b) K = obind (fold d a K) (fold d b).
Proof. reflexivity. Qed.
Lemma fold_outer d h a K : fold d (AOuter h a) K = obind (cons_lifted d (Some (shseg h 1)) K) (fold d a).
Proof. reflexivity. Qed.
Lemma fold_inner d h t a K :
  fold d (AInner h t a) K
  = obind (centry d [] h t K) (fun K1 =>
      if is_bound h then fold (S d) a K1
      else obind (cons_lifted d (open_seg h) K1) (fun K2 =>
           obind (fold (S d) a K2) (cons_lifted d (close_seg h)))).
Proof. reflexivity. Qed.
Lemma fold_lift d h a K :
  fold d (ALift h a) K
  = if is_bound h then fold (S d) a K
    else obind (cons_lifted d (open_seg h) K) (fun K2 => obind (fold (S d) a K2) (cons_lifted d (close_seg h))).
Proof. reflexivity. Qed.
Lemma centry_var d G h g i K : centry d G h (TVarE g i) K = cons_lifted d (obind (entry h (NVar g i)) (glifts G)) K.
Proof. reflexivity. Qed.
Lemma ptree_comp a p :
  ptree (PComp a p)
  = match ptree p, fold 0 a [] with
    | Some (w', b), Some l =>
        match expand l with
        | Some wa => match wcomp F ntm wa w' with Some w => Some (bnorm b w, b) | None => None end
        | None => None
        end
    | _, _ => None
    end.
Proof. reflexivity. Qed.
Lemma ptree_shift g p :
  ptree (PShift g p)
  = match ptree p with
    | Some (w', b) => match wcomp F ntm (WEnd (shseg g 1)) w' with Some w => Some (bnorm b w, b) | None => None end
    | None => None
    end.
Proof. reflexivity. Qed.

Lemma centry_shift d G h g t K :
  centry d G h (TShiftE g t) K
  = match tvar (TShiftE g t) with
    | Some (g', i) => cons_lifted d (obind (entry h (NVar g' i)) (glifts G)) K
    | None => None
    end.
Proof. reflexivity. Qed.

Lemma centry_bind d G h u p K :
  centry d G h (TBindE u p) K
  = if u <? ntm then
      if phard p then
        match ptree p with
        | Some (w, b) => cons_lifted d (obind (entry h (NBind u w b)) (glifts G)) K
        | None => None
        end
      else under G d (fun d' K' => cterm d' 0 h u p K') K
    else None.
Proof. reflexivity. Qed.
Lemma cterm_id d w h u K : cterm d w h u PId K = cons_lifted d (entry h (NBind u (WEnd SNil) None)) K.
Proof. reflexivity. Qed.
Lemma cterm_atom d w h u n K :
  cterm d w h u (PAtom n) K
  = cons_lifted d (entry h (NBind u (WEnd (match w with 0 => SNil | _ => shseg LNone w end)) (Some n))) K.
Proof. reflexivity. Qed.
Lemma byp_inner d w h G g tg a' inner K :
  byp d w h G (AInner g tg a') inner K
  = if is_bound g then None
    else obind (centry (d + w) G g tg K) (fun K1 =>
         obind (byp d w h (g :: G) a' inner K1)
           (cons_lifted d (obind (obind (glifts G (shseg g 1)) (slifts w)) (slift F ntm h)))).
Proof. reflexivity. Qed.
Lemma byp_lift d w h G g a' inner K :
  byp d w h G (ALift g a') inner K = if is_bound g then None else byp d w h (g :: G) a' inner K.
Proof. reflexivity. Qed.

End Layered.

(** ** Soundness *)

(** A lift is a close before and an open after, around the lift by the
    bound label.  Decided by the normaliser, for a label variable and an
    atom. *)
Definition rclose {T} (x : label) : radj T :=
  rpush_inner (Some x) (RRename (mk_rvar None 0)) (rpush_outer None ridentity).
Definition ropen {T} (x : label) : radj T :=
  rpush_inner None (RRename (mk_rvar (Some x) 0)) (rpush_outer (Some x) ridentity).

(** Four laws, each computed with the operations on segments and words. *)
Definition law_O : order := order_of [].
Definition law_c : seg := SEnt (LAtom 0) (TCons (NVar LNone 0) TNil) 0 (SEnt LNone TNil 1 SNil).
Definition law_o : seg := SEnt (LAtom 0) TNil 1 (SEnt LNone (TCons (NVar (LAtom 0) 0) TNil) 0 SNil).
Definition law_wa : word := WAtom SNil [(LNone, 1)] 0 (WEnd SNil).
Definition law_wr : word := WAtom SNil [(LAtom 0, 1)] 0 (WEnd SNil).

Lemma law_ok (l : list label) : facts_ok l law_O.
Proof. apply order_of_ok; unfold lfacts_ok; constructor. Qed.

Lemma law_close {T} (x : label) (ae : list (radj T)) : sden [x] (@nil T) ae [] law_c = rclose x.
Proof.
  assert (Ec : sfront law_O (LAtom 0) (NVar LNone 0) (shseg LNone 1) = Some law_c) by (vm_compute; reflexivity).
  destruct (sfront_sound [x] (@nil T) ae [] law_O (law_ok _) 0 (le_n _) (LAtom 0) (NVar LNone 0) (shseg LNone 1) law_c
              (shseg_dd [x] LNone 1) I Ec) as [_ Sc].
  rewrite Sc, sden_shseg; reflexivity.
Qed.

Lemma law_open {T} (x : label) (ae : list (radj T)) : sden [x] (@nil T) ae [] law_o = ropen x.
Proof.
  assert (Eo : sfront law_O LNone (NVar (LAtom 0) 0) (shseg (LAtom 0) 1) = Some law_o) by (vm_compute; reflexivity).
  destruct (sfront_sound [x] (@nil T) ae [] law_O (law_ok _) 0 (le_n _) LNone (NVar (LAtom 0) 0) (shseg (LAtom 0) 1) law_o
              (shseg_dd [x] (LAtom 0) 1) I Eo) as [_ So].
  rewrite So, sden_shseg; reflexivity.
Qed.

Lemma lift_close_open {T} (x : label) (a : radj T) :
  rlift (Some x) a = rcompose (rcompose (ropen x) (rlift None a)) (rclose x).
Proof.
  assert (Ew : match wcomp law_O 0 (WEnd law_o) law_wa with
               | Some w => wcomp law_O 0 w (WEnd law_c)
               | None => None
               end = Some law_wr) by (vm_compute; reflexivity).
  destruct (wcomp law_O 0 (WEnd law_o) law_wa) as [w1|] eqn:E1; [|discriminate Ew].
  assert (Da : wdist [x] law_wa) by (cbn; repeat split; exact I).
  assert (Do : wdist [x] (WEnd law_o)) by (cbn; repeat split; exact I).
  assert (Dc : wdist [x] (WEnd law_c)) by (cbn; repeat split; exact I).
  destruct (wcomp_sound [x] (@nil T) [a] [] law_O (law_ok _) 0 (le_n _) (WEnd law_o) law_wa w1 Do Da E1) as [D1 S1].
  destruct (wcomp_sound [x] (@nil T) [a] [] law_O (law_ok _) 0 (le_n _) w1 (WEnd law_c) law_wr D1 Dc Ew) as [_ S2].
  rewrite S1, !wden_end, law_open, law_close in S2.
  unfold law_wr, law_wa in S2; rewrite !wden_atom, !wden_end in S2.
  change (sden [x] (@nil T) [a] [] SNil) with (@ridentity T) in S2.
  rewrite !rcompose_identity_l, !rcompose_identity_r in S2.
  exact S2.
Qed.

Lemma law_outer {T} (x : label) :
  rcompose (rcompose (rpush_inner None (RRename (mk_rvar (Some x) 0)) ridentity)
                     (rlift None (rpush_outer (Some x) ridentity)))
           (rclose x) = @ridentity T.
Proof.
  assert (Ew : match sfront law_O LNone (NVar (LAtom 0) 0) SNil, slift law_O 0 LNone (shseg (LAtom 0) 1) with
               | Some e, Some l => match scomp law_O 0 l law_c with Some s => scomp law_O 0 e s | None => None end
               | _, _ => None
               end = Some SNil) by (vm_compute; reflexivity).
  destruct (sfront law_O LNone (NVar (LAtom 0) 0) SNil) as [e|] eqn:E1; [|discriminate Ew].
  destruct (slift law_O 0 LNone (shseg (LAtom 0) 1)) as [l|] eqn:E2; [|discriminate Ew].
  destruct (scomp law_O 0 l law_c) as [s0|] eqn:E3; [|discriminate Ew].
  assert (Dc : sdistd [x] law_c) by (cbn; repeat split; exact I).
  destruct (sfront_sound [x] (@nil T) [] [] law_O (law_ok _) 0 (le_n _) LNone (NVar (LAtom 0) 0) SNil e I I E1) as [De Se].
  destruct (slift_sound [x] (@nil T) [] [] law_O (law_ok _) 0 (le_n _) LNone (shseg (LAtom 0) 1) l (shseg_dd [x] (LAtom 0) 1) E2)
    as [Dl Sl].
  destruct (scomp_sound [x] (@nil T) [] [] law_O (law_ok _) 0 (le_n _) l law_c s0 Dl Dc E3) as [D0 S0].
  destruct (scomp_sound [x] (@nil T) [] [] law_O (law_ok _) 0 (le_n _) e s0 SNil De D0 Ew) as [_ S1].
  rewrite S0, Se, Sl, sden_shseg, law_close, rcompose_assoc in S1.
  symmetry; exact S1.
Qed.

Lemma law_outer_bound {T} :
  rcompose (rpush_inner None (RRename (mk_rvar None 0)) ridentity) (rlift None (rpush_outer None ridentity)) = @ridentity T.
Proof.
  assert (Ew : match sfront law_O LNone (NVar LNone 0) SNil, slift law_O 0 LNone (shseg LNone 1) with
               | Some e, Some l => scomp law_O 0 e l
               | _, _ => None
               end = Some SNil) by (vm_compute; reflexivity).
  destruct (sfront law_O LNone (NVar LNone 0) SNil) as [e|] eqn:E1; [|discriminate Ew].
  destruct (slift law_O 0 LNone (shseg LNone 1)) as [l|] eqn:E2; [|discriminate Ew].
  destruct (sfront_sound [] (@nil T) [] [] law_O (law_ok _) 0 (le_n _) LNone (NVar LNone 0) SNil e I I E1) as [De Se].
  destruct (slift_sound [] (@nil T) [] [] law_O (law_ok _) 0 (le_n _) LNone (shseg LNone 1) l (shseg_dd [] LNone 1) E2) as [Dl Sl].
  destruct (scomp_sound [] (@nil T) [] [] law_O (law_ok _) 0 (le_n _) e l SNil De Dl Ew) as [_ S1].
  rewrite Se, Sl, sden_shseg in S1.
  symmetry; exact S1.
Qed.

Lemma law_lift_shift {T} (y : label) : rlift (Some y) (rpush_outer None (@ridentity T)) = rpush_outer None ridentity.
Proof.
  assert (Ew : slift law_O 0 (LAtom 0) (shseg LNone 1) = Some (shseg LNone 1)) by (vm_compute; reflexivity).
  destruct (slift_sound [y] (@nil T) [] [] law_O (law_ok _) 0 (le_n _) (LAtom 0) (shseg LNone 1) _ (shseg_dd [y] LNone 1) Ew)
    as [_ S1].
  rewrite sden_shseg in S1; symmetry; exact S1.
Qed.

(** ** The algebra of going around a payload

    [lifted d a] is [a] under [d] lifts by the bound label. *)

Section Algebra.

Context {T : Type}.

Definition lifted (d : nat) (a : radj T) : radj T := iter d (rlift None) a.

Lemma lifted_compose d a b : lifted d (rcompose a b) = rcompose (lifted d a) (lifted d b).
Proof. unfold lifted; induction d as [|d IH]; [reflexivity|]; cbn [iter]; rewrite IH, rlift_compose; reflexivity. Qed.

Lemma lifted_S d a : lifted (S d) a = lifted d (rlift None a).
Proof. unfold lifted; induction d as [|d IH]; [reflexivity|]; cbn [iter] in *; rewrite IH; reflexivity. Qed.

Lemma lifted_identity d : lifted d ridentity = ridentity.
Proof. unfold lifted; induction d as [|d IH]; [reflexivity|]; cbn [iter]; rewrite IH; apply rlift_identity. Qed.

Lemma lifted_add w t a : lifted (w + t) a = lifted w (lifted t a).
Proof. unfold lifted; apply iter_add. Qed.

Lemma shiftk_one : @shiftk T None 1 = rshift None.
Proof. reflexivity. Qed.

Lemma shiftk_add w t : @shiftk T None (w + t) = rcompose (shiftk None w) (shiftk None t).
Proof.
  induction w as [|w IH]; [symmetry; apply rcompose_identity_l|].
  cbn [Nat.add]; rewrite <- (shiftk_S (T:=T) None (w + t)), <- (shiftk_S (T:=T) None w), IH, rcompose_assoc; reflexivity.
Qed.

(** Weakening the bound label, then [a] under the lifts, is [a], then
    the weakening. *)
Lemma lifted_shift w a : rcompose (lifted w a) (shiftk None w) = rcompose (shiftk None w) a.
Proof.
  induction w as [|w IH]; [cbn; rewrite rcompose_identity_l, rcompose_identity_r; reflexivity|].
  rewrite <- (shiftk_S (T:=T) None w), shiftk_one; unfold lifted in *; cbn [iter].
  rewrite rcompose_assoc, rcompose_lift_shift, <- rcompose_assoc, IH, rcompose_assoc; reflexivity.
Qed.

(** A term whose payload ends with [B] is the term without it, then [B],
    when everything else is first sent through [A], which [B] undoes. *)
Lemma bypass h u (ρ : rpadj T) (A B : radj T) :
  rcompose B A = ridentity ->
  rpush_inner h (RBind u (rpcompose B ρ)) ridentity
  = rcompose B (rcompose (rpush_inner h (RBind u ρ) ridentity) (rlift h A)).
Proof.
  intros H; rewrite <- (rpush_inner_compose (@nil T) 0 (le_n 0)), rcompose_identity_l, rcompose_push_inner_r, H.
  reflexivity.
Qed.

(** [A] and [J] go around [a] with [t] bound variables: [A], then [a]
    under [t] lifts, then [J] is the identity, and [J] consumes exactly
    the [t] variables. *)
Definition bpair (a A J : radj T) (t : nat) : Prop :=
  rcompose (rcompose J (lifted t a)) A = ridentity /\ rcompose J (shiftk None t) = ridentity.

Lemma bypass_step h u (ρ : rpadj T) a A J t w :
  bpair a A J t ->
  rpush_inner h (RBind u (rpcompose (shiftk None w) (rpcompose a ρ))) ridentity
  = rcompose (lifted w J)
      (rcompose (lifted (w + t) a)
         (rcompose (rpush_inner h (RBind u (rpcompose (shiftk None (w + t)) ρ)) ridentity) (rlift h (lifted w A)))).
Proof.
  intros [H1 H2].
  assert (HBA : rcompose (rcompose (lifted w J) (lifted (w + t) a)) (lifted w A) = ridentity).
  { rewrite lifted_add, <- !lifted_compose, H1; apply lifted_identity. }
  assert (E : rcompose (shiftk None w) a
              = rcompose (rcompose (lifted w J) (lifted (w + t) a)) (shiftk None (w + t))).
  { rewrite shiftk_add, lifted_add.
    rewrite <- (rcompose_assoc (lifted w J) (lifted w (lifted t a)) _).
    rewrite (rcompose_assoc (lifted w (lifted t a)) (shiftk None w) (shiftk None t)).
    rewrite (lifted_shift w (lifted t a)).
    rewrite <- (rcompose_assoc (shiftk None w) (lifted t a) (shiftk None t)).
    rewrite (lifted_shift t a).
    rewrite (rcompose_assoc (lifted w J) (shiftk None w) _), (lifted_shift w J).
    rewrite <- (rcompose_assoc (shiftk None w) J _), (rcompose_assoc J (shiftk None t) a), H2, rcompose_identity_l.
    reflexivity. }
  rewrite (rcompose_assoc (lifted w J)), <- (bypass h u _ _ _ HBA), !rpcompose_compose, E; reflexivity.
Qed.

(** The units. *)
Lemma bpair_entry g tg : bpair (rpush_inner g tg ridentity) (rshift g) ridentity 0.
Proof.
  split; [|apply rcompose_identity_l].
  cbn [lifted iter]; rewrite rcompose_identity_l; apply rcompose_push_inner_shift.
Qed.

Lemma bpair_outer x :
  bpair (rshift (Some x)) (rclose x) (rpush_inner None (RRename (mk_rvar (Some x) 0)) ridentity) 1.
Proof.
  split; [|rewrite shiftk_one; apply rcompose_push_inner_shift].
  unfold lifted, rshift, rclose; cbn [iter].
  exact (law_outer x).
Qed.

Lemma bpair_outer_bound :
  bpair (rshift None) ridentity (rpush_inner None (RRename (mk_rvar None 0)) (@ridentity T)) 1.
Proof.
  split; [|rewrite shiftk_one; apply rcompose_push_inner_shift].
  rewrite rcompose_identity_r; unfold lifted, rshift; cbn [iter].
  exact law_outer_bound.
Qed.

Lemma rlift_shift_bound y : rlift (Some y) (@rshift T None) = rshift None.
Proof.
  unfold rshift.
  exact (law_lift_shift y).
Qed.

Lemma rlift_shiftk_bound y t : rlift (Some y) (@shiftk T None t) = shiftk None t.
Proof.
  induction t as [|t IH]; [apply rlift_identity|].
  rewrite <- (shiftk_S (T:=T) None t), <- rlift_compose, IH, shiftk_one, rlift_shift_bound; reflexivity.
Qed.

Lemma lifted_rlift y t (a : radj T) : lifted t (rlift (Some y) a) = rlift (Some y) (lifted t a).
Proof.
  unfold lifted; induction t as [|t IH]; [reflexivity|]; cbn [iter]; rewrite IH.
  apply rlift_comm; discriminate.
Qed.

Lemma bpair_lift y a A J t : bpair a A J t -> bpair (rlift (Some y) a) (rlift (Some y) A) (rlift (Some y) J) t.
Proof.
  intros [H1 H2]; split.
  - rewrite lifted_rlift, !rlift_compose, H1; apply rlift_identity.
  - rewrite <- (rlift_shiftk_bound y t), rlift_compose, H2; apply rlift_identity.
Qed.

End Algebra.

Section Sound.

Context {T : Type}.
Variable lenv : list label.
Variable tenv : list T.
Variable aenv : list (radj T).
Variable penv : list (rpadj T).
Variable F : order.
Hypothesis HF : facts_ok lenv F.
Variable ntm : nat.
Hypothesis Hntm : ntm <= List.length tenv.

Local Notation lden := (lden lenv).
Local Notation tden := (tden lenv tenv aenv penv).
Local Notation sden := (sden lenv tenv aenv penv).
Local Notation sdistd := (sdistd lenv).
Local Notation tldist := (tldist lenv).
Local Notation aeden := (aeden lenv tenv aenv penv).
Local Notation teden := (teden lenv tenv aenv penv).

(** A layered word is its segments one after the other. *)
Fixpoint lwden (l : lword) : radj T :=
  match l with
  | [] => ridentity
  | LS s :: r => rcompose (lwden r) (sden s)
  | LA L a :: r => rcompose (lwden r) (lifts lenv L (aden aenv a))
  end.

Definition lwdist (l : lword) : Prop := Forall (fun x => match x with LS s => sdistd s | LA _ _ => True end) l.

Lemma idts_len i n : tlen (idts i n) = n.
Proof. revert i; induction n as [|n IH]; intros i; cbn [idts tlen]; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma idts_nth n : forall i j, j < n -> tnth (idts i n) j = NVar LNone (i + j).
Proof.
  induction n as [|n IH]; intros i j Hj; [lia|]; cbn [idts tnth].
  destruct j as [|j]; [rewrite Nat.add_0_r; reflexivity|].
  rewrite (IH (S i) j) by lia; f_equal; lia.
Qed.

Lemma idts_dist n : forall i, tldist (idts i n).
Proof. induction n as [|n IH]; intros i; cbn [idts tldist]; [exact I|split; [exact I|apply IH]]. Qed.

Lemma tldist_tcat a b : tldist a -> tldist b -> tldist (tcat a b).
Proof.
  intros Ha Hb; apply (proj2 (tldist_iff lenv _)); intros t Ht; rewrite tcat_list in Ht.
  apply in_app_or in Ht; destruct Ht as [Ht|Ht];
    [exact (proj1 (tldist_iff lenv a) Ha t Ht)|exact (proj1 (tldist_iff lenv b) Hb t Ht)].
Qed.

Lemma slifts_sound d : forall s s', sdistd s -> slifts F ntm d s = Some s' -> sdistd s' /\ sden s' = lifted d (sden s).
Proof.
  intros s s' Hd; unfold slifts; destruct d as [|d0]; [intros H; injection H as <-; split; [exact Hd|reflexivity]|].
  set (d := S d0).
  destruct (scomp F ntm (shseg LNone d) s) as [s1|] eqn:E; [|discriminate].
  destruct (scomp_sound lenv tenv aenv penv F HF ntm Hntm _ _ _ (shseg_dd lenv LNone d) Hd E) as [Hd1 Hs1].
  pose proof (sdistd_sdist lenv _ Hd1) as Ed1.
  destruct (sfind F LNone s1) as [e|] eqn:Ef; [|discriminate]; apply (sfind_sound lenv F HF) in Ef.
  change (lden LNone) with (@None label) in Ef.
  destruct (ofe e) as [ts m] eqn:Eo; intros H.
  assert (Hts : tldist (tcat (idts 0 d) ts)).
  { apply tldist_tcat; [apply idts_dist|].
    destruct e as [[ts1 m1]|]; cbn [ofe] in Eo; injection Eo as <- <-; [|exact I].
    exact (sget_dd lenv _ _ _ _ Hd1 (eq_sym Ef)). }
  destruct (sset_sound lenv tenv aenv penv F HF ntm Hntm _ _ _ _ _ Ed1 H) as [Hd' Hs].
  split; [exact (sset_dd lenv tenv aenv penv F HF ntm Hntm _ _ _ _ _ Hd1 Hts H)|].
  apply rextensionality; intros [l j]; unfold lifted.
  rewrite (iter_rlift_apply tenv ntm Hntm), rapply_sden by exact Hd'; cbn [v_label v_index]; rewrite Hs.
  change (lden LNone) with (@None label).
  rewrite <- rapply_compose_cres, <- (sden_shseg lenv tenv aenv penv LNone d : sden (shseg LNone d) = shiftk None d), <- Hs1.
  destruct l as [l|]; cbn [label_eqb andb].
  - rewrite rapply_sden by exact Ed1; reflexivity.
  - cbn [esem]; rewrite tlen_tcat, idts_len, tnth_tcat, idts_len.
    destruct (Nat.ltb_spec j d) as [Hj|Hj].
    + replace (j <? d + tlen ts) with true by (symmetry; apply Nat.ltb_lt; lia).
      rewrite (idts_nth d 0 j Hj); reflexivity.
    + rewrite rapply_sden by exact Ed1; cbn [v_label v_index].
      rewrite <- Ef, <- (esem_ofe lenv tenv aenv penv ntm Hntm None e (j - d)), Eo; cbn [esem].
      destruct (Nat.ltb_spec (j - d) (tlen ts)) as [Hk|Hk];
        [replace (j <? d + tlen ts) with true by (symmetry; apply Nat.ltb_lt; lia); reflexivity|].
      replace (j <? d + tlen ts) with false by (symmetry; apply Nat.ltb_ge; lia).
      do 2 f_equal; lia.
Qed.

Lemma lwden_lpre U r : lwden (lpre U ++ r) = rcompose (lwden r) (sden U).
Proof.
  destruct U; [|reflexivity]; cbn [lpre app].
  change (lwden r = rcompose (lwden r) ridentity); rewrite rcompose_identity_r; reflexivity.
Qed.

Lemma lwdist_lpre U r : sdistd U -> lwdist r -> lwdist (lpre U ++ r).
Proof. intros HU Hr; destruct U; [exact Hr|constructor; assumption]. Qed.

Lemma cons_seg_sound K : forall s K',
  sdistd s -> lwdist K -> cons_seg F ntm s K = Some K' ->
  lwdist K' /\ lwden K' = rcompose (lwden K) (sden s).
Proof.
  induction K as [|[s1|L a] K0 IH]; intros s K' Hs HK; cbn [cons_seg].
  - intros H; injection H as <-; rewrite <- (app_nil_r (lpre s)); split; [apply lwdist_lpre; assumption|].
    rewrite lwden_lpre; reflexivity.
  - inversion HK as [|? ? H1 H0]; subst.
    destruct (negb (has_terms s) || (bound_only s1 && no_atoms s)).
    + destruct (scomp F ntm s1 s) as [s'|] eqn:E; [|discriminate].
      destruct (scomp_sound lenv tenv aenv penv F HF ntm Hntm s1 s s' H1 Hs E) as [Hd' Hs'].
      assert (Hgoal : lwden (LS s' :: K0) = rcompose (lwden (LS s1 :: K0)) (sden s)).
      { cbn [lwden]; rewrite Hs', rcompose_assoc; reflexivity. }
      destruct s' as [|h ts m r]; intros H; injection H as <-.
      * split; [exact H0|]; rewrite <- Hgoal; change (lwden K0 = rcompose (lwden K0) ridentity);
        rewrite rcompose_identity_r; reflexivity.
      * split; [constructor; assumption|exact Hgoal].
    + intros H; injection H as <-; split; [constructor; assumption|reflexivity].
  - inversion HK as [|? ? _ H0]; subst.
    destruct (has_terms s); [intros H; injection H as <-; split; [constructor; assumption|reflexivity]|].
    destruct (wcomp F ntm (WAtom SNil L a (WEnd SNil)) (WEnd s)) as [[s0|s' L' a' [U|s2 L2 a2 w2]]|] eqn:E;
      [intros H; discriminate H| |intros H; discriminate H|intros H; discriminate H].
    destruct (cons_seg F ntm s' K0) as [K''|] eqn:E2; [|intros H; discriminate H]; cbn [obind]; intros H; injection H as <-.
    destruct (wcomp_sound lenv tenv aenv penv F HF ntm Hntm (WAtom SNil L a (WEnd SNil)) (WEnd s) _ (conj I I) Hs E)
      as [[Hd' HdU] D].
    destruct (IH s' K'' Hd' H0 E2) as [HK'' DK''].
    split; [apply lwdist_lpre; [exact HdU|constructor; [exact I|exact HK'']]|].
    rewrite lwden_lpre; cbn [lwden]; rewrite DK''.
    rewrite !wden_atom in D.
    change (Normalise.sden lenv tenv aenv penv SNil) with (@ridentity T) in D.
    change (Normalise.wden lenv tenv aenv penv (WEnd SNil)) with (@ridentity T) in D.
    change (Normalise.wden lenv tenv aenv penv (WEnd U)) with (sden U) in D.
    change (Normalise.wden lenv tenv aenv penv (WEnd s)) with (sden s) in D.
    rewrite rcompose_identity_l, rcompose_identity_r in D.
    rewrite <- !rcompose_assoc, D; reflexivity.
Qed.

(** The multiplied-out word means the same. *)
Lemma expand_sound l : forall w, lwdist l -> expand F ntm l = Some w ->
  Normalise.wdist lenv w /\ Normalise.wden lenv tenv aenv penv w = lwden l.
Proof.
  induction l as [|[s|L a] r IH]; intros w Hl; cbn [expand].
  - intros H; injection H as <-; split; [exact I|reflexivity].
  - inversion Hl as [|? ? Hs Hr]; subst.
    destruct (expand F ntm r) as [w0|] eqn:E; [|discriminate]; cbn [obind]; intros H.
    destruct (IH w0 Hr eq_refl) as [Hd0 D0].
    destruct (wcomp_sound lenv tenv aenv penv F HF ntm Hntm w0 (WEnd s) w Hd0 Hs H) as [Hd D].
    split; [exact Hd|]; rewrite D, D0; reflexivity.
  - inversion Hl as [|? ? _ Hr]; subst.
    destruct (expand F ntm r) as [w0|] eqn:E; [|discriminate]; cbn [obind]; intros H.
    destruct (IH w0 Hr eq_refl) as [Hd0 D0].
    destruct (wcomp_sound lenv tenv aenv penv F HF ntm Hntm w0 (WAtom SNil L a (WEnd SNil)) w Hd0 (conj I I) H) as [Hd D].
    split; [exact Hd|]; rewrite D, D0, wden_atom; cbn [lwden].
    change (Normalise.sden lenv tenv aenv penv SNil) with (@ridentity T).
    change (Normalise.wden lenv tenv aenv penv (WEnd SNil)) with (@ridentity T).
    rewrite rcompose_identity_l, rcompose_identity_r; reflexivity.
Qed.

(** What an optional segment means, when there is one. *)
Definition sok (s : option seg) (x : radj T) : Prop := forall s0, s = Some s0 -> sdistd s0 /\ sden s0 = x.

Lemma sok_some s : sdistd s -> sok (Some s) (sden s).
Proof. intros Hd s0 E; injection E as <-; split; [exact Hd|reflexivity]. Qed.

Lemma sok_eq s x y : sok s x -> x = y -> sok s y.
Proof. intros H <-; exact H. Qed.

Lemma sok_slift h s x : sok s x -> sok (obind s (slift F ntm h)) (rlift (lden h) x).
Proof.
  intros H s0 E; destruct s as [s1|]; [|discriminate]; destruct (H s1 eq_refl) as [Hd Hs].
  destruct (slift_sound lenv tenv aenv penv F HF ntm Hntm h s1 s0 Hd E) as [A B]; split; [exact A|rewrite B, Hs; reflexivity].
Qed.

Lemma sok_slifts w s x : sok s x -> sok (obind s (slifts F ntm w)) (lifted w x).
Proof.
  intros H s0 E; destruct s as [s1|]; [|discriminate]; destruct (H s1 eq_refl) as [Hd Hs].
  destruct (slifts_sound w s1 s0 Hd E) as [A B]; split; [exact A|rewrite B, Hs; reflexivity].
Qed.

(** Lifts by the labels of [G], the first innermost. *)
Fixpoint glden (G : list lexp) (x : radj T) : radj T :=
  match G with [] => x | g :: G' => glden G' (rlift (lden g) x) end.

Lemma glden_compose G : forall a b, glden G (rcompose a b) = rcompose (glden G a) (glden G b).
Proof. induction G as [|g G IH]; intros a b; [reflexivity|]; cbn [glden]; rewrite <- rlift_compose; apply IH. Qed.

Lemma glden_identity G : glden G ridentity = ridentity.
Proof. induction G as [|g G IH]; [reflexivity|]; cbn [glden]; rewrite rlift_identity; exact IH. Qed.

Lemma sok_glifts G : forall s x, sok s x -> sok (obind s (glifts F ntm G)) (glden G x).
Proof.
  induction G as [|g G IH]; intros s x H.
  - intros s0 E; destruct s as [s1|]; [|discriminate]; injection E as <-; exact (H s1 eq_refl).
  - intros s0 E; destruct s as [s1|]; [|discriminate]; cbn [obind glifts] in E.
    exact (IH _ _ (sok_slift g (Some s1) x H) s0 E).
Qed.

Lemma sok_glifts1 G s : sdistd s -> sok (glifts F ntm G s) (glden G (sden s)).
Proof. intros Hd; exact (sok_glifts G (Some s) _ (sok_some s Hd)). Qed.

Lemma sok_entry h t : Normalise.tdist lenv t -> sok (entry F h t) (rpush_inner (lden h) (tden t) ridentity).
Proof. intros Ht s E; exact (sfront_sound lenv tenv aenv penv F HF ntm Hntm h t SNil s I Ht E). Qed.

Lemma sok_close h x : lden h = Some x -> sok (close_seg F h) (rclose x).
Proof.
  intros Hx s H.
  destruct (sfront_sound lenv tenv aenv penv F HF ntm Hntm h (NVar LNone 0) (shseg LNone 1) s (shseg_dd lenv _ _) I H) as [A B].
  split; [exact A|]; rewrite B, Hx; reflexivity.
Qed.

Lemma sok_open h x : lden h = Some x -> sok (open_seg F h) (ropen x).
Proof.
  intros Hx s H.
  destruct (sfront_sound lenv tenv aenv penv F HF ntm Hntm LNone (NVar h 0) (shseg h 1) s (shseg_dd lenv _ _) I H) as [A B].
  split; [exact A|]; rewrite B, sden_shseg; unfold shiftk, ropen; cbn [iter Normalise.tden]; rewrite Hx; reflexivity.
Qed.

Lemma cons_lifted_sound d s x K K' :
  sok s x -> lwdist K -> cons_lifted F ntm d s K = Some K' ->
  lwdist K' /\ lwden K' = rcompose (lwden K) (lifted d x).
Proof.
  intros Hs HK; unfold cons_lifted; destruct s as [s0|]; [|discriminate]; cbn [obind].
  destruct (slifts F ntm d s0) as [s'|] eqn:E; [|discriminate]; cbn [obind]; intros H.
  destruct (Hs s0 eq_refl) as [Hd0 Hx]; destruct (slifts_sound d s0 s' Hd0 E) as [Hd' Hs'].
  destruct (cons_seg_sound K s' K' Hd' HK H) as [A B]; split; [exact A|]; rewrite B, Hs', Hx; reflexivity.
Qed.

Definition named (G : list lexp) : Prop := Forall (fun g => is_bound g = false) G.

Lemma named_label h : is_bound h = false -> exists x, lden h = Some x.
Proof. destruct h; cbn; [discriminate| |]; intros _; eexists; reflexivity. Qed.

Lemma bound_label h : is_bound h = true -> lden h = None.
Proof. destruct h; cbn; [reflexivity|discriminate|discriminate]. Qed.

Lemma bpair_glden G : named G -> forall a A J t, bpair a A J t -> bpair (glden G a) (glden G A) (glden G J) t.
Proof.
  induction 1 as [|g G Hg _ IH]; intros a A J t H; [exact H|]; cbn [glden].
  destruct (named_label g Hg) as [x Hx]; rewrite Hx; apply IH, bpair_lift, H.
Qed.

(** A close, something one level deeper, and an open. *)
Lemma close_open_den d y (X Kd : radj T) :
  rcompose (rcompose (rcompose Kd (lifted d (ropen y))) (lifted (S d) X)) (lifted d (rclose y))
  = rcompose Kd (lifted d (rlift (Some y) X)).
Proof. rewrite (lift_close_open y), lifted_S, !lifted_compose, !rcompose_assoc; reflexivity. Qed.

Lemma under_sound G : named G -> forall d k x K K',
  (forall d' K0 K1, lwdist K0 -> k d' K0 = Some K1 -> lwdist K1 /\ lwden K1 = rcompose (lwden K0) (lifted d' x)) ->
  lwdist K -> under F ntm G d k K = Some K' ->
  lwdist K' /\ lwden K' = rcompose (lwden K) (lifted d (glden G x)).
Proof.
  induction 1 as [|g G Hg _ IH]; intros d k x K K' Hk HK; cbn [under glden]; [apply Hk, HK|].
  destruct (named_label g Hg) as [y Hy].
  apply IH; [|exact HK]; intros d' K0 K3 HK0 H.
  destruct (cons_lifted F ntm d' (open_seg F g) K0) as [K1|] eqn:E1; [|discriminate]; cbn [obind] in H.
  destruct (k (S d') K1) as [K2|] eqn:E2; [|discriminate]; cbn [obind] in H.
  destruct (cons_lifted_sound d' _ _ K0 K1 (sok_open g y Hy) HK0 E1) as [H1 D1].
  destruct (Hk (S d') K1 K2 H1 E2) as [H2 D2].
  destruct (cons_lifted_sound d' _ _ K2 K3 (sok_close g y Hy) H2 H) as [H3 D3]; split; [exact H3|].
  rewrite D3, D2, D1, Hy; apply close_open_den.
Qed.

(** What [inner] must do: put the term [y] at [h] with payload [ρ] and
    then [w] weakenings of the bound label. *)
Definition ispec (d : nat) (h : lexp) (y : T) (inner : nat -> lword -> option lword) (ρ : rpadj T) : Prop :=
  forall w K K', lwdist K -> inner w K = Some K' ->
    lwdist K' /\ lwden K' = rcompose (lwden K)
                              (lifted d (rpush_inner (lden h) (RBind y (rpcompose (shiftk None w) ρ)) ridentity)).

Lemma line4 d (K J a E S : radj T) :
  rcompose (rcompose (rcompose (rcompose K (lifted d J)) (lifted d a)) (lifted d E)) (lifted d S)
  = rcompose K (lifted d (rcompose J (rcompose a (rcompose E S)))).
Proof. rewrite !lifted_compose, !rcompose_assoc; reflexivity. Qed.

Lemma bouter_sound d h y G g next ρ :
  named G -> ispec d h y next ρ ->
  ispec d h y (fun w K => bouter F ntm d w h G g next K) (rpcompose (glden G (rshift (lden g))) ρ).
Proof.
  intros HG Hn w K K' HK; unfold bouter.
  destruct (cons_lifted F ntm (d + w) _ K) as [K1|] eqn:E1; [|discriminate]; cbn [obind].
  destruct (cons_lifted F ntm (d + w + 1) _ K1) as [K2|] eqn:E2; [|discriminate]; cbn [obind].
  destruct (next (w + 1) K2) as [K3|] eqn:E3; [|discriminate]; cbn [obind].
  set (J := rpush_inner None (RRename (mk_rvar (lden g) 0)) (@ridentity T)).
  destruct (cons_lifted_sound (d + w) _ (glden G J) K K1 (sok_glifts G _ _ (sok_entry LNone (NVar g 0) I)) HK E1) as [H1 D1].
  destruct (cons_lifted_sound (d + w + 1) _ _ K1 K2 (sok_glifts1 G _ (shseg_dd lenv g 1)) H1 E2) as [H2 D2].
  destruct (Hn (w + 1) K2 K3 H2 E3) as [H3 D3].
  rewrite sden_shseg in D2; change (shiftk (lden g) 1) with (@rshift T (lden g)) in D2.
  rewrite <- Nat.add_assoc, lifted_add in D2; rewrite lifted_add in D1.
  unfold J in *; clear J.
  destruct (is_bound g) eqn:Eb.
  - intros H; injection H as <-; split; [exact H3|].
    pose proof (bpair_glden G HG _ _ _ _ (@bpair_outer_bound T)) as HP.
    rewrite (bound_label g Eb) in *; rewrite glden_identity in HP.
    rewrite (bypass_step (lden h) y ρ _ _ _ 1 w HP), lifted_identity, rlift_identity, rcompose_identity_r.
    rewrite D3, D2, D1, !lifted_compose, !rcompose_assoc; reflexivity.
  - destruct (named_label g Eb) as [x Hx]; intros H.
    destruct (cons_lifted_sound d _ _ K3 K' (sok_slift h _ _ (sok_slifts w _ _ (sok_glifts G _ _ (sok_close g x Hx)))) H3 H)
      as [H4 D4]; split; [exact H4|].
    pose proof (bpair_glden G HG _ _ _ _ (bpair_outer (T:=T) x)) as HP.
    rewrite Hx in *.
    rewrite (bypass_step (lden h) y ρ _ _ _ 1 w HP), D4, D3, D2, D1; apply line4.
Qed.

Lemma shiftk_payload_id w : rpcompose (shiftk None w) (@rpidentity T) = rpidentity.
Proof.
  rewrite <- (rpcompose_identity rpidentity) at 2; apply rpcompose_named; intros [l j] Hl; cbn in Hl.
  rewrite shiftk_apply, rapply_identity; destruct l as [l|]; [|contradiction]; cbn; rewrite Nat.add_0_r; reflexivity.
Qed.

Lemma tvar_sound t g i :
  tvar F t = Some (g, i) -> Normalise.teden lenv tenv aenv penv t = RRename (mk_rvar (lden g) i).
Proof.
  revert g i; induction t as [g0 i0|u p|h t IH]; intros g i H; cbn [tvar] in H.
  - injection H as <- <-; reflexivity.
  - discriminate H.
  - destruct (tvar F t) as [[g1 i1]|]; [|discriminate H].
    cbn [Normalise.teden]; rewrite (IH _ _ eq_refl).
    destruct (lcmp F h g1) as [c|] eqn:Ec; [|discriminate H].
    unfold shift_rvar; cbn [v_label v_index].
    destruct c.
    + injection H as <- <-; pose proof (lcmp_sound lenv F HF _ _ _ Ec) as E; cbn in E; rewrite E, label_eqb_refl.
      reflexivity.
    + injection H as <- <-; pose proof (lcmp_neq lenv F HF _ _ _ Ec ltac:(discriminate)) as E.
      destruct (label_eqb (lden h) (lden g1)) eqn:El; [apply label_eqb_eq in El; contradiction|reflexivity].
    + injection H as <- <-; pose proof (lcmp_neq lenv F HF _ _ _ Ec ltac:(discriminate)) as E.
      destruct (label_eqb (lden h) (lden g1)) eqn:El; [apply label_eqb_eq in El; contradiction|reflexivity].
Qed.

Theorem sound :
  (forall e,
     (forall d K K', lwdist K -> fold F ntm d e K = Some K' ->
        lwdist K' /\ lwden K' = rcompose (lwden K) (lifted d (aeden e)))
     /\ (forall d h y G inner ρ, named G -> ispec d h y inner ρ ->
           ispec d h y (fun w K => byp F ntm d w h G e inner K) (rpcompose (glden G (aeden e)) ρ)))
  /\ (forall t d G h K K', named G -> lwdist K -> centry F ntm d G h t K = Some K' ->
        lwdist K' /\ lwden K' = rcompose (lwden K) (lifted d (glden G (rpush_inner (lden h) (teden t) ridentity))))
  /\ (forall p,
        (forall d h u y, nth_error tenv u = Some y ->
           ispec d h y (fun w K => cterm F ntm d w h u p K) (Normalise.peden lenv tenv aenv penv p))
        /\ (forall w b, ptree F ntm p = Some (w, b) ->
              Normalise.wdist lenv w
              /\ rpcompose (Normalise.wden lenv tenv aenv penv w) (bden penv b) = Normalise.peden lenv tenv aenv penv p)).
Proof.
  apply exp_mind.
  - (* AId *) split.
    + intros d K K' HK H; injection H as <-; split; [exact HK|].
      cbn [Normalise.aeden]; rewrite lifted_identity, rcompose_identity_r; reflexivity.
    + intros d h y G inner ρ HG Hi; cbn [Normalise.aeden]; rewrite glden_identity, rpcompose_identity.
      intros w K K' HK H; exact (Hi w K K' HK H).
  - (* AAtom *) intros n; split.
    + intros d K K' HK H; injection H as <-; split; [constructor; [exact I|exact HK]|].
      cbn [lwden Normalise.aeden]; destruct d; reflexivity.
    + intros d h y G inner ρ HG Hi w K K' HK H; discriminate H.
  - (* ACompose *) intros a [IHa1 IHa2] b [IHb1 IHb2]; split.
    + intros d K K' HK; rewrite fold_compose; destruct (fold F ntm d a K) as [K1|] eqn:E1; [|discriminate]; cbn [obind]; intros H.
      destruct (IHa1 d K K1 HK E1) as [H1 D1]; destruct (IHb1 d K1 K' H1 H) as [H2 D2]; split; [exact H2|].
      rewrite D2, D1; cbn [Normalise.aeden]; rewrite lifted_compose, rcompose_assoc; reflexivity.
    + intros d h y G inner ρ HG Hi; cbn [Normalise.aeden]; rewrite glden_compose, <- rpcompose_compose.
      exact (IHa2 d h y G (fun w' K' => byp F ntm d w' h G b inner K') _ HG (IHb2 d h y G inner ρ HG Hi)).
  - (* AOuter *) intros g a [IH1 IH2]; split.
    + intros d K K' HK; rewrite fold_outer.
      destruct (cons_lifted F ntm d (Some (shseg g 1)) K) as [K1|] eqn:E1; [|discriminate]; cbn [obind]; intros H.
      destruct (cons_lifted_sound d _ _ K K1 (sok_some _ (shseg_dd lenv g 1)) HK E1) as [H1 D1].
      destruct (IH1 d K1 K' H1 H) as [H2 D2]; split; [exact H2|].
      rewrite D2, D1; cbn [Normalise.aeden]; rewrite <- rcompose_assoc, <- lifted_compose.
      rewrite sden_shseg; unfold shiftk; cbn [iter]; rewrite rcompose_identity_push_outer; reflexivity.
    + intros d h y G inner ρ HG Hi; cbn [Normalise.aeden].
      rewrite rpush_outer_as_compose, glden_compose, <- rpcompose_compose.
      exact (bouter_sound d h y G g (fun w' K' => byp F ntm d w' h G a inner K') _ HG (IH2 d h y G inner ρ HG Hi)).
  - (* AInner *) intros g t IHt a [IH1 IH2].
    assert (Ein : aeden (AInner g t a)
                  = rcompose (rpush_inner (lden g) (teden t) ridentity) (rlift (lden g) (aeden a))).
    { cbn [Normalise.aeden]; rewrite <- (rpush_inner_compose tenv ntm Hntm), rcompose_identity_l; reflexivity. }
    split.
    + intros d K K' HK; rewrite fold_inner.
      destruct (centry F ntm d [] g t K) as [K1|] eqn:E1; [|discriminate]; cbn [obind].
      destruct (IHt d [] g K K1 (Forall_nil _) HK E1) as [H1 D1]; cbn [glden] in D1.
      destruct (is_bound g) eqn:Eb.
      * intros H; destruct (IH1 (S d) K1 K' H1 H) as [H2 D2]; split; [exact H2|].
        rewrite D2, D1, Ein, (bound_label g Eb), lifted_S, <- rcompose_assoc, <- lifted_compose; reflexivity.
      * destruct (named_label g Eb) as [x Hx].
        destruct (cons_lifted F ntm d (open_seg F g) K1) as [K2|] eqn:E2; [|discriminate]; cbn [obind].
        destruct (fold F ntm (S d) a K2) as [K3|] eqn:E3; [|discriminate]; cbn [obind]; intros H.
        destruct (cons_lifted_sound d _ _ K1 K2 (sok_open g x Hx) H1 E2) as [H2 D2].
        destruct (IH1 (S d) K2 K3 H2 E3) as [H3 D3].
        destruct (cons_lifted_sound d _ _ K3 K' (sok_close g x Hx) H3 H) as [H4 D4]; split; [exact H4|].
        rewrite D4, D3, D2, close_open_den, D1, Ein, Hx, <- rcompose_assoc, <- lifted_compose; reflexivity.
    + intros d h y G inner ρ HG Hi w K K' HK; rewrite byp_inner.
      destruct (is_bound g) eqn:Eb; [discriminate|].
      destruct (centry F ntm (d + w) G g t K) as [K1|] eqn:E1; [|discriminate]; cbn [obind].
      destruct (byp F ntm d w h (g :: G) a inner K1) as [K2|] eqn:E2; [|discriminate]; cbn [obind]; intros H.
      destruct (IHt (d + w) G g K K1 HG HK E1) as [H1 D1].
      destruct (IH2 d h y (g :: G) inner ρ (Forall_cons _ Eb HG) Hi w K1 K2 H1 E2) as [H2 D2].
      destruct (cons_lifted_sound d _ _ K2 K'
                  (sok_slift h _ _ (sok_slifts w _ _ (sok_glifts1 G _ (shseg_dd lenv g 1)))) H2 H) as [H3 D3].
      split; [exact H3|].
      pose proof (bpair_glden G HG _ _ _ _ (bpair_entry (T:=T) (lden g) (teden t))) as HP.
      rewrite glden_identity in HP.
      rewrite Ein, glden_compose, <- rpcompose_compose.
      rewrite (bypass_step (lden h) y _ _ _ _ 0 w HP), lifted_identity, rcompose_identity_l, Nat.add_0_r.
      rewrite D3, D2, D1, lifted_add, sden_shseg; cbn [glden].
      rewrite !lifted_compose, !rcompose_assoc; reflexivity.
  - (* ALift *) intros g a [IH1 IH2]; split.
    + intros d K K' HK; rewrite fold_lift; destruct (is_bound g) eqn:Eb.
      * intros H; destruct (IH1 (S d) K K' HK H) as [H2 D2]; split; [exact H2|].
        rewrite D2; cbn [Normalise.aeden]; rewrite (bound_label g Eb), lifted_S; reflexivity.
      * destruct (named_label g Eb) as [x Hx].
        destruct (cons_lifted F ntm d (open_seg F g) K) as [K2|] eqn:E2; [|discriminate]; cbn [obind].
        destruct (fold F ntm (S d) a K2) as [K3|] eqn:E3; [|discriminate]; cbn [obind]; intros H.
        destruct (cons_lifted_sound d _ _ K K2 (sok_open g x Hx) HK E2) as [H2 D2].
        destruct (IH1 (S d) K2 K3 H2 E3) as [H3 D3].
        destruct (cons_lifted_sound d _ _ K3 K' (sok_close g x Hx) H3 H) as [H4 D4]; split; [exact H4|].
        rewrite D4, D3, D2, close_open_den; cbn [Normalise.aeden]; rewrite Hx; reflexivity.
    + intros d h y G inner ρ HG Hi w K K' HK; rewrite byp_lift.
      destruct (is_bound g) eqn:Eb; [discriminate|].
      exact (IH2 d h y (g :: G) inner ρ (Forall_cons _ Eb HG) Hi w K K' HK).
  - (* TVarE *) intros g i d G h K K' HG HK H; rewrite centry_var in H.
    exact (cons_lifted_sound d _ _ K K' (sok_glifts G _ _ (sok_entry h (NVar g i) I)) HK H).
  - (* TBindE *) intros u p IHp d G h K K' HG HK; rewrite centry_bind.
    destruct (u <? ntm) eqn:Eu; [|discriminate]; apply Nat.ltb_lt in Eu.
    destruct (nth_error tenv u) as [y|] eqn:Ey; [|apply nth_error_None in Ey; lia].
    destruct IHp as [IHp IHt].
    destruct (phard p).
    { destruct (ptree F ntm p) as [[w b]|] eqn:Ep; [|discriminate]; intros H.
      destruct (IHt w b eq_refl) as [Hw Dw].
      destruct (cons_lifted_sound d _ _ K K' (sok_glifts G _ _ (sok_entry h (NBind u w b) Hw)) HK H) as [A B].
      split; [exact A|]; rewrite B, (tden_bind lenv tenv aenv penv u w b y Ey), Dw.
      cbn [Normalise.teden]; rewrite Ey; reflexivity. }
    intros H; cbn [Normalise.teden]; rewrite Ey.
    refine (under_sound G HG d _ _ K K' _ HK H); intros d' K0 K1 HK0 H0.
    destruct (IHp d' h u y Ey 0 K0 K1 HK0 H0) as [A B]; split; [exact A|].
    rewrite B; change (shiftk None 0) with (@ridentity T); rewrite rpcompose_identity; reflexivity.
  - (* TShiftE *) intros g t _ d G h K K' HG HK H; rewrite centry_shift in H.
    destruct (tvar F (TShiftE g t)) as [[g' i]|] eqn:Ev; [|discriminate H].
    rewrite (tvar_sound _ _ _ Ev).
    exact (cons_lifted_sound d _ _ K K' (sok_glifts G _ _ (sok_entry h (NVar g' i) I)) HK H).
  - (* PId *) split; [|intros w b H; injection H as <- <-; split; [exact I|apply rpcompose_identity]].
    intros d h u y Ey w K K' HK H; rewrite cterm_id in H.
    destruct (cons_lifted_sound d _ _ K K' (sok_entry h (NBind u (WEnd SNil) None) I) HK H) as [A B]; split; [exact A|].
    rewrite B; cbn [Normalise.tden Normalise.peden]; rewrite Ey.
    cbn [Normalise.wden Normalise.sins Normalise.souts Normalise.bden].
    rewrite shiftk_payload_id, rpcompose_identity; reflexivity.
  - (* PAtom *) intros n; split; [|intros w b H; injection H as <- <-; split; [exact I|apply rpcompose_identity]].
    intros d h u y Ey w K K' HK H; rewrite cterm_atom in H.
    assert (Hd : Normalise.tdist lenv (NBind u (WEnd (match w with 0 => SNil | _ => shseg LNone w end)) (Some n))).
    { destruct w; [exact I|apply shseg_dd]. }
    destruct (cons_lifted_sound d _ _ K K' (sok_entry h _ Hd) HK H) as [A B]; split; [exact A|].
    rewrite B; cbn [Normalise.tden Normalise.peden]; rewrite Ey; destruct w; reflexivity.
  - (* PComp *) intros a [IHf IHa] p [IHp IHt]; split.
    + intros d h u y Ey; cbn [Normalise.peden].
      exact (IHa d h y [] (fun w' K' => cterm F ntm d w' h u p K') _ (Forall_nil _) (IHp d h u y Ey)).
    + intros w b; rewrite ptree_comp.
      destruct (ptree F ntm p) as [[w' b']|] eqn:Ep; [|discriminate].
      destruct (fold F ntm 0 a []) as [l|] eqn:El; [|discriminate].
      destruct (expand F ntm l) as [wa|] eqn:Ex; [|discriminate].
      destruct (wcomp F ntm wa w') as [w0|] eqn:Ec; [|discriminate]; intros H; injection H as <- <-.
      destruct (IHt w' b' eq_refl) as [Hw' Dw'].
      destruct (IHf 0 [] l (Forall_nil _) El) as [Hl Dl].
      destruct (expand_sound l wa Hl Ex) as [Hwa Dwa].
      destruct (wcomp_sound lenv tenv aenv penv F HF ntm Hntm wa w' w0 Hwa Hw' Ec) as [Hw0 Dw0].
      split; [apply bnorm_dd, Hw0|].
      rewrite bnorm_sound, Dw0, Dwa, Dl; cbn [lwden lifted iter Normalise.peden].
      rewrite rcompose_identity_l, <- Dw'; symmetry; apply rpcompose_compose.
  - (* PShift *) intros g p [IHp IHt]; split.
    + intros d h u y Ey; cbn [Normalise.peden]; rewrite rpshift_as_pcompose.
      exact (bouter_sound d h y [] g (fun w' K' => cterm F ntm d w' h u p K') _ (Forall_nil _) (IHp d h u y Ey)).
    + intros w b; rewrite ptree_shift.
      destruct (ptree F ntm p) as [[w' b']|] eqn:Ep; [|discriminate].
      destruct (wcomp F ntm (WEnd (shseg g 1)) w') as [w0|] eqn:Ec; [|discriminate]; intros H; injection H as <- <-.
      destruct (IHt w' b' eq_refl) as [Hw' Dw'].
      destruct (wcomp_sound lenv tenv aenv penv F HF ntm Hntm (WEnd (shseg g 1)) w' w0 (shseg_dd lenv g 1) Hw' Ec) as [Hw0 Dw0].
      split; [apply bnorm_dd, Hw0|].
      rewrite bnorm_sound, Dw0, wden_end, sden_shseg; cbn [Normalise.peden].
      rewrite rpshift_as_pcompose, <- Dw'; symmetry; apply rpcompose_compose.
Qed.

(** The layered word of an expression means what the expression means. *)
Theorem lnorm_sound e l : lnorm F ntm e = Some l -> lwden l = aeden e.
Proof.
  intros H; destruct (proj1 (proj1 sound e) 0 [] l (Forall_nil _) H) as [_ D].
  rewrite D; cbn [lwden lifted iter]; apply rcompose_identity_l.
Qed.

End Sound.

(** ** The decision

    Two expressions with the same layered word mean the same.  The
    words are compared with the lazy conjunction of [Normalise]. *)

Definition lstep_eqb (x y : lstep) : bool :=
  match x, y with
  | LS s, LS s' => seg_eqb s s'
  | LA L a, LA L' a' => if lifts_eqb L L' then Nat.eqb a a' else false
  | _, _ => false
  end.

Fixpoint lword_eqb (l m : lword) : bool :=
  match l, m with
  | [], [] => true
  | x :: l', y :: m' => if lstep_eqb x y then lword_eqb l' m' else false
  | _, _ => false
  end.

Lemma lstep_eqb_eq x y : lstep_eqb x y = true -> x = y.
Proof.
  destruct x as [s|L a], y as [s'|L' a']; cbn; try discriminate.
  - intros H; rewrite (proj1 (proj2 (proj2 nf_eqb_eq)) s s' H); reflexivity.
  - destruct (lifts_eqb L L') eqn:E; [|discriminate]; intros H.
    apply lifts_eqb_eq in E; apply Nat.eqb_eq in H; subst; reflexivity.
Qed.

Lemma lword_eqb_eq l : forall m, lword_eqb l m = true -> l = m.
Proof.
  induction l as [|x l IH]; intros [|y m]; cbn; try discriminate; [reflexivity|].
  destruct (lstep_eqb x y) eqn:E; [|discriminate]; intros H.
  rewrite (lstep_eqb_eq x y E), (IH m H); reflexivity.
Qed.

Definition nf_eq_l (F : order) (ntm : nat) (e1 e2 : aexp) : bool :=
  match lnorm F ntm e1, lnorm F ntm e2 with
  | Some l1, Some l2 => lword_eqb l1 l2
  | _, _ => false
  end.

Theorem nf_eq_l_sound {T : Type} (lenv : list label) (tenv : list T) (aenv : list (radj T)) (penv : list (rpadj T))
    (F : order) (HF : facts_ok lenv F) (ntm : nat) (Hntm : ntm <= List.length tenv) (e1 e2 : aexp) :
  nf_eq_l F ntm e1 e2 = true -> aeden lenv tenv aenv penv e1 = aeden lenv tenv aenv penv e2.
Proof.
  unfold nf_eq_l; destruct (lnorm F ntm e1) as [l1|] eqn:E1; [|discriminate].
  destruct (lnorm F ntm e2) as [l2|] eqn:E2; [|discriminate]; intros H.
  apply lword_eqb_eq in H; subst l2.
  rewrite <- (lnorm_sound lenv tenv aenv penv F HF ntm Hntm e1 l1 E1).
  exact (lnorm_sound lenv tenv aenv penv F HF ntm Hntm e2 l1 E2).
Qed.
