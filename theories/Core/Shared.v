(** * Normal forms with shared payloads

    Written out as a tree, a normal form can be exponentially larger than
    the expression: each term's payload holds everything that happens to
    its names afterwards, later terms with their payloads included (see
    [docs/normal-forms.md]).  Here a term's payload is stored as a
    *defined* payload atom: a table gives, for each defined atom, a
    payload word and the payload atom (or identity) it is applied over,
    and equal definitions share an atom.  Stored words are flat: every
    payload is the identity over an atom.

    The operations of the normaliser run unchanged on flat words, a
    defined atom being as opaque as any payload atom; [flatten] then names
    the payloads of the result.  The meaning of a definition table is an
    extension of the payload environment. *)

From Stdlib Require Import Arith List Lia Bool Sorted.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Unique Normal Complete.
Import ListNotations.

(** ** The table *)

(** [(w, b)]: the payload adjustment [w] over [b]. *)
Notation pdef := (word * option nat)%type.

Definition obeqb (b b' : option nat) : bool :=
  match b, b' with None, None => true | Some n, Some n' => Nat.eqb n n' | _, _ => false end.

Lemma obeqb_eq b b' : obeqb b b' = true -> b = b'.
Proof. destruct b, b'; cbn; try discriminate; [intros H; apply Nat.eqb_eq in H; subst|]; reflexivity. Qed.

Definition pdef_eqb (d d' : pdef) : bool := word_eqb (fst d) (fst d') && obeqb (snd d) (snd d').

Lemma pdef_eqb_eq d d' : pdef_eqb d d' = true -> d = d'.
Proof.
  destruct d as [w b], d' as [w' b']; unfold pdef_eqb; cbn [fst snd]; intros H; apply andb_true_iff in H as [H1 H2].
  apply (proj2 (proj2 (proj2 nf_eqb_eq))) in H1; apply obeqb_eq in H2; subst; reflexivity.
Qed.

(** The definitions, newest first, and what has been flattened already:
    [(β, p, b')] says [p] over the defined atom [β] is [b']. *)
Record sst := mk_sst { sdefs : list pdef; smemo : list (nat * word * option nat) }.

Definition is_id (w : word) : bool := match w with WEnd SNil => true | _ => false end.

Lemma is_id_eq w : is_id w = true -> w = WEnd SNil.
Proof. destruct w as [[|]|]; cbn; congruence. Qed.

Section Table.

(** The payload atoms of the expression are those below [np]; the defined
    atom [np + k] is the [k]-th definition made. *)
Variable np : nat.

Definition dget (ds : list pdef) (k : nat) : option pdef := nth_error ds (List.length ds - 1 - k).

Fixpoint dfind (ds : list pdef) (d : pdef) : option nat :=
  match ds with
  | [] => None
  | d' :: r => if pdef_eqb d d' then Some (List.length r) else dfind r d
  end.

(** The atom for [w] over [b]: [b] itself when [w] is the identity, the
    atom of an equal definition if there is one, else a new one. *)
Definition alloc (ds : list pdef) (w : word) (b : option nat) : list pdef * option nat :=
  if is_id w then (ds, b)
  else match dfind ds (w, b) with
       | Some k => (ds, Some (np + k))
       | None => ((w, b) :: ds, Some (np + List.length ds))
       end.

Fixpoint mlook (m : list (nat * word * option nat)) (β : nat) (p : word) : option (option nat) :=
  match m with
  | [] => None
  | (β', p', r) :: m => if Nat.eqb β β' && word_eqb p p' then Some r else mlook m β p
  end.

(** ** Flattening *)

Variable F : list (lexp * lexp).
Variable ntm : nat.

Section Fl.

(** Flattening the words inside. *)
Variable rec : sst -> word -> option (sst * word).

Definition fl_t (st : sst) (t : ntgt) : option (sst * ntgt) :=
  match t with
  | NVar _ _ => Some (st, t)
  | NBind u p b =>
      if is_id p then Some (st, t)
      else
        match rec st p with
        | None => None
        | Some (st1, p1) =>
            let direct :=
              let '(ds, b') := alloc (sdefs st1) p1 b in Some (mk_sst ds (smemo st1), NBind u (WEnd SNil) b') in
            match b with
            | None => direct
            | Some β =>
                if β <? np then direct
                else
                  match mlook (smemo st1) β p1 with
                  | Some b' => Some (st1, NBind u (WEnd SNil) b')
                  | None =>
                      match dget (sdefs st1) (β - np) with
                      | None => None
                      | Some (w0, b0) =>
                          match wcomp F ntm p1 w0 with
                          | None => None
                          | Some q0 =>
                              match pnormw F ntm b0 q0 with
                              | None => None
                              | Some q =>
                                  match rec st1 q with
                                  | None => None
                                  | Some (st2, q') =>
                                      let '(ds, b') := alloc (sdefs st2) q' b0 in
                                      Some (mk_sst ds ((β, p1, b') :: smemo st2), NBind u (WEnd SNil) b')
                                  end
                              end
                          end
                      end
                  end
            end
        end
  end.

Fixpoint fl_ts (st : sst) (ts : tlist) : option (sst * tlist) :=
  match ts with
  | TNil => Some (st, TNil)
  | TCons t r =>
      match fl_t st t with
      | Some (st1, t') => match fl_ts st1 r with Some (st2, r') => Some (st2, TCons t' r') | None => None end
      | None => None
      end
  end.

Fixpoint fl_s (st : sst) (s : seg) : option (sst * seg) :=
  match s with
  | SNil => Some (st, SNil)
  | SEnt h ts m r =>
      match fl_ts st ts with
      | Some (st1, ts') => match fl_s st1 r with Some (st2, r') => Some (st2, SEnt h ts' m r') | None => None end
      | None => None
      end
  end.

Fixpoint fl_w (st : sst) (w : word) : option (sst * word) :=
  match w with
  | WEnd s => match fl_s st s with Some (st1, s') => Some (st1, WEnd s') | None => None end
  | WAtom s L a w' =>
      match fl_s st s with
      | Some (st1, s') => match fl_w st1 w' with Some (st2, w'') => Some (st2, WAtom s' L a w'') | None => None end
      | None => None
      end
  end.

End Fl.

Fixpoint fl (fuel : nat) : sst -> word -> option (sst * word) :=
  match fuel with
  | 0 => fun _ _ => None
  | S f => fl_w (fl f)
  end.

(** Enough for the nesting of the definitions and of a result. *)
Definition flatten (st : sst) (w : word) : option (sst * word) :=
  fl (100 + 2 * List.length (sdefs st)) st w.

Definition flatten_t (st : sst) (t : ntgt) : option (sst * ntgt) :=
  fl_t (fl (100 + 2 * List.length (sdefs st))) st t.

(** ** The shared normaliser *)

Definition then_flatten (r : option word) (st : sst) : option (sst * word) :=
  match r with Some w => flatten st w | None => None end.

Fixpoint anorm_s (e : aexp) (st : sst) : option (sst * word) :=
  match e with
  | AId => Some (st, WEnd SNil)
  | AAtom n => Some (st, WAtom SNil [] n (WEnd SNil))
  | ACompose a b =>
      match anorm_s a st with
      | Some (st1, wa) =>
          match anorm_s b st1 with
          | Some (st2, wb) => then_flatten (wcomp F ntm wa wb) st2
          | None => None
          end
      | None => None
      end
  | AOuter h a =>
      match anorm_s a st with Some (st1, w) => then_flatten (wouter F ntm h w) st1 | None => None end
  | AInner h t a =>
      match tnorm_s t st with
      | Some (st1, t') =>
          match anorm_s a st1 with
          | Some (st2, w) => then_flatten (wpush F ntm h t' w) st2
          | None => None
          end
      | None => None
      end
  | ALift h a =>
      match anorm_s a st with Some (st1, w) => then_flatten (wlift F ntm h w) st1 | None => None end
  end
with tnorm_s (t : texp) (st : sst) : option (sst * ntgt) :=
  match t with
  | TVarE h i => Some (st, NVar h i)
  | TBindE u p =>
      if u <? ntm then
        match pnorm_e_s p st with
        | Some (st1, (w, b)) =>
            match pnormw F ntm b w with
            | Some w' => flatten_t st1 (NBind u w' b)
            | None => None
            end
        | None => None
        end
      else None
  | TShiftE h t =>
      match tnorm_s t st with
      | Some (st1, NVar h' i) =>
          match lcmp F h h' with
          | Some Eq => Some (st1, NVar h' (S i))
          | Some _ => Some (st1, NVar h' i)
          | None => None
          end
      | _ => None
      end
  end
with pnorm_e_s (p : pexp) (st : sst) : option (sst * (word * option nat)) :=
  match p with
  | PId => Some (st, (WEnd SNil, None))
  | PAtom n => Some (st, (WEnd SNil, Some n))
  | PComp a p =>
      match anorm_s a st with
      | Some (st1, wa) =>
          match pnorm_e_s p st1 with
          | Some (st2, (w, b)) =>
              match then_flatten (wcomp F ntm wa w) st2 with
              | Some (st3, w') => Some (st3, (w', b))
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | PShift h p =>
      match pnorm_e_s p st with
      | Some (st1, (w, b)) =>
          match then_flatten (wouter F ntm h w) st1 with
          | Some (st2, w') => Some (st2, (w', b))
          | None => None
          end
      | None => None
      end
  end.

(** The decision: normalised in one table, the two sides are the same
    stored word. *)
Definition nf_eq_s (e1 e2 : aexp) : bool :=
  match anorm_s e1 (mk_sst [] []) with
  | Some (st1, w1) =>
      match anorm_s e2 st1 with
      | Some (_, w2) => word_eqb w1 w2
      | None => false
      end
  | None => false
  end.

End Table.

(** ** Meaning *)

Section Sound.

Context {T : Type}.
Variable lenv : list label.
Variable tenv : list T.
Variable aenv : list (radj T).
Variable penv : list (rpadj T).
Variable labs : list lexp.
Variable F : list (lexp * lexp).
Hypothesis HF : facts_ok lenv F.
Variable ntm : nat.
Hypothesis Hntm : ntm <= List.length tenv.

Local Notation np := (List.length penv).
Local Notation tnf := (tnf lenv labs).
Local Notation tlnf := (tlnf lenv labs).
Local Notation snf := (snf lenv labs).
Local Notation wnf := (wnf lenv labs).
Local Notation rnf := (rnf lenv labs).
Local Notation sshape := (sshape lenv labs).
Local Notation wden := (wden lenv tenv aenv).
Local Notation tden := (tden lenv tenv aenv).
Local Notation tins := (tins lenv tenv aenv).
Local Notation sins := (sins lenv tenv aenv).
Local Notation sden := (sden lenv tenv aenv).

(** A larger scope. *)
Lemma nf_mono N N' : N <= N' ->
  (forall t, tnf N t -> tnf N' t) /\ (forall ts, tlnf N ts -> tlnf N' ts) /\ (forall s, snf N s -> snf N' s)
  /\ (forall w nm, wnf N nm w -> wnf N' nm w).
Proof.
  intros HN; apply nf_mind; cbn [Unique.tnf Unique.tlnf Unique.snf Unique.wnf].
  - intros h i H; exact H.
  - intros u w IH b [Hb Hw]; split; [destruct b; cbn in *; lia|apply IH, Hw].
  - intros _; exact I.
  - intros t IHt r IHr [Ht Hr]; split; [apply IHt, Ht|apply IHr, Hr].
  - intros _; exact I.
  - intros h ts IHts m r IHr [Hts Hr]; split; [apply IHts, Hts|apply IHr, Hr].
  - intros s IH nm [Hs Hn]; split; [exact Hs|apply IH, Hn].
  - intros s IHs L a w IHw nm [Hs [Hn [Ha Hr]]]; exact (conj Hs (conj (IHs Hn) (conj Ha Hr))).
Qed.

Lemma wnf_mono N N' nm w : N <= N' -> wnf N nm w -> wnf N' nm w.
Proof. intros HN; apply (proj2 (proj2 (proj2 (nf_mono N N' HN)))). Qed.

Lemma tnf_mono N N' t : N <= N' -> tnf N t -> tnf N' t.
Proof. intros HN; apply (proj1 (nf_mono N N' HN)). Qed.

(** Normal forms have distinct labels throughout. *)
Lemma nf_dist N :
  (forall t, tnf N t -> tdist lenv t) /\ (forall ts, tlnf N ts -> tldist lenv ts)
  /\ (forall s nm, sshape nm s -> snf N s -> sdistd lenv s) /\ (forall w nm, wnf N nm w -> wdist lenv w).
Proof.
  apply nf_mind; cbn [Unique.tnf Unique.tlnf Unique.snf Unique.wnf tdist tldist sdistd wdist].
  - intros; exact I.
  - intros u w IH b [_ Hw]; exact (IH _ Hw).
  - intros; exact I.
  - intros t IHt r IHr [Ht Hr]; split; [apply IHt, Ht|apply IHr, Hr].
  - intros; exact I.
  - intros h ts IHts m r IHr nm Hs [Hts Hr]; split; [|split; [apply IHts, Hts|]].
    + exact (oks_shape lenv labs _ (sshape_weak lenv labs nm _ Hs) h ts m r eq_refl).
    + exact (IHr nm (sshape_tail lenv labs nm h ts m r Hs) Hr).
  - intros s IH nm [Hs Hn]; exact (IH nm Hs Hn).
  - intros s IHs L a w IHw nm [Hs [Hn [_ Hr]]]; split; [exact (IHs false Hs Hn)|].
    exact (IHw nm (rnf_wnf lenv labs N nm w Hr)).
Qed.

Lemma wnf_dist N nm w : wnf N nm w -> wdist lenv w.
Proof. apply (proj2 (proj2 (proj2 (nf_dist N)))). Qed.

(** The meaning of a word depends only on the payload atoms in scope. *)
Section Agree.

Variable N : nat.
Variables P1 P2 : list (rpadj T).
Hypothesis Hag : forall n, n < N -> nth n P1 rpidentity = nth n P2 rpidentity.

Lemma bden_agree b : bok N b -> bden P1 b = bden P2 b.
Proof. destruct b as [n|]; cbn [bok bden]; [apply Hag|reflexivity]. Qed.

Lemma tden_unfold P u w b :
  tden P (NBind u w b)
  = match nth_error tenv u with Some x => RBind x (rpcompose (wden P w) (bden P b)) | None => RRename (mk_rvar None 0) end.
Proof. reflexivity. Qed.

Lemma tins_cons P h t r tail : tins P h (TCons t r) tail = rpush_inner h (tden P t) (tins P h r tail).
Proof. reflexivity. Qed.

Lemma sins_ent P h ts m r tail : sins P (SEnt h ts m r) tail = tins P (lden lenv h) ts (sins P r tail).
Proof. reflexivity. Qed.

Lemma den_agree :
  (forall t, tnf N t -> tden P1 t = tden P2 t)
  /\ (forall ts, tlnf N ts -> forall h tail, tins P1 h ts tail = tins P2 h ts tail)
  /\ (forall s, snf N s -> forall tail, sins P1 s tail = sins P2 s tail)
  /\ (forall w nm, wnf N nm w -> wden P1 w = wden P2 w).
Proof.
  apply nf_mind.
  - intros; reflexivity.
  - intros u w IH b [Hb Hw]; rewrite !tden_unfold, (IH _ Hw), (bden_agree b Hb); reflexivity.
  - intros; reflexivity.
  - intros t IHt r IHr [Ht Hr] h tail; rewrite !tins_cons, (IHt Ht), (IHr Hr); reflexivity.
  - intros; reflexivity.
  - intros h ts IHts m r IHr [Hts Hr] tail; rewrite !sins_ent, (IHr Hr), (IHts Hts); reflexivity.
  - intros s IH nm [_ Hn]; rewrite !wden_end; unfold Normalise.sden; apply IH, Hn.
  - intros s IHs L a w IHw nm [_ [Hn [_ Hr]]]; rewrite !wden_atom; unfold Normalise.sden.
    rewrite (IHs Hn), (IHw nm (rnf_wnf lenv labs N nm w Hr)); reflexivity.
Qed.

Lemma wden_agree nm w : wnf N nm w -> wden P1 w = wden P2 w.
Proof. apply (proj2 (proj2 (proj2 den_agree))). Qed.

Lemma tden_agree t : tnf N t -> tden P1 t = tden P2 t.
Proof. apply (proj1 den_agree). Qed.

Local Notation aeden := (aeden lenv tenv aenv).
Local Notation teden := (teden lenv tenv aenv).
Local Notation peden := (peden lenv tenv aenv).

Lemma aeden_compose P a b : aeden P (ACompose a b) = rcompose (aeden P a) (aeden P b).
Proof. reflexivity. Qed.
Lemma aeden_outer P h a : aeden P (AOuter h a) = rpush_outer (lden lenv h) (aeden P a).
Proof. reflexivity. Qed.
Lemma aeden_inner P h t a : aeden P (AInner h t a) = rpush_inner (lden lenv h) (teden P t) (aeden P a).
Proof. reflexivity. Qed.
Lemma aeden_lift P h a : aeden P (ALift h a) = rlift (lden lenv h) (aeden P a).
Proof. reflexivity. Qed.
Lemma teden_bind P u p :
  teden P (TBindE u p) = match nth_error tenv u with Some x => RBind x (peden P p) | None => RRename (mk_rvar None 0) end.
Proof. reflexivity. Qed.
Lemma teden_shift P h t :
  teden P (TShiftE h t) = match teden P t with RRename w => RRename (shift_rvar (mk_rvar (lden lenv h) 0) w) | r => r end.
Proof. reflexivity. Qed.
Lemma peden_comp P a p : peden P (PComp a p) = rpcompose (aeden P a) (peden P p).
Proof. reflexivity. Qed.
Lemma peden_shift P h p : peden P (PShift h p) = rpshift (lden lenv h) (peden P p).
Proof. reflexivity. Qed.

Lemma eden_agree :
  (forall e, ascope N e -> aeden P1 e = aeden P2 e)
  /\ (forall t, tscope N t -> teden P1 t = teden P2 t)
  /\ (forall p, pscope N p -> peden P1 p = peden P2 p).
Proof.
  apply exp_mind.
  - intros _; reflexivity.
  - intros n _; reflexivity.
  - intros a IHa b IHb [Ha Hb]; rewrite !aeden_compose, (IHa Ha), (IHb Hb); reflexivity.
  - intros h a IH Ha; rewrite !aeden_outer, (IH Ha); reflexivity.
  - intros h t IHt a IHa [Ht Ha]; rewrite !aeden_inner, (IHt Ht), (IHa Ha); reflexivity.
  - intros h a IH Ha; rewrite !aeden_lift, (IH Ha); reflexivity.
  - intros h i _; reflexivity.
  - intros u p IH Hp; rewrite !teden_bind, (IH Hp); reflexivity.
  - intros h t IH Ht; rewrite !teden_shift, (IH Ht); reflexivity.
  - intros _; reflexivity.
  - intros n Hn; apply Hag, Hn.
  - intros a IHa p IHp [Ha Hp]; rewrite !peden_comp, (IHa Ha), (IHp Hp); reflexivity.
  - intros h p IH Hp; rewrite !peden_shift, (IH Hp); reflexivity.
Qed.

End Agree.

(** *** The table

    Definitions extend the payload environment, oldest first. *)

Fixpoint dden (ds : list pdef) : list (rpadj T) :=
  match ds with
  | [] => []
  | (w, b) :: r => dden r ++ [rpcompose (wden (penv ++ dden r) w) (bden penv b)]
  end.

Definition ext (ds : list pdef) : list (rpadj T) := penv ++ dden ds.

Lemma dden_length ds : List.length (dden ds) = List.length ds.
Proof. induction ds as [|[w b] r IH]; cbn [dden List.length]; [reflexivity|rewrite length_app, IH; cbn; lia]. Qed.

Lemma dden_app new ds : exists X, dden (new ++ ds) = dden ds ++ X.
Proof.
  induction new as [|[w b] r [X IH]]; [exists []; rewrite app_nil_r; reflexivity|].
  cbn [app dden]; rewrite IH; eexists; rewrite <- app_assoc; reflexivity.
Qed.

Lemma ext_agree new ds n : n < np + List.length ds -> nth n (ext (new ++ ds)) rpidentity = nth n (ext ds) rpidentity.
Proof.
  intros Hn; unfold ext; destruct (dden_app new ds) as [X ->]; rewrite app_assoc, app_nth1; [reflexivity|].
  rewrite length_app, dden_length; exact Hn.
Qed.

Lemma ext_real ds n : n < np -> nth n (ext ds) rpidentity = nth n penv rpidentity.
Proof. intros; unfold ext; apply app_nth1; assumption. Qed.

Lemma bok_mono N N' b : N <= N' -> bok N b -> bok N' b.
Proof. destruct b; cbn; [lia|auto]. Qed.

Lemma wden_ext new ds nm w : wnf (np + List.length ds) nm w -> wden (ext (new ++ ds)) w = wden (ext ds) w.
Proof. apply wden_agree; intros n Hn; apply ext_agree, Hn. Qed.

Lemma tden_ext new ds t : tnf (np + List.length ds) t -> tden (ext (new ++ ds)) t = tden (ext ds) t.
Proof. apply tden_agree; intros n Hn; apply ext_agree, Hn. Qed.

Lemma bden_ext new ds b : bok (np + List.length ds) b -> bden (ext (new ++ ds)) b = bden (ext ds) b.
Proof. apply bden_agree; intros n Hn; apply ext_agree, Hn. Qed.

Lemma bden_real ds b : bok np b -> bden (ext ds) b = bden penv b.
Proof. destruct b as [n|]; cbn [bok bden]; [apply ext_real|reflexivity]. Qed.

Definition bnm (b : option nat) : bool := match b with None => true | Some _ => false end.

(** Each definition is a normal payload word over the definitions before
    it, applied over a payload atom of the expression or the identity. *)
Fixpoint dok (ds : list pdef) : Prop :=
  match ds with
  | [] => True
  | (w, b) :: r => wnf (np + List.length r) (bnm b) w /\ bok np b /\ dok r
  end.

Lemma dget_top d r : dget (d :: r) (List.length r) = Some d.
Proof. unfold dget; cbn [List.length]; replace (S (List.length r) - 1 - List.length r) with 0 by lia; reflexivity. Qed.

Lemma dget_cons d r k : k < List.length r -> dget (d :: r) k = dget r k.
Proof.
  intros Hk; unfold dget; cbn [List.length].
  replace (S (List.length r) - 1 - k) with (S (List.length r - 1 - k)) by lia; reflexivity.
Qed.

Lemma dlevel ds : dok ds -> forall k w b, k < List.length ds -> dget ds k = Some (w, b) ->
  wnf (np + k) (bnm b) w /\ bok np b
  /\ nth (np + k) (ext ds) rpidentity = rpcompose (wden (ext ds) w) (bden penv b).
Proof.
  induction ds as [|[w' b'] r IH]; [cbn; lia|]; intros [Hw [Hb Hr]] k w b Hk E; cbn [List.length] in Hk.
  destruct (Nat.eq_dec k (List.length r)) as [->|Hne].
  - rewrite dget_top in E; injection E as -> ->; split; [exact Hw|split; [exact Hb|]].
    assert (Ew : wden (ext ((w, b) :: r)) w = wden (ext r) w) by exact (wden_ext [(w, b)] r _ w Hw).
    rewrite Ew; unfold ext; cbn [app dden]; rewrite app_assoc, app_nth2 by (rewrite length_app, dden_length; lia).
    rewrite length_app, dden_length, Nat.sub_diag; reflexivity.
  - rewrite dget_cons in E by lia; destruct (IH Hr k w b ltac:(lia) E) as [H1 [H2 H3]].
    split; [exact H1|split; [exact H2|]].
    assert (Ew : wden (ext ((w', b') :: r)) w = wden (ext r) w)
      by (apply (wden_ext [(w', b')] r (bnm b) w), (wnf_mono (np + k)); [lia|exact H1]).
    rewrite Ew; change ((w', b') :: r) with ([(w', b')] ++ r); rewrite ext_agree by lia; exact H3.
Qed.

Lemma dfind_get ds d k : dfind ds d = Some k -> k < List.length ds /\ dget ds k = Some d.
Proof.
  induction ds as [|d' r IH]; cbn [dfind]; [discriminate|]; destruct (pdef_eqb d d') eqn:E.
  - intros H; injection H as <-; apply pdef_eqb_eq in E; subst; split; [cbn; lia|apply dget_top].
  - intros H; destruct (IH H) as [H1 H2]; split; [cbn; lia|rewrite dget_cons by exact H1; exact H2].
Qed.

Lemma alloc_spec ds w b ds' b' :
  dok ds -> wnf (np + List.length ds) (bnm b) w -> bok np b -> alloc np ds w b = (ds', b') ->
  dok ds' /\ (exists new, ds' = new ++ ds) /\ bok (np + List.length ds') b'
  /\ bden (ext ds') b' = rpcompose (wden (ext ds) w) (bden penv b).
Proof.
  intros Hd Hw Hb; unfold alloc; destruct (is_id w) eqn:Ei.
  - intros H; injection H as <- <-; apply is_id_eq in Ei; subst w.
    split; [exact Hd|split; [exists []; reflexivity|split; [apply (bok_mono np); [lia|exact Hb]|]]].
    rewrite wden_id, rpcompose_identity; apply bden_real, Hb.
  - destruct (dfind ds (w, b)) as [k|] eqn:Ef; intros H; injection H as <- <-.
    + destruct (dfind_get _ _ _ Ef) as [Hk Hg]; destruct (dlevel ds Hd k w b Hk Hg) as [_ [_ H3]].
      split; [exact Hd|split; [exists []; reflexivity|split; [cbn; lia|exact H3]]].
    + assert (Hd' : dok ((w, b) :: ds)) by exact (conj Hw (conj Hb Hd)).
      split; [exact Hd'|split; [exists [(w, b)]; reflexivity|split; [cbn [bok List.length]; lia|]]].
      destruct (dlevel _ Hd' (List.length ds) w b ltac:(cbn; lia) (dget_top _ _)) as [_ [_ H3]].
      assert (Ew : wden (ext ((w, b) :: ds)) w = wden (ext ds) w) by exact (wden_ext [(w, b)] ds _ w Hw).
      cbn [bden]; rewrite H3, Ew; reflexivity.
Qed.

(** *** Flattening keeps the meaning *)

Definition extends (ds ds' : list pdef) : Prop := exists new, ds' = new ++ ds.

Lemma extends_refl ds : extends ds ds.
Proof. exists []; reflexivity. Qed.

Lemma extends_trans a b c : extends a b -> extends b c -> extends a c.
Proof. intros [n1 ->] [n2 ->]; exists (n2 ++ n1); rewrite app_assoc; reflexivity. Qed.

Lemma extends_len ds ds' : extends ds ds' -> List.length ds <= List.length ds'.
Proof. intros [n ->]; rewrite length_app; lia. Qed.

Lemma wden_up ds ds' nm w : extends ds ds' -> wnf (np + List.length ds) nm w -> wden (ext ds') w = wden (ext ds) w.
Proof. intros [new ->]; apply wden_ext. Qed.

Lemma tden_up ds ds' t : extends ds ds' -> tnf (np + List.length ds) t -> tden (ext ds') t = tden (ext ds) t.
Proof. intros [new ->]; apply tden_ext. Qed.

Lemma bden_up ds ds' b : extends ds ds' -> bok (np + List.length ds) b -> bden (ext ds') b = bden (ext ds) b.
Proof. intros [new ->]; apply bden_ext. Qed.

Lemma tins_up ds ds' ts : extends ds ds' -> tlnf (np + List.length ds) ts ->
  forall h tail, tins (ext ds') h ts tail = tins (ext ds) h ts tail.
Proof.
  intros [new ->] Hts; apply (proj1 (proj2 (den_agree (np + List.length ds) _ _ (fun n Hn => ext_agree new ds n Hn)))), Hts.
Qed.

Lemma wnf_up ds ds' nm w : extends ds ds' -> wnf (np + List.length ds) nm w -> wnf (np + List.length ds') nm w.
Proof. intros Hx; apply wnf_mono; pose proof (extends_len _ _ Hx); lia. Qed.

Lemma tnf_up ds ds' t : extends ds ds' -> tnf (np + List.length ds) t -> tnf (np + List.length ds') t.
Proof. intros Hx; apply tnf_mono; pose proof (extends_len _ _ Hx); lia. Qed.

Lemma tlnf_up ds ds' ts : extends ds ds' -> tlnf (np + List.length ds) ts -> tlnf (np + List.length ds') ts.
Proof. intros Hx; pose proof (extends_len _ _ Hx) as Hl; apply (proj1 (proj2 (nf_mono (np + List.length ds) (np + List.length ds') ltac:(lia)))). Qed.

Lemma snf_up ds ds' s : extends ds ds' -> snf (np + List.length ds) s -> snf (np + List.length ds') s.
Proof. intros Hx; pose proof (extends_len _ _ Hx) as Hl; apply (proj1 (proj2 (proj2 (nf_mono (np + List.length ds) (np + List.length ds') ltac:(lia))))). Qed.

(** What has been remembered stays true. *)
Definition mok (ds : list pdef) (e : nat * word * option nat) : Prop :=
  let '(β, p, b') := e in
  wnf (np + List.length ds) false p /\ bok (np + List.length ds) (Some β) /\ bok (np + List.length ds) b'
  /\ bden (ext ds) b' = rpcompose (wden (ext ds) p) (bden (ext ds) (Some β)).

Lemma mok_up ds ds' e : extends ds ds' -> mok ds e -> mok ds' e.
Proof.
  intros Hx; destruct e as [[β p] b']; intros [H1 [H2 [H3 H4]]]; pose proof (extends_len _ _ Hx) as Hl.
  split; [exact (wnf_up _ _ _ _ Hx H1)|split; [apply (bok_mono (np + List.length ds)); [lia|exact H2]|split; [apply (bok_mono (np + List.length ds)); [lia|exact H3]|]]].
  rewrite (bden_up _ _ _ Hx H3), (wden_up _ _ _ _ Hx H1), (bden_up _ _ _ Hx H2); exact H4.
Qed.

Definition inv (st : sst) : Prop := dok (sdefs st) /\ Forall (mok (sdefs st)) (smemo st).

Lemma mlook_in m β p r : mlook m β p = Some r -> In (β, p, r) m.
Proof.
  induction m as [|[[β' p'] r'] m IH]; cbn [mlook]; [discriminate|].
  destruct (Nat.eqb β β' && word_eqb p p') eqn:E.
  - intros H; injection H as <-; apply andb_true_iff in E as [E1 E2]; apply Nat.eqb_eq in E1.
    apply (proj2 (proj2 (proj2 nf_eqb_eq))) in E2; subst; left; reflexivity.
  - intros H; right; exact (IH H).
Qed.

Definition flspec (f : sst -> word -> option (sst * word)) : Prop :=
  forall st w st' w' nm, inv st -> wnf (np + List.length (sdefs st)) nm w -> f st w = Some (st', w') ->
    inv st' /\ extends (sdefs st) (sdefs st') /\ wnf (np + List.length (sdefs st')) nm w'
    /\ wden (ext (sdefs st')) w' = wden (ext (sdefs st')) w.

(** Variables are left alone, and terms stay terms. *)
Definition tsim (t t' : ntgt) : Prop :=
  match t, t' with NVar _ _, NVar _ _ => t = t' | NBind _ _ _, NBind _ _ _ => True | _, _ => False end.

Fixpoint tlsim (ts ts' : tlist) : Prop :=
  match ts, ts' with TNil, TNil => True | TCons t r, TCons t' r' => tsim t t' /\ tlsim r r' | _, _ => False end.

Fixpoint ssim (s s' : seg) : Prop :=
  match s, s' with
  | SNil, SNil => True
  | SEnt h ts m r, SEnt h' ts' m' r' => h = h' /\ m = m' /\ tlsim ts ts' /\ ssim r r'
  | _, _ => False
  end.

Lemma tden_flat P u p b b' :
  bden P b' = rpcompose (wden P p) (bden P b) -> tden P (NBind u (WEnd SNil) b') = tden P (NBind u p b).
Proof. intros H; rewrite !tden_unfold, wden_id, rpcompose_identity, H; reflexivity. Qed.

Lemma wnf_id N nm : wnf N nm (WEnd SNil).
Proof. split; [split; constructor|exact I]. Qed.

Lemma flat_tnf N u b : bok N b -> tnf N (NBind u (WEnd SNil) b).
Proof. intros Hb; split; [exact Hb|apply wnf_id]. Qed.

Lemma fl_t_spec rec : flspec rec -> forall st t st' t',
  inv st -> tnf (np + List.length (sdefs st)) t -> fl_t np F ntm rec st t = Some (st', t') ->
  inv st' /\ extends (sdefs st) (sdefs st') /\ tnf (np + List.length (sdefs st')) t' /\ tsim t t'
  /\ tden (ext (sdefs st')) t' = tden (ext (sdefs st')) t.
Proof.
  intros Hrec st t st' t' Hi Ht; destruct t as [h i|u p b]; cbn [fl_t].
  - intros H; injection H as <- <-; exact (conj Hi (conj (extends_refl _) (conj Ht (conj eq_refl eq_refl)))).
  - destruct Ht as [Hb Hp]; destruct (is_id p) eqn:Ei.
    { intros H; injection H as <- <-; exact (conj Hi (conj (extends_refl _) (conj (conj Hb Hp) (conj I eq_refl)))). }
    destruct (rec st p) as [[st1 p1]|] eqn:Er; [|discriminate].
    destruct (Hrec _ _ _ _ _ Hi Hp Er) as [Hi1 [Hx1 [Hp1 Ep1]]].
    pose proof (extends_len _ _ Hx1) as Hl1.
    assert (Hdirect : bok np b -> forall ds b', alloc np (sdefs st1) p1 b = (ds, b') ->
       inv (mk_sst ds (smemo st1)) /\ extends (sdefs st) ds /\ tnf (np + List.length ds) (NBind u (WEnd SNil) b')
       /\ tsim (NBind u p b) (NBind u (WEnd SNil) b')
       /\ tden (ext ds) (NBind u (WEnd SNil) b') = tden (ext ds) (NBind u p b)).
    { intros Hbr ds b' Ea.
      destruct (alloc_spec _ _ _ _ _ (proj1 Hi1) Hp1 Hbr Ea) as [Hd [Hx [Hb' Eb']]].
      split; [split; [exact Hd|eapply Forall_impl; [|exact (proj2 Hi1)]; intros e; apply mok_up, Hx]|].
      split; [exact (extends_trans _ _ _ Hx1 Hx)|split; [apply flat_tnf, Hb'|split; [exact I|]]].
      apply tden_flat; rewrite Eb', Ep1, (wden_up _ _ _ _ Hx1 Hp), (wden_up _ _ _ _ (extends_trans _ _ _ Hx1 Hx) Hp).
      rewrite (bden_real ds b Hbr); reflexivity. }
    destruct b as [β|].
    2:{ destruct (alloc np (sdefs st1) p1 None) as [ds b'] eqn:Ea; intros H; injection H as <- <-.
        exact (Hdirect I ds b' eq_refl). }
    destruct (Nat.ltb_spec β np) as [Hβ|Hβ].
    { destruct (alloc np (sdefs st1) p1 (Some β)) as [ds b'] eqn:Ea; intros H; injection H as <- <-.
      exact (Hdirect Hβ ds b' eq_refl). }
    destruct (mlook (smemo st1) β p1) as [b'|] eqn:Em.
    { intros H; injection H as <- <-.
      pose proof (proj1 (Forall_forall _ _) (proj2 Hi1) _ (mlook_in _ _ _ _ Em)) as [M1 [M2 [M3 M4]]].
      split; [exact Hi1|split; [exact Hx1|split; [apply flat_tnf, M3|split; [exact I|]]]].
      apply tden_flat; rewrite M4, Ep1; reflexivity. }
    destruct (dget (sdefs st1) (β - np)) as [[w0 b0]|] eqn:Eg; [|discriminate].
    assert (Hk : β - np < List.length (sdefs st1)) by (cbn [bok] in Hb; lia).
    destruct (dlevel _ (proj1 Hi1) _ _ _ Hk Eg) as [Hw0 [Hb0 Eβ]].
    replace (np + (β - np)) with β in Eβ, Hw0 by lia.
    destruct (wcomp F ntm p1 w0) as [q0|] eqn:Ec; [|discriminate].
    destruct (pnormw F ntm b0 q0) as [q|] eqn:Eq; [|discriminate].
    destruct (rec st1 q) as [[st2 q']|] eqn:Er2; [|discriminate].
    destruct (alloc np (sdefs st2) q' b0) as [ds3 b'] eqn:Ea; intros H; injection H as <- <-; cbn [sdefs smemo].
    assert (Hw0' : wnf (np + List.length (sdefs st1)) false w0).
    { apply (wnf_false lenv labs _ (bnm b0)), (wnf_mono β); [cbn [bok] in Hb; lia|exact Hw0]. }
    pose proof (wcomp_normal lenv labs _ F HF ntm p1 w0 q0 Hp1 Hw0' Ec) as Hq0.
    pose proof (pnormw_normal lenv labs _ F HF ntm b0 q0 q Hq0 Eq) as Hq.
    destruct (wcomp_sound lenv tenv aenv (ext (sdefs st1)) F HF ntm Hntm p1 w0 q0
                (wnf_dist _ _ _ Hp1) (wnf_dist _ _ _ Hw0') Ec) as [Hdq0 Eq0].
    destruct (pnormw_sound lenv tenv aenv (ext (sdefs st1)) F HF ntm Hntm b0 q0 q Hdq0 Eq) as [_ Eqq].
    destruct (Hrec _ _ _ _ _ Hi1 Hq Er2) as [Hi2 [Hx2 [Hq' Eq']]].
    destruct (alloc_spec _ _ _ _ _ (proj1 Hi2) Hq' Hb0 Ea) as [Hd3 [Hx3 [Hb' Eb']]].
    assert (Hx13 : extends (sdefs st1) ds3) by exact (extends_trans _ _ _ Hx2 Hx3).
    pose proof (extends_len _ _ Hx13) as Hl3.
    assert (E3 : bden (ext ds3) b' = rpcompose (wden (ext ds3) p1) (bden (ext ds3) (Some β))).
    { rewrite Eb', Eq', (wden_up _ _ _ _ Hx2 Hq).
      rewrite <- (bden_real (sdefs st1) b0 Hb0), Eqq, Eq0, <- rpcompose_compose, (bden_real _ b0 Hb0).
      rewrite (wden_up _ _ _ _ Hx13 Hp1); f_equal; cbn [bden]; rewrite <- Eβ.
      destruct Hx13 as [new ->]; symmetry; apply ext_agree; cbn [bok] in Hb; lia. }
    split.
    { split; [exact Hd3|constructor].
      - refine (conj (wnf_up _ _ _ _ Hx13 Hp1) (conj _ (conj Hb' E3))); cbn [bok sdefs] in *; lia.
      - eapply Forall_impl; [|exact (proj2 Hi2)]; intros e; apply mok_up, Hx3. }
    split; [exact (extends_trans _ _ _ Hx1 Hx13)|split; [apply flat_tnf, Hb'|split; [exact I|]]].
    apply tden_flat; rewrite E3, (wden_up _ _ _ _ Hx13 Hp1), Ep1, (wden_up _ _ _ _ Hx1 Hp).
    rewrite (wden_up _ _ _ _ (extends_trans _ _ _ Hx1 Hx13) Hp); reflexivity.
Qed.

(** The shape of a segment does not look inside its terms. *)
Lemma tsim_refl t : tsim t t.
Proof. destruct t; cbn; auto. Qed.

Lemma tlsim_list ts : forall ts', tlsim ts ts' -> Forall2 tsim (tl_list ts) (tl_list ts').
Proof.
  induction ts as [|t r IH] using tlist_spine; intros [|t' r']; cbn [tlsim tl_list]; try contradiction; [constructor|].
  intros [H1 H2]; constructor; [exact H1|exact (IH _ H2)].
Qed.

Lemma last_sim xs : forall xs' d, Forall2 tsim xs xs' -> tsim (last xs d) (last xs' d).
Proof.
  induction xs as [|x xs IH]; intros xs' d H; inversion H as [|a b l l' Hab Hl]; subst; [apply tsim_refl|].
  destruct xs as [|y ys]; inversion Hl as [|a2 b2 l2 l2' Hab2 Hl2]; subst; [exact Hab|].
  exact (IH _ d Hl).
Qed.

Lemma trimmed_sim h xs xs' m : Forall2 tsim xs xs' -> trimmed h xs m -> trimmed h xs' m.
Proof.
  intros H; pose proof (last_sim _ _ (NVar LNone 0) H) as Hl; unfold trimmed.
  destruct H as [|a b l l' Hab Hr]; [auto|].
  remember (last (a :: l) (NVar LNone 0)) as x; remember (last (b :: l') (NVar LNone 0)) as x'.
  destruct x as [g j|? ? ?], x' as [g' j'|? ? ?]; cbn [tsim] in Hl; try contradiction; [|destruct m; auto].
  injection Hl as <- <-; auto.
Qed.

Lemma sshape_sim nm s : forall s', ssim s s' -> sshape nm s ->
  sshape nm s' /\ (forall l, Forall (fun e => olabel_lt l (ekey lenv e)) (sents s) -> Forall (fun e => olabel_lt l (ekey lenv e)) (sents s')).
Proof.
  induction s as [|h ts m r IH] using seg_spine; intros [|h' ts' m' r']; cbn [ssim]; try contradiction.
  { intros _ H; split; [exact H|auto]. }
  intros [<- [<- [Hts Hr]]] [Hs Ho]; cbn [sents] in *.
  inversion Hs as [|e l Hsr Hall]; inversion Ho as [|e' l' He Hor]; subst.
  destruct (IH _ Hr (conj Hsr Hor)) as [[Hs' Ho'] Hk]; pose proof (tlsim_list _ _ Hts) as H2.
  split.
  - split; [constructor; [exact Hs'|exact (Hk _ Hall)]|constructor; [|exact Ho']].
    destruct He as [A [B [C D]]]; refine (conj A (conj (trimmed_sim _ _ _ _ H2 B) (conj _ D))).
    destruct C as [C|C]; [left|right; exact C]; intros E; rewrite E in H2; apply C; destruct (tl_list ts); [reflexivity|inversion H2].
  - intros l Hl; inversion Hl as [|e l0 H1 H3]; subst; constructor; [exact H1|exact (Hk _ H3)].
Qed.

Lemma souts_sim s : forall s' (tail : radj T), ssim s s' -> souts lenv s' tail = souts lenv s tail.
Proof.
  induction s as [|h ts m r IH] using seg_spine; intros [|h' ts' m' r'] tail; cbn [ssim]; try contradiction; [reflexivity|].
  intros [<- [<- [_ Hr]]]; cbn [souts]; rewrite (IH _ tail Hr); reflexivity.
Qed.

Lemma sins_up ds ds' s : extends ds ds' -> snf (np + List.length ds) s ->
  forall tail, sins (ext ds') s tail = sins (ext ds) s tail.
Proof.
  intros [new ->] Hs; apply (proj1 (proj2 (proj2 (den_agree (np + List.length ds) _ _ (fun n Hn => ext_agree new ds n Hn))))), Hs.
Qed.

Section FlSpec.

Variable rec : sst -> word -> option (sst * word).
Hypothesis Hrec : flspec rec.

Lemma fl_ts_spec ts : forall st st' ts',
  inv st -> tlnf (np + List.length (sdefs st)) ts -> fl_ts np F ntm rec st ts = Some (st', ts') ->
  inv st' /\ extends (sdefs st) (sdefs st') /\ tlnf (np + List.length (sdefs st')) ts' /\ tlsim ts ts'
  /\ forall h tail, tins (ext (sdefs st')) h ts' tail = tins (ext (sdefs st')) h ts tail.
Proof.
  induction ts as [|t r IH] using tlist_spine; intros st st' ts' Hi Hts; cbn [fl_ts].
  { intros H; injection H as <- <-; exact (conj Hi (conj (extends_refl _) (conj I (conj I (fun _ _ => eq_refl))))). }
  destruct Hts as [Ht Hr]; destruct (fl_t np F ntm rec st t) as [[st1 t']|] eqn:E1; [|discriminate].
  destruct (fl_t_spec rec Hrec _ _ _ _ Hi Ht E1) as [Hi1 [Hx1 [Ht' [Hsim Et]]]].
  destruct (fl_ts np F ntm rec st1 r) as [[st2 r']|] eqn:E2; [|discriminate]; intros H; injection H as <- <-.
  destruct (IH _ _ _ Hi1 (tlnf_up _ _ _ Hx1 Hr) E2) as [Hi2 [Hx2 [Hr' [Hsr Er]]]].
  split; [exact Hi2|split; [exact (extends_trans _ _ _ Hx1 Hx2)|split; [exact (conj (tnf_up _ _ _ Hx2 Ht') Hr')|split; [exact (conj Hsim Hsr)|]]]].
  intros h tail; rewrite !tins_cons, Er, (tden_up _ _ _ Hx2 Ht'), Et, <- (tden_up _ _ _ Hx2 (tnf_up _ _ _ Hx1 Ht)); reflexivity.
Qed.

Lemma fl_s_spec s : forall st st' s',
  inv st -> snf (np + List.length (sdefs st)) s -> fl_s np F ntm rec st s = Some (st', s') ->
  inv st' /\ extends (sdefs st) (sdefs st') /\ snf (np + List.length (sdefs st')) s' /\ ssim s s'
  /\ forall tail, sins (ext (sdefs st')) s' tail = sins (ext (sdefs st')) s tail.
Proof.
  induction s as [|h ts m r IH] using seg_spine; intros st st' s' Hi Hs; cbn [fl_s].
  { intros H; injection H as <- <-; exact (conj Hi (conj (extends_refl _) (conj I (conj I (fun _ => eq_refl))))). }
  destruct Hs as [Hts Hr]; destruct (fl_ts np F ntm rec st ts) as [[st1 ts1]|] eqn:E1; [|discriminate].
  destruct (fl_ts_spec _ _ _ _ Hi Hts E1) as [Hi1 [Hx1 [Hts' [Hsim Et]]]].
  destruct (fl_s np F ntm rec st1 r) as [[st2 r']|] eqn:E2; [|discriminate]; intros H; injection H as <- <-.
  destruct (IH _ _ _ Hi1 (snf_up _ _ _ Hx1 Hr) E2) as [Hi2 [Hx2 [Hr' [Hsr Er]]]].
  split; [exact Hi2|split; [exact (extends_trans _ _ _ Hx1 Hx2)|split; [exact (conj (tlnf_up _ _ _ Hx2 Hts') Hr')|split; [exact (conj eq_refl (conj eq_refl (conj Hsim Hsr)))|]]]].
  intros tail; rewrite !sins_ent, Er, (tins_up _ _ _ Hx2 Hts'), Et, <- (tins_up _ _ _ Hx2 (tlnf_up _ _ _ Hx1 Hts)); reflexivity.
Qed.

Lemma sden_flat st st' s s' :
  inv st -> snf (np + List.length (sdefs st)) s -> fl_s np F ntm rec st s = Some (st', s') ->
  sden (ext (sdefs st')) s' = sden (ext (sdefs st')) s.
Proof.
  intros Hi Hs E; destruct (fl_s_spec _ _ _ _ Hi Hs E) as [_ [_ [_ [Hsim Es]]]].
  unfold Normalise.sden; rewrite Es, (souts_sim _ _ _ Hsim); reflexivity.
Qed.

(** Renamings have nothing to flatten. *)
Lemma fl_ts_ren st ts : Forall (ren_target labs) (tl_list ts) -> fl_ts np F ntm rec st ts = Some (st, ts).
Proof.
  induction ts as [|t r IH] using tlist_spine; cbn [fl_ts tl_list]; [reflexivity|]; intros H.
  inversion H as [|a l Ha Hl]; subst; destruct t as [g j|? ? ?]; [|contradiction]; cbn [fl_t]; rewrite (IH Hl); reflexivity.
Qed.

Lemma fl_s_ren st s : sren labs s -> fl_s np F ntm rec st s = Some (st, s).
Proof.
  unfold sren; induction s as [|h ts m r IH] using seg_spine; cbn [fl_s]; [reflexivity|].
  rewrite stgts_cons, Forall_app; intros [H1 H2]; rewrite (fl_ts_ren _ _ H1), (IH H2); reflexivity.
Qed.

Lemma fl_w_ren nm w : forall st, rnf nm w -> fl_w np F ntm rec st w = Some (st, w).
Proof.
  induction w as [s|s L a w IH]; intros st; cbn [Unique.rnf fl_w].
  - intros [_ H]; rewrite (fl_s_ren _ _ H); reflexivity.
  - intros [_ [H [_ Hr]]]; rewrite (fl_s_ren _ _ H), (IH _ Hr); reflexivity.
Qed.

Lemma fl_w_spec : flspec (fl_w np F ntm rec).
Proof.
  intros st w st' w' nm Hi; destruct w as [s|s L a w]; cbn [Unique.wnf fl_w].
  - intros [Hs Hn]; destruct (fl_s np F ntm rec st s) as [[st1 s1]|] eqn:E; [|discriminate]; intros H; injection H as <- <-.
    destruct (fl_s_spec _ _ _ _ Hi Hn E) as [Hi1 [Hx1 [Hn1 [Hsim _]]]].
    refine (conj Hi1 (conj Hx1 (conj (conj (proj1 (sshape_sim _ _ _ Hsim Hs)) Hn1) _))).
    rewrite !wden_end; exact (sden_flat _ _ _ _ Hi Hn E).
  - intros [Hs [Hn [Ha Hr]]]; destruct (fl_s np F ntm rec st s) as [[st1 s1]|] eqn:E; [|discriminate].
    rewrite (fl_w_ren _ _ _ Hr); intros H; injection H as <- <-.
    destruct (fl_s_spec _ _ _ _ Hi Hn E) as [Hi1 [Hx1 [Hn1 [Hsim _]]]].
    refine (conj Hi1 (conj Hx1 (conj (conj (proj1 (sshape_sim _ _ _ Hsim Hs)) (conj Hn1 (conj Ha Hr))) _))).
    rewrite !wden_atom, (sden_flat _ _ _ _ Hi Hn E); reflexivity.
Qed.

End FlSpec.

Lemma fl_spec fuel : flspec (fl np F ntm fuel).
Proof.
  induction fuel as [|f IH]; [intros st w st' w' nm _ _ H; discriminate|exact (fl_w_spec _ IH)].
Qed.

Lemma flatten_spec : flspec (flatten np F ntm).
Proof. intros st; apply fl_spec. Qed.

Lemma flatten_t_spec st t st' t' :
  inv st -> tnf (np + List.length (sdefs st)) t -> flatten_t np F ntm st t = Some (st', t') ->
  inv st' /\ extends (sdefs st) (sdefs st') /\ tnf (np + List.length (sdefs st')) t'
  /\ tden (ext (sdefs st')) t' = tden (ext (sdefs st')) t.
Proof.
  intros Hi Ht E; destruct (fl_t_spec _ (fl_spec _) _ _ _ _ Hi Ht E) as [H1 [H2 [H3 [_ H4]]]]; auto.
Qed.

(** *** The shared normaliser is sound *)

Local Notation anorm_s := (anorm_s np F ntm).
Local Notation tnorm_s := (tnorm_s np F ntm).
Local Notation pnorm_e_s := (pnorm_e_s np F ntm).
Local Notation then_flatten := (then_flatten np F ntm).
Local Notation aeden := (aeden lenv tenv aenv).
Local Notation teden := (teden lenv tenv aenv).
Local Notation peden := (peden lenv tenv aenv).

Lemma anorm_s_compose a b st :
  anorm_s (ACompose a b) st
  = match anorm_s a st with
    | Some (st1, wa) =>
        match anorm_s b st1 with Some (st2, wb) => then_flatten (wcomp F ntm wa wb) st2 | None => None end
    | None => None
    end.
Proof. reflexivity. Qed.

Lemma anorm_s_outer h a st :
  anorm_s (AOuter h a) st = match anorm_s a st with Some (st1, w) => then_flatten (wouter F ntm h w) st1 | None => None end.
Proof. reflexivity. Qed.

Lemma anorm_s_inner h t a st :
  anorm_s (AInner h t a) st
  = match tnorm_s t st with
    | Some (st1, t') =>
        match anorm_s a st1 with Some (st2, w) => then_flatten (wpush F ntm h t' w) st2 | None => None end
    | None => None
    end.
Proof. reflexivity. Qed.

Lemma anorm_s_lift h a st :
  anorm_s (ALift h a) st = match anorm_s a st with Some (st1, w) => then_flatten (wlift F ntm h w) st1 | None => None end.
Proof. reflexivity. Qed.

Lemma tnorm_s_bind u p st :
  tnorm_s (TBindE u p) st
  = if u <? ntm then
      match pnorm_e_s p st with
      | Some (st1, (w, b)) =>
          match pnormw F ntm b w with Some w' => flatten_t np F ntm st1 (NBind u w' b) | None => None end
      | None => None
      end
    else None.
Proof. reflexivity. Qed.

Lemma tnorm_s_shift h t st :
  tnorm_s (TShiftE h t) st
  = match tnorm_s t st with
    | Some (st1, NVar h' i) =>
        match lcmp F h h' with
        | Some Eq => Some (st1, NVar h' (S i))
        | Some _ => Some (st1, NVar h' i)
        | None => None
        end
    | _ => None
    end.
Proof. reflexivity. Qed.

Lemma pnorm_s_comp a p st :
  pnorm_e_s (PComp a p) st
  = match anorm_s a st with
    | Some (st1, wa) =>
        match pnorm_e_s p st1 with
        | Some (st2, (w, b)) =>
            match then_flatten (wcomp F ntm wa w) st2 with Some (st3, w') => Some (st3, (w', b)) | None => None end
        | None => None
        end
    | None => None
    end.
Proof. reflexivity. Qed.

Lemma pnorm_s_shift h p st :
  pnorm_e_s (PShift h p) st
  = match pnorm_e_s p st with
    | Some (st1, (w, b)) =>
        match then_flatten (wouter F ntm h w) st1 with Some (st2, w') => Some (st2, (w', b)) | None => None end
    | None => None
    end.
Proof. reflexivity. Qed.

(** The operations, on normal forms over any table. *)
Lemma comp_ok N P wa wb w : wnf N false wa -> wnf N false wb -> wcomp F ntm wa wb = Some w ->
  wnf N false w /\ wden P w = rcompose (wden P wa) (wden P wb).
Proof.
  intros Ha Hb E; split; [exact (wcomp_normal lenv labs N F HF ntm _ _ _ Ha Hb E)|].
  exact (proj2 (wcomp_sound lenv tenv aenv P F HF ntm Hntm _ _ _ (wnf_dist _ _ _ Ha) (wnf_dist _ _ _ Hb) E)).
Qed.

Lemma outer_ok N P h wa w : In h labs -> wnf N false wa -> wouter F ntm h wa = Some w ->
  wnf N false w /\ wden P w = rpush_outer (lden lenv h) (wden P wa).
Proof.
  intros Hh Ha E; split; [exact (wouter_normal lenv labs N F HF ntm _ _ _ Hh Ha E)|].
  exact (proj2 (wouter_sound lenv tenv aenv P F HF ntm Hntm _ _ _ (wnf_dist _ _ _ Ha) E)).
Qed.

Lemma lift_ok N P h wa w : In h labs -> wnf N false wa -> wlift F ntm h wa = Some w ->
  wnf N false w /\ wden P w = rlift (lden lenv h) (wden P wa).
Proof.
  intros Hh Ha E; split; [exact (wlift_normal lenv labs N F HF ntm _ _ _ Hh Ha E)|].
  exact (proj2 (wlift_sound lenv tenv aenv P F HF ntm Hntm _ _ _ (wnf_dist _ _ _ Ha) E)).
Qed.

Lemma push_ok N P h t wa w : In h labs -> tnf N t -> wnf N false wa -> wpush F ntm h t wa = Some w ->
  wnf N false w /\ wden P w = rpush_inner (lden lenv h) (tden P t) (wden P wa).
Proof.
  intros Hh Ht Ha E; split; [exact (wpush_normal lenv labs N F HF ntm _ _ _ _ Hh Ht Ha E)|].
  exact (proj2 (wpush_sound lenv tenv aenv P F HF ntm Hntm _ _ _ _ (proj1 (nf_dist N) _ Ht) (wnf_dist _ _ _ Ha) E)).
Qed.

Lemma pn_ok N P b w w' : wnf N false w -> pnormw F ntm b w = Some w' ->
  wnf N (bnm b) w' /\ rpcompose (wden P w') (bden P b) = rpcompose (wden P w) (bden P b).
Proof.
  intros Hw E; split; [exact (pnormw_normal lenv labs N F HF ntm _ _ _ Hw E)|].
  exact (proj2 (pnormw_sound lenv tenv aenv P F HF ntm Hntm _ _ _ (wnf_dist _ _ _ Hw) E)).
Qed.

Lemma then_flatten_spec st r d st' w' :
  inv st -> (forall w, r = Some w -> wnf (np + List.length (sdefs st)) false w /\ wden (ext (sdefs st)) w = d) ->
  then_flatten r st = Some (st', w') ->
  inv st' /\ extends (sdefs st) (sdefs st') /\ wnf (np + List.length (sdefs st')) false w'
  /\ wden (ext (sdefs st')) w' = d.
Proof.
  intros Hi Hr; destruct r as [w|]; [|discriminate]; cbn [Shared.then_flatten]; intros E.
  destruct (Hr w eq_refl) as [Hw Ew]; destruct (flatten_spec _ _ _ _ _ Hi Hw E) as [H1 [H2 [H3 H4]]].
  refine (conj H1 (conj H2 (conj H3 _))); rewrite H4, (wden_up _ _ _ _ H2 Hw); exact Ew.
Qed.

Theorem norm_s_spec :
  (forall e, incl (alabs e) labs -> ascope np e -> forall st st' w, inv st -> anorm_s e st = Some (st', w) ->
     inv st' /\ extends (sdefs st) (sdefs st') /\ wnf (np + List.length (sdefs st')) false w
     /\ wden (ext (sdefs st')) w = aeden penv e)
  /\ (forall t, incl (tlabs t) labs -> tscope np t -> forall st st' t', inv st -> tnorm_s t st = Some (st', t') ->
     inv st' /\ extends (sdefs st) (sdefs st') /\ tnf (np + List.length (sdefs st')) t'
     /\ tden (ext (sdefs st')) t' = teden penv t)
  /\ (forall p, incl (plabs p) labs -> pscope np p -> forall st st' w b, inv st ->
     pnorm_e_s p st = Some (st', (w, b)) ->
     inv st' /\ extends (sdefs st) (sdefs st') /\ wnf (np + List.length (sdefs st')) false w /\ bok np b
     /\ rpcompose (wden (ext (sdefs st')) w) (bden penv b) = peden penv p).
Proof.
  apply exp_mind; cbn [alabs tlabs plabs ascope tscope pscope].
  - intros _ _ st st' w Hi H; injection H as <- <-.
    exact (conj Hi (conj (extends_refl _) (conj (wnf_id _ _) eq_refl))).
  - intros n _ _ st st' w Hi H; injection H as <- <-.
    refine (conj Hi (conj (extends_refl _) (conj (atom_word lenv labs _ [] n (conj (SSorted_nil _) (Forall_nil _))) _))).
    exact (proj2 (proj1 (anorm_sound_dist lenv tenv aenv (ext (sdefs st)) F HF ntm Hntm) (AAtom n) _ eq_refl)).
  - intros a IHa b IHb Hl [Sa Sb] st st' w Hi; rewrite anorm_s_compose.
    destruct (anorm_s a st) as [[st1 wa]|] eqn:Ea; [|discriminate].
    destruct (IHa (fun x Hx => Hl x (in_or_app _ _ _ (or_introl Hx))) Sa _ _ _ Hi Ea) as [Hi1 [Hx1 [Hwa Da]]].
    destruct (anorm_s b st1) as [[st2 wb]|] eqn:Eb; [|discriminate].
    destruct (IHb (fun x Hx => Hl x (in_or_app _ _ _ (or_intror Hx))) Sb _ _ _ Hi1 Eb) as [Hi2 [Hx2 [Hwb Db]]].
    intros E; apply (then_flatten_spec _ _ (rcompose (aeden penv a) (aeden penv b)) _ _ Hi2) in E as [H1 [H2 [H3 H4]]].
    2:{ intros w0 Ew; destruct (comp_ok _ (ext (sdefs st2)) _ _ _ (wnf_up _ _ _ _ Hx2 Hwa) Hwb Ew) as [A B]; split; [exact A|].
      rewrite B, Db, (wden_up _ _ _ _ Hx2 Hwa), Da; reflexivity. }
    exact (conj H1 (conj (extends_trans _ _ _ Hx1 (extends_trans _ _ _ Hx2 H2)) (conj H3 H4))).
  - intros h a IH Hl Sa st st' w Hi; rewrite anorm_s_outer.
    destruct (anorm_s a st) as [[st1 wa]|] eqn:Ea; [|discriminate].
    destruct (IH (fun x Hx => Hl x (or_intror Hx)) Sa _ _ _ Hi Ea) as [Hi1 [Hx1 [Hwa Da]]].
    intros E; apply (then_flatten_spec _ _ (rpush_outer (lden lenv h) (aeden penv a)) _ _ Hi1) in E as [H1 [H2 [H3 H4]]].
    2:{ intros w0 Ew; destruct (outer_ok _ (ext (sdefs st1)) _ _ _ (Hl h (or_introl eq_refl)) Hwa Ew) as [A B]; split; [exact A|].
      rewrite B, Da; reflexivity. }
    exact (conj H1 (conj (extends_trans _ _ _ Hx1 H2) (conj H3 H4))).
  - intros h t IHt a IHa Hl [St Sa] st st' w Hi; rewrite anorm_s_inner.
    destruct (tnorm_s t st) as [[st1 t1]|] eqn:Et; [|discriminate].
    destruct (IHt (fun x Hx => Hl x (or_intror (in_or_app _ _ _ (or_introl Hx)))) St _ _ _ Hi Et) as [Hi1 [Hx1 [Ht1 Dt]]].
    destruct (anorm_s a st1) as [[st2 wa]|] eqn:Ea; [|discriminate].
    destruct (IHa (fun x Hx => Hl x (or_intror (in_or_app _ _ _ (or_intror Hx)))) Sa _ _ _ Hi1 Ea) as [Hi2 [Hx2 [Hwa Da]]].
    intros E; apply (then_flatten_spec _ _ (rpush_inner (lden lenv h) (teden penv t) (aeden penv a)) _ _ Hi2) in E as [H1 [H2 [H3 H4]]].
    2:{ intros w0 Ew; destruct (push_ok _ (ext (sdefs st2)) _ _ _ _ (Hl h (or_introl eq_refl)) (tnf_up _ _ _ Hx2 Ht1) Hwa Ew) as [A B].
      split; [exact A|]; rewrite B, Da, (tden_up _ _ _ Hx2 Ht1), Dt; reflexivity. }
    exact (conj H1 (conj (extends_trans _ _ _ Hx1 (extends_trans _ _ _ Hx2 H2)) (conj H3 H4))).
  - intros h a IH Hl Sa st st' w Hi; rewrite anorm_s_lift.
    destruct (anorm_s a st) as [[st1 wa]|] eqn:Ea; [|discriminate].
    destruct (IH (fun x Hx => Hl x (or_intror Hx)) Sa _ _ _ Hi Ea) as [Hi1 [Hx1 [Hwa Da]]].
    intros E; apply (then_flatten_spec _ _ (rlift (lden lenv h) (aeden penv a)) _ _ Hi1) in E as [H1 [H2 [H3 H4]]].
    2:{ intros w0 Ew; destruct (lift_ok _ (ext (sdefs st1)) _ _ _ (Hl h (or_introl eq_refl)) Hwa Ew) as [A B]; split; [exact A|].
      rewrite B, Da; reflexivity. }
    exact (conj H1 (conj (extends_trans _ _ _ Hx1 H2) (conj H3 H4))).
  - intros h i Hl _ st st' t' Hi H; injection H as <- <-.
    exact (conj Hi (conj (extends_refl _) (conj (Hl h (or_introl eq_refl)) eq_refl))).
  - intros u p IH Hl Sp st st' t' Hi; rewrite tnorm_s_bind; destruct (Nat.ltb_spec u ntm) as [Hu|]; [|discriminate].
    destruct (pnorm_e_s p st) as [[st1 [w b]]|] eqn:Ep; [|discriminate].
    destruct (IH Hl Sp _ _ _ _ Hi Ep) as [Hi1 [Hx1 [Hw [Hb Dp]]]].
    destruct (pnormw F ntm b w) as [w1|] eqn:Ew; [|discriminate]; intros E.
    destruct (pn_ok _ (ext (sdefs st1)) _ _ _ Hw Ew) as [Hw1 Dw].
    assert (Ht : tnf (np + List.length (sdefs st1)) (NBind u w1 b)).
    { split; [apply (bok_mono np); [lia|exact Hb]|exact Hw1]. }
    destruct (flatten_t_spec _ _ _ _ Hi1 Ht E) as [H1 [H2 [H3 H4]]].
    refine (conj H1 (conj (extends_trans _ _ _ Hx1 H2) (conj H3 _))).
    rewrite H4, (tden_up _ _ _ H2 Ht), tden_unfold, teden_bind, Dw, (bden_real _ b Hb), Dp; reflexivity.
  - intros h t IH Hl St st st' t' Hi; rewrite tnorm_s_shift.
    destruct (tnorm_s t st) as [[st1 [h' i|? ? ?]]|] eqn:Et; try discriminate.
    destruct (IH (fun x Hx => Hl x (or_intror Hx)) St _ _ _ Hi Et) as [Hi1 [Hx1 [Ht1 Dt]]].
    rewrite teden_shift, <- Dt; cbn [Normalise.tden].
    destruct (lcmp F h h') as [c|] eqn:Ec; [|discriminate].
    apply (lcmp_sound lenv F HF) in Ec; destruct c; intros H; injection H as <- <-;
      refine (conj Hi1 (conj Hx1 (conj Ht1 _))); unfold shift_rvar; cbn [v_label v_index Normalise.tden]; cbn in Ec.
    + subst h'; rewrite label_eqb_refl; reflexivity.
    + rewrite (proj2 (label_eqb_neq _ _)); [reflexivity|].
      intros E; rewrite E in Ec; exact (olabel_lt_irrefl _ Ec).
    + rewrite (proj2 (label_eqb_neq _ _)); [reflexivity|].
      intros E; rewrite E in Ec; exact (olabel_lt_irrefl _ Ec).
  - intros _ _ st st' w b Hi H; injection H as <- <- <-.
    refine (conj Hi (conj (extends_refl _) (conj (wnf_id _ _) (conj I _)))); rewrite wden_id; apply rpcompose_identity.
  - intros n _ Hn st st' w b Hi H; injection H as <- <- <-.
    refine (conj Hi (conj (extends_refl _) (conj (wnf_id _ _) (conj Hn _)))); rewrite wden_id; apply rpcompose_identity.
  - intros a IHa p IHp Hl [Sa Sp] st st' w b Hi; rewrite pnorm_s_comp.
    destruct (anorm_s a st) as [[st1 wa]|] eqn:Ea; [|discriminate].
    destruct (IHa (fun x Hx => Hl x (in_or_app _ _ _ (or_introl Hx))) Sa _ _ _ Hi Ea) as [Hi1 [Hx1 [Hwa Da]]].
    destruct (pnorm_e_s p st1) as [[st2 [w0 b0]]|] eqn:Ep; [|discriminate].
    destruct (IHp (fun x Hx => Hl x (in_or_app _ _ _ (or_intror Hx))) Sp _ _ _ _ Hi1 Ep) as [Hi2 [Hx2 [Hw0 [Hb0 Dp]]]].
    destruct (then_flatten (wcomp F ntm wa w0) st2) as [[st3 w3]|] eqn:E; [|discriminate]; intros H; injection H as <- <- <-.
    apply (then_flatten_spec _ _ (rcompose (aeden penv a) (wden (ext (sdefs st2)) w0)) _ _ Hi2) in E as [H1 [H2 [H3 H4]]].
    2:{ intros w1 Ew; destruct (comp_ok _ (ext (sdefs st2)) _ _ _ (wnf_up _ _ _ _ Hx2 Hwa) Hw0 Ew) as [A B]; split; [exact A|].
      rewrite B, (wden_up _ _ _ _ Hx2 Hwa), Da; reflexivity. }
    refine (conj H1 (conj (extends_trans _ _ _ Hx1 (extends_trans _ _ _ Hx2 H2)) (conj H3 (conj Hb0 _)))).
    rewrite H4, <- rpcompose_compose, Dp; reflexivity.
  - intros h p IH Hl Sp st st' w b Hi; rewrite pnorm_s_shift.
    destruct (pnorm_e_s p st) as [[st1 [w0 b0]]|] eqn:Ep; [|discriminate].
    destruct (IH (fun x Hx => Hl x (or_intror Hx)) Sp _ _ _ _ Hi Ep) as [Hi1 [Hx1 [Hw0 [Hb0 Dp]]]].
    destruct (then_flatten (wouter F ntm h w0) st1) as [[st2 w2]|] eqn:E; [|discriminate]; intros H; injection H as <- <- <-.
    apply (then_flatten_spec _ _ (rpush_outer (lden lenv h) (wden (ext (sdefs st1)) w0)) _ _ Hi1) in E as [H1 [H2 [H3 H4]]].
    2:{ intros w1 Ew; exact (outer_ok _ (ext (sdefs st1)) _ _ _ (Hl h (or_introl eq_refl)) Hw0 Ew). }
    refine (conj H1 (conj (extends_trans _ _ _ Hx1 H2) (conj H3 (conj Hb0 _)))).
    rewrite H4, rpush_outer_as_compose, <- rpcompose_compose, Dp.
    symmetry; apply rpshift_as_pcompose.
Qed.

(** The shared decision is sound. *)
Theorem nf_eq_s_sound e1 e2 :
  incl (alabs e1) labs -> incl (alabs e2) labs -> ascope np e1 -> ascope np e2 ->
  nf_eq_s np F ntm e1 e2 = true -> aeden penv e1 = aeden penv e2.
Proof.
  intros Hl1 Hl2 Hs1 Hs2; unfold nf_eq_s.
  destruct (anorm_s e1 (mk_sst [] [])) as [[st1 w1]|] eqn:E1; [|discriminate].
  destruct (anorm_s e2 st1) as [[st2 w2]|] eqn:E2; [|discriminate]; intros Ew.
  apply (proj2 (proj2 (proj2 nf_eqb_eq))) in Ew; subst w2.
  assert (Hi0 : inv (mk_sst [] [])) by (split; [exact I|constructor]).
  destruct (proj1 norm_s_spec e1 Hl1 Hs1 _ _ _ Hi0 E1) as [Hi1 [_ [Hw1 D1]]].
  destruct (proj1 norm_s_spec e2 Hl2 Hs2 _ _ _ Hi1 E2) as [_ [Hx2 [_ D2]]].
  rewrite <- D1, <- D2; symmetry; exact (wden_up _ _ _ _ Hx2 Hw1).
Qed.

End Sound.
