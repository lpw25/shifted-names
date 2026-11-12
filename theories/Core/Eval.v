(** * Evaluation and display from the shared normal form

    What [names] reads off a normal form, from the stored word of
    [Shared]: the variable an adjustment sends a variable to
    ([apply_result_s]), and a check that it sends one to a term with a
    given payload ([apply_bind_check_s]).  Neither unfolds anything: a
    variable is the same in the stored word and in its unfolding, and
    two payloads are compared as atoms of one table.

    For display, the stored word is unfolded on demand, and only when the
    result is small ([anorm_show]): the tree can be exponentially larger
    than the stored word.  Display is not verified; what [names] shows is
    proved equal to what it started from by the decision. *)

From Stdlib Require Import Arith List Lia Bool NArith.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Unique Normal Complete Shared.
Import ListNotations.

(** ** Evaluation *)

Definition apply_result_s (F : list (lexp * lexp)) (ntm : nat) (e : aexp) (h : lexp) (i : nat) : option (lexp * nat) :=
  match anorm_s (apmax e) F ntm e (mk_sst [] []) with
  | Some (_, w) => match wtgt F w h i with Some (NVar h' j) => Some (h', j) | _ => None end
  | None => None
  end.

(** A variable sent to a term, checked against the reified adjustment
    [eb] its payload was shown as: [u] with the payload [eb] is the same
    stored term. *)
Definition apply_bind_check_s (F : list (lexp * lexp)) (ntm : nat) (e : aexp) (h : lexp) (i : nat) (eb : aexp) : option nat :=
  let N := Nat.max (apmax e) (apmax eb) in
  match anorm_s N F ntm e (mk_sst [] []) with
  | Some (st1, w) =>
      match wtgt F w h i with
      | Some (NBind u p b) =>
          match tnorm_s N F ntm (TBindE u (PComp eb PId)) st1 with
          | Some (_, t') => if ntgt_eqb (NBind u p b) t' then Some u else None
          | None => None
          end
      | _ => None
      end
  | None => None
  end.

Section Sound.

Context {T : Type}.
Variable lenv : list label.
Variable tenv : list T.
Variable aenv : list (radj T).
Variable penv : list (rpadj T).
Variable F : list (lexp * lexp).
Hypothesis HF : facts_ok lenv F.
Variable ntm : nat.
Hypothesis Hntm : ntm <= List.length tenv.

Local Notation aeden := (aeden lenv tenv aenv).
Local Notation wden := (wden lenv tenv aenv).
Local Notation tden := (tden lenv tenv aenv).
Local Notation lden := (lden lenv).

Theorem apply_result_s_sound e h i h' j :
  apply_result_s F ntm e h i = Some (h', j) ->
  rapply (aeden penv e) (mk_rvar (lden h) i) = inl (mk_rvar (lden h') j).
Proof.
  unfold apply_result_s; destruct (anorm_s (apmax e) F ntm e (mk_sst [] [])) as [[st w]|] eqn:E; [|discriminate].
  destruct (wtgt F w h i) as [[h1 j1|]|] eqn:Et; try discriminate; intros H; injection H as <- <-.
  destruct (pad_spec (apmax e) penv) as [P [HP Hag]].
  pose proof (proj1 (scope_max (apmax e)) e (le_n _)) as Sc.
  rewrite <- (proj1 (eden_agree lenv tenv aenv (apmax e) P penv Hag) e Sc).
  rewrite <- HP in E, Sc.
  assert (Hi0 : inv lenv tenv aenv P (alabs e) (mk_sst [] [])) by (split; [exact I|constructor]).
  destruct (proj1 (norm_s_spec lenv tenv aenv P (alabs e) F HF ntm Hntm) e (incl_refl _) Sc _ _ _ Hi0 E) as [_ [_ [Hw D]]].
  rewrite <- D, (proj2 (wtgt_sound lenv tenv aenv _ F HF ntm Hntm w h i _ (wnf_dist _ _ _ _ _ Hw) Et)); reflexivity.
Qed.

Theorem apply_bind_s_sound e h i eb u x :
  apply_bind_check_s F ntm e h i eb = Some u -> nth_error tenv u = Some x ->
  rapply (aeden penv e) (mk_rvar (lden h) i) = inr (x, rpcompose (aeden penv eb) rpidentity).
Proof.
  unfold apply_bind_check_s; set (N := Nat.max (apmax e) (apmax eb)).
  destruct (anorm_s N F ntm e (mk_sst [] [])) as [[st1 w]|] eqn:E; [|discriminate].
  destruct (wtgt F w h i) as [[|u0 p b]|] eqn:Et; try discriminate.
  destruct (tnorm_s N F ntm (TBindE u0 (PComp eb PId)) st1) as [[st2 t']|] eqn:Eb; [|discriminate].
  destruct (ntgt_eqb (NBind u0 p b) t') eqn:Eq; [|discriminate]; intros H; injection H as <-; intros Hx.
  apply (proj1 nf_eqb_eq) in Eq; subst t'.
  destruct (pad_spec N penv) as [P [HP Hag]].
  assert (S1 : ascope N e) by (apply (proj1 (scope_max N)); unfold N; lia).
  assert (S2 : ascope N eb) by (apply (proj1 (scope_max N)); unfold N; lia).
  rewrite <- (proj1 (eden_agree lenv tenv aenv N P penv Hag) e S1), <- (proj1 (eden_agree lenv tenv aenv N P penv Hag) eb S2).
  rewrite <- HP in E, Eb, S1, S2.
  set (labs := alabs e ++ alabs eb).
  assert (Hi0 : inv lenv tenv aenv P labs (mk_sst [] [])) by (split; [exact I|constructor]).
  assert (Hl1 : incl (alabs e) labs) by (intros y Hy; apply in_or_app; left; exact Hy).
  assert (Hl2 : incl (tlabs (TBindE u0 (PComp eb PId))) labs).
  { intros y Hy; apply in_or_app; right; change (In y (alabs eb ++ [])) in Hy; rewrite app_nil_r in Hy; exact Hy. }
  destruct (proj1 (norm_s_spec lenv tenv aenv P labs F HF ntm Hntm) e Hl1 S1 _ _ _ Hi0 E) as [Hi1 [_ [Hw D]]].
  destruct (proj1 (proj2 (norm_s_spec lenv tenv aenv P labs F HF ntm Hntm)) (TBindE u0 (PComp eb PId)) Hl2 (conj S2 I)
              _ _ _ Hi1 Eb) as [_ [Hx2 [_ Dt]]].
  rewrite <- D, <- (wden_up lenv tenv aenv P labs ntm Hntm _ _ _ _ Hx2 Hw).
  rewrite (proj2 (wtgt_sound lenv tenv aenv _ F HF ntm Hntm w h i _ (wnf_dist _ _ _ _ _ Hw) Et)), Dt.
  rewrite teden_bind, Hx; reflexivity.
Qed.

End Sound.

(** ** Unfolding for display *)

Section Show.

Variable np : nat.

Section One.

Variable rec : word -> word.
Variable ds : list pdef.

Definition unfd_t (t : ntgt) : ntgt :=
  match t with
  | NBind u p (Some β) =>
      if β <? np then t else match dget ds (β - np) with Some (w, b) => NBind u (rec w) b | None => t end
  | _ => t
  end.

Fixpoint unfd_ts (ts : tlist) : tlist :=
  match ts with TNil => TNil | TCons t r => TCons (unfd_t t) (unfd_ts r) end.

Fixpoint unfd_s (s : seg) : seg :=
  match s with SNil => SNil | SEnt h ts m r => SEnt h (unfd_ts ts) m (unfd_s r) end.

Definition unfd_w (w : word) : word :=
  match w with WEnd s => WEnd (unfd_s s) | WAtom s L a w' => WAtom (unfd_s s) L a w' end.

End One.

(** Only the definitions the word refers to are unfolded. *)
Fixpoint unfd (fuel : nat) (ds : list pdef) (w : word) : word :=
  match fuel with 0 => w | S f => unfd_w (unfd f ds) ds w end.

(** The size of the unfolding, without unfolding. *)
Definition dsz (zs : list N) (k : nat) : N := nth (List.length zs - 1 - k) zs 0%N.

Definition tsz_u (zs : list N) (t : ntgt) : N :=
  match t with
  | NBind _ _ (Some β) => if β <? np then 1%N else (1 + dsz zs (β - np))%N
  | _ => 1%N
  end.

Fixpoint tlsz_u (zs : list N) (ts : tlist) : N :=
  match ts with TNil => 0%N | TCons t r => (tsz_u zs t + tlsz_u zs r)%N end.

Fixpoint ssz_u (zs : list N) (s : seg) : N :=
  match s with SNil => 0%N | SEnt _ ts _ r => (1 + tlsz_u zs ts + ssz_u zs r)%N end.

Fixpoint wsz_r (w : word) : N :=
  match w with WEnd s => (1 + ssz_u [] s)%N | WAtom s _ _ w' => (1 + ssz_u [] s + wsz_r w')%N end.

Definition wsz_u (zs : list N) (w : word) : N :=
  match w with WEnd s => (1 + ssz_u zs s)%N | WAtom s _ _ w' => (1 + ssz_u zs s + wsz_r w')%N end.

Fixpoint usz (ds : list pdef) : list N :=
  match ds with
  | [] => []
  | (w, _) :: r => let zs := usz r in wsz_u zs w :: zs
  end.

Definition unfold_small (budget : N) (ds : list pdef) (w : word) : option word :=
  if (wsz_u (usz ds) w <=? budget)%N then Some (unfd (List.length ds) ds w) else None.

End Show.

(** Larger normal forms are not shown: a chain of substitutions doubles
    with each step. *)
Definition show_budget : N := 250%N.

(** The normal form as a tree, when it is small enough to show. *)
Inductive shown : Type :=
| ShNone
| ShLarge
| ShWord (w : word).

Definition anorm_show (F : list (lexp * lexp)) (ntm : nat) (e : aexp) : shown :=
  match anorm_s (apmax e) F ntm e (mk_sst [] []) with
  | Some (st, w) =>
      match unfold_small (apmax e) show_budget (sdefs st) w with Some w' => ShWord w' | None => ShLarge end
  | None => ShNone
  end.

(** A variable sent to a term whose payload ends with the identity: the
    term and the payload word, for [names] to show the word. *)
Definition apply_payload_s (F : list (lexp * lexp)) (ntm : nat) (e : aexp) (h : lexp) (i : nat) : option (nat * word) :=
  match anorm_s (apmax e) F ntm e (mk_sst [] []) with
  | Some (st, w) =>
      match wtgt F w h i with
      | Some (NBind u p None) => Some (u, p)
      | Some (NBind u _ (Some β)) =>
          if β <? apmax e then None
          else match dget (sdefs st) (β - apmax e) with
               | Some (w0, None) =>
                   match unfold_small (apmax e) show_budget (sdefs st) w0 with
                   | Some wp => Some (u, wp)
                   | None => None
                   end
               | _ => None
               end
      | _ => None
      end
  | None => None
  end.
