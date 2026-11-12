(** * The order on payloads

    [LayeredUnique.lw_unique] takes any strict order on what payloads do
    to named variables.  Here is where one comes from.

    A payload that has a normal word ([Unique.wnf], as a payload) has
    exactly one, so any strict order on words gives an order on
    payloads ([gt_of]), and a total order on words gives a total one:
    any two layers can be put in order.

    The order on words taken here ([ord_sz]) compares sizes first, so a
    word is above the payload words of the terms in it and a term that
    sees a layer is above that layer without any comparison; words of
    the same size are compared by a serialisation, which is an arbitrary
    but fixed choice. *)

From Stdlib Require Import Arith List Lia Bool String Ascii.
From ShiftedNames.Core Require Import Label Var Adjustment Normalise Unique Layered LayeredUnique.
Import ListNotations.

(** ** From an order on words to an order on payloads *)

Section Lift.

Variable lenv : list label.
Variable labs : list lexp.
Variable npa : nat.
Hypothesis Hinj : forall h h', In h labs -> In h' labs -> lden lenv h = lden lenv h' -> h = h'.

Variable ord : word -> word -> Prop.
Hypothesis ord_irrefl : forall w, ~ ord w w.
Hypothesis ord_trans : forall a b c, ord a b -> ord b c -> ord a c.

(** [w] is the normal word of the payload [k]. *)
Definition pword (k : rvar -> fres) (w : word) : Prop :=
  wnf lenv labs npa true w /\ keq k (fw lenv w FVar).

Definition gt_of (k k' : rvar -> fres) : Prop := exists w w', pword k w /\ pword k' w' /\ ord w w'.

Lemma pword_unique k k' w w' : keq k k' -> pword k w -> pword k' w' -> w = w'.
Proof.
  intros K [H1 K1] [H2 K2]; apply (nf_unique_n lenv labs npa Hinj (wsz w) w w' true (le_n _) H1 H2).
  intros v Hv; specialize (Hv eq_refl).
  exact (feq_trans _ _ _ (feq_sym _ _ (K1 v Hv)) (feq_trans _ _ _ (K v Hv) (K2 v Hv))).
Qed.

Lemma pword_keq k k' w : keq k k' -> pword k w -> pword k' w.
Proof. intros K [H1 K1]; split; [exact H1|exact (keq_trans _ _ _ (keq_sym _ _ K) K1)]. Qed.

Lemma gt_of_irrefl k k' : keq k k' -> ~ gt_of k k'.
Proof. intros K [w [w' [H1 [H2 Ho]]]]; rewrite (pword_unique k k' w w' K H1 H2) in Ho; exact (ord_irrefl _ Ho). Qed.

Lemma gt_of_trans k1 k2 k3 : gt_of k1 k2 -> gt_of k2 k3 -> gt_of k1 k3.
Proof.
  intros [w1 [w2 [H1 [H2 Ho]]]] [w2' [w3 [H2' [H3 Ho']]]]; exists w1, w3; split; [exact H1|split; [exact H3|]].
  rewrite <- (pword_unique k2 k2 w2 w2' (keq_refl _) H2 H2') in Ho'; exact (ord_trans _ _ _ Ho Ho').
Qed.

Lemma gt_of_keq k1 k1' k2 k2' : keq k1 k1' -> keq k2 k2' -> gt_of k1 k2 -> gt_of k1' k2'.
Proof.
  intros K1 K2 [w [w' [H1 [H2 Ho]]]]; exists w, w'.
  split; [exact (pword_keq _ _ _ K1 H1)|split; [exact (pword_keq _ _ _ K2 H2)|exact Ho]].
Qed.

(** With a total order on words, two payloads with normal words are the
    same on named variables or one is above the other. *)
Lemma gt_of_total k k' w w' :
  (forall a b, ord a b \/ a = b \/ ord b a) ->
  pword k w -> pword k' w' -> gt_of k k' \/ keq k k' \/ gt_of k' k.
Proof.
  intros Ht H1 H2; destruct (Ht w w') as [Ho|[<-|Ho]].
  - left; exists w, w'; auto.
  - right; left; destruct H1 as [_ K1]; destruct H2 as [_ K2]; exact (keq_trans _ _ _ K1 (keq_sym _ _ K2)).
  - right; right; exists w', w; auto.
Qed.

(** Uniqueness of layered normal forms for the order from [ord]. *)
Theorem lw_unique_of nt l m :
  lnf lenv labs gt_of l -> lnf lenv labs gt_of m -> lwok lenv (tenvT nt) l -> lwok lenv (tenvT nt) m ->
  (forall aenv penv, lwden lenv (tenvT nt) aenv penv l = lwden lenv (tenvT nt) aenv penv m) ->
  l = m.
Proof. exact (lw_unique_real lenv labs Hinj gt_of gt_of_irrefl gt_of_trans gt_of_keq nt l m). Qed.

End Lift.

(** ** A total order on words *)

(** A serialisation of words in which no word's code is the beginning of
    another's. *)
Fixpoint ccode (s : string) : list nat :=
  match s with EmptyString => [0] | String a s => S (nat_of_ascii a) :: ccode s end.

Definition lcode (h : lexp) : list nat :=
  match h with LNone => [0] | LCon s => 1 :: ccode s | LAtom n => [2; n] end.

Definition bcode (b : option nat) : list nat := match b with None => [0] | Some n => [1; n] end.

Fixpoint Lcode (L : list (lexp * nat)) : list nat :=
  match L with [] => [0] | (h, n) :: L' => 1 :: lcode h ++ n :: Lcode L' end.

Fixpoint tcode (t : ntgt) : list nat :=
  match t with
  | NVar h i => 0 :: lcode h ++ [i]
  | NBind u w b => 1 :: u :: bcode b ++ wcode w
  end
with tlcode (ts : tlist) : list nat :=
  match ts with TNil => [0] | TCons t r => 1 :: tcode t ++ tlcode r end
with scode (s : seg) : list nat :=
  match s with SNil => [0] | SEnt h ts m r => 1 :: lcode h ++ tlcode ts ++ m :: scode r end
with wcode (w : word) : list nat :=
  match w with
  | WEnd s => 0 :: scode s
  | WAtom s L a w' => 1 :: scode s ++ Lcode L ++ a :: wcode w'
  end.

Lemma ccode_inj s : forall s' l l', ccode s ++ l = ccode s' ++ l' -> s = s' /\ l = l'.
Proof.
  induction s as [|a s IH]; intros [|a' s'] l l' E; cbn in E; try discriminate E.
  - injection E as E; split; [reflexivity|exact E].
  - injection E as Ea E; destruct (IH _ _ _ E) as [-> ->]; split; [|reflexivity].
    f_equal; rewrite <- (ascii_nat_embedding a), <- (ascii_nat_embedding a'), Ea; reflexivity.
Qed.

Lemma lcode_inj h : forall h' l l', lcode h ++ l = lcode h' ++ l' -> h = h' /\ l = l'.
Proof.
  destruct h as [|s|n]; intros [|s'|n'] l l' E; cbn in E; try discriminate E.
  - injection E as E; split; [reflexivity|exact E].
  - injection E as E; destruct (ccode_inj _ _ _ _ E) as [-> ->]; split; reflexivity.
  - injection E as -> E; split; [reflexivity|exact E].
Qed.

Lemma bcode_inj b : forall b' l l', bcode b ++ l = bcode b' ++ l' -> b = b' /\ l = l'.
Proof.
  destruct b as [n|]; intros [n'|] l l' E; cbn in E; try discriminate E.
  - injection E as -> E; split; [reflexivity|exact E].
  - injection E as E; split; [reflexivity|exact E].
Qed.

Lemma Lcode_inj L : forall L' l l', Lcode L ++ l = Lcode L' ++ l' -> L = L' /\ l = l'.
Proof.
  induction L as [|[h n] L IH]; intros [|[h' n'] L'] l l' E; cbn in E; try discriminate E.
  - injection E as E; split; [reflexivity|exact E].
  - injection E as E; rewrite <- !app_assoc in E; cbn [app] in E.
    destruct (lcode_inj _ _ _ _ E) as [-> E']; injection E' as -> E'.
    destruct (IH _ _ _ E') as [-> ->]; split; reflexivity.
Qed.

Lemma code_inj :
  (forall t t' l l', tcode t ++ l = tcode t' ++ l' -> t = t' /\ l = l')
  /\ (forall ts ts' l l', tlcode ts ++ l = tlcode ts' ++ l' -> ts = ts' /\ l = l')
  /\ (forall s s' l l', scode s ++ l = scode s' ++ l' -> s = s' /\ l = l')
  /\ (forall w w' l l', wcode w ++ l = wcode w' ++ l' -> w = w' /\ l = l').
Proof.
  apply nf_mind.
  - intros h i [h' i'|u' w' b'] l l' E; cbn in E; [|discriminate E].
    injection E as E; rewrite <- !app_assoc in E; cbn [app] in E.
    destruct (lcode_inj _ _ _ _ E) as [-> E']; injection E' as -> ->; split; reflexivity.
  - intros u w IH b [h' i'|u' w' b'] l l' E; cbn in E; [discriminate E|].
    injection E as -> E; rewrite <- !app_assoc in E.
    destruct (bcode_inj _ _ _ _ E) as [-> E']; destruct (IH _ _ _ E') as [-> ->]; split; reflexivity.
  - intros [|t' r'] l l' E; cbn in E; [|discriminate E]; injection E as E; split; [reflexivity|exact E].
  - intros t IHt r IHr [|t' r'] l l' E; cbn in E; [discriminate E|].
    injection E as E; rewrite <- !app_assoc in E.
    destruct (IHt _ _ _ E) as [-> E']; destruct (IHr _ _ _ E') as [-> ->]; split; reflexivity.
  - intros [|h' ts' m' r'] l l' E; cbn in E; [|discriminate E]; injection E as E; split; [reflexivity|exact E].
  - intros h ts IHts m r IHr [|h' ts' m' r'] l l' E; cbn in E; [discriminate E|].
    injection E as E; rewrite <- !app_assoc in E; cbn [app] in E.
    destruct (lcode_inj _ _ _ _ E) as [-> E']; try rewrite <- !app_assoc in E'; cbn [app] in E'.
    destruct (IHts _ _ _ E') as [-> E'']; injection E'' as -> E''.
    destruct (IHr _ _ _ E'') as [-> ->]; split; reflexivity.
  - intros s IHs [s'|s' L' a' w'] l l' E; cbn in E; [|discriminate E].
    injection E as E; destruct (IHs _ _ _ E) as [-> ->]; split; reflexivity.
  - intros s IHs L a w IHw [s'|s' L' a' w'] l l' E; cbn in E; [discriminate E|].
    injection E as E; rewrite <- !app_assoc in E; cbn [app] in E.
    destruct (IHs _ _ _ E) as [-> E']; try rewrite <- !app_assoc in E'; cbn [app] in E'.
    destruct (Lcode_inj _ _ _ _ E') as [-> E'']; injection E'' as -> E''.
    destruct (IHw _ _ _ E'') as [-> ->]; split; reflexivity.
Qed.

Lemma wcode_inj w w' : wcode w = wcode w' -> w = w'.
Proof.
  intros E; apply (proj2 (proj2 (proj2 code_inj)) w w' [] []); rewrite !app_nil_r; exact E.
Qed.

(** Lists of numbers, in dictionary order. *)
Fixpoint llt (a b : list nat) : Prop :=
  match a, b with
  | [], _ :: _ => True
  | x :: a', y :: b' => x < y \/ (x = y /\ llt a' b')
  | _, [] => False
  end.

Lemma llt_irrefl a : ~ llt a a.
Proof. induction a as [|x a IH]; cbn; [tauto|intros [H|[_ H]]; [lia|exact (IH H)]]. Qed.

Lemma llt_trans a : forall b c, llt a b -> llt b c -> llt a c.
Proof.
  induction a as [|x a IH]; intros [|y b] [|z c]; cbn; try tauto.
  intros [H|[-> H]] [H'|[-> H']]; [left; lia|left; exact H|left; exact H'|right; split; [reflexivity|exact (IH _ _ H H')]].
Qed.

Lemma llt_total a : forall b, llt a b \/ a = b \/ llt b a.
Proof.
  induction a as [|x a IH]; intros [|y b]; cbn; [tauto|tauto|tauto|].
  destruct (Nat.lt_trichotomy x y) as [H|[->|H]]; [tauto| |tauto].
  destruct (IH b) as [H|[->|H]]; tauto.
Qed.

(** Larger words first; among words of one size, by code. *)
Definition ord_sz (a b : word) : Prop :=
  wsz b < wsz a \/ (wsz a = wsz b /\ llt (wcode b) (wcode a)).

Lemma ord_sz_irrefl w : ~ ord_sz w w.
Proof. intros [H|[_ H]]; [lia|exact (llt_irrefl _ H)]. Qed.

Lemma ord_sz_trans a b c : ord_sz a b -> ord_sz b c -> ord_sz a c.
Proof.
  intros [H|[E H]] [H'|[E' H']]; [left; lia|left; lia|left; lia|].
  right; split; [lia|exact (llt_trans _ _ _ H' H)].
Qed.

Lemma ord_sz_total a b : ord_sz a b \/ a = b \/ ord_sz b a.
Proof.
  unfold ord_sz; destruct (Nat.lt_trichotomy (wsz a) (wsz b)) as [H|[E|H]]; [tauto| |tauto].
  destruct (llt_total (wcode a) (wcode b)) as [H|[H|H]]; [right; right; right; split; [lia|exact H]| |tauto].
  right; left; exact (wcode_inj _ _ H).
Qed.

(** A word is above the payload word of any term in its last segment. *)
Lemma ord_sz_term w u wp b : In (NBind u wp b) (stgts (whead w)) -> ord_sz w wp.
Proof.
  intros H; left; pose proof (stgts_sz _ _ H) as Hs; cbn [tsz] in Hs.
  destruct w as [s|s L a w']; cbn [whead wsz] in *; lia.
Qed.

(** ** The theorem with this order *)

Section Concrete.

Variable lenv : list label.
Variable labs : list lexp.
Variable npa : nat.
Hypothesis Hinj : forall h h', In h labs -> In h' labs -> lden lenv h = lden lenv h' -> h = h'.

(** The order on payloads. *)
Definition gt_sz : (rvar -> fres) -> (rvar -> fres) -> Prop := gt_of lenv labs npa ord_sz.

(** Two layered words in normal form for this order that mean the same
    under every interpretation of the atoms are the same word. *)
Theorem lw_unique_sz nt l m :
  lnf lenv labs gt_sz l -> lnf lenv labs gt_sz m -> lwok lenv (tenvT nt) l -> lwok lenv (tenvT nt) m ->
  (forall aenv penv, lwden lenv (tenvT nt) aenv penv l = lwden lenv (tenvT nt) aenv penv m) ->
  l = m.
Proof. exact (lw_unique_of lenv labs npa Hinj ord_sz ord_sz_irrefl ord_sz_trans nt l m). Qed.

(** Any two payloads with normal words are in order, or the same. *)
Theorem gt_sz_total k k' w w' :
  pword lenv labs npa k w -> pword lenv labs npa k' w' -> gt_sz k k' \/ keq k k' \/ gt_sz k' k.
Proof. exact (gt_of_total lenv labs npa ord_sz k k' w w' ord_sz_total). Qed.

(** A payload is above the payload of a term with the identity payload
    adjustment that it sends a variable to. *)
Theorem gt_sz_term k w u wp :
  pword lenv labs npa k w -> In (NBind u wp None) (stgts (whead w)) -> gt_sz k (fw lenv wp FVar).
Proof.
  intros Hw Hin; exists w, wp; split; [exact Hw|split; [|exact (ord_sz_term w u wp None Hin)]].
  split; [|apply keq_refl].
  destruct Hw as [Hn _]; assert (Hs : snf lenv labs npa (whead w)).
  { destruct w as [s|s L a w']; cbn [wnf whead] in *; tauto. }
  exact (proj2 (snf_in lenv labs npa _ Hs _ Hin)).
Qed.

End Concrete.
