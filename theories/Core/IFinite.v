(** * Interleaved models from finitely many identifications

    The models used to tell normal forms apart.  The variables are the
    pairs [(h, i)]; by default [hᵢ] is [(h, i)], so every label has its
    own sequence (the disjoint model).  A list of identifications
    [((h, i), (g, j))] makes [hᵢ] the variable [(g, j)] of another label
    instead.  This is a model when no two indices of one label are made
    the same variable, and only labels the facts do not order share
    variables ([ident_ok]). *)

From Stdlib Require Import String Arith List Lia Bool.
From ShiftedNames.Core Require Import Label Var Normalise IModel.
Import ListNotations.

Definition svar : Type := (lexp * nat)%type.

Definition svar_eqb (x y : svar) : bool := lexp_eqb (fst x) (fst y) && Nat.eqb (snd x) (snd y).

Lemma svar_eqb_eq x y : svar_eqb x y = true <-> x = y.
Proof.
  destruct x as [h i], y as [g j]; unfold svar_eqb; cbn [fst snd]; rewrite andb_true_iff, lexp_eqb_eq, Nat.eqb_eq.
  split; [intros [-> ->]; reflexivity|intros E; injection E as -> ->; auto].
Qed.

Lemma svar_eqb_refl x : svar_eqb x x = true.
Proof. apply svar_eqb_eq; reflexivity. Qed.

(** An identification [(x, r)]: the variable [x] is the variable [r]. *)
Definition ident : Type := list (svar * svar).

Section Model.

Variable ids : ident.

(** Where a variable is redirected, if it is. *)
Fixpoint redir (l : ident) (x : svar) : option svar :=
  match l with
  | [] => None
  | (y, r) :: l' => if svar_eqb y x then Some r else redir l' x
  end.

(** Which index of [h] a representative stands for. *)
Fixpoint back (l : ident) (h : lexp) (v : svar) : option nat :=
  match l with
  | [] => None
  | (y, r) :: l' => if lexp_eqb (fst y) h && svar_eqb r v then Some (snd y) else back l' h v
  end.

Definition fseq (h : lexp) (i : nat) : svar :=
  match redir ids (h, i) with Some r => r | None => (h, i) end.

Definition fpos (h : lexp) (v : svar) : option nat :=
  match back ids h v with
  | Some i => Some i
  | None => if lexp_eqb (fst v) h then match redir ids v with None => Some (snd v) | Some _ => None end else None
  end.

(** The conditions:
    - a representative is a variable of another label, not redirected
      itself;
    - each variable is redirected at most once, and two variables of one
      label never to the same representative. *)
Definition wf_ids : Prop :=
  (forall x r, In (x, r) ids -> fst r <> fst x /\ redir ids r = None)
  /\ (forall x r, redir ids x = Some r -> In (x, r) ids)
  /\ (forall x r, In (x, r) ids -> redir ids x = Some r)
  /\ (forall x y r, In (x, r) ids -> In (y, r) ids -> fst x = fst y -> x = y).

Hypothesis Hwf : wf_ids.

Lemma redir_in l x r : redir l x = Some r -> In (x, r) l.
Proof.
  induction l as [|[y r'] l IH]; cbn [redir]; [discriminate|].
  destruct (svar_eqb y x) eqn:E; [intros H; injection H as <-; apply svar_eqb_eq in E; subst; left; reflexivity|].
  intros H; right; apply IH, H.
Qed.

Lemma back_in l h v i : back l h v = Some i -> In ((h, i), v) l.
Proof.
  induction l as [|[y r] l IH]; cbn [back]; [discriminate|].
  destruct (lexp_eqb (fst y) h && svar_eqb r v) eqn:E; [|intros H; right; apply IH, H].
  apply andb_true_iff in E; destruct E as [E1 E2]; apply lexp_eqb_eq in E1; apply svar_eqb_eq in E2; subst.
  intros H; injection H as <-; left; destruct y; reflexivity.
Qed.

Lemma back_none l h v : back l h v = None -> forall i, ~ In ((h, i), v) l.
Proof.
  induction l as [|[y r] l IH]; cbn [back]; [intros _ i []|].
  destruct (lexp_eqb (fst y) h && svar_eqb r v) eqn:E; [discriminate|].
  intros H i [E'|Hi]; [|exact (IH H i Hi)].
  injection E' as -> ->; cbn [fst] in E; rewrite (proj2 (lexp_eqb_eq h h) eq_refl), svar_eqb_refl in E; discriminate.
Qed.

Lemma fpos_seq h i : fpos h (fseq h i) = Some i.
Proof.
  destruct Hwf as (Hrep & Hr1 & Hr2 & Hinj).
  unfold fpos, fseq; destruct (redir ids (h, i)) as [r|] eqn:Er.
  - pose proof (Hr1 _ _ Er) as Hin.
    destruct (back ids h r) as [i'|] eqn:Eb.
    + pose proof (back_in _ _ _ _ Eb) as Hin'; f_equal.
      pose proof (Hinj _ _ _ Hin Hin' eq_refl) as E; injection E as ->; reflexivity.
    + exfalso; exact (back_none _ _ _ Eb i Hin).
  - destruct (back ids h (h, i)) as [i'|] eqn:Eb.
    + exfalso; destruct (Hrep _ _ (back_in _ _ _ _ Eb)) as [Hne _]; exact (Hne eq_refl).
    + cbn [fst snd]; rewrite (proj2 (lexp_eqb_eq h h) eq_refl), Er; reflexivity.
Qed.

Lemma fseq_pos h v i : fpos h v = Some i -> fseq h i = v.
Proof.
  destruct Hwf as (Hrep & Hr1 & Hr2 & Hinj).
  unfold fpos, fseq; destruct (back ids h v) as [i'|] eqn:Eb.
  - intros H; injection H as <-; rewrite (Hr2 _ _ (back_in _ _ _ _ Eb)); reflexivity.
  - destruct v as [g j]; cbn [fst snd].
    destruct (lexp_eqb g h) eqn:Eg; [|discriminate]; apply lexp_eqb_eq in Eg; subst g.
    destruct (redir ids (h, j)) eqn:Er; [discriminate|]; intros H; injection H as <-; rewrite Er; reflexivity.
Qed.

Definition fmodel : imodel := mk_imodel svar fseq fpos fpos_seq fseq_pos.

End Model.

(** ** Consistency with the facts *)

(** Every two variables made the same have labels the facts leave
    unordered. *)
Definition ids_unordered (F : order) (ids : ident) : Prop :=
  (forall x r, In (x, r) ids -> lt_known F (fst x) (fst r) = false /\ lt_known F (fst r) (fst x) = false)
  /\ (forall x y r, In (x, r) ids -> In (y, r) ids ->
        lt_known F (fst x) (fst y) = false).

(** If the facts order a label against itself there is no model at
    all, so that is ruled out by hypothesis. *)
Lemma fmodel_consistent F ids (Hwf : wf_ids ids) :
  (forall a, lt_known F a a = false) ->
  ids_unordered F ids -> consistent F (fmodel ids Hwf).
Proof.
  intros Hirr [Hu1 Hu2] a b i Hab; cbn [mpos mseq fmodel].
  destruct Hwf as (Hrep & Hr1 & Hr2 & Hinj) eqn:EW.
  unfold fpos, fseq; destruct (redir ids (a, i)) as [r|] eqn:Er.
  - pose proof (Hr1 _ _ Er) as Hin.
    destruct (back ids b r) as [j|] eqn:Eb.
    + pose proof (back_in _ _ _ _ Eb) as Hin'; exfalso.
      pose proof (Hu2 _ _ _ Hin Hin') as H; cbn [fst] in H; rewrite Hab in H; discriminate.
    + destruct (lexp_eqb (fst r) b) eqn:Eg; [|reflexivity].
      apply lexp_eqb_eq in Eg; exfalso.
      destruct (Hu1 _ _ Hin) as [H _]; cbn [fst] in H; rewrite Eg, Hab in H; discriminate.
  - destruct (back ids b (a, i)) as [j|] eqn:Eb.
    + pose proof (back_in _ _ _ _ Eb) as Hin; exfalso.
      destruct (Hu1 _ _ Hin) as [_ H]; cbn [fst] in H; rewrite Hab in H; discriminate.
    + cbn [fst]; destruct (lexp_eqb a b) eqn:Eg; [|reflexivity].
      apply lexp_eqb_eq in Eg; subst b; exfalso.
      rewrite Hirr in Hab; discriminate.
Qed.

(** The disjoint model: every label its own sequence. *)
Lemma wf_nil : wf_ids [].
Proof.
  repeat split; cbn; try tauto; intros; discriminate.
Qed.

Definition dmodel : imodel := fmodel [] wf_nil.
