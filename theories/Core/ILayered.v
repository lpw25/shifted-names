(** * Layered words in interleaved models

    The meaning of the normal-form syntax of [Normalise] (targets,
    segments, words) and of layered words ([Layered.lword]) in an
    interleaved model ([IModel]).  It is [Unique.fw] and
    [LayeredUnique.flw] with the model's sequences in place of label
    comparisons: a segment's entry for [h] applies to [v] when [v] is
    one of [h]'s variables.  In a standard interpretation the two agree
    ([std_mflw]). *)

From Stdlib Require Import String Arith List Lia Bool.
From ShiftedNames.Core Require Import Label Var Normalise Unique Layered LayeredUnique IModel.
Import ListNotations.

Section Meaning.

Variable M : imodel.
Local Notation V := (mV M) (only parsing).
Local Notation mres := (mres M) (only parsing).
Local Notation seqv := (@mseq M) (only parsing).
Local Notation posv := (@mpos M) (only parsing).

(** A lifted atom applied to [x], then [K]: a variable [hᵢ] with [i]
    below the lifts of [h] goes around the atom; any other variable is
    the atom's input, unshifted past the lifts, and the atom's outputs
    are shifted past them. *)

Fixpoint mlift (L : list (lexp * nat)) (x : V) : option (lexp * nat * nat) :=
  match L with
  | [] => None
  | (h, n) :: L' => match posv h x with Some i => Some (h, n, i) | None => mlift L' x end
  end.

Definition mshiftL (L : list (lexp * nat)) (y : V) : V :=
  match mlift L y with Some (h, n, j) => seqv h (j + n) | None => y end.

Definition mlatom (L : list (lexp * nat)) (a : nat) (K : V -> mres) (x : V) : mres :=
  match mlift L x with
  | Some (h, n, i) => if i <? n then K x else MStuck a (seqv h (i - n)) (fun y => K (mshiftL L y))
  | None => MStuck a x (fun y => K (mshiftL L y))
  end.

Fixpoint mw (w : word) (K : V -> mres) (v : V) {struct w} : mres :=
  match w with
  | WEnd Sg => ms Sg K v
  | WAtom Sg L a w' => mw w' (mlatom L a (fun y => ms Sg K y)) v
  | WLay Sg w' => mw w' (fun y => ms Sg K y) v
  end
with ms (Sg : seg) (K : V -> mres) (v : V) {struct Sg} : mres :=
  match Sg with
  | SNil => K v
  | SEnt h ts m r => match posv h v with Some i => mtl ts h m K i | None => ms r K v end
  end
with mtl (ts : tlist) (h : lexp) (m : nat) (K : V -> mres) (i : nat) {struct ts} : mres :=
  match ts with
  | TNil => K (seqv h (i + m))
  | TCons t r => match i with 0 => mtg t K | S i' => mtl r h m K i' end
  end
with mtg (t : ntgt) (K : V -> mres) {struct t} : mres :=
  match t with
  | NVar h j => K (seqv h j)
  | NBind u wp b => MTerm u b (fun x => mw wp K x)
  end.

Fixpoint mflw (l : lword) (K : V -> mres) (v : V) : mres :=
  match l with
  | [] => K v
  | LS s :: r => ms s (mflw r K) v
  | LA L a :: r => mlatom L a (mflw r K) v
  end.

(** What a word does, then nothing. *)
Definition mR (l : lword) : V -> mres := mflw l MVar.

End Meaning.

Arguments mlift {M} L x.
Arguments mshiftL {M} L y.
Arguments mlatom {M} L a K x.
Arguments mw {M} w K v.
Arguments ms {M} Sg K v.
Arguments mtl {M} ts h m K i.
Arguments mtg {M} t K.
Arguments mflw {M} l K v.
Arguments mR {M} l v.

(** ** The standard interpretations *)

Section Std.

Variable lenv : list label.
Local Notation lden := (Normalise.lden lenv).
Local Notation S := (std lenv) (only parsing).

(** Lifts whose labels denote distinct labels, as [Unique.lok] has
    them. *)
Definition lnd (L : list (lexp * nat)) : Prop := NoDup (map (fun p => lden (fst p)) L).

Lemma std_mlift L x : lnd L ->
  match @mlift S L x with
  | Some (h, n, i) => lden h = v_label x /\ i = v_index x /\ lc lenv (v_label x) L = n
  | None => lc lenv (v_label x) L = 0
  end.
Proof.
  unfold lnd; induction L as [|[h n] L IH]; intros Hnd; cbn [mlift Normalise.lc map fst] in *; [reflexivity|].
  inversion Hnd as [|? ? Hni Hnd']; subst.
  cbn [mpos std]; unfold std_pos.
  destruct (label_eqb_spec (lden h) (v_label x)) as [E|E].
  - repeat split; [exact E|].
    assert (H0 : lc lenv (v_label x) L = 0).
    { clear IH Hnd; induction L as [|[g k] L IHL]; [reflexivity|]; cbn [Normalise.lc].
      cbn [map fst] in Hni; apply Decidable.not_or in Hni; destruct Hni as [Hg Hni].
      rewrite (IHL Hni) by (inversion Hnd'; assumption).
      destruct (label_eqb_spec (lden g) (v_label x)) as [Eg|_]; [|reflexivity].
      exfalso; apply Hg; rewrite Eg, E; reflexivity. }
    rewrite H0; lia.
  - pose proof (IH Hnd') as H; destruct (@mlift (std lenv) L x) as [[[g k] i]|]; [|exact H].
    destruct H as (Hg & Hi & Hc); repeat split; try assumption; lia.
Qed.

Lemma std_mshiftL L y : lnd L -> @mshiftL S L y = shiftL lenv L y.
Proof.
  intros Hnd; unfold mshiftL, shiftL; pose proof (std_mlift L y Hnd) as H.
  destruct (@mlift (std lenv) L y) as [[[h n] j]|]; cbn [mseq std].
  - destruct H as (E & -> & <-); rewrite E; reflexivity.
  - rewrite H, Nat.add_0_r; destruct y; reflexivity.
Qed.

Lemma std_mlatom L a K K' x : lnd L -> (forall y, fm lenv (K y) (K' y)) ->
  fm lenv (latom lenv L a K x) (@mlatom S L a K' x).
Proof.
  intros Hnd HK; unfold mlatom, latom; pose proof (std_mlift L x Hnd) as H.
  destruct (@mlift (std lenv) L x) as [[[h n] i]|].
  - destruct H as (E & -> & Hc); rewrite Hc.
    destruct (v_index x <? n); [apply HK|].
    cbn [fm]; repeat split; [cbn [mseq std]; rewrite E; reflexivity|].
    intros y; rewrite std_mshiftL by exact Hnd; apply HK.
  - rewrite H; cbn [Nat.ltb Nat.leb]; cbn [fm]; repeat split.
    + destruct x; cbn; f_equal; lia.
    + intros y; rewrite std_mshiftL by exact Hnd; apply HK.
Qed.

(** Every lift list in a target, list, segment or word has distinct
    labels. *)
Fixpoint tnd (t : ntgt) : Prop :=
  match t with NVar _ _ => True | NBind _ w _ => wnd w end
with tlnd (ts : tlist) : Prop :=
  match ts with TNil => True | TCons t r => tnd t /\ tlnd r end
with snd' (s : seg) : Prop :=
  match s with SNil => True | SEnt _ ts _ r => tlnd ts /\ snd' r end
with wnd (w : word) : Prop :=
  match w with
  | WEnd s => snd' s
  | WAtom s L _ w => snd' s /\ lnd L /\ wnd w
  | WLay s w => snd' s /\ wnd w
  end.

Theorem std_mw_all :
  (forall t, tnd t -> forall K K', (forall y, fm lenv (K y) (K' y)) -> fm lenv (ft lenv t K) (@mtg S t K'))
  /\ (forall ts, tlnd ts -> forall h m K K', (forall y, fm lenv (K y) (K' y)) ->
        forall i, fm lenv (ftl lenv ts (lden h) m K i) (@mtl S ts h m K' i))
  /\ (forall s, snd' s -> forall K K', (forall y, fm lenv (K y) (K' y)) ->
        forall v, fm lenv (fs lenv s K v) (@ms S s K' v))
  /\ (forall w, wnd w -> forall K K', (forall y, fm lenv (K y) (K' y)) ->
        forall v, fm lenv (fw lenv w K v) (@mw S w K' v)).
Proof.
  apply nf_mind.
  - intros h j _ K K' HK; cbn [ft mtg]; apply HK.
  - intros u w IH b Hw K K' HK; cbn [ft mtg fm]; repeat split; intros y; apply IH; assumption.
  - intros _ h m K K' HK i; cbn [ftl mtl]; cbn [mseq std]; apply HK.
  - intros t IHt r IHr [Ht Hr] h m K K' HK [|i]; cbn [ftl mtl]; [apply IHt; assumption|apply IHr; assumption].
  - intros _ K K' HK v; cbn [fs ms]; apply HK.
  - intros h ts IHts m r IHr [Hts Hr] K K' HK v; cbn [fs ms]; cbn [mpos std]; unfold std_pos.
    destruct (label_eqb (lden h) (v_label v)) eqn:E.
    + apply IHts; assumption.
    + apply IHr; assumption.
  - intros s IH Hs K K' HK v; cbn [fw mw]; apply IH; assumption.
  - intros s IHs L a w IHw (Hs & HL & Hw) K K' HK v; cbn [fw mw]; apply IHw; [exact Hw|].
    intros y; apply std_mlatom; [exact HL|]; intros z; apply IHs; assumption.
  - intros s IHs w IHw (Hs & Hw) K K' HK v; cbn [fw mw]; apply IHw; [exact Hw|].
    intros y; apply IHs; assumption.
Qed.

(** Every step of a layered word has distinct lift labels. *)
Definition lwnd (l : lword) : Prop :=
  Forall (fun st => match st with LS s => snd' s | LA L _ => lnd L end) l.

(** In a standard interpretation, the meaning of a layered word is its
    free meaning. *)
Theorem std_mflw l : lwnd l -> forall K K', (forall y, fm lenv (K y) (K' y)) ->
  forall v, fm lenv (flw lenv l K v) (@mflw S l K' v).
Proof.
  induction l as [|st r IH]; intros Hl K K' HK v; cbn [flw mflw]; [apply HK|].
  inversion Hl as [|? ? Hst Hr]; subst; destruct st as [s|L a].
  - apply (proj1 (proj2 (proj2 std_mw_all)) s Hst); intros y; apply IH; assumption.
  - apply std_mlatom; [exact Hst|]; intros y; apply IH; assumption.
Qed.

End Std.
