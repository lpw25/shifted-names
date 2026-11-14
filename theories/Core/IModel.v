(** * Interleaved models

    The models the normaliser is specified against
    ([docs/normaliser-spec.md]).  A label denotes an infinite sequence of
    distinct variables, which is what [h₀, h₁, …] mean.  Labels the facts
    order have disjoint sequences; nothing else is assumed, so labels that
    are not ordered may share variables in any arrangement.

    Adjustment, term and payload atoms are left free here: an adjustment
    atom applied to a variable is stuck, as in [Unique.fres].  The
    standard interpretations are the models where each label has its own
    sequence ([std]), and there the meaning is the free meaning
    [GEval.fa] ([std_fa]). *)

From Stdlib Require Import String Arith List Lia Bool.
From ShiftedNames.Core Require Import Label Var Normalise Unique GEval.
Import ListNotations.

(** ** Models *)

Record imodel : Type := mk_imodel {
  mV : Type;
  (** [mseq h i] is the variable [hᵢ]. *)
  mseq : lexp -> nat -> mV;
  (** [mpos h v] is [Some i] exactly when [v] is [hᵢ]. *)
  mpos : lexp -> mV -> option nat;
  mpos_seq : forall h i, mpos h (mseq h i) = Some i;
  mseq_pos : forall h v i, mpos h v = Some i -> mseq h i = v
}.

Arguments mseq {_} _ _.
Arguments mpos {_} _ _.

(** A model is consistent with the facts when labels they order have
    disjoint sequences.  The bound label is ordered against every named
    label ([lt_base]), so its sequence is disjoint from theirs. *)
Definition consistent (F : order) (M : imodel) : Prop :=
  forall a b i, lt_known F a b = true -> @mpos M b (@mseq M a i) = None.

(** ** Results *)

Section Results.

Variable M : imodel.
Local Notation V := (mV M) (only parsing).

Inductive mres : Type :=
| MVar (v : V)
| MTerm (u : nat) (b : option nat) (k : V -> mres)
| MStuck (a : nat) (z : V) (k : V -> mres).

(** A variable is named when it is not a bound variable. *)
Definition mnamed (y : V) : Prop := @mpos M LNone y = None.

(** Results that agree; a term without a payload atom is compared on
    named variables only, as [Unique.feq]. *)
Fixpoint meq (f g : mres) : Prop :=
  match f, g with
  | MVar v, MVar v' => v = v'
  | MTerm u b k, MTerm u' b' k' =>
      u = u' /\ b = b' /\ forall y, (b = None -> mnamed y) -> meq (k y) (k' y)
  | MStuck a z k, MStuck a' z' k' => a = a' /\ z = z' /\ forall y, meq (k y) (k' y)
  | _, _ => False
  end.

Lemma meq_refl f : meq f f.
Proof. induction f as [v|u b k IH|a z k IH]; cbn [meq]; repeat split; auto. Qed.

Lemma meq_sym f : forall g, meq f g -> meq g f.
Proof.
  induction f as [v|u b k IH|a z k IH]; intros [v'|u' b' k'|a' z' k']; cbn [meq];
    try (intros []; fail).
  - intros ->; reflexivity.
  - intros [<- [<- H]]; repeat split; intros y Hy; apply IH, H, Hy.
  - intros [<- [<- H]]; repeat split; intros y; apply IH, H.
Qed.

Lemma meq_trans f : forall g h, meq f g -> meq g h -> meq f h.
Proof.
  induction f as [v|u b k IH|a z k IH]; intros [v'|u' b' k'|a' z' k'] [v''|u'' b'' k''|a'' z'' k''];
    cbn [meq]; try (intros []; fail); try (intros _ []; fail).
  - intros -> ->; reflexivity.
  - intros [<- [<- H]] [<- [<- H']]; repeat split; intros y Hy; apply (IH y (k' y)); [apply H, Hy|apply H', Hy].
  - intros [<- [<- H]] [<- [<- H']]; repeat split; intros y; apply (IH y (k' y)); [apply H|apply H'].
Qed.

(** ** Operations on one label

    [msh h] is [⟦ \ h ⟧] on variables: [hᵢ] to [hᵢ₊₁], every other
    variable alone.  [mush h] is its partial inverse, and [mat0 h v] tests
    whether [v] is [h₀]. *)

Definition msh (h : lexp) (y : V) : V :=
  match @mpos M h y with Some i => @mseq M h (S i) | None => y end.

Definition mush (h : lexp) (y : V) : V :=
  match @mpos M h y with Some (S i) => @mseq M h i | _ => y end.

Definition mat0 (h : lexp) (v : V) : bool :=
  match @mpos M h v with Some 0 => true | _ => false end.

(** The variable a target names, when it names one. *)
Fixpoint mtv (t : texp) : option V :=
  match t with
  | TVarE h i => Some (@mseq M h i)
  | TBindE _ _ => None
  | TShiftE h t => option_map (msh h) (mtv t)
  end.

(** ** The meaning of expressions

    [ma a K]: [a], then [K]; as [GEval.fa], with the model's sequences in
    place of label comparisons. *)

Fixpoint ma (a : aexp) (K : V -> mres) (v : V) {struct a} : mres :=
  match a with
  | AId => K v
  | AAtom n => MStuck n v K
  | ACompose a b => ma b (ma a K) v
  | AOuter h a => ma a (fun y => K (msh h y)) v
  | AInner h t a => if mat0 h v then mt t K else ma a K (mush h v)
  | ALift h a => if mat0 h v then K v else ma a (fun y => K (msh h y)) (mush h v)
  end
with mt (t : texp) (K : V -> mres) : mres :=
  match t with
  | TVarE h i => K (@mseq M h i)
  | TBindE u p => MTerm u (fpb p) (mp p K)
  | TShiftE h t => match mtv t with Some w => K (msh h w) | None => mt t K end
  end
with mp (p : pexp) (K : V -> mres) : V -> mres :=
  match p with
  | PId | PAtom _ => K
  | PComp a p => mp p (ma a K)
  | PShift h p => mp p (fun y => K (msh h y))
  end.

(** The meaning of an expression: [a], then nothing. *)
Definition mden (a : aexp) (v : V) : mres := ma a MVar v.

End Results.

Arguments MVar {M} v.
Arguments MTerm {M} u b k.
Arguments MStuck {M} a z k.
Arguments meq {M} f g.
Arguments mnamed {M} y.
Arguments msh {M} h y.
Arguments mush {M} h y.
Arguments mat0 {M} h v.
Arguments ma {M} a K v.
Arguments mt {M} t K.
Arguments mp {M} p K v.
Arguments mtv {M} t.
Arguments mden {M} a v.

(** Two expressions are equal when they agree in every model consistent
    with the facts. *)
Definition mequal (F : order) (a b : aexp) : Prop :=
  forall M, consistent F M -> forall v : mV M, meq (mden a v) (mden b v).

(** ** The standard interpretations *)

Section Std.

Variable lenv : list label.
Local Notation lden := (Normalise.lden lenv).

Definition std_pos (h : lexp) (v : rvar) : option nat :=
  if label_eqb (lden h) (v_label v) then Some (v_index v) else None.

Lemma std_pos_seq h i : std_pos h (mk_rvar (lden h) i) = Some i.
Proof. unfold std_pos; cbn [v_label v_index]; rewrite label_eqb_refl; reflexivity. Qed.

Lemma std_seq_pos h v i : std_pos h v = Some i -> mk_rvar (lden h) i = v.
Proof.
  unfold std_pos; destruct (label_eqb_spec (lden h) (v_label v)) as [E|_]; [|discriminate].
  intros H; injection H as <-; rewrite E; destruct v; reflexivity.
Qed.

(** Each label its own sequence: [hᵢ] is the variable [(lden h, i)]. *)
Definition std : imodel :=
  mk_imodel rvar (fun h i => mk_rvar (lden h) i) std_pos std_pos_seq std_seq_pos.

Lemma std_consistent F : facts_ok lenv F -> consistent F std.
Proof.
  intros HF a b i Hab; cbn [mpos mseq std]; unfold std_pos; cbn [v_label].
  pose proof (lt_known_sound lenv F HF a b Hab) as Hlt.
  destruct (label_eqb_spec (lden b) (lden a)) as [E|_]; [|reflexivity].
  rewrite E in Hlt; exfalso; exact (olabel_lt_irrefl _ Hlt).
Qed.

Lemma std_sh h y : @msh std h y = sh0 lenv h y.
Proof.
  destruct y as [l i]; unfold msh, sh0, shift_rvar; cbn [mpos mseq std v_label v_index]; unfold std_pos;
    cbn [v_label v_index].
  destruct (label_eqb_spec (lden h) l) as [E|E]; cbn; [|reflexivity].
  rewrite E; reflexivity.
Qed.

Lemma std_ush h y : @mush std h y = ush0 lenv h y.
Proof.
  destruct y as [l i]; unfold mush, ush0, unshift_rvar; cbn [mpos mseq std v_label v_index]; unfold std_pos;
    cbn [v_label v_index].
  destruct (label_eqb_spec (lden h) l) as [E|E]; cbn; [|reflexivity].
  destruct i as [|i]; cbn; [reflexivity|]; rewrite E; f_equal; lia.
Qed.

Lemma std_at0 h v : @mat0 std h v = rvar_eqb v (mk_rvar (lden h) 0).
Proof.
  unfold mat0, rvar_eqb; cbn [mpos std]; unfold std_pos; cbn [v_label v_index].
  rewrite label_eqb_sym; destruct (label_eqb (v_label v) (lden h)); cbn; [|reflexivity].
  destruct (v_index v); reflexivity.
Qed.

(** Free results and results of the standard model that agree. *)
Fixpoint fm (f : fres) (g : mres std) : Prop :=
  match f, g with
  | FVar v, MVar v' => v = v'
  | FTerm u b k, MTerm u' b' k' => u = u' /\ b = b' /\ forall y, fm (k y) (k' y)
  | FStuck a z k, MStuck a' z' k' => a = a' /\ z = z' /\ forall y, fm (k y) (k' y)
  | _, _ => False
  end.

Lemma std_tv t : @mtv std t = tvof lenv t.
Proof.
  induction t as [h i|u p|h t IH]; cbn [mtv tvof]; [reflexivity|reflexivity|].
  rewrite IH; destruct (tvof lenv t); cbn; [rewrite std_sh|]; reflexivity.
Qed.

(** In a standard interpretation, the meaning is the free meaning. *)
Theorem std_fa_all :
  (forall a K K', (forall y, fm (K y) (K' y)) -> forall v, fm (fa lenv a K v) (@ma std a K' v))
  /\ (forall t K K', (forall y, fm (K y) (K' y)) -> fm (ft lenv t K) (@mt std t K'))
  /\ (forall p K K', (forall y, fm (K y) (K' y)) -> forall v, fm (fp lenv p K v) (@mp std p K' v)).
Proof.
  apply exp_mind; intros; cbn [fa ft fp ma mt mp]; rewrite ?std_at0, ?std_tv.
  - apply H.
  - cbn [fm]; repeat split; exact H.
  - apply H0; intros y; apply H; exact H1.
  - apply H; intros y; rewrite std_sh; apply H0.
  - rewrite std_ush; destruct (rvar_eqb v (mk_rvar (lden h) 0)); [apply H; exact H1|apply H0; exact H1].
  - rewrite std_ush; destruct (rvar_eqb v (mk_rvar (lden h) 0)); [apply H0|].
    apply H; intros y; rewrite std_sh; apply H0.
  - apply H.
  - cbn [fm]; repeat split; intros y; apply H; exact H0.
  - destruct (tvof lenv t); [rewrite std_sh; apply H0|apply H; exact H0].
  - apply H.
  - apply H.
  - apply H0; intros y; apply H; exact H1.
  - apply H; intros y; rewrite std_sh; apply H0.
Qed.

End Std.

(** ** Laws every model satisfies *)

Section Laws.

Variable M : imodel.

Lemma mush_msh h y : @mush M h (msh h y) = y.
Proof.
  unfold mush, msh; destruct (mpos h y) as [i|] eqn:E; [|rewrite E; reflexivity].
  rewrite mpos_seq; apply mseq_pos, E.
Qed.

Lemma mat0_msh h y : @mat0 M h (msh h y) = false.
Proof.
  unfold mat0, msh; destruct (mpos h y) as [i|] eqn:E; [rewrite mpos_seq; reflexivity|rewrite E; reflexivity].
Qed.

Lemma msh_mush h v : @mat0 M h v = false -> @msh M h (mush h v) = v.
Proof.
  unfold mat0, mush, msh; destruct (mpos h v) as [[|i]|] eqn:E; try discriminate; intros _.
  - rewrite mpos_seq; apply mseq_pos, E.
  - rewrite E; reflexivity.
Qed.

Lemma mat0_eq h v : @mat0 M h v = true -> v = mseq h 0.
Proof.
  unfold mat0; destruct (mpos h v) as [[|i]|] eqn:E; try discriminate; intros _; symmetry; apply mseq_pos, E.
Qed.

(** The identity renaming: [⟦ h as a | Γ \ h as a | Γ ⟧ = ⟦⟧]. *)
Lemma ma_id_rename h (K : mV M -> mres M) v : ma (AInner h (TVarE h 0) (AOuter h AId)) K v = K v.
Proof.
  cbn [ma mt]; destruct (mat0 h v) eqn:E; [rewrite (mat0_eq h v E); reflexivity|].
  f_equal; apply msh_mush, E.
Qed.

(** Cancellation: [⟦ \ h ⟧ ⨾ ⟦ h := t | a ⟧ = a]. *)
Lemma ma_cancel h t a (K : mV M -> mres M) v : ma (ACompose (AInner h t a) (AOuter h AId)) K v = ma a K v.
Proof. cbn [ma]; rewrite mat0_msh, mush_msh; reflexivity. Qed.

(** Labels the facts order have disjoint sequences, both ways round. *)
Lemma consistent_sym F h g i : consistent F M -> lt_known F h g = true -> @mpos M h (mseq g i) = None.
Proof.
  intros HM Hhg; destruct (mpos h (mseq g i)) as [j|] eqn:E; [|reflexivity].
  pose proof (HM h g j Hhg) as D; rewrite (mseq_pos _ _ _ _ E), mpos_seq in D; discriminate.
Qed.

(** Weakenings on ordered labels commute. *)
Lemma msh_comm F h g y : consistent F M -> lt_known F h g = true -> @msh M h (msh g y) = msh g (msh h y).
Proof.
  intros HM Hhg; unfold msh.
  destruct (mpos g y) as [i|] eqn:Eg; cbn iota; destruct (mpos h y) as [j|] eqn:Eh; cbn iota.
  - pose proof (HM h g j Hhg) as D; rewrite (mseq_pos _ _ _ _ Eh), Eg in D; discriminate.
  - rewrite (consistent_sym F h g (S i) HM Hhg), Eg; reflexivity.
  - rewrite (HM h g (S j) Hhg); reflexivity.
  - rewrite Eg; reflexivity.
Qed.

End Laws.

(** ** An identity that holds only by a case split

    [L = ⟦ \ x ⟧ ⨾ ⟦ \ y ⟧ ⨾ ⟦ x := u; y := v ⟧] and
    [R = ⟦ \ y ⟧ ⨾ ⟦ \ x ⟧ ⨾ ⟦ y := v; x := u ⟧] are both the identity in
    every standard interpretation, by cases on whether [x = y].  With no
    facts, they differ in the model where [x = (A, B, C₂, …)] and
    [y = (B, A, C₂, …)]. *)

Section Example.

Definition ex_x : lexp := LAtom 0.
Definition ex_y : lexp := LAtom 1.

Definition ex_L : aexp :=
  ACompose (AInner ex_x (TBindE 0 PId) (AInner ex_y (TBindE 1 PId) AId))
    (ACompose (AOuter ex_y AId) (AOuter ex_x AId)).

Definition ex_R : aexp :=
  ACompose (AInner ex_y (TBindE 1 PId) (AInner ex_x (TBindE 0 PId) AId))
    (ACompose (AOuter ex_x AId) (AOuter ex_y AId)).

(** [y] uses [x]'s variables with the first two swapped; every other
    label has its own sequence. *)
Definition swap01 (i : nat) : nat := match i with 0 => 1 | 1 => 0 | _ => i end.
Definition ex_canon (h : lexp) : lexp := match h with LAtom 1 => LAtom 0 | _ => h end.
Definition ex_idx (h : lexp) (i : nat) : nat := match h with LAtom 1 => swap01 i | _ => i end.

Lemma ex_idx_inv h i : ex_idx h (ex_idx h i) = i.
Proof. destruct h as [| |[|[|n]]]; cbn; try reflexivity; destruct i as [|[|i]]; reflexivity. Qed.

Definition ex_pos (h : lexp) (v : lexp * nat) : option nat :=
  if lexp_eqb (ex_canon h) (fst v) then Some (ex_idx h (snd v)) else None.

Lemma ex_pos_seq h i : ex_pos h (ex_canon h, ex_idx h i) = Some i.
Proof.
  unfold ex_pos; cbn [fst snd]; rewrite (proj2 (lexp_eqb_eq _ _) eq_refl), ex_idx_inv; reflexivity.
Qed.

Lemma ex_seq_pos h v i : ex_pos h v = Some i -> (ex_canon h, ex_idx h i) = v.
Proof.
  unfold ex_pos; destruct (lexp_eqb (ex_canon h) (fst v)) eqn:E; [|discriminate].
  intros H; injection H as <-; apply lexp_eqb_eq in E; rewrite E, ex_idx_inv; destruct v; reflexivity.
Qed.

Definition ex_model : imodel :=
  mk_imodel (lexp * nat) (fun h i => (ex_canon h, ex_idx h i)) ex_pos ex_pos_seq ex_seq_pos.

Definition ex_facts : order := order_of [].

Lemma ex_lt_known a b : lt_known ex_facts a b = lt_base a b.
Proof.
  unfold lt_known, ex_facts; cbn.
  destruct a as [| |i], b as [| |j]; cbn; try reflexivity.
  all: try (unfold tab_get; destruct i; reflexivity).
  all: try (destruct j; reflexivity).
  all: destruct (is_less_than_label _ _); reflexivity.
Qed.


Lemma ex_consistent : consistent ex_facts ex_model.
Proof.
  intros a b i H; rewrite ex_lt_known in H; cbn [mpos mseq ex_model]; unfold ex_pos; cbn [fst].
  destruct (lexp_eqb (ex_canon b) (ex_canon a)) eqn:E; [|reflexivity]; exfalso.
  apply lexp_eqb_eq in E.
  destruct a as [|s|[|[|n]]], b as [|s'|[|[|n']]]; cbn in E, H; try discriminate; try congruence.
  all: injection E as ->; exact (label_lt_irrefl _ H).
Qed.

Theorem ex_differ : ~ meq (@mden ex_model ex_L (LAtom 0, 0)) (@mden ex_model ex_R (LAtom 0, 0)).
Proof. vm_compute; tauto. Qed.

(** In every standard interpretation the two agree. *)
Theorem ex_std_agree lenv v : meq (@mden (std lenv) ex_L v) (@mden (std lenv) ex_R v).
Proof.
  destruct v as [l i]; unfold mden, ex_L, ex_R; cbn [ma mt mp fpb].
  unfold mat0, mush, msh; cbn [mpos mseq std]; unfold std_pos; cbn [v_label v_index].
  generalize (Normalise.lden lenv ex_x) as lx; generalize (Normalise.lden lenv ex_y) as ly; intros ly lx.
  repeat (match goal with |- context [label_eqb ?a ?b] => destruct (label_eqb_spec a b); try subst end;
          cbn [v_label v_index] in * ).
  all: try congruence.
  all: destruct i as [|[|[|i]]]; cbn; repeat split; congruence.
Qed.

End Example.
