(** * Copied models

    A wider class of models than [IModel]'s interleaved models.  A label
    denotes not one sequence of variables but several disjoint copies,
    indexed by a *phase* [p]: [cseq h p i] is index [i] of copy [p] of
    [h].  An entry on [h] takes index 0 of every copy, and a variable
    named in its target is read in the copy of the variable it consumed.

    In an interleaved model, "[v] is [a]" and "[⟦ \ b ⟧ v] is [a]"
    together force [⟦ \ b ⟧] to fix [v], and so to fix [⟦ \ b ⟧ v]
    ([HEtaGap.r1_r2]).  Here [v] and [⟦ \ b ⟧ v] may be index 0 of two
    different copies of [a].

    This file states the models and proves, for them, the laws the
    normaliser [HNorm] and its eta pass [HEta] rely on.  The
    correspondence is in [docs/copied.md]. *)

From Stdlib Require Import String Arith List Bool.
From ShiftedNames.Core Require Import Label Var Normalise GEval.
Import ListNotations.

(** ** Models *)

Record cmodel : Type := mk_cmodel {
  cV : Type;
  (** [cseq h p i]: index [i] of copy [p] of [h]. *)
  cseq : lexp -> nat -> nat -> cV;
  (** [cpos h v = Some (p, i)] exactly when [v] is [cseq h p i]. *)
  cpos : lexp -> cV -> option (nat * nat);
  cpos_seq : forall h p i, cpos h (cseq h p i) = Some (p, i);
  cseq_pos : forall h v p i, cpos h v = Some (p, i) -> cseq h p i = v
}.

Arguments cseq {_} _ _ _.
Arguments cpos {_} _ _.

(** Consistent with the facts:
    - labels the facts order share no variable, in any copies;
    - when index 0 of two labels' copies is one variable, the copies
      have the same phase, so a variable named in a target means the
      same thing whichever of the two entries consumes it. *)
Definition ccons (F : order) (M : cmodel) : Prop :=
  (forall a b p i, lt_known F a b = true -> @cpos M b (@cseq M a p i) = None)
  /\ (forall h g p q, @cseq M h p 0 = @cseq M g q 0 -> p = q).

Section Results.

Variable M : cmodel.
Local Notation V := (cV M) (only parsing).

Inductive cres : Type :=
| CVar (v : V)
| CTerm (u : nat) (b : option nat) (k : V -> cres)
| CStuck (a : nat) (z : V) (k : V -> cres).

(** ** Operations on one label *)

Definition csh (h : lexp) (y : V) : V :=
  match @cpos M h y with Some (p, i) => @cseq M h p (S i) | None => y end.

Definition cush (h : lexp) (y : V) : V :=
  match @cpos M h y with Some (p, S i) => @cseq M h p i | _ => y end.

(** [Some p] when [v] is index 0 of copy [p] of [h]. *)
Definition cat0 (h : lexp) (v : V) : option nat :=
  match @cpos M h v with Some (p, 0) => Some p | _ => None end.

(** A target's variable, read in phase [p]. *)
Fixpoint ctv (p : nat) (t : texp) : option V :=
  match t with
  | TVarE h i => Some (@cseq M h p i)
  | TBindE _ _ => None
  | TShiftE h t => option_map (csh h) (ctv p t)
  end.

(** ** The meaning of expressions

    As [IModel.ma], except that an entry reads its target in the phase
    of the variable it consumes. *)

Fixpoint ca (a : aexp) (K : V -> cres) (v : V) {struct a} : cres :=
  match a with
  | AId => K v
  | AAtom n => CStuck n v K
  | ACompose a b => ca b (ca a K) v
  | AOuter h a => ca a (fun y => K (csh h y)) v
  | AInner h t a => match cat0 h v with Some p => ct p t K | None => ca a K (cush h v) end
  | ALift h a => match cat0 h v with Some _ => K v | None => ca a (fun y => K (csh h y)) (cush h v) end
  end
with ct (p : nat) (t : texp) (K : V -> cres) : cres :=
  match t with
  | TVarE h i => K (@cseq M h p i)
  | TBindE u q => CTerm u (fpb q) (cp q K)
  | TShiftE h t => match ctv p t with Some w => K (csh h w) | None => ct p t K end
  end
with cp (q : pexp) (K : V -> cres) : V -> cres :=
  match q with
  | PId | PAtom _ => K
  | PComp a q => cp q (ca a K)
  | PShift h q => cp q (fun y => K (csh h y))
  end.

Definition cden (a : aexp) (v : V) : cres := ca a CVar v.

End Results.

Arguments csh {M} h y.
Arguments cush {M} h y.
Arguments cat0 {M} h v.
Arguments ca {M} a K v.
Arguments ct {M} p t K.
Arguments cp {M} q K v.
Arguments CVar {M} v.
Arguments CTerm {M} u b k.
Arguments CStuck {M} a z k.
Arguments cden {M} a v.

(** ** Laws every model satisfies *)

Section Laws.

Variable M : cmodel.

Lemma cush_csh h y : @cush M h (csh h y) = y.
Proof.
  unfold cush, csh; destruct (cpos h y) as [[p i]|] eqn:E; [|rewrite E; reflexivity].
  rewrite cpos_seq; apply cseq_pos, E.
Qed.

Lemma cat0_csh h y : @cat0 M h (csh h y) = None.
Proof.
  unfold cat0, csh; destruct (cpos h y) as [[p i]|] eqn:E; [rewrite cpos_seq; reflexivity|rewrite E; reflexivity].
Qed.

Lemma csh_cush h v : @cat0 M h v = None -> @csh M h (cush h v) = v.
Proof.
  unfold cat0, cush, csh; destruct (cpos h v) as [[p [|i]]|] eqn:E; try discriminate; intros _.
  - rewrite cpos_seq; apply cseq_pos, E.
  - rewrite E; reflexivity.
Qed.

Lemma cat0_eq h v p : @cat0 M h v = Some p -> v = cseq h p 0.
Proof.
  unfold cat0; destruct (cpos h v) as [[q [|i]]|] eqn:E; try discriminate.
  intros H; injection H as <-; symmetry; apply cseq_pos, E.
Qed.

(** The identity renaming [⟦ h as a | Γ \ h as a | Γ ⟧ = ⟦⟧]: each copy's
    index 0 goes to itself. *)
Lemma ca_id_rename h (K : cV M -> cres M) v : ca (AInner h (TVarE h 0) (AOuter h AId)) K v = K v.
Proof.
  cbn [ca ct]; destruct (cat0 h v) as [p|] eqn:E; [rewrite (cat0_eq h v p E); reflexivity|].
  f_equal; apply csh_cush, E.
Qed.

(** Cancellation: [⟦ \ h ⟧] then an entry on [h]. *)
Lemma ca_cancel h t a (K : cV M -> cres M) v : ca (ACompose (AInner h t a) (AOuter h AId)) K v = ca a K v.
Proof. cbn [ca]; rewrite cat0_csh, cush_csh; reflexivity. Qed.

(** Lifting under [h] keeps each copy's index 0. *)
Lemma ca_lift_at0 h a (K : cV M -> cres M) v p : cat0 h v = Some p -> ca (ALift h a) K v = K v.
Proof. intros E; cbn [ca]; rewrite E; reflexivity. Qed.

End Laws.

(** ** Ordered labels

    Every step on [g] leaves alone the variables of a label [h] the facts
    order against [g], and keeps a variable's place on [h]. *)

Section Ordered.

Variables (F : order) (M : cmodel).
Hypothesis HM : ccons F M.

Definition ordered (g h : lexp) : bool := lt_known F g h || lt_known F h g.

Lemma ccons_off g h p i : ordered g h = true -> @cpos M g (@cseq M h p i) = None.
Proof.
  destruct HM as [Hd _]; unfold ordered; intros Ho.
  destruct (lt_known F h g) eqn:E1; [apply Hd, E1|].
  rewrite orb_false_r in Ho.
  destruct (cpos g (cseq h p i)) as [[q j]|] eqn:E; [|reflexivity].
  pose proof (Hd g h q j Ho) as D; rewrite (cseq_pos _ _ _ _ _ E), cpos_seq in D; discriminate.
Qed.

(** A variable on [h] is on no ordered [g]. *)
Lemma cpos_off g h y p i : ordered g h = true -> @cpos M h y = Some (p, i) -> @cpos M g y = None.
Proof. intros Ho E; rewrite <- (cseq_pos _ _ _ _ _ E); apply ccons_off, Ho. Qed.

Lemma csh_off g y : @cpos M g y = None -> @csh M g y = y.
Proof. unfold csh; intros E; rewrite E; reflexivity. Qed.

Lemma cush_off g y : @cpos M g y = None -> @cush M g y = y.
Proof. unfold cush; intros E; rewrite E; reflexivity. Qed.

Lemma cat0_off g y : @cpos M g y = None -> @cat0 M g y = None.
Proof. unfold cat0; intros E; rewrite E; reflexivity. Qed.

(** Steps on [g] keep a variable's place on an ordered [h]: they move
    only variables on [g], which are on no copy of [h], to variables on
    [g]. *)
Lemma cpos_csh g h y : ordered g h = true -> @cpos M h (csh g y) = @cpos M h y.
Proof.
  intros Ho; unfold csh; destruct (cpos g y) as [[p i]|] eqn:E; [|reflexivity].
  assert (Ho' : ordered h g = true) by (unfold ordered in *; rewrite orb_comm; exact Ho).
  rewrite (ccons_off h g p (S i) Ho').
  rewrite <- (cseq_pos _ _ _ _ _ E), (ccons_off h g p i Ho'); reflexivity.
Qed.

Lemma cpos_cush g h y : ordered g h = true -> @cpos M h (cush g y) = @cpos M h y.
Proof.
  intros Ho; unfold cush; destruct (cpos g y) as [[p [|i]]|] eqn:E; try reflexivity.
  assert (Ho' : ordered h g = true) by (unfold ordered in *; rewrite orb_comm; exact Ho).
  rewrite (ccons_off h g p i Ho').
  rewrite <- (cseq_pos _ _ _ _ _ E), (ccons_off h g p (S i) Ho'); reflexivity.
Qed.

Lemma cat0_csh_ord g h y : ordered g h = true -> @cat0 M h (csh g y) = @cat0 M h y.
Proof. intros Ho; unfold cat0; rewrite (cpos_csh g h y Ho); reflexivity. Qed.

Lemma cat0_cush_ord g h y : ordered g h = true -> @cat0 M h (cush g y) = @cat0 M h y.
Proof. intros Ho; unfold cat0; rewrite (cpos_cush g h y Ho); reflexivity. Qed.

(** Weakenings, and the moves of entries, on ordered labels commute. *)
Lemma csh_comm g h y : ordered g h = true -> @csh M g (csh h y) = csh h (csh g y).
Proof.
  intros Ho; assert (Ho' : ordered h g = true) by (unfold ordered in *; rewrite orb_comm; exact Ho).
  destruct (cpos g y) as [[p i]|] eqn:Eg.
  - rewrite (csh_off h y (cpos_off h g y p i Ho' Eg)).
    rewrite (csh_off h (csh g y)); [reflexivity|].
    rewrite (cpos_csh g h y Ho); exact (cpos_off h g y p i Ho' Eg).
  - rewrite (csh_off g y Eg); apply csh_off; rewrite (cpos_csh h g y Ho'); exact Eg.
Qed.

Lemma cush_comm g h y : ordered g h = true -> @cush M g (cush h y) = cush h (cush g y).
Proof.
  intros Ho; assert (Ho' : ordered h g = true) by (unfold ordered in *; rewrite orb_comm; exact Ho).
  destruct (cpos g y) as [[p i]|] eqn:Eg.
  - rewrite (cush_off h y (cpos_off h g y p i Ho' Eg)).
    rewrite (cush_off h (cush g y)); [reflexivity|].
    rewrite (cpos_cush g h y Ho); exact (cpos_off h g y p i Ho' Eg).
  - rewrite (cush_off g y Eg); apply cush_off; rewrite (cpos_cush h g y Ho'); exact Eg.
Qed.

Lemma csh_cush_comm g h y : ordered g h = true -> @csh M g (cush h y) = cush h (csh g y).
Proof.
  intros Ho; assert (Ho' : ordered h g = true) by (unfold ordered in *; rewrite orb_comm; exact Ho).
  destruct (cpos g y) as [[p i]|] eqn:Eg.
  - rewrite (cush_off h y (cpos_off h g y p i Ho' Eg)).
    rewrite (cush_off h (csh g y)); [reflexivity|].
    rewrite (cpos_csh g h y Ho); exact (cpos_off h g y p i Ho' Eg).
  - rewrite (csh_off g y Eg); apply csh_off; rewrite (cpos_cush h g y Ho'); exact Eg.
Qed.

(** Named variables are on no copy of the bound label. *)
Lemma bound_off h p i : h <> LNone -> ordered h LNone = true -> @cpos M LNone (@cseq M h p i) = None.
Proof. intros _ Ho; apply ccons_off; unfold ordered in *; rewrite orb_comm; exact Ho. Qed.

End Ordered.

(** ** Tests with the same target commute

    The normal form's words carry absolute values: an entry's value is
    the final result, not passed through the rest of the word.  On such
    words, an entry on [h] followed by [⟦ \ h ⟧] is the test "if the
    variable is index 0 of some copy [p] of [h], the result is the value
    read in phase [p]; otherwise the variable passes on unchanged".  Two
    such tests with the same value commute, whatever the labels: when
    both apply, the variable is index 0 of both labels' copies, which
    then have one phase. *)

Section Tests.

Variables (F : order) (M : cmodel).
Hypothesis HM : ccons F M.

Definition ctest (h : lexp) (val : nat -> cres M) (K : cV M -> cres M) (v : cV M) : cres M :=
  match @cat0 M h v with Some p => val p | None => K v end.

Lemma ctest_comm g h val K v : ctest g val (ctest h val K) v = ctest h val (ctest g val K) v.
Proof.
  unfold ctest; destruct (cat0 g v) as [p|] eqn:Eg, (cat0 h v) as [q|] eqn:Eh; try reflexivity.
  destruct HM as [_ Hz].
  rewrite (Hz g h p q (eq_trans (eq_sym (cat0_eq M g v p Eg)) (cat0_eq M h v q Eh))); reflexivity.
Qed.

End Tests.

(** ** Interleaved models are copied models

    Each variable of an interleaved model is repeated once per phase,
    with no sharing between phases. *)

From ShiftedNames.Core Require Import IModel.

Section Embed.

Variable M : imodel.

Definition emb_seq (h : lexp) (p i : nat) : (mV M * nat) := (mseq h i, p).
Definition emb_pos (h : lexp) (v : mV M * nat) : option (nat * nat) :=
  match mpos h (fst v) with Some i => Some (snd v, i) | None => None end.

Lemma emb_pos_seq h p i : emb_pos h (emb_seq h p i) = Some (p, i).
Proof. unfold emb_pos, emb_seq; cbn [fst snd]; rewrite mpos_seq; reflexivity. Qed.

Lemma emb_seq_pos h v p i : emb_pos h v = Some (p, i) -> emb_seq h p i = v.
Proof.
  destruct v as [x q]; unfold emb_pos, emb_seq; cbn [fst snd].
  destruct (mpos h x) as [j|] eqn:E; [|discriminate].
  intros H; injection H as -> ->; rewrite (mseq_pos _ _ _ _ E); reflexivity.
Qed.

Definition emb : cmodel := mk_cmodel (mV M * nat) emb_seq emb_pos emb_pos_seq emb_seq_pos.

Lemma emb_ccons F : consistent F M -> ccons F emb.
Proof.
  intros HM; split.
  - intros a b p i Hab; cbn; unfold emb_pos, emb_seq; cbn [fst]; rewrite (HM a b i Hab); reflexivity.
  - intros h g p q E; cbn in E; unfold emb_seq in E; injection E as _ E; exact E.
Qed.

End Embed.

(** The embedding keeps the meaning: an input in phase [p] gives, in
    phase [p], what it gives in the interleaved model. *)

Section EmbedMeaning.

Variable M : imodel.
Local Notation E := (emb M).

Lemma emb_csh h x p : @csh E h (x, p) = (msh h x, p).
Proof. cbn; unfold csh, msh; cbn; unfold emb_pos; cbn [fst snd]; destruct (mpos h x); reflexivity. Qed.

Lemma emb_cush h x p : @cush E h (x, p) = (mush h x, p).
Proof. cbn; unfold cush, mush; cbn; unfold emb_pos; cbn [fst snd]; destruct (mpos h x) as [[|i]|]; reflexivity. Qed.

Lemma emb_cat0 h x p : @cat0 E h (x, p) = if mat0 h x then Some p else None.
Proof. unfold cat0, mat0; cbn; unfold emb_pos; cbn [fst snd]; destruct (mpos h x) as [[|i]|]; reflexivity. Qed.

Lemma emb_ctv p t : @ctv E p t = option_map (fun x => (x, p)) (mtv t).
Proof.
  induction t as [h i|u q|h t IH]; cbn; [reflexivity|reflexivity|].
  rewrite IH; destruct (mtv t); cbn; [rewrite emb_csh|]; reflexivity.
Qed.

(** Results that agree, phase by phase. *)
Inductive erel : nat -> cres E -> mres M -> Prop :=
| erel_var (x : mV M) p : erel p (@CVar E (x, p)) (MVar x)
| erel_term p u b (k' : cV E -> cres E) (k : mV M -> mres M) : (forall y q, erel q (k' (y, q)) (k y)) -> erel p (@CTerm E u b k') (MTerm u b k)
| erel_stuck p a (z : mV M) (k' : cV E -> cres E) (k : mV M -> mres M) : (forall y q, erel q (k' (y, q)) (k y)) -> erel p (@CStuck E a (z, p) k') (MStuck a z k).

Fixpoint emb_ca (a : aexp) : forall (K' : cV E -> cres E) (K : mV M -> mres M),
  (forall (y : mV M) q, erel q (K' (y, q)) (K y)) ->
  forall (x : mV M) p, erel p (ca a K' (x, p)) (ma a K x)
with emb_ct (t : texp) : forall (K' : cV E -> cres E) (K : mV M -> mres M),
  (forall (y : mV M) q, erel q (K' (y, q)) (K y)) ->
  forall p, erel p (ct p t K') (mt t K)
with emb_cp (q : pexp) : forall (K' : cV E -> cres E) (K : mV M -> mres M),
  (forall (y : mV M) r, erel r (K' (y, r)) (K y)) ->
  forall (x : mV M) p, erel p (cp q K' (x, p)) (mp q K x).
Proof.
  - destruct a as [|n|a1 a2|h a1|h t a1|h a1]; intros K' K HK x p; cbn [ca ma].
    + apply HK.
    + apply erel_stuck, HK.
    + apply (emb_ca a2), (fun y q => emb_ca a1 K' K HK y q).
    + apply (emb_ca a1); intros y q; rewrite emb_csh; apply HK.
    + rewrite emb_cat0; destruct (mat0 h x).
      * apply (emb_ct t), HK.
      * rewrite emb_cush; apply (emb_ca a1), HK.
    + rewrite emb_cat0; destruct (mat0 h x).
      * apply HK.
      * rewrite emb_cush; apply (emb_ca a1); intros y q; rewrite emb_csh; apply HK.
  - destruct t as [h i|u q|h t1]; intros K' K HK p; cbn [ct mt].
    + apply HK.
    + apply erel_term; intros y r; apply (emb_cp q), HK.
    + rewrite emb_ctv; destruct (mtv t1) as [w|]; cbn [option_map].
      * rewrite emb_csh; apply HK.
      * apply (emb_ct t1), HK.
  - destruct q as [|n|a1 q1|h q1]; intros K' K HK x p; cbn [cp mp].
    + apply HK.
    + apply HK.
    + apply (emb_cp q1); intros y r; apply (emb_ca a1), HK.
    + apply (emb_cp q1); intros y r; rewrite emb_csh; apply HK.
Qed.

Lemma emb_cden a (x : mV M) p : erel p (@cden E a (x, p)) (mden a x).
Proof. apply emb_ca; intros y q; constructor. Qed.

End EmbedMeaning.
