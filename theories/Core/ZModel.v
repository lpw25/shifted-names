(** * Zero-set models

    The model of [docs/zero-sets.md].  A label's index 0 is a *set* of
    variables, not one variable:

    - [zsh h] is [⟦ \ h ⟧], an injection; the variables it misses are
      the index-0 variables of [h] ([zat0 h]);
    - each label has one *designated* index-0 variable [zdes h], what a
      target naming [h] means when nothing more specific is meant;
    - a target naming [g], read by an entry that consumed [v], means
      [v] itself (shifted along [g]) when [v] is index 0 of [g], and the
      designated variable otherwise;
    - labels the facts order commute, have disjoint index-0 sets, map
      each other's index-0 sets onto themselves, and fix each other's
      designated variables.  They may move the other index-0 variables
      among themselves.

    Interleaved models are the case where every index-0 set has one
    element ([iz], [iz_cons]).  The examples [HEtaGap.r1_r2] and the one
    with facts in [docs/separation.md] are identities in interleaved
    models and not here. *)

From Stdlib Require Import String Arith List Bool.
From ShiftedNames.Core Require Import Label Var Normalise GEval IModel.
Import ListNotations.

Record zmodel : Type := mk_zmodel {
  zV : Type;
  zsh : lexp -> zV -> zV;
  zun : lexp -> zV -> zV;
  zat0 : lexp -> zV -> bool;
  zdes : lexp -> zV;
  zun_zsh : forall h y, zun h (zsh h y) = y;
  zat0_zsh : forall h y, zat0 h (zsh h y) = false;
  zsh_zun : forall h v, zat0 h v = false -> zsh h (zun h v) = v;
  zat0_des : forall h, zat0 h (zdes h) = true;
  (** Variables on the bound label. *)
  zbnd : zV -> bool
}.

Arguments zsh {_} _ _.
Arguments zun {_} _ _.
Arguments zat0 {_} _ _.
Arguments zdes {_} _.
Arguments zbnd {_} _.

(** Consistency with the facts. *)
Definition zcons (F : order) (M : zmodel) : Prop :=
  (** labels the facts order *)
  (forall g h, lt_known F g h = true ->
     (forall y, @zsh M g (zsh h y) = zsh h (zsh g y))
     /\ (forall y, @zat0 M h (zsh g y) = zat0 h y) /\ (forall y, @zat0 M g (zsh h y) = zat0 g y)
     /\ (forall v, @zat0 M g v = true -> zat0 h v = false)
     /\ @zsh M g (zdes h) = zdes h /\ @zsh M h (zdes g) = zdes g)
  (** the bound label moves only its own variables, and named steps keep
      them its own *)
  /\ (forall v, @zat0 M LNone v = true -> zbnd v = true)
  /\ (forall v, @zbnd M v = false -> zsh LNone v = v)
  /\ (forall v, @zbnd M (zsh LNone v) = zbnd v)
  /\ (forall h v, h <> LNone -> @zbnd M (zsh h v) = zbnd v).

Section Results.

Variable M : zmodel.
Local Notation V := (zV M) (only parsing).

Inductive zres : Type :=
| ZVar (v : V)
| ZTerm (u : nat) (b : option nat) (k : V -> zres)
| ZStuck (a : nat) (z : V) (k : V -> zres).

Fixpoint iter (h : lexp) (n : nat) (v : V) : V :=
  match n with 0 => v | S n => @zsh M h (iter h n v) end.

(** The variable a target naming [gᵢ] means, read by an entry that
    consumed [v]. *)
Definition zread (g : lexp) (i : nat) (v : V) : V :=
  if @zat0 M g v then iter g i v else iter g i (zdes g).

Fixpoint ztv (v : V) (t : texp) : option V :=
  match t with
  | TVarE h i => Some (zread h i v)
  | TBindE _ _ => None
  | TShiftE h t => option_map (zsh h) (ztv v t)
  end.

Fixpoint za (a : aexp) (K : V -> zres) (v : V) {struct a} : zres :=
  match a with
  | AId => K v
  | AAtom n => ZStuck n v K
  | ACompose a b => za b (za a K) v
  | AOuter h a => za a (fun y => K (zsh h y)) v
  | AInner h t a => if zat0 h v then zt v t K else za a K (zun h v)
  | ALift h a => if zat0 h v then K v else za a (fun y => K (zsh h y)) (zun h v)
  end
with zt (v : V) (t : texp) (K : V -> zres) : zres :=
  match t with
  | TVarE h i => K (zread h i v)
  | TBindE u q => ZTerm u (fpb q) (zp q K)
  | TShiftE h t => match ztv v t with Some w => K (zsh h w) | None => zt v t K end
  end
with zp (q : pexp) (K : V -> zres) : V -> zres :=
  match q with
  | PId | PAtom _ => K
  | PComp a q => zp q (za a K)
  | PShift h q => zp q (fun y => K (zsh h y))
  end.

End Results.

Arguments iter {M} h n v.
Arguments zread {M} g i v.
Arguments za {M} a K v.
Arguments zt {M} v t K.
Arguments zp {M} q K v.
Arguments ZVar {M} v.
Arguments ZTerm {M} u b k.
Arguments ZStuck {M} a z k.

(** ** Laws every zero-set model satisfies *)

Section Laws.

Variable M : zmodel.

(** The identity renaming [⟦ h as a | Γ \ h as a | Γ ⟧ = ⟦⟧]: an index-0
    variable of [h] is sent to itself, whichever it is. *)
Lemma za_id_rename h (K : zV M -> zres M) v : za (AInner h (TVarE h 0) (AOuter h AId)) K v = K v.
Proof.
  cbn [za zt]; unfold zread; destruct (zat0 h v) eqn:E; cbn [iter]; [reflexivity|].
  f_equal; apply zsh_zun, E.
Qed.

(** Cancellation: [⟦ \ h ⟧] then an entry on [h]. *)
Lemma za_cancel h t a (K : zV M -> zres M) v : za (ACompose (AInner h t a) (AOuter h AId)) K v = za a K v.
Proof. cbn [za]; rewrite zat0_zsh, zun_zsh; reflexivity. Qed.

(** Two tests with the same target commute, whatever their labels: when
    both apply, the target is read at the same variable. *)
Definition ztest (h : lexp) (val : zV M -> zres M) (K : zV M -> zres M) (v : zV M) : zres M :=
  if @zat0 M h v then val v else K v.

Lemma ztest_comm g h val K v : ztest g val (ztest h val K) v = ztest h val (ztest g val K) v.
Proof. unfold ztest; destruct (zat0 g v), (zat0 h v); reflexivity. Qed.

End Laws.

(** ** Ordered labels *)

Section Ordered.

Variables (F : order) (M : zmodel) (g h : lexp).
Hypothesis HM : zcons F M.
Hypothesis Hgh : lt_known F g h = true.

Let H := proj1 HM g h Hgh.

Lemma z_comm y : @zsh M g (zsh h y) = zsh h (zsh g y).
Proof. apply H. Qed.

Lemma z_at0_h y : @zat0 M h (zsh g y) = zat0 h y.
Proof. apply H. Qed.

Lemma z_at0_g y : @zat0 M g (zsh h y) = zat0 g y.
Proof. apply H. Qed.

Lemma z_disj v : @zat0 M g v = true -> zat0 h v = false.
Proof. apply H. Qed.

(** The moves of entries commute with the weakenings of the other label,
    away from index 0. *)
Lemma z_un_sh y : @zat0 M h y = false -> @zun M h (zsh g y) = zsh g (zun h y).
Proof.
  intros E; rewrite <- (zsh_zun M h y E) at 1; rewrite z_comm, zun_zsh; reflexivity.
Qed.

Lemma z_at0_h_un y : @zat0 M g y = false -> @zat0 M h (zun g y) = zat0 h y.
Proof. intros E; rewrite <- (zsh_zun M g y E) at 2; rewrite z_at0_h; reflexivity. Qed.

(** Reading a target naming [g] commutes with steps on [h]: this is what
    lets a lookup of [gᵢ] pass a step on [h] unchanged. *)
Lemma iter_comm n v : @zsh M h (iter g n v) = iter g n (zsh h v).
Proof. induction n as [|n IH]; cbn [iter]; [reflexivity|]; rewrite <- IH, z_comm; reflexivity. Qed.

Lemma zread_sh i v : @zsh M h (zread g i v) = zread g i (zsh h v).
Proof.
  unfold zread; rewrite z_at0_g; destruct (zat0 g v); rewrite iter_comm; [reflexivity|].
  rewrite (proj2 (proj2 (proj2 (proj2 (proj2 H))))); reflexivity.
Qed.

End Ordered.

(** ** The bound label *)

Section Bound.

Variables (F : order) (M : zmodel).
Hypothesis HM : zcons F M.

Lemma z_bound_fix v : @zbnd M v = false -> zsh LNone v = v.
Proof. apply HM. Qed.

Lemma z_bound_at0 v : @zbnd M v = false -> zat0 LNone v = false.
Proof.
  intros E; destruct (zat0 LNone v) eqn:E0; [|reflexivity].
  rewrite (proj1 (proj2 HM) v E0) in E; discriminate.
Qed.

End Bound.

(** ** Interleaved models are zero-set models *)

Section Embed.

Variable M : imodel.

Definition iz : zmodel :=
  mk_zmodel (mV M) msh mush mat0 (fun h => mseq h 0)
    (mush_msh M) (mat0_msh M) (msh_mush M)
    (fun h => match mat0 h (mseq h 0) as b return mat0 h (mseq h 0) = b -> b = true with
              | true => fun _ => eq_refl
              | false => fun E => ltac:(unfold mat0 in E; rewrite mpos_seq in E; discriminate)
              end eq_refl)
    (fun v => match mpos LNone v with Some _ => true | None => false end).

(** The target reading agrees with the interleaved one: index 0 of [g] is
    the one variable [g₀]. *)
Lemma iz_read g i v : @zread iz g i v = mseq g i.
Proof.
  assert (It : forall n w, @iter iz g n w = match mpos g w with Some j => mseq g (n + j) | None => w end).
  { induction n as [|n IH]; intros w; cbn [iter].
    - destruct (mpos g w) as [j|] eqn:E; [cbn; symmetry; apply mseq_pos, E|reflexivity].
    - rewrite IH; cbn; unfold msh; destruct (mpos g w) as [j|] eqn:E; [rewrite mpos_seq; reflexivity|rewrite E; reflexivity]. }
  unfold zread; cbn [zat0 iz zdes]; destruct (mat0 g v) eqn:E.
  - rewrite (mat0_eq M g v E), It, mpos_seq, Nat.add_0_r; reflexivity.
  - rewrite It, mpos_seq, Nat.add_0_r; reflexivity.
Qed.

End Embed.

Section EmbedLaws.

Variables (F : order) (M : imodel).

(** Interleaved models consistent with the facts are zero-set models
    consistent with them. *)
Lemma iz_cons : consistent F M -> (forall a, lt_known F a LNone = true \/ a = LNone) -> zcons F (iz M).
Proof.
  intros HM Hb.
  assert (Off : forall a b (v : mV M), lt_known F a b = true -> mpos a v <> None -> mpos b v = None).
  { intros a b v Hab Ha; destruct (mpos a v) as [i|] eqn:E; [|contradiction].
    rewrite <- (mseq_pos _ _ _ _ E); apply (HM a b i Hab). }
  assert (Off' : forall a b (v : mV M), lt_known F a b = true -> mpos b v <> None -> mpos a v = None).
  { intros a b v Hab Hb'; destruct (mpos b v) as [i|] eqn:E; [|contradiction].
    rewrite <- (mseq_pos _ _ _ _ E); apply (consistent_sym M F a b i HM Hab). }
  assert (Pres : forall a b (y : mV M), lt_known F a b = true -> mpos b (msh a y) = mpos b y).
  { intros a b y Hab; unfold msh; destruct (mpos a y) as [i|] eqn:E; [|reflexivity].
    rewrite (HM a b (S i) Hab), (Off a b y Hab ltac:(rewrite E; discriminate)); reflexivity. }
  assert (Pres' : forall a b (y : mV M), lt_known F a b = true -> mpos a (msh b y) = mpos a y).
  { intros a b y Hab; unfold msh; destruct (mpos b y) as [i|] eqn:E; [|reflexivity].
    rewrite (consistent_sym M F a b (S i) HM Hab), (Off' a b y Hab ltac:(rewrite E; discriminate)); reflexivity. }
  split; [|split; [|split; [|split]]]; cbn [zsh zat0 zdes zbnd iz].
  - intros g h Hgh; repeat split.
    + intros y; apply (msh_comm M F g h y HM Hgh).
    + intros y; unfold mat0; rewrite Pres; auto.
    + intros y; unfold mat0; rewrite Pres'; auto.
    + intros v Ev; unfold mat0 in *; destruct (mpos g v) as [[|i]|] eqn:E; try discriminate.
      rewrite (Off g h v Hgh ltac:(rewrite E; discriminate)); reflexivity.
    + unfold msh; rewrite (consistent_sym M F g h 0 HM Hgh); reflexivity.
    + unfold msh; rewrite (HM g h 0 Hgh); reflexivity.
  - intros v; unfold mat0; destruct (mpos LNone v) as [[|i]|]; congruence.
  - intros v; unfold msh; destruct (mpos LNone v); congruence.
  - intros v; unfold msh; destruct (mpos LNone v) as [i|] eqn:E; [rewrite mpos_seq; reflexivity|rewrite E; reflexivity].
  - intros h v Hh; destruct (Hb h) as [Hl|Hl]; [|contradiction].
    unfold msh; destruct (mpos h v) as [i|] eqn:E; [|reflexivity].
    rewrite (HM h LNone (S i) Hl), (Off h LNone v Hl ltac:(rewrite E; discriminate)); reflexivity.
Qed.

(** And with the same meaning. *)
Inductive zrel : zres (iz M) -> mres M -> Prop :=
| zrel_var v : zrel (ZVar v) (MVar v)
| zrel_term u b k k' : (forall y, zrel (k y) (k' y)) -> zrel (ZTerm u b k) (MTerm u b k')
| zrel_stuck a z k k' : (forall y, zrel (k y) (k' y)) -> zrel (ZStuck a z k) (MStuck a z k').

Lemma iz_tv v t : @ztv (iz M) v t = mtv t.
Proof. induction t as [h i|u q|h t IH]; cbn; [rewrite iz_read|reflexivity|rewrite IH]; reflexivity. Qed.

Fixpoint iz_za (a : aexp) : forall K K', (forall y, zrel (K y) (K' y)) -> forall v, zrel (@za (iz M) a K v) (ma a K' v)
with iz_zt (t : texp) : forall K K', (forall y, zrel (K y) (K' y)) -> forall v, zrel (@zt (iz M) v t K) (mt t K')
with iz_zp (q : pexp) : forall K K', (forall y, zrel (K y) (K' y)) -> forall v, zrel (@zp (iz M) q K v) (mp q K' v).
Proof.
  - destruct a as [|n|a1 a2|h a1|h t a1|h a1]; intros K K' HK v; cbn [za ma].
    + apply HK.
    + apply zrel_stuck, HK.
    + apply iz_za, (iz_za a1 _ _ HK).
    + apply iz_za; intros y; apply HK.
    + cbn [zat0 iz]; destruct (mat0 h v); [apply iz_zt, HK|apply iz_za, HK].
    + cbn [zat0 iz]; destruct (mat0 h v); [apply HK|apply iz_za; intros y; apply HK].
  - destruct t as [h i|u q|h t1]; intros K K' HK v; cbn [zt mt].
    + rewrite iz_read; apply HK.
    + apply zrel_term; intros y; apply iz_zp, HK.
    + rewrite iz_tv; destruct (mtv t1); [apply HK|apply iz_zt, HK].
  - destruct q as [|n|a1 q1|h q1]; intros K K' HK v; cbn [zp mp].
    + apply HK.
    + apply HK.
    + apply iz_zp; intros y; apply iz_za, HK.
    + apply iz_zp; intros y; apply HK.
Qed.

End EmbedLaws.
