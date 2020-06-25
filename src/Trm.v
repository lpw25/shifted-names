Require Import String Omega Setoid Morphisms.
Require Import Morph Index Name Level Var.

Section Term.

  Context {trm : nset}.

  Variable unit : forall {N}, ivar N (@trm) N.

  Variable kleisli :
    forall {N M},
      ivar N (@trm) M ->
      morph (@trm) N (@trm) M.

  Definition open_ktrm n := open_ivar n (@unit 0).
  Definition open_trm n := kleisli (open_ktrm n).

  Definition close_ktrm n := close_ivar n (@unit 1).
  Definition close_trm n := kleisli (close_ktrm n).

  Definition weak_ktrm := weak_ivar (@unit 1).
  Definition weak_trm := kleisli weak_ktrm.

  Fixpoint weaken_trm (t : @trm 0) V : @trm (0 + V) :=
    match V with
    | 0 => t
    | S V => weak_trm V (weaken_trm t V)
    end.

  Lemma weaken_trm_extend t :
    pnset_extend (weaken_trm t) =p= morph_apply weak_trm (weaken_trm t).
  Proof.
    intro V; cbn; easy.
  Qed.

  Definition bind_ktrm t := bind_ivar (weaken_trm t) (@unit 0).
  Definition bind_trm t := kleisli (bind_ktrm t).

  Definition swap_ktrm := swap_ivar (@unit 2).
  Definition swap_trm := kleisli swap_ktrm.

  Hypothesis extensional :
    forall N M (f g : morph (@var) N (@trm) M),
      f =m= g ->
      kleisli f =m= kleisli g.

  Add Parametric Morphism {N M} : (@kleisli N M)
    with signature eq_morph ==> eq_morph
    as kleisli_mor.
    intros * Heq V n; unfold fst_ivar.
    apply extensional; easy.
  Qed.

  Hypothesis left_identity :
    forall N M (f : morph (@var) N (@trm) M),
      kleisli f @ unit =m= f.

  Hypothesis right_identity :
    forall N, kleisli (@unit N) =m= 1.

  Hypothesis associativity :
    forall N M L
      (f : morph (@var) N (@trm) M)
      (g : morph (@var) M (@trm) L),
      (kleisli g) @ (kleisli f)
      =m= kleisli (kleisli g @ f).

  Hypothesis unit_extend :
    forall N,
      morph_extend (@unit N) =m= unit.

  Hypothesis kleisli_extend :
    forall N M (f : morph (@var) N (@trm) M),
      morph_extend (kleisli f)
      =m= kleisli (morph_extend f).

  Hint Rewrite @left_identity @right_identity @associativity
       @unit_extend @kleisli_extend @weaken_trm_extend
       @morph_apply_compose @morph_apply_id
       @pair_ivar_compose_distribute @fst_ivar_compose_distribute
       @snd_ivar_compose_distribute @open_ivar_compose_distribute
       @close_ivar_compose_distribute @weak_ivar_compose_distribute
       @bind_ivar_compose_distribute @swap_ivar_compose_distribute
       @pair_ivar_extend @fst_ivar_extend
       @snd_ivar_extend @open_ivar_extend
       @close_ivar_extend @weak_ivar_extend
       @bind_ivar_extend @swap_ivar_extend
    : simpl_trms.

  (* Unfolding operations *)

  Lemma unfold_open_ktrm n :
    open_ktrm n = open_ivar n (@unit 0).
  Proof. easy. Qed.

  Lemma unfold_close_ktrm n :
    close_ktrm n = close_ivar n (@unit 1).
  Proof. easy. Qed.

  Lemma unfold_weak_ktrm :
    weak_ktrm = weak_ivar (@unit 1).
  Proof. easy. Qed.

  Lemma unfold_bind_ktrm t :
    bind_ktrm t = bind_ivar (weaken_trm t) (@unit 0).
  Proof. easy. Qed.

  Lemma unfold_swap_ktrm :
    swap_ktrm = swap_ivar (@unit 2).
  Proof. easy. Qed.

  Lemma unfold_open_trm n :
    open_trm n = kleisli (open_ktrm n).
  Proof. easy. Qed.

  Lemma unfold_close_trm n :
    close_trm n = kleisli (close_ktrm n).
  Proof. easy. Qed.

  Lemma unfold_weak_trm :
    weak_trm = kleisli weak_ktrm.
  Proof. easy. Qed.

  Lemma unfold_bind_trm t :
    bind_trm t = kleisli (bind_ktrm t).
  Proof. easy. Qed.

  Lemma unfold_swap_trm :
    swap_trm = kleisli swap_ktrm.
  Proof. easy. Qed.

  Hint Rewrite @unfold_open_ktrm @unfold_close_ktrm
       @unfold_weak_ktrm @unfold_bind_ktrm @unfold_swap_ktrm
       @unfold_open_trm @unfold_close_trm
       @unfold_weak_trm @unfold_bind_trm @unfold_swap_trm
    : unfold_trms.

  (* Folding operations *)

  Lemma fold_open_ktrm n :
    open_ivar n (@unit 0) = open_ktrm n.
  Proof. easy. Qed.

  Lemma fold_close_ktrm n :
    close_ivar n (@unit 1) = close_ktrm n.
  Proof. easy. Qed.

  Lemma fold_weak_ktrm :
    weak_ivar (@unit 1) = weak_ktrm.
  Proof. easy. Qed.

  Lemma fold_bind_ktrm t :
    bind_ivar (weaken_trm t) (@unit 0) = bind_ktrm t.
  Proof. easy. Qed.

  Lemma fold_swap_ktrm :
    swap_ivar (@unit 2) = swap_ktrm.
  Proof. easy. Qed.

  Lemma fold_open_trm n :
    kleisli (open_ktrm n) = open_trm n.
  Proof. easy. Qed.

  Lemma fold_close_trm n :
    kleisli (close_ktrm n) = close_trm n.
  Proof. easy. Qed.

  Lemma fold_weak_trm :
    kleisli weak_ktrm = weak_trm.
  Proof. easy. Qed.

  Lemma fold_bind_trm t :
    kleisli (bind_ktrm t) = bind_trm t.
  Proof. easy. Qed.

  Lemma fold_swap_trm :
    kleisli swap_ktrm = swap_trm.
  Proof. easy. Qed.

  Hint Rewrite @fold_open_ktrm @fold_close_ktrm
       @fold_weak_ktrm @fold_bind_ktrm @fold_swap_ktrm
       @fold_open_trm @fold_close_trm
       @fold_weak_trm @fold_bind_trm @fold_swap_trm
    : fold_trms.

  Ltac simpl_trms :=
    autorewrite with unfold_trms;
    autorewrite with simpl_trms;
    simpl_ivars;
    repeat progress
      (cbn;
       try (rewrite_strat topdown (hints simpl_trms));
       simpl_ivars);
    autorewrite with fold_trms.

End Term.


