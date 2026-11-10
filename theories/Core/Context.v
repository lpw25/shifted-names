(** * Typing contexts

    A context assigns a value (a type, say) to named variables.  It is
    built like a list, [∅] and [Γ & x ~ a], and looked up by shifted name:
    [Γ ∋ v ~ a].  It is stored per label, in a canonical trie of the
    label's entries, innermost first, so contexts that agree on every name
    are equal; in particular entries for different labels commute
    ([ctx_cons_comm]).

    A context morphism [Γ =[σ]=> Δ] says the adjustment [σ] renames every
    variable of [Γ] to one of [Δ] with the same value. *)

From Stdlib Require Import List String Bool StrictProp Arith Lia PArith.
From ShiftedNames.Core Require Import Trie Label Var Adjustment Scoped Indexed.
Import ListNotations.

Section Contexts.

Context {A : Type}.

(** ** Contexts *)

(** A key holding entries is the key of a named label. *)
Definition named_key (k : positive) : bool :=
  match key_label k with Some (Some s) => Pos.eqb (label_key (Some s)) k | _ => false end.

Definition ctx_okb (m : tree (list A)) : bool :=
  Trie.forallb (fun k l => named_key k && match l with [] => false | _ => true end) m.

Record ctx : Type := mk_ctx { ctx_tree : tree (list A); ctx_ok : Is_true_s (ctx_okb ctx_tree) }.

(** The entries of [x], innermost first. *)
Definition entries (Γ : ctx) (x : label) : list A :=
  match get (label_key (Some x)) (ctx_tree Γ) with Some l => l | None => [] end.

Lemma ctx_key (Γ : ctx) k l : get k (ctx_tree Γ) = Some l -> exists x, k = label_key (Some x) /\ l <> [].
Proof.
  intros E; pose proof (proj1 (forallb_spec _ _) (Is_true_s_elim (ctx_ok Γ)) k l E) as H; cbn in H.
  apply andb_true_iff in H as [Hk Hl]; unfold named_key in Hk.
  destruct (key_label k) as [[s|]|]; try discriminate.
  apply Pos.eqb_eq in Hk; exists s; split; [symmetry; exact Hk|destruct l; discriminate].
Qed.

Lemma ctx_eq (Γ Δ : ctx) : (forall x, entries Γ x = entries Δ x) -> Γ = Δ.
Proof.
  intros H; assert (E : ctx_tree Γ = ctx_tree Δ).
  { apply Trie.extensionality; intros k.
    destruct (get k (ctx_tree Γ)) as [l|] eqn:Ek.
    - destruct (ctx_key Γ k l Ek) as [x [-> Hl]].
      specialize (H x); unfold entries in H; rewrite Ek in H.
      destruct (get _ (ctx_tree Δ)); [congruence|contradiction].
    - destruct (get k (ctx_tree Δ)) as [l|] eqn:Ek'; [|reflexivity].
      destruct (ctx_key Δ k l Ek') as [x [-> Hl]].
      specialize (H x); unfold entries in H; rewrite Ek, Ek' in H; congruence. }
  destruct Γ as [m Hm], Δ as [n Hn]; cbn in E; subst n; reflexivity.
Qed.

Definition ctx_empty : ctx := mk_ctx Empty stt.

Lemma cons_ok (Γ : ctx) x a : Is_true_s (ctx_okb (set (label_key (Some x)) (a :: entries Γ x) (ctx_tree Γ))).
Proof.
  apply Is_true_s_intro, forallb_spec; intros k l; rewrite get_set.
  destruct (Pos.eqb_spec k (label_key (Some x))) as [->|].
  - intros E; injection E as <-; unfold named_key; rewrite key_label_spec, Pos.eqb_refl; reflexivity.
  - apply (proj1 (forallb_spec _ _) (Is_true_s_elim (ctx_ok Γ))).
Qed.

Definition ctx_cons (Γ : ctx) (x : label) (a : A) : ctx :=
  mk_ctx (set (label_key (Some x)) (a :: entries Γ x) (ctx_tree Γ)) (cons_ok Γ x a).

Lemma entries_empty x : entries ctx_empty x = [].
Proof. reflexivity. Qed.

Lemma entries_cons Γ x a y : entries (ctx_cons Γ x a) y = if String.eqb x y then a :: entries Γ x else entries Γ y.
Proof.
  unfold entries at 1; cbn [ctx_tree ctx_cons]; rewrite get_set, label_key_eqb; cbn [label_eqb].
  rewrite String.eqb_sym; destruct (String.eqb_spec x y) as [->|]; reflexivity.
Qed.

(** Entries for different names commute. *)
Theorem ctx_cons_comm Γ x a y b : x <> y -> ctx_cons (ctx_cons Γ x a) y b = ctx_cons (ctx_cons Γ y b) x a.
Proof.
  intros Hne; apply ctx_eq; intros z; repeat rewrite entries_cons.
  repeat match goal with |- context [String.eqb ?p ?q] => destruct (String.eqb_spec p q) end;
    subst; congruence.
Qed.

(** ** Lookup *)

(** [Γ ∋ v ~ a]: the variable [v], named [x₍ᵢ₎], has the value [a]. *)
Definition has {M} (Γ : ctx) (v : var M) (a : A) : Prop :=
  match var_raw v with
  | mk_rvar (Some x) i => nth_error (entries Γ x) i = Some a
  | mk_rvar None _ => False
  end.

Lemma has_here {M} Γ x a : has (M:=M) (ctx_cons Γ x a) (fvar x 0) a.
Proof. unfold has; cbn [var_raw fvar]; rewrite entries_cons, String.eqb_refl; reflexivity. Qed.

Lemma has_shift {M} Γ x a (v : var M) b : has Γ v b -> has (ctx_cons Γ x a) (vshift_free x v) b.
Proof.
  destruct v as [[[y|] i] Hv]; unfold has; cbn [var_raw]; [|contradiction].
  unfold vshift_free; cbn [var_raw]; unfold shift_rvar; cbn [v_label v_index label_eqb].
  destruct (String.eqb_spec x y) as [->|Hne]; cbn [andb Nat.leb].
  - rewrite entries_cons, String.eqb_refl; cbn [nth_error]; tauto.
  - rewrite entries_cons, (proj2 (String.eqb_neq _ _) Hne); tauto.
Qed.

Lemma has_cons_cases {M} Γ x a (v : var M) b :
  has (ctx_cons Γ x a) v b ->
  (var_raw v = mk_rvar (Some x) 0 /\ b = a) \/ (exists v', v = vshift_free x v' /\ has Γ v' b).
Proof.
  destruct v as [[[y|] i] Hv]; unfold has; cbn [var_raw]; [|contradiction].
  rewrite entries_cons; destruct (String.eqb_spec x y) as [<-|Hne].
  - destruct i as [|i]; cbn [nth_error]; intros H.
    + left; split; [reflexivity|congruence].
    + right; exists (mk_var (mk_rvar (Some x) i) stt); split; [apply var_eq; unfold vshift_free, shift_rvar; cbn;
        rewrite String.eqb_refl; reflexivity|exact H].
  - intros H; right; exists (mk_var (mk_rvar (Some y) i) Hv); split; [|exact H].
    apply var_eq; unfold vshift_free, shift_rvar; cbn; rewrite (proj2 (String.eqb_neq _ _) Hne); reflexivity.
Qed.

(** A property of every variable of a context. *)
Definition forall_has {M} (Γ : ctx) (P : var M -> A -> Prop) : Prop :=
  forall v a, has Γ v a -> P v a.

Lemma forall_has_cons {M} Γ x a (P : var M -> A -> Prop) :
  P (fvar x 0) a -> forall_has Γ (fun v b => P (vshift_free x v) b) -> forall_has (ctx_cons Γ x a) P.
Proof.
  intros H0 H v b Hv; destruct (has_cons_cases Γ x a v b Hv) as [[Ev ->]|[v' [-> Hv']]].
  - replace v with (fvar (M:=M) x 0) by (apply var_eq; exact (eq_sym Ev)); exact H0.
  - apply H, Hv'.
Qed.

Lemma forall_has_map {M} Γ (P Q : var M -> A -> Prop) :
  forall_has Γ P -> (forall v a, P v a -> Q v a) -> forall_has Γ Q.
Proof. intros H1 H2 v a H; apply H2, H1, H. Qed.

End Contexts.

Arguments ctx A : clear implicits.

Declare Scope ctx_scope.
Delimit Scope ctx_scope with ctx.
Bind Scope ctx_scope with ctx.
Notation "∅" := ctx_empty : ctx_scope.
Notation "Γ & x ~ a" := (ctx_cons Γ x a) (at level 50, left associativity) : ctx_scope.
Notation "Γ ∋ v ~ a" := (has Γ v a) (at level 60, v at next level).

(** ** Context morphisms *)

Section Morphisms.

Context {T A : Type}.

(** The variables an adjustment sends to variables. *)
Lemma apply_var_rename_inv {N M} (σ : adj T N M) (v : var N) (w : var M) :
  apply_var σ v = Rename w -> rapply (adj_raw σ) (var_raw v) = inl (var_raw w).
Proof.
  unfold apply_var; generalize (apply_wf σ v); unfold apply.
  destruct (rapply (adj_raw σ) (var_raw v)) as [w0|[u ρ]]; intros H E; [|discriminate].
  injection E as <-; reflexivity.
Qed.

(** [Γ =[σ]=> Δ]: [σ] renames every variable of [Γ] to one of [Δ] with the
    same value. *)
Definition ctx_map {N M} (Γ : ctx A) (σ : adj T N M) (Δ : ctx A) : Prop :=
  forall v a, has Γ v a -> exists w, apply_var σ v = Rename w /\ has Δ w a.

Lemma ctx_map_id {N} (Γ : ctx A) : ctx_map Γ (@identity T N) Γ.
Proof.
  intros v a H; exists v; split; [|exact H].
  apply apply_var_rename; cbn [adj_raw identity]; rewrite rapply_identity; reflexivity.
Qed.

(** Weakening the target by a new innermost [x]. *)
Lemma ctx_map_weaken {N M} (Γ Δ : ctx A) (σ : adj T N M) x a :
  ctx_map Γ σ Δ -> ctx_map Γ ⟦ | Γ \ x as _ | Γ[σ] ⟧ (ctx_cons Δ x a).
Proof.
  intros H v b Hv; destruct (H v b Hv) as [w [Ew Hw]].
  exists (vshift_free x w); split; [|apply has_shift, Hw].
  apply apply_var_rename; change (adj_raw ⟦ | Γ \ x as _ | Γ[σ] ⟧) with (rpush_outer (Some x) (adj_raw σ)).
  rewrite rapply_push_outer, (apply_var_rename_inv _ _ _ Ew); reflexivity.
Qed.

(** Going under a binder [x] in the source, [y] in the target. *)
Lemma ctx_map_under {N M} (Γ Δ : ctx A) (σ : adj T N M) x y a :
  ctx_map Γ σ Δ -> ctx_map (ctx_cons Γ x a) ⟦ x | Γ \ y | Γ[σ] ⟧ (ctx_cons Δ y a).
Proof.
  intros H v b Hv.
  change (adj_raw ⟦ x | Γ \ y | Γ[σ] ⟧)
    with (rpush_inner (Some x) (RRename (mk_rvar (Some y) 0)) (rpush_outer (Some y) (adj_raw σ))).
  destruct (has_cons_cases Γ x a v b Hv) as [[Ev ->]|[v' [-> Hv']]].
  - exists (fvar y 0); split; [|apply has_here].
    apply apply_var_rename; change (adj_raw ⟦ x | Γ \ y | Γ[σ] ⟧)
      with (rpush_inner (Some x) (RRename (mk_rvar (Some y) 0)) (rpush_outer (Some y) (adj_raw σ))).
    rewrite rapply_push_inner, Ev, rvar_eqb_refl; reflexivity.
  - destruct (H v' b Hv') as [w [Ew Hw]]; exists (vshift_free y w); split; [|apply has_shift, Hw].
    apply apply_var_rename; change (adj_raw ⟦ x | Γ \ y | Γ[σ] ⟧)
      with (rpush_inner (Some x) (RRename (mk_rvar (Some y) 0)) (rpush_outer (Some y) (adj_raw σ))).
    rewrite rapply_push_inner; cbn [var_raw vshift_free].
    destruct (rvar_eqb_spec (shift_rvar (mk_rvar (Some x) 0) (var_raw v')) (mk_rvar (Some x) 0)) as [E|E].
    + exfalso; pose proof (f_equal v_label E) as Hl; pose proof (f_equal v_index E) as Hi; revert Hl Hi.
      unfold shift_rvar; destruct (label_eqb _ _ && _); cbn [v_label v_index]; intros Hl Hi; [discriminate|].
      destruct v' as [[[z|] i] ?]; cbn in Hl, Hi; [injection Hl as ->|discriminate].
      unfold shift_rvar in E; cbn in E; rewrite String.eqb_refl in E; cbn in E; discriminate.
    + rewrite unshift_shift_rvar, rapply_push_outer, (apply_var_rename_inv _ _ _ Ew); reflexivity.
Qed.

End Morphisms.

Notation "Γ =[ σ ]=> Δ" := (ctx_map Γ σ Δ) (at level 60, σ at level 200).
