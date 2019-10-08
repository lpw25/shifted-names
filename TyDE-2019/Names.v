Require Import String.

Definition Zero := Empty_set.
Inductive Succ {S : Set} : Set := v0 | vS (s : S).

Fixpoint level (V : nat) : Set :=
  match V with
  | 0 => Zero
  | S V => @Succ (level V)
  end.

Inductive var {V : nat} :=
| free (name : string) (index : nat)
| bound (v : level V).

Definition wkv {V} (v : @var V) : @var (S V) :=
  match v with
  | free n i => free n i
  | bound v => @bound (S V) (vS v)
  end.

Definition openv a {V} (v : @var (S V)) : @var V :=
  match v with
  | free xn xi =>
    if string_dec a xn then
      free xn (S xi)
    else
      free xn xi
  | bound (vS v) => bound v
  | bound v0 => free a 0
  end.

Definition closev a {V} (v : @var V) : @var (S V) :=
  match v with
  | free xn xi =>
    if string_dec a xn then
      match xi with
      | 0 => @bound (S V) v0
      | S xi' => free xn xi'
      end
    else
      free xn xi
  | bound v => @bound (S V) (vS v)
  end.

Definition bindv {V} (v : @var (S V)) : option (@var V) :=
  match v with
  | free xn xi => Some (free xn xi)
  | bound v0 => None
  | bound (vS v) => Some (@bound V v)
  end.

Notation shiftv a v := (openv a (wkv v)).

Arguments openv : simpl nomatch.
Arguments closev : simpl nomatch.
Arguments bindv : simpl nomatch.

Ltac string_eqs :=
  match goal with
  | |- context C [string_dec ?x ?x] =>
    destruct (string_dec x x) as [_ | Neq]; cbn; try easy
  | |- context C [string_dec ?x ?y] =>
    let Neq := fresh "Hneq_" x y in
    destruct (string_dec x y) as [-> | Neq]; cbn; try easy
  end.

Lemma rw_openv_closev a {V} (v : @var V) : openv a (closev a v) = v.
Proof.
  unfold openv, closev.
  destruct v as [vn [|vi]|v]; cbn; try easy; repeat string_eqs.
Qed.
Lemma rw_closev_same a {V} :
  @closev a V (free a 0) = @bound (S V) v0.
Proof. unfold closev. string_eqs. Qed.
Lemma rw_closev_openv a {V} (v : @var (S V)) : closev a (openv a v) = v.
Proof.
  unfold openv, closev.
  destruct v as [vn vi|[|v]]; cbn; try easy; repeat string_eqs.
Qed.
Lemma rw_bindv_wkv {V} (v : @var V) : bindv (wkv v) = Some v.
Proof. destruct v; easy. Qed.
Lemma rw_shiftv_wkv b {V} (v : @var V) :
  shiftv b (wkv v) = wkv (shiftv b v). 
Proof. unfold openv; destruct v; cbn; try easy. string_eqs. Qed.
Hint Rewrite @rw_closev_openv @rw_closev_same @rw_openv_closev @rw_bindv_wkv
     @rw_shiftv_wkv : rw_names.
(* Slightly weird, but useful *)
Lemma rw_closev_wkv_shiftv a {V} (v : @var V) :
  closev a (wkv (shiftv a v)) = wkv (wkv v).
Proof. rewrite <- rw_shiftv_wkv. rewrite rw_closev_openv. easy. Qed.
Hint Rewrite @rw_closev_wkv_shiftv : rw_names.

Lemma compare_aux a {V} (x : @var V) :
  (x = free a 0) + { xi' | x = shiftv a xi' }.
Proof.
  unfold openv.
  destruct x as [xn xi | x]; cbn.
  destruct (string_dec a xn) as [->|Neq].
  destruct xi.
  - left; easy.
  - right; exists (free xn xi); cbn. string_eqs.
  - right; exists (free xn xi); cbn. string_eqs.
  - right; exists (bound x); easy.
Qed.

Inductive var_comparison (a : string) {V} : @var V -> Set :=
| samev : var_comparison a (@free V a 0)
| diffv x : var_comparison a (shiftv a x).
Definition compare a {V} (x : @var V) : var_comparison a x.
destruct (compare_aux a x) as [-> | [xi ->]]; constructor. Defined.


Inductive v0_comparison {V} : @var (S V) -> Set :=
| samev0 : v0_comparison (@bound (S V) v0)
| diffv0 v : v0_comparison (wkv v).
Definition compare0 {V} (v : @var (S V)) : v0_comparison v.
Proof.
  destruct v as [v i|[|v]].
  - change (@free (S V) v i) with (@wkv V (free v i)); constructor.
  - constructor.
  - change (@bound (S V) (vS v)) with (@wkv V (bound v)); constructor.
Qed.


Inductive term {V : nat} :=
| vv : @var V -> @term V
| const : nat -> @term V
| lam : @term (S V) -> @term V
| app : @term V -> @term V -> @term V.

Fixpoint open a {V} (t : @term (S V)) :=
  match t with
  | vv v => vv (openv a v)
  | const k => const k
  | lam t => lam (open a t)
  | app f e => app (open a f) (open a e)
  end.

Fixpoint close a {V} (t : @term V) :=
  match t with
  | vv v => vv (closev a v)
  | const k => const k
  | lam t => lam (close a t)
  | app f e => app (close a f) (close a e)
  end.

Fixpoint wk {V} (t : @term V) :=
  match t with
  | vv v => vv (wkv v)
  | const k => const k
  | lam t => lam (wk t)
  | app f e => app (wk f) (wk e)
  end.

Fixpoint wkn {V} (t : @term 0) :=
  match V with
  | 0 => t
  | S V => wk (wkn t)
  end.

Fixpoint bind {V} (u : @term 0) (t : @term (S V)) :=
  match t with
  | vv v =>
    match bindv v with
    | Some v => vv v
    | None => wkn u
    end
  | const k => const k
  | lam t => lam (bind u t)
  | app f e => app (bind u f) (bind u e)
  end.


Inductive ren :=
| r_id
| r_comp (r : ren) (s : ren)
| r_shift (b : string) (r : ren)
| r_rename (b : string) (r : ren) (a : string)
| r_subst (t : @term 0) (r : ren) (a : string).
Notation r_under a r := (r_rename a r a).

Fixpoint map_term (f : forall V, @var V -> @term V) {V} (t : @term V) : @term V :=
  match t with
  | vv v => f _ v
  | const k => const k
  | lam t => lam (map_term f t)
  | app a b => app (map_term f a) (map_term f b)
  end.


Fixpoint applyv (r : ren) {V} (v : @var V) {struct r} : @term V :=
  match r with
  | r_id => vv v
  | r_comp r s => map_term (@applyv r) (applyv s v)
  | r_shift b r => open b (applyv r (wkv v))
  | r_rename b r a => open b (applyv r (closev a v))
  | r_subst u r a => bind u (applyv r (closev a v))
  end.
Arguments applyv !r V v /.
Notation apply r := (map_term (@applyv r)).

Fixpoint is_renaming (r : ren) : Prop :=
  match r with
  | r_id => True
  | r_comp r s => is_renaming r /\ is_renaming s
  | r_shift b r => is_renaming r
  | r_rename b r a => is_renaming r
  | r_subst u r a => False
  end.

Definition proj1 {A B : Prop} (H : A /\ B) := let (a, _) := H in a.
Definition proj2 {A B : Prop} (H : A /\ B) := let (_, b) := H in b.
Fixpoint applyrv r : forall (rn : is_renaming r) {V} (v : @var V), @var V :=
  match r with
  | r_id => fun _ _ v => v
  | r_comp r s => fun rn _ v => applyrv r (proj1 rn) (applyrv s (proj2 rn) v)
  | r_shift b r => fun rn _ v => openv b (applyrv r rn (wkv v))
  | r_rename b r a => fun rn _ v => openv b (applyrv r rn (closev a v))
  | r_subst _ _ _ => False_rec _
  end.

Definition apply' r {V} (t : @term V) :=
  match r with
  | r_id => t
  | r_comp r s => apply r (apply s t)
  | r_shift b r => open b (apply r (wk t))
  | r_rename b r a => open b (apply r (close a t))
  | r_subst u r a => bind u (apply r (close a t))
  end.
Arguments apply' !r V t /.
Lemma expand_apply r {V} {t : @term V} :
  apply r t = apply' r t.
Proof. induction t; destruct r; cbn; f_equal; auto. Qed.
Ltac expand_apply :=
  repeat (rewrite expand_apply; cbn); repeat rewrite <- expand_apply.

(* Better dependent induction *)
Definition induction_S
  (ty : nat -> Set)
  (P : forall V, ty (S V) -> Prop)
  (Thm : forall V (t : ty V),
      match V return ty V -> Prop with
      | 0 => fun _ => True
      | S V => P V
      end t) : forall V t, P V t :=
  fun V t => Thm (S V) t.

Ltac induction_S :=
  match goal with
  | |- forall (V : nat) (tm : ?ty (S V)), @?P V tm =>
    apply (@induction_S ty P);
    induction tm;
    match goal with
    | |- match ?V with 0 => fun _ => True | S _ => _ end _ =>
      destruct V; [exact I | idtac]
    | _ => idtac
    end
  end.

Lemma rw_close_open a :
  forall {V} (t : @term (S V)), close a (open a t) = t.
Proof.
  induction_S; cbn; try (f_equal; easy).
  autorewrite with rw_names; easy.
Qed.

Lemma rw_open_close a :
  forall {V} (t : @term V), open a (close a t) = t.
Proof.
  induction t; cbn; try (f_equal; easy).
  autorewrite with rw_names; easy.
Qed.

Lemma rw_bind_wk u :
  forall {V} (t : @term V), bind u (wk t) = t.
Proof.
  induction t; cbn; try (f_equal; easy).
  autorewrite with rw_names; easy.
Qed.

Hint Rewrite @rw_close_open @rw_open_close @rw_bind_wk : rw_names.


Notation shift a t := (apply (r_shift a r_id) t).

(* identity and composition for apply *)
Lemma rw_apply_id {V} (t : @term V) : apply r_id t = t.
Proof. rewrite expand_apply; easy. Qed.
Lemma rw_apply_comp r s {V} (t : @term V) :
  apply r (apply s t) = apply (r_comp r s) t.
Proof. rewrite (expand_apply (r_comp r s)); easy. Qed.
Hint Rewrite @rw_apply_id @rw_apply_comp : rw_names.

(* Simple rewritings on applyv and shiftv (more later) *)
Lemma rw_applyv_bound r : forall {V} (v : level V),
  applyv r (bound v) = vv (bound v).
Proof.
  induction r; cbn; intros; autorewrite with rw_names; cbn;
    repeat match goal with [ H : _ |- _ ] => rewrite H; clear H end;
    cbn; easy.
Qed.
Lemma rw_applyrv_bound r (rn : is_renaming r) : forall {V} (v : level V),
  applyrv r rn (bound v) = bound v.
Proof.
  induction r; try destruct rn; cbn; intros; auto;
    repeat match goal with [ H : _ |- _ ] => rewrite H; clear H end;
    cbn; easy.
Qed.
Hint Rewrite @rw_applyv_bound (*@rw_shift_shiftv*) @rw_applyrv_bound: rw_names.

(* Rewrite to do the following:
    - group balanced pairs of operations into 'ren's
    - push opens/bind right and wk/close left
    - simplify rens *)

Lemma rw_group_rename a b {V} (t : @term V) :
  open a (close b t) = apply (r_rename a r_id b) t.
Proof. expand_apply; easy. Qed.
Lemma rw_group_shift a {V} (t : @term V) :
  open a (wk t) = apply (r_shift a r_id) t.
Proof. expand_apply; easy. Qed.
Lemma rw_group_subst u a {V} (t : @term V) :
  bind u (close a t) = apply (r_subst u r_id a) t.
Proof. expand_apply; easy. Qed.
Hint Rewrite @rw_group_rename @rw_group_shift @rw_group_subst : rw_names.


(* wk commutes with shift *)
Lemma rw_shift_wk b {V} (t : @term V) :
  shift b (wk t) = wk (shift b t).
Proof.
  induction t; cbn; try (f_equal; auto).
  autorewrite with rw_names; easy.
Qed.
Hint Rewrite @rw_shift_wk : rw_names.

(* wk commutes with apply.
   Somewhat harder to prove than I'd expect *)

Lemma apply_if_applyv_wk r :
  (forall {V} (v : @var V), applyv r (wkv v) = wk (applyv r v)) ->
  (forall {V} (t : @term V), apply r (wk t) = wk (apply r t)).
Proof. intro H. induction t; cbn; auto; f_equal; auto. Qed.

Lemma rw_applyv_wkv r : forall {V} (v : @var V), applyv r (wkv v) = wk (applyv r v).
Proof.
  induction r; cbn; intros.
  - easy.
  - rewrite IHr2. apply apply_if_applyv_wk. auto.

  - repeat rewrite IHr.
    autorewrite with rw_names. easy.

  - destruct (compare a v); cbn;
    autorewrite with rw_names; cbn; autorewrite with rw_names; cbn; try easy.
    repeat rewrite IHr.
    autorewrite with rw_names. easy.

  - destruct (compare a v); cbn;
    autorewrite with rw_names; cbn; autorewrite with rw_names; cbn; try easy.
    repeat rewrite IHr.
    autorewrite with rw_names; easy.
Qed.


(* FIXME where? *)
Lemma applyrv_is_applyv :
  forall r (rn : is_renaming r) {V} (v : @var V),
    applyv r v = vv (applyrv r rn v).
Proof.
  induction r; cbn; intuition.
  - erewrite IHr2; cbn. erewrite IHr1. reflexivity.
  - erewrite IHr. reflexivity.
  - erewrite IHr. cbn. reflexivity.
Qed.

Lemma rw_applyrv_wkv :
  forall r (rn : is_renaming r) {V} (v : @var V),
    applyrv r rn (wkv v) = wkv (applyrv r rn v).
Proof.
  intros.
  assert (Inj : forall {V} (a b : @var V), vv a = vv b -> a = b) by congruence.
  apply Inj. rewrite <- applyrv_is_applyv.
  rewrite rw_applyv_wkv.
  rewrite (applyrv_is_applyv r rn).
  easy.
Qed.

Lemma rw_apply_wk r {V} (t : @term V) : apply r (wk t) = wk (apply r t).
Proof. apply apply_if_applyv_wk. apply rw_applyv_wkv. Qed.

Lemma rw_apply_wkn r {V} (t : @term 0) :
  apply r (@wkn V t) = @wkn V (apply r t).
Proof.
  induction V; cbn; try easy.
  rewrite rw_apply_wk; rewrite IHV; easy.
Qed.

Hint Rewrite @rw_applyv_wkv @rw_applyrv_wkv @rw_apply_wk @rw_apply_wkn : rw_names.

Lemma rw_applyv_wkv_free r {an ai V} :
  applyv r (@free (S V) an ai) = wk (applyv r (@free V an ai)).
Proof.
  change (@free (S V) an ai) with (wkv (@free V an ai)).
  apply rw_applyv_wkv.
Qed.
Lemma rw_applyrv_wkv_free r rn {an ai V} :
  applyrv r rn (@free (S V) an ai) = wkv (applyrv r rn (@free V an ai)).
Proof.
  change (@free (S V) an ai) with (wkv (@free V an ai)).
  apply rw_applyrv_wkv.
Qed.
Hint Rewrite @rw_applyv_wkv_free @rw_applyrv_wkv_free : rw_names.

Ltac names :=
  cbn;
  repeat progress (autorewrite with rw_names; cbn).

(* Reductions for applyv to particular variables *)
Lemma rw_applyv_shift_comp r b {V} (x : @var V) :
  applyv (r_comp r (r_shift b r_id)) x = applyv r (shiftv b x).
Proof. easy. Qed.
Lemma rw_applyv_rename_same b r a {V} :
  applyv (r_rename b r a) (@free V a 0) = vv (free b 0).
Proof. names; easy. Qed.
Lemma rw_applyv_rename_same_comp r' b r a {V} :
  applyv (r_comp r' (r_rename b r a)) (@free V a 0) = applyv r' (free b 0).
Proof. names; easy. Qed.
Lemma rw_applyv_rename_diffv b r a {V} (x : @var V) :
  applyv (r_rename b r a) (shiftv a x) =
  applyv (r_shift b r) x.
Proof. names; easy. Qed.
Lemma rw_applyv_rename_diffv_comp r' b r a {V} (x : @var V) :
  applyv (r_comp r' (r_rename b r a)) (shiftv a x) =
  applyv (r_comp r' (r_shift b r)) x.
Proof. names; easy. Qed.
Lemma rw_applyv_subst_same u r a {V} :
  applyv (r_subst u r a) (@free V a 0) = wkn u.
Proof. names; easy. Qed.
Lemma rw_applyv_subst_same_comp r' u r a {V} :
  applyv (r_comp r' (r_subst u r a)) (@free V a 0) =
  wkn (apply r' u).
Proof. names; easy. Qed.
Lemma rw_applyv_subst_diffv u r a {V} (x : @var V) :
  applyv (r_subst u r a) (shiftv a x) = applyv r x.
Proof. names; easy. Qed.
Lemma rw_applyv_subst_diffv_comp r' u r a {V} (x : @var V) :
  applyv (r_comp r' (r_subst u r a)) (shiftv a x) =
  applyv (r_comp r' r) x.
Proof. names; easy. Qed.
Goal forall a b {V} (v : @var (S V)), 
  vv (openv a (shiftv b v)) = applyv (r_under a (r_shift b r_id)) (openv a v).
intros. cbn. names. easy. Qed.
Goal forall r a {V} (v : @var (S V)),
  applyv r (closev a v) = close a (applyv (r_under a r) v).
Proof. intros; names. easy. Qed.

Lemma comm_bind_apply u : forall {V} (t : @term (S V)) r,
  apply r (bind u t) = bind (apply r u) (apply r t).
Proof.
  induction_S; intro r; cbn; try solve [f_equal; auto].
  destruct (compare0 v); cbn; autorewrite with rw_names; easy.
Qed.


(* FIXME: maybe this should just be "names"? *)
Lemma rw_close_shift a r {V} (t : @term V) :
  close a (apply (r_shift a r) t) = wk (apply r t).
Proof. expand_apply. rewrite rw_apply_wk. rewrite rw_close_open. easy. Qed.
Lemma rw_subst_open u r b {V} (t : @term (S V)) :
  apply (r_subst u r b) (open b t) = bind u (apply r t).
Proof. expand_apply. rewrite rw_close_open. easy. Qed.
Lemma rw_rename_open a b {V} (t : @term (S V)) :
  apply (r_rename a r_id b) (open b t) = open a t.
Proof. expand_apply. rewrite rw_close_open. easy. Qed.
Hint Rewrite @rw_close_shift @rw_subst_open @rw_rename_open : rw_names.


(* FIXME: lots of applyrv rewritings below here *)



(* FIXME: not great, tbh *)

(* Commuting bind with apply.
   It seems more natural to make
     bind (r u) . r  --> r . bind u
   since bind is similar to open, and open moves right.
   But that rule breaks confluence, and isn't very useful
   as bind doesn't show up in terms. So, binds move left
   instead. *)
Lemma rw_push_bind u r {V} (t : @term (S V)) :
  apply r (bind u t) = bind (apply r u) (apply r t).
Proof. apply comm_bind_apply. Qed.
(* Shifts go the other way.
   This is confluent/terminating because shift doesn't simplify to apply (?) *)
Lemma rw_push_bind_shift u r s a {V} (t : @term (S V)) :
  bind (apply (r_shift a r) u) (apply (r_shift a s) t) =
  shift a (bind (apply r u) (apply s t)).
Proof. rewrite comm_bind_apply. expand_apply. names. easy. Qed.
Lemma rw_push_bind_shiftvu v a {V} (t : @term (S V)) :
  bind (vv (shiftv a v)) (shift a t) = shift a (bind (vv v) t).
Proof.
  change (vv (shiftv a v)) with (shift a (vv v)).
  rewrite rw_push_bind_shift. autorewrite with rw_names. easy.
Qed.
Hint Rewrite
  @rw_push_bind @rw_push_bind_shift @rw_push_bind_shiftvu : rw_names.


(* Morphisms. *)
Require Import Setoid.
Require Import Morphisms.

(* FIXME: is it better to define eqr over all vars or just free ones? *)
Definition eqr (r s : ren) : Prop :=
  forall {V} (v : @var V), applyv r v = applyv s v.

Instance eqr_Equivalence : Equivalence eqr.
Proof.
  split; red; unfold eqr; auto.
  intros. etransitivity; eauto.
Qed.

Instance mor_applyv : Proper
  (eqr ==> forall_relation (fun _ => (eq ==> eq))) applyv.
Proof. intros r s Hrs V v v' <-. auto. Qed.

Instance mor_map_term : Proper
  (forall_relation (fun _ => (eq ==> eq)) ==> forall_relation (fun _ => (eq ==> eq))) map_term.
Proof.
  intros f g Hfg V t t' <-. cbv in Hfg.
  induction t; cbn; try (f_equal; auto).
Qed.

(* FIXME applyv, applyrv, shift below  *)




Ltac easy_eqr :=
  repeat intro; cbn;
  repeat (match goal with [ H : _ |- _ ] => rewrite H; clear H end);
  expand_apply; names; easy.

Instance mor_r_comp   : Proper (eqr ==> eqr ==> eqr) r_comp. easy_eqr. Qed.
Instance mor_r_shift  : Proper (eq ==> eqr ==> eqr) r_shift. easy_eqr. Qed.
Instance mor_r_rename : Proper (eq ==> eqr ==> eq ==> eqr) r_rename. easy_eqr. Qed.
Instance mor_r_subst  : Proper (eq ==> eqr ==> eq ==> eqr) r_subst. easy_eqr. Qed.

Lemma rw_ren_id_comp r : eqr (r_comp r_id r) r.
Proof. easy_eqr. Qed.
Lemma rw_ren_comp_id r : eqr (r_comp r r_id) r.
Proof. easy_eqr. Qed.
Lemma rw_ren_comp_assoc r s t :
  eqr (r_comp r (r_comp s t)) (r_comp (r_comp r s) t).
Proof. easy_eqr. Qed.
Lemma rw_ren_under_id x :
  eqr (r_under x r_id) r_id.
Proof. easy_eqr. Qed.
Lemma rw_ren_rename_rename c b a r s :
  eqr (r_comp (r_rename c r b) (r_rename b s a))
      (r_rename c (r_comp r s) a).
Proof. easy_eqr. Qed.
Lemma rw_ren_rename_rename_comp l c b a r s :
  eqr (r_comp (r_comp l (r_rename c r b)) (r_rename b s a))
      (r_comp l (r_rename c (r_comp r s) a)).
Proof. easy_eqr. Qed.
Lemma rw_ren_rename_shift c b r s :
  eqr (r_comp (r_rename c r b) (r_shift b s))
      (r_shift c (r_comp r s)).
Proof.
  repeat intro; cbn. expand_apply. names. easy. Qed.
Lemma rw_ren_rename_shift_comp l c b r s :
  eqr (r_comp (r_comp l (r_rename c r b)) (r_shift b s))
      (r_comp l (r_shift c (r_comp r s))).
Proof. 
  repeat intro; cbn. expand_apply. rewrite rw_close_open; easy. Qed.
Lemma rw_ren_subst_rename u r a s b :
  eqr (r_comp (r_subst u r a) (r_rename a s b))
      (r_subst u (r_comp r s) b).
Proof. repeat intro; cbn; expand_apply; repeat rewrite rw_close_open; easy. Qed.
Lemma rw_ren_subst_rename_comp l u r a s b :
  eqr (r_comp (r_comp l (r_subst u r a)) (r_rename a s b))
      (r_comp l (r_subst u (r_comp r s) b)).
Proof. repeat intro; cbn; expand_apply; repeat rewrite rw_close_open; easy. Qed.
Lemma rw_ren_subst_shift u r a s :
  eqr (r_comp (r_subst u r a) (r_shift a s))
      (r_comp r s).
Proof.
  repeat intro; expand_apply; cbn; expand_apply.
  rewrite rw_close_open. rewrite rw_applyv_wkv. rewrite rw_apply_wk. rewrite rw_bind_wk.
  easy.
Qed.
Lemma rw_ren_subst_shift_comp l u r a s :
  eqr (r_comp (r_comp l (r_subst u r a)) (r_shift a s))
      (r_comp l (r_comp r s)).
Proof.
  repeat intro; expand_apply; cbn; expand_apply.
  rewrite rw_close_open. autorewrite with rw_names. easy.
Qed.
Lemma rw_ren_shift_any a r s :
  eqr (r_comp (r_shift a r) s) (r_shift a (r_comp r s)).
Proof.
  repeat intro; expand_apply; cbn; expand_apply.
  autorewrite with rw_names. easy.
Qed.
Lemma rw_ren_shift_any_comp l a r s :
  eqr (r_comp (r_comp l (r_shift a r)) s) (r_comp l (r_shift a (r_comp r s))).
Proof.
  repeat intro; expand_apply; cbn; expand_apply.
  autorewrite with rw_names. easy.
Qed.
Lemma rw_ren_any_subst r u s x :
  eqr (r_comp r (r_subst u s x)) (r_subst (apply r u) (r_comp r s) x).
Proof. easy_eqr. Qed.

(* No _comp version required for any_subst *)
(* Ensure crit pair of rw_ren_shift_any and rw_ren_any_subst is confluent *)
Lemma rw_ren_shift_subst_crit a u r b :
  eqr (r_subst (shift a u) (r_shift a r) b)
      (r_shift a (r_subst u r b)).
Proof.
  repeat intro; cbn.
  autorewrite with rw_names.
  rewrite rw_ren_shift_any.
  rewrite rw_push_bind_shift.
  rewrite rw_ren_comp_id. repeat rewrite rw_apply_id.
  change (bind u (@applyv r (S V) (closev b v))) with (@applyv (r_subst u r b) V v).
  change (bind u (@applyv r (S (S V)) (closev b (wkv v)))) with (@applyv (r_subst u r b) (S V) (wkv v)).
  rewrite rw_applyv_wkv.
  names; easy.
Qed.

Hint Rewrite
  @rw_ren_id_comp
  @rw_ren_comp_id
  @rw_ren_comp_assoc
  @rw_ren_under_id
  @rw_ren_rename_rename
  @rw_ren_rename_rename_comp
  @rw_ren_rename_shift
  @rw_ren_rename_shift_comp
  @rw_ren_subst_rename
  @rw_ren_subst_rename_comp
  @rw_ren_subst_shift
  @rw_ren_subst_shift_comp
  @rw_ren_shift_any
  @rw_ren_shift_any_comp
  @rw_ren_any_subst
  @rw_ren_shift_subst_crit : rw_names.

Goal
  forall a b c {V},
    apply (r_shift a (r_rename b r_id c)) (vv (@free V c 0)) =
    vv (shiftv a (free b 0)).
  intros. names.
  (* FIXME: should shiftv be a notation? *)
  unfold shiftv; cbn.
  match goal with [ |- ?x = ?x ] => reflexivity end.
Qed.

Goal
  forall a r b {V} (t : @term V),
    apply (r_rename a r b) (shift b t) = shift a (apply r t).
  intros. names.
  match goal with [ |- ?x = ?x ] => reflexivity end.
Qed.


(* Commuting open and close with apply *)

Lemma rw_push_open a r {V} (t : @term (S V)) :
  open a (apply r t) = apply (r_under a r) (open a t).
Proof. expand_apply; names; easy. Qed.
Lemma rw_push_close a r {V} (t : @term V) :
  apply r (close a t) = close a (apply (r_under a r) t).
Proof. expand_apply; names; easy. Qed.
Hint Rewrite @rw_push_open @rw_push_close : rw_names.



(*
 * Simply-typed lambda calculus
 *)



Inductive context {A : Set} : Set :=
| ctx_empty
| ctx_cons (Γ : @context A) (a : string) (val : A).
Notation "Γ ',,' x '~' A" := (ctx_cons Γ x A) (at level 60).

Fixpoint has {A} (ctx : @context A) (x : @var 0) (v : A) :=
  match ctx with
  | ctx_empty => False
  | ctx_cons ctx y val =>
    match bindv (closev y x) with
    | None => val = v
    | Some x' => has ctx x' v
    end
  end.

Inductive type := Base | Fn (a b : type).

Reserved Notation "Γ '⊢' e '~' A" (at level 60).
Inductive types (Γ : @context type) : @term 0 -> type -> Prop :=
| VAR x {A} :
   has Γ x A
   ->
   Γ ⊢ vv x ~ A
| BASE k :
   Γ ⊢ const k ~ Base
| LAM body {A B} :
   (forall x, (Γ,, x ~ A) ⊢ open x body ~ B)
   ->
   Γ ⊢ lam body ~ Fn A B
| APP f e {A B} :
   Γ ⊢ f ~ Fn A B ->
   Γ ⊢ e ~ A ->
   Γ ⊢ app f e ~ B
where "Γ '⊢' e '~' A" := (types Γ e A).

Notation "Γ ⊆ [ r , rn ] Δ" :=
  (forall v A, has Γ v A -> has Δ (applyrv r rn v) A)
  (at level 60, format "Γ  ⊆ [ r , rn ]  Δ").

Lemma ctx_extend_weakening {Γ Δ x} {A : type} {r} {rn : is_renaming r} :
  Γ ⊆ [ r , rn ] Δ -> (Γ,, x ~ A) ⊆[r_under x r,rn] (Δ,, x ~ A).
Proof.
  intros H v B; cbn.
  destruct (compare x v); names; auto.
Qed.

Theorem weakening {Γ e A}:
  Γ ⊢ e ~ A ->
  forall r (rn : is_renaming r) Δ,
    Γ ⊆[r, rn] Δ ->
    Δ ⊢ apply r e ~ A.
Proof.
  induction 1; cbn; intros.
  - erewrite applyrv_is_applyv.
    constructor.
    auto.
  - constructor.
  - constructor; intro v.
    names.
    eauto using ctx_extend_weakening.
  - econstructor; eauto.
Qed.


Notation "Γ ⊆ [ r ] Δ" :=
  (forall v A, has Γ v A -> Δ ⊢ applyv r v ~ A)
  (at level 60, format "Γ  ⊆ [ r ]  Δ").

Lemma ctx_extend_substitution {Γ Δ x} {A : type} {r} :
  Γ ⊆[r] Δ -> (Γ,, x ~ A) ⊆[r_under x r] (Δ,, x ~ A).
Proof.
  intros H v B; cbn.
  destruct (compare x v); names.
  - intros ->. constructor. names. auto.
  - intros ΓB. eapply (weakening (H _ _ ΓB) (r_shift x r_id) I).
    intros; names; auto.
Qed.

Theorem substitution {Γ e A} :
  Γ ⊢ e ~ A ->
  forall r Δ,
    Γ ⊆[r] Δ ->
    Δ ⊢ apply r e ~ A.
Proof.
  induction 1; cbn; intros.
  - auto.
  - constructor.
  - constructor; intro v.
    names.
    eauto using ctx_extend_substitution.
  - econstructor; eauto.
Qed.


Corollary weakening1 {Γ e A B x} :
  Γ ⊢ e ~ A ->
  Γ,, x ~ B ⊢ shift x e ~ A.
Proof.
  intro H. eapply (weakening H (r_shift x r_id) I).
  intros; names; auto.
Qed.

Corollary renaming1 {Γ e A B x y} :
  Γ,, x ~ B ⊢ e ~ A ->
  Γ,, y ~ B ⊢ apply (r_rename y r_id x) e ~ A.
Proof.
  intro H. eapply (weakening H (r_rename y r_id x) I).
  intros v C. destruct (compare x v); names; auto.
Qed.

Corollary substitution1 {Γ e e' A B x} :
  Γ,, x ~ B ⊢ e ~ A ->
  Γ ⊢ e' ~ B ->
  Γ ⊢ apply (r_subst e' r_id x) e ~ A.
Proof.
  intros He He'. eapply substitution; eauto.
  intros v C. destruct (compare x v); names.
  - intros <-; auto.
  - apply VAR.
Qed.



Lemma LAM' x {Γ body} {A B} :
  Γ,, x ~ A ⊢ open x body ~ B ->
  Γ ⊢ lam body ~ (Fn A B).
Proof.
  intro H.
  apply LAM.
  intro y.
  replace (open y body) with (apply (r_rename y r_id x) (open x body)) by (names; easy).
  auto using renaming1.
Qed.

Definition swap_bound {V} (v : @var (S (S V))) : @var (S (S V)) :=
  match v with
  | free vn vi =>
    free vn vi
  | bound v =>
    @bound (S (S V))
    (match v with
     | v0 => vS v0
     | vS v0 => v0
     | vS (vS v) => vS (vS v)
     end)
  end.

Lemma close_distinct {x an ai} (Hxy : x <> an) {V} :
  closev x (@free V an ai) = free an ai.
Proof. unfold closev. string_eqs. Qed.

(* This surprised me. *)
Lemma swap_shift_shift {x y} {V} (v : @var V) :
  shiftv x (shiftv y v) = shiftv y (shiftv x v).
Proof.
  destruct v as [vn vi|b]; unfold shiftv, openv; cbn; try easy.
  repeat string_eqs.
Qed.

Lemma shift_distinct {x y} (Hxy : x <> y) {V} :
  shiftv x (@free V y 0) = @free V y 0.
Proof. unfold shiftv, openv; cbn. string_eqs. Qed.

Lemma swap_shift_close {x y} (Hxy : x <> y) {V} (v : @var V) :
  closev x (shiftv y v) = shiftv y (closev x v).
Proof.
  destruct (compare x v).
  - rewrite shift_distinct; autorewrite with rw_names. easy. auto.
  - rewrite swap_shift_shift. autorewrite with rw_names; easy.
Qed.

Lemma swap_close_close {x y} (Hxy : x <> y) {V} {v : @var V} :
  closev x (closev y v) = swap_bound (closev y (closev x v)).
Proof.
  destruct (compare y v); autorewrite with rw_names; cbn.
  - replace (free y 0) with (shiftv x (@free V y 0)).
    autorewrite with rw_names. easy.
    unfold shiftv, openv; cbn. string_eqs.
  - rewrite swap_shift_close by assumption. autorewrite with rw_names.
    destruct x0 as [n i | b]; unfold closev; cbn; try easy.
    string_eqs. destruct i; easy.
Qed.

Lemma swap_subst_subst {x y} (Hxy : x <> y) {u v R} :
  eqr (r_subst u (r_subst v R x) y) (r_subst v (r_subst u R y) x).
Proof.
  intros V p. cbn.
  rewrite (swap_close_close Hxy).
  destruct (closev y (closev x _)) as [pn pi|[|[|b]]]; cbn;
  autorewrite with rw_names; cbn; autorewrite with rw_names; easy.
Qed.

Lemma barendregt_substitution_debruijn x y (M : @term 0) (L N : @term 0) :
  x <> y ->
  apply (r_subst L r_id y) (apply (r_subst N r_id x) M) =
  apply (r_subst (apply (r_subst L r_id y) N) r_id x) (apply (r_subst (shift x L) r_id y) M).
Proof.
  intros Hdistinct.
  autorewrite with rw_names.
  rewrite (swap_subst_subst Hdistinct); easy.
Qed.

Inductive Vclosed : @term 0 -> Set :=
| vc_vv v : Vclosed (vv v)
| vc_const n : Vclosed (const n)
| vc_lam t : (forall n, Vclosed (open n t)) -> Vclosed (lam t)
| vc_app f e : Vclosed f -> Vclosed e -> Vclosed (app f e).

Fixpoint Vclosedk (V : nat) : @term V -> Set :=
  match V with
  | 0 => fun t => Vclosed t
  | S V => fun t => forall n, Vclosedk V (open n t)
  end.

Fixpoint always_Vclosedk {V : nat} (t : term) {struct t} : Vclosedk V t :=
  match t with
  | vv v =>
    let fix go {V} : forall (v : @var V), Vclosedk V (vv v) :=
      match V with 0 => vc_vv | S V => fun v n => go _ end in
    go v

  | const n =>
    let fix go {V} : Vclosedk V _ :=
      match V with 0 => vc_const n | S V => fun _ => go end in
    go

  | lam t =>
    let fix go {V} : forall t, Vclosedk (S V) t -> Vclosedk V (lam t) :=
      match V with 0 => vc_lam | S V => fun _ vc a => go _ (vc a) end in
    go _ (always_Vclosedk t)

  | app f e  =>
    let fix go {V} : forall f e, Vclosedk V f -> Vclosedk V e -> Vclosedk V (app f e) :=
      match V with 0 => vc_app | S V => fun _ _ vf ve a => go _ _ (vf a) (ve a) end in
    go _ _ (always_Vclosedk f) (always_Vclosedk e)
  end.


Lemma always_Vclosedk_open x : forall {V} (t : @term (S V)),
  always_Vclosedk t x = always_Vclosedk (open x t).
Proof.
  induction_S; induction V; cbn; try easy.
  - rewrite IHt. easy.
  - rewrite IHt. easy.
  - rewrite IHt2. rewrite IHt1. easy.
  - rewrite IHt1. rewrite IHt2. easy.
Qed.
Hint Rewrite always_Vclosedk_open : rw_names.
Open Scope string.

Notation "'λ' v ~> t" := (lam (close v t)) (at level 60, format "'λ' v  ~>  t").
Notation "f & e" := (app f e) (at level 59, left associativity).
Notation "! k" := (vv (free k 0)) (at level 10, format "! k").

Fixpoint cps {tm} (t : Vclosed tm) : @term 0 :=
  match t with
  | vc_vv v =>
    λ"k" ~>
      !"k" & shift "k" (vv v)

  | vc_const n =>
    λ"k" ~>
     !"k" & const n

  | vc_lam _ t =>
    λ"k" ~>
     !"k" & λ"x" ~>
        shift "k" (cps (t "x"))

  | vc_app _ _ f e =>
    λ"k" ~>
       shift "k" (cps f) & λ"f" ~>
          shift "f" (shift "k" (cps e)) & λ"v" ~>
             !"f" & !"v" & !"k"
  end.
Print cps.

(* 
   Meyer and Wand's theorem about typed CPS transforms
     ("Continuation semantics in typed lambda calculi", 1985)
   This follows Harper and Lillibridge's presentation.
     ("Polymorphic Type Assignment and CPS Conversion", 1992)
 *)

Definition cont R A :=
  Fn (Fn A R) R.

Fixpoint cpsty R A :=
  match A with
  | Base => Base
  | Fn A B => Fn (cpsty R A) (cont R (cpsty R B))
  end.

Fixpoint cpsctx R ctx {struct ctx} :=
  match ctx with
  | ctx_empty => ctx_empty
  | ctx_cons G x A => ctx_cons (cpsctx R G) x (cpsty R A)
  end.

Lemma cpsctx_has {R Γ A} : forall x,
  has Γ x A -> has (cpsctx R Γ) x (cpsty R A).
Proof.
  induction Γ; cbn; auto.
  intro x; destruct (compare a x); names; [intros ->|]; auto.
Qed.

Theorem cps_type_preserving {Γ e A R} :
  types Γ e A ->
  types (cpsctx R Γ) (cps (always_Vclosedk e)) (cont R (cpsty R A)).
Proof.
  induction 1; names; intros.
  - apply LAM; intro y; cbn.
    eapply APP.
    eapply VAR. cbn. names. easy.
    eapply VAR. cbn. names.
    apply cpsctx_has; auto.
  - apply LAM; intro y; cbn.
    eapply APP.
    eapply VAR; cbn; names. easy.
    apply BASE.
  - apply (LAM' "k"); names.
    eapply APP. apply VAR. names. easy.
    apply (LAM' "x"); names.
    eapply weakening. eauto. cbn.
    intros v T'. cbn. names.
    rewrite swap_shift_close  by easy.
    destruct (compare "x" v); names;  easy.
  - apply (LAM' "k"). names.
    eapply APP.
    eapply weakening1; eauto.
    apply (LAM' "f"). names.
    eapply APP.
    eapply weakening. eauto.
    intros v T'. names. easy.
    apply (LAM' "v"). names.
    eapply APP.
    eapply APP.
    eapply VAR. cbn. easy.
    eapply VAR. cbn. easy.
    eapply VAR. cbn. easy.
  Unshelve. cbn. easy. cbn; easy.
Qed.
Print Assumptions cps_type_preserving.

