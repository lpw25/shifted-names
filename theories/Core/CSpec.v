(** * Context forms: the specification

    Forms, their reading as expressions ([of_exp], [wexp]), their
    meaning in a comprehension model ([fden], [wden]) and the semantic
    facts the passes are proved with.  The passes themselves
    ([CForm.run], [CRun], [CRun2], [CRunN]) are in other files; nothing
    here depends on them. *)

From Stdlib Require Import List Bool Arith Lia PArith.
From ShiftedNames.Core Require Import Label Normalise GEval CNorm Comp CSound CComplete.
Import ListNotations.

Inductive tgt : Type :=
| TR (z : lexp) (i d : nat)
| TT (u : nat) (p : pexp).

Record form : Type := mkF { fout : list lexp; fin : list (lexp * tgt) }.

Inductive item : Type :=
| IF (f : form)
| IA (L : list lexp) (n : nat).

Definition fword : Type := list item.

(** ** Expressions as words of forms *)

Definition shift_t (h : lexp) (t : tgt) : tgt :=
  match t with TR z i d => TR z i (S d) | TT u p => TT u (PShift h p) end.

Definition lift_f (h : lexp) (f : form) : form :=
  mkF (h :: fout f) ((h, TR h 0 0) :: map (fun '(g, t) => (g, shift_t h t)) (fin f)).

Definition lift_i (h : lexp) (it : item) : item :=
  match it with IF f => IF (lift_f h f) | IA L n => IA (h :: L) n end.

(** A target term: the weakenings it is read under, and the read. *)
Fixpoint ttgt (t : texp) : list lexp * tgt :=
  match t with
  | TVarE z i => ([], TR z i 0)
  | TBindE u p => ([], TT u p)
  | TShiftE k t' => if is_bind t' then ttgt t' else let '(ks, r) := ttgt t' in (k :: ks, shift_t k r)
  end.

(** The identity, popping [ks] and pushing them back. *)
Definition restore (ks : list lexp) : form := fold_right lift_f (mkF [] []) ks.

Definition entry (h : lexp) (t : texp) : form :=
  let '(ks, r) := ttgt t in mkF ks ((h, r) :: fin (restore ks)).

Definition weak (h : lexp) : form := mkF [h] [].

Fixpoint of_exp (e : aexp) : fword :=
  match e with
  | AId => []
  | AAtom n => [IA [] n]
  | ACompose a b => of_exp b ++ of_exp a
  | AOuter h a => of_exp a ++ [IF (weak h)]
  | AInner h t a => map (lift_i h) (of_exp a) ++ [IF (entry h t)]
  | ALift h a => map (lift_i h) (of_exp a)
  end.

(** ** Back to expressions *)

Fixpoint rexp (O : list lexp) (d : nat) (z : lexp) (i : nat) : texp :=
  match O, d with
  | o :: O', S d' => TShiftE o (rexp O' d' z i)
  | _, _ => TVarE z i
  end.

Definition texp_of (O : list lexp) (t : tgt) : texp :=
  match t with TR z i d => rexp O d z i | TT u p => TBindE u p end.

Definition fexp (f : form) : aexp :=
  fold_right (fun '(h, t) a => AInner h (texp_of (fout f) t) a)
    (fold_right (fun o a => AOuter o a) AId (fout f)) (fin f).

Definition iexp (it : item) : aexp :=
  match it with IF f => fexp f | IA L n => fold_right ALift (AAtom n) L end.

Fixpoint wexp (w : fword) : aexp :=
  match w with [] => AId | it :: w' => ACompose (wexp w') (iexp it) end.

(** ** The pass *)

Fixpoint omap {X Y} (f : X -> option Y) (l : list X) : option (list Y) :=
  match l with
  | [] => Some []
  | x :: l' => match f x, omap f l' with Some y, Some l'' => Some (y :: l'') | _, _ => None end
  end.

Fixpoint swap_at {X} (k : nat) (l : list X) : list X :=
  match k, l with
  | 0, a :: b :: r => b :: a :: r
  | S k', a :: r => a :: swap_at k' r
  | _, _ => l
  end.

Fixpoint remove_at {X} (k : nat) (l : list X) : list X :=
  match k, l with
  | 0, _ :: r => r
  | S k', a :: r => a :: remove_at k' r
  | _, [] => []
  end.

(** ** List helpers *)

Definition mem (x : positive) (l : list positive) : bool := existsb (Pos.eqb x) l.

Fixpoint index_of (x : positive) (l : list positive) : option nat :=
  match l with [] => None | y :: l' => if Pos.eqb x y then Some 0 else option_map S (index_of x l') end.

(** [n] fresh ids from [c]. *)
Fixpoint pseq (c : positive) (n : nat) : list positive :=
  match n with 0 => [] | S n' => c :: pseq (Pos.succ c) n' end.

Definition padd (c : positive) (n : nat) : positive := Nat.iter n Pos.succ c.

Fixpoint mapi_from {X Y} (k : nat) (g : nat -> X -> Y) (l : list X) : list Y :=
  match l with [] => [] | a :: l' => g k a :: mapi_from (S k) g l' end.

Fixpoint zipd {X} (ids : list positive) (l : list X) : list (positive * X) :=
  match l with
  | [] => []
  | x :: l' => match ids with i :: ids' => (i, x) :: zipd ids' l' | [] => (xH, x) :: zipd [] l' end
  end.

Fixpoint map_front {X} (n : nat) (g : X -> X) (l : list X) : list X :=
  match n, l with S n', x :: l' => g x :: map_front n' g l' | _, _ => l end.

Lemma last_map {X Y} (g : X -> Y) l d : last (map g l) (g d) = g (last l d).
Proof. induction l as [|a l IH]; [reflexivity|]; destruct l; [reflexivity|]; exact IH. Qed.

Lemma omap_ext {X Y} (g g' : X -> option Y) l : (forall x, g x = g' x) -> omap g l = omap g' l.
Proof. intros H; induction l as [|a l IH]; cbn; [reflexivity|rewrite H, IH; reflexivity]. Qed.

(** ** Meaning in a comprehension model *)

Section Sound.

Variable F : order.
Variable M : cmodel.
Hypothesis HM : ccons F M.

Fixpoint popn (O : list lexp) (d : nat) (x : cU M) : cU M :=
  match O, d with o :: O', S d' => popn O' d' (cpop o x) | _, _ => x end.

Definition tden (O : list lexp) (t : tgt) (x : cU M) : cA M :=
  match t with TR z i d => cname z i (popn O d x) | TT u p => cterm u (fpb p) (cp p x) end.

Fixpoint pushes (O : list lexp) (I : list (lexp * tgt)) (b x : cU M) : cU M :=
  match I with [] => b | (h, t) :: I' => cpush h (pushes O I' b x) (tden O t x) end.

Definition fden (f : form) (x : cU M) : cU M :=
  pushes (fout f) (fin f) (popn (fout f) (length (fout f)) x) x.

Fixpoint lden (L : list lexp) (n : nat) (x : cU M) : cU M :=
  match L with [] => catom n x | h :: L' => cpush h (lden L' n (cpop h x)) (chd h x) end.

Definition iden (it : item) (x : cU M) : cU M :=
  match it with IF f => fden f x | IA L n => lden L n x end.

Fixpoint wden (w : fword) (x : cU M) : cU M :=
  match w with [] => x | it :: w' => iden it (wden w' x) end.

Lemma wden_app w1 w2 x : wden (w1 ++ w2) x = wden w1 (wden w2 x).
Proof. induction w1 as [|it w1 IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma pushes_app O I1 I2 b x : pushes O (I1 ++ I2) b x = pushes O I1 (pushes O I2 b x) x.
Proof. induction I1 as [|[h t] I1 IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma pushes_ext O O' I b x x' : (forall h t, In (h, t) I -> tden O t x = tden O' t x') ->
  pushes O I b x = pushes O' I b x'.
Proof.
  induction I as [|[h t] I IH]; intros H; cbn; [reflexivity|].
  rewrite (H h t (or_introl eq_refl)); f_equal; apply IH.
  intros h' t' Ht; apply (H h'); right; exact Ht.
Qed.

(** *** From expressions *)

Lemma tden_shift h O t x : tden (h :: O) (shift_t h t) x = tden O t (cpop h x).
Proof. destruct t; reflexivity. Qed.

Lemma pushes_shift h O I b x :
  pushes (h :: O) (map (fun '(g, t) => (g, shift_t h t)) I) b x = pushes O I b (cpop h x).
Proof. induction I as [|[g t] I IH]; cbn; [reflexivity|]; rewrite IH, tden_shift; reflexivity. Qed.

Lemma lift_f_sound h f x : fden (lift_f h f) x = cpush h (fden f (cpop h x)) (chd h x).
Proof. unfold fden, lift_f; cbn [fout fin pushes length popn]; rewrite pushes_shift; reflexivity. Qed.

Lemma restore_out ks : fout (restore ks) = ks.
Proof. induction ks as [|k ks IH]; cbn; [reflexivity|f_equal; exact IH]. Qed.

Lemma restore_sound ks x : fden (restore ks) x = x.
Proof.
  revert x; induction ks as [|k ks IH]; intros x; [reflexivity|].
  change (restore (k :: ks)) with (lift_f k (restore ks)); rewrite lift_f_sound, IH; apply cpush_pop.
Qed.

Lemma ttgt_sound t x : tden (fst (ttgt t)) (snd (ttgt t)) x = ct t x.
Proof.
  revert x; induction t as [z i|u p|k t IH]; intros x; try reflexivity.
  cbn [ttgt ct]; destruct (is_bind t); [apply IH|].
  destruct (ttgt t) as [ks r] eqn:E; cbn [fst snd]; rewrite tden_shift.
  exact (IH (cpop k x)).
Qed.

Lemma entry_sound h t x : fden (entry h t) x = cpush h x (ct t x).
Proof.
  unfold entry; pose proof (ttgt_sound t x) as T; destruct (ttgt t) as [ks r]; cbn [fst snd] in T.
  unfold fden; cbn [fout fin pushes]; rewrite T; f_equal.
  pose proof (restore_sound ks x) as R; unfold fden in R; rewrite restore_out in R; exact R.
Qed.

Lemma lift_i_sound h it x : iden (lift_i h it) x = cpush h (iden it (cpop h x)) (chd h x).
Proof. destruct it; [apply lift_f_sound|reflexivity]. Qed.

Lemma lift_w_sound h w x : wden (map (lift_i h) w) x = cpush h (wden w (cpop h x)) (chd h x).
Proof.
  revert x; induction w as [|it w IH]; intros x; cbn [map wden].
  - symmetry; apply cpush_pop.
  - rewrite IH, lift_i_sound, cpop_push, chd_push; reflexivity.
Qed.

Theorem of_exp_sound e x : wden (of_exp e) x = ca e x.
Proof.
  revert x; induction e as [|n|a IHa b IHb|h a IH|h t a IH|h a IH]; intros x; cbn [of_exp ca].
  - reflexivity.
  - reflexivity.
  - rewrite wden_app, IHb, IHa; reflexivity.
  - rewrite wden_app; cbn; rewrite IH; reflexivity.
  - rewrite wden_app; cbn [wden iden]; rewrite entry_sound, lift_w_sound, cpop_push, chd_push, IH; reflexivity.
  - rewrite lift_w_sound, IH; reflexivity.
Qed.

(** *** Back to expressions *)

Lemma is_bind_rexp O d z i : is_bind (rexp O d z i) = false.
Proof. revert d; induction O as [|o O IH]; intros [|d]; cbn; auto. Qed.

Lemma rexp_sound O d z i x : ct (rexp O d z i) x = cname z i (popn O d x).
Proof.
  revert d x; induction O as [|o O IH]; intros [|d] x; try reflexivity.
  cbn [rexp ct]; rewrite is_bind_rexp, IH; reflexivity.
Qed.

Lemma texp_of_sound O t x : ct (texp_of O t) x = tden O t x.
Proof. destruct t; [apply rexp_sound|reflexivity]. Qed.

Lemma fexp_sound f x : ca (fexp f) x = fden f x.
Proof.
  unfold fexp, fden; destruct f as [O I]; cbn [fout fin].
  induction I as [|[h t] I IH]; cbn [fold_right pushes].
  - clear; revert x; induction O as [|o O IH]; intros x; [reflexivity|]; cbn; apply IH.
  - cbn [ca]; rewrite IH, texp_of_sound; reflexivity.
Qed.

Lemma iexp_sound it x : ca (iexp it) x = iden it x.
Proof.
  destruct it as [f|L n]; [apply fexp_sound|]; cbn.
  revert x; induction L as [|h L IH]; intros x; cbn; [reflexivity|rewrite IH; reflexivity].
Qed.

Lemma wexp_sound w x : ca (wexp w) x = wden w x.
Proof. induction w as [|it w IH]; cbn; [reflexivity|rewrite IH, iexp_sound; reflexivity]. Qed.

(** *** Labels the facts order *)

Lemma pops_comm y g i (z : cU M) : known_distinct F y g ->
  iter i (cpop y) (cpop g z) = cpop g (iter i (cpop y) z).
Proof.
  intros D; induction i as [|i IH]; cbn; [reflexivity|]; rewrite IH.
  destruct (kd_pops F M HM y g D (iter i (cpop y) z)) as [E _]; exact E.
Qed.

Lemma cname_pop_other y g i (z : cU M) : known_distinct F y g -> cname y i (cpop g z) = cname y i z.
Proof.
  intros D; unfold cname; rewrite (pops_comm y g i z D).
  destruct (kd_pops F M HM y g D (iter i (cpop y) z)) as [_ [E _]]; exact E.
Qed.

Lemma cname_push_other y g i (z : cU M) s : known_distinct F y g -> cname y i (cpush g z s) = cname y i z.
Proof.
  intros D; revert z; induction i as [|i IH]; intros z.
  - apply (kd_hd_push F M HM y g D).
  - rewrite <- (cname_pop M y i), (kd_pop_push F M HM y g D), IH, (cname_pop M y i); reflexivity.
Qed.

Lemma pop_comm a b (x : cU M) : known_distinct F a b -> cpop a (cpop b x) = cpop b (cpop a x).
Proof. intros D; destruct (kd_pops F M HM a b D x) as [E _]; exact E. Qed.

Lemma kdk a b : kd F a b = true -> known_distinct F a b.
Proof. apply kd_known. Qed.

Lemma bk a b : before F a b = true -> known_distinct F a b.
Proof. apply before_known. Qed.

Lemma lexp_eqb_true a b : lexp_eqb a b = true -> a = b.
Proof. apply lexp_eqb_eq. Qed.

(** *** Pops *)

Lemma popn_0 O x : popn O 0 x = x.
Proof. destruct O; reflexivity. Qed.

Lemma popn_app_le A B d x : d <= length A -> popn (A ++ B) d x = popn A d x.
Proof.
  revert d x; induction A as [|a A IH]; intros d x Hd.
  - destruct d; cbn in *; [destruct B; reflexivity|lia].
  - destruct d; cbn in *; [destruct (A ++ B); reflexivity|]; apply IH; lia.
Qed.

Lemma popn_app_add A B m x : popn (A ++ B) (length A + m) x = popn B m (popn A (length A) x).
Proof. revert x; induction A as [|a A IH]; intros x; cbn; [reflexivity|apply IH]. Qed.

Lemma popn_over O d x : length O <= d -> popn O d x = popn O (length O) x.
Proof.
  revert d x; induction O as [|o O IH]; intros d x Hd.
  - destruct d; reflexivity.
  - destruct d; cbn in *; [lia|]; apply IH; lia.
Qed.

Lemma popn_min O d x : popn O (Nat.min d (length O)) x = popn O d x.
Proof.
  destruct (Nat.le_ge_cases d (length O)) as [H|H].
  - rewrite Nat.min_l by exact H; reflexivity.
  - rewrite Nat.min_r by exact H; symmetry; apply popn_over, H.
Qed.

Lemma popn_S O d x : d < length O -> popn O (S d) x = cpop (nth d O LNone) (popn O d x).
Proof.
  revert d x; induction O as [|o O IH]; intros d x Hd; cbn in *; [lia|].
  destruct d as [|d]; [rewrite !popn_0; reflexivity|]; apply IH; lia.
Qed.

Lemma omap_pushes (g : lexp * tgt -> option (lexp * tgt)) O O' I I' b x x' :
  omap g I = Some I' ->
  (forall h t h' t', g (h, t) = Some (h', t') -> h' = h /\ tden O' t' x' = tden O t x) ->
  pushes O' I' b x' = pushes O I b x.
Proof.
  revert I'; induction I as [|[h t] I IH]; intros I' E H; cbn in E.
  - injection E as <-; reflexivity.
  - destruct (g (h, t)) as [[h' t']|] eqn:G; [|discriminate].
    destruct (omap g I) as [I''|] eqn:E2; [|discriminate]; injection E as <-.
    destruct (H h t h' t' G) as [-> T]; cbn; rewrite T, (IH I'' eq_refl H); reflexivity.
Qed.

Lemma omap_length {X Y} (g : X -> option Y) l l' : omap g l = Some l' -> length l' = length l.
Proof.
  revert l'; induction l as [|a l IH]; intros l' E; cbn in E; [injection E as <-; reflexivity|].
  destruct (g a), (omap g l) as [l''|] eqn:E2; try discriminate; injection E as <-; cbn; f_equal; apply IH; reflexivity.
Qed.

Lemma nth_error_last_len {X} (st : list X) n d : length st = S n -> nth_error st n = Some (last st d).
Proof.
  revert n; induction st as [|a st IH]; intros n H; [discriminate|]; cbn in H; injection H as H.
  destruct n as [|n]; [destruct st; [reflexivity|discriminate]|].
  destruct st as [|b st]; [discriminate|]; apply (IH n); cbn; exact H.
Qed.

(** *** Lists split at a position *)

Lemma split_at {X} (l : list X) k a : nth_error l k = Some a -> exists A B, l = A ++ a :: B /\ length A = k.
Proof. apply nth_error_split. Qed.

Lemma remove_at_app {X} (A B : list X) a : remove_at (length A) (A ++ a :: B) = A ++ B.
Proof. induction A as [|c A IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma swap_at_app {X} (A B : list X) a b : swap_at (length A) (A ++ a :: b :: B) = A ++ b :: a :: B.
Proof. induction A as [|c A IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma skipn_app_at {X} (A B : list X) a : skipn (S (length A)) (A ++ a :: B) = B.
Proof. induction A as [|c A IH]; cbn; [reflexivity|exact IH]. Qed.

Lemma firstn_app_at {X} (A B : list X) a : firstn (length A) (A ++ a :: B) = A.
Proof. induction A as [|c A IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma forallb_kd l (L : list lexp) : forallb (kd F l) L = true -> Forall (known_distinct F l) L.
Proof. intros H; rewrite forallb_forall in H; apply Forall_forall; intros a Ha; apply kdk, H, Ha. Qed.

Lemma forallb_kd_in l (Q : list (lexp * tgt)) : forallb (fun '(m, _) => kd F l m) Q = true ->
  Forall (fun mt => known_distinct F l (fst mt)) Q.
Proof.
  intros H; rewrite forallb_forall in H; apply Forall_forall; intros [m t] Hm; cbn.
  apply kdk; exact (H (m, t) Hm).
Qed.

(** *** Steps on labels the facts order, through pops and pushes *)

Lemma popn_pop_comm o B n y : Forall (known_distinct F o) B -> popn B n (cpop o y) = cpop o (popn B n y).
Proof.
  revert n y; induction B as [|b B IH]; intros [|n] y H; try reflexivity; inversion H; subst; cbn.
  rewrite (pop_comm b o) by (apply known_distinct_sym; assumption); apply IH; assumption.
Qed.

Lemma popn_hd o B n y : Forall (known_distinct F o) B -> chd o (popn B n y) = chd o y.
Proof.
  revert n y; induction B as [|b B IH]; intros [|n] y H; try reflexivity; inversion H; subst; cbn.
  rewrite IH by assumption; destruct (kd_pops F M HM o b H2 y) as [_ [E _]]; exact E.
Qed.

Lemma popn_push_comm h O d y v : Forall (known_distinct F h) O -> popn O d (cpush h y v) = cpush h (popn O d y) v.
Proof.
  revert d y; induction O as [|o O IH]; intros [|d] y H; try reflexivity; inversion H; subst; cbn.
  rewrite (kd_pop_push F M HM o h) by (apply known_distinct_sym; assumption); apply IH; assumption.
Qed.

Lemma pushes_pop_comm l O Q b y : Forall (fun mt => known_distinct F l (fst mt)) Q ->
  pushes O Q (cpop l b) y = cpop l (pushes O Q b y).
Proof.
  induction Q as [|[m t] Q IH]; intros H; [reflexivity|]; inversion H; subst; cbn [pushes].
  rewrite IH, (kd_pop_push F M HM l m) by assumption; reflexivity.
Qed.

Lemma pushes_hd l O Q b y : Forall (fun mt => known_distinct F l (fst mt)) Q -> chd l (pushes O Q b y) = chd l b.
Proof.
  induction Q as [|[m t] Q IH]; intros H; [reflexivity|]; inversion H; subst; cbn [pushes].
  rewrite (kd_hd_push F M HM l m) by assumption; apply IH; assumption.
Qed.

Lemma pushes_push_comm h O Q b v y : Forall (fun mt => known_distinct F h (fst mt)) Q ->
  cpush h (pushes O Q b y) v = pushes O Q (cpush h b v) y.
Proof.
  induction Q as [|[m t] Q IH]; intros H; [reflexivity|]; inversion H; subst; cbn [pushes].
  rewrite (kd_push_push F M HM h m) by assumption; f_equal; apply IH; assumption.
Qed.

Lemma popn_mid A a b B m x : popn (A ++ a :: b :: B) (length A + S (S m)) x = popn B m (cpop b (cpop a (popn A (length A) x))).
Proof. rewrite popn_app_add; reflexivity. Qed.

Lemma popn_at A a B m x : popn (A ++ a :: B) (length A + S m) x = popn B m (cpop a (popn A (length A) x)).
Proof. rewrite popn_app_add; reflexivity. Qed.

Lemma popn_len_le A B d x : d <= length A -> popn (A ++ B) d x = popn A d x.
Proof. apply popn_app_le. Qed.

Lemma wden_rev_cons it out x : wden (rev (it :: out)) x = wden (rev out) (iden it x).
Proof. cbn [rev]; rewrite wden_app; reflexivity. Qed.

(** *** Lifts *)

Lemma split2 {X} (st : list X) k a b : nth_error st k = Some a -> nth_error st (S k) = Some b ->
  st = firstn k st ++ a :: b :: skipn (S (S k)) st.
Proof.
  revert st; induction k as [|k IH]; intros [|c st] Ha Hb; cbn in *; try discriminate.
  - injection Ha as ->; destruct st as [|d st]; [discriminate|]; injection Hb as ->; reflexivity.
  - f_equal; apply IH; assumption.
Qed.

Fixpoint liftsem (L : list lexp) (g : cU M -> cU M) (x : cU M) : cU M :=
  match L with [] => g x | h :: L' => cpush h (liftsem L' g (cpop h x)) (chd h x) end.

Lemma liftsem_ext L g g' x : (forall y, g y = g' y) -> liftsem L g x = liftsem L g' x.
Proof. intros H; revert x; induction L as [|h L IH]; intros x; cbn; [apply H|rewrite IH; reflexivity]. Qed.

Lemma liftsem_app L1 L2 g x : liftsem (L1 ++ L2) g x = liftsem L1 (liftsem L2 g) x.
Proof. revert x; induction L1 as [|h L IH]; intros x; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma liftsem_comp L g g' x : liftsem L g (liftsem L g' x) = liftsem L (fun y => g (g' y)) x.
Proof.
  revert x; induction L as [|h L IH]; intros x; cbn; [reflexivity|].
  rewrite cpop_push, chd_push, IH; reflexivity.
Qed.

Lemma liftsem_id L x : liftsem L (fun y => y) x = x.
Proof. revert x; induction L as [|h L IH]; intros x; cbn; [reflexivity|rewrite IH; apply cpush_pop]. Qed.

Lemma lift_fold_sound L f x : fden (fold_right lift_f f L) x = liftsem L (fden f) x.
Proof.
  revert x; induction L as [|h L IH]; intros x; [reflexivity|].
  change (fold_right lift_f f (h :: L)) with (lift_f h (fold_right lift_f f L)); rewrite lift_f_sound, IH; reflexivity.
Qed.

Lemma lden_app L L' n x : lden (L ++ L') n x = liftsem L (lden L' n) x.
Proof. revert x; induction L as [|h L IH]; intros x; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

End Sound.
