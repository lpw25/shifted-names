(** * Things stored relative to a base

    The nodes of our trees carry weakening counts (Counts.v), and what they
    hold is stored relative to the node's base.  Elements say what they use
    and how to move between bases; this file states what is required of
    them and proves the facts about lists of elements that every annotated
    structure needs. *)

From Stdlib Require Import PArith Arith Lia List Bool.
From ShiftedNames.Core Require Import Trie Counts.
Import ListNotations.

Lemma map_id_in {A} (f : A -> A) l : (forall x, In x l -> f x = x) -> map f l = l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|]; cbn [map].
  rewrite (H x (or_introl eq_refl)), IH; [reflexivity|].
  intros y Hy; apply H; right; exact Hy.
Qed.

(** ** The interface *)

Class Based (X : Type) : Type := {
  (** What an element uses, relative to its own base. *)
  uses : X -> counts;
  (** [shift d x]: [x] relative to a base [d] higher; [unshift]: lower. *)
  shift : counts -> X -> X;
  unshift : counts -> X -> X;
  (** Well-formed elements. *)
  eok : X -> Prop
}.

Class BasedLaws (X : Type) `{Based X} : Prop := {
  ok_shift : forall d x, eok x -> eok (shift d x);
  ok_unshift : forall d x, eok x -> eok (unshift d x);
  shift_unshift : forall d x, eok x -> shift d (unshift d x) = x;
  unshift_shift : forall d x, eok x -> cle d (uses x) -> unshift d (shift d x) = x;
  unshift_unshift : forall d1 d2 x, unshift d1 (unshift d2 x) = unshift (cplus d1 d2) x;
  unshift_ext : forall d d' x,
    (forall k, cget (uses x) k <> None -> dval d k = dval d' k) -> unshift d x = unshift d' x;
  uses_unshift : forall d x k, cget (uses (unshift d x)) k = oadd (cget d k) (cget (uses x) k);
  uses_shift : forall d x k, cget (uses (shift d x)) k = osub (cget (uses x) k) (cget d k)
}.

Section Lists.

Context {X : Type} {BX : Based X} {LX : BasedLaws X}.

(** The minimum use of a list of elements (with [None] as ∞). *)
Definition lmin (l : list X) (k : positive) : option nat :=
  fold_right (fun e acc => omin (cget (uses e) k) acc) None l.

(** ** Lemmas about minima *)

Lemma lmin_app l1 l2 k : lmin (l1 ++ l2) k = omin (lmin l1 k) (lmin l2 k).
Proof.
  induction l1 as [|e l1 IH]; [reflexivity|].
  change (omin (cget (uses e) k) (lmin (l1 ++ l2) k)
          = omin (omin (cget (uses e) k) (lmin l1 k)) (lmin l2 k)).
  rewrite IH; destruct (cget (uses e) k), (lmin l1 k), (lmin l2 k); cbn; f_equal; lia.
Qed.

Lemma lmin_unshift d l k : lmin (map (unshift d) l) k = oadd (cget d k) (lmin l k).
Proof.
  induction l as [|e l IH]; [destruct (cget d k); reflexivity|].
  change (omin (cget (uses (unshift d e)) k) (lmin (map (unshift d) l) k)
          = oadd (cget d k) (omin (cget (uses e) k) (lmin l k))).
  rewrite IH, uses_unshift, oadd_omin; reflexivity.
Qed.

Lemma lmin_shift d l k : lmin (map (shift d) l) k = osub (lmin l k) (cget d k).
Proof.
  induction l as [|e l IH]; [reflexivity|].
  change (omin (cget (uses (shift d e)) k) (lmin (map (shift d) l) k)
          = osub (omin (cget (uses e) k) (lmin l k)) (cget d k)).
  rewrite IH, uses_shift, osub_omin; reflexivity.
Qed.

Lemma lmin_le l e k m : In e l -> cget (uses e) k = Some m -> exists n, lmin l k = Some n /\ n <= m.
Proof.
  induction l as [|e' l IH]; [intros []|].
  change (lmin (e' :: l) k) with (omin (cget (uses e') k) (lmin l k)).
  intros [->|Hin] Hm.
  - rewrite Hm; destruct (lmin l k) as [p|]; cbn [omin]; eexists; (split; [reflexivity|lia]).
  - destruct (IH Hin Hm) as [n [Hn Hle]]; rewrite Hn.
    destruct (cget (uses e') k) as [p|]; cbn [omin]; eexists; (split; [reflexivity|lia]).
Qed.

Lemma lmin_some l e k : In e l -> cget (uses e) k <> None -> lmin l k <> None.
Proof.
  intros Hin Hu; destruct (cget (uses e) k) as [m|] eqn:E; [|contradiction].
  destruct (lmin_le l e k m Hin E) as [n [Hn _]]; congruence.
Qed.

Lemma cle_lmin d l e : (forall k, cget d k = lmin l k) -> In e l -> cle d (uses e).
Proof.
  intros Hd Hin k n m Hn Hm; rewrite Hd in Hn.
  destruct (lmin_le l e k m Hin Hm) as [n' [Hn' Hle]]; congruence.
Qed.

Lemma cle_cmin_l a b : cle (cmin a b) a.
Proof.
  intros k n m; rewrite cget_cmin; destruct (cget a k), (cget b k); cbn;
    intros [= <-] [= <-]; lia.
Qed.

Lemma cle_cmin_r a b : cle (cmin a b) b.
Proof.
  intros k n m; rewrite cget_cmin; destruct (cget a k), (cget b k); cbn;
    intros [= <-] [= <-]; lia.
Qed.

Lemma cle_trans a b c : cle a b -> (forall k, cget a k <> None -> cget b k <> None) -> cle b c -> cle a c.
Proof.
  intros H1 Hd H2 k n m Ha Hc.
  destruct (cget b k) as [p|] eqn:Eb; [|exfalso; apply (Hd k); congruence].
  specialize (H1 k n p Ha Eb); specialize (H2 k p m Eb Hc); lia.
Qed.

Lemma lmin_single e k : lmin [e] k = cget (uses e) k.
Proof. cbn; destruct (cget (uses e) k); reflexivity. Qed.

(** A minimum below [a] is below every element counted in [a]. *)
Lemma cle_mem m a L e :
  cle m a -> (forall k, cget a k = lmin L k) -> In e L -> cle m (uses e).
Proof.
  intros Hm Ha Hin k n q Hn Hq.
  destruct (lmin_le L e k q Hin Hq) as [p [Hp Hle]].
  rewrite <- Ha in Hp; specialize (Hm k n p Hn Hp); lia.
Qed.

Lemma cle_min3_1 u a b : cle (cmin u (cmin a b)) u.
Proof.
  intros k n m; rewrite !cget_cmin; destruct (cget u k), (cget a k), (cget b k); cbn;
    intros [= <-] [= <-]; lia.
Qed.

Lemma cle_min3_2 u a b : cle (cmin u (cmin a b)) a.
Proof.
  intros k n m; rewrite !cget_cmin; destruct (cget u k), (cget a k), (cget b k); cbn;
    intros [= <-] [= <-]; lia.
Qed.

Lemma cle_min3_3 u a b : cle (cmin u (cmin a b)) b.
Proof.
  intros k n m; rewrite !cget_cmin; destruct (cget u k), (cget a k), (cget b k); cbn;
    intros [= <-] [= <-]; lia.
Qed.

(** ** Moving lists of elements between bases *)

Section Moving.

Variables (a : counts) (L : list X).
Hypothesis Ha : forall k, cget a k = lmin (map (unshift a) L) k.
Hypothesis Hok : forall e, In e L -> eok e.

Lemma uses_below e k : In e L -> cget (uses e) k <> None -> cget a k <> None.
Proof.
  intros Hin Hu; rewrite Ha; apply (lmin_some _ (unshift a e)); [apply in_map, Hin|].
  rewrite uses_unshift; intro H; apply oadd_none in H; contradiction.
Qed.

(** Raising the base of the top by [m]. *)
Lemma rebase_one m e :
  cle m a -> In e L -> unshift (csub a m) e = shift m (unshift a e).
Proof.
  intros Hm Hin.
  assert (unshift a e = unshift m (unshift (csub a m) e)) as ->.
  { rewrite unshift_unshift; apply unshift_ext; intros k Hk.
    rewrite dval_cplus; unfold dval; rewrite cget_csub.
    destruct (cget a k) as [p|] eqn:E; [|exfalso; apply (uses_below e k Hin Hk), E].
    destruct (cget m k) as [n|] eqn:F; cbn; [specialize (Hm k n p F E)|]; lia. }
  symmetry; apply shift_unshift, ok_unshift, Hok, Hin.
Qed.

Lemma rebase_list m :
  cle m a -> map (unshift (csub a m)) L = map (shift m) (map (unshift a) L).
Proof.
  intros Hm; rewrite map_map; apply map_ext_in; intros e Hin; apply rebase_one; assumption.
Qed.

(** Lowering the base of the top by [d]. *)
Lemma lift_one d e : In e L -> unshift (cadd d a) e = unshift d (unshift a e).
Proof.
  intros Hin; rewrite unshift_unshift.
  apply unshift_ext; intros k Hk; rewrite dval_cplus; unfold dval; rewrite cget_cadd.
  destruct (cget a k) as [p|] eqn:E; [|exfalso; apply (uses_below e k Hin Hk), E].
  destruct (cget d k); reflexivity.
Qed.

Lemma lift_list d : map (unshift (cadd d a)) L = map (unshift d) (map (unshift a) L).
Proof. rewrite map_map; apply map_ext_in; intros e Hin; apply lift_one, Hin. Qed.

End Moving.

(** A minimum is attained. *)
Lemma lmin_attained l k n : lmin l k = Some n -> exists e, In e l /\ cget (uses e) k = Some n.
Proof.
  induction l as [|e l IH]; [discriminate|].
  change (lmin (e :: l) k) with (omin (cget (uses e) k) (lmin l k)).
  destruct (cget (uses e) k) as [p|] eqn:Ep, (lmin l k) as [q|] eqn:Eq; cbn [omin]; intros H.
  - destruct (Nat.min_spec p q) as [[_ E]|[_ E]]; rewrite E in H; injection H as <-.
    + exists e; split; [left|]; auto.
    + destruct (IH eq_refl) as [e' [Hin He]]; exists e'; split; [right|]; auto.
  - injection H as <-; exists e; split; [left|]; auto.
  - destruct (IH H) as [e' [Hin He]]; exists e'; split; [right|]; auto.
  - discriminate.
Qed.

(** The minimum depends only on which elements occur. *)
Lemma lmin_same_members l1 l2 k : (forall e, In e l1 <-> In e l2) -> lmin l1 k = lmin l2 k.
Proof.
  assert (H : forall l, lmin l k = None /\ (forall e, In e l -> cget (uses e) k = None)
                     \/ exists n, lmin l k = Some n
                                 /\ (exists e, In e l /\ cget (uses e) k = Some n)
                                 /\ (forall e m, In e l -> cget (uses e) k = Some m -> n <= m)).
  { induction l as [|e l IH]; [left; split; [reflexivity|intros _ []]|].
    change (lmin (e :: l) k) with (omin (cget (uses e) k) (lmin l k)).
    destruct IH as [[E1 E2]|[n [E1 [[e0 [He0 Hn]] E3]]]]; rewrite E1;
      destruct (cget (uses e) k) as [p|] eqn:Ep; cbn [omin].
    - right; exists p; repeat split; [exists e; split; [left|]; auto|].
      intros e' m [<-|Hin] Hm; [rewrite Ep in Hm; injection Hm as <-; lia|].
      rewrite E2 in Hm by exact Hin; discriminate.
    - left; split; [reflexivity|intros e' [<-|Hin]; auto].
    - right; exists (Nat.min p n); split; [reflexivity|split].
      + destruct (Nat.min_spec p n) as [[_ ->]|[_ ->]];
          [exists e; split; [left|]; auto|exists e0; split; [right|]; auto].
      + intros e' m [<-|Hin] Hm; [rewrite Ep in Hm; injection Hm as <-; lia|].
        specialize (E3 e' m Hin Hm); lia.
    - right; exists n; split; [reflexivity|split; [exists e0; split; [right|]; auto|]].
      intros e' m [<-|Hin] Hm; [congruence|apply (E3 e' m Hin Hm)]. }
  intros Hm.
  destruct (H l1) as [[A1 B1]|[n1 [A1 [[e1 [I1 U1]] C1]]]],
           (H l2) as [[A2 B2]|[n2 [A2 [[e2 [I2 U2]] C2]]]]; rewrite A1, A2.
  - reflexivity.
  - rewrite B1 in U2 by (apply Hm, I2); discriminate.
  - rewrite B2 in U1 by (apply Hm, I1); discriminate.
  - f_equal; apply Nat.le_antisymm; [apply (C1 e2); [apply Hm|]|apply (C2 e1); [apply Hm|]]; assumption.
Qed.

End Lists.
