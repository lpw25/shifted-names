(** * Tools for the canonical layered word

    Segments as lists of entries; terms on bound variables in front of a
    segment ([tfront]); carrying terms along a word by bound variables
    ([thread]); an inverse of a renaming ([sinv]).

    [Canonical] builds the canonical word with these. *)

From Stdlib Require Import Arith List Lia Bool.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Normalise Layered.
From ShiftedNames.Core Require Export Merge.
Import ListNotations.

Section Canon.

Variable F : order.
Variable ntm : nat.

(** ** Segments as lists of entries *)

Fixpoint ents (s : seg) : list (lexp * tlist * nat) :=
  match s with SNil => [] | SEnt h ts m r => (h, ts, m) :: ents r end.

Definition bent (s : seg) : tlist * nat := match sfind F LNone s with Some e => ofe e | None => (TNil, 0) end.

(** Labels known to be in increasing order. *)
Fixpoint lsortb (l : list lexp) : bool :=
  match l with
  | g :: r => match r with
              | h :: _ => match lcmp F g h with Some Lt => lsortb r | _ => false end
              | [] => true
              end
  | [] => true
  end.

(** Entries in the order of their labels are a segment as they are. *)
Definition mkseg (es : list (lexp * tlist * nat)) : option seg :=
  if lsortb (map (fun e => fst (fst e)) es)
  then Some (fold_right (fun '(h, ts, m) acc => mkent h ts m acc) SNil es)
  else fold_right (fun '(h, ts, m) acc => obind acc (sset F h ts m)) (Some SNil) es.

Definition vars (l : list (lexp * nat)) : tlist := tl_of (map (fun v => NVar (fst v) (snd v)) l).
Definition bvars (l : list nat) : tlist := tl_of (map (NVar LNone) l).

Definition mem (j : nat) (l : list nat) : bool := existsb (Nat.eqb j) l.

(** The order on variables: by label, then index. *)
Definition vless (a b : lexp * nat) : bool :=
  match lcmp F (fst a) (fst b) with Some Lt => true | Some Eq => snd a <? snd b | _ => false end.

Definition vmin (l : list (lexp * nat)) : option (lexp * nat) :=
  fold_right (fun v acc => match acc with None => Some v | Some w => if vless v w then Some v else Some w end) None l.

Fixpoint findix (t : ntgt) (ts : tlist) (k : nat) : list nat :=
  match ts with TNil => [] | TCons t' r => (if ntgt_eqb t t' then [k] else []) ++ findix t r (S k) end.

(** The named inputs of [s1] with the target [t]. *)
Definition named_srcs (s1 : seg) (t : ntgt) : list (lexp * nat) :=
  flat_map (fun '(h, ts, m) => match h with LNone => [] | _ => map (fun k => (h, k)) (findix t ts 0) end) (ents s1)
  ++ match t with
     | NVar LNone _ => []
     | NVar g i =>
         match sfind F g s1 with
         | Some (Some (ts, m)) => if m <=? i then [(g, i - m + tlen ts)] else []
         | Some None => [(g, i)]
         | None => []
         end
     | _ => []
     end.

Definition veqb (a b : lexp * nat) : bool := lexp_eqb (fst a) (fst b) && Nat.eqb (snd a) (snd b).

(** The inputs that may not be their own representative. *)
Definition cands (s1 : seg) : list (lexp * nat) :=
  flat_map (fun '(h, ts, m) => map (fun k => (h, k)) (seq 0 (tlen ts))) (ents s1)
  ++ flat_map (fun t => match t with
                        | NVar g i => match sfind F g s1 with
                                      | Some (Some (ts, m)) => if m <=? i then [(g, i - m + tlen ts)] else []
                                      | Some None => [(g, i)]
                                      | None => []
                                      end
                        | _ => [] end) (stargets s1).

(** Bound variables below the default region, in the order they are
    first used. *)
Fixpoint nodup_nat (l : list nat) (seen : list nat) : list nat :=
  match l with [] => [] | x :: r => if mem x seen then nodup_nat r seen else x :: nodup_nat r (x :: seen) end.

Fixpoint index_of (x : nat) (l : list nat) (k : nat) : nat :=
  match l with [] => k | y :: r => if Nat.eqb x y then k else index_of x r (S k) end.

Definition nterms (s : seg) : nat := List.length (filter is_term (stargets s)).

Definition tfront (T : list ntgt) (s : seg) : option seg :=
  fold_right (fun t acc => obind acc (sfront F LNone t)) (Some s) T.

Definition is_pure (t : ntgt) : bool := match t with NBind u (WEnd SNil) None => u <? ntm | _ => false end.

Fixpoint thread (j : nat) (T : list ntgt) (K : lword) : option lword :=
  match j, K with
  | 1, LS s1 :: K' => option_map (fun x => LS x :: K') (tfront T s1)
  | S j', LS s1 :: K' =>
      match slifts F ntm (List.length T) s1, thread j' T K' with
      | Some a, Some b => Some (LS a :: b)
      | _, _ => None
      end
  | _, _ => None
  end.

Definition named_term (s : seg) : bool := has_terms (sdrop_none s).

(** ** Going behind the first layer *)

(** An inverse of a renaming of named variables; named outputs that
    nothing is sent to come back from fresh bound variables [R]. *)
Definition sinv (sg : seg) : option (seg * list ntgt) :=
  fold_right (fun '(g, ts, m) acc =>
    obind acc (fun '(a, R) =>
      let pre := map (fun i => (i, vmin (named_srcs sg (NVar g i)))) (seq 0 m) in
      let miss := filter (fun p => match snd p with None => true | _ => false end) pre in
      let tg := fun p => match snd p with
                         | Some (h, k) => NVar h k
                         | None => NVar LNone (List.length R + index_of (fst p) (map fst miss) 0)
                         end in
      match sset F g (tl_of (map tg pre)) (tlen ts) a with
      | Some a' => Some (a', R ++ map (fun p => NVar g (fst p)) miss)
      | None => None
      end)) (Some (SNil, [])) (ents sg).

Definition lcmp3 (a b : lexp) : comparison := match lcmp F a b with Some c => c | None => Eq end.

Fixpoint linsert (g : lexp) (l : list lexp) : list lexp :=
  match l with
  | [] => [g]
  | h :: r => match lcmp F g h with Some Lt => g :: l | Some Eq => l | _ => h :: linsert g r end
  end.

Definition wlabs (l : lword) : list lexp :=
  fold_right (fun x acc =>
    match x with
    | LS sg => fold_right (fun '(g, _, _) a => match g with LNone => a | _ => linsert g a end) acc (ents sg)
    | _ => acc
    end) [] l.

Definition wbound (l : lword) : nat :=
  fold_right (fun x acc => match x with LS sg => List.length (stargets sg) + acc | _ => acc end) 2 l.

(** ** In front of an atom

    A segment with terms in front of a lifted atom: the variables it
    sends around the atom are put in canonical form as above, among the
    variables the lifts pass around, and a bound variable that nothing
    reaches is one lift less.  The result is checked by composing. *)
Definition lcn (L : list (lexp * nat)) (g : lexp) : nat := match lcnt F g L with Some c => c | None => 0 end.

Definition setb (L : list (lexp * nat)) (c : nat) : list (lexp * nat) :=
  filter (fun p => negb (lexp_eqb (fst p) LNone)) L ++ match c with 0 => [] | _ => [(LNone, c)] end.

End Canon.

(** ** Soundness *)

Section Sound.

Context {T : Type}.
Variable lenv : list label.
Variable tenv : list T.
Variable aenv : list (radj T).
Variable penv : list (rpadj T).
Variable F : order.
Hypothesis HF : facts_ok lenv F.
Variable ntm : nat.
Hypothesis Hntm : ntm <= List.length tenv.

Local Notation lden := (lden lenv).
Local Notation tden := (tden lenv tenv aenv penv).
Local Notation sden := (sden lenv tenv aenv penv).
Local Notation wden := (wden lenv tenv aenv penv).
Local Notation sdistd := (sdistd lenv).
Local Notation tdist := (tdist lenv).
Local Notation tldist := (tldist lenv).
Local Notation wdist := (wdist lenv).
Local Notation lwden := (lwden lenv tenv aenv penv).
Local Notation lwdist := (lwdist lenv).


(** *** The merge *)

Local Notation esem := (esem lenv tenv aenv penv).

(** Entries of the bound label in front of an adjustment. *)
Definition pins (ts : list (rtarget T)) (X : radj T) : radj T := fold_right (rpush_inner None) X ts.

Lemma pins_compose_l a ts X : rcompose a (pins ts X) = pins (map (rapply_target a) ts) (rcompose a X).
Proof. induction ts as [|t ts IH]; cbn [pins fold_right map]; [reflexivity|]; rewrite rcompose_push_inner_r; fold (pins ts X); rewrite IH; reflexivity. Qed.

Lemma pins_compose_r ts X B : pins ts (rcompose X B) = rcompose (pins ts X) (lifted (List.length ts) B).
Proof.
  induction ts as [|t ts IH]; cbn [pins fold_right length]; [reflexivity|].
  fold (pins ts (rcompose X B)); fold (pins ts X); rewrite IH, (rpush_inner_compose tenv ntm Hntm); reflexivity.
Qed.

Lemma tfront_sound Ts : forall s s', sdistd s -> Forall tdist Ts -> tfront F Ts s = Some s' ->
  sdistd s' /\ sden s' = pins (map tden Ts) (sden s).
Proof.
  induction Ts as [|t Ts IH]; intros s s' Hs HT; cbn [tfront fold_right].
  - intros H; injection H as <-; split; [exact Hs|reflexivity].
  - inversion HT as [|? ? Ht HT']; subst.
    fold (tfront F Ts s); destruct (tfront F Ts s) as [s0|] eqn:E; [|discriminate]; cbn [obind]; intros H.
    destruct (IH s s0 Hs HT' E) as [Hd0 D0].
    destruct (sfront_sound lenv tenv aenv penv F HF ntm Hntm LNone t s0 s' Hd0 Ht H) as [Hd D].
    split; [exact Hd|]; rewrite D, D0; reflexivity.
Qed.

Lemma thread_0 Ts K : thread F ntm 0 Ts K = None.
Proof. destruct K as [|[?|? ?] ?]; reflexivity. Qed.

Lemma thread_SS j Ts s1 K :
  thread F ntm (S (S j)) Ts (LS s1 :: K)
  = match slifts F ntm (List.length Ts) s1, thread F ntm (S j) Ts K with
    | Some a, Some b => Some (LS a :: b)
    | _, _ => None
    end.
Proof. reflexivity. Qed.

Lemma thread_nil j Ts : thread F ntm j Ts [] = None.
Proof. destruct j as [|[|j]]; reflexivity. Qed.

Lemma thread_atom j Ts L a K : thread F ntm j Ts (LA L a :: K) = None.
Proof. destruct j as [|[|j]]; reflexivity. Qed.

Lemma thread_sound j : forall Ts K Kp, lwdist K -> Forall tdist Ts -> thread F ntm j Ts K = Some Kp ->
  lwdist Kp /\ lwden Kp = pins (map (fun t => rapply_target (lwden (skipn j K)) (tden t)) Ts) (lwden K).
Proof.
  induction j as [|j IH]; intros Ts K Kp HK HT.
  { rewrite thread_0; discriminate. }
  destruct K as [|[s1|L a] K']; [rewrite thread_nil; discriminate| |rewrite thread_atom; discriminate].
  inversion HK as [|? ? Hs1 HK']; subst.
  destruct j as [|j].
  - cbn [thread]; destruct (tfront F Ts s1) as [x|] eqn:E; [|discriminate]; intros H; injection H as <-.
    destruct (tfront_sound Ts s1 x Hs1 HT E) as [Hx Dx]; split; [constructor; assumption|].
    cbn [Layered.lwden skipn]; rewrite Dx, pins_compose_l, map_map; reflexivity.
  - rewrite thread_SS; destruct (slifts F ntm (List.length Ts) s1) as [a|] eqn:Ea; [|discriminate].
    destruct (thread F ntm (S j) Ts K') as [b|] eqn:Eb; [|discriminate]; intros H; injection H as <-.
    destruct (slifts_sound lenv tenv aenv penv F HF ntm Hntm _ s1 a Hs1 Ea) as [Ha Da].
    destruct (IH Ts K' b HK' HT Eb) as [Hb Db]; split; [constructor; assumption|].
    cbn [Layered.lwden]; rewrite Db, Da.
    change (skipn (S (S j)) (LS s1 :: K')) with (skipn (S j) K').
    rewrite pins_compose_r, length_map; reflexivity.
Qed.

Lemma pure_target (A B : radj T) t : is_pure ntm t = true ->
  (forall v, v_label v <> None -> rapply A v = rapply B v) ->
  tdist t /\ rapply_target A (tden t) = rapply_target B (tden t).
Proof.
  destruct t as [|u [[|]| |] [|]]; try discriminate; cbn [is_pure]; intros Hu Hn; apply Nat.ltb_lt in Hu.
  split; [exact I|].
  destruct (nth_error tenv u) as [y|] eqn:Ey; [|apply nth_error_None in Ey; lia].
  rewrite (tden_bind lenv tenv aenv penv u (WEnd SNil) None y Ey); cbn [rapply_target bden].
  rewrite (wden_id lenv tenv aenv penv), rpcompose_identity; f_equal; apply rpcompose_named, Hn.
Qed.

End Sound.
