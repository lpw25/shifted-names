(** * Labels, expressions and their meaning

    What the normaliser ([HNorm]) and the [names] tactic work on:
    - label expressions ([lexp]): the bound label, a concrete label, or a
      label atom; the fixed order on them and the known order the facts
      give ([order_of], [lt_known], [lcmp]), proved sound for facts that
      hold ([order_of_ok]);
    - expressions ([aexp], [texp]) over label atoms, adjustment atoms and
      term atoms, which the tactic reifies goals into, and their meaning
      as the library's adjustments ([aeden]);
    - [mbase] and [drel], the relations materialising a payload gives;
    - the data the display of normal forms is built from ([seg], [word]).
    Transitivity and irreflexivity of the known order are in
    [KnownOrder]; the normaliser and its proofs in [HNorm], [CNorm],
    [CSound], [CComplete], [HRefine] and [HConcrete]. *)

From Stdlib Require Import Arith List Lia Bool String NArith PArith FMapPositive.
From ShiftedNames.Core Require Import Label Var Adjustment Laws.
Import ListNotations.

(** ** Label expressions *)

Inductive lexp : Type :=
| LNone
| LCon (s : label)
| LAtom (n : N).

Arguments LAtom n%_N_scope.

Definition lexp_eqb (a b : lexp) : bool :=
  match a, b with
  | LNone, LNone => true
  | LCon s, LCon s' => String.eqb s s'
  | LAtom n, LAtom n' => N.eqb n n'
  | _, _ => false
  end.

Lemma lexp_eqb_eq a b : lexp_eqb a b = true <-> a = b.
Proof.
  destruct a, b; cbn; split; intro H; try discriminate; try reflexivity.
  - apply String.eqb_eq in H; subst; reflexivity.
  - injection H as ->; apply String.eqb_refl.
  - apply N.eqb_eq in H; subst; reflexivity.
  - injection H as ->; apply N.eqb_refl.
Qed.

(** The fixed order: concrete labels by the string order, and the bound
    label after every other. *)
Definition lt_base (a b : lexp) : bool :=
  match a, b with
  | LCon s, LCon s' => is_less_than_label s s'
  | LNone, _ => false
  | _, LNone => true
  | _, _ => false
  end.

(** ** The known order

    The fixed order, and the facts [(x, y)] ("[x < y]"), followed
    transitively.  They are worked out once ([order_of]):
    - [otab F i j]: whether the facts put label atom [i] below atom [j];
    - [oup F i]: the least concrete label the facts put above atom [i];
    - [odown F j]: the greatest concrete label the facts put below atom [j].
    Two atoms are one lookup in the table, which also holds [i < j]
    whenever [oup i] is at or below [odown j] (through the concrete
    labels between them); an atom and a concrete label are one string
    comparison with the atom's bound; two concrete labels are compared by
    the string order, which facts that hold cannot add to.  Atoms are keyed
    by [akey], which is cheap (no carry, unlike [N.succ_pos]); [nkey] undoes
    it on the keys it makes. *)
Record order := mk_order {
  ofacts : list (lexp * lexp);
  otab : positive -> positive -> bool;
  oup : positive -> option label;
  odown : positive -> option label }.

Definition akey (n : N) : positive := match n with N0 => xH | Npos p => xI p end.

Definition nkey (k : positive) : N := match k with xI p => Npos p | _ => N0 end.

(** Labels compared in one pass: each character once, its bits from the
    top (as [is_less_than_label], which compares each character twice). *)
Definition acmp (x y : Ascii.ascii) : comparison :=
  let '(Ascii.Ascii a1 a2 a3 a4 a5 a6 a7 a8) := x in
  let '(Ascii.Ascii c1 c2 c3 c4 c5 c6 c7 c8) := y in
  match a8, c8 with
    | true, false => Gt
    | false, true => Lt
    | _, _ => match a7, c7 with
      | true, false => Gt
      | false, true => Lt
      | _, _ => match a6, c6 with
        | true, false => Gt
        | false, true => Lt
        | _, _ => match a5, c5 with
          | true, false => Gt
          | false, true => Lt
          | _, _ => match a4, c4 with
            | true, false => Gt
            | false, true => Lt
            | _, _ => match a3, c3 with
              | true, false => Gt
              | false, true => Lt
              | _, _ => match a2, c2 with
                | true, false => Gt
                | false, true => Lt
                | _, _ => match a1, c1 with
                  | true, false => Gt
                  | false, true => Lt
                  | _, _ => Eq
                  end
                end
              end
            end
          end
        end
      end
    end.

Fixpoint lab_cmp (s t : label) : comparison :=
  match s, t with
  | EmptyString, EmptyString => Eq
  | String a _, EmptyString => if is_nul a then Lt else Gt
  | EmptyString, String b _ => if is_nul b then Gt else Lt
  | String a s', String b t' => match acmp a b with Eq => lab_cmp s' t' | c => c end
  end.

Definition lab_lt (s t : label) : bool := match lab_cmp s t with Lt => true | _ => false end.

Definition leb_lab (s t : label) : bool := match lab_cmp s t with Gt => false | _ => true end.

Definition lt_known (F : order) (a b : lexp) : bool :=
  match a, b with
  | LAtom i, LAtom j => otab F (akey i) (akey j)
  | LAtom i, LCon s => match oup F (akey i) with Some u => leb_lab u s | None => false end
  | LCon s, LAtom j => match odown F (akey j) with Some d => leb_lab s d | None => false end
  | LCon s, LCon t => lab_lt s t
  | _, _ => lt_base a b
  end.

(** *** The table

    The facts between atoms are the edges of a graph; for each atom, the
    atoms reachable from it are found by a depth-first search, and kept as
    a map keyed by [akey]: O(A (A + E)) for A atoms and E edges. *)

Definition succs (adj : PositiveMap.t (list N)) (i : N) : list N :=
  match PositiveMap.find (akey i) adj with Some l => l | None => [] end.

Definition addedge (i j : N) (adj : PositiveMap.t (list N)) : PositiveMap.t (list N) :=
  PositiveMap.add (akey i) (j :: succs adj i) adj.

(** An atom with a concrete label directly above it gets an entry, so
    that it gets a row (for its [up]) even with no edges.  Other atoms
    without edges get none: a lookup that misses stops early. *)
Definition touch (x : lexp) (adj : PositiveMap.t (list N)) : PositiveMap.t (list N) :=
  match x with
  | LAtom i => match PositiveMap.find (akey i) adj with Some _ => adj | None => PositiveMap.add (akey i) [] adj end
  | _ => adj
  end.

Definition edges (l : list (lexp * lexp)) : PositiveMap.t (list N) :=
  fold_left (fun adj '(x, y) =>
    match x, y with LAtom i, LAtom j => addedge i j adj | LAtom _, LCon _ => touch x adj | _, _ => adj end)
    l (PositiveMap.empty _).

(** A depth-first search: [visit n v seen] marks [v] and everything
    reachable from it that is not in [seen].  Each nested call marks a new
    node, so [n], the number of edges, is enough depth. *)
Fixpoint visit (adj : PositiveMap.t (list N)) (n : nat) (v : N) (seen : PositiveMap.t unit) {struct n} :
    PositiveMap.t unit :=
  match n with
  | O => seen
  | S n' =>
      match PositiveMap.find (akey v) seen with
      | Some _ => seen
      | None => fold_left (fun s w => visit adj n' w s) (succs adj v) (PositiveMap.add (akey v) tt seen)
      end
  end.

(** Every edge's target, so its length is the number of edges. *)
Definition nodes (adj : PositiveMap.t (list N)) : list N := List.concat (List.map snd (PositiveMap.elements adj)).

Definition mem (k : positive) (T : PositiveMap.t unit) : bool :=
  match PositiveMap.find k T with Some _ => true | None => false end.

Definition inset (T : PositiveMap.t unit) (j : N) : bool := mem (akey j) T.

Definition rows_of (adj : PositiveMap.t (list N)) (n : nat) : PositiveMap.t (PositiveMap.t unit) :=
  PositiveMap.mapi (fun _ st => fold_left (fun s w => visit adj n w s) st (PositiveMap.empty _)) adj.

(** *** The concrete bounds *)

(** [ble true x y]: [x] is at or below [y]; [ble false x y]: at or above. *)
Definition ble (lo : bool) (x y : label) : bool := if lo then leb_lab x y else leb_lab y x.

(** The lower ([lo]) or higher of two optional labels. *)
Definition pick (lo : bool) (o1 o2 : option label) : option label :=
  match o1, o2 with
  | Some x, Some y => Some (if ble lo x y then x else y)
  | None, o => o
  | o, None => o
  end.

Definition bump (lo : bool) (m : PositiveMap.t label) (kc : positive * label) : PositiveMap.t label :=
  let '(k, c) := kc in
  PositiveMap.add k (match PositiveMap.find k m with Some x => if ble lo x c then x else c | None => c end) m.

(** The lowest ([lo]) or highest label given for each key. *)
Definition bmap (lo : bool) (L : list (positive * label)) : PositiveMap.t label :=
  fold_left (bump lo) L (PositiveMap.empty _).

(** The concrete labels the facts put directly above, and below, atoms. *)
Definition dups (l : list (lexp * lexp)) : list (positive * label) :=
  flat_map (fun '(x, y) => match x, y with LAtom i, LCon c => [(akey i, c)] | _, _ => [] end) l.

Definition ddowns (l : list (lexp * lexp)) : list (positive * label) :=
  flat_map (fun '(x, y) => match x, y with LCon c, LAtom i => [(akey i, c)] | _, _ => [] end) l.

(** The least label directly above the atom [k] or one of its row. *)
Definition upval (d0 : PositiveMap.t label) (k : positive) (row : PositiveMap.t unit) : option label :=
  fold_left (pick true) (map (fun kt => PositiveMap.find (fst kt) d0) (PositiveMap.elements row)) (PositiveMap.find k d0).

(** Each label directly below an atom is below it and the atoms of its row. *)
Definition downs (dd : PositiveMap.t label) (rows : PositiveMap.t (PositiveMap.t unit)) : list (positive * label) :=
  PositiveMap.elements dd ++
  flat_map (fun '(k, row) =>
    match PositiveMap.find k dd with
    | Some c => map (fun kt => (fst kt, c)) (PositiveMap.elements row)
    | None => []
    end) (PositiveMap.elements rows).

(** A row with every atom whose [down] is at or above the row's [up]. *)
Definition extend (u : option label) (dml : list (positive * label)) (row : PositiveMap.t unit) : PositiveMap.t unit :=
  match u with
  | None => row
  | Some u => fold_left (fun s '(k, d) => if leb_lab u d then PositiveMap.add k tt s else s) dml row
  end.

Definition tab_of (d0 : PositiveMap.t label) (dml : list (positive * label)) (rows : PositiveMap.t (PositiveMap.t unit)) :
    PositiveMap.t (PositiveMap.t unit * option label) :=
  PositiveMap.mapi (fun k row => let u := upval d0 k row in (extend u dml row, u)) rows.

(** The lookups, kept in separate maps: unpacking a pair on every
    comparison costs about 10% on the commonest families. *)
Definition tmem (t : PositiveMap.t (PositiveMap.t unit)) (ki kj : positive) : bool :=
  match PositiveMap.find ki t with Some r => mem kj r | None => false end.

Definition tup (ups : PositiveMap.t (option label)) (ki : positive) : option label :=
  match PositiveMap.find ki ups with Some u => u | None => None end.

Definition dfind (dm : PositiveMap.t label) (kj : positive) : option label := PositiveMap.find kj dm.

Definition order_of (l : list (lexp * lexp)) : order :=
  let adj := edges l in
  let rows := rows_of adj (List.length (nodes adj)) in
  let dm := bmap false (downs (bmap false (ddowns l)) rows) in
  let tp := tab_of (bmap true (dups l)) (PositiveMap.elements dm) rows in
  mk_order l (tmem (PositiveMap.mapi (fun _ p => fst p) tp)) (tup (PositiveMap.mapi (fun _ p => snd p) tp)) (dfind dm).

Definition lcmp_spec (F : order) (a b : lexp) : option comparison :=
  if lexp_eqb a b then Some Eq
  else if lt_known F a b then Some Lt
  else if lt_known F b a then Some Gt
  else None.

(** [lcmp_spec], with two concrete labels compared in one pass. *)
Definition lcmp (F : order) (a b : lexp) : option comparison :=
  match a, b with
  | LCon s, LCon t => Some (lab_cmp s t)
  | _, _ => lcmp_spec F a b
  end.

(** *** Facts about keys, bounds and rows *)

Lemma akey_inj i j : akey i = akey j -> i = j.
Proof. destruct i as [|p], j as [|q]; cbn; intros E; try discriminate; [reflexivity|injection E as ->; reflexivity]. Qed.

Lemma nkey_akey n : nkey (akey n) = n.
Proof. destruct n; reflexivity. Qed.

(** A map whose keys are all keys of atoms. *)
Definition akeyed {A} (m : PositiveMap.t A) : Prop := forall k x, PositiveMap.find k m = Some x -> akey (nkey k) = k.

Lemma akeyed_empty {A} : akeyed (PositiveMap.empty A).
Proof. intros k x H; rewrite PositiveMap.gempty in H; discriminate. Qed.

Lemma akeyed_add {A} (m : PositiveMap.t A) i x : akeyed m -> akeyed (PositiveMap.add (akey i) x m).
Proof.
  intros H k y E; destruct (Pos.eq_dec k (akey i)) as [->|Ne]; [rewrite nkey_akey; reflexivity|].
  rewrite PositiveMap.gso in E by exact Ne; exact (H k y E).
Qed.

Lemma elements_key {A} (m : PositiveMap.t A) kt : akeyed m -> In kt (PositiveMap.elements m) -> akey (nkey (fst kt)) = fst kt.
Proof. destruct kt as [k x]; intros H E; apply PositiveMap.elements_complete in E; exact (H k x E). Qed.

Lemma acmp_spec a b : acmp a b =
  if is_less_than_ascii a b then Lt else if is_less_than_ascii b a then Gt else Eq.
Proof.
  destruct a as [a1 a2 a3 a4 a5 a6 a7 a8], b as [c1 c2 c3 c4 c5 c6 c7 c8].
  destruct a8, c8; cbn; try reflexivity.
  all: destruct a7, c7; cbn; try reflexivity.
  all: destruct a6, c6; cbn; try reflexivity.
  all: destruct a5, c5; cbn; try reflexivity.
  all: destruct a4, c4; cbn; try reflexivity.
  all: destruct a3, c3; cbn; try reflexivity.
  all: destruct a2, c2; cbn; try reflexivity.
  all: destruct a1, c1; cbn; reflexivity.
Qed.

Lemma lab_cmp_spec s t : lab_cmp s t =
  if is_less_than_label s t then Lt else if is_less_than_label t s then Gt else Eq.
Proof.
  revert t; induction s as [|a s IH]; intros [|b t]; cbn [lab_cmp is_less_than_label].
  - reflexivity.
  - destruct (is_nul b); reflexivity.
  - destruct (is_nul a); reflexivity.
  - rewrite acmp_spec; destruct (is_less_than_ascii a b) eqn:E1; [reflexivity|].
    destruct (is_less_than_ascii b a); [reflexivity|apply IH].
Qed.

Lemma lab_lt_eq s t : lab_lt s t = is_less_than_label s t.
Proof. unfold lab_lt; rewrite lab_cmp_spec; destruct (is_less_than_label s t); [reflexivity|destruct (is_less_than_label t s); reflexivity]. Qed.

Lemma leb_lab_eq s t : leb_lab s t = if String.eqb s t then true else is_less_than_label s t.
Proof.
  unfold leb_lab; rewrite lab_cmp_spec; destruct (String.eqb_spec s t) as [->|Ne].
  - destruct (is_less_than_label t t) eqn:E; [exfalso; exact (label_lt_irrefl t E)|reflexivity].
  - destruct (is_less_than_label s t) eqn:E1; [reflexivity|].
    destruct (is_less_than_label t s) eqn:E2; [reflexivity|exfalso; exact (Ne (is_less_than_label_total _ _ E1 E2))].
Qed.

Lemma lcmp_eq F a b : lcmp F a b = lcmp_spec F a b.
Proof.
  destruct a as [|s|i], b as [|t|j]; try reflexivity; unfold lcmp, lcmp_spec, lt_known; cbn [lexp_eqb].
  rewrite !lab_lt_eq, lab_cmp_spec; destruct (String.eqb_spec s t) as [->|Ne].
  - destruct (is_less_than_label t t) eqn:E; [exfalso; exact (label_lt_irrefl t E)|reflexivity].
  - destruct (is_less_than_label s t) eqn:E1; [reflexivity|].
    destruct (is_less_than_label t s) eqn:E2; [reflexivity|exfalso; exact (Ne (is_less_than_label_total _ _ E1 E2))].
Qed.

Lemma leb_lab_iff s t : leb_lab s t = true <-> s = t \/ label_lt s t.
Proof.
  rewrite leb_lab_eq; destruct (String.eqb_spec s t) as [->|Ne]; [split; [left; reflexivity|reflexivity]|].
  split; [intros H; right; exact H|intros [E|H]; [contradiction|exact H]].
Qed.

Lemma leb_lab_refl s : leb_lab s s = true.
Proof. apply leb_lab_iff; left; reflexivity. Qed.

Lemma leb_lab_false s t : leb_lab s t = false -> label_lt t s.
Proof.
  rewrite leb_lab_eq; destruct (String.eqb_spec s t) as [_|Ne]; [discriminate|]; intros H.
  destruct (label_trichotomy s t) as [L|[E|L]]; [unfold label_lt, label_ltb in L; congruence|contradiction|exact L].
Qed.

Lemma leb_lt_trans a b c : leb_lab a b = true -> label_lt b c -> label_lt a c.
Proof. intros H1 H2; apply leb_lab_iff in H1 as [->|H1]; [exact H2|exact (label_lt_trans _ _ _ H1 H2)]. Qed.

Lemma lt_leb_trans a b c : label_lt a b -> leb_lab b c = true -> label_lt a c.
Proof. intros H1 H2; apply leb_lab_iff in H2 as [<-|H2]; [exact H1|exact (label_lt_trans _ _ _ H1 H2)]. Qed.

Lemma leb_lab_trans a b c : leb_lab a b = true -> leb_lab b c = true -> leb_lab a c = true.
Proof.
  intros H1 H2; apply leb_lab_iff in H1 as [->|H1]; [exact H2|].
  apply leb_lab_iff; right; exact (lt_leb_trans _ _ _ H1 H2).
Qed.

Lemma lt_leb a b : label_lt a b -> leb_lab a b = true.
Proof. intros H; apply leb_lab_iff; right; exact H. Qed.

Lemma ble_refl lo x : ble lo x x = true.
Proof. destruct lo; apply leb_lab_refl. Qed.

Lemma ble_total lo x y : ble lo x y = false -> ble lo y x = true.
Proof. destruct lo; cbn; intros H; apply lt_leb, leb_lab_false, H. Qed.

Lemma ble_trans lo x y z : ble lo x y = true -> ble lo y z = true -> ble lo x z = true.
Proof. destruct lo; cbn; intros H1 H2; [exact (leb_lab_trans _ _ _ H1 H2)|exact (leb_lab_trans _ _ _ H2 H1)]. Qed.

Lemma pick_le_l lo x p : exists m, pick lo (Some x) p = Some m /\ ble lo m x = true.
Proof.
  destruct p as [y|]; cbn [pick]; [|exists x; split; [reflexivity|apply ble_refl]].
  destruct (ble lo x y) eqn:E; eexists; (split; [reflexivity|]); [apply ble_refl|apply ble_total, E].
Qed.

Lemma pick_le_r lo o y : exists m, pick lo o (Some y) = Some m /\ ble lo m y = true.
Proof.
  destruct o as [x|]; cbn [pick]; [|exists y; split; [reflexivity|apply ble_refl]].
  destruct (ble lo x y) eqn:E; eexists; (split; [reflexivity|]); [exact E|apply ble_refl].
Qed.

Lemma pick_fold_sound lo : forall L o m, fold_left (pick lo) L o = Some m -> o = Some m \/ In (Some m) L.
Proof.
  induction L as [|p L IH]; intros o m H; cbn [fold_left] in H; [left; exact H|].
  destruct (IH _ _ H) as [E|E]; [|right; right; exact E].
  destruct o as [x|], p as [y|]; cbn [pick] in E; try discriminate.
  - destruct (ble lo x y); injection E as <-; [left; reflexivity|right; left; reflexivity].
  - left; exact E.
  - right; left; exact E.
Qed.

Lemma pick_fold_best lo : forall L o c, (exists m, o = Some m /\ ble lo m c = true) \/ In (Some c) L ->
  exists m, fold_left (pick lo) L o = Some m /\ ble lo m c = true.
Proof.
  induction L as [|p L IH]; intros o c H; cbn [fold_left]; [destruct H as [H|[]]; exact H|].
  apply IH; destruct H as [[m [-> Hm]]|[->|H]].
  - left; destruct (pick_le_l lo m p) as [m' [E Hm']]; exists m'; split; [exact E|exact (ble_trans _ _ _ _ Hm' Hm)].
  - left; exact (pick_le_r lo o c).
  - right; exact H.
Qed.

(** The labels given for a key. *)
Definition vals (k : positive) (L : list (positive * label)) : list (option label) :=
  map (fun kc => Some (snd kc)) (filter (fun kc => Pos.eqb (fst kc) k) L).

Lemma vals_in k c L : In (Some c) (vals k L) <-> In (k, c) L.
Proof.
  unfold vals; rewrite in_map_iff; split.
  - intros [[k' c'] [E H]]; apply filter_In in H as [H Ek]; cbn in E, Ek; injection E as ->.
    apply Pos.eqb_eq in Ek; subst k'; exact H.
  - intros H; exists (k, c); split; [reflexivity|apply filter_In; split; [exact H|apply Pos.eqb_refl]].
Qed.

Lemma bump_fold lo k : forall L m, PositiveMap.find k (fold_left (bump lo) L m) = fold_left (pick lo) (vals k L) (PositiveMap.find k m).
Proof.
  induction L as [|[k' c] L IH]; intros m; [reflexivity|]; cbn [fold_left]; rewrite IH; unfold vals; cbn [filter fst].
  unfold bump; destruct (Pos.eqb_spec k' k) as [->|Ne].
  - cbn [map fold_left snd]; rewrite PositiveMap.gss; f_equal; destruct (PositiveMap.find k m); reflexivity.
  - rewrite PositiveMap.gso by (intros E; apply Ne; symmetry; exact E); reflexivity.
Qed.

Lemma bmap_sound lo L k m : PositiveMap.find k (bmap lo L) = Some m -> In (k, m) L.
Proof.
  unfold bmap; rewrite bump_fold, PositiveMap.gempty; intros H.
  destruct (pick_fold_sound lo _ _ _ H) as [E|E]; [discriminate|apply vals_in, E].
Qed.

Lemma bmap_best lo L k c : In (k, c) L -> exists m, PositiveMap.find k (bmap lo L) = Some m /\ ble lo m c = true.
Proof.
  intros H; unfold bmap; rewrite bump_fold, PositiveMap.gempty.
  apply pick_fold_best; right; apply vals_in, H.
Qed.

Lemma fold_add_mem u : forall dml row k,
  mem k (fold_left (fun s '(k', d) => if leb_lab u d then PositiveMap.add k' tt s else s) dml row) = true <->
  mem k row = true \/ exists d, In (k, d) dml /\ leb_lab u d = true.
Proof.
  induction dml as [|[k' d] dml IH]; intros row k; cbn [fold_left].
  - split; [intros H; left; exact H|intros [H|[d [[] _]]]; exact H].
  - rewrite IH; split.
    + intros [H|[d' [Hin Hl]]]; [|right; exists d'; split; [right; exact Hin|exact Hl]].
      destruct (leb_lab u d) eqn:L; [|left; exact H].
      unfold mem in H; destruct (Pos.eq_dec k k') as [->|Ne]; [right; exists d; split; [left; reflexivity|exact L]|].
      rewrite PositiveMap.gso in H by exact Ne; left; exact H.
    + intros [H|[d' [[E|Hin] Hl]]].
      * left; destruct (leb_lab u d); [|exact H]; unfold mem in *.
        destruct (Pos.eq_dec k k') as [->|Ne]; [rewrite PositiveMap.gss; reflexivity|rewrite PositiveMap.gso by exact Ne; exact H].
      * injection E as <- <-; left; rewrite Hl; unfold mem; rewrite PositiveMap.gss; reflexivity.
      * right; exists d'; split; assumption.
Qed.

Lemma extend_mem u dml row k : mem k (extend u dml row) = true <->
  mem k row = true \/ exists u' d, u = Some u' /\ In (k, d) dml /\ leb_lab u' d = true.
Proof.
  destruct u as [u|]; cbn [extend].
  - rewrite fold_add_mem; split; (intros [H|H]; [left; exact H|right]).
    + destruct H as [d H]; exists u, d; split; [reflexivity|exact H].
    + destruct H as [u' [d [E H]]]; injection E as <-; exists d; exact H.
  - split; [intros H; left; exact H|intros [H|[u' [d [E _]]]]; [exact H|discriminate]].
Qed.

(** A row's members, as atoms. *)
Lemma elements_row (row : PositiveMap.t unit) kt : akeyed row -> In kt (PositiveMap.elements row) -> inset row (nkey (fst kt)) = true.
Proof.
  intros K H; pose proof (elements_key row kt K H) as Ek; destruct kt as [k []].
  apply PositiveMap.elements_complete in H; unfold inset, mem; cbn [fst] in *; rewrite Ek, H; reflexivity.
Qed.

(** The keys of the graph and the rows are keys of atoms. *)
Lemma visit_keyed adj n : forall v s, akeyed s -> akeyed (visit adj n v s).
Proof.
  induction n as [|n IH]; intros v s Hs; cbn [visit]; [exact Hs|].
  destruct (PositiveMap.find (akey v) s); [exact Hs|].
  assert (H0 := akeyed_add s v tt Hs); revert H0.
  generalize (PositiveMap.add (akey v) tt s) as s0; generalize (succs adj v) as ws.
  induction ws as [|w ws IHw]; intros s0 H0; [exact H0|]; cbn [fold_left]; apply IHw, IH, H0.
Qed.

Lemma fold_visit_keyed adj n ws : forall s, akeyed s -> akeyed (fold_left (fun s w => visit adj n w s) ws s).
Proof. induction ws as [|w ws IH]; intros s H; [exact H|]; cbn [fold_left]; apply IH, visit_keyed, H. Qed.

Lemma edges_keyed l : akeyed (edges l).
Proof.
  unfold edges; generalize (@akeyed_empty (list N)); generalize (PositiveMap.empty (list N)) as a0.
  induction l as [|[x y] l IH]; intros a0 H0; [exact H0|]; cbn [fold_left]; apply IH.
  destruct x as [| |i], y as [| |j]; try exact H0; cbn [touch].
  - destruct (PositiveMap.find (akey i) a0); [exact H0|apply akeyed_add, H0].
  - unfold addedge; apply akeyed_add, H0.
Qed.

Lemma rows_keyed adj n : akeyed adj -> akeyed (rows_of adj n) /\ forall k row, PositiveMap.find k (rows_of adj n) = Some row -> akeyed row.
Proof.
  intros H; unfold rows_of; split.
  - intros k x; rewrite PositiveMap.gmapi; destruct (PositiveMap.find k adj) as [st|] eqn:E; [intros _; exact (H k st E)|discriminate].
  - intros k row; rewrite PositiveMap.gmapi; destruct (PositiveMap.find k adj) as [st|]; [|discriminate].
    intros Er; injection Er as <-; apply fold_visit_keyed, akeyed_empty.
Qed.

Lemma row_elements (row : PositiveMap.t unit) x : inset row x = true -> In (akey x, tt) (PositiveMap.elements row).
Proof.
  unfold inset, mem; destruct (PositiveMap.find (akey x) row) as [[]|] eqn:E; [intros _|discriminate].
  apply PositiveMap.elements_correct, E.
Qed.

Lemma succs_add adj i j k : succs (addedge i j adj) k = if N.eqb k i then j :: succs adj i else succs adj k.
Proof.
  unfold addedge, succs at 1; destruct (N.eqb_spec k i) as [->|Ne].
  - rewrite PositiveMap.gss; reflexivity.
  - rewrite PositiveMap.gso; [reflexivity|intros E; apply Ne, akey_inj, E].
Qed.

Lemma succs_touch x adj k : succs (touch x adj) k = succs adj k.
Proof.
  destruct x as [| |i]; try reflexivity; cbn [touch].
  destruct (PositiveMap.find (akey i) adj) eqn:E; [reflexivity|].
  unfold succs; destruct (N.eqb_spec k i) as [->|Ne]; [rewrite PositiveMap.gss, E; reflexivity|].
  rewrite PositiveMap.gso; [reflexivity|intros H; apply Ne, akey_inj, H].
Qed.

Lemma inset_add v s x : inset (PositiveMap.add (akey v) tt s) x = if N.eqb x v then true else inset s x.
Proof.
  unfold inset, mem; destruct (N.eqb_spec x v) as [->|Ne]; [rewrite PositiveMap.gss; reflexivity|].
  rewrite PositiveMap.gso; [reflexivity|intros E; apply Ne, akey_inj, E].
Qed.

(** What a search marks satisfies any property of its starting atoms
    that edges preserve. *)
Section Inv.
Variable adj : PositiveMap.t (list N).
Variable P : N -> Prop.
Hypothesis HP : forall u w, P u -> In w (succs adj u) -> P w.

Definition seen_ok (s : PositiveMap.t unit) : Prop := forall v, inset s v = true -> P v.

Lemma visit_inv n : forall v s, P v -> seen_ok s -> seen_ok (visit adj n v s).
Proof.
  induction n as [|n IH]; intros v s Hv Hs; cbn [visit]; [exact Hs|].
  destruct (PositiveMap.find (akey v) s); [exact Hs|].
  assert (Hws : forall w, In w (succs adj v) -> P w) by (intros w Hw; exact (HP v w Hv Hw)).
  assert (H0 : seen_ok (PositiveMap.add (akey v) tt s)).
  { intros x; rewrite inset_add; destruct (N.eqb_spec x v) as [->|_]; [intros _; exact Hv|apply Hs]. }
  revert H0 Hws; generalize (PositiveMap.add (akey v) tt s) as s0; generalize (succs adj v) as ws.
  induction ws as [|w ws IHw]; intros s0 H0 Hws; [exact H0|]; cbn [fold_left].
  apply IHw; [apply IH; [apply Hws; left; reflexivity|exact H0]|intros x Hx; apply Hws; right; exact Hx].
Qed.

Lemma reach_inv n st : Forall P st -> seen_ok (fold_left (fun s w => visit adj n w s) st (PositiveMap.empty _)).
Proof.
  intros Hst; assert (H0 : seen_ok (PositiveMap.empty unit)) by (intros v; unfold inset, mem; rewrite PositiveMap.gempty; discriminate).
  revert H0; generalize (PositiveMap.empty unit) as s0.
  induction Hst as [|w ws Hw Hws IHw]; intros s0 H0; [exact H0|]; cbn [fold_left]; apply IHw, visit_inv; assumption.
Qed.
End Inv.

(** The rows of [order_of], and its fields. *)
Lemma rows_of_find adj n a : PositiveMap.find (akey a) (rows_of adj n) =
  match PositiveMap.find (akey a) adj with
  | Some _ => Some (fold_left (fun s w => visit adj n w s) (succs adj a) (PositiveMap.empty _))
  | None => None
  end.
Proof. unfold rows_of; rewrite PositiveMap.gmapi; unfold succs; destruct (PositiveMap.find (akey a) adj); reflexivity. Qed.

Lemma tab_of_find d0 dml rows k : PositiveMap.find k (tab_of d0 dml rows) =
  match PositiveMap.find k rows with Some row => Some (extend (upval d0 k row) dml row, upval d0 k row) | None => None end.
Proof. unfold tab_of; rewrite PositiveMap.gmapi; destruct (PositiveMap.find k rows); reflexivity. Qed.

Section Labels.

Variable lenv : list label.

Definition lden (a : lexp) : option label :=
  match a with
  | LNone => None
  | LCon s => Some s
  | LAtom n => Some (nth (N.to_nat n) lenv EmptyString)
  end.

Definition lfacts_ok (l : list (lexp * lexp)) : Prop :=
  Forall (fun '(x, y) => olabel_lt (lden x) (lden y)) l.

Definition facts_ok (F : order) : Prop :=
  lfacts_ok (ofacts F)
  /\ (forall i j, otab F (akey i) (akey j) = true -> olabel_lt (lden (LAtom i)) (lden (LAtom j)))
  /\ (forall i u, oup F (akey i) = Some u -> olabel_lt (lden (LAtom i)) (Some u))
  /\ (forall j d, odown F (akey j) = Some d -> olabel_lt (Some d) (lden (LAtom j))).

Lemma lt_base_sound a b : lt_base a b = true -> olabel_lt (lden a) (lden b).
Proof. destruct a, b; cbn; try discriminate; unfold olabel_lt; cbn; auto. Qed.

(** [a] is at or below [b]. *)
Definition ole (a b : option label) : Prop := a = b \/ olabel_lt a b.

Lemma ole_lt_trans a b c : ole a b -> olabel_lt b c -> olabel_lt a c.
Proof. intros [->|H] H2; [exact H2|exact (olabel_lt_trans _ _ _ H H2)]. Qed.

Lemma lt_ole_trans a b c : olabel_lt a b -> ole b c -> olabel_lt a c.
Proof. intros H [<-|H2]; [exact H|exact (olabel_lt_trans _ _ _ H H2)]. Qed.

Lemma leb_lab_ole s t : leb_lab s t = true -> ole (Some s) (Some t).
Proof.
  rewrite leb_lab_eq; destruct (String.eqb_spec s t) as [->|_]; [left; reflexivity|intros H; right; exact H].
Qed.

(** The edges are sound: every edge goes up. *)
Definition ord (u v : N) : Prop := olabel_lt (lden (LAtom u)) (lden (LAtom v)).

Definition adj_ok (adj : PositiveMap.t (list N)) : Prop := forall i j, In j (succs adj i) -> ord i j.

Lemma addedge_ok adj i j : adj_ok adj -> ord i j -> adj_ok (addedge i j adj).
Proof.
  intros H Hij k m; rewrite succs_add; destruct (N.eqb_spec k i) as [->|_]; [|apply H].
  intros [<-|Hm]; [exact Hij|apply H, Hm].
Qed.

Lemma touch_ok x adj : adj_ok adj -> adj_ok (touch x adj).
Proof. intros H i j; rewrite succs_touch; apply H. Qed.

Lemma edges_ok l : lfacts_ok l -> adj_ok (edges l).
Proof.
  unfold edges; intros Hl.
  assert (H0 : adj_ok (PositiveMap.empty _)) by (intros i j; unfold succs; rewrite PositiveMap.gempty; intros []).
  revert H0; generalize (PositiveMap.empty (list N)) as a0.
  unfold lfacts_ok in Hl; induction Hl as [|[x y] l Hxy Hl IH]; intros a0 H0; [exact H0|]; cbn [fold_left]; apply IH.
  destruct x as [| |i], y as [| |j]; try exact H0; [apply touch_ok, H0|apply addedge_ok; [exact H0|exact Hxy]].
Qed.

(** The facts give the direct bounds. *)
Lemma dups_ok l : lfacts_ok l -> forall i c, In (akey i, c) (dups l) -> olabel_lt (lden (LAtom i)) (Some c).
Proof.
  intros Hl i c H; unfold dups in H; apply in_flat_map in H as [[x y] [Hin H]].
  destruct x as [| |i'], y as [|c'|]; cbn in H; try contradiction.
  destruct H as [E|[]]; injection E as Ei <-; apply akey_inj in Ei; subst i'.
  unfold lfacts_ok in Hl; rewrite Forall_forall in Hl; exact (Hl _ Hin).
Qed.

Lemma ddowns_ok l : lfacts_ok l -> forall i c, In (akey i, c) (ddowns l) -> olabel_lt (Some c) (lden (LAtom i)).
Proof.
  intros Hl i c H; unfold ddowns in H; apply in_flat_map in H as [[x y] [Hin H]].
  destruct x as [|c'|], y as [| |i']; cbn in H; try contradiction.
  destruct H as [E|[]]; injection E as Ei <-; apply akey_inj in Ei; subst i'.
  unfold lfacts_ok in Hl; rewrite Forall_forall in Hl; exact (Hl _ Hin).
Qed.

Section OrderOf.
Variable l : list (lexp * lexp).
Hypothesis Hl : lfacts_ok l.

Let adj := edges l.
Let rows := rows_of adj (List.length (nodes adj)).
Let d0 := bmap true (dups l).
Let dm := bmap false (downs (bmap false (ddowns l)) rows).

Lemma rows_ok a row : PositiveMap.find (akey a) rows = Some row -> forall x, inset row x = true -> ord a x.
Proof.
  unfold rows; rewrite rows_of_find; destruct (PositiveMap.find (akey a) adj); [|discriminate].
  intros E; injection E as <-; apply (reach_inv _ (ord a)).
  - intros u w Hu Hw; exact (olabel_lt_trans _ _ _ Hu (edges_ok l Hl u w Hw)).
  - rewrite Forall_forall; intros w Hw; exact (edges_ok l Hl a w Hw).
Qed.

Lemma up_ok a row u : PositiveMap.find (akey a) rows = Some row -> upval d0 (akey a) row = Some u ->
  olabel_lt (lden (LAtom a)) (Some u).
Proof.
  intros Er H; destruct (pick_fold_sound true _ _ _ H) as [E|E].
  - exact (dups_ok l Hl a u (bmap_sound _ _ _ _ E)).
  - apply in_map_iff in E as [kt [E Hkt]].
    pose proof (proj2 (rows_keyed _ _ (edges_keyed l)) _ row Er) as K.
    pose proof (bmap_sound _ _ _ _ E) as Hd; rewrite <- (elements_key row kt K Hkt) in Hd.
    exact (olabel_lt_trans _ _ _ (rows_ok a row Er _ (elements_row row kt K Hkt)) (dups_ok l Hl _ u Hd)).
Qed.

Lemma down_ok b d : PositiveMap.find (akey b) dm = Some d -> olabel_lt (Some d) (lden (LAtom b)).
Proof.
  intros H; apply bmap_sound in H; unfold downs in H; apply in_app_or in H as [H|H].
  - apply PositiveMap.elements_complete, bmap_sound in H; exact (ddowns_ok l Hl _ d H).
  - apply in_flat_map in H as [[k row] [Hin H]].
    apply PositiveMap.elements_complete in Hin.
    pose proof (proj2 (rows_keyed _ _ (edges_keyed l)) _ row Hin) as K.
    pose proof (proj1 (rows_keyed _ _ (edges_keyed l)) _ row Hin) as Ek; rewrite <- Ek in Hin, H.
    destruct (PositiveMap.find (akey (nkey k)) (bmap false (ddowns l))) as [c|] eqn:Ec; [|destruct H].
    pose proof (ddowns_ok l Hl _ c (bmap_sound _ _ _ _ Ec)) as Hc.
    apply in_map_iff in H as [kt [E Hkt]]; injection E as Ek0 <-.
    pose proof (elements_row row kt K Hkt) as Hr; rewrite Ek0, nkey_akey in Hr.
    exact (olabel_lt_trans _ _ _ Hc (rows_ok _ row Hin b Hr)).
Qed.

End OrderOf.

Lemma order_of_ok l : lfacts_ok l -> facts_ok (order_of l).
Proof.
  intros Hl; unfold order_of, facts_ok; cbn [ofacts otab oup odown]; unfold tmem, tup, dfind.
  split; [exact Hl|split; [|split]].
  - intros i j; rewrite PositiveMap.gmapi, tab_of_find; destruct (PositiveMap.find (akey i) _) as [row|] eqn:Er; [|discriminate].
    intros H; apply extend_mem in H as [H|[u [d [Eu [Hd Hl']]]]]; [exact (rows_ok l Hl i row Er j H)|].
    apply PositiveMap.elements_complete in Hd.
    exact (olabel_lt_trans _ _ _ (up_ok l Hl i row u Er Eu) (ole_lt_trans _ _ _ (leb_lab_ole _ _ Hl') (down_ok l Hl j d Hd))).
  - intros i u; rewrite PositiveMap.gmapi, tab_of_find; destruct (PositiveMap.find (akey i) _) as [row|] eqn:Er; [|discriminate].
    exact (up_ok l Hl i row u Er).
  - exact (down_ok l Hl).
Qed.

Variable F : order.
Hypothesis HF : facts_ok F.

Lemma lt_known_sound a b : lt_known F a b = true -> olabel_lt (lden a) (lden b).
Proof.
  destruct HF as [_ [Ht [Hu Hd]]].
  destruct a as [|s|i], b as [|t|j]; unfold lt_known; try apply lt_base_sound;
    [rewrite lab_lt_eq; exact (lt_base_sound (LCon s) (LCon t))| | |apply Ht].
  - destruct (odown F (akey j)) as [d|] eqn:E; [|discriminate]; intros H.
    exact (ole_lt_trans _ _ _ (leb_lab_ole _ _ H) (Hd j d E)).
  - destruct (oup F (akey i)) as [u|] eqn:E; [|discriminate]; intros H.
    exact (lt_ole_trans _ _ _ (Hu i u E) (leb_lab_ole _ _ H)).
Qed.

(** What a comparison tells about the labels. *)
Definition cmp_holds (c : comparison) (a b : lexp) : Prop :=
  match c with
  | Eq => a = b
  | Lt => olabel_lt (lden a) (lden b)
  | Gt => olabel_lt (lden b) (lden a)
  end.

Lemma lcmp_sound a b c : lcmp F a b = Some c -> cmp_holds c a b.
Proof.
  rewrite lcmp_eq; unfold lcmp_spec; destruct (lexp_eqb a b) eqn:E.
  - intros H; injection H as <-; apply lexp_eqb_eq, E.
  - destruct (lt_known F a b) eqn:L1; [intros H; injection H as <-; apply lt_known_sound, L1|].
    destruct (lt_known F b a) eqn:L2; [intros H; injection H as <-; apply lt_known_sound, L2|discriminate].
Qed.

Lemma lcmp_neq a b c : lcmp F a b = Some c -> c <> Eq -> lden a <> lden b.
Proof.
  intros H Hc; apply lcmp_sound in H; destruct c; cbn in H; [contradiction| |];
    intros E; rewrite E in H; exact (olabel_lt_irrefl _ H).
Qed.

End Labels.

(** [iter n f x] applies [f] [n] times. *)
Fixpoint iter {A} (n : nat) (f : A -> A) (x : A) : A :=
  match n with 0 => x | S n => f (iter n f x) end.

Lemma iter_add {A} n m (f : A -> A) x : iter (n + m) f x = iter n f (iter m f x).
Proof. induction n; cbn; congruence. Qed.

(** ** Segments, for the display

    What [Names] shows a normal form through: a target ([NBind u w] is a
    term with its payload); the targets of one label; a segment, one entry
    per label with its input targets and its number of outputs, which the
    display writes as one context form; a word. *)
Inductive ntgt : Type :=
| NVar (h : lexp) (i : nat)
| NBind (u : nat) (w : word)
with tlist : Type :=
| TNil
| TCons (t : ntgt) (r : tlist)
with seg : Type :=
| SNil
| SEnt (h : lexp) (ts : tlist) (m : nat) (r : seg)
with word : Type :=
| WEnd (s : seg)
| WAtom (s : seg) (L : list (lexp * nat)) (a : nat) (w : word)
| WLay (s : seg) (w : word).

Scheme ntgt_mind := Induction for ntgt Sort Prop
with tlist_mind := Induction for tlist Sort Prop
with seg_mind := Induction for seg Sort Prop
with word_mind := Induction for word Sort Prop.
Combined Scheme nf_mind from ntgt_mind, tlist_mind, seg_mind, word_mind.

(** ** Expressions *)

Inductive aexp : Type :=
| AId
| AAtom (n : nat)
| ACompose (a b : aexp)
| AOuter (h : lexp) (a : aexp)
| AInner (h : lexp) (t : texp) (a : aexp)
| ALift (h : lexp) (a : aexp)
with texp : Type :=
| TVarE (h : lexp) (i : nat)
| TBindE (u : nat) (p : aexp)
| TShiftE (h : lexp) (t : texp)
| TLookE (h : lexp) (i : nat) (a : aexp).

(** ** Denotation of expressions *)

Section Sound.

Context {T : Type}.
Variable lenv : list label.
Variable tenv : list T.
Variable aenv : list (radj T).

Local Notation lden := (lden lenv).

Definition aden (n : nat) : radj T := nth n aenv ridentity.

Fixpoint aeden (e : aexp) : radj T :=
  match e with
  | AId => ridentity
  | AAtom n => aden n
  | ACompose a b => rcompose (aeden a) (aeden b)
  | AOuter h a => rpush_outer (lden h) (aeden a)
  | AInner h t a => rpush_inner (lden h) (teden t) (aeden a)
  | ALift h a => rlift (lden h) (aeden a)
  end
with teden (t : texp) : rtarget T :=
  match t with
  | TVarE h i => RRename (mk_rvar (lden h) i)
  | TBindE u p => match nth_error tenv u with Some x => RBind x (aeden p) | None => RRename (mk_rvar None 0) end
  | TShiftE h t => rshift_target (lden h) (teden t)
  | TLookE h i a => rapply_target (aeden a) (RRename (mk_rvar (lden h) i))
  end.

Scheme aexp_mind := Induction for aexp Sort Prop
with texp_mind := Induction for texp Sort Prop.
Combined Scheme exp_mind from aexp_mind, texp_mind.

(** ** Shared definitions

    An atom may stand for a definition ([defs], aligned with the atoms):
    [Exp e e'] is [e] with each such atom replaced by (the expansion of)
    its definition.  [HNorm.normD] normalises [e] as if it were [e'],
    each definition once per word it is followed by. *)
Section Expand.

Variable defs : list (option aexp).

Inductive Exp : aexp -> aexp -> Prop :=
| ExId : Exp AId AId
| ExAtom n : nth n defs None = None -> Exp (AAtom n) (AAtom n)
| ExRef n d e' : nth n defs None = Some d -> Exp d e' -> Exp (AAtom n) e'
| ExCompose a b a' b' : Exp a a' -> Exp b b' -> Exp (ACompose a b) (ACompose a' b')
| ExOuter h a a' : Exp a a' -> Exp (AOuter h a) (AOuter h a')
| ExInner h t a t' a' : TExp t t' -> Exp a a' -> Exp (AInner h t a) (AInner h t' a')
| ExLift h a a' : Exp a a' -> Exp (ALift h a) (ALift h a')
with TExp : texp -> texp -> Prop :=
| ExVar h i : TExp (TVarE h i) (TVarE h i)
| ExBind u p p' : Exp p p' -> TExp (TBindE u p) (TBindE u p')
| ExShift h t t' : TExp t t' -> TExp (TShiftE h t) (TShiftE h t')
| ExLook h i a a' : Exp a a' -> TExp (TLookE h i a) (TLookE h i a').

Scheme Exp_mind := Induction for Exp Sort Prop
with TExp_mind := Induction for TExp Sort Prop.
Combined Scheme ex_mind from Exp_mind, TExp_mind.

(** The expansion is unique. *)
Lemma Exp_func :
  (forall e x, Exp e x -> forall y, Exp e y -> x = y)
  /\ (forall t x, TExp t x -> forall y, TExp t y -> x = y).
Proof.
  apply ex_mind; intros;
    lazymatch goal with |- _ = ?y => match goal with Hy : _ _ y |- _ => inversion Hy; subst end end;
    try congruence; try (f_equal; auto; fail).
  match goal with H1 : nth _ _ _ = Some _, H2 : nth _ _ _ = Some _ |- _ => rewrite H1 in H2; injection H2 as <- end; auto.
Qed.

End Expand.

(** An atom standing for a definition means the definition. *)
Lemma Exp_meaning defs :
  (forall k d, nth k defs None = Some d -> aden k = aeden d) ->
  (forall e e', Exp defs e e' -> aeden e = aeden e')
  /\ (forall t t', TExp defs t t' -> teden t = teden t').
Proof.
  intros Hd; apply ex_mind; intros; cbn [aeden teden]; rewrite ?H, ?H0; try reflexivity.
  rewrite <- H; apply Hd, e.
Qed.

(** Materialising: the term [u] with the payload [ρ], and the term [u']
    (which is [u] with [ρ] applied) with the identity payload. *)
Definition mbase (u u' : T) (ρ : radj T) (r r' : rresult T) : Prop := r = inr (u, ρ) /\ r' = inr (u', ridentity).

(** Results related by [B], also inside payloads, in steps: the same,
    related by [B], the same term with payloads [W ∘ ρ] and [W' ∘ ρ] for
    [W] and [W'] whose results are related (an entry changed after an
    atom changes the payloads of the atom's terms in this way), or
    related through a third. *)
Inductive drel (B : rresult T -> rresult T -> Prop) : rresult T -> rresult T -> Prop :=
| DEq r : drel B r r
| DBase r r' : B r r' -> drel B r r'
| DPay u (W W' : radj T) ρ : (forall v, drel B (rapply W v) (rapply W' v)) ->
    drel B (inr (u, rcompose W ρ)) (inr (u, rcompose W' ρ))
| DTrans r r' r'' : drel B r r' -> drel B r' r'' -> drel B r r''.

Lemma drel_mono (B B' : rresult T -> rresult T -> Prop) : (forall r r', B r r' -> B' r r') ->
  forall r r', drel B r r' -> drel B' r r'.
Proof. intros H; induction 1; [apply DEq|apply DBase, H; assumption|apply DPay; assumption|eapply DTrans; eassumption]. Qed.

End Sound.
