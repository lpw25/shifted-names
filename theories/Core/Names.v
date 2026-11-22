(** * The [names] tactic

    [names] rewrites every adjustment [adj T N M] built from context forms
    (full [⟦ I \ O ⟧], [⟦ I | Γ \ O | Γ[σ] ⟧] and short [⟦ I; σ ⟧], and so
    [lift] and [lift_free]), [∘], [⟦⟧] and [at_scope] to its normal form,
    shown as context forms, with any other adjustment as an atom; it then
    evaluates the variables those normal forms send to variables or terms.
    Equal adjustments get the same normal form, so an equation is proved
    by [names; reflexivity].  Labels may be concrete strings or
    variables; the order between label variables comes from hypotheses
    [label_lt x y] in the context ([label_compare] provides them by case
    analysis).

    An adjustment is taken to the raw layer and reified into [aexp].  Its
    normal form is computed by the layered normaliser (Layered.v,
    Canon.v) and rendered; the rewrite [a = b] to the rendered form is
    then checked by normalising both sides with [HNorm] ([names_same],
    sound by [HConcrete.hn_eq_t_sound]).  To be replaced: [HNorm]
    computing the normal form, with the rendering proved sound, so that
    no check is needed. *)

From Stdlib Require Import NArith List String Arith Bool StrictProp.
Open Scope bool_scope.
From ShiftedNames.Core Require Import Label Var Adjustment Indexed Syntax Normalise Layered Canon Keys Retarget Canonical LEval HConcrete.
From ShiftedNames.Core Require HNorm.
From Stdlib Require Import PArith FMapPositive.
Import ListNotations.

(** ** Reification *)

(** The position of [x] in the list [l], up to conversion, adding it at
    the end if absent; returns the index and the new list.  Syntactic
    equality is tried first, being much cheaper. *)
Ltac lookup_add x l :=
  let rec go_syn l n :=
    lazymatch l with
    | nil => constr:((n, false))
    | ?y :: ?r => match y with x => constr:((n, true)) | _ => go_syn r (S n) end
    end in
  let rec go l n :=
    lazymatch l with
    | nil => constr:((n, false))
    | ?y :: ?r =>
        match constr:(tt) with
        | _ => let _ := constr:(@eq_refl _ x : x = y) in constr:((n, true))
        | _ => go r (S n)
        end
    end in
  lazymatch go_syn l O with
  | (?n, true) => constr:((n, l))
  | _ =>
      lazymatch go l O with
      | (?n, true) => constr:((n, l))
      | (?n, false) => let l' := eval cbv [app] in (l ++ [x]) in constr:((n, l'))
      end
  end.

(** Checks returning [tt], so that they can be used inside reification
    functions, which return values. *)
Ltac is_nat_lit n :=
  lazymatch n with
  | O => constr:(tt)
  | S ?m => is_nat_lit m
  end.

Ltac is_string_lit s :=
  lazymatch s with
  | EmptyString => constr:(tt)
  | String _ ?r => is_string_lit r
  end.

(** Environments: [(lenv, tenv, aenv, penv)]. *)

Ltac reify_label h env :=
  lazymatch env with
  | (?le, ?te, ?ae, ?pe) =>
      lazymatch h with
      | None => constr:((LNone, env))
      | Some ?s =>
          match constr:(tt) with
          | _ => let _ := is_string_lit s in constr:((LCon s, env))
          | _ => lazymatch lookup_add s le with
                 | (?n, ?le') => let n' := eval vm_compute in (N.of_nat n) in constr:((LAtom n', (le', te, ae, pe)))
                 end
          end
      end
  end.

Ltac reify_atom a env :=
  lazymatch env with
  | (?le, ?te, ?ae, ?pe) =>
      lazymatch lookup_add a ae with
      | (?n, ?ae') => constr:((AAtom n, (le, te, ae', pe)))
      end
  end.

Ltac reify_adj a env :=
  match a with
  | ridentity => constr:((AId, env))
  | rcompose ?x ?y =>
      lazymatch reify_adj x env with
      | (?ex, ?env1) => lazymatch reify_adj y env1 with
                        | (?ey, ?env2) => constr:((ACompose ex ey, env2))
                        end
      end
  | rpush_outer ?h ?x =>
      lazymatch reify_label h env with
      | (?eh, ?env1) => lazymatch reify_adj x env1 with
                        | (?ex, ?env2) => constr:((AOuter eh ex, env2))
                        end
      end
  | rpush_inner ?h ?t ?x =>
      lazymatch reify_label h env with
      | (?eh, ?env1) =>
          lazymatch reify_target t env1 with
          | (?et, ?env2) => lazymatch reify_adj x env2 with
                            | (?ex, ?env3) => constr:((AInner eh et ex, env3))
                            end
          end
      end
  | rlift ?h ?x =>
      lazymatch reify_label h env with
      | (?eh, ?env1) => lazymatch reify_adj x env1 with
                        | (?ex, ?env2) => constr:((ALift eh ex, env2))
                        end
      end
  | _ => reify_atom a env
  end
with reify_var w env :=
  lazymatch w with
  | mk_rvar ?h ?i =>
      let _ := is_nat_lit i in
      lazymatch reify_label h env with
      | (?eh, ?env1) => constr:((TVarE eh i, env1))
      end
  | shift_rvar (mk_rvar ?h 0) ?w' =>
      lazymatch reify_label h env with
      | (?eh, ?env1) => lazymatch reify_var w' env1 with
                        | (?ew, ?env2) => constr:((TShiftE eh ew, env2))
                        end
      end
  end
with reify_target t env :=
  lazymatch t with
  | RRename ?w => reify_var w env
  | RBind ?u ?p =>
      lazymatch env with
      | (?le, ?te, ?ae, ?pe) =>
          lazymatch lookup_add u te with
          | (?n, ?te') => lazymatch reify_padj p (le, te', ae, pe) with
                          | (?ep, ?env1) => constr:((TBindE n ep, env1))
                          end
          end
      end
  end
with reify_padj p env :=
  match p with
  | rpidentity => constr:((PId, env))
  | rpcompose ?x ?q =>
      lazymatch reify_adj x env with
      | (?ex, ?env1) => lazymatch reify_padj q env1 with
                        | (?eq, ?env2) => constr:((PComp ex eq, env2))
                        end
      end
  | rpshift ?h ?q =>
      lazymatch reify_label h env with
      | (?eh, ?env1) => lazymatch reify_padj q env1 with
                        | (?eq, ?env2) => constr:((PShift eh eq, env2))
                        end
      end
  | _ =>
      lazymatch env with
      | (?le, ?te, ?ae, ?pe) =>
          lazymatch lookup_add p pe with
          | (?n, ?pe') => constr:((PAtom n, (le, te, ae, pe')))
          end
      end
  end.

(** An input entry whose target cannot be reified (a variable whose index
    is not a numeral, say) makes the whole entry an atom. *)
Ltac reify_adj_top a env :=
  match constr:(tt) with
  | _ => reify_adj a env
  | _ => reify_atom a env
  end.

(** The label order facts in the context, as pairs of label expressions
    (label variables or concrete labels). *)
Ltac label_hyps :=
  constr:(ltac:(let rec go acc :=
                  lazymatch goal with
                  | H : label_lt ?x ?y |- _ => clear H; go (@cons (label * label) (x, y) acc)
                  | _ => exact acc
                  end in
                go (@nil (label * label)))).

Ltac reify_facts hs env F :=
  lazymatch hs with
  | nil => constr:((env, F))
  | (?x, ?y) :: ?r =>
      lazymatch reify_label (Some x) env with
      | (?ex, ?env1) =>
          lazymatch reify_label (Some y) env1 with
          | (?ey, ?env2) =>
              let f := constr:((ex, ey)) in
              lazymatch F with
              | context [f] => reify_facts r env2 F
              | _ => reify_facts r env2 (f :: F)
              end
          end
      end
  end.

(** The hypotheses are taken in one pass; when one cannot be cleared
    in the copy of the context this is done in, one at a time. *)
Ltac collect_fact_list_slow env F :=
  match goal with
  | H : label_lt ?x ?y |- _ =>
      lazymatch reify_label (Some x) env with
      | (?ex, ?env1) =>
          lazymatch reify_label (Some y) env1 with
          | (?ey, ?env2) =>
              let f := constr:((ex, ey)) in
              lazymatch F with
              | context [f] => fail
              | _ => collect_fact_list_slow env2 (f :: F)
              end
          end
      end
  | _ => constr:((env, F))
  end.

Ltac collect_fact_list env F :=
  match constr:(tt) with
  | _ => let hs := label_hyps in reify_facts hs env F
  | _ => collect_fact_list_slow env F
  end.

(** ... as the order the normaliser works with. *)
Ltac collect_facts env F :=
  lazymatch collect_fact_list env F with
  | (?env', ?l) => constr:((env', order_of l))
  end.

(** ** Syntaxes

    What [names] needs to know about a syntax to materialise payloads:
    its substitution, how a payload adjustment acts on a closed term
    ([sm_g]), and that substitutions whose results on each variable are
    related by [mrel sm_g] are equal.  A syntax's [Subst] functor provides
    an instance. *)
Class SubstMat (T : Type) := {
  sm_term : nat -> Type;
  sm_subst : forall {N M}, adj T N M -> sm_term N -> sm_term M;
  sm_of : T -> sm_term 0;
  sm_back : sm_term 0 -> T;
  sm_g : rpadj T -> T -> T;
  sm_g_spec : forall (b : adj T 0 0) u, sm_g (rpcompose (adj_raw b) rpidentity) u = sm_back (sm_subst b (sm_of u));
  sm_mat : forall N (a a' : adj T N 0),
    (forall v : var N, mrel sm_g (rapply (adj_raw a) (var_raw v)) (rapply (adj_raw a') (var_raw v))) ->
    forall t, sm_subst a t = sm_subst a' t
}.

(** ** Displaying normal forms

    A normal form is shown as context forms composed with [∘]: each
    segment as a full form [⟦ I \ O ⟧], each lifted atom as a short form
    [⟦ x; ·; … | σ ⟧].  Context forms only refer to their own slots, so a
    segment is first expanded until every variable target is a slot: a
    label with targets beyond its outputs gets more outputs, and the
    matching inputs (and the matching names of payload terms) are written
    out.  A payload whose adjustment is not a single segment cannot be
    shown, and the adjustment is then left as it is. *)

Inductive dtgt : Type :=
| DSlot (h : lexp) (j : nat)
| DTerm (u : nat) (p : list (lexp * dtgt)).

Inductive dout : Type :=
| DONamed (h : lexp) (j : nat)
| DOPos (h : lexp) (j : nat).

Inductive din : Type :=
| DISlot (x : lexp) (h : lexp) (j : nat)
| DIPos (x : lexp)
| DITerm (x : lexp) (u : nat) (p : list (lexp * dtgt)).

(** A context form, its contexts listed outermost first (the order the
    renderer builds them in), with a tail atom or not; or a lifted atom. *)
Inductive sent : Type :=
| SELift (h : lexp)
| SESub (h : lexp) (u : nat).

Inductive dpiece : Type :=
| DFull (outs : list dout) (ins : list din) (tail : option (list nat))
| DShort (es : list sent) (tail : option (list nat))
| DLift (hs : list lexp) (tail : list nat).

(** A full form whose outputs are all positional, each with the label of
    its input, and whose terms name no slots, is a short form. *)
Fixpoint shorten (os : list dout) (is : list din) : option (list sent) :=
  match is with
  | [] => match os with [] => Some [] | _ => None end
  | DIPos x :: is =>
      match os with
      | DOPos h _ :: os => if lexp_eqb x h then option_map (cons (SELift x)) (shorten os is) else None
      | _ => None
      end
  | DITerm x u [] :: is => option_map (cons (SESub x u)) (shorten os is)
  | _ => None
  end.

Fixpoint only_lifts (es : list sent) : option (list lexp) :=
  match es with
  | [] => Some []
  | SELift h :: es => option_map (cons h) (only_lifts es)
  | _ => None
  end.

(** A form whose entries only pass variables around its tail is shown
    as that, and one with no entries as its tail. *)
Definition short_or_full (d : dpiece) : dpiece :=
  match d with
  | DFull os is t =>
      match shorten os is with
      | Some es =>
          match t, only_lifts es with
          | Some ns, Some hs => DLift hs ns
          | _, _ => DShort es t
          end
      | None => d
      end
  | _ => d
  end.

Fixpoint lget (h : lexp) (m : list (lexp * nat)) : nat :=
  match m with [] => 0 | (h', n) :: m => if lexp_eqb h h' then n else lget h m end.

Fixpoint bump (h : lexp) (k : nat) (m : list (lexp * nat)) : list (lexp * nat) :=
  match m with
  | [] => [(h, k)]
  | (h', n) :: m' => if lexp_eqb h h' then (h', Nat.max n k) :: m' else (h', n) :: bump h k m'
  end.

(** The slots each label needs. *)
Fixpoint need_t (t : ntgt) (acc : list (lexp * nat)) : option (list (lexp * nat)) :=
  match t with
  | NVar h j => Some (bump h (S j) acc)
  | NBind _ (WEnd P) None => need_s P acc
  | NBind _ _ _ => None
  end
with need_ts (ts : tlist) (acc : list (lexp * nat)) : option (list (lexp * nat)) :=
  match ts with
  | TNil => Some acc
  | TCons t r => match need_t t acc with Some acc' => need_ts r acc' | None => None end
  end
with need_s (s : seg) (acc : list (lexp * nat)) : option (list (lexp * nat)) :=
  match s with
  | SNil => Some acc
  | SEnt h ts m r => match need_ts ts (bump h m acc) with Some acc' => need_s r acc' | None => None end
  end.

Fixpoint cget (h : lexp) (c : list (lexp * (list dtgt * nat))) : list dtgt * nat :=
  match c with [] => ([], 0) | (h', e) :: c => if lexp_eqb h h' then e else cget h c end.

(** The entries of label [h], outermost first: the converted targets,
    then the ones the expansion writes out up to [n] slots. *)
Definition entries (h : lexp) (n : nat) (c : list (lexp * (list dtgt * nat))) : list (lexp * dtgt) :=
  let '(ds, m) := cget h c in rev (map (fun d => (h, d)) (ds ++ map (fun j => DSlot h j) (seq m (n - m)))).

Definition contexts (named : bool) (need : list (lexp * nat)) (c : list (lexp * (list dtgt * nat))) : list (lexp * dtgt) :=
  flat_map (fun '(h, n) => match h with LNone => if named then [] else entries h n c | _ => entries h n c end) need.

Fixpoint conv_t (need : list (lexp * nat)) (t : ntgt) : option dtgt :=
  match t with
  | NVar h j => Some (DSlot h j)
  | NBind u (WEnd P) None =>
      match conv_s need P with Some c => Some (DTerm u (contexts true need c)) | None => None end
  | NBind _ _ _ => None
  end
with conv_ts (need : list (lexp * nat)) (ts : tlist) : option (list dtgt) :=
  match ts with
  | TNil => Some []
  | TCons t r => match conv_t need t, conv_ts need r with Some d, Some ds => Some (d :: ds) | _, _ => None end
  end
with conv_s (need : list (lexp * nat)) (s : seg) : option (list (lexp * (list dtgt * nat))) :=
  match s with
  | SNil => Some []
  | SEnt h ts m r => match conv_ts need ts, conv_s need r with Some ds, Some c => Some ((h, (ds, m)) :: c) | _, _ => None end
  end.

(** How often a slot is used; a use in a payload counts twice, so that
    such a slot is always named. *)
Fixpoint dt_uses (h : lexp) (j : nat) (d : dtgt) : nat :=
  match d with
  | DSlot h' j' => if lexp_eqb h h' && Nat.eqb j j' then 1 else 0
  | DTerm _ p =>
      2 * (fix go (p : list (lexp * dtgt)) : nat :=
             match p with [] => 0 | (_, d) :: r => dt_uses h j d + go r end) p
  end.

Definition slot_uses (h : lexp) (j : nat) (is : list (lexp * dtgt)) : nat :=
  fold_right (fun '(_, d) n => dt_uses h j d + n) 0 is.

(** Inputs innermost first; an input is written positionally when its slot
    is used by it alone and comes after the previous positional slot of
    its label. *)
Fixpoint positional (all : list (lexp * dtgt)) (is : list (lexp * dtgt)) (last : list (lexp * nat))
  : list din * list (lexp * nat) :=
  match is with
  | [] => ([], [])
  | (x, DSlot h j) :: r =>
      if Nat.eqb (slot_uses h j all) 1 && Nat.leb (lget h last) j then
        let '(ds, ps) := positional all r (bump h (S j) last) in (DIPos x :: ds, (h, j) :: ps)
      else let '(ds, ps) := positional all r last in (DISlot x h j :: ds, ps)
  | (x, DTerm u p) :: r => let '(ds, ps) := positional all r last in (DITerm x u p :: ds, ps)
  end.

Fixpoint mem_slot (h : lexp) (j : nat) (ps : list (lexp * nat)) : bool :=
  match ps with [] => false | (h', j') :: ps => (lexp_eqb h h' && Nat.eqb j j') || mem_slot h j ps end.

(** Outputs innermost first: the positional slots in the order of their
    inputs, each preceded by the named slots of its label below it. *)
Fixpoint outputs (need : list (lexp * nat)) (ps : list (lexp * nat)) (done : list (lexp * nat)) : list dout :=
  match ps with
  | [] =>
      flat_map (fun '(h, n) =>
        map (fun j => DONamed h j) (filter (fun j => negb (mem_slot h j ps) && Nat.leb (lget h done) j) (seq 0 n))) need
  | (h, j) :: ps' =>
      map (fun j' => DONamed h j') (filter (fun j' => negb (mem_slot h j' ps)) (seq (lget h done) (j - lget h done)))
      ++ DOPos h j :: outputs need ps' (bump h (S j) done)
  end.

Definition display_seg (Sg : seg) (tail : option (list nat)) : option dpiece :=
  match need_s Sg [] with
  | None => None
  | Some need =>
      match conv_s need Sg with
      | Some c =>
          let is := rev (contexts false need c) in
          let '(ds, ps) := positional is is [] in
          Some (DFull (rev (outputs need ps [])) (rev ds) tail)
      | None => None
      end
  end.

Fixpoint din_count (h : lexp) (ds : list din) : nat :=
  match ds with
  | [] => 0
  | (DISlot x _ _ | DIPos x | DITerm x _ _) :: r => (if lexp_eqb h x then 1 else 0) + din_count h r
  end.

(** A segment followed by an atom lifted once for each of its inputs is
    one context form with that atom as its tail. *)
Definition merges (ds : list din) (L : list (lexp * nat)) : bool :=
  forallb (fun '(h, n) => Nat.eqb (din_count h ds) n) L
  && forallb (fun d => match d with DISlot x _ _ | DIPos x | DITerm x _ _ => Nat.eqb (din_count x ds) (lget x L) end) ds.

(** A normal form is shown as context forms in a sequence: each maximal run
    of atoms with the same lifts and nothing between them is the tail of
    one form; the segment after a run is split into the part acting on
    the variables passed around the run, which goes into that form's
    entries, and the part acting on the run's outputs, which stays a
    separate form.  The split is not made when the second part would put
    an output of the run underneath one of the form's own outputs. *)
Inductive gitem : Type :=
| GSeg (s : seg)
| GRun (L : list (lexp * nat)) (atoms : list nat).

Fixpoint lifts_eqb' (L L' : list (lexp * nat)) : bool :=
  match L, L' with
  | [], [] => true
  | (h, n) :: L, (h', n') :: L' => lexp_eqb h h' && Nat.eqb n n' && lifts_eqb' L L'
  | _, _ => false
  end.

(** The word as segments and runs, outermost first. *)
Fixpoint witems (w : word) : list gitem :=
  match w with
  | WEnd s => [GSeg s]
  | WAtom s L a w =>
      match witems w with
      | GRun L' as' :: rest =>
          match s with
          | SNil => if lifts_eqb' L L' then [GRun L (a :: as')] ++ rest else [GSeg s; GRun L [a]; GRun L' as'] ++ rest
          | _ => [GSeg s; GRun L [a]; GRun L' as'] ++ rest
          end
      | GSeg SNil :: GRun L' as' :: rest =>
          if lifts_eqb' L L' then GSeg s :: GRun L (a :: as') :: rest
          else GSeg s :: GRun L [a] :: GSeg SNil :: GRun L' as' :: rest
      | items => GSeg s :: GRun L [a] :: items
      end
  | WLay s w => GSeg s :: witems w
  end.

Section Split.

Variable F : order.
Variable ntm : nat.

Fixpoint tmax (t : ntgt) (acc : list (lexp * nat)) : list (lexp * nat) :=
  match t with NVar h j => bump h (S j) acc | NBind _ _ _ => acc end.

(** The targets of the first [k] inputs of [h]. *)
Fixpoint firsts (S : seg) (h : lexp) (k : nat) : option (list ntgt) :=
  match k with
  | 0 => Some []
  | S k' =>
      match firsts S h k', seg_tgt F S h k' with
      | Some ts, Some t => Some (ts ++ [t])
      | _, _ => None
      end
  end.

Fixpoint sbuild (es : list (lexp * (list ntgt * nat))) : option seg :=
  match es with
  | [] => Some SNil
  | (h, (ts, m)) :: es =>
      match sbuild es with Some s => sset F h (tl_of ts) m s | None => None end
  end.

Definition labels_of (L : list (lexp * nat)) (outs : list (lexp * nat)) (S : seg) : list lexp :=
  let fix go (s : seg) := match s with SNil => [] | SEnt h _ _ r => h :: go r end in
  map fst L ++ map fst outs ++ go S.

Fixpoint dedup (hs : list lexp) : list lexp :=
  match hs with [] => [] | h :: r => h :: filter (fun h' => negb (lexp_eqb h h')) (dedup r) end.

(** [S = B ∘ P]: [P] on the variables passed around ([L]), [B] on the
    rest, fixing [P]'s outputs and putting nothing underneath them. *)
Definition split_seg (L : list (lexp * nat)) (S : seg) : option (seg * seg) :=
  let pts := map (fun '(h, k) => (h, firsts S h k)) L in
  if forallb (fun '(_, o) => match o with Some _ => true | None => false end) pts then
    let pts := map (fun '(h, o) => (h, match o with Some ts => ts | None => [] end)) pts in
    let outs := fold_right (fun '(_, ts) acc => fold_right tmax acc ts) [] pts in
    let hs := dedup (labels_of L outs S) in
    let pent := map (fun h => (h, (match find (fun '(h', _) => lexp_eqb h h') pts with Some (_, ts) => ts | None => [] end, lget h outs))) hs in
    let bent := map (fun h =>
                  let k := lget h L in
                  let m := lget h outs in
                  let '(ts, mS) := match sfind F h S with Some (Some (ts, mS)) => (tl_list ts, mS) | _ => ([], 0) end in
                  let len := List.length ts in
                  (h, (map (fun j => NVar h j) (seq 0 m) ++ skipn k ts,
                       if len <=? k then mS + k - len else mS))) hs in
    let ok := forallb (fun h =>
                let k := lget h L in
                let m := lget h outs in
                let '(ts, mS) := match sfind F h S with Some (Some (ts, mS)) => (tl_list ts, mS) | _ => ([], 0) end in
                let len := List.length ts in
                (if len <=? k then m <=? mS + k - len else true)
                && forallb (fun t => match t with NVar g j => lget g outs <=? j | NBind _ _ _ => true end) (skipn k ts)) hs in
    if ok then
      match sbuild pent, sbuild bent with
      | Some P, Some B =>
          match scomp F ntm B P with Some S' => if seg_eqb S' S then Some (B, P) else None | None => None end
      | _, _ => None
      end
    else None
  else None.

End Split.

(** *** Normal forms of [HNorm]

    An [HNorm] word, outermost step first, is shown group by group: a
    group is a run of input entries, then of atoms, then of weakenings,
    and is one context form: the entries are its inputs, the atoms its
    tail, the weakenings its outputs.  A value is read at the end of the
    word; in the form it is a slot, the variable at the group's own
    input that the rest of the word sends there (found with [HNorm]'s
    lookup), or a term whose payload is some entries in front of exactly
    what follows the group's entries (the payload context).  Anything
    else is not shown.  The result is checked like any display. *)

Section HDisplay.

Variable F : order.
Variable T : HNorm.st.

(** The word from the cell [i]. *)
Fixpoint hcells (fuel : nat) (i : positive) : HNorm.word :=
  match fuel with
  | 0 => []
  | S f =>
      if Pos.eqb i 1 then []
      else match PositiveMap.find i (HNorm.cells T) with Some (s, t) => (s, i) :: hcells f t | None => [] end
  end.

Definition hfuel : nat := Pos.to_nat (HNorm.next T).

Fixpoint take_se (w : HNorm.word) : list (lexp * HNorm.val) * HNorm.word :=
  match w with (HNorm.SE h v, _) :: w' => let '(l, r) := take_se w' in ((h, v) :: l, r) | _ => ([], w) end.

Fixpoint take_sa (w : HNorm.word) : list nat * HNorm.word :=
  match w with (HNorm.SA a, _) :: w' => let '(l, r) := take_sa w' in (a :: l, r) | _ => ([], w) end.

Fixpoint take_sw (w : HNorm.word) : list lexp * HNorm.word :=
  match w with (HNorm.SW h, _) :: w' => let '(l, r) := take_sw w' in (h :: l, r) | _ => ([], w) end.

(** The groups: entries, atoms, weakenings, the word after the entries,
    and the word after the group. *)
Fixpoint hgroups (fuel : nat) (w : HNorm.word)
  : list (list (lexp * HNorm.val) * list nat * list lexp * HNorm.word * HNorm.word) :=
  match fuel with
  | 0 => []
  | S f =>
      match w with
      | [] => []
      | _ =>
          let '(es, w1) := take_se w in
          let '(as', w2) := take_sa w1 in
          let '(ws, w3) := take_sw w2 in
          (es, as', ws, w1, w3) :: hgroups f w3
      end
  end.

Fixpoint opt_all {A} (l : list (option A)) : option (list A) :=
  match l with [] => Some [] | Some x :: r => option_map (cons x) (opt_all r) | None :: _ => None end.

Fixpoint se_labels (w : HNorm.word) : list lexp :=
  match w with [] => [] | (HNorm.SE h _, _) :: w' => h :: se_labels w' | _ :: w' => se_labels w' end.

Fixpoint first_match (cs : list (lexp * nat)) (v : HNorm.val) (R : HNorm.word) : option (lexp * nat) :=
  match cs with
  | [] => None
  | (c, j) :: r => if HNorm.val_eqb (fst (HNorm.lookup F c j R T)) v then Some (c, j) else first_match r v R
  end.

(** The variable at the start of [R] that [R] sends to [v]. *)
Definition hrel (v : HNorm.val) (R : HNorm.word) : option (lexp * nat) :=
  match v with
  | HNorm.VVar g i | HNorm.VLook g i _ =>
      let n := i + List.length R + 1 in
      first_match (flat_map (fun c => map (pair c) (seq 0 n)) (g :: se_labels R)) v R
  | HNorm.VTerm _ _ _ => None
  end.

(** The entries of a payload word in front of the cell [a]. *)
Fixpoint strip_to (a : positive) (w : HNorm.word) : option (list (lexp * HNorm.val)) :=
  match w with
  | [] => if Pos.eqb a 1 then Some [] else None
  | (s, i) :: w' =>
      if Pos.eqb i a then Some []
      else match s with HNorm.SE h v => option_map (cons (h, v)) (strip_to a w') | _ => None end
  end.

Fixpoint tapp (ts u : tlist) : tlist := match ts with TNil => u | TCons t r => TCons t (tapp r u) end.

Fixpoint add_in (h : lexp) (t : ntgt) (s : seg) : seg :=
  match s with
  | SNil => SEnt h (TCons t TNil) 0 SNil
  | SEnt g ts m r => if lexp_eqb g h then SEnt g (tapp ts (TCons t TNil)) m r else SEnt g ts m (add_in h t r)
  end.

Fixpoint add_out (h : lexp) (s : seg) : seg :=
  match s with
  | SNil => SEnt h TNil 1 SNil
  | SEnt g ts m r => if lexp_eqb g h then SEnt g ts (S m) r else SEnt g ts m (add_out h r)
  end.

Fixpoint step_labels (w : HNorm.word) : list lexp :=
  match w with
  | [] => []
  | (HNorm.SE h _, _) :: w' | (HNorm.SW h, _) :: w' => h :: step_labels w'
  | _ :: w' => step_labels w'
  end.

Fixpoint dedup_l (hs : list lexp) : list lexp :=
  match hs with [] => [] | h :: r => h :: filter (fun g => negb (lexp_eqb h g)) (dedup_l r) end.

Fixpoint count_l (h : lexp) (hs : list lexp) : nat :=
  match hs with [] => 0 | g :: r => (if lexp_eqb h g then 1 else 0) + count_l h r end.

(** Targets in a form read at the start of [R], whose outputs are [outs].
    A term's payload is found name by name: where the payload sends
    [nₖ], as a variable at the start of [R], until the names follow the
    default, past the form's slots on [n]. *)
Fixpoint htgt (fuel : nat) (outs : list lexp) (R : HNorm.word) (v : HNorm.val) : option ntgt :=
  match v with
  | HNorm.VTerm u None p =>
      match fuel with
      | 0 => None
      | S f =>
          let pw := hcells hfuel p in
          let labs := filter (fun h => match h with LNone => false | _ => true end)
                        (dedup_l (step_labels pw ++ outs ++ step_labels R)) in
          let entry (n : lexp) : option (list ntgt * nat) :=
            let bound := count_l n (step_labels pw) + count_l n outs + count_l n (step_labels R) + 2 in
            let tg (k : nat) := htgt f outs R (fst (HNorm.lookup F n k pw T)) in
            let fix dflt (k : nat) (d : nat) (fuel : nat) : bool :=
              match fuel with
              | 0 => true
              | S fu => match tg k with
                        | Some (NVar c j) => lexp_eqb c n && Nat.eqb j d && dflt (S k) (S d) fu
                        | _ => false
                        end
              end in
            let fix firstK (K : nat) (fuel : nat) : option (nat * nat) :=
              match fuel with
              | 0 => None
              | S fu =>
                  match tg K with
                  | Some (NVar c d) => if lexp_eqb c n && dflt K d (S bound) then Some (K, d) else firstK (S K) fu
                  | _ => firstK (S K) fu
                  end
              end in
            match firstK 0 (S bound) with
            | Some (K, d) => option_map (fun ts => (ts, d)) (opt_all (map tg (seq 0 K)))
            | None => None
            end in
          let fix go (ls : list lexp) (acc : seg) : option seg :=
            match ls with
            | [] => Some acc
            | n :: r =>
                match entry n with
                | Some (ts, d) =>
                    match ts, d with
                    | [], 0 => go r acc
                    | _, _ => go r (SEnt n (fold_right TCons TNil ts) d acc)
                    end
                | None => None
                end
            end in
          option_map (fun P => NBind u (WEnd P) None) (go labs SNil)
      end
  | HNorm.VTerm _ (Some _) _ => None
  | _ => option_map (fun '(c, j) => NVar c j) (hrel v R)
  end.

Fixpoint add_in_front (h : lexp) (t : ntgt) (s : seg) : seg :=
  match s with
  | SNil => SEnt h (TCons t TNil) 0 SNil
  | SEnt g ts m r => if lexp_eqb g h then SEnt g (TCons t ts) m r else SEnt g ts m (add_in_front h t r)
  end.

Fixpoint hgseg (es : list (lexp * HNorm.val)) (ws : list lexp) (R : HNorm.word) : option seg :=
  match es with
  | [] => Some (fold_left (fun s h => add_out h s) ws SNil)
  | (h, v) :: r =>
      match htgt 8 ws R v, hgseg r ws R with
      | Some t, Some Sg => Some (add_in_front h t Sg)
      | _, _ => None
      end
  end.

Fixpoint entries_eqb (a b : list (lexp * HNorm.val)) : bool :=
  match a, b with
  | [], [] => true
  | (h, v) :: a', (g, u) :: b' => lexp_eqb h g && HNorm.val_eqb v u && entries_eqb a' b'
  | _, _ => false
  end.

Fixpoint remove_nth {A} (k : nat) (l : list A) : list A :=
  match k, l with _, [] => [] | 0, _ :: r => r | S k, x :: r => x :: remove_nth k r end.

(** An entry [h := u] whose payload is exactly the other entries in
    front of [a1] is the composition of [⟦ h := u ⟧] after them. *)
Definition factors (a1 : positive) (others : list (lexp * HNorm.val)) (v : HNorm.val) : option nat :=
  match v with
  | HNorm.VTerm u None p =>
      match strip_to a1 (hcells hfuel p) with Some pre => if entries_eqb pre others then Some u else None | None => None end
  | _ => None
  end.

Fixpoint find_factor (a1 : positive) (es : list (lexp * HNorm.val)) (k : nat) (l : list (lexp * HNorm.val))
  : option (nat * lexp * nat) :=
  match l with
  | [] => None
  | (h, v) :: r =>
      match factors a1 (remove_nth k es) v with
      | Some u => Some (k, h, u)
      | None => find_factor a1 es (S k) r
      end
  end.

(** The factored terms, outermost first, and the entries left. *)
Fixpoint factor (fuel : nat) (a1 : positive) (es : list (lexp * HNorm.val)) : list (lexp * nat) * list (lexp * HNorm.val) :=
  match fuel with
  | 0 => ([], es)
  | S f =>
      match find_factor a1 es 0 es with
      | Some (k, h, u) => let '(fs, rest) := factor f a1 (remove_nth k es) in ((h, u) :: fs, rest)
      | None => ([], es)
      end
  end.

End HDisplay.

Definition sub_piece (h : lexp) (u : nat) : option dpiece :=
  option_map short_or_full (display_seg (SEnt h (TCons (NBind u (WEnd SNil) None) TNil) 0 SNil) None).

Definition is_term (v : HNorm.val) : bool := match v with HNorm.VTerm _ _ _ => true | _ => false end.

(** One group, outermost piece first.  With atoms, terms that cannot sit
    in the tail form go into a form of their own outside it, read over
    the word without them. *)
Definition hgroup (F : order) (T : HNorm.st) (es : list (lexp * HNorm.val)) (as' : list nat) (ws : list lexp)
  (w1 w2 R : HNorm.word) : option (list dpiece) :=
  let '(fs, es') := factor T (List.length es) (HNorm.wid w1) es in
  match opt_all (map (fun '(h, u) => sub_piece h u) fs) with
  | None => None
  | Some ps =>
      let tail := match as' with [] => None | _ => Some (rev as') end in
      let one (es : list (lexp * HNorm.val)) :=
        match hgseg F T es ws R with
        | Some Sg => match display_seg Sg tail with Some d => Some [short_or_full d] | None => None end
        | None => None
        end in
      match es' with
      | [] =>
          let atoms := match tail with Some ns => [DLift [] ns] | None => [] end in
          match ws with
          | [] => Some (ps ++ atoms)
          | _ => match display_seg (fold_left (fun s h => add_out h s) ws SNil) None with
                 | Some d => Some (ps ++ atoms ++ [short_or_full d])
                 | None => None
                 end
          end
      | _ =>
          match one es' with
          | Some d => Some (ps ++ d)
          | None =>
              match tail with
              | None => None
              | Some _ =>
                  let terms := filter (fun '(_, v) => is_term v) es' in
                  let rest := filter (fun '(_, v) => negb (is_term v)) es' in
                  let '(Wi, T') := HNorm.rebuild (map (fun '(h, v) => HNorm.SE h v) rest) w1 T in
                  match hgseg F T' terms [] Wi, (match rest with [] => Some [] | _ => one rest end) with
                  | Some So, Some di =>
                      match display_seg So None with
                      | Some d => Some (ps ++ short_or_full d :: (match rest with [] => [DLift [] (rev as')] ++
                                          (match ws with [] => [] | _ => match display_seg (fold_left (fun s h => add_out h s) ws SNil) None with Some d' => [short_or_full d'] | None => [] end end)
                                        | _ => di end))
                      | None => None
                      end
                  | _, _ => None
                  end
              end
          end
      end
  end.

Fixpoint dt_size (d : dtgt) : nat :=
  match d with
  | DSlot _ _ => 1
  | DTerm _ p => S (fold_right (fun '(_, d) n => dt_size d + n) 0 p)
  end.

Definition dp_size (d : dpiece) : nat :=
  match d with
  | DFull os is _ => List.length os + fold_right (fun i n => match i with DITerm _ _ p => S (fold_right (fun '(_, d) n => dt_size d + n) 0 p) | _ => 1 end + n) 0 is
  | DShort es _ => List.length es
  | DLift hs ns => List.length hs + List.length ns
  end.

(** The pieces, innermost first (as [render_pieces] composes them). *)
Definition hdisplay (F : order) (T : HNorm.st) (w : HNorm.word) : option (list dpiece) :=
  match opt_all (map (fun '(es, as', ws, w1, R) =>
                        let '(_, w2) := take_sa w1 in hgroup F T es as' ws w1 w2 R) (hgroups (hfuel T) w)) with
  | Some pss =>
      let ps := rev (List.concat pss) in
      if Nat.leb (fold_right (fun d n => dp_size d + n) 0 ps) 200 then Some ps else None
  | None => None
  end.

(** Where [e]'s normal form sends [hᵢ], when it is a term: the term and
    its payload, shown. *)
Definition hlook_pay (F : order) (n : nat) (e : aexp) (h : lexp) (i : nat) : option (nat * list dpiece) :=
  match hlook F n e h i with
  | Some (HNorm.VTerm u None p, T1) => option_map (pair u) (hdisplay F T1 (hcells T1 (hfuel T1) p))
  | _ => None
  end.

(** Normalise and show. *)
Definition hshow (F : order) (ntm : nat) (e : aexp) : option (list dpiece) :=
  if aok ntm e then let '(w, T) := HNorm.norm F e [] HNorm.st0 in hdisplay F T w else None.

(** *** Terms before atoms

    The normaliser carries a term substituted before an atom past it: the
    input is passed around the atom, and the term sits in the last
    segment with the atom in its payload.  For display the term is moved
    back: it goes to the input passed around the atom, the atom comes off
    the front of its payload, and the atom loses a lift.  So
    [⟦ x := u ⟧ ⨾ σ] is shown as that, not as [⟦ x | σ ⟧ ⨾ ⟦ x := u⟨σ⟩ ⟧].
    The result is checked like any display. *)

Section Unpass.

Variable F : order.
Variable ntm : nat.

Fixpoint tcount (s : seg) : nat := match s with SNil => 0 | SEnt _ ts _ r => tlen ts + tcount r end.

(** The input of label [g] that [U] sends to [g₍ₖ₎]. *)
Fixpoint find_input (U : seg) (g : lexp) (k p fuel : nat) : option nat :=
  match fuel with
  | 0 => None
  | S f =>
      match seg_tgt F U g p with
      | Some (NVar g' k') => if lexp_eqb g' g && Nat.eqb k' k then Some p else find_input U g k (S p) f
      | _ => find_input U g k (S p) f
      end
  end.

Definition sentry (Sg : seg) (g : lexp) : option (list ntgt * nat) :=
  match sfind F g Sg with Some (Some (ts, m)) => Some (tl_list ts, m) | Some None => Some ([], 0) | None => None end.

(** Sending input [g₍ₚ₎] to [t]. *)
Definition set_input (Sg : seg) (g : lexp) (p : nat) (t : ntgt) : option seg :=
  match sentry Sg g with
  | Some (ts, m) =>
      let len := List.length ts in
      let ts' := ts ++ map (fun j => NVar g (j - len + m)) (seq len (S p - len)) in
      let m' := if p <? len then m else S p - len + m in
      sset F g (tl_of (firstn p ts' ++ t :: skipn (S p) ts')) m' Sg
  | None => None
  end.

(** Dropping the [k]-th input of [g]. *)
Definition drop_input (Sg : seg) (g : lexp) (k : nat) : option seg :=
  match sentry Sg g with
  | Some (ts, m) => if k <? List.length ts then sset F g (tl_of (firstn k ts ++ skipn (S k) ts)) m Sg else None
  | None => None
  end.

Fixpoint ldec (g : lexp) (L : list (lexp * nat)) : list (lexp * nat) :=
  match L with
  | [] => []
  | (h, n) :: L => if lexp_eqb g h then (if Nat.eqb n 1 then L else (h, n - 1) :: L) else (h, n) :: ldec g L
  end.

(** Moving the term at [g₍ₖ₎] of [A], in [A ∘ ⇑ᴸσₐ ∘ w], before the atom. *)
Definition unpass_at (A : seg) (L : list (lexp * nat)) (a : nat) (w : word) (g : lexp) (k : nat) : option word :=
  match seg_tgt F A g k with
  | Some (NBind u (WAtom SNil _ a' q) None) =>
      if Nat.eqb a a' then
        let U := whead w in
        let D := SEnt g (tl_of (map (fun j => NVar g j) (seq 0 k) ++ [NVar g 0])) k SNil in
        match find_input U g k 0 (S (k + tcount U)), drop_input A g k, scomp F ntm D U with
        | Some p, Some A', Some U1 =>
            match set_input U1 g p (NBind u q None) with
            | Some U' => Some (WAtom A' (ldec g L) a (wsethead w U'))
            | None => None
            end
        | _, _, _ => None
        end
      else None
  | _ => None
  end.

Fixpoint first_some {A B} (f : A -> option B) (xs : list A) : option B :=
  match xs with [] => None | x :: xs => match f x with Some y => Some y | None => first_some f xs end end.

Definition unpass_one (A : seg) (L : list (lexp * nat)) (a : nat) (w : word) : option word :=
  first_some (fun '(g, c) => first_some (unpass_at A L a w g) (seq 0 c)) L.

Fixpoint unpass (fuel : nat) (w : word) : word :=
  match fuel with
  | 0 => w
  | S f =>
      match w with
      | WEnd _ => w
      | WAtom A L a w' =>
          match unpass_one A L a w' with
          | Some w2 => unpass f w2
          | None => WAtom A L a (unpass f w')
          end
      | WLay A w' => WLay A (unpass f w')
      end
  end.

End Unpass.

Definition lift_list (L : list (lexp * nat)) : list lexp := rev (flat_map (fun '(h, n) => repeat h n) L).

Fixpoint display_items (F : order) (ntm : nat) (items : list gitem) : option (list dpiece) :=
  match items with
  | [] => Some []
  | GSeg SNil :: rest => display_items F ntm rest
  | GSeg Sg :: GRun L as' :: rest =>
      match display_items F ntm rest with
      | None => None
      | Some ds =>
          let separate :=
            match display_seg Sg None with
            | Some d => Some (d :: DLift (lift_list L) as' :: ds)
            | None => None
            end in
          match split_seg F ntm L Sg with
          | Some (B, P) =>
              match display_seg P (Some as') with
              | Some (DFull os is _) =>
                  if merges is L then
                    match B with
                    | SNil => Some (DFull os is (Some as') :: ds)
                    | _ => match display_seg B None with
                           | Some d => Some (d :: DFull os is (Some as') :: ds)
                           | None => separate
                           end
                    end
                  else separate
              | _ => separate
              end
          | None => separate
          end
      end
  | GSeg Sg :: rest =>
      match display_seg Sg None, display_items F ntm rest with
      | Some d, Some ds => Some (d :: ds)
      | _, _ => None
      end
  | GRun L as' :: rest =>
      match display_items F ntm rest with
      | Some ds => Some (DLift (lift_list L) as' :: ds)
      | None => None
      end
  end.

Definition display_nf (F : order) (ntm : nat) (r : option word) : option (list dpiece) :=
  match r with
  | Some w => option_map (map short_or_full) (display_items F ntm (witems (unpass F ntm 64 w)))
  | None => None
  end.

(** The canonical layered word, step by step: each segment is a context
    form and each atom a tail under its lifts. *)
Definition ldisplay (F : order) (ntm : nat) (l : lword) : option (list dpiece) :=
  fold_right (fun x acc =>
    match acc, display_nf F ntm (Some (match x with LS s => WEnd s | LA L a => WAtom SNil L a (WEnd SNil) end)) with
    | Some r, Some ps => Some (r ++ ps)
    | _, _ => None
    end) (Some []) l.

(** *** Materialising payloads: the terms with a payload adjustment in a
    single segment, and the segment with some of them replaced by term
    atoms. *)
Fixpoint mat_targets (s : seg) : list (nat * word) :=
  let fix go (ts : tlist) :=
    match ts with
    | TNil => []
    | TCons (NBind u wp None) r => if word_eqb wp (WEnd SNil) then go r else (u, wp) :: go r
    | TCons _ r => go r
    end in
  match s with SNil => [] | SEnt _ ts _ r => go ts ++ mat_targets r end.

Fixpoint mat_lookup (rep : list (nat * word * nat)) (u : nat) (wp : word) : option nat :=
  match rep with
  | [] => None
  | (u', wp', k) :: r => if (if Nat.eqb u u' then word_eqb wp wp' else false) then Some k else mat_lookup r u wp
  end.

Fixpoint smat_apply (rep : list (nat * word * nat)) (s : seg) : seg :=
  let fix go (ts : tlist) :=
    match ts with
    | TNil => TNil
    | TCons (NBind u wp None as t) r =>
        TCons (match mat_lookup rep u wp with Some k => NBind k (WEnd SNil) None | None => t end) (go r)
    | TCons t r => TCons t (go r)
    end in
  match s with SNil => SNil | SEnt h ts m r => SEnt h (go ts) m (smat_apply rep r) end.

(** ** Rendering *)

Ltac lnth l n :=
  lazymatch n with
  | O => lazymatch l with ?x :: _ => x end
  | S ?n => lazymatch l with _ :: ?l => lnth l n end
  end.

Ltac lab le h :=
  lazymatch h with
  | LCon ?s => s
  | LAtom ?n => let k := eval vm_compute in (N.to_nat n) in lnth le k
  end.

Ltac atom ae n := lazymatch lnth ae n with adj_raw ?s => s end.

Ltac slot env h j :=
  lazymatch env with
  | ((?h', ?j'), ?a) :: ?env => match constr:(tt) with
                                | _ => let _ := constr:(eq_refl : (h, j) = (h', j')) in a
                                | _ => slot env h j
                                end
  end.

Ltac render_pay le te p env :=
  lazymatch p with
  | nil => exact PEmpty
  | (?x, DSlot ?h ?j) :: ?r =>
      let xl := lab le x in let a := slot env h j in refine (PRen _ xl a); render_pay le te r env
  | (?x, DTerm ?u ?q) :: ?r =>
      let xl := lab le x in let ut := lnth te u in
      refine (PSub _ xl ut _); [render_pay le te r env|render_pay le te q env]
  end.

Ltac render_ins le te is env :=
  lazymatch is with
  | nil => exact IEmpty
  | DIPos LNone :: ?r => refine (IPosB _); render_ins le te r env
  | DIPos ?x :: ?r => let xl := lab le x in refine (IPosF _ xl); render_ins le te r env
  | DISlot LNone ?h ?j :: ?r => let a := slot env h j in refine (IRenB _ a); render_ins le te r env
  | DISlot ?x ?h ?j :: ?r =>
      let xl := lab le x in let a := slot env h j in refine (IRenF _ xl a); render_ins le te r env
  | DITerm LNone ?u ?q :: ?r =>
      let ut := lnth te u in refine (ISubB _ ut _); [render_ins le te r env|render_pay le te q env]
  | DITerm ?x ?u ?q :: ?r =>
      let xl := lab le x in let ut := lnth te u in
      refine (ISubF _ xl ut _); [render_ins le te r env|render_pay le te q env]
  end.

Ltac render_outs le te os is env g :=
  lazymatch os with
  | nil => lazymatch g with
           | tt => refine (OEnd _); render_ins le te is env
           | _ => refine (OEndT g _); render_ins le te is env
           end
  | DOPos LNone _ :: ?r => refine (OPosB _); render_outs le te r is env g
  | DOPos ?h _ :: ?r => let hl := lab le h in refine (OPosF _ hl); render_outs le te r is env g
  | DONamed LNone ?j :: ?r =>
      let a := fresh "a" in refine (ONamB (fun a => _)); render_outs le te r is (((LNone, j), a) :: env) g
  | DONamed ?h ?j :: ?r =>
      let hl := lab le h in let a := fresh "a" in
      refine (ONamF hl (fun a => _)); render_outs le te r is (((h, j), a) :: env) g
  end.

Ltac render_lifts le hs :=
  lazymatch hs with
  | nil => exact SEmpty
  | LNone :: ?r => refine (SLiftB _); render_lifts le r
  | ?h :: ?r => let hl := lab le h in refine (SLiftF _ hl); render_lifts le r
  end.

Ltac render_short le te es :=
  lazymatch es with
  | nil => exact SEmpty
  | SELift LNone :: ?r => refine (SLiftB _); render_short le te r
  | SELift ?h :: ?r => let hl := lab le h in refine (SLiftF _ hl); render_short le te r
  | SESub LNone ?u :: ?r => let ut := lnth te u in refine (SSubB _ ut PEmpty); render_short le te r
  | SESub ?h ?u :: ?r => let hl := lab le h in let ut := lnth te u in refine (SSubF _ hl ut PEmpty); render_short le te r
  end.

Ltac render_tail ae ns :=
  lazymatch ns with
  | ?n :: nil => atom ae n
  | ?n :: ?r => let s := atom ae n in let t := render_tail ae r in constr:(compose s t)
  end.

Ltac render_piece le te ae p :=
  lazymatch p with
  | DFull ?os ?is None =>
      refine (cform_id _);
      lazymatch goal with |- @octx _ ?K _ _ _ _ _ _ _ _ => render_outs le te os is (@nil ((lexp * nat) * slot K)) tt end
  | DFull ?os ?is (Some ?ns) =>
      let s := render_tail ae ns in let g := fresh "Γ" in
      refine (cform (fun g => _) s);
      lazymatch goal with |- @octx _ ?K _ _ _ _ _ _ _ _ => render_outs le te os is (@nil ((lexp * nat) * slot K)) g end
  | DLift nil ?ns => let s := render_tail ae ns in exact s
  | DLift ?hs ?ns => let s := render_tail ae ns in refine (cform_id (OShortT (Nt:=0) (STail _ s))); render_lifts le hs
  | DShort ?es None => refine (cform_id (OShort _)); render_short le te es
  | DShort ?es (Some ?ns) =>
      let s := render_tail ae ns in refine (cform_id (OShortT (Nt:=0) (STail _ s))); render_short le te es
  end.

Ltac render_pieces le te ae ps :=
  lazymatch ps with
  | nil => exact identity
  | ?p :: nil => render_piece le te ae p
  | ?p :: ?r => refine (compose _ _); [|render_pieces le te ae r]; render_piece le te ae p
  end.

(** ** The tactic *)

(** Proves [a = b] for the rewrite to a rendered normal form, by
    comparing their [HNorm] normal forms. *)
Ltac names_decide :=
  lazymatch goal with
  | |- @eq (radj ?T) ?lhs ?rhs =>
      let env0 := constr:((@nil label, @nil T, @nil (radj T), @nil (rpadj T))) in
      lazymatch reify_adj_top lhs env0 with
      | (?e1, ?env1) =>
          lazymatch reify_adj_top rhs env1 with
          | (?e2, ?env2) =>
              lazymatch collect_facts env2 (@nil (lexp * lexp)) with
              | ((?le, ?te, ?ae, ?pe), order_of ?l) =>
                  change (aeden le te ae pe e1 = aeden le te ae pe e2);
                  refine (hn_eq_t_sound le te ae pe l e1 e2 _ _);
                  [ unfold lfacts_ok; repeat constructor; cbn [lden N.to_nat Pos.to_nat Pos.iter_op Nat.add nth]; assumption
                  | vm_compute; first
                      [ reflexivity
                      | fail 2 "names: the two sides have different normal forms, or a label order is missing" ] ]
              end
          end
      end
  end.

(** Unfolding context forms down to the raw constructors. *)
Ltac names_unfold :=
  cbn [adj_raw identity compose at_scope
       cnil cent cbnd csub csubb
       cnil_full cnil_short cent_full cent_short cbnd_full cbnd_short
       csub_full csub_short csubb_full csubb_short
       cform cform_id octx_den octx_probe ictx_den sctx_den nth slot_at slot_ix
       in_bound in_free out_bound out_free pctx_den pctx_pay noslot pcompose padj_raw pid
       to_target var_raw bvar bvar0 fvar lvar vdummy vshift_bound vshift_free].

(** An adjustment and its displayed normal form are the same: their normal forms are compared. *)
Local Ltac names_same := apply adj_eq; names_unfold; names_decide.

Ltac is_adj_expr a :=
  lazymatch a with
  | compose _ _ => idtac
  | cform_id _ => idtac
  | cform _ _ => idtac
  | at_scope _ => idtac
  end.

(** The reifier sees term atoms after unfolding; they are shown as the
    subterms of the original adjustment they came from. *)
Ltac restore_term u a :=
  match a with
  | context [?v] => let _ := constr:(@eq_refl _ u : u = v) in v
  | _ => u
  end.

Ltac restore_terms te a :=
  lazymatch te with
  | nil => te
  | ?u :: ?r => let u' := restore_term u a in let r' := restore_terms r a in constr:(u' :: r')
  end.

(** Rewriting one adjustment to its normal form, shown as context forms,
    then running [kt] on its term atoms; runs [kt] alone when it is
    already shown that way or the normal form is too large to show, and
    [kn] when it cannot be shown. *)
Ltac names_rewrite_k a kt kn :=
  let ty := type of a in
  lazymatch ty with
  | adj ?T _ _ =>
      let r := eval cbn [adj_raw identity compose at_scope
                         cnil cent cbnd csub csubb
                         cnil_full cnil_short cent_full cent_short cbnd_full cbnd_short
                         csub_full csub_short csubb_full csubb_short
                         cform cform_id octx_den octx_probe ictx_den sctx_den nth slot_at slot_ix
                         in_bound in_free out_bound out_free pctx_den pctx_pay noslot pcompose padj_raw pid
                         to_target var_raw bvar bvar0 fvar lvar vdummy vshift_bound vshift_free] in (adj_raw a) in
      let env0 := constr:((@nil label, @nil T, @nil (radj T), @nil (rpadj T))) in
      lazymatch reify_adj_top r env0 with
      | (?e, ?env1) =>
          lazymatch collect_facts env1 (@nil (lexp * lexp)) with
          | ((?le, ?te, ?ae, ?pe), ?F) =>
              let d := eval vm_compute in (hshow F (List.length te) e) in
              lazymatch d with
              | Some ?ps =>
                  let te' := restore_terms te a in
                  let bb := fresh "b" in
                  unshelve evar (bb : ty); [render_pieces le te' ae ps|];
                  let b := eval cbv delta [bb] in bb in
                  clear bb;
                  tryif constr_eq a b then kt te'
                  else (let E := fresh "E" in assert (E : a = b) by names_same; rewrite E; clear E; kt te')
              | None => kn
              end
          end
      end
  end.

Ltac names_rewrite a := names_rewrite_k a ltac:(fun _ => fail) fail.

(** Applying an adjustment to a variable: when the normal form is a single
    context form, the result is read off it. *)
Ltac names_var_eq t E :=
  lazymatch t with
  | @apply_var ?T ?N ?M ?a ?v =>
      let r := eval cbn [adj_raw identity compose at_scope
                         cnil cent cbnd csub csubb
                         cnil_full cnil_short cent_full cent_short cbnd_full cbnd_short
                         csub_full csub_short csubb_full csubb_short
                         cform cform_id octx_den octx_probe ictx_den sctx_den nth slot_at slot_ix
                         in_bound in_free out_bound out_free pctx_den pctx_pay noslot pcompose padj_raw pid
                         to_target var_raw bvar bvar0 fvar lvar vdummy vshift_bound vshift_free] in (adj_raw a) in
      let vr := eval cbn [var_raw bvar bvar0 fvar lvar] in (var_raw v) in
      lazymatch vr with
      | mk_rvar ?hv ?i =>
          let _ := is_nat_lit i in
          let env0 := constr:((@nil label, @nil T, @nil (radj T), @nil (rpadj T))) in
          lazymatch reify_adj_top r env0 with
          | (?e, ?env1) =>
              lazymatch reify_label hv env1 with
              | (?eh, ?env2) =>
                  lazymatch collect_facts env2 (@nil (lexp * lexp)) with
                  | ((?le, ?te, ?ae, ?pe), order_of ?l) =>
                      let F := constr:(order_of l) in
                      let res := eval vm_compute in (hlook_var F (List.length te) e eh i) in
                      lazymatch res with
                      | Some (?h', ?j) =>
                          let w := lazymatch h' with
                                   | LNone => constr:(@bvar M j stt)
                                   | _ => let x := lab le h' in constr:(@fvar M x j)
                                   end in
                          assert (E : apply_var a v = Rename w)
                            by (apply apply_var_rename; names_unfold;
                                change (rapply (aeden le te ae pe e) (mk_rvar (lden le eh) i)
                                        = inl (mk_rvar (lden le h') j));
                                refine (hlook_var_sound le te ae pe l e eh i h' j _ _);
                                [ unfold lfacts_ok; repeat constructor; cbn [lden N.to_nat Pos.to_nat Pos.iter_op Nat.add nth]; assumption
                                | vm_compute; reflexivity ])
                      | None =>
                          let pr := eval vm_compute in (hlook_pay F (List.length te) e eh i) in
                          lazymatch pr with
                          | Some (?u, ?ps) =>
                              lazymatch constr:(Some ps) with
                              | Some ?ps =>
                                  let te' := restore_terms te a in
                                  let bb := fresh "b" in
                                  unshelve evar (bb : adj T 0 M); [render_pieces le te' ae ps|];
                                  let b := eval cbv delta [bb] in bb in
                                  clear bb;
                                  let rb := eval cbn [adj_raw identity compose at_scope
                                                      cnil cent cbnd csub csubb
                                                      cnil_full cnil_short cent_full cent_short cbnd_full cbnd_short
                                                      csub_full csub_short csubb_full csubb_short
                                                      cform cform_id octx_den octx_probe ictx_den sctx_den nth slot_at slot_ix
                                                      in_bound in_free out_bound out_free pctx_den pctx_pay noslot pcompose padj_raw pid
                                                      to_target var_raw bvar bvar0 fvar lvar vdummy vshift_bound vshift_free] in (adj_raw b) in
                                  lazymatch reify_adj_top rb (le, te, ae, pe) with
                                  | (?eb, ?env3) =>
                                      lazymatch collect_facts env3 (@nil (lexp * lexp)) with
                                      | ((?le3, ?te3, ?ae3, ?pe3), order_of ?l3) =>
                                          let x := lnth te' u in
                                          assert (E : apply_var a v = Bind x (pcompose b pid))
                                            by (apply apply_var_bind; names_unfold;
                                                change (rapply (aeden le3 te3 ae3 pe3 e) (mk_rvar (lden le3 eh) i)
                                                        = inr (x, rpcompose (aeden le3 te3 ae3 pe3 eb) rpidentity));
                                                refine (hbind_sound le3 te3 ae3 pe3 l3 e eh i eb u x _ _ _);
                                                [ unfold lfacts_ok; repeat constructor; cbn [lden N.to_nat Pos.to_nat Pos.iter_op Nat.add nth]; assumption
                                                | vm_compute; reflexivity
                                                | reflexivity ])
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end
  end.

(** Every adjustment in the goal built from context forms and [∘] is
    rewritten to its normal form, shown as context forms, and then every
    [apply_var a v] whose result the normal form of [a] gives. *)
Ltac names_apply_var t := let E := fresh "E" in names_var_eq t E; rewrite E; clear E.

(** Candidates for rewriting, as nested pairs ending in [tt]: adjustment
    expressions not inside another candidate.  (Value-returning, so that
    they can be collected.) *)
Ltac is_adj_v a :=
  lazymatch a with compose _ _ => tt | cform_id _ => tt | cform _ _ => tt | at_scope _ => tt end.

Ltac not_in a acc :=
  lazymatch acc with
  | tt => tt
  | (?c, ?r) => lazymatch c with context [a] => fail | _ => not_in a r end
  end.

Ltac goal_candidates acc :=
  match goal with
  | |- context [?a] => let _ := is_adj_v a in let _ := not_in a acc in goal_candidates (a, acc)
  | _ => acc
  end.

(** The candidates strictly inside [t]. *)
Ltac candidates_in t acc :=
  match t with
  | context [?a] =>
      let _ := is_adj_v a in
      let _ := lazymatch a with t => fail | _ => tt end in
      let _ := not_in a acc in
      candidates_in t (a, acc)
  | _ => acc
  end.

Ltac candidates_in_terms te acc :=
  lazymatch te with
  | nil => acc
  | ?u :: ?r => let acc' := candidates_in u acc in candidates_in_terms r acc'
  end.

(** Each candidate is rewritten once, and then the candidates in its
    terms; one whose normal form cannot be shown is left, and the
    candidates inside it are tried instead. *)
Ltac rewrite_each cs :=
  lazymatch cs with
  | (?a, ?r) =>
      try names_rewrite_k a
            ltac:(fun te => let cs' := candidates_in_terms te tt in rewrite_each cs')
            ltac:(idtac; let ins := candidates_in a tt in rewrite_each ins);
      rewrite_each r
  | tt => idtac
  end.

Ltac names_adjs := let cs := goal_candidates tt in rewrite_each cs.

Ltac names_apply :=
  repeat match goal with
         | |- context [?t] => lazymatch t with apply_var _ _ => names_apply_var t end
         end.

(** [eval f g a v] nodes whose variable [a]'s normal form renames are
    evaluated to [f w]. *)
Ltac names_eval :=
  repeat match goal with
  | |- context [@eval ?T ?N ?M ?R ?f ?g ?a ?v] =>
      let E := fresh "E" in
      names_var_eq (Indexed.apply_var a v) E;
      lazymatch type of E with
      | _ = Rename ?w =>
          rewrite (@eval_rename T N M R f g a v w E); clear E;
          let r := eval cbn in (f w) in change (f w) with r
      | _ = Bind ?x ?ρ => rewrite (@eval_bind T N M R f g a v x ρ E); clear E
      end
  end.

(** [names]:
    1. rewrites with [names_pre] and then [names_var], the monad laws that
       remove a Kleisli extension or move work into the adjustment (a
       syntax's [Subst] functor adds them): under binders and fusing
       nested substitutions first, then substituting into variables;
    2. rewrites every adjustment built from context forms and [∘] to its
       normal form, shown as context forms;
    3. evaluates [apply_var a v] and [eval] nodes for variables the normal
       form of [a] renames;
    4. rewrites with [names_post]: identity substitutions go, a payload
       result [u⟨b ∘ id⟩] becomes [subst b u], and an [eval] node left is
       shown as a substitution again;
    and repeats this until nothing changes: a pass after the first only
    finds work in terms that payload results put in the goal.
    Variables that the normal form sends to a term are evaluated as well,
    the payload adjustment shown as an adjustment. *)
(** Materialising: an adjustment [A] to the closed scope with terms with
    payload adjustments, used in a substitution, is replaced by [A'] where
    each such term [u⟨b⟩] is [u [b]], when the syntax has a [SubstMat]
    instance. *)
Ltac mat_render le te ae T ts :=
  lazymatch ts with
  | (_, ?wp) :: nil =>
      let F0 := constr:(order_of (@nil (lexp * lexp))) in
      let d := eval vm_compute in (display_nf F0 (List.length te) (Some wp)) in
      lazymatch d with
      | Some ?ps =>
          let bb := fresh "b" in
          unshelve evar (bb : adj T 0 0); [render_pieces le te ae ps|]
      end
  end.

Ltac mat_reify T bs env :=
  lazymatch bs with
  | nil => constr:((@nil aexp, env))
  | ?b :: ?r =>
      let rb := eval cbn [adj_raw identity compose at_scope
                          cnil cent cbnd csub csubb
                          cnil_full cnil_short cent_full cent_short cbnd_full cbnd_short
                          csub_full csub_short csubb_full csubb_short
                          cform cform_id octx_den octx_probe ictx_den sctx_den nth slot_at slot_ix
                          in_bound in_free out_bound out_free pctx_den pctx_pay noslot pcompose padj_raw pid
                          to_target var_raw bvar bvar0 fvar lvar vdummy vshift_bound vshift_free] in (adj_raw b) in
      lazymatch reify_adj_top rb env with
      | (?eb, ?env1) =>
          lazymatch mat_reify T r env1 with
          | (?ebs, ?env2) => constr:((eb :: ebs, env2))
          end
      end
  end.

Ltac mat_terms T inst te ts bs :=
  lazymatch ts with
  | (?u, _) :: nil =>
      lazymatch bs with
      | ?b :: nil =>
          let ut := lnth te u in
          let fb := eval hnf in (@sm_back _ inst) in
          let fs := eval hnf in (@sm_subst _ inst 0 0 b) in
          let fo := eval hnf in (@sm_of _ inst) in
          let x := eval cbv beta in (fb (fs (fo ut))) in
          constr:(x :: nil)
      end
  end.

Fixpoint mat_facts (k : nat) (ts : list (nat * word)) (ebs : list aexp) : list (nat * nat * aexp) :=
  match ts, ebs with
  | (u, _) :: ts, eb :: ebs => (k, u, eb) :: mat_facts (S k) ts ebs
  | _, _ => []
  end.

Fixpoint mat_rep (k : nat) (ts : list (nat * word)) : list (nat * word * nat) :=
  match ts with [] => [] | (u, wp) :: ts => (u, wp, k) :: mat_rep (S k) ts end.

Ltac mat_prove_facts inst te ts bs :=
  lazymatch ts with
  | nil => constructor
  | (?u, _) :: ?r =>
      lazymatch bs with
      | ?b :: ?bs' =>
          let ut := lnth te u in
          constructor;
          [ intros ? Hy; cbn [nth_error] in Hy |- *; injection Hy as <-; f_equal; symmetry;
            exact (@sm_g_spec _ inst b ut)
          | mat_prove_facts inst te r bs' ]
      end
  end.

Ltac names_mat_one A :=
  lazymatch type of A with
  | adj ?T ?N 0 =>
      let inst := constr:(_ : SubstMat T) in
      let r := eval cbn [adj_raw identity compose at_scope
                         cnil cent cbnd csub csubb
                         cnil_full cnil_short cent_full cent_short cbnd_full cbnd_short
                         csub_full csub_short csubb_full csubb_short
                         cform cform_id octx_den octx_probe ictx_den sctx_den nth slot_at slot_ix
                         in_bound in_free out_bound out_free pctx_den pctx_pay noslot pcompose padj_raw pid
                         to_target var_raw bvar bvar0 fvar lvar vdummy vshift_bound vshift_free] in (adj_raw A) in
      let env0 := constr:((@nil label, @nil T, @nil (radj T), @nil (rpadj T))) in
      lazymatch reify_adj_top r env0 with
      | (?e, ?env1) =>
          lazymatch collect_facts env1 (@nil (lexp * lexp)) with
          | ((?le, ?te, ?ae, ?pe), ?F) =>
              let w := eval vm_compute in (lshow F (List.length te) e) in
              lazymatch w with
              | ShWord (WEnd ?S) =>
                  let ts := eval vm_compute in (firstn 1 (mat_targets S)) in
                  lazymatch ts with
                  | _ :: _ =>
                      let te0 := restore_terms te A in
                      mat_render le te0 ae T ts;
                      lazymatch goal with
                      | b0 := ?bv : adj T 0 0 |- _ =>
                      clear b0; let bs := constr:(bv :: nil) in
                      lazymatch mat_reify T bs (le, te, ae, pe) with
                      | (?ebs, (?le2, ?te2, ?ae2, ?pe2)) =>
                          let xs := mat_terms T inst te0 ts bs in
                          let n2 := eval vm_compute in (List.length te2) in
                          let teall := eval cbn [List.app] in (te2 ++ xs) in
                          let te0all := let t2 := restore_terms te2 A in eval cbn [List.app] in (t2 ++ xs) in
                          let rep := eval vm_compute in (mat_rep n2 ts) in
                          let facts := eval vm_compute in (mat_facts n2 ts ebs) in
                          let S' := eval vm_compute in (smat_apply rep S) in
                          let nall := eval vm_compute in (List.length teall) in
                          let d := eval vm_compute in (display_nf F nall (Some (WEnd S'))) in
                          lazymatch d with
                          | Some ?ps =>
                              let bb := fresh "b" in
                              unshelve evar (bb : adj T N 0); [render_pieces le2 te0all ae2 ps|];
                              let A' := eval cbv delta [bb] in bb in
                              clear bb;
                              let r' := eval cbn [adj_raw identity compose at_scope
                                                  cnil cent cbnd csub csubb
                                                  cnil_full cnil_short cent_full cent_short cbnd_full cbnd_short
                                                  csub_full csub_short csubb_full csubb_short
                                                  cform cform_id octx_den octx_probe ictx_den sctx_den nth slot_at slot_ix
                                                  in_bound in_free out_bound out_free pctx_den pctx_pay noslot pcompose padj_raw pid
                                                  to_target var_raw bvar bvar0 fvar lvar vdummy vshift_bound vshift_free] in (adj_raw A') in
                              lazymatch reify_adj_top r' (le2, teall, ae2, pe2) with
                              | (?e', (?le3, ?te3, ?ae3, ?pe3)) =>
                                  lazymatch collect_facts (le3, te3, ae3, pe3) (@nil (lexp * lexp)) with
                                  | ((?le4, ?te4, ?ae4, ?pe4), ?F4) =>
                                      let H := fresh "H" in
                                      assert (H : forall v : var N, mrel (@sm_g _ inst) (rapply (adj_raw A) (var_raw v)) (rapply (adj_raw A') (var_raw v)));
                                      [ intros v;
                                        change (mrel (@sm_g _ inst) (rapply (aeden le4 te4 ae4 pe4 e) (var_raw v)) (rapply (aeden le4 te4 ae4 pe4 e') (var_raw v)));
                                        let HF := fresh "HF" in
                                        assert (HF : facts_ok le4 F4) by (apply order_of_ok; unfold lfacts_ok; repeat constructor; cbn [lden N.to_nat Pos.to_nat Pos.iter_op Nat.add nth]; assumption);
                                        let HM := fresh "HM" in
                                        assert (HM : Forall (fun f => let '(k, u, eb) := f in forall y, nth_error te4 u = Some y -> nth_error te4 k = Some (@sm_g _ inst (rpcompose (aeden le4 te4 ae4 pe4 eb) rpidentity) y)) facts)
                                          by (mat_prove_facts inst te4 ts bs);
                                        refine (lmat_sound le4 te4 ae4 pe4 F4 HF (List.length te4) (le_n _) (@sm_g _ inst) facts HM e e' _ (var_raw v));
                                        vm_compute; reflexivity
                                      | let E := fresh "E" in
                                        pose proof (@sm_mat _ inst N A A' H) as E; clear H;
                                        let f := eval hnf in (@sm_subst _ inst N 0 A) in
                                        let f' := eval hnf in (@sm_subst _ inst N 0 A') in
                                        change (forall t, f t = f' t) in E; cbv beta in E;
                                        progress rewrite E; clear E ]
                                  end
                              end
                          end
                      end
                      end
                  end
              end
          end
      end
  end.

Ltac names_mat :=
  repeat match goal with
         | |- context [?a] => is_adj_expr a; names_mat_one a
         end.

Ltac names_pass :=
  repeat progress (autorewrite with names_pre; cbn [ext_shift]);
  autorewrite with names_var;
  names_adjs; try names_mat; names_apply; names_eval;
  autorewrite with names_post.

Ltac names := repeat progress names_pass.
