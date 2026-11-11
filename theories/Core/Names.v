(** * The [names] tactic

    [names] proves an equation between adjustments [adj T N M] built from
    context forms (full [⟦ I \ O ⟧], [⟦ I | Γ \ O | Γ[σ] ⟧] and short
    [⟦ I; σ ⟧], and so [lift] and [lift_free]), [∘], [⟦⟧] and [at_scope],
    with any other adjustment as an atom.  Labels may be concrete strings or variables;
    the order between label variables comes from hypotheses [label_lt x y]
    in the context ([label_compare] provides them by case analysis).

    The goal is taken to the raw layer, reified into [aexp], both sides are
    normalised
    (Normalise.v), and the normal forms compared.  The tactic fails when
    the normal forms differ, or when normalisation needed the order
    between two labels and no hypothesis gave it. *)

From Stdlib Require Import List String Arith Bool StrictProp.
Open Scope bool_scope.
From ShiftedNames.Core Require Import Label Var Adjustment Indexed Syntax Normalise.
Import ListNotations.

(** ** Reification *)

(** The position of [x] in the list [l], up to conversion, adding it at
    the end if absent; returns the index and the new list. *)
Ltac lookup_add x l :=
  let rec go l n :=
    lazymatch l with
    | nil => constr:((n, false))
    | ?y :: ?r =>
        match constr:(tt) with
        | _ => let _ := constr:(@eq_refl _ x : x = y) in constr:((n, true))
        | _ => go r (S n)
        end
    end in
  lazymatch go l O with
  | (?n, true) => constr:((n, l))
  | (?n, false) => let l' := eval cbv [app] in (l ++ [x]) in constr:((n, l'))
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
                 | (?n, ?le') => constr:((LAtom n, (le', te, ae, pe)))
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
Ltac collect_facts env F :=
  match goal with
  | H : label_lt ?x ?y |- _ =>
      lazymatch reify_label (Some x) env with
      | (?ex, ?env1) =>
          lazymatch reify_label (Some y) env1 with
          | (?ey, ?env2) =>
              let f := constr:((ex, ey)) in
              lazymatch F with
              | context [f] => fail
              | _ => collect_facts env2 (f :: F)
              end
          end
      end
  | _ => constr:((env, F))
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
  end.

Section Split.

Variable F : list (lexp * lexp).
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
  if sdistb F S then
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
  else None
  else None.

End Split.

(** *** Terms before atoms

    The normaliser carries a term substituted before an atom past it: the
    input is passed around the atom, and the term sits in the last
    segment with the atom in its payload.  For display the term is moved
    back: it goes to the input passed around the atom, the atom comes off
    the front of its payload, and the atom loses a lift.  So
    [⟦ x := u ⟧ ⨾ σ] is shown as that, not as [⟦ x | σ ⟧ ⨾ ⟦ x := u⟨σ⟩ ⟧].
    The result is checked like any display. *)

Section Unpass.

Variable F : list (lexp * lexp).
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
      end
  end.

End Unpass.

Definition lift_list (L : list (lexp * nat)) : list lexp := rev (flat_map (fun '(h, n) => repeat h n) L).

Fixpoint display_items (F : list (lexp * lexp)) (ntm : nat) (items : list gitem) : option (list dpiece) :=
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

Definition display_nf (F : list (lexp * lexp)) (ntm : nat) (r : option word) : option (list dpiece) :=
  match r with
  | Some w => option_map (map short_or_full) (display_items F ntm (witems (unpass F ntm 64 w)))
  | None => None
  end.

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
  | (u', wp', k) :: r => if Nat.eqb u u' && word_eqb wp wp' then Some k else mat_lookup r u wp
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
  | LAtom ?n => lnth le n
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

Ltac names_decide :=
  lazymatch goal with
  | |- @eq (radj ?T) ?lhs ?rhs =>
      let env0 := constr:((@nil label, @nil T, @nil (radj T), @nil (rpadj T))) in
      lazymatch reify_adj_top lhs env0 with
      | (?e1, ?env1) =>
          lazymatch reify_adj_top rhs env1 with
          | (?e2, ?env2) =>
              lazymatch collect_facts env2 (@nil (lexp * lexp)) with
              | ((?le, ?te, ?ae, ?pe), ?F) =>
                  change (aeden le te ae pe e1 = aeden le te ae pe e2);
                  refine (nf_eq_sound le te ae pe F _ (List.length te) (le_n _) e1 e2 _);
                  [ lazymatch goal with
                    | |- facts_ok _ _ => unfold facts_ok; repeat constructor; cbn [lden nth]; assumption
                    | |- nf_eq _ _ _ _ = true =>
                        vm_compute; first
                          [ reflexivity
                          | fail 2 "names: the two sides have different normal forms, or a label order is missing" ]
                    end .. ]
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

(** Proving two adjustments equal by comparing their normal forms. *)
Ltac names_eq := apply adj_eq; names_unfold; names_decide.

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

(** Rewriting one adjustment to its normal form, shown as context forms;
    fails when it is already shown that way, or cannot be shown. *)
Ltac names_rewrite a :=
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
              let d := eval vm_compute in (display_nf F (List.length te) (anorm F (List.length te) e)) in
              lazymatch d with
              | Some ?ps =>
                  let te' := restore_terms te a in
                  let bb := fresh "b" in
                  unshelve evar (bb : ty); [render_pieces le te' ae ps|];
                  let b := eval cbv delta [bb] in bb in
                  clear bb;
                  tryif constr_eq a b then fail
                  else (let E := fresh "E" in assert (E : a = b) by names_eq; rewrite E; clear E)
              end
          end
      end
  end.

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
                  | ((?le, ?te, ?ae, ?pe), ?F) =>
                      let res := eval vm_compute in (apply_result F (List.length te) e eh i) in
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
                                refine (apply_result_sound le te ae pe F _ (List.length te) (le_n _) e eh i h' j _);
                                [ unfold facts_ok; repeat constructor; cbn [lden nth]; assumption
                                | vm_compute; reflexivity ])
                      | None =>
                          let pr := eval vm_compute in (apply_payload F (List.length te) e eh i) in
                          lazymatch pr with
                          | Some (?u, ?wp) =>
                              let d := eval vm_compute in (display_nf F (List.length te) (Some wp)) in
                              lazymatch d with
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
                                      | ((?le3, ?te3, ?ae3, ?pe3), ?F3) =>
                                          let x := lnth te' u in
                                          assert (E : apply_var a v = Bind x (pcompose b pid))
                                            by (apply apply_var_bind; names_unfold;
                                                change (rapply (aeden le3 te3 ae3 pe3 e) (mk_rvar (lden le3 eh) i)
                                                        = inr (x, rpcompose (aeden le3 te3 ae3 pe3 eb) rpidentity));
                                                refine (apply_bind_sound le3 te3 ae3 pe3 F3 _ (List.length te3) (le_n _) e eh i eb u x _ _);
                                                [ unfold facts_ok; repeat constructor; cbn [lden nth]; assumption
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

Ltac names_adjs :=
  repeat match goal with
         | |- context [?a] => is_adj_expr a; names_rewrite a
         end.

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
      let F0 := constr:(@nil (lexp * lexp)) in
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
              let w := eval vm_compute in (anorm F (List.length te) e) in
              lazymatch w with
              | Some (WEnd ?S) =>
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
                                        assert (HF : facts_ok le4 F4) by (unfold facts_ok; repeat constructor; cbn [lden nth]; assumption);
                                        let HM := fresh "HM" in
                                        assert (HM : Forall (fun f => let '(k, u, eb) := f in forall y, nth_error te4 u = Some y -> nth_error te4 k = Some (@sm_g _ inst (rpcompose (aeden le4 te4 ae4 pe4 eb) rpidentity) y)) facts)
                                          by (mat_prove_facts inst te4 ts bs);
                                        refine (mat_sound le4 te4 ae4 pe4 F4 HF (List.length te4) (le_n _) (@sm_g _ inst) facts HM e e' _ (var_raw v));
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
