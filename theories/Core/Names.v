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
From ShiftedNames.Core Require Import Label Var Adjustment Indexed Normalise.
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

(** The label order facts in the context, as pairs of label expressions. *)
Ltac collect_facts env F :=
  match goal with
  | H : label_lt ?x ?y |- _ =>
      lazymatch env with
      | (?le, ?te, ?ae, ?pe) =>
          let px := lookup_add x le in
          lazymatch px with
          | (?nx, ?le1) =>
              let py := lookup_add y le1 in
              lazymatch py with
              | (?ny, ?le2) =>
                  let f := constr:((LAtom nx, LAtom ny)) in
                  lazymatch F with
                  | context [f] => fail
                  | _ => collect_facts (le2, te, ae, pe) (f :: F)
                  end
              end
          end
      end
  | _ => constr:((env, F))
  end.

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
| DFull (outs : list dout) (ins : list din) (tail : option nat)
| DShort (es : list sent) (tail : option nat)
| DLift (hs : list lexp) (a : nat).

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

Definition short_or_full (d : dpiece) : dpiece :=
  match d with
  | DFull os is t => match shorten os is with Some es => DShort es t | None => d end
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

Definition display_seg (Sg : seg) (tail : option nat) : option dpiece :=
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

Fixpoint display (w : word) : option (list dpiece) :=
  match w with
  | WEnd SNil => Some []
  | WEnd Sg => match display_seg Sg None with Some d => Some [d] | None => None end
  | WAtom Sg L a w =>
      let lift := DLift (rev (flat_map (fun '(h, n) => repeat h n) L)) a in
      match display w with
      | None => None
      | Some ds =>
          match Sg with
          | SNil => Some (lift :: ds)
          | _ =>
              match display_seg Sg (Some a) with
              | Some (DFull os is _) =>
                  if merges is L then Some (DFull os is (Some a) :: ds)
                  else match display_seg Sg None with Some d => Some (d :: lift :: ds) | None => None end
              | _ => None
              end
          end
      end
  end.

Definition display_nf (r : option word) : option (list dpiece) :=
  match r with Some w => option_map (map short_or_full) (display w) | None => None end.

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

Ltac render_piece le te ae p :=
  lazymatch p with
  | DFull ?os ?is None =>
      refine (cform_id _);
      lazymatch goal with |- @octx _ ?K _ _ _ _ _ _ _ _ => render_outs le te os is (@nil ((lexp * nat) * slot K)) tt end
  | DFull ?os ?is (Some ?n) =>
      let s := atom ae n in let g := fresh "Γ" in
      refine (cform (fun g => _) s);
      lazymatch goal with |- @octx _ ?K _ _ _ _ _ _ _ _ => render_outs le te os is (@nil ((lexp * nat) * slot K)) g end
  | DLift nil ?n => let s := atom ae n in exact s
  | DLift ?hs ?n => let s := atom ae n in refine (cform_id (OShortT (Nt:=0) (STail _ s))); render_lifts le hs
  | DShort ?es None => refine (cform_id (OShort _)); render_short le te es
  | DShort ?es (Some ?n) =>
      let s := atom ae n in refine (cform_id (OShortT (Nt:=0) (STail _ s))); render_short le te es
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
              let d := eval vm_compute in (display_nf (anorm F (List.length te) e)) in
              lazymatch d with
              | Some ?ps =>
                  let bb := fresh "b" in
                  unshelve evar (bb : ty); [render_pieces le te ae ps|];
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
Ltac names_apply_var t :=
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
                          let E := fresh "E" in
                          assert (E : apply_var a v = Rename w);
                          [ apply apply_var_rename; names_unfold;
                            change (rapply (aeden le te ae pe e) (mk_rvar (lden le eh) i)
                                    = inl (mk_rvar (lden le h') j));
                            refine (apply_result_sound le te ae pe F _ (List.length te) (le_n _) e eh i h' j _);
                            [ unfold facts_ok; repeat constructor; cbn [lden nth]; assumption
                            | vm_compute; reflexivity ] .. 
                          | rewrite E; clear E ]
                      end
                  end
              end
          end
      end
  end.

(** Every adjustment in the goal built from context forms and [∘] is
    rewritten to its normal form, shown as context forms, and then every
    [apply_var a v] whose result the normal form of [a] gives. *)
Ltac names_adjs :=
  repeat match goal with
         | |- context [?a] => is_adj_expr a; names_rewrite a
         end.

Ltac names_apply :=
  repeat match goal with
         | |- context [?t] => lazymatch t with apply_var _ _ => names_apply_var t end
         end.

(** [names] rewrites with the [names] database (the laws of substitution,
    and whatever a syntax adds) and normalises adjustments and applications
    of adjustments to variables, until nothing changes. *)
Ltac names :=
  repeat progress (try autorewrite with names; names_adjs; names_apply).
