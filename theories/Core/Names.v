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
    normal form is computed by [HNorm] and shown ([HDisplay]): shared
    definitions and an expression, which are rendered as [share]s and
    context forms.  The rewrite [a = b] to the rendered form is proved by
    [HShow.hshow_sound]: the expression [b] unfolds to is the one shown,
    and it means [a]; nothing is normalised again.

    The tactic is written in Ltac2 ([names] is also an Ltac1 tactic, for
    Ltac1 proofs).  Its cost grows linearly with the adjustment, apart
    from what the normaliser and the display do:
    - the raw layer is unfolded one head at a time as the reifier goes,
      so terms and atoms are left as written;
    - environments are maps and arrays; an atom that is not a variable is
      compared up to conversion only with entries it could be convertible
      to;
    - indices are passed to and read back from [vm_compute] in binary;
    - rendering happens in a goal holding only what the types need, with
      placeholders for labels, terms and atoms (creating an evar costs
      time in the size of its context);
    - proof terms are built directly, checked by the kernel at [Qed];
    - a normal form [names] has produced is not normalised again. *)

From Stdlib Require Import NArith List String Arith Bool StrictProp.
Open Scope bool_scope.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Indexed Syntax Normalise HConcrete HShow.
From ShiftedNames.Core Require HNorm.
Import ListNotations.

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


Lemma share_intro_r {T N M K L} (a : adj T N M) (A : adj T K L) (f : adj T K L -> adj T N M) :
  (forall r, adj_raw r = adj_raw A -> a = f r) -> a = Indexed.share A f.
Proof. intros H; rewrite share_eq; apply H; reflexivity. Qed.

Lemma share_intro_p {T N M K L} (A : adj T K L) (f : adj T K L -> adj T N M) (P : adj T N M -> Prop) :
  (forall r, adj_raw r = adj_raw A -> P (f r)) -> P (Indexed.share A f).
Proof. intros H; rewrite share_eq; apply H; reflexivity. Qed.

(** A use of a shared definition, as the reifier marks it: [A] itself,
    with the atom [k] that stands for it. *)
Definition sref {T K L} (A : adj T K L) (k : nat) : adj T K L := A.

Lemma lfacts_nil le : lfacts_ok le [].
Proof. constructor. Qed.

Lemma lfacts_cons le x y l : olabel_lt (lden le x) (lden le y) -> lfacts_ok le l -> lfacts_ok le ((x, y) :: l).
Proof. intros H Hl; constructor; assumption. Qed.

Lemma nth_hk {A} (l : list A) u k (f : A -> A) ut :
  nth_error l u = Some ut -> nth_error l k = Some (f ut) -> forall y, nth_error l u = Some y -> nth_error l k = Some (f y).
Proof. intros H1 H2 y Hy; rewrite H1 in Hy; injection Hy as <-; exact H2. Qed.

(** ** Ltac2 *)

From Ltac2 Require Import Ltac2.

(** ** Tables *)

(** Entries in order of first occurrence (kept latest first); entries
    that are variables, or a raw adjustment of a variable, are also kept
    by name. *)
Ltac2 Type tbl := { mutable items : constr list; mutable size : int; mutable vars : (ident, int) FMap.t;
                    mutable flex : (constr * int) list }.

Ltac2 new_tbl () : tbl := { items := []; size := 0; vars := FMap.empty FSet.Tags.ident_tag; flex := [] }.

Ltac2 is_raw (f : constr) : bool :=
  match Constr.Unsafe.kind f with
  | Constr.Unsafe.Constant _ _ =>
      Bool.or (Constr.equal f constr:(@adj_raw)) (Constr.equal f constr:(@padj_raw))
  | _ => false
  end.

Ltac2 key_of (x : constr) : ident option :=
  match Constr.Unsafe.kind x with
  | Constr.Unsafe.Var id => Some id
  | Constr.Unsafe.App f args =>
      let n := Array.length args in
      if Int.equal n 0 then None else
      match Constr.Unsafe.kind (Array.get args (Int.sub n 1)) with
      | Constr.Unsafe.Var id => if is_raw f then Some id else None
      | _ => None
      end
  | Constr.Unsafe.Proj _ _ c =>
      match Constr.Unsafe.kind c with Constr.Unsafe.Var id => Some id | _ => None end
  | _ => None
  end.

Ltac2 conv (x : constr) (y : constr) : bool :=
  Control.plus (fun () => Unification.unify_with_current_ts x y; true) (fun _ => false).

Ltac2 rec find_idx (p : constr -> bool) (l : constr list) (i : int) : int option :=
  match l with
  | [] => None
  | y :: r => if p y then Some i else find_idx p r (Int.add i 1)
  end.

Ltac2 tbl_push (t : tbl) (x : constr) : int :=
  let i := (t.(size)) in
  t.(items) := x :: (t.(items));
  t.(size) := Int.add i 1;
  i.

(** A term built from variables without definitions, constructors and
    literals is normal: it is convertible to another such term only when
    equal to it.  So such a term needs comparing up to conversion only
    with the entries that are not ([flex]). *)
Ltac2 rec rigid (lets : ident FSet.t) (x : constr) : bool :=
  match Constr.Unsafe.kind x with
  | Constr.Unsafe.Var id => Bool.neg (FSet.mem id lets)
  | Constr.Unsafe.Constructor _ _ => true
  | Constr.Unsafe.Ind _ _ => true
  | Constr.Unsafe.Sort _ => true
  | Constr.Unsafe.Uint63 _ => true
  | Constr.Unsafe.Float _ => true
  | Constr.Unsafe.String _ => true
  | Constr.Unsafe.App f args =>
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Var _ => Bool.and (rigid lets f) (Array.for_all (rigid lets) args)
      | Constr.Unsafe.Constructor _ _ => Array.for_all (rigid lets) args
      | Constr.Unsafe.Ind _ _ => Array.for_all (rigid lets) args
      | _ => false
      end
  | _ => false
  end.

Ltac2 rec find_conv (x : constr) (l : (constr * int) list) : int option :=
  match l with
  | [] => None
  | (y, i) :: r => if conv x y then Some i else find_conv x r
  end.

Ltac2 tbl_add (lets : ident FSet.t) (t : tbl) (x : constr) : int :=
  match key_of x with
  | Some id =>
      match FMap.find_opt id (t.(vars)) with
      | Some i => i
      | None => let i := tbl_push t x in t.(vars) := FMap.add id i (t.(vars)); i
      end
  | None =>
      let l := List.rev (t.(items)) in
      match find_idx (Constr.equal x) l 0 with
      | Some i => i
      | None =>
          let r := rigid lets x in
          let cands := if r then List.rev (t.(flex)) else List.combine l (List.init (List.length l) (fun i => i)) in
          match find_conv x cands with
          | Some i => i
          | None =>
              let i := tbl_push t x in
              (if r then () else t.(flex) := ((x, i) :: (t.(flex))));
              i
          end
      end
  end.

Ltac2 app (f : constr) (args : constr list) : constr := Constr.Unsafe.make (Constr.Unsafe.App f (Array.of_list args)).

(** ** Literals *)

Ltac2 Type nats := { mutable lits : constr array; mutable nlits : int }.

Ltac2 new_nats () : nats := { lits := Array.make 1 constr:(O); nlits := 1 }.

(** [i] as a [nat] numeral, numerals shared. *)
Ltac2 nat_lit (ns : nats) (i : int) : constr :=
  (if Int.lt i (ns.(nlits)) then () else
   let n := Int.add i 1 in
   let a := Array.make n constr:(O) in
   Array.blit (ns.(lits)) 0 a 0 (ns.(nlits));
   let s := constr:(S) in
   let rec fill k :=
     if Int.lt k n then
       (Array.set a k (Constr.Unsafe.make (Constr.Unsafe.App s [| Array.get a (Int.sub k 1) |])); fill (Int.add k 1))
     else () in
   fill (ns.(nlits));
   ns.(lits) := a; ns.(nlits) := n);
  Array.get (ns.(lits)) i.

Ltac2 rec pos_lit (i : int) : constr :=
  if Int.equal i 1 then constr:(xH)
  else let p := pos_lit (Int.div i 2) in
       if Int.equal (Int.mod i 2) 0 then constr:(xO $p) else constr:(xI $p).

Ltac2 n_lit (i : int) : constr :=
  if Int.equal i 0 then constr:(N0) else let p := pos_lit i in app constr:(Npos) [p].

Ltac2 rec int_of_pos (p : constr) : int :=
  lazy_match! p with
  | xH => 1
  | xO ?q => Int.mul 2 (int_of_pos q)
  | xI ?q => Int.add 1 (Int.mul 2 (int_of_pos q))
  end.

Ltac2 int_of_n (n : constr) : int :=
  lazy_match! n with
  | N0 => 0
  | Npos ?p => int_of_pos p
  end.

Ltac2 int_of_nat (n : constr) : int :=
  let s := constr:(S) in
  let rec go n acc :=
    match Constr.Unsafe.kind n with
    | Constr.Unsafe.App f args => if Constr.equal f s then go (Array.get args 0) (Int.add acc 1) else Control.zero Not_found
    | Constr.Unsafe.Constructor _ _ => acc
    | _ => Control.zero Not_found
    end in
  go n 0.

(** An index as [idx] writes it. *)
Ltac2 int_of_idx (n : constr) : int :=
  match Constr.Unsafe.kind n with
  | Constr.Unsafe.App f args =>
      if Constr.equal f constr:(N.to_nat) then int_of_n (Array.get args 0) else int_of_nat n
  | _ => int_of_nat n
  end.

Ltac2 rec is_nat_lit (n : constr) : bool :=
  lazy_match! n with
  | O => true
  | S ?m => is_nat_lit m
  | _ => false
  end.

Ltac2 rec is_string_lit (s : constr) : bool :=
  lazy_match! s with
  | EmptyString => true
  | String _ ?r => is_string_lit r
  | _ => false
  end.

(** ** Reification *)

(** Context forms and the rest of the indexed layer are unfolded one
    head at a time, as the reifier goes: what is not unfolded (terms, and
    atoms) is kept as written. *)
Ltac2 raw_refs () : Std.reference list := [reference:(adj_raw); reference:(identity); reference:(compose); reference:(at_scope); reference:(cnil); reference:(cent); reference:(cbnd); reference:(csub); reference:(csubb); reference:(cren); reference:(crenb); reference:(cnil_full); reference:(cnil_short); reference:(cent_full); reference:(cent_short); reference:(cbnd_full); reference:(cbnd_short); reference:(csub_full); reference:(csub_short); reference:(csubb_full); reference:(csubb_short); reference:(cren_full); reference:(cren_short); reference:(crenb_full); reference:(crenb_short); reference:(cform); reference:(cform_id); reference:(octx_den); reference:(octx_probe); reference:(ictx_den); reference:(sctx_den); reference:(nth); reference:(slot_at); reference:(slot_ix); reference:(in_bound); reference:(in_free); reference:(out_bound); reference:(out_free); reference:(in_look_free); reference:(in_look_bound); reference:(pctx_den); reference:(pctx_pay); reference:(noslot); reference:(pcompose); reference:(padj_raw); reference:(pid); reference:(to_target); reference:(var_raw); reference:(bvar); reference:(bvar0); reference:(fvar); reference:(lvar); reference:(vdummy); reference:(vshift_bound); reference:(vshift_free)].

(** An index in the input: small ones as numerals, others as
    [N.to_nat] of a binary numeral, so that the input stays small. *)
Ltac2 idx (ns : nats) (k : int) : constr :=
  if Int.lt k 16 then nat_lit ns k else app constr:(N.to_nat) [n_lit k].

Ltac2 adj_args (ty : constr) (xs : constr list) : constr list :=
  lazy_match! ty with adj ?t ?k ?l => t :: k :: l :: xs end.

Ltac2 Type st := { labs : tbl; terms : tbl; atoms : tbl; patoms : tbl; ns : nats; lets : ident FSet.t;
                   wfl : Std.red_flags; nfl : Std.red_flags; mutable sdefs : (int, constr) FMap.t }.

Ltac2 new_st () : st :=
  let refs := raw_refs () in
  { labs := new_tbl (); terms := new_tbl (); atoms := new_tbl (); patoms := new_tbl (); ns := new_nats ();
    lets := List.fold_left (fun acc (id, b, _) => match b with Some _ => FSet.add id acc | None => acc end)
              (FSet.empty FSet.Tags.ident_tag) (Control.hyps ());
    wfl := { Std.rStrength := Std.Head; Std.rBeta := true; Std.rMatch := true; Std.rFix := true;
             Std.rCofix := true; Std.rZeta := true; Std.rDelta := false; Std.rConst := refs };
    nfl := { Std.rStrength := Std.Norm; Std.rBeta := true; Std.rMatch := true; Std.rFix := true;
             Std.rCofix := true; Std.rZeta := true; Std.rDelta := false; Std.rConst := refs };
    sdefs := FMap.empty FSet.Tags.int_tag }.

Ltac2 whd_s (s : st) (c : constr) : constr := Std.eval_cbn (s.(wfl)) c.

Ltac2 nf_s (s : st) (c : constr) : constr := Std.eval_cbv (s.(nfl)) c.

Ltac2 reify_lab (s : st) (x : constr) : constr :=
  if is_string_lit x then app constr:(LCon) [x]
  else let n := n_lit (tbl_add (s.(lets)) (s.(labs)) x) in app constr:(LAtom) [n].

Ltac2 reify_label (s : st) (h : constr) : constr :=
  lazy_match! whd_s s h with
  | None => constr:(LNone)
  | Some ?x => reify_lab s x
  end.

Ltac2 reify_atom (s : st) (a : constr) : constr :=
  let n := idx (s.(ns)) (tbl_add (s.(lets)) (s.(atoms)) a) in app constr:(AAtom) [n].

Ltac2 rec reify_adj (s : st) (a : constr) : constr :=
  let a := whd_s s a in
  lazy_match! a with
  | ridentity => constr:(AId)
  | rcompose ?x ?y =>
      let ex := reify_adj s x in let ey := reify_adj s y in app constr:(ACompose) [ex; ey]
  | rpush_outer ?h ?x =>
      let eh := reify_label s h in let ex := reify_adj s x in app constr:(AOuter) [eh; ex]
  | rpush_inner ?h ?t ?x =>
      let eh := reify_label s h in
      match reify_target s t with
      | Some et => let ex := reify_adj s x in app constr:(AInner) [eh; et; ex]
      | None => reify_atom s a
      end
  | rlift ?h ?x =>
      let eh := reify_label s h in let ex := reify_adj s x in app constr:(ALift) [eh; ex]
  | adj_raw ?sh =>
      lazy_match! sh with
      | Indexed.share ?aa ?f =>
          (* the definition, as a new atom standing for it, and the body with a
             marked use of it for the bound variable *)
          let araw := app constr:(@adj_raw) (adj_args (Constr.type aa) [aa]) in
          let d := reify_adj s araw in
          let k := tbl_push (s.(atoms)) araw in
          s.(sdefs) := FMap.add k d (s.(sdefs));
          let marker := app constr:(@sref) (adj_args (Constr.type aa) [aa; idx (s.(ns)) k]) in
          let body := match Constr.Unsafe.kind f with
                      | Constr.Unsafe.Lambda _ b => Constr.Unsafe.substnl [marker] 0 b
                      | _ => app f [marker]
                      end in
          reify_adj s (app constr:(@adj_raw) (adj_args (Constr.type sh) [body]))
      | sref _ ?k => app constr:(AAtom) [k]
      | _ => reify_atom s a
      end
  | _ => reify_atom s a
  end
with reify_var (s : st) (w : constr) : constr option :=
  lazy_match! whd_s s w with
  | mk_rvar ?h ?i =>
      let i := nf_s s i in
      if is_nat_lit i then let eh := reify_label s h in Some (app constr:(TVarE) [eh; i]) else None
  | shift_rvar ?w0 ?w' =>
      lazy_match! nf_s s w0 with mk_rvar ?h 0 => () | _ => Control.zero Not_found end;
      let h := lazy_match! nf_s s w0 with mk_rvar ?h _ => h end in
      let eh := reify_label s h in
      match reify_var s w' with
      | Some ew => Some (app constr:(TShiftE) [eh; ew])
      | None => None
      end
  | _ => None
  end
with reify_target (s : st) (t : constr) : constr option :=
  lazy_match! whd_s s t with
  | Laws.rapply_target ?a ?w =>
      lazy_match! nf_s s w with
      | RRename (mk_rvar ?h ?i) =>
      if is_nat_lit i then
        let eh := reify_label s h in let ea := reify_adj s a in Some (app constr:(TLookE) [eh; i; ea])
      else None
      | _ => None
      end
  | RRename ?w => reify_var s w
  | RBind ?u ?p =>
      let n := idx (s.(ns)) (tbl_add (s.(lets)) (s.(terms)) u) in
      let ep := reify_padj s p in Some (app constr:(TBindE) [n; ep])
  | _ => None
  end
with reify_padj (s : st) (p : constr) : constr :=
  let p := whd_s s p in
  lazy_match! p with
  | rpidentity => constr:(PId)
  | rpcompose ?x ?q =>
      let ex := reify_adj s x in let eq := reify_padj s q in app constr:(PComp) [ex; eq]
  | rpshift ?h ?q =>
      let eh := reify_label s h in let eq := reify_padj s q in app constr:(PShift) [eh; eq]
  | _ =>
      let n := idx (s.(ns)) (tbl_add (s.(lets)) (s.(patoms)) p) in app constr:(PAtom) [n]
  end.

(** The label order facts in the context, and their proofs, in order. *)
Ltac2 collect_facts (s : st) : (constr * constr * ident) list :=
  List.rev
    (List.fold_left
       (fun acc (id, _, ty) =>
          lazy_match! ty with
          | label_lt ?x ?y => let ex := reify_lab s x in let ey := reify_lab s y in (ex, ey, id) :: acc
          | _ => acc
          end)
       [] (Control.hyps ())).

Ltac2 rec list_of (ty : constr) (l : constr list) : constr :=
  let c := constr:(@cons) in
  let n := Constr.Unsafe.make (Constr.Unsafe.App constr:(@nil) [| ty |]) in
  List.fold_right (fun x acc => Constr.Unsafe.make (Constr.Unsafe.App c [| ty; x; acc |])) l n.

Ltac2 rec of_list (l : constr) : constr list :=
  lazy_match! l with
  | nil => []
  | cons ?x ?r => x :: of_list r
  end.

(** ** Rendering

    A shown normal form, shared definitions and an expression, as
    [share]s and context forms, solving the goal [adj T N M]:
    - a run of entries as a short form over its tail, lifts first:
      [x := u], [x := u⟨| r ⟩], [x as w], [x as w⟨| r ⟩];
    - [x ↦ g₀] over a pop of [g] as [⟦ x | Γ \ g | Γ[σ] ⟧] (a lift when
      [x = g]);
    - pops alone as outputs [⟦ \ y as _ ⟧];
    - composition as [⨾], atoms as written, shared definitions as the
      variables [share] binds. *)

(** The rendering is done in a goal whose context holds only what the
    types need, with labels, terms and atoms as the placeholders
    [phl n], [pht n] and [pha A B n] (an atom of type [adj T A B]), so
    that its cost does not grow with the context; the placeholders are
    then replaced.  Shared definitions are rendered separately, their uses
    as placeholders too, and bound by [share] at the end. *)
Ltac2 Type rst := { phl : constr; pht : constr; pha : constr; atys : (constr * constr) array; rnb : int;
                    mutable shtys : (int, constr * constr) FMap.t }.

Ltac2 refine_c (c : unit -> constr) : unit := Control.refine c; Control.shelve_unifiable ().

Ltac2 intro_as (id : ident) : unit := Std.intros false [Std.IntroNaming (Std.IntroIdentifier id)].

Ltac2 fresh (base : ident) : ident := Fresh.in_goal base.

Ltac2 last_hyp () : ident := let (id, _, _) := List.last (Control.hyps ()) in id.

Ltac2 lab_env (labs : constr array) (h : constr) : constr :=
  lazy_match! h with
  | LCon ?s => s
  | LAtom ?n => Array.get labs (int_of_n n)
  end.

Ltac2 lab (r : rst) (h : constr) : constr :=
  lazy_match! h with
  | LCon ?s => s
  | LAtom ?n => app (r.(phl)) [n]
  end.

Ltac2 is_lnone (h : constr) : bool := lazy_match! h with LNone => true | _ => false end.

Ltac2 rvar (r : rst) (g : constr) (j : constr) : unit :=
  if is_lnone g then
    lazy_match! goal with [ |- var ?m ] => refine_c (fun () => '(@bvar $m $j stt)) end
  else let gl := lab r g in refine_c (fun () => '(fvar $gl $j)).

Ltac2 rec collect_short (e : constr) (lifts : bool) (acc : (constr * constr option) list) :=
  lazy_match! e with
  | AInner ?x (TVarE ?g 0) (AOuter ?g' ?b) =>
      if Bool.and (Constr.equal g g') (Constr.equal x g) then
        if lifts then collect_short b true ((x, None) :: acc) else (acc, e)
      else if Constr.equal g g' then (acc, e)
      else collect_short b false ((x, Some '(TVarE $g 0)) :: acc)
  | AInner ?x ?t ?b => collect_short b false ((x, Some t) :: acc)
  | _ => (acc, e)
  end.

Ltac2 rec collect_outs (e : constr) (acc : constr list) :=
  lazy_match! e with
  | AOuter ?y ?b => collect_outs b (y :: acc)
  | _ => (acc, e)
  end.

Ltac2 rec render_onames (r : rst) (ys : constr list) (fin : unit -> unit) : unit :=
  match ys with
  | [] => fin ()
  | y :: ys =>
      (if is_lnone y then refine_c (fun () => '(ONamB (fun a => _)))
       else let yl := lab r y in refine_c (fun () => '(ONamF $yl (fun a => _))));
      render_onames r ys fin
  end.

Ltac2 rec render_a (r : rst) (e : constr) : unit :=
  lazy_match! e with
  | AId => refine_c (fun () => '(identity))
  | AAtom ?m =>
      let i := int_of_idx m in
      let (ka, kb) :=
        if Int.lt i (r.(rnb)) then Array.get (r.(atys)) i
        else match FMap.find_opt (Int.sub i (r.(rnb))) (r.(shtys)) with
             | Some t => t
             | None => Control.zero Not_found
             end in
      refine_c (fun () => app (r.(pha)) [ka; kb; n_lit i])
  | ACompose ?x ?y => refine_c (fun () => '(compose _ _)); Control.dispatch [(fun () => render_a r x); (fun () => render_a r y)]
  | AInner ?x (TVarE ?g 0) (AOuter ?g' ?b) =>
      if Bool.and (Constr.equal g g') (Bool.neg (Constr.equal x g)) then render_ren r x g b
      else render_short r e
  | AInner _ _ _ => render_short r e
  | AOuter _ _ =>
      let (ys, tl) := collect_outs e [] in
      lazy_match! tl with
      | AId => refine_c (fun () => '(cform_id _)); render_onames r ys (fun () => refine_c (fun () => '(OEnd IEmpty)))
      | _ =>
          refine_c (fun () => '(cform (fun G => _) _));
          Control.dispatch
            [(fun () => let g := Control.hyp (last_hyp ()) in
                        render_onames r ys (fun () => refine_c (fun () => '(OEndT $g IEmpty))));
             (fun () => render_a r tl)]
      end
  end
with render_short (r : rst) (e : constr) : unit :=
  let (acc, tl) := collect_short e true [] in
  lazy_match! tl with
  | AId => refine_c (fun () => '(cform_id (OShort _))); render_entries r acc
  | _ =>
      refine_c (fun () => '(cform_id (OShortT (Nt:=0) (STail _ _))));
      Control.dispatch [(fun () => render_entries r acc); (fun () => render_a r tl)]
  end
with render_entries (r : rst) (acc : (constr * constr option) list) : unit :=
  match acc with
  | [] => refine_c (fun () => '(SEmpty))
  | (x, t) :: rest =>
      let k := fun () => render_entries r rest in
      let b := is_lnone x in
      match t with
      | None =>
          if b then (refine_c (fun () => '(SLiftB _)); k ())
          else let xl := lab r x in refine_c (fun () => '(SLiftF _ $xl)); k ()
      | Some t =>
          lazy_match! t with
          | TVarE ?g ?j =>
              (if b then refine_c (fun () => '(SRenB _ _))
               else let xl := lab r x in refine_c (fun () => '(SRenF _ $xl _)));
              Control.dispatch [k; (fun () => rvar r g j)]
          | TBindE ?u (PComp AId PId) =>
              let ut := app (r.(pht)) [n_lit (int_of_idx u)] in
              (if b then refine_c (fun () => '(SSubB _ $ut PEmpty))
               else let xl := lab r x in refine_c (fun () => '(SSubF _ $xl $ut PEmpty)));
              k ()
          | TBindE ?u (PComp ?rr PId) =>
              let ut := app (r.(pht)) [n_lit (int_of_idx u)] in
              (if b then refine_c (fun () => '(SSubBA _ $ut _))
               else let xl := lab r x in refine_c (fun () => '(SSubFA _ $xl $ut _)));
              Control.dispatch [k; (fun () => render_a r rr)]
          | TLookE ?g ?j ?rr =>
              (if b then refine_c (fun () => '(SLookB _ _ _))
               else let xl := lab r x in refine_c (fun () => '(SLookF _ $xl _ _)));
              Control.dispatch [k; (fun () => ()); (fun () => render_a r rr)];
              Control.enter (fun () => rvar r g j)
          end
      end
  end
with render_ren (r : rst) (x : constr) (g : constr) (b : constr) : unit :=
  let pos () :=
    if is_lnone g then refine_c (fun () => '(OPosB _))
    else let gl := lab r g in refine_c (fun () => '(OPosF _ $gl)) in
  let inp () :=
    if is_lnone x then refine_c (fun () => '(IPosB IEmpty))
    else let xl := lab r x in refine_c (fun () => '(IPosF IEmpty $xl)) in
  lazy_match! b with
  | AId => refine_c (fun () => '(cform_id _)); pos (); refine_c (fun () => '(OEnd _)); inp ()
  | _ =>
      refine_c (fun () => '(cform (fun G => _) _));
      Control.dispatch
        [(fun () => let gv := Control.hyp (last_hyp ()) in
                    pos (); refine_c (fun () => '(OEndT $gv _)); inp ());
         (fun () => render_a r b)]
  end.

Ltac2 rec fv (c : constr) (acc : ident FSet.t) : ident FSet.t :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var id => FSet.add id acc
  | _ => let r := { contents := acc } in Constr.Unsafe.iter (fun x => r.(contents) := fv x (r.(contents))) c; r.(contents)
  end.

(** The hypotheses [c] needs, with those their types need. *)
Ltac2 needed (cs : constr list) : ident FSet.t :=
  let hyps := Control.hyps () in
  let s := List.fold_left (fun acc c => fv c acc) (FSet.empty FSet.Tags.ident_tag) cs in
  List.fold_right
    (fun (id, body, ty) acc =>
       if FSet.mem id acc then
         let acc := fv ty acc in
         match body with Some b => fv b acc | None => acc end
       else acc)
    hyps s.

(** The placeholders (bound by the outermost three binders, stripped) as
    what they stand for; a shared definition [j] (an atom from [nb]) as
    the [j]th binder from the top. *)
Ltac2 rec subst_ph (labs : constr array) (terms : constr array) (atoms : constr array) (nb : int) (d : int) (c : constr) : constr :=
  let rec_ () := Constr.Unsafe.map_with_binders (fun d _ => Int.add d 1) (subst_ph labs terms atoms nb) d c in
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Rel i =>
          if Int.equal i (Int.add d 3) then Array.get labs (int_of_n (Array.get args 0))
          else if Int.equal i (Int.add d 2) then Array.get terms (int_of_n (Array.get args 0))
          else if Int.equal i (Int.add d 1) then
            let j := int_of_n (Array.get args 2) in
            if Int.lt j nb then Array.get atoms j
            else Constr.Unsafe.make (Constr.Unsafe.Rel (Int.sub d (Int.sub j nb)))
          else rec_ ()
      | _ => rec_ ()
      end
  | _ => rec_ ()
  end.

Ltac2 strip_lam (n : int) (c : constr) : constr :=
  let rec go n c :=
    if Int.equal n 0 then c else
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Lambda _ b => go (Int.sub n 1) b
    | Constr.Unsafe.Cast c _ _ => go n c
    | _ => Control.zero (Tactic_failure (Some (Message.concat (Message.of_string "strip_lam: ") (Message.of_constr c))))
    end in
  go n c.

Ltac2 nocast (c : constr) : constr :=
  match Constr.Unsafe.kind c with Constr.Unsafe.Cast c' _ _ => c' | _ => c end.

Ltac2 adj_idx (ty : constr) : constr * constr :=
  lazy_match! ty with adj _ ?a ?b => (a, b) end.

(** [render_term t ty labs terms atoms nb shd root]: the rendering of
    [shd] and [root], of type [ty] (an [adj t _ _]); [atoms] the raw
    atoms, those below [nb] in [root] and [shd]. *)
Ltac2 render_term (t : constr) (ty : constr) (labs : constr array) (terms : constr array) (atoms : constr array) (nb : int)
    (shd : constr list) (root : constr) : constr :=
  let atoms := Array.map (fun a => lazy_match! a with adj_raw ?s => s end) atoms in
  let atys := Array.map (fun s => adj_idx (Constr.type s)) atoms in
  let keep := (needed (ty :: Array.to_list (Array.map (fun s => Constr.type s) atoms))) in
  let (n, m) := adj_idx ty in
  let sk :=
    constr:(ltac2:(
      let phl := fresh @phl in intro_as phl;
      let pht := fresh @pht in intro_as pht;
      let pha := fresh @pha in intro_as pha;
      let keep := FSet.add phl (FSet.add pht (FSet.add pha keep)) in
      (Std.clear (List.map (fun (id, _, _) => id)
                   (List.filter (fun (id, _, _) => Bool.neg (FSet.mem id keep)) (Control.hyps ()))));
      let r := { phl := Control.hyp phl; pht := Control.hyp pht; pha := Control.hyp pha; atys := atys; rnb := nb;
                 shtys := FMap.empty FSet.Tags.int_tag } in
      let defs := (List.map
          (fun d =>
             let c := nocast open_constr:(ltac2:(render_a r d) : adj $t _ _) in
             let k := r.(shtys) in
             r.(shtys) := FMap.add (FMap.cardinal k) (adj_idx (Constr.type c)) k;
             c)
          shd) in
      let rt := nocast constr:(ltac2:(render_a r root) : $ty) in
      let k := List.length defs in
      let shc := constr:(@Indexed.share) in
      let rec nest i ds :=
        match ds with
        | [] => rt
        | d :: ds =>
            let (a, b) := Option.get (FMap.find_opt i (r.(shtys))) in
            let aty := app constr:(@adj) [t; a; b] in
            app shc [t; n; m; a; b; d;
                     Constr.Unsafe.make (Constr.Unsafe.Lambda (Constr.Binder.make (Some @r) aty) (nest (Int.add i 1) ds))]
        end in
      let tm := (nest 0 defs) in (Std.exact_no_check tm))
      : forall (phl : N -> label) (pht : N -> $t) (pha : forall A B : nat, N -> adj $t A B), $ty) in
  (subst_ph labs terms atoms nb 0 (strip_lam 3 sk)).

(** ** Environments *)

(** What reification gives: the environments as lists, the facts [l]
    with a proof [hl] of [lfacts_ok le l], and the environments' entries. *)
Ltac2 Type env := {
  e_le : constr; e_te : constr; e_ae : constr; e_pe : constr; e_l : constr; e_hl : constr;
  e_labs : constr array; e_terms : constr list; e_atoms : constr array; e_nt : int; e_nb : int; e_ns : nats;
  e_defs : constr; e_defl : constr option list }.

Ltac2 finish (s : st) (ty : constr) : env :=
  let fs := collect_facts s in
  let labs := List.rev ((s.(labs)).(items)) in
  let terms := List.rev ((s.(terms)).(items)) in
  let atoms := List.rev ((s.(atoms)).(items)) in
  let le := list_of constr:(label) labs in
  let te := list_of ty terms in
  let ae := list_of constr:(radj $ty) atoms in
  let pe := list_of constr:(rpadj $ty) (List.rev ((s.(patoms)).(items))) in
  let defl := List.init ((s.(atoms)).(size)) (fun k => FMap.find_opt k (s.(sdefs))) in
  let defl_c := List.map (fun od => match od with
                                   | Some d => app constr:(@Some aexp) [d]
                                   | None => constr:(@None aexp)
                                   end) defl in
  let lt := constr:((lexp * lexp)%type) in
  let pair := constr:(@pair lexp lexp) in
  let cons := constr:(@cons) in
  let lcons := constr:(lfacts_cons) in
  let (hl, l) :=
    List.fold_right
      (fun (x, y, id) (acc, tl) =>
         (app lcons [le; x; y; tl; Control.hyp id; acc], app cons [lt; app pair [x; y]; tl]))
      fs (app constr:(lfacts_nil) [le], app constr:(@nil) [lt]) in
  { e_le := le; e_te := te; e_ae := ae; e_pe := pe; e_l := l; e_hl := hl;
    e_labs := Array.of_list labs; e_terms := terms; e_atoms := Array.of_list atoms;
    e_nt := (s.(terms)).(size); e_nb := (s.(atoms)).(size); e_ns := s.(ns);
    e_defs := list_of constr:(option aexp) defl_c; e_defl := defl }.

(** [eq_refl : lhs = rhs], checked by the VM (when the proof is checked). *)
Ltac2 vm_eq (ty : constr) (lhs : constr) (rhs : constr) : constr :=
  Constr.Unsafe.make
    (Constr.Unsafe.Cast (app constr:(@eq_refl) [ty; rhs]) Constr.Cast.vm (app constr:(@eq) [ty; lhs; rhs])).

(** ** Tactic steps *)

Ltac2 concl () : Std.clause := { Std.on_hyps := Some []; Std.on_concl := Std.AllOccurrences }.

Ltac2 assert_by (id : ident) (t : constr) (tac : unit -> unit) : unit :=
  Std.assert (Std.AssertType (Some (Std.IntroNaming (Std.IntroIdentifier id))) t (Some tac)).

(** Rewriting with [pf : lhs = rhs] where [lhs] occurs as it is in the
    goal: its occurrences are found syntactically ([pattern]), never by
    unifying [lhs] with other terms, which can mean comparing two large
    adjustments by computing them. *)
Ltac2 rewrite_with (pf : constr) : unit :=
  lazy_match! Constr.type pf with
  | @eq ?ty ?lhs ?rhs =>
      Std.pattern [(lhs, Std.AllOccurrences)] (concl ());
      lazy_match! goal with
      | [ |- ?p _ ] =>
          match Constr.Unsafe.kind p with
          | Constr.Unsafe.Lambda _ body =>
              let g := Constr.Unsafe.substnl [rhs] 0 body in
              refine_c (fun () => '(@eq_ind_r $ty $rhs $p _ $lhs $pf));
              Std.change None (fun _ => g) (concl ())
          | _ => Control.zero Not_found
          end
      end
  end.

(** The instances [t] of [pf : forall t, L t = R t] whose [L t] occur in
    the goal, [L t] an application whose last argument is [t]. *)
Ltac2 rec app_instances (h : constr) (args : constr array) (c : constr) (acc : constr list) : constr list :=
  let acc :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App h' args' =>
        let n := Array.length args in
        if Bool.and (Constr.equal h h') (Int.equal (Array.length args') n) then
          let rec same i := if Int.equal i (Int.sub n 1) then true
                            else if Constr.equal (Array.get args i) (Array.get args' i) then same (Int.add i 1) else false in
          let t := Array.get args' (Int.sub n 1) in
          if Bool.and (same 0) (Constr.Unsafe.is_closed t) then (if List.exist (Constr.equal t) acc then acc else t :: acc) else acc
        else acc
    | _ => acc
    end in
  let r := { contents := acc } in
  Constr.Unsafe.iter (fun x => r.(contents) := app_instances h args x (r.(contents))) c;
  r.(contents).

Ltac2 rewrite_all_instances (pf : constr) : unit :=
  match Constr.Unsafe.kind (Constr.type pf) with
  | Constr.Unsafe.Prod _ b =>
      lazy_match! b with
      | _ = _ =>
          let l := match Constr.Unsafe.kind b with Constr.Unsafe.App _ a => Array.get a 1 | _ => Control.zero Not_found end in
          match Constr.Unsafe.kind l with
          | Constr.Unsafe.App h args =>
              let ts := app_instances h args (Control.goal ()) [] in
              List.iter (fun t => rewrite_with (app pf [t])) ts
          | _ => Control.zero Not_found
          end
      end
  | _ => Control.zero Not_found
  end.

(** The shares at the head of the right-hand side of the goal [_ = b] as
    variables, with what each is: their raw forms and hypotheses, in
    order. *)
Ltac2 rec intro_shares (rs : constr list) (hs : ident list) : constr list * ident list :=
  lazy_match! goal with
  | [ |- _ = Indexed.share ?aa ?f ] =>
      refine_c (fun () => '(share_intro_r _ $aa $f _));
      let r := fresh @r in intro_as r;
      let h := fresh @Hr in intro_as h;
      Std.cbv { Std.rStrength := Std.Norm; Std.rBeta := true; Std.rMatch := false; Std.rFix := false;
                Std.rCofix := false; Std.rZeta := false; Std.rDelta := false; Std.rConst := [] } (concl ());
      let rv := Control.hyp r in intro_shares (List.append rs ['(adj_raw $rv)]) (List.append hs [h])
  | [ |- _ ] => (rs, hs)
  end.

(** The same for the shares at the head of [t], wherever it is in the goal. *)
Ltac2 rec intro_shares_t (t : constr) (rs : constr list) (hs : ident list) : constr list * ident list :=
  lazy_match! t with
  | Indexed.share ?aa ?f =>
      Std.pattern [(t, Std.AllOccurrences)] (concl ());
      refine_c (fun () => '(share_intro_p $aa $f _ _));
      let r := fresh @r in intro_as r;
      let h := fresh @Hr in intro_as h;
      let rv := Control.hyp r in
      let t' := eval cbv beta in ($f $rv) in
      Std.cbv { Std.rStrength := Std.Norm; Std.rBeta := true; Std.rMatch := false; Std.rFix := false;
                Std.rCofix := false; Std.rZeta := false; Std.rDelta := false; Std.rConst := [] } (concl ());
      intro_shares_t t' (List.append rs ['(adj_raw $rv)]) (List.append hs [h])
  | _ => (rs, hs)
  end.

(** [Forall2 (fun x d => x = aeden d) rs sh] from the share hypotheses. *)
Ltac2 rec shares_ok (hs : ident list) : unit :=
  match hs with
  | [] => refine_c (fun () => '(@Forall2_nil _ _ _))
  | h :: hs =>
      refine_c (fun () => '(@Forall2_cons _ _ _ _ _ _ _ _ _));
      Control.dispatch [(fun () => Std.exact_no_check (Control.hyp h)); (fun () => shares_ok hs)]
  end.

(** ** Reading results back *)

Ltac2 rec dec_a (ns : nats) (e : constr) : constr :=
  lazy_match! e with
  | NId => constr:(AId)
  | NAtom ?n => app constr:(AAtom) [idx ns (int_of_n n)]
  | NCompose ?a ?b => let a := dec_a ns a in let b := dec_a ns b in app constr:(ACompose) [a; b]
  | NOuter ?h ?a => app constr:(AOuter) [h; dec_a ns a]
  | NInner ?h ?t ?a => let t := dec_t ns t in let a := dec_a ns a in app constr:(AInner) [h; t; a]
  | NLift ?h ?a => app constr:(ALift) [h; dec_a ns a]
  end
with dec_t (ns : nats) (t : constr) : constr :=
  lazy_match! t with
  | NVarE ?h ?i => app constr:(TVarE) [h; idx ns (int_of_n i)]
  | NBindE ?u ?p => app constr:(TBindE) [idx ns (int_of_n u); dec_p ns p]
  | NShiftE ?h ?t => app constr:(TShiftE) [h; dec_t ns t]
  | NLookE ?h ?i ?a => app constr:(TLookE) [h; idx ns (int_of_n i); dec_a ns a]
  end
with dec_p (ns : nats) (p : constr) : constr :=
  lazy_match! p with
  | NPId => constr:(PId)
  | NPAtom ?n => app constr:(PAtom) [idx ns (int_of_n n)]
  | NPComp ?a ?p => let a := dec_a ns a in let p := dec_p ns p in app constr:(PComp) [a; p]
  | NPShift ?h ?p => app constr:(PShift) [h; dec_p ns p]
  end.

(** A shown normal form: the shared definitions (as a list and as a
    Gallina list) and the expression. *)
Ltac2 Type shown := { sh_l : constr list; sh_c : constr; sh_root : constr; sh_val : constr }.

Ltac2 dec_shown (ns : nats) (sh : constr) (r : constr) : shown :=
  let l := List.map (dec_a ns) (of_list sh) in
  let c := list_of constr:(aexp) l in
  let root := dec_a ns r in
  { sh_l := l; sh_c := c; sh_root := root;
    sh_val := app constr:(@pair (list aexp) aexp) [c; root] }.

(** [c : option (list aexp * aexp)], computed. *)
Ltac2 vm_show (ns : nats) (c : constr) : shown option :=
  lazy_match! (Std.eval_vm None '(option_map enc_show $c)) with
  | Some (?sh, ?r) => Some ((dec_shown ns sh r))
  | None => None
  end.

(** [c : option (nat * (list aexp * aexp))], computed. *)
Ltac2 vm_pay (ns : nats) (c : constr) : (constr * shown) option :=
  lazy_match! Std.eval_vm None '(option_map (fun p : nat * (list aexp * aexp) => (N.of_nat (fst p), enc_show (snd p))) $c) with
  | Some (?u, (?sh, ?r)) => Some (idx ns (int_of_n u), dec_shown ns sh r)
  | None => None
  end.

Ltac2 some (ty : constr) (x : constr) : constr := app constr:(@Some) [ty; x].

(** [Forall2 (fun x od => od = Some d -> x = aeden d) atoms defs]: each
    defined atom is (convertibly) its definition. *)
Ltac2 defs_proof (t : constr) (rel : constr) (atoms : constr list) (defl : constr option list) : constr :=
  let rt := constr:(@radj) in
  let aty := app rt [t] in
  let oty := constr:(option aexp) in
  let rec go xs ds :=
    match xs, ds with
    | x :: xs2, od :: ds2 =>
        let (pf, l, lt2) := go xs2 ds2 in
        let odc := match od with Some d => app constr:(@Some aexp) [d] | None => constr:(@None aexp) end in
        let h := match od with Some _ => app constr:(@eq_refl) [aty; x] | None => constr:(I) end in
        (app constr:(@Forall2_cons) [aty; oty; rel; x; odc; l; lt2; h; pf],
         app constr:(@cons) [aty; x; l], app constr:(@cons) [oty; odc; lt2])
    | _, _ => (app constr:(@Forall2_nil) [aty; oty; rel], app constr:(@nil) [aty], app constr:(@nil) [oty])
    end in
  let (pf, _, _) := go atoms defl in pf.

(** ** Rewriting an adjustment to its normal form *)

Ltac2 Type outcome := [ Shown (constr list) | NotShown ].

(** The normal forms [names] has produced: rewriting them again would
    give them back. *)
Ltac2 Type memo := { mutable seen : constr list }.

(** [a = b], [b] the rendering of the normal form of [a], rewritten in the
    goal; the terms of [b]. *)
Ltac2 show_adj (memo : memo) (a : constr) : outcome :=
  lazy_match! Constr.type a with
  | adj ?t _ _ =>
      let ty := Constr.type a in
      let r := '(adj_raw $a) in
      let s := new_st () in
      let e := (reify_adj s r) in
      let en := (finish s t) in
      let nt := nat_lit (en.(e_ns)) (en.(e_nt)) in
      let nb := nat_lit (en.(e_ns)) (en.(e_nb)) in
      let l := en.(e_l) in
      let defs := en.(e_defs) in
      let d := (vm_show (en.(e_ns)) '(hshowD (order_of $l) $nt $nb $defs $e)) in
      match d with
      | Some sh =>
          let (shd, root) := (sh.(sh_c), sh.(sh_root)) in
          let terms := en.(e_terms) in
          let b := (render_term t ty (en.(e_labs)) (Array.of_list terms) (en.(e_atoms)) (en.(e_nb)) (sh.(sh_l)) root) in
          memo.(seen) := (b :: (memo.(seen)));
          (if Constr.equal a b then () else
           let id := fresh @E in
           let (le, te, ae, pe, hl) := (en.(e_le), en.(e_te), en.(e_ae), en.(e_pe), en.(e_hl)) in
           (assert_by id '($a = $b) (fun () =>
             let (rs, hs) := intro_shares [] [] in
             refine_c (fun () => '(adj_eq _ _ _));
             let rs := list_of '(radj $t) rs in
             let hsid := fresh @Hs in
             assert_by hsid '(Forall2 (fun z0 d0 => z0 = aeden $le $te ($ae ++ $rs) $pe d0) $rs $shd)
               (fun () => shares_ok hs);
             let hsp := Control.hyp hsid in
             let ty := constr:((list aexp * aexp)%type) in
             let ht := vm_eq '(option $ty) '(hshowD (order_of $l) (List.length $te) (List.length $ae) $defs $e) (some ty (sh.(sh_val))) in
             let rel := '(fun (x : radj $t) (od : option aexp) => match od with Some d => x = aeden $le $te ($ae ++ $rs) $pe d | None => True end) in
             let hd := defs_proof t rel (Array.to_list (en.(e_atoms))) (en.(e_defl)) in
             Std.exact_no_check '(hshowD_sound $le $te $ae $rs $pe $l $defs $e $shd $root $hl $ht $hd $hsp)));
           (rewrite_with (Control.hyp id)); Std.clear [id]);
          Shown terms
      | None => NotShown
      end
  end.

(** ** Candidates

    Adjustment expressions in [c] not inside another, and closed (so not
    under a binder they use). *)
Ltac2 is_adj_head (c : constr) : bool :=
  lazy_match! c with
  | compose _ _ => true
  | cform_id _ => true
  | cform _ _ => true
  | at_scope _ => true
  | _ => false
  end.

Ltac2 add_new (c : constr) (acc : constr list) : constr list :=
  if List.exist (Constr.equal c) acc then acc else c :: acc.

Ltac2 rec cands (p : constr -> bool) (c : constr) (acc : constr list) : constr list :=
  if Bool.and (Constr.Unsafe.is_closed c) (p c) then add_new c acc
  else
    let r := { contents := acc } in
    Constr.Unsafe.iter (fun x => r.(contents) := cands p x (r.(contents))) c;
    r.(contents).

Ltac2 candidates (p : constr -> bool) (c : constr) : constr list := List.rev (cands p c []).

(** Those strictly inside [c]. *)
Ltac2 candidates_in (p : constr -> bool) (c : constr) : constr list :=
  let r := { contents := [] } in
  Constr.Unsafe.iter (fun x => r.(contents) := cands p x (r.(contents))) c;
  List.rev (r.(contents)).

(** Each candidate is rewritten once, and then the candidates in its
    terms; one whose normal form cannot be shown is left, and the
    candidates inside it are tried instead.  Normal forms already
    produced are left alone. *)
Ltac2 rec rewrite_each (memo : memo) (cs : constr list) : unit :=
  List.iter
    (fun a =>
       if List.exist (Constr.equal a) (memo.(seen)) then () else
       Notations.try0 (fun () =>
         match show_adj memo a with
         | Shown terms => List.iter (fun u => rewrite_each memo (candidates is_adj_head u)) terms
         | NotShown => rewrite_each memo (candidates_in is_adj_head a)
         end))
    cs.

Ltac2 names_adjs (memo : memo) : unit := rewrite_each memo (candidates is_adj_head (Control.goal ())).

(** ** Variables *)

Ltac2 rec nth_c (l : constr list) (i : int) : constr := List.nth l i.

(** [apply_var a v]: when the normal form of [a] sends [v] to a variable
    or a term, an equation [id : apply_var a v = ...] for it. *)
Ltac2 var_eq (t : constr) (id : ident) : unit :=
  lazy_match! t with
  | @apply_var ?ty _ ?m ?a ?v =>
      let r := '(adj_raw $a) in
      let vr := eval cbn [var_raw bvar bvar0 fvar lvar] in (var_raw $v) in
      lazy_match! vr with
      | mk_rvar ?hv ?i =>
          if is_nat_lit i then () else Control.zero (Tactic_failure None);
          let s := new_st () in
          let e := reify_adj s r in
          let eh := reify_label s hv in
          let en := finish s ty in
          let nt := nat_lit (en.(e_ns)) (en.(e_nt)) in
          let nb := nat_lit (en.(e_ns)) (en.(e_nb)) in
          let (le, te, ae, pe, l, hl) := (en.(e_le), en.(e_te), en.(e_ae), en.(e_pe), en.(e_l), en.(e_hl)) in
          let res := Std.eval_vm None '(hlook_var (order_of $l) $nt $e $eh $i) in
          lazy_match! res with
          | Some (?h', ?j) =>
              let w := if is_lnone h' then '(@bvar $m $j stt)
                       else let x := lab_env (en.(e_labs)) h' in '(@fvar $m $x $j) in
              assert_by id '(apply_var $a $v = Rename $w) (fun () =>
                refine_c (fun () => '(apply_var_rename _ _ _ _));
                let hv := vm_eq '(option (lexp * nat)) '(hlook_var (order_of $l) (List.length $te) $e $eh $i) res in
                Std.exact_no_check '(hlook_var_sound $le $te $ae $pe $l $e $eh $i $h' $j $hl $hv))
          | None =>
              match vm_pay (en.(e_ns)) '(hlook_pay (order_of $l) $nt $nb $e $eh $i) with
              | Some (u, sh) =>
                  let (shd, root) := (sh.(sh_c), sh.(sh_root)) in
                  let terms := en.(e_terms) in
                  let b := render_term ty '(adj $ty 0 $m) (en.(e_labs)) (Array.of_list terms) (en.(e_atoms)) (en.(e_nb)) (sh.(sh_l)) root in
                  let x := nth_c terms (int_of_idx u) in
                  assert_by id '(apply_var $a $v = Bind $x (pcompose $b pid)) (fun () =>
                    refine_c (fun () => '(apply_var_bind _ _ _ _ _ _));
                    let (rs, hs) := intro_shares_t b [] [] in
                    let rs := list_of '(radj $ty) rs in
                    let hsid := fresh @Hs in
                    assert_by hsid '(Forall2 (fun z0 d0 => z0 = aeden $le $te ($ae ++ $rs) $pe d0) $rs $shd)
                      (fun () => shares_ok hs);
                    let hsp := Control.hyp hsid in
                    let pty := constr:((nat * (list aexp * aexp))%type) in
                    let hp := vm_eq '(option $pty)
                                '(hlook_pay (order_of $l) (List.length $te) (List.length $ae) $e $eh $i)
                                (some pty (app constr:(@pair nat (list aexp * aexp)) [u; sh.(sh_val)])) in
                    Std.exact_no_check
                      '(hbind_show_sound $le $te $ae $rs $pe $l $e $eh $i $u $shd $root $x $hl $hp $hsp eq_refl))
              | None => Control.zero Not_found
              end
          end
      end
  end.

(** The first candidate [t] in the goal on which [f t] succeeds, repeatedly. *)
Ltac2 rec each_until_fail (p : constr -> bool) (f : constr -> unit) : unit :=
  let rec first cs :=
    match cs with
    | [] => false
    | c :: cs => if Control.plus (fun () => f c; true) (fun _ => false) then true else first cs
    end in
  if first (candidates p (Control.goal ())) then each_until_fail p f else ().

Ltac2 names_apply () : unit :=
  Notations.repeat0 (fun () =>
    match! goal with
    | [ |- context [ @apply_var ?ty ?n ?m ?a ?v ] ] =>
        let t := app constr:(@apply_var) [ty; n; m; a; v] in
        let id := fresh @E in var_eq t id; rewrite_with (Control.hyp id); Std.clear [id]
    end).

(** [eval f g a v] nodes whose variable [a]'s normal form renames are
    evaluated to [f w]. *)
Ltac2 names_eval () : unit :=
  Notations.repeat0 (fun () =>
    match! goal with
    | [ |- context [ @eval _ _ _ _ ?f ?g ?a ?v ] ] =>
        let id := fresh @E in
        var_eq '(Indexed.apply_var $a $v) id;
        let hid := Control.hyp id in
        lazy_match! Constr.type hid with
        | _ = Rename ?w =>
            let r := eval cbn in ($f $w) in
            rewrite_with '(eval_rename $f $g $a $v $w $hid : _ = $r); Std.clear [id]
        | _ = Bind ?x ?rho => rewrite_with '(eval_bind $f $g $a $v $x $rho $hid); Std.clear [id]
        end
    end).

(** ** Materialising

    An adjustment [A] to the closed scope with terms with payload
    adjustments, used in a substitution, is replaced by [A'] where the
    first such term [u⟨b⟩] is [u [b]], when the syntax has a [SubstMat]
    instance. *)
Ltac2 mat_one (a : constr) : unit :=
  lazy_match! Constr.type a with
  | adj ?ty ?n 0 =>
      let inst := constr:(_ : SubstMat $ty) in
      let r := '(adj_raw $a) in
      let s := new_st () in
      let e := reify_adj s r in
      let en := finish s ty in
      let ns := en.(e_ns) in
      let (le, _, ae, pe, l, hl) := (en.(e_le), en.(e_te), en.(e_ae), en.(e_pe), en.(e_l), en.(e_hl)) in
      let n1 := nat_lit ns (en.(e_nt)) in
      let n2 := nat_lit ns (Int.add (en.(e_nt)) 1) in
      let nb := nat_lit ns (en.(e_nb)) in
      match vm_show ns '(hmat_display (order_of $l) $n2 $nb $e $n1) with
      | Some dsh =>
          let (sh', r') := (dsh.(sh_c), dsh.(sh_root)) in
          let shl := dsh.(sh_l) in
          let nbbi := Int.add (en.(e_nb)) (List.length shl) in
          let nbb := nat_lit ns nbbi in
          match vm_pay ns '(hmat_target (order_of $l) $n1 $nbb $e) with
          | Some (u, bsh) =>
              let (shb, rb) := (bsh.(sh_c), bsh.(sh_root)) in
              let terms := en.(e_terms) in
              let b := render_term ty '(adj $ty 0 0) (en.(e_labs)) (Array.of_list terms) (en.(e_atoms)) nbbi (bsh.(sh_l)) rb in
              let ut := nth_c terms (int_of_idx u) in
              let fb := Std.eval_hnf '(@sm_back _ $inst) in
              let fs := Std.eval_hnf '(@sm_subst _ $inst 0 0 $b) in
              let fo := Std.eval_hnf '(@sm_of _ $inst) in
              let x := eval cbv beta in ($fb ($fs ($fo $ut))) in
              let te2 := list_of ty (List.append (en.(e_terms)) [x]) in
              let a' := render_term ty '(adj $ty $n 0) (en.(e_labs)) (Array.of_list (List.append terms [x])) (en.(e_atoms))
                          (en.(e_nb)) shl r' in
              let hid := fresh @H in
              let g := '(@sm_g _ $inst) in
              assert_by hid '(forall v : var $n, mrel $g (rapply (adj_raw $a) (var_raw v)) (rapply (adj_raw $a') (var_raw v)))
                (fun () =>
                   let (rs, hs) := intro_shares_t a' [] [] in
                   let rs := list_of '(radj $ty) rs in
                   let v := fresh @v in intro_as v;
                   let vv := Control.hyp v in
                   let hsid := fresh @Hs in
                   assert_by hsid '(Forall2 (fun z0 d0 => z0 = aeden $le $te2 ($ae ++ $rs) $pe d0) $rs ($sh' ++ $shb))
                     (fun () => Std.cbv { Std.rStrength := Std.Norm; Std.rBeta := false; Std.rMatch := false; Std.rFix := false;
                                          Std.rCofix := false; Std.rZeta := false; Std.rDelta := false;
                                          Std.rConst := [reference:(List.app)] } (concl ());
                                shares_ok hs);
                   let hsp := Control.hyp hsid in
                   let pty := constr:((nat * (list aexp * aexp))%type) in
                   let sty := constr:((list aexp * aexp)%type) in
                   let ht := vm_eq '(option $pty) '(hmat_target (order_of $l) $n1 $nbb $e)
                               (some pty (app constr:(@pair nat (list aexp * aexp)) [u; bsh.(sh_val)])) in
                   let hd := vm_eq '(option $sty) '(hmat_display (order_of $l) $n2 (List.length $ae) $e $n1) (some sty (dsh.(sh_val))) in
                   let f := '(fun y => $g (rpcompose (aeden $le $te2 ($ae ++ $rs) $pe $rb) rpidentity) y) in
                   let hk := '(nth_hk $te2 $u $n1 $f $ut eq_refl (f_equal Some (eq_sym (@sm_g_spec _ $inst $b $ut)))) in
                   Std.exact_no_check
                     '(hmat_show_sound $le $te2 $ae $rs $pe $g $l $e $n1 $u $shb $rb $sh' $r' $nbb $n1 $n2 $hl
                         (le_S _ _ (le_n _)) (le_n _) $ht $hd eq_refl $hsp $hk (var_raw $vv)));
              let eid := fresh @E in
              let hh := Control.hyp hid in
              let f := Std.eval_hnf '(@sm_subst _ $inst $n 0 $a) in
              let f' := Std.eval_hnf '(@sm_subst _ $inst $n 0 $a') in
              let ety := eval cbv beta in (forall t, $f t = $f' t) in
              assert_by eid ety (fun () => Std.exact_no_check '(@sm_mat _ $inst $n $a $a' $hh));
              Std.clear [hid];
              Control.progress (fun () => rewrite_all_instances (Control.hyp eid));
              Std.clear [eid]
          | None => Control.zero Not_found
          end
      | None => Control.zero Not_found
      end
  end.

Ltac2 is_adj_expr (c : constr) : bool :=
  lazy_match! c with
  | compose _ _ => true
  | cform_id _ => true
  | cform _ _ => true
  | at_scope _ => true
  | Indexed.share _ _ => true
  | _ => false
  end.

Ltac2 names_mat () : unit := each_until_fail is_adj_expr mat_one.

(** ** The tactic

    [names]:
    1. rewrites with [names_pre] and then [names_var], the monad laws that
       remove a Kleisli extension or move work into the adjustment (a
       syntax's [Subst] functor adds them): under binders and fusing
       nested substitutions first, then substituting into variables;
    2. rewrites every adjustment built from context forms and [∘] to its
       normal form, shown as context forms;
    3. materialises payloads ([SubstMat]);
    4. evaluates [apply_var a v] and [eval] nodes for variables the normal
       form of [a] renames or sends to a term;
    5. rewrites with [names_post]: identity substitutions go, a payload
       result [u⟨b ∘ id⟩] becomes [subst b u], and an [eval] node left is
       shown as a substitution again;
    and repeats this until nothing changes: a pass after the first only
    finds work in terms that payload results put in the goal (normal
    forms already produced are not normalised again). *)
Ltac2 autorw (db : ident) : unit := Std.autorewrite false None [db] (concl ()).

Ltac2 names_pass (memo : memo) : unit :=
  (Notations.repeat0 (fun () => Control.progress (fun () =>
    autorw @names_pre; Std.cbn { Std.rStrength := Std.Norm; Std.rBeta := true; Std.rMatch := true; Std.rFix := true;
                                 Std.rCofix := true; Std.rZeta := true; Std.rDelta := false;
                                 Std.rConst := [reference:(ext_shift)] } (concl ()))));
  (autorw @names_var);
  (names_adjs memo);
  (Notations.try0 names_mat);
  (names_apply ());
  (names_eval ());
  (autorw @names_post).

Ltac2 names_tac () : unit :=
  let memo := { seen := [] } in
  Notations.repeat0 (fun () => Control.progress (fun () => names_pass memo)).

Ltac2 Notation "names" := names_tac ().

(** For Ltac1 proofs. *)
Ltac names := ltac2:(names_tac ()).
