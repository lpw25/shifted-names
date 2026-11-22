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
From ShiftedNames.Core Require Import Label Var Adjustment Laws Indexed Syntax Normalise HConcrete HShow Braun HShowB.
From ShiftedNames.Core Require HNorm.
Import ListNotations.

(** ** Syntaxes

    A substitution [t [a]] of a syntax, as [names] sees it: the node
    [csubst L a t], which carries the syntax's variables [var], its
    substitution [sub] and the law [L] that lets [names] change payloads,
    as arguments [names] reads and passes on, never unfolds:
    - materialising: how a payload adjustment acts on a closed term ([g],
      which is [sub] on one of the form [b ∘ id]), and that substitutions
      into the closed scope whose results on each variable are related by
      [mrel g] are equal;
    - a term that is a variable: substitutions whose results on each
      variable are related by [vrel var] are equal, [vrel] relating a
      variable [w] with a payload [W ∘ id] to where [W] sends [w].
    A syntax's [Subst] functor rewrites its substitution to the node before
    [names] works on it ([names_node]) and back after ([names_post]). *)
Definition vrel {T} (var0 : var 0 -> T) (r r' : rresult T) : Prop :=
  r = r' \/ exists (w : var 0) (W : radj T), r = inr (var0 w, rpcompose W rpidentity) /\ r' = rapply W (var_raw w).

Record SubstLaw (term : nat -> Type) (var0 : var 0 -> term 0) (sub : forall N M, adj (term 0) N M -> term N -> term M)
    (g : rpadj (term 0) -> term 0 -> term 0) : Prop := {
  sl_g : forall (b : adj (term 0) 0 0) u, g (rpcompose (adj_raw b) rpidentity) u = sub 0 0 b u;
  sl_mat : forall N (a a' : adj (term 0) N 0),
    (forall v : var N, mrel g (rapply (adj_raw a) (var_raw v)) (rapply (adj_raw a') (var_raw v))) ->
    forall t, sub N 0 a t = sub N 0 a' t;
  sl_var : forall N M (a a' : adj (term 0) N M),
    (forall v : var N, vrel var0 (rapply (adj_raw a) (var_raw v)) (rapply (adj_raw a') (var_raw v))) ->
    forall t, sub N M a t = sub N M a' t }.

Definition csubst {term var0 sub g} (L : SubstLaw term var0 sub g) {N M} (a : adj (term 0) N M) (t : term N) : term M :=
  sub N M a t.

(** A term that is a variable, as [names] sees it: the node [cvar L w],
    which [names] recognises syntactically.  The functor rewrites its
    closed variables to it ([names_node]) and back ([names_post]).  It is
    opaque to rewriting, so that the functor's rule does not see [var0 w]
    in it again. *)
Definition cvar {term var0 sub g} (L : SubstLaw term var0 sub g) (w : var 0) : term 0 := var0 w.

Lemma csubst_mat {term var0 sub g} (L : SubstLaw term var0 sub g) {N} (a a' : adj (term 0) N 0) :
  (forall v : var N, mrel g (rapply (adj_raw a) (var_raw v)) (rapply (adj_raw a') (var_raw v))) ->
  forall t, csubst L a t = csubst L a' t.
Proof. apply (sl_mat _ _ _ _ L). Qed.

Lemma csubst_var {term var0 sub g} (L : SubstLaw term var0 sub g) {N M} (a a' : adj (term 0) N M) :
  (forall v : var N, vrel var0 (rapply (adj_raw a) (var_raw v)) (rapply (adj_raw a') (var_raw v))) ->
  forall t, csubst L a t = csubst L a' t.
Proof. apply (sl_var _ _ _ _ L). Qed.

Lemma share_intro_r {T N M K L} (a : adj T N M) (A : adj T K L) (f : adj T K L -> adj T N M) :
  (forall r, adj_raw r = adj_raw A -> a = f r) -> a = Indexed.share A f.
Proof. intros H; rewrite share_eq; apply H; reflexivity. Qed.

Lemma share_intro_p {T N M K L} (A : adj T K L) (f : adj T K L -> adj T N M) (P : adj T N M -> Prop) :
  (forall r, adj_raw r = adj_raw A -> P (f r)) -> P (Indexed.share A f).
Proof. intros H; rewrite share_eq; apply H; reflexivity. Qed.

(** A rendering with shared definitions, as data: [nest] gives the
    rendering, and [chain_intro] proves a property of it from one of its
    root, the definitions as variables, with one step for each.  (The
    proof [names] builds mentions each definition once.) *)
Inductive chain {T : Type} {N M : nat} : Type :=
| CRoot (b : adj T N M)
| CShare {K L} (d : adj T K L) (k : adj T K L -> chain).
Arguments chain T N M : clear implicits.

Fixpoint nest {T N M} (c : chain T N M) : adj T N M :=
  match c with CRoot b => b | CShare d k => Indexed.share d (fun r => nest (k r)) end.

Fixpoint chain_all {T N M} (P : adj T N M -> Prop) (c : chain T N M) : Prop :=
  match c with CRoot b => P b | CShare d k => forall r, adj_raw r = adj_raw d -> chain_all P (k r) end.

Lemma chain_intro {T N M} (P : adj T N M -> Prop) (c : chain T N M) : chain_all P c -> P (nest c).
Proof.
  induction c as [b|K L d k IH]; cbn [chain_all nest]; [exact (fun H => H)|].
  intros H; rewrite share_eq; apply IH, H; reflexivity.
Qed.

(** [Forall] and [Forall2] proofs built as balanced trees, so that a
    proof for a list of [n] entries has size [O(n log n)] (one built by
    [cons] mentions each suffix of the list). *)
Lemma F_one {A} (P : A -> Prop) x : P x -> Forall P [x].
Proof. intros H; constructor; [exact H|constructor]. Qed.

Lemma F_app {A} (P : A -> Prop) l1 l2 : Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof. intros H1 H2; apply Forall_app; split; assumption. Qed.

Lemma F2_one {A B} (R : A -> B -> Prop) x y : R x y -> Forall2 R [x] [y].
Proof. intros H; constructor; [exact H|constructor]. Qed.

Lemma F2_app {A B} (R : A -> B -> Prop) l1 l2 m1 m2 : Forall2 R l1 m1 -> Forall2 R l2 m2 -> Forall2 R (l1 ++ l2) (m1 ++ m2).
Proof. apply Forall2_app. Qed.

(** A use of a shared definition, as the reifier marks it: [A] itself,
    with the atom [k] that stands for it. *)
Definition sref {T K L} (A : adj T K L) (k : N) : adj T K L := A.

Lemma lfacts_nil le : lfacts_ok le [].
Proof. constructor. Qed.

Lemma lfacts_cons le x y l : olabel_lt (lden le x) (lden le y) -> lfacts_ok le l -> lfacts_ok le ((x, y) :: l).
Proof. intros H Hl; constructor; assumption. Qed.

(** The term [k] is the term [u] with the payload [b] materialised. *)
Lemma mat_kB {term var0 sub g} (L : SubstLaw term var0 sub g) (l : braun (term 0)) u k ut (b : adj (term 0) 0 0)
    (d : radj (term 0)) :
  bnth l u = Some ut -> bnth l k = Some (csubst L b ut) -> adj_raw b = d ->
  forall y, bnth l u = Some y -> bnth l k = Some (g (rpcompose d rpidentity) y).
Proof. intros H1 H2 <- y Hy; rewrite H1 in Hy; injection Hy as <-; rewrite H2, (sl_g _ _ _ _ L); reflexivity. Qed.

#[global] Opaque cvar.

(** The terms [vt] says are variables are the variables [var0 w]: from
    what [hvarB_show_sound] gives, [vrel]. *)
Lemma var_bridge {T} (var0 : var 0 -> T) (Te : braun T) (Le : braun label) (vt : list (nat * (lexp * nat))) (A B : radj T) :
  Forall (fun '(u, (h, i)) => exists w : var 0, bnth Te (N.of_nat u) = Some (var0 w) /\ var_raw w = mk_rvar (ldenB Le h) i) vt ->
  ((forall u x, vlook u vt = Some x -> exists y, bnth Te (N.of_nat u) = Some y) ->
   forall v, rapply A v = rapply B v \/ exists u h i y W, vlook u vt = Some (h, i) /\ bnth Te (N.of_nat u) = Some y /\
     rapply A v = inr (y, rpcompose W rpidentity) /\ rapply B v = rapply W (mk_rvar (ldenB Le h) i)) ->
  forall v, vrel var0 (rapply A v) (rapply B v).
Proof.
  intros Hvt H v.
  assert (Hin : forall u x, vlook u vt = Some x -> In (u, x) vt).
  { clear; induction vt as [|[k x0] vt IH]; intros u x E; cbn in E; [discriminate|].
    destruct (Nat.eqb k u) eqn:Ek; [apply Nat.eqb_eq in Ek; injection E as <-; left; subst; reflexivity|right; apply IH, E]. }
  rewrite Forall_forall in Hvt.
  assert (Hy : forall u x, vlook u vt = Some x -> exists y, bnth Te (N.of_nat u) = Some y).
  { intros u [h i] E; destruct (Hvt _ (Hin _ _ E)) as [w [E1 _]]; exists (var0 w); exact E1. }
  destruct (H Hy v) as [E|[u [h [i [y [W [E1 [E2 [E3 E4]]]]]]]]]; [left; exact E|right].
  destruct (Hvt _ (Hin _ _ E1)) as [w [Ew Hw]].
  rewrite E2 in Ew; injection Ew as ->.
  exists w, W; split; [exact E3|rewrite E4, Hw; reflexivity].
Qed.

(** ** Ltac2 *)

From Ltac2 Require Import Ltac2.

(** ** Tables *)

(** Entries in order of first occurrence (kept latest first); entries
    that are variables, or a raw adjustment of a variable, are also kept
    by name. *)
Ltac2 Type tbl := { mutable items : constr list; mutable size : int; mutable vars : (ident, int) FMap.t }.

Ltac2 new_tbl () : tbl := { items := []; size := 0; vars := FMap.empty FSet.Tags.ident_tag }.

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

(** An entry's index, the entry added if it is not there: entries are
    compared syntactically (variables by name). *)
Ltac2 tbl_add (lets : ident FSet.t) (t : tbl) (x : constr) : int :=
  match key_of x with
  | Some id =>
      match FMap.find_opt id (t.(vars)) with
      | Some i => i
      | None => let i := tbl_push t x in t.(vars) := FMap.add id i (t.(vars)); i
      end
  | None =>
      match find_idx (Constr.equal x) (List.rev (t.(items))) 0 with
      | Some i => i
      | None => tbl_push t x
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

(** ** Reification

    Reification reads the syntax as it is written, with no reduction:
    [⨾], [⟦⟧], context forms (their entries written with the [CEnt]...
    classes or the constructors), [at_scope] and [share]; anything else,
    and a context form with an entry it cannot read (a variable that is
    not a literal), is an atom.  The expression it gives is what
    [adj_raw] of the syntax computes to ([aedenB]), as the kernel checks:
    the reifier follows [octx_den], [ictx_den], [sctx_den] and
    [pctx_den]. *)

(** An index in the input: small ones as numerals, others as
    [N.to_nat] of a binary numeral, so that the input stays small. *)
Ltac2 idx (ns : nats) (k : int) : constr :=
  if Int.lt k 16 then nat_lit ns k else app constr:(N.to_nat) [n_lit k].

Ltac2 adj_args (ty : constr) (xs : constr list) : constr list :=
  lazy_match! ty with adj ?t ?k ?l => t :: k :: l :: xs end.

(** The heads the reifier reads. *)
Ltac2 Type rh := {
  h_identity : constr; h_compose : constr; h_at : constr; h_share : constr; h_sref : constr;
  h_cform_id : constr; h_cform : constr; h_adj_raw : constr;
  h_OEnd : constr; h_OEndT : constr; h_OPosF : constr; h_OPosB : constr; h_ONamF : constr; h_ONamB : constr;
  h_OShort : constr; h_OShortT : constr; h_STail : constr;
  h_IEmpty : constr; h_IPosF : constr; h_IPosB : constr; h_IRenF : constr; h_IRenB : constr; h_ISubF : constr; h_ISubB : constr;
  h_SEmpty : constr; h_SLiftF : constr; h_SLiftB : constr; h_SSubF : constr; h_SSubB : constr; h_SRenF : constr;
  h_SRenB : constr; h_SSubFA : constr; h_SSubBA : constr; h_SLookF : constr; h_SLookB : constr;
  h_PEmpty : constr; h_PRen : constr; h_PSub : constr;
  h_methods : (constr * int) list; h_insts : (constr * constr) list;
  h_bvar : constr; h_bvar0 : constr; h_fvar : constr; h_lvar : constr; h_vshift_free : constr; h_vshift_bound : constr;
  h_O : constr; h_S : constr;
  r_NId : constr; r_NAtom : constr; r_NCompose : constr; r_NOuter : constr; r_NInner : constr;
  r_NVarE : constr; r_NBindE : constr; r_NShiftE : constr; r_NLookE : constr; r_NPComp : constr; r_NPId : constr;
  r_LNone : constr; r_N0 : constr }.

Ltac2 mk_rh () : rh := {
  h_identity := constr:(@identity); h_compose := constr:(@compose); h_at := constr:(@at_scope);
  h_share := constr:(@Indexed.share); h_sref := constr:(@sref); h_cform_id := constr:(@cform_id); h_cform := constr:(@cform);
  h_adj_raw := constr:(@adj_raw);
  h_OEnd := constr:(@OEnd); h_OEndT := constr:(@OEndT); h_OPosF := constr:(@OPosF); h_OPosB := constr:(@OPosB);
  h_ONamF := constr:(@ONamF); h_ONamB := constr:(@ONamB); h_OShort := constr:(@OShort); h_OShortT := constr:(@OShortT);
  h_STail := constr:(@STail);
  h_IEmpty := constr:(@IEmpty); h_IPosF := constr:(@IPosF); h_IPosB := constr:(@IPosB); h_IRenF := constr:(@IRenF);
  h_IRenB := constr:(@IRenB); h_ISubF := constr:(@ISubF); h_ISubB := constr:(@ISubB);
  h_SEmpty := constr:(@SEmpty); h_SLiftF := constr:(@SLiftF); h_SLiftB := constr:(@SLiftB); h_SSubF := constr:(@SSubF);
  h_SSubB := constr:(@SSubB); h_SRenF := constr:(@SRenF); h_SRenB := constr:(@SRenB); h_SSubFA := constr:(@SSubFA);
  h_SSubBA := constr:(@SSubBA); h_SLookF := constr:(@SLookF); h_SLookB := constr:(@SLookB);
  h_PEmpty := constr:(@PEmpty); h_PRen := constr:(@PRen); h_PSub := constr:(@PSub);
  (* each method, with the number of its class's parameters before the instance *)
  h_methods := [(constr:(@cnil), 1); (constr:(@cent), 2); (constr:(@cbnd), 2); (constr:(@csub), 4);
                (constr:(@csubb), 4); (constr:(@cren), 3); (constr:(@crenb), 3)];
  (* each instance, with the constructor it is *)
  h_insts := [(constr:(@cnil_full), constr:(@IEmpty)); (constr:(@cnil_short), constr:(@SEmpty));
              (constr:(@cent_full), constr:(@IPosF)); (constr:(@cent_short), constr:(@SLiftF));
              (constr:(@cbnd_full), constr:(@IPosB)); (constr:(@cbnd_short), constr:(@SLiftB));
              (constr:(@csub_full), constr:(@ISubF)); (constr:(@csub_short), constr:(@SSubF));
              (constr:(@csubb_full), constr:(@ISubB)); (constr:(@csubb_short), constr:(@SSubB));
              (constr:(@cren_full), constr:(@IRenF)); (constr:(@cren_short), constr:(@SRenF));
              (constr:(@crenb_full), constr:(@IRenB)); (constr:(@crenb_short), constr:(@SRenB))];
  h_bvar := constr:(@bvar); h_bvar0 := constr:(@bvar0); h_fvar := constr:(@fvar); h_lvar := constr:(@lvar);
  h_vshift_free := constr:(@vshift_free); h_vshift_bound := constr:(@vshift_bound);
  h_O := constr:(O); h_S := constr:(S);
  r_NId := constr:(NId); r_NAtom := constr:(NAtom); r_NCompose := constr:(NCompose); r_NOuter := constr:(NOuter);
  r_NInner := constr:(NInner); r_NVarE := constr:(NVarE); r_NBindE := constr:(NBindE); r_NShiftE := constr:(NShiftE);
  r_NLookE := constr:(NLookE); r_NPComp := constr:(NPComp); r_NPId := constr:(NPId);
  r_LNone := constr:(LNone); r_N0 := constr:(N0) }.

Ltac2 Type st := { labs : tbl; terms : tbl; atoms : tbl; patoms : tbl; ns : nats; lets : ident FSet.t;
                   heads : rh; mutable sdefs : (int, constr) FMap.t }.

Ltac2 new_st () : st :=
  { labs := new_tbl (); terms := new_tbl (); atoms := new_tbl (); patoms := new_tbl (); ns := new_nats ();
    lets := List.fold_left (fun acc (id, b, _) => match b with Some _ => FSet.add id acc | None => acc end)
              (FSet.empty FSet.Tags.ident_tag) (Control.hyps ());
    heads := mk_rh ();
    sdefs := FMap.empty FSet.Tags.int_tag }.

Ltac2 reify_lab (s : st) (x : constr) : constr :=
  if is_string_lit x then app constr:(LCon) [x]
  else let n := n_lit (tbl_add (s.(lets)) (s.(labs)) x) in app constr:(LAtom) [n].

(** The head and arguments of [c], under casts. *)
Ltac2 rec split_app (c : constr) : constr * constr array :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args => (f, args)
  | Constr.Unsafe.Cast c' _ _ => split_app c'
  | _ => (c, Array.make 0 c)
  end.

Ltac2 rec assoc_c (k : constr) (l : (constr * 'a) list) : 'a option :=
  match l with
  | [] => None
  | (k', v) :: l' => if Constr.equal k k' then Some v else assoc_c k l'
  end.

(** A node of a context form, with an entry written with a class method
    read as the constructor its instance is. *)
Ltac2 view (h : rh) (c : constr) : constr * constr array :=
  let (f, args) := split_app c in
  match assoc_c f (h.(h_methods)) with
  | Some np =>
      let (fi, iargs) := split_app (Array.get args np) in
      match assoc_c fi (h.(h_insts)) with
      | Some ctor =>
          let n := Array.length args in
          (ctor, Array.append iargs (Array.sub args (Int.add np 1) (Int.sub n (Int.add np 1))))
      | None => Control.zero Not_found
      end
  | None => (f, args)
  end.

Ltac2 is_h (f : constr) (g : constr) : bool := Constr.equal f g.

Ltac2 n_of_nat_lit (s : st) (i : constr) : constr :=
  if is_nat_lit i then n_lit (int_of_nat i) else Control.zero Not_found.

(** A variable as written: [x ^ i], [· ^ i], or one shifted. *)
Ltac2 rec reify_var (s : st) (w : constr) : constr :=
  let h := s.(heads) in
  let (f, a) := split_app w in
  if is_h f (h.(h_fvar)) then app (h.(r_NVarE)) [reify_lab s (Array.get a 1); n_of_nat_lit s (Array.get a 2)]
  else if is_h f (h.(h_lvar)) then app (h.(r_NVarE)) [reify_lab s (Array.get a 1); h.(r_N0)]
  else if is_h f (h.(h_bvar)) then app (h.(r_NVarE)) [h.(r_LNone); n_of_nat_lit s (Array.get a 1)]
  else if is_h f (h.(h_bvar0)) then app (h.(r_NVarE)) [h.(r_LNone); h.(r_N0)]
  else if is_h f (h.(h_vshift_free)) then app (h.(r_NShiftE)) [reify_lab s (Array.get a 1); reify_var s (Array.get a 2)]
  else if is_h f (h.(h_vshift_bound)) then app (h.(r_NShiftE)) [h.(r_LNone); reify_var s (Array.get a 1)]
  else Control.zero Not_found.

Ltac2 reify_term (s : st) (u : constr) : constr := n_lit (tbl_add (s.(lets)) (s.(terms)) u).

(** [adj_raw a], [a : adj t n m], as an expression. *)
Ltac2 rec reify_adj (s : st) (t : constr) (n : constr) (m : constr) (a : constr) : constr :=
  let h := s.(heads) in
  let atom () :=
    let r := app (h.(h_adj_raw)) [t; n; m; a] in
    app (h.(r_NAtom)) [n_lit (tbl_add (s.(lets)) (s.(atoms)) r)] in
  let (f, args) := split_app a in
  if is_h f (h.(h_identity)) then h.(r_NId)
  else if is_h f (h.(h_compose)) then
    let (nn, mm, kk) := (Array.get args 1, Array.get args 2, Array.get args 3) in
    let ex := reify_adj s t mm kk (Array.get args 4) in
    let ey := reify_adj s t nn mm (Array.get args 5) in
    app (h.(r_NCompose)) [ex; ey]
  else if is_h f (h.(h_at)) then reify_adj s t constr:(O) constr:(O) (Array.get args 2)
  else if is_h f (h.(h_sref)) then app (h.(r_NAtom)) [Array.get args 4]
  else if is_h f (h.(h_share)) then
    (* the definition, as a new atom standing for it, and the body with a
       marked use of it for the bound variable *)
    let (kk, ll, aa, fb) := (Array.get args 3, Array.get args 4, Array.get args 5, Array.get args 6) in
    let d := reify_adj s t kk ll aa in
    let k := tbl_push (s.(atoms)) (app (h.(h_adj_raw)) [t; kk; ll; aa]) in
    s.(sdefs) := FMap.add k d (s.(sdefs));
    let marker := app (h.(h_sref)) [t; kk; ll; aa; n_lit k] in
    match Constr.Unsafe.kind fb with
    | Constr.Unsafe.Lambda _ b => reify_adj s t n m (Constr.Unsafe.substnl [marker] 0 b)
    | _ => atom ()
    end
  else if is_h f (h.(h_cform_id)) then
    Control.plus (fun () => reify_octx s t (Array.get args 6) (h.(r_NId))) (fun _ => atom ())
  else if is_h f (h.(h_cform)) then
    Control.plus (fun () =>
      match Constr.Unsafe.kind (Array.get args 7) with
      | Constr.Unsafe.Lambda _ o =>
          let x := reify_adj s t (Array.get args 2) (Array.get args 3) (Array.get args 8) in
          reify_octx s t o x
      | _ => Control.zero Not_found
      end) (fun _ => atom ())
  else atom ()

(** [octx_den o]: the outputs, outermost first, then what is inside them. *)
with reify_octx (s : st) (t : constr) (o : constr) (x0 : constr) : constr :=
  let h := s.(heads) in
  (* the outputs: (label, positional), and the node after them *)
  let rec outs o acc :=
    let (f, a) := split_app o in
    if is_h f (h.(h_OPosF)) then outs (Array.get a 10) ((reify_lab s (Array.get a 11), true) :: acc)
    else if is_h f (h.(h_OPosB)) then outs (Array.get a 10) ((h.(r_LNone), true) :: acc)
    else if is_h f (h.(h_ONamF)) then
      match Constr.Unsafe.kind (Array.get a 11) with
      | Constr.Unsafe.Lambda _ b => outs b ((reify_lab s (Array.get a 10), false) :: acc)
      | _ => Control.zero Not_found
      end
    else if is_h f (h.(h_ONamB)) then
      match Constr.Unsafe.kind (Array.get a 10) with
      | Constr.Unsafe.Lambda _ b => outs b ((h.(r_LNone), false) :: acc)
      | _ => Control.zero Not_found
      end
    else (List.rev acc, f, a) in
  let (os, f, a) := outs o [] in
  (* the variable each output gives the inputs: [octx_probe], shifted past
     the outputs inside it *)
  let rec probes os :=
    match os with
    | [] => []
    | (y, _) :: os' =>
        let v := List.fold_left (fun v (y', _) => app (h.(r_NShiftE)) [y'; v])
                   (app (h.(r_NVarE)) [y; h.(r_N0)]) os' in
        v :: probes os'
    end in
  let ps := probes os in
  let env := List.rev ps in
  let pos := List.rev (List.map snd (List.filter (fun ((_, p), _) => p) (List.combine os ps))) in
  let slots := List.rev (List.map snd (List.filter (fun ((_, p), _) => Bool.neg p) (List.combine os ps))) in
  let wrap x := List.fold_left (fun x (y, _) => app (h.(r_NOuter)) [y; x]) x os in
  let wk := wrap (h.(r_NId)) in
  let x := wrap x0 in
  if is_h f (h.(h_OEnd)) then reify_ictx s t (Array.get a 6) env pos slots wk x
  else if is_h f (h.(h_OEndT)) then reify_ictx s t (Array.get a 7) env pos slots wk x
  else if is_h f (h.(h_OShort)) then reify_sctx s t (Array.get a 6) (h.(r_NId)) x
  else if is_h f (h.(h_OShortT)) then
    let (fc, c) := split_app (Array.get a 6) in
    if is_h fc (h.(h_STail)) then
      let sig := reify_adj s t (Array.get c 3) (Array.get c 4) (Array.get c 6) in
      reify_sctx s t (Array.get c 5) (h.(r_NId)) sig
    else Control.zero Not_found
  else Control.zero Not_found

(** [ictx_den i]: each entry put on [x], the outermost first. *)
with reify_ictx (s : st) (t : constr) (i : constr) (env : constr list) (pos : constr list) (slots : constr list)
    (wk : constr) (x : constr) : constr :=
  let h := s.(heads) in
  let slot c :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Rel r => List.nth slots (Int.sub r 1)
    | _ => Control.zero Not_found
    end in
  let posn p := List.nth pos (int_of_nat p) in
  let pay q := app (h.(r_NPComp)) [reify_pctx s t q (Some slots) wk wk; h.(r_NPId)] in
  let (f, a) := view h i in
  let inner c e := reify_ictx s t c env pos slots wk e in
  if is_h f (h.(h_IEmpty)) then x
  else if is_h f (h.(h_IPosF)) then inner (Array.get a 6) (app (h.(r_NInner)) [reify_lab s (Array.get a 7); posn (Array.get a 5); x])
  else if is_h f (h.(h_IPosB)) then inner (Array.get a 6) (app (h.(r_NInner)) [h.(r_LNone); posn (Array.get a 5); x])
  else if is_h f (h.(h_IRenF)) then inner (Array.get a 6) (app (h.(r_NInner)) [reify_lab s (Array.get a 7); slot (Array.get a 8); x])
  else if is_h f (h.(h_IRenB)) then inner (Array.get a 6) (app (h.(r_NInner)) [h.(r_LNone); slot (Array.get a 7); x])
  else if is_h f (h.(h_ISubF)) then
    inner (Array.get a 6)
      (app (h.(r_NInner)) [reify_lab s (Array.get a 7); app (h.(r_NBindE)) [reify_term s (Array.get a 8); pay (Array.get a 9)]; x])
  else if is_h f (h.(h_ISubB)) then
    inner (Array.get a 6)
      (app (h.(r_NInner)) [h.(r_LNone); app (h.(r_NBindE)) [reify_term s (Array.get a 7); pay (Array.get a 8)]; x])
  else Control.zero Not_found

(** [sctx_den s wk]: each entry put on [x], the outermost first. *)
with reify_sctx (s : st) (t : constr) (c : constr) (wk : constr) (x : constr) : constr :=
  let h := s.(heads) in
  let (f, a) := view h c in
  let pay q := app (h.(r_NPComp)) [reify_pctx s t q None wk wk; h.(r_NPId)] in
  let ent y tg := app (h.(r_NInner)) [y; tg; x] in
  let bind u p := app (h.(r_NBindE)) [reify_term s u; p] in
  let payr r := app (h.(r_NPComp)) [reify_adj s t (Array.get a 5) (Array.get a 2) r; h.(r_NPId)] in
  if is_h f (h.(h_SEmpty)) then x
  else if is_h f (h.(h_SLiftF)) then
    let y := reify_lab s (Array.get a 6) in
    reify_sctx s t (Array.get a 5) (app (h.(r_NOuter)) [y; wk])
      (app (h.(r_NInner)) [y; app (h.(r_NVarE)) [y; h.(r_N0)]; app (h.(r_NOuter)) [y; x]])
  else if is_h f (h.(h_SLiftB)) then
    let y := h.(r_LNone) in
    reify_sctx s t (Array.get a 5) (app (h.(r_NOuter)) [y; wk])
      (app (h.(r_NInner)) [y; app (h.(r_NVarE)) [y; h.(r_N0)]; app (h.(r_NOuter)) [y; x]])
  else if is_h f (h.(h_SSubF)) then
    reify_sctx s t (Array.get a 5) wk (ent (reify_lab s (Array.get a 6)) (bind (Array.get a 7) (pay (Array.get a 8))))
  else if is_h f (h.(h_SSubB)) then
    reify_sctx s t (Array.get a 5) wk (ent (h.(r_LNone)) (bind (Array.get a 6) (pay (Array.get a 7))))
  else if is_h f (h.(h_SRenF)) then
    reify_sctx s t (Array.get a 5) wk (ent (reify_lab s (Array.get a 6)) (reify_var s (Array.get a 7)))
  else if is_h f (h.(h_SRenB)) then
    reify_sctx s t (Array.get a 5) wk (ent (h.(r_LNone)) (reify_var s (Array.get a 6)))
  else if is_h f (h.(h_SSubFA)) then
    reify_sctx s t (Array.get a 6) wk (ent (reify_lab s (Array.get a 7)) (bind (Array.get a 8) (payr (Array.get a 9))))
  else if is_h f (h.(h_SSubBA)) then
    reify_sctx s t (Array.get a 6) wk (ent (h.(r_LNone)) (bind (Array.get a 7) (payr (Array.get a 8))))
  else if is_h f (h.(h_SLookF)) then
    reify_sctx s t (Array.get a 6) wk (ent (reify_lab s (Array.get a 7)) (reify_look s t a (Array.get a 8) (Array.get a 9)))
  else if is_h f (h.(h_SLookB)) then
    reify_sctx s t (Array.get a 6) wk (ent (h.(r_LNone)) (reify_look s t a (Array.get a 7) (Array.get a 8)))
  else Control.zero Not_found

(** [rapply_target r w]: [w] a plain variable, [r : adj t K Mb]. *)
with reify_look (s : st) (t : constr) (a : constr array) (w : constr) (r : constr) : constr :=
  let h := s.(heads) in
  let (vf, va) := split_app (reify_var s w) in
  if is_h vf (h.(r_NVarE)) then
    app (h.(r_NLookE)) [Array.get va 0; Array.get va 1; reify_adj s t (Array.get a 5) (Array.get a 2) r]
  else Control.zero Not_found

(** [pctx_den p f wk acc]: [slots] the variables of the slots ([None]: no
    slots). *)
with reify_pctx (s : st) (t : constr) (p : constr) (slots : constr list option) (wk : constr) (acc : constr) : constr :=
  let h := s.(heads) in
  let (f, a) := split_app p in
  if is_h f (h.(h_PEmpty)) then acc
  else if is_h f (h.(h_PRen)) then
    match slots, Constr.Unsafe.kind (Array.get a 4) with
    | Some sl, Constr.Unsafe.Rel r =>
        reify_pctx s t (Array.get a 2) slots wk (app (h.(r_NInner)) [reify_lab s (Array.get a 3); List.nth sl (Int.sub r 1); acc])
    | _, _ => Control.zero Not_found
    end
  else if is_h f (h.(h_PSub)) then
    let q := app (h.(r_NPComp)) [reify_pctx s t (Array.get a 5) slots wk wk; h.(r_NPId)] in
    reify_pctx s t (Array.get a 2) slots wk
      (app (h.(r_NInner)) [reify_lab s (Array.get a 3); app (h.(r_NBindE)) [reify_term s (Array.get a 4); q]; acc])
  else Control.zero Not_found.

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

Ltac2 adj_idx (ty : constr) : constr * constr :=
  lazy_match! ty with adj _ ?a ?b => (a, b) end.

Ltac2 lab_env (labs : constr array) (h : constr) : constr :=
  lazy_match! h with
  | LCon ?s => s
  | LAtom ?n => Array.get labs (int_of_n n)
  end.

Ltac2 is_lnone (h : constr) : bool := lazy_match! h with LNone => true | _ => false end.

Ltac2 refine_c (c : unit -> constr) : unit := Control.refine c; Control.shelve_unifiable ().

Ltac2 intro_as (id : ident) : unit := Std.intros false [Std.IntroNaming (Std.IntroIdentifier id)].

Ltac2 fresh (base : ident) : ident := Fresh.in_goal base.

(** ** Rendering

    A shown normal form, shared definitions and expressions, is built as
    a term directly:
    - a run of entries as a short form over its tail, lifts first:
      [x := u], [x := u⟨| r ⟩], [x as w], [x as w⟨| r ⟩];
    - [x ↦ g₀] over a pop of [g] as [⟦ x | Γ \ g | Γ[σ] ⟧] (a lift when
      [x = g]);
    - pops alone as outputs [⟦ \ y as _ ⟧];
    - composition as [⨾], atoms as written, shared definitions as the
      variables [share] binds.

    The scope indices the constructors take are found first: each is a
    variable plus an offset, and the variables are unified, with the
    atoms' types and the type of the whole fixing their values, as a
    [nat] term with [S]s on it.  The terms are then built: a builder
    takes where the shared definitions are bound (the de Bruijn index of
    each, at the builder's root) and how many binders it is under. *)

Ltac2 Type rec ix := { iid : int; mutable up : (ix * int) option; mutable cst : (constr * int) option; mutable lo : int }.

Ltac2 rec ix_find (x : ix) : ix * int :=
  match x.(up) with
  | None => (x, 0)
  | Some p =>
      let (p, k) := p in
      let (r, k2) := ix_find p in
      let o := Int.add k k2 in
      x.(up) := Some (r, o); (r, o)
  end.

Ltac2 scope_err () := Control.zero (Tactic_failure (Some (Message.of_string "names: no scopes for the rendering"))).

(** The value of [a] is that of [b] plus [k]. *)
Ltac2 ix_eq (a : ix) (b : ix) (k : int) : unit :=
  let (ra, oa) := ix_find a in
  let (rb, ob) := ix_find b in
  let d := Int.sub (Int.add ob k) oa in
  if Int.equal (ra.(iid)) (rb.(iid)) then (if Int.equal d 0 then () else scope_err ())
  else
    (ra.(up) := Some (rb, d);
     let l := Int.add (ra.(lo)) d in
     (if Int.lt l (rb.(lo)) then rb.(lo) := l else ());
     match ra.(cst) with
     | Some c =>
         let (bs, v) := c in
         match rb.(cst) with
         | None => rb.(cst) := Some (bs, Int.sub v d)
         | Some c' => let (bs', v') := c' in
                      if Bool.and (Constr.equal bs bs') (Bool.neg (Int.equal v' (Int.sub v d))) then scope_err () else ()
         end
     | None => ()
     end).

(** The constructors, looked up once. *)
Ltac2 Type kc := {
  kO : constr; kS : constr; kN0 : constr; kAId : constr; kAAtom : constr; kACompose : constr; kAOuter : constr; kAInner : constr;
  kTVarE : constr; kTBindE : constr; kTLookE : constr; kPComp : constr; kPId : constr; kLNone : constr; kLCon : constr;
  kidentity : constr; kcompose : constr; kcform : constr; kcform_id : constr; kshare : constr; kadj : constr;
  kONamF : constr; kONamB : constr; kOEnd : constr; kOEndT : constr; kOPosF : constr; kOPosB : constr;
  kOShort : constr; kOShortT : constr; kIEmpty : constr; kIPosF : constr; kIPosB : constr; kSTail : constr;
  kSEmpty : constr; kSLiftF : constr; kSLiftB : constr; kSSubF : constr; kSSubB : constr; kSRenF : constr;
  kSRenB : constr; kSSubFA : constr; kSSubBA : constr; kSLookF : constr; kSLookB : constr; kPEmpty : constr;
  kbvar : constr; kfvar : constr; kstt : constr; kslot : constr; ktname : constr; kSome : constr; kNone : constr }.

Ltac2 mk_kc () : kc := {
  kO := constr:(O); kS := constr:(S); kN0 := constr:(N0); kAId := constr:(NId); kAAtom := constr:(NAtom); kACompose := constr:(NCompose);
  kAOuter := constr:(NOuter); kAInner := constr:(NInner); kTVarE := constr:(NVarE); kTBindE := constr:(NBindE);
  kTLookE := constr:(NLookE); kPComp := constr:(NPComp); kPId := constr:(NPId); kLNone := constr:(LNone); kLCon := constr:(LCon);
  kidentity := constr:(@identity); kcompose := constr:(@compose); kcform := constr:(@cform); kcform_id := constr:(@cform_id);
  kshare := constr:(@Indexed.share); kadj := constr:(@adj);
  kONamF := constr:(@ONamF); kONamB := constr:(@ONamB); kOEnd := constr:(@OEnd); kOEndT := constr:(@OEndT);
  kOPosF := constr:(@OPosF); kOPosB := constr:(@OPosB); kOShort := constr:(@OShort); kOShortT := constr:(@OShortT);
  kIEmpty := constr:(@IEmpty); kIPosF := constr:(@IPosF); kIPosB := constr:(@IPosB); kSTail := constr:(@STail);
  kSEmpty := constr:(@SEmpty); kSLiftF := constr:(@SLiftF); kSLiftB := constr:(@SLiftB); kSSubF := constr:(@SSubF);
  kSSubB := constr:(@SSubB); kSRenF := constr:(@SRenF); kSRenB := constr:(@SRenB); kSSubFA := constr:(@SSubFA);
  kSSubBA := constr:(@SSubBA); kSLookF := constr:(@SLookF); kSLookB := constr:(@SLookB); kPEmpty := constr:(@PEmpty);
  kbvar := constr:(@bvar); kfvar := constr:(@fvar); kstt := constr:(stt); kslot := constr:(slot); ktname := constr:(tname);
  kSome := constr:(@Some tname); kNone := constr:(@None tname) }.

(** The universe constraints the constructors' applications to [t]
    need, which building terms directly does not add. *)
Ltac2 univs (t : constr) : unit :=
  let _ := '(@identity $t) in let _ := '(@compose $t) in let _ := '(@cform $t) in let _ := '(@cform_id $t) in
  let _ := '(@Indexed.share $t) in let _ := '(@adj $t) in let _ := '(@ONamF $t) in let _ := '(@ONamB $t) in
  let _ := '(@OEnd $t) in let _ := '(@OEndT $t) in let _ := '(@OPosF $t) in let _ := '(@OPosB $t) in
  let _ := '(@OShort $t) in let _ := '(@OShortT $t) in let _ := '(@IEmpty $t) in let _ := '(@IPosF $t) in
  let _ := '(@IPosB $t) in let _ := '(@STail $t) in let _ := '(@SEmpty $t) in let _ := '(@SLiftF $t) in
  let _ := '(@SLiftB $t) in let _ := '(@SSubF $t) in let _ := '(@SSubB $t) in let _ := '(@SRenF $t) in
  let _ := '(@SRenB $t) in let _ := '(@SSubFA $t) in let _ := '(@SSubBA $t) in let _ := '(@SLookF $t) in
  let _ := '(@SLookB $t) in let _ := '(@PEmpty $t) in let _ := '(@share_intro_p $t) in let _ := '(@adj_raw $t) in
  let _ := '(@Adjustment.radj $t) in let _ := '(@adj_eq $t) in let _ := '(@apply_var_bind $t) in
  let _ := '(@CRoot $t) in let _ := '(@CShare $t) in let _ := '(@chain_intro $t) in
  let _ := '(@hshowDB_sound $t) in let _ := '(@hbindB_show_sound $t) in let _ := '(@hlook_varB_sound $t) in
  let _ := '(@aedenB $t) in let _ := '(@braun $t) in let _ := '(@BN $t) in let _ := '(@BE $t) in
  let _ := '(@F2_one (radj $t)) in let _ := '(@F2_app (radj $t)) in let _ := '(@F_one (radj $t)) in let _ := '(@F_app (radj $t)) in
  ().

(** A builder: given the index of each shared definition at its root and
    the binders it is under, a term. *)
Ltac2 Type rnd := {
  rk : kc; rt : constr; rns : nats; mutable rctr : int; rlabs : constr array;
  mutable rterm : int -> (int -> int) -> int -> constr;
  mutable ratoms : (constr * (ix * int) * (ix * int)) array; rnb : int;
  rpos : (int, int) FMap.t; mutable rshty : ((ix * int) * (ix * int)) array }.

Ltac2 new_ix (r : rnd) : ix * int :=
  let i := r.(rctr) in
  r.(rctr) := Int.add i 1;
  ({ iid := i; up := None; cst := None; lo := 0 }, 0).

Ltac2 rec nat_parse (k : kc) (c : constr) : constr * int :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      if Constr.equal f (k.(kS)) then let (b, n) := nat_parse k (Array.get args 0) in (b, Int.add n 1) else (c, 0)
  | _ => (c, 0)
  end.

Ltac2 const_ix (r : rnd) (c : constr) : ix * int :=
  let (x, _) := new_ix r in x.(cst) := Some (nat_parse (r.(rk)) c); (x, 0).

Ltac2 ie_eq (a : ix * int) (b : ix * int) : unit :=
  let (x, ka) := a in let (y, kb) := b in ix_eq x y (Int.sub kb ka).

Ltac2 ie_add (a : ix * int) (k : int) : ix * int := let (x, o) := a in (x, Int.add o k).

Ltac2 rec add_s (r : rnd) (b : constr) (n : int) : constr :=
  let k := r.(rk) in
  if Constr.equal b (k.(kO)) then (if Int.lt n 0 then scope_err () else nat_lit (r.(rns)) n)
  else if Int.equal n 0 then b
  else if Int.lt n 0 then
    match Constr.Unsafe.kind b with
    | Constr.Unsafe.App f args => if Constr.equal f (k.(kS)) then add_s r (Array.get args 0) (Int.add n 1) else scope_err ()
    | _ => scope_err ()
    end
  else app (k.(kS)) [add_s r b (Int.sub n 1)].

(** The value of an index, once all are unified; one no type fixes is
    made as small as it can be. *)
Ltac2 ie_nat (r : rnd) (a : ix * int) : constr :=
  let (x, n) := a in
  let (rx, o) := ix_find x in
  match rx.(cst) with
  | Some c => let (b, v) := c in add_s r b (Int.add v (Int.add o n))
  | None => add_s r (r.(rk).(kO)) (Int.sub (Int.add o n) (rx.(lo)))
  end.

Ltac2 hd_args (c : constr) : constr * constr array :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args => (f, args)
  | _ => (c, Array.make 0 c)
  end.

Ltac2 rel (i : int) : constr := Constr.Unsafe.make (Constr.Unsafe.Rel i).

Ltac2 lam (id : ident) (ty : constr) (b : constr) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.Lambda (Constr.Binder.unsafe_make (Some id) Constr.Binder.Relevant ty) b).

Ltac2 is_lnone' (r : rnd) (h : constr) : bool := Constr.equal h (r.(rk).(kLNone)).

Ltac2 rlab (r : rnd) (h : constr) : constr :=
  let (f, a) := hd_args h in
  if Constr.equal f (r.(rk).(kLCon)) then Array.get a 0 else Array.get (r.(rlabs)) (int_of_n (Array.get a 0)).

(** The variable [gⱼ] in scope [m]. *)
Ltac2 rvar (r : rnd) (g : constr) (j : constr) (m : constr) : constr :=
  let k := r.(rk) in
  let jn := nat_lit (r.(rns)) (int_of_n j) in
  if is_lnone' r g then app (k.(kbvar)) [m; jn; k.(kstt)] else app (k.(kfvar)) [m; rlab r g; jn].

(** [x ↦ g₀] over a pop of [g], [x] not [g]: [(x, g, b)], [b] under the pop. *)
Ltac2 is_ren (r : rnd) (a : constr array) : (constr * constr * constr) option :=
  let k := r.(rk) in
  let x := Array.get a 0 in
  let (th, ta) := hd_args (Array.get a 1) in
  let (bh, ba) := hd_args (Array.get a 2) in
  if Constr.equal th (k.(kTVarE)) then
    if Constr.equal bh (k.(kAOuter)) then
      let g := Array.get ta 0 in
      if Constr.equal (Array.get ta 1) (k.(kN0)) then
        if Constr.equal g (Array.get ba 0) then
          if Constr.equal x g then None else Some (x, g, Array.get ba 1)
        else None
      else None
    else None
  else None.

(** The entries of a short form, outermost first ([None] for a lift),
    and its tail. *)
Ltac2 rec collect_short (r : rnd) (e : constr) (lifts : bool) (acc : (constr * constr option) list) :=
  let k := r.(rk) in
  let (h, a) := hd_args e in
  if Constr.equal h (k.(kAInner)) then
    let x := Array.get a 0 in
    let t := Array.get a 1 in
    let b := Array.get a 2 in
    let (th, ta) := hd_args t in
    let (bh, ba) := hd_args b in
    let pop :=
      if Constr.equal th (k.(kTVarE)) then
        if Constr.equal bh (k.(kAOuter)) then
          if Constr.equal (Array.get ta 1) (k.(kN0)) then Constr.equal (Array.get ta 0) (Array.get ba 0) else false
        else false
      else false in
    if pop then
      if Bool.and lifts (Constr.equal x (Array.get ta 0)) then collect_short r (Array.get ba 1) true ((x, None) :: acc)
      else (acc, e)
    else collect_short r b false ((x, Some t) :: acc)
  else (acc, e).

Ltac2 rec render_a (r : rnd) (e : constr) : (ix * int) * (ix * int) * ((int -> int) -> int -> constr) :=
  let k := r.(rk) in
  let t := r.(rt) in
  let (h, a) := hd_args e in
  if Constr.equal h (k.(kAId)) then
    let n := new_ix r in (n, n, (fun _ _ => app (k.(kidentity)) [t; ie_nat r n]))
  else if Constr.equal h (k.(kAAtom)) then
    let i := int_of_n (Array.get a 0) in
    if Int.lt i (r.(rnb)) then
      let (s, an, am) := Array.get (r.(ratoms)) i in (an, am, (fun _ _ => s))
    else
      let p := match FMap.find_opt i (r.(rpos)) with Some p => p | None => Control.zero Not_found end in
      let (sn, sm) := Array.get (r.(rshty)) p in
      (sn, sm, (fun sb d => rel (Int.add (sb p) d)))
  else if Constr.equal h (k.(kACompose)) then
    let (nx, mx, bx) := render_a r (Array.get a 0) in
    let (ny, my, byy) := render_a r (Array.get a 1) in
    ie_eq my nx;
    (ny, mx, (fun sb d => app (k.(kcompose)) [t; ie_nat r ny; ie_nat r nx; ie_nat r mx; bx sb d; byy sb d]))
  else if Constr.equal h (k.(kAOuter)) then render_outs r e
  else if Constr.equal h (k.(kAInner)) then
    match is_ren r a with
    | Some xgb => let (x, g, b) := xgb in render_ren r x g b
    | None => render_short r e
    end
  else Control.zero Not_found
with render_outs (r : rnd) (e : constr) :=
  let k := r.(rk) in
  let t := r.(rt) in
  let rec coll e acc :=
    let (h, a) := hd_args e in
    if Constr.equal h (k.(kAOuter)) then coll (Array.get a 1) (Array.get a 0 :: acc) else (acc, e) in
  let (ys, tl) := coll e [] in
  let kn := List.length ys in
  let nbd := List.length (List.filter (is_lnone' r) ys) in
  let kk := nat_lit (r.(rns)) kn in
  let z := k.(kO) in
  let sl := app (k.(kslot)) [kk] in
  (* the output names from level [lvl] on, [j] bound ones before *)
  let rec chain ys lvl j jb bt fin nNt nN nM :=
    match ys with
    | [] => fin
    | y :: ys' =>
        let isb := is_lnone' r y in
        let inner := chain ys' (Int.add lvl 1) (if isb then Int.add j 1 else j) jb bt fin nNt nN nM in
        let jc := ie_nat r (ie_add jb j) in
        let nc := nat_lit (r.(rns)) (Int.sub (Int.sub kn lvl) 1) in
        if isb then app (k.(kONamB)) [t; kk; nNt; nN; nM; z; z; jc; nc; bt lvl; lam @a sl inner]
        else app (k.(kONamF)) [t; kk; nNt; nN; nM; z; z; jc; nc; bt lvl; rlab r y; lam @a sl inner]
    end in
  let (th, _) := hd_args tl in
  if Constr.equal th (k.(kAId)) then
    let n := new_ix r in
    let m := ie_add n nbd in
    (n, m, (fun _ _ =>
       let nN := ie_nat r n in
       let nM := ie_nat r m in
       let fin := app (k.(kOEnd)) [t; kk; nN; nN; nM; z; app (k.(kIEmpty)) [t; kk; nM; nN]] in
       let o := chain ys 0 0 n (fun _ => k.(kNone)) fin nN nN nM in
       app (k.(kcform_id)) [t; kk; nN; nN; nM; z; o]))
  else
    let (ns, ms, bs) := render_a r tl in
    let m := ie_add ms nbd in
    (ns, m, (fun sb d =>
       let nN := ie_nat r ns in
       let nMt := ie_nat r ms in
       let nM := ie_nat r m in
       let fin := app (k.(kOEndT)) [t; kk; nN; nN; nM; z; rel (Int.add kn 1); app (k.(kIEmpty)) [t; kk; nM; nN]] in
       let o := chain ys 0 0 ms (fun lvl => app (k.(kSome)) [rel (Int.add lvl 1)]) fin nN nN nM in
       app (k.(kcform)) [t; kk; nN; nMt; nN; nM; z; lam @G (k.(ktname)) o; bs sb d]))
with render_ren (r : rnd) (x : constr) (g : constr) (b : constr) :=
  let k := r.(rk) in
  let t := r.(rt) in
  let xb := is_lnone' r x in
  let gb := is_lnone' r g in
  let one := nat_lit (r.(rns)) 1 in
  let z := k.(kO) in
  let inp nM nNt nN :=
    let i0 := app (k.(kIEmpty)) [t; one; nM; nN] in
    if xb then app (k.(kIPosB)) [t; one; nM; nNt; nN; z; i0]
    else app (k.(kIPosF)) [t; one; nM; nNt; nN; z; i0; rlab r x] in
  let pos fin nNt nN nM j bo :=
    if gb then app (k.(kOPosB)) [t; one; nNt; nN; nM; one; z; j; z; bo; fin]
    else app (k.(kOPosF)) [t; one; nNt; nN; nM; one; z; j; z; bo; fin; rlab r g] in
  let (bh, _) := hd_args b in
  if Constr.equal bh (k.(kAId)) then
    let nt := new_ix r in
    let n := ie_add nt (if xb then 1 else 0) in
    let m := ie_add nt (if gb then 1 else 0) in
    (n, m, (fun _ _ =>
       let (nNt, nN, nM) := (ie_nat r nt, ie_nat r n, ie_nat r m) in
       let fin := app (k.(kOEnd)) [t; one; nNt; nN; nM; one; inp nM nNt nN] in
       app (k.(kcform_id)) [t; one; nNt; nN; nM; one; pos fin nNt nN nM nNt (k.(kNone))]))
  else
    let (ns, ms, bs) := render_a r b in
    let n := ie_add ns (if xb then 1 else 0) in
    let m := ie_add ms (if gb then 1 else 0) in
    (n, m, (fun sb d =>
       let (nNt, nMt, nN, nM) := (ie_nat r ns, ie_nat r ms, ie_nat r n, ie_nat r m) in
       let fin := app (k.(kOEndT)) [t; one; nNt; nN; nM; one; rel 1; inp nM nNt nN] in
       let o := pos fin nNt nN nM nMt (app (k.(kSome)) [rel 1]) in
       app (k.(kcform)) [t; one; nNt; nMt; nN; nM; one; lam @G (k.(ktname)) o; bs sb d]))
with render_short (r : rnd) (e : constr) :=
  let k := r.(rk) in
  let t := r.(rt) in
  let z := k.(kO) in
  let (acc, tl) := collect_short r e true [] in
  let be := List.length (List.filter (fun (x, _) => is_lnone' r x) acc) in
  let bl := List.length (List.filter (fun (x, o) => Bool.and (is_lnone' r x) (match o with None => true | Some _ => false end)) acc) in
  let (th, _) := hd_args tl in
  let notail := Constr.equal th (k.(kAId)) in
  let (nb0, mb0, bs) :=
    if notail then let nt := new_ix r in (nt, nt, (fun _ _ => z)) else render_a r tl in
  let n := ie_add nb0 be in
  let m := ie_add mb0 bl in
  (* the entries from [l] on, [cb] bound ones and [cl] bound lifts before *)
  let rec ents l cb cl : (int -> int) -> int -> constr :=
    match l with
    | [] => (fun _ _ => app (k.(kSEmpty)) [t; ie_nat r n; ie_nat r m])
    | xo :: l' =>
        let (x, o) := xo in
        let xb := is_lnone' r x in
        let nbi := ie_add nb0 cb in
        let mbi := ie_add mb0 cl in
        let cb' := if xb then Int.add cb 1 else cb in
        let hd sb d := [t; ie_nat r nbi; ie_nat r mbi; ie_nat r n; ie_nat r m] in
        match o with
        | None =>
            let inner := ents l' cb' (if xb then Int.add cl 1 else cl) in
            (fun sb d =>
               let s := inner sb d in
               if xb then app (k.(kSLiftB)) (List.append (hd sb d) [s])
               else app (k.(kSLiftF)) (List.append (hd sb d) [s; rlab r x]))
        | Some tm =>
            let inner := ents l' cb' cl in
            let (th, ta) := hd_args tm in
            if Constr.equal th (k.(kTVarE)) then
              (fun sb d =>
                 let s := inner sb d in
                 let w := rvar r (Array.get ta 0) (Array.get ta 1) (ie_nat r mbi) in
                 if xb then app (k.(kSRenB)) (List.append (hd sb d) [s; w])
                 else app (k.(kSRenF)) (List.append (hd sb d) [s; rlab r x; w]))
            else if Constr.equal th (k.(kTBindE)) then
              let u := int_of_n (Array.get ta 0) in
              let (ph, pa) := hd_args (Array.get ta 1) in
              (if Constr.equal ph (k.(kPComp)) then (if Constr.equal (Array.get pa 1) (k.(kPId)) then () else Control.zero Not_found)
               else Control.zero Not_found);
              let rr := Array.get pa 0 in
              let (rh, _) := hd_args rr in
              if Constr.equal rh (k.(kAId)) then
                (fun sb d =>
                   let s := inner sb d in
                   let uc := r.(rterm) u sb d in
                   let q := app (k.(kPEmpty)) [t; z] in
                   if xb then app (k.(kSSubB)) (List.append (hd sb d) [s; uc; q])
                   else app (k.(kSSubF)) (List.append (hd sb d) [s; rlab r x; uc; q]))
              else
                let (nr, mr, br) := render_a r rr in
                ie_eq mr mbi;
                (fun sb d =>
                   let s := inner sb d in
                   let uc := r.(rterm) u sb d in
                   let hk := List.append (hd sb d) [ie_nat r nr] in
                   if xb then app (k.(kSSubBA)) (List.append hk [s; uc; br sb d])
                   else app (k.(kSSubFA)) (List.append hk [s; rlab r x; uc; br sb d]))
            else if Constr.equal th (k.(kTLookE)) then
              let (nr, mr, br) := render_a r (Array.get ta 2) in
              ie_eq mr mbi;
              (fun sb d =>
                 let s := inner sb d in
                 let kr := ie_nat r nr in
                 let w := rvar r (Array.get ta 0) (Array.get ta 1) kr in
                 let hk := List.append (hd sb d) [kr] in
                 if xb then app (k.(kSLookB)) (List.append hk [s; w; br sb d])
                 else app (k.(kSLookF)) (List.append hk [s; rlab r x; w; br sb d]))
            else Control.zero Not_found
        end
    end in
  let es := ents acc 0 0 in
  (n, m, (fun sb d =>
     let (nN, nM) := (ie_nat r n, ie_nat r m) in
     let s := es sb d in
     if notail then
       let nNt := ie_nat r nb0 in
       app (k.(kcform_id)) [t; z; nNt; nN; nM; z; app (k.(kOShort)) [t; z; nNt; nN; nM; z; s]]
     else
       let c := app (k.(kSTail)) [t; nN; nM; ie_nat r nb0; ie_nat r mb0; s; bs sb d] in
       app (k.(kcform_id)) [t; z; z; nN; nM; z; app (k.(kOShortT)) [t; z; z; nN; nM; z; c]])).

(** A rendering: the shared definitions in the order they are bound,
    each with its type and its scope indices, under the binders of those
    before it; the suffixes of the whole ([share]s from the [i]th on, the
    last the root alone), each under the binders before it; the whole. *)
Ltac2 Type rendered := {
  rd_k : int; rd_tys : constr array; rd_kl : (constr * constr) array; rd_defs : constr array;
  rd_sufs : constr array; rd_term : constr; rd_chain : constr }.

(** [render_all t ns labs terms atoms nb shs roots term_of]: the shared
    definitions [shs] (atom numbers and expressions, in the order they are
    bound) and the expressions [roots] (with their scope indices), the
    last the root; [term_of] gives the terms, from the builders of the
    roots. *)
Ltac2 render_all (t : constr) (ns : nats) (labs : constr array) (atoms : constr array) (nb : int)
    (shs : (int * constr) list) (roots : (constr * constr * constr) list)
    (term_of : ((int -> int) -> int -> constr) list -> int -> (int -> int) -> int -> constr) : rendered * ((int -> int) -> int -> constr) list :=
  let k := mk_kc () in
  univs t;
  let shn := List.length shs in
  let pos := List.fold_left (fun acc (i, j) => FMap.add j i acc) (FMap.empty FSet.Tags.int_tag)
               (List.combine (List.init shn (fun i => i)) (List.map (fun (j, _) => j) shs)) in
  let r := { rk := k; rt := t; rns := ns; rctr := 0; rlabs := labs; rterm := (fun _ _ _ => k.(kO));
             ratoms := Array.of_list []; rnb := nb; rpos := pos; rshty := Array.of_list [] } in
  r.(ratoms) := Array.map (fun a =>
      let s := lazy_match! a with adj_raw ?s => s end in
      let (an, am) := adj_idx (Constr.type s) in
      (s, const_ix r an, const_ix r am)) atoms;
  let shty := Array.init shn (fun _ => let x := new_ix r in (x, new_ix r)) in
  r.(rshty) := shty;
  let dbs := List.map (fun (j, d) =>
      let (n, m, b) := render_a r d in
      let (sn, sm) := Array.get shty (Option.get (FMap.find_opt j pos)) in
      ie_eq n sn; ie_eq m sm; b) shs in
  let rbs := List.map (fun (e, rn, rm) =>
      let (n, m, b) := render_a r e in
      ie_eq n (const_ix r rn); ie_eq m (const_ix r rm); b) roots in
  r.(rterm) := term_of rbs;
  let (rn, rm) := let (_, rn, rm) := List.last roots in (rn, rm) in
  let kl := Array.map (fun (sn, sm) => (ie_nat r sn, ie_nat r sm)) shty in
  let tys := Array.map (fun (a, b) => app (k.(kadj)) [t; a; b]) kl in
  let defs := Array.of_list (List.mapi (fun i b => b (fun p => Int.sub i p) 0) dbs) in
  let sufs := Array.make (Int.add shn 1) (k.(kO)) in
  Array.set sufs shn ((List.last rbs) (fun p => Int.sub shn p) 0);
  let rec nest i :=
    if Int.lt i 0 then () else
    let (a, b) := Array.get kl i in
    Array.set sufs i (app (k.(kshare)) [t; rn; rm; a; b; Array.get defs i; lam @r (Array.get tys i) (Array.get sufs (Int.add i 1))]);
    nest (Int.sub i 1) in
  nest (Int.sub shn 1);
  let rec chain i :=
    if Int.equal i shn then app constr:(@CRoot) [t; rn; rm; Array.get sufs shn]
    else let (a, b) := Array.get kl i in
         app constr:(@CShare) [t; rn; rm; a; b; Array.get defs i; lam @r (Array.get tys i) (chain (Int.add i 1))] in
  ({ rd_k := shn; rd_tys := tys; rd_kl := kl; rd_defs := defs; rd_sufs := sufs; rd_term := Array.get sufs 0;
     rd_chain := chain 0 }, rbs).

(** The closed terms [terms]. *)
Ltac2 closed_terms (terms : constr array) : ((int -> int) -> int -> constr) list -> int -> (int -> int) -> int -> constr :=
  fun _ i _ _ => Array.get terms i.

(** [render_term t ty labs terms atoms nb shd root]: the rendering of the
    shared definitions [shd] (the atoms from [nb] on) and [root], of type
    [ty]. *)
Ltac2 render_term (t : constr) (ty : constr) (ns : nats) (labs : constr array) (terms : constr array) (atoms : constr array) (nb : int)
    (shd : constr list) (root : constr) : rendered :=
  let (n, m) := adj_idx ty in
  let shs := List.mapi (fun i d => (Int.add nb i, d)) shd in
  let (rd, _) := render_all t ns labs atoms nb shs [(root, n, m)] (closed_terms terms) in rd.

(** ** Proofs about renderings

    For a rendering [b] with shared definitions, a proof of [P b] from
    one of [P] of its root, with each [share] as a variable [r] and a
    hypothesis that [r] is its definition, by [chain_intro]: the
    variables and hypotheses are bound alternately.  [inner rs hs root]
    is the proof for the root, given the variables (as [adj_raw r]) and
    the hypotheses, in the order they are bound. *)
Ltac2 share_proof (t : constr) (n : constr) (m : constr) (p : constr) (rd : rendered)
    (inner : constr list -> constr list -> constr -> constr) : constr :=
  let k := rd.(rd_k) in
  let raw := constr:(@adj_raw) in
  (* the [j]th variable from the inside is the [2j]th binder: the
     definitions and the root use only the variables bound before them *)
  let rels := List.init k (fun j => rel (Int.mul 2 (Int.add j 1))) in
  let eqc := constr:(@eq) in
  let rty := app constr:(@Adjustment.radj) [t] in
  let rec lvl i :=
    if Int.equal i k then
      let root := Constr.Unsafe.substnl rels 0 (Array.get (rd.(rd_sufs)) k) in
      let rs := List.init k (fun j => let (a, b) := Array.get (rd.(rd_kl)) j in app raw [t; a; b; rel (Int.mul 2 (Int.sub k j))]) in
      let hs := List.init k (fun j => rel (Int.sub (Int.mul 2 (Int.sub k j)) 1)) in
      inner rs hs root
    else
      let (a, b) := Array.get (rd.(rd_kl)) i in
      let ty := Array.get (rd.(rd_tys)) i in
      let d := Constr.Unsafe.substnl rels 0 (Array.get (rd.(rd_defs)) i) in
      let hty := app eqc [rty; app raw [t; a; b; rel 1]; app raw [t; a; b; Constr.Unsafe.liftn 1 1 d]] in
      lam @r ty (lam @H hty (lvl (Int.add i 1))) in
  app constr:(@chain_intro) [t; n; m; p; rd.(rd_chain); lvl 0].

(** [Forall2 rel xs ys] from proofs [hs] of [rel x y]. *)
(** [let _ : ty := v in b]. *)
Ltac2 let_in (ty : constr) (v : constr) (b : constr) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.LetIn (Constr.Binder.unsafe_make None Constr.Binder.Relevant ty) v b).

(** [Forall2 rl xs ys] from proofs [hs] of [rl x y], as a balanced tree of
    [F2_app]s, with [rl] bound once. *)
Ltac2 forall2_proof (aty : constr) (bty : constr) (rl : constr) (xs : constr list) (ys : constr list) (hs : constr list) : constr :=
  match xs with
  | [] => app constr:(@Forall2_nil) [aty; bty; rl]
  | _ =>
      let lift c := Constr.Unsafe.liftn 1 1 c in
      let xa := Array.of_list (List.map lift xs) in
      let ya := Array.of_list (List.map lift ys) in
      let ha := Array.of_list (List.map lift hs) in
      let r := rel 1 in
      let nil_a := app constr:(@nil) [aty] in
      let nil_b := app constr:(@nil) [bty] in
      let rec go i j :=
        if Int.equal (Int.sub j i) 1 then
          let (x, y) := (Array.get xa i, Array.get ya i) in
          (app constr:(@F2_one) [aty; bty; r; x; y; Array.get ha i],
           app constr:(@cons) [aty; x; nil_a], app constr:(@cons) [bty; y; nil_b])
        else
          let mid := Int.div (Int.add i j) 2 in
          let (p1, l1, m1) := go i mid in
          let (p2, l2, m2) := go mid j in
          (app constr:(@F2_app) [aty; bty; r; l1; l2; m1; m2; p1; p2],
           app constr:(@List.app) [aty; l1; l2], app constr:(@List.app) [bty; m1; m2]) in
      let (pf, _, _) := go 0 (Array.length xa) in
      let_in '($aty -> $bty -> Prop) rl pf
  end.

(** [Forall pr xs] from proofs [hs] of [pr x], the same way. *)
Ltac2 forall_proof (aty : constr) (pr : constr) (xs : constr list) (hs : constr list) : constr :=
  match xs with
  | [] => app constr:(@Forall_nil) [aty; pr]
  | _ =>
      let lift c := Constr.Unsafe.liftn 1 1 c in
      let xa := Array.of_list (List.map lift xs) in
      let ha := Array.of_list (List.map lift hs) in
      let r := rel 1 in
      let nil_a := app constr:(@nil) [aty] in
      let rec go i j :=
        if Int.equal (Int.sub j i) 1 then
          let x := Array.get xa i in
          (app constr:(@F_one) [aty; r; x; Array.get ha i], app constr:(@cons) [aty; x; nil_a])
        else
          let mid := Int.div (Int.add i j) 2 in
          let (p1, l1) := go i mid in
          let (p2, l2) := go mid j in
          (app constr:(@F_app) [aty; r; l1; l2; p1; p2], app constr:(@List.app) [aty; l1; l2]) in
      let (pf, _) := go 0 (Array.length xa) in
      let_in '($aty -> Prop) pr pf
  end.

(** ** Environments *)

(** [xs] as a Braun tree: [bof xs]. *)
Ltac2 rec btree (ty : constr) (xs : constr list) : constr :=
  match xs with
  | [] => app constr:(@BE) [ty]
  | x :: rest =>
      let rec halves l :=
        match l with
        | [] => ([], [])
        | y :: l' => let (a, b) := halves l' in (y :: b, a)
        end in
      let (od, ev) := halves rest in
      app constr:(@BN) [ty; x; btree ty od; btree ty ev]
  end.

(** What reification gives: the environments as lists and as trees, the
    facts [l] with a proof [hl] of [lfacts_okB lt l], and the
    environments' entries. *)
Ltac2 Type env := {
  e_le : constr; e_te : constr; e_ae : constr; e_pe : constr; e_l : constr; e_hl : constr;
  e_lt : constr; e_tt : constr; e_pt : constr;
  e_labs : constr array; e_terms : constr list; e_atoms : constr array; e_nt : int; e_nb : int; e_ns : nats;
  e_defs : constr; e_defl : constr option list }.

Ltac2 finish (s : st) (ty : constr) : env :=
  let fs := collect_facts s in
  let labs := List.rev ((s.(labs)).(items)) in
  let terms := List.rev ((s.(terms)).(items)) in
  let atoms := List.rev ((s.(atoms)).(items)) in
  let patoms := List.rev ((s.(patoms)).(items)) in
  let le := list_of constr:(label) labs in
  let te := list_of ty terms in
  let ae := list_of constr:(radj $ty) atoms in
  let pe := list_of constr:(rpadj $ty) patoms in
  let lt := btree constr:(label) labs in
  let defl := List.init ((s.(atoms)).(size)) (fun k => FMap.find_opt k (s.(sdefs))) in
  let defl_c := List.map (fun od => match od with
                                   | Some d => app constr:(@Some aexpN) [d]
                                   | None => constr:(@None aexpN)
                                   end) defl in
  let lty := constr:((lexp * lexp)%type) in
  let pair := constr:(@pair lexp lexp) in
  let cons := constr:(@cons) in
  let l := List.fold_right (fun (x, y, _) tl => app cons [lty; app pair [x; y]; tl]) fs (app constr:(@nil) [lty]) in
  let pr := '(fun pr : lexp * lexp => let '(x, y) := pr in olabel_lt (ldenB $lt x) (ldenB $lt y)) in
  let hl := forall_proof lty pr (List.map (fun (x, y, _) => app pair [x; y]) fs) (List.map (fun (_, _, id) => Control.hyp id) fs) in
  { e_le := le; e_te := te; e_ae := ae; e_pe := pe; e_l := l; e_hl := hl;
    e_lt := lt; e_tt := btree ty terms; e_pt := btree constr:(rpadj $ty) patoms;
    e_labs := Array.of_list labs; e_terms := terms; e_atoms := Array.of_list atoms;
    e_nt := (s.(terms)).(size); e_nb := (s.(atoms)).(size); e_ns := s.(ns);
    e_defs := list_of constr:(option aexpN) defl_c; e_defl := defl }.

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
Ltac2 nocast (c : constr) : constr :=
  match Constr.Unsafe.kind c with Constr.Unsafe.Cast c' _ _ => c' | _ => c end.

Ltac2 rewrite_with (pf : constr) : unit :=
  lazy_match! Constr.type pf with
  | @eq ?ty ?lhs ?rhs =>
      Std.pattern [(lhs, Std.AllOccurrences)] (concl ());
      lazy_match! goal with
      | [ |- ?p _ ] =>
          match Constr.Unsafe.kind p with
          | Constr.Unsafe.Lambda _ body =>
              let g := Constr.Unsafe.substnl [rhs] 0 body in
              (* the new goal as an evar, the old one closed with no check:
                 [refine] would type check the whole term *)
              let ev := nocast '(_ : $g) in
              let evid := match Constr.Unsafe.kind ev with
                          | Constr.Unsafe.Evar e _ => e
                          | _ => Control.zero Not_found
                          end in
              Std.exact_no_check (app constr:(@eq_ind_r) [ty; rhs; p; ev; lhs; pf]);
              Control.new_goal evid
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

(** ** Reading results back *)

(** A shown normal form: the shared definitions (as a list and as a
    Gallina list) and the expression. *)
Ltac2 Type shown := { sh_l : constr list; sh_c : constr; sh_root : constr; sh_val : constr }.

Ltac2 mk_shown (sh : constr) (r : constr) : shown :=
  { sh_l := of_list sh; sh_c := sh; sh_root := r; sh_val := app constr:(@pair (list aexpN) aexpN) [sh; r] }.

(** [c : option (list aexpN * aexpN)], computed. *)
Ltac2 vm_show (c : constr) : shown option :=
  lazy_match! Std.eval_vm None c with
  | Some (?sh, ?r) => Some (mk_shown sh r)
  | None => None
  end.

(** [c : option (N * (list aexpN * aexpN))], computed. *)
Ltac2 vm_pay (c : constr) : (constr * shown) option :=
  lazy_match! Std.eval_vm None c with
  | Some (?u, (?sh, ?r)) => Some (u, mk_shown sh r)
  | None => None
  end.

Ltac2 some (ty : constr) (x : constr) : constr := app constr:(@Some) [ty; x].

(** [Forall2 (fun x od => od = Some d -> x = aeden d) atoms defs]: each
    defined atom is (convertibly) its definition. *)
Ltac2 defs_proof (t : constr) (rel : constr) (atoms : constr list) (defl : constr option list) : constr :=
  let aty := app constr:(@radj) [t] in
  let oty := constr:(option aexpN) in
  let ys := List.map (fun od => match od with Some d => app constr:(@Some aexpN) [d] | None => constr:(@None aexpN) end) defl in
  let hs := List.map2 (fun x od => match od with Some _ => app constr:(@eq_refl) [aty; x] | None => constr:(I) end) atoms defl in
  forall2_proof aty oty rel atoms ys hs.

(** ** Rewriting an adjustment to its normal form *)

Ltac2 Type outcome := [ Shown (constr list) | NotShown ].

(** The normal forms [names] has produced: rewriting them again would
    give them back. *)
Ltac2 Type memo := { mutable seen : constr list }.

(** [a = b], [b] the rendering of the normal form of [a], rewritten in the
    goal; the terms of [b]. *)
(** [eq_refl x : x = y], [y] a computation the kernel does. *)
Ltac2 refl (ty : constr) (x : constr) : constr := app constr:(@eq_refl) [ty; x].

Ltac2 show_adj (memo : memo) (a : constr) : outcome :=
  lazy_match! Constr.type a with
  | adj ?t ?n ?m =>
      let ty := Constr.type a in
      let s := new_st () in
      let e := reify_adj s t n m a in
      let en := (finish s t) in
      let ns := en.(e_ns) in
      let nt := nat_lit ns (en.(e_nt)) in
      let nb := nat_lit ns (en.(e_nb)) in
      let l := en.(e_l) in
      let defs := en.(e_defs) in
      let d := vm_show '(hshowDN (order_of $l) $nt $nb $defs $e) in
      match d with
      | Some sh =>
          let (shd, root) := (sh.(sh_c), sh.(sh_root)) in
          let terms := en.(e_terms) in
          let rd := (render_term t ty ns (en.(e_labs)) (Array.of_list terms) (en.(e_atoms)) (en.(e_nb)) (sh.(sh_l)) root) in
          let b := rd.(rd_term) in
          memo.(seen) := (b :: (memo.(seen)));
          (if Constr.equal a b then () else
           let id := fresh @E in
           let (le, te, ae, pe, hl) := (en.(e_le), en.(e_te), en.(e_ae), en.(e_pe), en.(e_hl)) in
           let (lt, tt, pt) := (en.(e_lt), en.(e_tt), en.(e_pt)) in
           let sty := constr:((list aexpN * aexpN)%type) in
           let ht := vm_eq '(option $sty) '(hshowDN (order_of $l) (List.length $te) (List.length $ae) $defs $e) (some sty (sh.(sh_val))) in
           let rty := '(radj $t) in
           let q := '(fun (rs : list (radj $t)) (Ae : braun (radj $t))
                          (hLe : $lt = bof $le) (hTe : $tt = bof $te) (hAe : Ae = bof ($ae ++ rs)) (hPe : $pt = bof $pe)
                          (hd : Forall2 (fun x od => match od with Some d => x = aedenB $lt $tt Ae $pt d | None => True end) $ae $defs)
                          (hs : Forall2 (fun z0 d0 => z0 = aedenB $lt $tt Ae $pt d0) rs $shd) =>
                        hshowDB_sound $le $te $ae rs $pe $lt $tt Ae $pt hLe hTe hAe hPe $l $defs $e $shd $root $hl $ht hd hs) in
           let hrel := '(fun (Ae : braun (radj $t)) (x : radj $t) (od : option aexpN) =>
                           match od with Some d => x = aedenB $lt $tt Ae $pt d | None => True end) in
           let srel := '(fun (Ae : braun (radj $t)) (z0 : radj $t) (d0 : aexpN) => z0 = aedenB $lt $tt Ae $pt d0) in
           let p := '(fun x : $ty => $a = x) in
           let atoms := Array.to_list (en.(e_atoms)) in
           let pf := share_proof t n m p rd (fun rs hs root' =>
             let rsl := list_of rty rs in
             let at_ := btree rty (List.append atoms rs) in
             let hd := defs_proof t (app hrel [at_]) atoms (en.(e_defl)) in
             let hsp := forall2_proof rty constr:(aexpN) (app srel [at_]) rs (sh.(sh_l)) hs in
             app constr:(@adj_eq) [t; n; m; a; root';
               app q [rsl; at_; refl constr:(braun label) lt; refl '(braun $t) tt; refl '(braun (radj $t)) at_;
                      refl '(braun (rpadj $t)) pt; hd; hsp]]) in
           assert_by id '($a = $b) (fun () => Std.exact_no_check pf);
           (rewrite_with (Control.hyp id)); Std.clear [id]);
          Shown terms
      | None => NotShown
      end
  end.

(** ** Candidates

    Adjustment expressions in [c] not inside another, and closed (so not
    under a binder they use). *)
Ltac2 Type heads := { h_comp : constr; h_cid : constr; h_cf : constr; h_at : constr; h_sh : constr }.

Ltac2 adj_heads () : heads :=
  { h_comp := constr:(@compose); h_cid := constr:(@cform_id); h_cf := constr:(@cform); h_at := constr:(@at_scope);
    h_sh := constr:(@Indexed.share) }.

(** An adjustment expression's head: [⨾], a context form, [at_scope] or
    [share]. *)
Ltac2 is_adj_head_in (hs : heads) (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f _ =>
      let (f, _) := match Constr.Unsafe.kind f with Constr.Unsafe.App g a => (g, a) | _ => (f, Array.make 0 f) end in
      if Constr.equal f (hs.(h_comp)) then true
      else if Constr.equal f (hs.(h_cid)) then true
      else if Constr.equal f (hs.(h_cf)) then true
      else if Constr.equal f (hs.(h_at)) then true
      else Constr.equal f (hs.(h_sh))
  | _ => false
  end.

Ltac2 is_adj_head (c : constr) : bool := is_adj_head_in (adj_heads ()) c.

Ltac2 add_new (c : constr) (acc : constr list) : constr list :=
  if List.exist (Constr.equal c) acc then acc else c :: acc.

Ltac2 rec cands (p : constr -> bool) (c : constr) (acc : constr list) : constr list :=
  if (if p c then Constr.Unsafe.is_closed c else false) then add_new c acc
  else
    let r := { contents := acc } in
    Constr.Unsafe.iter (fun x => r.(contents) := cands p x (r.(contents))) c;
    r.(contents).

Ltac2 candidates (p : constr -> bool) (c : constr) : constr list := List.rev (cands p c []).

(** The same, not looking inside the subterms [stop] holds of. *)
Ltac2 rec cands_stop (p : constr -> bool) (stop : constr -> bool) (c : constr) (acc : constr list) : constr list :=
  if (if p c then Constr.Unsafe.is_closed c else false) then add_new c acc
  else if stop c then acc
  else
    let r := { contents := acc } in
    Constr.Unsafe.iter (fun x => r.(contents) := cands_stop p stop x (r.(contents))) c;
    r.(contents).

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
  let hs := adj_heads () in
  List.iter
    (fun a =>
       if List.exist (Constr.equal a) (memo.(seen)) then () else
       Notations.try0 (fun () =>
         match show_adj memo a with
         | Shown terms => List.iter (fun u => rewrite_each memo (candidates (is_adj_head_in hs) u)) terms
         | NotShown => rewrite_each memo (candidates_in (is_adj_head_in hs) a)
         end))
    cs.

Ltac2 names_adjs (memo : memo) : unit := let hs := adj_heads () in rewrite_each memo (candidates (is_adj_head_in hs) (Control.goal ())).

(** ** Variables *)

Ltac2 rec nth_c (l : constr list) (i : int) : constr := List.nth l i.

(** [apply_var a v]: when the normal form of [a] sends [v] to a variable
    or a term, an equation [id : apply_var a v = ...] for it. *)
Ltac2 var_eq (t : constr) (id : ident) : unit :=
  lazy_match! t with
  | @apply_var ?ty _ ?m ?a ?v =>
      let n := lazy_match! Constr.type a with adj _ ?n _ => n end in
      let s := new_st () in
      let (eh, i) :=
        let (vf, va) := split_app (reify_var s v) in
        if Constr.equal vf (s.(heads).(r_NVarE)) then (Array.get va 0, nat_lit (s.(ns)) (int_of_n (Array.get va 1)))
        else Control.zero Not_found in
      let e := reify_adj s ty n m a in
          let en := finish s ty in
          let nt := nat_lit (en.(e_ns)) (en.(e_nt)) in
          let nb := nat_lit (en.(e_ns)) (en.(e_nb)) in
          let (le, te, ae, pe, l, hl) := (en.(e_le), en.(e_te), en.(e_ae), en.(e_pe), en.(e_l), en.(e_hl)) in
          let (lt, tt, pt) := (en.(e_lt), en.(e_tt), en.(e_pt)) in
          let rty := '(radj $ty) in
          let atoms := Array.to_list (en.(e_atoms)) in
          univs ty;
          let res := Std.eval_vm None '(hlook_varN (order_of $l) $nt $e $eh $i) in
          lazy_match! res with
          | Some (?h', ?j) =>
              let w := if is_lnone h' then '(@bvar $m $j stt)
                       else let x := lab_env (en.(e_labs)) h' in '(@fvar $m $x $j) in
              assert_by id '(apply_var $a $v = Rename $w) (fun () =>
                refine_c (fun () => '(apply_var_rename _ _ _ _));
                let hv := vm_eq '(option (lexp * nat)) '(hlook_varN (order_of $l) (List.length $te) $e $eh $i) res in
                let at_ := btree rty atoms in
                Std.exact_no_check
                  (app constr:(@hlook_varB_sound)
                     [ty; le; te; ae; pe; lt; tt; at_; pt; l; e; eh; i; h'; j;
                      refl constr:(braun label) lt; refl '(braun $ty) tt; refl '(braun (radj $ty)) at_;
                      refl '(braun (rpadj $ty)) pt; hl; hv]))
          | None =>
              match vm_pay '(hlook_payN (order_of $l) $nt $nb $e $eh $i) with
              | Some (u, sh) =>
                  let (shd, root) := (sh.(sh_c), sh.(sh_root)) in
                  let terms := en.(e_terms) in
                  let rd := render_term ty '(adj $ty 0 $m) (en.(e_ns)) (en.(e_labs)) (Array.of_list terms) (en.(e_atoms)) (en.(e_nb)) (sh.(sh_l)) root in
                  let b := rd.(rd_term) in
                  let x := nth_c terms (int_of_n u) in
                  let n := lazy_match! Constr.type a with adj _ ?n _ => n end in
                  let pty := constr:((N * (list aexpN * aexpN))%type) in
                  let hp := vm_eq '(option $pty)
                              '(hlook_payN (order_of $l) (List.length $te) (List.length $ae) $e $eh $i)
                              (some pty (app constr:(@pair N (list aexpN * aexpN)) [u; sh.(sh_val)])) in
                  let q := '(fun (rs : list (radj $ty)) (Ae : braun (radj $ty))
                                 (hLe : $lt = bof $le) (hTe : $tt = bof $te) (hAe : Ae = bof ($ae ++ rs)) (hPe : $pt = bof $pe)
                                 (hs : Forall2 (fun z0 d0 => z0 = aedenB $lt $tt Ae $pt d0) rs $shd) =>
                               hbindB_show_sound $le $te $ae rs $pe $lt $tt Ae $pt hLe hTe hAe hPe $l $e $eh $i $u $shd $root $x
                                 $hl $hp hs eq_refl) in
                  let srel := '(fun (Ae : braun (radj $ty)) (z0 : radj $ty) (d0 : aexpN) => z0 = aedenB $lt $tt Ae $pt d0) in
                  let p := '(fun y : adj $ty 0 $m => rapply (adj_raw $a) (var_raw $v) = inr ($x, rpcompose (adj_raw y) (padj_raw (@pid $ty 0)))) in
                  let pf := share_proof ty constr:(O) m p rd (fun rs hs _ =>
                    let rsl := list_of rty rs in
                    let at_ := btree rty (List.append atoms rs) in
                    app q [rsl; at_; refl constr:(braun label) lt; refl '(braun $ty) tt; refl '(braun (radj $ty)) at_;
                           refl '(braun (rpadj $ty)) pt; forall2_proof rty constr:(aexpN) (app srel [at_]) rs (sh.(sh_l)) hs]) in
                  let fin := app constr:(@apply_var_bind) [ty; n; m; constr:(O); a; v; x; b; '(@pid $ty 0); pf] in
                  assert_by id '(apply_var $a $v = Bind $x (pcompose $b pid)) (fun () => Std.exact_no_check fin)
              | None => Control.zero Not_found
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
  let hs := adj_heads () in
  (* substitution nodes are looked for outside adjustments *)
  if first (List.rev (cands_stop p (is_adj_head_in hs) (Control.goal ()) [])) then each_until_fail p f else ().

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
            let r := match Constr.Unsafe.kind f with
                     | Constr.Unsafe.Lambda _ b => Constr.Unsafe.substnl [w] 0 b
                     | _ => app f [w]
                     end in
            rewrite_with '(eval_rename $f $g $a $v $w $hid : _ = $r); Std.clear [id]
        | _ = Bind ?x ?rho => rewrite_with '(eval_bind $f $g $a $v $x $rho $hid); Std.clear [id]
        end
    end).

(** ** Materialising

    An adjustment [A] to the closed scope with terms with payload
    adjustments, used in a substitution, is replaced by [A'] where the
    first such term [u⟨b⟩] is [u [b]], for a substitution node
    [csubst L a t] (built with the syntax's [L]). *)
Ltac2 mat_one (node : constr) : unit :=
  let (_, na) := split_app node in
  let (term, vr, sub, g, lw, n, a) :=
    (Array.get na 0, Array.get na 1, Array.get na 2, Array.get na 3, Array.get na 4, Array.get na 5, Array.get na 7) in
  let ty := app term [constr:(O)] in
  (
      let s := new_st () in
      let e := reify_adj s ty n constr:(O) a in
      let en := finish s ty in
      let ns := en.(e_ns) in
      let (le, te, ae, pe, l, hl) := (en.(e_le), en.(e_te), en.(e_ae), en.(e_pe), en.(e_l), en.(e_hl)) in
      let n1 := nat_lit ns (en.(e_nt)) in
      let n2 := nat_lit ns (Int.add (en.(e_nt)) 1) in
      let nb := nat_lit ns (en.(e_nb)) in
      match vm_show '(hmat_displayN (order_of $l) $n2 $nb $e $n1) with
      | Some dsh =>
          let (sh', r') := (dsh.(sh_c), dsh.(sh_root)) in
          let shl := dsh.(sh_l) in
          let nbbi := Int.add (en.(e_nb)) (List.length shl) in
          let nbb := nat_lit ns nbbi in
          match vm_pay '(hmat_targetN (order_of $l) $n1 $nbb $e) with
          | Some (u, bsh) =>
              let (shb, rb) := (bsh.(sh_c), bsh.(sh_root)) in
              let terms := en.(e_terms) in
              let ut := nth_c terms (int_of_n u) in
              (* [u [b]] as the node, as a function of [b] *)
              let csub := constr:(@csubst) in
              let mk_x bt := app csub [term; vr; sub; g; lw; constr:(O); constr:(O); bt; ut] in
              let xf := '(fun b : adj $ty 0 0 => @csubst $term $vr $sub $g $lw 0 0 b $ut) in
              let nt := en.(e_nt) in
              let tarr := Array.of_list terms in
              let term_of rbs i sb d := if Int.equal i nt then mk_x ((List.hd rbs) sb d) else Array.get tarr i in
              (* the payload's shared definitions are bound first, as the payload is in a term of the rest *)
              let nsb := List.length (bsh.(sh_l)) in
              let shs := List.append (List.mapi (fun i d => (Int.add nbbi i, d)) (bsh.(sh_l)))
                                     (List.mapi (fun i d => (Int.add (en.(e_nb)) i, d)) shl) in
              let (rd, rbs) := render_all ty ns (en.(e_labs)) (en.(e_atoms)) (en.(e_nb)) shs
                                 [(rb, constr:(O), constr:(O)); (r', n, constr:(O))] term_of in
              let a' := rd.(rd_term) in
              let hid := fresh @H in
              let pty := constr:((N * (list aexpN * aexpN))%type) in
              let sty := constr:((list aexpN * aexpN)%type) in
              let ht := vm_eq '(option $pty) '(hmat_targetN (order_of $l) $n1 $nbb $e)
                          (some pty (app constr:(@pair N (list aexpN * aexpN)) [u; bsh.(sh_val)])) in
              let hd := vm_eq '(option $sty) '(hmat_displayN (order_of $l) $n2 (List.length $ae) $e $n1) (some sty (dsh.(sh_val))) in
              let rty := '(radj $ty) in
              let (lt, pt) := (en.(e_lt), en.(e_pt)) in
              let q := '(fun (rs : list (radj $ty)) (b : adj $ty 0 0) (Ae : braun (radj $ty)) (Te : braun $ty)
                             (hLe : $lt = bof $le) (hTe : Te = bof ($te ++ [$xf b])) (hAe : Ae = bof ($ae ++ rs)) (hPe : $pt = bof $pe)
                             (hs : Forall2 (fun z0 d0 => z0 = aedenB $lt Te Ae $pt d0) rs ($sh' ++ $shb))
                             (hu : bnth Te $u = Some $ut)
                             (hx : bnth Te (N.of_nat $n1) = Some (@csubst $term $vr $sub $g $lw 0 0 b $ut))
                             (hb : adj_raw b = aedenB $lt Te Ae $pt $rb)
                             (v : var $n) =>
                           hmatB_show_sound $le ($te ++ [$xf b]) $ae rs $pe $lt Te Ae $pt hLe hTe hAe hPe $g $l $e $n1 $u
                             $shb $rb $sh' $r' $nbb $n1 $n2 $hl (le_S _ _ (le_n _)) (le_n _) $ht $hd eq_refl hs
                             (@mat_kB $term $vr $sub $g $lw Te $u (N.of_nat $n1) $ut b _ hu hx hb) (var_raw v)) in
              let srel := '(fun (Te : braun $ty) (Ae : braun (radj $ty)) (z0 : radj $ty) (d0 : aexpN) =>
                              z0 = aedenB $lt Te Ae $pt d0) in
              let hxf := '(fun b : adj $ty 0 0 => @eq_refl (option $ty) (Some (@csubst $term $vr $sub $g $lw 0 0 b $ut))) in
              let p := '(fun y : adj $ty $n 0 => forall v : var $n, mrel $g (rapply (adj_raw $a) (var_raw v)) (rapply (adj_raw y) (var_raw v))) in
              let atoms := Array.to_list (en.(e_atoms)) in
              let pf := share_proof ty n constr:(O) p rd (fun rs hs _ =>
                let k := rd.(rd_k) in
                let bt := Constr.Unsafe.substnl (List.init k (fun j => rel (Int.mul 2 (Int.add j 1)))) 0
                            ((List.hd rbs) (fun p => Int.sub k p) 0) in
                let ord l := List.append (List.skipn nsb l) (List.firstn nsb l) in
                let rs := ord rs in
                let rsl := list_of rty rs in
                let at_ := btree rty (List.append atoms rs) in
                let tt := btree ty (List.append terms [mk_x bt]) in
                let hsp := forall2_proof rty constr:(aexpN) (app srel [tt; at_]) rs (List.append shl (bsh.(sh_l))) (ord hs) in
                app q [rsl; bt; at_; tt; refl constr:(braun label) lt; refl '(braun $ty) tt; refl '(braun (radj $ty)) at_;
                       refl '(braun (rpadj $ty)) pt; hsp; refl '(option $ty) (app constr:(@Some) [ty; ut]); app hxf [bt];
                       refl rty (app constr:(@adj_raw) [ty; constr:(O); constr:(O); bt])]) in
              assert_by hid '(forall v : var $n, mrel $g (rapply (adj_raw $a) (var_raw v)) (rapply (adj_raw $a') (var_raw v)))
                (fun () => Std.exact_no_check pf);
              let eid := fresh @E in
              let hh := Control.hyp hid in
              let ety := '(forall t, @csubst $term $vr $sub $g $lw $n 0 $a t = @csubst $term $vr $sub $g $lw $n 0 $a' t) in
              assert_by eid ety (fun () => Std.exact_no_check '(@csubst_mat $term $vr $sub $g $lw $n $a $a' $hh));
              Std.clear [hid];
              Control.progress (fun () => rewrite_all_instances (Control.hyp eid));
              Std.clear [eid]
          | None => Control.zero Not_found
          end
      | None => Control.zero Not_found
      end).

(** ** Terms that are variables

    In a substitution node [csubst L a t], an entry of the normal form of
    [a] sending a name to a term that is a variable [var0 w], with a
    payload [r], is replaced by one sending it to where [r] sends [w]
    ([x as w⟨| r ⟩]), by the law's [sl_var].  The terms that are variables
    are those that are [var0] (the node's own argument) applied to a
    variable as written. *)
Ltac2 var_one (node : constr) : unit :=
  let (_, na) := split_app node in
  let (term, vr, sub, g, lw, n, m, a) :=
    (Array.get na 0, Array.get na 1, Array.get na 2, Array.get na 3, Array.get na 4, Array.get na 5,
     Array.get na 6, Array.get na 7) in
  let ty := app term [constr:(O)] in
  let s := new_st () in
  let e := reify_adj s ty n m a in
  let cv := constr:(@cvar) in
  let is_var u :=
    let (uf, ua) := split_app u in
    if Constr.equal uf cv then
      if Int.equal (Array.length ua) 6 then
        if Constr.equal (Array.get ua 4) lw then
          Control.plus (fun () =>
            let ev := reify_var s (Array.get ua 5) in
            let (ef, ea) := split_app ev in
            if Constr.equal ef (s.(heads).(r_NVarE)) then Some (Array.get ea 0, Array.get ea 1, Array.get ua 5) else None)
            (fun _ => None)
        else None
      else None
    else None in
  let vts := List.fold_left (fun acc (k, u) => match is_var u with Some (h, i, w) => (k, h, i, w) :: acc | None => acc end)
               [] (List.combine (List.init ((s.(terms)).(size)) (fun k => k)) (List.rev ((s.(terms)).(items)))) in
  match vts with
  | [] => Control.zero Not_found
  | _ =>
      let en := finish s ty in
      let ns := en.(e_ns) in
      let nt := nat_lit ns (en.(e_nt)) in
      let nb := nat_lit ns (en.(e_nb)) in
      let l := en.(e_l) in
      let vty := constr:((nat * (lexp * nat))%type) in
      let pr_li := constr:(@pair lexp nat) in
      let pr_v := constr:(@pair nat (lexp * nat)) in
      let vt := list_of vty (List.map (fun (k, h, i, _) => app pr_v [nat_lit ns k; app pr_li [h; nat_lit ns (int_of_n i)]]) vts) in
      match vm_show '(hvar_displayN (order_of $l) $nt $nb $e $vt) with
      | Some sh =>
          let (shd, root) := (sh.(sh_c), sh.(sh_root)) in
          let terms := en.(e_terms) in
          let rd := render_term ty '(adj $ty $n $m) ns (en.(e_labs)) (Array.of_list terms) (en.(e_atoms)) (en.(e_nb)) (sh.(sh_l)) root in
          let a' := rd.(rd_term) in
          let (le, te, ae, pe, hl) := (en.(e_le), en.(e_te), en.(e_ae), en.(e_pe), en.(e_hl)) in
          let (lt, tt, pt) := (en.(e_lt), en.(e_tt), en.(e_pt)) in
          let sty := constr:((list aexpN * aexpN)%type) in
          let ht := vm_eq '(option $sty) '(hvar_displayN (order_of $l) (List.length $te) (List.length $ae) $e $vt)
                      (some sty (sh.(sh_val))) in
          let rty := '(radj $ty) in
          let q := '(fun (rs : list (radj $ty)) (Ae : braun (radj $ty))
                         (hLe : $lt = bof $le) (hTe : $tt = bof $te) (hAe : Ae = bof ($ae ++ rs)) (hPe : $pt = bof $pe)
                         (hvt : Forall (fun '(u, (h, i)) => exists w : var 0, bnth $tt (N.of_nat u) = Some ($vr w) /\
                                                                       var_raw w = mk_rvar (ldenB $lt h) i) $vt)
                         (hs : Forall2 (fun z0 d0 => z0 = aedenB $lt $tt Ae $pt d0) rs $shd) (v : var $n) =>
                       var_bridge $vr $tt $lt $vt _ _ hvt
                         (fun Hy => hvarB_show_sound $le $te $ae rs $pe $lt $tt Ae $pt hLe hTe hAe hPe $l $e $vt $shd $root
                                      $hl Hy $ht hs) (var_raw v)) in
          let srel := '(fun (Ae : braun (radj $ty)) (z0 : radj $ty) (d0 : aexpN) => z0 = aedenB $lt $tt Ae $pt d0) in
          (* that each term in [vt] is the variable it says *)
          let pr := '(fun x : nat * (lexp * nat) => let '(u, (h, i)) := x in
                        exists w : var 0, bnth $tt (N.of_nat u) = Some ($vr w) /\ var_raw w = mk_rvar (ldenB $lt h) i) in
          let fa := '(fun (u : nat) (w : var 0) => bnth $tt (N.of_nat u) = Some ($vr w)) in
          let fb := '(fun (h : lexp) (i : nat) (w : var 0) => var_raw w = mk_rvar (ldenB $lt h) i) in
          let pw := '(fun (u : nat) (h : lexp) (i : nat) (w : var 0) =>
                        bnth $tt (N.of_nat u) = Some ($vr w) /\ var_raw w = mk_rvar (ldenB $lt h) i) in
          let vproofs := List.map (fun (k, h, i, w) =>
              let (kc, ic) := (nat_lit ns k, nat_lit ns (int_of_n i)) in
              app constr:(@ex_intro) [constr:(var 0); app pw [kc; h; ic]; w;
                app constr:(@conj) [app fa [kc; w]; app fb [h; ic; w];
                  refl '(option $ty) (app constr:(@Some) [ty; app vr [w]]);
                  refl constr:(rvar) (app constr:(@var_raw) [constr:(O); w])]]) vts in
          let hvt := forall_proof vty pr (List.map (fun (k, h, i, _) => app pr_v [nat_lit ns k; app pr_li [h; nat_lit ns (int_of_n i)]]) vts)
                       vproofs in
          let p := '(fun y : adj $ty $n $m => forall v : var $n, vrel $vr (rapply (adj_raw $a) (var_raw v)) (rapply (adj_raw y) (var_raw v))) in
          let atoms := Array.to_list (en.(e_atoms)) in
          let pf := share_proof ty n m p rd (fun rs hs _ =>
            let rsl := list_of rty rs in
            let at_ := btree rty (List.append atoms rs) in
            app q [rsl; at_; refl constr:(braun label) lt; refl '(braun $ty) tt; refl '(braun (radj $ty)) at_;
                   refl '(braun (rpadj $ty)) pt; hvt; forall2_proof rty constr:(aexpN) (app srel [at_]) rs (sh.(sh_l)) hs]) in
          let hid := fresh @H in
          assert_by hid '(forall v : var $n, vrel $vr (rapply (adj_raw $a) (var_raw v)) (rapply (adj_raw $a') (var_raw v)))
            (fun () => Std.exact_no_check pf);
          let eid := fresh @E in
          let hh := Control.hyp hid in
          let ety := '(forall t, @csubst $term $vr $sub $g $lw $n $m $a t = @csubst $term $vr $sub $g $lw $n $m $a' t) in
          assert_by eid ety (fun () => Std.exact_no_check '(@csubst_var $term $vr $sub $g $lw $n $m $a $a' $hh));
          Std.clear [hid];
          Control.progress (fun () => rewrite_all_instances (Control.hyp eid));
          Std.clear [eid]
      | None => Control.zero Not_found
      end
  end.

(** A substitution node ([cs] is [@csubst]). *)
Ltac2 is_csubst_in (cs : constr) (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args => if Constr.equal f cs then Int.equal (Array.length args) 9 else false
  | _ => false
  end.

Ltac2 names_varbind () : unit := let cs := constr:(@csubst) in each_until_fail (is_csubst_in cs) var_one.

(** A substitution node into the closed scope ([cs] is [@csubst]). *)
Ltac2 is_csubst_closed_in (cs : constr) (o : constr) (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      if Constr.equal f cs then
        if Int.equal (Array.length args) 9 then Constr.equal (Array.get args 6) o else false
      else false
  | _ => false
  end.

Ltac2 names_mat () : unit := let (cs, o) := (constr:(@csubst), constr:(O)) in each_until_fail (is_csubst_closed_in cs o) mat_one.

(** ** The tactic

    [names]:
    1. rewrites with [names_pre] and then [names_var], the monad laws that
       remove a Kleisli extension or move work into the adjustment (a
       syntax's [Subst] functor adds them): under binders and fusing
       nested substitutions first, then substituting into variables;
    2. rewrites every adjustment built from context forms and [∘] to its
       normal form, shown as context forms;
    3. materialises payloads in substitution nodes ([csubst]);
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
  (autorw @names_pre);
  (autorw @names_var);
  (autorw @names_node);
  (names_adjs memo);
  (Notations.try0 names_varbind);
  (Notations.try0 names_mat);
  (names_apply ());
  (names_eval ());
  (autorw @names_post).

Ltac2 names_tac () : unit :=
  let memo := { seen := [] } in
  (* passes until one leaves the goal as it is (compared syntactically:
     [progress] would normalise the goal's evars to compare) *)
  let rec go () :=
    let g := Control.goal () in
    names_pass memo;
    Control.enter (fun () => if Constr.equal g (Control.goal ()) then () else go ()) in
  Control.enter go.

Ltac2 Notation "names" := names_tac ().

(** For Ltac1 proofs. *)
Ltac names := ltac2:(names_tac ()).
