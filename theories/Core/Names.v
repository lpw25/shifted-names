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
From ShiftedNames.Core Require Import Label Var Adjustment Laws Indexed Syntax Normalise HConcrete HShow Braun HShowB Conv MatShow.
From ShiftedNames.Core Require HNorm.
Import ListNotations.

(** ** Syntaxes

    A syntax is a family of terms [term K] (with the bound variables of
    scope [K]), its variables [tv] and its substitution [sub].  A
    substitution [t [a]], as [names] sees it, is the node [csubst L a t],
    which carries [term], [tv], [sub] and the law [L] that lets [names]
    evaluate and change payloads, as arguments [names] reads and passes
    on, never unfolds: substituting into a variable gives what the
    adjustment sends it to ([sl_var]), and substitutions whose results on
    each variable are related by
    [drel (lawbase tv sub)] are equal ([Conv]): a term that is a
    substitution [u [c]] with [u] with [c] in its payload, a term that is
    a variable with a look-up through its payload, a term with a payload
    [u⟨c⟩] with [u [c]], also inside payloads and in steps.  A syntax's
    [Subst] functor rewrites its substitution to the node before [names]
    works on it ([names_node]); after, the node is [sub] again, by
    conversion ([names_post]). *)
Record SubstLaw (term : nat -> Type) (tv : forall K, var K -> term K) (sub : forall N M, adj term N M -> term N -> term M)
  : Prop := {
  sl_var : forall N M (a : adj term N M) (v : var N),
    sub N M a (tv N v) = Indexed.eval (tv M) (fun K ρ u => sub K M ρ u) a v;
  sl_rel : forall N M (a a' : adj term N M),
    (forall v : var N, drel (lawbase tv sub) (rapply (adj_raw a) (var_raw v)) (rapply (adj_raw a') (var_raw v))) ->
    forall t, sub N M a t = sub N M a' t;
  sl_res : forall N N' M (a : adj term N M) (v : var N) (a' : adj term N' M) (v' : var N'),
    drel (lawbase tv sub) (rapply (adj_raw a) (var_raw v)) (rapply (adj_raw a') (var_raw v')) ->
    sub N M a (tv N v) = sub N' M a' (tv N' v');
  sl_id : forall N (t : term N), sub N N identity t = t;
  sl_comp : forall N M P (a : adj term M P) (b : adj term N M) (t : term N),
    sub M P a (sub N M b t) = sub N P (compose a b) t }.

Definition csubst {term tv sub} (L : SubstLaw term tv sub) {N M} (a : adj term N M) (t : term N) : term M :=
  sub N M a t.

(** A chain of substitutions [t [a₁] … [aₙ]] as data: applied one after
    the other ([fch_apply]), it is one substitution by the composite
    ([fch_comp]); one lemma, proved once ([fch_fuse]). *)
Inductive fchain {term : nat -> Type} : nat -> nat -> Type :=
| FOne {N M} (a : adj term N M) : fchain N M
| FCons {N K M} (a : adj term N K) (rest : fchain K M) : fchain N M.
Arguments fchain term : clear implicits.

Fixpoint fch_apply {term tv sub} (L : SubstLaw term tv sub) {N M} (l : fchain term N M) : term N -> term M :=
  match l in fchain _ N M return term N -> term M with
  | FOne a => fun t => csubst L a t
  | FCons a rest => fun t => fch_apply L rest (csubst L a t)
  end.

Fixpoint fch_comp {term} {N M} (l : fchain term N M) : adj term N M :=
  match l in fchain _ N M return adj term N M with
  | FOne a => a
  | FCons a rest => compose (fch_comp rest) a
  end.

Lemma fch_fuse {term tv sub} (L : SubstLaw term tv sub) {N M} (l : fchain term N M) (t : term N) :
  fch_apply L l t = csubst L (fch_comp l) t.
Proof.
  revert t; induction l as [N M a|N K M a rest IH]; intros t; cbn [fch_apply fch_comp]; [reflexivity|].
  rewrite IH; unfold csubst; apply (sl_comp _ _ _ L).
Qed.

Lemma csubst_rel {term tv sub} (L : SubstLaw term tv sub) {N M} (a a' : adj term N M) :
  (forall v : var N, drel (lawbase tv sub) (rapply (adj_raw a) (var_raw v)) (rapply (adj_raw a') (var_raw v))) ->
  forall t, csubst L a t = csubst L a' t.
Proof. apply (sl_rel _ _ _ L). Qed.

(** A node substituting into a variable, evaluated from what its
    adjustment's result is related to: a variable, a term with its
    payload (as a node), or the result of another node on a variable.
    [names] recognises a term that is a variable syntactically: [tv K w],
    or what [tv] unfolds to. *)
(** A rendering with shared definitions, as data: [nest] gives the
    rendering, and [chain_intro] proves a property of it from one of its
    root, the definitions as variables, with one step for each.  (The
    proof [names] builds mentions each definition once.) *)
Inductive chain {T : nat -> Type} {N M : nat} : Type :=
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


(** A node substituting by the identity is its term. *)
Lemma node_id {term tv sub} (L : SubstLaw term tv sub) {N} (t : term N) : csubst L identity t = t.
Proof. apply (sl_id _ _ _ L). Qed.

Lemma node_look {term tv sub} (L : SubstLaw term tv sub) {N M K} (a : adj term N M) (v : var N) (b : adj term K M)
    (w : var K) :
  drel (lawbase tv sub) (rapply (adj_raw a) (var_raw v)) (rapply (adj_raw b) (var_raw w)) ->
  csubst L a (tv N v) = csubst L b (tv K w).
Proof. apply (sl_res _ _ _ L). Qed.

(** The first variable sent to [t], the rest by [a]. *)
#[local] Transparent in_bound.
Lemma in_bound_here {T : nat -> Type} {N M} (t : target T M) (a : adj T N M) :
  rapply (adj_raw (in_bound t a)) (var_raw (@bvar (S N) 0 stt)) = rtarget_result (to_target t).
Proof. unfold in_bound; cbn [adj_raw]; rewrite rapply_push_inner; reflexivity. Qed.
#[local] Opaque in_bound.

Lemma node_target {term tv sub} (L : SubstLaw term tv sub) {N M} (a : adj term N M) (v : var N) (t : target term M) :
  drel (lawbase tv sub) (rapply (adj_raw a) (var_raw v)) (rtarget_result (to_target t)) ->
  csubst L a (tv N v) = match t with Rename w => tv M w | Bind u b => csubst L b u end.
Proof.
  intros H; rewrite (node_look L a v (in_bound t a) bvar0) by (rewrite in_bound_here; exact H).
  unfold csubst; rewrite (sl_var _ _ _ L); unfold Indexed.eval.
  pose proof (in_bound_here t a) as E; destruct t as [w|K u b]; cbn [to_target rtarget_result] in E.
  - match goal with |- context [apply_var ?x ?y] => rewrite (apply_var_rename x y w E) end; reflexivity.
  - match goal with |- context [apply_var ?x ?y] => rewrite (apply_var_bind x y u b E) end; reflexivity.
Qed.

Lemma node_var {term tv sub} (L : SubstLaw term tv sub) {N M} (a : adj term N M) (v : var N) (w : var M) :
  drel (lawbase tv sub) (rapply (adj_raw a) (var_raw v)) (inl (var_raw w)) -> csubst L a (tv N v) = tv M w.
Proof. apply (node_target L a v (Rename w)). Qed.

Lemma node_term {term tv sub} (L : SubstLaw term tv sub) {N M} (a : adj term N M) (v : var N) K (u : term K)
    (b : adj term K M) :
  drel (lawbase tv sub) (rapply (adj_raw a) (var_raw v)) (inr (existT term K u, adj_raw b)) ->
  csubst L a (tv N v) = csubst L b u.
Proof. apply (node_target L a v (Bind u b)). Qed.

(** Converting: the facts [aconv] uses, from the terms as written. *)
Lemma nest_fact {term tv sub} (L : SubstLaw term tv sub) Le Te Ae (C : aexpN) K M (l : fchain term K M) (u : term K) k k' :
  adj_raw (fch_comp l) = aedenB Le Te Ae C -> bnth Te k' = Some (existT term K u) ->
  bnth Te k = Some (existT term M (fch_apply L l u)) ->
  exists K M (c : adj term K M) (u : term K), adj_raw c = aedenB Le Te Ae C /\ bnth Te k' = Some (existT term K u)
    /\ bnth Te k = Some (existT term M (sub K M c u)).
Proof.
  intros H1 H2 H3; exists K, M, (fch_comp l), u; split; [exact H1|split; [exact H2|]].
  rewrite H3, fch_fuse; reflexivity.
Qed.

Lemma var_fact {term tv sub} (L : SubstLaw term tv sub) (Le : braun label) (Te : braun {K & term K}) k h i K (w : var K) :
  bnth Te k = Some (existT term K (tv K w)) -> var_raw w = mk_rvar (ldenB Le h) (N.to_nat i) ->
  exists K (w : var K), bnth Te k = Some (existT term K (tv K w)) /\ var_raw w = mk_rvar (ldenB Le h) (N.to_nat i).
Proof. intros H1 H2; exists K, w; split; [exact H1|exact H2]. Qed.

Lemma conv_rel {term} (tv : forall K, var K -> term K) (sub : forall N M, adj term N M -> term N -> term M)
    nf vf Le Te Ae (A B : radj {K & term K}) f e :
  Forall (fun '(k, (k', C)) => exists K M (c : adj term K M) (u : term K),
            adj_raw c = aedenB Le Te Ae C /\ bnth Te k' = Some (existT term K u)
            /\ bnth Te k = Some (existT term M (sub K M c u))) nf ->
  Forall (fun '(k, (h, i)) => exists K (w : var K),
            bnth Te k = Some (existT term K (tv K w)) /\ var_raw w = mk_rvar (ldenB Le h) (N.to_nat i)) vf ->
  A = aedenB Le Te Ae e -> aedenB Le Te Ae (aconvn nf vf f e) = B ->
  forall v, drel (lawbase tv sub) (rapply A v) (rapply B v).
Proof.
  intros Hn Hv -> <- v.
  refine (drel_mono _ _ (cbase_lawbase tv sub) _ _ (aconvn_sound nf vf tv sub Le Te Ae Hn Hv f e v)).
Qed.

(** The same for one variable, whose result in the converted adjustment
    is [r]. *)
Lemma conv_res {term} (tv : forall K, var K -> term K) (sub : forall N M, adj term N M -> term N -> term M)
    nf vf Le Te Ae (A : radj {K & term K}) f e v r :
  Forall (fun '(k, (k', C)) => exists K M (c : adj term K M) (u : term K),
            adj_raw c = aedenB Le Te Ae C /\ bnth Te k' = Some (existT term K u)
            /\ bnth Te k = Some (existT term M (sub K M c u))) nf ->
  Forall (fun '(k, (h, i)) => exists K (w : var K),
            bnth Te k = Some (existT term K (tv K w)) /\ var_raw w = mk_rvar (ldenB Le h) (N.to_nat i)) vf ->
  A = aedenB Le Te Ae e -> rapply (aedenB Le Te Ae (aconvn nf vf f e)) v = r ->
  drel (lawbase tv sub) (rapply A v) r.
Proof. intros Hn Hv HA <-; exact (conv_rel tv sub nf vf Le Te Ae A _ f e Hn Hv HA eq_refl v). Qed.

Lemma share_intro_r {T N M K L} (a : adj T N M) (A : adj T K L) (f : adj T K L -> adj T N M) :
  (forall r, adj_raw r = adj_raw A -> a = f r) -> a = Indexed.share A f.
Proof. intros H; rewrite share_eq; apply H; reflexivity. Qed.

Lemma share_intro_p {T N M K L} (A : adj T K L) (f : adj T K L -> adj T N M) (P : adj T N M -> Prop) :
  (forall r, adj_raw r = adj_raw A -> P (f r)) -> P (Indexed.share A f).
Proof. intros H; rewrite share_eq; apply H; reflexivity. Qed.


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
  | Constr.Unsafe.Constant _ _ => Constr.equal f constr:(@adj_raw)
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

(** [f ()], or [g e] if it fails with [e], leaving no choice point: a
    failure later does not come back to try [g] ([Control.plus] would,
    and its choice points multiply). *)
Ltac2 attempt (f : unit -> 'a) (g : exn -> 'a) : 'a :=
  match Control.case f with Val (x, _) => x | Err e => g e end.

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
  h_ISubFA : constr; h_ISubBA : constr;
  h_SEmpty : constr; h_SLiftF : constr; h_SLiftB : constr; h_SSubF : constr; h_SSubB : constr; h_SRenF : constr;
  h_SRenB : constr; h_SSubFA : constr; h_SSubBA : constr; h_SLookF : constr; h_SLookB : constr;
  h_methods : (constr * int) list; h_insts : (constr * constr) list;
  h_bvar : constr; h_bvar0 : constr; h_fvar : constr; h_lvar : constr; h_vshift_free : constr; h_vshift_bound : constr;
  h_O : constr; h_S : constr;
  r_NId : constr; r_NAtom : constr; r_NCompose : constr; r_NOuter : constr; r_NInner : constr;
  r_NVarE : constr; r_NBindE : constr; r_NShiftE : constr; r_NLookE : constr;
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
  h_ISubFA := constr:(@ISubFA); h_ISubBA := constr:(@ISubBA);
  h_SEmpty := constr:(@SEmpty); h_SLiftF := constr:(@SLiftF); h_SLiftB := constr:(@SLiftB); h_SSubF := constr:(@SSubF);
  h_SSubB := constr:(@SSubB); h_SRenF := constr:(@SRenF); h_SRenB := constr:(@SRenB); h_SSubFA := constr:(@SSubFA);
  h_SSubBA := constr:(@SSubBA); h_SLookF := constr:(@SLookF); h_SLookB := constr:(@SLookB);
  (* each method, with the number of its class's parameters before the instance *)
  h_methods := [(constr:(@cnil), 1); (constr:(@cent), 2); (constr:(@cbnd), 2); (constr:(@csub), 3);
                (constr:(@csubb), 3); (constr:(@cren), 3); (constr:(@crenb), 3); (constr:(@csuba), 4);
                (constr:(@csubba), 4)];
  (* each instance, with the constructor it is *)
  h_insts := [(constr:(@cnil_full), constr:(@IEmpty)); (constr:(@cnil_short), constr:(@SEmpty));
              (constr:(@cent_full), constr:(@IPosF)); (constr:(@cent_short), constr:(@SLiftF));
              (constr:(@cbnd_full), constr:(@IPosB)); (constr:(@cbnd_short), constr:(@SLiftB));
              (constr:(@csub_full), constr:(@ISubF)); (constr:(@csub_short), constr:(@SSubF));
              (constr:(@csubb_full), constr:(@ISubB)); (constr:(@csubb_short), constr:(@SSubB));
              (constr:(@cren_full), constr:(@IRenF)); (constr:(@cren_short), constr:(@SRenF));
              (constr:(@crenb_full), constr:(@IRenB)); (constr:(@crenb_short), constr:(@SRenB));
              (constr:(@csuba_full), constr:(@ISubFA)); (constr:(@csuba_short), constr:(@SSubFA));
              (constr:(@csubba_full), constr:(@ISubBA)); (constr:(@csubba_short), constr:(@SSubBA))];
  h_bvar := constr:(@bvar); h_bvar0 := constr:(@bvar0); h_fvar := constr:(@fvar); h_lvar := constr:(@lvar);
  h_vshift_free := constr:(@vshift_free); h_vshift_bound := constr:(@vshift_bound);
  h_O := constr:(O); h_S := constr:(S);
  r_NId := constr:(NId); r_NAtom := constr:(NAtom); r_NCompose := constr:(NCompose); r_NOuter := constr:(NOuter);
  r_NInner := constr:(NInner); r_NVarE := constr:(NVarE); r_NBindE := constr:(NBindE); r_NShiftE := constr:(NShiftE);
  r_NLookE := constr:(NLookE);
  r_LNone := constr:(LNone); r_N0 := constr:(N0) }.

Ltac2 Type st := { labs : tbl; terms : tbl; atoms : tbl; ns : nats; lets : ident FSet.t;
                   heads : rh; mutable sdefs : (int, constr) FMap.t }.

Ltac2 new_st () : st :=
  { labs := new_tbl (); terms := new_tbl (); atoms := new_tbl (); ns := new_nats ();
    lets := List.fold_left (fun acc (id, b, _) => match b with Some _ => FSet.add id acc | None => acc end)
              (FSet.empty FSet.Tags.ident_tag) (Control.hyps ());
    heads := mk_rh ();
    sdefs := FMap.empty FSet.Tags.int_tag }.

Ltac2 reify_lab (s : st) (x : constr) : constr :=
  if is_string_lit x then app constr:(LCon) [x]
  else let n := n_lit (tbl_add (s.(lets)) (s.(labs)) x) in app constr:(LAtom) [n].

(** The head and arguments of [c], under casts. *)
(** Literals: a [string], [ascii], [positive], [N], [bool] or [nat]
    constructor, applied or not.  No node or adjustment is inside one, so
    traversals of the goal skip them (labels are most of a goal). *)
Ltac2 lit_inds () : inductive list :=
  List.map (fun c => match Constr.Unsafe.kind c with Constr.Unsafe.Ind i _ => i | _ => Control.throw Not_found end)
    [constr:(String.string); constr:(Ascii.ascii); constr:(positive); constr:(N); constr:(bool); constr:(nat)].

Ltac2 is_lit (li : inductive list) (c : constr) : bool :=
  let h := match Constr.Unsafe.kind c with Constr.Unsafe.App h _ => h | _ => c end in
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constructor k _ => let i := Constructor.inductive k in List.exist (Ind.equal i) li
  | _ => false
  end.

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

(** The raw terms of a family [t]: [{K & t K}], as the indexed layer
    writes it. *)
Ltac2 raw_ty (t : constr) : constr := '({K & $t K}).

(** A term [u : t k], as the raw term [existT _ k u]. *)
Ltac2 raw_term (t : constr) (k : constr) (u : constr) : constr :=
  let (_, a) := split_app (raw_ty t) in app constr:(@existT) [Array.get a 0; Array.get a 1; k; u].

(** The scope and the term of a raw term. *)
Ltac2 term_parts (c : constr) : constr * constr := let (_, a) := split_app c in (Array.get a 2, Array.get a 3).

Ltac2 reify_term (s : st) (t : constr) (k : constr) (u : constr) : constr :=
  n_lit (tbl_add (s.(lets)) (s.(terms)) (raw_term t k u)).

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
    attempt (fun () => reify_octx s t (Array.get args 6) (h.(r_NId))) (fun _ => atom ())
  else if is_h f (h.(h_cform)) then
    attempt (fun () =>
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
  let x := wrap x0 in
  if is_h f (h.(h_OEnd)) then reify_ictx s t (Array.get a 6) env pos slots x
  else if is_h f (h.(h_OEndT)) then reify_ictx s t (Array.get a 7) env pos slots x
  else if is_h f (h.(h_OShort)) then reify_sctx s t (Array.get a 6) x
  else if is_h f (h.(h_OShortT)) then
    let (fc, c) := split_app (Array.get a 6) in
    if is_h fc (h.(h_STail)) then
      let sig := reify_adj s t (Array.get c 3) (Array.get c 4) (Array.get c 6) in
      reify_sctx s t (Array.get c 5) sig
    else Control.zero Not_found
  else Control.zero Not_found

(** [ictx_den i]: each entry put on [x], the outermost first.  A term
    [x := u] is in the output scope, with the identity payload. *)
with reify_ictx (s : st) (t : constr) (i : constr) (env : constr list) (pos : constr list) (slots : constr list)
    (x : constr) : constr :=
  let h := s.(heads) in
  let slot c :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Rel r => List.nth slots (Int.sub r 1)
    | _ => Control.zero Not_found
    end in
  let posn p := List.nth pos (int_of_nat p) in
  let (f, a) := view h i in
  let inner c e := reify_ictx s t c env pos slots e in
  let m := Array.get a 2 in
  let bind k u p := app (h.(r_NBindE)) [reify_term s t k u; p] in
  if is_h f (h.(h_IEmpty)) then x
  else if is_h f (h.(h_IPosF)) then inner (Array.get a 6) (app (h.(r_NInner)) [reify_lab s (Array.get a 7); posn (Array.get a 5); x])
  else if is_h f (h.(h_IPosB)) then inner (Array.get a 6) (app (h.(r_NInner)) [h.(r_LNone); posn (Array.get a 5); x])
  else if is_h f (h.(h_IRenF)) then inner (Array.get a 6) (app (h.(r_NInner)) [reify_lab s (Array.get a 7); slot (Array.get a 8); x])
  else if is_h f (h.(h_IRenB)) then inner (Array.get a 6) (app (h.(r_NInner)) [h.(r_LNone); slot (Array.get a 7); x])
  else if is_h f (h.(h_ISubF)) then
    inner (Array.get a 6) (app (h.(r_NInner)) [reify_lab s (Array.get a 7); bind m (Array.get a 8) (h.(r_NId)); x])
  else if is_h f (h.(h_ISubB)) then
    inner (Array.get a 6) (app (h.(r_NInner)) [h.(r_LNone); bind m (Array.get a 7) (h.(r_NId)); x])
  else if is_h f (h.(h_ISubFA)) then
    let k := Array.get a 8 in
    inner (Array.get a 6)
      (app (h.(r_NInner)) [reify_lab s (Array.get a 7); bind k (Array.get a 9) (reify_adj s t k m (Array.get a 10)); x])
  else if is_h f (h.(h_ISubBA)) then
    let k := Array.get a 7 in
    inner (Array.get a 6) (app (h.(r_NInner)) [h.(r_LNone); bind k (Array.get a 8) (reify_adj s t k m (Array.get a 9)); x])
  else Control.zero Not_found

(** [sctx_den s]: each entry put on [x], the outermost first.  A term
    [x := u] is in its entry's scope, with the identity payload. *)
with reify_sctx (s : st) (t : constr) (c : constr) (x : constr) : constr :=
  let h := s.(heads) in
  let (f, a) := view h c in
  let ent y tg := app (h.(r_NInner)) [y; tg; x] in
  let mb := Array.get a 2 in
  let bind k u p := app (h.(r_NBindE)) [reify_term s t k u; p] in
  if is_h f (h.(h_SEmpty)) then x
  else if is_h f (h.(h_SLiftF)) then
    let y := reify_lab s (Array.get a 6) in
    reify_sctx s t (Array.get a 5) (app (h.(r_NInner)) [y; app (h.(r_NVarE)) [y; h.(r_N0)]; app (h.(r_NOuter)) [y; x]])
  else if is_h f (h.(h_SLiftB)) then
    let y := h.(r_LNone) in
    reify_sctx s t (Array.get a 5) (app (h.(r_NInner)) [y; app (h.(r_NVarE)) [y; h.(r_N0)]; app (h.(r_NOuter)) [y; x]])
  else if is_h f (h.(h_SSubF)) then
    reify_sctx s t (Array.get a 5) (ent (reify_lab s (Array.get a 6)) (bind mb (Array.get a 7) (h.(r_NId))))
  else if is_h f (h.(h_SSubB)) then
    reify_sctx s t (Array.get a 5) (ent (h.(r_LNone)) (bind mb (Array.get a 6) (h.(r_NId))))
  else if is_h f (h.(h_SRenF)) then
    reify_sctx s t (Array.get a 5) (ent (reify_lab s (Array.get a 6)) (reify_var s (Array.get a 7)))
  else if is_h f (h.(h_SRenB)) then
    reify_sctx s t (Array.get a 5) (ent (h.(r_LNone)) (reify_var s (Array.get a 6)))
  else if is_h f (h.(h_SSubFA)) then
    let k := Array.get a 7 in
    reify_sctx s t (Array.get a 5)
      (ent (reify_lab s (Array.get a 6)) (bind k (Array.get a 8) (reify_adj s t k mb (Array.get a 9))))
  else if is_h f (h.(h_SSubBA)) then
    let k := Array.get a 6 in
    reify_sctx s t (Array.get a 5) (ent (h.(r_LNone)) (bind k (Array.get a 7) (reify_adj s t k mb (Array.get a 8))))
  else if is_h f (h.(h_SLookF)) then
    reify_sctx s t (Array.get a 6) (ent (reify_lab s (Array.get a 7)) (reify_look s t a (Array.get a 8) (Array.get a 9)))
  else if is_h f (h.(h_SLookB)) then
    reify_sctx s t (Array.get a 6) (ent (h.(r_LNone)) (reify_look s t a (Array.get a 7) (Array.get a 8)))
  else Control.zero Not_found

(** [rapply_target r w]: [w] a plain variable, [r : adj t K Mb]. *)
with reify_look (s : st) (t : constr) (a : constr array) (w : constr) (r : constr) : constr :=
  let h := s.(heads) in
  let (vf, va) := split_app (reify_var s w) in
  if is_h vf (h.(r_NVarE)) then
    app (h.(r_NLookE)) [Array.get va 0; Array.get va 1; reify_adj s t (Array.get a 5) (Array.get a 2) r]
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
  kTVarE : constr; kTBindE : constr; kTLookE : constr; kLNone : constr; kLCon : constr;
  kidentity : constr; kcompose : constr; kcform : constr; kcform_id : constr; kshare : constr; kadj : constr;
  kONamF : constr; kONamB : constr; kOEnd : constr; kOEndT : constr; kOPosF : constr; kOPosB : constr;
  kOShort : constr; kOShortT : constr; kIEmpty : constr; kIPosF : constr; kIPosB : constr; kSTail : constr;
  kSEmpty : constr; kSLiftF : constr; kSLiftB : constr; kSSubF : constr; kSSubB : constr; kSRenF : constr;
  kSRenB : constr; kSSubFA : constr; kSSubBA : constr; kSLookF : constr; kSLookB : constr;
  kbvar : constr; kfvar : constr; kstt : constr; kslot : constr; ktname : constr; kSome : constr; kNone : constr }.

Ltac2 mk_kc () : kc := {
  kO := constr:(O); kS := constr:(S); kN0 := constr:(N0); kAId := constr:(NId); kAAtom := constr:(NAtom); kACompose := constr:(NCompose);
  kAOuter := constr:(NOuter); kAInner := constr:(NInner); kTVarE := constr:(NVarE); kTBindE := constr:(NBindE);
  kTLookE := constr:(NLookE); kLNone := constr:(LNone); kLCon := constr:(LCon);
  kidentity := constr:(@identity); kcompose := constr:(@compose); kcform := constr:(@cform); kcform_id := constr:(@cform_id);
  kshare := constr:(@Indexed.share); kadj := constr:(@adj);
  kONamF := constr:(@ONamF); kONamB := constr:(@ONamB); kOEnd := constr:(@OEnd); kOEndT := constr:(@OEndT);
  kOPosF := constr:(@OPosF); kOPosB := constr:(@OPosB); kOShort := constr:(@OShort); kOShortT := constr:(@OShortT);
  kIEmpty := constr:(@IEmpty); kIPosF := constr:(@IPosF); kIPosB := constr:(@IPosB); kSTail := constr:(@STail);
  kSEmpty := constr:(@SEmpty); kSLiftF := constr:(@SLiftF); kSLiftB := constr:(@SLiftB); kSSubF := constr:(@SSubF);
  kSSubB := constr:(@SSubB); kSRenF := constr:(@SRenF); kSRenB := constr:(@SRenB); kSSubFA := constr:(@SSubFA);
  kSSubBA := constr:(@SSubBA); kSLookF := constr:(@SLookF); kSLookB := constr:(@SLookB);
  kbvar := constr:(@bvar); kfvar := constr:(@fvar); kstt := constr:(stt); kslot := constr:(slot); ktname := constr:(tname);
  kSome := constr:(@Some tname); kNone := constr:(@None tname) }.

(** The same, rendering data ([MatShow.madj]) instead: the constructors
    the data mirrors, and those it shares, are the data's. *)
Ltac2 mk_kc_data () : kc :=
  let k := mk_kc () in
  { k with kcompose := constr:(@MCompose); kcform := constr:(@MCform);
    kSEmpty := constr:(@MSEmpty); kSLiftF := constr:(@MSLiftF); kSLiftB := constr:(@MSLiftB); kSSubF := constr:(@MSSubF);
    kSSubB := constr:(@MSSubB); kSRenF := constr:(@MSRenF); kSRenB := constr:(@MSRenB); kSSubFA := constr:(@MSSubFA);
    kSSubBA := constr:(@MSSubBA); kSLookF := constr:(@MSLookF); kSLookB := constr:(@MSLookB) }.

(** The universe constraints the constructors' applications to [t]
    need, which building terms directly does not add. *)
Ltac2 univs (t : constr) : unit :=
  let p := raw_ty t in
  let _ := '(@identity $t) in let _ := '(@compose $t) in let _ := '(@cform $t) in let _ := '(@cform_id $t) in
  let _ := '(@Indexed.share $t) in let _ := '(@adj $t) in let _ := '(@ONamF $t) in let _ := '(@ONamB $t) in
  let _ := '(@OEnd $t) in let _ := '(@OEndT $t) in let _ := '(@OPosF $t) in let _ := '(@OPosB $t) in
  let _ := '(@OShort $t) in let _ := '(@OShortT $t) in let _ := '(@IEmpty $t) in let _ := '(@IPosF $t) in
  let _ := '(@IPosB $t) in let _ := '(@STail $t) in let _ := '(@SEmpty $t) in let _ := '(@SLiftF $t) in
  let _ := '(@SLiftB $t) in let _ := '(@SSubF $t) in let _ := '(@SSubB $t) in let _ := '(@SRenF $t) in
  let _ := '(@SRenB $t) in let _ := '(@SSubFA $t) in let _ := '(@SSubBA $t) in let _ := '(@SLookF $t) in
  let _ := '(@SLookB $t) in let _ := '(@share_intro_p $t) in let _ := '(@adj_raw $t) in
  let _ := '(@Adjustment.radj $p) in let _ := '(@adj_eq $t) in let _ := '(@apply_var_bind $t) in
  let _ := '(@CRoot $t) in let _ := '(@CShare $t) in let _ := '(@chain_intro $t) in
  let _ := '(@hshowDB_sound $p) in let _ := '(@hlookB_term $p) in let _ := '(@hlookB_var $p) in let _ := '(@hlookB_look $p) in
  let _ := '(@aedenB $p) in let _ := '(@braun $p) in let _ := '(@BN $p) in let _ := '(@BE $p) in
  let _ := '(@F2_one (radj $p)) in let _ := '(@F2_app (radj $p)) in let _ := '(@F_one (radj $p)) in let _ := '(@F_app (radj $p)) in
  ().

(** A builder: given the index of each shared definition at its root and
    the binders it is under, a term. *)
Ltac2 Type rnd := {
  rk : kc; rt : constr; rns : nats; mutable rctr : int; rlabs : constr array;
  mutable rterm : int -> (int -> int) -> int -> constr; mutable rscope : int -> constr;
  mutable ratoms : (constr * (ix * int) * (ix * int)) array; rnb : int;
  rpos : (int, int) FMap.t; mutable rshty : ((ix * int) * (ix * int)) array; rdat : bool }.

(** In the data mode, an adjustment left as it is. *)
Ltac2 as_is (r : rnd) (n : constr) (m : constr) (c : constr) : constr :=
  if r.(rdat) then app constr:(@MAtom) [r.(rt); n; m; c] else c.

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
    let n := new_ix r in (n, n, (fun _ _ => as_is r (ie_nat r n) (ie_nat r n) (app (k.(kidentity)) [t; ie_nat r n])))
  else if Constr.equal h (k.(kAAtom)) then
    let i := int_of_n (Array.get a 0) in
    if Int.lt i (r.(rnb)) then
      let (s, an, am) := Array.get (r.(ratoms)) i in (an, am, (fun _ _ => as_is r (ie_nat r an) (ie_nat r am) s))
    else
      let p := match FMap.find_opt i (r.(rpos)) with Some p => p | None => Control.zero Not_found end in
      let (sn, sm) := Array.get (r.(rshty)) p in
      (sn, sm, (fun sb d => as_is r (ie_nat r sn) (ie_nat r sm) (rel (Int.add (sb p) d))))
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
       as_is r nN nM (app (k.(kcform_id)) [t; kk; nN; nN; nM; z; o])))
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
       as_is r nN nM (app (k.(kcform_id)) [t; one; nNt; nN; nM; one; pos fin nNt nN nM nNt (k.(kNone))])))
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
              let ku := const_ix r (r.(rscope) u) in
              let rr := Array.get ta 1 in
              let (rh, _) := hd_args rr in
              if Constr.equal rh (k.(kAId)) then
                (* the identity payload: the term is in its entry's scope *)
                (ie_eq ku mbi;
                 (fun sb d =>
                    let s := inner sb d in
                    let uc := r.(rterm) u sb d in
                    if xb then app (k.(kSSubB)) (List.append (hd sb d) [s; uc])
                    else app (k.(kSSubF)) (List.append (hd sb d) [s; rlab r x; uc])))
              else
                let (nr, mr, br) := render_a r rr in
                ie_eq mr mbi; ie_eq nr ku;
                (fun sb d =>
                   let s := inner sb d in
                   let uc := r.(rterm) u sb d in
                   let kr := ie_nat r nr in
                   if xb then app (k.(kSSubBA)) (List.append (hd sb d) [s; kr; uc; br sb d])
                   else app (k.(kSSubFA)) (List.append (hd sb d) [s; rlab r x; kr; uc; br sb d]))
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
       if r.(rdat) then app constr:(@MShort) [t; nNt; nN; nM; s]
       else app (k.(kcform_id)) [t; z; nNt; nN; nM; z; app (k.(kOShort)) [t; z; nNt; nN; nM; z; s]]
     else if r.(rdat) then app constr:(@MShortT) [t; nN; nM; ie_nat r nb0; ie_nat r mb0; s; bs sb d]
     else
       let c := app (k.(kSTail)) [t; nN; nM; ie_nat r nb0; ie_nat r mb0; s; bs sb d] in
       app (k.(kcform_id)) [t; z; z; nN; nM; z; app (k.(kOShortT)) [t; z; z; nN; nM; z; c]])).

(** A rendering: the shared definitions in the order they are bound,
    each with its type and its scope indices, under the binders of those
    before it; the suffixes of the whole ([share]s from the [i]th on, the
    last the root alone), each under the binders before it; the whole. *)
Ltac2 Type rendered := {
  rd_k : int; rd_tys : constr array; rd_kl : (constr * constr) array; rd_defs : constr array;
  rd_sufs : constr array; rd_term : constr; rd_chain : constr; rd_n : constr }.

(** [render_all t ns labs terms atoms nb shs roots term_of]: the shared
    definitions [shs] (atom numbers and expressions, in the order they are
    bound) and the expressions [roots] (with their scope indices), the
    last the root; [term_of] gives the terms, from the builders of the
    roots. *)
Ltac2 render_all (t : constr) (ns : nats) (labs : constr array) (atoms : constr array) (nb : int)
    (shs : (int * constr) list) (roots : (constr * constr option * constr) list)
    (scope_of : int -> constr)
    (term_of : ((int -> int) -> int -> constr) list -> int -> (int -> int) -> int -> constr) (dat : bool)
    : rendered * ((int -> int) -> int -> constr) list :=
  let k := if dat then mk_kc_data () else mk_kc () in
  univs t;
  let shn := List.length shs in
  let pos := List.fold_left (fun acc (i, j) => FMap.add j i acc) (FMap.empty FSet.Tags.int_tag)
               (List.combine (List.init shn (fun i => i)) (List.map (fun (j, _) => j) shs)) in
  let r := { rk := k; rt := t; rns := ns; rctr := 0; rlabs := labs; rterm := (fun _ _ _ => k.(kO)); rscope := scope_of;
             ratoms := Array.of_list []; rnb := nb; rpos := pos; rshty := Array.of_list []; rdat := dat } in
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
      (match rn with Some rn => ie_eq n (const_ix r rn) | None => () end);
      ie_eq m (const_ix r rm); (n, b)) roots in
  let rm := let (_, _, rm) := List.last roots in rm in
  let rn := let (n, _) := List.last rbs in ie_nat r n in
  let rbs := List.map (fun (_, b) => b) rbs in
  r.(rterm) := term_of rbs;
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
     rd_chain := chain 0; rd_n := rn }, rbs).

(** The terms [terms], given as raw terms, and their scopes. *)
Ltac2 given_terms (terms : constr array) : ((int -> int) -> int -> constr) list -> int -> (int -> int) -> int -> constr :=
  fun _ i _ _ => let (_, u) := term_parts (Array.get terms i) in u.

Ltac2 given_scopes (terms : constr array) : int -> constr := fun i => let (k, _) := term_parts (Array.get terms i) in k.

(** [render_term t ty labs terms atoms nb shd root]: the rendering of the
    shared definitions [shd] (the atoms from [nb] on) and [root], of type
    [ty]. *)
Ltac2 render_term (t : constr) (ty : constr) (ns : nats) (labs : constr array) (terms : constr array) (atoms : constr array) (nb : int)
    (shd : constr list) (root : constr) (dat : bool) : rendered :=
  let (n, m) := adj_idx ty in
  let shs := List.mapi (fun i d => (Int.add nb i, d)) shd in
  let (rd, _) := render_all t ns labs atoms nb shs [(root, Some n, m)] (given_scopes terms) (given_terms terms) dat in rd.

(** ** Rendered data to Gallina

    The data ([MatShow.madj]) a rendering in the data mode gives, as the
    Gallina term it means: as shown ([mden]), or materialised ([mmat],
    with [msub K M r u] the term [u] substituted by [r]).  Shared
    definitions and their binders are kept as they are. *)
Ltac2 Type dk := {
  dAtom : constr; dComp : constr; dShort : constr; dShortT : constr; dCform : constr;
  dEmpty : constr; dLiftF : constr; dLiftB : constr; dSubF : constr; dSubB : constr; dRenF : constr; dRenB : constr;
  dSubFA : constr; dSubBA : constr; dLookF : constr; dLookB : constr;
  gshare : constr; gCShare : constr; gCRoot : constr; gk : kc }.

Ltac2 mk_dk () : dk := {
  dAtom := constr:(@MAtom); dComp := constr:(@MCompose); dShort := constr:(@MShort); dShortT := constr:(@MShortT);
  dCform := constr:(@MCform); dEmpty := constr:(@MSEmpty); dLiftF := constr:(@MSLiftF); dLiftB := constr:(@MSLiftB);
  dSubF := constr:(@MSSubF); dSubB := constr:(@MSSubB); dRenF := constr:(@MSRenF); dRenB := constr:(@MSRenB);
  dSubFA := constr:(@MSSubFA); dSubBA := constr:(@MSSubBA); dLookF := constr:(@MSLookF); dLookB := constr:(@MSLookB);
  gshare := constr:(@Indexed.share); gCShare := constr:(@CShare); gCRoot := constr:(@CRoot); gk := mk_kc () }.

(** Whether a short form has a lift ([MatShow.mlift]). *)
Ltac2 rec dlift (d : dk) (s : constr) : bool :=
  let (f, a) := split_app s in
  if Constr.equal f (d.(dEmpty)) then false
  else if Constr.equal f (d.(dLiftF)) then true
  else if Constr.equal f (d.(dLiftB)) then true
  else if Constr.equal f (d.(dLookF)) then dlift d (Array.get a 6)
  else if Constr.equal f (d.(dLookB)) then dlift d (Array.get a 6)
  else dlift d (Array.get a 5).

Ltac2 rec dconv (d : dk) (msub : constr -> constr -> constr -> constr -> constr) (mat : bool) (c : constr) : constr :=
  let k := d.(gk) in
  let z := k.(kO) in
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Lambda b body => Constr.Unsafe.make (Constr.Unsafe.Lambda b (dconv d msub mat body))
  | Constr.Unsafe.App f a =>
      let g i := Array.get a i in
      if Constr.equal f (d.(dAtom)) then g 3
      else if Constr.equal f (d.(dComp)) then
        app (k.(kcompose)) [g 0; g 1; g 2; g 3; dconv d msub mat (g 4); dconv d msub false (g 5)]
      else if Constr.equal f (d.(dShort)) then
        (* T Nt N M s *)
        let m' := if mat then Bool.neg (dlift d (g 4)) else false in
        app (k.(kcform_id)) [g 0; z; g 1; g 2; g 3; z; app (k.(kOShort)) [g 0; z; g 1; g 2; g 3; z; sconv d msub m' (g 4)]]
      else if Constr.equal f (d.(dShortT)) then
        (* T N M Nb Mb s σ *)
        let m' := if mat then Bool.neg (dlift d (g 5)) else false in
        let cl := app (k.(kSTail)) [g 0; g 1; g 2; g 3; g 4; sconv d msub m' (g 5); dconv d msub m' (g 6)] in
        app (k.(kcform_id)) [g 0; z; z; g 1; g 2; z; app (k.(kOShortT)) [g 0; z; z; g 1; g 2; z; cl]]
      else if Constr.equal f (d.(dCform)) then
        app (k.(kcform)) [g 0; g 1; g 2; g 3; g 4; g 5; g 6; g 7; dconv d msub false (g 8)]
      else if Constr.equal f (d.(gshare)) then
        app f [g 0; g 1; g 2; g 3; g 4; dconv d msub mat (g 5); dconv d msub mat (g 6)]
      else if Constr.equal f (d.(gCShare)) then
        app f [g 0; g 1; g 2; g 3; g 4; dconv d msub mat (g 5); dconv d msub mat (g 6)]
      else if Constr.equal f (d.(gCRoot)) then app f [g 0; g 1; g 2; dconv d msub mat (g 3)]
      else c
  | _ => c
  end
with sconv (d : dk) (msub : constr -> constr -> constr -> constr -> constr) (m : bool) (s : constr) : constr :=
  let k := d.(gk) in
  let (f, a) := split_app s in
  let g i := Array.get a i in
  let rest i := Array.mapi (fun j x => if Int.equal j i then sconv d msub m x else x) a in
  let mk h i := Constr.Unsafe.make (Constr.Unsafe.App h (rest i)) in
  if Constr.equal f (d.(dEmpty)) then app (k.(kSEmpty)) (Array.to_list a)
  else if Constr.equal f (d.(dLiftF)) then mk (k.(kSLiftF)) 5
  else if Constr.equal f (d.(dLiftB)) then mk (k.(kSLiftB)) 5
  else if Constr.equal f (d.(dSubF)) then mk (k.(kSSubF)) 5
  else if Constr.equal f (d.(dSubB)) then mk (k.(kSSubB)) 5
  else if Constr.equal f (d.(dRenF)) then mk (k.(kSRenF)) 5
  else if Constr.equal f (d.(dRenB)) then mk (k.(kSRenB)) 5
  else if Constr.equal f (d.(dSubFA)) then
    (* T Nb Mb N M s x K u r *)
    if m then app (k.(kSSubF)) [g 0; g 1; g 2; g 3; g 4; sconv d msub m (g 5); g 6; msub (g 7) (g 2) (dconv d msub true (g 9)) (g 8)]
    else app (k.(kSSubFA)) [g 0; g 1; g 2; g 3; g 4; sconv d msub m (g 5); g 6; g 7; g 8; dconv d msub false (g 9)]
  else if Constr.equal f (d.(dSubBA)) then
    (* T Nb Mb N M s K u r *)
    if m then app (k.(kSSubB)) [g 0; g 1; g 2; g 3; g 4; sconv d msub m (g 5); msub (g 6) (g 2) (dconv d msub true (g 8)) (g 7)]
    else app (k.(kSSubBA)) [g 0; g 1; g 2; g 3; g 4; sconv d msub m (g 5); g 6; g 7; dconv d msub false (g 8)]
  else if Constr.equal f (d.(dLookF)) then
    (* T Nb Mb N M K s x w r *)
    app (k.(kSLookF)) [g 0; g 1; g 2; g 3; g 4; g 5; sconv d msub m (g 6); g 7; g 8; dconv d msub m (g 9)]
  else if Constr.equal f (d.(dLookB)) then
    app (k.(kSLookB)) [g 0; g 1; g 2; g 3; g 4; g 5; sconv d msub m (g 6); g 7; dconv d msub m (g 8)]
  else s.

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
  let rty := app constr:(@Adjustment.radj) [raw_ty t] in
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
  e_le : constr; e_te : constr; e_ae : constr; e_l : constr; e_hl : constr;
  e_lt : constr; e_tt : constr;
  e_labs : constr array; e_terms : constr list; e_atoms : constr array; e_nt : int; e_nb : int; e_ns : nats;
  e_defs : constr; e_defl : constr option list }.

Ltac2 finish (s : st) (t : constr) : env :=
  let ty := raw_ty t in
  let fs := collect_facts s in
  let labs := List.rev ((s.(labs)).(items)) in
  let terms := List.rev ((s.(terms)).(items)) in
  let atoms := List.rev ((s.(atoms)).(items)) in
  let le := list_of constr:(label) labs in
  let te := list_of ty terms in
  let ae := list_of constr:(radj $ty) atoms in
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
  { e_le := le; e_te := te; e_ae := ae; e_l := l; e_hl := hl;
    e_lt := lt; e_tt := btree ty terms;
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

(** A term that is a node [csubst L a t] as written, or as materialising
    writes it under a shared definition's binder: the body of the law's [sub] (a constant) at [N M a t].  The
    match is syntactic, with the body's four arguments as holes. *)
Ltac2 sub_body (sub : constr) : constr option :=
  match Constr.Unsafe.kind sub with
  | Constr.Unsafe.Constant k _ =>
      let rec strip n c := if Int.equal n 0 then Some c else
        match Constr.Unsafe.kind c with Constr.Unsafe.Lambda _ b => strip (Int.sub n 1) b | _ => None end in
      strip 4 (Std.eval_unfold [(Std.ConstRef k, Std.AllOccurrences)] sub)
  | _ => None
  end.

(** A substitution node ([cs] is [@csubst]). *)
Ltac2 is_csubst_in (cs : constr) (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args => if Constr.equal f cs then Int.equal (Array.length args) 8 else false
  | _ => false
  end.

(** A node [csubst L a t] ([c]) as the law's [sub] at [N M a t], which
    it is by conversion, with [sub] unfolded when it is a constant
    ([sub_body], remembered in [cache]). *)
Ltac2 node_to_sub (cache : (constr * constr option) list ref) (c : constr) : constr :=
  let (_, a) := split_app c in
  let sub := Array.get a 2 in
  let body :=
    match List.find_opt (fun (s, _) => Constr.equal s sub) (cache.(contents)) with
    | Some (_, b) => b
    | None => let b := sub_body sub in cache.(contents) := (sub, b) :: cache.(contents); b
    end in
  let args := [Array.get a 4; Array.get a 5; Array.get a 6; Array.get a 7] in
  match body with
  | Some b => Constr.Unsafe.substnl (List.rev args) 0 b
  | None => app sub args
  end.

(** [c] with each node in it written as [sub] ([node_to_sub]); [changed]
    set if there was one. *)
Ltac2 rec post_conv (li : inductive list) (cs : constr) (cache : (constr * constr option) list ref) (changed : bool ref) (c : constr) : constr :=
  if is_lit li c then c else
  let c' := Constr.Unsafe.map (post_conv li cs cache changed) c in
  if is_csubst_in cs c' then (changed.(contents) := true; node_to_sub cache c') else c'.

(** The goal changed to [g'], convertible to it: checked by the kernel,
    once, at [Qed]. *)
Ltac2 change_no_check (g' : constr) : unit :=
  let ev := nocast '(_ : $g') in
  let evid := match Constr.Unsafe.kind ev with Constr.Unsafe.Evar e _ => e | _ => Control.zero Not_found end in
  Std.exact_no_check ev;
  Control.new_goal evid.

(** Step 5: every node in the goal written as [sub], in one traversal
    ([post_conv]) and one [change]: by conversion, so with no proof.
    What [names_norm] rewrites to it builds as [sub] already. *)
Ltac2 names_post () : unit :=
  (* whether there is a node at all: found by the matcher, not by a
     traversal in Ltac2 *)
  match Control.case (fun () => Pattern.matches_subterm pat:(@csubst _ _ _ _ _ _ _ _) (Control.goal ())) with
  | Err _ => ()
  | Val _ =>
  let changed := { contents := false } in
  let g' := post_conv (lit_inds ()) constr:(@csubst) { contents := [] } changed (Control.goal ()) in
  if changed.(contents) then change_no_check g' else ()
  end.

(** ** Many rewrites at once

    [rewrite_many [(x₁, y₁, e₁); …]], each [eᵢ : xᵢ = yᵢ] with [xᵢ]
    closed: every occurrence of each [xᵢ] in the goal replaced, in one
    traversal of the goal, with one proof.  The goal is abstracted over
    the occurrences once, [F z₁ … zₙ]; a term [Q], built for [n], takes
    [F], the [xᵢ], [yᵢ], [eᵢ] and a proof of [F y₁ … yₙ], and gives one of
    [F x₁ … xₙ] by [eq_ind_r] on each, its motives mentioning only
    variables.  The kernel substitutes the arguments of [Q] in one pass.
    An [xᵢ] inside another is left for a further round; those that no
    longer occur (rewritten away inside another) are dropped. *)
Ltac2 rec abst_occ (li : inductive list) (find : constr -> int option) (n : int) (d : int) (c : constr) : constr :=
  if is_lit li c then c else
  match find c with
  | Some i => rel (Int.add d (Int.sub n i))
  | None => Constr.Unsafe.map_with_binders (fun d _ => Int.add d 1) (abst_occ li find n) d c
  end.

Ltac2 rewrite_round (eqs : (constr * constr * constr) list) : bool * (constr * constr * constr) list :=
  let xs := Array.of_list eqs in
  let n := Array.length xs in
  let found := Array.make n false in
  (* the [xᵢ] grouped by head; within a group, the last arguments are
     compared first *)
  let hl c := match Constr.Unsafe.kind c with
              | Constr.Unsafe.App h a => (h, Array.get a (Int.sub (Array.length a) 1))
              | _ => (c, c) end in
  let groups := { contents := [] } in
  Array.iteri (fun i (x, _, _) =>
    let (h, l) := hl x in
    let rec ins gs :=
      match gs with
      | [] => [(h, [(i, l)])]
      | (h', is) :: gs => if Constr.equal h h' then (h', (i, l) :: is) :: gs else (h', is) :: ins gs
      end in
    groups.(contents) := ins (groups.(contents))) xs;
  let groups := groups.(contents) in
  let find c :=
    let (h, lc) := hl c in
    match List.find_opt (fun (h', _) => Constr.equal h h') groups with
    | None => None
    | Some (_, is) =>
        let rec go is :=
          match is with
          | [] => None
          | (i, l) :: is =>
              if (if Constr.equal lc l then (let (x, _, _) := Array.get xs i in Constr.equal c x) else false)
              then (Array.set found i true; Some i) else go is
          end in
        go (List.rev is)
    end in
  let g := Control.goal () in
  let g' := abst_occ (lit_inds ()) find n 0 g in
  let idx := List.filter (fun i => Array.get found i) (List.init n (fun i => i)) in
  let rest := List.filter (fun i => Bool.neg (Array.get found i)) (List.init n (fun i => i)) in
  let rest := List.map (fun i => Array.get xs i) rest in
  match idx with
  | [] => (false, rest)
  | _ =>
      (* the occurrences found, renumbered [0 .. m-1] *)
      let m := List.length idx in
      let sel := Array.of_list (List.map (fun i => Array.get xs i) idx) in
      let pos := Array.make n 0 in
      List.iteri (fun j i => Array.set pos i j) idx;
      let g' := Constr.Unsafe.substnl (List.init n (fun k =>
                  let i := Int.sub (Int.sub n 1) k in
                  if Array.get found i then rel (Int.sub m (Array.get pos i)) else rel 1)) 0
                  (Constr.Unsafe.liftn m (Int.add n 1) g') in
      let tys := Array.map (fun (x, _, _) => Constr.type x) sel in
      let prop := constr:(Prop) in
      let anon ty := Constr.Binder.unsafe_make None Constr.Binder.Relevant ty in
      let fty := Array.fold_right (fun t acc => Constr.Unsafe.make (Constr.Unsafe.Prod (anon t) acc)) tys prop in
      let f := Array.fold_right (fun t acc => Constr.Unsafe.make (Constr.Unsafe.Lambda (anon t) acc)) tys g' in
      (* [Q]: binders F, (xᵢ, yᵢ, eᵢ)ᵢ, H *)
      let refp d p := rel (Int.sub d p) in
      let px i := Int.add 1 (Int.mul 3 i) in
      let py i := Int.add 2 (Int.mul 3 i) in
      let pe i := Int.add 3 (Int.mul 3 i) in
      let ph := Int.add (Int.mul 3 m) 1 in
      let dbody := Int.add ph 1 in
      let eqc := constr:(@eq) in
      let rec chain i cur :=
        if Int.lt i 0 then cur else
        let ti := Array.get tys i in
        let d1 := Int.add dbody 1 in
        let margs := List.init m (fun j => if Int.lt j i then refp d1 (py j) else if Int.equal j i then rel 1 else refp d1 (px j)) in
        let mot := Constr.Unsafe.make (Constr.Unsafe.Lambda (anon ti) (app (refp d1 0) margs)) in
        chain (Int.sub i 1)
          (app constr:(@eq_ind_r) [ti; refp dbody (py i); mot; cur; refp dbody (px i); refp dbody (pe i)]) in
      let body := chain (Int.sub m 1) (rel 1) in
      let hty := app (refp ph 0) (List.init m (fun j => refp ph (py j))) in
      let rec lams i acc :=
        if Int.lt i 0 then acc else
        let ti := Array.get tys i in
        let ety := app eqc [ti; rel 2; rel 1] in
        lams (Int.sub i 1) (Constr.Unsafe.make (Constr.Unsafe.Lambda (anon ti) (Constr.Unsafe.make (Constr.Unsafe.Lambda (anon ti)
              (Constr.Unsafe.make (Constr.Unsafe.Lambda (anon ety) acc)))))) in
      let q := Constr.Unsafe.make (Constr.Unsafe.Lambda (anon fty) (lams (Int.sub m 1) (Constr.Unsafe.make (Constr.Unsafe.Lambda (anon hty) body)))) in
      let newg := Constr.Unsafe.substnl (List.rev (List.map (fun (_, y, _) => y) (Array.to_list sel))) 0 g' in
      let ev := nocast '(_ : $newg) in
      let evid := match Constr.Unsafe.kind ev with Constr.Unsafe.Evar e _ => e | _ => Control.zero Not_found end in
      let args := List.flat_map (fun (x, y, e) => [x; y; e]) (Array.to_list sel) in
      Std.exact_no_check (app q (List.append (f :: args) [ev]));
      Control.new_goal evid;
      (true, rest)
  end.

Ltac2 rewrite_many (eqs : (constr * constr * constr) list) : unit :=
  let rec rounds eqs :=
    match eqs with
    | [] => ()
    | _ =>
        let (progress, rest) := rewrite_round eqs in
        if progress then rounds rest else ()
    end in
  rounds eqs.

(** Rewrites collected, to be made together ([rewrite_many]); the
    hypotheses their proofs use, to be cleared after. *)
Ltac2 Type rb := { mutable rb_eqs : (constr * constr * constr) list; mutable rb_hyps : ident list;
                   mutable rb_nodes : constr list }.

Ltac2 new_rb () : rb := { rb_eqs := []; rb_hyps := []; rb_nodes := [] }.

Ltac2 rb_push (b : rb) (l : constr) (r : constr) (pf : constr) : unit :=
  if List.exist (fun (l', _, _) => Constr.equal l l') (b.(rb_eqs)) then () else b.(rb_eqs) := (l, r, pf) :: b.(rb_eqs).

Ltac2 rb_flush (b : rb) : unit :=
  rewrite_many (List.rev (b.(rb_eqs)));
  Std.clear (b.(rb_hyps));
  b.(rb_eqs) := []; b.(rb_hyps) := [].

(** The closed applications of [h] in [c], anywhere. *)
Ltac2 rec apps_of (li : inductive list) (h : constr) (c : constr) (acc : constr list) : constr list :=
  if is_lit li c then acc else
  let acc :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App h' _ => if Bool.and (Constr.equal h h') (Constr.Unsafe.is_closed c) then c :: acc else acc
    | _ => acc
    end in
  let r := { contents := acc } in
  Constr.Unsafe.iter (fun x => r.(contents) := apps_of li h x (r.(contents))) c;
  r.(contents).

(** [eid : forall t, L t = R t], [L t] an application whose last argument
    is [t]: each [L t] among [b]'s nodes, rewritten (with [eid t]) to
    [rhs t], [R t] up to conversion. *)
Ltac2 rb_instances (b : rb) (eid : ident) (rhs : constr -> constr) : unit :=
  let pf := Control.hyp eid in
  let l :=
    match Constr.Unsafe.kind (Constr.type pf) with
    | Constr.Unsafe.Prod _ e =>
        match Constr.Unsafe.kind e with
        | Constr.Unsafe.App _ a => Array.get a 1
        | _ => Control.zero Not_found
        end
    | _ => Control.zero Not_found
    end in
  let (h, args) := match Constr.Unsafe.kind l with Constr.Unsafe.App h a => (h, a) | _ => Control.zero Not_found end in
  let k := Int.sub (Array.length args) 1 in
  let inst c :=
    let (h', a') := split_app c in
    if Bool.and (Constr.equal h h') (Int.equal (Array.length a') (Array.length args)) then
      let rec same i := if Int.equal i k then true
                        else if Constr.equal (Array.get args i) (Array.get a' i) then same (Int.add i 1) else false in
      if same 0 then Some (Array.get a' k) else None
    else None in
  List.iter (fun c => match inst c with
                      | Some t => rb_push b c (rhs t) (app pf [t])
                      | None => () end) (b.(rb_nodes));
  b.(rb_hyps) := eid :: b.(rb_hyps).

(** [pf : ty], an equation, asserted with no check and rewritten with:
    the type of [pf] is not computed. *)
Ltac2 rewrite_by (ty : constr) (pf : constr) : unit :=
  let id := fresh @E in
  assert_by id ty (fun () => Std.exact_no_check pf);
  rewrite_with (Control.hyp id); Std.clear [id].

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

Ltac2 some (ty : constr) (x : constr) : constr := app constr:(@Some) [ty; x].

(** [Forall2 (fun x od => od = Some d -> x = aeden d) atoms defs]: each
    defined atom is (convertibly) its definition. *)
Ltac2 defs_proof (t : constr) (rel : constr) (atoms : constr list) (defl : constr option list) : constr :=
  let aty := app constr:(@radj) [raw_ty t] in
  let oty := constr:(option aexpN) in
  let ys := List.map (fun od => match od with Some d => app constr:(@Some aexpN) [d] | None => constr:(@None aexpN) end) defl in
  let hs := List.map2 (fun x od => match od with Some _ => app constr:(@eq_refl) [aty; x] | None => constr:(I) end) atoms defl in
  forall2_proof aty oty rel atoms ys hs.

(** ** Rewriting an adjustment to its normal form *)

Ltac2 Type outcome := [ Shown (constr) | NotShown ].

(** [a = b], [b] the rendering of the normal form of [a], rewritten in the
    goal by [rw]. *)
(** [eq_refl x : x = y], [y] a computation the kernel does. *)
Ltac2 refl (ty : constr) (x : constr) : constr := app constr:(@eq_refl) [ty; x].

Ltac2 show_adj_with (rw : constr -> constr -> unit) (a : constr) : outcome :=
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
          let rd := (render_term t ty ns (en.(e_labs)) (Array.of_list terms) (en.(e_atoms)) (en.(e_nb)) (sh.(sh_l)) root false) in
          let b := rd.(rd_term) in
          (if Constr.equal a b then () else
           let (le, te, ae, hl) := (en.(e_le), en.(e_te), en.(e_ae), en.(e_hl)) in
           let (lt, tt) := (en.(e_lt), en.(e_tt)) in
           let sty := constr:((list aexpN * aexpN)%type) in
           let ht := vm_eq '(option $sty) '(hshowDN (order_of $l) $nt $nb $defs $e) (some sty (sh.(sh_val))) in
           let pt := raw_ty t in
           let rty := '(radj $pt) in
           let q := '(fun (rs : list (radj $pt)) (Ae : braun (radj $pt))
                          (hLe : $lt = bof $le) (hTe : $tt = bof $te) (hAe : Ae = bof ($ae ++ rs))
                          (hd : Forall2 (fun x od => match od with Some d => x = aedenB $lt $tt Ae d | None => True end) $ae $defs)
                          (hs : Forall2 (fun z0 d0 => z0 = aedenB $lt $tt Ae d0) rs $shd) =>
                        hshowDB_sound $le $te $ae rs $lt $tt Ae hLe hTe hAe $l $defs $e $shd $root $hl $ht hd hs) in
           let hrel := '(fun (Ae : braun (radj $pt)) (x : radj $pt) (od : option aexpN) =>
                           match od with Some d => x = aedenB $lt $tt Ae d | None => True end) in
           let srel := '(fun (Ae : braun (radj $pt)) (z0 : radj $pt) (d0 : aexpN) => z0 = aedenB $lt $tt Ae d0) in
           let p := '(fun x : $ty => $a = x) in
           let atoms := Array.to_list (en.(e_atoms)) in
           let pf := share_proof t n m p rd (fun rs hs root' =>
             let rsl := list_of rty rs in
             let at_ := btree rty (List.append atoms rs) in
             let hd := defs_proof t (app hrel [at_]) atoms (en.(e_defl)) in
             let hsp := forall2_proof rty constr:(aexpN) (app srel [at_]) rs (sh.(sh_l)) hs in
             app constr:(@adj_eq) [t; n; m; a; root';
               app q [rsl; at_; refl constr:(braun label) lt; refl '(braun $pt) tt; refl '(braun (radj $pt)) at_; hd; hsp]]) in
           rw b pf);
          Shown b
      | None => NotShown
      end
  end.

Ltac2 show_adj (a : constr) : outcome := show_adj_with (fun b pf => rewrite_by '($a = $b) pf) a.

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

Ltac2 add_new (c : constr) (acc : constr list) : constr list :=
  if List.exist (Constr.equal c) acc then acc else c :: acc.

(** The result of [hlook_showN], read back. *)
Ltac2 Type vsh := [ SVar (constr, constr) | STerm (constr, shown) | SLook (constr, constr, shown) ].

Ltac2 vm_vshow (c : constr) : (vsh * constr) option :=
  let res := Std.eval_vm None c in
  lazy_match! res with
  | Some (VSVarN ?h ?j) => Some (SVar h j, res)
  | Some (VSTermN ?u (?sh, ?r)) => Some (STerm u (mk_shown sh r), res)
  | Some (VSLookN ?g ?j (?sh, ?r)) => Some (SLook g j (mk_shown sh r), res)
  | None => None
  end.

(** The variable [v] at scope [k], from its reified label and index. *)
Ltac2 mk_var (labs : constr array) (ns : nats) (k : constr) (h : constr) (j : constr) : constr :=
  let jn := nat_lit ns (int_of_n j) in
  if is_lnone h then '(@bvar $k $jn stt) else let x := lab_env labs h in '(@fvar $k $x $jn).

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
          let (le, te, ae, l, hl) := (en.(e_le), en.(e_te), en.(e_ae), en.(e_l), en.(e_hl)) in
          let (lt, tt) := (en.(e_lt), en.(e_tt)) in
          let pt := raw_ty ty in
          let rty := '(radj $pt) in
          let atoms := Array.to_list (en.(e_atoms)) in
          univs ty;
          let look_p := '(hlook_showN (order_of $l) $nt $nb $e $eh $i) in
          match vm_vshow '(hlook_showN (order_of $l) $nt $nb $e $eh $i) with
          | Some (SVar h' j, res) =>
              let w := mk_var (en.(e_labs)) (en.(e_ns)) m h' j in
              let hres := vm_eq constr:(option vshowN) look_p res in
              let at_ := btree rty atoms in
              let q := '(fun (Ae : braun (radj $pt)) (hLe : $lt = bof $le) (hTe : $tt = bof $te) (hAe : Ae = bof ($ae ++ []))
                           => hlookB_var $le $te $ae [] $lt $tt Ae hLe hTe hAe $l $e $eh $i $h' $j $hl $hres) in
              assert_by id '(apply_var $a $v = Rename $w) (fun () =>
                refine_c (fun () => '(apply_var_rename _ _ _ _));
                Std.exact_no_check (app q [at_; refl constr:(braun label) lt; refl '(braun $pt) tt; refl '(braun (radj $pt)) at_]))
          | Some (STerm u sh, res) =>
              let (shd, root) := (sh.(sh_c), sh.(sh_root)) in
              let terms := en.(e_terms) in
              let x := nth_c terms (int_of_n u) in
              let (kx, ux) := term_parts x in
              let rd := render_term ty '(adj $ty $kx $m) (en.(e_ns)) (en.(e_labs)) (Array.of_list terms) (en.(e_atoms)) (en.(e_nb)) (sh.(sh_l)) root false in
              let b := rd.(rd_term) in
              let hres := vm_eq constr:(option vshowN) look_p res in
              let q := '(fun (rs : list (radj $pt)) (Ae : braun (radj $pt))
                             (hLe : $lt = bof $le) (hTe : $tt = bof $te) (hAe : Ae = bof ($ae ++ rs))
                             (hs : Forall2 (fun z0 d0 => z0 = aedenB $lt $tt Ae d0) rs $shd) =>
                           hlookB_term $le $te $ae rs $lt $tt Ae hLe hTe hAe $l $e $eh $i $u $shd $root $x $hl $hres hs eq_refl) in
              let srel := '(fun (Ae : braun (radj $pt)) (z0 : radj $pt) (d0 : aexpN) => z0 = aedenB $lt $tt Ae d0) in
              let p := '(fun y : adj $ty $kx $m => rapply (adj_raw $a) (var_raw $v) = inr ($x, adj_raw y)) in
              let pf := share_proof ty kx m p rd (fun rs hs _ =>
                let rsl := list_of rty rs in
                let at_ := btree rty (List.append atoms rs) in
                app q [rsl; at_; refl constr:(braun label) lt; refl '(braun $pt) tt; refl '(braun (radj $pt)) at_;
                       forall2_proof rty constr:(aexpN) (app srel [at_]) rs (sh.(sh_l)) hs]) in
              let fin := app constr:(@apply_var_bind) [ty; n; m; kx; a; v; ux; b; pf] in
              assert_by id '(apply_var $a $v = Bind $ux $b) (fun () => Std.exact_no_check fin)
          | _ => Control.zero Not_found
          end
  end.

Ltac2 names_apply () : unit :=
  Notations.repeat0 (fun () =>
    match! goal with
    | [ |- context [ @apply_var ?ty ?n ?m ?a ?v ] ] =>
        let t := app constr:(@apply_var) [ty; n; m; a; v] in
        let id := fresh @E in var_eq t id; rewrite_with (Control.hyp id); Std.clear [id]
    end).


(** Terms that are variables: the law's [tv] applied to a scope and a
    variable, or what [tv] unfolds to (a syntax's variable constructor),
    found by unfolding [tv] alone. *)
Ltac2 var_heads (vr : constr) : constr list :=
  match Constr.Unsafe.kind vr with
  | Constr.Unsafe.Constant c _ =>
      let probe := app vr [constr:(O); constr:(@fvar O EmptyString O)] in
      let (f, _) := split_app (Std.eval_unfold [(Std.ConstRef c, Std.AllOccurrences)] probe) in
      if Constr.equal f vr then [vr] else [vr; f]
  | _ => [vr]
  end.

Ltac2 var_term (heads : constr list) (u : constr) : (constr * constr) option :=
  let (f, a) := split_app u in
  if Bool.and (Int.equal (Array.length a) 2) (List.exist (Constr.equal f) heads) then Some (Array.get a 0, Array.get a 1)
  else None.

(** ** Converting before normalising

    In a substitution node [csubst L a t], the terms of [a] that are
    variables, and those that are substitutions [csubst L c
    u], are converted ([aconv]): a variable to a look-up through its
    payload, a substitution to [u] with [c] in its payload.  The result
    is normalised and shown, by the law's [sl_rel]. *)
Ltac2 rec pmatch (holes : constr option array) (p : constr) (c : constr) : bool :=
  match Constr.Unsafe.kind p with
  | Constr.Unsafe.Rel i =>
      if Int.le i 4 then
        match Array.get holes (Int.sub i 1) with
        | Some x => Constr.equal x c
        | None => if Constr.Unsafe.is_closed c then (Array.set holes (Int.sub i 1) (Some c); true) else false
        end
      else Constr.equal p c
  | Constr.Unsafe.App f args =>
      match Constr.Unsafe.kind c with
      | Constr.Unsafe.App g args' =>
          if Int.equal (Array.length args) (Array.length args') then
            if pmatch holes f g then
              let ok := { contents := true } in
              Array.iter2 (fun x y => if ok.(contents) then ok.(contents) := pmatch holes x y else ()) args args';
              ok.(contents)
            else false
          else false
      | _ => false
      end
  | _ => Constr.equal p c
  end.

Ltac2 as_node (cs : constr) (term : constr) (vr : constr) (sub : constr) (lw : constr) (body : constr option) (u : constr)
  : constr option :=
  let (uf, ua) := split_app u in
  if (if Constr.equal uf cs then (if Int.equal (Array.length ua) 8 then Constr.equal (Array.get ua 3) lw else false) else false)
  then Some u
  else match body with
       | Some p =>
           let holes := Array.make 4 None in
           if pmatch holes p u then
             match (Array.get holes 3, Array.get holes 2, Array.get holes 1, Array.get holes 0) with
             | (Some n, Some m, Some a, Some t) => Some (app cs [term; vr; sub; lw; n; m; a; t])
             | _ => None
             end
           else None
       | None => None
       end.

Ltac2 conv_one (bt : rb) (node : constr) : unit :=
  let (_, na) := split_app node in
  let (term, vr, sub, lw, n, m, a, t) :=
    (Array.get na 0, Array.get na 1, Array.get na 2, Array.get na 3, Array.get na 4, Array.get na 5,
     Array.get na 6, Array.get na 7) in
  let ty := term in
  let pt := raw_ty ty in
  let s := new_st () in
  let e := reify_adj s ty n m a in
  let cs := constr:(@csubst) in
  let vh := var_heads vr in
  let sbody := sub_body sub in
  (* the node's variable, when it is on one written out *)
  let vv := match var_term vh t with
            | Some (_, v) =>
                attempt (fun () =>
                  let (vf, va) := split_app (reify_var s v) in
                  if Constr.equal vf (s.(heads).(r_NVarE)) then
                    Some (v, Array.get va 0, nat_lit (s.(ns)) (int_of_n (Array.get va 1)))
                  else None) (fun _ => None)
            | None => None
            end in
  (* the terms of [a], then those of the nested substitutions found, in
     rounds *)
  let one acc ki :=
      let (nfs, vfs) := acc in let (k, it) := ki in
      let (_, u) := term_parts it in
      let (uf, ua) := split_app u in
      match var_term vh u with
      | Some (kw, w) =>
          match attempt (fun () =>
                  let ev := reify_var s w in
                  let (ef, ea) := split_app ev in
                  if Constr.equal ef (s.(heads).(r_NVarE)) then Some (k, Array.get ea 0, Array.get ea 1, kw, w, it)
                  else None)
                  (fun _ => None) with
          | Some x => (nfs, x :: vfs)
          | None => (nfs, vfs)
          end
      | None =>
      match as_node cs term vr sub lw sbody u with
      | Some nd =>
          (* a chain [u' [a₁] … [aₙ]]: one fact about its composite *)
          let rec coll nd acc :=
            let (_, ua) := split_app nd in
            let acc := (Array.get ua 4, Array.get ua 5, Array.get ua 6) :: acc in
            let u' := Array.get ua 7 in
            match as_node cs term vr sub lw sbody u' with
            | Some nd' => coll nd' acc
            | None => (u', acc)
            end in
          let (u', ch) := coll nd [] in
          let mc := let (_, ua) := split_app nd in Array.get ua 5 in
          let rec build l :=
            match l with
            | [(nn, mm, aa)] => (app constr:(@FOne) [term; nn; mm; aa], aa)
            | (nn, kk, aa) :: rest =>
                let (r, c) := build rest in
                (app constr:(@FCons) [term; nn; kk; mc; aa; r], app constr:(@compose) [term; nn; kk; mc; c; aa])
            | [] => Control.throw Not_found
            end in
          let (l, c) := build ch in
          let kc := let (nn, _, _) := List.hd ch in nn in
          let ce := reify_adj s ty kc mc c in
          let k' := tbl_add (s.(lets)) (s.(terms)) (raw_term ty kc u') in
          ((k, k', ce, kc, mc, l, u', it) :: nfs, vfs)
      | None => (nfs, vfs)
      end
      end in
  let rec rounds k0 acc :=
    let sz := (s.(terms)).(size) in
    if Int.ge k0 sz then acc else
    let items := List.skipn k0 (List.rev ((s.(terms)).(items))) in
    let acc := List.fold_left one acc (List.combine (List.init (Int.sub sz k0) (fun k => Int.add k0 k)) items) in
    rounds sz acc in
  let (nfs, vfs) := rounds 0 ([], []) in
  let en := finish s ty in
  let ns := en.(e_ns) in
  let nt := nat_lit ns (en.(e_nt)) in
  let nb := nat_lit ns (en.(e_nb)) in
  let l := en.(e_l) in
  let defs := en.(e_defs) in
  let nfty := constr:((N * (N * aexpN))%type) in
  let vfty := constr:((N * (lexp * N))%type) in
  let (pnn, pna, pvl, pln) := (constr:(@pair N (N * aexpN)), constr:(@pair N aexpN), constr:(@pair N (lexp * N)),
                               constr:(@pair lexp N)) in
  let nfi := List.map (fun (k, k', ce, _, _, _, _, _) => app pnn [n_lit k; app pna [n_lit k'; ce]]) nfs in
  let vfi := List.map (fun (k, h, i, _, _, _) => app pvl [n_lit k; app pln [h; i]]) vfs in
  let (nfc, vfc) := (list_of nfty nfi, list_of vfty vfi) in
  let fuel := nat_lit ns (List.length nfs) in
  let ce := '(aconvn $nfc $vfc $fuel $e) in
  let terms := en.(e_terms) in
  let (le, te, ae, hl) := (en.(e_le), en.(e_te), en.(e_ae), en.(e_hl)) in
  let (lt, tt) := (en.(e_lt), en.(e_tt)) in
  let rty := '(radj $pt) in
  let atoms := Array.to_list (en.(e_atoms)) in
  (* the facts the conversion uses: [hv] for the variables, [hn at_] for
     the nested substitutions *)
  let prn := '(fun (Ae : braun (radj $pt)) (x : N * (N * aexpN)) => let '(k, (k', C)) := x in
                 exists K M (c : adj $ty K M) (u : $ty K), adj_raw c = aedenB $lt $tt Ae C
                   /\ bnth $tt k' = Some (existT $ty K u) /\ bnth $tt k = Some (existT $ty M ($sub K M c u))) in
  let prv := '(fun x : N * (lexp * N) => let '(k, (h, i)) := x in
                 exists K (w : var K), bnth $tt k = Some (existT $ty K ($vr K w))
                   /\ var_raw w = mk_rvar (ldenB $lt h) (N.to_nat i)) in
  let vproofs := List.map (fun (k, h, i, kw, w, it) =>
      app constr:(@var_fact) [term; vr; sub; lw; lt; tt; n_lit k; h; i; kw; w;
        refl '(option $pt) (app constr:(@Some) [pt; it]);
        refl constr:(rvar) (app constr:(@var_raw) [kw; w])]) vfs in
  let hv := forall_proof vfty prv vfi vproofs in
  let hn at_ :=
    let nproofs := List.map (fun (k, k', ce, kc, mc, c, u', it) =>
        app constr:(@nest_fact) [term; vr; sub; lw; lt; tt; at_; ce; kc; mc; c; u'; n_lit k; n_lit k';
                   refl rty (app constr:(@adj_raw) [ty; kc; mc; app constr:(@fch_comp) [ty; kc; mc; c]]);
                   refl '(option $pt) (app constr:(@Some) [pt; raw_term ty kc u']);
                   refl '(option $pt) (app constr:(@Some) [pt; it])]) nfs in
    forall_proof nfty (app prn [at_]) nfi nproofs in
  let srel := '(fun (Ae : braun (radj $pt)) (z0 : radj $pt) (d0 : aexpN) => z0 = aedenB $lt $tt Ae d0) in
  (* the arguments of a proof under the shared definitions [rs] *)
  let env_args rs := 
    let at_ := btree rty (List.append atoms rs) in
    (at_, [list_of rty rs; at_; refl constr:(braun label) lt; refl '(braun $pt) tt; refl '(braun (radj $pt)) at_;
           hn at_; hv]) in
  (* materialising what is shown: whether [safeN] holds (computed), with
     its proof; the rendering as data, and as Gallina materialised *)
  let msub kk mm rc uc := match sbody with
    | Some body => Constr.Unsafe.substnl [uc; rc; mm; kk] 0 body
    | None => app cs [term; vr; sub; lw; kk; mm; rc; uc] end in
  let dkc := mk_dk () in
  let safe_of shd root :=
      let lhs := '(safeN (N.of_nat $nt) (N.of_nat $nb) $shd $root) in
      if Constr.equal (Std.eval_vm None lhs) constr:(true) then Some (vm_eq constr:(bool) lhs constr:(true)) else None in
  (* each definition and the root converted once; the [share]s and the
     chain over them rebuilt around them *)
  let mat_rd (rdd : rendered) : rendered :=
      let cv c := dconv dkc msub true c in
      let k := rdd.(rd_k) in
      let defs := Array.map cv (rdd.(rd_defs)) in
      let sufs := Array.copy (rdd.(rd_sufs)) in
      Array.set sufs k (cv (Array.get sufs k));
      let rec nest i :=
        if Int.lt i 0 then () else
        let (f, a) := split_app (Array.get (rdd.(rd_sufs)) i) in
        let b := match Constr.Unsafe.kind (Array.get a 6) with Constr.Unsafe.Lambda b _ => b | _ => Control.throw Not_found end in
        Array.set sufs i (app f [Array.get a 0; Array.get a 1; Array.get a 2; Array.get a 3; Array.get a 4; Array.get defs i;
                                 Constr.Unsafe.make (Constr.Unsafe.Lambda b (Array.get sufs (Int.add i 1)))]);
        nest (Int.sub i 1) in
      nest (Int.sub k 1);
      let rec chain c i :=
        let (f, a) := split_app c in
        if Int.equal i k then app f [Array.get a 0; Array.get a 1; Array.get a 2; Array.get sufs k]
        else match Constr.Unsafe.kind (Array.get a 6) with
             | Constr.Unsafe.Lambda b body =>
                 app f [Array.get a 0; Array.get a 1; Array.get a 2; Array.get a 3; Array.get a 4; Array.get defs i;
                        Constr.Unsafe.make (Constr.Unsafe.Lambda b (chain body (Int.add i 1)))]
             | _ => Control.throw Not_found
             end in
      { rdd with rd_defs := defs; rd_sufs := sufs; rd_term := Array.get sufs 0; rd_chain := chain (rdd.(rd_chain)) 0 } in
  let braun_rty := '(braun (radj $pt)) in
  let srel_m := '(fun (Ae' : braun (radj $pt)) (z : radj $pt) (d : aexpN) =>
                    forall v, drel (lawbase $vr $sub) (rapply (aedenB $lt $tt Ae' d) v) (rapply z v)) in
  (* at the root of the proof: the shared variables [rs] related to the
     shown definitions, one [def_rel] each, the new atom environment, and
     the root's data *)
  let mat_leaf (rdd : rendered) rs hs :=
      let k := rdd.(rd_k) in
      let rels := List.init k (fun j => rel (Int.mul 2 (Int.add j 1))) in
      let data_def i := Constr.Unsafe.liftn (Int.mul 2 (Int.sub k i)) 1
                          (Constr.Unsafe.substnl rels 0 (Array.get (rdd.(rd_defs)) i)) in
      let rootd := Constr.Unsafe.substnl rels 0 (Array.get (rdd.(rd_sufs)) k) in
      let hrel := List.mapi (fun i zh => let (z, h) := zh in let (kn, km) := Array.get (rdd.(rd_kl)) i in
                    app constr:(@def_rel) [term; vr; sub; kn; km; data_def i; z; h]) (List.combine rs hs) in
      let at' := btree rty (List.append atoms rs) in
      (at', rootd, hrel) in
  (* the nodes with adjustment [a] rewritten to ones with [a'], given
     [pf] relating them (the law's [sl_rel]); when [a'] is the identity, to
     their terms ([sl_id]) *)
  let is_id c := let (f, _) := split_app c in Constr.equal f constr:(@identity) in
  let node_rewrite a' pf :=
      let hid := fresh @H in
      assert_by hid '(forall v : var $n, drel (lawbase $vr $sub) (rapply (adj_raw $a) (var_raw v)) (rapply (adj_raw $a') (var_raw v)))
        (fun () => Std.exact_no_check pf);
      let eid := fresh @E in
      let hh := Control.hyp hid in
      (if is_id a' then
         assert_by eid '(forall t, @csubst $term $vr $sub $lw $n $m $a t = t)
           (fun () => Std.exact_no_check '(fun t => eq_trans (@csubst_rel $term $vr $sub $lw $n $m $a $a' $hh t)
                                                     (@node_id $term $vr $sub $lw $n t)))
       else
         assert_by eid '(forall t, @csubst $term $vr $sub $lw $n $m $a t = @csubst $term $vr $sub $lw $n $m $a' t)
           (fun () => Std.exact_no_check '(@csubst_rel $term $vr $sub $lw $n $m $a $a' $hh)));
      Std.clear [hid];
      rb_instances bt eid (fun t => if is_id a' then t else msub n m a' t) in
  (* a node on a variable rewritten to the term [ux] with the payload
     [b] ([sl_res]); to [ux] itself when [b] is the identity ([sl_id]) *)
  let term_rewrite b kx ux v pf :=
      let nt := app constr:(@node_term) [term; vr; sub; lw; n; m; a; v; kx; ux; b; pf] in
      if is_id b then
        rb_push bt node ux '(eq_trans $nt (@node_id $term $vr $sub $lw $kx $ux))
      else rb_push bt node (msub kx m b ux) nt in
  let at0 := btree rty atoms in
  let adj_path_mat sh :=
      let (shd, root) := (sh.(sh_c), sh.(sh_root)) in
      match safe_of shd root with
      | None => Control.zero Not_found
      | Some hm =>
          let rdd := render_term ty '(adj $ty $n $m) ns (en.(e_labs)) (Array.of_list terms) (en.(e_atoms)) (en.(e_nb))
                      (sh.(sh_l)) root true in
          let rd := mat_rd rdd in
          let a' := rd.(rd_term) in
          (* already as shown: nothing to do (not a failure, which would
             show it again without materialising) *)
          if (if Constr.equal a a' then Bool.neg (is_id a') else false) then () else
          let sty := constr:((list aexpN * aexpN)%type) in
          let ht := vm_eq '(option $sty) '(hshowDN (order_of $l) $nt $nb $defs $ce) (some sty (sh.(sh_val))) in
          let hd := defs_proof ty (app '(fun (Ae : braun (radj $pt)) (x : radj $pt) (od : option aexpN) =>
                          match od with Some d => x = aedenB $lt $tt Ae d | None => True end) [at0]) atoms (en.(e_defl)) in
          let hn0 := hn at0 in
          let q := '(fun (hn : Forall ($prn $at0) $nfc) (hv : Forall $prv $vfc)
                         (rs : list (radj $pt)) (Ae' : braun (radj $pt)) (hAe' : Ae' = bof ($ae ++ rs))
                         (hs : Forall2 (fun z d => forall v, drel (lawbase $vr $sub) (rapply (aedenB $lt $tt Ae' d) v) (rapply z v)) rs $shd)
                         (R : radj $pt) (hr : forall v, drel (lawbase $vr $sub) (rapply (aedenB $lt $tt Ae' $root) v) (rapply R v))
                         (v : var $n) =>
                       DTrans _ _ _ _
                         (conv_rel $vr $sub $nfc $vfc $lt $tt $at0 _ _ $fuel $e hn hv eq_refl eq_refl (var_raw v))
                         (DTrans _ _ _ _
                            (show_rel $vr $sub $le $te $ae rs $lt $tt $at0 Ae' eq_refl eq_refl eq_refl hAe'
                               $l $defs $ce $shd $root $hl $ht $hm $hd hs (var_raw v))
                            (hr (var_raw v)))) in
          let p := '(fun y : adj $ty $n $m => forall v : var $n, drel (lawbase $vr $sub) (rapply (adj_raw $a) (var_raw v)) (rapply (adj_raw y) (var_raw v))) in
          let pf := share_proof ty n m p rd (fun rs hs root_l =>
            let (at', rootd, hrel) := mat_leaf rdd rs hs in
            let hs' := forall2_proof rty constr:(aexpN) (app srel_m [at']) rs (sh.(sh_l)) hrel in
            app q [hn0; hv; list_of rty rs; at'; refl braun_rty at'; hs'; app constr:(@adj_raw) [ty; n; m; root_l];
                   app constr:(@mat_rel_a) [term; vr; sub; n; m; rootd]]) in
          node_rewrite a' pf
      end in
  let adj_path () :=
      match vm_show '(hshowDN (order_of $l) $nt $nb $defs $ce) with
      | Some sh => attempt (fun () => adj_path_mat sh) (fun _ =>
          let (shd, root) := (sh.(sh_c), sh.(sh_root)) in
          let rd := render_term ty '(adj $ty $n $m) ns (en.(e_labs)) (Array.of_list terms) (en.(e_atoms)) (en.(e_nb)) (sh.(sh_l)) root false in
          let a' := rd.(rd_term) in
          (if (if Constr.equal a a' then Bool.neg (is_id a') else false) then Control.zero Not_found else ());
          let sty := constr:((list aexpN * aexpN)%type) in
          let ht := vm_eq '(option $sty) '(hshowDN (order_of $l) $nt $nb $defs $ce) (some sty (sh.(sh_val))) in
          let q := '(fun (rs : list (radj $pt)) (Ae : braun (radj $pt))
                         (hLe : $lt = bof $le) (hTe : $tt = bof $te) (hAe : Ae = bof ($ae ++ rs))
                         (hn : Forall ($prn Ae) $nfc) (hv : Forall $prv $vfc)
                         (hd : Forall2 (fun x od => match od with Some d => x = aedenB $lt $tt Ae d | None => True end) $ae $defs)
                         (hs : Forall2 (fun z0 d0 => z0 = aedenB $lt $tt Ae d0) rs $shd) (v : var $n) =>
                       conv_rel $vr $sub $nfc $vfc $lt $tt Ae _ _ $fuel $e hn hv eq_refl
                         (hshowDB_sound $le $te $ae rs $lt $tt Ae hLe hTe hAe $l $defs $ce $shd $root $hl $ht hd hs)
                         (var_raw v)) in
          let hrel := '(fun (Ae : braun (radj $pt)) (x : radj $pt) (od : option aexpN) =>
                          match od with Some d => x = aedenB $lt $tt Ae d | None => True end) in
          let p := '(fun y : adj $ty $n $m => forall v : var $n, drel (lawbase $vr $sub) (rapply (adj_raw $a) (var_raw v)) (rapply (adj_raw y) (var_raw v))) in
          let pf := share_proof ty n m p rd (fun rs hs _ =>
            let (at_, args) := env_args rs in
            let hd := defs_proof ty (app hrel [at_]) atoms (en.(e_defl)) in
            let hsp := forall2_proof rty constr:(aexpN) (app srel [at_]) rs (sh.(sh_l)) hs in
            app q (List.append args [hd; hsp])) in
          node_rewrite a' pf)
      | None => Control.zero Not_found
      end in
  (* a node on a variable: the normal form followed from it, once *)
  let var_path v eh i :=
      let vty := constr:(option vshowN) in
      let look := '(hlook_showN (order_of $l) $nt $nb $ce $eh $i) in
      let look_p := '(hlook_showN (order_of $l) $nt $nb $ce $eh $i) in
      let r := '(fun (rs : list (radj $pt)) (Ae : braun (radj $pt)) (hn : Forall ($prn Ae) $nfc) (hv : Forall $prv $vfc) z
                     (hz : rapply (aedenB $lt $tt Ae $ce) (mk_rvar (ldenB $lt $eh) $i) = z) =>
                   conv_res $vr $sub $nfc $vfc $lt $tt Ae _ $fuel $e (mk_rvar (ldenB $lt $eh) $i) z hn hv eq_refl hz) in
      match vm_vshow look with
      | Some (SVar h' j, res) =>
          let w := mk_var (en.(e_labs)) ns m h' j in
          let hres := vm_eq vty look_p res in
          let (at_, args) := env_args [] in
          let q := '(fun (rs : list (radj $pt)) (Ae : braun (radj $pt))
                         (hLe : $lt = bof $le) (hTe : $tt = bof $te) (hAe : Ae = bof ($ae ++ rs))
                         (hn : Forall ($prn Ae) $nfc) (hv : Forall $prv $vfc) =>
                       $r rs Ae hn hv _ (hlookB_var $le $te $ae rs $lt $tt Ae hLe hTe hAe $l $ce $eh $i $h' $j $hl $hres)) in
          let pf := app q args in
          rb_push bt node '($vr $m $w) (app constr:(@node_var) [term; vr; sub; lw; n; m; a; v; w; pf])
      | Some (STerm u sh, res) =>
          let (shd, root) := (sh.(sh_c), sh.(sh_root)) in
          let x := nth_c terms (int_of_n u) in
          let (kx, ux) := term_parts x in
          match safe_of shd root with
          | Some hm =>
              (* the payload shown materialised ([term_rel], [mat_rel]) *)
              let rdd := render_term ty '(adj $ty $kx $m) ns (en.(e_labs)) (Array.of_list terms) (en.(e_atoms)) (en.(e_nb))
                          (sh.(sh_l)) root true in
              let rd := mat_rd rdd in
              let b := rd.(rd_term) in
              let hres := vm_eq vty look_p res in
              let hn0 := hn at0 in
              let q := '(fun (hn : Forall ($prn $at0) $nfc) (hv : Forall $prv $vfc)
                             (rs : list (radj $pt)) (Ae' : braun (radj $pt)) (hAe' : Ae' = bof ($ae ++ rs))
                             (hs : Forall2 (fun z d => forall v, drel (lawbase $vr $sub) (rapply (aedenB $lt $tt Ae' d) v) (rapply z v)) rs $shd)
                             (R : radj $pt) (hr : forall v, drel (lawbase $vr $sub) (rapply (aedenB $lt $tt Ae' $root) v) (rapply R v)) =>
                           DTrans _ _ _ _ ($r (@nil (radj $pt)) $at0 hn hv _ eq_refl)
                             (DTrans _ _ _ _
                                (term_rel $vr $sub $le $te $ae rs $lt $tt $at0 Ae' eq_refl eq_refl eq_refl hAe'
                                   $l $ce $eh $i $u $shd $root $x $hl $hres eq_refl $hm hs)
                                (pay_rel _ $x _ _ hr))) in
              let p := '(fun y : adj $ty $kx $m => drel (lawbase $vr $sub) (rapply (adj_raw $a) (var_raw $v)) (inr ($x, adj_raw y))) in
              let pf := share_proof ty kx m p rd (fun rs hs root_l =>
                let (at', rootd, hrel) := mat_leaf rdd rs hs in
                let hs' := forall2_proof rty constr:(aexpN) (app srel_m [at']) rs (sh.(sh_l)) hrel in
                app q [hn0; hv; list_of rty rs; at'; refl braun_rty at'; hs'; app constr:(@adj_raw) [ty; kx; m; root_l];
                       app constr:(@mat_rel_a) [term; vr; sub; kx; m; rootd]]) in
              term_rewrite b kx ux v pf
          | None =>
          let rd := render_term ty '(adj $ty $kx $m) ns (en.(e_labs)) (Array.of_list terms) (en.(e_atoms)) (en.(e_nb)) (sh.(sh_l)) root false in
          let b := rd.(rd_term) in
          let hres := vm_eq vty look_p res in
          let q := '(fun (rs : list (radj $pt)) (Ae : braun (radj $pt))
                         (hLe : $lt = bof $le) (hTe : $tt = bof $te) (hAe : Ae = bof ($ae ++ rs))
                         (hn : Forall ($prn Ae) $nfc) (hv : Forall $prv $vfc)
                         (hs : Forall2 (fun z0 d0 => z0 = aedenB $lt $tt Ae d0) rs $shd) =>
                       $r rs Ae hn hv _ (hlookB_term $le $te $ae rs $lt $tt Ae hLe hTe hAe $l $ce $eh $i $u $shd $root $x
                                            $hl $hres hs eq_refl)) in
          let p := '(fun y : adj $ty $kx $m => drel (lawbase $vr $sub) (rapply (adj_raw $a) (var_raw $v)) (inr ($x, adj_raw y))) in
          let pf := share_proof ty kx m p rd (fun rs hs _ =>
            let (at_, args) := env_args rs in
            app q (List.append args [forall2_proof rty constr:(aexpN) (app srel [at_]) rs (sh.(sh_l)) hs])) in
          term_rewrite b kx ux v pf
          end
      | Some (SLook g j sh, res) =>
          let (shd, root) := (sh.(sh_c), sh.(sh_root)) in
          match safe_of shd root with
          | Some hm =>
              (* the rest shown materialised ([look_rel], [mat_rel]) *)
              let shs := List.mapi (fun i d => (Int.add (en.(e_nb)) i, d)) (sh.(sh_l)) in
              let (rdd, _) := render_all ty ns (en.(e_labs)) (en.(e_atoms)) (en.(e_nb)) shs [(root, None, m)]
                                (given_scopes (Array.of_list terms)) (given_terms (Array.of_list terms)) true in
              let rd := mat_rd rdd in
              let k := rd.(rd_n) in
              let b := rd.(rd_term) in
              let w := mk_var (en.(e_labs)) ns k g j in
              let hres := vm_eq vty look_p res in
              let hn0 := hn at0 in
              let q := '(fun (hn : Forall ($prn $at0) $nfc) (hv : Forall $prv $vfc)
                             (rs : list (radj $pt)) (Ae' : braun (radj $pt)) (hAe' : Ae' = bof ($ae ++ rs))
                             (hs : Forall2 (fun z d => forall v, drel (lawbase $vr $sub) (rapply (aedenB $lt $tt Ae' d) v) (rapply z v)) rs $shd)
                             (R : radj $pt) (hr : forall v, drel (lawbase $vr $sub) (rapply (aedenB $lt $tt Ae' $root) v) (rapply R v)) =>
                           DTrans _ _ _ _ ($r (@nil (radj $pt)) $at0 hn hv _ eq_refl)
                             (DTrans _ _ _ _
                                (look_rel $vr $sub $le $te $ae rs $lt $tt $at0 Ae' eq_refl eq_refl eq_refl hAe'
                                   $l $ce $eh $i $g $j $shd $root $hl $hres $hm hs)
                                (hr (mk_rvar (ldenB $lt $g) (N.to_nat $j))))) in
              let p := '(fun y : adj $ty $k $m => drel (lawbase $vr $sub) (rapply (adj_raw $a) (var_raw $v)) (rapply (adj_raw y) (var_raw $w))) in
              let pf := share_proof ty k m p rd (fun rs hs root_l =>
                let (at', rootd, hrel) := mat_leaf rdd rs hs in
                let hs' := forall2_proof rty constr:(aexpN) (app srel_m [at']) rs (sh.(sh_l)) hrel in
                app q [hn0; hv; list_of rty rs; at'; refl braun_rty at'; hs'; app constr:(@adj_raw) [ty; k; m; root_l];
                       app constr:(@mat_rel_a) [term; vr; sub; k; m; rootd]]) in
              rb_push bt node (msub k m b (app vr [k; w])) (app constr:(@node_look) [term; vr; sub; lw; n; m; k; a; v; b; w; pf])
          | None =>
          let shs := List.mapi (fun i d => (Int.add (en.(e_nb)) i, d)) (sh.(sh_l)) in
          let (rd, _) := render_all ty ns (en.(e_labs)) (en.(e_atoms)) (en.(e_nb)) shs [(root, None, m)]
                           (given_scopes (Array.of_list terms)) (given_terms (Array.of_list terms)) false in
          let k := rd.(rd_n) in
          let b := rd.(rd_term) in
          let w := mk_var (en.(e_labs)) ns k g j in
          let hres := vm_eq vty look_p res in
          let q := '(fun (rs : list (radj $pt)) (Ae : braun (radj $pt))
                         (hLe : $lt = bof $le) (hTe : $tt = bof $te) (hAe : Ae = bof ($ae ++ rs))
                         (hn : Forall ($prn Ae) $nfc) (hv : Forall $prv $vfc)
                         (hs : Forall2 (fun z0 d0 => z0 = aedenB $lt $tt Ae d0) rs $shd) =>
                       $r rs Ae hn hv _ (hlookB_look $le $te $ae rs $lt $tt Ae hLe hTe hAe $l $ce $eh $i $g $j $shd $root
                                            $hl $hres hs)) in
          let p := '(fun y : adj $ty $k $m => drel (lawbase $vr $sub) (rapply (adj_raw $a) (var_raw $v)) (rapply (adj_raw y) (var_raw $w))) in
          let pf := share_proof ty k m p rd (fun rs hs _ =>
            let (at_, args) := env_args rs in
            app q (List.append args [forall2_proof rty constr:(aexpN) (app srel [at_]) rs (sh.(sh_l)) hs])) in
          rb_push bt node (msub k m b (app vr [k; w])) (app constr:(@node_look) [term; vr; sub; lw; n; m; k; a; v; b; w; pf])
          end
      | None => Control.zero Not_found
      end in
  match vv with
  | Some (v, eh, i) => attempt (fun () => var_path v eh i) (fun _ => match (nfs, vfs) with ([], []) => Control.zero Not_found | _ => adj_path () end)
  | None => adj_path ()
  end.

(** ** The passes *)

(** [f c], once, for each of [cs]; a failure is ignored. *)
Ltac2 each (f : constr -> unit) (cs : constr list) : unit :=
  List.iter (fun c => match Control.case (fun () => Control.once (fun () => f c)) with _ => () end) cs.

(** The nodes and adjustments of [c] not inside an adjustment: inside a
    node, only its term is looked in. *)
Ltac2 rec outer (li : inductive list) (cs : constr) (hs : heads) (c : constr) (acc : constr list) : constr list :=
  if is_lit li c then acc
  else if (if is_csubst_in cs c then Constr.Unsafe.is_closed c else false) then
    let (_, na) := split_app c in outer li cs hs (Array.get na 7) (add_new c acc)
  else if (if is_adj_head_in hs c then Constr.Unsafe.is_closed c else false) then add_new c acc
  else
    let r := { contents := acc } in
    Constr.Unsafe.iter (fun x => r.(contents) := outer li cs hs x (r.(contents))) c;
    r.(contents).

(** The adjustment of a node. *)
Ltac2 node_adj (c : constr) : constr := let (_, na) := split_app c in Array.get na 6.

(** [h : a = b], rewritten in the nodes [csubst L a t] like [node] only. *)
Ltac2 node_rw (bt : rb) (node : constr) (b : constr) (h : constr) : unit :=
  let (_, na) := split_app node in
  let (term, vr, sub, lw, n, m, a) :=
    (Array.get na 0, Array.get na 1, Array.get na 2, Array.get na 3, Array.get na 4, Array.get na 5, Array.get na 6) in
  let eid := fresh @E in
  assert_by eid '(forall t, @csubst $term $vr $sub $lw $n $m $a t = @csubst $term $vr $sub $lw $n $m $b t)
    (fun () => Std.exact_no_check
       (app '(fun (h0 : $a = $b) t => f_equal (fun x => @csubst $term $vr $sub $lw $n $m x t) h0) [h]));
  let cache := { contents := [] } in
  rb_instances bt eid (fun t => node_to_sub cache (app constr:(@csubst) [term; vr; sub; lw; n; m; b; t])).

(** A node on a variable written out. *)
Ltac2 is_var_node (c : constr) : bool :=
  let (_, na) := split_app c in
  match var_term (var_heads (Array.get na 1)) (Array.get na 7) with Some _ => true | None => false end.

(** Pass 1: each node's adjustment, with its nested substitutions and its
    variables converted to payloads and look-ups, normalised, and a node
    on a variable evaluated (the normal form followed from the variable);
    and each other adjustment normalised.  Nodes on variables go first,
    each on its own; another node's adjustment is taken once, as the
    rewrite changes the nodes that share it. *)
(** Chains of substitutions [t [a₁] … [aₙ]], each fused into one node by
    one lemma ([fch_fuse]), the outermost first. *)
Ltac2 fuse_chains (bt : rb) : unit :=
  let cs := constr:(@csubst) in
  let xs := List.filter (is_csubst_in cs) (List.rev (outer (lit_inds ()) cs (adj_heads ()) (Control.goal ()) [])) in
  let term_of x := Array.get (snd (split_app x)) 7 in
  (* a node that is another's term is inside that chain *)
  let inner := List.map term_of xs in
  let tops := List.filter (fun x => Bool.neg (List.exist (Constr.equal x) inner)) xs in
  each (fun x =>
    let (_, na) := split_app x in
    let (term, vr, sub, lw, m) := (Array.get na 0, Array.get na 1, Array.get na 2, Array.get na 3, Array.get na 5) in
    (* the chain, outermost first: (scope in, adjustment) *)
    let rec coll c acc :=
      let (f, a) := split_app c in
      if (if Constr.equal f cs then (if Int.equal (Array.length a) 8 then Constr.equal (Array.get a 3) lw else false) else false)
      then coll (Array.get a 7) ((Array.get a 4, Array.get a 5, Array.get a 6) :: acc)
      else (c, acc) in
    let (t0, ch) := coll x [] in
    match ch with
    | [] => Control.zero Not_found
    | [_] => Control.zero Not_found
    | (n0, _, _) :: _ =>
        (* [ch] is innermost first *)
        let rec build l :=
          match l with
          | [(nn, mm, aa)] => (app constr:(@FOne) [term; nn; mm; aa], aa)
          | (nn, kk, aa) :: rest =>
              let (r, c) := build rest in
              (app constr:(@FCons) [term; nn; kk; m; aa; r], app constr:(@compose) [term; nn; kk; m; c; aa])
          | [] => Control.throw Not_found
          end in
        let (l, ac) := build ch in
        rb_push bt x '(@csubst $term $vr $sub $lw $n0 $m $ac $t0) (app constr:(@fch_fuse) [term; vr; sub; lw; n0; m; l; t0])
    end) tops.

Ltac2 names_norm () : unit :=
  let bt := new_rb () in
  fuse_chains bt; rb_flush bt;
  let cs := constr:(@csubst) in
  let xs := List.rev (outer (lit_inds ()) cs (adj_heads ()) (Control.goal ()) []) in
  let (vs, xs) := List.partition (fun x => if is_csubst_in cs x then is_var_node x else false) xs in
  let rec dedup xs seen :=
    match xs with
    | [] => []
    | x :: xs =>
        let k := if is_csubst_in cs x then node_adj x else x in
        if List.exist (Constr.equal k) seen then dedup xs seen else x :: dedup xs (k :: seen)
    end in
  bt.(rb_nodes) := apps_of (lit_inds ()) cs (Control.goal ()) [];
  each (fun x =>
    let (e0, h0) := (bt.(rb_eqs), bt.(rb_hyps)) in
    let undo () := bt.(rb_eqs) := e0; bt.(rb_hyps) := h0 in
    attempt (fun () =>
      if is_csubst_in cs x then
        attempt (fun () => conv_one bt x)
          (fun _ => undo (); let _ := show_adj_with (node_rw bt x) (node_adj x) in ())
      else let _ := show_adj_with (rb_push bt x) x in ())
      (fun e => undo (); Control.zero e)) (List.append vs (dedup xs []));
  rb_flush bt.

(** ** The tactic

    [names], in one pass:
    1. rewrites with [names_pre], the monad laws that remove a Kleisli
       extension or move work into the adjustment (a syntax's [Subst]
       functor adds them): going under binders lifts the adjustment;
    2. rewrites with [names_node]: substitutions are nodes
       [csubst L a t];
    3. normalises ([names_norm]): a chain of nodes fuses into one
       ([fuse_chains]); in each node's adjustment, the terms
       that are substitutions become payloads and those that are
       variables look-ups, all the way down ([conv_one]); then a node on
       a variable [v] becomes what the normal form, followed from [v],
       gives (a variable, a term with its payload, or a variable looked
       up through the rest), and any other node's adjustment, and any
       other adjustment, is normalised; in a node, payloads shown are
       rendered as substitutions, [u⟨| b ⟩] as [u [b]] ([MatShow]), and
       an adjustment shown as the identity goes; the rewrites are made
       together, in one traversal and one proof ([rewrite_many]);
    4. evaluates [apply_var a v] for variables the normal form of [a]
       renames or sends to a term;
    5. writes the nodes back as the law's substitution, by conversion
       ([names_post]).
    Each step's results need nothing from the ones before: a payload's
    normal form is normal, and what a node on a variable becomes is a
    variable, or a node whose term is not one and whose adjustment is
    normal. *)
Ltac2 autorw (db : ident) : unit := Std.autorewrite false None [db] (concl ()).

Ltac2 names_pass () : unit :=
  (autorw @names_pre);
  (autorw @names_node);
  (names_norm ());
  (names_apply ());
  (names_post ()).

(** [names] commits to what it does: a failure after it does not backtrack
    into it. *)
Ltac2 names_tac () : unit := Control.enter (fun () => Control.once names_pass).

Ltac2 Notation "names" := names_tac ().

(** For Ltac1 proofs. *)
Ltac names := ltac2:(names_tac ()).
