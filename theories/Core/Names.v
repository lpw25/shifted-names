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
    and it means [a]; nothing is normalised again. *)

From Stdlib Require Import NArith List String Arith Bool StrictProp.
Open Scope bool_scope.
From ShiftedNames.Core Require Import Label Var Adjustment Indexed Syntax Normalise HConcrete HShow.
From ShiftedNames.Core Require HNorm.
From Stdlib Require Import PArith FMapPositive.
Import ListNotations.

(** ** Reification *)

(** [tt] when [v] is a variable (a variable is convertible only to
    itself, so it is looked up syntactically). *)
Ltac is_var_v v := let _ := match goal with _ => is_var v end in constr:(tt).

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
  let simple := match x with
                | adj_raw ?v => match constr:(tt) with _ => let _ := is_var_v v in true | _ => false end
                | _ => match constr:(tt) with _ => let _ := is_var_v x in true | _ => false end
                end in
  lazymatch go_syn l O with
  | (?n, true) => constr:((n, l))
  | (?n, false) =>
      lazymatch simple with
      | true => let l' := eval cbv [app] in (l ++ [x]) in constr:((n, l'))
      | false =>
      lazymatch go l O with
      | (?n, true) => constr:((n, l))
      | (?n, false) => let l' := eval cbv [app] in (l ++ [x]) in constr:((n, l'))
      end
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
                 | (?n, ?le') => let n' := eval cbv in (N.of_nat n) in constr:((LAtom n', (le', te, ae, pe)))
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
  | Laws.rapply_target ?a (RRename (mk_rvar ?h ?i)) =>
      let _ := is_nat_lit i in
      lazymatch reify_label h env with
      | (?eh, ?env1) => lazymatch reify_adj a env1 with
                        | (?ea, ?env2) => constr:((TLookE eh i ea, env2))
                        end
      end
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

(** ** Rendering

    [hshow] gives a normal form as shared definitions and an expression
    ([HDisplay]); they are rendered as [share]s and context forms:
    - a run of entries as a short form over its tail, lifts first:
      [x := u], [x := u⟨| r ⟩], [x as w], [x as w⟨| r ⟩];
    - [x ↦ g₀] over a pop of [g] as [⟦ x | Γ \ g | Γ[σ] ⟧] (a lift when
      [x = g]);
    - pops alone as outputs [⟦ \ y as _ ⟧];
    - composition as [⨾], atoms as written, shared definitions as the
      variables [share] binds. *)

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

(** The shares so far, latest first. *)
Ltac sh_nth sh k :=
  lazymatch k with
  | O => lazymatch sh with (?r, _) => r end
  | S ?k => lazymatch sh with (_, ?sh) => sh_nth sh k end
  end.

Ltac rvar le g j :=
  lazymatch g with
  | LNone => lazymatch goal with |- var ?M => exact (@bvar M j stt) end
  | _ => let gl := lab le g in exact (fvar gl j)
  end.

(** The entries of a short form, latest first, and its tail. *)
Ltac collect_short e lifts acc :=
  lazymatch e with
  | AInner ?x (TVarE ?x 0) (AOuter ?x ?B) =>
      lazymatch lifts with
      | true => collect_short B true (cons (x, @None texp) acc)
      | false => constr:((acc, e))
      end
  | AInner ?x (TVarE ?g 0) (AOuter ?g ?B) => constr:((acc, e))
  | AInner ?x ?t ?B => collect_short B false (cons (x, Some t) acc)
  | _ => constr:((acc, e))
  end.

Ltac collect_outs e acc :=
  lazymatch e with AOuter ?y ?B => collect_outs B (cons y acc) | _ => constr:((acc, e)) end.

Ltac render_onames_id le ys :=
  lazymatch ys with
  | nil => exact (OEnd IEmpty)
  | LNone :: ?r => let a := fresh "a" in refine (ONamB (fun a => _)); render_onames_id le r
  | ?y :: ?r => let yl := lab le y in let a := fresh "a" in refine (ONamF yl (fun a => _)); render_onames_id le r
  end.

Ltac render_onames_t le ys G :=
  lazymatch ys with
  | nil => exact (OEndT G IEmpty)
  | LNone :: ?r => let a := fresh "a" in refine (ONamB (fun a => _)); render_onames_t le r G
  | ?y :: ?r => let yl := lab le y in let a := fresh "a" in refine (ONamF yl (fun a => _)); render_onames_t le r G
  end.

Ltac render_a le te ae nb sh n e :=
  lazymatch e with
  | AId => exact identity
  | AAtom ?m =>
      lazymatch eval vm_compute in (Nat.ltb m nb) with
      | true => let s := atom ae m in exact s
      | false => let p := eval vm_compute in (n - 1 - (m - nb)) in let r := sh_nth sh p in exact r
      end
  | ACompose ?X ?Y => refine (compose _ _); [render_a le te ae nb sh n X|render_a le te ae nb sh n Y]
  | AInner ?x (TVarE ?x 0) (AOuter ?x _) => render_short le te ae nb sh n e
  | AInner ?x (TVarE ?g 0) (AOuter ?g ?B) => render_ren le te ae nb sh n x g B
  | AInner _ _ _ => render_short le te ae nb sh n e
  | AOuter _ _ =>
      lazymatch collect_outs e (@nil lexp) with
      | (?ys, AId) => refine (cform_id _); render_onames_id le ys
      | (?ys, ?tl) => let G := fresh "Γ" in
                      refine (cform (fun G => _) _); [render_onames_t le ys G|render_a le te ae nb sh n tl]
      end
  end
with render_short le te ae nb sh n e :=
  lazymatch collect_short e true (@nil (lexp * option texp)) with
  | (?acc, AId) => refine (cform_id (OShort _)); render_entries le te ae nb sh n acc
  | (?acc, ?tl) => refine (cform_id (OShortT (Nt:=0) (STail _ _)));
                   [render_entries le te ae nb sh n acc|render_a le te ae nb sh n tl]
  end
with render_entries le te ae nb sh n acc :=
  lazymatch acc with
  | nil => exact SEmpty
  | (LNone, None) :: ?r => refine (SLiftB _); render_entries le te ae nb sh n r
  | (?x, None) :: ?r => let xl := lab le x in refine (SLiftF _ xl); render_entries le te ae nb sh n r
  | (LNone, Some (TVarE ?g ?j)) :: ?r => refine (SRenB _ _); [render_entries le te ae nb sh n r|rvar le g j]
  | (?x, Some (TVarE ?g ?j)) :: ?r =>
      let xl := lab le x in refine (SRenF _ xl _); [render_entries le te ae nb sh n r|rvar le g j]
  | (LNone, Some (TBindE ?u (PComp AId PId))) :: ?r =>
      let ut := lnth te u in refine (SSubB _ ut PEmpty); render_entries le te ae nb sh n r
  | (?x, Some (TBindE ?u (PComp AId PId))) :: ?r =>
      let xl := lab le x in let ut := lnth te u in refine (SSubF _ xl ut PEmpty); render_entries le te ae nb sh n r
  | (LNone, Some (TBindE ?u (PComp ?R PId))) :: ?r =>
      let ut := lnth te u in refine (SSubBA _ ut _); [render_entries le te ae nb sh n r|render_a le te ae nb sh n R]
  | (?x, Some (TBindE ?u (PComp ?R PId))) :: ?r =>
      let xl := lab le x in let ut := lnth te u in
      refine (SSubFA _ xl ut _); [render_entries le te ae nb sh n r|render_a le te ae nb sh n R]
  | (LNone, Some (TLookE ?g ?j ?R)) :: ?r =>
      refine (SLookB _ _ _); [render_entries le te ae nb sh n r| |render_a le te ae nb sh n R]; rvar le g j
  | (?x, Some (TLookE ?g ?j ?R)) :: ?r =>
      let xl := lab le x in
      refine (SLookF _ xl _ _); [render_entries le te ae nb sh n r| |render_a le te ae nb sh n R]; rvar le g j
  end
with render_ren le te ae nb sh n x g B :=
  lazymatch B with
  | AId =>
      refine (cform_id _);
      lazymatch g with LNone => refine (OPosB _) | _ => let gl := lab le g in refine (OPosF _ gl) end;
      refine (OEnd _);
      lazymatch x with LNone => exact (IPosB IEmpty) | _ => let xl := lab le x in exact (IPosF IEmpty xl) end
  | _ =>
      let G := fresh "Γ" in
      refine (cform (fun G => _) _);
      [ lazymatch g with LNone => refine (OPosB _) | _ => let gl := lab le g in refine (OPosF _ gl) end;
        refine (OEndT G _);
        lazymatch x with LNone => exact (IPosB IEmpty) | _ => let xl := lab le x in exact (IPosF IEmpty xl) end
      | render_a le te ae nb sh n B ]
  end.

Ltac render_sh le te ae nb sh n defs root :=
  lazymatch defs with
  | nil => render_a le te ae nb sh n root
  | ?d :: ?ds =>
      let r := fresh "r" in
      refine (Indexed.share _ (fun r => _));
      [render_a le te ae nb sh n d
      |let sh' := constr:((r, sh)) in let n' := eval vm_compute in (S n) in render_sh le te ae nb sh' n' ds root]
  end.

(** ** The tactic *)

(** Unfolding context forms down to the raw constructors.  [share] is not
    unfolded: what it binds is reified as an atom. *)
Ltac names_unfold :=
  cbn [adj_raw identity compose at_scope
       cnil cent cbnd csub csubb cren crenb
       cnil_full cnil_short cent_full cent_short cbnd_full cbnd_short
       csub_full csub_short csubb_full csubb_short cren_full cren_short crenb_full crenb_short
       cform cform_id octx_den octx_probe ictx_den sctx_den nth slot_at slot_ix
       in_bound in_free out_bound out_free in_look_free in_look_bound pctx_den pctx_pay noslot pcompose padj_raw pid
       to_target var_raw bvar bvar0 fvar lvar vdummy vshift_bound vshift_free].

Ltac names_red t :=
  eval cbn [adj_raw identity compose at_scope
            cnil cent cbnd csub csubb cren crenb
            cnil_full cnil_short cent_full cent_short cbnd_full cbnd_short
            csub_full csub_short csubb_full csubb_short cren_full cren_short crenb_full crenb_short
            cform cform_id octx_den octx_probe ictx_den sctx_den nth slot_at slot_ix
            in_bound in_free out_bound out_free in_look_free in_look_bound pctx_den pctx_pay noslot pcompose padj_raw pid
            to_target var_raw bvar bvar0 fvar lvar vdummy vshift_bound vshift_free] in t.

Lemma share_intro_r {T N M K L} (a : adj T N M) (A : adj T K L) (f : adj T K L -> adj T N M) :
  (forall r, adj_raw r = adj_raw A -> a = f r) -> a = Indexed.share A f.
Proof. intros H; rewrite share_eq; apply H; reflexivity. Qed.

Lemma share_intro_p {T N M K L} (A : adj T K L) (f : adj T K L -> adj T N M) (P : adj T N M -> Prop) :
  (forall r, adj_raw r = adj_raw A -> P (f r)) -> P (Indexed.share A f).
Proof. intros H; rewrite share_eq; apply H; reflexivity. Qed.

(** The shares at the head of [t] as variables, wherever [t] occurs in the
    goal: then [k] with their raw forms. *)
Ltac intro_shares_t t rs k :=
  lazymatch t with
  | Indexed.share ?A ?f =>
      let r := fresh "r" in let H := fresh "Hr" in
      pattern t; apply (share_intro_p A f); intros r H;
      let t' := eval cbv beta in (f r) in
      let rs' := eval cbv [List.app] in (rs ++ [adj_raw r]) in
      cbv beta; intro_shares_t t' rs' k
  | _ => k rs
  end.

Ltac is_adj_expr a :=
  lazymatch a with
  | compose _ _ => idtac
  | cform_id _ => idtac
  | cform _ _ => idtac
  | at_scope _ => idtac
  | Indexed.share _ _ => idtac
  end.

(** The reifier sees term atoms after unfolding; they are shown as the
    subterms of the original adjustment they came from. *)
Ltac restore_term u a :=
  lazymatch a with
  | context [u] => u
  | _ =>
      match a with
      | context [?v] => let _ := constr:(@eq_refl _ u : u = v) in v
      | _ => u
      end
  end.

Ltac restore_terms te a :=
  lazymatch te with
  | nil => te
  | ?u :: ?r => let u' := restore_term u a in let r' := restore_terms r a in constr:(u' :: r')
  end.

Ltac lfacts_tac :=
  unfold lfacts_ok;
  repeat (apply Forall_cons;
          [lazymatch goal with
           | |- ?g => let g' := eval cbv -[olabel_lt] in g in
                      lazymatch g' with
                      | olabel_lt (Some ?x) (Some ?y) => lazymatch goal with H : label_lt x y |- _ => exact H end
                      end
           end|]);
  apply Forall_nil.

(** The shares of the goal's right-hand side as variables, with what each
    is: then [k] with their raw forms and the hypotheses, latest first. *)
Ltac intro_shares rs hs k :=
  lazymatch goal with
  | |- _ = Indexed.share ?A ?f =>
      let r := fresh "r" in let H := fresh "Hr" in
      apply (share_intro_r _ A f); intros r H; cbv beta;
      let rs' := eval cbv [List.app] in (rs ++ [adj_raw r]) in intro_shares rs' (H, hs) k
  | |- _ => k rs hs
  end.

(** The hypotheses, as the shared definitions they are. *)
Ltac shares_ok hs :=
  lazymatch goal with
  | |- Forall2 _ nil nil => constructor
  | |- Forall2 _ (_ :: _) (_ :: _) =>
      apply Forall2_cons; [|shares_ok hs];
      lazymatch goal with
      | |- ?x = _ => lazymatch goal with H : x = _ |- _ => let t := type of H in let t' := names_red t in exact (H : t') end
      end
  end.

(** [a = b], [b] the rendered normal form of [a]. *)
Ltac names_prove T le te ae pe l nb e shd root :=
  intro_shares (@nil (radj T)) tt ltac:(fun rs hs =>
    apply adj_eq;
    let Hl := fresh "Hl" in assert (Hl : lfacts_ok le l) by lfacts_tac;
    let Hs := fresh "Hs" in
    assert (Hs : Forall2 (fun z0 d0 => z0 = aeden le te (ae ++ rs) pe d0) rs shd) by (cbv [List.app]; shares_ok hs);
    exact_no_check (hshow_sound le te ae rs pe l e shd root Hl
                      (@eq_refl _ (Some (shd, root)) <: hshow (order_of l) (List.length te) (List.length ae) e = Some (shd, root))
                      Hs)).

(** Rewriting one adjustment to its normal form, shown as context forms,
    then running [kt] on its term atoms; runs [kt] alone when it is
    already shown that way, and [kn] when it cannot be shown (a payload
    atom in a term with a payload, say). *)
Ltac names_rewrite_k a kt kn :=
  let ty := type of a in
  lazymatch ty with
  | adj ?T _ _ =>
      let r := names_red (adj_raw a) in
      let env0 := constr:((@nil label, @nil T, @nil (radj T), @nil (rpadj T))) in
      lazymatch reify_adj_top r env0 with
      | (?e, ?env1) =>
          lazymatch collect_facts env1 (@nil (lexp * lexp)) with
          | ((?le, ?te, ?ae, ?pe), order_of ?l) =>
              let nb := eval vm_compute in (List.length ae) in
              let d := eval vm_compute in (hshow (order_of l) (List.length te) nb e) in
              lazymatch d with
              | Some (?shd, ?root) =>
                  let te' := restore_terms te a in
                  let bb := fresh "b" in
                  unshelve evar (bb : ty); [render_sh le te' ae nb tt 0 shd root|];
                  let b := eval cbv delta [bb] in bb in
                  clear bb;
                  tryif constr_eq a b then kt te'
                  else (let E := fresh "E" in
                        assert (E : a = b) by names_prove T le te ae pe l nb e shd root;
                        rewrite E; clear E; kt te')
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
                          let nb := eval vm_compute in (List.length ae) in
                          let pr := eval vm_compute in (hlook_pay F (List.length te) nb e eh i) in
                          lazymatch pr with
                          | Some (?u, (?shd, ?root)) =>
                              let te' := restore_terms te a in
                              let bb := fresh "b" in
                              unshelve evar (bb : adj T 0 M); [render_sh le te' ae nb tt 0 shd root|];
                              let b := eval cbv delta [bb] in bb in
                              clear bb;
                              let x := lnth te' u in
                              assert (E : apply_var a v = Bind x (pcompose b pid))
                                by (apply apply_var_bind;
                                    intro_shares_t b (@nil (radj T)) ltac:(fun rs =>
                                      names_unfold;
                                      change (rapply (aeden le te (ae ++ rs) pe e) (mk_rvar (lden le eh) i)
                                              = inr (x, rpcompose (aeden le te (ae ++ rs) pe root) rpidentity));
                                      refine (hbind_show_sound le te ae rs pe l e eh i u shd root x _ _ _ _);
                                      [ lfacts_tac
                                      | vm_cast_no_check (@eq_refl _ (Some (u, (shd, root))))
                                      | shares_ok tt
                                      | reflexivity ]))
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
(** Materialising: an adjustment [A] to the closed scope with terms with
    payload adjustments, used in a substitution, is replaced by [A'] where
    the first such term [u⟨b⟩] is [u [b]], when the syntax has a
    [SubstMat] instance. *)
Ltac names_mat_one A :=
  lazymatch type of A with
  | adj ?T ?N 0 =>
      let inst := constr:(_ : SubstMat T) in
      let r := names_red (adj_raw A) in
      let env0 := constr:((@nil label, @nil T, @nil (radj T), @nil (rpadj T))) in
      lazymatch reify_adj_top r env0 with
      | (?e, ?env1) =>
          lazymatch collect_facts env1 (@nil (lexp * lexp)) with
          | ((?le, ?te, ?ae, ?pe), order_of ?l) =>
              let F := constr:(order_of l) in
              let nb := eval vm_compute in (List.length ae) in
              let n1 := eval vm_compute in (List.length te) in
              let n2 := eval vm_compute in (S n1) in
              let d := eval vm_compute in (hmat_display F n2 nb e n1) in
              lazymatch d with
              | Some (?sh', ?r') =>
                  let nbb := eval vm_compute in (nb + List.length sh') in
                  let tg := eval vm_compute in (hmat_target F n1 nbb e) in
                  lazymatch tg with
                  | Some (?u, (?shb, ?rb)) =>
                      let te0 := restore_terms te A in
                      let bb := fresh "b" in
                      unshelve evar (bb : adj T 0 0); [render_sh le te0 ae nbb tt 0 shb rb|];
                      let b := eval cbv delta [bb] in bb in
                      clear bb;
                      let ut := lnth te0 u in
                      let fb := eval hnf in (@sm_back _ inst) in
                      let fs := eval hnf in (@sm_subst _ inst 0 0 b) in
                      let fo := eval hnf in (@sm_of _ inst) in
                      let x := eval cbv beta in (fb (fs (fo ut))) in
                      let te2 := eval cbv [List.app] in (te ++ [x]) in
                      let te2' := eval cbv [List.app] in (te0 ++ [x]) in
                      let bb2 := fresh "A" in
                      unshelve evar (bb2 : adj T N 0); [render_sh le te2' ae nb tt 0 sh' r'|];
                      let A' := eval cbv delta [bb2] in bb2 in
                      clear bb2;
                      let H := fresh "H" in
                      assert (H : forall v : var N, mrel (@sm_g _ inst) (rapply (adj_raw A) (var_raw v)) (rapply (adj_raw A') (var_raw v)));
                      [ intro_shares_t A' (@nil (radj T)) ltac:(fun rs =>
                          intros v; names_unfold;
                          change (mrel (@sm_g _ inst) (rapply (aeden le te2 (ae ++ rs) pe e) (var_raw v))
                                    (rapply (aeden le te2 (ae ++ rs) pe r') (var_raw v)));
                          let Hl := fresh "Hl" in assert (Hl : lfacts_ok le l) by lfacts_tac;
                          let L1 := fresh "L1" in assert (L1 : n1 <= List.length te2) by (cbn [List.length]; repeat constructor);
                          let L2 := fresh "L2" in assert (L2 : n2 <= List.length te2) by (cbn [List.length]; repeat constructor);
                          let Ht := fresh "Ht" in
                          assert (Ht : hmat_target (order_of l) n1 nbb e = Some (u, (shb, rb)))
                            by vm_cast_no_check (@eq_refl _ (Some (u, (shb, rb))));
                          let Hd := fresh "Hd" in
                          assert (Hd : hmat_display (order_of l) n2 (List.length ae) e n1 = Some (sh', r'))
                            by vm_cast_no_check (@eq_refl _ (Some (sh', r')));
                          let Hn := fresh "Hn" in
                          assert (Hn : nbb = List.length ae + List.length sh') by (vm_compute; reflexivity);
                          let Hs := fresh "Hs" in
                          assert (Hs : Forall2 (fun z0 d0 => z0 = aeden le te2 (ae ++ rs) pe d0) rs (sh' ++ shb))
                            by (cbv [List.app]; shares_ok tt);
                          let Hk := fresh "Hk" in
                          assert (Hk : forall y, nth_error te2 u = Some y ->
                                    nth_error te2 n1 = Some (@sm_g _ inst (rpcompose (aeden le te2 (ae ++ rs) pe rb) rpidentity) y))
                            by (intros ? Hy; cbn [nth_error] in Hy |- *; injection Hy as <-; f_equal; symmetry;
                                exact (@sm_g_spec _ inst b ut));
                          exact (hmat_show_sound le te2 ae rs pe (@sm_g _ inst) l e n1 u shb rb sh' r' nbb n1 n2
                                   Hl L1 L2 Ht Hd Hn Hs Hk (var_raw v)))
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
