(** * The [names] tactic

    [names] proves an equation between adjustments, scoped ([adj T N M]) or
    raw ([radj T]), built from [identity], [compose], [weaken],
    [weaken_free], [extend], [extend_free], [lift], [lift_free] and
    [at_scope] (or their raw counterparts), with any other adjustment as an
    atom.  Labels may be concrete strings, the bound label, or variables;
    the order between label variables comes from hypotheses
    [label_lt (Some x) (Some y)] in the context.

    The equation is reified into [aexp], both sides are normalised
    (Normalise.v), and the normal forms compared.  The tactic fails when
    the normal forms differ, or when normalisation needed the order
    between two labels and no hypothesis gave it. *)

From Stdlib Require Import List String.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Indexed Normalise.
Import ListNotations.

(** ** Reification *)

(** The position of [x] in the list [l], adding it at the end if absent;
    returns the index and the new list. *)
Ltac lookup_add x l :=
  let rec go l n :=
    lazymatch l with
    | nil => constr:((n, false))
    | x :: _ => constr:((n, true))
    | _ :: ?r => go r (S n)
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
with reify_target t env :=
  lazymatch t with
  | RRename (mk_rvar ?h ?i) =>
      let _ := is_nat_lit i in
      lazymatch reify_label h env with
      | (?eh, ?env1) => constr:((TVarE eh i, env1))
      end
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
  | H : label_lt (Some ?x) (Some ?y) |- _ =>
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

(** ** The tactic *)

Ltac names_raw :=
  unfold ropen, rclose, rswap, rsubst1, rrename1, rshift;
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

Ltac names :=
  lazymatch goal with
  | |- @eq (adj _ _ _) _ _ =>
      apply adj_eq;
      cbn [adj_raw identity compose weaken weaken_free extend extend_free lift lift_free at_scope
           to_target var_raw bvar bvar0 fvar];
      names_raw
  | |- @eq (radj _) _ _ => names_raw
  end.
