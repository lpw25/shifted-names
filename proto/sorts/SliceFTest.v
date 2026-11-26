(** * Prototype: the library's substitution and [names] on System F terms,
    from the slice ([SliceF]) *)

From Stdlib Require Import Arith List StrictProp.
From ShiftedNames.Core Require Import Label Var Adjustment Laws Scoped Indexed Syntax Subst Names PMap.
From Proto Require Desc Slice SliceF.
Import Desc (tm, ty, tmvar, lam, app, tlam, tapp, tyvar).

Definition tsh {G K} (u : tm G K) : tm (S G) K := SliceF.shN 1 u.
Arguments tsh : simpl never.

#[export] Instance tmF_kleisli G : Kleisli (tm G) (tm G) := {| Syntax.kleisli := @SliceF.kl_tmF G |}.
#[export] Instance tmF_syntax G : Syntax (tm G) := {|
  Syntax.tvar := @tmvar G;
  Syntax.kleisli_var := proj1 (SliceF.tmF_laws G);
  Syntax.kleisli_ext := proj1 (proj2 (SliceF.tmF_laws G));
  Syntax.kleisli_rebase := proj1 (proj2 (proj2 (SliceF.tmF_laws G)));
  Syntax.kleisli_unit_ := proj1 (proj2 (proj2 (proj2 (SliceF.tmF_laws G))));
  Syntax.kleisli_assoc_ := proj2 (proj2 (proj2 (proj2 (SliceF.tmF_laws G)))) |}.
Canonical Structure tmF_kleisli.
Canonical Structure tmF_syntax.

#[export] Instance tsh_map G : SyntaxMap (@tsh G) := {|
  smap_var := fun K v => eq_refl;
  smap_kleisli := fun N M f K L e u => SliceF.kl_tmF_shN G f e u |}.

Lemma kleisli_tlam G {N M} (f : morph (tm G) N M) {K L} (e : ext N M K L) (b : tm (S G) K) :
  kleisli f e (tlam b) = tlam (kleisli (mmap (@tsh G) f) e b).
Proof. exact (SliceF.kl_tmF_tlam G f e b). Qed.

Lemma kleisli_lam G {N M} (f : morph (tm G) N M) {K L} (e : ext N M K L) A (b : tm G (S K)) :
  kleisli f e (lam A b) = lam A (kleisli f (ext_under e) b).
Proof. reflexivity. Qed.

Lemma kleisli_app G {N M} (f : morph (tm G) N M) {K L} (e : ext N M K L) (t u : tm G K) :
  kleisli f e (app t u) = app (kleisli f e t) (kleisli f e u).
Proof. reflexivity. Qed.

Lemma kleisli_tapp G {N M} (f : morph (tm G) N M) {K L} (e : ext N M K L) (t : tm G K) A :
  kleisli f e (tapp t A) = tapp (kleisli f e t) A.
Proof. reflexivity. Qed.

Notation sub G K K' := (adj (tm G) K K').

(** ** Term substitution *)

Example sub_id {G K} (t : tm G K) : t [⟦⟧] = t.
Proof. names; reflexivity. Qed.

Example sub_fuse {G K K' K''} (a1 : sub G K K') (a2 : sub G K' K'') (t : tm G K) : t [a1] [a2] = t [a1 ⨾ a2].
Proof. names; reflexivity. Qed.

Theorem open_close {G K} x (t : tm G K) : t [⟦ x \ · ⟧] [⟦ · \ x ⟧] = t.
Proof. names; reflexivity. Qed.

Example sub_lam {G K K'} (a : sub G K K') A (b : tm G (S K)) : (lam A b) [a] = lam A (b [lift a]).
Proof. rewrite kleisli_lam; names; reflexivity. Qed.

(** ** Under type binders *)

Example sub_tlam {G K K'} (a : sub G K K') (b : tm (S G) K) : (tlam b) [a] = tlam (b [pmap (@tsh G) a]).
Proof. rewrite kleisli_tlam; names; reflexivity. Qed.

Example sub_tlam_inst x (u : tm 0 0) (b : tm 1 0) : (tlam b) [⟦ x := u ⟧] = tlam (b [⟦ x := (tsh u) ⟧]).
Proof. rewrite kleisli_tlam; names; reflexivity. Qed.

Example sub_tlam_compose {G K K' K''} (a1 : sub G K K') (a2 : sub G K' K'') (b : tm (S G) K) :
  (tlam b) [a1] [a2] = tlam (b [pmap (@tsh G) (a1 ⨾ a2)]).
Proof. rewrite !kleisli_tlam; names; reflexivity. Qed.

Example sub_tlam_lam {G K K'} (a : sub G K K') (A : ty (S G)) (b : tm (S G) (S K)) :
  (tlam (lam A b)) [a] = tlam (lam A (b [lift (pmap (@tsh G) a)])).
Proof. rewrite kleisli_tlam, kleisli_lam; names; reflexivity. Qed.

Example sub_tlam_inst_open x (u : tm 0 0) (b : tm 1 1) :
  (tlam (lam (tyvar Indexed.bvar0) b)) [⟦ x := u ⟧] = tlam (lam (tyvar Indexed.bvar0) (b [lift ⟦ x := (tsh u) ⟧])).
Proof. rewrite kleisli_tlam, kleisli_lam; names; reflexivity. Qed.
