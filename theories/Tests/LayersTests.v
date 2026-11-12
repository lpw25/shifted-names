(** Tests of the layered form (prototype, [Core/Layers.v]): the layered
    form of an expression normalises to the same stored word, and is
    small where the stored form is not. *)

From Stdlib Require Import String Ascii List NArith.
From ShiftedNames.Core Require Import Label Var Adjustment Normalise Shared Eval Layers.
Import ListNotations.

Definition lab (k : nat) : lexp :=
  LCon (String (ascii_of_nat (65 + Nat.div k 26)) (String (ascii_of_nat (65 + Nat.modulo k 26)) EmptyString)).
Definition O := order_of (@nil (lexp * lexp)).

(** [⟦ k := u ⟧] and [⟦ k \ j ⟧]. *)
Definition sub (k u : nat) : aexp := AInner (lab k) (TBindE u PId) AId.
Definition ren (k j : nat) : aexp := AInner (lab k) (TVarE (lab j) 0) (AOuter (lab j) AId).

Fixpoint chain (n k : nat) : list aexp := match n with 0 => [] | S n' => sub k k :: chain n' (S k) end.

(** Whether the layered form is the same adjustment, its size, and the
    size of the stored form. *)
Definition res (e : aexp) : option (bool * nat * nat) :=
  option_map (fun r => (snd (fst r), fst (fst (snd r)), snd (fst (snd r)))) (layers_check O 200 e).

(** A chain of substitutions: one step per substitution, where the
    stored form grows with the square. *)
Example chain_sizes :
  map (fun n => res (compose_steps (chain n 0))) [4; 8; 16; 32]
  = [Some (true, 47, 34); Some (true, 95, 116); Some (true, 191, 424); Some (true, 383, 1616)].
Proof. vm_compute. reflexivity. Qed.

(** The layered form of three substitutions: close a name, instantiate. *)
Example chain_3 :
  option_map (fun r => fst (fst r)) (layers_check O 10 (compose_steps (chain 3 0)))
  = Some (compose_steps
            [ AInner (lab 0) (TVarE LNone 0) (AOuter LNone AId); AInner LNone (TBindE 0 (PComp AId PId)) AId;
              AInner (lab 1) (TVarE LNone 0) (AOuter LNone AId); AInner LNone (TBindE 1 (PComp AId PId)) AId;
              AInner (lab 2) (TVarE LNone 0) (AOuter LNone AId); AInner LNone (TBindE 2 (PComp AId PId)) AId ]).
Proof. vm_compute. reflexivity. Qed.

(** A renaming after the chain is shared too. *)
Example chain_then_renaming :
  map (fun n => res (compose_steps (chain n 0 ++ [ren 100 101]))) [4; 16]
  = [Some (true, 52, 50); Some (true, 196, 476)].
Proof. vm_compute. reflexivity. Qed.

(** Two terms that do not depend on each other, with different
    payloads, [⟦ a := u⟨ x := p ⟩; b := v⟨ x := q ⟩ ⟧]: one layer for
    [u] and [v], each with a renaming payload, and one for [p] and [q]. *)
Definition indep : aexp :=
  AInner (lab 0) (TBindE 0 (PComp (sub 5 2) PId)) (AInner (lab 1) (TBindE 1 (PComp (sub 5 3) PId)) AId).

Example indep_layers :
  option_map (fun r => fst (fst r)) (layers_check O 10 indep)
  = Some (compose_steps
            [ AInner (lab 0) (TVarE LNone 0) (AInner (lab 1) (TVarE LNone 1) (iter 4 (AOuter LNone) AId));
              AInner LNone (TBindE 0 (PComp (AInner (lab 5) (TVarE LNone 0) AId) PId))
                (AInner LNone (TBindE 1 (PComp (AInner (lab 5) (TVarE LNone 1) AId) PId)) AId);
              AInner LNone (TBindE 2 (PComp AId PId)) (AInner LNone (TBindE 3 (PComp AId PId)) AId) ]).
Proof. vm_compute. reflexivity. Qed.

(** Atoms are not shared yet: a term carried past an atom keeps it in
    its payload, and the layered form is no smaller than the stored one. *)
Fixpoint achain (n k : nat) : list aexp := match n with 0 => [] | S n' => sub k k :: AAtom k :: achain n' (S k) end.

Example atoms_not_shared :
  map (fun n => res (compose_steps (achain n 0))) [4; 8] = [Some (true, 123, 111); Some (true, 391, 413)].
Proof. vm_compute. reflexivity. Qed.
