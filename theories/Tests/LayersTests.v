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

(** Whether the layered form is the same adjustment, its size, the size
    of the expression, and the size of the stored form. *)
Definition res (e : aexp) : option (bool * nat * nat * nat) :=
  option_map (fun r => (snd (fst r), fst (fst (snd r)), csize e, snd (fst (snd r)))) (layers_check O 700 e).

(** A chain of substitutions comes back as written, where the stored
    form grows with the square. *)
Example chain_3 :
  option_map (fun r => fst (fst r)) (layers_check O 10 (compose_steps (chain 3 0)))
  = Some (compose_steps (chain 3 0)).
Proof. vm_compute. reflexivity. Qed.

Example chain_sizes :
  map (fun n => res (compose_steps (chain n 0))) [4; 8; 16; 32]
  = [Some (true, 8, 8, 26); Some (true, 16, 16, 100); Some (true, 32, 32, 392); Some (true, 64, 64, 1552)].
Proof. vm_compute. reflexivity. Qed.

(** A renaming after the chain is shared too. *)
Example chain_then_renaming :
  map (fun n => res (compose_steps (chain n 0 ++ [ren 100 101]))) [4; 16]
  = [Some (true, 10, 10, 40); Some (true, 34, 34, 442)].
Proof. vm_compute. reflexivity. Qed.

(** So are atoms: a substitution and an atom, repeated. *)
Fixpoint achain (n k : nat) : list aexp := match n with 0 => [] | S n' => sub k k :: AAtom k :: achain n' (S k) end.

Example atom_chain :
  option_map (fun r => fst (fst r)) (layers_check O 10 (compose_steps (achain 2 0)))
  = Some (compose_steps (achain 2 0)).
Proof. vm_compute. reflexivity. Qed.

Example atom_chain_sizes :
  map (fun n => res (compose_steps (achain n 0))) [4; 8; 16]
  = [Some (true, 12, 12, 64); Some (true, 24, 24, 272); Some (true, 48, 48, 1376)].
Proof. vm_compute. reflexivity. Qed.

(** Two terms that do not depend on each other, with different
    payloads, [⟦ a := u⟨ x := p ⟩; b := v⟨ x := q ⟩ ⟧]: [u] and [v] are
    written with a renaming payload each, and [p] and [q] after them. *)
Definition indep : aexp :=
  AInner (lab 0) (TBindE 0 (PComp (sub 5 2) PId)) (AInner (lab 1) (TBindE 1 (PComp (sub 5 3) PId)) AId).

Example indep_layers :
  option_map (fun r => fst (fst r)) (layers_check O 10 indep)
  = Some (compose_steps
            [ AInner (lab 0) (TBindE 0 (PComp (AInner (lab 5) (TVarE LNone 0) AId) PId))
                (AInner (lab 1) (TBindE 1 (PComp (AInner (lab 5) (TVarE LNone 1) AId) PId))
                   (AOuter LNone (AOuter LNone AId)));
              AInner LNone (TBindE 2 PId) (AInner LNone (TBindE 3 PId) AId) ]).
Proof. vm_compute. reflexivity. Qed.
