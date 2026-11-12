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
            [ AInner (lab 0) (TBindE 0 (PComp (AInner (lab 5) (TVarE LNone 1) AId) PId))
                (AInner (lab 1) (TBindE 1 (PComp (AInner (lab 5) (TVarE LNone 0) AId) PId))
                   (AOuter LNone (AOuter LNone AId)));
              AInner LNone (TBindE 3 PId) (AInner LNone (TBindE 2 PId) AId) ]).
Proof. vm_compute. reflexivity. Qed.

(** Two families of terms that share nothing: a term whose payload is a
    chain of its own, on top of a chain.  Each chain is written once;
    the parties of one step over the other's substitutions by a shared
    renaming. *)
Definition ch (n k : nat) : aexp := compose_steps (chain n k).
Definition two (n : nat) : aexp := AInner (lab 600) (TBindE 190 (PComp (ch n 100) PId)) (ch n 0).

Example two_families :
  map (fun n => res (two n)) [2; 4; 8]
  = [Some (true, 18, 10, 17); Some (true, 28, 18, 55); Some (true, 48, 34, 203)].
Proof. vm_compute. reflexivity. Qed.

(** Several terms with the same chain as payload, and several with
    another: the payload is written twice in the expression for each. *)
Fixpoint alt (k n i : nat) : aexp :=
  match k with
  | 0 => AId
  | S k' =>
      AInner (lab (300 + 2 * i)) (TBindE (200 + 2 * i) (PComp (ch n 0) PId))
        (AInner (lab (301 + 2 * i)) (TBindE (201 + 2 * i) (PComp (ch n 100) PId)) (alt k' n (S i)))
  end.

Example shared_families :
  map (fun n => res (alt 2 n 0)) [2; 4] = [Some (true, 23, 24, 26); Some (true, 35, 40, 64)].
Proof. vm_compute. reflexivity. Qed.

(** Many small families, each a term with its own chain. *)
Fixpoint fams (k n i : nat) : aexp :=
  match k with
  | 0 => AId
  | S k' => AInner (lab (300 + i)) (TBindE (200 + i) (PComp (ch n (20 * i)) PId)) (fams k' n (S i))
  end.

Example many_families :
  map (fun k => res (fams k 2 0)) [2; 4] = [Some (true, 19, 12, 20); Some (true, 39, 24, 40)].
Proof. vm_compute. reflexivity. Qed.

(** A term with the identity payload beside a chain. *)
Example beside_chain :
  map (fun n => res (AInner (lab 600) (TBindE 190 PId) (ch n 20))) [4; 8]
  = [Some (true, 12, 10, 28); Some (true, 20, 18, 102)].
Proof. vm_compute. reflexivity. Qed.

