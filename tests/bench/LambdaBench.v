(** Workloads for timing the extracted substitution of the λ example
    (run by [tests/bench/run.sh]). *)
From Stdlib Require Import String Arith List.
From ShiftedNames.Extraction Require Import Extraction.
From ShiftedNames.Core Require Import Label Var Indexed.
From ShiftedNames.Examples Require Import Lambda.
Import LS.
Open Scope string_scope.

Definition tsubst {N M} (a : sub N M) (t : tm N) : tm M := t [a].
Definition topen_f {N} (x : label) (t : tm (S N)) : tm N := t [⟦ · \ x ⟧].
Definition tclose_f {N} (x : label) (t : tm N) : tm (S N) := t [⟦ x \ · ⟧].
Definition tinst_f {N} (u : tm N) (t : tm (S N)) : tm N := t [⟦ · := u ⟧].

(** Names from numbers. *)
Fixpoint digits (fuel n : nat) (acc : string) : string :=
  match fuel with
  | 0 => acc
  | S f => let d := String (Ascii.ascii_of_nat (48 + Nat.modulo n 10)) EmptyString in
           if Nat.ltb n 10 then d ++ acc else digits f (Nat.div n 10) (d ++ acc)
  end.
Definition name (n : nat) : label := "v" ++ digits 20 n "".

(** Substitutions built by composing singletons. *)
Definition sub_one (x : label) (u : tm 0) : sub 0 0 := ⟦ x := u ⟧.
Definition sub_comp (a b : sub 0 0) : sub 0 0 := a ⨾ b.
Definition sub_id : sub 0 0 := ⟦⟧.
Definition sub_ren (x y : label) : sub 0 0 := ⟦ x as (fvar y 0) ⟧.

(** A locally nameless normal-order normaliser: binders are opened with
    fresh names, a redex is instantiated with a closed argument. *)
Fixpoint whnf (fuel : nat) (t : tm 0) : tm 0 :=
  match fuel with
  | 0 => t
  | S f =>
      match t with
      | tapp t1 t2 =>
          match whnf f t1 with
          | tlam b => whnf f (tinst_f t2 b)
          | h => tapp h t2
          end
      | _ => t
      end
  end.

Fixpoint nf (fuel : nat) (k : nat) (t : tm 0) : tm 0 :=
  match fuel with
  | 0 => t
  | S f =>
      match whnf fuel t with
      | tlam b => let x := name k in tlam (tclose_f x (nf f (S k) (topen_f x b)))
      | tapp t1 t2 => tapp (nf f k t1) (nf f k t2)
      | h => h
      end
  end.

(** The same with de Bruijn binders only: a redex is instantiated with an
    open argument, under the binders around it. *)
Fixpoint whnf_db (fuel : nat) {N} (t : tm N) : tm N :=
  match fuel with
  | 0 => t
  | S f =>
      match t with
      | tapp t1 t2 =>
          match whnf_db f t1 with
          | tlam b => whnf_db f (tinst_f t2 b)
          | h => tapp h t2
          end
      | _ => t
      end
  end.

Fixpoint nf_db (fuel : nat) {N} (t : tm N) : tm N :=
  match fuel with
  | 0 => t
  | S f =>
      match whnf_db fuel t with
      | tlam b => tlam (nf_db f b)
      | tapp t1 t2 => tapp (nf_db f t1) (nf_db f t2)
      | h => h
      end
  end.

Extraction "lambda.ml" nf_db tsubst topen_f tclose_f tinst_f name sub_one sub_comp sub_id sub_ren nf whnf.
