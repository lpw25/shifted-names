Require Import Label PeanoNat Compare_dec StrictProp.
Require Import Var Closing.

Definition raw_renaming_pushes : Type :=
  list (label * list (option var)).

Definition is_less_than_renaming_pushes
           s (r : raw_renaming_pushes) :=
  match r with
  | nil => true
  | cons (s', ps) r => is_less_than_label s s'
  end.

Fixpoint is_normalized_raw_renaming_pushes
         (r : raw_renaming_pushes) :=
  match r with
  | nil => true
  | cons (s, ps) r =>
    andb
      (is_less_than_renaming_pushes s r)
      (andb
         (andb (negb (is_pushes_nil ps))
               (is_normalized_pushes ps))
         (is_normalized_raw_renaming_pushes r))
  end.

Definition normalized_raw_renaming_pushes r :=
  if is_normalized_raw_renaming_pushes r then sUnit
  else sEmpty.

Set Primitive Projections.
Record raw_renaming :=
  mk_raw_renaming {
      r_renaming : raw_renaming_pushes;
      r_closing : raw_closing;
    }.
Add Printing Constructor raw_renaming.
Unset Primitive Projections.

Definition is_normalized_raw_renaming r :=
  andb (is_normalized_raw_renaming_pushes (r_renaming r))
       (is_normalized_pushes (r_closing r)).

Definition normalized_raw_renaming r :=
  if is_normalized_raw_renaming r then sUnit
  else sEmpty.

Set Primitive Projections.
Record renaming :=
  mk_renaming {
      r_raw : raw_renaming;
      r_normalized : normalized_raw_renaming r_raw;
    }.
Add Printing Constructor renaming.
Unset Primitive Projections.






