(** Extract the λ example's substitution with the library's extraction
    settings (run by [tests/extraction/run.sh]). *)
From ShiftedNames.Extraction Require Import Extraction.
From ShiftedNames.Core Require Import Label Var Indexed.
From ShiftedNames.Examples Require Import Lambda.
Import LS.

(** [subst], [topen], [tclose] and [tinst] are abbreviations; these are
    functions to extract. *)
Definition tsubst {N M} (a : sub N M) (t : tm N) : tm M := subst a t.
Definition topen_f {N} (x : label) (t : tm (S N)) : tm N := topen x t.
Definition tclose_f {N} (x : label) (t : tm N) : tm (S N) := tclose x t.
Definition tinst_f {N} (u : tm 0) (t : tm (S N)) : tm N := tinst u t.

Extraction "lambda.ml" tsubst topen_f tclose_f tinst_f.
